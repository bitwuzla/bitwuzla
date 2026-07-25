/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_MALLOB
/*------------------------------------------------------------------------*/

#include "sat/mallob.h"

#include <fcntl.h>
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>
#ifdef __linux__
#include <sys/prctl.h>
#endif

#include <atomic>
#include <cassert>
#include <charconv>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <mutex>
#include <sstream>
#include <system_error>
#include <thread>

#include "util/exceptions.h"

/*------------------------------------------------------------------------*/

namespace bzla::sat {

/*------------------------------------------------------------------------*/

namespace {

namespace fs = std::filesystem;

/** The user name used for job submissions. */
const char* s_user = "bitwuzla";

/** Counter to make job names unique across solver instances. */
std::atomic<uint64_t> s_instance_counter{0};

std::string
escape_json(const std::string& s)
{
  std::string res;
  res.reserve(s.size());
  for (char c : s)
  {
    if (c == '"' || c == '\\')
    {
      res.push_back('\\');
    }
    res.push_back(c);
  }
  return res;
}

/**
 * Find a top-level key in a JSON string, set `pos` to the position right
 * after the associated ':'. Note: `key` must not be a prefix of another key
 * occurring in the document (the needle includes both quotes).
 */
bool
find_json_key(const std::string& json, const std::string& key, size_t& pos)
{
  std::string needle = "\"" + key + "\"";
  size_t p           = json.find(needle);
  if (p == std::string::npos)
  {
    return false;
  }
  p = json.find(':', p + needle.size());
  if (p == std::string::npos)
  {
    return false;
  }
  pos = p + 1;
  return true;
}

bool
parse_json_int(const std::string& json, const std::string& key, int64_t& value)
{
  size_t pos;
  if (!find_json_key(json, key, pos))
  {
    return false;
  }
  char* end;
  const char* start = json.c_str() + pos;
  long long v       = std::strtoll(start, &end, 10);
  if (end == start)
  {
    return false;
  }
  value = v;
  return true;
}

bool
parse_json_string(const std::string& json,
                  const std::string& key,
                  std::string& value)
{
  size_t pos;
  if (!find_json_key(json, key, pos))
  {
    return false;
  }
  size_t start = json.find('"', pos);
  if (start == std::string::npos)
  {
    return false;
  }
  size_t end = json.find('"', start + 1);
  if (end == std::string::npos)
  {
    return false;
  }
  value = json.substr(start + 1, end - start - 1);
  return true;
}

std::string
shell_quote(const std::string& s)
{
  std::string res = "'";
  for (char c : s)
  {
    if (c == '\'')
    {
      res += "'\\''";
    }
    else
    {
      res.push_back(c);
    }
  }
  res.push_back('\'');
  return res;
}

/** Resolve a binary to an absolute path, searching PATH if necessary. */
std::string
resolve_binary(const std::string& binary)
{
  std::error_code ec;
  if (binary.find('/') != std::string::npos)
  {
    fs::path abs = fs::absolute(binary, ec);
    if (!ec && fs::is_regular_file(abs, ec))
    {
      return abs.lexically_normal().string();
    }
  }
  else if (const char* path_env = std::getenv("PATH"))
  {
    std::stringstream ss(path_env);
    std::string dir;
    while (std::getline(ss, dir, ':'))
    {
      if (dir.empty())
      {
        continue;
      }
      fs::path cand = fs::path(dir) / binary;
      if (fs::is_regular_file(cand, ec)
          && access(cand.c_str(), X_OK) == 0)
      {
        return cand.string();
      }
    }
  }
  throw Error("Mallob binary '" + binary + "' not found");
}

}  // namespace

/*------------------------------------------------------------------------*/

/**
 * A Mallob process launched and managed by Bitwuzla (option --mallob-binary).
 *
 * The process runs in a fresh scratch directory such that its job API
 * (`.api/jobs.0/`) and any other relative output is contained there. Mallob
 * spawns helper binaries (mallob_sat_process, mallob_process_dispatcher) via
 * a path prefix baked in at Mallob compile time, which is relative (usually
 * "build/") in default builds and thus resolved against the working
 * directory. To support such builds, the directory containing the Mallob
 * binary is symlinked into the scratch directory as `build` and the helper
 * binaries are also symlinked directly.
 *
 * The daemon is shared between all Mallob solver instances of this process
 * and is terminated (SIGTERM to its process group, SIGKILL on timeout) when
 * the last instance is deleted. The child additionally gets SIGTERM if this
 * process dies (PR_SET_PDEATHSIG).
 */
class MallobDaemon
{
 public:
  /** Get the process-wide daemon, launching it if not running. */
  static std::shared_ptr<MallobDaemon> acquire(const std::string& binary,
                                               const std::string& launcher,
                                               const std::string& args,
                                               uint32_t nthreads)
  {
    static std::mutex mutex;
    static std::weak_ptr<MallobDaemon> instance;
    std::lock_guard<std::mutex> lock(mutex);
    std::shared_ptr<MallobDaemon> daemon = instance.lock();
    if (!daemon)
    {
      daemon.reset(new MallobDaemon(binary, launcher, args, nthreads));
      instance = daemon;
    }
    return daemon;
  }

  ~MallobDaemon()
  {
    if (d_pid > 0)
    {
      kill(-d_pid, SIGTERM);
      // Give Mallob time for a clean shutdown (it needs to reap its
      // solver subprocesses), then force termination.
      constexpr int64_t max_wait_ms = 10000;
      int64_t waited_ms             = 0;
      int status;
      while (waitpid(d_pid, &status, WNOHANG) == 0 && waited_ms < max_wait_ms)
      {
        std::this_thread::sleep_for(std::chrono::milliseconds(20));
        waited_ms += 20;
      }
      if (waited_ms >= max_wait_ms)
      {
        kill(-d_pid, SIGKILL);
        waitpid(d_pid, &status, 0);
      }
    }
    if (!d_scratch_dir.empty())
    {
      std::error_code ec;
      fs::remove_all(d_scratch_dir, ec);
    }
  }

  const std::string& api_dir() const { return d_api_dir; }

  /** Throw if the managed Mallob process exited. */
  void check_alive()
  {
    if (d_pid <= 0)
    {
      throw Error("managed Mallob process terminated unexpectedly"
                  + log_excerpt());
    }
    int status;
    if (waitpid(d_pid, &status, WNOHANG) == d_pid)
    {
      d_pid = -1;
      throw Error("managed Mallob process terminated unexpectedly"
                  + log_excerpt());
    }
  }

 private:
  MallobDaemon(const std::string& binary,
               const std::string& launcher,
               const std::string& args,
               uint32_t nthreads)
  {
    std::string abs_binary = resolve_binary(binary);

    // Create scratch working directory.
    std::string tmpl =
        (fs::temp_directory_path() / "bitwuzla-mallob-XXXXXX").string();
    if (mkdtemp(tmpl.data()) == nullptr)
    {
      throw Error("failed to create scratch directory for Mallob: "
                  + std::string(std::strerror(errno)));
    }
    d_scratch_dir = tmpl;
    d_log_file    = d_scratch_dir + "/mallob.log";
    d_api_dir     = d_scratch_dir + "/.api/jobs.0";

    // Make Mallob's helper binaries resolvable from the scratch directory
    // (covers relative subprocess dispatch prefixes "build/" and "").
    fs::path bin_dir = fs::path(abs_binary).parent_path();
    std::error_code ec;
    fs::create_directory_symlink(bin_dir, d_scratch_dir + "/build", ec);
    for (const char* helper :
         {"mallob_sat_process", "mallob_process_dispatcher"})
    {
      if (fs::is_regular_file(bin_dir / helper, ec))
      {
        fs::create_symlink(
            bin_dir / helper, fs::path(d_scratch_dir) / helper, ec);
      }
    }

    if (nthreads == 0)
    {
      nthreads = std::thread::hardware_concurrency();
      if (nthreads == 0)
      {
        nthreads = 1;
      }
    }

    std::string cmd = "exec ";
    if (!launcher.empty())
    {
      cmd += launcher + " ";
    }
    cmd += shell_quote(abs_binary) + " -t=" + std::to_string(nthreads);
    if (!args.empty())
    {
      cmd += " " + args;
    }

    pid_t pid = fork();
    if (pid < 0)
    {
      throw Error("failed to fork Mallob process: "
                  + std::string(std::strerror(errno)));
    }
    if (pid == 0)
    {
      // Child: new process group (for clean shutdown of the whole tree),
      // terminate with the parent, run in scratch dir, log to file.
      setpgid(0, 0);
#ifdef __linux__
      prctl(PR_SET_PDEATHSIG, SIGTERM);
#endif
      if (chdir(d_scratch_dir.c_str()) != 0)
      {
        _exit(127);
      }
      int fd = open(d_log_file.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0644);
      if (fd >= 0)
      {
        dup2(fd, STDOUT_FILENO);
        dup2(fd, STDERR_FILENO);
        close(fd);
      }
      execl("/bin/sh", "sh", "-c", cmd.c_str(), (char*) nullptr);
      _exit(127);
    }
    d_pid = pid;
    setpgid(pid, pid);

    // Wait for the job API to come up.
    constexpr int64_t max_wait_ms = 60000;
    int64_t waited_ms             = 0;
    while (!fs::is_directory(fs::path(d_api_dir) / "in", ec)
           || !fs::is_directory(fs::path(d_api_dir) / "out", ec))
    {
      int status;
      if (waitpid(d_pid, &status, WNOHANG) == d_pid)
      {
        d_pid           = -1;
        std::string msg = "failed to launch Mallob via `" + cmd + "'";
        msg += log_excerpt();
        std::error_code ec2;
        fs::remove_all(d_scratch_dir, ec2);
        d_scratch_dir.clear();
        throw Error(msg);
      }
      if (waited_ms >= max_wait_ms)
      {
        throw Error("timeout waiting for Mallob job API at '" + d_api_dir
                    + "'" + log_excerpt());
      }
      std::this_thread::sleep_for(std::chrono::milliseconds(20));
      waited_ms += 20;
    }
  }

  /** Get the tail of the daemon log for error messages. */
  std::string log_excerpt() const
  {
    std::ifstream is(d_log_file);
    if (!is)
    {
      return "";
    }
    std::stringstream ss;
    ss << is.rdbuf();
    std::string log = ss.str();
    constexpr size_t max_size = 2048;
    if (log.size() > max_size)
    {
      log = "..." + log.substr(log.size() - max_size);
    }
    if (log.empty())
    {
      return "";
    }
    return "; Mallob output:\n" + log;
  }

  std::string d_scratch_dir;
  std::string d_api_dir;
  std::string d_log_file;
  pid_t d_pid = -1;
};

/*------------------------------------------------------------------------*/

Mallob::Mallob(const std::string& api_dir,
               const std::string& binary,
               const std::string& launcher,
               const std::string& args,
               uint32_t nthreads)
    : d_api_dir(api_dir),
      d_binary(binary),
      d_launcher(launcher),
      d_args(args),
      d_nthreads(nthreads)
{
  d_job_prefix = "job-" + std::to_string(getpid()) + "-"
                 + std::to_string(s_instance_counter++);
}

Mallob::~Mallob() {}

int32_t
Mallob::new_var()
{
  return d_max_var++;
}

void
Mallob::add(int32_t lit, int64_t cgroup_id)
{
  assert(std::abs(lit) < d_max_var);
  (void) cgroup_id;
  d_literals.push_back(lit);
  if (lit == 0)
  {
    ++d_num_clauses;
  }
}

void
Mallob::assume(int32_t lit)
{
  assert(std::abs(lit) < d_max_var);
  d_assumptions.push_back(lit);
}

int32_t
Mallob::value(int32_t lit)
{
  assert(lit != 0);
  int32_t var = std::abs(lit);
  assert(var < d_max_var);
  int32_t val =
      static_cast<size_t>(var) < d_model.size() ? d_model[var] : 0;
  return lit < 0 ? -val : val;
}

bool
Mallob::failed(int32_t lit)
{
  (void) lit;
  throw Error("failed() not supported in Mallob");
  return false;
}

int32_t
Mallob::fixed(int32_t lit)
{
  (void) lit;
  throw Error("fixed() not supported in Mallob");
  return false;
}

const std::string&
Mallob::api_dir()
{
  if (!d_binary.empty())
  {
    if (!d_daemon)
    {
      d_daemon = MallobDaemon::acquire(d_binary, d_launcher, d_args,
                                       d_nthreads);
    }
    return d_daemon->api_dir();
  }
  return d_api_dir;
}

Result
Mallob::solve()
{
  std::error_code ec;
  const fs::path base(api_dir());
  if (!fs::is_directory(base / "in", ec) || !fs::is_directory(base / "out", ec))
  {
    throw Error("Mallob job API directory '" + base.string()
                + "' not found (expected subdirectories 'in' and 'out'); "
                  "start a Mallob process with a job API at this location or "
                  "configure it via option --mallob-api-dir (or have Bitwuzla "
                  "launch Mallob itself via option --mallob-binary)");
  }

  d_model.clear();
  std::string job_name = d_job_prefix + "-" + std::to_string(d_num_solves++);

  fs::path cnf_path = fs::temp_directory_path() / (job_name + ".cnf");
  write_dimacs(cnf_path.string());
  d_assumptions.clear();

  submit_json(job_name + ".json",
              std::string("{\"user\": \"") + s_user + "\", \"name\": \""
                  + job_name
                  + "\", \"application\": \"SAT\", \"priority\": 1.0, "
                    "\"files\": [\""
                  + escape_json(cnf_path.string()) + "\"]}");

  fs::path result_path =
      base / "out" / (std::string(s_user) + "." + job_name + ".json");

  Result res = Result::UNKNOWN;
  if (wait_for_result(job_name, result_path.string()))
  {
    std::ifstream is(result_path);
    std::stringstream ss;
    ss << is.rdbuf();
    std::string json = ss.str();

    int64_t resultcode;
    if (!parse_json_int(json, "resultcode", resultcode))
    {
      throw Error("failed to parse Mallob result file '"
                  + result_path.string() + "'");
    }
    if (resultcode == 10)
    {
      parse_model(json);
      res = Result::SAT;
    }
    else if (resultcode == 20)
    {
      res = Result::UNSAT;
    }
    fs::remove(result_path, ec);
  }
  fs::remove(cnf_path, ec);
  return res;
}

void
Mallob::configure_terminator(Terminator* terminator)
{
  d_terminator = terminator;
}

const char*
Mallob::get_version() const
{
  return "unknown";
}

/*------------------------------------------------------------------------*/

void
Mallob::write_dimacs(const std::string& path) const
{
  std::ofstream os(path, std::ios::binary);
  if (!os)
  {
    throw Error("failed to open '" + path + "' for writing");
  }

  std::string buf;
  buf.reserve(1 << 20);
  char nbuf[16];
  auto append_lit = [&buf, &nbuf](int32_t lit, char sep) {
    auto res = std::to_chars(nbuf, nbuf + sizeof(nbuf), lit);
    buf.append(nbuf, static_cast<size_t>(res.ptr - nbuf));
    buf.push_back(sep);
  };
  auto flush_if_full = [&buf, &os]() {
    if (buf.size() >= (1 << 20) - 32)
    {
      os.write(buf.data(), static_cast<std::streamsize>(buf.size()));
      buf.clear();
    }
  };

  buf += "p cnf " + std::to_string(d_max_var - 1) + " "
         + std::to_string(d_num_clauses
                          + static_cast<int64_t>(d_assumptions.size()))
         + "\n";
  for (int32_t lit : d_literals)
  {
    append_lit(lit, lit == 0 ? '\n' : ' ');
    flush_if_full();
  }
  // Encode assumptions as unit clauses (one-shot solving).
  for (int32_t lit : d_assumptions)
  {
    append_lit(lit, ' ');
    buf += "0\n";
    flush_if_full();
  }
  os.write(buf.data(), static_cast<std::streamsize>(buf.size()));
  os.close();
  if (!os)
  {
    throw Error("failed to write CNF to '" + path + "'");
  }
}

void
Mallob::submit_json(const std::string& file_name, const std::string& contents)
{
  fs::path in_dir = fs::path(api_dir()) / "in";
  // Mallob ignores files prefixed with '~' in its `in/` directory; write the
  // job file under a temporary name first and move it in place atomically.
  fs::path tmp_path = in_dir / ("~" + file_name);
  {
    std::ofstream os(tmp_path);
    if (!os)
    {
      throw Error("failed to open '" + tmp_path.string() + "' for writing");
    }
    os << contents;
    os.close();
    if (!os)
    {
      throw Error("failed to write Mallob job file '" + tmp_path.string()
                  + "'");
    }
  }
  std::error_code ec;
  fs::rename(tmp_path, in_dir / file_name, ec);
  if (ec)
  {
    throw Error("failed to submit Mallob job file '" + file_name
                + "': " + ec.message());
  }
}

bool
Mallob::wait_for_result(const std::string& job_name,
                        const std::string& result_path)
{
  std::error_code ec;
  const fs::path path(result_path);
  bool interrupted = false;
  std::chrono::steady_clock::time_point interrupt_deadline;
  auto interval               = std::chrono::microseconds(500);
  constexpr auto max_interval = std::chrono::microseconds(100000);

  // Mallob moves complete result files into `out/`, thus the file contents
  // are guaranteed to be complete as soon as the file exists.
  while (!fs::exists(path, ec))
  {
    if (d_daemon)
    {
      d_daemon->check_alive();
    }
    if (d_terminator && d_terminator->terminate())
    {
      if (!interrupted)
      {
        // Forward termination request as job interrupt. Mallob responds
        // with an UNKNOWN result for the interrupted job.
        submit_json(job_name + ".interrupt.json",
                    std::string("{\"user\": \"") + s_user + "\", \"name\": \""
                        + job_name
                        + "\", \"application\": \"SAT\", \"interrupt\": "
                          "true}");
        interrupted        = true;
        interrupt_deadline = std::chrono::steady_clock::now()
                             + std::chrono::seconds(10);
      }
      else if (std::chrono::steady_clock::now() >= interrupt_deadline)
      {
        // Give up waiting for Mallob to acknowledge the interrupt.
        return false;
      }
    }
    std::this_thread::sleep_for(interval);
    if (interval < max_interval)
    {
      interval *= 2;
    }
  }
  return true;
}

void
Mallob::parse_model(const std::string& json)
{
  d_model.assign(static_cast<size_t>(d_max_var), 0);

  auto set_value = [this](int64_t lit) {
    int64_t var = lit < 0 ? -lit : lit;
    if (var > 0 && var < d_max_var)
    {
      d_model[static_cast<size_t>(var)] = lit < 0 ? -1 : 1;
    }
  };

  size_t pos;
  if (find_json_key(json, "solution", pos))
  {
    size_t p = json.find_first_not_of(" \t\n\r", pos);
    if (p == std::string::npos || json[p] != '[')
    {
      throw Error(
          "unexpected solution format in Mallob result (Mallob must be run "
          "without model compression, i.e., with -cm=0)");
    }
    const char* c = json.c_str() + p + 1;
    while (true)
    {
      while (*c == ' ' || *c == ',' || *c == '\n' || *c == '\r' || *c == '\t')
      {
        ++c;
      }
      if (*c == ']' || *c == '\0')
      {
        break;
      }
      char* end;
      long long lit = std::strtoll(c, &end, 10);
      if (end == c)
      {
        throw Error("failed to parse solution in Mallob result");
      }
      set_value(lit);
      c = end;
    }
    return;
  }

  // Large solutions are delivered via a named pipe if Mallob runs with
  // option -pls (pipe large solutions).
  std::string sol_file;
  int64_t sol_size;
  if (parse_json_string(json, "solution-file", sol_file)
      && parse_json_int(json, "solution-size", sol_size) && sol_size >= 0)
  {
    std::vector<int32_t> solution(static_cast<size_t>(sol_size));
    size_t total = static_cast<size_t>(sol_size) * sizeof(int32_t);
    FILE* pipe   = std::fopen(sol_file.c_str(), "rb");
    if (!pipe)
    {
      throw Error("failed to open Mallob solution pipe '" + sol_file + "'");
    }
    size_t nread = 0;
    while (nread < total)
    {
      size_t n = std::fread(reinterpret_cast<char*>(solution.data()) + nread,
                            1,
                            total - nread,
                            pipe);
      if (n == 0)
      {
        break;
      }
      nread += n;
    }
    std::fclose(pipe);
    std::error_code ec;
    fs::remove(fs::path(sol_file), ec);
    if (nread < total)
    {
      throw Error("failed to read solution from Mallob solution pipe '"
                  + sol_file + "'");
    }
    for (int32_t lit : solution)
    {
      set_value(lit);
    }
    return;
  }

  throw Error("no solution found in Mallob result for satisfiable formula");
}

/*------------------------------------------------------------------------*/

}  // namespace bzla::sat

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
