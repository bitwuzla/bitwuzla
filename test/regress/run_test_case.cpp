/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

/**
 * Runs a regression test case and compares the output of the binary with the
 * expected output. This is a compiled program since the start-up of a script
 * interpreter takes longer than most test cases.
 *
 * Usage:
 *   run_test_case [--check-sat|--check-unsat] <binary> <test file> [<opt>...]
 *
 * The options are passed to the binary. The expected output is read from the
 * .expect file of the test if it exists. Without an expect file, the expected
 * output is the sequence of results given by '(set-info :status ...)' in the
 * test file. If the test file contains '; ignore output', only the results of
 * the binary are compared.
 *
 * '{{\d+}}' in an .expect file matches a number, e.g. a limit that differs
 * between architectures:
 *   expected floating-point exponent size <= {{\d+}}, got '64'
 */

#include <cerrno>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <optional>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

#ifdef _WIN32
#include <windows.h>

#include <thread>
#else
#include <fcntl.h>
#include <poll.h>
#include <spawn.h>
#include <sys/wait.h>
#include <unistd.h>

extern char** environ;
#endif

namespace {

const char* s_whitespace        = " \t\n\r\v\f";
const std::string_view s_number = "{{\\d+}}";

std::string
strip(const std::string& s)
{
  size_t begin = s.find_first_not_of(s_whitespace);
  if (begin == std::string::npos)
  {
    return "";
  }
  size_t end = s.find_last_not_of(s_whitespace);
  return s.substr(begin, end - begin + 1);
}

/** Read a file, line endings may be \r\n depending on the checkout. */
std::string
read_file(const std::string& filename)
{
  std::ifstream file(filename, std::ios::binary);
  std::stringstream ss;
  ss << file.rdbuf();
  std::string res = ss.str();
  std::erase(res, '\r');
  return res;
}

#ifdef _WIN32

/** Quote an argument as parsed by the C runtime of the started process. */
std::string
quote(const std::string& arg)
{
  if (!arg.empty() && arg.find_first_of(" \t\n\v\"") == std::string::npos)
  {
    return arg;
  }
  std::string res    = "\"";
  size_t backslashes = 0;
  for (char c : arg)
  {
    if (c == '\\')
    {
      ++backslashes;
      continue;
    }
    // Backslashes are only special if they precede a quote.
    res.append(c == '"' ? 2 * backslashes + 1 : backslashes, '\\');
    backslashes = 0;
    res += c;
  }
  res.append(2 * backslashes, '\\');
  res += '"';
  return res;
}

void
read_all(HANDLE handle, std::string& res)
{
  char buf[65536];
  DWORD n;
  while (ReadFile(handle, buf, sizeof(buf), &n, nullptr) && n > 0)
  {
    res.append(buf, n);
  }
}

/** Run `cmd` and capture its standard output and error. */
bool
run(const std::vector<std::string>& cmd, std::string& out, std::string& err)
{
  SECURITY_ATTRIBUTES sa{sizeof(sa), nullptr, TRUE};
  HANDLE out_read, out_write, err_read, err_write;
  if (!CreatePipe(&out_read, &out_write, &sa, 0))
  {
    std::cerr << "failed to create pipe: error " << GetLastError() << std::endl;
    return false;
  }
  if (!CreatePipe(&err_read, &err_write, &sa, 0))
  {
    std::cerr << "failed to create pipe: error " << GetLastError() << std::endl;
    CloseHandle(out_read);
    CloseHandle(out_write);
    return false;
  }
  SetHandleInformation(out_read, HANDLE_FLAG_INHERIT, 0);
  SetHandleInformation(err_read, HANDLE_FLAG_INHERIT, 0);
  HANDLE null = CreateFileA("NUL",
                            GENERIC_READ,
                            FILE_SHARE_READ | FILE_SHARE_WRITE,
                            &sa,
                            OPEN_EXISTING,
                            0,
                            nullptr);

  STARTUPINFOA si{};
  si.cb         = sizeof(si);
  si.dwFlags    = STARTF_USESTDHANDLES;
  si.hStdInput  = null;
  si.hStdOutput = out_write;
  si.hStdError  = err_write;

  std::string cmdline;
  for (const std::string& arg : cmd)
  {
    cmdline += (cmdline.empty() ? "" : " ") + quote(arg);
  }
  PROCESS_INFORMATION pi;
  BOOL started = CreateProcessA(nullptr,
                                cmdline.data(),
                                nullptr,
                                nullptr,
                                TRUE,
                                0,
                                nullptr,
                                nullptr,
                                &si,
                                &pi);
  CloseHandle(out_write);
  CloseHandle(err_write);
  CloseHandle(null);
  if (!started)
  {
    std::cerr << "failed to run '" << cmd[0] << "': error " << GetLastError()
              << std::endl;
  }
  else
  {
    // Read both pipes concurrently, the process blocks if one of them is full.
    std::thread t([&]() { read_all(err_read, err); });
    read_all(out_read, out);
    t.join();
    WaitForSingleObject(pi.hProcess, INFINITE);
    CloseHandle(pi.hProcess);
    CloseHandle(pi.hThread);
  }
  CloseHandle(out_read);
  CloseHandle(err_read);
  return started;
}

#else

/** Run `cmd` and capture its standard output and error. */
bool
run(const std::vector<std::string>& cmd, std::string& out, std::string& err)
{
  int out_pipe[2], err_pipe[2];
  if (pipe(out_pipe) != 0)
  {
    std::cerr << "failed to create pipe: " << std::strerror(errno) << std::endl;
    return false;
  }
  if (pipe(err_pipe) != 0)
  {
    std::cerr << "failed to create pipe: " << std::strerror(errno) << std::endl;
    close(out_pipe[0]);
    close(out_pipe[1]);
    return false;
  }

  posix_spawn_file_actions_t actions;
  posix_spawn_file_actions_init(&actions);
  posix_spawn_file_actions_addopen(&actions, 0, "/dev/null", O_RDONLY, 0);
  posix_spawn_file_actions_adddup2(&actions, out_pipe[1], 1);
  posix_spawn_file_actions_adddup2(&actions, err_pipe[1], 2);
  for (int fd : {out_pipe[0], out_pipe[1], err_pipe[0], err_pipe[1]})
  {
    posix_spawn_file_actions_addclose(&actions, fd);
  }

  std::vector<char*> argv;
  for (const std::string& arg : cmd)
  {
    argv.push_back(const_cast<char*>(arg.c_str()));
  }
  argv.push_back(nullptr);

  pid_t pid;
  int rc = posix_spawn(&pid, argv[0], &actions, nullptr, argv.data(), environ);
  posix_spawn_file_actions_destroy(&actions);
  close(out_pipe[1]);
  close(err_pipe[1]);
  if (rc != 0)
  {
    std::cerr << "failed to run '" << cmd[0] << "': " << std::strerror(rc)
              << std::endl;
    close(out_pipe[0]);
    close(err_pipe[0]);
    return false;
  }

  // Read both pipes concurrently, the process blocks if one of them is full.
  pollfd fds[2]      = {{out_pipe[0], POLLIN, 0}, {err_pipe[0], POLLIN, 0}};
  std::string* res[] = {&out, &err};
  char buf[65536];
  for (int open = 2; open > 0;)
  {
    if (poll(fds, 2, -1) < 0)
    {
      if (errno == EINTR)
      {
        continue;
      }
      break;
    }
    for (size_t i = 0; i < 2; ++i)
    {
      if (fds[i].fd < 0 || fds[i].revents == 0)
      {
        continue;
      }
      ssize_t n = read(fds[i].fd, buf, sizeof(buf));
      if (n > 0)
      {
        res[i]->append(buf, n);
      }
      else if (n == 0 || errno != EINTR)
      {
        close(fds[i].fd);
        // poll() ignores negative file descriptors.
        fds[i].fd = -1;
        --open;
      }
    }
  }
  for (int fd : {fds[0].fd, fds[1].fd})
  {
    if (fd >= 0)
    {
      close(fd);
    }
  }
  int status;
  while (waitpid(pid, &status, 0) < 0 && errno == EINTR)
  {
  }
  return true;
}

#endif

/** Compare `actual` against `expected`, in which '{{\d+}}' matches a number. */
bool
matches(std::string_view expected, std::string_view actual)
{
  size_t pos = expected.find(s_number);
  if (pos == std::string_view::npos)
  {
    return expected == actual;
  }
  size_t end = actual.find_first_not_of("0123456789", pos);
  if (end == std::string_view::npos)
  {
    end = actual.size();
  }
  return actual.substr(0, pos) == expected.substr(0, pos) && end > pos
         && matches(expected.substr(pos + s_number.size()), actual.substr(end));
}

/**
 * Determine the expected results from the status annotations of the test
 * file. Sets `ignore_output` if the output of the binary other than its
 * results is not compared.
 */
std::optional<std::string>
expected_from_status(const std::string& testfile, bool& ignore_output)
{
  std::ifstream file(testfile, std::ios::binary);
  std::string expected, line;
  size_t num_check_sat = 0, num_status = 0;
  while (std::getline(file, line))
  {
    line = strip(line);
    if (line.starts_with("(set-info :status"))
    {
      ++num_status;
      // The status is the last word without its closing parenthesis.
      std::string status = line.substr(line.find_last_of(s_whitespace) + 1);
      status             = strip(status.substr(0, status.size() - 1));
      if (status != "sat" && status != "unsat")
      {
        std::cerr << "invalid status '" << status << "' in '" << testfile << "'"
                  << std::endl;
        return std::nullopt;
      }
      expected += status + "\n";
    }
    else if (line.starts_with("(check-sat"))
    {
      ++num_check_sat;
    }
    else if (line.starts_with("; ignore output"))
    {
      ignore_output = true;
    }
  }
  if (num_check_sat != num_status)
  {
    std::cerr << "number of check-sat commands and status annotations differ"
              << " in '" << testfile << "'" << std::endl;
    return std::nullopt;
  }
  return expected;
}

bool
check(const std::string& testfile,
      std::optional<std::string> expected,
      std::string out,
      std::string err)
{
  // Remove \r from output of Windows binaries
  std::erase(out, '\r');
  std::erase(err, '\r');
  size_t pos = err.find("regress/");
  if (pos != std::string::npos)
  {
    err = err.substr(pos);
  }

  bool ignore_output = false;
  std::string cmp    = out;

  if (!expected || expected->empty())
  {
    expected = expected_from_status(testfile, ignore_output);
    if (!expected)
    {
      return false;
    }
  }

  if (ignore_output)
  {
    std::stringstream ss(cmp);
    std::string line;
    cmp.clear();
    while (std::getline(ss, line))
    {
      if (line == "sat" || line == "unsat" || line == "unknown")
      {
        cmp += (cmp.empty() ? "" : "\n") + line;
      }
    }
  }

  cmp += err;

  if (matches(strip(*expected), strip(cmp)))
  {
    return true;
  }

  bool is_pattern = expected->find(s_number) != std::string::npos;
  auto line       = [](const std::string& s) {
    return s.empty() || s.back() != '\n' ? s + "\n" : s;
  };
  std::cerr << "Expected" << (is_pattern ? " (pattern)" : "") << ":\n"
            << line(*expected) << std::string(80, '=') << "\nGot:\n"
            << line(cmp) << std::flush;
  return false;
}

}  // namespace

int
main(int argc, char* argv[])
{
  std::optional<std::string> expected;
  int i = 1;
  for (; i < argc; ++i)
  {
    std::string_view arg = argv[i];
    if (arg == "--check-sat")
    {
      expected = "sat";
    }
    else if (arg == "--check-unsat")
    {
      expected = "unsat";
    }
    else
    {
      break;
    }
  }
  if (argc - i < 2)
  {
    std::cerr << "usage: " << argv[0]
              << " [--check-sat|--check-unsat] <binary> <test file> [<opt>...]"
              << std::endl;
    return 1;
  }
  std::vector<std::string> cmd(argv + i, argv + argc);
  const std::string& testfile = cmd[1];

  std::string cmdline;
  for (const std::string& arg : cmd)
  {
    cmdline += (cmdline.empty() ? "" : " ") + arg;
  }
  std::cout << "Running test case '" << cmdline << "'" << std::endl;

  std::string out, err;
  if (!run(cmd, out, err))
  {
    return 1;
  }

  std::string expect_file =
      std::filesystem::path(testfile).replace_extension(".expect").string();
  if (std::filesystem::exists(expect_file))
  {
    expected = read_file(expect_file);
  }

  return check(testfile, expected, out, err) ? 0 : 1;
}
