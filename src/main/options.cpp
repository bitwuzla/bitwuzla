#include "main/options.h"

#include <bitwuzla/cpp/bitwuzla.h>

#include <algorithm>
#include <cassert>
#include <iomanip>
#include <iostream>
#include <sstream>

#include "main/error.h"

namespace bzla::main {

namespace {

namespace {

/** Helper to format option names and add meta variables. */
std::string
format_opt(const char* name, bool is_shrt, bool is_numeric, bool is_mode)
{
  if (name)
  {
    std::string fmt = is_shrt ? "-" : "--";
    fmt += name;
    if (is_numeric)
    {
      fmt += " <n>";
    }
    else if (is_mode)
    {
      fmt += " <M>";
    }
    return fmt;
  }
  return std::string();
}

/** Format short name of mode option. */
std::string
format_shortm(const char* shrt)
{
  return format_opt(shrt, true, false, true);
}

/** Format long name of mode option. */
std::string
format_longm(const char* lng)
{
  return format_opt(lng, false, false, true);
}

/** Format short name of numeric option. */
std::string
format_shortn(const char* shrt)
{
  return format_opt(shrt, true, true, false);
}

/** Format long name of numeric option. */
std::string
format_longn(const char* lng)
{
  return format_opt(lng, false, true, false);
}

/** Format short name of boolean option. */
std::string
format_shortb(const char* shrt)
{
  return format_opt(shrt, true, false, false);
}

/** Format long name of boolean option. */
std::string
format_longb(const char* lng)
{
  return format_opt(lng, false, false, false);
}

/** Format string of default value. */
std::string
format_dflt(const std::string& dflt, bool is_bool = false)
{
  if (is_bool)
  {
    return "[" + std::string((dflt == "1" ? "true" : "false")) + "]";
  }
  return "[" + dflt + "]";
}

/** Wrap text to remaining width of 80 character wide line. */
std::string
wrap(const std::string& text, size_t already_used_width)
{
  std::istringstream iss(text);
  size_t line_len = 0;
  size_t width    = 80 - already_used_width;
  std::stringstream wrapped;
  std::string w;
  while (std::getline(iss, w, ' '))
  {
    assert(w.size() < width);
    if (line_len + w.size() >= width)
    {
      wrapped << "\n  " << std::setw(already_used_width) << " ";
      line_len = 0;
    }
    wrapped << w << " ";
    line_len += w.size();
  }
  return wrapped.str();
}

/** Print help message. */
void
print_help()
{
  std::vector<std::tuple<std::string, std::string, std::string, std::string>>
      opts;

  Options dflt_opts;

  // Main options
  opts.emplace_back("", "<input>", format_dflt("<stdin>"), "input file");
  opts.emplace_back(format_shortb("h"),
                    format_longb("help"),
                    "",
                    "print this message and exit");
  opts.emplace_back(format_shortb("V"),
                    format_longb("version"),
                    "",
                    "print version and exit");
  opts.emplace_back(format_shortb("c"),
                    format_longb("copyright"),
                    "",
                    "print copyright and exit");
  opts.emplace_back(format_shortb("p"),
                    format_longb("print-formula"),
                    "",
                    "print formula in smt2 format");
  opts.emplace_back("",
                    format_longb("print-unsat-core"),
                    "",
                    "print unsat core in smt2 format");
  opts.emplace_back(
      "", format_longb("print-model"), "", "print model in smt2 format");
  opts.emplace_back(format_shortb("P"),
                    format_longb("parse-only"),
                    format_dflt(std::to_string(dflt_opts.parse_only), true),
                    "only parse input without calling check-sat");
  opts.emplace_back("",
                    format_longb("bv-output-format"),
                    format_dflt(std::to_string(dflt_opts.bv_format)),
                    "output number format for bit-vector values {2, 10, 16}");
  opts.emplace_back(format_shortn("t"),
                    format_longn("time-limit"),
                    format_dflt(std::to_string(dflt_opts.time_limit)),
                    "time limit in milliseconds");
  opts.emplace_back("",
                    format_longm("lang"),
                    format_dflt(dflt_opts.language),
                    "input language {smt2, btor2}");

  // Format library options
  bitwuzla::Options options;
  for (size_t i = 0, size = static_cast<size_t>(bitwuzla::Option::NUM_OPTS);
       i < size;
       ++i)
  {
    auto o    = static_cast<bitwuzla::Option>(i);
    auto shrt = options.shrt(o);
    auto lng  = options.lng(o);

    if (options.is_mode(o))
    {
      std::stringstream desc;
      desc << options.description(o);
      auto modes = options.modes(o);
      desc << " {";
      for (size_t j = 0, size = modes.size(); j < size; ++j)
      {
        if (j > 0)
        {
          desc << ", ";
        }
        desc << modes[j];
      }
      desc << "}";
      opts.emplace_back(format_shortm(shrt),
                        format_longm(lng),
                        format_dflt(options.get_mode(o)),
                        desc.str());
    }
    else if (options.is_numeric(o))
    {
      opts.emplace_back(format_shortn(shrt),
                        format_longn(lng),
                        format_dflt(std::to_string(options.get(o))),
                        options.description(o));
    }
    else
    {
      assert(options.is_bool(o));
      opts.emplace_back(format_shortb(shrt),
                        format_longb(lng),
                        format_dflt(std::to_string(options.get(o)), true),
                        options.description(o));
    }
  }

  // Compute maximum size of option column
  size_t max_size_first  = 0;
  size_t max_size_second = 0;
  for (const auto& [shrt, lng, dflt, desc] : opts)
  {
    size_t col_size = shrt.size() + lng.size() + 2;
    if (col_size > max_size_first)
    {
      max_size_first = col_size;
    }
    col_size = dflt.size() + 2;
    if (col_size > max_size_second)
    {
      max_size_second = col_size;
    }
  }

  // Print help message
  std::stringstream ss;
  ss << "Usage:\n";
  ss << "  bitwuzla [<options>] [<input>]\n";
  ss << "\n";
  ss << "Options:\n";
  for (const auto& [shrt, lng, dflt, desc] : opts)
  {
    std::string col;
    if (!shrt.empty())
    {
      col = shrt + ", ";
    }
    col += lng;

    ss << "  " << std::left << std::setw(max_size_first) << col
       << std::setw(max_size_second) << dflt
       << wrap(desc, max_size_first + max_size_second) << "\n";
  }
  std::cout << ss.str() << std::endl;
}

/** Print copyright. */
void
print_copyright()
{
  std::cout << bitwuzla::copyright() << std::endl;
}

/** Print version. */
void
print_version()
{
  std::cout << bitwuzla::version() << std::endl;
}

}  // namespace

bool
is_input_file(const std::string& arg, const std::string& suffix)
{
  size_t pos = arg.find(suffix);
  return pos != arg.npos && pos == arg.size() - suffix.size();
}

bool
startswith(const std::string& str, const std::string& prefix)
{
  return str.rfind(prefix, 0) == 0;
}

std::pair<std::string, std::string>
parse_arg_val(int32_t argc, int32_t& i, char* argv[])
{
  std::string arg(argv[i]);

  std::string opt, value;
  auto pos = arg.rfind("=");
  // -o=v, --option=value
  if (pos != std::string::npos)
  {
    opt   = arg.substr(0, pos);
    value = arg.substr(pos + 1);
  }
  // -o v, --option value
  else if (i + 1 < argc && argv[i + 1][0] != '-')
  {
    opt   = argv[i];
    value = argv[i + 1];
    ++i;
  }

  if (value.empty())
  {
    Error() << "expected value for option `" << opt << "`";
  }

  return std::make_pair(opt, value);
}

uint64_t
parse_arg_uint64_t(int32_t argc, int32_t& i, char* argv[])
{
  auto [opt, value] = parse_arg_val(argc, i, argv);
  try
  {
    return std::stoull(value);
  }
  catch (std::invalid_argument& e)
  {
    Error() << "expected numeric value for option `" << opt << "` but got `"
            << value << "`";
  }
}

bool
check_opt_value(const std::string& arg,
                const std::string& short_opt,
                const std::string& long_opt)
{
  return arg == short_opt || arg == long_opt || startswith(arg, short_opt + "=")
         || startswith(arg, long_opt + "=");
}

}  // namespace

Options
parse_options(int32_t argc, char* argv[], std::vector<std::string>& args)
{
  bitwuzla::Options library_opts;
  Options opts;
  bool input_file_set = false;
  bool lang_forced = false;
  for (int32_t i = 1; i < argc; ++i)
  {
    std::string arg(argv[i]);
    if (arg == "-h" || arg == "--help")
    {
      print_help();
      std::exit(EXIT_SUCCESS);
    }
    else if (arg == "-c" || arg == "--copyright")
    {
      print_copyright();
      std::exit(EXIT_SUCCESS);
    }
    else if (arg == "-V" || arg == "--version")
    {
      print_version();
      std::exit(EXIT_SUCCESS);
    }
    else if (arg == "-p" || arg == "--print-formula")
    {
      opts.print = true;
    }
    else if (arg == "--print-unsat-core")
    {
      opts.print_unsat_core = true;
    }
    else if (arg == "--print-model")
    {
      opts.print_model = true;
    }
    else if (arg == "-P" || arg == "--parse-only")
    {
      opts.parse_only = true;
    }
    else if (check_opt_value(arg, "", "--bv-output-format"))
    {
      opts.bv_format = parse_arg_uint64_t(argc, i, argv);
      if (opts.bv_format != 2 && opts.bv_format != 10 && opts.bv_format != 16)
      {
        Error() << "invalid bit-vector output number format, "
                   "expected '2', '10', or '16'";
      }
    }
    else if (check_opt_value(arg, "-t", "--time-limit"))
    {
      opts.time_limit = parse_arg_uint64_t(argc, i, argv);
    }
    else if (check_opt_value(arg, "", "--lang"))
    {
      auto [opt, val] = parse_arg_val(argc, i, argv);
      if (val != "smt2" && val != "btor2")
      {
        Error() << "invalid input language given `" << val << "`, expected "
                << "'smt2' or 'btor2'";
      }
      opts.language = val;
      lang_forced   = true;
    }
    else if (arg[0] == '-')
    {
      args.push_back(arg);
      // Determine whether library options require arguments. We do not check
      // whether it is a valid library option.
      auto pos = arg.rfind("=");
      if (pos == std::string::npos)
      {
        std::string name = arg.substr(1);
        // Long option
        if (!name.empty() && name[0] == '-')
        {
          name = name.substr(1);
        }
        if (library_opts.is_valid(name))
        {
          auto option = library_opts.option(name.c_str());
          if (library_opts.is_mode(option))
          {
            if (i + 1 < argc)
            {
              args.emplace_back(argv[++i]);
            }
          }
          else if (library_opts.is_numeric(option))
          {
            if (i + 1 < argc)
            {
              bool allow_inc = option == bitwuzla::Option::VERBOSITY
                               || option == bitwuzla::Option::LOGLEVEL;
              auto value = std::string(argv[i + 1]);
              if (!allow_inc
                  || std::all_of(value.begin(), value.end(), ::isdigit))
              {
                args.emplace_back(argv[++i]);
              }
            }
          }
        }
      }
    }
    else if (!input_file_set)
    {
      opts.infile_name = arg;
      input_file_set   = true;
    }
    else if (arg != opts.infile_name)
    {
      Error() << "multiple input files detected: `" << arg << "`, already got `"
              << opts.infile_name << "`.";
    }
  }

  // If user did not force an input language, set it according to file suffix.
  if (!lang_forced)
  {
    if (is_input_file(opts.infile_name, ".btor2"))
    {
      opts.language = "btor2";
    }
    else
    {
      opts.language = "smt2";
    }
  }
  return opts;
}

}  // namespace bzla::main
