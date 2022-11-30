#include <iostream>

#include "api/cpp/bitwuzla.h"

int32_t
main(int32_t argc, char* argv[])
{
  if (argc != 2)
  {
    std::cerr << "[error] Invalid number of arguments. Expected input file"
              << std::endl;
    return EXIT_FAILURE;
  }

  const char* filename = argv[1];
  FILE* smt2_input     = fopen(filename, "r");

  char* err_msg;
  bitwuzla::Result parsed_status;

  bitwuzla::Options options;
  bitwuzla::Bitwuzla bitwuzla(options);
  // bitwuzla_parse_format(
  //     bzla, "smt2", smt2_input, filename, stdout, &err_msg, &parsed_status);

  if (err_msg)
  {
    std::cerr << "[error]" << err_msg << std::endl;
    return EXIT_FAILURE;
  }

  return EXIT_SUCCESS;
}
