#include <iostream>

extern "C" {
#include "api/c/bitwuzla.h"
}

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
  BitwuzlaResult parsed_status;

  Bitwuzla* bitwuzla;
  bitwuzla_parse_format("smt2",
                        smt2_input,
                        filename,
                        stdout,
                        &err_msg,
                        &bitwuzla,
                        &parsed_status);

  if (err_msg)
  {
    std::cerr << "[error]" << err_msg << std::endl;
    return EXIT_FAILURE;
  }

  return EXIT_SUCCESS;
}
