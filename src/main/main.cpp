extern "C" {
#include "api/c/bitwuzla.h"
}

#include <iostream>

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

  Bitwuzla* bzla = bitwuzla_new();
  bitwuzla_parse_format(
      bzla, "smt2", smt2_input, filename, stdout, &err_msg, &parsed_status);

  if (err_msg)
  {
    std::cerr << "[error]" << err_msg << std::endl;
    bitwuzla_delete(bzla);
    return EXIT_FAILURE;
  }

  bitwuzla_delete(bzla);
  return EXIT_SUCCESS;
}
