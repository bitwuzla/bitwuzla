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

  bitwuzla::Options options;
  std::string err_msg = bitwuzla::parse(options, argv[1]);
  if (err_msg.empty())
  {
    return EXIT_SUCCESS;
  }
  std::cerr << "[error] " << err_msg << std::endl;
  return EXIT_FAILURE;
}
