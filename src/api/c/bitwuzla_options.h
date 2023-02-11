// TODO: This code is to be moved back to api/c/bitwuzla.cpp after the parser
//       is rewrittern and uses the C++ API!

#ifndef BITWUZLA_API_C_BITWUZLA_OPTIONS_H_INCLUDED
#define BITWUZLA_API_C_BITWUZLA_OPTIONS_H_INCLUDED

#include <bitwuzla/cpp/bitwuzla.h>

struct BitwuzlaOptions
{
  BitwuzlaOptions() : d_options(bitwuzla::Options()) {}
  BitwuzlaOptions(bitwuzla::Options& options) : d_options(options) {}
  bitwuzla::Options d_options;
};

#endif
