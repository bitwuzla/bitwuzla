#include "util/util.h"

#include <cassert>

namespace bzla::util {

bool
is_digit(char c)
{
  return c >= '0' && c <= '9';
}

bool
is_xdigit(char c)
{
  return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')
         || (c >= 'A' && c <= 'F');
}

bool
is_space(char c)
{
  return c == ' ' || c == '\t' || c == '\n' || c == '\v' || c == '\f'
         || c == '\r';
}

char
to_lower(char c)
{
  return (c >= 'A' && c <= 'Z') ? static_cast<char>(c - 'A' + 'a') : c;
}

bool
is_valid_bv_str(const std::string &value, uint8_t base)
{
  if (base == 2)
  {
    for (const auto &c : value)
    {
      if (c != '0' && c != '1') return false;
    }
    return true;
  }
  if (base == 10)
  {
    for (size_t i = value[0] == '-' ? 1 : 0, n = value.size(); i < n; ++i)
    {
      if (!is_digit(value[i])) return false;
    }
    return true;
  }
  assert(base == 16);
  for (const auto &c : value)
  {
    if (!is_xdigit(c))
    {
      return false;
    }
  }
  return true;
}

bool
is_valid_real_str(const std::string &value)
{
  bool found_dec_point = false;
  for (size_t i = 0, size = value.size(); i < size; ++i)
  {
    if (!is_digit(value[i]))
    {
      if (i == 0 && value[i] == '-')
      {
        continue;
      }
      else if (value[i] == '.' && !found_dec_point)
      {
        found_dec_point = true;
        continue;
      }
      return false;
    }
  }
  return true;
}

}  // namespace bzla::util
