#include "util/util.h"

#include <cassert>

namespace bzla::util {

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
      if (value[i] < '0' || value[i] > '9') return false;
    }
    return true;
  }
  assert(base == 16);
  for (const auto &c : value)
  {
    if ((c < '0' || c > '9') && (c < 'a' || c > 'f') && (c < 'A' || c > 'F'))
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
    if (!isdigit(value[i]))
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
