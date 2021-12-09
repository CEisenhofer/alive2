// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "big_num.h"

#include <cassert>
#include <string.h>

namespace util {

static void uint64ToBinaryString(uint64_t n, char *arr) {
  // arr contains at least 65 elements
  arr[64] = '\0';
  for (int i = 64; i > 0; i--) {
    char item = (char)(n & 1);
    n >>= 1;
    arr[i - 1] = (char)('0' + item);
  }
}

BigNum::BigNum(uint64_t u64, size_t bitWidth) : arr(nullptr), bitWidth(bitWidth) {
  if (bitWidth < 64)
    this->u64 = u64 & ((1ull << bitWidth) - 1);
  else
    this->u64 = u64;
}

BigNum::BigNum(const char *arr, size_t bitWidth) {
  assert(strlen(arr) == bitWidth); // leading zeros important for comparing binary numbers
  u64 = 0;
  this->bitWidth = bitWidth;
  if (bitWidth > 64) {
    this->arr = strdup(arr);
  } else {
    this->arr = nullptr;
    // Simplify
    for (size_t i = 0; i < bitWidth && arr[i] != '\0'; i++) {
      u64 <<= 1;
      u64 |= arr[i] - '0';
    }
  }
}


BigNum::BigNum(const BigNum &other) :
        arr(other.arr == nullptr ? nullptr : strdup(other.arr)),
        bitWidth(other.bitWidth), u64(other.u64) {}

BigNum::~BigNum() {
  if (arr) {
    free(arr);
  }
}

BigNum BigNum::truncOrExtend(uint64_t u64, size_t toBitWidth) {
  if (toBitWidth == 64) {
    return BigNum(u64, toBitWidth);
  }
  if (toBitWidth < 64) {
    return BigNum(u64 & ((1ull << toBitWidth) - 1), toBitWidth);
  }
  char *arr = (char *)malloc(sizeof(char) * (toBitWidth + 1));
  memset(arr, '0', toBitWidth - 64);
  uint64ToBinaryString(u64, arr + toBitWidth - 64);
  BigNum res(arr, toBitWidth);
  free(arr);
  return res;
}

BigNum BigNum::truncOrExtend(const char *arr, size_t toBitWidth) {
  size_t len = strlen(arr);
  if (len == toBitWidth) {
    return BigNum(arr, toBitWidth);
  }
  char *a = (char *)malloc(sizeof(char) * (toBitWidth + 1));
  if (len < toBitWidth) {
    memset(a, '0', toBitWidth - len);
    memcpy(a + toBitWidth - len, arr, len + 1);
  } else {
    memcpy(a, arr + (len - toBitWidth), toBitWidth + 1);
  }
  BigNum res(a, toBitWidth);
  free(a);
  return res;
}

BigNum BigNum::operator+(const BigNum &other) const {
  assert(bitWidth == other.bitWidth);
  // Simple case
  if (!arr && !other.arr) {
    uint64_t res = u64 + other.u64;
    if (bitWidth == 64) {
      return BigNum(res, bitWidth);
    }
    if (bitWidth < 64) {
      return BigNum(res & ((1ull << bitWidth) - 1ull), bitWidth);
    }
    if (res >= u64 && res >= other.u64) {
      // No overflow
      return BigNum(res, bitWidth);
    }
    // Overflow
    char arr[66];
    arr[0] = '1';
    uint64ToBinaryString(res, arr + 1);
    return BigNum(arr, bitWidth);
  }

  // Array case
  char help[65]; // In case one of the elements is saved as a plain uint64
  unsigned overflow = 0;
  size_t i1 = bitWidth, i2 = bitWidth, i = bitWidth;
  char *a1, *a2;
  if (arr == nullptr) {
    a1 = help;
    i1 = 64;
    uint64ToBinaryString(u64, help);
  } else {
    a1 = arr;
  }
  if (other.arr == nullptr) {
    a2 = help;
    i2 = 64;
    uint64ToBinaryString(other.u64, help);
  } else {
    a2 = other.arr;
  }

  char *res = (char *)malloc(sizeof(char) * (bitWidth + 1));

  while (i1 > 0 || i2 > 0) {
    unsigned c1 = 0, c2 = 0;
    if (i1 > 0) {
      c1 = a1[--i1] - '0';
    }
    if (i2 > 0) {
      c2 = a2[--i2] - '0';
    }
    unsigned v = c1 + c2 + overflow;
    res[--i] = (char)('0' + (v & 1));
    overflow = v >> 1;
  }
  res[bitWidth] = '\0';
  return BigNum(res, bitWidth);
}

bool BigNum::operator==(const BigNum &other) const {
  assert(bitWidth == other.bitWidth);
  if (arr == nullptr && other.arr == nullptr) {
    return u64 == other.u64;
  }
  if (arr != nullptr && other.arr != nullptr) {
    return strcmp(arr, other.arr) == 0;
  }
  uint64_t n;
  char *a;
  if (arr != nullptr) {
    a = arr;
    n = other.u64;
  } else {
    a = other.arr;
    n = u64;
  }
  for (int i = bitWidth; i > 0; i--) {
    char item = (char)(n & 1);
    n >>= 1;
    if (a[i - 1] != item) {
      return false;
    }
  }
  return true;
}

bool BigNum::operator<(const BigNum &other) const {
  assert(bitWidth == other.bitWidth);
  if (arr == nullptr && other.arr == nullptr) {
    return u64 < other.u64;
  }
  if (arr != nullptr && other.arr != nullptr) {
    return strcmp(arr, other.arr) < 0;
  }
  uint64_t n;
  char *a;
  bool invert = false;
  if (arr != nullptr) {
    a = arr;
    n = other.u64;
  } else {
    a = other.arr;
    n = u64;
    invert = true;
  }
  for (int i = bitWidth - 1; i >= 64; i--) {
    if (a[i] == '1') {
      return invert; // a > n
    }
  }
  for (int i = bitWidth; i > 0; i--) {
    char item = (n & (1ull << (i - 1))) >> (i - 1);
    if (a[i - 1] > item)
      return invert;
    else if (a[i - 1] < item)
      return !invert;
  }
  return false;
}

bool BigNum::operator<=(const BigNum &other) const {
  assert(bitWidth == other.bitWidth);
  if (arr == nullptr && other.arr == nullptr) {
    return u64 <= other.u64;
  }
  if (arr != nullptr && other.arr != nullptr) {
    return strcmp(arr, other.arr) <= 0;
  }
  uint64_t n;
  char *a;
  bool invert = false;
  if (arr != nullptr) {
    a = arr;
    n = other.u64;
  } else {
    a = other.arr;
    n = u64;
    invert = true;
  }
  for (int i = bitWidth - 1; i >= 64; i--) {
    if (a[i] == '1') {
      return invert; // a > n
    }
  }
  for (int i = bitWidth; i > 0; i--) {
    char item = (n & (1ull << (i - 1))) >> (i - 1);
    if (a[i - 1] > item)
      return invert;
    else if (a[i - 1] < item)
      return !invert;
  }
  return true;
}

char BigNum::extract(size_t pos) const {
  if (arr == nullptr) {
    if (pos >= 64) {
      return 0;
    }
    return (char)((u64 & (1ull << pos)) >> pos);
  }
  return arr[pos] - '0';
}

}
