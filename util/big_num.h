#pragma once
#include <cstdint>
#include <string>

// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

namespace util {

// We could use also use arithmetic over z3 constants but this is slow
class BigNum {
  /**
   * Binary string
   * Contains exactly bitWidth 0/1.
   * If set to nullptr the value of u64 is taken
   */
  char *arr;
  /**
   * The number of bits
   */
  size_t bitWidth;
  /**
   * If number is short enough
   */
  uint64_t u64;

public:

  BigNum() : arr(nullptr), bitWidth(0), u64(0) {}

  BigNum(size_t bitWidth) : arr(nullptr), bitWidth(bitWidth), u64(0) {}

  BigNum(uint64_t u64, size_t bitWidth);

  BigNum(const char *arr, size_t bitWidth);

  BigNum(const BigNum &other);

  ~BigNum();

  static BigNum truncOrExtend(uint64_t u64, size_t toBitWidth);

  static BigNum truncOrExtend(const char *arr, size_t toBitWidth);

  BigNum operator+(const BigNum &other) const;

  bool operator==(const BigNum &other) const;

  bool operator!=(const BigNum &other) const { return !(*this == other); }

  bool operator<(const BigNum &other) const;

  bool operator<=(const BigNum &other) const;

  bool operator>(const BigNum &other) const { return other < *this; }

  bool operator>=(const BigNum &other) const { return other <= *this; }

  char extract(size_t pos) const;

  std::string toString() {
    return (arr == nullptr ? std::to_string(u64) : std::string(arr)) + " (" + std::to_string(bitWidth) + "bits)";
  }

};

}
