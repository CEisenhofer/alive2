#pragma once
#include <cstdint>
#include <string>
#include <vector>

// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

namespace util {

// We could use also use arithmetic over z3 constants but this is slow
class BigNum {

  /**
   * Representation of the number
   */
  std::vector<uint64_t> arr;
  /**
   * The number of bits
   */
  size_t bitWidth;

public:

  BigNum();

  explicit BigNum(size_t bitWidth);

  BigNum(uint64_t u64, size_t bitWidth);

  BigNum(const char *arr, size_t bitWidth);

  BigNum(std::vector<uint64_t> &&arr, size_t bitWidth);

  BigNum(const BigNum &other);

  virtual ~BigNum();

  size_t bits() const {
    return bitWidth;
  }

  void set(uint64_t u64);

  void set(const char* a);

  BigNum operator+(const BigNum &other) const;

  BigNum operator-(const BigNum &other) const;

  bool operator==(const BigNum &other) const;

  bool operator!=(const BigNum &other) const { return !(*this == other); }

  bool operator<(const BigNum &other) const;

  bool operator<=(const BigNum &other) const;

  bool operator>(const BigNum &other) const { return other < *this; }

  bool operator>=(const BigNum &other) const { return other <= *this; }

  bool extract(size_t pos) const;

  bool isZero() const;

  std::string toString() const;

  std::string toString2() {
    return toString() + " (" + std::to_string(bitWidth) + "bits)";
  }

};

}
