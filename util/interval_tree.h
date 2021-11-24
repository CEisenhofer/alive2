#pragma once

// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include <set>

namespace util {

template<typename R, typename T>
struct Interval {
  // [start; end)

  R start;
  R end;
  T tag;

  Interval() : start(0), end(0) {}

  Interval(const Interval &o) : start(o.start), end(o.end), tag(o.tag) {}

  Interval(const R start, const R end) : start(start), end(end) {}

  bool intersect(const Interval &o) const {
    /*return
            (start >= o.start && start < o.end) ||
            (o.start >= start && o.start < end);*/
    return !(start >= o.end || o.start >= end);
  }

  bool isPositive() const {
    return start < end;
  }

  bool isNegative() const {
    return end < start;
  }

  std::string toString() {
    return "[" + std::to_string(start) + ", " + std::to_string(end) + ")";
  }

};

template<typename R, typename T>
bool operator<(const Interval<R, T> &o1, const Interval<R, T> &o2) {
  return
          o1.start < o2.start ||
          (o1.start == o2.start && o1.end > o2.end
                  /*special case for 0-intervals. Put 0-intervals higher up than non-zero ones */
          ) ||
          (o1.start == o2.start && o1.end == o2.end && o1.tag < o2.tag);
}

template<typename R, typename T>
bool operator==(const Interval<R, T> &o1, const Interval<R, T> &o2) {
  return o1.start == o2.start && o1.end == o2.end && o1.tag == o2.tag;
}

// Tests interval intersections in log(n) time
template<typename R, typename T>
class IntervalTree : public std::set<Interval<R, T>> {

public:

  // returns true if there is an intersection (interval not added and collision set to corresponding interval)
  // or return false if there was no intersection (interval added if positive)
  bool addOrIntersect(const Interval<R, T> &interval, Interval<R, T> *collision) {
    if (interval.isNegative()) {
      return false;
    }
    if (this->empty()) {
      this->insert(interval);
      return false;
    }

    auto bound = this->upper_bound(interval);
    if (bound != this->end() && bound->intersect(interval)) {
      if (collision != nullptr) {
        *collision = *bound;
      }
      return true;
    }
    // consider the interval directly below. Skip all 0-intervals that might come before the relevant one
    while (bound != this->begin()) {
      bound--;
      if (bound->intersect(interval)) {
        if (collision != nullptr) {
          *collision = *bound;
        }
        return true;
      }
      if (bound->start != bound->end) {
        break;
      }
    }
    this->insert(bound, interval);
    return false;
  }

};
}
