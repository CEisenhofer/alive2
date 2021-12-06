#pragma once

// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "ir/function.h"
#include "ir/state.h"
#include "smt/solver.h"
#include "util/errors.h"
#include <memory>
#include <ostream>
#include <unordered_map>
#include <stack>

namespace tools {
struct BlockFieldInfo;
}

template<>
struct std::hash<tools::BlockFieldInfo> {
  std::size_t operator()(const tools::BlockFieldInfo &k) const;
};

namespace tools {

struct TransformPrintOpts {
  bool print_fn_header = true;
};

struct Transform {
  std::string name;
  IR::Function src, tgt;
  IR::Predicate *precondition = nullptr;

  void preprocess();

  void print(std::ostream &os, const TransformPrintOpts &opt) const;

  friend std::ostream &operator<<(std::ostream &os, const Transform &t);
};


class TypingAssignments {
  smt::Solver s, sneg;
  smt::Result r;
  bool has_only_one_solution = false;
  bool is_unsat = false;
  TypingAssignments(const smt::expr &e);

public:
  bool operator!() const { return !(bool)*this; }
  operator bool() const;
  void operator++(void);
  bool hasSingleTyping() const { return has_only_one_solution; }

  friend class TransformVerify;
};


class TransformVerify {
  Transform &t;
  std::unordered_map<std::string, const IR::Instr*> tgt_instrs;
  bool check_each_var;

public:
  TransformVerify(Transform &t, bool check_each_var);
  std::pair<std::unique_ptr<IR::State>,std::unique_ptr<IR::State>> exec() const;
  util::Errors verify() const;
  TypingAssignments getTypings() const;
  void fixupTypes(const TypingAssignments &ty);
};


void print_model_val(std::ostream &os, const IR::State &st, const smt::Model &m,
                     const IR::Value *var, const IR::Type &type,
                     const IR::StateValue &val, unsigned child = 0);

struct Interval {
  // [start; end)
  // start and end are constants

  smt::expr start;
  smt::expr end;
  unsigned bid;

  Interval();

  Interval(const Interval &o) = default;

  Interval(const smt::expr &start, const smt::expr &end);

  bool intersect(const Interval &o) const;

  bool isPositive() const;

  bool isNegative() const;

  std::string toString() {
    return "[" + start.toString() + ", " + end.toString() + ")";
  }

};

bool operator<(const Interval &o1, const Interval &o2);

bool operator==(const Interval &o1, const Interval &o2);

// Tests interval intersections in log(n) time
class IntervalTree : public std::set<Interval> {

public:

  // returns true if there is an intersection (interval not added and collision set to corresponding interval)
  // or return false if there was no intersection (interval added if positive)
  bool addOrIntersect(const Interval &interval, Interval *collision);
};

struct BlockFieldInfo {

  enum BlockFieldInfoEnum : unsigned char {
    None = 0,
    BlockAddress = 1,
    BlockSize = 2,
  };

  BlockFieldInfoEnum field;
  unsigned bid;

  BlockFieldInfo() : field(None), bid(0) {}

  BlockFieldInfo(const BlockFieldInfo &) = default;

  BlockFieldInfo(BlockFieldInfoEnum field, unsigned bid) : field(field), bid(bid) {}


  bool operator==(const BlockFieldInfo &other) const {
    return field == other.field && bid == other.bid;
  }

  std::string toString() {
    return "Bid: " + std::to_string(bid) + "; " + (field == None ? "None" : field == BlockAddress ? "Address" : "Size");
  }
};

struct BlockData {

  unsigned bid;
  smt::expr addr;
  smt::expr size; // Not extended/truncated. The unaltered constant
  smt::expr align;

  BlockData() : bid(UINT32_MAX) {}

  BlockData(unsigned int bid, const smt::expr &addr, const smt::expr &size, const smt::expr &align)
          : bid(bid), addr(addr), size(size), align(align) {}

  BlockData(const BlockData &) = default;

  std::string toString() {
    return "Block: " + std::to_string(bid) +
           "; addr: " + addr.toString() + "; size: " + size.toString() + "; align: " + align.toString();
  }
};

class MemoryAxiomPropagator : public smt::Solver, smt::PropagatorBase {

  const IR::Memory &src_memory, &tgt_memory;

  std::unordered_map<unsigned, BlockFieldInfo>
          idToFieldMapping; // Maps Z3 propagator id -> block information field (inverse from fieldToIdMapping)
  std::unordered_map<BlockFieldInfo, unsigned>
          fieldToIdMapping; // Maps block information field -> Z3 propagator id (inverse from idToFieldMapping)
  std::unordered_map<unsigned, BlockData> bidToExprMapping; // Maps bid to the z3 expressions

  // TODO: Make it work for more than 64 bit (arbitrary integers: performance problem)
  std::unordered_map<BlockFieldInfo, smt::expr> model; // Maps bid field info -> value of that field

  std::vector<BlockFieldInfo> fixedValues; // The fixed values in the order they were assigned
  std::vector<Interval> intervalValues; // The complete memory-blocks in the order they were completed

  std::stack<unsigned> fixedCnt; // Number of fixed values per decision level
  std::stack<unsigned> intervalCnt; // Number of complete memory-blocks per decision level

  // The addresses + sizes in the memory (used for block disjointness)
  // Tag: bid (unsigned)
  IntervalTree blockIntervals;

  void registerBlocks();

public:
  MemoryAxiomPropagator(const IR::Memory &src_memory,
                        const IR::Memory &tgt_memory);

  ~MemoryAxiomPropagator() override = default;

  void push() override;

  void pop(unsigned num_scopes) override;

  PropagatorBase *fresh(Z3_context ctx) override;

  void fixed(unsigned int i, const smt::expr &expr) override;

  void final() override;

  static smt::Result check_expr(const IR::Memory &src_memory,
                                const IR::Memory &tgt_memory,
                                const smt::expr &e) {
    MemoryAxiomPropagator s(src_memory, tgt_memory);
    s.add(e);
    smt::Result result = s.check();
    if (result.isSat()) {
      result.printModel();
    }
    return result;
  }
};

} // namespace tools
