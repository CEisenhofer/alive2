#pragma once

// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "ir/function.h"
#include "ir/state.h"
#include "ir/memory.h"
#include "smt/solver.h"
#include "util/big_num.h"
#include "util/errors.h"
#include <memory>
#include <ostream>
#include <unordered_map>
#include <stack>

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
  std::unordered_map<std::string, const IR::Instr *> tgt_instrs;
  bool check_each_var;

public:
  TransformVerify(Transform &t, bool check_each_var);

  std::pair<std::unique_ptr<IR::State>, std::unique_ptr<IR::State>> exec() const;

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

  util::BigNum start;
  util::BigNum end;
  unsigned bid;

  Interval();

  Interval(const Interval &o) = default;

  Interval(const util::BigNum &start, const util::BigNum &end);

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
    BlockAlive = 3,
    BlockAllocated = 4,
  };


  IR::Memory::BlockData* block;
  BlockFieldInfoEnum field;

  BlockFieldInfo(IR::Memory::BlockData* block, BlockFieldInfoEnum field): block(block), field(field) {}
  BlockFieldInfo(const BlockFieldInfo& other) = default;
  BlockFieldInfo() = default;

  bool operator==(const BlockFieldInfo& other) const {
    return block == other.block && field == other.field;
  }

  void remove();

  void add(const smt::expr &expr);
};

class MemoryAxiomPropagator : public smt::Solver, smt::PropagatorBase {

  const IR::Memory &src_memory, &tgt_memory;

  std::vector<IR::Memory::BlockData*> registeredBlocks; // BlockFieldInfo and bidToData contain these pointers (==> these pointers are valid)

  std::unordered_map<unsigned, BlockFieldInfo> idToField; // Maps Z3 propagator id -> block information field
  std::unordered_map<unsigned, IR::Memory::BlockData*> bidToData; // Maps bid to the z3 expressions and (partial) model

  std::vector<BlockFieldInfo> fixedValues; // The fixed values in the order they were assigned
  std::vector<Interval> globalIntervalValues; // The complete global memory-blocks in the order they were completed
  std::vector<Interval> localIntervalValues; // The complete local memory-blocks in the order they were completed

  std::stack<unsigned> fixedCnt; // Number of fixed values per decision level
  std::stack<unsigned> globalIntervalCnt; // Number of complete global memory-blocks per decision level
  std::stack<unsigned> localIntervalCnt; // Number of complete local memory-blocks per decision level

  // The addresses + sizes in the memory (used for block disjointness)
  IntervalTree globalIntervals;
  IntervalTree localIntervals;

  // memory allocated by new -> deleted by destructor
  void registerBlock(IR::Memory::BlockData* toRegister);
  void registerLocalBlocks();
  void registerGlobalBlocks();

public:
  MemoryAxiomPropagator(const IR::Memory &src, const IR::Memory &tgt);

  ~MemoryAxiomPropagator() override;

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
#ifdef NDEBUG
    if (result.isSat()) {
      result.printModel();
    }
#endif
    return result;
  }
};

} // namespace tools
