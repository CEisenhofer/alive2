#pragma once

// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "ir/globals.h"
#include "ir/state.h"
#include "smt/ctx.h"
#include "smt/expr.h"
#include "smt/smt.h"
#include "smt/solver.h"
#include "ir/function.h"
#include "ir/state.h"
#include "ir/memory.h"
#include "smt/solver.h"
#include "util/big_num.h"
#include "util/interval_tree.hpp"
#include <memory>
#include <ostream>
#include <random>
#include <stack>
#include <unordered_map>

namespace tools {

enum Argument {
    Literal,
    Addr,
    Size,
    Func,
    Allocated,
    Alive,
};

struct PropagatorBlock;

class FixedValue {

protected:

    bool assigned = false;

public:

    smt::expr expr;
    std::vector<PropagatorBlock*> containedBlocks;
    const Argument argument;

    FixedValue(Argument argument, const smt::expr& expr) : expr(expr), argument(expr.isConst() ? Argument::Literal : argument) { }

    virtual ~FixedValue() = default;

    inline bool isAssigned() const {
      return assigned;
    }

    inline bool isConstant() const {
      return argument == Argument::Literal;
    }

    virtual void add(const smt::expr&) = 0;

    void remove() {
      assert(!isConstant());
      assigned = false;
    }

    virtual std::string toString() const = 0;
};

class FixedBoolValue : public FixedValue {

    bool value;

public:

    FixedBoolValue(Argument argument, const smt::expr& expr) : FixedValue(argument, expr) {
      add(expr);
    }

    void add(const smt::expr& expr) final {
      if (expr.isTrue()) {
        value = true;
        assigned = true;
      }
      else if (expr.isFalse()) {
        value = false;
        assigned = true;
      }
    }

    inline bool getValue() const { return value; }

    std::string toString() const final {
      return assigned ? "not-set" : value ? "true" : "false";
    };

};

class FixedNumericValue : public FixedValue {

    util::BigNum value;

public:

    FixedNumericValue(Argument argument, const smt::expr& expr, unsigned bits) : FixedValue(argument, expr), value(bits) {
      add(expr);
    }

    void add(const smt::expr& expr) final {
      if (!expr.isConst())
        return;
      assigned = true;
      uint64_t i;
      if (expr.isUInt(i))
        value.set(i);
      else
        value.set(expr.getBinaryString());
    }

    inline const util::BigNum& getValue() const { return value; }

    std::string toString() const final {
      return assigned ? "not-set" : value.toString();
    };
};

struct PropagatorBlock {

    const smt::expr align;

    const FixedNumericValue* addr;
    const FixedNumericValue* size;
    const FixedBoolValue* func;
    const FixedBoolValue* allocated;
    std::unordered_map<PropagatorBlock*, FixedBoolValue*> alive;

    const unsigned id; // not necessarily the bid; just a unique and incrementally generated id within a propagator-object
    const unsigned instance; // the number of previous MBQI checks
    const bool local;

    PropagatorBlock(unsigned id, unsigned instance, bool local, FixedNumericValue* addr, FixedNumericValue* size,
                    FixedBoolValue* func, FixedBoolValue* allocated, const smt::expr& align)
      : align(align), addr(addr), size(size), func(func), allocated(allocated), id(id), instance(instance), local(local) { }

    bool isPartiallyComplete() const {
      return addr->isAssigned() && size->isAssigned();
    }
};

template<typename T, typename __Hash = std::hash<T>>
class FixedComplex {

    // size of the (outer) vectors is the same
    std::vector<std::stack<size_t>> prevCnts;
    std::vector<std::vector<T>> list;
    std::vector<std::unordered_set<T, __Hash>> set;

public:

    inline void push() {
      for (unsigned i = 0; i < list.size(); i++) {
        prevCnts[i].push(list[i].size());
      }
    }

    inline void pop() {
      for (unsigned i = 0; i < list.size(); i++) {
        if (prevCnts[i].empty()) {
          // some instances were added later
          continue;
        }
        unsigned prevCnt = prevCnts[i].top();
        prevCnts[i].pop();
        std::vector<T> &curr = list[i];
        for (unsigned j = curr.size(); j > prevCnt; j--) {
          set[i].erase(curr[j - 1]);
        }
        curr.resize(prevCnt);
      }
    }

    inline size_t size(unsigned instance) const {
      return list[instance].size();
    }

    inline bool empty(unsigned instance) const {
      return list[instance].empty();
    }

    inline void addInstance() {
      prevCnts.emplace_back();
      list.emplace_back();
      set.emplace_back();
    }

    inline void tryAdd(unsigned instance, const T& v) {
      if (!isContained(instance, v)) {
        list[instance].push_back(v);
        set[instance].emplace(v);
      }
    }

    inline bool isContained(unsigned instance, const T &v) const {
      return set[instance].contains(v);
    }

    inline std::vector<T>& getValues(unsigned instance) {
      return list[instance];
    }
};

struct HashPair {
    std::size_t operator()(const std::pair<unsigned, unsigned> &v) const {
      // rather unlikely that there is a collision for small values
      return (v.first << (sizeof(unsigned) * 8 / 2)) ^ v.second;
    }
};

struct Interval {
    // [start; end)
    // start and end are constants

    using value_type = util::BigNum;

    value_type start;
    value_type end;
    unsigned id;

    Interval() {
      assert(false); // just here to avoid std::vector<Interval>::resize complaining. The size won't increase!
    }

    Interval(const Interval &o) = default;

    Interval(const value_type &start, const value_type &end);

    bool intersect(const Interval &o) const;

    bool is_positive() const;

    bool is_negative() const;

    std::string to_string() {
        return "[" + start.toString() + ", " + end.toString() + ")";
    }

    friend bool operator==(Interval const& lhs, Interval const& rhs) {
        return lhs.start == rhs.start && lhs.start == rhs.start && lhs.id == rhs.id;
    }

    friend inline bool operator!=(Interval const& lhs, Interval const& rhs) {
        return !(lhs == rhs);
    }

    value_type low() const { return start; }

    value_type high() const { return end; }

    bool overlaps(value_type l, value_type h) const;

    bool overlaps_exclusive(value_type l, value_type h) const;

    bool overlaps(Interval const& other) const {
        return overlaps(other.start, other.end);
    }

    bool overlaps_exclusive(Interval const& other) const {
        return overlaps_exclusive(other.start, other.end);
    }

    bool within(value_type value) const;

    bool within(Interval const& other) const;

    value_type operator-(Interval const& other) const;

    value_type size() const { return end - start; }

    Interval join(Interval const& other) const;
};

// Tests interval intersections in log(n) time
class IntervalTree : private util::interval_tree<Interval> {

public:

  void add(const Interval &interval, unsigned instance, FixedComplex<std::pair<unsigned, unsigned>, HashPair>& collisions);

  void remove(const Interval &interval) {
    auto it = this->find(interval);
    if (it == this->end()) {
      // assert(false); <-- this should not happen
      return;
    }
    erase(it);
  }

  using util::interval_tree<Interval>::size;
};

class MemoryAxiomPropagator : public smt::PropagatorBase {

  const IR::Memory &src_memory, &tgt_memory;

  std::vector<PropagatorBlock*> blocks;
  std::unordered_map<smt::expr, FixedValue*> currentInterpretation;

  std::stack<size_t> fixedValuesCnt;
  std::vector<FixedValue*> fixedValues;

  std::stack<size_t> fixedBlocksCnt;
  std::vector<IntervalTree> intervalTrees;
  std::vector<std::pair<PropagatorBlock*, Interval>> fixedBlock;
  std::vector<std::unordered_set<PropagatorBlock*>> hasFixedBlock;


  FixedComplex<std::pair<unsigned, unsigned>, HashPair> collisions; // first block index is the smaller one
  FixedComplex<unsigned> overflows;
  std::vector<unsigned> refinements;

  std::unordered_map<std::string, std::vector<IR::State::MemoryBlockExpressions>*> userFunctionsToInfo;
  
  int decisionLevel = 0;
  std::vector<std::pair<int, smt::expr>> instantiate;
  PropagatorBase* subPropagator = nullptr;
  
  std::mt19937 gen;
  std::bernoulli_distribution dist;

  void checkPredicate(unsigned instance, const FixedBoolValue* func); // In case we already know if the predicate should be true/false we propagate new expressions in case the predicate was not assigned properly
  void fixBlock(PropagatorBlock* block); // Adds the given block to the interval tree

  FixedBoolValue* registerBoolArgument(const smt::expr& argExpr, Argument argument);
  FixedNumericValue* registerNumericArgument(const smt::expr& argExpr, Argument argument, unsigned size);

  void encodeCompletely(const std::vector<IR::State::MemoryBlockExpressions>* blockData, const std::vector<PropagatorBlock*>& b);
  
  void truePredicateWrongArgumentsLocal(PropagatorBlock *block1, PropagatorBlock *block2);
  void truePredicateWrongArgumentsGlobal(PropagatorBlock *block1, PropagatorBlock *block2);
  void falsePredicateTrueArguments(unsigned int instance, const FixedBoolValue *func);

public:

  MemoryAxiomPropagator(smt::context* c, const IR::Memory &src, const IR::Memory &tgt, const std::unordered_map<std::string, std::vector<IR::State::MemoryBlockExpressions>*>& userFunctionsToInfo);

  MemoryAxiomPropagator(smt::Solver& s, const IR::Memory &src, const IR::Memory &tgt, const std::unordered_map<std::string, std::vector<IR::State::MemoryBlockExpressions>*>& userFunctionsToInfo);

  ~MemoryAxiomPropagator() override;
  
  void push() override;

  void pop(unsigned num_scopes) override;

  PropagatorBase *fresh(smt::context* c) override;

  void fixed(const smt::expr &ast, const smt::expr &value) override;

  void created(const smt::expr &ast) override;
  
  void decide(const smt::expr &ast, const unsigned& bit, int& phase) override;

  void final() override;

  static smt::Result check_expr(const IR::Memory &src_memory,
                                const IR::Memory &tgt_memory,
                                const smt::expr &e,
                                const std::unordered_map<std::string, std::vector<IR::State::MemoryBlockExpressions>*>& userFunctionToInfo);
};
}