// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "tools/lazy_instantiation.h"
#include "tools/transform.h"

// #define VERBOSE
#ifdef VERBOSE
#include <iostream>
#define WriteEmptyLine std::cout << std::endl
#define WriteLine(x) std::cout << (x) << std::endl
#define Write(x) std::cout << x
#else
#define WriteEmptyLine
#define WriteLine(x)
#define Write(x)
#endif

using namespace IR;
using namespace smt;
using namespace tools;
using namespace util;
using namespace std;

namespace tools {

Interval::Interval(const BigNum &start, const BigNum &end) : start(start), end(end) {}

bool Interval::intersect(const Interval &o) const {
  return start >= o.end || o.start >= end;
}

bool Interval::is_positive() const {
  return start < end;
}

bool Interval::is_negative() const {
  return end < start;
}

bool Interval::overlaps(Interval::value_type l, Interval::value_type h) const {
  return start <= h && l <= end;
}

bool Interval::overlaps_exclusive(Interval::value_type l, Interval::value_type h) const {
  return start < h && l < end;
}

bool Interval::within(Interval::value_type value) const {
    return value >= start && value <= end;
}

bool Interval::within(const Interval & other) const {
    return start <= other.start && end >= other.end;
}

Interval::value_type Interval::operator-(const Interval & other) const {
    if (overlaps(other))
        return value_type((uint64_t)0, start.bits());
    if (end < other.start)
        return other.start - end;
    else
        return start - other.end;
}

Interval Interval::join(const Interval & other) const {
    auto& min = start < other.start ? start : other.start;
    auto& max = end > other.end ? end : other.end;
    return Interval(min, max);
}

void IntervalTree::add(const Interval &interval, unsigned instance, FixedComplex<std::pair<unsigned, unsigned>, HashPair>& collisions) {
  if (interval.is_negative()) {
    return;
  }
  if (this->empty()) {
    this->insert(interval);
    return;
  }
  this->overlap_find_all(interval, [&](auto iter) {
    unsigned a = interval.id, b = iter->interval().id;
    unsigned lower = a < b ? a : b;
    unsigned higher = a > b ? a : b;
    // add the conflicting indexes ordered (to generate nice looking terms)
    collisions.tryAdd(instance, std::make_pair(lower, higher));
    return true;
  }, true);
  this->insert(interval);
}
}

// sub user-propagator for local axioms
MemoryAxiomPropagator::MemoryAxiomPropagator(smt::context* c, const Memory &src, const Memory &tgt, const std::unordered_map<std::string, std::vector<IR::State::MemoryBlockExpressions>*>& userFunctionsToInfo)
        : PropagatorBase(c), src_memory(src), tgt_memory(tgt), userFunctionsToInfo(userFunctionsToInfo) {
  register_fixed();
  register_final();
  register_created();
}

// user-propagator for global axioms
MemoryAxiomPropagator::MemoryAxiomPropagator(Solver& s, const Memory &src, const Memory &tgt, const std::unordered_map<std::string, std::vector<IR::State::MemoryBlockExpressions>*>& userFunctionsToInfo)
        : PropagatorBase(&s), src_memory(src), tgt_memory(tgt), userFunctionsToInfo(userFunctionsToInfo) {
  register_fixed();
  register_final();
  register_created();
}

MemoryAxiomPropagator::~MemoryAxiomPropagator() {
  for (auto& block : blocks)
    delete block;
  for (auto& ptr : currentInterpretation)
    delete ptr.second;
  if (subPropagator) {
      delete subPropagator;
  }
}

void MemoryAxiomPropagator::push() {
  fixedValuesCnt.push(fixedValues.size());
  fixedBlocksCnt.push(fixedBlock.size());
  collisions.push();
  overflows.push();
}

void MemoryAxiomPropagator::pop(unsigned int num_scopes) {
  for (unsigned i = 0; i < num_scopes; i++) {
    unsigned previousFixedCnt = fixedValuesCnt.top();
    unsigned previousIntervalCnt = fixedBlocksCnt.top();
    fixedValuesCnt.pop();
    fixedBlocksCnt.pop();
    for (auto j = fixedValues.size(); j > previousFixedCnt; j--) {
      fixedValues[j - 1]->remove();
    }
    for (auto j = fixedBlock.size(); j > previousIntervalCnt; j--) {
      auto value = fixedBlock[j - 1];
      intervalTrees[value.first->instance].remove(value.second);
      hasFixedBlock[value.first->instance].erase(value.first);
    }

    fixedValues.resize(previousFixedCnt);
    fixedBlock.resize(previousIntervalCnt);

    collisions.pop();
    overflows.pop();
  }
}

void MemoryAxiomPropagator::truePredicateWrongArgumentsLocal(PropagatorBlock* block1, PropagatorBlock* block2) {
  assert(block1->local && block2->local);
  if (block1->alive.contains(block2)) {
    FixedBoolValue* aliveValue = block1->alive.at(block2);
    if (aliveValue->isAssigned() && aliveValue->getValue()) {
      smt::expr disjoint =
        (block1->allocated->expr && aliveValue->expr).implies(
          disjointBlocks(
            block1->addr->expr, block1->size->expr.zextOrTrunc(bits_ptr_address), block1->align,
            block2->addr->expr, block2->size->expr.zextOrTrunc(bits_ptr_address), block2->align
          )
        );
      WriteLine(
        "Interval intersection (local): " + Interval(block1->addr->getValue(), block1->addr->getValue() + block1->addr->getValue()).to_string() +
        " and " + Interval(block2->addr->getValue(), block2->addr->getValue() + block2->addr->getValue()).to_string()
      );
      this->propagate(0, nullptr, block1->func->expr.implies(disjoint));
    }
  }
}

void MemoryAxiomPropagator::truePredicateWrongArgumentsGlobal(PropagatorBlock* block1, PropagatorBlock* block2) {
  assert(!block1->local && !block2->local);
  smt::expr disjoint =
    disjointBlocks(
      block1->addr->expr, block1->size->expr.zextOrTrunc(bits_ptr_address), block1->align,
      block2->addr->expr, block2->size->expr.zextOrTrunc(bits_ptr_address), block2->align
    );
  WriteLine(
    "Interval intersection (global): " + Interval(block1->addr->getValue(), block1->addr->getValue() + block1->addr->getValue()).to_string() +
    " and " + Interval(block2->addr->getValue(), block2->addr->getValue() + block2->addr->getValue()).to_string()
  );
  this->propagate(0, nullptr, block1->func->expr.implies(disjoint));
}

void MemoryAxiomPropagator::falsePredicateTrueArguments(unsigned instance, const FixedBoolValue* func) {

  std::vector<smt::expr> conflicting;

  for (const std::pair<unsigned, unsigned> &collision : collisions.getValues(instance)) {
    PropagatorBlock* block1 = blocks.at(collision.first);
    PropagatorBlock* block2 = blocks.at(collision.second);
    if (block1->alive.contains(block2)) {
      if (!block1->alive.at(block2)->isAssigned() || block1->alive.at(block2)->getValue())
        return; // there is either an alive value missing or we already found an invalid placement
      if (!block1->alive.at(block2)->expr.isConst())
        conflicting.push_back(block1->alive.at(block2)->expr);
    }
    if (block2->alive.contains(block1)){
      if (!block2->alive.at(block1)->isAssigned() || block2->alive.at(block1)->getValue())
        return;
      if (!block2->alive.at(block1)->expr.isConst())
        conflicting.push_back(block2->alive.at(block1)->expr);
    }
  }
  unsigned argCnt = func->expr.getFnArgCnt();
  for (unsigned i = 0; i < argCnt; i++) {
    smt::expr arg = func->expr.getFnArg(i);
    if (!arg.isConst())
      conflicting.push_back(arg);
  }
  conflicting.push_back(func->expr);
  this->conflict(conflicting.size(), conflicting.data());
}

void MemoryAxiomPropagator::checkPredicate(unsigned instance, const FixedBoolValue* func) {

  assert(func != nullptr);
  assert(!func->containedBlocks.empty());

  if (!func->isAssigned())
    return; // We do not know whether to expect intersections or not

  bool val = func->getValue();

  if (val) {
    // Ordinary global addresses may not be zero
    if (!func->containedBlocks[0]->local &&
        func->containedBlocks[0]->addr->isAssigned() &&
        func->containedBlocks[0]->addr->getValue().isZero()) {

      // considering only index 0 as global axioms only occur in a single function application
      std::vector<expr> conflicting;
      conflicting.push_back(func->expr);
      if (!func->containedBlocks[0]->addr->expr.isConst()) {
        conflicting.push_back(func->containedBlocks[0]->addr->expr);
      }
      this->conflict(conflicting.size(), conflicting.data());
      return;
    }
    // We expect that the blocks are disjoint
    for (auto& collision : collisions.getValues(instance)) {
      PropagatorBlock* block1 = blocks[collision.first];
      PropagatorBlock* block2 = blocks[collision.second];
      assert(block1->instance == instance && block2->instance == instance);
      assert(block1->func == func && block2->func == func);
      if (block1->local) {
        truePredicateWrongArgumentsLocal(block1, block2);
        // We may add both (not symmetric because of alive-property)
        truePredicateWrongArgumentsLocal(block2, block1);
      }
      else{
        // this is symmetric so we call it only once
        truePredicateWrongArgumentsGlobal(block1, block2);
      }
    }
    // only for global axioms (otherwise always empty)
    for (auto& overflow : overflows.getValues(instance)) {
      PropagatorBlock* block1 = blocks[overflow];
      // global memory overflows
      auto truncatedSize = block1->size->expr.zextOrTrunc(bits_ptr_address);
      WriteLine("Added overflow: " + Interval(block1->addr->getValue(), block1->addr->getValue() + block1->addr->getValue()).to_string());

      this->propagate(0, nullptr,
        func->expr.implies(
          Pointer::hasLocalBit()
          // don't spill to local addr section
          ? (block1->addr->expr + truncatedSize).extract(bits_ptr_address - 1, bits_ptr_address - 1) == 0
          : block1->addr->expr.add_no_uoverflow(truncatedSize.zextOrTrunc(bits_ptr_address))
        )
      );
    }
  }
  else {
    // We expect that the blocks are not disjoint
    if (!overflows.empty(instance) || intervalTrees[instance].size() < func->containedBlocks.size())
      return;
    WriteLine("Encountered critical situation...");
    // ... but the assignment is fine and all blocks are assigned
    // we either not say d(addr1, size1, ..., addrn, sizen) => disj(addr1, ..., sizen)
    // or just add a conflict between everything for memory reasons
    falsePredicateTrueArguments(instance, func);
  }
}

void MemoryAxiomPropagator::fixBlock(PropagatorBlock* block) {

  if (!block->isComplete() || hasFixedBlock[block->instance].contains(block))
    return;

  Interval interval(block->addr->getValue(), block->addr->getValue() + block->size->getValue());
  interval.id = block->id;

  if (!block->local && Pointer::hasLocalBit()
      ? interval.end.extract(bits_ptr_address - 1) != 0
      : !(interval.end >= block->addr->getValue() && interval.end >= block->size->getValue())) {

    overflows.tryAdd(block->instance, block->id);
  } else {
    intervalTrees[block->instance].add(interval, block->instance, collisions);
    WriteLine("Added interval: " + interval.to_string() + " for " + to_string(block->instance));
    assert(intervalTrees[block->instance].size() <= block->func->containedBlocks.size());
    assert(collisions.size(block->instance) <= block->func->containedBlocks.size() * block->func->containedBlocks.size());
    fixedBlock.emplace_back(block, interval);
    hasFixedBlock[block->instance].emplace(block);
  }
}

void MemoryAxiomPropagator::fixed(const expr& ast, const expr &v) {

  WriteLine("Fixed " + ast.toString() + " to " + v.toString());

  FixedValue* value = currentInterpretation.at(ast);
  assert(!value->isAssigned());
  assert(!value->isConstant());

  value->add(v);
  fixedValues.push_back(value);

  if (value->argument == Func) {
    for (const auto& block : value->containedBlocks) {
      fixBlock(block);
    }
    checkPredicate(value->containedBlocks[0]->instance, (FixedBoolValue*)value);
  }
  else {
    for (const auto& block : value->containedBlocks) {
      fixBlock(block);
      checkPredicate(block->instance, block->func);
    }
  }
}

FixedBoolValue* MemoryAxiomPropagator::registerBoolArgument(smt::expr argExpr, Argument argument) {
  auto it = currentInterpretation.find(argExpr);
  FixedBoolValue* value;
  if (it == currentInterpretation.end()) {
    value = new FixedBoolValue(argument, argExpr);
    currentInterpretation.emplace(argExpr, value);
    if (!argExpr.isConst()) {
      register_expr(argExpr);
      WriteLine("Registered: " + argExpr.toString());
    }
  }
  else {
    value = (FixedBoolValue*)it->second;
  }
  return value;
}

FixedNumericValue* MemoryAxiomPropagator::registerNumericArgument(smt::expr argExpr, Argument argument, unsigned size) {
  auto it = currentInterpretation.find(argExpr);
  FixedNumericValue* value;
  if (it == currentInterpretation.end()) {
    value = new FixedNumericValue(argument, argExpr, size);
    currentInterpretation.emplace(argExpr, value);
    if (!argExpr.isConst()) {
      register_expr(argExpr);
      WriteLine("Registered: " + argExpr.toString());
    }
  }
  else {
    value = (FixedNumericValue*)it->second;
  }
  return value;
}

void MemoryAxiomPropagator::created(const smt::expr &ast) {
  WriteLine("Created: " + ast.toString());

  const std::vector<IR::State::MemoryBlockExpressions>* blockData = userFunctionsToInfo.at(ast.fn_name());

  intervalTrees.emplace_back();
  collisions.addInstance();
  overflows.addInstance();
  hasFixedBlock.emplace_back();

  auto funcValue = new FixedBoolValue(Argument::Func, ast);
  currentInterpretation.emplace(ast, funcValue);

  unsigned prevBlockCnt = blocks.size();
  std::vector<unsigned> aliveStarts;

  unsigned argCnt = ast.getFnArgCnt();

  unsigned i = 0;
  unsigned blockId = 0;

  while (i < argCnt) {

    const IR::State::MemoryBlockExpressions &blockExpressions = (*blockData)[blockId++];
    FixedNumericValue *addrValue;
    FixedNumericValue *sizeValue;
    FixedBoolValue *allocatedValue;

    smt::expr addr = ast.getFnArg(i++);
    addrValue = registerNumericArgument(addr, Argument::Addr, addr.bits());

    smt::expr size = ast.getFnArg(i++);
    sizeValue = registerNumericArgument(size, Argument::Size, IR::bits_ptr_address);

    if (blockExpressions.allocatedExpr.isTrue() || blockExpressions.allocatedExpr.isFalse()) {
      // all instances will be true/false
      // the argument was only passed indirectly
      allocatedValue = registerBoolArgument(blockExpressions.allocatedExpr, Argument::Allocated);
    }
    else {
      smt::expr allocated = ast.getFnArg(i++);
      allocatedValue = registerBoolArgument(allocated, Argument::Allocated);
    }

    auto block = new PropagatorBlock(blocks.size(), intervalTrees.size() - 1, blockExpressions.local,
                                     addrValue, sizeValue, funcValue, allocatedValue, blockExpressions.alignExpr);
    blocks.push_back(block);

    aliveStarts.push_back(i), i += blockExpressions.collisionCandidates.size();

    addrValue->containedBlocks.push_back(block);
    sizeValue->containedBlocks.push_back(block);
    funcValue->containedBlocks.push_back(block);
    allocatedValue->containedBlocks.push_back(block);

    fixBlock(block);
  }

  // Link the alive-expressions to the corresponding blocks
  for (unsigned j = 0; j < blockData->size();  j++) {
    const IR::State::MemoryBlockExpressions &blockExpressions = (*blockData)[j];
    unsigned aliveStart = aliveStarts[j];
    PropagatorBlock* block = blocks[prevBlockCnt + j];

    for (unsigned k = 0; k < blockExpressions.collisionCandidates.size(); k++) {
      FixedBoolValue* aliveValue = registerBoolArgument(ast.getFnArg(aliveStart + k), Argument::Alive);
      block->alive.emplace(blocks[prevBlockCnt + blockExpressions.collisionCandidates[k].correspondingIndex], aliveValue);
      aliveValue->containedBlocks.push_back(block);
    }
  }
}

void MemoryAxiomPropagator::final() {
    WriteLine("Final");
}

PropagatorBase* MemoryAxiomPropagator::fresh(smt::context* c) {
    WriteLine("Fresh");
    return subPropagator = new MemoryAxiomPropagator(c, src_memory, tgt_memory, userFunctionsToInfo);
}

smt::Result MemoryAxiomPropagator::check_expr(const Memory & src_memory, const Memory & tgt_memory, const expr & e, const unordered_map<std::string, std::vector<IR::State::MemoryBlockExpressions> *> & userFunctionToInfo) {
  WriteLine(std::string("Problem: ") + e.toString());
  smt::Solver s(false);
  s.add(e);
  MemoryAxiomPropagator propagator(s, src_memory, tgt_memory, userFunctionToInfo);
  return s.check();
}
