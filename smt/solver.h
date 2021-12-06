#pragma once

// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "smt/expr.h"
#include <cassert>
#include <ostream>
#include <string>
#include <utility>
#include <functional>

typedef struct _Z3_model* Z3_model;
typedef struct _Z3_solver* Z3_solver;
typedef struct _Z3_solver_callback* Z3_solver_callback;

namespace smt {

class PropagatorBase;

class Model {
  Z3_model m;

  Model() : m(0) {}
  Model(Z3_model m);
  ~Model();

  friend class Result;

public:
  Model(Model &&other) noexcept : m(0) {
    std::swap(other.m, m);
  }

  void operator=(Model &&other);

  expr operator[](const expr &var) const { return eval(var, true); }
  expr eval(const expr &var, bool complete = false) const;
  uint64_t getUInt(const expr &var) const;
  int64_t getInt(const expr &var) const;
  bool hasFnModel(const expr &fn) const;

  class iterator {
    Z3_model m;
    unsigned idx;
    iterator(Z3_model m, unsigned idx) : m(m), idx(idx) {}
  public:
    void operator++(void) { ++idx; }
    std::pair<expr, expr> operator*(void) const; // <var, value>
    bool operator!=(const iterator &rhs) const { return idx != rhs.idx; }
    friend class Model;
  };

  // WARNING: the parent Model class has to be alive while iterators are in use.
  iterator begin() const;
  iterator end() const;

  friend std::ostream& operator<<(std::ostream &os, const Model &m);
};


class Result {
public:
  enum answer { UNSAT, SAT, INVALID, SKIP, TIMEOUT, ERROR };

  Result() : a(ERROR) {}

  bool isSat() const { return a == SAT; }
  bool isUnsat() const { return a == UNSAT; }
  bool isInvalid() const { return a == INVALID; }
  bool isSkip() const { return a == SKIP; }
  bool isTimeout() const { return a == TIMEOUT; }
  bool isError() const { return a == ERROR; }

  auto& getReason() const { return reason; }

  const Model& getModel() const {
    assert(isSat());
    return m;
  }

  void printModel();

private:
  Model m;
  answer a;
  std::string reason;

  Result(answer a) : a(a) {}
  Result(answer a, std::string &&reason) : a(a), reason(std::move(reason)) {}
  Result(Z3_model m) : m(m), a(SAT) {}

  friend class Solver;
};

enum SolverType {
  Simple,
  Tactics,
  SimpleWithPreprocessing
};

class Solver {
  Z3_solver s;
  SolverType type;
  bool valid = true;
  bool is_unsat = false;

public:
  Solver(SolverType type = SolverType::Tactics);

  ~Solver();

  void add(const expr &e);
  // use a negated solver for minimization
  void block(const Model &m, Solver *sneg = nullptr);
  void reset();

  expr assertions() const;

  Result check() const;

  friend class SolverPush;
  friend class PropagatorBase;
};

Result check_expr(const expr &e);


class SolverPush {
  Solver &s;
  bool valid, is_unsat;
public:
  SolverPush(Solver &s);
  ~SolverPush();
};

class PropagatorBase {

  typedef std::function<void(unsigned, expr const &)> fixed_eh_t;
  typedef std::function<void(void)> final_eh_t;
  typedef std::function<void(unsigned, unsigned)> eq_eh_t;

  final_eh_t m_final_eh;
  eq_eh_t m_eq_eh;
  fixed_eh_t m_fixed_eh;
  Solver *s;
  Z3_solver_callback cb { nullptr };

  struct scoped_cb {
    PropagatorBase &p;
    scoped_cb(void *_p, Z3_solver_callback cb)
        : p(*static_cast<PropagatorBase *>(_p)) {
      p.cb = cb;
    }
    ~scoped_cb() {
      p.cb = nullptr;
    }
  };

  static void push_eh(void *p) {
    static_cast<PropagatorBase *>(p)->push();
  }

  static void pop_eh(void *p, unsigned num_scopes) {
    static_cast<PropagatorBase *>(p)->pop(num_scopes);
  }

  static void *fresh_eh(void *p, Z3_context context) {
    return static_cast<PropagatorBase *>(p)->fresh(context);
  }

  static void fixed_eh(void *_p, Z3_solver_callback cb, unsigned id,
                       Z3_ast _value) {
    PropagatorBase *p = static_cast<PropagatorBase *>(_p);
    scoped_cb _cb(p, cb);
    expr value(_value);
    static_cast<PropagatorBase *>(p)->m_fixed_eh(id, value);
  }

  static void eq_eh(void *p, Z3_solver_callback cb, unsigned x, unsigned y) {
    scoped_cb _cb(p, cb);
    static_cast<PropagatorBase *>(p)->m_eq_eh(x, y);
  }

  static void final_eh(void *p, Z3_solver_callback cb) {
    scoped_cb _cb(p, cb);
    static_cast<PropagatorBase *>(p)->m_final_eh();
  }

public:
  PropagatorBase(Solver *s);

  virtual void push() = 0;
  virtual void pop(unsigned num_scopes) = 0;

  virtual ~PropagatorBase() = default;

  virtual PropagatorBase *fresh(Z3_context ctx) = 0;

  void register_fixed();

  void register_eq();

  void register_final();

  virtual void fixed(unsigned, expr const &) {}

  virtual void eq(unsigned, unsigned) {}

  virtual void final() {}

  unsigned register_expr(expr const &e);

  void conflict(unsigned num_fixed, unsigned const *fixed);

  void propagate(unsigned num_fixed, unsigned const *fixed,
                 expr const &conseq);

  void propagate(unsigned num_fixed, unsigned const *fixed, unsigned num_eqs,
                 unsigned const *lhs, unsigned const *rhs, expr const &conseq);
};

void solver_print_queries(bool yes);
void solver_tactic_verbose(bool yes);
void solver_print_stats(std::ostream &os);


struct EnableSMTQueriesTMP {
  bool old;
  EnableSMTQueriesTMP();
  ~EnableSMTQueriesTMP();
};


void solver_init();
void solver_destroy();

}
