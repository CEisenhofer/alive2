#pragma once

// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "smt/ctx.h"
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
  bool valid = true;
  bool is_unsat = false;

public:
  Solver(bool simple);

  ~Solver();

  void add(const expr &e);
  // use a negated solver for minimization
  void block(const Model &m, Solver *sneg = nullptr);
  void reset();

  expr assertions() const;

  Result check() const;
  Result check(std::vector<smt::expr> assumptions) const;

  std::string toString() const;

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

  typedef std::function<void(expr const &, expr const &)> fixed_eh_t;
  typedef std::function<void(void)> final_eh_t;
  typedef std::function<void(expr const &)> created_eh_t;

  final_eh_t m_final_eh;
  fixed_eh_t m_fixed_eh;
  created_eh_t m_created_eh;
  context* _ctx;
  Solver* _s;
  std::vector<smt::context*> subcontexts;

  Z3_solver_callback cb = nullptr;

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

  static void push_eh(void *p, Z3_solver_callback cb) {
    scoped_cb _cb(p, cb);
    static_cast<PropagatorBase *>(p)->push();
  }

  static void pop_eh(void *p, Z3_solver_callback cb, unsigned num_scopes) {
    scoped_cb _cb(p, cb);
    static_cast<PropagatorBase *>(p)->pop(num_scopes);
  }

  static void *fresh_eh(void *_p, Z3_context context) {
    PropagatorBase* p = static_cast<PropagatorBase*>(_p);
    smt::context* c = new smt::context();
    c->ctx = context;
    p->subcontexts.push_back(c);
    return p->fresh(c);
  }

  static void fixed_eh(void *_p, Z3_solver_callback cb, Z3_ast _ast, Z3_ast _value) {
    PropagatorBase *p = static_cast<PropagatorBase *>(_p);
    scoped_cb _cb(p, cb);
    expr value(_value);
    expr ast(_ast);
    static_cast<PropagatorBase *>(p)->m_fixed_eh(ast, value);
  }

  static void final_eh(void *p, Z3_solver_callback cb) {
    scoped_cb _cb(p, cb);
    static_cast<PropagatorBase *>(p)->m_final_eh();
  }

  static void created_eh(void *p, Z3_solver_callback cb, Z3_ast _ast) {
    scoped_cb _cb(p, cb);
    expr ast(_ast);
    static_cast<PropagatorBase *>(p)->m_created_eh(ast);
  }

public:
  PropagatorBase(context* ctx);
  PropagatorBase(Solver *s);

  context& ctx() { return *_ctx; }
  Solver& s() { return *_s; }

  virtual void push() = 0;
  virtual void pop(unsigned num_scopes) = 0;

  virtual ~PropagatorBase() {
    for (auto& subcontext : subcontexts) {
        // subcontext->destroy(); do not destroy; will be done by Z3
        delete subcontext;
    }
  }

  virtual PropagatorBase *fresh(smt::context* c) = 0;

  void register_fixed();

  void register_final();

  void register_created();

  virtual void fixed(expr const &, expr const &) {}

  virtual void final() {}

  virtual void created(expr const &) {}

  void register_expr(expr const &e);

  void conflict(unsigned num_fixed, expr const *fixed);

  void propagate(unsigned num_fixed, expr const *fixed, expr const &conseq);
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
