#pragma once

// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

typedef struct _Z3_context *Z3_context;
typedef struct _Z3_params *Z3_params;

namespace smt {

class PropagatorBase;

typedef enum
{
  Z3_OK,
  Z3_SORT_ERROR,
  Z3_IOB,
  Z3_INVALID_ARG,
  Z3_PARSER_ERROR,
  Z3_NO_PARSER,
  Z3_INVALID_PATTERN,
  Z3_MEMOUT_FAIL,
  Z3_FILE_ACCESS_ERROR,
  Z3_INTERNAL_FATAL,
  Z3_INVALID_USAGE,
  Z3_DEC_REF_ERROR,
  Z3_EXCEPTION
} Z3_error;

class context {
  Z3_context ctx;
  Z3_params no_timeout_param;

public:

  Z3_context operator()() const { return ctx; }

  Z3_params getNoTimeoutParam() const { return no_timeout_param; }

  void init();

  void destroy();

  smt::Z3_error getErrorCode();

   friend PropagatorBase;
};

extern context ctx;

}
