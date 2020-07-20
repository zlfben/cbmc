/*******************************************************************\

Module: Abstraction

Author: Lefan Zhang, lefanz@amazon.com
        Murali Talupur talupur@amazon.com

\*******************************************************************/

/// \file
/// Abstraction
/// Abstract certain data types to make proofs unbounded

#ifndef CPROVER_GOTO_INSTRUMENT_ABSTRACTION_H
#define CPROVER_GOTO_INSTRUMENT_ABSTRACTION_H

#include <util/expr.h>
#include <util/json.h>

#include <goto-programs/goto_model.h>
#include <util/ui_message.h>
#include <util/options.h>

#include "abstraction_spect.h"

// class to find out type relations between exprs
// this is used to identify symbols we need to abstract given a target array
// call solve() after reading in all exprs and adding needed links
class expr_type_relation
{
protected:
  irep_idt target_array;

  std::vector<std::vector<size_t>> edges;
  std::vector<exprt> expr_list;
  std::unordered_set<size_t> finished;
  std::unordered_set<size_t> todo;
  std::map<irep_idt, std::vector<size_t>> symbols;
  std::unordered_set<irep_idt> abst_variables;

public:
  expr_type_relation(irep_idt _target_array) : target_array(_target_array)
  {
  }
  void link(size_t i1, size_t i2);
  size_t add_expr(const exprt &expr);
  void solve();
  const std::unordered_set<irep_idt> & get_abst_variables()
  {
    return abst_variables;
  }
};

// link abst functions to goto programs
void link_abst_functions(goto_modelt &goto_model, const abstraction_spect &abst_spec, ui_message_handlert &msg_handler, const optionst &options);

// abstract goto programs
void abstract_goto_program(goto_modelt &goto_model, jsont json);

#endif // CPROVER_GOTO_INSTRUMENT_ABSTRACTION_H
