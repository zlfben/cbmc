/*******************************************************************\

Module: Specify write set in function contracts.

Author: Felipe R. Monteiro

Date: July 2021

\*******************************************************************/

/// \file
/// Specify write set in function contracts

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H

#include "contracts.h"

#include <util/pointer_offset_size.h>

/// \brief A base class for assigns clause targets
class assigns_clause_targett
{
public:
  assigns_clause_targett(
    const exprt &object,
    code_contractst &contract,
    messaget &log_parameter,
    const irep_idt &function_id);
  ~assigns_clause_targett();

  exprt alias_expression(const exprt &lhs);
  exprt compatible_expression(const assigns_clause_targett &called_target);
  const exprt &get_target() const;

  static exprt pointer_for(const exprt &object)
  {
    return address_of_exprt(object);
  }

protected:
  const code_contractst &contract;
  goto_programt init_block;
  messaget &log;
  exprt target;
  const irep_idt &target_id;
};

class assigns_clauset
{
public:
  assigns_clauset(
    const exprt &assigns,
    code_contractst &contract,
    const irep_idt function_id,
    messaget log_parameter);
  ~assigns_clauset();

  void add_target(exprt target);
  goto_programt havoc_code();
  exprt alias_expression(const exprt &lhs);
  exprt compatible_expression(const assigns_clauset &called_assigns);

protected:
  const exprt &assigns;

  std::vector<assigns_clause_targett *> targets;
  goto_programt standin_declarations;

  code_contractst &parent;
  const irep_idt function_id;
  messaget log;
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H
