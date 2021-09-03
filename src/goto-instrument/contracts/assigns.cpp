/*******************************************************************\

Module: Specify write set in function contracts.

Author: Felipe R. Monteiro

Date: July 2021

\*******************************************************************/

/// \file
/// Specify write set in function contracts

#include "assigns.h"

#include <goto-instrument/havoc_utils.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_predicates.h>

assigns_clause_targett::assigns_clause_targett(
  const exprt &object,
  code_contractst &contract,
  messaget &log_parameter,
  const irep_idt &function_id)
  : contract(contract),
    init_block(),
    log(log_parameter),
    target(pointer_for(object)),
    target_id(object.id())
{
  INVARIANT(
    target.type().id() == ID_pointer,
    "Assigns clause targets should be stored as pointer expressions.");
}

assigns_clause_targett::~assigns_clause_targett()
{
}

exprt assigns_clause_targett::alias_expression(const exprt &lhs)
{
  exprt::operandst condition;
  exprt lhs_ptr = (lhs.id() == ID_address_of) ? to_address_of_expr(lhs).object()
                                              : pointer_for(lhs);

  // __CPROVER_w_ok(target, sizeof(target))
  condition.push_back(w_ok_exprt(
    target,
    size_of_expr(dereference_exprt(target).type(), contract.ns).value()));

  // __CPROVER_same_object(lhs, target)
  condition.push_back(same_object(lhs_ptr, target));

  // If assigns target was a dereference, comparing objects is enough
  if(target_id == ID_dereference)
  {
    return conjunction(condition);
  }

  const exprt lhs_offset = pointer_offset(lhs_ptr);
  const exprt target_offset = pointer_offset(target);

  // __CPROVER_offset(lhs) >= __CPROVER_offset(target)
  condition.push_back(binary_relation_exprt(lhs_offset, ID_ge, target_offset));

  const exprt region_lhs = plus_exprt(
    typecast_exprt::conditional_cast(
      size_of_expr(lhs.type(), contract.ns).value(), lhs_offset.type()),
    lhs_offset);

  const exprt region_target = plus_exprt(
    typecast_exprt::conditional_cast(
      size_of_expr(dereference_exprt(target).type(), contract.ns).value(),
      target_offset.type()),
    target_offset);

  // (sizeof(lhs) + __CPROVER_offset(lhs)) <=
  // (sizeof(target) + __CPROVER_offset(target))
  condition.push_back(binary_relation_exprt(region_lhs, ID_le, region_target));

  return conjunction(condition);
}

exprt assigns_clause_targett::compatible_expression(
  const assigns_clause_targett &called_target)
{
  return same_object(called_target.get_target(), target);
}

const exprt &assigns_clause_targett::get_target() const
{
  return target;
}

assigns_clauset::assigns_clauset(
  const exprt &assigns,
  code_contractst &contract,
  const irep_idt function_id,
  messaget log_parameter)
  : assigns(assigns),
    parent(contract),
    function_id(function_id),
    log(log_parameter)
{
  for(exprt target : assigns.operands())
  {
    add_target(target);
  }
}

assigns_clauset::~assigns_clauset()
{
  for(assigns_clause_targett *target : targets)
  {
    delete target;
  }
}

void assigns_clauset::add_target(exprt target)
{
  assigns_clause_targett *new_target = new assigns_clause_targett(
    (target.id() == ID_address_of)
      ? to_index_expr(to_address_of_expr(target).object()).array()
      : target,
    parent,
    log,
    function_id);
  targets.push_back(new_target);
}

goto_programt assigns_clauset::havoc_code()
{
  modifiest modifies;
  for(const auto &t : targets)
    modifies.insert(to_address_of_expr(t->get_target()).object());

  goto_programt havoc_statements;
  append_havoc_code(assigns.source_location(), modifies, havoc_statements);
  return havoc_statements;
}

exprt assigns_clauset::alias_expression(const exprt &lhs)
{
  // If write set is empty, no assignment is allowed.
  if(targets.empty())
  {
    return false_exprt();
  }

  exprt::operandst condition;
  for(assigns_clause_targett *target : targets)
  {
    condition.push_back(target->alias_expression(lhs));
  }
  return disjunction(condition);
}

exprt assigns_clauset::compatible_expression(
  const assigns_clauset &called_assigns)
{
  if(called_assigns.targets.empty())
  {
    return true_exprt();
  }

  bool first_clause = true;
  exprt result = true_exprt();
  for(assigns_clause_targett *called_target : called_assigns.targets)
  {
    bool first_iter = true;
    exprt current_target_compatible = false_exprt();
    for(assigns_clause_targett *target : targets)
    {
      if(first_iter)
      {
        // TODO: Optimize the validation below and remove code duplication
        // See GitHub issue #6105 for further details

        // Validating the called target through __CPROVER_w_ok() is
        // only useful when the called target is a dereference
        const auto &called_target_ptr = called_target->get_target();
        if(
          to_address_of_expr(called_target_ptr).object().id() == ID_dereference)
        {
          // or_exprt is short-circuited, therefore
          // target->compatible_expression(*called_target) would not be
          // checked on invalid called_targets.
          current_target_compatible = or_exprt(
            not_exprt(w_ok_exprt(
              called_target_ptr, from_integer(0, unsigned_int_type()))),
            target->compatible_expression(*called_target));
        }
        else
        {
          current_target_compatible =
            target->compatible_expression(*called_target);
        }
        first_iter = false;
      }
      else
      {
        current_target_compatible = or_exprt(
          current_target_compatible,
          target->compatible_expression(*called_target));
      }
    }
    if(first_clause)
    {
      result = current_target_compatible;
      first_clause = false;
    }
    else
    {
      exprt::operandst conjuncts;
      conjuncts.push_back(result);
      conjuncts.push_back(current_target_compatible);
      result = conjunction(conjuncts);
    }
  }

  return result;
}
