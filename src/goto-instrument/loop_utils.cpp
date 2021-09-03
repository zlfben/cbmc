/*******************************************************************\

Module: Helper functions for k-induction and loop invariants

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Helper functions for k-induction and loop invariants

#include "loop_utils.h"

#include <analyses/local_may_alias.h>

#include <goto-programs/pointer_arithmetic.h>

#include <util/pointer_expr.h>
#include <util/std_expr.h>

goto_programt::targett get_loop_exit(const loopt &loop)
{
  assert(!loop.empty());

  // find the last instruction in the loop
  std::map<unsigned, goto_programt::targett> loop_map;

  for(loopt::const_iterator l_it=loop.begin();
      l_it!=loop.end();
      l_it++)
    loop_map[(*l_it)->location_number]=*l_it;

  // get the one with the highest number
  goto_programt::targett last=(--loop_map.end())->second;

  return ++last;
}


void get_modifies_lhs(
  const local_may_aliast &local_may_alias,
  goto_programt::const_targett t,
  const exprt &lhs,
  modifiest &modifies)
{
  if(lhs.id() == ID_symbol || lhs.id() == ID_member || lhs.id() == ID_index)
    modifies.insert(lhs);
  else if(lhs.id()==ID_dereference)
  {
    const pointer_arithmetict ptr(to_dereference_expr(lhs).pointer());
    for(const auto &mod : local_may_alias.get(t, ptr.pointer))
    {
      if(ptr.offset.is_nil())
        modifies.insert(dereference_exprt{mod});
      else
        modifies.insert(dereference_exprt{plus_exprt{mod, ptr.offset}});
    }
  }
  else if(lhs.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(lhs);

    get_modifies_lhs(local_may_alias, t, if_expr.true_case(), modifies);
    get_modifies_lhs(local_may_alias, t, if_expr.false_case(), modifies);
  }
}

void get_modifies(
  const local_may_aliast &local_may_alias,
  const loopt &loop,
  modifiest &modifies)
{
  for(loopt::const_iterator
      i_it=loop.begin(); i_it!=loop.end(); i_it++)
  {
    const goto_programt::instructiont &instruction=**i_it;

    if(instruction.is_assign())
    {
      const exprt &lhs = instruction.get_assign().lhs();
      get_modifies_lhs(local_may_alias, *i_it, lhs, modifies);
    }
    else if(instruction.is_function_call())
    {
      const exprt &lhs = instruction.call_lhs();
      get_modifies_lhs(local_may_alias, *i_it, lhs, modifies);
    }
  }
}

void get_accesses_expr(
  const local_may_aliast &local_may_alias,
  goto_programt::const_targett t,
  const exprt &expr,
  accessest &accesses)
{
  // a class that will iterate through sub-exprs of an expr
  // to get accessed expressions 
  class visit_accessest : public const_expr_visitort
  {
  protected:
    accessest &accesses;
    const local_may_aliast &local_may_alias;
    goto_programt::const_targett t;
  
  public:
    explicit visit_accessest(
      accessest &_accesses, 
      const local_may_aliast &_local_may_alias, 
      goto_programt::const_targett _t)
      : accesses(_accesses),
        local_may_alias(_local_may_alias),
        t(_t)
    {
    }

    void operator()(const exprt &expr)
    {
      if(expr.id() == ID_symbol || expr.id() == ID_member || expr.id() == ID_index)
        accesses.insert(expr);
      else if(expr.id()==ID_dereference)
      {
        const pointer_arithmetict ptr(to_dereference_expr(expr).pointer());
        for(const auto &mod : local_may_alias.get(t, ptr.pointer))
        {
          if(ptr.offset.is_nil())
            accesses.insert(dereference_exprt{mod});
          else
            accesses.insert(dereference_exprt{plus_exprt{mod, ptr.offset}});
        }
      }
    }
  };

  visit_accessest visit_accesses(accesses, local_may_alias, t);
  expr.visit(visit_accesses);
}

void get_accesses_instr(
  const local_may_aliast &local_may_alias,
  goto_programt::const_targett t,
  const goto_programt::instructiont &instruction, 
  accessest &writes,
  accessest &reads)
{
  if(instruction.is_goto() || instruction.is_assert() || instruction.is_assume())
  {
    const exprt &expr = instruction.get_condition();
    get_accesses_expr(local_may_alias, t, expr, reads);
  }
  else if(instruction.is_set_return_value())
  {
    if(instruction.get_return().has_return_value())
    {
      const exprt &ret = instruction.get_return().return_value();
      get_accesses_expr(local_may_alias, t, ret, reads);
    }
  }
  else if(instruction.is_assign())
  {
    const exprt &lhs = instruction.get_assign().lhs();
    const exprt &rhs = instruction.get_assign().rhs();
    get_modifies_lhs(local_may_alias, t, lhs, writes);
    get_accesses_expr(local_may_alias, t, rhs, reads);
  }
  else if(instruction.is_function_call())
  {
    const exprt &lhs = instruction.get_function_call().lhs();
    get_modifies_lhs(local_may_alias, t, lhs, writes);
    for (const auto &arg: instruction.get_function_call().arguments())
      get_accesses_expr(local_may_alias, t, arg, reads);
  }
}

void get_accesses(
  const local_may_aliast &local_may_alias,
  const loopt &loop,
  accessest &write_accesses,
  accessest &read_accesses,
  const accessest &iterator_bypasses)
{
  for(loopt::const_iterator
      i_it=loop.begin(); i_it!=loop.end(); i_it++)
  {
    const goto_programt::instructiont &instruction=**i_it;
    // reads and writes to variables in this instruction
    accessest writes, reads;
    get_accesses_instr(local_may_alias, *i_it, instruction, writes, reads);

    // we can bypass the instruction 
    // if it is a self-update of an iterator
    // otherwise update the access set
    if(!(writes.size() == 1 && reads.size() == 1 && 
         *writes.begin() == *reads.begin() &&
         iterator_bypasses.find(*writes.begin()) != iterator_bypasses.end()))
    {
      for(const auto &exp: writes)
        write_accesses.insert(exp);
      for(const auto &exp: reads)
        read_accesses.insert(exp);
    }
  }
}