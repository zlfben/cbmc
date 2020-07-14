/*******************************************************************\

Module: Abstraction

Author: Lefan Zhang, lefanz@amazon.com

\*******************************************************************/

/// \file
/// Abstraction
/// Abstract certain data types to make proofs unbounded

#include <iostream>

#include <util/std_expr.h>

#include "abstraction.h"

void expr_type_relation::link(size_t i1, size_t i2)
{
  edges[i1].push_back(i2);
  edges[i2].push_back(i1);
}

size_t expr_type_relation::add_expr(const exprt &expr)
{
  size_t index = expr_list.size();
  expr_list.push_back(expr);
  edges.push_back(std::vector<size_t>());

  // add symbol to symbol list
  if(expr.id() == ID_symbol)
  {
    const symbol_exprt &symb = to_symbol_expr(expr);
    if(symbols.find(symb.get_identifier()) == symbols.end())
      symbols[symb.get_identifier()] = std::vector<size_t>();
    symbols[symb.get_identifier()].push_back(index);
  }

  // add operands also
  if(expr.has_operands())
  {
    std::vector<size_t> operands_index;
    for(auto &op : expr.operands())
      operands_index.push_back(add_expr(op));

    if(
      expr.id() == ID_equal || expr.id() == ID_notequal || expr.id() == ID_ge ||
      expr.id() == ID_gt || expr.id() == ID_le || expr.id() == ID_lt)
    {
      link(operands_index[0], operands_index[1]);
    }
    else if(
      expr.id() == ID_const_cast || expr.id() == ID_static_cast ||
      expr.id() == ID_dynamic_cast || expr.id() == ID_reinterpret_cast)
    {
      link(index, operands_index[0]);
    }

    // If this is an access to the array, put it into the set of exprs covered
    if(
      expr.id() == ID_plus && expr.operands().front().id() == ID_symbol &&
      expr.operands().front().type().id() == ID_pointer)
    {
      const symbol_exprt &symb = to_symbol_expr(expr.operands().front());
      if(symb.get_identifier() == target_array)
        todo.insert(operands_index[1]);
    }
  }

  return index;
}

void expr_type_relation::solve()
{
}

void abstract_goto_program(goto_modelt &goto_model, jsont json)
{
  class show_index_exprt : public expr_visitort
  {
  private:
    const irep_idt array_name;

  public:
    explicit show_index_exprt(const irep_idt &_array_name)
      : array_name(_array_name)
    {
    }

    static void print_exprt(const exprt &expr)
    {
      std::cout << expr.id();
      if(expr.has_operands())
      {
        std::cout << "[";
        for(auto &op : expr.operands())
        {
          print_exprt(op);
          std::cout << ",";
        }
        std::cout << "]";
      }
      if(expr.id() == ID_constant)
      {
        // print the constant
        std::cout << "(" << to_constant_expr(expr).get_value() << ")";
      }
    }

    void operator()(exprt &expr) override
    {
      // if there is an operand of this expr that is "array_name", this is a ref
      if(expr.has_operands())
      {
        exprt::operandst operands = expr.operands();

        // tell if it's access to pointer
        if(
          expr.id() == ID_plus && operands.front().id() == ID_symbol &&
          operands.front().type().id() == ID_pointer)
        {
          symbol_exprt &symb = to_symbol_expr(operands.front());
          // tell if the pointer is the target one
          if(symb.get_identifier() == array_name)
          {
            // get the index in array[index]
            exprt &index = operands.at(1);
            // std::cout << index.pretty() << std::endl;
            print_exprt(index);
            std::cout << std::endl;
            // std::cout << index.pretty() << std::endl;
          }
        }
      }
    }
  };

  irep_idt abst_array_id = json["array_name"].value;

  show_index_exprt se(abst_array_id);

  // for each function, rename all references to that variable
  Forall_goto_functions(it, goto_model.goto_functions)
  {
    // it->second is the goto_functiont
    goto_functiont &goto_function = it->second;

    // for each instruction, we change the referenced name of the target variable
    Forall_goto_program_instructions(it, goto_function.body)
    {
      // go through conditions
      if(it->has_condition())
      {
        exprt new_guard = it->get_condition();
        new_guard.visit(se);
        it->set_condition(new_guard);
      }

      // go through all expressions
      if(it->is_function_call())
      {
        const code_function_callt fc = it->get_function_call();
        code_function_callt::argumentst new_arguments = fc.arguments();
        exprt new_lhs = fc.lhs();
        exprt new_function = fc.function();
        new_lhs.visit(se);
        new_function.visit(se);
        for(auto &arg : new_arguments)
          arg.visit(se);
      }
      else if(it->is_assign())
      {
        const code_assignt as = it->get_assign();
        exprt new_lhs = as.lhs();
        exprt new_rhs = as.rhs();
        new_lhs.visit(se);
        new_rhs.visit(se);
      }
    }
  }
}