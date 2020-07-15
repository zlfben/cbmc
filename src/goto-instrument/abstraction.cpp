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
      expr.id() == ID_const_cast || expr.id() == ID_static_cast || expr.id() == ID_typecast || 
      expr.id() == ID_dynamic_cast || expr.id() == ID_reinterpret_cast)
    {
      link(index, operands_index[0]);
    }
    else if(expr.id() == ID_plus || expr.id() == ID_minus)
    {
      if(expr.operands()[0].id() == ID_symbol)
      {
        if(
          (expr.operands()[1].id() == ID_typecast && expr.operands()[1].operands()[0].id() == ID_constant) ||
          expr.operands()[1].id() == ID_constant)
        {
          link(index, operands_index[0]);
        }
      }
    }

    // If this is an access to the array, put it into the set of exprs covered
    if(
      expr.id() == ID_plus && expr.operands().front().id() == ID_symbol &&
      expr.operands().front().type().id() == ID_pointer)
    {
      const symbol_exprt &symb = to_symbol_expr(expr.operands().front());
      if(symb.get_identifier() == target_array)
      {
        todo.insert(operands_index[1]);
      }
    }
  }

  return index;
}

void expr_type_relation::solve()
{
  while(!todo.empty())
  {
    std::unordered_set<size_t>::iterator current_it = todo.begin();
    size_t current_index = *current_it;
    todo.erase(current_it);
    finished.insert(current_index);

    for(size_t neighbor: edges[current_index])
    {
      if(todo.find(neighbor) == todo.end() && finished.find(neighbor) == finished.end())
      {
        // this neighbor doesn't exist previously, should be put into todo
        todo.insert(neighbor);
      }
    }
    if(expr_list[current_index].id() == ID_symbol)
    {
      const symbol_exprt &symb = to_symbol_expr(expr_list[current_index]);
      const irep_idt symb_id = symb.get_identifier();
      for(size_t neighbor: symbols[symb_id])
      {
        if(todo.find(neighbor) == todo.end() && finished.find(neighbor) == finished.end())
          todo.insert(neighbor);
      }
      abst_variables.insert(symb_id);
    }
  }
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

  expr_type_relation etr(abst_array_id);

  // for each function, rename all references to that variable
  Forall_goto_functions(it, goto_model.goto_functions)
  {
    std::cout << "**" << it->first << std::endl;
    if(std::string(abst_array_id.c_str()).rfind((it->first).c_str(), 0) == 0)
    {
      // this function is the one that contains the target variable
      // it->second is the goto_functiont
      goto_functiont &goto_function = it->second;

      // for each instruction, we change the referenced name of the target variable
      Forall_goto_program_instructions(it, goto_function.body)
      {
        // go through conditions
        if(it->has_condition())
        {
          etr.add_expr(it->get_condition());
        }

        // go through all expressions
        if(it->is_function_call())
        {
          const code_function_callt fc = it->get_function_call();
          code_function_callt::argumentst new_arguments = fc.arguments();
          exprt new_lhs = fc.lhs();
          etr.add_expr(fc.lhs());
          
          for(auto &arg : fc.arguments())
            etr.add_expr(arg);
        }
        else if(it->is_assign())
        {
          const code_assignt as = it->get_assign();
          size_t l_id = etr.add_expr(as.lhs());
          size_t r_id = etr.add_expr(as.rhs());
          etr.link(l_id, r_id);
        }
      }
    }
  }

  etr.solve();
  for(auto v: etr.get_abst_variables())
    std::cout << v << std::endl;
}