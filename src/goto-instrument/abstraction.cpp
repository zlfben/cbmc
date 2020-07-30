/*******************************************************************\

Module: Abstraction

Author: Lefan Zhang, lefanz@amazon.com
        Murali Talupur talupur@amazon.com

\*******************************************************************/

/// \file
/// Abstraction
/// Abstract certain data types to make proofs unbounded

#include <iostream>
#include <queue>

#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_goto_model.h>

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

void link_abst_functions(goto_modelt &goto_model, const abstraction_spect &abst_spec, ui_message_handlert &msg_handler, const optionst &options)
{
  std::vector<std::string> abstfiles = abst_spec.get_abstraction_function_files();  // get abst function file names
  goto_modelt goto_model_for_abst_fns = initialize_goto_model(abstfiles, msg_handler, options);  // read files
  link_goto_model(goto_model, goto_model_for_abst_fns, msg_handler);  // link goto model
}

const std::unordered_set<irep_idt> find_index_symbols(const goto_functiont &goto_function, const irep_idt &array_name)
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

  irep_idt abst_array_id = array_name;

  expr_type_relation etr(abst_array_id);

  // within the function, rename all references to that variable
  // for each instruction, we change the referenced name of the target variable
  forall_goto_program_instructions(it, goto_function.body)
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

  etr.solve();
  return etr.get_abst_variables();
}

void complete_abst_spec(const goto_functiont& goto_function, abstraction_spect &abst_spec)
{
  for(auto &spec: abst_spec.get_specs())
  {
    for(const auto &ent: spec.get_abst_arrays())
      for(irep_idt index_name: find_index_symbols(goto_function, ent.first))
        if(spec.get_abst_indices().find(index_name) == spec.get_abst_indices().end())
          spec.insert_entity(index_name, true);
  }
}

/// check if expr is a symbol (or typecast from a symbol)
/// \return the symbol name, "" if expr is not a symbol
irep_idt check_expr_is_symbol(const exprt &expr)
{
  if(expr.id() == ID_symbol)
  {
    // if it is a symbol, return itself's name
    const symbol_exprt &symb = to_symbol_expr(expr);
    return symb.get_identifier();
  }
  else if(expr.id() == ID_typecast)
  {
    // if it is a typecast, check the next level
    return check_expr_is_symbol(expr.operands()[0]);
  }
  else
  {
    // otherwise, the argument is not a symbol
    return irep_idt("");
  }
}

// go into a function to find all function calls we'll need to abstract
std::vector<std::tuple<irep_idt, std::unordered_map<irep_idt, irep_idt>>>
find_function_calls(irep_idt func_name, goto_modelt &goto_model, const abstraction_spect &abst_spec)
{
  std::vector<std::tuple<irep_idt, std::unordered_map<irep_idt, irep_idt>>> result;
  
  const goto_functiont &goto_function = goto_model.get_goto_function(func_name);
  forall_goto_program_instructions(it, goto_function.body)
  {
    // go through every instruction
    if(it->is_function_call())
    {
      // it is a function call that we potentially need to abstract
      const code_function_callt fc = it->get_function_call();
      const irep_idt &new_func_name = to_symbol_expr(fc.function()).get_identifier();
      const goto_functiont &new_function = goto_model.get_goto_function(new_func_name);
      std::unordered_map<irep_idt, irep_idt> map;
      for(size_t i=0; i<fc.arguments().size(); i++)
      {
        // for each argument, we check whether we need to abstract it.
        const exprt &arg = fc.arguments()[i];
        irep_idt symbol_name = check_expr_is_symbol(arg);
        if(symbol_name != "" && abst_spec.has_entity(symbol_name))
          // if so, we push it into the map
          map.insert({symbol_name, new_function.parameter_identifiers[i]});
      }
      if(!map.empty())  //if map is not empty, we create a new entry in the result
        result.push_back(std::make_tuple(new_func_name, map));
    }
  }
  return result;
}

std::unordered_map<irep_idt, abstraction_spect> 
calculate_complete_abst_specs_for_funcs(goto_modelt &goto_model, abstraction_spect &abst_spec)
{
  std::unordered_map<irep_idt, abstraction_spect> function_spec_map;  // map from function to its abst_spec
  const goto_functiont &init_function = goto_model.get_goto_function(abst_spec.get_func_name());
  complete_abst_spec(init_function, abst_spec);
  function_spec_map.insert({abst_spec.get_func_name(), abst_spec});

  // The following is a search of functions.
  // At each step, we pop one function A from the todo list.
  // We analyze A to see if it calls other functions.
  // If any other functions are called and have not been analyzed, 
  // we analyze the function with update_abst and complete_abst, 
  // and then push that to the todo list.
  // Each function is only analyzed for one time. 
  // We assume each function will only have a unique abst_spec.
  std::queue<irep_idt> todo;  // functions to be further analyzed
  todo.push(abst_spec.get_func_name());

  while(!todo.empty())
  {
    // pop the first function in the todo list
    irep_idt current_func_name = todo.front();
    todo.pop();

    // check it calls any other functions that we need to abstract
    std::vector<std::tuple<irep_idt, std::unordered_map<irep_idt, irep_idt>>>
      func_tuples = find_function_calls(
        current_func_name, goto_model, function_spec_map[current_func_name]);

    // for each function we need to abstract, check if it's already analyzed
    // if not, we analyze it and put it into the function_spec_map and todo
    for(const auto &func_tuple: func_tuples)
    {
      irep_idt new_func_name = std::get<0>(func_tuple);
      std::unordered_map<irep_idt, irep_idt> name_pairs = std::get<1>(func_tuple);
      if(function_spec_map.find(new_func_name) == function_spec_map.end())
      {
        // we need to abstract it and analyze it
        todo.push(new_func_name);
        abstraction_spect new_func_abst =
          function_spec_map[current_func_name].update_abst_spec(
            current_func_name, new_func_name, name_pairs);
        complete_abst_spec(goto_model.get_goto_function(new_func_name), new_func_abst);
        function_spec_map.insert({new_func_name, new_func_abst});
      }
      else
      {
        // we need to compare if the structure is the same
        abstraction_spect new_func_abst = function_spec_map[current_func_name].update_abst_spec(current_func_name, new_func_name, name_pairs);
        if(!new_func_abst.compare_shape(function_spec_map[new_func_name]))
        {
          std::string error_code = "Same function abstracted with different shape!\n";
          error_code += "Original abst spec:\n";
          error_code += function_spec_map[new_func_name].get_entities_string();
          error_code += "New abst spec:\n";
          error_code += new_func_abst.get_entities_string();
          throw error_code;
        }
      }
    }
  }
  return function_spec_map;
}

bool contains_an_abstracted_entity(const exprt &expr, const abstraction_spect &abst_spec)
{
  struct match_abst_symbolt
  {
    match_abst_symbolt(const abstraction_spect &_abst_spec) : abst_spec(_abst_spec) {}
    // check if expr is an entity symbol that we want to abstract
    bool operator()(const exprt &expr)
    {
      irep_idt symbol_name = check_expr_is_symbol(expr);
      return symbol_name != "" && abst_spec.has_entity(symbol_name);
    }
  protected:
    // we assume this abst_spec's life span covers 
    // the life span of the match_abst_symbolt object
    const abstraction_spect &abst_spec;
  };
  match_abst_symbolt match_abst_symbol(abst_spec);
  return has_subexpr(expr, match_abst_symbol);

}

void declare_abst_variables_for_func(goto_modelt &goto_model, const irep_idt &func_name, const abstraction_spect &abst_spec)
{
  symbol_tablet &symbol_table = goto_model.symbol_table;

  // helper function to insert abst variables into the symbol table
  auto insert_abst_symbol = [&symbol_table](const abstraction_spect::spect::entityt &entity)
  {
    // sometimes vars in built in functions has no identifers
    // we don't handle those cases by default
    if(symbol_table.has_symbol(entity.entity_name()))
    {
      // insert the symbol var_name$abst into the symbol table
      const symbolt &orig_symbol = symbol_table.lookup_ref(entity.entity_name());
      symbolt abst_symbol(orig_symbol);
      abst_symbol.name = std::string(entity.entity_name().c_str()) + "$abst";
      if(!symbol_table.has_symbol(abst_symbol.name))
        symbol_table.insert(abst_symbol);
    }
    
  };

  // Step 1: insert abst variables into the symbol table
  for(const abstraction_spect::spect &spec: abst_spec.get_specs())
  {
    for(const auto &ent_pair: spec.get_abst_arrays())
      insert_abst_symbol(ent_pair.second);
    for(const auto &ent_pair: spec.get_abst_indices())
      insert_abst_symbol(ent_pair.second);
  }

  // Step 2: if it is in the function parameter list, change the name
  goto_functiont &function = goto_model.goto_functions.function_map.at(func_name);
  for(auto &param: function.parameter_identifiers)
    if(abst_spec.has_entity(param))
      param = std::string(param.c_str()) + "$abst";
  
  // Step 3: if it is declared within the function, change DECLARE and DEAD
  Forall_goto_program_instructions(it, function.body)
  {
    if(it->is_decl())
    {
      // change symbol name in DECLARE instruction
      const code_declt &decl = it->get_decl();
      if(abst_spec.has_entity(decl.get_identifier()))
      {
        irep_idt new_name = std::string(decl.get_identifier().c_str()) + "$abst";
        typet typ = symbol_table.lookup_ref(new_name).type;
        symbol_exprt new_symb_expr(new_name, typ);
        code_declt new_decl(new_symb_expr);
        it->set_decl(new_decl);
      }
    }
    else if(it->is_dead())
    {
      // change symbol name in DEAD instruction
      const code_deadt &dead = it->get_dead();
      if(abst_spec.has_entity(dead.get_identifier()))
      {
        irep_idt new_name = std::string(dead.get_identifier().c_str()) + "$abst";
        typet typ = symbol_table.lookup_ref(new_name).type;
        symbol_exprt new_symb_expr(new_name, typ);
        code_deadt new_dead(new_symb_expr);
        it->set_dead(new_dead);
      }
    }
    else {}
    
  }
}

void abstract_goto_program(goto_modelt &goto_model, abstraction_spect &abst_spec)
{
  // A couple of spects are initialized from the json file. We should go from there and insert spects to other functions
  std::unordered_map<irep_idt, abstraction_spect> function_spec_map =
    calculate_complete_abst_specs_for_funcs(goto_model, abst_spec);
  for(auto &p: function_spec_map)
    declare_abst_variables_for_func(goto_model, p.first, p.second);
  
  for(auto &p: function_spec_map)
  {
    std::cout << "=========== " << p.first << " ===========" << std::endl;
    std::cout << "----------- " << "Entities to be abstracted" << " -----------" << std::endl;
    p.second.print_entities();
    std::cout << "----------- " << "Exprs containing the above entities" << " -----------" << std::endl;
    const goto_functiont &goto_function = goto_model.get_goto_function(p.first);
    const abstraction_spect &abst_spec = p.second;
    forall_goto_program_instructions(it, goto_function.body)
    {
      // go through conditions
      if(it->has_condition())
        if(contains_an_abstracted_entity(it->get_condition(), abst_spec))
          format_rec(std::cout, it->get_condition()) << std::endl;

      // go through all expressions
      if(it->is_function_call())
      {
        const code_function_callt fc = it->get_function_call();
        if(contains_an_abstracted_entity(fc.lhs(), abst_spec))
          format_rec(std::cout, fc.lhs()) << std::endl;
        
        for(const auto &arg : fc.arguments())
          if(contains_an_abstracted_entity(arg, abst_spec))
            format_rec(std::cout, arg) << std::endl;
      }
      else if(it->is_assign())
      {
        const code_assignt as = it->get_assign();
        if(contains_an_abstracted_entity(as.lhs(), abst_spec))
          format_rec(std::cout, as.lhs()) << std::endl;
        if(contains_an_abstracted_entity(as.rhs(), abst_spec))
          format_rec(std::cout, as.rhs()) << std::endl;
      }
    }
  }
}
