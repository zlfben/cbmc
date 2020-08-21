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
#include <util/c_types.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_goto_model.h>
#include <linking/static_lifetime_init.h>
#include "abstraction.h"

void expr_type_relation::link(size_t i1, size_t i2)
{
  edges[i1].push_back(i2);
  edges[i2].push_back(i1);
}

void expr_type_relation::link_array(size_t i1, size_t i2)
{
  edges_array[i1].push_back(i2);
  edges_array[i2].push_back(i1);
}

size_t expr_type_relation::add_expr(const exprt &expr)
{
  size_t index = expr_list.size();
  expr_list.push_back(expr);
  edges.push_back(std::vector<size_t>());
  edges_array.push_back(std::vector<size_t>());

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
      link_array(index, operands_index[0]);
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

  // If this is the array itself, put it into the set of array exprs
  if(expr.id() == ID_symbol)
  {
    const symbol_exprt &symb = to_symbol_expr(expr);
    if(symb.get_identifier() == target_array)
    {
      todo_array.insert(index);
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

void expr_type_relation::solve_array()
{
  while(!todo_array.empty())
  {
    std::unordered_set<size_t>::iterator current_it = todo_array.begin();
    size_t current_index = *current_it;
    todo_array.erase(current_it);
    finished_array.insert(current_index);

    for(size_t neighbor: edges_array[current_index])
    {
      if(todo_array.find(neighbor) == todo_array.end() && finished_array.find(neighbor) == finished_array.end())
      {
        // this neighbor doesn't exist previously, should be put into todo
        todo_array.insert(neighbor);
      }
    }
    if(expr_list[current_index].id() == ID_symbol)
    {
      const symbol_exprt &symb = to_symbol_expr(expr_list[current_index]);
      const irep_idt symb_id = symb.get_identifier();
      for(size_t neighbor: symbols[symb_id])
      {
        if(todo_array.find(neighbor) == todo_array.end() && finished_array.find(neighbor) == finished_array.end())
          todo_array.insert(neighbor);
      }
      abst_arrays.insert(symb_id);
    }
  }
}

void link_abst_functions(goto_modelt &goto_model, const abstraction_spect &abst_spec, ui_message_handlert &msg_handler, const optionst &options)
{
  std::vector<std::string> abstfiles = abst_spec.get_abstraction_function_files();  // get abst function file names
  goto_modelt goto_model_for_abst_fns = initialize_goto_model(abstfiles, msg_handler, options);  // read files
  link_goto_model(goto_model, goto_model_for_abst_fns, msg_handler);  // link goto model
}

const std::tuple<std::unordered_set<irep_idt>, std::unordered_set<irep_idt>>
find_index_symbols(
  const goto_functiont &goto_function,
  const irep_idt &array_name)
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
      etr.link_array(l_id, r_id);
    }
  }

  etr.solve();
  etr.solve_array();

  std::tuple<std::unordered_set<irep_idt>, std::unordered_set<irep_idt>> result(
    etr.get_abst_arrays(), etr.get_abst_variables());

  return result;
}

void complete_abst_spec(const goto_functiont& goto_function, abstraction_spect &abst_spec)
{
  for(auto &spec: abst_spec.get_specs())
  {
    for(const auto &ent: spec.get_abst_arrays())
    {
      std::tuple<std::unordered_set<irep_idt>, std::unordered_set<irep_idt>> abst_entities = find_index_symbols(goto_function, ent.first);
      for(irep_idt index_name: std::get<0>(abst_entities))
        if(spec.get_abst_arrays().find(index_name) == spec.get_abst_arrays().end())
          spec.insert_entity(index_name, "array");
      for(irep_idt index_name: std::get<1>(abst_entities))
        if(spec.get_abst_indices().find(index_name) == spec.get_abst_indices().end())
          spec.insert_entity(index_name, "scalar");
    }
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

bool contains_an_entity_to_be_abstracted(const exprt &expr, const abstraction_spect &abst_spec)
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

irep_idt get_abstract_name(const irep_idt &old_name)
{
  return irep_idt(std::string(old_name.c_str())+"$abst");
}

bool contains_a_function_call(const exprt &expr)
{
  class find_functiont : public const_expr_visitort
  {
  public:
    bool found;
    find_functiont(): found(false) {}
    void operator()(const exprt &expr)
    {
      if(expr.id() == ID_symbol)
      {
        std::string symb_name(to_symbol_expr(expr).get_identifier().c_str());
        if(
          symb_name.find("$tmp") != std::string::npos &&
          symb_name.find("return_value") != std::string::npos)
          found = true;
      }
    }
  };
  find_functiont ff;
  expr.visit(ff);
  return ff.found;
}

std::vector<exprt> get_direct_access_exprs(const exprt &expr, const abstraction_spect::spect &spec)
{
  class find_direct_accesst : public const_expr_visitort
  {
  protected:
    const irep_idt target_array;
    std::vector<exprt> direct_accesses;
  public:
    find_direct_accesst(const irep_idt &_target_array): target_array(_target_array) {}
    void operator()(const exprt &expr)
    {
      if(expr.id() == ID_dereference)
      {
        INVARIANT(expr.operands().size() == 1, "dereference should only have one operand");
        const exprt pointer_expr = expr.operands()[0];
        if(
          pointer_expr.id() == ID_plus && pointer_expr.operands().front().id() == ID_symbol &&
          pointer_expr.operands().front().type().id() == ID_pointer)
        {
          INVARIANT(pointer_expr.operands().size() == 2, "plus should have 2 operands");
          const symbol_exprt &symb = to_symbol_expr(pointer_expr.operands().front());
          // tell if the pointer is the target one
          if(symb.get_identifier() == target_array)
            direct_accesses.push_back(pointer_expr.operands()[1]);
        }
      }
    }
    std::vector<exprt> get_direct_accesses() const
    {
      return direct_accesses;
    }
  };
  std::vector<exprt> result;
  for(const auto &array: spec.get_abst_arrays())
  {
    const irep_idt &array_name = array.first;
    const irep_idt array_name_abst = get_abstract_name(array_name);
    find_direct_accesst fda(array_name_abst);
    expr.visit(fda);
    for(const auto &e: fda.get_direct_accesses())
      result.push_back(e);
  }
  return result;
}

exprt add_guard_expression_to_assert(
  const exprt &expr,
  const exprt &expr_before_abst,
  const abstraction_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  // helper: create a symbol map to find symbols faster
  std::unordered_map<irep_idt, symbolt> new_symbs_map;
  for(const auto &symb: new_symbs)
    new_symbs_map.insert({symb.name, symb});
  // helper: find an abst symbol. it should be either in the symbol table or in the new_symbs
  auto find_symbol_helper = [&new_symbs_map, &goto_model](const irep_idt &symb_name)
  {
    if(goto_model.symbol_table.has_symbol(symb_name))
      return goto_model.symbol_table.lookup_ref(symb_name);
    if(new_symbs_map.find(symb_name) != new_symbs_map.end())
      return new_symbs_map.at(symb_name);
    throw "The abstract symbol " + std::string(symb_name.c_str()) + " is not found";
  };

  if(contains_a_function_call(expr_before_abst))
    throw "The assertion contains a function call. Currently our system doesn't support it.";

  // get all abstract indices in the assertion and create the new expr
  exprt::operandst is_precise_exprs;
  for(const auto &spec: abst_spec.get_specs())
  {
    const irep_idt is_prec_func = spec.get_precise_func();
    for(const exprt &index: get_direct_access_exprs(expr, spec))
    {
      // initialize the operands used by is_precise function
      exprt::operandst operands{index};
      for(const auto &c_ind: spec.get_shape_indices())
      {
        const symbolt &c_ind_symb = find_symbol_helper(c_ind);
        operands.push_back(c_ind_symb.symbol_expr());
      }
      // create the function call for is_precise
      symbolt symb_precise = create_function_call(
        is_prec_func, operands, current_func,
        goto_model, insts_before, insts_after, new_symbs);
      typecast_exprt symb_precise_bool(symb_precise.symbol_expr(), bool_typet());
      is_precise_exprs.push_back(symb_precise_bool);
    }
  }
  
  // the final exprt should be is_prec_all->expr
  if(is_precise_exprs.size() > 0)
  {
    and_exprt is_prec_all(is_precise_exprs);
    implies_exprt final_expr(is_prec_all, expr);
    return std::move(final_expr);
  }
  else
  {
    return expr;
  }
}

void declare_abst_variables_for_func(
  goto_modelt &goto_model,
  const irep_idt &func_name,
  const abstraction_spect &abst_spec,
  std::unordered_set<irep_idt> &abst_var_set)
{
  symbol_tablet &symbol_table = goto_model.symbol_table;

  // helper function to insert abst variables into the symbol table
  auto insert_abst_symbol = [&symbol_table, &abst_var_set](const abstraction_spect::spect::entityt &entity)
  {
    // sometimes vars in built in functions has no identifers
    // we don't handle those cases by default
    if(symbol_table.has_symbol(entity.entity_name()))
    {
      // insert the symbol var_name$abst into the symbol table
      const symbolt &orig_symbol = symbol_table.lookup_ref(entity.entity_name());
      symbolt abst_symbol(orig_symbol);
      abst_symbol.name = get_abstract_name(entity.entity_name());
      if(!symbol_table.has_symbol(abst_symbol.name))
      {
          symbol_table.insert(abst_symbol);
          abst_var_set.insert(abst_symbol.name);
      }
      else
      {
        if(abst_var_set.find(abst_symbol.name) == abst_var_set.end())
          throw "Abstract variable's name already occupied.";
      }
      
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
  INVARIANT(
    goto_model.get_symbol_table().has_symbol(func_name),
    "The function " + std::string(func_name.c_str()) + " is not found");
  symbolt &function_symb = goto_model.symbol_table.get_writeable_ref(func_name);
  code_typet &function_type = to_code_type(function_symb.type);
  for(auto &param: function_type.parameters())
  {
    const irep_idt param_id = param.get_identifier();
    if(abst_spec.has_entity(param_id))
      param.set_identifier(std::string(param_id.c_str()) + "$abst");
  }
    

  // Step 3: if it is declared within the function, change DECLARE and DEAD
  Forall_goto_program_instructions(it, function.body)
  {
    if(it->is_decl())
    {
      // change symbol name in DECLARE instruction
      const code_declt &decl = it->get_decl();
      if(abst_spec.has_entity(decl.get_identifier()))
      {
        irep_idt new_name = get_abstract_name(decl.get_identifier());
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
        irep_idt new_name = get_abstract_name(dead.get_identifier());
        typet typ = symbol_table.lookup_ref(new_name).type;
        symbol_exprt new_symb_expr(new_name, typ);
        code_deadt new_dead(new_symb_expr);
        it->set_dead(new_dead);
      }
    }
    else {}
    
  }
}

bool check_if_exprt_eval_to_abst_index(
  const exprt &expr,
  const abstraction_spect &abst_spec,
  abstraction_spect::spect &spec)
{
  if(expr.id() == ID_symbol)
  {
    // if it is a symbol, check whether if it is in the entity list
    const symbol_exprt &symb = to_symbol_expr(expr);
    if(abst_spec.has_index_entity(symb.get_identifier()))
    {
      spec = abst_spec.get_spec_for_index_entity(symb.get_identifier());
      return true;
    }
    else
    {
      return false;
    }
  }
  else if(
      expr.id() == ID_const_cast || expr.id() == ID_static_cast || expr.id() == ID_typecast || 
      expr.id() == ID_dynamic_cast || expr.id() == ID_reinterpret_cast)
  {
    // if it is a cast, we check the lower level
    if(expr.operands().size() != 1)
      throw "cast expressions should have one operand";
    return check_if_exprt_eval_to_abst_index(*expr.operands().begin(), abst_spec, spec);
  }
  else if(expr.id() == ID_plus || expr.id() == ID_minus)
  {
    // if it is plus or minus, it should stay the same as the abstracted operand
    if(expr.operands().size() != 2)
      throw "add/minus expressions should have two operands";
    abstraction_spect::spect spec1, spec2;
    bool abs1 = check_if_exprt_eval_to_abst_index(expr.operands()[0], abst_spec, spec1);
    bool abs2 = check_if_exprt_eval_to_abst_index(expr.operands()[1], abst_spec, spec2);
    if(!abs1 && !abs2)
    {
      return false;
    }
    else if(!abs1 && abs2)
    {
      spec = spec2;
      return true;
    }
    else if(abs1 && !abs2)
    {
      spec = spec1;
      return true;
    }
    else
    {
      // TODO: we may want to change that in the future
      // e.g. using abst_index1-abst_index2 might be possible in the code
      throw "Direct computation on two abstracted indices are prohibited";
    }
  }
  else
  {
    return false;
  }
}

symbolt create_function_call(
  const irep_idt &func_name,
  const exprt::operandst operands,
  const irep_idt &caller, 
  const goto_modelt &goto_model,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  // determine the temp symbol's name
  std::unordered_set<irep_idt> new_symbs_name;
  for(const auto &symb: new_symbs)
    new_symbs_name.insert(symb.name);

  auto get_name = [&caller, &func_name, &goto_model, &new_symbs_name]() {
    // base name is "{caller}::$temp::return_value_{callee}"
    std::string base_name = std::string(caller.c_str()) +
                            "::$tmp::return_value_" +
                            std::string(func_name.c_str());
    // if base name is not defined yet, use the base name
    if(
      !goto_model.symbol_table.has_symbol(irep_idt(base_name)) &&
      new_symbs_name.find(irep_idt(base_name)) == new_symbs_name.end())
      return irep_idt(base_name);
    
    // otherwise use "{basename}$id" with the lowest id available
    size_t id = 0;
    while(goto_model.symbol_table.has_symbol(
            irep_idt(base_name + "$" + std::to_string(id))) ||
          new_symbs_name.find(irep_idt(base_name + "$" + std::to_string(id))) !=
            new_symbs_name.end())
      id++;
    
    return irep_idt(base_name + "$" + std::to_string(id));
  };
  irep_idt temp_symb_name = get_name();

  // define the symbol
  symbolt new_symb;
  if(!goto_model.get_symbol_table().has_symbol(func_name))
    throw "unable to find function " + std::string(func_name.c_str()) + " in the symbol table";
  new_symb.type =
    to_code_type(goto_model.get_symbol_table().lookup_ref(func_name).type)
      .return_type();
  new_symb.name = temp_symb_name;
  new_symb.mode = ID_C;
  symbol_exprt new_symb_expr = new_symb.symbol_expr();
  new_symbs.push_back(new_symb);

  // instruction 1: DECLARE of the temp symbol
  auto new_decl_inst = goto_programt::make_decl(code_declt(new_symb_expr));
  insts_before.push_back(new_decl_inst);

  // instruction 2: FUNCTION_CALL
  symbol_exprt func_call_expr =
    goto_model.get_symbol_table().lookup_ref(func_name).symbol_expr();
  auto new_func_call_inst = goto_programt::make_function_call(
    code_function_callt(new_symb_expr, func_call_expr, operands));
  insts_before.push_back(new_func_call_inst);

  // instruction 3: DEAD for the temp symbol 
  auto new_dead_inst = goto_programt::make_dead(new_symb_expr);
  insts_after.push_back(new_dead_inst);

  return new_symb;
}

exprt abstract_expr_write(
  const exprt &expr,
  const abstraction_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  if(!contains_an_entity_to_be_abstracted(expr, abst_spec))
    return expr;
  
  if(expr.id() == ID_symbol)
  {
    // if it is a symbol, we just return the new abstract symbol
    const symbol_exprt &symb = to_symbol_expr(expr);
    irep_idt new_name = get_abstract_name(symb.get_identifier());
    if(goto_model.symbol_table.has_symbol(new_name))
    {
      symbol_exprt new_symb_expr = goto_model.symbol_table.lookup_ref(new_name).symbol_expr();
      return std::move(new_symb_expr);
    }
    else
    {
      std::string error_code = "Abst variable " +
                               std::string(new_name.c_str()) +
                               " used before inserting to the symbol table";
      throw error_code;
    }
  }
  else
  {
    // TODO: actually we also support abstracting array access as lhs
    //       we haven't implemented it yet because there's no such case in our benchmarks
    //       an error is thrown if we find this case
    std::string error_code = "";
    error_code += "Currently, " + std::string(expr.id().c_str()) + "cannot be abstracted as lhs.";
    throw error_code;
  }
}

exprt create_comparator_expr_abs_abs(
  const exprt &orig_expr,
  const abstraction_spect::spect &spec,
  const goto_modelt &goto_model,
  const irep_idt &caller,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  // create the function call is_abst(op0)
  irep_idt is_prec_func = spec.get_precise_func();
  exprt::operandst operands{orig_expr.operands()[0]};
  for(const auto &c_ind: spec.get_shape_indices())
  {
    if(!goto_model.get_symbol_table().has_symbol(c_ind))
      throw "Concrete index symbol " + std::string(c_ind.c_str()) + " not found";
    const symbolt &c_ind_symb = goto_model.get_symbol_table().lookup_ref(c_ind);
    operands.push_back(c_ind_symb.symbol_expr());
  }
  symbolt is_prec_symb = create_function_call(
    is_prec_func, operands, caller, goto_model,
    insts_before, insts_after, new_symbs);
  
  // create the expr op0==op1 ? (is_precise(op0) ? orig_expr : non_det) : orig_expr
  // we allow users to create custom plus/minus functions, 
  // but we use built-in comparator function for comparing two abst indices
  // this is fine because we think this would work for most common shapes such as "*c*", "*c*c*", etc.
  equal_exprt eq_expr_0(orig_expr.operands()[0], orig_expr.operands()[1]);
  typecast_exprt eq_expr(eq_expr_0, bool_typet());
  typecast_exprt is_prec_expr(is_prec_symb.symbol_expr(), bool_typet());
  if_exprt t_expr(is_prec_expr, orig_expr, side_effect_expr_nondett(bool_typet(), source_locationt()));
  if_exprt result_expr(eq_expr, t_expr, orig_expr);
  return std::move(result_expr);
}

exprt abstract_expr_read_comparator(
  const exprt &expr,
  const abstraction_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  // handle comparators, need to call functions if 
  // needed based on whether each operands are abstract
  INVARIANT(
    expr.id() == ID_le || expr.id() == ID_lt || expr.id() == ID_ge ||
      expr.id() == ID_gt || expr.id() == ID_equal || expr.id() == ID_notequal,
    "type of expr does not match abst_read_comparator");
  INVARIANT(expr.operands().size() == 2, "number of ops should be 2 for comparators");

  abstraction_spect::spect spec0;
  abstraction_spect::spect spec1;
  bool abs0 = check_if_exprt_eval_to_abst_index(expr.operands()[0], abst_spec, spec0);
  bool abs1 = check_if_exprt_eval_to_abst_index(expr.operands()[1], abst_spec, spec1);
  if(!abs0 && !abs1)
  {
    // if none of op0 and op1 is abstract index, just do plain comparision.
    exprt new_expr(expr);
    new_expr.operands()[0] = abstract_expr_read(expr.operands()[0], abst_spec, goto_model, current_func, insts_before, insts_after, new_symbs);
    new_expr.operands()[1] = abstract_expr_read(expr.operands()[1], abst_spec, goto_model, current_func, insts_before, insts_after, new_symbs);
    return new_expr;
  }
  else if(abs0 && abs1)
  {
    // if both of them is abstract index, we should do non-det comparision if they are at the same abst value
    exprt new_expr(expr);
    if(!spec0.compare_shape(spec1))
      throw "two operands of a comparator is not of the same spect";
    new_expr.operands()[0] = abstract_expr_read(expr.operands()[0], abst_spec, goto_model, current_func, insts_before, insts_after, new_symbs);
    new_expr.operands()[1] = abstract_expr_read(expr.operands()[1], abst_spec, goto_model, current_func, insts_before, insts_after, new_symbs);
    return create_comparator_expr_abs_abs(new_expr, spec0, goto_model, current_func, insts_before, insts_after, new_symbs);
  }
  else if(abs0 && !abs1)
  {
    // we need to make op1 abstract before calling create_comparator_expr_abs_abs
    exprt new_expr(expr);
    irep_idt abst_func = spec0.get_abstract_func();
    exprt::operandst operands{abstract_expr_read(
      expr.operands()[1], abst_spec, goto_model,
      current_func, insts_before, insts_after, new_symbs)};
    for(const auto &c_ind: spec0.get_shape_indices())
    {
      if(!goto_model.get_symbol_table().has_symbol(c_ind))
        throw "Concrete index symbol " + std::string(c_ind.c_str()) + " not found";
      const symbolt &c_ind_symb = goto_model.get_symbol_table().lookup_ref(c_ind);
      operands.push_back(c_ind_symb.symbol_expr());
    }
    symbolt op1_abst_symb = create_function_call(
      abst_func, operands, current_func, goto_model, 
      insts_before, insts_after, new_symbs);
    new_expr.operands()[0] = abstract_expr_read(expr.operands()[0], abst_spec, goto_model, current_func, insts_before, insts_after, new_symbs);
    new_expr.operands()[1] = op1_abst_symb.symbol_expr();
    return create_comparator_expr_abs_abs(new_expr, spec0, goto_model, current_func, insts_before, insts_after, new_symbs);
  }
  else  // !abs0 && abs1
  {
    // we need to make op0 abstract before calling create_comparator_expr_abs_abs
    exprt new_expr(expr);
    irep_idt abst_func = spec1.get_abstract_func();
    exprt::operandst operands{abstract_expr_read(
      expr.operands()[0], abst_spec, goto_model,
      current_func, insts_before, insts_after, new_symbs)};
    for(const auto &c_ind: spec1.get_shape_indices())
    {
      if(!goto_model.get_symbol_table().has_symbol(c_ind))
        throw "Concrete index symbol " + std::string(c_ind.c_str()) + " not found";
      const symbolt &c_ind_symb = goto_model.get_symbol_table().lookup_ref(c_ind);
      operands.push_back(c_ind_symb.symbol_expr());
    }
    symbolt op0_abst_symb = create_function_call(
      abst_func, operands, current_func, goto_model, 
      insts_before, insts_after, new_symbs);
    new_expr.operands()[0] = op0_abst_symb.symbol_expr();
    new_expr.operands()[1] = abstract_expr_read(expr.operands()[1], abst_spec, goto_model, current_func, insts_before, insts_after, new_symbs);
    return create_comparator_expr_abs_abs(new_expr, spec1, goto_model, current_func, insts_before, insts_after, new_symbs);
  }
}

exprt abstract_expr_read_plusminus(
  const exprt &expr,
  const abstraction_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  // handle plus/minus, should call plus/minus function if needed
  INVARIANT(expr.id() == ID_plus || expr.id() == ID_minus, "abst_read_plus_minus should get + or - exprs");
  INVARIANT(expr.operands().size() == 2, "The number of operands should be 2 for plus/minus");

  abstraction_spect::spect spec0;
  abstraction_spect::spect spec1;
  bool abs0 = check_if_exprt_eval_to_abst_index(expr.operands()[0], abst_spec, spec0);
  bool abs1 = check_if_exprt_eval_to_abst_index(expr.operands()[1], abst_spec, spec1);
  if(!abs0 && !abs1)
  {
    exprt new_expr(expr);
    new_expr.operands()[0] = abstract_expr_read(expr.operands()[0], abst_spec, goto_model, current_func, insts_before, insts_after, new_symbs);
    new_expr.operands()[1] = abstract_expr_read(expr.operands()[1], abst_spec, goto_model, current_func, insts_before, insts_after, new_symbs);
    return new_expr;
  }
  else if((!abs0 && abs1) || (abs0 && !abs1))
  {
    // couldn't do conc-abs
    if(!abs0 && abs1 && expr.id() == ID_minus)
      throw "We couldn't do concrete_index-abst_index right now";
    
    // what is the spec we are using?
    const abstraction_spect::spect &spec = abs0 ? spec0 : spec1;
    // find the func name of add_abs_to_conc
    const irep_idt &calc_func_name = expr.id() == ID_plus ? spec.get_addition_func() : spec.get_minus_func();
    // define the operands {abs, num}
    exprt op0 = abstract_expr_read(
      abs0 ? expr.operands()[0] : expr.operands()[1],
      abst_spec, goto_model, current_func,
      insts_before, insts_after, new_symbs);
    exprt op1 = abs0 ? expr.operands()[1] : expr.operands()[0];
    exprt::operandst operands{op0, op1};
    // put the concrete indices into operands
    for(const auto &c_ind: spec.get_shape_indices())
    {
      if(!goto_model.get_symbol_table().has_symbol(c_ind))
        throw "Concrete index symbol " + std::string(c_ind.c_str()) + " not found";
      const symbolt &c_ind_symb = goto_model.get_symbol_table().lookup_ref(c_ind);
      operands.push_back(c_ind_symb.symbol_expr());
    }
    // make the function call
    symbolt temp_var = create_function_call(
      calc_func_name, operands, current_func,
      goto_model, insts_before, insts_after, new_symbs);
    return std::move(temp_var.symbol_expr());
  }
  else
  {
    // this is an error
    throw "Direct computation on two abstracted indices are prohibited";
  }
}

exprt abstract_expr_read_dereference(
  const exprt &expr,
  const abstraction_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  INVARIANT(expr.id() == ID_dereference, "abstract_expr_read_dereference should get dereference exprs");
  INVARIANT(expr.operands().size() == 1, "The number of operands should be 1 for dereference");

  // the pointer to be dereferenced
  exprt pointer_expr = expr.operands()[0];

  if(pointer_expr.id() == ID_symbol)
  {
    const symbol_exprt pointer_symb_expr = to_symbol_expr(pointer_expr);
    const irep_idt orig_name = pointer_symb_expr.get_identifier();
    if(abst_spec.has_array_entity(orig_name))
    {
      const irep_idt new_name = get_abstract_name(orig_name);
      if(!goto_model.symbol_table.has_symbol(new_name))
        throw "The abst symbol " + std::string(new_name.c_str()) + " is not added to the symbol table";
      const symbolt &abst_symb = goto_model.symbol_table.lookup_ref(new_name);
      dereference_exprt new_expr(abst_symb.symbol_expr());
      return std::move(new_expr);
    }
    else
    {
      return expr;
    }
  }
  else if(pointer_expr.id() == ID_plus)
  {
    INVARIANT(pointer_expr.operands().size() == 2, "The number of operands should be 2 for plus/minus");
    const exprt &base_pointer = pointer_expr.operands()[0];
    const exprt &offset_expr = pointer_expr.operands()[1];
    if(base_pointer.id() == ID_symbol && base_pointer.type().id() == ID_pointer)
    {
      const irep_idt base_pointer_orig_name = to_symbol_expr(base_pointer).get_identifier();
      if(abst_spec.has_array_entity(base_pointer_orig_name))
      {
        // a[i]  ==>   is_prec(i$abst) ? a$abst[i$abst] : nondet

        // get the new base pointer a$abst
        const irep_idt base_pointer_new_name = get_abstract_name(base_pointer_orig_name);
        if(!goto_model.symbol_table.has_symbol(base_pointer_new_name))
          throw "The abst symbol " + std::string(base_pointer_new_name.c_str()) + " is not added to the symbol table";
        const symbolt &abst_base_pointer_symb = goto_model.symbol_table.lookup_ref(base_pointer_new_name);
        const exprt new_base_pointer = abst_base_pointer_symb.symbol_expr();

        // get the new offset i$abst
        const exprt new_offset = abstract_expr_read(
          offset_expr, abst_spec, goto_model, current_func,
          insts_before, insts_after, new_symbs);

        // the access a$abst[i$abst]
        plus_exprt new_plus_expr(abst_base_pointer_symb.symbol_expr(), new_offset);
        dereference_exprt new_access(new_plus_expr);

        // the function call is_prec(i$abst)
        const auto &spec = abst_spec.get_spec_for_array_entity(base_pointer_orig_name);
        exprt::operandst operands{new_offset};
        for(const auto &c_ind: spec.get_shape_indices())
        {
          if(!goto_model.get_symbol_table().has_symbol(c_ind))
          throw "Concrete index symbol " + std::string(c_ind.c_str()) + " not found";
          const symbolt &c_ind_symb = goto_model.get_symbol_table().lookup_ref(c_ind);
          operands.push_back(c_ind_symb.symbol_expr());
        }
        const symbolt is_prec_symb = create_function_call(
          spec.get_precise_func(), operands, current_func,
          goto_model, insts_before, insts_after, new_symbs);
        const exprt is_prec = is_prec_symb.symbol_expr();
        const typecast_exprt is_prec_bool(is_prec, bool_typet());

        // the final expression is_prec(i$abst) ? a$abst[i$abst] : nondet
        if_exprt final_expr(
          is_prec_bool, new_access,
          side_effect_expr_nondett(expr.type(), source_locationt()));
        return std::move(final_expr);
      }
      else
      {
        const exprt new_offset = abstract_expr_read(
          offset_expr, abst_spec, goto_model, current_func,
          insts_before, insts_after, new_symbs);
        plus_exprt new_plus_expr(base_pointer, new_offset);
        dereference_exprt new_expr(new_plus_expr);
        return std::move(new_expr);
      }
    }
    else
    {
      throw "unknown type of dereference";
    }
  }
  else
  {
    throw "Unknown type to be dereferenced: " + std::string(pointer_expr.id().c_str());
  }
}

exprt abstract_expr_read(
  const exprt &expr,
  const abstraction_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  if(!contains_an_entity_to_be_abstracted(expr, abst_spec))
    return expr;
  
  if(expr.id() == ID_symbol)
  {
    // if it is a symbol, we just return the new abstract symbol
    const symbol_exprt &symb = to_symbol_expr(expr);
    irep_idt new_name = get_abstract_name(symb.get_identifier());
    if(goto_model.symbol_table.has_symbol(new_name))
    {
      symbol_exprt new_symb_expr = goto_model.symbol_table.lookup_ref(new_name).symbol_expr();
      return std::move(new_symb_expr);
    }
    else
    {
      std::string error_code = "Abst variable " +
                               std::string(new_name.c_str()) +
                               " used before inserting to the symbol table";
      throw error_code;
    }
  }
  else if(
    expr.id() == ID_typecast || expr.id() == ID_and || expr.id() == ID_or ||
    expr.id() == ID_xor || expr.id() == ID_not || expr.id() == ID_implies ||
    expr.id() == ID_is_invalid_pointer || expr.id() == ID_is_dynamic_object || 
    expr.id() == ID_pointer_object || expr.id() == ID_pointer_offset || 
    expr.id() == ID_object_size)
  {
    // those types of exprs should not be changed, just run abst_read on lower level
    exprt new_expr(expr);
    for(size_t i = 0; i < expr.operands().size(); i++)
      new_expr.operands()[i] = abstract_expr_read(expr.operands()[i], abst_spec, goto_model, current_func, insts_before, insts_after, new_symbs);
    return new_expr;
  }
  else if(
    expr.id() == ID_le || expr.id() == ID_lt || expr.id() == ID_ge ||
    expr.id() == ID_gt || expr.id() == ID_equal || expr.id() == ID_notequal)
  {
    // handle comparators, need to call functions if 
    // needed based on whether each operands are abstract
    return abstract_expr_read_comparator(
      expr,abst_spec, goto_model, current_func,
      insts_before, insts_after, new_symbs);
  }
  else if(expr.id() == ID_dereference)
  {
    // TODO: handle dereference, need to check the structure of lower exprts
    return abstract_expr_read_dereference(
      expr,abst_spec, goto_model, current_func,
      insts_before, insts_after, new_symbs);
  }
  else if(expr.id() == ID_plus || expr.id() == ID_minus)
  {
    // handle plus/minus, should call plus/minus function if needed
    return abstract_expr_read_plusminus(
      expr, abst_spec, goto_model, current_func,
      insts_before, insts_after, new_symbs);
  }
  else
  {
    // TODO: actually we also support abstracting array access as lhs
    //       we haven't implemented it yet because there's no such case in our benchmarks
    //       an error is thrown if we find this case
    std::string error_code = "";
    error_code += "Currently, " + std::string(expr.id().c_str()) + " cannot be abstracted in abst_read.";
    throw error_code;
  }
}

void define_concrete_indices(goto_modelt &goto_model, const abstraction_spect &abst_spec)
{
  for(const auto &spec: abst_spec.get_specs())
  {
    for(const irep_idt &index: spec.get_shape_indices())
    {
      // define the "index" in the global scope
      // Step 0: Define the symbolt. what is the type/location of this variable?
      // The type should be size_t, which is unsigned_long_int_type
      // mode should be C
      unsignedbv_typet index_type = unsigned_long_int_type();
      source_locationt src_loc;
      symbolt symb;
      symb.type = index_type;
      symb.location = src_loc;
      symb.name = index;
      symb.mode = ID_C;
      symbol_exprt symb_expr = symb.symbol_expr();

      // Step 1: put it into the symbol table
      if(goto_model.symbol_table.has_symbol(index))
        throw "the concrete index variable " + std::string(index.c_str()) + " is already defined";
      goto_model.symbol_table.insert(std::move(symb));

      // Step 2: put it into __CPROVER_initialize which is the entry function for each goto program
      goto_functionst::function_mapt::iterator fct_entry =
        goto_model.goto_functions.function_map.find(INITIALIZE_FUNCTION);
      CHECK_RETURN(fct_entry != goto_model.goto_functions.function_map.end());
      goto_programt &init_function = fct_entry->second.body;
      auto last_instruction = std::prev(init_function.instructions.end());
      DATA_INVARIANT(
        last_instruction->is_end_function(),
        "last instruction in function should be END_FUNCTION");
      goto_programt::instructiont new_inst = goto_programt::make_assignment(
        code_assignt(symb_expr, side_effect_expr_nondett(index_type, src_loc)));
      init_function.insert_before_swap(last_instruction, new_inst);
    }
  }
}

void insert_shape_assumptions(goto_modelt &goto_model, const abstraction_spect &abst_spec)
{


  namespacet ns(goto_model.get_symbol_table());
  for(const auto &spec: abst_spec.get_specs())
  {
    for(const exprt &expr: spec.get_assumption_exprs(ns))
    {
      // put the assumption expr into __CPROVER_initialize 
      // which is the entry function for each goto program
      goto_functionst::function_mapt::iterator fct_entry =
        goto_model.goto_functions.function_map.find(INITIALIZE_FUNCTION);
      CHECK_RETURN(fct_entry != goto_model.goto_functions.function_map.end());
      goto_programt &init_function = fct_entry->second.body;
      auto last_instruction = std::prev(init_function.instructions.end());
      DATA_INVARIANT(
        last_instruction->is_end_function(),
        "last instruction in function should be END_FUNCTION");

      goto_programt::instructiont new_inst = goto_programt::make_assumption(expr);
      init_function.insert_before_swap(last_instruction, new_inst);
    }
  }
}

void add_length_assumptions(goto_modelt &goto_model, const abstraction_spect &abst_spec)
{
  for(const auto &spec: abst_spec.get_specs())
  {
    for(const auto &lp: spec.get_abst_lengths())
    {
      const irep_idt func_name = abst_spec.get_func_name();

      // TODO: currently we are assuming every entities in the 
      // json file belong to the same function. That may not be the case.
      auto &function = goto_model.goto_functions.function_map.at(func_name);
      // if this variable is a local varible
      bool is_local = false;

      // go through each instruction in the function to find the declare
      Forall_goto_program_instructions(it, function.body)
      {
        if(it->is_decl())
        {
          const code_declt &decl = it->get_decl();
          // check if this declares the length variable
          if(decl.get_identifier() == lp.first)
          {
            is_local = true;
            // need to add an assumption after this inst
            INVARIANT(
              goto_model.get_symbol_table().has_symbol(decl.get_identifier()),
              "Symbol " + std::string(decl.get_identifier().c_str()) +
                " not defined");
            INVARIANT(
              goto_model.get_symbol_table().has_symbol(
                spec.get_length_index_name()),
              "Symbol " + std::string(spec.get_length_index_name().c_str()) +
                " not defined");

            // define the assumption instruction
            const symbolt symb1 = goto_model.get_symbol_table().lookup_ref(decl.get_identifier());
            const symbolt symb2 = goto_model.get_symbol_table().lookup_ref(spec.get_length_index_name());
            equal_exprt assumption_expr(symb1.symbol_expr(), symb2.symbol_expr());
            auto new_assumption = goto_programt::make_assumption(assumption_expr);

            // insert it
            function.body.insert_after(it, new_assumption);
            std::cout << "Added length assumption after the decl: ";
            format_rec(std::cout, assumption_expr) << std::endl;
            it++;
          }
        }
      }

      // if it is not a local variable, the assumption should be added at 
      // the end of the global INITIAL function
      if(!is_local)
      {
        // find the CPROVER_INITIAL function
        goto_functionst::function_mapt::iterator fct_entry =
          goto_model.goto_functions.function_map.find(INITIALIZE_FUNCTION);
        CHECK_RETURN(fct_entry != goto_model.goto_functions.function_map.end());
        goto_programt &init_function = fct_entry->second.body;
        auto last_instruction = std::prev(init_function.instructions.end());
        DATA_INVARIANT(
          last_instruction->is_end_function(),
          "last instruction in function should be END_FUNCTION");
        
        // define the assumption instruction
        INVARIANT(
          goto_model.get_symbol_table().has_symbol(lp.first),
          "Symbol " + std::string(lp.first.c_str()) +
            " not defined");
        INVARIANT(
          goto_model.get_symbol_table().has_symbol(
            spec.get_length_index_name()),
          "Symbol " + std::string(spec.get_length_index_name().c_str()) +
            " not defined");
        const symbolt symb1 = goto_model.get_symbol_table().lookup_ref(lp.first);
        const symbolt symb2 = goto_model.get_symbol_table().lookup_ref(spec.get_length_index_name());
        equal_exprt assumption_expr(symb1.symbol_expr(), symb2.symbol_expr());
        auto new_assumption = goto_programt::make_assumption(assumption_expr);

        // insert it
        std::cout << "Added length assumption in the beginning of the function: ";
        format_rec(std::cout, assumption_expr);
        init_function.insert_before_swap(last_instruction, new_assumption);
      }
    }
  }
}

void abstract_goto_program(goto_modelt &goto_model, abstraction_spect &abst_spec)
{
  // Define the global concrete indices to be used
  define_concrete_indices(goto_model, abst_spec);

  // Insert the assumptions about concrete indices
  insert_shape_assumptions(goto_model, abst_spec);

  // Add the assumption for len==$clen
  add_length_assumptions(goto_model, abst_spec);

  // A couple of spects are initialized from the json file. We should go from there and insert spects to other functions
  std::unordered_map<irep_idt, abstraction_spect> function_spec_map =
    calculate_complete_abst_specs_for_funcs(goto_model, abst_spec);
  std::unordered_set<irep_idt> abst_symbol_set;
  for(auto &p: function_spec_map)
    declare_abst_variables_for_func(goto_model, p.first, p.second, abst_symbol_set);
  
  for(auto &p: function_spec_map)
  {
    std::cout << "=========== " << p.first << " ===========" << std::endl;
    std::cout << "----------- " << "Entities to be abstracted" << " -----------" << std::endl;
    p.second.print_entities();
    std::cout << "----------- " << "Exprs containing the above entities" << " -----------" << std::endl;
    goto_functiont &goto_function = goto_model.goto_functions.function_map.at(p.first);
    const abstraction_spect &abst_spec = p.second;
    Forall_goto_program_instructions(it, goto_function.body)
    {
      // go through all expressions
      goto_programt::instructionst inst_before;
      goto_programt::instructionst inst_after;
      std::vector<symbolt> new_symbs;

      // need to backup the expr for assertion
      exprt assert_orig_expr;
      if(it->is_assert())
        assert_orig_expr = it->get_condition();
      
      // go through conditions
      if(it->has_condition())
      {
        if(contains_an_entity_to_be_abstracted(it->get_condition(), abst_spec))
        {
          format_rec(std::cout, it->get_condition()) << " ==abst_read==> ";
          exprt new_condition = abstract_expr_read(it->get_condition(), abst_spec, goto_model, p.first, inst_before, inst_after, new_symbs);
          format_rec(std::cout, new_condition) << std::endl;
          it->set_condition(new_condition);
        }
      }
      
      if(it->is_function_call())
      {
        const code_function_callt fc = it->get_function_call();
        exprt new_lhs;
        if(contains_an_entity_to_be_abstracted(fc.lhs(), abst_spec))
        {
          format_rec(std::cout, fc.lhs()) << " ==abst_write==> ";
          new_lhs = abstract_expr_write(fc.lhs(), abst_spec, goto_model, p.first, inst_before, inst_after, new_symbs);
          format_rec(std::cout, new_lhs) << std::endl;
        }
        else
        {
          new_lhs = fc.lhs();
        }

        code_function_callt::argumentst new_arguments;
        for(const auto &arg : fc.arguments())
        {
          exprt new_arg;
          if(contains_an_entity_to_be_abstracted(arg, abst_spec))
          {
            format_rec(std::cout, arg) << " ==abst_read==> ";
            new_arg = abstract_expr_read(arg, abst_spec, goto_model, p.first, inst_before, inst_after, new_symbs);
            format_rec(std::cout, new_arg) << std::endl;
            new_arguments.push_back(new_arg);
          }
          else
          {
            new_arguments.push_back(arg);
          }
        }

        code_function_callt new_fc(new_lhs, fc.function(), new_arguments);
        it->set_function_call(new_fc);
      }
      else if(it->is_assign())
      {
        const code_assignt as = it->get_assign();
        exprt new_lhs;
        if(contains_an_entity_to_be_abstracted(as.lhs(), abst_spec))
        {
          format_rec(std::cout, as.lhs()) << " ==abst_write==> ";
          new_lhs = abstract_expr_write(as.lhs(), abst_spec, goto_model, p.first, inst_before, inst_after, new_symbs);
          format_rec(std::cout, new_lhs) << std::endl;
        }
        else
        {
          new_lhs = as.lhs();
        }

        exprt new_rhs;
        if(contains_an_entity_to_be_abstracted(as.rhs(), abst_spec))
        {
          format_rec(std::cout, as.rhs()) << " ==abst_read==> ";
          new_rhs = abstract_expr_read(as.rhs(), abst_spec, goto_model, p.first, inst_before, inst_after, new_symbs);
          format_rec(std::cout, new_rhs) << std::endl;
        }
        else
        {
          new_rhs = as.rhs();
        }

        code_assignt new_as(new_lhs, new_rhs);
        it->set_assign(new_as);
      }
      else if(it->is_assert())
      {
        // if this is assertion, we should make the condition optimistic
        format_rec(std::cout, it->get_condition()) << " ==optimistic==> ";
        exprt optim_cond = add_guard_expression_to_assert(
          it->get_condition(), assert_orig_expr, abst_spec,
          goto_model, p.first, inst_before, inst_after, new_symbs);
        format_rec(std::cout, optim_cond) << std::endl;
        it->set_condition(optim_cond);
      }

      // is there any unknown inst types?
      if(
        !it->is_decl() && !it->is_end_function() && !it->is_goto() &&
        !it->is_return() && !it->is_function_call() && !it->is_assert() &&
        !it->is_assign() && !it->is_assume() && !it->is_dead())
        throw "Unknown instruction type " + std::to_string(it->type);
      
      // insert new instructions before it
      for(auto &inst: inst_before)
      {
        goto_function.body.insert_before_swap(it, inst);
        it++;
      }

      // insert new instructions after it
      for(auto &inst: inst_after)
      {
        goto_function.body.insert_after(it, inst);
        it++;
      }

      // insert new symbols to the symbol table
      for(auto &symb: new_symbs)
      {
        if(goto_model.get_symbol_table().has_symbol(symb.name))
          throw "the temp symbol " + std::string(symb.name.c_str()) + " is already defined";
        goto_model.symbol_table.insert(symb);
      }
    }
  }
}
