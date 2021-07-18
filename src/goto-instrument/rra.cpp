/*******************************************************************\

Module: Replication Reducing Abstraction

Author: Adrian Palacios accorell@amazon.com
        Murali Talupur  talupur@amazon.com
        Lefan Zhang     lefanz@amazon.com

\*******************************************************************/

/// \file
/// Replication Reducing Abstraction
/// Abstract certain data types to make proofs unbounded

#include <iostream>
#include <queue>

#include "rra.h"

#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_goto_model.h>
#include <linking/static_lifetime_init.h>
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/pointer_predicates.h>
#include <util/std_expr.h>
#include <util/pointer_expr.h>
#include <analyses/natural_loops.h>
#include <analyses/local_may_alias.h>
#include <goto-instrument/loop_utils.h>

irep_idt rrat::get_string_id_from_exprt(const exprt &expr)
{
  if(expr.id() == ID_symbol)
  {
    const symbol_exprt &symb_expr = to_symbol_expr(expr);
    return symb_expr.get_identifier();
  }
  else if(expr.id() == ID_member)
  {
    INVARIANT(
      expr.operands().size() == 1,
      "member access should only have one operand");
    const member_exprt &mem_expr = to_member_expr(expr);
    const exprt &obj_expr = expr.operands()[0];
    const irep_idt &comp_name = mem_expr.get_component_name();

    // we need to get rid of dereference/address_of pairs
    // e.g. *&*&buf
    exprt current_obj_expr = obj_expr;
    while((current_obj_expr.id() == ID_dereference &&
           current_obj_expr.operands()[0].id() == ID_address_of) ||
          (current_obj_expr.id() == ID_address_of &&
           current_obj_expr.operands()[0].id() == ID_dereference))
      current_obj_expr = current_obj_expr.operands()[0].operands()[0];
    // buf->a --translated--> (*buf).a
    if(current_obj_expr.id() == ID_dereference)
    {
      INVARIANT(
        current_obj_expr.operands().size() == 1,
        "dereference should only have one operand");
      const exprt &pointer = current_obj_expr.operands()[0]; // buf
      irep_idt pointer_str_id = get_string_id_from_exprt(pointer);
      return std::string(pointer_str_id.c_str()) + "->" +
             std::string(comp_name.c_str());
    }
    else // buf.a
    {
      irep_idt obj_str_id = get_string_id_from_exprt(current_obj_expr); // buf
      return std::string(obj_str_id.c_str()) + "." +
             std::string(comp_name.c_str());
    }
  }
  else
  {
    throw "cannot translate to string id for expression " +
      std::string(expr.id().c_str());
  }
}

// check if an expr is a entity
// e.g. a, b, a.len, b->len are all entities
// *buf_p.len is a entity,
// but *(buf_p+1).len is not considered as one
bool rrat::is_entity_expr(const exprt &expr)
{
  if(expr.id() == ID_symbol)
  {
    return true;
  }
  else if(expr.id() == ID_member)
  {
    INVARIANT(
      expr.operands().size() == 1,
      "member access should only have one operand");
    const exprt &obj_expr = expr.operands()[0];

    // we need to get rid of dereference/address_of pairs
    // e.g. *&*&buf
    exprt current_obj_expr = obj_expr;
    while((current_obj_expr.id() == ID_dereference &&
           current_obj_expr.operands()[0].id() == ID_address_of) ||
          (current_obj_expr.id() == ID_address_of &&
           current_obj_expr.operands()[0].id() == ID_dereference))
      current_obj_expr = current_obj_expr.operands()[0].operands()[0];
    // buf->a --translated--> (*buf).a
    if(current_obj_expr.id() == ID_dereference)
    {
      INVARIANT(
        current_obj_expr.operands().size() == 1,
        "dereference should only have one operand");
      const exprt &pointer = current_obj_expr.operands()[0]; // buf
      return is_entity_expr(pointer);
    }
    else // buf.a
    {
      return is_entity_expr(current_obj_expr);
    }
  }
  else
  {
    return false;
  }
}

std::pair<std::string, irep_idt> rrat::get_parent_id(const irep_idt &id)
{
  std::string id_str = id.c_str();
  size_t arrow_pos = id_str.rfind("->");
  size_t point_pos = id_str.rfind(".");
  if(arrow_pos != std::string::npos && point_pos != std::string::npos)
  {
    if(arrow_pos > point_pos) // should be "->"
      return std::make_pair("->", id_str.substr(0, arrow_pos));
    else // should be "."
      return std::make_pair(".", id_str.substr(0, point_pos));
  }
  else if(arrow_pos == std::string::npos && point_pos != std::string::npos)
  {
    // should be "."
    return std::make_pair(".", id_str.substr(0, point_pos));
  }
  else if(arrow_pos != std::string::npos && point_pos == std::string::npos)
  {
    // should be "->"
    return std::make_pair("->", id_str.substr(0, arrow_pos));
  }
  else // both "->" and "." are not found
  {
    return std::make_pair("", irep_idt(""));
  }
}

void rrat::link_abst_functions(
  goto_modelt &goto_model,
  const rra_spect &abst_spec,
  ui_message_handlert &msg_handler,
  const optionst &options)
{
  // get abst function file names
  std::vector<std::string> abstfiles =
    abst_spec.get_abstraction_function_files();
  // read files
  goto_modelt goto_model_for_abst_fns =
    initialize_goto_model(abstfiles, msg_handler, options);
  // link goto model
  link_goto_model(goto_model, goto_model_for_abst_fns, msg_handler);
}

std::unordered_set<irep_idt> rrat::get_all_funcs_called(
  const goto_functiont &goto_function)
{
  std::unordered_set<irep_idt> funcs_called;
  forall_goto_program_instructions(it, goto_function.body)
  {
    // go through all expressions
    if(it->is_function_call())
    {
      const code_function_callt fc = it->get_function_call();
      const irep_idt &new_func_name =
        to_symbol_expr(fc.function()).get_identifier();

      if(funcs_called.find(new_func_name) == funcs_called.end())
        funcs_called.insert(new_func_name);
    }
  }
  return funcs_called;
}

/// check if an expr is address_of or dereference
/// \return flag: 0(none); 1(address_of) -1(dereference)
rra_spect::spect::func_call_arg_namet::arg_translate_typet
rrat::check_expr_is_address_or_deref(const exprt &expr, exprt &next_layer)
{
  if(expr.id() == ID_dereference)
  {
    INVARIANT(
      expr.operands().size() == 1, "dereference should only have one operand");
    next_layer = expr.operands()[0];
    return rra_spect::spect::func_call_arg_namet::POINTER_TO_ENTITY;
  }
  else if(expr.id() == ID_address_of)
  {
    INVARIANT(
      expr.operands().size() == 1, "address_of should only have one operand");
    next_layer = expr.operands()[0];
    return rra_spect::spect::func_call_arg_namet::ENTITY_TO_POINTER;
  }
  else
  {
    return rra_spect::spect::func_call_arg_namet::REGULAR;
  }
}

/// check if expr is a symbol (or typecast from a symbol)
/// \return the symbol name, "" if expr is not a symbol
irep_idt rrat::check_expr_is_symbol(const exprt &expr)
{
  if(expr.id() == ID_symbol || expr.id() == ID_member)
  {
    // if it is a symbol, return itself's name
    return get_string_id_from_exprt(expr);
  }
  else if(expr.id() == ID_typecast)
  {
    // if it is a typecast, check the next level
    // typecast are something like (char *)lhs, (size_t)a
    return check_expr_is_symbol(expr.operands()[0]);
  }
  else
  {
    // otherwise, the argument is not a symbol
    return irep_idt("");
  }
}

std::unordered_set<irep_idt> rrat::get_all_functions(
  goto_modelt &goto_model)
{
  std::unordered_set<irep_idt> all_functions;
  // The following is a search of functions.
  // At each step, we pop one function A from the todo list.
  // We analyze A to see if it calls other functions.
  // If any other functions are called and have not been analyzed, 
  // we also analyze that function, 
  // and then push that to the todo list.
  // Each function is only analyzed for one time. 
  std::set<irep_idt> todo;  // functions to be further analyzed
  todo.insert(goto_model.get_goto_functions().entry_point());  // the analysis starts from the init function

  while(!todo.empty())
  {
    // pop the first function in the todo list
    irep_idt current_func_name = *todo.begin();
    INVARIANT(all_functions.find(current_func_name) == all_functions.end(), "we should never analyze the same functino twice");
    todo.erase(current_func_name);
    all_functions.insert(current_func_name);

    const goto_functiont &current_func = goto_model.get_goto_function(current_func_name);

    // check it calls any other functions that we need to abstract
    std::unordered_set<irep_idt> funcs_called = get_all_funcs_called(current_func);

    // for each function we need to abstract, check if it's already analyzed
    // if not, we analyze it and put it into the function_spec_map and todo
    for(const auto &new_func_name: funcs_called)
    {
      if(todo.find(new_func_name) == todo.end() &&
          all_functions.find(new_func_name) == all_functions.end())
        todo.insert(new_func_name);
    }
  }

  return all_functions;
}

bool rrat::contains_an_entity_to_be_abstracted(
  const exprt &expr,
  const rra_spect &abst_spec)
{
  struct match_abst_symbolt
  {
    explicit match_abst_symbolt(const rra_spect &_abst_spec)
      : abst_spec(_abst_spec)
    {
    }
    // check if expr is an entity symbol that we want to abstract
    bool operator()(const exprt &expr)
    {
      irep_idt symbol_name = check_expr_is_symbol(expr);
      return symbol_name != "" && abst_spec.has_entity(symbol_name);
    }

  protected:
    // we assume this abst_spec's life span covers
    // the life span of the match_abst_symbolt object
    const rra_spect &abst_spec;
  };
  match_abst_symbolt match_abst_symbol(abst_spec);
  return has_subexpr(expr, match_abst_symbol);
}

irep_idt rrat::get_abstract_name(const irep_idt &old_name)
{
  return irep_idt(std::string(old_name.c_str()) + "$abst");
}

irep_idt rrat::get_const_c_str_len_name(const irep_idt &c_str_name)
{
  return irep_idt(std::string(c_str_name.c_str()) + "$cstrlen$abst");
}

irep_idt rrat::get_memory_addr_name(const irep_idt &entity_name)
{
  return irep_idt(std::string(entity_name.c_str())+"$abst$memobj");
}

bool rrat::contains_a_function_call(const exprt &expr)
{
  class find_functiont : public const_expr_visitort
  {
  public:
    bool found;
    find_functiont() : found(false)
    {
    }
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

std::vector<exprt>
rrat::get_dereferenced_pointers(const exprt &expr)
{
  class find_dereferenced_pointerst : public const_expr_visitort
  {
  protected:
    std::vector<exprt> dereferenced_pointers;
    std::unordered_set<irep_idt> symbol_addresses;
  public:
    find_dereferenced_pointerst() {}
    void operator()(const exprt &expr)
    {
      if(expr.id() == ID_dereference)
      {
        INVARIANT(expr.operands().size() == 1, "dereference should only have one operand");
        const exprt pointer_expr = expr.operands()[0];
        if(pointer_expr.id() == ID_symbol)
        {
          // It only checks for identical symbols. If i+j appears in two places, it will be handled as two 
          // different references.
          const symbol_exprt &pointer_expr_symb = to_symbol_expr(pointer_expr);
          if(symbol_addresses.find(pointer_expr_symb.get_identifier()) == symbol_addresses.end())
          {
            symbol_addresses.insert(pointer_expr_symb.get_identifier());
            dereferenced_pointers.push_back(pointer_expr);
          }
        }
        else
        {
          dereferenced_pointers.push_back(pointer_expr);
        }
      }
    }
    std::vector<exprt> get_dereferenced_pointers() const
    {
      return dereferenced_pointers;
    }
  };
  find_dereferenced_pointerst fdp;
  expr.visit(fdp);
  return fdp.get_dereferenced_pointers();
}

exprt rrat::add_guard_expression_to_assert(
  const exprt &expr,
  const exprt &expr_before_abst,
  const rra_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs,
  std::unordered_map<size_t, size_t> &insts_before_goto_target_map)
{
  // ======================
  // declare is_prec
  // is_prec=true
  // for every spec$x: counter_spec$x = 0
  // for every dereference deref(pointer) in assertion (the pointer should be the original one which need to be read again)
  //   for every abst array with obj array$obj (using spec$x)
  //     if (pointer_object(pointer) != array$obj) GOTO endif
  //       declare abst_index
  //       declare is_prec_ret
  //       abst_index = abstract(pointer_offset(pointer))
  //       is_prec_ret = is_precise(abst_index)
  //       is_prec = is_prec && is_prec_ret
  //       counter_spec$x++
  //       dead is_prec_ret
  //       dead abst_index
  //       GOTO end ==> this is important because when two abst arrays refer to the same obj, 
  //                    we don't want to count twice in the invariant check.
  //     endif: SKIP
  //   end for
  // end for
  // end: for every spec$x: assert(1+number of length vars+counter_spec$x<=number of concrete index in spec$x)
  // assert(is_prec -> xxxxx)
  // dead is_prec
  // ======================
  // example on why we couldn't directly run is_prec on i$abst
  // lhs
  // a = lhs+3
  // a+i$abst
  // abst_read(a+i$abst) ---->  a+conc(i$abst)
  // pointer_offset(a+conc(i$abst)) = conc(i$abst)+3
  // add_abst(i$abst, 3)

  if(contains_a_function_call(expr_before_abst))
  {
    const char *assertion_error =
      "the assertion contains a function call. "
      "Currently our system doesn't support it.";
    throw assertion_error;
  }
  
  // declare is_prec=true
  symbolt is_prec_symb = create_temp_var(
    "is_prec", bool_typet(), current_func, goto_model, 
    insts_before, insts_after, new_symbs);
  insts_before.push_back(goto_programt::make_assignment(is_prec_symb.symbol_expr(), true_exprt()));

  // for every spec$x: counter_spec$x = 0
  const auto zero_uint = zero_initializer(unsigned_int_type(), source_locationt(), namespacet(goto_model.symbol_table));
  CHECK_RETURN(zero_uint.has_value());
  const constant_exprt one_uint = constant_exprt(integer2bvrep(1, unsigned_int_type().get_width()), unsigned_int_type());
  std::vector<symbolt> spec_access_counters;
  for(size_t i = 0; i < abst_spec.get_specs().size(); i++)
  {
    symbolt access_counter = create_temp_var("access_counter", unsigned_int_type(), current_func, goto_model, insts_before, insts_after, new_symbs);
    spec_access_counters.push_back(access_counter);
    insts_before.push_back(goto_programt::make_assignment(access_counter.symbol_expr(), *zero_uint));
  }

  std::unordered_map<size_t, std::string> goto_label_map;  // goto's index in insts_before ==> labels: "0","1",..., "deft", "end"
  std::unordered_map<std::string, size_t> label_target_map;  // labels: "0"..."end" ==> target inst's index in insts_before

  size_t counter = 0;
  // get all pointers to be dereferenced in this function
  for(const exprt &pointer_old: get_dereferenced_pointers(expr_before_abst))
  {
    auto pointer = abstract_expr_read(
      pointer_old, abst_spec, goto_model, current_func, 
      insts_before, insts_after, new_symbs, insts_before_goto_target_map);
    // check if the pointer matched any abstracted array
    for(size_t spec_i=0; spec_i<abst_spec.get_specs().size(); spec_i++)
    {
      const auto &spec = abst_spec.get_specs()[spec_i];
      for(const auto &ent: spec.get_abst_pointers())
      {
        // get array$obj for this entity
        const irep_idt ent_pointer_obj_id = get_memory_addr_name(ent.first);
        const exprt ent_pointer_obj =
          goto_model.symbol_table.lookup_ref(ent_pointer_obj_id).symbol_expr();
        // since the target inst is not inserted yet, here we use an empty place holder
        goto_programt::targett empty_target;

        // if(pointer_object(pointer) != array$obj) GOTO endif$counter
        // guard: pointer_object(pointer) == ent$obj
        exprt guard = notequal_exprt(pointer_object(pointer), ent_pointer_obj);
        // insert the instruction, update goto_label_map
        goto_label_map.insert({insts_before.size(), "endif" + std::to_string(counter)});
        insts_before.push_back(goto_programt::make_goto(empty_target, guard));

        // the dead of the tmp function calls should be add right after this block, but not the entire thing
        goto_programt::instructionst fake_insts_after;

        // abst_index = abstract(pointer_offset(pointer))
        exprt::operandst operands_abstract{pointer_offset(pointer)};
        push_concrete_indices_to_operands(operands_abstract, spec, goto_model);
        auto abst_index_symb = create_function_call(
          spec.get_abstract_func(), operands_abstract, current_func,
          goto_model, insts_before, fake_insts_after, new_symbs);

        // is_prec_ret = is_precise(abst_index)
        exprt::operandst operands_is_prec{abst_index_symb.symbol_expr()};
        push_concrete_indices_to_operands(operands_is_prec, spec, goto_model);
        auto is_prec_ret_symb = create_function_call(
          spec.get_precise_func(), operands_is_prec, current_func,
          goto_model, insts_before, fake_insts_after, new_symbs);

        // is_prec = is_prec && is_prec_ret
        insts_before.push_back(goto_programt::make_assignment(
          is_prec_symb.symbol_expr(),
          and_exprt(
            is_prec_symb.symbol_expr(),
            typecast_exprt(is_prec_ret_symb.symbol_expr(), bool_typet()))));

        // counter_spec$x += 1
        insts_before.push_back(goto_programt::make_assignment(
          spec_access_counters[spec_i].symbol_expr(), 
          plus_exprt(spec_access_counters[spec_i].symbol_expr(), one_uint)));

        // the dead instructions
        insts_before.insert(insts_before.end(), fake_insts_after.begin(), fake_insts_after.end());

        // insert the goto end, update goto_label map
        goto_label_map.insert({insts_before.size(), "end"});
        insts_before.push_back(goto_programt::make_goto(empty_target));

        // endif$counter: SKIP
        label_target_map.insert({"endif" + std::to_string(counter), insts_before.size()});
        insts_before.push_back(goto_programt::make_skip());

        counter++;
      }
    }
  }

  // end label
  label_target_map.insert({"end", insts_before.size()});
  insts_before.push_back(goto_programt::make_skip());

  // for every spec$x: assert(1+number of length vars+counter_spec$x<=number of concrete index in spec$x)
  for(size_t i = 0; i < abst_spec.get_specs().size(); i++)
  {
    const auto &spec = abst_spec.get_specs()[i];
    insts_before.push_back(goto_programt::make_assertion(binary_relation_exprt(
      plus_exprt(
        spec_access_counters[i].symbol_expr(), 
        constant_exprt(
          integer2bvrep(1+spec.get_abst_lengths().size(), unsigned_int_type().get_width()), 
          unsigned_int_type())),
      ID_le,
      constant_exprt(
        integer2bvrep(spec.get_shape_indices().size(), unsigned_int_type().get_width()), 
        unsigned_int_type()))));
  }

  // before returning, update the goto target map
  for(auto &id_label: goto_label_map)
  {
    INVARIANT(
      label_target_map.find(id_label.second) != label_target_map.end(),
      "the label " + id_label.second + " is not defined");
    INVARIANT(
      insts_before_goto_target_map.find(id_label.first) ==
        insts_before_goto_target_map.end(),
      "instruction's target defined twice");
    insts_before_goto_target_map.insert({id_label.first, label_target_map[id_label.second]});
  }

  // return is_prec -> xxxxx
  implies_exprt final_expr(is_prec_symb.symbol_expr(), expr);
  return std::move(final_expr);

  // TODO: what should we do with the number of concrete indices invariant check?
  //       it should go dynamic
}

void rrat::declare_abst_variables(
  goto_modelt &goto_model,
  const std::unordered_set<irep_idt> &functions,
  const rra_spect &abst_spec)
{
  symbol_tablet &symbol_table = goto_model.symbol_table;
  std::unordered_set<irep_idt> abst_var_set;

  // helper function to insert abst variables into the symbol table
  auto insert_abst_symbol =
    [&symbol_table, &abst_var_set](const rra_spect::spect::entityt &entity) {
      // sometimes vars in built in functions has no identifers
      // we don't handle those cases by default
      if(symbol_table.has_symbol(entity.entity_name()))
      {
        // insert the symbol var_name$abst into the symbol table
        const symbolt &orig_symbol =
          symbol_table.lookup_ref(entity.entity_name());
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
            throw "abstract variable's name already occupied.";
        }
      }
    };

  // Step 1: insert abst variables into the symbol table
  for(const rra_spect::spect &spec : abst_spec.get_specs())
  {
    for(const auto &ent_pair : spec.get_top_level_abst_entities())
      insert_abst_symbol(ent_pair.second);
  }

  // Step 2: if it is in the function parameter list, change the name
  for(const auto &func_name : functions)
  {
    goto_functiont &function =
      goto_model.goto_functions.function_map.at(func_name);
    for(auto &param : function.parameter_identifiers)
      if(abst_spec.has_entity(param))
        param = std::string(param.c_str()) + "$abst";
    INVARIANT(
      goto_model.get_symbol_table().has_symbol(func_name),
      "The function " + std::string(func_name.c_str()) + " is not found");
    symbolt &function_symb =
      goto_model.symbol_table.get_writeable_ref(func_name);
    code_typet &function_type = to_code_type(function_symb.type);
    for(auto &param : function_type.parameters())
    {
      const irep_idt param_id = param.get_identifier();
      if(abst_spec.has_entity(param_id))
        param.set_identifier(get_abstract_name(param_id));
    }
  }

  // Note: we don't have to handle declare and dead here.
  // They'll be handled in the main run through the instructions.
}

void rrat::declare_abst_addrs(goto_modelt &goto_model, const rra_spect &abst_spec)
{
  for(const auto &spec: abst_spec.get_specs())
  {
    // entity: (name, entityt) pair
    for(const auto &entity: spec.get_abst_pointers())
    {
      pointer_typet typ = pointer_type(void_type());
      source_locationt src_loc;
      symbolt symb;
      symb.type = size_type();
      symb.location = src_loc;
      symb.name = get_memory_addr_name(entity.first);
      symb.mode = ID_C;
      symbol_exprt symb_expr = symb.symbol_expr();

      // Step 1: put it into the symbol table
      if(goto_model.symbol_table.has_symbol(symb.name))
        throw "the memory addr variable " + std::string(symb.name.c_str()) + " is already defined";
      goto_model.symbol_table.insert(std::move(symb));

      // Step 2: put it into __CPROVER_initialize which is the entry function for each goto program
      //         note that it should be at the beginning of the init function because it will need 
      //         to be updated in __CPROVER_initialize if the entity is a global variable
      goto_functionst::function_mapt::iterator fct_entry =
        goto_model.goto_functions.function_map.find(INITIALIZE_FUNCTION);
      CHECK_RETURN(fct_entry != goto_model.goto_functions.function_map.end());
      goto_programt &init_function = fct_entry->second.body;
      auto first_instruction = init_function.instructions.begin();
      const auto zero = zero_initializer(symb_expr.type(), source_locationt(), namespacet(goto_model.symbol_table));
      CHECK_RETURN(zero.has_value());
      goto_programt::instructiont new_inst = goto_programt::make_assignment(
        code_assignt(symb_expr, *zero));
      init_function.insert_before_swap(first_instruction, new_inst);
    }
  }
}

bool rrat::check_if_exprt_eval_to_abst_index(
  const exprt &expr,
  const rra_spect &abst_spec,
  rra_spect::spect &spec)
{
  if(expr.id() == ID_symbol || expr.id() == ID_member)
  {
    // if it is a symbol, check whether if it is in the entity list
    const irep_idt symb_id = get_string_id_from_exprt(expr);
    if(abst_spec.has_index_entity(symb_id))
    {
      spec = abst_spec.get_spec_for_index_entity(symb_id);
      return true;
    }
    else
    {
      return false;
    }
  }
  else if(
    expr.id() == ID_const_cast || expr.id() == ID_static_cast ||
    expr.id() == ID_typecast || expr.id() == ID_dynamic_cast ||
    expr.id() == ID_reinterpret_cast)
  {
    // if it is a cast, we check the lower level
    if(expr.operands().size() != 1)
      throw "cast expressions should have one operand";
    return check_if_exprt_eval_to_abst_index(
      *expr.operands().begin(), abst_spec, spec);
  }
  else if(expr.id() == ID_plus || expr.id() == ID_minus)
  {
    // if it is plus or minus, it should stay the same as the abstracted operand
    if(expr.operands().size() != 2)
      throw "add/minus expressions should have two operands";
    rra_spect::spect spec1, spec2;
    bool abs1 =
      check_if_exprt_eval_to_abst_index(expr.operands()[0], abst_spec, spec1);
    bool abs2 =
      check_if_exprt_eval_to_abst_index(expr.operands()[1], abst_spec, spec2);
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
      throw "direct computation on two abstracted indices are prohibited";
    }
  }
  else if(expr.id() == ID_pointer_offset || expr.id() == ID_object_size)
  {
    // if we are trying to get the offset of a pointer or
    // the size is a pointer, expr will be evaluated to abst index
    // if the pointer is an abst array
    INVARIANT(
      expr.operands().size() == 1,
      "pointer offset or object size exprs should only have one operand");
    const exprt &pointer = *expr.operands().begin();
    if(pointer.id() == ID_symbol)
    {
      if(abst_spec.has_array_entity(to_symbol_expr(pointer).get_identifier()))
      {
        // if the pointer is an abstracted array,
        // we should use the same spec of this array
        spec = abst_spec.get_spec_for_array_entity(
          to_symbol_expr(pointer).get_identifier());
        return true;
      }
      else if(abst_spec.has_const_c_str_entity(
                to_symbol_expr(pointer).get_identifier()))
      {
        // if the pointer is an abstracted array,
        // we should use the same spec of this array
        spec = abst_spec.get_spec_for_const_c_str_entity(
          to_symbol_expr(pointer).get_identifier());
        return true;
      }
      else
      {
        return false;
      }
    }
    else
    {
      const char *size_error =
        "size or offset checking on complex pointers"
        " are not supported in abstraction right now";
      throw size_error;
    }
  }
  else
  {
    return false;
  }
}

bool rrat::check_if_exprt_is_abst_index(
    const exprt &expr,
    const rra_spect &abst_spec, 
    rra_spect::spect &spec)
{
  if(expr.id() == ID_symbol || expr.id() == ID_member)
  {
    // if it is a symbol, check whether if it is in the entity list
    const irep_idt symb_id = get_string_id_from_exprt(expr);
    if(abst_spec.has_index_entity(symb_id))
    {
      spec = abst_spec.get_spec_for_index_entity(symb_id);
      return true;
    }
    else
    {
      return false;
    }
  }
  else
  {
    return false;
  }
}

bool rrat::check_if_exprt_is_abst_array(
    const exprt &expr,
    const rra_spect &abst_spec, 
    rra_spect::spect &spec)
{
  if(expr.id() == ID_symbol || expr.id() == ID_member)
  {
    // if it is a symbol, check whether if it is in the entity list
    const irep_idt symb_id = get_string_id_from_exprt(expr);
    if(
      abst_spec.has_array_entity(symb_id) ||
      abst_spec.has_const_c_str_entity(symb_id))
    {
      spec = abst_spec.get_spec_for_array_entity(symb_id);
      return true;
    }
    else
    {
      return false;
    }
  }
  else
  {
    return false;
  }
}

void rrat::push_concrete_indices_to_operands(
  exprt::operandst &operands,
  const rra_spect::spect &spec,
  const goto_modelt &goto_model)
{
  for(const auto &c_ind : spec.get_shape_indices())
  {
    if(!goto_model.get_symbol_table().has_symbol(c_ind))
      throw "concrete index symbol " + std::string(c_ind.c_str()) +
        " not found";
    const symbolt &c_ind_symb = goto_model.get_symbol_table().lookup_ref(c_ind);
    operands.push_back(c_ind_symb.symbol_expr());
  }
}

symbolt rrat::create_function_call(
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
  for(const auto &symb : new_symbs)
    new_symbs_name.insert(symb.name);

  auto get_name = [&caller, &func_name, &goto_model, &new_symbs_name]() {
    // base name is "{caller}::$tmp::return_value_{callee}"
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
    throw "unable to find function " + std::string(func_name.c_str()) +
      " in the symbol table";
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

symbolt rrat::create_temp_var_for_expr(
  const exprt &target_expr,
  const irep_idt &caller,
  const goto_modelt &goto_model,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs,
  bool cprover_prefix = false)
{
  // determine the temp symbol's name
  std::unordered_set<irep_idt> new_symbs_name;
  for(const auto &symb : new_symbs)
    new_symbs_name.insert(symb.name);

  auto get_name = [&caller, &goto_model, &new_symbs_name, &cprover_prefix]() {
    // base name is "{caller}::$tmp::return_value_{callee}"
    std::string base_name =
      std::string(caller.c_str()) + "::$tmp::$abst::temp_var_for_expr";
    if(cprover_prefix)
      base_name = CPROVER_PREFIX + base_name;
    
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
  new_symb.type = target_expr.type();
  new_symb.name = temp_symb_name;
  new_symb.mode = ID_C;
  symbol_exprt new_symb_expr = new_symb.symbol_expr();
  new_symbs.push_back(new_symb);

  // instruction 1: DECLARE of the temp symbol
  auto new_decl_inst = goto_programt::make_decl(code_declt(new_symb_expr));
  insts_before.push_back(new_decl_inst);

  // instruction 2: ASSIGNMENT
  auto new_assign_inst =
    goto_programt::make_assignment(code_assignt(new_symb_expr, target_expr));
  insts_before.push_back(new_assign_inst);

  // instruction 3: DEAD for the temp symbol
  auto new_dead_inst = goto_programt::make_dead(new_symb_expr);
  insts_after.push_back(new_dead_inst);

  return new_symb;
}

symbolt rrat::create_temp_var(
  const irep_idt &name, 
  const typet typ,
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

  auto get_name = [&caller, &goto_model, &new_symbs_name, &name]() {
    // base name is "{caller}::$tmp::return_value_{callee}"
    std::string base_name = std::string(caller.c_str()) +
                            "::$tmp::$abst::" + std::string(name.c_str());
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
  new_symb.type = typ;
  new_symb.name = temp_symb_name;
  new_symb.mode = ID_C;
  symbol_exprt new_symb_expr = new_symb.symbol_expr();
  new_symbs.push_back(new_symb);

  // instruction 1: DECLARE of the temp symbol
  auto new_decl_inst = goto_programt::make_decl(code_declt(new_symb_expr));
  insts_before.push_back(new_decl_inst);

  // instruction 2: DEAD for the temp symbol 
  auto new_dead_inst = goto_programt::make_dead(new_symb_expr);
  insts_after.push_back(new_dead_inst);

  return new_symb;
}

symbolt rrat::create_abstract_func_after(
  const exprt &real_lhs,
  const rra_spect::spect &spec,
  const irep_idt &caller,
  const goto_modelt &goto_model,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  // determine the temp lhs's name
  std::unordered_set<irep_idt> new_symbs_name;
  for(const auto &symb : new_symbs)
    new_symbs_name.insert(symb.name);

  const irep_idt &func_name = spec.get_abstract_func();
  auto get_name = [&caller, &func_name, &goto_model, &new_symbs_name]() {
    // base name is "{caller}::$tmp::before_{callee}"
    std::string base_name = std::string(caller.c_str()) + "::$tmp::before_" +
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
  symbolt temp_lhs_symb;
  temp_lhs_symb.type = real_lhs.type();
  temp_lhs_symb.name = temp_symb_name;
  temp_lhs_symb.mode = ID_C;
  symbol_exprt temp_lhs_expr = temp_lhs_symb.symbol_expr();
  new_symbs.push_back(temp_lhs_symb);

  // instruction 1: DECLARE of the temp symbol
  auto new_decl_inst = goto_programt::make_decl(code_declt(temp_lhs_expr));
  insts_before.push_back(new_decl_inst);

  // instruction 2: FUNCTION_CALL
  symbol_exprt func_call_expr =
    goto_model.get_symbol_table().lookup_ref(func_name).symbol_expr();
  exprt::operandst operands{temp_lhs_expr};
  push_concrete_indices_to_operands(operands, spec, goto_model);
  auto new_func_call_inst = goto_programt::make_function_call(
    code_function_callt(real_lhs, func_call_expr, operands));
  insts_after.push_back(new_func_call_inst);

  // instruction 3: DEAD for the temp symbol
  auto new_dead_inst = goto_programt::make_dead(temp_lhs_expr);
  insts_after.push_back(new_dead_inst);

  return temp_lhs_symb;
}

exprt rrat::abstract_expr_write(
  const exprt &expr,
  const rra_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs, 
  std::unordered_map<size_t, size_t> &insts_before_goto_target_map)
{
  rra_spect::spect spec;
  if(check_if_exprt_is_abst_index(expr, abst_spec, spec))
  {
    // replace symb with symb$abst
    // Find abstracted symbol for this expr
    INVARIANT(
      expr.id() == ID_symbol,
      "let's now just assume loop iterators can't be member of objects");
    const irep_idt symb_id = get_string_id_from_exprt(expr);
    const irep_idt new_symb_id = get_abstract_name(symb_id);
    INVARIANT(
      goto_model.symbol_table.has_symbol(new_symb_id),
      "Abst variable " + std::string(new_symb_id.c_str()) +
        " used before inserting to the symbol table");
    symbol_exprt new_symb_expr = goto_model.symbol_table.lookup_ref(new_symb_id).symbol_expr();
    return std::move(new_symb_expr);
  }
  else
  {
    // run abst_write on every operands
    exprt new_expr = expr;
    for(auto &op: new_expr.operands())
    {
      op = abstract_expr_write(
        op, abst_spec, goto_model, current_func, insts_before, 
        insts_after, new_symbs, insts_before_goto_target_map);
    }
    if(new_expr.id() == ID_dereference)
    {
      // In the previous step, we do:  
      // expr <deref(pointer)> =======> new_expr <deref(abst_read(pointer))> 
      // need to check if this is an abstracted array reference 
      // ============= instructions ============= 
      // declare result_pointer 
      // declare abst_index 
      // declare base_pointer
      // base_pointer = pointer - offset(pointer)
      // **for every array entity** 
      // if(pointer_object(pointer) == entity1$obj) GOTO 1; 
      // if(pointer_object(pointer) == entity2$obj) GOTO 2; 
      // ... 
      // GOTO deft; 
      // 1:    
      //      abst_index = abstract(offset(pointer)) 
      //      result_pointer = base_pointer + abst_index 
      //      GOTO end; 
      // ... 
      // deft: result_pointer = pointer
      // end: **inst containing this deref**: replace with deref(result_pointer) 
      // dead abst_index 
      // dead result_pointer 
      // =========================================
      const exprt &pointer = new_expr.operands()[0];
      
      // Declare and dead for result, abst_index, base_pointer
      symbolt result_pointer_symb = create_temp_var(
        "result_pointer", remove_const(pointer.type()), current_func, goto_model, 
        insts_before, insts_after, new_symbs);
      symbolt abst_index_symb = create_temp_var(
        "abst_index", size_type(), current_func, goto_model, 
        insts_before, insts_after, new_symbs);
      symbolt base_pointer_symb = create_temp_var(
        "base_pointer", remove_const(pointer.type()), current_func, goto_model, 
        insts_before, insts_after, new_symbs);

      // base_pointer = pointer - offset(pointer)
      insts_before.push_back(goto_programt::make_assignment(
        base_pointer_symb.symbol_expr(),
        minus_exprt(pointer, pointer_offset(pointer))));

      std::unordered_map<size_t, std::string> goto_label_map;  // goto's index in insts_before ==> labels: "0","1",..., "deft", "end"
      std::unordered_map<std::string, size_t> label_target_map;  // labels: "0"..."end" ==> target inst's index in insts_before
      
      // Go through each abst array and insert conditional goto
      size_t counter = 0;
      for(const auto &spec: abst_spec.get_specs())
      {
        for(const auto &ent: spec.get_abst_pointers())
        {
          // since the target inst is not inserted yet, here we use an empty place holder
          goto_programt::targett empty_target;
          // get the global pointer_obj var
          const irep_idt ent_pointer_obj_id = get_memory_addr_name(ent.first);
          const exprt ent_pointer_obj =
            goto_model.symbol_table.lookup_ref(ent_pointer_obj_id).symbol_expr();
          // guard: pointer_object(pointer) == ent$obj
          exprt guard = equal_exprt(pointer_object(pointer), ent_pointer_obj);
          // insert the instruction, update goto_label_map
          goto_label_map.insert({insts_before.size(), std::to_string(counter)});
          insts_before.push_back(goto_programt::make_goto(empty_target, guard));
          counter++;
        }
      }

      // If not matched to any, GOTO deft
      goto_programt::targett empty_target;
      goto_label_map.insert({insts_before.size(), "deft"});
      insts_before.push_back(goto_programt::make_goto(empty_target));

      // Go through each abst array, calculate abst_index and result 
      counter = 0;
      for(const auto &spec: abst_spec.get_specs())
      {
        for(size_t i=0; i<spec.get_abst_pointers().size(); i++)
        {
          // update label_target to label the starting point of this body
          label_target_map.insert({std::to_string(counter), insts_before.size()});

          // function call: abst_index = abstract(offset(pointer))
          exprt::operandst operands{pointer_offset(pointer)};
          push_concrete_indices_to_operands(operands, spec, goto_model);
          symbol_exprt func_call_expr =
            goto_model.get_symbol_table().lookup_ref(spec.get_abstract_func()).symbol_expr();
          auto new_func_call_inst = goto_programt::make_function_call(
            code_function_callt(abst_index_symb.symbol_expr(), func_call_expr, operands));
          insts_before.push_back(new_func_call_inst);

          // update result_pointer: result_pointer = base_pointer+abst_index
          insts_before.push_back(goto_programt::make_assignment(
            result_pointer_symb.symbol_expr(),
            plus_exprt(
              base_pointer_symb.symbol_expr(), abst_index_symb.symbol_expr())));

          // GOTO end, and update goto_label_map
          goto_label_map.insert({insts_before.size(), "end"});
          insts_before.push_back(goto_programt::make_goto(empty_target));

          counter++;
        }
      }

      // Calculate default result_pointer (deft: result_pointer = pointer)
      label_target_map.insert({"deft", insts_before.size()});
      insts_before.push_back(goto_programt::make_assignment(result_pointer_symb.symbol_expr(), pointer));

      // placeholder end label
      label_target_map.insert({"end", insts_before.size()});
      insts_before.push_back(goto_programt::make_skip());

      // before returning, update the goto target map
      for(auto &id_label: goto_label_map)
      {
        INVARIANT(
          label_target_map.find(id_label.second) != label_target_map.end(),
          "the label " + id_label.second + " is not defined");
        INVARIANT(
          insts_before_goto_target_map.find(id_label.first) ==
            insts_before_goto_target_map.end(),
          "instruction's target defined twice");
        insts_before_goto_target_map.insert({id_label.first, label_target_map[id_label.second]});
      }

      return std::move(dereference_exprt(result_pointer_symb.symbol_expr()));
    }
    else
    {
      // just return the original expr
      return new_expr;
    }
  }
}

exprt rrat::create_comparator_expr_abs_abs(
  const exprt &orig_expr,
  const rra_spect::spect &spec,
  const goto_modelt &goto_model,
  const irep_idt &caller,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  // create the function call is_abst(op0)
  irep_idt is_prec_func = spec.get_precise_func();
  exprt::operandst operands{orig_expr.operands()[0]};
  push_concrete_indices_to_operands(operands, spec, goto_model);
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

// check whether an expr is a pointer offset
bool rrat::is_pointer_offset(const exprt &expr)
{
  if(expr.id() == ID_pointer_offset)
  {
    return true;
  }
  else if(expr.id() == ID_typecast)
  {
    INVARIANT(expr.operands().size() == 1, "typecast should only have one operand");
    return is_pointer_offset(expr.operands()[0]);
  }
  else
  {
    return false;
  }
}

exprt rrat::abstract_expr_read(
  const exprt &expr,
  const rra_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs,
  std::unordered_map<size_t, size_t> &insts_before_goto_target_map)
{
  rra_spect::spect spec;
  if(check_if_exprt_is_abst_index(expr, abst_spec, spec))
  {
    // TODO: what if an entity is refered elsewhere????
    //       should do closure analysis
    // declare conc
    // conc = concrete(expr)
    // **inst containing this read**: replace with conc
    // dead conc
    
    // Find abstracted symbol for this expr
    INVARIANT(
      expr.id() == ID_symbol,
      "let's now just assume loop iterators can't be member of objects");
    const irep_idt symb_id = get_string_id_from_exprt(expr);
    const irep_idt new_symb_id = get_abstract_name(symb_id);
    INVARIANT(
      goto_model.symbol_table.has_symbol(new_symb_id),
      "Abst variable " + std::string(new_symb_id.c_str()) +
        " used before inserting to the symbol table");
    symbol_exprt new_symb_expr = goto_model.symbol_table.lookup_ref(new_symb_id).symbol_expr();

    const irep_idt conc_func = spec.get_concretize_func();
    exprt::operandst operands{new_symb_expr};
    // Put the concrete indices into operands
    push_concrete_indices_to_operands(operands, spec, goto_model);
    // Make the function call
    auto conc_symb = create_function_call(conc_func, operands, current_func, goto_model, insts_before, insts_after, new_symbs);
    return std::move(conc_symb.symbol_expr());
  }
  else
  {
    // run abst_read on every operands
    exprt new_expr = expr;
    for(auto &op: new_expr.operands())
    {
      op = abstract_expr_read(
        op, abst_spec, goto_model, current_func, insts_before,
        insts_after, new_symbs, insts_before_goto_target_map);
    }
    if(new_expr.id() == ID_dereference)
    {
      // In the previous step, we do:  
      // expr <deref(pointer)> =======> new_expr <deref(abst_read(pointer))> 
      // need to check if this is an abstracted array reference 
      // TO DISCUSS: should we put these instructions into a function?
      // ============= instructions ============= 
      // declare result 
      // declare abst_index 
      // declare base_pointer
      // base_pointer = pointer - offset(pointer)
      // **for every array entity** 
      // if(pointer_object(pointer) == entity1$obj) GOTO 1; 
      // if(pointer_object(pointer) == entity2$obj) GOTO 2; 
      // ... 
      // GOTO deft; 
      // 1:   abst_index = abstract(offset(pointer)) 
      //      result = is_precise(abst_index) ? deref(base_pointer(pointer) + abst_index) : nondet 
      //      GOTO end; 
      // ... 
      // deft: result = new_expr 
      // end: **inst containing this deref**: replace with result 
      // dead abst_index 
      // dead result 
      // =========================================
      const exprt &pointer = new_expr.operands()[0];
      
      // Declare and dead for result, abst_index, base_pointer
      symbolt result_symb = create_temp_var(
        "result", remove_const(new_expr.type()), current_func, goto_model, 
        insts_before, insts_after, new_symbs);
      symbolt abst_index_symb = create_temp_var(
        "abst_index", size_type(), current_func, goto_model, 
        insts_before, insts_after, new_symbs);
      symbolt base_pointer_symb = create_temp_var(
        "base_pointer", remove_const(pointer.type()), current_func, goto_model, 
        insts_before, insts_after, new_symbs);

      // base_pointer = pointer - offset(pointer)
      insts_before.push_back(goto_programt::make_assignment(
        base_pointer_symb.symbol_expr(),
        minus_exprt(pointer, pointer_offset(pointer))));

      std::unordered_map<size_t, std::string> goto_label_map;  // goto's index in insts_before ==> labels: "0","1",..., "deft", "end"
      std::unordered_map<std::string, size_t> label_target_map;  // labels: "0"..."end" ==> target inst's index in insts_before
      
      // Go through each abst array and insert conditional goto
      size_t counter = 0;
      for(const auto &spec: abst_spec.get_specs())
      {
        for(const auto &ent: spec.get_abst_pointers())
        {
          // since the target inst is not inserted yet, here we use an empty place holder
          goto_programt::targett empty_target;
          // get the global pointer_obj var
          const irep_idt ent_pointer_obj_id = get_memory_addr_name(ent.first);
          const exprt ent_pointer_obj =
            goto_model.symbol_table.lookup_ref(ent_pointer_obj_id).symbol_expr();
          // guard: pointer_object(pointer) == ent$obj
          exprt guard = equal_exprt(pointer_object(pointer), ent_pointer_obj);
          // insert the instruction, update goto_label_map
          goto_label_map.insert({insts_before.size(), std::to_string(counter)});
          insts_before.push_back(goto_programt::make_goto(empty_target, guard));
          counter++;
        }
      }

      // If not matched to any, GOTO deft
      goto_programt::targett empty_target;
      goto_label_map.insert({insts_before.size(), "deft"});
      insts_before.push_back(goto_programt::make_goto(empty_target));

      // Go through each abst array, calculate abst_index and result 
      counter = 0;
      for(const auto &spec: abst_spec.get_specs())
      {
        for(size_t i=0; i<spec.get_abst_pointers().size(); i++)
        {
          // update label_target to label the starting point of this body
          label_target_map.insert({std::to_string(counter), insts_before.size()});

          // function call: abst_index = abstract(offset(pointer))
          exprt::operandst operands{pointer_offset(pointer)};
          push_concrete_indices_to_operands(operands, spec, goto_model);
          symbol_exprt func_call_expr =
            goto_model.get_symbol_table().lookup_ref(spec.get_abstract_func()).symbol_expr();
          auto new_func_call_inst = goto_programt::make_function_call(
            code_function_callt(abst_index_symb.symbol_expr(), func_call_expr, operands));
          insts_before.push_back(new_func_call_inst);

          // update result: result = is_precise(abst_index) ? deref(base_pointer+abst_index) : nondet
          //        first call is_precise
          exprt::operandst operands_is_prec{abst_index_symb.symbol_expr()};
          push_concrete_indices_to_operands(operands_is_prec, spec, goto_model);
          //        the dead of the tmp function call should be add right after this block, but not the entire thing
          goto_programt::instructionst fake_insts_after;
          auto is_prec_ret = create_function_call(
            spec.get_precise_func(), operands_is_prec, current_func,
            goto_model, insts_before, fake_insts_after, new_symbs);
          //        then create the instruction
          exprt precise_val = dereference_exprt(plus_exprt(
            base_pointer_symb.symbol_expr(), abst_index_symb.symbol_expr()));
          exprt result_expr = if_exprt(
            typecast_exprt(is_prec_ret.symbol_expr(), bool_typet()),
            precise_val,
            side_effect_expr_nondett(new_expr.type(), source_locationt()));
          insts_before.push_back(goto_programt::make_assignment(result_symb.symbol_expr(), result_expr));
          //        the dead instructions for the is_prec call
          insts_before.insert(insts_before.end(), fake_insts_after.begin(), fake_insts_after.end());

          // GOTO end, and update goto_label_map
          goto_label_map.insert({insts_before.size(), "end"});
          insts_before.push_back(goto_programt::make_goto(empty_target));

          counter++;
        }
      }

      // Calculate default result (deft: result = new_expr)
      label_target_map.insert({"deft", insts_before.size()});
      insts_before.push_back(goto_programt::make_assignment(result_symb.symbol_expr(), new_expr));

      // placeholder end label
      label_target_map.insert({"end", insts_before.size()});
      insts_before.push_back(goto_programt::make_skip());

      // before returning, update the goto target map
      for(auto &id_label: goto_label_map)
      {
        INVARIANT(
          label_target_map.find(id_label.second) != label_target_map.end(),
          "the label " + id_label.second + " is not defined");
        INVARIANT(
          insts_before_goto_target_map.find(id_label.first) ==
            insts_before_goto_target_map.end(),
          "instruction's target defined twice");
        insts_before_goto_target_map.insert({id_label.first, label_target_map[id_label.second]});
      }

      return result_symb.symbol_expr();
    }
    else
    {
      return new_expr;
    }
  }
}

void rrat::define_concrete_indices(
  goto_modelt &goto_model,
  const rra_spect &abst_spec)
{
  for(const auto &spec : abst_spec.get_specs())
  {
    for(const irep_idt &index : spec.get_shape_indices())
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
        throw "the concrete index variable " + std::string(index.c_str()) +
          " is already defined";
      goto_model.symbol_table.insert(std::move(symb));

      // Step 2: put it into __CPROVER_initialize
      // which is the entry function for each goto program
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

void rrat::define_const_c_str_lengths(
  goto_modelt &goto_model,
  const rra_spect &abst_spec)
{
  for(const auto &spec : abst_spec.get_specs())
  {
    for(auto &c_str_len_pair : spec.get_abst_const_c_strs())
    {
      irep_idt var_name = get_const_c_str_len_name(c_str_len_pair.first);

      unsignedbv_typet index_type = unsigned_long_int_type();
      source_locationt src_loc;
      symbolt symb;
      symb.type = index_type;
      symb.location = src_loc;
      symb.name = var_name;
      symb.mode = ID_C;
      symbol_exprt symb_expr = symb.symbol_expr();

      // Step 1: put it into the symbol table
      if(goto_model.symbol_table.has_symbol(var_name))
        throw "the c_str len variable " + std::string(var_name.c_str()) +
          " is already defined";
      goto_model.symbol_table.insert(std::move(symb));

      // Step 2: put it into __CPROVER_initialize
      // which is the entry function for each goto program
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

      // Step 3: run is_precise on the '\0' location variable
      goto_programt::instructionst insts_before, insts_after;
      std::vector<symbolt> new_symbs;
      exprt::operandst operands{symb_expr};
      // put the concrete indices into operands
      push_concrete_indices_to_operands(operands, spec, goto_model);
      auto is_prec_ret = create_function_call(
        spec.get_precise_func(),
        operands,
        INITIALIZE_FUNCTION,
        goto_model,
        insts_before,
        insts_after,
        new_symbs);
      for(auto &inst : insts_before)
      {
        last_instruction = std::prev(init_function.instructions.end());
        DATA_INVARIANT(
          last_instruction->is_end_function(),
          "last instruction in function should be END_FUNCTION");
        init_function.insert_before_swap(last_instruction, inst);
      }
      for(auto &new_symb : new_symbs)
      {
        INVARIANT(
          !goto_model.symbol_table.has_symbol(new_symb.name),
          "the c_str len variable " + std::string(new_symb.name.c_str()) +
            " is already defined");
        goto_model.symbol_table.insert(std::move(new_symb));
      }

      // Step 4: add assumption saying it must be precise
      typecast_exprt assumption_expr(is_prec_ret.symbol_expr(), bool_typet());
      auto new_assumption = goto_programt::make_assumption(assumption_expr);
      last_instruction = std::prev(init_function.instructions.end());
      DATA_INVARIANT(
        last_instruction->is_end_function(),
        "last instruction in function should be END_FUNCTION");
      init_function.insert_before_swap(last_instruction, new_assumption);

      // Step 5: insert the instructions introduced by the create function call
      for(auto &inst : insts_after)
      {
        last_instruction = std::prev(init_function.instructions.end());
        DATA_INVARIANT(
          last_instruction->is_end_function(),
          "last instruction in function should be END_FUNCTION");
        init_function.insert_before_swap(last_instruction, inst);
      }
    }
  }
}

void rrat::insert_shape_assumptions(
  goto_modelt &goto_model,
  const rra_spect &abst_spec)
{
  namespacet ns(goto_model.get_symbol_table());
  for(const auto &spec : abst_spec.get_specs())
  {
    for(const exprt &expr : spec.get_assumption_exprs(ns))
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

      goto_programt::instructiont new_inst =
        goto_programt::make_assumption(expr);
      init_function.insert_before_swap(last_instruction, new_inst);
    }
  }
}

void rrat::add_length_assumptions(
  goto_modelt &goto_model,
  const rra_spect &abst_spec)
{
  const namespacet ns(goto_model.get_symbol_table());
  for(const auto &spec : abst_spec.get_specs())
  {
    for(const auto &lp : spec.get_abst_lengths_with_expr(ns))
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
        if(it->is_decl() || it->is_assign())
        {
          irep_idt var_name;
          if(it->is_decl())
          {
            const code_declt &decl = it->get_decl();
            var_name = decl.get_identifier();
          }
          else if(it->is_assign())
          {
            const code_assignt &assn = it->get_assign();
            if(is_entity_expr(assn.lhs()))
              var_name = get_string_id_from_exprt(assn.lhs());
            else
              continue;
          }
          else
          {
            continue;
          }

          // check if this declares the symbol containing the length
          // note that this symbol can be the length variable itself
          // or a struct containing the length variable
          if(var_name == lp.first)
          {
            // need to add an assumption after this inst
            INVARIANT(
              goto_model.get_symbol_table().has_symbol(var_name),
              "Symbol " + std::string(var_name.c_str()) + " not defined");

            if(it->is_decl())
              is_local = true;

            // define the assumption instruction
            const exprt length_expr = lp.second;
            exprt::operandst assumption_exprs;
            for(const auto &conc : spec.get_shape_indices())
            {
              INVARIANT(
                goto_model.get_symbol_table().has_symbol(conc),
                "Symbol " + std::string(spec.get_length_index_name().c_str()) +
                  " not defined");
              const symbolt conc_index_expr =
                goto_model.get_symbol_table().lookup_ref(conc);
              assumption_exprs.push_back(
                equal_exprt(length_expr, conc_index_expr.symbol_expr()));
            }

            // the value of the length variable should be
            // one of the concrete indices
            or_exprt assumption_expr(assumption_exprs);
            auto new_assumption =
              goto_programt::make_assumption(assumption_expr);

            // insert it
            function.body.insert_after(it, new_assumption);
            std::cout << "Added length assumption after the decl/assign: ";
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
          "Symbol " + std::string(lp.first.c_str()) + " not defined");
        INVARIANT(
          goto_model.get_symbol_table().has_symbol(
            spec.get_length_index_name()),
          "Symbol " + std::string(spec.get_length_index_name().c_str()) +
            " not defined");
        // define the assumption instruction
        const exprt length_expr = lp.second;
        exprt::operandst assumption_exprs;
        for(const auto &conc : spec.get_shape_indices())
        {
          INVARIANT(
            goto_model.get_symbol_table().has_symbol(conc),
            "Symbol " + std::string(spec.get_length_index_name().c_str()) +
              " not defined");
          const symbolt conc_index_expr =
            goto_model.get_symbol_table().lookup_ref(conc);
          assumption_exprs.push_back(
            equal_exprt(length_expr, conc_index_expr.symbol_expr()));
        }

        // the value of the length variable should be
        // one of the concrete indices
        or_exprt assumption_expr(assumption_exprs);
        auto new_assumption = goto_programt::make_assumption(assumption_expr);

        // insert it
        std::cout
          << "Added length assumption in the beginning of the function: ";
        format_rec(std::cout, assumption_expr) << std::endl;
        init_function.insert_before_swap(last_instruction, new_assumption);
      }
    }
  }
}

void rrat::update_pointer_obj(
  const exprt &lhs,
  goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &inst_after,
  std::vector<symbolt> &new_symbs)
{
  // in this case, this instruction is writing to an abstracted array itself
  // we need to update the global variable to keep track of the pointer_object
  // lhs = malloc()
  // lhs$obj = pointer_object(lhs) <==== this function insert this inst
  // we will disable primitive check for the instruction we inserted because 
  // it will fail when we malloc a size 0 pointer which is a FP.

  // First, we need to get the global object variable exprt (obj_var)
  const irep_idt symb_id = get_string_id_from_exprt(lhs);
  const irep_idt obj_var_id = get_memory_addr_name(symb_id);
  const exprt obj_var =
    goto_model.symbol_table.lookup_ref(obj_var_id).symbol_expr();

  // Create an instruction "C_PROVER_pointer = lhs". This is to bypass the pointer primitive check.
  goto_programt::instructionst fake_insts_before;
  goto_programt::instructionst fake_insts_after;
  symbolt lhs_with_prefix = create_temp_var_for_expr(
    lhs, current_func, goto_model, fake_insts_before, fake_insts_after, new_symbs, true);
  inst_after.insert(inst_after.end(), fake_insts_before.begin(), fake_insts_before.end());

  // Next, find the pointer object of the current lhs
  exprt pointer_obj = pointer_object(lhs_with_prefix.symbol_expr());

  // Create an instruction "obj_var := pointer_object(lhs)"
  goto_programt::instructiont new_inst =
    goto_programt::make_assignment(code_assignt(obj_var, pointer_obj));

  // Insert the instruction
  inst_after.push_back(new_inst);

  inst_after.insert(inst_after.end(), fake_insts_after.begin(), fake_insts_after.end());
}

void rrat::analyze_soundness(
    goto_modelt &goto_model,
    std::unordered_set<irep_idt> &all_funcs,
    const rra_spect &abst_spec)
{
  auto &goto_functions = goto_model.goto_functions;

  for (const auto &func_name: all_funcs) {
    auto goto_func = goto_functions.function_map.find(func_name);
    natural_loops_mutablet natural_loops(goto_func->second.body);
    local_may_aliast local_may_alias(goto_func->second);
    
    for (const auto &loop: natural_loops.loop_map) {
      modifiest modifies;
      get_modifies(local_may_alias, loop.second, modifies);
      std::cout << "!!!!!!loop found in " 
                << func_name
                << " size: "
                << loop.second.size() 
                << std::endl;
      for (const auto &exp: modifies) {
        format_rec(std::cout, exp);
      }
    }
  }
}

void rrat::abstract_goto_program(goto_modelt &goto_model, rra_spect &abst_spec)
{
  // A couple of spects are initialized from the json file.
  // We should go from there and insert spects to other functions
  std::unordered_set<irep_idt> all_funcs =
    get_all_functions(goto_model);

  // Analyze soundness of abstraction
  analyze_soundness(goto_model, all_funcs, abst_spec);
  
  // Define the global concrete indices to be used
  define_concrete_indices(goto_model, abst_spec);

  // Insert the assumptions about concrete indices
  insert_shape_assumptions(goto_model, abst_spec);

  // Define the const c_string length symbols
  define_const_c_str_lengths(goto_model, abst_spec);

  // Add the assumption for len==$clen
  add_length_assumptions(goto_model, abst_spec);

  // Put the abstracted variables into the symbol table
  // Change the function parameter's name if needed
  declare_abst_variables(goto_model, all_funcs, abst_spec);

  // Declare the variables to store memory addresses
  declare_abst_addrs(goto_model, abst_spec);
  
  // Probably also need to do translation from concrete to abstract somewhere

  std::cout << "=========== " 
            << "Entities to be abstracted/length entities" 
            << " ===========" 
            << std::endl;
  abst_spec.print_entities();
  for(auto &func_name : all_funcs)
  {
    std::cout << "=========== " << func_name.c_str() << " ==========="
              << "\n";
    std::cout << "----------- "
              << "Exprs containing the above entities"
              << " -----------"
              << "\n";
    goto_functiont &goto_function =
      goto_model.goto_functions.function_map.at(func_name);
    Forall_goto_program_instructions(it, goto_function.body)
    {
      // go through all expressions
      goto_programt::instructionst inst_before;
      goto_programt::instructionst inst_after;
      std::vector<symbolt> new_symbs;
      std::unordered_map<size_t, size_t> insts_before_goto_target_map;

      // need to backup the expr for assertion
      exprt assert_orig_expr;
      if(it->is_assert())
        assert_orig_expr = it->get_condition();

      // go through conditions
      if(it->has_condition())
      {
        format_rec(std::cout, it->get_condition()) << " ==abst_read==> ";
        exprt new_condition = abstract_expr_read(
          it->get_condition(), abst_spec, goto_model, func_name, 
          inst_before, inst_after, new_symbs, insts_before_goto_target_map);
        format_rec(std::cout, new_condition) << std::endl;
        it->set_condition(new_condition);
      }

      if(it->is_function_call())
      {
        const code_function_callt fc = it->get_function_call();
        exprt new_lhs;
        format_rec(std::cout, fc.lhs()) << " ==abst_write==> ";
        new_lhs = abstract_expr_write(
          fc.lhs(), abst_spec, goto_model, func_name, 
          inst_before, inst_after, new_symbs, insts_before_goto_target_map);
        format_rec(std::cout, new_lhs) << std::endl;

        code_function_callt::argumentst new_arguments;
        for(const auto &arg : fc.arguments())
        {
          exprt new_arg;
          format_rec(std::cout, arg) << " ==abst_read==> ";
          new_arg = abstract_expr_read(
            arg, abst_spec, goto_model, func_name, 
            inst_before, inst_after, new_symbs, insts_before_goto_target_map);
          format_rec(std::cout, new_arg) << std::endl;
          new_arguments.push_back(new_arg);
        }

        rra_spect::spect lhs_spec;
        bool abs_lhs =
          check_if_exprt_is_abst_index(fc.lhs(), abst_spec, lhs_spec);
        if(abs_lhs)
        {
          // in this case, we need to abstract the return value
          // lhs = func()
          // =========>
          // temp_lhs = func()
          // lhs = abstract(temp_lhs)
          symbolt tmp_lhs = create_abstract_func_after(
            new_lhs,
            lhs_spec,
            func_name,
            goto_model,
            inst_before,
            inst_after,
            new_symbs);
          code_function_callt new_fc(
            tmp_lhs.symbol_expr(), fc.function(), new_arguments);
          it->set_function_call(new_fc);
        }
        else
        {
          code_function_callt new_fc(new_lhs, fc.function(), new_arguments);
          it->set_function_call(new_fc);
        }

        // need to update memobj/memaddr if lhs is an abstracted array
        // Assumption: each array entity var will only be assigned once in execution
        //             though syntacticly it might happen multiple times in code
        // array_a = malloc()
        if(check_if_exprt_is_abst_array(fc.lhs(), abst_spec, lhs_spec))
          update_pointer_obj(fc.lhs(), goto_model, func_name, inst_after, new_symbs);

      }
      else if(it->is_assign())
      {
        const code_assignt as = it->get_assign();
        exprt new_lhs;
        format_rec(std::cout, as.lhs()) << " ==abst_write==> ";
        new_lhs = abstract_expr_write(
          as.lhs(), abst_spec, goto_model, func_name, 
          inst_before, inst_after, new_symbs, insts_before_goto_target_map);
        format_rec(std::cout, new_lhs) << std::endl;

        exprt new_rhs;
        format_rec(std::cout, as.rhs()) << " ==abst_read==> ";
        new_rhs = abstract_expr_read(
          as.rhs(), abst_spec, goto_model, func_name, 
          inst_before, inst_after, new_symbs, insts_before_goto_target_map);
        format_rec(std::cout, new_rhs) << std::endl;

        // When lhs and rhs are not both abstracted, we should
        // do the translation.
        rra_spect::spect lhs_spec;
        bool lhs_abs =
          check_if_exprt_eval_to_abst_index(as.lhs(), abst_spec, lhs_spec);
        if(lhs_abs)
        {
          // lhs=rhs ===> lhs$abst = abstract(rhs)
          const irep_idt abst_func = lhs_spec.get_abstract_func();
          exprt::operandst operands{new_rhs};
          // put the concrete indices into operands
          push_concrete_indices_to_operands(operands, lhs_spec, goto_model);
          // make the function call
          auto new_rhs_symb = create_function_call(
            abst_func,
            operands,
            func_name,
            goto_model,
            inst_before,
            inst_after,
            new_symbs);
          new_rhs = new_rhs_symb.symbol_expr();
        }
        else
        {
        } // don't need to do anything

        code_assignt new_as(new_lhs, new_rhs);
        it->set_assign(new_as);

        // need to update memobj/memaddr if lhs is an abstracted array
        if(check_if_exprt_is_abst_array(as.lhs(), abst_spec, lhs_spec))
          update_pointer_obj(as.lhs(), goto_model, func_name, inst_after, new_symbs);
      }
      else if(it->is_return())
      {
        // Function will always return concrete value.
        // We need to convert them into abstract
        // values in the caller if needed.
        const code_returnt re = it->get_return();
        if(re.has_return_value())
        {
          const exprt &re_val = re.return_value();
          exprt new_re_val;
          format_rec(std::cout, re_val) << " ==abst_read==> ";
          new_re_val = abstract_expr_read(
            re_val, abst_spec, goto_model, func_name, 
            inst_before, inst_after, new_symbs, insts_before_goto_target_map);
          format_rec(std::cout, new_re_val) << std::endl;
          code_returnt new_re(new_re_val);
          it->set_return(new_re);
        }
      }
      else if(it->is_assert())
      {
        // if this is assertion, we should make the condition optimistic
        format_rec(std::cout, it->get_condition()) << " ==optimistic==> ";
        exprt optim_cond = add_guard_expression_to_assert(
          it->get_condition(),
          assert_orig_expr,
          abst_spec,
          goto_model,
          func_name,
          inst_before,
          inst_after,
          new_symbs, 
          insts_before_goto_target_map);
        format_rec(std::cout, optim_cond) << std::endl;
        it->set_condition(optim_cond);
      }
      if(it->is_decl())
      {
        // change symbol name in DECLARE instruction
        const code_declt &decl = it->get_decl();
        const symbol_tablet &symbol_table = goto_model.get_symbol_table();
        if(abst_spec.has_index_entity(decl.get_identifier()))
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
        const symbol_tablet &symbol_table = goto_model.get_symbol_table();
        if(abst_spec.has_index_entity(dead.get_identifier()))
        {
          irep_idt new_name = get_abstract_name(dead.get_identifier());
          typet typ = symbol_table.lookup_ref(new_name).type;
          symbol_exprt new_symb_expr(new_name, typ);
          code_deadt new_dead(new_symb_expr);
          it->set_dead(new_dead);
        }
      }

      // is there any unknown inst types?
      if(
        !it->is_decl() && !it->is_end_function() && !it->is_goto() &&
        !it->is_return() && !it->is_function_call() && !it->is_assert() &&
        !it->is_assign() && !it->is_assume() && !it->is_dead() &&
        !it->is_skip() && !it->is_other())
        throw "unknown instruction type " + std::to_string(it->type);

      // the iterator for every inserted inst before it
      std::vector<goto_programt::instructiont::targett> insts_before_its;

      auto orig_it = it;
      // insert new instructions before it
      for(auto &inst : inst_before)
      {
        goto_function.body.insert_before_swap(it, inst);
        it++;
      }
      // get the iterators for each inserted instruction
      for(; orig_it != it; orig_it++)
        insts_before_its.push_back(orig_it);
      INVARIANT(
        insts_before_its.size() == inst_before.size(), 
        "size of insts_before_its and inst_before should match");
      // set up targets for all GOTO instructions
      for(size_t i=0; i<inst_before.size(); i++)
      {
        if(insts_before_goto_target_map.find(i) != insts_before_goto_target_map.end())
        {
          auto &curr_it = insts_before_its[i];
          // this should be a GOTO instruction with out the target being specified
          INVARIANT(curr_it->is_goto(), "Only GOTO instruction can have a target mapping");
          // update the target with the target map
          curr_it->set_target(insts_before_its[insts_before_goto_target_map[i]]);
        }
      }

      // insert new instructions after it
      for(auto &inst : inst_after)
      {
        goto_function.body.insert_after(it, inst);
        it++;
      }

      // insert new symbols to the symbol table
      for(auto &symb : new_symbs)
      {
        if(goto_model.get_symbol_table().has_symbol(symb.name))
          throw "the temp symbol " + std::string(symb.name.c_str()) +
            " is already defined";
        goto_model.symbol_table.insert(symb);
      }
    }
  }
}
