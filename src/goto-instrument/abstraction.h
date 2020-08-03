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
  std::vector<std::vector<size_t>> edges_array;
  std::vector<exprt> expr_list;
  std::unordered_set<size_t> finished;
  std::unordered_set<size_t> finished_array;
  std::unordered_set<size_t> todo;
  std::unordered_set<size_t> todo_array;
  std::map<irep_idt, std::vector<size_t>> symbols;
  std::unordered_set<irep_idt> abst_variables;
  std::unordered_set<irep_idt> abst_arrays;

public:
  expr_type_relation(irep_idt _target_array) : target_array(_target_array)
  {
  }
  void link(size_t i1, size_t i2);
  void link_array(size_t i1, size_t i2);
  size_t add_expr(const exprt &expr);
  void solve();
  void solve_array();
  const std::unordered_set<irep_idt> get_abst_variables()
  {
    return abst_variables;
  }
  const std::unordered_set<irep_idt> get_abst_arrays()
  {
    return abst_arrays;
  }
};

// link abst functions to goto programs
void link_abst_functions(goto_modelt &goto_model, const abstraction_spect &abst_spec, ui_message_handlert &msg_handler, const optionst &options);

/// \param goto_function: the function to be analyzed
/// \param array_name: the array to be analyzed
/// \return the related variables within function. the first entry in the tuple is the set of related arrays
/// the second entry is the set of related indices
const std::tuple<std::unordered_set<irep_idt>, std::unordered_set<irep_idt>>
find_index_symbols(
  const goto_functiont &goto_function,
  const irep_idt &array_name);

/// \param goto_model: the goto model
/// \param abst_spec: the initialized abst_spec, containing all spects from the json file
/// \return a map with function name as key and its abst_spect as value
/// The function starts from the initial spects and check all function calls to build a complete set of entityts.
/// The new entityts are stored in abst_spec.specs
std::unordered_map<irep_idt, abstraction_spect>
calculate_complete_abst_specs_for_funcs(goto_modelt &goto_model, abstraction_spect &abst_spec);

/// \param expr: the expression to be checked
/// \param abst_spec: the abstraction_spect for the current function which contains all spects
/// \return whether the expr contains an entity to be abstracted
bool contains_an_abstracted_entity(const exprt &expr, const abstraction_spect &abst_spec);

/// \param goto_model: the goto model
/// \param func_name: the target function
/// \param abst_spec: the abstraction specification
/// The function helps declare the abstract variables in the abst_spec
/// For each variable "var_name", the function inserts the abstracted version
/// into the symbol table with name "var_name$abst"
/// If it is a local variable in the function, we'll also change the declaration for the abstracted variable to "var_name$abst"
/// If it is a function argument, we'll change the parameter table (var_name => var_name$abst)
void declare_abst_variables_for_func(
  goto_modelt &goto_model,
  const irep_idt &func_name,
  const abstraction_spect &abst_spec,
  std::unordered_set<irep_idt> &abst_var_set);

/// \param expr: the expression to be checked
/// \param abst_spec: the abstraction specification
/// \param index: if this exprt is abstract, 
/// \return whether it is abstract, the spec will be put here
bool check_if_exprt_is_abstract(
  const exprt &expr,
  const abstraction_spect &abst_spec,
  abstraction_spect::spect &spec);

/// \param expr: the lhs expression to be written to
/// \param abst_spec: the abstration information for the current function
/// \param goto_model: the goto_model
/// \param insts_before: instructions that need to be added before the instruction to support the write
/// \param insts_after: instructions that need to be added after the instruction to support the write
/// \param new_symbs: new symbols to be added to support the write
/// \return an exprt that is abstracted
exprt abstract_expr_write(
  const exprt &expr,
  const abstraction_spect &abst_spec,
  const goto_modelt &goto_model,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs);

/// \param expr: the expression to be read 
/// \param abst_spec: the abstration information for the current function
/// \param goto_model: the goto_model
/// \param insts_before: instructions that need to be added before the instruction to support the read
/// \param insts_after: instructions that need to be added after the instruction to support the read
/// \param new_symbs: new symbols to be added to support the read
/// \return an exprt that is abstracted
exprt abstract_expr_read(
  const exprt &expr,
  const abstraction_spect &abst_spec,
  const goto_modelt &goto_model,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs);

// abstract goto programs
void abstract_goto_program(goto_modelt &goto_model, abstraction_spect &abst_spec);

#endif // CPROVER_GOTO_INSTRUMENT_ABSTRACTION_H
