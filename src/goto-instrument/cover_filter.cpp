/*******************************************************************\

Module: Coverage Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Filters for the Coverage Instrumentation

#include "cover_filter.h"

#include <util/prefix.h>
#include <util/symbol.h>

#include <linking/static_lifetime_init.h>

/// Filter out functions that are not considered provided by the user
/// \param function: the function under consideration
/// \param goto_function: a goto function
/// \return returns true if function is considered user-provided
bool internal_functions_filtert::operator()(
  const symbolt &function,
  const goto_functionst::goto_functiont &goto_function) const
{
  if(function.name == goto_functionst::entry_point())
    return false;

  if(function.name == INITIALIZE_FUNCTION)
    return false;

  if(goto_function.is_hidden())
    return false;

  // ignore Java built-ins (synthetic functions)
  if(has_prefix(id2string(function.name), "java::array["))
    return false;

  // ignore if built-in library
  if(
    !goto_function.body.instructions.empty() &&
    goto_function.body.instructions.front().source_location.is_built_in())
    return false;

  return true;
}

/// Filter out all functions except those defined in the file that is given
/// in the constructor.
/// \param function: the function under consideration
/// \param goto_function: a goto function
/// \return returns true if `function` is defined in the file
/// given in the constructor
bool file_filtert::operator()(
  const symbolt &function,
  const goto_functionst::goto_functiont &goto_function) const
{
  (void)goto_function; // unused parameter
  return function.location.get_file() == file_id;
}

/// Filter out all functions except for one particular function given
/// in the constructor.
/// \param function: the function under consideration
/// \param goto_function: a goto function
/// \return returns true if `function` is different from the
/// function given in the constructor
bool single_function_filtert::operator()(
  const symbolt &function,
  const goto_functionst::goto_functiont &goto_function) const
{
  (void)goto_function; // unused parameter
  return function.name == function_id;
}

/// Filter functions whose name matches the regex
/// \param function: the function under consideration
/// \param goto_function: a goto function
/// \return returns true if the function name matches
bool include_pattern_filtert::operator()(
  const symbolt &function,
  const goto_functionst::goto_functiont &goto_function) const
{
  (void)goto_function; // unused parameter
  std::smatch string_matcher;
  return std::regex_match(
    id2string(function.name), string_matcher, regex_matcher);
}

/// Call a goto_program non-trivial if it has:
///  * Any declarations
///  * At least 2 branches
///  * At least 5 assignments
/// These criteria are arbitrarily chosen.
/// \param function: function symbol for function corresponding
/// to \p goto_function
/// \param goto_function: a goto function
/// \return returns true if non-trivial
bool trivial_functions_filtert::operator()(
  const symbolt &function,
  const goto_functionst::goto_functiont &goto_function) const
{
  (void)function; // unused parameter
  unsigned long count_assignments = 0, count_goto = 0;
  for(const auto &instruction : goto_function.body.instructions)
  {
    if(instruction.is_goto())
    {
      if((++count_goto) >= 2)
        return true;
    }
    else if(instruction.is_assign())
    {
      if((++count_assignments) >= 5)
        return true;
    }
    else if(instruction.is_decl())
      return true;
  }

  return false;
}

/// Filter goals at source locations considered internal
/// \param source_location: source location of the current goal
/// \return true : if the given source location is not considered internal
bool internal_goals_filtert::
operator()(const source_locationt &source_location) const
{
  if(source_location.get_file().empty())
    return false;

  if(source_location.is_built_in())
    return false;

  return true;
}
