/*******************************************************************\

Module:

Authors: Murali Talupur, talupur@amazon.com
         Lefan Zhang,    lefanz@amazon.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_ABSTSPEC_H
#define CPROVER_GOTO_INSTRUMENT_ABSTSPEC_H

#include <limits>
#include <list>
#include <map>
#include <string>
#include <tuple>
#include <vector>

class abstraction_spect
{
public:
  //This constructor parses the json abstraction specification and populates the class.
  abstraction_spect(std::string, message_handlert &);

  //gathers file names from all the individual specs and returns a list.
  std::vector<std::string> get_abstraction_function_files() const;

public:
  struct spect
  {
  public:
    struct entityt
    {
      //Hierarchical path to the array/list being abstracted
      std::string function; // function name, no need to have path
      //Name of the array/list being abstracted
      std::string name; // should be in the id format: function::x::name, this is the unique identifier
      std::string name_of_abst;

    public:
      entityt(){}
      entityt(std::string _function, std::string _name) : function(_function), name(_name) {}
      entityt(const entityt &_entity) : function(_entity.function), name(_entity.name), name_of_abst(_entity.name_of_abst) {}

      std::string function_name() const
      {
        return function;
      }

      void set_function_name(const std::string &new_func_name)
      {
        function = new_func_name;
      }

      std::string entity_name() const
      {
        return name;
      }

      void set_entity_name(const std::string &new_name)
      {
        name = new_name;
      }

      std::string entity_abst() const
      {
        return name_of_abst;
      }

      std::string entity_path()
      {
        return ("foo");
      };
    };

  protected:
    //Abstraction func file
    std::string abst_func_file;

    //Arrays to be abstracted
    std::unordered_map<std::string, entityt> abst_arrays;
    // std::vector<entityt> abst_arrays;

    //Index vars to be abstracted
    std::unordered_map<std::string, entityt> abst_indices;
    // std::vector<entityt> abst_indices;

    //Names of references in increasing order
    //Each ref is stored with path+name of the array being abstracted along
    //with the name of ref itself (like c1, c2)
    std::vector<entityt> refs_name;

    //Assumptions on the references
    std::vector<exprt> assumptions;

    //List of variables directly indexing into array being abstracted.
    //This list is required to handle while-loops correctly. Say ind indexes into array f
    //and ind is used as iterator in the while loop. Then ind has to be abstracted ind-abs
    //so as to reduce it's range from an potentially large value to a small abstract range.
    std::vector<std::string> indices;

    //Abstraction functions follow. These should be defined in the abstraction_funcs_file or
    //they are hard-coded ones. In abstraction_funcs_file function will begin with prefixes
    //such as is_precise, compare_indices,... followed by the some shape identifier.

    //Says if an index into the abstracted entity is precisely tracked or not.
    std::string is_precise_func;
    //Says how the two indices into abstracted entity compare.
    std::string compare_indices_func;
    //Addition over abstract indices
    std::string addition_func;
    //Subtraction over abstract indices
    std::string minus_func;

  public:
    spect() {}
    spect(const spect &_spec)
      : abst_func_file(_spec.abst_func_file),
        abst_arrays(_spec.abst_arrays),
        abst_indices(_spec.abst_indices),
        refs_name(_spec.refs_name),
        assumptions(_spec.assumptions),
        indices(_spec.indices),
        is_precise_func(_spec.is_precise_func),
        compare_indices_func(_spec.compare_indices_func),
        addition_func(_spec.addition_func),
        minus_func(_spec.minus_func)
    {
    }

    //We will have functions for accessing and modifying the above data.
    //array_or_index: false-array, true-index
    void insert_entity(const std::string &_function, const std::string &_name, bool array_or_index)
    {
      entityt new_entity(_function, _name);
      if(array_or_index)
        abst_arrays.insert({_name, new_entity});
      else
        abst_indices.insert({_name, new_entity});
    }

    const std::unordered_map<std::string, entityt> &get_abst_arrays() const
    {
      return abst_arrays;
    }

    //set abst func file path
    void set_abst_func_file(const std::string &_abst_func_file)
    {
      abst_func_file = _abst_func_file;
    }

    //get abst func file
    std::string get_abst_func_file() const
    {
      return abst_func_file;
    }

    //We need to update the abstracted array/list/var names as we cross the function boundary.
    //For example, if function Foo has two arrays f1 and f2 that are abstracted.
    //Function Bar is defined as void Bar(array b1, array b2) and suppose Foo calls Bar(f1,f2).
    //Abst_spec in Foo will contain f1, f2. These should be renamed to b1, b2 to obtain abst_spec for Bar.
    //The argument for the following function would be Foo, Bar, {f1: b1, f2: b2}
    //Return a new spect reflecting the changes
    spect update_abst_spec(std::string old_function, std::string new_function, std::unordered_map<std::string, std::string> _name_pairs);
  };

  // gather specs
  std::vector<spect> &get_specs();

protected:
  std::vector<spect> specs;
};

#endif // CPROVER_GOTO_INSTRUMENT_ABSTSPEC_H