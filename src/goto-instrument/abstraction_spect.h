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
  abstraction_spect() {}
  //This constructor parses the json abstraction specification and populates the class.
  abstraction_spect(std::string, message_handlert &);

  //gathers file names from all the individual specs and returns a list.
  std::vector<std::string> get_abstraction_function_files() const;

public:
  struct spect
  {
  public:
    struct abst_shapet
    {
      std::vector<irep_idt> indices;
      std::vector<std::string> assumptions;
      std::string shape_type;  // e.g. "*cc*"
    public:
      abst_shapet() {}
      abst_shapet(
        std::vector<irep_idt> _indices,
        std::vector<std::string> _assumptions,
        std::string _shape_type)
        : indices(_indices), assumptions(_assumptions), shape_type(_shape_type) {}
      abst_shapet(const abst_shapet &other)
        : indices(other.indices),
          assumptions(other.assumptions),
          shape_type(other.shape_type)
      {
      }
      void add_index(const irep_idt &_index)
      {
        indices.push_back(_index);
      }
      void add_assumption(const std::string &_assumption)
      {
        assumptions.push_back(_assumption);
      }
      void set_shape_type(const std::string &_shape_type)
      {
        shape_type = _shape_type;
      }
      bool operator==(const abst_shapet &other) const
      {
        if(indices.size() != other.indices.size())
          return false;
        if(assumptions.size() != other.assumptions.size())
          return false;
        for(size_t i=0; i<indices.size(); i++)
          if(indices[i] != other.indices[i])
            return false;
        for(size_t i=0; i<assumptions.size(); i++)
          if(assumptions[i] != other.assumptions[i])
            return false;
        return (shape_type == other.shape_type);
      }
    };

    struct entityt
    {
      //Name of the array/list being abstracted
      irep_idt name; // should be in the id format: function::x::name, this is the unique identifier
      std::string name_of_abst;

    public:
      entityt(){}
      entityt(irep_idt _name) : name(_name) {}
      entityt(const entityt &_entity) : name(_entity.name), name_of_abst(_entity.name_of_abst) {}


      irep_idt entity_name() const
      {
        return name;
      }

      void set_entity_name(const irep_idt &new_name)
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
    std::unordered_map<irep_idt, entityt> abst_arrays;
    // std::vector<entityt> abst_arrays;

    //Index vars to be abstracted
    std::unordered_map<irep_idt, entityt> abst_indices;
    // std::vector<entityt> abst_indices;

    // Shape of the abstraction
    abst_shapet shape;

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
        shape(_spec.shape), 
        is_precise_func(_spec.is_precise_func),
        compare_indices_func(_spec.compare_indices_func),
        addition_func(_spec.addition_func),
        minus_func(_spec.minus_func)
    {
    }

    //We will have functions for accessing and modifying the above data.
    //array_or_index: false-array, true-index
    void insert_entity(const irep_idt &_name, bool array_or_index)
    {
      entityt new_entity(_name);
      if(!array_or_index)
        abst_arrays.insert({_name, new_entity});
      else
        abst_indices.insert({_name, new_entity});
    }

    const std::unordered_map<irep_idt, entityt> &get_abst_arrays() const
    {
      return abst_arrays;
    }

    const std::unordered_map<irep_idt, entityt> &get_abst_indices() const
    {
      return abst_indices;
    }

    const bool has_entity(const irep_idt &entity_name) const
    {
      return (abst_arrays.find(entity_name) != abst_arrays.end()) ||
             (abst_indices.find(entity_name) != abst_indices.end());
    }

    const bool has_index_entity(const irep_idt &entity_name) const
    {
      return (abst_indices.find(entity_name) != abst_indices.end());
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

    // set the shape
    void set_shape(const std::vector<irep_idt> &indices, const std::vector<std::string> &assumptions, const std::string &shape_type)
    {
      shape = abst_shapet(indices, assumptions, shape_type);
    }

    // compare if two spect have the same abst shape
    bool compare_shape(const spect &other) const
    {
      if(abst_arrays.size() != other.abst_arrays.size())
        return false;
      if(abst_indices.size() != other.abst_indices.size())
        return false;
      for(const auto &array: abst_arrays)
        if(other.abst_arrays.find(array.first) == other.abst_arrays.end())
          return false;
      for(const auto &index: abst_indices)
        if(other.abst_indices.find(index.first) == other.abst_indices.end())
          return false;
      return shape == other.shape;
    }

    bool compare_shape_only(const spect &other) const
    {
      return shape == other.shape;
    }

    //We need to update the abstracted array/list/var names as we cross the function boundary.
    //For example, if function Foo has two arrays f1 and f2 that are abstracted.
    //Function Bar is defined as void Bar(array b1, array b2) and suppose Foo calls Bar(f1,f2).
    //Abst_spec in Foo will contain f1, f2. These should be renamed to b1, b2 to obtain abst_spec for Bar.
    //The argument for the following function would be Foo, Bar, {f1: b1, f2: b2}
    //Return a new spect reflecting the changes
    spect update_abst_spec(
      irep_idt old_function,
      irep_idt new_function,
      std::unordered_map<irep_idt, irep_idt> _name_pairs) const;
  };

  // gather specs
  std::vector<spect> &get_specs()
  {
    return specs;
  }

  // gather specs constant version
  const std::vector<spect> &get_specs() const
  {
    return specs;
  }

  // get function name
  const irep_idt &get_func_name() const
  {
    return function;
  }

  // update all specs when crossing the function call boundary
  abstraction_spect update_abst_spec(
    irep_idt old_function,
    irep_idt new_function,
    std::unordered_map<irep_idt, irep_idt> _name_pairs) const;

  // check if a variable is abstracted
  bool has_entity(const irep_idt &entity_name) const
  {
    for(const spect &spec: specs)
    {
      if(spec.has_entity(entity_name))
        return true;
    }
    return false;
  }

  // check if a variable is an index to be abstracted
  bool has_index_entity(const irep_idt &entity_name) const
  {
    for(const spect &spec: specs)
    {
      if(spec.has_index_entity(entity_name))
        return true;
    }
    return false;
  }

  // return the spect that has the entity, should always run has_index_entity before running this function
  const spect &get_spec_for_index_entity(const irep_idt &entity_name) const
  {
    for(const spect &spec: specs)
    {
      if(spec.has_index_entity(entity_name))
        return spec;
    }
    throw "Entity " + std::string(entity_name.c_str()) + " not found";
  }

  // compare if two spect have the same structure
  bool compare_shape(const abstraction_spect &other) const
  {
    // In the update_abst_spec function, the result and the 
    // original one should have the same spects in terms 
    // of both order and shape
    if(specs.size() != other.specs.size())
      return false;
    for(size_t i=0; i<specs.size(); i++)
      if(!specs[i].compare_shape(other.specs[i]))
        return false;
    return true;
  }

  // get a string containing all entity names
  std::string get_entities_string() const;
  // print all entities
  void print_entities() const;
protected:
  std::vector<spect> specs;
  irep_idt function; // function name, no need to have path
};

#endif // CPROVER_GOTO_INSTRUMENT_ABSTSPEC_H
