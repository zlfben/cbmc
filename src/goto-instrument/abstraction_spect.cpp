/*******************************************************************\

Module:

Authors: Murali Talupur talupur@amazon.com
         Lefan Zhang    lefanz@amazon.com

\*******************************************************************/

#include <iostream>

#include <json/json_parser.h>
#include <util/file_util.h>

#include "abstraction_spect.h"

abstraction_spect::abstraction_spect(
  std::string filename,
  message_handlert &message_handler)
{
  jsont json;
  parse_json(filename, message_handler, json);
  const auto &json_object = to_json_object(json);
  const auto &json_entries = json_object.find("entries")->second;
  const auto &json_entries_array = to_json_array(json_entries);
  for(auto it=json_entries_array.begin(); it != json_entries_array.end(); ++it)
  {
    const auto &entry_obj = to_json_object(*it);
    spect spec;
    size_t spec_index = specs.size();
    function = entry_obj.find("function")->second.value;  // we assume that all entries in the json file are located in the same function
    // insert the entity
    spec.insert_entity(entry_obj.find("name")->second.value, entry_obj.find("entity")->second.value!="array");
    const auto &json_re_array = to_json_array(entry_obj.find("related-entities")->second);
    for(auto it_r=json_re_array.begin(); it_r != json_re_array.end(); ++it_r)
    {
      const auto &related_entity = to_json_object(*it_r);
      spec.insert_entity(related_entity.find("name")->second.value, related_entity.find("entity")->second.value!="array");
    }

    // initialize the abst functions
    spec.set_abst_func_file(get_absolute_path(entry_obj.find("abst-function-file")->second.value));
    spec.set_addition_func(to_json_object(entry_obj.find("abst-functions")->second).find("add-abs-conc")->second.value);
    spec.set_minus_func(to_json_object(entry_obj.find("abst-functions")->second).find("sub-abs-conc")->second.value);
    spec.set_precise_func(to_json_object(entry_obj.find("abst-functions")->second).find("precise-check")->second.value);
    spec.set_abstract_func(to_json_object(entry_obj.find("abst-functions")->second).find("abstract-index")->second.value);
    
    // initialize the shape of this spect
    const auto &json_shape_obj = to_json_object(entry_obj.find("shape")->second);
    const auto &json_shape_i_array = to_json_array(json_shape_obj.find("indices")->second);
    const auto &json_shape_a_array = to_json_array(json_shape_obj.find("assumptions")->second);
    std::vector<irep_idt> indices;
    std::vector<std::string> assumptions;
    for(auto it_i=json_shape_i_array.begin(); it_i != json_shape_i_array.end(); ++it_i)
      indices.push_back(to_json_string(*it_i).value);
    for(auto it_a=json_shape_a_array.begin(); it_a != json_shape_a_array.end(); ++it_a)
      assumptions.push_back(to_json_string(*it_a).value);
    std::string shape_type = to_json_string(json_shape_obj.find("shape-type")->second).value;
    spec.set_shape(indices, assumptions, shape_type, spec_index);

    specs.push_back(spec);
  }
}

std::vector<std::string> abstraction_spect::get_abstraction_function_files() const
{
  std::vector<std::string> files;
  for (const spect &s: specs)
  {
    files.push_back(s.get_abst_func_file());
  }
  return files;
}

abstraction_spect::spect abstraction_spect::spect::update_abst_spec(
  irep_idt old_function,
  irep_idt new_function,
  std::unordered_map<irep_idt, irep_idt> _name_pairs) const
{
  // copy the spec into a new one
  spect new_spec(*this);

  // store the entity names in the original spect
  std::vector<irep_idt> abst_array_ids;
  std::vector<irep_idt> abst_index_ids;
  for(const auto &p: abst_arrays)
    abst_array_ids.push_back(p.first);
  for(const auto &p: abst_indices)
    abst_index_ids.push_back(p.first);
  
  for(const auto &name: abst_array_ids)
  {
    if(
      std::string(abst_arrays.at(name).entity_name().c_str())
        .rfind(old_function.c_str(), 0) ==
      0) // erase the old entity if it's not a global variable
      new_spec.abst_arrays.erase(name);
    if(_name_pairs.find(name) != _name_pairs.end())
    {
      // This array needs to be updated
      new_spec.abst_arrays.insert({_name_pairs[name], entityt(_name_pairs[name])});
    }
  }
  for(const auto &name: abst_index_ids)
  {
    if(
        std::string(abst_indices.at(name).entity_name().c_str())
          .rfind(old_function.c_str(), 0) ==
        0) // erase the old entity if it's not a global variable
        new_spec.abst_indices.erase(name);
    if(_name_pairs.find(name) != _name_pairs.end())
    {
      // This index variable needs to be updated
      new_spec.abst_indices.insert({_name_pairs[name], entityt(_name_pairs[name])});
    }
  }

  return new_spec;
}

abstraction_spect abstraction_spect::update_abst_spec(
  irep_idt old_function,
  irep_idt new_function,
  std::unordered_map<irep_idt, irep_idt> _name_pairs) const
{
  if(function != old_function)
  {
    throw "The old abstraction_spect should match the callee";
  }

  abstraction_spect new_abst_spec;
  new_abst_spec.function = new_function;
  for(const auto &spec: specs)
  {
    spect new_spec = spec.update_abst_spec(old_function, new_function, _name_pairs);
    if(!spec.compare_shape_only(new_spec))
      throw "The updated spect's shape should be the same as the original one";
    new_abst_spec.specs.push_back(new_spec);
  }
  if(specs.size() != new_abst_spec.specs.size())
    throw "The updated specs' size should remain the same";
  return new_abst_spec;
}

std::string abstraction_spect::get_entities_string() const
{
  std::string str = "";
  for(const auto &spec: specs)
  {
    for(const auto &ent: spec.get_abst_arrays())
      str += "array: " + std::string(ent.second.entity_name().c_str()) + "\n";
    for(const auto &ent: spec.get_abst_indices())
      str += "index: " + std::string(ent.second.entity_name().c_str()) + "\n";
  }
  return str;
}

void abstraction_spect::print_entities() const
{
  std::cout << get_entities_string();
}