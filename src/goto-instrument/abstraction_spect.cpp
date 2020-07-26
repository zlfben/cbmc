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
  for(const jsont &entry : to_json_array(json["entries"]))
  {
    spect spec;
    function = entry["function"].value;  // we assume that all entries in the json file are located in the same function
    spec.insert_entity(entry["name"].value, entry["entity"].value=="array");
    spec.set_abst_func_file(get_absolute_path(entry["abst-function-file"].value));
    for(const jsont &related_entity : to_json_array(entry["related-entities"]))
    {
      spec.insert_entity(related_entity["name"].value, related_entity["entity"].value=="array");
    }
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
    if(_name_pairs.find(name) != _name_pairs.end())
    {
      // This array needs to be updated
      if(
        std::string(abst_arrays.at(name).entity_name().c_str())
          .rfind(old_function.c_str(), 0) ==
        0) // erase the old entity if it's not a global variable
        new_spec.abst_arrays.erase(name);
      new_spec.abst_arrays.insert({_name_pairs[name], entityt(_name_pairs[name])});
    }
  }
  for(const auto &name: abst_index_ids)
  {
    if(_name_pairs.find(name) != _name_pairs.end())
    {
      // This index variable needs to be updated
      if(
        std::string(abst_indices.at(name).entity_name().c_str())
          .rfind(old_function.c_str(), 0) ==
        0) // erase the old entity if it's not a global variable
        new_spec.abst_indices.erase(name);
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
  for(const auto &spec: specs)
  {
    new_abst_spec.specs.push_back(spec.update_abst_spec(old_function, new_function, _name_pairs));
  }
  return new_abst_spec;
}
