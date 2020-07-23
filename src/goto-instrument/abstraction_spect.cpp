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
    spec.insert_entity(entry["function"].value, entry["name"].value, entry["entity"].value=="array");
    spec.set_abst_func_file(get_absolute_path(entry["abst-function-file"].value));
    for(const jsont &related_entity : to_json_array(entry["related-entities"]))
    {
      spec.insert_entity(related_entity["function"].value, related_entity["name"].value, related_entity["entity"].value=="array");
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

std::vector<abstraction_spect::spect> &abstraction_spect::get_specs()
{
  return specs;
}

abstraction_spect::spect abstraction_spect::spect::update_abst_spec(
  std::string old_function,
  std::string new_function,
  std::unordered_map<std::string, std::string> _name_pairs)
{
  spect new_spec(*this);

  std::vector<std::string> abst_array_ids;
  std::vector<std::string> abst_index_ids;
  for(const auto &p: abst_arrays)
    abst_array_ids.push_back(p.first);
  for(const auto &p: abst_indices)
    abst_index_ids.push_back(p.first);
  
  for(const auto &name: abst_array_ids)
  {
    if(_name_pairs.find(name) != _name_pairs.end())
    {
      // This array needs to be updated
      if(abst_arrays[name].function_name() != old_function)
        throw "global variables shouldn't be updated";
      new_spec.abst_arrays.erase(name);
      new_spec.abst_arrays.insert({_name_pairs[name], entityt(new_function, _name_pairs[name])});
    }
  }
  for(const auto &name: abst_index_ids)
  {
    if(_name_pairs.find(name) != _name_pairs.end())
    {
      // This index variable needs to be updated
      if(abst_indices[name].function_name() != old_function)
        throw "global variables shouldn't be updated";
      new_spec.abst_indices.erase(name);
      new_spec.abst_indices.insert({_name_pairs[name], entityt(new_function, _name_pairs[name])});
    }
  }

  return new_spec;
}