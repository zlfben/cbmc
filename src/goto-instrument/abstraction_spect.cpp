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