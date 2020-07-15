/*******************************************************************\

Module:

Authors: Murali Talupur talupur@amazon.com
         Lefan Zhang    lefanz@amazon.com

\*******************************************************************/

#include <iostream>

#include <json/json_parser.h>

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
    spec.path = entry["path"].value;
    spec.name = entry["name"].value;
    specs.push_back(spec);
  }
}

std::vector<std::string> abstraction_spect::get_abstraction_function_files()
{
  std::string file =
    "/Users/talupur/workspaces/abstract-cbmc/cbmc/regression/abstraction";
  std::vector<std::string> files(1, file);
  return (files);
}