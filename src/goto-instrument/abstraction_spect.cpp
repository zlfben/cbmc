/*******************************************************************\

Module:

Authors: Murali Talupur talupur@amazon.com
         Lefan Zhang    lefanz@amazon.com

\*******************************************************************/

#include "abstraction_spect.h"

std::vector<std::string> abstraction_spect::get_abstraction_function_files() {
    std::string file = "/Users/talupur/workspaces/abstract-cbmc/cbmc/regression/abstraction";
    std::vector<std::string> files(1, file);
    return (files);
}