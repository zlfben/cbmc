/*******************************************************************\

Module:

Authors: Murali Talupur, talupur@amazon.com
         Lefan Zhang,    lefanz@amazon.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_ABSTSPEC_H
#define CPROVER_GOTO_INSTRUMENT_ABSTSPEC_H

#include <limits>
#include <list>
#include <string>
#include <vector>
#include <tuple>

class abstraction_spect
{
public:

  //This constructor parses the json abstraction specification and populates the class.
  abstraction_spect(std::string, message_handlert &);

  //gathers file names from all the individual specs and returns a list.  
  std::vector<std::string> get_abstraction_function_files() const;


  protected:
  struct spect
  {
    //Hierarchical path to the array/list being abstracted
    std::string path;
    //Name of the array/list being abstracted
    std::string name;
    //Abstraction func file
    std::string abst_func_file;
    //Names of references in increasing order
    std::vector<std::string> refs_name;
    //Actual index in references in the list
    std::vector<int> refs_indices;
  
    //List of directly indexing variables. 
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

    //Use the same abstraction as a different array
    std::tuple<std::string, std::string> follow_array;

  public:
    spect() {}

    //We will have functions for accessing and modifying the above data.
    //In particular we will have functions for updating indices list as we cross fucntion boundary.
    int update_indices(std::string, std::string, std::vector<std::string>);


  };

  std::vector<spect> specs;


};

#endif // CPROVER_GOTO_INSTRUMENT_ABSTSPEC_H