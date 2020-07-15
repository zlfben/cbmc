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
#include <map>

class abstraction_spect
{
public:

  //This constructor parses the json abstraction specification and populates the class.
  abstraction_spect(std::string, message_handlert &);

  //gathers file names from all the individual specs and returns a list.  
  std::vector<std::string> get_abstraction_function_files();


  protected:
  struct entityt {
    std::string path;
    std::string name_of_abst;
    std::string name;

    public:
      entityt() {};
      entityt(std::string, std::string) {};
      std::string function_name() {return("foo");};
      std::string entity_name() {return ("foo");};
      std::string entity_abst() {return("foo");}
      std::string entity_path() {return("foo");};

  };

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

    //Use the same abstraction as a different array
    std::tuple<std::string, std::string> follow_array;

  public:
    spect() {}

    //We will have functions for accessing and modifying the above data.

    //We need to update the abstracted array/list/var names as we cross the function boundary.
    //For example, if function Foo has two arrays f1 and f2 that are abstracted.
    //Function Bar is defined as void Bar(array b1, array b2) and suppose Foo calls Bar(f1,f2).
    //Abst_spec in Foo will contain f1, f2. These should be renamed to b1, b2 to obtain abst_spec for Bar.
    //The argument for the following function would [(f1, b1),[f2,b2)]
    int update_entity_names(std::vector<std::tuple<std::string, std::string>>);
    
    //This function update indices list as we cross fucntion boundary.
    //Say we are abstraction array f1 in Foo. Abst_spec for f1 has indices say {i,j}. 
    //That is, variables i, j are used to directly index into f1.
    //Now we cross into Bar, and the arrays are now b1, b2. Suppose {l,m} are used to directly
    //index into b1, b2. After renaming the arrays f1 --> b1, f2 --> b2 we need to update the 
    //indices from {i,j} --> {l,m}. That's what this function does.
    int update_indices(std::string, std::string, std::vector<std::string>);

    
    //Update abst_spec: the overall function that uses the above two functions.
    int update_abst_spec(std::vector<std::tuple<std::string, std::string>>);

    

  };

  std::vector<spect> specs;

  //Actual index in references in the list. 
  //Say we use c1, c2 as references for abstracting array f. 
  //In the abstract program (C program level) c1,c2 will declared as variables and their 
  //values will be used to compute the abstractions. But at CBMC level we know only their names
  //c1,c2 but not their value. At C program level we have an array called ref-inds that is passed
  //to all functions being abstracted. We will associated index 0 with c1 and 1 with c2. So value of c1 
  //is just ref-inds[0] and so on. At C program level ref-inds will be populated at the function specified
  //in "path" field above for the array being abstracted. 
  //These will be computed by considering all the specs.
  std::map<entityt, int> ref_index_map;

};

#endif // CPROVER_GOTO_INSTRUMENT_ABSTSPEC_H