/*******************************************************************\

Module: RRA Specification-Based Generation

Author: Adrian Palacios accorell@amazon.com
        Murali Talupur  talupur@amazon.com
        Lefan Zhang     lefanz@amazon.com

\*******************************************************************/

#include <util/cprover_prefix.h>
#include <util/irep.h>

#include <string>
#include <vector>
#include <map>

#include "rra_spec_gen.h"

std::vector<irep_idt> rra_spec_gent::generate_indices(std::string shape_type)
{
  std::vector<irep_idt> indices;
  size_t num_concs = count_concs(shape_type);

  for(size_t i = 0; i < num_concs; i++)
  {
    irep_idt index;
    index = "cncrt" + std::to_string(i);
    indices.push_back(index);
  }

  return indices;
}

/*
 * Generate a set of assumptions given a shape and a set of indices
 *
 * If the first symbol is a 'c', we must add assumption "cncrt0==0".
 * In the general case, whenever we find a 'c' ("cncrtX") in the shape,
 * we add an assumption depending on the preceding symbol:
 *  - 'c': "cncrtY==cncrtX-1"
 *  - '*': "cncrtY<cncrtX"
 * where Y = X-1
 *
 * Example: c*c*c*
 * Output: ["cncrt0==0","cncrt0<cncrt1","cncrt1<cncrt2"]
 *
 * Example: *cc*c*
 * Output: ["cncrt0==cncrt1-1","cncrt1<cncrt2"]
 */
std::vector<std::string> rra_spec_gent::generate_assumptions(
  std::string shape_type,
  std::vector<irep_idt> indices)
{
  std::vector<std::string> assumptions;
  size_t shape_len = shape_type.length();
  size_t cur_c = 0;

  if(shape_type[0] == 'c')
  {
    std::string fst_assumption = id2string(indices[0]) + "==0";
    assumptions.push_back(fst_assumption);
  }

  for(size_t i = 0; i < shape_len; i++)
  {
    if(shape_type[i] == 'c' || shape_type[i] == 'l')
    {
      if(cur_c > 0)
      {
        std::string assumption;

        if(shape_type[i - 1] == '*')
        {
          assumption =
            id2string(indices[cur_c - 1]) + "<" + id2string(indices[cur_c]);
        }
        else // shape_type[i - 1] == 'c'
        {
          assumption = id2string(indices[cur_c - 1]) +
                       "==" + id2string(indices[cur_c]) + "-1";
        }

        assumptions.push_back(assumption);
      }
      cur_c++;
    }
  }

  return assumptions;
}

void rra_spec_gent::generate_functions(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  generate_fun_raw2real(spec_index, shape_type, output);
  generate_fun_real2raw(spec_index, shape_type, output);
  generate_fun_abs(spec_index, shape_type, output);
  generate_fun_conc(spec_index, shape_type, output);
  generate_fun_prec(spec_index, shape_type, output);
  generate_fun_add(spec_index, shape_type, output);
  generate_fun_sub(spec_index, shape_type, output);
  generate_fun_mult(spec_index, shape_type, output);
}

size_t rra_spec_gent::count_concs(std::string shape_type)
{
  size_t num_concs = 0;
  size_t shape_len = shape_type.length();

  for(size_t i = 0; i < shape_len; i++)
    if(shape_type[i] == 'c' || shape_type[i] == 'l')
      num_concs++;

  return num_concs;
}

void rra_spec_gent::generate_abst_funcs_hdr(std::ostream &output)
{
  output << "#include <stdint.h>\n";
  output << "#include <assert.h>\n";
  output << "#include <stddef.h>\n";
  output << "#include <stdbool.h>\n\n";

  output << "size_t nndt_int(){\n";
  output << "\tsize_t i;\n";
  output << "\treturn(i);\n";
  output << "}\n\n";

  output << "bool nndt_bool(){\n";
  output << "\tsize_t i;\n";
  output << "\treturn(i % 2);\n";
  output << "}\n\n";

  output << "size_t nndt_under(size_t bound){\n";
  output << "\tsize_t nd;\n";
  output << "\t" CPROVER_PREFIX "assume(nd < bound);\n";
  output << "\treturn(nd);\n";
  output << "}\n\n";

  output << "size_t nndt_between(size_t l, size_t u){\n";
  output << "\tsize_t diff = u - l;\n";
  output << "\tsize_t nd = nndt_under(diff);\n";
  output << "\tif (nd == 0) return(l+1);\n";
  output << "\telse return(nd + l);\n";
  output << "}\n\n";

  output << "size_t nndt_above(size_t bound){\n";
  output << "\tsize_t nd = nndt_int();\n";
  output << "\t" CPROVER_PREFIX "assume(nd > bound);\n";
  output << "\treturn(nd);\n";
  output << "}\n\n";
}

std::map<size_t, std::string> rra_spec_gent::get_conc_loc_names(
  std::string shape_type)
{
  size_t count = 0;
  std::map<size_t, std::string> res;
  for(size_t i = 0; i < shape_type.length(); i++)
  {
    if(shape_type[i] == 'c' || shape_type[i] == 'l')
    {
      count++;
      res.insert(std::make_pair(i, "a"+std::to_string(count)));
    }
  }
  return res;
}

std::map<size_t, std::string> rra_spec_gent::get_star_skip_pred(
  std::string shape_type)
{
  size_t count = 0;
  std::map<size_t, std::string> res;
  for(size_t i = 0; i < shape_type.length(); i++)
  {
    if(shape_type[i] == 'c' || shape_type[i] == 'l')
    {
      count++;
    }
    else
    {
      if(i == 0)
        res.insert(std::make_pair(i, "a" + std::to_string(count + 1) + "==0"));
      else
        res.insert(std::make_pair(
          i,
          "a" + std::to_string(count) + "+1==" + "a" +
            std::to_string(count + 1)));
    }
  }
  return res;
}

void rra_spec_gent::generate_fun_raw2real(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  INVARIANT(shape_type.length() > 0, "Shape should not be empty");
  if(shape_type[shape_type.length()-1] != '*')
    shape_type += '*';
  std::map<size_t, std::string> conc_loc_names = get_conc_loc_names(shape_type);
  std::map<size_t, std::string> star_skip_pred = get_star_skip_pred(shape_type);

  output << "size_t raw_to_real_" + std::to_string(spec_index) + "(size_t raw_index";
  for (auto it = conc_loc_names.begin(); it != conc_loc_names.end(); it++)
    output << ",size_t " + it->second;
  output << ") {\n";
  output << "\treturn raw_index";
  for (size_t i = 0; i < shape_type.length(); i++) {
    if (i != shape_type.length()-1 && shape_type[i] == '*') {
      std::string entry = "raw_index>" + std::to_string(i);
      entry += " && ";
      entry += star_skip_pred[i];
      output << " - (" + entry + ")";
    }
  }
  output << ";\n";
  output << "}\n\n";
}

void rra_spec_gent::generate_fun_real2raw(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  INVARIANT(shape_type.length() > 0, "Shape should not be empty");
  if(shape_type[shape_type.length()-1] != '*')
    shape_type += '*';

  std::map<size_t, std::string> conc_loc_names = get_conc_loc_names(shape_type);
  std::map<size_t, std::string> star_skip_pred = get_star_skip_pred(shape_type);
  std::map<size_t, std::string> conc_locs;

  output << "size_t real_to_raw_" + std::to_string(spec_index) + "(size_t real_index";
  for (auto it = conc_loc_names.begin(); it != conc_loc_names.end(); it++)
    output << ",size_t " + it->second;
  output << ") {\n";

  for(size_t i = 0; i < shape_type.length(); i++)
  {
    std::string entry = std::to_string(i);
    if (shape_type[i] != '*')
    {
      for(size_t j = 0; j < i; j++)
      if(shape_type[j] == '*')
        entry = entry + "-(" + star_skip_pred[j] + ")";
      conc_locs.insert(std::make_pair(i, entry));
    }
  }

  for(size_t i = 0; i < shape_type.length(); i++)
  {
    if(i != shape_type.length()-1)
    {
      output << "\tif (real_index";
      if(shape_type[i] == '*') // real_index < next conc_loc
        output << " < " << conc_locs[i+1] << ")\n";
      else // real_index == current conc_loc
        output << " == " << conc_locs[i] << ")\n";
      output << "\t\treturn " + std::to_string(i) + ";\n";
    }
    else
    {
      output << "\telse\n";
      output << "\t\treturn " + std::to_string(i) + ";\n";
    }
  }

  output << "}\n\n";
}

void rra_spec_gent::generate_fun_abs(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  INVARIANT(shape_type.length() > 0, "Shape should not be empty");
  if(shape_type[shape_type.length()-1] != '*')
    shape_type += '*';
  
  std::map<size_t, std::string> conc_loc_names = get_conc_loc_names(shape_type);

  output << "// Detected shape: " + shape_type + "\n";
  output << "size_t abs_" + std::to_string(spec_index) + "(size_t index";

  for (auto it = conc_loc_names.begin(); it != conc_loc_names.end(); it++)
    output << ",size_t " + it->second;
  output << ") {\n";

  output << "\tsize_t raw_index = ";
  output << std::to_string(shape_type.length()-1);
  output << ";\n";

  for(size_t i = 0; i < shape_type.length(); i++)
  {
    if(i != shape_type.length()-1)
    {
      output << "\tif (";
      if(shape_type[i] == '*' && i == 0)
        output << "index < " << conc_loc_names[i+1];
      else if(shape_type[i] == '*' && i != 0)
        output << "index > " << conc_loc_names[i-1] << " && " << "index < " << conc_loc_names[i+1];
      else
        output << "index == " << conc_loc_names[i];
      output << ") raw_index=";
      output << std::to_string(i) + ";\n";
    }
  }

  output << "\treturn raw_to_real_" << std::to_string(spec_index) << "(";
  output << "raw_index";
  for (auto it = conc_loc_names.begin(); it != conc_loc_names.end(); it++)
    output << ", " + it->second;
  output << ");\n";
  output << "}\n\n";
}

void rra_spec_gent::generate_fun_conc(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  INVARIANT(shape_type.length() > 0, "Shape should not be empty");
  if(shape_type[shape_type.length()-1] != '*')
    shape_type += '*';

  std::map<size_t, std::string> conc_loc_names = get_conc_loc_names(shape_type);

  output << "size_t conc_" + std::to_string(spec_index) + "(size_t abs_ind";
  for (auto it = conc_loc_names.begin(); it != conc_loc_names.end(); it++)
    output << ",size_t " + it->second;
  output << ") {\n";
  
  output << "\tsize_t raw_index = real_to_raw_" << std::to_string(spec_index);
  output << "(abs_ind";
  for (auto it = conc_loc_names.begin(); it != conc_loc_names.end(); it++)
    output << ", " + it->second;
  output << ");\n";

  for(size_t i = 0; i < shape_type.length(); i++)
  {
    output << "\tif (raw_index == " << std::to_string(i) << ") ";
    output << "return ";
    if(shape_type[i] == '*' && i == 0)
      output << "nndt_under(" << conc_loc_names[i+1] << ")";
    else if(shape_type[i] == '*' && i == shape_type.length()-1)
      output << "nndt_above(" << conc_loc_names[i-1] << ")";
    else if(shape_type[i] == '*')
      output << "nndt_between(" << conc_loc_names[i-1]+","+conc_loc_names[i+1]+")";
    else
      output << conc_loc_names[i];
    output << ";\n";
  }
  output << "}\n\n";
}

void rra_spec_gent::generate_fun_prec(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  INVARIANT(shape_type.length() > 0, "Shape should not be empty");
  if(shape_type[shape_type.length()-1] != '*')
    shape_type += '*';

  std::map<size_t, std::string> conc_loc_names = get_conc_loc_names(shape_type);

  output << "bool is_precise_" + std::to_string(spec_index) +
              "(size_t abs_ind";
  for (auto it = conc_loc_names.begin(); it != conc_loc_names.end(); it++)
    output << ",size_t " + it->second;
  output << ") {\n";

  output << "\tsize_t raw_index = real_to_raw_" << std::to_string(spec_index);
  output << "(abs_ind";
  for (auto it = conc_loc_names.begin(); it != conc_loc_names.end(); it++)
    output << ", " + it->second;
  output << ");\n";

  for(size_t i = 0; i < shape_type.length(); i++)
    if(shape_type[i] != '*')
      output << "\tif(raw_index == " + std::to_string(i) + ") return 1;\n";

  output << "\treturn 0;\n";
  output << "}\n\n";
}

void rra_spec_gent::generate_fun_add(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  INVARIANT(shape_type.length() > 0, "Shape should not be empty");
  if(shape_type[shape_type.length()-1] != '*')
    shape_type += '*';

  std::map<size_t, std::string> conc_loc_names = get_conc_loc_names(shape_type);
  std::map<size_t, std::string> star_skip_pred = get_star_skip_pred(shape_type);

  size_t num_concs = count_concs(shape_type);

  output << "size_t add_" + std::to_string(spec_index) +
              "(size_t abs_ind, size_t num";
  for (auto it = conc_loc_names.begin(); it != conc_loc_names.end(); it++)
    output << ",size_t " + it->second;
  output << ") {\n";

  output << "\tif (num == 0) return abs_ind;\n";
  output << "\tif (num == 1) {\n";

  output << "\t\tif (is_precise_" + std::to_string(spec_index) + "(abs_ind";
  for (auto it = conc_loc_names.begin(); it != conc_loc_names.end(); it++)
    output << ", " + it->second;
  output << "))\n";
  output << "\t\t\treturn abs_ind + 1;\n";

  std::string last_loc = std::to_string(shape_type.length()-1);
  for(size_t i = 0; i < shape_type.length()-1; i++)
  {
    if (shape_type[i] == '*')
    {
      last_loc += "-(";
      last_loc += star_skip_pred[i];
      last_loc += ")";
    }
  }

  output << "\t\treturn ((abs_ind == " << last_loc << ")";
  output << " || nndt_bool()) ? abs_ind : abs_ind + 1;\n";
  output << "\t}\n";
  output << "\tsize_t conc_idx = conc_" + std::to_string(spec_index) +
              "(abs_ind,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ");\n";
  output << "\treturn abs_" + std::to_string(spec_index) + "(conc_idx + num,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ");\n";
  output << "}\n\n";
}

void rra_spec_gent::generate_fun_sub(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  size_t num_concs = count_concs(shape_type);

  output << "size_t sub_" + std::to_string(spec_index) +
              "(size_t abs_ind, size_t num,";

  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "size_t a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ") {\n";
  output << "\tif (num == 0) return abs_ind;\n";
  output << "\tif (num == 1) {\n";

  output << "\t\tif (is_precise_" + std::to_string(spec_index) + "(abs_ind,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ")) {\n";
  output << "\t\t\tif (abs_ind != 0)\n";
  output << "\t\t\t\treturn abs_ind - 1;\n";
  output << "\t\t\telse assert(0!=0);\n";
  output << "\t\t} else return (abs_ind == 0 || nndt_bool()) ? ";
  output << "abs_ind : abs_ind - 1;\n";
  output << "\t}\n";

  output << "\tsize_t conc_idx = conc_" + std::to_string(spec_index) +
              "(abs_ind,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ");\n";
  output << "\tassert(conc_idx >= num);\n";
  output << "\treturn abs_" + std::to_string(spec_index) + "(conc_idx - num,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ");\n";
  output << "}\n\n";
}

void rra_spec_gent::generate_fun_mult(
  size_t spec_index,
  std::string shape_type,
  std::ostream &output)
{
  size_t num_concs = count_concs(shape_type);

  output << "size_t mult_" + std::to_string(spec_index) +
              "(size_t abs_ind, size_t num,";

  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "size_t a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ") {\n";
  output << "\tif (num == 0) return 0;\n";
  output << "\tif (num == 1) return abs_ind;\n";
  output << "\tsize_t conc_idx = conc_" + std::to_string(spec_index) +
              "(abs_ind,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ");\n";
  output << "\treturn abs_" + std::to_string(spec_index) + "(conc_idx * num,";
  for(size_t i = 1; i <= num_concs; i++)
  {
    output << "a" + std::to_string(i);
    if(i != num_concs)
      output << ",";
  }
  output << ");\n";
  output << "}\n\n";
}
