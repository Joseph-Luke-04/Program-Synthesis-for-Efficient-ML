#include "define_fun_parser.h"

#include <solvers/smt2/smt2_parser.h>
#include <solvers/smt2/smt2_format.h>
#include <iostream>

class smt2_define_fun_parsert:public smt2_parsert
{
public:
  smt2_define_fun_parsert(std::istream &_in) : smt2_parsert(_in)
  {
  }
  
  // Predeclare known function symbols (name → type) into id_map
  void predeclare_functions(const std::vector<std::pair<irep_idt, typet>> &fns)
  {
    for(const auto &p : fns)
    {
      // IMPORTANT: avoid operator[]; idt has no default constructor
      auto ins = id_map.emplace(p.first, idt{idt::PARAMETER, p.second});
      if(!ins.second)
      {
        // key existed: overwrite the entry to the (kind,type) we want
        ins.first->second = idt{idt::PARAMETER, p.second};
      }
    }
  }

  define_fun_resultt define_fun()
  {
    if(next_token() != smt2_tokenizert::OPEN)
      throw error("expected (define-fun");

    if(next_token() != smt2_tokenizert::SYMBOL ||
       smt2_tokenizer.get_buffer() != "define-fun")
      throw error("expected (define-fun");

    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after define-fun");


    define_fun_resultt result;

    result.id = smt2_tokenizer.get_buffer();

    const auto signature = function_signature_definition();

    // put the parameters into the scope and take care of hiding
    std::vector<std::pair<irep_idt, idt>> hidden_ids;

    for(const auto &pair : signature.ids_and_types())
    {
      auto insert_result =
        id_map.insert({pair.first, idt{idt::PARAMETER, pair.second}});
      if(!insert_result.second) // already there
      {
        auto &id_entry = *insert_result.first;
        hidden_ids.emplace_back(id_entry.first, std::move(id_entry.second));
        id_entry.second = idt{idt::PARAMETER, pair.second};
      }
    }

    result.type = signature.type;
    result.parameters = signature.parameters;
    result.body = expression();

    // remove the parameter ids
    for(auto &id : signature.parameters)
      id_map.erase(id);

    // restore the hidden ids, if any
    for(auto &hidden_id : hidden_ids)
      id_map.insert(std::move(hidden_id));

    // check type of body
    if(signature.type.id() == ID_mathematical_function)
    {
      const auto &f_signature = to_mathematical_function_type(signature.type);
      if(result.body.type() != f_signature.codomain())
      {
        throw error() << "type mismatch in function definition: expected '"
                      << smt2_format(f_signature.codomain()) << "' but got '"
                      << smt2_format(result.body.type()) << '\'';
      }
    }
    else if(result.body.type() != signature.type)
    {
      throw error() << "type mismatch in function definition: expected '"
                    << smt2_format(signature.type) << "' but got '"
                    << smt2_format(result.body.type()) << '\'';
    }

    return result;
  }
};

define_fun_resultt define_fun_parser(std::istream &in)
{
  define_fun_resultt result;
  try{
    result = smt2_define_fun_parsert(in).define_fun();
  }
  catch(const smt2_tokenizert::smt2_errort &smterror)
  {
    std::cerr << smterror.what() << " on line number" << smterror.get_line_no() << std::endl;
    throw smterror;
  }
  return result;
}

define_fun_resultt define_fun_parser(
  std::istream &in,
  const std::vector<std::pair<irep_idt, typet>> &predeclared)
{
  define_fun_resultt result;
  try
  {
    smt2_define_fun_parsert P(in);
    P.predeclare_functions(predeclared);
    result = P.define_fun();
  }
  catch(const smt2_tokenizert::smt2_errort &smterror)
  {
    std::cerr << smterror.what() << " on line number" << smterror.get_line_no() << std::endl;
    throw smterror;
  }
  return result;
}
