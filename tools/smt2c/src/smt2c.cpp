#include "define_fun_parser.h"

#include <util/cmdline.h>
#include <util/mathematical_types.h>

#include <iostream>
#include <regex>
#include <set>
#include <algorithm>

#include <ansi-c/expr2c.h>

#include <util/config.h>
#include <util/exception_utils.h>
#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/substitute_symbols.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/namespace.h>

#define CBMC_ORACLE_OPTIONS ""

void help(std::ostream &out)
{
  out <<
    "SMT2C converts SMT-LIB (define-fun ...) blocks into compilable C functions.\n"
    "\n"
    "Usage:\n"
    "  smt2c \"<define-fun helper1 ...>\" [\"<define-fun helper2 ...>\"] ... \"<define-fun top ...>\"\n"
    "\n"
    "Notes:\n"
    "  • You may pass multiple (define-fun ...) blocks.\n"
    "  • Helpers must appear before any function that calls them.\n"
    "\n"
    "Example:\n"
    "  smt2c \\\n"
    "    \"(define-fun select_exponent ((e1 (_ BitVec 4)) (e2 (_ BitVec 4))) (_ BitVec 4)\n"
    "       (ite (bvsge e1 e2) e1 e2))\" \\\n"
    "    \"(define-fun align_mantissas ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4))) (_ BitVec 8)\n"
    "       (let ((_let_1 (bvsge e1 e2)))\n"
    "         (concat (ite _let_1 m1 (bvashr m1 (bvsub e2 e1)))\n"
    "                 (ite _let_1 (bvashr m2 (bvsub e1 e2)) m2))))\" \\\n"
    "    \"(define-fun add_raw ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4))) (_ BitVec 9)\n"
    "       (let ((_let_1 (align_mantissas m1 e1 m2 e2)))\n"
    "         (concat (bvadd ((_ sign_extend 1) ((_ extract 7 4) _let_1))\n"
    "                         ((_ sign_extend 1) ((_ extract 3 0) _let_1)))\n"
    "                 (select_exponent e1 e2))))\"\n";
}

irep_idt tweak_identifier(irep_idt src)
{
  std::string new_identifier = id2string(src);

  for(auto &ch : new_identifier)
    if(ch == '#')
      ch = '$';

  return new_identifier;
}

exprt tweak_symbols(exprt src)
{
  exprt dest = src;

  dest.visit_pre([](exprt &node) {
    if(node.id() == ID_symbol)
    {
      auto &symbol = to_symbol_expr(node);
      symbol.set_identifier(tweak_identifier(symbol.get_identifier()));
    }
  });

  return dest;
}

exprt lower_concatenation_for_c(const concatenation_exprt &concat_expr)
{
  const typet &result_type = concat_expr.type();
  const auto &ops = concat_expr.operands();

  if(ops.empty())
    return concat_expr;

  exprt result = typecast_exprt::conditional_cast(ops.front(), result_type);

  for(std::size_t i = 1; i < ops.size(); ++i)
  {
    const auto &op = ops[i];
    const auto op_width = to_bitvector_type(op.type()).get_width();

    result = bitor_exprt(
      shl_exprt(std::move(result), from_integer(op_width, result_type)),
      typecast_exprt::conditional_cast(op, result_type));
  }

  return result;
}

void normalize_for_c_output(exprt &expr)
{
  for(auto &op : expr.operands())
    normalize_for_c_output(op);

  if(expr.id() == ID_zero_extend)
  {
    const auto &zero_extend = to_zero_extend_expr(expr);
    expr = typecast_exprt::conditional_cast(zero_extend.op(), zero_extend.type());
  }
  else if(expr.id() == ID_concatenation)
  {
    expr = lower_concatenation_for_c(to_concatenation_expr(expr));
  }
}

void collect_bitor_operands(const exprt &expr, std::vector<exprt> &out)
{
  if(expr.id() == ID_bitor)
  {
    for(const auto &op : expr.operands())
      collect_bitor_operands(op, out);
    return;
  }

  out.push_back(expr);
}

void simplify_for_readability(exprt &expr)
{
  for(auto &op : expr.operands())
    simplify_for_readability(op);

  if(expr.id() == ID_if)
  {
    const auto &if_expr = to_if_expr(expr);
    if(if_expr.true_case() == if_expr.false_case())
    {
      expr = if_expr.true_case();
      return;
    }
  }

  if(expr.id() == ID_typecast)
  {
    const auto &typecast = to_typecast_expr(expr);
    if(typecast.op().type() == typecast.type())
    {
      expr = typecast.op();
      return;
    }
  }

  if(expr.id() == ID_bitor)
  {
    std::vector<exprt> flattened;
    collect_bitor_operands(expr, flattened);

    std::vector<exprt> unique;
    unique.reserve(flattened.size());

    for(const auto &op : flattened)
    {
      const bool already_seen = std::any_of(
        unique.begin(),
        unique.end(),
        [&](const exprt &existing) { return existing == op; });
      if(!already_seen)
        unique.push_back(op);
    }

    if(unique.empty())
      return;

    if(unique.size() == 1)
    {
      expr = unique.front();
      return;
    }

    exprt rebuilt = unique.front();
    for(std::size_t i = 1; i < unique.size(); ++i)
      rebuilt = bitor_exprt(std::move(rebuilt), unique[i]);
    expr = std::move(rebuilt);
  }
}

struct hoisted_let_bindingt
{
  irep_idt identifier;
  typet type;
  exprt value;
};

struct hoisted_bindingt
{
  enum class kindt
  {
    EXPR,
    RANGE
  };

  kindt kind;
  irep_idt identifier;
  exprt value;
  typet result_type;
  typet source_type;
  std::size_t range_hi = 0;
  std::size_t range_lo = 0;
};

const hoisted_bindingt *find_hoisted_source_expr(
  const std::vector<hoisted_bindingt> &bindings,
  const exprt &value,
  const typet &type)
{
  for(auto it = bindings.rbegin(); it != bindings.rend(); ++it)
  {
    if(it->kind != hoisted_bindingt::kindt::EXPR)
      continue;

    if(it->value.type() != type || it->value != value)
      continue;

    if(id2string(it->identifier).rfind("__smt2c_src_", 0) != 0)
      continue;

    return &(*it);
  }

  return nullptr;
}

const hoisted_bindingt *find_hoisted_range(
  const std::vector<hoisted_bindingt> &bindings,
  const exprt &source,
  const typet &source_type,
  const typet &result_type,
  std::size_t range_hi,
  std::size_t range_lo)
{
  for(auto it = bindings.rbegin(); it != bindings.rend(); ++it)
  {
    if(it->kind != hoisted_bindingt::kindt::RANGE)
      continue;

    if(
      it->range_hi == range_hi && it->range_lo == range_lo &&
      it->source_type == source_type && it->result_type == result_type &&
      it->value == source)
      return &(*it);
  }

  return nullptr;
}

irep_idt fresh_identifier(
  const std::string &prefix,
  std::size_t &counter,
  std::set<std::string> &used_identifiers)
{
  while(true)
  {
    std::string candidate = prefix + std::to_string(counter++);
    if(used_identifiers.insert(candidate).second)
      return irep_idt(candidate);
  }
}

irep_idt fresh_preferred_identifier(
  const irep_idt &preferred,
  const std::string &fallback_prefix,
  std::size_t &counter,
  std::set<std::string> &used_identifiers)
{
  const std::string base = id2string(tweak_identifier(preferred));

  if(!base.empty() && used_identifiers.insert(base).second)
    return irep_idt(base);

  if(!base.empty())
  {
    while(true)
    {
      std::string candidate = base + "_" + std::to_string(counter++);
      if(used_identifiers.insert(candidate).second)
        return irep_idt(candidate);
    }
  }

  return fresh_identifier(fallback_prefix, counter, used_identifiers);
}

irep_idt fresh_let_identifier(
  const irep_idt &preferred,
  std::size_t &counter,
  std::set<std::string> &used_identifiers)
{
  return fresh_preferred_identifier(
    preferred,
    "__smt2c_let_",
    counter,
    used_identifiers);
}

exprt hoist_let_expressions(
  exprt expr,
  std::vector<hoisted_let_bindingt> &bindings,
  std::size_t &counter,
  std::set<std::string> &used_identifiers)
{
  if(expr.id() == ID_let)
  {
    auto let_expr = to_let_expr(expr);

    // Preserve SMT-LIB let semantics: values are evaluated in the outer scope.
    for(auto &value : let_expr.values())
      value = hoist_let_expressions(
        std::move(value),
        bindings,
        counter,
        used_identifiers);

    std::map<irep_idt, exprt> substitutions;

    for(std::size_t i = 0; i < let_expr.variables().size(); ++i)
    {
      const auto &bound_symbol = to_symbol_expr(let_expr.variables()[i]);
      const irep_idt fresh_id = fresh_let_identifier(
        bound_symbol.get_identifier(),
        counter,
        used_identifiers);
      symbol_exprt fresh_symbol(fresh_id, bound_symbol.type());

      substitutions.emplace(bound_symbol.get_identifier(), fresh_symbol);
      bindings.push_back(
        {fresh_id, bound_symbol.type(), std::move(let_expr.values()[i])});
    }

    exprt where = let_expr.where();
    if(!substitutions.empty())
    {
      if(auto substituted = substitute_symbols(substitutions, std::move(where)))
        where = std::move(*substituted);
    }

    return hoist_let_expressions(
      std::move(where),
      bindings,
      counter,
      used_identifiers);
  }

  for(auto &op : expr.operands())
    op = hoist_let_expressions(
      std::move(op),
      bindings,
      counter,
      used_identifiers);

  return expr;
}

exprt hoist_extract_expressions(
  exprt expr,
  std::vector<hoisted_bindingt> &bindings,
  std::size_t &counter,
  std::set<std::string> &used_identifiers)
{
  for(auto &op : expr.operands())
    op = hoist_extract_expressions(
      std::move(op),
      bindings,
      counter,
      used_identifiers);

  if(expr.id() != ID_extractbits && expr.id() != ID_extractbit)
    return expr;

  exprt source = expr.operands().front();
  typet source_type = source.type();

  if(source.id() != ID_symbol)
  {
    const auto *existing_source =
      find_hoisted_source_expr(bindings, source, source_type);
    if(existing_source != nullptr)
    {
      source = symbol_exprt(existing_source->identifier, source_type);
    }
    else
    {
      const irep_idt source_id =
        fresh_identifier("__smt2c_src_", counter, used_identifiers);
      bindings.push_back(
        {hoisted_bindingt::kindt::EXPR,
         source_id,
         std::move(source),
         source_type,
         typet(),
         0,
         0});
      source = symbol_exprt(source_id, source_type);
    }
  }

  std::size_t range_lo = 0;
  std::size_t range_hi = 0;

  if(expr.id() == ID_extractbits)
  {
    const auto &extract = to_extractbits_expr(expr);
    const auto lo_mp = numeric_cast<mp_integer>(extract.index());
    if(!lo_mp.has_value())
      return expr;
    range_lo = numeric_cast_v<std::size_t>(*lo_mp);
    const auto width = to_bitvector_type(extract.type()).get_width();
    range_hi = range_lo + width - 1;
  }
  else
  {
    const auto &extract = to_extractbit_expr(expr);
    const auto lo_mp = numeric_cast<mp_integer>(extract.index());
    if(!lo_mp.has_value())
      return expr;
    range_lo = numeric_cast_v<std::size_t>(*lo_mp);
    range_hi = range_lo;
  }

  const auto *existing_range =
    find_hoisted_range(
      bindings,
      source,
      source_type,
      expr.type(),
      range_hi,
      range_lo);
  if(existing_range != nullptr)
    return symbol_exprt(existing_range->identifier, expr.type());

  const irep_idt result_id =
    fresh_identifier("__smt2c_ext_", counter, used_identifiers);

  bindings.push_back(
    {hoisted_bindingt::kindt::RANGE,
     result_id,
     source,
     expr.type(),
     source_type,
     range_hi,
     range_lo});

  return symbol_exprt(result_id, expr.type());
}

std::string canonicalize_slice_bounds(const std::string &expr_c)
{
  static const std::regex slice_add_re(R"(\[(\d+)\s*\+\s*(\d+),\s*(\d+)\])");

  std::string result;
  auto begin = expr_c.cbegin();
  std::smatch match;

  while(std::regex_search(begin, expr_c.cend(), match, slice_add_re))
  {
    result.append(begin, match[0].first);

    const auto lhs = std::stoull(match[1].str());
    const auto rhs = std::stoull(match[2].str());
    result += "[" + std::to_string(lhs + rhs) + ", " + match[3].str() + "]";

    begin = match[0].second;
  }

  result.append(begin, expr_c.cend());
  return result;
}

bool collect_if_chain(
  const exprt &expr,
  std::vector<std::pair<exprt, exprt>> &branches,
  exprt &else_case)
{
  if(expr.id() != ID_if)
    return false;

  const exprt *cursor = &expr;
  while(cursor->id() == ID_if)
  {
    const auto &if_expr = to_if_expr(*cursor);
    branches.emplace_back(if_expr.cond(), if_expr.true_case());
    cursor = &if_expr.false_case();
  }

  else_case = *cursor;
  return true;
}

std::string range_cast_type(const typet &type)
{
  if(type.id() == ID_unsignedbv)
  {
    const auto width = to_unsignedbv_type(type).get_width();
    return "ap_uint<" + std::to_string(width) + '>';
  }

  if(type.id() == ID_signedbv)
  {
    const auto width = to_signedbv_type(type).get_width();
    return "ap_int<" + std::to_string(width) + '>';
  }

  return {};
}

void output_function(const define_fun_resultt &define_fun, std::ostream &out)
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  expr2c_configurationt configuration = expr2c_configurationt::default_configuration;

  // return type
  std::string return_type_c;
  if(define_fun.type.id() == ID_mathematical_function)
    return_type_c =
      type2c(to_mathematical_function_type(define_fun.type).codomain(), ns, configuration);
  else
    return_type_c = type2c(define_fun.type, ns, configuration);
  out << return_type_c;

  out << ' ';

  // name of function
  out << define_fun.id;

  // parameters, if any, or void
  out << '(';

  if(define_fun.type.id() == ID_mathematical_function)
  {
    auto &function_type = to_mathematical_function_type(define_fun.type);
    for(std::size_t index = 0; index < function_type.domain().size(); index++)
    {
      if(index != 0)
        out << ", ";
      out << type2c(function_type.domain()[index], ns, configuration);
      out << ' ';
      auto parameter_name = tweak_identifier(define_fun.parameters[index]);
      out << parameter_name;
    }
  }
  else
    out << "void";

  out << ')';

  // body
  exprt body_tweaked = tweak_symbols(define_fun.body);
  normalize_for_c_output(body_tweaked);
  simplify_for_readability(body_tweaked);

  std::set<std::string> used_identifiers;
  for(const auto &param : define_fun.parameters)
    used_identifiers.insert(id2string(tweak_identifier(param)));

  std::vector<hoisted_let_bindingt> let_bindings;
  std::size_t temp_counter = 0;
  body_tweaked = hoist_let_expressions(
    std::move(body_tweaked),
    let_bindings,
    temp_counter,
    used_identifiers);

  std::vector<hoisted_bindingt> bindings;
  bindings.reserve(let_bindings.size());

  for(const auto &let_binding : let_bindings)
  {
    exprt let_value = hoist_extract_expressions(
      let_binding.value,
      bindings,
      temp_counter,
      used_identifiers);

    bindings.push_back(
      {hoisted_bindingt::kindt::EXPR,
       let_binding.identifier,
       std::move(let_value),
       let_binding.type,
       typet(),
       0,
       0});
  }

  body_tweaked = hoist_extract_expressions(
    std::move(body_tweaked),
    bindings,
    temp_counter,
    used_identifiers);

  std::string body_c = canonicalize_slice_bounds(expr2c(body_tweaked, ns, configuration));

  out << " {\n";
  for(const auto &binding : bindings)
  {
    std::string value_c;

    if(binding.kind == hoisted_bindingt::kindt::RANGE)
    {
      std::string source_c =
        canonicalize_slice_bounds(expr2c(binding.value, ns, configuration));

      const std::string cast_type = range_cast_type(binding.source_type);
      if(cast_type.empty())
      {
        value_c = source_c;
      }
      else
      {
        value_c =
          "((" + cast_type + ")" + source_c + ").range(" +
          std::to_string(binding.range_hi) + ", " +
          std::to_string(binding.range_lo) + ")";
      }

      out << "  " << type2c(binding.result_type, ns, configuration) << " "
          << tweak_identifier(binding.identifier) << " = " << value_c << ";\n";
    }
    else
    {
      value_c = canonicalize_slice_bounds(expr2c(binding.value, ns, configuration));
      if(!binding.result_type.is_nil())
      {
        out << "  " << type2c(binding.result_type, ns, configuration) << " "
            << tweak_identifier(binding.identifier) << " = " << value_c
            << ";\n";
      }
      else
      {
        out << "  auto " << tweak_identifier(binding.identifier) << " = " << value_c
            << ";\n";
      }
    }
  }
  std::vector<std::pair<exprt, exprt>> if_chain;
  exprt else_case;
  const bool has_if_chain = collect_if_chain(body_tweaked, if_chain, else_case);
  if(has_if_chain && if_chain.size() >= 2)
  {
    out << "  " << return_type_c << " __smt2c_result;\n";
    for(std::size_t i = 0; i < if_chain.size(); ++i)
    {
      const std::string cond_c =
        canonicalize_slice_bounds(expr2c(if_chain[i].first, ns, configuration));
      const std::string value_chain_c =
        canonicalize_slice_bounds(expr2c(if_chain[i].second, ns, configuration));

      if(i == 0)
        out << "  if(" << cond_c << ") {\n";
      else
        out << "  else if(" << cond_c << ") {\n";
      out << "    __smt2c_result = " << value_chain_c << ";\n";
      out << "  }\n";
    }

    const std::string else_c =
      canonicalize_slice_bounds(expr2c(else_case, ns, configuration));
    out << "  else {\n";
    out << "    __smt2c_result = " << else_c << ";\n";
    out << "  }\n";
    out << "  return __smt2c_result;\n";
  }
  else
  {
    out << "  return " << body_c << ";\n";
  }
  out << "}\n\n";
}

int main(int argc, const char *argv[])
{
  cmdlinet cmdline;
  if(cmdline.parse(argc, argv, CBMC_ORACLE_OPTIONS))
  {
    std::cerr << "Usage error\n";
    help(std::cerr);
    return 1;
  }

  if(cmdline.isset("help") || cmdline.isset("h") || cmdline.isset("?"))
  {
    help(std::cout);
    return 1;
  }

  try
  {
    config.set(cmdline);
    
    // NEW: running environment of known functions
    std::vector<std::pair<irep_idt, typet>> env;

    for(const auto &arg : cmdline.args)
    {
      std::istringstream arg_stream(arg);

      // pass previously seen functions to the parser
      auto def = define_fun_parser(arg_stream, env);

      // emit C for this function
      output_function(def, std::cout);

      // make this one available to subsequent definitions
      env.emplace_back(def.id, def.type);
    }
  }
  catch(const cprover_exception_baset &error)
  {
    std::cerr << "Error: " << error.what() << '\n';
  }
  catch(const char *s)
  {
    std::cerr << "Error: " << s << '\n';
  }
  catch(const std::string &s)
  {
    std::cerr << "Error: " << s << '\n';
  }
}
