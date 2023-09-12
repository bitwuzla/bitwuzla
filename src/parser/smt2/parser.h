/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PARSER_SMT2_PARSER_H_INCLUDED
#define BZLA_PARSER_SMT2_PARSER_H_INCLUDED

#include "backtrack/vector.h"
#include "parser/parser.h"
#include "parser/smt2/lexer.h"
#include "parser/smt2/symbol_table.h"

namespace bzla {
namespace parser::smt2 {

class Parser : public bzla::parser::Parser
{
 public:
  /**
   * Constructor.
   * @param options     The associated Bitwuzla options. Parser creates
   *                    Bitwuzla instance from these options.
   * @param infile_name The name of the input file.
   * @param out         The output stream.
   */
  Parser(bitwuzla::Options& options,
         const std::string& infile_name,
         std::ostream* out = &std::cout);
  /**
   * Constructor.
   * @param options     The associated Bitwuzla options. Parser creates
   *                    Bitwuzla instance from these options.
   * @param infile_name The name of the input file.
   * @param infile      The input file.
   * @param out         The output stream.
   */
  Parser(bitwuzla::Options& options,
         const std::string& infile_name,
         FILE* infile,
         std::ostream* out = &std::cout);

  std::string parse(bool parse_only) override;

 private:
  /** A parsed item. */
  struct ParsedItem
  {
    /** Constructor. */
    ParsedItem() {}
    /**
     * Constructor.
     * @param token The token of the item, doubles as kind.
     * @param coo   The coordinate of the item in the input file.
     */
    ParsedItem(Token token, const Lexer::Coordinate& coo)
        : d_token(token), d_coo(coo)
    {
    }
    /**
     * Constructor.
     * @param token The token of the item, doubles as kind.
     * @param T     The actual object this item represents, may be a symbol
     *              node, a sort or a term.
     * @param coo   The coordinate of the item in the input file.
     */
    template <typename T>
    ParsedItem(Token token, T item, const Lexer::Coordinate& coo)
        : d_token(token), d_coo(coo), d_item(item)
    {
    }
    /** The token of this item, doubles as kind. */
    Token d_token;
    /** The coordinate in the input file of this item. */
    Lexer::Coordinate d_coo;
    /** The associated object. */
    std::variant<SymbolTable::Node*, bitwuzla::Sort, bitwuzla::Term> d_item;
    /** Cache for the indices of an open (indexed) term item. */
    std::vector<uint64_t> d_uints;
    /** The coordinates associated with the indices in the index cache. */
    std::vector<Lexer::Coordinate> d_uints_coo;
    /** Cache for strings (representing values) of an open term item. */
    std::vector<std::string> d_strs;
    /** The coordinates associated with the strings in the string cache. */
    std::vector<Lexer::Coordinate> d_strs_coo;
    /**
     * True if this open item is a to_fp from rational conversion term.
     * Needed to be able to determine how many strings we require to be cached.
     */
    bool d_from_rational = false;
  };

  /** Initialize logic. */
  void init_logic()
  {
    if (d_logic.empty())
    {
      enable_theory("ALL");
    }
  }

  /**
   * Get next token from the lexer and insert new symbols into symbol table.
   * Caches parsed symbols (new and existing) in d_last_node.
   * @param insert     True if parsed symbol is to be inserted in the symbol
   *                   table. This will always be the case except when parsing
   *                   sorted vars of a let binding.
   * @return The next token.
   */
  Token next_token(bool insert = true)
  {
    assert(d_lexer);
    Token token = d_lexer->next_token();
    if (token == Token::SYMBOL || token == Token::ATTRIBUTE)
    {
      assert(d_lexer->has_token());
      std::string symbol      = d_lexer->token();
      SymbolTable::Node* node = d_table.find(symbol);
      if (!node)
      {
        if (insert)
        {
          node = d_table.insert(token, symbol, d_assertion_level);
        }
        else
        {
          node = new SymbolTable::Node(token, symbol, d_assertion_level);
        }
      }
      d_last_node = node;
      token       = d_last_node->d_token;
    }
    if (d_save_repr)
    {
      d_repr +=
          (d_repr.size() && d_repr.back() != '(' && token != Token::RPAR ? " "
                                                                         : "")
          + std::string(d_lexer->token());
    }
    return token;
  }

  /**
   * Parse command.
   * @param parse_only True to only parse without executing check-sat calls.
   * @return True if command was parsed without an error.
   */
  bool parse_command(bool parse_only);
  /**
   * Parse assert command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_assert();
  /**
   * Parse check-sat or check-sat-assuming command.
   * @param parse_only True to only parse without executing check-sat calls.
   * @param with_assumptions True if command is a check-sat-assuming command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_check_sat(bool parse_only, bool with_assumptions = false);
  /**
   * Parse declare-sort command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_declare_sort();
  /**
   * Parse declare-fun or declare-const command.
   * @param is_const True if command is a declare-const command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_declare_fun(bool is_const = false);
  /**
   * Parse define-fun command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_define_fun();
  /**
   * Parse define-sort command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_define_sort();
  /**
   * Parse echo command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_echo();
  /**
   * Parse exit command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_exit();
  /**
   * Parse get-model command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_get_model();
  /**
   * Parse get-unsat-assumptions command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_get_unsat_assumptions();
  /**
   * Parse get-unsat-core command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_get_unsat_core();
  /**
   * Parse get-value command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_get_value();
  /**
   * Parse pop command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_pop();
  /**
   * Parse push command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_push();
  /**
   * Parse reset command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_reset();
  /**
   * Parse reset-assertions command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_reset_assertions();
  /**
   * Parse set-info command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_set_info();
  /**
   * Parse set-logic command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_set_logic();
  /**
   * Parse set-option command.
   * @return True if command was parsed without an error.
   */
  bool parse_command_set_option();

  /**
   * Parse left parenthesis.
   * @return False if next token is not a '('.
   */
  bool parse_lpar()
  {
    if (next_token() != Token::LPAR)
    {
      return error("missing '('");
    }
    return true;
  }
  /**
   * Parse right parenthesis.
   * @return False if next token is not a ')'.
   */
  bool parse_rpar()
  {
    if (next_token() != Token::RPAR)
    {
      return error("missing ')'");
    }
    return true;
  }

  /**
   * Parse unsigned 64 bit integer.
   * @param uint Stores the resulting integer.
   * @return False on error.
   */
  bool parse_uint64(uint64_t& uint);

  /**
   * Parse symbol.
   * @param error_msg  A message indicating where the symbol was expected,
   *                   e.g., "after declare-const".
   * @param shadow     True if parsed symbol may shadow an existing symbol.
   * @param insert     True if parsed symbol is to be inserted in the symbol
   *                   table. This will always be the case except when parsing
   *                   sorted vars of a let binding.
   * @param look_ahead True if we have a look ahead token.
   * @param la         The look ahead token.
   * @return False on error.
   */
  bool parse_symbol(const std::string& error_msg,
                    bool shadow     = false,
                    bool insert     = true,
                    bool look_ahead = false,
                    Token la        = Token::INVALID);

  /**
   * Parse term.
   * @param look_ahead True if we have a look ahead token.
   * @param la         The look ahead token.
   * @return False on error.
   */
  bool parse_term(bool look_ahead = false, Token la_char = Token::INVALID);
  /**
   * Parse list of terms.
   * @param repr The resulting list of terms.
   * @return False on error.
   */
  bool parse_term_list(std::vector<bitwuzla::Term>& terms,
                       std::vector<std::string>* repr = nullptr);
  /**
   * Helper for parse_term, parse currently open term.
   */
  bool parse_open_term(Token token);
  /**
   * Helper for parse_open_term, parse currently open (as ...) term.
   * @return False on error.
   */
  bool parse_open_term_as();
  /**
   * Helper for parse_open_term, parse currently open indexed term.
   * @return False on error.
   */
  bool parse_open_term_indexed();
  /**
   * Helper for parse_open_term, parse currently open quantified term.
   * @return False on error.
   */
  bool parse_open_term_quant();
  /**
   * Helper for parse_open_term, parse currently open symbol term.
   * @return False on error.
   */
  bool parse_open_term_symbol();

  /**
   * Parse sort.
   * @param sort       The resulting sort.
   * @param look_ahead True if we have a look ahead token.
   * @param la         The look ahead token.
   * @return False on error.
   */
  bool parse_sort(bitwuzla::Sort& sort,
                  bool look_ahead = false,
                  Token la_char   = Token::INVALID);
  /**
   * Helper for parse_sort, parse array sort.
   * @param sort The resulting sort.
   * @return False on error.
   */
  bool parse_sort_array(bitwuzla::Sort& sort);
  /**
   * Helper for parse_sort, parse bit-vector or floating-point sort.
   * @param sort The resulting sort.
   * @return False on error.
   */
  bool parse_sort_bv_fp(bitwuzla::Sort& sort);

  /**
   * Close currently open term.
   * @return False on error.
   */
  bool close_term();
  /**
   * Helper for close_term, close currently open (as ...) term.
   * @param item_open The currently open item.
   * @return False on error.
   */
  bool close_term_as(ParsedItem& item_open);
  /**
   * Helper for close_term, close currently open (! ...) term.
   * @param item_open The currently open item.
   * @return False on error.
   */
  bool close_term_bang(ParsedItem& item_open);
  /**
   * Helper for close_term, close currently open core theory term.
   * @param item_open The currently open item.
   * @return False on error.
   */
  bool close_term_core(ParsedItem& item_open);
  /**
   * Helper for close_term, close currently open array theory term.
   * @param item_open The currently open item.
   * @return False on error.
   */
  bool close_term_array(ParsedItem& item_open);
  /**
   * Helper for close_term, close currently open bit-vector theory term.
   * @param item_open The currently open item.
   * @return False on error.
   */
  bool close_term_bv(ParsedItem& item_open);
  /**
   * Helper for close_term, close currently open floating-point theory term.
   * @param item_open The currently open item.
   * @return False on error.
   */
  bool close_term_fp(ParsedItem& item_open);
  /**
   * Helper for close_term, close currently open function application term.
   * @param item_open The currently open item.
   * @return False on error.
   */
  bool close_term_fun_app(ParsedItem& item_open);
  /**
   * Helper for close_term, close currently open let term.
   * @param item_open The currently open item.
   * @return False on error.
   */
  bool close_term_let(ParsedItem& item_open);
  /**
   * Helper for close_term, close currently open let binding.
   * @param item_open The currently open item.
   * @return False on error.
   */
  bool close_term_letbind(ParsedItem& item_open);
  /**
   * Helper for close_term, close currently open list of let bindings.
   * @param item_open The currently open item.
   * @return False on error.
   */
  bool close_term_parletbind(ParsedItem& item_open);
  /**
   * Helper for close_term, close currently open quantified term.
   * @param item_open The currently open item.
   * @return False on error.
   */
  bool close_term_quant(ParsedItem& item_open);
  /**
   * Helper for close_term, close currently open sorted variable.
   * @param item_open The currently open item.
   * @return False on error.
   */
  bool close_term_sorted_var(ParsedItem& item_open);
  /**
   * Helper for close_term, close currently open list of sorted variable.
   * @param item_open The currently open item.
   * @return False on error.
   */
  bool close_term_sorted_vars(ParsedItem& item_open);

  /**
   * Open new term scope.
   * Pushes an intermediate Token::OPEN item onto to work stack, which is then
   * replaced but the actual item that is currently open.
   * Further, pushes index of currently open item onto work control stack.
   */
  void open_term_scope();
  /**
   * Close term scope and, if given, saves term argument (as argument, in place
   * of the opening '(') on the work stack.
   * @param term Saved as argument on the work stack, if given.
   */
  void close_term_scope(
      const std::optional<bitwuzla::Term>& term = std::nullopt);

  /**
   * Skip the given number of s-expressions.
   * @param nopen The number of open s-expressions to skip.
   * @return False on error.
   */
  bool skip_sexprs(uint64_t nopen = 0);

  /**
   * Set error message and error coordinate.
   * @param error_msg The error message.
   * @param coo       The error coordinate. Set to the current coordinate of
   *                  the lexer if not given.
   * @return Always returns false to allow using the result of this function
   *         call to indicate a parse error.
   */
  bool error(const std::string& error_msg,
             const std::optional<Lexer::Coordinate>& coo = std::nullopt);
  /**
   * Helper to set error message with the coordinate of the current item
   * on the work stack as error coordinate. Used for errors concerning
   * term arguments.
   * @param error_msg The error message.
   * @return Always returns false to allow using the result of this function
   *         call to indicate a parse error.
   */
  bool error_arg(const std::string& error_msg);
  /**
   * Set error message and coordinate for errors where the current token is
   * invalid.
   * @return Always returns false to allow using the result of this function
   *         call to indicate a parse error.
   */
  bool error_invalid();
  /**
   * Set error message and coordinate for errors where the current token is
   * the end-of-file token.
   * @return Always returns false to allow using the result of this function
   *         call to indicate a parse error.
   */
  bool error_eof();

  /**
   * Check if the given token is an invalid of eof token and set error message
   * and coordinate on error.
   * @return False on error.
   */
  bool check_token(Token token)
  {
    if (token == Token::ENDOFFILE)
    {
      return error_eof();
    }
    if (token == Token::INVALID)
    {
      return error_invalid();
    }
    return true;
  }

  /** @return True if the given token is a symbol token. */
  bool is_symbol(Token token) const
  {
    return token == Token::SYMBOL || token == Token::ATTRIBUTE
           || (static_cast<uint32_t>(token) & d_token_class_mask) > 0;
  }

  /**
   * Helper for is_supported_logic, enables theory support for a given logic.
   *
   * If given theory is enabled in the logic is checked while skipping
   * 'size_prefix' characters, e.g., enable_theory("QF_ABV", "A", n) assumes
   * that n = 3 to skip "QF_" to check for "A".
   *
   * @param logic  The logic string, "ALL" to enable all theories.
   * @param theory The theory to enable if included in the logic. Quantifiers
   *               are not enabled if theory is "QF_".
   * @param size_prefix The size of the prefix to skip in the logic.
   * @return The size of the currently checked prefix, size_prefix +
   *         len(theory) if theory appears in the logic, else size_prefix.
   */
  size_t enable_theory(const std::string& logic,
                       const std::string& theory = "",
                       size_t size_prefix        = 0);
  /**
   * Check if given logic is supported and enable included theories and
   * quantifiers according to the logic.
   * @param logic The logic string.
   * @return False if logic is not supported.
   */
  bool is_supported_logic(const std::string& logic);

  /** Print "success" if option print-success is enabled. */
  void print_success();

  /** @return The number of arguments of an open term on the work stack. */
  size_t nargs() const
  {
    assert(idx_open() < d_work.size());
    return d_work.size() - idx_open() - 1;
  }
  /** @return The number of open items. */
  size_t nopen() const { return d_work_control.size() - 1; }
  /** @return The index of the currently open item. */
  size_t idx_open() const { return d_work_control.back(); }
  /** @return The index of the open term enclosing the currently open item. */
  size_t idx_prev() const
  {
    assert(d_work_control.size() > 1);
    return d_work_control[d_work_control.size() - 2];
  }
  /** @return The currently open item. */
  ParsedItem& item_open()
  {
    assert(idx_open() < d_work.size());
    return d_work[idx_open()];
  }
  /** @return The open item that encloses the currently open item. */
  ParsedItem& item_prev()
  {
    assert(idx_prev() < d_work.size());
    return d_work[idx_prev()];
  }

  /**
   * Get the coordinate of the item on the work stack at the given index.
   * @param idx The index on the work stack.
   * @return The coordinate.
   */
  const Lexer::Coordinate& arg_coo(size_t idx) const;

  /**
   * Push a new item on the work stack.
   * @param token The token of the item.
   * @param coo   The coordinate of the item.
   * @return The item.
   */
  ParsedItem& push_item(Token token, const Lexer::Coordinate& coo)
  {
    if (peek_item_is_token(Token::OPEN))
    {
      set_item(d_work.back(), token, coo);
    }
    else
    {
      d_work.emplace_back(token, coo);
    }
    return d_work.back();
  }
  /**
   * Push a new item on the work stack.
   * @param token The token of the item.
   * @param T     The associated item object, may be symbol node, sort, or term.
   * @param coo   The coordinate of the item.
   * @return The item.
   */
  template <typename T>
  ParsedItem& push_item(Token token, T item, const Lexer::Coordinate& coo)
  {
    if (peek_item_is_token(Token::OPEN))
    {
      set_item(d_work.back(), token, item, coo);
    }
    else
    {
      d_work.emplace_back(token, item, coo);
    }
    return d_work.back();
  }

  /** @return True if the top item on the work stack has the given token. */
  bool peek_item_is_token(Token token) const
  {
    return d_work.size() && d_work.back().d_token == token;
  }
  /**
   * @return True if the item at the given index on the work stack has the
   *         given token.
   */
  bool peek_item_is_token(Token token, size_t idx) const
  {
    return idx < d_work.size() && d_work[idx].d_token == token;
  }

  /**
   * Set the token and coordinate of the given iterm.
   * @param item  The item.
   * @param token The token to set.
   * @param coo   The coordinate to set.
   */
  void set_item(ParsedItem& item, Token token, const Lexer::Coordinate& coo)
  {
    item.d_token = token;
    item.d_coo   = coo;
  }
  /**
   * Set the token, associated object and coordinate of the given iterm.
   * @param item  The item.
   * @param token The token to set.
   * @param T     The associated object.
   * @param coo   The coordinate to set.
   */
  template <typename T>
  void set_item(ParsedItem& item,
                Token token,
                T t,
                const std::optional<Lexer::Coordinate>& coo = std::nullopt)
  {
    item.d_token = token;
    item.d_item  = t;
    if (coo)
    {
      d_work.back().d_coo = *coo;
    }
  }

  /**
   * Pop top term item from the work stack.
   * Asserts that the top item on the work stack is a Token::TERM item.
   * @return The associated term of the popped TERM item.
   */
  bitwuzla::Term pop_term_arg();
  /**
   * Pop top symbol node item from the work stack.
   * Asserts that the top item on the work stack is a Token::SYMBOL item.
   * @param set_coo True to set the coordinate of the symbol node to the
   *                coordinate of the popped item.
   * @return The associated symbol node of the popped SYMBOL item.
   */
  SymbolTable::Node* pop_node_arg(bool set_coo = false);

  /**
   * Get the associated term of the top term item from the work stack.
   * Asserts that the top item on the work stack is a Token::TERM item.
   * @return The associated term of the top TERM item.
   */
  const bitwuzla::Term& peek_term_arg() const
  {
    assert(peek_is_term_arg());
    return std::get<bitwuzla::Term>(d_work.back().d_item);
  }
  /**
   * Get the associated symbol node of the top node item from the work stack.
   * Asserts that the top item on the work stack is a Token::SYMBOL item.
   * @return The associated symbol node of the top SYMBOL item.
   */
  SymbolTable::Node* peek_node_arg() const
  {
    assert(peek_is_node_arg());
    return std::get<SymbolTable::Node*>(d_work.back().d_item);
  }
  /**
   * Get the associated term of the item at the given index on the work stack.
   * Asserts that the item at the given index is a Token::TERM item.
   * @param idx The index on the work stack.
   * @return The associated term.
   */
  const bitwuzla::Term& peek_term_arg(size_t idx) const
  {
    assert(peek_is_term_arg(idx));
    return std::get<bitwuzla::Term>(d_work[idx].d_item);
  }
  /**
   * Get the associated symbol node of the item at the given index on the work
   * stack. Asserts that the item at the given index is a Token::SYMBOL item.
   * @param idx The index on the work stack.
   * @return The associated symbol node.
   */
  SymbolTable::Node* peek_node_arg(size_t idx) const
  {
    assert(peek_is_node_arg(idx));
    return std::get<SymbolTable::Node*>(d_work[idx].d_item);
  }

  /** @return True if the top item on the work stack is a term. */
  bool peek_is_term_arg() const
  {
    assert(
        d_work.size()
        && (d_work.back().d_token != Token::TERM
            || std::holds_alternative<bitwuzla::Term>(d_work.back().d_item)));
    return d_work.back().d_token == Token::TERM;
  }
  /** @return True if the item at a given index on the work stack is a term. */
  bool peek_is_term_arg(size_t idx) const
  {
    assert(idx > d_work.size() || d_work[idx].d_token != Token::TERM
           || std::holds_alternative<bitwuzla::Term>(d_work[idx].d_item));
    return idx < d_work.size() && d_work[idx].d_token == Token::TERM;
  }
  /** @return True if the top item on the work stack is a symbol node. */
  bool peek_is_node_arg() const
  {
    assert(d_work.size()
           && (d_work.back().d_token != Token::SYMBOL
               || std::holds_alternative<SymbolTable::Node*>(
                   d_work.back().d_item)));
    return d_work.back().d_token == Token::SYMBOL;
  }
  /**
   * @return True if the item at a given index on the work stack is a symbol
   * node.
   */
  bool peek_is_node_arg(size_t idx) const
  {
    assert(idx > d_work.size() || d_work[idx].d_token != Token::SYMBOL
           || std::holds_alternative<SymbolTable::Node*>(d_work[idx].d_item));
    return idx < d_work.size() && d_work[idx].d_token == Token::SYMBOL;
  }

  /**
   * Helper to check and pop the arguments of an open term item.
   * @note Associated indices and strings (representing values) are cached
   *       in the open item.
   * @param item_open The open term item.
   * @param args      The popped term arguments.
   */
  bool pop_args(const ParsedItem& item_open, std::vector<bitwuzla::Term>& args);

#ifndef NDEBUG
  /** Print contents of work stack. */
  void print_work_stack();
  /** Print contents of work control stack. */
  void print_work_control_stack();
#endif

  /** The associated SMT-LIB2 lexer. */
  std::unique_ptr<Lexer> d_lexer;
  /** The associated symbol table. */
  SymbolTable d_table;

  /** True if SMT-LIB option print-success is enabled. */
  bool d_print_success = false;
  /** True if SMT-LIB option global-declarations is enabled. */
  bool d_global_decl = false;
  /** True if input file contains arrays. */
  bool d_arrays_enabled = false;
  /** True if input file contains bit-vectors. */
  bool d_bv_enabled     = false;
  /** True if input file contains floating-point arithmetic. */
  bool d_fp_enabled     = false;
  /** The enabled logic. */
  std::string d_logic;

  /** The current assertion level. */
  uint64_t d_assertion_level = 0;

  /** Cache declared symbols for get-model. */
  backtrack::vector<SymbolTable::Node*> d_decls;

  /** The work stack. */
  std::vector<ParsedItem> d_work;
  /**
   * The control stack for the work stack, maintains the start indices of open
   * parsed items.
   */
  std::vector<uint64_t> d_work_control;

  /**
   * The mask for enabled token classes (including currently enabled theory
   * token classes).
   */
  uint64_t d_token_class_mask = 0;

  /** True if currently open term expects a body term. */
  bool d_expect_body    = false;
  /** True if currently open term is a sorted variable. */
  bool d_is_sorted_var  = false;
  /** True if currently open term is a variable binding. */
  bool d_is_var_binding = false;

  /**
   * True to ignore any undefined symbols when parsing unsupported attribute
   * values of unsupported annotation attributes.
   */
  bool d_skip_attribute_value = false;

  /** The most recently parsed symbol node. */
  SymbolTable::Node* d_last_node = nullptr;

  /** True to record the string representation of parsed input into d_repr. */
  bool d_save_repr = false;
  /** The string representation of input parsed while d_save_repr was true. */
  std::string d_repr;

  /**
   * Flag indicating if on parsing (! ... :named ...), the named term should
   * be recorded in d_named_assertions.
   */
  bool d_record_named_assertions = false;
  /** A map from annotated (:named) assertions to their named symbol. */
  std::unordered_map<bitwuzla::Term, SymbolTable::Node*> d_named_assertions;

  /** The set of currently active assumptions. */
  std::unordered_map<bitwuzla::Term, std::string> d_assumptions;

  /** Parse statistics. */
  struct Statistics
  {
    Statistics();

    util::Statistics d_stats;

    /** The number of assert commands. */
    uint64_t& num_assertions;
    /** The number of check-sat(-assuming) commands. */
    uint64_t& num_check_sat;
    /** The overall number of commands. */
    uint64_t& num_commands;
    /** The number of exit commands. */
    uint64_t& num_exit;
    /** The number of set-logic commands. */
    uint64_t& num_set_logic;

    /**
     * The time required for parsing.
     * @note This is not parse-only, it includes time for any calls to the
     *       solver (check-sat, get-model, ...).
     */
    util::TimerStatistic& time_parse;

  } d_statistics;
};
}  // namespace parser::smt2
}  // namespace bzla

#endif
