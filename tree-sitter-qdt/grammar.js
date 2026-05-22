/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

/**
 * @param {RuleOrLiteral} rule
 * @param {RuleOrLiteral} sep
 */
function sep1(rule, sep) {
  return seq(rule, repeat(seq(sep, rule)));
}

export default grammar({
  name: "qdt",

  extras: ($) => [/[ \t\r\n]+/, $.line_comment, $.block_comment],

  word: ($) => $._ident_word,

  rules: {
    source_file: ($) => repeat($._top),

    line_comment: (_) => token(seq("--", /[^\n]*/)),

    block_comment: (_) =>
      token(seq("/-", repeat(choice(/[^-]/, /-[^\/]/)), /-+\//)),

    _top: ($) =>
      choice(
        $.import,
        $.definition,
        $.example,
        $.axiom,
        $.inductive,
        $.structure,
      ),

    import: ($) => seq("import", field("name", $.identifier)),

    definition: ($) =>
      seq(
        "def",
        field("name", $.identifier),
        optional($.univ_params),
        repeat($._term_token),
      ),

    example: ($) => seq("example", repeat($._term_token)),

    axiom: ($) =>
      seq(
        "axiom",
        field("name", $.identifier),
        optional($.univ_params),
        repeat($._term_token),
      ),

    inductive: ($) =>
      seq(
        "inductive",
        field("name", $.identifier),
        optional($.univ_params),
        repeat($._term_token_no_pipe),
        repeat($.ctor),
      ),

    ctor: ($) =>
      seq("|", field("name", $.identifier), repeat($._term_token_no_pipe)),

    structure: ($) =>
      seq(
        "structure",
        field("name", $.identifier),
        optional($.univ_params),
        repeat($._term_token),
      ),

    univ_params: ($) =>
      prec(
        2,
        seq($._dotbrace, sep1(alias($.identifier, $.univ_param), ","), "}"),
      ),

    univ_args: ($) => prec(1, seq($._dotbrace, sep1($._level, ","), "}")),

    _level: ($) =>
      choice(
        $.number,
        $.identifier,
        prec.left(seq("max", repeat1($._level))),
        seq("(", $._level, ")"),
      ),

    _dotbrace: (_) => token(prec(1, ".{")),

    _term_token: ($) =>
      choice(
        $.identifier,
        $.number,
        $.univ_args,
        $._term_keyword,
        $._operator,
        $.paren_group,
        $.brace_group,
      ),

    _term_token_no_pipe: ($) =>
      choice(
        $.identifier,
        $.number,
        $.univ_args,
        $._term_keyword,
        $._operator_no_pipe,
        $.paren_group,
        $.brace_group,
      ),

    _term_keyword: (_) => choice("fun", "let", "sorry", "Type", "where", "max"),

    _operator: (_) =>
      choice("->", "→", "=>", "⇒", ":=", "=", "+", ":", ";", ",", "|", "_"),

    _operator_no_pipe: (_) =>
      choice("->", "→", "=>", "⇒", ":=", "=", "+", ":", ";", ",", "_"),

    paren_group: ($) => seq("(", repeat($._term_token), ")"),
    brace_group: ($) => seq("{", repeat($._term_token), "}"),

    number: (_) => /\d+/,

    identifier: (_) =>
      token(
        seq(
          /[\p{L}_][\p{L}\p{N}_']*/,
          repeat(seq(".", /[\p{L}_][\p{L}\p{N}_']*/)),
        ),
      ),

    _ident_word: (_) => /[\p{L}_][\p{L}\p{N}_']*/,
  },
});
