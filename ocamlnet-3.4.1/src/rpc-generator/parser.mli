type token =
  | LBRACKET
  | RBRACKET
  | LANGLE
  | RANGLE
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | STAR
  | COMMA
  | SEMICOLON
  | COLON
  | EQUAL
  | MAPSTO
  | IDENT of (string)
  | INTLITERAL of (string)
  | K_opaque
  | K_string
  | K_void
  | K_unsigned
  | K_int
  | K_hyper
  | K_float
  | K_double
  | K_quadruple
  | K_bool
  | K_enum
  | K_struct
  | K_union
  | K_switch
  | K_case
  | K_default
  | K_const
  | K_typedef
  | K_program
  | K_version
  | K_int32
  | K_int64
  | K_unboxed
  | K_abstract
  | K_managed
  | IGNORE
  | PERCENT
  | LINEFEED of (int*int)
  | SETFILE of (int*string)
  | EOF

val specification :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Syntax.xdr_def list
