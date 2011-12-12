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

open Parsing;;
# 2 "parser.mly"

(* $Id: parser.mly 1444 2010-04-25 23:14:52Z gerd $
 *)

  open Syntax

# 58 "parser.ml"
let yytransl_const = [|
  257 (* LBRACKET *);
  258 (* RBRACKET *);
  259 (* LANGLE *);
  260 (* RANGLE *);
  261 (* LPAREN *);
  262 (* RPAREN *);
  263 (* LBRACE *);
  264 (* RBRACE *);
  265 (* STAR *);
  266 (* COMMA *);
  267 (* SEMICOLON *);
  268 (* COLON *);
  269 (* EQUAL *);
  270 (* MAPSTO *);
  273 (* K_opaque *);
  274 (* K_string *);
  275 (* K_void *);
  276 (* K_unsigned *);
  277 (* K_int *);
  278 (* K_hyper *);
  279 (* K_float *);
  280 (* K_double *);
  281 (* K_quadruple *);
  282 (* K_bool *);
  283 (* K_enum *);
  284 (* K_struct *);
  285 (* K_union *);
  286 (* K_switch *);
  287 (* K_case *);
  288 (* K_default *);
  289 (* K_const *);
  290 (* K_typedef *);
  291 (* K_program *);
  292 (* K_version *);
  293 (* K_int32 *);
  294 (* K_int64 *);
  295 (* K_unboxed *);
  296 (* K_abstract *);
  297 (* K_managed *);
  298 (* IGNORE *);
  299 (* PERCENT *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  271 (* IDENT *);
  272 (* INTLITERAL *);
  300 (* LINEFEED *);
  301 (* SETFILE *);
    0|]

let yylhs = "\255\255\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\006\000\006\000\005\000\005\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\009\000\009\000\009\000\009\000\009\000\009\000\009\000\009\000\
\009\000\010\000\010\000\013\000\014\000\014\000\011\000\011\000\
\015\000\016\000\016\000\012\000\012\000\017\000\018\000\018\000\
\020\000\020\000\021\000\021\000\019\000\019\000\022\000\023\000\
\023\000\023\000\023\000\024\000\025\000\025\000\026\000\027\000\
\027\000\028\000\029\000\029\000\031\000\031\000\030\000\030\000\
\032\000\032\000\032\000\001\000\001\000\008\000\004\000\004\000\
\007\000\000\000"

let yylen = "\002\000\
\002\000\005\000\005\000\005\000\005\000\005\000\006\000\003\000\
\001\000\001\000\000\000\001\000\001\000\002\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\003\000\003\000\005\000\002\000\002\000\
\003\000\002\000\003\000\002\000\002\000\008\000\003\000\004\000\
\004\000\005\000\002\000\000\000\004\000\000\000\005\000\003\000\
\004\000\004\000\004\000\008\000\001\000\002\000\008\000\001\000\
\002\000\008\000\001\000\001\000\001\000\003\000\001\000\001\000\
\001\000\001\000\001\000\002\000\001\000\001\000\001\000\003\000\
\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\077\000\082\000\074\000\073\000\075\000\000\000\000\000\000\000\
\000\000\000\000\000\000\078\000\000\000\000\000\009\000\000\000\
\025\000\026\000\017\000\018\000\019\000\020\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\024\000\016\000\021\000\022\000\023\000\000\000\076\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\014\000\035\000\034\000\040\000\039\000\045\000\044\000\
\031\000\032\000\033\000\029\000\030\000\027\000\028\000\000\000\
\056\000\000\000\000\000\000\000\080\000\000\000\000\000\057\000\
\000\000\000\000\058\000\000\000\059\000\081\000\000\000\000\000\
\000\000\000\000\000\000\008\000\000\000\000\000\000\000\000\000\
\000\000\000\000\036\000\000\000\041\000\000\000\055\000\000\000\
\012\000\013\000\010\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\062\000\000\000\043\000\000\000\004\000\005\000\
\006\000\000\000\002\000\003\000\000\000\000\000\000\000\000\000\
\007\000\068\000\067\000\000\000\000\000\000\000\000\000\038\000\
\000\000\000\000\000\000\000\000\065\000\000\000\060\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\046\000\000\000\000\000\072\000\000\000\000\000\071\000\051\000\
\000\000\000\000\048\000\063\000\000\000\000\000\050\000\053\000\
\070\000\000\000\000\000\066\000"

let yydgoto = "\002\000\
\010\000\081\000\040\000\078\000\107\000\108\000\105\000\041\000\
\042\000\043\000\044\000\045\000\050\000\079\000\052\000\082\000\
\054\000\138\000\146\000\139\000\151\000\011\000\012\000\013\000\
\096\000\097\000\132\000\133\000\134\000\158\000\159\000\014\000"

let yysindex = "\011\000\
\001\000\000\000\011\255\011\255\011\255\011\255\129\255\011\255\
\000\000\000\000\000\000\000\000\000\000\001\000\017\255\012\255\
\034\255\040\255\059\255\000\000\011\255\011\255\000\000\006\255\
\000\000\000\000\000\000\000\000\000\000\000\000\045\255\046\255\
\255\254\055\255\036\255\047\255\053\255\060\255\072\255\039\255\
\000\000\000\000\000\000\000\000\000\000\077\255\000\000\073\255\
\011\255\076\255\129\255\078\255\086\255\081\255\079\255\061\255\
\090\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\011\255\
\000\000\011\255\062\255\063\255\000\000\083\255\089\255\000\000\
\087\255\092\255\000\000\129\255\000\000\000\000\093\255\051\255\
\051\255\051\255\102\255\000\000\051\255\051\255\011\255\098\255\
\063\255\051\255\000\000\129\255\000\000\112\255\000\000\117\255\
\000\000\000\000\000\000\116\255\118\255\051\255\119\255\120\255\
\123\255\121\255\000\000\125\255\000\000\124\255\000\000\000\000\
\000\000\132\255\000\000\000\000\088\255\079\255\011\255\106\255\
\000\000\000\000\000\000\130\255\088\255\011\255\128\255\000\000\
\051\255\108\255\129\255\146\255\000\000\136\255\000\000\147\255\
\131\255\134\255\149\255\079\255\183\255\148\255\150\255\129\255\
\000\000\106\255\153\255\000\000\155\255\166\255\000\000\000\000\
\106\255\175\255\000\000\000\000\204\255\176\255\000\000\000\000\
\000\000\079\255\177\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\029\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\041\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\004\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\186\255\186\255\000\000\000\000\000\000\186\255\000\000\000\000\
\179\255\000\000\000\000\191\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\186\255\000\000\000\000\
\000\000\000\000\000\000\192\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\193\255\000\000\000\000\000\000\
\000\000\205\255\000\000\000\000\000\000\000\000\000\000\180\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\005\255\000\000\000\000\185\255\000\000\000\000\000\000\
\156\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\200\000\249\255\140\255\255\255\174\255\184\255\209\255\248\255\
\191\000\000\000\000\000\000\000\185\000\090\000\186\000\134\000\
\202\000\082\000\000\000\076\000\000\000\000\000\000\000\000\000\
\141\000\000\000\106\000\000\000\000\000\000\000\075\000\000\000"

let yytablesize = 292
let yytable = "\039\000\
\009\000\016\000\017\000\018\000\019\000\104\000\046\000\087\000\
\131\000\001\000\111\000\001\000\047\000\020\000\001\000\116\000\
\131\000\109\000\049\000\056\000\057\000\112\000\059\000\061\000\
\063\000\015\000\025\000\026\000\053\000\079\000\048\000\079\000\
\157\000\079\000\079\000\079\000\047\000\122\000\075\000\079\000\
\051\000\079\000\034\000\035\000\036\000\037\000\015\000\074\000\
\157\000\015\000\015\000\049\000\051\000\015\000\144\000\015\000\
\066\000\067\000\079\000\020\000\020\000\088\000\093\000\089\000\
\094\000\020\000\086\000\068\000\069\000\053\000\091\000\055\000\
\092\000\070\000\071\000\065\000\102\000\072\000\135\000\106\000\
\106\000\106\000\073\000\076\000\106\000\106\000\080\000\077\000\
\083\000\106\000\084\000\085\000\090\000\113\000\086\000\098\000\
\099\000\100\000\095\000\101\000\155\000\106\000\020\000\103\000\
\110\000\114\000\130\000\024\000\025\000\026\000\027\000\028\000\
\029\000\030\000\031\000\032\000\033\000\118\000\119\000\120\000\
\123\000\121\000\171\000\124\000\034\000\035\000\036\000\037\000\
\106\000\125\000\128\000\147\000\142\000\126\000\127\000\129\000\
\137\000\140\000\143\000\145\000\149\000\153\000\152\000\020\000\
\162\000\021\000\022\000\023\000\024\000\025\000\026\000\027\000\
\028\000\029\000\030\000\031\000\032\000\033\000\148\000\154\000\
\150\000\161\000\160\000\164\000\165\000\034\000\035\000\036\000\
\037\000\038\000\049\000\166\000\049\000\049\000\049\000\049\000\
\049\000\049\000\049\000\049\000\049\000\049\000\049\000\049\000\
\049\000\168\000\061\000\172\000\170\000\011\000\069\000\052\000\
\049\000\049\000\049\000\049\000\049\000\020\000\042\000\037\000\
\064\000\156\000\024\000\025\000\026\000\027\000\028\000\029\000\
\030\000\031\000\032\000\033\000\054\000\047\000\058\000\060\000\
\136\000\062\000\020\000\034\000\035\000\036\000\037\000\024\000\
\025\000\026\000\027\000\028\000\029\000\030\000\031\000\032\000\
\033\000\117\000\064\000\163\000\167\000\115\000\141\000\169\000\
\034\000\035\000\036\000\037\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\003\000\004\000\005\000\000\000\000\000\
\000\000\006\000\007\000\008\000"

let yycheck = "\007\000\
\000\000\003\000\004\000\005\000\006\000\088\000\008\000\055\000\
\125\000\006\001\093\000\001\000\008\001\015\001\011\001\098\000\
\133\000\090\000\007\001\021\000\022\000\094\000\031\000\032\000\
\033\000\015\001\021\001\022\001\030\001\001\001\014\001\003\001\
\149\000\005\001\006\001\007\001\032\001\110\000\040\000\011\001\
\007\001\013\001\037\001\038\001\039\001\040\001\006\001\009\001\
\165\000\009\001\010\001\007\001\007\001\015\001\137\000\015\001\
\021\001\022\001\030\001\015\001\015\001\001\001\001\001\003\001\
\003\001\015\001\016\001\021\001\022\001\030\001\072\000\013\001\
\074\000\021\001\022\001\021\001\084\000\018\001\126\000\088\000\
\089\000\090\000\011\001\007\001\093\000\094\000\011\001\015\001\
\011\001\098\000\005\001\011\001\003\001\095\000\016\001\013\001\
\008\001\011\001\036\001\008\001\148\000\110\000\015\001\011\001\
\003\001\008\001\019\001\020\001\021\001\022\001\023\001\024\001\
\025\001\026\001\027\001\028\001\029\001\006\001\002\001\004\001\
\002\001\004\001\170\000\004\001\037\001\038\001\039\001\040\001\
\137\000\007\001\007\001\139\000\134\000\013\001\010\001\004\001\
\031\001\008\001\011\001\032\001\005\001\008\001\012\001\015\001\
\152\000\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\029\001\013\001\011\001\
\014\001\012\001\015\001\011\001\010\001\037\001\038\001\039\001\
\040\001\041\001\015\001\006\001\017\001\018\001\019\001\020\001\
\021\001\022\001\023\001\024\001\025\001\026\001\027\001\028\001\
\029\001\011\001\008\001\011\001\013\001\004\001\006\001\012\001\
\037\001\038\001\039\001\040\001\041\001\015\001\008\001\008\001\
\008\001\019\001\020\001\021\001\022\001\023\001\024\001\025\001\
\026\001\027\001\028\001\029\001\008\001\014\000\024\000\031\000\
\127\000\032\000\015\001\037\001\038\001\039\001\040\001\020\001\
\021\001\022\001\023\001\024\001\025\001\026\001\027\001\028\001\
\029\001\100\000\033\000\154\000\161\000\097\000\133\000\165\000\
\037\001\038\001\039\001\040\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\027\001\028\001\029\001\255\255\255\255\
\255\255\033\001\034\001\035\001"

let yynames_const = "\
  LBRACKET\000\
  RBRACKET\000\
  LANGLE\000\
  RANGLE\000\
  LPAREN\000\
  RPAREN\000\
  LBRACE\000\
  RBRACE\000\
  STAR\000\
  COMMA\000\
  SEMICOLON\000\
  COLON\000\
  EQUAL\000\
  MAPSTO\000\
  K_opaque\000\
  K_string\000\
  K_void\000\
  K_unsigned\000\
  K_int\000\
  K_hyper\000\
  K_float\000\
  K_double\000\
  K_quadruple\000\
  K_bool\000\
  K_enum\000\
  K_struct\000\
  K_union\000\
  K_switch\000\
  K_case\000\
  K_default\000\
  K_const\000\
  K_typedef\000\
  K_program\000\
  K_version\000\
  K_int32\000\
  K_int64\000\
  K_unboxed\000\
  K_abstract\000\
  K_managed\000\
  IGNORE\000\
  PERCENT\000\
  EOF\000\
  "

let yynames_block = "\
  IDENT\000\
  INTLITERAL\000\
  LINEFEED\000\
  SETFILE\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'type_specifier) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'declared_identifier) in
    Obj.repr(
# 35 "parser.mly"
    ( mk_decl _2 _1 )
# 360 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'type_specifier) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'value) in
    Obj.repr(
# 37 "parser.mly"
    ( mk_decl _2 (T_array_fixed(_4, _1)) )
# 369 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'type_specifier) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'value_opt) in
    Obj.repr(
# 39 "parser.mly"
    ( let v_opt = _4 in
      match v_opt with
	  None   -> mk_decl _2 (T_array_unlimited _1)
	| Some v -> mk_decl _2 (T_array (v, _1))
    )
# 382 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'value) in
    Obj.repr(
# 45 "parser.mly"
    ( mk_decl _2 (T_opaque_fixed _4) )
# 390 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'value_opt) in
    Obj.repr(
# 47 "parser.mly"
    ( let v_opt = _4 in
      match v_opt with
	  None   -> mk_decl _2 T_opaque_unlimited
	| Some v -> mk_decl _2 (T_opaque v)
    )
# 402 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'value_opt) in
    Obj.repr(
# 53 "parser.mly"
    ( let v_opt = _4 in
      match v_opt with
	  None   -> mk_decl _2 (T_string_unlimited)
	| Some v -> mk_decl _2 (T_string v)
    )
# 414 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'declared_identifier) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'value_opt) in
    Obj.repr(
# 59 "parser.mly"
    ( let v_opt = _5 in
      let name = ( _3 ).xdr_name in
      match v_opt with
	  None   -> mk_decl _3 (T_mstring_unlimited name)
	| Some v -> mk_decl _3 (T_mstring(name,v))
    )
# 427 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_specifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'declared_identifier) in
    Obj.repr(
# 66 "parser.mly"
    ( mk_decl _3 (T_option _1) )
# 435 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    Obj.repr(
# 68 "parser.mly"
    ( mk_decl (mk_void_id()) T_void )
# 441 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'value) in
    Obj.repr(
# 73 "parser.mly"
    ( Some _1 )
# 448 "parser.ml"
               : 'value_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 75 "parser.mly"
    ( None )
# 454 "parser.ml"
               : 'value_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'constant) in
    Obj.repr(
# 80 "parser.mly"
    ( let (sign,absval) = _1 in ref (Constant(sign,absval)) )
# 461 "parser.ml"
               : 'value))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 82 "parser.mly"
    ( ref (Named_constant _1) )
# 468 "parser.ml"
               : 'value))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'int_or_hyper) in
    Obj.repr(
# 87 "parser.mly"
    ( match _2 with
	  T_int v   -> T_uint v
	| T_hyper v -> T_uhyper v
	| _         -> assert false
    )
# 479 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 93 "parser.mly"
    ( T_uint !Options.default_int_variant )
# 485 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'int_or_hyper) in
    Obj.repr(
# 95 "parser.mly"
    ( _1 )
# 492 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 97 "parser.mly"
    ( T_float )
# 498 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 99 "parser.mly"
    ( T_double )
# 504 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 101 "parser.mly"
    ( error "Sorry, quadruple-precision floating point numbers are not supported"
    )
# 511 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 104 "parser.mly"
    ( T_bool )
# 517 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'enum_type_spec) in
    Obj.repr(
# 106 "parser.mly"
    ( _1 )
# 524 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'struct_type_spec) in
    Obj.repr(
# 108 "parser.mly"
    ( _1 )
# 531 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'union_type_spec) in
    Obj.repr(
# 110 "parser.mly"
    ( _1 )
# 538 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 112 "parser.mly"
    ( T_refer_to (R_any, ref _1) )
# 545 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 117 "parser.mly"
    ( T_int !Options.default_int_variant )
# 551 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 119 "parser.mly"
    ( T_hyper !Options.default_hyper_variant )
# 557 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 121 "parser.mly"
    ( T_int Abstract )
# 563 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 123 "parser.mly"
    ( T_hyper Abstract )
# 569 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 125 "parser.mly"
    ( T_int Unboxed )
# 575 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 127 "parser.mly"
    ( T_hyper Unboxed )
# 581 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 129 "parser.mly"
    ( T_int INT32 )
# 587 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 131 "parser.mly"
    ( T_int INT64 )
# 593 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 133 "parser.mly"
    ( T_hyper INT64 )
# 599 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'enum_body) in
    Obj.repr(
# 138 "parser.mly"
    ( T_enum _2 )
# 606 "parser.ml"
               : 'enum_type_spec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 140 "parser.mly"
    ( T_refer_to (R_enum, ref _2) )
# 613 "parser.ml"
               : 'enum_type_spec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'enum_body_list) in
    Obj.repr(
# 145 "parser.mly"
    ( _2 )
# 620 "parser.ml"
               : 'enum_body))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'declared_identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'value) in
    Obj.repr(
# 150 "parser.mly"
    ( [ _1, _3 ] )
# 628 "parser.ml"
               : 'enum_body_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'declared_identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'value) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'enum_body_list) in
    Obj.repr(
# 152 "parser.mly"
    ( ( _1, _3 ) :: _5 )
# 637 "parser.ml"
               : 'enum_body_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'struct_body) in
    Obj.repr(
# 157 "parser.mly"
    ( T_struct _2 )
# 644 "parser.ml"
               : 'struct_type_spec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 159 "parser.mly"
    ( T_refer_to (R_struct, ref _2) )
# 651 "parser.ml"
               : 'struct_type_spec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'struct_body_list) in
    Obj.repr(
# 164 "parser.mly"
    ( _2 )
# 658 "parser.ml"
               : 'struct_body))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'declaration) in
    Obj.repr(
# 169 "parser.mly"
    ( [ _1 ] )
# 665 "parser.ml"
               : 'struct_body_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'declaration) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'struct_body_list) in
    Obj.repr(
# 171 "parser.mly"
    ( _1 :: _3 )
# 673 "parser.ml"
               : 'struct_body_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'union_body) in
    Obj.repr(
# 176 "parser.mly"
    ( T_union _2 )
# 680 "parser.ml"
               : 'union_type_spec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 178 "parser.mly"
    ( T_refer_to (R_union, ref _2) )
# 687 "parser.ml"
               : 'union_type_spec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'declaration) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'union_body_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'union_default_opt) in
    Obj.repr(
# 184 "parser.mly"
    ( mk_union _3 _6 _7 )
# 696 "parser.ml"
               : 'union_body))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'union_case_list) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'declaration) in
    Obj.repr(
# 198 "parser.mly"
    ( let d = _2 in List.map (fun (v,mv) -> (v,mv,d)) _1 )
# 704 "parser.ml"
               : 'union_body_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'union_case_list) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'declaration) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'union_body_list) in
    Obj.repr(
# 200 "parser.mly"
    ( let d = _2 in List.map (fun (v,mv) -> (v,mv,d)) _1 @ _4 )
# 713 "parser.ml"
               : 'union_body_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'value) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'union_case_mapping) in
    Obj.repr(
# 205 "parser.mly"
    ( [ _2, _3 ] )
# 721 "parser.ml"
               : 'union_case_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'value) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'union_case_mapping) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'union_case_list) in
    Obj.repr(
# 207 "parser.mly"
    ( (_2, _3) :: _5 )
# 730 "parser.ml"
               : 'union_case_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 212 "parser.mly"
    ( Some _2 )
# 737 "parser.ml"
               : 'union_case_mapping))
; (fun __caml_parser_env ->
    Obj.repr(
# 214 "parser.mly"
    ( None )
# 743 "parser.ml"
               : 'union_case_mapping))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'declaration) in
    Obj.repr(
# 219 "parser.mly"
    ( Some _3 )
# 750 "parser.ml"
               : 'union_default_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 221 "parser.mly"
    ( None )
# 756 "parser.ml"
               : 'union_default_opt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'constant) in
    Obj.repr(
# 226 "parser.mly"
    ( Constdef(_2, _4) )
# 764 "parser.ml"
               : 'constant_def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'declaration) in
    Obj.repr(
# 231 "parser.mly"
    ( Typedef _2 )
# 771 "parser.ml"
               : 'type_def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'declared_identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'enum_body) in
    Obj.repr(
# 233 "parser.mly"
    ( Typedef (mk_decl _2 (T_enum _3)) )
# 779 "parser.ml"
               : 'type_def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'declared_identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'struct_body) in
    Obj.repr(
# 235 "parser.mly"
    ( Typedef (mk_decl _2 (T_struct _3)) )
# 787 "parser.ml"
               : 'type_def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'declared_identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'union_body) in
    Obj.repr(
# 237 "parser.mly"
    ( Typedef (mk_decl _2 (T_union _3)) )
# 795 "parser.ml"
               : 'type_def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'program_def_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'constant) in
    Obj.repr(
# 243 "parser.mly"
    ( let (sign,nr) = _7 in
      if sign then error "Program numbers must not be negative";
      mk_program _2 _4 nr
    )
# 807 "parser.ml"
               : 'program_def))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'version_def) in
    Obj.repr(
# 251 "parser.mly"
    ( [ _1 ] )
# 814 "parser.ml"
               : 'program_def_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'version_def) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'program_def_list) in
    Obj.repr(
# 253 "parser.mly"
    ( _1 :: _2 )
# 822 "parser.ml"
               : 'program_def_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'version_def_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'constant) in
    Obj.repr(
# 259 "parser.mly"
    ( let (sign,nr) = _7 in
      if sign then error "Version numbers must not be negative";
      mk_version _2 _4 nr
    )
# 834 "parser.ml"
               : 'version_def))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'procedure_def) in
    Obj.repr(
# 267 "parser.mly"
    ( [ _1 ] )
# 841 "parser.ml"
               : 'version_def_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'procedure_def) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'version_def_list) in
    Obj.repr(
# 269 "parser.mly"
    ( _1 :: _2 )
# 849 "parser.ml"
               : 'version_def_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 7 : 'type_specifier_or_void) in
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'parameter_list_or_void) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'constant) in
    Obj.repr(
# 275 "parser.mly"
    ( let (sign,nr) = _7 in
      if sign then error "Procdure numbers must not be negative";
      mk_procedure _2 _4 _1 nr
    )
# 862 "parser.ml"
               : 'procedure_def))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'type_specifier) in
    Obj.repr(
# 283 "parser.mly"
    ( _1 )
# 869 "parser.ml"
               : 'type_specifier_or_void))
; (fun __caml_parser_env ->
    Obj.repr(
# 285 "parser.mly"
    ( T_void )
# 875 "parser.ml"
               : 'type_specifier_or_void))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'type_specifier) in
    Obj.repr(
# 290 "parser.mly"
    ( [ _1 ] )
# 882 "parser.ml"
               : 'parameter_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_specifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'parameter_list) in
    Obj.repr(
# 292 "parser.mly"
    ( _1 :: _3 )
# 890 "parser.ml"
               : 'parameter_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parameter_list) in
    Obj.repr(
# 297 "parser.mly"
    ( _1 )
# 897 "parser.ml"
               : 'parameter_list_or_void))
; (fun __caml_parser_env ->
    Obj.repr(
# 299 "parser.mly"
    ( [ T_void ] )
# 903 "parser.ml"
               : 'parameter_list_or_void))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'type_def) in
    Obj.repr(
# 304 "parser.mly"
    ( _1 )
# 910 "parser.ml"
               : 'definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'constant_def) in
    Obj.repr(
# 306 "parser.mly"
    ( _1 )
# 917 "parser.ml"
               : 'definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'program_def) in
    Obj.repr(
# 308 "parser.mly"
    ( Progdef _1 )
# 924 "parser.ml"
               : 'definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'definition) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Syntax.xdr_def list) in
    Obj.repr(
# 313 "parser.mly"
    ( _1 :: _2 )
# 932 "parser.ml"
               : Syntax.xdr_def list))
; (fun __caml_parser_env ->
    Obj.repr(
# 315 "parser.mly"
    ( [] )
# 938 "parser.ml"
               : Syntax.xdr_def list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 320 "parser.mly"
    ( _1 )
# 945 "parser.ml"
               : 'identifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 325 "parser.mly"
    ( mk_id _1 )
# 952 "parser.ml"
               : 'declared_identifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 327 "parser.mly"
    ( mk_mapped_id _1 _3 )
# 960 "parser.ml"
               : 'declared_identifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 332 "parser.mly"
    ( constant_of_string _1 )
# 967 "parser.ml"
               : 'constant))
(* Entry specification *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let specification (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Syntax.xdr_def list)
;;
# 336 "parser.mly"

# 994 "parser.ml"
