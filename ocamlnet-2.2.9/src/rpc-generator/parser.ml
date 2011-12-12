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
  | IGNORE
  | PERCENT
  | LINEFEED of (int*int)
  | SETFILE of (int*string)
  | EOF

open Parsing;;
# 2 "parser.mly"

(* $Id: parser.mly 459 2006-04-30 19:49:19Z gerd $
 *)

  open Syntax

# 57 "parser.ml"
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
  297 (* IGNORE *);
  298 (* PERCENT *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  271 (* IDENT *);
  272 (* INTLITERAL *);
  299 (* LINEFEED *);
  300 (* SETFILE *);
    0|]

let yylhs = "\255\255\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\006\000\006\000\005\000\005\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\009\000\
\009\000\009\000\009\000\009\000\009\000\009\000\009\000\009\000\
\010\000\010\000\013\000\014\000\014\000\011\000\011\000\015\000\
\016\000\016\000\012\000\012\000\017\000\018\000\018\000\020\000\
\020\000\021\000\021\000\019\000\019\000\022\000\023\000\023\000\
\023\000\023\000\024\000\025\000\025\000\026\000\027\000\027\000\
\028\000\029\000\029\000\031\000\031\000\030\000\030\000\032\000\
\032\000\032\000\001\000\001\000\008\000\004\000\004\000\007\000\
\000\000"

let yylen = "\002\000\
\002\000\005\000\005\000\005\000\005\000\005\000\003\000\001\000\
\001\000\000\000\001\000\001\000\002\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\003\000\003\000\005\000\002\000\002\000\003\000\
\002\000\003\000\002\000\002\000\008\000\003\000\004\000\004\000\
\005\000\002\000\000\000\004\000\000\000\005\000\003\000\004\000\
\004\000\004\000\008\000\001\000\002\000\008\000\001\000\002\000\
\008\000\001\000\001\000\001\000\003\000\001\000\001\000\001\000\
\001\000\001\000\002\000\001\000\001\000\001\000\003\000\001\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\076\000\081\000\073\000\072\000\074\000\000\000\000\000\000\000\
\000\000\000\000\000\000\077\000\000\000\000\000\008\000\000\000\
\024\000\025\000\016\000\017\000\018\000\019\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\023\000\
\015\000\020\000\021\000\022\000\000\000\075\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\013\000\034\000\033\000\039\000\038\000\044\000\043\000\030\000\
\031\000\032\000\028\000\029\000\026\000\027\000\055\000\000\000\
\000\000\000\000\079\000\000\000\000\000\056\000\000\000\000\000\
\057\000\000\000\058\000\080\000\000\000\000\000\000\000\000\000\
\007\000\000\000\000\000\000\000\000\000\000\000\000\000\035\000\
\000\000\040\000\000\000\054\000\000\000\011\000\012\000\009\000\
\000\000\000\000\000\000\000\000\000\000\000\000\061\000\000\000\
\042\000\000\000\004\000\005\000\006\000\002\000\003\000\000\000\
\000\000\000\000\000\000\067\000\066\000\000\000\000\000\000\000\
\000\000\037\000\000\000\000\000\000\000\000\000\064\000\000\000\
\059\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\045\000\000\000\000\000\071\000\000\000\000\000\
\070\000\050\000\000\000\000\000\047\000\062\000\000\000\000\000\
\049\000\052\000\069\000\000\000\000\000\065\000"

let yydgoto = "\002\000\
\010\000\079\000\039\000\076\000\104\000\105\000\102\000\040\000\
\041\000\042\000\043\000\044\000\049\000\077\000\051\000\080\000\
\053\000\132\000\140\000\133\000\145\000\011\000\012\000\013\000\
\093\000\094\000\126\000\127\000\128\000\152\000\153\000\014\000"

let yysindex = "\039\000\
\001\000\000\000\051\255\051\255\051\255\051\255\059\255\051\255\
\000\000\000\000\000\000\000\000\000\000\001\000\055\255\063\255\
\082\255\070\255\088\255\000\000\051\255\051\255\000\000\009\255\
\000\000\000\000\000\000\000\000\000\000\000\000\017\255\030\255\
\011\255\081\255\250\254\035\255\040\255\093\255\044\255\000\000\
\000\000\000\000\000\000\000\000\096\255\000\000\090\255\051\255\
\095\255\059\255\098\255\102\255\099\255\097\255\089\255\108\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\051\255\
\092\255\076\255\000\000\101\255\107\255\000\000\106\255\110\255\
\000\000\059\255\000\000\000\000\109\255\028\255\028\255\028\255\
\000\000\028\255\028\255\051\255\111\255\076\255\028\255\000\000\
\059\255\000\000\115\255\000\000\120\255\000\000\000\000\000\000\
\119\255\121\255\122\255\124\255\125\255\116\255\000\000\126\255\
\000\000\127\255\000\000\000\000\000\000\000\000\000\000\149\255\
\097\255\051\255\100\255\000\000\000\000\129\255\149\255\051\255\
\142\255\000\000\028\255\103\255\059\255\117\255\000\000\128\255\
\000\000\140\255\143\255\148\255\146\255\097\255\175\255\144\255\
\153\255\059\255\000\000\100\255\155\255\000\000\157\255\152\255\
\000\000\000\000\100\255\168\255\000\000\000\000\196\255\167\255\
\000\000\000\000\000\000\097\255\170\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\022\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\045\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\008\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\178\255\178\255\
\000\000\000\000\178\255\000\000\000\000\176\255\000\000\000\000\
\177\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\184\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\185\255\000\000\
\000\000\000\000\000\000\197\255\000\000\000\000\000\000\000\000\
\000\000\171\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\004\255\000\000\000\000\200\255\000\000\
\000\000\000\000\123\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\177\000\249\255\147\255\255\255\183\255\207\255\208\255\233\255\
\183\000\000\000\000\000\000\000\178\000\086\000\194\000\113\000\
\195\000\079\000\000\000\074\000\000\000\000\000\000\000\000\000\
\136\000\000\000\104\000\000\000\000\000\000\000\073\000\000\000"

let yytablesize = 292
let yytable = "\038\000\
\009\000\016\000\017\000\018\000\019\000\085\000\045\000\058\000\
\060\000\062\000\125\000\046\000\101\000\001\000\065\000\066\000\
\107\000\125\000\001\000\055\000\056\000\112\000\078\000\048\000\
\078\000\020\000\078\000\078\000\078\000\025\000\026\000\020\000\
\078\000\151\000\078\000\046\000\050\000\073\000\106\000\001\000\
\052\000\108\000\020\000\084\000\020\000\034\000\035\000\036\000\
\037\000\151\000\014\000\078\000\072\000\014\000\014\000\067\000\
\068\000\138\000\015\000\014\000\069\000\070\000\103\000\103\000\
\103\000\015\000\103\000\103\000\047\000\048\000\089\000\103\000\
\129\000\020\000\099\000\021\000\022\000\023\000\024\000\025\000\
\026\000\027\000\028\000\029\000\030\000\031\000\032\000\033\000\
\050\000\086\000\109\000\087\000\090\000\149\000\091\000\034\000\
\035\000\036\000\037\000\052\000\054\000\064\000\074\000\071\000\
\075\000\078\000\082\000\103\000\081\000\083\000\088\000\092\000\
\084\000\095\000\096\000\165\000\097\000\098\000\110\000\100\000\
\114\000\115\000\116\000\118\000\117\000\141\000\136\000\119\000\
\121\000\142\000\131\000\120\000\143\000\123\000\139\000\122\000\
\134\000\048\000\156\000\048\000\048\000\048\000\048\000\048\000\
\048\000\048\000\048\000\048\000\048\000\048\000\048\000\048\000\
\137\000\144\000\146\000\147\000\148\000\160\000\154\000\048\000\
\048\000\048\000\048\000\020\000\155\000\158\000\159\000\124\000\
\024\000\025\000\026\000\027\000\028\000\029\000\030\000\031\000\
\032\000\033\000\162\000\164\000\166\000\010\000\051\000\060\000\
\041\000\034\000\035\000\036\000\037\000\020\000\046\000\036\000\
\063\000\150\000\024\000\025\000\026\000\027\000\028\000\029\000\
\030\000\031\000\032\000\033\000\053\000\068\000\057\000\130\000\
\059\000\113\000\020\000\034\000\035\000\036\000\037\000\024\000\
\025\000\026\000\027\000\028\000\029\000\030\000\031\000\032\000\
\033\000\061\000\157\000\063\000\161\000\111\000\135\000\163\000\
\034\000\035\000\036\000\037\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\003\000\004\000\005\000\000\000\000\000\
\000\000\006\000\007\000\008\000"

let yycheck = "\007\000\
\000\000\003\000\004\000\005\000\006\000\054\000\008\000\031\000\
\032\000\033\000\120\000\008\001\086\000\006\001\021\001\022\001\
\090\000\127\000\011\001\021\000\022\000\095\000\001\001\007\001\
\003\001\015\001\005\001\006\001\007\001\021\001\022\001\015\001\
\011\001\143\000\013\001\032\001\007\001\039\000\088\000\001\000\
\030\001\091\000\015\001\016\001\015\001\037\001\038\001\039\001\
\040\001\159\000\006\001\030\001\009\001\009\001\010\001\021\001\
\022\001\131\000\015\001\015\001\021\001\022\001\086\000\087\000\
\088\000\015\001\090\000\091\000\014\001\007\001\072\000\095\000\
\121\000\015\001\082\000\017\001\018\001\019\001\020\001\021\001\
\022\001\023\001\024\001\025\001\026\001\027\001\028\001\029\001\
\007\001\001\001\092\000\003\001\001\001\142\000\003\001\037\001\
\038\001\039\001\040\001\030\001\013\001\021\001\007\001\011\001\
\015\001\011\001\005\001\131\000\011\001\011\001\003\001\036\001\
\016\001\013\001\008\001\164\000\011\001\008\001\008\001\011\001\
\006\001\002\001\004\001\002\001\004\001\133\000\128\000\004\001\
\013\001\013\001\031\001\007\001\005\001\007\001\032\001\010\001\
\008\001\015\001\146\000\017\001\018\001\019\001\020\001\021\001\
\022\001\023\001\024\001\025\001\026\001\027\001\028\001\029\001\
\011\001\014\001\012\001\008\001\011\001\006\001\015\001\037\001\
\038\001\039\001\040\001\015\001\012\001\011\001\010\001\019\001\
\020\001\021\001\022\001\023\001\024\001\025\001\026\001\027\001\
\028\001\029\001\011\001\013\001\011\001\004\001\012\001\008\001\
\008\001\037\001\038\001\039\001\040\001\015\001\014\000\008\001\
\008\001\019\001\020\001\021\001\022\001\023\001\024\001\025\001\
\026\001\027\001\028\001\029\001\008\001\006\001\024\000\122\000\
\031\000\097\000\015\001\037\001\038\001\039\001\040\001\020\001\
\021\001\022\001\023\001\024\001\025\001\026\001\027\001\028\001\
\029\001\032\000\148\000\033\000\155\000\094\000\127\000\159\000\
\037\001\038\001\039\001\040\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
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
# 354 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'type_specifier) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'value) in
    Obj.repr(
# 37 "parser.mly"
    ( mk_decl _2 (T_array_fixed(_4, _1)) )
# 363 "parser.ml"
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
# 376 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'value) in
    Obj.repr(
# 45 "parser.mly"
    ( mk_decl _2 (T_opaque_fixed _4) )
# 384 "parser.ml"
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
# 396 "parser.ml"
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
# 408 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_specifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'declared_identifier) in
    Obj.repr(
# 59 "parser.mly"
    ( mk_decl _3 (T_option _1) )
# 416 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "parser.mly"
    ( mk_decl (mk_void_id()) T_void )
# 422 "parser.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'value) in
    Obj.repr(
# 66 "parser.mly"
    ( Some _1 )
# 429 "parser.ml"
               : 'value_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 68 "parser.mly"
    ( None )
# 435 "parser.ml"
               : 'value_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'constant) in
    Obj.repr(
# 73 "parser.mly"
    ( let (sign,absval) = _1 in ref (Constant(sign,absval)) )
# 442 "parser.ml"
               : 'value))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 75 "parser.mly"
    ( ref (Named_constant _1) )
# 449 "parser.ml"
               : 'value))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'int_or_hyper) in
    Obj.repr(
# 80 "parser.mly"
    ( match _2 with
	  T_int v   -> T_uint v
	| T_hyper v -> T_uhyper v
	| _         -> assert false
    )
# 460 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 86 "parser.mly"
    ( T_uint !Options.default_int_variant )
# 466 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'int_or_hyper) in
    Obj.repr(
# 88 "parser.mly"
    ( _1 )
# 473 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 90 "parser.mly"
    ( T_float )
# 479 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 92 "parser.mly"
    ( T_double )
# 485 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 94 "parser.mly"
    ( error "Sorry, quadruple-precision floating point numbers are not supported"
    )
# 492 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 97 "parser.mly"
    ( T_bool )
# 498 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'enum_type_spec) in
    Obj.repr(
# 99 "parser.mly"
    ( _1 )
# 505 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'struct_type_spec) in
    Obj.repr(
# 101 "parser.mly"
    ( _1 )
# 512 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'union_type_spec) in
    Obj.repr(
# 103 "parser.mly"
    ( _1 )
# 519 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 105 "parser.mly"
    ( T_refer_to (R_any, ref _1) )
# 526 "parser.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 110 "parser.mly"
    ( T_int !Options.default_int_variant )
# 532 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 112 "parser.mly"
    ( T_hyper !Options.default_hyper_variant )
# 538 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 114 "parser.mly"
    ( T_int Abstract )
# 544 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 116 "parser.mly"
    ( T_hyper Abstract )
# 550 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 118 "parser.mly"
    ( T_int Unboxed )
# 556 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 120 "parser.mly"
    ( T_hyper Unboxed )
# 562 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 122 "parser.mly"
    ( T_int INT32 )
# 568 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 124 "parser.mly"
    ( T_int INT64 )
# 574 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    Obj.repr(
# 126 "parser.mly"
    ( T_hyper INT64 )
# 580 "parser.ml"
               : 'int_or_hyper))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'enum_body) in
    Obj.repr(
# 131 "parser.mly"
    ( T_enum _2 )
# 587 "parser.ml"
               : 'enum_type_spec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 133 "parser.mly"
    ( T_refer_to (R_enum, ref _2) )
# 594 "parser.ml"
               : 'enum_type_spec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'enum_body_list) in
    Obj.repr(
# 138 "parser.mly"
    ( _2 )
# 601 "parser.ml"
               : 'enum_body))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'declared_identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'value) in
    Obj.repr(
# 143 "parser.mly"
    ( [ _1, _3 ] )
# 609 "parser.ml"
               : 'enum_body_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'declared_identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'value) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'enum_body_list) in
    Obj.repr(
# 145 "parser.mly"
    ( ( _1, _3 ) :: _5 )
# 618 "parser.ml"
               : 'enum_body_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'struct_body) in
    Obj.repr(
# 150 "parser.mly"
    ( T_struct _2 )
# 625 "parser.ml"
               : 'struct_type_spec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 152 "parser.mly"
    ( T_refer_to (R_struct, ref _2) )
# 632 "parser.ml"
               : 'struct_type_spec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'struct_body_list) in
    Obj.repr(
# 157 "parser.mly"
    ( _2 )
# 639 "parser.ml"
               : 'struct_body))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'declaration) in
    Obj.repr(
# 162 "parser.mly"
    ( [ _1 ] )
# 646 "parser.ml"
               : 'struct_body_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'declaration) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'struct_body_list) in
    Obj.repr(
# 164 "parser.mly"
    ( _1 :: _3 )
# 654 "parser.ml"
               : 'struct_body_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'union_body) in
    Obj.repr(
# 169 "parser.mly"
    ( T_union _2 )
# 661 "parser.ml"
               : 'union_type_spec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 171 "parser.mly"
    ( T_refer_to (R_union, ref _2) )
# 668 "parser.ml"
               : 'union_type_spec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'declaration) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'union_body_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'union_default_opt) in
    Obj.repr(
# 177 "parser.mly"
    ( mk_union _3 _6 _7 )
# 677 "parser.ml"
               : 'union_body))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'union_case_list) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'declaration) in
    Obj.repr(
# 191 "parser.mly"
    ( let d = _2 in List.map (fun (v,mv) -> (v,mv,d)) _1 )
# 685 "parser.ml"
               : 'union_body_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'union_case_list) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'declaration) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'union_body_list) in
    Obj.repr(
# 193 "parser.mly"
    ( let d = _2 in List.map (fun (v,mv) -> (v,mv,d)) _1 @ _4 )
# 694 "parser.ml"
               : 'union_body_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'value) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'union_case_mapping) in
    Obj.repr(
# 198 "parser.mly"
    ( [ _2, _3 ] )
# 702 "parser.ml"
               : 'union_case_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'value) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'union_case_mapping) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'union_case_list) in
    Obj.repr(
# 200 "parser.mly"
    ( (_2, _3) :: _5 )
# 711 "parser.ml"
               : 'union_case_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 205 "parser.mly"
    ( Some _2 )
# 718 "parser.ml"
               : 'union_case_mapping))
; (fun __caml_parser_env ->
    Obj.repr(
# 207 "parser.mly"
    ( None )
# 724 "parser.ml"
               : 'union_case_mapping))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'declaration) in
    Obj.repr(
# 212 "parser.mly"
    ( Some _3 )
# 731 "parser.ml"
               : 'union_default_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 214 "parser.mly"
    ( None )
# 737 "parser.ml"
               : 'union_default_opt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'constant) in
    Obj.repr(
# 219 "parser.mly"
    ( Constdef(_2, _4) )
# 745 "parser.ml"
               : 'constant_def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'declaration) in
    Obj.repr(
# 224 "parser.mly"
    ( Typedef _2 )
# 752 "parser.ml"
               : 'type_def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'declared_identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'enum_body) in
    Obj.repr(
# 226 "parser.mly"
    ( Typedef (mk_decl _2 (T_enum _3)) )
# 760 "parser.ml"
               : 'type_def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'declared_identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'struct_body) in
    Obj.repr(
# 228 "parser.mly"
    ( Typedef (mk_decl _2 (T_struct _3)) )
# 768 "parser.ml"
               : 'type_def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'declared_identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'union_body) in
    Obj.repr(
# 230 "parser.mly"
    ( Typedef (mk_decl _2 (T_union _3)) )
# 776 "parser.ml"
               : 'type_def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'program_def_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'constant) in
    Obj.repr(
# 236 "parser.mly"
    ( let (sign,nr) = _7 in
      if sign then error "Program numbers must not be negative";
      mk_program _2 _4 nr
    )
# 788 "parser.ml"
               : 'program_def))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'version_def) in
    Obj.repr(
# 244 "parser.mly"
    ( [ _1 ] )
# 795 "parser.ml"
               : 'program_def_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'version_def) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'program_def_list) in
    Obj.repr(
# 246 "parser.mly"
    ( _1 :: _2 )
# 803 "parser.ml"
               : 'program_def_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'version_def_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'constant) in
    Obj.repr(
# 252 "parser.mly"
    ( let (sign,nr) = _7 in
      if sign then error "Version numbers must not be negative";
      mk_version _2 _4 nr
    )
# 815 "parser.ml"
               : 'version_def))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'procedure_def) in
    Obj.repr(
# 260 "parser.mly"
    ( [ _1 ] )
# 822 "parser.ml"
               : 'version_def_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'procedure_def) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'version_def_list) in
    Obj.repr(
# 262 "parser.mly"
    ( _1 :: _2 )
# 830 "parser.ml"
               : 'version_def_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 7 : 'type_specifier_or_void) in
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'declared_identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'parameter_list_or_void) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'constant) in
    Obj.repr(
# 268 "parser.mly"
    ( let (sign,nr) = _7 in
      if sign then error "Procdure numbers must not be negative";
      mk_procedure _2 _4 _1 nr
    )
# 843 "parser.ml"
               : 'procedure_def))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'type_specifier) in
    Obj.repr(
# 276 "parser.mly"
    ( _1 )
# 850 "parser.ml"
               : 'type_specifier_or_void))
; (fun __caml_parser_env ->
    Obj.repr(
# 278 "parser.mly"
    ( T_void )
# 856 "parser.ml"
               : 'type_specifier_or_void))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'type_specifier) in
    Obj.repr(
# 283 "parser.mly"
    ( [ _1 ] )
# 863 "parser.ml"
               : 'parameter_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_specifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'parameter_list) in
    Obj.repr(
# 285 "parser.mly"
    ( _1 :: _3 )
# 871 "parser.ml"
               : 'parameter_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parameter_list) in
    Obj.repr(
# 290 "parser.mly"
    ( _1 )
# 878 "parser.ml"
               : 'parameter_list_or_void))
; (fun __caml_parser_env ->
    Obj.repr(
# 292 "parser.mly"
    ( [ T_void ] )
# 884 "parser.ml"
               : 'parameter_list_or_void))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'type_def) in
    Obj.repr(
# 297 "parser.mly"
    ( _1 )
# 891 "parser.ml"
               : 'definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'constant_def) in
    Obj.repr(
# 299 "parser.mly"
    ( _1 )
# 898 "parser.ml"
               : 'definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'program_def) in
    Obj.repr(
# 301 "parser.mly"
    ( Progdef _1 )
# 905 "parser.ml"
               : 'definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'definition) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Syntax.xdr_def list) in
    Obj.repr(
# 306 "parser.mly"
    ( _1 :: _2 )
# 913 "parser.ml"
               : Syntax.xdr_def list))
; (fun __caml_parser_env ->
    Obj.repr(
# 308 "parser.mly"
    ( [] )
# 919 "parser.ml"
               : Syntax.xdr_def list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 313 "parser.mly"
    ( _1 )
# 926 "parser.ml"
               : 'identifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 318 "parser.mly"
    ( mk_id _1 )
# 933 "parser.ml"
               : 'declared_identifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 320 "parser.mly"
    ( mk_mapped_id _1 _3 )
# 941 "parser.ml"
               : 'declared_identifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 325 "parser.mly"
    ( constant_of_string _1 )
# 948 "parser.ml"
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
# 329 "parser.mly"

# 975 "parser.ml"
