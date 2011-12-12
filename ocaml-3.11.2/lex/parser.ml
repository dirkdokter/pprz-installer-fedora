type token =
  | Tident of (string)
  | Tchar of (int)
  | Tstring of (string)
  | Taction of (Syntax.location)
  | Trule
  | Tparse
  | Tparse_shortest
  | Tand
  | Tequal
  | Tend
  | Tor
  | Tunderscore
  | Teof
  | Tlbracket
  | Trbracket
  | Tstar
  | Tmaybe
  | Tplus
  | Tlparen
  | Trparen
  | Tcaret
  | Tdash
  | Tlet
  | Tas
  | Tsharp

open Parsing;;
# 18 "parser.mly"
open Syntax

(* Auxiliaries for the parser. *)

let named_regexps =
  (Hashtbl.create 13 : (string, regular_expression) Hashtbl.t)

let regexp_for_string s =
  let rec re_string n =
    if n >= String.length s then Epsilon
    else if succ n = String.length s then
      Characters (Cset.singleton (Char.code s.[n]))
    else
      Sequence
        (Characters(Cset.singleton (Char.code s.[n])),
         re_string (succ n))
  in re_string 0

let rec remove_as = function
  | Bind (e,_) -> remove_as e
  | Epsilon|Eof|Characters _ as e -> e
  | Sequence (e1, e2) -> Sequence (remove_as e1, remove_as e2)
  | Alternative (e1, e2) -> Alternative (remove_as e1, remove_as e2)
  | Repetition e -> Repetition (remove_as e)

let as_cset = function
  | Characters s -> s
  | _ -> raise Cset.Bad

# 60 "parser.ml"
let yytransl_const = [|
  261 (* Trule *);
  262 (* Tparse *);
  263 (* Tparse_shortest *);
  264 (* Tand *);
  265 (* Tequal *);
  266 (* Tend *);
  267 (* Tor *);
  268 (* Tunderscore *);
  269 (* Teof *);
  270 (* Tlbracket *);
  271 (* Trbracket *);
  272 (* Tstar *);
  273 (* Tmaybe *);
  274 (* Tplus *);
  275 (* Tlparen *);
  276 (* Trparen *);
  277 (* Tcaret *);
  278 (* Tdash *);
  279 (* Tlet *);
  280 (* Tas *);
  281 (* Tsharp *);
    0|]

let yytransl_block = [|
  257 (* Tident *);
  258 (* Tchar *);
  259 (* Tstring *);
  260 (* Taction *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\003\000\003\000\005\000\005\000\004\000\
\004\000\007\000\007\000\008\000\008\000\010\000\010\000\009\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\012\000\011\000\
\011\000\013\000\013\000\013\000\000\000"

let yylen = "\002\000\
\007\000\001\000\000\000\005\000\000\000\003\000\000\000\005\000\
\005\000\002\000\000\000\002\000\003\000\003\000\000\000\002\000\
\001\000\001\000\001\000\001\000\003\000\002\000\002\000\002\000\
\003\000\003\000\002\000\003\000\001\000\003\000\001\000\002\000\
\001\000\003\000\001\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\002\000\037\000\005\000\000\000\000\000\000\000\
\000\000\007\000\000\000\000\000\000\000\000\000\000\000\010\000\
\000\000\000\000\000\000\029\000\019\000\020\000\017\000\018\000\
\000\000\000\000\000\000\000\000\000\000\006\000\001\000\000\000\
\000\000\000\000\000\000\000\000\000\000\022\000\023\000\024\000\
\000\000\000\000\000\000\000\000\000\000\008\000\015\000\009\000\
\000\000\000\000\021\000\000\000\028\000\000\000\031\000\030\000\
\000\000\015\000\016\000\000\000\034\000\000\000\000\000\014\000"

let yydgoto = "\002\000\
\004\000\005\000\006\000\010\000\014\000\043\000\013\000\046\000\
\047\000\060\000\034\000\056\000\052\000"

let yysindex = "\005\000\
\013\255\000\000\000\000\000\000\000\000\003\255\008\255\017\255\
\018\255\000\000\023\255\018\255\028\255\049\255\157\255\000\000\
\254\254\008\255\021\255\000\000\000\000\000\000\000\000\000\000\
\255\254\157\255\067\255\154\255\154\255\000\000\000\000\032\255\
\041\255\029\255\041\255\022\255\157\255\000\000\000\000\000\000\
\044\255\157\255\135\255\157\255\048\255\000\000\000\000\000\000\
\056\255\041\255\000\000\041\255\000\000\135\255\000\000\000\000\
\116\255\000\000\000\000\052\255\000\000\052\255\157\255\000\000"

let yyrindex = "\000\000\
\005\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\068\255\000\000\000\000\068\255\000\000\072\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\007\255\000\000\000\000\000\000\000\000\001\255\
\000\000\000\000\074\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\083\255\000\000\000\000\000\000\000\000\000\000\
\000\000\075\255\000\000\085\255\000\000\091\255\000\000\000\000\
\051\255\000\000\000\000\089\255\000\000\136\255\000\000\000\000"

let yygindex = "\000\000\
\000\000\084\000\000\000\083\000\000\000\241\255\092\000\076\000\
\214\255\051\000\000\000\000\000\238\255"

let yytablesize = 176
let yytable = "\027\000\
\032\000\058\000\035\000\028\000\029\000\001\000\035\000\007\000\
\009\000\003\000\036\000\004\000\045\000\045\000\050\000\035\000\
\003\000\011\000\012\000\033\000\064\000\054\000\020\000\021\000\
\022\000\008\000\057\000\003\000\045\000\004\000\031\000\015\000\
\037\000\023\000\024\000\025\000\017\000\038\000\039\000\040\000\
\026\000\053\000\032\000\051\000\055\000\041\000\042\000\045\000\
\020\000\021\000\022\000\059\000\003\000\049\000\025\000\025\000\
\018\000\061\000\037\000\023\000\024\000\025\000\063\000\038\000\
\039\000\040\000\026\000\020\000\021\000\022\000\025\000\041\000\
\042\000\025\000\025\000\025\000\011\000\037\000\023\000\024\000\
\025\000\003\000\038\000\039\000\040\000\026\000\027\000\027\000\
\033\000\032\000\041\000\042\000\012\000\027\000\026\000\026\000\
\012\000\019\000\012\000\036\000\030\000\026\000\027\000\016\000\
\048\000\027\000\027\000\027\000\062\000\000\000\026\000\000\000\
\000\000\026\000\026\000\026\000\020\000\021\000\022\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\037\000\023\000\
\024\000\025\000\000\000\038\000\039\000\040\000\026\000\020\000\
\021\000\022\000\000\000\013\000\000\000\000\000\000\000\013\000\
\000\000\013\000\023\000\024\000\025\000\000\000\038\000\039\000\
\040\000\026\000\020\000\021\000\022\000\020\000\021\000\022\000\
\000\000\000\000\000\000\000\000\044\000\023\000\024\000\025\000\
\023\000\024\000\025\000\000\000\026\000\000\000\000\000\026\000"

let yycheck = "\015\000\
\002\001\044\000\002\001\006\001\007\001\001\000\025\000\005\001\
\001\001\005\001\026\000\005\001\028\000\029\000\033\000\015\001\
\004\001\001\001\001\001\021\001\063\000\037\000\001\001\002\001\
\003\001\023\001\042\000\023\001\044\000\023\001\010\001\009\001\
\011\001\012\001\013\001\014\001\009\001\016\001\017\001\018\001\
\019\001\020\001\002\001\015\001\001\001\024\001\025\001\063\000\
\001\001\002\001\003\001\004\001\004\001\022\001\004\001\005\001\
\008\001\002\001\011\001\012\001\013\001\014\001\011\001\016\001\
\017\001\018\001\019\001\001\001\002\001\003\001\020\001\024\001\
\025\001\023\001\024\001\025\001\009\001\011\001\012\001\013\001\
\014\001\010\001\016\001\017\001\018\001\019\001\004\001\005\001\
\015\001\015\001\024\001\025\001\004\001\011\001\004\001\005\001\
\008\001\014\000\010\001\015\001\018\000\011\001\020\001\012\000\
\029\000\023\001\024\001\025\001\058\000\255\255\020\001\255\255\
\255\255\023\001\024\001\025\001\001\001\002\001\003\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\011\001\012\001\
\013\001\014\001\255\255\016\001\017\001\018\001\019\001\001\001\
\002\001\003\001\255\255\004\001\255\255\255\255\255\255\008\001\
\255\255\010\001\012\001\013\001\014\001\255\255\016\001\017\001\
\018\001\019\001\001\001\002\001\003\001\001\001\002\001\003\001\
\255\255\255\255\255\255\255\255\011\001\012\001\013\001\014\001\
\012\001\013\001\014\001\255\255\019\001\255\255\255\255\019\001"

let yynames_const = "\
  Trule\000\
  Tparse\000\
  Tparse_shortest\000\
  Tand\000\
  Tequal\000\
  Tend\000\
  Tor\000\
  Tunderscore\000\
  Teof\000\
  Tlbracket\000\
  Trbracket\000\
  Tstar\000\
  Tmaybe\000\
  Tplus\000\
  Tlparen\000\
  Trparen\000\
  Tcaret\000\
  Tdash\000\
  Tlet\000\
  Tas\000\
  Tsharp\000\
  "

let yynames_block = "\
  Tident\000\
  Tchar\000\
  Tstring\000\
  Taction\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : 'header) in
    let _2 = (Parsing.peek_val __caml_parser_env 5 : 'named_regexps) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'definition) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'other_definitions) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'header) in
    Obj.repr(
# 70 "parser.mly"
        ( {header = _1;
           entrypoints = _4 :: List.rev _5;
           trailer = _6} )
# 237 "parser.ml"
               : Syntax.lexer_definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Syntax.location) in
    Obj.repr(
# 76 "parser.mly"
        ( _1 )
# 244 "parser.ml"
               : 'header))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "parser.mly"
        ( { start_pos = 0; end_pos = 0; start_line = 1; start_col = 0 } )
# 250 "parser.ml"
               : 'header))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'named_regexps) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'regexp) in
    Obj.repr(
# 82 "parser.mly"
        ( Hashtbl.add named_regexps _3 _5 )
# 259 "parser.ml"
               : 'named_regexps))
; (fun __caml_parser_env ->
    Obj.repr(
# 84 "parser.mly"
        ( () )
# 265 "parser.ml"
               : 'named_regexps))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'other_definitions) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'definition) in
    Obj.repr(
# 88 "parser.mly"
        ( _3::_1 )
# 273 "parser.ml"
               : 'other_definitions))
; (fun __caml_parser_env ->
    Obj.repr(
# 90 "parser.mly"
        ( [] )
# 279 "parser.ml"
               : 'other_definitions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'arguments) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'entry) in
    Obj.repr(
# 94 "parser.mly"
        ( {name=_1 ; shortest=false ; args=_2 ; clauses=_5} )
# 288 "parser.ml"
               : 'definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'arguments) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'entry) in
    Obj.repr(
# 96 "parser.mly"
        ( {name=_1 ; shortest=true ; args=_2 ; clauses=_5} )
# 297 "parser.ml"
               : 'definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'arguments) in
    Obj.repr(
# 100 "parser.mly"
                            ( _1::_2 )
# 305 "parser.ml"
               : 'arguments))
; (fun __caml_parser_env ->
    Obj.repr(
# 101 "parser.mly"
                            ( [] )
# 311 "parser.ml"
               : 'arguments))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'case) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'rest_of_entry) in
    Obj.repr(
# 107 "parser.mly"
        ( _1::List.rev _2 )
# 319 "parser.ml"
               : 'entry))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'case) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'rest_of_entry) in
    Obj.repr(
# 109 "parser.mly"
        ( _2::List.rev _3 )
# 327 "parser.ml"
               : 'entry))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'rest_of_entry) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'case) in
    Obj.repr(
# 114 "parser.mly"
        ( _3::_1 )
# 335 "parser.ml"
               : 'rest_of_entry))
; (fun __caml_parser_env ->
    Obj.repr(
# 116 "parser.mly"
        ( [] )
# 341 "parser.ml"
               : 'rest_of_entry))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'regexp) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Syntax.location) in
    Obj.repr(
# 120 "parser.mly"
        ( (_1,_2) )
# 349 "parser.ml"
               : 'case))
; (fun __caml_parser_env ->
    Obj.repr(
# 124 "parser.mly"
        ( Characters Cset.all_chars )
# 355 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    Obj.repr(
# 126 "parser.mly"
        ( Eof )
# 361 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 128 "parser.mly"
        ( Characters (Cset.singleton _1) )
# 368 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 130 "parser.mly"
        ( regexp_for_string _1 )
# 375 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'char_class) in
    Obj.repr(
# 132 "parser.mly"
        ( Characters _2 )
# 382 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'regexp) in
    Obj.repr(
# 134 "parser.mly"
        ( Repetition _1 )
# 389 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'regexp) in
    Obj.repr(
# 136 "parser.mly"
        ( Alternative(Epsilon, _1) )
# 396 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'regexp) in
    Obj.repr(
# 138 "parser.mly"
        ( Sequence(Repetition (remove_as _1), _1) )
# 403 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'regexp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'regexp) in
    Obj.repr(
# 140 "parser.mly"
        (
          let s1 = as_cset _1
          and s2 = as_cset _3 in
          Characters (Cset.diff s1 s2)
        )
# 415 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'regexp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'regexp) in
    Obj.repr(
# 146 "parser.mly"
        ( Alternative(_1,_3) )
# 423 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'regexp) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'regexp) in
    Obj.repr(
# 148 "parser.mly"
        ( Sequence(_1,_2) )
# 431 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'regexp) in
    Obj.repr(
# 150 "parser.mly"
        ( _2 )
# 438 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 152 "parser.mly"
        ( try
            Hashtbl.find named_regexps _1
          with Not_found ->
            let p = Parsing.symbol_start_pos () in
            Printf.eprintf "File \"%s\", line %d, character %d:\n\
                             Reference to unbound regexp name `%s'.\n"
                           p.Lexing.pos_fname p.Lexing.pos_lnum
                           (p.Lexing.pos_cnum - p.Lexing.pos_bol)
                           _1;
            exit 2 )
# 454 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'regexp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'ident) in
    Obj.repr(
# 163 "parser.mly"
        (let p1 = Parsing.rhs_start_pos 3
         and p2 = Parsing.rhs_end_pos 3 in
         let p = {
           start_pos = p1.Lexing.pos_cnum ;
           end_pos = p2.Lexing.pos_cnum ;
           start_line = p1.Lexing.pos_lnum ;
           start_col = p1.Lexing.pos_cnum - p1.Lexing.pos_bol ; } in
         Bind (_1, (_3, p)))
# 469 "parser.ml"
               : 'regexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 174 "parser.mly"
         (_1)
# 476 "parser.ml"
               : 'ident))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'char_class1) in
    Obj.repr(
# 179 "parser.mly"
        ( Cset.complement _2 )
# 483 "parser.ml"
               : 'char_class))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'char_class1) in
    Obj.repr(
# 181 "parser.mly"
        ( _1 )
# 490 "parser.ml"
               : 'char_class))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 185 "parser.mly"
        ( Cset.interval _1 _3 )
# 498 "parser.ml"
               : 'char_class1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 187 "parser.mly"
        ( Cset.singleton _1 )
# 505 "parser.ml"
               : 'char_class1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'char_class1) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'char_class1) in
    Obj.repr(
# 189 "parser.mly"
        ( Cset.union _1 _2 )
# 513 "parser.ml"
               : 'char_class1))
(* Entry lexer_definition *)
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
let lexer_definition (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Syntax.lexer_definition)
;;
