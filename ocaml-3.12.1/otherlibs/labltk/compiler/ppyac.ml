type token =
  | IFDEF of (string)
  | IFNDEF of (string)
  | ELSE
  | ENDIF
  | DEFINE of (string)
  | UNDEF of (string)
  | OTHER of (string)
  | EOF

open Parsing;;
# 18 "ppyac.mly"
open Code
# 15 "ppyac.ml"
let yytransl_const = [|
  259 (* ELSE *);
  260 (* ENDIF *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* IFDEF *);
  258 (* IFNDEF *);
  261 (* DEFINE *);
  262 (* UNDEF *);
  263 (* OTHER *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\000\000"

let yylen = "\002\000\
\000\000\002\000\001\000\001\000\005\000\005\000\003\000\003\000\
\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\003\000\004\000\009\000\010\000\
\000\000\000\000\000\000\002\000\000\000\007\000\000\000\008\000\
\000\000\000\000\005\000\006\000"

let yydgoto = "\002\000\
\008\000\009\000"

let yysindex = "\003\000\
\004\255\000\000\004\255\004\255\000\000\000\000\000\000\000\000\
\004\255\012\255\014\255\000\000\004\255\000\000\004\255\000\000\
\252\254\003\255\000\000\000\000"

let yyrindex = "\000\000\
\013\000\000\000\016\255\016\255\000\000\000\000\000\000\000\000\
\001\000\000\000\000\000\000\000\017\255\000\000\017\255\000\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\255\255\000\000"

let yytablesize = 261
let yytable = "\019\000\
\001\000\010\000\011\000\001\000\003\000\004\000\020\000\012\000\
\005\000\006\000\007\000\017\000\001\000\018\000\013\000\014\000\
\015\000\016\000\001\000\001\000\001\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\001\000\001\000"

let yycheck = "\004\001\
\000\000\003\000\004\000\001\000\001\001\002\001\004\001\009\000\
\005\001\006\001\007\001\013\000\000\000\015\000\003\001\004\001\
\003\001\004\001\003\001\004\001\004\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\003\001\004\001"

let yynames_const = "\
  ELSE\000\
  ENDIF\000\
  EOF\000\
  "

let yynames_block = "\
  IFDEF\000\
  IFNDEF\000\
  DEFINE\000\
  UNDEF\000\
  OTHER\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 38 "ppyac.mly"
                ( [] )
# 150 "ppyac.ml"
               : Code.code list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'code) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Code.code list) in
    Obj.repr(
# 39 "ppyac.mly"
                   ( _1 :: _2 )
# 158 "ppyac.ml"
               : Code.code list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 43 "ppyac.mly"
           ( Define _1 )
# 165 "ppyac.ml"
               : 'code))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 44 "ppyac.mly"
          ( Undef _1 )
# 172 "ppyac.ml"
               : 'code))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Code.code list) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Code.code list) in
    Obj.repr(
# 45 "ppyac.mly"
                                         ( Ifdef (true, _1, _2, Some (_4)) )
# 181 "ppyac.ml"
               : 'code))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Code.code list) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Code.code list) in
    Obj.repr(
# 46 "ppyac.mly"
                                          ( Ifdef (false, _1, _2, Some (_4)) )
# 190 "ppyac.ml"
               : 'code))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Code.code list) in
    Obj.repr(
# 47 "ppyac.mly"
                          ( Ifdef (true, _1, _2, None) )
# 198 "ppyac.ml"
               : 'code))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Code.code list) in
    Obj.repr(
# 48 "ppyac.mly"
                           ( Ifdef (false, _1, _2, None) )
# 206 "ppyac.ml"
               : 'code))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 49 "ppyac.mly"
          ( Line _1 )
# 213 "ppyac.ml"
               : 'code))
(* Entry code_list *)
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
let code_list (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Code.code list)
;;
