# 28 "pitlexertotex.mll"
 
open Parsing_helper
open Pitptree
open Fileprint

let kinds = Hashtbl.create 7

let init_kinds d = 
  Hashtbl.iter (fun keyw _ -> Hashtbl.add kinds keyw "\\kwl") Pitlexer.keyword_table;
  Hashtbl.add kinds "channel" "\\kwt";
  Hashtbl.add kinds "bitstring" "\\kwt";
  Hashtbl.add kinds "bool" "\\kwt";
  Hashtbl.add kinds "true" "\\kwc";
  Hashtbl.add kinds "false" "\\kwc";
  List.iter (function
      TTypeDecl(t,_) -> Hashtbl.add kinds t "\\kwt"
    | TFunDecl((f,_),_,_,_) -> Hashtbl.add kinds f "\\kwf"
    | TReduc(((_,(PFunApp((f,_),_),_),_)::_),_) -> Hashtbl.add kinds f "\\kwf"
    | TPredDecl((p,_),_,_) -> Hashtbl.add kinds p "\\kwp"
    | TFree((c,_),_,_) -> Hashtbl.add kinds c "\\kwc"
    | TConstDecl((c,_),_,_) -> Hashtbl.add kinds c "\\kwc"
    | TTableDecl((t,_),_) -> Hashtbl.add kinds t "\\kwt"
    | TEventDecl((e,_),_) -> Hashtbl.add kinds e "\\kwe"
    | TLetFun((f,_),_,_) -> Hashtbl.add kinds f "\\kwf"
    | _ -> ()) d

let parse filename = 
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    let ptree =
      try
        Pitparser.all Pitlexer.token lexbuf
      with Parsing.Parse_error ->
        input_error "Syntax error" (extent lexbuf)
    in
    close_in ic;
    ptree
  with Sys_error s ->
    user_error ("File error: " ^ s ^ "\n")


# 45 "pitlexertotex.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\222\255\223\255\081\000\000\000\231\255\232\255\233\255\
    \234\255\003\000\236\255\237\255\001\000\004\000\241\255\242\255\
    \243\255\244\255\245\255\005\000\001\000\081\000\144\000\097\001\
    \049\002\002\000\253\255\145\000\001\000\255\255\134\000\001\000\
    \054\000\064\001\062\000\063\000\064\000\065\000\148\000\107\000\
    \108\000\109\000\001\003\218\003\080\000\064\000\083\000\075\000\
    \070\000\224\255\250\255\117\004\248\255\155\000\156\000\127\000\
    \159\000\160\000\189\000\252\255\253\255\005\000\254\255\152\000\
    \255\255";
  Lexing.lex_backtrk = 
   "\255\255\255\255\255\255\033\000\033\000\255\255\255\255\255\255\
    \255\255\020\000\255\255\255\255\033\000\015\000\255\255\255\255\
    \255\255\255\255\255\255\008\000\009\000\006\000\033\000\004\000\
    \004\000\003\000\255\255\001\000\000\000\255\255\255\255\255\255\
    \255\255\255\255\017\000\025\000\029\000\255\255\026\000\028\000\
    \026\000\027\000\004\000\004\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\016\000\015\000\255\255\
    \020\000\030\000\255\255\255\255\255\255\001\000\255\255\003\000\
    \255\255";
  Lexing.lex_default = 
   "\001\000\000\000\000\000\255\255\255\255\000\000\000\000\000\000\
    \000\000\255\255\000\000\000\000\255\255\255\255\000\000\000\000\
    \000\000\000\000\000\000\255\255\255\255\255\255\051\000\255\255\
    \255\255\255\255\000\000\255\255\255\255\000\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\051\000\000\000\255\255\255\255\255\255\
    \255\255\255\255\059\000\000\000\000\000\255\255\000\000\255\255\
    \000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\026\000\029\000\029\000\025\000\028\000\025\000\062\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \027\000\010\000\022\000\056\000\054\000\019\000\012\000\034\000\
    \020\000\018\000\006\000\052\000\019\000\004\000\007\000\008\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\005\000\011\000\003\000\009\000\035\000\035\000\
    \055\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\017\000\034\000\016\000\034\000\035\000\
    \036\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\024\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\015\000\013\000\014\000\037\000\041\000\
    \053\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\039\000\040\000\041\000\038\000\036\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\033\000\050\000\037\000\040\000\045\000\046\000\032\000\
    \047\000\048\000\049\000\053\000\054\000\057\000\031\000\056\000\
    \057\000\064\000\000\000\038\000\036\000\000\000\000\000\062\000\
    \000\000\000\000\061\000\000\000\000\000\030\000\009\000\000\000\
    \000\000\000\000\039\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\063\000\
    \000\000\000\000\000\000\000\000\255\255\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\013\000\000\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \033\000\000\000\000\000\000\000\000\000\000\000\032\000\255\255\
    \000\000\000\000\000\000\000\000\000\000\031\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\030\000\009\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\255\255\
    \023\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \255\255\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\013\000\060\000\000\000\000\000\
    \023\000\000\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \000\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\000\000\000\000\000\000\000\000\
    \023\000\000\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\042\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \000\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\000\000\000\000\000\000\000\000\
    \023\000\000\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\043\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \000\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \000\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\000\000\000\000\000\000\000\000\000\000\044\000\
    \000\000\000\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\000\000\000\000\000\000\
    \000\000\023\000\000\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\000\000\050\000\
    \000\000\000\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\000\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\255\255\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\255\255";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\028\000\000\000\000\000\025\000\061\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\009\000\013\000\019\000\000\000\012\000\
    \000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\004\000\031\000\
    \009\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\032\000\000\000\034\000\035\000\
    \036\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\003\000\037\000\
    \013\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\039\000\040\000\041\000\003\000\003\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\027\000\022\000\030\000\038\000\044\000\045\000\027\000\
    \046\000\047\000\048\000\053\000\054\000\055\000\027\000\056\000\
    \057\000\063\000\255\255\030\000\030\000\255\255\255\255\058\000\
    \255\255\255\255\058\000\255\255\255\255\027\000\027\000\255\255\
    \255\255\255\255\038\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\058\000\
    \255\255\255\255\255\255\255\255\022\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\027\000\255\255\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \033\000\255\255\255\255\255\255\255\255\255\255\033\000\022\000\
    \255\255\255\255\255\255\255\255\255\255\033\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\033\000\033\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\022\000\
    \023\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \022\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\033\000\058\000\255\255\255\255\
    \023\000\255\255\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \255\255\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \024\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\255\255\255\255\255\255\255\255\
    \024\000\255\255\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \255\255\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \042\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\255\255\255\255\255\255\255\255\
    \042\000\255\255\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \255\255\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \255\255\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\043\000\255\255\255\255\255\255\255\255\255\255\043\000\
    \255\255\255\255\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\255\255\255\255\255\255\
    \255\255\043\000\255\255\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\255\255\051\000\
    \255\255\255\255\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\255\255\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\051\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\051\000\051\000\051\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\051\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\051\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\051\000";
  Lexing.lex_base_code = 
   "";
  Lexing.lex_backtrk_code = 
   "";
  Lexing.lex_default_code = 
   "";
  Lexing.lex_trans_code = 
   "";
  Lexing.lex_check_code = 
   "";
  Lexing.lex_code = 
   "";
}

let rec token lexbuf =
  __ocaml_lex_token_rec lexbuf 0
and __ocaml_lex_token_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 73 "pitlexertotex.mll"
     ( print_string "$\\\\\n$"; token lexbuf )
# 450 "pitlexertotex.ml"

  | 1 ->
# 75 "pitlexertotex.mll"
     ( print_string "\\ "; token lexbuf )
# 455 "pitlexertotex.ml"

  | 2 ->
# 77 "pitlexertotex.mll"
     ( print_string "\\qquad\\qquad "; token lexbuf )
# 460 "pitlexertotex.ml"

  | 3 ->
# 79 "pitlexertotex.mll"
     ( token lexbuf )
# 465 "pitlexertotex.ml"

  | 4 ->
# 81 "pitlexertotex.mll"
     ( 
       let s = Lexing.lexeme lexbuf in
       begin
	 try
           let k = Hashtbl.find kinds s  in
	   print_string (k ^ "{");
	   print_sanitize s;
	   print_string "}"
	 with Not_found ->
	   print_string "\\var{";
	   print_sanitize s;
	   print_string "}"
       end;
       token lexbuf
     )
# 484 "pitlexertotex.ml"

  | 5 ->
# 97 "pitlexertotex.mll"
    ( print_string "\\textit{";
      print_sanitize (Lexing.lexeme lexbuf);
      print_string "}"; token lexbuf )
# 491 "pitlexertotex.ml"

  | 6 ->
# 101 "pitlexertotex.mll"
     ( print_string (Lexing.lexeme lexbuf); token lexbuf )
# 496 "pitlexertotex.ml"

  | 7 ->
# 102 "pitlexertotex.mll"
       (
         print_string "\\textit{(*";
         comment lexbuf
       )
# 504 "pitlexertotex.ml"

  | 8 ->
# 106 "pitlexertotex.mll"
              ( print_string ", "; token lexbuf )
# 509 "pitlexertotex.ml"

  | 9 ->
# 107 "pitlexertotex.mll"
      ( print_string "("; token lexbuf )
# 514 "pitlexertotex.ml"

  | 10 ->
# 108 "pitlexertotex.mll"
      ( print_string ")"; token lexbuf )
# 519 "pitlexertotex.ml"

  | 11 ->
# 109 "pitlexertotex.mll"
      ( print_string "["; token lexbuf )
# 524 "pitlexertotex.ml"

  | 12 ->
# 110 "pitlexertotex.mll"
      ( print_string "]"; token lexbuf )
# 529 "pitlexertotex.ml"

  | 13 ->
# 111 "pitlexertotex.mll"
      ( print_string "\\{"; token lexbuf )
# 534 "pitlexertotex.ml"

  | 14 ->
# 112 "pitlexertotex.mll"
      ( print_string "\\}"; token lexbuf )
# 539 "pitlexertotex.ml"

  | 15 ->
# 113 "pitlexertotex.mll"
                      ( print_string "\\mid"; token lexbuf )
# 544 "pitlexertotex.ml"

  | 16 ->
# 114 "pitlexertotex.mll"
                       ( print_string (if !nice_tex then "\\vee" else "\\mid\\mid"); token lexbuf )
# 549 "pitlexertotex.ml"

  | 17 ->
# 115 "pitlexertotex.mll"
                       ( print_string (if !nice_tex then "\\wedge" else "\\ \\&\\&\\ "); token lexbuf )
# 554 "pitlexertotex.ml"

  | 18 ->
# 116 "pitlexertotex.mll"
      ( print_string ";"; token lexbuf )
# 559 "pitlexertotex.ml"

  | 19 ->
# 117 "pitlexertotex.mll"
      ( print_string "!"; token lexbuf )
# 564 "pitlexertotex.ml"

  | 20 ->
# 118 "pitlexertotex.mll"
                      ( print_string " = "; token lexbuf )
# 569 "pitlexertotex.ml"

  | 21 ->
# 119 "pitlexertotex.mll"
      ( print_string "/"; token lexbuf )
# 574 "pitlexertotex.ml"

  | 22 ->
# 120 "pitlexertotex.mll"
      ( print_string "."; token lexbuf )
# 579 "pitlexertotex.ml"

  | 23 ->
# 121 "pitlexertotex.mll"
      ( print_string "*"; token lexbuf )
# 584 "pitlexertotex.ml"

  | 24 ->
# 122 "pitlexertotex.mll"
      ( print_string "{:}"; token lexbuf )
# 589 "pitlexertotex.ml"

  | 25 ->
# 123 "pitlexertotex.mll"
                       ( print_string (if !nice_tex then "\\rightarrow" else "\\ {-}{>}\\ "); token lexbuf )
# 594 "pitlexertotex.ml"

  | 26 ->
# 124 "pitlexertotex.mll"
                       ( print_string (if !nice_tex then "\\leq" else "\\ {<}{=}\\ "); token lexbuf )
# 599 "pitlexertotex.ml"

  | 27 ->
# 125 "pitlexertotex.mll"
                        ( print_string (if !nice_tex then "\\leftrightarrow" else "\\ {<}{-}{>}\\ "); token lexbuf )
# 604 "pitlexertotex.ml"

  | 28 ->
# 126 "pitlexertotex.mll"
                        ( print_string (if !nice_tex then "\\Leftrightarrow" else "\\ {<}{=}{>}\\ "); token lexbuf )
# 609 "pitlexertotex.ml"

  | 29 ->
# 127 "pitlexertotex.mll"
                       ( print_string (if !nice_tex then "\\neq" else "\\ {<}{>}\\ "); token lexbuf )
# 614 "pitlexertotex.ml"

  | 30 ->
# 128 "pitlexertotex.mll"
                        ( print_string (if !nice_tex then "\\Longrightarrow" else "\\ {=}{=}{>}\\ "); token lexbuf )
# 619 "pitlexertotex.ml"

  | 31 ->
# 129 "pitlexertotex.mll"
              ( print_string "\\kwl{inj\\textbf{-}event}"; token lexbuf )
# 624 "pitlexertotex.ml"

  | 32 ->
# 130 "pitlexertotex.mll"
      (  print_string "$\n\\end{tabbing}\n" )
# 629 "pitlexertotex.ml"

  | 33 ->
# 131 "pitlexertotex.mll"
    ( input_error "Illegal character" (extent lexbuf) )
# 634 "pitlexertotex.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_token_rec lexbuf __ocaml_lex_state

and comment lexbuf =
  __ocaml_lex_comment_rec lexbuf 58
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 134 "pitlexertotex.mll"
       ( print_string "*)}";
         token lexbuf )
# 646 "pitlexertotex.ml"

  | 1 ->
# 137 "pitlexertotex.mll"
     ( print_string "}$\\\\\n$\\textit{"; comment lexbuf )
# 651 "pitlexertotex.ml"

  | 2 ->
# 138 "pitlexertotex.mll"
      ( print_string "}$\n\\end{tabbing}\n" )
# 656 "pitlexertotex.ml"

  | 3 ->
# 139 "pitlexertotex.mll"
    ( print_sanitize (Lexing.lexeme lexbuf); comment lexbuf )
# 661 "pitlexertotex.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

;;

# 141 "pitlexertotex.mll"
 

let convert filename = 
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    print_preamble();
    print_string "\\begin{tabbing}\n$";
    token lexbuf;
    close_in ic
  with Sys_error s ->
    user_error ("File error: " ^ s ^ "\n")

let converttotex f =
  let (d,_) = parse f in
  init_kinds d;
  convert f 


# 687 "pitlexertotex.ml"
