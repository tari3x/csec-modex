# 46 "olexer.mll"
 
open Parsing_helper
open Oparser

let create_hashtable size init =
  let tbl = Hashtbl.create size in
  List.iter (fun (key,data) -> Hashtbl.add tbl key data) init;
  tbl

let keyword_table =
  create_hashtable 11
[ "if", IF;
  "then", THEN;
  "else", ELSE;
  "find", FIND;
  "orfind", ORFIND;
  "suchthat", SUCHTHAT;
  "fun", FUN;
  "param", PARAM;
  "forall", FORALL;
  "proba", PROBA;
  "type", TYPE;
  "equiv", EQUIV;
  "process", PROCESS;
  "let", LET;
  "in", IN;
  "query", QUERY;
  "secret", SECRET;
  "secret1", SECRET1;
  "const", CONST;
  "set", SET;
  "defined", DEFINED;
  "collision", COLLISION;
  "event", EVENT;
  "time", TIME;
  "end", END;
  "otheruses", OTHERUSES;
  "maxlength", MAXLENGTH;
  "length", LENGTH;
  "max", MAX;
  "newOracle", NEWORACLE;
  "inj", INJ;
  "foreach", FOREACH;
  "do", DO;
  "return", RETURN;
  "define", DEFINE;
  "expand", EXPAND;
  "proof", PROOF
]


# 54 "olexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\218\255\219\255\220\255\221\255\222\255\223\255\225\255\
    \000\000\233\255\001\000\002\000\081\000\031\000\240\255\003\000\
    \242\255\243\255\244\255\245\255\034\000\248\255\054\000\082\000\
    \144\000\097\001\005\000\001\000\255\255\252\255\252\001\131\000\
    \249\255\067\000\231\255\234\255\228\255\058\000\236\255\101\000\
    \232\255\226\255\114\000\230\255\235\255\229\255\188\000\252\255\
    \253\255\005\000\254\255\136\000\255\255";
  Lexing.lex_backtrk = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \031\000\255\255\037\000\018\000\037\000\016\000\255\255\014\000\
    \255\255\255\255\255\255\255\255\009\000\255\255\008\000\004\000\
    \037\000\002\000\001\000\000\000\255\255\255\255\255\255\005\000\
    \255\255\255\255\255\255\255\255\255\255\028\000\255\255\017\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\001\000\255\255\003\000\255\255";
  Lexing.lex_default = 
   "\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \255\255\000\000\255\255\255\255\255\255\255\255\000\000\255\255\
    \000\000\000\000\000\000\000\000\255\255\000\000\255\255\255\255\
    \030\000\255\255\255\255\255\255\000\000\000\000\030\000\255\255\
    \000\000\255\255\000\000\000\000\000\000\255\255\000\000\255\255\
    \000\000\000\000\255\255\000\000\000\000\000\000\047\000\000\000\
    \000\000\255\255\000\000\255\255\000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\026\000\028\000\028\000\026\000\027\000\026\000\050\000\
    \000\000\026\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \026\000\000\000\024\000\003\000\000\000\026\000\010\000\044\000\
    \022\000\020\000\006\000\007\000\021\000\008\000\009\000\005\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\013\000\014\000\012\000\011\000\045\000\042\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\019\000\036\000\018\000\004\000\033\000\
    \032\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\017\000\015\000\016\000\037\000\035\000\
    \031\000\034\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\041\000\040\000\039\000\038\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \043\000\052\000\029\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\050\000\000\000\
    \000\000\049\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\051\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\255\255\
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
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\255\255\
    \025\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \255\255\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\048\000\000\000\000\000\000\000\
    \025\000\000\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\000\000\000\000\029\000\000\000\
    \000\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \000\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \255\255\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\255\255\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\255\255\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\027\000\000\000\000\000\026\000\049\000\
    \255\255\026\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\000\000\000\000\255\255\026\000\000\000\010\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\008\000\011\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\013\000\000\000\000\000\020\000\
    \022\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\012\000\015\000\
    \023\000\033\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\037\000\039\000\012\000\012\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \042\000\051\000\024\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\046\000\255\255\
    \255\255\046\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\046\000\255\255\
    \255\255\255\255\255\255\255\255\024\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\024\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\024\000\
    \025\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \024\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\046\000\255\255\255\255\255\255\
    \025\000\255\255\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\255\255\255\255\030\000\255\255\
    \255\255\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \255\255\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \030\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\030\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\030\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\030\000";
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
# 100 "olexer.mll"
     ( next_line lexbuf; token lexbuf )
# 295 "olexer.ml"

  | 1 ->
# 102 "olexer.mll"
     ( token lexbuf )
# 300 "olexer.ml"

  | 2 ->
# 104 "olexer.mll"
     ( let s = Lexing.lexeme lexbuf in
	 try
	   Hashtbl.find keyword_table s
         with Not_found ->
	   if (not (!accept_arobase)) && (String.contains s '@') then
	     raise IllegalCharacter;
           IDENT (s, extent lexbuf)
     )
# 312 "olexer.ml"

  | 3 ->
# 113 "olexer.mll"
    ( let s = Lexing.lexeme lexbuf in
      STRING (String.sub s 1 (String.length s - 2), extent lexbuf)
    )
# 319 "olexer.ml"

  | 4 ->
# 117 "olexer.mll"
    ( 
      try 
        INT (int_of_string(Lexing.lexeme lexbuf))
      with Failure _ ->
	input_error "Incorrect integer" (extent lexbuf)
    )
# 329 "olexer.ml"

  | 5 ->
# 124 "olexer.mll"
     ( FLOAT (float_of_string(Lexing.lexeme lexbuf)) )
# 334 "olexer.ml"

  | 6 ->
# 125 "olexer.mll"
       (
         comment lexbuf;
         token lexbuf
       )
# 342 "olexer.ml"

  | 7 ->
# 129 "olexer.mll"
      ( COMMA )
# 347 "olexer.ml"

  | 8 ->
# 130 "olexer.mll"
      ( LPAREN )
# 352 "olexer.ml"

  | 9 ->
# 131 "olexer.mll"
      ( RPAREN )
# 357 "olexer.ml"

  | 10 ->
# 132 "olexer.mll"
      ( LBRACKET )
# 362 "olexer.ml"

  | 11 ->
# 133 "olexer.mll"
      ( RBRACKET )
# 367 "olexer.ml"

  | 12 ->
# 134 "olexer.mll"
      ( LBRACE )
# 372 "olexer.ml"

  | 13 ->
# 135 "olexer.mll"
      ( RBRACE )
# 377 "olexer.ml"

  | 14 ->
# 136 "olexer.mll"
      ( BAR )
# 382 "olexer.ml"

  | 15 ->
# 137 "olexer.mll"
      ( SEMI )
# 387 "olexer.ml"

  | 16 ->
# 138 "olexer.mll"
      ( COLON )
# 392 "olexer.ml"

  | 17 ->
# 139 "olexer.mll"
       ( LEQ )
# 397 "olexer.ml"

  | 18 ->
# 140 "olexer.mll"
      ( EQUAL )
# 402 "olexer.ml"

  | 19 ->
# 141 "olexer.mll"
       ( DIFF )
# 407 "olexer.ml"

  | 20 ->
# 142 "olexer.mll"
       ( AND )
# 412 "olexer.ml"

  | 21 ->
# 143 "olexer.mll"
       ( OR )
# 417 "olexer.ml"

  | 22 ->
# 144 "olexer.mll"
      ( DOT )
# 422 "olexer.ml"

  | 23 ->
# 145 "olexer.mll"
        ( EQUIVLEFT )
# 427 "olexer.ml"

  | 24 ->
# 146 "olexer.mll"
        ( EQUIVRIGHT )
# 432 "olexer.ml"

  | 25 ->
# 147 "olexer.mll"
        ( IMPLIES )
# 437 "olexer.ml"

  | 26 ->
# 148 "olexer.mll"
       ( MAPSTO )
# 442 "olexer.ml"

  | 27 ->
# 149 "olexer.mll"
       ( DEF )
# 447 "olexer.ml"

  | 28 ->
# 150 "olexer.mll"
       ( LEFTARROW )
# 452 "olexer.ml"

  | 29 ->
# 151 "olexer.mll"
        ( RANDOM )
# 457 "olexer.ml"

  | 30 ->
# 152 "olexer.mll"
      ( ADD )
# 462 "olexer.ml"

  | 31 ->
# 153 "olexer.mll"
      ( SUB )
# 467 "olexer.ml"

  | 32 ->
# 154 "olexer.mll"
      ( MUL )
# 472 "olexer.ml"

  | 33 ->
# 155 "olexer.mll"
      ( DIV )
# 477 "olexer.ml"

  | 34 ->
# 156 "olexer.mll"
      ( POWER )
# 482 "olexer.ml"

  | 35 ->
# 157 "olexer.mll"
      ( COUNT )
# 487 "olexer.ml"

  | 36 ->
# 158 "olexer.mll"
      ( EOF )
# 492 "olexer.ml"

  | 37 ->
# 159 "olexer.mll"
    ( raise IllegalCharacter )
# 497 "olexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_token_rec lexbuf __ocaml_lex_state

and comment lexbuf =
    __ocaml_lex_comment_rec lexbuf 46
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 162 "olexer.mll"
       ( )
# 508 "olexer.ml"

  | 1 ->
# 164 "olexer.mll"
     ( next_line lexbuf; comment lexbuf )
# 513 "olexer.ml"

  | 2 ->
# 165 "olexer.mll"
      ( )
# 518 "olexer.ml"

  | 3 ->
# 166 "olexer.mll"
    ( comment lexbuf )
# 523 "olexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

;;

