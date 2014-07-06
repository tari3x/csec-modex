# 46 "lexer.mll"
 
open Parsing_helper
open Parser

let create_hashtable size init =
  let tbl = Hashtbl.create size in
  List.iter (fun (key,data) -> Hashtbl.add tbl key data) init;
  tbl

let keyword_table =
  create_hashtable 11
[ "new", NEW;
  "out", OUT;
  "in", IN;
  "if", IF;
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
  "query", QUERY;
  "secret", SECRET;
  "secret1", SECRET1;
  "const", CONST;
  "channel", CHANNEL;
  "set", SET;
  "defined", DEFINED;
  "collision", COLLISION;
  "event", EVENT;
  "time", TIME;
  "yield", YIELD;
  "otheruses", OTHERUSES;
  "maxlength", MAXLENGTH;
  "length", LENGTH;
  "max", MAX;
  "newChannel", NEWCHANNEL;
  "inj", INJ;
  "define", DEFINE;
  "expand", EXPAND;
  "proof", PROOF
]


# 54 "lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\219\255\220\255\221\255\224\255\225\255\226\255\000\000\
    \228\255\232\255\001\000\002\000\034\000\238\255\031\000\240\255\
    \002\000\242\255\243\255\244\255\245\255\066\000\248\255\086\000\
    \083\000\141\000\094\001\005\000\001\000\255\255\252\255\249\001\
    \128\000\249\255\068\000\230\255\233\255\222\255\235\255\133\000\
    \231\255\112\000\229\255\234\255\223\255\185\000\252\255\253\255\
    \005\000\254\255\145\000\255\255";
  Lexing.lex_backtrk = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\028\000\
    \255\255\255\255\036\000\019\000\036\000\255\255\016\000\255\255\
    \014\000\255\255\255\255\255\255\255\255\009\000\255\255\008\000\
    \004\000\036\000\002\000\001\000\000\000\255\255\255\255\255\255\
    \005\000\255\255\255\255\255\255\255\255\255\255\255\255\018\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \001\000\255\255\003\000\255\255";
  Lexing.lex_default = 
   "\001\000\000\000\000\000\000\000\000\000\000\000\000\000\255\255\
    \000\000\000\000\255\255\255\255\255\255\000\000\255\255\000\000\
    \255\255\000\000\000\000\000\000\000\000\255\255\000\000\255\255\
    \255\255\031\000\255\255\255\255\255\255\000\000\000\000\031\000\
    \255\255\000\000\255\255\000\000\000\000\000\000\000\000\255\255\
    \000\000\255\255\000\000\000\000\000\000\046\000\000\000\000\000\
    \255\255\000\000\255\255\000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\027\000\029\000\029\000\027\000\028\000\027\000\049\000\
    \000\000\027\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \027\000\013\000\025\000\003\000\000\000\027\000\010\000\043\000\
    \023\000\021\000\006\000\008\000\022\000\007\000\009\000\005\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\014\000\015\000\012\000\011\000\044\000\041\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\020\000\037\000\019\000\004\000\039\000\
    \038\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\018\000\016\000\017\000\036\000\034\000\
    \033\000\032\000\035\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\040\000\042\000\030\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\051\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\049\000\000\000\000\000\048\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\050\000\000\000\000\000\000\000\000\000\
    \000\000\255\255\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
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
    \000\000\000\000\000\000\000\000\255\255\026\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\255\255\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\047\000\000\000\000\000\000\000\026\000\000\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\030\000\000\000\000\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\000\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\255\255\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\255\255";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\028\000\000\000\000\000\027\000\048\000\
    \255\255\027\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\255\255\027\000\000\000\010\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\007\000\011\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\014\000\000\000\000\000\012\000\
    \012\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\016\000\021\000\
    \023\000\024\000\034\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\039\000\041\000\025\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\050\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\045\000\255\255\255\255\045\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\045\000\255\255\255\255\255\255\255\255\
    \255\255\025\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\025\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\025\000\026\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\025\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\045\000\255\255\255\255\255\255\026\000\255\255\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\255\255\255\255\031\000\255\255\255\255\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\255\255\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\031\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \031\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \031\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\031\000";
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
# 100 "lexer.mll"
     ( next_line lexbuf; token lexbuf )
# 295 "lexer.ml"

  | 1 ->
# 102 "lexer.mll"
     ( token lexbuf )
# 300 "lexer.ml"

  | 2 ->
# 104 "lexer.mll"
     ( let s = Lexing.lexeme lexbuf in
	 try
	   Hashtbl.find keyword_table s
         with Not_found ->
	   if (not (!accept_arobase)) && (String.contains s '@') then
	     raise IllegalCharacter;
           IDENT (s, extent lexbuf)
     )
# 312 "lexer.ml"

  | 3 ->
# 113 "lexer.mll"
    ( let s = Lexing.lexeme lexbuf in
      STRING (String.sub s 1 (String.length s - 2), extent lexbuf)
    )
# 319 "lexer.ml"

  | 4 ->
# 117 "lexer.mll"
    ( 
      try 
        INT (int_of_string(Lexing.lexeme lexbuf))
      with Failure _ ->
	input_error "Incorrect integer" (extent lexbuf)
    )
# 329 "lexer.ml"

  | 5 ->
# 124 "lexer.mll"
     ( FLOAT (float_of_string(Lexing.lexeme lexbuf)) )
# 334 "lexer.ml"

  | 6 ->
# 125 "lexer.mll"
       (
         comment lexbuf;
         token lexbuf
       )
# 342 "lexer.ml"

  | 7 ->
# 129 "lexer.mll"
      ( COMMA )
# 347 "lexer.ml"

  | 8 ->
# 130 "lexer.mll"
      ( LPAREN )
# 352 "lexer.ml"

  | 9 ->
# 131 "lexer.mll"
      ( RPAREN )
# 357 "lexer.ml"

  | 10 ->
# 132 "lexer.mll"
      ( LBRACKET )
# 362 "lexer.ml"

  | 11 ->
# 133 "lexer.mll"
      ( RBRACKET )
# 367 "lexer.ml"

  | 12 ->
# 134 "lexer.mll"
      ( LBRACE )
# 372 "lexer.ml"

  | 13 ->
# 135 "lexer.mll"
      ( RBRACE )
# 377 "lexer.ml"

  | 14 ->
# 136 "lexer.mll"
      ( BAR )
# 382 "lexer.ml"

  | 15 ->
# 137 "lexer.mll"
      ( SEMI )
# 387 "lexer.ml"

  | 16 ->
# 138 "lexer.mll"
      ( COLON )
# 392 "lexer.ml"

  | 17 ->
# 139 "lexer.mll"
      ( REPL )
# 397 "lexer.ml"

  | 18 ->
# 140 "lexer.mll"
       ( LEQ )
# 402 "lexer.ml"

  | 19 ->
# 141 "lexer.mll"
      ( EQUAL )
# 407 "lexer.ml"

  | 20 ->
# 142 "lexer.mll"
       ( DIFF )
# 412 "lexer.ml"

  | 21 ->
# 143 "lexer.mll"
       ( AND )
# 417 "lexer.ml"

  | 22 ->
# 144 "lexer.mll"
       ( OR )
# 422 "lexer.ml"

  | 23 ->
# 145 "lexer.mll"
      ( DOT )
# 427 "lexer.ml"

  | 24 ->
# 146 "lexer.mll"
        ( EQUIVLEFT )
# 432 "lexer.ml"

  | 25 ->
# 147 "lexer.mll"
        ( EQUIVRIGHT )
# 437 "lexer.ml"

  | 26 ->
# 148 "lexer.mll"
        ( IMPLIES )
# 442 "lexer.ml"

  | 27 ->
# 149 "lexer.mll"
      ( ADD )
# 447 "lexer.ml"

  | 28 ->
# 150 "lexer.mll"
      ( SUB )
# 452 "lexer.ml"

  | 29 ->
# 151 "lexer.mll"
      ( MUL )
# 457 "lexer.ml"

  | 30 ->
# 152 "lexer.mll"
      ( DIV )
# 462 "lexer.ml"

  | 31 ->
# 153 "lexer.mll"
      ( POWER )
# 467 "lexer.ml"

  | 32 ->
# 154 "lexer.mll"
       ( MAPSTO )
# 472 "lexer.ml"

  | 33 ->
# 155 "lexer.mll"
       ( DEF )
# 477 "lexer.ml"

  | 34 ->
# 156 "lexer.mll"
      ( COUNT )
# 482 "lexer.ml"

  | 35 ->
# 157 "lexer.mll"
      ( EOF )
# 487 "lexer.ml"

  | 36 ->
# 158 "lexer.mll"
    ( raise IllegalCharacter )
# 492 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_token_rec lexbuf __ocaml_lex_state

and comment lexbuf =
    __ocaml_lex_comment_rec lexbuf 45
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 161 "lexer.mll"
       ( )
# 503 "lexer.ml"

  | 1 ->
# 163 "lexer.mll"
     ( next_line lexbuf; comment lexbuf )
# 508 "lexer.ml"

  | 2 ->
# 164 "lexer.mll"
      ( )
# 513 "lexer.ml"

  | 3 ->
# 165 "lexer.mll"
    ( comment lexbuf )
# 518 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

;;

