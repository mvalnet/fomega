{ (* Emacs, use -*- tuareg -*- to open this file. *)

open Lexing
open Parser

let pp_location _ _ = ()

  (* A table of keywords. *)
let keywords = [
      "lam", LAMBDA;
      "lam", LAMBDA;
      "fun", FUN;
      "all", ALL;
      "exi", EXI;
      "type", TYPE;
      "Type", TTYPE;
      "let", LET;
      "val", VAL;
      "in", IN;
      "rec", REC;
       "as", AS; 
      (* "if", IF;
       * "then", THEN;
       * "else", ELSE; *)
    ]

let unless_keyword f s =
  try List.assoc s keywords
  with Not_found -> f s
                        

let newline lexbuf =
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
                         pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
                         pos_bol =  lexbuf.lex_curr_p.pos_cnum;
                       }

let in_comment = ref false

(* included from ocaml lexer.mll *)
let in_pattern () = not !in_comment
let string_buff = Buffer.create 256

let reset_string_buffer () = Buffer.clear string_buff
let store_string_char c = Buffer.add_char string_buff c
let get_stored_string () = Buffer.contents string_buff
let char_for_backslash = function
    'n' -> '\n'
  | 't' -> '\t'
  | 'b' -> '\b'
  | 'r' -> '\r'
  | c   -> c

let warning lexbuf msg =
  let p = Lexing.lexeme_start_p lexbuf in
  Printf.eprintf "ocamllex warning:\nFile \"%s\", line %d, character %d: %s.\n"
    p.Lexing.pos_fname p.Lexing.pos_lnum
    (p.Lexing.pos_cnum - p.Lexing.pos_bol + 1) msg;
  flush stderr

let decimal_code  c d u =
  100 * (Char.code c - 48) + 10 * (Char.code d - 48) + (Char.code u - 48)

let char_for_hexadecimal_code d u =
  let d1 = Char.code d in
  let val1 = if d1 >= 97 then d1 - 87
             else if d1 >= 65 then d1 - 55
             else d1 - 48
  in
  let d2 = Char.code u in
  let val2 = if d2 >= 97 then d2 - 87
             else if d2 >= 65 then d2 - 55
             else d2 - 48
  in
  Char.chr (val1 * 16 + val2)

let incr_loc lexbuf delta =
  let pos = lexbuf.Lexing.lex_curr_p in
  lexbuf.Lexing.lex_curr_p <- { pos with
    Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
    Lexing.pos_bol = pos.Lexing.pos_cnum - delta;
  }

}

let newline = ('\n' | '\r' | "\r\n")

let whitespace   = [' ' '\t' '\012']

let digit = [ '0'-'9' ]

let integer = ( "0x" | "0o" | "0b" )? digit+

let lowerletter = ['a'-'z' '\223'-'\246' '\248'-'\255' '_']

let upperletter = ['A'-'Z' '\192'-'\214' '\216'-'\222']

let identletter = lowerletter | upperletter | digit | '\'' 
                 
let lident = lowerletter identletter*
let cident = upperletter identletter*

(* included from lexer.mll *)
let backslash_escapes =
  ['\\' '"' '\'' 'n' 't' 'b' 'r']
                                    

rule token = parse
| whitespace   { token lexbuf }
| newline      { newline lexbuf; token lexbuf }
| "(*"         { in_comment := true;
                 comment [Locations.curr_loc lexbuf] lexbuf;
                 token lexbuf }
| "->"         { ARROW }
| "=>"         { DOUBLEARROW }
| "."          { DOT }
| ":"          { COLON }
| "::"          { COLONCOLON }
| ","          { COMMA }
| ";"          { SEMI }
| "="          { EQUAL }
| "("          { LPAREN }
| ")"          { RPAREN }
| "["          { LBRACKET }
| "]"          { RBRACKET }
| "{"          { LBRACE }
| "}"          { RBRACE }
| "<"          { LANGLE }
| ">"          { RANGLE }
| "#include"   { INCLUDE }
| "#option"    { OPTION }
| "$"          { DOLAR }
| "*"          { STAR }
(* | "-"          { MINUS }
 * | "+"          { PLUS  } *)
| integer as i { INT (int_of_string i) }
| lident as s  { unless_keyword (fun s -> LIDENT s) s }
| cident as s  { unless_keyword (fun s -> CIDENT s) s }
| eof          { EOF }
| '"'          { reset_string_buffer();
                 string (Locations.curr_loc lexbuf) lexbuf;
                 STRING (get_stored_string()) }
| _ as c       { let pos = Locations.curr_loc lexbuf in
                 raise (Error.Lexing (Error.InvalidChar (pos, c))) }

and comment depth = parse
| "*)"         { match depth with
                 | [] -> assert false
                 | [_] -> in_comment := false
                 | _ :: outer -> comment outer lexbuf }
| "(*"         { comment (Locations.curr_loc lexbuf :: depth) lexbuf }
| newline      { newline lexbuf;
                 comment depth lexbuf }
| eof          { in_comment := false;
                 let pos = List.hd depth in
                 raise (Error.Lexing (Error.OpenComment pos)) }
| _            { comment depth lexbuf }

(* included from ocaml lexer.mll *)
(* String parsing comes from the compiler lexer *)
and string loc = parse
    '"'
    { () }
   | '\\' ("\010" | "\013" | "\013\010") ([' ' '\009'] * as spaces)
    { incr_loc lexbuf (String.length spaces);
      string loc lexbuf }
  | '\\' (backslash_escapes as c)
    { store_string_char(char_for_backslash c);
      string loc lexbuf }
  | '\\' (['0'-'9'] as c) (['0'-'9'] as d) (['0'-'9']  as u)
    { let v = decimal_code c d u in
      if in_pattern () && v > 255 then
       warning lexbuf
        (Printf.sprintf
          "illegal backslash escape in string: `\\%c%c%c'" c d u) ;
      store_string_char (Char.chr v);
      string loc lexbuf }
 | '\\' 'x' (['0'-'9' 'a'-'f' 'A'-'F'] as d) (['0'-'9' 'a'-'f' 'A'-'F'] as u)
    { store_string_char (char_for_hexadecimal_code d u) ;
      string loc lexbuf }
  | '\\' (_ as c)
    {if in_pattern () then
       warning lexbuf
        (Printf.sprintf "illegal backslash escape in string: `\\%c'" c) ;
      store_string_char '\\' ;
      store_string_char c ;
      string loc lexbuf }
  | eof
     { raise (Error.Lexing (Error.OpenString loc)) }
  | '\010'
    { store_string_char '\010';
      incr_loc lexbuf 0;
      string loc lexbuf }
  | _ as c
    { store_string_char c;
      string loc lexbuf }
