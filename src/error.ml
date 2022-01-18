open Format
open Locations

(** Parsing and Lexing errors *)

type lexing_error =
  | InvalidChar of location * char
  | OpenComment of location
  | OpenString of location

type parsing_error =
  | Unclosed of (string * location) * string * (string * location)
  | Parse of string * location
  
exception Lexing of lexing_error
exception Parsing of parsing_error

let report_lexing ppf = function
  | InvalidChar (loc, c) ->
      print_loc ppf loc;
      fprintf ppf "Illegal character %s\n" (Char.escaped c);
  | OpenComment loc ->
      Locations.print_loc ppf loc;
      fprintf ppf "Unterminated comment\n";
  | OpenString loc ->
      print_loc ppf loc;
      fprintf ppf "Unterminated string\n"

let report_parsing ppf = function
  | Parse (explain, loc) ->
     print_loc ppf loc;
     fprintf ppf "Syntax error: %s\n" explain
  | Unclosed ((opening, opening_loc), _decl, (closing, closing_loc)) ->
     fprintf ppf "%aSyntax error: '%s' expected\n"
       print_loc closing_loc closing;
     fprintf ppf "%aThis '%s' might be unmatched\n"
       print_loc opening_loc opening

(* diff *)
let report_parser_error lexbuf msg =
  print_loc Format.err_formatter (curr_loc lexbuf);
  fprintf Format.err_formatter "%s\n%!" msg;;
(* /diff *)

let handle_parsing parser lexbuf =
  let ppf = Format.err_formatter in
  try parser lexbuf with
  (* | Parser.Error -> report_parser_error lexbuf "Parsing error"; exit 2  *)
  | Parsing err -> report_parsing ppf err; exit 1
  | Lexing err -> report_lexing ppf err; exit 1
                
(** Typing errros *)

open Syntax
open Print

type shape =
  | Sarr  
  | Srcd  of lab option
  | Sprod of int option
  | Sexi  
  | Sall  

let string_of_shape s =
  match s with
  | Sarr  -> "arrow"
  | Srcd None  -> "record"
  | Sprod None -> "tuple"
  | Srcd (Some lab)  -> "record with label " ^ lab
  | Sprod (Some i) -> "tuple of length at most " ^ string_of_int i
  | Sexi  -> "existential"
  | Sall  -> "forall"
   
type 'a expected =
  | Matching of shape
  | Nonequal of 'a 
  | Showdiff of 'a * 'a * 'a

type typing_error =
  |  Kinding of styp * kind * kind expected
  |  Unbound of (styp option * svar, evar) typorexp
  |  Expected of ctyp * ctyp expected
  |  Escaping of ctyp  * cvar
  |  Annotation of evar
  |  NotImplemented of string

exception Typing of location option * typing_error
let error_ loc err = raise  (Typing (loc, err))
let error_unloc = error_ None
let error exp = error_ (Some exp.loc)

let within_loc f t =
  try f t.obj with Typing (None, err) -> error t err

let within_typ f t =
  try f t with
  | Typing (loc, Unbound (Typ (None, a))) ->
     error_ loc (Unbound (Typ (Some t, a)))

exception Failed
let expected_success =
  Util.spec_true "--fail" "Tell that failure is expected"
  
let handle_typing_with ctyp f x =
  let chan = if !expected_success then stderr else stdout in
  let print_lines = print_lines chan in
  let expected str print info =
    match info with
    | Matching s ->
       print_lines
         [[ !^ ("Expected " ^ str ^ " shape:  "); !^(string_of_shape s) ]]
    | Nonequal t ->
       print_lines
         [[ !^  ("Expected " ^ str ^ ":  "); print t ]];
    | Showdiff (t, t1, t2) ->
       print_lines
         [[ !^("Expected " ^ str ^ ":  "); print t ];
          [ !^"-- in actual:   "; print t1 ]; 
          [ !^"-- in expected: "; print t2; ]] in
  
  let explain loc err =
    let () =
      match loc with
      | Some loc -> Printf.fprintf chan "%s\n%!" (string_loc loc);
      | None -> () in
    
    match err with
    | Kinding (t, k1, k2) ->
       print_lines
         [[ !^ "Kinding error:" ];
          [ !^ "In type:  " ; styp t ];
          [ !^ "Actual   kind:  "; kind k1 ]];
       expected "kind" kind k2

    | Expected (t1, (t2 : ctyp expected)) ->
       print_lines
         [[ !^ "Typing error: mistmatch between: " ];
          [ !^ "Actual type:    "; ctyp t1 ]];
       expected "type" ctyp t2

    | Unbound (Exp x) ->
       print_lines
         [[ !^ "Unbound expession variable: "; evar x ]]

    | Unbound (Typ (t, a)) ->
       print_lines
         [[ !^ "Unbound type variable: "; svar a ]];
       Option.iter (fun t -> print_lines [[ !^"In type:  "; styp t ]]) t

    | Escaping (t, a) ->
       print_lines
         [[ !^"Typing error: out of scope variable "; cvar a];
          [ !^"in actual type:  "; ctyp t ]]

    | Annotation x -> 
       print_lines
         [[ !^"Unnanotated program variable: "; evar x; ]]
    | NotImplemented str -> 
       print_lines
         [[ !^"Construct implemented: "; !^str; ]]

  in
  try f x with Typing (loc, err) -> explain loc err; raise Failed

let expect_success f x =
  let actual r =
    let signal b str =
      Printf.fprintf (if b then stdout else stderr)  "%s\n%!" str;
      exit (if b then 0 else 2)
    in
    match !expected_success, r with
    | true, true -> ()
    | false, false -> signal true "Expected failure is ok!"
    | true, false -> exit 1
    | false, true -> signal false "Error: unexpected success!"
  in
  try f x; actual true with Failed -> actual false


