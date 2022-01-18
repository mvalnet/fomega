open Util
open Syntax
open Error 
open Typing

(** Parsing functions *)
let parse parser lexbuf =
  handle_parsing (parser Lexer.token) lexbuf

let parse_string parser src =
  let lexbuf = Lexing.from_string src in
  let () = Locations.set_source (Locations.String src) in
  parse parser lexbuf

let parse_chan chan =
  let lexbuf = Lexing.from_channel chan in
  let () = Locations.set_source (Locations.Stdin lexbuf) in
  parse Parser.program 

let parse_file filename =
  let chan =
    try open_in filename
    with Sys_error  mes -> 
      Printf.eprintf "Openfile error: %s\n%!" mes; exit 2 in
  let lexbuf = Lexing.from_channel chan in
  let () = Locations.set_source (Locations.File (filename, lexbuf)) in
  Lexing.set_filename lexbuf filename;
  parse Parser.program lexbuf

(** Flags driven by command line arguments *)

let do_reprint   = spec_false  "--reprint"    "print after parsing or reparsing"
let do_reparse   = spec_false  "--reparse"    "reparse and compare"
let do_showtypes = spec_true   "--no-types"   "do not show inferred types"
let do_typing    = spec_true   "--no-typing"  "do not typecheck"

let included = ref []
let include_file s = included := s :: !included
let () = spec_add "--include" (Arg.String include_file) "include [file]"
let () = spec_alias "-I" "--include"

(** Printing a source program *)
let print_prog p =
  let decl d = 
      Print.print stdout (Print.decl d.obj); 
      print_newline(); print_newline ()
  in
  List.iter decl p 

(** [reparse p] checks that the printing of program [p] can be sucessfully 
    reparses and is identical to [p] *)
let reparse p =
  let decl (d : decl) = 
    let s = Print.string (Print.decl d.obj) in
    let d' : decl = parse_string Parser.decl_ s in
    let s' = Print.string  (Print.decl d'.obj) in
    if s <> s' then
      begin
        prerr_endline "*** Differrence!";
        prerr_endline s';
        prerr_newline ();
      end
  in
  List.iter decl p

(** Printing the inferred program interface *)
let print_typed_prog _env p =
  (* [_env] could be used in extension to rebase variable names *)
  let decl d =
    Print.print stdout (Print.typed_decl Print.cvar d);
    print_newline () in
  List.iter decl p 

let arg_files = ref []
let add_file name = arg_files := name :: !arg_files

let usage_msg = "./fomega [ options ] file_1 .. file_n"

let process_program verbose env p = 
  let env = 
    if !do_typing then
      let env, p = type_program env p in
      let () = if !do_showtypes && verbose then print_typed_prog env p in
      env 
    else
      env in
  env
    
let rec process_file verbose env name =
  let directives, p = parse_file name in
  let directive env d =
    match d with
    | Include file ->
        process_file false env file
    | Flag "fail" ->
        if verbose then Error.expected_success := false;
        (* otherwise ignore *)
        env
    | Flag s ->
        Printf.eprintf "Unknown directive flag: %s\n%!" s;
        exit 1
  in
  let env = List.fold_left directive env directives in
  if !do_reprint && verbose then print_prog p; 
  if !do_reparse && verbose then reparse p;
  let env =
    let ctyp t = Print.ctyp (minimize_typ env t) in
    if !do_typing then
      let env, p = handle_typing_with ctyp (type_program env) p in
      let () = if !do_showtypes && verbose then print_typed_prog env p in
      env 
    else
      env in
  env

let () = Arg.parse (List.sort compare !spec_list) add_file usage_msg

let main() =
  let env = initial_env in
  let verbose = verbose_level 2 in
  let () = if verbose then print_typed_prog env initial_program in
  let included = List.rev !included in
  let files = List.rev !arg_files in
  let env = List.fold_left (process_file verbose) env included in
  let _ = List.map (process_file !do_showtypes env) files in
  ()

let () =  expect_success main ()
