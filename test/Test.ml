(* This script produces the file [dune.auto], which describes the tests we
   would like dune to execute. *)

open Printf
open Sys
open Array
open List
open Filename
open DuneRule

type filename =
  string
let has_suffix suffix name =
  check_suffix name suffix

(* -------------------------------------------------------------------------- *)

(* Creating a phony target and recording its name in a growing list. *)

let targets =
  ref []

let target basename mode =
  let target = sprintf "%s.%s.target" basename mode in
  targets := target :: !targets;
  target

let targets () =
  List.rev !targets

(* -------------------------------------------------------------------------- *)

(* Running a positive test. *)

(* The file %.fw  is the source file.
   The file %.exp is the expected output.
   The file %.out is the output. *)

let modes =
  [ "lazy"; "eager" ]

let process_positive_test command sourcedir filename : unit =
  let basename = chop_extension filename in
  (* We perform two tests: in test 1, we execute the source file; in test 2,
     we typecheck it. *)
  modes |> List.iter (fun mode ->
      (* In each test, we process the source file and check if the actual
         output in [%.out] matches the expected output in [%.exp]. The
         messages printed on the error channel are logged in the file
         [%.err], but are not compared against a reference. *)
    run_and_compare
      (target basename mode)
      command [A  (sprintf "--%s" mode)]
      sourcedir
      filename
      (sprintf "%s.%s.out" basename mode)
      (sprintf "%s.%s.err" basename mode)
      (sprintf "%s.%s.exp" basename mode)
  )

(* -------------------------------------------------------------------------- *)

(* Running all tests. *)

let () =
  print_endline
    ";; This file has been auto-generated. Please do not edit it.\n\
     ;; Instead, edit ../Test.ml (if needed),\n\
     ;; then run [make depend] at the top level.\n"

(* When this script is executed, the current directory is [test/inputs].
   So, the command that we want to test is [../../src/main.exe], and the
   directory where the input files are found is [.]. *)

let command =
  "../../src/main.exe"

let sourcedir =
  "."

let filenames : filename list =
  readdir sourcedir
  |> to_list
  |> filter (has_suffix ".fw")
  |> sort Stdlib.compare

let () =
  iter (process_positive_test command sourcedir) filenames;
  alias "runtest" (targets())
