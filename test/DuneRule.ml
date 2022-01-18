open PrintSExp

(* Constructing a standard [make]-like rule. *)

let target (targets : string list) =
  let keyword = if List.length targets = 1 then "target" else "targets" in
  L (atom keyword :: atoms targets)

let rule (targets : string list) (deps : string list) (action : sexp) =
  L[A"rule";
    target targets;
    L(A"deps" :: atoms deps);
    L[A"action"; action]
  ]

(* Constructing a phony rule, that is, a rule whose target is an alias. *)

let phony (alias : string) (action : sexp) =
  L[A"rule";
    L[A"alias"; A alias];
    L[A"action"; action]
  ]

(* Constructing a diff action. *)

let diff (expected : string) (actual : string) =
  L[A"diff"; A expected; A actual]

(* Redirecting the output channels of an action towards a file. *)

(* At the time of writing (2.7.1), dune has a bug that causes it to send
   an ill-formed command to the shell if both stdout and stderr are
   redirected to the same file. *)

let redirect_stdout filename action =
  L[A"with-stdout-to"; A filename; action]

let redirect_stderr filename action =
  L[A"with-stderr-to"; A filename; action]

(* Changing the working directory of an action. *)

let chdir directory action =
  L[A"chdir"; A directory; action]

(* Expressing the fact that an action is expected to fail. *)

let expecting_failure action =
  L[A"with-accepted-exit-codes"; L[A"not"; A"0"]; action]

let possibly_expecting_failure positive action =
  if positive then action else expecting_failure action

(* Constructing (and printing) a pair of rules to run a command
   and compare its output against an expected-output file.

   [target]     the name of the target that we are defining
   [command]    short name of the command
   [args]       arguments (beyond the file name) for this command
   [source]     directory where the source file resides
   [filename]   short name of the source file
   [stdout]     short name of the stdout output file
   [stderr]     short name of the stderr output file
   [expected]   short name of the expected stdout output file

   The content of the file [stderr] is not compared against a
   reference. *)

let (/) =
  Filename.concat

let run_and_compare
    target command args sourcedir filename stdout _stderr expected =
  let _experror = expected ^ "err" in
  print (rule
    [sourcedir/stdout]
    [sourcedir/filename]
    (redirect_stdout (sourcedir/stdout) (
      L(A"run" :: A command :: A (sourcedir/filename) :: args)
  )));
  print (phony target (
    diff (sourcedir/expected) (sourcedir/stdout)
  ))
  (* ; print (phony target (
   *     diff (sourcedir/experror) (sourcedir/stderr)
   * )) *)

(* Constructing (and printing) a target that is an alias for a
   conjunction of targets. *)

let alias target deps =
  print
    (L[A"alias";
       L[A"name"; A target];
       Lnewline(A"deps" :: List.map (fun dep -> L[A"alias"; A dep]) deps)])
