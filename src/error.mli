(** Lexing and parsing errors *)

type lexing_error =
    InvalidChar of Locations.location * char
  | OpenComment of Locations.location
  | OpenString of Locations.location
type parsing_error =
    Unclosed of (string * Locations.location) * string *
      (string * Locations.location)
  | Parse of string * Locations.location

exception Lexing of lexing_error
exception Parsing of parsing_error

(* diff *)
val  report_parser_error : Lexing.lexbuf -> string -> unit
(* /diff *)

val handle_parsing : ('a -> 'b) -> 'a -> 'b

(** Typing errors *)

open Locations
open Syntax

(** type [shape] is used to report mismatching, when some type is not of the
   expected shape *)
type shape =
  | Sarr  
  | Srcd  of lab option
  | Sprod of int option
  | Sexi  
  | Sall  

(** ['a expected] is used to report the expected ['a], which may be a [kind]
   or a semantic type. [Matching s] describes the expected shape [s];
   [Nonequal t] describes the expected (kind or type) [t], while [Showdiff
   (t, u, v)] also reports a finer difference between [u] and [v]: that is
   [u] and [v] are subterms of the actual and expected types, respectively,
   that witness the disequality between the actual and expected types.  *)
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

val error : 'a loc -> typing_error -> 'b
val error_unloc : typing_error -> 'b
val within_loc  : ('a -> 'b) -> 'a loc -> 'b
val within_typ  : (styp -> 'b) -> styp -> 'b

val handle_typing_with : (ctyp -> Print.doc) -> ('a -> 'b) -> 'a -> 'b
val expected_success : bool ref


(** [expect_success f x] evaluated [f x] as usual if the value of
   [!expected_success] is true; otherwises it turns success into failure and
   faillue into success (and prints typing-error messages in [stdout]
   instead of [stderr] *)
val expect_success : ('a -> unit) -> 'a -> unit
