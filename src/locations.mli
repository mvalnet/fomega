type 'a loc = { obj : 'a; loc : location; }
and location = {
  loc_start : Lexing.position;
  loc_end : Lexing.position;
  loc_ghost : bool;
  loc_source : source;
  loc_string : string option;
}
and source =
    String of string
  | File of string * Lexing.lexbuf
  | Toplevel of Lexing.lexbuf
  | Stdin of Lexing.lexbuf
  | Unknown

val with_loc : 'a loc -> 'b -> 'b loc
val map_loc : ('a -> 'b) -> 'a loc -> 'b loc

val loc_source : source ref
val set_source : source -> unit
val get_source : unit -> source
val get_loc_string :
  source -> Lexing.position -> Lexing.position -> string option
val loc_aux :
  ?source:source -> bool -> Lexing.position -> Lexing.position -> location
val loc_ : Lexing.position -> Lexing.position -> location
val dummy_loc : location
val dummy_located : 'a -> 'a loc
val string_pos : int -> Lexing.position
val loc_of_string : string -> location
val loc :
  ?source:source ->
  ?ghost:bool -> 'a -> Lexing.position -> Lexing.position -> 'a loc
val noloc : 'a -> 'a loc
val curr_loc : Lexing.lexbuf -> location
val merge_source : source -> source -> source
val join : location -> location -> location
val string_of_loc : location -> string
val string_loc : location -> string
val print_loc : Format.formatter -> location -> unit
