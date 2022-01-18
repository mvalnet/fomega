(** Helper library functions *)

val map_snd : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list
val iter_snd : ('a -> unit) -> ('c * 'a) list -> unit

(** Helper for command line options *)
val spec_list : (string * Arg.spec * string) list ref

val spec_add : string -> Arg.spec -> string -> unit
val spec_bool : bool ref -> string -> string -> unit
val spec_flip : bool ref -> string -> string -> unit

(** [spec_bool_new b arg doc] creates a new flag set to [b] by default and
   returned. The flag can be inverted by command line argument [arg]. [doc]
   is a short document string that for usage help. *)
val spec_bool_new : bool -> string -> string -> bool ref
val spec_false : string -> string -> bool ref
val spec_true  : string -> string -> bool ref

val spec_alias  : string -> string -> unit

(** By defaul [verbose] is set to [0]. This can be increased by the commmand
   line option "--verbose" or its alias "-v". *)
val verbose : int ref

(** [verbose_level n] returns the value of [!verbose > n] i.e.
   [verbose_level 0] means no verbosity *)
val verbose_level : int -> bool
                                       
