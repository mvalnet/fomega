open Syntax

type doc = PPrint.document

val ( ^^ ) : doc -> doc -> doc
val ( !^ ) : string -> doc
val ( ^^^ ) : doc -> doc -> doc
val ( ^/^ ) : doc -> doc -> doc
         
val evar : evar -> doc
val svar : svar -> doc
val var : (svar, evar) typorexp -> doc

val cvar : cvar -> doc
val dvar : int -> cvar -> doc

val kind : kind -> doc
val styp : styp -> doc
val ctyp : ctyp -> doc
val typ : ('a -> doc) -> 'a typ -> doc

val pat : pat_ loc -> doc
val binding : binding -> doc
val exp : exp -> doc
val decl : decl_ -> doc
val typed_decl : (cvar -> doc) -> typed_decl -> doc

val string : doc -> string
val print : out_channel -> doc -> unit
val print_lines : out_channel -> doc list list -> unit

val prerr : doc list -> unit
val prerr_lines : doc list list -> unit
val prerr_str : string list -> unit

(** For debugging purposes *)
val prerr_styp : string -> styp -> unit
val prerr_ctyp : string -> ctyp -> unit

(** Kinds `Type` are omitted when [show_Type] is unset (default). Use
   command line opion `--show_Type` to set. *)
val show_Type : bool ref

(** [def] field of [tvar] type is for lazy expansion of definition.  When
   printing types. definitions are folded unless [show_def] is set with
   command line option `--show_Type`, in which case its expansion is printed
   in brackets.  This is only usefull for debuging purposes, as such types
   cannot be parsed back.*)
val show_def : bool ref
