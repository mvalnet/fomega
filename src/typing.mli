open Syntax

type env

(* 

(** We keep these for documentation, but they should not be exported *)
val empty_env : env
  
(** functions to modify the environment accordingly. Same semantics as maps,
   except for the order of arguments. *)
val add_evar : env -> evar -> ctyp -> env
val add_svar : env -> svar -> cvar -> env
val add_cvar : env -> cvar -> kind -> env

(** functions to query the environment accordingly. Same semantics as maps,
   except for the order of arguments. In particular all `find_xvar`
   functions raise the exception [Not_found] when their argument is not in
   the environment. *)
val find_evar : env -> evar -> ctyp
val find_svar : env -> svar -> cvar
val find_cvar : env -> cvar -> kind
*)



val type_decl : env -> decl -> env * typed_decl
val type_program : env -> decl list -> env * typed_decl list

val initial_env : env
val initial_program : typed_decl list

(** By default, [do_minimize] is set, which means that types [id] field in
   types will be minimzed so as to display type variables will lower
   integer suffixes. This can be canceled with the `--rawtypes` command-line
   option. *)  
val do_minimize : bool ref

(** [minimize_typ t] returns a term that is alpha-equivalent to [t] use
   minimal suffixes without shadowing other variables, unless the flag
   [doₘminimize] is unset, in which case it just returns [t]. *) 
val minimize_typ : env -> ctyp -> ctyp

