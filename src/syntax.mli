(** The type ['a loc] is used to recursively wrap expressions and patterns
   with source locations, For convenience, we alias it in module [Syntax] to
   avoid always depending on module [Location]. *)

type 'a loc = 'a Locations.loc = { obj : 'a; loc : Locations.location; }

(** We also reexport two helper functions [with_loc] and [map_loc] from 
   module [Location] *)
val with_loc : 'a loc -> 'b -> 'b loc
val map_loc : ('a -> 'b) -> 'a loc -> 'b loc

 
(** The representation of variable is an important design choice.

   On source expressions, both program and type variables are just strings.
   These are the types [evar] for expression variables and [svar] for type
   variables. *)

type evar = string
type svar = string   

(** To allow for further changes of the type evar, we use smart
   constructors [evar] and [svar] to generate a source variables
   from a name. Both functios are currently the identity. *)

val evar : string -> evar
val svar : string -> svar
                                        
(** Internally, however, we need to compute with types and rename type
   variables to avoid clashs. Hence type variables need another internal
   representation

   We choose to represent both free and bound variables *by name*.

   An name internal variable of type [cvar] is uniquely identified by a pair
   of a string field [name] (its original name) and an integer suffix [id].
   Since variable are also used to name type definitions, which are expended
   lazily, [cvar] also contain a field [def] which is an option type: [None]
   menas that variable is abtract, which [Some t] means that the variable
   actually stand for type [t], and may be unfolded on demand.

   Hence, the representation of types will differ between source types
   [styp] and internal types [ctyp]---but only by their representations of
   variables.

   We can factor this difference by abracting the type of types over the
   representation of varibales as ['a typ].
*)

(** Kinds of F-omega are represnted as follows *)

type kind = Ktyp | Karr of kind * kind

(** Since `Type` is the most frequent kind, we may omit it in the source
   syntax.  To be able to change this we use [default_kind] for omitted
   kinds, which is thus currenly [Ktyp]. *)
val default_kind : kind

(** Constant types and constant expressions *)
type prim_typ = Tint | Tbool | Tstring | Tunit
type prim_val = Int of int | Bool of bool | String of string

(** Record labels *)
type lab = string

(** Finally, here is the representation ['a typ] of types. *)         

(** We factor out the thee form of binders *)         
type binder = Tlam | Tall | Texi

type 'a typ = 
  | Tvar  of 'a
  | Tprim of prim_typ
  | Tapp  of 'a typ * 'a typ
  | Tprod of 'a typ list
  | Trcd of (lab * 'a typ) list
  | Tarr  of 'a typ * 'a typ
  | Tbind of binder * 'a * kind * 'a typ

(** We may now define source types *)           
type styp = string typ

(** Internally, types are not located.  However, expressions will be located.
  as well as types in expression *)

type styp_loc = styp loc

(** Patterns and expressions are recursively located, so that we can easily
   repport type errors. For this purpose, we recursively defind [exp] the
   external located expressions and [exp_] raw expressoins stipped of their
   location and similarly for patterns. *)

(** Expression bindings. *)
type pat = pat_ loc
and pat_ =
    Pvar of evar
  | Ptyp of pat * styp_loc
  | Pprod of pat list
  | Pprim of prim_val

(** Both functions an application are n-ary. This is convenient in the
   source syntax, but may also be convenient for typing with some local form
   of inference. *)

(** Moreover, we may alternate type and expessions both in parameters of
   functions and in arguments of application.  We use the helper union type
   [typorexp] to distinguish them: *)

type ('a, 'b) typorexp = Typ of 'a | Exp of 'b

(** We also introduce an auxiliary type [binding] for parameters of funtions *)
type binding = (svar * kind, pat) typorexp
                            
(** Expressions. *)
type exp = exp_ loc
and exp_ =
    Evar of evar
  | Efun of binding list * exp
  | Eappl of exp * (styp_loc, exp) typorexp list
  | Elet of bool * pat * exp * exp
  | Eprod of exp list
  | Ercd of (lab * exp) list
  | Elab of exp * lab
  | Eproj of exp * int
  | Eprim of prim_val
  | Eannot of exp * styp_loc
  | Epack of styp_loc * exp * styp_loc
  | Eopen of svar * evar * exp * exp

(** Declarations are either expression bindings or type declarations.  Type
   declarations may either define a type alias (as in OCaml), or introduce a
   new abstract type---which be used to model type generativity.  *)           
type decl = decl_ loc
and decl_ =
  | Dtyp of svar * (kind, styp_loc) typorexp
  | Dlet of bool * pat * exp
  | Dopen of svar * evar * exp
          

(** Source programs are just list of declarations *)
type program = decl list

type directive = Include of string | Flag of string           

(** 2. Elaborated types *)

(** internal type variables [cvar] and internal types [ctyp], are
   recursively defined because variables representing definitions contrain
   their definitions.  Definitions must be well-founded (recursive type
   definitions are disallowed).  So we can number them accordingly,
   which is used to perform unfolding of definitions in a youngest-first
   order when checking for convertibility. *) 
type cvar = { name: string; id : int; def : def option }
and def = { scope : int; typ : ctyp}
and ctyp = cvar typ


(** We also introduce a type [typed_decl] for typed declarations, where type
   variables are now of type [ctyp] and expressions definition are replaced
   by their types. *)

type 'a typed_decl_ =
  | Gtyp of 'a * (kind, kind * 'a typ) typorexp
  | Glet of evar * 'a typ
  | Gopen of 'a * evar * 'a typ
type typed_decl = cvar typed_decl_

(** Syntax for interface files *)
(* type 'a idecl =
 *   | Ival of evar * 'a typ
 *   | Ityp of 'a * (kind, kind * 'a typ) typorexp *)

type interface = svar typed_decl_ list



val cmp_def : def -> def -> int
val make_def : ctyp -> def
  

val cvar : svar -> cvar

(** [fresh_id] generates a few positive integer every time it is call *)
val fresh_id : unit -> int
val refresh : cvar -> cvar

