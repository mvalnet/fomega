type 'a loc = 'a Locations.loc =
  { obj: 'a;
    loc: Locations.location;
  }

let with_loc = Locations.with_loc
let map_loc = Locations.map_loc

type evar = string 
let evar n = n 


type kind = Ktyp | Karr of kind * kind

let default_kind = Ktyp

type prim_typ = Tint | Tbool | Tstring | Tunit
                                       
type prim_val =
  | Int of int
  | Bool of bool
  | String of string

type lab = string

type binder =
  | Tlam
  | Tall
  | Texi

type 'a typ = 
  | Tvar  of 'a
  | Tprim of prim_typ
  | Tapp  of 'a typ * 'a typ
  | Tprod of 'a typ list
  | Trcd of (lab * 'a typ) list
  | Tarr  of 'a typ * 'a typ
  | Tbind of binder * 'a * kind * 'a typ

type svar = string   
type styp = svar typ
type styp_loc = styp loc

type cvar = { name: string; id : int; def : def option }
and def = { scope : int; typ : ctyp}
and ctyp = cvar typ

type pat = pat_ loc
and pat_ =
  | Pvar  of evar
  | Ptyp  of pat * styp_loc
  | Pprod of pat list
  | Pprim of prim_val

type ('a, 'b) typorexp = Typ of 'a | Exp of 'b
type binding = (svar * kind, pat) typorexp

type exp = exp_ loc
and exp_ =
  | Evar  of evar
  | Efun  of binding list * exp
  | Eappl of exp * (styp_loc, exp) typorexp list
  | Elet  of bool * pat * exp * exp
  | Eprod of exp list
  | Ercd  of (lab * exp) list
  | Elab of exp * lab
  | Eproj of exp * int
  | Eprim of prim_val
  | Eannot of exp * styp_loc
  | Epack of styp_loc * exp * styp_loc
  | Eopen of svar * evar * exp * exp
                          
type decl = decl_ loc
and decl_ =
  | Dtyp of svar * (kind, styp_loc) typorexp
  | Dlet of bool * pat * exp
  | Dopen of svar * evar * exp

type program = decl list

type 'a typed_decl_ =
  | Gtyp of 'a * (kind, kind * 'a typ) typorexp
  | Glet of evar * 'a typ
  | Gopen of 'a * evar * 'a typ
type typed_decl = cvar typed_decl_

type directive = Include of string | Flag of string           

(* type 'a idecl = 
 *   | Ival of evar * 'a typ
 *   | Ityp of 'a * (kind, kind * 'a typ) typorexp *)

type interface = svar typed_decl_ list

(* fresh variables *)
let svar n = n

let global_def = ref 0
let next r = incr r; !r
let make_def t = { typ = t; scope = next global_def }
let cmp_def t1 t2 = Int.compare t1.scope t2.scope
let cvar n = { name = n; id = -1; def = None }

let global_id = ref 0
let fresh_id() = next global_id    
let refresh v = { v with id = fresh_id() }
