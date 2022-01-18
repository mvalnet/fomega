(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-27-32-33-37-39-60"]
open Util
open Syntax

module Tenv = Map.Make (struct
    type t = cvar
    let compare u v =
      let uv = Int.compare u.id v.id in
      if uv = 0 then String.compare u.name v.name
      else uv
  end)

(** Renaming tvars *)

(** Computations may introduce, auxiliary fresh that have disapeared after
   normalization. When done, we may rename types to minimize the numeric
   suffixes of type variables.  *)

(** We mainting for each name, the highest suffix appearing in scope *)
module Senv = Map.Make (struct
    type t = string
    let compare = String.compare
  end)

let apply_with_default t su a =
  try Tenv.find a su with Not_found -> t

let apply su a = apply_with_default a su a

(** Kind equality *)
let rec eq_kind k1 k2 =
     true

(** Type substitution as opposed to renaming *)
let rec subst su (t : ctyp) : ctyp =
     t (* fix me *)

let subst_typ a ta t =
     t (* fix me *)

(** Type normalization *)
let eager =
  spec_false "--eager" "Eager full reduction and definition expansion"

(** We still provide the --lazy option, even though this is the default *)
let _lazy =
  spec_add "--lazy" (Arg.Clear eager)
    "Lazy definition expansion and reduction to head normal forms"

let norm t1 = t1
let eq_typ t1 t2 = compare t1 t2 = 0
let diff_typ t1 t2 = None (* fix me *)



