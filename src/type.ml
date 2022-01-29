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

(** We maintain for each name, the highest suffix appearing in scope *)
module Senv = Map.Make (struct
    type t = string
    let compare = String.compare
  end)

let apply_with_default t su a : ctyp =
  try Tenv.find a su with Not_found -> t

let apply (su : ctyp Tenv.t) (a : cvar) =
  apply_with_default (Tvar a) su a

(** Kind equality *)
let rec eq_kind k1 k2 =
  match k1, k2 with
    | Ktyp, Ktyp -> true
    | Karr(k1_1, k1_2), Karr(k2_1, k2_2) ->
      eq_kind k1_1 k2_1 && eq_kind k1_2 k2_2
    | _ -> false

(** Type substitution as opposed to renaming *)
let rec subst (su :ctyp Tenv.t) (t : ctyp) : ctyp =
  match t with
    | Tvar(v) -> apply su v
    | Tprim(_) -> t
    | Tapp(t1, t2) -> Tapp(subst su t1, subst su t2)
    | Tarr(t1, t2) -> Tarr(subst su t1, subst su t2)
    | Tprod(typ_list) ->
      (Tprod(
        List.fold_left
          (fun l t -> (subst su t)::l )
          []
          typ_list
      ) : ctyp)
    | Trcd(ltyp_list) ->
      Trcd(
        List.fold_left
          (fun l (lab,t) -> (lab, subst su t)::l )
          []
          ltyp_list
      )
    | Tbind(b, x, k, t) ->
      Tbind(b, x, k, subst su t)

    
let subst_typ (a : Tenv.key) (ta : ctyp) t =
  let su = Tenv.singleton a ta in
    subst su t

(** Type normalization *)
let eager =
  spec_false "--eager" "Eager full reduction and definition expansion"

(** We still provide the --lazy option, even though this is the default *)
let _lazy =
  spec_add "--lazy" (Arg.Clear eager)
    "Lazy definition expansion and reduction to head normal forms"

let norm t1 = t1
let eq_typ t1 t2 = compare t1 t2 = 0

let eq_binder b1 b2 =
  match b1, b2 with
  | Tlam, Tlam | Tall, Tall | Texi, Texi -> true
  | _ -> false

let eq_cvar v1 v2 =
  v1.name = v2.name && v1.id = v2.id

let eq_prim p1 p2 =
  match p1, p2 with
  | Tint, Tint | Tbool, Tbool
  | Tstring, Tstring | Tunit, Tunit -> true
  | _ -> false

let rec recurse_if_equal h1 h2 q1 q2 =
  match diff_typ h1 h2 with
  | None -> diff_typ q1 q2
  | Some(_) as l -> l

and diff_typ t1 t2 = 
  match t1, t2 with
  | Tvar(v1), Tvar(v2) ->
    if eq_cvar v1 v2 then None
    else Some(t1,t2)
  
  | Tprim(p1), Tprim(p2) -> 
    if eq_prim p1 p2 then None
    else Some(t1, t2)

  | Tapp(f1, a1), Tapp(f2, a2)
  | Tarr(f1, a1), Tarr(f2, a2) ->
    recurse_if_equal f1 f2 a1 a2
  
  | Tprod([]), Tprod([]) | Trcd([]), Trcd([]) -> None
  | Tprod([]), _ | _, Tprod([])
  | Trcd([]), _  | _, Trcd([]) -> Some(t1, t2)

  | Tprod(h1::q1), Tprod(h2::q2) ->
    recurse_if_equal h1 h2 (Tprod q1) (Tprod q2)

  | Trcd((l1,h1)::q1), Trcd((l2,h2)::q2) ->
    if l1 <> l2 then
      Some(t1,t2)
    else
      recurse_if_equal h1 h2 (Trcd q1) (Trcd q2)

  | Tbind(b1,x1,k1,body1), Tbind(b2,x2,k2,body2) ->
    if eq_binder b1 b2 && eq_cvar x1 x2 && eq_kind k1 k2 then
      diff_typ body1 body2
    else Some(t1, t2)

  | _ -> Some(t1, t2)

