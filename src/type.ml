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


let struct_eq_cvar c1 c2 =
  c1.name = c2.name && c1.id = c2.id

(** [rename] replaces every occurrence of the first argument by
   the second argument in the body of the third argument **)
let rec rename cvar cvar_ctyp ctyp =
  match ctyp with 
  | Tvar(cvar') -> 
    if struct_eq_cvar cvar cvar' then 
      cvar_ctyp
    else ctyp
  | Tprim(_) -> ctyp
  | Tapp(ctyp1, ctyp2) -> 
    Tapp(
      rename cvar cvar_ctyp ctyp1,
      rename cvar cvar_ctyp ctyp2)
  | Tarr(ctyp1, ctyp2) -> 
    Tarr(
      rename cvar cvar_ctyp ctyp1,
      rename cvar cvar_ctyp ctyp2)
  | Tprod(ctyp_list) -> 
    Tprod(
      List.map (rename cvar cvar_ctyp) ctyp_list
    )
  | Trcd(lab_ctyp_list) ->
    Trcd(
      map_snd (rename cvar cvar_ctyp) lab_ctyp_list
    )
  | Tbind(binder, binded_cvar, k, ctyp_body) ->
    if (binded_cvar.name) = (cvar.name) then ctyp
    else
      Tbind(binder, binded_cvar, k, rename cvar cvar_ctyp ctyp_body)

(* ____________________________ Eager and lazy modes ____________________________ *)

let rec eager_expansion ctyp = 
  match ctyp with 
  | Tvar(cvar) -> (
    match cvar.def with 
      | None -> ctyp
      | Some(def) -> eager_expansion def.typ
    )
  | Tprim(_) -> ctyp
  | Tarr(ctyp1, ctyp2) -> Tarr(eager_expansion ctyp1, eager_expansion ctyp2)
  | Tapp(ctyp1, ctyp2) -> Tapp(eager_expansion ctyp1, eager_expansion ctyp2)
  | Tprod(typ_list) -> Tprod (List.map eager_expansion typ_list)
  | Trcd(labctyp_list) -> Trcd (map_snd eager_expansion labctyp_list)
  | Tbind(binder, cvar, kind, ctyp) -> 
    Tbind(binder, cvar, kind, eager_expansion ctyp)

let rec full_normal t1 = 
  match t1 with 
  | Tvar(_) | Tprim(_) -> t1
  | Tapp(Tbind(Tlam, alpha, kind, ct1), ct2) -> 
    full_normal (rename alpha ct2 ct1)
  | Tarr(ct1, ct2) ->
    Tarr(full_normal ct1, full_normal ct2)
  | Trcd(lab_ctyp_list) -> 
    Trcd (map_snd full_normal lab_ctyp_list)
  | Tprod(ctyp_list) ->
    Tprod (List.map full_normal ctyp_list)
  | Tbind(binder, alpha, kind, ctyp) -> 
    Tbind(binder, alpha, kind, full_normal ctyp)
  | Tapp(ct1, ct2) -> 
    let n_ct1, n_ct2 = full_normal ct1, full_normal ct2 in 
    match n_ct1 with 
    | Tbind(Tlam, _, _, _) -> full_normal (Tapp(n_ct1, n_ct2))
    | _ -> Tapp(ct1, ct2)

let head_norm t1 = 
  let rec head_reduction t1 =
    match t1 with
    | Tapp(Tbind(Tlam, alpha, kind, ct1), ct2) -> 
      head_reduction (rename alpha ct2 ct1)
    | _ -> t1
  in
  if !eager then t1
  else head_reduction t1

let norm t1 = 
  if !eager then full_normal (eager_expansion t1)
  else t1

let eq_typ t1 t2 = compare t1 t2 = 0
(* compare (norm t1) (norm t2) for Task 4*)

let eq_binder b1 b2 =
  match b1, b2 with
  | Tlam, Tlam | Tall, Tall | Texi, Texi -> true
  | _ -> false

let eq_prim p1 p2 =
  match p1, p2 with
  | Tint, Tint | Tbool, Tbool
  | Tstring, Tstring | Tunit, Tunit -> true
  | _ -> false

let rec eq_cvar v1 v2 =
  if v1.name = v2.name && v1.id = v2.id then None 
  else (
    match v1.def, v2.def with 
    | None, None ->
      Format.printf "%s%n vs %s%n" v1.name v1.id v2.name v2.id;
      Some(Tvar v1, Tvar v2) 
    | Some(def1), None -> diff_typ def1.typ (Tvar v2) 
    | None, Some(def2) -> diff_typ (Tvar v1) def2.typ
    | Some(def1), Some(def2) -> diff_typ def1.typ def2.typ
  )
and recurse_if_equal h1 h2 q1 q2 =
  match diff_typ h1 h2 with
  | None -> diff_typ q1 q2
  | Some(_) as l -> l
and iter_diff_typ t1 t2 l1 l2 =
  match l1, l2 with
  | [], [] -> None 
  | t1 :: q1, t2 :: q2 ->
    (match diff_typ t1 t2 with
      | None -> iter_diff_typ t1 t2 q1 q2
      | Some _ as s -> s)
  | _ -> Some(t1, t2)

and record_diff_typ typ1 typ2 l1 l2 =
  match l1, l2 with 
  | [], [] -> None 
  | (l1, t1) :: q1, (l2, t2) :: q2 -> 
    if l1 <> l2 then Some(t1, t2)
    else (
      match diff_typ t1 t2 with 
      | None -> record_diff_typ typ1 typ2 q1 q2
      | Some _ as s -> s
    )
  | _ -> Some(typ1, typ2)

and diff_typ t1 t2 = 
  match t1, t2 with
  | Tvar(v1), Tvar(v2) -> eq_cvar v1 v2
  | Tvar(v1), _ -> (
      match v1.def with
      | Some def -> diff_typ def.typ t2
      | None -> Some(t1,t2)
  )
  | _, Tvar(v2) -> (
      match v2.def with
      | Some def -> diff_typ t1 def.typ
      | None -> Some(t1,t2)
  )  
  | Tprim(p1), Tprim(p2) -> 
    if eq_prim p1 p2 then None
    else Some(t1, t2)

  | Tapp(f1, a1), Tapp(f2, a2)
  | Tarr(f1, a1), Tarr(f2, a2) ->
    recurse_if_equal f1 f2 a1 a2

  | Tprod(l1), Tprod(l2) -> iter_diff_typ t1 t2 l1 l2

  | Trcd(l1), Trcd(l2) ->
    let compare_label (l1, t1) (l2, t2) =
      if l1 = l2 then 0 else if l1 > l2 then 1 else -1
    in 
    let sorted_l1 = List.sort compare_label l1 in 
    let sorted_l2 = List.sort compare_label l2 in 
    record_diff_typ t1 t2 sorted_l1 sorted_l2

  | Tbind(b1,x1,k1,body1), Tbind(b2,x2,k2,body2) ->
    if eq_binder b1 b2 && eq_kind k1 k2 then
      let body1_renamed = rename x1 (Tvar x2) body1 in 
      diff_typ body1_renamed body2
    else Some(t1, t2)

  | _ -> Some(t1, t2)

