(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
(* [@@@warning "-27-32-33-37-39-60"] *)

open Util
open Syntax

(* __________________________ Module definitions _________________________ *)


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


(** Type substitution as opposed to renaming *)
let rec subst (su :ctyp Tenv.t) (t : ctyp) : ctyp =
  match t with
    | Tvar(v) -> apply su v
    | Tprim(_) -> t
    | Tapp(t1, t2) -> Tapp(subst su t1, subst su t2)
    | Tarr(t1, t2) -> Tarr(subst su t1, subst su t2)
    | Tprod(typ_list) ->
      Tprod(List.map (subst su) typ_list)
    | Trcd(ltyp_list) ->
      Trcd(map_snd (subst su) ltyp_list)
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


(* __________________ Reduction and unfolding: eager mode __________________ *)


(** [eager_expansion ctyp] expand eagerly every variable presents in [ctyp].
  Is is used in eager normalization. It returns the normalized type and a bool
  indicating if it has been modified *)
let rec eager_expansion ctyp : ctyp * bool = 
  match ctyp with 
  | Tvar(cvar) -> (
    match cvar.def with 
      | None -> ctyp, false
      | Some(def) -> fst (eager_expansion def.typ), true
    )
  | Tprim(_) -> ctyp, false 
  | Tarr(ctyp1, ctyp2) -> 
    let exp_ctyp1, b1 = eager_expansion ctyp1 in
    let exp_ctyp2, b2 = eager_expansion ctyp2 in
    Tarr(exp_ctyp1, exp_ctyp2), b1 || b2
  | Tapp(ctyp1, ctyp2) -> 
    let exp_ctyp1, b1 = eager_expansion ctyp1 in
    let exp_ctyp2, b2 = eager_expansion ctyp2 in
    Tapp(exp_ctyp1, exp_ctyp2), b1 || b2
  | Tprod(typ_list) ->
    let b, expand_typ_list = 
    List.fold_left_map 
      (fun b ctyp -> 
        let expand_ctyp, b' = eager_expansion ctyp in 
        b || b', expand_ctyp)
      false
      typ_list
    in 
    Tprod(expand_typ_list), b
  | Trcd(labctyp_list) ->
    let b, expand_typ_list = 
    List.fold_left_map 
      (fun b (lab,ctyp) -> 
        let expand_ctyp, b' = eager_expansion ctyp in 
        b || b', (lab, expand_ctyp))
      false
      labctyp_list
    in 
    Trcd(expand_typ_list), b
  | Tbind(binder, cvar, kind, ctyp) -> 
    let exp_ctyp, b = eager_expansion ctyp in 
    Tbind(binder, cvar, kind, exp_ctyp), b


(** [full_normal ctyp] fully normalizes [ctyp]. Is is used in eager
 normalization. *)
let rec full_normal t1 = 
  match t1 with 
  | Tvar(_) | Tprim(_) -> t1
  | Tapp(Tbind(Tlam, alpha, _, ct1), ct2) ->
    full_normal (subst_typ alpha ct2 ct1)
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
    | _ ->  Tapp(n_ct1, n_ct2)


(* __________________ Reduction and unfolding: lazy mode __________________ *)


(** [head_norm t] returns a type equivalent to [t1] but in head normal form. *)
let head_norm t1 = 
  let rec head_reduction t =
    match t with
    | Tapp(Tbind(Tlam, alpha, _, ct1), ct2) ->
      let _, reduct_t1 = head_reduction (subst_typ alpha ct2 ct1) in
      true, reduct_t1
    | Tapp(t1, t2) ->
      let is_reduct_t1, reduct_t1 = head_reduction t1 in 
      if is_reduct_t1 then
        let _, red_term = head_reduction (Tapp(reduct_t1, t2)) in 
        true, red_term
      else false, Tapp(reduct_t1, t2)
    | _ -> false, t
  in
  if !eager then t1
  else snd (head_reduction t1)

(** [lazy_reduce_expand t] performs head reduction and head unfolding in
    lazy mode,ie. unfold only when it can change the shape of [t]. It is
    used when checking its shape. It returns a type equivalent to [t] but
    expanded and reduced, with a bool indicating if it has been modified *)
let lazy_reduce_expand t1 =
  let rec head_reduce_expand ctyp =
    (* type shape can change by :
      - head reducting
      - unfolding variable in head position then head reducing *)
    match ctyp with 
    | Tvar(cvar) -> (
      match cvar.def with 
      | None -> false, ctyp
      | Some def ->
        true, snd (head_reduce_expand def.typ)
    )
    | Tapp(Tbind(Tlam, alpha, _, ct1), ct2) ->
      let _, expand_ctyp = head_reduce_expand (subst_typ alpha ct2 ct1) in 
      true, expand_ctyp
    | Tapp(t1, t2) -> 
      let b, expand_t1 = head_reduce_expand t1 in 
      if b then 
        true, snd (head_reduce_expand (Tapp(expand_t1,t2)))
      else false, ctyp
    | _ -> false, ctyp
  in
  if !eager then false, t1
  else head_reduce_expand t1

(** [norm t1] normalize t1 according to the mode *)
let norm t1 = 
  if !eager then
    let expand_t1, _  = eager_expansion t1 in 
    full_normal expand_t1
  else head_norm t1


(* ______________________________ Equalities ______________________________ *)

(** Kind equality *)
let rec eq_kind k1 k2 =
  match k1, k2 with
    | Ktyp, Ktyp -> true
    | Karr(k1_1, k1_2), Karr(k2_1, k2_2) ->
      eq_kind k1_1 k2_1 && eq_kind k1_2 k2_2
    | _ -> false

(** Binder equality *)
let eq_binder b1 b2 =
  match b1, b2 with
  | Tlam, Tlam | Tall, Tall | Texi, Texi -> true
  | _ -> false

(** Primitive type equality *)
let eq_prim p1 p2 =
  match p1, p2 with
  | Tint, Tint | Tbool, Tbool
  | Tstring, Tstring | Tunit, Tunit -> true
  | _ -> false

let struct_eq_cvar c1 c2 =
  c1.name = c2.name && c1.id = c2.id

(** Variable equality, unfolding only when necessary *)
let rec eq_cvar v1 v2 =
  if v1.name = v2.name && v1.id = v2.id then None 
  else (
    match v1.def, v2.def with 
    | None, None -> Some(Tvar v1, Tvar v2) 
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

(* In lazy mode, we start by head reducing. Then, if types does not
   structurally coincides:
  - if at least one is a variable, we progressively unfold it and stop
    when getting equality or a primitive definition (it doesn't happen
    in eager mode since variables are completely unfold)
  - if at least one is an application, we apply lazy_reduce_expand, which
    head reduce and unfold in lazy mode
   In eager mode, it is equivalent to structural equality.*)
and diff_typ t1 t2 =
  let t1, t2 = head_norm t1, head_norm t2 in 
  match t1, t2 with
  | Tprim(p1), Tprim(p2) -> 
    if eq_prim p1 p2 then None
    else Some(t1, t2)

  | Tprim Tunit, Tprod [] 
  | Tprod [], Tprim Tunit -> None

  | Tarr(f1, a1), Tarr(f2, a2) ->
    recurse_if_equal f1 f2 a1 a2

  | Tprod(l1), Tprod(l2) -> iter_diff_typ t1 t2 l1 l2

  | Trcd(l1), Trcd(l2) ->
    (* Sorting field's label before comparing records *)
    let compare_label (l1, _) (l2, _) =
      if l1 = l2 then 0 else if l1 > l2 then 1 else -1
    in 
    let sorted_l1 = List.sort compare_label l1 in 
    let sorted_l2 = List.sort compare_label l2 in 
    record_diff_typ t1 t2 sorted_l1 sorted_l2

  | Tbind(b1,x1,k1,body1), Tbind(b2,x2,k2,body2) ->
    if eq_binder b1 b2 && eq_kind k1 k2 then
      let body1_renamed = subst_typ x1 (Tvar x2) body1 in 
      diff_typ body1_renamed body2
    else Some(t1, t2)

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

  | Tapp(f1, a1), Tapp(f2, a2) ->
    (match recurse_if_equal f1 f2 a1 a2 with 
    | None -> None 
    | Some(t1, t2) ->
      let b1, expand_f1 = lazy_reduce_expand f1 in 
      let b2, expand_f2 = lazy_reduce_expand f2 in
      if b1 || b2 then 
        diff_typ 
          (head_norm (Tapp(expand_f1, a1)) )
          (head_norm (Tapp(expand_f2, a2)) )
      else Some(t1, t2)
    )

  | Tapp(f1, a1), _ ->
    let b, expand_f1 = lazy_reduce_expand f1 in 
    if b then diff_typ (Tapp(expand_f1, a1)) t2
    else Some(t1, t2)

  | _, Tapp(f1, a1) ->
    let b, expand_f1 = lazy_reduce_expand f1 in 
    if b then(diff_typ t1 (Tapp(expand_f1, a1)))
    else Some(t1, t2)

  | _ -> Some(t1, t2)

  let eq_typ t1 t2 =
  match diff_typ t1 t2 with 
  | None -> true 
  | _ -> false