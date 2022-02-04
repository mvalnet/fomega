(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-27-32-33-37-39-60"]
open Util
open List
open Syntax
open Type
open Error

(**________________________ 1. Environments ____________________________*)


(** We represent the environment using maps.  (For short programs, we could
   use lists, but large programs with modules, may have quite large
   contexts.)  We separate the name spaces of expression variables [evar]
   from type variables, hence using a separate map.

   For type variables, we actually need two maps: [svar] maps source type
   variables (which may be shadowed) to internal type variables while [cvar]
   maps internal type variables (which are never shadowed) to their kind or
   definition.

   You may need to add another map in type [env] for Task 4.  *)
                    
type env = {
    evar : ctyp Senv.t;
    svar : cvar Senv.t;
    cvar : kind Tenv.t;
}

let empty_env = {
    evar = Senv.empty;
    svar = Senv.empty;
    cvar = Tenv.empty;
}

(** Functions to query the environment accordingly. Same semantics as maps,
   except for the order of arguments. All `find_` functions raise the
   exception [Not_found] when their argument is not in the environment. *)
let find_cvar env a =  Tenv.find a env.cvar
let find_evar env x = Senv.find x env.evar
let find_svar env s = Senv.find s env.svar

(** Functions to modify the environment accordingly. Same semantics as maps,
   except for the order of arguments. *)
let add_evar env x t = { env with evar = Senv.add x t env.evar }
let add_cvar env a k = { env with cvar = Tenv.add a k env.cvar }

(** [add_svar] must also deal with shallow bindings *)
let add_svar env s a = { env with svar = Senv.add s a env.svar }


(** [fresh_id_for env a] returns the smallest possible id for variable name
   [a] given the already allocated variables in [env]. Depending on the
   implementation, it may need to store information in env, hence it returns
   a possibly modified version of [env] *)

(** Assuming source type variables never end with an integer, a simple correct 
    implementation of [fresh_id_for] *)
let fresh_id_for_T1 env _a =
  env, fresh_id ()

(** Assuming source type variables never end with an integer, a simple and more
    readable correct implementation of [fresh_id_for] *)
let fresh_id_for_T2 env _a =
  let id = 
    try
      (find_svar env _a).id + 1
    with
      | Not_found -> 0
  in
  add_svar env _a { name = _a ; id ; def = None }, id

let fresh_id_for =
     fresh_id_for_T2

(** [get_svar env a] is a wrapper around [find_evar env a] that turns a
   [Not_found] exception into a non-localized [Unbound] typing-error
   exception.  These will have to be localized by their calling context,
   using [within_loc]. *)
let get_svar env a =
  try find_svar env a
  with Not_found -> error_unloc (Unbound (Typ (None, a)))
                  
(** May raise non-localized [Unbound] error *)
let get_evar exp env x =
  try find_evar env x
  with Not_found -> error exp (Unbound (Exp x))

let make_cvar name id def =
  { name ; id ; def}
let make_loc obj loc =
  { obj ; loc}

let complex_pattern pat = Typing(Some pat.loc, NotImplemented "Complex Pattern")
let f_omega loc = Typing(Some loc, NotImplemented "F_Omega")

let not_ktyp styp kind  = (Typing(None, Kinding(styp, kind, Nonequal (Ktyp))))

(* _________________________ 2. Type minimization _________________________ *)

(** Type checking must perform computation on types when checking for
   convertibilty.  This requires appropriate renaming to avoid capture,
   hence generating many fresh variables, which may then disappear during
   reduction. The resulting type may thefore use large integer suffixes,
   which are unpleasant for the user to read.

   For this reason, we minimize variable names after typechecking each
   declaration, and before printing error messages.  We take advantage of
   this to allow chose possibly large intergers when renaming local
   variables during computation on types, given that this will be minimized
   after computation.

   (We could use this to further optimize maps, using just some additional
   [uid] integer field for identificatiion instead of the pair [name] and [id].)
*)

let min_excluded (env,loc_env) cvar =
  try 
    (Senv.find cvar.name loc_env).id + 1
  with
    | Not_found -> 
      try 
        (find_svar env cvar.name).id + 1
      with
        | Not_found -> 0

(** [minimize_typ env t] returns a renaming of [t] that minimizes the
   variables suffixes but still avoids shallowing internally and with
   respect to env [env] *)
let rec aux_minimize_typ (global_env, map_to_new_cvar) (t :ctyp) =
  let env = (global_env, map_to_new_cvar) in
  match t with
    | Tvar(cv) -> (
      try
        Tvar(Senv.find (cv.name) map_to_new_cvar)
      with 
       | Not_found -> 
        try Tvar(find_svar global_env cv.name)
        with 
          | Not_found ->
            Tvar({name = cv.name ; id = 0 ; def = None}) 
          (* STILL A PROBLEM THERE *)
           (*Format.printf "here" ; Format.printf "%s" cv.name ; raise Not_found*)
    )
    | Tprim(_) -> t
    | Tapp(t1, t2) -> 
      Tapp(
        aux_minimize_typ env t1,
        aux_minimize_typ env t2
      )
    | Tarr(t1, t2) ->
      Tarr(
        aux_minimize_typ env t1,
        aux_minimize_typ env t2
      )
    | Tprod (ctyp_l) -> 
      Tprod(List.map (aux_minimize_typ env) ctyp_l)
    | Trcd(rcd_l) ->
      Trcd(map_snd (aux_minimize_typ env) rcd_l)
    | Tbind(binder, binded_cvar, kind, t) ->
      let min_id = min_excluded (global_env, map_to_new_cvar) binded_cvar in
      let new_cvar = {name = binded_cvar.name ; id = min_id ; def = None } in
      let new_map = Senv.add (binded_cvar.name) new_cvar map_to_new_cvar in
      Tbind(binder, new_cvar, kind, aux_minimize_typ (global_env,new_map) t)

(** [do_minimize] tells whether types should be minimized. It defaults to
   [true] and may be changed with the `--rawtypes` command line option, *)
let do_minimize = spec_true "--rawtypes"  "Do not minimize types"

let minimize_typ env t =
  if !do_minimize then aux_minimize_typ (env, Senv.empty) t else t

(** [type_typ env t] typechecks source type [t] returning its kind [k] and
   an internal representation of [t].  This may non-localized (Unbound and
   Kinding) typing error exceptions. *)
let rec type_typ env (t : styp) : kind * ctyp =
  match t with
  | Tprim c -> 
     Ktyp, Tprim c
  | Tvar(svar) ->
    let cvar = get_svar env svar in
    let kind = find_cvar env cvar in 
    kind,
    if svar = "int" && (cvar.id = 0) then Tprim Tint 
    else if svar = "bool" && (cvar.id = 0) then Tprim Tbool
    else if svar = "string" && (cvar.id = 0) then Tprim Tstring
    else if svar = "unit" && (cvar.id = 0) then Tprim Tunit 
    else Tvar cvar   
  | Tarr(styp1, styp2) ->
    let kind1, ctyp1 = type_typ env styp1 in
    let kind2, ctyp2 = type_typ env styp2 in
    (match kind1, kind2 with 
    | Ktyp, Ktyp -> Ktyp, Tarr(ctyp1, ctyp2)
    | Karr(_), _ -> raise (not_ktyp styp1 kind1)
    | _, Karr(_) -> raise (not_ktyp styp2 kind2))
  | Tapp(styp1, styp2) -> 
    let kind1, ctyp1 = type_typ env styp1 in
    let kind2, ctyp2 = type_typ env styp2 in
    (match kind1 with
    | Ktyp -> raise (
      Typing (
        None,
        Kinding(t,kind1,Matching(Sarr))
      )
     )
    | Karr(k_arg, k_ret) ->
      if eq_kind k_arg kind2 then
        k_ret, Tapp(ctyp1, ctyp2)
      else (raise (
        Typing(
          None,
          Kinding(t, k_arg, Nonequal(kind2))
        )
      ))
    )
  | Tbind(binder, svar, kind, styp) ->
    let nenv, id = fresh_id_for env svar in 
    let cvar = make_cvar svar id None in 
    let nenv = add_cvar nenv cvar kind in
    let kind_body, cbody = type_typ nenv styp in
    (match binder with
      | Tlam -> Karr(kind, kind_body), Tbind(Tlam, cvar, kind, cbody)
      | binder -> (
        match kind_body with
        | Ktyp -> Ktyp, Tbind(binder, cvar, kind, cbody)
        | _ -> raise (not_ktyp styp kind_body)
      )
    )
  | Tprod(styp_list) -> 
    let ctyp_list =
      List.map
        (fun styp -> 
          match type_typ env styp with
          | Ktyp, ctyp -> ctyp 
          | kind, _ -> raise (not_ktyp styp kind)
        )
        styp_list
    in 
    Ktyp, Tprod(ctyp_list)
  | Trcd(labstyp_list) -> 
    Ktyp, (* I suppose? *)
    Trcd( map_snd (fun s -> snd (type_typ env s)) labstyp_list)

let type_typ env styp_loc = 
  let kind, ctyp = within_loc (type_typ env) styp_loc in
  kind, norm ctyp

(** Checking that local variables do not escape. Typechecking of
   existential types requires that locally abstract variables do not escape
   from their scope. This amounts to verifying that the returned type is
   well-formed. It suffices to check that all variables are bound in the
   given environment.

   One must be careful of non linear redexes and delayed definitions.
   Therefore, we must not only check for well-formedness, but return an
   equivalent type that is well-formed. This should just perform the
   necessary unfoldings and reductions. *)
exception Escape of cvar
let rec wf_ctyp env t : ctyp =
  match t with
  | Tvar a -> 
     (* fix me *)
     if true then t else raise (Escape a)
  | _ -> t

(* __________________________ 3. Type checking __________________________ *)

let (!@) = Locations.with_loc  
let (!@-) = Locations.dummy_located

let rec svar_to_cvar env (scar : styp) : (env * ctyp) =
  match scar with
  | Tvar(v) -> env,
    let cvar = get_svar env v in 
    if v = "int" && (cvar.id = 0) then Tprim Tint 
    else if v = "bool" && (cvar.id = 0) then Tprim Tbool
    else if v = "string" && (cvar.id = 0) then Tprim Tstring
    else if v = "unit" && (cvar.id = 0) then Tprim Tunit 
    else Tvar cvar     
  | Tprim(x) -> env, Tprim(x)
   | Tarr(s1, s2) ->
    let env1, c1 = svar_to_cvar env s1 in
    let env2, c2 = svar_to_cvar env1 s2 in
    env2, Tarr(c1, c2)
  | Tapp(s1, s2) ->
    let env1, c1 = svar_to_cvar env s1 in
    let env2, c2 = svar_to_cvar env1 s2 in
    env2, Tapp(c1, c2)
  | Tprod(s_list) ->
    let nenv, c_list = List.fold_left_map svar_to_cvar env s_list in 
    nenv, Tprod(c_list)
  | Trcd(labs_list) ->
    let nenv, labc_list =
      List.fold_left_map
        (fun env (lab,s)  ->
          let nenv, c = svar_to_cvar env s in
          nenv, (lab, c)
        )
        env
        labs_list
    in 
    nenv, Trcd(labc_list)
  | Tbind(b, var, kind, styp) ->
    let nenv, id = fresh_id_for env var in
    let nenv, ctyp = svar_to_cvar nenv styp in
    let def = { scope = -1 ; typ = ctyp } in
    let cvar = {name = var ; id ; def = Some def } in
    nenv, Tbind(b, cvar, kind, ctyp )

let styp_to_ctyp env styp =
  let env, ctyp = within_loc (within_typ (svar_to_cvar env)) styp in 
  env, norm ctyp 

let make_showdiff_error loc cur exp sub_cur sub_exp =
  Typing(Some loc, Expected(cur, Showdiff(exp, sub_cur, sub_exp)))


let is_pvar x = 
  match x.obj with
  | Pvar(_) -> true
  | _ -> false

let rec rename_svar tau alpha tau' = 
  match tau with
  | Tvar(x) -> 
    if x = alpha then tau'
    else tau 
  | Tprim(_) -> tau 
  | Tprod(styp_list) ->
    Tprod(
      List.map (fun styp -> (rename_svar styp alpha tau')) styp_list
    )
  | Trcd(lab_styp_list) -> 
    Trcd(
      map_snd (fun styp -> (rename_svar styp alpha tau')) lab_styp_list
    )
  | Tapp(styp1, styp2) -> 
    Tapp(
      rename_svar styp1 alpha tau',
      rename_svar styp2 alpha tau'
    )
  | Tarr(styp1, styp2) -> 
    Tarr(
      rename_svar styp1 alpha tau',
      rename_svar styp2 alpha tau'
    )
  | Tbind(binder, svar, kind, styp) -> 
    if svar = alpha then tau
    else
      Tbind(binder, svar, kind, rename_svar styp alpha tau')    

let rec find_binded_var pat =
  match pat.obj with
  | Pvar(evar) -> evar
  | Ptyp(pat, _) -> find_binded_var pat
  | _ -> raise (complex_pattern pat)
(*
let find_binded_type env pat exp =
  match pat.obj with
  | Pvar(evar) -> (
    match exp with
    | Efun(_, exp_loc) ->
      (match exp_loc.obj with 
      | Eannot(_, styp_loc) -> None
      | _ -> raise (Typing(Some(pat.loc), Annotation(evar)))
      )
    | _ -> raise (Typing(Some(pat.loc), Annotation(evar)))
    )
  | Ptyp(x, styp_loc) -> (
      match x.obj with 
      | Pvar(evar) -> Some(styp_loc)
      | _ -> raise (complex_pattern pat)
  )
 | _ -> raise (complex_pattern pat)

 *)
let find_binded_type env pat exp =
  match pat.obj with
  | Pvar(evar) -> (
    match exp with
    | Efun(args, exp_loc) -> (* partnership with cross_binding to get the type *)
      (match exp_loc.obj with 
      | Eannot(_, styp_loc) ->
        let nenv, typ = styp_to_ctyp env styp_loc in
        add_evar nenv evar typ, typ
      | _ -> raise (Typing(Some(pat.loc), Annotation(evar)))
      )
    | _ -> raise (Typing(Some(pat.loc), Annotation(evar)))
    )
  | Ptyp(x, styp_loc) -> (
      match x.obj with 
      | Pvar(evar) -> 
        let nenv, typ = styp_to_ctyp env styp_loc in
        add_evar nenv evar typ, typ
      | _ -> raise (complex_pattern pat)
  )
 | _ -> raise (complex_pattern pat)

let typ_to_string = function
  | Tvar(_) -> "tvar"
  | Tprim(_) -> "tprim"
  | Tapp(_) -> "tapp"
  | Tprod(_) -> "tprod"
  | Trcd(_) -> "trcd"
  | Tarr(_) -> "tarr"
  | Tbind(_) -> "tbind"

let rec type_exp env exp : ctyp =
  match exp.obj with 
  | Evar x -> norm(get_evar exp env x)
  | Eprim (Int _) -> Tprim Tint
  | Eprim (Bool _) -> Tprim Tbool
  | Eprim (String _) -> Tprim Tstring
  | Eannot(exp, styp_loc) ->
    let t_expr = type_exp env exp in
    let nenv, t_annot = styp_to_ctyp env styp_loc in
   ( match diff_typ t_expr t_annot with
    | None -> t_annot
    | Some(subt_expr, subt_annot) -> raise (
      make_showdiff_error exp.loc t_expr t_annot subt_expr subt_annot
      )
    )
  | Eprod(exp_list) ->
    Tprod(
      List.map (type_exp env) exp_list
    )
  | Eproj(exp, n) -> (
    match type_exp env exp with
      | Tprod(typ_list) -> List.nth typ_list (n-1)
      | ctyp -> raise (
        Typing(
          Some exp.loc,
          Expected(ctyp,Matching(Sprod (Some n)))
        )
      )
  )
  | Ercd(labexp_list) ->
    Trcd(
      map_snd (type_exp env) labexp_list
    )
  | Elab(exp, lab) -> 
  ( match type_exp env exp with
    | Trcd(labexp_list) as ctyp ->  (
        try
          snd 
            (List.find 
              (fun (lab_i,_) -> lab_i = lab )
              labexp_list
            )
        with 
          | Not_found -> raise (
            Typing(
              Some exp.loc,
              Expected(ctyp, Matching(Srcd (Some lab) ))
           )
          )
    )
    | ctyp -> raise (
      Typing(
        Some exp.loc,
        Expected(ctyp, Matching(Srcd (Some lab) ))
      )
    )
  )

  | Efun(binding_list, exp) ->
    cross_binding env exp binding_list
  | Eappl(exp, arg_list) ->
    let t_expr = type_exp env exp in
    norm(apply_arg env t_expr arg_list)
  | Elet(is_rec, pat, exp1, exp2) ->
    if is_rec then
      let nenv, binded_type = find_binded_type env pat exp1.obj in
      let t_expr1 = type_exp nenv exp1 in
      (match diff_typ t_expr1 binded_type with 
      | None -> type_exp nenv exp2
      | Some(subt_expr1, sub_binded_type) -> raise (
        make_showdiff_error
          exp.loc 
          t_expr1 binded_type
          subt_expr1 sub_binded_type
        )
      ) 
    else 
      let binded_var = find_binded_var pat in
      let t_expr1 = type_exp env exp1 in 
      let nenv = add_evar env binded_var t_expr1 in
      type_exp nenv exp2

  | Epack(packed_styp, exp, styp_as) ->
    let env, ctyp_as = styp_to_ctyp env styp_as in
    let env, packed_ctyp = styp_to_ctyp env packed_styp in
    norm(typ_pack env packed_ctyp exp ctyp_as )
  | Eopen(alpha, x, exp1, exp2) ->
    let ctyp1 = type_exp env exp1 in 
    (match ctyp1 with
    | Tbind(Texi, beta, kind, ctyp) ->
      let env, id = fresh_id_for env alpha in 
      let cvar = make_cvar alpha id None in
      let unpack_ctyp1 = rename beta (Tvar(cvar)) ctyp in
      let nenv = add_evar env x unpack_ctyp1 in
      let ctyp2 = type_exp nenv exp2 in
      norm(wf_ctyp cvar ctyp2)
    | _ -> raise (
      Typing(
        Some exp.loc,
         Expected(ctyp1, Matching(Sexi))
      )
    ))

and typ_pack env tau' exp ctyp_as =
  let ctyp = norm (type_exp env exp) in
  match ctyp_as with
  | Tvar(cvar) -> (
      match cvar.def with 
      | Some(def) -> typ_pack env tau' exp def.typ
      | None -> raise (
        Typing(
          Some exp.loc,
          Expected(ctyp_as, Matching(Sexi))
        )
      )
    )
  | Tbind(Texi, alpha, kind, tau)  -> 
    let expected_ctyp = norm (rename alpha tau' tau) in
    (match diff_typ ctyp expected_ctyp with
    | None -> ctyp_as
    | Some(subt_expr, subt_expected) ->
      raise (
        make_showdiff_error exp.loc ctyp expected_ctyp subt_expr subt_expected
      )
    )
    
    | _ -> raise (
      Typing(
        Some exp.loc,
         Expected(ctyp_as, Matching(Sexi))
      )
    )

and apply_arg env t_expr arg_list =
  match t_expr, arg_list with
  | Tbind(Tall, cvar, kind, ctyp), Typ(styp_loc) :: arg_list -> 
    let nenv, arg_ctyp = styp_to_ctyp env styp_loc in
    (* check kind compatibility *)
    let ctyp = rename cvar arg_ctyp ctyp in
    apply_arg nenv ctyp arg_list 
  | Tarr(t1,t2), Exp(arg1) :: arg_list -> 
      let t_arg1 = type_exp env arg1 in
      (match diff_typ t_arg1 t1 with
      | None -> apply_arg env t2 arg_list
      | Some(subt_arg1, sub_t1) -> raise (
        make_showdiff_error arg1.loc t_arg1 t1 subt_arg1 sub_t1
        )
      )
  | _, [] -> t_expr
  | Tvar(cvar), Exp(arg1) :: q -> (
    match cvar.def with 
    | Some def -> apply_arg env def.typ arg_list
    | None -> raise (
      Typing(Some (arg1.loc), Expected(t_expr, Matching(Sarr)))
    )
  )
  | Tvar(cvar), Typ(styp_loc) :: q -> (
    match cvar.def with 
    | Some def -> apply_arg env def.typ arg_list
    | None -> raise (
      Typing(Some (styp_loc.loc), Expected(t_expr, Matching(Sall)))
    )
  )
  | _, Exp(arg1) :: q -> raise (
    Typing(Some (arg1.loc), Expected(t_expr, Matching(Sarr)))
  )
  | _, Typ(styp_loc) :: q -> raise (
    Typing(Some (styp_loc.loc), Expected(t_expr, Matching(Sall)))
  )

and cross_binding env expr = function
  | [] -> type_exp env expr
  | (Typ(svar,kind)) :: q ->
    let nenv, id_svar = fresh_id_for env svar in 
    let cvar = make_cvar svar id_svar None in 
    let nenv = add_svar env svar cvar in 
    let nenv = add_cvar nenv cvar kind in
    Tbind(Tall, cvar, kind, cross_binding nenv expr q)
  | Exp(pat) :: q -> (
    match pat.obj with
    | Ptyp(pat, styp_loc) -> 
      (match pat.obj with 
        | Pvar(evar) ->
          (*let tp_evar = "temporary" in
          let nenv, id_svar = fresh_id_for env tp_evar in*)
          let _, ctyp = styp_to_ctyp env styp_loc in
          (*let def = { scope = -1 ; typ = ctyp } in
          let cvar = make_cvar tp_evar id_svar (Some def) in
          let nenv = add_svar nenv tp_evar cvar in*)
          let nenv = add_evar env evar ctyp in
          Tarr(ctyp, cross_binding nenv expr q)
        | _ -> raise (complex_pattern pat))
    | Pvar(evar) ->  raise (Typing(Some(pat.loc), Annotation(evar)))
    | _ -> raise (complex_pattern pat)
  )

let norm_when_eager =
  spec_true "--loose"  "Do not force toplevel normalization in eager mode"

let type_decl env (d :decl) : env * typed_decl = 
  match d.obj with
  | Dtyp(svar, toe) -> (
    match toe with
    | Exp(styp_loc) ->
      let nenv, id = fresh_id_for env svar in
      (*let _, ctyp = styp_to_ctyp nenv styp_loc in  *)
      let kind, ctyp = type_typ nenv styp_loc in
      let def = { scope = 0 (* ??? *); typ = ctyp } in
      let cvar = make_cvar svar id (Some def) in
      let nenv = add_svar nenv svar cvar in 
      let nenv = add_cvar nenv cvar kind in
      nenv, Gtyp(cvar, Exp(kind, minimize_typ env ctyp))

    | Typ(k) ->
      let env, id = fresh_id_for env svar in
      let cvar = make_cvar svar id None in
      env, Gtyp(cvar,Typ(k))
  )
  | Dlet(is_rec, pat, exp) ->
    let binded_var = find_binded_var pat in
    if is_rec then
      let nenv, binded_type = find_binded_type env pat exp.obj in
      let ctyp = type_exp nenv exp in
      (match diff_typ ctyp binded_type with 
      | None -> nenv, Glet(binded_var,  type_exp nenv exp)
      | Some(sub_ctyp, sub_binded_type) -> raise (
        make_showdiff_error
        exp.loc
        ctyp binded_type
        sub_ctyp sub_binded_type
      )
    )
    else 
      let ctyp = type_exp env exp in 
      (add_evar env binded_var ctyp), Glet(binded_var, minimize_typ env ctyp)
        
  | Dopen(svar, evar, exp) ->
    let ctyp = type_exp env exp in 
    let nenv, id = fresh_id_for env svar in
    let cvar = make_cvar svar id None in 
    match ctyp with 
    | Tbind(Texi,_,_, _) -> 
      nenv, Gopen(cvar, evar, ctyp)
    | _ -> raise (
      Typing(
        Some d.loc,
         Expected(ctyp, Matching(Sexi))
      )
    )

let type_program env (p : program) : env * typed_decl list =
  List.fold_left_map type_decl env p


(** Initial environment *)
  
let unit, int, bool, string, bot =
  let unit = Tprod [] in
  let int = Tprim Tint in
  let bool = Tprim Tbool in
  let string = Tprim Tstring in
  let bot = let a = svar "#" in Tbind (Tall, a, Ktyp, Tvar a) in
  unit, int, bool, string, bot
  
let primitive_types =     
  [ "unit", unit;
    "bool", bool;
    "int", int;
    "string", string;
    "bot", bot;
  ]

let initial_env, initial_program =
  let magic = evar "magic" in
  let p : program =
    let pair (s, t) : decl = !@- (Dtyp (svar s, Exp !@- t)) in
    List.map pair primitive_types @
    [ !@- (Dlet (true, !@- (Ptyp (!@- (Pvar magic), !@- bot)),
                 !@- (Evar magic))) ]
  in

  type_program empty_env p 

