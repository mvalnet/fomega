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
    pvar : (int list) Senv.t ;
    cvar : kind Tenv.t;
}

let empty_env = {
    evar = Senv.empty;
    svar = Senv.empty;
    pvar = Senv.empty;
    cvar = Tenv.empty;
}

(** Functions to query the environment accordingly. Same semantics as maps,
   except for the order of arguments. All `find_` functions raise the
   exception [Not_found] when their argument is not in the environment. *)
let find_cvar env a =  Tenv.find a env.cvar
let find_evar env x = Senv.find x env.evar
let find_pvar env x = Senv.find x env.pvar
let find_svar env s = Senv.find s env.svar

(** Functions to modify the environment accordingly. Same semantics as maps,
   except for the order of arguments. *)
let add_evar env x t = { env with evar = Senv.add x t env.evar }
let add_cvar env a k = { env with cvar = Tenv.add a k env.cvar }

let add_pvar env a s = { env with pvar = Senv.add a s env.pvar }

(** [add_svar] must also deal with shallow bindings *)
let add_svar env s a = { env with svar = Senv.add s a env.svar }


(** [fresh_id_for env a] returns the smallest possible id for variable name
   [a] given the already allocated variables in [env]. Depending on the
   implementation, it may need to store information in env, hence it returns
   a possibly modified version of [env] *)

let is_number (c : char) = String.contains "0123456789" c

let integer_suffix _a = 
  let n = String.length _a in
  let i = ref (n - 1) in 
  while is_number _a.[!i] do
    decr i;
  done ;
  if !i = n - 1 then _a, String.empty 
  else String.sub _a 0 (!i+1), String.sub _a (!i+1) (n - !i - 1)

let smallest_available suffix int_list = 
  let n = List.length int_list in 
  let used_int = Array.make (n+1) 0 in 
  List.iter 
    (fun x ->
      if x = suffix then 
        used_int.(0) <- 1 ;
      if x >= suffix*10 && x < n + suffix*10 then
        used_int.(x-suffix*10) <- 1
    )
    int_list ;
  let i = ref 0 in
  while !i < n && used_int.(!i) = 1 do 
    incr i ;
  done ;
  !i

let fresh_id_for_T3 env _a =
  let prefix, suffix = integer_suffix _a in
  let int_suffix = if suffix = "" then 0 else int_of_string suffix in 
  let nenv, id = 
  try 
    let available_suffix = Senv.find prefix env.pvar in
    let id = smallest_available int_suffix available_suffix in
    let new_suffix = if id = 0 then int_suffix else (int_suffix * 10 + id) in 
    let pvar_env = Senv.add prefix (new_suffix :: available_suffix) env.pvar in
    let nenv = { env with pvar = pvar_env} in
    nenv,id
  with
    Not_found ->
    let pvar_env = Senv.add prefix [int_suffix] env.pvar in
    let nenv = { env with pvar = pvar_env} in
    ignore (Senv.find prefix nenv.pvar) ;
    nenv, 0
  in 
  add_svar nenv _a { name = _a ; id ; def = None }, id


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
     fresh_id_for_T3

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

let min_excluded_I3 (env, loc_to_suffix) cvar = 
  let prefix, suffix = integer_suffix cvar.name in
  let svar_taken_suffix =
    ( try Senv.find prefix env.pvar with Not_found -> [])
    @ 
    (try (Senv.find prefix loc_to_suffix) with Not_found -> [])
  in
  let new_pvar = Senv.add prefix svar_taken_suffix env.pvar in 
  let nenv = { env with pvar = new_pvar } in
  let id = snd (fresh_id_for_T3 nenv cvar.name) in 
  let int_suffix = if suffix = "" then 0 else int_of_string suffix in 
  let new_suffix = if id = 0 then int_suffix else (int_suffix * 10 + id) in 
  new_suffix, id
  

let min_excluded_I2 (env,loc_env) cvar =
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
let rec aux_minimize_typ (global_env, (map_to_suffix : (int list) Senv.t), (map_to_new_cvar: cvar Senv.t)) (t :ctyp) =
  let env = (global_env, map_to_suffix, map_to_new_cvar) in
  match t with
    | Tvar(cv) -> (
      try
        Tvar( Senv.find (cv.name) map_to_new_cvar)
      with 
       | Not_found -> t
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
      let new_suffix, min_id = min_excluded_I3 (global_env, map_to_suffix) binded_cvar in
      let new_cvar = {name = binded_cvar.name ; id = min_id ; def = None } in
      let prefix, _ = integer_suffix binded_cvar.name in
      let taken_suffix =
        try Senv.find prefix map_to_suffix with 
        | _ -> [] in
      let new_suffix_map =
        Senv.add
          prefix
          (new_suffix :: taken_suffix)
          map_to_suffix
      in
      let new_cvar_map = Senv.add binded_cvar.name (new_cvar) map_to_new_cvar in
      Tbind(binder, new_cvar, kind, aux_minimize_typ (global_env,new_suffix_map, new_cvar_map) t)

(** [do_minimize] tells whether types should be minimized. It defaults to
   [true] and may be changed with the `--rawtypes` command line option, *)
let do_minimize = spec_true "--rawtypes"  "Do not minimize types"

let minimize_typ env t =
  if !do_minimize then aux_minimize_typ (env,Senv.empty, Senv.empty) t else t

(** [type_typ env t] typechecks source type [t] returning its kind [k] and
   an internal representation of [t].  This may non-localized (Unbound and
   Kinding) typing error exceptions. *)
let rec type_typ env (t : styp) : kind * ctyp =
  match t with
  | Tprim c -> 
     Ktyp, Tprim c
  | Tvar(svar) ->
  let cvar =
    try 
     get_svar env svar
    with | Not_found -> raise Not_found
    in
    let kind = try
       find_cvar env cvar
      with 
        | Not_found -> default_kind
    in 
      kind, Tvar cvar  
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
    Ktyp,
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
  | Tvar cvar ->
    (try 
      let current_cvar = find_svar env (cvar.name) in
      if cvar.id <> current_cvar.id then
       raise (Escape cvar)
      else t 
    with Not_found | Escape _ ->
      match cvar.def with
      | None -> raise (Escape cvar)
      | Some def -> wf_ctyp env def.typ
    )
  | Tprim _ -> t
  | Tapp(t1, t2) ->
    (try 
      Tapp(wf_ctyp env t1, wf_ctyp env t2)
    with Escape cvar ->
      let typ1_expand, b = eager_expansion t1 in 
      if b then wf_ctyp env (head_norm (Tapp(typ1_expand, t2)))
      else raise (Escape cvar)
    )
  | Tarr(t1, t2) -> Tarr(wf_ctyp env t1, wf_ctyp env t2)
  | Tprod(typ_list) -> Tprod(List.map (wf_ctyp env) typ_list)
  | Trcd(lab_typ_list) -> Trcd(map_snd (wf_ctyp env) lab_typ_list)
  | Tbind(binder, cvar, kind, ctyp) ->
    let nenv = add_svar env cvar.name cvar in 
    Tbind(binder, cvar, kind, wf_ctyp nenv ctyp)

(* __________________________ 3. Type checking __________________________ *)

let (!@) = Locations.with_loc  
let (!@-) = Locations.dummy_located

let rec svar_to_cvar env (scar : styp) : (env * ctyp) =
  match scar with
  | Tvar(v) -> env,
    let cvar = get_svar env v in
   Tvar cvar     
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
    let _, ctyp = svar_to_cvar nenv styp in
    let def = { scope = -1 ; typ = ctyp } in
    let cvar = {name = var ; id ; def = Some def } in
    env, Tbind(b, cvar, kind, ctyp )

let styp_to_ctyp env styp =
  let env, ctyp = within_loc (within_typ (svar_to_cvar env)) styp in 
  env, norm ctyp 

let make_showdiff_error loc cur exp sub_cur sub_exp =
  Typing(Some loc, Expected(cur, Showdiff(exp, sub_cur, sub_exp)))

let rec find_binded_var pat =
  match pat.obj with
  | Pvar(evar) -> evar, None 
  | Ptyp(pat, t_annot) ->
    let binded_var, _ = find_binded_var pat in
    binded_var,  Some t_annot
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
    let _, t_annot = styp_to_ctyp env styp_loc in
   ( match diff_typ (norm t_expr) (norm t_annot) with
    | None -> t_annot
    | Some(subt_expr, subt_annot) -> raise (
      make_showdiff_error exp.loc t_expr t_annot subt_expr subt_annot
      )
    )
  | Eprod(exp_list) ->
    Tprod(
      List.map (type_exp env) exp_list
    )
  | Eproj(exp, n) -> 
    let ctyp = type_exp env exp in 
    let _, expand_ctyp = lazy_reduce_expand ctyp in 
    ( match norm expand_ctyp with
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
    let ctyp = type_exp env exp in 
    let _, expand_ctyp = lazy_reduce_expand ctyp in 
  ( match norm expand_ctyp with
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
    cross_binding env (Exp exp) binding_list
  | Eappl(exp, arg_list) ->
    let t_expr = type_exp env exp in
    norm(apply_arg env t_expr arg_list)
  | Elet(is_rec, pat, exp1, exp2) ->
    if is_rec then
      let nenv, binded_type = find_binded_type env pat exp1.obj in
      let t_expr1 = type_exp nenv exp1 in
      (match diff_typ (norm t_expr1) (norm binded_type) with 
      | None -> type_exp nenv exp2
      | Some(subt_expr1, sub_binded_type) -> raise (
        make_showdiff_error
          exp.loc 
          t_expr1 binded_type
          subt_expr1 sub_binded_type
        )
      ) 
    else 
      let binded_var, annot_var = find_binded_var pat in
      let t_exp1 = type_exp env exp1 in
      let nenv = 
        match annot_var with 
        | None -> env
        | Some styp_annot -> 
          let env, ctyp_annot = styp_to_ctyp env styp_annot in 
          (match diff_typ (norm t_exp1) (norm ctyp_annot) with
          | None -> env
          | Some (sub_t_exp1, sub_ctyp_annot) -> raise (
            make_showdiff_error exp1.loc t_exp1 ctyp_annot sub_t_exp1 sub_ctyp_annot
            )
          )
      in
      let nenv = add_evar nenv binded_var t_exp1 in
      type_exp nenv exp2
      

  | Epack(packed_styp, exp, styp_as) ->
    let env, ctyp_as = styp_to_ctyp env styp_as in
    let env, packed_ctyp = styp_to_ctyp env packed_styp in
    let _, expand_ctyp_as = lazy_reduce_expand ctyp_as in
    norm(typ_pack env packed_ctyp exp expand_ctyp_as )
  | Eopen(alpha, x, exp1, exp2) ->
    let exi_ctyp1 = type_exp env exp1 in 
    let _, expand_exi_ctyp1 = lazy_reduce_expand exi_ctyp1 in
    (match expand_exi_ctyp1 with
    | Tbind(Texi, beta, kind, ctyp1) ->
      let nenv, id = fresh_id_for env alpha in 
      let cvar = make_cvar alpha id None in
      let unpack_ctyp1 = subst_typ beta (Tvar(cvar)) ctyp1 in
      let nenv = add_evar nenv x unpack_ctyp1 in
      let ctyp2 = type_exp nenv exp2 in
      (*let _, expand_ctyp2 = lazy_reduce_expand ctyp2 in*)
      (try 
        norm(wf_ctyp env ctyp2)
      with 
        | Escape cvar -> raise (Typing(Some exp.loc, Escaping(ctyp2,cvar)))
      )
    | _ -> raise (
      Typing(
        Some exp.loc,
         Expected(exi_ctyp1, Matching(Sexi))
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
    let expected_ctyp = norm (subst_typ alpha tau' tau) in
    (match diff_typ (norm ctyp) (norm expected_ctyp) with
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


and find_binded_type env pat exp =
  match pat.obj with
  | Pvar(evar) -> (
    match exp with
    | Efun(args, exp_loc) ->
      (match exp_loc.obj with 
      | Eannot(_, styp_loc) ->
        let ctyp = cross_binding env (Typ styp_loc) args in 
        add_evar env evar ctyp, norm ctyp
      | _ -> raise (Typing(Some(pat.loc), Annotation(evar)))
      )
    | _ -> raise (Typing(Some(pat.loc), Annotation(evar)))
    )
  | Ptyp(x, styp_loc) -> (
      match x.obj with 
      | Pvar(evar) -> 
        let nenv, typ = styp_to_ctyp env styp_loc in
        add_evar nenv evar typ, norm typ
      | _ -> raise (complex_pattern pat)
  )
 | _ -> raise (complex_pattern pat)

and apply_arg env t_expr arg_list =
  match t_expr, arg_list with
  | Tbind(Tall, cvar, kind, ctyp), Typ(styp_loc) :: arg_list -> 
    let nenv, arg_ctyp = styp_to_ctyp env styp_loc in
    (* check kind compatibility *)
    let ctyp = subst_typ cvar arg_ctyp ctyp in
    apply_arg nenv ctyp arg_list 
  | Tarr(t1,t2), Exp(arg1) :: arg_list -> 
      let t_arg1 = type_exp env arg1 in
      (match diff_typ (norm t_arg1) (norm t1) with
      | None -> apply_arg env t2 arg_list
      | Some(subt_arg1, sub_t1) -> raise (
        make_showdiff_error arg1.loc t_arg1 t1 subt_arg1 sub_t1
        )
      )
  | _, [] -> t_expr
  | Tvar(cvar), Exp(arg1) :: q -> (
    match cvar.def with 
    | Some def -> apply_arg env (head_norm def.typ) arg_list
    | None -> raise (
      Typing(Some (arg1.loc), Expected(t_expr, Matching(Sarr)))
    )
  )
  | Tvar(cvar), Typ(styp_loc) :: q -> (
    match cvar.def with 
    | Some def -> apply_arg env (head_norm def.typ) arg_list
    | None -> raise (
      Typing(Some (styp_loc.loc), Expected(t_expr, Matching(Sall)))
    )
  )
  | Tapp(ctyp1, ctyp2), Typ(styp_loc) :: q  -> 
    let ctyp1_expand, b = eager_expansion ctyp1 in
    if b then apply_arg env (head_norm (Tapp(ctyp1_expand, ctyp2))) arg_list 
    else raise (
      Typing(Some (styp_loc.loc), Expected(t_expr, Matching(Sall))))
  
  | Tapp(ctyp1, ctyp2), Exp(arg1) :: q  -> 
    let ctyp1_expand, b = eager_expansion ctyp1 in
    if b then apply_arg env (head_norm (Tapp(ctyp1_expand, ctyp2))) arg_list 
    else raise (
      Typing(Some (arg1.loc), Expected(t_expr, Matching(Sall))))

  | _, Exp(arg1) :: q -> raise (
    Typing(Some (arg1.loc), Expected(t_expr, Matching(Sarr)))
  )
  | _, Typ(styp_loc) :: q -> raise (
    Typing(Some (styp_loc.loc), Expected(t_expr, Matching(Sall)))
  )

and cross_binding env expr = function
  | [] -> (
      match expr with 
      | Exp(body_exp) -> type_exp env body_exp
      | Typ(styp_loc) -> snd (styp_to_ctyp env styp_loc)
  )
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
      let kind, ctyp = type_typ env styp_loc in
      let ctyp = norm ctyp in
      let def = { scope = 0 ; typ = ctyp } in
      let cvar = make_cvar svar id (Some def) in
      let nenv = add_svar nenv svar cvar in
      let nenv = add_cvar nenv cvar kind in
      nenv, Gtyp(cvar, Exp(kind, minimize_typ env ctyp))

    | Typ(kind) ->
      let env, id = fresh_id_for env svar in
      let cvar = make_cvar svar id None in
      let nenv = add_cvar env cvar kind in
      nenv, Gtyp(cvar,Typ(kind))
  )
  | Dlet(is_rec, pat, exp) ->
    let binded_var, _ = find_binded_var pat in
    if is_rec then
      let nenv, binded_type = find_binded_type env pat exp.obj in
      let ctyp = type_exp nenv exp in
      (match diff_typ (norm ctyp) (norm binded_type) with 
      | None -> nenv, Glet(binded_var, minimize_typ env ctyp)
      | Some(sub_ctyp, sub_binded_type) -> raise (
        make_showdiff_error
        exp.loc
        ctyp binded_type
        sub_ctyp sub_binded_type
      )
    )
    else 
      let ctyp_exp = type_exp env exp in
      let binded_var, annot_var = find_binded_var pat in
      let nenv, ctyp = 
        match annot_var with 
        | None -> env, ctyp_exp
        | Some styp_annot -> 
          let nenv, ctyp_annot = styp_to_ctyp env styp_annot in 
          (match diff_typ (norm ctyp_exp) (norm ctyp_annot) with
          | None -> nenv, ctyp_annot
          | Some (sub_ctyp_exp, sub_ctyp_annot) -> raise (
            make_showdiff_error exp.loc ctyp_exp ctyp_annot sub_ctyp_exp sub_ctyp_annot
            )
          )
      in
      (add_evar nenv binded_var ctyp_exp), Glet(binded_var, minimize_typ env ctyp)
        
  | Dopen(alpha, evar, exp) ->
    let ctyp = type_exp env exp in 
    let _, expand_ctyp = lazy_reduce_expand ctyp in
    match expand_ctyp with 
    | Tbind(Texi, beta, kind, ctyp_body) -> 
      let nenv, id = fresh_id_for env alpha in
      let cvar = make_cvar alpha id None in
      let unpack_ctyp_body = subst_typ beta (Tvar(cvar)) ctyp_body in
      let nenv = add_evar nenv evar unpack_ctyp_body in 
      let nenv = add_svar nenv alpha cvar in 
      (add_cvar nenv cvar kind), Gopen(cvar, evar, (minimize_typ env (norm unpack_ctyp_body)))
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

