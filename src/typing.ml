(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-27-32-33-37-39-60"]
open Util
open List
open Syntax
open Type
open Error

(** 1. Environments *)


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

(** 2. Type minimization *)

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
  let _ = find_cvar env cvar in
  let min_excluded_list id_list =
    let n = List.length id_list in
    let id_tab = Array.make n 0 in
    List.iter (fun x -> if x < n then id_tab.(x) <- 1) id_list ;
    let i = ref 0 in
    while (!i < n && id_tab.(!i) = 0) do
      incr i
    done ;
    !i
  in
  let id_list =
    Tenv.fold 
      (fun cvar_key _ ind_list ->
        if cvar_key.name = cvar.name then (cvar.id) :: ind_list
        else ind_list
      )
      env.cvar
      []
  in
  let mex = min_excluded_list id_list in
  { name = cvar.name ; id = mex ; def = cvar.def }

let minimize_env env = env


(** [minimize_typ env t] returns a renaming of [t] that minimizes the
   variables suffixes but still avoids shallowing internally and with
   respect to env [env] *)
let rec aux_minimize_typ (global_env, map_to_new_name) (t :ctyp) =
  let env = (global_env, map_to_new_name) in
  match t with
    | Tvar(cv) -> Tvar(Tenv.find cv map_to_new_name)
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
      Tprod(
        List.fold_left
          (fun l t -> (aux_minimize_typ env t) :: l)
          []
          ctyp_l
      )
    | Trcd(rcd_l) ->
      Trcd(
        List.fold_left
          (fun l (lab, t) -> (lab, aux_minimize_typ env t) :: l)
          []
          rcd_l
      )
    | Tbind(binder, binded_cvar, kind , t) ->
      let min_binded = min_excluded (global_env, map_to_new_name) binded_cvar in
      let new_map = Tenv.add binded_cvar min_binded map_to_new_name in
      Tbind(binder, min_binded , kind, aux_minimize_typ (global_env,new_map) t)


(** [do_minimize] tells whether types should be minimized. It defaults to
   [true] and may be changed with the `--rawtypes` command line option, *)
let do_minimize = spec_true "--rawtypes"  "Do not minimize types"

let minimize_typ env t =
  let min_env = minimize_env env in
  if !do_minimize then aux_minimize_typ (min_env, Tenv.empty) t else t

(** [type_typ env t] typechecks source type [t] returning its kind [k] and
   an internal representation of [t].  This may non-localized (Unbound and
   Kinding) typing error exceptions. *)
let rec type_typ env (t : styp) : kind * ctyp =
  match t with
  | Tprim  c -> 
     Ktyp, Tprim c
  | _ -> failwith "not implemented" 

(** Checking that lovcal variable do not escape.  Typechecking of
   existential types requires that locally abstract variables do not escape
   from their scope.  This amounts to verifying that the returned type is
   well-formed.  It suffices to check that all variables are bound in the
   given environment.

   One must be careful of non linear redexes and delayed definitions.
   Therefore, we must not only check for well-formedness, but return an
   equivalent type that is well-formed.  This should just perform the
   necessary unfoldings and reductions.  *)
exception Escape of cvar
let rec wf_ctyp env t : ctyp =
  match t with
  | Tvar a -> 
     (* fix me *)
     if true then t else raise (Escape a)
  | _ -> t


let (!@) = Locations.with_loc  
let (!@-) = Locations.dummy_located

let infer_kind env ctyp = default_kind
  (*match ctyp with 
  | Tvar(cvar) -> find_cvar env cvar
  | Tprim(_) -> default_kind
  | Tarr(k1, k2) -> Karr(infer_kind env k1, infer_kind env k2)*)

let make_cvar name id def =
  { name ; id ; def}

let rec svar_to_cvar env (scar : styp) : (env * ctyp) =
  match scar with
  | Tvar(v) -> env, Tvar(Senv.find v env.svar)
  | Tprim(x) -> env, Tprim(x)
  | Tapp(s1, s2) | Tarr(s1, s2) ->
    let env1, c1 = svar_to_cvar env s1 in
    let env2, c2 = svar_to_cvar env1 s2 in
    env2, Tapp(c1, c2)
  | Tprod(s_list) ->
    let nenv, c_list = 
      List.fold_left
        (fun (env, l) s ->
          let nenv, c = (svar_to_cvar env s) in
          nenv, c :: l
        )
        (env, [])
        s_list
    in 
    nenv, Tprod(c_list)
  | Trcd(labs_list) ->
    let nenv, labc_list =
      List.fold_left
        (fun (env,l) (lab,s) ->
          let nenv, c = (svar_to_cvar env s) in
          nenv, (lab, c) :: l
        )
        (env, [])
        labs_list
    in 
    nenv, Trcd(labc_list)
  | Tbind(b, var, kind, s_typ) ->
    let nenv, id = fresh_id_for env var in
    let cvar = {name = var ; id ; def = None } in
    let nenv, c_typ = svar_to_cvar nenv s_typ in
    nenv, Tbind(b, cvar, kind, c_typ )

let is_pvar x = 
  match x.obj with
  | Pvar(_) -> true
  | _ -> false

let find_binded_type env pat exp =
  match pat with
  | Pvar(evar) -> (
    match exp with
    | Eannot(_, styp_loc) ->
      let nenv, typ = svar_to_cvar env (styp_loc.obj) in
      add_evar nenv evar typ, Some(typ)
    | _ -> env, None
  )
  | Ptyp(x, styp_loc) -> (
      match x.obj with 
      | Pvar(evar) -> 
        let nenv, typ = svar_to_cvar env (styp_loc.obj) in
        add_evar nenv evar typ, Some(typ)
      | _ -> failwith "Complex Pattern Not Implemented"
  )
 | _ -> failwith "Complex Pattern Not Implemented"


let rec type_exp env exp : ctyp =
  match exp.obj with 
  | Evar x -> get_evar exp env x
  | Eprim (Int _) -> Tprim Tint
  | Eprim (Bool _) -> Tprim Tbool
  | Eprim (String _) -> Tprim Tstring
  | Eannot(exp, styp_loc) ->
    let t_expr = type_exp env exp in
    let nenv, t_annot = svar_to_cvar env styp_loc.obj in
   ( match diff_typ t_expr t_annot with
    | None -> t_annot
    | Some(_) ->  failwith "type error")
  | Eprod(exp_list) ->
    Tprod(
      List.fold_left
        (fun l exp -> 
          (type_exp env exp) :: l
        )
        []
        exp_list
    )
  | Eproj(exp, n) ->(
    match type_exp env exp with
      | Tprod(typ_list) -> List.nth typ_list n
      | _ -> failwith "Ill typed")
  | Ercd(labexp_list) ->
    Trcd(
      List.fold_left
        (fun l (lab,exp) -> 
          (lab, type_exp env exp) :: l
        )
        []
        labexp_list
    )
  | Elab(exp, lab) -> 
    (match type_exp env exp with
      | Trcd(labexp_list) ->
        (try
          snd (List.find (fun (lab_i,_) -> lab_i = lab ) labexp_list)
        with
        | Not_found -> failwith "Ill typed")
      | _ -> failwith "Ill typed")

  | Efun(binding_list, exp) ->
    cross_binding env exp binding_list
  | Eappl(exp, arg_list) ->
    let t_expr = type_exp env exp in
    apply_arg env t_expr arg_list
  | Elet(is_rec, pat, exp1, exp2) ->
    let nenv, opt_binded_type = find_binded_type env pat.obj exp1.obj in
    let t_expr1 = type_exp nenv exp1 in
    (match opt_binded_type with 
    | None -> type_exp nenv exp2
    | Some(binded_type) ->
      (match diff_typ binded_type t_expr1 with 
      | None -> type_exp nenv exp2
      | Some(_) -> failwith "Ill Typed") )

  | Epack(_)
  | Eopen(_) -> failwith "not implemented"

and apply_arg env t_expr arg_list =
  match t_expr, arg_list with
  | Tarr(t1,t2), arg1 :: arg_list -> (
    match arg1 with
    | Exp(arg1) -> 
      let t_arg1 = type_exp env arg1 in 
      (match diff_typ t1 t_arg1 with
      | None -> apply_arg env t2 arg_list
      | Some(_) -> failwith "Ill typed"
      )
    | Typ(_) -> failwith "not Implemented"
  ) 
  | _, [] -> t_expr
  | _, t::q -> failwith "Too much argument (or cannot be applied)"

and cross_binding env expr = function
  | [] -> type_exp env expr
  | (Typ(svar,kind)) :: q ->
    let nenv, id_svar = fresh_id_for env svar in 
    let cvar = make_cvar svar id_svar None in
    Tbind(Tlam, cvar, kind, cross_binding nenv expr q)
  | Exp(pat) :: q -> (
    match pat.obj with
    | Ptyp(pat, styp_loc) -> 
      (match pat.obj with 
        | Pvar(evar) ->
          let tp_evar = "temporary" in
          let nenv, id_svar = fresh_id_for env tp_evar in
          let cvar = make_cvar tp_evar id_svar None in
          let nenv = add_svar nenv tp_evar cvar in
          let nenv, ctyp = svar_to_cvar nenv (styp_loc.obj) in
          let nenv = add_evar nenv evar ctyp in
          Tbind(Tlam, cvar, infer_kind env ctyp, cross_binding nenv expr q)
        | _ -> failwith "Not implemented")
    | Pvar(evar) ->  failwith "Missing annotation"
    | Pprod(pat_list) -> failwith "Not implemented"
    | Pprim(prim_val) -> failwith "Not implemented"
  )

let norm_when_eager =
  spec_true "--loose"  "Do not force toplevel normalization in eager mode"

let type_decl env (d :decl) = 
  match d.obj with
    | Dtyp(_)
    | Dlet(_)
    | Dopen(_) ->
     failwith "Not implemented"

  
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

