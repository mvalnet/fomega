open Syntax

module S =
  struct
    let exists = "exi " 
    let forall = "all " 
    let lambda = "lam " 
    let llambda = "Fun "
    let lamdot = "=>"
  end

module P =
  struct
    include PPrint
    let doublecolon = !^ "::"
    let arrow = !^ "->"
    let doublearrow = !^ "=>"
    let break0 = break 0
    let break1 = break 1
    let nest2 = nest 2
    let exi = !^ S.exists
    let all = !^ S.forall
    let lam = !^ S.lambda
    let llam = !^ S.llambda
    let lamdot = !^ S.lamdot
    let separator sep = sep ^^ break1
    let binary sep = space ^^ separator sep
                       

    let int n = string (string_of_int n)

    let (^^^) x y = x ^^ space ^^ y
    let (^/^) x y = x ^^ break1 ^^ y

    let abs left bind right exp =
      group (left ^^ bind ^^ right ^^ nest2 (break1 ^^ group exp))
  end

let (^^) = P.(^^)
let (!^) = P.string
let (^^^) = P.(^^^)
let (^/^) = P.(^/^)


let prod sep f l = P.group (P.flow_map (sep ^^ P.break1) f l)
let braces doc = P.hang 1 (P.lbrace ^^ doc ^^ P.rbrace)
let angles doc = P.hang 1 (P.langle ^^ P.group doc ^^ P.rangle)

let show_def = Util.spec_false  "--showdef"  "Show type aliases."

let svar n = !^ n
let cvar a =
  let n = svar a.name in
  if a.id > 0 then n (* ^^ !^"!"*) ^^ P.int a.id else n

let dvar id a =
  let n = svar a.name in
  if id > 0 then n ^^ P.int id
  else if id < 0 then n ^^ !^"/" ^^ (P.int (- id))
  else n

let evar (x : evar) = !^ x

let var v =
  match v with
  | Exp x -> evar x
  | Typ a -> svar a

let prim_typ t =
  P.string
    begin match t with
    | Tint -> "int"
    | Tbool -> "bool"
    | Tstring -> "string"
    | Tunit -> "unit"
    end

let prim_val v =
  P.string
    begin  match v with
    | Int i -> string_of_int i
    | Bool b ->  if b then "true" else "false"
    | String s -> s 
    end

type level = Atom | App | Prod | Arr | Abs | Let | Max

let kind_level = function
  | Ktyp -> Atom
  | Karr (_,_) -> Max

let rec kind_ p k =
  let actual = kind_level k in
  let kind' = kind_ actual in
  let doc = 
    match k with
    | Ktyp 	    -> !^ "Type" (* P.dollar *)
    | Karr (k1, k2) -> P.group (kind_ Atom k1 ^^^ P.arrow ^/^ kind' k2)
  in
  if actual > p then P.parens doc else doc

let kind = kind_ Max

let show_Type = Util.spec_false  "--Type"  "show kind Type"

let tbind a k = 
    match k with
    | Ktyp when not !show_Type -> a
    | k -> P.group (a ^^^ P.doublecolon ^/^ (kind k))

(* let tabs left a k t = P.abs left (tbind a k) P.dot t *)

let typ_level t =
  match t with 
  | Tvar _ | Tprim _ -> Atom | Trcd _ -> Atom
  | Tapp (_, _) -> App
  | Tprod _ -> Prod
  | Tarr (_, _) -> Arr
  | Tbind (_, _, _, _) -> Abs

let hv n doc = P.hang n (P.group doc)
type doc = P.document
type docl = Doc of doc | Right of doc list | Left of doc list
let flow dl = P.hang 2 (P.group (P.flow P.break1 dl))
    
let docof docl =
  match docl with
  | Doc d -> P.group d
  | Right dl -> flow dl
  | Left dl -> flow (List.rev dl)

(** Left associative *)
let (>>@) d docl =
  match docl with
  | Right dl -> Right (d :: dl)
  | Doc d1 -> Right [d; d1]
  | flow -> Doc (d ^/^ docof flow)
  
(** Right associative *)
let (@<<) docl d = 
  match docl with
  | Left dl -> Left (d :: dl)
  | Doc d1 -> Left [d; d1]
  | flow -> Doc (docof flow ^/^ d)
let parif b docl = 
  if b then Doc (P.hang 1 (P.parens (docof docl))) else docl

let binder b =
  match b with
  | Tlam -> P.lam
  | Tall -> P.all
  | Texi -> P.exi

let typ tvar =
  let rec typ_docl level t =
    let actual = typ_level t in
    let typ' = typ_docl actual in
    parif (actual > level)
      begin match t with
      | Tvar a	      -> Doc (tvar a)
      | Tprim pt	      -> Doc (prim_typ pt)
      | Trcd tl	      -> Doc (braces (prod P.semi typ_field tl))
      | Tapp (t1, t2)   -> typ' t1 @<< typ_  Atom t2
      | Tprod []	      -> Doc (!^ "unit")
      | Tprod tl	      -> Doc (prod (P.space ^^ P.star) (typ_ App) tl)
      | Tarr (t1, t2)   -> typ_ App t1 ^^^ P.arrow >>@ typ' t2
      | Tbind (b, a, k, t)  -> binder b ^^ tbind (tvar a) k ^^ P.dot >>@ typ' t
      end
  and typ_field (l, t) =
    P.hang 2 (P.string l ^^^ P.colon ^^^ typ_ Max t)

  and typ_ level t = docof (typ_docl level t)  in
  fun t -> P.group (typ_ Max t)            

let styp t = typ svar t
let ctyp t = typ cvar t
let tdef a =
  let doc = cvar a in 
  match a.def with
  | Some t when !show_def ->
     P.group (doc ^^ !^"[" ^^ P.break0 ^^ typ cvar t.typ ^^ !^"]")
  | _ -> doc

let dtyp t = typ tdef t
   
let styp_ t = styp t.obj

let pat_level p =
  match p.obj with
  | Pvar _ -> Atom
  | _ -> Max
                       
let rec pat_ level p = 
  let actual = pat_level p in
  let pat' = pat_ actual in
  let doc = 
    match p.obj with
    | Pvar v        -> evar v
    | Ptyp (p, t)   -> P.group (pat' p ^^^ P.colon ^/^ styp_ t)
    | Pprod pl 	    -> prod P.comma (pat_ Atom) pl
    | Pprim pv 	    -> prim_val pv
  in
  if actual > level then P.parens doc else doc

let pat = pat_ Max

let binding b =
  match b with
  | Typ (a, k)    -> P.brackets (tbind (svar a) k)
  | Exp p         -> hv 2 (pat_ Atom p)

let eabs left p exp =
  P.abs left p (P.space ^^ P.lamdot) exp
  
let exp_level e =
  match e.obj with
  | Evar _  | Eprim _ | Eproj (_, _) | Elab (_, _) | Ercd _ 
  | Epack (_, _, _) -> Atom
  | Eappl (_, _) -> App
  | Eprod _ | Eannot (_,_) -> Prod 
  | Efun (_, _) -> Abs
  | Eopen (_, _, _, _) 
  | Elet (_, _, _, _) -> Let

let rec exp_docl level e =
  let actual = exp_level e in
  let exp' = exp_docl actual in
  let exp_let (b, p, e1, e2) = 
    Doc (P.group begin
        P.group begin P.hang 2 begin
            P.string (if b then "let rec" else  "let")
            ^/^ P.group p
            ^^^ P.equals
            ^/^ docof (exp' e1) ^^^ !^ "in"
          end end
        ^/^ docof (exp' e2)
      end) in
  parif (actual > level)
    begin match e.obj with
      (* atom_level *)                      
      | Evar v	        -> Doc (evar v)
      | Eprim pv        -> Doc (prim_val pv)
      | Eproj (e, i)    -> Doc (exp_ actual e ^^ P.break0 ^^ P.dot ^^ P.int i)
      | Elab (e, l )    -> Doc (exp_ actual e ^^ P.break0 ^^ P.dot ^^ P.string l)
      | Ercd fl ->
          let typ_field (l, e) =
            P.hang 2 (P.group (P.string l ^^ !^ " =" ^/^ exp_ Prod e)) in
          Doc (braces (prod P.semi typ_field fl))
      | Epack(t1,e,t2)  ->
         Doc (angles
                (styp_ t1 ^^ P.comma ^/^ exp_ Max e ^^^ !^"as" ^/^ styp_ t2))

      (* app_level *)
      | Eappl (e, args) ->
          let exp_arg typorexp =
            match typorexp with
            | Typ t -> P.brackets (styp_ t)
            | Exp arg -> exp_ Atom arg in
          Right (exp_ Atom e :: List.map exp_arg args)

      (* prod_level *)  
      | Eprod [] 	-> Doc (!^ "()")
      | Eprod el 	-> Doc (prod P.comma (exp_ App) el)
      | Eannot (e, t)   -> Doc (exp_ actual e ^/^ P.colon ^^^ styp t.obj)

      (* abs *) 
      | Efun (bl, e)    ->
          Doc (P.hang 2
                 (P.hang 2
                    (P.flow P.break1 (!^ "fun" :: List.map binding bl))
                  ^^^ P.doublearrow ^/^ docof (exp' e)))

      (* let_level *)
      | Elet (b, p, e1, e2)  ->
          exp_let (b, pat p, e1, e2)
      | Eopen (a, x, e1, e2) ->
          let tx = angles (svar a ^^ P.comma ^^ evar x) in
          exp_let (false, tx, e1, e2)
    end


and exp_ level e = docof (exp_docl level e)

let exp e = P.group (exp_ Max e)


let val_xk_t key xk sep t = P.group (P.hang 2 (!^ key ^^^ xk ^^^ sep ^/^ t))
let val_xk  x sep k = P.group  (x ^^^ sep ^/^ k)
          

let decl (d : decl_) =
  match d with
  | Dlet (b, p, e) ->
     val_xk_t (if b then "let rec" else  "let") (pat p) P.equals (exp e)
  | Dtyp (a, Typ k) -> !^"type" ^^^ (tbind (svar a) k)
  | Dtyp (a, Exp t) -> val_xk_t "type" (svar a) P.equals (styp_ t)
  | Dopen (a, x, e) -> 
     let ax = angles (svar a ^^ P.comma ^^ evar x) in
     val_xk_t "let" ax P.equals (exp e)

let typed_decl tvar d =
  match d with
  | Glet (x, t) -> val_xk_t "val" (evar x) P.colon (typ tvar t)
  | Gtyp (a, Typ k) -> !^ "type" ^^^ (tbind (tvar a) k)
  | Gtyp (a, Exp (k, t)) ->
     val_xk_t "type" (tbind (tvar a) k)
       P.equals (typ tvar t)
  | Gopen (a, x, t) ->
     let ax = angles (tvar a ^^ P.comma ^^ evar x) in
     val_xk_t "val" ax P.equals (typ tvar t)
       
let string doc =
  let buf = Buffer.create 113 in
  P.ToBuffer.pretty 1. 76 buf (P.hang 0 doc);
  Buffer.contents buf

let print chan doc =
  Printf.fprintf chan "%s" (string doc)

let print_lines chan docss =
  let doc =
    let inner docs = P.hang 2 (P.group (P.separate P.break1 docs)) in
    P.separate_map P.break0 inner docss in
  print chan doc;
  print chan P.break0;;

let prerr_lines = print_lines stderr

(** For debugging purposes *)
let prerr docs =
  let doc = P.hang 2 (P.separate_map P.break1 P.group docs) in
  prerr_endline (string doc)

let prerr_str strings =  prerr (List.map (!^) strings)
         
let prerr_styp s t = prerr_endline (s ^ string (styp t))
let prerr_ctyp s t = prerr_endline (s ^ string (ctyp t))
