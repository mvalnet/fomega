%{
  open Syntax
  open Locations

  let error r (loc : unit loc) =
    let err = Error.Parse (r, loc_ loc.loc.loc_start loc.loc.loc_end) in
    raise (Error.Parsing err)
    
  let unclosed symb pos1 pos1' decl symb' pos2 pos2' =
    let loc1 = loc_ pos1 pos1' in
    let loc2 = loc_ pos2 pos2' in
    let err = Error.Unclosed ((symb, loc1), decl, (symb', loc2)) in
    raise (Error.Parsing err)
    
%}

%token EOF
%token <string> LIDENT CIDENT 
%token <string> STRING
%token <int> INT
%token DOT COLON COLONCOLON EQUAL
(* %token SEMI *)
%token LPAREN RPAREN

%token COMMA SEMI
%token LBRACKET RBRACKET
%token LBRACE RBRACE
%token LANGLE RANGLE
%token ALL EXI LAMBDA FUN
%token LET REC IN TYPE AS
(* %token PACK OPEN AS *)
(* %token IF THEN ELSE  *)
%token ARROW DOUBLEARROW
%token STAR TTYPE DOLAR INCLUDE OPTION VAL
(* %token PLUS MINUS *)

(* %nonassoc THEN       (\* Dangling else *\)
 * %nonassoc ELSE       (\* cf. THEN   *\) *)

(* %right    ARROW DOUBLEARROW
 *                      (\* Associativity in type declaration *\) *)

%start <Syntax.styp_loc> typ_
%start <Syntax.exp> exp_
%start <Syntax.decl> decl_
%start <directive list * Syntax.program> program
%start <svar typed_decl_ list> interface

%%

%inline separated_list_mintwo(separator, X):
| x = X; separator; l = separated_nonempty_list(separator, X)
    { x :: l }

%inline paren(X):
| LPAREN; x = X; RPAREN { x }

%inline brace(X):
| LBRACE; x = X; RBRACE { x }

record(X):
| { [] }  
| SEMI { [] }  
| x = X  { [x] }  
| x = X SEMI r =record(X) { x :: r }

%inline list_option(X):
| { [] }
| x = X  { x }

%inline l(X):
   x = X { loc x $startpos(x) $endpos(x) }
         
%inline lerror:
e = l(error) { e }

%inline lab :
| s = CIDENT { s }
| s = LIDENT { s }

%inline var :
| s = CIDENT { s }
| s = LIDENT { s }

%inline evar : a = var { evar a}
%inline tvar : a = var { svar a}

kind_atom:
| DOLAR { Ktyp }
| TTYPE { Ktyp }
| TYPE { Ktyp }
| k = paren(kind) { k }

kind:
| k = kind_atom { k }
| k1 = kind_atom ARROW k2 = kind { Karr (k1, k2) }

%inline
kind_option: 
| { default_kind } 
| COLONCOLON k = kind { k } 

typ_field:
| l = lab COLON t = typ { l, t }

typ_atom:
| a = tvar { Tvar a }
| t = paren(typ) { t }
| fl = brace(record(typ_field)) { Trcd fl }
                    
typ_app:
| t = typ_atom { t } 
| t1 = typ_app  t2 = typ_atom { Tapp (t1, t2) }

typ_prod:
| t = typ_app { t } 
| tl = separated_list_mintwo(STAR,typ_app) { Tprod tl }

typ_arr:
| t = typ_prod { t } 
| t1 = typ_prod  ARROW t2 = typ_arr { Tarr (t1, t2) }

%inline tbind:
| a = tvar k = kind_option { a, k }
| LPAREN a = tvar k = kind_option RPAREN { a, k }

typ:
| t = typ_arr { t } 
| EXI ak = tbind DOT t = typ { Tbind (Texi, fst ak, snd ak, t) }
| ALL ak = tbind DOT t = typ { Tbind (Tall, fst ak, snd ak, t) }
| LAMBDA ak = tbind DOT t = typ { Tbind (Tlam, fst ak, snd ak, t) }
| FUN ak = tbind DOUBLEARROW t = typ { Tbind (Tlam, fst ak, snd ak, t) }
| err = lerror { error "Syntax error: type" err }

%inline
pat_atom:
| x = evar { Pvar x }
| p = paren(pat) { p }
  
pat_annot:
| p = pat_atom { p }
| p = l(pat_atom) COLON t = l(typ) { Ptyp (p, (t : styp_loc)) }

pat:
| p = pat_annot { p }
| pl = separated_list_mintwo (COMMA, l(pat_annot)) { Pprod pl }

binding:
| LBRACKET a = tvar k = kind_option RBRACKET { Typ (a, k) }
| p = l(pat_atom) { Exp p }
| err = lerror { error "Binding Expected" err }

%inline pat_typ:
| p = l(pat_atom) COLON t = l(typ) { Ptyp (p, t) }
| p = l(pat_atom) COMMA pl = separated_nonempty_list (COMMA, l(pat_annot))
      { Pprod (p::pl) }

fun_bindings: 
  | b = nonempty_list(binding) { b }
  | p = l(pat_typ)  { [Exp p] }
  | a = tvar COLONCOLON k = kind  { [Typ (a, k)] }

(* let_bindings: 
 *   | b = nonempty_list(binding) { b }
 *   | p = l(pat_atom)  { [Exp p] }
 *   | a = tvar COLONCOLON k = kind  { [Typ (a, k)] } *)

exp_field:
| l = lab EQUAL e = l(exp) { l, e }
| l = lab COLON t = l(typ) EQUAL e = l(exp)
    { l, loc (Eannot (e,t)) $startpos(t) $endpos(e) }
| l = lab
    { l, loc (Evar (evar l)) $startpos(l) $endpos(l) }
        
exp_atom:
| x = evar  { Evar x }
| i = INT     { Eprim (Int i) }
| s = STRING  { Eprim (String s) }
| e = l(exp_atom) DOT i = INT  { Eproj (e, i) }
| e = l(exp_atom) DOT l = lab  { Elab (e, l) }
| fl = brace(record(exp_field))  { Ercd fl }
| LANGLE t1 = l(typ) COMMA e = l(exp) AS t2 = l(typ) RANGLE
    { Epack (t1, e, t2) }
| LPAREN RPAREN { Eprod [] }
| e = paren(exp) { e }

exp_arg:
| e = l(exp_atom) { Exp e } 
| LBRACKET t = l(typ) RBRACKET  { Typ t }

exp_app:
| e = exp_atom { e }
| e = l(exp_app) COLON t = l(typ) { Eannot (e,t) }
| e = l(exp_atom) el = nonempty_list(exp_arg) { Eappl (e, el) }

exp_prod:
| e = exp_app { e }
| el = separated_list_mintwo (COMMA, l(exp_app)) { Eprod el }

exp_abs:
| e = exp_prod { e }
| FUN b = fun_bindings DOUBLEARROW e = l(exp) { Efun (b, e) } 
(* | FUN b = fun_bindings COLON t = l(typ) DOUBLEARROW e = l(exp)
 *     { Efun (b, loc (Eannot (e, t)) $startpos(e) $endpos(t)) }  *)

exp:
| e = exp_abs { e }
| LET LANGLE a = tvar COMMA x = evar RANGLE EQUAL e1 = l(exp) IN e2 = l(exp)
    { Eopen (a, x, e1, e2) }
| LET b = boption(REC) p = l(pat) EQUAL e1 = l(exp) IN e2 = l(exp)
    { Elet (b, p, e1, e2) }
| LET b = boption(REC) p = l(pat_atom) e1 = l(let_fun) IN e2 = l(exp)
    { Elet (b, p, e1, e2) }
| err = lerror { error "Syntax error: exp" err }

%inline
let_fun:
| args = nonempty_list(binding) EQUAL e = l(exp)
    { Efun (args, e) }
| args = nonempty_list(binding) COLON t = l(typ) EQUAL e = l(exp)
    { let et = loc (Eannot (e,t)) $startpos(t) $endpos(e) in
      Efun (args, et) }  
                                                             
type_lam:
| EQUAL t = typ { t }
| a = tvar k = kind_option t = type_lam
   {Tbind (Tlam, a, k, t) }
| LPAREN a = tvar COLONCOLON k = kind RPAREN t  = type_lam
   {Tbind (Tlam, a, k, t) }

(* Phrases *)
decl:
| LET b = boption(REC) p = l(pat) EQUAL e = l(exp)
   { Dlet (b, p, e) }
| LET b = boption(REC) p = l(pat_atom) e = l(let_fun)
   { Dlet (b, p, e) }
| LET LANGLE a = tvar COMMA x = evar RANGLE EQUAL e1 = l(exp) 
    { Dopen (a, x, e1) }
| TYPE a = tvar t = l(type_lam) { Dtyp (a, Exp t) }
| TYPE a = tvar { Dtyp (a, Typ default_kind) }
| TYPE a = tvar COLONCOLON k = kind { Dtyp (a, Typ k) }
| err = lerror { error "Syntax error: decl" err }

directives:
| INCLUDE s = STRING l = directives {  Include s :: l } 
| OPTION  s = STRING l = directives {  Flag s :: l } 
|  { [] } 

typed_decl:
| VAL x = evar COLON t = typ { Glet (evar x, t) }
| VAL LANGLE a = tvar COMMA x = evar RANGLE EQUAL t = typ
    { Gopen (svar a, evar x, t) }
| TYPE a = tvar k = kind_option { Gtyp (svar a, Typ k) }
| TYPE a = tvar k = kind_option EQUAL t = typ { Gtyp (svar a, Exp (k, t)) }


(* Entry points *)

program:
| dirs = directives p = list(l(decl)) EOF { dirs, p }

interface:
| p = list(typed_decl) EOF { p }


typ_:  t = l(typ) EOF { t }
exp_:  e = l(exp) EOF { e }
decl_: d = l(decl) EOF { d }
                      
