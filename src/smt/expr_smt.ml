(*
   Base modules that defines the terms used in the prover.
*)

module Dom = Vpl.WDomain
(* module Dom = Vpl.NCDomain.NCVPL_Unit *)
module Polynomial = Dom.I_Q.Term
module Var = Vpl.Var.Positive

type cmpT = Vpl.Cstr.cmpT_extended
type coeff = Vpl.Scalar.Rat.t
type polynomial = Polynomial.t
type condition = cmpT * Polynomial.t(* Dom.I_Q.CQCstr.t *)(* Vpl.Cstr.cmpT_extended * Dom.I_Q.Term.t *)


(* module Ident = Vpl.UserInterface.Lift_Ident (struct
    type t = string
    let compare = Pervasives.compare
    let to_string s = s
    end)

module VExpr = struct
  module Ident = Ident

  type t = Vpl.UserInterface.Polynomial.t

  exception Out_of_Scope

  let to_term p: polynomial =
  let term_list = List.map
    (fun (vl,c) ->
    let l = Polynomial.Prod (List.map (fun v -> Polynomial.Var v) vl)
    in
    Polynomial.Mul (Polynomial.Cte c, l))
    (Vpl.UserInterface.CP.Poly.data2 p)
  in
  Polynomial.Sum term_list
end *)

(* module VPL = IntVpl.Interface(Vpl.NCDomain.NCVPL_Unit.Q)(VExpr) *)
type polyhedre = (* Dom.I_Q.t *)Dom.P.t

let empty: polyhedre =
  Dom.I_Q.top

let is_bottom (p: polyhedre): bool =
  Dom.I_Q.is_bottom p

let assume (cl: condition list) (e: polyhedre): polyhedre =
  Dom.I_Q.assume cl e

let to_cond (s: cmpT) (g: polynomial) (d: polynomial): condition =
  (s,(Polynomial.Add(d,Polynomial.Opp(g))))

let to_coeff (n: float): coeff =
  Vpl.Scalar.Rat.of_float n

let to_cmpT (cmp: Vpl.Cstr.cmpT): cmpT =
  match cmp with
  | Eq -> EQ
  | Le -> LE
  | Lt -> LT

(* (Vpl.Scalar.Rat.t * Vpl.Pol.Cs.t) list *)
let get_bottom_cert (p: polyhedre): (cmpT * polynomial) list =
  match Dom.I_Q.get_bottom_cert p with
  | Some(f) ->
    List.fold_left (fun x (co,cp) ->
    let cs = Vpl.WrapperTraductors.CP.ofCstr cp in
    let cp = ((to_cmpT cs.Vpl.WrapperTraductors.CP.typ),Polynomial.Poly(cs.Vpl.WrapperTraductors.CP.p)) in
    if co != Vpl.Scalar.Rat.z then
      (cp::x)
    else
      x) [] f
  | None -> failwith "cert: not bottom"


(* (Vpl.Scalar.Rat.t * Vpl.Pol.Cs.t) list *)
(* let get_bottom_cert (p: polyhedre): (cmpT * polynomial) list =
  match Dom.I_Q.get_bottom_cert p with
  | Some(f) ->
    let csl = List.map (fun (co,cp) -> Vpl.WrapperTraductors.CP.ofCstr cp) f in
      List.map (fun (cs) -> ((to_cmpT cs.Vpl.WrapperTraductors.CP.typ),Polynomial.Poly(cs.Vpl.WrapperTraductors.CP.p))) csl
  | None -> failwith "cert: not bottom" *)

(* let rec print_expr (e: IntVpl.VPL_Expr.t): string =
  match e with
  | IntVpl.Term.Add (e1,e2) -> ""
  | IntVpl.Term.Sum v       -> ""
  | IntVpl.Term.Opp v       -> ""
  | IntVpl.Term.Mul (e1,e2) -> ""
  | IntVpl.Term.Prod v      -> ""
  | IntVpl.Term.Annot (_,_) -> ""
  | IntVpl.Term.Var v       -> Ident.Var.toInt v *)

(*let print_varP (v: Vpl.UserInterface.Var.t( Ident.Map_var_to_t.key )): string =
  "x"^(string_of_int (Vpl.UserInterface.Var.toInt v))*)

(* 
let print_condition (c: condition): string =
  match c with
  | Atom(g,s,d) -> 
    (Vpl.Cstr.cmpT_extended_to_string s) ^ (IntVpl.Term.to_string g) *)

(* Type definitions *)
(* ************************************************************************ *)

(* Private aliases *)
type hash = int
type index = int

(* Type for first order types *)
type ttype = Type

type bvar = {
  symbol: string;
  index : int;
}


(* Terms & formulas *)
type term_descr =
  | Var of bvar
  | Cstr of condition

and term = {
  term    : term_descr;
  mutable t_hash : hash; (* lazy hash *)
}

and atom = {
  sign : bool;
  atom : term;
  mutable f_hash  : hash; (* lazy hash *)
}

(* Utilities *)
(* ************************************************************************ *)

let rec list_cmp ord l1 l2 =
  match l1, l2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x1::l1', x2::l2' ->
    let c = ord x1 x2 in
    if c = 0
    then list_cmp ord l1' l2'
    else c


(* Substitutions *)
(* ************************************************************************ *)

module Subst = struct
  module Mi = Map.Make(struct
      type t = int * int
      let compare (a, b) (c, d) = match compare a c with 0 -> compare b d | x -> x
    end)

  type ('a, 'b) t = ('a * 'b) Mi.t

  (* Usual functions *)
  let empty = Mi.empty

  let is_empty = Mi.is_empty

  let iter f = Mi.iter (fun _ (key, value) -> f key value)

  let fold f = Mi.fold (fun _ (key, value) acc -> f key value acc)

  let bindings s = Mi.fold (fun _ (key, value) acc -> (key, value) :: acc) s []

  (* Comparisons *)
  let equal f = Mi.equal (fun (_, value1) (_, value2) -> f value1 value2)
  let compare f = Mi.compare (fun (_, value1) (_, value2) -> f value1 value2)
  let hash h s = Mi.fold (fun i (_, value) acc -> Hashtbl.hash (acc, i, h value)) s 1

  let choose m = snd (Mi.choose m)

  (* Iterators *)
  let exists pred s =
    try
      iter (fun m s -> if pred m s then raise Exit) s;
      false
    with Exit ->
      true

  let for_all pred s =
    try
      iter (fun m s -> if not (pred m s) then raise Exit) s;
      true
    with Exit ->
      false

  let print print_key print_value fmt map =
    let aux _ (key, value) =
      Format.fprintf fmt "%a -> %a@ " print_key key print_value value
    in
    Format.fprintf fmt "@[<hov 0>%a@]" (fun _ -> Mi.iter aux) map

  module type S = sig
    type 'a key
    val get : 'a key -> ('a key, 'b) t -> 'b
    val mem : 'a key -> ('a key, 'b) t -> bool
    val bind : 'a key -> 'b -> ('a key, 'b) t -> ('a key, 'b) t
    val remove : 'a key -> ('a key, 'b) t -> ('a key, 'b) t
  end

end


(* Variables *)
(* ************************************************************************ *)

module Id = struct
  type t = bvar

  (* Hash & comparisons *)
  let hash v = v.index

  let compare =
    fun v1 v2 -> compare v1.index v2.index

  let equal v1 v2 = compare v1 v2 = 0

  (* Printing functions *)
  let print = print_endline

  (* Id count *)
  let _count = ref 0

  (* Constructors *)
  (* let mk_new symbol =
    incr _count;
    let index = !_count in
    { symbol; index; } *)

  let id_table_len: int ref = ref 0
  let id_table: string list ref = ref []
  let mk_new (symbol: string): t =
    let rec inner l i =
      match l with
      | x::ll when 0 = String.compare x symbol -> 1 + !id_table_len - i
      | x::ll -> inner ll (i+1)
      | [] -> id_table := symbol::(!id_table); id_table_len := !id_table_len + 1; i + 1
    in
      { symbol = symbol; index = (inner (!id_table) 0) }

  let new_unknown_var () =
    id_table_len := !id_table_len + 1;
    { symbol = "unknown " ^ (string_of_int !id_table_len); index = !id_table_len }

  let const name fun_vars fun_args fun_ret =
    mk_new name
end

(* Terms *)
(* ************************************************************************ *)

module Term = struct
(* let cstr_hash: int ref = ref 0
let get_cstr_hash (c: condition): int = 
  cstr_hash := !cstr_hash + 1;
  !cstr_hash *)



let cstr_hash: int ref = ref 0
let hstl: condition list ref = ref []
let add_var_hash (v: condition): int =
  hstl := v::!hstl;
  cstr_hash := !cstr_hash + 1;
  !cstr_hash

(**
  TODO: Temporary, should unmap var number to original name
*)
let var_print (v: Var.t): string =
  Var.to_string v

let ts (c: condition): string =
  let s,p = c in
    (Vpl.Cstr.cmpT_extended_to_string s) ^ (Polynomial.to_string (var_print) p)

let get_cstr_hash (v: condition): int =
  let rec inner lst ind =
      match lst with
      | s :: ll -> if String.equal (ts s) (ts v) then
          Some(!cstr_hash - ind)
        else
        (* let _ = print_endline ("tst " ^ (ts s) ^ " " ^ (ts v) ^ " end") in *)
          inner ll (ind+1)
      | [] -> None
  in
  match (inner !hstl 0) with
  | Some(i) -> i
  | none    -> add_var_hash v


  type t = term


  let rec hash_aux t = match t.term with
    | Var v -> Id.hash v
    | Cstr v -> get_cstr_hash v

  let hash t =
    if t.t_hash = -1 then
      t.t_hash <- hash_aux t;
    t.t_hash

  let discr t = match t.term with
    | Var  _ -> 1
    | Cstr _ -> 2

  let rec compare u v =
    let hu = hash u and hv = hash v in
    if hu <> hv then Pervasives.compare hu hv
    else match u.term, v.term with
      | Var v1, Var v2 -> Id.compare v1 v2
      | _, _ -> Pervasives.compare (discr u) (discr v)

  let equal u v =
    u == v || (hash u = hash v && compare u v = 0)

  (* Printing functions *)
  let rec print (fmt: Format.formatter) (t: term) = match t.term with
    | Var v -> Format.fprintf fmt "%s" v.symbol
    | Cstr (s,p) ->
      Format.fprintf fmt "Cstr %s" ((Vpl.Cstr.cmpT_extended_to_string s) ^ (Polynomial.to_string (var_print) p))

  (* Constructors *)
  let mk_term (term: term_descr) =
    { term; t_hash = -1; }

  let make_lt (cst: condition): term =
    { term = Cstr cst; t_hash = -1}
    (* { term = Cstr cst; t_type = {ty = TyCstr; ty_hash = -1}; t_hash = -1} *)

  let negate_cstr (c: condition): condition * (condition option) =
    let s,p = c in
    match s with
    | Vpl.Cstr.LT -> (Vpl.Cstr.GE,p),None
    | Vpl.Cstr.LE -> (Vpl.Cstr.GT,p),None
    | Vpl.Cstr.GT -> (Vpl.Cstr.LE,p),None
    | Vpl.Cstr.GE -> (Vpl.Cstr.LT,p),None
    | Vpl.Cstr.EQ -> (Vpl.Cstr.LT,p),Some(Vpl.Cstr.GT,p)(* Vpl.Cstr.NEQ *)
    | Vpl.Cstr.NEQ -> (Vpl.Cstr.EQ,p),None

  let bvar (symbol: string): t =
    mk_term (Var(Id.mk_new symbol))
end

(* Formulas *)
(* ************************************************************************ *)

module Atom = struct
  type t = atom

  type proof = unit

  let extract_Cstr (a: t) : (condition * bool) option =
    let {atom = a_d; sign = s} = a in
    match a_d with
    | { term = Cstr(c) } -> Some(c,s)
    | _ -> None

  let mk_formula f = {
    sign = true;
    atom = f;
    f_hash = -1;
  }

  let fresh () =
    mk_formula (Term.mk_term (Var(Id.new_unknown_var ())))


let hash f = 
  if f.f_hash = -1 then
    f.f_hash <- Term.hash f.atom;
  f.f_hash

  let compare f g =
    let hf = hash f and hg = hash g in
    if hf <> hg then Pervasives.compare hf hg
    else Term.compare f.atom g.atom

  let equal u v =
    (* let _ = print_endline (if u == v || (hash u = hash v && compare u v = 0) then "e -> true" else "e -> false") in *)
    u == v || (hash u = hash v && compare u v = 0)

  let print fmt a = Format.fprintf fmt "⟦%s%a⟧" (if a.sign then "" else "¬ ") Term.print a.atom

  (* Constructors *)
  let mk_formula f = {
    sign = true;
    atom = f;
    f_hash = -1;
  }

    let dummy = fresh ()
  
  let neg f =
    { f with sign = not f.sign }

  let norm f =
    { f with sign = true },
    if f.sign then Formula_intf.Same_sign
    else Formula_intf.Negated
end

module Formula = Tseitin.Make(Atom)

