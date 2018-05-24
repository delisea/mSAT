
(* Log&Module Init *)
(* ************************************************************************ *)

module Ast = Dolmen.Term
module Id = Dolmen.Id
(* module M = Map.Make(Id) *)
(* module H = Hashtbl.Make(Id) *)
module Expr = Expr_smt

type condition = Expr.condition
(* type polyhedre = Expr.polyhedre *)
(* 
module IntVpl = Vpl.UserInterface.Interface(Vpl.Scalar.Rat)
type condition = IntVpl.Cond.t *)



  let var_hash_size: int ref = ref 0
let var_hash: string list ref = ref []
let add_var_hash (v: string): int =
  var_hash := v::!var_hash;
  var_hash_size := !var_hash_size + 1;
  !var_hash_size
let get_var_hash (v: string): int =
  let rec inner lst ind =
      match lst with
      | s :: ll -> if String.equal s v then Some(!var_hash_size - ind) else inner ll (ind+1)
      | [] -> None
  in
  match (inner !var_hash 0) with
  | Some(i) -> i
  | none    -> add_var_hash v


(* unused *)
exception Typing_error of string * Ast.t


exception SyntaxError
exception NotTypped

type formula = Expr.Formula.t

(** hashage de type? *)
type typped_symbol = {
  symbol: string;
  stype: string;
}

type typped_function = {
  symbol: string;
  stype: string;
  params: string list;
  value: Ast.t;
}

type syntaxique_bind = {
  symbol: string;
  value: Ast.t;
}

type element = Fun of string * string list * string * Ast.t | Var of string * string | Bind of string * Ast.t

(* TODO : Hashmap to speed up *)
type environment = {
  vars : typped_symbol list;
  functions : typped_function list;
  lets : syntaxique_bind list;

(*   term_lets : Expr.term     M.t;
  prop_lets : Expr.Formula.t M.t;

  expect   : expect; *)
}

let add_var (env: environment) (symbol: string) (stype: string) : environment =
  {vars = (({symbol = symbol; stype = stype})::env.vars); functions = env.functions; lets = env.lets} 

let add_fun (env: environment) (symbol: string) (stype: string) (params: string list) (value: Ast.t) : environment =
  {vars = env.vars; functions = (({symbol = symbol; stype = stype; params = params; value = value})::env.functions); lets = env.lets}

let add_bind (env: environment) (symbol: string) (value: Ast.t) : environment =
  {vars = env.vars; functions = env.functions; lets = (({symbol = symbol; value = value})::env.lets)}

let add_vars (env: environment) (symbols: string list) (stypes: string list) : environment =
  if symbols <> [] then
    failwith "add_vars not empty"
  else
    env
  (* {vars = (({symbol = symbol; stype = stype})::env.vars); functions = env.functions}  *)

let type_equal (t1: string) (t2: string) : bool =
  0 = String.compare (String.uppercase_ascii t1) (String.uppercase_ascii t2)

let find_unit_function (env: environment) (symbol: string): typped_function option =
  List.find_opt (fun x -> (x.params=[]) && 0=String.compare symbol x.symbol) env.functions

let syntaxique_bind (env: environment) (symbol: string): syntaxique_bind option =
  List.find_opt (fun b -> 0 = String.compare b.symbol symbol) env.lets

let get_var (env: environment) (symbol: string): typped_symbol option =
  let rec inner (lv: typped_symbol list) =
    match lv with
    | tv::llv when String.compare tv.symbol symbol = 0 -> Some(tv)
    | tv::llv -> inner llv
    | [] -> None
  in inner env.vars


let empty_env: environment = {vars=[];functions=[];lets=[]}

module type Type_checker = sig
  val eval : environment -> Ast.t -> formula
end

let eval tc =
  let module Tc =
    (val tc : Type_checker)
  in
    Tc.eval


let _ltc : (module Type_checker) list ref = ref []

let add_theory (tc: (module Type_checker)) =
  _ltc := tc::(!_ltc)

let set_theory_list (ltc: (module Type_checker) list) =
  _ltc := ltc

let type_check (env: environment) (ast: Ast.t): formula =
let rec inner (ltc : (module Type_checker) list) (env: environment) (ast: Ast.t): formula =
  match ltc with
  | tc::lltc ->
    (try
      eval tc env ast
    with
    | SyntaxError -> inner lltc env ast)
  | [] -> raise SyntaxError
in
  inner (!_ltc) env ast


let curr_env : environment ref = ref empty_env

let assumptions (*  (env: environment) *)(t: Ast.t) =
  let env = empty_env in
  let cnf = Expr.Formula.make_cnf (type_check env t) in
  List.map (function
      | [ x ] -> x
      | _ -> assert false
    ) cnf

let antecedent t =
  let env = !curr_env(* empty_env *) in
  Expr.Formula.make_cnf (type_check env t)

let consequent t =
  failwith "cs"

let def (s: Id.t) (body: Ast.t) =
  let symbol =
    match s with
    | { Id.name = v } -> v
  in
  match body with
  | { Ast.term = Ast.Binder (Ast.Fun, [], {Ast.term = Ast.Colon(value, {Ast.term = Ast.Symbol { Id.name = stype }})}) } ->
    curr_env := add_fun (!curr_env) symbol stype [] value
  | { Ast.term = Ast.Binder (Ast.Fun, _, {Ast.term = Ast.Colon({Ast.term = value}, {Ast.term = Ast.Symbol { Id.name = stype }})}) } ->
    failwith "Def: Function declaration."
  | _ -> failwith "Def: Not declaration."

let decl (s: Id.t) (ty: Ast.t) =
  let symbol =
    match s with
    | { Id.name = v } -> v
  in
  match ty with
  | { Ast.term = Ast.Binder (Ast.Arrow, [], {Ast.term = Ast.Symbol { Id.name = ty }}) } ->
    curr_env := add_var (!curr_env) symbol ty
  | { Ast.term = Ast.Binder (Ast.Arrow, _, _) } ->
    failwith "Decl: Function declaration."
  | _ -> failwith "Decl: Not declaration."

let do_match_let (ast: Ast.t): bool =
  match ast with
  | { Ast.term = Ast.Binder (Ast.Let, _, _) } -> true
  | _ -> false

let match_let (env: environment) (ast: Ast.t): environment * Ast.t =
  match ast with
  | { Ast.term = Ast.Binder (Ast.Let, vars, f) } ->
      let rec inner (env: environment) (binds: Ast.t list): environment =
        match binds with
        | {Ast.term = Ast.Colon({Ast.term = Ast.Symbol { Id.name = symbol }}, value)}::ll ->
          inner (add_bind env symbol value) ll
        | [] -> env
      in
        ((inner env vars),f)
  | _ -> failwith "match_let bad use"





(* Eval var as typped var or binding *)
let eval_var (env: environment) (sym: string): element =
  match syntaxique_bind env sym with
  | Some(b) -> Bind(b.symbol, b.value)
  | None    -> 
    match find_unit_function env sym with
    | Some(f) -> Fun(f.symbol, f.params, f.stype, f.value)
    | None    -> match get_var env sym with | Some(v) -> Var(v.symbol, v.stype) | None -> raise SyntaxError




  (** file handleman_theory *)

module Smt_Type_checker : Type_checker = struct

  let is_scmp op =
  match op with
  | Ast.Lt | Ast.Leq | Ast.Gt | Ast.Geq -> true
  | _ -> false

  let is_eq op =
  match op with
  | Ast.Eq | Ast.Distinct -> true
  | _ -> false

let is_pol_op op =
  match op with
  | Ast.Add | Ast.Mult | Ast.Sub | Ast.Div -> true
  | _ -> false

  let eval_operator (ast: Ast.builtin): Expr.cmpT =
  match ast with
  | Ast.Lt -> Vpl.Cstr.LT
  | Ast.Leq -> Vpl.Cstr.LE
  | Ast.Gt -> Vpl.Cstr.GT
  | Ast.Geq -> Vpl.Cstr.GE
  | Ast.Eq -> Vpl.Cstr.EQ
  | Ast.Distinct -> Vpl.Cstr.NEQ
  |_ -> raise SyntaxError

  let rec eval_polynomial (env: environment) (ast: Ast.t): Expr.polynomial =
  match ast with
  | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin Ast.Mult }, l) } -> 
      Expr.Polynomial.Prod (List.map (fun a -> eval_polynomial env a) l)

  | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin Ast.Add }, l) } -> 
    Expr.Polynomial.Sum (List.map (fun a -> eval_polynomial env a) l)

  | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin Ast.Sub }, [g; d]) } -> 
    Expr.Polynomial.Add ((eval_polynomial env g),Expr.Polynomial.Opp(eval_polynomial env d))

(*   | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin Ast.Var }, ({ Ast.term = Ast.Symbol { Id.name = v }}::[])) } ->
    Expr.Polynomial.Var (Expr.Var.fromInt (get_var_hash v)) *)

  | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin Coef }, ({ Ast.term = Ast.Symbol { Id.name = c }}::[])) } ->
    Expr.Polynomial.Cte (Expr.to_coeff (float_of_string c))

  | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin Ast.Div }, [g; d]) } ->
    let g,d = (eval_polynomial env g),(eval_polynomial env d) in
      Expr.Polynomial.Poly(Expr.Polynomial.to_poly (Expr.Polynomial.Div(g,d)))
    (* (match g,d with
    | Expr.Polynomial.Cte(g),Expr.Polynomial.Cte(d) ->
      let c  = Vpl.Scalar.Rat.div g d in
      Expr.Polynomial.Cte(c)
    | _ -> failwith "Div implem not completed") *)

  | { Ast.term = Ast.App ({ Ast.term = Ast.Symbol { Id.name = v } }, []) } ->
    (* let _ = failwith "do var + fun check + let bind" in *)
    (match eval_var env v with
    | Fun(symbol, params, stype, value) when type_equal stype "Real" ->
      let env = add_vars env params [] in
        eval_polynomial env value
    | Var(symbol, stype) when type_equal stype "Real" ->
        Expr.Polynomial.Var (Expr.Var.fromInt (get_var_hash symbol))
    | Bind(symbol, value) -> eval_polynomial env value
    | _ -> raise SyntaxError)

  | ast when do_match_let ast ->
    let env, f = match_let env ast in
      eval_polynomial env f

  | _ -> raise SyntaxError

  let eval (env: environment) (ast: Ast.t): formula =
    match ast with
    | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin (op) }, [g; d]) } when is_scmp op ->
      let p_g = eval_polynomial env g
      and p_d = eval_polynomial env d
      and p_op = eval_operator op in
      Expr.Formula.make_atom (Expr.Atom.mk_formula (Expr.Term.make_lt (Expr.to_cond p_op p_g p_d)))
    | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin (op) }, [g; d]) } when is_eq op ->
      let p_g = eval_polynomial env g
      and p_d = eval_polynomial env d in
      let c1 = (Expr.Term.make_lt (Expr.to_cond Vpl.Cstr.LT p_g p_d))
      and c2 = (Expr.Term.make_lt (Expr.to_cond Vpl.Cstr.GT p_g p_d)) in
      let t1,t2 = (Expr.Formula.make_atom (Expr.Atom.mk_formula c1)),(Expr.Formula.make_atom (Expr.Atom.mk_formula c2)) in
        if op = Ast.Eq then 
          Expr.Formula.make_and [(Expr.Formula.make_not t1); (Expr.Formula.make_not t2)]
        else
          Expr.Formula.make_or [t1; t2]
    | _ -> raise SyntaxError
end
let smt_Type_checker = (module Smt_Type_checker : Type_checker)


  (** file sat_theory *)
module Sat_Type_checker : Type_checker = struct
  
  let diagonal l =
    let rec single x acc = function
      | [] -> acc
      | y :: r -> single x ((x, y) :: acc) r
    and aux acc = function
      | [] -> acc
      | x :: r -> aux (single x acc r) r
    in
    aux [] l

  let make_eq a b =
    Expr.Formula.make_or [Expr.Formula.make_and [a;b]; Expr.Formula.make_and [Expr.Formula.make_not a; Expr.Formula.make_not  b]]

  let eval (env: environment) (ast: Ast.t): formula =
    match ast with
    | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin Ast.True }, []) }
    | { Ast.term = Ast.Builtin Ast.True } ->
     Expr.Formula.f_true

    | { Ast.term = Ast.App ({ Ast.term = Ast.Builtin Ast.False }, []) }
    | { Ast.term = Ast.Builtin Ast.False } ->
      Expr.Formula.f_false

    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.And}, l) }
    | { Ast.term = Ast.App ({Ast.term = Ast.Symbol { Id.name = "and" }}, l) } ->
      (Expr.Formula.make_and (List.map (type_check env) l))

    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Or}, l) }
    | { Ast.term = Ast.App ({Ast.term = Ast.Symbol { Id.name = "or" }}, l) } ->
      (Expr.Formula.make_or (List.map (type_check env) l))

    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Xor}, l) } ->
      begin match l with
        | [p; q] ->
          let f = type_check env p in
          let g = type_check env q in
          (Expr.Formula.make_not (Expr.Formula.make_equiv f g))
        | _ -> raise SyntaxError
      end

    | ({ Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Imply}, l) })
    | ({ Ast.term = Ast.App ({Ast.term = Ast.Symbol { Id.name = "=>" }}, l) }) ->
      begin match l with
        | [p; q] ->
          let f = type_check env p in
          let g = type_check env q in
          (Expr.Formula.make_imply f g)
        | _ -> raise SyntaxError
      end
    | ({ Ast.term = Ast.App ({Ast.term = Ast.Symbol { Id.name = "xor" }}, l) }) ->
      begin match l with
        | [p; q] ->
          let f = type_check env p in
          let g = type_check env q in
          (Expr.Formula.make_xor f g)
        | _ -> raise SyntaxError
      end

    | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Equiv}, l) } ->
      begin match l with
        | [p; q] ->
          let f = type_check env p in
          let g = type_check env q in
          (Expr.Formula.make_equiv f g)
        | _ -> raise SyntaxError
      end

    | ({ Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Not}, l) })
    | ({ Ast.term = Ast.App ({Ast.term = Ast.Symbol { Id.name = "not" }}, l) }) ->
      begin match l with
        | [p] ->
          (Expr.Formula.make_not (type_check env p))
        | _ -> raise SyntaxError
      end

    (* (Dis)Equality *)
    | ({ Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Eq}, l) })
    | ({ Ast.term = Ast.App ({Ast.term = Ast.Symbol { Id.name = "=" }}, l) }) ->
      let l' = List.map (type_check env) l in
      let l'' = diagonal l' in
        Expr.Formula.make_and
          (List.map (fun (a, b) ->
                 (make_eq a b)) l'')
      

    | ({ Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Distinct}, l) }) ->
      (* let l' = List.map (type_check env) l in
      let l'' = diagonal l' in  *)failwith "wtf diagonal???"
      (*
        Expr.Formula.make_and
          (List.map (fun (a, b) ->
               Expr.Formula.make_not
                 (make_eq t a b)) l'')
      *)

    (* General case: application *)
    | { Ast.term = Ast.Symbol { Id.name = v } }
    | { Ast.term = Ast.App ({ Ast.term = Ast.Symbol { Id.name = v } }, []) } ->
      (* let _ = failwith "do var + fun check + let bind" in *)
      (match eval_var env v with
      | Fun(symbol, params, stype, value) when type_equal stype "Bool" ->
        let env = add_vars env params [] in
          type_check env value
      | Var(symbol, stype) when type_equal stype "Bool" ->
          Expr.Formula.make_atom (Expr.Atom.mk_formula (Expr.Term.bvar symbol))
      | Bind(symbol, value) -> type_check env value
      | _ -> raise SyntaxError)

    | { Ast.term = Ast.App ({ Ast.term = Ast.Symbol s }, l) } ->
      failwith "do define-fun + type"(* parse_app env ast s l *)

    (* Local bindings *)
    | ast when do_match_let ast ->
      let env, f = match_let env ast in
        type_check env f
    (* | { Ast.term = Ast.Binder (Ast.Let, vars, f) } ->
      let rec inner (env: environment) (binds: Ast.t list): environment =
        match binds with
        | {Ast.term = Ast.Colon({Ast.term = Ast.Symbol { Id.name = symbol }}, value)}::ll ->
          inner (add_bind env symbol value) ll
        | [] -> env
      in
        type_check (inner env vars) f  *)

    (* Other cases *)
    | ast -> raise SyntaxError
end
let sat_Type_checker = (module Sat_Type_checker : Type_checker)



(** file main *)
let _ = add_theory (module Smt_Type_checker : Type_checker)
let _ = set_theory_list [sat_Type_checker; smt_Type_checker]