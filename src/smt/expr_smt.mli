
(** Expressions for TabSat *)

(** {2 Type definitions} *)

(** These are custom types used in functions later. *)

(** {3 Identifiers} *)

(** Identifiers are the basic building blocks used to build types terms and expressions. *)
(* module Dom = Vpl.WDomain *)
module Dom = Vpl.NCDomain.NCVPL_Unit
module Polynomial = Dom.I_Q.Term
module Var = Vpl.Var.Positive


type condition
type polyhedre

type cmpT = Vpl.Cstr.cmpT_extended
type polynomial = Dom.I_Q.Term.t
type coeff = Vpl.Scalar.Rat.t
(* type coeff = Polynomial.Coeff.t *)

val empty: polyhedre
val is_bottom: polyhedre -> bool
val assume: condition list -> polyhedre -> polyhedre
val to_cond: cmpT -> polynomial -> polynomial -> condition
val to_coeff: float -> coeff

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

module Term : sig
  type t = term
  (** Type alias *)

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  (**  Usual hash/compare functions *)

  val print : Format.formatter -> t -> unit
  (** Printing functions *)

  val make_lt: condition -> term

  val negate_cstr: condition -> condition * (condition option)

  val bvar: string -> term

end

(** {2 Formulas} *)

module Atom : sig
  type t = atom
  type proof = unit
  (** Type alias *)

  val extract_Cstr : atom -> (condition * bool) option

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  (** Usual hash/compare functions *)

  val print : Format.formatter -> t -> unit
  (** Printing functions *)

  val fresh : unit -> atom
  (** Create a fresh propositional atom. *)

  val neg : atom -> atom
  (** Returns the negation of the given atom *)

  val norm : atom -> atom * Formula_intf.negated
  (** Normalization functions as required by msat. *)

  val dummy : t

  val mk_formula : term -> atom
end

module Formula : Tseitin.S with type atom = atom

