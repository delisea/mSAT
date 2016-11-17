(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon, Evelyne Contejean                    *)
(*                  Francois Bobot, Mohamed Iguernelala, Alain Mebsout    *)
(*                  CNRS, Universite Paris-Sud 11                         *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

open Msat

val cc_active : bool ref

type answer = Yes of Explanation.t | No

module type S = sig
  type t

  val empty : unit -> t

  val assume :
    cs:bool ->
    Literal.LT.t ->
    Explanation.t ->
    t -> t * Term.Set.t * int

  val query : Literal.LT.t -> t -> answer

  val class_of : t -> Term.t -> Term.t list
end

module Make (Dummy : sig end) : S
