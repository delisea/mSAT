(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
*)

module Expr = Expr_sat
module Type = Type_sat

include Minismt.Solver.Make(Expr)(Minismt.Solver.DummyTheory(Expr))
