(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
Copyright 2016 Simon Cruanes
*)

include Formula_intf.S

val make : int -> t
(** Make a proposition from an integer. *)

val fresh : unit -> t
(** Make a fresh atom *)
