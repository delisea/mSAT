(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

exception Incorrect_model
exception Out_of_time
exception Out_of_space

let file = ref ""
let p_cnf = ref false
let p_check = ref false
let p_dot_proof = ref ""
let p_proof_print = ref false
let time_limit = ref 300.
let itime_limit = ref 300
let size_limit = ref 1000_000_000.

let _ = Vpl.Flags.handelman_loop := true
let _ = Vpl.Flags.handelman_timeout := None

module P =
  Dolmen.Logic.Make(Dolmen.ParseLocation)
    (Dolmen.Id)(Dolmen.Term)(Dolmen.Statement)

module type S = sig
  val do_task : Dolmen.Statement.t -> unit
end

module Make
    (S : External.S)
    (T : Type.S with type atom := S.atom)
  : sig
    val do_task : Dolmen.Statement.t -> unit
  end = struct

  module D = Dot.Make(S.Proof)(Dot.Default(S.Proof))

  let hyps = ref []

  let check_model state =
    let check_clause c =
      let l = List.map (function a ->
          Log.debugf 99 "Checking value of %a"
            (fun k -> k S.St.pp_atom (S.St.add_atom a));
          state.Solver_intf.eval a) c in
      List.exists (fun x -> x) l
    in
    let l = List.map check_clause !hyps in
    List.for_all (fun x -> x) l

  let prove ~assumptions =
    let res = S.solve () in
    let t = Sys.time () in
    begin match res with
      | S.Sat state ->
        if !p_check then
          if not (check_model state) then
            raise Incorrect_model;
        let t' = Sys.time () -. t in
        Format.printf "Sat (%f/%f)@." t t'
      | S.Unsat state ->
        if !p_check then begin
          let p = state.Solver_intf.get_proof () in
          S.Proof.check p;
          if !p_dot_proof <> "" then begin
            let fmt = Format.formatter_of_out_channel (open_out !p_dot_proof) in
            D.print fmt p
          end
        end;
        let t' = Sys.time () -. t in
        Format.printf "Unsat (%f/%f)@." t t'
    end

  let do_task s =
    match s.Dolmen.Statement.descr with
    | Dolmen.Statement.Def (id, t) -> T.def id t
    | Dolmen.Statement.Decl (id, t) -> T.decl id t
    | Dolmen.Statement.Clause l ->
      let cnf = T.antecedent (Dolmen.Term.or_ l) in
      hyps := cnf @ !hyps;
      S.assume cnf
    | Dolmen.Statement.Consequent t ->
      let cnf = T.consequent t in
      hyps := cnf @ !hyps;
      S.assume cnf
    | Dolmen.Statement.Antecedent t ->
      (* let cnf = T.antecedent t in *)
      (* hyps := cnf @ !hyps; *)
      let cnf = ref (T.antecedent t) in
      let _ =
      while !cnf != [] do
        match !cnf with
        | c::cl -> hyps := c::!hyps; cnf := cl
      done in

      S.assume !cnf
    | Dolmen.Statement.Pack [
        { Dolmen.Statement.descr = Dolmen.Statement.Push 1; };
        { Dolmen.Statement.descr = Dolmen.Statement.Antecedent f; };
        { Dolmen.Statement.descr = Dolmen.Statement.Prove; };
        { Dolmen.Statement.descr = Dolmen.Statement.Pop 1; };
      ] ->
      let assumptions = T.assumptions f in
      prove ~assumptions
    | Dolmen.Statement.Prove ->
      prove ~assumptions:[]
    | Dolmen.Statement.Set_info _
    | Dolmen.Statement.Set_logic _ -> ()
    | Dolmen.Statement.Exit -> exit 0
    | _ ->
      Format.printf "Command not supported:@\n%a@."
        Dolmen.Statement.print s
end

module NotDummyTheory = struct
  module FI = Expr_smt
  module F = FI.Atom
  module T_I = Theory_intf
  (* We don't have anything to do since the SAT Solver already
   * does propagation and conflict detection *)

  type formula = F.t
  (* type proof = F.proof *)
  type proof = unit
  type level = FI.polyhedre
  type slice = (formula, proof) T_I.slice

  let dummy = FI.empty

  let _current_level: level ref = ref dummy

  let tempo: int ref = ref 0

  let current_level () = !_current_level
  let assume (sl: slice): (formula, proof) Theory_intf.res =
    let rec inner s e =
      if s = e then
        ()
      else
        let _ = F.print Format.str_formatter (sl.T_I.get s) in
        let _ = Log.debug 99 ("next:" ^ (Format.flush_str_formatter ())) in
          inner (s+1) e
    in
    let rec next_Cstr (s: int) (e: int): (FI.condition * int * bool) option =
      if s = e then
        None
      else
        match F.extract_Cstr (sl.T_I.get s) with
        | Some(c,non_neg) -> Some(c,(s+1),non_neg)
        | None -> next_Cstr (s+1) e
    in
    let _ = Log.debug 99 "start assuming" in
    let _ = inner sl.T_I.start (sl.T_I.start + sl.T_I.length) in
    let _ = Log.debug 99 "stop assuming" in
    let rec iinner (s: int) (e: int) (p: FI.polyhedre) (fl: formula list) =
      match next_Cstr s e with
      | Some(c, s, non_neg) ->
        let p = if non_neg then FI.assume [c] p else match FI.Term.negate_cstr c with |c,None -> FI.assume [c] p |c1,Some(c2) -> FI.assume [c1;c2] p in
        if FI.is_bottom p then
          (* Theory_intf.Unsat ((List.map F.neg ((sl.T_I.get (s-1))::fl)),()) *)
          let cert = FI.get_bottom_cert p in
          Theory_intf.Unsat ((List.map F.neg ((sl.T_I.get (s-1))::fl)),())
        else
          iinner s e p ((sl.T_I.get (s-1))::fl)
      | None -> let _ = _current_level := p in Theory_intf.Sat
    in
    let res = iinner sl.T_I.start (sl.T_I.start + sl.T_I.length) !_current_level [] in
    let _ = if res = Theory_intf.Sat then Log.debug 99 "Result: Sat"
    else Log.debug 99 "Result: Unsat" in
      res


  let backtrack (l: level) =
    _current_level := l


  let if_sat (sl: slice): (formula, proof) Theory_intf.res =
    let rec inner s e =
      if s = e then
        ()
      else
        let _ = F.print Format.str_formatter (sl.T_I.get s) in
        let _ = Log.debug 99 ("next:" ^ (Format.flush_str_formatter ())) in
          inner (s+1) e
    in
    let rec next_Cstr (s: int) (e: int): (FI.condition * int * bool) option =
      if s = e then
        None
      else
        match F.extract_Cstr (sl.T_I.get s) with
        | Some(c,non_neg) -> Some(c,(s+1),non_neg)
        | None -> next_Cstr (s+1) e
    in
    let _ = Log.debug 99 "start if_sat" in
    let _ = inner sl.T_I.start (sl.T_I.start + sl.T_I.length) in
    let _ = Log.debug 99 "stop if_sat" in
    let rec iinner (s: int) (e: int) (p: FI.polyhedre) (fl: formula list) =
      match next_Cstr s e with
      | Some(c, s, non_neg) ->
        let p = if non_neg then FI.assume [c] p else match FI.Term.negate_cstr c with |c,None -> FI.assume [c] p |c1,Some(c2) -> FI.assume [c1;c2] p in
        if FI.is_bottom p then
          Theory_intf.Unsat ((List.map F.neg ((sl.T_I.get (s-1))::fl)),())
        else
          iinner s e p ((sl.T_I.get (s-1))::fl)
      | None -> let _ = _current_level := p in Theory_intf.Sat
    in
    let res = iinner sl.T_I.start (sl.T_I.start + sl.T_I.length) !_current_level [] in
    let _ = if res = Theory_intf.Sat then Log.debug 99 "Result: Sat"
    else Log.debug 99 "Result: Unsat" in
    (* let _ = tempo := !tempo + 1 in
    let _ = if !tempo > 1 then failwith "stop" in *)
      res
end

module Th = NotDummyTheory

module SMake(Dummy:sig end) =
  Solver.Make(Expr_smt.Atom)(Th)(struct end)

module Smt = Make(SMake(struct end))(Type_smt)

(* module Smt = Make(Smt.Make(struct end))(Type_smt) *)

let error_msg opt arg l =
  Format.fprintf Format.str_formatter "'%s' is not a valid argument for '%s', valid arguments are : %a"
    arg opt (fun fmt -> List.iter (fun (s, _) -> Format.fprintf fmt "%s, " s)) l;
  Format.flush_str_formatter ()

(* Arguments parsing *)
let int_arg r arg =
  let l = String.length arg in
  let multiplier m =
    let arg1 = String.sub arg 0 (l-1) in
    r := m *. (float_of_string arg1)
  in
  if l = 0 then raise (Arg.Bad "bad numeric argument")
  else
    try
      match arg.[l-1] with
      | 'k' -> multiplier 1e3
      | 'M' -> multiplier 1e6
      | 'G' -> multiplier 1e9
      | 'T' -> multiplier 1e12
      | 's' -> multiplier 1.
      | 'm' -> multiplier 60.
      | 'h' -> multiplier 3600.
      | 'd' -> multiplier 86400.
      | '0'..'9' -> r := float_of_string arg
      | _ -> raise (Arg.Bad "bad numeric argument")
    with Failure _ -> raise (Arg.Bad "bad numeric argument")

let setup_gc_stat () =
  at_exit (fun () ->
      Gc.print_stat stdout;
    )

let input_file = fun s -> file := s

let usage = "Usage : main [options] <file>"
let argspec = Arg.align [
    "-bt", Arg.Unit (fun () -> Printexc.record_backtrace true),
    " Enable stack traces";
    "-cnf", Arg.Set p_cnf,
    " Prints the cnf used.";
    "-check", Arg.Set p_check,
    " Build, check and print the proof (if output is set), if unsat";
    "-dot", Arg.Set_string p_dot_proof,
    " If provided, print the dot proof in the given file";
    "-gc", Arg.Unit setup_gc_stat,
    " Outputs statistics about the GC";
    "-size", Arg.String (int_arg size_limit),
    "<s>[kMGT] Sets the size limit for the sat solver";
    "-time", Arg.String (fun x -> itime_limit := (int_of_string x); int_arg time_limit x),
    "<t>[smhd] Sets the time limit for the sat solver";
    "-v", Arg.Int (fun i -> Log.set_debug i),
    "<lvl> Sets the debug verbose level";
  ]

(* Limits alarm *)
let check () =
  let t = Sys.time () in
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  let s = float heap_size *. float Sys.word_size /. 8. in
  if t > !time_limit then
    raise Out_of_time
  else if s > !size_limit then
    raise Out_of_space

let beep _ = 
    print_endline "end";
    Format.printf "Timeout@.";
    exit 2(* ; flush stdout; ignore (alarm 30) *)

let main () =
  (* Administrative duties *)
  Arg.parse argspec input_file usage;
  if !file = "" then begin
    Arg.usage argspec usage;
    exit 2
  end;
  let _ = Sys.signal Sys.sigalrm (Sys.Signal_handle beep) in
  let _ = ignore (Unix.alarm !itime_limit) in
  let al = Gc.create_alarm check in

  (* Interesting stuff happening *)
  let lang, input = P.parse_file !file in
  let _ = (
    match lang with
    | P.Smtlib -> print_endline "Smtlib"
    | P.Dimacs ->  print_endline "Dimacs"
    | P.ICNF ->  print_endline "ICNF"
    | P.Tptp ->  print_endline "Tptp"
    | P.Zf ->  print_endline "Zf"
  ) in
  List.iter Smt.do_task input;
  Gc.delete_alarm al;
  ()

let () = 
let _ = Random.self_init () in
let _ = Log.set_debug 5 in
  try
    main ()
  with
  | Out_of_time ->
    Format.printf "Timeout@.";
    exit 2
  | Out_of_space ->
    Format.printf "Spaceout@.";
    exit 3
  | Incorrect_model ->
    Format.printf "Internal error : incorrect *sat* model@.";
    exit 4
  | Type_sat.Typing_error (msg, t)
  | Type_smt.Typing_error (msg, t) ->
    let b = Printexc.get_backtrace () in
    let loc = match t.Dolmen.Term.loc with
      | Some l -> l | None -> Dolmen.ParseLocation.mk "<>" 0 0 0 0
    in
    Format.fprintf Format.std_formatter "While typing:@\n%a@\n%a: typing error\n%s@."
      Dolmen.Term.print t Dolmen.ParseLocation.fmt loc msg;
    if Printexc.backtrace_status () then
      Format.fprintf Format.std_formatter "%s@." b
