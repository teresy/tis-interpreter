(* Modified by TrustInSoft *)

(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2015                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)

open Cil_types
open Eval

let dkey = Value_parameters.register_category "callbacks"


module Make
    (Value: Abstract_value.S)
    (Loc: Abstract_location.S with type value = Value.t)
    (Domain : Abstract_domain.External with type location = Loc.location
                                        and type value = Value.t)
    (Eva: Evaluation.S with type value = Domain.value
                        and type origin = Domain.origin
                        and type loc = Domain.location
                        and type state = Domain.t)
    (Init: Initialization.S with type state := Domain.t)
= struct

  module States = Partitioning.Make_Set (Domain)
  module Domain_Transfer = Domain.Transfer (Eva.Valuation)
  module Transfer = Transfer_stmt.Make (Domain_Transfer) (Eva)
  module Logic = Transfer_logic.Make (Domain) (Partitioning.Make_Set (Domain))

  module Computer =
    Partitioned_dataflow.Computer (Domain) (States) (Transfer) (Logic)

  let get_cvalue =
    match Domain.get Cvalue_domain.key with
    | None -> fun _ -> Cvalue.Model.top
    | Some get -> fun state -> get state

  (* Compute a call to [kf] in the state [state]. The evaluation will
     be done either using the body of [kf] or its specification, depending
     on whether the body exists and on option [-val-use-spec]. [call_kinstr]
     is the instruction at which the call takes place, and is used to update
     the statuses of the preconditions of [kf]. If [show_progress] is true,
     the callstack and additional information are printed. *)
  let compute_using_spec_or_body _call_kinstr _kf _state =
    assert false

  (* Mem Exec *)

  module MemExec = Mem_exec2.Make (Value) (Domain)

  let extract_value = function
    | Assign value -> `Value value
    | Copy (_lval, copy) ->
      match copy with
      | Determinate v -> `Value v.v
      | Exact v -> v.v

  let compute_call call_kinstr call init_state =
    let default () =
      compute_using_spec_or_body call_kinstr call.kf init_state
    in
    if Value_parameters.MemExecAll.get () then
      let args =
        List.map (fun {avalue} -> extract_value avalue) call.arguments
      in
      match MemExec.reuse_previous_call call.kf init_state args with
      | None ->
        let res, cacheable = default () in
        if not (!Db.Value.use_spec_instead_of_definition call.kf)
        && cacheable = Value_types.Cacheable
        then
          MemExec.store_computed_call call.kf init_state args res;
        res, cacheable
      | Some (res, i) ->
        Db.Value.Call_Type_Value_Callbacks.apply
          (`Memexec, get_cvalue init_state, Value_util.call_stack ());
        (* Evaluate the preconditions of kf, to update the statuses
           at this call. *)
        let spec = Annotations.funspec call.kf in
        if Eval_annots.has_requires spec then begin
          let ab = Logic.create init_state call.kf in
          ignore (Logic.check_fct_preconditions
                    call.kf ab call_kinstr init_state);
        end;
        if Value_parameters.ValShowProgress.get () then begin
          Value_parameters.feedback ~current:true
            "Reusing old results for call to %a" Kernel_function.pretty call.kf;
          Value_parameters.debug ~dkey
            "calling Record_Value_New callbacks on saved previous result";
        end;
        let stack_with_call = Value_util.call_stack () in
        Db.Value.Record_Value_Callbacks_New.apply
          (stack_with_call, Value_types.Reuse i);
        (* call can be cached since it was cached once *)
        res, Value_types.Cacheable
    else
      default ()

  let () = Transfer.compute_call_ref := compute_call


  (* Compute a call to the main function. The initial state is generated
     according to options such as [-lib-entry] and the options of Value governing
     the shape of this state. *)
  let compute_from_entry_point kf =
    Init.initial_state_with_formals kf >>-: fun init_state ->
    Value_util.push_call_stack kf Kglobal;
    (* TODO: apply for the whole domain. *)
    let cvalue_state = get_cvalue init_state in
    Db.Value.merge_initial_state (Value_util.call_stack ()) cvalue_state;
    Db.Value.Call_Value_Callbacks.apply (cvalue_state, [kf, Kglobal]);
    ignore (compute_using_spec_or_body Kglobal kf init_state)

end



let floats_ok () =
  let u = min_float /. 2. in
  let u = u /. 2. in
  0. < u && u < min_float

let need_assigns kf =
  let spec = Annotations.funspec ~populate:false kf in
  match Cil.find_default_behavior spec with
  | None -> true
  | Some bhv -> bhv.b_assigns = WritesAny

let options_ok () =
  (* Check that we can parse the values specified for the options that require
     advanced parsing. Just make a query, as this will force the kernel to
     parse them. *)
  let check f = try ignore (f ()) with Not_found -> () in
  check Value_parameters.SplitReturnFunction.get;
  check Value_parameters.BuiltinsOverrides.get;
  check Value_parameters.SlevelFunction.get;
  let check_assigns kf =
    if need_assigns kf then
      Value_parameters.error "@[no assigns@ specified@ for function '%a',@ for \
                              which@ a builtin@ or the specification@ will be used.@ \
                              Potential unsoundness.@]" Kernel_function.pretty kf
  in
  Value_parameters.BuiltinsOverrides.iter (fun (kf, _) -> check_assigns kf);
  Value_parameters.UsePrototype.iter (fun kf -> check_assigns kf);
;;

(* Preliminary checks before Value starts *)
let check () =
  assert (floats_ok ());
  options_ok ();
  Split_return.pretty_strategies ();
;;



(* Register a signal handler for SIGUSR1, that will be used to abort Value *)
let () =
  let prev = ref (fun _ -> ()) in
  let handler (_signal: int) =
    !prev Sys.sigusr1; (* Call previous signal handler *)
    Value_parameters.warning "Stopping analysis at user request@.";
    Partitioned_dataflow.signal_abort ()
  in
  try
    match Sys.signal Sys.sigusr1 (Sys.Signal_handle handler) with
    | Sys.Signal_default | Sys.Signal_ignore -> ()
    | Sys.Signal_handle f -> prev := f
  with Invalid_argument _ -> () (* Ignore: SIGURSR1 is not available on Windows,
                                   and possibly on other platforms. *)


(* Hard-wired instanciation of the analysis for the main abstract domain. *)

module Val = struct
  include Main_values.CVal
  include Structure.Open (Structure.Key_Value) (Main_values.CVal)
  let reduce t = t
end

module Loc = Main_locations.PLoc

module Domain = struct
  include Cvalue_domain.State
  include Structure.Open (Structure.Key_Domain) (Cvalue_domain.State)
end

module Eva = Evaluation.Make (Val) (Loc) (Domain)
module NonLinear = Non_linear_evaluation.Make (Val) (Eva)
module Eval = struct
  include Eva
  let evaluate = NonLinear.evaluate
end

module Init = Initialization.Make (Val) (Loc) (Domain) (Eval)
let set_main_init () =
  Db.Value.initial_state_only_globals :=
    (fun () -> Cvalue_domain.extract Domain.get (Init.initial_state ()))
let () = set_main_init ()

module MainComputer = Make (Val) (Loc) (Domain) (Eval) (Init)


(* On the fly instantiation of others abstract domains. *)
let analyzer config =
  let abstract = Abstractions.make config in
  let module Abstract = (val abstract : Abstractions.S) in
  let module Eva = Evaluation.Make (Abstract.Val) (Abstract.Loc) (Abstract.Dom) in
  let module NonLinear = Non_linear_evaluation.Make (Abstract.Val) (Eva) in
  let module Eval = struct
    include Eva
    let evaluate = NonLinear.evaluate
  end
  in
  let module Init =
    Initialization.Make (Abstract.Val) (Abstract.Loc) (Abstract.Dom) (Eval)
  in
  let () =
    Db.Value.initial_state_only_globals :=
      (fun () -> Cvalue_domain.extract Abstract.Dom.get (Init.initial_state ()))
  in
  let module Computer =
    Make (Abstract.Val) (Abstract.Loc) (Abstract.Dom) (Eval) (Init)
  in
  Computer.compute_from_entry_point

(* Analysis. *)

let main_compute _compute_from_entry_point =
  assert false


let ref_analyzer =
  ref (Abstractions.default_config, MainComputer.compute_from_entry_point)

let force_compute () =
  Ast.compute ();
  check ();
  let config = Abstractions.configure () in
  let analyzer =
    if config = fst !ref_analyzer then snd !ref_analyzer
    else if config = Abstractions.default_config
    then (set_main_init (); MainComputer.compute_from_entry_point)
    else
      let a = analyzer config in
      ref_analyzer := config, a;
      a
  in
  main_compute analyzer


(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
