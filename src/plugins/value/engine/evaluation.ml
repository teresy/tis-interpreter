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

(* Evaluation of expressions to values. *)

open Cil_types
open Eval


(* The forward evaluation of an expression [e] gives a value to each subterms
   of [e], from its variables to the root expression [e]. It also computes the
   set of alarms which may occur in the evaluaton of each subterm.
   All these intermediate results of an evaluation are stored in a cache, whose
   type is described in eval.mli. The cache is the complete result of the
   evaluation. *)

(* The forward evaluation of an expression relies on queries of the abstract
   domain, which must be able to assign a value to some expression (see
   abstract_domain.mli for more details).
   An oracle for the value of expressions is also given to the domain,
   which may use it to build its answer. This oracle is the main forward
   evaluation function itself, so the domain may initiate the evaluation
   of some new expressions.
   To avoid loops in the use of the oracle:
   - before any computation or an expression [e], Value.top is stored
     in the cache; this dummy value will be erased at the end of the
     computation, but in the meantime, any evaluation of [e] (by the oracle)
     returns top immediately.
   - fuel is used to limit the depth of the use of the oracle. The fuel level is
     decremented at each use of the oracle up to zero, where the oracle returns
     top.
     The fuel level with which an expression has been evaluated is stored in the
     cache. The recomputation of an expression may be performed with a higher
     fuel than before, if needed. *)

(* Reductions may happen in the forward evaluation when:
   - a domain returns a value more precise than the one internally computed;
   - alarms are emitted by an operation on values. In particular, locations
     are reduced to their valid part for a read or write operation.
   These reductions are propagated to the sub-expressions by a backward
   evaluation, after the forward evaluation has finished.
   The backward evaluation also propagates the reduction stemming from an if
   statement, where the condition may be reduced to zero or non-zero. *)

(* When a backward reduction has been successfully performed, the domain may
   initiate new reductions, via the reduce_further function.
   A fuel level is used in the same way as for the forward evaluation to
   avoid reduction loops. *)


(* The fuel level with which an expression has been evaluated. *)
type fuel =
  | Loop
  (* No evaluation at all: the value in the cache is a dummy value, set
     to avoid a loop in the use of the oracle. *)
  | Finite of int
  (* An evaluation with a finite level of fuel, which has been consumed. *)
  | Infty
  (* The evaluation never used all its fuel. *)

let less_fuel_than n = function
  | Loop     -> true
  | Finite f -> f >= n
  | Infty    -> true

(* Some information about a forward evaluation. *)
type forward_report = {
  fuel: fuel;      (* The fuel used for the evaluation. *)
  reduced: bool; (* Whether a reduction has occur, which may be propagated
                    to the sub-terms. *)
}

(* Parameters of the evaluation of the location of a left value. *)
type loc_report = {
  for_writing: bool;
  reduction: bool;
}

(* If a value is cached by an external source, we assume that it was
   computed with infty fuel and that possible reduction have been
   propagated backward. *)
let extern_report = { fuel = Infty; reduced = false }

(* Report used when the cache is filled with a dummy value to avoid evaluation
   loops. *)
let dummy_report = { fuel = Loop; reduced = false }

let no_fuel = -1
let root_fuel () = Value_parameters.OracleDepth.get ()
let backward_fuel () = Value_parameters.ReductionDepth.get ()

let already_precise_loc_report ~for_writing ~reduction loc_report =
  (not for_writing || loc_report.for_writing)
  && (not reduction || loc_report.reduction)


let rec may_be_reduced_offset = function
  | NoOffset -> false
  | Field (_, offset) -> may_be_reduced_offset offset
  | Index _ -> true

let may_be_reduced_lval (host, offset) = match host with
  | Var _ -> may_be_reduced_offset offset
  | Mem _ -> true

let may_be_reduced_expr = function
  | Lval _ | UnOp _ | BinOp _ | CastE _ -> true
  | _ -> false

module type S = sig
  type state
  type value
  type origin
  type loc
  module Valuation : Valuation with type value = value
                                and type origin = origin
                                and type loc = loc
  val evaluate :
    ?valuation:Valuation.t -> ?indeterminate:bool -> ?reduction:bool ->
    state -> exp -> (Valuation.t * value) evaluated
  val lvaluate :
    ?valuation:Valuation.t -> for_writing:bool ->
    state -> lval -> (Valuation.t * loc * typ) evaluated
  val reduce:
    ?valuation:Valuation.t -> state -> exp -> bool -> Valuation.t evaluated

  val loc_size: loc -> Int_Base.t
  val reinterpret: exp -> typ -> value -> value evaluated
  val do_promotion: src_typ:typ -> dst_typ: typ -> exp -> value -> value evaluated
  val split_by_evaluation:
    exp -> Integer.t list -> state list ->
    (Integer.t * state list * bool) list * state list
  val check_copy_lval: (lval * loc) -> (lval * loc) -> bool evaluated
  val check_non_overlapping:
    state -> lval list -> lval list -> unit evaluated
  val eval_function_exp:
    exp -> state -> (Kernel_function.t * Valuation.t) list evaluated
end

let return t = `Value t, Alarmset.none

(* Returns an over-approximation of the alarms that may occur in the dereference
   of the left-value [lval] of type [typ]. *)
let alarms_of_dereference lval typ =
  let indeterminate_alarms =
    Alarmset.add
      (Alarms.Dangling lval) (Alarmset.singleton (Alarms.Uninitialized lval))
  in
  match typ with
  | TFloat (fkind, _) ->
    let expr = Cil.dummy_exp (Cil_types.Lval lval) in
    Alarmset.add (Alarms.Is_nan_or_infinite (expr, fkind)) indeterminate_alarms
  | _ -> indeterminate_alarms

(* Intersects [alarms] with the only possible alarms from the dereference of
   the left-value [lval] of type [typ].
   Usefull if the abstract domain returns a non-closed AllBut alarmset for
   some lvalues. *)
let close_dereference_alarms lval typ alarms =
  let closed_alarms = alarms_of_dereference lval typ in
  match Alarmset.inter alarms closed_alarms with
  | `Inconsistent -> Value_parameters.abort ~current:true ~once:true
                       "Inconsistent status of alarms: unsound states."
  | `Value alarms -> alarms

let define_value value =
  { v = `Value value; initialized = true; escaping = false }

(* [v] and [alarms] must be the value and the alarms from the evaluation of
   the lvalue [lval].
   In indeterminate mode, remove the alarms about the initialization and the
   escaping of [lval], and sets accordingly the initialized and escaping flags
   of the computed value. *)
let determinize_lval indeterminate lval v alarms =
  let init_alarm = Alarms.Uninitialized lval
  and escap_alarm = Alarms.Dangling lval in
  let initialized = Alarmset.find init_alarm alarms = Alarmset.True
  and escaping = not (Alarmset.find escap_alarm alarms = Alarmset.True) in
  let alarms =
    if indeterminate
    then
      Alarmset.add' escap_alarm Alarmset.True
        (Alarmset.add' init_alarm Alarmset.True alarms)
    else alarms
  in
  let value =
    if indeterminate
    then { v; initialized; escaping }
    else { v; initialized = true; escaping = false }
  in
  let reductness =
    if indeterminate || (initialized && not escaping)
    then Unreduced
    else Reduced
  in
  if value.v = `Bottom && initialized && not escaping
  then `Bottom, alarms
  else `Value (value, reductness), alarms


module type Value = sig
  include Abstract_value.External
  val reduce : t -> t
end

module Make
    (Value : Value)
    (Loc : Abstract_location.S with type value = Value.t)
    (Domain : Abstract_domain.Queries with type value = Value.t
                                       and type location = Loc.location)
= struct

  type state = Domain.state
  type value = Value.t
  type origin = Domain.origin
  type loc = Loc.location

  module ECache = Cil_datatype.ExpStructEq.Map
  module LCache = Cil_datatype.LvalStructEq.Map

  (* Imperative cache for the evaluation:
     all intermediate results of an evaluation are cached here.
     See [eval.mli] for more details. *)
  module Cache = struct
    type value = Value.t
    type origin = Domain.origin
    type loc = Loc.location

    (* For expression, the forward_report about the evaluation is also stored. *)
    type t =
      ((value, origin) record_val * forward_report) ECache.t
      * (loc record_loc * (forward_report * loc_report)) LCache.t

    (* Interface of Context.Valuation *)
    let empty : t = ECache.empty, LCache.empty
    let find (cache:t) exp =
      try `Value (fst (ECache.find exp (fst cache)))
      with Not_found -> `Top
    let add (cache:t) exp record =
      let s, t = cache in ECache.add exp (record, extern_report) s, t
    let fold f (cache:t) acc =
      ECache.fold (fun e (r, _) acc -> f e r acc) (fst cache) acc

    (* Functions used by the evaluator, with the boolean for backward
       reduction. *)
    let find' (cache:t) exp = ECache.find exp (fst cache)
    let add' (cache:t) exp record =
      let s, t = cache in ECache.add exp record s, t

    (* Locations of lvalue. *)
    let find_loc (cache:t) lval =
      try `Value (fst (LCache.find lval (snd cache)))
      with Not_found -> `Top

    (* Locations of lvalue. *)
    let find_loc' (cache:t) lval =
      try `Value (LCache.find lval (snd cache))
      with Not_found -> `Top
    let add_loc' (cache:t) lval record =
      let s, t = cache in s, LCache.add lval record t

    let filter f_exp f_lv (s, t) =
      ECache.filter (fun exp (record, _) -> f_exp  exp record) s,
      LCache.filter (fun lval (record, _) -> f_lv lval record) t
  end

  (* Imperative cache for the evaluator. A reference is mandatory here, because
     the cache must be also filled by the evaluations initiated by a domain
     through the oracle, but should not leak in the domain queries signature. *)
  let cache = ref Cache.empty

  (* Was the fuel entirely consumed? *)
  let fuel_consumed = ref false

  let top_record =
    let flagged_top =
      { v = `Value Value.top; initialized = false; escaping = true }
    in
    { value = flagged_top; origin = None;
      reductness = Dull; val_alarms = Alarmset.all }

  let reduce_expr ~forward expr value =
    let record, report = Cache.find' !cache expr in
    let reductness =
      if record.reductness = Unreduced then Reduced else record.reductness
    in
    (* TODO: allow to reduce initialized and escaping flags? *)
    let record = { record with value = define_value value; reductness } in
    let report = { report with reduced = forward } in
    cache := Cache.add' !cache expr (record, report)

  let reduce_value record =
    let v = record.value.v >>-: Value.reduce in
    { record with value = {record.value with v = v} }

  (* Returns the cached evaluation if it exists;
     call [coop_forward_eval] and caches its result otherwise. *)
  let rec forward_eval ?(indeterminate=false) fuel state expr =
    (* Search in the cache for the result of a previous computation. *)
    try
      let record, report = Cache.find' !cache expr in
      (* If the record was computed with more fuel than [fuel], return it. *)
      if report.fuel = Loop then fuel_consumed := true;
      if less_fuel_than fuel report.fuel
      then record.value.v, record.val_alarms
      else raise Not_found
    (* If no result found, evaluate the expression. *)
    with Not_found ->
      let previous_fuel_consumed = !fuel_consumed in
      (* Fuel not consumed for this new evaluation. *)
      fuel_consumed := false;
      (* Fill the cache to avoid loops in the use of the oracle. *)
      cache := Cache.add' !cache expr (top_record, dummy_report);
      (* Evaluation of [expr] *)
      coop_forward_eval ~indeterminate fuel state expr
      >>=. fun (record, reduced) ->
      let record = reduce_value record in
      (* Cache the computed result with appropriate report. *)
      let fuel = if !fuel_consumed then Finite fuel else Infty in
      let report = {fuel; reduced} in
      cache := Cache.add' !cache expr (record, report);
      (* Reset the flag fuel_consumed. *)
      fuel_consumed := previous_fuel_consumed || !fuel_consumed;
      record.value.v

  (* Asks the abstract domain for the abstract value of [expr],
     and performs the narrowing with the value computed by
     [internal_forward_eval].
     Also returns:
     - the state of reduction of the value provided by the domain (Reduced if
     the value computed by the internal evaluation is more precise than that
     given by the domain);
     - a boolean indicating the need of a backward reduction from [expr]
     (true if the computed value has been reduced thanks to the domain or the
     emitted alarms). *)
  and coop_forward_eval ~indeterminate fuel state expr =
    match expr.enode with
    | Lval lval -> eval_lval ~indeterminate fuel state lval
    | BinOp _ | UnOp _ | CastE _ -> begin
        let intern_value, alarms = internal_forward_eval fuel state expr in
        let oracle =
          if fuel > 0
          then forward_eval ~indeterminate:false (pred fuel) state
          else fun _ -> fuel_consumed := true; `Value Value.top, Alarmset.all
        in
        let domain_value, alarms' = Domain.extract_expr oracle state expr in
        (* Intersection of alarms, as each sets of alarms are correct
           and "complete" for the evaluation of [expr]. *)
        match Alarmset.inter alarms alarms' with
        | `Inconsistent ->
          Value_parameters.abort ~current:true ~once:true
            "Inconsistent status of alarms: unsound states."
        | `Value alarms ->
          let v =
            intern_value >>- fun (intern_value, to_reduce) ->
            domain_value >>- fun (domain_value, origin) ->
            Value.narrow intern_value domain_value >>-: fun result ->
            let reductness =
              if Value.equal domain_value result then Unreduced
              else if Value.(equal domain_value top) then Created else Reduced
            in
            let to_reduce = Value.equal intern_value result && to_reduce
            and origin = Some origin
            and value = define_value result in
            {value; origin; reductness; val_alarms = alarms},
            to_reduce
          in
          v, alarms
      end
    | _ ->
      let eval, alarms = internal_forward_eval fuel state expr in
      let record =
        eval >>-: fun (value, to_reduce) ->
        let value = define_value value in
        {value; origin = None; reductness = Dull; val_alarms = alarms}, to_reduce
      in
      record, alarms

  (* Reinterpret the abstract value computed by [recursive_forward_eval]
     according to the type of [expr].
     Also returns a boolean indicating if the value has been reduced. *)
  and internal_forward_eval fuel state expr =
    recursive_forward_eval fuel state expr >>= fun (value, to_reduce) ->
    (* TODO: the functions called above should respect the destination type.
       Calling reinterpret should be useless *)
    let v, a = Value.reinterpret expr (Cil.typeOf expr) value in
    (v, a) >>=: fun v -> v, not (Alarmset.is_empty a) || to_reduce

  (* Recursive descent in the sub-expressions.
     Return the abstract value of the expression and a boolean that indicates
     whether this value could have been reduced by alarms. *)
  and recursive_forward_eval fuel state expr =
    let process (v, a) = (v, a) >>=: fun v -> v, not (Alarmset.is_empty a) in
    match expr.enode with
    | Info (e, _) -> internal_forward_eval fuel state e

    | Const c ->
      begin match c with
        | CEnum {eival = e} ->
          forward_eval fuel state e >>=: fun value -> value, false
        | _ -> Value.constant expr c >>=: fun value -> value, false
      end

    | Lval _lval -> assert false

    | AddrOf v | StartOf v ->
      lval_to_loc fuel ~for_writing:false ~reduction:false state v
      >>=: fun (loc, _) ->
      Loc.to_value loc, false

    | UnOp (op, e, _typ) ->
      forward_eval fuel state e >>= fun v ->
      let context = (e, expr)
      and typ = Cil.unrollType (Cil.typeOf e) in
      let v = Value.forward_unop ~context typ op v in
      process v

    | BinOp (op, e1, e2, typ) ->
      let context = (e1, e2, expr, typ) in
      forward_eval fuel state e1 >>= fun v1 ->
      forward_eval fuel state e2 >>= fun v2 ->
      let typ_e1 = Cil.unrollType (Cil.typeOf e1) in
      let v = Value.forward_binop ~context typ_e1 op v1 v2 in
      process v

    | CastE (dst_typ, e) ->
      forward_eval fuel state e >>= fun value ->
      let src_typ = Cil.typeOf e in
      let v = Value.do_promotion ~src_typ ~dst_typ e value in
      process v

    | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ ->
      match Cil.constFoldToInt expr with
      | Some v -> return (Value.inject_int v, false)
      | _      -> return (Value.top_int, false)


  (* ------------------------------------------------------------------------
                                Lvalue evaluation
     ------------------------------------------------------------------------ *)

  (* Calls the internal evaluation of an lvalue to a location, and stores the
     result in the cache. If the result is already in the cache, the computation
     is avoided, unless if it may reduce the cache.
     If [reduction] is false, don't reduce the location and the offset by their
     valid parts, and don't emit alarms about their validity. *)
  and lval_to_loc fuel ~for_writing ~reduction state lval =
    let compute () =
      let res, alarms =
        reduced_lval_to_loc fuel ~for_writing ~reduction state lval
      in
      let res =
        res >>- fun (loc, typ_offs) ->
        let record = { loc; typ = typ_offs; loc_alarms = alarms }
        and report = { fuel = Finite fuel;
                       reduced = not (Alarmset.is_empty alarms) }
        and loc_report = { for_writing; reduction } in
        cache := Cache.add_loc' !cache lval (record, (report, loc_report));
        res
      in
      res, alarms
    in
    match Cache.find_loc' !cache lval with
    | `Value (record, (forward_report, loc_report)) ->
      if
        already_precise_loc_report ~for_writing ~reduction loc_report
        && less_fuel_than fuel forward_report.fuel
      then `Value (record.loc, record.typ), record.loc_alarms
      else compute ()
    | `Top -> compute ()

  (* If [reduction] is false, don't reduce the location and the offset by their
     valid parts, and don't emit alarms about their validity. *)
  and reduced_lval_to_loc fuel ~for_writing ~reduction state lval =
    let eval = internal_lval_to_loc fuel ~for_writing ~reduction state lval in
    if not reduction
    then eval
    else
      eval >>= fun (loc, typ) ->
      let bitfield = Cil.isBitfield lval in
      Loc.reduce_loc_by_validity ~for_writing ~bitfield lval loc
      >>=: fun valid_loc -> valid_loc, typ

  (* Internal evaluation of a lvalue to an abstract location. *)
  and internal_lval_to_loc fuel ~for_writing ~reduction state lval =
    let host, offset = lval in
    let typ = match host with
      | Var host -> host.vtype
      | Mem x -> Cil.typeOf_pointed (Cil.typeOf x)
    in
    eval_offset fuel ~reduce_valid_index:reduction typ state offset
    >>= fun (offs, typ_offs) ->
    if for_writing && Value_util.is_const_write_invalid typ_offs
    then
      `Bottom,
      Alarmset.singleton (Alarms.Memory_access (lval, Alarms.For_writing))
    else
      eval_host fuel state typ_offs offs host >>=: fun loc ->
      loc, typ_offs

  (* Combination of the evaluation of the right part of an lval (an host) with
     an offset, to obtain a location *)
  and eval_host fuel state typ_offset offs = function
    | Var host -> Loc.forward_variable typ_offset host offs, Alarmset.none
    | Mem x ->
      forward_eval fuel state x >>=. fun loc_lv ->
      Loc.forward_pointer typ_offset loc_lv offs

  and eval_offset fuel ~reduce_valid_index typ state = function
    | NoOffset               -> return (Loc.no_offset, typ)
    | Index (index_expr, remaining) ->
      let typ_pointed, array_size = match Cil.unrollType typ with
        | TArray (t, size, _, _) -> t, size
        | t -> Value_parameters.fatal ~current:true
                 "Got type '%a'" Printer.pp_typ t
      in
      eval_offset fuel ~reduce_valid_index typ_pointed state remaining >>=
      fun (roffset, typ_offs) ->
      forward_eval fuel state index_expr >>= fun index ->
      let valid_index =
        if not (Kernel.SafeArrays.get ()) || not reduce_valid_index
        then `Value index, Alarmset.none
        else
          try
            (* If possible, reduce the index value by the array size. *)
            let size = Cil.lenOfArray64 array_size in
            (* Handle the special GCCism of zero-sized arrays: Frama-C
               pretends their size is unknown, exactly like GCC. *)
            if Integer.is_zero size
            then `Value index, Alarmset.none
            else
              let size_expr = Extlib.the array_size in (* array_size exists *)
              Loc.reduce_index_by_array_size ~size_expr ~index_expr size index
              >>=: fun new_index ->
              (* Update the cache with the new value of the index *)
              if not (Value.equal index new_index)
              then reduce_expr ~forward:true index_expr new_index;
              new_index
          with
          | Cil.LenOfArray -> `Value index, Alarmset.none (* unknown array size *)
      in
      valid_index >>=: fun index ->
      Loc.forward_index typ_pointed index roffset, typ_offs
    | Field (fi, remaining) ->
      let attrs = Cil.filter_qualifier_attributes (Cil.typeAttrs typ)  in
      let typ_fi = Cil.typeAddAttributes attrs fi.ftype in
      eval_offset fuel ~reduce_valid_index typ_fi state remaining
      >>=: fun (r, typ_res) ->
      let off = Loc.forward_field typ fi r in
      off, typ_res

  and eval_lval ?(indeterminate=false) fuel state lval =
    (* Computes the location of [lval]. *)
    let v, alarms =
      lval_to_loc fuel ~for_writing:false ~reduction:true state lval
    in
    let to_reduce = not (Alarmset.is_empty alarms) in
    (* Find the value of the location, if not bottom. *)
    let res, alarms =
      (v, alarms) >>= fun (loc, typ_lv) ->
      let oracle =
        if fuel > 0
        then forward_eval ~indeterminate (pred fuel) state
        else fun _ -> fuel_consumed := true; `Value Value.top, Alarmset.all
      in
      let v, alarms = Domain.extract_lval oracle state lval typ_lv loc in
      let alarms = close_dereference_alarms lval typ_lv alarms in
      determinize_lval indeterminate lval (v >>-: fst) alarms
      >>=: fun (value, reductness) ->
      let origin = match v with
        | `Bottom -> None
        | `Value (_, o) -> Some o
      in
      value, origin, reductness
    in
    (* Create the record, if not bottom. *)
    (res, alarms) >>=: fun (value, origin, reductness) ->
    {value = value; origin; reductness; val_alarms = alarms}, to_reduce


  (* ------------------------------------------------------------------------
                           Backward Evaluation
     ------------------------------------------------------------------------ *)

  let eq_zero positive e =
    let op = if positive then Eq else Ne in
    Cil.new_exp ~loc:e.eloc (BinOp (op, Value_util.zero e, e, Cil.intType))

  (* Find the value of a previously evaluated expression. *)
  let find_val expr =
    match Cache.find !cache expr with
    | `Value record -> record.value.v
    | `Top -> assert false (* [expr] must have been evaluated already. *)

  (* Find the location of a previously evaluated lvalue. *)
  let find_loc lval =
    match Cache.find_loc !cache lval with
    | `Value record -> record
    | `Top -> assert false

  (* Evaluate an expression before any reduction, if needed. Also return the
     report indicating if a forward reduction during the forward evaluation may
     be propagated backward. *)
  let evaluate_for_reduction state expr =
    try `Value (Cache.find' !cache expr)
    with Not_found ->
      fst (forward_eval no_fuel state expr) >>-: fun _ ->
      try Cache.find' !cache expr
      with Not_found -> assert false

  (* [backward_eval state expr value] reduces the the expression [expr] and
     its subterms in the cache, according to the state [state]:
     - the reductions performed during the forward evaluation (due to alarms or
       abstract domains) are propagated backward to the subexpressions;
     - the accessed memory locations are reduced by their valid part for a read
       operation;
     - if [value = Some v], then [expr] is assumed to evaluate to [v] (and is
       reduced accordingly). *)
  let rec backward_eval fuel state expr value =
    (* Evaluate the expression if needed. *)
    evaluate_for_reduction state expr >>- fun (record, report) ->
    record.value.v >>- fun old_value ->
    (* The reduction of the current operation is relevant only if:
       - the new value (if any) is more precise than the old value;
       - or the old value has been reduced during the forward évaluation due to
         alarms or abstract domains: then, [report.reduced] must be [true]. *)
    let reduction_value = match value with
      | None -> `Value (old_value, report.reduced)
      | Some new_value ->
        Value.narrow new_value old_value >>-: fun value ->
        if Value.is_included old_value value
        then old_value, report.reduced
        else value, true
    in
    reduction_value >>- fun (value, to_reduce) ->
    (* If no reduction to be propagated, just visit the subterms. *)
    if not to_reduce
    then recursive_descent fuel state expr
    else
      (* Otherwise, backward reduction of the subterms. *)
      reduce_backward fuel state expr value >>-: fun (reduced_value, exact) ->
      (* If the new [value] for [expr] is more precise than the [old_value],
         store it in the cache. *)
      if not (Value.is_included old_value reduced_value)
      then begin
        reduce_expr ~forward:false expr reduced_value;
        (* If enough fuel, asks the domain for more reductions. *)
        if fuel > 0
        then
          let reduce (expr, v) =
            ignore (backward_eval (pred fuel) state expr (Some v))
          in
          List.iter reduce (Domain.reduce_further state expr reduced_value)
      end;
      exact

  (* Propagate the reduction [expr] = [value] to the subterms of the expression.
     Also returns a boolean denoting whether the reduction has been exact, i.e.
     if the forward evaluation of [expr] now computes the reduced [value]. *)
  and reduce_backward fuel state expr value =
    match expr.enode with
    | Lval lval ->
      backward_lvalue fuel ~for_writing:false state lval >>- fun exact ->
      if may_be_reduced_lval lval
      then
        fst (eval_lval no_fuel state lval) >>- fun (record, _) ->
        record.value.v >>-: fun evaled_value ->
        let precise = Value.is_included evaled_value value in
        let value = if precise then evaled_value else value in
        value, precise && exact
      else `Value (value, true)
    | _ ->
      internal_backward fuel state expr value >>- fun exact ->
      if may_be_reduced_expr expr.enode
      then
        fst (internal_forward_eval no_fuel state expr) >>-: fun (evaled, _) ->
        let precise = Value.is_included evaled value in
        let value = if precise then evaled else value in
        value, exact && precise
      else
        `Value (value, true)

  (* Backward propagate the reduction [expr] = [value] to the subterms of the
     compound expression [expr]. Also returns a boolean denoting whether the
     reduction of all subterms have been exact.*)
  and internal_backward fuel state expr value =
    match expr.enode with
    | Lval _lv -> assert false
    | UnOp (LNot, e, _) ->
      (* TODO: should we compute the meet with the result of the call to
         Value.backward_unop? *)
      backward_eval fuel state (eq_zero true e) (Some value)
    | UnOp (op, e, _typ) ->
      let typ_e = Cil.unrollType (Cil.typeOf e) in
      find_val e >>- fun v ->
      Value.backward_unop ~typ_arg:typ_e op ~arg:v ~res:value
      >>- fun v ->
      backward_eval fuel state e v
    | BinOp (binop, e1, e2, typ) ->
      let typ_res = Cil.unrollType typ
      and typ_e1 = Cil.typeOf e1 in
      find_val e1 >>- fun v1 ->
      find_val e2 >>- fun v2 ->
      Value.backward_binop
        ~input_type:typ_e1
        ~resulting_type:typ_res
        binop ~left:v1 ~right:v2 ~result:value
      >>- fun (v1, v2) ->
      backward_eval fuel state e1 v1 >>- fun exact1 ->
      backward_eval fuel state e2 v2 >>-: fun exact2 ->
      exact1 && exact2
    | CastE (typ, e) ->
      begin
        let dst_typ = Cil.unrollType typ in
        let src_typ = Cil.unrollType (Cil.typeOf e) in
        find_val e >>- fun src_val ->
        Value.backward_cast ~src_typ ~dst_typ ~src_val ~dst_val:value
        >>- function v -> backward_eval fuel state e v
      end
    | Info (e, _) -> backward_eval fuel state e None
    | _ -> `Value true

  and recursive_descent fuel state expr =
    match expr.enode with
    | Lval lval -> recursive_descent_lval fuel state lval
    | UnOp (_, e, _)
    | CastE (_, e)
    | Info (e, _) -> backward_eval fuel state e None
    | BinOp (_binop, e1, e2, _typ) ->
      backward_eval fuel state e1 None >>- fun precise1 ->
      backward_eval fuel state e2 None >>-: fun precise2 ->
      precise1 && precise2
    | _ -> `Value true

  and recursive_descent_lval fuel state (host, offset) =
    recursive_descent_host fuel state host >>- fun precise1 ->
    recursive_descent_offset fuel state offset >>-: fun precise2 ->
    precise1 && precise2

  and recursive_descent_host fuel state = function
    | Var _ -> `Value true
    | Mem expr -> backward_eval fuel state expr None

  and recursive_descent_offset fuel state = function
    | NoOffset               -> `Value true
    | Field (_, remaining)   -> recursive_descent_offset fuel state remaining
    | Index (exp, remaining) ->
      backward_eval fuel state exp None >>- fun precise1 ->
      recursive_descent_offset fuel state remaining >>-: fun precise2 ->
      precise1 && precise2

  (* Backward evaluation of a left-value. *)
  and backward_lvalue fuel ~for_writing state lval =
    backward_host fuel ~for_writing state lval >>- fun precise1 ->
    recursive_descent_lval fuel state lval >>-: fun precise2 ->
    precise1 && precise2

  (* If [lv] is precise enough, we reduce its location to the parts that are
     valid for a read/write operation *)
  and backward_host fuel ~for_writing:_ state lv =
    match lv with
    | Var _, _ -> `Value true
    | Mem expr, offset ->
      let record = find_loc lv in
      let loc_value = Loc.to_value record.loc in
      match offset with
      | NoOffset -> backward_eval fuel state expr (Some loc_value)
      | _ ->
        let reduce_valid_index = true in
        let typ_lval = Cil.typeOf_pointed (Cil.typeOf expr) in
        fst (eval_offset no_fuel ~reduce_valid_index typ_lval state offset)
        >>- fun (offset, _) ->
        Loc.backward_pointer record.loc offset >>- fun pointer_value ->
        backward_eval fuel state expr (Some pointer_value)


  (* ------------------------------------------------------------------------
                           Reduce by Cond Enumerate
     ------------------------------------------------------------------------ *)

  (* Reduce by cond enumerate : when a backward evaluation is not precise
     enough, tries to reduce further by enumerating the value of some
     "influential" lvalues. As we can enumerate only on cvalues, extracts
     the cvalue component of the value module. *)

  let get_cvalue = Value.get Main_values.cvalue_key
  let set_cvalue = Value.set Main_values.cvalue_key

  (* It is worthwhile to enumerate on a cvalue when it has a small cardinal
     but is not a singleton. *)
  let is_enumerable value =
    not (Cvalue.V.cardinal_zero_or_one value) &&
    try
      let upto = succ (Ival.get_small_cardinal ()) in
      ignore (Cvalue.V.cardinal_less_than value upto);
      true
    with Abstract_interp.Not_less_than -> false

  (* Find locations on which it is interesting to proceed by case disjunction
     to evaluate the expression: locations which are singletons (on which the
     cvalue domain can reduce) and has an enumerable value. *)
  let rec get_influential_vars get_cvalue state exp acc =
    match exp.enode with
    | Lval (Var v,  off) ->
      let reduce_valid_index = true in
      let eval, _ = eval_offset no_fuel ~reduce_valid_index v.vtype state off in
      eval >>- fun (offset, _) ->
      if Loc.offset_cardinal_zero_or_one offset
      then
        (* no variable in offset can be influential. Check the
           contents of the location, on which we might want to enumerate  *)
        if Base.(is_weak (of_varinfo v)) then
          `Value acc (* cannot enumerate on the contents, multiple locations *)
        else
          find_val exp >>- fun contents ->
          if is_enumerable (get_cvalue contents)
          then `Value (exp :: acc)
          else `Value acc
      else
        (* A variable in offset may be influential. The contents themselves
           are not influential, because we would need to split both by
           offset and by content in sync. *)
        get_vars_offset get_cvalue state off acc
    | Lval (Mem e, off) ->
      let t = Cil.typeOf_pointed (Cil.typeOf e) in
      let eval, _ = eval_offset no_fuel ~reduce_valid_index:true t state off in
      eval >>- fun (offset, _) ->
      if Loc.offset_cardinal_zero_or_one offset
      then
        find_val e >>- fun contents ->
        find_val exp >>- fun value ->
        if Cvalue.V.cardinal_zero_or_one (get_cvalue contents)
        && is_enumerable (get_cvalue value)
        then `Value (exp :: acc)
        else get_influential_vars get_cvalue state e acc
      else
        (* variables in expr or offset can be influential *)
        get_influential_vars get_cvalue state e acc >>- fun acc ->
        get_vars_offset get_cvalue state off acc
    | BinOp (_, e1, e2, _) ->
      get_influential_vars get_cvalue state e1 acc >>- fun acc ->
      get_influential_vars get_cvalue state e2 acc
    | UnOp (_, e, _) -> get_influential_vars get_cvalue state e acc
    | CastE (_, exp) -> get_influential_vars get_cvalue state exp acc
    | _ -> `Value acc

  and get_vars_offset get_cvalue state offset acc = match offset with
    | NoOffset         -> `Value acc
    | Field (_, off)   -> get_vars_offset get_cvalue state off acc
    | Index (ind, off) ->
      get_influential_vars get_cvalue state ind acc >>- fun acc ->
      get_vars_offset get_cvalue state off acc

  let get_influential_exprs get_cvalue state expr =
    get_influential_vars get_cvalue state expr []

  module Clear = Eval.Clear_Valuation (Cache)

  let reduce_by_cond_enumerate get_cvalue state cond positive influentials =
    (* Test whether the condition [expr] may still be true when the
       sub-expression [e] has the value [v]. *)
    let condition_may_still_be_true cleared_cache expr record value =
      let cache_cache = !cache in
      let value = { record.value with v = `Value value } in
      cache := Cache.add cleared_cache expr { record with value };
      let eval, _alarms = forward_eval no_fuel state cond in
      cache := cache_cache;
      match eval with
      | `Bottom -> false
      | `Value v ->
        let v = get_cvalue v in
        if positive
        then Cvalue.V.contains_non_zero v
        else if Value_parameters.UndefinedPointerComparisonPropagateAll.get ()
        then Cvalue.V.contains_zero v
        else Cvalue.V.is_included Cvalue.V.singleton_zero v
    in
    let enumerate expr =
      match Cache.find !cache expr with
      | `Top -> `Value ()
      | `Value record ->
        record.value.v >>- fun v ->
        let cleared_cache = Clear.clear_expr !cache expr in
        let process sub_cvalue acc =
          let subvalue = set_cvalue sub_cvalue v in
          if condition_may_still_be_true cleared_cache expr record subvalue
          then Bottom.join Value.join (`Value subvalue) acc else acc
        in
        let cvalue = get_cvalue v in
        Cvalue.V.fold_enum process cvalue `Bottom >>-: fun value ->
        if not (Value.equal v value)
        then
          let reductness =
            if record.reductness = Created then Created else Reduced
          in
          let value = { record.value with v = `Value value } in
          let record = { record with value; reductness } in
          cache := Cache.add !cache expr record
    in
    match influentials with
    | [] -> `Value ()
    | expr :: _ -> enumerate expr

  (* If the value module contains no cvalue component, this function is
     inoperative. Otherwise, it calls reduce_by_cond_enumerate with the
     value accessor for the cvalue component. *)
  let reduce_by_enumeration = match get_cvalue with
    | None -> fun _ _ _ -> `Value ()
    | Some get_cvalue ->
      fun state expr positive ->
        get_influential_exprs get_cvalue state expr >>- fun split_on ->
        reduce_by_cond_enumerate get_cvalue state expr positive split_on


  (* ------------------------------------------------------------------------
                              Generic Interface
     ------------------------------------------------------------------------ *)

  module Valuation = Cache

  let evaluate
      ?(valuation=Cache.empty) ?(indeterminate=false) ?(reduction=true)
      state expr =
    cache := valuation;
    let value, alarms = forward_eval ~indeterminate (root_fuel ()) state expr in
    let result =
      value >>- fun value ->
      if not reduction || Alarmset.is_empty alarms
      then `Value (!cache, value)
      else
        backward_eval (backward_fuel ()) state expr None >>- fun _ ->
        find_val expr >>-: fun value ->
        !cache, value
    in
    result, alarms

  let lvaluate ?(valuation=Cache.empty) ~for_writing state lval =
    cache := valuation;
    lval_to_loc (root_fuel ()) ~for_writing ~reduction:true state lval
    >>=. fun (_, typ) ->
    backward_lvalue (backward_fuel ()) ~for_writing state lval >>-: fun _ ->
    let record = find_loc lval in
    !cache, record.loc, typ

  let inv_rel = function
    | Gt -> Le
    | Lt -> Ge
    | Le -> Gt
    | Ge -> Lt
    | Eq -> Ne
    | Ne -> Eq
    | _ -> assert false

  (* Transform an expression supposed to be [positive] into an equivalent
     one in which the root expression is a comparison operator. *)
  let rec normalize_as_cond expr positive =
    match expr.enode with
    | UnOp (LNot, e, _) -> normalize_as_cond e (not positive)
    | BinOp ((Le|Ne|Eq|Gt|Lt|Ge as binop), e1, e2, typ) ->
      if positive then
        expr
      else
        let binop = inv_rel binop in
        let enode = BinOp (binop, e1, e2, typ) in
        Cil.new_exp ~loc:expr.eloc enode
    | _ ->
      eq_zero (not positive) expr

  let reduce ?valuation:(valuation=Cache.empty) state expr positive =
    let aux state expr =
      (* Generate [e == 0] *)
      let expr = normalize_as_cond expr (not positive) in
      forward_eval (root_fuel ()) state expr >>=. fun _ ->
      (* Reduce by [(e == 0) == 0] *)
      backward_eval (backward_fuel ()) state expr (Some Value.zero)
      >>- fun exact ->
      if not exact
      then reduce_by_enumeration state expr false
      else `Value ()
    in
    cache := valuation;
    aux state expr >>=: fun () ->
    !cache


  (* ------------------------------------------------------------------------
                                      Misc
     ------------------------------------------------------------------------ *)

  let loc_size = Loc.size

  let reinterpret = Value.reinterpret
  let do_promotion = Value.do_promotion

  let eval_function_exp funcexp state =
    match funcexp.enode with
    | Lval (Var vinfo, NoOffset) ->
      `Value [Globals.Functions.get vinfo, Valuation.empty],
      Alarmset.none
    | Lval (Mem v, NoOffset) ->
      evaluate state v >>= fun (valuation, value) ->
      let typ_pointer = Cil.typeOf funcexp in
      let kfs, alarm = Value.resolve_functions ~typ_pointer value in
      let alarm =
        Alarmset.(if alarm then singleton (Alarms.Function_pointer v) else none)
      in
      (* For pointer calls, we retro-propagate which function is being called
         in the abstract state. This may be useful:
         - inside the call for langages with OO (think 'self')
         - everywhere, because we may remove invalid values for the pointer
         - after if enough slevel is available, as states obtained in
           different functions are not merged by default. *)
      let reduce kf =
        cache := valuation;
        let vi_f = Kernel_function.get_vi kf in
        let value = Loc.to_value (Loc.eval_varinfo vi_f) in
        backward_eval 0 state v (Some value) >>- fun exact ->
        if not exact then
          (* Build the expression [exp_f == &f] and reduce accordingly *)
          let addr = Cil.mkAddrOfVi vi_f in
          let expr = Cil.mkBinOp ~loc:v.eloc Eq v addr in
          reduce_by_enumeration state expr true >>-: fun () -> !cache
        else
          `Value !cache
      in
      let process kf acc =
        let res = reduce kf >>-: fun valuation -> kf, valuation in
        Bottom.add_to_list res acc
      in
      begin match kfs with
        | `Value kfs ->
          Bottom.bot_of_list (Kernel_function.Hptset.fold process kfs []), alarm
        | `Top ->
          if Mark_noresults.no_memoization_enabled () then
            Value_parameters.abort ~current:true
              "Function pointer evaluates to anything. Try deactivating \
               option(s) -no-results, -no-results-function and \
               -obviously-terminates@."
          else
            Value_parameters.fatal ~current:true
              "Function pointer evaluates to anything. function %a"
              Printer.pp_exp funcexp
      end
    | _ -> assert false

  let split_by_evaluation expr expected_values states =
    let eval acc state =
      match fst (evaluate state expr) with
      | `Bottom -> acc
      | `Value (_cache, value) -> (state, value) :: acc
    in
    let eval_states = List.fold_left eval [] states in
    let match_expected_value expected_value states =
      let process_one_state (eq, neq, mess) (s, v) =
        if Value.equal expected_value v
        then (s :: eq, neq, mess)
        else
          let mess = mess || Value.is_included expected_value v in
          (eq, (s, v) :: neq, mess)
      in
      List.fold_left process_one_state ([], [], false) states
    in
    let process_one_value (acc, states) i =
      let value = Value.inject_int i in
      let eq, neq, mess = match_expected_value value states in
      (i, eq, mess) :: acc, neq
    in
    let matched, tail =
      List.fold_left process_one_value ([], eval_states) expected_values
    in
    matched, List.map fst tail

  let check_non_overlapping state lvs1 lvs2 =
    let eval_loc (acc_list, valuation) lval =
      let for_writing = false in
      match fst (lvaluate ~valuation ~for_writing state lval) with
      | `Bottom -> acc_list, valuation
      | `Value (valuation, loc, _) -> (lval, loc) :: acc_list, valuation
    in
    let eval_list valuation lvs =
      List.fold_left eval_loc ([], valuation) lvs
    in
    let list1, valuation = eval_list Valuation.empty lvs1 in
    let list2, _ = eval_list valuation lvs2 in
    Loc.check_non_overlapping list1 list2

  let check_copy_lval (lval1, loc1) (lval2, loc2) =
    let alarms =
      if Loc.partially_overlap loc1 loc2
      then Alarmset.singleton (Alarms.Overlap (lval1, lval2))
      else Alarmset.none
    in
    let size1 = Loc.size loc1
    and size2 = Loc.size loc2 in
    let compatible_locations =
      Int_Base.equal size1 size2 && not (Int_Base.is_top size1)
    in
    `Value compatible_locations, alarms

end


(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
