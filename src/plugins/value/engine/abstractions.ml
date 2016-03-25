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

(* Configuration of the abstract domain. *)

type config = {
  cvalue : bool;
  apron_oct : bool;
  apron_box : bool;
  polka_loose : bool;
  polka_strict : bool;
  polka_equalities : bool;
}

let configure () = {
  cvalue = Value_parameters.CvalueDomain.get ();
  apron_oct = Value_parameters.ApronOctagon.get ();
  apron_box = Value_parameters.ApronBox.get ();
  polka_loose = Value_parameters.PolkaLoose.get ();
  polka_strict = Value_parameters.PolkaStrict.get ();
  polka_equalities = Value_parameters.PolkaEqualities.get ();
}

let default_config = configure ()

module type Value = sig
  include Abstract_value.External
  val reduce : t -> t
end

module type S = sig
  module Val : Value
  module Loc : Abstract_location.External with type value = Val.t
                                           and type location = Precise_locs.precise_location
  module Dom : Abstract_domain.External with type value = Val.t
                                         and type location = Loc.location
end


module Val = struct
  include Main_values.CVal
  include Structure.Open (Structure.Key_Value) (Main_values.CVal)
end



(* Abstractions needed for the analysis: value, location and domain. *)
module type Abstract = sig
  module Val : Abstract_value.External
  module Loc : Abstract_location.Internal with type value = Val.t
                                           and type location = Precise_locs.precise_location
  module Dom : Abstract_domain.Internal with type value = Val.t
                                         and type location = Loc.location
end


let has_apron config =
  config.apron_oct || config.apron_box || config.polka_equalities
  || config.polka_loose || config.polka_strict

let add_value_abstraction value v =
  let module Value = (val value : Abstract_value.Internal) in
  let module V = (val v : Abstract_value.Internal) in
  (module Value_product.Make (Value) (V) : Abstract_value.Internal)

let open_value_abstraction value =
  let module Value = (val value : Abstract_value.Internal) in
  (module struct
    include Value
    include Structure.Open (Structure.Key_Value) (Value)
  end : Abstract_value.External)

let build_value config =
  let value = (module Main_values.CVal : Abstract_value.Internal) in
  let value =
    if has_apron config
    then add_value_abstraction value (module Main_values.Interval)
    else value
  in
  open_value_abstraction value

(* Builds a module conversion from a generic external value to a key. *)
module Convert
    (Value : Abstract_value.External)
    (K : sig type v val key : v Abstract_value.key end)
= struct
  type extended_value = Value.t
  type extended_location = Main_locations.PLoc.location

  let extend_val =
    let set = Value.set K.key in
    fun v -> set v Value.top

  let restrict_val = match Value.get K.key with
    | None -> assert false
    | Some get -> get

  let restrict_loc = fun x -> x
end

let default_root_abstraction =
  (module struct
    module Val = Val
    module Loc = Main_locations.PLoc
    module Dom = Cvalue_domain.State
  end : Abstract)

let build_root_abstraction config value =
  let module Val = (val value : Abstract_value.External) in
  let module K = struct
    type v = Cvalue.V.t
    let key = Main_values.cvalue_key
  end in
  let module Conv = Convert (Val) (K) in
  if config.cvalue
  then
    (module struct
      module Val = Val
      module Loc = Location_lift.Make (Main_locations.PLoc) (Conv)
      module Dom = Domain_lift.Make (Cvalue_domain.State) (Conv)
    end : Abstract)
  else
    (module struct
      module Val = Val
      module Loc = Location_lift.Make (Main_locations.PLoc) (Conv)
      module Dom = Unit_domain.Make (Val) (Loc)
    end : Abstract)

let add_apron_domain abstract apron =
  let module Abstract = (val abstract: Abstract) in
  let module K = struct
    type v = Main_values.Interval.t
    let key = Main_values.interval_key
  end in
  let module Conv = Convert (Abstract.Val) (K) in
  let module Apron = Domain_lift.Make ((val apron : Apron_domain.S)) (Conv) in
  (module struct
    module Val = Abstract.Val
    module Loc = Abstract.Loc
    module Dom = Domain_product.Make (Abstract.Val) (Abstract.Dom) (Apron)
  end : Abstract)

let add_apron_domain abstractions apron =
  Value_parameters.warning
    "The Apron domains binding is experimental.";
  if Apron_domain.ok
  then add_apron_domain abstractions apron
  else
    Value_parameters.abort
      "Apron domain requested but apron binding not available: analysis aborted."


let build_abstractions config =
  let value = build_value config in
  let abstractions =
    if not (has_apron config)
    then default_root_abstraction
    else build_root_abstraction config value
  in
  let abstractions =
    if config.apron_oct
    then add_apron_domain abstractions (module Apron_domain.Octagon)
    else abstractions
  in
  let abstractions =
    if config.apron_box
    then add_apron_domain abstractions (module Apron_domain.Box)
    else abstractions
  in
  let abstractions =
    if config.polka_loose
    then add_apron_domain abstractions (module Apron_domain.Polka_Loose)
    else abstractions
  in
  let abstractions =
    if config.polka_strict
    then add_apron_domain abstractions (module Apron_domain.Polka_Strict)
    else abstractions
  in
  let abstractions =
    if config.polka_equalities
    then add_apron_domain abstractions (module Apron_domain.Polka_Equalities)
    else abstractions
  in
  abstractions


(* Add the reduce function to the value module. *)
module Reduce (Value : Abstract_value.External) = struct

  include Value

  (* When the value abstraction contains both a cvalue and an interval
     component (coming currently from an Apron domain), reduce them from each
     other. If the Cvalue is not a scalar do nothing, because we do not
     currently use Apron for pointer offsets. *)
  let reduce =
    match Value.get Main_values.interval_key, Value.get Main_values.cvalue_key with
    | Some get_interval, Some get_cvalue ->
      begin
        let set_cvalue = Value.set Main_values.cvalue_key in
        let set_interval = Value.set Main_values.interval_key in
        fun t -> match get_interval t with
          | None -> t
          | Some ival ->
            let cvalue = get_cvalue t in
            try
              let ival' = Cvalue.V.project_ival cvalue in
              (match ival' with
               | Ival.Float _ -> raise Cvalue.V.Not_based_on_null
               | _ -> ());
              let reduced_ival = Ival.narrow ival ival' in
              let cvalue = Cvalue.V.inject_ival reduced_ival in
              set_interval (Some reduced_ival) (set_cvalue cvalue t)
            with Cvalue.V.Not_based_on_null -> t
      end
    | _, _ -> fun x -> x

end

let open_abstractions abstraction =
  let module Abstract = (val abstraction : Abstract) in
  let module Val = Reduce (Abstract.Val) in
  let module Loc = struct
    include Abstract.Loc
    include Structure.Open
        (Structure.Key_Location)
        (struct include Abstract.Loc type t = location end)
  end in
  let module Domain = struct
    include Abstract.Dom
    include Structure.Open (Structure.Key_Domain) (Abstract.Dom)
  end in
  (module struct
    module Val = Val
    module Loc = Loc
    module Dom = Domain
  end : S)


let make config =
  let abstractions = build_abstractions config in
  open_abstractions abstractions


(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
