open Z3utils
module DeoptFile = ExprMap.Make (Deopt)
module UBFile = ExprMap.Make (Ub)

module Params = struct
  module Param = struct
    type t = BitVec.t

    (* paramater id *)
    let init pid = Value.init pid
  end

  type t = Param.t list

  let init nparams =
    let rec mk_param cnt params =
      if cnt == nparams then List.rev params
      else
        mk_param (cnt + 1) (Param.init ("p" ^ (cnt |> string_of_int)) :: params)
    in
    mk_param 0 []
end

type t = {
  stage : string;
  pc : IR.Node.id;
  final : bool;
  next_bid : int;
  register_file : RegisterFile.t;
  control_file : ControlFile.t;
  ub_file : UBFile.t;
  deopt_file : DeoptFile.t;
  memory : Memory.t;
  params : BitVec.t list;
  retval : BitVec.t;
  ub : Bool.t;
  assertion : BitVec.t;
  deopt : Bool.t;
}

let init nparams stage : t =
  {
    stage;
    pc = 0;
    final = false;
    next_bid = nparams;
    register_file = RegisterFile.init stage RegisterFile.symbol;
    control_file = ControlFile.init stage ControlFile.symbol;
    ub_file = UBFile.init stage Ub.symbol;
    deopt_file = DeoptFile.init stage Deopt.symbol;
    memory = Memory.init "mem";
    params = Params.init nparams;
    retval = Value.empty;
    ub = Bool.fl;
    assertion = Bool.tr;
    deopt = Bool.fl;
  }

(* getter *)
let stage t = t.stage

let pc t = t.pc

let next_bid t = t.next_bid

let register_file t = t.register_file

let control_file t = t.control_file

let ub_file t = t.ub_file

let deopt_file t = t.deopt_file

let memory t = t.memory

let params t = t.params

let ub t = t.ub

let retval t = t.retval

let assertion t = t.assertion

let deopt t = t.deopt

let value_of id t = RegisterFile.find id (register_file t)

let control_of id t = ControlFile.find id (control_file t)

let ub_of id t = UBFile.find id (ub_file t)

let deopt_of id t = DeoptFile.find id (deopt_file t)

let output_of id t = (value_of id t, control_of id t, ub_of id t, deopt_of id t)

let update ?value ?mem ?control ?ub ?deopt ?next_bid ?(final = false) t =
  let pc = t.pc |> string_of_int in
  let register_file = RegisterFile.add pc value (register_file t) in
  let control_file = ControlFile.add pc control (control_file t) in
  let ub_file = UBFile.add pc ub (ub_file t) in
  let deopt_file = DeoptFile.add pc deopt (deopt_file t) in
  {
    t with
    register_file;
    memory = (match mem with Some mem -> mem | None -> t.memory);
    next_bid =
      (match next_bid with Some next_bid -> next_bid | None -> t.next_bid);
    control_file;
    ub_file;
    deopt_file;
    final = t.final || final;
  }

let is_final t = t.final

let finalize t =
  let pc = pc t |> string_of_int in
  let retval = value_of pc t in
  let ub = ub_of pc t in
  let deopt = deopt_of pc t in
  { t with retval; ub; deopt }
