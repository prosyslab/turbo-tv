open Z3utils
module DeoptFile = Deopt.DeoptFile
module UBFile = Ub.UBFile

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
  next_bid : int;
  control_file : ControlFile.t;
  register_file : RegisterFile.t;
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
    next_bid = 0;
    control_file = ControlFile.init stage ControlFile.symbol;
    register_file = RegisterFile.init stage RegisterFile.symbol;
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

let control_file t = t.control_file

let register_file t = t.register_file

let ub_file t = t.ub_file

let deopt_file t = t.deopt_file

let memory t = t.memory

let params t = t.params

let ub t = t.ub

let retval t = t.retval

let assertion t = t.assertion

let deopt t = t.deopt

let update ?value ?control ?ub ?deopt t =
  let pc = pc t |> string_of_int in
  let register_file = RegisterFile.add pc value (register_file t) in
  let control_file = ControlFile.add pc control (control_file t) in
  let ub_file = UBFile.add pc ub (ub_file t) in
  let deopt_file = DeoptFile.add pc deopt (deopt_file t) in
  { t with register_file; control_file; ub_file; deopt_file }

let is_end t = t.pc = -1
