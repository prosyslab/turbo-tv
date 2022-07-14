open Z3utils
module ControlFile = Control.ControlFile
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
  control_file : Control.t ControlFile.C.t;
  register_file : Value.t RegisterFile.R.t;
  ub_file : Bool.t UBFile.U.t;
  deopt_file : Bool.t DeoptFile.D.t;
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
    control_file = ControlFile.init stage;
    register_file = RegisterFile.init stage;
    ub_file = UBFile.init stage;
    deopt_file = DeoptFile.init stage;
    memory = Memory.init "mem";
    params = Params.init nparams;
    retval = Value.empty;
    ub = Bool.fl;
    assertion = Bool.tr;
    deopt = Bool.fl;
  }

let update pc next_bid control_file register_file ub_file deopt_file memory
    assertion t =
  {
    t with
    pc;
    next_bid;
    control_file;
    register_file;
    ub_file;
    deopt_file;
    memory;
    assertion;
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

let is_end t = t.pc = -1
