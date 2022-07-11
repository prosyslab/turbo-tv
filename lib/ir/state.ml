open Z3utils
module ControlFile = Control.ControlFile

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
  memory : Memory.t;
  params : BitVec.t list;
  retval : BitVec.t;
  assertion : BitVec.t;
  ub : Bool.t;
  deopt : Bool.t;
}

let init nparams stage : t =
  {
    stage;
    pc = 0;
    next_bid = 0;
    control_file = ControlFile.init stage;
    register_file = RegisterFile.init stage;
    memory = Memory.init "mem";
    params = Params.init nparams;
    retval = Value.empty;
    assertion = Bool.tr;
    ub = Bool.fl;
    deopt = Bool.fl;
  }

let update pc next_bid control_file register_file memory assertion ub deopt t =
  {
    t with
    pc;
    next_bid;
    control_file;
    register_file;
    memory;
    assertion;
    ub;
    deopt;
  }

(* getter *)
let pc t = t.pc

let control_file t = t.control_file

let register_file t = t.register_file

let next_bid t = t.next_bid

let memory t = t.memory

let params t = t.params

let stage t = t.stage

let retval t = t.retval

let assertion t = t.assertion

let ub t = t.ub

let deopt t = t.deopt

let is_end t = t.pc = -1
