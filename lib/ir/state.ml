open Z3utils
module ControlFile = Control.ControlFile

module Params = struct
  module Param = struct
    type t = BitVec.t

    (* paramater id *)
    let init pid = Value.init pid |> Value.set_defined
  end

  type t = Param.t list

  let init nparams =
    let rec mk_param cnt params =
      if cnt == nparams then params
      else
        mk_param (cnt + 1) (Param.init ("p" ^ (cnt |> string_of_int)) :: params)
    in
    mk_param 0 []
end

type t = {
  pc : IR.Node.id;
  control_file : Control.t ControlFile.C.t;
  register_file : Value.t RegisterFile.R.t;
  memory : Memory.t;
  params : BitVec.t list;
  retvar : BitVec.t Option.t;
  assertion : BitVec.t;
  ub : Bool.t;
}

let init nparams stage : t =
  {
    pc = 0;
    control_file = ControlFile.init stage;
    register_file = RegisterFile.init stage;
    params = Params.init nparams;
    retvar = None;
    assertion = Bool.tr;
    memory = Memory.init ("mem_" ^ stage);
    ub = Bool.fl;
  }

let update pc control_file register_file memory assertion ub t =
  { t with pc; control_file; register_file; memory; assertion; ub }

(* getter *)
let pc t = t.pc

let control_file t = t.control_file

let register_file t = t.register_file

let memory t = t.memory

let params t = t.params

let retvar t = t.retvar

let assertion t = t.assertion

let ub t = t.ub

let is_end t = t.pc = -1
