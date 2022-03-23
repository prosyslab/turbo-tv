open Z3utils

module Params = struct
  module Param = struct
    type t = BitVec.t

    (* paramater id *)
    let init pid = Value.init pid
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
  register_file : Value.t RegisterFile.R.t;
  condition : Bool.t;
  memory : Memory.t;
  params : BitVec.t list;
  retvar : BitVec.t Option.t;
  assertion : BitVec.t;
}

let init nparams stage : t =
  {
    pc = 0;
    register_file = RegisterFile.init stage;
    condition = Bool.tr;
    params = Params.init nparams;
    retvar = None;
    assertion = Bool.tr;
    memory = Memory.init ("mem_" ^ stage);
  }

let update pc register_file condition assertion t =
  { t with pc; register_file; condition; assertion }

(* getter *)
let pc t = t.pc
let register_file t = t.register_file
let condition t = t.condition
let memory t = t.memory
let params t = t.params
let retvar t = t.retvar
let assertion t = t.assertion
let is_final t = t.pc = -1
