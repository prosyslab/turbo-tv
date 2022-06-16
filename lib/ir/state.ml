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
      if cnt == nparams then List.rev params
      else
        mk_param (cnt + 1) (Param.init ("p" ^ (cnt |> string_of_int)) :: params)
    in
    mk_param 0 []

  let print_evaluated model t =
    Format.printf "Parameters: \n";
    List.iteri
      (fun idx param ->
        Format.printf "Parameter[%d]: %s\n" idx
          (Model.eval model param |> Expr.to_string))
      t;
    Format.printf "\n"
end

type t = {
  stage : string;
  pc : IR.Node.id;
  next_bid : int;
  control_file : Control.t ControlFile.C.t;
  register_file : Value.t RegisterFile.R.t;
  memory : Memory.t;
  params : BitVec.t list;
  retvar : BitVec.t Option.t;
  assertion : BitVec.t;
  ub : Bool.t;
}

let init nparams stage : t =
  let params = Params.init nparams in
  let rec allocate_mem_for_parmas params memory =
    match params with
    | param :: rest ->
        let c =
          BitVec.init ~len:(8 * 12)
            (Format.sprintf "mem_for_%s" (param |> Expr.to_string))
        in
        allocate_mem_for_parmas rest
          (Bool.ite
             (Value.has_type Type.tagged_pointer param)
             (Memory.store param 12 Bool.tr c memory)
             memory)
    | _ -> memory
  in
  let memory = allocate_mem_for_parmas params (Memory.init ("mem_" ^ stage)) in

  {
    stage;
    pc = 0;
    next_bid = 0;
    control_file = ControlFile.init stage;
    register_file = RegisterFile.init stage;
    memory;
    params;
    retvar = None;
    assertion = Bool.tr;
    ub = Bool.fl;
  }

let update pc next_bid control_file register_file memory assertion ub t =
  { t with pc; next_bid; control_file; register_file; memory; assertion; ub }

(* getter *)
let pc t = t.pc

let control_file t = t.control_file

let register_file t = t.register_file

let next_bid t = t.next_bid

let memory t = t.memory

let params t = t.params

let stage t = t.stage

let retvar t = t.retvar

let assertion t = t.assertion

let ub t = t.ub

let is_end t = t.pc = -1
