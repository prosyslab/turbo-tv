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
          (Model.eval model param false |> Option.get |> Expr.to_string))
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
  let next_bid = ref 0 in
  let embed_default_constants mem rf =
    let default_constants =
      [ "undefined"; "the_hole"; "null"; "empty_string"; "false"; "true" ]
    in
    List.fold_left
      (fun (mem, rf) name ->
        let ptr =
          Memory.allocate next_bid (BitVecVal.from_int ~len:Value.len 1)
        in
        let updated_mem =
          Memory.store ptr 1 Bool.tr (BitVecVal.from_int 0) mem
        in
        (updated_mem, RegisterFile.add name ptr rf))
      (mem, rf) default_constants
  in

  let empty_memory = Memory.init ("mem_" ^ stage) in
  let empty_register_file = RegisterFile.init stage in
  let memory, register_file =
    embed_default_constants empty_memory empty_register_file
  in

  {
    stage;
    pc = 0;
    next_bid = !next_bid;
    control_file = ControlFile.init stage;
    register_file;
    memory;
    params = Params.init nparams;
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
