open Err
open Z3utils

module Params = struct
  module Param = struct
    type t = BitVec.t

    (* paramater id *)
    let init pid = BitVec.init pid
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

module Value = struct
  type id = string

  type t = BitVec.t

  let empty = BitVecVal.zero 1 ()

  let to_string t = str_of_exp t

  (* constants *)
  let tylen = 5

  let datalen = 64

  let len = tylen + datalen

  let smilen = 31

  let smimask = 0xfffffffe

  let smimin = -1073741824

  let smimax = 1073741823

  (* type-constants *)
  let int8_ty = BitVecVal.of_int ~len:tylen 0

  let uint8_ty = BitVecVal.of_int ~len:tylen 1

  let int16_ty = BitVecVal.of_int ~len:tylen 2

  let uint16_ty = BitVecVal.of_int ~len:tylen 3

  let int32_ty = BitVecVal.of_int ~len:tylen 4

  let uint32_ty = BitVecVal.of_int ~len:tylen 5

  let int64_ty = BitVecVal.of_int ~len:tylen 6

  let uint64_ty = BitVecVal.of_int ~len:tylen 7

  let float32_ty = BitVecVal.of_int ~len:tylen 8

  let float64_ty = BitVecVal.of_int ~len:tylen 9

  let simd128_ty = BitVecVal.of_int ~len:tylen 10

  let pointer_ty = BitVecVal.of_int ~len:tylen 11

  let tagged_pointer_ty = BitVecVal.of_int ~len:tylen 12

  let map_in_header_ty = BitVecVal.of_int ~len:tylen 13

  let tagged_signed_ty = BitVecVal.of_int ~len:tylen 14

  let any_tagged_ty = BitVecVal.of_int ~len:tylen 15

  let compressed_pointer_ty = BitVecVal.of_int ~len:tylen 16

  let any_compressed_ty = BitVecVal.of_int ~len:tylen 17

  let sandboxed_pointer_ty = BitVecVal.of_int ~len:tylen 18

  let bool_ty = BitVecVal.of_int ~len:tylen 19

  let none_ty = BitVecVal.of_int ~len:tylen 20

  (* type-cast *)
  let cast_to_int32 data = BitVec.concat int32_ty data

  let cast_to_int64 data = BitVec.concat int64_ty data

  let cast_to_uint64 data = BitVec.concat uint64_ty data

  let cast_to_float64 data = BitVec.concat float64_ty data

  let cast_to_pointer data = BitVec.concat pointer_ty data

  let cast_to_tagged_signed data = BitVec.concat tagged_signed_ty data

  let cast_to_any_tagged data = BitVec.concat any_tagged_ty data

  let cast_to_bool data = BitVec.concat bool_ty data

  let cast_to_ty ty data = BitVec.concat ty data

  (* type vector of machine type *)
  let ty_of_machine_type (mt : MachineType.t) =
    match mt with
    | Int8 -> int8_ty
    | Uint8 -> uint8_ty
    | Int16 -> int16_ty
    | Uint16 -> uint16_ty
    | Int32 -> int32_ty
    | Uint32 -> uint32_ty
    | Int64 -> int64_ty
    | Uint64 -> uint64_ty
    | Float32 -> float32_ty
    | Float64 -> float64_ty
    | Simd128 -> simd128_ty
    | Pointer -> pointer_ty
    | TaggedSigned -> tagged_signed_ty
    | TaggedPointer -> tagged_pointer_ty
    | MapInHeader -> map_in_header_ty
    | AnyTagged -> any_tagged_ty
    | CompressedPointer -> compressed_pointer_ty
    | AnyCompressed -> any_compressed_ty
    | SandboxedPointer -> sandboxed_pointer_ty
    | Bool -> bool_ty
    | None -> none_ty

  (* getter *)
  let ty_of t = BitVec.extract (tylen - 1) 0 t

  let data_of t = BitVec.extract (len - 1) tylen t

  let first_of t = BitVec.extract (len - 1) 0 t

  let second_of t = BitVec.extract ((2 * len) - 1) len t

  (* type check *)

  let is_int8 value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty int8_ty

  let is_uint8 value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty uint8_ty

  let is_int16 value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty int16_ty

  let is_uint16 value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty uint16_ty

  let is_word8 value = Bool.ors [ is_int8 value; is_uint8 value ]

  let is_word16 value = Bool.ors [ is_int16 value; is_uint16 value ]

  let is_int32 value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty int32_ty

  let is_uint32 value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty uint32_ty

  let is_word32 value = Bool.ors [ is_int32 value; is_uint32 value ]

  let is_int64 value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty int64_ty

  let is_uint64 value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty uint64_ty

  let is_pointer value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty pointer_ty

  let is_word64 value =
    Bool.ors [ is_int64 value; is_uint64 value; is_pointer value ]

  let is_float32 value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty float32_ty

  let is_float64 value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty float64_ty

  let is_word value =
    Bool.ors
      [ is_word8 value; is_word16 value; is_word32 value; is_word64 value ]

  let is_any_tagged value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty any_tagged_ty

  let is_tagged_signed value =
    let value_ty = ty_of value in
    Bool.ands
      [
        BitVec.eqb value_ty tagged_signed_ty; BitVec.eqi (BitVec.andi value 1) 1;
      ]

  let is_tagged_pointer value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty tagged_pointer_ty

  let is_number value = Bool.ors [ is_float32 value; is_float64 value ]

  let is_type_of value ty =
    let value_ty = ty_of value in
    BitVec.eqb value_ty ty

  let can_be_smi bv = Bool.ands [ BitVec.sgei bv smimin; BitVec.slti bv smimax ]

  (* conversion *)
  let smi_to_int31 data = BitVec.extract 31 1 data

  (* comparison *)
  (* lty = rty && ldata = rdata *)
  let is_equal lval rval = BitVec.eqb lval rval

  (* ldata = rdata *)
  let is_weak_equal lval rval =
    let ldata = data_of lval in
    let rdata = data_of rval in
    BitVec.eqb ldata rdata

  (* common: constants *)
  let int32_constant vid c =
    let value = BitVec.init ~len vid in
    let cval = cast_to_int32 (BitVecVal.of_str c) in
    let assertion = Bool.ands [ is_equal value cval ] in
    (value, assertion)

  let int64_constant vid c =
    let value = BitVec.init ~len vid in
    let cval = cast_to_int64 (BitVecVal.of_str c) in
    let assertion = Bool.ands [ is_equal value cval ] in
    (value, assertion)

  let external_constant vid c =
    let value = BitVec.init ~len vid in
    let cval = cast_to_pointer (BitVecVal.of_str c) in
    let assertion = Bool.ands [ is_equal value cval ] in
    (value, assertion)

  let heap_constant = external_constant

  let number_constant vid c =
    let value = BitVec.init ~len vid in
    let cbv = BitVecVal.of_str c in

    let c_is_smi =
      Bool.ands [ can_be_smi cbv; is_equal value (cast_to_tagged_signed cbv) ]
    in

    let c_is_not_smi =
      Bool.ands
        [ Bool.not (can_be_smi cbv); is_equal value (cast_to_any_tagged cbv) ]
    in

    let assertion = Bool.ors [ c_is_smi; c_is_not_smi ] in
    (value, assertion)

  (* common: control *)
  let projection vid pidx pval =
    let value = BitVec.init ~len vid in

    let res =
      if pidx = 0 then BitVec.extract (len - 1) 0 pval
      else if pidx = 1 then BitVec.extract ((2 * len) - 1) len pval
      else raise (Invalid_argument "Projection index out of range")
    in

    let assertion = is_equal value res in

    (value, assertion)

  (* common: procedure *)
  let parameter vid param =
    let value = BitVec.init ~len vid in
    let assertion = BitVec.eqb value (cast_to_tagged_signed param) in
    (value, assertion)

  let return _vid _pval = failwith "Not implemented"

  (* simplified: arithmetic *)
  let speculative_safe_integer_add vid lval rval =
    let value = BitVec.init ~len vid in
    let ldata = data_of lval in
    let rdata = data_of rval in

    let res =
      BitVec.andi (BitVec.addb ldata rdata) smimask |> cast_to_tagged_signed
    in

    let assertion =
      Bool.ands
        [ is_tagged_signed lval; is_tagged_signed rval; is_equal value res ]
    in

    (value, assertion)

  (* simplified: memory *)
  let allocate_raw vid size mem =
    let value = BitVec.init ~len vid in
    let bid, updated = Memory.allocate size !mem in
    mem := updated;

    let bid = BitVecVal.of_int bid |> cast_to_pointer in
    let assertion = Bool.ands [ is_equal value bid ] in

    (value, assertion)

  let store_field bid_val pos mt value_val mem =
    let bid =
      data_of bid_val |> Z3.BitVector.numeral_to_string |> int_of_string
    in
    let ty = ty_of_machine_type mt in
    let size = MachineType.size_of mt in
    let value = data_of value_val in

    (if pos < 0 || pos + size >= Memory.size bid mem then
     let cause = pos |> string_of_int in
     let reason =
       Format.sprintf "Out of bounds: 0 <= pos ^ pos+size <= %s"
         (Memory.size bid mem |> string_of_int)
     in
     err (InvalidIndex (cause, reason)));

    let assertion =
      Bool.ands
        [
          is_pointer bid_val;
          is_type_of value_val ty;
          Memory.write bid pos size value mem;
        ]
    in

    (empty, assertion)

  (* simplified: type-conversion *)
  let change_int32_to_tagged vid pval mem =
    let value = BitVec.init ~len vid in
    let pdata = data_of pval in
    let ovf = BitVec.ugei (BitVec.addb pdata pdata) smimax in

    let if_ovf =
      let bid, updated = Memory.allocate 12 !mem in
      (* TODO: Define map constants *)
      let heap_number_map = BitVecVal.of_int ~len:32 1234 in
      mem := updated;
      Bool.ands
        [
          Memory.write bid 0 4 heap_number_map !mem;
          Memory.write bid 4 8 pdata !mem;
        ]
    in
    let if_not_ovf = is_equal value (cast_to_tagged_signed pdata) in

    let assertion = Bool.ite ovf if_ovf if_not_ovf in
    (value, assertion)

  let change_int32_to_float64 vid pval =
    let value = BitVec.init ~len vid in
    let pdata = data_of pval in

    let assertion =
      Bool.ands [ is_int32 pval; is_equal value (cast_to_tagged_signed pdata) ]
    in
    (value, assertion)

  let checked_tagged_signed_to_int32 vid pval =
    let value = BitVec.init ~len vid in
    let pdata = data_of pval in

    (* TODO: handling deoptimization *)
    (* let deopt = Bool.not (is_tagged_signed pval) in *)
    let assertion =
      Bool.ands [ is_tagged_signed pval; is_equal value (cast_to_int32 pdata) ]
    in

    (value, assertion)

  (* machine: arithmetic *)
  (* value = (lval + rval) mod 2^32 *)
  let int32add vid lval rval =
    let value = BitVec.init ~len vid in
    let ldata = data_of lval in
    let rdata = data_of rval in
    let res = BitVec.andi (BitVec.addb ldata rdata) smimask |> cast_to_int32 in

    let assertion =
      Bool.ands [ is_int32 lval; is_int32 rval; is_equal value res ]
    in

    (value, assertion)

  let int32add_with_overflow vid lval rval =
    let value = BitVec.init ~len:(len * 2) vid in

    let ldata = data_of lval in
    let rdata = data_of rval in
    let res = BitVec.andi (BitVec.addb ldata rdata) smimask |> cast_to_int32 in
    let ovf = BitVec.ulti (BitVec.addb ldata rdata) smimax |> cast_to_bool in

    let assertion =
      Bool.ands
        [
          is_int32 lval;
          is_int32 rval;
          is_equal (second_of value) ovf;
          is_equal (first_of value) res;
        ]
    in

    (value, assertion)

  (* var = (lval + rval) mod 2^64 *)
  let int64add vid lval rval =
    let value = BitVec.init ~len vid in

    let ldata = data_of lval in
    let rdata = data_of rval in
    let res = BitVec.addb ldata rdata |> cast_to_int64 in

    let assertion =
      Bool.ands [ is_int64 lval; is_int64 rval; is_equal value res ]
    in

    (value, assertion)

  let int64sub vid lval rval =
    let value = BitVec.init ~len vid in

    let ldata = data_of lval in
    let rdata = data_of rval in
    let res = BitVec.subb ldata rdata |> cast_to_int64 in

    let assertion =
      Bool.ands [ is_int64 lval; is_int64 rval; is_equal value res ]
    in

    (value, assertion)

  let word32sar vid hint lval rval =
    let value = BitVec.init ~len vid in

    let is_shift_out_zero =
      if String.equal hint "ShfitOutZero" then BitVecVal.tr ()
      else BitVecVal.fl ()
    in

    let ldata = data_of lval in
    let rdata = data_of rval in
    let lval_ty = ty_of lval in

    let res =
      BitVec.andi (BitVec.ashrb ldata rdata) smimask |> cast_to_ty lval_ty
    in

    let assertion =
      Bool.ands
        [
          is_word32 lval;
          is_word32 rval;
          is_equal value res;
          Bool.ors
            [
              Bool.not is_shift_out_zero;
              (* TODO: undef *)
              is_weak_equal res (BitVecVal.zero len ());
            ];
        ]
    in
    (value, assertion)

  (* machine: comparison *)
  let word32equal vid lval rval =
    let value = BitVec.init ~len vid in

    let ldata = data_of lval in
    let rdata = data_of rval in
    let res = BitVec.eqb ldata rdata |> cast_to_bool in

    let assertion =
      Bool.ands [ is_word32 lval; is_word32 rval; is_equal value res ]
    in

    (value, assertion)

  let uint64less_than vid lval rval =
    let value = BitVec.init ~len vid in

    let ldata = data_of lval in
    let rdata = data_of rval in
    let res = BitVec.ultb ldata rdata |> cast_to_bool in

    let assertion =
      Bool.ands [ is_uint64 lval; is_uint64 rval; is_equal value res ]
    in

    (value, assertion)

  (* machine: memory *)
  let store bid_val pos_val repr value_val mem =
    let bid =
      data_of bid_val |> Z3.BitVector.numeral_to_string |> int_of_string
    in

    (* at this point, pos must be able to be evaluated into numeral*)
    let pos =
      data_of pos_val |> simplify None |> Z3.BitVector.numeral_to_string
      |> int_of_string
    in
    let size = repr |> MachineType.Repr.size_of in
    let value = data_of value_val in

    let assertion =
      Bool.ands [ is_pointer bid_val; Memory.write bid pos size value mem ]
    in

    (empty, assertion)

  let load vid bid_val pos_val repr mem =
    let value = BitVec.init ~len vid in
    let bid =
      data_of bid_val |> Z3.BitVector.numeral_to_string |> int_of_string
    in

    (* at this point, pos must be able to be evaluated into numeral*)
    let pos =
      data_of pos_val |> simplify None |> Z3.BitVector.numeral_to_string
      |> int_of_string
    in
    let size = repr |> MachineType.Repr.size_of in

    let assertion =
      Bool.ands
        [ is_pointer bid_val; BitVec.eqb value (Memory.read bid pos size mem) ]
    in

    (value, assertion)

  (* machine: type-conversion *)
  let bitcast_tagged_to_word vid pval =
    let value = BitVec.init ~len vid in
    let pdata = data_of pval in
    let assertion =
      Bool.ands [ is_any_tagged pval; is_equal value (cast_to_uint64 pdata) ]
    in

    (value, assertion)

  let bitcast_word32_to_word64 vid pval =
    let value = BitVec.init ~len vid in
    let pdata = data_of pval in
    let assertion =
      Bool.ands [ is_word32 pval; is_equal value (cast_to_uint64 pdata) ]
    in

    (value, assertion)

  let bitcast_word_to_tagged vid pval =
    let value = BitVec.init ~len vid in
    let pdata = data_of pval in
    let assertion =
      Bool.ands [ is_word pval; is_equal value (cast_to_any_tagged pdata) ]
    in
    (value, assertion)

  let truncate_int64_to_int32 vid pval =
    let value = BitVec.init ~len vid in
    let pdata = data_of pval in
    let assertion =
      Bool.ands [ is_int64 pval; is_equal value (cast_to_int32 pdata) ]
    in
    (value, assertion)
end

module RegisterFile = struct
  module R = Map.Make (String)

  let add = R.add

  let find vid rf =
    try R.find vid rf
    with Not_found ->
      let cause = vid in
      let reason = Format.sprintf "Cannot find %s from RegisterFile" cause in
      err (IdNotFound (cause, reason))

  let empty = R.empty

  let iter = R.iter
end

module State = struct
  type t = {
    pc : IR.Node.id;
    register_file : Value.t RegisterFile.R.t;
    memory : BitVec.t Memory.M.t;
    params : BitVec.t list;
    retvar : BitVec.t Option.t;
    assertion : BitVec.t;
  }

  let init nparams : t =
    {
      pc = 0;
      register_file = RegisterFile.empty;
      params = Params.init nparams;
      retvar = None;
      assertion = Bool.tr;
      memory = Memory.empty;
    }

  let update pc register_file assertion t =
    { t with pc; register_file; assertion }

  (* getter *)
  let pc t = t.pc

  let register_file t = t.register_file

  let memory t = t.memory

  let params t = t.params

  let retvar t = t.retvar

  let assertion t = t.assertion

  let is_final t = t.pc = -1
end

(* apply semantics to create SMT query *)
let apply program state prefix =
  let pc = State.pc state in
  let rf = State.register_file state in
  let mem = ref (State.memory state) in
  let params = State.params state in
  let vid = prefix ^ string_of_int pc in

  let opcode, operands = IR.instr_of pc program in
  let next_pc = match opcode with Return -> -1 | _ -> pc + 1 in

  let value, assertion =
    match opcode with
    (* common: constants *)
    | HeapConstant | ExternalConstant ->
        let addr_re = Re.Pcre.regexp "(0x[0-9a-f]*)" in
        let operand = Operands.const_of_nth operands 0 in
        Re.Group.get (Re.exec addr_re operand) 1 |> Value.heap_constant vid
    | Int32Constant ->
        Operands.const_of_nth operands 0 |> Value.int32_constant vid
    | Int64Constant ->
        Operands.const_of_nth operands 0 |> Value.int64_constant vid
    | NumberConstant ->
        Operands.const_of_nth operands 0 |> Value.number_constant vid
    (* common: control *)
    | Branch -> failwith "Not implemented"
    | Projection ->
        let pidx = Operands.const_of_nth operands 0 |> int_of_string in
        let pid = prefix ^ Operands.id_of_nth operands 1 in
        let pval = RegisterFile.find pid rf in
        Value.projection vid pidx pval
    (* common: procedure *)
    | Parameter ->
        let pidx = Operands.const_of_nth operands 0 |> int_of_string in
        if 0 < pidx && pidx <= List.length params then
          let param = List.nth params (pidx - 1) in
          Value.parameter vid param
        else (Value.empty, Bool.tr)
    | Return | Call | End -> (Value.empty, Bool.tr)
    (* simplified: arithmetic *)
    | SpeculativeSafeIntegerAdd ->
        let lpid = prefix ^ Operands.id_of_nth operands 0 in
        let rpid = prefix ^ Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        Value.speculative_safe_integer_add vid lval rval
    (* simplified: memory *)
    | AllocateRaw ->
        let size = Operands.const_of_nth operands 0 |> int_of_string in
        Value.allocate_raw vid size mem
    | StoreField ->
        let nbid = prefix ^ Operands.id_of_nth operands 0 in
        let bid_val = RegisterFile.find nbid rf in
        let pos = Operands.const_of_nth operands 1 |> int_of_string in
        let machine_type =
          Operands.const_of_nth operands 2 |> MachineType.of_rs_string
        in
        let nvalue = prefix ^ Operands.id_of_nth operands 3 in
        let value_val = RegisterFile.find nvalue rf in
        Value.store_field bid_val pos machine_type value_val !mem
    (* simplified: type-conversion *)
    | ChangeInt32ToTagged ->
        let pid = prefix ^ Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        Value.change_int32_to_tagged vid pval mem
    | ChangeInt32ToFloat64 ->
        let pid = prefix ^ Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        Value.change_int32_to_float64 vid pval
    | CheckedTaggedSignedToInt32 ->
        let pid = prefix ^ Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        Value.checked_tagged_signed_to_int32 vid pval
    (* machine: arithmetic *)
    | Int32Add ->
        let lpid = prefix ^ Operands.id_of_nth operands 0 in
        let rpid = prefix ^ Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        Value.int32add vid lval rval
    | Int32AddWithOverflow ->
        let lpid = prefix ^ Operands.id_of_nth operands 0 in
        let rpid = prefix ^ Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        Value.int32add_with_overflow vid lval rval
    | Int64Add ->
        let lpid = prefix ^ Operands.id_of_nth operands 0 in
        let rpid = prefix ^ Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        Value.int64add vid lval rval
    | Int64Sub ->
        let lpid = prefix ^ Operands.id_of_nth operands 0 in
        let rpid = prefix ^ Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        Value.int64sub vid lval rval
    | Word32Sar ->
        let hint = Operands.const_of_nth operands 0 in
        let lpid = prefix ^ Operands.id_of_nth operands 1 in
        let rpid = prefix ^ Operands.id_of_nth operands 2 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        Value.word32sar vid hint lval rval
    (* machine: comparison *)
    | StackPointerGreaterThan -> (Value.empty, Bool.tr)
    | Word32Equal ->
        let lpid = prefix ^ Operands.id_of_nth operands 0 in
        let rpid = prefix ^ Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        Value.word32equal vid lval rval
    | Uint64LessThan ->
        let lpid = prefix ^ Operands.id_of_nth operands 0 in
        let rpid = prefix ^ Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        Value.uint64less_than vid lval rval
    (* machine: memory *)
    | Store ->
        let nbid = prefix ^ Operands.id_of_nth operands 0 in
        let bid_val = RegisterFile.find nbid rf in
        let npos = prefix ^ Operands.id_of_nth operands 1 in
        let pos_val = RegisterFile.find npos rf in
        let repr =
          Operands.const_of_nth operands 2 |> MachineType.Repr.of_string
        in
        let nvalue = prefix ^ Operands.id_of_nth operands 3 in
        let value_val = RegisterFile.find nvalue rf in
        Value.store bid_val pos_val repr value_val !mem
    | Load ->
        let nbid = prefix ^ Operands.id_of_nth operands 0 in
        let bid_val = RegisterFile.find nbid rf in
        let npos = prefix ^ Operands.id_of_nth operands 1 in
        let pos_val = RegisterFile.find npos rf in
        let repr =
          Operands.const_of_nth operands 2 |> MachineType.Repr.of_string
        in
        Value.load vid bid_val pos_val repr !mem
    (* machine: bitcast *)
    | BitcastTaggedToWord ->
        let pid = prefix ^ Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        Value.bitcast_tagged_to_word vid pval
    | BitcastWord32ToWord64 ->
        let pid = prefix ^ Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        Value.bitcast_word32_to_word64 vid pval
    | BitcastWordToTagged ->
        let pid = prefix ^ Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        Value.bitcast_word_to_tagged vid pval
    | TruncateInt64ToInt32 ->
        let pid = prefix ^ Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        Value.truncate_int64_to_int32 vid pval
    | Empty -> (Value.empty, Bool.tr)
    | _ -> (Value.empty, Bool.tr)
  in
  let updated_rf = RegisterFile.add vid value rf in

  let updated_asrt = Bool.and_ (State.assertion state) assertion in
  let next_state = State.update next_pc updated_rf updated_asrt state in

  if State.is_final next_state then
    { next_state with retvar = Option.some (BitVec.init ~len:Value.len vid) }
  else next_state
