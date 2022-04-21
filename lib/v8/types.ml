open Err

type t =
  (* Internal Bitset Type List *)
  | OtherUnsigned31
  | OtherUnsigned32
  | OtherSigned32
  | OtherNumber
  | OtherString
  (* Proper Atomic Bitset Type Low List *)
  | Negative31
  | Null
  | Undefined
  | Boolean
  | Unsigned30
  | MinusZero
  | NaN
  | Symbol
  | InternalizedString
  | OtherCallable
  | OtherObject
  | OtherUndetectable
  | CallableProxy
  | OtherProxy
  | CallableFunction
  | ClassConstructor
  | BoundFunction
  | Hole
  | OtherInternal
  | ExternalPointer
  | Array
  | UnsignedBigInt63
  | OtherUnsignedBigInt64
  | NegativeBigInt63
  | OtherBigInt
  | WasmObject
  (* Proper Atomic Bitset Type High List *)
  | SandboxedPointer
  (* Proper Bitset Type List *)
  | None
  | Signed31
  | Signed32
  | Signed32OrMinusZero
  | Signed32OrMinusZeroOrNaN
  | Negative32
  | Unsigned31
  | Unsigned32
  | Unsigned32OrMinusZero
  | Unsigned32OrMinusZeroOrNaN
  | Integral32
  | Integral32OrMinusZero
  | Integral32OrMinusZeroOrNaN
  | PlainNumber
  | OrderedNumber
  | MinusZeroOrNaN
  | Number
  | SignedBigInt64
  | UnsignedBigInt64
  | BigInt
  | Numeric
  | String
  | UniqueName
  | Name
  | InternalizedStringOrNull
  | BooleanOrNumber
  | BooleanOrNullOrNumber
  | BooleanOrNullOrUndefined
  | Oddball
  | NullOrNumber
  | NullOrUndefined
  | Undetectable
  | NumberOrHole
  | NumberOrOddball
  | NumericOrString
  | NumberOrUndefined
  | NumberOrUndefinedOrNullOrBoolean
  | PlainPrimitive
  | NonBigIntPrimitive
  | Primitive
  | OtherUndetectableOrUndefined
  | Proxy
  | ArrayOrOtherObject
  | ArrayOrProxy
  | Function
  | DetectableCallable
  | Callable
  | NonCallable
  | NonCallableOrNull
  | DetectableObject
  | DetectableReceiver
  | DetectableReceiverOrNull
  | Object
  | Receiver
  | ReceiverOrUndefined
  | ReceiverOrNullOrUndefined
  | SymbolOrReceiver
  | StringOrReceiver
  | Unique
  | Internal
  | NonInternal
  | NonBigInt
  | NonNumber
  | Any
  | HeapConstant of int
  | OtherNumberConstant of int
  | Tuple of t list
  | Union of t list
  | Range of (float * float)

let rec of_string str =
  let parse_structural kind s_ty_str =
    let tys_reg = Re.Pcre.regexp "Union\\(([^\\)]*)\\)" in
    let elems_ty_str =
      try Re.Group.get (Re.exec tys_reg s_ty_str) 1 |> String.split_on_char ','
      with Not_found ->
        let cause = s_ty_str in
        let reason = "Cannot parse '" ^ kind ^ "' from the " ^ s_ty_str in
        raise (InvalidFormat (cause, reason))
    in
    let elems_ty = List.map of_string elems_ty_str in

    match kind with
    | "Union" -> Union elems_ty
    | "Tuple" -> Tuple elems_ty
    | _ -> failwith "Unreachable"
  in

  let parse_constant kind c_ty_str =
    let value_reg = Re.Pcre.regexp (kind ^ "\\((0x[0-9a-f]*).*") in
    let value_str =
      try Re.Group.get (Re.exec value_reg c_ty_str) 1
      with Not_found ->
        let cause = c_ty_str in
        let reason = "Cannot parse '" ^ kind ^ "' from the " ^ c_ty_str in
        raise (InvalidFormat (cause, reason))
    in
    let value = value_str |> int_of_string in
    match kind with
    | "HeapConstant" -> HeapConstant value
    | "OtherNumberConstant" -> OtherNumberConstant value
    | _ -> failwith "Unreachable"
  in

  let parse_range range_ty_str =
    let limits_reg =
      Re.Pcre.regexp "Range\\((-?[\\.0-9]*),\\s*(-?[\\.0-9]*)\\)"
    in
    let limits =
      try
        let lb =
          Re.Group.get (Re.exec limits_reg range_ty_str) 1 |> float_of_string
        in
        let ub =
          Re.Group.get (Re.exec limits_reg range_ty_str) 2 |> float_of_string
        in
        (lb, ub)
      with Not_found ->
        let cause = range_ty_str in
        let reason = "Cannot parse 'Range' from the " ^ range_ty_str in
        raise (InvalidFormat (cause, reason))
    in
    Range limits
  in

  match str with
  | "OtherUnsigned31" -> OtherUnsigned31
  | "OtherUnsigned32" -> OtherUnsigned32
  | "OtherSigned32" -> OtherSigned32
  | "OtherNumber" -> OtherNumber
  | "OtherString" -> OtherString
  | "Negative31" -> Negative31
  | "Null" -> Null
  | "Undefined" -> Undefined
  | "Boolean" -> Boolean
  | "Unsigned30" -> Unsigned30
  | "MinusZero" -> MinusZero
  | "NaN" -> NaN
  | "Symbol" -> Symbol
  | "InternalizedString" -> InternalizedString
  | "OtherCallable" -> OtherCallable
  | "OtherObject" -> OtherObject
  | "OtherUndetectable" -> OtherUndetectable
  | "CallableProxy" -> CallableProxy
  | "OtherProxy" -> OtherProxy
  | "CallableFunction" -> CallableFunction
  | "ClassConstructor" -> ClassConstructor
  | "BoundFunction" -> BoundFunction
  | "Hole" -> Hole
  | "OtherInternal" -> OtherInternal
  | "ExternalPointer" -> ExternalPointer
  | "Array" -> Array
  | "UnsignedBigInt63" -> UnsignedBigInt63
  | "OtherUnsignedBigInt64" -> OtherUnsignedBigInt64
  | "NegativeBigInt63" -> NegativeBigInt63
  | "OtherBigInt" -> OtherBigInt
  | "WasmObject" -> WasmObject
  | "SandboxedPointer" -> SandboxedPointer
  | "None" -> None
  | "Signed31" -> Signed31
  | "Signed32" -> Signed32
  | "Signed32OrMinusZero" -> Signed32OrMinusZero
  | "Signed32OrMinusZeroOrNaN" -> Signed32OrMinusZeroOrNaN
  | "Negative32" -> Negative32
  | "Unsigned31" -> Unsigned31
  | "Unsigned32" -> Unsigned32
  | "Unsigned32OrMinusZero" -> Unsigned32OrMinusZero
  | "Unsigned32OrMinusZeroOrNaN" -> Unsigned32OrMinusZeroOrNaN
  | "Integral32" -> Integral32
  | "Integral32OrMinusZero" -> Integral32OrMinusZero
  | "Integral32OrMinusZeroOrNaN" -> Integral32OrMinusZeroOrNaN
  | "PlainNumber" -> PlainNumber
  | "OrderedNumber" -> OrderedNumber
  | "MinusZeroOrNaN" -> MinusZeroOrNaN
  | "Number" -> Number
  | "SignedBigInt64" -> SignedBigInt64
  | "UnsignedBigInt64" -> UnsignedBigInt64
  | "BigInt" -> BigInt
  | "Numeric" -> Numeric
  | "String" -> String
  | "UniqueName" -> UniqueName
  | "Name" -> Name
  | "InternalizedStringOrNull" -> InternalizedStringOrNull
  | "BooleanOrNumber" -> BooleanOrNumber
  | "BooleanOrNullOrNumber" -> BooleanOrNullOrNumber
  | "BooleanOrNullOrUndefined" -> BooleanOrNullOrUndefined
  | "Oddball" -> Oddball
  | "NullOrNumber" -> NullOrNumber
  | "NullOrUndefined" -> NullOrUndefined
  | "Undetectable" -> Undetectable
  | "NumberOrHole" -> NumberOrHole
  | "NumberOrOddball" -> NumberOrOddball
  | "NumericOrString" -> NumericOrString
  | "NumberOrUndefined" -> NumberOrUndefined
  | "NumberOrUndefinedOrNullOrBoolean" -> NumberOrUndefinedOrNullOrBoolean
  | "PlainPrimitive" -> PlainPrimitive
  | "NonBigIntPrimitive" -> NonBigIntPrimitive
  | "Primitive" -> Primitive
  | "OtherUndetectableOrUndefined" -> OtherUndetectableOrUndefined
  | "Proxy" -> Proxy
  | "ArrayOrOtherObject" -> ArrayOrOtherObject
  | "ArrayOrProxy" -> ArrayOrProxy
  | "Function" -> Function
  | "DetectableCallable" -> DetectableCallable
  | "Callable" -> Callable
  | "NonCallable" -> NonCallable
  | "NonCallableOrNull" -> NonCallableOrNull
  | "DetectableObject" -> DetectableObject
  | "DetectableReceiver" -> DetectableReceiver
  | "DetectableReceiverOrNull" -> DetectableReceiverOrNull
  | "Object" -> Object
  | "Receiver" -> Receiver
  | "ReceiverOrUndefined" -> ReceiverOrUndefined
  | "ReceiverOrNullOrUndefined" -> ReceiverOrNullOrUndefined
  | "SymbolOrReceiver" -> SymbolOrReceiver
  | "StringOrReceiver" -> StringOrReceiver
  | "Unique" -> Unique
  | "Internal" -> Internal
  | "NonInternal" -> NonInternal
  | "NonBigInt" -> NonBigInt
  | "NonNumber" -> NonNumber
  | "Any" -> Any
  | s when String.starts_with ~prefix:"Union" s -> parse_structural "Union" s
  | s when String.starts_with ~prefix:"<" s -> parse_structural "Tuple" s
  | s when String.starts_with ~prefix:"Range" s -> parse_range s
  | s when String.starts_with ~prefix:"HeapConstant" s ->
      parse_constant "HeapConstant" s
  | s when String.starts_with ~prefix:"OtherNumberConstant" s ->
      parse_constant "OtherNumberConstant" s
  | _ -> failwith "Unreachable"

let rec to_string t =
  match t with
  | OtherUnsigned31 -> "OtherUnsigned31"
  | OtherUnsigned32 -> "OtherUnsigned32"
  | OtherSigned32 -> "OtherSigned32"
  | OtherNumber -> "OtherNumber"
  | OtherString -> "OtherString"
  | Negative31 -> "Negative31"
  | Null -> "Null"
  | Undefined -> "Undefined"
  | Boolean -> "Boolean"
  | Unsigned30 -> "Unsigned30"
  | MinusZero -> "MinusZero"
  | NaN -> "NaN"
  | Symbol -> "Symbol"
  | InternalizedString -> "InternalizedString"
  | OtherCallable -> "OtherCallable"
  | OtherObject -> "OtherObject"
  | OtherUndetectable -> "OtherUndetectable"
  | CallableProxy -> "CallableProxy"
  | OtherProxy -> "OtherProxy"
  | CallableFunction -> "CallableFunction"
  | ClassConstructor -> "ClassConstructor"
  | BoundFunction -> "BoundFunction"
  | Hole -> "Hole"
  | OtherInternal -> "OtherInternal"
  | ExternalPointer -> "ExternalPointer"
  | Array -> "Array"
  | UnsignedBigInt63 -> "UnsignedBigInt63"
  | OtherUnsignedBigInt64 -> "OtherUnsignedBigInt64"
  | NegativeBigInt63 -> "NegativeBigInt63"
  | OtherBigInt -> "OtherBigInt"
  | WasmObject -> "WasmObject"
  | SandboxedPointer -> "SandboxedPointer"
  | None -> "None"
  | Signed31 -> "Signed31"
  | Signed32 -> "Signed32"
  | Signed32OrMinusZero -> "Signed32OrMinusZero"
  | Signed32OrMinusZeroOrNaN -> "Signed32OrMinusZeroOrNaN"
  | Negative32 -> "Negative32"
  | Unsigned31 -> "Unsigned31"
  | Unsigned32 -> "Unsigned32"
  | Unsigned32OrMinusZero -> "Unsigned32OrMinusZero"
  | Unsigned32OrMinusZeroOrNaN -> "Unsigned32OrMinusZeroOrNaN"
  | Integral32 -> "Integral32"
  | Integral32OrMinusZero -> "Integral32OrMinusZero"
  | Integral32OrMinusZeroOrNaN -> "Integral32OrMinusZeroOrNaN"
  | PlainNumber -> "PlainNumber"
  | OrderedNumber -> "OrderedNumber"
  | MinusZeroOrNaN -> "MinusZeroOrNaN"
  | Number -> "Number"
  | SignedBigInt64 -> "SignedBigInt64"
  | UnsignedBigInt64 -> "UnsignedBigInt64"
  | BigInt -> "BigInt"
  | Numeric -> "Numeric"
  | String -> "String"
  | UniqueName -> "UniqueName"
  | Name -> "Name"
  | InternalizedStringOrNull -> "InternalizedStringOrNull"
  | BooleanOrNumber -> "BooleanOrNumber"
  | BooleanOrNullOrNumber -> "BooleanOrNullOrNumber"
  | BooleanOrNullOrUndefined -> "BooleanOrNullOrUndefined"
  | Oddball -> "Oddball"
  | NullOrNumber -> "NullOrNumber"
  | NullOrUndefined -> "NullOrUndefined"
  | Undetectable -> "Undetectable"
  | NumberOrHole -> "NumberOrHole"
  | NumberOrOddball -> "NumberOrOddball"
  | NumericOrString -> "NumericOrString"
  | NumberOrUndefined -> "NumberOrUndefined"
  | NumberOrUndefinedOrNullOrBoolean -> "NumberOrUndefinedOrNullOrBoolean"
  | PlainPrimitive -> "PlainPrimitive"
  | NonBigIntPrimitive -> "NonBigIntPrimitive"
  | Primitive -> "Primitive"
  | OtherUndetectableOrUndefined -> "OtherUndetectableOrUndefined"
  | Proxy -> "Proxy"
  | ArrayOrOtherObject -> "ArrayOrOtherObject"
  | ArrayOrProxy -> "ArrayOrProxy"
  | Function -> "Function"
  | DetectableCallable -> "DetectableCallable"
  | Callable -> "Callable"
  | NonCallable -> "NonCallable"
  | NonCallableOrNull -> "NonCallableOrNull"
  | DetectableObject -> "DetectableObject"
  | DetectableReceiver -> "DetectableReceiver"
  | DetectableReceiverOrNull -> "DetectableReceiverOrNull"
  | Object -> "Object"
  | Receiver -> "Receiver"
  | ReceiverOrUndefined -> "ReceiverOrUndefined"
  | ReceiverOrNullOrUndefined -> "ReceiverOrNullOrUndefined"
  | SymbolOrReceiver -> "SymbolOrReceiver"
  | StringOrReceiver -> "StringOrReceiver"
  | Unique -> "Unique"
  | Internal -> "Internal"
  | NonInternal -> "NonInternal"
  | NonBigInt -> "NonBigInt"
  | NonNumber -> "NonNumber"
  | Any -> "Any"
  | Union tys ->
      List.map to_string tys |> String.concat ", "
      |> Printf.sprintf "Union (%s)"
  | Tuple tys ->
      List.map to_string tys |> String.concat ", "
      |> Printf.sprintf "Tuple (%s)"
  | Range (lb, ub) -> Printf.sprintf "Range (%f, %f)" lb ub
  | HeapConstant v -> Printf.sprintf "HeapConstant (0x%x)" v
  | OtherNumberConstant v -> Printf.sprintf "OtherNumberConstant (0x%x)" v

let lb_of range_ty = fst range_ty

let ub_of range_ty = snd range_ty
