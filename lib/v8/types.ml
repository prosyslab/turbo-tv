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
  let parse_union union_ty_str =
    let elems_reg = Re.Pcre.regexp "\\(([^\\)]*)\\)" in
    let elems_ty_str =
      try
        Re.Group.get (Re.exec elems_reg union_ty_str) 1
        |> String.split_on_char '|' |> List.map String.trim
      with Not_found ->
        let cause = union_ty_str in
        let reason = "Cannot parse 'Union' from the " ^ union_ty_str in
        raise (InvalidFormat (cause, reason))
    in
    let elems_ty = List.map of_string elems_ty_str in
    Union elems_ty
  in

  let parse_tuple tuple_ty_str =
    let elems_reg = Re.Pcre.regexp "<([^\\)]*)>" in
    let elems_ty_str =
      (* could be error if one of element is Range since it also contains "," *)
      try
        Re.Group.get (Re.exec elems_reg tuple_ty_str) 1
        |> String.split_on_char ',' |> List.map String.trim
      with Not_found ->
        let cause = tuple_ty_str in
        let reason = "Cannot parse 'Tuple' from the " ^ tuple_ty_str in
        raise (InvalidFormat (cause, reason))
    in
    let elems_ty = List.map of_string elems_ty_str in
    Tuple elems_ty
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
  | s when String.starts_with ~prefix:"(" s -> parse_union s
  | s when String.starts_with ~prefix:"<" s -> parse_tuple s
  | s when String.starts_with ~prefix:"Range" s -> parse_range s
  | s when String.starts_with ~prefix:"HeapConstant" s ->
      parse_constant "HeapConstant" s
  | s when String.starts_with ~prefix:"OtherNumberConstant" s ->
      parse_constant "OtherNumberConstant" s
  | _ -> failwith ("Cannot parse " ^ str)

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

(* range *)
let lb_of range_ty = fst range_ty

let ub_of range_ty = snd range_ty

let is t1 t2 = List.mem t1 t2

(* decompose types into its atomic type unit *)
let decompose t =
  match t with
  | Unsigned30 -> [ Unsigned30 ]
  | Negative31 -> [ Negative31 ]
  | Signed31 -> [ Unsigned30; Negative31 ]
  | OtherUnsigned31 -> [ OtherUnsigned31 ]
  | OtherSigned32 -> [ OtherSigned32 ]
  | Signed32 -> [ OtherSigned32; Unsigned30; OtherUnsigned31; Negative31 ]
  | MinusZero -> [ MinusZero ]
  | Signed32OrMinusZero ->
      [ OtherSigned32; Unsigned30; MinusZero; OtherUnsigned31; Negative31 ]
  | NaN -> [ NaN ]
  | Signed32OrMinusZeroOrNaN ->
      [ OtherSigned32; NaN; Unsigned30; MinusZero; OtherUnsigned31; Negative31 ]
  | Negative32 -> [ OtherSigned32; Negative31 ]
  | Unsigned31 -> [ Unsigned30; OtherUnsigned31 ]
  | OtherUnsigned32 -> [ OtherUnsigned32 ]
  | Unsigned32 -> [ Unsigned30; OtherUnsigned31; OtherUnsigned32 ]
  | Unsigned32OrMinusZero ->
      [ Unsigned30; OtherUnsigned31; MinusZero; OtherUnsigned32 ]
  | Unsigned32OrMinusZeroOrNaN ->
      [ NaN; Unsigned30; MinusZero; OtherUnsigned31; OtherUnsigned32 ]
  | Integral32 ->
      [
        OtherSigned32; OtherUnsigned32; Unsigned30; OtherUnsigned31; Negative31;
      ]
  | Integral32OrMinusZero ->
      [
        OtherSigned32;
        OtherUnsigned32;
        Unsigned30;
        OtherUnsigned31;
        MinusZero;
        Negative31;
      ]
  | Integral32OrMinusZeroOrNaN ->
      [
        OtherSigned32;
        OtherUnsigned32;
        NaN;
        Unsigned30;
        OtherUnsigned31;
        MinusZero;
        Negative31;
      ]
  | OtherNumber -> [ OtherNumber ]
  | PlainNumber ->
      [
        OtherSigned32;
        OtherUnsigned32;
        Unsigned30;
        OtherUnsigned31;
        Negative31;
        OtherNumber;
      ]
  | OrderedNumber ->
      [
        OtherSigned32;
        OtherUnsigned32;
        Unsigned30;
        OtherUnsigned31;
        MinusZero;
        Negative31;
        OtherNumber;
      ]
  | MinusZeroOrNaN -> [ NaN; MinusZero ]
  | Number ->
      [
        OtherSigned32;
        OtherUnsigned32;
        NaN;
        Unsigned30;
        OtherUnsigned31;
        MinusZero;
        Negative31;
        OtherNumber;
      ]
  | UnsignedBigInt63 -> [ UnsignedBigInt63 ]
  | NegativeBigInt63 -> [ NegativeBigInt63 ]
  | SignedBigInt64 -> [ NegativeBigInt63; UnsignedBigInt63 ]
  | OtherUnsignedBigInt64 -> [ OtherUnsignedBigInt64 ]
  | UnsignedBigInt64 -> [ UnsignedBigInt63; OtherUnsignedBigInt64 ]
  | OtherBigInt -> [ OtherBigInt ]
  | BigInt ->
      [ NegativeBigInt63; UnsignedBigInt63; OtherUnsignedBigInt64; OtherBigInt ]
  | Numeric ->
      [
        OtherSigned32;
        NaN;
        Negative31;
        NegativeBigInt63;
        Unsigned30;
        OtherUnsignedBigInt64;
        MinusZero;
        UnsignedBigInt63;
        OtherBigInt;
        OtherUnsigned31;
        OtherUnsigned32;
        OtherNumber;
      ]
  | InternalizedString -> [ InternalizedString ]
  | OtherString -> [ OtherString ]
  | String -> [ InternalizedString; OtherString ]
  | Symbol -> [ Symbol ]
  | UniqueName -> [ Symbol; InternalizedString ]
  | Name -> [ Symbol; InternalizedString; OtherString ]
  | Null -> [ Null ]
  | InternalizedStringOrNull -> [ InternalizedString; Null ]
  | Boolean -> [ Boolean ]
  | BooleanOrNumber ->
      [
        OtherSigned32;
        NaN;
        Negative31;
        Unsigned30;
        MinusZero;
        Boolean;
        OtherUnsigned31;
        OtherUnsigned32;
        OtherNumber;
      ]
  | BooleanOrNullOrNumber ->
      [
        OtherSigned32;
        NaN;
        Negative31;
        Null;
        Unsigned30;
        MinusZero;
        Boolean;
        OtherUnsigned31;
        OtherUnsigned32;
        OtherNumber;
      ]
  | Undefined -> [ Undefined ]
  | BooleanOrNullOrUndefined -> [ Undefined; Boolean; Null ]
  | Hole -> [ Hole ]
  | Oddball -> [ Undefined; Boolean; Null; Hole ]
  | NullOrNumber ->
      [
        OtherSigned32;
        NaN;
        Null;
        Negative31;
        Unsigned30;
        MinusZero;
        OtherUnsigned31;
        OtherUnsigned32;
        OtherNumber;
      ]
  | NullOrUndefined -> [ Undefined; Null ]
  | OtherUndetectable -> [ OtherUndetectable ]
  | Undetectable -> [ Undefined; OtherUndetectable; Null ]
  | NumberOrHole ->
      [
        OtherSigned32;
        NaN;
        Negative31;
        Unsigned30;
        MinusZero;
        Hole;
        OtherUnsigned31;
        OtherUnsigned32;
        OtherNumber;
      ]
  | NumberOrOddball ->
      [
        OtherSigned32;
        NaN;
        Negative31;
        Null;
        Unsigned30;
        MinusZero;
        Boolean;
        Hole;
        Undefined;
        OtherUnsigned31;
        OtherUnsigned32;
        OtherNumber;
      ]
  | NumericOrString ->
      [
        OtherSigned32;
        NaN;
        Negative31;
        NegativeBigInt63;
        Unsigned30;
        OtherUnsignedBigInt64;
        MinusZero;
        OtherString;
        UnsignedBigInt63;
        OtherBigInt;
        InternalizedString;
        OtherUnsigned31;
        OtherUnsigned32;
        OtherNumber;
      ]
  | NumberOrUndefined ->
      [
        OtherSigned32;
        NaN;
        Negative31;
        Unsigned30;
        MinusZero;
        Undefined;
        OtherUnsigned31;
        OtherUnsigned32;
        OtherNumber;
      ]
  | NumberOrUndefinedOrNullOrBoolean ->
      [
        OtherSigned32;
        NaN;
        Negative31;
        Null;
        Unsigned30;
        MinusZero;
        Boolean;
        Undefined;
        OtherUnsigned31;
        OtherUnsigned32;
        OtherNumber;
      ]
  | PlainPrimitive ->
      [
        OtherSigned32;
        NaN;
        Negative31;
        Null;
        Unsigned30;
        MinusZero;
        OtherString;
        Boolean;
        InternalizedString;
        Undefined;
        OtherUnsigned31;
        OtherUnsigned32;
        OtherNumber;
      ]
  | NonBigIntPrimitive ->
      [
        Symbol;
        OtherSigned32;
        NaN;
        OtherUnsigned32;
        Null;
        Unsigned30;
        MinusZero;
        OtherString;
        Boolean;
        InternalizedString;
        Undefined;
        OtherUnsigned31;
        Negative31;
        OtherNumber;
      ]
  | Primitive ->
      [
        NegativeBigInt63;
        Unsigned30;
        MinusZero;
        OtherString;
        OtherBigInt;
        OtherUnsignedBigInt64;
        OtherUnsigned31;
        Symbol;
        OtherSigned32;
        NaN;
        Null;
        Negative31;
        UnsignedBigInt63;
        Boolean;
        InternalizedString;
        Undefined;
        OtherUnsigned32;
        OtherNumber;
      ]
  | OtherUndetectableOrUndefined -> [ Undefined; OtherUndetectable ]
  | CallableProxy -> [ CallableProxy ]
  | OtherProxy -> [ OtherProxy ]
  | Proxy -> [ CallableProxy; OtherProxy ]
  | Array -> [ Array ]
  | OtherObject -> [ OtherObject ]
  | ArrayOrOtherObject -> [ OtherObject; Array ]
  | ArrayOrProxy -> [ Array; CallableProxy; OtherProxy ]
  | CallableFunction -> [ CallableFunction ]
  | ClassConstructor -> [ ClassConstructor ]
  | Function -> [ ClassConstructor; CallableFunction ]
  | BoundFunction -> [ BoundFunction ]
  | OtherCallable -> [ OtherCallable ]
  | DetectableCallable ->
      [
        BoundFunction;
        ClassConstructor;
        OtherCallable;
        CallableProxy;
        CallableFunction;
      ]
  | Callable ->
      [
        OtherUndetectable;
        BoundFunction;
        ClassConstructor;
        OtherCallable;
        CallableProxy;
        CallableFunction;
      ]
  | NonCallable -> [ OtherObject; Array; OtherProxy ]
  | NonCallableOrNull -> [ OtherObject; Array; Null; OtherProxy ]
  | DetectableObject ->
      [
        BoundFunction;
        ClassConstructor;
        OtherObject;
        OtherCallable;
        Array;
        CallableFunction;
      ]
  | DetectableReceiver ->
      [
        Array;
        BoundFunction;
        OtherProxy;
        ClassConstructor;
        OtherObject;
        OtherCallable;
        CallableProxy;
        CallableFunction;
      ]
  | DetectableReceiverOrNull ->
      [
        BoundFunction;
        Null;
        OtherProxy;
        ClassConstructor;
        OtherObject;
        Array;
        OtherCallable;
        CallableProxy;
        CallableFunction;
      ]
  | Object ->
      [
        Array;
        BoundFunction;
        ClassConstructor;
        OtherObject;
        OtherCallable;
        OtherUndetectable;
        CallableFunction;
      ]
  | WasmObject -> [ WasmObject ]
  | Receiver ->
      [
        BoundFunction;
        OtherProxy;
        ClassConstructor;
        OtherObject;
        Array;
        OtherCallable;
        CallableProxy;
        WasmObject;
        OtherUndetectable;
        CallableFunction;
      ]
  | ReceiverOrUndefined ->
      [
        BoundFunction;
        OtherProxy;
        ClassConstructor;
        OtherObject;
        Array;
        OtherCallable;
        CallableProxy;
        WasmObject;
        Undefined;
        OtherUndetectable;
        CallableFunction;
      ]
  | ReceiverOrNullOrUndefined ->
      [
        BoundFunction;
        Null;
        OtherProxy;
        ClassConstructor;
        OtherObject;
        Array;
        OtherCallable;
        CallableProxy;
        WasmObject;
        Undefined;
        OtherUndetectable;
        CallableFunction;
      ]
  | SymbolOrReceiver ->
      [
        Symbol;
        BoundFunction;
        OtherProxy;
        ClassConstructor;
        OtherObject;
        Array;
        OtherCallable;
        CallableProxy;
        WasmObject;
        OtherUndetectable;
        CallableFunction;
      ]
  | StringOrReceiver ->
      [
        BoundFunction;
        OtherProxy;
        ClassConstructor;
        OtherObject;
        Array;
        OtherCallable;
        CallableProxy;
        OtherString;
        WasmObject;
        InternalizedString;
        OtherUndetectable;
        CallableFunction;
      ]
  | Unique ->
      [
        Symbol;
        BoundFunction;
        Null;
        OtherProxy;
        ClassConstructor;
        OtherObject;
        Array;
        OtherCallable;
        CallableProxy;
        WasmObject;
        Boolean;
        InternalizedString;
        Hole;
        Undefined;
        OtherUndetectable;
        CallableFunction;
      ]
  | ExternalPointer -> [ ExternalPointer ]
  | SandboxedPointer -> [ SandboxedPointer ]
  | OtherInternal -> [ OtherInternal ]
  | Internal -> [ ExternalPointer; SandboxedPointer; OtherInternal; Hole ]
  | NonInternal ->
      [
        BoundFunction;
        OtherProxy;
        ClassConstructor;
        NegativeBigInt63;
        Unsigned30;
        MinusZero;
        OtherString;
        WasmObject;
        OtherBigInt;
        OtherUnsignedBigInt64;
        OtherUnsigned31;
        OtherUndetectable;
        CallableFunction;
        Symbol;
        OtherSigned32;
        NaN;
        Null;
        Negative31;
        OtherObject;
        Array;
        OtherCallable;
        CallableProxy;
        UnsignedBigInt63;
        Boolean;
        InternalizedString;
        Undefined;
        OtherUnsigned32;
        OtherNumber;
      ]
  | NonBigInt ->
      [
        BoundFunction;
        OtherProxy;
        ClassConstructor;
        Unsigned30;
        MinusZero;
        OtherString;
        WasmObject;
        OtherUnsigned31;
        OtherUndetectable;
        CallableFunction;
        Symbol;
        OtherSigned32;
        NaN;
        Null;
        Negative31;
        OtherObject;
        Array;
        OtherCallable;
        CallableProxy;
        Boolean;
        InternalizedString;
        Undefined;
        OtherUnsigned32;
        OtherNumber;
      ]
  | NonNumber ->
      [
        BoundFunction;
        OtherProxy;
        ClassConstructor;
        NegativeBigInt63;
        ExternalPointer;
        WasmObject;
        OtherString;
        OtherBigInt;
        Hole;
        OtherUnsignedBigInt64;
        OtherUndetectable;
        CallableFunction;
        Symbol;
        Null;
        OtherObject;
        Array;
        OtherCallable;
        CallableProxy;
        SandboxedPointer;
        UnsignedBigInt63;
        Boolean;
        InternalizedString;
        OtherInternal;
        Undefined;
      ]
  | None -> [ None ]
  | Any ->
      [
        BoundFunction;
        OtherProxy;
        ClassConstructor;
        NegativeBigInt63;
        Unsigned30;
        ExternalPointer;
        MinusZero;
        OtherString;
        OtherBigInt;
        Hole;
        OtherUnsignedBigInt64;
        OtherUnsigned31;
        OtherSigned32;
        NaN;
        Null;
        OtherObject;
        Array;
        OtherCallable;
        CallableProxy;
        Boolean;
        OtherInternal;
        Undefined;
        OtherUnsigned32;
        WasmObject;
        OtherUndetectable;
        CallableFunction;
        Symbol;
        SandboxedPointer;
        UnsignedBigInt63;
        InternalizedString;
        Negative31;
        OtherNumber;
      ]
  | _ -> [ t ]