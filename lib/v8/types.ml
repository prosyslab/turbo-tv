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

let of_string str =
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
  | _ -> failwith "Unreachable"

let lb_of range_ty = fst range_ty

let ub_of range_ty = snd range_ty
