type bitset =
  | OtherUnsigned31
  | OtherUnsigned32
  | OtherSigned32
  | OtherNumber
  | OtherString
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
  | SandboxedPointer
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

type non_bitset = HeapConstant | OtherNumberConstant | Tuple | Union | Range

type t = B of bitset | NB of non_bitset

let of_str str =
  match str with
  | "OtherUnsigned31" -> B OtherUnsigned31
  | "OtherUnsigned32" -> B OtherUnsigned32
  | "OtherSigned32" -> B OtherSigned32
  | "OtherNumber" -> B OtherNumber
  | "OtherString" -> B OtherString
  | "Negative31" -> B Negative31
  | "Null" -> B Null
  | "Undefined" -> B Undefined
  | "Boolean" -> B Boolean
  | "Unsigned30" -> B Unsigned30
  | "MinusZero" -> B MinusZero
  | "NaN" -> B NaN
  | "Symbol" -> B Symbol
  | "InternalizedString" -> B InternalizedString
  | "OtherCallable" -> B OtherCallable
  | "OtherObject" -> B OtherObject
  | "OtherUndetectable" -> B OtherUndetectable
  | "CallableProxy" -> B CallableProxy
  | "OtherProxy" -> B OtherProxy
  | "CallableFunction" -> B CallableFunction
  | "ClassConstructor" -> B ClassConstructor
  | "BoundFunction" -> B BoundFunction
  | "Hole" -> B Hole
  | "OtherInternal" -> B OtherInternal
  | "ExternalPointer" -> B ExternalPointer
  | "Array" -> B Array
  | "UnsignedBigInt63" -> B UnsignedBigInt63
  | "OtherUnsignedBigInt64" -> B OtherUnsignedBigInt64
  | "NegativeBigInt63" -> B NegativeBigInt63
  | "OtherBigInt" -> B OtherBigInt
  | "WasmObject" -> B WasmObject
  | "SandboxedPointer" -> B SandboxedPointer
  | "None" -> B None
  | "Signed31" -> B Signed31
  | "Signed32" -> B Signed32
  | "Signed32OrMinusZero" -> B Signed32OrMinusZero
  | "Signed32OrMinusZeroOrNaN" -> B Signed32OrMinusZeroOrNaN
  | "Negative32" -> B Negative32
  | "Unsigned31" -> B Unsigned31
  | "Unsigned32" -> B Unsigned32
  | "Unsigned32OrMinusZero" -> B Unsigned32OrMinusZero
  | "Unsigned32OrMinusZeroOrNaN" -> B Unsigned32OrMinusZeroOrNaN
  | "Integral32" -> B Integral32
  | "Integral32OrMinusZero" -> B Integral32OrMinusZero
  | "Integral32OrMinusZeroOrNaN" -> B Integral32OrMinusZeroOrNaN
  | "PlainNumber" -> B PlainNumber
  | "OrderedNumber" -> B OrderedNumber
  | "MinusZeroOrNaN" -> B MinusZeroOrNaN
  | "Number" -> B Number
  | "SignedBigInt64" -> B SignedBigInt64
  | "UnsignedBigInt64" -> B UnsignedBigInt64
  | "BigInt" -> B BigInt
  | "Numeric" -> B Numeric
  | "String" -> B String
  | "UniqueName" -> B UniqueName
  | "Name" -> B Name
  | "InternalizedStringOrNull" -> B InternalizedStringOrNull
  | "BooleanOrNumber" -> B BooleanOrNumber
  | "BooleanOrNullOrNumber" -> B BooleanOrNullOrNumber
  | "BooleanOrNullOrUndefined" -> B BooleanOrNullOrUndefined
  | "Oddball" -> B Oddball
  | "NullOrNumber" -> B NullOrNumber
  | "NullOrUndefined" -> B NullOrUndefined
  | "Undetectable" -> B Undetectable
  | "NumberOrHole" -> B NumberOrHole
  | "NumberOrOddball" -> B NumberOrOddball
  | "NumericOrString" -> B NumericOrString
  | "NumberOrUndefined" -> B NumberOrUndefined
  | "NumberOrUndefinedOrNullOrBoolean" -> B NumberOrUndefinedOrNullOrBoolean
  | "PlainPrimitive" -> B PlainPrimitive
  | "NonBigIntPrimitive" -> B NonBigIntPrimitive
  | "Primitive" -> B Primitive
  | "OtherUndetectableOrUndefined" -> B OtherUndetectableOrUndefined
  | "Proxy" -> B Proxy
  | "ArrayOrOtherObject" -> B ArrayOrOtherObject
  | "ArrayOrProxy" -> B ArrayOrProxy
  | "Function" -> B Function
  | "DetectableCallable" -> B DetectableCallable
  | "Callable" -> B Callable
  | "NonCallable" -> B NonCallable
  | "NonCallableOrNull" -> B NonCallableOrNull
  | "DetectableObject" -> B DetectableObject
  | "DetectableReceiver" -> B DetectableReceiver
  | "DetectableReceiverOrNull" -> B DetectableReceiverOrNull
  | "Object" -> B Object
  | "Receiver" -> B Receiver
  | "ReceiverOrUndefined" -> B ReceiverOrUndefined
  | "ReceiverOrNullOrUndefined" -> B ReceiverOrNullOrUndefined
  | "SymbolOrReceiver" -> B SymbolOrReceiver
  | "StringOrReceiver" -> B StringOrReceiver
  | "Unique" -> B Unique
  | "Internal" -> B Internal
  | "NonInternal" -> B NonInternal
  | "NonBigInt" -> B NonBigInt
  | "NonNumber" -> B NonNumber
  | "Any" -> B Any
  | "HeapConstant" -> NB HeapConstant
  | "OtherNumberConstant" -> NB OtherNumberConstant
  | "Tuple" -> NB Tuple
  | "Union" -> NB Union
  | "Range" -> NB Range
  | _ -> raise Not_found

let none = B None
