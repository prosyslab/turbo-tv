module Repr = struct
  type t =
    | Word8
    | Word16
    | Word32
    | Word64
    | Float32
    | Float64
    | Simd128
    | TaggedPointer
    | MapWord
    | TaggedSigned
    | Tagged
    | CompressedPointer
    | Compressed
    | SandboxedPointer
    | Bit
    | None

  let of_string str =
    match str with
    | "Word8" -> Word8
    | "Word16" -> Word16
    | "Word32" -> Word32
    | "Word64" -> Word64
    | "Float32" -> Float32
    | "Float64" -> Float64
    | "Simd128" -> Simd128
    | "TaggedPointer" -> TaggedPointer
    | "MapWord" -> MapWord
    | "TaggedSigned" -> TaggedSigned
    | "Tagged" -> Tagged
    | "CompressedPointer" -> CompressedPointer
    | "Compressed" -> Compressed
    | "SandboxedPointer" -> SandboxedPointer
    | "Bit" -> Bit
    | "None" -> None
    | _ -> failwith "Invalid repr"

  let size_of t =
    match t with
    | Word8 -> 1
    | Word16 -> 2
    | Word32 -> 4
    | Word64 -> 8
    | Float32 -> 4
    | Float64 -> 8
    | Simd128 -> 16
    | TaggedPointer -> 8
    | MapWord -> 4
    | TaggedSigned -> 8
    | Tagged -> 8
    | CompressedPointer -> 4
    | Compressed -> 4
    | SandboxedPointer -> 5
    | Bit -> 1
    | None -> 0
end

module Sem = struct
  type t = Int32 | Uint32 | Int64 | Uint64 | Number | None | Any | Bool
end

type t =
  | Int8
  | Uint8
  | Int16
  | Uint16
  | Int32
  | Uint32
  | Int64
  | Uint64
  | Float32
  | Float64
  | Simd128
  | Pointer
  | TaggedPointer
  | MapInHeader
  | TaggedSigned
  | AnyTagged
  | CompressedPointer
  | AnyCompressed
  | SandboxedPointer
  | Bool
  | None

(* constructor *)
let of_rs_string rs =
  match rs with
  | "kRepWord8|kTypeInt32" -> Int8
  | "kRepWord8|kTypeUint32" -> Uint8
  | "kRepWord16|kTypeInt32" -> Int16
  | "kRepWord16|kTypeUint32" -> Uint16
  | "kRepWord32|kTypeInt32" -> Int32
  | "kRepWord32|kTypeUint32" -> Uint32
  | "kRepWord64|kTypeInt64" -> Int64
  | "kRepWord64|kTypeUint64" -> Uint64
  | "kRepFloat32|kTypeNumber" -> Float32
  | "kRepFloat64|kTypeNumber" -> Float64
  | "kRepSimd128|kMachNone" -> Simd128
  | "kRepWord64|kMachNone" -> Pointer
  | "kRepTaggedPointer|kTypeAny" -> TaggedPointer
  | "kRepMapWord|kTypeAny" -> MapInHeader
  | "kRepTaggedSigned|kTypeInt32" -> TaggedSigned
  | "kRepTagged|kTypeAny" -> AnyTagged
  | "kRepCompressedPointer|kTypeAny" -> CompressedPointer
  | "kRepCompressed|kTypeAny" -> AnyCompressed
  | "kRepSandboxedPointer|kMachNone" -> SandboxedPointer
  | "kRepBit|kTypeBool" -> Bool
  | "kRepNone|kMachNone" -> None
  | _ -> failwith "Invalid repr|semantic string"

let of_repr (repr : Repr.t) =
  match repr with
  | Word8 -> [ Int8; Uint8 ]
  | Word16 -> [ Int16; Uint16 ]
  | Word32 -> [ Int32; Uint32 ]
  | Word64 -> [ Int64; Uint64; Pointer ]
  | Float32 -> [ Float32 ]
  | Float64 -> [ Float64 ]
  | Simd128 -> [ Simd128 ]
  | TaggedPointer -> [ TaggedPointer ]
  | MapWord -> [ MapInHeader ]
  | TaggedSigned -> [ TaggedSigned ]
  | Tagged -> [ AnyTagged ]
  | CompressedPointer -> [ CompressedPointer ]
  | Compressed -> [ AnyCompressed ]
  | SandboxedPointer -> [ SandboxedPointer ]
  | Bit -> [ Bool ]
  | None -> [ None ]

(* getter *)
let repr t : Repr.t =
  match t with
  | Int8 -> Word8
  | Uint8 -> Word8
  | Int16 -> Word16
  | Uint16 -> Word16
  | Int32 -> Word32
  | Uint32 -> Word32
  | Int64 -> Word64
  | Uint64 -> Word64
  | Float32 -> Float32
  | Float64 -> Float64
  | Simd128 -> Simd128
  | Pointer -> Word64
  | TaggedPointer -> TaggedPointer
  | MapInHeader -> MapWord
  | TaggedSigned -> TaggedSigned
  | AnyTagged -> Tagged
  | CompressedPointer -> CompressedPointer
  | AnyCompressed -> Compressed
  | SandboxedPointer -> SandboxedPointer
  | Bool -> Bit
  | None -> None

let sem t : Sem.t =
  match t with
  | Int8 -> Int32
  | Uint8 -> Uint32
  | Int16 -> Int32
  | Uint16 -> Uint32
  | Int32 -> Int32
  | Uint32 -> Uint32
  | Int64 -> Int64
  | Uint64 -> Uint64
  | Float32 -> Number
  | Float64 -> Number
  | Simd128 -> None
  | Pointer -> None
  | TaggedPointer -> Any
  | MapInHeader -> Any
  | TaggedSigned -> Int32
  | AnyTagged -> Any
  | CompressedPointer -> Any
  | AnyCompressed -> Any
  | SandboxedPointer -> None
  | Bool -> Bool
  | None -> None

(* methods *)
let size_of t = repr t |> Repr.size_of
