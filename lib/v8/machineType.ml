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
    | "kRepWord8" -> Word8
    | "kRepWord16" -> Word16
    | "kRepWord32" -> Word32
    | "kRepWord64" -> Word64
    | "kRepFloat32" -> Float32
    | "kRepFloat64" -> Float64
    | "kRepSimd128" -> Simd128
    | "kRepTaggedPointer" -> TaggedPointer
    | "kRepMapWord" -> MapWord
    | "kRepTaggedSigned" -> TaggedSigned
    | "kRepTagged" -> Tagged
    | "kRepCompressedPointer" -> CompressedPointer
    | "kRepCompressed" -> Compressed
    | "kRepSandboxedPointer" -> SandboxedPointer
    | "kRepBit" -> Bit
    | "kNone" -> None
    | _ -> failwith (Printf.sprintf "Invalid repr: %s" str)

  let of_rs_string str =
    try
      List.find
        (fun prefix -> String.starts_with ~prefix str)
        [
          "kRepWord8";
          "kRepWord16";
          "kRepWord32";
          "kRepWord64";
          "kRepFloat32";
          "kRepFloat64";
          "kRepSimd128";
          "kRepTaggedPointer";
          "kRepMapWord";
          "kRepTaggedSigned";
          "kRepTagged";
          "kRepCompressedPointer";
          "kRepCompressed";
          "kRepSandboxedPointer";
          "kRepBit";
          "kNone";
        ]
      |> of_string
    with Not_found -> failwith (Printf.sprintf "Invalid repr: %s" str)

  let to_string t =
    match t with
    | Word8 -> "kRepWord8"
    | Word16 -> "kRepWord16"
    | Word32 -> "kRepWord32"
    | Word64 -> "kRepWord64"
    | Float32 -> "kRepFloat32"
    | Float64 -> "kRepFloat64"
    | Simd128 -> "kRepSimd128"
    | TaggedPointer -> "kRepTaggedPointer"
    | MapWord -> "kRepMapWord"
    | TaggedSigned -> "kRepTaggedSigned"
    | Tagged -> "kRepTagged"
    | CompressedPointer -> "kRepCompressedPointer"
    | Compressed -> "kRepCompressed"
    | SandboxedPointer -> "kRepSandboxedPointer"
    | Bit -> "kRepBit"
    | None -> "kNone"

  let width_of t =
    match t with
    | Word8 -> 8
    | Word16 -> 16
    | Word32 -> 32
    | Word64 -> 64
    | Float32 -> 32
    | Float64 -> 64
    | Simd128 -> 128
    | TaggedPointer -> 32
    | MapWord -> 32
    | TaggedSigned -> 32
    | Tagged -> 32
    | CompressedPointer -> 32
    | Compressed -> 32
    | SandboxedPointer -> 40
    | Bit -> 1
    | None -> 0

  let element_size_log2_of t =
    let tagged_size_log2 = 3 in
    let system_pointer_size_log2 = 3 in
    match t with
    | Bit | Word8 -> 0
    | Word16 -> 1
    | Word32 | Float32 -> 2
    | Word64 | Float64 -> 3
    | Simd128 -> 4
    | TaggedSigned | TaggedPointer | Tagged | MapWord | CompressedPointer
    | Compressed ->
        tagged_size_log2
    | SandboxedPointer -> system_pointer_size_log2
    | _ -> failwith (Printf.sprintf "Unreachable: %s" (to_string t))

  let size_of t = width_of t / 8
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
