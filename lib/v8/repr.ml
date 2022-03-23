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
