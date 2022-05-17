open Z3utils

(* smi *)
let smi_min = -1073741824

let smi_max = 1073741823

let smi_mask = 0xffffffff

(* int64 *)
let int64_min = Int64.min_int

let int64_max = Int64.max_int

let uint64_min = 0

(* it's enough for now *)
let uint64_max = Int64.max_int

(* IEEE-754 *)
let inf = BitVecVal.inf ()

let ninf = BitVecVal.ninf ()

let minus_zero = BitVecVal.minus_zero ()

let nan = BitVecVal.nan ()