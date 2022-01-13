exception Invalid_opcode

type t =
  | Branch
  | Call
  | ChangeInt32ToTagged
  | CheckedTaggedSignedToInt32
  | Checkpoint
  | EffectPhi
  | End
  | ExternalConstant
  | FrameState
  | HeapConstant
  | IfFalse
  | IfTrue
  | Int32Add
  | Int32Constant
  | Int64Constant
  | Load
  | LoadStackCheckOffset
  | Merge
  | Parameter
  | Return
  | StackPointerGreaterThan
  | Start
  | TypedStateValues

let of_str str =
  match str with
  | "Branch" -> Branch
  | "Call" -> Call
  | "ChangeInt32ToTagged" -> ChangeInt32ToTagged
  | "CheckedTaggedSignedToInt32" -> CheckedTaggedSignedToInt32
  | "Checkpoint" -> Checkpoint
  | "EffectPhi" -> EffectPhi
  | "End" -> End
  | "ExternalConstant" -> ExternalConstant
  | "FrameState" -> FrameState
  | "HeapConstant" -> HeapConstant
  | "IfFalse" -> IfFalse
  | "IfTrue" -> IfTrue
  | "Int32Add" -> Int32Add
  | "Int32Constant" -> Int32Constant
  | "Int64Constant" -> Int64Constant
  | "Load" -> Load
  | "LoadStackCheckOffset" -> LoadStackCheckOffset
  | "Merge" -> Merge
  | "Parameter" -> Parameter
  | "Return" -> Return
  | "StackPointerGreaterThan" -> StackPointerGreaterThan
  | "Start" -> Start
  | "TypedStateValues" -> TypedStateValues
  | _ -> raise Invalid_opcode

let to_str opcode =
  match opcode with
  | Branch -> "Branch"
  | Call -> "Call"
  | ChangeInt32ToTagged -> "ChangeInt32ToTagged"
  | CheckedTaggedSignedToInt32 -> "CheckedTaggedSignedToInt32"
  | Checkpoint -> "Checkpoint"
  | EffectPhi -> "EffectPhi"
  | End -> "End"
  | ExternalConstant -> "ExternalConstant"
  | FrameState -> "FrameState"
  | HeapConstant -> "HeapConstant"
  | IfFalse -> "IfFalse"
  | IfTrue -> "IfTrue"
  | Int32Add -> "Int32Add"
  | Int32Constant -> "Int32Constant"
  | Int64Constant -> "Int64Constant"
  | Load -> "Load"
  | LoadStackCheckOffset -> "LoadStackCheckOffset"
  | Merge -> "Merge"
  | Parameter -> "Parameter"
  | Return -> "Return"
  | StackPointerGreaterThan -> "StackPointerGreaterThan"
  | Start -> "Start"
  | TypedStateValues -> "TypedStateValues"
