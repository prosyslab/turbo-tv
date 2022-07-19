type t = { value : Value.t; control : Control.t; deopt : Deopt.t; ub : Ub.t }

let mk ?(value = Value.empty) ?(control = Control.empty) ?(deopt = Deopt.empty)
    ?(ub = Ub.empty) () =
  { value; control; deopt; ub }
