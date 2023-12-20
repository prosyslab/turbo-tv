TurboTV
========
TurboTV is Translation Validation tool for [TurboFan](https://v8.dev/docs/turbofan) (JIT compiler in the V8 JavaScript engine).


Prerequisites
-------------
To build TurboTV you need followings:
- [python3](https://www.python.org/) (>= 3.6.0)
- [opam](https://opam.ocaml.org/) ( >= 2.1.2)

Building
--------
For building TurboTV, run [build script](./build.sh).
```
./build.sh
```

Running Translation Validation
------------------------------
This tool has two modes.

### UB-checker 
In the first mode, UB-checker checks TurboFan IR has Undefined Behavior. If the IR has Undefined Behavior, TurboTV outputs counterexample that can cause UB.
```
$ cat test/oob/oob.ir
#0:Start()()()
#1:Int32Constant[12]()()()
#2:Parameter[1]()()()
#3:AllocateRaw[Any, Young](#1:Int32Constant)(#0:Start)(#0:Start)
#4:StoreField[MapInstanceType, tagged base, 5, Number, kRepFloat64|KTypeNumber, NoWriteBarrier, mutable](#3:AllocateRaw, #2:Parameter)(#0:Start)(#0:Start)
#5:Return(#4:StoreField, #4:StoreField)(#0:Start)(#0:Start)
#6:End()()(#5:Return)

$ ./turbo-tv --check-ub test/oob/oob.ir
Result: Possible
Example: 
Parameters: 
Parameter[0]: TaggedSigned(2)
Parameter[1]: TaggedSigned(-2)
...
```
### EQ-checker
In the second mode, EQ-checker checks TurboFan's transformation is correct. If the transformation is incorrect, TurboTV outputs counterexample that may have different behavior before and after the transformation.

```
$ ls test/regressor/regress-number-tagged-signed
src.ir  tgt.ir

$ ./turbo-tv --verify test/regressor/regress-number-tagged-signed 
Result: Not Verified 
CounterExample: 
Parameters: 
Parameter[0]: TaggedSigned(-1)
Parameter[1]: TaggedSigned(1)
```
