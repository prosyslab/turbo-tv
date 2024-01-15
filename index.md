## Introduction
TurboTV is a translation validator for the JavaScript (JS) just-in-time (JIT) compiler of V8.
While JS engines have become a crucial part of various software systems, their emerging adaption
of JIT compilation makes it increasingly challenging to ensure their correctness.
We tackle this problem with an SMT-based translation validation (TV) that checks whether a specific
compilation is semantically correct. We formally define the semantics of IR of TurboFan (JIT compiler of V8)
as SMT encoding. For efficient validation, we design a staged strategy for JS JIT compilers.
This allows us to decompose the whole correctness checking into simpler ones.
Furthermore, we utilize fuzzing to achieve practical TV. We generate a large number of JS functions using
a fuzzer to trigger various optimization passes of TurboFan and validate their compilation using TurboTV.
Lastly, we demonstrate that TurboTV can also be used for cross-language TV. We show that TurboTV can validate
the translation chain from LLVM IR to TurboFan IR, collaborating with an off-the-shelf TV tool for LLVM.
We evaluated TurboTV on various sets of JS and LLVM programs.
TurboTV effectively validated a large number of compilations of TurboFan with a low false positive rate
and discovered a new miscompilation in LLVM.

## Publications

* **Translation Validation for JIT Compiler in the V8 JavaScript Engine** <a href="https://prosys.kaist.ac.kr/publications/icse24.pdf"><i class="fas fa-file-pdf"></i></a><br>
  Seungwan Kwon, Jaeseong Kwon, Wooseok Kang, Juneyoung Lee, and [Kihong Heo](https://kihongheo.kaist.ac.kr)<br>
  ICSE 2024: International Conference on Software Engineering, 2024

## Artifacts

We provide the artifacts image that contains datasets and programs used by evaluating TurboTV.
You can access the artifacts image via the following links:
- [DockerHub](https://hub.docker.com/repository/docker/prosyslab/turbo-tv/)
- [Zenodo](https://zenodo.org/records/10453785)
- [Github](https://github.com/prosyslab/turbo-tv-artifact)
