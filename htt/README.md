# HTT

## Requirements

- [Coq](https://coq.inria.fr/) (>= "8.9.0" & < "8.12~")
- [Mathematical Components](http://math-comp.github.io/math-comp/) `ssreflect` (>= "1.10.0" & < "1.11~")
- [FCSL PCM library](https://github.com/imdea-software/fcsl-pcm) (>= "1.0.0" & < "1.3~")
- [HTT](https://github.com/TyGuS/htt)

## Build and Install

For Coq requirements available on [OPAM](https://opam.ocaml.org/doc/Install.html), we recommend installing with it:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq-htt git+https://github.com/TyGuS/htt\#master --no-action --yes
opam install coq coq-mathcomp-ssreflect coq-fcsl-pcm coq-htt
```

Then, compile the predefined tactics by running `make clean && make` in this directory.

