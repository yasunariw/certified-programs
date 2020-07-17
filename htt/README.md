# HTT

## Requirements

- [Coq](https://coq.inria.fr/) (>= "8.9.0" & < "8.12~")
- [Mathematical Components](http://math-comp.github.io/math-comp/) `ssreflect` (>= "1.10.0" & < "1.11~")
- [FCSL PCM library](https://github.com/imdea-software/fcsl-pcm) (>= "1.0.0" & < "1.3~")
- [HTT](https://github.com/TyGuS/htt)
- [SSL-HTT](https://github.com/TyGuS/ssl-htt)

## Build and Install

We recommend installing with [OPAM](https://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq-htt git+https://github.com/TyGuS/htt\#master --no-action --yes
opam pin add coq-ssl-htt git+https://github.com/TyGuS/ssl-htt\#master --no-action --yes
opam install coq coq-mathcomp-ssreflect coq-fcsl-pcm coq-htt coq-ssl-htt
```
