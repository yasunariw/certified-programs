Require Import VST.floyd.proofauto.
Require Import swap.
(* Seems that VST changed their notation. This re-enables the old one. *)
Require Export VST.floyd.Funspec_old_Notation.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


(* Functional spec of this program.  *)

Check semax_load.

(* Beginning of the API spec for the sumarray.c program *)
Definition swap_spec : ident * funspec :=
  DECLARE _swap
   WITH x: val, y: val, a: Z, b: Z, sh: share
   PRE  [_x OF tptr tint, _y OF tptr tint]
         PROP (writable_share sh)
         LOCAL(temp _x x; temp _y y)
         SEP  (data_at sh tint (Vint (Int.repr a)) x; data_at sh tint (Vint (Int.repr b)) y)
   POST [tvoid]
         PROP ()
         LOCAL()
         SEP  (data_at sh tint (Vint (Int.repr b)) x; data_at sh tint (Vint (Int.repr a)) y).

(** Instead of specifying the type of some arbitrary share sh in PROP,
 ** I could have used `Tsh`, the top share which gives total permission.
 **)

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [swap_spec]).

(** Proof that f_swap, the body of the swap() function,
 ** satisfies swap_spec, in the global context (Vprog,Gprog).
 **)
Lemma body_swap: semax_body Vprog Gprog f_swap swap_spec.
Proof.
  start_function.

  forward.
  forward.
  forward.
  forward.

  (* When in doubt, use `hint`. *)
  hint.
  
  entailer!.
Qed.
