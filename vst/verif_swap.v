Require Import VST.floyd.proofauto.

Require Import swap.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* Beginning of the API spec for the sumarray.c program *)

Definition swap_spec :=
  DECLARE _swap
   WITH x: val, y: val, a: val, b: val
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null(x); is_pointer_or_null(y); is_pointer_or_null(a); is_pointer_or_null(b) )
   PARAMS(x; y)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inr a] x); (data_at Tsh (tarray (Tunion _sslval noattr) 1) [inr b] y))
   POST[ tvoid ]
   PROP(  )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inr b] x); (data_at Tsh (tarray (Tunion _sslval noattr) 1) [inr a] y)).



(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [swap_spec]).

(** Proof that f_swap, the body of the swap() function,
 ** satisfies swap_spec, in the global context (Vprog,Gprog).
 **)
Lemma body_swap: semax_body Vprog Gprog f_swap swap_spec.
Proof.
  start_function.
  try forward.
  try forward.
  try forward.
  try forward.
  try entailer!.
Qed.
