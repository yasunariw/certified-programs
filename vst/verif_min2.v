Require Import VST.floyd.proofauto.

Require Import min2.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition ssl_is_valid_int (x: val) := exists y, x = Vint (Int.repr y) /\  Int.min_signed <= y <= Int.max_signed.

Ltac ssl_open_context :=
  lazymatch goal with
  | [ H:  ssl_is_valid_int ?x |- _ ] =>
    let x1 := fresh x in
    rename x into x1;
    let H2 := fresh H in
    let H3 := fresh H in
    destruct H as [x [H2 H3]]; rewrite H2; ssl_open_context
  | _ => idtac
  end.


Definition min2_spec :=
  DECLARE _min2
   WITH r: val, x: val, y: val
   PRE [ (tptr (Tunion _sslval noattr)), tint, tint ]
   PROP( is_pointer_or_null(r); ssl_is_valid_int(x); ssl_is_valid_int(y) )
   PARAMS(r; x; y)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inl (Vint (Int.repr 0))] r))
   POST[ tvoid ]
   EX m: Z,
   PROP( (m <= (force_signed_int x)); (m <= (force_signed_int y)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inl (Vint (Int.repr m))] r)).



(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [min2_spec]).

From mathcomp Require Import ssreflect ssrbool.

(** Proof that f_swap, the body of the swap() function,
 ** satisfies swap_spec, in the global context (Vprog,Gprog).
 **)
Lemma min2_swap: semax_body Vprog Gprog f_min2 min2_spec.
Proof.
  start_function.
  ssl_open_context.
  forward_if.
  - forward.
    forward.
    Exists x.
    entailer.
  - forward.
    forward.
    Exists y.
    entailer!.
Qed.

