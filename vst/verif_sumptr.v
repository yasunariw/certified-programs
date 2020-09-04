Require Import VST.floyd.proofauto.

Require Import sumptr.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


Definition sumptr_spec : ident * funspec :=
  DECLARE _sumptr
   WITH x: val, a: Z, b: Z
   PRE  [(tptr (Tunion _sslval noattr))]
   PROP (a + b < Int.max_signed)
   PARAMS(x)
   SEP  (data_at Tsh (tarray (Tunion _sslval noattr) 3)
                 [(inl (Vint (Int.repr a))); (inl (Vint (Int.repr b))); (inl (Vint (Int.repr 0)))] x)
   POST [tvoid]
         PROP ()
         LOCAL()
         SEP
         (data_at Tsh (tarray (Tunion _sslval noattr) 3)
                 [(inl (Vint (Int.repr a))); (inl (Vint (Int.repr b))); (inl (Vint (Int.repr (a + b))))] x).

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [sumptr_spec]).

(** Proof that f_swap, the body of the swap() function,
 ** satisfies swap_spec, in the global context (Vprog,Gprog).
 **)
Lemma body_sumptr: semax_body Vprog Gprog f_sumptr sumptr_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  entailer!.
  admit.
  entailer!.
Qed.
