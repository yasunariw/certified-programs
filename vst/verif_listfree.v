
Require Export VST.floyd.Funspec_old_Notation.
Require Import VST.floyd.proofauto.
Require Import listfree.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


(*

This proof doesn't compile!

Key difficulties encountered while translating the SuSLik spec:
- SuSLik's idealized memory model doesn't care about mixing types in a collection, while C does.

  Hence, a lot of creative interpretation went into translating the listfree program synthesized by
  SuSLik into a valid C program.

- We would have liked to encode predicates as inductive propositions using the Inductive keyword. But VST was more happy
  with encoding them using Fixpoints.
- To convince Coq that our fixpoints are well-founded, we needed to add a strictly decreasing size parameter - another
  deviation from the SuSLik spec.

Possible next steps:
- VST's powerful 'forward' and 'entailer!' tactics make extensive use of hint databases. A successful proof probably needs
  us to add some lemmas related to the lseg fixpoint to the hint database.
- A useful reference might be the '/progs/list_dt.v' file contained in the VST repository. It's a massive library of lemmas
  that define a theory of linked list segments (albeit a slightly different definition than SuSLik's). Their version of lseg
  is used to verify some programs, like 'progs/verif_append.v'. The question is, do we need to do something similar for every
  inductive predicate definable in SuSLik, or is there a better way?

*)

(* Unsuccessful result below...... *)


(* Functional spec of this program.  *)

(* First pass at lseg; is not well-founded because `x = y` is not a properly decreasing argument *)
(* Fixpoint lseg (x: val) (y: val) (s: list val) : mpred := *)
(*   if eq_dec x y *)
(*   then !!(x = y) && !! (s = []) && emp *)
(*   else !! not(x = y) && *)
(*           EX nxt:val, EX v:val,  EX s':(list val), *)
(*             !!(s = v :: s') && *)
(*             data_at Tsh (tptr tvoid) v x * *)
(*             data_at Tsh (tptr tvoid) nxt (offset_val 4 x) * *)
(*             lseg nxt y s'. *)


(* This version is well-defined and thus accepted by Coq, but is invalid because it does not match lseg's specification *)
Fixpoint lseg' (x: val) (y: val) (s: list val) : mpred :=
  match s with
  | [] => !!(x = y) && emp
  | v :: s' =>
    !!not(x = y) &&
    EX nxt:val,
    data_at Tsh (tptr tvoid) v x * data_at Tsh (tptr tvoid) nxt (offset_val 4 x) * lseg' nxt y s'
  end.

(* This well-defined version makes use of an auxiliary heap size indicator that is the fixpoint's decreasing argument *)
Fixpoint lseg'' (x: val) (y: val) (s: list val) (size: nat) : mpred :=
  match size with
  | S size'  =>
    !!not(x = y) &&
      EX nxt:val, EX v:val, EX s': list val,
    data_at Tsh (tptr tvoid) v x * data_at Tsh (tptr tvoid) nxt (offset_val 4 x) * lseg'' nxt y s' size'
  | O  => !!(x = y) && !!(s = [])  && emp
  end.

Print offset_val.

(* Fixes y to zero; however this doesn't work because it does not enforce the constraint length(s) = size *)
Fixpoint lseg''' (x: val) (s: list val) (size: nat) : mpred :=
  match size with
  | S size'  =>
    !!not(x = nullval) &&
      EX nxt:val, EX v:val, EX s': list val,
    data_at Tsh (tptr tint) v x * data_at Tsh (tptr tint) nxt (offset_val 4 x) * lseg''' nxt s' size'
  | O  => !!(x = nullval) && !!(s = nil)  && emp
  end.

Fixpoint lseg (x: val) (s: list val) (size: nat) : mpred :=
  match size with
  | S size'  =>
    !!not(x = nullval) &&
      EX nxt:val, EX v:val, EX s': list val,
      data_at Tsh (tarray (tptr tint) 2) (v :: nxt :: []) x * lseg nxt s' size'
    (*data_at Tsh (tptr tint) v x * data_at Tsh (tptr tint) nxt (offset_val 4 x) * lseg nxt s' size'*)
  | O  => !!(x = nullval) && !!(s = nil)  && emp
  end.
     
Definition listfree_spec :=
   DECLARE _listfree
  WITH s: list val, x: val, size: nat
  PRE  [ _x OF (tptr (tptr tint)) ]
    PROP(size = length s)
    LOCAL(temp _x x)
    SEP (lseg x s size)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (emp).

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [listfree_spec]).

(** Proof that f_listfree, the body of the listfree() function,
 ** satisfies listfree_spec, in the global context (Vprog,Gprog).
 **)

Lemma body_listfree : semax_body Vprog Gprog f_listfree listfree_spec.
Proof.
  start_function.
  forward_if.
  - 
    (*
    move: PNx; subst v. clear H.
    case: x=>//=[? ->/=|b pf _].
    apply: denote_tc_test_eq_split=>//.
    rewrite /valid_pointer /valid_pointer' /=.
    Search _ (predicates_hered.prop (_ = _)).
    Search _ (_ |-- _) (TT).
    Check  denote_tc_test_eq.
    have X: (denote_tc_test_eq (Vint Int.zero) (Vint (Int.repr 0)) = TT).
    Search _ (denote_tc_test_eq).
    Check (denote_tc_test_eq_split (lseg2 (Vint Int.zero) s) (Vint Int.zero) (Vint (Int.repr 0))).
    by rewrite X; apply: TT_right. *)

    move: PNx.
    
    admit.
  - unfold MORE_COMMANDS, abbreviate.
    forward.
    rewrite lseg_null.
    entailer!.
    exact PNx.
  - Fail forward.
    forward.
Qed.