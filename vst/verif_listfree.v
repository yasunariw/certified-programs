Require Import VST.floyd.proofauto.
(* Require Export VST.floyd.Funspec_old_Notation. *)
Require Import listfree.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


(*

Key difficulties encountered while translating the SuSLik spec:
- SuSLik's idealized memory model doesn't care about mixing types in a collection, while C does.

  Hence, a lot of creative interpretation went into translating the listfree program synthesized by
  SuSLik into a valid C program.

- We would have liked to encode predicates as inductive propositions using the Inductive keyword. But VST was more happy
  with encoding them using Fixpoints.
- To convince Coq that our fixpoints are well-founded, we needed to add a strictly decreasing size parameter - another
  deviation from the SuSLik spec.

(* Functional spec of this program.  *)

(* First pass at lseg; is not well-founded because `x = y` is not a properly decreasing argument *)
Fail Fixpoint lseg (x: val) (null: val) (s: list val) : mpred :=
  if eq_dec x null
  then !!(x = null) && !! (s = []) && emp
  else !! not(x = null) &&
          EX nxt:val, EX v:val,  EX s':(list val),
            !!(s = v :: s') &&
            data_at Tsh (tptr tvoid) v x *
            data_at Tsh (tptr tvoid) nxt (offset_val 4 x) *
            lseg nxt null s'.


(* This version is well-defined and thus accepted by Coq, but is invalid because it does not match lseg's specification *)
Fixpoint lseg' (x: val) (null: val) (s: list val) : mpred :=
  match s with
  | [] => !!(x = null) && emp
  | v :: s' =>
    !!not(x = null) &&
    EX nxt:val,
    data_at Tsh (tptr tvoid) v x * data_at Tsh (tptr tvoid) nxt (offset_val 4 x) * lseg' nxt null s'
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

(* Print offset_val. *)

(* Fixes y to zero; however this doesn't work because it does not enforce the constraint length(s) = size *)
Fixpoint lseg''' (x: val) (s: list val) (size: nat) : mpred :=
  match size with
  | S size'  =>
    !!not(x = nullval) &&
      EX nxt:val, EX v:val, EX s': list val,
    data_at Tsh (tptr tint) v x * data_at Tsh (tptr tint) nxt (offset_val 4 x) * lseg''' nxt s' size'
  | O  => !!(x = nullval) && !!(s = [])  && emp
  end.

Fixpoint lseg'''' (x: val) (s: list val) (size: nat) : mpred :=
  match size with
  | S size'  =>
      EX nxt:val, EX v:val, EX s': list val,
    !!not(x = nullval) &&
    !! (s = v :: s') &&
    data_at Tsh (tptr tint) v x * data_at Tsh (tptr tint) nxt (offset_val 4 x) * lseg''' nxt s' size'
  | O  => !!(x = nullval) && !!(s = [])  && emp
  end.
*)

Fixpoint lseg (x: val) (s: list val) (size: nat) : mpred :=
  match size with
  | S size'  =>
    EX nxt:val, EX v:val, EX s': list val,
    !!not(x = nullval) &&
     !! (s = v :: s') &&
      data_at Tsh (tarray (tptr tint) 2) (v :: nxt :: []) x *
      lseg nxt s' size'
  (*data_at Tsh (tptr tint) v x * data_at Tsh (tptr tint) nxt (offset_val 4 x) * lseg nxt s' size*)
  | O  => !!(x = nullval) && !!(s = nil)  && emp
  end.

(* helper obvious facts *)
Lemma lseg_lenP x s size :
  lseg x s size |-- !!(size = length s).
Proof.
  revert s x.
  induction size.
  - simpl. entailer!.
  - {
      simpl. intros s x. Intros nxt v s'.
      revert H0; case s.
      - simpl; intro H1; case (@nil_cons _ v s' H1).
      - {
          intros v_2 s'_2 H1; pose proof (@cons_inv _ _ _ _ _ H1) as H2.
          destruct H2 as [H3 H4].
          rewrite H3; rewrite H4; clear H3 H4 H1 v_2 s'_2; simpl.
          pose proof (@cancel_left (data_at Tsh (tarray (tptr tint) 2) [v; nxt] x) _  _ (IHsize s' nxt) ).
          entailer!.
        }
    }
Qed.


Lemma lseg_valid_pointer_or_nullP p s size:
  lseg p s size |-- !! is_pointer_or_null p.
Proof.
  destruct size as [|size]; simpl.
  - entailer!.
  - Intros nxt v s'. entailer!.
Qed.

Lemma lseg_valid_pointerP p s size:
  lseg p s size |--  valid_pointer p.
Proof.
  destruct size as [|size]; simpl.
  - entailer!.
  - Intros nxt v s'. entailer!.
Qed.

Lemma lseg_pointer_contentsP p s size:
  lseg p s size |-- !!(p=nullval <-> s=nil).
Proof.
  destruct size as [|size]; simpl.
  - entailer!; intuition.
  - {
      Intros nxt v s'.
      entailer!.
      split.
      - intro H3; case (H H3).
      - intro H3.
        case (@nil_cons _ _ _ (@eq_sym _ _ _ H3 )).
    }
Qed.

Lemma lseg_size_negP p s size:
  lseg p s size |-- !! ((p <> nullval) <-> (gt size 0)).
Proof.
  destruct size as [| size]; simpl.
  - entailer!.
    split.
    intro H; case (H (eq_refl nullval)).
    intro H; case (gt_irrefl 0 H).
  -
    Intros nxt v s'.
    entailer!.
    split.
    intro; apply gt_Sn_O.
    auto.
Qed.
    

Lemma lseg_local_factsP p s size :
  lseg p s size |-- !!( (size = length s) /\ ((p=nullval -> s=nil) /\
                                              ((is_pointer_or_null p) /\
                                               (((p <> nullval) -> (gt size 0)))))).
Proof.
  rewrite prop_and.
  apply andp_right.
  apply lseg_lenP.
  rewrite prop_and.
  apply andp_right.
  pose proof lseg_pointer_contentsP; entailer!; try destruct H0; entailer!.
  rewrite prop_and.
  apply andp_right.
  apply lseg_valid_pointer_or_nullP.
  pose proof lseg_size_negP; entailer!; try destruct H0; entailer!.
Qed.

Lemma is_pointer_or_null_not_null:
 forall x, is_pointer_or_null x -> x <> nullval -> isptr x.
Proof.
intros.
 destruct x; try contradiction. hnf in H; subst i. contradiction H0; reflexivity.
 apply I.
Qed.


Definition listfree_spec :=
  DECLARE _listfree
          WITH s: list val, x: val
                                 PRE  [ (tptr (tptr tint)) ]
                                 PROP()
                                 PARAMS(x)
                                 SEP (lseg x s (length s))
                                 POST [ Tvoid ]
                                 PROP()
                                 LOCAL()
                                 SEP (emp).

Definition free_spec :=
  DECLARE _free
          WITH x: val, s: list val
                              PRE  [ (tptr tvoid) ]
                              PROP()
                              PARAMS(x)
                              SEP (data_at Tsh (tarray (tptr tint) 2) s x)
                              POST [ Tvoid ]
                              PROP()
                              LOCAL()
                              SEP (emp).


(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [listfree_spec; free_spec]).

(** Proof that f_listfree, the body of the listfree() function,
 ** satisfies listfree_spec, in the global context (Vprog,Gprog).
 **)
From mathcomp Require Import ssreflect.
Hint Resolve lseg_valid_pointerP: valid_pointer.
Hint Resolve lseg_local_factsP : saturate_local.

Lemma body_listfree : semax_body Vprog Gprog f_listfree listfree_spec.
Proof.
  start_function. 
  forward_if.
  - forward.
    (* x = null *)
    move: (H0 (eq_refl nullval)) => ->; (* lseg (x, nil, 0) *) simpl.
    entailer!.
  - assert_PROP ((Datatypes.length s) > 0)%nat. { entailer!. }
    case: s H0; first by simpl=>/gt_irrefl.
    simpl lseg => y ys _.
    Intros nxt v s'.
    forward. (* _t = x[1] *)
    forward. (* nxt2 = _t *)
    deadvars!. (* drop temporary variable *)
    forward_call (s', nxt).
    * entailer!; rewrite H3; entailer!.
    * forward_call (x, [v; nxt]).
      entailer!.
Qed.

