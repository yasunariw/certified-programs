Require Import VST.floyd.proofauto.

Require Import listfree4.
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

Inductive lseg_card : Set :=
    | lseg_card_0 : lseg_card
    | lseg_card_1 : lseg_card -> lseg_card.

Fixpoint lseg (x: val) (s: (list val)) (self_card: lseg_card) : mpred := match self_card with
    | lseg_card_0  =>  !!(x = nullval) && !!(s = []) && emp
    | lseg_card_1 _alpha_513 => 
      EX v : Z,
      EX s1 : (list val),
      EX nxt : val,
               !!(~ (x = nullval)) && !!(s = ([(Vint (Int.repr v))] ++ s1)) &&
               (data_at Tsh (tarray (Tunion _sslval noattr) 2)
                        [inl (Vint (Int.repr v)); inr nxt] x) * (lseg nxt s1 _alpha_513)
end.

Lemma lseg_valid_pointer_or_nullP p s size:
  lseg p s size |-- !! is_pointer_or_null p.
Proof.
  destruct size as [|size]; simpl.
  - entailer!.
  - Intros nxt v s'. entailer!.
Qed.

Lemma lseg_valid_pointerP p s size:
  lseg p s size |-- valid_pointer p.
Proof.
  destruct size as [|size]; simpl.
  - entailer!.
  - Intros nxt v s'. entailer!.
Qed.


Lemma lseg_pointer_case0P p s size:
  lseg p s size |-- !!(p=nullval <-> size=lseg_card_0).
Proof.
  destruct size as [|size]; simpl.
  - entailer!; intuition.
  - {
      Intros nxt v s'.
      entailer!.
      split.
      - intro H5; case (H H5).
      - discriminate. 
    }
Qed.


Lemma lseg_size_negP p s size:
  lseg p s size |-- !! ((p <> nullval) <-> (size <> lseg_card_0)).
Proof.
  destruct size as [| size]; simpl.
  - entailer!.
    split.
    intro H; case (H (eq_refl nullval)).
    auto.
  -
    Intros nxt v s'.
    entailer!.
    split.
    discriminate.
    auto.
Qed.

Lemma lseg_local_factsP p s size :
  lseg p s size |-- !!((((p <> nullval) -> (size <> lseg_card_0))) /\ ((p=nullval -> size = lseg_card_0) /\
                         ((is_pointer_or_null p)
                          ))).
Proof.
  rewrite prop_and.
  apply andp_right.
  pose proof lseg_size_negP; entailer!; try destruct H0; entailer!.
  rewrite prop_and.
  apply andp_right.
  pose proof (lseg_pointer_case0P); entailer!; try destruct H0; entailer!.
  apply lseg_valid_pointer_or_nullP.
Qed.

Definition free_spec :=
  DECLARE _free
          WITH ty: type, x: val
                              PRE  [ (tptr tvoid) ]
                              PROP()
                              PARAMS(x)
                              SEP (data_at_ Tsh ty x)
                              POST [ Tvoid ]
                              PROP()
                              LOCAL()
                              SEP (emp).

Definition listfree_spec :=
  DECLARE _listfree
   WITH x: val, s: (list val), _alpha_514: lseg_card
   PRE [ (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null(x) )
   PARAMS(x)
   SEP ((lseg x s _alpha_514))
   POST[ tvoid ]
   PROP(  )
   LOCAL()
   SEP ().

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [listfree_spec; free_spec]).

(** Proof that f_listfree, the body of the listfree() function,
 ** satisfies listfree_spec, in the global context (Vprog,Gprog).
 **)

Hint Resolve lseg_valid_pointerP: valid_pointer.
Hint Resolve lseg_local_factsP : saturate_local.


Ltac ssl_open :=
  match goal with
  | [ X : ?x = ?x -> _ |- _ ] =>
    let H := fresh in
    pose proof (X (eq_refl x)) as H; rewrite H; clear H; simpl
  | _ => fail
  end.
Ltac ssl_dispatch_card :=
      match goal with
      | [ X : ?x, Y: ?x -> ?y <> ?z |- _]  =>
        let H := fresh in
        pose proof (Y X) as H; generalize H; try case y; try intuition; try eexists; auto
      | _ => fail
      end.

Ltac ssl_card H name :=
  match goal with
    | [ H : _ = _ |- _] => rewrite H; simpl lseg
    | [ H : exists _ : _, _ = _ |- _] =>
      let g := fresh in
      case H => name g; rewrite g; clear g; simpl lseg
    | _ => fail
  end.


Lemma body_listfree : semax_body Vprog Gprog f_listfree listfree_spec.
Proof.
  start_function. 
  forward_if.
  - assert_PROP (_alpha_514 = lseg_card_0) as H1. { entailer!; ssl_dispatch_card. }
    ssl_card H1 none.
    forward; entailer.
  - assert_PROP (exists alpha', (_alpha_514 = lseg_card_1 alpha')) as H2. { entailer!; ssl_dispatch_card. }
    ssl_card H2 _alpha_515.
    Intros vx s1x nxtx.
    assert_PROP (is_pointer_or_null nxtx) as Hnxtx. { entailer!. }
    forward.
    forward_call (nxtx, s1x, _alpha_515).
    forward_call (tarray (Tunion _sslval noattr) 2, x).
    forward.
Qed.

