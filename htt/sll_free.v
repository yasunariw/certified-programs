From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll0 of x == 0 of
    s = nil /\ h = empty
| sll1 of x != 0 of
  exists nxt s1 v,
  exists heap_sll_alpha_513,
    s = [:: v] ++ s1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ heap_sll_alpha_513 /\ sll nxt s1 heap_sll_alpha_513
.
Definition sll_free_type :=
  forall (x : ptr),
  {(s : seq nat)},
    STsep (
      fun h =>
          sll x s h,
      [vfun (_: unit) h =>
          h = empty      ]).
Program Definition sll_free : sll_free_type :=
  Fix (fun (sll_free : sll_free_type) x =>
    Do (
  if x == 0
  then
    ret tt
  else
    nxtx2 <-- @read ptr (x .+ 1);
    sll_free nxtx2;;
    dealloc x;;
    dealloc (x .+ 1);;
    ret tt
    )).
Next Obligation.
ssl_ghostelim_pre.
move=>s//=.
move=>H_sll_alpha_514.
move=>H_valid.
case: ifP=>H_cond.
case H_sll_alpha_514; rewrite H_cond=>//= _.
move=>[phi_sll_alpha_514].
move=>[->].
ssl_emp;
ssl_emp_post.
case H_sll_alpha_514; rewrite H_cond=>//= _.
move=>[nxtx] [s1x] [vx].
move=>[heap_sll_alpha_513x].
move=>[phi_sll_alpha_514].
move=>[->].
move=>H_sll_alpha_513x.
ssl_read.
put_to_head heap_sll_alpha_513x.
apply: bnd_seq.
apply: (gh_ex s1x).
apply: val_do=>//= _ ? ->; rewrite unitL=>_.
ssl_dealloc.
ssl_dealloc.
ssl_emp;
ssl_emp_post.

Qed.
