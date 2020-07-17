From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive tree (x : ptr) (s : seq nat) (h : heap) : Prop :=
| tree0 of x == 0 of
    s = nil /\ h = empty
| tree1 of x != 0 of
  exists l s1 r s2 v,
  exists heap_tree_alpha_513 heap_tree_alpha_514,
    s = [:: v] ++ s1 ++ s2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ heap_tree_alpha_513 \+ heap_tree_alpha_514 /\ tree l s1 heap_tree_alpha_513 /\ tree r s2 heap_tree_alpha_514
.
Definition treefree_type :=
  forall (x : ptr),
  {(s : seq nat)},
    STsep (
      fun h =>
          tree x s h,
      [vfun (_: unit) h =>
          h = empty      ]).
Program Definition treefree : treefree_type :=
  Fix (fun (treefree : treefree_type) x =>
    Do (
  if x == 0
  then
    ret tt
  else
    lx2 <-- @read ptr (x .+ 1);
    rx2 <-- @read ptr (x .+ 2);
    treefree lx2;;
    treefree rx2;;
    dealloc x;;
    dealloc (x .+ 1);;
    dealloc (x .+ 2);;
    ret tt
    )).
Next Obligation.
ssl_ghostelim_pre.
move=>s//=.
move=>H_tree_alpha_515.
move=>H_valid.
case: ifP=>H_cond.
case H_tree_alpha_515; rewrite H_cond=>//= _.
move=>[phi_tree_alpha_515].
move=>[->].
ssl_emp;
ssl_emp_post.
case H_tree_alpha_515; rewrite H_cond=>//= _.
move=>[lx] [s1x] [rx] [s2x] [vx].
move=>[heap_tree_alpha_513x] [heap_tree_alpha_514x].
move=>[phi_tree_alpha_515].
move=>[->].
move=>[H_tree_alpha_513x H_tree_alpha_514x].
ssl_read.
ssl_read.
put_to_head heap_tree_alpha_513x.
apply: bnd_seq.
apply: (gh_ex s1x).
apply: val_do=>//= _ ? ->; rewrite unitL=>_.
put_to_head heap_tree_alpha_514x.
apply: bnd_seq.
apply: (gh_ex s2x).
apply: val_do=>//= _ ? ->; rewrite unitL=>_.
ssl_dealloc.
ssl_dealloc.
ssl_dealloc.
ssl_emp;
ssl_emp_post.

Qed.
