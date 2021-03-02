From Coq Require Import Relations Relation_Operators.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq order.
From Equations Require Import Equations.
From event_struct Require Import utilities wftype monads.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Set Equations Transparent.

Import Order.LTheory.
Local Open Scope order_scope.

Arguments clos_rtn1_rt {_ _ _ _}.
Arguments clos_rt_rt1n {_ _ _ _}.
Arguments clos_rt_rtn1 {_ _ _ _}.
Arguments clos_rt1n_rt {_ _ _ _}.
Arguments clos_refl {_}.
Arguments clos_refl_trans_n1 {_}.
Arguments clos_trans {_}.
Arguments clos_trans_n1 {_}.
Arguments reflexive {_}.
Arguments rtn1_trans {_ _ _ _ _}.
Arguments rtn1_refl {_ _ _}.

Section well_founded.

Definition sfrel {T : eqType} (f : T -> seq T) : rel T :=
  [rel a b | a \in f b].

Definition strict {T : eqType} (f : T -> seq T) : T -> seq T :=
  fun n => filter^~ (f n) (fun x => x != n).

Notation "f '\eq'" := (strict f) (at level 5, format "f '\eq'").

Lemma strict_in_sfrel {T : eqType} (f : T -> seq T) a b : 
  sfrel f\eq a b -> sfrel f a b.
Proof. by rewrite /strict /sfrel /= mem_filter => /andP[]. Qed.

Lemma in_strict {T : eqType} (f : T -> seq T) a b :
  (a != b) -> (a \in f b) -> ((sfrel f\eq) a b).
Proof. by rewrite /sfrel /strict /= mem_filter => -> ->. Qed. 

Hint Resolve strict_in_sfrel in_strict : core.

Context {disp : unit} {T : wfType disp}.

Variable (f : T -> seq T).

Hypothesis descend : forall x n, x \in f n -> x <= n.

Lemma strict_lt n k : k \in f\eq n -> k < n.
Proof. by rewrite mem_filter lt_neqAle => /andP[] -> /descend ->. Qed.

Hint Resolve strict_lt : core.

Lemma rel_sublt a b : (sfrel f\eq) a b -> a < b.
Proof. rewrite/sfrel /=. exact: strict_lt. Qed.

Definition s_up_set_aux n (g : forall x : T, x < n -> seq T) := 
  let ys := f\eq n in 
  let ps := flatten (map^~ ys (fun x => 
  if x \in ys =P true is ReflectT pf then
    g x (strict_lt _ _ pf)
  else
    [::]
)) in ys ++ ps.

Arguments s_up_set_aux /.

(* Computation of the strict upward set of a given element
 * w.r.t relation R derived from function `f`,
 * i.e. s_up_set(x) = { y | x R y } 
 *)
Equations s_up_set (n : T) : seq T by wf n (<%O : rel T) :=
  s_up_set n := s_up_set_aux n s_up_set.

Definition t_closure (a b : T) : bool := a \in s_up_set b.

Lemma clos_trans_n1_lt a b : clos_trans_n1 (sfrel f\eq) a b -> a < b.
Proof.
  rewrite/sfrel //=.
  elim=> [x| x y xfy acx ax]. auto.
  apply: lt_trans; first exact: ax. auto.
Qed.

Lemma clos_trans_lt a b : clos_trans (sfrel f\eq) a b -> a < b.
Proof. move=> cab. by apply /clos_trans_n1_lt /clos_trans_tn1. Qed.

(* Transitive closure reflection lemma *)
Lemma t_closure_n1P a b : 
  reflect (clos_trans_n1 (sfrel f\eq) a b) (t_closure a b).
Proof.
  rewrite /t_closure. funelim (s_up_set b)=> /=. 
  apply /(iffP idP); rewrite mem_cat /sfrel /=.
  { move=> /orP[|/flatten_mapP[x]] //; first exact: tn1_step.
    case: eqP=> // S /strict_lt/X/(_ a x erefl) /[apply]. exact: tn1_trans. }
  move: X=> /[swap] [[?->//|y ? /[dup] ? L /[swap]]].
  move=> /[apply] ?; apply/orP; right; apply/flatten_mapP.
  exists y=> //. case: eqP; auto.
Qed.

Lemma t_closureP a b :
  reflect (clos_trans (sfrel f\eq) a b) (t_closure a b).
Proof.
  apply /(iffP idP) => [/t_closure_n1P| cab]; first exact: clos_tn1_trans.
  apply /t_closure_n1P. exact: clos_trans_tn1.
Qed.

Lemma t_closure_lt a b : t_closure a b -> a < b.
Proof. by move=> /t_closureP /clos_trans_lt. Qed.

Lemma t_closure_trans : transitive t_closure.
Proof.
  move=> b a c /t_closureP ab /t_closureP bc.
  apply /t_closureP /t_trans; first exact: ab. exact: bc.
Qed.

Lemma t_closure_antisym : antisymmetric t_closure.
Proof.
  move=> a b /andP[] /t_closure_lt ab /t_closure_lt ba. apply /eqP.
  by rewrite eq_le !ltW.
Qed.

(* Computation of the (non-strict) upward set of a given element
 * w.r.t relation R derived from function `f`,
 * i.e. up_set(x) = { y | x = y \/ x R y } 
 *)
Definition up_set a := a :: s_up_set a.

Definition rt_closure a b := a \in up_set b. 

Lemma rt_closure_reflP a b :
  reflect (clos_refl t_closure a b) (rt_closure a b).
Proof.
  rewrite /rt_closure /up_set. funelim (s_up_set b).
  apply /(iffP idP).
  { rewrite -cat_cons mem_cat in_cons => /orP[/orP[/eqP ->|]|].
    { exact: r_refl. }
    { constructor. rewrite /t_closure. funelim (s_up_set n).
      by rewrite mem_cat b. }
    constructor. rewrite /t_closure. funelim (s_up_set n).
    by rewrite mem_cat b. }
  case=> [b |]; last exact: mem_head.
  rewrite /t_closure in_cons. by funelim (s_up_set b) => ->.
Qed.

Lemma clos_t_clos_rt {R : rel T} a b :
  clos_trans R a b -> clos_refl_trans T R a b.
Proof.
  elim=> [|c d e ctcd crtcd ctde crtce]; first by constructor.
  apply /rt_trans; first exact: crtcd. exact: crtce.
Qed.

Lemma filter_clos_sub a b :
  clos_trans_n1 (sfrel f\eq) a b -> clos_trans_n1 (sfrel f) a b.
Proof.
  elim=> [c sfac | c d sfcd ctacn ctac].
  { apply /tn1_step. move: sfac. auto. }
  apply /tn1_trans; last exact: ctac. move: sfcd. auto.
Qed.

Lemma refl_trans_refl_rt a b :
  clos_refl_trans_n1 (sfrel f) a b -> clos_refl t_closure a b.
Proof.
  rewrite /sfrel /=. 
  elim=> [|c d sfcd crtac /rt_closure_reflP rtac]; first exact: r_refl.
  case: (c =P d) => [<-| /eqP neq].
  { apply /rt_closure_reflP. 
    case: (rt_closure_reflP a c rtac) => [e|]; last exact: mem_head.
    by rewrite /rt_closure /up_set /t_closure in_cons => ->. }
  constructor. apply /t_closureP. elim: crtac => //.
  case: (a =P c) => [->|nac].
  { constructor. auto. }
  apply /t_trans.
  { move: (rt_closure_reflP a c rtac) => /clos_reflE. case; first by [].
  exact: t_closureP. }
  constructor. auto.
Qed.

Lemma rt_closure_refl a : rt_closure a a.
Proof. exact: mem_head. Qed.

(* Reflexive-transitive closure reflection lemma *)
Lemma rt_closure_n1P a b :
  reflect (clos_refl_trans_n1 (sfrel f) a b) (rt_closure a b).
Proof.
  apply /(iffP idP).
  { move=> /rt_closure_reflP. case => [c /t_closure_n1P cac|]; last by constructor.
    by apply /clos_rt_rtn1 /clos_t_clos_rt /clos_tn1_trans /filter_clos_sub. }
  by move=> /refl_trans_refl_rt /rt_closure_reflP.
Qed.

Lemma rt_closureP a b :
  reflect (clos_refl_trans T (sfrel f) a b) (rt_closure a b).
Proof.
  apply /(iffP idP).
  { move=> /rt_closure_n1P. exact: clos_rtn1_rt. }
  move=> rtab. apply /rt_closure_n1P. exact: clos_rt_rtn1.
Qed.

Lemma rt_closure_trans : transitive rt_closure.
Proof.
  move=> b a c /rt_closureP ab /rt_closureP bc.
  apply/rt_closureP /rt_trans; first exact: ab. done.
Qed.

Lemma rt_closure_le a b : rt_closure a b -> a <= b.
Proof.
  rewrite /rt_closure /up_set in_cons => /orP[/eqP -> //|] asb.
  rewrite le_eqVlt. apply /orP. right. by apply /t_closure_lt.
Qed.

Lemma rt_closure_antisym : antisymmetric rt_closure.
Proof.
  move=> a b /andP[] /rt_closure_le ab /rt_closure_le ba. apply /eqP.
  by rewrite eq_le ab ba.
Qed.

Lemma rt_closure_subrel : subrel (sfrel f) rt_closure.
Proof. move=> a b sfrel; exact/rt_closure_n1P/(rtn1_trans sfrel rtn1_refl). Qed.

End well_founded.

Arguments rt_closure_n1P {disp T f descend a b}.
