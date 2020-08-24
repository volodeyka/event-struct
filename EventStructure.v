From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path.
From Equations Require Import Equations.
From event_struct Require Import utilities.

Definition var := nat.
Definition tid := nat.

Section prime_event_structure.
Context {val : eqType}.

(* labels for events in event structure *)
Inductive label :=
| R : tid -> var -> val -> label
| W : tid -> var -> val -> label.

Definition is_read  l := if l is (R _ _ _) then true else false.

Definition is_write l := if l is (W _ _ _) then true else false.

Definition compatible w r := 
  match w, r with
  | (W _ x a), (R _ y b) => (x == y) && (a == b)
  | _, _                 => false
  end.

Definition thread_id l := 
  match l with
  |  (R t _ _) | (W t _ _) => t
  end.

Definition advance {N} (m : 'I_N) (k : 'I_m) : 'I_N :=
  widen_ord (ltnW (ltn_ord m)) k.

Lemma nat_of_advance {N} (m : 'I_N) (k : 'I_m) : 
 advance m k = k :> nat.
Proof. by case: m k => ??[]. Qed.


Structure exec_event_struct := Pack {
  n  : nat;
  lab  : 'I_n -> label;
  pred : forall (m : 'I_n), option 'I_m;
  rff : forall k : 'I_n, is_read (lab k) ->
                  {l : 'I_k | (compatible (lab (advance k l)) (lab k))};
}.

Section Cause_Conflict.
Variables (e : exec_event_struct) (l : label).

Notation N := (n e).
Notation lab := (lab e).
Notation pred := (pred e).
Notation rff := (rff e).
Notation ltn_ind := (@ltn_ind N).

Definition opred x : option 'I_N :=
  if (pred x) is some y 
    then some (advance x y) 
  else None.

(*Lemma opred_spec*)
(*Lemma orff_spec*)
(*Lemma add_opred_spec*)
(*Lemma add_orff_spec*)

Definition rpred x y := opred x == some y.


Definition orff (n : 'I_N) : option 'I_N :=
  (if is_read (lab n) as r return (is_read (lab n) = r -> _)
    then fun pf => some (advance n (sval (rff n pf)))
  else fun=> None) erefl.

Lemma orff_le n m: orff n = some m -> (m < n)%N.
Proof.
rewrite/orff.
case: {2}(is_read (lab n)) {-1}(@erefl _ (is_read (lab n))) erefl=> {2 3}->// ?[].
case: (rff _ _)=>/= [[? L _]]<-. by rewrite nat_of_advance.
Qed.

Arguments advance : simpl never.

Lemma pred_le n m: opred n = some m -> (m < n)%N.
Proof. 
rewrite /opred. case: (pred n) =>//[[??[<-]]]. by rewrite nat_of_advance.
Qed.

Definition rf m n := orff n == some m.

Definition cause := connect [rel m n | rf m n || rpred n m].

Lemma rpred_cause n m: rpred n m -> cause m n.
Proof. move=> H. apply/connect1. by rewrite/= H. Qed.

Lemma rff_cause n m: rf m n -> cause m n.
Proof. move=> H. apply/connect1. by rewrite/= H. Qed.

Lemma refl_cause: reflexive cause.
Proof. exact: connect0. Qed.

Lemma trans_cause: transitive cause.
Proof. exact: connect_trans. Qed.

Lemma cause_decr n m: (n != m) -> cause n m ->
  exists k, (((rpred m k) || (orff m == some k)) && cause n k).
Proof.
move=> nm /connectP[].
elim/last_ind=> /=.
- move=> _ eq. move: eq nm=>-> /eqP nn. by exfalso.
move=> x a IHx. rewrite last_rcons rcons_path=> /swap-> /andP[*].
exists (last n x). apply/andP. split=> //=; first by rewrite orbC.
apply/connectP. by exists x.
Qed.

Lemma cause_sub_leq n m : cause n m -> n <= m.
Proof.
move: m. elim/ltn_ind=> m IHm cmn.
case H: (n == m); move: H.
- by move=> /eqP ->.
move/negbT/cause_decr/(_ cmn)=> [] k /andP[/orP[/eqP /pred_le|/eqP /orff_le]] km cnk;
apply/ltnW/(@leq_ltn_trans k n m)=> //; exact: (IHm k km cnk).
Qed.

Lemma anti_cause: antisymmetric cause.
Proof.
move=> x y /andP[/cause_sub_leq xy /cause_sub_leq yx].
by apply/ord_inj/anti_leq/andP.
Qed.

Definition lt_of_cause x y := (y != x) && (cause x y).

Lemma lt_neq_le : forall x y, lt_of_cause x y = (y != x) && (cause x y).
Proof. done. Qed.

Definition orderMixin :=
  LePOrderMixin lt_neq_le refl_cause anti_cause trans_cause.

Definition ev_display : unit.
Proof. exact: tt. Qed.

Canonical predrderType := POrderType ev_display 'I_N orderMixin.


Import Order.LTheory.
Open Scope order_scope.
Import Order.NatOrder.

(*Notation "x <=c y" := (@Order.le ev_display _ x y) (at level 10).*)

(* base of conflict relation *)
Definition pre_conflict n m := [&& (n != m), opred n == opred m & (thread_id (lab n) == thread_id (lab m))].

Equations conflict (n m : 'I_N) : bool by wf (n + m) lt :=
conflict n m := [|| pre_conflict n m,
(match opred n as ox return (opred n = ox -> _) with
| some x => fun=> conflict x m
| _      => fun=> false
end erefl),
(match opred m as ox return (opred m = ox -> _) with
| some x => fun=> conflict n x
| _      => fun=> false
end erefl),
(match orff n as ox return (orff n = ox -> _) with
| some x => fun=> conflict x m
| _      => fun=> false
end erefl) |
(match orff m as ox return (orff m = ox -> _) with
| some x => fun=> conflict n x
| _      => fun=> false
end erefl)].

Next Obligation. move: e0=> /pred_le. ssrnatlia. Qed.
Next Obligation. move: e0=> /pred_le. ssrnatlia. Qed.
Next Obligation. move: e0=> /orff_le. ssrnatlia. Qed.
Next Obligation. move: e0=> /orff_le. ssrnatlia. Qed.

Notation "a # b" := (conflict a b) (at level 10).

(* may be should merge this two lemmas *)
Lemma consist_conflictl {n1 n2 n3 : 'I_N}: n1 <= n2 -> n1 # n3 -> n2 # n3.
Proof.
(* proof using second defition of conflict *)
(*move=> C /conflictP [x [y/and3P[*]]]. apply/conflictP. exists x, y. apply/and3P;
split=>//. by apply/(trans_cause n1).*)
(* proof using first one *)
elim/ltn_ind: n2=> n2 IHn2. case EQ: (n1 == n2); move: EQ;
first by move=>/eqP->. move=> /negbT/cause_decr I /I [k /andP[O L C]].
have/IHn2/(_ L C): (k < n2)%N; first by move: O=> /orP[/eqP/pred_le|/eqP/orff_le].
move: O. by apply_funelim (n2 # n3)=> n m /orP[]/eqP->->.
Qed.

Lemma consist_conflictr {n1 n2 n3}: n1 <= n2 -> n3 # n1 -> n3 # n2.
Proof.
(* proof using second defition of conflict *)
(*move=> C /conflictP [x [y/and3P[*]]]. apply/conflictP. exists x, y. apply/and3P;
split=>//. by apply/(trans_cause n1).*)
(* proof using first one *)
elim/ltn_ind: n2=> n2 IHn2. case EQ: (n1 == n2); move: EQ;
first by move=>/eqP->. move=> /negbT/cause_decr I /I [k /andP[O L C]].
have/IHn2/(_ L C): (k < n2)%N; first by move: O=> /orP[/eqP/pred_le|/eqP/orff_le].
move: O. by apply_funelim (n3 # n2)=> n m /orP[]/eqP->->.
Qed.
(* we cant use second definition here because we need this lemmas in         *)
(* conflictP below                                                           *)

Lemma conflictP n m : 
  reflect (exists x y, [&& x <= n, y <= m & pre_conflict x y]) (n # m).
Proof.
elim/ltn_ind: n m=> n IHn. elim/ltn_ind=> m IHm. apply: (iffP idP).
- move: IHm IHn. apply_funelim (n # m)=> {n m} n m IHm IHn /or4P[?|||/orP[|]];
  [by exists n, m; rewrite !le_refl | case H : (opred n)|
  case H : (opred m)|case H : (orff n)|case H : (orff m)]=>//; move: (H).
  move/pred_le/IHn => R {}/R [x [y /and3P[]]].
  2: move/pred_le/IHm => R {}/R [x [y /and3P[?]]].
  3: move/orff_le/IHn => R {}/R [x [y /and3P[]]].
  4: move/orff_le/IHm => R {}/R [x [y /and3P[?]]].
  1,2: move: H=> /eqP/rpred_cause C /trans_cause/(_ C) *. 
  3,4: move: H=> /eqP/rff_cause C /trans_cause/(_ C) *.
  1-4: exists x, y; by apply/and3P; split.
case=> [x [y/and3P[?? P]]]. apply/(@consist_conflictl x)=>//.
apply/(@consist_conflictr y)=>//. move: P. by apply_funelim (x # y)=> ??->.
Qed.

Lemma symm_conflict: symmetric conflict.
Proof.
(* proof using second conflict definition *)
move=> n m. apply/Bool.eq_true_iff_eq. suff H: forall a b, a # b -> b # a;
first by split=> /H. move=> a b /conflictP [x [y/and3P[??/and3P[*]]]]. apply/conflictP.
exists y, x. apply/and3P; split=> //. apply/and3P; split; by rewrite eq_sym.
(* proof using first one *)
(*move=> n m. apply/Bool.eq_true_iff_eq. suff H: forall a b, a # b -> b # a;
first by split=> /H. move=> {m n}. elim/ltn_ind=> n IHn. elim/ltn_ind=> m.
move: IHn. apply_funelim (n # m)=> a b. apply_funelim (b # a)=> {n m} n m IHm IHn.
move=> /or4P[|||/orP[|]]. rewrite /pre_conflict.
- by rewrite (eq_sym n m) (eq_sym (osval (pred n)) _) (eq_sym (thread_id (lab n)) _)=>->.
- case EQ: (osval (pred m))=>//. by move: EQ=> /pred_le/IHm/(_ n) I /I->.
- case EQ: (osval (pred n))=>//. by move: EQ=> /pred_le/IHn I /I->.
- case EQ: (orff m)=>//. by move: EQ=> /orff_le/IHm/(_ n) I /I->.
case EQ: (orff n)=>//. by move: EQ=> /orff_le/IHn I /I->.*)
Qed.

Definition consistance := [forall n, [forall m, (orff m == some n) ==> ~~ m # n]].

Hypothesis (consist : consistance).

Lemma rff_consist n m : (orff m = some n) -> ~~ m # n.
Proof. 
move/forallP: consist=> /(_ n)/forallP/(_ m)/implyP I ?; by apply/I/eqP.
Qed.


(* the proof is so big because we need to analyze of cases in conflict         *)
(* definition                                                                  *)
Lemma no_confl_cause n m: n <= m -> ~~ (n # m).
Proof.
set rc := rff_consist.
move: m n. elim/ltn_ind=> b IHn. elim/ltn_ind=> a IHm C. apply/negP=> CN.
pose c := a. pose d := b. have aEc: a = c; first by rewrite/c. 
have bEd: b = d; first by rewrite/d. have CN': c # d; first by rewrite/c/d.
move: d c aEc bEd CN' IHn IHm C CN.
apply_funelim (a # b)=> n m c d E1 E2 CN IHm IHn C.
rewrite -E1 -E2 in CN=> {E1 E2 c d a b}. move=> /or4P[|||/orP[]].
- move=> /and3P[/cause_decr/(_ C) [x /andP[/orP[/eqP EQ nCx/eqP|/eqP/rc/negP F]]]].
- rewrite EQ. move=> /pred_le xLn. move: EQ=> /eqP/rpred_cause/(IHn _ xLn)/negP.
  by move: (consist_conflictl nCx CN).
- move/consist_conflictl/(_ CN). by rewrite symm_conflict.
- case EQ: (opred n)=>//. move: (EQ)=> /eqP/rpred_cause/trans_cause/(_ C). 
  by move: EQ=> /pred_le/IHn C'/C'/negP.
- case EQ: (opred m)=>// nCNa. move: (EQ) (nCNa)=> /eqP/rpred_cause aCm. 
  move: (C)=> /consist_conflictl H{}/H mCNa. move: C. case NM: (n == m)=> C.
- move: NM EQ=> /eqP<-/pred_le/IHn/(_ aCm)/negP. by rewrite symm_conflict=> /(_ mCNa).
- move: NM=> /negbT/cause_decr/(_ C) [x /andP[/orP[/eqP|/eqP/rc/negP F]]].
- rewrite EQ=> [[<-]]. by move: EQ=> /pred_le/IHm H/H/negP.
- move=> /consist_conflictl/(_ CN). by rewrite symm_conflict.
- case EQ: (orff n)=>//. move: (EQ)=> /eqP/rff_cause/trans_cause/(_ C).
  by move: EQ=> /orff_le/IHn C'/C'/negP.
- case EQ: (orff m)=>//. move: C=> /consist_conflictl H{}/H. by apply/negP/rc.
Qed.

Lemma irrefl_conflict : irreflexive conflict.
Proof. move=> n. apply/negbTE. by rewrite no_confl_cause// le_refl. Qed.


End Cause_Conflict.

Inductive cexec_event_struct := 
  Consist e of (consistance e).

Arguments Consist {_}.

Coercion ev_struct_of (e : cexec_event_struct) := let '(Consist e' _) := e in e'.

Canonical consist_subType := [subType for ev_struct_of].

Lemma consist_inj : injective (ev_struct_of). Proof. exact: val_inj. Qed.

End prime_event_structure.