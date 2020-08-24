From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From event_struct Require Import utilities EventStructure.
From Coq Require Import Arith.

(*Section foo.
Context {N : nat}.
Implicit Type (x y : 'I_N).
Definition lt_ord (x y : 'I_N) := (x < y)%N.

Lemma ltn_def (x y : 'I_N) : (x < y)%N = (y != x) && (x <= y)%N.
Proof. by rewrite ltn_neqAle eq_sym. Qed.

Lemma leqnn' x : (x <= x)%N.
Proof. Admitted.

Lemma anti_leq' : @antisymmetric 'I_N [eta leq].
Proof. Admitted.

Lemma leq_trans': @transitive 'I_N [eta leq].
Proof. Admitted.

Print anti_leq.

Definition orderMixin' :=
LePOrderMixin ltn_def leqnn' anti_leq' leq_trans'.

Definition ev_display' : unit.
Proof. exact: tt. Qed.

Canonical porderType := POrderType ev_display' 'I_N orderMixin'.
End foo.*)
Section transition_system.
Context {val : eqType}.
Notation exec_event_struct := (@exec_event_struct val).
Notation cexec_event_struct := (@cexec_event_struct val).
Implicit Types (x : var) (a : val) (t : tid).
Notation label := (@label val).
Notation n := (@n val).


(* Section with definitions for execution graph with added event *)
Section adding_event.
Variable 
  (l : label)               (* label of an event which we want to add      *)
  (e : exec_event_struct)     (* execution graph in which we want to add l *)
  (pre_pred : option 'I_(n e)). (* pred-child of new event (if it exists)        *)
Notation N := (n e).
Notation lab := (lab e).
Notation pred := (pred e).
Notation rf := (rf e).


Definition add_lab : 'I_N.+1 -> label := fun '(@Ordinal _ n L) =>
  if N =P n is ReflectF p then lab (Ordinal (ltS_neq_lt L p)) else l.

(* add_lab correctness first lemma *)
Lemma add_lab_eq_nat (m : 'I_N) (n : 'I_N.+1):
  n = m :> nat -> add_lab n = lab m.
Proof.
case: n. case: m => ? L ??/=. case: eqP=> *; last by apply/congr1/ord_inj.
exfalso. move: L. ssrnatlia.
Qed.

(* add_lab correctness second lemma *)
Lemma add_lab_N {L : N < N.+1}: add_lab (Ordinal L) = l.
Proof. move=> /=. by case: eqP. Qed.


Definition add_pred (m : 'I_N.+1) : option 'I_m := 
  let '(Ordinal m' L) := m in 
  match N =P m' with
  | ReflectT eq => let 'erefl := eq in pre_pred
  | ReflectF p => (pred (Ordinal (ltS_neq_lt L p))) 
  end.

(* if l \in 'I_N.+1 and l <> N then we can convert it's type to 'I_N *)
Definition decr_ord (l : 'I_N.+1) (neq : N <> l) : 'I_N :=
  Ordinal (ltS_neq_lt (ltn_ord l) neq).

Lemma decr_ord_ord k p: (decr_ord k p) = k :> nat.
Proof. by case: k p. Qed.

(* auxiliary lemma  *)
Lemma advance_is_read {K: N < N.+1} {m : 'I_(Ordinal K)} {L} L' : 
  compatible (lab m)                           (add_lab (@Ordinal _ N L)) ->
  compatible (add_lab (advance (Ordinal K) m)) (add_lab (@Ordinal _ N L')).
Proof.
rewrite [add_lab (advance _ _)](add_lab_eq_nat m)//.
have->//: (add_lab (Ordinal L)) = (add_lab (Ordinal L')).
by apply/congr1/ord_inj.
Qed.

(* auxiliary lemma *)
Lemma is_read_add_lab k neq: 
  is_read (add_lab k) -> is_read (lab (decr_ord k neq)).
Proof.
have->//: add_lab k = lab (decr_ord k neq). case: k neq=> /= m ? neq.
case: eqP=> [/neq|?]//. by apply/congr1/ord_inj.
Qed.

Arguments add_lab : simpl never.

Lemma compatible_lab_decr_ord 
  (k : 'I_N.+1) (m : nat) (r : 'I_N) (eq : r = k :> nat)
  (L : m < r) (L' : m < k) : 
  (compatible (lab     (advance r (Ordinal L)))  (lab r)) ->
  (compatible (add_lab (advance k (Ordinal L'))) (add_lab k)).
Proof.
by rewrite (add_lab_eq_nat (advance r (Ordinal L)))// (add_lab_eq_nat r).
Qed.

Equations incr_rf_codom 
  {k : 'I_N.+1} {r : 'I_N} (eq : r = k :> nat)
  (m : {l : 'I_r | (compatible (lab     (advance r l)) (lab r))}) :
       {l : 'I_k | (compatible (add_lab (advance k l)) (add_lab k))} :=
@incr_rf_codom (Ordinal L) (Ordinal L') erefl (@exist _ _ (@Ordinal m i) H) :=
  @exist _ _ (@Ordinal _ m i) (compatible_lab_decr_ord (Ordinal L) m (Ordinal L') erefl i i H).

Equations add_rf_some_aux 
  (k : 'I_N.+1) (m : 'I_N)
  (RF : compatible (lab m) (add_lab ord_max)) (IR : is_read (add_lab k)) :
  {l : 'I_k | (compatible (add_lab (advance k l)) (add_lab k))} :=
add_rf_some_aux (@Ordinal k' L) _ _ _ with Nat.eq_dec N k' := {
  add_rf_some_aux (Ordinal L) _ _ IR (right p) := 
  incr_rf_codom (decr_ord_ord (Ordinal L) p) (rff _ (decr_ord (Ordinal L) p) (is_read_add_lab (Ordinal L) p IR));
  add_rf_some_aux (Ordinal L) m RF IR (left erefl) :=
  (@exist _ (fun m => compatible (add_lab (advance (Ordinal L) m)) (add_lab (Ordinal L)))
  m (advance_is_read L RF))
}.

(*Definition add_rf_some_aux : forall
  (k : 'I_N.+1) (m : 'I_N)
  (RF : compatible (lab m) (add_lab ord_max)) (IR : is_read (add_lab k)),
  {l : 'I_k | (compatible (add_lab (advance k l)) (add_lab k))} :=
  (fun '(Ordinal k' L) =>
  match N =P k' with
  | ReflectF p => fun _ _ IR => 
      incr_rf_codom (decr_ord_ord (Ordinal L) p) (rff (decr_ord (Ordinal L) p) (is_read_add_lab (Ordinal L) p IR))
  | ReflectT eq => match eq, L with erefl, L => fun m RF IR =>
  (@exist _ (fun m => compatible (add_lab (advance (Ordinal L) m)) (add_lab (Ordinal L)))
            m (advance_is_read L RF))
  end end).*)

Definition add_rf_some : forall (m : 'I_N) (RF : compatible (lab m) l) 
  (k : 'I_N.+1) (IR : is_read (add_lab k)),
  {l : 'I_k | (compatible (add_lab (advance k l)) (add_lab k))} :=
  fun m => match (@add_lab_N (ltnSn N)) with
             erefl => fun (RF : compatible (lab m) (add_lab ord_max)) k IR =>
                        add_rf_some_aux k m RF IR
           end.

Lemma ord_P {L} : (~ is_read l) -> (~ is_read (add_lab (@Ordinal N.+1 N L))).
Proof. by rewrite add_lab_N. Qed.

Equations add_rf_None_aux  
  (k : 'I_N.+1)
  (NR : ~ is_read l)
  (IR : is_read (add_lab k)) :
  {l : 'I_k | (compatible (add_lab (advance k l)) (add_lab k))} :=
add_rf_None_aux (@Ordinal k' L) _ _ with Nat.eq_dec N k' := {
  add_rf_None_aux (Ordinal L) _ IR (right p) :=
  incr_rf_codom (decr_ord_ord (Ordinal L) p) (rff _ (decr_ord (Ordinal L) p) (is_read_add_lab (Ordinal L) p IR));
  add_rf_None_aux _ NR IR (left erefl) with (ord_P NR) IR := {}
}.

(*Definition add_rf_None_aux : forall
  (k : 'I_N.+1)
  (NR : ~ is_read l)
  (IR : is_read (add_lab k)),
  {l : 'I_k | (compatible (add_lab (advance k l)) (add_lab k))} :=
  fun '(Ordinal k' L) =>
  match N =P k' with
  | ReflectF p => fun _ IR => 
      incr_rf_codom (decr_ord_ord (Ordinal L) p) (rf (decr_ord (Ordinal L) p) (is_read_add_lab (Ordinal L) p IR))
  | ReflectT eq => match eq, L with erefl, L => fun NR IR =>
      match (ord_P NR) IR with end end
  end.*)

Definition add_rf_None := fun i j k => add_rf_None_aux j i k.

End adding_event.


Section add_event_def.
Variables (e : cexec_event_struct) (pre_pred : option 'I_(n e)).

Inductive add_label := 
| add_W : tid -> var -> val -> add_label
| add_R (n : 'I_(n e)) t x a : compatible (lab e n) (R t x a) -> add_label.

Definition add_event (l : add_label) := 
  match l with
  | add_W t x a      => Pack 
                         (n e).+1 
                         (add_lab (W t x a) e)
                         (add_pred e pre_pred) 
                         (add_rf_None (W t x a) e (is_read_W t x a))
  | add_R k t x a RF => Pack
                         (n e).+1 
                         (add_lab (R t x a) e)
                         (add_pred e pre_pred)
                         (add_rf_some (R t x a) e k RF)
  end.


End add_event_def.

Section confluence.
Implicit Type (e : cexec_event_struct).

Definition is_iso e e' (f : 'I_(n e) -> 'I_(n e')) :=
  (((n e' = n e) *  
  (injective f)) * (*???*)
  (((opred e') \o f =1 (opt f) \o (opred e)) *
  ((orff e') \o f =1 (opt f) \o (orff e))) *
  ((lab e')   \o f =1 lab e))%type.

Definition equviv e e' := exists f, is_iso e e' f.


Notation "e ~~ e'" := (equviv e e') (at level 20).

Lemma is_iso_id e : is_iso e e id.
Proof. 
do ?split=>//; move=>?/=; rewrite/opt; first by case: (opred _ _).
by case: (orff _ _).
Qed.

Lemma equiv_refl e: e ~~ e.
Proof. exists id. exact: is_iso_id. Qed.

Lemma opt_comp {T1 T2 T3} (f : T1 -> T2) (g : T2 -> T3) y : 
 opt (fun z => g (f z)) y = (opt g) ((opt f) y).
Proof. move: y. by case. Qed.


Lemma equiv_trans {e1} e2 {e3}: e1 ~~ e2 -> e2 ~~ e3 -> e1 ~~ e3 .
Proof.
case=> f1 [[[E a [b c d[f2[[[E1 a1[b1 c1 d1]]]]]]]]].
exists (f2 \o f1); do ? split; first (by rewrite -E); move=> x.
- by apply/inj_comp.
- move: b1 b. rewrite/eqfun/comp=>->->. by rewrite -opt_comp.
- move: c1 c. rewrite/eqfun/comp=>->->. by rewrite -opt_comp.
move: d1 d. by rewrite/eqfun/comp=>->->.
Qed.

Definition ev_rel e e' := exists k al, add_event e k al = e'.

Notation "e '-->' e'" := (ev_rel e e') (at level 20).

Inductive ev_rel_str : cexec_event_struct -> cexec_event_struct -> Prop :=
  | Base e : ev_rel_str e e
  | Steap {e1} e2 e3 (ers : ev_rel_str e1 e2) (er : e2 --> e3) : ev_rel_str e1 e3.

Notation "e '-*->' e'" := (ev_rel_str e e') (at level 20).

Definition add_place e e' k := exists al, add_event e k al = e'.

Lemma ev_rel_ord_le {e1 e }: e1 -*-> e -> n e1 <= n e.
Proof.
elim=> // ?????[?[l <-]]. rewrite/add_event. case: l=>/= *; ssrnatlia.
Qed.

Arguments add_lab : simpl never.

Lemma lab_add e1 e e'
  {f} (I : is_iso e e' f)
  (r : e1 -*-> e) (l : n e1 <= n e) (k : 'I_(n e1)) : 
   (lab e1 k) = (lab e' (f (widen_ord l k))).
Proof.
case: I=> _; rewrite/comp=>->. move: {f} r l k.
elim=> [???|e0 e2 e3 r IHr [k [[???<-|?????<-]/= l k']]]; 
first (by apply/congr1/ord_inj); move: (r)=> /ev_rel_ord_le l';
by rewrite (add_lab_eq_nat _ _ (widen_ord l' k')).
Qed.

Lemma comp_add e1 e e'
  {f} (I : is_iso e e' f)
  (r : e1 -*-> e) (l : label) k :
  compatible (lab e1 k) l ->
  compatible (lab e' (f (widen_ord (ev_rel_ord_le r) k))) l.
Proof. by rewrite -(lab_add e1 e e'). Qed.

Definition add_label_advance {e1 e e'} (r : e1 -*-> e) {f} (I : is_iso e e' f)
 : add_label e1 -> add_label e' :=
  fun al =>
  match al with
  | add_R k t x a comp => add_R e'
                          (f (widen_ord (ev_rel_ord_le r) k))
                          t x a
                          (comp_add e1 e e' I r (R t x a) k comp)
  | add_W t x a=> add_W e' t x a
  end.

Definition add_aux {e1 e e'}
  (k : option 'I_(n e1)) 
  (al : add_label e1)
  {f} (I : is_iso e e' f)
  (r : e1 -*-> e) : exec_event_struct :=
 add_event e' ((opt (f \o (widen_ord (ev_rel_ord_le r)))) k) (add_label_advance r I al).

Lemma rf_cosist_add {e1 e e'}
  {k : option 'I_(n e1)}
  {al : add_label e1}
  {f} (I : is_iso e e' f)
  (r : e1 -*-> e) : consistance (add_event e1 k al) -> 
  consistance (add_aux k al I r).
Proof. Admitted.

Definition add e1 e e'
  (k : option 'I_(n e1))
  (al : add_label e1)
  {f} (I : is_iso e e' f)
  (r : e1 -*-> e) (rc :  consistance (add_event e1 k al)) : cexec_event_struct := 
  Consist _ (rf_cosist_add I r rc).

Lemma add_equiv e1 e e'
  (k : option 'I_(n e1)) 
  (al : add_label e1)
  f (I : is_iso e e' f) r rc: 
  (add e1 e e k al (is_iso_id e) r rc) ~~ (add e1 e e' k al I r rc).
Proof. Admitted.


Lemma add_lem e1 e e'
  (k : option 'I_(n e1))
  (al : add_label e1)
  (r : e1 -*-> e) (rc :  consistance (add_event e1 k al)) :
    exists e'', (e'' ~~ (add e1 e e k al (is_iso_id e) r rc)) /\
               ((Consist (add_event e1 k al) rc)  -*-> e'').
Proof. Admitted.

Definition confluence_rel e1 e2 :=
  exists e3 e3', (((e1 -*-> e3) * (e2 -*-> e3')) * (e3 ~~ e3'))%type.

Notation "e ~c~ e'" := (confluence_rel e e') (at level 0).

Definition consist_of_eq e (l : exec_event_struct) : l = e -> 
  consistance l.
Proof. by case: e=> ?? /= ->. Qed.

Lemma confuense_add e1 e2 e1' : 
  e1 ~c~ e2 -> e1 --> e1' -> e1' ~c~ e2.
Proof.
case=> e [e'[[r ? EQV H]]]. inversion H. move: H0=> [al EQ].
move: (EQ) => /consist_of_eq rc.
set c := (Consist _ rc). have<-: c = e1'.
- apply/consist_inj. by rewrite -EQ.
case: (add_lem e1 e e' x al r rc)=> e'' [??].
case: (EQV)=> f I.
set e'pe1 := (add e1 e e' x al I r rc).
set epe1 := (add e1 e e x al (is_iso_id e) r rc).
exists e'', e'pe1; do ?split=>//; first last.
apply/(equiv_trans epe1)=>//. apply/add_equiv.
apply/(Steap e')=> //. rewrite /ev_rel/e'pe1/add/=/add_aux.
by exists (opt (f \o widen_ord (ev_rel_ord_le r)) x),  (add_label_advance r I al).
Qed.

Hint Resolve equiv_refl Base : core.

Theorem confluence e e1 e2 : e2 -*-> e1 -> e2 -*-> e -> e1 ~c~ e.
Proof. elim=> [*|? l ?? H ?/H?]; by [exists e, e|apply/(confuense_add l)]. Qed.
End confluence.

End transition_system.
