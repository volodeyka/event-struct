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

Arguments rf {_ _}.
Arguments rpred {_ _}.
Arguments cause {_ _}.
Arguments conflict {_ _}.

Definition explicit_event' (e : exec_event_struct) 
  (p : forall {e : exec_event_struct}, rel 'I_(n e)) i j
   (_ : phantom bool (p i j)) := @p e i j.

 Notation "e '|-' aRb " := (@explicit_event' e _ _ _ (Phantom _ aRb)) (at level 20).


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
exfalso. move: L. slia.
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

(* auxisliary lemma  *)
Lemma advance_is_read {K: N < N.+1} {m : 'I_(Ordinal K)} {L} L' : 
  compatible (lab m)                           (add_lab (@Ordinal _ N L)) ->
  compatible (add_lab (advance (Ordinal K) m)) (add_lab (@Ordinal _ N L')).
Proof.
rewrite [add_lab (advance _ _)](add_lab_eq_nat m)//.
have->//: (add_lab (Ordinal L)) = (add_lab (Ordinal L')).
by apply/congr1/ord_inj.
Qed.

(* auxisliary lemma *)
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
Variables (e : exec_event_struct) (pre_pred : option 'I_(n e)).

Inductive add_label := 
| add_W : tid -> var -> val -> add_label
| add_R (n : 'I_(n e)) t x a : compatible (lab e n) (R t x a) -> add_label.

Definition add_event (l : add_label) := 
  match l with
  | add_W t x a      => Pack 
                         (n e).+1 
                         (add_lab (W t x a) e)
                         (add_pred e pre_pred) 
                         (add_rf_None (W t x a) e not_false_is_true)
  | add_R k t x a RF => Pack
                         (n e).+1 
                         (add_lab (R t x a) e)
                         (add_pred e pre_pred)
                         (add_rf_some (R t x a) e k RF)
  end.

Lemma n_add_event l: n (add_event l) = (n e).+1.
Proof. by case: l. Qed.

Definition opredn (e' : exec_event_struct) := 
  ord_dom_to_nat (opred e') (opt (@nat_of_ord _)).

Definition orffn (e' : exec_event_struct)  := 
  ord_dom_to_nat (orff e') (opt (@nat_of_ord _)).

Definition olabn (e' : exec_event_struct)  := 
  ord_dom_to_nat (lab e') some.

Definition ord_restr N (f : nat -> nat) (n : 'I_N) : nat := f n.

Definition lab_of_add_lab al := 
  match al with
  | add_W t x a     => W t x a
  | add_R _ t x a _ => R t x a
  end.

Definition write_of_add_lab al := 
  match al with
  | add_W _ _ _     => None
  | add_R n _ _ _ _ => some n
  end.

Lemma olabn_add_event al k: 
  olabn (add_event al) k = 
  match n e =P k with (* TODO Replace with 'n e' *)
  | ReflectF p => olabn e k
  | ReflectT _ => some (lab_of_add_lab al)
  end.
Proof.
rewrite/olabn/ord_dom_to_nat.
set tn := n e.
case: {2}(k < n (add_event al)) {-1}(@erefl _ (k < n (add_event al))) erefl=> {2 3}->;
case: {2}(k < n e) {-1}(@erefl _ (k < n e)) erefl=> {2 3}->;
case: al; case: eqP=> //=.
- move=> eq t v s kne kne1. by case: eqP.
- move=> neq t v s kne kne1. case: eqP=> //= nek.
  have: kne = ltS_neq_lt kne1 nek. exact: eq_irrelevance. by move=>->.
- move=> eq n t v s comp kne kne1. by case: eqP.
- move=> neq n t v s comp kne kne1. case: eqP=> //= nek.
  have: kne = ltS_neq_lt kne1 nek. exact: eq_irrelevance. by move=>->.
- move=> eq t v s knef kne1. by case: eqP.
- move=> neq t v s knef kne1. case: eqP=> //= *.
  have: n e = k=> //. apply/eqP. by rewrite eqn_leq leqNgt knef -ltnS kne1.
- move=> eq n t v s comp knef kne1. by case: eqP.
- move=> neq n t v s comp knef kne1. case: eqP=> //.
  have: tn = k=> //. apply/eqP. by rewrite eqn_leq leqNgt knef -ltnS kne1.
- move=> eq t v s ktn kne1f.
  have: k < k. apply: (ltn_trans ktn). by rewrite ltnNge -ltnS kne1f.
  by rewrite ltnn.
- move=> neq _ _ _ ktn kne1f. have: k < k. 
  apply: (ltn_trans ktn). by rewrite ltnNge -ltnS kne1f.
  by rewrite ltnn.
- move=> eq n t v s comp ktn ktn1f. have: k < k.
  apply: (ltn_trans ktn). by rewrite ltnNge -ltnS ktn1f.
  by rewrite ltnn.
- move=> neq n t v s comp ktn kne1f. have: k < k.
  apply: (ltn_trans ktn). by rewrite ltnNge -ltnS kne1f.
  by rewrite ltnn.
- move=> eq t v s ktnf. by rewrite -eq leqNgt ltnn.
move=> eq n t v s comp ktnf. by rewrite -eq leqNgt ltnn.
Qed.

Lemma opredn_add_event l k: 
  opredn (add_event l) k = 
  match n e =P k with 
  | ReflectT _ => (opt (@nat_of_ord (n e))) pre_pred
  | ReflectF _ => (opredn e) k
  end.
Proof. Admitted.

Lemma opredn_le k l: 
  opredn e k = some l -> l < n e.
Proof.
rewrite/opredn/ord_dom_to_nat. dep_case=>// ?. 
by case E: (opred e _)=> [[]/=|//][<-].
Qed.

Lemma orffn_le k l: 
  orffn e k = some l -> l < n e.
Proof.
rewrite/orffn/ord_dom_to_nat. dep_case=>// L. 
by case E: (orff e (Ordinal L)) => [[]/=|//][<-].
Qed.

Lemma n_add_event_le_n al: n e <= n (add_event al).
Proof. by rewrite n_add_event. Qed.

Lemma orff_add_event al y :
  orff (add_event al) y = 
  (match y < n e as Lxn return (y < n e = Lxn -> _) with
  | true  => fun pf => if (orff e (Ordinal pf)) is Some a
                           then some (widen_ord (@n_add_event_le_n _) a)
                       else None
  | flase => fun=> if (write_of_add_lab al) is Some a
                     then some (widen_ord (@n_add_event_le_n _) a)
                   else None
  end) erefl.
Proof. Admitted.

Lemma orffn_add_event l k: 
  orffn (add_event l) k =
  match n e =P k with
  | ReflectT _ => (opt (@nat_of_ord (n e))) (write_of_add_lab l)
  | ReflectF _ => (orffn e) k
  end.
Proof.
case: eqP; rewrite/orffn/ord_dom_to_nat.
- dep_case=> [L?|]; last (rewrite n_add_event; slia).
  rewrite orff_add_event/=. dep_case; first (by move=>*; exfalso; slia).
  by case: l L.
do ?dep_case=>//.
- move=> L *. rewrite orff_add_event/=. dep_case; last by rewrite L.
  move=> L'. have->: (Ordinal L') = (Ordinal L) by apply/ord_inj.
  by case: (orff e (Ordinal (n:=n e) (m:=k) L)).
all: move=> ? L ?; exfalso; rewrite n_add_event in L; slia.
Qed.

End add_event_def.

Definition eq_al {e1 e2 : exec_event_struct}
    (al1 : add_label e1) (al2 : add_label e2) : bool :=
match al1, al2 with
| add_W t x a, add_W l y b         => [&& (t == l), (x == y) & (a == b)]
| add_R n t x a _, add_R k l y b _ => 
  [&& (n == k :> nat), (t == l), (x == y) & (a == b)]
| _, _                             => false
end.

Section confluence.

Section Homorphism.
Implicit Type (e : exec_event_struct) .

Definition is_mono_nat e e' (f : nat -> nat) := 
  (((injective f) *
  ((opredn e') \o f =1 (opt f) \o (opredn e))) *
  (((orffn e') \o f =1 (opt f) \o (orffn e)) *
  ((olabn e')   \o f =1 olabn e)))%type.


Definition is_iso_nat e e' (f : nat -> nat) :=
  ((n e = n e') * (is_mono_nat e e' f))%type.

Definition is_mono e e' (f : 'I_(n e) -> 'I_(n e')) := 
  (((injective f) *
  ((opred e') \o f =1 (opt f) \o (opred e))) *
  (((orff e') \o f =1 (opt f) \o (orff e)) *
  ((lab e')   \o f =1 lab e)))%type.


Lemma is_mono_nat_eq {e e' f} g: 
  f =1 g -> 
  (is_mono_nat e e' g <-> is_mono_nat e e' f).
Proof.
have L: forall f g, f =1 g -> is_mono_nat e e' f -> is_mono_nat e e' g.
- move=> {f g} f g E [[If Ep[Er El]]]. do ?split; first (by apply/(eq_inj If));
  move=> k/=. 
- move: (E k) (Ep k)=>/=->->. case ?: (opredn e k)=>//= a. by move: (E a)=>->.
- move: (E k) (Er k)=>/=->->. case ?: (orffn e k)=>//= a. by move: (E a)=>->.
- by move: (E k) (El k)=>/=->->.
move=> E. split=> /L; last by move/(_ _ E). by move/(_ _ (fsym E)).
Qed.

Lemma eq_is_mono {e e'} f g: g =1 ord_f_to_nat (n e' - n e) f ->
  (is_mono e e' f <-> is_mono_nat e e' g).
Proof.
move=> E. rewrite -(is_mono_nat_eq _ E).
have H: forall x y, (x < n e) -> (y < n e) = false ->
       ~ (ord_f_to_nat (n e' - n e) f x = ord_f_to_nat (n e' - n e) f y).
- move=> x y Lxn Lyn.
  rewrite -{1}[x]/(nat_of_ord (Ordinal Lxn)) -ord_f_to_natE ord_f_to_nat_Nlt//.
  case: (f (Ordinal Lxn))=>/= ?. slia.
split.
- case=> [[If Ep[Er El]]]. do ?split.
- move=> x y. case Lxn: (x < (n e)). rewrite -{1}[x]/(nat_of_ord (Ordinal Lxn)).
- case Lyn: (y < (n e)); first 
  by rewrite -{1}[y]/(nat_of_ord (Ordinal Lyn)) -?ord_f_to_natE=> /ord_inj/If[].
- move=> Eo. exfalso. move: Eo=> /H; by apply.
- case Lyn: (y < (n e)); first by move=>/esym Eo; exfalso; move: Eo=>/H; apply.
- rewrite ?ord_f_to_nat_Nlt//. slia.
1-3: move=>k; rewrite ord_dom_to_nat_comp// ?(ord_dom_to_nat_eq Ep)
  ?(ord_dom_to_nat_eq Er) ?(ord_dom_to_nat_eq El) -?ord_dom_to_nat_opt_comp//.
case=> [[If?[? L]]]. do ?split; move=>x.
- move=> y /(congr1 (@nat_of_ord (n e'))). 
  by rewrite 2?(ord_f_to_natE (n e' - n e))=> /If/ord_inj.
1,2: apply/(@inj_ord_dom_to_nat _ _ _ _ _ _(opt (@nat_of_ord (n e')))); first (by
  case=> [/=?[]//=?[]/ord_inj->|[]//]);
  rewrite -ord_dom_to_nat_comp (ord_dom_to_nat_opt_comp (n e' - n e))//.
apply/(inj_ord_dom_to_nat Some_inj).
rewrite -ord_dom_to_nat_comp//. exact: L.
Qed.

Lemma is_mono_nat_ex e e' f: 
  is_mono_nat e e' f -> exists g, is_mono e e' g.
Proof.
move=> I. case: (I)=> [[If Ep[Erf Elab]]].
have F: forall k, k < n e -> f k < n e'.
- move=> k L. case Lfkn: (f k < n e') (Elab k)=>//=. 
  rewrite/olabn/ord_dom_to_nat. dep_case=> [E|]; first by rewrite E in Lfkn.
  dep_case=>//. slia.
set g := (fun '(Ordinal k L) => (Ordinal (F k L))).
have Egf: forall k, k < n e -> f k = (ord_f_to_nat (n e' - n e) g) k.
- move=> k L. rewrite/ord_f_to_nat/=. case L': (k < n e)=> //. slia.
exists g. do ?split.
- move=> k l /(congr1 (@nat_of_ord _)). rewrite !(ord_f_to_natE (n e' - n e)).
  case: k l=>??[/=??]. rewrite -Egf// -Egf// => /If ?. by apply/ord_inj.
1,2: case=> k L;
  apply/(@inj_ord_dom_to_nat _ _ _ _ _ _(opt (@nat_of_ord (n e')))); first (by
  case=> [/=?[]//=?[]/ord_inj->|[]//]);
  rewrite -ord_dom_to_nat_comp (ord_dom_to_nat_opt_comp (n e' - n e))//=.
- move: (Egf k L) (Ep k) =>/=->; rewrite{1}/opredn=>->.
  rewrite -[(ord_dom_to_nat _ (opt (@nat_of_ord _)) k)]/(opredn e k).
  case E: (opredn e k)=>//=. by move/opredn_le/Egf: E->.
- move: (Egf k L) (Erf k) =>/=->; rewrite{1}/orffn=>->.
  rewrite -[(ord_dom_to_nat _ (opt (@nat_of_ord _)) k)]/(orffn e k).
  case E: (orffn e k)=>//=. by move/orffn_le/Egf: E->.
case=> k L. apply/(inj_ord_dom_to_nat Some_inj).
rewrite -ord_dom_to_nat_comp//=. by move: (Egf k L) (Elab k)=><-/=.
Qed.

Arguments conflictP {_ _ _ _}.

Lemma rf_mono {e e' l m} f: 
  is_mono e e' f -> rf (f l) (f m) = rf l m.
Proof.
rewrite/rf. case=> [[If _[] /(_ m)/=->_]]. 
by rewrite -[some (f l)]/(opt f (some l)) (inj_eq (opt_inj If)).
Qed.

Lemma rpred_mono {e e' l m} f: 
  is_mono e e' f -> rpred (f l) (f m) = rpred l m.
Proof.
rewrite/rpred. case=> [[If/(_ l)/=->_]]. 
by rewrite -[some (f m)]/(opt f (some m)) (inj_eq (opt_inj If)).
Qed.

Lemma pred_cause_ex_in_mono e e' w y f: 
  is_mono e e' f -> w <=c (f y) ->
  exists z, w = f z.
Proof. 
case=> [[? Ep[Er ?]]] /connectP[]. move=> x.
elim: x w=>/= [w?<-|?[/=? w/swap<-/andP[/orP[]]|/=]]; first by exists y.
- rewrite /rf. move: (Er y)=> /=->. case: (_ e y)=>/= [a/eqP[<- _]|/eqP//].
  by exists a.
- rewrite/rpred. move: (Ep y)=> /=->. case: (_ e y)=>/= [a/eqP[<- _]|/eqP//].
  by exists a.
move=> ?? IHx w /andP[/orP[]R /IHx H /H[x E]]; move: E R=>->.
- rewrite /rf. move: (Er x)=> /=->. case: (_ e x)=>/= [a/eqP[<-]|/eqP//].
  by exists a.
rewrite/rpred. move: (Ep x)=> /=->. case: (_ e x)=>/= [a/eqP[<-]|/eqP//].
by exists a.
Qed.

Lemma cause_mono {e e' l m} f
  (l' m' : 'I_(n e')): 
  is_mono e e' f ->
  (f l = l' :> nat) -> (f m = m' :> nat) -> 
  (l <=c m) = (l' <=c m').
Proof.
move=> I /ord_inj<-/ord_inj<-. case: (I)=> [[If Epo [? Elab]]].
rewrite/Order.le/=/cause. apply/(sameP connectP)/(equivP connectP). split.
- case=> x. move: l. 
  elim/last_ind: x m=>/=[x m _ /If ->|s h IHx l m]; first by exists [::].
  rewrite rcons_path last_rcons andbC/==>/swap<- /andP[R]. 
  have/pred_cause_ex_in_mono: (last (f m) s) <=c (f l) by apply/connect1=>/=.
  move: R=>/swap/(_ I)[x /esym E]. rewrite -E rf_mono ?rpred_mono// =>?/IHx/(_ E)[].
  move=> p ? H. exists (rcons p l); last by rewrite last_rcons. 
  rewrite rcons_path/= -H. by apply/andP.
case=> p ??. exists [seq f i | i <- p].
- rewrite path_map/relpre//=.
  rewrite -(@eq_path_in _ [rel m n | rf m n || rpred n m])// => ????/=.
  by rewrite rpred_mono ?rf_mono.
rewrite last_map. by apply/congr1/esym.
Qed.

Lemma conflict_mono {e e' f} l m 
  {l' m' : 'I_(n e')}: 
  is_mono e e' f ->
  (f l = l' :> nat) -> (f m = m' :> nat) -> 
  (l # m) = (l' # m').
Proof.
move=> I /ord_inj E1 /ord_inj E2. case: (I)=> [[If Epo [? Elab]]].
apply/(sameP conflictP)/(equivP conflictP). split.
- move=> [x [y /and3P[]]]. rewrite -E1 -E2=> Lxl Lxm. 
  move: (Lxl) (Lxm)=>/pred_cause_ex_in_mono[]//i E/pred_cause_ex_in_mono[]//j E'.
  move: E E' Lxl Lxm=>->-> L1 L2 /and3P[/eqP Ef Ep El]. exists i, j. 
  rewrite (cause_mono f (f i) (f l))// L1 (cause_mono f (f j) (f m))// L2/=.
  rewrite/pre_conflict. apply/and3P; split; first by apply/eqP=>E; rewrite E in Ef.
- by move: (Epo i) (Epo j) Ep=> /=->->/eqP /(opt_inj If)->.
  by move: (Elab i) (Elab j) El=> /=->->/eqP->.
move=> [x [y /and3P[]]]. 
rewrite (cause_mono f (f x) (f l)) ?(cause_mono f (f y) (f m))//.
rewrite/pre_conflict=> ??/and3P[N /eqP E /eqP E']. exists (f x), (f y).
apply/and4P. split; rewrite -?E1 -?E2//; first by apply/negP=> /eqP/If;
move/negP: N=> /swap->.  apply/andP. split; apply/eqP; 
first by move: (Epo x) (Epo y) E=>/=->->->.
by move: (Elab x) (Elab y) E'=>/=->->->.
Qed.

Lemma is_mono_add_event {e k al}: 
  is_mono_nat e (add_event e k al) 
  (fun k => if k < n e then k else 1 + k).
Proof.
do ?split; move=> x/=;
rewrite ?opredn_add_event ?orffn_add_event ?olabn_add_event; do ?case: eqP;
case: ifP; rewrite ?n_add_event//; try slia.
1,2: move=> ??; case: ifP; slia.
1,3: rewrite /opredn/orffn {1}/ord_dom_to_nat=> ?; dep_case; last slia.
1,2:  rewrite/ord_dom_to_nat=>e'' ?; dep_case=> e'; last slia.
1,2:  have->: Ordinal e' = Ordinal e'' by apply/ord_inj. 
- by case: (opred e (Ordinal e''))=>//= [[/=?->]].
- by case: (orff e (Ordinal e''))=>//= [[/=?->]].
1,2: rewrite /opredn/orffn {1}/ord_dom_to_nat=> ?;
  rewrite/ord_dom_to_nat; do ?dep_case=>//=; move=> *; exfalso; slia.
rewrite /olabn/ord_dom_to_nat; do ?dep_case=> *//; try exfalso; slia.
Qed.

Lemma conflict_add_event {e k al} (l m : 'I_(n e))
  (l' m' : 'I_(n (add_event e k al))): 
  (l = l' :> nat) -> (m = m' :> nat) -> 
  (l # m) = (l' # m').
Proof. 
move=> *. have L: n e <= n (add_event e k al) by rewrite n_add_event.
have/eq_is_mono E: 
      ((fun k => if k < n e then k else 1 + k)) =1
      (ord_f_to_nat ((n (add_event e k al) - n e)) (widen_ord L)).
- move=> x. case Lxn: (x < n e); rewrite /ord_f_to_nat; dep_case=>/=; try slia.
  by rewrite n_add_event subSnn.
move/E/conflict_mono: (@is_mono_add_event e k al). exact.
Qed.

Lemma is_mono_nat_le e1 e2 f: 
  is_mono_nat e1 e2 f -> n e1 <= n e2.
Proof. move/is_mono_nat_ex=> [x [[/inj_le_card]]]. by rewrite !card_ord. Qed.

Lemma is_mono_nat_comp {e1 e2 e3 f1 f2 f3}: 
  is_mono_nat e1 e2 f1 -> is_mono_nat e2 e3 f2 ->
  f3 =1 f2 \o f1 -> is_mono_nat e1 e3 f3.
Proof.
move=> I1 I2. move: (I1) (I2) (I1) (I2)=> /is_mono_nat_le L1 /is_mono_nat_le?.
case=>[[? Ep1[Er1 El1]]][[? Ep2[Er2 El2]]]?.
apply/(is_mono_nat_eq (f2 \o f1))=>//.
do ?split; first (by apply/inj_comp); move=> k/=; try rewrite opt_comp.
move: (Ep1 k) (Ep2 (f1 k))=> /=<-->. by case: (opredn e2 _).
move: (Er1 k) (Er2 (f1 k))=> /=<-->. by case: (orffn e2 _).
move: (El1 k) (El2 (f1 k))=> /=<-->. by case: (olabn e2 _).
Qed.

Definition is_iso e e' (f : 'I_(n e) -> 'I_(n e')) :=
  ((n e = n e') * (is_mono e e' f))%type.

Definition equviv e e' := exists f, is_iso e e' f.

Definition equviv_nat e e' := exists f, is_iso_nat e e' f.

Notation "e ~~ e'" := (equviv e e') (at level 20).

Lemma iff_and (A B C : Prop): (A -> (B <-> C)) -> (A * B <-> A * C).
Proof. move=> H. by split=> [][pA]; move/H: (pA)=> eBC /eBC. Qed.

Lemma eq_is_iso e e' f:  is_iso e e' f <-> is_iso_nat e e' (ord_f_to_nat 0 f).
Proof. apply/iff_and=> E. apply/eq_is_mono.  by rewrite {3}E subnn. Qed.

Lemma eq_equviv e e': e ~~ e' <-> equviv_nat e e'.
Proof.
split=> [[f /eq_is_iso ?]|[f]]; first by exists (ord_f_to_nat 0 f).
move=> [?/is_mono_nat_ex[g?]]. exists g. by split.
Qed.

Lemma is_iso_id e : is_iso e e id.
Proof. 
do ?split=>//; move=>?/=; rewrite/opt; first by case: (opred _ _).
by case: (orff _ _).
Qed.

Lemma equiv_refl e: e ~~ e.
Proof. exists id. exact: is_iso_id. Qed.


Lemma equiv_trans {e1} e2 {e3}: e1 ~~ e2 -> e2 ~~ e3 -> e1 ~~ e3 .
Proof.
case=> f1 [E [[a b[c d[f2[E1 [[a1 b1[c1 d1]]]]]]]]].
exists (f2 \o f1); do ? split; first (by rewrite E); move=> x.
- by apply/inj_comp.
- move: b1 b. rewrite/eqfun/comp=>->->. by rewrite -opt_comp.
- move: c1 c. rewrite/eqfun/comp=>->->. by rewrite -opt_comp.
move: d1 d. by rewrite/eqfun/comp=>->->.
Qed.

Lemma equiv_sym e1 e2: e1 ~~ e2 -> e2 ~~ e1.
Proof.
case=> f [E [[If x[y z]]]]. have[g ? c]: bijective f;
first by apply/inj_card_bij=>//; rewrite E. 
have Iof: injective (opt f) by case=> [|[]//]?[]//=?[/If->].
exists g. do ?(split=>//); first (by apply/(can_inj c)); move=> k/=.
1,2: apply/Iof; move: (x (g k)) (y (g k)); rewrite/= -opt_comp (c k)=> P R;
     rewrite -(P, R) /opt; case: (_ e2 k)=>//a; by rewrite (c a).
move: (z (g k))=>/=<-. by rewrite (c k).
Qed.

End Homorphism.
Notation "e ~~ e'" := (equviv e e') (at level 20).

Implicit Type (e : cexec_event_struct).


Definition ev_rel e e' := exists k al, add_event e k al = e'.

Notation "e '-->' e'" := (ev_rel e e') (at level 20).

Inductive ev_rel_str : cexec_event_struct -> cexec_event_struct -> Prop :=
  | Base e : ev_rel_str e e
  | Step {e1} e2 e3 (ers : ev_rel_str e1 e2) (er : e2 --> e3) : ev_rel_str e1 e3.

Notation "e '-*->' e'" := (ev_rel_str e e') (at level 20).

Definition add_place e e' k := exists al, add_event e k al = e'.

Lemma ev_rel_ord_le {e1 e }: e1 -*-> e -> n e1 <= n e.
Proof. elim=> // ?????[?[l <-]]. rewrite/add_event. case: l=>/= *; slia. Qed.

Arguments add_lab : simpl never.

Lemma lab_add e1 e e'
  {f} (I : is_iso e e' f)
  (r : e1 -*-> e) (l : n e1 <= n e) (k : 'I_(n e1)) : 
   (lab e1 k) = (lab e' (f (widen_ord l k))).
Proof.
case: I=> _[[_ _[_]]]. rewrite/comp=>->. move: {f} r l k.
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

Lemma eq_al_trans {e1 e2 e3} 
  {al1 : add_label e1} (al2 : add_label e2) (al3 : add_label e3) :
  eq_al al1 al2 -> eq_al al2 al3 -> eq_al al1 al3.
Proof.
case: al1; case al2=>//= ??????; first by move/and3P=>[]/eqP->/eqP->/eqP->.
move=> ????/and4P[]. by do ?(move/eqP=>->).
Qed.

Lemma eq_al_add_label_advane' {e1 e2: cexec_event_struct} 
  {e3 : exec_event_struct} (C : consistance e3) r 
  (al1 : add_label e1) (al2 : add_label e2) :
  eq_al (@add_label_advance e1 (Consist e3 C) (Consist e3 C) r id (is_iso_id e3) al1) al2 = 
  eq_al al1 al2.
Proof. by case: al1. Qed.

Lemma eq_al_add_label_advane {e1 e3: cexec_event_struct}
  {e2 : exec_event_struct}  r 
  (al1 : add_label e1) (al2 : add_label e2) :
  eq_al (@add_label_advance e1 e3 e3 r id (is_iso_id e3) al1) al2 = 
  eq_al al1 al2.
Proof. by case: al1. Qed.

Lemma eq_al_refl {e1} (al : add_label e1): eq_al al al.
Proof. by case: al=>/=*; rewrite !eqxx. Qed.

Hint Resolve eq_al_refl : core.

Lemma eq_al_sym {e2 : exec_event_struct} {e1}
  {al1 : add_label e1} (al2 : add_label e2)  :
  eq_al al1 al2 = eq_al al2 al1.
Proof.
case: al1; case: al2=>//=.
- move=> t x a *. by rewrite [t == _]eq_sym [x == _]eq_sym [a == _]eq_sym.
move=> n t x a *. 
by rewrite [n == _ :> nat]eq_sym [t == _]eq_sym [x == _]eq_sym [a == _]eq_sym.
Qed.


Definition add_aux {e1 e e'}
  (k : option 'I_(n e1))  (* place in e1 where we add event    *)
  (al : add_label e1)     (* label of this event               *)
  {f} (I : is_iso e e' f) (* f is isomorphism between e and e' *)
  (r : e1 -*-> e) : exec_event_struct :=
  add_event e' ((opt (f \o (widen_ord (ev_rel_ord_le r)))) k) (add_label_advance r I al).

Lemma add_equiv_nat {e e'}
  {k : option 'I_(n e)}
  {al : add_label e} {al' : add_label e'}
  f {I : is_iso e e' f}: 
  eq_al (add_label_advance (Base e) I al) al' ->
  equviv_nat (add_event e k al) (add_event e' ((opt f) k) al').
Proof.
move/eq_is_iso: (I). set g := (ord_f_to_nat 0 f) => [[E[[Ig P[]]]]].
have L: forall k, n e <= k -> g k = k. 
- move=>l. rewrite/g/ord_f_to_nat. dep_case; last slia. move=>*. exfalso. slia.
exists g. have E': n e = g (n e) by apply/esym/L; slia.
do ?split=>//; first (by rewrite !n_add_event E); move=> k0/=.
- rewrite !opredn_add_event. do ?(case: eqP).
- move=> ??. rewrite -?opt_comp. case: k=>//=?. apply/congr1/ord_f_to_natE.
- rewrite -{1}E {2}E'=> F /Ig. slia.
- move=><-. rewrite -{1}E L; slia.
- move=> *. exact: P.
- rewrite !orffn_add_event. do ?(case: eqP).
- move=> ??. rewrite -?opt_comp. move: H. case: al;
  case: al'=>//= ??????????/and4P[/eqP<-*]. apply/congr1/ord_f_to_natE.
- rewrite -{1}E {2}E'=> F /Ig. slia.
- move=><-. rewrite -{1}E L; slia.
- move=> *. exact: a.
rewrite !olabn_add_event. do ?(case: eqP).
- move: H. case: al; case al'=>//=??????; first by move/and3P=>[]; do ?move/eqP=>->.
- move=>????/and4P[?]. by do ?move/eqP=>->.
- rewrite -{1}E {2}E'=> F /Ig. slia.
- move=><-. rewrite -{1}E L; slia.
move=>*. exact: b.
Qed.

Lemma n_add_event_lt_n {e k al}: n e < n (add_event e k al).
Proof. by rewrite n_add_event. Qed.

Arguments add_event: simpl never.
Lemma ev_rel_mono e e' : e -*-> e' -> 
   is_mono_nat e e' (fun l => if l < n e then l else (n e' - n e) + l).
Proof.
elim=> [?|e1 e2 e3 ? M [k [al <-]]]; last rewrite !n_add_event.
rewrite subnn -(is_mono_nat_eq id); last by (move=>x; case:(x < _)).
do ?split=>//; move=>k/=; first by case: (opredn _ k).
- by case: (orffn _ k).
apply/(is_mono_nat_comp M is_mono_add_event).
have ?: n e1 <= n e2 by apply/ev_rel_ord_le.
move=> x//=. do ?case: ifP; slia.
Qed.


Lemma add_event_mono {e e'}
  {k : option 'I_(n e)} {k' : option 'I_(n e')}
  {al : add_label e} {al' : add_label e'}
  (L : n (add_event e k al) <= n (add_event e' k' al')) :
  onat_eq_ord k k' -> eq_al al al' ->
  e -*-> e' -> 
  is_mono 
    (add_event e k al)
    (add_event e' k' al')
    (fun (k : 'I_(n (add_event e k al))) =>  
    if k == (n e) :> nat then 
      (Ordinal n_add_event_lt_n)
    else widen_ord L k).
Proof.
move=> Eo Ea r. move/ev_rel_ord_le: r (r)=> ?/ev_rel_mono. 
set f := fun l => if l < n e then l else (n e' - n e) + l.
have f_eq: forall x : nat, (n e = x) <-> (n e' = f x).
- move=> x. rewrite /f. case: ifP; slia.
case=> [[? Epred[Erf Elab]]]. apply/(@eq_is_mono _ _ _ f).
- move=> x. rewrite/ord_f_to_nat. dep_case=>/=; first (case Exn: (x == _)=>/=);
  rewrite !n_add_event /f; case: ifP; slia.
do ?split=>//; move=> x/=.
- rewrite !opredn_add_event; do ?case: eqP; try by rewrite ?f_eq//.
- case: k k' Eo {L}=> [[? L][]//= ?/eqP/=[<-??]|[]//]. by rewrite /f L.
- by move: (Epred x)=>/=<-.
- rewrite !orffn_add_event; do ?case: eqP; try by rewrite ?f_eq//.
- case: al al' Ea {L}=> [???[]//|[? L????[]//=?????/and4P[/eqP<-*]]]. 
  by rewrite /f L.
- by move: (Erf x)=>/=<-.
rewrite !olabn_add_event. do ?case: eqP; try by rewrite ?f_eq//.
- by case: al al' Ea {L}=> [???[]//=???/and3P[]|[? L????[]//=?????/and4P[?]]];
  do ?move/eqP=>->.
by move: (Elab x)=>/=<-.
Qed.

Lemma consist_add_eq e {e'}
  (k : option 'I_(n e)) {k' : option 'I_(n e')}
  (al : add_label e) {al' : add_label e'} :
  e -*-> e' ->
  onat_eq_ord k k' -> eq_al al al' ->
  consistance (add_event e k al) -> consistance (add_event e' k' al').
Proof.
move=> r Eo Ea Ce. apply/forallP=> x. apply/forallP=> y. apply/implyP.
rewrite orff_add_event.
- dep_case=> L.
- case E: (orff e' (Ordinal L))=> [a|] // /eqP[<-].
  case: e' a al' k' y L {x r Eo Ea Ce} E=>/= e' C a al' k' y L /eqP E.
  move/forallP: (C)=> /(_ a)/forallP/(_ (Ordinal L))/implyP/(_ E).
  by rewrite (conflict_add_event (Ordinal L) a y 
  (widen_ord (n_add_event_le_n (Consist e' C) k' al') a)).
have Lnn: n (add_event e k al) <= n (add_event e' k' al'). 
- rewrite !n_add_event. move: (ev_rel_ord_le r). slia.
move: (add_event_mono Lnn Eo Ea r).
case: al' al Ea x y L Lnn Ce=>//= N ????[]//= N' t x a i/andP[/eqP EQ? z y L? C M].
case/eqP=><-.
set y' := Ordinal (@n_add_event_lt_n e k (add_R e N' t x a i)).
rewrite -(conflict_mono y' (widen_ord (n_add_event_le_n _ _ _) N') M)/= ?eqxx.
- move: C. rewrite/consistance.
  move/forallP/(_ (widen_ord (n_add_event_le_n e k (add_R e N' t x a i)) N')).
  move/forallP/(_ y')/implyP. apply. rewrite orff_add_event/=.
  case: {2}(n e < n e) {-1}(@erefl _ (n e < n e)) erefl=> {2 3}-> // H.
- exfalso. by rewrite ltnn in H.
- move=>/=. case: y L=>/= m. case: (ltngtP m (n e'))=>//. slia.
case: N' EQ i {M y' C}=>/= m L'<-. case E: (m == n e)=>//.
exfalso. move/eqP: E L'. slia.
Qed.

Lemma consist_equviv (e e' : exec_event_struct):
  e ~~ e' -> consistance e -> consistance e'.
Proof.
move/equiv_sym=>[f Is]. case:(Is)=>[E [[If ?[Erf ?]]]]. rewrite/consistance=>H.
move/inj_card_bij : (If)=> /=. rewrite !card_ord=> /(_ E) [g c' c].
have Eo: orff e =1 opt f \o orff e' \o g by move=> k; rewrite -(c k)/= c';
move: (Erf (g k))=>/=. apply/forallP=>k; apply/forallP=> m. apply/implyP=>/eqP.
rewrite -((opt_can c') (orff e' m)) -(c' m). move: (Eo (f m))=>/=<-.
rewrite -((opt_can c') (some k)) c'=> /opt_inj-/(_ (can_inj c))/=.
move: H=> /forallP/(_ (f k))/forallP/(_ (f m))/implyP H/eqP/H.
by rewrite -(conflict_mono m k (f := f)).
Qed.

Lemma rf_cosist_add {e1 e e'}
  {k : option 'I_(n e1)}
  {al : add_label e1}
  {f} (I : is_iso e e' f)
  (r : e1 -*-> e) : consistance (add_event e1 k al) -> 
  consistance (add_aux k al I r).
Proof.
move=> C. apply/(consist_equviv (add_aux k al (is_iso_id e) r)).
- apply/eq_equviv. rewrite/add_aux 2?opt_comp. 
  have->: opt id =1 id by move=> T[].
  apply/(add_equiv_nat f). case: al {C}=> //= [???|?????]; rewrite !eqxx//.
  apply/and4P. do ?(split=>//). by apply/eqP/congr1/congr1/ord_inj.
apply/(consist_add_eq e1 k al)=>//.
- case: k {C}=>//= ?. by rewrite/onat_eq_ord.
by rewrite eq_al_sym eq_al_add_label_advane.
Qed.


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
Proof.
apply/eq_equviv. rewrite/add/=/add_aux/comp. rewrite 2?opt_comp -opt_comp.
apply/add_equiv_nat=>//. case: al {rc}=> //= [???|?????]; rewrite !eqxx//.
apply/and4P. do ?(split=>//). by apply/eqP/congr1/congr1/ord_inj.
Qed.

Hint Resolve equiv_refl Base : core.

Definition consist_of_eq e (l : exec_event_struct) : l = e -> 
  consistance l.
Proof. by case: e=> ?? /= ->. Qed.

Lemma ev_rel_add e1 e e' k al r rc (f : 'I_(n e) -> 'I_(n e')) I :
  e' --> @add e1 e e' k al f I r rc.
Proof.
by exists (opt (f \o widen_ord (ev_rel_ord_le r)) k),
          (add_label_advance r I al).
Qed.

Lemma equiv_ev_rel e1 e2 e3: 
  e1 ~~ e2 -> e2 --> e3 -> exists e4, (e4 ~~ e3) /\ (e1 --> e4).
Proof.
move/equiv_sym=> [f I [k [al H]]]. move: (H)=> /consist_of_eq C.
exists (add e2 e2 e1 k al I (Base e2) C); split; last by apply/ev_rel_add.
have->: e3 = Consist _ C by apply/consist_inj.
apply/(equiv_trans (add e2 e2 e2 k al (is_iso_id e2) (Base e2) C)).
- apply/equiv_sym/add_equiv.
rewrite/add/=/add_aux.
have->: (opt (id \o widen_ord (ev_rel_ord_le (Base e2))) k) = 
      k by case: k {H C}=>//= ?; by apply/congr1/ord_inj.
have->//: (add_label_advance (Base e2) (is_iso_id e2) al) = al.
rewrite/add_label_advance; case: al {H C}=> // m t x a i.
have EQ: m = (widen_ord (ev_rel_ord_le (Base e2)) m) by apply/ord_inj.
move: {-2}(comp_add _ _ _ _ _ _ _ _) 
(@erefl _ (comp_add _ _ _ (is_iso_id e2) (Base e2) _ m i)).
move=> comp_add0 _. move: comp_add0.
case: (widen_ord (ev_rel_ord_le _) m) / EQ => ?. apply/congr1.
apply/eq_irrelevance. (* separate lemma *)
Qed.


Ltac add_event_tac := move=> *;
  do ?(match goal with
  | H : context [n (add_event _ _ _)] |- _ =>
     exfalso; rewrite !n_add_event/= in H
  end); slia.

Lemma add_evC e al0 (k0 : option 'I_(n e)) 
  (al1 : add_label (add_event e k0 al0))
  (k1 : option 'I_(n (add_event e k0 al0)))
  al1' (k1' : option 'I_(n e))
  (al0' : add_label (add_event e k1' al1'))
  (k0' : option 'I_(n (add_event e k1' al1'))) :
  onat_eq_ord k0 k0' -> 
  onat_eq_ord k1 k1' ->
  eq_al al1 al1' -> eq_al al0 al0' ->
  add_event (add_event e k0 al0) k1 al1 ~~
  add_event (add_event e k1' al1') k0' al0'.
Proof.
move=> Ek0 Ek1 Ea0 Ea1. apply/eq_equviv. rewrite/equviv_nat/is_iso.
set f := (fun k =>
match (n e).+1 =P k with
| ReflectT _ => (n e)
| ReflectF p =>
     match (n e) =P k with
     | ReflectT _  => (n e).+1
     | ReflectF p' => k
     end
end).
have If: injective f.
- move=> x y. rewrite/f; do ?(case: eqP); slia.
exists f; do ?split=>//.
- by rewrite !n_add_event.
move=> k/=. rewrite/f. case: eqP => [<-|];
  rewrite !opredn_add_event; do ?(case: eqP); try add_event_tac;
  rewrite ?n_add_event/=.
- move=> _ _ _. rewrite -opt_comp. move: {f If} Ek1.
  case: k1=> //=; case: k1' al0 {al1  al0' k0' Ea0 Ea1 Ek0} =>// a b c /eqP/=[->].
  case: eqP => [|_]; case: a=> ?/=; first by  move/swap=><-; slia.
  case: eqP=> //<-. slia.
1,2: do ?move=> _. 
- rewrite -opt_comp. move: {f If} Ek0.
  case: k0'=> //=; case: k0 al1 {k1 Ea0 Ek1}=> //= [[/=?? _[/=??]]]/eqP/=[<-].
  by do ?case: eqP; do ?slia.
- move: {-2}(opredn _ k) (@erefl _ (opredn e k)).
  case=> //= a H. have: a < (n e).
- move: H. rewrite /opredn => /ord_dom_to_nat_le. by apply.
- do ?case: eqP; try (rewrite ?n_add_event//=; slia).

move=> k/=. rewrite/f. case: eqP => [<-|];
  rewrite !orffn_add_event; do ?(case: eqP); try add_event_tac;
  rewrite ?n_add_event/=.
- move=> _ _ _. rewrite -opt_comp. move: {f If} Ea0.
  case: al1; case: al1' al0' {Ea1 k0' Ek0} =>//m ??? _ _ ?????/=/and4P[/eqP->].
  do 2?(case: eqP=> //); try (case: m=>/= ?; slia).
1,2: do ?move=> _.
- rewrite -opt_comp. move: {f If} Ea1.
  case: al0'; case: al0 {al1 Ea0 k1 Ek1}=> //= m' ??? _ m ??? _ /and4P[/eqP];
  move=> EQ; move: (EQ)=>->.
  do 2?(case: eqP=> //); first by case: m {EQ}=>/= ?; rewrite n_add_event; slia.
- rewrite -{}EQ. case: m'=>/= ?. slia.
- move: {-2}(orffn _ k) (@erefl _ (orffn e k)).
  case=> //= a H. have: a < (n e).
- move: H. rewrite /orffn => /ord_dom_to_nat_le. by apply.
- do ?case: eqP; try (rewrite ?n_add_event//=; slia).

have fEQ: ((f (n e) = (n e).+1) * (f (n e).+1 = n e))%type
 by split; rewrite/f; do ?(case: eqP); slia.
move=> k/=. have IE: (n e <> k) -> (n e).+1 <> f k.
- move=> nE E. apply/nE/If. by rewrite fEQ.
rewrite !olabn_add_event. do ?(case: eqP); rewrite !n_add_event/=.
1,5,7,8: move=><-; rewrite fEQ; slia.
2: move/IE; slia.
3: rewrite -{3}fEQ=> ?? /If; slia.
- move=> *. move: Ea1. case: al0 {al1 Ea0 Ek1 k1}; case: al0'=> //=.
3: move=> *; move: Ea0; case: al1; case: al1' {al0' Ea1 k0' Ek0}=> //=.
1,3: move=> ?????? /and3P[]; by do ?move/eqP=>->.
1,2: move=> ??????????/and4P[?]; by do ?move/eqP=>->.
move=> *. have->//: f k = k. rewrite/f; do ?(case eqP); slia.
Qed.

Lemma add_lem e1 e e'
  (k : option 'I_(n e1))
  (al : add_label e1)
  (r : e1 -*-> e) (rc :  consistance (add_event e1 k al)) :
    exists e'', (e'' ~~ (add e1 e e k al (is_iso_id e) r rc)) /\
                ((Consist (add_event e1 k al) rc)  -*-> e'').
Proof. move: {1}e1 (@erefl _ e1) k al rc. move=> e0 EQ.
have r0: e0 -*-> e by rewrite EQ.  move: EQ r. elim: r0.
- move=> e2 E r k al rc. exists (add e1 e2 e2 k al (is_iso_id e2) r rc); 
  split=>//.
- have->//: (Consist (add_event e1 k al) rc) =
            (add e1 e2 e2 k al (is_iso_id e2) r rc).
  apply/consist_inj. rewrite/add/=/add_aux. 
  move: E k r al rc. case: e1 / => k r al rc. apply/congr2.
- case: k {rc}=> //= ?. by apply/congr1/ord_inj.
- rewrite /add_label_advance. case: al {rc}=> // m t x a i.
  have EQ: m = (widen_ord (ev_rel_ord_le r) m) by apply/ord_inj.
  move: {-2}(comp_add _ _ _ _ _ _ _ _) 
 (@erefl _ (comp_add _ _ _ (is_iso_id e2) r _ m i)).
  move=> comp_add0 _. move: comp_add0.
  case: (widen_ord (ev_rel_ord_le r) m) / EQ => ?. apply/congr1.
  apply/eq_irrelevance.
- move=> e2 e3 e4 r IHr r' EQ. move: EQ IHr. case: e1 / => /(_ erefl r) IHr.
  move=> r0 k al rc. move: (IHr k al rc).
  set e5 := add e2 e3 e3 k al (is_iso_id e3) r rc.
  move=> [x [E' Rx]]. set e6 := add e2 e4 e4 k al (is_iso_id e4) r0 rc.
  have R: e3 --> e5 by apply/ev_rel_add. case: (r')=> k1 [al' E].
  set e7 := add e3 e5 e5 k1 al' (is_iso_id e5) (Step _ _ (Base e3) R) 
            (consist_of_eq _ _ E).
  have EQV: e7 ~~ e6; first last. 
- have R' : e5 --> e7 by apply/ev_rel_add.
  case: (equiv_ev_rel _ _ _ E' R')=> [y [??]].
  exists y; split; first exact: (@equiv_trans y e7 e6). by apply/(Step x).
  rewrite/e7/e6/=/add_aux=> {e e' e0 IHr Rx x E' e7 e6}.
  move: {-2}(opt (id \o widen_ord (ev_rel_ord_le r0)) k) 
  (@erefl _ (opt (id \o widen_ord (ev_rel_ord_le r0)) k))
  {-2}(add_label_advance r0 (is_iso_id e4) al)
  (@erefl _ (add_label_advance r0 (is_iso_id e4) al)) => o Eo al'' Eal''. 
  have: onat_eq_ord o k by rewrite Eo onat_eq_ord_widen_ord/onat_eq_ord.
  have: eq_al al'' al by rewrite Eal'' eq_al_add_label_advane.
  move: o al'' {Eal'' Eo}. case: (ev_struct_of e4) / E => *.
  apply/add_evC=>/=.
1,2: by rewrite onat_eq_ord_widen_ord/onat_eq_ord 1?eq_sym.
all: by rewrite (eq_al_add_label_advane', eq_al_add_label_advane)// eq_al_sym.
Qed.

Definition confluence_rel e1 e2 :=
  exists e3 e3', (((e1 -*-> e3) * (e2 -*-> e3')) * (e3 ~~ e3'))%type.

Notation "e ~c~ e'" := (confluence_rel e e') (at level 0).

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
apply/(Step e')=> //. rewrite /ev_rel/e'pe1/add/=/add_aux.
by exists (opt (f \o widen_ord (ev_rel_ord_le r)) x), (add_label_advance r I al).
Qed.

Theorem confluence e e1 e2 : e2 -*-> e1 -> e2 -*-> e -> e1 ~c~ e.
Proof. elim=> [*|? l ?? H ?/H?]; by [exists e, e|apply/(confuense_add l)]. Qed.
End confluence.

End transition_system.
