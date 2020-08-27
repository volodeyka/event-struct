From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssrfun fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*                     ssrnatlia                                             *)

(*Transformation of a constraint (x # y) where (x y : nat) and # is a comparison
relation into the corresponding constraint (x #' y) where #' is
the std lib analogue of #. The transformation is performed on the first such formula
found either in the context or the conclusion of the goal *)
Ltac ssrnatify_rel :=
 match goal with
  (* less or equal (also codes for strict comparison in ssrnat) *)
  | H : is_true (leq _ _) |- _ => move/leP: H => H
  | H : context [ is_true (leq ?a ?b)] |- _ =>
     rewrite <- (rwP (@leP a b)) in H
  | |- is_true (leq _ _) => apply/leP
  | |- context [ is_true (leq ?a ?b)] => rewrite <- (rwP (@leP a b))
  (* Boolean equality *)
  | H : is_true (@eq_op _ _ _) |- _ => move/eqP: H => H
  | |- is_true (@eq_op _ _ _) => apply/eqP
  | H : context [ is_true (@eq_op _ _ _)] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [ is_true (@eq_op _ ?x ?y)] => rewrite <- (rwP (@eqP _ x y))
  (* Negated boolean equality *)
  | H : is_true (negb (@eq_op _  _ _)) |- _ => move/eqP: H => H
  | |- is_true (negb (@eq_op _  _ _)) => apply/eqP
  | H : context [ is_true (negb (@eq_op _ _ _))] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [ is_true (negb (@eq_op _ ?x ?y))] =>
     rewrite <- (rwP (@eqP _ x y))
 end.

(* Converting ssrnat operation to their std lib analogues *)
Ltac ssrnatify_op :=
 match goal with
  (* subn -> minus *)
  | H : context [subn _ _] |- _ => rewrite -!minusE in H
  | |- context [subn _ _] => rewrite -!minusE
  (* addn -> plus *)
  | H : context [addn _ _] |- _ => rewrite -!plusE in H
  | |- context [addn _ _] => rewrite -!plusE
  (* muln -> mult *)
  | H : context [muln _ _] |- _ => rewrite -!multE in H
  | |- context [muln _ _] => rewrite -!multE
 end.

(* Preparing a goal to be solved by lia by translating every formula *)
(* in the context or the conclusion which expresses a constraint on *)
(* some nat into the std lib, Prop, analogues *)
Ltac ssrnatify :=
  repeat progress ssrnatify_rel;
  repeat progress ssrnatify_op.

(* Preprocessing + lia *)
Ltac slia := ssrnatify; lia.
(*                                 some automatic                            *)
Notation swap := 
   (ltac:(let f := fresh "_top_" in let s := fresh "_s_" in move=> f s; move: s f)).

Lemma snd_true3 a b : [|| a, true | b].
Proof. by case: a. Qed.

Lemma trd_true3 a b : [|| b, a | true].
Proof. by case: a; case b. Qed.

Lemma snd_true2 a : a || true.
Proof. by case: a. Qed.

Lemma frth_true4 a b c: [|| a, b, c | true].
Proof. by case: a; case: b; case: c. Qed.

Lemma fifth_true5 a b c d: [|| a, b, c, d | true].
Proof. apply/orP; right. exact: frth_true4. Qed.

Lemma ltS_neq_lt {n N : nat}: (n < N.+1 -> N <> n -> n < N)%N.
Proof. slia. Qed. 


Hint Resolve trd_true3 snd_true3 snd_true2 frth_true4 fifth_true5 : core.

Lemma ltn_ind N (P : 'I_N -> Type) :
  (forall (n : 'I_N), (forall (m : 'I_N), (m < n)%N -> P m) -> P n) ->
  forall n, P n.
Proof.
move=> IH n. have [k le_size] := ubnP (nat_of_ord n). 
elim: k n le_size=>// n IHn k le_size. apply/IH=> *. apply/IHn. slia.
Qed.

(*      continuation of ordinal-domain function on nat using option monad    *)
Section opt_fun.

Definition opt {T T'} (f : T -> T') (x : option T) := 
  if x is some y then some (f y) else None.

Definition ord_dom_to_nat {N T T'} 
  (f : 'I_N -> T) (h : T -> option T') (n : nat) : option T' := 
  (match n < N as L return (n < N = L -> _) with
   | true  => fun pf => h (f (Ordinal pf))
   | false => fun=> None
   end erefl).

Definition ord_f_to_nat {N M} (f : 'I_N -> 'I_M) (n : nat) : nat :=   
  (match n < N as L return (n < N = L -> _) with
   | true  => fun pf => nat_of_ord (f (Ordinal pf))
   | false => fun=> n
end erefl).

Lemma opt_comp {T1 T2 T3} (f : T1 -> T2) (g : T2 -> T3) y : 
  opt (fun z => g (f z)) y = (opt g) ((opt f) y).
Proof. move: y. by case. Qed.

Context {T T' T1 T2 T3 : Type} {N M K : nat}.

Lemma eq_opt {f g : T -> T'}: f =1 g -> opt f =1 opt g.
Proof. move=> E []//=?. by apply/congr1/E. Qed.

Definition onat_eq_ord {N M} (n : option 'I_N) (m : option 'I_M) :=
  (opt (@nat_of_ord N)) n == (opt (@nat_of_ord M)) m.

(*Definition ord_f_to_onat {N M} (f : 'I_N -> option 'I_M) (n : nat) : option nat :=
  (match n < N as L return (n < N = L -> _) with
   | true  => fun pf => (opt (@nat_of_ord M)) (f (Ordinal pf))
   | false => fun=> None
   end erefl).*)

(*Definition T_f_to_onat {T N} (f : 'I_N -> T) (n : nat) : option T := 
(match n < N as L return (n < N = L -> _) with
| true  => fun pf => some (f (Ordinal pf))
| false => fun=> None
end erefl).*)

Lemma ord_f_to_natE (f : 'I_N -> 'I_M) (i : 'I_N) :
  f i = (ord_f_to_nat f) i :> nat.
Proof.
rewrite/ord_f_to_nat.
case: {2}(i < N) {-1}(@erefl _ (i < N)) erefl=> {2 3}->.
- move=> ?. by apply/congr1/congr1/ord_inj.
case: i=> ?/= E. by rewrite E.
Qed.

Lemma ord_f_to_nat_Nlt (f : 'I_N -> 'I_M) n: 
  (n < N = false) -> ord_f_to_nat f n = n.
Proof.
move=> LnN. rewrite/ord_f_to_nat.
by case: {2}(n < N) {-1}(@erefl _ (n < N)) erefl=> {2 3}-> E; first 
by rewrite E in LnN.
Qed.


(*Lemma ord_f_to_onat_le {N M} f n k: 
  some k = () n -> k < M.
Proof.
rewrite/ord_f_to_onat.
case: {2}(n < N) {-1}(@erefl _ (n < N)) erefl=> {2 3}-> //.
move=> nN. rewrite/opt. case: (f (Ordinal (n:=N) (m:=n) nN))=> //.
move=> a []->. done.
Qed.*)

Lemma ord_dom_to_nat_le (f : 'I_N -> option 'I_M) n k: 
  some k = (ord_dom_to_nat f (opt (@nat_of_ord M))) n -> k < M.
Proof.
rewrite/ord_dom_to_nat.
case: {2}(n < N) {-1}(@erefl _ (n < N)) erefl=> {2 3}-> // nN.
rewrite/opt. by case: (f (Ordinal nN))=> // a [->].
Qed.

Lemma ord_dom_to_nat_comp (E : M = N)
  (f : 'I_M -> T) (g : 'I_N -> 'I_M) (h : T -> option T') :
  (ord_dom_to_nat f h) \o (ord_f_to_nat g) =1 ord_dom_to_nat (f \o g) h.
Proof.
move=> k/=. rewrite /ord_dom_to_nat.
case: {2}(_ < M) {-1}(erefl (ord_f_to_nat g k < M)) erefl=> {2 3}->;
case: {2}(k < N) {-1}(erefl (k < N)) erefl=> {2 3}-> //=.
- move=> L ?. apply/congr1/congr1/ord_inj=>/=. rewrite/ord_f_to_nat.
  case: {2}(k < N) {-1}(erefl (k < N)) erefl=> {2 3}-> //=.
- move=> ?. by apply/congr1/congr1/ord_inj. by rewrite L.
- rewrite/ord_f_to_nat=>LkN H. exfalso. move: H.
  case: {2}(k < N) {-1}(erefl (k < N)) erefl=> {2 3}-> //=; first by
  move=> LnNt; rewrite LnNt in LkN.
- by rewrite -E=>->.
rewrite/ord_f_to_nat=>LkN H. exfalso. move: H.
case: {2}(k < N) {-1}(erefl (k < N)) erefl=> {2 3}-> //=; last by
move=> LnNt; rewrite LnNt in LkN. move=> e. by case: (g (Ordinal _))=>/=?->.
Qed.

Lemma ord_dom_to_nat_eq
  {f1 f2 : 'I_M -> T} {h : T -> option T'} :
  f1 =1 f2 -> ord_dom_to_nat f1 h =1 ord_dom_to_nat f2 h.
Proof.
move=> Ef k. rewrite {1}/ord_dom_to_nat.
case: {2}(k < M) {-1}(erefl (k < M)) (erefl (k < M))=> {2 3}->; 
rewrite /ord_dom_to_nat=> e; 
case: {2}(k < M) {-1}(erefl (k < M)) (erefl (k < M))=> {2 3}->=>//.
- move=> ?. apply/congr1. rewrite Ef. by apply/congr1/ord_inj.
- by rewrite e.
move=> E. by rewrite E in e.
Qed.

Lemma ord_dom_to_nat_opt_comp
  (f : 'I_N -> 'I_M) (g : 'I_N -> option 'I_N):
  ord_dom_to_nat (opt f \o g) (opt (@nat_of_ord M)) =1
  (opt (ord_f_to_nat f) \o
  ord_dom_to_nat g (opt (@nat_of_ord N))).
Proof.
move=> k. rewrite {1}/ord_dom_to_nat/=.
case: {2}(k < N) {-1}(erefl (k < N)) erefl=> {2 3}->;
rewrite/ord_dom_to_nat=> L;
case: {2}(k < N) {-1}(erefl (k < N)) erefl=> {2 3}-> L'//; rewrite -?opt_comp.
- have->: (Ordinal L) = (Ordinal L') by apply/ord_inj.
  case: (g (Ordinal L'))=> //= ?. apply/congr1. exact: ord_f_to_natE.
all: exfalso; by rewrite L in L'.
Qed.

(*Lemma ord_f_to_nat_comp {N M K} (f : 'I_N -> 'I_M) (g : 'I_M -> option 'I_K):
  ord_f_to_onat g \o ord_f_to_nat f =1 ord_f_to_onat (g \o f).
Proof. Admitted.

Lemma ord_f_to_nat_eq {M K} {g g1 : 'I_M -> option 'I_K}:
  g1 =1 g -> ord_f_to_onat g1 =1 ord_f_to_onat g.
Proof. Admitted.

Lemma ord_f_to_nat_opt_comp {N M K} (f : 'I_K -> 'I_N) (g : 'I_M -> option 'I_K):
  ord_f_to_onat (opt f \o g) =1 (opt (ord_f_to_nat f) \o ord_f_to_onat g).
Proof. Admitted.

Lemma T_f_to_onat_comp {N M T} (f : 'I_N -> 'I_M) (g : 'I_M -> T): 
  (T_f_to_onat g \o ord_f_to_nat f) =1 T_f_to_onat (g \o f).
Proof. Admitted.

Lemma T_f_to_onat_eq {N T} {f1 f2 : 'I_N -> T}:
f1 =1 f2 -> T_f_to_onat f1 =1 T_f_to_onat f2.
Proof. Admitted.

Definition onat_eq_ord {N M} (n : option 'I_N) (m : option 'I_M) :=
  match n, m with
  | some n, some m => n == m :> nat
  | None, None     => true
  | _   , _        => false
  end.*)

(*Lemma onat_eq_ord_trans {N M K} 
  {n : option 'I_N} (m : option 'I_M) (k : option 'I_K): 
  onat_eq_ord n m -> onat_eq_ord m k -> onat_eq_ord n k.
Proof. by case: n; case m=>//= ??/eqP->. Qed.*)

Lemma onat_eq_ord_widen_ord
  (n : option 'I_N) (L : N <= M) (k : option 'I_K) :
  onat_eq_ord ((opt (id \o widen_ord L)) n) k = 
  onat_eq_ord n k.
Proof. by case: n. Qed.

(*Lemma onat_eq_ord_refl {N} (n : option 'I_N): onat_eq_ord n n.
Proof. by case: n=>/=. Qed.*)

Hint Resolve eqxx : core.

End opt_fun.