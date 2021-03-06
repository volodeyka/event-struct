From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice order. 
From RelationAlgebra Require Import lattice boolean.

From event_struct Require Import utilities pomset.

(******************************************************************************)
(* This file provides a theory of prime event structures.                     *)
(* Prime event structure inherits partial causality order from pomset and     *)
(* also has binary conflict relation (symmetric and irreflexive).             *)
(*                                                                            *)
(*       Prime.eventStruct E == the type of prime event structures.           *)
(*                              A prime event structure consists of           *)
(*                              a causality relation <= (a partial order),    *)
(*                              and a binary conflict relation # (irreflexive *)
(*                              and symmetric).                               *)
(*       Prime.eventType d   == a type of events, i.e. a type equipped with   *)
(*                              prime event structure instance.               *)
(*       Prime.cfg d es x    == a predicate asserting that subset x (given    *)
(*                              as decidable predicate) forms a configuration *)
(*                              of the event structure es.                    *)
(*                              Configuration is a causally-closed and        *)
(*                              conflict-free subset of events.               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.LTheory.
Local Open Scope order_scope.

(* a hack to bypass a shadowing problem caused by relation-algebra import *)
Local Notation symmetric  := Coq.ssr.ssrbool.symmetric.
Local Notation transitive := Coq.ssr.ssrbool.transitive.

Definition hereditary {T : Type} (ca cf : rel T) := 
  forall x y z : T, cf x y -> ca y z -> cf x z.

Module Prime.

Declare Scope prime_eventstruct_scope.
Delimit Scope prime_eventstruct_scope with prime_es.

Local Open Scope prime_eventstruct_scope.

Reserved Notation "x # y" (at level 75, no associativity).

Module PrimeEventStruct.
Section ClassDef. 

Record mixin_of (T0 : Type) (b : Pomset.Pomset.class_of T0)
                (T := Pomset.Pomset.Pack tt b) := Mixin {
  cf : rel T; 

  _  : irreflexive cf;
  _  : symmetric cf;
  _  : hereditary (<=%O) cf; 
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : Pomset.Pomset.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Pomset.Pomset.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@Order.POrder.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack disp cT class.
Definition pomsetEventType := @Pomset.Pomset.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Pomset.Pomset.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion pomsetEventType : type >-> Pomset.eventType.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical pomsetEventType.
End Exports.

End PrimeEventStruct.

Import PrimeEventStruct.Exports.

Notation eventType := PrimeEventStruct.type.
Notation eventStruct := PrimeEventStruct.class_of.

Module Import PrimeEventStructDef.
Section PrimeEventStructDef.

Variable (disp : unit) (E : eventType disp).

Definition cf : rel E := PrimeEventStruct.cf (PrimeEventStruct.class E).

Definition cf_free (X : pred E) : Prop := 
  cf ⊓ (X × X) ≦ bot.

End PrimeEventStructDef.
End PrimeEventStructDef.

Prenex Implicits cf.

Module Export PrimeEventStructSyntax.

Notation "x # y" := (cf x y) : prime_eventstruct_scope.

End PrimeEventStructSyntax.

Module Import PrimeEventStructTheory.
Section PrimeEventStructTheory.

Context {disp : unit} {E : eventType disp}.

Lemma cf_irrefl : irreflexive (cf : rel E).
Proof. by case: E => ? [? []]. Qed.

Lemma cf_sym : symmetric (cf : rel E).
Proof. by case: E => ? [? []]. Qed.

Lemma cf_hered : hereditary (<=%O) (cf : rel E).
Proof. by case: E => ? [? []]. Qed.

Lemma prefix_cf_free (e : E) : cf_free (<= e).
Proof. 
  move=> e1 e2 /=; rewrite /le_bool.
  case/andP=> /cf_hered cf /andP[+ {}/cf].
  rewrite cf_sym; move/cf_hered/[apply].
  by rewrite cf_irrefl.
Qed.

End PrimeEventStructTheory.
End PrimeEventStructTheory.

Section Config.

Context {disp : unit} {E : eventType disp}.

(* configuration *)
Definition cfg (x : pred E) := 
  ca_closed x /\ cf_free x.

End Config.

Module Import ConfigTheory.
Section ConfigTheory.

Context {disp : unit} {E : eventType disp}.

Lemma prefix_cfg (e : E) : cfg (<= e).
Proof.
  split; first by apply: prefix_ca_closed.
  exact: prefix_cf_free.
Qed.

End ConfigTheory.
End ConfigTheory.

End Prime.

Export Prime.PrimeEventStruct.Exports.
Export Prime.PrimeEventStructDef.
Export Prime.PrimeEventStructTheory.
Export Prime.ConfigTheory.
