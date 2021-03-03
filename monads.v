From mathcomp Require Import ssrfun.
From monae Require Import category.

Import Monad.
Local Open Scope category_scope.

Module MonadMorphism.

Definition kleisli {C : category} {M : monad C} {a b c : C}
  (f : {hom a, M b}) (g : {hom b, M c}) := 
    fun x => Bind g (f x).

Notation "f >=> g" := (kleisli f g) (at level 69).

Record mixin_of (C : category) (M N : monad C) (η : M ~> N) := Mixin {
  _ : forall A, η A \o Ret = Ret;
  _ : forall a b c (f : {hom a, M b}) (g : {hom b, M c}),
        η c \o (f >=> g) = [hom η b \o f] >=> [hom η c \o g]
}.
Structure type (C : category) (M N : monad C) (η : M ~> N) := Pack
  { cpmm : M ~> N ; class : mixin_of C M _ cpmm }.
Module Exports.
Coercion cpmm : type >-> Natural.type.
Notation "h ~M> g" := (type h g) (at level 1).
Notation MMorphism p := (Pack (Mixin p)).
End Exports.
End MonadMorphism.
Export MonadMorphism.Exports.
