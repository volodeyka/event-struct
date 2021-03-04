From mathcomp Require Import ssrfun.
From monae Require Import hierarchy.

Import Monad.
Local Open Scope monae_scope.

Module MonadMorphism.

Record mixin_of (M N : monad) (η : M ~> N) := Mixin {
  _ : forall A, η A \o Ret = Ret;
  _ : forall a b c (f : a -> M b) (g : b -> M c),
        η c \o (f >=> g) =  (η b \o f) >=> (η c \o g)
}.
Structure type (M N : monad) (η : M ~> N) := Pack
  { cpmm : M ~> N ; class : mixin_of M _ cpmm }.
Module Exports.
Coercion cpmm : type >-> Natural.type.
Notation "h ~M> g" := (type h g) (at level 1).
Notation MMorphism p := (Pack (Mixin p)).
End Exports.
End MonadMorphism.
Export MonadMorphism.Exports.
