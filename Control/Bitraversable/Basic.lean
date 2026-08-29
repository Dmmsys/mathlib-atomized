/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Bifunctor
public import Mathlib.Control.Traversable.Basic

/-!
# Bitraversable type class

Type class for traversing bifunctors.

Simple examples of `Bitraversable` are `Prod` and `Sum`. A more elaborate example is
to define an a-list as:

```
def AList (key val : Type) := List (key × val)
```

Then we can use `f : key → IO key'` and `g : val → IO val'` to manipulate the `AList`'s key
and value respectively with `bitraverse f g : AList key val → IO (AList key' val')`.

## Main definitions

* `Bitraversable`: Bare typeclass to hold the `bitraverse` function.
* `LawfulBitraversable`: Typeclass for the laws of the `bitraverse` function. Similar to
  `LawfulTraversable`.

## References

The concepts and laws are taken from
<https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable iterator functor bifunctor applicative
-/

@[expose] public section


universe u

/--
Definition of `Bitraversable` / `Bitraversable` 的定义

English:
class Bitraversable
  parameters: (t : Type u -> Type u -> Type u)
  extends: Bifunctor t
  axioms and operations (1):
    - bitraverse : forall {m : Type u -> Type u} [Applicative m] {α α' β β'}, (α -> m α') -> (β -> m β') -> t α β -> m (t α' β')

中文:
类 Bitraversable
  参数: (t : 类型u -> 类型u -> 类型u)
  继承: Bifunctor t
  公理与运算 (1 个):
    - bitraverse : 对任意 {m : 类型u -> 类型u} [Applicative m] {α α' β β'}, (α -> m α') -> (β -> m β') -> t α β -> m (t α' β')
-/
class Bitraversable (t : Type u -> Type u -> Type u) extends Bifunctor t where
  bitraverse :
    forall {m : Type u -> Type u} [Applicative m] {α α' β β'},
      (α -> m α') -> (β -> m β') -> t α β -> m (t α' β')

export Bitraversable (bitraverse)

/--
Definition of `bisequence` / `bisequence` 的定义

English:
definition bisequence
  signature: {t m} [Bitraversable t] [Applicative m] {α β}
  body: bitraverse id id

中文:
定义 bisequence
  签名: {t m} [Bitraversable t] [Applicative m] {α β}
  定义体: bitraverse id id

Depends on / 依赖: bitraverse
-/
def bisequence {t m} [Bitraversable t] [Applicative m] {α β} : t (m α) (m β) -> m (t α β) :=
  bitraverse id id

open Functor

/--
Definition of `LawfulBitraversable` / `LawfulBitraversable` 的定义

English:
class LawfulBitraversable
  parameters: (t : Type u -> Type u -> Type u) [Bitraversable t]
  extends: LawfulBifunctor t
  axioms and operations (4):
    - id_bitraverse : forall {α β} (x : t α β), (bitraverse pure pure x : Id _) = pure x
    - comp_bitraverse : forall {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G] {α α' β β' γ γ'} (f : β -> F γ) (f' : β' -> F γ') (g : α -> G β) (g' : α' -> G β') (x : t α α'), bitraverse (Comp.mk ∘ map f ∘ g) (Comp.mk ∘ map f' ∘ g') x = Comp.mk (bitraverse f f' <$> bitraverse g g' x)
    - bitraverse_eq_bimap_id : forall {α α' β β'} (f : α -> β) (f' : α' -> β') (x : t α α'), bitraverse (m := Id) (pure ∘ f) (pure ∘ f') x = pure (bimap f f' x)
    - binaturality : forall {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G] (η : ApplicativeTransformation F G) {α α' β β'} (f : α -> F β) (f' : α' -> F β') (x : t α α'), η (bitraverse f f' x) = bitraverse (@η _ ∘ f) (@η _ ∘ f') x

中文:
类 LawfulBitraversable
  参数: (t : 类型u -> 类型u -> 类型u) [Bitraversable t]
  继承: LawfulBifunctor t
  公理与运算 (4 个):
    - id_bitraverse : 对任意 {α β} (x : t α β), (bitraverse pure pure x : Id _) = pure x
    - comp_bitraverse : 对任意 {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G] {α α' β β' γ γ'} (f : β -> F γ) (f' : β' -> F γ') (g : α -> G β) (g' : α' -> G β') (x : t α α'), bitraverse (Comp.mk ∘ map f ∘ g) (Comp.mk ∘ map f' ∘ g') x = Comp.mk (bitraverse f f' <$> bitraverse g g' x)
    - bitraverse_eq_bimap_id : 对任意 {α α' β β'} (f : α -> β) (f' : α' -> β') (x : t α α'), bitraverse (m := Id) (pure ∘ f) (pure ∘ f') x = pure (bimap f f' x)
    - binaturality : 对任意 {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G] (η : ApplicativeTransformation F G) {α α' β β'} (f : α -> F β) (f' : α' -> F β') (x : t α α'), η (bitraverse f f' x) = bitraverse (@η _ ∘ f) (@η _ ∘ f') x
-/
class LawfulBitraversable (t : Type u -> Type u -> Type u) [Bitraversable t] : Prop
  extends LawfulBifunctor t where
  id_bitraverse : forall {α β} (x : t α β), (bitraverse pure pure x : Id _) = pure x
  comp_bitraverse :
    forall {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G]
      {α α' β β' γ γ'} (f : β -> F γ) (f' : β' -> F γ') (g : α -> G β) (g' : α' -> G β') (x : t α α'),
      bitraverse (Comp.mk ∘ map f ∘ g) (Comp.mk ∘ map f' ∘ g') x =
        Comp.mk (bitraverse f f' <$> bitraverse g g' x)
  bitraverse_eq_bimap_id :
    forall {α α' β β'} (f : α -> β) (f' : α' -> β') (x : t α α'),
      bitraverse (m := Id) (pure ∘ f) (pure ∘ f') x = pure (bimap f f' x)
  binaturality :
    forall {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G]
      (η : ApplicativeTransformation F G) {α α' β β'} (f : α -> F β) (f' : α' -> F β') (x : t α α'),
      η (bitraverse f f' x) = bitraverse (@η _ ∘ f) (@η _ ∘ f') x

export LawfulBitraversable (id_bitraverse comp_bitraverse bitraverse_eq_bimap_id)

open LawfulBitraversable

attribute [higher_order bitraverse_id_id] id_bitraverse

attribute [higher_order bitraverse_comp] comp_bitraverse

attribute [higher_order] binaturality bitraverse_eq_bimap_id

export LawfulBitraversable (bitraverse_id_id bitraverse_comp)
