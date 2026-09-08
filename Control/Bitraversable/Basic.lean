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

/-- Lawless bitraversable bifunctor. This only holds data for the bimap and bitraverse. -/
/-
**Bitraversable** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(Type u → Type u → Type u) → Type (u + 1)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lawless bitraversable bifunctor. This only holds data for the bimap and bitraver
se.
-/
class Bitraversable (t : Type u → Type u → Type u) extends Bifunctor t where
  bitraverse :
    ∀ {m : Type u → Type u} [Applicative m] {α α' β β'},
      (α → m α') → (β → m β') → t α β → m (t α' β')

export Bitraversable (bitraverse)

/-- A bitraversable functor commutes with all applicative functors. -/
/-
**bisequence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：bisequence {t m} [Bitraversable t] [Applicative m] {α β} : t (m α) (m β) -
> m (t α β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bitraversable functor commutes with all applicative functors.
-/
def bisequence {t m} [Bitraversable t] [Applicative m] {α β} : t (m α) (m β) → m (t α β) :=
  bitraverse id id

open Functor

/-- Bifunctor. This typeclass asserts that a lawless bitraversable bifunctor is lawful. -/
/-
**LawfulBitraversable** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：LawfulBitraversable (t : Type u -> Type u -> Type u) [Bitraversable t] : P
rop extends LawfulBifunctor t where id_bitraverse : forall {α β} (x : t α β), (b
itraverse pure pure x : Id _) = pure x comp_bitraverse : forall {F G} [Applicati
ve F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G] {α α' β β' γ γ
'} (f : β -> F γ) (f' : β' -> F γ') (g : α -> G β) (g' : α' -> G β') (x : t α α'
), bitraverse (Comp.mk ∘ map f ∘ g) (Comp.mk ∘ map f' ∘ g') x = Comp.mk (bitrave
rse f f' <$> bitraverse g 
参数：t : Type u -> Type u -> Type u。
继承自：LawfulBifunctor t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bifunctor. This typeclass asserts that a lawless bitraversable bifunctor is lawf
ul.
-/
class LawfulBitraversable (t : Type u → Type u → Type u) [Bitraversable t] : Prop
  extends LawfulBifunctor t where
  id_bitraverse : ∀ {α β} (x : t α β), (bitraverse pure pure x : Id _) = pure x
  comp_bitraverse :
    ∀ {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G]
      {α α' β β' γ γ'} (f : β → F γ) (f' : β' → F γ') (g : α → G β) (g' : α' → G β') (x : t α α'),
      bitraverse (Comp.mk ∘ map f ∘ g) (Comp.mk ∘ map f' ∘ g') x =
        Comp.mk (bitraverse f f' <$> bitraverse g g' x)
  bitraverse_eq_bimap_id :
    ∀ {α α' β β'} (f : α → β) (f' : α' → β') (x : t α α'),
      bitraverse (m := Id) (pure ∘ f) (pure ∘ f') x = pure (bimap f f' x)
  binaturality :
    ∀ {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G]
      (η : ApplicativeTransformation F G) {α α' β β'} (f : α → F β) (f' : α' → F β') (x : t α α'),
      η (bitraverse f f' x) = bitraverse (@η _ ∘ f) (@η _ ∘ f') x

export LawfulBitraversable (id_bitraverse comp_bitraverse bitraverse_eq_bimap_id)

open LawfulBitraversable

attribute [higher_order bitraverse_id_id] id_bitraverse

attribute [higher_order bitraverse_comp] comp_bitraverse

attribute [higher_order] binaturality bitraverse_eq_bimap_id

export LawfulBitraversable (bitraverse_id_id bitraverse_comp)
