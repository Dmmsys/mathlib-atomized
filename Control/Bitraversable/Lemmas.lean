/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Bitraversable.Basic

/-!
# Bitraversable Lemmas

## Main definitions
  * tfst - traverse on first functor argument
  * tsnd - traverse on second functor argument

## Lemmas

Combination of
  * bitraverse
  * tfst
  * tsnd

with the applicatives `id` and `comp`

## References

* Hackage: <https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable functor bifunctor applicative


-/

public section


universe u

variable {t : Type u -> Type u -> Type u} [Bitraversable t]
variable {β : Type u}

namespace Bitraversable

open Functor LawfulApplicative

variable {F G : Type u -> Type u} [Applicative F] [Applicative G]

/--
Definition of `tfst` / `tfst` 的定义

English:
abbreviation tfst
  signature: {α α'} (f : α -> F α')
  body: bitraverse f pure

中文:
缩写 tfst
  签名: {α α'} (f : α -> F α')
  定义体: bitraverse f pure

Depends on / 依赖: bitraverse
-/
abbrev tfst {α α'} (f : α -> F α') : t α β -> F (t α' β) :=
  bitraverse f pure

/--
Definition of `tsnd` / `tsnd` 的定义

English:
abbreviation tsnd
  signature: {α α'} (f : α -> F α')
  body: bitraverse pure f

中文:
缩写 tsnd
  签名: {α α'} (f : α -> F α')
  定义体: bitraverse pure f

Depends on / 依赖: bitraverse
-/
abbrev tsnd {α α'} (f : α -> F α') : t β α -> F (t β α') :=
  bitraverse pure f

variable [LawfulBitraversable t] [LawfulApplicative F] [LawfulApplicative G]

@[higher_order tfst_id]
/--
theorem `id_tfst` / 定理 `id_tfst`

English:
theorem id_tfst
  statement: forall {α β} (x : t α β), tfst (F := Id) pure x = pure x
  proof: id_bitraverse

@[higher_order tsnd_id]

中文:
定理 id_tfst
  结论: 对任意 {α β} (x : t α β), tfst (F := Id) pure x = pure x
  证明: id_bitraverse

@[higher_order tsnd_id]
-/
theorem id_tfst : forall {α β} (x : t α β), tfst (F := Id) pure x = pure x :=
  id_bitraverse

@[higher_order tsnd_id]
/--
theorem `id_tsnd` / 定理 `id_tsnd`

English:
theorem id_tsnd
  statement: forall {α β} (x : t α β), tsnd (F := Id) pure x = pure x
  proof: id_bitraverse

@[higher_order tfst_comp_tfst]

中文:
定理 id_tsnd
  结论: 对任意 {α β} (x : t α β), tsnd (F := Id) pure x = pure x
  证明: id_bitraverse

@[higher_order tfst_comp_tfst]
-/
theorem id_tsnd : forall {α β} (x : t α β), tsnd (F := Id) pure x = pure x :=
  id_bitraverse

@[higher_order tfst_comp_tfst]
/--
theorem `comp_tfst` / 定理 `comp_tfst`

English:
theorem comp_tfst
  given: {α₀ α₁ α₂ β} (f : α₀ -> F α₁) (f' : α₁ -> G α₂) (x : t α₀ β)
  proof: by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, tfst, map_pure, Pure.pure]

@[higher_order tfst_comp_tsnd]

中文:
定理 comp_tfst
  条件: {α₀ α₁ α₂ β} (f : α₀ -> F α₁) (f' : α₁ -> G α₂) (x : t α₀ β)
  证明: by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, tfst, map_pure, Pure.pure]

@[higher_order tfst_comp_tsnd]

Depends on / 依赖: Function, Function.comp_def, Pure.pure, comp_bitraverse, comp_def, map_pure
-/
theorem comp_tfst {α₀ α₁ α₂ β} (f : α₀ -> F α₁) (f' : α₁ -> G α₂) (x : t α₀ β) :
    Comp.mk (tfst f' <$> tfst f x) = tfst (Comp.mk ∘ map f' ∘ f) x := by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, tfst, map_pure, Pure.pure]

@[higher_order tfst_comp_tsnd]
/--
theorem `tfst_tsnd` / 定理 `tfst_tsnd`

English:
theorem tfst_tsnd
  given: {α₀ α₁ β₀ β₁} (f : α₀ -> F α₁) (f' : β₀ -> G β₁) (x : t α₀ β₀)
  proof: by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, map_pure]

@[higher_order tsnd_comp_tfst]

中文:
定理 tfst_tsnd
  条件: {α₀ α₁ β₀ β₁} (f : α₀ -> F α₁) (f' : β₀ -> G β₁) (x : t α₀ β₀)
  证明: by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, map_pure]

@[higher_order tsnd_comp_tfst]

Depends on / 依赖: Function, Function.comp_def, comp_bitraverse, comp_def, map_pure
-/
theorem tfst_tsnd {α₀ α₁ β₀ β₁} (f : α₀ -> F α₁) (f' : β₀ -> G β₁) (x : t α₀ β₀) :
    Comp.mk (tfst f <$> tsnd f' x)
      = bitraverse (Comp.mk ∘ pure ∘ f) (Comp.mk ∘ map pure ∘ f') x := by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, map_pure]

@[higher_order tsnd_comp_tfst]
/--
theorem `tsnd_tfst` / 定理 `tsnd_tfst`

English:
theorem tsnd_tfst
  given: {α₀ α₁ β₀ β₁} (f : α₀ -> F α₁) (f' : β₀ -> G β₁) (x : t α₀ β₀)
  proof: by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, map_pure]

@[higher_order tsnd_comp_tsnd]

中文:
定理 tsnd_tfst
  条件: {α₀ α₁ β₀ β₁} (f : α₀ -> F α₁) (f' : β₀ -> G β₁) (x : t α₀ β₀)
  证明: by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, map_pure]

@[higher_order tsnd_comp_tsnd]

Depends on / 依赖: Function, Function.comp_def, comp_bitraverse, comp_def, map_pure
-/
theorem tsnd_tfst {α₀ α₁ β₀ β₁} (f : α₀ -> F α₁) (f' : β₀ -> G β₁) (x : t α₀ β₀) :
    Comp.mk (tsnd f' <$> tfst f x)
      = bitraverse (Comp.mk ∘ map pure ∘ f) (Comp.mk ∘ pure ∘ f') x := by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, map_pure]

@[higher_order tsnd_comp_tsnd]
/--
theorem `comp_tsnd` / 定理 `comp_tsnd`

English:
theorem comp_tsnd
  given: {α β₀ β₁ β₂} (g : β₀ -> F β₁) (g' : β₁ -> G β₂) (x : t α β₀)
  proof: by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, map_pure]
  rfl

中文:
定理 comp_tsnd
  条件: {α β₀ β₁ β₂} (g : β₀ -> F β₁) (g' : β₁ -> G β₂) (x : t α β₀)
  证明: by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, map_pure]
  rfl

Depends on / 依赖: Function, Function.comp_def, comp_bitraverse, comp_def, map_pure
-/
theorem comp_tsnd {α β₀ β₁ β₂} (g : β₀ -> F β₁) (g' : β₁ -> G β₂) (x : t α β₀) :
    Comp.mk (tsnd g' <$> tsnd g x) = tsnd (Comp.mk ∘ map g' ∘ g) x := by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, map_pure]
  rfl

open Bifunctor Function

@[higher_order]
/--
theorem `tfst_eq_fst_id` / 定理 `tfst_eq_fst_id`

English:
theorem tfst_eq_fst_id
  given: {α α' β} (f : α -> α') (x : t α β)
  proof: by
  apply bitraverse_eq_bimap_id

@[higher_order]

中文:
定理 tfst_eq_fst_id
  条件: {α α' β} (f : α -> α') (x : t α β)
  证明: by
  apply bitraverse_eq_bimap_id

@[higher_order]

Depends on / 依赖: bitraverse_eq_bimap_id
-/
theorem tfst_eq_fst_id {α α' β} (f : α -> α') (x : t α β) :
    tfst (F := Id) (pure ∘ f) x = pure (fst f x) := by
  apply bitraverse_eq_bimap_id

@[higher_order]
/--
theorem `tsnd_eq_snd_id` / 定理 `tsnd_eq_snd_id`

English:
theorem tsnd_eq_snd_id
  given: {α β β'} (f : β -> β') (x : t α β)
  proof: by
  apply bitraverse_eq_bimap_id

中文:
定理 tsnd_eq_snd_id
  条件: {α β β'} (f : β -> β') (x : t α β)
  证明: by
  apply bitraverse_eq_bimap_id

Depends on / 依赖: bitraverse_eq_bimap_id
-/
theorem tsnd_eq_snd_id {α β β'} (f : β -> β') (x : t α β) :
    tsnd (F := Id) (pure ∘ f) x = pure (snd f x) := by
  apply bitraverse_eq_bimap_id

attribute [functor_norm] comp_bitraverse comp_tsnd comp_tfst tsnd_comp_tsnd tsnd_comp_tfst
  tfst_comp_tsnd tfst_comp_tfst bitraverse_comp bitraverse_id_id tfst_id tsnd_id

end Bitraversable
