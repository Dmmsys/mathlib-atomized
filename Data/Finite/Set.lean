/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Fintype.EquivFin

/-!
# Lemmas about `Finite` and `Set`s

In this file we prove two lemmas about `Finite` and `Set`s.

## Tags

finiteness, finite sets
-/

public section


open Set

universe u v w

variable {α : Type u} {β : Type v} {ι : Sort w}

/--
theorem `Finite.Set.finite_of_finite_image` / 定理 `Finite.Set.finite_of_finite_image`

English:
theorem Finite.Set.finite_of_finite_image
  statement: (s : Set α) {f : α -> β} (h : s.InjOn f)
  proof: Finite.of_equiv _ (Equiv.ofBijective _ h.bijOn_image.bijective).symm

中文:
定理 有限.集合.finite_of_finite_image
  结论: (s : 集合 α) {f : α -> β} (h : s.单射限制 f)
  证明: Finite.of_equiv _ (Equiv.ofBijective _ h.bijOn_image.bijective).symm

Depends on / 依赖: Equiv.ofBijective, Finite, Finite.of_equiv, bijOn_image, bijective, h.bijOn_image.bijective, ofBijective, of_equiv
-/
theorem Finite.Set.finite_of_finite_image (s : Set α) {f : α -> β} (h : s.InjOn f)
    [Finite (f '' s)] : Finite s :=
  Finite.of_equiv _ (Equiv.ofBijective _ h.bijOn_image.bijective).symm

/--
theorem `Finite.of_injective_finite_range` / 定理 `Finite.of_injective_finite_range`

English:
theorem Finite.of_injective_finite_range
  statement: {f : ι -> α} (hf : Function.Injective f)
  proof: Finite.of_injective (Set.rangeFactorization f) (hf.codRestrict _)

中文:
定理 有限.of_injective_finite_range
  结论: {f : ι -> α} (hf : 函数.单射 f)
  证明: Finite.of_injective (Set.rangeFactorization f) (hf.codRestrict _)

Depends on / 依赖: Finite, Finite.of_injective, Set.rangeFactorization, codRestrict, hf.codRestrict, of_injective, rangeFactorization
-/
theorem Finite.of_injective_finite_range {f : ι -> α} (hf : Function.Injective f)
    [Finite (range f)] : Finite ι :=
  Finite.of_injective (Set.rangeFactorization f) (hf.codRestrict _)
