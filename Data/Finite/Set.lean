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

/-
**Finite.Set.finite_of_finite_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.Set.finite_of_finite_image (s : Set α) {f : α -> β} (h : s.InjOn f)
 [Finite (f '' s)] : Finite s
参数：s : Set α；h : s.InjOn f；f '' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)
· 使用定理 `Set.BijOn.bijective`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Se
t β} {f : α → β} (h : Set.BijOn f s t),   Function.Bijective (Set.MapsTo.restric
t f s t ⋯…
-/
theorem Finite.Set.finite_of_finite_image (s : Set α) {f : α → β} (h : s.InjOn f)
    [Finite (f '' s)] : Finite s :=
  Finite.of_equiv _ (Equiv.ofBijective _ h.bijOn_image.bijective).symm
/-
**Finite.of_injective_finite_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.of_injective_finite_range {f : ι -> α} (hf : Function.Injective f) 
[Finite (range f)] : Finite ι
参数：hf : Function.Injective f；range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Function.Injective.codRestrict`：∀ {α : Type u_1} {ι : Sort u_5} {f : ι →
 α} {s : Set α} (h : ∀ (x : ι), f x ∈ s),   Function.Injective f → Function.Inje
ctive (Set.codRestri…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem Finite.of_injective_finite_range {f : ι → α} (hf : Function.Injective f)
    [Finite (range f)] : Finite ι :=
  Finite.of_injective (Set.rangeFactorization f) (hf.codRestrict _)
