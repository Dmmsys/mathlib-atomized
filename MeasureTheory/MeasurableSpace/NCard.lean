/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of `Set.encard` and `Set.ncard`

In this file we prove that `Set.encard` and `Set.ncard` are measurable functions,
provided that the ambient space is countable.
-/

public section

open Set

variable {α : Type*} [Countable α]

@[fun_prop]
/-
**measurable_encard** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_encard : Measurable (Set.encard : Set α -> Nat∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENat.measurable_iff`：ENat.measurable_iff {α : Type*} [MeasurableSpace α]
 {f : α -> Nat∞} : Measurable f ↔ forall n : Nat, MeasurableSet (f ⁻¹' {↑n})
· 使用定理 `Set.Countable.measurableSet`：Set.Countable.measurableSet {s : Set α} (hs
 : s.Countable) : MeasurableSet s
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.finite_of_encard_eq_coe`：finite_of_encard_eq_coe {k : Nat} (h : s.en
card = k) : s.Finite
· 使用定理 `Set.Countable.ofPred_finite`：∀ {α : Type u} [Countable α], {s | s.Finite
}.Countable
-/
theorem measurable_encard : Measurable (Set.encard : Set α → ℕ∞) :=
  ENat.measurable_iff.2 fun _n ↦ Countable.measurableSet <| Countable.ofPred_finite.mono fun _s hs ↦
    finite_of_encard_eq_coe hs

@[fun_prop]
/-
**measurable_ncard** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_ncard : Measurable (Set.ncard : Set α -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Measurable.of_discrete`：∀ {α : Type u_1} {β : Type u_2} [inst : Measurab
leSpace α] [inst_1 : MeasurableSpace β] [DiscreteMeasurableSpace α]   {f : α → β
}, Measurabl…
· 使用定理 `measurable_encard`：measurable_encard : Measurable (Set.encard : Set α ->
 Nat∞)
-/
theorem measurable_ncard : Measurable (Set.ncard : Set α → ℕ) :=
  Measurable.of_discrete.comp measurable_encard
