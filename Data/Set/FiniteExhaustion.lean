/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Finite.Prod

/-!
# Finite Exhaustions

This file defines a structure called `FiniteExhaustion` which represents an exhaustion of a
countable set by an increasing sequence of finite sets. Given a countable set `s`,
`FiniteExhaustion.choice s` is a choice of a finite exhaustion.
-/

@[expose] public section

open Set

/-- A `FiniteExhaustion` of a set `s` is a monotonically increasing sequence
of finite sets such that their union is `s`. -/
/-
**Set.FiniteExhaustion** 是 Mathlib 中的一个归纳类型，位于命名空间 `Set`。
形式化陈述：{α : Type u_1} → Set α → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FiniteExhaustion` of a set `s` is a monotonically increasing sequence
of finite sets such that their union is `s`.
-/
structure Set.FiniteExhaustion {α : Type*} (s : Set α) where
  /-- The underlying sequence of a `FiniteExhaustion`. -/
  toFun : ℕ → Set α
  /-- Every set in a `FiniteExhaustion` is finite. -/
  finite' : ∀ n, Finite (toFun n)
  /-- The sequence of sets in a `FiniteExhaustion` are monotonically increasing. -/
  subset_succ' : ∀ n, toFun n ⊆ toFun (n + 1)
  /-- The union of all sets in a `FiniteExhaustion` equals `s` -/
  iUnion_eq' : ⋃ n, toFun n = s

namespace Set.FiniteExhaustion

/-
**Set.FiniteExhaustion.** 是 Mathlib 中的一个实例，位于命名空间 `Set.FiniteExhaustion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {s : Set α} : FunLike (FiniteExhaustion s) ℕ (Set α) where
  coe := toFun
  coe_injective | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
/-
**Set.FiniteExhaustion.** 是 Mathlib 中的一个实例，位于命名空间 `Set.FiniteExhaustion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {s : Set α} : OrderHomClass (FiniteExhaustion s) Nat (Set α) where
  map_rel K _ _ h := monotone_nat_of_le_succ (fun n ↦ K.subset_succ' n) h
/-
**Set.FiniteExhaustion.** 是 Mathlib 中的一个实例，位于命名空间 `Set.FiniteExhaustion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {s : Set α} {K : FiniteExhaustion s} {n : ℕ} : Finite (K n) :=
  K.finite' n

variable {α : Type*} {s : Set α} (K : FiniteExhaustion s)

@[simp]
/-
**Set.FiniteExhaustion.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set.FiniteExhaust
ion`。
形式化陈述：toFun_eq_coe : K.toFun = K
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe : K.toFun = K := rfl
/-
**Set.FiniteExhaustion.finite** 是 Mathlib 中的一个定理，位于命名空间 `Set.FiniteExhaustion`。
形式化陈述：∀ {α : Type u_1} {s : Set α} (K : s.FiniteExhaustion) (n : ℕ), (K n).Finit
e
参数：K : s.FiniteExhaustion；n : ℕ；K n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.FiniteExhaustion.finite'`：∀ {α : Type u_1} {s : Set α} (self : s.Fin
iteExhaustion) (n : ℕ), Finite ↑(self.toFun n)
-/
protected theorem finite (n : ℕ) : (K n).Finite := K.finite' n
/-
**Set.FiniteExhaustion.subset_succ** 是 Mathlib 中的一个定理，位于命名空间 `Set.FiniteExhausti
on`。
形式化陈述：subset_succ (n : Nat) : K n subseteq K (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.FiniteExhaustion.subset_succ'`：∀ {α : Type u_1} {s : Set α} (self : 
s.FiniteExhaustion) (n : ℕ), self.toFun n ⊆ self.toFun (n + 1)
-/
theorem subset_succ (n : ℕ) : K n ⊆ K (n + 1) := K.subset_succ' n

@[gcongr]
/-
**Set.FiniteExhaustion.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.FiniteExhaustion`。
形式化陈述：∀ {α : Type u_1} {s : Set α} (K : s.FiniteExhaustion) {m n : ℕ}, m ≤ n → K
 m ⊆ K n
参数：K : s.FiniteExhaustion。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `Set.FiniteExhaustion.instOrderHomClassNat`：∀ {α : Type u_1} {s : Set α},
 OrderHomClass s.FiniteExhaustion ℕ (Set α)
-/
protected theorem mono {m n : ℕ} (h : m ≤ n) : K m ⊆ K n :=
  OrderHomClass.mono K h

@[simp]
/-
**Set.FiniteExhaustion.iUnion_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.FiniteExhaustion
`。
形式化陈述：iUnion_eq : ⋃ n, K n = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.FiniteExhaustion.iUnion_eq'`：∀ {α : Type u_1} {s : Set α} (self : s.
FiniteExhaustion), ⋃ n, self.toFun n = s
-/
theorem iUnion_eq : ⋃ n, K n = s :=
  K.iUnion_eq'

/-- A choice of a `FiniteExhaustion` for a countable set `s`. -/
/-
**Set.FiniteExhaustion._root_.Set.Countable.finiteExhaustion** 是 Mathlib 中的一个定义，
位于命名空间 `Set.FiniteExhaustion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of a `FiniteExhaustion` for a countable set `s`.
-/
noncomputable def _root_.Set.Countable.finiteExhaustion {s : Set α} (hs : s.Countable) :
    FiniteExhaustion s := by
  apply Classical.choice
  by_cases h : Nonempty s
  · obtain ⟨f, hf⟩ := @exists_surjective_nat s h hs
    refine ⟨fun n ↦ (Subtype.val ∘ f) '' {i | i ≤ n}, ?_, ?_, ?_⟩
    · exact fun n ↦ Finite.image _ (finite_le_nat n)
    · grind
    · simp [← image_image, ← image_iUnion, iUnion_le_nat, range_eq_univ.mpr hf]
  · refine ⟨fun _ ↦ ∅, by simp [Finite.to_subtype], fun n ↦ by simp, ?_⟩
    simp [Set.not_nonempty_iff_eq_empty'.mp h]
/-
**Set.FiniteExhaustion._root_.Set.nonempty_finiteExhaustion_iff** 是 Mathlib 中的一个
引理，位于命名空间 `Set.FiniteExhaustion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.nonempty_finiteExhaustion_iff {s : Set α} :
    Nonempty s.FiniteExhaustion ↔ s.Countable := by
  refine ⟨fun ⟨K⟩ ↦ ?_, fun h ↦ ⟨h.finiteExhaustion⟩⟩
  rw [← K.iUnion_eq]
  exact countable_iUnion <| fun i ↦ (K.finite i).countable

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")]
alias Set.nonempty_finiteExhaustion_iff := Set.nonempty_finiteExhaustion_iff

section prod

variable {β : Type*} {t : Set β} (K' : FiniteExhaustion t)

/-- Given `K : FiniteExhaustion s` and `K' : FiniteExhaustion t`, `FiniteExhaustion.prod K K'`
is the finite exhaustion on `s ×ˢ t` given by the pointwise set product of the exhaustions. -/
/-
**Set.FiniteExhaustion.prod** 是 Mathlib 中的一个定义，位于命名空间 `Set.FiniteExhaustion`。
形式化陈述：{α : Type u_1} →   {s : Set α} → s.FiniteExhaustion → {β : Type u_2} → {t 
: Set β} → t.FiniteExhaustion → (s ×ˢ t).FiniteExhaustion
参数：s ×ˢ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `K : FiniteExhaustion s` and `K' : FiniteExhaustion t`, `FiniteExhaustion.
prod K K'`
is the finite exhaustion on `s ×ˢ t` given by the pointwise set product of the e
xhaustions.
-/
protected def prod :
    FiniteExhaustion (s ×ˢ t) :=
  { toFun n := K n ×ˢ K' n
    finite' n := (K.finite n).prod (K'.finite n)
    subset_succ' := fun n ↦ Set.prod_mono (K.subset_succ n) (K'.subset_succ n)
    iUnion_eq' := by
      rw [Set.iUnion_prod_of_monotone (OrderHomClass.mono K) (OrderHomClass.mono K'),
          K.iUnion_eq, K'.iUnion_eq] }
/-
**Set.FiniteExhaustion.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Set.FiniteExhaustio
n`。
形式化陈述：∀ {α : Type u_1} {s : Set α} (K : s.FiniteExhaustion) {β : Type u_2} {t : 
Set β} (K' : t.FiniteExhaustion) (n : ℕ),   (K.prod K') n = K n ×ˢ K' n
参数：K : s.FiniteExhaustion；K' : t.FiniteExhaustion；n : ℕ；K.prod K'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem prod_apply (n : ℕ) : (K.prod K') n = K n ×ˢ K' n := by rfl

end prod

end Set.FiniteExhaustion

