/-
Copyright (c) 2023 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha, Thomas Browning
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!

This file defines the harmonic numbers.

* `Mathlib/NumberTheory/Harmonic/Int.lean` proves that the `n`th harmonic number is not an integer.
* `Mathlib/NumberTheory/Harmonic/Bounds.lean` provides basic log bounds.

-/

@[expose] public section

/-- The nth-harmonic number defined as a finset sum of consecutive reciprocals. -/
/-
**harmonic** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：harmonic : Nat -> Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nth-harmonic number defined as a finset sum of consecutive reciprocals.
-/
def harmonic : ℕ → ℚ := fun n => ∑ i ∈ Finset.range n, (↑(i + 1))⁻¹

@[simp]
/-
**harmonic_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：harmonic_zero : harmonic 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma harmonic_zero : harmonic 0 = 0 :=
  rfl

@[simp]
/-
**harmonic_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：harmonic_succ (n : Nat) : harmonic (n + 1) = harmonic n + (↑(n + 1))⁻¹
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
-/
lemma harmonic_succ (n : ℕ) : harmonic (n + 1) = harmonic n + (↑(n + 1))⁻¹ :=
  Finset.sum_range_succ ..
