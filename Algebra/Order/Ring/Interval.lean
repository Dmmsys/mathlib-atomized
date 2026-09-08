/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Ring.Cast

/-! # Intervals of integers in strict ordered rings

These statements could perhaps be generalized, or there could be other variations provided (e.g.,
for `ℕ` instead of `ℤ`, or a version for locally finite `SuccOrder`s with strictly monotone
functions), but for now these are the ones that have found utility in practice (e.g., for lemmas
about `Real.Angle`).
-/

public section

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Let `k : ℤ`. If its multiple of `r > 0` in a strict ordered ring lies strictly between
multiples `r * (m - 1)` and `r * (n + 1)`, then `m ≤ k ≤ n`. -/
/-
**IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo {r : R} (hr : 0 < r) {k m n
 : Int} (h : r * k in Set.Ioo (r * (m - 1 : Int)) (r * (n + 1 : Int))) : k in Fi
nset.Icc m n
参数：hr : 0 < r；h : r * k in Set.Ioo (r * (m - 1 : Int)) (r * (n + 1 : Int))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_lt_mul_iff_right₀`：mul_lt_mul_iff_right₀ [PosMulStrictMono α] [PosMu
lReflectLT α] (a0 : 0 < a) : a * b < a * c ↔ b < c where mp h
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R

--- 原说明 ---
Let `k : ℤ`. If its multiple of `r > 0` in a strict ordered ring lies strictly b
etween
multiples `r * (m - 1)` and `r * (n + 1)`, then `m ≤ k ≤ n`.
-/
lemma IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo
    {r : R} (hr : 0 < r) {k m n : ℤ} (h : r * k ∈ Set.Ioo (r * (m - 1 : ℤ)) (r * (n + 1 : ℤ))) :
    k ∈ Finset.Icc m n := by
  simp only [Set.mem_Ioo, mul_lt_mul_iff_right₀ hr, Int.cast_lt] at h
  grind [Int.lt_iff_add_one_le]

/-- Let `k : ℤ`. If its multiple of `r > 0` in a strict ordered ring lies strictly between
the preceding and succeeding multiples `r * (m - 1)` and `r * (m + 1)`, then `k = m`. -/
/-
**IsStrictOrderedRing.int_eq_of_mul_mem_Ioo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsStrictOrderedRing.int_eq_of_mul_mem_Ioo {r : R} (hr : 0 < r) {k m : Int}
 (h : r * k in Set.Ioo (r * (m - 1 : Int)) (r * (m + 1 : Int))) : k = m
参数：hr : 0 < r；h : r * k in Set.Ioo (r * (m - 1 : Int)) (r * (m + 1 : Int))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用引理 `IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo`：IsStrictOrderedRing.int_
mem_Icc_of_mul_mem_Ioo {r : R} (hr : 0 < r) {k m n : Int} (h : r * k in Set.Ioo 
(r * (m - 1 : Int)) (r * (n + 1 : In…

--- 原说明 ---
Let `k : ℤ`. If its multiple of `r > 0` in a strict ordered ring lies strictly b
etween
the preceding and succeeding multiples `r * (m - 1)` and `r * (m + 1)`, then `k 
= m`.
-/
lemma IsStrictOrderedRing.int_eq_of_mul_mem_Ioo
    {r : R} (hr : 0 < r) {k m : ℤ} (h : r * k ∈ Set.Ioo (r * (m - 1 : ℤ)) (r * (m + 1 : ℤ))) :
    k = m := by
  simpa using int_mem_Icc_of_mul_mem_Ioo hr h
