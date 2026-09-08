/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama

/-!

# Lemmas about square of maximal ideal of local ring

-/

public section

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

variable (R) in
/-
**IsLocalRing.maximalIdeal_sq_lt_maximalIdeal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalRing.maximalIdeal_sq_lt_maximalIdeal : maximalIdeal R ^ 2 < maximal
Ideal R ↔ ¬ IsField R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsLocalRing.isField_iff_maximalIdeal_eq`：isField_iff_maximalIdeal_eq : I
sField R ↔ maximalIdeal R = ⊥
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator`：eq_bot_of_
eq_ideal_smul_of_le_jacobson_annihilator {I : Ideal R} {N : Submodule R M} (hN :
 FG N) (hIN : N = I • N) (hIjac : I <= N.annihilat…
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.maximalIdeal_le_jacobson`：maximalIdeal_le_jacobson (I : Idea
l R) : IsLocalRing.maximalIdeal R <= I.jacobson
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.mul_bot`：mul_bot : M * ⊥ = ⊥
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsLocalRing.maximalIdeal_sq_lt_maximalIdeal :
    maximalIdeal R ^ 2 < maximalIdeal R ↔ ¬ IsField R := by
  trans ¬ maximalIdeal R ^ 2 = maximalIdeal R
  · simp [lt_iff_le_and_ne, Ideal.pow_le_self]
  · rw [IsLocalRing.isField_iff_maximalIdeal_eq, pow_two]
    refine Iff.not ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    exact Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator (IsNoetherian.noetherian _)
      h.symm (maximalIdeal_le_jacobson _)

/-- In a Noetherian local ring of positive Krull dimension,
the square of the maximal ideal is strictly contained in the maximal ideal. -/
/-
**IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero (h : ringKrullDim R
 != 0) : (maximalIdeal R) ^ 2 < maximalIdeal R
参数：h : ringKrullDim R != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsLocalRing.maximalIdeal_sq_lt_maximalIdeal`：IsLocalRing.maximalIdeal_sq
_lt_maximalIdeal : maximalIdeal R ^ 2 < maximalIdeal R ↔ ¬ IsField R
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `ringKrullDim_eq_zero_of_isField`：ringKrullDim_eq_zero_of_isField {F : Ty
pe*} [CommRing F] (hF : IsField F) : ringKrullDim F = 0

--- 原说明 ---
In a Noetherian local ring of positive Krull dimension,
the square of the maximal ideal is strictly contained in the maximal ideal.
-/
lemma IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero (h : ringKrullDim R ≠ 0) :
    (maximalIdeal R) ^ 2 < maximalIdeal R :=
  (maximalIdeal_sq_lt_maximalIdeal R).mpr (ringKrullDim_eq_zero_of_isField.mt h)

@[deprecated "Use `IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero` instead"
  (since := "2026-05-13")]
/-
**IsLocalRing.maximalIdeal_sq_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalRing.maximalIdeal_sq_lt (h : 0 < ringKrullDim R) : (maximalIdeal R)
 ^ 2 < maximalIdeal R
参数：h : 0 < ringKrullDim R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero`：IsLocalRing.maxi
malIdeal_sq_lt_of_ringKrullDim_ne_zero (h : ringKrullDim R != 0) : (maximalIdeal
 R) ^ 2 < maximalIdeal R
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma IsLocalRing.maximalIdeal_sq_lt (h : 0 < ringKrullDim R) :
    (maximalIdeal R) ^ 2 < maximalIdeal R :=
  IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero h.ne.symm
