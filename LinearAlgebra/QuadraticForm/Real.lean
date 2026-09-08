/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Data.Sign.Basic
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.RCLike.Basic

/-!
# Real quadratic forms

Sylvester's law of inertia `equivalent_one_neg_one_weighted_sum_squared`:
A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0.

When the real quadratic form is nondegenerate we can take the weights to be ±1,
as in `QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared`.

-/

@[expose] public section

open Finset Module QuadraticMap SignType

namespace QuadraticForm
variable {ι : Type*} [Fintype ι]

/-- The isometry between a weighted sum of squares with weights `u` on the
(non-zero) real numbers and the weighted sum of squares with weights `sign ∘ u`. -/
/-
**QuadraticForm.isometryEquivSignWeightedSumSquares** 是 Mathlib 中的一个定义，位于命名空间 `Q
uadraticForm`。
形式化陈述：isometryEquivSignWeightedSumSquares (w : ι -> Real) : IsometryEquiv (weigh
tedSumSquares Real w) (weightedSumSquares Real (fun i => (sign (w i) : Real)))
参数：w : ι -> Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The isometry between a weighted sum of squares with weights `u` on the
(non-zero) real numbers and the weighted sum of squares with weights `sign ∘ u`.
-/
noncomputable def isometryEquivSignWeightedSumSquares (w : ι → ℝ) :
    IsometryEquiv (weightedSumSquares ℝ w)
      (weightedSumSquares ℝ (fun i ↦ (sign (w i) : ℝ))) := by
  let u i := if h : w i = 0 then (1 : ℝˣ) else Units.mk0 (w i) h
  have hu : ∀ i : ι, 1 / √|(u i : ℝ)| ≠ 0 := fun i ↦
    have : (u i : ℝ) ≠ 0 := (u i).ne_zero
    by positivity
  have hwu : ∀ i, w i / |(u i : ℝ)| = sign (w i) := fun i ↦ by
    by_cases hi : w i = 0
    · simp [hi]
    · simp only [hi, ↓reduceDIte, Units.val_mk0, u]; field_simp; simp
  convert!
    QuadraticMap.isometryEquivBasisRepr (weightedSumSquares ℝ w)
      ((Pi.basisFun ℝ ι).unitsSMul fun i => .mk0 _ (hu i))
  ext1 v
  classical
  suffices ∑ i, (w i / |(u i : ℝ)|) * v i ^ 2 = ∑ i, w i * (v i ^ 2 * |(u i : ℝ)|⁻¹) by
    simpa [basisRepr_apply, Basis.unitsSMul_apply, ← _root_.sq, mul_pow, ← hwu, Pi.single_apply]
  exact sum_congr rfl fun j _ ↦ by ring

/-- **Sylvester's law of inertia**: A nondegenerate real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1, `SignType` version. -/
/-
**QuadraticForm.equivalent_sign_ne_zero_weighted_sum_squared** 是 Mathlib 中的一个定理，
位于命名空间 `QuadraticForm`。
形式化陈述：equivalent_sign_ne_zero_weighted_sum_squared {M : Type*} [AddCommGroup M] 
[Module Real M] [FiniteDimensional Real M] (Q : QuadraticForm Real M) (hQ : (ass
ociated (R
参数：Q : QuadraticForm Real M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'`：equ
ivalent_weightedSumSquares_units_of_nondegenerate' (Q : QuadraticForm K V) (hQ :
 (associated (R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sign_ne_zero`：sign_ne_zero : sign a != 0 ↔ a != 0
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0

--- 原说明 ---
**Sylvester's law of inertia**: A nondegenerate real quadratic form is equivalen
t to a weighted
sum of squares with the weights being ±1, `SignType` version.
-/
theorem equivalent_sign_ne_zero_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) (hQ : (associated (R := ℝ) Q).SeparatingLeft) :
    ∃ w : Fin (Module.finrank ℝ M) → SignType,
      (∀ i, w i ≠ 0) ∧ Equivalent Q (weightedSumSquares ℝ fun i ↦ (w i : ℝ)) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  ⟨sign ∘ ((↑) : ℝˣ → ℝ) ∘ w, fun i => sign_ne_zero.2 (w i).ne_zero,
    ⟨hw₁.trans (isometryEquivSignWeightedSumSquares (((↑) : ℝˣ → ℝ) ∘ w))⟩⟩

/-- **Sylvester's law of inertia**: A nondegenerate real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1. -/
/-
**QuadraticForm.equivalent_one_neg_one_weighted_sum_squared** 是 Mathlib 中的一个定理，位
于命名空间 `QuadraticForm`。
形式化陈述：equivalent_one_neg_one_weighted_sum_squared {M : Type*} [AddCommGroup M] [
Module Real M] [FiniteDimensional Real M] (Q : QuadraticForm Real M) (hQ : (asso
ciated (R
参数：Q : QuadraticForm Real M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `QuadraticForm.equivalent_sign_ne_zero_weighted_sum_squared`：equivalent_s
ign_ne_zero_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module Real M] [F
initeDimensional Real M] (Q : QuadraticForm Real…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SignType.coe_neg`：coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s :
 SignType) : (↑(-s) : α) = -↑s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True

--- 原说明 ---
**Sylvester's law of inertia**: A nondegenerate real quadratic form is equivalen
t to a weighted
sum of squares with the weights being ±1.
-/
theorem equivalent_one_neg_one_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) (hQ : (associated (R := ℝ) Q).SeparatingLeft) :
    ∃ w : Fin (Module.finrank ℝ M) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧ Equivalent Q (weightedSumSquares ℝ w) :=
  let ⟨w, hw₀, hw⟩ := Q.equivalent_sign_ne_zero_weighted_sum_squared hQ
  ⟨(w ·), fun i ↦ by cases hi : w i <;> simp_all, hw⟩

/-- **Sylvester's law of inertia**: A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0, `SignType` version. -/
/-
**QuadraticForm.equivalent_signType_weighted_sum_squared** 是 Mathlib 中的一个定理，位于命名
空间 `QuadraticForm`。
形式化陈述：equivalent_signType_weighted_sum_squared {M : Type*} [AddCommGroup M] [Mod
ule Real M] [FiniteDimensional Real M] (Q : QuadraticForm Real M) : exists w : F
in (Module.finrank Real M) -> SignType, Equivalent Q (weightedSumSquares Real fu
n i => (w i : Real))
参数：Q : QuadraticForm Real M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `QuadraticForm.equivalent_weightedSumSquares`：equivalent_weightedSumSquar
es (Q : QuadraticForm K V) : exists w : Fin (Module.finrank K V) -> K, Equivalen
t Q (weightedSumSquares K w)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
**Sylvester's law of inertia**: A real quadratic form is equivalent to a weighte
d
sum of squares with the weights being ±1 or 0, `SignType` version.
-/
theorem equivalent_signType_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) :
    ∃ w : Fin (Module.finrank ℝ M) → SignType,
      Equivalent Q (weightedSumSquares ℝ fun i ↦ (w i : ℝ)) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares
  ⟨sign ∘ w, ⟨hw₁.trans (isometryEquivSignWeightedSumSquares w)⟩⟩

/-- **Sylvester's law of inertia**: A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0. -/
/-
**QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared** 是 Mathlib 中的一
个定理，位于命名空间 `QuadraticForm`。
形式化陈述：equivalent_one_zero_neg_one_weighted_sum_squared {M : Type*} [AddCommGroup
 M] [Module Real M] [FiniteDimensional Real M] (Q : QuadraticForm Real M) : exis
ts w : Fin (Module.finrank Real M) -> Real, (forall i, w i = -1 ∨ w i = 0 ∨ w i 
= 1) ∧ Equivalent Q (weightedSumSquares Real w)
参数：Q : QuadraticForm Real M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `QuadraticForm.equivalent_signType_weighted_sum_squared`：equivalent_signT
ype_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module Real M] [FiniteDim
ensional Real M] (Q : QuadraticForm Real M) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SignType.coe_neg`：coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s :
 SignType) : (↑(-s) : α) = -↑s
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True

--- 原说明 ---
**Sylvester's law of inertia**: A real quadratic form is equivalent to a weighte
d
sum of squares with the weights being ±1 or 0.
-/
theorem equivalent_one_zero_neg_one_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) :
    ∃ w : Fin (Module.finrank ℝ M) → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧ Equivalent Q (weightedSumSquares ℝ w) :=
  let ⟨w, hw⟩ := Q.equivalent_signType_weighted_sum_squared
  ⟨(w ·), fun i ↦ by cases h : w i <;> simp [h], hw⟩

end QuadraticForm

