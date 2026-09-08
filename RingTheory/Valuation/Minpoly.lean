/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Minimal polynomials.

We prove some results about valuations of zero coefficients of minimal polynomials.

Let `K` be a field with a valuation `v` and let `L` be a field extension of `K`.

## Main statements

* `coeff_zero_minpoly` : for `x ∈ K` the valuation of the zeroth coefficient of the minimal
  polynomial of `algebraMap K L x` over `K` is equal to the valuation of `x`.
* `pow_coeff_zero_ne_zero_of_unit` : for any unit `x : Lˣ`, we prove that a certain power of the
  valuation of zeroth coefficient of the minimal polynomial of `x` over `K` is nonzero. This lemma
  is helpful for defining the valuation on `L` inducing `v`.
-/

public section

open Module minpoly Polynomial

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀) (L : Type*) [Field L] [Algebra K L]

namespace Valuation

/-- For `x ∈ K` the valuation of the zeroth coefficient of the minimal polynomial
of `algebraMap K L x` over `K` is equal to the valuation of `x`. -/
@[simp]
/-
**Valuation.coeff_zero_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：coeff_zero_minpoly (x : K) : v ((minpoly K (algebraMap K L x)).coeff 0) = 
v x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.eq_X_sub_C`：eq_X_sub_C (a : A) : minpoly A (algebraMap A B a) = 
X - C a
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Valuation.map_neg`：map_neg (x : R) : v (-x) = v x

--- 原说明 ---
For `x ∈ K` the valuation of the zeroth coefficient of the minimal polynomial
of `algebraMap K L x` over `K` is equal to the valuation of `x`.
-/
theorem coeff_zero_minpoly (x : K) : v ((minpoly K (algebraMap K L x)).coeff 0) = v x := by
  rw [minpoly.eq_X_sub_C, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, Valuation.map_neg]

variable {L}

/-- For any unit `x : Lˣ`, we prove that a certain power of the valuation of zeroth coefficient of
the minimal polynomial of `x` over `K` is nonzero. This lemma is helpful for defining the valuation
on `L` inducing `v`. -/
/-
**Valuation.pow_coeff_zero_ne_zero_of_unit** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`
。
形式化陈述：pow_coeff_zero_ne_zero_of_unit [FiniteDimensional K L] (x : L) (hx : IsUni
t x) : v ((minpoly K x).coeff 0) ^ (finrank K L / (minpoly K x).natDegree) != (0
 : Γ₀)
参数：x : L；hx : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `minpoly.natDegree_le`：natDegree_le [Module.Free A B] : (minpoly A x).nat
Degree <= Module.finrank A B
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `minpoly.natDegree_pos`：natDegree_pos [Nontrivial B] (hx : IsIntegral A x
) : 0 < natDegree (minpoly A x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `pow_eq_zero_iff`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} {
n : ℕ} [IsReduced M₀], n ≠ 0 → (a ^ n = 0 ↔ a = 0)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Valuation.zero_iff`：zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K
} : v x = 0 ↔ x = 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `minpoly.coeff_zero_ne_zero`：coeff_zero_ne_zero (hx : IsIntegral A x) (h 
: x != 0) : coeff (minpoly A x) 0 != 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0

--- 原说明 ---
For any unit `x : Lˣ`, we prove that a certain power of the valuation of zeroth 
coefficient of
the minimal polynomial of `x` over `K` is nonzero. This lemma is helpful for def
ining the valuation
on `L` inducing `v`.
-/
theorem pow_coeff_zero_ne_zero_of_unit [FiniteDimensional K L] (x : L) (hx : IsUnit x) :
    v ((minpoly K x).coeff 0) ^ (finrank K L / (minpoly K x).natDegree) ≠ (0 : Γ₀) := by
  have h_alg : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hx₀ : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hdeg := Nat.div_pos (natDegree_le x) (natDegree_pos hx₀)
  rw [ne_eq, pow_eq_zero_iff hdeg.ne.symm, Valuation.zero_iff]
  exact coeff_zero_ne_zero hx₀ hx.ne_zero

end Valuation

