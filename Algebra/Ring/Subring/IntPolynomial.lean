/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomials over subrings.

Given a field `K` with a subring `R`, in this file we construct a map from polynomials in `K[X]`
with coefficients in `R` to `R[X]`. We provide several lemmas to deal with
coefficients, degree, and evaluation of `Polynomial.int`.
This is useful when dealing with integral elements in an extension of fields.

## Main Definitions
* `Polynomial.int` : given a polynomial `P` in `K[X]` whose coefficients all belong to a subring `R`
  of the field `K`, `P.int R` is the corresponding polynomial in `R[X]`.
-/

@[expose] public section

variable {K : Type*} [Field K] (R : Subring K)

open scoped Polynomial

/-- Given a polynomial in `K[X]` such that all coefficients belong to the subring `R`,
  `Polynomial.int` is the corresponding polynomial in `R[X]`. -/
/-
**Polynomial.int** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Polynomial.int (P : K[X]) (hP : forall n : Nat, P.coeff n in R) : R[X] whe
re toFinsupp.coeff.toFun n
参数：P : K[X]；hP : forall n : Nat, P.coeff n in R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a polynomial in `K[X]` such that all coefficients belong to the subring `R
`,
  `Polynomial.int` is the corresponding polynomial in `R[X]`.
-/
def Polynomial.int (P : K[X]) (hP : ∀ n : ℕ, P.coeff n ∈ R) : R[X] where
  toFinsupp.coeff.toFun n := ⟨P.coeff n, hP n⟩
  toFinsupp.coeff.support := P.support
  toFinsupp.coeff.mem_support_toFun n := by rw [ne_eq, ← Subring.coe_eq_zero_iff, mem_support_iff]

namespace Polynomial

variable (P : K[X]) (hP : ∀ n : ℕ, P.coeff n ∈ R)

@[simp]
/-
**Polynomial.int_coeff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：int_coeff_eq (n : Nat) : ↑((P.int R hP).coeff n) = P.coeff n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem int_coeff_eq (n : ℕ) : ↑((P.int R hP).coeff n) = P.coeff n := rfl

@[simp]
/-
**Polynomial.int_leadingCoeff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：int_leadingCoeff_eq : ↑(P.int R hP).leadingCoeff = P.leadingCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem int_leadingCoeff_eq : ↑(P.int R hP).leadingCoeff = P.leadingCoeff := rfl

@[simp]
/-
**Polynomial.int_monic_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：int_monic_iff : (P.int R hP).Monic ↔ P.Monic
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.int_leadingCoeff_eq`：int_leadingCoeff_eq : ↑(P.int R hP).lead
ingCoeff = P.leadingCoeff
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `OneMemClass.coe_eq_one`：coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem int_monic_iff : (P.int R hP).Monic ↔ P.Monic := by
  rw [Monic, Monic, ← int_leadingCoeff_eq, OneMemClass.coe_eq_one]

@[simp]
/-
**Polynomial.int_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：int_natDegree : (P.int R hP).natDegree = P.natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem int_natDegree : (P.int R hP).natDegree = P.natDegree := rfl

variable {L : Type*} [Field L] [Algebra K L]

@[simp]
/-
**Polynomial.int_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem int_eval₂_eq (x : L) :
    eval₂ (algebraMap R L) x (P.int R hP) = aeval x P := by
  rw [aeval_eq_sum_range, eval₂_eq_sum_range]
  exact Finset.sum_congr rfl (fun n _ => by rw [Algebra.smul_def]; rfl)

end Polynomial

