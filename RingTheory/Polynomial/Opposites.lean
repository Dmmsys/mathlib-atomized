/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Tactic.NoncommRing

/-! # Interactions between `R[X]` and `Rᵐᵒᵖ[X]`

This file contains the basic API for "pushing through" the isomorphism
`opRingEquiv : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X]`. It allows going back and forth between a polynomial ring
over a semiring and the polynomial ring over the opposite semiring. -/

@[expose] public section


open Polynomial

open MulOpposite

variable {R : Type*} [Semiring R]

noncomputable section

namespace Polynomial

/--
Definition of `opRingEquiv` / `opRingEquiv` 的定义

English:
definition opRingEquiv
  signature: (R : Type*) [Semiring R]
  body: ((toFinsuppIso R).op.trans <| AddMonoidAlgebra.opRingEquiv.trans <|
    AddMonoidAlgebra.mapDomainRingEquiv _ AddOpposite.opAddEquiv.symm).trans (toFinsuppIso _).symm

中文:
定义 opRingEquiv
  签名: (R : 类型) [半环 R]
  定义体: ((toFinsuppIso R).op.trans <| AddMonoidAlgebra.opRingEquiv.trans <|
    AddMonoidAlgebra.mapDomainRingEquiv _ AddOpposite.opAddEquiv.symm).trans (toFinsuppIso _).symm

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mapDomainRingEquiv, AddMonoidAlgebra.opRingEquiv.trans, AddOpposite, AddOpposite.opAddEquiv.symm, mapDomainRingEquiv, op.trans, opAddEquiv, opRingEquiv, toFinsuppIso
-/
def opRingEquiv (R : Type*) [Semiring R] : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X] :=
  ((toFinsuppIso R).op.trans <| AddMonoidAlgebra.opRingEquiv.trans <|
    AddMonoidAlgebra.mapDomainRingEquiv _ AddOpposite.opAddEquiv.symm).trans (toFinsuppIso _).symm

/-! Lemmas to get started, using `opRingEquiv R` on the various expressions of
`Finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`. -/


set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `opRingEquiv_op_monomial` / 定理 `opRingEquiv_op_monomial`

English:
theorem opRingEquiv_op_monomial
  given: (n : Nat) (r : R)
  proof: by
  ext; simp [opRingEquiv, ← ofFinsupp_single]

@[simp]

中文:
定理 opRingEquiv_op_monomial
  条件: (n : 自然数) (r : R)
  证明: by
  ext; simp [opRingEquiv, ← ofFinsupp_single]

@[simp]

Depends on / 依赖: ofFinsupp_single, opRingEquiv
-/
theorem opRingEquiv_op_monomial (n : Nat) (r : R) :
    opRingEquiv R (op (monomial n r : R[X])) = monomial n (op r) := by
  ext; simp [opRingEquiv, ← ofFinsupp_single]

@[simp]
/--
theorem `opRingEquiv_op_C` / 定理 `opRingEquiv_op_C`

English:
theorem opRingEquiv_op_C
  given: (a : R)
  statement: opRingEquiv R (op (C a)) = C (op a)
  proof: opRingEquiv_op_monomial 0 a

@[simp]

中文:
定理 opRingEquiv_op_C
  条件: (a : R)
  结论: opRingEquiv R (op (C a)) = C (op a)
  证明: opRingEquiv_op_monomial 0 a

@[simp]

Depends on / 依赖: opRingEquiv_op_monomial
-/
theorem opRingEquiv_op_C (a : R) : opRingEquiv R (op (C a)) = C (op a) :=
  opRingEquiv_op_monomial 0 a

@[simp]
/--
theorem `opRingEquiv_op_X` / 定理 `opRingEquiv_op_X`

English:
theorem opRingEquiv_op_X
  statement: opRingEquiv R (op (X : R[X])) = X
  proof: opRingEquiv_op_monomial 1 1

中文:
定理 opRingEquiv_op_X
  结论: opRingEquiv R (op (X : R[X])) = X
  证明: opRingEquiv_op_monomial 1 1

Depends on / 依赖: opRingEquiv_op_monomial
-/
theorem opRingEquiv_op_X : opRingEquiv R (op (X : R[X])) = X :=
  opRingEquiv_op_monomial 1 1

/--
theorem `opRingEquiv_op_C_mul_X_pow` / 定理 `opRingEquiv_op_C_mul_X_pow`

English:
theorem opRingEquiv_op_C_mul_X_pow
  given: (r : R) (n : Nat)
  proof: by
  simp only [X_pow_mul, op_mul, op_pow, map_mul, map_pow, opRingEquiv_op_X, opRingEquiv_op_C]

中文:
定理 opRingEquiv_op_C_mul_X_pow
  条件: (r : R) (n : 自然数)
  证明: by
  simp only [X_pow_mul, op_mul, op_pow, map_mul, map_pow, opRingEquiv_op_X, opRingEquiv_op_C]

Depends on / 依赖: X_pow_mul, map_mul, map_pow, opRingEquiv_op_C, opRingEquiv_op_X, op_mul, op_pow
-/
theorem opRingEquiv_op_C_mul_X_pow (r : R) (n : Nat) :
    opRingEquiv R (op (C r * X ^ n : R[X])) = C (op r) * X ^ n := by
  simp only [X_pow_mul, op_mul, op_pow, map_mul, map_pow, opRingEquiv_op_X, opRingEquiv_op_C]

/-! Lemmas to get started, using `(opRingEquiv R).symm` on the various expressions of
`Finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`. -/


@[simp]
/--
theorem `opRingEquiv_symm_monomial` / 定理 `opRingEquiv_symm_monomial`

English:
theorem opRingEquiv_symm_monomial
  given: (n : Nat) (r : Rᵐᵒᵖ)
  proof: (opRingEquiv R).injective (by simp)

@[simp]

中文:
定理 opRingEquiv_symm_monomial
  条件: (n : 自然数) (r : Rᵐᵒᵖ)
  证明: (opRingEquiv R).injective (by simp)

@[simp]

Depends on / 依赖: injective, opRingEquiv
-/
theorem opRingEquiv_symm_monomial (n : Nat) (r : Rᵐᵒᵖ) :
    (opRingEquiv R).symm (monomial n r) = op (monomial n (unop r)) :=
  (opRingEquiv R).injective (by simp)

@[simp]
/--
theorem `opRingEquiv_symm_C` / 定理 `opRingEquiv_symm_C`

English:
theorem opRingEquiv_symm_C
  given: (a : Rᵐᵒᵖ)
  statement: (opRingEquiv R).symm (C a) = op (C (unop a))
  proof: opRingEquiv_symm_monomial 0 a

@[simp]

中文:
定理 opRingEquiv_symm_C
  条件: (a : Rᵐᵒᵖ)
  结论: (opRingEquiv R).symm (C a) = op (C (unop a))
  证明: opRingEquiv_symm_monomial 0 a

@[simp]

Depends on / 依赖: opRingEquiv_symm_monomial
-/
theorem opRingEquiv_symm_C (a : Rᵐᵒᵖ) : (opRingEquiv R).symm (C a) = op (C (unop a)) :=
  opRingEquiv_symm_monomial 0 a

@[simp]
/--
theorem `opRingEquiv_symm_X` / 定理 `opRingEquiv_symm_X`

English:
theorem opRingEquiv_symm_X
  statement: (opRingEquiv R).symm (X : Rᵐᵒᵖ[X]) = op X
  proof: opRingEquiv_symm_monomial 1 1

中文:
定理 opRingEquiv_symm_X
  结论: (opRingEquiv R).symm (X : Rᵐᵒᵖ[X]) = op X
  证明: opRingEquiv_symm_monomial 1 1

Depends on / 依赖: opRingEquiv_symm_monomial
-/
theorem opRingEquiv_symm_X : (opRingEquiv R).symm (X : Rᵐᵒᵖ[X]) = op X :=
  opRingEquiv_symm_monomial 1 1

/--
theorem `opRingEquiv_symm_C_mul_X_pow` / 定理 `opRingEquiv_symm_C_mul_X_pow`

English:
theorem opRingEquiv_symm_C_mul_X_pow
  given: (r : Rᵐᵒᵖ) (n : Nat)
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [opRingEquiv_symm_monomial]; rw [C_mul_X_pow_eq_monomial]

中文:
定理 opRingEquiv_symm_C_mul_X_pow
  条件: (r : Rᵐᵒᵖ) (n : 自然数)
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [opRingEquiv_symm_monomial]; rw [C_mul_X_pow_eq_monomial]

Depends on / 依赖: C_mul_X_pow_eq_monomial, opRingEquiv_symm_monomial
-/
theorem opRingEquiv_symm_C_mul_X_pow (r : Rᵐᵒᵖ) (n : Nat) :
    (opRingEquiv R).symm (C r * X ^ n : Rᵐᵒᵖ[X]) = op (C (unop r) * X ^ n) := by
  rw [C_mul_X_pow_eq_monomial]; rw [opRingEquiv_symm_monomial]; rw [C_mul_X_pow_eq_monomial]

/-! Lemmas about more global properties of polynomials and opposites. -/

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `coeff_opRingEquiv` / 定理 `coeff_opRingEquiv`

English:
theorem coeff_opRingEquiv
  given: (p : R[X]ᵐᵒᵖ) (n : Nat)
  proof: by simp [opRingEquiv, coeff]

@[simp]

中文:
定理 coeff_opRingEquiv
  条件: (p : R[X]ᵐᵒᵖ) (n : 自然数)
  证明: by simp [opRingEquiv, coeff]

@[simp]

Depends on / 依赖: opRingEquiv
-/
theorem coeff_opRingEquiv (p : R[X]ᵐᵒᵖ) (n : Nat) :
    (opRingEquiv R p).coeff n = op ((unop p).coeff n) := by simp [opRingEquiv, coeff]

@[simp]
/--
theorem `support_opRingEquiv` / 定理 `support_opRingEquiv`

English:
theorem support_opRingEquiv
  given: (p : R[X]ᵐᵒᵖ)
  statement: (opRingEquiv R p).support = (unop p).support
  proof: by
  ext; simp

@[simp]

中文:
定理 support_opRingEquiv
  条件: (p : R[X]ᵐᵒᵖ)
  结论: (opRingEquiv R p).support = (unop p).support
  证明: by
  ext; simp

@[simp]
-/
theorem support_opRingEquiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).support = (unop p).support := by
  ext; simp

@[simp]
/--
theorem `natDegree_opRingEquiv` / 定理 `natDegree_opRingEquiv`

English:
theorem natDegree_opRingEquiv
  given: (p : R[X]ᵐᵒᵖ)
  statement: (opRingEquiv R p).natDegree = (unop p).natDegree
  proof: by
  by_cases p0 : p = 0
  · simp only [p0, map_zero, natDegree_zero, unop_zero]
  · simp only [p0, natDegree_eq_support_max', Ne, EmbeddingLike.map_eq_zero_iff, not_false_iff,
      support_opRingEquiv, unop_eq_zero_iff]

@[simp]

中文:
定理 natDegree_opRingEquiv
  条件: (p : R[X]ᵐᵒᵖ)
  结论: (opRingEquiv R p).natDegree = (unop p).natDegree
  证明: by
  by_cases p0 : p = 0
  · simp only [p0, map_zero, natDegree_zero, unop_zero]
  · simp only [p0, natDegree_eq_support_max', Ne, EmbeddingLike.map_eq_zero_iff, not_false_iff,
      support_opRingEquiv, unop_eq_zero_iff]

@[simp]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.map_eq_zero_iff, map_eq_zero_iff, map_zero, natDegree_eq_support_max, natDegree_zero, not_false_iff, support_opRingEquiv, unop_eq_zero_iff, unop_zero
-/
theorem natDegree_opRingEquiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).natDegree = (unop p).natDegree := by
  by_cases p0 : p = 0
  · simp only [p0, map_zero, natDegree_zero, unop_zero]
  · simp only [p0, natDegree_eq_support_max', Ne, EmbeddingLike.map_eq_zero_iff, not_false_iff,
      support_opRingEquiv, unop_eq_zero_iff]

@[simp]
/--
theorem `leadingCoeff_opRingEquiv` / 定理 `leadingCoeff_opRingEquiv`

English:
theorem leadingCoeff_opRingEquiv
  given: (p : R[X]ᵐᵒᵖ)
  proof: by
  rw [leadingCoeff]; rw [coeff_opRingEquiv]; rw [natDegree_opRingEquiv]; rw [leadingCoeff]

中文:
定理 leadingCoeff_opRingEquiv
  条件: (p : R[X]ᵐᵒᵖ)
  证明: by
  rw [leadingCoeff]; rw [coeff_opRingEquiv]; rw [natDegree_opRingEquiv]; rw [leadingCoeff]

Depends on / 依赖: coeff_opRingEquiv, leadingCoeff, natDegree_opRingEquiv
-/
theorem leadingCoeff_opRingEquiv (p : R[X]ᵐᵒᵖ) :
    (opRingEquiv R p).leadingCoeff = op (unop p).leadingCoeff := by
  rw [leadingCoeff]; rw [coeff_opRingEquiv]; rw [natDegree_opRingEquiv]; rw [leadingCoeff]

/--
theorem `isLeftCancelMulZero_iff` / 定理 `isLeftCancelMulZero_iff`

English:
theorem isLeftCancelMulZero_iff
  proof: .intro (C_injective.isLeftCancelMulZero _ C_0 fun _ _ => C_mul)
    have : IsLeftCancelAdd R := .mk fun a b c eq => by
      nontriviality R
      let trinomial (r : R) : R[X] := a • X ^ 2 + r • X + C a
      have ht r : (X + C 1) * trinomial r = a • X ^ 3 + (a + r) • X ^ 2 + (a + r) • X + C a := by
        simp only [trinomial, mul_add, add_mul, ← C_mul', C_1, one_mul, ← mul_assoc, X_mul_C, C_add]
        noncomm_ring
simpa [trinomial] using congr_arg (coeff · 1)
h.1 (a₁ := trinomial b) (a₂ := trinomial c) (X_add_C_ne_zero 1) by simp_rw [ht, eq]
    AddCommMagma.IsLeftCancelAdd.toIsCancelAdd R
  mpr := fun ⟨_, _⟩ => inferInstance

中文:
定理 isLeftCancelMulZero_iff
  证明: .intro (C_injective.isLeftCancelMulZero _ C_0 fun _ _ => C_mul)
    have : IsLeftCancelAdd R := .mk fun a b c eq => by
      nontriviality R
      let trinomial (r : R) : R[X] := a • X ^ 2 + r • X + C a
      have ht r : (X + C 1) * trinomial r = a • X ^ 3 + (a + r) • X ^ 2 + (a + r) • X + C a := by
        simp only [trinomial, mul_add, add_mul, ← C_mul', C_1, one_mul, ← mul_assoc, X_mul_C, C_add]
        noncomm_ring
simpa [trinomial] using congr_arg (coeff · 1)
h.1 (a₁ := trinomial b) (a₂ := trinomial c) (X_add_C_ne_zero 1) by simp_rw [ht, eq]
    AddCommMagma.IsLeftCancelAdd.toIsCancelAdd R
  mpr := fun ⟨_, _⟩ => inferInstance

Depends on / 依赖: C_injective, C_injective.isLeftCancelMulZero, C_mul, isLeftCancelMulZero
-/
theorem isLeftCancelMulZero_iff :
    IsLeftCancelMulZero R[X] ↔ IsLeftCancelMulZero R ∧ IsCancelAdd R where
mp h := .intro (C_injective.isLeftCancelMulZero _ C_0 fun _ _ => C_mul)
    have : IsLeftCancelAdd R := .mk fun a b c eq => by
      nontriviality R
      let trinomial (r : R) : R[X] := a • X ^ 2 + r • X + C a
      have ht r : (X + C 1) * trinomial r = a • X ^ 3 + (a + r) • X ^ 2 + (a + r) • X + C a := by
        simp only [trinomial, mul_add, add_mul, ← C_mul', C_1, one_mul, ← mul_assoc, X_mul_C, C_add]
        noncomm_ring
simpa [trinomial] using congr_arg (coeff · 1)
h.1 (a₁ := trinomial b) (a₂ := trinomial c) (X_add_C_ne_zero 1) by simp_rw [ht, eq]
    AddCommMagma.IsLeftCancelAdd.toIsCancelAdd R
  mpr := fun ⟨_, _⟩ => inferInstance

/--
theorem `isRightCancelMulZero_iff` / 定理 `isRightCancelMulZero_iff`

English:
theorem isRightCancelMulZero_iff
  proof: by
  rw [← MulOpposite.isLeftCancelMulZero_iff]; rw [(opRingEquiv R).isLeftCancelMulZero_iff]; rw [isLeftCancelMulZero_iff]; rw [MulOpposite.isLeftCancelMulZero_iff]; rw [MulOpposite.isCancelAdd_iff]

中文:
定理 isRightCancelMulZero_iff
  证明: by
  rw [← MulOpposite.isLeftCancelMulZero_iff]; rw [(opRingEquiv R).isLeftCancelMulZero_iff]; rw [isLeftCancelMulZero_iff]; rw [MulOpposite.isLeftCancelMulZero_iff]; rw [MulOpposite.isCancelAdd_iff]

Depends on / 依赖: MulOpposite, MulOpposite.isCancelAdd_iff, MulOpposite.isLeftCancelMulZero_iff, isCancelAdd_iff, isLeftCancelMulZero_iff, opRingEquiv
-/
theorem isRightCancelMulZero_iff :
    IsRightCancelMulZero R[X] ↔ IsRightCancelMulZero R ∧ IsCancelAdd R := by
  rw [← MulOpposite.isLeftCancelMulZero_iff]; rw [(opRingEquiv R).isLeftCancelMulZero_iff]; rw [isLeftCancelMulZero_iff]; rw [MulOpposite.isLeftCancelMulZero_iff]; rw [MulOpposite.isCancelAdd_iff]

/--
theorem `isCancelMulZero_iff` / 定理 `isCancelMulZero_iff`

English:
theorem isCancelMulZero_iff
  proof: by
  simp_rw [isCancelMulZero_iff, isLeftCancelMulZero_iff, isRightCancelMulZero_iff]
  rw [and_and_and_comm]; rw [and_self]

中文:
定理 isCancelMulZero_iff
  证明: by
  simp_rw [isCancelMulZero_iff, isLeftCancelMulZero_iff, isRightCancelMulZero_iff]
  rw [and_and_and_comm]; rw [and_self]

Depends on / 依赖: continuousNeg, isInducing, opHomeomorph, opHomeomorph.symm.isInducing.continuousNeg
-/
protected theorem isCancelMulZero_iff :
    IsCancelMulZero R[X] ↔ IsCancelMulZero R ∧ IsCancelAdd R := by
  simp_rw [isCancelMulZero_iff, isLeftCancelMulZero_iff, isRightCancelMulZero_iff]
  rw [and_and_and_comm]; rw [and_self]

/--
theorem `isDomain_iff` / 定理 `isDomain_iff`

English:
theorem isDomain_iff
  statement: IsDomain R[X] ↔ IsDomain R ∧ IsCancelAdd R
  proof: by
  simp_rw [isDomain_iff_cancelMulZero_and_nontrivial, nontrivial_iff,
    Polynomial.isCancelMulZero_iff, and_right_comm]

中文:
定理 isDomain_iff
  结论: 是整环 R[X] ↔ 是整环 R ∧ 是消去加法 R
  证明: by
  simp_rw [isDomain_iff_cancelMulZero_and_nontrivial, nontrivial_iff,
    Polynomial.isCancelMulZero_iff, and_right_comm]

Depends on / 依赖: Polynomial, Polynomial.isCancelMulZero_iff, and_right_comm, isCancelMulZero_iff, isDomain_iff_cancelMulZero_and_nontrivial, nontrivial_iff, simp_rw
-/
theorem isDomain_iff : IsDomain R[X] ↔ IsDomain R ∧ IsCancelAdd R := by
  simp_rw [isDomain_iff_cancelMulZero_and_nontrivial, nontrivial_iff,
    Polynomial.isCancelMulZero_iff, and_right_comm]

end Polynomial
