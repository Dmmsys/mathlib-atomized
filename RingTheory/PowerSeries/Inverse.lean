/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.Data.ENat.Lattice

/-! # Formal power series - Inverses

If the constant coefficient of a formal (univariate) power series is invertible,
then this formal power series is invertible.
(See the discussion in `Mathlib/RingTheory/MvPowerSeries/Inverse.lean` for
the construction.)

Formal (univariate) power series over a local ring form a local ring.

Formal (univariate) power series over a field form a discrete valuation ring, and a normalization
monoid. The definition `residueFieldOfPowerSeries` provides the isomorphism between the residue
field of `k⟦X⟧` and `k`, when `k` is a field.

-/

@[expose] public section


noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}


section Ring

variable [Ring R]

/--
Definition of `inv.aux` / `inv.aux` 的定义

English:
definition inv.aux
  signature: : R -> R⟦X⟧ -> R⟦X⟧
  body: MvPowerSeries.inv.aux

中文:
定义 inv.aux
  签名: : R -> R⟦X⟧ -> R⟦X⟧
  定义体: MvPowerSeries.inv.aux
-/
protected def inv.aux : R -> R⟦X⟧ -> R⟦X⟧ :=
  MvPowerSeries.inv.aux

/--
theorem `coeff_inv_aux` / 定理 `coeff_inv_aux`

English:
theorem coeff_inv_aux
  given: (n : Nat) (a : R) (φ : R⟦X⟧)
  proof: by
  rw [coeff]; rw [inv.aux]; rw [MvPowerSeries.coeff_inv_aux]
  simp only [Finsupp.single_eq_zero]
  split_ifs; · rfl
  congr 1
  symm
  apply Finset.sum_nbij' (fun (a, b) => (single () a, single () b))
    fun (f, g) => (f (), g ())
  · aesop
  · aesop
  · aesop
  · aesop
  · rintro ⟨i, j⟩ _hij
 

中文:
定理 coeff_inv_aux
  条件: (n : 自然数) (a : R) (φ : R⟦X⟧)
  证明: by
  rw [coeff]; rw [inv.aux]; rw [MvPowerSeries.coeff_inv_aux]
  simp only [Finsupp.single_eq_zero]
  split_ifs; · rfl
  congr 1
  symm
  apply Finset.sum_nbij' (fun (a, b) => (single () a, single () b))
    fun (f, g) => (f (), g ())
  · aesop
  · aesop
  · aesop
  · aesop
  · rintro ⟨i, j⟩ _hij
 

Depends on / 依赖: Finset, Finset.sum_nbij, Finsupp, Finsupp.single_eq_same, Finsupp.single_eq_zero, H.not_ge, MvPowerSeries, MvPowerSeries.coeff_inv_aux, _hij, coeff_inv_aux, if_pos, inv.aux, le_of_lt, le_or_gt, not_ge, single, single_eq_same, single_eq_zero, split_ifs, sum_nbij
-/
theorem coeff_inv_aux (n : Nat) (a : R) (φ : R⟦X⟧) :
    coeff n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x in antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0 := by
  rw [coeff]; rw [inv.aux]; rw [MvPowerSeries.coeff_inv_aux]
  simp only [Finsupp.single_eq_zero]
  split_ifs; · rfl
  congr 1
  symm
  apply Finset.sum_nbij' (fun (a, b) => (single () a, single () b))
    fun (f, g) => (f (), g ())
  · aesop
  · aesop
  · aesop
  · aesop
  · rintro ⟨i, j⟩ _hij
    obtain H | H := le_or_gt n j
    · aesop
    rw [if_pos H]; rw [if_pos]
    · rfl
    refine ⟨?_, fun hh => H.not_ge ?_⟩
    · rintro ⟨⟩
      simpa [Finsupp.single_eq_same] using le_of_lt H
    · simpa [Finsupp.single_eq_same] using hh ()

/--
Definition of `invOfUnit` / `invOfUnit` 的定义

English:
definition invOfUnit
  signature: (φ : R⟦X⟧) (u : Rˣ)
  body: MvPowerSeries.invOfUnit φ u

中文:
定义 invOfUnit
  签名: (φ : R⟦X⟧) (u : Rˣ)
  定义体: MvPowerSeries.invOfUnit φ u

Depends on / 依赖: MvPowerSeries, MvPowerSeries.invOfUnit, invOfUnit
-/
def invOfUnit (φ : R⟦X⟧) (u : Rˣ) : R⟦X⟧ :=
  MvPowerSeries.invOfUnit φ u

/--
theorem `coeff_invOfUnit` / 定理 `coeff_invOfUnit`

English:
theorem coeff_invOfUnit
  given: (n : Nat) (φ : R⟦X⟧) (u : Rˣ)
  proof: coeff_inv_aux n (↑u⁻¹ : R) φ

@[simp]

中文:
定理 coeff_invOfUnit
  条件: (n : 自然数) (φ : R⟦X⟧) (u : Rˣ)
  证明: coeff_inv_aux n (↑u⁻¹ : R) φ

@[simp]

Depends on / 依赖: coeff_inv_aux
-/
theorem coeff_invOfUnit (n : Nat) (φ : R⟦X⟧) (u : Rˣ) :
    coeff n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x in antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 (invOfUnit φ u) else 0 :=
  coeff_inv_aux n (↑u⁻¹ : R) φ

@[simp]
/--
theorem `constantCoeff_invOfUnit` / 定理 `constantCoeff_invOfUnit`

English:
theorem constantCoeff_invOfUnit
  given: (φ : R⟦X⟧) (u : Rˣ)
  proof: by
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_invOfUnit]; rw [if_pos rfl]

@[simp]

中文:
定理 constantCoeff_invOfUnit
  条件: (φ : R⟦X⟧) (u : Rˣ)
  证明: by
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_invOfUnit]; rw [if_pos rfl]

@[simp]

Depends on / 依赖: coeff_invOfUnit, coeff_zero_eq_constantCoeff_apply, if_pos
-/
theorem constantCoeff_invOfUnit (φ : R⟦X⟧) (u : Rˣ) :
    constantCoeff (invOfUnit φ u) = ↑u⁻¹ := by
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_invOfUnit]; rw [if_pos rfl]

@[simp]
/--
theorem `mul_invOfUnit` / 定理 `mul_invOfUnit`

English:
theorem mul_invOfUnit
  given: (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff φ = u)
  proof: MvPowerSeries.mul_invOfUnit φ u h

@[simp]

中文:
定理 mul_invOfUnit
  条件: (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff φ = u)
  证明: MvPowerSeries.mul_invOfUnit φ u h

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.mul_invOfUnit, mul_invOfUnit
-/
theorem mul_invOfUnit (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff φ = u) :
    φ * invOfUnit φ u = 1 :=
MvPowerSeries.mul_invOfUnit φ u h

@[simp]
/--
theorem `invOfUnit_mul` / 定理 `invOfUnit_mul`

English:
theorem invOfUnit_mul
  given: (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff φ = u)
  proof: MvPowerSeries.invOfUnit_mul φ u h

中文:
定理 invOfUnit_mul
  条件: (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff φ = u)
  证明: MvPowerSeries.invOfUnit_mul φ u h

Depends on / 依赖: MvPowerSeries, MvPowerSeries.invOfUnit_mul, invOfUnit_mul
-/
theorem invOfUnit_mul (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff φ = u) :
    invOfUnit φ u * φ = 1 :=
  MvPowerSeries.invOfUnit_mul φ u h

/--
theorem `isUnit_iff_constantCoeff` / 定理 `isUnit_iff_constantCoeff`

English:
theorem isUnit_iff_constantCoeff
  given: {φ : R⟦X⟧}
  proof: MvPowerSeries.isUnit_iff_constantCoeff

中文:
定理 isUnit_iff_constantCoeff
  条件: {φ : R⟦X⟧}
  证明: MvPowerSeries.isUnit_iff_constantCoeff

Depends on / 依赖: MvPowerSeries, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_constantCoeff
-/
theorem isUnit_iff_constantCoeff {φ : R⟦X⟧} :
    IsUnit φ ↔ IsUnit (constantCoeff φ) :=
  MvPowerSeries.isUnit_iff_constantCoeff

/--
theorem `sub_const_eq_shift_mul_X` / 定理 `sub_const_eq_shift_mul_X`

English:
theorem sub_const_eq_shift_mul_X
  given: (φ : R⟦X⟧)
  proof: sub_eq_iff_eq_add.mpr (eq_shift_mul_X_add_const φ)

中文:
定理 sub_const_eq_shift_mul_X
  条件: (φ : R⟦X⟧)
  证明: sub_eq_iff_eq_add.mpr (eq_shift_mul_X_add_const φ)

Depends on / 依赖: eq_shift_mul_X_add_const, sub_eq_iff_eq_add, sub_eq_iff_eq_add.mpr
-/
theorem sub_const_eq_shift_mul_X (φ : R⟦X⟧) :
    φ - C (constantCoeff φ) = (mk fun p => coeff (p + 1) φ) * X :=
  sub_eq_iff_eq_add.mpr (eq_shift_mul_X_add_const φ)

/--
theorem `sub_const_eq_X_mul_shift` / 定理 `sub_const_eq_X_mul_shift`

English:
theorem sub_const_eq_X_mul_shift
  given: (φ : R⟦X⟧)
  proof: sub_eq_iff_eq_add.mpr (eq_X_mul_shift_add_const φ)

中文:
定理 sub_const_eq_X_mul_shift
  条件: (φ : R⟦X⟧)
  证明: sub_eq_iff_eq_add.mpr (eq_X_mul_shift_add_const φ)

Depends on / 依赖: eq_X_mul_shift_add_const, sub_eq_iff_eq_add, sub_eq_iff_eq_add.mpr
-/
theorem sub_const_eq_X_mul_shift (φ : R⟦X⟧) :
    φ - C (constantCoeff φ) = X * mk fun p => coeff (p + 1) φ :=
  sub_eq_iff_eq_add.mpr (eq_X_mul_shift_add_const φ)

end Ring

section Field

variable {k : Type*} [Field k]

/--
Definition of `inv` / `inv` 的定义

English:
abbreviation inv
  signature: : k⟦X⟧ -> k⟦X⟧
  body: MvPowerSeries.inv

中文:
缩写 inv
  签名: : k⟦X⟧ -> k⟦X⟧
  定义体: MvPowerSeries.inv
-/
protected abbrev inv : k⟦X⟧ -> k⟦X⟧ :=
  MvPowerSeries.inv

/--
theorem `inv_eq_inv_aux` / 定理 `inv_eq_inv_aux`

English:
theorem inv_eq_inv_aux
  given: (φ : k⟦X⟧)
  statement: φ⁻¹ = inv.aux (constantCoeff φ)⁻¹ φ
  proof: rfl

中文:
定理 inv_eq_inv_aux
  条件: (φ : k⟦X⟧)
  结论: φ⁻¹ = inv.aux (constantCoeff φ)⁻¹ φ
  证明: rfl
-/
theorem inv_eq_inv_aux (φ : k⟦X⟧) : φ⁻¹ = inv.aux (constantCoeff φ)⁻¹ φ :=
  rfl

/--
theorem `coeff_inv` / 定理 `coeff_inv`

English:
theorem coeff_inv
  given: (n) (φ : k⟦X⟧)
  proof: by
  rw [inv_eq_inv_aux]; rw [coeff_inv_aux n (constantCoeff φ)⁻¹ φ]

@[simp]

中文:
定理 coeff_inv
  条件: (n) (φ : k⟦X⟧)
  证明: by
  rw [inv_eq_inv_aux]; rw [coeff_inv_aux n (constantCoeff φ)⁻¹ φ]

@[simp]

Depends on / 依赖: coeff_inv_aux, constantCoeff, inv_eq_inv_aux
-/
theorem coeff_inv (n) (φ : k⟦X⟧) :
    coeff n φ⁻¹ =
      if n = 0 then (constantCoeff φ)⁻¹
      else
        -(constantCoeff φ)⁻¹ *
          ∑ x in antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 φ⁻¹ else 0 := by
  rw [inv_eq_inv_aux]; rw [coeff_inv_aux n (constantCoeff φ)⁻¹ φ]

@[simp]
/--
theorem `constantCoeff_inv` / 定理 `constantCoeff_inv`

English:
theorem constantCoeff_inv
  given: (φ : k⟦X⟧)
  statement: constantCoeff φ⁻¹ = (constantCoeff φ)⁻¹
  proof: MvPowerSeries.constantCoeff_inv φ

中文:
定理 constantCoeff_inv
  条件: (φ : k⟦X⟧)
  结论: constantCoeff φ⁻¹ = (constantCoeff φ)⁻¹
  证明: MvPowerSeries.constantCoeff_inv φ

Depends on / 依赖: MvPowerSeries, MvPowerSeries.constantCoeff_inv, constantCoeff_inv
-/
theorem constantCoeff_inv (φ : k⟦X⟧) : constantCoeff φ⁻¹ = (constantCoeff φ)⁻¹ :=
  MvPowerSeries.constantCoeff_inv φ

/--
theorem `inv_eq_zero` / 定理 `inv_eq_zero`

English:
theorem inv_eq_zero
  given: {φ : k⟦X⟧}
  statement: φ⁻¹ = 0 ↔ constantCoeff φ = 0
  proof: MvPowerSeries.inv_eq_zero

中文:
定理 inv_eq_zero
  条件: {φ : k⟦X⟧}
  结论: φ⁻¹ = 0 ↔ constantCoeff φ = 0
  证明: MvPowerSeries.inv_eq_zero

Depends on / 依赖: MvPowerSeries, MvPowerSeries.inv_eq_zero, inv_eq_zero
-/
theorem inv_eq_zero {φ : k⟦X⟧} : φ⁻¹ = 0 ↔ constantCoeff φ = 0 :=
  MvPowerSeries.inv_eq_zero

/--
theorem `zero_inv` / 定理 `zero_inv`

English:
theorem zero_inv
  statement: (0 : k⟦X⟧)⁻¹ = 0
  proof: MvPowerSeries.zero_inv

@[simp]

中文:
定理 zero_inv
  结论: (0 : k⟦X⟧)⁻¹ = 0
  证明: MvPowerSeries.zero_inv

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.zero_inv, zero_inv
-/
theorem zero_inv : (0 : k⟦X⟧)⁻¹ = 0 :=
  MvPowerSeries.zero_inv

@[simp]
/--
theorem `invOfUnit_eq` / 定理 `invOfUnit_eq`

English:
theorem invOfUnit_eq
  given: (φ : k⟦X⟧) (h : constantCoeff φ != 0)
  proof: rfl

@[simp]

中文:
定理 invOfUnit_eq
  条件: (φ : k⟦X⟧) (h : constantCoeff φ != 0)
  证明: rfl

@[simp]
-/
theorem invOfUnit_eq (φ : k⟦X⟧) (h : constantCoeff φ != 0) :
    invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  rfl

@[simp]
/--
theorem `invOfUnit_eq'` / 定理 `invOfUnit_eq'`

English:
theorem invOfUnit_eq'
  given: (φ : k⟦X⟧) (u : Units k) (h : constantCoeff φ = u)
  proof: MvPowerSeries.invOfUnit_eq' φ _ h

@[simp]

中文:
定理 invOfUnit_eq'
  条件: (φ : k⟦X⟧) (u : 单位群 k) (h : constantCoeff φ = u)
  证明: MvPowerSeries.invOfUnit_eq' φ _ h

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.invOfUnit_eq, invOfUnit_eq
-/
theorem invOfUnit_eq' (φ : k⟦X⟧) (u : Units k) (h : constantCoeff φ = u) :
    invOfUnit φ u = φ⁻¹ :=
  MvPowerSeries.invOfUnit_eq' φ _ h

@[simp]
/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  given: (φ : k⟦X⟧) (h : constantCoeff φ != 0)
  statement: φ * φ⁻¹ = 1
  proof: MvPowerSeries.mul_inv_cancel φ h

@[simp]

中文:
定理 mul_inv_cancel
  条件: (φ : k⟦X⟧) (h : constantCoeff φ != 0)
  结论: φ * φ⁻¹ = 1
  证明: MvPowerSeries.mul_inv_cancel φ h

@[simp]
-/
protected theorem mul_inv_cancel (φ : k⟦X⟧) (h : constantCoeff φ != 0) : φ * φ⁻¹ = 1 :=
  MvPowerSeries.mul_inv_cancel φ h

@[simp]
/--
theorem `inv_mul_cancel` / 定理 `inv_mul_cancel`

English:
theorem inv_mul_cancel
  given: (φ : k⟦X⟧) (h : constantCoeff φ != 0)
  statement: φ⁻¹ * φ = 1
  proof: MvPowerSeries.inv_mul_cancel φ h

中文:
定理 inv_mul_cancel
  条件: (φ : k⟦X⟧) (h : constantCoeff φ != 0)
  结论: φ⁻¹ * φ = 1
  证明: MvPowerSeries.inv_mul_cancel φ h
-/
protected theorem inv_mul_cancel (φ : k⟦X⟧) (h : constantCoeff φ != 0) : φ⁻¹ * φ = 1 :=
  MvPowerSeries.inv_mul_cancel φ h

/--
theorem `eq_mul_inv_iff_mul_eq` / 定理 `eq_mul_inv_iff_mul_eq`

English:
theorem eq_mul_inv_iff_mul_eq
  given: {φ₁ φ₂ φ₃ : k⟦X⟧} (h : constantCoeff φ₃ != 0)
  proof: MvPowerSeries.eq_mul_inv_iff_mul_eq h

中文:
定理 eq_mul_inv_iff_mul_eq
  条件: {φ₁ φ₂ φ₃ : k⟦X⟧} (h : constantCoeff φ₃ != 0)
  证明: MvPowerSeries.eq_mul_inv_iff_mul_eq h

Depends on / 依赖: MvPowerSeries, MvPowerSeries.eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq
-/
theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : k⟦X⟧} (h : constantCoeff φ₃ != 0) :
    φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
  MvPowerSeries.eq_mul_inv_iff_mul_eq h

/--
theorem `eq_inv_iff_mul_eq_one` / 定理 `eq_inv_iff_mul_eq_one`

English:
theorem eq_inv_iff_mul_eq_one
  given: {φ ψ : k⟦X⟧} (h : constantCoeff ψ != 0)
  proof: MvPowerSeries.eq_inv_iff_mul_eq_one h

中文:
定理 eq_inv_iff_mul_eq_one
  条件: {φ ψ : k⟦X⟧} (h : constantCoeff ψ != 0)
  证明: MvPowerSeries.eq_inv_iff_mul_eq_one h

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, MvPowerSeries, MvPowerSeries.eq_inv_iff_mul_eq_one, UniformSpaceCat, eq_inv_iff_mul_eq_one
-/
theorem eq_inv_iff_mul_eq_one {φ ψ : k⟦X⟧} (h : constantCoeff ψ != 0) :
    φ = ψ⁻¹ ↔ φ * ψ = 1 :=
  MvPowerSeries.eq_inv_iff_mul_eq_one h

/--
theorem `inv_eq_iff_mul_eq_one` / 定理 `inv_eq_iff_mul_eq_one`

English:
theorem inv_eq_iff_mul_eq_one
  given: {φ ψ : k⟦X⟧} (h : constantCoeff ψ != 0)
  proof: MvPowerSeries.inv_eq_iff_mul_eq_one h

中文:
定理 inv_eq_iff_mul_eq_one
  条件: {φ ψ : k⟦X⟧} (h : constantCoeff ψ != 0)
  证明: MvPowerSeries.inv_eq_iff_mul_eq_one h

Depends on / 依赖: MvPowerSeries, MvPowerSeries.inv_eq_iff_mul_eq_one, inv_eq_iff_mul_eq_one
-/
theorem inv_eq_iff_mul_eq_one {φ ψ : k⟦X⟧} (h : constantCoeff ψ != 0) :
    ψ⁻¹ = φ ↔ φ * ψ = 1 :=
  MvPowerSeries.inv_eq_iff_mul_eq_one h

/--
theorem `mul_inv_rev` / 定理 `mul_inv_rev`

English:
theorem mul_inv_rev
  given: (φ ψ : k⟦X⟧)
  statement: (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹
  proof: MvPowerSeries.mul_inv_rev _ _

@[simp]

中文:
定理 mul_inv_rev
  条件: (φ ψ : k⟦X⟧)
  结论: (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹
  证明: MvPowerSeries.mul_inv_rev _ _

@[simp]
-/
protected theorem mul_inv_rev (φ ψ : k⟦X⟧) : (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹ :=
  MvPowerSeries.mul_inv_rev _ _

@[simp]
/--
theorem `C_inv` / 定理 `C_inv`

English:
theorem C_inv
  given: (r : k)
  statement: (C r)⁻¹ = C r⁻¹
  proof: MvPowerSeries.C_inv _

@[simp]

中文:
定理 C_inv
  条件: (r : k)
  结论: (C r)⁻¹ = C r⁻¹
  证明: MvPowerSeries.C_inv _

@[simp]

Depends on / 依赖: C_inv, MvPowerSeries, MvPowerSeries.C_inv
-/
theorem C_inv (r : k) : (C r)⁻¹ = C r⁻¹ :=
  MvPowerSeries.C_inv _

@[simp]
/--
theorem `X_inv` / 定理 `X_inv`

English:
theorem X_inv
  statement: (X : k⟦X⟧)⁻¹ = 0
  proof: MvPowerSeries.X_inv _

中文:
定理 X_inv
  结论: (X : k⟦X⟧)⁻¹ = 0
  证明: MvPowerSeries.X_inv _

Depends on / 依赖: MvPowerSeries, MvPowerSeries.X_inv, X_inv
-/
theorem X_inv : (X : k⟦X⟧)⁻¹ = 0 :=
  MvPowerSeries.X_inv _

/--
theorem `smul_inv` / 定理 `smul_inv`

English:
theorem smul_inv
  given: (r : k) (φ : k⟦X⟧)
  statement: (r • φ)⁻¹ = r⁻¹ • φ⁻¹
  proof: MvPowerSeries.smul_inv _ _

中文:
定理 smul_inv
  条件: (r : k) (φ : k⟦X⟧)
  结论: (r • φ)⁻¹ = r⁻¹ • φ⁻¹
  证明: MvPowerSeries.smul_inv _ _

Depends on / 依赖: MvPowerSeries, MvPowerSeries.smul_inv, smul_inv
-/
theorem smul_inv (r : k) (φ : k⟦X⟧) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹ :=
  MvPowerSeries.smul_inv _ _

/--
Definition of `firstUnitCoeff` / `firstUnitCoeff` 的定义

English:
definition firstUnitCoeff
  signature: {f : k⟦X⟧} (hf : f != 0)
  body: have : Invertible (constantCoeff (divXPowOrder f)) := by
    apply invertibleOfNonzero
    simpa [constantCoeff_divXPowOrder_eq_zero_iff.not]
  unitOfInvertible (constantCoeff (divXPowOrder f))

中文:
定义 firstUnitCoeff
  签名: {f : k⟦X⟧} (hf : f != 0)
  定义体: have : Invertible (constantCoeff (divXPowOrder f)) := by
    apply invertibleOfNonzero
    simpa [constantCoeff_divXPowOrder_eq_zero_iff.not]
  unitOfInvertible (constantCoeff (divXPowOrder f))

Depends on / 依赖: Invertible, constantCoeff, constantCoeff_divXPowOrder_eq_zero_iff, constantCoeff_divXPowOrder_eq_zero_iff.not, divXPowOrder, invertibleOfNonzero, unitOfInvertible
-/
def firstUnitCoeff {f : k⟦X⟧} (hf : f != 0) : kˣ :=
  have : Invertible (constantCoeff (divXPowOrder f)) := by
    apply invertibleOfNonzero
    simpa [constantCoeff_divXPowOrder_eq_zero_iff.not]
  unitOfInvertible (constantCoeff (divXPowOrder f))

/--
Definition of `Inv_divided_by_X_pow_order` / `Inv_divided_by_X_pow_order` 的定义

English:
definition Inv_divided_by_X_pow_order
  signature: {f : k⟦X⟧} (hf : f != 0)
  body: invOfUnit (divXPowOrder f) (firstUnitCoeff hf)

@[simp]

中文:
定义 Inv_divided_by_X_pow_order
  签名: {f : k⟦X⟧} (hf : f != 0)
  定义体: invOfUnit (divXPowOrder f) (firstUnitCoeff hf)

@[simp]

Depends on / 依赖: divXPowOrder, firstUnitCoeff, invOfUnit
-/
def Inv_divided_by_X_pow_order {f : k⟦X⟧} (hf : f != 0) : k⟦X⟧ :=
  invOfUnit (divXPowOrder f) (firstUnitCoeff hf)

@[simp]
/--
theorem `Inv_divided_by_X_pow_order_rightInv` / 定理 `Inv_divided_by_X_pow_order_rightInv`

English:
theorem Inv_divided_by_X_pow_order_rightInv
  given: {f : k⟦X⟧} (hf : f != 0)
  proof: mul_invOfUnit (divXPowOrder f) (firstUnitCoeff hf) rfl

@[simp]

中文:
定理 Inv_divided_by_X_pow_order_rightInv
  条件: {f : k⟦X⟧} (hf : f != 0)
  证明: mul_invOfUnit (divXPowOrder f) (firstUnitCoeff hf) rfl

@[simp]

Depends on / 依赖: divXPowOrder, firstUnitCoeff, mul_invOfUnit
-/
theorem Inv_divided_by_X_pow_order_rightInv {f : k⟦X⟧} (hf : f != 0) :
    divXPowOrder f * Inv_divided_by_X_pow_order hf = 1 :=
  mul_invOfUnit (divXPowOrder f) (firstUnitCoeff hf) rfl

@[simp]
/--
theorem `Inv_divided_by_X_pow_order_leftInv` / 定理 `Inv_divided_by_X_pow_order_leftInv`

English:
theorem Inv_divided_by_X_pow_order_leftInv
  given: {f : k⟦X⟧} (hf : f != 0)
  proof: by
  rw [mul_comm]
  exact mul_invOfUnit (divXPowOrder f) (firstUnitCoeff hf) rfl

中文:
定理 Inv_divided_by_X_pow_order_leftInv
  条件: {f : k⟦X⟧} (hf : f != 0)
  证明: by
  rw [mul_comm]
  exact mul_invOfUnit (divXPowOrder f) (firstUnitCoeff hf) rfl

Depends on / 依赖: divXPowOrder, firstUnitCoeff, mul_comm, mul_invOfUnit
-/
theorem Inv_divided_by_X_pow_order_leftInv {f : k⟦X⟧} (hf : f != 0) :
    Inv_divided_by_X_pow_order hf * divXPowOrder f = 1 := by
  rw [mul_comm]
  exact mul_invOfUnit (divXPowOrder f) (firstUnitCoeff hf) rfl

open scoped Classical in
/--
Definition of `Unit_of_divided_by_X_pow_order` / `Unit_of_divided_by_X_pow_order` 的定义

English:
definition Unit_of_divided_by_X_pow_order
  signature: (f : k⟦X⟧)
  body: if hf : f = 0 then 1
  else
    { val := divXPowOrder f
      inv := Inv_divided_by_X_pow_order hf
      val_inv := Inv_divided_by_X_pow_order_rightInv hf
      inv_val := Inv_divided_by_X_pow_order_leftInv hf }

中文:
定义 Unit_of_divided_by_X_pow_order
  签名: (f : k⟦X⟧)
  定义体: if hf : f = 0 then 1
  else
    { val := divXPowOrder f
      inv := Inv_divided_by_X_pow_order hf
      val_inv := Inv_divided_by_X_pow_order_rightInv hf
      inv_val := Inv_divided_by_X_pow_order_leftInv hf }

Depends on / 依赖: Inv_divided_by_X_pow_order, Inv_divided_by_X_pow_order_leftInv, Inv_divided_by_X_pow_order_rightInv, divXPowOrder, inv_val, val_inv
-/
def Unit_of_divided_by_X_pow_order (f : k⟦X⟧) : k⟦X⟧ˣ :=
  if hf : f = 0 then 1
  else
    { val := divXPowOrder f
      inv := Inv_divided_by_X_pow_order hf
      val_inv := Inv_divided_by_X_pow_order_rightInv hf
      inv_val := Inv_divided_by_X_pow_order_leftInv hf }

/--
theorem `isUnit_divided_by_X_pow_order` / 定理 `isUnit_divided_by_X_pow_order`

English:
theorem isUnit_divided_by_X_pow_order
  given: {f : k⟦X⟧} (hf : f != 0)
  proof: ⟨Unit_of_divided_by_X_pow_order f,
    by simp only [Unit_of_divided_by_X_pow_order, dif_neg hf, Units.val_mk]⟩

中文:
定理 isUnit_divided_by_X_pow_order
  条件: {f : k⟦X⟧} (hf : f != 0)
  证明: ⟨Unit_of_divided_by_X_pow_order f,
    by simp only [Unit_of_divided_by_X_pow_order, dif_neg hf, Units.val_mk]⟩

Depends on / 依赖: Unit_of_divided_by_X_pow_order, Units.val_mk, dif_neg, val_mk
-/
theorem isUnit_divided_by_X_pow_order {f : k⟦X⟧} (hf : f != 0) :
    IsUnit (divXPowOrder f) :=
  ⟨Unit_of_divided_by_X_pow_order f,
    by simp only [Unit_of_divided_by_X_pow_order, dif_neg hf, Units.val_mk]⟩

/--
theorem `Unit_of_divided_by_X_pow_order_nonzero` / 定理 `Unit_of_divided_by_X_pow_order_nonzero`

English:
theorem Unit_of_divided_by_X_pow_order_nonzero
  given: {f : k⟦X⟧} (hf : f != 0)
  proof: by
  simp only [Unit_of_divided_by_X_pow_order, dif_neg hf, Units.val_mk]

@[simp]

中文:
定理 Unit_of_divided_by_X_pow_order_nonzero
  条件: {f : k⟦X⟧} (hf : f != 0)
  证明: by
  simp only [Unit_of_divided_by_X_pow_order, dif_neg hf, Units.val_mk]

@[simp]

Depends on / 依赖: Unit_of_divided_by_X_pow_order, Units.val_mk, dif_neg, val_mk
-/
theorem Unit_of_divided_by_X_pow_order_nonzero {f : k⟦X⟧} (hf : f != 0) :
    ↑(Unit_of_divided_by_X_pow_order f) = divXPowOrder f := by
  simp only [Unit_of_divided_by_X_pow_order, dif_neg hf, Units.val_mk]

@[simp]
/--
theorem `Unit_of_divided_by_X_pow_order_zero` / 定理 `Unit_of_divided_by_X_pow_order_zero`

English:
theorem Unit_of_divided_by_X_pow_order_zero
  statement: Unit_of_divided_by_X_pow_order (0 : k⟦X⟧) = 1
  proof: by
  simp only [Unit_of_divided_by_X_pow_order, dif_pos]

中文:
定理 Unit_of_divided_by_X_pow_order_zero
  结论: Unit_of_divided_by_X_pow_order (0 : k⟦X⟧) = 1
  证明: by
  simp only [Unit_of_divided_by_X_pow_order, dif_pos]

Depends on / 依赖: Unit_of_divided_by_X_pow_order, dif_pos
-/
theorem Unit_of_divided_by_X_pow_order_zero : Unit_of_divided_by_X_pow_order (0 : k⟦X⟧) = 1 := by
  simp only [Unit_of_divided_by_X_pow_order, dif_pos]

/--
theorem `eq_divided_by_X_pow_order_Iff_Unit` / 定理 `eq_divided_by_X_pow_order_Iff_Unit`

English:
theorem eq_divided_by_X_pow_order_Iff_Unit
  given: {f : k⟦X⟧} (hf : f != 0)
  proof: ⟨fun h => by rw [h]; exact isUnit_divided_by_X_pow_order hf, fun h => by
    have : f.order = 0 := by
      simp [order_zero_of_unit h]
    conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f := f), this, ENat.toNat_zero,
      pow_zero, one_mul]⟩

中文:
定理 eq_divided_by_X_pow_order_Iff_Unit
  条件: {f : k⟦X⟧} (hf : f != 0)
  证明: ⟨fun h => by rw [h]; exact isUnit_divided_by_X_pow_order hf, fun h => by
    have : f.order = 0 := by
      simp [order_zero_of_unit h]
    conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f := f), this, ENat.toNat_zero,
      pow_zero, one_mul]⟩

Depends on / 依赖: ENat.toNat_zero, X_pow_order_mul_divXPowOrder, conv_lhs, f.order, isUnit_divided_by_X_pow_order, one_mul, order_zero_of_unit, pow_zero, toNat_zero
-/
theorem eq_divided_by_X_pow_order_Iff_Unit {f : k⟦X⟧} (hf : f != 0) :
    f = divXPowOrder f ↔ IsUnit f :=
  ⟨fun h => by rw [h]; exact isUnit_divided_by_X_pow_order hf, fun h => by
    have : f.order = 0 := by
      simp [order_zero_of_unit h]
    conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f := f), this, ENat.toNat_zero,
      pow_zero, one_mul]⟩

end Field

section IsLocalRing

variable {S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) [IsLocalHom f]

@[instance]
/--
theorem `map.isLocalHom` / 定理 `map.isLocalHom`

English:
theorem map.isLocalHom
  statement: IsLocalHom (map f)
  proof: MvPowerSeries.map.isLocalHom f

中文:
定理 map.isLocalHom
  结论: 是Local态射 (map f)
  证明: MvPowerSeries.map.isLocalHom f
-/
theorem map.isLocalHom : IsLocalHom (map f) :=
  MvPowerSeries.map.isLocalHom f

end IsLocalRing

section IsDiscreteValuationRing

variable {k : Type*} [Field k]

open IsDiscreteValuationRing

/--
theorem `hasUnitMulPowIrreducibleFactorization` / 定理 `hasUnitMulPowIrreducibleFactorization`

English:
theorem hasUnitMulPowIrreducibleFactorization
  proof: ⟨X, And.intro X_irreducible
      (by
        intro f hf
        use f.order.toNat
        use Unit_of_divided_by_X_pow_order f
        simp only [Unit_of_divided_by_X_pow_order_nonzero hf]
        exact X_pow_order_mul_divXPowOrder)⟩

中文:
定理 hasUnitMulPowIrreducibleFactorization
  证明: ⟨X, And.intro X_irreducible
      (by
        intro f hf
        use f.order.toNat
        use Unit_of_divided_by_X_pow_order f
        simp only [Unit_of_divided_by_X_pow_order_nonzero hf]
        exact X_pow_order_mul_divXPowOrder)⟩

Depends on / 依赖: And.intro, Unit_of_divided_by_X_pow_order, Unit_of_divided_by_X_pow_order_nonzero, X_irreducible, X_pow_order_mul_divXPowOrder, f.order.toNat
-/
theorem hasUnitMulPowIrreducibleFactorization :
    HasUnitMulPowIrreducibleFactorization k⟦X⟧ :=
  ⟨X, And.intro X_irreducible
      (by
        intro f hf
        use f.order.toNat
        use Unit_of_divided_by_X_pow_order f
        simp only [Unit_of_divided_by_X_pow_order_nonzero hf]
        exact X_pow_order_mul_divXPowOrder)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniqueFactorizationMonoid k⟦X⟧
  body: hasUnitMulPowIrreducibleFactorization.toUniqueFactorizationMonoid

中文:
实例 :
  签名: 唯一分解幺半群 k⟦X⟧
  定义体: hasUnitMulPowIrreducibleFactorization.toUniqueFactorizationMonoid

Depends on / 依赖: hasUnitMulPowIrreducibleFactorization, hasUnitMulPowIrreducibleFactorization.toUniqueFactorizationMonoid, toUniqueFactorizationMonoid
-/
instance : UniqueFactorizationMonoid k⟦X⟧ :=
  hasUnitMulPowIrreducibleFactorization.toUniqueFactorizationMonoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDiscreteValuationRing k⟦X⟧
  body: ofHasUnitMulPowIrreducibleFactorization hasUnitMulPowIrreducibleFactorization

example : IsNoetherianRing k⟦X⟧ := inferInstance

中文:
实例 :
  签名: 是离散赋值环 k⟦X⟧
  定义体: ofHasUnitMulPowIrreducibleFactorization hasUnitMulPowIrreducibleFactorization

example : IsNoetherianRing k⟦X⟧ := inferInstance

Depends on / 依赖: hasUnitMulPowIrreducibleFactorization, ofHasUnitMulPowIrreducibleFactorization
-/
instance : IsDiscreteValuationRing k⟦X⟧ :=
  ofHasUnitMulPowIrreducibleFactorization hasUnitMulPowIrreducibleFactorization

example : IsNoetherianRing k⟦X⟧ := inferInstance

/--
theorem `maximalIdeal_eq_span_X` / 定理 `maximalIdeal_eq_span_X`

English:
theorem maximalIdeal_eq_span_X
  statement: IsLocalRing.maximalIdeal (k⟦X⟧) = Ideal.span {X}
  proof: by
  have hX : (Ideal.span {(X : k⟦X⟧)}).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · rw [Ideal.mem_span_singleton]
      exact Prime.not_dvd_one X_prime
    · intro I f hI hfX hfI
      rw [Ideal.mem_span_singleton]; rw [X_dvd_iff] at hfX
      have hfI0 : C (f 0) in I := by
 

中文:
定理 maximalIdeal_eq_span_X
  结论: 是局部环.maximalIdeal (k⟦X⟧) = 理想.span {X}
  证明: by
  have hX : (Ideal.span {(X : k⟦X⟧)}).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · rw [Ideal.mem_span_singleton]
      exact Prime.not_dvd_one X_prime
    · intro I f hI hfX hfI
      rw [Ideal.mem_span_singleton]; rw [X_dvd_iff] at hfX
      have hfI0 : C (f 0) in I := by
 

Depends on / 依赖: Ideal.isMaximal_iff, Ideal.mem_span_singleton, Ideal.span, Ideal.sub_mem, IsMaximal, Prime.not_dvd_one, X_dvd_iff, X_prime, coeff_zero_eq_constantCoeff_apply, constantCoeff_C, isMaximal_iff, map_sub, mem_span_singleton, not_dvd_one, sub_mem, sub_sub_cancel
-/
theorem maximalIdeal_eq_span_X : IsLocalRing.maximalIdeal (k⟦X⟧) = Ideal.span {X} := by
  have hX : (Ideal.span {(X : k⟦X⟧)}).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · rw [Ideal.mem_span_singleton]
      exact Prime.not_dvd_one X_prime
    · intro I f hI hfX hfI
      rw [Ideal.mem_span_singleton]; rw [X_dvd_iff] at hfX
      have hfI0 : C (f 0) in I := by
        have : C (f 0) = f - (f - C (f 0)) := by rw [sub_sub_cancel]
        rw [this]
        apply Ideal.sub_mem I hfI
        apply hI
        rw [Ideal.mem_span_singleton]; rw [X_dvd_iff]; rw [map_sub]; rw [constantCoeff_C]; rw [←
          coeff_zero_eq_constantCoeff_apply]; rw [sub_eq_zero]; rw [coeff_zero_eq_constantCoeff]
        rfl
      rw [← Ideal.eq_top_iff_one]
      apply Ideal.eq_top_of_isUnit_mem I hfI0 (IsUnit.map C (Ne.isUnit hfX))
  rw [IsLocalRing.eq_maximalIdeal hX]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StrongNormalizationMonoid k⟦X⟧
  body: (Unit_of_divided_by_X_pow_order f)⁻¹
  normUnit_zero := by simp only [Unit_of_divided_by_X_pow_order_zero, inv_one]
  normUnit_mul hf hg := by
    simp only [← mul_inv, inv_inj]
    simp only [Unit_of_divided_by_X_pow_order_nonzero (mul_ne_zero hf hg),
      Unit_of_divided_by_X_pow_order_nonzero hf

中文:
实例 :
  签名: StrongNormalization幺半群 k⟦X⟧
  定义体: (Unit_of_divided_by_X_pow_order f)⁻¹
  normUnit_zero := by simp only [Unit_of_divided_by_X_pow_order_zero, inv_one]
  normUnit_mul hf hg := by
    simp only [← mul_inv, inv_inj]
    simp only [Unit_of_divided_by_X_pow_order_nonzero (mul_ne_zero hf hg),
      Unit_of_divided_by_X_pow_order_nonzero hf

Depends on / 依赖: Unit_of_divided_by_X_pow_order
-/
instance : StrongNormalizationMonoid k⟦X⟧ where
  normUnit f := (Unit_of_divided_by_X_pow_order f)⁻¹
  normUnit_zero := by simp only [Unit_of_divided_by_X_pow_order_zero, inv_one]
  normUnit_mul hf hg := by
    simp only [← mul_inv, inv_inj]
    simp only [Unit_of_divided_by_X_pow_order_nonzero (mul_ne_zero hf hg),
      Unit_of_divided_by_X_pow_order_nonzero hf, Unit_of_divided_by_X_pow_order_nonzero hg,
      Units.ext_iff, Units.val_mul, ← divXPowOrder_mul]
  normUnit_coe_units u := by
    set u₀ := u.1 with hu
    have h₀ : IsUnit u₀ := ⟨u, hu.symm⟩
    rw [inv_inj]; rw [Units.ext_iff]; rw [← hu]; rw [Unit_of_divided_by_X_pow_order_nonzero h₀.ne_zero]
    exact ((eq_divided_by_X_pow_order_Iff_Unit h₀.ne_zero).mpr h₀).symm

/--
theorem `normUnit_X` / 定理 `normUnit_X`

English:
theorem normUnit_X
  statement: normUnit (X : k⟦X⟧) = 1
  proof: by
  simp [normUnit, ← Units.val_eq_one, Unit_of_divided_by_X_pow_order_nonzero]

中文:
定理 normUnit_X
  结论: normUnit (X : k⟦X⟧) = 1
  证明: by
  simp [normUnit, ← Units.val_eq_one, Unit_of_divided_by_X_pow_order_nonzero]

Depends on / 依赖: Unit_of_divided_by_X_pow_order_nonzero, Units.val_eq_one, normUnit, val_eq_one
-/
theorem normUnit_X : normUnit (X : k⟦X⟧) = 1 := by
  simp [normUnit, ← Units.val_eq_one, Unit_of_divided_by_X_pow_order_nonzero]

/--
theorem `X_eq_normalizeX` / 定理 `X_eq_normalizeX`

English:
theorem X_eq_normalizeX
  statement: (X : k⟦X⟧) = normalize X
  proof: by
  simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

中文:
定理 X_eq_normalizeX
  结论: (X : k⟦X⟧) = normalize X
  证明: by
  simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

Depends on / 依赖: Units.val_one, mul_one, normUnit_X, normalize_apply, val_one
-/
theorem X_eq_normalizeX : (X : k⟦X⟧) = normalize X := by
  simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

open UniqueFactorizationMonoid

open scoped Classical in
/--
theorem `normalized_count_X_eq_of_coe` / 定理 `normalized_count_X_eq_of_coe`

English:
theorem normalized_count_X_eq_of_coe
  given: {P : k[X]} (hP : P != 0)
  proof: by
  apply eq_of_forall_le_iff
  simp only [← Nat.cast_le (α := Nat∞)]
  rw [X_eq_normalize]; rw [PowerSeries.X_eq_normalizeX]; rw [← emultiplicity_eq_count_normalizedFactors
    irreducible_X hP]; rw [← emultiplicity_eq_count_normalizedFactors X_irreducible] <;>
  simp only [← pow_dvd_iff_le_emulti

中文:
定理 normalized_count_X_eq_of_coe
  条件: {P : k[X]} (hP : P != 0)
  证明: by
  apply eq_of_forall_le_iff
  simp only [← Nat.cast_le (α := Nat∞)]
  rw [X_eq_normalize]; rw [PowerSeries.X_eq_normalizeX]; rw [← emultiplicity_eq_count_normalizedFactors
    irreducible_X hP]; rw [← emultiplicity_eq_count_normalizedFactors X_irreducible] <;>
  simp only [← pow_dvd_iff_le_emulti

Depends on / 依赖: Nat.cast_le, Polynomial, Polynomial.X_pow_dvd_iff, Polynomial.coeff_coe, PowerSeries, PowerSeries.X_eq_normalizeX, PowerSeries.X_pow_dvd_iff, X_eq_normalize, X_eq_normalizeX, X_irreducible, X_pow_dvd_iff, cast_le, coe_eq_zero_iff, coeff_coe, emultiplicity_eq_count_normalizedFactors, eq_of_forall_le_iff, implies_true, irreducible_X, ne_eq, not_false_eq_true
-/
theorem normalized_count_X_eq_of_coe {P : k[X]} (hP : P != 0) :
    Multiset.count PowerSeries.X (normalizedFactors (P : k⟦X⟧)) =
      Multiset.count Polynomial.X (normalizedFactors P) := by
  apply eq_of_forall_le_iff
  simp only [← Nat.cast_le (α := Nat∞)]
  rw [X_eq_normalize]; rw [PowerSeries.X_eq_normalizeX]; rw [← emultiplicity_eq_count_normalizedFactors
    irreducible_X hP]; rw [← emultiplicity_eq_count_normalizedFactors X_irreducible] <;>
  simp only [← pow_dvd_iff_le_emultiplicity, Polynomial.X_pow_dvd_iff,
    PowerSeries.X_pow_dvd_iff, Polynomial.coeff_coe P, implies_true, ne_eq, coe_eq_zero_iff, hP,
    not_false_eq_true]

open IsLocalRing

/--
theorem `ker_coeff_eq_max_ideal` / 定理 `ker_coeff_eq_max_ideal`

English:
theorem ker_coeff_eq_max_ideal
  statement: RingHom.ker (constantCoeff (R := k)) = maximalIdeal _
  proof: Ideal.ext fun _ => by
    rw [RingHom.mem_ker]; rw [maximalIdeal_eq_span_X]; rw [Ideal.mem_span_singleton]; rw [X_dvd_iff]

中文:
定理 ker_coeff_eq_max_ideal
  结论: 环态射.ker (constantCoeff (R := k)) = maximalIdeal _
  证明: Ideal.ext fun _ => by
    rw [RingHom.mem_ker]; rw [maximalIdeal_eq_span_X]; rw [Ideal.mem_span_singleton]; rw [X_dvd_iff]

Depends on / 依赖: maximalIdeal
-/
theorem ker_coeff_eq_max_ideal : RingHom.ker (constantCoeff (R := k)) = maximalIdeal _ :=
  Ideal.ext fun _ => by
    rw [RingHom.mem_ker]; rw [maximalIdeal_eq_span_X]; rw [Ideal.mem_span_singleton]; rw [X_dvd_iff]

/--
Definition of `residueFieldOfPowerSeries` / `residueFieldOfPowerSeries` 的定义

English:
definition residueFieldOfPowerSeries
  signature: : ResidueField k⟦X⟧ ≃+* k
  body: .trans Ideal.quotEquivOfEq (ker_coeff_eq_max_ideal).symm
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)

中文:
定义 residueFieldOfPowerSeries
  签名: : ResidueField k⟦X⟧ ≃+* k
  定义体: .trans Ideal.quotEquivOfEq (ker_coeff_eq_max_ideal).symm
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)

Depends on / 依赖: Ideal.quotEquivOfEq, RingHom, RingHom.quotientKerEquivOfSurjective, constantCoeff_surj, ker_coeff_eq_max_ideal, quotEquivOfEq, quotientKerEquivOfSurjective
-/
def residueFieldOfPowerSeries : ResidueField k⟦X⟧ ≃+* k :=
.trans Ideal.quotEquivOfEq (ker_coeff_eq_max_ideal).symm
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)

end IsDiscreteValuationRing


end PowerSeries

end
