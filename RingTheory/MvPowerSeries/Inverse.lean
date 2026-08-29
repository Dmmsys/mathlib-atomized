/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Formal (multivariate) power series - Inverses

This file defines multivariate formal power series and develops the basic
properties of these objects, when it comes about multiplicative inverses.

For `φ : MvPowerSeries σ R` and `u : Rˣ` is the constant coefficient of `φ`,
`MvPowerSeries.invOfUnit φ u` is a formal power series such,
and `MvPowerSeries.mul_invOfUnit` proves that `φ * invOfUnit φ u = 1`.
The construction of the power series `invOfUnit` is done by writing that
relation and solving and for its coefficients by induction.

Over a field, all power series `φ` have an “inverse” `MvPowerSeries.inv φ`,
which is `0` if and only if the constant coefficient of `φ` is zero
(by `MvPowerSeries.inv_eq_zero`),
and `MvPowerSeries.mul_inv_cancel` asserts the equality `φ * φ⁻¹ = 1` when
the constant coefficient of `φ` is nonzero.

Instances are defined:

* Formal power series over a local ring form a local ring.
* The morphism `MvPowerSeries.map σ f : MvPowerSeries σ A →* MvPowerSeries σ B`
  induced by a local morphism `f : A →+* B` (`IsLocalHom f`)
  of commutative rings is a *local* morphism.

-/

@[expose] public section


noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

section Ring

variable [Ring R]

/-
The inverse of a multivariate formal power series is defined by
well-founded recursion on the coefficients of the inverse.
-/
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def inv.aux (a : R) (φ : MvPowerSeries σ R)
  body: Classical.decEq σ
    if n = 0 then a
    else
      -a *
        ∑ x in antidiagonal n, if _ : x.2 < n then coeff x.1 φ * inv.aux a φ x.2 else 0
termination_by n => n

中文:
定义 noncomputable
  签名: def inv.aux (a : R) (φ : MvPowerSeries σ R)
  定义体: Classical.decEq σ
    if n = 0 then a
    else
      -a *
        ∑ x in antidiagonal n, if _ : x.2 < n then coeff x.1 φ * inv.aux a φ x.2 else 0
termination_by n => n
-/
protected noncomputable def inv.aux (a : R) (φ : MvPowerSeries σ R) : MvPowerSeries σ R
  | n =>
    letI := Classical.decEq σ
    if n = 0 then a
    else
      -a *
        ∑ x in antidiagonal n, if _ : x.2 < n then coeff x.1 φ * inv.aux a φ x.2 else 0
termination_by n => n

/--
theorem `coeff_inv_aux` / 定理 `coeff_inv_aux`

English:
theorem coeff_inv_aux
  given: [DecidableEq σ] (n : σ ->₀ Nat) (a : R) (φ : MvPowerSeries σ R)
  proof: show inv.aux a φ n = _ by
    cases Subsingleton.elim ‹DecidableEq σ› (Classical.decEq σ)
    rw [inv.aux]
    rfl

中文:
定理 coeff_inv_aux
  条件: [DecidableEq σ] (n : σ ->₀ 自然数) (a : R) (φ : MvPowerSeries σ R)
  证明: show inv.aux a φ n = _ by
    cases Subsingleton.elim ‹DecidableEq σ› (Classical.decEq σ)
    rw [inv.aux]
    rfl

Depends on / 依赖: Classical, Classical.decEq, DecidableEq, Subsingleton, Subsingleton.elim, inv.aux
-/
theorem coeff_inv_aux [DecidableEq σ] (n : σ ->₀ Nat) (a : R) (φ : MvPowerSeries σ R) :
    coeff n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x in antidiagonal n, if x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0 :=
  show inv.aux a φ n = _ by
    cases Subsingleton.elim ‹DecidableEq σ› (Classical.decEq σ)
    rw [inv.aux]
    rfl

/--
Definition of `invOfUnit` / `invOfUnit` 的定义

English:
definition invOfUnit
  signature: (φ : MvPowerSeries σ R) (u : Rˣ)
  body: inv.aux (↑u⁻¹) φ

中文:
定义 invOfUnit
  签名: (φ : MvPowerSeries σ R) (u : Rˣ)
  定义体: inv.aux (↑u⁻¹) φ

Depends on / 依赖: inv.aux
-/
def invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) : MvPowerSeries σ R :=
  inv.aux (↑u⁻¹) φ

/--
theorem `coeff_invOfUnit` / 定理 `coeff_invOfUnit`

English:
theorem coeff_invOfUnit
  given: [DecidableEq σ] (n : σ ->₀ Nat) (φ : MvPowerSeries σ R) (u : Rˣ)
  proof: by
  convert! coeff_inv_aux n (↑u⁻¹) φ

@[simp]

中文:
定理 coeff_invOfUnit
  条件: [DecidableEq σ] (n : σ ->₀ 自然数) (φ : MvPowerSeries σ R) (u : Rˣ)
  证明: by
  convert! coeff_inv_aux n (↑u⁻¹) φ

@[simp]

Depends on / 依赖: coeff_inv_aux, convert
-/
theorem coeff_invOfUnit [DecidableEq σ] (n : σ ->₀ Nat) (φ : MvPowerSeries σ R) (u : Rˣ) :
    coeff n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x in antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 (invOfUnit φ u) else 0 := by
  convert! coeff_inv_aux n (↑u⁻¹) φ

@[simp]
/--
theorem `constantCoeff_invOfUnit` / 定理 `constantCoeff_invOfUnit`

English:
theorem constantCoeff_invOfUnit
  given: (φ : MvPowerSeries σ R) (u : Rˣ)
  proof: by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_invOfUnit]; rw [if_pos rfl]

@[simp]

中文:
定理 constantCoeff_invOfUnit
  条件: (φ : MvPowerSeries σ R) (u : Rˣ)
  证明: by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_invOfUnit]; rw [if_pos rfl]

@[simp]

Depends on / 依赖: classical, coeff_invOfUnit, coeff_zero_eq_constantCoeff_apply, if_pos
-/
theorem constantCoeff_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) :
    constantCoeff (invOfUnit φ u) = ↑u⁻¹ := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_invOfUnit]; rw [if_pos rfl]

@[simp]
/--
theorem `mul_invOfUnit` / 定理 `mul_invOfUnit`

English:
theorem mul_invOfUnit
  given: (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff φ = u)
  proof: ext fun n =>
    letI := Classical.decEq (σ ->₀ Nat)
    if H : n = 0 then by
      rw [H]
      simp [h]
    else by
      classical
      have : ((0 : σ ->₀ Nat), n) in antidiagonal n := by rw [mem_antidiagonal, zero_add]
      rw [coeff_one]; rw [if_neg H]; rw [coeff_mul]; rw [← Finset.insert_erase this]; rw [Finset.sum_insert (Finset.notMem_erase _ _)]; rw [coeff_zero_eq_constantCoeff_apply]; rw [h]; rw [coeff_invOfUnit]; rw [if_neg H]; rw [neg_mul]; rw [mul_neg]; rw [Units.mul_inv_cancel_left]; rw [←
        Finset.insert_erase this]; rw [Finset.sum_insert (Finset.notMem_erase _ _)]; rw [Finset.insert_erase this]; rw [if_neg (not_lt_of_ge <| le_rfl)]; rw [zero_add]; rw [add_comm]; rw [←
        sub_eq_add_neg]; rw [sub_eq_zero]; rw [Finset.sum_congr rfl]
      rintro ⟨i, j⟩ hij
      rw [Finset.mem_erase]; rw [mem_antidiagonal] at hij
      obtain ⟨h₁, rfl⟩ := hij
      rw [if_pos]
refine lt_add_of_pos_left _ pos_iff_ne_zero.2 ?_
      rintro rfl
      simp at h₁

中文:
定理 mul_invOfUnit
  条件: (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff φ = u)
  证明: ext fun n =>
    letI := Classical.decEq (σ ->₀ Nat)
    if H : n = 0 then by
      rw [H]
      simp [h]
    else by
      classical
      have : ((0 : σ ->₀ Nat), n) in antidiagonal n := by rw [mem_antidiagonal, zero_add]
      rw [coeff_one]; rw [if_neg H]; rw [coeff_mul]; rw [← Finset.insert_erase this]; rw [Finset.sum_insert (Finset.notMem_erase _ _)]; rw [coeff_zero_eq_constantCoeff_apply]; rw [h]; rw [coeff_invOfUnit]; rw [if_neg H]; rw [neg_mul]; rw [mul_neg]; rw [Units.mul_inv_cancel_left]; rw [←
        Finset.insert_erase this]; rw [Finset.sum_insert (Finset.notMem_erase _ _)]; rw [Finset.insert_erase this]; rw [if_neg (not_lt_of_ge <| le_rfl)]; rw [zero_add]; rw [add_comm]; rw [←
        sub_eq_add_neg]; rw [sub_eq_zero]; rw [Finset.sum_congr rfl]
      rintro ⟨i, j⟩ hij
      rw [Finset.mem_erase]; rw [mem_antidiagonal] at hij
      obtain ⟨h₁, rfl⟩ := hij
      rw [if_pos]
refine lt_add_of_pos_left _ pos_iff_ne_zero.2 ?_
      rintro rfl
      simp at h₁

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.insert_erase, Finset.notMem_erase, Finset.sum_insert, Units.mul_inv_cancel_left, antidiagonal, classical, coeff_invOfUnit, coeff_mul, coeff_one, coeff_zero_eq_constantCoeff_apply, if_neg, insert_erase, mem_antidiagonal, mul_inv_cancel_left, mul_neg, neg_mul, notMem_erase
-/
theorem mul_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff φ = u) :
    φ * invOfUnit φ u = 1 :=
  ext fun n =>
    letI := Classical.decEq (σ ->₀ Nat)
    if H : n = 0 then by
      rw [H]
      simp [h]
    else by
      classical
      have : ((0 : σ ->₀ Nat), n) in antidiagonal n := by rw [mem_antidiagonal, zero_add]
      rw [coeff_one]; rw [if_neg H]; rw [coeff_mul]; rw [← Finset.insert_erase this]; rw [Finset.sum_insert (Finset.notMem_erase _ _)]; rw [coeff_zero_eq_constantCoeff_apply]; rw [h]; rw [coeff_invOfUnit]; rw [if_neg H]; rw [neg_mul]; rw [mul_neg]; rw [Units.mul_inv_cancel_left]; rw [←
        Finset.insert_erase this]; rw [Finset.sum_insert (Finset.notMem_erase _ _)]; rw [Finset.insert_erase this]; rw [if_neg (not_lt_of_ge <| le_rfl)]; rw [zero_add]; rw [add_comm]; rw [←
        sub_eq_add_neg]; rw [sub_eq_zero]; rw [Finset.sum_congr rfl]
      rintro ⟨i, j⟩ hij
      rw [Finset.mem_erase]; rw [mem_antidiagonal] at hij
      obtain ⟨h₁, rfl⟩ := hij
      rw [if_pos]
refine lt_add_of_pos_left _ pos_iff_ne_zero.2 ?_
      rintro rfl
      simp at h₁

-- TODO : can one prove equivalence?
@[simp]
/--
theorem `invOfUnit_mul` / 定理 `invOfUnit_mul`

English:
theorem invOfUnit_mul
  given: (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff φ = u)
  proof: by
  rw [← mul_cancel_right_mem_nonZeroDivisors (r := φ.invOfUnit u)]; rw [mul_assoc]; rw [one_mul]; rw [mul_invOfUnit _ _ h]; rw [mul_one]
  apply mem_nonZeroDivisors_of_constantCoeff
  simp only [constantCoeff_invOfUnit, IsUnit.mem_nonZeroDivisors (Units.isUnit u⁻¹)]

中文:
定理 invOfUnit_mul
  条件: (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff φ = u)
  证明: by
  rw [← mul_cancel_right_mem_nonZeroDivisors (r := φ.invOfUnit u)]; rw [mul_assoc]; rw [one_mul]; rw [mul_invOfUnit _ _ h]; rw [mul_one]
  apply mem_nonZeroDivisors_of_constantCoeff
  simp only [constantCoeff_invOfUnit, IsUnit.mem_nonZeroDivisors (Units.isUnit u⁻¹)]

Depends on / 依赖: IsUnit, IsUnit.mem_nonZeroDivisors, Units.isUnit, constantCoeff_invOfUnit, invOfUnit, isUnit, mem_nonZeroDivisors, mem_nonZeroDivisors_of_constantCoeff, mul_assoc, mul_cancel_right_mem_nonZeroDivisors, mul_invOfUnit, mul_one, one_mul
-/
theorem invOfUnit_mul (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff φ = u) :
    invOfUnit φ u * φ = 1 := by
  rw [← mul_cancel_right_mem_nonZeroDivisors (r := φ.invOfUnit u)]; rw [mul_assoc]; rw [one_mul]; rw [mul_invOfUnit _ _ h]; rw [mul_one]
  apply mem_nonZeroDivisors_of_constantCoeff
  simp only [constantCoeff_invOfUnit, IsUnit.mem_nonZeroDivisors (Units.isUnit u⁻¹)]

/--
theorem `isUnit_iff_constantCoeff` / 定理 `isUnit_iff_constantCoeff`

English:
theorem isUnit_iff_constantCoeff
  given: {φ : MvPowerSeries σ R}
  proof: by
  constructor
  · exact IsUnit.map _
  · intro ⟨u, hu⟩
    exact ⟨⟨_, φ.invOfUnit u, mul_invOfUnit φ u hu.symm, invOfUnit_mul φ u hu.symm⟩, rfl⟩

中文:
定理 isUnit_iff_constantCoeff
  条件: {φ : MvPowerSeries σ R}
  证明: by
  constructor
  · exact IsUnit.map _
  · intro ⟨u, hu⟩
    exact ⟨⟨_, φ.invOfUnit u, mul_invOfUnit φ u hu.symm, invOfUnit_mul φ u hu.symm⟩, rfl⟩

Depends on / 依赖: IsUnit, IsUnit.map, hu.symm, invOfUnit, invOfUnit_mul, mul_invOfUnit
-/
theorem isUnit_iff_constantCoeff {φ : MvPowerSeries σ R} :
    IsUnit φ ↔ IsUnit (constantCoeff φ) := by
  constructor
  · exact IsUnit.map _
  · intro ⟨u, hu⟩
    exact ⟨⟨_, φ.invOfUnit u, mul_invOfUnit φ u hu.symm, invOfUnit_mul φ u hu.symm⟩, rfl⟩

end Ring

section CommRing

variable [CommRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLocalRing
  signature: R] : IsLocalRing (MvPowerSeries σ R)
  body: IsLocalRing.of_isUnit_or_isUnit_one_sub_self by
    intro φ
    obtain ⟨u, h⟩ | ⟨u, h⟩ := IsLocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff φ) <;>
        [left; right] <;>
      · refine .of_mul_eq_one _ (mul_invOfUnit _ u ?_)
        simpa using h.symm

中文:
实例 [是局部环
  签名: R] : 是局部环 (MvPowerSeries σ R)
  定义体: IsLocalRing.of_isUnit_or_isUnit_one_sub_self by
    intro φ
    obtain ⟨u, h⟩ | ⟨u, h⟩ := IsLocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff φ) <;>
        [left; right] <;>
      · refine .of_mul_eq_one _ (mul_invOfUnit _ u ?_)
        simpa using h.symm

Depends on / 依赖: IsLocalRing, IsLocalRing.isUnit_or_isUnit_one_sub_self, IsLocalRing.of_isUnit_or_isUnit_one_sub_self, constantCoeff, h.symm, isUnit_or_isUnit_one_sub_self, mul_invOfUnit, of_isUnit_or_isUnit_one_sub_self, of_mul_eq_one
-/
instance [IsLocalRing R] : IsLocalRing (MvPowerSeries σ R) :=
IsLocalRing.of_isUnit_or_isUnit_one_sub_self by
    intro φ
    obtain ⟨u, h⟩ | ⟨u, h⟩ := IsLocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff φ) <;>
        [left; right] <;>
      · refine .of_mul_eq_one _ (mul_invOfUnit _ u ?_)
        simpa using h.symm

-- TODO(jmc): once adic topology lands, show that this is complete
end CommRing

section IsLocalRing

variable {S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) [IsLocalHom f]

-- Thanks to the linter for informing us that this instance does
-- not actually need R and S to be local rings!
/-- The map between multivariate formal power series over the same indexing set
induced by a local ring hom `A → B` is local -/
@[instance]
/--
theorem `map.isLocalHom` / 定理 `map.isLocalHom`

English:
theorem map.isLocalHom
  statement: IsLocalHom (map (σ := σ) f)
  proof: ⟨by
    rintro φ ⟨ψ, h⟩
    replace h := congr_arg constantCoeff h
    rw [constantCoeff_map] at h
    have : IsUnit (constantCoeff ψ.val) := isUnit_constantCoeff _ ψ.isUnit
    rw [h] at this
    rcases isUnit_of_map_unit f _ this with ⟨c, hc⟩
    exact .of_mul_eq_one (invOfUnit φ c) (mul_invOfUnit φ c hc.symm)⟩

中文:
定理 map.isLocalHom
  结论: 是Local态射 (map (σ := σ) f)
  证明: ⟨by
    rintro φ ⟨ψ, h⟩
    replace h := congr_arg constantCoeff h
    rw [constantCoeff_map] at h
    have : IsUnit (constantCoeff ψ.val) := isUnit_constantCoeff _ ψ.isUnit
    rw [h] at this
    rcases isUnit_of_map_unit f _ this with ⟨c, hc⟩
    exact .of_mul_eq_one (invOfUnit φ c) (mul_invOfUnit φ c hc.symm)⟩
-/
theorem map.isLocalHom : IsLocalHom (map (σ := σ) f) :=
  ⟨by
    rintro φ ⟨ψ, h⟩
    replace h := congr_arg constantCoeff h
    rw [constantCoeff_map] at h
    have : IsUnit (constantCoeff ψ.val) := isUnit_constantCoeff _ ψ.isUnit
    rw [h] at this
    rcases isUnit_of_map_unit f _ this with ⟨c, hc⟩
    exact .of_mul_eq_one (invOfUnit φ c) (mul_invOfUnit φ c hc.symm)⟩

end IsLocalRing

section Field

open MvPowerSeries

variable {k : Type*} [Field k]

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: (φ : MvPowerSeries σ k)
  body: inv.aux (constantCoeff φ)⁻¹ φ

中文:
定义 inv
  签名: (φ : MvPowerSeries σ k)
  定义体: inv.aux (constantCoeff φ)⁻¹ φ
-/
protected def inv (φ : MvPowerSeries σ k) : MvPowerSeries σ k :=
  inv.aux (constantCoeff φ)⁻¹ φ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (MvPowerSeries σ k)
  body: ⟨MvPowerSeries.inv⟩

中文:
实例 :
  签名: 取逆 (MvPowerSeries σ k)
  定义体: ⟨MvPowerSeries.inv⟩

Depends on / 依赖: MvPowerSeries, MvPowerSeries.inv
-/
instance : Inv (MvPowerSeries σ k) :=
  ⟨MvPowerSeries.inv⟩

/--
theorem `coeff_inv` / 定理 `coeff_inv`

English:
theorem coeff_inv
  given: [DecidableEq σ] (n : σ ->₀ Nat) (φ : MvPowerSeries σ k)
  proof: coeff_inv_aux n _ φ

@[simp]

中文:
定理 coeff_inv
  条件: [DecidableEq σ] (n : σ ->₀ 自然数) (φ : MvPowerSeries σ k)
  证明: coeff_inv_aux n _ φ

@[simp]

Depends on / 依赖: coeff_inv_aux
-/
theorem coeff_inv [DecidableEq σ] (n : σ ->₀ Nat) (φ : MvPowerSeries σ k) :
    coeff n φ⁻¹ =
      if n = 0 then (constantCoeff φ)⁻¹
      else
        -(constantCoeff φ)⁻¹ *
          ∑ x in antidiagonal n, if x.2 < n then coeff x.1 φ * coeff x.2 φ⁻¹ else 0 :=
  coeff_inv_aux n _ φ

@[simp]
/--
theorem `constantCoeff_inv` / 定理 `constantCoeff_inv`

English:
theorem constantCoeff_inv
  given: (φ : MvPowerSeries σ k)
  proof: by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_inv]; rw [if_pos rfl]

中文:
定理 constantCoeff_inv
  条件: (φ : MvPowerSeries σ k)
  证明: by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_inv]; rw [if_pos rfl]

Depends on / 依赖: classical, coeff_inv, coeff_zero_eq_constantCoeff_apply, if_pos
-/
theorem constantCoeff_inv (φ : MvPowerSeries σ k) :
    constantCoeff φ⁻¹ = (constantCoeff φ)⁻¹ := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_inv]; rw [if_pos rfl]

/--
theorem `inv_eq_zero` / 定理 `inv_eq_zero`

English:
theorem inv_eq_zero
  given: {φ : MvPowerSeries σ k}
  statement: φ⁻¹ = 0 ↔ constantCoeff φ = 0
  proof: ⟨fun h => by simpa using congr_arg constantCoeff h, fun h =>
    ext fun n => by
      classical
      rw [coeff_inv]
      split_ifs <;>
        simp only [h, map_zero, zero_mul, inv_zero, neg_zero]⟩

@[simp]

中文:
定理 inv_eq_zero
  条件: {φ : MvPowerSeries σ k}
  结论: φ⁻¹ = 0 ↔ constantCoeff φ = 0
  证明: ⟨fun h => by simpa using congr_arg constantCoeff h, fun h =>
    ext fun n => by
      classical
      rw [coeff_inv]
      split_ifs <;>
        simp only [h, map_zero, zero_mul, inv_zero, neg_zero]⟩

@[simp]

Depends on / 依赖: classical, coeff_inv, congr_arg, constantCoeff, inv_zero, map_zero, neg_zero, split_ifs, zero_mul
-/
theorem inv_eq_zero {φ : MvPowerSeries σ k} : φ⁻¹ = 0 ↔ constantCoeff φ = 0 :=
  ⟨fun h => by simpa using congr_arg constantCoeff h, fun h =>
    ext fun n => by
      classical
      rw [coeff_inv]
      split_ifs <;>
        simp only [h, map_zero, zero_mul, inv_zero, neg_zero]⟩

@[simp]
/--
theorem `zero_inv` / 定理 `zero_inv`

English:
theorem zero_inv
  statement: (0 : MvPowerSeries σ k)⁻¹ = 0
  proof: by
  rw [inv_eq_zero]; rw [constantCoeff_zero]

@[simp]

中文:
定理 zero_inv
  结论: (0 : MvPowerSeries σ k)⁻¹ = 0
  证明: by
  rw [inv_eq_zero]; rw [constantCoeff_zero]

@[simp]

Depends on / 依赖: constantCoeff_zero, inv_eq_zero
-/
theorem zero_inv : (0 : MvPowerSeries σ k)⁻¹ = 0 := by
  rw [inv_eq_zero]; rw [constantCoeff_zero]

@[simp]
/--
theorem `invOfUnit_eq` / 定理 `invOfUnit_eq`

English:
theorem invOfUnit_eq
  given: (φ : MvPowerSeries σ k) (h : constantCoeff φ != 0)
  proof: rfl

@[simp]

中文:
定理 invOfUnit_eq
  条件: (φ : MvPowerSeries σ k) (h : constantCoeff φ != 0)
  证明: rfl

@[simp]
-/
theorem invOfUnit_eq (φ : MvPowerSeries σ k) (h : constantCoeff φ != 0) :
    invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  rfl

@[simp]
/--
theorem `invOfUnit_eq'` / 定理 `invOfUnit_eq'`

English:
theorem invOfUnit_eq'
  given: (φ : MvPowerSeries σ k) (u : Units k) (h : constantCoeff φ = u)
  proof: by
  rw [← invOfUnit_eq φ (h.symm ▸ u.ne_zero)]
  apply congrArg (invOfUnit φ)
  rw [Units.ext_iff]
  exact h.symm

@[simp]

中文:
定理 invOfUnit_eq'
  条件: (φ : MvPowerSeries σ k) (u : 单位群 k) (h : constantCoeff φ = u)
  证明: by
  rw [← invOfUnit_eq φ (h.symm ▸ u.ne_zero)]
  apply congrArg (invOfUnit φ)
  rw [Units.ext_iff]
  exact h.symm

@[simp]

Depends on / 依赖: Units.ext_iff, ext_iff, h.symm, invOfUnit, invOfUnit_eq, ne_zero, u.ne_zero
-/
theorem invOfUnit_eq' (φ : MvPowerSeries σ k) (u : Units k) (h : constantCoeff φ = u) :
    invOfUnit φ u = φ⁻¹ := by
  rw [← invOfUnit_eq φ (h.symm ▸ u.ne_zero)]
  apply congrArg (invOfUnit φ)
  rw [Units.ext_iff]
  exact h.symm

@[simp]
/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  given: (φ : MvPowerSeries σ k) (h : constantCoeff φ != 0)
  proof: by rw [← invOfUnit_eq φ h, mul_invOfUnit φ (Units.mk0 _ h) rfl]

@[simp]

中文:
定理 mul_inv_cancel
  条件: (φ : MvPowerSeries σ k) (h : constantCoeff φ != 0)
  证明: by rw [← invOfUnit_eq φ h, mul_invOfUnit φ (Units.mk0 _ h) rfl]

@[simp]
-/
protected theorem mul_inv_cancel (φ : MvPowerSeries σ k) (h : constantCoeff φ != 0) :
    φ * φ⁻¹ = 1 := by rw [← invOfUnit_eq φ h, mul_invOfUnit φ (Units.mk0 _ h) rfl]

@[simp]
/--
theorem `inv_mul_cancel` / 定理 `inv_mul_cancel`

English:
theorem inv_mul_cancel
  given: (φ : MvPowerSeries σ k) (h : constantCoeff φ != 0)
  proof: by rw [mul_comm, φ.mul_inv_cancel h]

中文:
定理 inv_mul_cancel
  条件: (φ : MvPowerSeries σ k) (h : constantCoeff φ != 0)
  证明: by rw [mul_comm, φ.mul_inv_cancel h]
-/
protected theorem inv_mul_cancel (φ : MvPowerSeries σ k) (h : constantCoeff φ != 0) :
    φ⁻¹ * φ = 1 := by rw [mul_comm, φ.mul_inv_cancel h]

/--
theorem `eq_mul_inv_iff_mul_eq` / 定理 `eq_mul_inv_iff_mul_eq`

English:
theorem eq_mul_inv_iff_mul_eq
  statement: {φ₁ φ₂ φ₃ : MvPowerSeries σ k}
  proof: ⟨fun k => by simp [k, mul_assoc, MvPowerSeries.inv_mul_cancel _ h], fun k => by
    simp [← k, mul_assoc, MvPowerSeries.mul_inv_cancel _ h]⟩

中文:
定理 eq_mul_inv_iff_mul_eq
  结论: {φ₁ φ₂ φ₃ : MvPowerSeries σ k}
  证明: ⟨fun k => by simp [k, mul_assoc, MvPowerSeries.inv_mul_cancel _ h], fun k => by
    simp [← k, mul_assoc, MvPowerSeries.mul_inv_cancel _ h]⟩
-/
protected theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : MvPowerSeries σ k}
    (h : constantCoeff φ₃ != 0) : φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
  ⟨fun k => by simp [k, mul_assoc, MvPowerSeries.inv_mul_cancel _ h], fun k => by
    simp [← k, mul_assoc, MvPowerSeries.mul_inv_cancel _ h]⟩

/--
theorem `eq_inv_iff_mul_eq_one` / 定理 `eq_inv_iff_mul_eq_one`

English:
theorem eq_inv_iff_mul_eq_one
  given: {φ ψ : MvPowerSeries σ k} (h : constantCoeff ψ != 0)
  proof: by rw [← MvPowerSeries.eq_mul_inv_iff_mul_eq h, one_mul]

中文:
定理 eq_inv_iff_mul_eq_one
  条件: {φ ψ : MvPowerSeries σ k} (h : constantCoeff ψ != 0)
  证明: by rw [← MvPowerSeries.eq_mul_inv_iff_mul_eq h, one_mul]
-/
protected theorem eq_inv_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constantCoeff ψ != 0) :
    φ = ψ⁻¹ ↔ φ * ψ = 1 := by rw [← MvPowerSeries.eq_mul_inv_iff_mul_eq h, one_mul]

/--
theorem `inv_eq_iff_mul_eq_one` / 定理 `inv_eq_iff_mul_eq_one`

English:
theorem inv_eq_iff_mul_eq_one
  given: {φ ψ : MvPowerSeries σ k} (h : constantCoeff ψ != 0)
  proof: by rw [eq_comm, MvPowerSeries.eq_inv_iff_mul_eq_one h]

@[simp]

中文:
定理 inv_eq_iff_mul_eq_one
  条件: {φ ψ : MvPowerSeries σ k} (h : constantCoeff ψ != 0)
  证明: by rw [eq_comm, MvPowerSeries.eq_inv_iff_mul_eq_one h]

@[simp]
-/
protected theorem inv_eq_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constantCoeff ψ != 0) :
    ψ⁻¹ = φ ↔ φ * ψ = 1 := by rw [eq_comm, MvPowerSeries.eq_inv_iff_mul_eq_one h]

@[simp]
/--
theorem `mul_inv_rev` / 定理 `mul_inv_rev`

English:
theorem mul_inv_rev
  given: (φ ψ : MvPowerSeries σ k)
  proof: by
  by_cases h : constantCoeff (φ * ψ) = 0
  · rw [inv_eq_zero.mpr h]
    simp only [map_mul, mul_eq_zero] at h
    -- we don't have `NoZeroDivisors (MvPowerSeries σ k)` yet,
    rcases h with h | h <;> simp [inv_eq_zero.mpr h]
  · rw [MvPowerSeries.inv_eq_iff_mul_eq_one h]
    simp only [not_or, map_mul, mul_eq_zero] at h
    rw [← mul_assoc]; rw [mul_assoc _⁻¹]; rw [MvPowerSeries.inv_mul_cancel _ h.left]; rw [mul_one]; rw [MvPowerSeries.inv_mul_cancel _ h.right]

中文:
定理 mul_inv_rev
  条件: (φ ψ : MvPowerSeries σ k)
  证明: by
  by_cases h : constantCoeff (φ * ψ) = 0
  · rw [inv_eq_zero.mpr h]
    simp only [map_mul, mul_eq_zero] at h
    -- we don't have `NoZeroDivisors (MvPowerSeries σ k)` yet,
    rcases h with h | h <;> simp [inv_eq_zero.mpr h]
  · rw [MvPowerSeries.inv_eq_iff_mul_eq_one h]
    simp only [not_or, map_mul, mul_eq_zero] at h
    rw [← mul_assoc]; rw [mul_assoc _⁻¹]; rw [MvPowerSeries.inv_mul_cancel _ h.left]; rw [mul_one]; rw [MvPowerSeries.inv_mul_cancel _ h.right]
-/
protected theorem mul_inv_rev (φ ψ : MvPowerSeries σ k) :
    (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹ := by
  by_cases h : constantCoeff (φ * ψ) = 0
  · rw [inv_eq_zero.mpr h]
    simp only [map_mul, mul_eq_zero] at h
    -- we don't have `NoZeroDivisors (MvPowerSeries σ k)` yet,
    rcases h with h | h <;> simp [inv_eq_zero.mpr h]
  · rw [MvPowerSeries.inv_eq_iff_mul_eq_one h]
    simp only [not_or, map_mul, mul_eq_zero] at h
    rw [← mul_assoc]; rw [mul_assoc _⁻¹]; rw [MvPowerSeries.inv_mul_cancel _ h.left]; rw [mul_one]; rw [MvPowerSeries.inv_mul_cancel _ h.right]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvOneClass (MvPowerSeries σ k)
  body: { (inferInstance : One (MvPowerSeries σ k)),
    (inferInstance : Inv (MvPowerSeries σ k)) with
    inv_one := by
      rw [MvPowerSeries.inv_eq_iff_mul_eq_one]; rw [mul_one]
      simp }

@[simp]

中文:
实例 :
  签名: InvOne类 (MvPowerSeries σ k)
  定义体: { (inferInstance : One (MvPowerSeries σ k)),
    (inferInstance : Inv (MvPowerSeries σ k)) with
    inv_one := by
      rw [MvPowerSeries.inv_eq_iff_mul_eq_one]; rw [mul_one]
      simp }

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.inv_eq_iff_mul_eq_one, inv_eq_iff_mul_eq_one, inv_one, mul_one
-/
instance : InvOneClass (MvPowerSeries σ k) :=
  { (inferInstance : One (MvPowerSeries σ k)),
    (inferInstance : Inv (MvPowerSeries σ k)) with
    inv_one := by
      rw [MvPowerSeries.inv_eq_iff_mul_eq_one]; rw [mul_one]
      simp }

@[simp]
/--
theorem `C_inv` / 定理 `C_inv`

English:
theorem C_inv
  given: (r : k)
  statement: (C (σ := σ) r)⁻¹ = C r⁻¹
  proof: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one]; rw [← map_mul]; rw [inv_mul_cancel₀ hr]; rw [map_one]
  simpa using hr

@[simp]

中文:
定理 C_inv
  条件: (r : k)
  结论: (C (σ := σ) r)⁻¹ = C r⁻¹
  证明: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one]; rw [← map_mul]; rw [inv_mul_cancel₀ hr]; rw [map_one]
  simpa using hr

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.inv_eq_iff_mul_eq_one, eq_or_ne, inv_eq_iff_mul_eq_one, map_mul, map_one
-/
theorem C_inv (r : k) : (C (σ := σ) r)⁻¹ = C r⁻¹ := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one]; rw [← map_mul]; rw [inv_mul_cancel₀ hr]; rw [map_one]
  simpa using hr

@[simp]
/--
theorem `X_inv` / 定理 `X_inv`

English:
theorem X_inv
  given: (s : σ)
  statement: (X s : MvPowerSeries σ k)⁻¹ = 0
  proof: by
  rw [inv_eq_zero]; rw [constantCoeff_X]

@[simp]

中文:
定理 X_inv
  条件: (s : σ)
  结论: (X s : MvPowerSeries σ k)⁻¹ = 0
  证明: by
  rw [inv_eq_zero]; rw [constantCoeff_X]

@[simp]

Depends on / 依赖: constantCoeff_X, inv_eq_zero
-/
theorem X_inv (s : σ) : (X s : MvPowerSeries σ k)⁻¹ = 0 := by
  rw [inv_eq_zero]; rw [constantCoeff_X]

@[simp]
/--
theorem `smul_inv` / 定理 `smul_inv`

English:
theorem smul_inv
  given: (r : k) (φ : MvPowerSeries σ k)
  statement: (r • φ)⁻¹ = r⁻¹ • φ⁻¹
  proof: by
  simp [smul_eq_C_mul, mul_comm]

中文:
定理 smul_inv
  条件: (r : k) (φ : MvPowerSeries σ k)
  结论: (r • φ)⁻¹ = r⁻¹ • φ⁻¹
  证明: by
  simp [smul_eq_C_mul, mul_comm]

Depends on / 依赖: mul_comm, smul_eq_C_mul
-/
theorem smul_inv (r : k) (φ : MvPowerSeries σ k) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹ := by
  simp [smul_eq_C_mul, mul_comm]

end Field

end MvPowerSeries

end
