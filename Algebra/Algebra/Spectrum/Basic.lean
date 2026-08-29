/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Star.Pointwise
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.Tactic.NoncommRing

/-!
# Spectrum of an element in an algebra

This file develops the basic theory of the spectrum of an element of an algebra.
This theory will serve as the foundation for spectral theory in Banach algebras.

## Main definitions

* `resolventSet a : Set R`: the resolvent set of an element `a : A` where
  `A` is an `R`-algebra.
* `spectrum a : Set R`: the spectrum of an element `a : A` where
  `A` is an `R`-algebra.
* `resolvent : R → A`: the resolvent function is `fun r ↦ (↑ₐ r - a)⁻¹ʳ`, and hence
  when `r ∈ resolvent R A`, it is actually the inverse of the unit `(↑ₐ r - a)`.

## Main statements

* `spectrum.unit_smul_eq_smul` and `spectrum.smul_eq_smul`: units in the scalar ring commute
  (multiplication) with the spectrum, and over a field even `0` commutes with the spectrum.
* `spectrum.left_add_coset_eq`: elements of the scalar ring commute (addition) with the spectrum.
* `spectrum.unit_mem_mul_comm` and `spectrum.preimage_units_mul_comm`: the
  units (of `R`) in `σ (a*b)` coincide with those in `σ (b*a)`.
* `spectrum.resolvent_sub_resolvent`: the second resolvent identity.
* `spectrum.scalar_eq`: in a nontrivial algebra over a field, the spectrum of a scalar is
  a singleton.

## Notation

* `σ a` : `spectrum R a` of `a : A`
-/

@[expose] public section

open Set

open scoped Pointwise Ring

universe u v

section Defs

variable (R : Type u) {A : Type v}
variable [CommSemiring R] [Ring A] [Algebra R A]

local notation "↑ₐ" => algebraMap R A

-- definition and basic properties
/--
Definition of `resolventSet` / `resolventSet` 的定义

English:
definition resolventSet
  signature: (a : A)
  body: {r : R | IsUnit (↑ₐ r - a)}

中文:
定义 resolventSet
  签名: (a : A)
  定义体: {r : R | IsUnit (↑ₐ r - a)}

Depends on / 依赖: IsUnit
-/
def resolventSet (a : A) : Set R :=
  {r : R | IsUnit (↑ₐ r - a)}

/--
Definition of `spectrum` / `spectrum` 的定义

English:
definition spectrum
  signature: (a : A)
  body: (resolventSet R a)ᶜ

中文:
定义 spectrum
  签名: (a : A)
  定义体: (resolventSet R a)ᶜ

Depends on / 依赖: Algebra, Semiring, Semiring.toNatAlgebra, resolventSet, toNatAlgebra
-/
def spectrum (a : A) : Set R :=
  (resolventSet R a)ᶜ

variable {R}

/--
Definition of `resolvent` / `resolvent` 的定义

English:
definition resolvent
  signature: (a : A) (r : R)
  body: (↑ₐ r - a)⁻¹ʳ

中文:
定义 resolvent
  签名: (a : A) (r : R)
  定义体: (↑ₐ r - a)⁻¹ʳ
-/
noncomputable def resolvent (a : A) (r : R) : A := (↑ₐ r - a)⁻¹ʳ

/-- The unit `1 - r⁻¹ • a` constructed from `r • 1 - a` when the latter is a unit. -/
@[simps]
/--
Definition of `IsUnit.subInvSMul` / `IsUnit.subInvSMul` 的定义

English:
definition IsUnit.subInvSMul
  signature: {r : Rˣ} {s : R} {a : A} (h : IsUnit <| r • ↑ₐ s - a)
  body: ↑ₐ s - r⁻¹ • a
  inv := r • ↑h.unit⁻¹
  val_inv := by rw [mul_smul_comm, ← smul_mul_assoc, smul_sub, smul_inv_smul, h.mul_val_inv]
  inv_val := by rw [smul_mul_assoc, ← mul_smul_comm, smul_sub, smul_inv_smul, h.val_inv_mul]

中文:
定义 IsUnit.subInvSMul
  签名: {r : Rˣ} {s : R} {a : A} (h : IsUnit <| r • ↑ₐ s - a)
  定义体: ↑ₐ s - r⁻¹ • a
  inv := r • ↑h.unit⁻¹
  val_inv := by rw [mul_smul_comm, ← smul_mul_assoc, smul_sub, smul_inv_smul, h.mul_val_inv]
  inv_val := by rw [smul_mul_assoc, ← mul_smul_comm, smul_sub, smul_inv_smul, h.val_inv_mul]
-/
noncomputable def IsUnit.subInvSMul {r : Rˣ} {s : R} {a : A} (h : IsUnit <| r • ↑ₐ s - a) : Aˣ where
  val := ↑ₐ s - r⁻¹ • a
  inv := r • ↑h.unit⁻¹
  val_inv := by rw [mul_smul_comm, ← smul_mul_assoc, smul_sub, smul_inv_smul, h.mul_val_inv]
  inv_val := by rw [smul_mul_assoc, ← mul_smul_comm, smul_sub, smul_inv_smul, h.val_inv_mul]

end Defs

namespace spectrum

section ScalarSemiring

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: {r : R} {a : A}
  statement: r in σ a ↔ ¬IsUnit (↑ₐ r - a)
  proof: Iff.rfl

@[simp]

中文:
定理 mem_iff
  条件: {r : R} {a : A}
  结论: r in σ a ↔ ¬IsUnit (↑ₐ r - a)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Algebra, Iff.rfl, Ring.toIntAlgebra, toIntAlgebra
-/
theorem mem_iff {r : R} {a : A} : r in σ a ↔ ¬IsUnit (↑ₐ r - a) :=
  Iff.rfl

@[simp]
/--
theorem `resolvent_zero_of_mem_spectrum` / 定理 `resolvent_zero_of_mem_spectrum`

English:
theorem resolvent_zero_of_mem_spectrum
  given: {r : R} {a : A} (hr : r in σ a)
  proof: Ring.inverse_non_unit _ (mem_iff.mp hr)

中文:
定理 resolvent_zero_of_mem_spectrum
  条件: {r : R} {a : A} (hr : r in σ a)
  证明: Ring.inverse_non_unit _ (mem_iff.mp hr)

Depends on / 依赖: Ring.inverse_non_unit, inverse_non_unit, mem_iff, mem_iff.mp
-/
theorem resolvent_zero_of_mem_spectrum {r : R} {a : A} (hr : r in σ a) :
    resolvent a r = 0 := Ring.inverse_non_unit _ (mem_iff.mp hr)

/--
theorem `mem_spectrum_iff_resolvent_zero` / 定理 `mem_spectrum_iff_resolvent_zero`

English:
theorem mem_spectrum_iff_resolvent_zero
  given: [Nontrivial A] {r : R} {a : A}
  proof: by
  refine ⟨resolvent_zero_of_mem_spectrum, fun hr => ?_⟩
  simpa [mem_iff, Ring.not_isUnit_iff_inverse_eq_zero]

中文:
定理 mem_spectrum_iff_resolvent_zero
  条件: [Nontrivial A] {r : R} {a : A}
  证明: by
  refine ⟨resolvent_zero_of_mem_spectrum, fun hr => ?_⟩
  simpa [mem_iff, Ring.not_isUnit_iff_inverse_eq_zero]

Depends on / 依赖: Ring.not_isUnit_iff_inverse_eq_zero, mem_iff, not_isUnit_iff_inverse_eq_zero, resolvent_zero_of_mem_spectrum
-/
theorem mem_spectrum_iff_resolvent_zero [Nontrivial A] {r : R} {a : A} :
    r in σ a ↔ resolvent a r = 0 := by
  refine ⟨resolvent_zero_of_mem_spectrum, fun hr => ?_⟩
  simpa [mem_iff, Ring.not_isUnit_iff_inverse_eq_zero]

/--
theorem `notMem_iff` / 定理 `notMem_iff`

English:
theorem notMem_iff
  given: {r : R} {a : A}
  statement: r ∉ σ a ↔ IsUnit (↑ₐ r - a)
  proof: by
  simp [mem_iff]

中文:
定理 notMem_iff
  条件: {r : R} {a : A}
  结论: r ∉ σ a ↔ IsUnit (↑ₐ r - a)
  证明: by
  simp [mem_iff]

Depends on / 依赖: mem_iff
-/
theorem notMem_iff {r : R} {a : A} : r ∉ σ a ↔ IsUnit (↑ₐ r - a) := by
  simp [mem_iff]

variable (R)

/--
theorem `zero_mem_iff` / 定理 `zero_mem_iff`

English:
theorem zero_mem_iff
  given: {a : A}
  statement: (0 : R) in σ a ↔ ¬IsUnit a
  proof: by
  rw [mem_iff]; rw [map_zero]; rw [zero_sub]; rw [IsUnit.neg_iff]

alias ⟨not_isUnit_of_zero_mem, zero_mem⟩ := spectrum.zero_mem_iff

中文:
定理 zero_mem_iff
  条件: {a : A}
  结论: (0 : R) in σ a ↔ ¬IsUnit a
  证明: by
  rw [mem_iff]; rw [map_zero]; rw [zero_sub]; rw [IsUnit.neg_iff]

alias ⟨not_isUnit_of_zero_mem, zero_mem⟩ := spectrum.zero_mem_iff

Depends on / 依赖: IsUnit, IsUnit.neg_iff, map_zero, mem_iff, neg_iff, zero_sub
-/
theorem zero_mem_iff {a : A} : (0 : R) in σ a ↔ ¬IsUnit a := by
  rw [mem_iff]; rw [map_zero]; rw [zero_sub]; rw [IsUnit.neg_iff]

alias ⟨not_isUnit_of_zero_mem, zero_mem⟩ := spectrum.zero_mem_iff

/--
theorem `zero_notMem_iff` / 定理 `zero_notMem_iff`

English:
theorem zero_notMem_iff
  given: {a : A}
  statement: (0 : R) ∉ σ a ↔ IsUnit a
  proof: by
  rw [zero_mem_iff]; rw [Classical.not_not]

alias ⟨isUnit_of_zero_notMem, zero_notMem⟩ := spectrum.zero_notMem_iff

@[simp]

中文:
定理 zero_notMem_iff
  条件: {a : A}
  结论: (0 : R) ∉ σ a ↔ IsUnit a
  证明: by
  rw [zero_mem_iff]; rw [Classical.not_not]

alias ⟨isUnit_of_zero_notMem, zero_notMem⟩ := spectrum.zero_notMem_iff

@[simp]

Depends on / 依赖: Classical, Classical.not_not, not_not, zero_mem_iff
-/
theorem zero_notMem_iff {a : A} : (0 : R) ∉ σ a ↔ IsUnit a := by
  rw [zero_mem_iff]; rw [Classical.not_not]

alias ⟨isUnit_of_zero_notMem, zero_notMem⟩ := spectrum.zero_notMem_iff

@[simp]
/--
lemma `_root_.Units.zero_notMem_spectrum` / 引理 `_root_.Units.zero_notMem_spectrum`

English:
lemma _root_.Units.zero_notMem_spectrum
  given: (a : Aˣ)
  statement: 0 ∉ spectrum R (a : A)
  proof: spectrum.zero_notMem R a.isUnit

中文:
引理 _root_.Units.zero_notMem_spectrum
  条件: (a : Aˣ)
  结论: 0 ∉ spectrum R (a : A)
  证明: spectrum.zero_notMem R a.isUnit

Depends on / 依赖: a.isUnit, isUnit, spectrum, spectrum.zero_notMem, zero_notMem
-/
lemma _root_.Units.zero_notMem_spectrum (a : Aˣ) : 0 ∉ spectrum R (a : A) :=
  spectrum.zero_notMem R a.isUnit

/--
lemma `subset_singleton_zero_compl` / 引理 `subset_singleton_zero_compl`

English:
lemma subset_singleton_zero_compl
  given: {a : A} (ha : IsUnit a)
  statement: spectrum R a subseteq {0}ᶜ
  proof: Set.subset_compl_singleton_iff.mpr spectrum.zero_notMem R ha

中文:
引理 subset_singleton_zero_compl
  条件: {a : A} (ha : IsUnit a)
  结论: spectrum R a subseteq {0}ᶜ
  证明: Set.subset_compl_singleton_iff.mpr spectrum.zero_notMem R ha

Depends on / 依赖: Set.subset_compl_singleton_iff.mpr, spectrum, spectrum.zero_notMem, subset_compl_singleton_iff, zero_notMem
-/
lemma subset_singleton_zero_compl {a : A} (ha : IsUnit a) : spectrum R a subseteq {0}ᶜ :=
Set.subset_compl_singleton_iff.mpr spectrum.zero_notMem R ha

variable {R}

/--
theorem `mem_resolventSet_of_left_right_inverse` / 定理 `mem_resolventSet_of_left_right_inverse`

English:
theorem mem_resolventSet_of_left_right_inverse
  statement: {r : R} {a b c : A} (h₁ : (↑ₐ r - a) * b = 1)
  proof: Units.isUnit ⟨↑ₐ r - a, b, h₁, by rwa [← left_inv_eq_right_inv h₂ h₁]⟩

中文:
定理 mem_resolventSet_of_left_right_inverse
  结论: {r : R} {a b c : A} (h₁ : (↑ₐ r - a) * b = 1)
  证明: Units.isUnit ⟨↑ₐ r - a, b, h₁, by rwa [← left_inv_eq_right_inv h₂ h₁]⟩

Depends on / 依赖: Units.isUnit, isUnit, left_inv_eq_right_inv
-/
theorem mem_resolventSet_of_left_right_inverse {r : R} {a b c : A} (h₁ : (↑ₐ r - a) * b = 1)
    (h₂ : c * (↑ₐ r - a) = 1) : r in resolventSet R a :=
  Units.isUnit ⟨↑ₐ r - a, b, h₁, by rwa [← left_inv_eq_right_inv h₂ h₁]⟩

/--
theorem `mem_resolventSet_iff` / 定理 `mem_resolventSet_iff`

English:
theorem mem_resolventSet_iff
  given: {r : R} {a : A}
  statement: r in resolventSet R a ↔ IsUnit (↑ₐ r - a)
  proof: Iff.rfl

@[simp]

中文:
定理 mem_resolventSet_iff
  条件: {r : R} {a : A}
  结论: r in resolventSet R a ↔ IsUnit (↑ₐ r - a)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_resolventSet_iff {r : R} {a : A} : r in resolventSet R a ↔ IsUnit (↑ₐ r - a) :=
  Iff.rfl

@[simp]
/--
theorem `algebraMap_mem_iff` / 定理 `algebraMap_mem_iff`

English:
theorem algebraMap_mem_iff
  statement: (S : Type*) {R A : Type*} [CommSemiring R] [CommSemiring S]
  proof: by
  simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

protected alias ⟨of_algebraMap_mem, algebraMap_mem⟩ := spectrum.algebraMap_mem_iff

@[simp]

中文:
定理 algebraMap_mem_iff
  结论: (S : 类型) {R A : 类型} [CommSemiring R] [CommSemiring S]
  证明: by
  simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

protected alias ⟨of_algebraMap_mem, algebraMap_mem⟩ := spectrum.algebraMap_mem_iff

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, mem_iff, one_smul, smul_assoc, spectrum, spectrum.mem_iff
-/
theorem algebraMap_mem_iff (S : Type*) {R A : Type*} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} {r : R} :
    algebraMap R S r in spectrum S a ↔ r in spectrum R a := by
  simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

protected alias ⟨of_algebraMap_mem, algebraMap_mem⟩ := spectrum.algebraMap_mem_iff

@[simp]
/--
theorem `preimage_algebraMap` / 定理 `preimage_algebraMap`

English:
theorem preimage_algebraMap
  statement: (S : Type*) {R A : Type*} [CommSemiring R] [CommSemiring S]
  proof: Set.ext fun _ => spectrum.algebraMap_mem_iff _

@[simp]

中文:
定理 preimage_algebraMap
  结论: (S : 类型) {R A : 类型} [CommSemiring R] [CommSemiring S]
  证明: Set.ext fun _ => spectrum.algebraMap_mem_iff _

@[simp]

Depends on / 依赖: Set.ext, algebraMap_mem_iff, spectrum, spectrum.algebraMap_mem_iff
-/
theorem preimage_algebraMap (S : Type*) {R A : Type*} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} :
    algebraMap R S ⁻¹' spectrum S a = spectrum R a :=
  Set.ext fun _ => spectrum.algebraMap_mem_iff _

@[simp]
/--
theorem `resolventSet_of_subsingleton` / 定理 `resolventSet_of_subsingleton`

English:
theorem resolventSet_of_subsingleton
  given: [Subsingleton A] (a : A)
  statement: resolventSet R a = Set.univ
  proof: by
  simp_rw [resolventSet, Subsingleton.elim (algebraMap R A _ - a) 1, isUnit_one, Set.ofPred_true]

@[simp]

中文:
定理 resolventSet_of_subsingleton
  条件: [Subsingleton A] (a : A)
  结论: resolventSet R a = Set.univ
  证明: by
  simp_rw [resolventSet, Subsingleton.elim (algebraMap R A _ - a) 1, isUnit_one, Set.ofPred_true]

@[simp]

Depends on / 依赖: Set.ofPred_true, Subsingleton, Subsingleton.elim, algebraMap, isUnit_one, ofPred_true, resolventSet, simp_rw
-/
theorem resolventSet_of_subsingleton [Subsingleton A] (a : A) : resolventSet R a = Set.univ := by
  simp_rw [resolventSet, Subsingleton.elim (algebraMap R A _ - a) 1, isUnit_one, Set.ofPred_true]

@[simp]
/--
theorem `of_subsingleton` / 定理 `of_subsingleton`

English:
theorem of_subsingleton
  given: [Subsingleton A] (a : A)
  statement: spectrum R a = ∅
  proof: by
  rw [spectrum]; rw [resolventSet_of_subsingleton]; rw [Set.compl_univ]

中文:
定理 of_subsingleton
  条件: [Subsingleton A] (a : A)
  结论: spectrum R a = ∅
  证明: by
  rw [spectrum]; rw [resolventSet_of_subsingleton]; rw [Set.compl_univ]

Depends on / 依赖: Set.compl_univ, compl_univ, resolventSet_of_subsingleton, spectrum
-/
theorem of_subsingleton [Subsingleton A] (a : A) : spectrum R a = ∅ := by
  rw [spectrum]; rw [resolventSet_of_subsingleton]; rw [Set.compl_univ]

/--
theorem `resolvent_eq` / 定理 `resolvent_eq`

English:
theorem resolvent_eq
  given: {a : A} {r : R} (h : r in resolventSet R a)
  statement: resolvent a r = ↑h.unit⁻¹
  proof: Ring.inverse_unit h.unit

中文:
定理 resolvent_eq
  条件: {a : A} {r : R} (h : r in resolventSet R a)
  结论: resolvent a r = ↑h.unit⁻¹
  证明: Ring.inverse_unit h.unit

Depends on / 依赖: Ring.inverse_unit, algebraMap, faithfulSMul_iff_algebraMap_injective, h.unit, injective_int, inverse_unit
-/
theorem resolvent_eq {a : A} {r : R} (h : r in resolventSet R a) : resolvent a r = ↑h.unit⁻¹ :=
  Ring.inverse_unit h.unit

/--
theorem `resolvent_sub_resolvent` / 定理 `resolvent_sub_resolvent`

English:
theorem resolvent_sub_resolvent
  statement: {a b : A} {r : R}
  proof: by
  rw [resolvent_eq ha]; rw [resolvent_eq hb]; rw [Units.eq_mul_inv_iff_mul_eq]; rw [Units.eq_inv_mul_iff_mul_eq]; rw [sub_mul]; rw [Units.inv_mul]; rw [mul_sub]; rw [← mul_assoc]; rw [Units.mul_inv]; rw [one_mul]; rw [mul_one]; rw [hb.unit_spec]; rw [ha.unit_spec]
  abel

中文:
定理 resolvent_sub_resolvent
  结论: {a b : A} {r : R}
  证明: by
  rw [resolvent_eq ha]; rw [resolvent_eq hb]; rw [Units.eq_mul_inv_iff_mul_eq]; rw [Units.eq_inv_mul_iff_mul_eq]; rw [sub_mul]; rw [Units.inv_mul]; rw [mul_sub]; rw [← mul_assoc]; rw [Units.mul_inv]; rw [one_mul]; rw [mul_one]; rw [hb.unit_spec]; rw [ha.unit_spec]
  abel

Depends on / 依赖: Units.eq_inv_mul_iff_mul_eq, Units.eq_mul_inv_iff_mul_eq, Units.inv_mul, Units.mul_inv, eq_inv_mul_iff_mul_eq, eq_mul_inv_iff_mul_eq, ha.unit_spec, hb.unit_spec, inv_mul, mul_assoc, mul_inv, mul_one, mul_sub, one_mul, resolvent_eq, sub_mul, unit_spec
-/
theorem resolvent_sub_resolvent {a b : A} {r : R}
    (ha : r in resolventSet R a) (hb : r in resolventSet R b) :
    resolvent a r - resolvent b r = resolvent a r * (a - b) * resolvent b r := by
  rw [resolvent_eq ha]; rw [resolvent_eq hb]; rw [Units.eq_mul_inv_iff_mul_eq]; rw [Units.eq_inv_mul_iff_mul_eq]; rw [sub_mul]; rw [Units.inv_mul]; rw [mul_sub]; rw [← mul_assoc]; rw [Units.mul_inv]; rw [one_mul]; rw [mul_one]; rw [hb.unit_spec]; rw [ha.unit_spec]
  abel

/--
theorem `units_smul_resolvent` / 定理 `units_smul_resolvent`

English:
theorem units_smul_resolvent
  given: {r : Rˣ} {s : R} {a : A}
  proof: by
  by_cases h : s in spectrum R a
  · rw [mem_iff] at h
    simp only [resolvent, Algebra.algebraMap_eq_smul_one] at *
    rw [smul_assoc]; rw [← smul_sub]
    have h' : ¬IsUnit (r⁻¹ • (s • (1 : A) - a)) := fun hu =>
      h (by simpa only [smul_inv_smul] using IsUnit.smul r hu)
    simp only [Rin

中文:
定理 units_smul_resolvent
  条件: {r : Rˣ} {s : R} {a : A}
  证明: by
  by_cases h : s in spectrum R a
  · rw [mem_iff] at h
    simp only [resolvent, Algebra.algebraMap_eq_smul_one] at *
    rw [smul_assoc]; rw [← smul_sub]
    have h' : ¬IsUnit (r⁻¹ • (s • (1 : A) - a)) := fun hu =>
      h (by simpa only [smul_inv_smul] using IsUnit.smul r hu)
    simp only [Rin

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, IsUnit, IsUnit.smul, Ring.inverse_non_unit, algebraMap, algebraMap_eq_smul_one, inverse_non_unit, mem_iff, notMem_iff, notMem_iff.mp, resolvent, smul_assoc, smul_inv_smul, smul_sub, smul_zero, spectrum
-/
theorem units_smul_resolvent {r : Rˣ} {s : R} {a : A} :
    r • resolvent a (s : R) = resolvent (r⁻¹ • a) (r⁻¹ • s : R) := by
  by_cases h : s in spectrum R a
  · rw [mem_iff] at h
    simp only [resolvent, Algebra.algebraMap_eq_smul_one] at *
    rw [smul_assoc]; rw [← smul_sub]
    have h' : ¬IsUnit (r⁻¹ • (s • (1 : A) - a)) := fun hu =>
      h (by simpa only [smul_inv_smul] using IsUnit.smul r hu)
    simp only [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', smul_zero]
  · simp only [resolvent]
    have h' : IsUnit (r • algebraMap R A (r⁻¹ • s) - a) := by
      simpa [Algebra.algebraMap_eq_smul_one, smul_assoc] using notMem_iff.mp h
    rw [← h'.val_subInvSMul]; rw [← (notMem_iff.mp h).unit_spec]; rw [Ring.inverse_unit]; rw [Ring.inverse_unit]; rw [h'.val_inv_subInvSMul]
    simp only [Algebra.algebraMap_eq_smul_one, smul_assoc, smul_inv_smul]

/--
theorem `units_smul_resolvent_self` / 定理 `units_smul_resolvent_self`

English:
theorem units_smul_resolvent_self
  given: {r : Rˣ} {a : A}
  proof: by
  simpa only [Units.smul_def, smul_eq_mul, Units.inv_mul] using
    @units_smul_resolvent _ _ _ _ _ r r a

中文:
定理 units_smul_resolvent_self
  条件: {r : Rˣ} {a : A}
  证明: by
  simpa only [Units.smul_def, smul_eq_mul, Units.inv_mul] using
    @units_smul_resolvent _ _ _ _ _ r r a

Depends on / 依赖: Units.inv_mul, Units.smul_def, inv_mul, smul_def, smul_eq_mul, units_smul_resolvent
-/
theorem units_smul_resolvent_self {r : Rˣ} {a : A} :
    r • resolvent a (r : R) = resolvent (r⁻¹ • a) (1 : R) := by
  simpa only [Units.smul_def, smul_eq_mul, Units.inv_mul] using
    @units_smul_resolvent _ _ _ _ _ r r a

/--
theorem `isUnit_resolvent` / 定理 `isUnit_resolvent`

English:
theorem isUnit_resolvent
  given: {r : R} {a : A}
  statement: r in resolventSet R a ↔ IsUnit (resolvent a r)
  proof: isUnit_ringInverse.symm

中文:
定理 isUnit_resolvent
  条件: {r : R} {a : A}
  结论: r in resolventSet R a ↔ IsUnit (resolvent a r)
  证明: isUnit_ringInverse.symm

Depends on / 依赖: IsScalarTower, IsScalarTower.to_smulCommClass, SMulCommClass, isUnit_ringInverse, isUnit_ringInverse.symm, to_smulCommClass
-/
theorem isUnit_resolvent {r : R} {a : A} : r in resolventSet R a ↔ IsUnit (resolvent a r) :=
  isUnit_ringInverse.symm

/--
theorem `inv_mem_resolventSet` / 定理 `inv_mem_resolventSet`

English:
theorem inv_mem_resolventSet
  given: {r : Rˣ} {a : Aˣ} (h : (r : R) in resolventSet R (a : A))
  proof: by
  rw [mem_resolventSet_iff]; rw [Algebra.algebraMap_eq_smul_one]; rw [← Units.smul_def] at h ⊢
  rw [IsUnit.smul_sub_iff_sub_inv_smul]; rw [inv_inv]; rw [IsUnit.sub_iff]
  have h₁ : (a : A) * (r • (↑a⁻¹ : A) - 1) = r • (1 : A) - a := by
    rw [mul_sub]; rw [mul_smul_comm]; rw [a.mul_inv]; rw [mu

中文:
定理 inv_mem_resolventSet
  条件: {r : Rˣ} {a : Aˣ} (h : (r : R) in resolventSet R (a : A))
  证明: by
  rw [mem_resolventSet_iff]; rw [Algebra.algebraMap_eq_smul_one]; rw [← Units.smul_def] at h ⊢
  rw [IsUnit.smul_sub_iff_sub_inv_smul]; rw [inv_inv]; rw [IsUnit.sub_iff]
  have h₁ : (a : A) * (r • (↑a⁻¹ : A) - 1) = r • (1 : A) - a := by
    rw [mul_sub]; rw [mul_smul_comm]; rw [a.mul_inv]; rw [mu

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Commute, IsScalarTower, IsScalarTower.to_smulCommClass, IsUnit, IsUnit.smul_sub_iff_sub_inv_smul, IsUnit.sub_iff, SMulCommClass, Units.smul_def, a.inv_mul, a.mul_inv, algebraMap_eq_smul_one, inv_inv, inv_mul, mem_resolventSet_iff, mul_inv, mul_one, mul_smul_comm, mul_sub
-/
theorem inv_mem_resolventSet {r : Rˣ} {a : Aˣ} (h : (r : R) in resolventSet R (a : A)) :
    (↑r⁻¹ : R) in resolventSet R (↑a⁻¹ : A) := by
  rw [mem_resolventSet_iff]; rw [Algebra.algebraMap_eq_smul_one]; rw [← Units.smul_def] at h ⊢
  rw [IsUnit.smul_sub_iff_sub_inv_smul]; rw [inv_inv]; rw [IsUnit.sub_iff]
  have h₁ : (a : A) * (r • (↑a⁻¹ : A) - 1) = r • (1 : A) - a := by
    rw [mul_sub]; rw [mul_smul_comm]; rw [a.mul_inv]; rw [mul_one]
  have h₂ : (r • (↑a⁻¹ : A) - 1) * a = r • (1 : A) - a := by
    rw [sub_mul]; rw [smul_mul_assoc]; rw [a.inv_mul]; rw [one_mul]
  have hcomm : Commute (a : A) (r • (↑a⁻¹ : A) - 1) := by rwa [← h₂] at h₁
  exact (hcomm.isUnit_mul_iff.mp (h₁.symm ▸ h)).2

/--
theorem `inv_mem_iff` / 定理 `inv_mem_iff`

English:
theorem inv_mem_iff
  given: {r : Rˣ} {a : Aˣ}
  statement: (r : R) in σ (a : A) ↔ (↑r⁻¹ : R) in σ (↑a⁻¹ : A)
  proof: not_iff_not.2 ⟨inv_mem_resolventSet, inv_mem_resolventSet⟩

中文:
定理 inv_mem_iff
  条件: {r : Rˣ} {a : Aˣ}
  结论: (r : R) in σ (a : A) ↔ (↑r⁻¹ : R) in σ (↑a⁻¹ : A)
  证明: not_iff_not.2 ⟨inv_mem_resolventSet, inv_mem_resolventSet⟩

Depends on / 依赖: Algebra, Algebra.to_smulCommClass, CommSemiring, Semiring, inv_mem_resolventSet, not_iff_not, to_smulCommClass
-/
theorem inv_mem_iff {r : Rˣ} {a : Aˣ} : (r : R) in σ (a : A) ↔ (↑r⁻¹ : R) in σ (↑a⁻¹ : A) :=
not_iff_not.2 ⟨inv_mem_resolventSet, inv_mem_resolventSet⟩

/--
theorem `zero_mem_resolventSet_of_unit` / 定理 `zero_mem_resolventSet_of_unit`

English:
theorem zero_mem_resolventSet_of_unit
  given: (a : Aˣ)
  statement: 0 in resolventSet R (a : A)
  proof: by
  simpa only [mem_resolventSet_iff, ← notMem_iff, zero_notMem_iff] using a.isUnit

中文:
定理 zero_mem_resolventSet_of_unit
  条件: (a : Aˣ)
  结论: 0 in resolventSet R (a : A)
  证明: by
  simpa only [mem_resolventSet_iff, ← notMem_iff, zero_notMem_iff] using a.isUnit

Depends on / 依赖: CommSemiring, Semiring, a.isUnit, isUnit, mem_resolventSet_iff, notMem_iff, zero_notMem_iff
-/
theorem zero_mem_resolventSet_of_unit (a : Aˣ) : 0 in resolventSet R (a : A) := by
  simpa only [mem_resolventSet_iff, ← notMem_iff, zero_notMem_iff] using a.isUnit

/--
theorem `ne_zero_of_mem_of_unit` / 定理 `ne_zero_of_mem_of_unit`

English:
theorem ne_zero_of_mem_of_unit
  given: {a : Aˣ} {r : R} (hr : r in σ (a : A))
  statement: r != 0
  proof: fun hn =>
  (hn ▸ hr) (zero_mem_resolventSet_of_unit a)

中文:
定理 ne_zero_of_mem_of_unit
  条件: {a : Aˣ} {r : R} (hr : r in σ (a : A))
  结论: r != 0
  证明: fun hn =>
  (hn ▸ hr) (zero_mem_resolventSet_of_unit a)
-/
theorem ne_zero_of_mem_of_unit {a : Aˣ} {r : R} (hr : r in σ (a : A)) : r != 0 := fun hn =>
  (hn ▸ hr) (zero_mem_resolventSet_of_unit a)

/--
theorem `add_mem_iff` / 定理 `add_mem_iff`

English:
theorem add_mem_iff
  given: {a : A} {r s : R}
  statement: r + s in σ a ↔ r in σ (-↑ₐ s + a)
  proof: by
  simp only [mem_iff, sub_neg_eq_add, ← sub_sub, map_add]

中文:
定理 add_mem_iff
  条件: {a : A} {r s : R}
  结论: r + s in σ a ↔ r in σ (-↑ₐ s + a)
  证明: by
  simp only [mem_iff, sub_neg_eq_add, ← sub_sub, map_add]

Depends on / 依赖: map_add, mem_iff, sub_neg_eq_add, sub_sub
-/
theorem add_mem_iff {a : A} {r s : R} : r + s in σ a ↔ r in σ (-↑ₐ s + a) := by
  simp only [mem_iff, sub_neg_eq_add, ← sub_sub, map_add]

/--
theorem `add_mem_add_iff` / 定理 `add_mem_add_iff`

English:
theorem add_mem_add_iff
  given: {a : A} {r s : R}
  statement: r + s in σ (↑ₐ s + a) ↔ r in σ a
  proof: by
  rw [add_mem_iff]; rw [neg_add_cancel_left]

中文:
定理 add_mem_add_iff
  条件: {a : A} {r s : R}
  结论: r + s in σ (↑ₐ s + a) ↔ r in σ a
  证明: by
  rw [add_mem_iff]; rw [neg_add_cancel_left]

Depends on / 依赖: add_mem_iff, neg_add_cancel_left
-/
theorem add_mem_add_iff {a : A} {r s : R} : r + s in σ (↑ₐ s + a) ↔ r in σ a := by
  rw [add_mem_iff]; rw [neg_add_cancel_left]

/--
theorem `smul_mem_smul_iff` / 定理 `smul_mem_smul_iff`

English:
theorem smul_mem_smul_iff
  given: {a : A} {s : R} {r : Rˣ}
  statement: r • s in σ (r • a) ↔ s in σ a
  proof: by
  simp only [mem_iff, Algebra.algebraMap_eq_smul_one, smul_assoc, ← smul_sub, isUnit_smul_iff]

中文:
定理 smul_mem_smul_iff
  条件: {a : A} {s : R} {r : Rˣ}
  结论: r • s in σ (r • a) ↔ s in σ a
  证明: by
  simp only [mem_iff, Algebra.algebraMap_eq_smul_one, smul_assoc, ← smul_sub, isUnit_smul_iff]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, isUnit_smul_iff, mem_iff, smul_assoc, smul_sub
-/
theorem smul_mem_smul_iff {a : A} {s : R} {r : Rˣ} : r • s in σ (r • a) ↔ s in σ a := by
  simp only [mem_iff, Algebra.algebraMap_eq_smul_one, smul_assoc, ← smul_sub, isUnit_smul_iff]

/--
theorem `unit_smul_eq_smul` / 定理 `unit_smul_eq_smul`

English:
theorem unit_smul_eq_smul
  given: (a : A) (r : Rˣ)
  statement: σ (r • a) = r • σ a
  proof: by
  ext x
  have x_eq : x = r • r⁻¹ • x := by simp
  nth_rw 1 [x_eq]
  rw [smul_mem_smul_iff]
  constructor
  · exact fun h => ⟨r⁻¹ • x, ⟨h, show r • r⁻¹ • x = x by simp⟩⟩
  · rintro ⟨w, _, (x'_eq : r • w = x)⟩
    simpa [← x'_eq]

中文:
定理 unit_smul_eq_smul
  条件: (a : A) (r : Rˣ)
  结论: σ (r • a) = r • σ a
  证明: by
  ext x
  have x_eq : x = r • r⁻¹ • x := by simp
  nth_rw 1 [x_eq]
  rw [smul_mem_smul_iff]
  constructor
  · exact fun h => ⟨r⁻¹ • x, ⟨h, show r • r⁻¹ • x = x by simp⟩⟩
  · rintro ⟨w, _, (x'_eq : r • w = x)⟩
    simpa [← x'_eq]

Depends on / 依赖: nth_rw, smul_mem_smul_iff, x_eq
-/
theorem unit_smul_eq_smul (a : A) (r : Rˣ) : σ (r • a) = r • σ a := by
  ext x
  have x_eq : x = r • r⁻¹ • x := by simp
  nth_rw 1 [x_eq]
  rw [smul_mem_smul_iff]
  constructor
  · exact fun h => ⟨r⁻¹ • x, ⟨h, show r • r⁻¹ • x = x by simp⟩⟩
  · rintro ⟨w, _, (x'_eq : r • w = x)⟩
    simpa [← x'_eq]

-- `r ∈ σ(a*b) ↔ r ∈ σ(b*a)` for any `r : Rˣ`
/--
theorem `unit_mem_mul_comm` / 定理 `unit_mem_mul_comm`

English:
theorem unit_mem_mul_comm
  given: {a b : A} {r : Rˣ}
  statement: ↑r in σ (a * b) ↔ ↑r in σ (b * a)
  proof: by
  have h₁ : forall x y : A, IsUnit (1 - x * y) -> IsUnit (1 - y * x) := by
    refine fun x y h => ⟨⟨1 - y * x, 1 + y * h.unit.inv * x, ?_, ?_⟩, rfl⟩
    · calc
        (1 - y * x) * (1 + y * (IsUnit.unit h).inv * x) =
            1 - y * x + y * ((1 - x * y) * h.unit.inv) * x := by noncomm_ring


中文:
定理 unit_mem_mul_comm
  条件: {a b : A} {r : Rˣ}
  结论: ↑r in σ (a * b) ↔ ↑r in σ (b * a)
  证明: by
  have h₁ : forall x y : A, IsUnit (1 - x * y) -> IsUnit (1 - y * x) := by
    refine fun x y h => ⟨⟨1 - y * x, 1 + y * h.unit.inv * x, ?_, ?_⟩, rfl⟩
    · calc
        (1 - y * x) * (1 + y * (IsUnit.unit h).inv * x) =
            1 - y * x + y * ((1 - x * y) * h.unit.inv) * x := by noncomm_ring


Depends on / 依赖: IsUnit, IsUnit.mul_val_inv, IsUnit.unit, Units.inv_eq_val_inv, h.unit.inv, inv_eq_val_inv, mul_one, mul_val_inv, noncomm_ring, sub_add_cancel
-/
theorem unit_mem_mul_comm {a b : A} {r : Rˣ} : ↑r in σ (a * b) ↔ ↑r in σ (b * a) := by
  have h₁ : forall x y : A, IsUnit (1 - x * y) -> IsUnit (1 - y * x) := by
    refine fun x y h => ⟨⟨1 - y * x, 1 + y * h.unit.inv * x, ?_, ?_⟩, rfl⟩
    · calc
        (1 - y * x) * (1 + y * (IsUnit.unit h).inv * x) =
            1 - y * x + y * ((1 - x * y) * h.unit.inv) * x := by noncomm_ring
        _ = 1 := by simp only [Units.inv_eq_val_inv, IsUnit.mul_val_inv, mul_one, sub_add_cancel]
    · calc
        (1 + y * (IsUnit.unit h).inv * x) * (1 - y * x) =
            1 - y * x + y * (h.unit.inv * (1 - x * y)) * x := by noncomm_ring
        _ = 1 := by simp only [Units.inv_eq_val_inv, IsUnit.val_inv_mul, mul_one, sub_add_cancel]
  have := Iff.intro (h₁ (r⁻¹ • a) b) (h₁ b (r⁻¹ • a))
  rw [mul_smul_comm r⁻¹ b a] at this
  simpa only [mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one, ← Units.smul_def,
    IsUnit.smul_sub_iff_sub_inv_smul, smul_mul_assoc]

/--
theorem `preimage_units_mul_comm` / 定理 `preimage_units_mul_comm`

English:
theorem preimage_units_mul_comm
  given: (a b : A)
  proof: Set.ext fun _ => unit_mem_mul_comm

中文:
定理 preimage_units_mul_comm
  条件: (a b : A)
  证明: Set.ext fun _ => unit_mem_mul_comm

Depends on / 依赖: FaithfulSMul, FaithfulSMul.to_isTorsionFree, IsCancelMulZero, Nontrivial, Set.ext, to_isTorsionFree, unit_mem_mul_comm
-/
theorem preimage_units_mul_comm (a b : A) :
    ((↑) : Rˣ -> R) ⁻¹' σ (a * b) = (↑) ⁻¹' σ (b * a) :=
  Set.ext fun _ => unit_mem_mul_comm

/--
theorem `setOfPred_isUnit_inter_mul_comm` / 定理 `setOfPred_isUnit_inter_mul_comm`

English:
theorem setOfPred_isUnit_inter_mul_comm
  given: (a b : A)
  proof: by
  ext r
  simpa using fun hr : IsUnit r => unit_mem_mul_comm (r := hr.unit)

@[deprecated (since := "2026-07-09")]
alias setOf_isUnit_inter_mul_comm := setOfPred_isUnit_inter_mul_comm

中文:
定理 setOfPred_isUnit_inter_mul_comm
  条件: (a b : A)
  证明: by
  ext r
  simpa using fun hr : IsUnit r => unit_mem_mul_comm (r := hr.unit)

@[deprecated (since := "2026-07-09")]
alias setOf_isUnit_inter_mul_comm := setOfPred_isUnit_inter_mul_comm

Depends on / 依赖: IsCancelMulZero, IsTorsionFree, IsTorsionFree.to_faithfulSMul, IsUnit, Nontrivial, hr.unit, to_faithfulSMul, unit_mem_mul_comm
-/
theorem setOfPred_isUnit_inter_mul_comm (a b : A) :
    {r | IsUnit r} inter σ (a * b) = {r | IsUnit r} inter σ (b * a) := by
  ext r
  simpa using fun hr : IsUnit r => unit_mem_mul_comm (r := hr.unit)

@[deprecated (since := "2026-07-09")]
alias setOf_isUnit_inter_mul_comm := setOfPred_isUnit_inter_mul_comm

section Star

variable [InvolutiveStar R] [StarRing A] [StarModule R A]

/--
theorem `star_mem_resolventSet_iff` / 定理 `star_mem_resolventSet_iff`

English:
theorem star_mem_resolventSet_iff
  given: {r : R} {a : A}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    simpa only [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, star_sub, star_smul,
      star_star, star_one] using IsUnit.star h

中文:
定理 star_mem_resolventSet_iff
  条件: {r : R} {a : A}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    simpa only [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, star_sub, star_smul,
      star_star, star_one] using IsUnit.star h

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, IsUnit, IsUnit.star, algebraMap_eq_smul_one, mem_resolventSet_iff, star_one, star_smul, star_star, star_sub
-/
theorem star_mem_resolventSet_iff {r : R} {a : A} :
    star r in resolventSet R a ↔ r in resolventSet R (star a) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    simpa only [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, star_sub, star_smul,
      star_star, star_one] using IsUnit.star h

/--
theorem `map_star` / 定理 `map_star`

English:
theorem map_star
  given: (a : A)
  statement: σ (star a) = star (σ a)
  proof: by
  ext
  simpa only [Set.mem_star, mem_iff, not_iff_not] using! star_mem_resolventSet_iff.symm

中文:
定理 map_star
  条件: (a : A)
  结论: σ (star a) = star (σ a)
  证明: by
  ext
  simpa only [Set.mem_star, mem_iff, not_iff_not] using! star_mem_resolventSet_iff.symm
-/
protected theorem map_star (a : A) : σ (star a) = star (σ a) := by
  ext
  simpa only [Set.mem_star, mem_iff, not_iff_not] using! star_mem_resolventSet_iff.symm

end Star

end ScalarSemiring

section ScalarRing

variable {R : Type u} {A : Type v}
variable [CommRing R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

/--
theorem `subset_subalgebra` / 定理 `subset_subalgebra`

English:
theorem subset_subalgebra
  statement: {S R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  proof: Set.compl_subset_compl.mpr fun _ => IsUnit.map (SubalgebraClass.val s)

中文:
定理 subset_subalgebra
  结论: {S R A : 类型} [CommSemiring R] [Ring A] [Algebra R A]
  证明: Set.compl_subset_compl.mpr fun _ => IsUnit.map (SubalgebraClass.val s)

Depends on / 依赖: IsUnit, IsUnit.map, Set.compl_subset_compl.mpr, SubalgebraClass, SubalgebraClass.val, compl_subset_compl
-/
theorem subset_subalgebra {S R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S R A] {s : S} (a : s) :
    spectrum R (a : A) subseteq spectrum R a :=
  Set.compl_subset_compl.mpr fun _ => IsUnit.map (SubalgebraClass.val s)

/--
theorem `singleton_add_eq` / 定理 `singleton_add_eq`

English:
theorem singleton_add_eq
  given: (a : A) (r : R)
  statement: {r} + σ a = σ (↑ₐ r + a)
  proof: ext fun x => by
    rw [singleton_add]; rw [image_add_left]; rw [mem_preimage]; rw [add_comm]; rw [add_mem_iff]; rw [map_neg]; rw [neg_neg]

中文:
定理 singleton_add_eq
  条件: (a : A) (r : R)
  结论: {r} + σ a = σ (↑ₐ r + a)
  证明: ext fun x => by
    rw [singleton_add]; rw [image_add_left]; rw [mem_preimage]; rw [add_comm]; rw [add_mem_iff]; rw [map_neg]; rw [neg_neg]

Depends on / 依赖: add_comm, add_mem_iff, image_add_left, map_neg, mem_preimage, neg_neg, singleton_add
-/
theorem singleton_add_eq (a : A) (r : R) : {r} + σ a = σ (↑ₐ r + a) :=
  ext fun x => by
    rw [singleton_add]; rw [image_add_left]; rw [mem_preimage]; rw [add_comm]; rw [add_mem_iff]; rw [map_neg]; rw [neg_neg]

/--
theorem `add_singleton_eq` / 定理 `add_singleton_eq`

English:
theorem add_singleton_eq
  given: (a : A) (r : R)
  statement: σ a + {r} = σ (a + ↑ₐ r)
  proof: add_comm {r} (σ a) ▸ add_comm (algebraMap R A r) a ▸ singleton_add_eq a r

中文:
定理 add_singleton_eq
  条件: (a : A) (r : R)
  结论: σ a + {r} = σ (a + ↑ₐ r)
  证明: add_comm {r} (σ a) ▸ add_comm (algebraMap R A r) a ▸ singleton_add_eq a r

Depends on / 依赖: add_comm, algebraMap, singleton_add_eq
-/
theorem add_singleton_eq (a : A) (r : R) : σ a + {r} = σ (a + ↑ₐ r) :=
  add_comm {r} (σ a) ▸ add_comm (algebraMap R A r) a ▸ singleton_add_eq a r

/--
theorem `vadd_eq` / 定理 `vadd_eq`

English:
theorem vadd_eq
  given: (a : A) (r : R)
  statement: r +ᵥ σ a = σ (↑ₐ r + a)
  proof: singleton_add.symm.trans singleton_add_eq a r

中文:
定理 vadd_eq
  条件: (a : A) (r : R)
  结论: r +ᵥ σ a = σ (↑ₐ r + a)
  证明: singleton_add.symm.trans singleton_add_eq a r

Depends on / 依赖: singleton_add, singleton_add.symm.trans, singleton_add_eq
-/
theorem vadd_eq (a : A) (r : R) : r +ᵥ σ a = σ (↑ₐ r + a) :=
singleton_add.symm.trans singleton_add_eq a r

/--
theorem `_root_.resolventSet_neg` / 定理 `_root_.resolventSet_neg`

English:
theorem _root_.resolventSet_neg
  given: (a : A)
  statement: resolventSet R (-a) = -resolventSet R a
  proof: Set.ext fun x => by
    simp only [mem_neg, mem_resolventSet_iff, map_neg, ← neg_add', IsUnit.neg_iff, sub_neg_eq_add]

中文:
定理 _root_.resolventSet_neg
  条件: (a : A)
  结论: resolventSet R (-a) = -resolventSet R a
  证明: Set.ext fun x => by
    simp only [mem_neg, mem_resolventSet_iff, map_neg, ← neg_add', IsUnit.neg_iff, sub_neg_eq_add]

Depends on / 依赖: IsUnit, IsUnit.neg_iff, Set.ext, map_neg, mem_neg, mem_resolventSet_iff, neg_add, neg_iff, sub_neg_eq_add
-/
theorem _root_.resolventSet_neg (a : A) : resolventSet R (-a) = -resolventSet R a :=
  Set.ext fun x => by
    simp only [mem_neg, mem_resolventSet_iff, map_neg, ← neg_add', IsUnit.neg_iff, sub_neg_eq_add]

/--
theorem `neg_eq` / 定理 `neg_eq`

English:
theorem neg_eq
  given: (a : A)
  statement: -σ a = σ (-a)
  proof: by
  rw [spectrum]; rw [Set.compl_neg]; rw [spectrum]; rw [resolventSet_neg]

中文:
定理 neg_eq
  条件: (a : A)
  结论: -σ a = σ (-a)
  证明: by
  rw [spectrum]; rw [Set.compl_neg]; rw [spectrum]; rw [resolventSet_neg]

Depends on / 依赖: Set.compl_neg, compl_neg, resolventSet_neg, spectrum
-/
theorem neg_eq (a : A) : -σ a = σ (-a) := by
  rw [spectrum]; rw [Set.compl_neg]; rw [spectrum]; rw [resolventSet_neg]

/--
theorem `singleton_sub_eq` / 定理 `singleton_sub_eq`

English:
theorem singleton_sub_eq
  given: (a : A) (r : R)
  statement: {r} - σ a = σ (↑ₐ r - a)
  proof: by
  rw [sub_eq_add_neg]; rw [neg_eq]; rw [singleton_add_eq]; rw [sub_eq_add_neg]

中文:
定理 singleton_sub_eq
  条件: (a : A) (r : R)
  结论: {r} - σ a = σ (↑ₐ r - a)
  证明: by
  rw [sub_eq_add_neg]; rw [neg_eq]; rw [singleton_add_eq]; rw [sub_eq_add_neg]

Depends on / 依赖: neg_eq, singleton_add_eq, sub_eq_add_neg
-/
theorem singleton_sub_eq (a : A) (r : R) : {r} - σ a = σ (↑ₐ r - a) := by
  rw [sub_eq_add_neg]; rw [neg_eq]; rw [singleton_add_eq]; rw [sub_eq_add_neg]

/--
theorem `sub_singleton_eq` / 定理 `sub_singleton_eq`

English:
theorem sub_singleton_eq
  given: (a : A) (r : R)
  statement: σ a - {r} = σ (a - ↑ₐ r)
  proof: by
  simpa only [neg_sub, neg_eq] using congr_arg Neg.neg (singleton_sub_eq a r)

中文:
定理 sub_singleton_eq
  条件: (a : A) (r : R)
  结论: σ a - {r} = σ (a - ↑ₐ r)
  证明: by
  simpa only [neg_sub, neg_eq] using congr_arg Neg.neg (singleton_sub_eq a r)

Depends on / 依赖: Neg.neg, congr_arg, neg_eq, neg_sub, singleton_sub_eq
-/
theorem sub_singleton_eq (a : A) (r : R) : σ a - {r} = σ (a - ↑ₐ r) := by
  simpa only [neg_sub, neg_eq] using congr_arg Neg.neg (singleton_sub_eq a r)

end ScalarRing

section ScalarSemifield

variable {R : Type u} {A : Type v} [Semifield R] [Ring A] [Algebra R A]

@[simp]
/--
lemma `inv₀_mem_iff` / 引理 `inv₀_mem_iff`

English:
lemma inv₀_mem_iff
  given: {r : R} {a : Aˣ}
  proof: by
  obtain (rfl | hr) := eq_or_ne r 0
  · simp
  · lift r to Rˣ using hr.isUnit
    simp [inv_mem_iff]

中文:
引理 inv₀_mem_iff
  条件: {r : R} {a : Aˣ}
  证明: by
  obtain (rfl | hr) := eq_or_ne r 0
  · simp
  · lift r to Rˣ using hr.isUnit
    simp [inv_mem_iff]

Depends on / 依赖: eq_or_ne, hr.isUnit, inv_mem_iff, isUnit
-/
lemma inv₀_mem_iff {r : R} {a : Aˣ} :
    r⁻¹ in spectrum R (a : A) ↔ r in spectrum R (↑a⁻¹ : A) := by
  obtain (rfl | hr) := eq_or_ne r 0
  · simp
  · lift r to Rˣ using hr.isUnit
    simp [inv_mem_iff]

/--
lemma `inv₀_mem_inv_iff` / 引理 `inv₀_mem_inv_iff`

English:
lemma inv₀_mem_inv_iff
  given: {r : R} {a : Aˣ}
  proof: by
  simp

alias ⟨of_inv₀_mem, inv₀_mem⟩ := inv₀_mem_iff
alias ⟨of_inv₀_mem_inv, inv₀_mem_inv⟩ := inv₀_mem_inv_iff

中文:
引理 inv₀_mem_inv_iff
  条件: {r : R} {a : Aˣ}
  证明: by
  simp

alias ⟨of_inv₀_mem, inv₀_mem⟩ := inv₀_mem_iff
alias ⟨of_inv₀_mem_inv, inv₀_mem_inv⟩ := inv₀_mem_inv_iff
-/
lemma inv₀_mem_inv_iff {r : R} {a : Aˣ} :
    r⁻¹ in spectrum R (↑a⁻¹ : A) ↔ r in spectrum R (a : A) := by
  simp

alias ⟨of_inv₀_mem, inv₀_mem⟩ := inv₀_mem_iff
alias ⟨of_inv₀_mem_inv, inv₀_mem_inv⟩ := inv₀_mem_inv_iff

end ScalarSemifield

section ScalarField

variable {𝕜 : Type u} {A : Type v}
variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

local notation "σ" => spectrum 𝕜

local notation "↑ₐ" => algebraMap 𝕜 A

/-- Without the assumption `Nontrivial A`, then `0 : A` would be invertible. -/
@[simp]
/--
theorem `zero_eq` / 定理 `zero_eq`

English:
theorem zero_eq
  given: [Nontrivial A]
  statement: σ (0 : A) = {0}
  proof: by
  refine Set.Subset.antisymm ?_ (by simp [Algebra.algebraMap_eq_smul_one, mem_iff])
  rw [spectrum]; rw [Set.compl_subset_comm]
  intro k hk
  rw [Set.mem_compl_singleton_iff] at hk
  have : IsUnit (Units.mk0 k hk • (1 : A)) := IsUnit.smul (Units.mk0 k hk) isUnit_one
  simpa [mem_resolventSet_iff

中文:
定理 zero_eq
  条件: [Nontrivial A]
  结论: σ (0 : A) = {0}
  证明: by
  refine Set.Subset.antisymm ?_ (by simp [Algebra.algebraMap_eq_smul_one, mem_iff])
  rw [spectrum]; rw [Set.compl_subset_comm]
  intro k hk
  rw [Set.mem_compl_singleton_iff] at hk
  have : IsUnit (Units.mk0 k hk • (1 : A)) := IsUnit.smul (Units.mk0 k hk) isUnit_one
  simpa [mem_resolventSet_iff

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, IsUnit, IsUnit.smul, Set.Subset.antisymm, Set.compl_subset_comm, Set.mem_compl_singleton_iff, Subset, Units.mk0, algebraMap_eq_smul_one, antisymm, compl_subset_comm, isUnit_one, mem_compl_singleton_iff, mem_iff, mem_resolventSet_iff, spectrum
-/
theorem zero_eq [Nontrivial A] : σ (0 : A) = {0} := by
  refine Set.Subset.antisymm ?_ (by simp [Algebra.algebraMap_eq_smul_one, mem_iff])
  rw [spectrum]; rw [Set.compl_subset_comm]
  intro k hk
  rw [Set.mem_compl_singleton_iff] at hk
  have : IsUnit (Units.mk0 k hk • (1 : A)) := IsUnit.smul (Units.mk0 k hk) isUnit_one
  simpa [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one]

@[simp]
/--
theorem `scalar_eq` / 定理 `scalar_eq`

English:
theorem scalar_eq
  given: [Nontrivial A] (k : 𝕜)
  statement: σ (↑ₐ k) = {k}
  proof: by
  rw [← add_zero (↑ₐ k)]; rw [← singleton_add_eq]; rw [zero_eq]; rw [Set.singleton_add_singleton]; rw [add_zero]

@[simp]

中文:
定理 scalar_eq
  条件: [Nontrivial A] (k : 𝕜)
  结论: σ (↑ₐ k) = {k}
  证明: by
  rw [← add_zero (↑ₐ k)]; rw [← singleton_add_eq]; rw [zero_eq]; rw [Set.singleton_add_singleton]; rw [add_zero]

@[simp]

Depends on / 依赖: Set.singleton_add_singleton, add_zero, singleton_add_eq, singleton_add_singleton, zero_eq
-/
theorem scalar_eq [Nontrivial A] (k : 𝕜) : σ (↑ₐ k) = {k} := by
  rw [← add_zero (↑ₐ k)]; rw [← singleton_add_eq]; rw [zero_eq]; rw [Set.singleton_add_singleton]; rw [add_zero]

@[simp]
/--
theorem `one_eq` / 定理 `one_eq`

English:
theorem one_eq
  given: [Nontrivial A]
  statement: σ (1 : A) = {1}
  proof: calc
    σ (1 : A) = σ (↑ₐ 1) := by rw [Algebra.algebraMap_eq_smul_one, one_smul]
    _ = {1} := scalar_eq 1

中文:
定理 one_eq
  条件: [Nontrivial A]
  结论: σ (1 : A) = {1}
  证明: calc
    σ (1 : A) = σ (↑ₐ 1) := by rw [Algebra.algebraMap_eq_smul_one, one_smul]
    _ = {1} := scalar_eq 1

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, one_smul, scalar_eq
-/
theorem one_eq [Nontrivial A] : σ (1 : A) = {1} :=
  calc
    σ (1 : A) = σ (↑ₐ 1) := by rw [Algebra.algebraMap_eq_smul_one, one_smul]
    _ = {1} := scalar_eq 1

/--
theorem `smul_eq_smul` / 定理 `smul_eq_smul`

English:
theorem smul_eq_smul
  given: [Nontrivial A] (k : 𝕜) (a : A) (ha : (σ a).Nonempty)
  proof: by
  rcases eq_or_ne k 0 with (rfl | h)
  · simpa [ha, zero_smul_set] using (show {(0 : 𝕜)} = (0 : Set 𝕜) from rfl)
  · exact unit_smul_eq_smul a (Units.mk0 k h)

中文:
定理 smul_eq_smul
  条件: [Nontrivial A] (k : 𝕜) (a : A) (ha : (σ a).Nonempty)
  证明: by
  rcases eq_or_ne k 0 with (rfl | h)
  · simpa [ha, zero_smul_set] using (show {(0 : 𝕜)} = (0 : Set 𝕜) from rfl)
  · exact unit_smul_eq_smul a (Units.mk0 k h)

Depends on / 依赖: Units.mk0, eq_or_ne, unit_smul_eq_smul, zero_smul_set
-/
theorem smul_eq_smul [Nontrivial A] (k : 𝕜) (a : A) (ha : (σ a).Nonempty) :
    σ (k • a) = k • σ a := by
  rcases eq_or_ne k 0 with (rfl | h)
  · simpa [ha, zero_smul_set] using (show {(0 : 𝕜)} = (0 : Set 𝕜) from rfl)
  · exact unit_smul_eq_smul a (Units.mk0 k h)

/--
theorem `nonzero_mul_comm` / 定理 `nonzero_mul_comm`

English:
theorem nonzero_mul_comm
  given: (a b : A)
  statement: σ (a * b) \ {0} = σ (b * a) \ {0}
  proof: by
  suffices h : forall x y : A, σ (x * y) \ {0} subseteq σ (y * x) \ {0} from
    Set.eq_of_subset_of_subset (h a b) (h b a)
  rintro _ _ k ⟨k_mem, k_ne⟩
  change ((Units.mk0 k k_ne) : 𝕜) in _ at k_mem
  exact ⟨unit_mem_mul_comm.mp k_mem, k_ne⟩

中文:
定理 nonzero_mul_comm
  条件: (a b : A)
  结论: σ (a * b) \ {0} = σ (b * a) \ {0}
  证明: by
  suffices h : forall x y : A, σ (x * y) \ {0} subseteq σ (y * x) \ {0} from
    Set.eq_of_subset_of_subset (h a b) (h b a)
  rintro _ _ k ⟨k_mem, k_ne⟩
  change ((Units.mk0 k k_ne) : 𝕜) in _ at k_mem
  exact ⟨unit_mem_mul_comm.mp k_mem, k_ne⟩

Depends on / 依赖: Set.eq_of_subset_of_subset, Units.mk0, eq_of_subset_of_subset, k_mem, k_ne, subseteq, unit_mem_mul_comm, unit_mem_mul_comm.mp
-/
theorem nonzero_mul_comm (a b : A) : σ (a * b) \ {0} = σ (b * a) \ {0} := by
  suffices h : forall x y : A, σ (x * y) \ {0} subseteq σ (y * x) \ {0} from
    Set.eq_of_subset_of_subset (h a b) (h b a)
  rintro _ _ k ⟨k_mem, k_ne⟩
  change ((Units.mk0 k k_ne) : 𝕜) in _ at k_mem
  exact ⟨unit_mem_mul_comm.mp k_mem, k_ne⟩

/--
theorem `map_inv` / 定理 `map_inv`

English:
theorem map_inv
  given: (a : Aˣ)
  statement: (σ (a : A))⁻¹ = σ (↑a⁻¹ : A)
  proof: by
  ext
  simp

中文:
定理 map_inv
  条件: (a : Aˣ)
  结论: (σ (a : A))⁻¹ = σ (↑a⁻¹ : A)
  证明: by
  ext
  simp
-/
protected theorem map_inv (a : Aˣ) : (σ (a : A))⁻¹ = σ (↑a⁻¹ : A) := by
  ext
  simp

end ScalarField

end spectrum

namespace AlgHom

section CommSemiring

variable {F R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [FunLike F A B] [AlgHomClass F R A B]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

/--
theorem `mem_resolventSet_apply` / 定理 `mem_resolventSet_apply`

English:
theorem mem_resolventSet_apply
  given: (φ : F) {a : A} {r : R} (h : r in resolventSet R a)
  proof: by
  simpa only [map_sub, AlgHomClass.commutes] using! h.map φ

中文:
定理 mem_resolventSet_apply
  条件: (φ : F) {a : A} {r : R} (h : r in resolventSet R a)
  证明: by
  simpa only [map_sub, AlgHomClass.commutes] using! h.map φ

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, commutes, h.map, map_sub
-/
theorem mem_resolventSet_apply (φ : F) {a : A} {r : R} (h : r in resolventSet R a) :
    r in resolventSet R ((φ : A -> B) a) := by
  simpa only [map_sub, AlgHomClass.commutes] using! h.map φ

/--
theorem `spectrum_apply_subset` / 定理 `spectrum_apply_subset`

English:
theorem spectrum_apply_subset
  given: (φ : F) (a : A)
  statement: σ ((φ : A -> B) a) subseteq σ a
  proof: fun _ =>
  mt (mem_resolventSet_apply φ)

中文:
定理 spectrum_apply_subset
  条件: (φ : F) (a : A)
  结论: σ ((φ : A -> B) a) subseteq σ a
  证明: fun _ =>
  mt (mem_resolventSet_apply φ)
-/
theorem spectrum_apply_subset (φ : F) (a : A) : σ ((φ : A -> B) a) subseteq σ a := fun _ =>
  mt (mem_resolventSet_apply φ)

end CommSemiring

section CommRing

variable {F R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable [FunLike F A R] [AlgHomClass F R A R]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

/--
theorem `apply_mem_spectrum` / 定理 `apply_mem_spectrum`

English:
theorem apply_mem_spectrum
  given: [Nontrivial R] (φ : F) (a : A)
  statement: φ a in σ a
  proof: by
  have h : ↑ₐ (φ a) - a in RingHom.ker (φ : A ->+* R) := by
    simp only [RingHom.mem_ker, map_sub, RingHom.coe_coe, AlgHomClass.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  simp only [spectrum.mem_iff, ← mem_nonunits_iff,
    coe_subset_nonunits (RingHom.ker_ne_top (φ 

中文:
定理 apply_mem_spectrum
  条件: [Nontrivial R] (φ : F) (a : A)
  结论: φ a in σ a
  证明: by
  have h : ↑ₐ (φ a) - a in RingHom.ker (φ : A ->+* R) := by
    simp only [RingHom.mem_ker, map_sub, RingHom.coe_coe, AlgHomClass.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  simp only [spectrum.mem_iff, ← mem_nonunits_iff,
    coe_subset_nonunits (RingHom.ker_ne_top (φ 

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, Algebra, Algebra.algebraMap_self, RingHom, RingHom.coe_coe, RingHom.id_apply, RingHom.ker, RingHom.ker_ne_top, RingHom.mem_ker, algebraMap_self, coe_coe, coe_subset_nonunits, commutes, id_apply, ker_ne_top, map_sub, mem_iff, mem_ker, mem_nonunits_iff
-/
theorem apply_mem_spectrum [Nontrivial R] (φ : F) (a : A) : φ a in σ a := by
  have h : ↑ₐ (φ a) - a in RingHom.ker (φ : A ->+* R) := by
    simp only [RingHom.mem_ker, map_sub, RingHom.coe_coe, AlgHomClass.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  simp only [spectrum.mem_iff, ← mem_nonunits_iff,
    coe_subset_nonunits (RingHom.ker_ne_top (φ : A ->+* R)) h]

end CommRing

end AlgHom

@[simp]
/--
theorem `AlgEquiv.spectrum_eq` / 定理 `AlgEquiv.spectrum_eq`

English:
theorem AlgEquiv.spectrum_eq
  statement: {F R A B : Type*} [CommSemiring R] [Ring A] [Ring B] [Algebra R A]
  proof: Set.Subset.antisymm (AlgHom.spectrum_apply_subset _ _) by
    simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_coe_symm_apply_coe_apply] using
      AlgHom.spectrum_apply_subset (AlgEquivClass.toAlgEquiv f : A ≃ₐ[R] B).symm (f a)

中文:
定理 AlgEquiv.spectrum_eq
  结论: {F R A B : 类型} [CommSemiring R] [Ring A] [Ring B] [Algebra R A]
  证明: Set.Subset.antisymm (AlgHom.spectrum_apply_subset _ _) by
    simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_coe_symm_apply_coe_apply] using
      AlgHom.spectrum_apply_subset (AlgEquivClass.toAlgEquiv f : A ≃ₐ[R] B).symm (f a)

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_coe_symm_apply_coe_apply, AlgEquiv.coe_toAlgHom, AlgEquivClass, AlgEquivClass.toAlgEquiv, AlgHom, AlgHom.spectrum_apply_subset, Set.Subset.antisymm, Subset, antisymm, coe_coe_symm_apply_coe_apply, coe_toAlgHom, spectrum_apply_subset, toAlgEquiv
-/
theorem AlgEquiv.spectrum_eq {F R A B : Type*} [CommSemiring R] [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] (f : F) (a : A) :
    spectrum R (f a) = spectrum R a :=
Set.Subset.antisymm (AlgHom.spectrum_apply_subset _ _) by
    simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_coe_symm_apply_coe_apply] using
      AlgHom.spectrum_apply_subset (AlgEquivClass.toAlgEquiv f : A ≃ₐ[R] B).symm (f a)

section ConjugateUnits

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- Conjugation by a unit preserves the spectrum, inverse on right. -/
@[simp]
/--
lemma `spectrum.units_conjugate` / 引理 `spectrum.units_conjugate`

English:
lemma spectrum.units_conjugate
  given: {a : A} {u : Aˣ}
  proof: by
  suffices forall (b : A) (v : Aˣ), spectrum R (v * b * v⁻¹) subseteq spectrum R b by
    refine le_antisymm (this a u) ?_
apply le_of_eq_of_le ?_ this (u * a * u⁻¹) u⁻¹
    simp [mul_assoc]
  intro a u μ hμ
  rw [spectrum.mem_iff] at hμ ⊢
  contrapose hμ
.mul u⁻¹.isUnit simpa [mul_sub, sub_mul, 

中文:
引理 spectrum.units_conjugate
  条件: {a : A} {u : Aˣ}
  证明: by
  suffices forall (b : A) (v : Aˣ), spectrum R (v * b * v⁻¹) subseteq spectrum R b by
    refine le_antisymm (this a u) ?_
apply le_of_eq_of_le ?_ this (u * a * u⁻¹) u⁻¹
    simp [mul_assoc]
  intro a u μ hμ
  rw [spectrum.mem_iff] at hμ ⊢
  contrapose hμ
.mul u⁻¹.isUnit simpa [mul_sub, sub_mul, 

Depends on / 依赖: Algebra, Algebra.right_comm, contrapose, isUnit, le_antisymm, le_of_eq_of_le, mem_iff, mul_assoc, mul_sub, right_comm, spectrum, spectrum.mem_iff, sub_mul, subseteq, u.isUnit.mul
-/
lemma spectrum.units_conjugate {a : A} {u : Aˣ} :
    spectrum R (u * a * u⁻¹) = spectrum R a := by
  suffices forall (b : A) (v : Aˣ), spectrum R (v * b * v⁻¹) subseteq spectrum R b by
    refine le_antisymm (this a u) ?_
apply le_of_eq_of_le ?_ this (u * a * u⁻¹) u⁻¹
    simp [mul_assoc]
  intro a u μ hμ
  rw [spectrum.mem_iff] at hμ ⊢
  contrapose hμ
.mul u⁻¹.isUnit simpa [mul_sub, sub_mul, Algebra.right_comm] using u.isUnit.mul hμ

/-- Conjugation by a unit preserves the spectrum, inverse on left. -/
@[simp]
/--
lemma `spectrum.units_conjugate'` / 引理 `spectrum.units_conjugate'`

English:
lemma spectrum.units_conjugate'
  given: {a : A} {u : Aˣ}
  proof: by
  simpa using spectrum.units_conjugate (u := u⁻¹)

中文:
引理 spectrum.units_conjugate'
  条件: {a : A} {u : Aˣ}
  证明: by
  simpa using spectrum.units_conjugate (u := u⁻¹)

Depends on / 依赖: spectrum, spectrum.units_conjugate, units_conjugate
-/
lemma spectrum.units_conjugate' {a : A} {u : Aˣ} :
    spectrum R (u⁻¹ * a * u) = spectrum R a := by
  simpa using spectrum.units_conjugate (u := u⁻¹)

end ConjugateUnits
