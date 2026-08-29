/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.PowerSeries.Order
/-!

# Distinguished polynomial

In this file we define the predicate `Polynomial.IsDistinguishedAt`
and develop the most basic lemmas about it.

-/

public section

open scoped Polynomial
open PowerSeries Ideal Quotient

variable {R : Type*} [CommRing R]

/--
Definition of `Polynomial.IsDistinguishedAt` / `Polynomial.IsDistinguishedAt` 的定义

English:
structure Polynomial.IsDistinguishedAt
  parameters: (f : R[X]) (I : Ideal R)
  extends: f.IsWeaklyEisensteinAt I
  axioms and operations (1):
    - monic : f.Monic

中文:
结构 Polynomial.IsDistinguishedAt
  参数: (f : R[X]) (I : Ideal R)
  继承: f.IsWeaklyEisensteinAt I
  公理与运算 (1 个):
    - monic : f.Monic
-/
structure Polynomial.IsDistinguishedAt (f : R[X]) (I : Ideal R) : Prop
    extends f.IsWeaklyEisensteinAt I where
  monic : f.Monic

namespace Polynomial.IsDistinguishedAt

/--
lemma `mul` / 引理 `mul`

English:
lemma mul
  given: {f f' : R[X]} {I : Ideal R} (hf : f.IsDistinguishedAt I) (hf' : f'.IsDistinguishedAt I)
  proof: ⟨hf.toIsWeaklyEisensteinAt.mul hf'.toIsWeaklyEisensteinAt, hf.monic.mul hf'.monic⟩

中文:
引理 mul
  条件: {f f' : R[X]} {I : Ideal R} (hf : f.IsDistinguishedAt I) (hf' : f'.IsDistinguishedAt I)
  证明: ⟨hf.toIsWeaklyEisensteinAt.mul hf'.toIsWeaklyEisensteinAt, hf.monic.mul hf'.monic⟩

Depends on / 依赖: hf.monic.mul, hf.toIsWeaklyEisensteinAt.mul, toIsWeaklyEisensteinAt
-/
lemma mul {f f' : R[X]} {I : Ideal R} (hf : f.IsDistinguishedAt I) (hf' : f'.IsDistinguishedAt I) :
    (f * f').IsDistinguishedAt I :=
  ⟨hf.toIsWeaklyEisensteinAt.mul hf'.toIsWeaklyEisensteinAt, hf.monic.mul hf'.monic⟩

/--
lemma `map_eq_X_pow` / 引理 `map_eq_X_pow`

English:
lemma map_eq_X_pow
  given: {f : R[X]} {I : Ideal R} (distinguish : f.IsDistinguishedAt I)
  proof: by
  ext i
  by_cases ne : i = f.natDegree
  · simp [ne, distinguish.monic]
  · rcases lt_or_gt_of_ne ne with lt | gt
    · simpa [ne, eq_zero_iff_mem] using (distinguish.mem lt)
    · simp [ne, Polynomial.coeff_eq_zero_of_natDegree_lt gt]

中文:
引理 map_eq_X_pow
  条件: {f : R[X]} {I : Ideal R} (distinguish : f.IsDistinguishedAt I)
  证明: by
  ext i
  by_cases ne : i = f.natDegree
  · simp [ne, distinguish.monic]
  · rcases lt_or_gt_of_ne ne with lt | gt
    · simpa [ne, eq_zero_iff_mem] using (distinguish.mem lt)
    · simp [ne, Polynomial.coeff_eq_zero_of_natDegree_lt gt]

Depends on / 依赖: Polynomial, Polynomial.coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt, distinguish, distinguish.mem, distinguish.monic, eq_zero_iff_mem, f.natDegree, lt_or_gt_of_ne, natDegree
-/
lemma map_eq_X_pow {f : R[X]} {I : Ideal R} (distinguish : f.IsDistinguishedAt I) :
    f.map (Ideal.Quotient.mk I) = Polynomial.X ^ f.natDegree := by
  ext i
  by_cases ne : i = f.natDegree
  · simp [ne, distinguish.monic]
  · rcases lt_or_gt_of_ne ne with lt | gt
    · simpa [ne, eq_zero_iff_mem] using (distinguish.mem lt)
    · simp [ne, Polynomial.coeff_eq_zero_of_natDegree_lt gt]

section degree_eq_order_map

variable {I : Ideal R} (f h : R⟦X⟧) {g : R[X]}

/--
lemma `map_ne_zero_of_eq_mul` / 引理 `map_ne_zero_of_eq_mul`

English:
lemma map_ne_zero_of_eq_mul
  statement: (distinguish : g.IsDistinguishedAt I)
  proof: fun H => by
  have mapf : f.map (Ideal.Quotient.mk I) = (Polynomial.X ^ g.natDegree : (R ⧸ I)[X]) *
      h.map (Ideal.Quotient.mk I) := by
    simp [← map_eq_X_pow distinguish, eq]
  apply_fun PowerSeries.coeff g.natDegree at H
  simp [mapf, PowerSeries.coeff_X_pow_mul', eq_zero_iff_mem, notMem] at

中文:
引理 map_ne_zero_of_eq_mul
  结论: (distinguish : g.IsDistinguishedAt I)
  证明: fun H => by
  have mapf : f.map (Ideal.Quotient.mk I) = (Polynomial.X ^ g.natDegree : (R ⧸ I)[X]) *
      h.map (Ideal.Quotient.mk I) := by
    simp [← map_eq_X_pow distinguish, eq]
  apply_fun PowerSeries.coeff g.natDegree at H
  simp [mapf, PowerSeries.coeff_X_pow_mul', eq_zero_iff_mem, notMem] at

Depends on / 依赖: Ideal.Quotient.mk, Polynomial, Polynomial.X, PowerSeries, PowerSeries.coeff, PowerSeries.coeff_X_pow_mul, Quotient, apply_fun, coeff_X_pow_mul, distinguish, eq_zero_iff_mem, f.map, g.natDegree, h.map, map_eq_X_pow, natDegree, notMem
-/
lemma map_ne_zero_of_eq_mul (distinguish : g.IsDistinguishedAt I)
    (notMem : PowerSeries.constantCoeff h ∉ I) (eq : f = g * h) :
    f.map (Ideal.Quotient.mk I) != 0 := fun H => by
  have mapf : f.map (Ideal.Quotient.mk I) = (Polynomial.X ^ g.natDegree : (R ⧸ I)[X]) *
      h.map (Ideal.Quotient.mk I) := by
    simp [← map_eq_X_pow distinguish, eq]
  apply_fun PowerSeries.coeff g.natDegree at H
  simp [mapf, PowerSeries.coeff_X_pow_mul', eq_zero_iff_mem, notMem] at H

/--
lemma `degree_eq_coe_lift_order_map` / 引理 `degree_eq_coe_lift_order_map`

English:
lemma degree_eq_coe_lift_order_map
  statement: (distinguish : g.IsDistinguishedAt I)
  proof: by
  have : Nontrivial R := _root_.nontrivial_iff.mpr
    ⟨0, PowerSeries.constantCoeff h, ne_of_mem_of_not_mem I.zero_mem notMem⟩
  rw [Polynomial.degree_eq_natDegree distinguish.monic.ne_zero]; rw [Nat.cast_inj]; rw [← ENat.natCast_inj]; rw [ENat.natCast_lift]; rw [Eq.comm]; rw [PowerSeries.order_

中文:
引理 degree_eq_coe_lift_order_map
  结论: (distinguish : g.IsDistinguishedAt I)
  证明: by
  have : Nontrivial R := _root_.nontrivial_iff.mpr
    ⟨0, PowerSeries.constantCoeff h, ne_of_mem_of_not_mem I.zero_mem notMem⟩
  rw [Polynomial.degree_eq_natDegree distinguish.monic.ne_zero]; rw [Nat.cast_inj]; rw [← ENat.natCast_inj]; rw [ENat.natCast_lift]; rw [Eq.comm]; rw [PowerSeries.order_

Depends on / 依赖: ENat.natCast_inj, ENat.natCast_lift, Eq.comm, I.zero_mem, Ideal.Quotient.mk, Nat.cast_inj, Nontrivial, Polynomial, Polynomial.X, Polynomial.degree_eq_natDegree, PowerSeries, PowerSeries.coef, PowerSeries.constantCoeff, PowerSeries.order_eq_nat, Quotient, _root_, _root_.nontrivial_iff.mpr, cast_inj, constantCoeff, degree_eq_natDegree
-/
lemma degree_eq_coe_lift_order_map (distinguish : g.IsDistinguishedAt I)
    (notMem : PowerSeries.constantCoeff h ∉ I) (eq : f = g * h) :
    g.degree = (f.map (Ideal.Quotient.mk I)).order.lift
      (order_finite_iff_ne_zero.2 (distinguish.map_ne_zero_of_eq_mul f h notMem eq)) := by
  have : Nontrivial R := _root_.nontrivial_iff.mpr
    ⟨0, PowerSeries.constantCoeff h, ne_of_mem_of_not_mem I.zero_mem notMem⟩
  rw [Polynomial.degree_eq_natDegree distinguish.monic.ne_zero]; rw [Nat.cast_inj]; rw [← ENat.natCast_inj]; rw [ENat.natCast_lift]; rw [Eq.comm]; rw [PowerSeries.order_eq_nat]
  have mapf : f.map (Ideal.Quotient.mk I) = (Polynomial.X ^ g.natDegree : (R ⧸ I)[X]) *
      h.map (Ideal.Quotient.mk I) := by
    simp [← map_eq_X_pow distinguish, eq]
  constructor
  · simp [mapf, PowerSeries.coeff_X_pow_mul', eq_zero_iff_mem, notMem]
  · intro i hi
    simp [mapf, PowerSeries.coeff_X_pow_mul', hi]

/--
lemma `coe_natDegree_eq_order_map` / 引理 `coe_natDegree_eq_order_map`

English:
lemma coe_natDegree_eq_order_map
  statement: (distinguish : g.IsDistinguishedAt I)
  proof: by
  rw [natDegree]; rw [distinguish.degree_eq_coe_lift_order_map f h notMem eq]
exact ENat.natCast_lift _ order_finite_iff_ne_zero.2
    distinguish.map_ne_zero_of_eq_mul f h notMem eq

中文:
引理 coe_natDegree_eq_order_map
  结论: (distinguish : g.IsDistinguishedAt I)
  证明: by
  rw [natDegree]; rw [distinguish.degree_eq_coe_lift_order_map f h notMem eq]
exact ENat.natCast_lift _ order_finite_iff_ne_zero.2
    distinguish.map_ne_zero_of_eq_mul f h notMem eq

Depends on / 依赖: ENat.natCast_lift, degree_eq_coe_lift_order_map, distinguish, distinguish.degree_eq_coe_lift_order_map, distinguish.map_ne_zero_of_eq_mul, map_ne_zero_of_eq_mul, natCast_lift, natDegree, notMem, order_finite_iff_ne_zero
-/
lemma coe_natDegree_eq_order_map (distinguish : g.IsDistinguishedAt I)
    (notMem : PowerSeries.constantCoeff h ∉ I) (eq : f = g * h) :
    g.natDegree = (f.map (Ideal.Quotient.mk I)).order := by
  rw [natDegree]; rw [distinguish.degree_eq_coe_lift_order_map f h notMem eq]
exact ENat.natCast_lift _ order_finite_iff_ne_zero.2
    distinguish.map_ne_zero_of_eq_mul f h notMem eq

end degree_eq_order_map

end Polynomial.IsDistinguishedAt
