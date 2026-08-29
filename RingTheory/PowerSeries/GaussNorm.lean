/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.GaussNorm

/-!
# Gauss norm for power series

This file defines the Gauss norm for power series using the gaussNorm for multivariate power series.
Given a power series `f` in `R⟦X⟧`, a function `v : R → ℝ` and a real number `c`, the Gauss norm is
defined as the supremum of the set of all values of `v (f.coeff i) * c ^ i` for all `i : ℕ`.

In case `f` is a polynomial, `v` is a non-negative function with `v 0 = 0` and `c ≥ 0`,
`f.gaussNorm v c` reduces to the Gauss norm defined in
`Mathlib/RingTheory/Polynomial/GaussNorm.lean`, see `Polynomial.gaussNorm_coe_powerSeries`.

## Main Definitions and Results
* Using `PowerSeries.gaussNorm_eq`, `PowerSeries.gaussNorm` is the supremum of the set of all values
  of `v (f.coeff i) * c ^ i` for all `i : ℕ`, where `f` is a power series in `R⟦X⟧`, `v : R → ℝ` is
  a function and `c` is a real number.

* `PowerSeries.gaussNorm_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.

* `PowerSeries.gaussNorm_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0` for
  all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series is
  zero.

* `PowerSeries.gaussNormC_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0`
  for all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series
  is zero.

* `PowerSeries.gaussNorm_add_le_max`: if `v` is a non-negative non-archimedean function and the
  set of values `v (coeff t f) * c ^ t` is bounded above (similarly for `g`), then
  the Gauss norm has the non-archimedean property.
-/

public section

namespace PowerSeries

variable {R : Type*} [Semiring R] (v : R -> Real) (c : Real) (f : PowerSeries R)

/-- Given a power series `f` in, a function `v : R → ℝ` and a real number `c`, the Gauss norm is
  defined as the supremum of the set of all values of `v (coeff t f) * c ^ t` for all `t : ℕ`. -/
noncomputable
/--
Definition of `gaussNorm` / `gaussNorm` 的定义

English:
abbreviation gaussNorm
  signature: : Real
  body: MvPowerSeries.gaussNorm v (fun _ => c) f

中文:
缩写 gaussNorm
  签名: : 实数
  定义体: MvPowerSeries.gaussNorm v (fun _ => c) f

Depends on / 依赖: MvPowerSeries, MvPowerSeries.gaussNorm, gaussNorm
-/
abbrev gaussNorm : Real := MvPowerSeries.gaussNorm v (fun _ => c) f

/--
lemma `gaussNorm_eq` / 引理 `gaussNorm_eq`

English:
lemma gaussNorm_eq
  statement: gaussNorm v c f = ⨆ i : Nat, v (f.coeff i) * c ^ i
  proof: by
  refine Equiv.iSup_congr (Finsupp.uniqueEquiv ()) ?_
  intro x
  simp only [coeff, Finsupp.uniqueEquiv_apply, PUnit.default_eq_unit, Finsupp.prod_pow,
    Finset.univ_unique, Finset.prod_singleton, show (Finsupp.single () (x PUnit.unit)) = x by grind]

中文:
引理 gaussNorm_eq
  结论: gaussNorm v c f = ⨆ i : 自然数, v (f.coeff i) * c ^ i
  证明: by
  refine Equiv.iSup_congr (Finsupp.uniqueEquiv ()) ?_
  intro x
  simp only [coeff, Finsupp.uniqueEquiv_apply, PUnit.default_eq_unit, Finsupp.prod_pow,
    Finset.univ_unique, Finset.prod_singleton, show (Finsupp.single () (x PUnit.unit)) = x by grind]

Depends on / 依赖: Equiv.iSup_congr, Finset, Finset.prod_singleton, Finset.univ_unique, Finsupp, Finsupp.prod_pow, Finsupp.single, Finsupp.uniqueEquiv, Finsupp.uniqueEquiv_apply, PUnit.default_eq_unit, PUnit.unit, default_eq_unit, iSup_congr, prod_pow, prod_singleton, single, uniqueEquiv, uniqueEquiv_apply, univ_unique
-/
lemma gaussNorm_eq : gaussNorm v c f = ⨆ i : Nat, v (f.coeff i) * c ^ i := by
  refine Equiv.iSup_congr (Finsupp.uniqueEquiv ()) ?_
  intro x
  simp only [coeff, Finsupp.uniqueEquiv_apply, PUnit.default_eq_unit, Finsupp.prod_pow,
    Finset.univ_unique, Finset.prod_singleton, show (Finsupp.single () (x PUnit.unit)) = x by grind]

/--
Definition of `HasGaussNorm` / `HasGaussNorm` 的定义

English:
abbreviation HasGaussNorm
  body: BddAbove (Set.range (fun (t : Nat) => (v (coeff t f) * c ^ t)))

中文:
缩写 HasGaussNorm
  定义体: BddAbove (Set.range (fun (t : Nat) => (v (coeff t f) * c ^ t)))

Depends on / 依赖: BddAbove, Set.range
-/
abbrev HasGaussNorm := BddAbove (Set.range (fun (t : Nat) => (v (coeff t f) * c ^ t)))

/--
lemma `HasGaussNorm.hasMvGaussNorm` / 引理 `HasGaussNorm.hasMvGaussNorm`

English:
lemma HasGaussNorm.hasMvGaussNorm
  given: (h : HasGaussNorm v c f)
  proof: by
  suffices (Set.range (fun (t : Nat) => (v (coeff t f) * c ^ t))) =
      Set.range fun t => v ((MvPowerSeries.coeff t) f) * t.prod fun _ x2 => c ^ x2 by
    simpa only [MvPowerSeries.HasGaussNorm, ← this]
  refine Set.ext (fun _ => ?_)
  simp only [Set.mem_range, Finsupp.prod_pow, Finset.univ_un

中文:
引理 HasGaussNorm.hasMvGaussNorm
  条件: (h : HasGaussNorm v c f)
  证明: by
  suffices (Set.range (fun (t : Nat) => (v (coeff t f) * c ^ t))) =
      Set.range fun t => v ((MvPowerSeries.coeff t) f) * t.prod fun _ x2 => c ^ x2 by
    simpa only [MvPowerSeries.HasGaussNorm, ← this]
  refine Set.ext (fun _ => ?_)
  simp only [Set.mem_range, Finsupp.prod_pow, Finset.univ_un

Depends on / 依赖: Finset, Finset.prod_singleton, Finset.univ_unique, Finsupp, Finsupp.prod_pow, Finsupp.uniqueEquiv, HasGaussNorm, MvPowerSeries, MvPowerSeries.HasGaussNorm, MvPowerSeries.coeff, PUnit.default_eq_unit, Set.ext, Set.mem_range, Set.range, default_eq_unit, mem_range, prod_pow, prod_singleton, t.prod, uniqueEquiv
-/
lemma HasGaussNorm.hasMvGaussNorm (h : HasGaussNorm v c f) :
    MvPowerSeries.HasGaussNorm v (fun _ => c) f := by
  suffices (Set.range (fun (t : Nat) => (v (coeff t f) * c ^ t))) =
      Set.range fun t => v ((MvPowerSeries.coeff t) f) * t.prod fun _ x2 => c ^ x2 by
    simpa only [MvPowerSeries.HasGaussNorm, ← this]
  refine Set.ext (fun _ => ?_)
  simp only [Set.mem_range, Finsupp.prod_pow, Finset.univ_unique, PUnit.default_eq_unit,
    Finset.prod_singleton]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h
    use (Finsupp.uniqueEquiv ()).symm y
    simpa [coeff] using hy
  · intro h
    obtain ⟨y, hy⟩ := h
    use Finsupp.uniqueEquiv () y
    simpa [coeff, show (Finsupp.single () (y PUnit.unit)) = y by grind]

@[deprecated (since := "2026-05-06")]
alias HasGaussNorm.HasMvGaussNorm := HasGaussNorm.hasMvGaussNorm

/--
theorem `gaussNorm_zero` / 定理 `gaussNorm_zero`

English:
theorem gaussNorm_zero
  given: (vZero : v 0 = 0)
  statement: gaussNorm v c 0 = 0
  proof: MvPowerSeries.gaussNorm_zero v (fun _ => c) vZero

中文:
定理 gaussNorm_zero
  条件: (vZero : v 0 = 0)
  结论: gaussNorm v c 0 = 0
  证明: MvPowerSeries.gaussNorm_zero v (fun _ => c) vZero

Depends on / 依赖: MvPowerSeries, MvPowerSeries.gaussNorm_zero, gaussNorm_zero
-/
theorem gaussNorm_zero (vZero : v 0 = 0) : gaussNorm v c 0 = 0 :=
  MvPowerSeries.gaussNorm_zero v (fun _ => c) vZero

/--
lemma `le_gaussNorm` / 引理 `le_gaussNorm`

English:
lemma le_gaussNorm
  given: (hbd : HasGaussNorm v c f) (t : Nat)
  proof: by
  rw [gaussNorm_eq]
  apply le_ciSup hbd

中文:
引理 le_gaussNorm
  条件: (hbd : HasGaussNorm v c f) (t : 自然数)
  证明: by
  rw [gaussNorm_eq]
  apply le_ciSup hbd

Depends on / 依赖: gaussNorm_eq, le_ciSup
-/
lemma le_gaussNorm (hbd : HasGaussNorm v c f) (t : Nat) :
    v (coeff t f) * c ^ t <= gaussNorm v c f := by
  rw [gaussNorm_eq]
  apply le_ciSup hbd

/--
lemma `gaussNorm_nonneg` / 引理 `gaussNorm_nonneg`

English:
lemma gaussNorm_nonneg
  given: (vNonneg : forall a, v a >= 0)
  statement: 0 <= gaussNorm v c f
  proof: MvPowerSeries.gaussNorm_nonneg v (fun _ => c) f vNonneg

中文:
引理 gaussNorm_nonneg
  条件: (vNonneg : 对任意 a, v a >= 0)
  结论: 0 <= gaussNorm v c f
  证明: MvPowerSeries.gaussNorm_nonneg v (fun _ => c) f vNonneg

Depends on / 依赖: MvPowerSeries, MvPowerSeries.gaussNorm_nonneg, gaussNorm_nonneg, vNonneg
-/
lemma gaussNorm_nonneg (vNonneg : forall a, v a >= 0) : 0 <= gaussNorm v c f :=
  MvPowerSeries.gaussNorm_nonneg v (fun _ => c) f vNonneg

/--
lemma `gaussNorm_eq_zero_iff` / 引理 `gaussNorm_eq_zero_iff`

English:
lemma gaussNorm_eq_zero_iff
  statement: (vZero : v 0 = 0) (vNonneg : forall a, v a >= 0)
  proof: MvPowerSeries.gaussNorm_eq_zero_iff v (fun _ => c) f vZero vNonneg h_eq_zero
    (by grind) hbd.hasMvGaussNorm

中文:
引理 gaussNorm_eq_zero_iff
  结论: (vZero : v 0 = 0) (vNonneg : 对任意 a, v a >= 0)
  证明: MvPowerSeries.gaussNorm_eq_zero_iff v (fun _ => c) f vZero vNonneg h_eq_zero
    (by grind) hbd.hasMvGaussNorm

Depends on / 依赖: MvPowerSeries, MvPowerSeries.gaussNorm_eq_zero_iff, gaussNorm_eq_zero_iff, h_eq_zero, hasMvGaussNorm, hbd.hasMvGaussNorm, vNonneg
-/
lemma gaussNorm_eq_zero_iff (vZero : v 0 = 0) (vNonneg : forall a, v a >= 0)
    (h_eq_zero : forall x : R, v x = 0 -> x = 0) (hc : 0 < c) (hbd : HasGaussNorm v c f) :
    gaussNorm v c f = 0 ↔ f = 0 :=
  MvPowerSeries.gaussNorm_eq_zero_iff v (fun _ => c) f vZero vNonneg h_eq_zero
    (by grind) hbd.hasMvGaussNorm

/--
lemma `gaussNorm_add_le_max` / 引理 `gaussNorm_add_le_max`

English:
lemma gaussNorm_add_le_max
  statement: (g : PowerSeries R) (hc : 0 <= c)
  proof: MvPowerSeries.gaussNorm_add_le_max v (fun _ => c) f g (fun _ => by simp [hc]) vNonneg hv
    hbfd.hasMvGaussNorm hbgd.hasMvGaussNorm

中文:
引理 gaussNorm_add_le_max
  结论: (g : PowerSeries R) (hc : 0 <= c)
  证明: MvPowerSeries.gaussNorm_add_le_max v (fun _ => c) f g (fun _ => by simp [hc]) vNonneg hv
    hbfd.hasMvGaussNorm hbgd.hasMvGaussNorm

Depends on / 依赖: MvPowerSeries, MvPowerSeries.gaussNorm_add_le_max, gaussNorm_add_le_max, hasMvGaussNorm, hbfd.hasMvGaussNorm, hbgd.hasMvGaussNorm, vNonneg
-/
lemma gaussNorm_add_le_max (g : PowerSeries R) (hc : 0 <= c)
    (vNonneg : forall a, v a >= 0) (hv : forall x y, v (x + y) <= max (v x) (v y))
    (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f + g) <= max (gaussNorm v c f) (gaussNorm v c g) :=
  MvPowerSeries.gaussNorm_add_le_max v (fun _ => c) f g (fun _ => by simp [hc]) vNonneg hv
    hbfd.hasMvGaussNorm hbgd.hasMvGaussNorm

end PowerSeries
