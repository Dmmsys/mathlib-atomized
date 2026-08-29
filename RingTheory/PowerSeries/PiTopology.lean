/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # Product topology on power series

Let `R` be with `Semiring R` and `TopologicalSpace R`
In this file we define the topology on `PowerSeries σ R`
that corresponds to the simple convergence on its coefficients.
It is the coarsest topology for which all coefficients maps are continuous.

When `R` has `UniformSpace R`, we define the corresponding uniform structure.

This topology can be included by writing `open scoped PowerSeries.WithPiTopology`.

When the type of coefficients has the discrete topology, it corresponds to the topology defined by
[N. Bourbaki, *Algebra II*, Chapter 4, §4, n°2][bourbaki1981].

It corresponds with the adic topology but this is not proved here.

- `PowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpotent`,
  `PowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero`: if the constant
  coefficient of `f` is nilpotent, or vanishes, then `f` is topologically nilpotent.

- `PowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent` :
  assuming the base ring has the discrete topology, `f` is topologically nilpotent iff the constant
  coefficient of `f` is nilpotent.

- `PowerSeries.WithPiTopology.hasSum_of_monomials_self` : viewed as an infinite sum, a power
  series converges to itself.

TODO: add the similar result for the series of homogeneous components.

## Instances

- If `R` is a topological (semi)ring, then so is `PowerSeries σ R`.
- If the topology of `R` is T0 or T2, then so is that of `PowerSeries σ R`.
- If `R` is a `IsUniformAddGroup`, then so is `PowerSeries σ R`.
- If `R` is complete, then so is `PowerSeries σ R`.

-/

public section


namespace PowerSeries

open Filter Function
open scoped MvPowerSeries.WithPiTopology

variable (R : Type*)

section Topological

variable [TopologicalSpace R]

namespace WithPiTopology

open scoped Topology

/-!
The instances defined in this file are copies of instances on `MvPowerSeries`.
Those instances are scoped in `MvPowerSeries.WithPiTopology`,
while these are scoped in `PowerSeries.WithPiTopology`.
It would probably be better to remove these instances, and use one shared scope.
-/

/-- The pointwise topology on `PowerSeries` -/
scoped instance : TopologicalSpace (PowerSeries R) :=
  inferInstance

/-- Separation of the topology on `PowerSeries` -/
@[scoped instance]
/--
theorem `instT0Space` / 定理 `instT0Space`

English:
theorem instT0Space
  given: [T0Space R]
  statement: T0Space (PowerSeries R)
  proof: inferInstance

中文:
定理 instT0Space
  条件: [T0Space R]
  结论: T0Space (PowerSeries R)
  证明: inferInstance
-/
theorem instT0Space [T0Space R] : T0Space (PowerSeries R) :=
  inferInstance

/-- `PowerSeries` on a `T2Space` form a `T2Space` -/
@[scoped instance]
/--
theorem `instT2Space` / 定理 `instT2Space`

English:
theorem instT2Space
  given: [T2Space R]
  statement: T2Space (PowerSeries R)
  proof: inferInstance

中文:
定理 instT2Space
  条件: [T2Space R]
  结论: T2Space (PowerSeries R)
  证明: inferInstance
-/
theorem instT2Space [T2Space R] : T2Space (PowerSeries R) :=
  inferInstance

/--
theorem `continuous_coeff` / 定理 `continuous_coeff`

English:
theorem continuous_coeff
  given: [Semiring R] (d : Nat)
  statement: Continuous (PowerSeries.coeff (R := R) d)
  proof: continuous_pi_iff.mp continuous_id (Finsupp.single () d)

中文:
定理 continuous_coeff
  条件: [Semiring R] (d : 自然数)
  结论: Continuous (PowerSeries.coeff (R := R) d)
  证明: continuous_pi_iff.mp continuous_id (Finsupp.single () d)
-/
theorem continuous_coeff [Semiring R] (d : Nat) : Continuous (PowerSeries.coeff (R := R) d) :=
  continuous_pi_iff.mp continuous_id (Finsupp.single () d)

/--
theorem `continuous_constantCoeff` / 定理 `continuous_constantCoeff`

English:
theorem continuous_constantCoeff
  given: [Semiring R]
  statement: Continuous (constantCoeff (R := R))
  proof: coeff_zero_eq_constantCoeff (R := R) ▸ continuous_coeff R 0

中文:
定理 continuous_constantCoeff
  条件: [Semiring R]
  结论: Continuous (constantCoeff (R := R))
  证明: coeff_zero_eq_constantCoeff (R := R) ▸ continuous_coeff R 0
-/
theorem continuous_constantCoeff [Semiring R] : Continuous (constantCoeff (R := R)) :=
  coeff_zero_eq_constantCoeff (R := R) ▸ continuous_coeff R 0

/--
theorem `tendsto_iff_coeff_tendsto` / 定理 `tendsto_iff_coeff_tendsto`

English:
theorem tendsto_iff_coeff_tendsto
  statement: [Semiring R] {ι : Type*}
  proof: by
  rw [MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  apply (Finsupp.uniqueLinearEquiv Nat Nat ()).toEquiv.forall_congr
  intro d
  simp only [LinearEquiv.coe_toEquiv, Finsupp.uniqueLinearEquiv_apply, coeff]
  apply iff_of_eq
  congr
  · ext _; congr; ext; simp
  · ext; simp

中文:
定理 tendsto_iff_coeff_tendsto
  结论: [Semiring R] {ι : 类型}
  证明: by
  rw [MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  apply (Finsupp.uniqueLinearEquiv Nat Nat ()).toEquiv.forall_congr
  intro d
  simp only [LinearEquiv.coe_toEquiv, Finsupp.uniqueLinearEquiv_apply, coeff]
  apply iff_of_eq
  congr
  · ext _; congr; ext; simp
  · ext; simp

Depends on / 依赖: Finsupp, Finsupp.uniqueLinearEquiv, Finsupp.uniqueLinearEquiv_apply, LinearEquiv, LinearEquiv.coe_toEquiv, MvPowerSeries, MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto, WithPiTopology, coe_toEquiv, forall_congr, iff_of_eq, tendsto_iff_coeff_tendsto, toEquiv, toEquiv.forall_congr, uniqueLinearEquiv, uniqueLinearEquiv_apply
-/
theorem tendsto_iff_coeff_tendsto [Semiring R] {ι : Type*}
    (f : ι -> PowerSeries R) (u : Filter ι) (g : PowerSeries R) :
    Tendsto f u (nhds g) ↔
    forall d : Nat, Tendsto (fun i => coeff d (f i)) u (nhds (coeff d g)) := by
  rw [MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  apply (Finsupp.uniqueLinearEquiv Nat Nat ()).toEquiv.forall_congr
  intro d
  simp only [LinearEquiv.coe_toEquiv, Finsupp.uniqueLinearEquiv_apply, coeff]
  apply iff_of_eq
  congr
  · ext _; congr; ext; simp
  · ext; simp

/--
theorem `tendsto_trunc_atTop` / 定理 `tendsto_trunc_atTop`

English:
theorem tendsto_trunc_atTop
  given: [CommSemiring R] (f : R⟦X⟧)
  proof: by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  exact tendsto_atTop_of_eventually_const fun n (hdn : d < n) => (by simp [coeff_trunc, hdn])

中文:
定理 tendsto_trunc_atTop
  条件: [CommSemiring R] (f : R⟦X⟧)
  证明: by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  exact tendsto_atTop_of_eventually_const fun n (hdn : d < n) => (by simp [coeff_trunc, hdn])

Depends on / 依赖: coeff_trunc, tendsto_atTop_of_eventually_const, tendsto_iff_coeff_tendsto
-/
theorem tendsto_trunc_atTop [CommSemiring R] (f : R⟦X⟧) :
    Tendsto (fun d => (trunc d f : R⟦X⟧)) atTop (𝓝 f) := by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  exact tendsto_atTop_of_eventually_const fun n (hdn : d < n) => (by simp [coeff_trunc, hdn])

/--
theorem `denseRange_toPowerSeries` / 定理 `denseRange_toPowerSeries`

English:
theorem denseRange_toPowerSeries
  given: [CommSemiring R]
  proof: fun f =>
mem_closure_of_tendsto (tendsto_trunc_atTop R f) .of_forall fun _ => Set.mem_range_self _

中文:
定理 denseRange_toPowerSeries
  条件: [CommSemiring R]
  证明: fun f =>
mem_closure_of_tendsto (tendsto_trunc_atTop R f) .of_forall fun _ => Set.mem_range_self _
-/
theorem denseRange_toPowerSeries [CommSemiring R] :
    DenseRange (Polynomial.toPowerSeries (R := R)) := fun f =>
mem_closure_of_tendsto (tendsto_trunc_atTop R f) .of_forall fun _ => Set.mem_range_self _

/-- The semiring topology on `PowerSeries` of a topological semiring -/
@[scoped instance]
/--
theorem `instIsTopologicalSemiring` / 定理 `instIsTopologicalSemiring`

English:
theorem instIsTopologicalSemiring
  given: [Semiring R] [IsTopologicalSemiring R]
  proof: inferInstance

中文:
定理 instIsTopologicalSemiring
  条件: [Semiring R] [IsTopologicalSemiring R]
  证明: inferInstance
-/
theorem instIsTopologicalSemiring [Semiring R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring (PowerSeries R) :=
  inferInstance

/-- The ring topology on `PowerSeries` of a topological ring -/
@[scoped instance]
/--
theorem `instIsTopologicalRing` / 定理 `instIsTopologicalRing`

English:
theorem instIsTopologicalRing
  given: [Ring R] [IsTopologicalRing R]
  proof: inferInstance

中文:
定理 instIsTopologicalRing
  条件: [Ring R] [IsTopologicalRing R]
  证明: inferInstance
-/
theorem instIsTopologicalRing [Ring R] [IsTopologicalRing R] :
    IsTopologicalRing (PowerSeries R) :=
  inferInstance

section Sum
variable [Semiring R] {ι : Type*} {f : ι -> R⟦X⟧}

/--
theorem `hasSum_iff_hasSum_coeff` / 定理 `hasSum_iff_hasSum_coeff`

English:
theorem hasSum_iff_hasSum_coeff
  given: {g : R⟦X⟧}
  proof: by
  simp_rw [HasSum, ← map_sum]
  apply tendsto_iff_coeff_tendsto

中文:
定理 hasSum_iff_hasSum_coeff
  条件: {g : R⟦X⟧}
  证明: by
  simp_rw [HasSum, ← map_sum]
  apply tendsto_iff_coeff_tendsto

Depends on / 依赖: HasSum, map_sum, simp_rw, tendsto_iff_coeff_tendsto
-/
theorem hasSum_iff_hasSum_coeff {g : R⟦X⟧} :
    HasSum f g ↔ forall d, HasSum (fun i => coeff d (f i)) (coeff d g) := by
  simp_rw [HasSum, ← map_sum]
  apply tendsto_iff_coeff_tendsto

/--
theorem `summable_iff_summable_coeff` / 定理 `summable_iff_summable_coeff`

English:
theorem summable_iff_summable_coeff
  proof: by
  simp_rw [Summable, hasSum_iff_hasSum_coeff]
  constructor
  · rintro ⟨a, h⟩ n
    exact ⟨coeff n a, h n⟩
  · intro h
    choose a h using h
    exact ⟨mk a, by simpa using h⟩

中文:
定理 summable_iff_summable_coeff
  证明: by
  simp_rw [Summable, hasSum_iff_hasSum_coeff]
  constructor
  · rintro ⟨a, h⟩ n
    exact ⟨coeff n a, h n⟩
  · intro h
    choose a h using h
    exact ⟨mk a, by simpa using h⟩

Depends on / 依赖: Summable, hasSum_iff_hasSum_coeff, simp_rw
-/
theorem summable_iff_summable_coeff :
    Summable f ↔ forall d : Nat, Summable (fun i => coeff d (f i)) := by
  simp_rw [Summable, hasSum_iff_hasSum_coeff]
  constructor
  · rintro ⟨a, h⟩ n
    exact ⟨coeff n a, h n⟩
  · intro h
    choose a h using h
    exact ⟨mk a, by simpa using h⟩

/--
theorem `summable_of_tendsto_order_atTop_nhds_top` / 定理 `summable_of_tendsto_order_atTop_nhds_top`

English:
theorem summable_of_tendsto_order_atTop_nhds_top
  statement: [LinearOrder ι] [LocallyFiniteOrderBot ι]
  proof: by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply summable_empty
  rw [summable_iff_summable_coeff]
  intro n
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop] at h
  obtain ⟨i, hi⟩ := h n
refine summable_of_hasFiniteSupport (Set.finite_Iic i).subset ?_
  simp_

中文:
定理 summable_of_tendsto_order_atTop_nhds_top
  结论: [LinearOrder ι] [LocallyFiniteOrderBot ι]
  证明: by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply summable_empty
  rw [summable_iff_summable_coeff]
  intro n
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop] at h
  obtain ⟨i, hi⟩ := h n
refine summable_of_hasFiniteSupport (Set.finite_Iic i).subset ?_
  simp_

Depends on / 依赖: ENat.tendsto_nhds_top_iff_natCast_lt, Filter, Filter.eventually_atTop, Function, Function.support_subset_iff, Set.finite_Iic, Set.mem_Iic, coeff_of_lt_order, contrapose, eventually_atTop, finite_Iic, hempty, hk.le, isEmpty_or_nonempty, mem_Iic, simp_rw, subset, summable_empty, summable_iff_summable_coeff, summable_of_hasFiniteSupport
-/
theorem summable_of_tendsto_order_atTop_nhds_top [LinearOrder ι] [LocallyFiniteOrderBot ι]
    (h : Tendsto (fun i => (f i).order) atTop (𝓝 ⊤)) : Summable f := by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply summable_empty
  rw [summable_iff_summable_coeff]
  intro n
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop] at h
  obtain ⟨i, hi⟩ := h n
refine summable_of_hasFiniteSupport (Set.finite_Iic i).subset ?_
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro k hk
  contrapose! hk
exact coeff_of_lt_order _ by simpa using (hi k hk.le)

variable {R} in
/--
theorem `summable_pow_of_constantCoeff_eq_zero` / 定理 `summable_pow_of_constantCoeff_eq_zero`

English:
theorem summable_pow_of_constantCoeff_eq_zero
  given: {f : PowerSeries R} (h : f.constantCoeff = 0)
  proof: MvPowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero h

中文:
定理 summable_pow_of_constantCoeff_eq_zero
  条件: {f : PowerSeries R} (h : f.constantCoeff = 0)
  证明: MvPowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero h

Depends on / 依赖: MvPowerSeries, MvPowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero, WithPiTopology, summable_pow_of_constantCoeff_eq_zero
-/
theorem summable_pow_of_constantCoeff_eq_zero {f : PowerSeries R} (h : f.constantCoeff = 0) :
    Summable (f ^ ·) :=
  MvPowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero h

section GeomSeries
variable {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R] [T2Space R]
variable {f : PowerSeries R}

/--
theorem `tsum_pow_mul_one_sub_of_constantCoeff_eq_zero` / 定理 `tsum_pow_mul_one_sub_of_constantCoeff_eq_zero`

English:
theorem tsum_pow_mul_one_sub_of_constantCoeff_eq_zero
  given: (h : f.constantCoeff = 0)
  proof: (summable_pow_of_constantCoeff_eq_zero h).tsum_pow_mul_one_sub

中文:
定理 tsum_pow_mul_one_sub_of_constantCoeff_eq_zero
  条件: (h : f.constantCoeff = 0)
  证明: (summable_pow_of_constantCoeff_eq_zero h).tsum_pow_mul_one_sub

Depends on / 依赖: summable_pow_of_constantCoeff_eq_zero, tsum_pow_mul_one_sub
-/
theorem tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (h : f.constantCoeff = 0) :
    (∑' (i : Nat), f ^ i) * (1 - f) = 1 :=
  (summable_pow_of_constantCoeff_eq_zero h).tsum_pow_mul_one_sub

/--
theorem `one_sub_mul_tsum_pow_of_constantCoeff_eq_zero` / 定理 `one_sub_mul_tsum_pow_of_constantCoeff_eq_zero`

English:
theorem one_sub_mul_tsum_pow_of_constantCoeff_eq_zero
  given: (h : f.constantCoeff = 0)
  proof: (summable_pow_of_constantCoeff_eq_zero h).one_sub_mul_tsum_pow

中文:
定理 one_sub_mul_tsum_pow_of_constantCoeff_eq_zero
  条件: (h : f.constantCoeff = 0)
  证明: (summable_pow_of_constantCoeff_eq_zero h).one_sub_mul_tsum_pow

Depends on / 依赖: one_sub_mul_tsum_pow, summable_pow_of_constantCoeff_eq_zero
-/
theorem one_sub_mul_tsum_pow_of_constantCoeff_eq_zero (h : f.constantCoeff = 0) :
    (1 - f) * ∑' (i : Nat), f ^ i = 1 :=
  (summable_pow_of_constantCoeff_eq_zero h).one_sub_mul_tsum_pow

end GeomSeries

end Sum

section Prod
variable [CommSemiring R] {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] {f : ι -> R⟦X⟧}

/--
theorem `summable_prod_of_tendsto_order_atTop_nhds_top` / 定理 `summable_prod_of_tendsto_order_atTop_nhds_top`

English:
theorem summable_prod_of_tendsto_order_atTop_nhds_top
  proof: by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply Summable.of_finite
  refine (summable_iff_summable_coeff _).mpr fun n => summable_of_hasFiniteSupport ?_
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, eventually_atTop] at h
  obtain ⟨i, hi⟩ := h n
  apply (Finset.Iio i).powerset.fi

中文:
定理 summable_prod_of_tendsto_order_atTop_nhds_top
  证明: by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply Summable.of_finite
  refine (summable_iff_summable_coeff _).mpr fun n => summable_of_hasFiniteSupport ?_
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, eventually_atTop] at h
  obtain ⟨i, hi⟩ := h n
  apply (Finset.Iio i).powerset.fi

Depends on / 依赖: ENat.tendsto_nhds_top_iff_natCast_lt, Finset, Finset.Iio, Set.Iio, Set.mem_Iio, Set.not_subset.mp, Summable, Summable.of_finite, contrapose, eventually_atTop, finite_toSet, hempty, isEmpty_or_nonempty, mem_Iio, not_lt, not_subset, of_finite, powerset, powerset.finite_toSet.subset, simp_rw
-/
theorem summable_prod_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i => (f i).order) atTop (𝓝 ⊤)) : Summable (∏ i in ·, f i) := by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply Summable.of_finite
  refine (summable_iff_summable_coeff _).mpr fun n => summable_of_hasFiniteSupport ?_
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, eventually_atTop] at h
  obtain ⟨i, hi⟩ := h n
  apply (Finset.Iio i).powerset.finite_toSet.subset
  suffices forall s : Finset ι, coeff n (∏ i in s, f i) != 0 -> ↑s subseteq Set.Iio i by simpa
  intro s hs
  contrapose hs
  obtain ⟨x, hxs, hxi⟩ := Set.not_subset.mp hs
  rw [Set.mem_Iio]; rw [not_lt] at hxi
refine coeff_of_lt_order _ (hi x hxi).trans_le le_trans ?_ (le_order_prod _ _)
  apply Finset.single_le_sum (by simp) hxs

/--
theorem `multipliable_one_add_of_tendsto_order_atTop_nhds_top` / 定理 `multipliable_one_add_of_tendsto_order_atTop_nhds_top`

English:
theorem multipliable_one_add_of_tendsto_order_atTop_nhds_top
  proof: multipliable_one_add_of_summable_prod summable_prod_of_tendsto_order_atTop_nhds_top _ h

中文:
定理 multipliable_one_add_of_tendsto_order_atTop_nhds_top
  证明: multipliable_one_add_of_summable_prod summable_prod_of_tendsto_order_atTop_nhds_top _ h

Depends on / 依赖: multipliable_one_add_of_summable_prod, summable_prod_of_tendsto_order_atTop_nhds_top
-/
theorem multipliable_one_add_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i => (f i).order) atTop (nhds ⊤)) : Multipliable (1 + f ·) :=
multipliable_one_add_of_summable_prod summable_prod_of_tendsto_order_atTop_nhds_top _ h

end Prod

section ProdOneSubPow
variable (R : Type*) [CommRing R] [TopologicalSpace R]

/--
theorem `multipliable_one_sub_X_pow` / 定理 `multipliable_one_sub_X_pow`

English:
theorem multipliable_one_sub_X_pow
  statement: Multipliable fun n => (1 : R⟦X⟧) - X ^ (n + 1)
  proof: by
  nontriviality R
  simp_rw [sub_eq_add_neg]
  apply multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  rw [order_neg]; rw [order_X_pow]
  norm_cast
  exact Nat.lt_add_one_iff.mpr hm

中文:
定理 multipliable_one_sub_X_pow
  结论: Multipliable fun n => (1 : R⟦X⟧) - X ^ (n + 1)
  证明: by
  nontriviality R
  simp_rw [sub_eq_add_neg]
  apply multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  rw [order_neg]; rw [order_X_pow]
  norm_cast
  exact Nat.lt_add_one_iff.mpr hm

Depends on / 依赖: ENat.tendsto_nhds_top_iff_natCast_lt.mpr, Filter, Filter.eventually_atTop.mpr, Nat.lt_add_one_iff.mpr, eventually_atTop, lt_add_one_iff, multipliable_one_add_of_tendsto_order_atTop_nhds_top, nontriviality, order_X_pow, order_neg, simp_rw, sub_eq_add_neg, tendsto_nhds_top_iff_natCast_lt
-/
theorem multipliable_one_sub_X_pow : Multipliable fun n => (1 : R⟦X⟧) - X ^ (n + 1) := by
  nontriviality R
  simp_rw [sub_eq_add_neg]
  apply multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  rw [order_neg]; rw [order_X_pow]
  norm_cast
  exact Nat.lt_add_one_iff.mpr hm

/--
theorem `tprod_one_sub_X_pow_ne_zero` / 定理 `tprod_one_sub_X_pow_ne_zero`

English:
theorem tprod_one_sub_X_pow_ne_zero
  given: [T2Space R] [Nontrivial R]
  proof: by
  by_contra! h
  obtain h := PowerSeries.ext_iff.mp h 0
  simp [coeff_zero_eq_constantCoeff, (multipliable_one_sub_X_pow R).map_tprod _
    (continuous_constantCoeff R)] at h

中文:
定理 tprod_one_sub_X_pow_ne_zero
  条件: [T2Space R] [Nontrivial R]
  证明: by
  by_contra! h
  obtain h := PowerSeries.ext_iff.mp h 0
  simp [coeff_zero_eq_constantCoeff, (multipliable_one_sub_X_pow R).map_tprod _
    (continuous_constantCoeff R)] at h

Depends on / 依赖: PowerSeries, PowerSeries.ext_iff.mp, coeff_zero_eq_constantCoeff, continuous_constantCoeff, ext_iff, map_tprod, multipliable_one_sub_X_pow
-/
theorem tprod_one_sub_X_pow_ne_zero [T2Space R] [Nontrivial R] :
    ∏' i, (1 - X ^ (i + 1)) != (0 : R⟦X⟧) := by
  by_contra! h
  obtain h := PowerSeries.ext_iff.mp h 0
  simp [coeff_zero_eq_constantCoeff, (multipliable_one_sub_X_pow R).map_tprod _
    (continuous_constantCoeff R)] at h

end ProdOneSubPow

end WithPiTopology

end Topological

section Uniform

namespace WithPiTopology

variable [UniformSpace R]

/-- The product uniformity on `PowerSeries` -/
scoped instance : UniformSpace (PowerSeries R) :=
  inferInstance

/--
theorem `uniformContinuous_coeff` / 定理 `uniformContinuous_coeff`

English:
theorem uniformContinuous_coeff
  given: [Semiring R] (d : Nat)
  proof: uniformContinuous_pi.mp uniformContinuous_id (Finsupp.single () d)

中文:
定理 uniformContinuous_coeff
  条件: [Semiring R] (d : 自然数)
  证明: uniformContinuous_pi.mp uniformContinuous_id (Finsupp.single () d)

Depends on / 依赖: Finsupp, Finsupp.single, single, uniformContinuous_id, uniformContinuous_pi, uniformContinuous_pi.mp
-/
theorem uniformContinuous_coeff [Semiring R] (d : Nat) :
    UniformContinuous fun f : PowerSeries R => coeff d f :=
  uniformContinuous_pi.mp uniformContinuous_id (Finsupp.single () d)

/-- Completeness of the uniform structure on `PowerSeries` -/
@[scoped instance]
/--
theorem `instCompleteSpace` / 定理 `instCompleteSpace`

English:
theorem instCompleteSpace
  given: [CompleteSpace R]
  proof: inferInstance

中文:
定理 instCompleteSpace
  条件: [CompleteSpace R]
  证明: inferInstance
-/
theorem instCompleteSpace [CompleteSpace R] :
    CompleteSpace (PowerSeries R) :=
  inferInstance

/-- The `IsUniformAddGroup` structure on `PowerSeries` of a `IsUniformAddGroup` -/
@[scoped instance]
/--
theorem `instIsUniformAddGroup` / 定理 `instIsUniformAddGroup`

English:
theorem instIsUniformAddGroup
  given: [AddGroup R] [IsUniformAddGroup R]
  proof: inferInstance

中文:
定理 instIsUniformAddGroup
  条件: [AddGroup R] [IsUniformAddGroup R]
  证明: inferInstance

Depends on / 依赖: CompHausLike, CompHausLike.finiteCoproduct.isColimit, Discrete, Discrete.functor, Discrete.mk, Discrete.natIsoFunctor.symm, F.obj, PreservesColimit, TopCat, TopCat.sigmaCofanIsColimit, compHausLikeToTop, finiteCoproduct, functor, isColimit, isColimitMapCoconeCofanMkEquiv, natIsoFunctor, preservesColimit_of_iso_diagram, preservesColimit_of_preserves_colimit_cocone, sigmaCofanIsColimit
-/
theorem instIsUniformAddGroup [AddGroup R] [IsUniformAddGroup R] :
    IsUniformAddGroup (PowerSeries R) :=
  inferInstance

end WithPiTopology

end Uniform

section

variable {R}

variable [TopologicalSpace R]

namespace WithPiTopology

open MvPowerSeries.WithPiTopology

/--
theorem `continuous_C` / 定理 `continuous_C`

English:
theorem continuous_C
  given: [Semiring R]
  statement: Continuous (C (R := R))
  proof: MvPowerSeries.WithPiTopology.continuous_C

中文:
定理 continuous_C
  条件: [Semiring R]
  结论: Continuous (C (R := R))
  证明: MvPowerSeries.WithPiTopology.continuous_C

Depends on / 依赖: PreservesFiniteCoproducts, compHausLikeToTop, preservesFiniteCoproducts_of_reflects_of_preserves, toCompHausLike
-/
theorem continuous_C [Semiring R] : Continuous (C (R := R)) :=
  MvPowerSeries.WithPiTopology.continuous_C

/--
theorem `isTopologicallyNilpotent_of_constantCoeff_isNilpotent` / 定理 `isTopologicallyNilpotent_of_constantCoeff_isNilpotent`

English:
theorem isTopologicallyNilpotent_of_constantCoeff_isNilpotent
  statement: [CommSemiring R]
  proof: MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpotent hf

中文:
定理 isTopologicallyNilpotent_of_constantCoeff_isNilpotent
  结论: [CommSemiring R]
  证明: MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpotent hf
-/
theorem isTopologicallyNilpotent_of_constantCoeff_isNilpotent [CommSemiring R]
    {f : PowerSeries R} (hf : IsNilpotent (constantCoeff (R := R) f)) :
    Tendsto (fun n : Nat => f ^ n) atTop (nhds 0) :=
  MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpotent hf

/--
theorem `isTopologicallyNilpotent_of_constantCoeff_zero` / 定理 `isTopologicallyNilpotent_of_constantCoeff_zero`

English:
theorem isTopologicallyNilpotent_of_constantCoeff_zero
  statement: [CommSemiring R]
  proof: MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero hf

中文:
定理 isTopologicallyNilpotent_of_constantCoeff_zero
  结论: [CommSemiring R]
  证明: MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero hf
-/
theorem isTopologicallyNilpotent_of_constantCoeff_zero [CommSemiring R]
    {f : PowerSeries R} (hf : constantCoeff (R := R) f = 0) :
    Tendsto (fun n : Nat => f ^ n) atTop (nhds 0) :=
  MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero hf

/--
theorem `isTopologicallyNilpotent_iff_constantCoeff_isNilpotent` / 定理 `isTopologicallyNilpotent_iff_constantCoeff_isNilpotent`

English:
theorem isTopologicallyNilpotent_iff_constantCoeff_isNilpotent
  proof: MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent f

中文:
定理 isTopologicallyNilpotent_iff_constantCoeff_isNilpotent
  证明: MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, Continuous, Continuous.comp, MvPowerSeries, MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent, WithPiTopology, continuous_fst, continuous_subtype_val, continuous_toFun, isTopologicallyNilpotent_iff_constantCoeff_isNilpotent
-/
theorem isTopologicallyNilpotent_iff_constantCoeff_isNilpotent
    [CommRing R] [DiscreteTopology R] (f : PowerSeries R) :
    Tendsto (fun n : Nat => f ^ n) atTop (nhds 0) ↔
      IsNilpotent (constantCoeff f) :=
  MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent f

end WithPiTopology

end

section Summable

variable [Semiring R] [TopologicalSpace R]

open WithPiTopology MvPowerSeries.WithPiTopology

variable {R}

-- NOTE : one needs an API to apply `Finsupp.uniqueLinearEquiv`
/--
theorem `hasSum_of_monomials_self` / 定理 `hasSum_of_monomials_self`

English:
theorem hasSum_of_monomials_self
  given: (f : PowerSeries R)
  proof: by
  rw [← (Finsupp.uniqueLinearEquiv Nat Nat ()).toEquiv.hasSum_iff]
  convert! MvPowerSeries.WithPiTopology.hasSum_of_monomials_self f
  simp only [LinearEquiv.coe_toEquiv, comp_apply, monomial, coeff]
  congr
  all_goals { ext; simp }

中文:
定理 hasSum_of_monomials_self
  条件: (f : PowerSeries R)
  证明: by
  rw [← (Finsupp.uniqueLinearEquiv Nat Nat ()).toEquiv.hasSum_iff]
  convert! MvPowerSeries.WithPiTopology.hasSum_of_monomials_self f
  simp only [LinearEquiv.coe_toEquiv, comp_apply, monomial, coeff]
  congr
  all_goals { ext; simp }

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, Continuous, Continuous.comp, Finsupp, Finsupp.uniqueLinearEquiv, LinearEquiv, LinearEquiv.coe_toEquiv, MvPowerSeries, MvPowerSeries.WithPiTopology.hasSum_of_monomials_self, WithPiTopology, all_goals, coe_toEquiv, comp_apply, continuous_snd, continuous_subtype_val, continuous_toFun, convert, hasSum_iff, hasSum_of_monomials_self
-/
theorem hasSum_of_monomials_self (f : PowerSeries R) :
    HasSum (fun d : Nat => monomial d (coeff d f)) f := by
  rw [← (Finsupp.uniqueLinearEquiv Nat Nat ()).toEquiv.hasSum_iff]
  convert! MvPowerSeries.WithPiTopology.hasSum_of_monomials_self f
  simp only [LinearEquiv.coe_toEquiv, comp_apply, monomial, coeff]
  congr
  all_goals { ext; simp }

/--
theorem `as_tsum` / 定理 `as_tsum`

English:
theorem as_tsum
  given: [T2Space R] (f : PowerSeries R)
  proof: (HasSum.tsum_eq (hasSum_of_monomials_self f)).symm

中文:
定理 as_tsum
  条件: [T2Space R] (f : PowerSeries R)
  证明: (HasSum.tsum_eq (hasSum_of_monomials_self f)).symm

Depends on / 依赖: HasSum, HasSum.tsum_eq, hasSum_of_monomials_self, tsum_eq
-/
theorem as_tsum [T2Space R] (f : PowerSeries R) :
    f = tsum fun d : Nat => monomial d (coeff d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self f)).symm

end Summable

end PowerSeries
