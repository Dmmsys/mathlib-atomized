/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions

/-! # Product topology on multivariate power series

Let `R` be with `Semiring R` and `TopologicalSpace R`
In this file we define the topology on `MvPowerSeries σ R`
that corresponds to the simple convergence on its coefficients.
It is the coarsest topology for which all coefficient maps are continuous.

When `R` has `UniformSpace R`, we define the corresponding uniform structure.

This topology can be included by writing `open scoped MvPowerSeries.WithPiTopology`.

When the type of coefficients has the discrete topology, it corresponds to the topology defined by
[N. Bourbaki, *Algebra II*, Chapter 4, §4, n°2][bourbaki1981].

It is *not* the adic topology in general.

## Main results

- `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpotent`,
  `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero`: if the constant
  coefficient of `f` is nilpotent, or vanishes, then `f` is topologically nilpotent.

- `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent` :
  assuming the base ring has the discrete topology, `f` is topologically nilpotent iff the constant
  coefficient of `f` is nilpotent.

- `MvPowerSeries.WithPiTopology.hasSum_of_monomials_self` : viewed as an infinite sum, a power
  series converges to itself.

TODO: add the similar result for the series of homogeneous components.

## Instances

- If `R` is a topological (semi)ring, then so is `MvPowerSeries σ R`.
- If the topology of `R` is T0 or T2, then so is that of `MvPowerSeries σ R`.
- If `R` is a `IsUniformAddGroup`, then so is `MvPowerSeries σ R`.
- If `R` is complete, then so is `MvPowerSeries σ R`.

## Implementation Notes

In `Mathlib/RingTheory/MvPowerSeries/LinearTopology.lean`, we generalize the criterion for
topological nilpotency by proving that, if the base ring is equipped with a *linear* topology, then
a power series is topologically nilpotent if and only if its constant coefficient is.
This is lemma `MvPowerSeries.LinearTopology.isTopologicallyNilpotent_iff_constantCoeff`.

Mathematically, everything proven in this file follows from that general statement. However,
formalizing this yields a few (minor) annoyances:

- we would need to push the results in this file slightly lower in the import tree
  (likely, in a new dedicated file);
- we would have to work in `CommRing`s rather than `CommSemiring`s (this probably does not
  matter in any way though);
- because `isTopologicallyNilpotent_of_constantCoeff_isNilpotent` holds for *any* topology,
  not necessarily discrete nor linear, the proof going through the general case involves
  juggling a bit with the topologies.

Since the code duplication is rather minor (the interesting part of the proof is already extracted
as `MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent`), we just leave this as is for now.
But future contributors wishing to clean this up should feel free to give it a try!

-/

public section

namespace MvPowerSeries

open Function Filter

open scoped Topology

variable {σ R : Type*}

namespace WithPiTopology

section Topology

variable [TopologicalSpace R]

variable (R) in
/-- The pointwise topology on `MvPowerSeries` -/
scoped instance : TopologicalSpace (MvPowerSeries σ R) :=
inferInstanceAs TopologicalSpace ((σ ->₀ Nat) -> R)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `instTopologicalSpace_mono` / 定理 `instTopologicalSpace_mono`

English:
theorem instTopologicalSpace_mono
  given: (σ : Type*) {R : Type*} {t u : TopologicalSpace R} (htu : t <= u)
  proof: by
  change ⨅ i, _ <= ⨅ i, _
  gcongr

中文:
定理 instTopologicalSpace_mono
  条件: (σ : 类型) {R : 类型} {t u : 拓扑空间 R} (htu : t <= u)
  证明: by
  change ⨅ i, _ <= ⨅ i, _
  gcongr
-/
theorem instTopologicalSpace_mono (σ : Type*) {R : Type*} {t u : TopologicalSpace R} (htu : t <= u) :
    @instTopologicalSpace σ R t <= @instTopologicalSpace σ R u := by
  change ⨅ i, _ <= ⨅ i, _
  gcongr

/-- `MvPowerSeries` on a `T0Space` form a `T0Space` -/
@[scoped instance]
/--
theorem `instT0Space` / 定理 `instT0Space`

English:
theorem instT0Space
  given: [T0Space R]
  statement: T0Space (MvPowerSeries σ R)
  proof: Pi.instT0Space

中文:
定理 instT0Space
  条件: [T0空间 R]
  结论: T0空间 (MvPowerSeries σ R)
  证明: Pi.instT0Space

Depends on / 依赖: Pi.instT0Space, instT0Space
-/
theorem instT0Space [T0Space R] : T0Space (MvPowerSeries σ R) := Pi.instT0Space

/-- `MvPowerSeries` on a `T2Space` form a `T2Space` -/
@[scoped instance]
/--
theorem `instT2Space` / 定理 `instT2Space`

English:
theorem instT2Space
  given: [T2Space R]
  statement: T2Space (MvPowerSeries σ R)
  proof: Pi.t2Space

中文:
定理 instT2Space
  条件: [T2空间 R]
  结论: T2空间 (MvPowerSeries σ R)
  证明: Pi.t2Space

Depends on / 依赖: Pi.t2Space, t2Space
-/
theorem instT2Space [T2Space R] : T2Space (MvPowerSeries σ R) := Pi.t2Space

variable (R) in
/-- `MvPowerSeries.coeff` is continuous. -/
@[fun_prop]
/--
theorem `continuous_coeff` / 定理 `continuous_coeff`

English:
theorem continuous_coeff
  given: [Semiring R] (d : σ ->₀ Nat)
  proof: continuous_pi_iff.mp continuous_id d

中文:
定理 continuous_coeff
  条件: [半环 R] (d : σ ->₀ 自然数)
  证明: continuous_pi_iff.mp continuous_id d
-/
theorem continuous_coeff [Semiring R] (d : σ ->₀ Nat) :
    Continuous (MvPowerSeries.coeff (R := R) d) :=
  continuous_pi_iff.mp continuous_id d

variable (R) in
/--
theorem `continuous_constantCoeff` / 定理 `continuous_constantCoeff`

English:
theorem continuous_constantCoeff
  given: [Semiring R]
  statement: Continuous (constantCoeff (σ := σ) (R := R))
  proof: continuous_coeff (R := R) 0

中文:
定理 continuous_constantCoeff
  条件: [半环 R]
  结论: 连续 (constantCoeff (σ := σ) (R := R))
  证明: continuous_coeff (R := R) 0
-/
theorem continuous_constantCoeff [Semiring R] : Continuous (constantCoeff (σ := σ) (R := R)) :=
  continuous_coeff (R := R) 0

set_option backward.isDefEq.respectTransparency false in
/--
theorem `tendsto_iff_coeff_tendsto` / 定理 `tendsto_iff_coeff_tendsto`

English:
theorem tendsto_iff_coeff_tendsto
  statement: [Semiring R] {ι : Type*}
  proof: by
  rw [nhds_pi]; rw [tendsto_pi]
  exact forall_congr' (fun d => Iff.rfl)

中文:
定理 tendsto_iff_coeff_tendsto
  结论: [半环 R] {ι : 类型}
  证明: by
  rw [nhds_pi]; rw [tendsto_pi]
  exact forall_congr' (fun d => Iff.rfl)

Depends on / 依赖: Iff.rfl, forall_congr, nhds_pi, tendsto_pi
-/
theorem tendsto_iff_coeff_tendsto [Semiring R] {ι : Type*}
    (f : ι -> MvPowerSeries σ R) (u : Filter ι) (g : MvPowerSeries σ R) :
    Tendsto f u (nhds g) ↔
    forall d : σ ->₀ Nat, Tendsto (fun i => coeff d (f i)) u (nhds (coeff d g)) := by
  rw [nhds_pi]; rw [tendsto_pi]
  exact forall_congr' (fun d => Iff.rfl)

/--
theorem `tendsto_trunc'_atTop` / 定理 `tendsto_trunc'_atTop`

English:
theorem tendsto_trunc'_atTop
  given: [DecidableEq σ] [CommSemiring R] (f : MvPowerSeries σ R)
  proof: by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  exact tendsto_atTop_of_eventually_const fun n (hdn : d <= n) => (by simp [coeff_trunc', hdn])

中文:
定理 tendsto_trunc'_atTop
  条件: [DecidableEq σ] [交换半环 R] (f : MvPowerSeries σ R)
  证明: by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  exact tendsto_atTop_of_eventually_const fun n (hdn : d <= n) => (by simp [coeff_trunc', hdn])

Depends on / 依赖: coeff_trunc, tendsto_atTop_of_eventually_const, tendsto_iff_coeff_tendsto
-/
theorem tendsto_trunc'_atTop [DecidableEq σ] [CommSemiring R] (f : MvPowerSeries σ R) :
    Tendsto (fun d => (trunc' R d f : MvPowerSeries σ R)) atTop (𝓝 f) := by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  exact tendsto_atTop_of_eventually_const fun n (hdn : d <= n) => (by simp [coeff_trunc', hdn])

/--
theorem `tendsto_trunc_atTop` / 定理 `tendsto_trunc_atTop`

English:
theorem tendsto_trunc_atTop
  given: [DecidableEq σ] [CommSemiring R] [Nonempty σ] (f : MvPowerSeries σ R)
  proof: by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  obtain ⟨s, _⟩ := (exists_const σ).mpr trivial
  apply tendsto_atTop_of_eventually_const (i₀ := d + Finsupp.single s 1)
  intro n hn
  rw [MvPolynomial.coeff_coe]; rw [coeff_trunc]; rw [if_pos]
  apply lt_of_lt_of_le _ hn
  simpa [Finsupp.lt_def] using ⟨s, by simp⟩

中文:
定理 tendsto_trunc_atTop
  条件: [DecidableEq σ] [交换半环 R] [非空 σ] (f : MvPowerSeries σ R)
  证明: by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  obtain ⟨s, _⟩ := (exists_const σ).mpr trivial
  apply tendsto_atTop_of_eventually_const (i₀ := d + Finsupp.single s 1)
  intro n hn
  rw [MvPolynomial.coeff_coe]; rw [coeff_trunc]; rw [if_pos]
  apply lt_of_lt_of_le _ hn
  simpa [Finsupp.lt_def] using ⟨s, by simp⟩

Depends on / 依赖: Finsupp, Finsupp.lt_def, Finsupp.single, MvPolynomial, MvPolynomial.coeff_coe, coeff_coe, coeff_trunc, exists_const, if_pos, lt_def, lt_of_lt_of_le, single, tendsto_atTop_of_eventually_const, tendsto_iff_coeff_tendsto
-/
theorem tendsto_trunc_atTop [DecidableEq σ] [CommSemiring R] [Nonempty σ] (f : MvPowerSeries σ R) :
    Tendsto (fun d => (trunc R d f : MvPowerSeries σ R)) atTop (𝓝 f) := by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  obtain ⟨s, _⟩ := (exists_const σ).mpr trivial
  apply tendsto_atTop_of_eventually_const (i₀ := d + Finsupp.single s 1)
  intro n hn
  rw [MvPolynomial.coeff_coe]; rw [coeff_trunc]; rw [if_pos]
  apply lt_of_lt_of_le _ hn
  simpa [Finsupp.lt_def] using ⟨s, by simp⟩

/--
theorem `denseRange_toMvPowerSeries` / 定理 `denseRange_toMvPowerSeries`

English:
theorem denseRange_toMvPowerSeries
  given: [CommSemiring R]
  proof: fun f => by
  classical
exact mem_closure_of_tendsto (tendsto_trunc'_atTop f) .of_forall fun _ => Set.mem_range_self _

中文:
定理 denseRange_toMvPowerSeries
  条件: [交换半环 R]
  证明: fun f => by
  classical
exact mem_closure_of_tendsto (tendsto_trunc'_atTop f) .of_forall fun _ => Set.mem_range_self _

Depends on / 依赖: Set.mem_range_self, _atTop, classical, mem_closure_of_tendsto, mem_range_self, of_forall, tendsto_trunc
-/
theorem denseRange_toMvPowerSeries [CommSemiring R] :
    DenseRange (MvPolynomial.toMvPowerSeries (R := R) (σ := σ)) := fun f => by
  classical
exact mem_closure_of_tendsto (tendsto_trunc'_atTop f) .of_forall fun _ => Set.mem_range_self _

variable (σ R)

/-- The semiring topology on `MvPowerSeries` of a topological semiring -/
@[scoped instance]
/--
theorem `instIsTopologicalSemiring` / 定理 `instIsTopologicalSemiring`

English:
theorem instIsTopologicalSemiring
  given: [Semiring R] [IsTopologicalSemiring R]
  proof: continuous_pi fun d => continuous_add.comp
    (((continuous_coeff R d).fst').prodMk (continuous_coeff R d).snd')
  continuous_mul := continuous_pi fun _ =>
    continuous_finsetSum _ fun i _ => continuous_mul.comp
      ((continuous_coeff R i.fst).fst'.prodMk (continuous_coeff R i.snd).snd')

中文:
定理 instIsTopologicalSemiring
  条件: [半环 R] [是TopologicalSemiring R]
  证明: continuous_pi fun d => continuous_add.comp
    (((continuous_coeff R d).fst').prodMk (continuous_coeff R d).snd')
  continuous_mul := continuous_pi fun _ =>
    continuous_finsetSum _ fun i _ => continuous_mul.comp
      ((continuous_coeff R i.fst).fst'.prodMk (continuous_coeff R i.snd).snd')

Depends on / 依赖: continuous_add, continuous_add.comp, continuous_pi
-/
theorem instIsTopologicalSemiring [Semiring R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring (MvPowerSeries σ R) where
  continuous_add := continuous_pi fun d => continuous_add.comp
    (((continuous_coeff R d).fst').prodMk (continuous_coeff R d).snd')
  continuous_mul := continuous_pi fun _ =>
    continuous_finsetSum _ fun i _ => continuous_mul.comp
      ((continuous_coeff R i.fst).fst'.prodMk (continuous_coeff R i.snd).snd')

/-- The ring topology on `MvPowerSeries` of a topological ring -/
@[scoped instance]
/--
theorem `instIsTopologicalRing` / 定理 `instIsTopologicalRing`

English:
theorem instIsTopologicalRing
  given: [Ring R] [IsTopologicalRing R]
  proof: { instIsTopologicalSemiring σ R with
    continuous_neg := continuous_pi fun d => Continuous.comp continuous_neg
      (continuous_coeff R d) }

中文:
定理 instIsTopologicalRing
  条件: [环 R] [是拓扑环 R]
  证明: { instIsTopologicalSemiring σ R with
    continuous_neg := continuous_pi fun d => Continuous.comp continuous_neg
      (continuous_coeff R d) }

Depends on / 依赖: Continuous, Continuous.comp, continuous_coeff, continuous_neg, continuous_pi, instIsTopologicalSemiring
-/
theorem instIsTopologicalRing [Ring R] [IsTopologicalRing R] :
    IsTopologicalRing (MvPowerSeries σ R) :=
  { instIsTopologicalSemiring σ R with
    continuous_neg := continuous_pi fun d => Continuous.comp continuous_neg
      (continuous_coeff R d) }

variable {σ R}

@[fun_prop]
/--
theorem `continuous_C` / 定理 `continuous_C`

English:
theorem continuous_C
  given: [Semiring R]
  proof: by
  classical
  simp only [continuous_iff_continuousAt]
  refine fun r => (tendsto_iff_coeff_tendsto _ _ _).mpr fun d => ?_
  simp only [coeff_C]
  split_ifs
  · exact tendsto_id
  · exact tendsto_const_nhds

中文:
定理 continuous_C
  条件: [半环 R]
  证明: by
  classical
  simp only [continuous_iff_continuousAt]
  refine fun r => (tendsto_iff_coeff_tendsto _ _ _).mpr fun d => ?_
  simp only [coeff_C]
  split_ifs
  · exact tendsto_id
  · exact tendsto_const_nhds

Depends on / 依赖: classical, coeff_C, continuous_iff_continuousAt, split_ifs, tendsto_const_nhds, tendsto_id, tendsto_iff_coeff_tendsto
-/
theorem continuous_C [Semiring R] :
    Continuous (C (σ := σ) (R := R)) := by
  classical
  simp only [continuous_iff_continuousAt]
  refine fun r => (tendsto_iff_coeff_tendsto _ _ _).mpr fun d => ?_
  simp only [coeff_C]
  split_ifs
  · exact tendsto_id
  · exact tendsto_const_nhds

/-- Scalar multiplication on `MvPowerSeries` is continuous. -/
instance {S : Type*} [Semiring S] [TopologicalSpace S]
    [CommSemiring R] [Algebra R S] [ContinuousSMul R S] :
    ContinuousSMul R (MvPowerSeries σ S) :=
  instContinuousSMulForall

/--
theorem `variables_tendsto_zero` / 定理 `variables_tendsto_zero`

English:
theorem variables_tendsto_zero
  given: [Semiring R]
  proof: by
  classical
  simp only [tendsto_iff_coeff_tendsto, coeff_X, coeff_zero]
  refine fun d => tendsto_nhds_of_eventually_eq ?_
  by_cases! h : exists i, d = Finsupp.single i 1
  · obtain ⟨i, hi⟩ := h
    filter_upwards [eventually_cofinite_ne i] with j hj
    simp [hi, Finsupp.single_eq_single_iff, hj.symm]
  · simpa only [ite_eq_right_iff] using
      Eventually.of_forall fun x h' => (h x h').elim

中文:
定理 variables_tendsto_zero
  条件: [半环 R]
  证明: by
  classical
  simp only [tendsto_iff_coeff_tendsto, coeff_X, coeff_zero]
  refine fun d => tendsto_nhds_of_eventually_eq ?_
  by_cases! h : exists i, d = Finsupp.single i 1
  · obtain ⟨i, hi⟩ := h
    filter_upwards [eventually_cofinite_ne i] with j hj
    simp [hi, Finsupp.single_eq_single_iff, hj.symm]
  · simpa only [ite_eq_right_iff] using
      Eventually.of_forall fun x h' => (h x h').elim

Depends on / 依赖: Eventually, Eventually.of_forall, Finsupp, Finsupp.single, Finsupp.single_eq_single_iff, classical, coeff_X, coeff_zero, eventually_cofinite_ne, filter_upwards, hj.symm, ite_eq_right_iff, of_forall, single, single_eq_single_iff, tendsto_iff_coeff_tendsto, tendsto_nhds_of_eventually_eq
-/
theorem variables_tendsto_zero [Semiring R] :
    Tendsto (X · : σ -> MvPowerSeries σ R) cofinite (nhds 0) := by
  classical
  simp only [tendsto_iff_coeff_tendsto, coeff_X, coeff_zero]
  refine fun d => tendsto_nhds_of_eventually_eq ?_
  by_cases! h : exists i, d = Finsupp.single i 1
  · obtain ⟨i, hi⟩ := h
    filter_upwards [eventually_cofinite_ne i] with j hj
    simp [hi, Finsupp.single_eq_single_iff, hj.symm]
  · simpa only [ite_eq_right_iff] using
      Eventually.of_forall fun x h' => (h x h').elim

/--
theorem `isTopologicallyNilpotent_of_constantCoeff_isNilpotent` / 定理 `isTopologicallyNilpotent_of_constantCoeff_isNilpotent`

English:
theorem isTopologicallyNilpotent_of_constantCoeff_isNilpotent
  statement: [CommSemiring R]
  proof: by
  obtain ⟨m, hm⟩ := hf
  simp_rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto, coeff_zero]
  exact fun d => tendsto_atTop_of_eventually_const fun n hn =>
    coeff_eq_zero_of_constantCoeff_nilpotent hm hn

中文:
定理 isTopologicallyNilpotent_of_constantCoeff_isNilpotent
  结论: [交换半环 R]
  证明: by
  obtain ⟨m, hm⟩ := hf
  simp_rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto, coeff_zero]
  exact fun d => tendsto_atTop_of_eventually_const fun n hn =>
    coeff_eq_zero_of_constantCoeff_nilpotent hm hn

Depends on / 依赖: IsTopologicallyNilpotent, coeff_eq_zero_of_constantCoeff_nilpotent, coeff_zero, simp_rw, tendsto_atTop_of_eventually_const, tendsto_iff_coeff_tendsto
-/
theorem isTopologicallyNilpotent_of_constantCoeff_isNilpotent [CommSemiring R]
    {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff f)) :
    IsTopologicallyNilpotent f := by
  obtain ⟨m, hm⟩ := hf
  simp_rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto, coeff_zero]
  exact fun d => tendsto_atTop_of_eventually_const fun n hn =>
    coeff_eq_zero_of_constantCoeff_nilpotent hm hn

/--
theorem `isTopologicallyNilpotent_of_constantCoeff_zero` / 定理 `isTopologicallyNilpotent_of_constantCoeff_zero`

English:
theorem isTopologicallyNilpotent_of_constantCoeff_zero
  statement: [CommSemiring R]
  proof: by
  apply isTopologicallyNilpotent_of_constantCoeff_isNilpotent
  rw [hf]
  exact IsNilpotent.zero

中文:
定理 isTopologicallyNilpotent_of_constantCoeff_zero
  结论: [交换半环 R]
  证明: by
  apply isTopologicallyNilpotent_of_constantCoeff_isNilpotent
  rw [hf]
  exact IsNilpotent.zero

Depends on / 依赖: IsNilpotent, IsNilpotent.zero, isTopologicallyNilpotent_of_constantCoeff_isNilpotent
-/
theorem isTopologicallyNilpotent_of_constantCoeff_zero [CommSemiring R]
    {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    Tendsto (fun n : Nat => f ^ n) atTop (nhds 0) := by
  apply isTopologicallyNilpotent_of_constantCoeff_isNilpotent
  rw [hf]
  exact IsNilpotent.zero

/--
theorem `isTopologicallyNilpotent_iff_constantCoeff_isNilpotent` / 定理 `isTopologicallyNilpotent_iff_constantCoeff_isNilpotent`

English:
theorem isTopologicallyNilpotent_iff_constantCoeff_isNilpotent
  proof: by
  refine ⟨fun H => ?_, isTopologicallyNilpotent_of_constantCoeff_isNilpotent⟩
  replace H := H.map (continuous_constantCoeff R)
  simp_rw [IsTopologicallyNilpotent, nhds_discrete, tendsto_pure] at H
  exact H.exists

中文:
定理 isTopologicallyNilpotent_iff_constantCoeff_isNilpotent
  证明: by
  refine ⟨fun H => ?_, isTopologicallyNilpotent_of_constantCoeff_isNilpotent⟩
  replace H := H.map (continuous_constantCoeff R)
  simp_rw [IsTopologicallyNilpotent, nhds_discrete, tendsto_pure] at H
  exact H.exists

Depends on / 依赖: H.exists, H.map, IsTopologicallyNilpotent, continuous_constantCoeff, isTopologicallyNilpotent_of_constantCoeff_isNilpotent, nhds_discrete, replace, simp_rw, tendsto_pure
-/
theorem isTopologicallyNilpotent_iff_constantCoeff_isNilpotent
    [CommRing R] [DiscreteTopology R] (f : MvPowerSeries σ R) :
    IsTopologicallyNilpotent f ↔ IsNilpotent (constantCoeff f) := by
  refine ⟨fun H => ?_, isTopologicallyNilpotent_of_constantCoeff_isNilpotent⟩
  replace H := H.map (continuous_constantCoeff R)
  simp_rw [IsTopologicallyNilpotent, nhds_discrete, tendsto_pure] at H
  exact H.exists

variable [Semiring R]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasSum_of_monomials_self` / 定理 `hasSum_of_monomials_self`

English:
theorem hasSum_of_monomials_self
  given: (f : MvPowerSeries σ R)
  proof: by
  rw [Pi.hasSum]
  intro d
  simpa using! hasSum_single d (fun d' h => coeff_monomial_ne h.symm _)

中文:
定理 hasSum_of_monomials_self
  条件: (f : MvPowerSeries σ R)
  证明: by
  rw [Pi.hasSum]
  intro d
  simpa using! hasSum_single d (fun d' h => coeff_monomial_ne h.symm _)

Depends on / 依赖: Pi.hasSum, coeff_monomial_ne, h.symm, hasSum, hasSum_single
-/
theorem hasSum_of_monomials_self (f : MvPowerSeries σ R) :
    HasSum (fun d : σ ->₀ Nat => monomial d (coeff d f)) f := by
  rw [Pi.hasSum]
  intro d
  simpa using! hasSum_single d (fun d' h => coeff_monomial_ne h.symm _)

/--
theorem `as_tsum` / 定理 `as_tsum`

English:
theorem as_tsum
  given: [T2Space R] (f : MvPowerSeries σ R)
  proof: (HasSum.tsum_eq (hasSum_of_monomials_self _)).symm

中文:
定理 as_tsum
  条件: [T2空间 R] (f : MvPowerSeries σ R)
  证明: (HasSum.tsum_eq (hasSum_of_monomials_self _)).symm

Depends on / 依赖: HasSum, HasSum.tsum_eq, hasSum_of_monomials_self, tsum_eq
-/
theorem as_tsum [T2Space R] (f : MvPowerSeries σ R) :
    f = tsum fun d : σ ->₀ Nat => monomial d (coeff d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self _)).symm

section Sum
variable {ι : Type*} {f : ι -> MvPowerSeries σ R}

/--
theorem `hasSum_iff_hasSum_coeff` / 定理 `hasSum_iff_hasSum_coeff`

English:
theorem hasSum_iff_hasSum_coeff
  given: {g : MvPowerSeries σ R}
  proof: by
  simp_rw [HasSum, ← map_sum]
  apply tendsto_iff_coeff_tendsto

中文:
定理 hasSum_iff_hasSum_coeff
  条件: {g : MvPowerSeries σ R}
  证明: by
  simp_rw [HasSum, ← map_sum]
  apply tendsto_iff_coeff_tendsto

Depends on / 依赖: HasSum, map_sum, simp_rw, tendsto_iff_coeff_tendsto
-/
theorem hasSum_iff_hasSum_coeff {g : MvPowerSeries σ R} :
    HasSum f g ↔ forall d : σ ->₀ Nat, HasSum (fun i => coeff d (f i)) (coeff d g) := by
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
    exact ⟨a, by simpa using! h⟩

中文:
定理 summable_iff_summable_coeff
  证明: by
  simp_rw [Summable, hasSum_iff_hasSum_coeff]
  constructor
  · rintro ⟨a, h⟩ n
    exact ⟨coeff n a, h n⟩
  · intro h
    choose a h using h
    exact ⟨a, by simpa using! h⟩

Depends on / 依赖: Summable, hasSum_iff_hasSum_coeff, simp_rw
-/
theorem summable_iff_summable_coeff :
    Summable f ↔ forall d : σ ->₀ Nat, Summable (fun i => coeff d (f i)) := by
  simp_rw [Summable, hasSum_iff_hasSum_coeff]
  constructor
  · rintro ⟨a, h⟩ n
    exact ⟨coeff n a, h n⟩
  · intro h
    choose a h using h
    exact ⟨a, by simpa using! h⟩

variable [LinearOrder ι] [LocallyFiniteOrderBot ι]

/--
theorem `summable_of_tendsto_weightedOrder_atTop_nhds_top` / 定理 `summable_of_tendsto_weightedOrder_atTop_nhds_top`

English:
theorem summable_of_tendsto_weightedOrder_atTop_nhds_top
  statement: {w : σ -> Nat}
  proof: by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply summable_empty
  rw [summable_iff_summable_coeff]
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop] at h
  intro d
  obtain ⟨i, hi⟩ := h (Finsupp.weight w d)
refine summable_of_hasFiniteSupport (Set.finite_Iic i).subset ?_
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro k hk
  contrapose! hk
exact coeff_eq_zero_of_lt_weightedOrder w hi k hk.le

中文:
定理 summable_of_tendsto_weightedOrder_atTop_nhds_top
  结论: {w : σ -> 自然数}
  证明: by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply summable_empty
  rw [summable_iff_summable_coeff]
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop] at h
  intro d
  obtain ⟨i, hi⟩ := h (Finsupp.weight w d)
refine summable_of_hasFiniteSupport (Set.finite_Iic i).subset ?_
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro k hk
  contrapose! hk
exact coeff_eq_zero_of_lt_weightedOrder w hi k hk.le

Depends on / 依赖: ENat.tendsto_nhds_top_iff_natCast_lt, Filter, Filter.eventually_atTop, Finsupp, Finsupp.weight, Function, Function.support_subset_iff, Set.finite_Iic, Set.mem_Iic, coeff_eq_zero_of_lt_weightedOrder, contrapose, eventually_atTop, finite_Iic, hempty, hk.le, isEmpty_or_nonempty, mem_Iic, simp_rw, subset, summable_empty
-/
theorem summable_of_tendsto_weightedOrder_atTop_nhds_top {w : σ -> Nat}
    (h : Tendsto (fun i => weightedOrder w (f i)) atTop (𝓝 ⊤)) : Summable f := by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply summable_empty
  rw [summable_iff_summable_coeff]
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop] at h
  intro d
  obtain ⟨i, hi⟩ := h (Finsupp.weight w d)
refine summable_of_hasFiniteSupport (Set.finite_Iic i).subset ?_
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro k hk
  contrapose! hk
exact coeff_eq_zero_of_lt_weightedOrder w hi k hk.le

/--
theorem `summable_of_tendsto_order_atTop_nhds_top` / 定理 `summable_of_tendsto_order_atTop_nhds_top`

English:
theorem summable_of_tendsto_order_atTop_nhds_top
  proof: summable_of_tendsto_weightedOrder_atTop_nhds_top h

中文:
定理 summable_of_tendsto_order_atTop_nhds_top
  证明: summable_of_tendsto_weightedOrder_atTop_nhds_top h

Depends on / 依赖: summable_of_tendsto_weightedOrder_atTop_nhds_top
-/
theorem summable_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i => (f i).order) atTop (𝓝 ⊤)) : Summable f :=
  summable_of_tendsto_weightedOrder_atTop_nhds_top h

/--
theorem `summable_pow_of_constantCoeff_eq_zero` / 定理 `summable_pow_of_constantCoeff_eq_zero`

English:
theorem summable_pow_of_constantCoeff_eq_zero
  statement: {f : MvPowerSeries σ R}
  proof: by
  apply summable_of_tendsto_order_atTop_nhds_top
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop]
  refine fun n => ⟨n + 1, fun m hm => lt_of_lt_of_le ?_ (le_order_pow _)⟩
  refine (ENat.natCast_lt_natCast.mpr (Nat.add_one_le_iff.mp hm)).trans_le ?_
  simpa [nsmul_eq_mul] using ENat.self_le_mul_right m (order_ne_zero_iff_constCoeff_eq_zero.mpr h)

中文:
定理 summable_pow_of_constantCoeff_eq_zero
  结论: {f : MvPowerSeries σ R}
  证明: by
  apply summable_of_tendsto_order_atTop_nhds_top
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop]
  refine fun n => ⟨n + 1, fun m hm => lt_of_lt_of_le ?_ (le_order_pow _)⟩
  refine (ENat.natCast_lt_natCast.mpr (Nat.add_one_le_iff.mp hm)).trans_le ?_
  simpa [nsmul_eq_mul] using ENat.self_le_mul_right m (order_ne_zero_iff_constCoeff_eq_zero.mpr h)

Depends on / 依赖: ENat.natCast_lt_natCast.mpr, ENat.self_le_mul_right, ENat.tendsto_nhds_top_iff_natCast_lt, Filter, Filter.eventually_atTop, Nat.add_one_le_iff.mp, add_one_le_iff, eventually_atTop, le_order_pow, lt_of_lt_of_le, natCast_lt_natCast, nsmul_eq_mul, order_ne_zero_iff_constCoeff_eq_zero, order_ne_zero_iff_constCoeff_eq_zero.mpr, self_le_mul_right, simp_rw, summable_of_tendsto_order_atTop_nhds_top, tendsto_nhds_top_iff_natCast_lt, trans_le
-/
theorem summable_pow_of_constantCoeff_eq_zero {f : MvPowerSeries σ R}
    (h : f.constantCoeff = 0) : Summable (f ^ ·) := by
  apply summable_of_tendsto_order_atTop_nhds_top
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop]
  refine fun n => ⟨n + 1, fun m hm => lt_of_lt_of_le ?_ (le_order_pow _)⟩
  refine (ENat.natCast_lt_natCast.mpr (Nat.add_one_le_iff.mp hm)).trans_le ?_
  simpa [nsmul_eq_mul] using ENat.self_le_mul_right m (order_ne_zero_iff_constCoeff_eq_zero.mpr h)

section GeomSeries
variable {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R] [T2Space R]
variable {f : MvPowerSeries σ R}

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
variable {σ R : Type*} [TopologicalSpace R] [CommSemiring R]
variable {ι : Type*} {f : ι -> MvPowerSeries σ R} [LinearOrder ι] [LocallyFiniteOrderBot ι]

/--
theorem `summable_prod_of_tendsto_weightedOrder_atTop_nhds_top` / 定理 `summable_prod_of_tendsto_weightedOrder_atTop_nhds_top`

English:
theorem summable_prod_of_tendsto_weightedOrder_atTop_nhds_top
  statement: {w : σ -> Nat}
  proof: by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply Summable.of_finite
  refine summable_iff_summable_coeff.mpr fun d => summable_of_hasFiniteSupport ?_
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, eventually_atTop] at h
  obtain ⟨i, hi⟩ := h (Finsupp.weight w d)
  apply (Finset.Iio i).powerset.finite_toSet.subset
  suffices forall s : Finset ι, coeff d (∏ i in s, f i) != 0 -> ↑s subseteq Set.Iio i by simpa
  intro s hs
  contrapose hs
  obtain ⟨x, hxs, hxi⟩ := Set.not_subset.mp hs
  rw [Set.mem_Iio]; rw [not_lt] at hxi
refine coeff_eq_zero_of_lt_weightedOrder w (hi x hxi).trans_le ?_
  apply le_trans (Finset.single_le_sum (by simp) hxs) (le_weightedOrder_prod w _ _)

中文:
定理 summable_prod_of_tendsto_weightedOrder_atTop_nhds_top
  结论: {w : σ -> 自然数}
  证明: by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply Summable.of_finite
  refine summable_iff_summable_coeff.mpr fun d => summable_of_hasFiniteSupport ?_
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, eventually_atTop] at h
  obtain ⟨i, hi⟩ := h (Finsupp.weight w d)
  apply (Finset.Iio i).powerset.finite_toSet.subset
  suffices forall s : Finset ι, coeff d (∏ i in s, f i) != 0 -> ↑s subseteq Set.Iio i by simpa
  intro s hs
  contrapose hs
  obtain ⟨x, hxs, hxi⟩ := Set.not_subset.mp hs
  rw [Set.mem_Iio]; rw [not_lt] at hxi
refine coeff_eq_zero_of_lt_weightedOrder w (hi x hxi).trans_le ?_
  apply le_trans (Finset.single_le_sum (by simp) hxs) (le_weightedOrder_prod w _ _)

Depends on / 依赖: ENat.tendsto_nhds_top_iff_natCast_lt, Finset, Finset.Iio, Finsupp, Finsupp.weight, Set.Iio, Set.mem_Iio, Set.not_subset.mp, Summable, Summable.of_finite, contrapose, eventually_atTop, finite_toSet, hempty, isEmpty_or_nonempty, mem_Iio, not_subset, of_finite, powerset, powerset.finite_toSet.subset
-/
theorem summable_prod_of_tendsto_weightedOrder_atTop_nhds_top {w : σ -> Nat}
    (h : Tendsto (fun i => weightedOrder w (f i)) atTop (𝓝 ⊤)) : Summable (∏ i in ·, f i) := by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply Summable.of_finite
  refine summable_iff_summable_coeff.mpr fun d => summable_of_hasFiniteSupport ?_
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, eventually_atTop] at h
  obtain ⟨i, hi⟩ := h (Finsupp.weight w d)
  apply (Finset.Iio i).powerset.finite_toSet.subset
  suffices forall s : Finset ι, coeff d (∏ i in s, f i) != 0 -> ↑s subseteq Set.Iio i by simpa
  intro s hs
  contrapose hs
  obtain ⟨x, hxs, hxi⟩ := Set.not_subset.mp hs
  rw [Set.mem_Iio]; rw [not_lt] at hxi
refine coeff_eq_zero_of_lt_weightedOrder w (hi x hxi).trans_le ?_
  apply le_trans (Finset.single_le_sum (by simp) hxs) (le_weightedOrder_prod w _ _)

/--
theorem `summable_prod_of_tendsto_order_atTop_nhds_top` / 定理 `summable_prod_of_tendsto_order_atTop_nhds_top`

English:
theorem summable_prod_of_tendsto_order_atTop_nhds_top
  proof: summable_prod_of_tendsto_weightedOrder_atTop_nhds_top h

中文:
定理 summable_prod_of_tendsto_order_atTop_nhds_top
  证明: summable_prod_of_tendsto_weightedOrder_atTop_nhds_top h

Depends on / 依赖: summable_prod_of_tendsto_weightedOrder_atTop_nhds_top
-/
theorem summable_prod_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i => (f i).order) atTop (𝓝 ⊤)) : Summable (∏ i in ·, f i) :=
  summable_prod_of_tendsto_weightedOrder_atTop_nhds_top h

/--
theorem `multipliable_one_add_of_tendsto_weightedOrder_atTop_nhds_top` / 定理 `multipliable_one_add_of_tendsto_weightedOrder_atTop_nhds_top`

English:
theorem multipliable_one_add_of_tendsto_weightedOrder_atTop_nhds_top
  statement: {w : σ -> Nat}
  proof: multipliable_one_add_of_summable_prod summable_prod_of_tendsto_weightedOrder_atTop_nhds_top h

中文:
定理 multipliable_one_add_of_tendsto_weightedOrder_atTop_nhds_top
  结论: {w : σ -> 自然数}
  证明: multipliable_one_add_of_summable_prod summable_prod_of_tendsto_weightedOrder_atTop_nhds_top h

Depends on / 依赖: multipliable_one_add_of_summable_prod, summable_prod_of_tendsto_weightedOrder_atTop_nhds_top
-/
theorem multipliable_one_add_of_tendsto_weightedOrder_atTop_nhds_top {w : σ -> Nat}
    (h : Tendsto (fun i => weightedOrder w (f i)) atTop (nhds ⊤)) : Multipliable (1 + f ·) :=
multipliable_one_add_of_summable_prod summable_prod_of_tendsto_weightedOrder_atTop_nhds_top h

/--
theorem `multipliable_one_add_of_tendsto_order_atTop_nhds_top` / 定理 `multipliable_one_add_of_tendsto_order_atTop_nhds_top`

English:
theorem multipliable_one_add_of_tendsto_order_atTop_nhds_top
  proof: multipliable_one_add_of_summable_prod summable_prod_of_tendsto_order_atTop_nhds_top h

中文:
定理 multipliable_one_add_of_tendsto_order_atTop_nhds_top
  证明: multipliable_one_add_of_summable_prod summable_prod_of_tendsto_order_atTop_nhds_top h

Depends on / 依赖: multipliable_one_add_of_summable_prod, summable_prod_of_tendsto_order_atTop_nhds_top
-/
theorem multipliable_one_add_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i => (f i).order) atTop (nhds ⊤)) : Multipliable (1 + f ·) :=
multipliable_one_add_of_summable_prod summable_prod_of_tendsto_order_atTop_nhds_top h

end Prod

end Topology

section Uniformity

variable [UniformSpace R]

/-- The componentwise uniformity on `MvPowerSeries` -/
scoped instance : UniformSpace (MvPowerSeries σ R) :=
inferInstanceAs UniformSpace ((σ ->₀ Nat) -> R)

variable (R) in
/--
theorem `uniformContinuous_coeff` / 定理 `uniformContinuous_coeff`

English:
theorem uniformContinuous_coeff
  given: [Semiring R] (d : σ ->₀ Nat)
  proof: uniformContinuous_pi.mp uniformContinuous_id d

中文:
定理 uniformContinuous_coeff
  条件: [半环 R] (d : σ ->₀ 自然数)
  证明: uniformContinuous_pi.mp uniformContinuous_id d

Depends on / 依赖: uniformContinuous_id, uniformContinuous_pi, uniformContinuous_pi.mp
-/
theorem uniformContinuous_coeff [Semiring R] (d : σ ->₀ Nat) :
    UniformContinuous fun f : MvPowerSeries σ R => coeff d f :=
  uniformContinuous_pi.mp uniformContinuous_id d

/-- Completeness of the uniform structure on `MvPowerSeries` -/
@[scoped instance]
/--
theorem `instCompleteSpace` / 定理 `instCompleteSpace`

English:
theorem instCompleteSpace
  given: [CompleteSpace R]
  proof: Pi.complete _

中文:
定理 instCompleteSpace
  条件: [完备空间 R]
  证明: Pi.complete _

Depends on / 依赖: Pi.complete, complete
-/
theorem instCompleteSpace [CompleteSpace R] :
    CompleteSpace (MvPowerSeries σ R) := Pi.complete _

/-- The `IsUniformAddGroup` structure on `MvPowerSeries` of a `IsUniformAddGroup` -/
@[scoped instance]
/--
theorem `instIsUniformAddGroup` / 定理 `instIsUniformAddGroup`

English:
theorem instIsUniformAddGroup
  given: [AddGroup R] [IsUniformAddGroup R]
  proof: Pi.instIsUniformAddGroup

中文:
定理 instIsUniformAddGroup
  条件: [加法群 R] [是UniformAdd群 R]
  证明: Pi.instIsUniformAddGroup

Depends on / 依赖: Pi.instIsUniformAddGroup, instIsUniformAddGroup
-/
theorem instIsUniformAddGroup [AddGroup R] [IsUniformAddGroup R] :
    IsUniformAddGroup (MvPowerSeries σ R) := Pi.instIsUniformAddGroup

end Uniformity

end WithPiTopology

end MvPowerSeries
