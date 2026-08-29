/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Products of finite measures and probability measures

This file introduces finite products of finite measures and probability measures. The constructions
are obtained from special cases of products of general measures. Taking products nevertheless has
specific properties in the cases of finite measures and probability measures, notably the fact that
the product measures depend continuously on their factors in the topology of weak convergence when
the underlying space is metrizable and separable.

## Main definitions

* `MeasureTheory.FiniteMeasure.pi`: The product of finitely many finite measures.
* `MeasureTheory.ProbabilityMeasure.pi`: The product of finitely many probability measures.

## Main results

`MeasureTheory.ProbabilityMeasure.continuous_pi`: the product probability measure depends
continuously on the factors.

-/

@[expose] public section

open MeasureTheory Topology Metric Filter Set ENNReal NNReal

open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

variable {ι : Type*} {α : ι -> Type*} [Fintype ι] [forall i, MeasurableSpace (α i)]

namespace FiniteMeasure

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (μ : Π i, FiniteMeasure (α i))
  body: ⟨Measure.pi (fun i => μ i), inferInstance⟩

中文:
定义 pi
  签名: (μ : Π i, FiniteMeasure (α i))
  定义体: ⟨Measure.pi (fun i => μ i), inferInstance⟩

Depends on / 依赖: Measure, Measure.pi
-/
noncomputable def pi (μ : Π i, FiniteMeasure (α i)) : FiniteMeasure (Π i, α i) :=
  ⟨Measure.pi (fun i => μ i), inferInstance⟩

variable (μ : Π i, FiniteMeasure (α i))

/--
lemma `toMeasure_pi` / 引理 `toMeasure_pi`

English:
lemma toMeasure_pi
  statement: (FiniteMeasure.pi μ).toMeasure = Measure.pi (fun i => μ i)
  proof: rfl

中文:
引理 toMeasure_pi
  结论: (FiniteMeasure.pi μ).toMeasure = Measure.pi (fun i => μ i)
  证明: rfl
-/
@[simp] lemma toMeasure_pi : (FiniteMeasure.pi μ).toMeasure = Measure.pi (fun i => μ i) := rfl

/--
lemma `pi_pi` / 引理 `pi_pi`

English:
lemma pi_pi
  given: (s : Π i, Set (α i))
  proof: by
  simp [coeFn_def]

中文:
引理 pi_pi
  条件: (s : Π i, Set (α i))
  证明: by
  simp [coeFn_def]
-/
@[simp] lemma pi_pi (s : Π i, Set (α i)) :
    (FiniteMeasure.pi μ) (Set.pi univ s) = ∏ i, μ i (s i) := by
  simp [coeFn_def]

/--
lemma `mass_pi` / 引理 `mass_pi`

English:
lemma mass_pi
  statement: (FiniteMeasure.pi μ).mass = ∏ i, (μ i).mass
  proof: by
  simp only [mass]
  rw [← pi_univ (univ : Set ι)]; rw [pi_pi]

中文:
引理 mass_pi
  结论: (FiniteMeasure.pi μ).mass = ∏ i, (μ i).mass
  证明: by
  simp only [mass]
  rw [← pi_univ (univ : Set ι)]; rw [pi_pi]
-/
@[simp] lemma mass_pi : (FiniteMeasure.pi μ).mass = ∏ i, (μ i).mass := by
  simp only [mass]
  rw [← pi_univ (univ : Set ι)]; rw [pi_pi]

/--
lemma `pi_map_pi` / 引理 `pi_map_pi`

English:
lemma pi_map_pi
  statement: {β : ι -> Type*} [forall i, MeasurableSpace (β i)] {f : Π i, α i -> β i}
  proof: by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_map, toMeasure_pi]
  rw [Measure.pi_map_pi f_mble]

中文:
引理 pi_map_pi
  结论: {β : ι -> 类型} [对任意 i, MeasurableSpace (β i)] {f : Π i, α i -> β i}
  证明: by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_map, toMeasure_pi]
  rw [Measure.pi_map_pi f_mble]

Depends on / 依赖: Measure, Measure.pi_map_pi, Subtype, Subtype.ext, f_mble, pi_map_pi, toMeasure_map, toMeasure_pi, val_eq_toMeasure
-/
lemma pi_map_pi {β : ι -> Type*} [forall i, MeasurableSpace (β i)] {f : Π i, α i -> β i}
    (f_mble : forall i, AEMeasurable (f i) (μ i)) :
    (FiniteMeasure.pi μ).map (fun x i => (f i (x i))) =
      FiniteMeasure.pi (fun i => (μ i).map (f i)) := by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_map, toMeasure_pi]
  rw [Measure.pi_map_pi f_mble]

end FiniteMeasure

namespace ProbabilityMeasure

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (μ : Π i, ProbabilityMeasure (α i))
  body: ⟨Measure.pi (fun i => μ i), inferInstance⟩

中文:
定义 pi
  签名: (μ : Π i, ProbabilityMeasure (α i))
  定义体: ⟨Measure.pi (fun i => μ i), inferInstance⟩

Depends on / 依赖: Measure, Measure.pi
-/
noncomputable def pi (μ : Π i, ProbabilityMeasure (α i)) : ProbabilityMeasure (Π i, α i) :=
  ⟨Measure.pi (fun i => μ i), inferInstance⟩

variable (μ : Π i, ProbabilityMeasure (α i))

/--
lemma `toMeasure_pi` / 引理 `toMeasure_pi`

English:
lemma toMeasure_pi
  proof: rfl

中文:
引理 toMeasure_pi
  证明: rfl
-/
@[simp] lemma toMeasure_pi :
    (ProbabilityMeasure.pi μ).toMeasure = Measure.pi (fun i => μ i) := rfl

/--
lemma `pi_pi` / 引理 `pi_pi`

English:
lemma pi_pi
  given: (s : Π i, Set (α i))
  proof: by
  simp [coeFn_def]

中文:
引理 pi_pi
  条件: (s : Π i, Set (α i))
  证明: by
  simp [coeFn_def]
-/
@[simp] lemma pi_pi (s : Π i, Set (α i)) :
    ProbabilityMeasure.pi μ (Set.pi univ s) = ∏ i, μ i (s i) := by
  simp [coeFn_def]

open TopologicalSpace

/-- The map associating to finitely many probability measures their product is a continuous map. -/
@[fun_prop]
/--
theorem `continuous_pi` / 定理 `continuous_pi`

English:
theorem continuous_pi
  statement: [forall i, TopologicalSpace (α i)] [forall i, SecondCountableTopology (α i)]
  proof: by
  refine continuous_iff_continuousAt.2 (fun μ => ?_)
  /- It suffices to check the convergence along elements of a π-system containing arbitrarily
  small neighborhoods of any point, by `tendsto_probabilityMeasure_of_tendsto_of_mem`.
  We take as a π-system the sets of the form `s₁ × ... × sₙ` wh

中文:
定理 continuous_pi
  结论: [对任意 i, TopologicalSpace (α i)] [对任意 i, SecondCountableTopology (α i)]
  证明: by
  refine continuous_iff_continuousAt.2 (fun μ => ?_)
  /- It suffices to check the convergence along elements of a π-system containing arbitrarily
  small neighborhoods of any point, by `tendsto_probabilityMeasure_of_tendsto_of_mem`.
  We take as a π-system the sets of the form `s₁ × ... × sₙ` wh

Depends on / 依赖: continuous_iff_continuousAt
-/
theorem continuous_pi [forall i, TopologicalSpace (α i)] [forall i, SecondCountableTopology (α i)]
    [forall i, PseudoMetrizableSpace (α i)] [forall i, OpensMeasurableSpace (α i)] :
    Continuous (fun (μ : Π i, ProbabilityMeasure (α i)) => ProbabilityMeasure.pi μ) := by
  refine continuous_iff_continuousAt.2 (fun μ => ?_)
  /- It suffices to check the convergence along elements of a π-system containing arbitrarily
  small neighborhoods of any point, by `tendsto_probabilityMeasure_of_tendsto_of_mem`.
  We take as a π-system the sets of the form `s₁ × ... × sₙ` where all the `sᵢ` have
  null frontier. -/
  let S : Set (Set (Π i, α i)) := {t | exists (s : Π i, Set (α i)), t = univ.pi s ∧
    (forall i, MeasurableSet (s i)) ∧ (forall i, μ i (frontier (s i)) = 0)}
  have : IsPiSystem S := by
    rintro - ⟨s, rfl, smeas, hs⟩ - ⟨s', rfl, s'meas, hs'⟩ -
    refine ⟨fun i => s i inter s' i, pi_inter_distrib.symm, fun i => (smeas i).inter (s'meas i),
      fun i => ?_⟩
    simp_rw [null_iff_toMeasure_null] at hs hs' ⊢
    exact null_frontier_inter (hs i) (hs' i)
  apply this.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro - ⟨s, rfl, smeas, hs⟩
    exact MeasurableSet.univ_pi smeas
  · let : forall i, PseudoMetricSpace (α i) :=
      fun i => TopologicalSpace.pseudoMetrizableSpacePseudoMetric (α i)
    intro u u_open x xu
    obtain ⟨ε, εpos, hε⟩ : exists ε > 0, ball x ε subseteq u := Metric.isOpen_iff.1 u_open x xu
    have A (i) : exists r in Ioo 0 ε, (μ i : Measure (α i)) (frontier (Metric.thickening r {x i})) = 0 :=
      exists_null_frontier_thickening _ _ εpos
    choose! r rpos hr using A
    refine ⟨univ.pi (fun i => ball (x i) (r i)), ⟨fun i => ball (x i) (r i), rfl,
      fun i => measurableSet_ball, fun i => by simpa using hr i⟩, ?_, ?_⟩
    · apply IsOpen.mem_nhds
      · exact isOpen_set_pi finite_univ (by simp)
      · simpa using fun i => (rpos i).1
    · calc univ.pi fun i => ball (x i) (r i)
      _ subseteq univ.pi fun i => ball (x i) ε := by gcongr with i hi; exact (rpos i).2.le
      _ subseteq u := by rwa [← ball_pi _ εpos]
  · rintro - ⟨s, rfl, smeas, hs⟩
    simp only [pi_pi]
    apply tendsto_finsetProd _ (fun i hi => ?_)
    exact tendsto_measure_of_null_frontier_of_tendsto (Tendsto.apply_nhds (fun ⦃U⦄ a => a) i) (hs i)

end ProbabilityMeasure

end MeasureTheory
