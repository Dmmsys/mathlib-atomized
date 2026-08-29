/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto, Oliver Butterley
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
public import Mathlib.Order.Interval.Set.Union

/-!
# Riesz–Markov–Kakutani representation theorem for real-linear functionals

The Riesz–Markov–Kakutani representation theorem relates linear functionals on spaces of continuous
functions on a locally compact space to measures.

There are many closely related variations of the theorem. This file contains the proof of the
version where the space is a locally compact T2 space, the linear functionals are real and the
continuous functions have compact support.

## Main definitions & statements

* `RealRMK.rieszMeasure`: the measure induced by a real linear positive functional.
* `RealRMK.integral_rieszMeasure`: the Riesz–Markov–Kakutani representation theorem for a real
  linear positive functional.
* `RealRMK.rieszMeasure_integralPositiveLinearMap`: the uniqueness of the representing measure in
  the Riesz–Markov–Kakutani representation theorem.

## Implementation notes

The measure is defined through `rieszContent` which is for `NNReal` using the `toNNRealLinear`
version of `Λ`.

The Riesz–Markov–Kakutani representation theorem is first proved for `Real`-linear `Λ` because
equality is proven using two inequalities by considering `Λ f` and `Λ (-f)` for all functions
`f`, yet on `C_c(X, ℝ≥0)` there is no negation.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]
-/

@[expose] public section

open scoped ENNReal BoundedContinuousFunction
open CompactlySupported CompactlySupportedContinuousMap Filter Function Set Topology
  TopologicalSpace MeasureTheory

namespace RealRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]
variable (Λ : C_c(X, Real) ->ₚ[Real] Real)

section Construction

variable [LocallyCompactSpace X]

/--
Definition of `rieszMeasure` / `rieszMeasure` 的定义

English:
definition rieszMeasure
  body: (rieszContent (toNNRealLinear Λ)).measure

中文:
定义 rieszMeasure
  定义体: (rieszContent (toNNRealLinear Λ)).measure

Depends on / 依赖: measure, rieszContent, toNNRealLinear
-/
noncomputable def rieszMeasure := (rieszContent (toNNRealLinear Λ)).measure

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `le_rieszMeasure_tsupport_subset` / 引理 `le_rieszMeasure_tsupport_subset`

English:
lemma le_rieszMeasure_tsupport_subset
  statement: {f : C_c(X, Real)} (hf : forall (x : X), 0 <= f x ∧ f x <= 1)
  proof: by
  apply le_trans _ (measure_mono hV)
  have := Content.measure_eq_content_of_regular (rieszContent (toNNRealLinear Λ))
    (contentRegular_rieszContent (toNNRealLinear Λ)) (⟨tsupport f, f.hasCompactSupport⟩)
  rw [← Compacts.coe_mk (tsupport f) f.hasCompactSupport]; rw [rieszMeasure]; rw [this]; rw [rieszContent]; rw [ENNReal.ofReal_eq_coe_nnreal (Λ.map_nonneg fun x => (hf x).1)]; rw [Content.mk_apply]; rw [ENNReal.coe_le_coe]
  apply le_iff_forall_pos_le_add.mpr
  intro _ hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos (toNNRealLinear Λ)
    ⟨tsupport f, f.hasCompactSupport⟩ (Real.toNNReal_pos.mpr hε)
  simp_rw [NNReal.val_eq_coe, Real.toNNReal_coe] at hg
  refine (Λ.mono ?_).trans hg.2.le
  intro x
  by_cases hx : x in tsupport f
  · simpa using le_trans (hf x).2 (hg.1 x hx)
  · simp [image_eq_zero_of_notMem_tsupport hx]

中文:
引理 le_rieszMeasure_tsupport_subset
  结论: {f : C_c(X, 实数)} (hf : 对任意 (x : X), 0 <= f x ∧ f x <= 1)
  证明: by
  apply le_trans _ (measure_mono hV)
  have := Content.measure_eq_content_of_regular (rieszContent (toNNRealLinear Λ))
    (contentRegular_rieszContent (toNNRealLinear Λ)) (⟨tsupport f, f.hasCompactSupport⟩)
  rw [← Compacts.coe_mk (tsupport f) f.hasCompactSupport]; rw [rieszMeasure]; rw [this]; rw [rieszContent]; rw [ENNReal.ofReal_eq_coe_nnreal (Λ.map_nonneg fun x => (hf x).1)]; rw [Content.mk_apply]; rw [ENNReal.coe_le_coe]
  apply le_iff_forall_pos_le_add.mpr
  intro _ hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos (toNNRealLinear Λ)
    ⟨tsupport f, f.hasCompactSupport⟩ (Real.toNNReal_pos.mpr hε)
  simp_rw [NNReal.val_eq_coe, Real.toNNReal_coe] at hg
  refine (Λ.mono ?_).trans hg.2.le
  intro x
  by_cases hx : x in tsupport f
  · simpa using le_trans (hf x).2 (hg.1 x hx)
  · simp [image_eq_zero_of_notMem_tsupport hx]

Depends on / 依赖: Compacts, Compacts.coe_mk, Content, Content.measure_eq_content_of_regular, Content.mk_apply, ENNReal, ENNReal.coe_le_coe, ENNReal.ofReal_eq_coe_nnreal, coe_le_coe, coe_mk, contentRegular_rieszContent, exists_lt_ri, f.hasCompactSupport, hasCompactSupport, le_iff_forall_pos_le_add, le_iff_forall_pos_le_add.mpr, le_trans, map_nonneg, measure_eq_content_of_regular, measure_mono
-/
lemma le_rieszMeasure_tsupport_subset {f : C_c(X, Real)} (hf : forall (x : X), 0 <= f x ∧ f x <= 1)
    {V : Set X} (hV : tsupport f subseteq V) : ENNReal.ofReal (Λ f) <= rieszMeasure Λ V := by
  apply le_trans _ (measure_mono hV)
  have := Content.measure_eq_content_of_regular (rieszContent (toNNRealLinear Λ))
    (contentRegular_rieszContent (toNNRealLinear Λ)) (⟨tsupport f, f.hasCompactSupport⟩)
  rw [← Compacts.coe_mk (tsupport f) f.hasCompactSupport]; rw [rieszMeasure]; rw [this]; rw [rieszContent]; rw [ENNReal.ofReal_eq_coe_nnreal (Λ.map_nonneg fun x => (hf x).1)]; rw [Content.mk_apply]; rw [ENNReal.coe_le_coe]
  apply le_iff_forall_pos_le_add.mpr
  intro _ hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos (toNNRealLinear Λ)
    ⟨tsupport f, f.hasCompactSupport⟩ (Real.toNNReal_pos.mpr hε)
  simp_rw [NNReal.val_eq_coe, Real.toNNReal_coe] at hg
  refine (Λ.mono ?_).trans hg.2.le
  intro x
  by_cases hx : x in tsupport f
  · simpa using le_trans (hf x).2 (hg.1 x hx)
  · simp [image_eq_zero_of_notMem_tsupport hx]

/--
lemma `rieszMeasure_le_of_eq_one` / 引理 `rieszMeasure_le_of_eq_one`

English:
lemma rieszMeasure_le_of_eq_one
  statement: {f : C_c(X, Real)} (hf : forall x, 0 <= f x) {K : Set X}
  proof: by
  rw [← Compacts.coe_mk K hK]; rw [rieszMeasure]; rw [Content.measure_eq_content_of_regular _ (contentRegular_rieszContent (toNNRealLinear Λ))]
  apply ENNReal.coe_le_iff.mpr
  intro p hp
  rw [← ENNReal.ofReal_coe_nnreal]; rw [ENNReal.ofReal_eq_ofReal_iff (Λ.map_nonneg hf) NNReal.zero_le_coe] at hp
  apply csInf_le'
  rw [Set.mem_image]
  use f.nnrealPart
  simp_rw [Set.mem_ofPred_eq, nnrealPart_apply, Real.one_le_toNNReal]
  refine ⟨(fun x hx => Eq.ge (hfK x hx)), ?_⟩
  apply NNReal.eq
  rw [toNNRealLinear_apply]; rw [show f.nnrealPart.toReal = f by ext z; simp [hf z], hp]

omit [T2Space X] [LocallyCompactSpace X] in

中文:
引理 rieszMeasure_le_of_eq_one
  结论: {f : C_c(X, 实数)} (hf : 对任意 x, 0 <= f x) {K : 集合 X}
  证明: by
  rw [← Compacts.coe_mk K hK]; rw [rieszMeasure]; rw [Content.measure_eq_content_of_regular _ (contentRegular_rieszContent (toNNRealLinear Λ))]
  apply ENNReal.coe_le_iff.mpr
  intro p hp
  rw [← ENNReal.ofReal_coe_nnreal]; rw [ENNReal.ofReal_eq_ofReal_iff (Λ.map_nonneg hf) NNReal.zero_le_coe] at hp
  apply csInf_le'
  rw [Set.mem_image]
  use f.nnrealPart
  simp_rw [Set.mem_ofPred_eq, nnrealPart_apply, Real.one_le_toNNReal]
  refine ⟨(fun x hx => Eq.ge (hfK x hx)), ?_⟩
  apply NNReal.eq
  rw [toNNRealLinear_apply]; rw [show f.nnrealPart.toReal = f by ext z; simp [hf z], hp]

omit [T2Space X] [LocallyCompactSpace X] in

Depends on / 依赖: Compacts, Compacts.coe_mk, Content, Content.measure_eq_content_of_regular, ENNReal, ENNReal.coe_le_iff.mpr, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_eq_ofReal_iff, Eq.ge, NNReal, NNReal.eq, NNReal.zero_le_coe, Real.one_le_toNNReal, Set.mem_image, Set.mem_ofPred_eq, coe_le_iff, coe_mk, contentRegular_rieszContent, csInf_le, f.nnrealPart
-/
lemma rieszMeasure_le_of_eq_one {f : C_c(X, Real)} (hf : forall x, 0 <= f x) {K : Set X}
    (hK : IsCompact K) (hfK : forall x in K, f x = 1) : rieszMeasure Λ K <= ENNReal.ofReal (Λ f) := by
  rw [← Compacts.coe_mk K hK]; rw [rieszMeasure]; rw [Content.measure_eq_content_of_regular _ (contentRegular_rieszContent (toNNRealLinear Λ))]
  apply ENNReal.coe_le_iff.mpr
  intro p hp
  rw [← ENNReal.ofReal_coe_nnreal]; rw [ENNReal.ofReal_eq_ofReal_iff (Λ.map_nonneg hf) NNReal.zero_le_coe] at hp
  apply csInf_le'
  rw [Set.mem_image]
  use f.nnrealPart
  simp_rw [Set.mem_ofPred_eq, nnrealPart_apply, Real.one_le_toNNReal]
  refine ⟨(fun x hx => Eq.ge (hfK x hx)), ?_⟩
  apply NNReal.eq
  rw [toNNRealLinear_apply]; rw [show f.nnrealPart.toReal = f by ext z; simp [hf z], hp]

omit [T2Space X] [LocallyCompactSpace X] in
/--
lemma `range_cut_partition` / 引理 `range_cut_partition`

English:
lemma range_cut_partition
  statement: (f : C_c(X, Real)) (a : Real) {ε : Real} (hε : 0 < ε) (N : Nat)
  proof: by
  let b := a + N * ε
  let y : Fin N -> Real := fun n => a + ε * (n + 1)
  -- By definition `y n` and `y m` are separated by at least `ε`.
  have hy {n m : Fin N} (h : n < m) : y n + ε <= y m := calc
    _ <= a + ε * m + ε := by
      exact add_le_add_three (by rfl) ((mul_le_mul_iff_of_pos_left hε).mpr (by norm_cast)) (by rfl)
    _ = _ := by dsimp [y]; rw [mul_add, mul_one, add_assoc]
  -- Define `E n` as the inverse image of the interval `(y n - ε, y n]`.
  let E (n : Fin N) := (f ⁻¹' Ioc (y n - ε) (y n)) inter (tsupport f)
  use E
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The sets `E n` are a partition of the support of `f`.
    have partition_aux : range f subseteq ⋃ n, Ioc (y n - ε) (y n) := calc
      _ subseteq Ioc (a + (0 : Nat) * ε) (a + N * ε) := by
        intro _ hz
        simpa using Ioo_subset_Ioc_self (hf hz)
      _ subseteq ⋃ i in Finset.range N, Ioc (a + ↑i * ε) (a + ↑(i + 1) * ε) :=
        Ioc_subset_biUnion_Ioc N (fun n => a + n * ε)
      _ subseteq _ := by
        intro z
        simp only [Finset.mem_range, mem_iUnion, mem_Ioc, forall_exists_index, and_imp, y]
        refine fun n hn _ _ => ⟨⟨n, hn⟩, ⟨by linarith, by simp_all [mul_comm ε _]⟩⟩
    simp only [E, ← iUnion_inter, ← preimage_iUnion, eq_comm (a := tsupport _), inter_eq_right]
    exact fun x _ => partition_aux (mem_range_self x)
  · -- The sets `E n` are pairwise disjoint.
    intro m _ n _ hmn
    apply Disjoint.preimage
    simp_rw [mem_preimage, mem_Ioc, disjoint_left]
    intro x hx
    rw [mem_ofPred_eq]; rw [and_assoc] at hx
    simp_rw [mem_ofPred_eq, not_and_or, not_lt, not_le, or_assoc]
    rcases (by lia : m < n ∨ n < m) with hc | hc
    · left
      exact le_trans hx.2.1 (le_tsub_of_add_le_right (hy hc))
    · right; left
      exact lt_of_le_of_lt (le_tsub_of_add_le_right (hy hc)) hx.1
  · -- Upper and lower bound on `f x` follow from the definition of `E n` .
    intro _ _ hx
    simp only [mem_inter_iff, mem_preimage, mem_Ioc, E, y] at hx
    constructor <;> linarith
  · exact fun _ => (f.1.measurable measurableSet_Ioc).inter measurableSet_closure

omit [LocallyCompactSpace X] in

中文:
引理 range_cut_partition
  结论: (f : C_c(X, 实数)) (a : 实数) {ε : 实数} (hε : 0 < ε) (N : 自然数)
  证明: by
  let b := a + N * ε
  let y : Fin N -> Real := fun n => a + ε * (n + 1)
  -- By definition `y n` and `y m` are separated by at least `ε`.
  have hy {n m : Fin N} (h : n < m) : y n + ε <= y m := calc
    _ <= a + ε * m + ε := by
      exact add_le_add_three (by rfl) ((mul_le_mul_iff_of_pos_left hε).mpr (by norm_cast)) (by rfl)
    _ = _ := by dsimp [y]; rw [mul_add, mul_one, add_assoc]
  -- Define `E n` as the inverse image of the interval `(y n - ε, y n]`.
  let E (n : Fin N) := (f ⁻¹' Ioc (y n - ε) (y n)) inter (tsupport f)
  use E
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The sets `E n` are a partition of the support of `f`.
    have partition_aux : range f subseteq ⋃ n, Ioc (y n - ε) (y n) := calc
      _ subseteq Ioc (a + (0 : Nat) * ε) (a + N * ε) := by
        intro _ hz
        simpa using Ioo_subset_Ioc_self (hf hz)
      _ subseteq ⋃ i in Finset.range N, Ioc (a + ↑i * ε) (a + ↑(i + 1) * ε) :=
        Ioc_subset_biUnion_Ioc N (fun n => a + n * ε)
      _ subseteq _ := by
        intro z
        simp only [Finset.mem_range, mem_iUnion, mem_Ioc, forall_exists_index, and_imp, y]
        refine fun n hn _ _ => ⟨⟨n, hn⟩, ⟨by linarith, by simp_all [mul_comm ε _]⟩⟩
    simp only [E, ← iUnion_inter, ← preimage_iUnion, eq_comm (a := tsupport _), inter_eq_right]
    exact fun x _ => partition_aux (mem_range_self x)
  · -- The sets `E n` are pairwise disjoint.
    intro m _ n _ hmn
    apply Disjoint.preimage
    simp_rw [mem_preimage, mem_Ioc, disjoint_left]
    intro x hx
    rw [mem_ofPred_eq]; rw [and_assoc] at hx
    simp_rw [mem_ofPred_eq, not_and_or, not_lt, not_le, or_assoc]
    rcases (by lia : m < n ∨ n < m) with hc | hc
    · left
      exact le_trans hx.2.1 (le_tsub_of_add_le_right (hy hc))
    · right; left
      exact lt_of_le_of_lt (le_tsub_of_add_le_right (hy hc)) hx.1
  · -- Upper and lower bound on `f x` follow from the definition of `E n` .
    intro _ _ hx
    simp only [mem_inter_iff, mem_preimage, mem_Ioc, E, y] at hx
    constructor <;> linarith
  · exact fun _ => (f.1.measurable measurableSet_Ioc).inter measurableSet_closure

omit [LocallyCompactSpace X] in
-/
lemma range_cut_partition (f : C_c(X, Real)) (a : Real) {ε : Real} (hε : 0 < ε) (N : Nat)
    (hf : range f subseteq Ioo a (a + N * ε)) : exists (E : Fin N -> Set X), tsupport f = ⋃ j, E j ∧
    univ.PairwiseDisjoint E ∧ (forall n : Fin N, forall x in E n, a + ε * n < f x ∧ f x <= a + ε * (n + 1)) ∧
    forall n : Fin N, MeasurableSet (E n) := by
  let b := a + N * ε
  let y : Fin N -> Real := fun n => a + ε * (n + 1)
  -- By definition `y n` and `y m` are separated by at least `ε`.
  have hy {n m : Fin N} (h : n < m) : y n + ε <= y m := calc
    _ <= a + ε * m + ε := by
      exact add_le_add_three (by rfl) ((mul_le_mul_iff_of_pos_left hε).mpr (by norm_cast)) (by rfl)
    _ = _ := by dsimp [y]; rw [mul_add, mul_one, add_assoc]
  -- Define `E n` as the inverse image of the interval `(y n - ε, y n]`.
  let E (n : Fin N) := (f ⁻¹' Ioc (y n - ε) (y n)) inter (tsupport f)
  use E
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The sets `E n` are a partition of the support of `f`.
    have partition_aux : range f subseteq ⋃ n, Ioc (y n - ε) (y n) := calc
      _ subseteq Ioc (a + (0 : Nat) * ε) (a + N * ε) := by
        intro _ hz
        simpa using Ioo_subset_Ioc_self (hf hz)
      _ subseteq ⋃ i in Finset.range N, Ioc (a + ↑i * ε) (a + ↑(i + 1) * ε) :=
        Ioc_subset_biUnion_Ioc N (fun n => a + n * ε)
      _ subseteq _ := by
        intro z
        simp only [Finset.mem_range, mem_iUnion, mem_Ioc, forall_exists_index, and_imp, y]
        refine fun n hn _ _ => ⟨⟨n, hn⟩, ⟨by linarith, by simp_all [mul_comm ε _]⟩⟩
    simp only [E, ← iUnion_inter, ← preimage_iUnion, eq_comm (a := tsupport _), inter_eq_right]
    exact fun x _ => partition_aux (mem_range_self x)
  · -- The sets `E n` are pairwise disjoint.
    intro m _ n _ hmn
    apply Disjoint.preimage
    simp_rw [mem_preimage, mem_Ioc, disjoint_left]
    intro x hx
    rw [mem_ofPred_eq]; rw [and_assoc] at hx
    simp_rw [mem_ofPred_eq, not_and_or, not_lt, not_le, or_assoc]
    rcases (by lia : m < n ∨ n < m) with hc | hc
    · left
      exact le_trans hx.2.1 (le_tsub_of_add_le_right (hy hc))
    · right; left
      exact lt_of_le_of_lt (le_tsub_of_add_le_right (hy hc)) hx.1
  · -- Upper and lower bound on `f x` follow from the definition of `E n` .
    intro _ _ hx
    simp only [mem_inter_iff, mem_preimage, mem_Ioc, E, y] at hx
    constructor <;> linarith
  · exact fun _ => (f.1.measurable measurableSet_Ioc).inter measurableSet_closure

omit [LocallyCompactSpace X] in
/--
lemma `exists_open_approx` / 引理 `exists_open_approx`

English:
lemma exists_open_approx
  statement: (f : C_c(X, Real)) {ε : Real} (hε : 0 < ε) (E : Set X) {μ : Content X}
  proof: by
have hε' := ne_of_gt Real.toNNReal_pos.mpr hε
  obtain ⟨V₁ : Opens X, hV₁⟩ := Content.outerMeasure_exists_open μ hμ hε'
  let V₂ : Opens X := ⟨(f ⁻¹' Iio c), IsOpen.preimage f.1.2 isOpen_Iio⟩
  use V₁ ⊓ V₂
  refine ⟨subset_inter hV₁.1 hfE, ?_, ?_⟩
  · intro x hx
    suffices forall x in V₂.carrier, f x < c from this x (mem_of_mem_inter_right hx)
    exact fun _ a => a
  · calc
      _ <= μ.measure V₁ := by simp [measure_mono]
      _ = μ.outerMeasure V₁ := Content.measure_apply μ (V₁.2.measurableSet)
      _ <= μ.outerMeasure E + ε.toNNReal := hV₁.2
      _ = _ := by rw [Content.measure_apply μ hμ', ENNReal.ofNNReal_toNNReal]

中文:
引理 存在_open_approx
  结论: (f : C_c(X, 实数)) {ε : 实数} (hε : 0 < ε) (E : 集合 X) {μ : 内容 X}
  证明: by
have hε' := ne_of_gt Real.toNNReal_pos.mpr hε
  obtain ⟨V₁ : Opens X, hV₁⟩ := Content.outerMeasure_exists_open μ hμ hε'
  let V₂ : Opens X := ⟨(f ⁻¹' Iio c), IsOpen.preimage f.1.2 isOpen_Iio⟩
  use V₁ ⊓ V₂
  refine ⟨subset_inter hV₁.1 hfE, ?_, ?_⟩
  · intro x hx
    suffices forall x in V₂.carrier, f x < c from this x (mem_of_mem_inter_right hx)
    exact fun _ a => a
  · calc
      _ <= μ.measure V₁ := by simp [measure_mono]
      _ = μ.outerMeasure V₁ := Content.measure_apply μ (V₁.2.measurableSet)
      _ <= μ.outerMeasure E + ε.toNNReal := hV₁.2
      _ = _ := by rw [Content.measure_apply μ hμ', ENNReal.ofNNReal_toNNReal]

Depends on / 依赖: Content, Content.measure_apply, Content.outerMeasure_exists_open, IsOpen, IsOpen.preimage, Real.toNNReal_pos.mpr, carrier, isOpen_Iio, measurableSet, measure, measure_apply, measure_mono, mem_of_mem_inter_right, ne_of_gt, outerMeasure, outerMeasure_exists_open, preimage, subset_inter, toNNReal_pos
-/
lemma exists_open_approx (f : C_c(X, Real)) {ε : Real} (hε : 0 < ε) (E : Set X) {μ : Content X}
    (hμ : μ.outerMeasure E != ∞) (hμ' : MeasurableSet E) {c : Real} (hfE : forall x in E, f x < c) :
    exists (V : Opens X), E subseteq V ∧ (forall x in V, f x < c) ∧ μ.measure V <= μ.measure E + ENNReal.ofReal ε := by
have hε' := ne_of_gt Real.toNNReal_pos.mpr hε
  obtain ⟨V₁ : Opens X, hV₁⟩ := Content.outerMeasure_exists_open μ hμ hε'
  let V₂ : Opens X := ⟨(f ⁻¹' Iio c), IsOpen.preimage f.1.2 isOpen_Iio⟩
  use V₁ ⊓ V₂
  refine ⟨subset_inter hV₁.1 hfE, ?_, ?_⟩
  · intro x hx
    suffices forall x in V₂.carrier, f x < c from this x (mem_of_mem_inter_right hx)
    exact fun _ a => a
  · calc
      _ <= μ.measure V₁ := by simp [measure_mono]
      _ = μ.outerMeasure V₁ := Content.measure_apply μ (V₁.2.measurableSet)
      _ <= μ.outerMeasure E + ε.toNNReal := hV₁.2
      _ = _ := by rw [Content.measure_apply μ hμ', ENNReal.ofNNReal_toNNReal]

/--
lemma `exists_nat_large` / 引理 `exists_nat_large`

English:
lemma exists_nat_large
  given: (a' b' : Real) {ε : Real} (hε : 0 < ε)
  statement: exists (N : Nat), 0 < N ∧
  proof: by
  have A : Tendsto (fun (N : Real) => a' / N * (b' + a' / N)) atTop (𝓝 (0 * (b' + 0))) := by
    apply Tendsto.mul
    · exact Tendsto.div_atTop tendsto_const_nhds tendsto_id
    · exact Tendsto.add tendsto_const_nhds (Tendsto.div_atTop tendsto_const_nhds tendsto_id)
  have B := A.comp tendsto_natCast_atTop_atTop
  simp only [add_zero, zero_mul] at B
  obtain ⟨N, hN, h'N⟩ := (((tendsto_order.1 B).2 _ hε).and (Ici_mem_atTop 1)).exists
  exact ⟨N, h'N, hN.le⟩

中文:
引理 存在_nat_large
  条件: (a' b' : 实数) {ε : 实数} (hε : 0 < ε)
  结论: 存在 (N : 自然数), 0 < N ∧
  证明: by
  have A : Tendsto (fun (N : Real) => a' / N * (b' + a' / N)) atTop (𝓝 (0 * (b' + 0))) := by
    apply Tendsto.mul
    · exact Tendsto.div_atTop tendsto_const_nhds tendsto_id
    · exact Tendsto.add tendsto_const_nhds (Tendsto.div_atTop tendsto_const_nhds tendsto_id)
  have B := A.comp tendsto_natCast_atTop_atTop
  simp only [add_zero, zero_mul] at B
  obtain ⟨N, hN, h'N⟩ := (((tendsto_order.1 B).2 _ hε).and (Ici_mem_atTop 1)).exists
  exact ⟨N, h'N, hN.le⟩
-/
private lemma exists_nat_large (a' b' : Real) {ε : Real} (hε : 0 < ε) : exists (N : Nat), 0 < N ∧
    a' / N * (b' + a' / N) <= ε := by
  have A : Tendsto (fun (N : Real) => a' / N * (b' + a' / N)) atTop (𝓝 (0 * (b' + 0))) := by
    apply Tendsto.mul
    · exact Tendsto.div_atTop tendsto_const_nhds tendsto_id
    · exact Tendsto.add tendsto_const_nhds (Tendsto.div_atTop tendsto_const_nhds tendsto_id)
  have B := A.comp tendsto_natCast_atTop_atTop
  simp only [add_zero, zero_mul] at B
  obtain ⟨N, hN, h'N⟩ := (((tendsto_order.1 B).2 _ hε).and (Ici_mem_atTop 1)).exists
  exact ⟨N, h'N, hN.le⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `integral_riesz_aux` / 引理 `integral_riesz_aux`

English:
lemma integral_riesz_aux
  given: (f : C_c(X, Real))
  statement: Λ f <= ∫ x, f x ∂(rieszMeasure Λ)
  proof: by
  let μ := rieszMeasure Λ
  let K := tsupport f
  -- Suffices to show that `Λ f ≤ ∫ x, f x ∂μ + ε` for arbitrary `ε`.
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  -- Choose an interval `(a, b)` which contains the range of `f`.
  obtain ⟨a, b, hab⟩ : exists a b : Real, a < b ∧ range f subseteq Ioo a b := by
    obtain ⟨r, hr⟩ := (Metric.isCompact_iff_isClosed_bounded.mp
      (HasCompactSupport.isCompact_range f.2 f.1.2)).2.subset_ball_lt 0 0
    exact ⟨-r, r, by linarith, hr.2.trans_eq (by simp [Real.ball_eq_Ioo])⟩
  -- Choose `N` positive and sufficiently large such that `ε'` is sufficiently small
  obtain ⟨N, hN, hε'⟩ := exists_nat_large (b - a) (2 * μ.real K + |a| + b) hε
  let ε' := (b - a) / N
  replace hε' : 0 < ε' ∧ ε' * (2 * μ.real K + |a| + b + ε') <= ε :=
    ⟨div_pos (sub_pos.mpr hab.1) (Nat.cast_pos'.mpr hN), hε'⟩
  -- Take a partition of the support of `f` into sets `E` by partitioning the range.
obtain ⟨E, hE⟩ := range_cut_partition f a hε'.1 N by
    dsimp [ε']
    field_simp
    simp [hab.2]
  -- Introduce notation for the partition of the range.
  let y : Fin N -> Real := fun n => a + ε' * (n + 1)
  -- The measure of each `E n` is finite.
  have hE' (n : Fin N) : μ (E n) != ∞ := by
    have h : E n subseteq tsupport f := by rw [hE.1]; exact subset_iUnion _ _
    refine lt_top_iff_ne_top.mp ?_
apply lt_of_le_of_lt measure_mono h
    dsimp [μ]
    rw [rieszMeasure]; rw [← coe_toContinuousMap]; rw [← ContinuousMap.toFun_eq_coe]; rw [Content.measure_apply _ f.2.measurableSet]
    exact Content.outerMeasure_lt_top_of_isCompact _ f.2
  -- Define sets `V` which are open approximations to the sets `E`
  obtain ⟨V, hV⟩ : exists V : Fin N -> Opens X, forall n, E n subseteq (V n) ∧ (forall x in V n, f x < y n + ε') ∧
      μ (V n) <= μ (E n) + ENNReal.ofReal (ε' / N) := by
    have h_ε' := (div_pos hε'.1 (Nat.cast_pos'.mpr hN))
    have h n x (hx : x in E n) := lt_add_of_le_of_pos ((hE.2.2.1 n x hx).right) hε'.1
    have h' n := Eq.trans_ne
      (Content.measure_apply (rieszContent (toNNRealLinear Λ)) (hE.2.2.2 n)).symm (hE' n)
    choose V hV using fun n => exists_open_approx f h_ε' (E n) (h' n) (hE.2.2.2 n) (h n)
    exact ⟨V, hV⟩
  -- Define a partition of unity subordinated to the sets `V`
  obtain ⟨g, hg⟩ : exists g : Fin N -> C_c(X, Real), (forall n, tsupport (g n) subseteq (V n).carrier) ∧
      EqOn (∑ n : Fin N, (g n)) 1 (tsupport f.toFun) ∧ (forall n x, (g n) x in Icc 0 1) ∧
      forall n, HasCompactSupport (g n) := by
    have : tsupport f subseteq ⋃ n, (V n).carrier := calc
      _ = ⋃ j, E j := hE.1
      _ subseteq _ := by gcongr with n; exact (hV n).1
    obtain ⟨g', hg⟩ := exists_continuous_sum_one_of_isOpen_isCompact (fun n => (V n).2) f.2 this
    exact ⟨fun n => ⟨g' n, hg.2.2.2 n⟩, hg⟩
  -- The proof is completed by a chain of inequalities.
  calc Λ f
    _ = Λ (∑ n, g n • f) := ?_
    _ = ∑ n, Λ (g n • f) := by simp
    _ <= ∑ n, Λ ((y n + ε') • g n) := ?_
    _ = ∑ n, (y n + ε') * Λ (g n) := by simp
    -- That `y n + ε'` can be negative is bad in the inequalities so we artificially include `|a|`.
    _ = ∑ n, (|a| + y n + ε') * Λ (g n) - |a| * ∑ n, Λ (g n) := by
      simp [add_assoc, add_mul |a|, Finset.sum_add_distrib, Finset.mul_sum]
    _ <= ∑ n, (|a| + y n + ε') * (μ.real (E n) + ε' / N) - |a| * ∑ n, Λ (g n) := ?_
    _ <= ∑ n, (|a| + y n + ε') * (μ.real (E n) + ε' / N) - |a| * μ.real K := ?_
    _ = ∑ n, (y n - ε') * μ.real (E n) +
      2 * ε' * μ.real K + ε' / N * ∑ n, (|a| + y n + ε') := ?_
    _ <= ∫ x, f x ∂μ + 2 * ε' * μ.real K + ε' / N * ∑ n, (|a| + y n + ε') := ?_
    _ <= ∫ x, f x ∂μ + ε' * (2 * μ.real K + |a| + b + ε') := ?_
    _ <= ∫ x, f x ∂μ + ε := by simp [hε'.2]
  · -- Equality since `∑ i : Fin N, (g i)` is equal to unity on the support of `f`
    congr; ext x
    simp only [coe_sum, smul_eq_mul, coe_mul, Pi.mul_apply,
      ← Finset.sum_mul]
    by_cases hx : x in tsupport f
    · simp [hg.2.1 hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · -- Use that `f ≤ y n + ε'` on `V n`
    gcongr with n hn
    intro x
    by_cases hx : x in tsupport (g n)
    · rw [smul_eq_mul, mul_comm]
      apply mul_le_mul_of_nonneg_right ?_ (hg.2.2.1 n x).1
exact le_of_lt (hV n).2.1 x mem_of_subset_of_mem (hg.1 n) hx
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · -- Use that `Λ (g n) ≤ μ (V n)).toReal ≤ μ (E n)).toReal + ε' / N`
    gcongr with n hn
    · calc
_ <= |a| + a := neg_le_iff_add_nonneg'.mp neg_abs_le a
_ <= |a| + a + ε' * (n + 1) := (le_add_iff_nonneg_right (|a| + a)).mpr Left.mul_nonneg
(le_of_lt hε'.1) Left.add_nonneg (Nat.cast_nonneg' n) (zero_le_one' Real)
        _ <= _ := by rw [← add_assoc, le_add_iff_nonneg_right]; exact le_of_lt hε'.1
    · calc
        _ <= μ.real (V n) := by
          apply (ENNReal.ofReal_le_iff_le_toReal _).mp
          · exact le_rieszMeasure_tsupport_subset Λ (fun x => hg.2.2.1 n x) (hg.1 n)
          · rw [← lt_top_iff_ne_top]
            apply lt_of_le_of_lt (hV n).2.2
            rw [WithTop.add_lt_top]
            exact ⟨WithTop.lt_top_iff_ne_top.mpr (hE' n), ENNReal.ofReal_lt_top⟩
        _ <= _ := by
          rw [← ENNReal.toReal_ofReal (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))]
          apply ENNReal.toReal_le_add (hV n).2.2 (hE' n)
          · finiteness
  · -- Use that `μ K ≤ Λ (∑ n, g n)`
    gcongr
    rw [← map_sum Λ g _]
    have h x : 0 <= (∑ n, g n) x := by simpa using Fintype.sum_nonneg fun n => (hg.2.2.1 n x).1
    apply ENNReal.toReal_le_of_le_ofReal
    · exact Λ.map_nonneg (fun x => h x)
    · have h' x (hx : x in K) : (∑ n, g n) x = 1 := by simp [hg.2.1 hx]
      refine rieszMeasure_le_of_eq_one Λ h f.2 h'
  · -- Rearrange the sums
    have (n : Fin N) : (|a| + y n + ε') * μ.real (E n) =
        (|a| + 2 * ε') * μ.real (E n) + (y n - ε') * μ.real (E n) := by linarith
    simp_rw [mul_add, this]
    have : ∑ i, μ.real (E i) = μ.real K := by
      suffices h : μ K = ∑ i, (μ (E i)) by
        simp only [measureReal_def, h]
exact Eq.symm ENNReal.toReal_sum fun n _ => hE' n
      dsimp [K]; rw [hE.1]
      rw [measure_iUnion (fun m n hmn => hE.2.1 trivial trivial hmn) hE.2.2.2]
      exact tsum_fintype fun b => μ (E b)
    rw [Finset.sum_add_distrib]; rw [Finset.sum_add_distrib]; rw [← Finset.mul_sum]; rw [this]; rw [← Finset.sum_mul]
    linarith
  · -- Use that `y n - ε' ≤ f x` on `E n`
    gcongr
    have h : forall n, (y n - ε') * μ.real (E n) <= ∫ x in (E n), f x ∂μ := by
      intro n
      apply setIntegral_ge_of_const_le_real (hE.2.2.2 n) (hE' n)
      · intro x hx
        dsimp [y]; linarith [(hE.2.2.1 n x hx).1]
      · apply Integrable.integrableOn
        dsimp [μ, rieszMeasure]
        exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
    calc
      _ <= ∑ n, ∫ (x : X) in E n, f x ∂μ := Finset.sum_le_sum fun i a => h i
      _ = ∫ x in (⋃ n, E n), f x ∂μ := by
refine Eq.symm integral_iUnion_fintype hE.2.2.2 (fun _ _ => hE.2.1 trivial trivial) ?_
        dsimp [μ, rieszMeasure]
        exact fun _ =>
Integrable.integrableOn Continuous.integrable_of_hasCompactSupport f.1.2 f.2
      _ = ∫ x in tsupport f, f x ∂μ := by simp_rw [hE.1]
      _ = _ := setIntegral_tsupport
  · -- Rough bound of the sum
    have h : ∑ n : Fin N, y n <= N * b := by
      have (n : Fin N) := calc y n
        _ <= a + ε' * N := by simp_all [y, show (n : Real) + 1 <= N by norm_cast; lia]
        _ = b := by simp [field, ε']
      have : ∑ n, y n <= ∑ n, b := Finset.sum_le_sum (fun n _ => this n)
      simp_all
    simp only [Finset.sum_add_distrib, Finset.sum_add_distrib,
               Fin.sum_const, Fin.sum_const, nsmul_eq_mul, ← add_assoc, mul_add, ← mul_assoc]
    simpa [show (N : Real) != 0 by simp [hN.ne.symm], mul_comm _ ε', div_eq_mul_inv, mul_assoc]
using (mul_le_mul_iff_of_pos_left hε'.1).mpr (inv_mul_le_iff₀ (Nat.cast_pos'.mpr hN)).mpr h

中文:
引理 integral_riesz_aux
  条件: (f : C_c(X, 实数))
  结论: Λ f <= ∫ x, f x ∂(rieszMeasure Λ)
  证明: by
  let μ := rieszMeasure Λ
  let K := tsupport f
  -- Suffices to show that `Λ f ≤ ∫ x, f x ∂μ + ε` for arbitrary `ε`.
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  -- Choose an interval `(a, b)` which contains the range of `f`.
  obtain ⟨a, b, hab⟩ : exists a b : Real, a < b ∧ range f subseteq Ioo a b := by
    obtain ⟨r, hr⟩ := (Metric.isCompact_iff_isClosed_bounded.mp
      (HasCompactSupport.isCompact_range f.2 f.1.2)).2.subset_ball_lt 0 0
    exact ⟨-r, r, by linarith, hr.2.trans_eq (by simp [Real.ball_eq_Ioo])⟩
  -- Choose `N` positive and sufficiently large such that `ε'` is sufficiently small
  obtain ⟨N, hN, hε'⟩ := exists_nat_large (b - a) (2 * μ.real K + |a| + b) hε
  let ε' := (b - a) / N
  replace hε' : 0 < ε' ∧ ε' * (2 * μ.real K + |a| + b + ε') <= ε :=
    ⟨div_pos (sub_pos.mpr hab.1) (Nat.cast_pos'.mpr hN), hε'⟩
  -- Take a partition of the support of `f` into sets `E` by partitioning the range.
obtain ⟨E, hE⟩ := range_cut_partition f a hε'.1 N by
    dsimp [ε']
    field_simp
    simp [hab.2]
  -- Introduce notation for the partition of the range.
  let y : Fin N -> Real := fun n => a + ε' * (n + 1)
  -- The measure of each `E n` is finite.
  have hE' (n : Fin N) : μ (E n) != ∞ := by
    have h : E n subseteq tsupport f := by rw [hE.1]; exact subset_iUnion _ _
    refine lt_top_iff_ne_top.mp ?_
apply lt_of_le_of_lt measure_mono h
    dsimp [μ]
    rw [rieszMeasure]; rw [← coe_toContinuousMap]; rw [← ContinuousMap.toFun_eq_coe]; rw [Content.measure_apply _ f.2.measurableSet]
    exact Content.outerMeasure_lt_top_of_isCompact _ f.2
  -- Define sets `V` which are open approximations to the sets `E`
  obtain ⟨V, hV⟩ : exists V : Fin N -> Opens X, forall n, E n subseteq (V n) ∧ (forall x in V n, f x < y n + ε') ∧
      μ (V n) <= μ (E n) + ENNReal.ofReal (ε' / N) := by
    have h_ε' := (div_pos hε'.1 (Nat.cast_pos'.mpr hN))
    have h n x (hx : x in E n) := lt_add_of_le_of_pos ((hE.2.2.1 n x hx).right) hε'.1
    have h' n := Eq.trans_ne
      (Content.measure_apply (rieszContent (toNNRealLinear Λ)) (hE.2.2.2 n)).symm (hE' n)
    choose V hV using fun n => exists_open_approx f h_ε' (E n) (h' n) (hE.2.2.2 n) (h n)
    exact ⟨V, hV⟩
  -- Define a partition of unity subordinated to the sets `V`
  obtain ⟨g, hg⟩ : exists g : Fin N -> C_c(X, Real), (forall n, tsupport (g n) subseteq (V n).carrier) ∧
      EqOn (∑ n : Fin N, (g n)) 1 (tsupport f.toFun) ∧ (forall n x, (g n) x in Icc 0 1) ∧
      forall n, HasCompactSupport (g n) := by
    have : tsupport f subseteq ⋃ n, (V n).carrier := calc
      _ = ⋃ j, E j := hE.1
      _ subseteq _ := by gcongr with n; exact (hV n).1
    obtain ⟨g', hg⟩ := exists_continuous_sum_one_of_isOpen_isCompact (fun n => (V n).2) f.2 this
    exact ⟨fun n => ⟨g' n, hg.2.2.2 n⟩, hg⟩
  -- The proof is completed by a chain of inequalities.
  calc Λ f
    _ = Λ (∑ n, g n • f) := ?_
    _ = ∑ n, Λ (g n • f) := by simp
    _ <= ∑ n, Λ ((y n + ε') • g n) := ?_
    _ = ∑ n, (y n + ε') * Λ (g n) := by simp
    -- That `y n + ε'` can be negative is bad in the inequalities so we artificially include `|a|`.
    _ = ∑ n, (|a| + y n + ε') * Λ (g n) - |a| * ∑ n, Λ (g n) := by
      simp [add_assoc, add_mul |a|, Finset.sum_add_distrib, Finset.mul_sum]
    _ <= ∑ n, (|a| + y n + ε') * (μ.real (E n) + ε' / N) - |a| * ∑ n, Λ (g n) := ?_
    _ <= ∑ n, (|a| + y n + ε') * (μ.real (E n) + ε' / N) - |a| * μ.real K := ?_
    _ = ∑ n, (y n - ε') * μ.real (E n) +
      2 * ε' * μ.real K + ε' / N * ∑ n, (|a| + y n + ε') := ?_
    _ <= ∫ x, f x ∂μ + 2 * ε' * μ.real K + ε' / N * ∑ n, (|a| + y n + ε') := ?_
    _ <= ∫ x, f x ∂μ + ε' * (2 * μ.real K + |a| + b + ε') := ?_
    _ <= ∫ x, f x ∂μ + ε := by simp [hε'.2]
  · -- Equality since `∑ i : Fin N, (g i)` is equal to unity on the support of `f`
    congr; ext x
    simp only [coe_sum, smul_eq_mul, coe_mul, Pi.mul_apply,
      ← Finset.sum_mul]
    by_cases hx : x in tsupport f
    · simp [hg.2.1 hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · -- Use that `f ≤ y n + ε'` on `V n`
    gcongr with n hn
    intro x
    by_cases hx : x in tsupport (g n)
    · rw [smul_eq_mul, mul_comm]
      apply mul_le_mul_of_nonneg_right ?_ (hg.2.2.1 n x).1
exact le_of_lt (hV n).2.1 x mem_of_subset_of_mem (hg.1 n) hx
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · -- Use that `Λ (g n) ≤ μ (V n)).toReal ≤ μ (E n)).toReal + ε' / N`
    gcongr with n hn
    · calc
_ <= |a| + a := neg_le_iff_add_nonneg'.mp neg_abs_le a
_ <= |a| + a + ε' * (n + 1) := (le_add_iff_nonneg_right (|a| + a)).mpr Left.mul_nonneg
(le_of_lt hε'.1) Left.add_nonneg (Nat.cast_nonneg' n) (zero_le_one' Real)
        _ <= _ := by rw [← add_assoc, le_add_iff_nonneg_right]; exact le_of_lt hε'.1
    · calc
        _ <= μ.real (V n) := by
          apply (ENNReal.ofReal_le_iff_le_toReal _).mp
          · exact le_rieszMeasure_tsupport_subset Λ (fun x => hg.2.2.1 n x) (hg.1 n)
          · rw [← lt_top_iff_ne_top]
            apply lt_of_le_of_lt (hV n).2.2
            rw [WithTop.add_lt_top]
            exact ⟨WithTop.lt_top_iff_ne_top.mpr (hE' n), ENNReal.ofReal_lt_top⟩
        _ <= _ := by
          rw [← ENNReal.toReal_ofReal (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))]
          apply ENNReal.toReal_le_add (hV n).2.2 (hE' n)
          · finiteness
  · -- Use that `μ K ≤ Λ (∑ n, g n)`
    gcongr
    rw [← map_sum Λ g _]
    have h x : 0 <= (∑ n, g n) x := by simpa using Fintype.sum_nonneg fun n => (hg.2.2.1 n x).1
    apply ENNReal.toReal_le_of_le_ofReal
    · exact Λ.map_nonneg (fun x => h x)
    · have h' x (hx : x in K) : (∑ n, g n) x = 1 := by simp [hg.2.1 hx]
      refine rieszMeasure_le_of_eq_one Λ h f.2 h'
  · -- Rearrange the sums
    have (n : Fin N) : (|a| + y n + ε') * μ.real (E n) =
        (|a| + 2 * ε') * μ.real (E n) + (y n - ε') * μ.real (E n) := by linarith
    simp_rw [mul_add, this]
    have : ∑ i, μ.real (E i) = μ.real K := by
      suffices h : μ K = ∑ i, (μ (E i)) by
        simp only [measureReal_def, h]
exact Eq.symm ENNReal.toReal_sum fun n _ => hE' n
      dsimp [K]; rw [hE.1]
      rw [measure_iUnion (fun m n hmn => hE.2.1 trivial trivial hmn) hE.2.2.2]
      exact tsum_fintype fun b => μ (E b)
    rw [Finset.sum_add_distrib]; rw [Finset.sum_add_distrib]; rw [← Finset.mul_sum]; rw [this]; rw [← Finset.sum_mul]
    linarith
  · -- Use that `y n - ε' ≤ f x` on `E n`
    gcongr
    have h : forall n, (y n - ε') * μ.real (E n) <= ∫ x in (E n), f x ∂μ := by
      intro n
      apply setIntegral_ge_of_const_le_real (hE.2.2.2 n) (hE' n)
      · intro x hx
        dsimp [y]; linarith [(hE.2.2.1 n x hx).1]
      · apply Integrable.integrableOn
        dsimp [μ, rieszMeasure]
        exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
    calc
      _ <= ∑ n, ∫ (x : X) in E n, f x ∂μ := Finset.sum_le_sum fun i a => h i
      _ = ∫ x in (⋃ n, E n), f x ∂μ := by
refine Eq.symm integral_iUnion_fintype hE.2.2.2 (fun _ _ => hE.2.1 trivial trivial) ?_
        dsimp [μ, rieszMeasure]
        exact fun _ =>
Integrable.integrableOn Continuous.integrable_of_hasCompactSupport f.1.2 f.2
      _ = ∫ x in tsupport f, f x ∂μ := by simp_rw [hE.1]
      _ = _ := setIntegral_tsupport
  · -- Rough bound of the sum
    have h : ∑ n : Fin N, y n <= N * b := by
      have (n : Fin N) := calc y n
        _ <= a + ε' * N := by simp_all [y, show (n : Real) + 1 <= N by norm_cast; lia]
        _ = b := by simp [field, ε']
      have : ∑ n, y n <= ∑ n, b := Finset.sum_le_sum (fun n _ => this n)
      simp_all
    simp only [Finset.sum_add_distrib, Finset.sum_add_distrib,
               Fin.sum_const, Fin.sum_const, nsmul_eq_mul, ← add_assoc, mul_add, ← mul_assoc]
    simpa [show (N : Real) != 0 by simp [hN.ne.symm], mul_comm _ ε', div_eq_mul_inv, mul_assoc]
using (mul_le_mul_iff_of_pos_left hε'.1).mpr (inv_mul_le_iff₀ (Nat.cast_pos'.mpr hN)).mpr h
-/
private lemma integral_riesz_aux (f : C_c(X, Real)) : Λ f <= ∫ x, f x ∂(rieszMeasure Λ) := by
  let μ := rieszMeasure Λ
  let K := tsupport f
  -- Suffices to show that `Λ f ≤ ∫ x, f x ∂μ + ε` for arbitrary `ε`.
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  -- Choose an interval `(a, b)` which contains the range of `f`.
  obtain ⟨a, b, hab⟩ : exists a b : Real, a < b ∧ range f subseteq Ioo a b := by
    obtain ⟨r, hr⟩ := (Metric.isCompact_iff_isClosed_bounded.mp
      (HasCompactSupport.isCompact_range f.2 f.1.2)).2.subset_ball_lt 0 0
    exact ⟨-r, r, by linarith, hr.2.trans_eq (by simp [Real.ball_eq_Ioo])⟩
  -- Choose `N` positive and sufficiently large such that `ε'` is sufficiently small
  obtain ⟨N, hN, hε'⟩ := exists_nat_large (b - a) (2 * μ.real K + |a| + b) hε
  let ε' := (b - a) / N
  replace hε' : 0 < ε' ∧ ε' * (2 * μ.real K + |a| + b + ε') <= ε :=
    ⟨div_pos (sub_pos.mpr hab.1) (Nat.cast_pos'.mpr hN), hε'⟩
  -- Take a partition of the support of `f` into sets `E` by partitioning the range.
obtain ⟨E, hE⟩ := range_cut_partition f a hε'.1 N by
    dsimp [ε']
    field_simp
    simp [hab.2]
  -- Introduce notation for the partition of the range.
  let y : Fin N -> Real := fun n => a + ε' * (n + 1)
  -- The measure of each `E n` is finite.
  have hE' (n : Fin N) : μ (E n) != ∞ := by
    have h : E n subseteq tsupport f := by rw [hE.1]; exact subset_iUnion _ _
    refine lt_top_iff_ne_top.mp ?_
apply lt_of_le_of_lt measure_mono h
    dsimp [μ]
    rw [rieszMeasure]; rw [← coe_toContinuousMap]; rw [← ContinuousMap.toFun_eq_coe]; rw [Content.measure_apply _ f.2.measurableSet]
    exact Content.outerMeasure_lt_top_of_isCompact _ f.2
  -- Define sets `V` which are open approximations to the sets `E`
  obtain ⟨V, hV⟩ : exists V : Fin N -> Opens X, forall n, E n subseteq (V n) ∧ (forall x in V n, f x < y n + ε') ∧
      μ (V n) <= μ (E n) + ENNReal.ofReal (ε' / N) := by
    have h_ε' := (div_pos hε'.1 (Nat.cast_pos'.mpr hN))
    have h n x (hx : x in E n) := lt_add_of_le_of_pos ((hE.2.2.1 n x hx).right) hε'.1
    have h' n := Eq.trans_ne
      (Content.measure_apply (rieszContent (toNNRealLinear Λ)) (hE.2.2.2 n)).symm (hE' n)
    choose V hV using fun n => exists_open_approx f h_ε' (E n) (h' n) (hE.2.2.2 n) (h n)
    exact ⟨V, hV⟩
  -- Define a partition of unity subordinated to the sets `V`
  obtain ⟨g, hg⟩ : exists g : Fin N -> C_c(X, Real), (forall n, tsupport (g n) subseteq (V n).carrier) ∧
      EqOn (∑ n : Fin N, (g n)) 1 (tsupport f.toFun) ∧ (forall n x, (g n) x in Icc 0 1) ∧
      forall n, HasCompactSupport (g n) := by
    have : tsupport f subseteq ⋃ n, (V n).carrier := calc
      _ = ⋃ j, E j := hE.1
      _ subseteq _ := by gcongr with n; exact (hV n).1
    obtain ⟨g', hg⟩ := exists_continuous_sum_one_of_isOpen_isCompact (fun n => (V n).2) f.2 this
    exact ⟨fun n => ⟨g' n, hg.2.2.2 n⟩, hg⟩
  -- The proof is completed by a chain of inequalities.
  calc Λ f
    _ = Λ (∑ n, g n • f) := ?_
    _ = ∑ n, Λ (g n • f) := by simp
    _ <= ∑ n, Λ ((y n + ε') • g n) := ?_
    _ = ∑ n, (y n + ε') * Λ (g n) := by simp
    -- That `y n + ε'` can be negative is bad in the inequalities so we artificially include `|a|`.
    _ = ∑ n, (|a| + y n + ε') * Λ (g n) - |a| * ∑ n, Λ (g n) := by
      simp [add_assoc, add_mul |a|, Finset.sum_add_distrib, Finset.mul_sum]
    _ <= ∑ n, (|a| + y n + ε') * (μ.real (E n) + ε' / N) - |a| * ∑ n, Λ (g n) := ?_
    _ <= ∑ n, (|a| + y n + ε') * (μ.real (E n) + ε' / N) - |a| * μ.real K := ?_
    _ = ∑ n, (y n - ε') * μ.real (E n) +
      2 * ε' * μ.real K + ε' / N * ∑ n, (|a| + y n + ε') := ?_
    _ <= ∫ x, f x ∂μ + 2 * ε' * μ.real K + ε' / N * ∑ n, (|a| + y n + ε') := ?_
    _ <= ∫ x, f x ∂μ + ε' * (2 * μ.real K + |a| + b + ε') := ?_
    _ <= ∫ x, f x ∂μ + ε := by simp [hε'.2]
  · -- Equality since `∑ i : Fin N, (g i)` is equal to unity on the support of `f`
    congr; ext x
    simp only [coe_sum, smul_eq_mul, coe_mul, Pi.mul_apply,
      ← Finset.sum_mul]
    by_cases hx : x in tsupport f
    · simp [hg.2.1 hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · -- Use that `f ≤ y n + ε'` on `V n`
    gcongr with n hn
    intro x
    by_cases hx : x in tsupport (g n)
    · rw [smul_eq_mul, mul_comm]
      apply mul_le_mul_of_nonneg_right ?_ (hg.2.2.1 n x).1
exact le_of_lt (hV n).2.1 x mem_of_subset_of_mem (hg.1 n) hx
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · -- Use that `Λ (g n) ≤ μ (V n)).toReal ≤ μ (E n)).toReal + ε' / N`
    gcongr with n hn
    · calc
_ <= |a| + a := neg_le_iff_add_nonneg'.mp neg_abs_le a
_ <= |a| + a + ε' * (n + 1) := (le_add_iff_nonneg_right (|a| + a)).mpr Left.mul_nonneg
(le_of_lt hε'.1) Left.add_nonneg (Nat.cast_nonneg' n) (zero_le_one' Real)
        _ <= _ := by rw [← add_assoc, le_add_iff_nonneg_right]; exact le_of_lt hε'.1
    · calc
        _ <= μ.real (V n) := by
          apply (ENNReal.ofReal_le_iff_le_toReal _).mp
          · exact le_rieszMeasure_tsupport_subset Λ (fun x => hg.2.2.1 n x) (hg.1 n)
          · rw [← lt_top_iff_ne_top]
            apply lt_of_le_of_lt (hV n).2.2
            rw [WithTop.add_lt_top]
            exact ⟨WithTop.lt_top_iff_ne_top.mpr (hE' n), ENNReal.ofReal_lt_top⟩
        _ <= _ := by
          rw [← ENNReal.toReal_ofReal (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))]
          apply ENNReal.toReal_le_add (hV n).2.2 (hE' n)
          · finiteness
  · -- Use that `μ K ≤ Λ (∑ n, g n)`
    gcongr
    rw [← map_sum Λ g _]
    have h x : 0 <= (∑ n, g n) x := by simpa using Fintype.sum_nonneg fun n => (hg.2.2.1 n x).1
    apply ENNReal.toReal_le_of_le_ofReal
    · exact Λ.map_nonneg (fun x => h x)
    · have h' x (hx : x in K) : (∑ n, g n) x = 1 := by simp [hg.2.1 hx]
      refine rieszMeasure_le_of_eq_one Λ h f.2 h'
  · -- Rearrange the sums
    have (n : Fin N) : (|a| + y n + ε') * μ.real (E n) =
        (|a| + 2 * ε') * μ.real (E n) + (y n - ε') * μ.real (E n) := by linarith
    simp_rw [mul_add, this]
    have : ∑ i, μ.real (E i) = μ.real K := by
      suffices h : μ K = ∑ i, (μ (E i)) by
        simp only [measureReal_def, h]
exact Eq.symm ENNReal.toReal_sum fun n _ => hE' n
      dsimp [K]; rw [hE.1]
      rw [measure_iUnion (fun m n hmn => hE.2.1 trivial trivial hmn) hE.2.2.2]
      exact tsum_fintype fun b => μ (E b)
    rw [Finset.sum_add_distrib]; rw [Finset.sum_add_distrib]; rw [← Finset.mul_sum]; rw [this]; rw [← Finset.sum_mul]
    linarith
  · -- Use that `y n - ε' ≤ f x` on `E n`
    gcongr
    have h : forall n, (y n - ε') * μ.real (E n) <= ∫ x in (E n), f x ∂μ := by
      intro n
      apply setIntegral_ge_of_const_le_real (hE.2.2.2 n) (hE' n)
      · intro x hx
        dsimp [y]; linarith [(hE.2.2.1 n x hx).1]
      · apply Integrable.integrableOn
        dsimp [μ, rieszMeasure]
        exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
    calc
      _ <= ∑ n, ∫ (x : X) in E n, f x ∂μ := Finset.sum_le_sum fun i a => h i
      _ = ∫ x in (⋃ n, E n), f x ∂μ := by
refine Eq.symm integral_iUnion_fintype hE.2.2.2 (fun _ _ => hE.2.1 trivial trivial) ?_
        dsimp [μ, rieszMeasure]
        exact fun _ =>
Integrable.integrableOn Continuous.integrable_of_hasCompactSupport f.1.2 f.2
      _ = ∫ x in tsupport f, f x ∂μ := by simp_rw [hE.1]
      _ = _ := setIntegral_tsupport
  · -- Rough bound of the sum
    have h : ∑ n : Fin N, y n <= N * b := by
      have (n : Fin N) := calc y n
        _ <= a + ε' * N := by simp_all [y, show (n : Real) + 1 <= N by norm_cast; lia]
        _ = b := by simp [field, ε']
      have : ∑ n, y n <= ∑ n, b := Finset.sum_le_sum (fun n _ => this n)
      simp_all
    simp only [Finset.sum_add_distrib, Finset.sum_add_distrib,
               Fin.sum_const, Fin.sum_const, nsmul_eq_mul, ← add_assoc, mul_add, ← mul_assoc]
    simpa [show (N : Real) != 0 by simp [hN.ne.symm], mul_comm _ ε', div_eq_mul_inv, mul_assoc]
using (mul_le_mul_iff_of_pos_left hε'.1).mpr (inv_mul_le_iff₀ (Nat.cast_pos'.mpr hN)).mpr h

/-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
the integral of `f` with respect to the `rieszMeasure` associated to `Λ` is equal to `Λ f`. -/
@[simp]
/--
theorem `integral_rieszMeasure` / 定理 `integral_rieszMeasure`

English:
theorem integral_rieszMeasure
  given: (f : C_c(X, Real))
  statement: ∫ x, f x ∂(rieszMeasure Λ) = Λ f
  proof: by
  -- We apply the result `Λ f ≤ ∫ x, f x ∂(rieszMeasure hΛ)` to `f` and `-f`.
  apply le_antisymm
  -- prove the inequality for `- f`
  · calc
      _ = - ∫ x, (-f) x ∂(rieszMeasure Λ) := by simpa using integral_neg' (-f)
      _ <= - Λ (-f) := neg_le_neg (integral_riesz_aux Λ (-f))
      _ = _ := by simp
  -- prove the inequality for `f`
  · exact integral_riesz_aux Λ f

中文:
定理 integral_rieszMeasure
  条件: (f : C_c(X, 实数))
  结论: ∫ x, f x ∂(rieszMeasure Λ) = Λ f
  证明: by
  -- We apply the result `Λ f ≤ ∫ x, f x ∂(rieszMeasure hΛ)` to `f` and `-f`.
  apply le_antisymm
  -- prove the inequality for `- f`
  · calc
      _ = - ∫ x, (-f) x ∂(rieszMeasure Λ) := by simpa using integral_neg' (-f)
      _ <= - Λ (-f) := neg_le_neg (integral_riesz_aux Λ (-f))
      _ = _ := by simp
  -- prove the inequality for `f`
  · exact integral_riesz_aux Λ f
-/
theorem integral_rieszMeasure (f : C_c(X, Real)) : ∫ x, f x ∂(rieszMeasure Λ) = Λ f := by
  -- We apply the result `Λ f ≤ ∫ x, f x ∂(rieszMeasure hΛ)` to `f` and `-f`.
  apply le_antisymm
  -- prove the inequality for `- f`
  · calc
      _ = - ∫ x, (-f) x ∂(rieszMeasure Λ) := by simpa using integral_neg' (-f)
      _ <= - Λ (-f) := neg_le_neg (integral_riesz_aux Λ (-f))
      _ = _ := by simp
  -- prove the inequality for `f`
  · exact integral_riesz_aux Λ f

/--
Instance `regular_rieszMeasure` / 实例 `regular_rieszMeasure`

English:
instance regular_rieszMeasure
  signature: : (rieszMeasure Λ).Regular
  body: (rieszContent _).regular

中文:
实例 regular_rieszMeasure
  签名: : (rieszMeasure Λ).正则
  定义体: (rieszContent _).regular

Depends on / 依赖: regular, rieszContent
-/
instance regular_rieszMeasure : (rieszMeasure Λ).Regular :=
  (rieszContent _).regular

end Construction

section integralPositiveLinearMap

variable {μ ν : Measure X} [LocallyCompactSpace X]

/-! We show that `RealRMK.rieszMeasure` is a bijection between positive linear functionals on
`C_c(X, ℝ)` and regular measures with inverse `RealRMK.integralPositiveLinearMap`. -/

/--
lemma `measure_le_of_isCompact_of_integral` / 引理 `measure_le_of_isCompact_of_integral`

English:
lemma measure_le_of_isCompact_of_integral
  statement: [ν.OuterRegular]
  proof: by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hν => ?_
  have hνK : ν K != ⊤ := hν.ne
  have hμK : μ K != ⊤ := hK.measure_lt_top.ne
  obtain ⟨V, pV1, pV2, pV3⟩ : exists V ⊇ K, IsOpen V ∧ ν V <= ν K + ε :=
    exists_isOpen_le_add K ν (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
  suffices μ.real K <= ν.real K + ε by
    rwa [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
    all_goals finiteness
have VltTop : ν V < ⊤ := pV3.trans_lt by finiteness
  obtain ⟨f, pf1, pf2, pf3⟩ :
      exists f : C_c(X, Real), Set.EqOn (⇑f) 1 K ∧ tsupport ⇑f subseteq V ∧ forall (x : X), f x in Set.Icc 0 1 := by
    obtain ⟨f, hf1, hf2, hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK pV2 pV1
    exact ⟨⟨f, hasCompactSupport_def.mpr hf2⟩, hf1, hf3⟩
  have hfV (x : X) : f x <= V.indicator 1 x := by
    by_cases hx : x in tsupport f
    · simp [(pf2 hx), (pf3 x).2]
    · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
  have hfK (x : X) : K.indicator 1 x <= f x := by
    by_cases hx : x in K
    · simp [hx, pf1 hx]
    · simp [hx, (pf3 x).1]
  calc
.symm μ.real K = ∫ x, K.indicator 1 x ∂μ := integral_indicator_one hK.measurableSet
    _ <= ∫ x, f x ∂μ := by
      refine integral_mono ?_ f.integrable hfK
      exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
    _ <= ∫ x, f x ∂ν := hμν f
    _ <= ∫ x, V.indicator 1 x ∂ν := by
      refine integral_mono f.integrable ?_ hfV
      exact IntegrableOn.integrable_indicator integrableOn_const pV2.measurableSet
    _ <= (ν K).toReal + ↑ε := by
      rwa [integral_indicator_one pV2.measurableSet, measureReal_def,
        ← ENNReal.coe_toReal, ← ENNReal.toReal_add, ENNReal.toReal_le_toReal]
      all_goals finiteness

中文:
引理 measure_le_of_isCompact_of_integral
  结论: [ν.外正则]
  证明: by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hν => ?_
  have hνK : ν K != ⊤ := hν.ne
  have hμK : μ K != ⊤ := hK.measure_lt_top.ne
  obtain ⟨V, pV1, pV2, pV3⟩ : exists V ⊇ K, IsOpen V ∧ ν V <= ν K + ε :=
    exists_isOpen_le_add K ν (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
  suffices μ.real K <= ν.real K + ε by
    rwa [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
    all_goals finiteness
have VltTop : ν V < ⊤ := pV3.trans_lt by finiteness
  obtain ⟨f, pf1, pf2, pf3⟩ :
      exists f : C_c(X, Real), Set.EqOn (⇑f) 1 K ∧ tsupport ⇑f subseteq V ∧ forall (x : X), f x in Set.Icc 0 1 := by
    obtain ⟨f, hf1, hf2, hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK pV2 pV1
    exact ⟨⟨f, hasCompactSupport_def.mpr hf2⟩, hf1, hf3⟩
  have hfV (x : X) : f x <= V.indicator 1 x := by
    by_cases hx : x in tsupport f
    · simp [(pf2 hx), (pf3 x).2]
    · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
  have hfK (x : X) : K.indicator 1 x <= f x := by
    by_cases hx : x in K
    · simp [hx, pf1 hx]
    · simp [hx, (pf3 x).1]
  calc
.symm μ.real K = ∫ x, K.indicator 1 x ∂μ := integral_indicator_one hK.measurableSet
    _ <= ∫ x, f x ∂μ := by
      refine integral_mono ?_ f.integrable hfK
      exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
    _ <= ∫ x, f x ∂ν := hμν f
    _ <= ∫ x, V.indicator 1 x ∂ν := by
      refine integral_mono f.integrable ?_ hfV
      exact IntegrableOn.integrable_indicator integrableOn_const pV2.measurableSet
    _ <= (ν K).toReal + ↑ε := by
      rwa [integral_indicator_one pV2.measurableSet, measureReal_def,
        ← ENNReal.coe_toReal, ← ENNReal.toReal_add, ENNReal.toReal_le_toReal]
      all_goals finiteness

Depends on / 依赖: ENNReal, ENNReal.coe_lt_coe.mpr, ENNReal.coe_toReal, ENNReal.le_of_forall_pos_le_add, ENNReal.toReal_add, ENNReal.toReal_le_toReal, IsOpen, VltTop, all_goals, coe_lt_coe, coe_toReal, exists_isOpen_le_add, finiteness, hK.measure_lt_top.ne, le_of_forall_pos_le_add, measure_lt_top, ne_of_gt, pV3.trans_lt, toReal_add, toReal_le_toReal
-/
lemma measure_le_of_isCompact_of_integral [ν.OuterRegular]
    [IsFiniteMeasureOnCompacts ν] [IsFiniteMeasureOnCompacts μ]
    (hμν : forall f : C_c(X, Real), ∫ x, f x ∂μ <= ∫ x, f x ∂ν)
    ⦃K : Set X⦄ (hK : IsCompact K) : μ K <= ν K := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hν => ?_
  have hνK : ν K != ⊤ := hν.ne
  have hμK : μ K != ⊤ := hK.measure_lt_top.ne
  obtain ⟨V, pV1, pV2, pV3⟩ : exists V ⊇ K, IsOpen V ∧ ν V <= ν K + ε :=
    exists_isOpen_le_add K ν (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
  suffices μ.real K <= ν.real K + ε by
    rwa [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
    all_goals finiteness
have VltTop : ν V < ⊤ := pV3.trans_lt by finiteness
  obtain ⟨f, pf1, pf2, pf3⟩ :
      exists f : C_c(X, Real), Set.EqOn (⇑f) 1 K ∧ tsupport ⇑f subseteq V ∧ forall (x : X), f x in Set.Icc 0 1 := by
    obtain ⟨f, hf1, hf2, hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK pV2 pV1
    exact ⟨⟨f, hasCompactSupport_def.mpr hf2⟩, hf1, hf3⟩
  have hfV (x : X) : f x <= V.indicator 1 x := by
    by_cases hx : x in tsupport f
    · simp [(pf2 hx), (pf3 x).2]
    · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
  have hfK (x : X) : K.indicator 1 x <= f x := by
    by_cases hx : x in K
    · simp [hx, pf1 hx]
    · simp [hx, (pf3 x).1]
  calc
.symm μ.real K = ∫ x, K.indicator 1 x ∂μ := integral_indicator_one hK.measurableSet
    _ <= ∫ x, f x ∂μ := by
      refine integral_mono ?_ f.integrable hfK
      exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
    _ <= ∫ x, f x ∂ν := hμν f
    _ <= ∫ x, V.indicator 1 x ∂ν := by
      refine integral_mono f.integrable ?_ hfV
      exact IntegrableOn.integrable_indicator integrableOn_const pV2.measurableSet
    _ <= (ν K).toReal + ↑ε := by
      rwa [integral_indicator_one pV2.measurableSet, measureReal_def,
        ← ENNReal.coe_toReal, ← ENNReal.toReal_add, ENNReal.toReal_le_toReal]
      all_goals finiteness

/--
theorem `_root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported` / 定理 `_root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`

English:
theorem _root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
  proof: by
  apply Measure.OuterRegular.ext_isOpen
  apply Measure.InnerRegularWRT.eq_of_innerRegularWRT_of_forall_eq Measure.Regular.innerRegular
    Measure.Regular.innerRegular
  intro K hK
  apply le_antisymm
  · exact measure_le_of_isCompact_of_integral (fun f => (hμν f).le) hK
  · exact measure_le_of_isCompact_of_integral (fun f => (hμν f).ge) hK

中文:
定理 _root_.测度论.测度.ext_of_integral_eq_on_compactlySupported
  证明: by
  apply Measure.OuterRegular.ext_isOpen
  apply Measure.InnerRegularWRT.eq_of_innerRegularWRT_of_forall_eq Measure.Regular.innerRegular
    Measure.Regular.innerRegular
  intro K hK
  apply le_antisymm
  · exact measure_le_of_isCompact_of_integral (fun f => (hμν f).le) hK
  · exact measure_le_of_isCompact_of_integral (fun f => (hμν f).ge) hK

Depends on / 依赖: InnerRegularWRT, Measure, Measure.InnerRegularWRT.eq_of_innerRegularWRT_of_forall_eq, Measure.OuterRegular.ext_isOpen, Measure.Regular.innerRegular, OuterRegular, Regular, eq_of_innerRegularWRT_of_forall_eq, ext_isOpen, innerRegular, le_antisymm, measure_le_of_isCompact_of_integral
-/
theorem _root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
    [μ.Regular] [ν.Regular] (hμν : forall f : C_c(X, Real), ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  apply Measure.OuterRegular.ext_isOpen
  apply Measure.InnerRegularWRT.eq_of_innerRegularWRT_of_forall_eq Measure.Regular.innerRegular
    Measure.Regular.innerRegular
  intro K hK
  apply le_antisymm
  · exact measure_le_of_isCompact_of_integral (fun f => (hμν f).le) hK
  · exact measure_le_of_isCompact_of_integral (fun f => (hμν f).ge) hK

/--
theorem `integralPositiveLinearMap_inj` / 定理 `integralPositiveLinearMap_inj`

English:
theorem integralPositiveLinearMap_inj
  given: [μ.Regular] [ν.Regular]
  proof: Measure.ext_of_integral_eq_on_compactlySupported fun f => congr($hμν f)
  mpr _ := by congr

中文:
定理 integralPositiveLinearMap_inj
  条件: [μ.正则] [ν.正则]
  证明: Measure.ext_of_integral_eq_on_compactlySupported fun f => congr($hμν f)
  mpr _ := by congr

Depends on / 依赖: Measure, Measure.ext_of_integral_eq_on_compactlySupported, ext_of_integral_eq_on_compactlySupported
-/
theorem integralPositiveLinearMap_inj [μ.Regular] [ν.Regular] :
    integralPositiveLinearMap μ = integralPositiveLinearMap ν ↔ μ = ν where
  mp hμν := Measure.ext_of_integral_eq_on_compactlySupported fun f => congr($hμν f)
  mpr _ := by congr

/-- Every regular measure is induced by a positive linear functional on `C_c(X, ℝ)`.
That is, `RealRMK.rieszMeasure` is a surjective function onto regular measures. -/
@[simp]
/--
theorem `rieszMeasure_integralPositiveLinearMap` / 定理 `rieszMeasure_integralPositiveLinearMap`

English:
theorem rieszMeasure_integralPositiveLinearMap
  given: [μ.Regular]
  proof: Measure.ext_of_integral_eq_on_compactlySupported (by simp)

@[simp]

中文:
定理 rieszMeasure_integralPositiveLinearMap
  条件: [μ.正则]
  证明: Measure.ext_of_integral_eq_on_compactlySupported (by simp)

@[simp]

Depends on / 依赖: Measure, Measure.ext_of_integral_eq_on_compactlySupported, ext_of_integral_eq_on_compactlySupported
-/
theorem rieszMeasure_integralPositiveLinearMap [μ.Regular] :
    rieszMeasure (integralPositiveLinearMap μ) = μ :=
  Measure.ext_of_integral_eq_on_compactlySupported (by simp)

@[simp]
/--
theorem `integralPositiveLinearMap_rieszMeasure` / 定理 `integralPositiveLinearMap_rieszMeasure`

English:
theorem integralPositiveLinearMap_rieszMeasure
  proof: by ext; simp

中文:
定理 integralPositiveLinearMap_rieszMeasure
  证明: by ext; simp
-/
theorem integralPositiveLinearMap_rieszMeasure :
    integralPositiveLinearMap (rieszMeasure Λ) = Λ := by ext; simp

end integralPositiveLinearMap

section Compact

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: X] (Λ
  body: by
  constructor
  let o : C_c(X, Real) := ⟨1, HasCompactSupport.of_compactSpace 1⟩
  calc rieszMeasure Λ univ
  _ <= ENNReal.ofReal (Λ o) :=
    rieszMeasure_le_of_eq_one _ (fun x => zero_le_one) isCompact_univ (fun x hx => rfl)
  _ < ⊤ := by simp

中文:
实例 [紧空间
  签名: X] (Λ
  定义体: by
  constructor
  let o : C_c(X, Real) := ⟨1, HasCompactSupport.of_compactSpace 1⟩
  calc rieszMeasure Λ univ
  _ <= ENNReal.ofReal (Λ o) :=
    rieszMeasure_le_of_eq_one _ (fun x => zero_le_one) isCompact_univ (fun x hx => rfl)
  _ < ⊤ := by simp

Depends on / 依赖: ENNReal, ENNReal.ofReal, HasCompactSupport, HasCompactSupport.of_compactSpace, isCompact_univ, ofReal, of_compactSpace, rieszMeasure, rieszMeasure_le_of_eq_one, zero_le_one
-/
instance [CompactSpace X] (Λ : C_c(X, Real) ->ₚ[Real] Real) : IsFiniteMeasure (rieszMeasure Λ) := by
  constructor
  let o : C_c(X, Real) := ⟨1, HasCompactSupport.of_compactSpace 1⟩
  calc rieszMeasure Λ univ
  _ <= ENNReal.ofReal (Λ o) :=
    rieszMeasure_le_of_eq_one _ (fun x => zero_le_one) isCompact_univ (fun x hx => rfl)
  _ < ⊤ := by simp

/--
lemma `_root_.MeasureTheory.Measure.exists_regular_eq_of_compactSpace` / 引理 `_root_.MeasureTheory.Measure.exists_regular_eq_of_compactSpace`

English:
lemma _root_.MeasureTheory.Measure.exists_regular_eq_of_compactSpace
  statement: [CompactSpace X]
  proof: by
  let Λ : C_c(X, Real) ->ₚ[Real] Real :=
  { toFun g := ∫ x, g x ∂μ
    map_add' g g' := integral_add g.integrable g'.integrable
    map_smul' c g := integral_smul c g
    monotone' g g' hgg' := integral_mono g.integrable g'.integrable hgg' }
  refine ⟨RealRMK.rieszMeasure Λ, by infer_instance, by infer_instance, fun g => ?_⟩
  let g' : C_c(X, Real) :=
  { toFun := g
    hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  exact (integral_rieszMeasure Λ g').symm

中文:
引理 _root_.测度论.测度.存在_regular_eq_of_compactSpace
  结论: [紧空间 X]
  证明: by
  let Λ : C_c(X, Real) ->ₚ[Real] Real :=
  { toFun g := ∫ x, g x ∂μ
    map_add' g g' := integral_add g.integrable g'.integrable
    map_smul' c g := integral_smul c g
    monotone' g g' hgg' := integral_mono g.integrable g'.integrable hgg' }
  refine ⟨RealRMK.rieszMeasure Λ, by infer_instance, by infer_instance, fun g => ?_⟩
  let g' : C_c(X, Real) :=
  { toFun := g
    hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  exact (integral_rieszMeasure Λ g').symm

Depends on / 依赖: HasCompactSupport, HasCompactSupport.of_compactSpace, RealRMK, RealRMK.rieszMeasure, g.integrable, hasCompactSupport, infer_instance, integrable, integral_add, integral_mono, integral_rieszMeasure, integral_smul, map_add, map_smul, monotone, of_compactSpace, rieszMeasure
-/
lemma _root_.MeasureTheory.Measure.exists_regular_eq_of_compactSpace [CompactSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    exists (ν : Measure X), ν.Regular ∧ IsFiniteMeasure ν ∧
      forall g : X ->ᵇ Real, ∫ x, g x ∂μ = ∫ x, g x ∂ν := by
  let Λ : C_c(X, Real) ->ₚ[Real] Real :=
  { toFun g := ∫ x, g x ∂μ
    map_add' g g' := integral_add g.integrable g'.integrable
    map_smul' c g := integral_smul c g
    monotone' g g' hgg' := integral_mono g.integrable g'.integrable hgg' }
  refine ⟨RealRMK.rieszMeasure Λ, by infer_instance, by infer_instance, fun g => ?_⟩
  let g' : C_c(X, Real) :=
  { toFun := g
    hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  exact (integral_rieszMeasure Λ g').symm

/--
lemma `_root_.MeasureTheory.Measure.exists_innerRegular_eq_of_isCompact` / 引理 `_root_.MeasureTheory.Measure.exists_innerRegular_eq_of_isCompact`

English:
lemma _root_.MeasureTheory.Measure.exists_innerRegular_eq_of_isCompact
  proof: by
  let μ' : Measure K := μ.comap Subtype.val
  obtain ⟨ν', ν'_reg, ν'_fin, hν'⟩ : exists (ν : Measure K), ν.Regular ∧ IsFiniteMeasure ν ∧
      forall g : K ->ᵇ Real, ∫ x, g x ∂μ' = ∫ x, g x ∂ν := by
    have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact Measure.exists_regular_eq_of_compactSpace μ'
  refine ⟨ν'.map Subtype.val, Measure.InnerRegular.map_of_continuous (by fun_prop),
    by infer_instance, ?_, fun g => ?_⟩
  · rw [Measure.map_apply (by fun_prop) hK.measurableSet.compl]
    simp
  convert! hν' (g.compContinuous ⟨Subtype.val, by fun_prop⟩)
  · simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    rw [← integral_map (φ := Subtype.val) (by fun_prop) (by fun_prop)]
    simp only [map_comap_subtype_coe hK.measurableSet, μ', Measure.restrict_eq_self_of_ae_mem h]
  · rw [integral_map (φ := Subtype.val) (by fun_prop) (by fun_prop)]
    simp

中文:
引理 _root_.测度论.测度.存在_innerRegular_eq_of_isCompact
  证明: by
  let μ' : Measure K := μ.comap Subtype.val
  obtain ⟨ν', ν'_reg, ν'_fin, hν'⟩ : exists (ν : Measure K), ν.Regular ∧ IsFiniteMeasure ν ∧
      forall g : K ->ᵇ Real, ∫ x, g x ∂μ' = ∫ x, g x ∂ν := by
    have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact Measure.exists_regular_eq_of_compactSpace μ'
  refine ⟨ν'.map Subtype.val, Measure.InnerRegular.map_of_continuous (by fun_prop),
    by infer_instance, ?_, fun g => ?_⟩
  · rw [Measure.map_apply (by fun_prop) hK.measurableSet.compl]
    simp
  convert! hν' (g.compContinuous ⟨Subtype.val, by fun_prop⟩)
  · simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    rw [← integral_map (φ := Subtype.val) (by fun_prop) (by fun_prop)]
    simp only [map_comap_subtype_coe hK.measurableSet, μ', Measure.restrict_eq_self_of_ae_mem h]
  · rw [integral_map (φ := Subtype.val) (by fun_prop) (by fun_prop)]
    simp

Depends on / 依赖: CompactSpace, InnerRegular, IsFiniteMeasure, Measure, Measure.InnerRegular.map_of_continuous, Measure.exists_regular_eq_of_compactSpace, Measure.map_apply, Regular, Subtype, Subtype.val, _fin, _reg, convert, exists_regular_eq_of_compactSpace, fun_prop, hK.measurableSet.compl, infer_instance, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, map_apply
-/
lemma _root_.MeasureTheory.Measure.exists_innerRegular_eq_of_isCompact
    (μ : Measure X) [IsFiniteMeasure μ] {K : Set X} (hK : IsCompact K) (h : μ Kᶜ = 0) :
    exists (ν : Measure X), ν.InnerRegular ∧ IsFiniteMeasure ν ∧ ν Kᶜ = 0 ∧
      forall g : X ->ᵇ Real, ∫ x, g x ∂μ = ∫ x, g x ∂ν := by
  let μ' : Measure K := μ.comap Subtype.val
  obtain ⟨ν', ν'_reg, ν'_fin, hν'⟩ : exists (ν : Measure K), ν.Regular ∧ IsFiniteMeasure ν ∧
      forall g : K ->ᵇ Real, ∫ x, g x ∂μ' = ∫ x, g x ∂ν := by
    have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact Measure.exists_regular_eq_of_compactSpace μ'
  refine ⟨ν'.map Subtype.val, Measure.InnerRegular.map_of_continuous (by fun_prop),
    by infer_instance, ?_, fun g => ?_⟩
  · rw [Measure.map_apply (by fun_prop) hK.measurableSet.compl]
    simp
  convert! hν' (g.compContinuous ⟨Subtype.val, by fun_prop⟩)
  · simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    rw [← integral_map (φ := Subtype.val) (by fun_prop) (by fun_prop)]
    simp only [map_comap_subtype_coe hK.measurableSet, μ', Measure.restrict_eq_self_of_ae_mem h]
  · rw [integral_map (φ := Subtype.val) (by fun_prop) (by fun_prop)]
    simp

end Compact

end RealRMK
