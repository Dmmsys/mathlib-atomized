/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Kernel.Defs

import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Probability.CDF

/-!
# Representation of kernels

This file contains results about isolation of kernels randomness. In particular, it shows that,
when the target space is a standard Borel space, any Markov kernel can be represented as the image
of the uniform measure on `[0,1]` by a deterministic map. It corresponds to Lemma 4.22 in
[Foundations of Modern Probability][kallenberg2021].

## Main results

* `ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval`:
  for a Markov kernel `κ : Kernel X Y` with `Y` a standard Borel space,
  there exists a jointly measurable function `f : X → I → Y` such that for all `a : X`,
  `volume.map (f a) = κ a`.

* `ProbabilityTheory.Kernel.exists_measurable_map_eq`:
  for a probability measure `μ` on a standard Borel space `Y`,
  there exists a measurable function `f : I → Y` such that `volume.map f = μ`.
-/

public section

open MeasureTheory ProbabilityTheory Set ENNReal unitInterval Filter Topology Function

variable {X Y : Type*} {mX : MeasurableSpace X} [Nonempty Y] {mY : MeasurableSpace Y}
    [StandardBorelSpace Y]

namespace ProbabilityTheory.Kernel

/--
lemma `exists_measurable_map_eq_unitInterval_aux` / 引理 `exists_measurable_map_eq_unitInterval_aux`

English:
lemma exists_measurable_map_eq_unitInterval_aux
  given: (κ : Kernel X I) [IsMarkovKernel κ]
  proof: by
  let f := fun s (t : I) => sSup {x | (κ s).real (Icc 0 x) < t}
  have measurable_f : Measurable (uncurry f) := by
    refine measurable_of_Ioi fun a => ?_
    simp only [preimage, uncurry, mem_Ioi]
    have h_monotone s : Monotone (fun x => (κ s).real (Icc 0 x)) :=
      fun x y hxy => measureReal_mono (by gcongr)
    have sSup_eq_iUnion_rat : {x : X × I | a < f x.1 x.2} =
        ⋃ (q : Rat) (hqI : ↑q in I) (_ : a < (q : Real)), {e | (κ e.1).real (Icc 0 ⟨q, hqI⟩) < e.2} := by
      ext e
      simp_all only [lt_sSup_iff, mem_ofPred_eq, Subtype.exists, mem_Icc, Rat.cast_nonneg,
        mem_iUnion, exists_prop, exists_and_left, f]
      constructor
      · rintro ⟨y, hyI, y_mem, (hy : a.1 < y)⟩
        obtain ⟨q, hqa, hqy⟩ := exists_rat_btwn hy
        refine ⟨q, hqa, ⟨?_, hqy.le.trans hyI.2⟩, lt_of_lt_of_le' y_mem (h_monotone e.1 hqy.le)⟩
        simp [← Rat.cast_nonneg (K := Real), a.2.1.trans hqa.le]
      · intro he
        obtain ⟨q, hqa, hqI, h⟩ := he
        refine ⟨q, ⟨by simp [hqI.1], hqI.2⟩, h, ?_⟩
        change a.1 < q
        simp [hqa]
    rw [sSup_eq_iUnion_rat]
    refine MeasurableSet.iUnion (fun b => MeasurableSet.iUnion
      (fun bI => MeasurableSet.iUnion (fun _ => ?_)))
    refine measurableSet_lt ?_ measurable_snd.subtype_val
    simp_rw [measureReal_def]
    have hκ := κ.measurable_coe (s := Icc 0 ⟨b, bI⟩) measurableSet_Icc
    fun_prop
  refine ⟨f, measurable_f, fun a => (volume.map (f a)).ext_of_Iic (κ a) fun x => ?_⟩
  have Iic_to_Icc : Iic x = Icc 0 x := by ext; simp
  have κ_in_I : ((κ a).real (Icc 0 x)) in I := ⟨measureReal_nonneg, measureReal_le_one⟩
  simp_rw [volume.map_apply measurable_f.of_uncurry_left measurableSet_Iic, preimage,
    mem_Iic, Iic_to_Icc, ← ofReal_measureReal (measure_ne_top (κ a) _), ← volume_Iic ⟨_, κ_in_I⟩]
  congr with ξ
  constructor
  · intro (hξ : f a ξ <= x)
    change ξ <= (κ a).real (Icc 0 x)
    by_cases hx : x = 1
    · simp [hx, ← univ_eq_Icc, ξ.2.2]
    let g := fun y => (κ a).real (Icc 0 y)
    let nebot : NeBot (𝓝[>] x) := by
      refine nhdsGT_neBot_of_exists_gt ?_
      use 1
      exact lt_of_le_of_ne x.2.2 hx
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) (g := g) continuousWithinAt_const ?_ ?_
    · let h := cdf ((κ a).map Subtype.val)
      have h_continuousWithinAt := continuousWithinAt_Ioi_iff_Ici.mpr (h.right_continuous x)
      simp_rw [g, ← unitInterval.cdf_eq_real (κ a)]
      exact h_continuousWithinAt.comp (Continuous.continuousWithinAt (by fun_prop)) (fun y hy => hy)
    · refine eventually_nhdsWithin_of_forall fun y hy => ?_
      by_contra! h
      simp only [sSup_le_iff, f] at hξ
      specialize hξ y h
      grind
  · intro (hξ : ξ <= (κ a).real (Icc 0 x))
    simp only [sSup_le_iff, f]
    intro c hc
    by_contra! h
    have h_lt : ¬ (κ a).real (Icc 0 x) <= (κ a).real (Icc 0 c) := not_le.mpr (lt_of_le_of_lt' hξ hc)
    refine h_lt ?_
    gcongr
    simp

中文:
引理 存在_measurable_map_eq_unit整数erval_aux
  条件: (κ : 核 X I) [是MarkovKernel κ]
  证明: by
  let f := fun s (t : I) => sSup {x | (κ s).real (Icc 0 x) < t}
  have measurable_f : Measurable (uncurry f) := by
    refine measurable_of_Ioi fun a => ?_
    simp only [preimage, uncurry, mem_Ioi]
    have h_monotone s : Monotone (fun x => (κ s).real (Icc 0 x)) :=
      fun x y hxy => measureReal_mono (by gcongr)
    have sSup_eq_iUnion_rat : {x : X × I | a < f x.1 x.2} =
        ⋃ (q : Rat) (hqI : ↑q in I) (_ : a < (q : Real)), {e | (κ e.1).real (Icc 0 ⟨q, hqI⟩) < e.2} := by
      ext e
      simp_all only [lt_sSup_iff, mem_ofPred_eq, Subtype.exists, mem_Icc, Rat.cast_nonneg,
        mem_iUnion, exists_prop, exists_and_left, f]
      constructor
      · rintro ⟨y, hyI, y_mem, (hy : a.1 < y)⟩
        obtain ⟨q, hqa, hqy⟩ := exists_rat_btwn hy
        refine ⟨q, hqa, ⟨?_, hqy.le.trans hyI.2⟩, lt_of_lt_of_le' y_mem (h_monotone e.1 hqy.le)⟩
        simp [← Rat.cast_nonneg (K := Real), a.2.1.trans hqa.le]
      · intro he
        obtain ⟨q, hqa, hqI, h⟩ := he
        refine ⟨q, ⟨by simp [hqI.1], hqI.2⟩, h, ?_⟩
        change a.1 < q
        simp [hqa]
    rw [sSup_eq_iUnion_rat]
    refine MeasurableSet.iUnion (fun b => MeasurableSet.iUnion
      (fun bI => MeasurableSet.iUnion (fun _ => ?_)))
    refine measurableSet_lt ?_ measurable_snd.subtype_val
    simp_rw [measureReal_def]
    have hκ := κ.measurable_coe (s := Icc 0 ⟨b, bI⟩) measurableSet_Icc
    fun_prop
  refine ⟨f, measurable_f, fun a => (volume.map (f a)).ext_of_Iic (κ a) fun x => ?_⟩
  have Iic_to_Icc : Iic x = Icc 0 x := by ext; simp
  have κ_in_I : ((κ a).real (Icc 0 x)) in I := ⟨measureReal_nonneg, measureReal_le_one⟩
  simp_rw [volume.map_apply measurable_f.of_uncurry_left measurableSet_Iic, preimage,
    mem_Iic, Iic_to_Icc, ← ofReal_measureReal (measure_ne_top (κ a) _), ← volume_Iic ⟨_, κ_in_I⟩]
  congr with ξ
  constructor
  · intro (hξ : f a ξ <= x)
    change ξ <= (κ a).real (Icc 0 x)
    by_cases hx : x = 1
    · simp [hx, ← univ_eq_Icc, ξ.2.2]
    let g := fun y => (κ a).real (Icc 0 y)
    let nebot : NeBot (𝓝[>] x) := by
      refine nhdsGT_neBot_of_exists_gt ?_
      use 1
      exact lt_of_le_of_ne x.2.2 hx
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) (g := g) continuousWithinAt_const ?_ ?_
    · let h := cdf ((κ a).map Subtype.val)
      have h_continuousWithinAt := continuousWithinAt_Ioi_iff_Ici.mpr (h.right_continuous x)
      simp_rw [g, ← unitInterval.cdf_eq_real (κ a)]
      exact h_continuousWithinAt.comp (Continuous.continuousWithinAt (by fun_prop)) (fun y hy => hy)
    · refine eventually_nhdsWithin_of_forall fun y hy => ?_
      by_contra! h
      simp only [sSup_le_iff, f] at hξ
      specialize hξ y h
      grind
  · intro (hξ : ξ <= (κ a).real (Icc 0 x))
    simp only [sSup_le_iff, f]
    intro c hc
    by_contra! h
    have h_lt : ¬ (κ a).real (Icc 0 x) <= (κ a).real (Icc 0 c) := not_le.mpr (lt_of_le_of_lt' hξ hc)
    refine h_lt ?_
    gcongr
    simp
-/
private lemma exists_measurable_map_eq_unitInterval_aux (κ : Kernel X I) [IsMarkovKernel κ] :
    exists (f : X -> I -> I), Measurable (uncurry f) ∧ forall a, volume.map (f a) = κ a := by
  let f := fun s (t : I) => sSup {x | (κ s).real (Icc 0 x) < t}
  have measurable_f : Measurable (uncurry f) := by
    refine measurable_of_Ioi fun a => ?_
    simp only [preimage, uncurry, mem_Ioi]
    have h_monotone s : Monotone (fun x => (κ s).real (Icc 0 x)) :=
      fun x y hxy => measureReal_mono (by gcongr)
    have sSup_eq_iUnion_rat : {x : X × I | a < f x.1 x.2} =
        ⋃ (q : Rat) (hqI : ↑q in I) (_ : a < (q : Real)), {e | (κ e.1).real (Icc 0 ⟨q, hqI⟩) < e.2} := by
      ext e
      simp_all only [lt_sSup_iff, mem_ofPred_eq, Subtype.exists, mem_Icc, Rat.cast_nonneg,
        mem_iUnion, exists_prop, exists_and_left, f]
      constructor
      · rintro ⟨y, hyI, y_mem, (hy : a.1 < y)⟩
        obtain ⟨q, hqa, hqy⟩ := exists_rat_btwn hy
        refine ⟨q, hqa, ⟨?_, hqy.le.trans hyI.2⟩, lt_of_lt_of_le' y_mem (h_monotone e.1 hqy.le)⟩
        simp [← Rat.cast_nonneg (K := Real), a.2.1.trans hqa.le]
      · intro he
        obtain ⟨q, hqa, hqI, h⟩ := he
        refine ⟨q, ⟨by simp [hqI.1], hqI.2⟩, h, ?_⟩
        change a.1 < q
        simp [hqa]
    rw [sSup_eq_iUnion_rat]
    refine MeasurableSet.iUnion (fun b => MeasurableSet.iUnion
      (fun bI => MeasurableSet.iUnion (fun _ => ?_)))
    refine measurableSet_lt ?_ measurable_snd.subtype_val
    simp_rw [measureReal_def]
    have hκ := κ.measurable_coe (s := Icc 0 ⟨b, bI⟩) measurableSet_Icc
    fun_prop
  refine ⟨f, measurable_f, fun a => (volume.map (f a)).ext_of_Iic (κ a) fun x => ?_⟩
  have Iic_to_Icc : Iic x = Icc 0 x := by ext; simp
  have κ_in_I : ((κ a).real (Icc 0 x)) in I := ⟨measureReal_nonneg, measureReal_le_one⟩
  simp_rw [volume.map_apply measurable_f.of_uncurry_left measurableSet_Iic, preimage,
    mem_Iic, Iic_to_Icc, ← ofReal_measureReal (measure_ne_top (κ a) _), ← volume_Iic ⟨_, κ_in_I⟩]
  congr with ξ
  constructor
  · intro (hξ : f a ξ <= x)
    change ξ <= (κ a).real (Icc 0 x)
    by_cases hx : x = 1
    · simp [hx, ← univ_eq_Icc, ξ.2.2]
    let g := fun y => (κ a).real (Icc 0 y)
    let nebot : NeBot (𝓝[>] x) := by
      refine nhdsGT_neBot_of_exists_gt ?_
      use 1
      exact lt_of_le_of_ne x.2.2 hx
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) (g := g) continuousWithinAt_const ?_ ?_
    · let h := cdf ((κ a).map Subtype.val)
      have h_continuousWithinAt := continuousWithinAt_Ioi_iff_Ici.mpr (h.right_continuous x)
      simp_rw [g, ← unitInterval.cdf_eq_real (κ a)]
      exact h_continuousWithinAt.comp (Continuous.continuousWithinAt (by fun_prop)) (fun y hy => hy)
    · refine eventually_nhdsWithin_of_forall fun y hy => ?_
      by_contra! h
      simp only [sSup_le_iff, f] at hξ
      specialize hξ y h
      grind
  · intro (hξ : ξ <= (κ a).real (Icc 0 x))
    simp only [sSup_le_iff, f]
    intro c hc
    by_contra! h
    have h_lt : ¬ (κ a).real (Icc 0 x) <= (κ a).real (Icc 0 c) := not_le.mpr (lt_of_le_of_lt' hξ hc)
    refine h_lt ?_
    gcongr
    simp

/--
theorem `exists_measurable_map_eq_unitInterval` / 定理 `exists_measurable_map_eq_unitInterval`

English:
theorem exists_measurable_map_eq_unitInterval
  given: (κ : Kernel X Y) [IsMarkovKernel κ]
  proof: by
  let g := sigmoid ∘ embeddingReal Y
  have hg := measurableEmbedding_sigmoid_comp_embeddingReal Y
  have hκg : IsMarkovKernel (κ.map g) := IsMarkovKernel.map κ hg.measurable
  have hg'κ : κ = (κ.map g).map hg.invFun := by
    rw [← map_comp_right _ hg.measurable (by fun_prop)]; rw [LeftInverse.id hg.leftInverse_invFun]; rw [map_id]
  obtain ⟨f', hf', hf'κ⟩ := (κ.map g).exists_measurable_map_eq_unitInterval_aux
  refine ⟨fun a u => hg.invFun (f' a u), by fun_prop, fun a => ?_⟩
  rw [hg'κ]; rw [map_apply _ (by fun_prop)]; rw [← hf'κ]; rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

中文:
定理 存在_measurable_map_eq_unit整数erval
  条件: (κ : 核 X Y) [是MarkovKernel κ]
  证明: by
  let g := sigmoid ∘ embeddingReal Y
  have hg := measurableEmbedding_sigmoid_comp_embeddingReal Y
  have hκg : IsMarkovKernel (κ.map g) := IsMarkovKernel.map κ hg.measurable
  have hg'κ : κ = (κ.map g).map hg.invFun := by
    rw [← map_comp_right _ hg.measurable (by fun_prop)]; rw [LeftInverse.id hg.leftInverse_invFun]; rw [map_id]
  obtain ⟨f', hf', hf'κ⟩ := (κ.map g).exists_measurable_map_eq_unitInterval_aux
  refine ⟨fun a u => hg.invFun (f' a u), by fun_prop, fun a => ?_⟩
  rw [hg'κ]; rw [map_apply _ (by fun_prop)]; rw [← hf'κ]; rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

Depends on / 依赖: IsMarkovKernel, IsMarkovKernel.map, LeftInverse, LeftInverse.id, embeddingReal, exists_measurable_map_eq_unitInterval_aux, fun_prop, hg.invFun, hg.leftInverse_invFun, hg.measurable, invFun, leftInverse_invFun, map_apply, map_comp_right, map_id, measurable, measurableEmbedding_sigmoid_comp_embeddingReal, sigmoid
-/
theorem exists_measurable_map_eq_unitInterval (κ : Kernel X Y) [IsMarkovKernel κ] :
    exists (f : X -> I -> Y), Measurable (uncurry f) ∧ forall a, volume.map (f a) = κ a := by
  let g := sigmoid ∘ embeddingReal Y
  have hg := measurableEmbedding_sigmoid_comp_embeddingReal Y
  have hκg : IsMarkovKernel (κ.map g) := IsMarkovKernel.map κ hg.measurable
  have hg'κ : κ = (κ.map g).map hg.invFun := by
    rw [← map_comp_right _ hg.measurable (by fun_prop)]; rw [LeftInverse.id hg.leftInverse_invFun]; rw [map_id]
  obtain ⟨f', hf', hf'κ⟩ := (κ.map g).exists_measurable_map_eq_unitInterval_aux
  refine ⟨fun a u => hg.invFun (f' a u), by fun_prop, fun a => ?_⟩
  rw [hg'κ]; rw [map_apply _ (by fun_prop)]; rw [← hf'κ]; rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end ProbabilityTheory.Kernel

/--
theorem `MeasureTheory.Measure.exists_measurable_map_eq` / 定理 `MeasureTheory.Measure.exists_measurable_map_eq`

English:
theorem MeasureTheory.Measure.exists_measurable_map_eq
  given: (μ : Measure Y) [IsProbabilityMeasure μ]
  proof: by
  obtain ⟨f, hf_meas, hf_map⟩ := Kernel.exists_measurable_map_eq_unitInterval (Kernel.const Unit μ)
  specialize hf_map ()
  exact ⟨f (), by fun_prop, by simpa⟩

中文:
定理 测度论.测度.存在_measurable_map_eq
  条件: (μ : 测度 Y) [是概率测度 μ]
  证明: by
  obtain ⟨f, hf_meas, hf_map⟩ := Kernel.exists_measurable_map_eq_unitInterval (Kernel.const Unit μ)
  specialize hf_map ()
  exact ⟨f (), by fun_prop, by simpa⟩

Depends on / 依赖: Kernel, Kernel.const, Kernel.exists_measurable_map_eq_unitInterval, exists_measurable_map_eq_unitInterval, fun_prop, hf_map, hf_meas, specialize
-/
theorem MeasureTheory.Measure.exists_measurable_map_eq (μ : Measure Y) [IsProbabilityMeasure μ] :
    exists (f : I -> Y), Measurable f ∧ volume.map f = μ := by
  obtain ⟨f, hf_meas, hf_map⟩ := Kernel.exists_measurable_map_eq_unitInterval (Kernel.const Unit μ)
  specialize hf_map ()
  exact ⟨f (), by fun_prop, by simpa⟩
