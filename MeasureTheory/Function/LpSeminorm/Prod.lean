/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# ℒp spaces and products

-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α β ε : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [TopologicalSpace ε] [ContinuousENorm ε]
  {μ : Measure α} {ν : Measure β} {p : Real>=0∞}

/--
lemma `MemLp.comp_fst` / 引理 `MemLp.comp_fst`

English:
lemma MemLp.comp_fst
  given: {f : α -> ε} (hf : MemLp f p μ) (ν : Measure β) [IsFiniteMeasure ν]
  proof: by
  have hf' : MemLp f p (ν .univ • μ) := hf.smul_measure (by simp)
  change MemLp (f ∘ Prod.fst) p (μ.prod ν)
  rw [← memLp_map_measure_iff ?_ (by fun_prop)]
  · simpa using hf'
  · simpa using hf'.1

中文:
引理 MemLp.comp_fst
  条件: {f : α -> ε} (hf : MemLp f p μ) (ν : Measure β) [IsFiniteMeasure ν]
  证明: by
  have hf' : MemLp f p (ν .univ • μ) := hf.smul_measure (by simp)
  change MemLp (f ∘ Prod.fst) p (μ.prod ν)
  rw [← memLp_map_measure_iff ?_ (by fun_prop)]
  · simpa using hf'
  · simpa using hf'.1

Depends on / 依赖: Prod.fst, fun_prop, hf.smul_measure, memLp_map_measure_iff, smul_measure
-/
lemma MemLp.comp_fst {f : α -> ε} (hf : MemLp f p μ) (ν : Measure β) [IsFiniteMeasure ν] :
    MemLp (fun x => f x.1) p (μ.prod ν) := by
  have hf' : MemLp f p (ν .univ • μ) := hf.smul_measure (by simp)
  change MemLp (f ∘ Prod.fst) p (μ.prod ν)
  rw [← memLp_map_measure_iff ?_ (by fun_prop)]
  · simpa using hf'
  · simpa using hf'.1

/--
lemma `MemLp.comp_snd` / 引理 `MemLp.comp_snd`

English:
lemma MemLp.comp_snd
  statement: {f : β -> ε} (hf : MemLp f p ν) (μ : Measure α) [IsFiniteMeasure μ]
  proof: by
  have hf' : MemLp f p (μ .univ • ν) := hf.smul_measure (by simp)
  change MemLp (f ∘ Prod.snd) p (μ.prod ν)
  rw [← memLp_map_measure_iff ?_ (by fun_prop)]
  · simpa using hf'
  · simpa using hf'.1

中文:
引理 MemLp.comp_snd
  结论: {f : β -> ε} (hf : MemLp f p ν) (μ : Measure α) [IsFiniteMeasure μ]
  证明: by
  have hf' : MemLp f p (μ .univ • ν) := hf.smul_measure (by simp)
  change MemLp (f ∘ Prod.snd) p (μ.prod ν)
  rw [← memLp_map_measure_iff ?_ (by fun_prop)]
  · simpa using hf'
  · simpa using hf'.1

Depends on / 依赖: Prod.snd, fun_prop, hf.smul_measure, memLp_map_measure_iff, smul_measure
-/
lemma MemLp.comp_snd {f : β -> ε} (hf : MemLp f p ν) (μ : Measure α) [IsFiniteMeasure μ]
    [SFinite ν] :
    MemLp (fun x => f x.2) p (μ.prod ν) := by
  have hf' : MemLp f p (μ .univ • ν) := hf.smul_measure (by simp)
  change MemLp (f ∘ Prod.snd) p (μ.prod ν)
  rw [← memLp_map_measure_iff ?_ (by fun_prop)]
  · simpa using hf'
  · simpa using hf'.1

end MeasureTheory
