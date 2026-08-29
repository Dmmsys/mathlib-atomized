/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Bernoulli distribution

We define the **Bernoulli distribution** over an arbitrary measurable space `X`. Given `x y : X`
and `p : I` (`I` is the `unitInterval`),
`Ber(x, y, p) := toNNReal p • dirac x + toNNReal (σ p) • dirac y`.
It is the measure which gives mass `p` to `{x}` and `1 - p` to `{y}`.

## Main definition

* `bernoulliMeasure x y p`: The measure `Ber(x, y, p)` which gives mass
  `p` to `{x}` and `1 - p` to `{y}`.

## Notation

* `Ber(x, y, p)`: notation for `bernoulliMeasure x y p`.

## Tags

Bernoulli distribution
-/

public section

open MeasureTheory Measure unitInterval
open scoped ENNReal

namespace ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {x y : X} {p : I}

/-- The **Bernoulli distribution** over an arbitrary measurable space `X`.
Given `x y : X` and `p : I` (`I` is the `unitInterval`),
it is the measure which gives mass `p` to `{x}` and `1 - p` to `{y}`. -/
@[expose]
/--
Definition of `bernoulliMeasure` / `bernoulliMeasure` 的定义

English:
definition bernoulliMeasure
  signature: (x y : X) (p : I)
  body: toNNReal p • dirac x + toNNReal (σ p) • dirac y

@[inherit_doc]
scoped notation "Ber(" x ", " y ", " p ")" => bernoulliMeasure x y p

中文:
定义 bernoulliMeasure
  签名: (x y : X) (p : I)
  定义体: toNNReal p • dirac x + toNNReal (σ p) • dirac y

@[inherit_doc]
scoped notation "Ber(" x ", " y ", " p ")" => bernoulliMeasure x y p

Depends on / 依赖: toNNReal
-/
noncomputable def bernoulliMeasure (x y : X) (p : I) : Measure X :=
  toNNReal p • dirac x + toNNReal (σ p) • dirac y

@[inherit_doc]
scoped notation "Ber(" x ", " y ", " p ")" => bernoulliMeasure x y p

/--
lemma `bernoulliMeasure_def` / 引理 `bernoulliMeasure_def`

English:
lemma bernoulliMeasure_def
  given: (x y : X) (p : I)
  proof: rfl

@[simp]

中文:
引理 bernoulliMeasure_def
  条件: (x y : X) (p : I)
  证明: rfl

@[simp]
-/
lemma bernoulliMeasure_def (x y : X) (p : I) :
    Ber(x, y, p) = toNNReal p • dirac x + toNNReal (σ p) • dirac y := rfl

@[simp]
/--
lemma `bernoulliMeasure_zero` / 引理 `bernoulliMeasure_zero`

English:
lemma bernoulliMeasure_zero
  given: (x y : X)
  statement: bernoulliMeasure x y 0 = dirac y
  proof: by
  simp [bernoulliMeasure_def]

@[simp]

中文:
引理 bernoulliMeasure_zero
  条件: (x y : X)
  结论: bernoulliMeasure x y 0 = dirac y
  证明: by
  simp [bernoulliMeasure_def]

@[simp]

Depends on / 依赖: bernoulliMeasure_def
-/
lemma bernoulliMeasure_zero (x y : X) : bernoulliMeasure x y 0 = dirac y := by
  simp [bernoulliMeasure_def]

@[simp]
/--
lemma `bernoulliMeasure_one` / 引理 `bernoulliMeasure_one`

English:
lemma bernoulliMeasure_one
  given: (x y : X)
  statement: bernoulliMeasure x y 1 = dirac x
  proof: by
  simp [bernoulliMeasure_def]

中文:
引理 bernoulliMeasure_one
  条件: (x y : X)
  结论: bernoulliMeasure x y 1 = dirac x
  证明: by
  simp [bernoulliMeasure_def]

Depends on / 依赖: bernoulliMeasure_def
-/
lemma bernoulliMeasure_one (x y : X) : bernoulliMeasure x y 1 = dirac x := by
  simp [bernoulliMeasure_def]

/--
lemma `bernoulliMeasure_apply` / 引理 `bernoulliMeasure_apply`

English:
lemma bernoulliMeasure_apply
  statement: (p : I) {s : Set X}
  proof: by
  split_ifs <;> simp_all [bernoulliMeasure_def, ← ENNReal.coe_add]

中文:
引理 bernoulliMeasure_apply
  结论: (p : I) {s : Set X}
  证明: by
  split_ifs <;> simp_all [bernoulliMeasure_def, ← ENNReal.coe_add]

Depends on / 依赖: ENNReal, ENNReal.coe_add, bernoulliMeasure_def, coe_add, split_ifs
-/
lemma bernoulliMeasure_apply (p : I) {s : Set X}
    (hs : MeasurableSet s) [DecidablePred (· in s)] :
    Ber(x, y, p) s =
      if x in s
        then if y in s
          then (1 : Real>=0∞)
          else toNNReal p
        else if y in s
          then toNNReal (σ p)
          else 0 := by
  split_ifs <;> simp_all [bernoulliMeasure_def, ← ENNReal.coe_add]

/--
lemma `bernoulliMeasure_real_apply` / 引理 `bernoulliMeasure_real_apply`

English:
lemma bernoulliMeasure_real_apply
  statement: (p : I) {s : Set X}
  proof: by
  simp [measureReal_def, bernoulliMeasure_apply p hs, apply_ite ENNReal.toReal]

@[simp]

中文:
引理 bernoulliMeasure_real_apply
  结论: (p : I) {s : Set X}
  证明: by
  simp [measureReal_def, bernoulliMeasure_apply p hs, apply_ite ENNReal.toReal]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.toReal, apply_ite, bernoulliMeasure_apply, measureReal_def, toReal
-/
lemma bernoulliMeasure_real_apply (p : I) {s : Set X}
    (hs : MeasurableSet s) [DecidablePred (· in s)] :
    Ber(x, y, p).real s =
      if x in s
        then if y in s
          then (1 : Real)
          else toNNReal p
        else if y in s
          then toNNReal (σ p)
          else 0 := by
  simp [measureReal_def, bernoulliMeasure_apply p hs, apply_ite ENNReal.toReal]

@[simp]
/--
lemma `bernoulliMeasure_apply_of_mem_of_mem` / 引理 `bernoulliMeasure_apply_of_mem_of_mem`

English:
lemma bernoulliMeasure_apply_of_mem_of_mem
  statement: (p : I) {s : Set X}
  proof: by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]

中文:
引理 bernoulliMeasure_apply_of_mem_of_mem
  结论: (p : I) {s : Set X}
  证明: by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]

Depends on / 依赖: bernoulliMeasure_apply, classical
-/
lemma bernoulliMeasure_apply_of_mem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x in s) (hy : y in s) :
    Ber(x, y, p) s = 1 := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
/--
lemma `bernoulliMeasure_real_apply_of_mem_of_mem` / 引理 `bernoulliMeasure_real_apply_of_mem_of_mem`

English:
lemma bernoulliMeasure_real_apply_of_mem_of_mem
  statement: (p : I) {s : Set X}
  proof: by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]

中文:
引理 bernoulliMeasure_real_apply_of_mem_of_mem
  结论: (p : I) {s : Set X}
  证明: by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]

Depends on / 依赖: bernoulliMeasure_real_apply, classical
-/
lemma bernoulliMeasure_real_apply_of_mem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x in s) (hy : y in s) :
    Ber(x, y, p).real s = 1 := by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]
/--
lemma `bernoulliMeasure_apply_of_mem_of_notMem` / 引理 `bernoulliMeasure_apply_of_mem_of_notMem`

English:
lemma bernoulliMeasure_apply_of_mem_of_notMem
  statement: (p : I) {s : Set X}
  proof: by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]

中文:
引理 bernoulliMeasure_apply_of_mem_of_notMem
  结论: (p : I) {s : Set X}
  证明: by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]

Depends on / 依赖: bernoulliMeasure_apply, classical
-/
lemma bernoulliMeasure_apply_of_mem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x in s) (hy : y ∉ s) :
    Ber(x, y, p) s = toNNReal p := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
/--
lemma `bernoulliMeasure_real_apply_of_mem_of_notMem` / 引理 `bernoulliMeasure_real_apply_of_mem_of_notMem`

English:
lemma bernoulliMeasure_real_apply_of_mem_of_notMem
  statement: (p : I) {s : Set X}
  proof: by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]

中文:
引理 bernoulliMeasure_real_apply_of_mem_of_notMem
  结论: (p : I) {s : Set X}
  证明: by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]

Depends on / 依赖: bernoulliMeasure_real_apply, classical
-/
lemma bernoulliMeasure_real_apply_of_mem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x in s) (hy : y ∉ s) :
    Ber(x, y, p).real s = p := by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]
/--
lemma `bernoulliMeasure_apply_of_notMem_of_mem` / 引理 `bernoulliMeasure_apply_of_notMem_of_mem`

English:
lemma bernoulliMeasure_apply_of_notMem_of_mem
  statement: (p : I) {s : Set X}
  proof: by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]

中文:
引理 bernoulliMeasure_apply_of_notMem_of_mem
  结论: (p : I) {s : Set X}
  证明: by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]

Depends on / 依赖: bernoulliMeasure_apply, classical
-/
lemma bernoulliMeasure_apply_of_notMem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y in s) :
    Ber(x, y, p) s = toNNReal (σ p) := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
/--
lemma `bernoulliMeasure_real_apply_of_notMem_of_mem` / 引理 `bernoulliMeasure_real_apply_of_notMem_of_mem`

English:
lemma bernoulliMeasure_real_apply_of_notMem_of_mem
  statement: (p : I) {s : Set X}
  proof: by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]

中文:
引理 bernoulliMeasure_real_apply_of_notMem_of_mem
  结论: (p : I) {s : Set X}
  证明: by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]

Depends on / 依赖: bernoulliMeasure_real_apply, classical
-/
lemma bernoulliMeasure_real_apply_of_notMem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y in s) :
    Ber(x, y, p).real s = 1 - p := by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]
/--
lemma `bernoulliMeasure_apply_of_notMem_of_notMem` / 引理 `bernoulliMeasure_apply_of_notMem_of_notMem`

English:
lemma bernoulliMeasure_apply_of_notMem_of_notMem
  statement: (p : I) {s : Set X}
  proof: by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]

中文:
引理 bernoulliMeasure_apply_of_notMem_of_notMem
  结论: (p : I) {s : Set X}
  证明: by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]

Depends on / 依赖: bernoulliMeasure_apply, classical
-/
lemma bernoulliMeasure_apply_of_notMem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∉ s) :
    Ber(x, y, p) s = 0 := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
/--
lemma `bernoulliMeasure_real_apply_of_notMem_of_notMem` / 引理 `bernoulliMeasure_real_apply_of_notMem_of_notMem`

English:
lemma bernoulliMeasure_real_apply_of_notMem_of_notMem
  statement: (p : I) {s : Set X}
  proof: by
  classical
  simp_all [bernoulliMeasure_real_apply]

中文:
引理 bernoulliMeasure_real_apply_of_notMem_of_notMem
  结论: (p : I) {s : Set X}
  证明: by
  classical
  simp_all [bernoulliMeasure_real_apply]

Depends on / 依赖: bernoulliMeasure_real_apply, classical
-/
lemma bernoulliMeasure_real_apply_of_notMem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∉ s) :
    Ber(x, y, p).real s = 0 := by
  classical
  simp_all [bernoulliMeasure_real_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsProbabilityMeasure Ber(x, y, p)
  body: by simp [bernoulliMeasure_def]

@[simp]

中文:
实例 :
  签名: IsProbabilityMeasure Ber(x, y, p)
  定义体: by simp [bernoulliMeasure_def]

@[simp]

Depends on / 依赖: bernoulliMeasure_def
-/
instance : IsProbabilityMeasure Ber(x, y, p) where
  measure_univ := by simp [bernoulliMeasure_def]

@[simp]
/--
theorem `bernoulliMeasure_self_eq_dirac` / 定理 `bernoulliMeasure_self_eq_dirac`

English:
theorem bernoulliMeasure_self_eq_dirac
  given: (x : X) (p : I)
  proof: by
  simp [bernoulliMeasure_def, ← add_smul]

@[simp]

中文:
定理 bernoulliMeasure_self_eq_dirac
  条件: (x : X) (p : I)
  证明: by
  simp [bernoulliMeasure_def, ← add_smul]

@[simp]

Depends on / 依赖: add_smul, bernoulliMeasure_def
-/
theorem bernoulliMeasure_self_eq_dirac (x : X) (p : I) :
    bernoulliMeasure x x p = dirac x := by
  simp [bernoulliMeasure_def, ← add_smul]

@[simp]
/--
theorem `map_bernoulliMeasure` / 定理 `map_bernoulliMeasure`

English:
theorem map_bernoulliMeasure
  statement: [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
  proof: by
  have hf (x : X) : AEMeasurable f (dirac x) := by fun_prop
  simp only [bernoulliMeasure_def]
  rw [AEMeasurable.map_add₀ (by fun_prop) (by fun_prop)]
  simp

中文:
定理 map_bernoulliMeasure
  结论: [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
  证明: by
  have hf (x : X) : AEMeasurable f (dirac x) := by fun_prop
  simp only [bernoulliMeasure_def]
  rw [AEMeasurable.map_add₀ (by fun_prop) (by fun_prop)]
  simp

Depends on / 依赖: AEMeasurable, AEMeasurable.map_add, bernoulliMeasure_def, fun_prop
-/
theorem map_bernoulliMeasure [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (x y : X) (f : X -> Y) (p : I) :
    Ber(x, y, p).map f = bernoulliMeasure (f x) (f y) p := by
  have hf (x : X) : AEMeasurable f (dirac x) := by fun_prop
  simp only [bernoulliMeasure_def]
  rw [AEMeasurable.map_add₀ (by fun_prop) (by fun_prop)]
  simp

/--
theorem `map_bernoulliMeasure'` / 定理 `map_bernoulliMeasure'`

English:
theorem map_bernoulliMeasure'
  given: (x y : X) {f : X -> Y} (hf : Measurable f) (p : I)
  proof: by
  simp [bernoulliMeasure_def, Measure.map_add _ _ hf, Measure.map_smul, map_dirac' hf]

中文:
定理 map_bernoulliMeasure'
  条件: (x y : X) {f : X -> Y} (hf : Measurable f) (p : I)
  证明: by
  simp [bernoulliMeasure_def, Measure.map_add _ _ hf, Measure.map_smul, map_dirac' hf]

Depends on / 依赖: Measure, Measure.map_add, Measure.map_smul, bernoulliMeasure_def, map_add, map_dirac, map_smul
-/
theorem map_bernoulliMeasure' (x y : X) {f : X -> Y} (hf : Measurable f) (p : I) :
    Ber(x, y, p).map f = bernoulliMeasure (f x) (f y) p := by
  simp [bernoulliMeasure_def, Measure.map_add _ _ hf, Measure.map_smul, map_dirac' hf]

section Integral

variable {E : Type*} [NormedAddCommGroup E]

/--
lemma `integrable_bernoulliMeasure` / 引理 `integrable_bernoulliMeasure`

English:
lemma integrable_bernoulliMeasure
  given: [MeasurableSingletonClass X] (x y : X) (p : I) (f : X -> E)
  proof: by
  simp [bernoulliMeasure_def, integrable_add_measure, integrable_dirac,
    Integrable.smul_measure_nnreal]

中文:
引理 integrable_bernoulliMeasure
  条件: [MeasurableSingletonClass X] (x y : X) (p : I) (f : X -> E)
  证明: by
  simp [bernoulliMeasure_def, integrable_add_measure, integrable_dirac,
    Integrable.smul_measure_nnreal]

Depends on / 依赖: Integrable, Integrable.smul_measure_nnreal, bernoulliMeasure_def, integrable_add_measure, integrable_dirac, smul_measure_nnreal
-/
lemma integrable_bernoulliMeasure [MeasurableSingletonClass X] (x y : X) (p : I) (f : X -> E) :
    Integrable f Ber(x, y, p) := by
  simp [bernoulliMeasure_def, integrable_add_measure, integrable_dirac,
    Integrable.smul_measure_nnreal]

variable [NormedSpace Real E] [CompleteSpace E]

/--
lemma `integral_bernoulliMeasure` / 引理 `integral_bernoulliMeasure`

English:
lemma integral_bernoulliMeasure
  given: [MeasurableSingletonClass X] (x y : X) (p : I) (f : X -> E)
  proof: by
  rw [bernoulliMeasure_def]; rw [integral_add_measure]
  · simp [NNReal.smul_def]
  all_goals exact (integrable_dirac (by simp)).smul_measure_nnreal

中文:
引理 integral_bernoulliMeasure
  条件: [MeasurableSingletonClass X] (x y : X) (p : I) (f : X -> E)
  证明: by
  rw [bernoulliMeasure_def]; rw [integral_add_measure]
  · simp [NNReal.smul_def]
  all_goals exact (integrable_dirac (by simp)).smul_measure_nnreal

Depends on / 依赖: NNReal, NNReal.smul_def, all_goals, bernoulliMeasure_def, integrable_dirac, integral_add_measure, smul_def, smul_measure_nnreal
-/
lemma integral_bernoulliMeasure [MeasurableSingletonClass X] (x y : X) (p : I) (f : X -> E) :
    ∫ z, f z ∂Ber(x, y, p) = (p : Real) • (f x) + (1 - p : Real) • (f y) := by
  rw [bernoulliMeasure_def]; rw [integral_add_measure]
  · simp [NNReal.smul_def]
  all_goals exact (integrable_dirac (by simp)).smul_measure_nnreal

end Integral

end ProbabilityTheory
