/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.UnitInterval

/-!
# Classes for probability measures

We introduce the following typeclasses for measures:

* `IsZeroOrProbabilityMeasure μ`: `μ univ = 0 ∨ μ univ = 1`;
* `IsProbabilityMeasure μ`: `μ univ = 1`.
-/

public section

namespace MeasureTheory

open Set Measure Filter Function ENNReal

variable {α β : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {s : Set α}

section IsZeroOrProbabilityMeasure

/--
Definition of `IsZeroOrProbabilityMeasure` / `IsZeroOrProbabilityMeasure` 的定义

English:
class IsZeroOrProbabilityMeasure
  parameters: (μ : Measure α)
  axioms and operations (1):
    - measure_univ : μ univ = 0 ∨ μ univ = 1

中文:
类 IsZeroOrProbabilityMeasure
  参数: (μ : Measure α)
  公理与运算 (1 个):
    - measure_univ : μ univ = 0 ∨ μ univ = 1
-/
class IsZeroOrProbabilityMeasure (μ : Measure α) : Prop where
  measure_univ : μ univ = 0 ∨ μ univ = 1

/--
lemma `isZeroOrProbabilityMeasure_iff` / 引理 `isZeroOrProbabilityMeasure_iff`

English:
lemma isZeroOrProbabilityMeasure_iff
  statement: IsZeroOrProbabilityMeasure μ ↔ μ univ = 0 ∨ μ univ = 1
  proof: ⟨fun _ => IsZeroOrProbabilityMeasure.measure_univ, IsZeroOrProbabilityMeasure.mk⟩

中文:
引理 isZeroOrProbabilityMeasure_iff
  结论: IsZeroOrProbabilityMeasure μ ↔ μ univ = 0 ∨ μ univ = 1
  证明: ⟨fun _ => IsZeroOrProbabilityMeasure.measure_univ, IsZeroOrProbabilityMeasure.mk⟩

Depends on / 依赖: IsZeroOrProbabilityMeasure, IsZeroOrProbabilityMeasure.measure_univ, IsZeroOrProbabilityMeasure.mk, measure_univ
-/
lemma isZeroOrProbabilityMeasure_iff : IsZeroOrProbabilityMeasure μ ↔ μ univ = 0 ∨ μ univ = 1 :=
  ⟨fun _ => IsZeroOrProbabilityMeasure.measure_univ, IsZeroOrProbabilityMeasure.mk⟩

/--
lemma `prob_le_one` / 引理 `prob_le_one`

English:
lemma prob_le_one
  given: {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α}
  statement: μ s <= 1
  proof: by
  apply (measure_mono (subset_univ _)).trans
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with h | h <;> simp [h]

@[simp]

中文:
引理 prob_le_one
  条件: {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α}
  结论: μ s <= 1
  证明: by
  apply (measure_mono (subset_univ _)).trans
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with h | h <;> simp [h]

@[simp]

Depends on / 依赖: IsZeroOrProbabilityMeasure, IsZeroOrProbabilityMeasure.measure_univ, measure_mono, measure_univ, subset_univ
-/
lemma prob_le_one {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α} : μ s <= 1 := by
  apply (measure_mono (subset_univ _)).trans
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with h | h <;> simp [h]

@[simp]
/--
lemma `measureReal_le_one` / 引理 `measureReal_le_one`

English:
lemma measureReal_le_one
  given: {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α}
  proof: ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one.symm ▸ prob_le_one)

@[simp]

中文:
引理 measureReal_le_one
  条件: {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α}
  证明: ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one.symm ▸ prob_le_one)

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_one.symm, ENNReal.toReal_le_of_le_ofReal, ofReal_one, prob_le_one, toReal_le_of_le_ofReal, zero_le_one
-/
lemma measureReal_le_one {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α} :
    μ.real s <= 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one.symm ▸ prob_le_one)

@[simp]
/--
theorem `one_le_prob_iff` / 定理 `one_le_prob_iff`

English:
theorem one_le_prob_iff
  given: {μ : Measure α} [IsZeroOrProbabilityMeasure μ]
  statement: 1 <= μ s ↔ μ s = 1
  proof: ⟨fun h => le_antisymm prob_le_one h, fun h => h ▸ le_refl _⟩

中文:
定理 one_le_prob_iff
  条件: {μ : Measure α} [IsZeroOrProbabilityMeasure μ]
  结论: 1 <= μ s ↔ μ s = 1
  证明: ⟨fun h => le_antisymm prob_le_one h, fun h => h ▸ le_refl _⟩

Depends on / 依赖: le_antisymm, le_refl, prob_le_one
-/
theorem one_le_prob_iff {μ : Measure α} [IsZeroOrProbabilityMeasure μ] : 1 <= μ s ↔ μ s = 1 :=
  ⟨fun h => le_antisymm prob_le_one h, fun h => h ▸ le_refl _⟩

instance (priority := 100) IsZeroOrProbabilityMeasure.toIsFiniteMeasure (μ : Measure α)
    [IsZeroOrProbabilityMeasure μ] : IsFiniteMeasure μ :=
  ⟨prob_le_one.trans_lt one_lt_top⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroOrProbabilityMeasure (0 : Measure α)
  body: ⟨Or.inl rfl⟩

中文:
实例 :
  签名: IsZeroOrProbabilityMeasure (0 : Measure α)
  定义体: ⟨Or.inl rfl⟩

Depends on / 依赖: Or.inl
-/
instance : IsZeroOrProbabilityMeasure (0 : Measure α) :=
  ⟨Or.inl rfl⟩

end IsZeroOrProbabilityMeasure

section IsProbabilityMeasure

/--
Definition of `IsProbabilityMeasure` / `IsProbabilityMeasure` 的定义

English:
class IsProbabilityMeasure
  parameters: (μ : Measure α)
  axioms and operations (1):
    - measure_univ : μ univ = 1

中文:
类 IsProbabilityMeasure
  参数: (μ : Measure α)
  公理与运算 (1 个):
    - measure_univ : μ univ = 1
-/
class IsProbabilityMeasure (μ : Measure α) : Prop where
  measure_univ : μ univ = 1

export MeasureTheory.IsProbabilityMeasure (measure_univ)

attribute [simp] IsProbabilityMeasure.measure_univ

/--
lemma `isProbabilityMeasure_iff` / 引理 `isProbabilityMeasure_iff`

English:
lemma isProbabilityMeasure_iff
  statement: IsProbabilityMeasure μ ↔ μ univ = 1
  proof: ⟨fun _ => measure_univ, IsProbabilityMeasure.mk⟩

中文:
引理 isProbabilityMeasure_iff
  结论: IsProbabilityMeasure μ ↔ μ univ = 1
  证明: ⟨fun _ => measure_univ, IsProbabilityMeasure.mk⟩

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.mk, measure_univ
-/
lemma isProbabilityMeasure_iff : IsProbabilityMeasure μ ↔ μ univ = 1 :=
  ⟨fun _ => measure_univ, IsProbabilityMeasure.mk⟩

instance (priority := 100) (μ : Measure α) [IsProbabilityMeasure μ] :
    IsZeroOrProbabilityMeasure μ :=
  ⟨Or.inr measure_univ⟩

/--
theorem `nonempty_of_isProbabilityMeasure` / 定理 `nonempty_of_isProbabilityMeasure`

English:
theorem nonempty_of_isProbabilityMeasure
  given: (μ : Measure α) [IsProbabilityMeasure μ]
  statement: Nonempty α
  proof: by
  by_contra! maybe_empty
  have : μ Set.univ = 0 := by
    rw [Set.univ_eq_empty_iff.mpr maybe_empty]; rw [measure_empty]
  simp at this

中文:
定理 nonempty_of_isProbabilityMeasure
  条件: (μ : Measure α) [IsProbabilityMeasure μ]
  结论: Nonempty α
  证明: by
  by_contra! maybe_empty
  have : μ Set.univ = 0 := by
    rw [Set.univ_eq_empty_iff.mpr maybe_empty]; rw [measure_empty]
  simp at this

Depends on / 依赖: Set.univ, Set.univ_eq_empty_iff.mpr, maybe_empty, measure_empty, univ_eq_empty_iff
-/
theorem nonempty_of_isProbabilityMeasure (μ : Measure α) [IsProbabilityMeasure μ] : Nonempty α := by
  by_contra! maybe_empty
  have : μ Set.univ = 0 := by
    rw [Set.univ_eq_empty_iff.mpr maybe_empty]; rw [measure_empty]
  simp at this

/--
theorem `IsProbabilityMeasure.ne_zero` / 定理 `IsProbabilityMeasure.ne_zero`

English:
theorem IsProbabilityMeasure.ne_zero
  given: (μ : Measure α) [IsProbabilityMeasure μ]
  statement: μ != 0
  proof: mt measure_univ_eq_zero.2 by simp [measure_univ]

中文:
定理 IsProbabilityMeasure.ne_zero
  条件: (μ : Measure α) [IsProbabilityMeasure μ]
  结论: μ != 0
  证明: mt measure_univ_eq_zero.2 by simp [measure_univ]

Depends on / 依赖: measure_univ, measure_univ_eq_zero
-/
theorem IsProbabilityMeasure.ne_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ != 0 :=
mt measure_univ_eq_zero.2 by simp [measure_univ]

instance (priority := 100) IsProbabilityMeasure.neZero (μ : Measure α) [IsProbabilityMeasure μ] :
    NeZero μ := ⟨IsProbabilityMeasure.ne_zero μ⟩

/--
theorem `IsProbabilityMeasure.ae_neBot` / 定理 `IsProbabilityMeasure.ae_neBot`

English:
theorem IsProbabilityMeasure.ae_neBot
  given: [IsProbabilityMeasure μ]
  statement: NeBot (ae μ)
  proof: inferInstance

中文:
定理 IsProbabilityMeasure.ae_neBot
  条件: [IsProbabilityMeasure μ]
  结论: NeBot (ae μ)
  证明: inferInstance
-/
theorem IsProbabilityMeasure.ae_neBot [IsProbabilityMeasure μ] : NeBot (ae μ) := inferInstance

/--
theorem `prob_add_prob_compl` / 定理 `prob_add_prob_compl`

English:
theorem prob_add_prob_compl
  given: [IsProbabilityMeasure μ] (h : MeasurableSet s)
  statement: μ s + μ sᶜ = 1
  proof: (measure_add_measure_compl h).trans measure_univ

中文:
定理 prob_add_prob_compl
  条件: [IsProbabilityMeasure μ] (h : MeasurableSet s)
  结论: μ s + μ sᶜ = 1
  证明: (measure_add_measure_compl h).trans measure_univ

Depends on / 依赖: measure_add_measure_compl, measure_univ
-/
theorem prob_add_prob_compl [IsProbabilityMeasure μ] (h : MeasurableSet s) : μ s + μ sᶜ = 1 :=
  (measure_add_measure_compl h).trans measure_univ

/--
lemma `probReal_add_probReal_compl` / 引理 `probReal_add_probReal_compl`

English:
lemma probReal_add_probReal_compl
  given: [IsProbabilityMeasure μ] (h : MeasurableSet s)
  proof: by
  simpa [Measure.real, ENNReal.toReal_add] using congr($(prob_add_prob_compl (μ := μ) h).toReal)

中文:
引理 probReal_add_probReal_compl
  条件: [IsProbabilityMeasure μ] (h : MeasurableSet s)
  证明: by
  simpa [Measure.real, ENNReal.toReal_add] using congr($(prob_add_prob_compl (μ := μ) h).toReal)

Depends on / 依赖: ENNReal, ENNReal.toReal_add, Measure, Measure.real, prob_add_prob_compl, toReal, toReal_add
-/
lemma probReal_add_probReal_compl [IsProbabilityMeasure μ] (h : MeasurableSet s) :
    μ.real s + μ.real sᶜ = 1 := by
  simpa [Measure.real, ENNReal.toReal_add] using congr($(prob_add_prob_compl (μ := μ) h).toReal)

/--
Instance `isProbabilityMeasureSMul` / 实例 `isProbabilityMeasureSMul`

English:
instance isProbabilityMeasureSMul
  signature: [IsFiniteMeasure μ] [NeZero μ]
  body: ⟨ENNReal.inv_mul_cancel (NeZero.ne (μ univ)) (measure_ne_top _ _)⟩

中文:
实例 isProbabilityMeasureSMul
  签名: [IsFiniteMeasure μ] [NeZero μ]
  定义体: ⟨ENNReal.inv_mul_cancel (NeZero.ne (μ univ)) (measure_ne_top _ _)⟩

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel, NeZero, NeZero.ne, inv_mul_cancel, measure_ne_top
-/
instance isProbabilityMeasureSMul [IsFiniteMeasure μ] [NeZero μ] :
    IsProbabilityMeasure ((μ univ)⁻¹ • μ) :=
  ⟨ENNReal.inv_mul_cancel (NeZero.ne (μ univ)) (measure_ne_top _ _)⟩

/--
Instance `isProbabilityMeasure_dite` / 实例 `isProbabilityMeasure_dite`

English:
instance isProbabilityMeasure_dite
  signature: {p : Prop} [Decidable p] {μ : p -> Measure α}
  body: by split <;> infer_instance

中文:
实例 isProbabilityMeasure_dite
  签名: {p : 命题} [Decidable p] {μ : p -> Measure α}
  定义体: by split <;> infer_instance

Depends on / 依赖: infer_instance
-/
instance isProbabilityMeasure_dite {p : Prop} [Decidable p] {μ : p -> Measure α}
    {ν : ¬ p -> Measure α} [forall h, IsProbabilityMeasure (μ h)] [forall h, IsProbabilityMeasure (ν h)] :
    IsProbabilityMeasure (dite p μ ν) := by split <;> infer_instance

/--
Instance `isProbabilityMeasure_ite` / 实例 `isProbabilityMeasure_ite`

English:
instance isProbabilityMeasure_ite
  signature: {p : Prop} [Decidable p] {μ ν : Measure α}
  body: by split <;> infer_instance

中文:
实例 isProbabilityMeasure_ite
  签名: {p : 命题} [Decidable p] {μ ν : Measure α}
  定义体: by split <;> infer_instance

Depends on / 依赖: infer_instance
-/
instance isProbabilityMeasure_ite {p : Prop} [Decidable p] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (ite p μ ν) := by split <;> infer_instance

open unitInterval in
instance {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {p : I} :
    IsProbabilityMeasure (toNNReal p • μ + toNNReal (σ p) • ν) where
  measure_univ := by simp [← ENNReal.coe_add]

variable [IsProbabilityMeasure μ] {p : α -> Prop} {f : β -> α}

/--
lemma `probReal_univ` / 引理 `probReal_univ`

English:
lemma probReal_univ
  statement: μ.real univ = 1
  proof: by simp [Measure.real]

中文:
引理 probReal_univ
  结论: μ.real univ = 1
  证明: by simp [Measure.real]
-/
@[simp] lemma probReal_univ : μ.real univ = 1 := by simp [Measure.real]

/--
lemma `isProbabilityMeasure_iff_real` / 引理 `isProbabilityMeasure_iff_real`

English:
lemma isProbabilityMeasure_iff_real
  given: {μ : Measure α}
  proof: by
  refine ⟨fun h => probReal_univ, fun h => ⟨(ENNReal.toReal_eq_one_iff (μ univ)).mp h⟩⟩

中文:
引理 isProbabilityMeasure_iff_real
  条件: {μ : Measure α}
  证明: by
  refine ⟨fun h => probReal_univ, fun h => ⟨(ENNReal.toReal_eq_one_iff (μ univ)).mp h⟩⟩

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_one_iff, probReal_univ, toReal_eq_one_iff
-/
lemma isProbabilityMeasure_iff_real {μ : Measure α} :
    IsProbabilityMeasure μ ↔ μ.real univ = 1 := by
  refine ⟨fun h => probReal_univ, fun h => ⟨(ENNReal.toReal_eq_one_iff (μ univ)).mp h⟩⟩

/--
theorem `Measure.isProbabilityMeasure_map` / 定理 `Measure.isProbabilityMeasure_map`

English:
theorem Measure.isProbabilityMeasure_map
  given: {f : α -> β} (hf : AEMeasurable f μ)
  proof: ⟨by simp [map_apply_of_aemeasurable, hf]⟩

中文:
定理 Measure.isProbabilityMeasure_map
  条件: {f : α -> β} (hf : AEMeasurable f μ)
  证明: ⟨by simp [map_apply_of_aemeasurable, hf]⟩

Depends on / 依赖: map_apply_of_aemeasurable
-/
theorem Measure.isProbabilityMeasure_map {f : α -> β} (hf : AEMeasurable f μ) :
    IsProbabilityMeasure (map f μ) :=
  ⟨by simp [map_apply_of_aemeasurable, hf]⟩

/--
theorem `Measure.isProbabilityMeasure_of_map` / 定理 `Measure.isProbabilityMeasure_of_map`

English:
theorem Measure.isProbabilityMeasure_of_map
  statement: {μ : Measure α} (f : α -> β)
  proof: by
    have hf : AEMeasurable f μ := AEMeasurable.of_map_ne_zero (IsProbabilityMeasure.ne_zero _)
    rw [← Set.preimage_univ (f := f)]; rw [← map_apply_of_aemeasurable hf .univ]
    exact IsProbabilityMeasure.measure_univ

中文:
定理 Measure.isProbabilityMeasure_of_map
  结论: {μ : Measure α} (f : α -> β)
  证明: by
    have hf : AEMeasurable f μ := AEMeasurable.of_map_ne_zero (IsProbabilityMeasure.ne_zero _)
    rw [← Set.preimage_univ (f := f)]; rw [← map_apply_of_aemeasurable hf .univ]
    exact IsProbabilityMeasure.measure_univ

Depends on / 依赖: AEMeasurable, AEMeasurable.of_map_ne_zero, IsProbabilityMeasure, IsProbabilityMeasure.measure_univ, IsProbabilityMeasure.ne_zero, Set.preimage_univ, map_apply_of_aemeasurable, measure_univ, ne_zero, of_map_ne_zero, preimage_univ
-/
theorem Measure.isProbabilityMeasure_of_map {μ : Measure α} (f : α -> β)
    [IsProbabilityMeasure (μ.map f)] : IsProbabilityMeasure μ where
  measure_univ := by
    have hf : AEMeasurable f μ := AEMeasurable.of_map_ne_zero (IsProbabilityMeasure.ne_zero _)
    rw [← Set.preimage_univ (f := f)]; rw [← map_apply_of_aemeasurable hf .univ]
    exact IsProbabilityMeasure.measure_univ

/--
theorem `Measure.isProbabilityMeasure_map_iff` / 定理 `Measure.isProbabilityMeasure_map_iff`

English:
theorem Measure.isProbabilityMeasure_map_iff
  statement: {μ : Measure α} {f : α -> β}
  proof: ⟨fun _ => isProbabilityMeasure_of_map f, fun _ => isProbabilityMeasure_map hf⟩

中文:
定理 Measure.isProbabilityMeasure_map_iff
  结论: {μ : Measure α} {f : α -> β}
  证明: ⟨fun _ => isProbabilityMeasure_of_map f, fun _ => isProbabilityMeasure_map hf⟩

Depends on / 依赖: isProbabilityMeasure_map, isProbabilityMeasure_of_map
-/
theorem Measure.isProbabilityMeasure_map_iff {μ : Measure α} {f : α -> β}
    (hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) ↔ IsProbabilityMeasure μ :=
  ⟨fun _ => isProbabilityMeasure_of_map f, fun _ => isProbabilityMeasure_map hf⟩

/--
Instance `IsProbabilityMeasure_comap_equiv` / 实例 `IsProbabilityMeasure_comap_equiv`

English:
instance IsProbabilityMeasure_comap_equiv
  signature: (f : β ≃ᵐ α)
  body: by
  rw [← MeasurableEquiv.map_symm]; exact isProbabilityMeasure_map f.symm.measurable.aemeasurable

中文:
实例 IsProbabilityMeasure_comap_equiv
  签名: (f : β ≃ᵐ α)
  定义体: by
  rw [← MeasurableEquiv.map_symm]; exact isProbabilityMeasure_map f.symm.measurable.aemeasurable

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.map_symm, aemeasurable, f.symm.measurable.aemeasurable, isProbabilityMeasure_map, map_symm, measurable
-/
instance IsProbabilityMeasure_comap_equiv (f : β ≃ᵐ α) : IsProbabilityMeasure (μ.comap f) := by
  rw [← MeasurableEquiv.map_symm]; exact isProbabilityMeasure_map f.symm.measurable.aemeasurable

/--
lemma `prob_compl_eq_one_sub₀` / 引理 `prob_compl_eq_one_sub₀`

English:
lemma prob_compl_eq_one_sub₀
  given: (h : NullMeasurableSet s μ)
  statement: μ sᶜ = 1 - μ s
  proof: by
  rw [measure_compl₀ h (measure_ne_top _ _)]; rw [measure_univ]

中文:
引理 prob_compl_eq_one_sub₀
  条件: (h : NullMeasurableSet s μ)
  结论: μ sᶜ = 1 - μ s
  证明: by
  rw [measure_compl₀ h (measure_ne_top _ _)]; rw [measure_univ]

Depends on / 依赖: measure_ne_top, measure_univ
-/
lemma prob_compl_eq_one_sub₀ (h : NullMeasurableSet s μ) : μ sᶜ = 1 - μ s := by
  rw [measure_compl₀ h (measure_ne_top _ _)]; rw [measure_univ]

/--
theorem `prob_compl_eq_one_sub` / 定理 `prob_compl_eq_one_sub`

English:
theorem prob_compl_eq_one_sub
  given: (hs : MeasurableSet s)
  statement: μ sᶜ = 1 - μ s
  proof: prob_compl_eq_one_sub₀ hs.nullMeasurableSet

中文:
定理 prob_compl_eq_one_sub
  条件: (hs : MeasurableSet s)
  结论: μ sᶜ = 1 - μ s
  证明: prob_compl_eq_one_sub₀ hs.nullMeasurableSet

Depends on / 依赖: hs.nullMeasurableSet, nullMeasurableSet
-/
theorem prob_compl_eq_one_sub (hs : MeasurableSet s) : μ sᶜ = 1 - μ s :=
  prob_compl_eq_one_sub₀ hs.nullMeasurableSet

/--
lemma `prob_compl_eq_zero_iff₀` / 引理 `prob_compl_eq_zero_iff₀`

English:
lemma prob_compl_eq_zero_iff₀
  given: (hs : NullMeasurableSet s μ)
  statement: μ sᶜ = 0 ↔ μ s = 1
  proof: by
  rw [prob_compl_eq_one_sub₀ hs]; rw [tsub_eq_zero_iff_le]; rw [one_le_prob_iff]

中文:
引理 prob_compl_eq_zero_iff₀
  条件: (hs : NullMeasurableSet s μ)
  结论: μ sᶜ = 0 ↔ μ s = 1
  证明: by
  rw [prob_compl_eq_one_sub₀ hs]; rw [tsub_eq_zero_iff_le]; rw [one_le_prob_iff]
-/
@[simp] lemma prob_compl_eq_zero_iff₀ (hs : NullMeasurableSet s μ) : μ sᶜ = 0 ↔ μ s = 1 := by
  rw [prob_compl_eq_one_sub₀ hs]; rw [tsub_eq_zero_iff_le]; rw [one_le_prob_iff]

/--
lemma `prob_compl_eq_zero_iff` / 引理 `prob_compl_eq_zero_iff`

English:
lemma prob_compl_eq_zero_iff
  given: (hs : MeasurableSet s)
  statement: μ sᶜ = 0 ↔ μ s = 1
  proof: by
  simp [hs]

中文:
引理 prob_compl_eq_zero_iff
  条件: (hs : MeasurableSet s)
  结论: μ sᶜ = 0 ↔ μ s = 1
  证明: by
  simp [hs]
-/
lemma prob_compl_eq_zero_iff (hs : MeasurableSet s) : μ sᶜ = 0 ↔ μ s = 1 := by
  simp [hs]

/--
lemma `prob_compl_eq_one_iff₀` / 引理 `prob_compl_eq_one_iff₀`

English:
lemma prob_compl_eq_one_iff₀
  given: (hs : NullMeasurableSet s μ)
  statement: μ sᶜ = 1 ↔ μ s = 0
  proof: by
  rw [← prob_compl_eq_zero_iff₀ hs.compl]; rw [compl_compl]

中文:
引理 prob_compl_eq_one_iff₀
  条件: (hs : NullMeasurableSet s μ)
  结论: μ sᶜ = 1 ↔ μ s = 0
  证明: by
  rw [← prob_compl_eq_zero_iff₀ hs.compl]; rw [compl_compl]
-/
@[simp] lemma prob_compl_eq_one_iff₀ (hs : NullMeasurableSet s μ) : μ sᶜ = 1 ↔ μ s = 0 := by
  rw [← prob_compl_eq_zero_iff₀ hs.compl]; rw [compl_compl]

/--
lemma `prob_compl_eq_one_iff` / 引理 `prob_compl_eq_one_iff`

English:
lemma prob_compl_eq_one_iff
  given: (hs : MeasurableSet s)
  statement: μ sᶜ = 1 ↔ μ s = 0
  proof: by
  simp [hs]

中文:
引理 prob_compl_eq_one_iff
  条件: (hs : MeasurableSet s)
  结论: μ sᶜ = 1 ↔ μ s = 0
  证明: by
  simp [hs]
-/
lemma prob_compl_eq_one_iff (hs : MeasurableSet s) : μ sᶜ = 1 ↔ μ s = 0 := by
  simp [hs]

/--
lemma `mem_ae_iff_prob_eq_one₀` / 引理 `mem_ae_iff_prob_eq_one₀`

English:
lemma mem_ae_iff_prob_eq_one₀
  given: (hs : NullMeasurableSet s μ)
  statement: s in ae μ ↔ μ s = 1
  proof: mem_ae_iff.trans prob_compl_eq_zero_iff₀ hs

中文:
引理 mem_ae_iff_prob_eq_one₀
  条件: (hs : NullMeasurableSet s μ)
  结论: s in ae μ ↔ μ s = 1
  证明: mem_ae_iff.trans prob_compl_eq_zero_iff₀ hs

Depends on / 依赖: mem_ae_iff, mem_ae_iff.trans
-/
lemma mem_ae_iff_prob_eq_one₀ (hs : NullMeasurableSet s μ) : s in ae μ ↔ μ s = 1 :=
mem_ae_iff.trans prob_compl_eq_zero_iff₀ hs

/--
lemma `mem_ae_iff_prob_eq_one` / 引理 `mem_ae_iff_prob_eq_one`

English:
lemma mem_ae_iff_prob_eq_one
  given: (hs : MeasurableSet s)
  statement: s in ae μ ↔ μ s = 1
  proof: mem_ae_iff.trans prob_compl_eq_zero_iff hs

中文:
引理 mem_ae_iff_prob_eq_one
  条件: (hs : MeasurableSet s)
  结论: s in ae μ ↔ μ s = 1
  证明: mem_ae_iff.trans prob_compl_eq_zero_iff hs

Depends on / 依赖: mem_ae_iff, mem_ae_iff.trans, prob_compl_eq_zero_iff
-/
lemma mem_ae_iff_prob_eq_one (hs : MeasurableSet s) : s in ae μ ↔ μ s = 1 :=
mem_ae_iff.trans prob_compl_eq_zero_iff hs

/--
lemma `ae_iff_prob_eq_one` / 引理 `ae_iff_prob_eq_one`

English:
lemma ae_iff_prob_eq_one
  given: (hp : Measurable p)
  statement: (forallᵐ a ∂μ, p a) ↔ μ {a | p a} = 1
  proof: mem_ae_iff_prob_eq_one hp.setOf

中文:
引理 ae_iff_prob_eq_one
  条件: (hp : Measurable p)
  结论: (对任意ᵐ a ∂μ, p a) ↔ μ {a | p a} = 1
  证明: mem_ae_iff_prob_eq_one hp.setOf

Depends on / 依赖: hp.setOf, mem_ae_iff_prob_eq_one
-/
lemma ae_iff_prob_eq_one (hp : Measurable p) : (forallᵐ a ∂μ, p a) ↔ μ {a | p a} = 1 :=
  mem_ae_iff_prob_eq_one hp.setOf

/--
lemma `isProbabilityMeasure_comap` / 引理 `isProbabilityMeasure_comap`

English:
lemma isProbabilityMeasure_comap
  statement: (hf : Injective f) (hf' : forallᵐ a ∂μ, a in range f)
  proof: by
    rw [comap_apply _ hf hf'' _ MeasurableSet.univ]; rw [← mem_ae_iff_prob_eq_one (hf'' _ MeasurableSet.univ)]
    simpa

中文:
引理 isProbabilityMeasure_comap
  结论: (hf : Injective f) (hf' : 对任意ᵐ a ∂μ, a in range f)
  证明: by
    rw [comap_apply _ hf hf'' _ MeasurableSet.univ]; rw [← mem_ae_iff_prob_eq_one (hf'' _ MeasurableSet.univ)]
    simpa

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, comap_apply, mem_ae_iff_prob_eq_one
-/
lemma isProbabilityMeasure_comap (hf : Injective f) (hf' : forallᵐ a ∂μ, a in range f)
    (hf'' : forall s, MeasurableSet s -> MeasurableSet (f '' s)) :
    IsProbabilityMeasure (μ.comap f) where
  measure_univ := by
    rw [comap_apply _ hf hf'' _ MeasurableSet.univ]; rw [← mem_ae_iff_prob_eq_one (hf'' _ MeasurableSet.univ)]
    simpa

/--
lemma `_root_.MeasurableEmbedding.isProbabilityMeasure_comap` / 引理 `_root_.MeasurableEmbedding.isProbabilityMeasure_comap`

English:
lemma _root_.MeasurableEmbedding.isProbabilityMeasure_comap
  statement: (hf : MeasurableEmbedding f)
  proof: isProbabilityMeasure_comap hf.injective hf' hf.measurableSet_image'

中文:
引理 _root_.MeasurableEmbedding.isProbabilityMeasure_comap
  结论: (hf : MeasurableEmbedding f)
  证明: isProbabilityMeasure_comap hf.injective hf' hf.measurableSet_image'
-/
protected lemma _root_.MeasurableEmbedding.isProbabilityMeasure_comap (hf : MeasurableEmbedding f)
    (hf' : forallᵐ a ∂μ, a in range f) : IsProbabilityMeasure (μ.comap f) :=
  isProbabilityMeasure_comap hf.injective hf' hf.measurableSet_image'

/--
Instance `isProbabilityMeasure_map_up` / 实例 `isProbabilityMeasure_map_up`

English:
instance isProbabilityMeasure_map_up
  signature: :
  body: isProbabilityMeasure_map measurable_up.aemeasurable

中文:
实例 isProbabilityMeasure_map_up
  签名: :
  定义体: isProbabilityMeasure_map measurable_up.aemeasurable

Depends on / 依赖: aemeasurable, isProbabilityMeasure_map, measurable_up, measurable_up.aemeasurable
-/
instance isProbabilityMeasure_map_up :
    IsProbabilityMeasure (μ.map ULift.up) := isProbabilityMeasure_map measurable_up.aemeasurable

/--
Instance `isProbabilityMeasure_comap_down` / 实例 `isProbabilityMeasure_comap_down`

English:
instance isProbabilityMeasure_comap_down
  signature: : IsProbabilityMeasure (μ.comap ULift.down)
  body: MeasurableEquiv.ulift.measurableEmbedding.isProbabilityMeasure_comap ae_of_all _ by
    simp [Function.Surjective.range_eq <| EquivLike.surjective _]

中文:
实例 isProbabilityMeasure_comap_down
  签名: : IsProbabilityMeasure (μ.comap ULift.down)
  定义体: MeasurableEquiv.ulift.measurableEmbedding.isProbabilityMeasure_comap ae_of_all _ by
    simp [Function.Surjective.range_eq <| EquivLike.surjective _]

Depends on / 依赖: EquivLike, EquivLike.surjective, Function, Function.Surjective.range_eq, MeasurableEquiv, MeasurableEquiv.ulift.measurableEmbedding.isProbabilityMeasure_comap, Surjective, ae_of_all, isProbabilityMeasure_comap, measurableEmbedding, range_eq, surjective
-/
instance isProbabilityMeasure_comap_down : IsProbabilityMeasure (μ.comap ULift.down) :=
MeasurableEquiv.ulift.measurableEmbedding.isProbabilityMeasure_comap ae_of_all _ by
    simp [Function.Surjective.range_eq <| EquivLike.surjective _]

/--
lemma `Measure.eq_of_le_of_isProbabilityMeasure` / 引理 `Measure.eq_of_le_of_isProbabilityMeasure`

English:
lemma Measure.eq_of_le_of_isProbabilityMeasure
  statement: {μ ν : Measure α}
  proof: eq_of_le_of_measure_univ_eq hμν (by simp)

中文:
引理 Measure.eq_of_le_of_isProbabilityMeasure
  结论: {μ ν : Measure α}
  证明: eq_of_le_of_measure_univ_eq hμν (by simp)

Depends on / 依赖: eq_of_le_of_measure_univ_eq
-/
lemma Measure.eq_of_le_of_isProbabilityMeasure {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ <= ν) : μ = ν :=
  eq_of_le_of_measure_univ_eq hμν (by simp)

end IsProbabilityMeasure

section IsZeroOrProbabilityMeasure

-- TODO: should infer_instance be considered normalising?
set_option linter.flexible false in
/--
Instance `isZeroOrProbabilityMeasureSMul` / 实例 `isZeroOrProbabilityMeasureSMul`

English:
instance isZeroOrProbabilityMeasureSMul
  signature: :
  body: by
  rcases eq_zero_or_neZero μ with rfl | h
  · simp; infer_instance
  rcases eq_top_or_lt_top (μ univ) with h | h
  · simp [h]; infer_instance
  have : IsFiniteMeasure μ := ⟨h⟩
  infer_instance

中文:
实例 isZeroOrProbabilityMeasureSMul
  签名: :
  定义体: by
  rcases eq_zero_or_neZero μ with rfl | h
  · simp; infer_instance
  rcases eq_top_or_lt_top (μ univ) with h | h
  · simp [h]; infer_instance
  have : IsFiniteMeasure μ := ⟨h⟩
  infer_instance

Depends on / 依赖: IsFiniteMeasure, eq_top_or_lt_top, eq_zero_or_neZero, infer_instance
-/
instance isZeroOrProbabilityMeasureSMul :
    IsZeroOrProbabilityMeasure ((μ univ)⁻¹ • μ) := by
  rcases eq_zero_or_neZero μ with rfl | h
  · simp; infer_instance
  rcases eq_top_or_lt_top (μ univ) with h | h
  · simp [h]; infer_instance
  have : IsFiniteMeasure μ := ⟨h⟩
  infer_instance

variable [IsZeroOrProbabilityMeasure μ] {p : α -> Prop} {f : β -> α}

variable (μ) in
/--
lemma `eq_zero_or_isProbabilityMeasure` / 引理 `eq_zero_or_isProbabilityMeasure`

English:
lemma eq_zero_or_isProbabilityMeasure
  statement: μ = 0 ∨ IsProbabilityMeasure μ
  proof: by
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with h | h
  · apply Or.inl (measure_univ_eq_zero.mp h)
  · exact Or.inr ⟨h⟩

中文:
引理 eq_zero_or_isProbabilityMeasure
  结论: μ = 0 ∨ IsProbabilityMeasure μ
  证明: by
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with h | h
  · apply Or.inl (measure_univ_eq_zero.mp h)
  · exact Or.inr ⟨h⟩

Depends on / 依赖: IsZeroOrProbabilityMeasure, IsZeroOrProbabilityMeasure.measure_univ, Or.inl, Or.inr, measure_univ, measure_univ_eq_zero, measure_univ_eq_zero.mp
-/
lemma eq_zero_or_isProbabilityMeasure : μ = 0 ∨ IsProbabilityMeasure μ := by
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with h | h
  · apply Or.inl (measure_univ_eq_zero.mp h)
  · exact Or.inr ⟨h⟩

instance {f : α -> β} : IsZeroOrProbabilityMeasure (map f μ) := by
  by_cases hf : AEMeasurable f μ
  · simpa [isZeroOrProbabilityMeasure_iff, hf] using IsZeroOrProbabilityMeasure.measure_univ
  · simp [isZeroOrProbabilityMeasure_iff, hf]

/--
lemma `prob_compl_lt_one_sub_of_lt_prob` / 引理 `prob_compl_lt_one_sub_of_lt_prob`

English:
lemma prob_compl_lt_one_sub_of_lt_prob
  given: {p : Real>=0∞} (hμs : p < μ s) (s_mble : MeasurableSet s)
  proof: by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp at hμs
  · rw [prob_compl_eq_one_sub s_mble]
    apply ENNReal.sub_lt_of_sub_lt prob_le_one (Or.inl one_ne_top)
    convert! hμs
    exact ENNReal.sub_sub_cancel one_ne_top (lt_of_lt_of_le hμs prob_le_one).le

中文:
引理 prob_compl_lt_one_sub_of_lt_prob
  条件: {p : 实数>=0∞} (hμs : p < μ s) (s_mble : MeasurableSet s)
  证明: by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp at hμs
  · rw [prob_compl_eq_one_sub s_mble]
    apply ENNReal.sub_lt_of_sub_lt prob_le_one (Or.inl one_ne_top)
    convert! hμs
    exact ENNReal.sub_sub_cancel one_ne_top (lt_of_lt_of_le hμs prob_le_one).le

Depends on / 依赖: ENNReal, ENNReal.sub_lt_of_sub_lt, ENNReal.sub_sub_cancel, Or.inl, convert, eq_zero_or_isProbabilityMeasure, lt_of_lt_of_le, one_ne_top, prob_compl_eq_one_sub, prob_le_one, s_mble, sub_lt_of_sub_lt, sub_sub_cancel
-/
lemma prob_compl_lt_one_sub_of_lt_prob {p : Real>=0∞} (hμs : p < μ s) (s_mble : MeasurableSet s) :
    μ sᶜ < 1 - p := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp at hμs
  · rw [prob_compl_eq_one_sub s_mble]
    apply ENNReal.sub_lt_of_sub_lt prob_le_one (Or.inl one_ne_top)
    convert! hμs
    exact ENNReal.sub_sub_cancel one_ne_top (lt_of_lt_of_le hμs prob_le_one).le

/--
lemma `prob_compl_le_one_sub_of_le_prob` / 引理 `prob_compl_le_one_sub_of_le_prob`

English:
lemma prob_compl_le_one_sub_of_le_prob
  given: {p : Real>=0∞} (hμs : p <= μ s) (s_mble : MeasurableSet s)
  proof: by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp
  · simpa [prob_compl_eq_one_sub s_mble] using tsub_le_tsub_left hμs 1

@[simp]

中文:
引理 prob_compl_le_one_sub_of_le_prob
  条件: {p : 实数>=0∞} (hμs : p <= μ s) (s_mble : MeasurableSet s)
  证明: by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp
  · simpa [prob_compl_eq_one_sub s_mble] using tsub_le_tsub_left hμs 1

@[simp]

Depends on / 依赖: eq_zero_or_isProbabilityMeasure, prob_compl_eq_one_sub, s_mble, tsub_le_tsub_left
-/
lemma prob_compl_le_one_sub_of_le_prob {p : Real>=0∞} (hμs : p <= μ s) (s_mble : MeasurableSet s) :
    μ sᶜ <= 1 - p := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp
  · simpa [prob_compl_eq_one_sub s_mble] using tsub_le_tsub_left hμs 1

@[simp]
/--
lemma `inv_measure_univ_smul_eq_self` / 引理 `inv_measure_univ_smul_eq_self`

English:
lemma inv_measure_univ_smul_eq_self
  statement: (μ univ)⁻¹ • μ = μ
  proof: by
  rcases eq_zero_or_isProbabilityMeasure μ with h | h <;> simp [h]

中文:
引理 inv_measure_univ_smul_eq_self
  结论: (μ univ)⁻¹ • μ = μ
  证明: by
  rcases eq_zero_or_isProbabilityMeasure μ with h | h <;> simp [h]

Depends on / 依赖: eq_zero_or_isProbabilityMeasure
-/
lemma inv_measure_univ_smul_eq_self : (μ univ)⁻¹ • μ = μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with h | h <;> simp [h]

end IsZeroOrProbabilityMeasure

end MeasureTheory
