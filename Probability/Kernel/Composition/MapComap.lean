/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Basic

/-!
# Map of a kernel by a measurable function

We define the map and comap of a kernel along a measurable function, as well as some often useful
particular cases.

## Main definitions

Kernels built from other kernels:
* `map (κ : Kernel α β) (f : β → γ) : Kernel α γ`
  `∫⁻ c, g c ∂(map κ f a) = ∫⁻ b, g (f b) ∂(κ a)`
* `comap (κ : Kernel α β) (f : γ → α) (hf : Measurable f) : Kernel γ β`
  `∫⁻ b, g b ∂(comap κ f hf c) = ∫⁻ b, g b ∂(κ (f c))`

## Main statements

* `lintegral_map`, `lintegral_comap`: Lebesgue integral of a function against the map or comap of
  a kernel.

-/

@[expose] public section


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

section MapComap

/-! ### map, comap -/


variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {f : β -> γ} {g : γ -> α}

/--
Definition of `mapOfMeasurable` / `mapOfMeasurable` 的定义

English:
definition mapOfMeasurable
  signature: (κ : Kernel α β) (f : β -> γ) (hf : Measurable f)
  body: (κ a).map f
  measurable' := by fun_prop

中文:
定义 mapOfMeasurable
  签名: (κ : Kernel α β) (f : β -> γ) (hf : Measurable f)
  定义体: (κ a).map f
  measurable' := by fun_prop
-/
noncomputable def mapOfMeasurable (κ : Kernel α β) (f : β -> γ) (hf : Measurable f) :
    Kernel α γ where
  toFun a := (κ a).map f
  measurable' := by fun_prop

open scoped Classical in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: [MeasurableSpace γ] (κ : Kernel α β) (f : β -> γ)
  body: if hf : Measurable f then mapOfMeasurable κ f hf else 0

中文:
定义 map
  签名: [MeasurableSpace γ] (κ : Kernel α β) (f : β -> γ)
  定义体: if hf : Measurable f then mapOfMeasurable κ f hf else 0

Depends on / 依赖: Measurable, mapOfMeasurable
-/
noncomputable def map [MeasurableSpace γ] (κ : Kernel α β) (f : β -> γ) : Kernel α γ :=
  if hf : Measurable f then mapOfMeasurable κ f hf else 0

/--
theorem `map_of_not_measurable` / 定理 `map_of_not_measurable`

English:
theorem map_of_not_measurable
  given: (κ : Kernel α β) {f : β -> γ} (hf : ¬(Measurable f))
  proof: by
  simp [map, hf]

中文:
定理 map_of_not_measurable
  条件: (κ : Kernel α β) {f : β -> γ} (hf : ¬(Measurable f))
  证明: by
  simp [map, hf]
-/
theorem map_of_not_measurable (κ : Kernel α β) {f : β -> γ} (hf : ¬(Measurable f)) :
    map κ f = 0 := by
  simp [map, hf]

/--
theorem `mapOfMeasurable_eq_map` / 定理 `mapOfMeasurable_eq_map`

English:
theorem mapOfMeasurable_eq_map
  given: (κ : Kernel α β) {f : β -> γ} (hf : Measurable f)
  proof: by
  simp [map, hf]

中文:
定理 mapOfMeasurable_eq_map
  条件: (κ : Kernel α β) {f : β -> γ} (hf : Measurable f)
  证明: by
  simp [map, hf]
-/
@[simp] theorem mapOfMeasurable_eq_map (κ : Kernel α β) {f : β -> γ} (hf : Measurable f) :
    mapOfMeasurable κ f hf = map κ f := by
  simp [map, hf]

/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: (κ : Kernel α β) (hf : Measurable f) (a : α)
  statement: map κ f a = (κ a).map f
  proof: by
  simp only [map, hf, ↓reduceDIte, mapOfMeasurable, coe_mk]

中文:
定理 map_apply
  条件: (κ : Kernel α β) (hf : Measurable f) (a : α)
  结论: map κ f a = (κ a).map f
  证明: by
  simp only [map, hf, ↓reduceDIte, mapOfMeasurable, coe_mk]

Depends on / 依赖: coe_mk, mapOfMeasurable, reduceDIte
-/
theorem map_apply (κ : Kernel α β) (hf : Measurable f) (a : α) : map κ f a = (κ a).map f := by
  simp only [map, hf, ↓reduceDIte, mapOfMeasurable, coe_mk]

/--
theorem `map_apply'` / 定理 `map_apply'`

English:
theorem map_apply'
  given: (κ : Kernel α β) (hf : Measurable f) (a : α) {s : Set γ} (hs : MeasurableSet s)
  proof: by rw [map_apply _ hf, Measure.map_apply hf hs]

中文:
定理 map_apply'
  条件: (κ : Kernel α β) (hf : Measurable f) (a : α) {s : Set γ} (hs : MeasurableSet s)
  证明: by rw [map_apply _ hf, Measure.map_apply hf hs]

Depends on / 依赖: Measure, Measure.map_apply, map_apply
-/
theorem map_apply' (κ : Kernel α β) (hf : Measurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    map κ f a s = κ a (f ⁻¹' s) := by rw [map_apply _ hf, Measure.map_apply hf hs]

/--
lemma `map_comp_right` / 引理 `map_comp_right`

English:
lemma map_comp_right
  statement: (κ : Kernel α β) {f : β -> γ} (hf : Measurable f) {g : γ -> δ}
  proof: by
  ext1 x
  rw [map_apply _ hg]; rw [map_apply _ hf]; rw [Measure.map_map hg hf]; rw [← map_apply _ (hg.comp hf)]

@[simp]

中文:
引理 map_comp_right
  结论: (κ : Kernel α β) {f : β -> γ} (hf : Measurable f) {g : γ -> δ}
  证明: by
  ext1 x
  rw [map_apply _ hg]; rw [map_apply _ hf]; rw [Measure.map_map hg hf]; rw [← map_apply _ (hg.comp hf)]

@[simp]

Depends on / 依赖: Measure, Measure.map_map, hg.comp, map_apply, map_map
-/
lemma map_comp_right (κ : Kernel α β) {f : β -> γ} (hf : Measurable f) {g : γ -> δ}
    (hg : Measurable g) : κ.map (g ∘ f) = (κ.map f).map g := by
  ext1 x
  rw [map_apply _ hg]; rw [map_apply _ hf]; rw [Measure.map_map hg hf]; rw [← map_apply _ (hg.comp hf)]

@[simp]
/--
lemma `map_zero` / 引理 `map_zero`

English:
lemma map_zero
  statement: Kernel.map (0 : Kernel α β) f = 0
  proof: by
  ext
  by_cases hf : Measurable f
  · simp [map_apply, hf]
  · simp [map_of_not_measurable _ hf]

@[simp]

中文:
引理 map_zero
  结论: Kernel.map (0 : Kernel α β) f = 0
  证明: by
  ext
  by_cases hf : Measurable f
  · simp [map_apply, hf]
  · simp [map_of_not_measurable _ hf]

@[simp]

Depends on / 依赖: Measurable, map_apply, map_of_not_measurable
-/
lemma map_zero : Kernel.map (0 : Kernel α β) f = 0 := by
  ext
  by_cases hf : Measurable f
  · simp [map_apply, hf]
  · simp [map_of_not_measurable _ hf]

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (κ : Kernel α β)
  statement: map κ id = κ
  proof: by
  ext a
  simp [map_apply, measurable_id]

@[simp]

中文:
引理 map_id
  条件: (κ : Kernel α β)
  结论: map κ id = κ
  证明: by
  ext a
  simp [map_apply, measurable_id]

@[simp]

Depends on / 依赖: map_apply, measurable_id
-/
lemma map_id (κ : Kernel α β) : map κ id = κ := by
  ext a
  simp [map_apply, measurable_id]

@[simp]
/--
lemma `map_id'` / 引理 `map_id'`

English:
lemma map_id'
  given: (κ : Kernel α β)
  statement: map κ (fun a => a) = κ
  proof: map_id κ

nonrec theorem lintegral_map (κ : Kernel α β) (hf : Measurable f) (a : α) {g' : γ -> Real>=0∞}
    (hg : Measurable g') : ∫⁻ b, g' b ∂map κ f a = ∫⁻ a, g' (f a) ∂κ a := by
  rw [map_apply _ hf]; rw [lintegral_map hg hf]

中文:
引理 map_id'
  条件: (κ : Kernel α β)
  结论: map κ (fun a => a) = κ
  证明: map_id κ

nonrec theorem lintegral_map (κ : Kernel α β) (hf : Measurable f) (a : α) {g' : γ -> Real>=0∞}
    (hg : Measurable g') : ∫⁻ b, g' b ∂map κ f a = ∫⁻ a, g' (f a) ∂κ a := by
  rw [map_apply _ hf]; rw [lintegral_map hg hf]

Depends on / 依赖: map_id
-/
lemma map_id' (κ : Kernel α β) : map κ (fun a => a) = κ := map_id κ

nonrec theorem lintegral_map (κ : Kernel α β) (hf : Measurable f) (a : α) {g' : γ -> Real>=0∞}
    (hg : Measurable g') : ∫⁻ b, g' b ∂map κ f a = ∫⁻ a, g' (f a) ∂κ a := by
  rw [map_apply _ hf]; rw [lintegral_map hg hf]

/--
lemma `map_apply_eq_iff_map_symm_apply_eq` / 引理 `map_apply_eq_iff_map_symm_apply_eq`

English:
lemma map_apply_eq_iff_map_symm_apply_eq
  given: (κ : Kernel α β) {f : β ≃ᵐ γ} (η : Kernel α γ)
  proof: by
  simp_rw [Kernel.ext_iff, map_apply _ f.measurable, map_apply _ f.symm.measurable,
    f.map_apply_eq_iff_map_symm_apply_eq]

中文:
引理 map_apply_eq_iff_map_symm_apply_eq
  条件: (κ : Kernel α β) {f : β ≃ᵐ γ} (η : Kernel α γ)
  证明: by
  simp_rw [Kernel.ext_iff, map_apply _ f.measurable, map_apply _ f.symm.measurable,
    f.map_apply_eq_iff_map_symm_apply_eq]

Depends on / 依赖: Kernel, Kernel.ext_iff, ext_iff, f.map_apply_eq_iff_map_symm_apply_eq, f.measurable, f.symm.measurable, map_apply, map_apply_eq_iff_map_symm_apply_eq, measurable, simp_rw
-/
lemma map_apply_eq_iff_map_symm_apply_eq (κ : Kernel α β) {f : β ≃ᵐ γ} (η : Kernel α γ) :
    κ.map f = η ↔ κ = η.map f.symm := by
  simp_rw [Kernel.ext_iff, map_apply _ f.measurable, map_apply _ f.symm.measurable,
    f.map_apply_eq_iff_map_symm_apply_eq]

/--
theorem `sum_map_seq` / 定理 `sum_map_seq`

English:
theorem sum_map_seq
  given: (κ : Kernel α β) [IsSFiniteKernel κ] (f : β -> γ)
  proof: by
  by_cases hf : Measurable f
  · ext a s hs
    rw [Kernel.sum_apply]; rw [map_apply' κ hf a hs]; rw [Measure.sum_apply _ hs]; rw [← measure_sum_seq κ]; rw [Measure.sum_apply _ (hf hs)]
    simp_rw [map_apply' _ hf _ hs]
  · simp [map_of_not_measurable _ hf]

中文:
定理 sum_map_seq
  条件: (κ : Kernel α β) [IsSFiniteKernel κ] (f : β -> γ)
  证明: by
  by_cases hf : Measurable f
  · ext a s hs
    rw [Kernel.sum_apply]; rw [map_apply' κ hf a hs]; rw [Measure.sum_apply _ hs]; rw [← measure_sum_seq κ]; rw [Measure.sum_apply _ (hf hs)]
    simp_rw [map_apply' _ hf _ hs]
  · simp [map_of_not_measurable _ hf]

Depends on / 依赖: Kernel, Kernel.sum_apply, Measurable, Measure, Measure.sum_apply, map_apply, map_of_not_measurable, measure_sum_seq, simp_rw, sum_apply
-/
theorem sum_map_seq (κ : Kernel α β) [IsSFiniteKernel κ] (f : β -> γ) :
    (Kernel.sum fun n => map (seq κ n) f) = map κ f := by
  by_cases hf : Measurable f
  · ext a s hs
    rw [Kernel.sum_apply]; rw [map_apply' κ hf a hs]; rw [Measure.sum_apply _ hs]; rw [← measure_sum_seq κ]; rw [Measure.sum_apply _ (hf hs)]
    simp_rw [map_apply' _ hf _ hs]
  · simp [map_of_not_measurable _ hf]

/--
lemma `IsMarkovKernel.map` / 引理 `IsMarkovKernel.map`

English:
lemma IsMarkovKernel.map
  given: (κ : Kernel α β) [IsMarkovKernel κ] (hf : Measurable f)
  proof: ⟨fun a => ⟨by rw [map_apply' κ hf a MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩⟩

中文:
引理 IsMarkovKernel.map
  条件: (κ : Kernel α β) [IsMarkovKernel κ] (hf : Measurable f)
  证明: ⟨fun a => ⟨by rw [map_apply' κ hf a MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Set.preimage_univ, map_apply, measure_univ, preimage_univ
-/
lemma IsMarkovKernel.map (κ : Kernel α β) [IsMarkovKernel κ] (hf : Measurable f) :
    IsMarkovKernel (map κ f) :=
  ⟨fun a => ⟨by rw [map_apply' κ hf a MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩⟩

/--
Instance `IsZeroOrMarkovKernel.map` / 实例 `IsZeroOrMarkovKernel.map`

English:
instance IsZeroOrMarkovKernel.map
  signature: (κ : Kernel α β) [IsZeroOrMarkovKernel κ] (f : β -> γ)
  body: by
  by_cases hf : Measurable f
  · rcases eq_zero_or_isMarkovKernel κ with rfl | h
    · simp only [map_zero]; infer_instance
    · have := IsMarkovKernel.map κ hf; infer_instance
  · simp only [map_of_not_measurable _ hf]; infer_instance

中文:
实例 IsZeroOrMarkovKernel.map
  签名: (κ : Kernel α β) [IsZeroOrMarkovKernel κ] (f : β -> γ)
  定义体: by
  by_cases hf : Measurable f
  · rcases eq_zero_or_isMarkovKernel κ with rfl | h
    · simp only [map_zero]; infer_instance
    · have := IsMarkovKernel.map κ hf; infer_instance
  · simp only [map_of_not_measurable _ hf]; infer_instance

Depends on / 依赖: IsMarkovKernel, IsMarkovKernel.map, Measurable, eq_zero_or_isMarkovKernel, infer_instance, map_of_not_measurable, map_zero
-/
instance IsZeroOrMarkovKernel.map (κ : Kernel α β) [IsZeroOrMarkovKernel κ] (f : β -> γ) :
    IsZeroOrMarkovKernel (map κ f) := by
  by_cases hf : Measurable f
  · rcases eq_zero_or_isMarkovKernel κ with rfl | h
    · simp only [map_zero]; infer_instance
    · have := IsMarkovKernel.map κ hf; infer_instance
  · simp only [map_of_not_measurable _ hf]; infer_instance

/--
Instance `IsFiniteKernel.map` / 实例 `IsFiniteKernel.map`

English:
instance IsFiniteKernel.map
  signature: (κ : Kernel α β) [IsFiniteKernel κ] (f : β -> γ)
  body: by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  by_cases hf : Measurable f
  · rw [map_apply' κ hf a MeasurableSet.univ]
    exact measure_le_bound κ a _
  · simp [map_of_not_measurable _ hf]

中文:
实例 IsFiniteKernel.map
  签名: (κ : Kernel α β) [IsFiniteKernel κ] (f : β -> γ)
  定义体: by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  by_cases hf : Measurable f
  · rw [map_apply' κ hf a MeasurableSet.univ]
    exact measure_le_bound κ a _
  · simp [map_of_not_measurable _ hf]

Depends on / 依赖: Measurable, MeasurableSet, MeasurableSet.univ, bound_lt_top, map_apply, map_of_not_measurable, measure_le_bound
-/
instance IsFiniteKernel.map (κ : Kernel α β) [IsFiniteKernel κ] (f : β -> γ) :
    IsFiniteKernel (map κ f) := by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  by_cases hf : Measurable f
  · rw [map_apply' κ hf a MeasurableSet.univ]
    exact measure_le_bound κ a _
  · simp [map_of_not_measurable _ hf]

/--
Instance `IsSFiniteKernel.map` / 实例 `IsSFiniteKernel.map`

English:
instance IsSFiniteKernel.map
  signature: (κ : Kernel α β) [IsSFiniteKernel κ] (f : β -> γ)
  body: ⟨⟨fun n => Kernel.map (seq κ n) f, inferInstance, (sum_map_seq κ f).symm⟩⟩

@[simp]

中文:
实例 IsSFiniteKernel.map
  签名: (κ : Kernel α β) [IsSFiniteKernel κ] (f : β -> γ)
  定义体: ⟨⟨fun n => Kernel.map (seq κ n) f, inferInstance, (sum_map_seq κ f).symm⟩⟩

@[simp]

Depends on / 依赖: Kernel, Kernel.map, sum_map_seq
-/
instance IsSFiniteKernel.map (κ : Kernel α β) [IsSFiniteKernel κ] (f : β -> γ) :
    IsSFiniteKernel (map κ f) :=
  ⟨⟨fun n => Kernel.map (seq κ n) f, inferInstance, (sum_map_seq κ f).symm⟩⟩

@[simp]
/--
lemma `map_const` / 引理 `map_const`

English:
lemma map_const
  given: (μ : Measure α) {f : α -> β} (hf : Measurable f)
  proof: by
  ext x s hs
  rw [map_apply' _ hf _ hs]; rw [const_apply]; rw [const_apply]; rw [Measure.map_apply hf hs]

中文:
引理 map_const
  条件: (μ : Measure α) {f : α -> β} (hf : Measurable f)
  证明: by
  ext x s hs
  rw [map_apply' _ hf _ hs]; rw [const_apply]; rw [const_apply]; rw [Measure.map_apply hf hs]

Depends on / 依赖: Measure, Measure.map_apply, const_apply, map_apply
-/
lemma map_const (μ : Measure α) {f : α -> β} (hf : Measurable f) :
    map (const γ μ) f = const γ (μ.map f) := by
  ext x s hs
  rw [map_apply' _ hf _ hs]; rw [const_apply]; rw [const_apply]; rw [Measure.map_apply hf hs]

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (κ : Kernel α β) (g : γ -> α) (hg : Measurable g)
  body: κ (g a)
  measurable' := κ.measurable.comp hg

@[simp, norm_cast]

中文:
定义 comap
  签名: (κ : Kernel α β) (g : γ -> α) (hg : Measurable g)
  定义体: κ (g a)
  measurable' := κ.measurable.comp hg

@[simp, norm_cast]
-/
def comap (κ : Kernel α β) (g : γ -> α) (hg : Measurable g) : Kernel γ β where
  toFun a := κ (g a)
  measurable' := κ.measurable.comp hg

@[simp, norm_cast]
/--
lemma `coe_comap` / 引理 `coe_comap`

English:
lemma coe_comap
  given: (κ : Kernel α β) (g : γ -> α) (hg : Measurable g)
  statement: κ.comap g hg = κ ∘ g
  proof: rfl

中文:
引理 coe_comap
  条件: (κ : Kernel α β) (g : γ -> α) (hg : Measurable g)
  结论: κ.comap g hg = κ ∘ g
  证明: rfl
-/
lemma coe_comap (κ : Kernel α β) (g : γ -> α) (hg : Measurable g) : κ.comap g hg = κ ∘ g := rfl

/--
theorem `comap_apply` / 定理 `comap_apply`

English:
theorem comap_apply
  given: (κ : Kernel α β) (hg : Measurable g) (c : γ)
  statement: comap κ g hg c = κ (g c)
  proof: rfl

中文:
定理 comap_apply
  条件: (κ : Kernel α β) (hg : Measurable g) (c : γ)
  结论: comap κ g hg c = κ (g c)
  证明: rfl
-/
theorem comap_apply (κ : Kernel α β) (hg : Measurable g) (c : γ) : comap κ g hg c = κ (g c) :=
  rfl

/--
theorem `comap_apply'` / 定理 `comap_apply'`

English:
theorem comap_apply'
  given: (κ : Kernel α β) (hg : Measurable g) (c : γ) (s : Set β)
  proof: rfl

@[simp]

中文:
定理 comap_apply'
  条件: (κ : Kernel α β) (hg : Measurable g) (c : γ) (s : Set β)
  证明: rfl

@[simp]
-/
theorem comap_apply' (κ : Kernel α β) (hg : Measurable g) (c : γ) (s : Set β) :
    comap κ g hg c s = κ (g c) s :=
  rfl

@[simp]
/--
lemma `comap_zero` / 引理 `comap_zero`

English:
lemma comap_zero
  given: (hg : Measurable g)
  statement: Kernel.comap (0 : Kernel α β) g hg = 0
  proof: by
  ext; simp

@[simp]

中文:
引理 comap_zero
  条件: (hg : Measurable g)
  结论: Kernel.comap (0 : Kernel α β) g hg = 0
  证明: by
  ext; simp

@[simp]
-/
lemma comap_zero (hg : Measurable g) : Kernel.comap (0 : Kernel α β) g hg = 0 := by
  ext; simp

@[simp]
/--
lemma `comap_id` / 引理 `comap_id`

English:
lemma comap_id
  given: (κ : Kernel α β)
  statement: comap κ id measurable_id = κ
  proof: by ext; simp

@[simp]

中文:
引理 comap_id
  条件: (κ : Kernel α β)
  结论: comap κ id measurable_id = κ
  证明: by ext; simp

@[simp]
-/
lemma comap_id (κ : Kernel α β) : comap κ id measurable_id = κ := by ext; simp

@[simp]
/--
lemma `comap_id'` / 引理 `comap_id'`

English:
lemma comap_id'
  given: (κ : Kernel α β)
  statement: comap κ (fun a => a) measurable_id = κ
  proof: comap_id κ

中文:
引理 comap_id'
  条件: (κ : Kernel α β)
  结论: comap κ (fun a => a) measurable_id = κ
  证明: comap_id κ

Depends on / 依赖: comap_id
-/
lemma comap_id' (κ : Kernel α β) : comap κ (fun a => a) measurable_id = κ := comap_id κ

/--
theorem `lintegral_comap` / 定理 `lintegral_comap`

English:
theorem lintegral_comap
  given: (κ : Kernel α β) (hg : Measurable g) (c : γ) (g' : β -> Real>=0∞)
  proof: rfl

中文:
定理 lintegral_comap
  条件: (κ : Kernel α β) (hg : Measurable g) (c : γ) (g' : β -> 实数>=0∞)
  证明: rfl
-/
theorem lintegral_comap (κ : Kernel α β) (hg : Measurable g) (c : γ) (g' : β -> Real>=0∞) :
    ∫⁻ b, g' b ∂comap κ g hg c = ∫⁻ b, g' b ∂κ (g c) :=
  rfl

/--
theorem `sum_comap_seq` / 定理 `sum_comap_seq`

English:
theorem sum_comap_seq
  given: (κ : Kernel α β) [IsSFiniteKernel κ] (hg : Measurable g)
  proof: by
  ext a s hs
  rw [Kernel.sum_apply]; rw [comap_apply' κ hg a s]; rw [Measure.sum_apply _ hs]; rw [← measure_sum_seq κ]; rw [Measure.sum_apply _ hs]
  simp_rw [comap_apply' _ hg _ s]

中文:
定理 sum_comap_seq
  条件: (κ : Kernel α β) [IsSFiniteKernel κ] (hg : Measurable g)
  证明: by
  ext a s hs
  rw [Kernel.sum_apply]; rw [comap_apply' κ hg a s]; rw [Measure.sum_apply _ hs]; rw [← measure_sum_seq κ]; rw [Measure.sum_apply _ hs]
  simp_rw [comap_apply' _ hg _ s]

Depends on / 依赖: Kernel, Kernel.sum_apply, Measure, Measure.sum_apply, comap_apply, measure_sum_seq, simp_rw, sum_apply
-/
theorem sum_comap_seq (κ : Kernel α β) [IsSFiniteKernel κ] (hg : Measurable g) :
    (Kernel.sum fun n => comap (seq κ n) g hg) = comap κ g hg := by
  ext a s hs
  rw [Kernel.sum_apply]; rw [comap_apply' κ hg a s]; rw [Measure.sum_apply _ hs]; rw [← measure_sum_seq κ]; rw [Measure.sum_apply _ hs]
  simp_rw [comap_apply' _ hg _ s]

/--
Instance `IsMarkovKernel.comap` / 实例 `IsMarkovKernel.comap`

English:
instance IsMarkovKernel.comap
  signature: (κ : Kernel α β) [IsMarkovKernel κ] (hg : Measurable g)
  body: ⟨fun a => ⟨by rw [comap_apply' κ hg a Set.univ, measure_univ]⟩⟩

中文:
实例 IsMarkovKernel.comap
  签名: (κ : Kernel α β) [IsMarkovKernel κ] (hg : Measurable g)
  定义体: ⟨fun a => ⟨by rw [comap_apply' κ hg a Set.univ, measure_univ]⟩⟩

Depends on / 依赖: Set.univ, comap_apply, measure_univ
-/
instance IsMarkovKernel.comap (κ : Kernel α β) [IsMarkovKernel κ] (hg : Measurable g) :
    IsMarkovKernel (comap κ g hg) :=
  ⟨fun a => ⟨by rw [comap_apply' κ hg a Set.univ, measure_univ]⟩⟩

/--
Instance `IsZeroOrMarkovKernel.comap` / 实例 `IsZeroOrMarkovKernel.comap`

English:
instance IsZeroOrMarkovKernel.comap
  signature: (κ : Kernel α β) [IsZeroOrMarkovKernel κ] (hg : Measurable g)
  body: by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp only [comap_zero]; infer_instance
  · have := IsMarkovKernel.comap κ hg; infer_instance

中文:
实例 IsZeroOrMarkovKernel.comap
  签名: (κ : Kernel α β) [IsZeroOrMarkovKernel κ] (hg : Measurable g)
  定义体: by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp only [comap_zero]; infer_instance
  · have := IsMarkovKernel.comap κ hg; infer_instance

Depends on / 依赖: IsMarkovKernel, IsMarkovKernel.comap, comap_zero, eq_zero_or_isMarkovKernel, infer_instance
-/
instance IsZeroOrMarkovKernel.comap (κ : Kernel α β) [IsZeroOrMarkovKernel κ] (hg : Measurable g) :
    IsZeroOrMarkovKernel (comap κ g hg) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp only [comap_zero]; infer_instance
  · have := IsMarkovKernel.comap κ hg; infer_instance

/--
Instance `IsFiniteKernel.comap` / 实例 `IsFiniteKernel.comap`

English:
instance IsFiniteKernel.comap
  signature: (κ : Kernel α β) [IsFiniteKernel κ] (hg : Measurable g)
  body: by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  rw [comap_apply' κ hg a Set.univ]
  exact measure_le_bound κ _ _

中文:
实例 IsFiniteKernel.comap
  签名: (κ : Kernel α β) [IsFiniteKernel κ] (hg : Measurable g)
  定义体: by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  rw [comap_apply' κ hg a Set.univ]
  exact measure_le_bound κ _ _

Depends on / 依赖: Set.univ, bound_lt_top, comap_apply, measure_le_bound
-/
instance IsFiniteKernel.comap (κ : Kernel α β) [IsFiniteKernel κ] (hg : Measurable g) :
    IsFiniteKernel (comap κ g hg) := by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  rw [comap_apply' κ hg a Set.univ]
  exact measure_le_bound κ _ _

/--
Instance `IsSFiniteKernel.comap` / 实例 `IsSFiniteKernel.comap`

English:
instance IsSFiniteKernel.comap
  signature: (κ : Kernel α β) [IsSFiniteKernel κ] (hg : Measurable g)
  body: ⟨⟨fun n => Kernel.comap (seq κ n) g hg, inferInstance, (sum_comap_seq κ hg).symm⟩⟩

中文:
实例 IsSFiniteKernel.comap
  签名: (κ : Kernel α β) [IsSFiniteKernel κ] (hg : Measurable g)
  定义体: ⟨⟨fun n => Kernel.comap (seq κ n) g hg, inferInstance, (sum_comap_seq κ hg).symm⟩⟩

Depends on / 依赖: Kernel, Kernel.comap, sum_comap_seq
-/
instance IsSFiniteKernel.comap (κ : Kernel α β) [IsSFiniteKernel κ] (hg : Measurable g) :
    IsSFiniteKernel (comap κ g hg) :=
  ⟨⟨fun n => Kernel.comap (seq κ n) g hg, inferInstance, (sum_comap_seq κ hg).symm⟩⟩

/--
lemma `comap_comp_right` / 引理 `comap_comp_right`

English:
lemma comap_comp_right
  given: (κ : Kernel α β) {f : δ -> γ} (hf : Measurable f) (hg : Measurable g)
  proof: by ext; simp

中文:
引理 comap_comp_right
  条件: (κ : Kernel α β) {f : δ -> γ} (hf : Measurable f) (hg : Measurable g)
  证明: by ext; simp
-/
lemma comap_comp_right (κ : Kernel α β) {f : δ -> γ} (hf : Measurable f) (hg : Measurable g) :
    comap κ (g ∘ f) (hg.comp hf) = (comap κ g hg).comap f hf := by ext; simp

/--
lemma `comap_map_comm` / 引理 `comap_map_comm`

English:
lemma comap_map_comm
  statement: (κ : Kernel β γ) {f : α -> β} {g : γ -> δ}
  proof: by
  ext x s _
  rw [comap_apply]; rw [map_apply _ hg]; rw [map_apply _ hg]; rw [comap_apply]

中文:
引理 comap_map_comm
  结论: (κ : Kernel β γ) {f : α -> β} {g : γ -> δ}
  证明: by
  ext x s _
  rw [comap_apply]; rw [map_apply _ hg]; rw [map_apply _ hg]; rw [comap_apply]

Depends on / 依赖: comap_apply, map_apply
-/
lemma comap_map_comm (κ : Kernel β γ) {f : α -> β} {g : γ -> δ}
    (hf : Measurable f) (hg : Measurable g) :
    comap (map κ g) f hf = map (comap κ f hf) g := by
  ext x s _
  rw [comap_apply]; rw [map_apply _ hg]; rw [map_apply _ hg]; rw [comap_apply]

end MapComap

@[simp]
/--
lemma `id_map` / 引理 `id_map`

English:
lemma id_map
  given: {f : α -> β} (hf : Measurable f)
  statement: Kernel.id.map f = deterministic f hf
  proof: by
  ext
  rw [Kernel.map_apply _ hf]; rw [Kernel.deterministic_apply]; rw [Kernel.id_apply]; rw [Measure.map_dirac' hf]

@[simp]

中文:
引理 id_map
  条件: {f : α -> β} (hf : Measurable f)
  结论: Kernel.id.map f = deterministic f hf
  证明: by
  ext
  rw [Kernel.map_apply _ hf]; rw [Kernel.deterministic_apply]; rw [Kernel.id_apply]; rw [Measure.map_dirac' hf]

@[simp]

Depends on / 依赖: Kernel, Kernel.deterministic_apply, Kernel.id_apply, Kernel.map_apply, Measure, Measure.map_dirac, deterministic_apply, id_apply, map_apply, map_dirac
-/
lemma id_map {f : α -> β} (hf : Measurable f) : Kernel.id.map f = deterministic f hf := by
  ext
  rw [Kernel.map_apply _ hf]; rw [Kernel.deterministic_apply]; rw [Kernel.id_apply]; rw [Measure.map_dirac' hf]

@[simp]
/--
lemma `id_comap` / 引理 `id_comap`

English:
lemma id_comap
  given: {f : α -> β} (hf : Measurable f)
  statement: Kernel.id.comap f hf = deterministic f hf
  proof: by
  ext
  rw [Kernel.comap_apply _ hf]; rw [Kernel.deterministic_apply]; rw [Kernel.id_apply]

中文:
引理 id_comap
  条件: {f : α -> β} (hf : Measurable f)
  结论: Kernel.id.comap f hf = deterministic f hf
  证明: by
  ext
  rw [Kernel.comap_apply _ hf]; rw [Kernel.deterministic_apply]; rw [Kernel.id_apply]

Depends on / 依赖: Kernel, Kernel.comap_apply, Kernel.deterministic_apply, Kernel.id_apply, comap_apply, deterministic_apply, id_apply
-/
lemma id_comap {f : α -> β} (hf : Measurable f) : Kernel.id.comap f hf = deterministic f hf := by
  ext
  rw [Kernel.comap_apply _ hf]; rw [Kernel.deterministic_apply]; rw [Kernel.id_apply]

/--
lemma `deterministic_map` / 引理 `deterministic_map`

English:
lemma deterministic_map
  given: {f : α -> β} (hf : Measurable f) {g : β -> γ} (hg : Measurable g)
  proof: by
  rw [← id_map]; rw [← map_comp_right _ hf hg]; rw [id_map]

中文:
引理 deterministic_map
  条件: {f : α -> β} (hf : Measurable f) {g : β -> γ} (hg : Measurable g)
  证明: by
  rw [← id_map]; rw [← map_comp_right _ hf hg]; rw [id_map]

Depends on / 依赖: id_map, map_comp_right
-/
lemma deterministic_map {f : α -> β} (hf : Measurable f) {g : β -> γ} (hg : Measurable g) :
    (deterministic f hf).map g = deterministic (g ∘ f) (hg.comp hf) := by
  rw [← id_map]; rw [← map_comp_right _ hf hg]; rw [id_map]

section FstSnd

variable {δ : Type*} {mδ : MeasurableSpace δ}

/--
Definition of `prodMkLeft` / `prodMkLeft` 的定义

English:
definition prodMkLeft
  signature: (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β)
  body: comap κ Prod.snd measurable_snd

中文:
定义 prodMkLeft
  签名: (γ : 类型) [MeasurableSpace γ] (κ : Kernel α β)
  定义体: comap κ Prod.snd measurable_snd

Depends on / 依赖: Prod.snd, measurable_snd
-/
def prodMkLeft (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β) : Kernel (γ × α) β :=
  comap κ Prod.snd measurable_snd

/--
Definition of `prodMkRight` / `prodMkRight` 的定义

English:
definition prodMkRight
  signature: (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β)
  body: comap κ Prod.fst measurable_fst

@[simp]

中文:
定义 prodMkRight
  签名: (γ : 类型) [MeasurableSpace γ] (κ : Kernel α β)
  定义体: comap κ Prod.fst measurable_fst

@[simp]

Depends on / 依赖: Prod.fst, measurable_fst
-/
def prodMkRight (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β) : Kernel (α × γ) β :=
  comap κ Prod.fst measurable_fst

@[simp]
/--
theorem `prodMkLeft_apply` / 定理 `prodMkLeft_apply`

English:
theorem prodMkLeft_apply
  given: (κ : Kernel α β) (ca : γ × α)
  statement: prodMkLeft γ κ ca = κ ca.snd
  proof: rfl

@[simp]

中文:
定理 prodMkLeft_apply
  条件: (κ : Kernel α β) (ca : γ × α)
  结论: prodMkLeft γ κ ca = κ ca.snd
  证明: rfl

@[simp]
-/
theorem prodMkLeft_apply (κ : Kernel α β) (ca : γ × α) : prodMkLeft γ κ ca = κ ca.snd :=
  rfl

@[simp]
/--
theorem `prodMkRight_apply` / 定理 `prodMkRight_apply`

English:
theorem prodMkRight_apply
  given: (κ : Kernel α β) (ca : α × γ)
  statement: prodMkRight γ κ ca = κ ca.fst
  proof: rfl

中文:
定理 prodMkRight_apply
  条件: (κ : Kernel α β) (ca : α × γ)
  结论: prodMkRight γ κ ca = κ ca.fst
  证明: rfl
-/
theorem prodMkRight_apply (κ : Kernel α β) (ca : α × γ) : prodMkRight γ κ ca = κ ca.fst := rfl

/--
theorem `prodMkLeft_apply'` / 定理 `prodMkLeft_apply'`

English:
theorem prodMkLeft_apply'
  given: (κ : Kernel α β) (ca : γ × α) (s : Set β)
  proof: rfl

中文:
定理 prodMkLeft_apply'
  条件: (κ : Kernel α β) (ca : γ × α) (s : Set β)
  证明: rfl
-/
theorem prodMkLeft_apply' (κ : Kernel α β) (ca : γ × α) (s : Set β) :
    prodMkLeft γ κ ca s = κ ca.snd s :=
  rfl

/--
theorem `prodMkRight_apply'` / 定理 `prodMkRight_apply'`

English:
theorem prodMkRight_apply'
  given: (κ : Kernel α β) (ca : α × γ) (s : Set β)
  proof: rfl

@[simp]

中文:
定理 prodMkRight_apply'
  条件: (κ : Kernel α β) (ca : α × γ) (s : Set β)
  证明: rfl

@[simp]
-/
theorem prodMkRight_apply' (κ : Kernel α β) (ca : α × γ) (s : Set β) :
    prodMkRight γ κ ca s = κ ca.fst s := rfl

@[simp]
/--
lemma `prodMkLeft_zero` / 引理 `prodMkLeft_zero`

English:
lemma prodMkLeft_zero
  statement: Kernel.prodMkLeft α (0 : Kernel β γ) = 0
  proof: by
  ext x s _; simp

@[simp]

中文:
引理 prodMkLeft_zero
  结论: Kernel.prodMkLeft α (0 : Kernel β γ) = 0
  证明: by
  ext x s _; simp

@[simp]
-/
lemma prodMkLeft_zero : Kernel.prodMkLeft α (0 : Kernel β γ) = 0 := by
  ext x s _; simp

@[simp]
/--
lemma `prodMkRight_zero` / 引理 `prodMkRight_zero`

English:
lemma prodMkRight_zero
  statement: Kernel.prodMkRight α (0 : Kernel β γ) = 0
  proof: by
  ext x s _; simp

@[simp]

中文:
引理 prodMkRight_zero
  结论: Kernel.prodMkRight α (0 : Kernel β γ) = 0
  证明: by
  ext x s _; simp

@[simp]
-/
lemma prodMkRight_zero : Kernel.prodMkRight α (0 : Kernel β γ) = 0 := by
  ext x s _; simp

@[simp]
/--
lemma `prodMkLeft_add` / 引理 `prodMkLeft_add`

English:
lemma prodMkLeft_add
  given: (κ η : Kernel α β)
  proof: by ext; simp

@[simp]

中文:
引理 prodMkLeft_add
  条件: (κ η : Kernel α β)
  证明: by ext; simp

@[simp]
-/
lemma prodMkLeft_add (κ η : Kernel α β) :
    prodMkLeft γ (κ + η) = prodMkLeft γ κ + prodMkLeft γ η := by ext; simp

@[simp]
/--
lemma `prodMkRight_add` / 引理 `prodMkRight_add`

English:
lemma prodMkRight_add
  given: (κ η : Kernel α β)
  proof: by ext; simp

中文:
引理 prodMkRight_add
  条件: (κ η : Kernel α β)
  证明: by ext; simp
-/
lemma prodMkRight_add (κ η : Kernel α β) :
    prodMkRight γ (κ + η) = prodMkRight γ κ + prodMkRight γ η := by ext; simp

/--
lemma `sum_prodMkLeft` / 引理 `sum_prodMkLeft`

English:
lemma sum_prodMkLeft
  given: {ι : Type*} [Countable ι] {κ : ι -> Kernel α β}
  proof: by
  ext
  simp_rw [sum_apply, prodMkLeft_apply, sum_apply]

中文:
引理 sum_prodMkLeft
  条件: {ι : 类型} [Countable ι] {κ : ι -> Kernel α β}
  证明: by
  ext
  simp_rw [sum_apply, prodMkLeft_apply, sum_apply]

Depends on / 依赖: prodMkLeft_apply, simp_rw, sum_apply
-/
lemma sum_prodMkLeft {ι : Type*} [Countable ι] {κ : ι -> Kernel α β} :
    Kernel.sum (fun i => Kernel.prodMkLeft γ (κ i)) = Kernel.prodMkLeft γ (Kernel.sum κ) := by
  ext
  simp_rw [sum_apply, prodMkLeft_apply, sum_apply]

/--
lemma `sum_prodMkRight` / 引理 `sum_prodMkRight`

English:
lemma sum_prodMkRight
  given: {ι : Type*} [Countable ι] {κ : ι -> Kernel α β}
  proof: by
  ext
  simp_rw [sum_apply, prodMkRight_apply, sum_apply]

中文:
引理 sum_prodMkRight
  条件: {ι : 类型} [Countable ι] {κ : ι -> Kernel α β}
  证明: by
  ext
  simp_rw [sum_apply, prodMkRight_apply, sum_apply]

Depends on / 依赖: prodMkRight_apply, simp_rw, sum_apply
-/
lemma sum_prodMkRight {ι : Type*} [Countable ι] {κ : ι -> Kernel α β} :
    Kernel.sum (fun i => Kernel.prodMkRight γ (κ i)) = Kernel.prodMkRight γ (Kernel.sum κ) := by
  ext
  simp_rw [sum_apply, prodMkRight_apply, sum_apply]

/--
theorem `lintegral_prodMkLeft` / 定理 `lintegral_prodMkLeft`

English:
theorem lintegral_prodMkLeft
  given: (κ : Kernel α β) (ca : γ × α) (g : β -> Real>=0∞)
  proof: rfl

中文:
定理 lintegral_prodMkLeft
  条件: (κ : Kernel α β) (ca : γ × α) (g : β -> 实数>=0∞)
  证明: rfl
-/
theorem lintegral_prodMkLeft (κ : Kernel α β) (ca : γ × α) (g : β -> Real>=0∞) :
    ∫⁻ b, g b ∂prodMkLeft γ κ ca = ∫⁻ b, g b ∂κ ca.snd := rfl

/--
theorem `lintegral_prodMkRight` / 定理 `lintegral_prodMkRight`

English:
theorem lintegral_prodMkRight
  given: (κ : Kernel α β) (ca : α × γ) (g : β -> Real>=0∞)
  proof: rfl

中文:
定理 lintegral_prodMkRight
  条件: (κ : Kernel α β) (ca : α × γ) (g : β -> 实数>=0∞)
  证明: rfl
-/
theorem lintegral_prodMkRight (κ : Kernel α β) (ca : α × γ) (g : β -> Real>=0∞) :
    ∫⁻ b, g b ∂prodMkRight γ κ ca = ∫⁻ b, g b ∂κ ca.fst := rfl

/--
Instance `IsMarkovKernel.prodMkLeft` / 实例 `IsMarkovKernel.prodMkLeft`

English:
instance IsMarkovKernel.prodMkLeft
  signature: (κ : Kernel α β) [IsMarkovKernel κ]
  body: by rw [Kernel.prodMkLeft]; infer_instance

中文:
实例 IsMarkovKernel.prodMkLeft
  签名: (κ : Kernel α β) [IsMarkovKernel κ]
  定义体: by rw [Kernel.prodMkLeft]; infer_instance

Depends on / 依赖: Kernel, Kernel.prodMkLeft, infer_instance, prodMkLeft
-/
instance IsMarkovKernel.prodMkLeft (κ : Kernel α β) [IsMarkovKernel κ] :
    IsMarkovKernel (prodMkLeft γ κ) := by rw [Kernel.prodMkLeft]; infer_instance

/--
Instance `IsMarkovKernel.prodMkRight` / 实例 `IsMarkovKernel.prodMkRight`

English:
instance IsMarkovKernel.prodMkRight
  signature: (κ : Kernel α β) [IsMarkovKernel κ]
  body: by rw [Kernel.prodMkRight]; infer_instance

中文:
实例 IsMarkovKernel.prodMkRight
  签名: (κ : Kernel α β) [IsMarkovKernel κ]
  定义体: by rw [Kernel.prodMkRight]; infer_instance

Depends on / 依赖: Kernel, Kernel.prodMkRight, MvPowerSeries, MvPowerSeries.map.isLocalHom, infer_instance, isLocalHom, prodMkRight
-/
instance IsMarkovKernel.prodMkRight (κ : Kernel α β) [IsMarkovKernel κ] :
    IsMarkovKernel (prodMkRight γ κ) := by rw [Kernel.prodMkRight]; infer_instance

/--
Instance `IsZeroOrMarkovKernel.prodMkLeft` / 实例 `IsZeroOrMarkovKernel.prodMkLeft`

English:
instance IsZeroOrMarkovKernel.prodMkLeft
  signature: (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
  body: by rw [Kernel.prodMkLeft]; infer_instance

中文:
实例 IsZeroOrMarkovKernel.prodMkLeft
  签名: (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
  定义体: by rw [Kernel.prodMkLeft]; infer_instance

Depends on / 依赖: Kernel, Kernel.prodMkLeft, infer_instance, prodMkLeft
-/
instance IsZeroOrMarkovKernel.prodMkLeft (κ : Kernel α β) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (prodMkLeft γ κ) := by rw [Kernel.prodMkLeft]; infer_instance

/--
Instance `IsZeroOrMarkovKernel.prodMkRight` / 实例 `IsZeroOrMarkovKernel.prodMkRight`

English:
instance IsZeroOrMarkovKernel.prodMkRight
  signature: (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
  body: by rw [Kernel.prodMkRight]; infer_instance

中文:
实例 IsZeroOrMarkovKernel.prodMkRight
  签名: (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
  定义体: by rw [Kernel.prodMkRight]; infer_instance

Depends on / 依赖: Kernel, Kernel.prodMkRight, infer_instance, prodMkRight
-/
instance IsZeroOrMarkovKernel.prodMkRight (κ : Kernel α β) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (prodMkRight γ κ) := by rw [Kernel.prodMkRight]; infer_instance

/--
Instance `IsFiniteKernel.prodMkLeft` / 实例 `IsFiniteKernel.prodMkLeft`

English:
instance IsFiniteKernel.prodMkLeft
  signature: (κ : Kernel α β) [IsFiniteKernel κ]
  body: by rw [Kernel.prodMkLeft]; infer_instance

中文:
实例 IsFiniteKernel.prodMkLeft
  签名: (κ : Kernel α β) [IsFiniteKernel κ]
  定义体: by rw [Kernel.prodMkLeft]; infer_instance

Depends on / 依赖: Kernel, Kernel.prodMkLeft, infer_instance, prodMkLeft
-/
instance IsFiniteKernel.prodMkLeft (κ : Kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel (prodMkLeft γ κ) := by rw [Kernel.prodMkLeft]; infer_instance

/--
Instance `IsFiniteKernel.prodMkRight` / 实例 `IsFiniteKernel.prodMkRight`

English:
instance IsFiniteKernel.prodMkRight
  signature: (κ : Kernel α β) [IsFiniteKernel κ]
  body: by rw [Kernel.prodMkRight]; infer_instance

中文:
实例 IsFiniteKernel.prodMkRight
  签名: (κ : Kernel α β) [IsFiniteKernel κ]
  定义体: by rw [Kernel.prodMkRight]; infer_instance

Depends on / 依赖: Kernel, Kernel.prodMkRight, infer_instance, prodMkRight
-/
instance IsFiniteKernel.prodMkRight (κ : Kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel (prodMkRight γ κ) := by rw [Kernel.prodMkRight]; infer_instance

/--
Instance `IsSFiniteKernel.prodMkLeft` / 实例 `IsSFiniteKernel.prodMkLeft`

English:
instance IsSFiniteKernel.prodMkLeft
  signature: (κ : Kernel α β) [IsSFiniteKernel κ]
  body: by rw [Kernel.prodMkLeft]; infer_instance

中文:
实例 IsSFiniteKernel.prodMkLeft
  签名: (κ : Kernel α β) [IsSFiniteKernel κ]
  定义体: by rw [Kernel.prodMkLeft]; infer_instance

Depends on / 依赖: Kernel, Kernel.prodMkLeft, infer_instance, prodMkLeft
-/
instance IsSFiniteKernel.prodMkLeft (κ : Kernel α β) [IsSFiniteKernel κ] :
    IsSFiniteKernel (prodMkLeft γ κ) := by rw [Kernel.prodMkLeft]; infer_instance

/--
Instance `IsSFiniteKernel.prodMkRight` / 实例 `IsSFiniteKernel.prodMkRight`

English:
instance IsSFiniteKernel.prodMkRight
  signature: (κ : Kernel α β) [IsSFiniteKernel κ]
  body: by rw [Kernel.prodMkRight]; infer_instance

中文:
实例 IsSFiniteKernel.prodMkRight
  签名: (κ : Kernel α β) [IsSFiniteKernel κ]
  定义体: by rw [Kernel.prodMkRight]; infer_instance

Depends on / 依赖: Kernel, Kernel.prodMkRight, infer_instance, prodMkRight
-/
instance IsSFiniteKernel.prodMkRight (κ : Kernel α β) [IsSFiniteKernel κ] :
    IsSFiniteKernel (prodMkRight γ κ) := by rw [Kernel.prodMkRight]; infer_instance

/--
lemma `isSFiniteKernel_prodMkLeft_unit` / 引理 `isSFiniteKernel_prodMkLeft_unit`

English:
lemma isSFiniteKernel_prodMkLeft_unit
  given: {κ : Kernel α β}
  proof: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  change IsSFiniteKernel ((prodMkLeft Unit κ).comap (fun a => ((), a)) (by fun_prop))
  infer_instance

中文:
引理 isSFiniteKernel_prodMkLeft_unit
  条件: {κ : Kernel α β}
  证明: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  change IsSFiniteKernel ((prodMkLeft Unit κ).comap (fun a => ((), a)) (by fun_prop))
  infer_instance

Depends on / 依赖: IsSFiniteKernel, fun_prop, infer_instance, prodMkLeft
-/
lemma isSFiniteKernel_prodMkLeft_unit {κ : Kernel α β} :
    IsSFiniteKernel (prodMkLeft Unit κ) ↔ IsSFiniteKernel κ := by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  change IsSFiniteKernel ((prodMkLeft Unit κ).comap (fun a => ((), a)) (by fun_prop))
  infer_instance

/--
lemma `isSFiniteKernel_prodMkRight_unit` / 引理 `isSFiniteKernel_prodMkRight_unit`

English:
lemma isSFiniteKernel_prodMkRight_unit
  given: {κ : Kernel α β}
  proof: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  change IsSFiniteKernel ((prodMkRight Unit κ).comap (fun a => (a, ())) (by fun_prop))
  infer_instance

中文:
引理 isSFiniteKernel_prodMkRight_unit
  条件: {κ : Kernel α β}
  证明: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  change IsSFiniteKernel ((prodMkRight Unit κ).comap (fun a => (a, ())) (by fun_prop))
  infer_instance

Depends on / 依赖: IsSFiniteKernel, fun_prop, infer_instance, prodMkRight
-/
lemma isSFiniteKernel_prodMkRight_unit {κ : Kernel α β} :
    IsSFiniteKernel (prodMkRight Unit κ) ↔ IsSFiniteKernel κ := by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  change IsSFiniteKernel ((prodMkRight Unit κ).comap (fun a => (a, ())) (by fun_prop))
  infer_instance

/--
lemma `map_prodMkLeft` / 引理 `map_prodMkLeft`

English:
lemma map_prodMkLeft
  given: (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β) (f : β -> δ)
  proof: by
  by_cases hf : Measurable f
  · simp only [map, hf, ↓reduceDIte]
    rfl
  · simp [map_of_not_measurable _ hf]

中文:
引理 map_prodMkLeft
  条件: (γ : 类型) [MeasurableSpace γ] (κ : Kernel α β) (f : β -> δ)
  证明: by
  by_cases hf : Measurable f
  · simp only [map, hf, ↓reduceDIte]
    rfl
  · simp [map_of_not_measurable _ hf]

Depends on / 依赖: Measurable, map_of_not_measurable, reduceDIte
-/
lemma map_prodMkLeft (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β) (f : β -> δ) :
    map (prodMkLeft γ κ) f = prodMkLeft γ (map κ f) := by
  by_cases hf : Measurable f
  · simp only [map, hf, ↓reduceDIte]
    rfl
  · simp [map_of_not_measurable _ hf]

/--
lemma `map_prodMkRight` / 引理 `map_prodMkRight`

English:
lemma map_prodMkRight
  given: (κ : Kernel α β) (γ : Type*) {mγ : MeasurableSpace γ} (f : β -> δ)
  proof: by
  by_cases hf : Measurable f
  · simp only [map, hf, ↓reduceDIte]
    rfl
  · simp [map_of_not_measurable _ hf]

中文:
引理 map_prodMkRight
  条件: (κ : Kernel α β) (γ : 类型) {mγ : MeasurableSpace γ} (f : β -> δ)
  证明: by
  by_cases hf : Measurable f
  · simp only [map, hf, ↓reduceDIte]
    rfl
  · simp [map_of_not_measurable _ hf]

Depends on / 依赖: Measurable, map_of_not_measurable, reduceDIte
-/
lemma map_prodMkRight (κ : Kernel α β) (γ : Type*) {mγ : MeasurableSpace γ} (f : β -> δ) :
    map (prodMkRight γ κ) f = prodMkRight γ (map κ f) := by
  by_cases hf : Measurable f
  · simp only [map, hf, ↓reduceDIte]
    rfl
  · simp [map_of_not_measurable _ hf]

/--
Definition of `swapLeft` / `swapLeft` 的定义

English:
definition swapLeft
  signature: (κ : Kernel (α × β) γ)
  body: comap κ Prod.swap measurable_swap

@[simp]

中文:
定义 swapLeft
  签名: (κ : Kernel (α × β) γ)
  定义体: comap κ Prod.swap measurable_swap

@[simp]

Depends on / 依赖: Prod.swap, measurable_swap
-/
def swapLeft (κ : Kernel (α × β) γ) : Kernel (β × α) γ :=
  comap κ Prod.swap measurable_swap

@[simp]
/--
lemma `swapLeft_zero` / 引理 `swapLeft_zero`

English:
lemma swapLeft_zero
  statement: swapLeft (0 : Kernel (α × β) γ) = 0
  proof: by simp [swapLeft]

@[simp]

中文:
引理 swapLeft_zero
  结论: swapLeft (0 : Kernel (α × β) γ) = 0
  证明: by simp [swapLeft]

@[simp]

Depends on / 依赖: swapLeft
-/
lemma swapLeft_zero : swapLeft (0 : Kernel (α × β) γ) = 0 := by simp [swapLeft]

@[simp]
/--
theorem `swapLeft_apply` / 定理 `swapLeft_apply`

English:
theorem swapLeft_apply
  given: (κ : Kernel (α × β) γ) (a : β × α)
  statement: swapLeft κ a = κ a.swap
  proof: rfl

中文:
定理 swapLeft_apply
  条件: (κ : Kernel (α × β) γ) (a : β × α)
  结论: swapLeft κ a = κ a.swap
  证明: rfl
-/
theorem swapLeft_apply (κ : Kernel (α × β) γ) (a : β × α) : swapLeft κ a = κ a.swap := rfl

/--
theorem `swapLeft_apply'` / 定理 `swapLeft_apply'`

English:
theorem swapLeft_apply'
  given: (κ : Kernel (α × β) γ) (a : β × α) (s : Set γ)
  proof: rfl

中文:
定理 swapLeft_apply'
  条件: (κ : Kernel (α × β) γ) (a : β × α) (s : Set γ)
  证明: rfl
-/
theorem swapLeft_apply' (κ : Kernel (α × β) γ) (a : β × α) (s : Set γ) :
    swapLeft κ a s = κ a.swap s := rfl

/--
theorem `lintegral_swapLeft` / 定理 `lintegral_swapLeft`

English:
theorem lintegral_swapLeft
  given: (κ : Kernel (α × β) γ) (a : β × α) (g : γ -> Real>=0∞)
  proof: by
  rw [swapLeft_apply]

中文:
定理 lintegral_swapLeft
  条件: (κ : Kernel (α × β) γ) (a : β × α) (g : γ -> 实数>=0∞)
  证明: by
  rw [swapLeft_apply]

Depends on / 依赖: swapLeft_apply
-/
theorem lintegral_swapLeft (κ : Kernel (α × β) γ) (a : β × α) (g : γ -> Real>=0∞) :
    ∫⁻ c, g c ∂swapLeft κ a = ∫⁻ c, g c ∂κ a.swap := by
  rw [swapLeft_apply]

/--
Instance `IsMarkovKernel.swapLeft` / 实例 `IsMarkovKernel.swapLeft`

English:
instance IsMarkovKernel.swapLeft
  signature: (κ : Kernel (α × β) γ) [IsMarkovKernel κ]
  body: by rw [Kernel.swapLeft]; infer_instance

中文:
实例 IsMarkovKernel.swapLeft
  签名: (κ : Kernel (α × β) γ) [IsMarkovKernel κ]
  定义体: by rw [Kernel.swapLeft]; infer_instance

Depends on / 依赖: Kernel, Kernel.swapLeft, infer_instance, swapLeft
-/
instance IsMarkovKernel.swapLeft (κ : Kernel (α × β) γ) [IsMarkovKernel κ] :
    IsMarkovKernel (swapLeft κ) := by rw [Kernel.swapLeft]; infer_instance

/--
Instance `IsFiniteKernel.swapLeft` / 实例 `IsFiniteKernel.swapLeft`

English:
instance IsFiniteKernel.swapLeft
  signature: (κ : Kernel (α × β) γ) [IsFiniteKernel κ]
  body: by rw [Kernel.swapLeft]; infer_instance

中文:
实例 IsFiniteKernel.swapLeft
  签名: (κ : Kernel (α × β) γ) [IsFiniteKernel κ]
  定义体: by rw [Kernel.swapLeft]; infer_instance

Depends on / 依赖: Kernel, Kernel.swapLeft, infer_instance, swapLeft
-/
instance IsFiniteKernel.swapLeft (κ : Kernel (α × β) γ) [IsFiniteKernel κ] :
    IsFiniteKernel (swapLeft κ) := by rw [Kernel.swapLeft]; infer_instance

/--
Instance `IsSFiniteKernel.swapLeft` / 实例 `IsSFiniteKernel.swapLeft`

English:
instance IsSFiniteKernel.swapLeft
  signature: (κ : Kernel (α × β) γ) [IsSFiniteKernel κ]
  body: by rw [Kernel.swapLeft]; infer_instance

中文:
实例 IsSFiniteKernel.swapLeft
  签名: (κ : Kernel (α × β) γ) [IsSFiniteKernel κ]
  定义体: by rw [Kernel.swapLeft]; infer_instance

Depends on / 依赖: Kernel, Kernel.swapLeft, infer_instance, swapLeft
-/
instance IsSFiniteKernel.swapLeft (κ : Kernel (α × β) γ) [IsSFiniteKernel κ] :
    IsSFiniteKernel (swapLeft κ) := by rw [Kernel.swapLeft]; infer_instance

/--
lemma `swapLeft_prodMkLeft` / 引理 `swapLeft_prodMkLeft`

English:
lemma swapLeft_prodMkLeft
  given: (κ : Kernel α β) (γ : Type*) {_ : MeasurableSpace γ}
  proof: rfl

中文:
引理 swapLeft_prodMkLeft
  条件: (κ : Kernel α β) (γ : 类型) {_ : MeasurableSpace γ}
  证明: rfl
-/
@[simp] lemma swapLeft_prodMkLeft (κ : Kernel α β) (γ : Type*) {_ : MeasurableSpace γ} :
    swapLeft (prodMkLeft γ κ) = prodMkRight γ κ := rfl

/--
lemma `swapLeft_prodMkRight` / 引理 `swapLeft_prodMkRight`

English:
lemma swapLeft_prodMkRight
  given: (κ : Kernel α β) (γ : Type*) {_ : MeasurableSpace γ}
  proof: rfl

中文:
引理 swapLeft_prodMkRight
  条件: (κ : Kernel α β) (γ : 类型) {_ : MeasurableSpace γ}
  证明: rfl
-/
@[simp] lemma swapLeft_prodMkRight (κ : Kernel α β) (γ : Type*) {_ : MeasurableSpace γ} :
    swapLeft (prodMkRight γ κ) = prodMkLeft γ κ := rfl

/--
Definition of `swapRight` / `swapRight` 的定义

English:
definition swapRight
  signature: (κ : Kernel α (β × γ))
  body: mapOfMeasurable κ Prod.swap measurable_swap

中文:
定义 swapRight
  签名: (κ : Kernel α (β × γ))
  定义体: mapOfMeasurable κ Prod.swap measurable_swap

Depends on / 依赖: Prod.swap, mapOfMeasurable, measurable_swap
-/
noncomputable def swapRight (κ : Kernel α (β × γ)) : Kernel α (γ × β) :=
  mapOfMeasurable κ Prod.swap measurable_swap

/--
lemma `swapRight_eq` / 引理 `swapRight_eq`

English:
lemma swapRight_eq
  given: (κ : Kernel α (β × γ))
  statement: swapRight κ = map κ Prod.swap
  proof: by
  simp [swapRight]

@[simp]

中文:
引理 swapRight_eq
  条件: (κ : Kernel α (β × γ))
  结论: swapRight κ = map κ Prod.swap
  证明: by
  simp [swapRight]

@[simp]

Depends on / 依赖: swapRight
-/
lemma swapRight_eq (κ : Kernel α (β × γ)) : swapRight κ = map κ Prod.swap := by
  simp [swapRight]

@[simp]
/--
lemma `swapRight_zero` / 引理 `swapRight_zero`

English:
lemma swapRight_zero
  statement: swapRight (0 : Kernel α (β × γ)) = 0
  proof: by simp [swapRight]

中文:
引理 swapRight_zero
  结论: swapRight (0 : Kernel α (β × γ)) = 0
  证明: by simp [swapRight]

Depends on / 依赖: swapRight
-/
lemma swapRight_zero : swapRight (0 : Kernel α (β × γ)) = 0 := by simp [swapRight]

/--
theorem `swapRight_apply` / 定理 `swapRight_apply`

English:
theorem swapRight_apply
  given: (κ : Kernel α (β × γ)) (a : α)
  statement: swapRight κ a = (κ a).map Prod.swap
  proof: rfl

中文:
定理 swapRight_apply
  条件: (κ : Kernel α (β × γ)) (a : α)
  结论: swapRight κ a = (κ a).map Prod.swap
  证明: rfl
-/
theorem swapRight_apply (κ : Kernel α (β × γ)) (a : α) : swapRight κ a = (κ a).map Prod.swap :=
  rfl

/--
theorem `swapRight_apply'` / 定理 `swapRight_apply'`

English:
theorem swapRight_apply'
  given: (κ : Kernel α (β × γ)) (a : α) {s : Set (γ × β)} (hs : MeasurableSet s)
  proof: by
  rw [swapRight_apply]; rw [Measure.map_apply measurable_swap hs]; rfl

中文:
定理 swapRight_apply'
  条件: (κ : Kernel α (β × γ)) (a : α) {s : Set (γ × β)} (hs : MeasurableSet s)
  证明: by
  rw [swapRight_apply]; rw [Measure.map_apply measurable_swap hs]; rfl

Depends on / 依赖: Measure, Measure.map_apply, map_apply, measurable_swap, swapRight_apply
-/
theorem swapRight_apply' (κ : Kernel α (β × γ)) (a : α) {s : Set (γ × β)} (hs : MeasurableSet s) :
    swapRight κ a s = κ a {p | p.swap in s} := by
  rw [swapRight_apply]; rw [Measure.map_apply measurable_swap hs]; rfl

/--
theorem `lintegral_swapRight` / 定理 `lintegral_swapRight`

English:
theorem lintegral_swapRight
  given: (κ : Kernel α (β × γ)) (a : α) {g : γ × β -> Real>=0∞} (hg : Measurable g)
  proof: by
  rw [swapRight_eq]; rw [lintegral_map _ measurable_swap a hg]

中文:
定理 lintegral_swapRight
  条件: (κ : Kernel α (β × γ)) (a : α) {g : γ × β -> 实数>=0∞} (hg : Measurable g)
  证明: by
  rw [swapRight_eq]; rw [lintegral_map _ measurable_swap a hg]

Depends on / 依赖: lintegral_map, measurable_swap, swapRight_eq
-/
theorem lintegral_swapRight (κ : Kernel α (β × γ)) (a : α) {g : γ × β -> Real>=0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂swapRight κ a = ∫⁻ bc : β × γ, g bc.swap ∂κ a := by
  rw [swapRight_eq]; rw [lintegral_map _ measurable_swap a hg]

/--
Instance `IsMarkovKernel.swapRight` / 实例 `IsMarkovKernel.swapRight`

English:
instance IsMarkovKernel.swapRight
  signature: (κ : Kernel α (β × γ)) [IsMarkovKernel κ]
  body: by
  rw [Kernel.swapRight_eq]; exact IsMarkovKernel.map _ measurable_swap

中文:
实例 IsMarkovKernel.swapRight
  签名: (κ : Kernel α (β × γ)) [IsMarkovKernel κ]
  定义体: by
  rw [Kernel.swapRight_eq]; exact IsMarkovKernel.map _ measurable_swap

Depends on / 依赖: IsMarkovKernel, IsMarkovKernel.map, Kernel, Kernel.swapRight_eq, measurable_swap, swapRight_eq
-/
instance IsMarkovKernel.swapRight (κ : Kernel α (β × γ)) [IsMarkovKernel κ] :
    IsMarkovKernel (swapRight κ) := by
  rw [Kernel.swapRight_eq]; exact IsMarkovKernel.map _ measurable_swap

/--
Instance `IsZeroOrMarkovKernel.swapRight` / 实例 `IsZeroOrMarkovKernel.swapRight`

English:
instance IsZeroOrMarkovKernel.swapRight
  signature: (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ]
  body: by rw [Kernel.swapRight_eq]; infer_instance

中文:
实例 IsZeroOrMarkovKernel.swapRight
  签名: (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ]
  定义体: by rw [Kernel.swapRight_eq]; infer_instance

Depends on / 依赖: Kernel, Kernel.swapRight_eq, infer_instance, swapRight_eq
-/
instance IsZeroOrMarkovKernel.swapRight (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (swapRight κ) := by rw [Kernel.swapRight_eq]; infer_instance

/--
Instance `IsFiniteKernel.swapRight` / 实例 `IsFiniteKernel.swapRight`

English:
instance IsFiniteKernel.swapRight
  signature: (κ : Kernel α (β × γ)) [IsFiniteKernel κ]
  body: by rw [Kernel.swapRight_eq]; infer_instance

中文:
实例 IsFiniteKernel.swapRight
  签名: (κ : Kernel α (β × γ)) [IsFiniteKernel κ]
  定义体: by rw [Kernel.swapRight_eq]; infer_instance

Depends on / 依赖: Kernel, Kernel.swapRight_eq, infer_instance, swapRight_eq
-/
instance IsFiniteKernel.swapRight (κ : Kernel α (β × γ)) [IsFiniteKernel κ] :
    IsFiniteKernel (swapRight κ) := by rw [Kernel.swapRight_eq]; infer_instance

/--
Instance `IsSFiniteKernel.swapRight` / 实例 `IsSFiniteKernel.swapRight`

English:
instance IsSFiniteKernel.swapRight
  signature: (κ : Kernel α (β × γ)) [IsSFiniteKernel κ]
  body: by rw [Kernel.swapRight_eq]; infer_instance

中文:
实例 IsSFiniteKernel.swapRight
  签名: (κ : Kernel α (β × γ)) [IsSFiniteKernel κ]
  定义体: by rw [Kernel.swapRight_eq]; infer_instance

Depends on / 依赖: Kernel, Kernel.swapRight_eq, infer_instance, swapRight_eq
-/
instance IsSFiniteKernel.swapRight (κ : Kernel α (β × γ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (swapRight κ) := by rw [Kernel.swapRight_eq]; infer_instance

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: (κ : Kernel α (β × γ))
  body: mapOfMeasurable κ Prod.fst measurable_fst

中文:
定义 fst
  签名: (κ : Kernel α (β × γ))
  定义体: mapOfMeasurable κ Prod.fst measurable_fst

Depends on / 依赖: Prod.fst, mapOfMeasurable, measurable_fst
-/
noncomputable def fst (κ : Kernel α (β × γ)) : Kernel α β :=
  mapOfMeasurable κ Prod.fst measurable_fst

/--
theorem `fst_eq` / 定理 `fst_eq`

English:
theorem fst_eq
  given: (κ : Kernel α (β × γ))
  statement: fst κ = map κ Prod.fst
  proof: by simp [fst]

中文:
定理 fst_eq
  条件: (κ : Kernel α (β × γ))
  结论: fst κ = map κ Prod.fst
  证明: by simp [fst]
-/
theorem fst_eq (κ : Kernel α (β × γ)) : fst κ = map κ Prod.fst := by simp [fst]

/--
theorem `fst_apply` / 定理 `fst_apply`

English:
theorem fst_apply
  given: (κ : Kernel α (β × γ)) (a : α)
  statement: fst κ a = (κ a).map Prod.fst
  proof: rfl

中文:
定理 fst_apply
  条件: (κ : Kernel α (β × γ)) (a : α)
  结论: fst κ a = (κ a).map Prod.fst
  证明: rfl
-/
theorem fst_apply (κ : Kernel α (β × γ)) (a : α) : fst κ a = (κ a).map Prod.fst :=
  rfl

/--
theorem `fst_apply'` / 定理 `fst_apply'`

English:
theorem fst_apply'
  given: (κ : Kernel α (β × γ)) (a : α) {s : Set β} (hs : MeasurableSet s)
  proof: by rw [fst_apply, Measure.map_apply measurable_fst hs]; rfl

中文:
定理 fst_apply'
  条件: (κ : Kernel α (β × γ)) (a : α) {s : Set β} (hs : MeasurableSet s)
  证明: by rw [fst_apply, Measure.map_apply measurable_fst hs]; rfl

Depends on / 依赖: Measure, Measure.map_apply, fst_apply, map_apply, measurable_fst
-/
theorem fst_apply' (κ : Kernel α (β × γ)) (a : α) {s : Set β} (hs : MeasurableSet s) :
    fst κ a s = κ a {p | p.1 in s} := by rw [fst_apply, Measure.map_apply measurable_fst hs]; rfl

/--
theorem `fst_real_apply` / 定理 `fst_real_apply`

English:
theorem fst_real_apply
  given: (κ : Kernel α (β × γ)) (a : α) {s : Set β} (hs : MeasurableSet s)
  proof: by
  simp [fst_apply', hs, measureReal_def]

@[simp]

中文:
定理 fst_real_apply
  条件: (κ : Kernel α (β × γ)) (a : α) {s : Set β} (hs : MeasurableSet s)
  证明: by
  simp [fst_apply', hs, measureReal_def]

@[simp]

Depends on / 依赖: fst_apply, measureReal_def
-/
theorem fst_real_apply (κ : Kernel α (β × γ)) (a : α) {s : Set β} (hs : MeasurableSet s) :
    (fst κ a).real s = (κ a).real {p | p.1 in s} := by
  simp [fst_apply', hs, measureReal_def]

@[simp]
/--
lemma `fst_zero` / 引理 `fst_zero`

English:
lemma fst_zero
  statement: fst (0 : Kernel α (β × γ)) = 0
  proof: by simp [fst]

中文:
引理 fst_zero
  结论: fst (0 : Kernel α (β × γ)) = 0
  证明: by simp [fst]
-/
lemma fst_zero : fst (0 : Kernel α (β × γ)) = 0 := by simp [fst]

/--
theorem `lintegral_fst` / 定理 `lintegral_fst`

English:
theorem lintegral_fst
  given: (κ : Kernel α (β × γ)) (a : α) {g : β -> Real>=0∞} (hg : Measurable g)
  proof: by
  rw [fst_eq]; rw [lintegral_map _ measurable_fst a hg]

中文:
定理 lintegral_fst
  条件: (κ : Kernel α (β × γ)) (a : α) {g : β -> 实数>=0∞} (hg : Measurable g)
  证明: by
  rw [fst_eq]; rw [lintegral_map _ measurable_fst a hg]

Depends on / 依赖: fst_eq, lintegral_map, measurable_fst
-/
theorem lintegral_fst (κ : Kernel α (β × γ)) (a : α) {g : β -> Real>=0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂fst κ a = ∫⁻ bc : β × γ, g bc.fst ∂κ a := by
  rw [fst_eq]; rw [lintegral_map _ measurable_fst a hg]

/--
Instance `IsMarkovKernel.fst` / 实例 `IsMarkovKernel.fst`

English:
instance IsMarkovKernel.fst
  signature: (κ : Kernel α (β × γ)) [IsMarkovKernel κ]
  body: by
  rw [Kernel.fst_eq]; exact IsMarkovKernel.map _ measurable_fst

中文:
实例 IsMarkovKernel.fst
  签名: (κ : Kernel α (β × γ)) [IsMarkovKernel κ]
  定义体: by
  rw [Kernel.fst_eq]; exact IsMarkovKernel.map _ measurable_fst

Depends on / 依赖: IsMarkovKernel, IsMarkovKernel.map, Kernel, Kernel.fst_eq, fst_eq, measurable_fst
-/
instance IsMarkovKernel.fst (κ : Kernel α (β × γ)) [IsMarkovKernel κ] : IsMarkovKernel (fst κ) := by
  rw [Kernel.fst_eq]; exact IsMarkovKernel.map _ measurable_fst

/--
Instance `IsZeroOrMarkovKernel.fst` / 实例 `IsZeroOrMarkovKernel.fst`

English:
instance IsZeroOrMarkovKernel.fst
  signature: (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ]
  body: by
  rw [Kernel.fst_eq]; infer_instance

中文:
实例 IsZeroOrMarkovKernel.fst
  签名: (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ]
  定义体: by
  rw [Kernel.fst_eq]; infer_instance

Depends on / 依赖: Kernel, Kernel.fst_eq, fst_eq, infer_instance
-/
instance IsZeroOrMarkovKernel.fst (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (fst κ) := by
  rw [Kernel.fst_eq]; infer_instance

/--
Instance `IsFiniteKernel.fst` / 实例 `IsFiniteKernel.fst`

English:
instance IsFiniteKernel.fst
  signature: (κ : Kernel α (β × γ)) [IsFiniteKernel κ]
  body: by
  rw [Kernel.fst_eq]; infer_instance

中文:
实例 IsFiniteKernel.fst
  签名: (κ : Kernel α (β × γ)) [IsFiniteKernel κ]
  定义体: by
  rw [Kernel.fst_eq]; infer_instance

Depends on / 依赖: Kernel, Kernel.fst_eq, fst_eq, infer_instance
-/
instance IsFiniteKernel.fst (κ : Kernel α (β × γ)) [IsFiniteKernel κ] : IsFiniteKernel (fst κ) := by
  rw [Kernel.fst_eq]; infer_instance

/--
Instance `IsSFiniteKernel.fst` / 实例 `IsSFiniteKernel.fst`

English:
instance IsSFiniteKernel.fst
  signature: (κ : Kernel α (β × γ)) [IsSFiniteKernel κ]
  body: by rw [Kernel.fst_eq]; infer_instance

中文:
实例 IsSFiniteKernel.fst
  签名: (κ : Kernel α (β × γ)) [IsSFiniteKernel κ]
  定义体: by rw [Kernel.fst_eq]; infer_instance

Depends on / 依赖: Kernel, Kernel.fst_eq, fst_eq, infer_instance
-/
instance IsSFiniteKernel.fst (κ : Kernel α (β × γ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (fst κ) := by rw [Kernel.fst_eq]; infer_instance

instance (priority := 100) isFiniteKernel_of_isFiniteKernel_fst {κ : Kernel α (β × γ)}
    [h : IsFiniteKernel (fst κ)] :
    IsFiniteKernel κ := by
  refine ⟨(fst κ).bound, (fst κ).bound_lt_top,
    fun a => le_trans ?_ (measure_le_bound (fst κ) a Set.univ)⟩
  rw [fst_apply' _ _ MeasurableSet.univ]
  simp

/--
lemma `fst_map_prod` / 引理 `fst_map_prod`

English:
lemma fst_map_prod
  given: (κ : Kernel α β) {f : β -> γ} {g : β -> δ} (hg : Measurable g)
  proof: by
  by_cases hf : Measurable f
  · ext x s hs
    rw [fst_apply' _ _ hs]; rw [map_apply' _ (hf.prod hg) _]; rw [map_apply' _ hf _ hs]
    · simp only [Set.preimage, Set.mem_ofPred]
    · exact measurable_fst hs
  · have : ¬ Measurable (fun x => (f x, g x)) := by
      contrapose hf; exact hf.fst
  

中文:
引理 fst_map_prod
  条件: (κ : Kernel α β) {f : β -> γ} {g : β -> δ} (hg : Measurable g)
  证明: by
  by_cases hf : Measurable f
  · ext x s hs
    rw [fst_apply' _ _ hs]; rw [map_apply' _ (hf.prod hg) _]; rw [map_apply' _ hf _ hs]
    · simp only [Set.preimage, Set.mem_ofPred]
    · exact measurable_fst hs
  · have : ¬ Measurable (fun x => (f x, g x)) := by
      contrapose hf; exact hf.fst
  

Depends on / 依赖: Measurable, Set.mem_ofPred, Set.preimage, contrapose, fst_apply, hf.fst, hf.prod, map_apply, map_of_not_measurable, measurable_fst, mem_ofPred, preimage
-/
lemma fst_map_prod (κ : Kernel α β) {f : β -> γ} {g : β -> δ} (hg : Measurable g) :
    fst (map κ (fun x => (f x, g x))) = map κ f := by
  by_cases hf : Measurable f
  · ext x s hs
    rw [fst_apply' _ _ hs]; rw [map_apply' _ (hf.prod hg) _]; rw [map_apply' _ hf _ hs]
    · simp only [Set.preimage, Set.mem_ofPred]
    · exact measurable_fst hs
  · have : ¬ Measurable (fun x => (f x, g x)) := by
      contrapose hf; exact hf.fst
    simp [map_of_not_measurable _ hf, map_of_not_measurable _ this]

/--
lemma `fst_map_id_prod` / 引理 `fst_map_id_prod`

English:
lemma fst_map_id_prod
  given: (κ : Kernel α β) {f : β -> γ} (hf : Measurable f)
  proof: by
  rw [fst_map_prod _ hf]; rw [Kernel.map_id']

中文:
引理 fst_map_id_prod
  条件: (κ : Kernel α β) {f : β -> γ} (hf : Measurable f)
  证明: by
  rw [fst_map_prod _ hf]; rw [Kernel.map_id']

Depends on / 依赖: Kernel, Kernel.map_id, fst_map_prod, map_id
-/
lemma fst_map_id_prod (κ : Kernel α β) {f : β -> γ} (hf : Measurable f) :
    fst (map κ (fun a => (a, f a))) = κ := by
  rw [fst_map_prod _ hf]; rw [Kernel.map_id']

/--
lemma `fst_prodMkLeft` / 引理 `fst_prodMkLeft`

English:
lemma fst_prodMkLeft
  given: (δ : Type*) [MeasurableSpace δ] (κ : Kernel α (β × γ))
  proof: rfl

中文:
引理 fst_prodMkLeft
  条件: (δ : 类型) [MeasurableSpace δ] (κ : Kernel α (β × γ))
  证明: rfl
-/
lemma fst_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : Kernel α (β × γ)) :
    fst (prodMkLeft δ κ) = prodMkLeft δ (fst κ) := rfl

/--
lemma `fst_prodMkRight` / 引理 `fst_prodMkRight`

English:
lemma fst_prodMkRight
  given: (κ : Kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ]
  proof: rfl

中文:
引理 fst_prodMkRight
  条件: (κ : Kernel α (β × γ)) (δ : 类型) [MeasurableSpace δ]
  证明: rfl
-/
lemma fst_prodMkRight (κ : Kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] :
    fst (prodMkRight δ κ) = prodMkRight δ (fst κ) := rfl

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: (κ : Kernel α (β × γ))
  body: mapOfMeasurable κ Prod.snd measurable_snd

中文:
定义 snd
  签名: (κ : Kernel α (β × γ))
  定义体: mapOfMeasurable κ Prod.snd measurable_snd

Depends on / 依赖: Prod.snd, mapOfMeasurable, measurable_snd
-/
noncomputable def snd (κ : Kernel α (β × γ)) : Kernel α γ :=
  mapOfMeasurable κ Prod.snd measurable_snd

/--
theorem `snd_eq` / 定理 `snd_eq`

English:
theorem snd_eq
  given: (κ : Kernel α (β × γ))
  statement: snd κ = map κ Prod.snd
  proof: by simp [snd]

中文:
定理 snd_eq
  条件: (κ : Kernel α (β × γ))
  结论: snd κ = map κ Prod.snd
  证明: by simp [snd]
-/
theorem snd_eq (κ : Kernel α (β × γ)) : snd κ = map κ Prod.snd := by simp [snd]

/--
theorem `snd_apply` / 定理 `snd_apply`

English:
theorem snd_apply
  given: (κ : Kernel α (β × γ)) (a : α)
  statement: snd κ a = (κ a).map Prod.snd
  proof: rfl

中文:
定理 snd_apply
  条件: (κ : Kernel α (β × γ)) (a : α)
  结论: snd κ a = (κ a).map Prod.snd
  证明: rfl
-/
theorem snd_apply (κ : Kernel α (β × γ)) (a : α) : snd κ a = (κ a).map Prod.snd :=
  rfl

/--
theorem `snd_apply'` / 定理 `snd_apply'`

English:
theorem snd_apply'
  given: (κ : Kernel α (β × γ)) (a : α) {s : Set γ} (hs : MeasurableSet s)
  proof: by rw [snd_apply, Measure.map_apply measurable_snd hs]

@[simp]

中文:
定理 snd_apply'
  条件: (κ : Kernel α (β × γ)) (a : α) {s : Set γ} (hs : MeasurableSet s)
  证明: by rw [snd_apply, Measure.map_apply measurable_snd hs]

@[simp]

Depends on / 依赖: Measure, Measure.map_apply, map_apply, measurable_snd, snd_apply
-/
theorem snd_apply' (κ : Kernel α (β × γ)) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    snd κ a s = κ a (Prod.snd ⁻¹' s) := by rw [snd_apply, Measure.map_apply measurable_snd hs]

@[simp]
/--
lemma `snd_zero` / 引理 `snd_zero`

English:
lemma snd_zero
  statement: snd (0 : Kernel α (β × γ)) = 0
  proof: by simp [snd]

中文:
引理 snd_zero
  结论: snd (0 : Kernel α (β × γ)) = 0
  证明: by simp [snd]
-/
lemma snd_zero : snd (0 : Kernel α (β × γ)) = 0 := by simp [snd]

/--
theorem `lintegral_snd` / 定理 `lintegral_snd`

English:
theorem lintegral_snd
  given: (κ : Kernel α (β × γ)) (a : α) {g : γ -> Real>=0∞} (hg : Measurable g)
  proof: by
  rw [snd_eq]; rw [lintegral_map _ measurable_snd a hg]

中文:
定理 lintegral_snd
  条件: (κ : Kernel α (β × γ)) (a : α) {g : γ -> 实数>=0∞} (hg : Measurable g)
  证明: by
  rw [snd_eq]; rw [lintegral_map _ measurable_snd a hg]

Depends on / 依赖: lintegral_map, measurable_snd, snd_eq
-/
theorem lintegral_snd (κ : Kernel α (β × γ)) (a : α) {g : γ -> Real>=0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂snd κ a = ∫⁻ bc : β × γ, g bc.snd ∂κ a := by
  rw [snd_eq]; rw [lintegral_map _ measurable_snd a hg]

/--
Instance `IsMarkovKernel.snd` / 实例 `IsMarkovKernel.snd`

English:
instance IsMarkovKernel.snd
  signature: (κ : Kernel α (β × γ)) [IsMarkovKernel κ]
  body: by
  rw [Kernel.snd_eq]; exact IsMarkovKernel.map _ measurable_snd

中文:
实例 IsMarkovKernel.snd
  签名: (κ : Kernel α (β × γ)) [IsMarkovKernel κ]
  定义体: by
  rw [Kernel.snd_eq]; exact IsMarkovKernel.map _ measurable_snd

Depends on / 依赖: IsMarkovKernel, IsMarkovKernel.map, Kernel, Kernel.snd_eq, measurable_snd, snd_eq
-/
instance IsMarkovKernel.snd (κ : Kernel α (β × γ)) [IsMarkovKernel κ] : IsMarkovKernel (snd κ) := by
  rw [Kernel.snd_eq]; exact IsMarkovKernel.map _ measurable_snd

/--
Instance `IsZeroOrMarkovKernel.snd` / 实例 `IsZeroOrMarkovKernel.snd`

English:
instance IsZeroOrMarkovKernel.snd
  signature: (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ]
  body: by
  rw [Kernel.snd_eq]; infer_instance

中文:
实例 IsZeroOrMarkovKernel.snd
  签名: (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ]
  定义体: by
  rw [Kernel.snd_eq]; infer_instance

Depends on / 依赖: Kernel, Kernel.snd_eq, infer_instance, snd_eq
-/
instance IsZeroOrMarkovKernel.snd (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (snd κ) := by
  rw [Kernel.snd_eq]; infer_instance

/--
Instance `IsFiniteKernel.snd` / 实例 `IsFiniteKernel.snd`

English:
instance IsFiniteKernel.snd
  signature: (κ : Kernel α (β × γ)) [IsFiniteKernel κ]
  body: by
  rw [Kernel.snd_eq]; infer_instance

中文:
实例 IsFiniteKernel.snd
  签名: (κ : Kernel α (β × γ)) [IsFiniteKernel κ]
  定义体: by
  rw [Kernel.snd_eq]; infer_instance

Depends on / 依赖: Kernel, Kernel.snd_eq, infer_instance, snd_eq
-/
instance IsFiniteKernel.snd (κ : Kernel α (β × γ)) [IsFiniteKernel κ] : IsFiniteKernel (snd κ) := by
  rw [Kernel.snd_eq]; infer_instance

/--
Instance `IsSFiniteKernel.snd` / 实例 `IsSFiniteKernel.snd`

English:
instance IsSFiniteKernel.snd
  signature: (κ : Kernel α (β × γ)) [IsSFiniteKernel κ]
  body: by rw [Kernel.snd_eq]; infer_instance

中文:
实例 IsSFiniteKernel.snd
  签名: (κ : Kernel α (β × γ)) [IsSFiniteKernel κ]
  定义体: by rw [Kernel.snd_eq]; infer_instance

Depends on / 依赖: Kernel, Kernel.snd_eq, infer_instance, snd_eq
-/
instance IsSFiniteKernel.snd (κ : Kernel α (β × γ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (snd κ) := by rw [Kernel.snd_eq]; infer_instance

instance (priority := 100) isFiniteKernel_of_isFiniteKernel_snd {κ : Kernel α (β × γ)}
    [h : IsFiniteKernel (snd κ)] :
    IsFiniteKernel κ := by
  refine ⟨(snd κ).bound, (snd κ).bound_lt_top,
    fun a => le_trans ?_ (measure_le_bound (snd κ) a Set.univ)⟩
  rw [snd_apply' _ _ MeasurableSet.univ]
  simp

/--
lemma `snd_map_prod` / 引理 `snd_map_prod`

English:
lemma snd_map_prod
  given: (κ : Kernel α β) {f : β -> γ} {g : β -> δ} (hf : Measurable f)
  proof: by
  by_cases hg : Measurable g
  · ext x s hs
    rw [snd_apply' _ _ hs]; rw [map_apply' _ (hf.prod hg)]; rw [map_apply' _ hg _ hs]
    · simp only [Set.preimage, Set.mem_ofPred]
    · exact measurable_snd hs
  · have : ¬ Measurable (fun x => (f x, g x)) := by
      contrapose hg; exact hg.snd
    

中文:
引理 snd_map_prod
  条件: (κ : Kernel α β) {f : β -> γ} {g : β -> δ} (hf : Measurable f)
  证明: by
  by_cases hg : Measurable g
  · ext x s hs
    rw [snd_apply' _ _ hs]; rw [map_apply' _ (hf.prod hg)]; rw [map_apply' _ hg _ hs]
    · simp only [Set.preimage, Set.mem_ofPred]
    · exact measurable_snd hs
  · have : ¬ Measurable (fun x => (f x, g x)) := by
      contrapose hg; exact hg.snd
    

Depends on / 依赖: Measurable, Set.mem_ofPred, Set.preimage, contrapose, hf.prod, hg.snd, map_apply, map_of_not_measurable, measurable_snd, mem_ofPred, preimage, snd_apply
-/
lemma snd_map_prod (κ : Kernel α β) {f : β -> γ} {g : β -> δ} (hf : Measurable f) :
    snd (map κ (fun x => (f x, g x))) = map κ g := by
  by_cases hg : Measurable g
  · ext x s hs
    rw [snd_apply' _ _ hs]; rw [map_apply' _ (hf.prod hg)]; rw [map_apply' _ hg _ hs]
    · simp only [Set.preimage, Set.mem_ofPred]
    · exact measurable_snd hs
  · have : ¬ Measurable (fun x => (f x, g x)) := by
      contrapose hg; exact hg.snd
    simp [map_of_not_measurable _ hg, map_of_not_measurable _ this]

/--
lemma `snd_map_prod_id` / 引理 `snd_map_prod_id`

English:
lemma snd_map_prod_id
  given: (κ : Kernel α β) {f : β -> γ} (hf : Measurable f)
  proof: by
  rw [snd_map_prod _ hf]; rw [Kernel.map_id']

中文:
引理 snd_map_prod_id
  条件: (κ : Kernel α β) {f : β -> γ} (hf : Measurable f)
  证明: by
  rw [snd_map_prod _ hf]; rw [Kernel.map_id']

Depends on / 依赖: Kernel, Kernel.map_id, map_id, snd_map_prod
-/
lemma snd_map_prod_id (κ : Kernel α β) {f : β -> γ} (hf : Measurable f) :
    snd (map κ (fun a => (f a, a))) = κ := by
  rw [snd_map_prod _ hf]; rw [Kernel.map_id']

/--
lemma `snd_prodMkLeft` / 引理 `snd_prodMkLeft`

English:
lemma snd_prodMkLeft
  given: (δ : Type*) [MeasurableSpace δ] (κ : Kernel α (β × γ))
  proof: rfl

中文:
引理 snd_prodMkLeft
  条件: (δ : 类型) [MeasurableSpace δ] (κ : Kernel α (β × γ))
  证明: rfl
-/
lemma snd_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : Kernel α (β × γ)) :
    snd (prodMkLeft δ κ) = prodMkLeft δ (snd κ) := rfl

/--
lemma `snd_prodMkRight` / 引理 `snd_prodMkRight`

English:
lemma snd_prodMkRight
  given: (κ : Kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ]
  proof: rfl

@[simp]

中文:
引理 snd_prodMkRight
  条件: (κ : Kernel α (β × γ)) (δ : 类型) [MeasurableSpace δ]
  证明: rfl

@[simp]
-/
lemma snd_prodMkRight (κ : Kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] :
    snd (prodMkRight δ κ) = prodMkRight δ (snd κ) := rfl

@[simp]
/--
lemma `fst_swapRight` / 引理 `fst_swapRight`

English:
lemma fst_swapRight
  given: (κ : Kernel α (β × γ))
  statement: fst (swapRight κ) = snd κ
  proof: by
  ext a s hs
  rw [fst_apply' _ _ hs]; rw [swapRight_apply']; rw [snd_apply' _ _ hs]
  · rfl
  · exact measurable_fst hs

@[simp]

中文:
引理 fst_swapRight
  条件: (κ : Kernel α (β × γ))
  结论: fst (swapRight κ) = snd κ
  证明: by
  ext a s hs
  rw [fst_apply' _ _ hs]; rw [swapRight_apply']; rw [snd_apply' _ _ hs]
  · rfl
  · exact measurable_fst hs

@[simp]

Depends on / 依赖: fst_apply, measurable_fst, snd_apply, swapRight_apply
-/
lemma fst_swapRight (κ : Kernel α (β × γ)) : fst (swapRight κ) = snd κ := by
  ext a s hs
  rw [fst_apply' _ _ hs]; rw [swapRight_apply']; rw [snd_apply' _ _ hs]
  · rfl
  · exact measurable_fst hs

@[simp]
/--
lemma `snd_swapRight` / 引理 `snd_swapRight`

English:
lemma snd_swapRight
  given: (κ : Kernel α (β × γ))
  statement: snd (swapRight κ) = fst κ
  proof: by
  ext a s hs
  rw [snd_apply' _ _ hs]; rw [swapRight_apply']; rw [fst_apply' _ _ hs]
  · rfl
  · exact measurable_snd hs

中文:
引理 snd_swapRight
  条件: (κ : Kernel α (β × γ))
  结论: snd (swapRight κ) = fst κ
  证明: by
  ext a s hs
  rw [snd_apply' _ _ hs]; rw [swapRight_apply']; rw [fst_apply' _ _ hs]
  · rfl
  · exact measurable_snd hs

Depends on / 依赖: fst_apply, measurable_snd, snd_apply, swapRight_apply
-/
lemma snd_swapRight (κ : Kernel α (β × γ)) : snd (swapRight κ) = fst κ := by
  ext a s hs
  rw [snd_apply' _ _ hs]; rw [swapRight_apply']; rw [fst_apply' _ _ hs]
  · rfl
  · exact measurable_snd hs

end FstSnd

section sectLsectR

variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

/--
Definition of `sectL` / `sectL` 的定义

English:
definition sectL
  signature: (κ : Kernel (α × β) γ) (b : β)
  body: comap κ (fun a => (a, b)) (measurable_id.prodMk measurable_const)

中文:
定义 sectL
  签名: (κ : Kernel (α × β) γ) (b : β)
  定义体: comap κ (fun a => (a, b)) (measurable_id.prodMk measurable_const)

Depends on / 依赖: measurable_const, measurable_id, measurable_id.prodMk, prodMk
-/
noncomputable def sectL (κ : Kernel (α × β) γ) (b : β) : Kernel α γ :=
  comap κ (fun a => (a, b)) (measurable_id.prodMk measurable_const)

/--
theorem `sectL_apply` / 定理 `sectL_apply`

English:
theorem sectL_apply
  given: (κ : Kernel (α × β) γ) (b : β) (a : α)
  statement: sectL κ b a = κ (a, b)
  proof: rfl

中文:
定理 sectL_apply
  条件: (κ : Kernel (α × β) γ) (b : β) (a : α)
  结论: sectL κ b a = κ (a, b)
  证明: rfl
-/
@[simp] theorem sectL_apply (κ : Kernel (α × β) γ) (b : β) (a : α) : sectL κ b a = κ (a, b) := rfl

/--
lemma `sectL_zero` / 引理 `sectL_zero`

English:
lemma sectL_zero
  given: (b : β)
  statement: sectL (0 : Kernel (α × β) γ) b = 0
  proof: by simp [sectL]

中文:
引理 sectL_zero
  条件: (b : β)
  结论: sectL (0 : Kernel (α × β) γ) b = 0
  证明: by simp [sectL]
-/
@[simp] lemma sectL_zero (b : β) : sectL (0 : Kernel (α × β) γ) b = 0 := by simp [sectL]

instance (κ : Kernel (α × β) γ) (b : β) [IsMarkovKernel κ] : IsMarkovKernel (sectL κ b) := by
  rw [sectL]; infer_instance

instance (κ : Kernel (α × β) γ) (b : β) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (sectL κ b) := by
  rw [sectL]; infer_instance

instance (κ : Kernel (α × β) γ) (b : β) [IsFiniteKernel κ] : IsFiniteKernel (sectL κ b) := by
  rw [sectL]; infer_instance

instance (κ : Kernel (α × β) γ) (b : β) [IsSFiniteKernel κ] : IsSFiniteKernel (sectL κ b) := by
  rw [sectL]; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) (b : β) [NeZero (κ (a, b))] : NeZero ((sectL κ b) a) := by
  rw [sectL_apply]; infer_instance

instance (priority := 100) {κ : Kernel (α × β) γ} [forall b, IsMarkovKernel (sectL κ b)] :
    IsMarkovKernel κ := by
  refine ⟨fun _ => ⟨?_⟩⟩
  rw [← sectL_apply]; rw [measure_univ]

--I'm not sure this lemma is actually useful
/--
lemma `comap_sectL` / 引理 `comap_sectL`

English:
lemma comap_sectL
  given: (κ : Kernel (α × β) γ) (b : β) {f : δ -> α} (hf : Measurable f)
  proof: by
  ext d s
  rw [comap_apply]; rw [sectL_apply]; rw [comap_apply]

@[simp]

中文:
引理 comap_sectL
  条件: (κ : Kernel (α × β) γ) (b : β) {f : δ -> α} (hf : Measurable f)
  证明: by
  ext d s
  rw [comap_apply]; rw [sectL_apply]; rw [comap_apply]

@[simp]

Depends on / 依赖: comap_apply, sectL_apply
-/
lemma comap_sectL (κ : Kernel (α × β) γ) (b : β) {f : δ -> α} (hf : Measurable f) :
    comap (sectL κ b) f hf = comap κ (fun d => (f d, b)) (hf.prodMk measurable_const) := by
  ext d s
  rw [comap_apply]; rw [sectL_apply]; rw [comap_apply]

@[simp]
/--
lemma `sectL_prodMkLeft` / 引理 `sectL_prodMkLeft`

English:
lemma sectL_prodMkLeft
  given: (α : Type*) [MeasurableSpace α] (κ : Kernel β γ) (a : α) {b : β}
  proof: rfl

@[simp]

中文:
引理 sectL_prodMkLeft
  条件: (α : 类型) [MeasurableSpace α] (κ : Kernel β γ) (a : α) {b : β}
  证明: rfl

@[simp]
-/
lemma sectL_prodMkLeft (α : Type*) [MeasurableSpace α] (κ : Kernel β γ) (a : α) {b : β} :
    sectL (prodMkLeft α κ) b a = κ b := rfl

@[simp]
/--
lemma `sectL_prodMkRight` / 引理 `sectL_prodMkRight`

English:
lemma sectL_prodMkRight
  given: (β : Type*) [MeasurableSpace β] (κ : Kernel α γ) (b : β)
  proof: rfl

中文:
引理 sectL_prodMkRight
  条件: (β : 类型) [MeasurableSpace β] (κ : Kernel α γ) (b : β)
  证明: rfl
-/
lemma sectL_prodMkRight (β : Type*) [MeasurableSpace β] (κ : Kernel α γ) (b : β) :
    sectL (prodMkRight β κ) b = κ := rfl

/--
Definition of `sectR` / `sectR` 的定义

English:
definition sectR
  signature: (κ : Kernel (α × β) γ) (a : α)
  body: comap κ (fun b => (a, b)) (measurable_const.prodMk measurable_id)

中文:
定义 sectR
  签名: (κ : Kernel (α × β) γ) (a : α)
  定义体: comap κ (fun b => (a, b)) (measurable_const.prodMk measurable_id)

Depends on / 依赖: measurable_const, measurable_const.prodMk, measurable_id, prodMk
-/
noncomputable def sectR (κ : Kernel (α × β) γ) (a : α) : Kernel β γ :=
  comap κ (fun b => (a, b)) (measurable_const.prodMk measurable_id)

/--
theorem `sectR_apply` / 定理 `sectR_apply`

English:
theorem sectR_apply
  given: (κ : Kernel (α × β) γ) (b : β) (a : α)
  statement: sectR κ a b = κ (a, b)
  proof: rfl

中文:
定理 sectR_apply
  条件: (κ : Kernel (α × β) γ) (b : β) (a : α)
  结论: sectR κ a b = κ (a, b)
  证明: rfl
-/
@[simp] theorem sectR_apply (κ : Kernel (α × β) γ) (b : β) (a : α) : sectR κ a b = κ (a, b) := rfl

/--
lemma `sectR_zero` / 引理 `sectR_zero`

English:
lemma sectR_zero
  given: (a : α)
  statement: sectR (0 : Kernel (α × β) γ) a = 0
  proof: by simp [sectR]

中文:
引理 sectR_zero
  条件: (a : α)
  结论: sectR (0 : Kernel (α × β) γ) a = 0
  证明: by simp [sectR]
-/
@[simp] lemma sectR_zero (a : α) : sectR (0 : Kernel (α × β) γ) a = 0 := by simp [sectR]

instance (κ : Kernel (α × β) γ) (a : α) [IsMarkovKernel κ] : IsMarkovKernel (sectR κ a) := by
  rw [sectR]; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (sectR κ a) := by
  rw [sectR]; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) [IsFiniteKernel κ] : IsFiniteKernel (sectR κ a) := by
  rw [sectR]; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) [IsSFiniteKernel κ] : IsSFiniteKernel (sectR κ a) := by
  rw [sectR]; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) (b : β) [NeZero (κ (a, b))] : NeZero ((sectR κ a) b) := by
  rw [sectR_apply]; infer_instance

instance (priority := 100) {κ : Kernel (α × β) γ} [forall b, IsMarkovKernel (sectR κ b)] :
    IsMarkovKernel κ := by
  refine ⟨fun _ => ⟨?_⟩⟩
  rw [← sectR_apply]; rw [measure_univ]

--I'm not sure this lemma is actually useful
/--
lemma `comap_sectR` / 引理 `comap_sectR`

English:
lemma comap_sectR
  given: (κ : Kernel (α × β) γ) (a : α) {f : δ -> β} (hf : Measurable f)
  proof: by
  ext d s
  rw [comap_apply]; rw [sectR_apply]; rw [comap_apply]

@[simp]

中文:
引理 comap_sectR
  条件: (κ : Kernel (α × β) γ) (a : α) {f : δ -> β} (hf : Measurable f)
  证明: by
  ext d s
  rw [comap_apply]; rw [sectR_apply]; rw [comap_apply]

@[simp]

Depends on / 依赖: comap_apply, sectR_apply
-/
lemma comap_sectR (κ : Kernel (α × β) γ) (a : α) {f : δ -> β} (hf : Measurable f) :
    comap (sectR κ a) f hf = comap κ (fun d => (a, f d)) (measurable_const.prodMk hf) := by
  ext d s
  rw [comap_apply]; rw [sectR_apply]; rw [comap_apply]

@[simp]
/--
lemma `sectR_prodMkLeft` / 引理 `sectR_prodMkLeft`

English:
lemma sectR_prodMkLeft
  given: (α : Type*) [MeasurableSpace α] (κ : Kernel β γ) (a : α)
  proof: rfl

@[simp]

中文:
引理 sectR_prodMkLeft
  条件: (α : 类型) [MeasurableSpace α] (κ : Kernel β γ) (a : α)
  证明: rfl

@[simp]
-/
lemma sectR_prodMkLeft (α : Type*) [MeasurableSpace α] (κ : Kernel β γ) (a : α) :
    sectR (prodMkLeft α κ) a = κ := rfl

@[simp]
/--
lemma `sectR_prodMkRight` / 引理 `sectR_prodMkRight`

English:
lemma sectR_prodMkRight
  given: (β : Type*) [MeasurableSpace β] (κ : Kernel α γ) (b : β) {a : α}
  proof: rfl

中文:
引理 sectR_prodMkRight
  条件: (β : 类型) [MeasurableSpace β] (κ : Kernel α γ) (b : β) {a : α}
  证明: rfl
-/
lemma sectR_prodMkRight (β : Type*) [MeasurableSpace β] (κ : Kernel α γ) (b : β) {a : α} :
    sectR (prodMkRight β κ) a b = κ a := rfl

/--
lemma `sectL_swapRight` / 引理 `sectL_swapRight`

English:
lemma sectL_swapRight
  given: (κ : Kernel (α × β) γ)
  statement: sectL (swapLeft κ) = sectR κ
  proof: rfl

中文:
引理 sectL_swapRight
  条件: (κ : Kernel (α × β) γ)
  结论: sectL (swapLeft κ) = sectR κ
  证明: rfl
-/
@[simp] lemma sectL_swapRight (κ : Kernel (α × β) γ) : sectL (swapLeft κ) = sectR κ := rfl

/--
lemma `sectR_swapRight` / 引理 `sectR_swapRight`

English:
lemma sectR_swapRight
  given: (κ : Kernel (α × β) γ)
  statement: sectR (swapLeft κ) = sectL κ
  proof: rfl

中文:
引理 sectR_swapRight
  条件: (κ : Kernel (α × β) γ)
  结论: sectR (swapLeft κ) = sectL κ
  证明: rfl
-/
@[simp] lemma sectR_swapRight (κ : Kernel (α × β) γ) : sectR (swapLeft κ) = sectL κ := rfl

end sectLsectR

/--
lemma `isSFiniteKernel_prodMkLeft_iff` / 引理 `isSFiniteKernel_prodMkLeft_iff`

English:
lemma isSFiniteKernel_prodMkLeft_iff
  given: [Nonempty γ] {κ : Kernel α β}
  proof: by
  inhabit γ
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [← sectR_prodMkLeft γ κ default]
  infer_instance

中文:
引理 isSFiniteKernel_prodMkLeft_iff
  条件: [Nonempty γ] {κ : Kernel α β}
  证明: by
  inhabit γ
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [← sectR_prodMkLeft γ κ default]
  infer_instance

Depends on / 依赖: infer_instance, inhabit, sectR_prodMkLeft
-/
lemma isSFiniteKernel_prodMkLeft_iff [Nonempty γ] {κ : Kernel α β} :
    IsSFiniteKernel (prodMkLeft γ κ) ↔ IsSFiniteKernel κ := by
  inhabit γ
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [← sectR_prodMkLeft γ κ default]
  infer_instance

/--
lemma `isSFiniteKernel_prodMkRight_iff` / 引理 `isSFiniteKernel_prodMkRight_iff`

English:
lemma isSFiniteKernel_prodMkRight_iff
  given: [Nonempty γ] {κ : Kernel α β}
  proof: by
  inhabit γ
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [← sectL_prodMkRight γ κ default]
  infer_instance

中文:
引理 isSFiniteKernel_prodMkRight_iff
  条件: [Nonempty γ] {κ : Kernel α β}
  证明: by
  inhabit γ
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [← sectL_prodMkRight γ κ default]
  infer_instance

Depends on / 依赖: infer_instance, inhabit, sectL_prodMkRight
-/
lemma isSFiniteKernel_prodMkRight_iff [Nonempty γ] {κ : Kernel α β} :
    IsSFiniteKernel (prodMkRight γ κ) ↔ IsSFiniteKernel κ := by
  inhabit γ
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [← sectL_prodMkRight γ κ default]
  infer_instance

end Kernel
end ProbabilityTheory
