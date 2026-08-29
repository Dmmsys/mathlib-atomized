/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Bochner Integration on Groups

We develop properties of integrals with a group as domain.
This file contains properties about integrability and Bochner integration.
-/

public section

namespace MeasureTheory

open Measure TopologicalSpace

open scoped ENNReal

variable {𝕜 M α G E F : Type*} [MeasurableSpace G]
variable [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup F]
variable {μ : Measure G} {f : G -> E} {g : G}

section MeasurableInv

variable [Group G] [MeasurableInv G]

@[to_additive]
/--
theorem `Integrable.comp_inv` / 定理 `Integrable.comp_inv`

English:
theorem Integrable.comp_inv
  given: [IsInvInvariant μ] {f : G -> F} (hf : Integrable f μ)
  proof: (hf.mono_measure (map_inv_eq_self μ).le).comp_measurable measurable_inv

@[to_additive]

中文:
定理 Integrable.comp_inv
  条件: [IsInvInvariant μ] {f : G -> F} (hf : 整数egrable f μ)
  证明: (hf.mono_measure (map_inv_eq_self μ).le).comp_measurable measurable_inv

@[to_additive]

Depends on / 依赖: comp_measurable, hf.mono_measure, map_inv_eq_self, measurable_inv, mono_measure
-/
theorem Integrable.comp_inv [IsInvInvariant μ] {f : G -> F} (hf : Integrable f μ) :
    Integrable (fun t => f t⁻¹) μ :=
  (hf.mono_measure (map_inv_eq_self μ).le).comp_measurable measurable_inv

@[to_additive]
/--
theorem `integral_inv_eq_self` / 定理 `integral_inv_eq_self`

English:
theorem integral_inv_eq_self
  given: (f : G -> E) (μ : Measure G) [IsInvInvariant μ]
  proof: by
  have h : MeasurableEmbedding fun x : G => x⁻¹ := (MeasurableEquiv.inv G).measurableEmbedding
  rw [← h.integral_map]; rw [map_inv_eq_self]

@[to_additive]

中文:
定理 integral_inv_eq_self
  条件: (f : G -> E) (μ : Measure G) [IsInvInvariant μ]
  证明: by
  have h : MeasurableEmbedding fun x : G => x⁻¹ := (MeasurableEquiv.inv G).measurableEmbedding
  rw [← h.integral_map]; rw [map_inv_eq_self]

@[to_additive]

Depends on / 依赖: MeasurableEmbedding, MeasurableEquiv, MeasurableEquiv.inv, h.integral_map, integral_map, map_inv_eq_self, measurableEmbedding
-/
theorem integral_inv_eq_self (f : G -> E) (μ : Measure G) [IsInvInvariant μ] :
    ∫ x, f x⁻¹ ∂μ = ∫ x, f x ∂μ := by
  have h : MeasurableEmbedding fun x : G => x⁻¹ := (MeasurableEquiv.inv G).measurableEmbedding
  rw [← h.integral_map]; rw [map_inv_eq_self]

@[to_additive]
/--
theorem `IntegrableOn.comp_inv` / 定理 `IntegrableOn.comp_inv`

English:
theorem IntegrableOn.comp_inv
  given: [IsInvInvariant μ] {f : G -> F} {s : Set G} (hf : IntegrableOn f s μ)
  proof: by
  apply (integrable_map_equiv (MeasurableEquiv.inv G) f).mp
  have : s⁻¹ = MeasurableEquiv.inv G ⁻¹' s := by simp
  rw [this]; rw [← MeasurableEquiv.restrict_map]
  simpa using! hf

中文:
定理 IntegrableOn.comp_inv
  条件: [IsInvInvariant μ] {f : G -> F} {s : Set G} (hf : 整数egrableOn f s μ)
  证明: by
  apply (integrable_map_equiv (MeasurableEquiv.inv G) f).mp
  have : s⁻¹ = MeasurableEquiv.inv G ⁻¹' s := by simp
  rw [this]; rw [← MeasurableEquiv.restrict_map]
  simpa using! hf

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.inv, MeasurableEquiv.restrict_map, integrable_map_equiv, restrict_map
-/
theorem IntegrableOn.comp_inv [IsInvInvariant μ] {f : G -> F} {s : Set G} (hf : IntegrableOn f s μ) :
    IntegrableOn (fun x => f x⁻¹) s⁻¹ μ := by
  apply (integrable_map_equiv (MeasurableEquiv.inv G) f).mp
  have : s⁻¹ = MeasurableEquiv.inv G ⁻¹' s := by simp
  rw [this]; rw [← MeasurableEquiv.restrict_map]
  simpa using! hf

end MeasurableInv

section MeasurableInvOrder

variable [PartialOrder G] [CommGroup G] [IsOrderedMonoid G] [MeasurableInv G]
variable [IsInvInvariant μ]

@[to_additive]
/--
theorem `IntegrableOn.comp_inv_Iic` / 定理 `IntegrableOn.comp_inv_Iic`

English:
theorem IntegrableOn.comp_inv_Iic
  given: {c : G} {f : G -> F} (hf : IntegrableOn f (Set.Ici c⁻¹) μ)
  proof: by
  simpa using hf.comp_inv

@[to_additive]

中文:
定理 IntegrableOn.comp_inv_Iic
  条件: {c : G} {f : G -> F} (hf : 整数egrableOn f (Set.Ici c⁻¹) μ)
  证明: by
  simpa using hf.comp_inv

@[to_additive]

Depends on / 依赖: comp_inv, hf.comp_inv
-/
theorem IntegrableOn.comp_inv_Iic {c : G} {f : G -> F} (hf : IntegrableOn f (Set.Ici c⁻¹) μ) :
    IntegrableOn (fun x => f x⁻¹) (Set.Iic c) μ := by
  simpa using hf.comp_inv

@[to_additive]
/--
theorem `IntegrableOn.comp_inv_Ici` / 定理 `IntegrableOn.comp_inv_Ici`

English:
theorem IntegrableOn.comp_inv_Ici
  given: {c : G} {f : G -> F} (hf : IntegrableOn f (Set.Iic c⁻¹) μ)
  proof: by
  simpa using hf.comp_inv

@[to_additive]

中文:
定理 IntegrableOn.comp_inv_Ici
  条件: {c : G} {f : G -> F} (hf : 整数egrableOn f (Set.Iic c⁻¹) μ)
  证明: by
  simpa using hf.comp_inv

@[to_additive]

Depends on / 依赖: comp_inv, hf.comp_inv
-/
theorem IntegrableOn.comp_inv_Ici {c : G} {f : G -> F} (hf : IntegrableOn f (Set.Iic c⁻¹) μ) :
    IntegrableOn (fun x => f x⁻¹) (Set.Ici c) μ := by
  simpa using hf.comp_inv

@[to_additive]
/--
theorem `IntegrableOn.comp_inv_Iio` / 定理 `IntegrableOn.comp_inv_Iio`

English:
theorem IntegrableOn.comp_inv_Iio
  given: {c : G} {f : G -> F} (hf : IntegrableOn f (Set.Ioi c⁻¹) μ)
  proof: by
  simpa using hf.comp_inv

@[to_additive]

中文:
定理 IntegrableOn.comp_inv_Iio
  条件: {c : G} {f : G -> F} (hf : 整数egrableOn f (Set.Ioi c⁻¹) μ)
  证明: by
  simpa using hf.comp_inv

@[to_additive]

Depends on / 依赖: comp_inv, hf.comp_inv
-/
theorem IntegrableOn.comp_inv_Iio {c : G} {f : G -> F} (hf : IntegrableOn f (Set.Ioi c⁻¹) μ) :
    IntegrableOn (fun x => f x⁻¹) (Set.Iio c) μ := by
  simpa using hf.comp_inv

@[to_additive]
/--
theorem `IntegrableOn.comp_inv_Ioi` / 定理 `IntegrableOn.comp_inv_Ioi`

English:
theorem IntegrableOn.comp_inv_Ioi
  given: {c : G} {f : G -> F} (hf : IntegrableOn f (Set.Iio c⁻¹) μ)
  proof: by
  simpa using hf.comp_inv

中文:
定理 IntegrableOn.comp_inv_Ioi
  条件: {c : G} {f : G -> F} (hf : 整数egrableOn f (Set.Iio c⁻¹) μ)
  证明: by
  simpa using hf.comp_inv

Depends on / 依赖: comp_inv, hf.comp_inv
-/
theorem IntegrableOn.comp_inv_Ioi {c : G} {f : G -> F} (hf : IntegrableOn f (Set.Iio c⁻¹) μ) :
    IntegrableOn (fun x => f x⁻¹) (Set.Ioi c) μ := by
  simpa using hf.comp_inv

end MeasurableInvOrder

section MeasurableMul

variable [Group G] [MeasurableMul G]

/-- Translating a function by left-multiplication does not change its integral with respect to a
left-invariant measure. -/
@[to_additive
      /-- Translating a function by left-addition does not change its integral with respect to a
      left-invariant measure. -/]
/--
theorem `integral_mul_left_eq_self` / 定理 `integral_mul_left_eq_self`

English:
theorem integral_mul_left_eq_self
  given: [IsMulLeftInvariant μ] (f : G -> E) (g : G)
  proof: by
  have h_mul : MeasurableEmbedding fun x => g * x := (MeasurableEquiv.mulLeft g).measurableEmbedding
  rw [← h_mul.integral_map]; rw [map_mul_left_eq_self]

中文:
定理 integral_mul_left_eq_self
  条件: [IsMulLeftInvariant μ] (f : G -> E) (g : G)
  证明: by
  have h_mul : MeasurableEmbedding fun x => g * x := (MeasurableEquiv.mulLeft g).measurableEmbedding
  rw [← h_mul.integral_map]; rw [map_mul_left_eq_self]

Depends on / 依赖: MeasurableEmbedding, MeasurableEquiv, MeasurableEquiv.mulLeft, h_mul, h_mul.integral_map, integral_map, map_mul_left_eq_self, measurableEmbedding, mulLeft
-/
theorem integral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G -> E) (g : G) :
    (∫ x, f (g * x) ∂μ) = ∫ x, f x ∂μ := by
  have h_mul : MeasurableEmbedding fun x => g * x := (MeasurableEquiv.mulLeft g).measurableEmbedding
  rw [← h_mul.integral_map]; rw [map_mul_left_eq_self]

/-- Translating a function by right-multiplication does not change its integral with respect to a
right-invariant measure. -/
@[to_additive
      /-- Translating a function by right-addition does not change its integral with respect to a
      right-invariant measure. -/]
/--
theorem `integral_mul_right_eq_self` / 定理 `integral_mul_right_eq_self`

English:
theorem integral_mul_right_eq_self
  given: [IsMulRightInvariant μ] (f : G -> E) (g : G)
  proof: by
  have h_mul : MeasurableEmbedding fun x => x * g :=
    (MeasurableEquiv.mulRight g).measurableEmbedding
  rw [← h_mul.integral_map]; rw [map_mul_right_eq_self]

@[to_additive]

中文:
定理 integral_mul_right_eq_self
  条件: [IsMulRightInvariant μ] (f : G -> E) (g : G)
  证明: by
  have h_mul : MeasurableEmbedding fun x => x * g :=
    (MeasurableEquiv.mulRight g).measurableEmbedding
  rw [← h_mul.integral_map]; rw [map_mul_right_eq_self]

@[to_additive]

Depends on / 依赖: MeasurableEmbedding, MeasurableEquiv, MeasurableEquiv.mulRight, h_mul, h_mul.integral_map, integral_map, map_mul_right_eq_self, measurableEmbedding, mulRight
-/
theorem integral_mul_right_eq_self [IsMulRightInvariant μ] (f : G -> E) (g : G) :
    (∫ x, f (x * g) ∂μ) = ∫ x, f x ∂μ := by
  have h_mul : MeasurableEmbedding fun x => x * g :=
    (MeasurableEquiv.mulRight g).measurableEmbedding
  rw [← h_mul.integral_map]; rw [map_mul_right_eq_self]

@[to_additive]
/--
theorem `integral_div_right_eq_self` / 定理 `integral_div_right_eq_self`

English:
theorem integral_div_right_eq_self
  given: [IsMulRightInvariant μ] (f : G -> E) (g : G)
  proof: by
  simp_rw [div_eq_mul_inv, integral_mul_right_eq_self f g⁻¹]

中文:
定理 integral_div_right_eq_self
  条件: [IsMulRightInvariant μ] (f : G -> E) (g : G)
  证明: by
  simp_rw [div_eq_mul_inv, integral_mul_right_eq_self f g⁻¹]

Depends on / 依赖: div_eq_mul_inv, integral_mul_right_eq_self, simp_rw
-/
theorem integral_div_right_eq_self [IsMulRightInvariant μ] (f : G -> E) (g : G) :
    (∫ x, f (x / g) ∂μ) = ∫ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, integral_mul_right_eq_self f g⁻¹]

/-- If some left-translate of a function negates it, then the integral of the function with respect
to a left-invariant measure is 0. -/
@[to_additive
      /-- If some left-translate of a function negates it, then the integral of the function with
      respect to a left-invariant measure is 0. -/]
/--
theorem `integral_eq_zero_of_mul_left_eq_neg` / 定理 `integral_eq_zero_of_mul_left_eq_neg`

English:
theorem integral_eq_zero_of_mul_left_eq_neg
  given: [IsMulLeftInvariant μ] (hf' : forall x, f (g * x) = -f x)
  proof: by
  have : IsAddTorsionFree E := .of_isTorsionFree Real E
  simp_rw [← self_eq_neg, ← integral_neg, ← hf', integral_mul_left_eq_self]

中文:
定理 integral_eq_zero_of_mul_left_eq_neg
  条件: [IsMulLeftInvariant μ] (hf' : 对任意 x, f (g * x) = -f x)
  证明: by
  have : IsAddTorsionFree E := .of_isTorsionFree Real E
  simp_rw [← self_eq_neg, ← integral_neg, ← hf', integral_mul_left_eq_self]

Depends on / 依赖: IsAddTorsionFree, integral_mul_left_eq_self, integral_neg, of_isTorsionFree, self_eq_neg, simp_rw
-/
theorem integral_eq_zero_of_mul_left_eq_neg [IsMulLeftInvariant μ] (hf' : forall x, f (g * x) = -f x) :
    ∫ x, f x ∂μ = 0 := by
  have : IsAddTorsionFree E := .of_isTorsionFree Real E
  simp_rw [← self_eq_neg, ← integral_neg, ← hf', integral_mul_left_eq_self]

/-- If some right-translate of a function negates it, then the integral of the function with respect
to a right-invariant measure is 0. -/
@[to_additive
      /-- If some right-translate of a function negates it, then the integral of the function with
      respect to a right-invariant measure is 0. -/]
/--
theorem `integral_eq_zero_of_mul_right_eq_neg` / 定理 `integral_eq_zero_of_mul_right_eq_neg`

English:
theorem integral_eq_zero_of_mul_right_eq_neg
  given: [IsMulRightInvariant μ] (hf' : forall x, f (x * g) = -f x)
  proof: by
  have : IsAddTorsionFree E := .of_isTorsionFree Real E
  simp_rw [← self_eq_neg, ← integral_neg, ← hf', integral_mul_right_eq_self]

@[to_additive]

中文:
定理 integral_eq_zero_of_mul_right_eq_neg
  条件: [IsMulRightInvariant μ] (hf' : 对任意 x, f (x * g) = -f x)
  证明: by
  have : IsAddTorsionFree E := .of_isTorsionFree Real E
  simp_rw [← self_eq_neg, ← integral_neg, ← hf', integral_mul_right_eq_self]

@[to_additive]

Depends on / 依赖: IsAddTorsionFree, integral_mul_right_eq_self, integral_neg, of_isTorsionFree, self_eq_neg, simp_rw
-/
theorem integral_eq_zero_of_mul_right_eq_neg [IsMulRightInvariant μ] (hf' : forall x, f (x * g) = -f x) :
    ∫ x, f x ∂μ = 0 := by
  have : IsAddTorsionFree E := .of_isTorsionFree Real E
  simp_rw [← self_eq_neg, ← integral_neg, ← hf', integral_mul_right_eq_self]

@[to_additive]
/--
theorem `Integrable.comp_mul_left` / 定理 `Integrable.comp_mul_left`

English:
theorem Integrable.comp_mul_left
  given: {f : G -> F} [IsMulLeftInvariant μ] (hf : Integrable f μ) (g : G)
  proof: (hf.mono_measure (map_mul_left_eq_self μ g).le).comp_measurable measurable_const_mul g

@[to_additive]

中文:
定理 Integrable.comp_mul_left
  条件: {f : G -> F} [IsMulLeftInvariant μ] (hf : 整数egrable f μ) (g : G)
  证明: (hf.mono_measure (map_mul_left_eq_self μ g).le).comp_measurable measurable_const_mul g

@[to_additive]

Depends on / 依赖: comp_measurable, hf.mono_measure, map_mul_left_eq_self, measurable_const_mul, mono_measure
-/
theorem Integrable.comp_mul_left {f : G -> F} [IsMulLeftInvariant μ] (hf : Integrable f μ) (g : G) :
    Integrable (fun t => f (g * t)) μ :=
(hf.mono_measure (map_mul_left_eq_self μ g).le).comp_measurable measurable_const_mul g

@[to_additive]
/--
theorem `Integrable.comp_mul_right` / 定理 `Integrable.comp_mul_right`

English:
theorem Integrable.comp_mul_right
  statement: {f : G -> F} [IsMulRightInvariant μ] (hf : Integrable f μ)
  proof: (hf.mono_measure (map_mul_right_eq_self μ g).le).comp_measurable measurable_mul_const g

@[to_additive]

中文:
定理 Integrable.comp_mul_right
  结论: {f : G -> F} [IsMulRightInvariant μ] (hf : 整数egrable f μ)
  证明: (hf.mono_measure (map_mul_right_eq_self μ g).le).comp_measurable measurable_mul_const g

@[to_additive]

Depends on / 依赖: comp_measurable, hf.mono_measure, map_mul_right_eq_self, measurable_mul_const, mono_measure
-/
theorem Integrable.comp_mul_right {f : G -> F} [IsMulRightInvariant μ] (hf : Integrable f μ)
    (g : G) : Integrable (fun t => f (t * g)) μ :=
(hf.mono_measure (map_mul_right_eq_self μ g).le).comp_measurable measurable_mul_const g

@[to_additive]
/--
theorem `Integrable.comp_div_right` / 定理 `Integrable.comp_div_right`

English:
theorem Integrable.comp_div_right
  statement: {f : G -> F} [IsMulRightInvariant μ] (hf : Integrable f μ)
  proof: by
  simp_rw [div_eq_mul_inv]
  exact hf.comp_mul_right g⁻¹

中文:
定理 Integrable.comp_div_right
  结论: {f : G -> F} [IsMulRightInvariant μ] (hf : 整数egrable f μ)
  证明: by
  simp_rw [div_eq_mul_inv]
  exact hf.comp_mul_right g⁻¹

Depends on / 依赖: comp_mul_right, div_eq_mul_inv, hf.comp_mul_right, simp_rw
-/
theorem Integrable.comp_div_right {f : G -> F} [IsMulRightInvariant μ] (hf : Integrable f μ)
    (g : G) : Integrable (fun t => f (t / g)) μ := by
  simp_rw [div_eq_mul_inv]
  exact hf.comp_mul_right g⁻¹

variable [MeasurableInv G]

@[to_additive]
/--
theorem `Integrable.comp_div_left` / 定理 `Integrable.comp_div_left`

English:
theorem Integrable.comp_div_left
  statement: {f : G -> F} [IsInvInvariant μ] [IsMulLeftInvariant μ]
  proof: ((measurePreserving_div_left μ g).integrable_comp hf.aestronglyMeasurable).mpr hf

@[to_additive]

中文:
定理 Integrable.comp_div_left
  结论: {f : G -> F} [IsInvInvariant μ] [IsMulLeftInvariant μ]
  证明: ((measurePreserving_div_left μ g).integrable_comp hf.aestronglyMeasurable).mpr hf

@[to_additive]

Depends on / 依赖: aestronglyMeasurable, hf.aestronglyMeasurable, integrable_comp, measurePreserving_div_left
-/
theorem Integrable.comp_div_left {f : G -> F} [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (hf : Integrable f μ) (g : G) : Integrable (fun t => f (g / t)) μ :=
  ((measurePreserving_div_left μ g).integrable_comp hf.aestronglyMeasurable).mpr hf

@[to_additive]
/--
theorem `integrable_comp_div_left` / 定理 `integrable_comp_div_left`

English:
theorem integrable_comp_div_left
  given: (f : G -> F) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G)
  proof: by
  refine ⟨fun h => ?_, fun h => h.comp_div_left g⟩
  convert! h.comp_inv.comp_mul_left g⁻¹
  simp_rw [div_inv_eq_mul, mul_inv_cancel_left]

@[to_additive]

中文:
定理 integrable_comp_div_left
  条件: (f : G -> F) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G)
  证明: by
  refine ⟨fun h => ?_, fun h => h.comp_div_left g⟩
  convert! h.comp_inv.comp_mul_left g⁻¹
  simp_rw [div_inv_eq_mul, mul_inv_cancel_left]

@[to_additive]

Depends on / 依赖: comp_div_left, comp_inv, comp_mul_left, convert, div_inv_eq_mul, h.comp_div_left, h.comp_inv.comp_mul_left, mul_inv_cancel_left, simp_rw
-/
theorem integrable_comp_div_left (f : G -> F) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G) :
    Integrable (fun t => f (g / t)) μ ↔ Integrable f μ := by
  refine ⟨fun h => ?_, fun h => h.comp_div_left g⟩
  convert! h.comp_inv.comp_mul_left g⁻¹
  simp_rw [div_inv_eq_mul, mul_inv_cancel_left]

@[to_additive]
/--
theorem `integral_div_left_eq_self` / 定理 `integral_div_left_eq_self`

English:
theorem integral_div_left_eq_self
  statement: (f : G -> E) (μ : Measure G) [IsInvInvariant μ]
  proof: by
  simp_rw [div_eq_mul_inv, integral_inv_eq_self (fun x => f (x' * x)) μ,
    integral_mul_left_eq_self f x']

中文:
定理 integral_div_left_eq_self
  结论: (f : G -> E) (μ : Measure G) [IsInvInvariant μ]
  证明: by
  simp_rw [div_eq_mul_inv, integral_inv_eq_self (fun x => f (x' * x)) μ,
    integral_mul_left_eq_self f x']

Depends on / 依赖: div_eq_mul_inv, integral_inv_eq_self, integral_mul_left_eq_self, simp_rw
-/
theorem integral_div_left_eq_self (f : G -> E) (μ : Measure G) [IsInvInvariant μ]
    [IsMulLeftInvariant μ] (x' : G) : (∫ x, f (x' / x) ∂μ) = ∫ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, integral_inv_eq_self (fun x => f (x' * x)) μ,
    integral_mul_left_eq_self f x']

end MeasurableMul

section SMul

variable {G : Type*} [Group G] [MeasurableSpace α] [MulAction G α] [MeasurableConstSMul G α]

@[to_additive]
/--
theorem `integral_smul_eq_self` / 定理 `integral_smul_eq_self`

English:
theorem integral_smul_eq_self
  given: {μ : Measure α} [SMulInvariantMeasure G α μ] (f : α -> E) {g : G}
  proof: by
  have h : MeasurableEmbedding fun x : α => g • x := (MeasurableEquiv.smul g).measurableEmbedding
  rw [← h.integral_map]; rw [MeasureTheory.map_smul]

中文:
定理 integral_smul_eq_self
  条件: {μ : Measure α} [SMulInvariantMeasure G α μ] (f : α -> E) {g : G}
  证明: by
  have h : MeasurableEmbedding fun x : α => g • x := (MeasurableEquiv.smul g).measurableEmbedding
  rw [← h.integral_map]; rw [MeasureTheory.map_smul]

Depends on / 依赖: MeasurableEmbedding, MeasurableEquiv, MeasurableEquiv.smul, MeasureTheory, MeasureTheory.map_smul, h.integral_map, integral_map, map_smul, measurableEmbedding
-/
theorem integral_smul_eq_self {μ : Measure α} [SMulInvariantMeasure G α μ] (f : α -> E) {g : G} :
    (∫ x, f (g • x) ∂μ) = ∫ x, f x ∂μ := by
  have h : MeasurableEmbedding fun x : α => g • x := (MeasurableEquiv.smul g).measurableEmbedding
  rw [← h.integral_map]; rw [MeasureTheory.map_smul]

end SMul

end MeasureTheory
