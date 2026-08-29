/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Pullback of a measure

In this file we define the pullback `MeasureTheory.Measure.comap f μ`
of a measure `μ` along an injective map `f`
such that the image of any measurable set under `f` is a null-measurable set.
If `f` does not have these properties, then we define `comap f μ` to be zero.

In the future, we may decide to redefine `comap f μ` so that it gives meaningful results, e.g.,
for covering maps like `(↑) : ℝ → AddCircle (1 : ℝ)`.
-/

@[expose] public section

open Function Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureTheory

namespace Measure

variable {α β γ : Type*} {s : Set α}

open scoped Classical in
/--
Definition of `comapₗ` / `comapₗ` 的定义

English:
definition comapₗ
  signature: [MeasurableSpace α] [MeasurableSpace β] (f : α -> β)
  body: if hf : Injective f ∧ forall s, MeasurableSet s -> MeasurableSet (f '' s) then
    liftLinear (OuterMeasure.comap f) fun μ s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_sdiff hf.1]
      apply le_toOuterMeasure_caratheodory
      exact hf.2 s hs
  else 0

中文:
定义 comapₗ
  签名: [MeasurableSpace α] [MeasurableSpace β] (f : α -> β)
  定义体: if hf : Injective f ∧ forall s, MeasurableSet s -> MeasurableSet (f '' s) then
    liftLinear (OuterMeasure.comap f) fun μ s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_sdiff hf.1]
      apply le_toOuterMeasure_caratheodory
      exact hf.2 s hs
  else 0

Depends on / 依赖: Injective, MeasurableSet, OuterMeasure, OuterMeasure.comap, OuterMeasure.comap_apply, comap_apply, image_inter, image_sdiff, le_toOuterMeasure_caratheodory, liftLinear
-/
def comapₗ [MeasurableSpace α] [MeasurableSpace β] (f : α -> β) : Measure β ->ₗ[Real>=0∞] Measure α :=
  if hf : Injective f ∧ forall s, MeasurableSet s -> MeasurableSet (f '' s) then
    liftLinear (OuterMeasure.comap f) fun μ s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_sdiff hf.1]
      apply le_toOuterMeasure_caratheodory
      exact hf.2 s hs
  else 0

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comapₗ_apply` / 定理 `comapₗ_apply`

English:
theorem comapₗ_apply
  statement: {_ : MeasurableSpace α} {_ : MeasurableSpace β} (f : α -> β)
  proof: by
  rw [comapₗ]; rw [dif_pos]; rw [liftLinear_apply _ hs]; rw [OuterMeasure.comap_apply]; rw [coe_toOuterMeasure]
  exact ⟨hfi, hf⟩

中文:
定理 comapₗ_apply
  结论: {_ : MeasurableSpace α} {_ : MeasurableSpace β} (f : α -> β)
  证明: by
  rw [comapₗ]; rw [dif_pos]; rw [liftLinear_apply _ hs]; rw [OuterMeasure.comap_apply]; rw [coe_toOuterMeasure]
  exact ⟨hfi, hf⟩

Depends on / 依赖: OuterMeasure, OuterMeasure.comap_apply, coe_toOuterMeasure, comap_apply, dif_pos, liftLinear_apply
-/
theorem comapₗ_apply {_ : MeasurableSpace α} {_ : MeasurableSpace β} (f : α -> β)
    (hfi : Injective f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure β)
    (hs : MeasurableSet s) : comapₗ f μ s = μ (f '' s) := by
  rw [comapₗ]; rw [dif_pos]; rw [liftLinear_apply _ hs]; rw [OuterMeasure.comap_apply]; rw [coe_toOuterMeasure]
  exact ⟨hfi, hf⟩

open scoped Classical in
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: [MeasurableSpace α] [MeasurableSpace β] (f : α -> β) (μ : Measure β)
  body: if hf : Injective f ∧ forall s, MeasurableSet s -> NullMeasurableSet (f '' s) μ then
    (OuterMeasure.comap f μ.toOuterMeasure).toMeasure fun s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_sdiff hf.1]
      exact (measure_inter_add_sdiff₀ _ (hf.2 s hs)).symm
  else 

中文:
定义 comap
  签名: [MeasurableSpace α] [MeasurableSpace β] (f : α -> β) (μ : Measure β)
  定义体: if hf : Injective f ∧ forall s, MeasurableSet s -> NullMeasurableSet (f '' s) μ then
    (OuterMeasure.comap f μ.toOuterMeasure).toMeasure fun s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_sdiff hf.1]
      exact (measure_inter_add_sdiff₀ _ (hf.2 s hs)).symm
  else 

Depends on / 依赖: Injective, MeasurableSet, NullMeasurableSet, OuterMeasure, OuterMeasure.comap, OuterMeasure.comap_apply, comap_apply, image_inter, image_sdiff, toMeasure, toOuterMeasure
-/
def comap [MeasurableSpace α] [MeasurableSpace β] (f : α -> β) (μ : Measure β) : Measure α :=
  if hf : Injective f ∧ forall s, MeasurableSet s -> NullMeasurableSet (f '' s) μ then
    (OuterMeasure.comap f μ.toOuterMeasure).toMeasure fun s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_sdiff hf.1]
      exact (measure_inter_add_sdiff₀ _ (hf.2 s hs)).symm
  else 0

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {f : α -> β} {g : β -> γ}

/--
theorem `comap_apply₀` / 定理 `comap_apply₀`

English:
theorem comap_apply₀
  statement: (f : α -> β) (μ : Measure β) (hfi : Injective f)
  proof: by
  rw [comap]; rw [dif_pos (And.intro hfi hf)] at hs ⊢
  rw [toMeasure_apply₀ _ _ hs]; rw [OuterMeasure.comap_apply]; rw [coe_toOuterMeasure]

中文:
定理 comap_apply₀
  结论: (f : α -> β) (μ : Measure β) (hfi : Injective f)
  证明: by
  rw [comap]; rw [dif_pos (And.intro hfi hf)] at hs ⊢
  rw [toMeasure_apply₀ _ _ hs]; rw [OuterMeasure.comap_apply]; rw [coe_toOuterMeasure]

Depends on / 依赖: And.intro, OuterMeasure, OuterMeasure.comap_apply, coe_toOuterMeasure, comap_apply, dif_pos
-/
theorem comap_apply₀ (f : α -> β) (μ : Measure β) (hfi : Injective f)
    (hf : forall s, MeasurableSet s -> NullMeasurableSet (f '' s) μ)
    (hs : NullMeasurableSet s (comap f μ)) : comap f μ s = μ (f '' s) := by
  rw [comap]; rw [dif_pos (And.intro hfi hf)] at hs ⊢
  rw [toMeasure_apply₀ _ _ hs]; rw [OuterMeasure.comap_apply]; rw [coe_toOuterMeasure]

/--
lemma `comap_undef` / 引理 `comap_undef`

English:
lemma comap_undef
  statement: {μ : Measure β}
  proof: dif_neg h

中文:
引理 comap_undef
  结论: {μ : Measure β}
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
lemma comap_undef {μ : Measure β}
    (h : ¬ (Injective f ∧ forall s, MeasurableSet s -> NullMeasurableSet (f '' s) μ)) :
    comap f μ = 0 := dif_neg h

/--
theorem `le_comap_apply` / 定理 `le_comap_apply`

English:
theorem le_comap_apply
  statement: (f : α -> β) (μ : Measure β) (hfi : Injective f)
  proof: by
  rw [comap]; rw [dif_pos (And.intro hfi hf)]
  exact le_toMeasure_apply _ _ _

中文:
定理 le_comap_apply
  结论: (f : α -> β) (μ : Measure β) (hfi : Injective f)
  证明: by
  rw [comap]; rw [dif_pos (And.intro hfi hf)]
  exact le_toMeasure_apply _ _ _

Depends on / 依赖: And.intro, dif_pos, le_toMeasure_apply
-/
theorem le_comap_apply (f : α -> β) (μ : Measure β) (hfi : Injective f)
    (hf : forall s, MeasurableSet s -> NullMeasurableSet (f '' s) μ) (s : Set α) :
    μ (f '' s) <= comap f μ s := by
  rw [comap]; rw [dif_pos (And.intro hfi hf)]
  exact le_toMeasure_apply _ _ _

/--
theorem `comap_apply` / 定理 `comap_apply`

English:
theorem comap_apply
  statement: (f : α -> β) (hfi : Injective f)
  proof: comap_apply₀ f μ hfi (fun s hs => (hf s hs).nullMeasurableSet) hs.nullMeasurableSet

中文:
定理 comap_apply
  结论: (f : α -> β) (hfi : Injective f)
  证明: comap_apply₀ f μ hfi (fun s hs => (hf s hs).nullMeasurableSet) hs.nullMeasurableSet

Depends on / 依赖: hs.nullMeasurableSet, nullMeasurableSet
-/
theorem comap_apply (f : α -> β) (hfi : Injective f)
    (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    comap f μ s = μ (f '' s) :=
  comap_apply₀ f μ hfi (fun s hs => (hf s hs).nullMeasurableSet) hs.nullMeasurableSet

/--
theorem `comap_apply_le` / 定理 `comap_apply_le`

English:
theorem comap_apply_le
  given: (f : α -> β) (μ : Measure β) (hs : NullMeasurableSet s (μ.comap f))
  proof: by
  by_cases hf : Injective f ∧ forall t, MeasurableSet t -> NullMeasurableSet (f '' t) μ
  · rw [comap_apply₀ _ _ hf.1 hf.2 hs]
  · simp [comap_undef hf]

中文:
定理 comap_apply_le
  条件: (f : α -> β) (μ : Measure β) (hs : NullMeasurableSet s (μ.comap f))
  证明: by
  by_cases hf : Injective f ∧ forall t, MeasurableSet t -> NullMeasurableSet (f '' t) μ
  · rw [comap_apply₀ _ _ hf.1 hf.2 hs]
  · simp [comap_undef hf]

Depends on / 依赖: Injective, MeasurableSet, NullMeasurableSet, comap_undef
-/
theorem comap_apply_le (f : α -> β) (μ : Measure β) (hs : NullMeasurableSet s (μ.comap f)) :
    μ.comap f s <= μ (f '' s) := by
  by_cases hf : Injective f ∧ forall t, MeasurableSet t -> NullMeasurableSet (f '' t) μ
  · rw [comap_apply₀ _ _ hf.1 hf.2 hs]
  · simp [comap_undef hf]

/--
theorem `comapₗ_eq_comap` / 定理 `comapₗ_eq_comap`

English:
theorem comapₗ_eq_comap
  statement: (f : α -> β) (hfi : Injective f)
  proof: (comapₗ_apply f hfi hf μ hs).trans (comap_apply f hfi hf μ hs).symm

中文:
定理 comapₗ_eq_comap
  结论: (f : α -> β) (hfi : Injective f)
  证明: (comapₗ_apply f hfi hf μ hs).trans (comap_apply f hfi hf μ hs).symm

Depends on / 依赖: comap_apply
-/
theorem comapₗ_eq_comap (f : α -> β) (hfi : Injective f)
    (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    comapₗ f μ s = comap f μ s :=
  (comapₗ_apply f hfi hf μ hs).trans (comap_apply f hfi hf μ hs).symm

/--
theorem `measure_image_eq_zero_of_comap_eq_zero` / 定理 `measure_image_eq_zero_of_comap_eq_zero`

English:
theorem measure_image_eq_zero_of_comap_eq_zero
  statement: (f : α -> β) (μ : Measure β) (hfi : Injective f)
  proof: by
  rw [← nonpos_iff_eq_zero]
  exact (le_comap_apply f μ hfi hf s).trans hs.le

中文:
定理 measure_image_eq_zero_of_comap_eq_zero
  结论: (f : α -> β) (μ : Measure β) (hfi : Injective f)
  证明: by
  rw [← nonpos_iff_eq_zero]
  exact (le_comap_apply f μ hfi hf s).trans hs.le

Depends on / 依赖: hs.le, le_comap_apply, nonpos_iff_eq_zero
-/
theorem measure_image_eq_zero_of_comap_eq_zero (f : α -> β) (μ : Measure β) (hfi : Injective f)
    (hf : forall s, MeasurableSet s -> NullMeasurableSet (f '' s) μ) {s : Set α} (hs : comap f μ s = 0) :
    μ (f '' s) = 0 := by
  rw [← nonpos_iff_eq_zero]
  exact (le_comap_apply f μ hfi hf s).trans hs.le

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ae_eq_image_of_ae_eq_comap` / 定理 `ae_eq_image_of_ae_eq_comap`

English:
theorem ae_eq_image_of_ae_eq_comap
  statement: (f : α -> β) (μ : Measure β) (hfi : Injective f)
  proof: by
  rw [EventuallyEq]; rw [ae_iff] at hst ⊢
  have h_eq_α : { a : α | ¬s a = t a } = s \ t union t \ s := by
    ext1 x
    simp only [eq_iff_iff, mem_ofPred_eq, mem_union, Set.mem_sdiff]
    tauto
  have h_eq_β : { a : β | ¬(f '' s) a = (f '' t) a } = f '' s \ f '' t union f '' t \ f '' s := by
  

中文:
定理 ae_eq_image_of_ae_eq_comap
  结论: (f : α -> β) (μ : Measure β) (hfi : Injective f)
  证明: by
  rw [EventuallyEq]; rw [ae_iff] at hst ⊢
  have h_eq_α : { a : α | ¬s a = t a } = s \ t union t \ s := by
    ext1 x
    simp only [eq_iff_iff, mem_ofPred_eq, mem_union, Set.mem_sdiff]
    tauto
  have h_eq_β : { a : β | ¬(f '' s) a = (f '' t) a } = f '' s \ f '' t union f '' t \ f '' s := by
  

Depends on / 依赖: EventuallyEq, Set.image_sdiff, Set.image_union, Set.mem_sdiff, ae_iff, eq_iff_iff, image_sdiff, image_union, measure_image_eq_, mem_ofPred_eq, mem_sdiff, mem_union
-/
theorem ae_eq_image_of_ae_eq_comap (f : α -> β) (μ : Measure β) (hfi : Injective f)
    (hf : forall s, MeasurableSet s -> NullMeasurableSet (f '' s) μ)
    {s t : Set α} (hst : s =ᵐ[comap f μ] t) : f '' s =ᵐ[μ] f '' t := by
  rw [EventuallyEq]; rw [ae_iff] at hst ⊢
  have h_eq_α : { a : α | ¬s a = t a } = s \ t union t \ s := by
    ext1 x
    simp only [eq_iff_iff, mem_ofPred_eq, mem_union, Set.mem_sdiff]
    tauto
  have h_eq_β : { a : β | ¬(f '' s) a = (f '' t) a } = f '' s \ f '' t union f '' t \ f '' s := by
    ext1 x
    simp only [eq_iff_iff, mem_ofPred_eq, mem_union, Set.mem_sdiff]
    tauto
  rw [← Set.image_sdiff hfi]; rw [← Set.image_sdiff hfi]; rw [← Set.image_union] at h_eq_β
  rw [h_eq_β]
  rw [h_eq_α] at hst
  exact measure_image_eq_zero_of_comap_eq_zero f μ hfi hf hst

/--
theorem `NullMeasurableSet.image` / 定理 `NullMeasurableSet.image`

English:
theorem NullMeasurableSet.image
  statement: (f : α -> β) (μ : Measure β) (hfi : Injective f)
  proof: by
  refine ⟨toMeasurable μ (f '' toMeasurable (μ.comap f) s), measurableSet_toMeasurable _ _, ?_⟩
  refine EventuallyEq.trans ?_ (NullMeasurableSet.toMeasurable_ae_eq ?_).symm
  swap
  · exact hf _ (measurableSet_toMeasurable _ _)
  have h : toMeasurable (comap f μ) s =ᵐ[comap f μ] s :=
    NullMea

中文:
定理 NullMeasurableSet.image
  结论: (f : α -> β) (μ : Measure β) (hfi : Injective f)
  证明: by
  refine ⟨toMeasurable μ (f '' toMeasurable (μ.comap f) s), measurableSet_toMeasurable _ _, ?_⟩
  refine EventuallyEq.trans ?_ (NullMeasurableSet.toMeasurable_ae_eq ?_).symm
  swap
  · exact hf _ (measurableSet_toMeasurable _ _)
  have h : toMeasurable (comap f μ) s =ᵐ[comap f μ] s :=
    NullMea

Depends on / 依赖: EventuallyEq, EventuallyEq.trans, NullMeasurableSet, NullMeasurableSet.toMeasurable_ae_eq, ae_eq_image_of_ae_eq_comap, h.symm, measurableSet_toMeasurable, toMeasurable, toMeasurable_ae_eq
-/
theorem NullMeasurableSet.image (f : α -> β) (μ : Measure β) (hfi : Injective f)
    (hf : forall s, MeasurableSet s -> NullMeasurableSet (f '' s) μ)
    (hs : NullMeasurableSet s (μ.comap f)) : NullMeasurableSet (f '' s) μ := by
  refine ⟨toMeasurable μ (f '' toMeasurable (μ.comap f) s), measurableSet_toMeasurable _ _, ?_⟩
  refine EventuallyEq.trans ?_ (NullMeasurableSet.toMeasurable_ae_eq ?_).symm
  swap
  · exact hf _ (measurableSet_toMeasurable _ _)
  have h : toMeasurable (comap f μ) s =ᵐ[comap f μ] s :=
    NullMeasurableSet.toMeasurable_ae_eq hs
  exact ae_eq_image_of_ae_eq_comap f μ hfi hf h.symm

/--
theorem `comap_preimage` / 定理 `comap_preimage`

English:
theorem comap_preimage
  statement: (f : α -> β) (μ : Measure β) (hf : Injective f) (hf' : Measurable f)
  proof: by
  rw [comap_apply₀ _ _ hf h (hf' hs).nullMeasurableSet]; rw [image_preimage_eq_inter_range]

中文:
定理 comap_preimage
  结论: (f : α -> β) (μ : Measure β) (hf : Injective f) (hf' : Measurable f)
  证明: by
  rw [comap_apply₀ _ _ hf h (hf' hs).nullMeasurableSet]; rw [image_preimage_eq_inter_range]

Depends on / 依赖: image_preimage_eq_inter_range, nullMeasurableSet
-/
theorem comap_preimage (f : α -> β) (μ : Measure β) (hf : Injective f) (hf' : Measurable f)
    (h : forall t, MeasurableSet t -> NullMeasurableSet (f '' t) μ) {s : Set β} (hs : MeasurableSet s) :
    μ.comap f (f ⁻¹' s) = μ (s inter range f) := by
  rw [comap_apply₀ _ _ hf h (hf' hs).nullMeasurableSet]; rw [image_preimage_eq_inter_range]

/--
lemma `comap_zero` / 引理 `comap_zero`

English:
lemma comap_zero
  given: (f : α -> β)
  statement: (0 : Measure β).comap f = 0
  proof: by
  by_cases hf : Injective f ∧ forall s, MeasurableSet s -> NullMeasurableSet (f '' s) (0 : Measure β)
  · simp [comap, hf]
  · simp [comap, hf]

@[simp]

中文:
引理 comap_zero
  条件: (f : α -> β)
  结论: (0 : Measure β).comap f = 0
  证明: by
  by_cases hf : Injective f ∧ forall s, MeasurableSet s -> NullMeasurableSet (f '' s) (0 : Measure β)
  · simp [comap, hf]
  · simp [comap, hf]

@[simp]
-/
@[simp] lemma comap_zero (f : α -> β) : (0 : Measure β).comap f = 0 := by
  by_cases hf : Injective f ∧ forall s, MeasurableSet s -> NullMeasurableSet (f '' s) (0 : Measure β)
  · simp [comap, hf]
  · simp [comap, hf]

@[simp]
/--
lemma `comap_id` / 引理 `comap_id`

English:
lemma comap_id
  given: (μ : Measure β)
  statement: comap (fun x => x) μ = μ
  proof: by
  ext s hs
  rw [comap_apply]; rw [image_id']
  · exact injective_id
  all_goals simp [*]

中文:
引理 comap_id
  条件: (μ : Measure β)
  结论: comap (fun x => x) μ = μ
  证明: by
  ext s hs
  rw [comap_apply]; rw [image_id']
  · exact injective_id
  all_goals simp [*]

Depends on / 依赖: all_goals, comap_apply, image_id, injective_id
-/
lemma comap_id (μ : Measure β) : comap (fun x => x) μ = μ := by
  ext s hs
  rw [comap_apply]; rw [image_id']
  · exact injective_id
  all_goals simp [*]

/--
lemma `comap_comap` / 引理 `comap_comap`

English:
lemma comap_comap
  statement: (hf' : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (hg : Injective g)
  proof: by
  by_cases hf : Injective f
  · ext s hs
    rw [comap_apply _ hf hf' _ hs]; rw [comap_apply _ hg hg' _ (hf' _ hs)]; rw [comap_apply _ (hg.comp hf) (fun t ht => image_comp g f _ ▸ hg' _ <| hf' _ ht) _ hs]; rw [image_comp]
  · rw [comap, dif_neg <| mt And.left hf, comap, dif_neg fun h => hf h.1.of

中文:
引理 comap_comap
  结论: (hf' : 对任意 s, MeasurableSet s -> MeasurableSet (f '' s)) (hg : Injective g)
  证明: by
  by_cases hf : Injective f
  · ext s hs
    rw [comap_apply _ hf hf' _ hs]; rw [comap_apply _ hg hg' _ (hf' _ hs)]; rw [comap_apply _ (hg.comp hf) (fun t ht => image_comp g f _ ▸ hg' _ <| hf' _ ht) _ hs]; rw [image_comp]
  · rw [comap, dif_neg <| mt And.left hf, comap, dif_neg fun h => hf h.1.of

Depends on / 依赖: And.left, Injective, comap_apply, dif_neg, hg.comp, image_comp, of_comp
-/
lemma comap_comap (hf' : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (hg : Injective g)
    (hg' : forall s, MeasurableSet s -> MeasurableSet (g '' s)) (μ : Measure γ) :
    comap f (comap g μ) = comap (g ∘ f) μ := by
  by_cases hf : Injective f
  · ext s hs
    rw [comap_apply _ hf hf' _ hs]; rw [comap_apply _ hg hg' _ (hf' _ hs)]; rw [comap_apply _ (hg.comp hf) (fun t ht => image_comp g f _ ▸ hg' _ <| hf' _ ht) _ hs]; rw [image_comp]
  · rw [comap, dif_neg <| mt And.left hf, comap, dif_neg fun h => hf h.1.of_comp]

/--
lemma `comap_smul` / 引理 `comap_smul`

English:
lemma comap_smul
  given: {μ : Measure β} (c : Real>=0∞)
  statement: comap f (c • μ) = c • comap f μ
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  by_cases h : Function.Injective f ∧ forall s : Set α, MeasurableSet s -> NullMeasurableSet (f '' s) μ
  · ext s hs
    rw [comap_apply₀ f _ h.1 _ hs.nullMeasurableSet]; rw [smul_apply]; rw [smul_apply]; rw [comap_apply₀ f μ h.1 h.2 hs.nullMeasurableSet

中文:
引理 comap_smul
  条件: {μ : Measure β} (c : 实数>=0∞)
  结论: comap f (c • μ) = c • comap f μ
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  by_cases h : Function.Injective f ∧ forall s : Set α, MeasurableSet s -> NullMeasurableSet (f '' s) μ
  · ext s hs
    rw [comap_apply₀ f _ h.1 _ hs.nullMeasurableSet]; rw [smul_apply]; rw [smul_apply]; rw [comap_apply₀ f μ h.1 h.2 hs.nullMeasurableSet

Depends on / 依赖: Function, Function.Injective, Injective, MeasurableSet, NullMeasurableSet, eq_or_ne, hs.nullMeasurableSet, nullMeasurableSet, nullMeasurableSet_smul_measu, nullMeasurableSet_smul_measure_iff, smul_apply
-/
lemma comap_smul {μ : Measure β} (c : Real>=0∞) : comap f (c • μ) = c • comap f μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  by_cases h : Function.Injective f ∧ forall s : Set α, MeasurableSet s -> NullMeasurableSet (f '' s) μ
  · ext s hs
    rw [comap_apply₀ f _ h.1 _ hs.nullMeasurableSet]; rw [smul_apply]; rw [smul_apply]; rw [comap_apply₀ f μ h.1 h.2 hs.nullMeasurableSet]
    simpa [nullMeasurableSet_smul_measure_iff hc] using h.2
  · have h' : ¬ (Function.Injective f ∧
        forall (s : Set α), MeasurableSet s -> NullMeasurableSet (f '' s) (c • μ)) := by
      simpa [nullMeasurableSet_smul_measure_iff hc] using h
    simp [comap_undef, h, h']

end Measure

end MeasureTheory

open MeasureTheory Measure

variable {α β : Type*} {ma : MeasurableSpace α} {mb : MeasurableSpace β}

/--
lemma `MeasurableEmbedding.comap_add` / 引理 `MeasurableEmbedding.comap_add`

English:
lemma MeasurableEmbedding.comap_add
  given: {f : α -> β} (hf : MeasurableEmbedding f) (μ ν : Measure β)
  proof: by
  ext s hs
  simp only [← comapₗ_eq_comap _ hf.injective (fun _ => hf.measurableSet_image.mpr) _ hs,
    map_add, add_apply]

中文:
引理 MeasurableEmbedding.comap_add
  条件: {f : α -> β} (hf : MeasurableEmbedding f) (μ ν : Measure β)
  证明: by
  ext s hs
  simp only [← comapₗ_eq_comap _ hf.injective (fun _ => hf.measurableSet_image.mpr) _ hs,
    map_add, add_apply]

Depends on / 依赖: add_apply, hf.injective, hf.measurableSet_image.mpr, injective, map_add, measurableSet_image
-/
lemma MeasurableEmbedding.comap_add {f : α -> β} (hf : MeasurableEmbedding f) (μ ν : Measure β) :
    (μ + ν).comap f = μ.comap f + ν.comap f := by
  ext s hs
  simp only [← comapₗ_eq_comap _ hf.injective (fun _ => hf.measurableSet_image.mpr) _ hs,
    map_add, add_apply]

namespace MeasurableEquiv

/--
lemma `comap_symm` / 引理 `comap_symm`

English:
lemma comap_symm
  given: {μ : Measure α} (e : α ≃ᵐ β)
  statement: μ.comap e.symm = μ.map e
  proof: by
  ext s hs
  rw [e.map_apply]; rw [Measure.comap_apply _ e.symm.injective _ _ hs]; rw [image_symm]
  exact fun t ht => e.symm.measurableSet_image.mpr ht

中文:
引理 comap_symm
  条件: {μ : Measure α} (e : α ≃ᵐ β)
  结论: μ.comap e.symm = μ.map e
  证明: by
  ext s hs
  rw [e.map_apply]; rw [Measure.comap_apply _ e.symm.injective _ _ hs]; rw [image_symm]
  exact fun t ht => e.symm.measurableSet_image.mpr ht

Depends on / 依赖: Measure, Measure.comap_apply, comap_apply, e.map_apply, e.symm.injective, e.symm.measurableSet_image.mpr, image_symm, injective, map_apply, measurableSet_image
-/
lemma comap_symm {μ : Measure α} (e : α ≃ᵐ β) : μ.comap e.symm = μ.map e := by
  ext s hs
  rw [e.map_apply]; rw [Measure.comap_apply _ e.symm.injective _ _ hs]; rw [image_symm]
  exact fun t ht => e.symm.measurableSet_image.mpr ht

/--
lemma `map_symm` / 引理 `map_symm`

English:
lemma map_symm
  given: {μ : Measure α} (e : β ≃ᵐ α)
  statement: μ.map e.symm = μ.comap e
  proof: by
  rw [← comap_symm]; rw [symm_symm]

中文:
引理 map_symm
  条件: {μ : Measure α} (e : β ≃ᵐ α)
  结论: μ.map e.symm = μ.comap e
  证明: by
  rw [← comap_symm]; rw [symm_symm]

Depends on / 依赖: comap_symm, symm_symm
-/
lemma map_symm {μ : Measure α} (e : β ≃ᵐ α) : μ.map e.symm = μ.comap e := by
  rw [← comap_symm]; rw [symm_symm]

end MeasurableEquiv

/--
lemma `MeasureTheory.Measure.comap_swap` / 引理 `MeasureTheory.Measure.comap_swap`

English:
lemma MeasureTheory.Measure.comap_swap
  given: (μ : Measure (α × β))
  statement: μ.comap .swap = μ.map .swap
  proof: (MeasurableEquiv.prodComm ..).comap_symm

中文:
引理 MeasureTheory.Measure.comap_swap
  条件: (μ : Measure (α × β))
  结论: μ.comap .swap = μ.map .swap
  证明: (MeasurableEquiv.prodComm ..).comap_symm

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.prodComm, comap_symm, prodComm
-/
lemma MeasureTheory.Measure.comap_swap (μ : Measure (α × β)) : μ.comap .swap = μ.map .swap :=
  (MeasurableEquiv.prodComm ..).comap_symm
