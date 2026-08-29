/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.Order.Filter.EventuallyConst

/-!
# Measure-preserving maps

We say that `f : α → β` is a measure-preserving map w.r.t. measures `μ : Measure α` and
`ν : Measure β` if `f` is measurable and `map f μ = ν`. In this file we define the predicate
`MeasureTheory.MeasurePreserving` and prove its basic properties.

We use the term "measure preserving" because in many applications `α = β` and `μ = ν`.

## References

Partially based on
[this](https://www.isa-afp.org/browser_info/current/AFP/Ergodic_Theory/Measure_Preserving_Transformations.html)
Isabelle formalization.

## Tags

measure-preserving map, measure
-/

public section

open MeasureTheory.Measure Function Set
open scoped ENNReal

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

namespace MeasureTheory

variable {μa : Measure α} {μb : Measure β} {μc : Measure γ} {μd : Measure δ}

/--
Definition of `MeasurePreserving` / `MeasurePreserving` 的定义

English:
structure MeasurePreserving
  parameters: (f : α -> β)
  axioms and operations (2):
    - measurable : Measurable f
    - map_eq : map f μa = μb

中文:
结构 MeasurePreserving
  参数: (f : α -> β)
  公理与运算 (2 个):
    - measurable : Measurable f
    - map_eq : map f μa = μb

Depends on / 依赖: Measurable, Measure, map_eq, measurable, protected, volume_tac
-/
structure MeasurePreserving (f : α -> β)
  (μa : Measure α := by volume_tac) (μb : Measure β := by volume_tac) : Prop where
  protected measurable : Measurable f
  protected map_eq : map f μa = μb

/--
theorem `_root_.Measurable.measurePreserving` / 定理 `_root_.Measurable.measurePreserving`

English:
theorem _root_.Measurable.measurePreserving
  proof: ⟨h, rfl⟩

中文:
定理 _root_.Measurable.measurePreserving
  证明: ⟨h, rfl⟩
-/
protected theorem _root_.Measurable.measurePreserving
    {f : α -> β} (h : Measurable f) (μa : Measure α) : MeasurePreserving f μa (map f μa) :=
  ⟨h, rfl⟩

namespace MeasurePreserving

/--
theorem `id` / 定理 `id`

English:
theorem id
  given: (μ : Measure α)
  statement: MeasurePreserving id μ μ
  proof: ⟨measurable_id, map_id⟩

中文:
定理 id
  条件: (μ : Measure α)
  结论: MeasurePreserving id μ μ
  证明: ⟨measurable_id, map_id⟩
-/
protected theorem id (μ : Measure α) : MeasurePreserving id μ μ :=
  ⟨measurable_id, map_id⟩

/--
theorem `aemeasurable` / 定理 `aemeasurable`

English:
theorem aemeasurable
  given: {f : α -> β} (hf : MeasurePreserving f μa μb)
  statement: AEMeasurable f μa
  proof: hf.1.aemeasurable

中文:
定理 aemeasurable
  条件: {f : α -> β} (hf : MeasurePreserving f μa μb)
  结论: AEMeasurable f μa
  证明: hf.1.aemeasurable
-/
protected theorem aemeasurable {f : α -> β} (hf : MeasurePreserving f μa μb) : AEMeasurable f μa :=
  hf.1.aemeasurable

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  statement: {f f' : α -> β} (hf : MeasurePreserving f μa μb) (hf' : Measurable f')
  proof: by
  refine ⟨hf', ?_⟩
  rw [Measure.map_congr h.symm]
  exact hf.map_eq

@[nontriviality]

中文:
定理 congr
  结论: {f f' : α -> β} (hf : MeasurePreserving f μa μb) (hf' : Measurable f')
  证明: by
  refine ⟨hf', ?_⟩
  rw [Measure.map_congr h.symm]
  exact hf.map_eq

@[nontriviality]
-/
protected theorem congr {f f' : α -> β} (hf : MeasurePreserving f μa μb) (hf' : Measurable f')
    (h : f =ᵐ[μa] f') : MeasurePreserving f' μa μb := by
  refine ⟨hf', ?_⟩
  rw [Measure.map_congr h.symm]
  exact hf.map_eq

@[nontriviality]
/--
theorem `of_isEmpty` / 定理 `of_isEmpty`

English:
theorem of_isEmpty
  given: [IsEmpty β] (f : α -> β) (μa : Measure α) (μb : Measure β)
  proof: ⟨measurable_of_subsingleton_codomain _, Subsingleton.elim _ _⟩

中文:
定理 of_isEmpty
  条件: [IsEmpty β] (f : α -> β) (μa : Measure α) (μb : Measure β)
  证明: ⟨measurable_of_subsingleton_codomain _, Subsingleton.elim _ _⟩

Depends on / 依赖: IsScalarTower, Subsingleton, Subsingleton.elim, measurable_of_subsingleton_codomain
-/
theorem of_isEmpty [IsEmpty β] (f : α -> β) (μa : Measure α) (μb : Measure β) :
    MeasurePreserving f μa μb :=
  ⟨measurable_of_subsingleton_codomain _, Subsingleton.elim _ _⟩

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (e : α ≃ᵐ β) {μa : Measure α} {μb : Measure β} (h : MeasurePreserving e μa μb)
  proof: ⟨e.symm.measurable, by
    rw [← h.map_eq]; rw [map_map e.symm.measurable e.measurable]; rw [e.symm_comp_self]; rw [map_id]⟩

中文:
定理 symm
  条件: (e : α ≃ᵐ β) {μa : Measure α} {μb : Measure β} (h : MeasurePreserving e μa μb)
  证明: ⟨e.symm.measurable, by
    rw [← h.map_eq]; rw [map_map e.symm.measurable e.measurable]; rw [e.symm_comp_self]; rw [map_id]⟩

Depends on / 依赖: e.measurable, e.symm.measurable, e.symm_comp_self, h.map_eq, map_eq, map_id, map_map, measurable, symm_comp_self
-/
theorem symm (e : α ≃ᵐ β) {μa : Measure α} {μb : Measure β} (h : MeasurePreserving e μa μb) :
    MeasurePreserving e.symm μb μa :=
  ⟨e.symm.measurable, by
    rw [← h.map_eq]; rw [map_map e.symm.measurable e.measurable]; rw [e.symm_comp_self]; rw [map_id]⟩

/--
theorem `restrict_preimage` / 定理 `restrict_preimage`

English:
theorem restrict_preimage
  statement: {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
  proof: ⟨hf.measurable, by rw [← hf.map_eq, restrict_map hf.measurable hs]⟩

中文:
定理 restrict_preimage
  结论: {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
  证明: ⟨hf.measurable, by rw [← hf.map_eq, restrict_map hf.measurable hs]⟩

Depends on / 依赖: hf.map_eq, hf.measurable, map_eq, measurable, restrict_map
-/
theorem restrict_preimage {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : MeasurableSet s) : MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.measurable, by rw [← hf.map_eq, restrict_map hf.measurable hs]⟩

/--
theorem `restrict_preimage_emb` / 定理 `restrict_preimage_emb`

English:
theorem restrict_preimage_emb
  statement: {f : α -> β} (hf : MeasurePreserving f μa μb)
  proof: ⟨hf.measurable, by rw [← hf.map_eq, h₂.restrict_map]⟩

中文:
定理 restrict_preimage_emb
  结论: {f : α -> β} (hf : MeasurePreserving f μa μb)
  证明: ⟨hf.measurable, by rw [← hf.map_eq, h₂.restrict_map]⟩

Depends on / 依赖: hf.map_eq, hf.measurable, map_eq, measurable, restrict_map
-/
theorem restrict_preimage_emb {f : α -> β} (hf : MeasurePreserving f μa μb)
    (h₂ : MeasurableEmbedding f) (s : Set β) :
    MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.measurable, by rw [← hf.map_eq, h₂.restrict_map]⟩

/--
theorem `restrict_image_emb` / 定理 `restrict_image_emb`

English:
theorem restrict_image_emb
  statement: {f : α -> β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f)
  proof: by
  simpa only [Set.preimage_image_eq _ h₂.injective] using hf.restrict_preimage_emb h₂ (f '' s)

中文:
定理 restrict_image_emb
  结论: {f : α -> β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f)
  证明: by
  simpa only [Set.preimage_image_eq _ h₂.injective] using hf.restrict_preimage_emb h₂ (f '' s)

Depends on / 依赖: Set.preimage_image_eq, hf.restrict_preimage_emb, injective, preimage_image_eq, restrict_preimage_emb
-/
theorem restrict_image_emb {f : α -> β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f)
    (s : Set α) : MeasurePreserving f (μa.restrict s) (μb.restrict (f '' s)) := by
  simpa only [Set.preimage_image_eq _ h₂.injective] using hf.restrict_preimage_emb h₂ (f '' s)

/--
theorem `aemeasurable_comp_iff` / 定理 `aemeasurable_comp_iff`

English:
theorem aemeasurable_comp_iff
  statement: {f : α -> β} (hf : MeasurePreserving f μa μb)
  proof: by
  rw [← hf.map_eq]; rw [h₂.aemeasurable_map_iff]

中文:
定理 aemeasurable_comp_iff
  结论: {f : α -> β} (hf : MeasurePreserving f μa μb)
  证明: by
  rw [← hf.map_eq]; rw [h₂.aemeasurable_map_iff]

Depends on / 依赖: aemeasurable_map_iff, hf.map_eq, map_eq
-/
theorem aemeasurable_comp_iff {f : α -> β} (hf : MeasurePreserving f μa μb)
    (h₂ : MeasurableEmbedding f) {g : β -> γ} : AEMeasurable (g ∘ f) μa ↔ AEMeasurable g μb := by
  rw [← hf.map_eq]; rw [h₂.aemeasurable_map_iff]

/--
theorem `quasiMeasurePreserving` / 定理 `quasiMeasurePreserving`

English:
theorem quasiMeasurePreserving
  given: {f : α -> β} (hf : MeasurePreserving f μa μb)
  proof: ⟨hf.1, hf.2.absolutelyContinuous⟩

中文:
定理 quasiMeasurePreserving
  条件: {f : α -> β} (hf : MeasurePreserving f μa μb)
  证明: ⟨hf.1, hf.2.absolutelyContinuous⟩
-/
protected theorem quasiMeasurePreserving {f : α -> β} (hf : MeasurePreserving f μa μb) :
    QuasiMeasurePreserving f μa μb :=
  ⟨hf.1, hf.2.absolutelyContinuous⟩

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {g : β -> γ} {f : α -> β} (hg : MeasurePreserving g μb μc)
  proof: ⟨hg.1.comp hf.1, by rw [← map_map hg.1 hf.1, hf.2, hg.2]⟩

中文:
定理 comp
  结论: {g : β -> γ} {f : α -> β} (hg : MeasurePreserving g μb μc)
  证明: ⟨hg.1.comp hf.1, by rw [← map_map hg.1 hf.1, hf.2, hg.2]⟩
-/
protected theorem comp {g : β -> γ} {f : α -> β} (hg : MeasurePreserving g μb μc)
    (hf : MeasurePreserving f μa μb) : MeasurePreserving (g ∘ f) μa μc :=
  ⟨hg.1.comp hf.1, by rw [← map_map hg.1 hf.1, hf.2, hg.2]⟩

/--
theorem `map_of_comp` / 定理 `map_of_comp`

English:
theorem map_of_comp
  statement: {f : α -> β} {g : β -> γ} (hgf : MeasurePreserving (g ∘ f) μa μc)
  proof: ⟨hg, (map_map hg hf).trans hgf.map_eq⟩

中文:
定理 map_of_comp
  结论: {f : α -> β} {g : β -> γ} (hgf : MeasurePreserving (g ∘ f) μa μc)
  证明: ⟨hg, (map_map hg hf).trans hgf.map_eq⟩
-/
protected theorem map_of_comp {f : α -> β} {g : β -> γ} (hgf : MeasurePreserving (g ∘ f) μa μc)
    (hg : Measurable g) (hf : Measurable f) :
    MeasurePreserving g (μa.map f) μc :=
  ⟨hg, (map_map hg hf).trans hgf.map_eq⟩

/--
theorem `of_semiconj` / 定理 `of_semiconj`

English:
theorem of_semiconj
  statement: {f : α -> β} {ga : α -> α} {gb : β -> β}
  proof: by
.map_of_comp hgb hfm.measurable have := hf.comp_eq ▸ hfm.comp hga
  rwa [hfm.map_eq] at this

中文:
定理 of_semiconj
  结论: {f : α -> β} {ga : α -> α} {gb : β -> β}
  证明: by
.map_of_comp hgb hfm.measurable have := hf.comp_eq ▸ hfm.comp hga
  rwa [hfm.map_eq] at this
-/
protected theorem of_semiconj {f : α -> β} {ga : α -> α} {gb : β -> β}
    (hfm : MeasurePreserving f μa μb) (hga : MeasurePreserving ga μa μa) (hf : Semiconj f ga gb)
    (hgb : Measurable gb) : MeasurePreserving gb μb μb := by
.map_of_comp hgb hfm.measurable have := hf.comp_eq ▸ hfm.comp hga
  rwa [hfm.map_eq] at this

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  statement: {e : α ≃ᵐ β} {e' : β ≃ᵐ γ}
  proof: h'.comp h

中文:
定理 trans
  结论: {e : α ≃ᵐ β} {e' : β ≃ᵐ γ}
  证明: h'.comp h
-/
protected theorem trans {e : α ≃ᵐ β} {e' : β ≃ᵐ γ}
    {μa : Measure α} {μb : Measure β} {μc : Measure γ}
    (h : MeasurePreserving e μa μb) (h' : MeasurePreserving e' μb μc) :
    MeasurePreserving (e.trans e') μa μc :=
  h'.comp h

/--
theorem `comp_left_iff` / 定理 `comp_left_iff`

English:
theorem comp_left_iff
  given: {g : α -> β} {e : β ≃ᵐ γ} (h : MeasurePreserving e μb μc)
  proof: by
  refine ⟨fun hg => ?_, fun hg => h.comp hg⟩
  convert! (MeasurePreserving.symm e h).comp hg
  simp [← Function.comp_assoc e.symm e g]

中文:
定理 comp_left_iff
  条件: {g : α -> β} {e : β ≃ᵐ γ} (h : MeasurePreserving e μb μc)
  证明: by
  refine ⟨fun hg => ?_, fun hg => h.comp hg⟩
  convert! (MeasurePreserving.symm e h).comp hg
  simp [← Function.comp_assoc e.symm e g]
-/
protected theorem comp_left_iff {g : α -> β} {e : β ≃ᵐ γ} (h : MeasurePreserving e μb μc) :
    MeasurePreserving (e ∘ g) μa μc ↔ MeasurePreserving g μa μb := by
  refine ⟨fun hg => ?_, fun hg => h.comp hg⟩
  convert! (MeasurePreserving.symm e h).comp hg
  simp [← Function.comp_assoc e.symm e g]

/--
theorem `comp_right_iff` / 定理 `comp_right_iff`

English:
theorem comp_right_iff
  given: {g : α -> β} {e : γ ≃ᵐ α} (h : MeasurePreserving e μc μa)
  proof: by
  refine ⟨fun hg => ?_, fun hg => hg.comp h⟩
  convert! hg.comp (MeasurePreserving.symm e h)
  simp [Function.comp_assoc g e e.symm]

中文:
定理 comp_right_iff
  条件: {g : α -> β} {e : γ ≃ᵐ α} (h : MeasurePreserving e μc μa)
  证明: by
  refine ⟨fun hg => ?_, fun hg => hg.comp h⟩
  convert! hg.comp (MeasurePreserving.symm e h)
  simp [Function.comp_assoc g e e.symm]
-/
protected theorem comp_right_iff {g : α -> β} {e : γ ≃ᵐ α} (h : MeasurePreserving e μc μa) :
    MeasurePreserving (g ∘ e) μc μb ↔ MeasurePreserving g μa μb := by
  refine ⟨fun hg => ?_, fun hg => hg.comp h⟩
  convert! hg.comp (MeasurePreserving.symm e h)
  simp [Function.comp_assoc g e e.symm]

/--
theorem `sigmaFinite` / 定理 `sigmaFinite`

English:
theorem sigmaFinite
  given: {f : α -> β} (hf : MeasurePreserving f μa μb) [SigmaFinite μb]
  proof: SigmaFinite.of_map μa hf.aemeasurable (by rwa [hf.map_eq])

中文:
定理 sigmaFinite
  条件: {f : α -> β} (hf : MeasurePreserving f μa μb) [SigmaFinite μb]
  证明: SigmaFinite.of_map μa hf.aemeasurable (by rwa [hf.map_eq])
-/
protected theorem sigmaFinite {f : α -> β} (hf : MeasurePreserving f μa μb) [SigmaFinite μb] :
    SigmaFinite μa :=
  SigmaFinite.of_map μa hf.aemeasurable (by rwa [hf.map_eq])

/--
theorem `sfinite` / 定理 `sfinite`

English:
theorem sfinite
  given: {f : α -> β} (hf : MeasurePreserving f μa μb) [SFinite μa]
  proof: by
  rw [← hf.map_eq]
  infer_instance

中文:
定理 sfinite
  条件: {f : α -> β} (hf : MeasurePreserving f μa μb) [SFinite μa]
  证明: by
  rw [← hf.map_eq]
  infer_instance
-/
protected theorem sfinite {f : α -> β} (hf : MeasurePreserving f μa μb) [SFinite μa] :
    SFinite μb := by
  rw [← hf.map_eq]
  infer_instance

/--
theorem `measure_preimage` / 定理 `measure_preimage`

English:
theorem measure_preimage
  statement: {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
  proof: by
  rw [← hf.map_eq] at hs ⊢
  rw [map_apply₀ hf.1.aemeasurable hs]

中文:
定理 measure_preimage
  结论: {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
  证明: by
  rw [← hf.map_eq] at hs ⊢
  rw [map_apply₀ hf.1.aemeasurable hs]

Depends on / 依赖: aemeasurable, hf.map_eq, map_eq
-/
theorem measure_preimage {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : NullMeasurableSet s μb) : μa (f ⁻¹' s) = μb s := by
  rw [← hf.map_eq] at hs ⊢
  rw [map_apply₀ hf.1.aemeasurable hs]

/--
theorem `measureReal_preimage` / 定理 `measureReal_preimage`

English:
theorem measureReal_preimage
  statement: {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
  proof: by
  simp [measureReal_def, measure_preimage hf hs]

中文:
定理 measureReal_preimage
  结论: {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
  证明: by
  simp [measureReal_def, measure_preimage hf hs]

Depends on / 依赖: measureReal_def, measure_preimage
-/
theorem measureReal_preimage {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : NullMeasurableSet s μb) : μa.real (f ⁻¹' s) = μb.real s := by
  simp [measureReal_def, measure_preimage hf hs]

/--
theorem `measure_preimage_emb` / 定理 `measure_preimage_emb`

English:
theorem measure_preimage_emb
  statement: {f : α -> β} (hf : MeasurePreserving f μa μb)
  proof: by
  rw [← hf.map_eq]; rw [hfe.map_apply]

中文:
定理 measure_preimage_emb
  结论: {f : α -> β} (hf : MeasurePreserving f μa μb)
  证明: by
  rw [← hf.map_eq]; rw [hfe.map_apply]

Depends on / 依赖: hf.map_eq, hfe.map_apply, map_apply, map_eq
-/
theorem measure_preimage_emb {f : α -> β} (hf : MeasurePreserving f μa μb)
    (hfe : MeasurableEmbedding f) (s : Set β) : μa (f ⁻¹' s) = μb s := by
  rw [← hf.map_eq]; rw [hfe.map_apply]

/--
theorem `measure_preimage_equiv` / 定理 `measure_preimage_equiv`

English:
theorem measure_preimage_equiv
  given: {f : α ≃ᵐ β} (hf : MeasurePreserving f μa μb) (s : Set β)
  proof: measure_preimage_emb hf f.measurableEmbedding s

中文:
定理 measure_preimage_equiv
  条件: {f : α ≃ᵐ β} (hf : MeasurePreserving f μa μb) (s : Set β)
  证明: measure_preimage_emb hf f.measurableEmbedding s

Depends on / 依赖: f.measurableEmbedding, measurableEmbedding, measure_preimage_emb
-/
theorem measure_preimage_equiv {f : α ≃ᵐ β} (hf : MeasurePreserving f μa μb) (s : Set β) :
    μa (f ⁻¹' s) = μb s :=
  measure_preimage_emb hf f.measurableEmbedding s

/--
theorem `measure_preimage_le` / 定理 `measure_preimage_le`

English:
theorem measure_preimage_le
  given: {f : α -> β} (hf : MeasurePreserving f μa μb) (s : Set β)
  proof: by
  rw [← hf.map_eq]
  exact le_map_apply hf.aemeasurable _

中文:
定理 measure_preimage_le
  条件: {f : α -> β} (hf : MeasurePreserving f μa μb) (s : Set β)
  证明: by
  rw [← hf.map_eq]
  exact le_map_apply hf.aemeasurable _

Depends on / 依赖: aemeasurable, hf.aemeasurable, hf.map_eq, le_map_apply, map_eq
-/
theorem measure_preimage_le {f : α -> β} (hf : MeasurePreserving f μa μb) (s : Set β) :
    μa (f ⁻¹' s) <= μb s := by
  rw [← hf.map_eq]
  exact le_map_apply hf.aemeasurable _

/--
theorem `preimage_null` / 定理 `preimage_null`

English:
theorem preimage_null
  statement: {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
  proof: hf.quasiMeasurePreserving.preimage_null hs

中文:
定理 preimage_null
  结论: {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
  证明: hf.quasiMeasurePreserving.preimage_null hs

Depends on / 依赖: hf.quasiMeasurePreserving.preimage_null, preimage_null, quasiMeasurePreserving
-/
theorem preimage_null {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : μb s = 0) : μa (f ⁻¹' s) = 0 :=
  hf.quasiMeasurePreserving.preimage_null hs

/--
theorem `aeconst_comp` / 定理 `aeconst_comp`

English:
theorem aeconst_comp
  statement: [MeasurableSingletonClass γ] {f : α -> β} (hf : MeasurePreserving f μa μb)
  proof: exists_congr fun s => and_congr_left fun hs => by
    simp only [Filter.mem_map, mem_ae_iff, ← hf.measure_preimage (hg hs.measurableSet).compl,
      preimage_comp, preimage_compl]

中文:
定理 aeconst_comp
  结论: [MeasurableSingletonClass γ] {f : α -> β} (hf : MeasurePreserving f μa μb)
  证明: exists_congr fun s => and_congr_left fun hs => by
    simp only [Filter.mem_map, mem_ae_iff, ← hf.measure_preimage (hg hs.measurableSet).compl,
      preimage_comp, preimage_compl]

Depends on / 依赖: Filter, Filter.mem_map, and_congr_left, exists_congr, hf.measure_preimage, hs.measurableSet, measurableSet, measure_preimage, mem_ae_iff, mem_map, preimage_comp, preimage_compl
-/
theorem aeconst_comp [MeasurableSingletonClass γ] {f : α -> β} (hf : MeasurePreserving f μa μb)
    {g : β -> γ} (hg : NullMeasurable g μb) :
    Filter.EventuallyConst (g ∘ f) (ae μa) ↔ Filter.EventuallyConst g (ae μb) :=
  exists_congr fun s => and_congr_left fun hs => by
    simp only [Filter.mem_map, mem_ae_iff, ← hf.measure_preimage (hg hs.measurableSet).compl,
      preimage_comp, preimage_compl]

/--
theorem `aeconst_preimage` / 定理 `aeconst_preimage`

English:
theorem aeconst_preimage
  statement: {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
  proof: aeconst_comp hf hs.mem

中文:
定理 aeconst_preimage
  结论: {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
  证明: aeconst_comp hf hs.mem

Depends on / 依赖: aeconst_comp, hs.mem
-/
theorem aeconst_preimage {f : α -> β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : NullMeasurableSet s μb) :
    Filter.EventuallyConst (f ⁻¹' s) (ae μa) ↔ Filter.EventuallyConst s (ae μb) :=
  aeconst_comp hf hs.mem

/--
theorem `add_measure` / 定理 `add_measure`

English:
theorem add_measure
  statement: {f μa' μb'} (hf : MeasurePreserving f μa μb)
  proof: hf.measurable
  map_eq := by rw [Measure.map_add _ _ hf.measurable, hf.map_eq, hf'.map_eq]

中文:
定理 add_measure
  结论: {f μa' μb'} (hf : MeasurePreserving f μa μb)
  证明: hf.measurable
  map_eq := by rw [Measure.map_add _ _ hf.measurable, hf.map_eq, hf'.map_eq]

Depends on / 依赖: hf.measurable, measurable
-/
theorem add_measure {f μa' μb'} (hf : MeasurePreserving f μa μb)
    (hf' : MeasurePreserving f μa' μb') : MeasurePreserving f (μa + μa') (μb + μb') where
  measurable := hf.measurable
  map_eq := by rw [Measure.map_add _ _ hf.measurable, hf.map_eq, hf'.map_eq]

/--
theorem `smul_measure` / 定理 `smul_measure`

English:
theorem smul_measure
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] {f : α -> β}
  proof: hf.measurable
  map_eq := by rw [Measure.map_smul, hf.map_eq]

中文:
定理 smul_measure
  结论: {R : 类型} [SMul R 实数>=0∞] [IsScalarTower R 实数>=0∞ 实数>=0∞] {f : α -> β}
  证明: hf.measurable
  map_eq := by rw [Measure.map_smul, hf.map_eq]

Depends on / 依赖: hf.measurable, measurable
-/
theorem smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] {f : α -> β}
    (hf : MeasurePreserving f μa μb) (c : R) : MeasurePreserving f (c • μa) (c • μb) where
  measurable := hf.measurable
  map_eq := by rw [Measure.map_smul, hf.map_eq]

variable {μ : Measure α} {f : α -> α} {s : Set α}

/--
theorem `iterate` / 定理 `iterate`

English:
theorem iterate
  given: (hf : MeasurePreserving f μ μ)

中文:
定理 iterate
  条件: (hf : MeasurePreserving f μ μ)

Depends on / 依赖: MulAction, toMulAction
-/
protected theorem iterate (hf : MeasurePreserving f μ μ) :
    forall n, MeasurePreserving f^[n] μ μ
  | 0 => .id μ
  | n + 1 => (MeasurePreserving.iterate hf n).comp hf

open scoped symmDiff in
/--
lemma `measure_symmDiff_preimage_iterate_le` / 引理 `measure_symmDiff_preimage_iterate_le`

English:
lemma measure_symmDiff_preimage_iterate_le
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [add_smul, one_smul]
    grw [← ih, measure_symmDiff_le s (f^[n] ⁻¹' s) (f^[n + 1] ⁻¹' s)]
    replace hs : NullMeasurableSet (s ∆ (f ⁻¹' s)) μ :=
hs.symmDiff hs.preimage hf.quasiMeasurePreserving
    rw [iterate_succ']; rw [preim

中文:
引理 measure_symmDiff_preimage_iterate_le
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [add_smul, one_smul]
    grw [← ih, measure_symmDiff_le s (f^[n] ⁻¹' s) (f^[n + 1] ⁻¹' s)]
    replace hs : NullMeasurableSet (s ∆ (f ⁻¹' s)) μ :=
hs.symmDiff hs.preimage hf.quasiMeasurePreserving
    rw [iterate_succ']; rw [preim

Depends on / 依赖: NullMeasurableSet, add_smul, hf.iterate, hf.quasiMeasurePreserving, hs.preimage, hs.symmDiff, iterate, iterate_succ, measure_preimage, measure_symmDiff_le, one_smul, preimage, preimage_comp, preimage_symmDiff, quasiMeasurePreserving, replace, symmDiff
-/
lemma measure_symmDiff_preimage_iterate_le
    (hf : MeasurePreserving f μ μ) (hs : NullMeasurableSet s μ) (n : Nat) :
    μ (s ∆ (f^[n] ⁻¹' s)) <= n • μ (s ∆ (f ⁻¹' s)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [add_smul, one_smul]
    grw [← ih, measure_symmDiff_le s (f^[n] ⁻¹' s) (f^[n + 1] ⁻¹' s)]
    replace hs : NullMeasurableSet (s ∆ (f ⁻¹' s)) μ :=
hs.symmDiff hs.preimage hf.quasiMeasurePreserving
    rw [iterate_succ']; rw [preimage_comp]; rw [← preimage_symmDiff]; rw [(hf.iterate n).measure_preimage hs]

/--
theorem `exists_mem_iterate_mem_of_measure_univ_lt_mul_measure` / 定理 `exists_mem_iterate_mem_of_measure_univ_lt_mul_measure`

English:
theorem exists_mem_iterate_mem_of_measure_univ_lt_mul_measure
  statement: (hf : MeasurePreserving f μ μ)
  proof: by
  have A : forall m, NullMeasurableSet (f^[m] ⁻¹' s) μ := fun m =>
    hs.preimage (hf.iterate m).quasiMeasurePreserving
  have B : forall m, μ (f^[m] ⁻¹' s) = μ s := fun m => (hf.iterate m).measure_preimage hs
  have : μ (univ : Set α) < ∑ m in Finset.range n, μ (f^[m] ⁻¹' s) := by simpa [B]
  o

中文:
定理 exists_mem_iterate_mem_of_measure_univ_lt_mul_measure
  结论: (hf : MeasurePreserving f μ μ)
  证明: by
  have A : forall m, NullMeasurableSet (f^[m] ⁻¹' s) μ := fun m =>
    hs.preimage (hf.iterate m).quasiMeasurePreserving
  have B : forall m, μ (f^[m] ⁻¹' s) = μ s := fun m => (hf.iterate m).measure_preimage hs
  have : μ (univ : Set α) < ∑ m in Finset.range n, μ (f^[m] ⁻¹' s) := by simpa [B]
  o

Depends on / 依赖: Finset, Finset.range, Nonempty, NullMeasurableSet, exists_nonempty_inter_of_measure_univ_lt_sum_, hf.iterate, hs.preimage, iterate, measure_preimage, preimage, quasiMeasurePreserving
-/
theorem exists_mem_iterate_mem_of_measure_univ_lt_mul_measure (hf : MeasurePreserving f μ μ)
    (hs : NullMeasurableSet s μ) {n : Nat} (hvol : μ (Set.univ : Set α) < n * μ s) :
    exists x in s, exists m in Set.Ioo 0 n, f^[m] x in s := by
  have A : forall m, NullMeasurableSet (f^[m] ⁻¹' s) μ := fun m =>
    hs.preimage (hf.iterate m).quasiMeasurePreserving
  have B : forall m, μ (f^[m] ⁻¹' s) = μ s := fun m => (hf.iterate m).measure_preimage hs
  have : μ (univ : Set α) < ∑ m in Finset.range n, μ (f^[m] ⁻¹' s) := by simpa [B]
  obtain ⟨i, hi, j, hj, hij, x, hxi : f^[i] x in s, hxj : f^[j] x in s⟩ :
      exists i < n, exists j < n, i != j ∧ (f^[i] ⁻¹' s inter f^[j] ⁻¹' s).Nonempty := by
    simpa using exists_nonempty_inter_of_measure_univ_lt_sum_measure μ (fun m _ => A m) this
  wlog hlt : i < j generalizing i j
  · exact this j hj i hi hij.symm hxj hxi (hij.lt_or_gt.resolve_left hlt)
  refine ⟨f^[i] x, hxi, j - i, ⟨tsub_pos_of_lt hlt, lt_of_le_of_lt (j.sub_le i) hj⟩, ?_⟩
  rwa [← iterate_add_apply, tsub_add_cancel_of_le hlt.le]

/--
theorem `exists_mem_iterate_mem` / 定理 `exists_mem_iterate_mem`

English:
theorem exists_mem_iterate_mem
  statement: [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ)
  proof: by
  rcases ENNReal.exists_nat_mul_gt hs' (measure_ne_top μ (Set.univ : Set α)) with ⟨N, hN⟩
  rcases hf.exists_mem_iterate_mem_of_measure_univ_lt_mul_measure hs hN with ⟨x, hx, m, hm, hmx⟩
  exact ⟨x, hx, m, hm.1.ne', hmx⟩

中文:
定理 exists_mem_iterate_mem
  结论: [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ)
  证明: by
  rcases ENNReal.exists_nat_mul_gt hs' (measure_ne_top μ (Set.univ : Set α)) with ⟨N, hN⟩
  rcases hf.exists_mem_iterate_mem_of_measure_univ_lt_mul_measure hs hN with ⟨x, hx, m, hm, hmx⟩
  exact ⟨x, hx, m, hm.1.ne', hmx⟩

Depends on / 依赖: ENNReal, ENNReal.exists_nat_mul_gt, Set.univ, exists_mem_iterate_mem_of_measure_univ_lt_mul_measure, exists_nat_mul_gt, hf.exists_mem_iterate_mem_of_measure_univ_lt_mul_measure, measure_ne_top
-/
theorem exists_mem_iterate_mem [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ)
    (hs : NullMeasurableSet s μ) (hs' : μ s != 0) : exists x in s, exists m != 0, f^[m] x in s := by
  rcases ENNReal.exists_nat_mul_gt hs' (measure_ne_top μ (Set.univ : Set α)) with ⟨N, hN⟩
  rcases hf.exists_mem_iterate_mem_of_measure_univ_lt_mul_measure hs hN with ⟨x, hx, m, hm, hmx⟩
  exact ⟨x, hx, m, hm.1.ne', hmx⟩

end MeasurePreserving

/--
lemma `measurePreserving_subtype_coe` / 引理 `measurePreserving_subtype_coe`

English:
lemma measurePreserving_subtype_coe
  given: {s : Set α} (hs : MeasurableSet s)
  proof: measurable_subtype_coe
  map_eq := map_comap_subtype_coe hs _

中文:
引理 measurePreserving_subtype_coe
  条件: {s : Set α} (hs : MeasurableSet s)
  证明: measurable_subtype_coe
  map_eq := map_comap_subtype_coe hs _

Depends on / 依赖: measurable_subtype_coe
-/
lemma measurePreserving_subtype_coe {s : Set α} (hs : MeasurableSet s) :
    MeasurePreserving (Subtype.val : s -> α) (μa.comap Subtype.val) (μa.restrict s) where
  measurable := measurable_subtype_coe
  map_eq := map_comap_subtype_coe hs _

namespace MeasurableEquiv

/--
theorem `measurePreserving_symm` / 定理 `measurePreserving_symm`

English:
theorem measurePreserving_symm
  given: (μ : Measure α) (e : α ≃ᵐ β)
  proof: (e.measurable.measurePreserving μ).symm _

中文:
定理 measurePreserving_symm
  条件: (μ : Measure α) (e : α ≃ᵐ β)
  证明: (e.measurable.measurePreserving μ).symm _

Depends on / 依赖: e.measurable.measurePreserving, measurable, measurePreserving
-/
theorem measurePreserving_symm (μ : Measure α) (e : α ≃ᵐ β) :
    MeasurePreserving e.symm (map e μ) μ :=
  (e.measurable.measurePreserving μ).symm _

end MeasurableEquiv

end MeasureTheory
