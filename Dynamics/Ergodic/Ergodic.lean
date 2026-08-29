/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Ergodic maps and measures

Let `f : α → α` be measure preserving with respect to a measure `μ`. We say `f` is ergodic with
respect to `μ` (or `μ` is ergodic with respect to `f`) if the only measurable sets `s` such that
`f⁻¹' s = s` are either almost empty or full.

In this file we define ergodic maps / measures together with quasi-ergodic maps / measures and
provide some basic API. Quasi-ergodicity is a weaker condition than ergodicity for which the measure
preserving condition is relaxed to quasi-measure-preserving.

## Main definitions

* `PreErgodic`: the ergodicity condition without the measure-preserving condition. This exists
  to share code between the `Ergodic` and `QuasiErgodic` definitions.
* `Ergodic`: the definition of ergodic maps / measures.
* `QuasiErgodic`: the definition of quasi-ergodic maps / measures.
* `Ergodic.quasiErgodic`: an ergodic map / measure is quasi-ergodic.
* `QuasiErgodic.ae_empty_or_univ'`: when the map is quasi-measure-preserving, one may relax the
  strict invariance condition to almost invariance in the ergodicity condition.

-/

public section

open Set Function Filter MeasureTheory MeasureTheory.Measure

open ENNReal

variable {α : Type*} {m : MeasurableSpace α} {s : Set α}

/--
Definition of `PreErgodic` / `PreErgodic` 的定义

English:
structure PreErgodic
  parameters: (f : α -> α) (μ : Measure α := by volume_tac)
  axioms and operations (1):
    - aeconst_set(⦃s) : Set α⦄ : MeasurableSet s -> f ⁻¹' s = s -> EventuallyConst s (ae μ)

中文:
结构 PreErgodic
  参数: (f : α -> α) (μ : Measure α := by volume_tac)
  公理与运算 (1 个):
    - aeconst_set(⦃s) : Set α⦄ : MeasurableSet s -> f ⁻¹' s = s -> EventuallyConst s (ae μ)

Depends on / 依赖: EventuallyConst, MeasurableSet, aeconst_set, volume_tac
-/
structure PreErgodic (f : α -> α) (μ : Measure α := by volume_tac) : Prop where
  aeconst_set ⦃s : Set α⦄ : MeasurableSet s -> f ⁻¹' s = s -> EventuallyConst s (ae μ)

/--
Definition of `Ergodic` / `Ergodic` 的定义

English:
structure Ergodic
  parameters: (f : α -> α) (μ : Measure α := by volume_tac)
  (no additional axioms)

中文:
结构 Ergodic
  参数: (f : α -> α) (μ : Measure α := by volume_tac)
  (无附加公理)

Depends on / 依赖: MeasurePreserving, PreErgodic, extends, volume_tac
-/
structure Ergodic (f : α -> α) (μ : Measure α := by volume_tac) : Prop extends
  MeasurePreserving f μ μ, PreErgodic f μ

/--
Definition of `QuasiErgodic` / `QuasiErgodic` 的定义

English:
structure QuasiErgodic
  parameters: (f : α -> α) (μ : Measure α := by volume_tac)
  (no additional axioms)

中文:
结构 QuasiErgodic
  参数: (f : α -> α) (μ : Measure α := by volume_tac)
  (无附加公理)

Depends on / 依赖: PreErgodic, QuasiMeasurePreserving, extends, volume_tac
-/
structure QuasiErgodic (f : α -> α) (μ : Measure α := by volume_tac) : Prop extends
  QuasiMeasurePreserving f μ μ, PreErgodic f μ

variable {f : α -> α} {μ : Measure α}

namespace PreErgodic

/--
theorem `ae_empty_or_univ` / 定理 `ae_empty_or_univ`

English:
theorem ae_empty_or_univ
  given: (hf : PreErgodic f μ) (hs : MeasurableSet s) (hfs : f ⁻¹' s = s)
  proof: by
  simpa only [eventuallyConst_set'] using hf.aeconst_set hs hfs

中文:
定理 ae_empty_or_univ
  条件: (hf : PreErgodic f μ) (hs : MeasurableSet s) (hfs : f ⁻¹' s = s)
  证明: by
  simpa only [eventuallyConst_set'] using hf.aeconst_set hs hfs

Depends on / 依赖: aeconst_set, eventuallyConst_set, hf.aeconst_set
-/
theorem ae_empty_or_univ (hf : PreErgodic f μ) (hs : MeasurableSet s) (hfs : f ⁻¹' s = s) :
    s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  simpa only [eventuallyConst_set'] using hf.aeconst_set hs hfs

/--
theorem `measure_self_or_compl_eq_zero` / 定理 `measure_self_or_compl_eq_zero`

English:
theorem measure_self_or_compl_eq_zero
  statement: (hf : PreErgodic f μ) (hs : MeasurableSet s)
  proof: by
  simpa using hf.ae_empty_or_univ hs hs'

中文:
定理 measure_self_or_compl_eq_zero
  结论: (hf : PreErgodic f μ) (hs : MeasurableSet s)
  证明: by
  simpa using hf.ae_empty_or_univ hs hs'

Depends on / 依赖: ae_empty_or_univ, hf.ae_empty_or_univ
-/
theorem measure_self_or_compl_eq_zero (hf : PreErgodic f μ) (hs : MeasurableSet s)
    (hs' : f ⁻¹' s = s) : μ s = 0 ∨ μ sᶜ = 0 := by
  simpa using hf.ae_empty_or_univ hs hs'

/--
theorem `ae_mem_or_ae_notMem` / 定理 `ae_mem_or_ae_notMem`

English:
theorem ae_mem_or_ae_notMem
  given: (hf : PreErgodic f μ) (hsm : MeasurableSet s) (hs : f ⁻¹' s = s)
  proof: eventuallyConst_set.1 hf.aeconst_set hsm hs

中文:
定理 ae_mem_or_ae_notMem
  条件: (hf : PreErgodic f μ) (hsm : MeasurableSet s) (hs : f ⁻¹' s = s)
  证明: eventuallyConst_set.1 hf.aeconst_set hsm hs

Depends on / 依赖: aeconst_set, eventuallyConst_set, hf.aeconst_set
-/
theorem ae_mem_or_ae_notMem (hf : PreErgodic f μ) (hsm : MeasurableSet s) (hs : f ⁻¹' s = s) :
    (forallᵐ x ∂μ, x in s) ∨ forallᵐ x ∂μ, x ∉ s :=
eventuallyConst_set.1 hf.aeconst_set hsm hs

/--
theorem `prob_eq_zero_or_one` / 定理 `prob_eq_zero_or_one`

English:
theorem prob_eq_zero_or_one
  statement: [IsProbabilityMeasure μ] (hf : PreErgodic f μ) (hs : MeasurableSet s)
  proof: by
  simpa [hs] using hf.measure_self_or_compl_eq_zero hs hs'

中文:
定理 prob_eq_zero_or_one
  结论: [IsProbabilityMeasure μ] (hf : PreErgodic f μ) (hs : MeasurableSet s)
  证明: by
  simpa [hs] using hf.measure_self_or_compl_eq_zero hs hs'

Depends on / 依赖: hf.measure_self_or_compl_eq_zero, measure_self_or_compl_eq_zero
-/
theorem prob_eq_zero_or_one [IsProbabilityMeasure μ] (hf : PreErgodic f μ) (hs : MeasurableSet s)
    (hs' : f ⁻¹' s = s) : μ s = 0 ∨ μ s = 1 := by
  simpa [hs] using hf.measure_self_or_compl_eq_zero hs hs'

/--
theorem `of_iterate` / 定理 `of_iterate`

English:
theorem of_iterate
  given: (n : Nat) (hf : PreErgodic f^[n] μ)
  statement: PreErgodic f μ
  proof: ⟨fun _ hs hs' => hf.aeconst_set hs IsFixedPt.preimage_iterate hs' n⟩

中文:
定理 of_iterate
  条件: (n : 自然数) (hf : PreErgodic f^[n] μ)
  结论: PreErgodic f μ
  证明: ⟨fun _ hs hs' => hf.aeconst_set hs IsFixedPt.preimage_iterate hs' n⟩

Depends on / 依赖: IsFixedPt, IsFixedPt.preimage_iterate, aeconst_set, hf.aeconst_set, preimage_iterate
-/
theorem of_iterate (n : Nat) (hf : PreErgodic f^[n] μ) : PreErgodic f μ :=
⟨fun _ hs hs' => hf.aeconst_set hs IsFixedPt.preimage_iterate hs' n⟩

/--
theorem `smul_measure` / 定理 `smul_measure`

English:
theorem smul_measure
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: (hf.aeconst_set hs hfs).anti ae_smul_measure_le _

中文:
定理 smul_measure
  结论: {R : 类型} [SMul R 实数>=0∞] [IsScalarTower R 实数>=0∞ 实数>=0∞]
  证明: (hf.aeconst_set hs hfs).anti ae_smul_measure_le _

Depends on / 依赖: ae_smul_measure_le, aeconst_set, hf.aeconst_set
-/
theorem smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    (hf : PreErgodic f μ) (c : R) : PreErgodic f (c • μ) where
aeconst_set _s hs hfs := (hf.aeconst_set hs hfs).anti ae_smul_measure_le _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `zero_measure` / 定理 `zero_measure`

English:
theorem zero_measure
  given: (f : α -> α)
  statement: @PreErgodic α m f 0 where
  proof: by simp

中文:
定理 zero_measure
  条件: (f : α -> α)
  结论: @PreErgodic α m f 0 where
  证明: by simp
-/
theorem zero_measure (f : α -> α) : @PreErgodic α m f 0 where
  aeconst_set _ _ _ := by simp

end PreErgodic

namespace MeasureTheory.MeasurePreserving

variable {β : Type*} {m' : MeasurableSpace β} {μ' : Measure β} {g : α -> β}

/--
theorem `preErgodic_of_preErgodic_semiconj` / 定理 `preErgodic_of_preErgodic_semiconj`

English:
theorem preErgodic_of_preErgodic_semiconj
  statement: (hg : MeasurePreserving g μ μ') (hf : PreErgodic f μ)
  proof: by
    rw [← hg.aeconst_preimage hs₀.nullMeasurableSet]
    apply hf.aeconst_set (hg.measurable hs₀)
    rw [← preimage_comp]; rw [h_comm.comp_eq]; rw [preimage_comp]; rw [hs₁]

中文:
定理 preErgodic_of_preErgodic_semiconj
  结论: (hg : MeasurePreserving g μ μ') (hf : PreErgodic f μ)
  证明: by
    rw [← hg.aeconst_preimage hs₀.nullMeasurableSet]
    apply hf.aeconst_set (hg.measurable hs₀)
    rw [← preimage_comp]; rw [h_comm.comp_eq]; rw [preimage_comp]; rw [hs₁]

Depends on / 依赖: aeconst_preimage, aeconst_set, comp_eq, h_comm, h_comm.comp_eq, hf.aeconst_set, hg.aeconst_preimage, hg.measurable, measurable, nullMeasurableSet, preimage_comp
-/
theorem preErgodic_of_preErgodic_semiconj (hg : MeasurePreserving g μ μ') (hf : PreErgodic f μ)
    {f' : β -> β} (h_comm : Semiconj g f f') : PreErgodic f' μ' where
  aeconst_set s hs₀ hs₁ := by
    rw [← hg.aeconst_preimage hs₀.nullMeasurableSet]
    apply hf.aeconst_set (hg.measurable hs₀)
    rw [← preimage_comp]; rw [h_comm.comp_eq]; rw [preimage_comp]; rw [hs₁]

/--
theorem `ergodic_of_ergodic_semiconj` / 定理 `ergodic_of_ergodic_semiconj`

English:
theorem ergodic_of_ergodic_semiconj
  statement: (hg : MeasurePreserving g μ μ') (hf : Ergodic f μ)
  proof: ⟨hg.of_semiconj hf.toMeasurePreserving h_comm hf',
   hg.preErgodic_of_preErgodic_semiconj hf.toPreErgodic h_comm⟩

中文:
定理 ergodic_of_ergodic_semiconj
  结论: (hg : MeasurePreserving g μ μ') (hf : Ergodic f μ)
  证明: ⟨hg.of_semiconj hf.toMeasurePreserving h_comm hf',
   hg.preErgodic_of_preErgodic_semiconj hf.toPreErgodic h_comm⟩

Depends on / 依赖: h_comm, hf.toMeasurePreserving, hf.toPreErgodic, hg.of_semiconj, hg.preErgodic_of_preErgodic_semiconj, of_semiconj, preErgodic_of_preErgodic_semiconj, toMeasurePreserving, toPreErgodic
-/
theorem ergodic_of_ergodic_semiconj (hg : MeasurePreserving g μ μ') (hf : Ergodic f μ)
    {f' : β -> β} (hf' : Measurable f') (h_comm : Semiconj g f f') : Ergodic f' μ' :=
  ⟨hg.of_semiconj hf.toMeasurePreserving h_comm hf',
   hg.preErgodic_of_preErgodic_semiconj hf.toPreErgodic h_comm⟩

/--
theorem `preErgodic_conjugate_iff` / 定理 `preErgodic_conjugate_iff`

English:
theorem preErgodic_conjugate_iff
  given: {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ')
  proof: by
  refine ⟨fun hf => preErgodic_of_preErgodic_semiconj (h.symm e) hf ?_,
      fun hf => preErgodic_of_preErgodic_semiconj h hf ?_⟩
  · simp [Semiconj]
  · simp [Semiconj]

中文:
定理 preErgodic_conjugate_iff
  条件: {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ')
  证明: by
  refine ⟨fun hf => preErgodic_of_preErgodic_semiconj (h.symm e) hf ?_,
      fun hf => preErgodic_of_preErgodic_semiconj h hf ?_⟩
  · simp [Semiconj]
  · simp [Semiconj]

Depends on / 依赖: Semiconj, h.symm, preErgodic_of_preErgodic_semiconj
-/
theorem preErgodic_conjugate_iff {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ') :
    PreErgodic (e ∘ f ∘ e.symm) μ' ↔ PreErgodic f μ := by
  refine ⟨fun hf => preErgodic_of_preErgodic_semiconj (h.symm e) hf ?_,
      fun hf => preErgodic_of_preErgodic_semiconj h hf ?_⟩
  · simp [Semiconj]
  · simp [Semiconj]

/--
theorem `ergodic_conjugate_iff` / 定理 `ergodic_conjugate_iff`

English:
theorem ergodic_conjugate_iff
  given: {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ')
  proof: by
  have : MeasurePreserving (e ∘ f ∘ e.symm) μ' μ' ↔ MeasurePreserving f μ μ := by
    rw [h.comp_left_iff]; rw [(MeasurePreserving.symm e h).comp_right_iff]
  replace h : PreErgodic (e ∘ f ∘ e.symm) μ' ↔ PreErgodic f μ := h.preErgodic_conjugate_iff
  exact ⟨fun hf => { this.mp hf.toMeasurePreserv

中文:
定理 ergodic_conjugate_iff
  条件: {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ')
  证明: by
  have : MeasurePreserving (e ∘ f ∘ e.symm) μ' μ' ↔ MeasurePreserving f μ μ := by
    rw [h.comp_left_iff]; rw [(MeasurePreserving.symm e h).comp_right_iff]
  replace h : PreErgodic (e ∘ f ∘ e.symm) μ' ↔ PreErgodic f μ := h.preErgodic_conjugate_iff
  exact ⟨fun hf => { this.mp hf.toMeasurePreserv

Depends on / 依赖: MeasurePreserving, MeasurePreserving.symm, PreErgodic, comp_left_iff, comp_right_iff, e.symm, h.comp_left_iff, h.mp, h.mpr, h.preErgodic_conjugate_iff, hf.toMeasurePreserving, hf.toPreErgodic, preErgodic_conjugate_iff, replace, this.mp, this.mpr, toMeasurePreserving, toPreErgodic
-/
theorem ergodic_conjugate_iff {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ') :
    Ergodic (e ∘ f ∘ e.symm) μ' ↔ Ergodic f μ := by
  have : MeasurePreserving (e ∘ f ∘ e.symm) μ' μ' ↔ MeasurePreserving f μ μ := by
    rw [h.comp_left_iff]; rw [(MeasurePreserving.symm e h).comp_right_iff]
  replace h : PreErgodic (e ∘ f ∘ e.symm) μ' ↔ PreErgodic f μ := h.preErgodic_conjugate_iff
  exact ⟨fun hf => { this.mp hf.toMeasurePreserving, h.mp hf.toPreErgodic with },
    fun hf => { this.mpr hf.toMeasurePreserving, h.mpr hf.toPreErgodic with }⟩

end MeasureTheory.MeasurePreserving

namespace QuasiErgodic

/--
theorem `aeconst_set₀` / 定理 `aeconst_set₀`

English:
theorem aeconst_set₀
  given: (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ) (hs : f ⁻¹' s =ᵐ[μ] s)
  proof: let ⟨_t, h₀, h₁, h₂⟩ := hf.toQuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae hsm hs
  (hf.aeconst_set h₀ h₂).congr h₁

中文:
定理 aeconst_set₀
  条件: (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ) (hs : f ⁻¹' s =ᵐ[μ] s)
  证明: let ⟨_t, h₀, h₁, h₂⟩ := hf.toQuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae hsm hs
  (hf.aeconst_set h₀ h₂).congr h₁

Depends on / 依赖: aeconst_set, exists_preimage_eq_of_preimage_ae, hf.aeconst_set, hf.toQuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae, toQuasiMeasurePreserving
-/
theorem aeconst_set₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ) (hs : f ⁻¹' s =ᵐ[μ] s) :
    EventuallyConst s (ae μ) :=
  let ⟨_t, h₀, h₁, h₂⟩ := hf.toQuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae hsm hs
  (hf.aeconst_set h₀ h₂).congr h₁

/--
theorem `ae_empty_or_univ₀` / 定理 `ae_empty_or_univ₀`

English:
theorem ae_empty_or_univ₀
  statement: (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ)
  proof: eventuallyConst_set'.mp hf.aeconst_set₀ hsm hs

中文:
定理 ae_empty_or_univ₀
  结论: (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ)
  证明: eventuallyConst_set'.mp hf.aeconst_set₀ hsm hs

Depends on / 依赖: eventuallyConst_set, hf.aeconst_set
-/
theorem ae_empty_or_univ₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) :
    s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
eventuallyConst_set'.mp hf.aeconst_set₀ hsm hs

/--
theorem `ae_mem_or_ae_notMem₀` / 定理 `ae_mem_or_ae_notMem₀`

English:
theorem ae_mem_or_ae_notMem₀
  statement: (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ)
  proof: eventuallyConst_set.mp hf.aeconst_set₀ hsm hs

中文:
定理 ae_mem_or_ae_notMem₀
  结论: (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ)
  证明: eventuallyConst_set.mp hf.aeconst_set₀ hsm hs

Depends on / 依赖: eventuallyConst_set, eventuallyConst_set.mp, hf.aeconst_set
-/
theorem ae_mem_or_ae_notMem₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) :
    (forallᵐ x ∂μ, x in s) ∨ forallᵐ x ∂μ, x ∉ s :=
eventuallyConst_set.mp hf.aeconst_set₀ hsm hs

/--
theorem `smul_measure` / 定理 `smul_measure`

English:
theorem smul_measure
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: ⟨hf.1.smul_measure _, hf.2.smul_measure _⟩

中文:
定理 smul_measure
  结论: {R : 类型} [SMul R 实数>=0∞] [IsScalarTower R 实数>=0∞ 实数>=0∞]
  证明: ⟨hf.1.smul_measure _, hf.2.smul_measure _⟩

Depends on / 依赖: smul_measure
-/
theorem smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    (hf : QuasiErgodic f μ) (c : R) : QuasiErgodic f (c • μ) :=
  ⟨hf.1.smul_measure _, hf.2.smul_measure _⟩

/--
theorem `zero_measure` / 定理 `zero_measure`

English:
theorem zero_measure
  given: {f : α -> α} (hf : Measurable f)
  statement: @QuasiErgodic α m f 0 where
  proof: hf
  absolutelyContinuous := by simp
  toPreErgodic := .zero_measure f

中文:
定理 zero_measure
  条件: {f : α -> α} (hf : Measurable f)
  结论: @QuasiErgodic α m f 0 where
  证明: hf
  absolutelyContinuous := by simp
  toPreErgodic := .zero_measure f
-/
theorem zero_measure {f : α -> α} (hf : Measurable f) : @QuasiErgodic α m f 0 where
  measurable := hf
  absolutelyContinuous := by simp
  toPreErgodic := .zero_measure f

end QuasiErgodic

namespace Ergodic

/--
theorem `quasiErgodic` / 定理 `quasiErgodic`

English:
theorem quasiErgodic
  given: (hf : Ergodic f μ)
  statement: QuasiErgodic f μ
  proof: { hf.toPreErgodic, hf.toMeasurePreserving.quasiMeasurePreserving with }

中文:
定理 quasiErgodic
  条件: (hf : Ergodic f μ)
  结论: QuasiErgodic f μ
  证明: { hf.toPreErgodic, hf.toMeasurePreserving.quasiMeasurePreserving with }

Depends on / 依赖: hf.toMeasurePreserving.quasiMeasurePreserving, hf.toPreErgodic, quasiMeasurePreserving, toMeasurePreserving, toPreErgodic
-/
theorem quasiErgodic (hf : Ergodic f μ) : QuasiErgodic f μ :=
  { hf.toPreErgodic, hf.toMeasurePreserving.quasiMeasurePreserving with }

/--
theorem `ae_empty_or_univ_of_preimage_ae_le'` / 定理 `ae_empty_or_univ_of_preimage_ae_le'`

English:
theorem ae_empty_or_univ_of_preimage_ae_le'
  statement: (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
  proof: by
  refine hf.quasiErgodic.ae_empty_or_univ₀ hs ?_
  refine ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).ge ?_ h_fin
  exact hs.preimage hf.quasiMeasurePreserving

中文:
定理 ae_empty_or_univ_of_preimage_ae_le'
  结论: (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
  证明: by
  refine hf.quasiErgodic.ae_empty_or_univ₀ hs ?_
  refine ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).ge ?_ h_fin
  exact hs.preimage hf.quasiMeasurePreserving

Depends on / 依赖: ae_eq_of_ae_subset_of_measure_ge, h_fin, hf.measure_preimage, hf.quasiErgodic.ae_empty_or_univ, hf.quasiMeasurePreserving, hs.preimage, measure_preimage, preimage, quasiErgodic, quasiMeasurePreserving
-/
theorem ae_empty_or_univ_of_preimage_ae_le' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f ⁻¹' s <=ᵐ[μ] s) (h_fin : μ s != ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  refine hf.quasiErgodic.ae_empty_or_univ₀ hs ?_
  refine ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).ge ?_ h_fin
  exact hs.preimage hf.quasiMeasurePreserving

/--
theorem `ae_empty_or_univ_of_ae_le_preimage'` / 定理 `ae_empty_or_univ_of_ae_le_preimage'`

English:
theorem ae_empty_or_univ_of_ae_le_preimage'
  statement: (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
  proof: by
  replace h_fin : μ (f ⁻¹' s) != ∞ := by rwa [hf.measure_preimage hs]
  refine hf.quasiErgodic.ae_empty_or_univ₀ hs ?_
  exact (ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).le hs h_fin).symm

中文:
定理 ae_empty_or_univ_of_ae_le_preimage'
  结论: (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
  证明: by
  replace h_fin : μ (f ⁻¹' s) != ∞ := by rwa [hf.measure_preimage hs]
  refine hf.quasiErgodic.ae_empty_or_univ₀ hs ?_
  exact (ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).le hs h_fin).symm

Depends on / 依赖: ae_eq_of_ae_subset_of_measure_ge, h_fin, hf.measure_preimage, hf.quasiErgodic.ae_empty_or_univ, measure_preimage, quasiErgodic, replace
-/
theorem ae_empty_or_univ_of_ae_le_preimage' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : s <=ᵐ[μ] f ⁻¹' s) (h_fin : μ s != ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  replace h_fin : μ (f ⁻¹' s) != ∞ := by rwa [hf.measure_preimage hs]
  refine hf.quasiErgodic.ae_empty_or_univ₀ hs ?_
  exact (ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).le hs h_fin).symm

/--
theorem `ae_empty_or_univ_of_image_ae_le'` / 定理 `ae_empty_or_univ_of_image_ae_le'`

English:
theorem ae_empty_or_univ_of_image_ae_le'
  statement: (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
  proof: by
  replace hs' : s <=ᵐ[μ] f ⁻¹' s :=
    (LE.le.eventuallyLE (subset_preimage_image f s)).trans
      (hf.quasiMeasurePreserving.preimage_mono_ae hs')
  exact ae_empty_or_univ_of_ae_le_preimage' hf hs hs' h_fin

中文:
定理 ae_empty_or_univ_of_image_ae_le'
  结论: (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
  证明: by
  replace hs' : s <=ᵐ[μ] f ⁻¹' s :=
    (LE.le.eventuallyLE (subset_preimage_image f s)).trans
      (hf.quasiMeasurePreserving.preimage_mono_ae hs')
  exact ae_empty_or_univ_of_ae_le_preimage' hf hs hs' h_fin

Depends on / 依赖: LE.le.eventuallyLE, ae_empty_or_univ_of_ae_le_preimage, eventuallyLE, h_fin, hf.quasiMeasurePreserving.preimage_mono_ae, preimage_mono_ae, quasiMeasurePreserving, replace, subset_preimage_image
-/
theorem ae_empty_or_univ_of_image_ae_le' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f '' s <=ᵐ[μ] s) (h_fin : μ s != ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  replace hs' : s <=ᵐ[μ] f ⁻¹' s :=
    (LE.le.eventuallyLE (subset_preimage_image f s)).trans
      (hf.quasiMeasurePreserving.preimage_mono_ae hs')
  exact ae_empty_or_univ_of_ae_le_preimage' hf hs hs' h_fin

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: {e : α ≃ᵐ α} (he : Ergodic e μ)
  statement: Ergodic e.symm μ where
  proof: he.toMeasurePreserving.symm
aeconst_set s hsm hs := he.aeconst_set hsm by
    conv_lhs => rw [← hs, ← e.image_eq_preimage_symm, e.preimage_image]

中文:
定理 symm
  条件: {e : α ≃ᵐ α} (he : Ergodic e μ)
  结论: Ergodic e.symm μ where
  证明: he.toMeasurePreserving.symm
aeconst_set s hsm hs := he.aeconst_set hsm by
    conv_lhs => rw [← hs, ← e.image_eq_preimage_symm, e.preimage_image]

Depends on / 依赖: he.toMeasurePreserving.symm, toMeasurePreserving
-/
theorem symm {e : α ≃ᵐ α} (he : Ergodic e μ) : Ergodic e.symm μ where
  toMeasurePreserving := he.toMeasurePreserving.symm
aeconst_set s hsm hs := he.aeconst_set hsm by
    conv_lhs => rw [← hs, ← e.image_eq_preimage_symm, e.preimage_image]

/--
theorem `symm_iff` / 定理 `symm_iff`

English:
theorem symm_iff
  given: {e : α ≃ᵐ α}
  statement: Ergodic e.symm μ ↔ Ergodic e μ
  proof: ⟨.symm, .symm⟩

中文:
定理 symm_iff
  条件: {e : α ≃ᵐ α}
  结论: Ergodic e.symm μ ↔ Ergodic e μ
  证明: ⟨.symm, .symm⟩
-/
@[simp] theorem symm_iff {e : α ≃ᵐ α} : Ergodic e.symm μ ↔ Ergodic e μ := ⟨.symm, .symm⟩

/--
theorem `smul_measure` / 定理 `smul_measure`

English:
theorem smul_measure
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: ⟨hf.1.smul_measure _, hf.2.smul_measure _⟩

中文:
定理 smul_measure
  结论: {R : 类型} [SMul R 实数>=0∞] [IsScalarTower R 实数>=0∞ 实数>=0∞]
  证明: ⟨hf.1.smul_measure _, hf.2.smul_measure _⟩

Depends on / 依赖: smul_measure
-/
theorem smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    (hf : Ergodic f μ) (c : R) : Ergodic f (c • μ) :=
  ⟨hf.1.smul_measure _, hf.2.smul_measure _⟩

/--
theorem `zero_measure` / 定理 `zero_measure`

English:
theorem zero_measure
  given: {f : α -> α} (hf : Measurable f)
  statement: @Ergodic α m f 0 where
  proof: hf
  map_eq := by simp
  toPreErgodic := .zero_measure f

中文:
定理 zero_measure
  条件: {f : α -> α} (hf : Measurable f)
  结论: @Ergodic α m f 0 where
  证明: hf
  map_eq := by simp
  toPreErgodic := .zero_measure f
-/
theorem zero_measure {f : α -> α} (hf : Measurable f) : @Ergodic α m f 0 where
  measurable := hf
  map_eq := by simp
  toPreErgodic := .zero_measure f

section IsFiniteMeasure

variable [IsFiniteMeasure μ]

/--
theorem `ae_empty_or_univ_of_preimage_ae_le` / 定理 `ae_empty_or_univ_of_preimage_ae_le`

English:
theorem ae_empty_or_univ_of_preimage_ae_le
  statement: (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
  proof: ae_empty_or_univ_of_preimage_ae_le' hf hs hs' measure_ne_top μ s

中文:
定理 ae_empty_or_univ_of_preimage_ae_le
  结论: (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
  证明: ae_empty_or_univ_of_preimage_ae_le' hf hs hs' measure_ne_top μ s

Depends on / 依赖: ae_empty_or_univ_of_preimage_ae_le, measure_ne_top
-/
theorem ae_empty_or_univ_of_preimage_ae_le (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f ⁻¹' s <=ᵐ[μ] s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
ae_empty_or_univ_of_preimage_ae_le' hf hs hs' measure_ne_top μ s

/--
theorem `ae_empty_or_univ_of_ae_le_preimage` / 定理 `ae_empty_or_univ_of_ae_le_preimage`

English:
theorem ae_empty_or_univ_of_ae_le_preimage
  statement: (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
  proof: ae_empty_or_univ_of_ae_le_preimage' hf hs hs' measure_ne_top μ s

中文:
定理 ae_empty_or_univ_of_ae_le_preimage
  结论: (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
  证明: ae_empty_or_univ_of_ae_le_preimage' hf hs hs' measure_ne_top μ s

Depends on / 依赖: ae_empty_or_univ_of_ae_le_preimage, measure_ne_top
-/
theorem ae_empty_or_univ_of_ae_le_preimage (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : s <=ᵐ[μ] f ⁻¹' s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
ae_empty_or_univ_of_ae_le_preimage' hf hs hs' measure_ne_top μ s

/--
theorem `ae_empty_or_univ_of_image_ae_le` / 定理 `ae_empty_or_univ_of_image_ae_le`

English:
theorem ae_empty_or_univ_of_image_ae_le
  statement: (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
  proof: ae_empty_or_univ_of_image_ae_le' hf hs hs' measure_ne_top μ s

中文:
定理 ae_empty_or_univ_of_image_ae_le
  结论: (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
  证明: ae_empty_or_univ_of_image_ae_le' hf hs hs' measure_ne_top μ s

Depends on / 依赖: ae_empty_or_univ_of_image_ae_le, measure_ne_top
-/
theorem ae_empty_or_univ_of_image_ae_le (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f '' s <=ᵐ[μ] s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
ae_empty_or_univ_of_image_ae_le' hf hs hs' measure_ne_top μ s

end IsFiniteMeasure

end Ergodic
