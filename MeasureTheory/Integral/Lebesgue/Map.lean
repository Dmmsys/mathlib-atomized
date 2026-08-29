/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Behavior of the Lebesgue integral under maps
-/

public section

namespace MeasureTheory

open Set Filter ENNReal SimpleFunc

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

section Map

open Measure

/--
theorem `lintegral_map` / 定理 `lintegral_map`

English:
theorem lintegral_map
  statement: {f : β -> Real>=0∞} {g : α -> β} (hf : Measurable f)
  proof: by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  simp only [← Function.comp_apply (f := f) (g := g)]
  rw [lintegral_eq_iSup_eapprox_lintegral (hf.comp hg)]
  congr with n : 1
  convert! SimpleFunc.lintegral_map _ hg
  ext1 x; simp only [eapprox_comp hf hg, coe_comp]

中文:
定理 lintegral_map
  结论: {f : β -> 实数>=0∞} {g : α -> β} (hf : 可测 f)
  证明: by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  simp only [← Function.comp_apply (f := f) (g := g)]
  rw [lintegral_eq_iSup_eapprox_lintegral (hf.comp hg)]
  congr with n : 1
  convert! SimpleFunc.lintegral_map _ hg
  ext1 x; simp only [eapprox_comp hf hg, coe_comp]

Depends on / 依赖: Function, Function.comp_apply, SimpleFunc, SimpleFunc.lintegral_map, coe_comp, comp_apply, convert, eapprox_comp, hf.comp, lintegral_eq_iSup_eapprox_lintegral, lintegral_map
-/
theorem lintegral_map {f : β -> Real>=0∞} {g : α -> β} (hf : Measurable f)
    (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  simp only [← Function.comp_apply (f := f) (g := g)]
  rw [lintegral_eq_iSup_eapprox_lintegral (hf.comp hg)]
  congr with n : 1
  convert! SimpleFunc.lintegral_map _ hg
  ext1 x; simp only [eapprox_comp hf hg, coe_comp]

/--
theorem `lintegral_map'` / 定理 `lintegral_map'`

English:
theorem lintegral_map'
  statement: {f : β -> Real>=0∞} {g : α -> β}
  proof: calc
    ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, hf.mk f a ∂Measure.map g μ :=
      lintegral_congr_ae hf.ae_eq_mk
    _ = ∫⁻ a, hf.mk f a ∂Measure.map (hg.mk g) μ := by
      congr 1
      exact Measure.map_congr hg.ae_eq_mk
    _ = ∫⁻ a, hf.mk f (hg.mk g a) ∂μ := lintegral_map hf.measurable_mk hg.measurable_mk
_ = ∫⁻ a, hf.mk f (g a) ∂μ := lintegral_congr_ae hg.ae_eq_mk.symm.fun_comp _
    _ = ∫⁻ a, f (g a) ∂μ := lintegral_congr_ae (ae_eq_comp hg hf.ae_eq_mk.symm)

中文:
定理 lintegral_map'
  结论: {f : β -> 实数>=0∞} {g : α -> β}
  证明: calc
    ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, hf.mk f a ∂Measure.map g μ :=
      lintegral_congr_ae hf.ae_eq_mk
    _ = ∫⁻ a, hf.mk f a ∂Measure.map (hg.mk g) μ := by
      congr 1
      exact Measure.map_congr hg.ae_eq_mk
    _ = ∫⁻ a, hf.mk f (hg.mk g a) ∂μ := lintegral_map hf.measurable_mk hg.measurable_mk
_ = ∫⁻ a, hf.mk f (g a) ∂μ := lintegral_congr_ae hg.ae_eq_mk.symm.fun_comp _
    _ = ∫⁻ a, f (g a) ∂μ := lintegral_congr_ae (ae_eq_comp hg hf.ae_eq_mk.symm)

Depends on / 依赖: Measure, Measure.map, Measure.map_congr, ae_eq_comp, ae_eq_mk, fun_comp, hf.ae_eq_mk, hf.ae_eq_mk.symm, hf.measurable_mk, hf.mk, hg.ae_eq_mk, hg.ae_eq_mk.symm.fun_comp, hg.measurable_mk, hg.mk, lintegral_congr_ae, lintegral_map, map_congr, measurable_mk
-/
theorem lintegral_map' {f : β -> Real>=0∞} {g : α -> β}
    (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, f (g a) ∂μ :=
  calc
    ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, hf.mk f a ∂Measure.map g μ :=
      lintegral_congr_ae hf.ae_eq_mk
    _ = ∫⁻ a, hf.mk f a ∂Measure.map (hg.mk g) μ := by
      congr 1
      exact Measure.map_congr hg.ae_eq_mk
    _ = ∫⁻ a, hf.mk f (hg.mk g a) ∂μ := lintegral_map hf.measurable_mk hg.measurable_mk
_ = ∫⁻ a, hf.mk f (g a) ∂μ := lintegral_congr_ae hg.ae_eq_mk.symm.fun_comp _
    _ = ∫⁻ a, f (g a) ∂μ := lintegral_congr_ae (ae_eq_comp hg hf.ae_eq_mk.symm)

/--
theorem `lintegral_map_le` / 定理 `lintegral_map_le`

English:
theorem lintegral_map_le
  given: (f : β -> Real>=0∞) (g : α -> β)
  proof: by
  by_cases hg : AEMeasurable g μ
  · rw [← iSup_lintegral_measurable_le_eq_lintegral]
    refine iSup₂_le fun i hi => iSup_le fun h'i => ?_
    rw [lintegral_map' hi.aemeasurable hg]
    exact lintegral_mono fun _ => h'i _
  · simp [map_of_not_aemeasurable hg]

中文:
定理 lintegral_map_le
  条件: (f : β -> 实数>=0∞) (g : α -> β)
  证明: by
  by_cases hg : AEMeasurable g μ
  · rw [← iSup_lintegral_measurable_le_eq_lintegral]
    refine iSup₂_le fun i hi => iSup_le fun h'i => ?_
    rw [lintegral_map' hi.aemeasurable hg]
    exact lintegral_mono fun _ => h'i _
  · simp [map_of_not_aemeasurable hg]

Depends on / 依赖: AEMeasurable, aemeasurable, hi.aemeasurable, iSup_le, iSup_lintegral_measurable_le_eq_lintegral, lintegral_map, lintegral_mono, map_of_not_aemeasurable
-/
theorem lintegral_map_le (f : β -> Real>=0∞) (g : α -> β) :
    ∫⁻ a, f a ∂Measure.map g μ <= ∫⁻ a, f (g a) ∂μ := by
  by_cases hg : AEMeasurable g μ
  · rw [← iSup_lintegral_measurable_le_eq_lintegral]
    refine iSup₂_le fun i hi => iSup_le fun h'i => ?_
    rw [lintegral_map' hi.aemeasurable hg]
    exact lintegral_mono fun _ => h'i _
  · simp [map_of_not_aemeasurable hg]

/--
theorem `lintegral_comp` / 定理 `lintegral_comp`

English:
theorem lintegral_comp
  statement: {f : β -> Real>=0∞} {g : α -> β} (hf : Measurable f)
  proof: (lintegral_map hf hg).symm

中文:
定理 lintegral_comp
  结论: {f : β -> 实数>=0∞} {g : α -> β} (hf : 可测 f)
  证明: (lintegral_map hf hg).symm

Depends on / 依赖: lintegral_map
-/
theorem lintegral_comp {f : β -> Real>=0∞} {g : α -> β} (hf : Measurable f)
    (hg : Measurable g) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂map g μ :=
  (lintegral_map hf hg).symm

/--
theorem `lintegral_comp'` / 定理 `lintegral_comp'`

English:
theorem lintegral_comp'
  statement: {f : β -> Real>=0∞} {g : α -> β} (hf : AEMeasurable f (μ.map g))
  proof: (lintegral_map' hf hg).symm

中文:
定理 lintegral_comp'
  结论: {f : β -> 实数>=0∞} {g : α -> β} (hf : 几乎处处可测 f (μ.map g))
  证明: (lintegral_map' hf hg).symm

Depends on / 依赖: lintegral_map
-/
theorem lintegral_comp' {f : β -> Real>=0∞} {g : α -> β} (hf : AEMeasurable f (μ.map g))
    (hg : AEMeasurable g μ) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂μ.map g :=
  (lintegral_map' hf hg).symm

/--
theorem `setLIntegral_map` / 定理 `setLIntegral_map`

English:
theorem setLIntegral_map
  statement: {f : β -> Real>=0∞} {g : α -> β} {s : Set β}
  proof: by
  rw [restrict_map hg hs]; rw [lintegral_map hf hg]

中文:
定理 setL整数egral_map
  结论: {f : β -> 实数>=0∞} {g : α -> β} {s : 集合 β}
  证明: by
  rw [restrict_map hg hs]; rw [lintegral_map hf hg]

Depends on / 依赖: lintegral_map, restrict_map
-/
theorem setLIntegral_map {f : β -> Real>=0∞} {g : α -> β} {s : Set β}
    (hs : MeasurableSet s) (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ y in s, f y ∂map g μ = ∫⁻ x in g ⁻¹' s, f (g x) ∂μ := by
  rw [restrict_map hg hs]; rw [lintegral_map hf hg]

/--
theorem `lintegral_indicator_const_comp` / 定理 `lintegral_indicator_const_comp`

English:
theorem lintegral_indicator_const_comp
  statement: {f : α -> β} {s : Set β}
  proof: by
  rw [← lintegral_map (measurable_const.indicator hs) hf]; rw [lintegral_indicator_const hs]; rw [Measure.map_apply hf hs]

中文:
定理 lintegral_indicator_const_comp
  结论: {f : α -> β} {s : 集合 β}
  证明: by
  rw [← lintegral_map (measurable_const.indicator hs) hf]; rw [lintegral_indicator_const hs]; rw [Measure.map_apply hf hs]

Depends on / 依赖: Measure, Measure.map_apply, indicator, lintegral_indicator_const, lintegral_map, map_apply, measurable_const, measurable_const.indicator
-/
theorem lintegral_indicator_const_comp {f : α -> β} {s : Set β}
    (hf : Measurable f) (hs : MeasurableSet s) (c : Real>=0∞) :
    ∫⁻ a, s.indicator (fun _ => c) (f a) ∂μ = c * μ (f ⁻¹' s) := by
  rw [← lintegral_map (measurable_const.indicator hs) hf]; rw [lintegral_indicator_const hs]; rw [Measure.map_apply hf hs]

/--
theorem `_root_.MeasurableEmbedding.lintegral_map` / 定理 `_root_.MeasurableEmbedding.lintegral_map`

English:
theorem _root_.MeasurableEmbedding.lintegral_map
  statement: {g : α -> β}
  proof: by
  rw [lintegral]; rw [lintegral]
  refine le_antisymm (iSup₂_le fun f₀ hf₀ => ?_) (iSup₂_le fun f₀ hf₀ => ?_)
  · rw [SimpleFunc.lintegral_map _ hg.measurable]
    have : (f₀.comp g hg.measurable : α -> Real>=0∞) <= f ∘ g := fun x => hf₀ (g x)
    exact le_iSup_of_le (comp f₀ g hg.measurable) (by exact le_iSup (α := Real>=0∞) _ this)
  · rw [← f₀.extend_comp_eq hg (const _ 0), ← SimpleFunc.lintegral_map, ←
      SimpleFunc.lintegral_eq_lintegral, ← lintegral]
    refine lintegral_mono_ae (hg.ae_map_iff.2 <| Eventually.of_forall fun x => ?_)
    exact (extend_apply _ _ _ _).trans_le (hf₀ _)

中文:
定理 _root_.可测嵌入.lintegral_map
  结论: {g : α -> β}
  证明: by
  rw [lintegral]; rw [lintegral]
  refine le_antisymm (iSup₂_le fun f₀ hf₀ => ?_) (iSup₂_le fun f₀ hf₀ => ?_)
  · rw [SimpleFunc.lintegral_map _ hg.measurable]
    have : (f₀.comp g hg.measurable : α -> Real>=0∞) <= f ∘ g := fun x => hf₀ (g x)
    exact le_iSup_of_le (comp f₀ g hg.measurable) (by exact le_iSup (α := Real>=0∞) _ this)
  · rw [← f₀.extend_comp_eq hg (const _ 0), ← SimpleFunc.lintegral_map, ←
      SimpleFunc.lintegral_eq_lintegral, ← lintegral]
    refine lintegral_mono_ae (hg.ae_map_iff.2 <| Eventually.of_forall fun x => ?_)
    exact (extend_apply _ _ _ _).trans_le (hf₀ _)

Depends on / 依赖: Eventually, SimpleFunc, SimpleFunc.lintegral_eq_lintegral, SimpleFunc.lintegral_map, ae_map_iff, extend_comp_eq, hg.ae_map_iff, hg.measurable, le_antisymm, le_iSup, le_iSup_of_le, lintegral, lintegral_eq_lintegral, lintegral_map, lintegral_mono_ae, measurable
-/
theorem _root_.MeasurableEmbedding.lintegral_map {g : α -> β}
    (hg : MeasurableEmbedding g) (f : β -> Real>=0∞) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ := by
  rw [lintegral]; rw [lintegral]
  refine le_antisymm (iSup₂_le fun f₀ hf₀ => ?_) (iSup₂_le fun f₀ hf₀ => ?_)
  · rw [SimpleFunc.lintegral_map _ hg.measurable]
    have : (f₀.comp g hg.measurable : α -> Real>=0∞) <= f ∘ g := fun x => hf₀ (g x)
    exact le_iSup_of_le (comp f₀ g hg.measurable) (by exact le_iSup (α := Real>=0∞) _ this)
  · rw [← f₀.extend_comp_eq hg (const _ 0), ← SimpleFunc.lintegral_map, ←
      SimpleFunc.lintegral_eq_lintegral, ← lintegral]
    refine lintegral_mono_ae (hg.ae_map_iff.2 <| Eventually.of_forall fun x => ?_)
    exact (extend_apply _ _ _ _).trans_le (hf₀ _)

/--
theorem `lintegral_map_equiv` / 定理 `lintegral_map_equiv`

English:
theorem lintegral_map_equiv
  given: (f : β -> Real>=0∞) (g : α ≃ᵐ β)
  proof: g.measurableEmbedding.lintegral_map f

中文:
定理 lintegral_map_equiv
  条件: (f : β -> 实数>=0∞) (g : α ≃ᵐ β)
  证明: g.measurableEmbedding.lintegral_map f

Depends on / 依赖: g.measurableEmbedding.lintegral_map, lintegral_map, measurableEmbedding
-/
theorem lintegral_map_equiv (f : β -> Real>=0∞) (g : α ≃ᵐ β) :
    ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ :=
  g.measurableEmbedding.lintegral_map f

/--
theorem `lintegral_subtype_comap` / 定理 `lintegral_subtype_comap`

English:
theorem lintegral_subtype_comap
  given: {s : Set α} (hs : MeasurableSet s) (f : α -> Real>=0∞)
  proof: by
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map]; rw [map_comap_subtype_coe hs]

中文:
定理 lintegral_subtype_comap
  条件: {s : 集合 α} (hs : 可测集 s) (f : α -> 实数>=0∞)
  证明: by
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map]; rw [map_comap_subtype_coe hs]

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.subtype_coe, lintegral_map, map_comap_subtype_coe, subtype_coe
-/
theorem lintegral_subtype_comap {s : Set α} (hs : MeasurableSet s) (f : α -> Real>=0∞) :
    ∫⁻ x : s, f x ∂(μ.comap (↑)) = ∫⁻ x in s, f x ∂μ := by
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map]; rw [map_comap_subtype_coe hs]

/--
theorem `setLIntegral_subtype` / 定理 `setLIntegral_subtype`

English:
theorem setLIntegral_subtype
  given: {s : Set α} (hs : MeasurableSet s) (t : Set s) (f : α -> Real>=0∞)
  proof: by
  rw [(MeasurableEmbedding.subtype_coe hs).restrict_comap]; rw [lintegral_subtype_comap hs]; rw [restrict_restrict hs]; rw [inter_eq_right.2 (Subtype.coe_image_subset _ _)]

中文:
定理 setL整数egral_subtype
  条件: {s : 集合 α} (hs : 可测集 s) (t : 集合 s) (f : α -> 实数>=0∞)
  证明: by
  rw [(MeasurableEmbedding.subtype_coe hs).restrict_comap]; rw [lintegral_subtype_comap hs]; rw [restrict_restrict hs]; rw [inter_eq_right.2 (Subtype.coe_image_subset _ _)]

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.subtype_coe, Subtype, Subtype.coe_image_subset, coe_image_subset, inter_eq_right, lintegral_subtype_comap, restrict_comap, restrict_restrict, subtype_coe
-/
theorem setLIntegral_subtype {s : Set α} (hs : MeasurableSet s) (t : Set s) (f : α -> Real>=0∞) :
    ∫⁻ x in t, f x ∂(μ.comap (↑)) = ∫⁻ x in (↑) '' t, f x ∂μ := by
  rw [(MeasurableEmbedding.subtype_coe hs).restrict_comap]; rw [lintegral_subtype_comap hs]; rw [restrict_restrict hs]; rw [inter_eq_right.2 (Subtype.coe_image_subset _ _)]

end Map

namespace MeasurePreserving

variable {g : α -> β} (hg : MeasurePreserving g μ ν)

/--
theorem `lintegral_map_equiv` / 定理 `lintegral_map_equiv`

English:
theorem lintegral_map_equiv
  given: (f : β -> Real>=0∞) (g : α ≃ᵐ β) (hg : MeasurePreserving g μ ν)
  proof: by
  rw [← MeasureTheory.lintegral_map_equiv f g]; rw [hg.map_eq]

include hg

中文:
定理 lintegral_map_equiv
  条件: (f : β -> 实数>=0∞) (g : α ≃ᵐ β) (hg : 保测 g μ ν)
  证明: by
  rw [← MeasureTheory.lintegral_map_equiv f g]; rw [hg.map_eq]

include hg
-/
protected theorem lintegral_map_equiv (f : β -> Real>=0∞) (g : α ≃ᵐ β) (hg : MeasurePreserving g μ ν) :
    ∫⁻ a, f a ∂ν = ∫⁻ a, f (g a) ∂μ := by
  rw [← MeasureTheory.lintegral_map_equiv f g]; rw [hg.map_eq]

include hg

/--
theorem `lintegral_comp` / 定理 `lintegral_comp`

English:
theorem lintegral_comp
  given: {f : β -> Real>=0∞} (hf : Measurable f)
  proof: by rw [← hg.map_eq, lintegral_map hf hg.measurable]

中文:
定理 lintegral_comp
  条件: {f : β -> 实数>=0∞} (hf : 可测 f)
  证明: by rw [← hg.map_eq, lintegral_map hf hg.measurable]

Depends on / 依赖: hg.map_eq, hg.measurable, lintegral_map, map_eq, measurable
-/
theorem lintegral_comp {f : β -> Real>=0∞} (hf : Measurable f) :
    ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν := by rw [← hg.map_eq, lintegral_map hf hg.measurable]

/--
theorem `lintegral_comp_emb` / 定理 `lintegral_comp_emb`

English:
theorem lintegral_comp_emb
  given: (hge : MeasurableEmbedding g) (f : β -> Real>=0∞)
  proof: by rw [← hg.map_eq, hge.lintegral_map]

中文:
定理 lintegral_comp_emb
  条件: (hge : 可测嵌入 g) (f : β -> 实数>=0∞)
  证明: by rw [← hg.map_eq, hge.lintegral_map]

Depends on / 依赖: hg.map_eq, hge.lintegral_map, lintegral_map, map_eq
-/
theorem lintegral_comp_emb (hge : MeasurableEmbedding g) (f : β -> Real>=0∞) :
    ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν := by rw [← hg.map_eq, hge.lintegral_map]

/--
theorem `setLIntegral_comp_preimage` / 定理 `setLIntegral_comp_preimage`

English:
theorem setLIntegral_comp_preimage
  proof: by
  rw [← hg.map_eq]; rw [setLIntegral_map hs hf hg.measurable]

中文:
定理 setL整数egral_comp_preimage
  证明: by
  rw [← hg.map_eq]; rw [setLIntegral_map hs hf hg.measurable]

Depends on / 依赖: hg.map_eq, hg.measurable, map_eq, measurable, setLIntegral_map
-/
theorem setLIntegral_comp_preimage
    {s : Set β} (hs : MeasurableSet s) {f : β -> Real>=0∞} (hf : Measurable f) :
    ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν := by
  rw [← hg.map_eq]; rw [setLIntegral_map hs hf hg.measurable]

/--
theorem `setLIntegral_comp_preimage_emb` / 定理 `setLIntegral_comp_preimage_emb`

English:
theorem setLIntegral_comp_preimage_emb
  given: (hge : MeasurableEmbedding g) (f : β -> Real>=0∞) (s : Set β)
  proof: by
  rw [← hg.map_eq]; rw [hge.restrict_map]; rw [hge.lintegral_map]

中文:
定理 setL整数egral_comp_preimage_emb
  条件: (hge : 可测嵌入 g) (f : β -> 实数>=0∞) (s : 集合 β)
  证明: by
  rw [← hg.map_eq]; rw [hge.restrict_map]; rw [hge.lintegral_map]

Depends on / 依赖: hg.map_eq, hge.lintegral_map, hge.restrict_map, lintegral_map, map_eq, restrict_map
-/
theorem setLIntegral_comp_preimage_emb (hge : MeasurableEmbedding g) (f : β -> Real>=0∞) (s : Set β) :
    ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν := by
  rw [← hg.map_eq]; rw [hge.restrict_map]; rw [hge.lintegral_map]

/--
theorem `setLIntegral_comp_emb` / 定理 `setLIntegral_comp_emb`

English:
theorem setLIntegral_comp_emb
  given: (hge : MeasurableEmbedding g) (f : β -> Real>=0∞) (s : Set α)
  proof: by
  rw [← hg.setLIntegral_comp_preimage_emb hge]; rw [Set.preimage_image_eq _ hge.injective]

中文:
定理 setL整数egral_comp_emb
  条件: (hge : 可测嵌入 g) (f : β -> 实数>=0∞) (s : 集合 α)
  证明: by
  rw [← hg.setLIntegral_comp_preimage_emb hge]; rw [Set.preimage_image_eq _ hge.injective]

Depends on / 依赖: Set.preimage_image_eq, hg.setLIntegral_comp_preimage_emb, hge.injective, injective, preimage_image_eq, setLIntegral_comp_preimage_emb
-/
theorem setLIntegral_comp_emb (hge : MeasurableEmbedding g) (f : β -> Real>=0∞) (s : Set α) :
    ∫⁻ a in s, f (g a) ∂μ = ∫⁻ b in g '' s, f b ∂ν := by
  rw [← hg.setLIntegral_comp_preimage_emb hge]; rw [Set.preimage_image_eq _ hge.injective]

end MeasurePreserving

end MeasureTheory
