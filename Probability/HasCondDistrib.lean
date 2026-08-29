/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/

module

public import Mathlib.Probability.HasLaw

import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# A predicate for having a specified conditional distribution

We introduce a predicate `HasCondDistrib Y X κ P` stating that the conditional distribution of `Y`
given `X` under the measure `P` is equal to the kernel `κ`.
The statement uses `HasLaw` to express that the law of the pair `(X, Y)` under `P` is equal to
`(P.map X) ⊗ₘ κ`, the product of the law of `X` under `P` and the kernel `κ`.
The use of `HasLaw` also implies that `Y` and `X` are a.e. measurable.

## Main definitions

* `HasCondDistrib Y X κ P` : predicate stating that the conditional distribution of `Y` given `X`
  under the measure `P` is equal to the kernel `κ`.

-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 𝓩 : Type*} {mΩ : MeasurableSpace Ω}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩}
  {P : Measure Ω} {X : Ω -> 𝓧} {Y : Ω -> 𝓨} {κ : Kernel 𝓧 𝓨}

/--
Definition of `HasCondDistrib` / `HasCondDistrib` 的定义

English:
definition HasCondDistrib
  signature: (Y : Ω -> 𝓨) (X : Ω -> 𝓧) (κ : Kernel 𝓧 𝓨) (P : Measure Ω)
  body: HasLaw (fun ω => (X ω, Y ω)) ((P.map X) otimesₘ κ) P

@[fun_prop]

中文:
定义 HasCondDistrib
  签名: (Y : Ω -> 𝓨) (X : Ω -> 𝓧) (κ : 核 𝓧 𝓨) (P : 测度 Ω)
  定义体: HasLaw (fun ω => (X ω, Y ω)) ((P.map X) otimesₘ κ) P

@[fun_prop]

Depends on / 依赖: HasLaw, P.map
-/
def HasCondDistrib (Y : Ω -> 𝓨) (X : Ω -> 𝓧) (κ : Kernel 𝓧 𝓨) (P : Measure Ω) : Prop :=
  HasLaw (fun ω => (X ω, Y ω)) ((P.map X) otimesₘ κ) P

@[fun_prop]
/--
lemma `HasCondDistrib.aemeasurable_fst` / 引理 `HasCondDistrib.aemeasurable_fst`

English:
lemma HasCondDistrib.aemeasurable_fst
  given: (h : HasCondDistrib Y X κ P)
  proof: h.aemeasurable.fst

@[fun_prop]

中文:
引理 HasCondDistrib.aemeasurable_fst
  条件: (h : HasCondDistrib Y X κ P)
  证明: h.aemeasurable.fst

@[fun_prop]

Depends on / 依赖: aemeasurable, h.aemeasurable.fst
-/
lemma HasCondDistrib.aemeasurable_fst (h : HasCondDistrib Y X κ P) :
    AEMeasurable X P := h.aemeasurable.fst

@[fun_prop]
/--
lemma `HasCondDistrib.aemeasurable_snd` / 引理 `HasCondDistrib.aemeasurable_snd`

English:
lemma HasCondDistrib.aemeasurable_snd
  given: (h : HasCondDistrib Y X κ P)
  proof: h.aemeasurable.snd

中文:
引理 HasCondDistrib.aemeasurable_snd
  条件: (h : HasCondDistrib Y X κ P)
  证明: h.aemeasurable.snd

Depends on / 依赖: aemeasurable, h.aemeasurable.snd
-/
lemma HasCondDistrib.aemeasurable_snd (h : HasCondDistrib Y X κ P) :
    AEMeasurable Y P := h.aemeasurable.snd

/--
lemma `HasLaw.prodMk_of_hasCondDistrib` / 引理 `HasLaw.prodMk_of_hasCondDistrib`

English:
lemma HasLaw.prodMk_of_hasCondDistrib
  statement: {Q : Measure 𝓧}
  proof: by rwa [← h1.map_eq]

中文:
引理 有Law.prodMk_of_hasCondDistrib
  结论: {Q : 测度 𝓧}
  证明: by rwa [← h1.map_eq]

Depends on / 依赖: h1.map_eq, map_eq
-/
lemma HasLaw.prodMk_of_hasCondDistrib {Q : Measure 𝓧}
    (h1 : HasLaw X Q P) (h2 : HasCondDistrib Y X κ P) :
    HasLaw (fun ω => (X ω, Y ω)) (Q otimesₘ κ) P := by rwa [← h1.map_eq]

/--
lemma `HasCondDistrib.hasLaw_of_const` / 引理 `HasCondDistrib.hasLaw_of_const`

English:
lemma HasCondDistrib.hasLaw_of_const
  statement: [IsProbabilityMeasure P] {Q : Measure 𝓨} [SFinite Q]
  proof: by
    have h_snd : (P.map (fun ω => (X ω, Y ω))).snd = Q := by
      rw [h.map_eq]; rw [Measure.snd_compProd]
      simp [Measure.map_apply_of_aemeasurable h.aemeasurable_fst]
    rwa [Measure.snd_map_prodMk₀ h.aemeasurable_fst] at h_snd

中文:
引理 HasCondDistrib.hasLaw_of_const
  结论: [是概率测度 P] {Q : 测度 𝓨} [SFinite Q]
  证明: by
    have h_snd : (P.map (fun ω => (X ω, Y ω))).snd = Q := by
      rw [h.map_eq]; rw [Measure.snd_compProd]
      simp [Measure.map_apply_of_aemeasurable h.aemeasurable_fst]
    rwa [Measure.snd_map_prodMk₀ h.aemeasurable_fst] at h_snd

Depends on / 依赖: Measure, Measure.map_apply_of_aemeasurable, Measure.snd_compProd, Measure.snd_map_prodMk, P.map, aemeasurable_fst, h.aemeasurable_fst, h.map_eq, h_snd, map_apply_of_aemeasurable, map_eq, snd_compProd
-/
lemma HasCondDistrib.hasLaw_of_const [IsProbabilityMeasure P] {Q : Measure 𝓨} [SFinite Q]
    (h : HasCondDistrib Y X (Kernel.const 𝓧 Q) P) :
    HasLaw Y Q P where
  map_eq := by
    have h_snd : (P.map (fun ω => (X ω, Y ω))).snd = Q := by
      rw [h.map_eq]; rw [Measure.snd_compProd]
      simp [Measure.map_apply_of_aemeasurable h.aemeasurable_fst]
    rwa [Measure.snd_map_prodMk₀ h.aemeasurable_fst] at h_snd

variable [SFinite P] [IsSFiniteKernel κ]

/--
lemma `HasCondDistrib.comp_left` / 引理 `HasCondDistrib.comp_left`

English:
lemma HasCondDistrib.comp_left
  given: (h : HasCondDistrib Y X κ P) {f : 𝓨 -> 𝓩} (hf : Measurable f)
  proof: calc
    P.map (fun ω => (X ω, f (Y ω)))
    _ = (P.map (fun ω => (X ω, Y ω))).map (Prod.map id f) := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      congr
    _ = (P.map X otimesₘ κ).map (Prod.map id f) := by rw [h.map_eq]
    _ = P.map X otimesₘ κ.map f := by r

中文:
引理 HasCondDistrib.comp_left
  条件: (h : HasCondDistrib Y X κ P) {f : 𝓨 -> 𝓩} (hf : 可测 f)
  证明: calc
    P.map (fun ω => (X ω, f (Y ω)))
    _ = (P.map (fun ω => (X ω, Y ω))).map (Prod.map id f) := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      congr
    _ = (P.map X otimesₘ κ).map (Prod.map id f) := by rw [h.map_eq]
    _ = P.map X otimesₘ κ.map f := by r
-/
lemma HasCondDistrib.comp_left (h : HasCondDistrib Y X κ P) {f : 𝓨 -> 𝓩} (hf : Measurable f) :
    HasCondDistrib (f ∘ Y) X (κ.map f) P where
  map_eq := calc
    P.map (fun ω => (X ω, f (Y ω)))
    _ = (P.map (fun ω => (X ω, Y ω))).map (Prod.map id f) := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      congr
    _ = (P.map X otimesₘ κ).map (Prod.map id f) := by rw [h.map_eq]
    _ = P.map X otimesₘ κ.map f := by rw [Measure.compProd_map hf]

/--
lemma `HasCondDistrib.fst` / 引理 `HasCondDistrib.fst`

English:
lemma HasCondDistrib.fst
  statement: {Y : Ω -> 𝓨 × 𝓩} {κ : Kernel 𝓧 (𝓨 × 𝓩)} [IsSFiniteKernel κ]
  proof: by
  rw [Kernel.fst_eq]
  exact h.comp_left measurable_fst

中文:
引理 HasCondDistrib.fst
  结论: {Y : Ω -> 𝓨 × 𝓩} {κ : 核 𝓧 (𝓨 × 𝓩)} [是SFiniteKernel κ]
  证明: by
  rw [Kernel.fst_eq]
  exact h.comp_left measurable_fst

Depends on / 依赖: Kernel, Kernel.fst_eq, comp_left, fst_eq, h.comp_left, measurable_fst
-/
lemma HasCondDistrib.fst {Y : Ω -> 𝓨 × 𝓩} {κ : Kernel 𝓧 (𝓨 × 𝓩)} [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun ω => (Y ω).1) X κ.fst P := by
  rw [Kernel.fst_eq]
  exact h.comp_left measurable_fst

/--
lemma `HasCondDistrib.snd` / 引理 `HasCondDistrib.snd`

English:
lemma HasCondDistrib.snd
  statement: {Y : Ω -> 𝓨 × 𝓩} {κ : Kernel 𝓧 (𝓨 × 𝓩)} [IsSFiniteKernel κ]
  proof: by
  rw [Kernel.snd_eq]
  exact h.comp_left measurable_snd

中文:
引理 HasCondDistrib.snd
  结论: {Y : Ω -> 𝓨 × 𝓩} {κ : 核 𝓧 (𝓨 × 𝓩)} [是SFiniteKernel κ]
  证明: by
  rw [Kernel.snd_eq]
  exact h.comp_left measurable_snd

Depends on / 依赖: Kernel, Kernel.snd_eq, comp_left, h.comp_left, measurable_snd, snd_eq
-/
lemma HasCondDistrib.snd {Y : Ω -> 𝓨 × 𝓩} {κ : Kernel 𝓧 (𝓨 × 𝓩)} [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun ω => (Y ω).2) X κ.snd P := by
  rw [Kernel.snd_eq]
  exact h.comp_left measurable_snd

/--
lemma `HasCondDistrib.comp_right` / 引理 `HasCondDistrib.comp_right`

English:
lemma HasCondDistrib.comp_right
  statement: {f : 𝓩 -> 𝓧}
  proof: calc
    P.map (fun a => ((f ∘ Z) a, Y a))
    _ = (P.map (fun a => (Z a, Y a))).map (Prod.map f id) := by
        rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
        rfl
    _ = (P.map Z otimesₘ κ.comap f hf).map (Prod.map f id) := by rw [h.map_eq]
    _ = (P.map Z).map f 

中文:
引理 HasCondDistrib.comp_right
  结论: {f : 𝓩 -> 𝓧}
  证明: calc
    P.map (fun a => ((f ∘ Z) a, Y a))
    _ = (P.map (fun a => (Z a, Y a))).map (Prod.map f id) := by
        rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
        rfl
    _ = (P.map Z otimesₘ κ.comap f hf).map (Prod.map f id) := by rw [h.map_eq]
    _ = (P.map Z).map f 
-/
lemma HasCondDistrib.comp_right {f : 𝓩 -> 𝓧}
    {hf : Measurable f} {Z : Ω -> 𝓩} (h : HasCondDistrib Y Z (κ.comap f hf) P) :
    HasCondDistrib Y (f ∘ Z) κ P where
  map_eq := calc
    P.map (fun a => ((f ∘ Z) a, Y a))
    _ = (P.map (fun a => (Z a, Y a))).map (Prod.map f id) := by
        rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
        rfl
    _ = (P.map Z otimesₘ κ.comap f hf).map (Prod.map f id) := by rw [h.map_eq]
    _ = (P.map Z).map f otimesₘ κ := by
        ext s hs
        rw [Measure.map_apply (by fun_prop) hs]; rw [Measure.compProd_apply (by measurability)]; rw [Measure.compProd_apply hs]; rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
        rfl
    _ = P.map (f ∘ Z) otimesₘ κ := by
        rw [AEMeasurable.map_map_of_aemeasurable hf.aemeasurable (by fun_prop)]

/--
lemma `HasCondDistrib.measurableEquiv_comp_right` / 引理 `HasCondDistrib.measurableEquiv_comp_right`

English:
lemma HasCondDistrib.measurableEquiv_comp_right
  given: (h : HasCondDistrib Y X κ P) (f : 𝓧 ≃ᵐ 𝓩)
  proof: by
  apply HasCondDistrib.comp_right (hf := f.measurable)
  simpa [← Kernel.comap_comp_right]

中文:
引理 HasCondDistrib.measurableEquiv_comp_right
  条件: (h : HasCondDistrib Y X κ P) (f : 𝓧 ≃ᵐ 𝓩)
  证明: by
  apply HasCondDistrib.comp_right (hf := f.measurable)
  simpa [← Kernel.comap_comp_right]

Depends on / 依赖: HasCondDistrib, HasCondDistrib.comp_right, Kernel, Kernel.comap_comp_right, comap_comp_right, comp_right, f.measurable, measurable
-/
lemma HasCondDistrib.measurableEquiv_comp_right (h : HasCondDistrib Y X κ P) (f : 𝓧 ≃ᵐ 𝓩) :
    HasCondDistrib Y (f ∘ X) (κ.comap f.symm f.symm.measurable) P := by
  apply HasCondDistrib.comp_right (hf := f.measurable)
  simpa [← Kernel.comap_comp_right]

/--
lemma `HasCondDistrib.of_compProd` / 引理 `HasCondDistrib.of_compProd`

English:
lemma HasCondDistrib.of_compProd
  statement: {Z : Ω -> 𝓩} {η : Kernel (𝓧 × 𝓨) 𝓩} [IsMarkovKernel η]
  proof: by
  have hZ : AEMeasurable Z P := h.aemeasurable_snd.snd
  have hY : AEMeasurable Y P := h.aemeasurable_snd.fst
  refine ⟨by fun_prop, ?_⟩
  calc P.map (fun a => ((X a, Y a), Z a))
  _ = (P.map X otimesₘ (κ otimesₖ η)).map MeasurableEquiv.prodAssoc.symm := by
      rw [← h.map_eq]; rw [AEMeasurable

中文:
引理 HasCondDistrib.of_compProd
  结论: {Z : Ω -> 𝓩} {η : 核 (𝓧 × 𝓨) 𝓩} [是MarkovKernel η]
  证明: by
  have hZ : AEMeasurable Z P := h.aemeasurable_snd.snd
  have hY : AEMeasurable Y P := h.aemeasurable_snd.fst
  refine ⟨by fun_prop, ?_⟩
  calc P.map (fun a => ((X a, Y a), Z a))
  _ = (P.map X otimesₘ (κ otimesₖ η)).map MeasurableEquiv.prodAssoc.symm := by
      rw [← h.map_eq]; rw [AEMeasurable

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, MeasurableEquiv, MeasurableEquiv.prodAssoc.symm, Measure, Measure.compProd_assoc, P.map, aemeasurable_snd, compProd_assoc, fun_prop, h.aemeasurable_snd.fst, h.aemeasurable_snd.snd, h.fst.map_eq, h.map_eq, map_eq, map_map_of_aemeasurable, prodAssoc
-/
lemma HasCondDistrib.of_compProd {Z : Ω -> 𝓩} {η : Kernel (𝓧 × 𝓨) 𝓩} [IsMarkovKernel η]
    (h : HasCondDistrib (fun a => (Y a, Z a)) X (κ otimesₖ η) P) :
    HasCondDistrib Z (fun a => (X a, Y a)) η P := by
  have hZ : AEMeasurable Z P := h.aemeasurable_snd.snd
  have hY : AEMeasurable Y P := h.aemeasurable_snd.fst
  refine ⟨by fun_prop, ?_⟩
  calc P.map (fun a => ((X a, Y a), Z a))
  _ = (P.map X otimesₘ (κ otimesₖ η)).map MeasurableEquiv.prodAssoc.symm := by
      rw [← h.map_eq]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      rfl
  _ = P.map X otimesₘ κ otimesₘ η := Measure.compProd_assoc
  _ = P.map (fun a => (X a, Y a)) otimesₘ η := by simp [h.fst.map_eq]

end ProbabilityTheory
