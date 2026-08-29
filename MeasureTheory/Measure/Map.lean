/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Pushforward of a measure

In this file we define the pushforward `MeasureTheory.Measure.map f μ`
of a measure `μ` along an almost everywhere measurable map `f`.
If `f` is not a.e. measurable, then we define `map f μ` to be zero.

## Main definitions

* `MeasureTheory.Measure.map f μ`: map of the measure `μ` along the map `f`.

## Main statements

* `map_apply`: for `s` a measurable set, `μ.map f s = μ (f ⁻¹' s)`
* `map_map`: `(μ.map f).map g = μ.map (g ∘ f)`

-/

@[expose] public section

variable {α β γ : Type*}

open Set Function ENNReal NNReal
open Filter hiding map

namespace MeasureTheory

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {s : Set α}

namespace Measure

/-- Lift a linear map between `OuterMeasure` spaces such that for each measure `μ` every measurable
set is Carathéodory-measurable w.r.t. `f μ` to a linear map between `Measure` spaces. -/
noncomputable
/--
Definition of `liftLinear` / `liftLinear` 的定义

English:
definition liftLinear
  signature: [MeasurableSpace β] (f : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β)
  body: (f μ.toOuterMeasure).toMeasure (hf μ)
  map_add' μ₁ μ₂ := ext fun s hs => by
    simp only [map_add, coe_add, Pi.add_apply, toMeasure_apply, add_toOuterMeasure,
      FunLike.coe_add, hs]
  map_smul' c μ := ext fun s hs => by
    simp only [map_smulₛₗ, Pi.smul_apply, toMeasure_apply, smul_toOuterMea

中文:
定义 liftLinear
  签名: [MeasurableSpace β] (f : OuterMeasure α ->ₗ[实数>=0∞] OuterMeasure β)
  定义体: (f μ.toOuterMeasure).toMeasure (hf μ)
  map_add' μ₁ μ₂ := ext fun s hs => by
    simp only [map_add, coe_add, Pi.add_apply, toMeasure_apply, add_toOuterMeasure,
      FunLike.coe_add, hs]
  map_smul' c μ := ext fun s hs => by
    simp only [map_smulₛₗ, Pi.smul_apply, toMeasure_apply, smul_toOuterMea

Depends on / 依赖: toMeasure, toOuterMeasure
-/
def liftLinear [MeasurableSpace β] (f : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β)
    (hf : forall μ : Measure α, ‹_› <= (f μ.toOuterMeasure).caratheodory) :
    Measure α ->ₗ[Real>=0∞] Measure β where
  toFun μ := (f μ.toOuterMeasure).toMeasure (hf μ)
  map_add' μ₁ μ₂ := ext fun s hs => by
    simp only [map_add, coe_add, Pi.add_apply, toMeasure_apply, add_toOuterMeasure,
      FunLike.coe_add, hs]
  map_smul' c μ := ext fun s hs => by
    simp only [map_smulₛₗ, Pi.smul_apply, toMeasure_apply, smul_toOuterMeasure (R := Real>=0∞),
      FunLike.coe_smul, smul_apply, hs]

/--
lemma `liftLinear_apply₀` / 引理 `liftLinear_apply₀`

English:
lemma liftLinear_apply₀
  statement: {f : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β} (hf) {s : Set β}
  proof: toMeasure_apply₀ _ (hf μ) hs

@[simp]

中文:
引理 liftLinear_apply₀
  结论: {f : OuterMeasure α ->ₗ[实数>=0∞] OuterMeasure β} (hf) {s : Set β}
  证明: toMeasure_apply₀ _ (hf μ) hs

@[simp]
-/
lemma liftLinear_apply₀ {f : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β} (hf) {s : Set β}
    (hs : NullMeasurableSet s (liftLinear f hf μ)) : liftLinear f hf μ s = f μ.toOuterMeasure s :=
  toMeasure_apply₀ _ (hf μ) hs

@[simp]
/--
theorem `liftLinear_apply` / 定理 `liftLinear_apply`

English:
theorem liftLinear_apply
  statement: {f : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β} (hf) {s : Set β}
  proof: toMeasure_apply _ (hf μ) hs

中文:
定理 liftLinear_apply
  结论: {f : OuterMeasure α ->ₗ[实数>=0∞] OuterMeasure β} (hf) {s : Set β}
  证明: toMeasure_apply _ (hf μ) hs

Depends on / 依赖: toMeasure_apply
-/
theorem liftLinear_apply {f : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β} (hf) {s : Set β}
    (hs : MeasurableSet s) : liftLinear f hf μ s = f μ.toOuterMeasure s :=
  toMeasure_apply _ (hf μ) hs

/--
theorem `le_liftLinear_apply` / 定理 `le_liftLinear_apply`

English:
theorem le_liftLinear_apply
  given: {f : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β} (hf) (s : Set β)
  proof: le_toMeasure_apply _ (hf μ) s

中文:
定理 le_liftLinear_apply
  条件: {f : OuterMeasure α ->ₗ[实数>=0∞] OuterMeasure β} (hf) (s : Set β)
  证明: le_toMeasure_apply _ (hf μ) s

Depends on / 依赖: le_toMeasure_apply
-/
theorem le_liftLinear_apply {f : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β} (hf) (s : Set β) :
    f μ.toOuterMeasure s <= liftLinear f hf μ s :=
  le_toMeasure_apply _ (hf μ) s

open scoped Classical in
/-- The pushforward of a measure as a linear map. It is defined to be `0` if `f` is not
a measurable function. -/
noncomputable
/--
Definition of `mapₗ` / `mapₗ` 的定义

English:
definition mapₗ
  signature: [MeasurableSpace α] [MeasurableSpace β] (f : α -> β)
  body: if hf : Measurable f then
    liftLinear (OuterMeasure.map f) fun μ _s hs t =>
      le_toOuterMeasure_caratheodory μ _ (hf hs) (f ⁻¹' t)
  else 0

中文:
定义 mapₗ
  签名: [MeasurableSpace α] [MeasurableSpace β] (f : α -> β)
  定义体: if hf : Measurable f then
    liftLinear (OuterMeasure.map f) fun μ _s hs t =>
      le_toOuterMeasure_caratheodory μ _ (hf hs) (f ⁻¹' t)
  else 0

Depends on / 依赖: Measurable, OuterMeasure, OuterMeasure.map, le_toOuterMeasure_caratheodory, liftLinear
-/
def mapₗ [MeasurableSpace α] [MeasurableSpace β] (f : α -> β) : Measure α ->ₗ[Real>=0∞] Measure β :=
  if hf : Measurable f then
    liftLinear (OuterMeasure.map f) fun μ _s hs t =>
      le_toOuterMeasure_caratheodory μ _ (hf hs) (f ⁻¹' t)
  else 0

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mapₗ_congr` / 定理 `mapₗ_congr`

English:
theorem mapₗ_congr
  given: {f g : α -> β} (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g)
  proof: by
  ext1 s hs
  simpa only [mapₗ, hf, hg, hs, dif_pos, liftLinear_apply, OuterMeasure.map_apply]
    using! measure_congr (h.preimage s)

中文:
定理 mapₗ_congr
  条件: {f g : α -> β} (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g)
  证明: by
  ext1 s hs
  simpa only [mapₗ, hf, hg, hs, dif_pos, liftLinear_apply, OuterMeasure.map_apply]
    using! measure_congr (h.preimage s)

Depends on / 依赖: OuterMeasure, OuterMeasure.map_apply, dif_pos, h.preimage, liftLinear_apply, map_apply, measure_congr, preimage
-/
theorem mapₗ_congr {f g : α -> β} (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    mapₗ f μ = mapₗ g μ := by
  ext1 s hs
  simpa only [mapₗ, hf, hg, hs, dif_pos, liftLinear_apply, OuterMeasure.map_apply]
    using! measure_congr (h.preimage s)

open scoped Classical in
/-- The pushforward of a measure. It is defined to be `0` if `f` is not an almost everywhere
measurable function. -/
noncomputable
irreducible_def map [MeasurableSpace α] [MeasurableSpace β] (f : α -> β) (μ : Measure α) :
    Measure β :=
  if hf : AEMeasurable f μ then mapₗ (hf.mk f) μ else 0

/--
theorem `mapₗ_mk_apply_of_aemeasurable` / 定理 `mapₗ_mk_apply_of_aemeasurable`

English:
theorem mapₗ_mk_apply_of_aemeasurable
  given: {f : α -> β} (hf : AEMeasurable f μ)
  proof: by simp [map, hf]

中文:
定理 mapₗ_mk_apply_of_aemeasurable
  条件: {f : α -> β} (hf : AEMeasurable f μ)
  证明: by simp [map, hf]
-/
theorem mapₗ_mk_apply_of_aemeasurable {f : α -> β} (hf : AEMeasurable f μ) :
    mapₗ (hf.mk f) μ = map f μ := by simp [map, hf]

/--
theorem `mapₗ_apply_of_measurable` / 定理 `mapₗ_apply_of_measurable`

English:
theorem mapₗ_apply_of_measurable
  given: {f : α -> β} (hf : Measurable f) (μ : Measure α)
  proof: by
  simp only [← mapₗ_mk_apply_of_aemeasurable hf.aemeasurable]
  exact mapₗ_congr hf hf.aemeasurable.measurable_mk hf.aemeasurable.ae_eq_mk

@[simp]

中文:
定理 mapₗ_apply_of_measurable
  条件: {f : α -> β} (hf : Measurable f) (μ : Measure α)
  证明: by
  simp only [← mapₗ_mk_apply_of_aemeasurable hf.aemeasurable]
  exact mapₗ_congr hf hf.aemeasurable.measurable_mk hf.aemeasurable.ae_eq_mk

@[simp]

Depends on / 依赖: ae_eq_mk, aemeasurable, hf.aemeasurable, hf.aemeasurable.ae_eq_mk, hf.aemeasurable.measurable_mk, measurable_mk
-/
theorem mapₗ_apply_of_measurable {f : α -> β} (hf : Measurable f) (μ : Measure α) :
    mapₗ f μ = map f μ := by
  simp only [← mapₗ_mk_apply_of_aemeasurable hf.aemeasurable]
  exact mapₗ_congr hf hf.aemeasurable.measurable_mk hf.aemeasurable.ae_eq_mk

@[simp]
/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (μ ν : Measure α) {f : α -> β} (hf : Measurable f)
  proof: by simp [← mapₗ_apply_of_measurable hf]

@[simp]

中文:
定理 map_add
  条件: (μ ν : Measure α) {f : α -> β} (hf : Measurable f)
  证明: by simp [← mapₗ_apply_of_measurable hf]

@[simp]
-/
protected theorem map_add (μ ν : Measure α) {f : α -> β} (hf : Measurable f) :
    (μ + ν).map f = μ.map f + ν.map f := by simp [← mapₗ_apply_of_measurable hf]

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : α -> β)
  statement: (0 : Measure α).map f = 0
  proof: by
  by_cases hf : AEMeasurable f (0 : Measure α) <;> simp [map, hf]

@[simp]

中文:
定理 map_zero
  条件: (f : α -> β)
  结论: (0 : Measure α).map f = 0
  证明: by
  by_cases hf : AEMeasurable f (0 : Measure α) <;> simp [map, hf]

@[simp]
-/
protected theorem map_zero (f : α -> β) : (0 : Measure α).map f = 0 := by
  by_cases hf : AEMeasurable f (0 : Measure α) <;> simp [map, hf]

@[simp]
/--
theorem `map_of_not_aemeasurable` / 定理 `map_of_not_aemeasurable`

English:
theorem map_of_not_aemeasurable
  given: {f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ)
  proof: by simp [map, hf]

中文:
定理 map_of_not_aemeasurable
  条件: {f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ)
  证明: by simp [map, hf]
-/
theorem map_of_not_aemeasurable {f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) :
    μ.map f = 0 := by simp [map, hf]

/--
theorem `_root_.AEMeasurable.of_map_ne_zero` / 定理 `_root_.AEMeasurable.of_map_ne_zero`

English:
theorem _root_.AEMeasurable.of_map_ne_zero
  given: {f : α -> β} {μ : Measure α} (hf : μ.map f != 0)
  proof: not_imp_comm.1 map_of_not_aemeasurable hf

中文:
定理 _root_.AEMeasurable.of_map_ne_zero
  条件: {f : α -> β} {μ : Measure α} (hf : μ.map f != 0)
  证明: not_imp_comm.1 map_of_not_aemeasurable hf

Depends on / 依赖: map_of_not_aemeasurable, not_imp_comm
-/
theorem _root_.AEMeasurable.of_map_ne_zero {f : α -> β} {μ : Measure α} (hf : μ.map f != 0) :
    AEMeasurable f μ := not_imp_comm.1 map_of_not_aemeasurable hf

/--
theorem `map_congr` / 定理 `map_congr`

English:
theorem map_congr
  given: {f g : α -> β} (h : f =ᵐ[μ] g)
  statement: Measure.map f μ = Measure.map g μ
  proof: by
  by_cases hf : AEMeasurable f μ
  · have hg : AEMeasurable g μ := hf.congr h
    simp only [← mapₗ_mk_apply_of_aemeasurable hf, ← mapₗ_mk_apply_of_aemeasurable hg]
    exact
      mapₗ_congr hf.measurable_mk hg.measurable_mk (hf.ae_eq_mk.symm.trans (h.trans hg.ae_eq_mk))
  · have hg : ¬AEMeasura

中文:
定理 map_congr
  条件: {f g : α -> β} (h : f =ᵐ[μ] g)
  结论: Measure.map f μ = Measure.map g μ
  证明: by
  by_cases hf : AEMeasurable f μ
  · have hg : AEMeasurable g μ := hf.congr h
    simp only [← mapₗ_mk_apply_of_aemeasurable hf, ← mapₗ_mk_apply_of_aemeasurable hg]
    exact
      mapₗ_congr hf.measurable_mk hg.measurable_mk (hf.ae_eq_mk.symm.trans (h.trans hg.ae_eq_mk))
  · have hg : ¬AEMeasura

Depends on / 依赖: AEMeasurable, ae_eq_mk, aemeasurable_congr, h.trans, hf.ae_eq_mk.symm.trans, hf.congr, hf.measurable_mk, hg.ae_eq_mk, hg.measurable_mk, map_of_not_aemeasurable, measurable_mk
-/
theorem map_congr {f g : α -> β} (h : f =ᵐ[μ] g) : Measure.map f μ = Measure.map g μ := by
  by_cases hf : AEMeasurable f μ
  · have hg : AEMeasurable g μ := hf.congr h
    simp only [← mapₗ_mk_apply_of_aemeasurable hf, ← mapₗ_mk_apply_of_aemeasurable hg]
    exact
      mapₗ_congr hf.measurable_mk hg.measurable_mk (hf.ae_eq_mk.symm.trans (h.trans hg.ae_eq_mk))
  · have hg : ¬AEMeasurable g μ := by simpa [← aemeasurable_congr h] using hf
    simp [map_of_not_aemeasurable, hf, hg]

@[simp]
/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: by
  suffices forall c : Real>=0∞, (c • μ).map f = c • μ.map f by simpa using this (c • 1)
  clear c; intro c
  rcases eq_or_ne c 0 with (rfl | hc); · simp
  by_cases hf : AEMeasurable f μ
  · have hfc : AEMeasurable f (c • μ) :=
      ⟨hf.mk f, hf.measurable_mk, (ae_ennreal_smul_measure_iff hc).2 h

中文:
定理 map_smul
  结论: {R : 类型} [SMul R 实数>=0∞] [IsScalarTower R 实数>=0∞ 实数>=0∞]
  证明: by
  suffices forall c : Real>=0∞, (c • μ).map f = c • μ.map f by simpa using this (c • 1)
  clear c; intro c
  rcases eq_or_ne c 0 with (rfl | hc); · simp
  by_cases hf : AEMeasurable f μ
  · have hfc : AEMeasurable f (c • μ) :=
      ⟨hf.mk f, hf.measurable_mk, (ae_ennreal_smul_measure_iff hc).2 h
-/
protected theorem map_smul {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    (c : R) (μ : Measure α) (f : α -> β) : (c • μ).map f = c • μ.map f := by
  suffices forall c : Real>=0∞, (c • μ).map f = c • μ.map f by simpa using this (c • 1)
  clear c; intro c
  rcases eq_or_ne c 0 with (rfl | hc); · simp
  by_cases hf : AEMeasurable f μ
  · have hfc : AEMeasurable f (c • μ) :=
      ⟨hf.mk f, hf.measurable_mk, (ae_ennreal_smul_measure_iff hc).2 hf.ae_eq_mk⟩
    simp only [← mapₗ_mk_apply_of_aemeasurable hf, ← mapₗ_mk_apply_of_aemeasurable hfc, map_smulₛₗ,
      RingHom.id_apply]
    congr 1
    apply mapₗ_congr hfc.measurable_mk hf.measurable_mk
    exact .trans ((ae_ennreal_smul_measure_iff hc).1 hfc.ae_eq_mk.symm) hf.ae_eq_mk
  · have hfc : ¬AEMeasurable f (c • μ) := by
      intro hfc
      exact hf ⟨hfc.mk f, hfc.measurable_mk, (ae_ennreal_smul_measure_iff hc).1 hfc.ae_eq_mk⟩
    simp [map_of_not_aemeasurable hf, map_of_not_aemeasurable hfc]

variable {f : α -> β}

/--
lemma `map_apply₀` / 引理 `map_apply₀`

English:
lemma map_apply₀
  statement: {f : α -> β} (hf : AEMeasurable f μ) {s : Set β}
  proof: by
  rw [map]; rw [dif_pos hf]; rw [mapₗ]; rw [dif_pos hf.measurable_mk] at hs ⊢
  rw [liftLinear_apply₀ _ hs]; rw [measure_congr (hf.ae_eq_mk.preimage s)]
  rfl

中文:
引理 map_apply₀
  结论: {f : α -> β} (hf : AEMeasurable f μ) {s : Set β}
  证明: by
  rw [map]; rw [dif_pos hf]; rw [mapₗ]; rw [dif_pos hf.measurable_mk] at hs ⊢
  rw [liftLinear_apply₀ _ hs]; rw [measure_congr (hf.ae_eq_mk.preimage s)]
  rfl

Depends on / 依赖: ae_eq_mk, dif_pos, hf.ae_eq_mk.preimage, hf.measurable_mk, measurable_mk, measure_congr, preimage
-/
lemma map_apply₀ {f : α -> β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : NullMeasurableSet s (map f μ)) : μ.map f s = μ (f ⁻¹' s) := by
  rw [map]; rw [dif_pos hf]; rw [mapₗ]; rw [dif_pos hf.measurable_mk] at hs ⊢
  rw [liftLinear_apply₀ _ hs]; rw [measure_congr (hf.ae_eq_mk.preimage s)]
  rfl

/-- We can evaluate the pushforward on measurable sets. For non-measurable sets, see
  `MeasureTheory.Measure.le_map_apply` and `MeasurableEquiv.map_apply`. -/
@[simp]
/--
theorem `map_apply_of_aemeasurable` / 定理 `map_apply_of_aemeasurable`

English:
theorem map_apply_of_aemeasurable
  given: (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s)
  proof: map_apply₀ hf hs.nullMeasurableSet

@[simp]

中文:
定理 map_apply_of_aemeasurable
  条件: (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s)
  证明: map_apply₀ hf hs.nullMeasurableSet

@[simp]

Depends on / 依赖: hs.nullMeasurableSet, nullMeasurableSet
-/
theorem map_apply_of_aemeasurable (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    μ.map f s = μ (f ⁻¹' s) := map_apply₀ hf hs.nullMeasurableSet

@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: (hf : Measurable f) {s : Set β} (hs : MeasurableSet s)
  proof: map_apply_of_aemeasurable hf.aemeasurable hs

中文:
定理 map_apply
  条件: (hf : Measurable f) {s : Set β} (hs : MeasurableSet s)
  证明: map_apply_of_aemeasurable hf.aemeasurable hs

Depends on / 依赖: aemeasurable, hf.aemeasurable, map_apply_of_aemeasurable
-/
theorem map_apply (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    μ.map f s = μ (f ⁻¹' s) :=
  map_apply_of_aemeasurable hf.aemeasurable hs

/--
theorem `map_toOuterMeasure` / 定理 `map_toOuterMeasure`

English:
theorem map_toOuterMeasure
  given: (hf : AEMeasurable f μ)
  proof: by
  rw [← trimmed]; rw [OuterMeasure.trim_eq_trim_iff]
  intro s hs
  simp [hf, hs]

中文:
定理 map_toOuterMeasure
  条件: (hf : AEMeasurable f μ)
  证明: by
  rw [← trimmed]; rw [OuterMeasure.trim_eq_trim_iff]
  intro s hs
  simp [hf, hs]

Depends on / 依赖: OuterMeasure, OuterMeasure.trim_eq_trim_iff, trim_eq_trim_iff, trimmed
-/
theorem map_toOuterMeasure (hf : AEMeasurable f μ) :
    (μ.map f).toOuterMeasure = (OuterMeasure.map f μ.toOuterMeasure).trim := by
  rw [← trimmed]; rw [OuterMeasure.trim_eq_trim_iff]
  intro s hs
  simp [hf, hs]

/--
lemma `map_eq_zero_iff` / 引理 `map_eq_zero_iff`

English:
lemma map_eq_zero_iff
  given: (hf : AEMeasurable f μ)
  statement: μ.map f = 0 ↔ μ = 0
  proof: by
  simp_rw [← measure_univ_eq_zero, map_apply_of_aemeasurable hf .univ, preimage_univ]

中文:
引理 map_eq_zero_iff
  条件: (hf : AEMeasurable f μ)
  结论: μ.map f = 0 ↔ μ = 0
  证明: by
  simp_rw [← measure_univ_eq_zero, map_apply_of_aemeasurable hf .univ, preimage_univ]
-/
@[simp] lemma map_eq_zero_iff (hf : AEMeasurable f μ) : μ.map f = 0 ↔ μ = 0 := by
  simp_rw [← measure_univ_eq_zero, map_apply_of_aemeasurable hf .univ, preimage_univ]

/--
lemma `mapₗ_eq_zero_iff` / 引理 `mapₗ_eq_zero_iff`

English:
lemma mapₗ_eq_zero_iff
  given: (hf : Measurable f)
  statement: Measure.mapₗ f μ = 0 ↔ μ = 0
  proof: by
  rw [mapₗ_apply_of_measurable hf]; rw [map_eq_zero_iff hf.aemeasurable]

中文:
引理 mapₗ_eq_zero_iff
  条件: (hf : Measurable f)
  结论: Measure.mapₗ f μ = 0 ↔ μ = 0
  证明: by
  rw [mapₗ_apply_of_measurable hf]; rw [map_eq_zero_iff hf.aemeasurable]
-/
@[simp] lemma mapₗ_eq_zero_iff (hf : Measurable f) : Measure.mapₗ f μ = 0 ↔ μ = 0 := by
  rw [mapₗ_apply_of_measurable hf]; rw [map_eq_zero_iff hf.aemeasurable]

/--
lemma `measure_preimage_of_map_eq_self` / 引理 `measure_preimage_of_map_eq_self`

English:
lemma measure_preimage_of_map_eq_self
  statement: {f : α -> α} (hf : map f μ = μ)
  proof: by
  if hfm : AEMeasurable f μ then
    rw [← map_apply₀ hfm]; rw [hf]
    rwa [hf]
  else
    rw [map_of_not_aemeasurable hfm] at hf
    simp [← hf]

中文:
引理 measure_preimage_of_map_eq_self
  结论: {f : α -> α} (hf : map f μ = μ)
  证明: by
  if hfm : AEMeasurable f μ then
    rw [← map_apply₀ hfm]; rw [hf]
    rwa [hf]
  else
    rw [map_of_not_aemeasurable hfm] at hf
    simp [← hf]

Depends on / 依赖: AEMeasurable, map_of_not_aemeasurable
-/
lemma measure_preimage_of_map_eq_self {f : α -> α} (hf : map f μ = μ)
    {s : Set α} (hs : NullMeasurableSet s μ) : μ (f ⁻¹' s) = μ s := by
  if hfm : AEMeasurable f μ then
    rw [← map_apply₀ hfm]; rw [hf]
    rwa [hf]
  else
    rw [map_of_not_aemeasurable hfm] at hf
    simp [← hf]

/--
lemma `map_ne_zero_iff` / 引理 `map_ne_zero_iff`

English:
lemma map_ne_zero_iff
  given: (hf : AEMeasurable f μ)
  statement: μ.map f != 0 ↔ μ != 0
  proof: (map_eq_zero_iff hf).not

中文:
引理 map_ne_zero_iff
  条件: (hf : AEMeasurable f μ)
  结论: μ.map f != 0 ↔ μ != 0
  证明: (map_eq_zero_iff hf).not

Depends on / 依赖: map_eq_zero_iff
-/
lemma map_ne_zero_iff (hf : AEMeasurable f μ) : μ.map f != 0 ↔ μ != 0 := (map_eq_zero_iff hf).not
/--
lemma `mapₗ_ne_zero_iff` / 引理 `mapₗ_ne_zero_iff`

English:
lemma mapₗ_ne_zero_iff
  given: (hf : Measurable f)
  statement: Measure.mapₗ f μ != 0 ↔ μ != 0
  proof: (mapₗ_eq_zero_iff hf).not

@[simp]

中文:
引理 mapₗ_ne_zero_iff
  条件: (hf : Measurable f)
  结论: Measure.mapₗ f μ != 0 ↔ μ != 0
  证明: (mapₗ_eq_zero_iff hf).not

@[simp]
-/
lemma mapₗ_ne_zero_iff (hf : Measurable f) : Measure.mapₗ f μ != 0 ↔ μ != 0 :=
  (mapₗ_eq_zero_iff hf).not

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map id μ = μ
  proof: ext fun _ => map_apply measurable_id

@[simp]

中文:
定理 map_id
  结论: map id μ = μ
  证明: ext fun _ => map_apply measurable_id

@[simp]

Depends on / 依赖: Preorder, Preorder.lift, ULift.down, map_apply, measurable_id
-/
theorem map_id : map id μ = μ :=
  ext fun _ => map_apply measurable_id

@[simp]
/--
theorem `map_id'` / 定理 `map_id'`

English:
theorem map_id'
  statement: map (fun x => x) μ = μ
  proof: map_id

中文:
定理 map_id'
  结论: map (fun x => x) μ = μ
  证明: map_id

Depends on / 依赖: PartialOrder, PartialOrder.lift, ULift.down, ULift.down_injective, down_injective, map_id
-/
theorem map_id' : map (fun x => x) μ = μ :=
  map_id

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: {g : β -> γ} {f : α -> β} (hg : Measurable g) (hf : Measurable f)
  proof: ext fun s hs => by simp [hf, hg, hs, hg hs, hg.comp hf, ← preimage_comp]

@[gcongr, mono]

中文:
定理 map_map
  条件: {g : β -> γ} {f : α -> β} (hg : Measurable g) (hf : Measurable f)
  证明: ext fun s hs => by simp [hf, hg, hs, hg hs, hg.comp hf, ← preimage_comp]

@[gcongr, mono]

Depends on / 依赖: hg.comp, preimage_comp
-/
theorem map_map {g : β -> γ} {f : α -> β} (hg : Measurable g) (hf : Measurable f) :
    (μ.map f).map g = μ.map (g ∘ f) :=
  ext fun s hs => by simp [hf, hg, hs, hg hs, hg.comp hf, ← preimage_comp]

@[gcongr, mono]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: {f : α -> β} (h : μ <= ν) (hf : Measurable f)
  statement: μ.map f <= ν.map f
  proof: le_iff.2 fun s hs => by simp [hf.aemeasurable, hs, h _]

中文:
定理 map_mono
  条件: {f : α -> β} (h : μ <= ν) (hf : Measurable f)
  结论: μ.map f <= ν.map f
  证明: le_iff.2 fun s hs => by simp [hf.aemeasurable, hs, h _]

Depends on / 依赖: aemeasurable, hf.aemeasurable, le_iff
-/
theorem map_mono {f : α -> β} (h : μ <= ν) (hf : Measurable f) : μ.map f <= ν.map f :=
  le_iff.2 fun s hs => by simp [hf.aemeasurable, hs, h _]

/--
theorem `le_map_apply` / 定理 `le_map_apply`

English:
theorem le_map_apply
  given: {f : α -> β} (hf : AEMeasurable f μ) (s : Set β)
  statement: μ (f ⁻¹' s) <= μ.map f s
  proof: calc
    μ (f ⁻¹' s) <= μ (f ⁻¹' toMeasurable (μ.map f) s) := by gcongr; apply subset_toMeasurable
    _ = μ.map f (toMeasurable (μ.map f) s) :=
      (map_apply_of_aemeasurable hf <| measurableSet_toMeasurable _ _).symm
    _ = μ.map f s := measure_toMeasurable _

中文:
定理 le_map_apply
  条件: {f : α -> β} (hf : AEMeasurable f μ) (s : Set β)
  结论: μ (f ⁻¹' s) <= μ.map f s
  证明: calc
    μ (f ⁻¹' s) <= μ (f ⁻¹' toMeasurable (μ.map f) s) := by gcongr; apply subset_toMeasurable
    _ = μ.map f (toMeasurable (μ.map f) s) :=
      (map_apply_of_aemeasurable hf <| measurableSet_toMeasurable _ _).symm
    _ = μ.map f s := measure_toMeasurable _

Depends on / 依赖: map_apply_of_aemeasurable, measurableSet_toMeasurable, measure_toMeasurable, subset_toMeasurable, toMeasurable
-/
theorem le_map_apply {f : α -> β} (hf : AEMeasurable f μ) (s : Set β) : μ (f ⁻¹' s) <= μ.map f s :=
  calc
    μ (f ⁻¹' s) <= μ (f ⁻¹' toMeasurable (μ.map f) s) := by gcongr; apply subset_toMeasurable
    _ = μ.map f (toMeasurable (μ.map f) s) :=
      (map_apply_of_aemeasurable hf <| measurableSet_toMeasurable _ _).symm
    _ = μ.map f s := measure_toMeasurable _

/--
theorem `le_map_apply_image` / 定理 `le_map_apply_image`

English:
theorem le_map_apply_image
  given: {f : α -> β} (hf : AEMeasurable f μ) (s : Set α)
  proof: (measure_mono (subset_preimage_image f s)).trans (le_map_apply hf _)

中文:
定理 le_map_apply_image
  条件: {f : α -> β} (hf : AEMeasurable f μ) (s : Set α)
  证明: (measure_mono (subset_preimage_image f s)).trans (le_map_apply hf _)

Depends on / 依赖: le_map_apply, measure_mono, subset_preimage_image
-/
theorem le_map_apply_image {f : α -> β} (hf : AEMeasurable f μ) (s : Set α) :
    μ s <= μ.map f (f '' s) :=
  (measure_mono (subset_preimage_image f s)).trans (le_map_apply hf _)

/--
theorem `preimage_null_of_map_null` / 定理 `preimage_null_of_map_null`

English:
theorem preimage_null_of_map_null
  statement: {f : α -> β} (hf : AEMeasurable f μ) {s : Set β}
  proof: nonpos_iff_eq_zero.mp (le_map_apply hf s).trans_eq hs

中文:
定理 preimage_null_of_map_null
  结论: {f : α -> β} (hf : AEMeasurable f μ) {s : Set β}
  证明: nonpos_iff_eq_zero.mp (le_map_apply hf s).trans_eq hs

Depends on / 依赖: le_map_apply, nonpos_iff_eq_zero, nonpos_iff_eq_zero.mp, trans_eq
-/
theorem preimage_null_of_map_null {f : α -> β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : μ.map f s = 0) : μ (f ⁻¹' s) = 0 :=
nonpos_iff_eq_zero.mp (le_map_apply hf s).trans_eq hs

/--
theorem `tendsto_ae_map` / 定理 `tendsto_ae_map`

English:
theorem tendsto_ae_map
  given: {f : α -> β} (hf : AEMeasurable f μ)
  statement: Tendsto f (ae μ) (ae (μ.map f))
  proof: fun _ hs => preimage_null_of_map_null hf hs

中文:
定理 tendsto_ae_map
  条件: {f : α -> β} (hf : AEMeasurable f μ)
  结论: Tendsto f (ae μ) (ae (μ.map f))
  证明: fun _ hs => preimage_null_of_map_null hf hs

Depends on / 依赖: preimage_null_of_map_null
-/
theorem tendsto_ae_map {f : α -> β} (hf : AEMeasurable f μ) : Tendsto f (ae μ) (ae (μ.map f)) :=
  fun _ hs => preimage_null_of_map_null hf hs

end Measure

open Measure

/--
theorem `mem_ae_map_iff` / 定理 `mem_ae_map_iff`

English:
theorem mem_ae_map_iff
  given: {f : α -> β} (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s)
  proof: by
  simp only [mem_ae_iff, map_apply_of_aemeasurable hf hs.compl, preimage_compl]

中文:
定理 mem_ae_map_iff
  条件: {f : α -> β} (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s)
  证明: by
  simp only [mem_ae_iff, map_apply_of_aemeasurable hf hs.compl, preimage_compl]

Depends on / 依赖: hs.compl, map_apply_of_aemeasurable, mem_ae_iff, preimage_compl
-/
theorem mem_ae_map_iff {f : α -> β} (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    s in ae (μ.map f) ↔ f ⁻¹' s in ae μ := by
  simp only [mem_ae_iff, map_apply_of_aemeasurable hf hs.compl, preimage_compl]

/--
theorem `mem_ae_of_mem_ae_map` / 定理 `mem_ae_of_mem_ae_map`

English:
theorem mem_ae_of_mem_ae_map
  statement: {f : α -> β} (hf : AEMeasurable f μ) {s : Set β}
  proof: (tendsto_ae_map hf).eventually hs

中文:
定理 mem_ae_of_mem_ae_map
  结论: {f : α -> β} (hf : AEMeasurable f μ) {s : Set β}
  证明: (tendsto_ae_map hf).eventually hs

Depends on / 依赖: eventually, tendsto_ae_map
-/
theorem mem_ae_of_mem_ae_map {f : α -> β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : s in ae (μ.map f)) : f ⁻¹' s in ae μ :=
  (tendsto_ae_map hf).eventually hs

/--
theorem `ae_map_iff` / 定理 `ae_map_iff`

English:
theorem ae_map_iff
  statement: {f : α -> β} (hf : AEMeasurable f μ) {p : β -> Prop}
  proof: mem_ae_map_iff hf hp

中文:
定理 ae_map_iff
  结论: {f : α -> β} (hf : AEMeasurable f μ) {p : β -> 命题}
  证明: mem_ae_map_iff hf hp

Depends on / 依赖: IsWellFounded, IsWellFounded.wf.onFun, mem_ae_map_iff
-/
theorem ae_map_iff {f : α -> β} (hf : AEMeasurable f μ) {p : β -> Prop}
    (hp : MeasurableSet { x | p x }) : (forallᵐ y ∂μ.map f, p y) ↔ forallᵐ x ∂μ, p (f x) :=
  mem_ae_map_iff hf hp

/--
theorem `ae_of_ae_map` / 定理 `ae_of_ae_map`

English:
theorem ae_of_ae_map
  given: {f : α -> β} (hf : AEMeasurable f μ) {p : β -> Prop} (h : forallᵐ y ∂μ.map f, p y)
  proof: mem_ae_of_mem_ae_map hf h

中文:
定理 ae_of_ae_map
  条件: {f : α -> β} (hf : AEMeasurable f μ) {p : β -> 命题} (h : 对任意ᵐ y ∂μ.map f, p y)
  证明: mem_ae_of_mem_ae_map hf h

Depends on / 依赖: mem_ae_of_mem_ae_map
-/
theorem ae_of_ae_map {f : α -> β} (hf : AEMeasurable f μ) {p : β -> Prop} (h : forallᵐ y ∂μ.map f, p y) :
    forallᵐ x ∂μ, p (f x) :=
  mem_ae_of_mem_ae_map hf h

/--
theorem `ae_map_mem_range` / 定理 `ae_map_mem_range`

English:
theorem ae_map_mem_range
  statement: {m0 : MeasurableSpace α} (f : α -> β) (hf : MeasurableSet (range f))
  proof: by
  by_cases h : AEMeasurable f μ
  · change range f in ae (μ.map f)
    rw [mem_ae_map_iff h hf]
    filter_upwards using mem_range_self
  · simp [map_of_not_aemeasurable h]

中文:
定理 ae_map_mem_range
  结论: {m0 : MeasurableSpace α} (f : α -> β) (hf : MeasurableSet (range f))
  证明: by
  by_cases h : AEMeasurable f μ
  · change range f in ae (μ.map f)
    rw [mem_ae_map_iff h hf]
    filter_upwards using mem_range_self
  · simp [map_of_not_aemeasurable h]

Depends on / 依赖: AEMeasurable, filter_upwards, map_of_not_aemeasurable, mem_ae_map_iff, mem_range_self
-/
theorem ae_map_mem_range {m0 : MeasurableSpace α} (f : α -> β) (hf : MeasurableSet (range f))
    (μ : Measure α) : forallᵐ x ∂μ.map f, x in range f := by
  by_cases h : AEMeasurable f μ
  · change range f in ae (μ.map f)
    rw [mem_ae_map_iff h hf]
    filter_upwards using mem_range_self
  · simp [map_of_not_aemeasurable h]

end MeasureTheory

namespace MeasurableEmbedding

open MeasureTheory Measure

variable {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} {f : α -> β} {μ ν : Measure α}

nonrec theorem map_apply (hf : MeasurableEmbedding f) (μ : Measure α) (s : Set β) :
    μ.map f s = μ (f ⁻¹' s) := by
  refine le_antisymm ?_ (le_map_apply hf.measurable.aemeasurable s)
  set t := f '' toMeasurable μ (f ⁻¹' s) union (range f)ᶜ
  have htm : MeasurableSet t :=
    (hf.measurableSet_image.2 <| measurableSet_toMeasurable _ _).union
      hf.measurableSet_range.compl
  have hst : s subseteq t := by
    rw [subset_union_compl_iff_inter_subset]; rw [← image_preimage_eq_inter_range]
    exact image_mono (subset_toMeasurable _ _)
  have hft : f ⁻¹' t = toMeasurable μ (f ⁻¹' s) := by
    rw [preimage_union]; rw [preimage_compl]; rw [preimage_range]; rw [compl_univ]; rw [union_empty]; rw [hf.injective.preimage_image]
  calc
    μ.map f s <= μ.map f t := by gcongr
    _ = μ (f ⁻¹' s) := by rw [map_apply hf.measurable htm, hft, measure_toMeasurable]

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: (hf : MeasurableEmbedding f)
  statement: Function.Injective (Measure.map f)
  proof: by
  intro μ ν h
  ext s hs
  rw [← Set.preimage_image_eq s hf.injective]; rw [← hf.map_apply]; rw [← hf.map_apply]
  congr

中文:
定理 map_injective
  条件: (hf : MeasurableEmbedding f)
  结论: Function.Injective (Measure.map f)
  证明: by
  intro μ ν h
  ext s hs
  rw [← Set.preimage_image_eq s hf.injective]; rw [← hf.map_apply]; rw [← hf.map_apply]
  congr

Depends on / 依赖: Set.preimage_image_eq, hf.injective, hf.map_apply, injective, map_apply, preimage_image_eq
-/
theorem map_injective (hf : MeasurableEmbedding f) : Function.Injective (Measure.map f) := by
  intro μ ν h
  ext s hs
  rw [← Set.preimage_image_eq s hf.injective]; rw [← hf.map_apply]; rw [← hf.map_apply]
  congr

end MeasurableEmbedding

namespace MeasurableEquiv

/-! Interactions of measurable equivalences and measures -/

open Equiv MeasureTheory MeasureTheory.Measure

variable {_ : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: (f : α ≃ᵐ β) (s : Set β)
  statement: μ.map f s = μ (f ⁻¹' s)
  proof: f.measurableEmbedding.map_apply _ _

@[simp]

中文:
定理 map_apply
  条件: (f : α ≃ᵐ β) (s : Set β)
  结论: μ.map f s = μ (f ⁻¹' s)
  证明: f.measurableEmbedding.map_apply _ _

@[simp]
-/
protected theorem map_apply (f : α ≃ᵐ β) (s : Set β) : μ.map f s = μ (f ⁻¹' s) :=
  f.measurableEmbedding.map_apply _ _

@[simp]
/--
theorem `map_symm_map` / 定理 `map_symm_map`

English:
theorem map_symm_map
  given: (e : α ≃ᵐ β)
  statement: (μ.map e).map e.symm = μ
  proof: by
  simp [map_map e.symm.measurable e.measurable]

@[simp]

中文:
定理 map_symm_map
  条件: (e : α ≃ᵐ β)
  结论: (μ.map e).map e.symm = μ
  证明: by
  simp [map_map e.symm.measurable e.measurable]

@[simp]

Depends on / 依赖: e.measurable, e.symm.measurable, map_map, measurable
-/
theorem map_symm_map (e : α ≃ᵐ β) : (μ.map e).map e.symm = μ := by
  simp [map_map e.symm.measurable e.measurable]

@[simp]
/--
theorem `map_map_symm` / 定理 `map_map_symm`

English:
theorem map_map_symm
  given: (e : α ≃ᵐ β)
  statement: (ν.map e.symm).map e = ν
  proof: by
  simp [map_map e.measurable e.symm.measurable]

中文:
定理 map_map_symm
  条件: (e : α ≃ᵐ β)
  结论: (ν.map e.symm).map e = ν
  证明: by
  simp [map_map e.measurable e.symm.measurable]

Depends on / 依赖: e.measurable, e.symm.measurable, map_map, measurable
-/
theorem map_map_symm (e : α ≃ᵐ β) : (ν.map e.symm).map e = ν := by
  simp [map_map e.measurable e.symm.measurable]

/--
theorem `map_measurableEquiv_injective` / 定理 `map_measurableEquiv_injective`

English:
theorem map_measurableEquiv_injective
  given: (e : α ≃ᵐ β)
  statement: Injective (Measure.map e)
  proof: by
  intro μ₁ μ₂ hμ
  apply_fun Measure.map e.symm at hμ
  simpa [map_symm_map e] using hμ

中文:
定理 map_measurableEquiv_injective
  条件: (e : α ≃ᵐ β)
  结论: Injective (Measure.map e)
  证明: by
  intro μ₁ μ₂ hμ
  apply_fun Measure.map e.symm at hμ
  simpa [map_symm_map e] using hμ

Depends on / 依赖: Measure, Measure.map, apply_fun, e.symm, map_symm_map
-/
theorem map_measurableEquiv_injective (e : α ≃ᵐ β) : Injective (Measure.map e) := by
  intro μ₁ μ₂ hμ
  apply_fun Measure.map e.symm at hμ
  simpa [map_symm_map e] using hμ

/--
theorem `map_apply_eq_iff_map_symm_apply_eq` / 定理 `map_apply_eq_iff_map_symm_apply_eq`

English:
theorem map_apply_eq_iff_map_symm_apply_eq
  given: (e : α ≃ᵐ β)
  statement: μ.map e = ν ↔ μ = ν.map e.symm
  proof: by
  rw [← (map_measurableEquiv_injective e).eq_iff]; rw [map_map_symm]

中文:
定理 map_apply_eq_iff_map_symm_apply_eq
  条件: (e : α ≃ᵐ β)
  结论: μ.map e = ν ↔ μ = ν.map e.symm
  证明: by
  rw [← (map_measurableEquiv_injective e).eq_iff]; rw [map_map_symm]

Depends on / 依赖: eq_iff, map_map_symm, map_measurableEquiv_injective
-/
theorem map_apply_eq_iff_map_symm_apply_eq (e : α ≃ᵐ β) : μ.map e = ν ↔ μ = ν.map e.symm := by
  rw [← (map_measurableEquiv_injective e).eq_iff]; rw [map_map_symm]

/--
theorem `map_ae` / 定理 `map_ae`

English:
theorem map_ae
  given: (f : α ≃ᵐ β) (μ : Measure α)
  statement: Filter.map f (ae μ) = ae (map f μ)
  proof: by
  ext s
  simp_rw [mem_map, mem_ae_iff, ← preimage_compl, f.map_apply]

中文:
定理 map_ae
  条件: (f : α ≃ᵐ β) (μ : Measure α)
  结论: Filter.map f (ae μ) = ae (map f μ)
  证明: by
  ext s
  simp_rw [mem_map, mem_ae_iff, ← preimage_compl, f.map_apply]

Depends on / 依赖: f.map_apply, map_apply, mem_ae_iff, mem_map, preimage_compl, simp_rw
-/
theorem map_ae (f : α ≃ᵐ β) (μ : Measure α) : Filter.map f (ae μ) = ae (map f μ) := by
  ext s
  simp_rw [mem_map, mem_ae_iff, ← preimage_compl, f.map_apply]

end MeasurableEquiv
