/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Comap

/-!
# Restricting a measure to a subset or a subtype

Given a measure `μ` on a type `α` and a subset `s` of `α`, we define a measure `μ.restrict s` as
the restriction of `μ` to `s` (still as a measure on `α`).

We investigate how this notion interacts with usual operations on measures (sum, pushforward,
pullback), and on sets (inclusion, union, Union).

We also study the relationship between the restriction of a measure to a subtype (given by the
pullback under `Subtype.val`) and the restriction to a set as above.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open Set MeasureTheory Measure Filter MeasurableSpace ENNReal Function

variable {R α β δ γ ι : Type*}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]
variable {μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : Measure α} {s s' t : Set α}

namespace Measure

/-! ### Restricting a measure -/

/-- Restrict a measure `μ` to a set `s` as an `ℝ≥0∞`-linear map. -/
@[irreducible]
/--
Definition of `restrictₗ` / `restrictₗ` 的定义

English:
definition restrictₗ
  signature: {m0 : MeasurableSpace α} (s : Set α)
  body: liftLinear (OuterMeasure.restrict s) fun μ s' hs' t => by
    suffices μ (s inter t) = μ (s inter t inter s') + μ ((s inter t) \ s') by
      simpa [← Set.inter_assoc, Set.inter_comm _ s, ← inter_sdiff_assoc]
    exact le_toOuterMeasure_caratheodory _ _ hs' _

中文:
定义 restrictₗ
  签名: {m0 : 可测空间 α} (s : 集合 α)
  定义体: liftLinear (OuterMeasure.restrict s) fun μ s' hs' t => by
    suffices μ (s inter t) = μ (s inter t inter s') + μ ((s inter t) \ s') by
      simpa [← Set.inter_assoc, Set.inter_comm _ s, ← inter_sdiff_assoc]
    exact le_toOuterMeasure_caratheodory _ _ hs' _

Depends on / 依赖: OuterMeasure, OuterMeasure.restrict, Set.inter_assoc, Set.inter_comm, inter_assoc, inter_comm, inter_sdiff_assoc, le_toOuterMeasure_caratheodory, liftLinear, restrict
-/
noncomputable def restrictₗ {m0 : MeasurableSpace α} (s : Set α) : Measure α ->ₗ[Real>=0∞] Measure α :=
  liftLinear (OuterMeasure.restrict s) fun μ s' hs' t => by
    suffices μ (s inter t) = μ (s inter t inter s') + μ ((s inter t) \ s') by
      simpa [← Set.inter_assoc, Set.inter_comm _ s, ← inter_sdiff_assoc]
    exact le_toOuterMeasure_caratheodory _ _ hs' _

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: {_m0 : MeasurableSpace α} (μ : Measure α) (s : Set α)
  body: restrictₗ s μ

@[simp]

中文:
定义 restrict
  签名: {_m0 : 可测空间 α} (μ : 测度 α) (s : 集合 α)
  定义体: restrictₗ s μ

@[simp]
-/
noncomputable def restrict {_m0 : MeasurableSpace α} (μ : Measure α) (s : Set α) : Measure α :=
  restrictₗ s μ

@[simp]
/--
theorem `restrictₗ_apply` / 定理 `restrictₗ_apply`

English:
theorem restrictₗ_apply
  given: {_m0 : MeasurableSpace α} (s : Set α) (μ : Measure α)
  proof: rfl

中文:
定理 restrictₗ_apply
  条件: {_m0 : 可测空间 α} (s : 集合 α) (μ : 测度 α)
  证明: rfl
-/
theorem restrictₗ_apply {_m0 : MeasurableSpace α} (s : Set α) (μ : Measure α) :
    restrictₗ s μ = μ.restrict s :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `restrict_toOuterMeasure_eq_toOuterMeasure_restrict` / 定理 `restrict_toOuterMeasure_eq_toOuterMeasure_restrict`

English:
theorem restrict_toOuterMeasure_eq_toOuterMeasure_restrict
  given: (h : MeasurableSet s)
  proof: by
  simp_rw [restrict, restrictₗ, liftLinear, LinearMap.coe_mk, AddHom.coe_mk,
    toMeasure_toOuterMeasure, OuterMeasure.restrict_trim h, μ.trimmed]

中文:
定理 restrict_toOuterMeasure_eq_toOuterMeasure_restrict
  条件: (h : 可测集 s)
  证明: by
  simp_rw [restrict, restrictₗ, liftLinear, LinearMap.coe_mk, AddHom.coe_mk,
    toMeasure_toOuterMeasure, OuterMeasure.restrict_trim h, μ.trimmed]

Depends on / 依赖: AddHom, AddHom.coe_mk, LinearMap, LinearMap.coe_mk, OuterMeasure, OuterMeasure.restrict_trim, coe_mk, liftLinear, restrict, restrict_trim, simp_rw, toMeasure_toOuterMeasure, trimmed
-/
theorem restrict_toOuterMeasure_eq_toOuterMeasure_restrict (h : MeasurableSet s) :
    (μ.restrict s).toOuterMeasure = OuterMeasure.restrict s μ.toOuterMeasure := by
  simp_rw [restrict, restrictₗ, liftLinear, LinearMap.coe_mk, AddHom.coe_mk,
    toMeasure_toOuterMeasure, OuterMeasure.restrict_trim h, μ.trimmed]

/--
theorem `restrict_apply₀` / 定理 `restrict_apply₀`

English:
theorem restrict_apply₀
  given: (ht : NullMeasurableSet t (μ.restrict s))
  statement: μ.restrict s t = μ (t inter s)
  proof: by
  rw [restrict]; rw [restrictₗ] at ht
  rw [← restrictₗ_apply]; rw [restrictₗ]; rw [liftLinear_apply₀ _ ht]; rw [OuterMeasure.restrict_apply]; rw [coe_toOuterMeasure]

中文:
定理 restrict_apply₀
  条件: (ht : NullMeasurableSet t (μ.restrict s))
  结论: μ.restrict s t = μ (t inter s)
  证明: by
  rw [restrict]; rw [restrictₗ] at ht
  rw [← restrictₗ_apply]; rw [restrictₗ]; rw [liftLinear_apply₀ _ ht]; rw [OuterMeasure.restrict_apply]; rw [coe_toOuterMeasure]

Depends on / 依赖: OuterMeasure, OuterMeasure.restrict_apply, coe_toOuterMeasure, restrict, restrict_apply
-/
theorem restrict_apply₀ (ht : NullMeasurableSet t (μ.restrict s)) : μ.restrict s t = μ (t inter s) := by
  rw [restrict]; rw [restrictₗ] at ht
  rw [← restrictₗ_apply]; rw [restrictₗ]; rw [liftLinear_apply₀ _ ht]; rw [OuterMeasure.restrict_apply]; rw [coe_toOuterMeasure]

/-- If `t` is a measurable set, then the measure of `t` with respect to the restriction of
  the measure to `s` equals the outer measure of `t ∩ s`. An alternate version requiring that `s`
  be measurable instead of `t` exists as `Measure.restrict_apply'`. -/
@[simp]
/--
theorem `restrict_apply` / 定理 `restrict_apply`

English:
theorem restrict_apply
  given: (ht : MeasurableSet t)
  statement: μ.restrict s t = μ (t inter s)
  proof: restrict_apply₀ ht.nullMeasurableSet

中文:
定理 restrict_apply
  条件: (ht : 可测集 t)
  结论: μ.restrict s t = μ (t inter s)
  证明: restrict_apply₀ ht.nullMeasurableSet

Depends on / 依赖: ht.nullMeasurableSet, nullMeasurableSet
-/
theorem restrict_apply (ht : MeasurableSet t) : μ.restrict s t = μ (t inter s) :=
  restrict_apply₀ ht.nullMeasurableSet

/--
theorem `restrict_mono'` / 定理 `restrict_mono'`

English:
theorem restrict_mono'
  given: {_m0 : MeasurableSpace α} ⦃s s'
  statement: Set α⦄ ⦃μ ν : Measure α⦄ (hs : s <=ᵐ[μ] s')
  proof: Measure.le_iff.2 fun t ht => calc
    μ.restrict s t = μ (t inter s) := restrict_apply ht
    _ <= μ (t inter s') := (measure_mono_ae <| hs.mono fun _x hx ⟨hxt, hxs⟩ => ⟨hxt, hx hxs⟩)
    _ <= ν (t inter s') := le_iff'.1 hμν (t inter s')
    _ = ν.restrict s' t := (restrict_apply ht).symm

中文:
定理 restrict_mono'
  条件: {_m0 : 可测空间 α} ⦃s s'
  结论: 集合 α⦄ ⦃μ ν : 测度 α⦄ (hs : s <=ᵐ[μ] s')
  证明: Measure.le_iff.2 fun t ht => calc
    μ.restrict s t = μ (t inter s) := restrict_apply ht
    _ <= μ (t inter s') := (measure_mono_ae <| hs.mono fun _x hx ⟨hxt, hxs⟩ => ⟨hxt, hx hxs⟩)
    _ <= ν (t inter s') := le_iff'.1 hμν (t inter s')
    _ = ν.restrict s' t := (restrict_apply ht).symm

Depends on / 依赖: Measure, Measure.le_iff, hs.mono, le_iff, measure_mono_ae, restrict, restrict_apply
-/
theorem restrict_mono' {_m0 : MeasurableSpace α} ⦃s s' : Set α⦄ ⦃μ ν : Measure α⦄ (hs : s <=ᵐ[μ] s')
    (hμν : μ <= ν) : μ.restrict s <= ν.restrict s' :=
  Measure.le_iff.2 fun t ht => calc
    μ.restrict s t = μ (t inter s) := restrict_apply ht
    _ <= μ (t inter s') := (measure_mono_ae <| hs.mono fun _x hx ⟨hxt, hxs⟩ => ⟨hxt, hx hxs⟩)
    _ <= ν (t inter s') := le_iff'.1 hμν (t inter s')
    _ = ν.restrict s' t := (restrict_apply ht).symm

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
@[mono, gcongr]
/--
theorem `restrict_mono` / 定理 `restrict_mono`

English:
theorem restrict_mono
  given: {_m0 : MeasurableSpace α} ⦃s s'
  statement: Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄
  proof: restrict_mono' (ae_of_all _ hs) hμν

中文:
定理 restrict_mono
  条件: {_m0 : 可测空间 α} ⦃s s'
  结论: 集合 α⦄ (hs : s subseteq s') ⦃μ ν : 测度 α⦄
  证明: restrict_mono' (ae_of_all _ hs) hμν

Depends on / 依赖: ae_of_all, restrict_mono
-/
theorem restrict_mono {_m0 : MeasurableSpace α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄
    (hμν : μ <= ν) : μ.restrict s <= ν.restrict s' :=
  restrict_mono' (ae_of_all _ hs) hμν

/--
theorem `restrict_mono_measure` / 定理 `restrict_mono_measure`

English:
theorem restrict_mono_measure
  given: {_ : MeasurableSpace α} {μ ν : Measure α} (h : μ <= ν) (s : Set α)
  proof: restrict_mono subset_rfl h

中文:
定理 restrict_mono_measure
  条件: {_ : 可测空间 α} {μ ν : 测度 α} (h : μ <= ν) (s : 集合 α)
  证明: restrict_mono subset_rfl h

Depends on / 依赖: restrict_mono, subset_rfl
-/
theorem restrict_mono_measure {_ : MeasurableSpace α} {μ ν : Measure α} (h : μ <= ν) (s : Set α) :
    μ.restrict s <= ν.restrict s :=
  restrict_mono subset_rfl h

/--
theorem `restrict_mono_set` / 定理 `restrict_mono_set`

English:
theorem restrict_mono_set
  given: {_ : MeasurableSpace α} (μ : Measure α) {s t : Set α} (h : s subseteq t)
  proof: restrict_mono h le_rfl

中文:
定理 restrict_mono_set
  条件: {_ : 可测空间 α} (μ : 测度 α) {s t : 集合 α} (h : s subseteq t)
  证明: restrict_mono h le_rfl

Depends on / 依赖: le_rfl, restrict_mono
-/
theorem restrict_mono_set {_ : MeasurableSpace α} (μ : Measure α) {s t : Set α} (h : s subseteq t) :
    μ.restrict s <= μ.restrict t :=
  restrict_mono h le_rfl

/--
theorem `restrict_mono_ae` / 定理 `restrict_mono_ae`

English:
theorem restrict_mono_ae
  given: (h : s <=ᵐ[μ] t)
  statement: μ.restrict s <= μ.restrict t
  proof: restrict_mono' h (le_refl μ)

中文:
定理 restrict_mono_ae
  条件: (h : s <=ᵐ[μ] t)
  结论: μ.restrict s <= μ.restrict t
  证明: restrict_mono' h (le_refl μ)

Depends on / 依赖: le_refl, restrict_mono
-/
theorem restrict_mono_ae (h : s <=ᵐ[μ] t) : μ.restrict s <= μ.restrict t :=
  restrict_mono' h (le_refl μ)

/--
theorem `restrict_congr_set` / 定理 `restrict_congr_set`

English:
theorem restrict_congr_set
  given: (h : s =ᵐ[μ] t)
  statement: μ.restrict s = μ.restrict t
  proof: le_antisymm (restrict_mono_ae h.le) (restrict_mono_ae h.symm.le)

中文:
定理 restrict_congr_set
  条件: (h : s =ᵐ[μ] t)
  结论: μ.restrict s = μ.restrict t
  证明: le_antisymm (restrict_mono_ae h.le) (restrict_mono_ae h.symm.le)

Depends on / 依赖: BddOrd, ConcreteCategory, ConcreteCategory.hom, h.le, h.symm.le, le_antisymm, restrict_mono_ae
-/
theorem restrict_congr_set (h : s =ᵐ[μ] t) : μ.restrict s = μ.restrict t :=
  le_antisymm (restrict_mono_ae h.le) (restrict_mono_ae h.symm.le)

/-- If `s` is a measurable set, then the outer measure of `t` with respect to the restriction of
the measure to `s` equals the outer measure of `t ∩ s`. This is an alternate version of
`Measure.restrict_apply`, requiring that `s` is measurable instead of `t`. -/
@[simp]
/--
theorem `restrict_apply'` / 定理 `restrict_apply'`

English:
theorem restrict_apply'
  given: (hs : MeasurableSet s)
  statement: μ.restrict s t = μ (t inter s)
  proof: by
  rw [← toOuterMeasure_apply]; rw [Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict hs]; rw [OuterMeasure.restrict_apply s t _]; rw [toOuterMeasure_apply]

中文:
定理 restrict_apply'
  条件: (hs : 可测集 s)
  结论: μ.restrict s t = μ (t inter s)
  证明: by
  rw [← toOuterMeasure_apply]; rw [Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict hs]; rw [OuterMeasure.restrict_apply s t _]; rw [toOuterMeasure_apply]

Depends on / 依赖: Measure, Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict, OuterMeasure, OuterMeasure.restrict_apply, restrict_apply, restrict_toOuterMeasure_eq_toOuterMeasure_restrict, toOuterMeasure_apply
-/
theorem restrict_apply' (hs : MeasurableSet s) : μ.restrict s t = μ (t inter s) := by
  rw [← toOuterMeasure_apply]; rw [Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict hs]; rw [OuterMeasure.restrict_apply s t _]; rw [toOuterMeasure_apply]

/--
theorem `_root_.IsCountablySpanning.null_of_forall_inter_null` / 定理 `_root_.IsCountablySpanning.null_of_forall_inter_null`

English:
theorem _root_.IsCountablySpanning.null_of_forall_inter_null
  statement: {C : Set (Set α)}
  proof: by
  obtain ⟨t, ht1, ht2⟩ := hC
  rw [show s = ⋃ n]; rw [s inter t n by rw [← inter_iUnion]; rw [ht2]; rw [inter_univ], measure_iUnion_null_iff]
  exact fun i => ht (t i) (ht1 i)

中文:
定理 _root_.IsCountablySpanning.null_of_对任意_inter_null
  结论: {C : 集合 (集合 α)}
  证明: by
  obtain ⟨t, ht1, ht2⟩ := hC
  rw [show s = ⋃ n]; rw [s inter t n by rw [← inter_iUnion]; rw [ht2]; rw [inter_univ], measure_iUnion_null_iff]
  exact fun i => ht (t i) (ht1 i)

Depends on / 依赖: f.hom, inter_iUnion, inter_univ, measure_iUnion_null_iff
-/
theorem _root_.IsCountablySpanning.null_of_forall_inter_null {C : Set (Set α)}
    (hC : IsCountablySpanning C) (ht : forall t in C, μ (s inter t) = 0) :
    μ s = 0 := by
  obtain ⟨t, ht1, ht2⟩ := hC
  rw [show s = ⋃ n]; rw [s inter t n by rw [← inter_iUnion]; rw [ht2]; rw [inter_univ], measure_iUnion_null_iff]
  exact fun i => ht (t i) (ht1 i)

/--
theorem `forall_measure_inter_isCountablySpanning_eq_zero` / 定理 `forall_measure_inter_isCountablySpanning_eq_zero`

English:
theorem forall_measure_inter_isCountablySpanning_eq_zero
  statement: {C : Set (Set α)}
  proof: hC.null_of_forall_inter_null
  mpr h t _ := measure_inter_null_of_null_left t h

中文:
定理 对任意_measure_inter_isCountablySpanning_eq_zero
  结论: {C : 集合 (集合 α)}
  证明: hC.null_of_forall_inter_null
  mpr h t _ := measure_inter_null_of_null_left t h

Depends on / 依赖: hC.null_of_forall_inter_null, null_of_forall_inter_null
-/
theorem forall_measure_inter_isCountablySpanning_eq_zero {C : Set (Set α)}
    (hC : IsCountablySpanning C) : (forall t in C, μ (s inter t) = 0) ↔ μ s = 0 where
  mp := hC.null_of_forall_inter_null
  mpr h t _ := measure_inter_null_of_null_left t h

/--
theorem `_root_.IsCountablySpanning.null_of_forall_restrict_null` / 定理 `_root_.IsCountablySpanning.null_of_forall_restrict_null`

English:
theorem _root_.IsCountablySpanning.null_of_forall_restrict_null
  statement: {C : Set (Set α)}
  proof: by
  rw [← forall_measure_inter_isCountablySpanning_eq_zero hC]
  intro t htc
  simpa [← μ.restrict_apply' (hm _ htc)] using ht t htc

中文:
定理 _root_.IsCountablySpanning.null_of_对任意_restrict_null
  结论: {C : 集合 (集合 α)}
  证明: by
  rw [← forall_measure_inter_isCountablySpanning_eq_zero hC]
  intro t htc
  simpa [← μ.restrict_apply' (hm _ htc)] using ht t htc

Depends on / 依赖: forall_measure_inter_isCountablySpanning_eq_zero, restrict_apply
-/
theorem _root_.IsCountablySpanning.null_of_forall_restrict_null {C : Set (Set α)}
    (hC : IsCountablySpanning C) (hm : forall t in C, MeasurableSet t)
    (ht : forall t in C, μ.restrict t s = 0) :
    μ s = 0 := by
  rw [← forall_measure_inter_isCountablySpanning_eq_zero hC]
  intro t htc
  simpa [← μ.restrict_apply' (hm _ htc)] using ht t htc

/--
theorem `restrict_apply₀'` / 定理 `restrict_apply₀'`

English:
theorem restrict_apply₀'
  given: (hs : NullMeasurableSet s μ)
  statement: μ.restrict s t = μ (t inter s)
  proof: by
  rw [← restrict_congr_set hs.toMeasurable_ae_eq]; rw [restrict_apply' (measurableSet_toMeasurable _ _)]; rw [measure_congr ((ae_eq_refl t).inter hs.toMeasurable_ae_eq)]

中文:
定理 restrict_apply₀'
  条件: (hs : NullMeasurableSet s μ)
  结论: μ.restrict s t = μ (t inter s)
  证明: by
  rw [← restrict_congr_set hs.toMeasurable_ae_eq]; rw [restrict_apply' (measurableSet_toMeasurable _ _)]; rw [measure_congr ((ae_eq_refl t).inter hs.toMeasurable_ae_eq)]

Depends on / 依赖: ae_eq_refl, hs.toMeasurable_ae_eq, measurableSet_toMeasurable, measure_congr, restrict_apply, restrict_congr_set, toMeasurable_ae_eq
-/
theorem restrict_apply₀' (hs : NullMeasurableSet s μ) : μ.restrict s t = μ (t inter s) := by
  rw [← restrict_congr_set hs.toMeasurable_ae_eq]; rw [restrict_apply' (measurableSet_toMeasurable _ _)]; rw [measure_congr ((ae_eq_refl t).inter hs.toMeasurable_ae_eq)]

/--
theorem `restrict_le_self` / 定理 `restrict_le_self`

English:
theorem restrict_le_self
  statement: μ.restrict s <= μ
  proof: Measure.le_iff.2 fun t ht => calc
    μ.restrict s t = μ (t inter s) := restrict_apply ht
    _ <= μ t := measure_mono inter_subset_left

中文:
定理 restrict_le_self
  结论: μ.restrict s <= μ
  证明: Measure.le_iff.2 fun t ht => calc
    μ.restrict s t = μ (t inter s) := restrict_apply ht
    _ <= μ t := measure_mono inter_subset_left

Depends on / 依赖: Measure, Measure.le_iff, inter_subset_left, le_iff, measure_mono, restrict, restrict_apply
-/
theorem restrict_le_self : μ.restrict s <= μ :=
  Measure.le_iff.2 fun t ht => calc
    μ.restrict s t = μ (t inter s) := restrict_apply ht
    _ <= μ t := measure_mono inter_subset_left

/--
theorem `absolutelyContinuous_restrict` / 定理 `absolutelyContinuous_restrict`

English:
theorem absolutelyContinuous_restrict
  statement: μ.restrict s ≪ μ
  proof: Measure.absolutelyContinuous_of_le Measure.restrict_le_self

中文:
定理 absolutelyContinuous_restrict
  结论: μ.restrict s ≪ μ
  证明: Measure.absolutelyContinuous_of_le Measure.restrict_le_self

Depends on / 依赖: Measure, Measure.absolutelyContinuous_of_le, Measure.restrict_le_self, absolutelyContinuous_of_le, restrict_le_self
-/
theorem absolutelyContinuous_restrict : μ.restrict s ≪ μ :=
  Measure.absolutelyContinuous_of_le Measure.restrict_le_self

variable (μ)

/--
theorem `restrict_eq_self` / 定理 `restrict_eq_self`

English:
theorem restrict_eq_self
  given: (h : s subseteq t)
  statement: μ.restrict t s = μ s
  proof: (le_iff'.1 restrict_le_self s).antisymm
    calc
      μ s <= μ (toMeasurable (μ.restrict t) s inter t) :=
        measure_mono (subset_inter (subset_toMeasurable _ _) h)
      _ = μ.restrict t s := by
        rw [← restrict_apply (measurableSet_toMeasurable _ _)]; rw [measure_toMeasurable]

@[simp]

中文:
定理 restrict_eq_self
  条件: (h : s subseteq t)
  结论: μ.restrict t s = μ s
  证明: (le_iff'.1 restrict_le_self s).antisymm
    calc
      μ s <= μ (toMeasurable (μ.restrict t) s inter t) :=
        measure_mono (subset_inter (subset_toMeasurable _ _) h)
      _ = μ.restrict t s := by
        rw [← restrict_apply (measurableSet_toMeasurable _ _)]; rw [measure_toMeasurable]

@[simp]

Depends on / 依赖: antisymm, le_iff, measurableSet_toMeasurable, measure_mono, measure_toMeasurable, restrict, restrict_apply, restrict_le_self, subset_inter, subset_toMeasurable, toMeasurable
-/
theorem restrict_eq_self (h : s subseteq t) : μ.restrict t s = μ s :=
(le_iff'.1 restrict_le_self s).antisymm
    calc
      μ s <= μ (toMeasurable (μ.restrict t) s inter t) :=
        measure_mono (subset_inter (subset_toMeasurable _ _) h)
      _ = μ.restrict t s := by
        rw [← restrict_apply (measurableSet_toMeasurable _ _)]; rw [measure_toMeasurable]

@[simp]
/--
theorem `restrict_apply_self` / 定理 `restrict_apply_self`

English:
theorem restrict_apply_self
  given: (s : Set α)
  statement: (μ.restrict s) s = μ s
  proof: restrict_eq_self μ Subset.rfl

中文:
定理 restrict_apply_self
  条件: (s : 集合 α)
  结论: (μ.restrict s) s = μ s
  证明: restrict_eq_self μ Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, restrict_eq_self
-/
theorem restrict_apply_self (s : Set α) : (μ.restrict s) s = μ s :=
  restrict_eq_self μ Subset.rfl

variable {μ}

/--
theorem `restrict_apply_univ` / 定理 `restrict_apply_univ`

English:
theorem restrict_apply_univ
  given: (s : Set α)
  statement: μ.restrict s univ = μ s
  proof: by
  rw [restrict_apply MeasurableSet.univ]; rw [Set.univ_inter]

中文:
定理 restrict_apply_univ
  条件: (s : 集合 α)
  结论: μ.restrict s univ = μ s
  证明: by
  rw [restrict_apply MeasurableSet.univ]; rw [Set.univ_inter]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Set.univ_inter, restrict_apply, univ_inter
-/
theorem restrict_apply_univ (s : Set α) : μ.restrict s univ = μ s := by
  rw [restrict_apply MeasurableSet.univ]; rw [Set.univ_inter]

/--
theorem `le_restrict_apply` / 定理 `le_restrict_apply`

English:
theorem le_restrict_apply
  given: (s t : Set α)
  statement: μ (t inter s) <= μ.restrict s t
  proof: calc
    μ (t inter s) = μ.restrict s (t inter s) := (restrict_eq_self μ inter_subset_right).symm
    _ <= μ.restrict s t := measure_mono inter_subset_left

中文:
定理 le_restrict_apply
  条件: (s t : 集合 α)
  结论: μ (t inter s) <= μ.restrict s t
  证明: calc
    μ (t inter s) = μ.restrict s (t inter s) := (restrict_eq_self μ inter_subset_right).symm
    _ <= μ.restrict s t := measure_mono inter_subset_left

Depends on / 依赖: inter_subset_left, inter_subset_right, measure_mono, restrict, restrict_eq_self
-/
theorem le_restrict_apply (s t : Set α) : μ (t inter s) <= μ.restrict s t :=
  calc
    μ (t inter s) = μ.restrict s (t inter s) := (restrict_eq_self μ inter_subset_right).symm
    _ <= μ.restrict s t := measure_mono inter_subset_left

/--
theorem `restrict_apply_le` / 定理 `restrict_apply_le`

English:
theorem restrict_apply_le
  given: (s t : Set α)
  statement: μ.restrict s t <= μ t
  proof: Measure.le_iff'.1 restrict_le_self _

中文:
定理 restrict_apply_le
  条件: (s t : 集合 α)
  结论: μ.restrict s t <= μ t
  证明: Measure.le_iff'.1 restrict_le_self _

Depends on / 依赖: Measure, Measure.le_iff, le_iff, restrict_le_self
-/
theorem restrict_apply_le (s t : Set α) : μ.restrict s t <= μ t :=
  Measure.le_iff'.1 restrict_le_self _

/--
theorem `restrict_apply_superset` / 定理 `restrict_apply_superset`

English:
theorem restrict_apply_superset
  given: (h : s subseteq t)
  statement: μ.restrict s t = μ s
  proof: ((measure_mono (subset_univ _)).trans_eq <| restrict_apply_univ _).antisymm
    ((restrict_apply_self μ s).symm.trans_le <| measure_mono h)

@[simp]

中文:
定理 restrict_apply_superset
  条件: (h : s subseteq t)
  结论: μ.restrict s t = μ s
  证明: ((measure_mono (subset_univ _)).trans_eq <| restrict_apply_univ _).antisymm
    ((restrict_apply_self μ s).symm.trans_le <| measure_mono h)

@[simp]

Depends on / 依赖: antisymm, measure_mono, restrict_apply_self, restrict_apply_univ, subset_univ, symm.trans_le, trans_eq, trans_le
-/
theorem restrict_apply_superset (h : s subseteq t) : μ.restrict s t = μ s :=
  ((measure_mono (subset_univ _)).trans_eq <| restrict_apply_univ _).antisymm
    ((restrict_apply_self μ s).symm.trans_le <| measure_mono h)

@[simp]
/--
theorem `restrict_add` / 定理 `restrict_add`

English:
theorem restrict_add
  given: {_m0 : MeasurableSpace α} (μ ν : Measure α) (s : Set α)
  proof: (restrictₗ s).map_add μ ν

@[simp]

中文:
定理 restrict_add
  条件: {_m0 : 可测空间 α} (μ ν : 测度 α) (s : 集合 α)
  证明: (restrictₗ s).map_add μ ν

@[simp]

Depends on / 依赖: map_add
-/
theorem restrict_add {_m0 : MeasurableSpace α} (μ ν : Measure α) (s : Set α) :
    (μ + ν).restrict s = μ.restrict s + ν.restrict s :=
  (restrictₗ s).map_add μ ν

@[simp]
/--
theorem `restrict_zero` / 定理 `restrict_zero`

English:
theorem restrict_zero
  given: {_m0 : MeasurableSpace α} (s : Set α)
  statement: (0 : Measure α).restrict s = 0
  proof: (restrictₗ s).map_zero

@[simp]

中文:
定理 restrict_zero
  条件: {_m0 : 可测空间 α} (s : 集合 α)
  结论: (0 : 测度 α).restrict s = 0
  证明: (restrictₗ s).map_zero

@[simp]

Depends on / 依赖: map_zero
-/
theorem restrict_zero {_m0 : MeasurableSpace α} (s : Set α) : (0 : Measure α).restrict s = 0 :=
  (restrictₗ s).map_zero

@[simp]
/--
theorem `restrict_smul` / 定理 `restrict_smul`

English:
theorem restrict_smul
  statement: {_m0 : MeasurableSpace α} {R : Type*} [SMul R Real>=0∞]
  proof: by
  simpa only [smul_one_smul] using! (restrictₗ s).map_smul (c • 1) μ

中文:
定理 restrict_smul
  结论: {_m0 : 可测空间 α} {R : 类型} [标量乘法 R 实数>=0∞]
  证明: by
  simpa only [smul_one_smul] using! (restrictₗ s).map_smul (c • 1) μ

Depends on / 依赖: map_smul, smul_one_smul
-/
theorem restrict_smul {_m0 : MeasurableSpace α} {R : Type*} [SMul R Real>=0∞]
    [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (μ : Measure α) (s : Set α) :
    (c • μ).restrict s = c • μ.restrict s := by
  simpa only [smul_one_smul] using! (restrictₗ s).map_smul (c • 1) μ

/--
theorem `restrict_restrict₀` / 定理 `restrict_restrict₀`

English:
theorem restrict_restrict₀
  given: (hs : NullMeasurableSet s (μ.restrict t))
  proof: ext fun u hu => by
    simp only [Set.inter_assoc, restrict_apply hu,
      restrict_apply₀ (hu.nullMeasurableSet.inter hs)]

@[simp]

中文:
定理 restrict_restrict₀
  条件: (hs : NullMeasurableSet s (μ.restrict t))
  证明: ext fun u hu => by
    simp only [Set.inter_assoc, restrict_apply hu,
      restrict_apply₀ (hu.nullMeasurableSet.inter hs)]

@[simp]

Depends on / 依赖: Set.inter_assoc, hu.nullMeasurableSet.inter, inter_assoc, nullMeasurableSet, restrict_apply
-/
theorem restrict_restrict₀ (hs : NullMeasurableSet s (μ.restrict t)) :
    (μ.restrict t).restrict s = μ.restrict (s inter t) :=
  ext fun u hu => by
    simp only [Set.inter_assoc, restrict_apply hu,
      restrict_apply₀ (hu.nullMeasurableSet.inter hs)]

@[simp]
/--
theorem `restrict_restrict` / 定理 `restrict_restrict`

English:
theorem restrict_restrict
  given: (hs : MeasurableSet s)
  statement: (μ.restrict t).restrict s = μ.restrict (s inter t)
  proof: restrict_restrict₀ hs.nullMeasurableSet

中文:
定理 restrict_restrict
  条件: (hs : 可测集 s)
  结论: (μ.restrict t).restrict s = μ.restrict (s inter t)
  证明: restrict_restrict₀ hs.nullMeasurableSet

Depends on / 依赖: hs.nullMeasurableSet, nullMeasurableSet
-/
theorem restrict_restrict (hs : MeasurableSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t) :=
  restrict_restrict₀ hs.nullMeasurableSet

/--
theorem `restrict_restrict_of_subset` / 定理 `restrict_restrict_of_subset`

English:
theorem restrict_restrict_of_subset
  given: (h : s subseteq t)
  statement: (μ.restrict t).restrict s = μ.restrict s
  proof: by
  ext1 u hu
  rw [restrict_apply hu]; rw [restrict_apply hu]; rw [restrict_eq_self]
  exact inter_subset_right.trans h

中文:
定理 restrict_restrict_of_subset
  条件: (h : s subseteq t)
  结论: (μ.restrict t).restrict s = μ.restrict s
  证明: by
  ext1 u hu
  rw [restrict_apply hu]; rw [restrict_apply hu]; rw [restrict_eq_self]
  exact inter_subset_right.trans h

Depends on / 依赖: inter_subset_right, inter_subset_right.trans, restrict_apply, restrict_eq_self
-/
theorem restrict_restrict_of_subset (h : s subseteq t) : (μ.restrict t).restrict s = μ.restrict s := by
  ext1 u hu
  rw [restrict_apply hu]; rw [restrict_apply hu]; rw [restrict_eq_self]
  exact inter_subset_right.trans h

/--
theorem `restrict_restrict₀'` / 定理 `restrict_restrict₀'`

English:
theorem restrict_restrict₀'
  given: (ht : NullMeasurableSet t μ)
  proof: ext fun u hu => by simp only [restrict_apply hu, restrict_apply₀' ht, inter_assoc]

中文:
定理 restrict_restrict₀'
  条件: (ht : NullMeasurableSet t μ)
  证明: ext fun u hu => by simp only [restrict_apply hu, restrict_apply₀' ht, inter_assoc]

Depends on / 依赖: inter_assoc, restrict_apply
-/
theorem restrict_restrict₀' (ht : NullMeasurableSet t μ) :
    (μ.restrict t).restrict s = μ.restrict (s inter t) :=
  ext fun u hu => by simp only [restrict_apply hu, restrict_apply₀' ht, inter_assoc]

/--
theorem `restrict_restrict'` / 定理 `restrict_restrict'`

English:
theorem restrict_restrict'
  given: (ht : MeasurableSet t)
  proof: restrict_restrict₀' ht.nullMeasurableSet

中文:
定理 restrict_restrict'
  条件: (ht : 可测集 t)
  证明: restrict_restrict₀' ht.nullMeasurableSet

Depends on / 依赖: ht.nullMeasurableSet, nullMeasurableSet
-/
theorem restrict_restrict' (ht : MeasurableSet t) :
    (μ.restrict t).restrict s = μ.restrict (s inter t) :=
  restrict_restrict₀' ht.nullMeasurableSet

/--
theorem `restrict_comm` / 定理 `restrict_comm`

English:
theorem restrict_comm
  given: (hs : MeasurableSet s)
  proof: by
  rw [restrict_restrict hs]; rw [restrict_restrict' hs]; rw [inter_comm]

中文:
定理 restrict_comm
  条件: (hs : 可测集 s)
  证明: by
  rw [restrict_restrict hs]; rw [restrict_restrict' hs]; rw [inter_comm]

Depends on / 依赖: inter_comm, restrict_restrict
-/
theorem restrict_comm (hs : MeasurableSet s) :
    (μ.restrict t).restrict s = (μ.restrict s).restrict t := by
  rw [restrict_restrict hs]; rw [restrict_restrict' hs]; rw [inter_comm]

/--
theorem `restrict_apply_eq_zero` / 定理 `restrict_apply_eq_zero`

English:
theorem restrict_apply_eq_zero
  given: (ht : MeasurableSet t)
  statement: μ.restrict s t = 0 ↔ μ (t inter s) = 0
  proof: by
  rw [restrict_apply ht]

中文:
定理 restrict_apply_eq_zero
  条件: (ht : 可测集 t)
  结论: μ.restrict s t = 0 ↔ μ (t inter s) = 0
  证明: by
  rw [restrict_apply ht]

Depends on / 依赖: restrict_apply
-/
theorem restrict_apply_eq_zero (ht : MeasurableSet t) : μ.restrict s t = 0 ↔ μ (t inter s) = 0 := by
  rw [restrict_apply ht]

/--
theorem `measure_inter_eq_zero_of_restrict` / 定理 `measure_inter_eq_zero_of_restrict`

English:
theorem measure_inter_eq_zero_of_restrict
  given: (h : μ.restrict s t = 0)
  statement: μ (t inter s) = 0
  proof: nonpos_iff_eq_zero.1 (h ▸ le_restrict_apply _ _)

中文:
定理 measure_inter_eq_zero_of_restrict
  条件: (h : μ.restrict s t = 0)
  结论: μ (t inter s) = 0
  证明: nonpos_iff_eq_zero.1 (h ▸ le_restrict_apply _ _)

Depends on / 依赖: le_restrict_apply, nonpos_iff_eq_zero
-/
theorem measure_inter_eq_zero_of_restrict (h : μ.restrict s t = 0) : μ (t inter s) = 0 :=
  nonpos_iff_eq_zero.1 (h ▸ le_restrict_apply _ _)

/--
theorem `restrict_apply_eq_zero'` / 定理 `restrict_apply_eq_zero'`

English:
theorem restrict_apply_eq_zero'
  given: (hs : MeasurableSet s)
  statement: μ.restrict s t = 0 ↔ μ (t inter s) = 0
  proof: by
  rw [restrict_apply' hs]

@[simp]

中文:
定理 restrict_apply_eq_zero'
  条件: (hs : 可测集 s)
  结论: μ.restrict s t = 0 ↔ μ (t inter s) = 0
  证明: by
  rw [restrict_apply' hs]

@[simp]

Depends on / 依赖: restrict_apply
-/
theorem restrict_apply_eq_zero' (hs : MeasurableSet s) : μ.restrict s t = 0 ↔ μ (t inter s) = 0 := by
  rw [restrict_apply' hs]

@[simp]
/--
theorem `restrict_eq_zero` / 定理 `restrict_eq_zero`

English:
theorem restrict_eq_zero
  statement: μ.restrict s = 0 ↔ μ s = 0
  proof: by
  rw [← measure_univ_eq_zero]; rw [restrict_apply_univ]

中文:
定理 restrict_eq_zero
  结论: μ.restrict s = 0 ↔ μ s = 0
  证明: by
  rw [← measure_univ_eq_zero]; rw [restrict_apply_univ]

Depends on / 依赖: measure_univ_eq_zero, restrict_apply_univ
-/
theorem restrict_eq_zero : μ.restrict s = 0 ↔ μ s = 0 := by
  rw [← measure_univ_eq_zero]; rw [restrict_apply_univ]

/--
Instance `restrict.neZero` / 实例 `restrict.neZero`

English:
instance restrict.neZero
  signature: [NeZero (μ s)]
  body: ⟨mt restrict_eq_zero.mp NeZero.ne _⟩

中文:
实例 restrict.neZero
  签名: [NeZero (μ s)]
  定义体: ⟨mt restrict_eq_zero.mp NeZero.ne _⟩

Depends on / 依赖: NeZero, NeZero.ne, restrict_eq_zero, restrict_eq_zero.mp
-/
instance restrict.neZero [NeZero (μ s)] : NeZero (μ.restrict s) :=
⟨mt restrict_eq_zero.mp NeZero.ne _⟩

/--
theorem `restrict_zero_set` / 定理 `restrict_zero_set`

English:
theorem restrict_zero_set
  given: {s : Set α} (h : μ s = 0)
  statement: μ.restrict s = 0
  proof: restrict_eq_zero.2 h

@[simp]

中文:
定理 restrict_zero_set
  条件: {s : 集合 α} (h : μ s = 0)
  结论: μ.restrict s = 0
  证明: restrict_eq_zero.2 h

@[simp]

Depends on / 依赖: restrict_eq_zero
-/
theorem restrict_zero_set {s : Set α} (h : μ s = 0) : μ.restrict s = 0 :=
  restrict_eq_zero.2 h

@[simp]
/--
theorem `restrict_empty` / 定理 `restrict_empty`

English:
theorem restrict_empty
  statement: μ.restrict ∅ = 0
  proof: restrict_zero_set measure_empty

@[simp]

中文:
定理 restrict_empty
  结论: μ.restrict ∅ = 0
  证明: restrict_zero_set measure_empty

@[simp]

Depends on / 依赖: measure_empty, restrict_zero_set
-/
theorem restrict_empty : μ.restrict ∅ = 0 :=
  restrict_zero_set measure_empty

@[simp]
/--
theorem `restrict_univ` / 定理 `restrict_univ`

English:
theorem restrict_univ
  statement: μ.restrict univ = μ
  proof: ext fun s hs => by simp [hs]

中文:
定理 restrict_univ
  结论: μ.restrict univ = μ
  证明: ext fun s hs => by simp [hs]
-/
theorem restrict_univ : μ.restrict univ = μ :=
  ext fun s hs => by simp [hs]

/--
theorem `restrict_inter_add_sdiff₀` / 定理 `restrict_inter_add_sdiff₀`

English:
theorem restrict_inter_add_sdiff₀
  given: (s : Set α) (ht : NullMeasurableSet t μ)
  proof: by
  ext1 u hu
  simp only [add_apply, restrict_apply hu, ← inter_assoc, sdiff_eq]
  exact measure_inter_add_sdiff₀ (u inter s) ht

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff₀ := restrict_inter_add_sdiff₀

中文:
定理 restrict_inter_add_sdiff₀
  条件: (s : 集合 α) (ht : NullMeasurableSet t μ)
  证明: by
  ext1 u hu
  simp only [add_apply, restrict_apply hu, ← inter_assoc, sdiff_eq]
  exact measure_inter_add_sdiff₀ (u inter s) ht

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff₀ := restrict_inter_add_sdiff₀

Depends on / 依赖: BoolAlg, ConcreteCategory, ConcreteCategory.hom, add_apply, inter_assoc, restrict_apply, sdiff_eq
-/
theorem restrict_inter_add_sdiff₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ.restrict (s inter t) + μ.restrict (s \ t) = μ.restrict s := by
  ext1 u hu
  simp only [add_apply, restrict_apply hu, ← inter_assoc, sdiff_eq]
  exact measure_inter_add_sdiff₀ (u inter s) ht

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff₀ := restrict_inter_add_sdiff₀

/--
theorem `restrict_inter_add_sdiff` / 定理 `restrict_inter_add_sdiff`

English:
theorem restrict_inter_add_sdiff
  given: (s : Set α) (ht : MeasurableSet t)
  proof: restrict_inter_add_sdiff₀ s ht.nullMeasurableSet

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff := restrict_inter_add_sdiff

中文:
定理 restrict_inter_add_sdiff
  条件: (s : 集合 α) (ht : 可测集 t)
  证明: restrict_inter_add_sdiff₀ s ht.nullMeasurableSet

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff := restrict_inter_add_sdiff

Depends on / 依赖: ht.nullMeasurableSet, nullMeasurableSet
-/
theorem restrict_inter_add_sdiff (s : Set α) (ht : MeasurableSet t) :
    μ.restrict (s inter t) + μ.restrict (s \ t) = μ.restrict s :=
  restrict_inter_add_sdiff₀ s ht.nullMeasurableSet

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff := restrict_inter_add_sdiff

/--
theorem `restrict_union_add_inter₀` / 定理 `restrict_union_add_inter₀`

English:
theorem restrict_union_add_inter₀
  given: (s : Set α) (ht : NullMeasurableSet t μ)
  proof: by
  rw [← restrict_inter_add_sdiff₀ (s union t) ht]; rw [union_inter_cancel_right]; rw [union_sdiff_right]; rw [←
    restrict_inter_add_sdiff₀ s ht]; rw [add_comm]; rw [← add_assoc]; rw [add_right_comm]

中文:
定理 restrict_union_add_inter₀
  条件: (s : 集合 α) (ht : NullMeasurableSet t μ)
  证明: by
  rw [← restrict_inter_add_sdiff₀ (s union t) ht]; rw [union_inter_cancel_right]; rw [union_sdiff_right]; rw [←
    restrict_inter_add_sdiff₀ s ht]; rw [add_comm]; rw [← add_assoc]; rw [add_right_comm]

Depends on / 依赖: add_assoc, add_comm, add_right_comm, f.hom, union_inter_cancel_right, union_sdiff_right
-/
theorem restrict_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ.restrict (s union t) + μ.restrict (s inter t) = μ.restrict s + μ.restrict t := by
  rw [← restrict_inter_add_sdiff₀ (s union t) ht]; rw [union_inter_cancel_right]; rw [union_sdiff_right]; rw [←
    restrict_inter_add_sdiff₀ s ht]; rw [add_comm]; rw [← add_assoc]; rw [add_right_comm]

/--
theorem `restrict_union_add_inter` / 定理 `restrict_union_add_inter`

English:
theorem restrict_union_add_inter
  given: (s : Set α) (ht : MeasurableSet t)
  proof: restrict_union_add_inter₀ s ht.nullMeasurableSet

中文:
定理 restrict_union_add_inter
  条件: (s : 集合 α) (ht : 可测集 t)
  证明: restrict_union_add_inter₀ s ht.nullMeasurableSet

Depends on / 依赖: ht.nullMeasurableSet, nullMeasurableSet
-/
theorem restrict_union_add_inter (s : Set α) (ht : MeasurableSet t) :
    μ.restrict (s union t) + μ.restrict (s inter t) = μ.restrict s + μ.restrict t :=
  restrict_union_add_inter₀ s ht.nullMeasurableSet

/--
theorem `restrict_union_add_inter'` / 定理 `restrict_union_add_inter'`

English:
theorem restrict_union_add_inter'
  given: (hs : MeasurableSet s) (t : Set α)
  proof: by
  simpa only [union_comm, inter_comm, add_comm] using restrict_union_add_inter t hs

中文:
定理 restrict_union_add_inter'
  条件: (hs : 可测集 s) (t : 集合 α)
  证明: by
  simpa only [union_comm, inter_comm, add_comm] using restrict_union_add_inter t hs

Depends on / 依赖: add_comm, inter_comm, restrict_union_add_inter, union_comm
-/
theorem restrict_union_add_inter' (hs : MeasurableSet s) (t : Set α) :
    μ.restrict (s union t) + μ.restrict (s inter t) = μ.restrict s + μ.restrict t := by
  simpa only [union_comm, inter_comm, add_comm] using restrict_union_add_inter t hs

/--
theorem `restrict_union₀` / 定理 `restrict_union₀`

English:
theorem restrict_union₀
  given: (h : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
  proof: by
  simp [← restrict_union_add_inter₀ s ht, restrict_zero_set h]

中文:
定理 restrict_union₀
  条件: (h : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
  证明: by
  simp [← restrict_union_add_inter₀ s ht, restrict_zero_set h]

Depends on / 依赖: restrict_zero_set
-/
theorem restrict_union₀ (h : AEDisjoint μ s t) (ht : NullMeasurableSet t μ) :
    μ.restrict (s union t) = μ.restrict s + μ.restrict t := by
  simp [← restrict_union_add_inter₀ s ht, restrict_zero_set h]

/--
theorem `restrict_union` / 定理 `restrict_union`

English:
theorem restrict_union
  given: (h : Disjoint s t) (ht : MeasurableSet t)
  proof: restrict_union₀ h.aedisjoint ht.nullMeasurableSet

中文:
定理 restrict_union
  条件: (h : Disjoint s t) (ht : 可测集 t)
  证明: restrict_union₀ h.aedisjoint ht.nullMeasurableSet

Depends on / 依赖: aedisjoint, h.aedisjoint, ht.nullMeasurableSet, nullMeasurableSet
-/
theorem restrict_union (h : Disjoint s t) (ht : MeasurableSet t) :
    μ.restrict (s union t) = μ.restrict s + μ.restrict t :=
  restrict_union₀ h.aedisjoint ht.nullMeasurableSet

/--
theorem `restrict_union'` / 定理 `restrict_union'`

English:
theorem restrict_union'
  given: (h : Disjoint s t) (hs : MeasurableSet s)
  proof: by
  rw [union_comm]; rw [restrict_union h.symm hs]; rw [add_comm]

@[simp]

中文:
定理 restrict_union'
  条件: (h : Disjoint s t) (hs : 可测集 s)
  证明: by
  rw [union_comm]; rw [restrict_union h.symm hs]; rw [add_comm]

@[simp]

Depends on / 依赖: add_comm, h.symm, restrict_union, union_comm
-/
theorem restrict_union' (h : Disjoint s t) (hs : MeasurableSet s) :
    μ.restrict (s union t) = μ.restrict s + μ.restrict t := by
  rw [union_comm]; rw [restrict_union h.symm hs]; rw [add_comm]

@[simp]
/--
theorem `restrict_add_restrict_compl` / 定理 `restrict_add_restrict_compl`

English:
theorem restrict_add_restrict_compl
  given: (hs : MeasurableSet s)
  proof: by
  rw [← restrict_union (@disjoint_compl_right (Set α) _ _) hs.compl]; rw [union_compl_self]; rw [restrict_univ]

@[simp]

中文:
定理 restrict_add_restrict_compl
  条件: (hs : 可测集 s)
  证明: by
  rw [← restrict_union (@disjoint_compl_right (Set α) _ _) hs.compl]; rw [union_compl_self]; rw [restrict_univ]

@[simp]

Depends on / 依赖: disjoint_compl_right, hs.compl, restrict_union, restrict_univ, union_compl_self
-/
theorem restrict_add_restrict_compl (hs : MeasurableSet s) :
    μ.restrict s + μ.restrict sᶜ = μ := by
  rw [← restrict_union (@disjoint_compl_right (Set α) _ _) hs.compl]; rw [union_compl_self]; rw [restrict_univ]

@[simp]
/--
theorem `restrict_compl_add_restrict` / 定理 `restrict_compl_add_restrict`

English:
theorem restrict_compl_add_restrict
  given: (hs : MeasurableSet s)
  statement: μ.restrict sᶜ + μ.restrict s = μ
  proof: by
  rw [add_comm]; rw [restrict_add_restrict_compl hs]

中文:
定理 restrict_compl_add_restrict
  条件: (hs : 可测集 s)
  结论: μ.restrict sᶜ + μ.restrict s = μ
  证明: by
  rw [add_comm]; rw [restrict_add_restrict_compl hs]

Depends on / 依赖: add_comm, restrict_add_restrict_compl
-/
theorem restrict_compl_add_restrict (hs : MeasurableSet s) : μ.restrict sᶜ + μ.restrict s = μ := by
  rw [add_comm]; rw [restrict_add_restrict_compl hs]

/--
theorem `restrict_union_le` / 定理 `restrict_union_le`

English:
theorem restrict_union_le
  given: (s s' : Set α)
  statement: μ.restrict (s union s') <= μ.restrict s + μ.restrict s'
  proof: le_iff.2 fun t ht => by
    simpa [ht, inter_union_distrib_left] using measure_union_le (t inter s) (t inter s')

中文:
定理 restrict_union_le
  条件: (s s' : 集合 α)
  结论: μ.restrict (s union s') <= μ.restrict s + μ.restrict s'
  证明: le_iff.2 fun t ht => by
    simpa [ht, inter_union_distrib_left] using measure_union_le (t inter s) (t inter s')

Depends on / 依赖: inter_union_distrib_left, le_iff, measure_union_le
-/
theorem restrict_union_le (s s' : Set α) : μ.restrict (s union s') <= μ.restrict s + μ.restrict s' :=
  le_iff.2 fun t ht => by
    simpa [ht, inter_union_distrib_left] using measure_union_le (t inter s) (t inter s')

/--
theorem `restrict_iUnion_apply_ae` / 定理 `restrict_iUnion_apply_ae`

English:
theorem restrict_iUnion_apply_ae
  statement: [Countable ι] {s : ι -> Set α} (hd : Pairwise (AEDisjoint μ on s))
  proof: by
  simp only [restrict_apply, ht, inter_iUnion]
  exact
    measure_iUnion₀ (hd.mono fun i j h => h.mono inter_subset_right inter_subset_right)
      fun i => ht.nullMeasurableSet.inter (hm i)

中文:
定理 restrict_iUnion_apply_ae
  结论: [可数 ι] {s : ι -> 集合 α} (hd : 两两 (AEDisjoint μ on s))
  证明: by
  simp only [restrict_apply, ht, inter_iUnion]
  exact
    measure_iUnion₀ (hd.mono fun i j h => h.mono inter_subset_right inter_subset_right)
      fun i => ht.nullMeasurableSet.inter (hm i)

Depends on / 依赖: h.mono, hd.mono, ht.nullMeasurableSet.inter, inter_iUnion, inter_subset_right, nullMeasurableSet, restrict_apply
-/
theorem restrict_iUnion_apply_ae [Countable ι] {s : ι -> Set α} (hd : Pairwise (AEDisjoint μ on s))
    (hm : forall i, NullMeasurableSet (s i) μ) {t : Set α} (ht : MeasurableSet t) :
    μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t := by
  simp only [restrict_apply, ht, inter_iUnion]
  exact
    measure_iUnion₀ (hd.mono fun i j h => h.mono inter_subset_right inter_subset_right)
      fun i => ht.nullMeasurableSet.inter (hm i)

/--
theorem `restrict_iUnion_apply` / 定理 `restrict_iUnion_apply`

English:
theorem restrict_iUnion_apply
  statement: [Countable ι] {s : ι -> Set α} (hd : Pairwise (Disjoint on s))
  proof: restrict_iUnion_apply_ae hd.aedisjoint (fun i => (hm i).nullMeasurableSet) ht

中文:
定理 restrict_iUnion_apply
  结论: [可数 ι] {s : ι -> 集合 α} (hd : 两两 (Disjoint on s))
  证明: restrict_iUnion_apply_ae hd.aedisjoint (fun i => (hm i).nullMeasurableSet) ht

Depends on / 依赖: aedisjoint, hd.aedisjoint, nullMeasurableSet, restrict_iUnion_apply_ae
-/
theorem restrict_iUnion_apply [Countable ι] {s : ι -> Set α} (hd : Pairwise (Disjoint on s))
    (hm : forall i, MeasurableSet (s i)) {t : Set α} (ht : MeasurableSet t) :
    μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t :=
  restrict_iUnion_apply_ae hd.aedisjoint (fun i => (hm i).nullMeasurableSet) ht

/--
theorem `restrict_iUnion_apply_eq_iSup` / 定理 `restrict_iUnion_apply_eq_iSup`

English:
theorem restrict_iUnion_apply_eq_iSup
  statement: [Countable ι] {s : ι -> Set α} (hd : Directed (· subseteq ·) s)
  proof: by
  simp only [restrict_apply ht, inter_iUnion]
  rw [Directed.measure_iUnion]
  exacts [hd.mono_comp _ fun s₁ s₂ => inter_subset_inter_right _]

中文:
定理 restrict_iUnion_apply_eq_iSup
  结论: [可数 ι] {s : ι -> 集合 α} (hd : Directed (· subseteq ·) s)
  证明: by
  simp only [restrict_apply ht, inter_iUnion]
  rw [Directed.measure_iUnion]
  exacts [hd.mono_comp _ fun s₁ s₂ => inter_subset_inter_right _]

Depends on / 依赖: Directed, Directed.measure_iUnion, exacts, hd.mono_comp, inter_iUnion, inter_subset_inter_right, measure_iUnion, mono_comp, restrict_apply
-/
theorem restrict_iUnion_apply_eq_iSup [Countable ι] {s : ι -> Set α} (hd : Directed (· subseteq ·) s)
    {t : Set α} (ht : MeasurableSet t) : μ.restrict (⋃ i, s i) t = ⨆ i, μ.restrict (s i) t := by
  simp only [restrict_apply ht, inter_iUnion]
  rw [Directed.measure_iUnion]
  exacts [hd.mono_comp _ fun s₁ s₂ => inter_subset_inter_right _]

/--
theorem `restrict_map` / 定理 `restrict_map`

English:
theorem restrict_map
  given: {f : α -> β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s)
  proof: ext fun t ht => by simp [*, hf ht]

中文:
定理 restrict_map
  条件: {f : α -> β} (hf : 可测 f) {s : 集合 β} (hs : 可测集 s)
  证明: ext fun t ht => by simp [*, hf ht]
-/
theorem restrict_map {f : α -> β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  ext fun t ht => by simp [*, hf ht]

/--
theorem `restrict_inter_toMeasurable` / 定理 `restrict_inter_toMeasurable`

English:
theorem restrict_inter_toMeasurable
  given: (h : μ s != ∞) (ht : MeasurableSet t) (hst : s subseteq t)
  proof: by
  ext u hu
  rw [restrict_apply hu]; rw [restrict_apply hu]; rw [inter_comm t]; rw [inter_comm]; rw [inter_assoc]; rw [measure_toMeasurable_inter (ht.inter hu) h]
  congr 1
  grind

中文:
定理 restrict_inter_toMeasurable
  条件: (h : μ s != ∞) (ht : 可测集 t) (hst : s subseteq t)
  证明: by
  ext u hu
  rw [restrict_apply hu]; rw [restrict_apply hu]; rw [inter_comm t]; rw [inter_comm]; rw [inter_assoc]; rw [measure_toMeasurable_inter (ht.inter hu) h]
  congr 1
  grind

Depends on / 依赖: ht.inter, inter_assoc, inter_comm, measure_toMeasurable_inter, restrict_apply
-/
theorem restrict_inter_toMeasurable (h : μ s != ∞) (ht : MeasurableSet t) (hst : s subseteq t) :
    μ.restrict (t inter toMeasurable μ s) = μ.restrict s := by
  ext u hu
  rw [restrict_apply hu]; rw [restrict_apply hu]; rw [inter_comm t]; rw [inter_comm]; rw [inter_assoc]; rw [measure_toMeasurable_inter (ht.inter hu) h]
  congr 1
  grind

/--
theorem `restrict_toMeasurable` / 定理 `restrict_toMeasurable`

English:
theorem restrict_toMeasurable
  given: (h : μ s != ∞)
  statement: μ.restrict (toMeasurable μ s) = μ.restrict s
  proof: by
  simpa using restrict_inter_toMeasurable h MeasurableSet.univ (subset_univ _)

中文:
定理 restrict_toMeasurable
  条件: (h : μ s != ∞)
  结论: μ.restrict (toMeasurable μ s) = μ.restrict s
  证明: by
  simpa using restrict_inter_toMeasurable h MeasurableSet.univ (subset_univ _)

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, restrict_inter_toMeasurable, subset_univ
-/
theorem restrict_toMeasurable (h : μ s != ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s := by
  simpa using restrict_inter_toMeasurable h MeasurableSet.univ (subset_univ _)

/--
theorem `restrict_eq_self_of_ae_mem` / 定理 `restrict_eq_self_of_ae_mem`

English:
theorem restrict_eq_self_of_ae_mem
  given: {_m0 : MeasurableSpace α} ⦃s
  statement: Set α⦄ ⦃μ : Measure α⦄
  proof: calc
    μ.restrict s = μ.restrict univ := restrict_congr_set (eventuallyEq_univ.mpr hs)
    _ = μ := restrict_univ

中文:
定理 restrict_eq_self_of_ae_mem
  条件: {_m0 : 可测空间 α} ⦃s
  结论: 集合 α⦄ ⦃μ : 测度 α⦄
  证明: calc
    μ.restrict s = μ.restrict univ := restrict_congr_set (eventuallyEq_univ.mpr hs)
    _ = μ := restrict_univ

Depends on / 依赖: eventuallyEq_univ, eventuallyEq_univ.mpr, restrict, restrict_congr_set, restrict_univ
-/
theorem restrict_eq_self_of_ae_mem {_m0 : MeasurableSpace α} ⦃s : Set α⦄ ⦃μ : Measure α⦄
    (hs : forallᵐ x ∂μ, x in s) : μ.restrict s = μ :=
  calc
    μ.restrict s = μ.restrict univ := restrict_congr_set (eventuallyEq_univ.mpr hs)
    _ = μ := restrict_univ

/--
theorem `restrict_congr_meas` / 定理 `restrict_congr_meas`

English:
theorem restrict_congr_meas
  given: (hs : MeasurableSet s)
  proof: ⟨fun H t hts ht => by
    rw [← inter_eq_self_of_subset_left hts]; rw [← restrict_apply ht]; rw [H]; rw [restrict_apply ht], fun H =>
    ext fun t ht => by
      rw [restrict_apply ht]; rw [restrict_apply ht]; rw [H _ inter_subset_right (ht.inter hs)]⟩

中文:
定理 restrict_congr_meas
  条件: (hs : 可测集 s)
  证明: ⟨fun H t hts ht => by
    rw [← inter_eq_self_of_subset_left hts]; rw [← restrict_apply ht]; rw [H]; rw [restrict_apply ht], fun H =>
    ext fun t ht => by
      rw [restrict_apply ht]; rw [restrict_apply ht]; rw [H _ inter_subset_right (ht.inter hs)]⟩

Depends on / 依赖: ht.inter, inter_eq_self_of_subset_left, inter_subset_right, restrict_apply
-/
theorem restrict_congr_meas (hs : MeasurableSet s) :
    μ.restrict s = ν.restrict s ↔ forall t subseteq s, MeasurableSet t -> μ t = ν t :=
  ⟨fun H t hts ht => by
    rw [← inter_eq_self_of_subset_left hts]; rw [← restrict_apply ht]; rw [H]; rw [restrict_apply ht], fun H =>
    ext fun t ht => by
      rw [restrict_apply ht]; rw [restrict_apply ht]; rw [H _ inter_subset_right (ht.inter hs)]⟩

/--
theorem `restrict_congr_mono` / 定理 `restrict_congr_mono`

English:
theorem restrict_congr_mono
  given: (hs : s subseteq t) (h : μ.restrict t = ν.restrict t)
  proof: by
  rw [← restrict_restrict_of_subset hs]; rw [h]; rw [restrict_restrict_of_subset hs]

中文:
定理 restrict_congr_mono
  条件: (hs : s subseteq t) (h : μ.restrict t = ν.restrict t)
  证明: by
  rw [← restrict_restrict_of_subset hs]; rw [h]; rw [restrict_restrict_of_subset hs]

Depends on / 依赖: restrict_restrict_of_subset
-/
theorem restrict_congr_mono (hs : s subseteq t) (h : μ.restrict t = ν.restrict t) :
    μ.restrict s = ν.restrict s := by
  rw [← restrict_restrict_of_subset hs]; rw [h]; rw [restrict_restrict_of_subset hs]

/--
theorem `restrict_union_congr` / 定理 `restrict_union_congr`

English:
theorem restrict_union_congr
  proof: by
  refine ⟨fun h => ⟨restrict_congr_mono subset_union_left h,
    restrict_congr_mono subset_union_right h⟩, ?_⟩
  rintro ⟨hs, ht⟩
  ext1 u hu
  simp only [restrict_apply hu, inter_union_distrib_left]
  rcases exists_measurable_superset₂ μ ν (u inter s) with ⟨US, hsub, hm, hμ, hν⟩
  calc
    μ (u 

中文:
定理 restrict_union_congr
  证明: by
  refine ⟨fun h => ⟨restrict_congr_mono subset_union_left h,
    restrict_congr_mono subset_union_right h⟩, ?_⟩
  rintro ⟨hs, ht⟩
  ext1 u hu
  simp only [restrict_apply hu, inter_union_distrib_left]
  rcases exists_measurable_superset₂ μ ν (u inter s) with ⟨US, hsub, hm, hμ, hν⟩
  calc
    μ (u 

Depends on / 依赖: Subset, Subset.rfl, hm.nullMeasurableSet, inter_union_distrib_left, le_rfl, measure_add_sdiff, measure_union_congr_of_subset, nullMeasurableSet, restrict, restrict_apply, restrict_congr_mono, subset_union_left, subset_union_right
-/
theorem restrict_union_congr :
    μ.restrict (s union t) = ν.restrict (s union t) ↔
      μ.restrict s = ν.restrict s ∧ μ.restrict t = ν.restrict t := by
  refine ⟨fun h => ⟨restrict_congr_mono subset_union_left h,
    restrict_congr_mono subset_union_right h⟩, ?_⟩
  rintro ⟨hs, ht⟩
  ext1 u hu
  simp only [restrict_apply hu, inter_union_distrib_left]
  rcases exists_measurable_superset₂ μ ν (u inter s) with ⟨US, hsub, hm, hμ, hν⟩
  calc
    μ (u inter s union u inter t) = μ (US union u inter t) :=
      measure_union_congr_of_subset hsub hμ.le Subset.rfl le_rfl
    _ = μ US + μ ((u inter t) \ US) := (measure_add_sdiff hm.nullMeasurableSet _).symm
    _ = restrict μ s u + restrict μ t (u \ US) := by
      simp only [restrict_apply, hu, hu.diff hm, hμ, ← inter_comm t, inter_sdiff_assoc]
    _ = restrict ν s u + restrict ν t (u \ US) := by rw [hs, ht]
    _ = ν US + ν ((u inter t) \ US) := by
      simp only [restrict_apply, hu, hu.diff hm, hν, ← inter_comm t, inter_sdiff_assoc]
    _ = ν (US union u inter t) := measure_add_sdiff hm.nullMeasurableSet _
_ = ν (u inter s union u inter t) := .symm measure_union_congr_of_subset hsub hν.le Subset.rfl le_rfl

/--
theorem `restrict_biUnion_finset_congr` / 定理 `restrict_biUnion_finset_congr`

English:
theorem restrict_biUnion_finset_congr
  given: {s : Finset ι} {t : ι -> Set α}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s _ hs =>
    simp only [forall_eq_or_imp, iUnion_iUnion_eq_or_left, Finset.mem_insert]
    rw [restrict_union_congr]; rw [← hs]

中文:
定理 restrict_biUnion_finset_congr
  条件: {s : 有限集 ι} {t : ι -> 集合 α}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s _ hs =>
    simp only [forall_eq_or_imp, iUnion_iUnion_eq_or_left, Finset.mem_insert]
    rw [restrict_union_congr]; rw [← hs]

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert, classical, forall_eq_or_imp, iUnion_iUnion_eq_or_left, induction_on, insert, mem_insert, restrict_union_congr
-/
theorem restrict_biUnion_finset_congr {s : Finset ι} {t : ι -> Set α} :
    μ.restrict (⋃ i in s, t i) = ν.restrict (⋃ i in s, t i) ↔
      forall i in s, μ.restrict (t i) = ν.restrict (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s _ hs =>
    simp only [forall_eq_or_imp, iUnion_iUnion_eq_or_left, Finset.mem_insert]
    rw [restrict_union_congr]; rw [← hs]

/--
theorem `restrict_iUnion_congr` / 定理 `restrict_iUnion_congr`

English:
theorem restrict_iUnion_congr
  given: [Countable ι] {s : ι -> Set α}
  proof: by
  refine ⟨fun h i => restrict_congr_mono (subset_iUnion _ _) h, fun h => ?_⟩
  ext1 t ht
  have D : Directed (· subseteq ·) fun t : Finset ι => ⋃ i in t, s i :=
    Monotone.directed_le fun t₁ t₂ ht => biUnion_subset_biUnion_left ht
  rw [iUnion_eq_iUnion_finset]
  simp only [restrict_iUnion_appl

中文:
定理 restrict_iUnion_congr
  条件: [可数 ι] {s : ι -> 集合 α}
  证明: by
  refine ⟨fun h i => restrict_congr_mono (subset_iUnion _ _) h, fun h => ?_⟩
  ext1 t ht
  have D : Directed (· subseteq ·) fun t : Finset ι => ⋃ i in t, s i :=
    Monotone.directed_le fun t₁ t₂ ht => biUnion_subset_biUnion_left ht
  rw [iUnion_eq_iUnion_finset]
  simp only [restrict_iUnion_appl

Depends on / 依赖: Directed, Finset, Monotone, Monotone.directed_le, biUnion_subset_biUnion_left, directed_le, iUnion_eq_iUnion_finset, restrict_biUnion_finset_congr, restrict_congr_mono, restrict_iUnion_apply_eq_iSup, subset_iUnion, subseteq
-/
theorem restrict_iUnion_congr [Countable ι] {s : ι -> Set α} :
    μ.restrict (⋃ i, s i) = ν.restrict (⋃ i, s i) ↔ forall i, μ.restrict (s i) = ν.restrict (s i) := by
  refine ⟨fun h i => restrict_congr_mono (subset_iUnion _ _) h, fun h => ?_⟩
  ext1 t ht
  have D : Directed (· subseteq ·) fun t : Finset ι => ⋃ i in t, s i :=
    Monotone.directed_le fun t₁ t₂ ht => biUnion_subset_biUnion_left ht
  rw [iUnion_eq_iUnion_finset]
  simp only [restrict_iUnion_apply_eq_iSup D ht, restrict_biUnion_finset_congr.2 fun i _ => h i]

/--
theorem `restrict_biUnion_congr` / 定理 `restrict_biUnion_congr`

English:
theorem restrict_biUnion_congr
  given: {s : Set ι} {t : ι -> Set α} (hc : s.Countable)
  proof: by
  have := hc.toEncodable
  simp only [biUnion_eq_iUnion, SetCoe.forall', restrict_iUnion_congr]

中文:
定理 restrict_biUnion_congr
  条件: {s : 集合 ι} {t : ι -> 集合 α} (hc : s.可数)
  证明: by
  have := hc.toEncodable
  simp only [biUnion_eq_iUnion, SetCoe.forall', restrict_iUnion_congr]

Depends on / 依赖: SetCoe, SetCoe.forall, biUnion_eq_iUnion, hc.toEncodable, restrict_iUnion_congr, toEncodable
-/
theorem restrict_biUnion_congr {s : Set ι} {t : ι -> Set α} (hc : s.Countable) :
    μ.restrict (⋃ i in s, t i) = ν.restrict (⋃ i in s, t i) ↔
      forall i in s, μ.restrict (t i) = ν.restrict (t i) := by
  have := hc.toEncodable
  simp only [biUnion_eq_iUnion, SetCoe.forall', restrict_iUnion_congr]

/--
theorem `restrict_sUnion_congr` / 定理 `restrict_sUnion_congr`

English:
theorem restrict_sUnion_congr
  given: {S : Set (Set α)} (hc : S.Countable)
  proof: by
  rw [sUnion_eq_biUnion]; rw [restrict_biUnion_congr hc]

中文:
定理 restrict_sUnion_congr
  条件: {S : 集合 (集合 α)} (hc : S.可数)
  证明: by
  rw [sUnion_eq_biUnion]; rw [restrict_biUnion_congr hc]

Depends on / 依赖: restrict_biUnion_congr, sUnion_eq_biUnion
-/
theorem restrict_sUnion_congr {S : Set (Set α)} (hc : S.Countable) :
    μ.restrict (⋃₀ S) = ν.restrict (⋃₀ S) ↔ forall s in S, μ.restrict s = ν.restrict s := by
  rw [sUnion_eq_biUnion]; rw [restrict_biUnion_congr hc]

/--
theorem `restrict_sInf_eq_sInf_restrict` / 定理 `restrict_sInf_eq_sInf_restrict`

English:
theorem restrict_sInf_eq_sInf_restrict
  statement: {m0 : MeasurableSpace α} {m : Set (Measure α)}
  proof: by
  ext1 s hs
  simp_rw [sInf_apply hs, restrict_apply hs, sInf_apply (MeasurableSet.inter hs ht),
    Set.image_image, restrict_toOuterMeasure_eq_toOuterMeasure_restrict ht, ←
    Set.image_image _ toOuterMeasure, ← OuterMeasure.restrict_sInf_eq_sInf_restrict _ (hm.image _),
    OuterMeasure.restr

中文:
定理 restrict_sInf_eq_sInf_restrict
  结论: {m0 : 可测空间 α} {m : 集合 (测度 α)}
  证明: by
  ext1 s hs
  simp_rw [sInf_apply hs, restrict_apply hs, sInf_apply (MeasurableSet.inter hs ht),
    Set.image_image, restrict_toOuterMeasure_eq_toOuterMeasure_restrict ht, ←
    Set.image_image _ toOuterMeasure, ← OuterMeasure.restrict_sInf_eq_sInf_restrict _ (hm.image _),
    OuterMeasure.restr

Depends on / 依赖: MeasurableSet, MeasurableSet.inter, OuterMeasure, OuterMeasure.restrict_apply, OuterMeasure.restrict_sInf_eq_sInf_restrict, Set.image_image, hm.image, image_image, restrict_apply, restrict_sInf_eq_sInf_restrict, restrict_toOuterMeasure_eq_toOuterMeasure_restrict, sInf_apply, simp_rw, toOuterMeasure
-/
theorem restrict_sInf_eq_sInf_restrict {m0 : MeasurableSpace α} {m : Set (Measure α)}
    (hm : m.Nonempty) (ht : MeasurableSet t) :
    (sInf m).restrict t = sInf ((fun μ : Measure α => μ.restrict t) '' m) := by
  ext1 s hs
  simp_rw [sInf_apply hs, restrict_apply hs, sInf_apply (MeasurableSet.inter hs ht),
    Set.image_image, restrict_toOuterMeasure_eq_toOuterMeasure_restrict ht, ←
    Set.image_image _ toOuterMeasure, ← OuterMeasure.restrict_sInf_eq_sInf_restrict _ (hm.image _),
    OuterMeasure.restrict_apply]

/--
theorem `exists_mem_of_measure_ne_zero_of_ae` / 定理 `exists_mem_of_measure_ne_zero_of_ae`

English:
theorem exists_mem_of_measure_ne_zero_of_ae
  statement: (hs : μ s != 0) {p : α -> Prop}
  proof: by
  rw [← μ.restrict_apply_self]; rw [← frequently_ae_mem_iff] at hs
  exact (hs.and_eventually hp).exists

中文:
定理 存在_mem_of_measure_ne_zero_of_ae
  结论: (hs : μ s != 0) {p : α -> 命题}
  证明: by
  rw [← μ.restrict_apply_self]; rw [← frequently_ae_mem_iff] at hs
  exact (hs.and_eventually hp).exists

Depends on / 依赖: and_eventually, frequently_ae_mem_iff, hs.and_eventually, restrict_apply_self
-/
theorem exists_mem_of_measure_ne_zero_of_ae (hs : μ s != 0) {p : α -> Prop}
    (hp : forallᵐ x ∂μ.restrict s, p x) : exists x, x in s ∧ p x := by
  rw [← μ.restrict_apply_self]; rw [← frequently_ae_mem_iff] at hs
  exact (hs.and_eventually hp).exists

/--
theorem `QuasiMeasurePreserving.restrict` / 定理 `QuasiMeasurePreserving.restrict`

English:
theorem QuasiMeasurePreserving.restrict
  statement: {ν : Measure β} {f : α -> β}
  proof: hf.measurable
  absolutelyContinuous := by
    refine AbsolutelyContinuous.mk fun u hum => ?_
    suffices ν (u inter t) = 0 -> μ (f ⁻¹' u inter s) = 0 by simpa [hum, hf.measurable, hf.measurable hum]
    refine fun hu => measure_mono_null ?_ (hf.preimage_null hu)
    rw [preimage_inter]
    gcongr


中文:
定理 拟保测.restrict
  结论: {ν : 测度 β} {f : α -> β}
  证明: hf.measurable
  absolutelyContinuous := by
    refine AbsolutelyContinuous.mk fun u hum => ?_
    suffices ν (u inter t) = 0 -> μ (f ⁻¹' u inter s) = 0 by simpa [hum, hf.measurable, hf.measurable hum]
    refine fun hu => measure_mono_null ?_ (hf.preimage_null hu)
    rw [preimage_inter]
    gcongr


Depends on / 依赖: hf.measurable, measurable
-/
theorem QuasiMeasurePreserving.restrict {ν : Measure β} {f : α -> β}
    (hf : QuasiMeasurePreserving f μ ν) {t : Set β} (hmaps : MapsTo f s t) :
    QuasiMeasurePreserving f (μ.restrict s) (ν.restrict t) where
  measurable := hf.measurable
  absolutelyContinuous := by
    refine AbsolutelyContinuous.mk fun u hum => ?_
    suffices ν (u inter t) = 0 -> μ (f ⁻¹' u inter s) = 0 by simpa [hum, hf.measurable, hf.measurable hum]
    refine fun hu => measure_mono_null ?_ (hf.preimage_null hu)
    rw [preimage_inter]
    gcongr
    assumption

/-! ### Extensionality results -/

/--
theorem `ext_iff_of_iUnion_eq_univ` / 定理 `ext_iff_of_iUnion_eq_univ`

English:
theorem ext_iff_of_iUnion_eq_univ
  given: [Countable ι] {s : ι -> Set α} (hs : ⋃ i, s i = univ)
  proof: by
  rw [← restrict_iUnion_congr]; rw [hs]; rw [restrict_univ]; rw [restrict_univ]

alias ⟨_, ext_of_iUnion_eq_univ⟩ := ext_iff_of_iUnion_eq_univ

中文:
定理 ext_iff_of_iUnion_eq_univ
  条件: [可数 ι] {s : ι -> 集合 α} (hs : ⋃ i, s i = univ)
  证明: by
  rw [← restrict_iUnion_congr]; rw [hs]; rw [restrict_univ]; rw [restrict_univ]

alias ⟨_, ext_of_iUnion_eq_univ⟩ := ext_iff_of_iUnion_eq_univ

Depends on / 依赖: restrict_iUnion_congr, restrict_univ
-/
theorem ext_iff_of_iUnion_eq_univ [Countable ι] {s : ι -> Set α} (hs : ⋃ i, s i = univ) :
    μ = ν ↔ forall i, μ.restrict (s i) = ν.restrict (s i) := by
  rw [← restrict_iUnion_congr]; rw [hs]; rw [restrict_univ]; rw [restrict_univ]

alias ⟨_, ext_of_iUnion_eq_univ⟩ := ext_iff_of_iUnion_eq_univ

/--
theorem `ext_iff_of_biUnion_eq_univ` / 定理 `ext_iff_of_biUnion_eq_univ`

English:
theorem ext_iff_of_biUnion_eq_univ
  statement: {S : Set ι} {s : ι -> Set α} (hc : S.Countable)
  proof: by
  rw [← restrict_biUnion_congr hc]; rw [hs]; rw [restrict_univ]; rw [restrict_univ]

alias ⟨_, ext_of_biUnion_eq_univ⟩ := ext_iff_of_biUnion_eq_univ

中文:
定理 ext_iff_of_biUnion_eq_univ
  结论: {S : 集合 ι} {s : ι -> 集合 α} (hc : S.可数)
  证明: by
  rw [← restrict_biUnion_congr hc]; rw [hs]; rw [restrict_univ]; rw [restrict_univ]

alias ⟨_, ext_of_biUnion_eq_univ⟩ := ext_iff_of_biUnion_eq_univ

Depends on / 依赖: restrict_biUnion_congr, restrict_univ
-/
theorem ext_iff_of_biUnion_eq_univ {S : Set ι} {s : ι -> Set α} (hc : S.Countable)
    (hs : ⋃ i in S, s i = univ) : μ = ν ↔ forall i in S, μ.restrict (s i) = ν.restrict (s i) := by
  rw [← restrict_biUnion_congr hc]; rw [hs]; rw [restrict_univ]; rw [restrict_univ]

alias ⟨_, ext_of_biUnion_eq_univ⟩ := ext_iff_of_biUnion_eq_univ

/--
theorem `ext_iff_of_sUnion_eq_univ` / 定理 `ext_iff_of_sUnion_eq_univ`

English:
theorem ext_iff_of_sUnion_eq_univ
  given: {S : Set (Set α)} (hc : S.Countable) (hs : ⋃₀ S = univ)
  proof: ext_iff_of_biUnion_eq_univ hc by rwa [← sUnion_eq_biUnion]

alias ⟨_, ext_of_sUnion_eq_univ⟩ := ext_iff_of_sUnion_eq_univ

中文:
定理 ext_iff_of_sUnion_eq_univ
  条件: {S : 集合 (集合 α)} (hc : S.可数) (hs : ⋃₀ S = univ)
  证明: ext_iff_of_biUnion_eq_univ hc by rwa [← sUnion_eq_biUnion]

alias ⟨_, ext_of_sUnion_eq_univ⟩ := ext_iff_of_sUnion_eq_univ

Depends on / 依赖: ext_iff_of_biUnion_eq_univ, sUnion_eq_biUnion
-/
theorem ext_iff_of_sUnion_eq_univ {S : Set (Set α)} (hc : S.Countable) (hs : ⋃₀ S = univ) :
    μ = ν ↔ forall s in S, μ.restrict s = ν.restrict s :=
ext_iff_of_biUnion_eq_univ hc by rwa [← sUnion_eq_biUnion]

alias ⟨_, ext_of_sUnion_eq_univ⟩ := ext_iff_of_sUnion_eq_univ

/--
theorem `ext_of_generateFrom_of_cover` / 定理 `ext_of_generateFrom_of_cover`

English:
theorem ext_of_generateFrom_of_cover
  statement: {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S)
  proof: by
  refine ext_of_sUnion_eq_univ hc hU fun t ht => ?_
  ext1 u hu
  simp only [restrict_apply hu]
  induction u, hu using induction_on_inter h_gen h_inter with
  | empty => simp only [Set.empty_inter, measure_empty]
  | basic u hu => exact ST_eq _ ht _ hu
  | compl u hu ihu =>
    have := T_eq t ht

中文:
定理 ext_of_generateFrom_of_cover
  结论: {S T : 集合 (集合 α)} (h_gen : ‹_› = generateFrom S)
  证明: by
  refine ext_of_sUnion_eq_univ hc hU fun t ht => ?_
  ext1 u hu
  simp only [restrict_apply hu]
  induction u, hu using induction_on_inter h_gen h_inter with
  | empty => simp only [Set.empty_inter, measure_empty]
  | basic u hu => exact ST_eq _ ht _ hu
  | compl u hu ihu =>
    have := T_eq t ht

Depends on / 依赖: ENNReal, ENNReal.add_right_inj, ST_eq, Set.empty_inter, Set.inter_comm, Set.inter_subset_left, T_eq, add_right_inj, empty_inter, ext_of_sUnion_eq_univ, h_gen, h_inter, induction_on_inter, inter_comm, inter_subset_left, measure_empty, measure_inter_add_sdiff, measure_mono, ne_top_of_le_ne_top, restrict_apply
-/
theorem ext_of_generateFrom_of_cover {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S)
    (hc : T.Countable) (h_inter : IsPiSystem S) (hU : ⋃₀ T = univ) (htop : forall t in T, μ t != ∞)
    (ST_eq : forall t in T, forall s in S, μ (s inter t) = ν (s inter t)) (T_eq : forall t in T, μ t = ν t) : μ = ν := by
  refine ext_of_sUnion_eq_univ hc hU fun t ht => ?_
  ext1 u hu
  simp only [restrict_apply hu]
  induction u, hu using induction_on_inter h_gen h_inter with
  | empty => simp only [Set.empty_inter, measure_empty]
  | basic u hu => exact ST_eq _ ht _ hu
  | compl u hu ihu =>
    have := T_eq t ht
    rw [Set.inter_comm] at ihu ⊢
    rwa [← measure_inter_add_sdiff t hu, ← measure_inter_add_sdiff t hu, ← ihu,
      ENNReal.add_right_inj] at this
    exact ne_top_of_le_ne_top (htop t ht) (measure_mono Set.inter_subset_left)
  | iUnion f hfd hfm ihf =>
    simp only [← restrict_apply (hfm _), ← restrict_apply (MeasurableSet.iUnion hfm)] at ihf ⊢
    simp only [measure_iUnion hfd hfm, ihf]

/--
theorem `ext_of_generateFrom_of_cover_subset` / 定理 `ext_of_generateFrom_of_cover_subset`

English:
theorem ext_of_generateFrom_of_cover_subset
  statement: {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S)
  proof: by
  refine ext_of_generateFrom_of_cover h_gen hc h_inter hU htop ?_ fun t ht => h_eq t (h_sub ht)
  intro t ht s hs; rcases (s inter t).eq_empty_or_nonempty with H | H
  · simp only [H, measure_empty]
  · exact h_eq _ (h_inter _ hs _ (h_sub ht) H)

中文:
定理 ext_of_generateFrom_of_cover_subset
  结论: {S T : 集合 (集合 α)} (h_gen : ‹_› = generateFrom S)
  证明: by
  refine ext_of_generateFrom_of_cover h_gen hc h_inter hU htop ?_ fun t ht => h_eq t (h_sub ht)
  intro t ht s hs; rcases (s inter t).eq_empty_or_nonempty with H | H
  · simp only [H, measure_empty]
  · exact h_eq _ (h_inter _ hs _ (h_sub ht) H)

Depends on / 依赖: eq_empty_or_nonempty, ext_of_generateFrom_of_cover, h_eq, h_gen, h_inter, h_sub, measure_empty
-/
theorem ext_of_generateFrom_of_cover_subset {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S)
    (h_inter : IsPiSystem S) (h_sub : T subseteq S) (hc : T.Countable) (hU : ⋃₀ T = univ)
    (htop : forall s in T, μ s != ∞) (h_eq : forall s in S, μ s = ν s) : μ = ν := by
  refine ext_of_generateFrom_of_cover h_gen hc h_inter hU htop ?_ fun t ht => h_eq t (h_sub ht)
  intro t ht s hs; rcases (s inter t).eq_empty_or_nonempty with H | H
  · simp only [H, measure_empty]
  · exact h_eq _ (h_inter _ hs _ (h_sub ht) H)

/--
theorem `ext_of_generateFrom_of_iUnion` / 定理 `ext_of_generateFrom_of_iUnion`

English:
theorem ext_of_generateFrom_of_iUnion
  statement: (C : Set (Set α)) (B : Nat -> Set α) (hA : ‹_› = generateFrom C)
  proof: by
  refine ext_of_generateFrom_of_cover_subset hA hC ?_ (countable_range B) h1B ?_ h_eq
  · rintro _ ⟨i, rfl⟩
    apply h2B
  · rintro _ ⟨i, rfl⟩
    apply hμB

@[simp]

中文:
定理 ext_of_generateFrom_of_iUnion
  结论: (C : 集合 (集合 α)) (B : 自然数 -> 集合 α) (hA : ‹_› = generateFrom C)
  证明: by
  refine ext_of_generateFrom_of_cover_subset hA hC ?_ (countable_range B) h1B ?_ h_eq
  · rintro _ ⟨i, rfl⟩
    apply h2B
  · rintro _ ⟨i, rfl⟩
    apply hμB

@[simp]

Depends on / 依赖: countable_range, ext_of_generateFrom_of_cover_subset, h_eq
-/
theorem ext_of_generateFrom_of_iUnion (C : Set (Set α)) (B : Nat -> Set α) (hA : ‹_› = generateFrom C)
    (hC : IsPiSystem C) (h1B : ⋃ i, B i = univ) (h2B : forall i, B i in C) (hμB : forall i, μ (B i) != ∞)
    (h_eq : forall s in C, μ s = ν s) : μ = ν := by
  refine ext_of_generateFrom_of_cover_subset hA hC ?_ (countable_range B) h1B ?_ h_eq
  · rintro _ ⟨i, rfl⟩
    apply h2B
  · rintro _ ⟨i, rfl⟩
    apply hμB

@[simp]
/--
theorem `restrict_sum` / 定理 `restrict_sum`

English:
theorem restrict_sum
  given: (μ : ι -> Measure α) {s : Set α} (hs : MeasurableSet s)
  proof: ext fun t ht => by simp only [sum_apply, restrict_apply, ht, ht.inter hs]

@[simp]

中文:
定理 restrict_sum
  条件: (μ : ι -> 测度 α) {s : 集合 α} (hs : 可测集 s)
  证明: ext fun t ht => by simp only [sum_apply, restrict_apply, ht, ht.inter hs]

@[simp]

Depends on / 依赖: ht.inter, restrict_apply, sum_apply
-/
theorem restrict_sum (μ : ι -> Measure α) {s : Set α} (hs : MeasurableSet s) :
    (sum μ).restrict s = sum fun i => (μ i).restrict s :=
  ext fun t ht => by simp only [sum_apply, restrict_apply, ht, ht.inter hs]

@[simp]
/--
theorem `restrict_sum_of_countable` / 定理 `restrict_sum_of_countable`

English:
theorem restrict_sum_of_countable
  given: [Countable ι] (μ : ι -> Measure α) (s : Set α)
  proof: by
  ext t ht
  simp_rw [sum_apply _ ht, restrict_apply ht, sum_apply_of_countable]

中文:
定理 restrict_sum_of_countable
  条件: [可数 ι] (μ : ι -> 测度 α) (s : 集合 α)
  证明: by
  ext t ht
  simp_rw [sum_apply _ ht, restrict_apply ht, sum_apply_of_countable]

Depends on / 依赖: restrict_apply, simp_rw, sum_apply, sum_apply_of_countable
-/
theorem restrict_sum_of_countable [Countable ι] (μ : ι -> Measure α) (s : Set α) :
    (sum μ).restrict s = sum fun i => (μ i).restrict s := by
  ext t ht
  simp_rw [sum_apply _ ht, restrict_apply ht, sum_apply_of_countable]

/--
lemma `AbsolutelyContinuous.restrict` / 引理 `AbsolutelyContinuous.restrict`

English:
lemma AbsolutelyContinuous.restrict
  given: (h : μ ≪ ν) (s : Set α)
  statement: μ.restrict s ≪ ν.restrict s
  proof: by
  refine Measure.AbsolutelyContinuous.mk (fun t ht htν => ?_)
  rw [restrict_apply ht] at htν ⊢
  exact h htν

中文:
引理 AbsolutelyContinuous.restrict
  条件: (h : μ ≪ ν) (s : 集合 α)
  结论: μ.restrict s ≪ ν.restrict s
  证明: by
  refine Measure.AbsolutelyContinuous.mk (fun t ht htν => ?_)
  rw [restrict_apply ht] at htν ⊢
  exact h htν

Depends on / 依赖: AbsolutelyContinuous, ConcreteCategory, ConcreteCategory.ofHom, Measure, Measure.AbsolutelyContinuous.mk, restrict_apply
-/
lemma AbsolutelyContinuous.restrict (h : μ ≪ ν) (s : Set α) : μ.restrict s ≪ ν.restrict s := by
  refine Measure.AbsolutelyContinuous.mk (fun t ht htν => ?_)
  rw [restrict_apply ht] at htν ⊢
  exact h htν

/--
theorem `restrict_iUnion_ae` / 定理 `restrict_iUnion_ae`

English:
theorem restrict_iUnion_ae
  statement: [Countable ι] {s : ι -> Set α} (hd : Pairwise (AEDisjoint μ on s))
  proof: ext fun t ht => by simp only [sum_apply _ ht, restrict_iUnion_apply_ae hd hm ht]

中文:
定理 restrict_iUnion_ae
  结论: [可数 ι] {s : ι -> 集合 α} (hd : 两两 (AEDisjoint μ on s))
  证明: ext fun t ht => by simp only [sum_apply _ ht, restrict_iUnion_apply_ae hd hm ht]

Depends on / 依赖: restrict_iUnion_apply_ae, sum_apply
-/
theorem restrict_iUnion_ae [Countable ι] {s : ι -> Set α} (hd : Pairwise (AEDisjoint μ on s))
    (hm : forall i, NullMeasurableSet (s i) μ) : μ.restrict (⋃ i, s i) = sum fun i => μ.restrict (s i) :=
  ext fun t ht => by simp only [sum_apply _ ht, restrict_iUnion_apply_ae hd hm ht]

/--
theorem `restrict_iUnion` / 定理 `restrict_iUnion`

English:
theorem restrict_iUnion
  statement: [Countable ι] {s : ι -> Set α} (hd : Pairwise (Disjoint on s))
  proof: restrict_iUnion_ae hd.aedisjoint fun i => (hm i).nullMeasurableSet

中文:
定理 restrict_iUnion
  结论: [可数 ι] {s : ι -> 集合 α} (hd : 两两 (Disjoint on s))
  证明: restrict_iUnion_ae hd.aedisjoint fun i => (hm i).nullMeasurableSet

Depends on / 依赖: aedisjoint, hd.aedisjoint, nullMeasurableSet, restrict_iUnion_ae
-/
theorem restrict_iUnion [Countable ι] {s : ι -> Set α} (hd : Pairwise (Disjoint on s))
    (hm : forall i, MeasurableSet (s i)) : μ.restrict (⋃ i, s i) = sum fun i => μ.restrict (s i) :=
  restrict_iUnion_ae hd.aedisjoint fun i => (hm i).nullMeasurableSet

/--
theorem `restrict_biUnion` / 定理 `restrict_biUnion`

English:
theorem restrict_biUnion
  statement: {s : ι -> Set α} {T : Set ι} (hT : Countable T)
  proof: by
  rw [Set.biUnion_eq_iUnion]
  exact restrict_iUnion (fun i j hij => hd i.coe_prop j.coe_prop (Subtype.coe_ne_coe.mpr hij)) (hm ·)

中文:
定理 restrict_biUnion
  结论: {s : ι -> 集合 α} {T : 集合 ι} (hT : 可数 T)
  证明: by
  rw [Set.biUnion_eq_iUnion]
  exact restrict_iUnion (fun i j hij => hd i.coe_prop j.coe_prop (Subtype.coe_ne_coe.mpr hij)) (hm ·)

Depends on / 依赖: Set.biUnion_eq_iUnion, Subtype, Subtype.coe_ne_coe.mpr, biUnion_eq_iUnion, coe_ne_coe, coe_prop, i.coe_prop, j.coe_prop, restrict_iUnion
-/
theorem restrict_biUnion {s : ι -> Set α} {T : Set ι} (hT : Countable T)
    (hd : T.Pairwise (Disjoint on s)) (hm : forall i, MeasurableSet (s i)) :
    μ.restrict (⋃ i in T, s i) = sum fun (i : T) => μ.restrict (s i) := by
  rw [Set.biUnion_eq_iUnion]
  exact restrict_iUnion (fun i j hij => hd i.coe_prop j.coe_prop (Subtype.coe_ne_coe.mpr hij)) (hm ·)

/--
theorem `restrict_biUnion_finset` / 定理 `restrict_biUnion_finset`

English:
theorem restrict_biUnion_finset
  statement: {s : ι -> Set α} {T : Finset ι}
  proof: restrict_biUnion (T := (T : Set ι)) Finite.to_countable hd hm

中文:
定理 restrict_biUnion_finset
  结论: {s : ι -> 集合 α} {T : 有限集 ι}
  证明: restrict_biUnion (T := (T : Set ι)) Finite.to_countable hd hm

Depends on / 依赖: Finite, Finite.to_countable, restrict_biUnion, to_countable
-/
theorem restrict_biUnion_finset {s : ι -> Set α} {T : Finset ι}
    (hd : (T : Set ι).Pairwise (Disjoint on s)) (hm : forall i, MeasurableSet (s i)) :
    μ.restrict (⋃ i in T, s i) = sum fun (i : T) => μ.restrict (s i) :=
  restrict_biUnion (T := (T : Set ι)) Finite.to_countable hd hm

/--
theorem `restrict_iUnion_le` / 定理 `restrict_iUnion_le`

English:
theorem restrict_iUnion_le
  given: [Countable ι] {s : ι -> Set α}
  proof: le_iff.2 fun t ht => by simpa [ht, inter_iUnion] using measure_iUnion_le (t inter s ·)

中文:
定理 restrict_iUnion_le
  条件: [可数 ι] {s : ι -> 集合 α}
  证明: le_iff.2 fun t ht => by simpa [ht, inter_iUnion] using measure_iUnion_le (t inter s ·)

Depends on / 依赖: inter_iUnion, le_iff, measure_iUnion_le
-/
theorem restrict_iUnion_le [Countable ι] {s : ι -> Set α} :
    μ.restrict (⋃ i, s i) <= sum fun i => μ.restrict (s i) :=
  le_iff.2 fun t ht => by simpa [ht, inter_iUnion] using measure_iUnion_le (t inter s ·)

/--
theorem `restrict_biUnion_le` / 定理 `restrict_biUnion_le`

English:
theorem restrict_biUnion_le
  given: {s : ι -> Set α} {T : Set ι} (hT : Countable T)
  proof: le_iff.2 fun t ht => by simpa [ht, inter_iUnion] using measure_biUnion_le μ hT (t inter s ·)

中文:
定理 restrict_biUnion_le
  条件: {s : ι -> 集合 α} {T : 集合 ι} (hT : 可数 T)
  证明: le_iff.2 fun t ht => by simpa [ht, inter_iUnion] using measure_biUnion_le μ hT (t inter s ·)

Depends on / 依赖: inter_iUnion, le_iff, measure_biUnion_le
-/
theorem restrict_biUnion_le {s : ι -> Set α} {T : Set ι} (hT : Countable T) :
    μ.restrict (⋃ i in T, s i) <= sum fun (i : T) => μ.restrict (s i) :=
  le_iff.2 fun t ht => by simpa [ht, inter_iUnion] using measure_biUnion_le μ hT (t inter s ·)

end Measure

@[simp]
/--
theorem `ae_restrict_iUnion_eq` / 定理 `ae_restrict_iUnion_eq`

English:
theorem ae_restrict_iUnion_eq
  given: [Countable ι] (s : ι -> Set α)
  proof: le_antisymm ((ae_sum_eq fun i => μ.restrict (s i)) ▸ ae_mono restrict_iUnion_le)
iSup_le fun i => ae_mono restrict_mono (subset_iUnion s i) le_rfl

@[simp]

中文:
定理 ae_restrict_iUnion_eq
  条件: [可数 ι] (s : ι -> 集合 α)
  证明: le_antisymm ((ae_sum_eq fun i => μ.restrict (s i)) ▸ ae_mono restrict_iUnion_le)
iSup_le fun i => ae_mono restrict_mono (subset_iUnion s i) le_rfl

@[simp]

Depends on / 依赖: ae_mono, ae_sum_eq, iSup_le, le_antisymm, le_rfl, restrict, restrict_iUnion_le, restrict_mono, subset_iUnion
-/
theorem ae_restrict_iUnion_eq [Countable ι] (s : ι -> Set α) :
    ae (μ.restrict (⋃ i, s i)) = ⨆ i, ae (μ.restrict (s i)) :=
le_antisymm ((ae_sum_eq fun i => μ.restrict (s i)) ▸ ae_mono restrict_iUnion_le)
iSup_le fun i => ae_mono restrict_mono (subset_iUnion s i) le_rfl

@[simp]
/--
theorem `ae_restrict_union_eq` / 定理 `ae_restrict_union_eq`

English:
theorem ae_restrict_union_eq
  given: (s t : Set α)
  proof: by
  simp [union_eq_iUnion, iSup_bool_eq]

中文:
定理 ae_restrict_union_eq
  条件: (s t : 集合 α)
  证明: by
  simp [union_eq_iUnion, iSup_bool_eq]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, DistLat, iSup_bool_eq, union_eq_iUnion
-/
theorem ae_restrict_union_eq (s t : Set α) :
    ae (μ.restrict (s union t)) = ae (μ.restrict s) ⊔ ae (μ.restrict t) := by
  simp [union_eq_iUnion, iSup_bool_eq]

/--
theorem `ae_restrict_biUnion_eq` / 定理 `ae_restrict_biUnion_eq`

English:
theorem ae_restrict_biUnion_eq
  given: (s : ι -> Set α) {t : Set ι} (ht : t.Countable)
  proof: by
  have := ht.to_subtype
  rw [biUnion_eq_iUnion]; rw [ae_restrict_iUnion_eq]; rw [← iSup_subtype'']

中文:
定理 ae_restrict_biUnion_eq
  条件: (s : ι -> 集合 α) {t : 集合 ι} (ht : t.可数)
  证明: by
  have := ht.to_subtype
  rw [biUnion_eq_iUnion]; rw [ae_restrict_iUnion_eq]; rw [← iSup_subtype'']

Depends on / 依赖: ae_restrict_iUnion_eq, biUnion_eq_iUnion, ht.to_subtype, iSup_subtype, to_subtype
-/
theorem ae_restrict_biUnion_eq (s : ι -> Set α) {t : Set ι} (ht : t.Countable) :
    ae (μ.restrict (⋃ i in t, s i)) = ⨆ i in t, ae (μ.restrict (s i)) := by
  have := ht.to_subtype
  rw [biUnion_eq_iUnion]; rw [ae_restrict_iUnion_eq]; rw [← iSup_subtype'']

/--
theorem `ae_restrict_biUnion_finset_eq` / 定理 `ae_restrict_biUnion_finset_eq`

English:
theorem ae_restrict_biUnion_finset_eq
  given: (s : ι -> Set α) (t : Finset ι)
  proof: ae_restrict_biUnion_eq s t.countable_toSet

中文:
定理 ae_restrict_biUnion_finset_eq
  条件: (s : ι -> 集合 α) (t : 有限集 ι)
  证明: ae_restrict_biUnion_eq s t.countable_toSet

Depends on / 依赖: ae_restrict_biUnion_eq, countable_toSet, f.hom, t.countable_toSet
-/
theorem ae_restrict_biUnion_finset_eq (s : ι -> Set α) (t : Finset ι) :
    ae (μ.restrict (⋃ i in t, s i)) = ⨆ i in t, ae (μ.restrict (s i)) :=
  ae_restrict_biUnion_eq s t.countable_toSet

/--
theorem `ae_restrict_iUnion_iff` / 定理 `ae_restrict_iUnion_iff`

English:
theorem ae_restrict_iUnion_iff
  given: [Countable ι] (s : ι -> Set α) (p : α -> Prop)
  proof: by simp

中文:
定理 ae_restrict_iUnion_iff
  条件: [可数 ι] (s : ι -> 集合 α) (p : α -> 命题)
  证明: by simp
-/
theorem ae_restrict_iUnion_iff [Countable ι] (s : ι -> Set α) (p : α -> Prop) :
    (forallᵐ x ∂μ.restrict (⋃ i, s i), p x) ↔ forall i, forallᵐ x ∂μ.restrict (s i), p x := by simp

/--
theorem `ae_restrict_union_iff` / 定理 `ae_restrict_union_iff`

English:
theorem ae_restrict_union_iff
  given: (s t : Set α) (p : α -> Prop)
  proof: by simp

中文:
定理 ae_restrict_union_iff
  条件: (s t : 集合 α) (p : α -> 命题)
  证明: by simp
-/
theorem ae_restrict_union_iff (s t : Set α) (p : α -> Prop) :
    (forallᵐ x ∂μ.restrict (s union t), p x) ↔ (forallᵐ x ∂μ.restrict s, p x) ∧ forallᵐ x ∂μ.restrict t, p x := by simp

/--
theorem `ae_restrict_biUnion_iff` / 定理 `ae_restrict_biUnion_iff`

English:
theorem ae_restrict_biUnion_iff
  given: (s : ι -> Set α) {t : Set ι} (ht : t.Countable) (p : α -> Prop)
  proof: by
  simp_rw [Filter.Eventually, ae_restrict_biUnion_eq s ht, mem_iSup]

@[simp]

中文:
定理 ae_restrict_biUnion_iff
  条件: (s : ι -> 集合 α) {t : 集合 ι} (ht : t.可数) (p : α -> 命题)
  证明: by
  simp_rw [Filter.Eventually, ae_restrict_biUnion_eq s ht, mem_iSup]

@[simp]

Depends on / 依赖: Eventually, Filter, Filter.Eventually, ae_restrict_biUnion_eq, mem_iSup, simp_rw
-/
theorem ae_restrict_biUnion_iff (s : ι -> Set α) {t : Set ι} (ht : t.Countable) (p : α -> Prop) :
    (forallᵐ x ∂μ.restrict (⋃ i in t, s i), p x) ↔ forall i in t, forallᵐ x ∂μ.restrict (s i), p x := by
  simp_rw [Filter.Eventually, ae_restrict_biUnion_eq s ht, mem_iSup]

@[simp]
/--
theorem `ae_restrict_biUnion_finset_iff` / 定理 `ae_restrict_biUnion_finset_iff`

English:
theorem ae_restrict_biUnion_finset_iff
  given: (s : ι -> Set α) (t : Finset ι) (p : α -> Prop)
  proof: by
  simp_rw [Filter.Eventually, ae_restrict_biUnion_finset_eq s, mem_iSup]

中文:
定理 ae_restrict_biUnion_finset_iff
  条件: (s : ι -> 集合 α) (t : 有限集 ι) (p : α -> 命题)
  证明: by
  simp_rw [Filter.Eventually, ae_restrict_biUnion_finset_eq s, mem_iSup]

Depends on / 依赖: Eventually, Filter, Filter.Eventually, ae_restrict_biUnion_finset_eq, mem_iSup, simp_rw
-/
theorem ae_restrict_biUnion_finset_iff (s : ι -> Set α) (t : Finset ι) (p : α -> Prop) :
    (forallᵐ x ∂μ.restrict (⋃ i in t, s i), p x) ↔ forall i in t, forallᵐ x ∂μ.restrict (s i), p x := by
  simp_rw [Filter.Eventually, ae_restrict_biUnion_finset_eq s, mem_iSup]

/--
theorem `ae_eq_restrict_iUnion_iff` / 定理 `ae_eq_restrict_iUnion_iff`

English:
theorem ae_eq_restrict_iUnion_iff
  given: [Countable ι] (s : ι -> Set α) (f g : α -> δ)
  proof: by
  simp_rw [EventuallyEq, ae_restrict_iUnion_eq, eventually_iSup]

中文:
定理 ae_eq_restrict_iUnion_iff
  条件: [可数 ι] (s : ι -> 集合 α) (f g : α -> δ)
  证明: by
  simp_rw [EventuallyEq, ae_restrict_iUnion_eq, eventually_iSup]

Depends on / 依赖: EventuallyEq, ae_restrict_iUnion_eq, eventually_iSup, simp_rw
-/
theorem ae_eq_restrict_iUnion_iff [Countable ι] (s : ι -> Set α) (f g : α -> δ) :
    f =ᵐ[μ.restrict (⋃ i, s i)] g ↔ forall i, f =ᵐ[μ.restrict (s i)] g := by
  simp_rw [EventuallyEq, ae_restrict_iUnion_eq, eventually_iSup]

/--
theorem `ae_eq_restrict_biUnion_iff` / 定理 `ae_eq_restrict_biUnion_iff`

English:
theorem ae_eq_restrict_biUnion_iff
  given: (s : ι -> Set α) {t : Set ι} (ht : t.Countable) (f g : α -> δ)
  proof: by
  simp_rw [ae_restrict_biUnion_eq s ht, EventuallyEq, eventually_iSup]

中文:
定理 ae_eq_restrict_biUnion_iff
  条件: (s : ι -> 集合 α) {t : 集合 ι} (ht : t.可数) (f g : α -> δ)
  证明: by
  simp_rw [ae_restrict_biUnion_eq s ht, EventuallyEq, eventually_iSup]

Depends on / 依赖: EventuallyEq, ae_restrict_biUnion_eq, eventually_iSup, simp_rw
-/
theorem ae_eq_restrict_biUnion_iff (s : ι -> Set α) {t : Set ι} (ht : t.Countable) (f g : α -> δ) :
    f =ᵐ[μ.restrict (⋃ i in t, s i)] g ↔ forall i in t, f =ᵐ[μ.restrict (s i)] g := by
  simp_rw [ae_restrict_biUnion_eq s ht, EventuallyEq, eventually_iSup]

/--
theorem `ae_eq_restrict_biUnion_finset_iff` / 定理 `ae_eq_restrict_biUnion_finset_iff`

English:
theorem ae_eq_restrict_biUnion_finset_iff
  given: (s : ι -> Set α) (t : Finset ι) (f g : α -> δ)
  proof: ae_eq_restrict_biUnion_iff s t.countable_toSet f g

中文:
定理 ae_eq_restrict_biUnion_finset_iff
  条件: (s : ι -> 集合 α) (t : 有限集 ι) (f g : α -> δ)
  证明: ae_eq_restrict_biUnion_iff s t.countable_toSet f g

Depends on / 依赖: ae_eq_restrict_biUnion_iff, countable_toSet, t.countable_toSet
-/
theorem ae_eq_restrict_biUnion_finset_iff (s : ι -> Set α) (t : Finset ι) (f g : α -> δ) :
    f =ᵐ[μ.restrict (⋃ i in t, s i)] g ↔ forall i in t, f =ᵐ[μ.restrict (s i)] g :=
  ae_eq_restrict_biUnion_iff s t.countable_toSet f g

open scoped Interval in
/--
theorem `ae_restrict_uIoc_eq` / 定理 `ae_restrict_uIoc_eq`

English:
theorem ae_restrict_uIoc_eq
  given: [LinearOrder α] (a b : α)
  proof: by
  simp only [uIoc_eq_union, ae_restrict_union_eq]

中文:
定理 ae_restrict_uIoc_eq
  条件: [线性序 α] (a b : α)
  证明: by
  simp only [uIoc_eq_union, ae_restrict_union_eq]

Depends on / 依赖: ae_restrict_union_eq, uIoc_eq_union
-/
theorem ae_restrict_uIoc_eq [LinearOrder α] (a b : α) :
    ae (μ.restrict (Ι a b)) = ae (μ.restrict (Ioc a b)) ⊔ ae (μ.restrict (Ioc b a)) := by
  simp only [uIoc_eq_union, ae_restrict_union_eq]

open scoped Interval in
/--
theorem `ae_restrict_uIoc_iff` / 定理 `ae_restrict_uIoc_iff`

English:
theorem ae_restrict_uIoc_iff
  given: [LinearOrder α] {a b : α} {P : α -> Prop}
  proof: by
  rw [ae_restrict_uIoc_eq]; rw [eventually_sup]

中文:
定理 ae_restrict_uIoc_iff
  条件: [线性序 α] {a b : α} {P : α -> 命题}
  证明: by
  rw [ae_restrict_uIoc_eq]; rw [eventually_sup]

Depends on / 依赖: ae_restrict_uIoc_eq, eventually_sup
-/
theorem ae_restrict_uIoc_iff [LinearOrder α] {a b : α} {P : α -> Prop} :
    (forallᵐ x ∂μ.restrict (Ι a b), P x) ↔
      (forallᵐ x ∂μ.restrict (Ioc a b), P x) ∧ forallᵐ x ∂μ.restrict (Ioc b a), P x := by
  rw [ae_restrict_uIoc_eq]; rw [eventually_sup]

/--
theorem `ae_restrict_iff₀` / 定理 `ae_restrict_iff₀`

English:
theorem ae_restrict_iff₀
  given: {p : α -> Prop} (hp : NullMeasurableSet { x | p x } (μ.restrict s))
  proof: by
  simp only [ae_iff, ← compl_ofPred, Measure.restrict_apply₀ hp.compl]
  rw [iff_iff_eq]; congr with x; simp [and_comm]

中文:
定理 ae_restrict_iff₀
  条件: {p : α -> 命题} (hp : NullMeasurableSet { x | p x } (μ.restrict s))
  证明: by
  simp only [ae_iff, ← compl_ofPred, Measure.restrict_apply₀ hp.compl]
  rw [iff_iff_eq]; congr with x; simp [and_comm]

Depends on / 依赖: Measure, Measure.restrict_apply, ae_iff, and_comm, compl_ofPred, hp.compl, iff_iff_eq
-/
theorem ae_restrict_iff₀ {p : α -> Prop} (hp : NullMeasurableSet { x | p x } (μ.restrict s)) :
    (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -> p x := by
  simp only [ae_iff, ← compl_ofPred, Measure.restrict_apply₀ hp.compl]
  rw [iff_iff_eq]; congr with x; simp [and_comm]

/--
theorem `ae_restrict_iff` / 定理 `ae_restrict_iff`

English:
theorem ae_restrict_iff
  given: {p : α -> Prop} (hp : MeasurableSet { x | p x })
  proof: ae_restrict_iff₀ hp.nullMeasurableSet

中文:
定理 ae_restrict_iff
  条件: {p : α -> 命题} (hp : 可测集 { x | p x })
  证明: ae_restrict_iff₀ hp.nullMeasurableSet

Depends on / 依赖: hp.nullMeasurableSet, nullMeasurableSet
-/
theorem ae_restrict_iff {p : α -> Prop} (hp : MeasurableSet { x | p x }) :
    (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -> p x :=
  ae_restrict_iff₀ hp.nullMeasurableSet

/--
theorem `ae_imp_of_ae_restrict` / 定理 `ae_imp_of_ae_restrict`

English:
theorem ae_imp_of_ae_restrict
  given: {s : Set α} {p : α -> Prop} (h : forallᵐ x ∂μ.restrict s, p x)
  proof: by
  simp only [ae_iff] at h ⊢
  simpa [ofPred_and, inter_comm] using measure_inter_eq_zero_of_restrict h

中文:
定理 ae_imp_of_ae_restrict
  条件: {s : 集合 α} {p : α -> 命题} (h : 对任意ᵐ x ∂μ.restrict s, p x)
  证明: by
  simp only [ae_iff] at h ⊢
  simpa [ofPred_and, inter_comm] using measure_inter_eq_zero_of_restrict h

Depends on / 依赖: ae_iff, inter_comm, measure_inter_eq_zero_of_restrict, ofPred_and
-/
theorem ae_imp_of_ae_restrict {s : Set α} {p : α -> Prop} (h : forallᵐ x ∂μ.restrict s, p x) :
    forallᵐ x ∂μ, x in s -> p x := by
  simp only [ae_iff] at h ⊢
  simpa [ofPred_and, inter_comm] using measure_inter_eq_zero_of_restrict h

/--
theorem `ae_restrict_iff'₀` / 定理 `ae_restrict_iff'₀`

English:
theorem ae_restrict_iff'₀
  given: {p : α -> Prop} (hs : NullMeasurableSet s μ)
  proof: by
  simp only [ae_iff, ← compl_ofPred, restrict_apply₀' hs]
  rw [iff_iff_eq]; congr with x; simp [and_comm]

中文:
定理 ae_restrict_iff'₀
  条件: {p : α -> 命题} (hs : NullMeasurableSet s μ)
  证明: by
  simp only [ae_iff, ← compl_ofPred, restrict_apply₀' hs]
  rw [iff_iff_eq]; congr with x; simp [and_comm]

Depends on / 依赖: ae_iff, and_comm, compl_ofPred, iff_iff_eq
-/
theorem ae_restrict_iff'₀ {p : α -> Prop} (hs : NullMeasurableSet s μ) :
    (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -> p x := by
  simp only [ae_iff, ← compl_ofPred, restrict_apply₀' hs]
  rw [iff_iff_eq]; congr with x; simp [and_comm]

/--
theorem `ae_restrict_iff'` / 定理 `ae_restrict_iff'`

English:
theorem ae_restrict_iff'
  given: {p : α -> Prop} (hs : MeasurableSet s)
  proof: ae_restrict_iff'₀ hs.nullMeasurableSet

中文:
定理 ae_restrict_iff'
  条件: {p : α -> 命题} (hs : 可测集 s)
  证明: ae_restrict_iff'₀ hs.nullMeasurableSet
-/
theorem ae_restrict_iff' {p : α -> Prop} (hs : MeasurableSet s) :
    (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -> p x :=
  ae_restrict_iff'₀ hs.nullMeasurableSet

/--
theorem `_root_.Filter.EventuallyEq.restrict` / 定理 `_root_.Filter.EventuallyEq.restrict`

English:
theorem _root_.Filter.EventuallyEq.restrict
  given: {f g : α -> δ} {s : Set α} (hfg : f =ᵐ[μ] g)
  proof: by
  -- note that we cannot use `ae_restrict_iff` since we do not require measurability
  refine hfg.filter_mono ?_
  rw [Measure.ae_le_iff_absolutelyContinuous]
  exact absolutelyContinuous_restrict

中文:
定理 _root_.滤子.EventuallyEq.restrict
  条件: {f g : α -> δ} {s : 集合 α} (hfg : f =ᵐ[μ] g)
  证明: by
  -- note that we cannot use `ae_restrict_iff` since we do not require measurability
  refine hfg.filter_mono ?_
  rw [Measure.ae_le_iff_absolutelyContinuous]
  exact absolutelyContinuous_restrict
-/
theorem _root_.Filter.EventuallyEq.restrict {f g : α -> δ} {s : Set α} (hfg : f =ᵐ[μ] g) :
    f =ᵐ[μ.restrict s] g := by
  -- note that we cannot use `ae_restrict_iff` since we do not require measurability
  refine hfg.filter_mono ?_
  rw [Measure.ae_le_iff_absolutelyContinuous]
  exact absolutelyContinuous_restrict

/--
theorem `ae_restrict_mem₀` / 定理 `ae_restrict_mem₀`

English:
theorem ae_restrict_mem₀
  given: (hs : NullMeasurableSet s μ)
  statement: forallᵐ x ∂μ.restrict s, x in s
  proof: (ae_restrict_iff'₀ hs).2 (Filter.Eventually.of_forall fun _ => id)

中文:
定理 ae_restrict_mem₀
  条件: (hs : NullMeasurableSet s μ)
  结论: 对任意ᵐ x ∂μ.restrict s, x in s
  证明: (ae_restrict_iff'₀ hs).2 (Filter.Eventually.of_forall fun _ => id)

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, ae_restrict_iff, of_forall
-/
theorem ae_restrict_mem₀ (hs : NullMeasurableSet s μ) : forallᵐ x ∂μ.restrict s, x in s :=
  (ae_restrict_iff'₀ hs).2 (Filter.Eventually.of_forall fun _ => id)

/--
theorem `ae_restrict_mem` / 定理 `ae_restrict_mem`

English:
theorem ae_restrict_mem
  given: (hs : MeasurableSet s)
  statement: forallᵐ x ∂μ.restrict s, x in s
  proof: ae_restrict_mem₀ hs.nullMeasurableSet

中文:
定理 ae_restrict_mem
  条件: (hs : 可测集 s)
  结论: 对任意ᵐ x ∂μ.restrict s, x in s
  证明: ae_restrict_mem₀ hs.nullMeasurableSet

Depends on / 依赖: hs.nullMeasurableSet, nullMeasurableSet
-/
theorem ae_restrict_mem (hs : MeasurableSet s) : forallᵐ x ∂μ.restrict s, x in s :=
  ae_restrict_mem₀ hs.nullMeasurableSet

/--
theorem `ae_restrict_of_forall_mem` / 定理 `ae_restrict_of_forall_mem`

English:
theorem ae_restrict_of_forall_mem
  statement: {μ : Measure α} {s : Set α}
  proof: (ae_restrict_mem hs).mono h

中文:
定理 ae_restrict_of_对任意_mem
  结论: {μ : 测度 α} {s : 集合 α}
  证明: (ae_restrict_mem hs).mono h

Depends on / 依赖: ae_restrict_mem
-/
theorem ae_restrict_of_forall_mem {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {p : α -> Prop} (h : forall x in s, p x) : forallᵐ (x : α) ∂μ.restrict s, p x :=
  (ae_restrict_mem hs).mono h

/--
lemma `_root_.Set.EqOn.aeEq_restrict` / 引理 `_root_.Set.EqOn.aeEq_restrict`

English:
lemma _root_.Set.EqOn.aeEq_restrict
  statement: {α β : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
  proof: ae_restrict_of_forall_mem hs h

中文:
引理 _root_.集合.EqOn.aeEq_restrict
  结论: {α β : 类型} [可测空间 α] {μ : 测度 α} {s : 集合 α}
  证明: ae_restrict_of_forall_mem hs h

Depends on / 依赖: ae_restrict_of_forall_mem
-/
lemma _root_.Set.EqOn.aeEq_restrict {α β : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f g : α -> β} (h : s.EqOn f g) (hs : MeasurableSet s) : f =ᵐ[μ.restrict s] g :=
  ae_restrict_of_forall_mem hs h

/--
theorem `ae_restrict_of_ae` / 定理 `ae_restrict_of_ae`

English:
theorem ae_restrict_of_ae
  given: {s : Set α} {p : α -> Prop} (h : forallᵐ x ∂μ, p x)
  statement: forallᵐ x ∂μ.restrict s, p x
  proof: h.filter_mono (ae_mono Measure.restrict_le_self)

中文:
定理 ae_restrict_of_ae
  条件: {s : 集合 α} {p : α -> 命题} (h : 对任意ᵐ x ∂μ, p x)
  结论: 对任意ᵐ x ∂μ.restrict s, p x
  证明: h.filter_mono (ae_mono Measure.restrict_le_self)

Depends on / 依赖: Measure, Measure.restrict_le_self, ae_mono, filter_mono, h.filter_mono, restrict_le_self
-/
theorem ae_restrict_of_ae {s : Set α} {p : α -> Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x :=
  h.filter_mono (ae_mono Measure.restrict_le_self)

/--
theorem `ae_restrict_of_ae_restrict_of_subset` / 定理 `ae_restrict_of_ae_restrict_of_subset`

English:
theorem ae_restrict_of_ae_restrict_of_subset
  statement: {s t : Set α} {p : α -> Prop} (hst : s subseteq t)
  proof: h.filter_mono (ae_mono <| Measure.restrict_mono hst (le_refl μ))

中文:
定理 ae_restrict_of_ae_restrict_of_subset
  结论: {s t : 集合 α} {p : α -> 命题} (hst : s subseteq t)
  证明: h.filter_mono (ae_mono <| Measure.restrict_mono hst (le_refl μ))

Depends on / 依赖: Measure, Measure.restrict_mono, ae_mono, filter_mono, h.filter_mono, le_refl, restrict_mono
-/
theorem ae_restrict_of_ae_restrict_of_subset {s t : Set α} {p : α -> Prop} (hst : s subseteq t)
    (h : forallᵐ x ∂μ.restrict t, p x) : forallᵐ x ∂μ.restrict s, p x :=
  h.filter_mono (ae_mono <| Measure.restrict_mono hst (le_refl μ))

/--
theorem `ae_of_ae_restrict_of_ae_restrict_compl` / 定理 `ae_of_ae_restrict_of_ae_restrict_compl`

English:
theorem ae_of_ae_restrict_of_ae_restrict_compl
  statement: (t : Set α) {p : α -> Prop}
  proof: nonpos_iff_eq_zero.1
    calc
      μ { x | ¬p x } <= μ ({ x | ¬p x } inter t) + μ ({ x | ¬p x } inter tᶜ) :=
        measure_le_inter_add_sdiff _ _ _
      _ <= μ.restrict t { x | ¬p x } + μ.restrict tᶜ { x | ¬p x } :=
        add_le_add (le_restrict_apply _ _) (le_restrict_apply _ _)
      _ = 0 :

中文:
定理 ae_of_ae_restrict_of_ae_restrict_compl
  结论: (t : 集合 α) {p : α -> 命题}
  证明: nonpos_iff_eq_zero.1
    calc
      μ { x | ¬p x } <= μ ({ x | ¬p x } inter t) + μ ({ x | ¬p x } inter tᶜ) :=
        measure_le_inter_add_sdiff _ _ _
      _ <= μ.restrict t { x | ¬p x } + μ.restrict tᶜ { x | ¬p x } :=
        add_le_add (le_restrict_apply _ _) (le_restrict_apply _ _)
      _ = 0 :

Depends on / 依赖: add_le_add, ae_iff, le_restrict_apply, measure_le_inter_add_sdiff, nonpos_iff_eq_zero, restrict, zero_add
-/
theorem ae_of_ae_restrict_of_ae_restrict_compl (t : Set α) {p : α -> Prop}
    (ht : forallᵐ x ∂μ.restrict t, p x) (htc : forallᵐ x ∂μ.restrict tᶜ, p x) : forallᵐ x ∂μ, p x :=
nonpos_iff_eq_zero.1
    calc
      μ { x | ¬p x } <= μ ({ x | ¬p x } inter t) + μ ({ x | ¬p x } inter tᶜ) :=
        measure_le_inter_add_sdiff _ _ _
      _ <= μ.restrict t { x | ¬p x } + μ.restrict tᶜ { x | ¬p x } :=
        add_le_add (le_restrict_apply _ _) (le_restrict_apply _ _)
      _ = 0 := by rw [ae_iff.1 ht, ae_iff.1 htc, zero_add]

/--
theorem `mem_map_restrict_ae_iff` / 定理 `mem_map_restrict_ae_iff`

English:
theorem mem_map_restrict_ae_iff
  given: {β} {s : Set α} {t : Set β} {f : α -> β} (hs : MeasurableSet s)
  proof: by
  rw [mem_map]; rw [mem_ae_iff]; rw [Measure.restrict_apply' hs]

中文:
定理 mem_map_restrict_ae_iff
  条件: {β} {s : 集合 α} {t : 集合 β} {f : α -> β} (hs : 可测集 s)
  证明: by
  rw [mem_map]; rw [mem_ae_iff]; rw [Measure.restrict_apply' hs]

Depends on / 依赖: Measure, Measure.restrict_apply, mem_ae_iff, mem_map, restrict_apply
-/
theorem mem_map_restrict_ae_iff {β} {s : Set α} {t : Set β} {f : α -> β} (hs : MeasurableSet s) :
    t in Filter.map f (ae (μ.restrict s)) ↔ μ ((f ⁻¹' t)ᶜ inter s) = 0 := by
  rw [mem_map]; rw [mem_ae_iff]; rw [Measure.restrict_apply' hs]

/--
theorem `ae_add_measure_iff` / 定理 `ae_add_measure_iff`

English:
theorem ae_add_measure_iff
  given: {p : α -> Prop} {ν}
  proof: add_eq_zero

中文:
定理 ae_add_measure_iff
  条件: {p : α -> 命题} {ν}
  证明: add_eq_zero

Depends on / 依赖: X.str
-/
@[simp] theorem ae_add_measure_iff {p : α -> Prop} {ν} :
    (forallᵐ x ∂μ + ν, p x) ↔ (forallᵐ x ∂μ, p x) ∧ forallᵐ x ∂ν, p x :=
  add_eq_zero

/--
lemma `ae_finsetSum_measure_iff` / 引理 `ae_finsetSum_measure_iff`

English:
lemma ae_finsetSum_measure_iff
  given: {p : α -> Prop} {s : Finset ι} {μ : ι -> Measure α}
  proof: by
  induction s using Finset.cons_induction <;> simp [*]

中文:
引理 ae_finsetSum_measure_iff
  条件: {p : α -> 命题} {s : 有限集 ι} {μ : ι -> 测度 α}
  证明: by
  induction s using Finset.cons_induction <;> simp [*]

Depends on / 依赖: X.isBoundedOrder, isBoundedOrder
-/
@[simp] lemma ae_finsetSum_measure_iff {p : α -> Prop} {s : Finset ι} {μ : ι -> Measure α} :
    (forallᵐ x ∂∑ i in s, μ i, p x) ↔ forall i in s, forallᵐ x ∂μ i, p x := by
  induction s using Finset.cons_induction <;> simp [*]

/--
theorem `ae_eq_comp'` / 定理 `ae_eq_comp'`

English:
theorem ae_eq_comp'
  statement: {ν : Measure β} {f : α -> β} {g g' : β -> δ} (hf : AEMeasurable f μ)
  proof: (tendsto_ae_map hf).mono_right h2.ae_le h

中文:
定理 ae_eq_comp'
  结论: {ν : 测度 β} {f : α -> β} {g g' : β -> δ} (hf : 几乎处处可测 f μ)
  证明: (tendsto_ae_map hf).mono_right h2.ae_le h

Depends on / 依赖: ae_le, h2.ae_le, mono_right, tendsto_ae_map
-/
theorem ae_eq_comp' {ν : Measure β} {f : α -> β} {g g' : β -> δ} (hf : AEMeasurable f μ)
    (h : g =ᵐ[ν] g') (h2 : μ.map f ≪ ν) : g ∘ f =ᵐ[μ] g' ∘ f :=
  (tendsto_ae_map hf).mono_right h2.ae_le h

/--
theorem `Measure.QuasiMeasurePreserving.ae_eq_comp` / 定理 `Measure.QuasiMeasurePreserving.ae_eq_comp`

English:
theorem Measure.QuasiMeasurePreserving.ae_eq_comp
  statement: {ν : Measure β} {f : α -> β} {g g' : β -> δ}
  proof: ae_eq_comp' hf.aemeasurable h hf.absolutelyContinuous

中文:
定理 测度.拟保测.ae_eq_comp
  结论: {ν : 测度 β} {f : α -> β} {g g' : β -> δ}
  证明: ae_eq_comp' hf.aemeasurable h hf.absolutelyContinuous

Depends on / 依赖: absolutelyContinuous, ae_eq_comp, aemeasurable, hf.absolutelyContinuous, hf.aemeasurable
-/
theorem Measure.QuasiMeasurePreserving.ae_eq_comp {ν : Measure β} {f : α -> β} {g g' : β -> δ}
    (hf : QuasiMeasurePreserving f μ ν) (h : g =ᵐ[ν] g') : g ∘ f =ᵐ[μ] g' ∘ f :=
  ae_eq_comp' hf.aemeasurable h hf.absolutelyContinuous

/--
theorem `ae_eq_comp` / 定理 `ae_eq_comp`

English:
theorem ae_eq_comp
  given: {f : α -> β} {g g' : β -> δ} (hf : AEMeasurable f μ) (h : g =ᵐ[μ.map f] g')
  proof: ae_eq_comp' hf h AbsolutelyContinuous.rfl

@[to_additive]

中文:
定理 ae_eq_comp
  条件: {f : α -> β} {g g' : β -> δ} (hf : 几乎处处可测 f μ) (h : g =ᵐ[μ.map f] g')
  证明: ae_eq_comp' hf h AbsolutelyContinuous.rfl

@[to_additive]

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.rfl, ae_eq_comp
-/
theorem ae_eq_comp {f : α -> β} {g g' : β -> δ} (hf : AEMeasurable f μ) (h : g =ᵐ[μ.map f] g') :
    g ∘ f =ᵐ[μ] g' ∘ f :=
  ae_eq_comp' hf h AbsolutelyContinuous.rfl

@[to_additive]
/--
theorem `div_ae_eq_one` / 定理 `div_ae_eq_one`

English:
theorem div_ae_eq_one
  given: {β} [Group β] (f g : α -> β)
  statement: f / g =ᵐ[μ] 1 ↔ f =ᵐ[μ] g
  proof: by
  refine ⟨fun h => h.mono fun x hx => ?_, fun h => h.mono fun x hx => ?_⟩
  · rwa [Pi.div_apply, Pi.one_apply, div_eq_one] at hx
  · rwa [Pi.div_apply, Pi.one_apply, div_eq_one]

@[to_additive sub_nonneg_ae]

中文:
定理 div_ae_eq_one
  条件: {β} [群 β] (f g : α -> β)
  结论: f / g =ᵐ[μ] 1 ↔ f =ᵐ[μ] g
  证明: by
  refine ⟨fun h => h.mono fun x hx => ?_, fun h => h.mono fun x hx => ?_⟩
  · rwa [Pi.div_apply, Pi.one_apply, div_eq_one] at hx
  · rwa [Pi.div_apply, Pi.one_apply, div_eq_one]

@[to_additive sub_nonneg_ae]

Depends on / 依赖: Pi.div_apply, Pi.one_apply, div_apply, div_eq_one, h.mono, one_apply
-/
theorem div_ae_eq_one {β} [Group β] (f g : α -> β) : f / g =ᵐ[μ] 1 ↔ f =ᵐ[μ] g := by
  refine ⟨fun h => h.mono fun x hx => ?_, fun h => h.mono fun x hx => ?_⟩
  · rwa [Pi.div_apply, Pi.one_apply, div_eq_one] at hx
  · rwa [Pi.div_apply, Pi.one_apply, div_eq_one]

@[to_additive sub_nonneg_ae]
/--
lemma `one_le_div_ae` / 引理 `one_le_div_ae`

English:
lemma one_le_div_ae
  given: {β : Type*} [Group β] [LE β] [MulRightMono β] (f g : α -> β)
  proof: by
  refine ⟨fun h => h.mono fun a ha => ?_, fun h => h.mono fun a ha => ?_⟩
  · rwa [Pi.one_apply, Pi.div_apply, one_le_div'] at ha
  · rwa [Pi.one_apply, Pi.div_apply, one_le_div']

中文:
引理 one_le_div_ae
  条件: {β : 类型} [群 β] [LE β] [MulRightMono β] (f g : α -> β)
  证明: by
  refine ⟨fun h => h.mono fun a ha => ?_, fun h => h.mono fun a ha => ?_⟩
  · rwa [Pi.one_apply, Pi.div_apply, one_le_div'] at ha
  · rwa [Pi.one_apply, Pi.div_apply, one_le_div']

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, FinBddDistLat, Pi.div_apply, Pi.one_apply, div_apply, h.mono, one_apply, one_le_div
-/
lemma one_le_div_ae {β : Type*} [Group β] [LE β] [MulRightMono β] (f g : α -> β) :
    1 <=ᵐ[μ] g / f ↔ f <=ᵐ[μ] g := by
  refine ⟨fun h => h.mono fun a ha => ?_, fun h => h.mono fun a ha => ?_⟩
  · rwa [Pi.one_apply, Pi.div_apply, one_le_div'] at ha
  · rwa [Pi.one_apply, Pi.div_apply, one_le_div']

/--
theorem `le_ae_restrict` / 定理 `le_ae_restrict`

English:
theorem le_ae_restrict
  statement: ae μ ⊓ 𝓟 s <= ae (μ.restrict s)
  proof: fun _s hs =>
  eventually_inf_principal.2 (ae_imp_of_ae_restrict hs)

@[simp]

中文:
定理 le_ae_restrict
  结论: ae μ ⊓ 𝓟 s <= ae (μ.restrict s)
  证明: fun _s hs =>
  eventually_inf_principal.2 (ae_imp_of_ae_restrict hs)

@[simp]
-/
theorem le_ae_restrict : ae μ ⊓ 𝓟 s <= ae (μ.restrict s) := fun _s hs =>
  eventually_inf_principal.2 (ae_imp_of_ae_restrict hs)

@[simp]
/--
theorem `ae_restrict_eq` / 定理 `ae_restrict_eq`

English:
theorem ae_restrict_eq
  given: (hs : MeasurableSet s)
  statement: ae (μ.restrict s) = ae μ ⊓ 𝓟 s
  proof: by
  ext t
  simp only [mem_inf_principal, mem_ae_iff, restrict_apply_eq_zero' hs, compl_ofPred,
    Classical.not_imp, fun a => and_comm (a := a in s) (b := a ∉ t)]
  rfl

中文:
定理 ae_restrict_eq
  条件: (hs : 可测集 s)
  结论: ae (μ.restrict s) = ae μ ⊓ 𝓟 s
  证明: by
  ext t
  simp only [mem_inf_principal, mem_ae_iff, restrict_apply_eq_zero' hs, compl_ofPred,
    Classical.not_imp, fun a => and_comm (a := a in s) (b := a ∉ t)]
  rfl

Depends on / 依赖: Classical, Classical.not_imp, and_comm, compl_ofPred, f.hom, mem_ae_iff, mem_inf_principal, not_imp, restrict_apply_eq_zero
-/
theorem ae_restrict_eq (hs : MeasurableSet s) : ae (μ.restrict s) = ae μ ⊓ 𝓟 s := by
  ext t
  simp only [mem_inf_principal, mem_ae_iff, restrict_apply_eq_zero' hs, compl_ofPred,
    Classical.not_imp, fun a => and_comm (a := a in s) (b := a ∉ t)]
  rfl

/--
lemma `ae_restrict_le` / 引理 `ae_restrict_le`

English:
lemma ae_restrict_le
  statement: ae (μ.restrict s) <= ae μ
  proof: ae_mono restrict_le_self

中文:
引理 ae_restrict_le
  结论: ae (μ.restrict s) <= ae μ
  证明: ae_mono restrict_le_self

Depends on / 依赖: ae_mono, restrict_le_self
-/
lemma ae_restrict_le : ae (μ.restrict s) <= ae μ :=
  ae_mono restrict_le_self

/--
theorem `ae_restrict_eq_bot` / 定理 `ae_restrict_eq_bot`

English:
theorem ae_restrict_eq_bot
  given: {s}
  statement: ae (μ.restrict s) = ⊥ ↔ μ s = 0
  proof: ae_eq_bot.trans restrict_eq_zero

中文:
定理 ae_restrict_eq_bot
  条件: {s}
  结论: ae (μ.restrict s) = ⊥ ↔ μ s = 0
  证明: ae_eq_bot.trans restrict_eq_zero

Depends on / 依赖: ae_eq_bot, ae_eq_bot.trans, restrict_eq_zero
-/
theorem ae_restrict_eq_bot {s} : ae (μ.restrict s) = ⊥ ↔ μ s = 0 :=
  ae_eq_bot.trans restrict_eq_zero

/--
theorem `ae_restrict_neBot` / 定理 `ae_restrict_neBot`

English:
theorem ae_restrict_neBot
  given: {s}
  statement: (ae <| μ.restrict s).NeBot ↔ μ s != 0
  proof: neBot_iff.trans ae_restrict_eq_bot.not

中文:
定理 ae_restrict_neBot
  条件: {s}
  结论: (ae <| μ.restrict s).NeBot ↔ μ s != 0
  证明: neBot_iff.trans ae_restrict_eq_bot.not

Depends on / 依赖: ae_restrict_eq_bot, ae_restrict_eq_bot.not, neBot_iff, neBot_iff.trans
-/
theorem ae_restrict_neBot {s} : (ae <| μ.restrict s).NeBot ↔ μ s != 0 :=
  neBot_iff.trans ae_restrict_eq_bot.not

/--
theorem `self_mem_ae_restrict` / 定理 `self_mem_ae_restrict`

English:
theorem self_mem_ae_restrict
  given: {s} (hs : MeasurableSet s)
  statement: s in ae (μ.restrict s)
  proof: by
  simp only [ae_restrict_eq hs, mem_principal, mem_inf_iff]
  exact ⟨_, univ_mem, s, Subset.rfl, (univ_inter s).symm⟩

中文:
定理 self_mem_ae_restrict
  条件: {s} (hs : 可测集 s)
  结论: s in ae (μ.restrict s)
  证明: by
  simp only [ae_restrict_eq hs, mem_principal, mem_inf_iff]
  exact ⟨_, univ_mem, s, Subset.rfl, (univ_inter s).symm⟩

Depends on / 依赖: Subset, Subset.rfl, ae_restrict_eq, mem_inf_iff, mem_principal, univ_inter, univ_mem
-/
theorem self_mem_ae_restrict {s} (hs : MeasurableSet s) : s in ae (μ.restrict s) := by
  simp only [ae_restrict_eq hs, mem_principal, mem_inf_iff]
  exact ⟨_, univ_mem, s, Subset.rfl, (univ_inter s).symm⟩

/--
theorem `ae_restrict_of_ae_eq_of_ae_restrict` / 定理 `ae_restrict_of_ae_eq_of_ae_restrict`

English:
theorem ae_restrict_of_ae_eq_of_ae_restrict
  given: {s t} (hst : s =ᵐ[μ] t) {p : α -> Prop}
  proof: by simp [Measure.restrict_congr_set hst]

中文:
定理 ae_restrict_of_ae_eq_of_ae_restrict
  条件: {s t} (hst : s =ᵐ[μ] t) {p : α -> 命题}
  证明: by simp [Measure.restrict_congr_set hst]

Depends on / 依赖: Measure, Measure.restrict_congr_set, restrict_congr_set
-/
theorem ae_restrict_of_ae_eq_of_ae_restrict {s t} (hst : s =ᵐ[μ] t) {p : α -> Prop} :
    (forallᵐ x ∂μ.restrict s, p x) -> forallᵐ x ∂μ.restrict t, p x := by simp [Measure.restrict_congr_set hst]

/--
theorem `ae_restrict_congr_set` / 定理 `ae_restrict_congr_set`

English:
theorem ae_restrict_congr_set
  given: {s t} (hst : s =ᵐ[μ] t) {p : α -> Prop}
  proof: ⟨ae_restrict_of_ae_eq_of_ae_restrict hst, ae_restrict_of_ae_eq_of_ae_restrict hst.symm⟩

中文:
定理 ae_restrict_congr_set
  条件: {s t} (hst : s =ᵐ[μ] t) {p : α -> 命题}
  证明: ⟨ae_restrict_of_ae_eq_of_ae_restrict hst, ae_restrict_of_ae_eq_of_ae_restrict hst.symm⟩

Depends on / 依赖: ae_restrict_of_ae_eq_of_ae_restrict, hst.symm
-/
theorem ae_restrict_congr_set {s t} (hst : s =ᵐ[μ] t) {p : α -> Prop} :
    (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ.restrict t, p x :=
  ⟨ae_restrict_of_ae_eq_of_ae_restrict hst, ae_restrict_of_ae_eq_of_ae_restrict hst.symm⟩

/--
lemma `NullMeasurable.measure_preimage_eq_measure_restrict_preimage_of_ae_compl_eq_const` / 引理 `NullMeasurable.measure_preimage_eq_measure_restrict_preimage_of_ae_compl_eq_const`

English:
lemma NullMeasurable.measure_preimage_eq_measure_restrict_preimage_of_ae_compl_eq_const
  proof: by
  rw [Measure.restrict_apply₀ (f_mble t_mble)]
  rw [EventuallyEq]; rw [ae_iff]; rw [Measure.restrict_apply₀] at hs
  · apply le_antisymm _ (measure_mono inter_subset_left)
    apply (measure_mono (Eq.symm (inter_union_compl (f ⁻¹' t) s)).le).trans
    apply (measure_union_le _ _).trans
    suffi

中文:
引理 NullMeasurable.measure_preimage_eq_measure_restrict_preimage_of_ae_compl_eq_const
  证明: by
  rw [Measure.restrict_apply₀ (f_mble t_mble)]
  rw [EventuallyEq]; rw [ae_iff]; rw [Measure.restrict_apply₀] at hs
  · apply le_antisymm _ (measure_mono inter_subset_left)
    apply (measure_mono (Eq.symm (inter_union_compl (f ⁻¹' t) s)).le).trans
    apply (measure_union_le _ _).trans
    suffi

Depends on / 依赖: Eq.symm, EventuallyEq, Measure, Measure.restrict_apply, NullMeasurableSet, NullMeasurableSet.of_null, ae_iff, f_mble, inter_subset_left, inter_union_compl, le_antisymm, measure_mono, measure_union_le, nonpos_iff_eq_zero, of_null, t_mble
-/
lemma NullMeasurable.measure_preimage_eq_measure_restrict_preimage_of_ae_compl_eq_const
    {β : Type*} [MeasurableSpace β] {b : β} {f : α -> β} {s : Set α}
    (f_mble : NullMeasurable f (μ.restrict s)) (hs : f =ᵐ[Measure.restrict μ sᶜ] (fun _ => b))
    {t : Set β} (t_mble : MeasurableSet t) (ht : b ∉ t) :
    μ (f ⁻¹' t) = μ.restrict s (f ⁻¹' t) := by
  rw [Measure.restrict_apply₀ (f_mble t_mble)]
  rw [EventuallyEq]; rw [ae_iff]; rw [Measure.restrict_apply₀] at hs
  · apply le_antisymm _ (measure_mono inter_subset_left)
    apply (measure_mono (Eq.symm (inter_union_compl (f ⁻¹' t) s)).le).trans
    apply (measure_union_le _ _).trans
    suffices μ ((f ⁻¹' t) inter sᶜ) = 0 by simp [this]
    rw [← nonpos_iff_eq_zero]; rw [← hs]
    gcongr
    exact fun x hx hfx => ht (hfx ▸ hx)
  · exact NullMeasurableSet.of_null hs

/--
lemma `nullMeasurableSet_restrict` / 引理 `nullMeasurableSet_restrict`

English:
lemma nullMeasurableSet_restrict
  given: (hs : NullMeasurableSet s μ) {t : Set α}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨t', -, ht', t't⟩ : exists t' ⊇ t, MeasurableSet t' ∧ t' =ᵐ[μ.restrict s] t :=
      h.exists_measurable_superset_ae_eq
    have A : (t' inter s : Set α) =ᵐ[μ] (t inter s : Set α) := by
      have : forallᵐ x ∂μ, x in s -> (x in t') = (x in t) :=
   

中文:
引理 nullMeasurableSet_restrict
  条件: (hs : NullMeasurableSet s μ) {t : 集合 α}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨t', -, ht', t't⟩ : exists t' ⊇ t, MeasurableSet t' ∧ t' =ᵐ[μ.restrict s] t :=
      h.exists_measurable_superset_ae_eq
    have A : (t' inter s : Set α) =ᵐ[μ] (t inter s : Set α) := by
      have : forallᵐ x ∂μ, x in s -> (x in t') = (x in t) :=
   

Depends on / 依赖: Measurab, MeasurableSet, ae_restrict_iff, and_congr_left_iff, eq_iff_iff, exists_measurable_superset_ae_eq, filter_upwards, h.exists_measurable_superset_ae_eq, mem_inter_iff, restrict
-/
lemma nullMeasurableSet_restrict (hs : NullMeasurableSet s μ) {t : Set α} :
    NullMeasurableSet t (μ.restrict s) ↔ NullMeasurableSet (t inter s) μ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨t', -, ht', t't⟩ : exists t' ⊇ t, MeasurableSet t' ∧ t' =ᵐ[μ.restrict s] t :=
      h.exists_measurable_superset_ae_eq
    have A : (t' inter s : Set α) =ᵐ[μ] (t inter s : Set α) := by
      have : forallᵐ x ∂μ, x in s -> (x in t') = (x in t) :=
        (ae_restrict_iff'₀ hs).1 t't
      filter_upwards [this] with y hy
      change (y in t' inter s) = (y in t inter s)
      simpa only [eq_iff_iff, mem_inter_iff, and_congr_left_iff] using hy
    obtain ⟨s', -, hs', s's⟩ : exists s' ⊇ s, MeasurableSet s' ∧ s' =ᵐ[μ] s :=
      hs.exists_measurable_superset_ae_eq
    have B : (t' inter s' : Set α) =ᵐ[μ] (t' inter s : Set α) :=
      ae_eq_set_inter (EventuallyEq.refl _ _) s's
    exact (ht'.inter hs').nullMeasurableSet.congr (B.trans A)
  · have A : NullMeasurableSet (t \ s) (μ.restrict s) := by
      apply NullMeasurableSet.of_null
      rw [Measure.restrict_apply₀' hs]
      simp
    have B : NullMeasurableSet (t inter s) (μ.restrict s) :=
      h.mono_ac absolutelyContinuous_restrict
    simpa using A.union B

/--
lemma `nullMeasurableSet_restrict_of_subset` / 引理 `nullMeasurableSet_restrict_of_subset`

English:
lemma nullMeasurableSet_restrict_of_subset
  given: {t : Set α} (ht : t subseteq s)
  proof: by
  refine ⟨fun h => ?_, fun h => h.mono_ac absolutelyContinuous_restrict⟩
  obtain ⟨t', t'_subs, ht', t't⟩ : exists t' subseteq t, MeasurableSet t' ∧ t' =ᵐ[μ.restrict s] t :=
    h.exists_measurable_subset_ae_eq
  have : forallᵐ x ∂μ, x in s -> (x in t' ↔ x in t) := by
    apply ae_imp_of_ae_restr

中文:
引理 nullMeasurableSet_restrict_of_subset
  条件: {t : 集合 α} (ht : t subseteq s)
  证明: by
  refine ⟨fun h => ?_, fun h => h.mono_ac absolutelyContinuous_restrict⟩
  obtain ⟨t', t'_subs, ht', t't⟩ : exists t' subseteq t, MeasurableSet t' ∧ t' =ᵐ[μ.restrict s] t :=
    h.exists_measurable_subset_ae_eq
  have : forallᵐ x ∂μ, x in s -> (x in t' ↔ x in t) := by
    apply ae_imp_of_ae_restr

Depends on / 依赖: MeasurableSet, _subs, absolutelyContinuous_restrict, ae_imp_of_ae_restrict, eq_iff_iff, exists_measurable_subset_ae_eq, filter_upwards, h.exists_measurable_subset_ae_eq, h.mono_ac, mono_ac, nullMeasurableSet, nullMeasurableSet.congr, restrict, subseteq
-/
lemma nullMeasurableSet_restrict_of_subset {t : Set α} (ht : t subseteq s) :
    NullMeasurableSet t (μ.restrict s) ↔ NullMeasurableSet t μ := by
  refine ⟨fun h => ?_, fun h => h.mono_ac absolutelyContinuous_restrict⟩
  obtain ⟨t', t'_subs, ht', t't⟩ : exists t' subseteq t, MeasurableSet t' ∧ t' =ᵐ[μ.restrict s] t :=
    h.exists_measurable_subset_ae_eq
  have : forallᵐ x ∂μ, x in s -> (x in t' ↔ x in t) := by
    apply ae_imp_of_ae_restrict
    filter_upwards [t't] with x hx using by simpa using! hx
  have : t' =ᵐ[μ] t := by
    filter_upwards [this] with x hx
    change (x in t') = (x in t)
    simp only [eq_iff_iff]
    tauto
  exact ht'.nullMeasurableSet.congr this

namespace Measure

section Subtype

/-! ### Subtype of a measure space -/

section ComapAnyMeasure

/--
theorem `MeasurableSet.nullMeasurableSet_subtype_coe` / 定理 `MeasurableSet.nullMeasurableSet_subtype_coe`

English:
theorem MeasurableSet.nullMeasurableSet_subtype_coe
  statement: {t : Set s} (hs : NullMeasurableSet s μ)
  proof: by
  rw [Subtype.instMeasurableSpace]; rw [comap_eq_generateFrom] at ht
  induction t, ht using generateFrom_induction with
  | hC t' ht' =>
    obtain ⟨s', hs', rfl⟩ := ht'
    rw [Subtype.image_preimage_coe]
    exact hs.inter (hs'.nullMeasurableSet)
  | empty => simp only [image_empty, nullMeasur

中文:
定理 可测集.nullMeasurableSet_subtype_coe
  结论: {t : 集合 s} (hs : NullMeasurableSet s μ)
  证明: by
  rw [Subtype.instMeasurableSpace]; rw [comap_eq_generateFrom] at ht
  induction t, ht using generateFrom_induction with
  | hC t' ht' =>
    obtain ⟨s', hs', rfl⟩ := ht'
    rw [Subtype.image_preimage_coe]
    exact hs.inter (hs'.nullMeasurableSet)
  | empty => simp only [image_empty, nullMeasur

Depends on / 依赖: Subtype, Subtype.coe_injective, Subtype.image_preimage_coe, Subtype.instMeasurableSpace, Subtype.range_coe_subtype, coe_injective, comap_eq_generateFrom, generateFrom_induction, hs.diff, hs.inter, iUnion, image_empty, image_iUnion, image_preimage_coe, instMeasurableSpace, nullMeasurableSet, nullMeasurableSet_empty, ofPred_mem_eq, range_coe_subtype, range_sdiff_image
-/
theorem MeasurableSet.nullMeasurableSet_subtype_coe {t : Set s} (hs : NullMeasurableSet s μ)
    (ht : MeasurableSet t) : NullMeasurableSet ((↑) '' t) μ := by
  rw [Subtype.instMeasurableSpace]; rw [comap_eq_generateFrom] at ht
  induction t, ht using generateFrom_induction with
  | hC t' ht' =>
    obtain ⟨s', hs', rfl⟩ := ht'
    rw [Subtype.image_preimage_coe]
    exact hs.inter (hs'.nullMeasurableSet)
  | empty => simp only [image_empty, nullMeasurableSet_empty]
  | compl t' _ ht' =>
    simp only [← range_sdiff_image Subtype.coe_injective, Subtype.range_coe_subtype, ofPred_mem_eq]
    exact hs.diff ht'
  | iUnion f _ hf =>
    rw [image_iUnion]
    exact .iUnion hf

/--
theorem `NullMeasurableSet.subtype_coe` / 定理 `NullMeasurableSet.subtype_coe`

English:
theorem NullMeasurableSet.subtype_coe
  statement: {t : Set s} (hs : NullMeasurableSet s μ)
  proof: NullMeasurableSet.image _ μ Subtype.coe_injective
    (fun _ => MeasurableSet.nullMeasurableSet_subtype_coe hs) ht

中文:
定理 NullMeasurableSet.subtype_coe
  结论: {t : 集合 s} (hs : NullMeasurableSet s μ)
  证明: NullMeasurableSet.image _ μ Subtype.coe_injective
    (fun _ => MeasurableSet.nullMeasurableSet_subtype_coe hs) ht

Depends on / 依赖: MeasurableSet, MeasurableSet.nullMeasurableSet_subtype_coe, NullMeasurableSet, NullMeasurableSet.image, Subtype, Subtype.coe_injective, coe_injective, nullMeasurableSet_subtype_coe
-/
theorem NullMeasurableSet.subtype_coe {t : Set s} (hs : NullMeasurableSet s μ)
    (ht : NullMeasurableSet t (μ.comap Subtype.val)) : NullMeasurableSet (((↑) : s -> α) '' t) μ :=
  NullMeasurableSet.image _ μ Subtype.coe_injective
    (fun _ => MeasurableSet.nullMeasurableSet_subtype_coe hs) ht

/--
theorem `measure_subtype_coe_le_comap` / 定理 `measure_subtype_coe_le_comap`

English:
theorem measure_subtype_coe_le_comap
  given: (hs : NullMeasurableSet s μ) (t : Set s)
  proof: le_comap_apply _ _ Subtype.coe_injective (fun _ =>
    MeasurableSet.nullMeasurableSet_subtype_coe hs) _

中文:
定理 measure_subtype_coe_le_comap
  条件: (hs : NullMeasurableSet s μ) (t : 集合 s)
  证明: le_comap_apply _ _ Subtype.coe_injective (fun _ =>
    MeasurableSet.nullMeasurableSet_subtype_coe hs) _

Depends on / 依赖: MeasurableSet, MeasurableSet.nullMeasurableSet_subtype_coe, Subtype, Subtype.coe_injective, coe_injective, le_comap_apply, nullMeasurableSet_subtype_coe
-/
theorem measure_subtype_coe_le_comap (hs : NullMeasurableSet s μ) (t : Set s) :
    μ (((↑) : s -> α) '' t) <= μ.comap Subtype.val t :=
  le_comap_apply _ _ Subtype.coe_injective (fun _ =>
    MeasurableSet.nullMeasurableSet_subtype_coe hs) _

/--
theorem `measure_subtype_coe_eq_zero_of_comap_eq_zero` / 定理 `measure_subtype_coe_eq_zero_of_comap_eq_zero`

English:
theorem measure_subtype_coe_eq_zero_of_comap_eq_zero
  statement: (hs : NullMeasurableSet s μ) {t : Set s}
  proof: eq_bot_iff.mpr (measure_subtype_coe_le_comap hs t).trans ht.le

中文:
定理 measure_subtype_coe_eq_zero_of_comap_eq_zero
  结论: (hs : NullMeasurableSet s μ) {t : 集合 s}
  证明: eq_bot_iff.mpr (measure_subtype_coe_le_comap hs t).trans ht.le

Depends on / 依赖: eq_bot_iff, eq_bot_iff.mpr, ht.le, measure_subtype_coe_le_comap
-/
theorem measure_subtype_coe_eq_zero_of_comap_eq_zero (hs : NullMeasurableSet s μ) {t : Set s}
    (ht : μ.comap Subtype.val t = 0) : μ (((↑) : s -> α) '' t) = 0 :=
eq_bot_iff.mpr (measure_subtype_coe_le_comap hs t).trans ht.le

end ComapAnyMeasure

section MeasureSpace

variable {u : Set δ} [MeasureSpace δ] {p : δ -> Prop}

/-- In a measure space, one can restrict the measure to a subtype to get a new measure space.
Not registered as an instance, as there are other natural choices such as the normalized restriction
for a probability measure, or the subspace measure when restricting to a vector subspace. Enable
locally if needed with `attribute [local instance] Measure.Subtype.measureSpace`. -/
@[instance_reducible]
/--
Definition of `Subtype.measureSpace` / `Subtype.measureSpace` 的定义

English:
definition Subtype.measureSpace
  signature: : MeasureSpace (Subtype p) where
  body: Measure.comap Subtype.val volume

中文:
定义 子类型.measureSpace
  签名: : 测度空间 (子类型 p) where
  定义体: Measure.comap Subtype.val volume

Depends on / 依赖: Measure, Measure.comap, Subtype, Subtype.val, volume
-/
noncomputable def Subtype.measureSpace : MeasureSpace (Subtype p) where
  volume := Measure.comap Subtype.val volume

attribute [local instance] Subtype.measureSpace

/--
theorem `Subtype.volume_def` / 定理 `Subtype.volume_def`

English:
theorem Subtype.volume_def
  statement: (volume : Measure u) = volume.comap Subtype.val
  proof: rfl

中文:
定理 子类型.volume_def
  结论: (volume : 测度 u) = volume.comap 子类型.val
  证明: rfl
-/
theorem Subtype.volume_def : (volume : Measure u) = volume.comap Subtype.val :=
  rfl

/--
theorem `Subtype.volume_univ` / 定理 `Subtype.volume_univ`

English:
theorem Subtype.volume_univ
  given: (hu : NullMeasurableSet u)
  statement: volume (univ : Set u) = volume u
  proof: by
  rw [Subtype.volume_def]; rw [comap_apply₀ _ _ _ _ MeasurableSet.univ.nullMeasurableSet]
  · simp only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq]
  · exact Subtype.coe_injective
  · exact fun t => MeasurableSet.nullMeasurableSet_subtype_coe hu

中文:
定理 子类型.volume_univ
  条件: (hu : NullMeasurableSet u)
  结论: volume (univ : 集合 u) = volume u
  证明: by
  rw [Subtype.volume_def]; rw [comap_apply₀ _ _ _ _ MeasurableSet.univ.nullMeasurableSet]
  · simp only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq]
  · exact Subtype.coe_injective
  · exact fun t => MeasurableSet.nullMeasurableSet_subtype_coe hu

Depends on / 依赖: MeasurableSet, MeasurableSet.nullMeasurableSet_subtype_coe, MeasurableSet.univ.nullMeasurableSet, Subtype, Subtype.coe_injective, Subtype.range_coe_subtype, Subtype.volume_def, coe_injective, image_univ, nullMeasurableSet, nullMeasurableSet_subtype_coe, ofPred_mem_eq, range_coe_subtype, volume_def
-/
theorem Subtype.volume_univ (hu : NullMeasurableSet u) : volume (univ : Set u) = volume u := by
  rw [Subtype.volume_def]; rw [comap_apply₀ _ _ _ _ MeasurableSet.univ.nullMeasurableSet]
  · simp only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq]
  · exact Subtype.coe_injective
  · exact fun t => MeasurableSet.nullMeasurableSet_subtype_coe hu

/--
theorem `volume_subtype_coe_le_volume` / 定理 `volume_subtype_coe_le_volume`

English:
theorem volume_subtype_coe_le_volume
  given: (hu : NullMeasurableSet u) (t : Set u)
  proof: measure_subtype_coe_le_comap hu t

中文:
定理 volume_subtype_coe_le_volume
  条件: (hu : NullMeasurableSet u) (t : 集合 u)
  证明: measure_subtype_coe_le_comap hu t

Depends on / 依赖: measure_subtype_coe_le_comap
-/
theorem volume_subtype_coe_le_volume (hu : NullMeasurableSet u) (t : Set u) :
    volume (((↑) : u -> δ) '' t) <= volume t :=
  measure_subtype_coe_le_comap hu t

/--
theorem `volume_subtype_coe_eq_zero_of_volume_eq_zero` / 定理 `volume_subtype_coe_eq_zero_of_volume_eq_zero`

English:
theorem volume_subtype_coe_eq_zero_of_volume_eq_zero
  statement: (hu : NullMeasurableSet u) {t : Set u}
  proof: measure_subtype_coe_eq_zero_of_comap_eq_zero hu ht

中文:
定理 volume_subtype_coe_eq_zero_of_volume_eq_zero
  结论: (hu : NullMeasurableSet u) {t : 集合 u}
  证明: measure_subtype_coe_eq_zero_of_comap_eq_zero hu ht

Depends on / 依赖: measure_subtype_coe_eq_zero_of_comap_eq_zero
-/
theorem volume_subtype_coe_eq_zero_of_volume_eq_zero (hu : NullMeasurableSet u) {t : Set u}
    (ht : volume t = 0) : volume (((↑) : u -> δ) '' t) = 0 :=
  measure_subtype_coe_eq_zero_of_comap_eq_zero hu ht

end MeasureSpace

end Subtype

end Measure

end MeasureTheory

open MeasureTheory Measure

namespace MeasurableEmbedding

variable {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} {f : α -> β}

section
variable (hf : MeasurableEmbedding f)
include hf

/--
theorem `map_comap` / 定理 `map_comap`

English:
theorem map_comap
  given: (μ : Measure β)
  statement: (comap f μ).map f = μ.restrict (range f)
  proof: by
  ext1 t ht
  rw [hf.map_apply]; rw [comap_apply f hf.injective hf.measurableSet_image' _ (hf.measurable ht)]; rw [image_preimage_eq_inter_range]; rw [Measure.restrict_apply ht]

中文:
定理 map_comap
  条件: (μ : 测度 β)
  结论: (comap f μ).map f = μ.restrict (range f)
  证明: by
  ext1 t ht
  rw [hf.map_apply]; rw [comap_apply f hf.injective hf.measurableSet_image' _ (hf.measurable ht)]; rw [image_preimage_eq_inter_range]; rw [Measure.restrict_apply ht]

Depends on / 依赖: Measure, Measure.restrict_apply, comap_apply, hf.injective, hf.map_apply, hf.measurable, hf.measurableSet_image, image_preimage_eq_inter_range, injective, map_apply, measurable, measurableSet_image, restrict_apply
-/
theorem map_comap (μ : Measure β) : (comap f μ).map f = μ.restrict (range f) := by
  ext1 t ht
  rw [hf.map_apply]; rw [comap_apply f hf.injective hf.measurableSet_image' _ (hf.measurable ht)]; rw [image_preimage_eq_inter_range]; rw [Measure.restrict_apply ht]

/--
theorem `comap_apply` / 定理 `comap_apply`

English:
theorem comap_apply
  given: (μ : Measure β) (s : Set α)
  statement: comap f μ s = μ (f '' s)
  proof: calc
    comap f μ s = comap f μ (f ⁻¹' f '' s) := by rw [hf.injective.preimage_image]
    _ = (comap f μ).map f (f '' s) := (hf.map_apply _ _).symm
    _ = μ (f '' s) := by
      rw [hf.map_comap]; rw [restrict_apply' hf.measurableSet_range]; rw [inter_eq_self_of_subset_left (image_subset_range _ _

中文:
定理 comap_apply
  条件: (μ : 测度 β) (s : 集合 α)
  结论: comap f μ s = μ (f '' s)
  证明: calc
    comap f μ s = comap f μ (f ⁻¹' f '' s) := by rw [hf.injective.preimage_image]
    _ = (comap f μ).map f (f '' s) := (hf.map_apply _ _).symm
    _ = μ (f '' s) := by
      rw [hf.map_comap]; rw [restrict_apply' hf.measurableSet_range]; rw [inter_eq_self_of_subset_left (image_subset_range _ _

Depends on / 依赖: hf.injective.preimage_image, hf.map_apply, hf.map_comap, hf.measurableSet_range, image_subset_range, injective, inter_eq_self_of_subset_left, map_apply, map_comap, measurableSet_range, preimage_image, restrict_apply
-/
theorem comap_apply (μ : Measure β) (s : Set α) : comap f μ s = μ (f '' s) :=
  calc
    comap f μ s = comap f μ (f ⁻¹' f '' s) := by rw [hf.injective.preimage_image]
    _ = (comap f μ).map f (f '' s) := (hf.map_apply _ _).symm
    _ = μ (f '' s) := by
      rw [hf.map_comap]; rw [restrict_apply' hf.measurableSet_range]; rw [inter_eq_self_of_subset_left (image_subset_range _ _)]

/--
theorem `comap_map` / 定理 `comap_map`

English:
theorem comap_map
  given: (μ : Measure α)
  statement: (map f μ).comap f = μ
  proof: by
  ext t _
  rw [hf.comap_apply]; rw [hf.map_apply]; rw [preimage_image_eq _ hf.injective]

中文:
定理 comap_map
  条件: (μ : 测度 α)
  结论: (map f μ).comap f = μ
  证明: by
  ext t _
  rw [hf.comap_apply]; rw [hf.map_apply]; rw [preimage_image_eq _ hf.injective]

Depends on / 依赖: comap_apply, hf.comap_apply, hf.injective, hf.map_apply, injective, map_apply, preimage_image_eq
-/
theorem comap_map (μ : Measure α) : (map f μ).comap f = μ := by
  ext t _
  rw [hf.comap_apply]; rw [hf.map_apply]; rw [preimage_image_eq _ hf.injective]

/--
theorem `ae_map_iff` / 定理 `ae_map_iff`

English:
theorem ae_map_iff
  given: {p : β -> Prop} {μ : Measure α}
  statement: (forallᵐ x ∂μ.map f, p x) ↔ forallᵐ x ∂μ, p (f x)
  proof: by
  simp only [ae_iff, hf.map_apply, preimage_ofPred_eq]

中文:
定理 ae_map_iff
  条件: {p : β -> 命题} {μ : 测度 α}
  结论: (对任意ᵐ x ∂μ.map f, p x) ↔ 对任意ᵐ x ∂μ, p (f x)
  证明: by
  simp only [ae_iff, hf.map_apply, preimage_ofPred_eq]

Depends on / 依赖: ae_iff, hf.map_apply, map_apply, preimage_ofPred_eq
-/
theorem ae_map_iff {p : β -> Prop} {μ : Measure α} : (forallᵐ x ∂μ.map f, p x) ↔ forallᵐ x ∂μ, p (f x) := by
  simp only [ae_iff, hf.map_apply, preimage_ofPred_eq]

/--
theorem `restrict_map` / 定理 `restrict_map`

English:
theorem restrict_map
  given: (μ : Measure α) (s : Set β)
  proof: Measure.ext fun t ht => by simp [hf.map_apply, ht, hf.measurable ht]

中文:
定理 restrict_map
  条件: (μ : 测度 α) (s : 集合 β)
  证明: Measure.ext fun t ht => by simp [hf.map_apply, ht, hf.measurable ht]

Depends on / 依赖: Measure, Measure.ext, hf.map_apply, hf.measurable, map_apply, measurable
-/
theorem restrict_map (μ : Measure α) (s : Set β) :
    (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  Measure.ext fun t ht => by simp [hf.map_apply, ht, hf.measurable ht]

/--
theorem `comap_preimage` / 定理 `comap_preimage`

English:
theorem comap_preimage
  given: (μ : Measure β) (s : Set β)
  proof: by
  rw [← hf.map_apply]; rw [hf.map_comap]; rw [restrict_apply' hf.measurableSet_range]

中文:
定理 comap_preimage
  条件: (μ : 测度 β) (s : 集合 β)
  证明: by
  rw [← hf.map_apply]; rw [hf.map_comap]; rw [restrict_apply' hf.measurableSet_range]
-/
protected theorem comap_preimage (μ : Measure β) (s : Set β) :
    μ.comap f (f ⁻¹' s) = μ (s inter range f) := by
  rw [← hf.map_apply]; rw [hf.map_comap]; rw [restrict_apply' hf.measurableSet_range]

/--
lemma `comap_restrict` / 引理 `comap_restrict`

English:
lemma comap_restrict
  given: (μ : Measure β) (s : Set β)
  proof: by
  ext t ht
  rw [Measure.restrict_apply ht]; rw [comap_apply hf]; rw [comap_apply hf]; rw [Measure.restrict_apply (hf.measurableSet_image.2 ht)]; rw [image_inter_preimage]

中文:
引理 comap_restrict
  条件: (μ : 测度 β) (s : 集合 β)
  证明: by
  ext t ht
  rw [Measure.restrict_apply ht]; rw [comap_apply hf]; rw [comap_apply hf]; rw [Measure.restrict_apply (hf.measurableSet_image.2 ht)]; rw [image_inter_preimage]

Depends on / 依赖: Measure, Measure.restrict_apply, comap_apply, hf.measurableSet_image, image_inter_preimage, measurableSet_image, restrict_apply
-/
lemma comap_restrict (μ : Measure β) (s : Set β) :
    (μ.restrict s).comap f = (μ.comap f).restrict (f ⁻¹' s) := by
  ext t ht
  rw [Measure.restrict_apply ht]; rw [comap_apply hf]; rw [comap_apply hf]; rw [Measure.restrict_apply (hf.measurableSet_image.2 ht)]; rw [image_inter_preimage]

/--
lemma `restrict_comap` / 引理 `restrict_comap`

English:
lemma restrict_comap
  given: (μ : Measure β) (s : Set α)
  proof: by
  rw [comap_restrict hf]; rw [preimage_image_eq _ hf.injective]

中文:
引理 restrict_comap
  条件: (μ : 测度 β) (s : 集合 α)
  证明: by
  rw [comap_restrict hf]; rw [preimage_image_eq _ hf.injective]

Depends on / 依赖: comap_restrict, hf.injective, injective, preimage_image_eq
-/
lemma restrict_comap (μ : Measure β) (s : Set α) :
    (μ.comap f).restrict s = (μ.restrict (f '' s)).comap f := by
  rw [comap_restrict hf]; rw [preimage_image_eq _ hf.injective]

end

/--
theorem `_root_.MeasurableEquiv.restrict_map` / 定理 `_root_.MeasurableEquiv.restrict_map`

English:
theorem _root_.MeasurableEquiv.restrict_map
  given: (e : α ≃ᵐ β) (μ : Measure α) (s : Set β)
  proof: e.measurableEmbedding.restrict_map _ _

中文:
定理 _root_.可测等价.restrict_map
  条件: (e : α ≃ᵐ β) (μ : 测度 α) (s : 集合 β)
  证明: e.measurableEmbedding.restrict_map _ _

Depends on / 依赖: e.measurableEmbedding.restrict_map, measurableEmbedding, restrict_map
-/
theorem _root_.MeasurableEquiv.restrict_map (e : α ≃ᵐ β) (μ : Measure α) (s : Set β) :
    (μ.map e).restrict s = (μ.restrict <| e ⁻¹' s).map e :=
  e.measurableEmbedding.restrict_map _ _

/--
lemma `_root_.MeasurableEquiv.comap_apply` / 引理 `_root_.MeasurableEquiv.comap_apply`

English:
lemma _root_.MeasurableEquiv.comap_apply
  given: (e : α ≃ᵐ β) (μ : Measure β) (s : Set α)
  proof: by
  rw [e.measurableEmbedding.comap_apply]; rw [e.image_eq_preimage_symm]

中文:
引理 _root_.可测等价.comap_apply
  条件: (e : α ≃ᵐ β) (μ : 测度 β) (s : 集合 α)
  证明: by
  rw [e.measurableEmbedding.comap_apply]; rw [e.image_eq_preimage_symm]

Depends on / 依赖: comap_apply, e.image_eq_preimage_symm, e.measurableEmbedding.comap_apply, image_eq_preimage_symm, measurableEmbedding
-/
lemma _root_.MeasurableEquiv.comap_apply (e : α ≃ᵐ β) (μ : Measure β) (s : Set α) :
    comap e μ s = μ (e.symm ⁻¹' s) := by
  rw [e.measurableEmbedding.comap_apply]; rw [e.image_eq_preimage_symm]

end MeasurableEmbedding

/--
lemma `MeasureTheory.Measure.map_eq_comap` / 引理 `MeasureTheory.Measure.map_eq_comap`

English:
lemma MeasureTheory.Measure.map_eq_comap
  statement: {_ : MeasurableSpace α} {_ : MeasurableSpace β} {f : α -> β}
  proof: by
  ext s hs
  rw [map_apply hf hs]; rw [hg.comap_apply]; rw [← measure_sdiff_null hμg]
  congr
  simp
  grind

中文:
引理 测度论.测度.map_eq_comap
  结论: {_ : 可测空间 α} {_ : 可测空间 β} {f : α -> β}
  证明: by
  ext s hs
  rw [map_apply hf hs]; rw [hg.comap_apply]; rw [← measure_sdiff_null hμg]
  congr
  simp
  grind

Depends on / 依赖: comap_apply, hg.comap_apply, map_apply, measure_sdiff_null
-/
lemma MeasureTheory.Measure.map_eq_comap {_ : MeasurableSpace α} {_ : MeasurableSpace β} {f : α -> β}
    {g : β -> α} {μ : Measure α} (hf : Measurable f) (hg : MeasurableEmbedding g)
    (hμg : forallᵐ a ∂μ, a in Set.range g) (hfg : forall a, f (g a) = a) : μ.map f = μ.comap g := by
  ext s hs
  rw [map_apply hf hs]; rw [hg.comap_apply]; rw [← measure_sdiff_null hμg]
  congr
  simp
  grind

section Subtype

/--
theorem `comap_subtype_coe_apply` / 定理 `comap_subtype_coe_apply`

English:
theorem comap_subtype_coe_apply
  statement: {_m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s)
  proof: (MeasurableEmbedding.subtype_coe hs).comap_apply _ _

中文:
定理 comap_subtype_coe_apply
  结论: {_m0 : 可测空间 α} {s : 集合 α} (hs : 可测集 s)
  证明: (MeasurableEmbedding.subtype_coe hs).comap_apply _ _

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.subtype_coe, comap_apply, subtype_coe
-/
theorem comap_subtype_coe_apply {_m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) (t : Set s) : comap (↑) μ t = μ ((↑) '' t) :=
  (MeasurableEmbedding.subtype_coe hs).comap_apply _ _

/--
theorem `map_comap_subtype_coe` / 定理 `map_comap_subtype_coe`

English:
theorem map_comap_subtype_coe
  statement: {m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s)
  proof: by
  rw [(MeasurableEmbedding.subtype_coe hs).map_comap]; rw [Subtype.range_coe]

中文:
定理 map_comap_subtype_coe
  结论: {m0 : 可测空间 α} {s : 集合 α} (hs : 可测集 s)
  证明: by
  rw [(MeasurableEmbedding.subtype_coe hs).map_comap]; rw [Subtype.range_coe]

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.subtype_coe, Subtype, Subtype.range_coe, map_comap, range_coe, subtype_coe
-/
theorem map_comap_subtype_coe {m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) : (comap (↑) μ).map ((↑) : s -> α) = μ.restrict s := by
  rw [(MeasurableEmbedding.subtype_coe hs).map_comap]; rw [Subtype.range_coe]

/--
theorem `ae_restrict_iff_subtype` / 定理 `ae_restrict_iff_subtype`

English:
theorem ae_restrict_iff_subtype
  statement: {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}
  proof: by
  rw [← map_comap_subtype_coe hs]; rw [(MeasurableEmbedding.subtype_coe hs).ae_map_iff]

中文:
定理 ae_restrict_iff_subtype
  结论: {m0 : 可测空间 α} {μ : 测度 α} {s : 集合 α}
  证明: by
  rw [← map_comap_subtype_coe hs]; rw [(MeasurableEmbedding.subtype_coe hs).ae_map_iff]

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.subtype_coe, ae_map_iff, map_comap_subtype_coe, subtype_coe
-/
theorem ae_restrict_iff_subtype {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {p : α -> Prop} :
    (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ (x : s) ∂comap ((↑) : s -> α) μ, p x := by
  rw [← map_comap_subtype_coe hs]; rw [(MeasurableEmbedding.subtype_coe hs).ae_map_iff]

variable [MeasureSpace α] {s t : Set α}

/-!
### Volume on `s : Set α`

Note the instance is provided earlier as `Subtype.measureSpace`.
-/
attribute [local instance] Subtype.measureSpace

/--
theorem `volume_set_coe_def` / 定理 `volume_set_coe_def`

English:
theorem volume_set_coe_def
  given: (s : Set α)
  statement: (volume : Measure s) = comap ((↑) : s -> α) volume
  proof: rfl

中文:
定理 volume_set_coe_def
  条件: (s : 集合 α)
  结论: (volume : 测度 s) = comap ((↑) : s -> α) volume
  证明: rfl
-/
theorem volume_set_coe_def (s : Set α) : (volume : Measure s) = comap ((↑) : s -> α) volume :=
  rfl

/--
theorem `MeasurableSet.map_coe_volume` / 定理 `MeasurableSet.map_coe_volume`

English:
theorem MeasurableSet.map_coe_volume
  given: {s : Set α} (hs : MeasurableSet s)
  proof: by
  rw [volume_set_coe_def]; rw [(MeasurableEmbedding.subtype_coe hs).map_comap volume]; rw [Subtype.range_coe]

中文:
定理 可测集.map_coe_volume
  条件: {s : 集合 α} (hs : 可测集 s)
  证明: by
  rw [volume_set_coe_def]; rw [(MeasurableEmbedding.subtype_coe hs).map_comap volume]; rw [Subtype.range_coe]

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.subtype_coe, Subtype, Subtype.range_coe, map_comap, range_coe, subtype_coe, volume, volume_set_coe_def
-/
theorem MeasurableSet.map_coe_volume {s : Set α} (hs : MeasurableSet s) :
    volume.map ((↑) : s -> α) = restrict volume s := by
  rw [volume_set_coe_def]; rw [(MeasurableEmbedding.subtype_coe hs).map_comap volume]; rw [Subtype.range_coe]

/--
theorem `volume_image_subtype_coe` / 定理 `volume_image_subtype_coe`

English:
theorem volume_image_subtype_coe
  given: {s : Set α} (hs : MeasurableSet s) (t : Set s)
  proof: (comap_subtype_coe_apply hs volume t).symm

@[simp]

中文:
定理 volume_image_subtype_coe
  条件: {s : 集合 α} (hs : 可测集 s) (t : 集合 s)
  证明: (comap_subtype_coe_apply hs volume t).symm

@[simp]

Depends on / 依赖: comap_subtype_coe_apply, volume
-/
theorem volume_image_subtype_coe {s : Set α} (hs : MeasurableSet s) (t : Set s) :
    volume ((↑) '' t : Set α) = volume t :=
  (comap_subtype_coe_apply hs volume t).symm

@[simp]
/--
theorem `volume_preimage_coe` / 定理 `volume_preimage_coe`

English:
theorem volume_preimage_coe
  given: (hs : NullMeasurableSet s) (ht : MeasurableSet t)
  proof: by
  rw [volume_set_coe_def]; rw [comap_apply₀ _ _ Subtype.coe_injective
      (fun h => MeasurableSet.nullMeasurableSet_subtype_coe hs)
      (measurable_subtype_coe ht).nullMeasurableSet]; rw [image_preimage_eq_inter_range]; rw [Subtype.range_coe]

中文:
定理 volume_preimage_coe
  条件: (hs : NullMeasurableSet s) (ht : 可测集 t)
  证明: by
  rw [volume_set_coe_def]; rw [comap_apply₀ _ _ Subtype.coe_injective
      (fun h => MeasurableSet.nullMeasurableSet_subtype_coe hs)
      (measurable_subtype_coe ht).nullMeasurableSet]; rw [image_preimage_eq_inter_range]; rw [Subtype.range_coe]

Depends on / 依赖: BoolAlg, BoolAlg.ofHom, InducedCategory, InducedCategory.homMk, MeasurableSet, MeasurableSet.nullMeasurableSet_subtype_coe, Subtype, Subtype.coe_injective, Subtype.range_coe, coe_injective, image_preimage_eq_inter_range, measurable_subtype_coe, nullMeasurableSet, nullMeasurableSet_subtype_coe, range_coe, volume_set_coe_def
-/
theorem volume_preimage_coe (hs : NullMeasurableSet s) (ht : MeasurableSet t) :
    volume (((↑) : s -> α) ⁻¹' t) = volume (t inter s) := by
  rw [volume_set_coe_def]; rw [comap_apply₀ _ _ Subtype.coe_injective
      (fun h => MeasurableSet.nullMeasurableSet_subtype_coe hs)
      (measurable_subtype_coe ht).nullMeasurableSet]; rw [image_preimage_eq_inter_range]; rw [Subtype.range_coe]

end Subtype

section Piecewise

variable [MeasurableSpace α] {μ : Measure α} {s t : Set α} {f g : α -> β}

/--
theorem `piecewise_ae_eq_restrict` / 定理 `piecewise_ae_eq_restrict`

English:
theorem piecewise_ae_eq_restrict
  given: [DecidablePred (· in s)] (hs : MeasurableSet s)
  proof: by
  rw [ae_restrict_eq hs]
  exact (piecewise_eqOn s f g).eventuallyEq.filter_mono inf_le_right

中文:
定理 piecewise_ae_eq_restrict
  条件: [DecidablePred (· in s)] (hs : 可测集 s)
  证明: by
  rw [ae_restrict_eq hs]
  exact (piecewise_eqOn s f g).eventuallyEq.filter_mono inf_le_right

Depends on / 依赖: ae_restrict_eq, eventuallyEq, eventuallyEq.filter_mono, filter_mono, inf_le_right, piecewise_eqOn
-/
theorem piecewise_ae_eq_restrict [DecidablePred (· in s)] (hs : MeasurableSet s) :
    piecewise s f g =ᵐ[μ.restrict s] f := by
  rw [ae_restrict_eq hs]
  exact (piecewise_eqOn s f g).eventuallyEq.filter_mono inf_le_right

/--
theorem `piecewise_ae_eq_restrict_compl` / 定理 `piecewise_ae_eq_restrict_compl`

English:
theorem piecewise_ae_eq_restrict_compl
  given: [DecidablePred (· in s)] (hs : MeasurableSet s)
  proof: by
  rw [ae_restrict_eq hs.compl]
  exact (piecewise_eqOn_compl s f g).eventuallyEq.filter_mono inf_le_right

中文:
定理 piecewise_ae_eq_restrict_compl
  条件: [DecidablePred (· in s)] (hs : 可测集 s)
  证明: by
  rw [ae_restrict_eq hs.compl]
  exact (piecewise_eqOn_compl s f g).eventuallyEq.filter_mono inf_le_right

Depends on / 依赖: ae_restrict_eq, eventuallyEq, eventuallyEq.filter_mono, filter_mono, hs.compl, inf_le_right, piecewise_eqOn_compl
-/
theorem piecewise_ae_eq_restrict_compl [DecidablePred (· in s)] (hs : MeasurableSet s) :
    piecewise s f g =ᵐ[μ.restrict sᶜ] g := by
  rw [ae_restrict_eq hs.compl]
  exact (piecewise_eqOn_compl s f g).eventuallyEq.filter_mono inf_le_right

/--
theorem `piecewise_ae_eq_of_ae_eq_set` / 定理 `piecewise_ae_eq_of_ae_eq_set`

English:
theorem piecewise_ae_eq_of_ae_eq_set
  statement: [DecidablePred (· in s)] [DecidablePred (· in t)]
  proof: hst.mem_iff.mono fun x hx => by simp [piecewise, hx]

中文:
定理 piecewise_ae_eq_of_ae_eq_set
  结论: [DecidablePred (· in s)] [DecidablePred (· in t)]
  证明: hst.mem_iff.mono fun x hx => by simp [piecewise, hx]

Depends on / 依赖: hst.mem_iff.mono, mem_iff, piecewise
-/
theorem piecewise_ae_eq_of_ae_eq_set [DecidablePred (· in s)] [DecidablePred (· in t)]
    (hst : s =ᵐ[μ] t) : s.piecewise f g =ᵐ[μ] t.piecewise f g :=
  hst.mem_iff.mono fun x hx => by simp [piecewise, hx]

end Piecewise

section IndicatorFunction

variable [MeasurableSpace α] {μ : Measure α} {s t : Set α} {f : α -> β}

/--
theorem `mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem` / 定理 `mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem`

English:
theorem mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem
  statement: [Zero β] {t : Set β}
  proof: by
  classical
  simp_rw [mem_map, mem_ae_iff]
  rw [Measure.restrict_apply' hs]; rw [Set.indicator_preimage]; rw [Set.ite]
  simp_rw [Set.compl_union, Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ union sᶜ) inter ((fun _ => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ inter s) = 0
  simp only [ht, ← Set.co

中文:
定理 mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem
  结论: [零 β] {t : 集合 β}
  证明: by
  classical
  simp_rw [mem_map, mem_ae_iff]
  rw [Measure.restrict_apply' hs]; rw [Set.indicator_preimage]; rw [Set.ite]
  simp_rw [Set.compl_union, Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ union sᶜ) inter ((fun _ => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ inter s) = 0
  simp only [ht, ← Set.co

Depends on / 依赖: Measure, Measure.restrict_apply, Set.compl_eq_univ_sdiff, Set.compl_inter, Set.compl_inter_self, Set.compl_union, Set.indicator_preimage, Set.ite, Set.preimage_const, Set.union_empty, Set.union_inter_distrib_right, classical, compl_compl, compl_eq_univ_sdiff, compl_inter, compl_inter_self, compl_union, if_true, indicator_preimage, mem_ae_iff
-/
theorem mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem [Zero β] {t : Set β}
    (ht : (0 : β) in t) (hs : MeasurableSet s) :
    t in Filter.map (s.indicator f) (ae μ) ↔ t in Filter.map f (ae <| μ.restrict s) := by
  classical
  simp_rw [mem_map, mem_ae_iff]
  rw [Measure.restrict_apply' hs]; rw [Set.indicator_preimage]; rw [Set.ite]
  simp_rw [Set.compl_union, Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ union sᶜ) inter ((fun _ => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ inter s) = 0
  simp only [ht, ← Set.compl_eq_univ_sdiff, compl_compl, if_true,
    Set.preimage_const]
  simp_rw [Set.union_inter_distrib_right, Set.compl_inter_self s, Set.union_empty]

/--
theorem `mem_map_indicator_ae_iff_of_zero_notMem` / 定理 `mem_map_indicator_ae_iff_of_zero_notMem`

English:
theorem mem_map_indicator_ae_iff_of_zero_notMem
  given: [Zero β] {t : Set β} (ht : (0 : β) ∉ t)
  proof: by
  classical
  rw [mem_map]; rw [mem_ae_iff]; rw [Set.indicator_preimage]; rw [Set.ite]; rw [Set.compl_union]; rw [Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ union sᶜ) inter ((fun _ => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ union sᶜ) = 0
  simp only [ht, if_false, Set.compl_empty, Set.empty_sdiff

中文:
定理 mem_map_indicator_ae_iff_of_zero_notMem
  条件: [零 β] {t : 集合 β} (ht : (0 : β) ∉ t)
  证明: by
  classical
  rw [mem_map]; rw [mem_ae_iff]; rw [Set.indicator_preimage]; rw [Set.ite]; rw [Set.compl_union]; rw [Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ union sᶜ) inter ((fun _ => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ union sᶜ) = 0
  simp only [ht, if_false, Set.compl_empty, Set.empty_sdiff

Depends on / 依赖: Set.compl_empty, Set.compl_inter, Set.compl_union, Set.empty_sdiff, Set.indicator_preimage, Set.inter_univ, Set.ite, Set.preimage_const, classical, compl_empty, compl_inter, compl_union, empty_sdiff, if_false, indicator_preimage, inter_univ, mem_ae_iff, mem_map, preimage_const
-/
theorem mem_map_indicator_ae_iff_of_zero_notMem [Zero β] {t : Set β} (ht : (0 : β) ∉ t) :
    t in Filter.map (s.indicator f) (ae μ) ↔ μ ((f ⁻¹' t)ᶜ union sᶜ) = 0 := by
  classical
  rw [mem_map]; rw [mem_ae_iff]; rw [Set.indicator_preimage]; rw [Set.ite]; rw [Set.compl_union]; rw [Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ union sᶜ) inter ((fun _ => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ union sᶜ) = 0
  simp only [ht, if_false, Set.compl_empty, Set.empty_sdiff, Set.inter_univ, Set.preimage_const]

/--
theorem `map_restrict_ae_le_map_indicator_ae` / 定理 `map_restrict_ae_le_map_indicator_ae`

English:
theorem map_restrict_ae_le_map_indicator_ae
  given: [Zero β] (hs : MeasurableSet s)
  proof: by
  intro t
  by_cases ht : (0 : β) in t
  · rw [mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem ht hs]
    exact id
  rw [mem_map_indicator_ae_iff_of_zero_notMem ht]; rw [mem_map_restrict_ae_iff hs]
  exact fun h => measure_mono_null (Set.inter_subset_left.trans Set.subset_union_left) h

中文:
定理 map_restrict_ae_le_map_indicator_ae
  条件: [零 β] (hs : 可测集 s)
  证明: by
  intro t
  by_cases ht : (0 : β) in t
  · rw [mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem ht hs]
    exact id
  rw [mem_map_indicator_ae_iff_of_zero_notMem ht]; rw [mem_map_restrict_ae_iff hs]
  exact fun h => measure_mono_null (Set.inter_subset_left.trans Set.subset_union_left) h

Depends on / 依赖: Set.inter_subset_left.trans, Set.subset_union_left, X.toPartOrd.str, inter_subset_left, measure_mono_null, mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem, mem_map_indicator_ae_iff_of_zero_notMem, mem_map_restrict_ae_iff, subset_union_left, toPartOrd
-/
theorem map_restrict_ae_le_map_indicator_ae [Zero β] (hs : MeasurableSet s) :
    Filter.map f (ae <| μ.restrict s) <= Filter.map (s.indicator f) (ae μ) := by
  intro t
  by_cases ht : (0 : β) in t
  · rw [mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem ht hs]
    exact id
  rw [mem_map_indicator_ae_iff_of_zero_notMem ht]; rw [mem_map_restrict_ae_iff hs]
  exact fun h => measure_mono_null (Set.inter_subset_left.trans Set.subset_union_left) h

variable [Zero β]

/--
theorem `indicator_ae_eq_restrict` / 定理 `indicator_ae_eq_restrict`

English:
theorem indicator_ae_eq_restrict
  given: (hs : MeasurableSet s)
  statement: indicator s f =ᵐ[μ.restrict s] f
  proof: by
  classical exact piecewise_ae_eq_restrict hs

中文:
定理 indicator_ae_eq_restrict
  条件: (hs : 可测集 s)
  结论: indicator s f =ᵐ[μ.restrict s] f
  证明: by
  classical exact piecewise_ae_eq_restrict hs

Depends on / 依赖: classical, piecewise_ae_eq_restrict
-/
theorem indicator_ae_eq_restrict (hs : MeasurableSet s) : indicator s f =ᵐ[μ.restrict s] f := by
  classical exact piecewise_ae_eq_restrict hs

/--
theorem `indicator_ae_eq_restrict_compl` / 定理 `indicator_ae_eq_restrict_compl`

English:
theorem indicator_ae_eq_restrict_compl
  given: (hs : MeasurableSet s)
  proof: by
  classical exact piecewise_ae_eq_restrict_compl hs

中文:
定理 indicator_ae_eq_restrict_compl
  条件: (hs : 可测集 s)
  证明: by
  classical exact piecewise_ae_eq_restrict_compl hs

Depends on / 依赖: classical, piecewise_ae_eq_restrict_compl
-/
theorem indicator_ae_eq_restrict_compl (hs : MeasurableSet s) :
    indicator s f =ᵐ[μ.restrict sᶜ] 0 := by
  classical exact piecewise_ae_eq_restrict_compl hs

/--
theorem `indicator_ae_eq_of_restrict_compl_ae_eq_zero` / 定理 `indicator_ae_eq_of_restrict_compl_ae_eq_zero`

English:
theorem indicator_ae_eq_of_restrict_compl_ae_eq_zero
  statement: (hs : MeasurableSet s)
  proof: by
  rw [Filter.EventuallyEq]; rw [ae_restrict_iff' hs.compl] at hf
  filter_upwards [hf] with x hx
  by_cases hxs : x in s
  · simp only [hxs, Set.indicator_of_mem]
  · simp only [hx hxs, Pi.zero_apply, Set.indicator_apply_eq_zero, imp_true_iff]

中文:
定理 indicator_ae_eq_of_restrict_compl_ae_eq_zero
  结论: (hs : 可测集 s)
  证明: by
  rw [Filter.EventuallyEq]; rw [ae_restrict_iff' hs.compl] at hf
  filter_upwards [hf] with x hx
  by_cases hxs : x in s
  · simp only [hxs, Set.indicator_of_mem]
  · simp only [hx hxs, Pi.zero_apply, Set.indicator_apply_eq_zero, imp_true_iff]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Pi.zero_apply, Set.indicator_apply_eq_zero, Set.indicator_of_mem, ae_restrict_iff, filter_upwards, hs.compl, imp_true_iff, indicator_apply_eq_zero, indicator_of_mem, zero_apply
-/
theorem indicator_ae_eq_of_restrict_compl_ae_eq_zero (hs : MeasurableSet s)
    (hf : f =ᵐ[μ.restrict sᶜ] 0) : s.indicator f =ᵐ[μ] f := by
  rw [Filter.EventuallyEq]; rw [ae_restrict_iff' hs.compl] at hf
  filter_upwards [hf] with x hx
  by_cases hxs : x in s
  · simp only [hxs, Set.indicator_of_mem]
  · simp only [hx hxs, Pi.zero_apply, Set.indicator_apply_eq_zero, imp_true_iff]

/--
theorem `indicator_ae_eq_zero_of_restrict_ae_eq_zero` / 定理 `indicator_ae_eq_zero_of_restrict_ae_eq_zero`

English:
theorem indicator_ae_eq_zero_of_restrict_ae_eq_zero
  statement: (hs : MeasurableSet s)
  proof: by
  rw [Filter.EventuallyEq]; rw [ae_restrict_iff' hs] at hf
  filter_upwards [hf] with x hx
  by_cases hxs : x in s
  · simp only [hxs, hx hxs, Set.indicator_of_mem]
  · simp [hxs]

中文:
定理 indicator_ae_eq_zero_of_restrict_ae_eq_zero
  结论: (hs : 可测集 s)
  证明: by
  rw [Filter.EventuallyEq]; rw [ae_restrict_iff' hs] at hf
  filter_upwards [hf] with x hx
  by_cases hxs : x in s
  · simp only [hxs, hx hxs, Set.indicator_of_mem]
  · simp [hxs]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Set.indicator_of_mem, ae_restrict_iff, filter_upwards, indicator_of_mem
-/
theorem indicator_ae_eq_zero_of_restrict_ae_eq_zero (hs : MeasurableSet s)
    (hf : f =ᵐ[μ.restrict s] 0) : s.indicator f =ᵐ[μ] 0 := by
  rw [Filter.EventuallyEq]; rw [ae_restrict_iff' hs] at hf
  filter_upwards [hf] with x hx
  by_cases hxs : x in s
  · simp only [hxs, hx hxs, Set.indicator_of_mem]
  · simp [hxs]

/--
theorem `indicator_ae_eq_of_ae_eq_set` / 定理 `indicator_ae_eq_of_ae_eq_set`

English:
theorem indicator_ae_eq_of_ae_eq_set
  given: (hst : s =ᵐ[μ] t)
  statement: s.indicator f =ᵐ[μ] t.indicator f
  proof: by
  classical exact piecewise_ae_eq_of_ae_eq_set hst

中文:
定理 indicator_ae_eq_of_ae_eq_set
  条件: (hst : s =ᵐ[μ] t)
  结论: s.indicator f =ᵐ[μ] t.indicator f
  证明: by
  classical exact piecewise_ae_eq_of_ae_eq_set hst

Depends on / 依赖: classical, piecewise_ae_eq_of_ae_eq_set
-/
theorem indicator_ae_eq_of_ae_eq_set (hst : s =ᵐ[μ] t) : s.indicator f =ᵐ[μ] t.indicator f := by
  classical exact piecewise_ae_eq_of_ae_eq_set hst

/--
theorem `indicator_meas_zero` / 定理 `indicator_meas_zero`

English:
theorem indicator_meas_zero
  given: (hs : μ s = 0)
  statement: indicator s f =ᵐ[μ] 0
  proof: indicator_empty' f ▸ indicator_ae_eq_of_ae_eq_set (ae_eq_empty.2 hs)

中文:
定理 indicator_meas_zero
  条件: (hs : μ s = 0)
  结论: indicator s f =ᵐ[μ] 0
  证明: indicator_empty' f ▸ indicator_ae_eq_of_ae_eq_set (ae_eq_empty.2 hs)

Depends on / 依赖: ae_eq_empty, indicator_ae_eq_of_ae_eq_set, indicator_empty
-/
theorem indicator_meas_zero (hs : μ s = 0) : indicator s f =ᵐ[μ] 0 :=
  indicator_empty' f ▸ indicator_ae_eq_of_ae_eq_set (ae_eq_empty.2 hs)

/--
theorem `ae_eq_restrict_iff_indicator_ae_eq` / 定理 `ae_eq_restrict_iff_indicator_ae_eq`

English:
theorem ae_eq_restrict_iff_indicator_ae_eq
  given: {g : α -> β} (hs : MeasurableSet s)
  proof: by
  rw [Filter.EventuallyEq]; rw [ae_restrict_iff' hs]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> filter_upwards [h] with x hx
  · by_cases hxs : x in s
    · simp [hxs, hx hxs]
    · simp [hxs]
  · intro hxs
    simpa [hxs] using hx

中文:
定理 ae_eq_restrict_iff_indicator_ae_eq
  条件: {g : α -> β} (hs : 可测集 s)
  证明: by
  rw [Filter.EventuallyEq]; rw [ae_restrict_iff' hs]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> filter_upwards [h] with x hx
  · by_cases hxs : x in s
    · simp [hxs, hx hxs]
    · simp [hxs]
  · intro hxs
    simpa [hxs] using hx

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, ae_restrict_iff, filter_upwards
-/
theorem ae_eq_restrict_iff_indicator_ae_eq {g : α -> β} (hs : MeasurableSet s) :
    f =ᵐ[μ.restrict s] g ↔ s.indicator f =ᵐ[μ] s.indicator g := by
  rw [Filter.EventuallyEq]; rw [ae_restrict_iff' hs]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> filter_upwards [h] with x hx
  · by_cases hxs : x in s
    · simp [hxs, hx hxs]
    · simp [hxs]
  · intro hxs
    simpa [hxs] using hx

end IndicatorFunction

section Sum

open Finset in
/--
lemma `MeasureTheory.Measure.sum_restrict_le` / 引理 `MeasureTheory.Measure.sum_restrict_le`

English:
lemma MeasureTheory.Measure.sum_restrict_le
  statement: {_ : MeasurableSpace α}
  proof: by
  classical
  refine le_iff.mpr (fun t ht => le_of_eq_of_le (sum_apply _ ht) ?_)
  refine ENNReal.summable.tsum_le_of_sum_le (fun F => ?_)
  -- `P` is a partition of `⋃ i ∈ F, s i` indexed by `C ∈ Cs` (nonempty subsets of `F`).
  -- `P` is a partition of `s i` when restricted to `C ∈ G i` (subset

中文:
引理 测度论.测度.sum_restrict_le
  结论: {_ : 可测空间 α}
  证明: by
  classical
  refine le_iff.mpr (fun t ht => le_of_eq_of_le (sum_apply _ ht) ?_)
  refine ENNReal.summable.tsum_le_of_sum_le (fun F => ?_)
  -- `P` is a partition of `⋃ i ∈ F, s i` indexed by `C ∈ Cs` (nonempty subsets of `F`).
  -- `P` is a partition of `s i` when restricted to `C ∈ G i` (subset

Depends on / 依赖: ENNReal, ENNReal.summable.tsum_le_of_sum_le, classical, le_iff, le_iff.mpr, le_of_eq_of_le, sum_apply, summable, tsum_le_of_sum_le
-/
lemma MeasureTheory.Measure.sum_restrict_le {_ : MeasurableSpace α}
    {μ : Measure α} {s : ι -> Set α} {M : Nat} (hs_meas : forall i, MeasurableSet (s i))
    (hs : forall y, {i | y in s i}.encard <= M) :
    Measure.sum (fun i => μ.restrict (s i)) <= M • μ.restrict (⋃ i, s i) := by
  classical
  refine le_iff.mpr (fun t ht => le_of_eq_of_le (sum_apply _ ht) ?_)
  refine ENNReal.summable.tsum_le_of_sum_le (fun F => ?_)
  -- `P` is a partition of `⋃ i ∈ F, s i` indexed by `C ∈ Cs` (nonempty subsets of `F`).
  -- `P` is a partition of `s i` when restricted to `C ∈ G i` (subsets of `F` containing `i`).
  let P (C : Finset ι) := (⋂ i in C, s i) inter (⋂ i in (F \ C), (s i)ᶜ)
  let Cs := F.powerset \ {∅}
  let G (i : ι) := { C | C in F.powerset ∧ i in C }
  have P_meas C : MeasurableSet (P C) :=
.inter measurableSet_biInter C (fun i _ => hs_meas i)
      measurableSet_biInter _ (fun i _ => (hs_meas i).compl)
  have P_cover {i : ι} (hi : i in F) : s i subseteq ⋃ C in G i, P C := by
    refine fun x hx => Set.mem_biUnion (x := F.filter (x in s ·)) ?_ ?_
    · exact ⟨Finset.mem_powerset.mpr (filter_subset _ F), mem_filter.mpr ⟨hi, hx⟩⟩
    · simp_rw [P, mem_inter_iff, mem_iInter, Finset.mem_sdiff, mem_filter]; tauto
  have iUnion_P : ⋃ C in Cs, P C subseteq ⋃ i, s i := by
    intro x hx
    simp_rw [Cs, Finset.mem_sdiff, mem_iUnion] at hx
    have ⟨C, ⟨_, C_nonempty⟩, hxC⟩ := hx
have ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr Finset.notMem_singleton.mp C_nonempty
    exact ⟨s i, ⟨i, rfl⟩, hxC.1 (s i) ⟨i, by simp [hi]⟩⟩
  have P_subset_s {i : ι} {C : Finset ι} (hiC : i in C) : P C subseteq s i := by
    intro x hx
    simp only [P, mem_inter_iff, mem_iInter] at hx
    exact hx.1 i hiC
  have mem_C {i} (hi : i in F) {C : Finset ι} {x : α} (hx : x in P C) (hxs : x in s i) : i in C := by
    rw [mem_inter_iff]; rw [mem_iInter₂]; rw [mem_iInter₂] at hx
    exact of_not_not fun h => hx.2 i (mem_sdiff.mpr ⟨hi, h⟩) hxs
  have C_subset_C {C₁ C₂} (hC₁ : C₁ in Cs) {x : α} (hx : x in P C₁ inter P C₂) : C₁ subseteq C₂ :=
fun i hi => mem_C (mem_powerset.mp (sdiff_subset hC₁) hi) hx.2 P_subset_s hi hx.1
  calc ∑ i in F, (μ.restrict (s i)) t
    _ <= ∑ i in F, Measure.sum (fun (C : G i) => μ.restrict (P C)) t :=
F.sum_le_sum fun i hi => (restrict_mono_set μ (P_cover hi) t).trans
        restrict_biUnion_le ((finite_toSet F.powerset).subset (sep_subset _ _)).countable t
    _ = ∑ i in F, ∑' (C : G i), μ.restrict (P C) t := by simp_rw [Measure.sum_apply _ ht]
    _ = ∑' C, ∑ i in F, (G i).indicator (fun C => μ.restrict (P C) t) C := by
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      congr with i
      rw [tsum_subtype (G i) (fun C => (μ.restrict (P C)) t)]
    _ = ∑ C in Cs, ∑ i in F, (C : Set ι).indicator (fun _ => (μ.restrict (P C)) t) i := by
      rw [sum_eq_tsum_indicator]
      congr with C
      by_cases hC : C in F.powerset <;> by_cases hC' : C = ∅ <;>
        simp [hC, hC', Cs, G, indicator, -Finset.mem_powerset, -coe_powerset]
    _ = ∑ C in Cs, {a in F | a in C}.card • μ.restrict (P C) t := by simp [indicator]; rfl
    _ <= ∑ C in Cs, M • μ.restrict (P C) t := by
      refine sum_le_sum fun C hC => ?_
      by_cases hPC : P C = ∅
      · simp [hPC]
      have hCM : (C : Set ι).encard <= M :=
        have ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hPC
        (encard_mono (mem_iInter₂.mp hx.1)).trans (hs x)
exact nsmul_le_nsmul_left zero_le calc {a in F | a in C}.card
_ <= C.card := card_mono fun i hi => (F.mem_filter.mp hi).2
        _ = (C : Set ι).ncard := (ncard_coe_finset C).symm
        _ <= M := ENat.toNat_le_of_le_natCast hCM
    _ = M • (μ.restrict (⋃ C in Cs, (P C)) t) := by
      rw [← smul_sum]; rw [← Cs.tsum_subtype]; rw [μ.restrict_biUnion_finset _ P_meas]; rw [Measure.sum_apply _ ht]
refine fun C₁ hC₁ C₂ hC₂ hC => Set.disjoint_iff.mpr fun x hx => hC ?_
      exact subset_antisymm (C_subset_C hC₁ hx) (C_subset_C hC₂ (Set.inter_comm _ _ ▸ hx))
    _ <= (M • μ.restrict (⋃ i, s i)) t := by
      rw [Measure.smul_apply]
      exact nsmul_le_nsmul_right (μ.restrict_mono_set iUnion_P t) M

end Sum
