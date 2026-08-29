/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Restriction of a measure to a sub-σ-algebra


## Main definitions

* `MeasureTheory.Measure.trim`: restriction of a measure to a sub-sigma algebra.

-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*}

/-- Restriction of a measure to a sub-σ-algebra.
It is common to see a measure `μ` on a measurable space structure `m0` as being also a measure on
any `m ≤ m0`. Since measures in mathlib have to be trimmed to the measurable space, `μ` itself
cannot be a measure on `m`, hence the definition of `μ.trim hm`.

This notion is related to `OuterMeasure.trim`, see the lemma
`toOuterMeasure_trim_eq_trim_toOuterMeasure`. -/
noncomputable
/--
Definition of `Measure.trim` / `Measure.trim` 的定义

English:
definition Measure.trim
  signature: {m m0 : MeasurableSpace α} (μ : @Measure α m0) (hm : m <= m0)
  body: @OuterMeasure.toMeasure α m μ.toOuterMeasure (hm.trans (le_toOuterMeasure_caratheodory μ))

@[simp]

中文:
定义 Measure.trim
  签名: {m m0 : MeasurableSpace α} (μ : @Measure α m0) (hm : m <= m0)
  定义体: @OuterMeasure.toMeasure α m μ.toOuterMeasure (hm.trans (le_toOuterMeasure_caratheodory μ))

@[simp]

Depends on / 依赖: OuterMeasure, OuterMeasure.toMeasure, hm.trans, le_toOuterMeasure_caratheodory, toMeasure, toOuterMeasure
-/
def Measure.trim {m m0 : MeasurableSpace α} (μ : @Measure α m0) (hm : m <= m0) : @Measure α m :=
  @OuterMeasure.toMeasure α m μ.toOuterMeasure (hm.trans (le_toOuterMeasure_caratheodory μ))

@[simp]
/--
theorem `trim_eq_self` / 定理 `trim_eq_self`

English:
theorem trim_eq_self
  given: [MeasurableSpace α] {μ : Measure α}
  statement: μ.trim le_rfl = μ
  proof: by
  simp [Measure.trim]

中文:
定理 trim_eq_self
  条件: [MeasurableSpace α] {μ : Measure α}
  结论: μ.trim le_rfl = μ
  证明: by
  simp [Measure.trim]

Depends on / 依赖: Measure, Measure.trim
-/
theorem trim_eq_self [MeasurableSpace α] {μ : Measure α} : μ.trim le_rfl = μ := by
  simp [Measure.trim]

variable {m m0 : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {s : Set α}

/--
theorem `toOuterMeasure_trim_eq_trim_toOuterMeasure` / 定理 `toOuterMeasure_trim_eq_trim_toOuterMeasure`

English:
theorem toOuterMeasure_trim_eq_trim_toOuterMeasure
  given: (μ : Measure α) (hm : m <= m0)
  proof: by
  rw [Measure.trim]; rw [toMeasure_toOuterMeasure (ms := m)]

@[simp]

中文:
定理 toOuterMeasure_trim_eq_trim_toOuterMeasure
  条件: (μ : Measure α) (hm : m <= m0)
  证明: by
  rw [Measure.trim]; rw [toMeasure_toOuterMeasure (ms := m)]

@[simp]

Depends on / 依赖: Measure, Measure.trim, f.hom, injective, toMeasure_toOuterMeasure
-/
theorem toOuterMeasure_trim_eq_trim_toOuterMeasure (μ : Measure α) (hm : m <= m0) :
    @Measure.toOuterMeasure _ m (μ.trim hm) = @OuterMeasure.trim _ m μ.toOuterMeasure := by
  rw [Measure.trim]; rw [toMeasure_toOuterMeasure (ms := m)]

@[simp]
/--
theorem `zero_trim` / 定理 `zero_trim`

English:
theorem zero_trim
  given: (hm : m <= m0)
  statement: (0 : Measure α).trim hm = (0 : @Measure α m)
  proof: by
  simp [Measure.trim, @OuterMeasure.toMeasure_zero _ m]

中文:
定理 zero_trim
  条件: (hm : m <= m0)
  结论: (0 : Measure α).trim hm = (0 : @Measure α m)
  证明: by
  simp [Measure.trim, @OuterMeasure.toMeasure_zero _ m]

Depends on / 依赖: Measure, Measure.trim, OuterMeasure, OuterMeasure.toMeasure_zero, f.hom, le_iff_le, toMeasure_zero
-/
theorem zero_trim (hm : m <= m0) : (0 : Measure α).trim hm = (0 : @Measure α m) := by
  simp [Measure.trim, @OuterMeasure.toMeasure_zero _ m]

/--
theorem `trim_measurableSet_eq` / 定理 `trim_measurableSet_eq`

English:
theorem trim_measurableSet_eq
  given: (hm : m <= m0) (hs : @MeasurableSet α m s)
  statement: μ.trim hm s = μ s
  proof: by
  rw [Measure.trim]; rw [toMeasure_apply (ms := m) _ _ hs]; rw [Measure.coe_toOuterMeasure]

中文:
定理 trim_measurableSet_eq
  条件: (hm : m <= m0) (hs : @MeasurableSet α m s)
  结论: μ.trim hm s = μ s
  证明: by
  rw [Measure.trim]; rw [toMeasure_apply (ms := m) _ _ hs]; rw [Measure.coe_toOuterMeasure]

Depends on / 依赖: Measure, Measure.coe_toOuterMeasure, Measure.trim, coe_toOuterMeasure, toMeasure_apply
-/
theorem trim_measurableSet_eq (hm : m <= m0) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s := by
  rw [Measure.trim]; rw [toMeasure_apply (ms := m) _ _ hs]; rw [Measure.coe_toOuterMeasure]

/--
theorem `le_trim` / 定理 `le_trim`

English:
theorem le_trim
  given: (hm : m <= m0)
  statement: μ s <= μ.trim hm s
  proof: by
  simp_rw [Measure.trim]
  exact @le_toMeasure_apply _ m _ _ _

中文:
定理 le_trim
  条件: (hm : m <= m0)
  结论: μ s <= μ.trim hm s
  证明: by
  simp_rw [Measure.trim]
  exact @le_toMeasure_apply _ m _ _ _

Depends on / 依赖: Measure, Measure.trim, le_toMeasure_apply, simp_rw
-/
theorem le_trim (hm : m <= m0) : μ s <= μ.trim hm s := by
  simp_rw [Measure.trim]
  exact @le_toMeasure_apply _ m _ _ _

/--
lemma `trim_eq_map` / 引理 `trim_eq_map`

English:
lemma trim_eq_map
  given: (hm : m <= m0)
  statement: μ.trim hm = @Measure.map _ _ _ m id μ
  proof: by
  refine @Measure.ext α m _ _ (fun s hs => ?_)
  rw [Measure.map_apply (measurable_id'' hm) hs]; rw [trim_measurableSet_eq hm hs]; rw [Set.preimage_id]

中文:
引理 trim_eq_map
  条件: (hm : m <= m0)
  结论: μ.trim hm = @Measure.map _ _ _ m id μ
  证明: by
  refine @Measure.ext α m _ _ (fun s hs => ?_)
  rw [Measure.map_apply (measurable_id'' hm) hs]; rw [trim_measurableSet_eq hm hs]; rw [Set.preimage_id]

Depends on / 依赖: Measure, Measure.ext, Measure.map_apply, Set.preimage_id, map_apply, measurable_id, preimage_id, trim_measurableSet_eq
-/
lemma trim_eq_map (hm : m <= m0) : μ.trim hm = @Measure.map _ _ _ m id μ := by
  refine @Measure.ext α m _ _ (fun s hs => ?_)
  rw [Measure.map_apply (measurable_id'' hm) hs]; rw [trim_measurableSet_eq hm hs]; rw [Set.preimage_id]

/--
lemma `map_trim_comap` / 引理 `map_trim_comap`

English:
lemma map_trim_comap
  given: {f : α -> β} (hf : Measurable f)
  proof: by
  ext s hs
  rw [Measure.map_apply hf hs]; rw [Measure.map_apply _ hs]; rw [trim_measurableSet_eq]
  · exact ⟨s, hs, rfl⟩
  · exact Measurable.of_comap_le le_rfl

中文:
引理 map_trim_comap
  条件: {f : α -> β} (hf : Measurable f)
  证明: by
  ext s hs
  rw [Measure.map_apply hf hs]; rw [Measure.map_apply _ hs]; rw [trim_measurableSet_eq]
  · exact ⟨s, hs, rfl⟩
  · exact Measurable.of_comap_le le_rfl

Depends on / 依赖: Measurable, Measurable.of_comap_le, Measure, Measure.map_apply, le_rfl, map_apply, of_comap_le, trim_measurableSet_eq
-/
lemma map_trim_comap {f : α -> β} (hf : Measurable f) :
    @Measure.map _ _ (mβ.comap f) _ f (μ.trim hf.comap_le) = μ.map f := by
  ext s hs
  rw [Measure.map_apply hf hs]; rw [Measure.map_apply _ hs]; rw [trim_measurableSet_eq]
  · exact ⟨s, hs, rfl⟩
  · exact Measurable.of_comap_le le_rfl

/--
lemma `trim_comap_apply` / 引理 `trim_comap_apply`

English:
lemma trim_comap_apply
  given: {f : α -> β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s)
  proof: by
  rw [← map_trim_comap hf]; rw [Measure.map_apply (Measurable.of_comap_le le_rfl) hs]

中文:
引理 trim_comap_apply
  条件: {f : α -> β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s)
  证明: by
  rw [← map_trim_comap hf]; rw [Measure.map_apply (Measurable.of_comap_le le_rfl) hs]

Depends on / 依赖: Measurable, Measurable.of_comap_le, Measure, Measure.map_apply, le_rfl, map_apply, map_trim_comap, of_comap_le
-/
lemma trim_comap_apply {f : α -> β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    μ.trim hf.comap_le (f ⁻¹' s) = μ.map f s := by
  rw [← map_trim_comap hf]; rw [Measure.map_apply (Measurable.of_comap_le le_rfl) hs]

/--
lemma `ae_map_iff_ae_trim` / 引理 `ae_map_iff_ae_trim`

English:
lemma ae_map_iff_ae_trim
  statement: {f : α -> β} (hf : Measurable f)
  proof: by
  rw [← map_trim_comap hf]; rw [ae_map_iff (Measurable.of_comap_le le_rfl).aemeasurable hp]

中文:
引理 ae_map_iff_ae_trim
  结论: {f : α -> β} (hf : Measurable f)
  证明: by
  rw [← map_trim_comap hf]; rw [ae_map_iff (Measurable.of_comap_le le_rfl).aemeasurable hp]

Depends on / 依赖: Measurable, Measurable.of_comap_le, ae_map_iff, aemeasurable, le_rfl, map_trim_comap, of_comap_le
-/
lemma ae_map_iff_ae_trim {f : α -> β} (hf : Measurable f)
    {p : β -> Prop} (hp : MeasurableSet { x | p x }) :
    (forallᵐ y ∂μ.map f, p y) ↔ forallᵐ x ∂(μ.trim hf.comap_le), p (f x) := by
  rw [← map_trim_comap hf]; rw [ae_map_iff (Measurable.of_comap_le le_rfl).aemeasurable hp]

/--
lemma `trim_add` / 引理 `trim_add`

English:
lemma trim_add
  given: {ν : Measure α} (hm : m <= m0)
  statement: (μ + ν).trim hm = μ.trim hm + ν.trim hm
  proof: @Measure.ext _ m _ _ (fun s hs => by simp [trim_measurableSet_eq hm hs])

中文:
引理 trim_add
  条件: {ν : Measure α} (hm : m <= m0)
  结论: (μ + ν).trim hm = μ.trim hm + ν.trim hm
  证明: @Measure.ext _ m _ _ (fun s hs => by simp [trim_measurableSet_eq hm hs])

Depends on / 依赖: Measure, Measure.ext, trim_measurableSet_eq
-/
lemma trim_add {ν : Measure α} (hm : m <= m0) : (μ + ν).trim hm = μ.trim hm + ν.trim hm :=
  @Measure.ext _ m _ _ (fun s hs => by simp [trim_measurableSet_eq hm hs])

/--
theorem `measure_eq_zero_of_trim_eq_zero` / 定理 `measure_eq_zero_of_trim_eq_zero`

English:
theorem measure_eq_zero_of_trim_eq_zero
  given: (hm : m <= m0) (h : μ.trim hm s = 0)
  statement: μ s = 0
  proof: by
  grw [← nonpos_iff_eq_zero, ← h, le_trim hm]

中文:
定理 measure_eq_zero_of_trim_eq_zero
  条件: (hm : m <= m0) (h : μ.trim hm s = 0)
  结论: μ s = 0
  证明: by
  grw [← nonpos_iff_eq_zero, ← h, le_trim hm]

Depends on / 依赖: le_trim, nonpos_iff_eq_zero
-/
theorem measure_eq_zero_of_trim_eq_zero (hm : m <= m0) (h : μ.trim hm s = 0) : μ s = 0 := by
  grw [← nonpos_iff_eq_zero, ← h, le_trim hm]

/--
theorem `measure_trim_toMeasurable_eq_zero` / 定理 `measure_trim_toMeasurable_eq_zero`

English:
theorem measure_trim_toMeasurable_eq_zero
  given: {hm : m <= m0} (hs : μ.trim hm s = 0)
  proof: measure_eq_zero_of_trim_eq_zero hm (by rwa [@measure_toMeasurable _ m])

中文:
定理 measure_trim_toMeasurable_eq_zero
  条件: {hm : m <= m0} (hs : μ.trim hm s = 0)
  证明: measure_eq_zero_of_trim_eq_zero hm (by rwa [@measure_toMeasurable _ m])

Depends on / 依赖: measure_eq_zero_of_trim_eq_zero, measure_toMeasurable
-/
theorem measure_trim_toMeasurable_eq_zero {hm : m <= m0} (hs : μ.trim hm s = 0) :
    μ (@toMeasurable α m (μ.trim hm) s) = 0 :=
  measure_eq_zero_of_trim_eq_zero hm (by rwa [@measure_toMeasurable _ m])

/--
theorem `ae_of_ae_trim` / 定理 `ae_of_ae_trim`

English:
theorem ae_of_ae_trim
  given: (hm : m <= m0) {μ : Measure α} {P : α -> Prop} (h : forallᵐ x ∂μ.trim hm, P x)
  proof: measure_eq_zero_of_trim_eq_zero hm h

中文:
定理 ae_of_ae_trim
  条件: (hm : m <= m0) {μ : Measure α} {P : α -> 命题} (h : 对任意ᵐ x ∂μ.trim hm, P x)
  证明: measure_eq_zero_of_trim_eq_zero hm h

Depends on / 依赖: measure_eq_zero_of_trim_eq_zero
-/
theorem ae_of_ae_trim (hm : m <= m0) {μ : Measure α} {P : α -> Prop} (h : forallᵐ x ∂μ.trim hm, P x) :
    forallᵐ x ∂μ, P x :=
  measure_eq_zero_of_trim_eq_zero hm h

/--
theorem `ae_eq_of_ae_eq_trim` / 定理 `ae_eq_of_ae_eq_trim`

English:
theorem ae_eq_of_ae_eq_trim
  statement: {E} {hm : m <= m0} {f₁ f₂ : α -> E}
  proof: measure_eq_zero_of_trim_eq_zero hm h12

中文:
定理 ae_eq_of_ae_eq_trim
  结论: {E} {hm : m <= m0} {f₁ f₂ : α -> E}
  证明: measure_eq_zero_of_trim_eq_zero hm h12

Depends on / 依赖: measure_eq_zero_of_trim_eq_zero
-/
theorem ae_eq_of_ae_eq_trim {E} {hm : m <= m0} {f₁ f₂ : α -> E}
    (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂ :=
  measure_eq_zero_of_trim_eq_zero hm h12

/--
theorem `ae_le_of_ae_le_trim` / 定理 `ae_le_of_ae_le_trim`

English:
theorem ae_le_of_ae_le_trim
  statement: {E} [LE E] {hm : m <= m0} {f₁ f₂ : α -> E}
  proof: measure_eq_zero_of_trim_eq_zero hm h12

中文:
定理 ae_le_of_ae_le_trim
  结论: {E} [LE E] {hm : m <= m0} {f₁ f₂ : α -> E}
  证明: measure_eq_zero_of_trim_eq_zero hm h12

Depends on / 依赖: measure_eq_zero_of_trim_eq_zero
-/
theorem ae_le_of_ae_le_trim {E} [LE E] {hm : m <= m0} {f₁ f₂ : α -> E}
    (h12 : f₁ <=ᵐ[μ.trim hm] f₂) : f₁ <=ᵐ[μ] f₂ :=
  measure_eq_zero_of_trim_eq_zero hm h12

/--
theorem `trim_trim` / 定理 `trim_trim`

English:
theorem trim_trim
  given: {m₁ m₂ : MeasurableSpace α} {hm₁₂ : m₁ <= m₂} {hm₂ : m₂ <= m0}
  proof: by
  refine @Measure.ext _ m₁ _ _ (fun t ht => ?_)
  rw [trim_measurableSet_eq hm₁₂ ht]; rw [trim_measurableSet_eq (hm₁₂.trans hm₂) ht]; rw [trim_measurableSet_eq hm₂ (hm₁₂ t ht)]

中文:
定理 trim_trim
  条件: {m₁ m₂ : MeasurableSpace α} {hm₁₂ : m₁ <= m₂} {hm₂ : m₂ <= m0}
  证明: by
  refine @Measure.ext _ m₁ _ _ (fun t ht => ?_)
  rw [trim_measurableSet_eq hm₁₂ ht]; rw [trim_measurableSet_eq (hm₁₂.trans hm₂) ht]; rw [trim_measurableSet_eq hm₂ (hm₁₂ t ht)]

Depends on / 依赖: Measure, Measure.ext, trim_measurableSet_eq
-/
theorem trim_trim {m₁ m₂ : MeasurableSpace α} {hm₁₂ : m₁ <= m₂} {hm₂ : m₂ <= m0} :
    (μ.trim hm₂).trim hm₁₂ = μ.trim (hm₁₂.trans hm₂) := by
  refine @Measure.ext _ m₁ _ _ (fun t ht => ?_)
  rw [trim_measurableSet_eq hm₁₂ ht]; rw [trim_measurableSet_eq (hm₁₂.trans hm₂) ht]; rw [trim_measurableSet_eq hm₂ (hm₁₂ t ht)]

/--
theorem `restrict_trim` / 定理 `restrict_trim`

English:
theorem restrict_trim
  given: (hm : m <= m0) (μ : Measure α) (hs : @MeasurableSet α m s)
  proof: by
  refine @Measure.ext _ m _ _ (fun t ht => ?_)
  rw [@Measure.restrict_apply α m _ _ _ ht]; rw [trim_measurableSet_eq hm ht]; rw [Measure.restrict_apply (hm t ht)]; rw [trim_measurableSet_eq hm (@MeasurableSet.inter α m t s ht hs)]

中文:
定理 restrict_trim
  条件: (hm : m <= m0) (μ : Measure α) (hs : @MeasurableSet α m s)
  证明: by
  refine @Measure.ext _ m _ _ (fun t ht => ?_)
  rw [@Measure.restrict_apply α m _ _ _ ht]; rw [trim_measurableSet_eq hm ht]; rw [Measure.restrict_apply (hm t ht)]; rw [trim_measurableSet_eq hm (@MeasurableSet.inter α m t s ht hs)]

Depends on / 依赖: MeasurableSet, MeasurableSet.inter, Measure, Measure.ext, Measure.restrict_apply, restrict_apply, trim_measurableSet_eq
-/
theorem restrict_trim (hm : m <= m0) (μ : Measure α) (hs : @MeasurableSet α m s) :
    @Measure.restrict α m (μ.trim hm) s = (μ.restrict s).trim hm := by
  refine @Measure.ext _ m _ _ (fun t ht => ?_)
  rw [@Measure.restrict_apply α m _ _ _ ht]; rw [trim_measurableSet_eq hm ht]; rw [Measure.restrict_apply (hm t ht)]; rw [trim_measurableSet_eq hm (@MeasurableSet.inter α m t s ht hs)]

/--
theorem `measure_spanningSets_trim_lt_top` / 定理 `measure_spanningSets_trim_lt_top`

English:
theorem measure_spanningSets_trim_lt_top
  statement: (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
  proof: (le_trim hm).trans_lt (measure_spanningSets_lt_top (μ.trim hm) n)

中文:
定理 measure_spanningSets_trim_lt_top
  结论: (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
  证明: (le_trim hm).trans_lt (measure_spanningSets_lt_top (μ.trim hm) n)

Depends on / 依赖: le_trim, measure_spanningSets_lt_top, trans_lt
-/
theorem measure_spanningSets_trim_lt_top (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
    (n : Nat) :
    μ (spanningSets (μ.trim hm) n) < ⊤ :=
  (le_trim hm).trans_lt (measure_spanningSets_lt_top (μ.trim hm) n)

instance (hm : m <= m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (n : Nat) :
    IsFiniteMeasure (μ.restrict (spanningSets (μ.trim hm) n)) :=
  isFiniteMeasure_restrict.2 (measure_spanningSets_trim_lt_top hm μ n).ne

/--
Instance `isFiniteMeasure_trim` / 实例 `isFiniteMeasure_trim`

English:
instance isFiniteMeasure_trim
  signature: (hm : m <= m0) [IsFiniteMeasure μ]
  body: by
    rw [trim_measurableSet_eq hm (@MeasurableSet.univ _ m)]
    exact measure_lt_top _ _

中文:
实例 isFiniteMeasure_trim
  签名: (hm : m <= m0) [IsFiniteMeasure μ]
  定义体: by
    rw [trim_measurableSet_eq hm (@MeasurableSet.univ _ m)]
    exact measure_lt_top _ _

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, measure_lt_top, trim_measurableSet_eq
-/
instance isFiniteMeasure_trim (hm : m <= m0) [IsFiniteMeasure μ] : IsFiniteMeasure (μ.trim hm) where
  measure_univ_lt_top := by
    rw [trim_measurableSet_eq hm (@MeasurableSet.univ _ m)]
    exact measure_lt_top _ _

/--
theorem `sigmaFiniteTrim_mono` / 定理 `sigmaFiniteTrim_mono`

English:
theorem sigmaFiniteTrim_mono
  statement: {m m₂ m0 : MeasurableSpace α} {μ : Measure α} (hm : m <= m0)
  proof: by
  have : SigmaFinite ((μ.trim hm).trim hm₂) := by simpa [trim_trim]
  exact ⟨⟨
    { set := spanningSets ((μ.trim hm).trim hm₂)
      set_mem := fun _ => Set.mem_univ _
      finite := fun i => measure_spanningSets_trim_lt_top hm₂ (μ.trim hm) i
      spanning := iUnion_spanningSets _ }⟩⟩

中文:
定理 sigmaFiniteTrim_mono
  结论: {m m₂ m0 : MeasurableSpace α} {μ : Measure α} (hm : m <= m0)
  证明: by
  have : SigmaFinite ((μ.trim hm).trim hm₂) := by simpa [trim_trim]
  exact ⟨⟨
    { set := spanningSets ((μ.trim hm).trim hm₂)
      set_mem := fun _ => Set.mem_univ _
      finite := fun i => measure_spanningSets_trim_lt_top hm₂ (μ.trim hm) i
      spanning := iUnion_spanningSets _ }⟩⟩

Depends on / 依赖: Set.mem_univ, SigmaFinite, finite, iUnion_spanningSets, measure_spanningSets_trim_lt_top, mem_univ, set_mem, spanning, spanningSets, trim_trim
-/
theorem sigmaFiniteTrim_mono {m m₂ m0 : MeasurableSpace α} {μ : Measure α} (hm : m <= m0)
    (hm₂ : m₂ <= m) [SigmaFinite (μ.trim (hm₂.trans hm))] : SigmaFinite (μ.trim hm) := by
  have : SigmaFinite ((μ.trim hm).trim hm₂) := by simpa [trim_trim]
  exact ⟨⟨
    { set := spanningSets ((μ.trim hm).trim hm₂)
      set_mem := fun _ => Set.mem_univ _
      finite := fun i => measure_spanningSets_trim_lt_top hm₂ (μ.trim hm) i
      spanning := iUnion_spanningSets _ }⟩⟩

/--
lemma `SigmaFinite.of_trim` / 引理 `SigmaFinite.of_trim`

English:
lemma SigmaFinite.of_trim
  statement: {m m0 : MeasurableSpace α} {μ : Measure α} (hm : m <= m0)
  proof: by
  rw [← trim_eq_self (μ := μ)]
  exact sigmaFiniteTrim_mono le_rfl hm

中文:
引理 SigmaFinite.of_trim
  结论: {m m0 : MeasurableSpace α} {μ : Measure α} (hm : m <= m0)
  证明: by
  rw [← trim_eq_self (μ := μ)]
  exact sigmaFiniteTrim_mono le_rfl hm

Depends on / 依赖: le_rfl, sigmaFiniteTrim_mono, trim_eq_self
-/
lemma SigmaFinite.of_trim {m m0 : MeasurableSpace α} {μ : Measure α} (hm : m <= m0)
    [SigmaFinite (μ.trim hm)] : SigmaFinite μ := by
  rw [← trim_eq_self (μ := μ)]
  exact sigmaFiniteTrim_mono le_rfl hm

/--
theorem `sigmaFinite_trim_bot_iff` / 定理 `sigmaFinite_trim_bot_iff`

English:
theorem sigmaFinite_trim_bot_iff
  statement: SigmaFinite (μ.trim bot_le) ↔ IsFiniteMeasure μ
  proof: by
  rw [sigmaFinite_bot_iff]
  refine ⟨fun h => ⟨?_⟩, fun h => ⟨?_⟩⟩ <;> have h_univ := h.measure_univ_lt_top
  · rwa [trim_measurableSet_eq bot_le MeasurableSet.univ] at h_univ
  · rwa [trim_measurableSet_eq bot_le MeasurableSet.univ]

中文:
定理 sigmaFinite_trim_bot_iff
  结论: SigmaFinite (μ.trim bot_le) ↔ IsFiniteMeasure μ
  证明: by
  rw [sigmaFinite_bot_iff]
  refine ⟨fun h => ⟨?_⟩, fun h => ⟨?_⟩⟩ <;> have h_univ := h.measure_univ_lt_top
  · rwa [trim_measurableSet_eq bot_le MeasurableSet.univ] at h_univ
  · rwa [trim_measurableSet_eq bot_le MeasurableSet.univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, bot_le, h.measure_univ_lt_top, h_univ, measure_univ_lt_top, sigmaFinite_bot_iff, trim_measurableSet_eq
-/
theorem sigmaFinite_trim_bot_iff : SigmaFinite (μ.trim bot_le) ↔ IsFiniteMeasure μ := by
  rw [sigmaFinite_bot_iff]
  refine ⟨fun h => ⟨?_⟩, fun h => ⟨?_⟩⟩ <;> have h_univ := h.measure_univ_lt_top
  · rwa [trim_measurableSet_eq bot_le MeasurableSet.univ] at h_univ
  · rwa [trim_measurableSet_eq bot_le MeasurableSet.univ]

/--
lemma `Measure.AbsolutelyContinuous.trim` / 引理 `Measure.AbsolutelyContinuous.trim`

English:
lemma Measure.AbsolutelyContinuous.trim
  given: {ν : Measure α} (hμν : μ ≪ ν) (hm : m <= m0)
  proof: by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hsν => ?_)
  rw [trim_measurableSet_eq hm hs] at hsν ⊢
  exact hμν hsν

中文:
引理 Measure.AbsolutelyContinuous.trim
  条件: {ν : Measure α} (hμν : μ ≪ ν) (hm : m <= m0)
  证明: by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hsν => ?_)
  rw [trim_measurableSet_eq hm hs] at hsν ⊢
  exact hμν hsν

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.mk, trim_measurableSet_eq
-/
lemma Measure.AbsolutelyContinuous.trim {ν : Measure α} (hμν : μ ≪ ν) (hm : m <= m0) :
    μ.trim hm ≪ ν.trim hm := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hsν => ?_)
  rw [trim_measurableSet_eq hm hs] at hsν ⊢
  exact hμν hsν

/--
theorem `_root_.ae_eq_trim_of_measurable` / 定理 `_root_.ae_eq_trim_of_measurable`

English:
theorem _root_.ae_eq_trim_of_measurable
  statement: {α β} {m m0 : MeasurableSpace α} {μ : Measure α}
  proof: by
  rwa [Filter.EventuallyEq, ae_iff, trim_measurableSet_eq hm _]
  measurability

中文:
定理 _root_.ae_eq_trim_of_measurable
  结论: {α β} {m m0 : MeasurableSpace α} {μ : Measure α}
  证明: by
  rwa [Filter.EventuallyEq, ae_iff, trim_measurableSet_eq hm _]
  measurability

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, ae_iff, measurability, trim_measurableSet_eq
-/
theorem _root_.ae_eq_trim_of_measurable {α β} {m m0 : MeasurableSpace α} {μ : Measure α}
    [MeasurableSpace β] [MeasurableEq β]
    (hm : m <= m0) {f g : α -> β} (hf : Measurable[m] f) (hg : Measurable[m] g) (hfg : f =ᵐ[μ] g) :
    f =ᵐ[μ.trim hm] g := by
  rwa [Filter.EventuallyEq, ae_iff, trim_measurableSet_eq hm _]
  measurability

end MeasureTheory
