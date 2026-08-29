/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Composition of kernels

We define the composition `η ∘ₖ κ` of kernels `κ : Kernel α β` and `η : Kernel β γ`, which is
a kernel from `α` to `γ`.

## Main definitions

* `comp (η : Kernel β γ) (κ : Kernel α β) : Kernel α γ`: composition of 2 kernels.
  We define a notation `η ∘ₖ κ = comp η κ`.
  `∫⁻ c, g c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a)`
* The monoid structure on `Kernel α α` given by kernel composition.

## Main statements

* `lintegral_comp`: Lebesgue integral of a function against a composition of kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by composition.
* `pow_add_apply_eq_lintegral`: Chapman-Kolmogorov equations.

## Notation

* `η ∘ₖ κ = ProbabilityTheory.Kernel.comp η κ`

-/

@[expose] public section


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (η : Kernel β γ) (κ : Kernel α β)
  body: (κ a).bind η
  measurable' := (Measure.measurable_bind' η.measurable).comp κ.measurable

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ∘ₖ " => ProbabilityTheory.Kernel.comp

中文:
定义 comp
  签名: (η : 核 β γ) (κ : 核 α β)
  定义体: (κ a).bind η
  measurable' := (Measure.measurable_bind' η.measurable).comp κ.measurable

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ∘ₖ " => ProbabilityTheory.Kernel.comp
-/
noncomputable def comp (η : Kernel β γ) (κ : Kernel α β) : Kernel α γ where
  toFun a := (κ a).bind η
  measurable' := (Measure.measurable_bind' η.measurable).comp κ.measurable

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ∘ₖ " => ProbabilityTheory.Kernel.comp

/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (η : Kernel β γ) (κ : Kernel α β) (a : α)
  statement: (η ∘ₖ κ) a = (κ a).bind η
  proof: rfl

中文:
定理 comp_apply
  条件: (η : 核 β γ) (κ : 核 α β) (a : α)
  结论: (η ∘ₖ κ) a = (κ a).bind η
  证明: rfl
-/
theorem comp_apply (η : Kernel β γ) (κ : Kernel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η :=
  rfl

/--
theorem `comp_apply'` / 定理 `comp_apply'`

English:
theorem comp_apply'
  given: (η : Kernel β γ) (κ : Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s)
  proof: by
  rw [comp_apply]; rw [Measure.bind_apply hs (Kernel.aemeasurable _)]

中文:
定理 comp_apply'
  条件: (η : 核 β γ) (κ : 核 α β) (a : α) {s : 集合 γ} (hs : 可测集 s)
  证明: by
  rw [comp_apply]; rw [Measure.bind_apply hs (Kernel.aemeasurable _)]

Depends on / 依赖: Kernel, Kernel.aemeasurable, Measure, Measure.bind_apply, aemeasurable, bind_apply, comp_apply
-/
theorem comp_apply' (η : Kernel β γ) (κ : Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    (η ∘ₖ κ) a s = ∫⁻ b, η b s ∂κ a := by
  rw [comp_apply]; rw [Measure.bind_apply hs (Kernel.aemeasurable _)]

/--
theorem `comp_apply_univ_le` / 定理 `comp_apply_univ_le`

English:
theorem comp_apply_univ_le
  given: (κ : Kernel α β) (η : Kernel β γ) (a : α)
  proof: by
  rw [comp_apply' _ _ _ .univ]
  let Cη := η.bound
  calc
    ∫⁻ b, η b Set.univ ∂κ a <= ∫⁻ _, Cη ∂κ a :=
      lintegral_mono fun b => measure_le_bound η b Set.univ
    _ = Cη * κ a Set.univ := MeasureTheory.lintegral_const Cη
    _ = κ a Set.univ * Cη := mul_comm _ _

中文:
定理 comp_apply_univ_le
  条件: (κ : 核 α β) (η : 核 β γ) (a : α)
  证明: by
  rw [comp_apply' _ _ _ .univ]
  let Cη := η.bound
  calc
    ∫⁻ b, η b Set.univ ∂κ a <= ∫⁻ _, Cη ∂κ a :=
      lintegral_mono fun b => measure_le_bound η b Set.univ
    _ = Cη * κ a Set.univ := MeasureTheory.lintegral_const Cη
    _ = κ a Set.univ * Cη := mul_comm _ _

Depends on / 依赖: MeasureTheory, MeasureTheory.lintegral_const, Set.univ, comp_apply, lintegral_const, lintegral_mono, measure_le_bound, mul_comm
-/
theorem comp_apply_univ_le (κ : Kernel α β) (η : Kernel β γ) (a : α) :
    (η ∘ₖ κ) a Set.univ <= κ a Set.univ * η.bound := by
  rw [comp_apply' _ _ _ .univ]
  let Cη := η.bound
  calc
    ∫⁻ b, η b Set.univ ∂κ a <= ∫⁻ _, Cη ∂κ a :=
      lintegral_mono fun b => measure_le_bound η b Set.univ
    _ = Cη * κ a Set.univ := MeasureTheory.lintegral_const Cη
    _ = κ a Set.univ * Cη := mul_comm _ _

/--
lemma `zero_comp` / 引理 `zero_comp`

English:
lemma zero_comp
  given: (κ : Kernel α β)
  statement: (0 : Kernel β γ) ∘ₖ κ = 0
  proof: by
  ext; simp [comp_apply, FunLike.coe_zero]

中文:
引理 zero_comp
  条件: (κ : 核 α β)
  结论: (0 : 核 β γ) ∘ₖ κ = 0
  证明: by
  ext; simp [comp_apply, FunLike.coe_zero]
-/
@[simp] lemma zero_comp (κ : Kernel α β) : (0 : Kernel β γ) ∘ₖ κ = 0 := by
  ext; simp [comp_apply, FunLike.coe_zero]

/--
lemma `comp_zero` / 引理 `comp_zero`

English:
lemma comp_zero
  given: (κ : Kernel β γ)
  statement: κ ∘ₖ (0 : Kernel α β) = 0
  proof: by ext; simp [comp_apply]

中文:
引理 comp_zero
  条件: (κ : 核 β γ)
  结论: κ ∘ₖ (0 : 核 α β) = 0
  证明: by ext; simp [comp_apply]
-/
@[simp] lemma comp_zero (κ : Kernel β γ) : κ ∘ₖ (0 : Kernel α β) = 0 := by ext; simp [comp_apply]

/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  given: (κ : Kernel α β)
  statement: Kernel.id ∘ₖ κ = κ
  proof: by
  ext a s hs
  simpa [comp_apply' _ _ _ hs, id_apply, Measure.dirac_apply' _ hs]
    using lintegral_indicator_one hs

中文:
引理 id_comp
  条件: (κ : 核 α β)
  结论: 核.id ∘ₖ κ = κ
  证明: by
  ext a s hs
  simpa [comp_apply' _ _ _ hs, id_apply, Measure.dirac_apply' _ hs]
    using lintegral_indicator_one hs
-/
@[simp] lemma id_comp (κ : Kernel α β) : Kernel.id ∘ₖ κ = κ := by
  ext a s hs
  simpa [comp_apply' _ _ _ hs, id_apply, Measure.dirac_apply' _ hs]
    using lintegral_indicator_one hs

/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  given: (κ : Kernel β γ)
  statement: κ ∘ₖ Kernel.id = κ
  proof: by
  ext a s hs
  simp [comp_apply' _ _ _ hs, id_apply,
lintegral_dirac' a κ.measurable_coe hs]

中文:
引理 comp_id
  条件: (κ : 核 β γ)
  结论: κ ∘ₖ 核.id = κ
  证明: by
  ext a s hs
  simp [comp_apply' _ _ _ hs, id_apply,
lintegral_dirac' a κ.measurable_coe hs]
-/
@[simp] lemma comp_id (κ : Kernel β γ) : κ ∘ₖ Kernel.id = κ := by
  ext a s hs
  simp [comp_apply' _ _ _ hs, id_apply,
lintegral_dirac' a κ.measurable_coe hs]

section Ae

/-! ### `ae` filter of the composition -/

variable {κ : Kernel α β} {η : Kernel β γ} {a : α} {s : Set γ}

/--
theorem `ae_lt_top_of_comp_ne_top` / 定理 `ae_lt_top_of_comp_ne_top`

English:
theorem ae_lt_top_of_comp_ne_top
  given: (a : α) (hs : (η ∘ₖ κ) a s != ∞)
  statement: forallᵐ b ∂κ a, η b s < ∞
  proof: by
  have h : forallᵐ b ∂κ a, η b (toMeasurable ((η ∘ₖ κ) a) s) < ∞ := by
    refine ae_lt_top (Kernel.measurable_coe η (measurableSet_toMeasurable ..)) ?_
    rwa [← Kernel.comp_apply' _ _ _ (measurableSet_toMeasurable ..), measure_toMeasurable]
  filter_upwards [h] with b hb using (measure_mono (subset_toMeasurable _ _)).trans_lt hb

中文:
定理 ae_lt_top_of_comp_ne_top
  条件: (a : α) (hs : (η ∘ₖ κ) a s != ∞)
  结论: 对任意ᵐ b ∂κ a, η b s < ∞
  证明: by
  have h : forallᵐ b ∂κ a, η b (toMeasurable ((η ∘ₖ κ) a) s) < ∞ := by
    refine ae_lt_top (Kernel.measurable_coe η (measurableSet_toMeasurable ..)) ?_
    rwa [← Kernel.comp_apply' _ _ _ (measurableSet_toMeasurable ..), measure_toMeasurable]
  filter_upwards [h] with b hb using (measure_mono (subset_toMeasurable _ _)).trans_lt hb

Depends on / 依赖: Kernel, Kernel.comp_apply, Kernel.measurable_coe, ae_lt_top, comp_apply, filter_upwards, measurableSet_toMeasurable, measurable_coe, measure_mono, measure_toMeasurable, subset_toMeasurable, toMeasurable, trans_lt
-/
theorem ae_lt_top_of_comp_ne_top (a : α) (hs : (η ∘ₖ κ) a s != ∞) : forallᵐ b ∂κ a, η b s < ∞ := by
  have h : forallᵐ b ∂κ a, η b (toMeasurable ((η ∘ₖ κ) a) s) < ∞ := by
    refine ae_lt_top (Kernel.measurable_coe η (measurableSet_toMeasurable ..)) ?_
    rwa [← Kernel.comp_apply' _ _ _ (measurableSet_toMeasurable ..), measure_toMeasurable]
  filter_upwards [h] with b hb using (measure_mono (subset_toMeasurable _ _)).trans_lt hb

/--
theorem `comp_null` / 定理 `comp_null`

English:
theorem comp_null
  given: (a : α) (hs : MeasurableSet s)
  proof: by
  rw [comp_apply' _ _ _ hs]; rw [lintegral_eq_zero_iff (η.measurable_coe hs)]

中文:
定理 comp_null
  条件: (a : α) (hs : 可测集 s)
  证明: by
  rw [comp_apply' _ _ _ hs]; rw [lintegral_eq_zero_iff (η.measurable_coe hs)]

Depends on / 依赖: comp_apply, lintegral_eq_zero_iff, measurable_coe
-/
theorem comp_null (a : α) (hs : MeasurableSet s) :
    (η ∘ₖ κ) a s = 0 ↔ (fun y => η y s) =ᵐ[κ a] 0 := by
  rw [comp_apply' _ _ _ hs]; rw [lintegral_eq_zero_iff (η.measurable_coe hs)]

/--
theorem `ae_null_of_comp_null` / 定理 `ae_null_of_comp_null`

English:
theorem ae_null_of_comp_null
  given: (h : (η ∘ₖ κ) a s = 0)
  statement: (η · s) =ᵐ[κ a] 0
  proof: by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [comp_null a mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact ⟨Filter.EventuallyLE.trans_eq (ae_of_all _ fun _ => measure_mono hst) ht,
    ae_of_all _ fun _ => zero_le⟩

中文:
定理 ae_null_of_comp_null
  条件: (h : (η ∘ₖ κ) a s = 0)
  结论: (η · s) =ᵐ[κ a] 0
  证明: by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [comp_null a mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact ⟨Filter.EventuallyLE.trans_eq (ae_of_all _ fun _ => measure_mono hst) ht,
    ae_of_all _ fun _ => zero_le⟩

Depends on / 依赖: EventuallyLE, Filter, Filter.EventuallyLE.trans_eq, Filter.eventuallyLE_antisymm_iff, ae_of_all, comp_null, eventuallyLE_antisymm_iff, exists_measurable_superset_of_null, measure_mono, simp_rw, trans_eq, zero_le
-/
theorem ae_null_of_comp_null (h : (η ∘ₖ κ) a s = 0) : (η · s) =ᵐ[κ a] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [comp_null a mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact ⟨Filter.EventuallyLE.trans_eq (ae_of_all _ fun _ => measure_mono hst) ht,
    ae_of_all _ fun _ => zero_le⟩

variable {p : γ -> Prop}

/--
theorem `ae_ae_of_ae_comp` / 定理 `ae_ae_of_ae_comp`

English:
theorem ae_ae_of_ae_comp
  given: (h : forallᵐ z ∂(η ∘ₖ κ) a, p z)
  proof: ae_null_of_comp_null h

中文:
定理 ae_ae_of_ae_comp
  条件: (h : 对任意ᵐ z ∂(η ∘ₖ κ) a, p z)
  证明: ae_null_of_comp_null h

Depends on / 依赖: ae_null_of_comp_null
-/
theorem ae_ae_of_ae_comp (h : forallᵐ z ∂(η ∘ₖ κ) a, p z) :
    forallᵐ y ∂κ a, forallᵐ z ∂η y, p z := ae_null_of_comp_null h

/--
lemma `ae_comp_of_ae_ae` / 引理 `ae_comp_of_ae_ae`

English:
lemma ae_comp_of_ae_ae
  statement: (hp : MeasurableSet {z | p z})
  proof: by
  rwa [ae_iff, comp_null] at *
  exact hp.compl

中文:
引理 ae_comp_of_ae_ae
  结论: (hp : 可测集 {z | p z})
  证明: by
  rwa [ae_iff, comp_null] at *
  exact hp.compl

Depends on / 依赖: ae_iff, comp_null, hp.compl
-/
lemma ae_comp_of_ae_ae (hp : MeasurableSet {z | p z})
    (h : forallᵐ y ∂κ a, forallᵐ z ∂η y, p z) : forallᵐ z ∂(η ∘ₖ κ) a, p z := by
  rwa [ae_iff, comp_null] at *
  exact hp.compl

/--
lemma `ae_comp_iff` / 引理 `ae_comp_iff`

English:
lemma ae_comp_iff
  given: (hp : MeasurableSet {z | p z})
  proof: ⟨ae_ae_of_ae_comp, ae_comp_of_ae_ae hp⟩

中文:
引理 ae_comp_iff
  条件: (hp : 可测集 {z | p z})
  证明: ⟨ae_ae_of_ae_comp, ae_comp_of_ae_ae hp⟩

Depends on / 依赖: ae_ae_of_ae_comp, ae_comp_of_ae_ae
-/
lemma ae_comp_iff (hp : MeasurableSet {z | p z}) :
    (forallᵐ z ∂(η ∘ₖ κ) a, p z) ↔ forallᵐ y ∂κ a, forallᵐ z ∂η y, p z :=
  ⟨ae_ae_of_ae_comp, ae_comp_of_ae_ae hp⟩

end Ae

section Restrict

variable {κ : Kernel α β} {η : Kernel β γ}

/--
theorem `comp_restrict` / 定理 `comp_restrict`

English:
theorem comp_restrict
  given: {s : Set γ} (hs : MeasurableSet s)
  proof: by
  ext a t ht
  simp_rw [comp_apply' _ _ _ ht, restrict_apply' _ _ _ ht, comp_apply' _ _ _ (ht.inter hs)]

中文:
定理 comp_restrict
  条件: {s : 集合 γ} (hs : 可测集 s)
  证明: by
  ext a t ht
  simp_rw [comp_apply' _ _ _ ht, restrict_apply' _ _ _ ht, comp_apply' _ _ _ (ht.inter hs)]

Depends on / 依赖: comp_apply, ht.inter, restrict_apply, simp_rw
-/
theorem comp_restrict {s : Set γ} (hs : MeasurableSet s) :
    η.restrict hs ∘ₖ κ = (η ∘ₖ κ).restrict hs := by
  ext a t ht
  simp_rw [comp_apply' _ _ _ ht, restrict_apply' _ _ _ ht, comp_apply' _ _ _ (ht.inter hs)]

end Restrict

/--
theorem `lintegral_comp` / 定理 `lintegral_comp`

English:
theorem lintegral_comp
  statement: (η : Kernel β γ) (κ : Kernel α β) (a : α) {g : γ -> Real>=0∞}
  proof: by
  rw [comp_apply]; rw [Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]

中文:
定理 lintegral_comp
  结论: (η : 核 β γ) (κ : 核 α β) (a : α) {g : γ -> 实数>=0∞}
  证明: by
  rw [comp_apply]; rw [Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]

Depends on / 依赖: Kernel, Kernel.aemeasurable, Measure, Measure.lintegral_bind, aemeasurable, comp_apply, hg.aemeasurable, lintegral_bind
-/
theorem lintegral_comp (η : Kernel β γ) (κ : Kernel α β) (a : α) {g : γ -> Real>=0∞}
    (hg : Measurable g) : ∫⁻ c, g c ∂(η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂η b ∂κ a := by
  rw [comp_apply]; rw [Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: {δ : Type*} {mδ : MeasurableSpace δ} (ξ : Kernel γ δ)
  proof: by
  refine ext_fun fun a f hf => ?_
  simp_rw [lintegral_comp _ _ _ hf, lintegral_comp _ _ _ hf.lintegral_kernel]

中文:
定理 comp_assoc
  结论: {δ : 类型} {mδ : 可测空间 δ} (ξ : 核 γ δ)
  证明: by
  refine ext_fun fun a f hf => ?_
  simp_rw [lintegral_comp _ _ _ hf, lintegral_comp _ _ _ hf.lintegral_kernel]

Depends on / 依赖: ext_fun, hf.lintegral_kernel, lintegral_comp, lintegral_kernel, simp_rw
-/
theorem comp_assoc {δ : Type*} {mδ : MeasurableSpace δ} (ξ : Kernel γ δ)
    (η : Kernel β γ) (κ : Kernel α β) : ξ ∘ₖ η ∘ₖ κ = ξ ∘ₖ (η ∘ₖ κ) := by
  refine ext_fun fun a f hf => ?_
  simp_rw [lintegral_comp _ _ _ hf, lintegral_comp _ _ _ hf.lintegral_kernel]

/--
lemma `comp_discard'` / 引理 `comp_discard'`

English:
lemma comp_discard'
  given: (κ : Kernel α β)
  proof: by
  ext a s hs
  simp [comp_apply' _ _ _ hs, mul_comm]

@[simp]

中文:
引理 comp_discard'
  条件: (κ : 核 α β)
  证明: by
  ext a s hs
  simp [comp_apply' _ _ _ hs, mul_comm]

@[simp]

Depends on / 依赖: Measure, Measure.dirac, PUnit.unit
-/
lemma comp_discard' (κ : Kernel α β) :
    discard β ∘ₖ κ =
      { toFun a := κ a .univ • Measure.dirac PUnit.unit
        measurable' := (κ.measurable_coe .univ).smul_measure _ } := by
  ext a s hs
  simp [comp_apply' _ _ _ hs, mul_comm]

@[simp]
/--
lemma `comp_discard` / 引理 `comp_discard`

English:
lemma comp_discard
  given: (κ : Kernel α β) [IsMarkovKernel κ]
  statement: discard β ∘ₖ κ = discard α
  proof: by
  ext; simp [comp_discard']

@[simp]

中文:
引理 comp_discard
  条件: (κ : 核 α β) [是MarkovKernel κ]
  结论: discard β ∘ₖ κ = discard α
  证明: by
  ext; simp [comp_discard']

@[simp]

Depends on / 依赖: comp_discard
-/
lemma comp_discard (κ : Kernel α β) [IsMarkovKernel κ] : discard β ∘ₖ κ = discard α := by
  ext; simp [comp_discard']

@[simp]
/--
lemma `swap_copy` / 引理 `swap_copy`

English:
lemma swap_copy
  statement: (swap α α) ∘ₖ (copy α) = copy α
  proof: by
  ext a s hs
  rw [comp_apply]; rw [copy_apply]; rw [Measure.dirac_bind (Kernel.measurable _)]; rw [swap_apply' _ hs]; rw [Measure.dirac_apply' _ hs]
  congr

中文:
引理 swap_copy
  结论: (swap α α) ∘ₖ (copy α) = copy α
  证明: by
  ext a s hs
  rw [comp_apply]; rw [copy_apply]; rw [Measure.dirac_bind (Kernel.measurable _)]; rw [swap_apply' _ hs]; rw [Measure.dirac_apply' _ hs]
  congr

Depends on / 依赖: Kernel, Kernel.measurable, Measure, Measure.dirac_apply, Measure.dirac_bind, comp_apply, copy_apply, dirac_apply, dirac_bind, measurable, swap_apply
-/
lemma swap_copy : (swap α α) ∘ₖ (copy α) = copy α := by
  ext a s hs
  rw [comp_apply]; rw [copy_apply]; rw [Measure.dirac_bind (Kernel.measurable _)]; rw [swap_apply' _ hs]; rw [Measure.dirac_apply' _ hs]
  congr

/--
lemma `const_comp` / 引理 `const_comp`

English:
lemma const_comp
  given: (μ : Measure γ) (κ : Kernel α β)
  proof: by
  ext _ _ hs
  simp_rw [comp_apply' _ _ _ hs, const_apply, MeasureTheory.lintegral_const, Measure.smul_apply,
    smul_eq_mul, mul_comm]

@[simp]

中文:
引理 const_comp
  条件: (μ : 测度 γ) (κ : 核 α β)
  证明: by
  ext _ _ hs
  simp_rw [comp_apply' _ _ _ hs, const_apply, MeasureTheory.lintegral_const, Measure.smul_apply,
    smul_eq_mul, mul_comm]

@[simp]

Depends on / 依赖: Measure, Measure.smul_apply, MeasureTheory, MeasureTheory.lintegral_const, comp_apply, const_apply, lintegral_const, mul_comm, simp_rw, smul_apply, smul_eq_mul
-/
lemma const_comp (μ : Measure γ) (κ : Kernel α β) :
    const β μ ∘ₖ κ = fun a => (κ a) Set.univ • μ := by
  ext _ _ hs
  simp_rw [comp_apply' _ _ _ hs, const_apply, MeasureTheory.lintegral_const, Measure.smul_apply,
    smul_eq_mul, mul_comm]

@[simp]
/--
lemma `const_comp'` / 引理 `const_comp'`

English:
lemma const_comp'
  given: (μ : Measure γ) (κ : Kernel α β) [IsMarkovKernel κ]
  proof: by
  ext; simp_rw [const_comp, measure_univ, one_smul, const_apply]

中文:
引理 const_comp'
  条件: (μ : 测度 γ) (κ : 核 α β) [是MarkovKernel κ]
  证明: by
  ext; simp_rw [const_comp, measure_univ, one_smul, const_apply]

Depends on / 依赖: const_apply, const_comp, measure_univ, one_smul, simp_rw
-/
lemma const_comp' (μ : Measure γ) (κ : Kernel α β) [IsMarkovKernel κ] :
    const β μ ∘ₖ κ = const α μ := by
  ext; simp_rw [const_comp, measure_univ, one_smul, const_apply]

/--
lemma `comp_add_right` / 引理 `comp_add_right`

English:
lemma comp_add_right
  given: (μ κ : Kernel α β) (η : Kernel β γ)
  proof: by ext _ _ hs; simp [comp_apply' _ _ _ hs]

中文:
引理 comp_add_right
  条件: (μ κ : 核 α β) (η : 核 β γ)
  证明: by ext _ _ hs; simp [comp_apply' _ _ _ hs]

Depends on / 依赖: comp_apply
-/
lemma comp_add_right (μ κ : Kernel α β) (η : Kernel β γ) :
    η ∘ₖ (μ + κ) = η ∘ₖ μ + η ∘ₖ κ := by ext _ _ hs; simp [comp_apply' _ _ _ hs]

/--
lemma `comp_add_left` / 引理 `comp_add_left`

English:
lemma comp_add_left
  given: (μ : Kernel α β) (κ η : Kernel β γ)
  proof: by
  ext a s hs
  simp_rw [comp_apply' _ _ _ hs, add_apply, Measure.add_apply, comp_apply' _ _ _ hs,
    lintegral_add_left (Kernel.measurable_coe κ hs)]

中文:
引理 comp_add_left
  条件: (μ : 核 α β) (κ η : 核 β γ)
  证明: by
  ext a s hs
  simp_rw [comp_apply' _ _ _ hs, add_apply, Measure.add_apply, comp_apply' _ _ _ hs,
    lintegral_add_left (Kernel.measurable_coe κ hs)]

Depends on / 依赖: Kernel, Kernel.measurable_coe, Measure, Measure.add_apply, add_apply, comp_apply, lintegral_add_left, measurable_coe, simp_rw
-/
lemma comp_add_left (μ : Kernel α β) (κ η : Kernel β γ) :
    (κ + η) ∘ₖ μ = κ ∘ₖ μ + η ∘ₖ μ := by
  ext a s hs
  simp_rw [comp_apply' _ _ _ hs, add_apply, Measure.add_apply, comp_apply' _ _ _ hs,
    lintegral_add_left (Kernel.measurable_coe κ hs)]

/--
lemma `comp_sum_right` / 引理 `comp_sum_right`

English:
lemma comp_sum_right
  given: {ι : Type*} [Countable ι] (κ : ι -> Kernel α β) (η : Kernel β γ)
  proof: by
  ext _ _ hs
  simp_rw [sum_apply, comp_apply' _ _ _ hs, Measure.sum_apply _ hs, sum_apply,
    lintegral_sum_measure, comp_apply' _ _ _ hs]

中文:
引理 comp_sum_right
  条件: {ι : 类型} [可数 ι] (κ : ι -> 核 α β) (η : 核 β γ)
  证明: by
  ext _ _ hs
  simp_rw [sum_apply, comp_apply' _ _ _ hs, Measure.sum_apply _ hs, sum_apply,
    lintegral_sum_measure, comp_apply' _ _ _ hs]

Depends on / 依赖: Measure, Measure.sum_apply, comp_apply, lintegral_sum_measure, simp_rw, sum_apply
-/
lemma comp_sum_right {ι : Type*} [Countable ι] (κ : ι -> Kernel α β) (η : Kernel β γ) :
    η ∘ₖ Kernel.sum κ = Kernel.sum fun i => η ∘ₖ (κ i) := by
  ext _ _ hs
  simp_rw [sum_apply, comp_apply' _ _ _ hs, Measure.sum_apply _ hs, sum_apply,
    lintegral_sum_measure, comp_apply' _ _ _ hs]

/--
lemma `comp_sum_left` / 引理 `comp_sum_left`

English:
lemma comp_sum_left
  given: {ι : Type*} [Countable ι] (κ : Kernel α β) (η : ι -> Kernel β γ)
  proof: by
  ext _ _ hs
  simp_rw [sum_apply, comp_apply' _ _ _ hs, sum_apply, Measure.sum_apply _ hs,
    comp_apply' _ _ _ hs]
  rw [lintegral_tsum]
  exact fun _ => (Kernel.measurable_coe _ hs).aemeasurable

中文:
引理 comp_sum_left
  条件: {ι : 类型} [可数 ι] (κ : 核 α β) (η : ι -> 核 β γ)
  证明: by
  ext _ _ hs
  simp_rw [sum_apply, comp_apply' _ _ _ hs, sum_apply, Measure.sum_apply _ hs,
    comp_apply' _ _ _ hs]
  rw [lintegral_tsum]
  exact fun _ => (Kernel.measurable_coe _ hs).aemeasurable

Depends on / 依赖: Kernel, Kernel.measurable_coe, Measure, Measure.sum_apply, aemeasurable, comp_apply, lintegral_tsum, measurable_coe, simp_rw, sum_apply
-/
lemma comp_sum_left {ι : Type*} [Countable ι] (κ : Kernel α β) (η : ι -> Kernel β γ) :
    (Kernel.sum η) ∘ₖ κ = Kernel.sum (fun i => (η i) ∘ₖ κ) := by
  ext _ _ hs
  simp_rw [sum_apply, comp_apply' _ _ _ hs, sum_apply, Measure.sum_apply _ hs,
    comp_apply' _ _ _ hs]
  rw [lintegral_tsum]
  exact fun _ => (Kernel.measurable_coe _ hs).aemeasurable

/--
lemma `copy_comp_apply_prod` / 引理 `copy_comp_apply_prod`

English:
lemma copy_comp_apply_prod
  statement: (κ : Kernel α β) (a : α) {s t : Set β} (hs : MeasurableSet s)
  proof: by
  rw [comp_apply' _ _ _ <| hs.prod ht]
  simp_rw [copy_apply, Measure.dirac_apply' _ <| hs.prod ht, Set.indicator_prod_one]
  calc
  _ = ∫⁻ b, (s inter t).indicator 1 b ∂κ a := by
    congr with b
    simp [Set.inter_indicator_one]
_ = κ a (s inter t) := lintegral_indicator_one hs.inter ht

中文:
引理 copy_comp_apply_prod
  结论: (κ : 核 α β) (a : α) {s t : 集合 β} (hs : 可测集 s)
  证明: by
  rw [comp_apply' _ _ _ <| hs.prod ht]
  simp_rw [copy_apply, Measure.dirac_apply' _ <| hs.prod ht, Set.indicator_prod_one]
  calc
  _ = ∫⁻ b, (s inter t).indicator 1 b ∂κ a := by
    congr with b
    simp [Set.inter_indicator_one]
_ = κ a (s inter t) := lintegral_indicator_one hs.inter ht

Depends on / 依赖: Measure, Measure.dirac_apply, Set.indicator_prod_one, Set.inter_indicator_one, comp_apply, copy_apply, dirac_apply, hs.inter, hs.prod, indicator, indicator_prod_one, inter_indicator_one, lintegral_indicator_one, simp_rw
-/
lemma copy_comp_apply_prod (κ : Kernel α β) (a : α) {s t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : (copy β ∘ₖ κ) a (s ×ˢ t) = κ a (s inter t) := by
  rw [comp_apply' _ _ _ <| hs.prod ht]
  simp_rw [copy_apply, Measure.dirac_apply' _ <| hs.prod ht, Set.indicator_prod_one]
  calc
  _ = ∫⁻ b, (s inter t).indicator 1 b ∂κ a := by
    congr with b
    simp [Set.inter_indicator_one]
_ = κ a (s inter t) := lintegral_indicator_one hs.inter ht

/--
Instance `IsMarkovKernel.comp` / 实例 `IsMarkovKernel.comp`

English:
instance IsMarkovKernel.comp
  signature: (η : Kernel β γ) [IsMarkovKernel η] (κ : Kernel α β)
  body: by
    rw [comp_apply]
    constructor
    rw [Measure.bind_apply .univ η.aemeasurable]
    simp

中文:
实例 是MarkovKernel.comp
  签名: (η : 核 β γ) [是MarkovKernel η] (κ : 核 α β)
  定义体: by
    rw [comp_apply]
    constructor
    rw [Measure.bind_apply .univ η.aemeasurable]
    simp

Depends on / 依赖: Measure, Measure.bind_apply, aemeasurable, bind_apply, comp_apply
-/
instance IsMarkovKernel.comp (η : Kernel β γ) [IsMarkovKernel η] (κ : Kernel α β)
    [IsMarkovKernel κ] : IsMarkovKernel (η ∘ₖ κ) where
  isProbabilityMeasure a := by
    rw [comp_apply]
    constructor
    rw [Measure.bind_apply .univ η.aemeasurable]
    simp

/--
Instance `IsZeroOrMarkovKernel.comp` / 实例 `IsZeroOrMarkovKernel.comp`

English:
instance IsZeroOrMarkovKernel.comp
  signature: (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
  body: by
  obtain rfl | _ := eq_zero_or_isMarkovKernel κ <;> obtain rfl | _ := eq_zero_or_isMarkovKernel η
  all_goals simpa using by infer_instance

中文:
实例 是ZeroOrMarkovKernel.comp
  签名: (κ : 核 α β) [是ZeroOrMarkovKernel κ]
  定义体: by
  obtain rfl | _ := eq_zero_or_isMarkovKernel κ <;> obtain rfl | _ := eq_zero_or_isMarkovKernel η
  all_goals simpa using by infer_instance

Depends on / 依赖: all_goals, eq_zero_or_isMarkovKernel, infer_instance
-/
instance IsZeroOrMarkovKernel.comp (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
    (η : Kernel β γ) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (η ∘ₖ κ) := by
  obtain rfl | _ := eq_zero_or_isMarkovKernel κ <;> obtain rfl | _ := eq_zero_or_isMarkovKernel η
  all_goals simpa using by infer_instance

/--
Instance `IsFiniteKernel.comp` / 实例 `IsFiniteKernel.comp`

English:
instance IsFiniteKernel.comp
  signature: (η : Kernel β γ) [IsFiniteKernel η] (κ : Kernel α β)
  body: by
  refine ⟨⟨κ.bound * η.bound, ENNReal.mul_lt_top κ.bound_lt_top η.bound_lt_top, fun a => ?_⟩⟩
  calc (η ∘ₖ κ) a Set.univ
  _ <= κ a Set.univ * η.bound := comp_apply_univ_le κ η a
  _ <= κ.bound * η.bound := by gcongr; exact measure_le_bound κ a Set.univ

中文:
实例 是FiniteKernel.comp
  签名: (η : 核 β γ) [是FiniteKernel η] (κ : 核 α β)
  定义体: by
  refine ⟨⟨κ.bound * η.bound, ENNReal.mul_lt_top κ.bound_lt_top η.bound_lt_top, fun a => ?_⟩⟩
  calc (η ∘ₖ κ) a Set.univ
  _ <= κ a Set.univ * η.bound := comp_apply_univ_le κ η a
  _ <= κ.bound * η.bound := by gcongr; exact measure_le_bound κ a Set.univ

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, Set.univ, bound_lt_top, comp_apply_univ_le, measure_le_bound, mul_lt_top
-/
instance IsFiniteKernel.comp (η : Kernel β γ) [IsFiniteKernel η] (κ : Kernel α β)
    [IsFiniteKernel κ] : IsFiniteKernel (η ∘ₖ κ) := by
  refine ⟨⟨κ.bound * η.bound, ENNReal.mul_lt_top κ.bound_lt_top η.bound_lt_top, fun a => ?_⟩⟩
  calc (η ∘ₖ κ) a Set.univ
  _ <= κ a Set.univ * η.bound := comp_apply_univ_le κ η a
  _ <= κ.bound * η.bound := by gcongr; exact measure_le_bound κ a Set.univ

/--
Instance `IsSFiniteKernel.comp` / 实例 `IsSFiniteKernel.comp`

English:
instance IsSFiniteKernel.comp
  signature: (η : Kernel β γ) [IsSFiniteKernel η] (κ : Kernel α β)
  body: by
  simp_rw [← kernel_sum_seq κ, ← kernel_sum_seq η, comp_sum_left, comp_sum_right]
  infer_instance

中文:
实例 是SFiniteKernel.comp
  签名: (η : 核 β γ) [是SFiniteKernel η] (κ : 核 α β)
  定义体: by
  simp_rw [← kernel_sum_seq κ, ← kernel_sum_seq η, comp_sum_left, comp_sum_right]
  infer_instance

Depends on / 依赖: comp_sum_left, comp_sum_right, infer_instance, kernel_sum_seq, simp_rw
-/
instance IsSFiniteKernel.comp (η : Kernel β γ) [IsSFiniteKernel η] (κ : Kernel α β)
    [IsSFiniteKernel κ] : IsSFiniteKernel (η ∘ₖ κ) := by
  simp_rw [← kernel_sum_seq κ, ← kernel_sum_seq η, comp_sum_left, comp_sum_right]
  infer_instance

section Monoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (Kernel α α)
  body: η ∘ₖ κ
  mul_assoc ξ η κ := comp_assoc _ _ _
  one := Kernel.id
  one_mul := id_comp
  mul_one := comp_id

中文:
实例 :
  签名: 幺半群 (核 α α)
  定义体: η ∘ₖ κ
  mul_assoc ξ η κ := comp_assoc _ _ _
  one := Kernel.id
  one_mul := id_comp
  mul_one := comp_id
-/
noncomputable instance : Monoid (Kernel α α) where
  mul η κ := η ∘ₖ κ
  mul_assoc ξ η κ := comp_assoc _ _ _
  one := Kernel.id
  one_mul := id_comp
  mul_one := comp_id

/-! ### Chapman-Kolmogorov Equations -/

/--
theorem `pow_add` / 定理 `pow_add`

English:
theorem pow_add
  given: (κ : Kernel α α) (m n : Nat)
  proof: _root_.pow_add κ m n

中文:
定理 pow_add
  条件: (κ : 核 α α) (m n : 自然数)
  证明: _root_.pow_add κ m n

Depends on / 依赖: _root_, _root_.pow_add, pow_add
-/
theorem pow_add (κ : Kernel α α) (m n : Nat) :
    κ ^ (m + n) = (κ ^ m) ∘ₖ (κ ^ n) := _root_.pow_add κ m n

/--
theorem `pow_add_apply_eq_lintegral` / 定理 `pow_add_apply_eq_lintegral`

English:
theorem pow_add_apply_eq_lintegral
  statement: (κ : Kernel α α) (m n : Nat) (a : α) {s : Set α}
  proof: by
  rw [add_comm]; simp [pow_add, comp_apply' _ _ _ hs]

中文:
定理 pow_add_apply_eq_lintegral
  结论: (κ : 核 α α) (m n : 自然数) (a : α) {s : 集合 α}
  证明: by
  rw [add_comm]; simp [pow_add, comp_apply' _ _ _ hs]

Depends on / 依赖: add_comm, comp_apply, pow_add
-/
theorem pow_add_apply_eq_lintegral (κ : Kernel α α) (m n : Nat) (a : α) {s : Set α}
    (hs : MeasurableSet s) :
    (κ ^ (m + n)) a s = ∫⁻ b, (κ ^ n) b s ∂((κ ^ m) a) := by
  rw [add_comm]; simp [pow_add, comp_apply' _ _ _ hs]

/--
theorem `pow_succ_apply_eq_lintegral` / 定理 `pow_succ_apply_eq_lintegral`

English:
theorem pow_succ_apply_eq_lintegral
  statement: (κ : Kernel α α) (n : Nat) (a : α) {s : Set α}
  proof: by
  simpa using pow_add_apply_eq_lintegral _ n 1 _ hs

中文:
定理 pow_succ_apply_eq_lintegral
  结论: (κ : 核 α α) (n : 自然数) (a : α) {s : 集合 α}
  证明: by
  simpa using pow_add_apply_eq_lintegral _ n 1 _ hs

Depends on / 依赖: pow_add_apply_eq_lintegral
-/
theorem pow_succ_apply_eq_lintegral (κ : Kernel α α) (n : Nat) (a : α) {s : Set α}
    (hs : MeasurableSet s) :
    (κ ^ (n + 1)) a s = ∫⁻ b, κ b s ∂((κ ^ n) a) := by
  simpa using pow_add_apply_eq_lintegral _ n 1 _ hs

end Monoid

end Kernel
end ProbabilityTheory
