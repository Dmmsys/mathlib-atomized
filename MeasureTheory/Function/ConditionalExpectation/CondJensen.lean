/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin, Thomas Zhu
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.Continuous

/-!
# Conditional Jensen's Inequality

This file contains the conditional Jensen's inequality. We follow the proof in
[Hytonen_VanNeerven_Veraar_Wies_2016].

## Main Statement

* `Convex.condExp_mem `: in a Banach space `E` with a finite measure `μ`, if `f` lies in a
  closed convex set `s` a.e., then `μ[f | m]` lies in `s` a.e.
* `ConvexOn.map_condExp_le_univ`: in a Banach space `E` with a sigma finite measure `μ`, if
  `φ : E → ℝ` is a convex lower-semicontinuous function, then for any `f : α → E` such that `f` and
  `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ 𝔼[φ ∘ f | m]` a.e.

-/

public section

open MeasureTheory Function Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {α : Type*} {f : α → E} {φ : E → ℝ} {m mα : MeasurableSpace α} {μ : Measure α} {s : Set E}

/-
**Convex.condExp_mem_of_hereditarilyLindelofSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Convex.condExp_mem_of_hereditarilyLindelofSpace [IsFiniteMeasure μ]
    [HereditarilyLindelofSpace E] (hm : m ≤ mα) (hf_int : Integrable f μ) (hs : IsClosed s)
    (hc : Convex ℝ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) :
    ∀ᵐ a ∂μ, μ[f | m] a ∈ s := by
  obtain ⟨L, c, hLc⟩ := RCLike.iInter_countable_halfSpaces_eq (𝕜 := ℝ) hc hs
  simp_all only [← hLc, RCLike.re_to_real, mem_iInter, ae_all_iff]
  intro n
  have h1 := ContinuousLinearMap.comp_condExp_comm (m := m) hf_int (L n)
  have h2 := condExp_mono (m := m) ((L n).integrable_comp hf_int) (integrable_const (c n)) (hf n)
  filter_upwards [h1, h2] with a ha hb
  simp_all only [condExp_const, comp_apply]
  exact hb
/-
**Convex.condExp_mem_of_isFiniteMeasure** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Convex.condExp_mem_of_isFiniteMeasure [IsFiniteMeasure μ] (hm : m ≤ mα)
    (hf_int : Integrable f μ) (hs : IsClosed s) (hc : Convex ℝ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) :
    ∀ᵐ a ∂μ, μ[f | m] a ∈ s := by
  borelize E
  obtain ⟨t, ht, htt⟩ := hf_int.aestronglyMeasurable.isSeparable_ae_range
  let Y := (Submodule.span ℝ t).topologicalClosure
  have : CompleteSpace Y := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have : SecondCountableTopology Y := ht.span.closure.secondCountableTopology
  classical
  let fY : α → Y := fun a => if h : f a ∈ Y then ⟨f a, h⟩ else 0
  let fX : α → E := Y.subtypeL ∘ fY
  have lem0 : ∀ᵐ a ∂μ, f a ∈ Y := by
    filter_upwards [htt] with a ha using
      (Submodule.closure_subset_topologicalClosure_span t) (subset_closure ha)
  have lem1 : f =ᵐ[μ] fX := by
    filter_upwards [lem0] with a ha
    simp_all [fX, fY]
  have lem2 : ∀ᵐ a ∂μ, fY a ∈ Y.subtypeL ⁻¹' s := by
    filter_upwards [lem0, hf] with a ha hs
    simpa [fY, ha]
  have hfY_int : Integrable fY μ := by
    refine (hf_int.congr lem1).mono ?_ (by simp [fX])
    obtain ⟨g, hg1, hg2, hg3⟩ := hf_int.1.exists_stronglyMeasurable_range_subset
      ((Submodule.isClosed_topologicalClosure _).measurableSet) Nonempty.of_subtype lem0
    refine ⟨codRestrict g Y hg2, (hg1.measurable.codRestrict hg2).stronglyMeasurable, ?_⟩
    filter_upwards [hg3] with a ha
    have : g a ∈ Y := hg2 a
    simp_all [fY, codRestrict]
  have lem3 : μ[f | m] =ᵐ[μ] Y.subtypeL ∘ μ[fY | m] := calc
    _ =ᵐ[μ] μ[fX | m] := condExp_congr_ae lem1
    _ =ᵐ[μ] _ := (Y.subtypeL.comp_condExp_comm hfY_int).symm
  filter_upwards [(hc.linear_preimage Y.subtype).condExp_mem_of_hereditarilyLindelofSpace
    hm hfY_int (hs.preimage Y.subtypeL.continuous) lem2, lem3] with a ha hb
  simp_all

/-- If `f` lies in a closed convex set `s` a.e., then `μ[f | m]` lies in `s` a.e. -/
/-
**Convex.condExp_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Convex.condExp_mem (hm : m <= mα) [SigmaFinite (μ.trim hm)] (hf_int : Inte
grable f μ) (hs : IsClosed s) (hc : Convex Real s) (hf : forallᵐ a ∂μ, f a in s)
 : forallᵐ a ∂μ, μ[f | m] a in s
参数：hm : m <= mα；μ.trim hm；hf_int : Integrable f μ；hs : IsClosed s；hc : Convex Re
al s；hf : forallᵐ a ∂μ, f a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsCountablySpanning.null_of_forall_restrict_null`：∀ {α : Type u_2} {m0 :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {s : Set α} {C : Set (Set α)},
   IsCountablySpanning C → (∀ t ∈ C, M…
· 使用定理 `MeasureTheory.isCountablySpanning_spanningSets`：isCountablySpanning_span
ningSets (μ : Measure α) [SigmaFinite μ] : IsCountablySpanning (range (spanningS
ets μ))
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `MeasureTheory.condExp_restrict_ae_eq_restrict`：condExp_restrict_ae_eq_re
strict (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs_m : MeasurableSet[m] s) (hf_
int : Integrable f μ) : (μ.restrict…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.isFiniteMeasure_restrict`：isFiniteMeasure_restrict : IsFin
iteMeasure (μ.restrict s) ↔ μ s != ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.le_trim`：le_trim (hm : m <= m0) : μ s <= μ.trim hm s
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `_private.Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJense
n.0.Convex.condExp_mem_of_isFiniteMeasure`：∀ {E : Type u_1} [inst : NormedAddCom
mGroup E] [inst_1 : NormedSpace ℝ E] [CompleteSpace E] {α : Type u_2} {f : α → E
}   {m mα : MeasurableS…
· 使用定理 `MeasureTheory.Integrable.restrict`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]   [
inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If `f` lies in a closed convex set `s` a.e., then `μ[f | m]` lies in `s` a.e.
-/
lemma Convex.condExp_mem (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hf_int : Integrable f μ) (hs : IsClosed s) (hc : Convex ℝ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) :
    ∀ᵐ a ∂μ, μ[f | m] a ∈ s := by
  apply (isCountablySpanning_spanningSets (μ.trim hm)).null_of_forall_restrict_null <;>
    rintro - ⟨n, rfl⟩
  · exact hm _ (measurableSet_spanningSets (μ.trim hm) n)
  have h1 := condExp_restrict_ae_eq_restrict hm (measurableSet_spanningSets (μ.trim hm) n) hf_int
  have : IsFiniteMeasure (μ.restrict (spanningSets (μ.trim hm) n)) := isFiniteMeasure_restrict.2
    ((le_trim hm).trans_lt (measure_spanningSets_lt_top (μ.trim hm) n)).ne
  have h2 := hc.condExp_mem_of_isFiniteMeasure (μ := μ.restrict (spanningSets (μ.trim hm) n)) hm
    hf_int.restrict hs (ae_restrict_of_ae hf)
  filter_upwards [h1, h2] with a ha hb
  simp_all

/-- Conditional Jensen's inequality for hereditarily Lindelof Spaces. -/
/-
**ConvexOn.map_condExp_le_of_hereditarilyLindelofSpace** 是 Mathlib 中的一个引理，位于命名空间
 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conditional Jensen's inequality for hereditarily Lindelof Spaces.
-/
private lemma ConvexOn.map_condExp_le_of_hereditarilyLindelofSpace [IsFiniteMeasure μ]
    [HereditarilyLindelofSpace E] (hm : m ≤ mα) (hφ_cvx : ConvexOn ℝ s φ)
    (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) (hs : IsClosed s)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    ∀ᵐ a ∂μ, φ (μ[f | m] a) ≤ μ[φ ∘ f | m] a := by
  obtain ⟨L, c, hLc1, hLc2⟩ := hφ_cvx.real_sSup_of_nat_affine_eq hs hφ_cont
  have hp := ae_all_iff.2 fun i => (L i).comp_condExp_add_const_comm hm hf_int (c i)
  have hw : ∀ᵐ a ∂μ, ∀ i : ℕ, μ[(L i) ∘ f + const α (c i) | m] a ≤ μ[φ ∘ f | m] a := by
    refine ae_all_iff.2 fun i => condExp_mono ?_ hφ_int ?_
    · exact ((L i).integrable_comp hf_int).add (integrable_const (c i))
    · filter_upwards [hf] with a ha using hLc1 i ⟨f a, ha⟩
  filter_upwards [hp, hw, hφ_cvx.1.condExp_mem hm hf_int hs hf] with a hp hw hq
  rw [show φ (μ[f | m] a) = s.domRestrict φ ⟨μ[f | m] a, hq⟩ by simp, ← hLc2]
  simpa [iSup_congr hp] using! ciSup_le hw

/-- Conditional Jensen's inequality for finite measures. -/
/-
**ConvexOn.map_condExp_le_of_isFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conditional Jensen's inequality for finite measures.
-/
private theorem ConvexOn.map_condExp_le_of_isFiniteMeasure [IsFiniteMeasure μ] (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] := by
  borelize E
  obtain ⟨t, ht, htt⟩ := hf_int.aestronglyMeasurable.isSeparable_ae_range
  let Y := (Submodule.span ℝ t).topologicalClosure
  have : CompleteSpace Y := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have : SecondCountableTopology Y := ht.span.closure.secondCountableTopology
  let φY := φ ∘ Y.subtypeL
  classical
  let fY : α → Y := fun a => if h : f a ∈ Y then ⟨f a, h⟩ else 0
  let fX : α → E := Y.subtypeL ∘ fY
  have lem0 : ∀ᵐ a ∂μ, f a ∈ Y := by
    filter_upwards [htt] with a ha using
      (Submodule.closure_subset_topologicalClosure_span t) (subset_closure ha)
  have lem1 : f =ᵐ[μ] fX := by
    filter_upwards [lem0] with a ha
    simp_all [fX, fY]
  have hfY_int : Integrable fY μ := by
    refine (hf_int.congr lem1).mono ?_ (by simp [fX])
    obtain ⟨g, hg1, hg2, hg3⟩ := hf_int.1.exists_stronglyMeasurable_range_subset
      ((Submodule.isClosed_topologicalClosure _).measurableSet) Nonempty.of_subtype lem0
    refine ⟨codRestrict g Y hg2, (hg1.measurable.codRestrict hg2).stronglyMeasurable, ?_⟩
    filter_upwards [hg3] with a ha
    have : g a ∈ Y := hg2 a
    simp_all [fY, codRestrict]
  have lem2 : μ[f | m] =ᵐ[μ] Y.subtypeL ∘ μ[fY | m] := calc
    _ =ᵐ[μ] μ[fX | m] := condExp_congr_ae lem1
    _ =ᵐ[μ] _ := (Y.subtypeL.comp_condExp_comm hfY_int).symm
  have lem3 : φ ∘ f =ᵐ[μ] φY ∘ fY := by filter_upwards [lem1] with a ha; simp [φY, ha, fX]
  calc
    φ ∘ μ[f | m]
      =ᵐ[μ] φY ∘ μ[fY | m] := by filter_upwards [lem2] with a ha; simp [φY, ha]
    _ ≤ᵐ[μ] μ[φY ∘ fY | m] := by
      refine (hφ_cvx.comp_linearMap Y.subtype).map_condExp_le_of_hereditarilyLindelofSpace
        (s := Y.subtypeL ⁻¹' s) hm ?_ ?_ ?_ hfY_int (Integrable.congr hφ_int lem3)
      · exact hφ_cont.comp (by fun_prop) fun x => by
          #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
          (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
          goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem
          in the new canonicalizer; a minimization would help. The original proof was: `grind` -/
          simp
      · filter_upwards [lem0, hf] with a ha hb
        simp_all [fY]
      · exact hs.preimage Y.subtypeL.continuous
    _ =ᵐ[μ] μ[φ ∘ f | m] := condExp_congr_ae lem3.symm

/-- **Conditional Jensen's inequality**: in a Banach space `E` with a measure `μ` that is σ-finite
on a sub-σ-algebra `m`, if `φ : E → ℝ` is convex and lower-semicontinuous on a closed set `s`, then
for any `f : α → E` such that `f` and `φ ∘ f` are integrable, and `f` lies in `s` a.e., we have
`φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`. -/
/-
**ConvexOn.map_condExp_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.map_condExp_le (hm : m <= mα) [SigmaFinite (μ.trim hm)] (hφ_cvx :
 ConvexOn Real s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : forallᵐ a ∂μ, f 
a in s) (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f)
 μ) : φ ∘ μ[f | m] <=ᵐ[μ] μ[φ ∘ f | m]
参数：hm : m <= mα；μ.trim hm；hφ_cvx : ConvexOn Real s φ；hφ_cont : LowerSemicontinuo
usOn φ s；hf : forallᵐ a ∂μ, f a in s；hs : IsClosed s；hf_int : Integrable f μ；hφ_
int : Integrable (φ ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsCountablySpanning.null_of_forall_restrict_null`：∀ {α : Type u_2} {m0 :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {s : Set α} {C : Set (Set α)},
   IsCountablySpanning C → (∀ t ∈ C, M…
· 使用定理 `MeasureTheory.isCountablySpanning_spanningSets`：isCountablySpanning_span
ningSets (μ : Measure α) [SigmaFinite μ] : IsCountablySpanning (range (spanningS
ets μ))
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `MeasureTheory.condExp_restrict_ae_eq_restrict`：condExp_restrict_ae_eq_re
strict (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs_m : MeasurableSet[m] s) (hf_
int : Integrable f μ) : (μ.restrict…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.isFiniteMeasure_restrict`：isFiniteMeasure_restrict : IsFin
iteMeasure (μ.restrict s) ↔ μ s != ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.le_trim`：le_trim (hm : m <= m0) : μ s <= μ.trim hm s
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `_private.Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJense
n.0.ConvexOn.map_condExp_le_of_isFiniteMeasure`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] [CompleteSpace E] {α : Type u_2} {f : 
α → E}   {φ : E → ℝ} {m mα :…
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.Integrable.restrict`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]   [
inst_1 : ContinuousENor…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
**Conditional Jensen's inequality**: in a Banach space `E` with a measure `μ` th
at is σ-finite
on a sub-σ-algebra `m`, if `φ : E → ℝ` is convex and lower-semicontinuous on a c
losed set `s`, then
for any `f : α → E` such that `f` and `φ ∘ f` are integrable, and `f` lies in `s
` a.e., we have
`φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`.
-/
theorem ConvexOn.map_condExp_le (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] := by
  apply (isCountablySpanning_spanningSets (μ.trim hm)).null_of_forall_restrict_null <;>
    rintro - ⟨n, rfl⟩
  · exact hm _ (measurableSet_spanningSets (μ.trim hm) n)
  have h1 := condExp_restrict_ae_eq_restrict hm (measurableSet_spanningSets (μ.trim hm) n) hf_int
  have h2 := condExp_restrict_ae_eq_restrict hm (measurableSet_spanningSets (μ.trim hm) n) hφ_int
  have : IsFiniteMeasure (μ.restrict (spanningSets (μ.trim hm) n)) := isFiniteMeasure_restrict.2
    ((le_trim hm).trans_lt (measure_spanningSets_lt_top (μ.trim hm) n)).ne
  have h3 := hφ_cvx.map_condExp_le_of_isFiniteMeasure (μ := μ.restrict (spanningSets (μ.trim hm) n))
    hm hφ_cont (ae_restrict_of_ae hf) hs hf_int.restrict hφ_int.restrict
  filter_upwards [h1, h2, h3] with a ha hb hc
  simpa [← ha, ← hb]
/-
**ConvexOn.map_condExp_le_trim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.map_condExp_le_trim {mE : MeasurableSpace E} [BorelSpace E] (hm :
 m <= mα) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConvexOn Real s φ) (hφ_cont : Lowe
rSemicontinuousOn φ s) (hφ_meas : StronglyMeasurable φ) (hf : forallᵐ a ∂μ, f a 
in s) (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ
) : φ ∘ μ[f | m] <=ᵐ[μ.trim hm] μ[φ ∘ f | m]
参数：hm : m <= mα；μ.trim hm；hφ_cvx : ConvexOn Real s φ；hφ_cont : LowerSemicontinuo
usOn φ s；hφ_meas : StronglyMeasurable φ；hf : forallᵐ a ∂μ, f a in s；hs : IsClose
d s；hf_int : Integrable f μ；hφ_int : Integrable (φ ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_le_trim_iff`：ae_le_trim_iff (hm : m 
<= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : f <=ᵐ[μ.t
rim hm] g ↔ f <=ᵐ[μ] g
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `ConvexOn.map_condExp_le`：ConvexOn.map_condExp_le (hm : m <= mα) [SigmaFi
nite (μ.trim hm)] (hφ_cvx : ConvexOn Real s φ) (hφ_cont : LowerSemicontinuousOn 
φ s) (hf : fo…
-/
theorem ConvexOn.map_condExp_le_trim {mE : MeasurableSpace E} [BorelSpace E]
    (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s)
    (hφ_meas : StronglyMeasurable φ) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ.trim hm] μ[φ ∘ f | m] := by
  rw [StronglyMeasurable.ae_le_trim_iff hm (by fun_prop) (by fun_prop)]
  exact hφ_cvx.map_condExp_le hm hφ_cont hf hs hf_int hφ_int
/-
**ConcaveOn.condExp_map_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.condExp_map_le (hm : m <= mα) [SigmaFinite (μ.trim hm)] (hφ_cvx 
: ConcaveOn Real s φ) (hφ_cont : UpperSemicontinuousOn φ s) (hf : forallᵐ a ∂μ, 
f a in s) (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ 
f) μ) : μ[φ ∘ f | m] <=ᵐ[μ] φ ∘ μ[f | m]
参数：hm : m <= mα；μ.trim hm；hφ_cvx : ConcaveOn Real s φ；hφ_cont : UpperSemicontinu
ousOn φ s；hf : forallᵐ a ∂μ, f a in s；hs : IsClosed s；hf_int : Integrable f μ；hφ
_int : Integrable (φ ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.condExp_neg`：condExp_neg (f : α -> E) (m : MeasurableSpace
 α) : μ[-f | m] =ᵐ[μ] -μ[f | m]
· 使用定理 `ConvexOn.map_condExp_le`：ConvexOn.map_condExp_le (hm : m <= mα) [SigmaFi
nite (μ.trim hm)] (hφ_cvx : ConvexOn Real s φ) (hφ_cont : LowerSemicontinuousOn 
φ s) (hf : fo…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `UpperSemicontinuousOn.neg`：∀ {α : Type u_4} [inst : TopologicalSpace α] 
{β : Type u_5} {f : α → β} {s : Set α} [inst_1 : PartialOrder β]   [inst_2 : Add
CommGroup β] [I…
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem ConcaveOn.condExp_map_le (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConcaveOn ℝ s φ) (hφ_cont : UpperSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ] φ ∘ μ[f | m] := by
  filter_upwards [hφ_cvx.neg.map_condExp_le hm hφ_cont.neg hf hs hf_int hφ_int.neg,
    condExp_neg (φ ∘ f) m] with a h ha
  simp_all [Pi.neg_comp]
/-
**ConcaveOn.condExp_map_le_trim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.condExp_map_le_trim {mE : MeasurableSpace E} [BorelSpace E] (hm 
: m <= mα) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConcaveOn Real s φ) (hφ_cont : Up
perSemicontinuousOn φ s) (hφ_meas : StronglyMeasurable φ) (hf : forallᵐ a ∂μ, f 
a in s) (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f)
 μ) : μ[φ ∘ f | m] <=ᵐ[μ.trim hm] φ ∘ μ[f | m]
参数：hm : m <= mα；μ.trim hm；hφ_cvx : ConcaveOn Real s φ；hφ_cont : UpperSemicontinu
ousOn φ s；hφ_meas : StronglyMeasurable φ；hf : forallᵐ a ∂μ, f a in s；hs : IsClos
ed s；hf_int : Integrable f μ；hφ_int : Integrable (φ ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_le_trim_iff`：ae_le_trim_iff (hm : m 
<= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : f <=ᵐ[μ.t
rim hm] g ↔ f <=ᵐ[μ] g
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `ConcaveOn.condExp_map_le`：ConcaveOn.condExp_map_le (hm : m <= mα) [Sigma
Finite (μ.trim hm)] (hφ_cvx : ConcaveOn Real s φ) (hφ_cont : UpperSemicontinuous
On φ s) (hf : …
-/
theorem ConcaveOn.condExp_map_le_trim {mE : MeasurableSpace E} [BorelSpace E]
    (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConcaveOn ℝ s φ) (hφ_cont : UpperSemicontinuousOn φ s)
    (hφ_meas : StronglyMeasurable φ) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ.trim hm] φ ∘ μ[f | m] := by
  rw [StronglyMeasurable.ae_le_trim_iff hm (by fun_prop) (by fun_prop)]
  exact hφ_cvx.condExp_map_le hm hφ_cont hf hs hf_int hφ_int

/-- **Conditional Jensen's inequality**: in a Banach space `E` with a measure `μ` that is σ-finite
on a sub-σ-algebra `m`, if `φ : E → ℝ` is convex and lower-semicontinuous, then for any `f : α → E`
such that `f` and `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`. -/
/-
**ConvexOn.map_condExp_le_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.map_condExp_le_univ (hm : m <= mα) [SigmaFinite (μ.trim hm)] (hφ_
cvx : ConvexOn Real univ φ) (hφ_cont : LowerSemicontinuous φ) (hf_int : Integrab
le f μ) (hφ_int : Integrable (φ ∘ f) μ) : φ ∘ μ[f | m] <=ᵐ[μ] μ[φ ∘ f | m]
参数：hm : m <= mα；μ.trim hm；hφ_cvx : ConvexOn Real univ φ；hφ_cont : LowerSemiconti
nuous φ；hf_int : Integrable f μ；hφ_int : Integrable (φ ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.map_condExp_le`：ConvexOn.map_condExp_le (hm : m <= mα) [SigmaFi
nite (μ.trim hm)] (hφ_cvx : ConvexOn Real s φ) (hφ_cont : LowerSemicontinuousOn 
φ s) (hf : fo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lowerSemicontinuousOn_univ_iff`：lowerSemicontinuousOn_univ_iff : LowerSe
micontinuousOn f univ ↔ LowerSemicontinuous f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)

--- 原说明 ---
**Conditional Jensen's inequality**: in a Banach space `E` with a measure `μ` th
at is σ-finite
on a sub-σ-algebra `m`, if `φ : E → ℝ` is convex and lower-semicontinuous, then 
for any `f : α → E`
such that `f` and `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | 
m]`.
-/
theorem ConvexOn.map_condExp_le_univ (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  ConvexOn.map_condExp_le hm hφ_cvx (lowerSemicontinuousOn_univ_iff.2 hφ_cont) (by simp)
    isClosed_univ hf_int hφ_int
/-
**ConvexOn.map_condExp_le_trim_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.map_condExp_le_trim_univ {mE : MeasurableSpace E} [BorelSpace E] 
(hm : m <= mα) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConvexOn Real univ φ) (hφ_con
t : LowerSemicontinuous φ) (hφ_meas : StronglyMeasurable φ) (hf_int : Integrable
 f μ) (hφ_int : Integrable (φ ∘ f) μ) : φ ∘ μ[f | m] <=ᵐ[μ.trim hm] μ[φ ∘ f | m]
参数：hm : m <= mα；μ.trim hm；hφ_cvx : ConvexOn Real univ φ；hφ_cont : LowerSemiconti
nuous φ；hφ_meas : StronglyMeasurable φ；hf_int : Integrable f μ；hφ_int : Integrab
le (φ ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_le_trim_iff`：ae_le_trim_iff (hm : m 
<= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : f <=ᵐ[μ.t
rim hm] g ↔ f <=ᵐ[μ] g
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `ConvexOn.map_condExp_le_univ`：ConvexOn.map_condExp_le_univ (hm : m <= mα
) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConvexOn Real univ φ) (hφ_cont : LowerSemi
continuous φ) (hf_…
-/
theorem ConvexOn.map_condExp_le_trim_univ {mE : MeasurableSpace E} [BorelSpace E]
    (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hφ_meas : StronglyMeasurable φ) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ.trim hm] μ[φ ∘ f | m] := by
  rw [StronglyMeasurable.ae_le_trim_iff hm (by fun_prop) (by fun_prop)]
  exact hφ_cvx.map_condExp_le_univ hm hφ_cont hf_int hφ_int
/-
**ConcaveOn.condExp_map_le_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.condExp_map_le_univ (hm : m <= mα) [SigmaFinite (μ.trim hm)] (hφ
_cvx : ConcaveOn Real univ φ) (hφ_cont : UpperSemicontinuous φ) (hf_int : Integr
able f μ) (hφ_int : Integrable (φ ∘ f) μ) : μ[φ ∘ f | m] <=ᵐ[μ] φ ∘ μ[f | m]
参数：hm : m <= mα；μ.trim hm；hφ_cvx : ConcaveOn Real univ φ；hφ_cont : UpperSemicont
inuous φ；hf_int : Integrable f μ；hφ_int : Integrable (φ ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_neg`：condExp_neg (f : α -> E) (m : MeasurableSpace
 α) : μ[-f | m] =ᵐ[μ] -μ[f | m]
· 使用定理 `ConvexOn.map_condExp_le_univ`：ConvexOn.map_condExp_le_univ (hm : m <= mα
) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConvexOn Real univ φ) (hφ_cont : LowerSemi
continuous φ) (hf_…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `UpperSemicontinuous.neg`：∀ {α : Type u_4} [inst : TopologicalSpace α] {β
 : Type u_5} {f : α → β} [inst_1 : PartialOrder β]   [inst_2 : AddCommGroup β] [
IsOrderedAddM…
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem ConcaveOn.condExp_map_le_univ (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConcaveOn ℝ univ φ) (hφ_cont : UpperSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ] φ ∘ μ[f | m] := by
  filter_upwards [hφ_cvx.neg.map_condExp_le_univ hm hφ_cont.neg hf_int hφ_int.neg,
    condExp_neg (φ ∘ f) m] with a h ha
  simp_all [Pi.neg_comp]
/-
**ConcaveOn.condExp_map_le_trim_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.condExp_map_le_trim_univ {mE : MeasurableSpace E} [BorelSpace E]
 (hm : m <= mα) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConcaveOn Real univ φ) (hφ_c
ont : UpperSemicontinuous φ) (hφ_meas : StronglyMeasurable φ) (hf_int : Integrab
le f μ) (hφ_int : Integrable (φ ∘ f) μ) : μ[φ ∘ f | m] <=ᵐ[μ.trim hm] φ ∘ μ[f | 
m]
参数：hm : m <= mα；μ.trim hm；hφ_cvx : ConcaveOn Real univ φ；hφ_cont : UpperSemicont
inuous φ；hφ_meas : StronglyMeasurable φ；hf_int : Integrable f μ；hφ_int : Integra
ble (φ ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_le_trim_iff`：ae_le_trim_iff (hm : m 
<= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : f <=ᵐ[μ.t
rim hm] g ↔ f <=ᵐ[μ] g
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `ConcaveOn.condExp_map_le_univ`：ConcaveOn.condExp_map_le_univ (hm : m <= 
mα) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConcaveOn Real univ φ) (hφ_cont : UpperS
emicontinuous φ) (h…
-/
theorem ConcaveOn.condExp_map_le_trim_univ {mE : MeasurableSpace E} [BorelSpace E]
    (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConcaveOn ℝ univ φ) (hφ_cont : UpperSemicontinuous φ)
    (hφ_meas : StronglyMeasurable φ) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ.trim hm] φ ∘ μ[f | m] := by
  rw [StronglyMeasurable.ae_le_trim_iff hm (by fun_prop) (by fun_prop)]
  exact hφ_cvx.condExp_map_le_univ hm hφ_cont hf_int hφ_int

/-- In a Banach space `E` with a measure `μ`, then for any `f : α → E`, we have
`‖𝔼[f | m]‖ ≤ᵐ[μ] 𝔼[‖f‖ | m]`. -/
/-
**norm_condExp_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_condExp_le (f : α -> E) : (‖μ[f | m] ·‖) <=ᵐ[μ] μ[(‖f ·‖) | m]
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Filter.EventuallyLE.refl`：∀ {α : Type u} {β : Type v} [inst : Preorder β
] (l : Filter α) (f : α → β), f ≤ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用引理 `MeasureTheory.condExp_nonneg`：condExp_nonneg (hf : 0 <=ᵐ[μ] f) : 0 <=ᵐ[μ
] μ[f | m]
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ConvexOn.map_condExp_le_univ`：ConvexOn.map_condExp_le_univ (hm : m <= mα
) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConvexOn Real univ φ) (hφ_cont : LowerSemi
continuous φ) (hf_…
· 使用定理 `convexOn_univ_norm`：convexOn_univ_norm : ConvexOn Real univ (norm : E ->
 Real)
· 使用定理 `Continuous.lowerSemicontinuous`：Continuous.lowerSemicontinuous {f : α ->
 γ} (h : Continuous f) : LowerSemicontinuous f
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…

--- 原说明 ---
In a Banach space `E` with a measure `μ`, then for any `f : α → E`, we have
`‖𝔼[f | m]‖ ≤ᵐ[μ] 𝔼[‖f‖ | m]`.
-/
theorem norm_condExp_le (f : α → E) : (‖μ[f | m] ·‖) ≤ᵐ[μ] μ[(‖f ·‖) | m] := by
  by_cases! hm : ¬ m ≤ mα
  · simp [condExp_of_not_le hm]; aesop
  by_cases! hμm : ¬ SigmaFinite (μ.trim hm)
  · simp [condExp_of_not_sigmaFinite hm hμm]; aesop
  by_cases! hf_int : ¬ Integrable f μ
  · simp only [condExp_of_not_integrable hf_int, Pi.zero_apply, norm_zero]
    apply condExp_nonneg
    filter_upwards with a; positivity
  exact convexOn_univ_norm.map_condExp_le_univ hm continuous_norm.lowerSemicontinuous hf_int
    hf_int.norm
/-
**Integrable.norm_condExp_rpow_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Integrable.norm_condExp_rpow_le {p : Real} (hp : 1 <= p) (hfint : Integrab
le (fun x => ‖f x‖ ^ p) μ) : (‖μ[f | m] ·‖ ^ p) <=ᵐ[μ] μ[(‖f ·‖ ^ p) | m]
参数：hp : 1 <= p；hfint : Integrable (fun x => ‖f x‖ ^ p) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 71 条，此处仅展示前 30 条）
-/
theorem Integrable.norm_condExp_rpow_le {p : ℝ} (hp : 1 ≤ p)
    (hfint : Integrable (fun x => ‖f x‖ ^ p) μ) :
    (‖μ[f | m] ·‖ ^ p) ≤ᵐ[μ] μ[(‖f ·‖ ^ p) | m] := by
  have hp' : 0 < p := by linarith
  by_cases! hm : ¬ m ≤ mα
  · simp [condExp_of_not_le hm, Real.zero_rpow hp'.ne.symm]; aesop
  by_cases! hμm : ¬ SigmaFinite (μ.trim hm)
  · simp [condExp_of_not_sigmaFinite hm hμm, Real.zero_rpow hp'.ne.symm]; aesop
  by_cases! hf_int : ¬ Integrable f μ
  · simp only [condExp_of_not_integrable hf_int, Pi.zero_apply, norm_zero,
      Real.zero_rpow hp'.ne.symm]
    apply condExp_nonneg
    filter_upwards with a; positivity
  have hl := (Real.continuous_rpow_const hp'.le).lowerSemicontinuous.lowerSemicontinuousOn (Ici 0)
  have := (convexOn_rpow hp).map_condExp_le hm hl (by simp) isClosed_Ici hf_int.norm hfint
  filter_upwards [norm_condExp_le f, this] with a ha hb
  exact (Real.rpow_le_rpow (norm_nonneg _) ha hp'.le).trans hb

/-- **Conditional Jensen's inequality**: in a finite dimensional Banach space `E` with a measure
`μ` that is σ-finite on a sub-σ-algebra `m`, if `φ : E → ℝ` is convex, then for any `f : α → E` such
that `f` and `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`. -/
/-
**ConvexOn.map_condExp_le_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.map_condExp_le_of_finiteDimensional [FiniteDimensional Real E] (h
m : m <= mα) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConvexOn Real univ φ) (hf_int :
 Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) : φ ∘ μ[f | m] <=ᵐ[μ] μ[φ ∘ f |
 m]
参数：hm : m <= mα；μ.trim hm；hφ_cvx : ConvexOn Real univ φ；hf_int : Integrable f μ；
hφ_int : Integrable (φ ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.map_condExp_le_univ`：ConvexOn.map_condExp_le_univ (hm : m <= mα
) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConvexOn Real univ φ) (hφ_cont : LowerSemi
continuous φ) (hf_…
· 使用定理 `Continuous.lowerSemicontinuous`：Continuous.lowerSemicontinuous {f : α ->
 γ} (h : Continuous f) : LowerSemicontinuous f
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ConvexOn.continuousOn`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [i
nst_1 : NormedSpace ℝ E] {C : Set E} {f : E → ℝ}   [FiniteDimensional ℝ E], IsOp
en C → Conv…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ

--- 原说明 ---
**Conditional Jensen's inequality**: in a finite dimensional Banach space `E` wi
th a measure
`μ` that is σ-finite on a sub-σ-algebra `m`, if `φ : E → ℝ` is convex, then for 
any `f : α → E` such
that `f` and `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`.
-/
theorem ConvexOn.map_condExp_le_of_finiteDimensional [FiniteDimensional ℝ E] (hm : m ≤ mα)
    [SigmaFinite (μ.trim hm)] (hφ_cvx : ConvexOn ℝ univ φ) (hf_int : Integrable f μ)
    (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  hφ_cvx.map_condExp_le_univ hm
    (continuousOn_univ.1 (hφ_cvx.continuousOn isOpen_univ)).lowerSemicontinuous hf_int hφ_int
/-
**ConcaveOn.condExp_map_le_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.condExp_map_le_of_finiteDimensional [FiniteDimensional Real E] (
hm : m <= mα) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConcaveOn Real univ φ) (hf_int
 : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) : μ[φ ∘ f | m] <=ᵐ[μ] φ ∘ μ[f
 | m]
参数：hm : m <= mα；μ.trim hm；hφ_cvx : ConcaveOn Real univ φ；hf_int : Integrable f μ
；hφ_int : Integrable (φ ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_neg`：condExp_neg (f : α -> E) (m : MeasurableSpace
 α) : μ[-f | m] =ᵐ[μ] -μ[f | m]
· 使用定理 `ConvexOn.map_condExp_le_of_finiteDimensional`：ConvexOn.map_condExp_le_of
_finiteDimensional [FiniteDimensional Real E] (hm : m <= mα) [SigmaFinite (μ.tri
m hm)] (hφ_cvx : ConvexOn Real uni…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem ConcaveOn.condExp_map_le_of_finiteDimensional [FiniteDimensional ℝ E] (hm : m ≤ mα)
    [SigmaFinite (μ.trim hm)] (hφ_cvx : ConcaveOn ℝ univ φ) (hf_int : Integrable f μ)
    (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ] φ ∘ μ[f | m] := by
  filter_upwards [hφ_cvx.neg.map_condExp_le_of_finiteDimensional hm hf_int hφ_int.neg,
    condExp_neg (φ ∘ f) m] with a h ha
  simp_all [Pi.neg_comp]
