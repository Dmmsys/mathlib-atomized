/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!

# Conditional expectation of indicator functions

This file proves some results about the conditional expectation of an indicator function and
as a corollary, also proves several results about the behaviour of the conditional expectation on
a restricted measure.

## Main result

* `MeasureTheory.condExp_indicator`: If `s` is an `m`-measurable set, then the conditional
  expectation of the indicator function of `s` is almost everywhere equal to the indicator
  of `s` of the conditional expectation. Namely, `𝔼[s.indicator f | m] = s.indicator 𝔼[f | m]` a.e.

-/

public section


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α E : Type*} {m m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure α} {f : α → E} {s : Set α}

/-
**MeasureTheory.condExp_ae_eq_restrict_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：condExp_ae_eq_restrict_zero (hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restric
t s] 0) : μ[f | m] =ᵐ[μ.restrict s] 0
参数：hs : MeasurableSet[m] s；hf : f =ᵐ[μ.restrict s] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.restrict_trim`：restrict_trim (hm : m <= m0) (μ : Measure α
) (hs : @MeasurableSet α m s) : @Measure.restrict α m (μ.trim hm) s = (μ.restric
t s).trim hm
· 使用定理 `MeasureTheory.Restrict.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} (μ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ] (s : Set α),  
 MeasureTheory.SigmaFini…
· 使用定理 `MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'`：ae_eq_of_f
orall_setIntegral_eq_of_sigmaFinite' (hm : m <= m0) [SigmaFinite (μ.trim hm)] {f
 g : α -> F'} (hf_int_finite : forall s, Measurabl…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasureTheory.setIntegral_condExp`：setIntegral_condExp (hm : m <= m₀) [S
igmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in
 s, (μ[f | m]) x ∂μ = ∫…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.stronglyMeasurable_zero`：∀ {α : Type u_1} {β : Type u_2} {
x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Zero β],   MeasureT
heory.StronglyMeasurable 0
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
-/
theorem condExp_ae_eq_restrict_zero (hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restrict s] 0) :
    μ[f | m] =ᵐ[μ.restrict s] 0 := by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  have : SigmaFinite (μ.trim hm) := hμm
  have : SigmaFinite ((μ.restrict s).trim hm) := by
    rw [← restrict_trim hm _ hs]
    exact Restrict.sigmaFinite _ s
  by_cases hf_int : Integrable f μ
  swap; · rw [condExp_of_not_integrable hf_int]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm ?_ ?_ ?_ ?_ ?_
  · exact fun t _ _ => integrable_condExp.integrableOn.integrableOn
  · exact fun t _ _ => (integrable_zero _ _ _).integrableOn
  · intro t ht _
    rw [Measure.restrict_restrict (hm _ ht), setIntegral_condExp hm hf_int (ht.inter hs), ←
      Measure.restrict_restrict (hm _ ht)]
    refine setIntegral_congr_ae (hm _ ht) ?_
    filter_upwards [hf] with x hx _ using hx
  · exact stronglyMeasurable_condExp.aestronglyMeasurable
  · exact stronglyMeasurable_zero.aestronglyMeasurable

/-- Auxiliary lemma for `condExp_indicator`. -/
/-
**MeasureTheory.condExp_indicator_aux** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_indicator_aux (hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restrict sᶜ] 
0) : μ[s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m])
参数：hs : MeasurableSet[m] s；hf : f =ᵐ[μ.restrict sᶜ] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `indicator_ae_eq_of_restrict_compl_ae_eq_zero`：indicator_ae_eq_of_restric
t_compl_ae_eq_zero (hs : MeasurableSet s) (hf : f =ᵐ[μ.restrict sᶜ] 0) : s.indic
ator f =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_ae_eq_restrict_zero`：condExp_ae_eq_restrict_zero (
hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restrict s] 0) : μ[f | m] =ᵐ[μ.restrict s]
 0
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
· 使用定理 `Set.indicator_zero'`：∀ {α : Type u_1} (M : Type u_3) [inst : Zero M] {s 
: Set α}, s.indicator 0 = 0
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f

--- 原说明 ---
Auxiliary lemma for `condExp_indicator`.
-/
theorem condExp_indicator_aux (hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    μ[s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m]) := by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condExp_of_not_le hm, Set.indicator_zero']; rfl
  have hsf_zero : ∀ g : α → E, g =ᵐ[μ.restrict sᶜ] 0 → s.indicator g =ᵐ[μ] g := fun g =>
    indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs)
  refine ((hsf_zero (μ[f | m]) (condExp_ae_eq_restrict_zero hs.compl hf)).trans ?_).symm
  exact condExp_congr_ae (hsf_zero f hf).symm

/-- The conditional expectation of the indicator of a function over an `m`-measurable set with
respect to the σ-algebra `m` is a.e. equal to the indicator of the conditional expectation. -/
/-
**MeasureTheory.condExp_indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_indicator (hf_int : Integrable f μ) (hs : MeasurableSet[m] s) : μ[
s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m])
参数：hf_int : Integrable f μ；hs : MeasurableSet[m] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_self_add_compl`：∀ {α : Type u_1} {M : Type u_4} [inst : Ad
dZeroClass M] (s : Set α) (f : α → M), s.indicator f + sᶜ.indicator f = f
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.condExp_add`：condExp_add (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m]
· 使用定理 `MeasureTheory.Integrable.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {mα
 : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topolo
gicalSpace ε'] [inst_1 :…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `Set.indicator_add'`：∀ {α : Type u_1} {M : Type u_4} [inst : AddZeroClass
 M] (s : Set α) (f g : α → M),   s.indicator (f + g) = s.indicator f + s.indicat
or g
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_indicator_aux`：condExp_indicator_aux (hs : Measura
bleSet[m] s) (hf : f =ᵐ[μ.restrict sᶜ] 0) : μ[s.indicator f | m] =ᵐ[μ] s.indicat
or (μ[f | m])
· 使用定理 `indicator_ae_eq_restrict_compl`：indicator_ae_eq_restrict_compl (hs : Mea
surableSet s) : indicator s f =ᵐ[μ.restrict sᶜ] 0
· 使用定理 `Set.indicator_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 (s t : Set α) (f : α → M),   s.indicator (t.indicator f) = (s ∩ t).indicator f
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.inter_compl_self`：inter_compl_self (s : Set α) : s inter sᶜ = ∅
· 使用定理 `Set.indicator_empty'`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f
 : α → M), ∅.indicator f = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The conditional expectation of the indicator of a function over an `m`-measurabl
e set with
respect to the σ-algebra `m` is a.e. equal to the indicator of the conditional e
xpectation.
-/
theorem condExp_indicator (hf_int : Integrable f μ) (hs : MeasurableSet[m] s) :
    μ[s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m]) := by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condExp_of_not_le hm, Set.indicator_zero']; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm, Set.indicator_zero']; rfl
  have : SigmaFinite (μ.trim hm) := hμm
  -- use `have` to perform what should be the first calc step because of an error I don't
  -- understand
  have : s.indicator (μ[f | m]) =ᵐ[μ] s.indicator (μ[s.indicator f + sᶜ.indicator f | m]) := by
    rw [Set.indicator_self_add_compl s f]
  refine (this.trans ?_).symm
  calc
    s.indicator (μ[s.indicator f + sᶜ.indicator f | m]) =ᵐ[μ]
        s.indicator (μ[s.indicator f | m] + μ[sᶜ.indicator f | m]) := by
      filter_upwards [condExp_add (hf_int.indicator (hm _ hs)) (hf_int.indicator (hm _ hs.compl)) m]
        with x hx
      classical rw [Set.indicator_apply, Set.indicator_apply, hx]
    _ = s.indicator (μ[s.indicator f | m]) + s.indicator (μ[sᶜ.indicator f | m]) :=
      (s.indicator_add' _ _)
    _ =ᵐ[μ] s.indicator (μ[s.indicator f | m]) +
        s.indicator (sᶜ.indicator (μ[sᶜ.indicator f | m])) := by
      refine Filter.EventuallyEq.rfl.add ?_
      have : sᶜ.indicator (μ[sᶜ.indicator f | m]) =ᵐ[μ] μ[sᶜ.indicator f | m] := by
        refine (condExp_indicator_aux hs.compl ?_).symm.trans ?_
        · exact indicator_ae_eq_restrict_compl (hm _ hs.compl)
        · rw [Set.indicator_indicator, Set.inter_self]
      filter_upwards [this] with x hx
      by_cases hxs : x ∈ s
      · simp only [hx, hxs, Set.indicator_of_mem]
      · simp only [hxs, Set.indicator_of_notMem, not_false_iff]
    _ =ᵐ[μ] s.indicator (μ[s.indicator f | m]) := by
      rw [Set.indicator_indicator, Set.inter_compl_self, Set.indicator_empty', add_zero]
    _ =ᵐ[μ] μ[s.indicator f | m] := by
      refine (condExp_indicator_aux hs ?_).symm.trans ?_
      · exact indicator_ae_eq_restrict_compl (hm _ hs)
      · rw [Set.indicator_indicator, Set.inter_self]
/-
**MeasureTheory.condExp_restrict_ae_eq_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：condExp_restrict_ae_eq_restrict (hm : m <= m0) [SigmaFinite (μ.trim hm)] (
hs_m : MeasurableSet[m] s) (hf_int : Integrable f μ) : (μ.restrict s)[f | m] =ᵐ[
μ.restrict s] μ[f | m]
参数：hm : m <= m0；μ.trim hm；hs_m : MeasurableSet[m] s；hf_int : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.restrict_trim`：restrict_trim (hm : m <= m0) (μ : Measure α
) (hs : @MeasurableSet α m s) : @Measure.restrict α m (μ.trim hm) s = (μ.restric
t s).trim hm
· 使用定理 `MeasureTheory.Restrict.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} (μ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ] (s : Set α),  
 MeasureTheory.SigmaFini…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ae_eq_restrict_iff_indicator_ae_eq`：ae_eq_restrict_iff_indicator_ae_eq {
g : α -> β} (hs : MeasurableSet s) : f =ᵐ[μ.restrict s] g ↔ s.indicator f =ᵐ[μ] 
s.indicator g
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`：ae_eq_condExp_of_f
orall_setIntegral_eq (hm : m <= m₀) [SigmaFinite (μ.trim hm)] {f g : α -> E} (hf
 : Integrable f μ) (hg_int_finite : forall…
· 使用定理 `MeasureTheory.Integrable.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {mα
 : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topolo
gicalSpace ε'] [inst_1 :…
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `Set.indicator_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 (s t : Set α) (f : α → M),   s.indicator (t.indicator f) = (s ∩ t).indicator f
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasureTheory.setIntegral_condExp`：setIntegral_condExp (hm : m <= m₀) [S
igmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in
 s, (μ[f | m]) x ∂μ = ∫…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.condExp_indicator`：condExp_indicator (hf_int : Integrable 
f μ) (hs : MeasurableSet[m] s) : μ[s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m
])
-/
theorem condExp_restrict_ae_eq_restrict (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs_m : MeasurableSet[m] s) (hf_int : Integrable f μ) :
    (μ.restrict s)[f | m] =ᵐ[μ.restrict s] μ[f | m] := by
  have : SigmaFinite ((μ.restrict s).trim hm) := by rw [← restrict_trim hm _ hs_m]; infer_instance
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  refine EventuallyEq.trans ?_ (condExp_indicator hf_int hs_m)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm (hf_int.indicator (hm _ hs_m)) ?_ ?_ ?_
  · intro t ht _
    rw [← integrable_indicator_iff (hm _ ht), Set.indicator_indicator, Set.inter_comm, ←
      Set.indicator_indicator]
    suffices h_int_restrict : Integrable (t.indicator ((μ.restrict s)[f | m])) (μ.restrict s) by
      rw [integrable_indicator_iff (hm _ hs_m), IntegrableOn]
      exact h_int_restrict
    exact integrable_condExp.indicator (hm _ ht)
  · intro t ht _
    calc
      ∫ x in t, s.indicator ((μ.restrict s)[f | m]) x ∂μ =
          ∫ x in t, ((μ.restrict s)[f | m]) x ∂μ.restrict s := by
        rw [integral_indicator (hm _ hs_m), Measure.restrict_restrict (hm _ hs_m),
          Measure.restrict_restrict (hm _ ht), Set.inter_comm]
      _ = ∫ x in t, f x ∂μ.restrict s := setIntegral_condExp hm hf_int.integrableOn ht
      _ = ∫ x in t, s.indicator f x ∂μ := by
        rw [integral_indicator (hm _ hs_m), Measure.restrict_restrict (hm _ hs_m),
          Measure.restrict_restrict (hm _ ht), Set.inter_comm]
  · exact (stronglyMeasurable_condExp.indicator hs_m).aestronglyMeasurable

/-- If the restriction to an `m`-measurable set `s` of a σ-algebra `m` is equal to the restriction
to `s` of another σ-algebra `m₂` (hypothesis `hs`), then `μ[f | m] =ᵐ[μ.restrict s] μ[f | m₂]`. -/
/-
**MeasureTheory.condExp_ae_eq_restrict_of_measurableSpace_eq_on** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_ae_eq_restrict_of_measurableSpace_eq_on {m m₂ m0 : MeasurableSpace
 α} {μ : Measure α} (hm : m <= m0) (hm₂ : m₂ <= m0) [SigmaFinite (μ.trim hm)] [S
igmaFinite (μ.trim hm₂)] (hs_m : MeasurableSet[m] s) (hs : forall t, MeasurableS
et[m] (s inter t) ↔ MeasurableSet[m₂] (s inter t)) : μ[f | m] =ᵐ[μ.restrict s] μ
[f | m₂]
参数：hm : m <= m0；hm₂ : m₂ <= m0；μ.trim hm；μ.trim hm₂；hs_m : MeasurableSet[m] s；hs
 : forall t, MeasurableSet[m] (s inter t) ↔ MeasurableSet[m₂] (s inter t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ae_eq_restrict_iff_indicator_ae_eq`：ae_eq_restrict_iff_indicator_ae_eq {
g : α -> β} (hs : MeasurableSet s) : f =ᵐ[μ.restrict s] g ↔ s.indicator f =ᵐ[μ] 
s.indicator g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_indicator`：condExp_indicator (hf_int : Integrable 
f μ) (hs : MeasurableSet[m] s) : μ[s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m
])
· 使用定理 `MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'`：ae_eq_of_f
orall_setIntegral_eq_of_sigmaFinite' (hm : m <= m0) [SigmaFinite (μ.trim hm)] {f
 g : α -> F'} (hf_int_finite : forall s, Measurabl…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `MeasureTheory.integral_add_compl`：integral_add_compl (hs : MeasurableSet
 s) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.condExp_ae_eq_restrict_zero`：condExp_ae_eq_restrict_zero (
hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restrict s] 0) : μ[f | m] =ᵐ[μ.restrict s]
 0
· 使用定理 `indicator_ae_eq_restrict_compl`：indicator_ae_eq_restrict_compl (hs : Mea
surableSet s) : indicator s f =ᵐ[μ.restrict sᶜ] 0
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.setIntegral_condExp`：setIntegral_condExp (hm : m <= m₀) [S
igmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in
 s, (μ[f | m]) x ∂μ = ∫…
· 使用定理 `MeasureTheory.Integrable.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {mα
 : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topolo
gicalSpace ε'] [inst_1 :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If the restriction to an `m`-measurable set `s` of a σ-algebra `m` is equal to t
he restriction
to `s` of another σ-algebra `m₂` (hypothesis `hs`), then `μ[f | m] =ᵐ[μ.restrict
 s] μ[f | m₂]`.
-/
theorem condExp_ae_eq_restrict_of_measurableSpace_eq_on {m m₂ m0 : MeasurableSpace α}
    {μ : Measure α} (hm : m ≤ m0) (hm₂ : m₂ ≤ m0) [SigmaFinite (μ.trim hm)]
    [SigmaFinite (μ.trim hm₂)] (hs_m : MeasurableSet[m] s)
    (hs : ∀ t, MeasurableSet[m] (s ∩ t) ↔ MeasurableSet[m₂] (s ∩ t)) :
    μ[f | m] =ᵐ[μ.restrict s] μ[f | m₂] := by
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  have hs_m₂ : MeasurableSet[m₂] s := by rwa [← Set.inter_univ s, ← hs Set.univ, Set.inter_univ]
  by_cases hf_int : Integrable f μ
  swap; · simp_rw [condExp_of_not_integrable hf_int]; rfl
  refine ((condExp_indicator hf_int hs_m).symm.trans ?_).trans (condExp_indicator hf_int hs_m₂)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm₂
    (fun s _ _ => integrable_condExp.integrableOn)
    (fun s _ _ => integrable_condExp.integrableOn) ?_ ?_
    stronglyMeasurable_condExp.aestronglyMeasurable
  swap
  · have : StronglyMeasurable[m] (μ[s.indicator f | m]) := stronglyMeasurable_condExp
    refine this.aestronglyMeasurable.of_measurableSpace_le_on hm hs_m (fun t => (hs t).mp) ?_
    exact condExp_ae_eq_restrict_zero hs_m.compl (indicator_ae_eq_restrict_compl (hm _ hs_m))
  intro t ht _
  have : ∫ x in t, (μ[s.indicator f | m]) x ∂μ = ∫ x in s ∩ t, (μ[s.indicator f | m]) x ∂μ := by
    rw [← integral_add_compl (hm _ hs_m) integrable_condExp.integrableOn]
    suffices ∫ x in sᶜ, (μ[s.indicator f | m]) x ∂μ.restrict t = 0 by
      rw [this, add_zero, Measure.restrict_restrict (hm _ hs_m)]
    rw [Measure.restrict_restrict (MeasurableSet.compl (hm _ hs_m))]
    suffices μ[s.indicator f | m] =ᵐ[μ.restrict sᶜ] 0 by
      rw [Set.inter_comm, ← Measure.restrict_restrict (hm₂ _ ht)]
      calc
        ∫ x : α in t, (μ[s.indicator f | m]) x ∂μ.restrict sᶜ =
            ∫ x : α in t, 0 ∂μ.restrict sᶜ := by
          refine setIntegral_congr_ae (hm₂ _ ht) ?_
          filter_upwards [this] with x hx _ using hx
        _ = 0 := integral_zero _ _
    refine condExp_ae_eq_restrict_zero hs_m.compl ?_
    exact indicator_ae_eq_restrict_compl (hm _ hs_m)
  have hst_m : MeasurableSet[m] (s ∩ t) := (hs _).mpr (hs_m₂.inter ht)
  simp_rw [this, setIntegral_condExp hm₂ (hf_int.indicator (hm _ hs_m)) ht,
    setIntegral_condExp hm (hf_int.indicator (hm _ hs_m)) hst_m, integral_indicator (hm _ hs_m),
    Measure.restrict_restrict (hm _ hs_m), ← Set.inter_assoc, Set.inter_self]

end MeasureTheory

