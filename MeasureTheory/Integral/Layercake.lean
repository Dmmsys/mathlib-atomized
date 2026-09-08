/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The layer cake formula / Cavalieri's principle / tail probability formula

In this file we prove the following layer cake formula.

Consider a non-negative measurable function `f` on a measure space. Apply pointwise
to it an increasing absolutely continuous function `G : ℝ≥0 → ℝ≥0` vanishing at the origin, with
derivative `G' = g` on the positive real line (in other words, `G` a primitive of a non-negative
locally integrable function `g` on the positive real line). Then the integral of the result,
`∫ G ∘ f`, can be written as the integral over the positive real line of the "tail measures" of `f`
(i.e., a function giving the measures of the sets on which `f` exceeds different positive real
values) weighted by `g`. In probability theory contexts, the "tail measures" could be referred to
as "tail probabilities" of the random variable `f`, or as values of the "complementary cumulative
distribution function" of the random variable `f`. The terminology "tail probability formula" is
therefore occasionally used for the layer cake formula (or a standard application of it).

The essence of the (mathematical) proof is Fubini's theorem.

We also give the most common application of the layer cake formula -
a representation of the integral of a nonnegative function f:
$$∫ f(ω) \,∂μ(ω) = ∫ μ \{ω \mid f(ω) ≥ t\} \,dt$$

Variants of the formulas with measures of sets of the form `{ω | f(ω) > t}` instead of
`{ω | f(ω) ≥ t}` are also included.

## Main results

* `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`
  and `MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul`:
  The general layer cake formulas with Lebesgue integrals, written in terms of measures of
  sets of the forms `{ω | t ≤ f(ω)}` and `{ω | t < f(ω)}`, respectively.
* `MeasureTheory.lintegral_eq_lintegral_meas_le` and
  `MeasureTheory.lintegral_eq_lintegral_meas_lt`:
  The most common special cases of the layer cake formulas, stating that for a nonnegative
  function f we have $∫ f(ω) \,∂μ(ω) = ∫ μ \{ω \mid f(ω) ≥ t\} \,dt$ and
  $∫ f(ω) \,∂μ(ω) = ∫ μ \{ω \mid f(ω) > t\} \,dt$, respectively.
* `Integrable.integral_eq_integral_meas_lt`:
  A Bochner integral version of the most common special case of the layer cake formulas, stating
  that for an integrable and a.e.-nonnegative function f we have
  $∫ f(ω) \,∂μ(ω) = ∫ μ \{ω \mid f(ω) > t\} \,dt$.

## See also

Another common application, a representation of the integral of a real power of a nonnegative
function, is given in `Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean`.

## Tags

layer cake representation, Cavalieri's principle, tail probability formula
-/

public section

noncomputable section

open scoped ENNReal MeasureTheory Topology

open Set MeasureTheory Filter Measure

namespace MeasureTheory

section

variable {α R : Type*} [MeasurableSpace α] (μ : Measure α) [LinearOrder R]

/-
**MeasureTheory.countable_meas_le_ne_meas_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：countable_meas_le_ne_meas_lt (g : α -> R) : {t : R | μ {a : α | t <= g a} 
!= μ {a : α | t < g a}}.Countable
参数：g : α -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `countable_image_gt_image_Ioi`：countable_image_gt_image_Ioi [LinearOrder 
β] (f : β -> α) [SecondCountableTopology α] : Set.Countable {x | exists z, z < f
 x ∧ forall y, x <…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem countable_meas_le_ne_meas_lt (g : α → R) :
    {t : R | μ {a : α | t ≤ g a} ≠ μ {a : α | t < g a}}.Countable := by
  -- the target set is contained in the set of points where the function `t ↦ μ {a : α | t ≤ g a}`
  -- jumps down on the right of `t`. This jump set is countable for any function.
  let F : R → ℝ≥0∞ := fun t ↦ μ {a : α | t ≤ g a}
  apply (countable_image_gt_image_Ioi F).mono
  intro t ht
  have : μ {a | t < g a} < μ {a | t ≤ g a} :=
    lt_of_le_of_ne (measure_mono (fun a ha ↦ le_of_lt ha)) (Ne.symm ht)
  exact ⟨μ {a | t < g a}, this, fun s hs ↦ measure_mono (fun a ha ↦ hs.trans_le ha)⟩
/-
**MeasureTheory.meas_le_ae_eq_meas_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：meas_le_ae_eq_meas_lt {R : Type*} [LinearOrder R] [MeasurableSpace R] (ν :
 Measure R) [NullSingletonClass ν] (g : α -> R) : (fun t => μ {a : α | t <= g a}
) =ᵐ[ν] fun t => μ {a : α | t < g a}
参数：ν : Measure R；g : α -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.measure_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s
 : Set α},   s.Countable → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSi
ngletonClass μ],…
· 使用定理 `MeasureTheory.countable_meas_le_ne_meas_lt`：countable_meas_le_ne_meas_lt
 (g : α -> R) : {t : R | μ {a : α | t <= g a} != μ {a : α | t < g a}}.Countable
-/
theorem meas_le_ae_eq_meas_lt {R : Type*} [LinearOrder R] [MeasurableSpace R]
    (ν : Measure R) [NullSingletonClass ν] (g : α → R) :
    (fun t => μ {a : α | t ≤ g a}) =ᵐ[ν] fun t => μ {a : α | t < g a} :=
  Set.Countable.measure_zero (countable_meas_le_ne_meas_lt μ g) _

end

/-! ### Layercake formula -/


section Layercake

variable {α : Type*} [MeasurableSpace α] {f : α → ℝ} {g : ℝ → ℝ}

set_option backward.isDefEq.respectTransparency.types false in
/-- An auxiliary version of the layer cake formula (Cavalieri's principle, tail probability
formula), with a measurability assumption that would also essentially follow from the
integrability assumptions, and a sigma-finiteness assumption.

See `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul` and
`MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul` for the main formulations of the layer
cake formula. -/
/-
**MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul_of_measurable_of_sigmaFi
nite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_comp_eq_lintegral_meas_le_mul_of_measurable_of_sigmaFinite (μ : 
Measure α) [SFinite μ] (f_nn : 0 <= f) (f_mble : Measurable f) (g_intble : foral
l t > 0, IntervalIntegrable g volume 0 t) (g_mble : Measurable g) (g_nn : forall
 t > 0, 0 <= g t) : ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ = ∫⁻ t in Ioi 0
, μ {a : α | t <= f a} * ENNReal.ofReal (g t)
参数：μ : Measure α；f_nn : 0 <= f；f_mble : Measurable f；g_intble : forall t > 0, In
tervalIntegrable g volume 0 t；g_mble : Measurable g；g_nn : forall t > 0, 0 <= g 
t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.self_mem_ae_restrict`：self_mem_ae_restrict {s} (hs : Measu
rableSet s) : s in ae (μ.restrict s)
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.lintegral_congr`：lintegral_congr {f g : α -> Real>=0∞} (h 
: forall a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `MeasureTheory.lintegral_lintegral_swap`：lintegral_lintegral_swap [SFinit
e μ] ⦃f : α -> β -> Real>=0∞⦄ (hf : AEMeasurable (uncurry f) (μ.prod ν)) : ∫⁻ x,
 ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
An auxiliary version of the layer cake formula (Cavalieri's principle, tail prob
ability
formula), with a measurability assumption that would also essentially follow fro
m the
integrability assumptions, and a sigma-finiteness assumption.

See `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul` and
`MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul` for the main formulation
s of the layer
cake formula.
-/
theorem lintegral_comp_eq_lintegral_meas_le_mul_of_measurable_of_sigmaFinite
    (μ : Measure α) [SFinite μ]
    (f_nn : 0 ≤ f) (f_mble : Measurable f)
    (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t) (g_mble : Measurable g)
    (g_nn : ∀ t > 0, 0 ≤ g t) :
    ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
  have g_intble' : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable g volume 0 t := by
    intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · simp [← h]
    · exact g_intble t h
  have integrand_eq : ∀ ω,
      ENNReal.ofReal (∫ t in 0..f ω, g t) = ∫⁻ t in Ioc 0 (f ω), ENNReal.ofReal (g t) := by
    intro ω
    have g_ae_nn : 0 ≤ᵐ[volume.restrict (Ioc 0 (f ω))] g := by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioc : MeasurableSet (Ioc 0 (f ω)))]
        with x hx using g_nn x hx.1
    rw [← ofReal_integral_eq_lintegral_ofReal (g_intble' (f ω) (f_nn ω)).1 g_ae_nn]
    congr
    exact intervalIntegral.integral_of_le (f_nn ω)
  rw [lintegral_congr integrand_eq]
  simp_rw [← lintegral_indicator measurableSet_Ioc]
  rw [← lintegral_indicator measurableSet_Ioi, lintegral_lintegral_swap]
  · apply congr_arg
    funext s
    have aux₁ :
      (fun x => (Ioc 0 (f x)).indicator (fun t : ℝ => ENNReal.ofReal (g t)) s) = fun x =>
        ENNReal.ofReal (g s) * (Ioi (0 : ℝ)).indicator (fun _ => 1) s *
          (Ici s).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (f x) := by
      funext a
      by_cases h : s ∈ Ioc (0 : ℝ) (f a)
      · simp only [h, show s ∈ Ioi (0 : ℝ) from h.1, show f a ∈ Ici s from h.2, indicator_of_mem,
          mul_one]
      · have h_copy := h
        simp only [mem_Ioc, not_and, not_le] at h
        by_cases h' : 0 < s
        · simp only [h_copy, h h', indicator_of_notMem, not_false_iff, mem_Ici, not_le, mul_zero]
        · have : s ∉ Ioi (0 : ℝ) := h'
          simp only [this, h', indicator_of_notMem, not_false_iff, mul_zero,
            zero_mul, mem_Ioc, false_and]
    simp_rw [aux₁]
    rw [lintegral_const_mul']
    swap
    · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      by_cases h : (0 : ℝ) < s <;> · simp [h]
    simp_rw [show
        (fun a => (Ici s).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (f a)) = fun a =>
          {a : α | s ≤ f a}.indicator (fun _ => 1) a
        by funext a; by_cases h : s ≤ f a <;> simp [h]]
    rw [lintegral_indicator₀]
    swap; · exact f_mble.nullMeasurable measurableSet_Ici
    rw [lintegral_one, Measure.restrict_apply MeasurableSet.univ, univ_inter, indicator_mul_left,
      mul_assoc,
      show
        (Ioi 0).indicator (fun _x : ℝ => (1 : ℝ≥0∞)) s * μ {a : α | s ≤ f a} =
          (Ioi 0).indicator (fun _x : ℝ => 1 * μ {a : α | s ≤ f a}) s
        by by_cases h : 0 < s <;> simp [h]]
    simp_rw [mul_comm _ (ENNReal.ofReal _), one_mul]
    rfl
  have aux₂ :
    (Function.uncurry fun (x : α) (y : ℝ) =>
        (Ioc 0 (f x)).indicator (fun t : ℝ => ENNReal.ofReal (g t)) y) =
      {p : α × ℝ | p.2 ∈ Ioc 0 (f p.1)}.indicator fun p => ENNReal.ofReal (g p.2) := by
    funext p
    cases p with | mk p_fst p_snd => ?_
    rw [Function.uncurry_apply_pair]
    by_cases h : p_snd ∈ Ioc 0 (f p_fst)
    · have h' : (p_fst, p_snd) ∈ {p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst)} := h
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
    · have h' : (p_fst, p_snd) ∉ {p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst)} := h
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
  rw [aux₂]
  have mble₀ : MeasurableSet {p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst)} := by
    simpa only [mem_univ, Pi.zero_apply, true_and] using
      measurableSet_region_between_oc measurable_zero f_mble MeasurableSet.univ
  exact (ENNReal.measurable_ofReal.comp (g_mble.comp measurable_snd)).aemeasurable.indicator₀
    mble₀.nullMeasurableSet

/-- An auxiliary version of the layer cake formula (Cavalieri's principle, tail probability
formula), with a measurability assumption that would also essentially follow from the
integrability assumptions.
Compared to `lintegral_comp_eq_lintegral_meas_le_mul_of_measurable_of_sigmaFinite`, we remove
the sigma-finite assumption.

See `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul` and
`MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul` for the main formulations of the layer
cake formula. -/
/-
**MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul_of_measurable** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_comp_eq_lintegral_meas_le_mul_of_measurable (μ : Measure α) (f_n
n : 0 <= f) (f_mble : Measurable f) (g_intble : forall t > 0, IntervalIntegrable
 g volume 0 t) (g_mble : Measurable g) (g_nn : forall t > 0, 0 <= g t) : ∫⁻ ω, E
NNReal.ofReal (∫ t in 0..f ω, g t) ∂μ = ∫⁻ t in Ioi 0, μ {a : α | t <= f a} * EN
NReal.ofReal (g t)
参数：μ : Measure α；f_nn : 0 <= f；f_mble : Measurable f；g_intble : forall t > 0, In
tervalIntegrable g volume 0 t；g_mble : Measurable g；g_nn : forall t > 0, 0 <= g 
t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_restrict_of_ae_restrict_of_subset`：ae_restrict_of_ae_re
strict_of_subset {s t : Set α} {p : α -> Prop} (hst : s subseteq t) (h : forallᵐ
 x ∂μ.restrict t, p x) : forallᵐ x ∂μ.re…
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_zero`：integral_zero : (∫ _ in a..b, (0 : E) ∂μ
) = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Real.volume_Ioi`：volume_Ioi {a : Real} : volume (Ioi a) = ∞
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
（共 136 条，此处仅展示前 30 条）

--- 原说明 ---
An auxiliary version of the layer cake formula (Cavalieri's principle, tail prob
ability
formula), with a measurability assumption that would also essentially follow fro
m the
integrability assumptions.
Compared to `lintegral_comp_eq_lintegral_meas_le_mul_of_measurable_of_sigmaFinit
e`, we remove
the sigma-finite assumption.

See `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul` and
`MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul` for the main formulation
s of the layer
cake formula.
-/
theorem lintegral_comp_eq_lintegral_meas_le_mul_of_measurable (μ : Measure α)
    (f_nn : 0 ≤ f) (f_mble : Measurable f)
    (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t) (g_mble : Measurable g)
    (g_nn : ∀ t > 0, 0 ≤ g t) :
    ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
  /- We will reduce to the sigma-finite case, after excluding two easy cases where the result
  is more or less obvious. -/
  have f_nonneg : ∀ ω, 0 ≤ f ω := fun ω ↦ f_nn ω
  -- trivial case where `g` is ae zero. Then both integrals vanish.
  by_cases H1 : g =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0
  · have A : ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ = 0 := by
      have : ∀ ω, ∫ t in 0..f ω, g t = ∫ t in 0..f ω, 0 := by
        intro ω
        simp_rw [intervalIntegral.integral_of_le (f_nonneg ω)]
        apply integral_congr_ae
        exact ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self H1
      simp [this]
    have B : ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) = 0 := by
      have : (fun t ↦ μ {a : α | t ≤ f a} * ENNReal.ofReal (g t))
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
          filter_upwards [H1] with t ht using by simp [ht]
      simp [lintegral_congr_ae this]
    rw [A, B]
  -- easy case where both sides are obviously infinite: for some `s`, one has
  -- `μ {a : α | s < f a} = ∞` and moreover `g` is not ae zero on `[0, s]`.
  by_cases! H2 : ∃ s > 0, 0 < ∫ t in 0..s, g t ∧ μ {a : α | s < f a} = ∞
  · rcases H2 with ⟨s, s_pos, hs, h's⟩
    rw [intervalIntegral.integral_of_le s_pos.le] at hs
    /- The first integral is infinite, as for `t ∈ [0, s]` one has `μ {a : α | t ≤ f a} = ∞`,
    and moreover the additional integral `g` is not uniformly zero. -/
    have A : ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) = ∞ := by
      rw [eq_top_iff]
      calc
      ∞ = ∫⁻ t in Ioc 0 s, ∞ * ENNReal.ofReal (g t) := by
          have I_pos : ∫⁻ (a : ℝ) in Ioc 0 s, ENNReal.ofReal (g a) ≠ 0 := by
            rw [← ofReal_integral_eq_lintegral_ofReal (g_intble s s_pos).1]
            · simpa only [not_lt, ne_eq, ENNReal.ofReal_eq_zero, not_le] using hs
            · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using g_nn _ ht.1
          rw [lintegral_const_mul, ENNReal.top_mul I_pos]
          exact ENNReal.measurable_ofReal.comp g_mble
      _ ≤ ∫⁻ t in Ioc 0 s, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
          apply setLIntegral_mono' measurableSet_Ioc (fun x hx ↦ ?_)
          rw [← h's]
          gcongr
          exact fun ha ↦ hx.2.trans (le_of_lt ha)
      _ ≤ ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) :=
          lintegral_mono_set Ioc_subset_Ioi_self
    /- The second integral is infinite, as one integrates among other things on those `ω` where
    `f ω > s`: this is an infinite measure set, and on it the integrand is bounded below
    by `∫ t in 0..s, g t` which is positive. -/
    have B : ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ = ∞ := by
      rw [eq_top_iff]
      calc
      ∞ = ∫⁻ _ in {a | s < f a}, ENNReal.ofReal (∫ t in 0..s, g t) ∂μ := by
          simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
            h's]
          rw [ENNReal.mul_top]
          simpa [intervalIntegral.integral_of_le s_pos.le] using hs
      _ ≤ ∫⁻ ω in {a | s < f a}, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ := by
          apply setLIntegral_mono' (measurableSet_lt measurable_const f_mble) (fun a ha ↦ ?_)
          apply ENNReal.ofReal_le_ofReal
          apply intervalIntegral.integral_mono_interval le_rfl s_pos.le (le_of_lt ha)
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using g_nn _ ht.1
          · exact g_intble _ (s_pos.trans ha)
      _ ≤ ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ := setLIntegral_le_lintegral _ _
    rw [A, B]
  /- It remains to handle the interesting case, where `g` is not zero, but both integrals are
  not obviously infinite. Let `M` be the largest number such that `g = 0` on `[0, M]`. Then we
  may restrict `μ` to the points where `f ω > M` (as the other ones do not contribute to the
  integral). The restricted measure `ν` is sigma-finite, as `μ` gives finite measure to
  `{ω | f ω > a}` for any `a > M` (otherwise, we would be in the easy case above), so that
  one can write (a full measure subset of) the space as the countable union of the finite measure
  sets `{ω | f ω > uₙ}` for `uₙ` a sequence decreasing to `M`. Therefore,
  this case follows from the case where the measure is sigma-finite, applied to `ν`. -/
  have M_bdd : BddAbove {s : ℝ | g =ᵐ[volume.restrict (Ioc (0 : ℝ) s)] 0} := by
    contrapose H1
    have : ∀ (n : ℕ), g =ᵐ[volume.restrict (Ioc (0 : ℝ) n)] 0 := by
      intro n
      rcases not_bddAbove_iff.1 H1 n with ⟨s, hs, ns⟩
      exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ns.le) hs
    have Hg : g =ᵐ[volume.restrict (⋃ (n : ℕ), (Ioc (0 : ℝ) n))] 0 :=
      (ae_restrict_iUnion_iff _ _).2 this
    have : (⋃ (n : ℕ), (Ioc (0 : ℝ) n)) = Ioi 0 :=
      iUnion_Ioc_eq_Ioi_self_iff.2 (fun x _ ↦ exists_nat_ge x)
    rwa [this] at Hg
  -- let `M` be the largest number such that `g` vanishes ae on `(0, M]`.
  let M : ℝ := sSup {s : ℝ | g =ᵐ[volume.restrict (Ioc (0 : ℝ) s)] 0}
  have zero_mem : 0 ∈ {s : ℝ | g =ᵐ[volume.restrict (Ioc (0 : ℝ) s)] 0} := by simpa using! trivial
  have M_nonneg : 0 ≤ M := le_csSup M_bdd zero_mem
  -- Then the function `g` indeed vanishes ae on `(0, M]`.
  have hgM : g =ᵐ[volume.restrict (Ioc (0 : ℝ) M)] 0 := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    obtain ⟨u, -, uM, ulim⟩ : ∃ u, StrictMono u ∧ (∀ (n : ℕ), u n < M) ∧ Tendsto u atTop (𝓝 M) :=
      exists_seq_strictMono_tendsto M
    have I : ∀ n, g =ᵐ[volume.restrict (Ioc (0 : ℝ) (u n))] 0 := by
      intro n
      obtain ⟨s, hs, uns⟩ : ∃ s, g =ᵐ[Measure.restrict volume (Ioc 0 s)] 0 ∧ u n < s :=
        exists_lt_of_lt_csSup (Set.nonempty_of_mem zero_mem) (uM n)
      exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right uns.le) hs
    have : g =ᵐ[volume.restrict (⋃ n, Ioc (0 : ℝ) (u n))] 0 := (ae_restrict_iUnion_iff _ _).2 I
    apply ae_restrict_of_ae_restrict_of_subset _ this
    rintro x ⟨x_pos, xM⟩
    obtain ⟨n, hn⟩ : ∃ n, x < u n := ((tendsto_order.1 ulim).1 _ xM).exists
    exact mem_iUnion.2 ⟨n, ⟨x_pos, hn.le⟩⟩
  -- Let `ν` be the restriction of `μ` to those points where `f a > M`.
  let ν := μ.restrict {a : α | M < f a}
  -- This measure is sigma-finite (this is the whole point of the argument).
  have : SigmaFinite ν := by
    obtain ⟨u, -, uM, ulim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), M < u n) ∧ Tendsto u atTop (𝓝 M) :=
      exists_seq_strictAnti_tendsto M
    let s : ν.FiniteSpanningSetsIn univ :=
    { set := fun n ↦ {a | f a ≤ M} ∪ {a | u n < f a}
      set_mem := fun _ ↦ trivial
      finite := by
        intro n
        have I : ν {a | f a ≤ M} = 0 := by
          rw [Measure.restrict_apply (measurableSet_le f_mble measurable_const)]
          convert! measure_empty (μ := μ)
          rw [← disjoint_iff_inter_eq_empty]
          exact disjoint_left.mpr (fun a ha ↦ by simpa using ha)
        have J : μ {a | u n < f a} < ∞ := by
          rw [lt_top_iff_ne_top]
          apply H2 _ (M_nonneg.trans_lt (uM n))
          by_contra H3
          rw [not_lt, intervalIntegral.integral_of_le (M_nonneg.trans (uM n).le)] at H3
          have g_nn_ae : ∀ᵐ t ∂(volume.restrict (Ioc 0 (u n))), 0 ≤ g t := by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs using g_nn _ hs.1
          have Ig : ∫ (t : ℝ) in Ioc 0 (u n), g t = 0 :=
            le_antisymm H3 (integral_nonneg_of_ae g_nn_ae)
          have J : ∀ᵐ t ∂(volume.restrict (Ioc 0 (u n))), g t = 0 :=
            (integral_eq_zero_iff_of_nonneg_ae g_nn_ae
              (g_intble (u n) (M_nonneg.trans_lt (uM n))).1).1 Ig
          have : u n ≤ M := le_csSup M_bdd J
          exact lt_irrefl _ (this.trans_lt (uM n))
        refine lt_of_le_of_lt (measure_union_le _ _) ?_
        rw [I, zero_add]
        apply lt_of_le_of_lt _ J
        exact restrict_le_self _
      spanning := by
        apply eq_univ_iff_forall.2 (fun a ↦ ?_)
        rcases le_or_gt (f a) M with ha | ha
        · exact mem_iUnion.2 ⟨0, Or.inl ha⟩
        · obtain ⟨n, hn⟩ : ∃ n, u n < f a := ((tendsto_order.1 ulim).2 _ ha).exists
          exact mem_iUnion.2 ⟨n, Or.inr hn⟩ }
    exact ⟨⟨s⟩⟩
  -- the first integrals with respect to `μ` and to `ν` coincide, as points with `f a ≤ M` are
  -- weighted by zero as `g` vanishes there.
  have A : ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ
         = ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂ν := by
    have meas : MeasurableSet {a | M < f a} := measurableSet_lt measurable_const f_mble
    have I : ∫⁻ ω in {a | M < f a}ᶜ, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ
             = ∫⁻ _ in {a | M < f a}ᶜ, 0 ∂μ := by
      apply setLIntegral_congr_fun meas.compl (fun s hs ↦ ?_)
      have : ∫ (t : ℝ) in 0..f s, g t = ∫ (t : ℝ) in 0..f s, 0 := by
        simp_rw [intervalIntegral.integral_of_le (f_nonneg s)]
        apply integral_congr_ae
        apply ae_mono (restrict_mono ?_ le_rfl) hgM
        apply Ioc_subset_Ioc_right
        simpa using hs
      simp [this]
    simp only [lintegral_const, zero_mul] at I
    rw [← lintegral_add_compl _ meas, I, add_zero]
  -- the second integrals with respect to `μ` and to `ν` coincide, as points with `f a ≤ M` do not
  -- contribute to either integral since the weight `g` vanishes.
  have B : ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t)
           = ∫⁻ t in Ioi 0, ν {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
    have B1 : ∫⁻ t in Ioc 0 M, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t)
         = ∫⁻ t in Ioc 0 M, ν {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
      apply lintegral_congr_ae
      filter_upwards [hgM] with t ht
      simp [ht]
    have B2 : ∫⁻ t in Ioi M, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t)
              = ∫⁻ t in Ioi M, ν {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
      apply setLIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ ?_)
      rw [Measure.restrict_apply (measurableSet_le measurable_const f_mble)]
      congr 3
      exact (inter_eq_left.2 (fun a ha ↦ (mem_Ioi.1 ht).trans_le ha)).symm
    have I : Ioi (0 : ℝ) = Ioc (0 : ℝ) M ∪ Ioi M := (Ioc_union_Ioi_eq_Ioi M_nonneg).symm
    have J : Disjoint (Ioc 0 M) (Ioi M) := Ioc_disjoint_Ioi le_rfl
    rw [I, lintegral_union measurableSet_Ioi J, lintegral_union measurableSet_Ioi J, B1, B2]
  -- therefore, we may replace the integrals w.r.t. `μ` with integrals w.r.t. `ν`, and apply the
  -- result for sigma-finite measures.
  rw [A, B]
  exact lintegral_comp_eq_lintegral_meas_le_mul_of_measurable_of_sigmaFinite
    ν f_nn f_mble g_intble g_mble g_nn

/-- The layer cake formula / **Cavalieri's principle** / tail probability formula:

Let `f` be a non-negative measurable function on a measure space. Let `G` be an
increasing absolutely continuous function on the positive real line, vanishing at the origin,
with derivative `G' = g`. Then the integral of the composition `G ∘ f` can be written as
the integral over the positive real line of the "tail measures" `μ {ω | f(ω) ≥ t}` of `f`
weighted by `g`.

Roughly speaking, the statement is: `∫⁻ (G ∘ f) ∂μ = ∫⁻ t in 0..∞, g(t) * μ {ω | f(ω) ≥ t}`.

See `MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul` for a version with sets of the form
`{ω | f(ω) > t}` instead. -/
/-
**MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：lintegral_comp_eq_lintegral_meas_le_mul (μ : Measure α) (f_nn : 0 <=ᵐ[μ] f
) (f_mble : AEMeasurable f μ) (g_intble : forall t > 0, IntervalIntegrable g vol
ume 0 t) (g_nn : forallᵐ t ∂volume.restrict (Ioi 0), 0 <= g t) : ∫⁻ ω, ENNReal.o
fReal (∫ t in 0..f ω, g t) ∂μ = ∫⁻ t in Ioi 0, μ {a : α | t <= f a} * ENNReal.of
Real (g t)
参数：μ : Measure α；f_nn : 0 <=ᵐ[μ] f；f_mble : AEMeasurable f μ；g_intble : forall t
 > 0, IntervalIntegrable g volume 0 t；g_nn : forallᵐ t ∂volume.restrict (Ioi 0),
 0 <= g t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.exists_measurable_nonneg`：exists_measurable_nonneg {β} [Pre
order β] [Zero β] {mβ : MeasurableSpace β} {f : α -> β} (hf : AEMeasurable f μ) 
(f_nn : forallᵐ t ∂μ, 0 <= …
· 使用定理 `aemeasurable_Ioi_of_forall_Ioc`：aemeasurable_Ioi_of_forall_Ioc {β} {mβ :
 MeasurableSpace β} [LinearOrder α] [(atTop : Filter α).IsCountablyGenerated] {x
 : α} {g : α -> β} (…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.IntegrableOn.congr_fun_ae`：∀ {α : Type u_1} {ε : Type u_3}
 {mα : MeasurableSpace α} {f g : α → ε} {s : Set α} {μ : MeasureTheory.Measure α
}   [inst : TopologicalSpace …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioc_eq_empty_of_le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, 
a ≤ b → Set.Ioc b a = ∅
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
· 使用定理 `MeasureTheory.integrableOn_empty`：integrableOn_empty : IntegrableOn f ∅ 
μ
· 使用定理 `Measurable.max`：Measurable.max {f g : δ -> α} (hf : Measurable f) (hg : 
Measurable g) : Measurable fun a => max (f a) (g a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
The layer cake formula / **Cavalieri's principle** / tail probability formula:

Let `f` be a non-negative measurable function on a measure space. Let `G` be an
increasing absolutely continuous function on the positive real line, vanishing a
t the origin,
with derivative `G' = g`. Then the integral of the composition `G ∘ f` can be wr
itten as
the integral over the positive real line of the "tail measures" `μ {ω | f(ω) ≥ t
}` of `f`
weighted by `g`.

Roughly speaking, the statement is: `∫⁻ (G ∘ f) ∂μ = ∫⁻ t in 0..∞, g(t) * μ {ω |
 f(ω) ≥ t}`.

See `MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul` for a version with s
ets of the form
`{ω | f(ω) > t}` instead.
-/
theorem lintegral_comp_eq_lintegral_meas_le_mul (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (g_nn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t) :
    ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
  obtain ⟨G, G_mble, G_nn, g_eq_G⟩ : ∃ G : ℝ → ℝ, Measurable G ∧ 0 ≤ G
      ∧ g =ᵐ[volume.restrict (Ioi 0)] G := by
    refine AEMeasurable.exists_measurable_nonneg ?_ g_nn
    exact aemeasurable_Ioi_of_forall_Ioc fun t ht => (g_intble t ht).1.1.aemeasurable
  have g_eq_G_on : ∀ t, g =ᵐ[volume.restrict (Ioc 0 t)] G := fun t =>
    ae_mono (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl) g_eq_G
  have G_intble : ∀ t > 0, IntervalIntegrable G volume 0 t := by
    refine fun t t_pos => ⟨(g_intble t t_pos).1.congr_fun_ae (g_eq_G_on t), ?_⟩
    rw [Ioc_eq_empty_of_le t_pos.lt.le]
    exact integrableOn_empty
  obtain ⟨F, F_mble, F_nn, f_eq_F⟩ : ∃ F : α → ℝ, Measurable F ∧ 0 ≤ F ∧ f =ᵐ[μ] F := by
    refine ⟨fun ω ↦ max (f_mble.mk f ω) 0, f_mble.measurable_mk.max measurable_const,
        fun ω ↦ le_max_right _ _, ?_⟩
    filter_upwards [f_mble.ae_eq_mk, f_nn] with ω hω h'ω
    rw [← hω]
    exact (max_eq_left h'ω).symm
  have eq₁ :
    ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ F a} * ENNReal.ofReal (G t) := by
    apply lintegral_congr_ae
    filter_upwards [g_eq_G] with t ht
    rw [ht]
    congr 1
    apply measure_congr
    filter_upwards [f_eq_F] with a ha using by simp [Set.ofPred, ha]
  have eq₂ : ∀ᵐ ω ∂μ,
      ENNReal.ofReal (∫ t in 0..f ω, g t) = ENNReal.ofReal (∫ t in 0..F ω, G t) := by
    filter_upwards [f_eq_F] with ω fω_nn
    rw [fω_nn]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    have fω_nn : 0 ≤ F ω := F_nn ω
    rw [uIoc_of_le fω_nn, ←
      ae_restrict_iff' (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) (F ω)))]
    exact g_eq_G_on (F ω)
  simp_rw [lintegral_congr_ae eq₂, eq₁]
  exact lintegral_comp_eq_lintegral_meas_le_mul_of_measurable μ F_nn F_mble
          G_intble G_mble (fun t _ => G_nn t)

/-- The standard case of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f ∂μ = ∫⁻ t in 0..∞, μ {ω | f(ω) ≥ t}`.

See `MeasureTheory.lintegral_eq_lintegral_meas_lt` for a version with sets of the form
`{ω | f(ω) > t}` instead. -/
/-
**MeasureTheory.lintegral_eq_lintegral_meas_le** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：lintegral_eq_lintegral_meas_le (μ : Measure α) (f_nn : 0 <=ᵐ[μ] f) (f_mble
 : AEMeasurable f μ) : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ = ∫⁻ t in Ioi 0, μ {a : α |
 t <= f a}
参数：μ : Measure α；f_nn : 0 <=ᵐ[μ] f；f_mble : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegrable_const`：intervalIntegrable_const [IsLocallyFiniteMeasu
re μ] {c : E} : IntervalIntegrable (fun _ => c) μ a b
· 使用定理 `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`：lintegral_comp_eq
_lintegral_meas_le_mul (μ : Measure α) (f_nn : 0 <=ᵐ[μ] f) (f_mble : AEMeasurabl
e f μ) (g_intble : forall t > 0, IntervalIn…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The standard case of the layer cake formula / Cavalieri's principle / tail proba
bility formula:

For a nonnegative function `f` on a measure space, the Lebesgue integral of `f` 
can
be written (roughly speaking) as: `∫⁻ f ∂μ = ∫⁻ t in 0..∞, μ {ω | f(ω) ≥ t}`.

See `MeasureTheory.lintegral_eq_lintegral_meas_lt` for a version with sets of th
e form
`{ω | f(ω) > t}` instead.
-/
theorem lintegral_eq_lintegral_meas_le (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ = ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} := by
  set cst := fun _ : ℝ => (1 : ℝ)
  have cst_intble : ∀ t > 0, IntervalIntegrable cst volume 0 t := fun _ _ =>
    intervalIntegrable_const
  have key :=
    lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble cst_intble
      (Eventually.of_forall fun _ => zero_le_one)
  simp_rw [cst, ENNReal.ofReal_one, mul_one] at key
  rw [← key]
  congr with ω
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]

end Layercake

section LayercakeLT

variable {α : Type*} [MeasurableSpace α]
variable {f : α → ℝ} {g : ℝ → ℝ}

/-- The layer cake formula / Cavalieri's principle / tail probability formula:

Let `f` be a non-negative measurable function on a measure space. Let `G` be an
increasing absolutely continuous function on the positive real line, vanishing at the origin,
with derivative `G' = g`. Then the integral of the composition `G ∘ f` can be written as
the integral over the positive real line of the "tail measures" `μ {ω | f(ω) > t}` of `f`
weighted by `g`.

Roughly speaking, the statement is: `∫⁻ (G ∘ f) ∂μ = ∫⁻ t in 0..∞, g(t) * μ {ω | f(ω) > t}`.

See `lintegral_comp_eq_lintegral_meas_le_mul` for a version with sets of the form `{ω | f(ω) ≥ t}`
instead. -/
/-
**MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：lintegral_comp_eq_lintegral_meas_lt_mul (μ : Measure α) (f_nn : 0 <=ᵐ[μ] f
) (f_mble : AEMeasurable f μ) (g_intble : forall t > 0, IntervalIntegrable g vol
ume 0 t) (g_nn : forallᵐ t ∂volume.restrict (Ioi 0), 0 <= g t) : ∫⁻ ω, ENNReal.o
fReal (∫ t in 0..f ω, g t) ∂μ = ∫⁻ t in Ioi 0, μ {a : α | t < f a} * ENNReal.ofR
eal (g t)
参数：μ : Measure α；f_nn : 0 <=ᵐ[μ] f；f_mble : AEMeasurable f μ；g_intble : forall t
 > 0, IntervalIntegrable g volume 0 t；g_nn : forallᵐ t ∂volume.restrict (Ioi 0),
 0 <= g t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`：lintegral_comp_eq
_lintegral_meas_le_mul (μ : Measure α) (f_nn : 0 <=ᵐ[μ] f) (f_mble : AEMeasurabl
e f μ) (g_intble : forall t > 0, IntervalIn…
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.meas_le_ae_eq_meas_lt`：meas_le_ae_eq_meas_lt {R : Type*} [
LinearOrder R] [MeasurableSpace R] (ν : Measure R) [NullSingletonClass ν] (g : α
 -> R) : (fun t => μ {a :…
· 使用定理 `MeasureTheory.Measure.restrict.instNullSingletonClass`：∀ {α : Type u_1} 
{m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.NullSingle
tonClass μ]   (s : Set α), MeasureTheory.Nu…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
The layer cake formula / Cavalieri's principle / tail probability formula:

Let `f` be a non-negative measurable function on a measure space. Let `G` be an
increasing absolutely continuous function on the positive real line, vanishing a
t the origin,
with derivative `G' = g`. Then the integral of the composition `G ∘ f` can be wr
itten as
the integral over the positive real line of the "tail measures" `μ {ω | f(ω) > t
}` of `f`
weighted by `g`.

Roughly speaking, the statement is: `∫⁻ (G ∘ f) ∂μ = ∫⁻ t in 0..∞, g(t) * μ {ω |
 f(ω) > t}`.

See `lintegral_comp_eq_lintegral_meas_le_mul` for a version with sets of the for
m `{ω | f(ω) ≥ t}`
instead.
-/
theorem lintegral_comp_eq_lintegral_meas_lt_mul (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (g_nn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t) :
    ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {a : α | t < f a} * ENNReal.ofReal (g t) := by
  rw [lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn]
  apply lintegral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f]
    with t ht
  rw [ht]

/-- The standard case of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f ∂μ = ∫⁻ t in 0..∞, μ {ω | f(ω) > t}`.

See `lintegral_eq_lintegral_meas_le` for a version with sets of the form `{ω | f(ω) ≥ t}`
instead. -/
/-
**MeasureTheory.lintegral_eq_lintegral_meas_lt** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：lintegral_eq_lintegral_meas_lt (μ : Measure α) (f_nn : 0 <=ᵐ[μ] f) (f_mble
 : AEMeasurable f μ) : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ = ∫⁻ t in Ioi 0, μ {a : α |
 t < f a}
参数：μ : Measure α；f_nn : 0 <=ᵐ[μ] f；f_mble : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_eq_lintegral_meas_le`：lintegral_eq_lintegral_mea
s_le (μ : Measure α) (f_nn : 0 <=ᵐ[μ] f) (f_mble : AEMeasurable f μ) : ∫⁻ ω, ENN
Real.ofReal (f ω) ∂μ = ∫⁻ t in Ioi…
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.meas_le_ae_eq_meas_lt`：meas_le_ae_eq_meas_lt {R : Type*} [
LinearOrder R] [MeasurableSpace R] (ν : Measure R) [NullSingletonClass ν] (g : α
 -> R) : (fun t => μ {a :…
· 使用定理 `MeasureTheory.Measure.restrict.instNullSingletonClass`：∀ {α : Type u_1} 
{m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.NullSingle
tonClass μ]   (s : Set α), MeasureTheory.Nu…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
The standard case of the layer cake formula / Cavalieri's principle / tail proba
bility formula:

For a nonnegative function `f` on a measure space, the Lebesgue integral of `f` 
can
be written (roughly speaking) as: `∫⁻ f ∂μ = ∫⁻ t in 0..∞, μ {ω | f(ω) > t}`.

See `lintegral_eq_lintegral_meas_le` for a version with sets of the form `{ω | f
(ω) ≥ t}`
instead.
-/
theorem lintegral_eq_lintegral_meas_lt (μ : Measure α)
    (f_nn : 0 ≤ᵐ[μ] f) (f_mble : AEMeasurable f μ) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ = ∫⁻ t in Ioi 0, μ {a : α | t < f a} := by
  rw [lintegral_eq_lintegral_meas_le μ f_nn f_mble]
  apply lintegral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f]
    with t ht
  rw [ht]

end LayercakeLT

section LayercakeIntegral

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}

/-- The standard case of the layer cake formula / Cavalieri's principle / tail probability formula:

For an integrable a.e.-nonnegative real-valued function `f`, the Bochner integral of `f` can be
written (roughly speaking) as: `∫ f ∂μ = ∫ t in 0..∞, μ {ω | f(ω) > t}`.

See `MeasureTheory.lintegral_eq_lintegral_meas_lt` for a version with Lebesgue integral `∫⁻`
instead. -/
/-
**MeasureTheory.Integrable.integral_eq_integral_meas_lt** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} 
{f : α → ℝ},   MeasureTheory.Integrable f μ → 0 ≤ᵐ[μ] f → ∫ (ω : α), f ω ∂μ = ∫ 
(t : ℝ) in Set.Ioi 0, μ.real {a | t < f a}
参数：ω : α；t : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_eq_lintegral_meas_lt`：lintegral_eq_lintegral_mea
s_lt (μ : Measure α) (f_nn : 0 <=ᵐ[μ] f) (f_mble : AEMeasurable f μ) : ∫⁻ ω, ENN
Real.ofReal (f ω) ∂μ = ∫⁻ t in Ioi…
· 使用定理 `MeasureTheory.Integrable.aemeasurable`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]
   [inst_1 : ContinuousENor…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Integrable.lintegral_lt_top`：∀ {α : Type u_1} {mα : Measur
ableSpace α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.Integrab
le f μ → ∫⁻ (x : α), ENNReal.of…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Integrable.measure_gt_lt_top`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   {f : α → β} [inst_1 : …
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.measureReal_nonneg`：∀ {α : Type u_1} {x : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α}, 0 ≤ μ.real s
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `Antitone.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Topological
Space α] {mα : MeasurableSpace α} [BorelSpace α]   [inst_2 : TopologicalSpace β]
 {mβ : Me…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The standard case of the layer cake formula / Cavalieri's principle / tail proba
bility formula:

For an integrable a.e.-nonnegative real-valued function `f`, the Bochner integra
l of `f` can be
written (roughly speaking) as: `∫ f ∂μ = ∫ t in 0..∞, μ {ω | f(ω) > t}`.

See `MeasureTheory.lintegral_eq_lintegral_meas_lt` for a version with Lebesgue i
ntegral `∫⁻`
instead.
-/
theorem Integrable.integral_eq_integral_meas_lt
    (f_intble : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) :
    ∫ ω, f ω ∂μ = ∫ t in Set.Ioi 0, μ.real {a : α | t < f a} := by
  have key := lintegral_eq_lintegral_meas_lt μ f_nn f_intble.aemeasurable
  have lhs_finite : ∫⁻ (ω : α), ENNReal.ofReal (f ω) ∂μ < ∞ := Integrable.lintegral_lt_top f_intble
  have rhs_finite : ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a} < ∞ := by simp only [← key, lhs_finite]
  have rhs_integrand_finite : ∀ (t : ℝ), t > 0 → μ {a | t < f a} < ∞ :=
    fun t ht ↦ measure_gt_lt_top f_intble ht
  convert! (ENNReal.toReal_eq_toReal_iff' lhs_finite.ne rhs_finite.ne).mpr key
  · exact integral_eq_lintegral_of_nonneg_ae f_nn f_intble.aestronglyMeasurable
  · have aux := @integral_eq_lintegral_of_nonneg_ae _ _ ((volume : Measure ℝ).restrict (Set.Ioi 0))
      (fun t ↦ μ.real {a : α | t < f a}) ?_ ?_
    · rw [aux]
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      exact fun t t_pos ↦ ENNReal.ofReal_toReal (rhs_integrand_finite t t_pos).ne
    · exact Eventually.of_forall (fun x ↦ by positivity)
    · apply Measurable.aestronglyMeasurable
      refine Measurable.ennreal_toReal ?_
      exact Antitone.measurable (fun _ _ hst ↦ measure_mono (fun _ h ↦ lt_of_le_of_lt hst h))
/-
**MeasureTheory.Integrable.integral_eq_integral_meas_le** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} 
{f : α → ℝ},   MeasureTheory.Integrable f μ → 0 ≤ᵐ[μ] f → ∫ (ω : α), f ω ∂μ = ∫ 
(t : ℝ) in Set.Ioi 0, μ.real {a | t ≤ f a}
参数：ω : α；t : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Integrable.integral_eq_integral_meas_lt`：∀ {α : Type u_1} 
[inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureT
heory.Integrable f μ → 0 ≤ᵐ[μ] f → ∫ (ω : α…
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.meas_le_ae_eq_meas_lt`：meas_le_ae_eq_meas_lt {R : Type*} [
LinearOrder R] [MeasurableSpace R] (ν : Measure R) [NullSingletonClass ν] (g : α
 -> R) : (fun t => μ {a :…
· 使用定理 `MeasureTheory.Measure.restrict.instNullSingletonClass`：∀ {α : Type u_1} 
{m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.NullSingle
tonClass μ]   (s : Set α), MeasureTheory.Nu…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Integrable.integral_eq_integral_meas_le
    (f_intble : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) :
    ∫ ω, f ω ∂μ = ∫ t in Set.Ioi 0, μ.real {a : α | t ≤ f a} := by
  rw [Integrable.integral_eq_integral_meas_lt f_intble f_nn]
  apply integral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f] with t ht
  exact congrArg ENNReal.toReal ht.symm
/-
**MeasureTheory.Integrable.integral_eq_integral_Ioc_meas_le** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} 
{f : α → ℝ} {M : ℝ},   MeasureTheory.Integrable f μ →     0 ≤ᵐ[μ] f → (f ≤ᵐ[μ] f
un x => M) → ∫ (ω : α), f ω ∂μ = ∫ (t : ℝ) in Set.Ioc 0 M, μ.real {a | t ≤ f a}
参数：f ≤ᵐ[μ] fun x => M；ω : α；t : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Integrable.integral_eq_integral_meas_le`：∀ {α : Type u_1} 
[inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureT
heory.Integrable f μ → 0 ≤ᵐ[μ] f → ∫ (ω : α…
· 使用定理 `MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero`：setIntegral_
eq_of_subset_of_ae_sdiff_eq_zero (ht : NullMeasurableSet t μ) (hts : s subseteq 
t) (h't : forallᵐ x ∂μ, x in t \ s -> f x = 0) :…
· 使用定理 `nullMeasurableSet_Ioi`：nullMeasurableSet_Ioi [ClosedIicTopology α] : Nul
lMeasurableSet (Ioi a) μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.measure_eq_zero_iff_ae_notMem`：measure_eq_zero_iff_ae_notM
em {s : Set α} : μ s = 0 ↔ forallᵐ a ∂μ, a ∉ s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_eq_zero_iff`：toReal_eq_zero_iff (x : Real>=0∞) : x.toReal
 = 0 ↔ x = 0 ∨ x = ∞
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
lemma Integrable.integral_eq_integral_Ioc_meas_le {f : α → ℝ} {M : ℝ}
    (f_intble : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) (f_bdd : f ≤ᵐ[μ] (fun _ ↦ M)) :
    ∫ ω, f ω ∂μ = ∫ t in Ioc 0 M, μ.real {a : α | t ≤ f a} := by
  rw [f_intble.integral_eq_integral_meas_le f_nn]
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      nullMeasurableSet_Ioi Ioc_subset_Ioi_self ?_]
  apply Eventually.of_forall (fun t ht ↦ ?_)
  have htM : M < t := by simp_all only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le]
  have obs : μ {a | M < f a} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [f_bdd] with a ha using not_lt.mpr ha
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
  exact Or.inl <| measure_mono_null (fun a ha ↦ lt_of_lt_of_le htM ha) obs

end LayercakeIntegral

end MeasureTheory

