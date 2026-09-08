/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Displacement is at most the integral of the speed

In this file we prove several version of the following fact:
the displacement (`dist (f a) (f b)`) is at most the integral of `‖deriv f‖` over `[a, b]`.
-/


public section

open Filter Set MeasureTheory Measure Metric
open scoped Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

section Line

variable {f : ℝ → E} {a b : ℝ}

/-- Displacement is at most the integral of an upper estimate on the speed.

Let `f : ℝ → E` be a function which is continuous on a closed interval `[a, b]`
and is differentiable on the open interval `(a, b)`.
If `B t` is an integrable upper estimate on `‖f' t‖`, `a < t < b`,
then `‖f b - f a‖ ≤ ∫ t in a..b, B t`.
-/
/-
**norm_sub_le_integral_of_norm_deriv_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_sub_le_integral_of_norm_deriv_le_of_le {B : Real -> Real} (hab : a <=
 b) (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn Real f (Ioo a b)) (
hfB : forallᵐ t, t in Ioo a b -> ‖deriv f t‖ <= B t) (hBi : IntervalIntegrable B
 volume a b) : ‖f b - f a‖ <= ∫ t in a..b, B t
参数：hab : a <= b；hfc : ContinuousOn f (Icc a b)；hfd : DifferentiableOn Real f (Io
o a b)；hfB : forallᵐ t, t in Ioo a b -> ‖deriv f t‖ <= B t；hBi : IntervalIntegra
ble B volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc`：Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b
· 使用定理 `Filter.EventuallyLE.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : LE β] 
(l : Filter α) (f g : α → β), (f ≤ᶠ[l] g) = ∀ᶠ (x : α) in l, f x ≤ g x
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDeriv_right`：integral_eq_sub_of_h
asDeriv_right (hcont : ContinuousOn f (uIcc a b)) (hderiv : forall x in Ioo (min
 a b) (max a b), HasDerivWithinAt f (f' …
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `DifferentiableOn.hasDerivAt`：DifferentiableOn.hasDerivAt (h : Differenti
ableOn 𝕜 f s) (hs : s in 𝓝 x) : HasDerivAt f (deriv f x) x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `IntervalIntegrable.mono_fun`：mono_fun {f : Real -> E} [NormedAddCommGrou
p F] {g : Real -> F} (hf : IntervalIntegrable f μ a b) (hgm : AEStronglyMeasurab
le g (μ.restrict …
· 使用定理 `aestronglyMeasurable_deriv`：aestronglyMeasurable_deriv [MeasurableSpace 
𝕜] [OpensMeasurableSpace 𝕜] [SecondCountableTopologyEither 𝕜 F] (f : 𝕜 -> F) (μ 
: Measure 𝕜) : A…
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `intervalIntegral.norm_integral_le_of_norm_le`：norm_integral_le_of_norm_l
e {g : Real -> Real} (hab : a <= b) (h : forallᵐ t ∂μ, t in Set.Ioc a b -> ‖f t‖
 <= g t) (hbound : IntervalIntegra…
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
Displacement is at most the integral of an upper estimate on the speed.

Let `f : ℝ → E` be a function which is continuous on a closed interval `[a, b]`
and is differentiable on the open interval `(a, b)`.
If `B t` is an integrable upper estimate on `‖f' t‖`, `a < t < b`,
then `‖f b - f a‖ ≤ ∫ t in a..b, B t`.
-/
lemma norm_sub_le_integral_of_norm_deriv_le_of_le {B : ℝ → ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hfB : ∀ᵐ t, t ∈ Ioo a b → ‖deriv f t‖ ≤ B t)
    (hBi : IntervalIntegrable B volume a b) :
    ‖f b - f a‖ ≤ ∫ t in a..b, B t := by
  -- WLOG, the codomain is a complete space.
  wlog hE : CompleteSpace E generalizing E
  · set g : ℝ → UniformSpace.Completion E := (↑) ∘ f with hg
    have hgc : ContinuousOn g (Icc a b) :=
      (UniformSpace.Completion.continuous_coe E).comp_continuousOn hfc
    have hgd : DifferentiableOn ℝ g (Ioo a b) :=
      UniformSpace.Completion.toComplL.differentiable.comp_differentiableOn hfd
    have hdg t (ht : t ∈ Ioo a b) : deriv g t = deriv f t := by
      have : HasFDerivAt (𝕜 := ℝ) (↑) UniformSpace.Completion.toComplL (f t) := by
        rw [← UniformSpace.Completion.coe_toComplL (𝕜 := ℝ)]
        exact (UniformSpace.Completion.toComplL (E := E) (𝕜 := ℝ)).hasFDerivAt
      have hdft : HasDerivAt f (deriv f t) t := hfd.hasDerivAt <| Ioo_mem_nhds ht.1 ht.2
      rw [hg, (this.comp_hasDerivAt t hdft).deriv, UniformSpace.Completion.coe_toComplL]
    have hgn : ∀ᵐ t, t ∈ Ioo a b → ‖deriv g t‖ ≤ B t :=
      hfB.mono fun t htB ht ↦ by
        simpa only [hdg t ht, UniformSpace.Completion.norm_coe] using htB ht
    simpa [g, ← dist_eq_norm_sub] using this hgc hgd hgn inferInstance
  -- In a complete space, we have
  -- `‖f b - f a‖ = ‖∫ t in a..b, deriv f t‖ ≤ ∫ t in a..b, ‖deriv f t‖`
  have hfB' : (‖deriv f ·‖) ≤ᵐ[volume.restrict (uIoc a b)] B := by
    rwa [uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc, EventuallyLE,
        ae_restrict_iff' measurableSet_Ioo]
  rw [← intervalIntegral.integral_eq_sub_of_hasDeriv_right (f' := deriv f)]
  · apply intervalIntegral.norm_integral_le_of_norm_le hab _ hBi
    rwa [← ae_restrict_iff' measurableSet_Ioc, ← uIoc_of_le hab]
  · rwa [uIcc_of_le hab]
  · rw [min_eq_left hab, max_eq_right hab]
    intro t ht
    exact hfd.hasDerivAt (isOpen_Ioo.mem_nhds ht) |>.hasDerivWithinAt
  · apply hBi.mono_fun (aestronglyMeasurable_deriv _ _)
    exact hfB'.trans <| .of_forall fun _ ↦ le_abs_self _

/-- Let `f : ℝ → E` be a function which is continuous on `[a, b]` and is differentiable on `(a, b)`.
Suppose that `‖f' t‖ ≤ C` for a.e. `t ∈ (a, b)`.
Then the distance between `f a` and `f b`
is at most `C` times the measure of `x ∈ (a, b)` such that `f' x ≠ 0`.

This lemma is useful, if `f` is known to have zero derivative at most points of `[a, b]`. -/
/-
**norm_sub_le_mul_volume_of_norm_deriv_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_sub_le_mul_volume_of_norm_deriv_le_of_le {C : Real} (hab : a <= b) (h
fc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn Real f (Ioo a b)) (hnorm 
: forallᵐ t, t in Ioo a b -> ‖deriv f t‖ <= C) : ‖f b - f a‖ <= C * volume.real 
{x in Ioo a b | deriv f x != 0}
参数：hab : a <= b；hfc : ContinuousOn f (Icc a b)；hfd : DifferentiableOn Real f (Io
o a b)；hnorm : forallᵐ t, t in Ioo a b -> ‖deriv f t‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `norm_sub_le_integral_of_norm_deriv_le_of_le`：norm_sub_le_integral_of_nor
m_deriv_le_of_le {B : Real -> Real} (hab : a <= b) (hfc : ContinuousOn f (Icc a 
b)) (hfd : DifferentiableOn Real …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Set.le_indicator_apply`：∀ {α : Type u_2} {M : Type u_3} [inst : LE M] [i
nst_1 : Zero M] {s : Set α} {g : α → M} {a : α} {y : M},   (a ∈ s → y ≤ g a) → (
a ∉ s → y ≤ …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioo_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioo_of_le [NullSingletonClass μ] (hab : a <= b) (ha : ‖f a‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.IntegrableOn.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {
mα : MeasurableSpace α} {s t : Set α} {μ : MeasureTheory.Measure α}   [inst : To
pologicalSpace ε'] [inst_1…
· 使用定理 `MeasureTheory.integrableOn_const`：integrableOn_const {C : ε'} (hs : μ s 
!= ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.volume_Ioo`：volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b 
- a)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc`：Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasureTheory.setIntegral_const`：setIntegral_const [CompleteSpace E] (c 
: E) : ∫ _ in s, c ∂μ = μ.real s • c
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.Measure.measure_toMeasurable_inter_of_sFinite`：measure_toM
easurable_inter_of_sFinite [SFinite μ] {s : Set α} (hs : MeasurableSet s) (t : S
et α) : μ (toMeasurable μ t inter s) = μ (t inter…
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Let `f : ℝ → E` be a function which is continuous on `[a, b]` and is differentia
ble on `(a, b)`.
Suppose that `‖f' t‖ ≤ C` for a.e. `t ∈ (a, b)`.
Then the distance between `f a` and `f b`
is at most `C` times the measure of `x ∈ (a, b)` such that `f' x ≠ 0`.

This lemma is useful, if `f` is known to have zero derivative at most points of 
`[a, b]`.
-/
lemma norm_sub_le_mul_volume_of_norm_deriv_le_of_le {C : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hnorm : ∀ᵐ t, t ∈ Ioo a b → ‖deriv f t‖ ≤ C) :
    ‖f b - f a‖ ≤ C * volume.real {x ∈ Ioo a b | deriv f x ≠ 0} := by
  set s := toMeasurable volume {x | deriv f x ≠ 0}
  have hsm : MeasurableSet s := by measurability
  calc
    ‖f b - f a‖ ≤ ∫ t in a..b, indicator s (fun _ ↦ C) t := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le hab hfc hfd
      · refine hnorm.mono fun t ht ht_mem ↦ ?_
        apply le_indicator_apply
        · exact fun ht' ↦ ht ht_mem
        · simp only [s, norm_le_zero_iff]
          exact not_imp_comm.2 fun h ↦ subset_toMeasurable _ _ h
      · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
        refine (integrableOn_const ?_ ?_).indicator hsm <;> simp
    _ = C * volume.real {x ∈ Ioo a b | deriv f x ≠ 0} := by
      rw [intervalIntegral.integral_of_le hab, Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm,
        integral_indicator hsm, Measure.restrict_restrict hsm,
        setIntegral_const, smul_eq_mul, mul_comm]
      simp only [s, Measure.real,
        Measure.measure_toMeasurable_inter_of_sFinite measurableSet_Ioo]
      simp only [inter_def, mem_ofPred_eq, and_comm]

end Line

section NormedSpace

open AffineMap
variable {f : E → F} {a b : E} {C r : ℝ} {s : Set E}

set_option backward.isDefEq.respectTransparency.types false in
/-- Consider a function `f : E → F` continuous on a segment `[a, b]`
and line differentiable in the direction `b - a` at all points of the open segment `(a, b)`.

If `‖∂_{b - a} f‖ ≤ C` at a.e. all points of the open segment,
then `‖f b - f a‖ ≤ C * volume s`, where `s` is the set of points `t ∈ Ioo 0 1`
such that `f` has nonzero line derivative in the direction `b - a` at `lineMap a b t`. -/
/-
**norm_sub_le_mul_volume_of_norm_lineDeriv_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_sub_le_mul_volume_of_norm_lineDeriv_le (hfc : ContinuousOn f (segment
 Real a b)) (hfd : forall t in Ioo (0 : Real) 1, LineDifferentiableAt Real f (li
neMap a b t) (b - a)) (hf' : forallᵐ t : Real, t in Ioo (0 : Real) 1 -> ‖lineDer
iv Real f (lineMap a b t) (b - a)‖ <= C) : ‖f b - f a‖ <= C * volume.real {t in 
Ioo (0 : Real) 1 | lineDeriv Real f (lineMap a b t) (b - a) != 0}
参数：hfc : ContinuousOn f (segment Real a b)；hfd : forall t in Ioo (0 : Real) 1, L
ineDifferentiableAt Real f (lineMap a b t) (b - a)；hf' : forallᵐ t : Real, t in 
Ioo (0 : Real) 1 -> ‖lineDeriv Real f (lineMap a b t) (b - a)‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `AffineMap.lineMap_continuous`：lineMap_continuous {p q : P} : Continuous 
(lineMap p q : R ->ᵃ[R] P)
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_eq_image_lineMap`：segment_eq_image_lineMap (x y : E) : [x -[𝕜] y
] = AffineMap.lineMap x y '' Icc (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `HasDerivAt.scomp_of_eq`：HasDerivAt.scomp_of_eq (hg : HasDerivAt g₁ g₁' y
) (hh : HasDerivAt h h' x) (hy : y = h x) : HasDerivAt (g₁ ∘ h) (h' • g₁') x
· 使用定理 `LineDifferentiableAt.hasLineDerivAt`：LineDifferentiableAt.hasLineDerivAt
 (h : LineDifferentiableAt 𝕜 f x v) : HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v
· 使用定理 `HasDerivAt.sub_const`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `add_add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a + c + (b - c) = a + b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `norm_sub_le_mul_volume_of_norm_deriv_le_of_le`：norm_sub_le_mul_volume_of
_norm_deriv_le_of_le {C : Real} (hab : a <= b) (hfc : ContinuousOn f (Icc a b)) 
(hfd : DifferentiableOn Real f (Ioo…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a function `f : E → F` continuous on a segment `[a, b]`
and line differentiable in the direction `b - a` at all points of the open segme
nt `(a, b)`.

If `‖∂_{b - a} f‖ ≤ C` at a.e. all points of the open segment,
then `‖f b - f a‖ ≤ C * volume s`, where `s` is the set of points `t ∈ Ioo 0 1`
such that `f` has nonzero line derivative in the direction `b - a` at `lineMap a
 b t`.
-/
lemma norm_sub_le_mul_volume_of_norm_lineDeriv_le
    (hfc : ContinuousOn f (segment ℝ a b))
    (hfd : ∀ t ∈ Ioo (0 : ℝ) 1, LineDifferentiableAt ℝ f (lineMap a b t) (b - a))
    (hf' : ∀ᵐ t : ℝ, t ∈ Ioo (0 : ℝ) 1 → ‖lineDeriv ℝ f (lineMap a b t) (b - a)‖ ≤ C) :
    ‖f b - f a‖ ≤
      C * volume.real {t ∈ Ioo (0 : ℝ) 1 | lineDeriv ℝ f (lineMap a b t) (b - a) ≠ 0} := by
  set g : ℝ → F := fun t ↦ f (lineMap a b t)
  have hgc : ContinuousOn g (Icc 0 1) := by
    refine hfc.comp ?_ ?_
    · exact AffineMap.lineMap_continuous.continuousOn
    · simp [segment_eq_image_lineMap, mapsTo_image]
  have hdg (t : ℝ) (ht : t ∈ Ioo 0 1) : HasDerivAt g (lineDeriv ℝ f (lineMap a b t) (b - a)) t := by
    have := (hfd t ht).hasLineDerivAt.scomp_of_eq (𝕜 := ℝ) t ((hasDerivAt_id t).sub_const t)
    simpa [g, lineMap_apply_module', Function.comp_def, sub_smul, add_comm _ a] using this
  suffices ‖g 1 - g 0‖ ≤ C * volume.real {t ∈ Ioo 0 1 | deriv g t ≠ 0} by
    convert! this using 1
    · simp [g]
    · congr 2 with t
      simp +contextual [(hdg _ _).deriv]
  apply norm_sub_le_mul_volume_of_norm_deriv_le_of_le zero_le_one hgc
  · exact fun t ht ↦ (hdg t ht).differentiableAt.differentiableWithinAt
  · exact hf'.mono fun t ht ht_mem ↦ by simpa only [(hdg t ht_mem).deriv] using ht ht_mem

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `f : E → F` be a function differentiable on a set `s` and continuous on its closure.
Let `a`, `b` be two points such that the open segment connecting `a` to `b` is a subset of `s`.

If `‖Df‖ ≤ C` everywhere on `s` then `‖f b - f a‖ ≤ C * volume u`,
where `u` is the set of points `t ∈ Ioo 0 1`
such that `f` has nonzero derivative at `lineMap a b t`. -/
/-
**norm_sub_le_mul_volume_of_norm_fderiv_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_sub_le_mul_volume_of_norm_fderiv_le (hs : IsOpen s) (hf : DiffContOnC
l Real f s) (hab : openSegment Real a b subseteq s) (hC : forall x in s, ‖fderiv
 Real f x‖ <= C) : ‖f b - f a‖ <= C * ‖b - a‖ * volume.real {t in Ioo (0 : Real)
 1 | fderiv Real f (lineMap a b t) != 0}
参数：hs : IsOpen s；hf : DiffContOnCl Real f s；hab : openSegment Real a b subseteq 
s；hC : forall x in s, ‖fderiv Real f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lineMap_mem_openSegment`：lineMap_mem_openSegment (a b : E) {t : 𝕜} (ht :
 t in Ioo 0 1) : AffineMap.lineMap a b t in openSegment 𝕜 a b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
· 使用定理 `segment_subset_closure_openSegment`：segment_subset_closure_openSegment :
 [x -[𝕜] y] subseteq closure (openSegment 𝕜 x y)
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
Let `f : E → F` be a function differentiable on a set `s` and continuous on its 
closure.
Let `a`, `b` be two points such that the open segment connecting `a` to `b` is a
 subset of `s`.

If `‖Df‖ ≤ C` everywhere on `s` then `‖f b - f a‖ ≤ C * volume u`,
where `u` is the set of points `t ∈ Ioo 0 1`
such that `f` has nonzero derivative at `lineMap a b t`.
-/
lemma norm_sub_le_mul_volume_of_norm_fderiv_le (hs : IsOpen s) (hf : DiffContOnCl ℝ f s)
    (hab : openSegment ℝ a b ⊆ s) (hC : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ C) :
    ‖f b - f a‖ ≤
      C * ‖b - a‖ * volume.real {t ∈ Ioo (0 : ℝ) 1 | fderiv ℝ f (lineMap a b t) ≠ 0} := by
  have hmem_s : ∀ t ∈ Ioo (0 : ℝ) 1, lineMap a b t ∈ s := fun t ht ↦
    hab <| lineMap_mem_openSegment _ a b ht
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans <| hC _ <| hmem_s (1 / 2) (by norm_num)
  have hfc : ContinuousOn f (segment ℝ a b) :=
    hf.continuousOn.mono <| segment_subset_closure_openSegment.trans <| closure_mono hab
  have hfd : ∀ t ∈ Ioo (0 : ℝ) 1, LineDifferentiableAt ℝ f (lineMap a b t) (b - a) := fun t ht ↦
    (hf.differentiableAt hs <| hmem_s t ht).lineDifferentiableAt
  have hfC : ∀ t ∈ Ioo (0 : ℝ) 1, ‖lineDeriv ℝ f (lineMap a b t) (b - a)‖ ≤ C * ‖b - a‖ := by
    intro t ht
    rw [DifferentiableAt.lineDeriv_eq_fderiv]
    · exact ContinuousLinearMap.le_of_opNorm_le _ (hC _ <| hmem_s t ht) _
    · exact hf.differentiableAt hs <| hmem_s t ht
  refine norm_sub_le_mul_volume_of_norm_lineDeriv_le hfc hfd (.of_forall hfC) |>.trans ?_
  gcongr
  · refine ne_top_of_le_ne_top ?_ (measure_mono inter_subset_left)
    simp
  · simp +contextual [(hf.differentiableAt hs <| hmem_s _ ‹_›).lineDeriv_eq_fderiv]

/-- Let `f : E → F` be a function differentiable in a neighborhood of `a`.
If $Df(x) = O(‖x - a‖ ^ r)$ as `x → a`, where `r ≥ 0`,
then $f(x) - f(a) = O(‖x - a‖ ^ {r + 1})$ as `x → a`. -/
/-
**sub_isBigO_norm_rpow_add_one_of_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_isBigO_norm_rpow_add_one_of_fderiv (hr : 0 <= r) (hdf : forallᶠ x in 𝓝
 a, DifferentiableAt Real f x) (hderiv : fderiv Real f =O[𝓝 a] (‖· - a‖ ^ r)) : 
(f · - f a) =O[𝓝 a] (‖· - a‖ ^ (r + 1))
参数：hr : 0 <= r；hdf : forallᶠ x in 𝓝 a, DifferentiableAt Real f x；hderiv : fderiv
 Real f =O[𝓝 a] (‖· - a‖ ^ r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.eventually_nhds_iff_ball`：eventually_nhds_iff_ball {p : α -> Prop
} : (forallᶠ y in 𝓝 x, p y) ↔ exists ε > 0, forall y in ball x ε, p y
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Asymptotics.IsBigO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}   (
c : ℝ), (∀ᶠ (x : …
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Real.rpow_add_one'`：rpow_add_one' (hx : 0 <= x) (h : y + 1 != 0) : x ^ (
y + 1) = x ^ y * x
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Metric.closedBall_subset_ball`：closedBall_subset_ball (h : ε₁ < ε₂) : cl
osedBall x ε₁ subseteq ball x ε₂
· 使用定理 `mem_ball_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] {a
 b : E} {r : ℝ}, b ∈ Metric.ball a r ↔ ‖b - a‖ < r
· 使用定理 `Convex.norm_image_sub_le_of_norm_fderiv_le`：norm_image_sub_le_of_norm_fd
eriv_le (hf : forall x in s, DifferentiableAt 𝕜 f x) (bound : forall x in s, ‖fd
eriv 𝕜 f x‖ <= C) (hs : Convex R…
· 使用定理 `instIsRCLikeNormedField`：∀ (𝕜 : Type u_3) [h : RCLike 𝕜], IsRCLikeNormed
Field 𝕜
· 使用定理 `convex_closedBall`：convex_closedBall (a : E) (r : Real) : Convex Real (c
losedBall a r)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Let `f : E → F` be a function differentiable in a neighborhood of `a`.
If $Df(x) = O(‖x - a‖ ^ r)$ as `x → a`, where `r ≥ 0`,
then $f(x) - f(a) = O(‖x - a‖ ^ {r + 1})$ as `x → a`.
-/
theorem sub_isBigO_norm_rpow_add_one_of_fderiv (hr : 0 ≤ r)
    (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x) (hderiv : fderiv ℝ f =O[𝓝 a] (‖· - a‖ ^ r)) :
    (f · - f a) =O[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  rcases hderiv.exists_pos with ⟨C, hC₀, hC⟩
  rw [Asymptotics.IsBigOWith_def] at hC
  rcases eventually_nhds_iff_ball.mp (hdf.and hC) with ⟨ε, hε₀, hε⟩
  refine .of_bound C ?_
  rw [eventually_nhds_iff_ball]
  refine ⟨ε, hε₀, fun y hy ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_add_one' (by positivity) (by positivity),
    ← mul_assoc]
  have hsub : closedBall a ‖y - a‖ ⊆ ball a ε :=
    closedBall_subset_ball (mem_ball_iff_norm.mp hy)
  apply (convex_closedBall a ‖y - a‖).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
  · exact fun z hz ↦ (hε z <| hsub hz).1
  · intro z hz
    grw [(hε z <| hsub hz).2, Real.norm_of_nonneg (by positivity), mem_closedBall_iff_norm.mp hz]
  · simp
  · simp [dist_eq_norm_sub]

/-- Let `f : E → F` be a function differentiable in a neighborhood of `a`.
If $Df(x) = O(‖x - a‖ ^ r)$ as `x → a`, where `r ≥ 0`, and `f a = 0`,
then $f(x) = O(‖x - a‖ ^ {r + 1})$ as `x → a`. -/
/-
**isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero (hr : 0 <= r) (hdf : f
orallᶠ x in 𝓝 a, DifferentiableAt Real f x) (hderiv : fderiv Real f =O[𝓝 a] (‖· 
- a‖ ^ r)) (hf₀ : f a = 0) : f =O[𝓝 a] (‖· - a‖ ^ (r + 1))
参数：hr : 0 <= r；hdf : forallᶠ x in 𝓝 a, DifferentiableAt Real f x；hderiv : fderiv
 Real f =O[𝓝 a] (‖· - a‖ ^ r)；hf₀ : f a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_isBigO_norm_rpow_add_one_of_fderiv`：sub_isBigO_norm_rpow_add_one_of_
fderiv (hr : 0 <= r) (hdf : forallᶠ x in 𝓝 a, DifferentiableAt Real f x) (hderiv
 : fderiv Real f =O[𝓝 a] (‖·…

--- 原说明 ---
Let `f : E → F` be a function differentiable in a neighborhood of `a`.
If $Df(x) = O(‖x - a‖ ^ r)$ as `x → a`, where `r ≥ 0`, and `f a = 0`,
then $f(x) = O(‖x - a‖ ^ {r + 1})$ as `x → a`.
-/
theorem isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero (hr : 0 ≤ r)
    (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x) (hderiv : fderiv ℝ f =O[𝓝 a] (‖· - a‖ ^ r))
    (hf₀ : f a = 0) :
    f =O[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  simpa [hf₀] using sub_isBigO_norm_rpow_add_one_of_fderiv hr hdf hderiv

end NormedSpace

