/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Tight

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# Lévy's convergence theorem

This file contains developments related to Lévy's convergence theorem, which links convergence of
characteristic functions and convergence in distribution in finite dimensional inner product spaces.

## Main statements

* `isTightMeasureSet_of_tendsto_charFun`: if the characteristic functions of a sequence of measures
  `μ : ℕ → Measure E` on a finite dimensional inner product space converge pointwise
  to a function which is continuous at 0, then `{μ n | n}` is tight.
* `ProbabilityMeasure.tendsto_iff_tendsto_charFun`: the weak convergence of probability measures is
  equivalent to the pointwise convergence of their characteristic functions.

-/

public section

open Filter BoundedContinuousFunction Real RCLike
open scoped Topology RealInnerProductSpace ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- If the characteristic functions of a sequence of measures `μ : ℕ → Measure E` converge pointwise
to a function which is continuous at 0, then `{μ n | n}` is tight. -/
/-
**MeasureTheory.isTightMeasureSet_of_tendsto_charFun** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory`。
形式化陈述：isTightMeasureSet_of_tendsto_charFun {μ : Nat -> Measure E} [forall i, IsP
robabilityMeasure (μ i)] {f : E -> Complex} (hf : ContinuousAt f 0) (h : forall 
t, Tendsto (fun n => charFun (μ n) t) atTop (𝓝 (f t))) : IsTightMeasureSet (Set.
range μ)
参数：μ i；hf : ContinuousAt f 0；h : forall t, Tendsto (fun n => charFun (μ n) t) at
Top (𝓝 (f t))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.isTightMeasureSet_range_of_tendsto_limsup_measureReal_inne
r_of_norm_eq_one`：isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of
_norm_eq_one (h : forall y, ‖y‖ = 1 -> Tendsto (fun r : Real => limsup (fun n …
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_le_self_iff`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [IsOrderedAddMonoid α] {a : α}, -a ≤ a ↔ 0 ≤ a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `intervalIntegral.norm_integral_le_integral_norm`：norm_integral_le_integr
al_norm (h : a <= b) : ‖∫ x in a..b, f x ∂μ‖ <= ∫ x in a..b, ‖f x‖ ∂μ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用引理 `MeasureTheory.integral_mono_of_nonneg`：integral_mono_of_nonneg {f g : α 
-> E} (hf : 0 <=ᵐ[μ] f) (hgi : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ a, f a ∂μ <=
 ∫ a, g a ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
（共 199 条，此处仅展示前 30 条）

--- 原说明 ---
If the characteristic functions of a sequence of measures `μ : ℕ → Measure E` co
nverge pointwise
to a function which is continuous at 0, then `{μ n | n}` is tight.
-/
lemma isTightMeasureSet_of_tendsto_charFun {μ : ℕ → Measure E} [∀ i, IsProbabilityMeasure (μ i)]
    {f : E → ℂ} (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (f t))) :
    IsTightMeasureSet (Set.range μ) := by
  -- it suffices to show that a limsup tends to 0
  refine isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one ℝ
    (fun z hz ↦ ?_) 1 (.of_forall fun _ ↦ by simp)
  -- first, prove an auxiliary inequality that will be used to bound the limsup
  have h_le_4 n r (hr : 0 < r) :
      2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖ ≤ 4 := by
    have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
    calc 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖
    _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - charFun (μ n) (t • z)‖ := by
      grw [neg_mul, intervalIntegral.norm_integral_le_integral_norm hr']
    _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, 2 := by
      gcongr
      rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
      refine integral_mono_of_nonneg ?_ (by fun_prop) ?_
      · exact ae_of_all _ fun _ ↦ by positivity
      · exact ae_of_all _ fun _ ↦ norm_one_sub_charFun_le_two
    _ ≤ 4 := by
      simp only [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul]
      field_simp
      norm_num
  have h_le n r (hr : 0 < r) : (μ n).real {x | r < |⟪z, x⟫|} ≤
      2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖ :=
    measureReal_abs_inner_gt_le_integral_charFun hr
  -- We introduce an upper bound for the limsup.
  -- This is where we use that `charFun (μ n)` converges to `f`.
  have h_limsup_le r (hr : 0 < r) :
      limsup (fun n ↦ (μ n).real {x | r < |⟪z, x⟫|}) atTop
        ≤ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖ := by
    calc limsup (fun n ↦ (μ n).real {x | r < |⟪z, x⟫|}) atTop
    _ ≤ limsup (fun n ↦ 2⁻¹ * r
        * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖) atTop := by
      refine limsup_le_limsup (.of_forall fun n ↦ h_le n r hr) ?_ ?_
      · exact IsCoboundedUnder.of_frequently_ge <| .of_forall fun _ ↦ ENNReal.toReal_nonneg
      · refine ⟨4, ?_⟩
        simp only [eventually_map, eventually_atTop]
        exact ⟨0, fun n _ ↦ h_le_4 n r hr⟩
    _ = 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖ := by
      refine ((Tendsto.norm ?_).const_mul _).limsup_eq
      simp only [neg_mul]
      have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
      simp_rw [intervalIntegral.integral_of_le hr']
      refine tendsto_integral_of_dominated_convergence (fun _ ↦ 2) ?_ (by fun_prop) ?_ ?_
      · exact fun _ ↦ Measurable.aestronglyMeasurable <| by fun_prop
      · exact fun _ ↦ ae_of_all _ fun _ ↦ norm_one_sub_charFun_le_two
      · exact ae_of_all _ fun _ ↦ tendsto_const_nhds.sub (h _)
  -- It suffices to show that the upper bound tends to 0.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (h := fun r ↦ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖) ?_ ?_ ?_
  rotate_left
  · filter_upwards [eventually_gt_atTop 0] with r hr
    refine le_limsup_of_le ?_ fun u hu ↦ ?_
    · refine ⟨4, ?_⟩
      simp only [eventually_map, eventually_atTop]
      exact ⟨0, fun n _ ↦ (h_le n r hr).trans (h_le_4 n r hr)⟩
    · exact ENNReal.toReal_nonneg.trans hu.exists.choose_spec
  · filter_upwards [eventually_gt_atTop 0] with r hr using h_limsup_le r hr
  -- We now show that the upper bound tends to 0.
  -- This will follow from the fact that `f` is continuous at `0`.
  -- `⊢ Tendsto (fun r ↦ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖) atTop (𝓝 0)`
  have hf_tendsto := hf.tendsto
  rw [Metric.tendsto_nhds_nhds] at hf_tendsto
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hf0 : f 0 = 1 := by symm; simpa using h 0
  simp only [gt_iff_lt, dist_eq_norm_sub', zero_sub, norm_neg, hf0] at hf_tendsto
  simp only [ge_iff_le, neg_mul, dist_zero_right, norm_mul, norm_inv,
    Real.norm_ofNat, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  obtain ⟨δ, hδ, hδ_lt⟩ : ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ < δ → ‖1 - f x‖ < ε / 4 :=
    hf_tendsto (ε / 4) (by positivity)
  refine ⟨4 * δ⁻¹, fun r hrδ ↦ ?_⟩
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hrδ
  have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
  have h_le_Ioc x (hx : x ∈ Set.Ioc (-(2 * r⁻¹)) (2 * r⁻¹)) : ‖1 - f (x • z)‖ ≤ ε / 4 := by
    refine (hδ_lt ?_).le
    simp only [norm_smul, Real.norm_eq_abs, mul_one, hz]
    calc |x|
    _ ≤ 2 * r⁻¹ := by grind
    _ < δ := by
      rw [← lt_div_iff₀' (by positivity), inv_lt_comm₀ hr (by positivity)]
      refine lt_of_lt_of_le ?_ hrδ
      field_simp
      norm_num
  rw [abs_of_nonneg hr.le]
  calc 2⁻¹ * r * ‖∫ t in -(2 * r⁻¹)..2 * r⁻¹, 1 - f (t • z)‖
  _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - f (t • z)‖ := by
    grw [intervalIntegral.norm_integral_le_integral_norm hr']
  _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ε / 4 := by
    gcongr
    rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
    have hf_meas : Measurable f := by
      refine measurable_of_tendsto_metrizable (f := fun n t ↦ charFun (μ n) t) (by fun_prop) ?_
      rwa [tendsto_pi_nhds]
    refine integral_mono_ae ?_ (by fun_prop) ?_
    · refine Integrable.mono' (integrable_const (ε / 4)) ?_ ?_
      · exact Measurable.aestronglyMeasurable <| by fun_prop
      · simpa using ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
    · exact ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
  _ = ε / 2 := by simp; field
  _ < ε := by simp [hε]

/-- Let `μ` be a tight sequence of probability measures and `μ₀` a probability measure.
If `A` is a star sub-algebra of bounded continuous scalar functions that separates points
and the integrals of elements of `A` with respect to `μ` converge to the integrals
with respect to `μ₀`, then `μ` converges weakly to `μ₀`. -/
/-
**MeasureTheory.ProbabilityMeasure.tendsto_of_tight_of_separatesPoints** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ (𝕜 : Type u_2) [inst : RCLike 𝕜] {E : Type u_3} [inst_1 : MeasurableSpac
e E] [inst_2 : TopologicalSpace E]   [PolishSpace E] [inst_4 : BorelSpace E] {ι 
: Type u_4} {𝓕 : Filter ι} {μ : ι → MeasureTheory.ProbabilityMeasure E},   Measu
reTheory.IsTightMeasureSet {x | ∃ n, ↑(μ n) = x} →     ∀ {μ₀ : MeasureTheory.Pro
babilityMeasure E} {A : StarSubalgebra 𝕜 (BoundedContinuousFunction E 𝕜)},      
 (StarSubalgebra.map (BoundedContinuousFunction.toContinuousMapStarₐ 𝕜) A).Separ
atesPoints →         (∀ g ∈ A, Filter.Tendsto (fun n => ∫ (x : E), g x ∂↑(μ n)) 
𝓕 (nhds (∫ (x : E), g x ∂↑μ₀))) →           Filter.Tendsto μ 𝓕 (nhds μ₀)
参数：𝕜 : Type u_2；μ n；BoundedContinuousFunction E 𝕜；StarSubalgebra.map (BoundedCon
tinuousFunction.toContinuousMapStarₐ 𝕜) A；∀ g ∈ A, Filter.Tendsto (fun n => ∫ (x
 : E), g x ∂↑(μ n)) 𝓕 (nhds (∫ (x : E), g x ∂↑μ₀))；nhds μ₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_iff_ultrafilter`：tendsto_iff_ultrafilter (f : α -> β) (l₁
 : Filter α) (l₂ : Filter β) : Tendsto f l₁ l₂ ↔ forall g : Ultrafilter α, ↑g <=
 l₁ -> Tendsto f g l…
· 使用引理 `isCompact_closure_of_isTightMeasureSet`：isCompact_closure_of_isTightMeas
ureSet {S : Set (ProbabilityMeasure E)} (hS : IsTightMeasureSet {((μ : Probabili
tyMeasure E) : Measure E) | …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCompact.ultrafilter_le_nhds`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X},   IsCompact s → ∀ (f : Ultrafilter X), ↑f ≤ Filter.principal s → 
∃ x ∈ s, ↑f ≤ nhds …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Let `μ` be a tight sequence of probability measures and `μ₀` a probability measu
re.
If `A` is a star sub-algebra of bounded continuous scalar functions that separat
es points
and the integrals of elements of `A` with respect to `μ` converge to the integra
ls
with respect to `μ₀`, then `μ` converges weakly to `μ₀`.
-/
lemma ProbabilityMeasure.tendsto_of_tight_of_separatesPoints (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
    {ι : Type*} {𝓕 : Filter ι}
    {μ : ι → ProbabilityMeasure E} (h_tight : IsTightMeasureSet {(μ n : Measure E) | n})
    {μ₀ : ProbabilityMeasure E}
    {A : StarSubalgebra 𝕜 (E →ᵇ 𝕜)} (hA : (A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints)
    (hμ : ∀ g ∈ A, Tendsto (fun n ↦ ∫ x, g x ∂(μ n)) 𝓕 (𝓝 (∫ x, g x ∂μ₀))) :
    Tendsto μ 𝓕 (𝓝 μ₀) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable E
  obtain rfl | _ := 𝓕.eq_or_neBot
  · simp
  refine (Filter.tendsto_iff_ultrafilter _ _ _).2 fun U hU ↦ ?_
  have h_compact : IsCompact (closure {μ n | n}) :=
    isCompact_closure_of_isTightMeasureSet (by simpa using h_tight)
  obtain ⟨μ', -, hμ' : Tendsto _ _ _⟩ := h_compact.ultrafilter_le_nhds (U.map μ)
    (.trans (by simp) (monotone_principal subset_closure))
  suffices (μ' : Measure E) = μ₀ by convert! hμ'; ext; rw [this]
  refine ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable hA
    fun g hg ↦ tendsto_nhds_unique ?_ ((hμ g hg).comp hU)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜] at hμ'
  exact hμ' g

variable {ι : Type*} {𝓕 : Filter ι} {μ₀ : ProbabilityMeasure E}

set_option backward.isDefEq.respectTransparency.types false in
omit [FiniteDimensional ℝ E] in
/-
**MeasureTheory.ProbabilityMeasure.tendsto_charPoly_of_tendsto_charFun** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : MeasurableSpace E]   [BorelSpace E] {ι : Type u_2} {𝓕 : Filter ι
} {μ₀ : MeasureTheory.ProbabilityMeasure E}   {μ : ι → MeasureTheory.Probability
Measure E},   (∀ (t : E), Filter.Tendsto (fun n => MeasureTheory.charFun (↑(μ n)
) t) 𝓕 (nhds (MeasureTheory.charFun (↑μ₀) t))) →     ∀ {g : BoundedContinuousFun
ction E ℂ},       g ∈ BoundedContinuousFunction.charPoly Real.continuous_probCha
r ⋯ →         Filter.Tendsto (fun n => ∫ (x : E), g x ∂↑(μ n)) 𝓕 (nhds (∫ (x : E
), g x ∂↑μ₀))
参数：∀ (t : E), Filter.Tendsto (fun n => MeasureTheory.charFun (↑(μ n)) t) 𝓕 (nhds
 (MeasureTheory.charFun (↑μ₀) t))；fun n => ∫ (x : E), g x ∂↑(μ n)；nhds (∫ (x : E
), g x ∂↑μ₀)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `Real.continuous_probChar`：continuous_probChar : Continuous probChar
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `BoundedContinuousFunction.mem_charPoly`：mem_charPoly (f : V ->ᵇ Complex)
 : f in charPoly he hL ↔ exists w : AddMonoidAlgebra Complex W, f = fun x => w.c
oeff.sum (fun a z => z * (e …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.integral_finsetSum`：integral_finsetSum {ι} (s : Finset ι) 
{f : ι -> α -> G} (hf : forall i in s, Integrable (f i) μ) : ∫ a, ∑ i in s, f i 
a ∂μ = ∑ i in s, ∫ a, …
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用引理 `BoundedContinuousFunction.integrable`：integrable [IsFiniteMeasure μ] (f 
: X ->ᵇ E) : Integrable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
（共 37 条，此处仅展示前 30 条）
-/
lemma ProbabilityMeasure.tendsto_charPoly_of_tendsto_charFun {μ : ι → ProbabilityMeasure E}
    (h : ∀ t : E, Tendsto (fun n ↦ charFun (μ n) t) 𝓕 (𝓝 (charFun μ₀ t)))
    {g : E →ᵇ ℂ} (hg : g ∈ charPoly continuous_probChar (L := innerₗ E) continuous_inner) :
    Tendsto (fun n ↦ ∫ x, g x ∂(μ n)) 𝓕 (𝓝 (∫ x, g x ∂μ₀)) := by
  rw [mem_charPoly] at hg
  obtain ⟨w, hw⟩ := hg
  have h_eq (μ : Measure E) (hμ : IsProbabilityMeasure μ) :
      ∫ x, g x ∂μ = w.coeff.sum (fun a z ↦ z * ∫ x, (probChar (innerₗ E x a) : ℂ) ∂μ) := by
    simp_rw [hw, Finsupp.sum]
    rw [integral_finsetSum]
    · congr with y
      rw [integral_const_mul]
    · refine fun i hi ↦ Integrable.const_mul ?_ _
      change Integrable (innerProbChar i) μ
      exact BoundedContinuousFunction.integrable μ _
  simp_rw [h_eq (μ _), h_eq μ₀]
  refine tendsto_finsetSum _ fun y hy ↦ Tendsto.const_mul _ ?_
  simpa [← charFun_eq_integral_probChar] using h y

variable {μ : ℕ → ProbabilityMeasure E}

/-- If the characteristic functions of a sequence of probability measures converge pointwise to
the characteristic function of a probability measure, then the measures converge weakly. -/
/-
**MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [FiniteDimensional ℝ E]   [inst_3 : MeasurableSpace E] [inst_4 : BorelSpac
e E] {μ₀ : MeasureTheory.ProbabilityMeasure E}   {μ : ℕ → MeasureTheory.Probabil
ityMeasure E},   (∀ (t : E),       Filter.Tendsto (fun n => MeasureTheory.charFu
n (↑(μ n)) t) Filter.atTop (nhds (MeasureTheory.charFun (↑μ₀) t))) →     Filter.
Tendsto μ Filter.atTop (nhds μ₀)
参数：∀ (t : E),       Filter.Tendsto (fun n => MeasureTheory.charFun (↑(μ n)) t) F
ilter.atTop (nhds (MeasureTheory.charFun (↑μ₀) t))；nhds μ₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.isTightMeasureSet_of_tendsto_charFun`：isTightMeasureSet_of
_tendsto_charFun {μ : Nat -> Measure E} [forall i, IsProbabilityMeasure (μ i)] {
f : E -> Complex} (hf : ContinuousAt f 0…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用引理 `MeasureTheory.continuous_charFun`：continuous_charFun : Continuous (charF
un μ)
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`：∀ 
(𝕜 : Type u_2) [inst : RCLike 𝕜] {E : Type u_3} [inst_1 : MeasurableSpace E] [in
st_2 : TopologicalSpace E]   [PolishSpace E] [inst_4 : Bor…
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Real.continuous_probChar`：continuous_probChar : Continuous probChar
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
· 使用引理 `BoundedContinuousFunction.separatesPoints_charPoly`：separatesPoints_char
Poly (he : Continuous e) (he' : e != 1) (hL : Continuous fun p : V × W => L p.1 
p.2) (hL' : forall v != 0, L v != 0) : (…
· 使用定理 `Real.probChar_ne_one`：probChar_ne_one : probChar != 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
· 使用定理 `inner_self_ne_zero`：inner_self_ne_zero {x : E} : ⟪x, x⟫ != 0 ↔ x != 0
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_charPoly_of_tendsto_charFun`：∀ 
{E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [i
nst_2 : MeasurableSpace E]   [BorelSpace E] {ι : Type u_2}…

--- 原说明 ---
If the characteristic functions of a sequence of probability measures converge p
ointwise to
the characteristic function of a probability measure, then the measures converge
 weakly.
-/
lemma ProbabilityMeasure.tendsto_of_tendsto_charFun
    (h : ∀ t : E, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (charFun μ₀ t))) :
    Tendsto μ atTop (𝓝 μ₀) := by
  have h_tight : IsTightMeasureSet (𝓧 := E) {μ n | n} :=
    isTightMeasureSet_of_tendsto_charFun (by fun_prop) h
  refine tendsto_of_tight_of_separatesPoints h_tight (𝕜 := ℂ)
    (A := charPoly continuous_probChar (L := innerₗ E) continuous_inner) ?_ ?_
  · refine separatesPoints_charPoly continuous_probChar probChar_ne_one _ ?_
    exact fun v hv ↦ DFunLike.ne_iff.mpr ⟨v, inner_self_ne_zero.mpr hv⟩
  · exact fun g ↦ tendsto_charPoly_of_tendsto_charFun h

/-- The **Lévy convergence theorem**: the weak convergence of probability measures is equivalent
to the pointwise convergence of their characteristic functions. -/
/-
**MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [FiniteDimensional ℝ E]   [inst_3 : MeasurableSpace E] [inst_4 : BorelSpac
e E] {μ₀ : MeasureTheory.ProbabilityMeasure E}   {μ : ℕ → MeasureTheory.Probabil
ityMeasure E},   Filter.Tendsto μ Filter.atTop (nhds μ₀) ↔     ∀ (t : E),       
Filter.Tendsto (fun n => MeasureTheory.charFun (↑(μ n)) t) Filter.atTop (nhds (M
easureTheory.charFun (↑μ₀) t))
参数：nhds μ₀；t : E；fun n => MeasureTheory.charFun (↑(μ n)) t；nhds (MeasureTheory.c
harFun (↑μ₀) t)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.charFun_eq_integral_innerProbChar`：charFun_eq_integral_inn
erProbChar : charFun μ t = ∫ v, innerProbChar t v ∂μ
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tend
sto`：tendsto_iff_forall_integral_rclike_tendsto {γ : Type*} (𝕜 : Type*) [RCLike 
𝕜] {F : Filter γ} {μs : γ -> ProbabilityMeasure Ω} {μ : Probabili…
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun`：∀ {E : Type
 u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [FiniteDime
nsional ℝ E]   [inst_3 : MeasurableSpace E] [inst…

--- 原说明 ---
The **Lévy convergence theorem**: the weak convergence of probability measures i
s equivalent
to the pointwise convergence of their characteristic functions.
-/
theorem ProbabilityMeasure.tendsto_iff_tendsto_charFun :
    Tendsto μ atTop (𝓝 μ₀) ↔
      ∀ t : E, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (charFun μ₀ t)) := by
  refine ⟨fun h t ↦ ?_, tendsto_of_tendsto_charFun⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at h
  simp_rw [charFun_eq_integral_innerProbChar]
  exact h (innerProbChar t)

end MeasureTheory

