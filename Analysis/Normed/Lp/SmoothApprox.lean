/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!

# Density of smooth compactly supported functions in `Lp`

In this file, we prove that `Lp` functions can be approximated by smooth compactly supported
functions for `p < ∞`.

This result is recorded in `MeasureTheory.MemLp.exist_sub_eLpNorm_le`.
-/

public section

variable {α β E F : Type*} [MeasurableSpace E] [NormedAddCommGroup F]

open scoped Nat NNReal ContDiff
open MeasureTheory Pointwise ENNReal

namespace HasCompactSupport

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedSpace ℝ F]

/-- For every continuous compactly supported function `f` there exists a smooth compactly supported
function `g` such that `f - g` is arbitrary small in the `Lp`-norm for `p < ∞`. -/
/-
**HasCompactSupport.exist_eLpNorm_sub_le_of_continuous** 是 Mathlib 中的一个定理，位于命名空间
 `HasCompactSupport`。
形式化陈述：exist_eLpNorm_sub_le_of_continuous (μ : Measure E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Continuous.exists_contDiff_approx`：Continuous.exists_contDiff_approx (n 
: Nat∞) (f_cont : Continuous f) (ε_cont : Continuous ε) (ε_pos : forall x, 0 < ε
 x) : exists g : E -> F…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `HasCompactSupport.mono`：∀ {α : Type u_2} {β : Type u_4} {γ : Type u_5} [
inst : TopologicalSpace α] [inst_1 : Zero β] [inst_2 : Zero γ]   {f : α → β} {f'
 : α → γ}, H…
· 使用定理 `MeasureTheory.eLpNormEssSup_le_of_ae_bound`：eLpNormEssSup_le_of_ae_bound
 {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : eLpNormEssSup f μ <=
 ENNReal.ofReal C
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `MeasureTheory.pos_mono`：pos_mono ⦃s t : Set α⦄ (h : s subseteq t) (hs : 
0 < μ s) : 0 < μ t
· 使用定理 `subset_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst_1
 : TopologicalSpace X] (f : X → α),   Function.support f ⊆ tsupport f
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `MeasureTheory.Measure.measure_support_eq_zero_iff`：measure_support_eq_ze
ro_iff {E : Type*} [Zero E] (μ : Measure α
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
For every continuous compactly supported function `f` there exists a smooth comp
actly supported
function `g` such that `f - g` is arbitrary small in the `Lp`-norm for `p < ∞`.
-/
theorem exist_eLpNorm_sub_le_of_continuous (μ : Measure E := by volume_tac)
    [IsFiniteMeasureOnCompacts μ] {p : ℝ≥0∞} {ε : ℝ} (hε : 0 < ε) {f : E → F}
    (h₁ : HasCompactSupport f) (h₂ : Continuous f) :
    ∃ (g : E → F), HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
    eLpNorm (f - g) p μ ≤ ENNReal.ofReal ε := by
  rcases eq_or_ne p ∞ with rfl | hp
  · obtain ⟨g, hg₁, hg₂, hg₃⟩ := h₂.exists_contDiff_approx ⊤ (ε := fun _ ↦ ε) (by fun_prop)
      (by intro; positivity)
    refine ⟨g, h₁.mono hg₃, hg₁, eLpNormEssSup_le_of_ae_bound (.of_forall fun x ↦ ?_)⟩
    simpa [← dist_eq_norm_sub'] using (hg₂ x).le
  by_cases hf : f =ᵐ[μ] 0
  -- We will need that the support is non-empty, so we treat the trivial case `f = 0` first.
  · use 0
    simpa [HasCompactSupport.zero, eLpNorm_congr_ae hf] using! contDiff_const
  have hs₁ : μ (tsupport f) ≠ ⊤ := h₁.measure_lt_top.ne
  have hs₂ : 0 < (μ <| tsupport f).toReal := by
    -- Since `f` is not the zero function `tsupport f` has positive measure
    rw [← Measure.measure_support_eq_zero_iff _] at hf
    exact toReal_pos (pos_mono (subset_tsupport f) (pos_of_ne_zero hf)).ne' hs₁
  set ε' := ε * (μ <| tsupport f).toReal ^ (-(1 / p.toReal)) with ε'_def
  have hε' : 0 < ε' := by positivity
  have hε₂ : ENNReal.ofReal ε' * μ (tsupport f) ^ (1 / p.toReal) ≤ ENNReal.ofReal ε := by
    rw [← ofReal_toReal hs₁, ofReal_rpow_of_pos hs₂, ← ofReal_mul hε'.le,
      ofReal_le_ofReal_iff hε.le, ε'_def, mul_assoc, ← Real.rpow_add hs₂, neg_add_cancel,
      Real.rpow_zero, mul_one]
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := h₂.exists_contDiff_approx ⊤ (ε := fun _ ↦ ε') (by fun_prop)
    (by intro; positivity)
  refine ⟨g, h₁.mono hg₃, hg₁, (eLpNorm_sub_le_of_dist_bdd μ hp h₁.measurableSet hε'.le ?_
    (subset_tsupport f) (hg₃.trans (subset_tsupport f))).trans hε₂⟩
  intro x
  rw [dist_comm]
  exact (hg₂ x).le

end HasCompactSupport

namespace MeasureTheory.MemLp

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedSpace ℝ F]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- Every `Lp` function can be approximated by a smooth compactly supported function provided that
`p < ∞`. -/
/-
**MeasureTheory.MemLp.exist_eLpNorm_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.MemLp`。
形式化陈述：exist_eLpNorm_sub_le {p : Real>=0∞} (hp : p != ⊤) (hp₂ : 1 <= p) {f : E ->
 F} (hf : MemLp f p μ) {ε : Real} (hε : 0 < ε) : exists g, HasCompactSupport g ∧
 ContDiff Real ∞ g ∧ eLpNorm (f - g) p μ <= ENNReal.ofReal ε
参数：hp : p != ⊤；hp₂ : 1 <= p；hf : MemLp f p μ；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
· 使用定理 `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`：∀ {α : Type
 u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : MeasurableSpace α] [
BorelSpace α] {E : Type u_2}   [inst_4 : NormedAd…
· 使用定理 `PerfectlyNormalSpace.toNormalSpace`：∀ {X : Type u} {inst : TopologicalSp
ace X} [self : PerfectlyNormalSpace X], NormalSpace X
· 使用定理 `T6Space.toPerfectlyNormalSpace`：∀ {X : Type u} {inst : TopologicalSpace 
X} [self : T6Space X], PerfectlyNormalSpace X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMea
sure`：∀ {X : Type u_3} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetri
zableSpace X] [SigmaCompactSpace X]   [inst_3 : MeasurableSpace X]…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `HasCompactSupport.exist_eLpNorm_sub_le_of_continuous`：exist_eLpNorm_sub_
le_of_continuous (μ : Measure E
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
Every `Lp` function can be approximated by a smooth compactly supported function
 provided that
`p < ∞`.
-/
theorem exist_eLpNorm_sub_le {p : ℝ≥0∞} (hp : p ≠ ⊤) (hp₂ : 1 ≤ p) {f : E → F} (hf : MemLp f p μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ eLpNorm (f - g) p μ ≤ ENNReal.ofReal ε := by
  -- We use a standard ε / 2 argument to deduce the result from the approximation for
  -- continuous compactly supported functions.
  have hε₂ : 0 < ε / 2 := by positivity
  have hε₂' : 0 < ENNReal.ofReal (ε / 2) := by positivity
  obtain ⟨g, hg₁, hg₂, hg₃, hg₄⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hp hε₂'.ne'
  obtain ⟨g', hg'₁, hg'₂, hg'₃⟩ := hg₁.exist_eLpNorm_sub_le_of_continuous μ hε₂ hg₃
  refine ⟨g', hg'₁, hg'₂, ?_⟩
  have : f - g' = (f - g) - (g' - g) := by simp
  grw [this, eLpNorm_sub_le (hf.aestronglyMeasurable.sub hg₄.aestronglyMeasurable)
    (hg'₂.continuous.aestronglyMeasurable.sub hg₄.aestronglyMeasurable) hp₂, hg₂,
    eLpNorm_sub_comm, hg'₃, ← ENNReal.ofReal_add hε₂.le hε₂.le, add_halves]
/-
**MeasureTheory.MemLp._root_.MeasureTheory.Lp.dense_hasCompactSupport_contDiff**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Lp.dense_hasCompactSupport_contDiff {p : ℝ≥0∞} (hp : p ≠ ⊤)
    [hp₂ : Fact (1 ≤ p)] :
    Dense {f : Lp F p μ | ∃ (g : E → F), f =ᵐ[μ] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε ↦ ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := exist_eLpNorm_sub_le hp hp₂.out (Lp.memLp f) hε
  have hg₄ : MemLp g p μ := hg₂.continuous.memLp_of_hasCompactSupport hg₁
  use hg₄.toLp
  use ⟨g, hg₄.coeFn_toLp, hg₁, hg₂⟩
  rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
    ← le_ofReal_iff_toReal_le ((Lp.memLp f).sub (Lp.memLp hg₄.toLp)).eLpNorm_ne_top hε.le]
  convert! hg₃ using 1
  apply eLpNorm_congr_ae
  gcongr
  exact hg₄.coeFn_toLp

end MeasureTheory.MemLp

