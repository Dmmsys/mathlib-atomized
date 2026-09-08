/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.FactorizedRational
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.CircleIntegral

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Integrability for Logarithms of Meromorphic Functions

We establish integrability for functions of the form `log ‖meromorphic‖`. In the real setting, these
functions are interval integrable over every interval of the real line. This implies in particular
that logarithms of trigonometric functions are interval integrable. In the complex setting, the
functions are circle integrable over every circle in the complex plane.
-/

public section

open Filter Interval MeasureTheory MeromorphicOn Metric Real

/-!
## Interval Integrability for Logarithms of Real Meromorphic Functions
-/

section IntervalIntegrable

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E} {a b : ℝ}

/--
If `f` is real-meromorphic on a compact interval, then `log ‖f ·‖` is interval integrable on this
interval.
-/
/-
**MeromorphicOn.intervalIntegrable_log_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicOn.intervalIntegrable_log_norm (hf : MeromorphicOn f [[a, b]]) 
: IntervalIntegrable (log ‖f ·‖) volume a b
参数：hf : MeromorphicOn f [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.extract_zeros_poles`：MeromorphicOn.extract_zeros_poles {f 
: 𝕜 -> E} (h₁f : MeromorphicOn f U) (h₂f : forall u : U, meromorphicOrderAt f u 
!= ⊤) (h₃f : (divisor f…
· 使用定理 `Function.locallyFinsuppWithin.finiteSupport`：finiteSupport [T2Space X] [
Zero Y] (D : locallyFinsuppWithin U Y) (hU : IsCompact U) : Set.Finite D.support
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `MeromorphicOn.extract_zeros_poles_log`：MeromorphicOn.extract_zeros_poles
_log {f g : 𝕜 -> E} {D : Function.locallyFinsuppWithin U Int} (hg : forall u : U
, g u != 0) (h : f =ᶠ[codis…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_congr_codiscreteWithin`：intervalIntegrable_congr_codi
screteWithin {g : Real -> ε} [NullSingletonClass μ] (h : f =ᶠ[codiscreteWithin (
Ι a b)] g) : IntervalIntegrable…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用引理 `Filter.codiscreteWithin_mono`：Filter.codiscreteWithin_mono {U₁ U : Set X
} (hU : U₁ subseteq U) : codiscreteWithin U₁ <= codiscreteWithin U
· 使用引理 `Set.uIoc_subset_uIcc`：uIoc_subset_uIcc : Ι a b subseteq uIcc a b
· 使用定理 `IntervalIntegrable.add`：add [ContinuousAdd ε] (hf : IntervalIntegrable f
 μ a b) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable (fun x => f x + g
 x) μ a b
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IntervalIntegrable.finsum`：∀ {ι : Type u_1} {a b : ℝ} {μ : MeasureTheory
.Measure ℝ} {ε : Type u_8} [inst : TopologicalSpace ε]   [inst_1 : ENormedAddCom
mMonoid ε] [Con…
· 使用定理 `IntervalIntegrable.const_mul`：const_mul {f : Real -> A} (hf : IntervalIn
tegrable f μ a b) (c : A) : IntervalIntegrable (fun x => c * f x) μ a b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
（共 73 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is real-meromorphic on a compact interval, then `log ‖f ·‖` is interval i
ntegrable on this
interval.
-/
theorem MeromorphicOn.intervalIntegrable_log_norm (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log ‖f ·‖) volume a b := by
  by_cases t₀ : ∀ u : [[a, b]], meromorphicOrderAt f u ≠ ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((MeromorphicOn.divisor f [[a, b]]).finiteSupport isCompact_uIcc)
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    rw [intervalIntegrable_congr_codiscreteWithin
      (h₄g.filter_mono (Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc))]
    apply IntervalIntegrable.add
    · apply IntervalIntegrable.finsum
      intro i
      apply IntervalIntegrable.const_mul
      rw [(by ring : a = ((a - i) + i)), (by ring : b = ((b - i) + i))]
      apply IntervalIntegrable.comp_sub_right (f := (log ‖·‖)) _ i
      simp [norm_eq_abs, log_abs]
    · apply ContinuousOn.intervalIntegrable
      apply h₁g.continuousOn.norm.log
      simp_all
  · rw [← hf.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_Icc inf_le_sup)] at t₀
    push Not at t₀
    have : (log ‖f ·‖) =ᶠ[Filter.codiscreteWithin (Ι a b)] 0 := by
      apply Filter.EventuallyEq.filter_mono _ (Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc)
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        Filter.self_mem_codiscreteWithin [[a, b]]] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.meromorphicOrderAt_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    rw [intervalIntegrable_congr_codiscreteWithin this]
    apply Iff.mpr _root_.intervalIntegrable_const_iff
    tauto

@[deprecated (since := "2026-03-28")]
alias intervalIntegrable_log_norm_meromorphicOn := MeromorphicOn.intervalIntegrable_log_norm

/--
If `f` is real-meromorphic on a compact interval, then `log ‖f ·‖` is interval integrable on this
interval.
-/
/-
**MeromorphicOn.intervalIntegrable_posLog_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicOn.intervalIntegrable_posLog_norm (hf : MeromorphicOn f [[a, b]
]) : IntervalIntegrable (log⁺ ‖f ·‖) volume a b
参数：hf : MeromorphicOn f [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `IntervalIntegrable.add`：add [ContinuousAdd ε] (hf : IntervalIntegrable f
 μ a b) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable (fun x => f x + g
 x) μ a b
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IntervalIntegrable.const_mul`：const_mul {f : Real -> A} (hf : IntervalIn
tegrable f μ a b) (c : A) : IntervalIntegrable (fun x => c * f x) μ a b
· 使用定理 `MeromorphicOn.intervalIntegrable_log_norm`：MeromorphicOn.intervalIntegra
ble_log_norm (hf : MeromorphicOn f [[a, b]]) : IntervalIntegrable (log ‖f ·‖) vo
lume a b
· 使用定理 `IntervalIntegrable.abs`：abs {f : Real -> Real} (h : IntervalIntegrable f
 μ a b) : IntervalIntegrable (fun x => |f x|) μ a b

--- 原说明 ---
If `f` is real-meromorphic on a compact interval, then `log ‖f ·‖` is interval i
ntegrable on this
interval.
-/
theorem MeromorphicOn.intervalIntegrable_posLog_norm (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log⁺ ‖f ·‖) volume a b := by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply IntervalIntegrable.add
  · apply hf.intervalIntegrable_log_norm.const_mul
  · apply hf.intervalIntegrable_log_norm.abs.const_mul

@[deprecated (since := "2026-03-28")]
alias MeromorphicOn.intervalIntegrable_posLog_norm_meromorphicOn := intervalIntegrable_posLog_norm

/--
If `f` is real-meromorphic on a compact interval, then `log ∘ f` is interval integrable on this
interval.
-/
/-
**_root_.MeromorphicOn.intervalIntegrable_log** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.MeromorphicOn.intervalIntegrable_log {f : Real -> Real} (hf : Merom
orphicOn f [[a, b]]) : IntervalIntegrable (log ∘ f) volume a b
参数：hf : MeromorphicOn f [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is real-meromorphic on a compact interval, then `log ∘ f` is interval int
egrable on this
interval.
-/
theorem _root_.MeromorphicOn.intervalIntegrable_log {f : ℝ → ℝ} (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log ∘ f) volume a b := by
  rw [(by aesop : log ∘ f = (log ‖f ·‖))]
  exact hf.intervalIntegrable_log_norm

/--
Special case of `MeromorphicOn.intervalIntegrable_log`: The function `log ∘ sin` is interval
integrable over every interval.
-/
/-
**intervalIntegrable_log_sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_log_sin : IntervalIntegrable (log ∘ sin) volume a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.intervalIntegrable_log`：∀ {a b : ℝ} {f : ℝ → ℝ}, Meromorph
icOn f (Set.uIcc a b) → IntervalIntegrable (Real.log ∘ f) MeasureTheory.volume a
 b
· 使用引理 `AnalyticOnNhd.meromorphicOn`：AnalyticOnNhd.meromorphicOn {f : 𝕜 -> E} {U
 : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) : MeromorphicOn f U
· 使用定理 `Real.analyticOnNhd_sin`：analyticOnNhd_sin {s : Set Real} : AnalyticOnNhd
 Real sin s

--- 原说明 ---
Special case of `MeromorphicOn.intervalIntegrable_log`: The function `log ∘ sin`
 is interval
integrable over every interval.
-/
theorem intervalIntegrable_log_sin : IntervalIntegrable (log ∘ sin) volume a b :=
  analyticOnNhd_sin.meromorphicOn.intervalIntegrable_log

/--
Special case of `MeromorphicOn.intervalIntegrable_log`: The function `log ∘ cos` is interval
integrable over every interval.
-/
/-
**intervalIntegrable_log_cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_log_cos : IntervalIntegrable (log ∘ cos) volume a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.intervalIntegrable_log`：∀ {a b : ℝ} {f : ℝ → ℝ}, Meromorph
icOn f (Set.uIcc a b) → IntervalIntegrable (Real.log ∘ f) MeasureTheory.volume a
 b
· 使用引理 `AnalyticOnNhd.meromorphicOn`：AnalyticOnNhd.meromorphicOn {f : 𝕜 -> E} {U
 : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) : MeromorphicOn f U
· 使用定理 `Real.analyticOnNhd_cos`：analyticOnNhd_cos {s : Set Real} : AnalyticOnNhd
 Real cos s

--- 原说明 ---
Special case of `MeromorphicOn.intervalIntegrable_log`: The function `log ∘ cos`
 is interval
integrable over every interval.
-/
theorem intervalIntegrable_log_cos : IntervalIntegrable (log ∘ cos) volume a b :=
  analyticOnNhd_cos.meromorphicOn.intervalIntegrable_log

end IntervalIntegrable

/-!
## Circle Integrability for Logarithms of Complex Meromorphic Functions
-/

section CircleIntegrable

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {c : ℂ} {R : ℝ} {f : ℂ → E}

/--
If `f` is complex meromorphic on a circle in the complex plane, then `log ‖f ·‖` is circle
integrable over that circle.
-/
/-
**MeromorphicOn.circleIntegrable_log_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicOn.circleIntegrable_log_norm (hf : MeromorphicOn f (sphere c |R
|)) : CircleIntegrable (log ‖f ·‖) c R
参数：hf : MeromorphicOn f (sphere c |R|)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.extract_zeros_poles`：MeromorphicOn.extract_zeros_poles {f 
: 𝕜 -> E} (h₁f : MeromorphicOn f U) (h₂f : forall u : U, meromorphicOrderAt f u 
!= ⊤) (h₃f : (divisor f…
· 使用定理 `Function.locallyFinsuppWithin.finiteSupport`：finiteSupport [T2Space X] [
Zero Y] (D : locallyFinsuppWithin U Y) (hU : IsCompact U) : Set.Finite D.support
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `isCompact_sphere`：isCompact_sphere {α : Type*} [PseudoMetricSpace α] [Pr
operSpace α] (x : α) (r : Real) : IsCompact (sphere x r)
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `MeromorphicOn.extract_zeros_poles_log`：MeromorphicOn.extract_zeros_poles
_log {f g : 𝕜 -> E} {D : Function.locallyFinsuppWithin U Int} (hg : forall u : U
, g u != 0) (h : f =ᶠ[codis…
· 使用定理 `CircleIntegrable.congr_codiscreteWithin`：CircleIntegrable.congr_codiscre
teWithin {c : Complex} {R : Real} {f₁ f₂ : Complex -> E} (hf : f₁ =ᶠ[codiscreteW
ithin (sphere c |R|)] f₂) (hf…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `CircleIntegrable.add`：add (hf : CircleIntegrable f c R) (hg : CircleInte
grable g c R) : CircleIntegrable (f + g) c R
· 使用定理 `CircleIntegrable.finsum`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
{c : ℂ} {R : ℝ} {ι : Type u_3} {f : ι → ℂ → E},   (∀ (i : ι), CircleIntegrable (
f i) c R) → C…
· 使用定理 `IntervalIntegrable.const_mul`：const_mul {f : Real -> A} (hf : IntervalIn
tegrable f μ a b) (c : A) : IntervalIntegrable (fun x => c * f x) μ a b
· 使用定理 `MeromorphicOn.intervalIntegrable_log_norm`：MeromorphicOn.intervalIntegra
ble_log_norm (hf : MeromorphicOn f [[a, b]]) : IntervalIntegrable (log ‖f ·‖) vo
lume a b
· 使用引理 `AnalyticOnNhd.meromorphicOn`：AnalyticOnNhd.meromorphicOn {f : 𝕜 -> E} {U
 : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) : MeromorphicOn f U
· 使用定理 `AnalyticOnNhd.sub`：AnalyticOnNhd.sub (hf : AnalyticOnNhd 𝕜 f s) (hg : An
alyticOnNhd 𝕜 g s) : AnalyticOnNhd 𝕜 (f - g) s
· 使用定理 `AnalyticOnNhd.mono`：AnalyticOnNhd.mono {s t : Set E} (hf : AnalyticOnNhd
 𝕜 f t) (hst : s subseteq t) : AnalyticOnNhd 𝕜 f s
· 使用定理 `analyticOnNhd_circleMap`：analyticOnNhd_circleMap (c : Complex) (R : Real
) : AnalyticOnNhd Real (circleMap c R) Set.univ
· 使用定理 `trivial`：True
· 使用定理 `analyticOnNhd_const`：analyticOnNhd_const {v : F} {s : Set E} : AnalyticO
nNhd 𝕜 (fun _ => v) s
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `ContinuousOn.log`：ContinuousOn.log (hf : ContinuousOn f s) (h₀ : forall 
x in s, f x != 0) : ContinuousOn (fun x => log (f x)) s
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `AnalyticOnNhd.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_circleMap`：continuous_circleMap (c : Complex) (R : Real) : Co
ntinuous (circleMap c R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `circleMap_sub_center`：circleMap_sub_center (c : Complex) (R : Real) (θ :
 Real) : circleMap c R θ - c = circleMap 0 R θ
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is complex meromorphic on a circle in the complex plane, then `log ‖f ·‖`
 is circle
integrable over that circle.
-/
theorem MeromorphicOn.circleIntegrable_log_norm (hf : MeromorphicOn f (sphere c |R|)) :
    CircleIntegrable (log ‖f ·‖) c R := by
  by_cases t₀ : ∀ u : (sphere c |R|), meromorphicOrderAt f u ≠ ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((divisor f (sphere c |R|)).finiteSupport (isCompact_sphere c |R|))
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    apply CircleIntegrable.congr_codiscreteWithin h₄g.symm
    apply CircleIntegrable.add
    · apply CircleIntegrable.finsum
      intro i
      apply IntervalIntegrable.const_mul
      apply MeromorphicOn.intervalIntegrable_log_norm
      apply AnalyticOnNhd.meromorphicOn
      apply AnalyticOnNhd.sub _ analyticOnNhd_const
      apply (analyticOnNhd_circleMap c R).mono (by tauto)
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.log
      · apply ContinuousOn.norm
        apply h₁g.continuousOn.comp (t := sphere c |R|) (continuous_circleMap c R).continuousOn
        intro x hx
        simp
      · intro x hx
        rw [ne_eq, norm_eq_zero]
        apply h₂g ⟨circleMap c R x, circleMap_mem_sphere' c R x⟩
  · rw [← hf.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_sphere (by simp) c
      (abs_nonneg R))] at t₀
    push Not at t₀
    have : (log ‖f ·‖) =ᶠ[codiscreteWithin (sphere c |R|)] 0 := by
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        self_mem_codiscreteWithin (sphere c |R|)] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.meromorphicOrderAt_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    apply CircleIntegrable.congr_codiscreteWithin this.symm (circleIntegrable_const 0 c R)

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_log_norm_meromorphicOn := MeromorphicOn.circleIntegrable_log_norm

/--
Variant of `MeromorphicOn.circleIntegrable_log_norm` for non-negative radii.
-/
/-
**MeromorphicOn.circleIntegrable_log_norm_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：MeromorphicOn.circleIntegrable_log_norm_of_nonneg (hf : MeromorphicOn f (s
phere c R)) (hR : 0 <= R) : CircleIntegrable (log ‖f ·‖) c R
参数：hf : MeromorphicOn f (sphere c R)；hR : 0 <= R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.circleIntegrable_log_norm`：MeromorphicOn.circleIntegrable_
log_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log ‖f ·‖) c 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
Variant of `MeromorphicOn.circleIntegrable_log_norm` for non-negative radii.
-/
theorem MeromorphicOn.circleIntegrable_log_norm_of_nonneg (hf : MeromorphicOn f (sphere c R))
    (hR : 0 ≤ R) :
    CircleIntegrable (log ‖f ·‖) c R := by
  rw [← abs_of_nonneg hR] at hf
  exact hf.circleIntegrable_log_norm

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_log_norm_meromorphicOn_of_nonneg :=
    MeromorphicOn.circleIntegrable_log_norm_of_nonneg

/--
Variant of `MeromorphicOn.circleIntegrable_log_norm` for factorized rational functions.
-/
@[fun_prop]
/-
**circleIntegrable_log_norm_factorizedRational** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleIntegrable_log_norm_factorizedRational {R : Real} {c : Complex} (D :
 Complex -> Int) : CircleIntegrable (∑ᶠ u, ((D u) * log ‖· - u‖)) c R
参数：D : Complex -> Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleIntegrable.finsum`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
{c : ℂ} {R : ℝ} {ι : Type u_3} {f : ι → ℂ → E},   (∀ (i : ι), CircleIntegrable (
f i) c R) → C…
· 使用定理 `CircleIntegrable.const_smul`：const_smul {f : Complex -> A} (h : CircleIn
tegrable f c R) : CircleIntegrable (a • f) c R
· 使用定理 `MeromorphicOn.circleIntegrable_log_norm`：MeromorphicOn.circleIntegrable_
log_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log ‖f ·‖) c 
R
· 使用引理 `AnalyticOnNhd.meromorphicOn`：AnalyticOnNhd.meromorphicOn {f : 𝕜 -> E} {U
 : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) : MeromorphicOn f U
· 使用定理 `AnalyticOnNhd.sub`：AnalyticOnNhd.sub (hf : AnalyticOnNhd 𝕜 f s) (hg : An
alyticOnNhd 𝕜 g s) : AnalyticOnNhd 𝕜 (f - g) s
· 使用定理 `analyticOnNhd_id`：analyticOnNhd_id : AnalyticOnNhd 𝕜 (fun x : E => x) s
· 使用定理 `analyticOnNhd_const`：analyticOnNhd_const {v : F} {s : Set E} : AnalyticO
nNhd 𝕜 (fun _ => v) s

--- 原说明 ---
Variant of `MeromorphicOn.circleIntegrable_log_norm` for factorized rational fun
ctions.
-/
theorem circleIntegrable_log_norm_factorizedRational {R : ℝ} {c : ℂ} (D : ℂ → ℤ) :
    CircleIntegrable (∑ᶠ u, ((D u) * log ‖· - u‖)) c R :=
  CircleIntegrable.finsum (fun _ ↦
    ((analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm).const_smul)

/--
If `f` is complex meromorphic on a circle in the complex plane, then `log⁺ ‖f ·‖` is circle
integrable over that circle.
-/
/-
**MeromorphicOn.circleIntegrable_posLog_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicOn.circleIntegrable_posLog_norm (hf : MeromorphicOn f (sphere c
 |R|)) : CircleIntegrable (log⁺ ‖f ·‖) c R
参数：hf : MeromorphicOn f (sphere c |R|)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `CircleIntegrable.add`：add (hf : CircleIntegrable f c R) (hg : CircleInte
grable g c R) : CircleIntegrable (f + g) c R
· 使用定理 `IntervalIntegrable.const_mul`：const_mul {f : Real -> A} (hf : IntervalIn
tegrable f μ a b) (c : A) : IntervalIntegrable (fun x => c * f x) μ a b
· 使用定理 `MeromorphicOn.circleIntegrable_log_norm`：MeromorphicOn.circleIntegrable_
log_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log ‖f ·‖) c 
R
· 使用定理 `CircleIntegrable.abs`：abs {f : Complex -> Real} (hf : CircleIntegrable f
 c R) : CircleIntegrable |f| c R

--- 原说明 ---
If `f` is complex meromorphic on a circle in the complex plane, then `log⁺ ‖f ·‖
` is circle
integrable over that circle.
-/
theorem MeromorphicOn.circleIntegrable_posLog_norm (hf : MeromorphicOn f (sphere c |R|)) :
    CircleIntegrable (log⁺ ‖f ·‖) c R := by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply CircleIntegrable.add
  · apply hf.circleIntegrable_log_norm.const_mul
  · apply hf.circleIntegrable_log_norm.abs.const_mul

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_posLog_norm_meromorphicOn := MeromorphicOn.circleIntegrable_posLog_norm

/--
Variant of `MeromorphicOn.circleIntegrable_posLog_norm` for non-negative radii.
-/
/-
**MeromorphicOn.circleIntegrable_posLog_norm_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：MeromorphicOn.circleIntegrable_posLog_norm_of_nonneg (hf : MeromorphicOn f
 (sphere c R)) (hR : 0 <= R) : CircleIntegrable (log⁺ ‖f ·‖) c R
参数：hf : MeromorphicOn f (sphere c R)；hR : 0 <= R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.circleIntegrable_posLog_norm`：MeromorphicOn.circleIntegrab
le_posLog_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log⁺ ‖f
 ·‖) c R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
Variant of `MeromorphicOn.circleIntegrable_posLog_norm` for non-negative radii.
-/
theorem MeromorphicOn.circleIntegrable_posLog_norm_of_nonneg (hf : MeromorphicOn f (sphere c R))
    (hR : 0 ≤ R) :
    CircleIntegrable (log⁺ ‖f ·‖) c R := by
  rw [← abs_of_nonneg hR] at hf
  exact hf.circleIntegrable_posLog_norm

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_posLog_norm_meromorphicOn_of_nonneg :=
    MeromorphicOn.circleIntegrable_posLog_norm_of_nonneg

end CircleIntegrable

