/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Properties of analyticity restricted to a set

From `Mathlib/Analysis/Analytic/Basic.lean`, we have the definitions

1. `AnalyticWithinAt 𝕜 f s x` means a power series at `x` converges to `f` on `𝓝[insert x s] x`.
2. `AnalyticOn 𝕜 f s t` means `∀ x ∈ t, AnalyticWithinAt 𝕜 f s x`.

This means there exists an extension of `f` which is analytic and agrees with `f` on `s ∪ {x}`, but
`f` is allowed to be arbitrary elsewhere.

Here we prove basic properties of these definitions. Where convenient we assume completeness of the
ambient space, which allows us to relate `AnalyticWithinAt` to analyticity of a local extension.
-/

public section

noncomputable section

open scoped Topology Filter ENNReal
open Set Filter Metric

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-!
### Basic properties
-/

/-- `AnalyticWithinAt` is trivial if `{x} ∈ 𝓝[s] x` -/
/-
**analyticWithinAt_of_singleton_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticWithinAt_of_singleton_mem {f : E -> F} {s : Set E} {x : E} (h : {x
} in 𝓝[s] x) : AnalyticWithinAt 𝕜 f s x
参数：h : {x} in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.constFormalMultilinearSeries_radius`：constFormal
MultilinearSeries_radius {v : F} : (constFormalMultilinearSeries 𝕜 E v).radius =
 ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `dist_self_add_left`：∀ {E : Type u_2} [inst : SeminormedAddGroup E] (a b 
: E), dist (b + a) b = ‖a‖
· 使用定理 `Metric.eball_ofReal`：Metric.eball_ofReal {x : α} {ε : Real} : eball x (.
ofReal ε) = ball x ε
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
· 使用定理 `hasFPowerSeriesOnBall_const`：hasFPowerSeriesOnBall_const {c : F} {e : E}
 : HasFPowerSeriesOnBall (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e ⊤
· 使用定理 `Metric.eball_top`：Metric.eball_top (x : α) : eball x ⊤ = univ

--- 原说明 ---
`AnalyticWithinAt` is trivial if `{x} ∈ 𝓝[s] x`
-/
lemma analyticWithinAt_of_singleton_mem {f : E → F} {s : Set E} {x : E} (h : {x} ∈ 𝓝[s] x) :
    AnalyticWithinAt 𝕜 f s x := by
  rcases mem_nhdsWithin.mp h with ⟨t, ot, xt, st⟩
  rcases Metric.mem_nhds_iff.mp (ot.mem_nhds xt) with ⟨r, r0, rt⟩
  exact ⟨constFormalMultilinearSeries 𝕜 E (f x), .ofReal r,
  { r_le := by simp only [FormalMultilinearSeries.constFormalMultilinearSeries_radius, le_top]
    r_pos := by positivity
    hasSum := by
      intro y ys yr
      simp only [subset_singleton_iff, mem_inter_iff, and_imp] at st
      simp only [mem_insert_iff, add_eq_left] at ys
      have : x + y = x := by
        rcases ys with rfl | ys
        · simp
        · exact st (x + y) (rt (by simpa using yr)) ys
      simp only [this]
      apply (hasFPowerSeriesOnBall_const (e := 0)).hasSum
      simp only [eball_top, mem_univ] }⟩

/-- If `f` is `AnalyticOn` near each point in a set, it is `AnalyticOn` the set -/
/-
**analyticOn_of_locally_analyticOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOn_of_locally_analyticOn {f : E -> F} {s : Set E} (h : forall x in
 s, exists u, IsOpen u ∧ x in u ∧ AnalyticOn 𝕜 f (s inter u)) : AnalyticOn 𝕜 f s
参数：h : forall x in s, exists u, IsOpen u ∧ x in u ∧ AnalyticOn 𝕜 f (s inter u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `min_le_of_right_le`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, c
 ≤ a → min b c ≤ a
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `dist_self_add_left`：∀ {E : Type u_2} [inst : SeminormedAddGroup E] (a b 
: E), dist (b + a) b = ‖a‖

--- 原说明 ---
If `f` is `AnalyticOn` near each point in a set, it is `AnalyticOn` the set
-/
lemma analyticOn_of_locally_analyticOn {f : E → F} {s : Set E}
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ AnalyticOn 𝕜 f (s ∩ u)) :
    AnalyticOn 𝕜 f s := by
  intro x m
  rcases h x m with ⟨u, ou, xu, fu⟩
  rcases Metric.mem_nhds_iff.mp (ou.mem_nhds xu) with ⟨r, r0, ru⟩
  rcases fu x ⟨m, xu⟩ with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t,
    { r_pos := lt_min (by positivity) fp.r_pos
      r_le := min_le_of_right_le fp.r_le
      hasSum := by
        intro y ys yr
        simp only [mem_eball, lt_min_iff, edist_lt_ofReal, dist_zero_right] at yr
        apply fp.hasSum
        · simp only [mem_insert_iff, add_eq_left] at ys
          rcases ys with rfl | ys
          · simp
          · simp only [mem_insert_iff, add_eq_left, mem_inter_iff, ys, true_and]
            apply Or.inr (ru ?_)
            simp only [mem_ball, dist_self_add_left, yr]
        · simp only [mem_eball, yr] }⟩

/-- On open sets, `AnalyticOnNhd` and `AnalyticOn` coincide -/
/-
**IsOpen.analyticOn_iff_analyticOnNhd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.analyticOn_iff_analyticOnNhd {f : E -> F} {s : Set E} (hs : IsOpen 
s) : AnalyticOn 𝕜 f s ↔ AnalyticOnNhd 𝕜 f s
参数：hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `min_le_of_right_le`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, c
 ≤ a → min b c ≤ a
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self_add_left`：∀ {E : Type u_2} [inst : SeminormedAddGroup E] (a b 
: E), dist (b + a) b = ‖a‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s

--- 原说明 ---
On open sets, `AnalyticOnNhd` and `AnalyticOn` coincide
-/
lemma IsOpen.analyticOn_iff_analyticOnNhd {f : E → F} {s : Set E} (hs : IsOpen s) :
    AnalyticOn 𝕜 f s ↔ AnalyticOnNhd 𝕜 f s := by
  refine ⟨?_, AnalyticOnNhd.analyticOn⟩
  intro hf x m
  rcases Metric.mem_nhds_iff.mp (hs.mem_nhds m) with ⟨r, r0, rs⟩
  rcases hf x m with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t,
  { r_pos := lt_min (by positivity) fp.r_pos
    r_le := min_le_of_right_le fp.r_le
    hasSum := by
      intro y ym
      simp only [mem_eball, lt_min_iff, edist_lt_ofReal, dist_zero_right] at ym
      refine fp.hasSum ?_ ym.2
      apply mem_insert_of_mem
      apply rs
      simp only [mem_ball, dist_self_add_left, ym.1] }⟩

/-!
### Equivalence to analyticity of a local extension

We show that `HasFPowerSeriesWithinOnBall`, `HasFPowerSeriesWithinAt`, and `AnalyticWithinAt` are
equivalent to the existence of a local extension with full analyticity.  We do not yet show a
result for `AnalyticOn`, as this requires a bit more work to show that local extensions can
be stitched together.
-/

/-- `f` has power series `p` at `x` iff some local extension of `f` has that series -/
/-
**hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall** 是 Mathlib 中的一个引
理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall [CompleteSpac
e F] {f : E -> F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : R
eal>=0∞} : HasFPowerSeriesWithinOnBall f p s x r ↔ exists g, EqOn f g (insert x 
s inter eball x r) ∧ HasFPowerSeriesOnBall g p x r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FormalMultilinearSeries.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_3} {F : Typ
e u_4} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [ins
t_2 : NormedSpace 𝕜 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …

--- 原说明 ---
`f` has power series `p` at `x` iff some local extension of `f` has that series
-/
lemma hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall [CompleteSpace F] {f : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : ℝ≥0∞} :
    HasFPowerSeriesWithinOnBall f p s x r ↔
      ∃ g, EqOn f g (insert x s ∩ eball x r) ∧
        HasFPowerSeriesOnBall g p x r := by
  constructor
  · intro h
    refine ⟨fun y ↦ p.sum (y - x), ?_, ?_⟩
    · intro y ⟨ys,yb⟩
      simp only [mem_eball, edist_eq_enorm_sub] at yb
      have e0 := p.hasSum (x := y - x) ?_
      · have e1 := (h.hasSum (y := y - x) ?_ ?_)
        · simp only [add_sub_cancel] at e1
          exact e1.unique e0
        · simpa only [add_sub_cancel]
        · simpa only [mem_eball, edist_zero_right]
      · simp only [mem_eball, edist_zero_right]
        exact lt_of_lt_of_le yb h.r_le
    · refine ⟨h.r_le, h.r_pos, ?_⟩
      intro y lt
      simp only [add_sub_cancel_left]
      apply p.hasSum
      simp only [mem_eball] at lt ⊢
      exact lt_of_lt_of_le lt h.r_le
  · intro ⟨g, hfg, hg⟩
    refine ⟨hg.r_le, hg.r_pos, ?_⟩
    intro y ys lt
    rw [hfg]
    · exact hg.hasSum lt
    · refine ⟨ys, ?_⟩
      simpa only [mem_eball, edist_eq_enorm_sub, add_sub_cancel_left, sub_zero] using lt

/-- `f` has power series `p` at `x` iff some local extension of `f` has that series -/
/-
**hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt [CompleteSpace F] {f 
: E -> F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} : HasFPowerSer
iesWithinAt f p s x ↔ exists g, f =ᶠ[𝓝[insert x s] x] g ∧ HasFPowerSeriesAt g p 
x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall`：hasFPowerS
eriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall [CompleteSpace F] {f : E -> F
} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyEq_iff_exists_mem`：eventuallyEq_iff_exists_mem {l : Fil
ter α} {f g : α -> β} : f =ᶠ[l] g ↔ exists s in l, EqOn f g s
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFPowerSeriesOnBall.mono`：HasFPowerSeriesOnBall.mono (hf : HasFPowerSe
riesOnBall f p x r) (r'_pos : 0 < r') (hr : r' <= r) : HasFPowerSeriesOnBall f p
 x r'
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a

--- 原说明 ---
`f` has power series `p` at `x` iff some local extension of `f` has that series
-/
lemma hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt [CompleteSpace F] {f : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} :
    HasFPowerSeriesWithinAt f p s x ↔
      ∃ g, f =ᶠ[𝓝[insert x s] x] g ∧ HasFPowerSeriesAt g p x := by
  constructor
  · intro ⟨r, h⟩
    rcases hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mp h with ⟨g, e, h⟩
    refine ⟨g, ?_, ⟨r, h⟩⟩
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, ?_, e⟩
    exact inter_mem_nhdsWithin _ (eball_mem_nhds _ h.r_pos)
  · intro ⟨g, hfg, ⟨r, hg⟩⟩
    simp only [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff] at hfg
    rcases hfg with ⟨e, e0, hfg⟩
    refine ⟨min r (.ofReal e), ?_⟩
    refine hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mpr ⟨g, ?_, ?_⟩
    · intro y ⟨ys, xy⟩
      refine hfg ?_ ys
      simp only [mem_eball, lt_min_iff, edist_lt_ofReal] at xy
      exact xy.2
    · exact hg.mono (lt_min hg.r_pos (by positivity)) (min_le_left _ _)

/-- `f` is analytic within `s` at `x` iff some local extension of `f` is analytic at `x` -/
/-
**analyticWithinAt_iff_exists_analyticAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticWithinAt_iff_exists_analyticAt [CompleteSpace F] {f : E -> F} {s :
 Set E} {x : E} : AnalyticWithinAt 𝕜 f s x ↔ exists g, f =ᶠ[𝓝[insert x s] x] g ∧
 AnalyticAt 𝕜 g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
`f` is analytic within `s` at `x` iff some local extension of `f` is analytic at
 `x`
-/
lemma analyticWithinAt_iff_exists_analyticAt [CompleteSpace F] {f : E → F} {s : Set E} {x : E} :
    AnalyticWithinAt 𝕜 f s x ↔
      ∃ g, f =ᶠ[𝓝[insert x s] x] g ∧ AnalyticAt 𝕜 g x := by
  simp only [AnalyticWithinAt, AnalyticAt, hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt]
  tauto

/-- `f` is analytic within `s` at `x` iff some local extension of `f` is analytic at `x`. In this
version, we make sure that the extension coincides with `f` on all of `insert x s`. -/
/-
**analyticWithinAt_iff_exists_analyticAt'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticWithinAt_iff_exists_analyticAt' [CompleteSpace F] {f : E -> F} {s 
: Set E} {x : E} : AnalyticWithinAt 𝕜 f s x ↔ exists g, f x = g x ∧ EqOn f g (in
sert x s) ∧ AnalyticAt 𝕜 g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AnalyticAt.congr`：AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 
x] g) : AnalyticAt 𝕜 g x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a

--- 原说明 ---
`f` is analytic within `s` at `x` iff some local extension of `f` is analytic at
 `x`. In this
version, we make sure that the extension coincides with `f` on all of `insert x 
s`.
-/
lemma analyticWithinAt_iff_exists_analyticAt' [CompleteSpace F] {f : E → F} {s : Set E} {x : E} :
    AnalyticWithinAt 𝕜 f s x ↔
      ∃ g, f x = g x ∧ EqOn f g (insert x s) ∧ AnalyticAt 𝕜 g x := by
  classical
  simp only [analyticWithinAt_iff_exists_analyticAt]
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hf, hg⟩
    rcases mem_nhdsWithin.1 hf with ⟨u, u_open, xu, hu⟩
    let g' := Set.piecewise u g f
    refine ⟨g', ?_, ?_, ?_⟩
    · have : x ∈ u ∩ insert x s := ⟨xu, by simp⟩
      simpa [g', xu, this] using hu this
    · intro y hy
      by_cases h'y : y ∈ u
      · have : y ∈ u ∩ insert x s := ⟨h'y, hy⟩
        simpa [g', h'y, this] using hu this
      · simp [g', h'y]
    · apply hg.congr
      filter_upwards [u_open.mem_nhds xu] with y hy using by simp [g', hy]
  · rintro ⟨g, -, hf, hg⟩
    exact ⟨g, by filter_upwards [self_mem_nhdsWithin] using hf, hg⟩

alias ⟨AnalyticWithinAt.exists_analyticAt, _⟩ := analyticWithinAt_iff_exists_analyticAt'
/-
**AnalyticWithinAt.exists_mem_nhdsWithin_analyticOn** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：AnalyticWithinAt.exists_mem_nhdsWithin_analyticOn [CompleteSpace F] {f : E
 -> F} {s : Set E} {x : E} (h : AnalyticWithinAt 𝕜 f s x) : exists u in 𝓝[insert
 x s] x, AnalyticOn 𝕜 f u
参数：h : AnalyticWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.exists_analyticAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} {F : Type u_3} [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_analyticAt`：isOpen_analyticAt : IsOpen { x | AnalyticAt 𝕜 f x }
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `AnalyticWithinAt.congr`：AnalyticWithinAt.congr {f g : E -> F} {s : Set E
} {x : E} (hf : AnalyticWithinAt 𝕜 f s x) (hs : EqOn g f s) (hx : g x = f x) : A
nalyticWithi…
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma AnalyticWithinAt.exists_mem_nhdsWithin_analyticOn
    [CompleteSpace F] {f : E → F} {s : Set E} {x : E} (h : AnalyticWithinAt 𝕜 f s x) :
    ∃ u ∈ 𝓝[insert x s] x, AnalyticOn 𝕜 f u := by
  obtain ⟨g, -, h'g, hg⟩ : ∃ g, f x = g x ∧ EqOn f g (insert x s) ∧ AnalyticAt 𝕜 g x :=
    h.exists_analyticAt
  let u := insert x s ∩ {y | AnalyticAt 𝕜 g y}
  refine ⟨u, ?_, ?_⟩
  · exact inter_mem_nhdsWithin _ ((isOpen_analyticAt 𝕜 g).mem_nhds hg)
  · intro y hy
    have : AnalyticWithinAt 𝕜 g u y := hy.2.analyticWithinAt
    exact this.congr (h'g.mono (inter_subset_left)) (h'g (inter_subset_left hy))
/-
**AnalyticWithinAt.eventually_analyticWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.eventually_analyticWithinAt [CompleteSpace F] {f : E -> F
} {s : Set E} {x : E} (hf : AnalyticWithinAt 𝕜 f s x) : forallᶠ y in 𝓝[s] x, Ana
lyticWithinAt 𝕜 f s y
参数：hf : AnalyticWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `analyticWithinAt_iff_exists_analyticAt`：analyticWithinAt_iff_exists_anal
yticAt [CompleteSpace F] {f : E -> F} {s : Set E} {x : E} : AnalyticWithinAt 𝕜 f
 s x ↔ exists g, f =ᶠ[𝓝[inse…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `AnalyticAt.eventually_analyticAt`：AnalyticAt.eventually_analyticAt (h : 
AnalyticAt 𝕜 f x) : forallᶠ y in 𝓝 x, AnalyticAt 𝕜 f y
· 使用定理 `Filter.Eventually.eventually_nhds`：Filter.Eventually.eventually_nhds {p 
: X -> Prop} (h : forallᶠ y in 𝓝 x, p y) : forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p
 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
-/
theorem AnalyticWithinAt.eventually_analyticWithinAt
    [CompleteSpace F] {f : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) : ∀ᶠ y in 𝓝[s] x, AnalyticWithinAt 𝕜 f s y := by
  obtain ⟨g, hfg, hga⟩ := analyticWithinAt_iff_exists_analyticAt.mp hf
  simp only [Filter.EventuallyEq, eventually_nhdsWithin_iff] at hfg ⊢
  filter_upwards [hfg.eventually_nhds, hga.eventually_analyticAt] with z hfgz hgaz hz
  refine analyticWithinAt_iff_exists_analyticAt.mpr ⟨g, ?_, hgaz⟩
  exact (eventually_nhdsWithin_iff.mpr hfgz).filter_mono <| nhdsWithin_mono _ (by simp [hz])
