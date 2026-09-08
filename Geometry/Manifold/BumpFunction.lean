/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Smooth bump functions on a smooth manifold

In this file we define `SmoothBumpFunction I c` to be a bundled smooth "bump" function centered at
`c`. It is a structure that consists of two real numbers `0 < rIn < rOut` with small enough `rOut`.
We define a coercion to function for this type, and for `f : SmoothBumpFunction I c`, the function
`⇑f` written in the extended chart at `c` has the following properties:

* `f x = 1` in the closed ball of radius `f.rIn` centered at `c`;
* `f x = 0` outside of the ball of radius `f.rOut` centered at `c`;
* `0 ≤ f x ≤ 1` for all `x`.

The actual statements involve (pre)images under `extChartAt I f` and are given as lemmas in the
`SmoothBumpFunction` namespace.

## Tags

manifold, smooth bump function
-/

@[expose] public section

universe uE uF uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M]

open Function Filter Module Set Metric

open scoped Topology Manifold ContDiff

noncomputable section

/-!
### Smooth bump function

In this section we define a structure for a bundled smooth bump function and prove its properties.
-/

variable (I) in
/-- Given a smooth manifold modelled on a finite-dimensional space `E`,
`f : SmoothBumpFunction I M` is a smooth function on `M` such that in the extended chart `e` at
`f.c`:

* `f x = 1` in the closed ball of radius `f.rIn` centered at `f.c`;
* `f x = 0` outside of the ball of radius `f.rOut` centered at `f.c`;
* `0 ≤ f x ≤ 1` for all `x`.

The structure contains data required to construct a function with these properties. The function is
available as `⇑f` or `f x`. Formal statements of the properties listed above involve some
(pre)images under `extChartAt I f.c` and are given as lemmas in the `SmoothBumpFunction`
namespace. -/
/-
**SmoothBumpFunction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{E : Type uE} →   [inst : NormedAddCommGroup E] →     [inst_1 : NormedSpac
e ℝ E] →       {H : Type uH} →         [inst_2 : TopologicalSpace H] →          
 ModelWithCorners ℝ E H → {M : Type uM} → [inst : TopologicalSpace M] → [Charted
Space H M] → M → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a smooth manifold modelled on a finite-dimensional space `E`,
`f : SmoothBumpFunction I M` is a smooth function on `M` such that in the extend
ed chart `e` at
`f.c`:

* `f x = 1` in the closed ball of radius `f.rIn` centered at `f.c`;
* `f x = 0` outside of the ball of radius `f.rOut` centered at `f.c`;
* `0 ≤ f x ≤ 1` for all `x`.

The structure contains data required to construct a function with these properti
es. The function is
available as `⇑f` or `f x`. Formal statements of the properties listed above inv
olve some
(pre)images under `extChartAt I f.c` and are given as lemmas in the `SmoothBumpF
unction`
namespace.
-/
structure SmoothBumpFunction (c : M) extends ContDiffBump (extChartAt I c c) where
  closedBall_subset : closedBall (extChartAt I c c) rOut ∩ range I ⊆ (extChartAt I c).target

namespace SmoothBumpFunction

section FiniteDimensional

variable [FiniteDimensional ℝ E]

variable {c : M} (f : SmoothBumpFunction I c) {x : M}

/-- The function defined by `f : SmoothBumpFunction c`. Use automatic coercion to function
instead. -/
/-
**SmoothBumpFunction.toFun** 是 Mathlib 中的一个定义，位于命名空间 `SmoothBumpFunction`。
形式化陈述：{E : Type uE} →   [inst : NormedAddCommGroup E] →     [inst_1 : NormedSpac
e ℝ E] →       {H : Type uH} →         [inst_2 : TopologicalSpace H] →          
 {I : ModelWithCorners ℝ E H} →             {M : Type uM} →               [inst_
3 : TopologicalSpace M] →                 [inst_4 : ChartedSpace H M] → [FiniteD
imensional ℝ E] → {c : M} → SmoothBumpFunction I c → M → ℝ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsContDiffBumpBase.instHasContDiffBumpOfFiniteDimensionalReal`：∀ {E 
: Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDime
nsional ℝ E], HasContDiffBump E

--- 原说明 ---
The function defined by `f : SmoothBumpFunction c`. Use automatic coercion to fu
nction
instead.
-/
@[coe] def toFun : M → ℝ :=
  indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c)
/-
**SmoothBumpFunction.** 是 Mathlib 中的一个实例，位于命名空间 `SmoothBumpFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (SmoothBumpFunction I c) fun _ => M → ℝ :=
  ⟨toFun⟩
/-
**SmoothBumpFunction.coe_def** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunction`。
形式化陈述：coe_def : ⇑f = indicator (chartAt H c).source (f.toContDiffBump ∘ extChart
At I c)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_def : ⇑f = indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c) :=
  rfl

end FiniteDimensional

variable {c : M} (f : SmoothBumpFunction I c) {x : M}

/-
**SmoothBumpFunction.rOut_pos** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunction`。
形式化陈述：rOut_pos : 0 < f.rOut
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffBump.rOut_pos`：rOut_pos {c : E} (f : ContDiffBump c) : 0 < f.rOu
t
-/
theorem rOut_pos : 0 < f.rOut :=
  f.toContDiffBump.rOut_pos
/-
**SmoothBumpFunction.ball_subset** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunction`。
形式化陈述：ball_subset : ball (extChartAt I c c) f.rOut inter range I subseteq (extCh
artAt I c).target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `SmoothBumpFunction.closedBall_subset`：∀ {E : Type uE} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH} [inst_2 : TopologicalSpace 
H]   {I : ModelWithCorners…
-/
theorem ball_subset : ball (extChartAt I c c) f.rOut ∩ range I ⊆ (extChartAt I c).target :=
  Subset.trans (inter_subset_inter_left _ ball_subset_closedBall) f.closedBall_subset
/-
**SmoothBumpFunction.ball_inter_range_eq_ball_inter_target** 是 Mathlib 中的一个定理，位于
命名空间 `SmoothBumpFunction`。
形式化陈述：ball_inter_range_eq_ball_inter_target : ball (extChartAt I c c) f.rOut int
er range I = ball (extChartAt I c c) f.rOut inter (extChartAt I c).target
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `SmoothBumpFunction.ball_subset`：ball_subset : ball (extChartAt I c c) f.
rOut inter range I subseteq (extChartAt I c).target
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `extChartAt_target_subset_range`：extChartAt_target_subset_range (x : M) :
 (extChartAt I x).target subseteq range I
-/
theorem ball_inter_range_eq_ball_inter_target :
    ball (extChartAt I c c) f.rOut ∩ range I =
      ball (extChartAt I c c) f.rOut ∩ (extChartAt I c).target :=
  (subset_inter inter_subset_left f.ball_subset).antisymm <| inter_subset_inter_right _ <|
    extChartAt_target_subset_range _

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-
**SmoothBumpFunction.eqOn_source** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunction`。
形式化陈述：eqOn_source : EqOn f (f.toContDiffBump ∘ extChartAt I c) (chartAt H c).sou
rce
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eqOn_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s :
 Set α} {f : α → M}, Set.EqOn (s.indicator f) f s
· 使用定理 `ExistsContDiffBumpBase.instHasContDiffBumpOfFiniteDimensionalReal`：∀ {E 
: Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDime
nsional ℝ E], HasContDiffBump E
-/
theorem eqOn_source : EqOn f (f.toContDiffBump ∘ extChartAt I c) (chartAt H c).source :=
  eqOn_indicator
/-
**SmoothBumpFunction.eventuallyEq_of_mem_source** 是 Mathlib 中的一个定理，位于命名空间 `Smoot
hBumpFunction`。
形式化陈述：eventuallyEq_of_mem_source (hx : x in (chartAt H c).source) : f =ᶠ[𝓝 x] f.
toContDiffBump ∘ extChartAt I c
参数：hx : x in (chartAt H c).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.eventuallyEq_of_mem`：Set.EqOn.eventuallyEq_of_mem {α β} {s : Se
t α} {l : Filter α} {f g : α -> β} (h : EqOn f g s) (hl : s in l) : f =ᶠ[l] g
· 使用定理 `ExistsContDiffBumpBase.instHasContDiffBumpOfFiniteDimensionalReal`：∀ {E 
: Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDime
nsional ℝ E], HasContDiffBump E
· 使用定理 `SmoothBumpFunction.eqOn_source`：eqOn_source : EqOn f (f.toContDiffBump ∘
 extChartAt I c) (chartAt H c).source
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem eventuallyEq_of_mem_source (hx : x ∈ (chartAt H c).source) :
    f =ᶠ[𝓝 x] f.toContDiffBump ∘ extChartAt I c :=
  f.eqOn_source.eventuallyEq_of_mem <| (chartAt H c).open_source.mem_nhds hx
/-
**SmoothBumpFunction.one_of_dist_le** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunctio
n`。
形式化陈述：one_of_dist_le (hs : x in (chartAt H c).source) (hd : dist (extChartAt I c
 x) (extChartAt I c c) <= f.rIn) : f x = 1
参数：hs : x in (chartAt H c).source；hd : dist (extChartAt I c x) (extChartAt I c c
) <= f.rIn。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExistsContDiffBumpBase.instHasContDiffBumpOfFiniteDimensionalReal`：∀ {E 
: Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDime
nsional ℝ E], HasContDiffBump E
· 使用定理 `SmoothBumpFunction.eqOn_source`：eqOn_source : EqOn f (f.toContDiffBump ∘
 extChartAt I c) (chartAt H c).source
· 使用定理 `ContDiffBump.one_of_mem_closedBall`：one_of_mem_closedBall (hx : x in clo
sedBall c f.rIn) : f x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_of_dist_le (hs : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) ≤ f.rIn) : f x = 1 := by
  simp only [f.eqOn_source hs, (· ∘ ·), f.one_of_mem_closedBall hd]
/-
**SmoothBumpFunction.support_eq_inter_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Smooth
BumpFunction`。
形式化陈述：support_eq_inter_preimage : support f = (chartAt H c).source inter extChar
tAt I c ⁻¹' ball (extChartAt I c c) f.rOut
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsContDiffBumpBase.instHasContDiffBumpOfFiniteDimensionalReal`：∀ {E 
: Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDime
nsional ℝ E], HasContDiffBump E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SmoothBumpFunction.coe_def`：coe_def : ⇑f = indicator (chartAt H c).sourc
e (f.toContDiffBump ∘ extChartAt I c)
· 使用定理 `Set.support_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {
s : Set α} {f : α → M},   Function.support (s.indicator f) = s ∩ Function.suppor
t f
· 使用定理 `Function.support_comp_eq_preimage`：∀ {ι : Type u_1} {κ : Type u_2} {M : 
Type u_3} [inst : Zero M] (g : κ → M) (f : ι → κ),   Function.support (g ∘ f) = 
f ⁻¹' Function.support …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `PartialEquiv.symm_image_target_inter_eq'`：symm_image_target_inter_eq' (s
 : Set β) : e.symm '' (e.target inter s) = e.source inter e ⁻¹' s
· 使用定理 `ContDiffBump.support_eq`：support_eq : Function.support f = Metric.ball c
 f.rOut
-/
theorem support_eq_inter_preimage :
    support f = (chartAt H c).source ∩ extChartAt I c ⁻¹' ball (extChartAt I c c) f.rOut := by
  rw [coe_def, support_indicator, support_comp_eq_preimage, ← extChartAt_source I,
    ← (extChartAt I c).symm_image_target_inter_eq', ← (extChartAt I c).symm_image_target_inter_eq',
    f.support_eq]
/-
**SmoothBumpFunction.isOpen_support** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunctio
n`。
形式化陈述：isOpen_support : IsOpen (support f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SmoothBumpFunction.support_eq_inter_preimage`：support_eq_inter_preimage 
: support f = (chartAt H c).source inter extChartAt I c ⁻¹' ball (extChartAt I c
 c) f.rOut
· 使用定理 `isOpen_extChartAt_preimage`：isOpen_extChartAt_preimage (x : M) {s : Set 
E} (hs : IsOpen s) : IsOpen ((chartAt H x).source inter extChartAt I x ⁻¹' s)
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
-/
theorem isOpen_support : IsOpen (support f) := by
  rw [support_eq_inter_preimage]
  exact isOpen_extChartAt_preimage c isOpen_ball
/-
**SmoothBumpFunction.support_eq_symm_image** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBump
Function`。
形式化陈述：support_eq_symm_image : support f = (extChartAt I c).symm '' (ball (extCha
rtAt I c c) f.rOut inter range I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SmoothBumpFunction.support_eq_inter_preimage`：support_eq_inter_preimage 
: support f = (chartAt H c).source inter extChartAt I c ⁻¹' ball (extChartAt I c
 c) f.rOut
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `PartialEquiv.symm_image_target_inter_eq'`：symm_image_target_inter_eq' (s
 : Set β) : e.symm '' (e.target inter s) = e.source inter e ⁻¹' s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `SmoothBumpFunction.ball_inter_range_eq_ball_inter_target`：ball_inter_ran
ge_eq_ball_inter_target : ball (extChartAt I c c) f.rOut inter range I = ball (e
xtChartAt I c c) f.rOut inter (extChartAt I c)…
-/
theorem support_eq_symm_image :
    support f = (extChartAt I c).symm '' (ball (extChartAt I c c) f.rOut ∩ range I) := by
  rw [f.support_eq_inter_preimage, ← extChartAt_source I,
    ← (extChartAt I c).symm_image_target_inter_eq', inter_comm,
    ball_inter_range_eq_ball_inter_target]
/-
**SmoothBumpFunction.support_subset_source** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBump
Function`。
形式化陈述：support_subset_source : support f subseteq (chartAt H c).source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SmoothBumpFunction.support_eq_inter_preimage`：support_eq_inter_preimage 
: support f = (chartAt H c).source inter extChartAt I c ⁻¹' ball (extChartAt I c
 c) f.rOut
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem support_subset_source : support f ⊆ (chartAt H c).source := by
  rw [f.support_eq_inter_preimage, ← extChartAt_source I]; exact inter_subset_left
/-
**SmoothBumpFunction.image_eq_inter_preimage_of_subset_support** 是 Mathlib 中的一个定
理，位于命名空间 `SmoothBumpFunction`。
形式化陈述：image_eq_inter_preimage_of_subset_support {s : Set M} (hs : s subseteq sup
port f) : extChartAt I c '' s = closedBall (extChartAt I c c) f.rOut inter range
 I inter (extChartAt I c).symm ⁻¹' s
参数：hs : s subseteq support f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
· 使用定理 `SmoothBumpFunction.support_eq_inter_preimage`：support_eq_inter_preimage 
: support f = (chartAt H c).source inter extChartAt I c ⁻¹' ball (extChartAt I c
 c) f.rOut
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `PartialEquiv.image_eq_target_inter_inv_preimage`：image_eq_target_inter_i
nv_preimage {s : Set α} (h : s subseteq e.source) : e '' s = e.target inter e.sy
mm ⁻¹' s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `SmoothBumpFunction.closedBall_subset`：∀ {E : Type uE} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH} [inst_2 : TopologicalSpace 
H]   {I : ModelWithCorners…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem image_eq_inter_preimage_of_subset_support {s : Set M} (hs : s ⊆ support f) :
    extChartAt I c '' s =
      closedBall (extChartAt I c c) f.rOut ∩ range I ∩ (extChartAt I c).symm ⁻¹' s := by
  rw [support_eq_inter_preimage, subset_inter_iff, ← extChartAt_source I, ← image_subset_iff] at hs
  obtain ⟨hse, hsf⟩ := hs
  apply Subset.antisymm
  · refine subset_inter (subset_inter (hsf.trans ball_subset_closedBall) ?_) ?_
    · rintro _ ⟨x, -, rfl⟩; exact mem_range_self _
    · rw [(extChartAt I c).image_eq_target_inter_inv_preimage hse]
      exact inter_subset_right
  · refine Subset.trans (inter_subset_inter_left _ f.closedBall_subset) ?_
    rw [(extChartAt I c).image_eq_target_inter_inv_preimage hse]
/-
**SmoothBumpFunction.mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunction`。
形式化陈述：mem_Icc : f x in Icc (0 : Real) 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsContDiffBumpBase.instHasContDiffBumpOfFiniteDimensionalReal`：∀ {E 
: Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDime
nsional ℝ E], HasContDiffBump E
· 使用定理 `Set.indicator_eq_zero_or_self`：∀ {α : Type u_1} {M : Type u_3} [inst : Z
ero M] (s : Set α) (f : α → M) (a : α),   s.indicator f a = 0 ∨ s.indicator f a 
= f a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `ContDiffBump.nonneg`：nonneg : 0 <= f x
· 使用定理 `ContDiffBump.le_one`：le_one : f x <= 1
-/
theorem mem_Icc : f x ∈ Icc (0 : ℝ) 1 := by
  have : f x = 0 ∨ f x = _ := indicator_eq_zero_or_self _ _ _
  rcases this with h | h <;> rw [h]
  exacts [left_mem_Icc.2 zero_le_one, ⟨f.nonneg, f.le_one⟩]
/-
**SmoothBumpFunction.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunction`。
形式化陈述：nonneg : 0 <= f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SmoothBumpFunction.mem_Icc`：mem_Icc : f x in Icc (0 : Real) 1
-/
theorem nonneg : 0 ≤ f x :=
  f.mem_Icc.1
/-
**SmoothBumpFunction.le_one** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunction`。
形式化陈述：le_one : f x <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SmoothBumpFunction.mem_Icc`：mem_Icc : f x in Icc (0 : Real) 1
-/
theorem le_one : f x ≤ 1 :=
  f.mem_Icc.2
/-
**SmoothBumpFunction.eventuallyEq_one_of_dist_lt** 是 Mathlib 中的一个定理，位于命名空间 `Smoo
thBumpFunction`。
形式化陈述：eventuallyEq_one_of_dist_lt (hs : x in (chartAt H c).source) (hd : dist (e
xtChartAt I c x) (extChartAt I c c) < f.rIn) : f =ᶠ[𝓝 x] 1
参数：hs : x in (chartAt H c).source；hd : dist (extChartAt I c x) (extChartAt I c c
) < f.rIn。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_extChartAt_preimage`：isOpen_extChartAt_preimage (x : M) {s : Set 
E} (hs : IsOpen s) : IsOpen ((chartAt H x).source inter extChartAt I x ⁻¹' s)
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `SmoothBumpFunction.one_of_dist_le`：one_of_dist_le (hs : x in (chartAt H 
c).source) (hd : dist (extChartAt I c x) (extChartAt I c c) <= f.rIn) : f x = 1
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem eventuallyEq_one_of_dist_lt (hs : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) < f.rIn) : f =ᶠ[𝓝 x] 1 := by
  filter_upwards [IsOpen.mem_nhds (isOpen_extChartAt_preimage c isOpen_ball) ⟨hs, hd⟩]
  rintro z ⟨hzs, hzd⟩
  exact f.one_of_dist_le hzs <| le_of_lt hzd
/-
**SmoothBumpFunction.eventuallyEq_one** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunct
ion`。
形式化陈述：eventuallyEq_one : f =ᶠ[𝓝 c] 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothBumpFunction.eventuallyEq_one_of_dist_lt`：eventuallyEq_one_of_dist
_lt (hs : x in (chartAt H c).source) (hd : dist (extChartAt I c x) (extChartAt I
 c c) < f.rIn) : f =ᶠ[𝓝 x] 1
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `ContDiffBump.rIn_pos`：∀ {E : Type u_1} {c : E} (self : ContDiffBump c), 
0 < self.rIn
-/
theorem eventuallyEq_one : f =ᶠ[𝓝 c] 1 :=
  f.eventuallyEq_one_of_dist_lt (mem_chart_source _ _) <| by rw [dist_self]; exact f.rIn_pos

@[simp]
/-
**SmoothBumpFunction.eq_one** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunction`。
形式化陈述：eq_one : f c = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `SmoothBumpFunction.eventuallyEq_one`：eventuallyEq_one : f =ᶠ[𝓝 c] 1
-/
theorem eq_one : f c = 1 :=
  f.eventuallyEq_one.eq_of_nhds
/-
**SmoothBumpFunction.support_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunct
ion`。
形式化陈述：support_mem_nhds : support f in 𝓝 c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `SmoothBumpFunction.eventuallyEq_one`：eventuallyEq_one : f =ᶠ[𝓝 c] 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem support_mem_nhds : support f ∈ 𝓝 c :=
  f.eventuallyEq_one.mono fun x hx => by rw [hx]; exact one_ne_zero
/-
**SmoothBumpFunction.tsupport_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunc
tion`。
形式化陈述：tsupport_mem_nhds : tsupport f in 𝓝 c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `SmoothBumpFunction.support_mem_nhds`：support_mem_nhds : support f in 𝓝 c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem tsupport_mem_nhds : tsupport f ∈ 𝓝 c :=
  mem_of_superset f.support_mem_nhds subset_closure
/-
**SmoothBumpFunction.c_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunction
`。
形式化陈述：c_mem_support : c in support f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `SmoothBumpFunction.support_mem_nhds`：support_mem_nhds : support f in 𝓝 c
-/
theorem c_mem_support : c ∈ support f :=
  mem_of_mem_nhds f.support_mem_nhds
/-
**SmoothBumpFunction.nonempty_support** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunct
ion`。
形式化陈述：nonempty_support : (support f).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothBumpFunction.c_mem_support`：c_mem_support : c in support f
-/
theorem nonempty_support : (support f).Nonempty :=
  ⟨c, f.c_mem_support⟩
/-
**SmoothBumpFunction.isCompact_symm_image_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `
SmoothBumpFunction`。
形式化陈述：isCompact_symm_image_closedBall : IsCompact ((extChartAt I c).symm '' (clo
sedBall (extChartAt I c c) f.rOut inter range I))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `ModelWithCorners.isClosed_range`：isClosed_range : IsClosed (range I)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `continuousOn_extChartAt_symm`：continuousOn_extChartAt_symm (x : M) : Con
tinuousOn (extChartAt I x).symm (extChartAt I x).target
· 使用定理 `SmoothBumpFunction.closedBall_subset`：∀ {E : Type uE} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH} [inst_2 : TopologicalSpace 
H]   {I : ModelWithCorners…
-/
theorem isCompact_symm_image_closedBall :
    IsCompact ((extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I)) :=
  ((isCompact_closedBall _ _).inter_right I.isClosed_range).image_of_continuousOn <|
    (continuousOn_extChartAt_symm _).mono f.closedBall_subset

end FiniteDimensional

/-- Given a smooth bump function `f : SmoothBumpFunction I c`, the closed ball of radius `f.R` is
known to include the support of `f`. These closed balls (in the model normed space `E`) intersected
with `Set.range I` form a basis of `𝓝[range I] (extChartAt I c c)`. -/
/-
**SmoothBumpFunction.nhdsWithin_range_basis** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBum
pFunction`。
形式化陈述：nhdsWithin_range_basis : (𝓝[range I] extChartAt I c c).HasBasis (fun _ : S
moothBumpFunction I c => True) fun f => closedBall (extChartAt I c c) f.rOut int
er range I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' 
→ Set α},   l.HasB…
· 使用定理 `Filter.HasBasis.restrict_subset`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fi
lter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {V : Set α}, V ∈ l 
→ l.HasBasis (fun i =…
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
· 使用定理 `trivial`：True
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
· 使用定理 `SmoothBumpFunction.rOut_pos`：rOut_pos : 0 < f.rOut
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a

--- 原说明 ---
Given a smooth bump function `f : SmoothBumpFunction I c`, the closed ball of ra
dius `f.R` is
known to include the support of `f`. These closed balls (in the model normed spa
ce `E`) intersected
with `Set.range I` form a basis of `𝓝[range I] (extChartAt I c c)`.
-/
theorem nhdsWithin_range_basis :
    (𝓝[range I] extChartAt I c c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f =>
      closedBall (extChartAt I c c) f.rOut ∩ range I := by
  refine ((nhdsWithin_hasBasis nhds_basis_closedBall _).restrict_subset
    (extChartAt_target_mem_nhdsWithin _)).to_hasBasis' ?_ ?_
  · rintro R ⟨hR0, hsub⟩
    exact ⟨⟨⟨R / 2, R, half_pos hR0, half_lt_self hR0⟩, hsub⟩, trivial, Subset.rfl⟩
  · exact fun f _ => inter_mem (mem_nhdsWithin_of_mem_nhds <| closedBall_mem_nhds _ f.rOut_pos)
      self_mem_nhdsWithin

variable [FiniteDimensional ℝ E]
/-
**SmoothBumpFunction.isClosed_image_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Smoot
hBumpFunction`。
形式化陈述：isClosed_image_of_isClosed {s : Set M} (hsc : IsClosed s) (hs : s subseteq
 support f) : IsClosed (extChartAt I c '' s)
参数：hsc : IsClosed s；hs : s subseteq support f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SmoothBumpFunction.image_eq_inter_preimage_of_subset_support`：image_eq_i
nter_preimage_of_subset_support {s : Set M} (hs : s subseteq support f) : extCha
rtAt I c '' s = closedBall (extChartAt I c c) f.rO…
· 使用定理 `ContinuousOn.preimage_isClosed_of_isClosed`：ContinuousOn.preimage_isClos
ed_of_isClosed {t : Set β} (hf : ContinuousOn f s) (hs : IsClosed s) (ht : IsClo
sed t) : IsClosed (s inter f ⁻¹'…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `continuousOn_extChartAt_symm`：continuousOn_extChartAt_symm (x : M) : Con
tinuousOn (extChartAt I x).symm (extChartAt I x).target
· 使用定理 `SmoothBumpFunction.closedBall_subset`：∀ {E : Type uE} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH} [inst_2 : TopologicalSpace 
H]   {I : ModelWithCorners…
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
· 使用定理 `ModelWithCorners.isClosed_range`：isClosed_range : IsClosed (range I)
-/
theorem isClosed_image_of_isClosed {s : Set M} (hsc : IsClosed s) (hs : s ⊆ support f) :
    IsClosed (extChartAt I c '' s) := by
  rw [f.image_eq_inter_preimage_of_subset_support hs]
  refine ContinuousOn.preimage_isClosed_of_isClosed
    ((continuousOn_extChartAt_symm _).mono f.closedBall_subset) ?_ hsc
  exact IsClosed.inter isClosed_closedBall I.isClosed_range

/-- If `f` is a smooth bump function and `s` closed subset of the support of `f` (i.e., of the open
ball of radius `f.rOut`), then there exists `0 < r < f.rOut` such that `s` is a subset of the open
ball of radius `r`. Formally, `s ⊆ e.source ∩ e ⁻¹' (ball (e c) r)`, where `e = extChartAt I c`. -/
/-
**SmoothBumpFunction.exists_r_pos_lt_subset_ball** 是 Mathlib 中的一个定理，位于命名空间 `Smoo
thBumpFunction`。
形式化陈述：exists_r_pos_lt_subset_ball {s : Set M} (hsc : IsClosed s) (hs : s subsete
q support f) : exists r in Ioo 0 f.rOut, s subseteq (chartAt H c).source inter e
xtChartAt I c ⁻¹' ball (extChartAt I c c) r
参数：hsc : IsClosed s；hs : s subseteq support f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothBumpFunction.isClosed_image_of_isClosed`：isClosed_image_of_isClose
d {s : Set M} (hsc : IsClosed s) (hs : s subseteq support f) : IsClosed (extChar
tAt I c '' s)
· 使用定理 `exists_pos_lt_subset_ball`：exists_pos_lt_subset_ball (hr : 0 < r) (hs : 
IsClosed s) (h : s subseteq ball x r) : exists r' in Ioo 0 r, s subseteq ball x 
r'
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `SmoothBumpFunction.rOut_pos`：rOut_pos : 0 < f.rOut
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
· 使用定理 `SmoothBumpFunction.support_eq_inter_preimage`：support_eq_inter_preimage 
: support f = (chartAt H c).source inter extChartAt I c ⁻¹' ball (extChartAt I c
 c) f.rOut
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
If `f` is a smooth bump function and `s` closed subset of the support of `f` (i.
e., of the open
ball of radius `f.rOut`), then there exists `0 < r < f.rOut` such that `s` is a 
subset of the open
ball of radius `r`. Formally, `s ⊆ e.source ∩ e ⁻¹' (ball (e c) r)`, where `e = 
extChartAt I c`.
-/
theorem exists_r_pos_lt_subset_ball {s : Set M} (hsc : IsClosed s) (hs : s ⊆ support f) :
    ∃ r ∈ Ioo 0 f.rOut,
      s ⊆ (chartAt H c).source ∩ extChartAt I c ⁻¹' ball (extChartAt I c c) r := by
  set e := extChartAt I c
  have : IsClosed (e '' s) := f.isClosed_image_of_isClosed hsc hs
  rw [support_eq_inter_preimage, subset_inter_iff, ← image_subset_iff] at hs
  rcases exists_pos_lt_subset_ball f.rOut_pos this hs.2 with ⟨r, hrR, hr⟩
  exact ⟨r, hrR, subset_inter hs.1 (image_subset_iff.1 hr)⟩

/-- Replace `rIn` with another value in the interval `(0, f.rOut)`. -/
@[simps rOut rIn]
/-
**SmoothBumpFunction.updateRIn** 是 Mathlib 中的一个定义，位于命名空间 `SmoothBumpFunction`。
形式化陈述：updateRIn (r : Real) (hr : r in Ioo 0 f.rOut) : SmoothBumpFunction I c
参数：r : Real；hr : r in Ioo 0 f.rOut。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothBumpFunction.closedBall_subset`：∀ {E : Type uE} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH} [inst_2 : TopologicalSpace 
H]   {I : ModelWithCorners…

--- 原说明 ---
Replace `rIn` with another value in the interval `(0, f.rOut)`.
-/
def updateRIn (r : ℝ) (hr : r ∈ Ioo 0 f.rOut) : SmoothBumpFunction I c :=
  ⟨⟨r, f.rOut, hr.1, hr.2⟩, f.closedBall_subset⟩

@[simp]
/-
**SmoothBumpFunction.support_updateRIn** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunc
tion`。
形式化陈述：support_updateRIn {r : Real} (hr : r in Ioo 0 f.rOut) : support (f.updateR
In r hr) = support f
参数：hr : r in Ioo 0 f.rOut。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SmoothBumpFunction.support_eq_inter_preimage`：support_eq_inter_preimage 
: support f = (chartAt H c).source inter extChartAt I c ⁻¹' ball (extChartAt I c
 c) f.rOut
· 使用定理 `SmoothBumpFunction.updateRIn_rOut`：∀ {E : Type uE} [inst : NormedAddComm
Group E] [inst_1 : NormedSpace ℝ E] {H : Type uH} [inst_2 : TopologicalSpace H] 
  {I : ModelWithCorners…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem support_updateRIn {r : ℝ} (hr : r ∈ Ioo 0 f.rOut) :
    support (f.updateRIn r hr) = support f := by
  simp only [support_eq_inter_preimage, updateRIn_rOut]
/-
**SmoothBumpFunction.** 是 Mathlib 中的一个实例，位于命名空间 `SmoothBumpFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (SmoothBumpFunction I c) := nhdsWithin_range_basis.nonempty

variable [T2Space M]
/-
**SmoothBumpFunction.isClosed_symm_image_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `S
moothBumpFunction`。
形式化陈述：isClosed_symm_image_closedBall : IsClosed ((extChartAt I c).symm '' (close
dBall (extChartAt I c c) f.rOut inter range I))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `SmoothBumpFunction.isCompact_symm_image_closedBall`：isCompact_symm_image
_closedBall : IsCompact ((extChartAt I c).symm '' (closedBall (extChartAt I c c)
 f.rOut inter range I))
-/
theorem isClosed_symm_image_closedBall :
    IsClosed ((extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I)) :=
  f.isCompact_symm_image_closedBall.isClosed
/-
**SmoothBumpFunction.tsupport_subset_symm_image_closedBall** 是 Mathlib 中的一个定理，位于
命名空间 `SmoothBumpFunction`。
形式化陈述：tsupport_subset_symm_image_closedBall : tsupport f subseteq (extChartAt I 
c).symm '' (closedBall (extChartAt I c c) f.rOut inter range I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsupport.eq_1`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst_1 :
 TopologicalSpace X] (f : X → α),   tsupport f = closure (Function.support f)
· 使用定理 `SmoothBumpFunction.support_eq_symm_image`：support_eq_symm_image : suppor
t f = (extChartAt I c).symm '' (ball (extChartAt I c c) f.rOut inter range I)
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `SmoothBumpFunction.isClosed_symm_image_closedBall`：isClosed_symm_image_c
losedBall : IsClosed ((extChartAt I c).symm '' (closedBall (extChartAt I c c) f.
rOut inter range I))
-/
theorem tsupport_subset_symm_image_closedBall :
    tsupport f ⊆ (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I) := by
  rw [tsupport, support_eq_symm_image]
  exact closure_minimal (image_mono <| inter_subset_inter_left _ ball_subset_closedBall)
    f.isClosed_symm_image_closedBall
/-
**SmoothBumpFunction.tsupport_subset_extChartAt_source** 是 Mathlib 中的一个定理，位于命名空间
 `SmoothBumpFunction`。
形式化陈述：tsupport_subset_extChartAt_source : tsupport f subseteq (extChartAt I c).s
ource
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SmoothBumpFunction.tsupport_subset_symm_image_closedBall`：tsupport_subse
t_symm_image_closedBall : tsupport f subseteq (extChartAt I c).symm '' (closedBa
ll (extChartAt I c c) f.rOut inter range I)
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `SmoothBumpFunction.closedBall_subset`：∀ {E : Type uE} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type uH} [inst_2 : TopologicalSpace 
H]   {I : ModelWithCorners…
· 使用定理 `PartialEquiv.symm_image_target_eq_source`：symm_image_target_eq_source : 
e.symm '' e.target = e.source
-/
theorem tsupport_subset_extChartAt_source : tsupport f ⊆ (extChartAt I c).source :=
  calc
    tsupport f ⊆ (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I) :=
      f.tsupport_subset_symm_image_closedBall
    _ ⊆ (extChartAt I c).symm '' (extChartAt I c).target := image_mono f.closedBall_subset
    _ = (extChartAt I c).source := (extChartAt I c).symm_image_target_eq_source
/-
**SmoothBumpFunction.tsupport_subset_chartAt_source** 是 Mathlib 中的一个定理，位于命名空间 `S
moothBumpFunction`。
形式化陈述：tsupport_subset_chartAt_source : tsupport f subseteq (chartAt H c).source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `SmoothBumpFunction.tsupport_subset_extChartAt_source`：tsupport_subset_ex
tChartAt_source : tsupport f subseteq (extChartAt I c).source
-/
theorem tsupport_subset_chartAt_source : tsupport f ⊆ (chartAt H c).source := by
  simpa only [extChartAt_source] using f.tsupport_subset_extChartAt_source
/-
**SmoothBumpFunction.hasCompactSupport** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunc
tion`。
形式化陈述：∀ {E : Type uE} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {
H : Type uH} [inst_2 : TopologicalSpace H]   {I : ModelWithCorners ℝ E H} {M : T
ype uM} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M] {c : M}   (f :
 SmoothBumpFunction I c) [inst_5 : FiniteDimensional ℝ E] [T2Space M], HasCompac
tSupport ↑f
参数：f : SmoothBumpFunction I c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `SmoothBumpFunction.isCompact_symm_image_closedBall`：isCompact_symm_image
_closedBall : IsCompact ((extChartAt I c).symm '' (closedBall (extChartAt I c c)
 f.rOut inter range I))
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `SmoothBumpFunction.tsupport_subset_symm_image_closedBall`：tsupport_subse
t_symm_image_closedBall : tsupport f subseteq (extChartAt I c).symm '' (closedBa
ll (extChartAt I c c) f.rOut inter range I)
-/
protected theorem hasCompactSupport : HasCompactSupport f :=
  f.isCompact_symm_image_closedBall.of_isClosed_subset isClosed_closure
    f.tsupport_subset_symm_image_closedBall

variable (c) in
/-- The closures of supports of smooth bump functions centered at `c` form a basis of `𝓝 c`.
In other words, each of these closures is a neighborhood of `c` and each neighborhood of `c`
includes `tsupport f` for some `f : SmoothBumpFunction I c`. -/
/-
**SmoothBumpFunction.nhds_basis_tsupport** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFu
nction`。
形式化陈述：nhds_basis_tsupport : (𝓝 c).HasBasis (fun _ : SmoothBumpFunction I c => Tr
ue) fun f => tsupport f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_extChartAt_symm_nhdsWithin_range`：map_extChartAt_symm_nhdsWithin_ran
ge (x : M) : map (extChartAt I x).symm (𝓝[range I] extChartAt I x x) = 𝓝 x
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `SmoothBumpFunction.nhdsWithin_range_basis`：nhdsWithin_range_basis : (𝓝[r
ange I] extChartAt I c c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun 
f => closedBall (extChartAt I c…
· 使用定理 `Filter.HasBasis.to_hasBasis'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' 
→ Set α},   l.HasB…
· 使用定理 `trivial`：True
· 使用定理 `SmoothBumpFunction.tsupport_subset_symm_image_closedBall`：tsupport_subse
t_symm_image_closedBall : tsupport f subseteq (extChartAt I c).symm '' (closedBa
ll (extChartAt I c c) f.rOut inter range I)
· 使用定理 `SmoothBumpFunction.tsupport_mem_nhds`：tsupport_mem_nhds : tsupport f in 
𝓝 c

--- 原说明 ---
The closures of supports of smooth bump functions centered at `c` form a basis o
f `𝓝 c`.
In other words, each of these closures is a neighborhood of `c` and each neighbo
rhood of `c`
includes `tsupport f` for some `f : SmoothBumpFunction I c`.
-/
theorem nhds_basis_tsupport :
    (𝓝 c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f => tsupport f := by
  have :
    (𝓝 c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f =>
      (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I) := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) c]
    exact nhdsWithin_range_basis.map _
  exact this.to_hasBasis' (fun f _ => ⟨f, trivial, f.tsupport_subset_symm_image_closedBall⟩)
    fun f _ => f.tsupport_mem_nhds

/-- Given `s ∈ 𝓝 c`, the supports of smooth bump functions `f : SmoothBumpFunction I c` such that
`tsupport f ⊆ s` form a basis of `𝓝 c`.  In other words, each of these supports is a
neighborhood of `c` and each neighborhood of `c` includes `support f` for some
`f : SmoothBumpFunction I c` such that `tsupport f ⊆ s`. -/
/-
**SmoothBumpFunction.nhds_basis_support** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFun
ction`。
形式化陈述：nhds_basis_support {s : Set M} (hs : s in 𝓝 c) : (𝓝 c).HasBasis (fun f : S
moothBumpFunction I c => tsupport f subseteq s) fun f => support f
参数：hs : s in 𝓝 c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' 
→ Set α},   l.HasB…
· 使用定理 `Filter.HasBasis.restrict_subset`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fi
lter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {V : Set α}, V ∈ l 
→ l.HasBasis (fun i =…
· 使用定理 `SmoothBumpFunction.nhds_basis_tsupport`：nhds_basis_tsupport : (𝓝 c).HasB
asis (fun _ : SmoothBumpFunction I c => True) fun f => tsupport f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `SmoothBumpFunction.support_mem_nhds`：support_mem_nhds : support f in 𝓝 c

--- 原说明 ---
Given `s ∈ 𝓝 c`, the supports of smooth bump functions `f : SmoothBumpFunction I
 c` such that
`tsupport f ⊆ s` form a basis of `𝓝 c`.  In other words, each of these supports 
is a
neighborhood of `c` and each neighborhood of `c` includes `support f` for some
`f : SmoothBumpFunction I c` such that `tsupport f ⊆ s`.
-/
theorem nhds_basis_support {s : Set M} (hs : s ∈ 𝓝 c) :
    (𝓝 c).HasBasis (fun f : SmoothBumpFunction I c => tsupport f ⊆ s) fun f => support f :=
  ((nhds_basis_tsupport c).restrict_subset hs).to_hasBasis'
    (fun f hf => ⟨f, hf.2, subset_closure⟩) fun f _ => f.support_mem_nhds

variable [IsManifold I ∞ M]

/-- A smooth bump function is infinitely smooth. -/
/-
**SmoothBumpFunction.contMDiff** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunction`。
形式化陈述：∀ {E : Type uE} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {
H : Type uH} [inst_2 : TopologicalSpace H]   {I : ModelWithCorners ℝ E H} {M : T
ype uM} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M] {c : M}   (f :
 SmoothBumpFunction I c) [inst_5 : FiniteDimensional ℝ E] [T2Space M] [IsManifol
d I (↑⊤) M],   ContMDiff I (modelWithCornersSelf ℝ ℝ) ↑⊤ ↑f
参数：f : SmoothBumpFunction I c；↑⊤；modelWithCornersSelf ℝ ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiff_of_tsupport`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `SmoothBumpFunction.tsupport_subset_chartAt_source`：tsupport_subset_chart
At_source : tsupport f subseteq (chartAt H c).source
· 使用定理 `ContMDiffAt.congr_of_eventuallyEq`：ContMDiffAt.congr_of_eventuallyEq (h 
: ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMDiffAt I I' n f₁ x
· 使用定理 `ExistsContDiffBumpBase.instHasContDiffBumpOfFiniteDimensionalReal`：∀ {E 
: Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDime
nsional ℝ E], HasContDiffBump E
· 使用定理 `ContMDiffAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `ContDiffAt.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{E' : Type u…
· 使用定理 `ContDiffBump.contDiffAt`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] [inst_2 : HasContDiffBump E] {c : E}   (f : ContDiffB
ump c) {x : E…
· 使用定理 `contMDiffAt_extChartAt'`：contMDiffAt_extChartAt' [IsManifold I n M] {x' 
: M} (h : x' in (chartAt H x).source) : ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x)
 x'
· 使用定理 `Set.EqOn.eventuallyEq_of_mem`：Set.EqOn.eventuallyEq_of_mem {α β} {s : Se
t α} {l : Filter α} {f g : α -> β} (h : EqOn f g s) (hl : s in l) : f =ᶠ[l] g
· 使用定理 `SmoothBumpFunction.eqOn_source`：eqOn_source : EqOn f (f.toContDiffBump ∘
 extChartAt I c) (chartAt H c).source
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
A smooth bump function is infinitely smooth.
-/
protected theorem contMDiff : CMDiff ∞ f := by
  refine contMDiff_of_tsupport fun x hx => ?_
  have : x ∈ (chartAt H c).source := f.tsupport_subset_chartAt_source hx
  refine ContMDiffAt.congr_of_eventuallyEq ?_ <| f.eqOn_source.eventuallyEq_of_mem <|
    (chartAt H c).open_source.mem_nhds this
  exact f.contDiffAt.contMDiffAt.comp _ (contMDiffAt_extChartAt' this)
/-
**SmoothBumpFunction.contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunction`。
形式化陈述：∀ {E : Type uE} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {
H : Type uH} [inst_2 : TopologicalSpace H]   {I : ModelWithCorners ℝ E H} {M : T
ype uM} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M] {c : M}   (f :
 SmoothBumpFunction I c) [inst_5 : FiniteDimensional ℝ E] [T2Space M] [IsManifol
d I (↑⊤) M] {x : M},   ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (↑⊤) (↑f) x
参数：f : SmoothBumpFunction I c；↑⊤；modelWithCornersSelf ℝ ℝ；↑⊤；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `SmoothBumpFunction.contMDiff`：∀ {E : Type uE} [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] {H : Type uH} [inst_2 : TopologicalSpace H]   {I 
: ModelWithCorners…
-/
protected theorem contMDiffAt {x} : CMDiffAt ∞ f x :=
  f.contMDiff.contMDiffAt
/-
**SmoothBumpFunction.continuous** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunction`。
形式化陈述：∀ {E : Type uE} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {
H : Type uH} [inst_2 : TopologicalSpace H]   {I : ModelWithCorners ℝ E H} {M : T
ype uM} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M] {c : M}   (f :
 SmoothBumpFunction I c) [inst_5 : FiniteDimensional ℝ E] [T2Space M] [IsManifol
d I (↑⊤) M], Continuous ↑f
参数：f : SmoothBumpFunction I c；↑⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.continuous`：ContMDiff.continuous (hf : ContMDiff I I' n f) : C
ontinuous f
· 使用定理 `SmoothBumpFunction.contMDiff`：∀ {E : Type uE} [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] {H : Type uH} [inst_2 : TopologicalSpace H]   {I 
: ModelWithCorners…
-/
protected theorem continuous : Continuous f :=
  f.contMDiff.continuous

/-- If `f : SmoothBumpFunction I c` is a smooth bump function and `g : M → G` is a function smooth
on the source of the chart at `c`, then `f • g` is smooth on the whole manifold. -/
/-
**SmoothBumpFunction.contMDiff_smul** 是 Mathlib 中的一个定理，位于命名空间 `SmoothBumpFunctio
n`。
形式化陈述：contMDiff_smul {G} [NormedAddCommGroup G] [NormedSpace Real G] {g : M -> G
} (hg : CMDiff[(chartAt H c).source] ∞ g) : CMDiff ∞ fun x => f x • g x
参数：hg : CMDiff[(chartAt H c).source] ∞ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiff_of_tsupport`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `SmoothBumpFunction.tsupport_subset_chartAt_source`：tsupport_subset_chart
At_source : tsupport f subseteq (chartAt H c).source
· 使用定理 `tsupport_smul_subset_left`：tsupport_smul_subset_left {M α} [Zero M] [Zer
o α] [SMulWithZero M α] (f : X -> M) (g : X -> α) : (tsupport fun x => f x • g x
) subseteq tsup…
· 使用定理 `ContMDiffAt.smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H
 : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddC
ommGro…
· 使用定理 `instContMDiffSMulModelWithCornersSelf`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {n : WithTop…
· 使用定理 `SmoothBumpFunction.contMDiffAt`：∀ {E : Type uE} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {H : Type uH} [inst_2 : TopologicalSpace H]   {
I : ModelWithCorners…
· 使用定理 `ContMDiffWithinAt.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
If `f : SmoothBumpFunction I c` is a smooth bump function and `g : M → G` is a f
unction smooth
on the source of the chart at `c`, then `f • g` is smooth on the whole manifold.
-/
theorem contMDiff_smul {G} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : M → G}
    (hg : CMDiff[(chartAt H c).source] ∞ g) : CMDiff ∞ fun x => f x • g x := by
  refine contMDiff_of_tsupport fun x hx => ?_
  -- Porting note: was a more readable `calc`
  -- calc
  --   x ∈ tsupport fun x => f x • g x := hx
  --   _ ⊆ tsupport f := tsupport_smul_subset_left _ _
  --   _ ⊆ (chart_at _ c).source := f.tsupport_subset_chartAt_source
  have : x ∈ (chartAt H c).source :=
    f.tsupport_subset_chartAt_source <| tsupport_smul_subset_left _ _ hx
  exact f.contMDiffAt.smul ((hg _ this).contMDiffAt <| (chartAt _ _).open_source.mem_nhds this)

end SmoothBumpFunction

