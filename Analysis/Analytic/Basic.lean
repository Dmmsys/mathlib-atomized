/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Analytic functions

A function is analytic in one dimension around `0` if it can be written as a converging power series
`Σ pₙ zⁿ`. This definition can be extended to any dimension (even in infinite dimension) by
requiring that `pₙ` is a continuous `n`-multilinear map. In general, `pₙ` is not unique (in two
dimensions, taking `p₂ (x, y) (x', y') = x y'` or `y x'` gives the same map when applied to a
vector `(x, y) (x, y)`). A way to guarantee uniqueness is to take a symmetric `pₙ`, but this is not
always possible in nonzero characteristic (in characteristic 2, the previous example has no
symmetric representative). Therefore, we do not insist on symmetry or uniqueness in the definition,
and we only require the existence of a converging series.

The general framework is important to say that the exponential map on bounded operators on a Banach
space is analytic, as well as the inverse on invertible operators.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`.

* `HasFPowerSeriesOnBall f p x r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₙ yⁿ`.
* `HasFPowerSeriesAt f p x`: on some ball of center `x` with positive radius, holds
  `HasFPowerSeriesOnBall f p x r`.
* `AnalyticAt 𝕜 f x`: there exists a power series `p` such that holds `HasFPowerSeriesAt f p x`.
* `AnalyticOnNhd 𝕜 f s`: the function `f` is analytic at every point of `s`.

We also define versions of `HasFPowerSeriesOnBall`, `AnalyticAt`, and `AnalyticOnNhd` restricted to
a set, similar to `ContinuousWithinAt`.
See `Mathlib/Analysis/Analytic/Within.lean` for basic properties.

* `AnalyticWithinAt 𝕜 f s x` means a power series at `x` converges to `f` on `𝓝[s ∪ {x}] x`.
* `AnalyticOn 𝕜 f s t` means `∀ x ∈ t, AnalyticWithinAt 𝕜 f s x`.

We develop the basic properties of these notions, notably:
* If a function admits a power series, it is continuous (see
  `HasFPowerSeriesOnBall.continuousOn` and `HasFPowerSeriesAt.continuousAt` and
  `AnalyticAt.continuousAt`).
* In a complete space, the sum of a formal power series with positive radius is well defined on the
  disk of convergence, see `FormalMultilinearSeries.hasFPowerSeriesOnBall`.

-/

@[expose] public section

variable {𝕜 E F G : Type*}

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open Topology NNReal Filter ENNReal Set Asymptotics
open scoped Pointwise

/-! ### Expanding a function as a power series -/

section

variable {f g : E → F} {p pf : FormalMultilinearSeries 𝕜 E F} {s t : Set E} {x : E} {r r' : ℝ≥0∞}

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series on the ball of radius `r > 0` around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `‖y‖ < r`.
-/
/-
**HasFPowerSeriesOnBall** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField 𝕜] →         [inst_1 : NormedAddCommGroup E] →           [i
nst_2 : NormedSpace 𝕜 E] →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] → (E → F) → FormalMultilinearSeries 𝕜 E F → E 
→ ENNReal → Prop
参数：E → F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : E → F` and a formal multilinear series `p`, we say that `f
` has `p` as
a power series on the ball of radius `r > 0` around `x` if `f (x + y) = ∑' pₙ yⁿ
` for all `‖y‖ < r`.
-/
structure HasFPowerSeriesOnBall (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (r : ℝ≥0∞) :
    Prop where
  r_le : r ≤ p.radius
  r_pos : 0 < r
  hasSum :
    ∀ {y}, y ∈ Metric.eball (0 : E) r → HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y))

/-- Analogue of `HasFPowerSeriesOnBall` where convergence is required only on a set `s`. We also
require convergence at `x` as the behavior of this notion is very bad otherwise. -/
/-
**HasFPowerSeriesWithinOnBall** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField 𝕜] →         [inst_1 : NormedAddCommGroup E] →           [i
nst_2 : NormedSpace 𝕜 E] →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] → (E → F) → FormalMultilinearSeries 𝕜 E F → Se
t E → E → ENNReal → Prop
参数：E → F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Analogue of `HasFPowerSeriesOnBall` where convergence is required only on a set 
`s`. We also
require convergence at `x` as the behavior of this notion is very bad otherwise.
-/
structure HasFPowerSeriesWithinOnBall (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (s : Set E)
    (x : E) (r : ℝ≥0∞) : Prop where
  /-- `p` converges on `ball 0 r` -/
  r_le : r ≤ p.radius
  /-- The radius of convergence is positive -/
  r_pos : 0 < r
  /-- `p converges to f` within `s` -/
  hasSum : ∀ {y}, x + y ∈ insert x s → y ∈ Metric.eball (0 : E) r →
    HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y))

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `y` in a neighborhood of `0`. -/
/-
**HasFPowerSeriesAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (x : E)
参数：f : E -> F；p : FormalMultilinearSeries 𝕜 E F；x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : E → F` and a formal multilinear series `p`, we say that `f
` has `p` as
a power series around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `y` in a neighborhoo
d of `0`.
-/
def HasFPowerSeriesAt (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) :=
  ∃ r, HasFPowerSeriesOnBall f p x r

/-- Analogue of `HasFPowerSeriesAt` where convergence is required only on a set `s`. -/
/-
**HasFPowerSeriesWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (
s : Set E) (x : E)
参数：f : E -> F；p : FormalMultilinearSeries 𝕜 E F；s : Set E；x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Analogue of `HasFPowerSeriesAt` where convergence is required only on a set `s`.
-/
def HasFPowerSeriesWithinAt (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (s : Set E) (x : E) :=
  ∃ r, HasFPowerSeriesWithinOnBall f p s x r

-- Teach the `bound` tactic that power series have positive radius
attribute [bound_forward] HasFPowerSeriesOnBall.r_pos HasFPowerSeriesWithinOnBall.r_pos

variable (𝕜)

/-- Given a function `f : E → F`, we say that `f` is analytic at `x` if it admits a convergent power
series expansion around `x`. -/
@[fun_prop]
/-
**AnalyticAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AnalyticAt (f : E -> F) (x : E)
参数：f : E -> F；x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : E → F`, we say that `f` is analytic at `x` if it admits a 
convergent power
series expansion around `x`.
-/
def AnalyticAt (f : E → F) (x : E) :=
  ∃ p : FormalMultilinearSeries 𝕜 E F, HasFPowerSeriesAt f p x

/-- `f` is analytic within `s` at `x` if it has a power series at `x` that converges on `𝓝[s] x` -/
/-
**AnalyticWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AnalyticWithinAt (f : E -> F) (s : Set E) (x : E) : Prop
参数：f : E -> F；s : Set E；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is analytic within `s` at `x` if it has a power series at `x` that converges
 on `𝓝[s] x`
-/
def AnalyticWithinAt (f : E → F) (s : Set E) (x : E) : Prop :=
  ∃ p : FormalMultilinearSeries 𝕜 E F, HasFPowerSeriesWithinAt f p s x

/-- Given a function `f : E → F`, we say that `f` is analytic on a set `s` if it is analytic around
every point of `s`. -/
/-
**AnalyticOnNhd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AnalyticOnNhd (f : E -> F) (s : Set E)
参数：f : E -> F；s : Set E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : E → F`, we say that `f` is analytic on a set `s` if it is 
analytic around
every point of `s`.
-/
def AnalyticOnNhd (f : E → F) (s : Set E) :=
  ∀ x, x ∈ s → AnalyticAt 𝕜 f x

/-- `f` is analytic within `s` if it is analytic within `s` at each point of `s`.  Note that
this is weaker than `AnalyticOnNhd 𝕜 f s`, as `f` is allowed to be arbitrary outside `s`. -/
/-
**AnalyticOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AnalyticOn (f : E -> F) (s : Set E) : Prop
参数：f : E -> F；s : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is analytic within `s` if it is analytic within `s` at each point of `s`.  N
ote that
this is weaker than `AnalyticOnNhd 𝕜 f s`, as `f` is allowed to be arbitrary out
side `s`.
-/
def AnalyticOn (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, AnalyticWithinAt 𝕜 f s x

/-!
### `HasFPowerSeriesOnBall` and `HasFPowerSeriesWithinOnBall`
-/

variable {𝕜}

/-
**HasFPowerSeriesOnBall.hasFPowerSeriesAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.hasFPowerSeriesAt (hf : HasFPowerSeriesOnBall f p x 
r) : HasFPowerSeriesAt f p x
参数：hf : HasFPowerSeriesOnBall f p x r。
该定理/引理描述了相关对象所满足的性质。
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
-/
theorem HasFPowerSeriesOnBall.hasFPowerSeriesAt (hf : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesAt f p x :=
  ⟨r, hf⟩
/-
**HasFPowerSeriesAt.analyticAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.analyticAt (hf : HasFPowerSeriesAt f p x) : AnalyticAt 𝕜
 f x
参数：hf : HasFPowerSeriesAt f p x。
该定理/引理描述了相关对象所满足的性质。
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
-/
theorem HasFPowerSeriesAt.analyticAt (hf : HasFPowerSeriesAt f p x) : AnalyticAt 𝕜 f x :=
  ⟨p, hf⟩
/-
**HasFPowerSeriesOnBall.analyticAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.analyticAt (hf : HasFPowerSeriesOnBall f p x r) : An
alyticAt 𝕜 f x
参数：hf : HasFPowerSeriesOnBall f p x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesAt.analyticAt`：HasFPowerSeriesAt.analyticAt (hf : HasFPow
erSeriesAt f p x) : AnalyticAt 𝕜 f x
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
-/
theorem HasFPowerSeriesOnBall.analyticAt (hf : HasFPowerSeriesOnBall f p x r) : AnalyticAt 𝕜 f x :=
  hf.hasFPowerSeriesAt.analyticAt
/-
**HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt (hf : HasFPowerSeriesW
ithinOnBall f p s x r) : HasFPowerSeriesWithinAt f p s x
参数：hf : HasFPowerSeriesWithinOnBall f p s x r。
该定理/引理描述了相关对象所满足的性质。
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
-/
theorem HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt
    (hf : HasFPowerSeriesWithinOnBall f p s x r) : HasFPowerSeriesWithinAt f p s x :=
  ⟨r, hf⟩
/-
**HasFPowerSeriesWithinAt.analyticWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.analyticWithinAt (hf : HasFPowerSeriesWithinAt f p
 s x) : AnalyticWithinAt 𝕜 f s x
参数：hf : HasFPowerSeriesWithinAt f p s x。
该定理/引理描述了相关对象所满足的性质。
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
-/
theorem HasFPowerSeriesWithinAt.analyticWithinAt (hf : HasFPowerSeriesWithinAt f p s x) :
    AnalyticWithinAt 𝕜 f s x := ⟨p, hf⟩
/-
**HasFPowerSeriesWithinOnBall.analyticWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.analyticWithinAt (hf : HasFPowerSeriesWithinOn
Ball f p s x r) : AnalyticWithinAt 𝕜 f s x
参数：hf : HasFPowerSeriesWithinOnBall f p s x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesWithinAt.analyticWithinAt`：HasFPowerSeriesWithinAt.analyt
icWithinAt (hf : HasFPowerSeriesWithinAt f p s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt`：HasFPowerSeriesWith
inOnBall.hasFPowerSeriesWithinAt (hf : HasFPowerSeriesWithinOnBall f p s x r) : 
HasFPowerSeriesWithinAt f p s x
-/
theorem HasFPowerSeriesWithinOnBall.analyticWithinAt (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    AnalyticWithinAt 𝕜 f s x :=
  hf.hasFPowerSeriesWithinAt.analyticWithinAt

/-- If a function `f` has a power series `p` around `x`, then the function `z ↦ f (z - y)` has the
same power series around `x + y`. -/
/-
**HasFPowerSeriesOnBall.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.comp_sub (hf : HasFPowerSeriesOnBall f p x r) (y : E
) : HasFPowerSeriesOnBall (fun z => f (z - y)) p (x + y) r
参数：hf : HasFPowerSeriesOnBall f p x r；y : E。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Analysis.Analytic.Basic.0.HasFPowerSeriesOnBall.comp_su
b._abel_1_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] {x : E} (y : E) {z :
 E}, x + y + z - y = x + z
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …

--- 原说明 ---
If a function `f` has a power series `p` around `x`, then the function `z ↦ f (z
 - y)` has the
same power series around `x + y`.
-/
theorem HasFPowerSeriesOnBall.comp_sub (hf : HasFPowerSeriesOnBall f p x r) (y : E) :
    HasFPowerSeriesOnBall (fun z => f (z - y)) p (x + y) r :=
  { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {z} hz => by
      convert hf.hasSum hz
      abel }
/-
**HasFPowerSeriesWithinOnBall.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.comp_sub (hf : HasFPowerSeriesWithinOnBall f p
 s x r) (y : E) : HasFPowerSeriesWithinOnBall (fun z => f (z - y)) p (s + {y}) (
x + y) r where r_le
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；y : E。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `Mathlib.Tactic.Abel.subst_into_addg`：subst_into_addg {α} [AddCommGroup α
] (l r tl tr t) (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r 
= t
· 使用定理 `Mathlib.Tactic.Abel.term_atomg`：term_atomg {α} [AddCommGroup α] (x : α) 
: x = termg 1 x 0
· 使用定理 `Mathlib.Tactic.Abel.term_add_constg`：term_add_constg {α} [AddCommGroup α
] (n x a k a') (h : a + k = a') : @termg α _ n x a + k = termg n x a'
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `Mathlib.Tactic.Abel.subst_into_negg`：subst_into_negg {α} [AddCommGroup α
] (a ta t : α) (pra : a = ta) (prt : -ta = t) : -a = t
· 使用定理 `Mathlib.Tactic.Abel.term_neg`：term_neg {α} [AddCommGroup α] (n x a n' a'
) (h₁ : -n = n') (h₂ : -a = a') : -@termg α _ n x a = termg n' x a'
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Mathlib.Tactic.Abel.term_add_termg`：term_add_termg {α} [AddCommGroup α] 
(n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') : @termg α _ n₁ x 
a₁ + @termg α _ n₂ x a₂ …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Abel.zero_termg`：zero_termg {α} [AddCommGroup α] (x a) : 
@termg α _ 0 x a = a
· 使用定理 `Mathlib.Tactic.Abel.termg_eq`：termg_eq {α : Type*} [AddCommGroup α] (n :
 Int) (x a : α) : termg n x a = n • x + a
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `Set.add_singleton`：∀ {α : Type u_2} [inst : Add α] {s : Set α} {b : α}, 
s + {b} = (fun x => x + b) '' s
· 使用定理 `Set.image_add_right`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {b
 : α}, (fun x => x + b) '' t = (fun x => x + -b) ⁻¹' t
（共 35 条，此处仅展示前 30 条）
-/
theorem HasFPowerSeriesWithinOnBall.comp_sub (hf : HasFPowerSeriesWithinOnBall f p s x r) (y : E) :
    HasFPowerSeriesWithinOnBall (fun z ↦ f (z - y)) p (s + {y}) (x + y) r where
  r_le := hf.r_le
  r_pos := hf.r_pos
  hasSum {z} hz1 hz2 := by
    have : x + z ∈ insert x s := by
      simp only [add_singleton, image_add_right, mem_insert_iff, add_eq_left, mem_preimage] at hz1 ⊢
      abel_nf at hz1
      assumption
    convert hf.hasSum this hz2
    abel
/-
**HasFPowerSeriesAt.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.comp_sub (hf : HasFPowerSeriesAt f p x) (y : E) : HasFPo
werSeriesAt (fun z => f (z - y)) p (x + y)
参数：hf : HasFPowerSeriesAt f p x；y : E。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesOnBall.comp_sub`：HasFPowerSeriesOnBall.comp_sub (hf : Has
FPowerSeriesOnBall f p x r) (y : E) : HasFPowerSeriesOnBall (fun z => f (z - y))
 p (x + y) r
-/
theorem HasFPowerSeriesAt.comp_sub (hf : HasFPowerSeriesAt f p x) (y : E) :
    HasFPowerSeriesAt (fun z ↦ f (z - y)) p (x + y) := by
  obtain ⟨r, hf⟩ := hf
  exact ⟨r, hf.comp_sub _⟩
/-
**HasFPowerSeriesWithinAt.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.comp_sub (hf : HasFPowerSeriesWithinAt f p s x) (y
 : E) : HasFPowerSeriesWithinAt (fun z => f (z - y)) p (s + {y}) (x + y)
参数：hf : HasFPowerSeriesWithinAt f p s x；y : E。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.comp_sub`：HasFPowerSeriesWithinOnBall.comp_s
ub (hf : HasFPowerSeriesWithinOnBall f p s x r) (y : E) : HasFPowerSeriesWithinO
nBall (fun z => f (z - y))…
-/
theorem HasFPowerSeriesWithinAt.comp_sub (hf : HasFPowerSeriesWithinAt f p s x) (y : E) :
    HasFPowerSeriesWithinAt (fun z ↦ f (z - y)) p (s + {y}) (x + y) := by
  obtain ⟨r, hf⟩ := hf
  exact ⟨r, hf.comp_sub _⟩
/-
**AnalyticAt.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.comp_sub (hf : AnalyticAt 𝕜 f x) (y : E) : AnalyticAt 𝕜 (fun z 
=> f (z - y)) (x + y)
参数：hf : AnalyticAt 𝕜 f x；y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesAt.comp_sub`：HasFPowerSeriesAt.comp_sub (hf : HasFPowerSe
riesAt f p x) (y : E) : HasFPowerSeriesAt (fun z => f (z - y)) p (x + y)
-/
theorem AnalyticAt.comp_sub (hf : AnalyticAt 𝕜 f x) (y : E) :
    AnalyticAt 𝕜 (fun z ↦ f (z - y)) (x + y) := by
  obtain ⟨p, hf⟩ := hf
  exact ⟨p, hf.comp_sub _⟩
/-
**AnalyticOnNhd.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.comp_sub (hf : AnalyticOnNhd 𝕜 f s) (y : E) : AnalyticOnNhd 
𝕜 (fun z => f (z - y)) (s + {y})
参数：hf : AnalyticOnNhd 𝕜 f s；y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.Analytic.Basic.0.AnalyticOnNhd.comp_sub._abel_
1_2`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] (y x : E), x = x - y + y
· 使用定理 `AnalyticAt.comp_sub`：AnalyticAt.comp_sub (hf : AnalyticAt 𝕜 f x) (y : E)
 : AnalyticAt 𝕜 (fun z => f (z - y)) (x + y)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Analysis.Analytic.Basic.0.AnalyticOnNhd.comp_sub._abel_
1_3`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] (y x : E), x - y = x + -y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.add_singleton`：∀ {α : Type u_2} [inst : Add α] {s : Set α} {b : α}, 
s + {b} = (fun x => x + b) '' s
· 使用定理 `Set.image_add_right`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {b
 : α}, (fun x => x + b) '' t = (fun x => x + -b) ⁻¹' t
-/
theorem AnalyticOnNhd.comp_sub (hf : AnalyticOnNhd 𝕜 f s) (y : E) :
    AnalyticOnNhd 𝕜 (fun z ↦ f (z - y)) (s + {y}) := by
  intro x hx
  simp only [add_singleton, image_add_right, mem_preimage] at hx
  rw [show x = (x - y) + y by abel]
  apply (hf (x - y) (by convert hx; abel)).comp_sub
/-
**AnalyticWithinAt.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.comp_sub (hf : AnalyticWithinAt 𝕜 f s x) (y : E) : Analyt
icWithinAt 𝕜 (fun z => f (z - y)) (s + {y}) (x + y)
参数：hf : AnalyticWithinAt 𝕜 f s x；y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesWithinAt.comp_sub`：HasFPowerSeriesWithinAt.comp_sub (hf :
 HasFPowerSeriesWithinAt f p s x) (y : E) : HasFPowerSeriesWithinAt (fun z => f 
(z - y)) p (s + {y}) (…
-/
theorem AnalyticWithinAt.comp_sub (hf : AnalyticWithinAt 𝕜 f s x) (y : E) :
    AnalyticWithinAt 𝕜 (fun z ↦ f (z - y)) (s + {y}) (x + y) := by
  obtain ⟨p, hf⟩ := hf
  exact ⟨p, hf.comp_sub _⟩
/-
**AnalyticOn.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.comp_sub (hf : AnalyticOn 𝕜 f s) (y : E) : AnalyticOn 𝕜 (fun z 
=> f (z - y)) (s + {y})
参数：hf : AnalyticOn 𝕜 f s；y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.Analytic.Basic.0.AnalyticOn.comp_sub._abel_1_2
`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] (y x : E), x = x - y + y
· 使用定理 `AnalyticWithinAt.comp_sub`：AnalyticWithinAt.comp_sub (hf : AnalyticWithi
nAt 𝕜 f s x) (y : E) : AnalyticWithinAt 𝕜 (fun z => f (z - y)) (s + {y}) (x + y)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Analysis.Analytic.Basic.0.AnalyticOn.comp_sub._abel_1_3
`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] (y x : E), x - y = x + -y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.add_singleton`：∀ {α : Type u_2} [inst : Add α] {s : Set α} {b : α}, 
s + {b} = (fun x => x + b) '' s
· 使用定理 `Set.image_add_right`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {b
 : α}, (fun x => x + b) '' t = (fun x => x + -b) ⁻¹' t
-/
theorem AnalyticOn.comp_sub (hf : AnalyticOn 𝕜 f s) (y : E) :
    AnalyticOn 𝕜 (fun z ↦ f (z - y)) (s + {y}) := by
  intro x hx
  simp only [add_singleton, image_add_right, mem_preimage] at hx
  rw [show x = (x - y) + y by abel]
  apply (hf (x - y) (by convert hx; abel)).comp_sub
/-
**HasFPowerSeriesWithinOnBall.hasSum_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.hasSum_sub (hf : HasFPowerSeriesWithinOnBall f
 p s x r) {y : E} (hy : y in (insert x s) inter Metric.eball x r) : HasSum (fun 
n : Nat => p n fun _ => y - x) (f y)
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；hy : y in (insert x s) inter Metri
c.eball x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem HasFPowerSeriesWithinOnBall.hasSum_sub (hf : HasFPowerSeriesWithinOnBall f p s x r) {y : E}
    (hy : y ∈ (insert x s) ∩ Metric.eball x r) :
    HasSum (fun n : ℕ => p n fun _ => y - x) (f y) := by
  have : y - x ∈ Metric.eball 0 r := by simpa [edist_eq_enorm_sub] using hy.2
  simpa only [add_sub_cancel] using hf.hasSum (by simpa only [add_sub_cancel] using hy.1) this
/-
**HasFPowerSeriesOnBall.hasSum_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.hasSum_sub (hf : HasFPowerSeriesOnBall f p x r) {y :
 E} (hy : y in Metric.eball x r) : HasSum (fun n : Nat => p n fun _ => y - x) (f
 y)
参数：hf : HasFPowerSeriesOnBall f p x r；hy : y in Metric.eball x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesOnBall.hasSum_sub (hf : HasFPowerSeriesOnBall f p x r) {y : E}
    (hy : y ∈ Metric.eball x r) : HasSum (fun n : ℕ => p n fun _ => y - x) (f y) := by
  have : y - x ∈ Metric.eball 0 r := by simpa [edist_eq_enorm_sub] using hy
  simpa only [add_sub_cancel] using hf.hasSum this
/-
**HasFPowerSeriesOnBall.radius_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.radius_pos (hf : HasFPowerSeriesOnBall f p x r) : 0 
< p.radius
参数：hf : HasFPowerSeriesOnBall f p x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesOnBall.radius_pos (hf : HasFPowerSeriesOnBall f p x r) : 0 < p.radius :=
  lt_of_lt_of_le hf.r_pos hf.r_le
/-
**HasFPowerSeriesWithinOnBall.radius_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.radius_pos (hf : HasFPowerSeriesWithinOnBall f
 p s x r) : 0 < p.radius
参数：hf : HasFPowerSeriesWithinOnBall f p s x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesWithinOnBall.radius_pos (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    0 < p.radius :=
  lt_of_lt_of_le hf.r_pos hf.r_le
/-
**HasFPowerSeriesAt.radius_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.radius_pos (hf : HasFPowerSeriesAt f p x) : 0 < p.radius
参数：hf : HasFPowerSeriesAt f p x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesOnBall.radius_pos`：HasFPowerSeriesOnBall.radius_pos (hf :
 HasFPowerSeriesOnBall f p x r) : 0 < p.radius
-/
theorem HasFPowerSeriesAt.radius_pos (hf : HasFPowerSeriesAt f p x) : 0 < p.radius :=
  let ⟨_, hr⟩ := hf
  hr.radius_pos
/-
**HasFPowerSeriesWithinOnBall.of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.of_le (hf : HasFPowerSeriesWithinOnBall f p s 
x r) (r'_pos : 0 < r') (hr : r' <= r) : HasFPowerSeriesWithinOnBall f p s x r'
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；r'_pos : 0 < r'；hr : r' <= r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `Metric.eball_subset_eball`：eball_subset_eball (h : ε₁ <= ε₂) : eball x ε
₁ subseteq eball x ε₂
-/
theorem HasFPowerSeriesWithinOnBall.of_le
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (r'_pos : 0 < r') (hr : r' ≤ r) :
    HasFPowerSeriesWithinOnBall f p s x r' :=
  ⟨le_trans hr hf.1, r'_pos, fun hy h'y => hf.hasSum hy (Metric.eball_subset_eball hr h'y)⟩
/-
**HasFPowerSeriesOnBall.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.mono (hf : HasFPowerSeriesOnBall f p x r) (r'_pos : 
0 < r') (hr : r' <= r) : HasFPowerSeriesOnBall f p x r'
参数：hf : HasFPowerSeriesOnBall f p x r；r'_pos : 0 < r'；hr : r' <= r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
· 使用定理 `Metric.eball_subset_eball`：eball_subset_eball (h : ε₁ <= ε₂) : eball x ε
₁ subseteq eball x ε₂
-/
theorem HasFPowerSeriesOnBall.mono (hf : HasFPowerSeriesOnBall f p x r) (r'_pos : 0 < r')
    (hr : r' ≤ r) : HasFPowerSeriesOnBall f p x r' :=
  ⟨le_trans hr hf.1, r'_pos, fun hy => hf.hasSum (Metric.eball_subset_eball hr hy)⟩
/-
**HasFPowerSeriesWithinOnBall.congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.congr {f g : E -> F} {p : FormalMultilinearSer
ies 𝕜 E F} {s : Set E} {x : E} {r : Real>=0∞} (h : HasFPowerSeriesWithinOnBall f
 p s x r) (h' : EqOn g f (s inter Metric.eball x r)) (h'' : g x = f x) : HasFPow
erSeriesWithinOnBall g p s x r
参数：h : HasFPowerSeriesWithinOnBall f p s x r；h' : EqOn g f (s inter Metric.eball
 x r)；h'' : g x = f x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
-/
lemma HasFPowerSeriesWithinOnBall.congr {f g : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {s : Set E} {x : E} {r : ℝ≥0∞} (h : HasFPowerSeriesWithinOnBall f p s x r)
    (h' : EqOn g f (s ∩ Metric.eball x r)) (h'' : g x = f x) :
    HasFPowerSeriesWithinOnBall g p s x r := by
  refine ⟨h.r_le, h.r_pos, ?_⟩
  intro y hy h'y
  convert h.hasSum hy h'y
  simp only [mem_insert_iff, add_eq_left] at hy
  rcases hy with rfl | hy
  · simpa using h''
  · apply h'
    refine ⟨hy, ?_⟩
    simpa [edist_eq_enorm_sub] using h'y

/-- Variant of `HasFPowerSeriesWithinOnBall.congr` in which one requests equality on `insert x s`
instead of separating `x` and `s`. -/
/-
**HasFPowerSeriesWithinOnBall.congr'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.congr' {f g : E -> F} {p : FormalMultilinearSe
ries 𝕜 E F} {s : Set E} {x : E} {r : Real>=0∞} (h : HasFPowerSeriesWithinOnBall 
f p s x r) (h' : EqOn g f (insert x s inter Metric.eball x r)) : HasFPowerSeries
WithinOnBall g p s x r
参数：h : HasFPowerSeriesWithinOnBall f p s x r；h' : EqOn g f (insert x s inter Met
ric.eball x r)。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …

--- 原说明 ---
Variant of `HasFPowerSeriesWithinOnBall.congr` in which one requests equality on
 `insert x s`
instead of separating `x` and `s`.
-/
lemma HasFPowerSeriesWithinOnBall.congr' {f g : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {s : Set E} {x : E} {r : ℝ≥0∞} (h : HasFPowerSeriesWithinOnBall f p s x r)
    (h' : EqOn g f (insert x s ∩ Metric.eball x r)) :
    HasFPowerSeriesWithinOnBall g p s x r := by
  refine ⟨h.r_le, h.r_pos, fun {y} hy h'y ↦ ?_⟩
  convert h.hasSum hy h'y
  exact h' ⟨hy, by simpa [edist_eq_enorm_sub] using h'y⟩
/-
**HasFPowerSeriesWithinAt.congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.congr {f g : E -> F} {p : FormalMultilinearSeries 
𝕜 E F} {s : Set E} {x : E} (h : HasFPowerSeriesWithinAt f p s x) (h' : g =ᶠ[𝓝[s]
 x] f) (h'' : g x = f x) : HasFPowerSeriesWithinAt g p s x
参数：h : HasFPowerSeriesWithinAt f p s x；h' : g =ᶠ[𝓝[s] x] f；h'' : g x = f x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `EMetric.mem_nhdsWithin_iff`：mem_nhdsWithin_iff : s in 𝓝[t] x ↔ exists ε 
> 0, eball x ε inter t subseteq s
· 使用定理 `HasFPowerSeriesWithinOnBall.of_le`：HasFPowerSeriesWithinOnBall.of_le (hf
 : HasFPowerSeriesWithinOnBall f p s x r) (r'_pos : 0 < r') (hr : r' <= r) : Has
FPowerSeriesWithinOnBal…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `HasFPowerSeriesWithinOnBall.congr`：HasFPowerSeriesWithinOnBall.congr {f 
g : E -> F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : Real>=0
∞} (h : HasFPowerSeries…
· 使用定理 `Metric.eball_subset_eball`：eball_subset_eball (h : ε₁ <= ε₂) : eball x ε
₁ subseteq eball x ε₂
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma HasFPowerSeriesWithinAt.congr {f g : E → F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E}
    {x : E} (h : HasFPowerSeriesWithinAt f p s x) (h' : g =ᶠ[𝓝[s] x] f) (h'' : g x = f x) :
    HasFPowerSeriesWithinAt g p s x := by
  rcases h with ⟨r, hr⟩
  obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, Metric.eball x ε ∩ s ⊆ {y | g y = f y} :=
    EMetric.mem_nhdsWithin_iff.1 h'
  let r' := min r ε
  refine ⟨r', ?_⟩
  have := hr.of_le (r' := r') (by simp [r', εpos, hr.r_pos]) (min_le_left _ _)
  apply this.congr _ h''
  intro z hz
  exact hε ⟨Metric.eball_subset_eball (min_le_right _ _) hz.2, hz.1⟩
/-
**HasFPowerSeriesOnBall.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.congr (hf : HasFPowerSeriesOnBall f p x r) (hg : EqO
n f g (Metric.eball x r)) : HasFPowerSeriesOnBall g p x r
参数：hf : HasFPowerSeriesOnBall f p x r；hg : EqOn f g (Metric.eball x r)。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesOnBall.congr (hf : HasFPowerSeriesOnBall f p x r)
    (hg : EqOn f g (Metric.eball x r)) : HasFPowerSeriesOnBall g p x r :=
  { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {y} hy => by
      convert hf.hasSum hy
      apply hg.symm
      simpa [edist_eq_enorm_sub] using hy }
/-
**HasFPowerSeriesAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.congr (hf : HasFPowerSeriesAt f p x) (hg : f =ᶠ[𝓝 x] g) 
: HasFPowerSeriesAt g p x
参数：hf : HasFPowerSeriesAt f p x；hg : f =ᶠ[𝓝 x] g。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `EMetric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, eball x ε 
subseteq s
· 使用定理 `HasFPowerSeriesOnBall.congr`：HasFPowerSeriesOnBall.congr (hf : HasFPower
SeriesOnBall f p x r) (hg : EqOn f g (Metric.eball x r)) : HasFPowerSeriesOnBall
 g p x r
· 使用定理 `HasFPowerSeriesOnBall.mono`：HasFPowerSeriesOnBall.mono (hf : HasFPowerSe
riesOnBall f p x r) (r'_pos : 0 < r') (hr : r' <= r) : HasFPowerSeriesOnBall f p
 x r'
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Metric.eball_subset_eball`：eball_subset_eball (h : ε₁ <= ε₂) : eball x ε
₁ subseteq eball x ε₂
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem HasFPowerSeriesAt.congr (hf : HasFPowerSeriesAt f p x) (hg : f =ᶠ[𝓝 x] g) :
    HasFPowerSeriesAt g p x := by
  rcases hf with ⟨r₁, h₁⟩
  rcases EMetric.mem_nhds_iff.mp hg with ⟨r₂, h₂pos, h₂⟩
  exact ⟨min r₁ r₂,
    (h₁.mono (lt_min h₁.r_pos h₂pos) inf_le_left).congr
      fun y hy => h₂ (Metric.eball_subset_eball inf_le_right hy)⟩
/-
**HasFPowerSeriesWithinOnBall.unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.unique (hf : HasFPowerSeriesWithinOnBall f p s
 x r) (hg : HasFPowerSeriesWithinOnBall g p s x r) : (insert x s inter Metric.eb
all x r).EqOn f g
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；hg : HasFPowerSeriesWithinOnBall g
 p s x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum_sub`：HasFPowerSeriesWithinOnBall.hasS
um_sub (hf : HasFPowerSeriesWithinOnBall f p s x r) {y : E} (hy : y in (insert x
 s) inter Metric.eball x r) …
-/
theorem HasFPowerSeriesWithinOnBall.unique (hf : HasFPowerSeriesWithinOnBall f p s x r)
    (hg : HasFPowerSeriesWithinOnBall g p s x r) :
    (insert x s ∩ Metric.eball x r).EqOn f g := fun _ hy ↦
  (hf.hasSum_sub hy).unique (hg.hasSum_sub hy)
/-
**HasFPowerSeriesOnBall.unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.unique (hf : HasFPowerSeriesOnBall f p x r) (hg : Ha
sFPowerSeriesOnBall g p x r) : (Metric.eball x r).EqOn f g
参数：hf : HasFPowerSeriesOnBall f p x r；hg : HasFPowerSeriesOnBall g p x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasFPowerSeriesOnBall.hasSum_sub`：HasFPowerSeriesOnBall.hasSum_sub (hf :
 HasFPowerSeriesOnBall f p x r) {y : E} (hy : y in Metric.eball x r) : HasSum (f
un n : Nat => p n fun …
-/
theorem HasFPowerSeriesOnBall.unique (hf : HasFPowerSeriesOnBall f p x r)
    (hg : HasFPowerSeriesOnBall g p x r) : (Metric.eball x r).EqOn f g := fun _ hy ↦
  (hf.hasSum_sub hy).unique (hg.hasSum_sub hy)
/-
**HasFPowerSeriesWithinAt.eventually** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerSeriesW
ithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {s : Set E} {x : E},   HasFPowerSeriesWithinAt f p s x → ∀ᶠ (r
 : ENNReal) in nhdsWithin 0 (Set.Ioi 0), HasFPowerSeriesWithinOnBall f p s x r
参数：r : ENNReal；Set.Ioi 0。
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
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioo_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioo b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.of_le`：HasFPowerSeriesWithinOnBall.of_le (hf
 : HasFPowerSeriesWithinOnBall f p s x r) (r'_pos : 0 < r') (hr : r' <= r) : Has
FPowerSeriesWithinOnBal…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem HasFPowerSeriesWithinAt.eventually (hf : HasFPowerSeriesWithinAt f p s x) :
    ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0, HasFPowerSeriesWithinOnBall f p s x r :=
  let ⟨_, hr⟩ := hf
  mem_of_superset (Ioo_mem_nhdsGT hr.r_pos) fun _ hr' => hr.of_le hr'.1 hr'.2.le
/-
**HasFPowerSeriesAt.eventually** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerSeriesAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {x : E},   HasFPowerSeriesAt f p x → ∀ᶠ (r : ENNReal) in nhdsW
ithin 0 (Set.Ioi 0), HasFPowerSeriesOnBall f p x r
参数：r : ENNReal；Set.Ioi 0。
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
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioo_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioo b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.mono`：HasFPowerSeriesOnBall.mono (hf : HasFPowerSe
riesOnBall f p x r) (r'_pos : 0 < r') (hr : r' <= r) : HasFPowerSeriesOnBall f p
 x r'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem HasFPowerSeriesAt.eventually (hf : HasFPowerSeriesAt f p x) :
    ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0, HasFPowerSeriesOnBall f p x r :=
  let ⟨_, hr⟩ := hf
  mem_of_superset (Ioo_mem_nhdsGT hr.r_pos) fun _ hr' => hr.mono hr'.1 hr'.2.le
/-
**HasFPowerSeriesOnBall.eventually_hasSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.eventually_hasSum (hf : HasFPowerSeriesOnBall f p x 
r) : forallᶠ y in 𝓝 0, HasSum (fun n : Nat => p n fun _ : Fin n => y) (f (x + y)
)
参数：hf : HasFPowerSeriesOnBall f p x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesOnBall.eventually_hasSum (hf : HasFPowerSeriesOnBall f p x r) :
    ∀ᶠ y in 𝓝 0, HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y)) := by
  filter_upwards [Metric.eball_mem_nhds (0 : E) hf.r_pos] using fun _ => hf.hasSum
/-
**HasFPowerSeriesAt.eventually_hasSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.eventually_hasSum (hf : HasFPowerSeriesAt f p x) : foral
lᶠ y in 𝓝 0, HasSum (fun n : Nat => p n fun _ : Fin n => y) (f (x + y))
参数：hf : HasFPowerSeriesAt f p x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesOnBall.eventually_hasSum`：HasFPowerSeriesOnBall.eventuall
y_hasSum (hf : HasFPowerSeriesOnBall f p x r) : forallᶠ y in 𝓝 0, HasSum (fun n 
: Nat => p n fun _ : Fin n =>…
-/
theorem HasFPowerSeriesAt.eventually_hasSum (hf : HasFPowerSeriesAt f p x) :
    ∀ᶠ y in 𝓝 0, HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y)) :=
  let ⟨_, hr⟩ := hf
  hr.eventually_hasSum
/-
**HasFPowerSeriesOnBall.eventually_hasSum_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.eventually_hasSum_sub (hf : HasFPowerSeriesOnBall f 
p x r) : forallᶠ y in 𝓝 x, HasSum (fun n : Nat => p n fun _ : Fin n => y - x) (f
 y)
参数：hf : HasFPowerSeriesOnBall f p x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `HasFPowerSeriesOnBall.hasSum_sub`：HasFPowerSeriesOnBall.hasSum_sub (hf :
 HasFPowerSeriesOnBall f p x r) {y : E} (hy : y in Metric.eball x r) : HasSum (f
un n : Nat => p n fun …
-/
theorem HasFPowerSeriesOnBall.eventually_hasSum_sub (hf : HasFPowerSeriesOnBall f p x r) :
    ∀ᶠ y in 𝓝 x, HasSum (fun n : ℕ => p n fun _ : Fin n => y - x) (f y) := by
  filter_upwards [Metric.eball_mem_nhds x hf.r_pos] with y using hf.hasSum_sub
/-
**HasFPowerSeriesAt.eventually_hasSum_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.eventually_hasSum_sub (hf : HasFPowerSeriesAt f p x) : f
orallᶠ y in 𝓝 x, HasSum (fun n : Nat => p n fun _ : Fin n => y - x) (f y)
参数：hf : HasFPowerSeriesAt f p x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesOnBall.eventually_hasSum_sub`：HasFPowerSeriesOnBall.event
ually_hasSum_sub (hf : HasFPowerSeriesOnBall f p x r) : forallᶠ y in 𝓝 x, HasSum
 (fun n : Nat => p n fun _ : Fin …
-/
theorem HasFPowerSeriesAt.eventually_hasSum_sub (hf : HasFPowerSeriesAt f p x) :
    ∀ᶠ y in 𝓝 x, HasSum (fun n : ℕ => p n fun _ : Fin n => y - x) (f y) :=
  let ⟨_, hr⟩ := hf
  hr.eventually_hasSum_sub
/-
**HasFPowerSeriesOnBall.eventually_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.eventually_eq_zero (hf : HasFPowerSeriesOnBall f (0 
: FormalMultilinearSeries 𝕜 E F) x r) : forallᶠ z in 𝓝 x, f z = 0
参数：hf : HasFPowerSeriesOnBall f (0 : FormalMultilinearSeries 𝕜 E F) x r。
该定理/引理给出了一组等式。
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
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `HasFPowerSeriesOnBall.eventually_hasSum_sub`：HasFPowerSeriesOnBall.event
ually_hasSum_sub (hf : HasFPowerSeriesOnBall f p x r) : forallᶠ y in 𝓝 x, HasSum
 (fun n : Nat => p n fun _ : Fin …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasSum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] {L : SummationFilter β},   HasSum (fun x => 0) 0 L
-/
theorem HasFPowerSeriesOnBall.eventually_eq_zero
    (hf : HasFPowerSeriesOnBall f (0 : FormalMultilinearSeries 𝕜 E F) x r) :
    ∀ᶠ z in 𝓝 x, f z = 0 := by
  filter_upwards [hf.eventually_hasSum_sub] with z hz using hz.unique hasSum_zero
/-
**HasFPowerSeriesAt.eventually_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.eventually_eq_zero (hf : HasFPowerSeriesAt f (0 : Formal
MultilinearSeries 𝕜 E F) x) : forallᶠ z in 𝓝 x, f z = 0
参数：hf : HasFPowerSeriesAt f (0 : FormalMultilinearSeries 𝕜 E F) x。
该定理/引理给出了一组等式。
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
· 使用定理 `HasFPowerSeriesOnBall.eventually_eq_zero`：HasFPowerSeriesOnBall.eventual
ly_eq_zero (hf : HasFPowerSeriesOnBall f (0 : FormalMultilinearSeries 𝕜 E F) x r
) : forallᶠ z in 𝓝 x, f z = 0
-/
theorem HasFPowerSeriesAt.eventually_eq_zero
    (hf : HasFPowerSeriesAt f (0 : FormalMultilinearSeries 𝕜 E F) x) : ∀ᶠ z in 𝓝 x, f z = 0 :=
  let ⟨_, hr⟩ := hf
  hr.eventually_eq_zero
/-
**hasFPowerSeriesWithinOnBall_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {x : E} {r : ENNReal},   HasFPowerSeriesWithinOnBall f p Set.u
niv x r ↔ HasFPowerSeriesOnBall f p x r
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
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
-/
@[simp] lemma hasFPowerSeriesWithinOnBall_univ :
    HasFPowerSeriesWithinOnBall f p univ x r ↔ HasFPowerSeriesOnBall f p x r := by
  constructor
  · intro h
    refine ⟨h.r_le, h.r_pos, fun {y} m ↦ h.hasSum (by simp) m⟩
  · intro h
    exact ⟨h.r_le, h.r_pos, fun {y} _ m => h.hasSum m⟩
/-
**hasFPowerSeriesWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {x : E}, HasFPowerSeriesWithinAt f p Set.univ x ↔ HasFPowerSer
iesAt f p x
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma hasFPowerSeriesWithinAt_univ :
    HasFPowerSeriesWithinAt f p univ x ↔ HasFPowerSeriesAt f p x := by
  simp only [HasFPowerSeriesWithinAt, hasFPowerSeriesWithinOnBall_univ, HasFPowerSeriesAt]
/-
**HasFPowerSeriesWithinOnBall.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.mono (hf : HasFPowerSeriesWithinOnBall f p s x
 r) (h : t subseteq s) : HasFPowerSeriesWithinOnBall f p t x r where r_le
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；h : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
-/
lemma HasFPowerSeriesWithinOnBall.mono (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : t ⊆ s) :
    HasFPowerSeriesWithinOnBall f p t x r where
  r_le := hf.r_le
  r_pos := hf.r_pos
  hasSum hy h'y := hf.hasSum (insert_subset_insert h hy) h'y
/-
**HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall (hf : HasFPowerSeriesOnB
all f p x r) : HasFPowerSeriesWithinOnBall f p s x r
参数：hf : HasFPowerSeriesOnBall f p x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用引理 `HasFPowerSeriesWithinOnBall.mono`：HasFPowerSeriesWithinOnBall.mono (hf :
 HasFPowerSeriesWithinOnBall f p s x r) (h : t subseteq s) : HasFPowerSeriesWith
inOnBall f p t x r whe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall (hf : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesWithinOnBall f p s x r := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  exact hf.mono (subset_univ _)
/-
**HasFPowerSeriesWithinAt.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.mono (hf : HasFPowerSeriesWithinAt f p s x) (h : t
 subseteq s) : HasFPowerSeriesWithinAt f p t x
参数：hf : HasFPowerSeriesWithinAt f p s x；h : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
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
· 使用引理 `HasFPowerSeriesWithinOnBall.mono`：HasFPowerSeriesWithinOnBall.mono (hf :
 HasFPowerSeriesWithinOnBall f p s x r) (h : t subseteq s) : HasFPowerSeriesWith
inOnBall f p t x r whe…
-/
lemma HasFPowerSeriesWithinAt.mono (hf : HasFPowerSeriesWithinAt f p s x) (h : t ⊆ s) :
    HasFPowerSeriesWithinAt f p t x := by
  obtain ⟨r, hp⟩ := hf
  exact ⟨r, hp.mono h⟩
/-
**HasFPowerSeriesAt.hasFPowerSeriesWithinAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.hasFPowerSeriesWithinAt (hf : HasFPowerSeriesAt f p x) :
 HasFPowerSeriesWithinAt f p s x
参数：hf : HasFPowerSeriesAt f p x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用引理 `HasFPowerSeriesWithinAt.mono`：HasFPowerSeriesWithinAt.mono (hf : HasFPow
erSeriesWithinAt f p s x) (h : t subseteq s) : HasFPowerSeriesWithinAt f p t x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma HasFPowerSeriesAt.hasFPowerSeriesWithinAt (hf : HasFPowerSeriesAt f p x) :
    HasFPowerSeriesWithinAt f p s x := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  apply hf.mono (subset_univ _)
/-
**HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin (h : HasFPowerSeriesWithinA
t f p s x) (hst : s in 𝓝[t] x) : HasFPowerSeriesWithinAt f p t x
参数：h : HasFPowerSeriesWithinAt f p s x；hst : s in 𝓝[t] x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `EMetric.mem_nhdsWithin_iff`：mem_nhdsWithin_iff : s in 𝓝[t] x ↔ exists ε 
> 0, eball x ε inter t subseteq s
· 使用定理 `HasFPowerSeriesWithinOnBall.of_le`：HasFPowerSeriesWithinOnBall.of_le (hf
 : HasFPowerSeriesWithinOnBall f p s x r) (r'_pos : 0 < r') (hr : r' <= r) : Has
FPowerSeriesWithinOnBal…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin
    (h : HasFPowerSeriesWithinAt f p s x) (hst : s ∈ 𝓝[t] x) :
    HasFPowerSeriesWithinAt f p t x := by
  rcases h with ⟨r, hr⟩
  rcases EMetric.mem_nhdsWithin_iff.1 hst with ⟨r', r'_pos, hr'⟩
  refine ⟨min r r', ?_⟩
  have Z := hr.of_le (by simp [r'_pos, hr.r_pos]) (min_le_left r r')
  refine ⟨Z.r_le, Z.r_pos, fun {y} hy h'y ↦ ?_⟩
  apply Z.hasSum ?_ h'y
  simp only [mem_insert_iff, add_eq_left] at hy
  rcases hy with rfl | hy
  · simp
  apply mem_insert_of_mem _ (hr' ?_)
  simp only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, lt_min_iff, mem_inter_iff,
    add_sub_cancel_left, hy, and_true] at h'y ⊢
  exact h'y.2
/-
**hasFPowerSeriesWithinAt_iff_of_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesWithinAt_iff_of_nhds (f : E -> F) (p : FormalMultilinearSer
ies 𝕜 E F) {U : Set E} (hU : U in 𝓝 x) : HasFPowerSeriesWithinAt f p U x ↔ HasFP
owerSeriesAt f p x
参数：f : E -> F；p : FormalMultilinearSeries 𝕜 E F；hU : U in 𝓝 x。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin`：HasFPowerSeriesWithinAt.
mono_of_mem_nhdsWithin (h : HasFPowerSeriesWithinAt f p s x) (hst : s in 𝓝[t] x)
 : HasFPowerSeriesWithinAt f p t x
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用引理 `HasFPowerSeriesWithinAt.mono`：HasFPowerSeriesWithinAt.mono (hf : HasFPow
erSeriesWithinAt f p s x) (h : t subseteq s) : HasFPowerSeriesWithinAt f p t x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma hasFPowerSeriesWithinAt_iff_of_nhds (f : E → F) (p : FormalMultilinearSeries 𝕜 E F)
    {U : Set E} (hU : U ∈ 𝓝 x) :
    HasFPowerSeriesWithinAt f p U x ↔ HasFPowerSeriesAt f p x := by
  rw [← hasFPowerSeriesWithinAt_univ]
  exact ⟨fun h ↦ h.mono_of_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hU),
    fun h ↦ h.mono (subset_univ _)⟩
/-
**hasFPowerSeriesWithinOnBall_insert_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {s : Set E} {x : E} {r : ENNReal},   HasFPowerSeriesWithinOnBa
ll f p (insert x s) x r ↔ HasFPowerSeriesWithinOnBall f p s x r
参数：insert x s。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_idem`：insert_idem (a : α) (s : Set α) : insert a (insert a s)
 = insert a s
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
-/
@[simp] lemma hasFPowerSeriesWithinOnBall_insert_self :
    HasFPowerSeriesWithinOnBall f p (insert x s) x r ↔ HasFPowerSeriesWithinOnBall f p s x r := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩  <;>
  exact ⟨h.r_le, h.r_pos, fun {y} ↦ by simpa only [insert_idem] using h.hasSum (y := y)⟩
/-
**hasFPowerSeriesWithinAt_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {s : Set E} {x y : E},   HasFPowerSeriesWithinAt f p (insert y
 s) x ↔ HasFPowerSeriesWithinAt f p s x
参数：insert y s。
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
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `HasFPowerSeriesWithinAt.mono`：HasFPowerSeriesWithinAt.mono (hf : HasFPow
erSeriesWithinAt f p s x) (h : t subseteq s) : HasFPowerSeriesWithinAt f p t x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin`：HasFPowerSeriesWithinAt.
mono_of_mem_nhdsWithin (h : HasFPowerSeriesWithinAt f p s x) (hst : s in 𝓝[t] x)
 : HasFPowerSeriesWithinAt f p t x
· 使用定理 `nhdsWithin_insert_of_ne`：nhdsWithin_insert_of_ne [T1Space X] {x y : X} {
s : Set X} (hxy : x != y) : 𝓝[insert y s] x = 𝓝[s] x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
@[simp] theorem hasFPowerSeriesWithinAt_insert {y : E} :
    HasFPowerSeriesWithinAt f p (insert y s) x ↔ HasFPowerSeriesWithinAt f p s x := by
  rcases eq_or_ne x y with rfl | hy
  · simp [HasFPowerSeriesWithinAt]
  · refine ⟨fun h ↦ h.mono (subset_insert _ _), fun h ↦ ?_⟩
    apply HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin h
    rw [nhdsWithin_insert_of_ne hy]
    exact self_mem_nhdsWithin
/-
**HasFPowerSeriesWithinOnBall.coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.coeff_zero (hf : HasFPowerSeriesWithinOnBall f
 pf s x r) (v : Fin 0 -> E) : pf 0 v = f x
参数：hf : HasFPowerSeriesWithinOnBall f pf s x r；v : Fin 0 -> E。
该定理/引理给出了一组等式。
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
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ContinuousMultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M
₁ i} (i : ι) (h : m i = 0) : f m = 0
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `hasSum_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {f : β → α} (b : β),   (∀ (b' : β), b' ≠ b → f b' 
= 0…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem HasFPowerSeriesWithinOnBall.coeff_zero (hf : HasFPowerSeriesWithinOnBall f pf s x r)
    (v : Fin 0 → E) : pf 0 v = f x := by
  have v_eq : v = fun i => 0 := Subsingleton.elim _ _
  have zero_mem : (0 : E) ∈ Metric.eball (0 : E) r := by simp [hf.r_pos]
  have : ∀ i, i ≠ 0 → (pf i fun _ => 0) = 0 := by
    intro i hi
    have : 0 < i := pos_iff_ne_zero.2 hi
    exact ContinuousMultilinearMap.map_coord_zero _ (⟨0, this⟩ : Fin i) rfl
  have A := (hf.hasSum (by simp) zero_mem).unique (hasSum_single _ this)
  simpa [v_eq] using A.symm
/-
**HasFPowerSeriesOnBall.coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.coeff_zero (hf : HasFPowerSeriesOnBall f pf x r) (v 
: Fin 0 -> E) : pf 0 v = f x
参数：hf : HasFPowerSeriesOnBall f pf x r；v : Fin 0 -> E。
该定理/引理给出了一组等式。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.coeff_zero`：HasFPowerSeriesWithinOnBall.coef
f_zero (hf : HasFPowerSeriesWithinOnBall f pf s x r) (v : Fin 0 -> E) : pf 0 v =
 f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesOnBall.coeff_zero (hf : HasFPowerSeriesOnBall f pf x r)
    (v : Fin 0 → E) : pf 0 v = f x := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  exact hf.coeff_zero v
/-
**HasFPowerSeriesWithinAt.coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.coeff_zero (hf : HasFPowerSeriesWithinAt f pf s x)
 (v : Fin 0 -> E) : pf 0 v = f x
参数：hf : HasFPowerSeriesWithinAt f pf s x；v : Fin 0 -> E。
该定理/引理给出了一组等式。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.coeff_zero`：HasFPowerSeriesWithinOnBall.coef
f_zero (hf : HasFPowerSeriesWithinOnBall f pf s x r) (v : Fin 0 -> E) : pf 0 v =
 f x
-/
theorem HasFPowerSeriesWithinAt.coeff_zero (hf : HasFPowerSeriesWithinAt f pf s x) (v : Fin 0 → E) :
    pf 0 v = f x :=
  let ⟨_, hrf⟩ := hf
  hrf.coeff_zero v
/-
**HasFPowerSeriesAt.coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.coeff_zero (hf : HasFPowerSeriesAt f pf x) (v : Fin 0 ->
 E) : pf 0 v = f x
参数：hf : HasFPowerSeriesAt f pf x；v : Fin 0 -> E。
该定理/引理给出了一组等式。
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
· 使用定理 `HasFPowerSeriesOnBall.coeff_zero`：HasFPowerSeriesOnBall.coeff_zero (hf :
 HasFPowerSeriesOnBall f pf x r) (v : Fin 0 -> E) : pf 0 v = f x
-/
theorem HasFPowerSeriesAt.coeff_zero (hf : HasFPowerSeriesAt f pf x) (v : Fin 0 → E) :
    pf 0 v = f x :=
  let ⟨_, hrf⟩ := hf
  hrf.coeff_zero v

/-!
### Analytic functions
-/

/-
**analyticOn_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}, AnalyticOn 𝕜 f ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
### Analytic functions
-/
@[simp] theorem analyticOn_empty : AnalyticOn 𝕜 f ∅ := by intro; simp
/-
**analyticOnNhd_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}, AnalyticOnNhd 𝕜 f ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
### Analytic functions
-/
@[simp] theorem analyticOnNhd_empty : AnalyticOnNhd 𝕜 f ∅ := by intro; simp
/-
**analyticWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {x : E},   AnalyticW
ithinAt 𝕜 f Set.univ x ↔ AnalyticAt 𝕜 f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Analytic functions
-/
@[simp] lemma analyticWithinAt_univ :
    AnalyticWithinAt 𝕜 f univ x ↔ AnalyticAt 𝕜 f x := by
  simp [AnalyticWithinAt, AnalyticAt]
/-
**analyticOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F},   AnalyticOn 𝕜 f Se
t.univ ↔ AnalyticOnNhd 𝕜 f Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma analyticOn_univ {f : E → F} :
    AnalyticOn 𝕜 f univ ↔ AnalyticOnNhd 𝕜 f univ := by
  simp only [AnalyticOn, analyticWithinAt_univ, AnalyticOnNhd]
/-
**AnalyticWithinAt.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.mono (hf : AnalyticWithinAt 𝕜 f s x) (h : t subseteq s) :
 AnalyticWithinAt 𝕜 f t x
参数：hf : AnalyticWithinAt 𝕜 f s x；h : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasFPowerSeriesWithinAt.mono`：HasFPowerSeriesWithinAt.mono (hf : HasFPow
erSeriesWithinAt f p s x) (h : t subseteq s) : HasFPowerSeriesWithinAt f p t x
-/
lemma AnalyticWithinAt.mono (hf : AnalyticWithinAt 𝕜 f s x) (h : t ⊆ s) :
    AnalyticWithinAt 𝕜 f t x := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, hp.mono h⟩
/-
**AnalyticAt.analyticWithinAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.analyticWithinAt (hf : AnalyticAt 𝕜 f x) : AnalyticWithinAt 𝕜 f
 s x
参数：hf : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticWithinAt.mono`：AnalyticWithinAt.mono (hf : AnalyticWithinAt 𝕜 f 
s x) (h : t subseteq s) : AnalyticWithinAt 𝕜 f t x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `analyticWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [i
nst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 …
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma AnalyticAt.analyticWithinAt (hf : AnalyticAt 𝕜 f x) : AnalyticWithinAt 𝕜 f s x := by
  rw [← analyticWithinAt_univ] at hf
  apply hf.mono (subset_univ _)
/-
**AnalyticOnNhd.analyticOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOn 𝕜 f s
参数：hf : AnalyticOnNhd 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
-/
lemma AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOn 𝕜 f s :=
  fun x hx ↦ (hf x hx).analyticWithinAt
/-
**AnalyticWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.congr_of_eventuallyEq {f g : E -> F} {s : Set E} {x : E} 
(hf : AnalyticWithinAt 𝕜 f s x) (hs : g =ᶠ[𝓝[s] x] f) (hx : g x = f x) : Analyti
cWithinAt 𝕜 g s x
参数：hf : AnalyticWithinAt 𝕜 f s x；hs : g =ᶠ[𝓝[s] x] f；hx : g x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasFPowerSeriesWithinAt.congr`：HasFPowerSeriesWithinAt.congr {f g : E ->
 F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} (h : HasFPowerSeries
WithinAt f p s x) (…
-/
lemma AnalyticWithinAt.congr_of_eventuallyEq {f g : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : g =ᶠ[𝓝[s] x] f) (hx : g x = f x) :
    AnalyticWithinAt 𝕜 g s x := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p, hp.congr hs hx⟩
/-
**AnalyticWithinAt.congr_of_eventuallyEq_insert** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.congr_of_eventuallyEq_insert {f g : E -> F} {s : Set E} {
x : E} (hf : AnalyticWithinAt 𝕜 f s x) (hs : g =ᶠ[𝓝[insert x s] x] f) : Analytic
WithinAt 𝕜 g s x
参数：hf : AnalyticWithinAt 𝕜 f s x；hs : g =ᶠ[𝓝[insert x s] x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticWithinAt.congr_of_eventuallyEq`：AnalyticWithinAt.congr_of_eventu
allyEq {f g : E -> F} {s : Set E} {x : E} (hf : AnalyticWithinAt 𝕜 f s x) (hs : 
g =ᶠ[𝓝[s] x] f) (hx : g x = …
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
lemma AnalyticWithinAt.congr_of_eventuallyEq_insert {f g : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : g =ᶠ[𝓝[insert x s] x] f) :
    AnalyticWithinAt 𝕜 g s x := by
  apply hf.congr_of_eventuallyEq (nhdsWithin_mono x (subset_insert x s) hs)
  apply mem_of_mem_nhdsWithin (mem_insert x s) hs
/-
**AnalyticWithinAt.congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.congr {f g : E -> F} {s : Set E} {x : E} (hf : AnalyticWi
thinAt 𝕜 f s x) (hs : EqOn g f s) (hx : g x = f x) : AnalyticWithinAt 𝕜 g s x
参数：hf : AnalyticWithinAt 𝕜 f s x；hs : EqOn g f s；hx : g x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticWithinAt.congr_of_eventuallyEq`：AnalyticWithinAt.congr_of_eventu
allyEq {f g : E -> F} {s : Set E} {x : E} (hf : AnalyticWithinAt 𝕜 f s x) (hs : 
g =ᶠ[𝓝[s] x] f) (hx : g x = …
· 使用定理 `Set.EqOn.eventuallyEq_nhdsWithin`：Set.EqOn.eventuallyEq_nhdsWithin {f g 
: α -> β} {s : Set α} {a : α} (h : EqOn f g s) : f =ᶠ[𝓝[s] a] g
-/
lemma AnalyticWithinAt.congr {f g : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : EqOn g f s) (hx : g x = f x) :
    AnalyticWithinAt 𝕜 g s x :=
  hf.congr_of_eventuallyEq hs.eventuallyEq_nhdsWithin hx
/-
**AnalyticOn.congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.congr {f g : E -> F} {s : Set E} (hf : AnalyticOn 𝕜 f s) (hs : 
EqOn g f s) : AnalyticOn 𝕜 g s
参数：hf : AnalyticOn 𝕜 f s；hs : EqOn g f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticWithinAt.congr`：AnalyticWithinAt.congr {f g : E -> F} {s : Set E
} {x : E} (hf : AnalyticWithinAt 𝕜 f s x) (hs : EqOn g f s) (hx : g x = f x) : A
nalyticWithi…
-/
lemma AnalyticOn.congr {f g : E → F} {s : Set E}
    (hf : AnalyticOn 𝕜 f s) (hs : EqOn g f s) :
    AnalyticOn 𝕜 g s :=
  fun x m ↦ (hf x m).congr hs (hs m)
/-
**analyticOn_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOn_congr (hs : EqOn f g s) : AnalyticOn 𝕜 f s ↔ AnalyticOn 𝕜 g s
参数：hs : EqOn f g s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOn.congr`：AnalyticOn.congr {f g : E -> F} {s : Set E} (hf : Anal
yticOn 𝕜 f s) (hs : EqOn g f s) : AnalyticOn 𝕜 g s
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
lemma analyticOn_congr (hs : EqOn f g s) : AnalyticOn 𝕜 f s ↔ AnalyticOn 𝕜 g s :=
  ⟨fun h ↦ h.congr hs.symm, fun h ↦ h.congr hs⟩
/-
**AnalyticAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜
 g x
参数：hf : AnalyticAt 𝕜 f x；hg : f =ᶠ[𝓝 x] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesAt.analyticAt`：HasFPowerSeriesAt.analyticAt (hf : HasFPow
erSeriesAt f p x) : AnalyticAt 𝕜 f x
· 使用定理 `HasFPowerSeriesAt.congr`：HasFPowerSeriesAt.congr (hf : HasFPowerSeriesAt
 f p x) (hg : f =ᶠ[𝓝 x] g) : HasFPowerSeriesAt g p x
-/
theorem AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 g x :=
  let ⟨_, hpf⟩ := hf
  (hpf.congr hg).analyticAt
/-
**analyticAt_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticAt_congr (h : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 f x ↔ AnalyticAt 𝕜 g x
参数：h : f =ᶠ[𝓝 x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.congr`：AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 
x] g) : AnalyticAt 𝕜 g x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem analyticAt_congr (h : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 f x ↔ AnalyticAt 𝕜 g x :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩
/-
**AnalyticOnNhd.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.mono {s t : Set E} (hf : AnalyticOnNhd 𝕜 f t) (hst : s subse
teq t) : AnalyticOnNhd 𝕜 f s
参数：hf : AnalyticOnNhd 𝕜 f t；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AnalyticOnNhd.mono {s t : Set E} (hf : AnalyticOnNhd 𝕜 f t) (hst : s ⊆ t) :
    AnalyticOnNhd 𝕜 f s :=
  fun z hz => hf z (hst hz)
/-
**AnalyticOnNhd.congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.congr' (hf : AnalyticOnNhd 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g) : Anal
yticOnNhd 𝕜 g s
参数：hf : AnalyticOnNhd 𝕜 f s；hg : f =ᶠ[𝓝ˢ s] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.congr`：AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 
x] g) : AnalyticAt 𝕜 g x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsSet_iff_forall`：mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : 
X, x in t -> s in 𝓝 x
-/
theorem AnalyticOnNhd.congr' (hf : AnalyticOnNhd 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g) :
    AnalyticOnNhd 𝕜 g s :=
  fun z hz => (hf z hz).congr (mem_nhdsSet_iff_forall.mp hg z hz)
/-
**analyticOnNhd_congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOnNhd_congr' (h : f =ᶠ[𝓝ˢ s] g) : AnalyticOnNhd 𝕜 f s ↔ AnalyticOn
Nhd 𝕜 g s
参数：h : f =ᶠ[𝓝ˢ s] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.congr'`：AnalyticOnNhd.congr' (hf : AnalyticOnNhd 𝕜 f s) (h
g : f =ᶠ[𝓝ˢ s] g) : AnalyticOnNhd 𝕜 g s
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem analyticOnNhd_congr' (h : f =ᶠ[𝓝ˢ s] g) : AnalyticOnNhd 𝕜 f s ↔ AnalyticOnNhd 𝕜 g s :=
  ⟨fun hf => hf.congr' h, fun hg => hg.congr' h.symm⟩
/-
**AnalyticOnNhd.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.congr (hs : IsOpen s) (hf : AnalyticOnNhd 𝕜 f s) (hg : s.EqO
n f g) : AnalyticOnNhd 𝕜 g s
参数：hs : IsOpen s；hf : AnalyticOnNhd 𝕜 f s；hg : s.EqOn f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.congr'`：AnalyticOnNhd.congr' (hf : AnalyticOnNhd 𝕜 f s) (h
g : f =ᶠ[𝓝ˢ s] g) : AnalyticOnNhd 𝕜 g s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsSet_iff_forall`：mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : 
X, x in t -> s in 𝓝 x
· 使用定理 `Filter.eventuallyEq_iff_exists_mem`：eventuallyEq_iff_exists_mem {l : Fil
ter α} {f g : α -> β} : f =ᶠ[l] g ↔ exists s in l, EqOn f g s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem AnalyticOnNhd.congr (hs : IsOpen s) (hf : AnalyticOnNhd 𝕜 f s) (hg : s.EqOn f g) :
    AnalyticOnNhd 𝕜 g s :=
  hf.congr' <| mem_nhdsSet_iff_forall.mpr
    (fun _ hz => eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hz, hg⟩)
/-
**analyticOnNhd_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOnNhd_congr (hs : IsOpen s) (h : s.EqOn f g) : AnalyticOnNhd 𝕜 f s
 ↔ AnalyticOnNhd 𝕜 g s
参数：hs : IsOpen s；h : s.EqOn f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.congr`：AnalyticOnNhd.congr (hs : IsOpen s) (hf : AnalyticO
nNhd 𝕜 f s) (hg : s.EqOn f g) : AnalyticOnNhd 𝕜 g s
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
theorem analyticOnNhd_congr (hs : IsOpen s) (h : s.EqOn f g) : AnalyticOnNhd 𝕜 f s ↔
    AnalyticOnNhd 𝕜 g s := ⟨fun hf => hf.congr hs h, fun hg => hg.congr hs h.symm⟩
/-
**AnalyticWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.mono_of_mem_nhdsWithin (h : AnalyticWithinAt 𝕜 f s x) (hs
t : s in 𝓝[t] x) : AnalyticWithinAt 𝕜 f t x
参数：h : AnalyticWithinAt 𝕜 f s x；hst : s in 𝓝[t] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin`：HasFPowerSeriesWithinAt.
mono_of_mem_nhdsWithin (h : HasFPowerSeriesWithinAt f p s x) (hst : s in 𝓝[t] x)
 : HasFPowerSeriesWithinAt f p t x
-/
theorem AnalyticWithinAt.mono_of_mem_nhdsWithin
    (h : AnalyticWithinAt 𝕜 f s x) (hst : s ∈ 𝓝[t] x) : AnalyticWithinAt 𝕜 f t x := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, hp.mono_of_mem_nhdsWithin hst⟩
/-
**AnalyticWithinAt.congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.congr_set (h : AnalyticWithinAt 𝕜 f s x) (hst : s =ᶠ[𝓝 x]
 t) : AnalyticWithinAt 𝕜 f t x
参数：h : AnalyticWithinAt 𝕜 f s x；hst : s =ᶠ[𝓝 x] t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.mono_of_mem_nhdsWithin`：AnalyticWithinAt.mono_of_mem_nh
dsWithin (h : AnalyticWithinAt 𝕜 f s x) (hst : s in 𝓝[t] x) : AnalyticWithinAt 𝕜
 f t x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
-/
theorem AnalyticWithinAt.congr_set (h : AnalyticWithinAt 𝕜 f s x) (hst : s =ᶠ[𝓝 x] t) :
    AnalyticWithinAt 𝕜 f t x := by
  refine h.mono_of_mem_nhdsWithin ?_
  simp [← nhdsWithin_eq_iff_eventuallyEq.mpr hst, self_mem_nhdsWithin]
/-
**AnalyticOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.mono {f : E -> F} {s t : Set E} (h : AnalyticOn 𝕜 f t) (hs : s 
subseteq t) : AnalyticOn 𝕜 f s
参数：h : AnalyticOn 𝕜 f t；hs : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticWithinAt.mono`：AnalyticWithinAt.mono (hf : AnalyticWithinAt 𝕜 f 
s x) (h : t subseteq s) : AnalyticWithinAt 𝕜 f t x
-/
lemma AnalyticOn.mono {f : E → F} {s t : Set E} (h : AnalyticOn 𝕜 f t)
    (hs : s ⊆ t) : AnalyticOn 𝕜 f s :=
  fun _ m ↦ (h _ (hs m)).mono hs
/-
**analyticWithinAt_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {s : Set E}   {x y :
 E}, AnalyticWithinAt 𝕜 f (insert y s) x ↔ AnalyticWithinAt 𝕜 f s x
参数：insert y s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem analyticWithinAt_insert {f : E → F} {s : Set E} {x y : E} :
    AnalyticWithinAt 𝕜 f (insert y s) x ↔ AnalyticWithinAt 𝕜 f s x := by
  simp [AnalyticWithinAt]
/-
**AnalyticOn.analyticAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.analyticAt {f : E -> F} {z : E} {s : Set E} (hU : s in 𝓝 z) (h 
: AnalyticOn 𝕜 f s) : AnalyticAt 𝕜 f z
参数：hU : s in 𝓝 z；h : AnalyticOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `hasFPowerSeriesWithinAt_iff_of_nhds`：hasFPowerSeriesWithinAt_iff_of_nhds
 (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) {U : Set E} (hU : U in 𝓝 x) : 
HasFPowerSeriesWithinAt f…
-/
lemma AnalyticOn.analyticAt {f : E → F} {z : E} {s : Set E} (hU : s ∈ 𝓝 z)
    (h : AnalyticOn 𝕜 f s) : AnalyticAt 𝕜 f z := by
  obtain ⟨p, hp⟩ := h z (mem_of_mem_nhds hU)
  exact ⟨p, hasFPowerSeriesWithinAt_iff_of_nhds f p hU |>.mp hp⟩

/-!
### Composition with linear maps
-/

/-- If a function `f` has a power series `p` on a ball within a set and `g` is linear,
then `g ∘ f` has the power series `g ∘ p` on the same ball. -/
/-
**ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall (g : F ->L[𝕜] G) (h :
 HasFPowerSeriesWithinOnBall f p s x r) : HasFPowerSeriesWithinOnBall (g ∘ f) (g
.compFormalMultilinearSeries p) s x r where r_le
参数：g : F ->L[𝕜] G；h : HasFPowerSeriesWithinOnBall f p s x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `FormalMultilinearSeries.radius_le_radius_continuousLinearMap_comp`：radiu
s_le_radius_continuousLinearMap_comp (p : FormalMultilinearSeries 𝕜 E F) (f : F 
->L[𝕜] G) : p.radius <= (f.compFormalMultilinearSeries …
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `ContinuousLinearMap.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u
_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂]
 [inst_2 : AddCo…
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …

--- 原说明 ---
If a function `f` has a power series `p` on a ball within a set and `g` is linea
r,
then `g ∘ f` has the power series `g ∘ p` on the same ball.
-/
theorem ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall (g : F →L[𝕜] G)
    (h : HasFPowerSeriesWithinOnBall f p s x r) :
    HasFPowerSeriesWithinOnBall (g ∘ f) (g.compFormalMultilinearSeries p) s x r where
  r_le := h.r_le.trans (p.radius_le_radius_continuousLinearMap_comp _)
  r_pos := h.r_pos
  hasSum hy h'y := by
    simpa only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] using
      g.hasSum (h.hasSum hy h'y)

/-- If a function `f` has a power series `p` on a ball and `g` is linear, then `g ∘ f` has the
power series `g ∘ p` on the same ball. -/
/-
**ContinuousLinearMap.comp_hasFPowerSeriesOnBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.comp_hasFPowerSeriesOnBall (g : F ->L[𝕜] G) (h : HasFP
owerSeriesOnBall f p x r) : HasFPowerSeriesOnBall (g ∘ f) (g.compFormalMultiline
arSeries p) x r
参数：g : F ->L[𝕜] G；h : HasFPowerSeriesOnBall f p x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall`：ContinuousLinearMa
p.comp_hasFPowerSeriesWithinOnBall (g : F ->L[𝕜] G) (h : HasFPowerSeriesWithinOn
Ball f p s x r) : HasFPowerSeriesWithinOnB…

--- 原说明 ---
If a function `f` has a power series `p` on a ball and `g` is linear, then `g ∘ 
f` has the
power series `g ∘ p` on the same ball.
-/
theorem ContinuousLinearMap.comp_hasFPowerSeriesOnBall (g : F →L[𝕜] G)
    (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (g ∘ f) (g.compFormalMultilinearSeries p) x r := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact g.comp_hasFPowerSeriesWithinOnBall h

/-- If a function `f` is analytic on a set `s` and `g` is linear, then `g ∘ f` is analytic
on `s`. -/
/-
**ContinuousLinearMap.comp_analyticOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.comp_analyticOn (g : F ->L[𝕜] G) (h : AnalyticOn 𝕜 f s
) : AnalyticOn 𝕜 (g ∘ f) s
参数：g : F ->L[𝕜] G；h : AnalyticOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall`：ContinuousLinearMa
p.comp_hasFPowerSeriesWithinOnBall (g : F ->L[𝕜] G) (h : HasFPowerSeriesWithinOn
Ball f p s x r) : HasFPowerSeriesWithinOnB…

--- 原说明 ---
If a function `f` is analytic on a set `s` and `g` is linear, then `g ∘ f` is an
alytic
on `s`.
-/
theorem ContinuousLinearMap.comp_analyticOn (g : F →L[𝕜] G) (h : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (g ∘ f) s := by
  rintro x hx
  rcases h x hx with ⟨p, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, r, g.comp_hasFPowerSeriesWithinOnBall hp⟩

/-- If a function `f` is analytic on a set `s` and `g` is linear, then `g ∘ f` is analytic
on `s`. -/
/-
**ContinuousLinearMap.comp_analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.comp_analyticOnNhd {s : Set E} (g : F ->L[𝕜] G) (h : A
nalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (g ∘ f) s
参数：g : F ->L[𝕜] G；h : AnalyticOnNhd 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `ContinuousLinearMap.comp_hasFPowerSeriesOnBall`：ContinuousLinearMap.comp
_hasFPowerSeriesOnBall (g : F ->L[𝕜] G) (h : HasFPowerSeriesOnBall f p x r) : Ha
sFPowerSeriesOnBall (g ∘ f) (g.compF…

--- 原说明 ---
If a function `f` is analytic on a set `s` and `g` is linear, then `g ∘ f` is an
alytic
on `s`.
-/
theorem ContinuousLinearMap.comp_analyticOnNhd
    {s : Set E} (g : F →L[𝕜] G) (h : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (g ∘ f) s := by
  rintro x hx
  rcases h x hx with ⟨p, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, r, g.comp_hasFPowerSeriesOnBall hp⟩

/-!
### Relation between analytic function and the partial sums of its power series
-/

/-
**HasFPowerSeriesWithinOnBall.tendsto_partialSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.tendsto_partialSum (hf : HasFPowerSeriesWithin
OnBall f p s x r) {y : E} (hy : y in Metric.eball (0 : E) r) (h'y : x + y in ins
ert x s) : Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y)))
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；hy : y in Metric.eball (0 : E) r；h
'y : x + y in insert x s。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasSum.tendsto_sum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {m : M} {f : ℕ → M},   HasSum f m → Filter.Tendsto (fun 
n => ∑ i ∈ F…
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …

--- 原说明 ---
### Relation between analytic function and the partial sums of its power series
-/
theorem HasFPowerSeriesWithinOnBall.tendsto_partialSum
    (hf : HasFPowerSeriesWithinOnBall f p s x r) {y : E} (hy : y ∈ Metric.eball (0 : E) r)
    (h'y : x + y ∈ insert x s) :
    Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y))) :=
  (hf.hasSum h'y hy).tendsto_sum_nat
/-
**HasFPowerSeriesOnBall.tendsto_partialSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.tendsto_partialSum (hf : HasFPowerSeriesOnBall f p x
 r) {y : E} (hy : y in Metric.eball (0 : E) r) : Tendsto (fun n => p.partialSum 
n y) atTop (𝓝 (f (x + y)))
参数：hf : HasFPowerSeriesOnBall f p x r；hy : y in Metric.eball (0 : E) r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasSum.tendsto_sum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {m : M} {f : ℕ → M},   HasSum f m → Filter.Tendsto (fun 
n => ∑ i ∈ F…
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesOnBall.tendsto_partialSum
    (hf : HasFPowerSeriesOnBall f p x r) {y : E} (hy : y ∈ Metric.eball (0 : E) r) :
    Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y))) :=
  (hf.hasSum hy).tendsto_sum_nat
/-
**HasFPowerSeriesAt.tendsto_partialSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.tendsto_partialSum (hf : HasFPowerSeriesAt f p x) : fora
llᶠ y in 𝓝 0, Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y)))
参数：hf : HasFPowerSeriesAt f p x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `HasFPowerSeriesOnBall.tendsto_partialSum`：HasFPowerSeriesOnBall.tendsto_
partialSum (hf : HasFPowerSeriesOnBall f p x r) {y : E} (hy : y in Metric.eball 
(0 : E) r) : Tendsto (fun n =>…
-/
theorem HasFPowerSeriesAt.tendsto_partialSum
    (hf : HasFPowerSeriesAt f p x) :
    ∀ᶠ y in 𝓝 0, Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y))) := by
  rcases hf with ⟨r, hr⟩
  filter_upwards [Metric.eball_mem_nhds (0 : E) hr.r_pos] with y hy
  exact hr.tendsto_partialSum hy

open Finset in
/-- If a function admits a power series expansion within a ball, then the partial sums
`p.partialSum n z` converge to `f (x + y)` as `n → ∞` and `z → y`. Note that `x + z` doesn't need
to belong to the set where the power series expansion holds. -/
/-
**HasFPowerSeriesWithinOnBall.tendsto_partialSum_prod** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：HasFPowerSeriesWithinOnBall.tendsto_partialSum_prod {y : E} (hf : HasFPowe
rSeriesWithinOnBall f p s x r) (hy : y in Metric.eball (0 : E) r) (h'y : x + y i
n insert x s) : Tendsto (fun (z : Nat × E) => p.partialSum z.1 z.2) (atTop ×ˢ 𝓝 
y) (𝓝 (f (x + y)))
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；hy : y in Metric.eball (0 : E) r；h
'y : x + y in insert x s。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `HasFPowerSeriesWithinOnBall.tendsto_partialSum`：HasFPowerSeriesWithinOnB
all.tendsto_partialSum (hf : HasFPowerSeriesWithinOnBall f p s x r) {y : E} (hy 
: y in Metric.eball (0 : E) r) (h'y …
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `FormalMultilinearSeries.summable_norm_mul_pow`：summable_norm_mul_pow (p 
: FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : ↑r < p.radius) : Summable fu
n n : Nat => ‖p n‖ * (r : Real) ^ n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `tendsto_sum_nat_add`：∀ {G : Type u_2} [inst : AddCommGroup G] [inst_1 : 
TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   (f : ℕ → G), Filter.
Tendsto (…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
（共 137 条，此处仅展示前 30 条）

--- 原说明 ---
If a function admits a power series expansion within a ball, then the partial su
ms
`p.partialSum n z` converge to `f (x + y)` as `n → ∞` and `z → y`. Note that `x 
+ z` doesn't need
to belong to the set where the power series expansion holds.
-/
theorem HasFPowerSeriesWithinOnBall.tendsto_partialSum_prod {y : E}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (hy : y ∈ Metric.eball (0 : E) r)
    (h'y : x + y ∈ insert x s) :
    Tendsto (fun (z : ℕ × E) ↦ p.partialSum z.1 z.2) (atTop ×ˢ 𝓝 y) (𝓝 (f (x + y))) := by
  have A : Tendsto (fun (z : ℕ × E) ↦ p.partialSum z.1 y) (atTop ×ˢ 𝓝 y) (𝓝 (f (x + y))) := by
    apply (hf.tendsto_partialSum hy h'y).comp tendsto_fst
  suffices Tendsto (fun (z : ℕ × E) ↦ p.partialSum z.1 z.2 - p.partialSum z.1 y)
    (atTop ×ˢ 𝓝 y) (𝓝 0) by simpa using A.add this
  apply Metric.tendsto_nhds.2 (fun ε εpos ↦ ?_)
  obtain ⟨r', yr', r'r⟩ : ∃ (r' : ℝ≥0), ‖y‖₊ < r' ∧ r' < r := by
    simp at hy
    simpa using ENNReal.lt_iff_exists_nnreal_btwn.1 hy
  have yr'_2 : ‖y‖ < r' := by simpa [← coe_nnnorm] using yr'
  have S : Summable fun n ↦ ‖p n‖ * ↑r' ^ n := p.summable_norm_mul_pow (r'r.trans_le hf.r_le)
  obtain ⟨k, hk⟩ : ∃ k, ∑' (n : ℕ), ‖p (n + k)‖ * ↑r' ^ (n + k) < ε / 4 := by
    have : Tendsto (fun k ↦ ∑' n, ‖p (n + k)‖ * ↑r' ^ (n + k)) atTop (𝓝 0) := by
      apply _root_.tendsto_sum_nat_add (f := fun n ↦ ‖p n‖ * ↑r' ^ n)
    exact ((tendsto_order.1 this).2 _ (by linarith)).exists
  have A : ∀ᶠ (z : ℕ × E) in atTop ×ˢ 𝓝 y,
      dist (p.partialSum k z.2) (p.partialSum k y) < ε / 4 := by
    have : ContinuousAt (fun z ↦ p.partialSum k z) y := (p.partialSum_continuous k).continuousAt
    exact tendsto_snd (Metric.tendsto_nhds.1 this.tendsto (ε / 4) (by linarith))
  have B : ∀ᶠ (z : ℕ × E) in atTop ×ˢ 𝓝 y, ‖z.2‖₊ < r' := by
    suffices ∀ᶠ (z : E) in 𝓝 y, ‖z‖₊ < r' from tendsto_snd this
    have : Metric.ball 0 r' ∈ 𝓝 y := Metric.isOpen_ball.mem_nhds (by simpa using yr'_2)
    filter_upwards [this] with a ha using by simpa [← coe_nnnorm] using ha
  have C : ∀ᶠ (z : ℕ × E) in atTop ×ˢ 𝓝 y, k ≤ z.1 := tendsto_fst (Ici_mem_atTop _)
  filter_upwards [A, B, C]
  rintro ⟨n, z⟩ hz h'z hkn
  simp only [dist_eq_norm, sub_zero] at hz ⊢
  have I (w : E) (hw : ‖w‖₊ < r') : ‖∑ i ∈ Ico k n, p i (fun _ ↦ w)‖ ≤ ε / 4 := calc
    ‖∑ i ∈ Ico k n, p i (fun _ ↦ w)‖
    _ = ‖∑ i ∈ range (n - k), p (i + k) (fun _ ↦ w)‖ := by
        rw [sum_Ico_eq_sum_range]
        congr with i
        rw [add_comm k]
    _ ≤ ∑ i ∈ range (n - k), ‖p (i + k) (fun _ ↦ w)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range (n - k), ‖p (i + k)‖ * ‖w‖ ^ (i + k) := by
        gcongr with i _hi; exact ((p (i + k)).le_opNorm _).trans_eq (by simp)
    _ ≤ ∑ i ∈ range (n - k), ‖p (i + k)‖ * ↑r' ^ (i + k) := by
        gcongr with i _hi; simpa [← coe_nnnorm] using hw.le
    _ ≤ ∑' i, ‖p (i + k)‖ * ↑r' ^ (i + k) := by
        apply Summable.sum_le_tsum _ (fun i _hi ↦ by positivity)
        apply ((_root_.summable_nat_add_iff k).2 S)
    _ ≤ ε / 4 := hk.le
  calc
  ‖p.partialSum n z - p.partialSum n y‖
  _ = ‖∑ i ∈ range n, p i (fun _ ↦ z) - ∑ i ∈ range n, p i (fun _ ↦ y)‖ := rfl
  _ = ‖(∑ i ∈ range k, p i (fun _ ↦ z) + ∑ i ∈ Ico k n, p i (fun _ ↦ z))
        - (∑ i ∈ range k, p i (fun _ ↦ y) + ∑ i ∈ Ico k n, p i (fun _ ↦ y))‖ := by
    simp [sum_range_add_sum_Ico _ hkn]
  _ = ‖(p.partialSum k z - p.partialSum k y) + (∑ i ∈ Ico k n, p i (fun _ ↦ z))
        + (- ∑ i ∈ Ico k n, p i (fun _ ↦ y))‖ := by
    congr 1
    simp only [FormalMultilinearSeries.partialSum]
    abel
  _ ≤ ‖p.partialSum k z - p.partialSum k y‖ + ‖∑ i ∈ Ico k n, p i (fun _ ↦ z)‖
      + ‖- ∑ i ∈ Ico k n, p i (fun _ ↦ y)‖ := norm_add₃_le
  _ ≤ ε / 4 + ε / 4 + ε / 4 := by
    gcongr
    · exact I _ h'z
    · simp only [norm_neg]; exact I _ yr'
  _ < ε := by linarith

/-- If a function admits a power series on a ball, then the partial sums
`p.partialSum n z` converges to `f (x + y)` as `n → ∞` and `z → y`. -/
/-
**HasFPowerSeriesOnBall.tendsto_partialSum_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.tendsto_partialSum_prod {y : E} (hf : HasFPowerSerie
sOnBall f p x r) (hy : y in Metric.eball (0 : E) r) : Tendsto (fun (z : Nat × E)
 => p.partialSum z.1 z.2) (atTop ×ˢ 𝓝 y) (𝓝 (f (x + y)))
参数：hf : HasFPowerSeriesOnBall f p x r；hy : y in Metric.eball (0 : E) r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.tendsto_partialSum_prod`：HasFPowerSeriesWith
inOnBall.tendsto_partialSum_prod {y : E} (hf : HasFPowerSeriesWithinOnBall f p s
 x r) (hy : y in Metric.eball (0 : E) r) …
· 使用引理 `HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall`：HasFPowerSeriesOnBall
.hasFPowerSeriesWithinOnBall (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSer
iesWithinOnBall f p s x r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s

--- 原说明 ---
If a function admits a power series on a ball, then the partial sums
`p.partialSum n z` converges to `f (x + y)` as `n → ∞` and `z → y`.
-/
theorem HasFPowerSeriesOnBall.tendsto_partialSum_prod {y : E}
    (hf : HasFPowerSeriesOnBall f p x r) (hy : y ∈ Metric.eball (0 : E) r) :
    Tendsto (fun (z : ℕ × E) ↦ p.partialSum z.1 z.2) (atTop ×ˢ 𝓝 y) (𝓝 (f (x + y))) :=
  (hf.hasFPowerSeriesWithinOnBall (s := univ)).tendsto_partialSum_prod hy (by simp)

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence.

This version provides an upper estimate that decreases both in `‖y‖` and `n`. See also
`HasFPowerSeriesWithinOnBall.uniform_geometric_approx` for a weaker version. -/
/-
**HasFPowerSeriesWithinOnBall.uniform_geometric_approx'** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.uniform_geometric_approx' {r' : Real>=0} (hf :
 HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : Real>=0∞) < r) : exists a in 
Ioo (0 : Real) 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n, x 
+ y in insert x s -> ‖f (x + y) - p.partialSum n y‖ <= C * (a * (‖y‖ / r')) ^ n
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；h : (r' : Real>=0∞) < r。
该定理/引理给出了一组等式。
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
· 使用定理 `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius`：norm_mul_p
ow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) : exists a in Ioo (0 : Real) 1, e
xists C > 0, forall n, ‖p n‖ * (r : Real) ^ n <= C…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ball_zero_eq`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (r : ℝ), Me
tric.ball 0 r = {x | ‖x‖ < r}
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mem_eball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : 
E} {r : ENNReal}, a ∈ Metric.eball 0 r ↔ ‖a‖ₑ < r
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_right_comm`：mul_div_right_comm : a * b / c = a / c * b
（共 89 条，此处仅展示前 30 条）

--- 原说明 ---
If a function admits a power series expansion, then it is exponentially close to
 the partial
sums of this power series on strict subdisks of the disk of convergence.

This version provides an upper estimate that decreases both in `‖y‖` and `n`. Se
e also
`HasFPowerSeriesWithinOnBall.uniform_geometric_approx` for a weaker version.
-/
theorem HasFPowerSeriesWithinOnBall.uniform_geometric_approx' {r' : ℝ≥0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n, x + y ∈ insert x s →
      ‖f (x + y) - p.partialSum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n := by
  obtain ⟨a, ha, C, hC, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n, ‖p n‖ * (r' : ℝ) ^ n ≤ C * a ^ n :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (h.trans_le hf.r_le)
  refine ⟨a, ha, C / (1 - a), div_pos hC (sub_pos.2 ha.2), fun y hy n ys => ?_⟩
  have yr' : ‖y‖ < r' := by
    rw [ball_zero_eq] at hy
    exact hy
  have hr'0 : 0 < (r' : ℝ) := (norm_nonneg _).trans_lt yr'
  have : y ∈ Metric.eball (0 : E) r := by
    refine mem_eball_zero_iff.2 (lt_trans ?_ h)
    simpa [enorm] using! yr'
  rw [norm_sub_rev, ← mul_div_right_comm]
  have ya : a * (‖y‖ / ↑r') ≤ a :=
    mul_le_of_le_one_right ha.1.le (div_le_one_of_le₀ yr'.le r'.coe_nonneg)
  suffices ‖p.partialSum n y - f (x + y)‖ ≤ C * (a * (‖y‖ / r')) ^ n / (1 - a * (‖y‖ / r')) by
    refine this.trans ?_
    have : 0 < a := ha.1
    gcongr
    apply_rules [sub_pos.2, ha.2]
  apply norm_sub_le_of_geometric_bound_of_hasSum (ya.trans_lt ha.2) _ (hf.hasSum ys this)
  intro n
  calc
    ‖(p n) fun _ : Fin n => y‖
    _ ≤ ‖p n‖ * ∏ _i : Fin n, ‖y‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖p n‖ * (r' : ℝ) ^ n * (‖y‖ / r') ^ n := by simp [field, div_pow]
    _ ≤ C * a ^ n * (‖y‖ / r') ^ n := by gcongr ?_ * _; apply hp
    _ ≤ C * (a * (‖y‖ / r')) ^ n := by rw [mul_pow, mul_assoc]

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence.

This version provides an upper estimate that decreases both in `‖y‖` and `n`. See also
`HasFPowerSeriesOnBall.uniform_geometric_approx` for a weaker version. -/
/-
**HasFPowerSeriesOnBall.uniform_geometric_approx'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.uniform_geometric_approx' {r' : Real>=0} (hf : HasFP
owerSeriesOnBall f p x r) (h : (r' : Real>=0∞) < r) : exists a in Ioo (0 : Real)
 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n, ‖f (x + y) - p.p
artialSum n y‖ <= C * (a * (‖y‖ / r')) ^ n
参数：hf : HasFPowerSeriesOnBall f p x r；h : (r' : Real>=0∞) < r。
该定理/引理给出了一组等式。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `HasFPowerSeriesWithinOnBall.uniform_geometric_approx'`：HasFPowerSeriesWi
thinOnBall.uniform_geometric_approx' {r' : Real>=0} (hf : HasFPowerSeriesWithinO
nBall f p s x r) (h : (r' : Real>=0∞) < r) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …

--- 原说明 ---
If a function admits a power series expansion, then it is exponentially close to
 the partial
sums of this power series on strict subdisks of the disk of convergence.

This version provides an upper estimate that decreases both in `‖y‖` and `n`. Se
e also
`HasFPowerSeriesOnBall.uniform_geometric_approx` for a weaker version.
-/
theorem HasFPowerSeriesOnBall.uniform_geometric_approx' {r' : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x r) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n,
      ‖f (x + y) - p.partialSum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.uniform_geometric_approx' h

/-- If a function admits a power series expansion within a set in a ball, then it is exponentially
close to the partial sums of this power series on strict subdisks of the disk of convergence. -/
/-
**HasFPowerSeriesWithinOnBall.uniform_geometric_approx** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.uniform_geometric_approx {r' : Real>=0} (hf : 
HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : Real>=0∞) < r) : exists a in I
oo (0 : Real) 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n, x +
 y in insert x s -> ‖f (x + y) - p.partialSum n y‖ <= C * a ^ n
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；h : (r' : Real>=0∞) < r。
该定理/引理给出了一组等式。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.uniform_geometric_approx'`：HasFPowerSeriesWi
thinOnBall.uniform_geometric_approx' {r' : Real>=0} (hf : HasFPowerSeriesWithinO
nBall f p s x r) (h : (r' : Real>=0∞) < r) …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ball_zero_eq`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (r : ℝ), Me
tric.ball 0 r = {x | ‖x‖ < r}
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `mul_le_of_le_one_right`：mul_le_of_le_one_right [PosMulMono α] (ha : 0 <=
 a) (h : b <= 1) : a * b <= a
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
If a function admits a power series expansion within a set in a ball, then it is
 exponentially
close to the partial sums of this power series on strict subdisks of the disk of
 convergence.
-/
theorem HasFPowerSeriesWithinOnBall.uniform_geometric_approx {r' : ℝ≥0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n, x + y ∈ insert x s →
      ‖f (x + y) - p.partialSum n y‖ ≤ C * a ^ n := by
  obtain ⟨a, ha, C, hC, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n,
      x + y ∈ insert x s → ‖f (x + y) - p.partialSum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n :=
    hf.uniform_geometric_approx' h
  refine ⟨a, ha, C, hC, fun y hy n ys => (hp y hy n ys).trans ?_⟩
  have yr' : ‖y‖ < r' := by rwa [ball_zero_eq] at hy
  have := ha.1.le -- needed to discharge a side goal on the next line
  gcongr
  exact mul_le_of_le_one_right ha.1.le (div_le_one_of_le₀ yr'.le r'.coe_nonneg)

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence. -/
/-
**HasFPowerSeriesOnBall.uniform_geometric_approx** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.uniform_geometric_approx {r' : Real>=0} (hf : HasFPo
werSeriesOnBall f p x r) (h : (r' : Real>=0∞) < r) : exists a in Ioo (0 : Real) 
1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n, ‖f (x + y) - p.pa
rtialSum n y‖ <= C * a ^ n
参数：hf : HasFPowerSeriesOnBall f p x r；h : (r' : Real>=0∞) < r。
该定理/引理给出了一组等式。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `HasFPowerSeriesWithinOnBall.uniform_geometric_approx`：HasFPowerSeriesWit
hinOnBall.uniform_geometric_approx {r' : Real>=0} (hf : HasFPowerSeriesWithinOnB
all f p s x r) (h : (r' : Real>=0∞) < r) :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …

--- 原说明 ---
If a function admits a power series expansion, then it is exponentially close to
 the partial
sums of this power series on strict subdisks of the disk of convergence.
-/
theorem HasFPowerSeriesOnBall.uniform_geometric_approx {r' : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x r) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n,
      ‖f (x + y) - p.partialSum n y‖ ≤ C * a ^ n := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.uniform_geometric_approx h

/-- Taylor formula for an analytic function within a set, `IsBigO` version. -/
/-
**HasFPowerSeriesWithinAt.isBigO_sub_partialSum_pow** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：HasFPowerSeriesWithinAt.isBigO_sub_partialSum_pow (hf : HasFPowerSeriesWit
hinAt f p s x) (n : Nat) : (fun y : E => f (x + y) - p.partialSum n y) =O[𝓝[(x +
 ·) ⁻¹' insert x s] 0] fun y => ‖y‖ ^ n
参数：hf : HasFPowerSeriesWithinAt f p s x；n : Nat。
该定理/引理给出了一组等式。
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
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.uniform_geometric_approx'`：HasFPowerSeriesWi
thinOnBall.uniform_geometric_approx' {r' : Real>=0} (hf : HasFPowerSeriesWithinO
nBall f p s x r) (h : (r' : Real>=0∞) < r) …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Taylor formula for an analytic function within a set, `IsBigO` version.
-/
theorem HasFPowerSeriesWithinAt.isBigO_sub_partialSum_pow
    (hf : HasFPowerSeriesWithinAt f p s x) (n : ℕ) :
    (fun y : E => f (x + y) - p.partialSum n y)
      =O[𝓝[(x + ·) ⁻¹' insert x s] 0] fun y => ‖y‖ ^ n := by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  obtain ⟨a, -, C, -, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n,
      x + y ∈ insert x s → ‖f (x + y) - p.partialSum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n :=
    hf.uniform_geometric_approx' h
  refine isBigO_iff.2 ⟨C * (a / r') ^ n, ?_⟩
  replace r'0 : 0 < (r' : ℝ) := mod_cast r'0
  filter_upwards [inter_mem_nhdsWithin _ (Metric.ball_mem_nhds (0 : E) r'0)] with y hy
  simpa [mul_pow, mul_div_assoc, mul_assoc, div_mul_eq_mul_div, div_pow]
    using hp y hy.2 n (by simpa using hy.1)

/-- Taylor formula for an analytic function, `IsBigO` version. -/
/-
**HasFPowerSeriesAt.isBigO_sub_partialSum_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.isBigO_sub_partialSum_pow (hf : HasFPowerSeriesAt f p x)
 (n : Nat) : (fun y : E => f (x + y) - p.partialSum n y) =O[𝓝 0] fun y => ‖y‖ ^ 
n
参数：hf : HasFPowerSeriesAt f p x；n : Nat。
该定理/引理给出了一组等式。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `HasFPowerSeriesWithinAt.isBigO_sub_partialSum_pow`：HasFPowerSeriesWithin
At.isBigO_sub_partialSum_pow (hf : HasFPowerSeriesWithinAt f p s x) (n : Nat) : 
(fun y : E => f (x + y) - p.partialSum …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …

--- 原说明 ---
Taylor formula for an analytic function, `IsBigO` version.
-/
theorem HasFPowerSeriesAt.isBigO_sub_partialSum_pow
    (hf : HasFPowerSeriesAt f p x) (n : ℕ) :
    (fun y : E => f (x + y) - p.partialSum n y) =O[𝓝 0] fun y => ‖y‖ ^ n := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  simpa using hf.isBigO_sub_partialSum_pow n

/-- If `f` has formal power series `∑ n, pₙ` in a set, within a ball of radius `r`, then
for `y, z` in any smaller ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is
bounded above by `C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. This lemma formulates this property
using `IsBigO` and `Filter.principal` on `E × E`. -/
/-
**HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal** 是 Mat
hlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal (hf
 : HasFPowerSeriesWithinOnBall f p s x r) (hr : r' < r) : (fun y : E × E => f y.
1 - f y.2 - p 1 fun _ => y.1 - y.2) =O[𝓟 (Metric.eball (x, x) r' inter ((insert 
x s) ×ˢ (insert x s)))] fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；hr : r' < r。
该定理/引理给出了一组等式。
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
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.eball_zero`：eball_zero : eball x 0 = ∅
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius`：norm_mul_p
ow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) : exists a in Ioo (0 : Real) 1, e
xists C > 0, forall n, ‖p n‖ * (r : Real) ^ n <= C…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.eball_prod_same`：eball_prod_same [PseudoEMetricSpace β] (x : α) (
y : β) (r : Real>=0∞) : eball x r ×ˢ eball y r = eball (x, y) r
· 使用定理 `Metric.eball_subset_eball`：eball_subset_eball (h : ε₁ <= ε₂) : eball x ε
₁ subseteq eball x ε₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Finset.sum_range_one`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ →
 M), ∑ k ∈ Finset.range 1, f k = f 0
· 使用定理 `HasFPowerSeriesWithinOnBall.coeff_zero`：HasFPowerSeriesWithinOnBall.coef
f_zero (hf : HasFPowerSeriesWithinOnBall f pf s x r) (v : Fin 0 -> E) : pf 0 v =
 f x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
（共 161 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` has formal power series `∑ n, pₙ` in a set, within a ball of radius `r`, 
then
for `y, z` in any smaller ball, the norm of the difference `f y - f z - p 1 (fun
 _ ↦ y - z)` is
bounded above by `C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. This lemma formulates th
is property
using `IsBigO` and `Filter.principal` on `E × E`.
-/
theorem HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (hr : r' < r) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2)
      =O[𝓟 (Metric.eball (x, x) r' ∩ ((insert x s) ×ˢ (insert x s)))]
      fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  lift r' to ℝ≥0 using ne_top_of_lt hr
  rcases eq_zero_or_pos r' with (rfl | hr'0)
  · simp only [ENNReal.coe_zero, Metric.eball_zero, empty_inter, principal_empty, isBigO_bot]
  obtain ⟨a, ha, C, hC : 0 < C, hp⟩ :
      ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n : ℕ, ‖p n‖ * (r' : ℝ) ^ n ≤ C * a ^ n :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (hr.trans_le hf.r_le)
  simp only [← le_div_iff₀ (pow_pos (NNReal.coe_pos.2 hr'0) _)] at hp
  set L : E × E → ℝ := fun y =>
    C * (a / r') ^ 2 * (‖y - (x, x)‖ * ‖y.1 - y.2‖) * (a / (1 - a) ^ 2 + 2 / (1 - a))
  have hL : ∀ y ∈ Metric.eball (x, x) r' ∩ ((insert x s) ×ˢ (insert x s)),
      ‖f y.1 - f y.2 - p 1 fun _ => y.1 - y.2‖ ≤ L y := by
    intro y ⟨hy', ys⟩
    have hy : y ∈ Metric.eball x r ×ˢ Metric.eball x r := by
      rw [Metric.eball_prod_same]
      exact Metric.eball_subset_eball hr.le hy'
    set A : ℕ → F := fun n => (p n fun _ => y.1 - x) - p n fun _ => y.2 - x
    have hA : HasSum (fun n => A (n + 2)) (f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) := by
      convert
        (hasSum_nat_add_iff' 2).2
          ((hf.hasSum_sub ⟨ys.1, hy.1⟩).sub (hf.hasSum_sub ⟨ys.2, hy.2⟩))
      rw [Finset.sum_range_succ, Finset.sum_range_one, hf.coeff_zero, hf.coeff_zero, sub_self,
        zero_add, ← Subsingleton.pi_single_eq (0 : Fin 1) (y.1 - x), Pi.single,
        ← Subsingleton.pi_single_eq (0 : Fin 1) (y.2 - x), Pi.single, ← (p 1).map_update_sub,
        ← Pi.single, Subsingleton.pi_single_eq, sub_sub_sub_cancel_right]
    rw [Metric.mem_eball, edist_eq_enorm_sub, enorm_lt_coe] at hy'
    set B : ℕ → ℝ := fun n => C * (a / r') ^ 2 * (‖y - (x, x)‖ * ‖y.1 - y.2‖) * ((n + 2) * a ^ n)
    have hAB : ∀ n, ‖A (n + 2)‖ ≤ B n := fun n =>
      calc
        ‖A (n + 2)‖ ≤ ‖p (n + 2)‖ * ↑(n + 2) * ‖y - (x, x)‖ ^ (n + 1) * ‖y.1 - y.2‖ := by
          simpa only [Fintype.card_fin, pi_norm_const, Prod.norm_def, Pi.sub_def,
            Prod.fst_sub, Prod.snd_sub, sub_sub_sub_cancel_right] using!
            (p <| n + 2).norm_image_sub_le (fun _ => y.1 - x) fun _ => y.2 - x
        _ = ‖p (n + 2)‖ * ‖y - (x, x)‖ ^ n * (↑(n + 2) * ‖y - (x, x)‖ * ‖y.1 - y.2‖) := by
          rw [pow_succ ‖y - (x, x)‖]
          ring
        _ ≤ C * a ^ (n + 2) / r' ^ (n + 2)
            * r' ^ n * (↑(n + 2) * ‖y - (x, x)‖ * ‖y.1 - y.2‖) := by
          have : 0 < a := ha.1
          gcongr
          · apply hp
          · apply hy'.le
        _ = B n := by
          simp [field, B, pow_succ]
    have hBL : HasSum B (L y) := by
      apply HasSum.mul_left
      simp only [add_mul]
      have : ‖a‖ < 1 := by simp only [Real.norm_eq_abs, abs_of_pos ha.1, ha.2]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact (hasSum_coe_mul_geometric_of_norm_lt_one this).add
          ((hasSum_geometric_of_norm_lt_one this).mul_left 2)
    exact hA.norm_le_of_bounded hBL hAB
  suffices L =O[𝓟 (Metric.eball (x, x) r' ∩ ((insert x s) ×ˢ (insert x s)))]
      fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ from
    .trans (.of_norm_eventuallyLE (eventually_principal.2 hL)) this
  simp_rw [L, mul_right_comm _ (_ * _)]
  exact (isBigO_refl _ _).const_mul_left _

/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is bounded above by
`C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. This lemma formulates this property using `IsBigO` and
`Filter.principal` on `E × E`. -/
/-
**HasFPowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal (hf : Has
FPowerSeriesOnBall f p x r) (hr : r' < r) : (fun y : E × E => f y.1 - f y.2 - p 
1 fun _ => y.1 - y.2) =O[𝓟 (Metric.eball (x, x) r')] fun y => ‖y - (x, x)‖ * ‖y.
1 - y.2‖
参数：hf : HasFPowerSeriesOnBall f p x r；hr : r' < r。
该定理/引理给出了一组等式。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal`：
HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal (hf : Has
FPowerSeriesWithinOnBall f p s x r) (hr : r' < r) : (fun y :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …

--- 原说明 ---
If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z
` in any smaller
ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is bounded ab
ove by
`C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. This lemma formulates this property using
 `IsBigO` and
`Filter.principal` on `E × E`.
-/
theorem HasFPowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal
    (hf : HasFPowerSeriesOnBall f p x r) (hr : r' < r) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2)
      =O[𝓟 (Metric.eball (x, x) r')] fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.isBigO_image_sub_image_sub_deriv_principal hr

/-- If `f` has formal power series `∑ n, pₙ` within a set, on a ball of radius `r`, then for `y, z`
in any smaller ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is bounded above
by `C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. -/
/-
**HasFPowerSeriesWithinOnBall.image_sub_sub_deriv_le** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：HasFPowerSeriesWithinOnBall.image_sub_sub_deriv_le (hf : HasFPowerSeriesWi
thinOnBall f p s x r) (hr : r' < r) : exists C, forallᵉ (y in insert x s inter M
etric.eball x r') (z in insert x s inter Metric.eball x r'), ‖f y - f z - p 1 fu
n _ => y - z‖ <= C * max ‖y - x‖ ‖z - x‖ * ‖y - z‖
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；hr : r' < r。
该定理/引理给出了一组等式。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal`：
HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal (hf : Has
FPowerSeriesWithinOnBall f p s x r) (hr : r' < r) : (fun y :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖

--- 原说明 ---
If `f` has formal power series `∑ n, pₙ` within a set, on a ball of radius `r`, 
then for `y, z`
in any smaller ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)
` is bounded above
by `C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`.
-/
theorem HasFPowerSeriesWithinOnBall.image_sub_sub_deriv_le
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (hr : r' < r) :
    ∃ C, ∀ᵉ (y ∈ insert x s ∩ Metric.eball x r') (z ∈ insert x s ∩ Metric.eball x r'),
      ‖f y - f z - p 1 fun _ => y - z‖ ≤ C * max ‖y - x‖ ‖z - x‖ * ‖y - z‖ := by
  have := hf.isBigO_image_sub_image_sub_deriv_principal hr
  simp only [isBigO_principal, mem_inter_iff, Metric.mem_eball, Prod.edist_eq, max_lt_iff, mem_prod,
    norm_mul, Real.norm_eq_abs, abs_norm, and_imp, Prod.forall, mul_assoc] at this ⊢
  rcases this with ⟨C, hC⟩
  exact ⟨C, fun y ys hy z zs hz ↦ hC y z hy hz ys zs⟩

/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is bounded above by
`C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. -/
/-
**HasFPowerSeriesOnBall.image_sub_sub_deriv_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.image_sub_sub_deriv_le (hf : HasFPowerSeriesOnBall f
 p x r) (hr : r' < r) : exists C, forallᵉ (y in Metric.eball x r') (z in Metric.
eball x r'), ‖f y - f z - p 1 fun _ => y - z‖ <= C * max ‖y - x‖ ‖z - x‖ * ‖y - 
z‖
参数：hf : HasFPowerSeriesOnBall f p x r；hr : r' < r。
该定理/引理给出了一组等式。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `HasFPowerSeriesWithinOnBall.image_sub_sub_deriv_le`：HasFPowerSeriesWithi
nOnBall.image_sub_sub_deriv_le (hf : HasFPowerSeriesWithinOnBall f p s x r) (hr 
: r' < r) : exists C, forallᵉ (y in inse…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …

--- 原说明 ---
If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z
` in any smaller
ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is bounded ab
ove by
`C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`.
-/
theorem HasFPowerSeriesOnBall.image_sub_sub_deriv_le
    (hf : HasFPowerSeriesOnBall f p x r) (hr : r' < r) :
    ∃ C, ∀ᵉ (y ∈ Metric.eball x r') (z ∈ Metric.eball x r'),
      ‖f y - f z - p 1 fun _ => y - z‖ ≤ C * max ‖y - x‖ ‖z - x‖ * ‖y - z‖ := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa only [mem_univ, insert_eq_of_mem, univ_inter] using hf.image_sub_sub_deriv_le hr

/-- If `f` has formal power series `∑ n, pₙ` at `x` within a set `s`, then
`f y - f z - p 1 (fun _ ↦ y - z) = O(‖(y, z) - (x, x)‖ * ‖y - z‖)` as `(y, z) → (x, x)`
within `s × s`. -/
/-
**HasFPowerSeriesWithinAt.isBigO_image_sub_norm_mul_norm_sub** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.isBigO_image_sub_norm_mul_norm_sub (hf : HasFPower
SeriesWithinAt f p s x) : (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y
.2) =O[𝓝[(insert x s) ×ˢ (insert x s)] (x, x)] fun y => ‖y - (x, x)‖ * ‖y.1 - y.
2‖
参数：hf : HasFPowerSeriesWithinAt f p s x。
该定理/引理给出了一组等式。
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
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `Asymptotics.IsBigO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} 
[inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f
 =O[l'] g → l…
· 使用定理 `HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal`：
HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal (hf : Has
FPowerSeriesWithinOnBall f p s x r) (hr : r' < r) : (fun y :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x

--- 原说明 ---
If `f` has formal power series `∑ n, pₙ` at `x` within a set `s`, then
`f y - f z - p 1 (fun _ ↦ y - z) = O(‖(y, z) - (x, x)‖ * ‖y - z‖)` as `(y, z) → 
(x, x)`
within `s × s`.
-/
theorem HasFPowerSeriesWithinAt.isBigO_image_sub_norm_mul_norm_sub
    (hf : HasFPowerSeriesWithinAt f p s x) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2)
      =O[𝓝[(insert x s) ×ˢ (insert x s)] (x, x)] fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  refine (hf.isBigO_image_sub_image_sub_deriv_principal h).mono ?_
  rw [inter_comm]
  exact le_principal_iff.2 (inter_mem_nhdsWithin _ (Metric.eball_mem_nhds _ r'0))

/-- If `f` has formal power series `∑ n, pₙ` at `x`, then
`f y - f z - p 1 (fun _ ↦ y - z) = O(‖(y, z) - (x, x)‖ * ‖y - z‖)` as `(y, z) → (x, x)`.
In particular, `f` is strictly differentiable at `x`. -/
/-
**HasFPowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：HasFPowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub (hf : HasFPowerSeries
At f p x) : (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) =O[𝓝 (x, x
)] fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖
参数：hf : HasFPowerSeriesAt f p x。
该定理/引理给出了一组等式。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `HasFPowerSeriesWithinAt.isBigO_image_sub_norm_mul_norm_sub`：HasFPowerSer
iesWithinAt.isBigO_image_sub_norm_mul_norm_sub (hf : HasFPowerSeriesWithinAt f p
 s x) : (fun y : E × E => f y.1 - f y.2 - p 1 fu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …

--- 原说明 ---
If `f` has formal power series `∑ n, pₙ` at `x`, then
`f y - f z - p 1 (fun _ ↦ y - z) = O(‖(y, z) - (x, x)‖ * ‖y - z‖)` as `(y, z) → 
(x, x)`.
In particular, `f` is strictly differentiable at `x`.
-/
theorem HasFPowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub (hf : HasFPowerSeriesAt f p x) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) =O[𝓝 (x, x)] fun y =>
      ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  simpa using hf.isBigO_image_sub_norm_mul_norm_sub

/-- If a function admits a power series expansion within a set at `x`, then it is the uniform limit
of the partial sums of this power series on strict subdisks of the disk of convergence, i.e.,
`f (x + y)` is the uniform limit of `p.partialSum n y` there. -/
/-
**HasFPowerSeriesWithinOnBall.tendstoUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.tendstoUniformlyOn {r' : Real>=0} (hf : HasFPo
werSeriesWithinOnBall f p s x r) (h : (r' : Real>=0∞) < r) : TendstoUniformlyOn 
(fun n y => p.partialSum n y) (fun y => f (x + y)) atTop ((x + ·) ⁻¹' (insert x 
s) inter Metric.ball (0 : E) r')
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；h : (r' : Real>=0∞) < r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.uniform_geometric_approx`：HasFPowerSeriesWit
hinOnBall.uniform_geometric_approx {r' : Real>=0} (hf : HasFPowerSeriesWithinOnB
all f p s x r) (h : (r' : Real>=0∞) < r) :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.tendstoUniformlyOn_iff`：tendstoUniformlyOn_iff {F : ι -> β -> α} 
{f : β -> α} {p : Filter ι} {s : Set β} : TendstoUniformlyOn F f p s ↔ forall ε 
> 0, forallᶠ n in p…
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_lt_one`：tendsto_pow_atTop_nhds_zero_of_lt
_one {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAd
dOfLE 𝕜] [Archimedean 𝕜] [T…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c

--- 原说明 ---
If a function admits a power series expansion within a set at `x`, then it is th
e uniform limit
of the partial sums of this power series on strict subdisks of the disk of conve
rgence, i.e.,
`f (x + y)` is the uniform limit of `p.partialSum n y` there.
-/
theorem HasFPowerSeriesWithinOnBall.tendstoUniformlyOn {r' : ℝ≥0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      ((x + ·) ⁻¹' (insert x s) ∩ Metric.ball (0 : E) r') := by
  obtain ⟨a, ha, C, -, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n,
    x + y ∈ insert x s → ‖f (x + y) - p.partialSum n y‖ ≤ C * a ^ n := hf.uniform_geometric_approx h
  refine Metric.tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  have L : Tendsto (fun n => (C : ℝ) * a ^ n) atTop (𝓝 ((C : ℝ) * 0)) :=
    tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one ha.1.le ha.2)
  rw [mul_zero] at L
  refine (L.eventually (gt_mem_nhds εpos)).mono fun n hn y hy => ?_
  rw [dist_eq_norm]
  exact (hp y hy.2 n hy.1).trans_lt hn

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f (x + y)`
is the uniform limit of `p.partialSum n y` there. -/
/-
**HasFPowerSeriesOnBall.tendstoUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.tendstoUniformlyOn {r' : Real>=0} (hf : HasFPowerSer
iesOnBall f p x r) (h : (r' : Real>=0∞) < r) : TendstoUniformlyOn (fun n y => p.
partialSum n y) (fun y => f (x + y)) atTop (Metric.ball (0 : E) r')
参数：hf : HasFPowerSeriesOnBall f p x r；h : (r' : Real>=0∞) < r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `HasFPowerSeriesWithinOnBall.tendstoUniformlyOn`：HasFPowerSeriesWithinOnB
all.tendstoUniformlyOn {r' : Real>=0} (hf : HasFPowerSeriesWithinOnBall f p s x 
r) (h : (r' : Real>=0∞) < r) : Tends…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …

--- 原说明 ---
If a function admits a power series expansion at `x`, then it is the uniform lim
it of the
partial sums of this power series on strict subdisks of the disk of convergence,
 i.e., `f (x + y)`
is the uniform limit of `p.partialSum n y` there.
-/
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn {r' : ℝ≥0} (hf : HasFPowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      (Metric.ball (0 : E) r') := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn h

/-- If a function admits a power series expansion within a set at `x`, then it is the locally
uniform limit of the partial sums of this power series on the disk of convergence, i.e., `f (x + y)`
is the locally uniform limit of `p.partialSum n y` there. -/
/-
**HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn (hf : HasFPowerSerie
sWithinOnBall f p s x r) : TendstoLocallyUniformlyOn (fun n y => p.partialSum n 
y) (fun y => f (x + y)) atTop ((x + ·) ⁻¹' (insert x s) inter Metric.eball (0 : 
E) r)
参数：hf : HasFPowerSeriesWithinOnBall f p s x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_eball`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x : α
} {ε : ENNReal}, IsOpen (Metric.eball x ε)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_inter_of_mem'`：nhdsWithin_inter_of_mem' {a : α} {s t : Set α}
 (h : t in 𝓝[s] a) : 𝓝[s inter t] a = 𝓝[s] a
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Metric.eball_subset_eball`：eball_subset_eball (h : ε₁ <= ε₂) : eball x ε
₁ subseteq eball x ε₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Metric.eball_coe`：Metric.eball_coe {x : α} {ε : Real>=0} : eball x ε = b
all x ε
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If a function admits a power series expansion within a set at `x`, then it is th
e locally
uniform limit of the partial sums of this power series on the disk of convergenc
e, i.e., `f (x + y)`
is the locally uniform limit of `p.partialSum n y` there.
-/
theorem HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      ((x + ·) ⁻¹' (insert x s) ∩ Metric.eball (0 : E) r) := by
  intro u hu y hy
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hy.2 with ⟨r', yr', hr'⟩
  have : Metric.eball (0 : E) r' ∈ 𝓝 y := IsOpen.mem_nhds Metric.isOpen_eball yr'
  refine ⟨(x + ·)⁻¹' (insert x s) ∩ Metric.eball (0 : E) r', ?_, ?_⟩
  · rw [nhdsWithin_inter_of_mem']
    · exact inter_mem_nhdsWithin _ this
    · apply mem_nhdsWithin_of_mem_nhds
      apply Filter.mem_of_superset this (Metric.eball_subset_eball hr'.le)
  · simpa [Metric.eball_coe] using hf.tendstoUniformlyOn hr' u hu

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the partial sums of this power series on the disk of convergence, i.e., `f (x + y)`
is the locally uniform limit of `p.partialSum n y` there. -/
/-
**HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn (hf : HasFPowerSeriesOnBal
l f p x r) : TendstoLocallyUniformlyOn (fun n y => p.partialSum n y) (fun y => f
 (x + y)) atTop (Metric.eball (0 : E) r)
参数：hf : HasFPowerSeriesOnBall f p x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn`：HasFPowerSeriesWi
thinOnBall.tendstoLocallyUniformlyOn (hf : HasFPowerSeriesWithinOnBall f p s x r
) : TendstoLocallyUniformlyOn (fun n y => p…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …

--- 原说明 ---
If a function admits a power series expansion at `x`, then it is the locally uni
form limit of
the partial sums of this power series on the disk of convergence, i.e., `f (x + 
y)`
is the locally uniform limit of `p.partialSum n y` there.
-/
theorem HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn (hf : HasFPowerSeriesOnBall f p x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      (Metric.eball (0 : E) r) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoLocallyUniformlyOn

/-- If a function admits a power series expansion within a set at `x`, then it is the uniform limit
of the partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f y`
is the uniform limit of `p.partialSum n (y - x)` there. -/
/-
**HasFPowerSeriesWithinOnBall.tendstoUniformlyOn'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.tendstoUniformlyOn' {r' : Real>=0} (hf : HasFP
owerSeriesWithinOnBall f p s x r) (h : (r' : Real>=0∞) < r) : TendstoUniformlyOn
 (fun n y => p.partialSum n (y - x)) f atTop (insert x s inter Metric.ball (x : 
E) r')
参数：hf : HasFPowerSeriesWithinOnBall f p s x r；h : (r' : Real>=0∞) < r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `TendstoUniformlyOn.comp`：TendstoUniformlyOn.comp (h : TendstoUniformlyOn
 F f p s) (g : γ -> α) : TendstoUniformlyOn (fun n => F n ∘ g) (f ∘ g) p (g ⁻¹' 
s)
· 使用定理 `HasFPowerSeriesWithinOnBall.tendstoUniformlyOn`：HasFPowerSeriesWithinOnB
all.tendstoUniformlyOn {r' : Real>=0} (hf : HasFPowerSeriesWithinOnBall f p s x 
r) (h : (r' : Real>=0∞) < r) : Tends…

--- 原说明 ---
If a function admits a power series expansion within a set at `x`, then it is th
e uniform limit
of the partial sums of this power series on strict subdisks of the disk of conve
rgence, i.e., `f y`
is the uniform limit of `p.partialSum n (y - x)` there.
-/
theorem HasFPowerSeriesWithinOnBall.tendstoUniformlyOn' {r' : ℝ≥0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop
      (insert x s ∩ Metric.ball (x : E) r') := by
  convert! (hf.tendstoUniformlyOn h).comp fun y => y - x using 1
  · simp [Function.comp_def]
  · ext z
    simp [dist_eq_norm]

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f y`
is the uniform limit of `p.partialSum n (y - x)` there. -/
/-
**HasFPowerSeriesOnBall.tendstoUniformlyOn'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.tendstoUniformlyOn' {r' : Real>=0} (hf : HasFPowerSe
riesOnBall f p x r) (h : (r' : Real>=0∞) < r) : TendstoUniformlyOn (fun n y => p
.partialSum n (y - x)) f atTop (Metric.ball (x : E) r')
参数：hf : HasFPowerSeriesOnBall f p x r；h : (r' : Real>=0∞) < r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `HasFPowerSeriesWithinOnBall.tendstoUniformlyOn'`：HasFPowerSeriesWithinOn
Ball.tendstoUniformlyOn' {r' : Real>=0} (hf : HasFPowerSeriesWithinOnBall f p s 
x r) (h : (r' : Real>=0∞) < r) : Tend…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …

--- 原说明 ---
If a function admits a power series expansion at `x`, then it is the uniform lim
it of the
partial sums of this power series on strict subdisks of the disk of convergence,
 i.e., `f y`
is the uniform limit of `p.partialSum n (y - x)` there.
-/
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn' {r' : ℝ≥0} (hf : HasFPowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop (Metric.ball (x : E) r') := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn' h

/-- If a function admits a power series expansion within a set at `x`, then it is the locally
uniform limit of the partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partialSum n (y - x)` there. -/
/-
**HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn'** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn' (hf : HasFPowerSeri
esWithinOnBall f p s x r) : TendstoLocallyUniformlyOn (fun n y => p.partialSum n
 (y - x)) f atTop (insert x s inter Metric.eball (x : E) r)
参数：hf : HasFPowerSeriesWithinOnBall f p s x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `ContinuousOn.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TendstoLocallyUniformlyOn.comp`：TendstoLocallyUniformlyOn.comp [Topologi
calSpace γ] {t : Set γ} (h : TendstoLocallyUniformlyOn F f p s) (g : γ -> α) (hg
 : MapsTo g t s) (cg…
· 使用定理 `HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn`：HasFPowerSeriesWi
thinOnBall.tendstoLocallyUniformlyOn (hf : HasFPowerSeriesWithinOnBall f p s x r
) : TendstoLocallyUniformlyOn (fun n y => p…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a

--- 原说明 ---
If a function admits a power series expansion within a set at `x`, then it is th
e locally
uniform limit of the partial sums of this power series on the disk of convergenc
e, i.e., `f y`
is the locally uniform limit of `p.partialSum n (y - x)` there.
-/
theorem HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn'
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop
      (insert x s ∩ Metric.eball (x : E) r) := by
  have A : ContinuousOn (fun y : E => y - x) (insert x s ∩ Metric.eball (x : E) r) := by fun_prop
  convert! hf.tendstoLocallyUniformlyOn.comp (fun y : E => y - x) _ A using 1
  · ext z
    simp
  · intro z
    simp [edist_eq_enorm_sub]

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partialSum n (y - x)` there. -/
/-
**HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn' (hf : HasFPowerSeriesOnBa
ll f p x r) : TendstoLocallyUniformlyOn (fun n y => p.partialSum n (y - x)) f at
Top (Metric.eball (x : E) r)
参数：hf : HasFPowerSeriesOnBall f p x r。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn'`：HasFPowerSeriesW
ithinOnBall.tendstoLocallyUniformlyOn' (hf : HasFPowerSeriesWithinOnBall f p s x
 r) : TendstoLocallyUniformlyOn (fun n y => …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …

--- 原说明 ---
If a function admits a power series expansion at `x`, then it is the locally uni
form limit of
the partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partialSum n (y - x)` there.
-/
theorem HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn' (hf : HasFPowerSeriesOnBall f p x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop
      (Metric.eball (x : E) r) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoLocallyUniformlyOn'

/-- If a function admits a power series expansion within a set on a ball, then it is
continuous there. -/
/-
**HasFPowerSeriesWithinOnBall.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerS
eriesWithinOnBall`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {s : Set E} {x : E} {r : ENNReal},   HasFPowerSeriesWithinOnBa
ll f p s x r → ContinuousOn f (insert x s ∩ Metric.eball x r)
参数：insert x s ∩ Metric.eball x r。
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
· 使用定理 `TendstoLocallyUniformlyOn.continuousOn`：∀ {α : Type u_1} {β : Type u_2} 
{ι : Type u_3} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : ι → α 
→ β}   {f : α → β} {s : Set …
· 使用定理 `HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn'`：HasFPowerSeriesW
ithinOnBall.tendstoLocallyUniformlyOn' (hf : HasFPowerSeriesWithinOnBall f p s x
 r) : TendstoLocallyUniformlyOn (fun n y => …
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `FormalMultilinearSeries.partialSum_continuous`：partialSum_continuous (p 
: FormalMultilinearSeries 𝕜 E F) (n : Nat) : Continuous (p.partialSum n)
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
If a function admits a power series expansion within a set on a ball, then it is
continuous there.
-/
protected theorem HasFPowerSeriesWithinOnBall.continuousOn
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    ContinuousOn f (insert x s ∩ Metric.eball x r) :=
  hf.tendstoLocallyUniformlyOn'.continuousOn <|
    Frequently.of_forall fun n =>
      ((p.partialSum_continuous n).comp (continuous_id.sub continuous_const)).continuousOn

/-- If a function admits a power series expansion on a ball, then it is continuous there. -/
/-
**HasFPowerSeriesOnBall.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerSeriesO
nBall`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {x : E} {r : ENNReal},   HasFPowerSeriesOnBall f p x r → Conti
nuousOn f (Metric.eball x r)
参数：Metric.eball x r。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `HasFPowerSeriesWithinOnBall.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2
} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup
 E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinOnBall_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …

--- 原说明 ---
If a function admits a power series expansion on a ball, then it is continuous t
here.
-/
protected theorem HasFPowerSeriesOnBall.continuousOn (hf : HasFPowerSeriesOnBall f p x r) :
    ContinuousOn f (Metric.eball x r) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.continuousOn
/-
**HasFPowerSeriesWithinOnBall.continuousWithinAt_insert** 是 Mathlib 中的一个定理，位于命名空
间 `HasFPowerSeriesWithinOnBall`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {s : Set E} {x : E} {r : ENNReal},   HasFPowerSeriesWithinOnBa
ll f p s x r → ContinuousWithinAt f (insert x s) x
参数：insert x s。
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
· 使用定理 `ContinuousWithinAt.mono_of_mem_nhdsWithin`：ContinuousWithinAt.mono_of_me
m_nhdsWithin (h : ContinuousWithinAt f t x) (hs : t in 𝓝[s] x) : ContinuousWithi
nAt f s x
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用定理 `HasFPowerSeriesWithinOnBall.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2
} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup
 E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
-/
protected theorem HasFPowerSeriesWithinOnBall.continuousWithinAt_insert
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    ContinuousWithinAt f (insert x s) x := by
  apply (hf.continuousOn.continuousWithinAt (x := x) (by simp [hf.r_pos])).mono_of_mem_nhdsWithin
  exact inter_mem_nhdsWithin _ (Metric.eball_mem_nhds x hf.r_pos)
/-
**HasFPowerSeriesWithinOnBall.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `HasF
PowerSeriesWithinOnBall`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {s : Set E} {x : E} {r : ENNReal},   HasFPowerSeriesWithinOnBa
ll f p s x r → ContinuousWithinAt f s x
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
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `HasFPowerSeriesWithinOnBall.continuousWithinAt_insert`：∀ {𝕜 : Type u_1} 
{E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : Norme
dAddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
protected theorem HasFPowerSeriesWithinOnBall.continuousWithinAt
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    ContinuousWithinAt f s x :=
  hf.continuousWithinAt_insert.mono (subset_insert x s)
/-
**HasFPowerSeriesWithinAt.continuousWithinAt_insert** 是 Mathlib 中的一个定理，位于命名空间 `H
asFPowerSeriesWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {s : Set E} {x : E},   HasFPowerSeriesWithinAt f p s x → Conti
nuousWithinAt f (insert x s) x
参数：insert x s。
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
· 使用定理 `HasFPowerSeriesWithinOnBall.continuousWithinAt_insert`：∀ {𝕜 : Type u_1} 
{E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : Norme
dAddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
-/
protected theorem HasFPowerSeriesWithinAt.continuousWithinAt_insert
    (hf : HasFPowerSeriesWithinAt f p s x) :
    ContinuousWithinAt f (insert x s) x := by
  rcases hf with ⟨r, hr⟩
  apply hr.continuousWithinAt_insert
/-
**HasFPowerSeriesWithinAt.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowe
rSeriesWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {s : Set E} {x : E}, HasFPowerSeriesWithinAt f p s x → Continu
ousWithinAt f s x
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
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `HasFPowerSeriesWithinAt.continuousWithinAt_insert`：∀ {𝕜 : Type u_1} {E :
 Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAdd
CommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
protected theorem HasFPowerSeriesWithinAt.continuousWithinAt
    (hf : HasFPowerSeriesWithinAt f p s x) :
    ContinuousWithinAt f s x :=
  hf.continuousWithinAt_insert.mono (subset_insert x s)
/-
**HasFPowerSeriesAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerSeriesAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {x : E}, HasFPowerSeriesAt f p x → ContinuousAt f x
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
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `HasFPowerSeriesOnBall.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
-/
protected theorem HasFPowerSeriesAt.continuousAt (hf : HasFPowerSeriesAt f p x) :
    ContinuousAt f x :=
  let ⟨_, hr⟩ := hf
  hr.continuousOn.continuousAt (Metric.eball_mem_nhds x hr.r_pos)
/-
**AnalyticWithinAt.continuousWithinAt_insert** 是 Mathlib 中的一个定理，位于命名空间 `Analytic
WithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {s : Set E} {x : E},
   AnalyticWithinAt 𝕜 f s x → ContinuousWithinAt f (insert x s) x
参数：insert x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesWithinAt.continuousWithinAt_insert`：∀ {𝕜 : Type u_1} {E :
 Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAdd
CommGroup E]   [inst_2 : NormedSpace 𝕜 …
-/
protected theorem AnalyticWithinAt.continuousWithinAt_insert (hf : AnalyticWithinAt 𝕜 f s x) :
    ContinuousWithinAt f (insert x s) x :=
  let ⟨_, hp⟩ := hf
  hp.continuousWithinAt_insert
/-
**AnalyticWithinAt.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticWithinA
t`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {s : Set E} {x : E},
   AnalyticWithinAt 𝕜 f s x → ContinuousWithinAt f s x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `AnalyticWithinAt.continuousWithinAt_insert`：∀ {𝕜 : Type u_1} {E : Type u
_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGro
up E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
protected theorem AnalyticWithinAt.continuousWithinAt (hf : AnalyticWithinAt 𝕜 f s x) :
    ContinuousWithinAt f s x :=
  hf.continuousWithinAt_insert.mono (subset_insert x s)

@[fun_prop]
/-
**AnalyticAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {x : E},   AnalyticA
t 𝕜 f x → ContinuousAt f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Typ
e u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [ins
t_2 : NormedSpace 𝕜 …
-/
protected theorem AnalyticAt.continuousAt (hf : AnalyticAt 𝕜 f x) : ContinuousAt f x :=
  let ⟨_, hp⟩ := hf
  hp.continuousAt
/-
**AnalyticAt.eventually_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {x : E},   AnalyticA
t 𝕜 f x → ∀ᶠ (y : E) in nhds x, ContinuousAt f y
参数：y : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `HasFPowerSeriesOnBall.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_eball`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x : α
} {ε : ENNReal}, IsOpen (Metric.eball x ε)
-/
protected theorem AnalyticAt.eventually_continuousAt (hf : AnalyticAt 𝕜 f x) :
    ∀ᶠ y in 𝓝 x, ContinuousAt f y := by
  rcases hf with ⟨g, r, hg⟩
  have : Metric.eball x r ∈ 𝓝 x := Metric.eball_mem_nhds _ hg.r_pos
  filter_upwards [this] with y hy
  apply hg.continuousOn.continuousAt
  exact Metric.isOpen_eball.mem_nhds hy
/-
**AnalyticOnNhd.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticOnNhd`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {s : Set E},   Analy
ticOnNhd 𝕜 f s → ContinuousOn f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
-/
protected theorem AnalyticOnNhd.continuousOn {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) :
    ContinuousOn f s :=
  fun x hx => (hf x hx).continuousAt.continuousWithinAt
/-
**AnalyticOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticOn`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {s : Set E},   Analy
ticOn 𝕜 f s → ContinuousOn f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.continuousWithinAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F 
: Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]  
 [inst_2 : NormedSpace 𝕜 …
-/
protected lemma AnalyticOn.continuousOn {f : E → F} {s : Set E} (h : AnalyticOn 𝕜 f s) :
    ContinuousOn f s :=
  fun x m ↦ (h x m).continuousWithinAt

/-- Analytic everywhere implies continuous -/
/-
**AnalyticOnNhd.continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.continuous {f : E -> F} (fa : AnalyticOnNhd 𝕜 f univ) : Cont
inuous f
参数：fa : AnalyticOnNhd 𝕜 f univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `AnalyticOnNhd.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …

--- 原说明 ---
Analytic everywhere implies continuous
-/
theorem AnalyticOnNhd.continuous {f : E → F} (fa : AnalyticOnNhd 𝕜 f univ) : Continuous f := by
  rw [← continuousOn_univ]; exact fa.continuousOn

/-- In a complete space, the sum of a converging power series `p` admits `p` as a power series.
This is not totally obvious as we need to check the convergence of the series. -/
/-
**FormalMultilinearSeries.hasFPowerSeriesOnBall** 是 Mathlib 中的一个定理，位于命名空间 `Forma
lMultilinearSeries`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] [CompleteSpace F]   (p : FormalM
ultilinearSeries 𝕜 E F), 0 < p.radius → HasFPowerSeriesOnBall p.sum p 0 p.radius
参数：p : FormalMultilinearSeries 𝕜 E F。
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
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `FormalMultilinearSeries.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_3} {F : Typ
e u_4} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [ins
t_2 : NormedSpace 𝕜 …

--- 原说明 ---
In a complete space, the sum of a converging power series `p` admits `p` as a po
wer series.
This is not totally obvious as we need to check the convergence of the series.
-/
protected theorem FormalMultilinearSeries.hasFPowerSeriesOnBall [CompleteSpace F]
    (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) :
    HasFPowerSeriesOnBall p.sum p 0 p.radius :=
  { r_le := le_rfl
    r_pos := h
    hasSum := fun hy => by
      rw [zero_add]
      exact p.hasSum hy }
/-
**HasFPowerSeriesWithinOnBall.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.sum (h : HasFPowerSeriesWithinOnBall f p s x r
) {y : E} (h'y : x + y in insert x s) (hy : y in Metric.eball (0 : E) r) : f (x 
+ y) = p.sum y
参数：h : HasFPowerSeriesWithinOnBall f p s x r；h'y : x + y in insert x s；hy : y in
 Metric.eball (0 : E) r。
该定理/引理给出了一组等式。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesWithinOnBall.sum (h : HasFPowerSeriesWithinOnBall f p s x r) {y : E}
    (h'y : x + y ∈ insert x s) (hy : y ∈ Metric.eball (0 : E) r) : f (x + y) = p.sum y :=
  (h.hasSum h'y hy).tsum_eq.symm
/-
**HasFPowerSeriesOnBall.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.sum (h : HasFPowerSeriesOnBall f p x r) {y : E} (hy 
: y in Metric.eball (0 : E) r) : f (x + y) = p.sum y
参数：h : HasFPowerSeriesOnBall f p x r；hy : y in Metric.eball (0 : E) r。
该定理/引理给出了一组等式。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesOnBall.sum (h : HasFPowerSeriesOnBall f p x r) {y : E}
    (hy : y ∈ Metric.eball (0 : E) r) : f (x + y) = p.sum y :=
  (h.hasSum hy).tsum_eq.symm

/-- The sum of a converging power series is continuous in its disk of convergence. -/
/-
**FormalMultilinearSeries.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilin
earSeries`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   {p : FormalMultilinearSeries 𝕜
 E F} [CompleteSpace F], ContinuousOn p.sum (Metric.eball 0 p.radius)
参数：Metric.eball 0 p.radius。
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
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.eball_zero`：eball_zero : eball x 0 = ∅
· 使用定理 `HasFPowerSeriesOnBall.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `FormalMultilinearSeries.hasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E : Typ
e u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddComm
Group E]   [inst_2 : NormedSpace 𝕜 …

--- 原说明 ---
The sum of a converging power series is continuous in its disk of convergence.
-/
protected theorem FormalMultilinearSeries.continuousOn [CompleteSpace F] :
    ContinuousOn p.sum (Metric.eball 0 p.radius) := by
  rcases eq_zero_or_pos p.radius with h | h
  · simp [h, continuousOn_empty]
  · exact (p.hasFPowerSeriesOnBall h).continuousOn

end

section

open FormalMultilinearSeries

variable {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E} {z₀ : 𝕜}

/-- A function `f : 𝕜 → E` has `p` as power series expansion at a point `z₀` iff it is the sum of
`p` in a neighborhood of `z₀`. This makes some proofs easier by hiding the fact that
`HasFPowerSeriesAt` depends on `p.radius`. -/
/-
**hasFPowerSeriesAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesAt_iff : HasFPowerSeriesAt f p z₀ ↔ forallᶠ z in 𝓝 0, HasSu
m (fun n => z ^ n • p.coeff n) (f (z₀ + z))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `NormedField.exists_norm_lt`：exists_norm_lt {r : Real} (hr : 0 < r) : exi
sts x : α, 0 < ‖x‖ ∧ ‖x‖ < r
· 使用定理 `FormalMultilinearSeries.le_radius_of_tendsto`：le_radius_of_tendsto (p : 
FormalMultilinearSeries 𝕜 E F) {l : Real} (h : Tendsto (fun n => ‖p n‖ * (r : Re
al) ^ n) atTop (𝓝 l)) : ↑r <= p.ra…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
A function `f : 𝕜 → E` has `p` as power series expansion at a point `z₀` iff it 
is the sum of
`p` in a neighborhood of `z₀`. This makes some proofs easier by hiding the fact 
that
`HasFPowerSeriesAt` depends on `p.radius`.
-/
theorem hasFPowerSeriesAt_iff :
    HasFPowerSeriesAt f p z₀ ↔ ∀ᶠ z in 𝓝 0, HasSum (fun n => z ^ n • p.coeff n) (f (z₀ + z)) := by
  refine ⟨fun ⟨r, _, r_pos, h⟩ =>
    eventually_of_mem (Metric.eball_mem_nhds 0 r_pos) fun _ => by simpa using h, ?_⟩
  simp only [Metric.eventually_nhds_iff]
  rintro ⟨r, r_pos, h⟩
  refine ⟨p.radius ⊓ r.toNNReal, by simp, ?_, ?_⟩
  · simp only [r_pos.lt, lt_inf_iff, ENNReal.coe_pos, Real.toNNReal_pos, and_true]
    obtain ⟨z, z_pos, le_z⟩ := NormedField.exists_norm_lt 𝕜 r_pos.lt
    have : (‖z‖₊ : ENNReal) ≤ p.radius := by
      simp only [dist_zero_right] at h
      apply FormalMultilinearSeries.le_radius_of_tendsto
      convert! tendsto_norm.comp (h le_z).summable.tendsto_atTop_zero
      simp [norm_smul, mul_comm]
    refine lt_of_lt_of_le ?_ this
    simp only [ENNReal.coe_pos]
    exact zero_lt_iff.mpr (nnnorm_ne_zero_iff.mpr (norm_pos_iff.mp z_pos))
  · simp only [Metric.mem_eball, lt_inf_iff, edist_lt_coe, apply_eq_pow_smul_coeff, and_imp,
      dist_zero_right] at h ⊢
    refine fun {y} _ hyr => h ?_
    simpa [nndist_eq_nnnorm, Real.lt_toNNReal_iff_coe_lt] using hyr
/-
**hasFPowerSeriesAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesAt_iff' : HasFPowerSeriesAt f p z₀ ↔ forallᶠ z in 𝓝 z₀, Has
Sum (fun n => (z - z₀) ^ n • p.coeff n) (f z)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add_left_nhds_zero`：∀ {G : Type w} [inst : TopologicalSpace G] [inst
_1 : AddGroup G] [IsTopologicalAddGroup G] (x : G),   Filter.map (fun x_1 => x +
 x_1) (nhds …
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `hasFPowerSeriesAt_iff`：hasFPowerSeriesAt_iff : HasFPowerSeriesAt f p z₀ 
↔ forallᶠ z in 𝓝 0, HasSum (fun n => z ^ n • p.coeff n) (f (z₀ + z))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFPowerSeriesAt_iff' :
    HasFPowerSeriesAt f p z₀ ↔ ∀ᶠ z in 𝓝 z₀, HasSum (fun n => (z - z₀) ^ n • p.coeff n) (f z) := by
  rw [← map_add_left_nhds_zero, eventually_map, hasFPowerSeriesAt_iff]
  simp_rw [add_sub_cancel_left]

end

