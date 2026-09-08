/-
Copyright (c) 2023 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Analysis.Analytic.ChangeOrigin

/-! We specialize the theory of analytic functions to the case of functions that admit a
development given by a *finite* formal multilinear series. We call them "continuously polynomial",
which is abbreviated to `CPolynomial`. One reason to do that is that we no longer need a
completeness assumption on the target space `F` to make the series converge, so some of the results
are more general. The class of continuously polynomial functions includes functions defined by
polynomials on a normed `𝕜`-algebra and continuous multilinear maps.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`, and let `f` be a function from `E` to `F`.

* `HasFiniteFPowerSeriesOnBall f p x n r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₘ yᵐ`, and moreover `pₘ = 0` if `n ≤ m`.
* `HasFiniteFPowerSeriesAt f p x n`: on some ball of center `x` with positive radius, holds
  `HasFiniteFPowerSeriesOnBall f p x n r`.
* `CPolynomialAt 𝕜 f x`: there exists a power series `p` and a natural number `n` such that
  holds `HasFPowerSeriesAt f p x n`.
* `CPolynomialOn 𝕜 f s`: the function `f` is analytic at every point of `s`.

In this file, we develop the basic properties of these notions, notably:
* If a function is continuously polynomial, then it is analytic, see
  `HasFiniteFPowerSeriesOnBall.hasFPowerSeriesOnBall`, `HasFiniteFPowerSeriesAt.hasFPowerSeriesAt`,
  `CPolynomialAt.analyticAt` and `CPolynomialOn.analyticOnNhd`.
* The sum of a finite formal power series with positive radius is well defined on the whole space,
  see `FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite`.
* If a function admits a finite power series in a ball, then it is continuously polynomial at
  any point `y` of this ball, and the power series there can be expressed in terms of the initial
  power series `p` as `p.changeOrigin y`, which is finite (with the same bound as `p`) by
  `changeOrigin_finite_of_finite`. See `HasFiniteFPowerSeriesOnBall.changeOrigin`. It follows in
  particular that the set of points at which a given function is continuously polynomial is open,
  see `isOpen_cpolynomialAt`.

More API is available in the file `Mathlib/Analysis/Analytic/CPolynomial.lean`, with heavier
imports.
-/

@[expose] public section

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open scoped Topology
open Set Filter Asymptotics NNReal ENNReal

variable {f g : E → F} {p pf pg : FormalMultilinearSeries 𝕜 E F} {x : E} {r r' : ℝ≥0∞} {n m : ℕ}

section FiniteFPowerSeries

/-- Given a function `f : E → F`, a formal multilinear series `p` and `n : ℕ`, we say that
`f` has `p` as a finite power series on the ball of radius `r > 0` around `x` if
`f (x + y) = ∑' pₘ yᵐ` for all `‖y‖ < r` and `pₙ = 0` for `n ≤ m`. -/
/-
**HasFiniteFPowerSeriesOnBall** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField 𝕜] →         [inst_1 : NormedAddCommGroup E] →           [i
nst_2 : NormedSpace 𝕜 E] →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] → (E → F) → FormalMultilinearSeries 𝕜 E F → E 
→ ℕ → ENNReal → Prop
参数：E → F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : E → F`, a formal multilinear series `p` and `n : ℕ`, we sa
y that
`f` has `p` as a finite power series on the ball of radius `r > 0` around `x` if
`f (x + y) = ∑' pₘ yᵐ` for all `‖y‖ < r` and `pₙ = 0` for `n ≤ m`.
-/
structure HasFiniteFPowerSeriesOnBall (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E)
    (n : ℕ) (r : ℝ≥0∞) : Prop extends HasFPowerSeriesOnBall f p x r where
  finite : ∀ (m : ℕ), n ≤ m → p m = 0
/-
**HasFiniteFPowerSeriesOnBall.mk'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.mk' {f : E -> F} {p : FormalMultilinearSeries 
𝕜 E F} {x : E} {n : Nat} {r : Real>=0∞} (finite : forall (m : Nat), n <= m -> p 
m = 0) (pos : 0 < r) (sum_eq : forall y in Metric.eball 0 r, (∑ i in Finset.rang
e n, p i fun _ => y) = f (x + y)) : HasFiniteFPowerSeriesOnBall f p x n r where 
r_le
参数：finite : forall (m : Nat), n <= m -> p m = 0；pos : 0 < r；sum_eq : forall y in
 Metric.eball 0 r, (∑ i in Finset.range n, p i fun _ => y) = f (x + y)。
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
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero`：radius_eq_t
op_of_eventually_eq_zero (h : forallᶠ n in atTop, p n = 0) : p.radius = ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `hasSum_sum_of_ne_finset_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α} {s : Finset β},…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
theorem HasFiniteFPowerSeriesOnBall.mk' {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    {n : ℕ} {r : ℝ≥0∞} (finite : ∀ (m : ℕ), n ≤ m → p m = 0) (pos : 0 < r)
    (sum_eq : ∀ y ∈ Metric.eball 0 r, (∑ i ∈ Finset.range n, p i fun _ ↦ y) = f (x + y)) :
    HasFiniteFPowerSeriesOnBall f p x n r where
  r_le := p.radius_eq_top_of_eventually_eq_zero (Filter.eventually_atTop.mpr ⟨n, finite⟩) ▸ le_top
  r_pos := pos
  hasSum hy := sum_eq _ hy ▸ hasSum_sum_of_ne_finset_zero fun m hm ↦ by
    rw [Finset.mem_range, not_lt] at hm; rw [finite m hm]; rfl
  finite := finite

/-- Given a function `f : E → F`, a formal multilinear series `p` and `n : ℕ`, we say that
`f` has `p` as a finite power series around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `y` in a
neighborhood of `0` and `pₙ = 0` for `n ≤ m`. -/
/-
**HasFiniteFPowerSeriesAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesAt (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (
x : E) (n : Nat)
参数：f : E -> F；p : FormalMultilinearSeries 𝕜 E F；x : E；n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : E → F`, a formal multilinear series `p` and `n : ℕ`, we sa
y that
`f` has `p` as a finite power series around `x` if `f (x + y) = ∑' pₙ yⁿ` for al
l `y` in a
neighborhood of `0` and `pₙ = 0` for `n ≤ m`.
-/
def HasFiniteFPowerSeriesAt (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (n : ℕ) :=
  ∃ r, HasFiniteFPowerSeriesOnBall f p x n r
/-
**HasFiniteFPowerSeriesAt.hasFPowerSeriesAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesAt.hasFPowerSeriesAt (hf : HasFiniteFPowerSeriesAt f 
p x n) : HasFPowerSeriesAt f p x
参数：hf : HasFiniteFPowerSeriesAt f p x n。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
-/
theorem HasFiniteFPowerSeriesAt.hasFPowerSeriesAt
    (hf : HasFiniteFPowerSeriesAt f p x n) : HasFPowerSeriesAt f p x :=
  let ⟨r, hf⟩ := hf
  ⟨r, hf.toHasFPowerSeriesOnBall⟩
/-
**HasFiniteFPowerSeriesAt.finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesAt.finite (hf : HasFiniteFPowerSeriesAt f p x n) : fo
rall m : Nat, n <= m -> p m = 0
参数：hf : HasFiniteFPowerSeriesAt f p x n。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.finite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
-/
theorem HasFiniteFPowerSeriesAt.finite (hf : HasFiniteFPowerSeriesAt f p x n) :
    ∀ m : ℕ, n ≤ m → p m = 0 := let ⟨_, hf⟩ := hf; hf.finite

variable (𝕜)

/-- Given a function `f : E → F`, we say that `f` is continuously polynomial (cpolynomial)
at `x` if it admits a finite power series expansion around `x`. -/
/-
**CPolynomialAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CPolynomialAt (f : E -> F) (x : E)
参数：f : E -> F；x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : E → F`, we say that `f` is continuously polynomial (cpolyn
omial)
at `x` if it admits a finite power series expansion around `x`.
-/
def CPolynomialAt (f : E → F) (x : E) :=
  ∃ (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ), HasFiniteFPowerSeriesAt f p x n

/-- Given a function `f : E → F`, we say that `f` is continuously polynomial on a set `s`
if it is continuously polynomial around every point of `s`. -/
/-
**CPolynomialOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CPolynomialOn (f : E -> F) (s : Set E)
参数：f : E -> F；s : Set E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : E → F`, we say that `f` is continuously polynomial on a se
t `s`
if it is continuously polynomial around every point of `s`.
-/
def CPolynomialOn (f : E → F) (s : Set E) :=
  ∀ x, x ∈ s → CPolynomialAt 𝕜 f x

variable {𝕜}
/-
**HasFiniteFPowerSeriesOnBall.hasFiniteFPowerSeriesAt** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：HasFiniteFPowerSeriesOnBall.hasFiniteFPowerSeriesAt (hf : HasFiniteFPowerS
eriesOnBall f p x n r) : HasFiniteFPowerSeriesAt f p x n
参数：hf : HasFiniteFPowerSeriesOnBall f p x n r。
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
theorem HasFiniteFPowerSeriesOnBall.hasFiniteFPowerSeriesAt
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    HasFiniteFPowerSeriesAt f p x n :=
  ⟨r, hf⟩
/-
**HasFiniteFPowerSeriesAt.cpolynomialAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesAt.cpolynomialAt (hf : HasFiniteFPowerSeriesAt f p x 
n) : CPolynomialAt 𝕜 f x
参数：hf : HasFiniteFPowerSeriesAt f p x n。
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
theorem HasFiniteFPowerSeriesAt.cpolynomialAt (hf : HasFiniteFPowerSeriesAt f p x n) :
    CPolynomialAt 𝕜 f x :=
  ⟨p, n, hf⟩
/-
**HasFiniteFPowerSeriesOnBall.cpolynomialAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.cpolynomialAt (hf : HasFiniteFPowerSeriesOnBal
l f p x n r) : CPolynomialAt 𝕜 f x
参数：hf : HasFiniteFPowerSeriesOnBall f p x n r。
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
· 使用定理 `HasFiniteFPowerSeriesAt.cpolynomialAt`：HasFiniteFPowerSeriesAt.cpolynomi
alAt (hf : HasFiniteFPowerSeriesAt f p x n) : CPolynomialAt 𝕜 f x
· 使用定理 `HasFiniteFPowerSeriesOnBall.hasFiniteFPowerSeriesAt`：HasFiniteFPowerSeri
esOnBall.hasFiniteFPowerSeriesAt (hf : HasFiniteFPowerSeriesOnBall f p x n r) : 
HasFiniteFPowerSeriesAt f p x n
-/
theorem HasFiniteFPowerSeriesOnBall.cpolynomialAt (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    CPolynomialAt 𝕜 f x :=
  hf.hasFiniteFPowerSeriesAt.cpolynomialAt
/-
**CPolynomialAt.analyticAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt.analyticAt (hf : CPolynomialAt 𝕜 f x) : AnalyticAt 𝕜 f x
参数：hf : CPolynomialAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFiniteFPowerSeriesAt.hasFPowerSeriesAt`：HasFiniteFPowerSeriesAt.hasFP
owerSeriesAt (hf : HasFiniteFPowerSeriesAt f p x n) : HasFPowerSeriesAt f p x
-/
theorem CPolynomialAt.analyticAt (hf : CPolynomialAt 𝕜 f x) : AnalyticAt 𝕜 f x :=
  let ⟨p, _, hp⟩ := hf
  ⟨p, hp.hasFPowerSeriesAt⟩
/-
**CPolynomialAt.analyticWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt.analyticWithinAt {s : Set E} (hf : CPolynomialAt 𝕜 f x) : An
alyticWithinAt 𝕜 f s x
参数：hf : CPolynomialAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `CPolynomialAt.analyticAt`：CPolynomialAt.analyticAt (hf : CPolynomialAt 𝕜
 f x) : AnalyticAt 𝕜 f x
-/
theorem CPolynomialAt.analyticWithinAt {s : Set E} (hf : CPolynomialAt 𝕜 f x) :
    AnalyticWithinAt 𝕜 f s x :=
  hf.analyticAt.analyticWithinAt
/-
**CPolynomialOn.analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.analyticOnNhd {s : Set E} (hf : CPolynomialOn 𝕜 f s) : Analy
ticOnNhd 𝕜 f s
参数：hf : CPolynomialOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialAt.analyticAt`：CPolynomialAt.analyticAt (hf : CPolynomialAt 𝕜
 f x) : AnalyticAt 𝕜 f x
-/
theorem CPolynomialOn.analyticOnNhd {s : Set E} (hf : CPolynomialOn 𝕜 f s) : AnalyticOnNhd 𝕜 f s :=
  fun x hx ↦ (hf x hx).analyticAt
/-
**CPolynomialOn.analyticOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.analyticOn {s : Set E} (hf : CPolynomialOn 𝕜 f s) : Analytic
On 𝕜 f s
参数：hf : CPolynomialOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用定理 `CPolynomialOn.analyticOnNhd`：CPolynomialOn.analyticOnNhd {s : Set E} (hf
 : CPolynomialOn 𝕜 f s) : AnalyticOnNhd 𝕜 f s
-/
theorem CPolynomialOn.analyticOn {s : Set E} (hf : CPolynomialOn 𝕜 f s) : AnalyticOn 𝕜 f s :=
  hf.analyticOnNhd.analyticOn
/-
**HasFiniteFPowerSeriesOnBall.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.congr (hf : HasFiniteFPowerSeriesOnBall f p x 
n r) (hg : EqOn f g (Metric.eball x r)) : HasFiniteFPowerSeriesOnBall g p x n r
参数：hf : HasFiniteFPowerSeriesOnBall f p x n r；hg : EqOn f g (Metric.eball x r)。
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
· 使用定理 `HasFPowerSeriesOnBall.congr`：HasFPowerSeriesOnBall.congr (hf : HasFPower
SeriesOnBall f p x r) (hg : EqOn f g (Metric.eball x r)) : HasFPowerSeriesOnBall
 g p x r
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.finite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
-/
theorem HasFiniteFPowerSeriesOnBall.congr (hf : HasFiniteFPowerSeriesOnBall f p x n r)
    (hg : EqOn f g (Metric.eball x r)) : HasFiniteFPowerSeriesOnBall g p x n r :=
  ⟨hf.1.congr hg, hf.finite⟩
/-
**HasFiniteFPowerSeriesOnBall.of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.of_le {m n : Nat} (h : HasFiniteFPowerSeriesOn
Ball f p x n r) (hmn : n <= m) : HasFiniteFPowerSeriesOnBall f p x m r
参数：h : HasFiniteFPowerSeriesOnBall f p x n r；hmn : n <= m。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.finite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem HasFiniteFPowerSeriesOnBall.of_le {m n : ℕ}
    (h : HasFiniteFPowerSeriesOnBall f p x n r) (hmn : n ≤ m) :
    HasFiniteFPowerSeriesOnBall f p x m r :=
  ⟨h.toHasFPowerSeriesOnBall, fun i hi ↦ h.finite i (hmn.trans hi)⟩
/-
**HasFiniteFPowerSeriesAt.of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesAt.of_le {m n : Nat} (h : HasFiniteFPowerSeriesAt f p
 x n) (hmn : n <= m) : HasFiniteFPowerSeriesAt f p x m
参数：h : HasFiniteFPowerSeriesAt f p x n；hmn : n <= m。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.of_le`：HasFiniteFPowerSeriesOnBall.of_le {m 
n : Nat} (h : HasFiniteFPowerSeriesOnBall f p x n r) (hmn : n <= m) : HasFiniteF
PowerSeriesOnBall f p x…
-/
theorem HasFiniteFPowerSeriesAt.of_le {m n : ℕ}
    (h : HasFiniteFPowerSeriesAt f p x n) (hmn : n ≤ m) :
    HasFiniteFPowerSeriesAt f p x m := by
  rcases h with ⟨r, hr⟩
  exact ⟨r, hr.of_le hmn⟩

/-- If a function `f` has a finite power series `p` around `x`, then the function
`z ↦ f (z - y)` has the same finite power series around `x + y`. -/
/-
**HasFiniteFPowerSeriesOnBall.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.comp_sub (hf : HasFiniteFPowerSeriesOnBall f p
 x n r) (y : E) : HasFiniteFPowerSeriesOnBall (fun z => f (z - y)) p (x + y) n r
参数：hf : HasFiniteFPowerSeriesOnBall f p x n r；y : E。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.finite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …

--- 原说明 ---
If a function `f` has a finite power series `p` around `x`, then the function
`z ↦ f (z - y)` has the same finite power series around `x + y`.
-/
theorem HasFiniteFPowerSeriesOnBall.comp_sub (hf : HasFiniteFPowerSeriesOnBall f p x n r) (y : E) :
    HasFiniteFPowerSeriesOnBall (fun z => f (z - y)) p (x + y) n r :=
  ⟨hf.1.comp_sub y, hf.finite⟩
/-
**HasFiniteFPowerSeriesOnBall.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.mono (hf : HasFiniteFPowerSeriesOnBall f p x n
 r) (r'_pos : 0 < r') (hr : r' <= r) : HasFiniteFPowerSeriesOnBall f p x n r'
参数：hf : HasFiniteFPowerSeriesOnBall f p x n r；r'_pos : 0 < r'；hr : r' <= r。
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
· 使用定理 `HasFPowerSeriesOnBall.mono`：HasFPowerSeriesOnBall.mono (hf : HasFPowerSe
riesOnBall f p x r) (r'_pos : 0 < r') (hr : r' <= r) : HasFPowerSeriesOnBall f p
 x r'
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.finite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
-/
theorem HasFiniteFPowerSeriesOnBall.mono (hf : HasFiniteFPowerSeriesOnBall f p x n r)
    (r'_pos : 0 < r') (hr : r' ≤ r) : HasFiniteFPowerSeriesOnBall f p x n r' :=
  ⟨hf.1.mono r'_pos hr, hf.finite⟩
/-
**HasFiniteFPowerSeriesAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesAt.congr (hf : HasFiniteFPowerSeriesAt f p x n) (hg :
 f =ᶠ[𝓝 x] g) : HasFiniteFPowerSeriesAt g p x n
参数：hf : HasFiniteFPowerSeriesAt f p x n；hg : f =ᶠ[𝓝 x] g。
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
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `HasFiniteFPowerSeriesAt.finite`：HasFiniteFPowerSeriesAt.finite (hf : Has
FiniteFPowerSeriesAt f p x n) : forall m : Nat, n <= m -> p m = 0
· 使用定理 `HasFPowerSeriesAt.congr`：HasFPowerSeriesAt.congr (hf : HasFPowerSeriesAt
 f p x) (hg : f =ᶠ[𝓝 x] g) : HasFPowerSeriesAt g p x
· 使用定理 `HasFiniteFPowerSeriesAt.hasFPowerSeriesAt`：HasFiniteFPowerSeriesAt.hasFP
owerSeriesAt (hf : HasFiniteFPowerSeriesAt f p x n) : HasFPowerSeriesAt f p x
-/
theorem HasFiniteFPowerSeriesAt.congr (hf : HasFiniteFPowerSeriesAt f p x n) (hg : f =ᶠ[𝓝 x] g) :
    HasFiniteFPowerSeriesAt g p x n :=
  Exists.imp (fun _ hg ↦ ⟨hg, hf.finite⟩) (hf.hasFPowerSeriesAt.congr hg)
/-
**HasFiniteFPowerSeriesAt.eventually** 是 Mathlib 中的一个定理，位于命名空间 `HasFiniteFPowerS
eriesAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {x : E} {n : ℕ},   HasFiniteFPowerSeriesAt f p x n → ∀ᶠ (r : E
NNReal) in nhdsWithin 0 (Set.Ioi 0), HasFiniteFPowerSeriesOnBall f p x n r
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
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `HasFPowerSeriesAt.eventually`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesAt.hasFPowerSeriesAt`：HasFiniteFPowerSeriesAt.hasFP
owerSeriesAt (hf : HasFiniteFPowerSeriesAt f p x n) : HasFPowerSeriesAt f p x
· 使用定理 `HasFiniteFPowerSeriesAt.finite`：HasFiniteFPowerSeriesAt.finite (hf : Has
FiniteFPowerSeriesAt f p x n) : forall m : Nat, n <= m -> p m = 0
-/
protected theorem HasFiniteFPowerSeriesAt.eventually (hf : HasFiniteFPowerSeriesAt f p x n) :
    ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0, HasFiniteFPowerSeriesOnBall f p x n r :=
  hf.hasFPowerSeriesAt.eventually.mono fun _ h ↦ ⟨h, hf.finite⟩
/-
**CPolynomialAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt.congr (hf : CPolynomialAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g) : CPolyn
omialAt 𝕜 g x
参数：hf : CPolynomialAt 𝕜 f x；hg : f =ᶠ[𝓝 x] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFiniteFPowerSeriesAt.cpolynomialAt`：HasFiniteFPowerSeriesAt.cpolynomi
alAt (hf : HasFiniteFPowerSeriesAt f p x n) : CPolynomialAt 𝕜 f x
· 使用定理 `HasFiniteFPowerSeriesAt.congr`：HasFiniteFPowerSeriesAt.congr (hf : HasFi
niteFPowerSeriesAt f p x n) (hg : f =ᶠ[𝓝 x] g) : HasFiniteFPowerSeriesAt g p x n
-/
theorem CPolynomialAt.congr (hf : CPolynomialAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g) : CPolynomialAt 𝕜 g x :=
  let ⟨_, _, hpf⟩ := hf
  (hpf.congr hg).cpolynomialAt
/-
**CPolynomialAt_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt_congr (h : f =ᶠ[𝓝 x] g) : CPolynomialAt 𝕜 f x ↔ CPolynomialA
t 𝕜 g x
参数：h : f =ᶠ[𝓝 x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialAt.congr`：CPolynomialAt.congr (hf : CPolynomialAt 𝕜 f x) (hg 
: f =ᶠ[𝓝 x] g) : CPolynomialAt 𝕜 g x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem CPolynomialAt_congr (h : f =ᶠ[𝓝 x] g) : CPolynomialAt 𝕜 f x ↔ CPolynomialAt 𝕜 g x :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩
/-
**CPolynomialOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.mono {s t : Set E} (hf : CPolynomialOn 𝕜 f t) (hst : s subse
teq t) : CPolynomialOn 𝕜 f s
参数：hf : CPolynomialOn 𝕜 f t；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem CPolynomialOn.mono {s t : Set E} (hf : CPolynomialOn 𝕜 f t) (hst : s ⊆ t) :
    CPolynomialOn 𝕜 f s :=
  fun z hz => hf z (hst hz)
/-
**CPolynomialOn.congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.congr' {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : f =ᶠ[𝓝ˢ 
s] g) : CPolynomialOn 𝕜 g s
参数：hf : CPolynomialOn 𝕜 f s；hg : f =ᶠ[𝓝ˢ s] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialAt.congr`：CPolynomialAt.congr (hf : CPolynomialAt 𝕜 f x) (hg 
: f =ᶠ[𝓝 x] g) : CPolynomialAt 𝕜 g x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsSet_iff_forall`：mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : 
X, x in t -> s in 𝓝 x
-/
theorem CPolynomialOn.congr' {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g) :
    CPolynomialOn 𝕜 g s :=
  fun z hz => (hf z hz).congr (mem_nhdsSet_iff_forall.mp hg z hz)
/-
**CPolynomialOn_congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn_congr' {s : Set E} (h : f =ᶠ[𝓝ˢ s] g) : CPolynomialOn 𝕜 f s 
↔ CPolynomialOn 𝕜 g s
参数：h : f =ᶠ[𝓝ˢ s] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialOn.congr'`：CPolynomialOn.congr' {s : Set E} (hf : CPolynomial
On 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g) : CPolynomialOn 𝕜 g s
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem CPolynomialOn_congr' {s : Set E} (h : f =ᶠ[𝓝ˢ s] g) :
    CPolynomialOn 𝕜 f s ↔ CPolynomialOn 𝕜 g s :=
  ⟨fun hf => hf.congr' h, fun hg => hg.congr' h.symm⟩
/-
**CPolynomialOn.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.congr {s : Set E} (hs : IsOpen s) (hf : CPolynomialOn 𝕜 f s)
 (hg : s.EqOn f g) : CPolynomialOn 𝕜 g s
参数：hs : IsOpen s；hf : CPolynomialOn 𝕜 f s；hg : s.EqOn f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialOn.congr'`：CPolynomialOn.congr' {s : Set E} (hf : CPolynomial
On 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g) : CPolynomialOn 𝕜 g s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsSet_iff_forall`：mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : 
X, x in t -> s in 𝓝 x
· 使用定理 `Filter.eventuallyEq_iff_exists_mem`：eventuallyEq_iff_exists_mem {l : Fil
ter α} {f g : α -> β} : f =ᶠ[l] g ↔ exists s in l, EqOn f g s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem CPolynomialOn.congr {s : Set E} (hs : IsOpen s) (hf : CPolynomialOn 𝕜 f s)
    (hg : s.EqOn f g) : CPolynomialOn 𝕜 g s :=
  hf.congr' <| mem_nhdsSet_iff_forall.mpr
    (fun _ hz => eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hz, hg⟩)
/-
**CPolynomialOn_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn_congr {s : Set E} (hs : IsOpen s) (h : s.EqOn f g) : CPolyno
mialOn 𝕜 f s ↔ CPolynomialOn 𝕜 g s
参数：hs : IsOpen s；h : s.EqOn f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialOn.congr`：CPolynomialOn.congr {s : Set E} (hs : IsOpen s) (hf
 : CPolynomialOn 𝕜 f s) (hg : s.EqOn f g) : CPolynomialOn 𝕜 g s
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
theorem CPolynomialOn_congr {s : Set E} (hs : IsOpen s) (h : s.EqOn f g) :
    CPolynomialOn 𝕜 f s ↔ CPolynomialOn 𝕜 g s :=
  ⟨fun hf => hf.congr hs h, fun hg => hg.congr hs h.symm⟩

/-- If a function `f` has a finite power series `p` on a ball and `g` is a continuous linear map,
then `g ∘ f` has the finite power series `g ∘ p` on the same ball. -/
/-
**ContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：ContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall (g : F ->L[𝕜] G) (h :
 HasFiniteFPowerSeriesOnBall f p x n r) : HasFiniteFPowerSeriesOnBall (g ∘ f) (g
.compFormalMultilinearSeries p) x n r
参数：g : F ->L[𝕜] G；h : HasFiniteFPowerSeriesOnBall f p x n r。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.compFormalMultilinearSeries_apply`：compFormalMultili
nearSeries_apply (f : F ->L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F) (n : Nat) 
: (f.compFormalMultilinearSeries p) n = f.c…
· 使用定理 `HasFiniteFPowerSeriesOnBall.finite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…

--- 原说明 ---
If a function `f` has a finite power series `p` on a ball and `g` is a continuou
s linear map,
then `g ∘ f` has the finite power series `g ∘ p` on the same ball.
-/
theorem ContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall (g : F →L[𝕜] G)
    (h : HasFiniteFPowerSeriesOnBall f p x n r) :
    HasFiniteFPowerSeriesOnBall (g ∘ f) (g.compFormalMultilinearSeries p) x n r :=
  ⟨g.comp_hasFPowerSeriesOnBall h.1, fun m hm ↦ by
    rw [compFormalMultilinearSeries_apply, h.finite m hm]
    ext; exact map_zero g⟩

/-- If a function `f` is continuously polynomial on a set `s` and `g` is a continuous linear map,
then `g ∘ f` is continuously polynomial on `s`. -/
/-
**ContinuousLinearMap.comp_cpolynomialOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.comp_cpolynomialOn {s : Set E} (g : F ->L[𝕜] G) (h : C
PolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 (g ∘ f) s
参数：g : F ->L[𝕜] G；h : CPolynomialOn 𝕜 f s。
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
· 使用定理 `ContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall`：ContinuousLinearMa
p.comp_hasFiniteFPowerSeriesOnBall (g : F ->L[𝕜] G) (h : HasFiniteFPowerSeriesOn
Ball f p x n r) : HasFiniteFPowerSeriesOnB…

--- 原说明 ---
If a function `f` is continuously polynomial on a set `s` and `g` is a continuou
s linear map,
then `g ∘ f` is continuously polynomial on `s`.
-/
theorem ContinuousLinearMap.comp_cpolynomialOn {s : Set E} (g : F →L[𝕜] G)
    (h : CPolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 (g ∘ f) s := by
  rintro x hx
  rcases h x hx with ⟨p, n, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, n, r, g.comp_hasFiniteFPowerSeriesOnBall hp⟩

/-- If a function admits a finite power series expansion bounded by `n`, then it is equal to
the `m`th partial sums of this power series at every point of the disk for `n ≤ m`. -/
/-
**HasFiniteFPowerSeriesOnBall.eq_partialSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.eq_partialSum (hf : HasFiniteFPowerSeriesOnBal
l f p x n r) : forall y in Metric.eball (0 : E) r, forall m, n <= m -> f (x + y)
 = p.partialSum m y
参数：hf : HasFiniteFPowerSeriesOnBall f p x n r。
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
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `hasSum_sum_of_ne_finset_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α} {s : Finset β},…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFiniteFPowerSeriesOnBall.finite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop

--- 原说明 ---
If a function admits a finite power series expansion bounded by `n`, then it is 
equal to
the `m`th partial sums of this power series at every point of the disk for `n ≤ 
m`.
-/
theorem HasFiniteFPowerSeriesOnBall.eq_partialSum
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    ∀ y ∈ Metric.eball (0 : E) r, ∀ m, n ≤ m →
    f (x + y) = p.partialSum m y :=
  fun y hy m hm ↦ (hf.hasSum hy).unique (hasSum_sum_of_ne_finset_zero
    (f := fun m => p m (fun _ => y)) (s := Finset.range m)
    (fun N hN => by simp only [Finset.mem_range, not_lt] at hN
                    rw [hf.finite _ (le_trans hm hN), zero_apply]))

/-- Variant of the previous result with the variable expressed as `y` instead of `x + y`. -/
/-
**HasFiniteFPowerSeriesOnBall.eq_partialSum'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.eq_partialSum' (hf : HasFiniteFPowerSeriesOnBa
ll f p x n r) : forall y in Metric.eball x r, forall m, n <= m -> f y = p.partia
lSum m (y - x)
参数：hf : HasFiniteFPowerSeriesOnBall f p x n r。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFiniteFPowerSeriesOnBall.eq_partialSum`：HasFiniteFPowerSeriesOnBall.e
q_partialSum (hf : HasFiniteFPowerSeriesOnBall f p x n r) : forall y in Metric.e
ball (0 : E) r, forall m, n <= …
· 使用定理 `mem_eball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : 
E} {r : ENNReal}, a ∈ Metric.eball 0 r ↔ ‖a‖ₑ < r
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `Metric.mem_eball`：∀ {α : Type u} [inst : EDist α] {x y : α} {ε : ENNReal
}, y ∈ Metric.eball x ε ↔ edist y x < ε
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b

--- 原说明 ---
Variant of the previous result with the variable expressed as `y` instead of `x 
+ y`.
-/
theorem HasFiniteFPowerSeriesOnBall.eq_partialSum'
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    ∀ y ∈ Metric.eball x r, ∀ m, n ≤ m →
    f y = p.partialSum m (y - x) := by
  intro y hy m hm
  rw [Metric.mem_eball, edist_eq_enorm_sub, ← mem_eball_zero_iff] at hy
  rw [← (HasFiniteFPowerSeriesOnBall.eq_partialSum hf _ hy m hm), add_sub_cancel]

/-! The particular cases where `f` has a finite power series bounded by `0` or `1`. -/

/-- If `f` has a formal power series on a ball bounded by `0`, then `f` is equal to `0` on
the ball. -/
/-
**HasFiniteFPowerSeriesOnBall.eq_zero_of_bound_zero** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：HasFiniteFPowerSeriesOnBall.eq_zero_of_bound_zero (hf : HasFiniteFPowerSer
iesOnBall f pf x 0 r) : forall y in Metric.eball x r, f y = 0
参数：hf : HasFiniteFPowerSeriesOnBall f pf x 0 r。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.eq_partialSum'`：HasFiniteFPowerSeriesOnBall.
eq_partialSum' (hf : HasFiniteFPowerSeriesOnBall f p x n r) : forall y in Metric
.eball x r, forall m, n <= m -> …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `FormalMultilinearSeries.partialSum.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : AddComm
Monoid F]   [inst_3 : _root_.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` has a formal power series on a ball bounded by `0`, then `f` is equal to 
`0` on
the ball.
-/
theorem HasFiniteFPowerSeriesOnBall.eq_zero_of_bound_zero
    (hf : HasFiniteFPowerSeriesOnBall f pf x 0 r) : ∀ y ∈ Metric.eball x r, f y = 0 := by
  intro y hy
  rw [hf.eq_partialSum' y hy 0 le_rfl, FormalMultilinearSeries.partialSum]
  simp only [Finset.range_zero, Finset.sum_empty]
/-
**HasFiniteFPowerSeriesOnBall.bound_zero_of_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：HasFiniteFPowerSeriesOnBall.bound_zero_of_eq_zero (hf : forall y in Metric
.eball x r, f y = 0) (r_pos : 0 < r) (hp : forall n, p n = 0) : HasFiniteFPowerS
eriesOnBall f p x 0 r
参数：hf : forall y in Metric.eball x r, f y = 0；r_pos : 0 < r；hp : forall n, p n =
 0。
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
· 使用定理 `FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero`：radiu
s_eq_top_of_forall_image_add_eq_zero (n : Nat) (hn : forall m, p (m + n) = 0) : 
p.radius = ∞
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Metric.mem_eball`：∀ {α : Type u} [inst : EDist α] {x y : α} {ε : ENNReal
}, y ∈ Metric.eball x ε ↔ edist y x < ε
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `hasSum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] {L : SummationFilter β},   HasSum (fun x => 0) 0 L
-/
theorem HasFiniteFPowerSeriesOnBall.bound_zero_of_eq_zero (hf : ∀ y ∈ Metric.eball x r, f y = 0)
    (r_pos : 0 < r) (hp : ∀ n, p n = 0) : HasFiniteFPowerSeriesOnBall f p x 0 r := by
  refine ⟨⟨?_, r_pos, ?_⟩, fun n _ ↦ hp n⟩
  · rw [p.radius_eq_top_of_forall_image_add_eq_zero 0 (fun n ↦ by rw [add_zero]; exact hp n)]
    exact le_top
  · intro y hy
    rw [hf (x + y)]
    · convert! hasSum_zero
      rw [hp, zero_apply]
    · rwa [Metric.mem_eball, edist_eq_enorm_sub, add_comm, add_sub_cancel_right,
        ← edist_zero_right, ← Metric.mem_eball]

/-- If `f` has a formal power series at `x` bounded by `0`, then `f` is equal to `0` in a
neighborhood of `x`. -/
/-
**HasFiniteFPowerSeriesAt.eventually_zero_of_bound_zero** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：HasFiniteFPowerSeriesAt.eventually_zero_of_bound_zero (hf : HasFiniteFPowe
rSeriesAt f pf x 0) : f =ᶠ[𝓝 x] 0
参数：hf : HasFiniteFPowerSeriesAt f pf x 0。
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyEq_iff_exists_mem`：eventuallyEq_iff_exists_mem {l : Fil
ter α} {f g : α -> β} : f =ᶠ[l] g ↔ exists s in l, EqOn f g s
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.eq_zero_of_bound_zero`：HasFiniteFPowerSeries
OnBall.eq_zero_of_bound_zero (hf : HasFiniteFPowerSeriesOnBall f pf x 0 r) : for
all y in Metric.eball x r, f y = 0

--- 原说明 ---
If `f` has a formal power series at `x` bounded by `0`, then `f` is equal to `0`
 in a
neighborhood of `x`.
-/
theorem HasFiniteFPowerSeriesAt.eventually_zero_of_bound_zero
    (hf : HasFiniteFPowerSeriesAt f pf x 0) : f =ᶠ[𝓝 x] 0 :=
  Filter.eventuallyEq_iff_exists_mem.mpr (let ⟨r, hf⟩ := hf; ⟨Metric.eball x r,
    Metric.eball_mem_nhds x hf.r_pos, fun y hy ↦ hf.eq_zero_of_bound_zero y hy⟩)

/-- If `f` has a formal power series on a ball bounded by `1`, then `f` is constant equal
to `f x` on the ball. -/
/-
**HasFiniteFPowerSeriesOnBall.eq_const_of_bound_one** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：HasFiniteFPowerSeriesOnBall.eq_const_of_bound_one (hf : HasFiniteFPowerSer
iesOnBall f pf x 1 r) : forall y in Metric.eball x r, f y = f x
参数：hf : HasFiniteFPowerSeriesOnBall f pf x 1 r。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.eq_partialSum'`：HasFiniteFPowerSeriesOnBall.
eq_partialSum' (hf : HasFiniteFPowerSeriesOnBall f p x n r) : forall y in Metric
.eball x r, forall m, n <= m -> …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Metric.mem_eball`：∀ {α : Type u} [inst : EDist α] {x y : α} {ε : ENNReal
}, y ∈ Metric.eball x ε ↔ edist y x < ε
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
If `f` has a formal power series on a ball bounded by `1`, then `f` is constant 
equal
to `f x` on the ball.
-/
theorem HasFiniteFPowerSeriesOnBall.eq_const_of_bound_one
    (hf : HasFiniteFPowerSeriesOnBall f pf x 1 r) : ∀ y ∈ Metric.eball x r, f y = f x := by
  intro y hy
  rw [hf.eq_partialSum' y hy 1 le_rfl, hf.eq_partialSum' x
    (by rw [Metric.mem_eball, edist_self]; exact hf.r_pos) 1 le_rfl]
  simp only [FormalMultilinearSeries.partialSum, Finset.range_one, Finset.sum_singleton]
  congr
  apply funext
  simp only [IsEmpty.forall_iff]

/-- If `f` has a formal power series at x bounded by `1`, then `f` is constant equal
to `f x` in a neighborhood of `x`. -/
/-
**HasFiniteFPowerSeriesAt.eventually_const_of_bound_one** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：HasFiniteFPowerSeriesAt.eventually_const_of_bound_one (hf : HasFiniteFPowe
rSeriesAt f pf x 1) : f =ᶠ[𝓝 x] (fun _ => f x)
参数：hf : HasFiniteFPowerSeriesAt f pf x 1。
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyEq_iff_exists_mem`：eventuallyEq_iff_exists_mem {l : Fil
ter α} {f g : α -> β} : f =ᶠ[l] g ↔ exists s in l, EqOn f g s
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.eq_const_of_bound_one`：HasFiniteFPowerSeries
OnBall.eq_const_of_bound_one (hf : HasFiniteFPowerSeriesOnBall f pf x 1 r) : for
all y in Metric.eball x r, f y = f x

--- 原说明 ---
If `f` has a formal power series at x bounded by `1`, then `f` is constant equal
to `f x` in a neighborhood of `x`.
-/
theorem HasFiniteFPowerSeriesAt.eventually_const_of_bound_one
    (hf : HasFiniteFPowerSeriesAt f pf x 1) : f =ᶠ[𝓝 x] (fun _ => f x) :=
  Filter.eventuallyEq_iff_exists_mem.mpr (let ⟨r, hf⟩ := hf; ⟨Metric.eball x r,
    Metric.eball_mem_nhds x hf.r_pos, fun y hy ↦ hf.eq_const_of_bound_one y hy⟩)

/-- If a function admits a finite power series expansion on a disk, then it is continuous there. -/
/-
**HasFiniteFPowerSeriesOnBall.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `HasFiniteF
PowerSeriesOnBall`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {x : E} {r : ENNReal} {n : ℕ},   HasFiniteFPowerSeriesOnBall f
 p x n r → ContinuousOn f (Metric.eball x r)
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
· 使用定理 `HasFPowerSeriesOnBall.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …

--- 原说明 ---
If a function admits a finite power series expansion on a disk, then it is conti
nuous there.
-/
protected theorem HasFiniteFPowerSeriesOnBall.continuousOn
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    ContinuousOn f (Metric.eball x r) := hf.1.continuousOn
/-
**HasFiniteFPowerSeriesAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `HasFiniteFPowe
rSeriesAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {x : E} {n : ℕ}, HasFiniteFPowerSeriesAt f p x n → ContinuousA
t f x
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
· 使用定理 `HasFPowerSeriesAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Typ
e u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [ins
t_2 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesAt.hasFPowerSeriesAt`：HasFiniteFPowerSeriesAt.hasFP
owerSeriesAt (hf : HasFiniteFPowerSeriesAt f p x n) : HasFPowerSeriesAt f p x
-/
protected theorem HasFiniteFPowerSeriesAt.continuousAt (hf : HasFiniteFPowerSeriesAt f p x n) :
    ContinuousAt f x := hf.hasFPowerSeriesAt.continuousAt
/-
**CPolynomialAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `CPolynomialAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {x : E},   CPolynomi
alAt 𝕜 f x → ContinuousAt f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `CPolynomialAt.analyticAt`：CPolynomialAt.analyticAt (hf : CPolynomialAt 𝕜
 f x) : AnalyticAt 𝕜 f x
-/
protected theorem CPolynomialAt.continuousAt (hf : CPolynomialAt 𝕜 f x) : ContinuousAt f x :=
  hf.analyticAt.continuousAt
/-
**CPolynomialOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `CPolynomialOn`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {s : Set E},   CPoly
nomialOn 𝕜 f s → ContinuousOn f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `CPolynomialOn.analyticOnNhd`：CPolynomialOn.analyticOnNhd {s : Set E} (hf
 : CPolynomialOn 𝕜 f s) : AnalyticOnNhd 𝕜 f s
-/
protected theorem CPolynomialOn.continuousOn {s : Set E} (hf : CPolynomialOn 𝕜 f s) :
    ContinuousOn f s :=
  hf.analyticOnNhd.continuousOn

/-- Continuously polynomial everywhere implies continuous -/
/-
**CPolynomialOn.continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.continuous {f : E -> F} (fa : CPolynomialOn 𝕜 f univ) : Cont
inuous f
参数：fa : CPolynomialOn 𝕜 f univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `CPolynomialOn.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …

--- 原说明 ---
Continuously polynomial everywhere implies continuous
-/
theorem CPolynomialOn.continuous {f : E → F} (fa : CPolynomialOn 𝕜 f univ) : Continuous f := by
  rw [← continuousOn_univ]; exact fa.continuousOn
/-
**FormalMultilinearSeries.sum_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultili
nearSeries`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   (p : FormalMultilinearSeries 𝕜
 E F) {n : ℕ}, (∀ (m : ℕ), n ≤ m → p m = 0) → ∀ (x : E), p.sum x = p.partialSum 
n x
参数：p : FormalMultilinearSeries 𝕜 E F；∀ (m : ℕ), n ≤ m → p m = 0；x : E。
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
· 使用定理 `tsum_eq_sum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [L.LeAtTop] {s
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
-/
protected theorem FormalMultilinearSeries.sum_of_finite (p : FormalMultilinearSeries 𝕜 E F)
    {n : ℕ} (hn : ∀ m, n ≤ m → p m = 0) (x : E) :
    p.sum x = p.partialSum n x :=
  tsum_eq_sum fun m hm ↦ by rw [Finset.mem_range, not_lt] at hm; rw [hn m hm]; rfl

/-- A finite formal multilinear series sums to its sum at every point. -/
/-
**FormalMultilinearSeries.hasSum_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `FormalMult
ilinearSeries`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   (p : FormalMultilinearSeries 𝕜
 E F) {n : ℕ},   (∀ (m : ℕ), n ≤ m → p m = 0) → ∀ (x : E), HasSum (fun n => (p n
) fun x_1 => x) (p.sum x)
参数：p : FormalMultilinearSeries 𝕜 E F；∀ (m : ℕ), n ≤ m → p m = 0；x : E；fun n => (
p n) fun x_1 => x；p.sum x。
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
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `summable_of_ne_finset_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddC
ommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}
 {s : Finset β},…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop

--- 原说明 ---
A finite formal multilinear series sums to its sum at every point.
-/
protected theorem FormalMultilinearSeries.hasSum_of_finite (p : FormalMultilinearSeries 𝕜 E F)
    {n : ℕ} (hn : ∀ m, n ≤ m → p m = 0) (x : E) :
    HasSum (fun n : ℕ => p n fun _ => x) (p.sum x) :=
  summable_of_ne_finset_zero (s := .range n)
    (fun m hm ↦ by rw [Finset.mem_range, not_lt] at hm; rw [hn m hm]; rfl)
    |>.hasSum

/-- The sum of a finite power series `p` admits `p` as a power series. -/
/-
**FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite** 是 Mathlib 中的一个
定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   (p : FormalMultilinearSeries 𝕜
 E F) {n : ℕ}, (∀ (m : ℕ), n ≤ m → p m = 0) → HasFiniteFPowerSeriesOnBall p.sum 
p 0 n ⊤
参数：p : FormalMultilinearSeries 𝕜 E F；∀ (m : ℕ), n ≤ m → p m = 0。
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
· 使用定理 `FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero`：radiu
s_eq_top_of_forall_image_add_eq_zero (n : Nat) (hn : forall m, p (m + n) = 0) : 
p.radius = ∞
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.zero_lt_top`：0 < ⊤
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `FormalMultilinearSeries.hasSum_of_finite`：∀ {𝕜 : Type u_1} {E : Type u_2
} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup
 E]   [inst_2 : NormedSpace 𝕜 …

--- 原说明 ---
The sum of a finite power series `p` admits `p` as a power series.
-/
protected theorem FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite
    (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (hn : ∀ m, n ≤ m → p m = 0) :
    HasFiniteFPowerSeriesOnBall p.sum p 0 n ⊤ where
  r_le := by rw [radius_eq_top_of_forall_image_add_eq_zero p n fun _ => hn _ (Nat.le_add_left _ _)]
  r_pos := zero_lt_top
  finite := hn
  hasSum {y} _ := by rw [zero_add]; exact p.hasSum_of_finite hn y
/-
**HasFiniteFPowerSeriesOnBall.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.sum (h : HasFiniteFPowerSeriesOnBall f p x n r
) {y : E} (hy : y in Metric.eball (0 : E) r) : f (x + y) = p.sum y
参数：h : HasFiniteFPowerSeriesOnBall f p x n r；hy : y in Metric.eball (0 : E) r。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
-/
theorem HasFiniteFPowerSeriesOnBall.sum (h : HasFiniteFPowerSeriesOnBall f p x n r) {y : E}
    (hy : y ∈ Metric.eball (0 : E) r) : f (x + y) = p.sum y :=
  (h.hasSum hy).tsum_eq.symm

/-- The sum of a finite power series is continuous. -/
/-
**FormalMultilinearSeries.continuousOn_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Form
alMultilinearSeries`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   (p : FormalMultilinearSeries 𝕜
 E F) {n : ℕ}, (∀ (m : ℕ), n ≤ m → p m = 0) → Continuous p.sum
参数：p : FormalMultilinearSeries 𝕜 E F；∀ (m : ℕ), n ≤ m → p m = 0。
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
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `Metric.eball_top`：Metric.eball_top (x : α) : eball x ⊤ = univ
· 使用定理 `HasFiniteFPowerSeriesOnBall.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2
} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup
 E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite`：∀ {𝕜 : Ty
pe u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 …

--- 原说明 ---
The sum of a finite power series is continuous.
-/
protected theorem FormalMultilinearSeries.continuousOn_of_finite
    (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (hn : ∀ m, n ≤ m → p m = 0) :
    Continuous p.sum := by
  rw [← continuousOn_univ, ← Metric.eball_top]
  exact (p.hasFiniteFPowerSeriesOnBall_of_finite hn).continuousOn

end FiniteFPowerSeries

namespace FormalMultilinearSeries

section

/-! We study what happens when we change the origin of a finite formal multilinear series `p`. The
main point is that the new series `p.changeOrigin x` is still finite, with the same bound. -/

/-- If `p` is a formal multilinear series such that `p m = 0` for `n ≤ m`, then
`p.changeOriginSeriesTerm k l = 0` for `n ≤ k + l`. -/
/-
**FormalMultilinearSeries.changeOriginSeriesTerm_bound** 是 Mathlib 中的一个引理，位于命名空间
 `FormalMultilinearSeries`。
形式化陈述：changeOriginSeriesTerm_bound (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
 (hn : forall (m : Nat), n <= m -> p m = 0) (k l : Nat) {s : Finset (Fin (k + l)
)} (hs : s.card = l) (hkl : n <= k + l) : p.changeOriginSeriesTerm k l s hs = 0
参数：p : FormalMultilinearSeries 𝕜 E F；hn : forall (m : Nat), n <= m -> p m = 0；k 
l : Nat；Fin (k + l)；hs : s.card = l；hkl : n <= k + l。
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
· 使用定理 `FormalMultilinearSeries.changeOriginSeriesTerm.eq_1`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…

--- 原说明 ---
If `p` is a formal multilinear series such that `p m = 0` for `n ≤ m`, then
`p.changeOriginSeriesTerm k l = 0` for `n ≤ k + l`.
-/
lemma changeOriginSeriesTerm_bound (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (hn : ∀ (m : ℕ), n ≤ m → p m = 0) (k l : ℕ) {s : Finset (Fin (k + l))}
    (hs : s.card = l) (hkl : n ≤ k + l) :
    p.changeOriginSeriesTerm k l s hs = 0 := by
  rw [changeOriginSeriesTerm, hn _ hkl, map_zero]

/-- If `p` is a finite formal multilinear series, then so is `p.changeOriginSeries k` for every
`k` in `ℕ`. More precisely, if `p m = 0` for `n ≤ m`, then `p.changeOriginSeries k m = 0` for
`n ≤ k + m`. -/
/-
**FormalMultilinearSeries.changeOriginSeries_finite_of_finite** 是 Mathlib 中的一个引理
，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：changeOriginSeries_finite_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n
 : Nat} (hn : forall (m : Nat), n <= m -> p m = 0) (k : Nat) : forall {m : Nat},
 n <= k + m -> p.changeOriginSeries k m = 0
参数：p : FormalMultilinearSeries 𝕜 E F；hn : forall (m : Nat), n <= m -> p m = 0；k 
: Nat。
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
· 使用定理 `FormalMultilinearSeries.changeOriginSeries.eq_1`：∀ {𝕜 : Type u_1} {E : T
ype u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCo
mmGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用引理 `FormalMultilinearSeries.changeOriginSeriesTerm_bound`：changeOriginSeries
Term_bound (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : forall (m : Nat),
 n <= m -> p m = 0) (k l : Nat) {s : Finse…

--- 原说明 ---
If `p` is a finite formal multilinear series, then so is `p.changeOriginSeries k
` for every
`k` in `ℕ`. More precisely, if `p m = 0` for `n ≤ m`, then `p.changeOriginSeries
 k m = 0` for
`n ≤ k + m`.
-/
lemma changeOriginSeries_finite_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (hn : ∀ (m : ℕ), n ≤ m → p m = 0) (k : ℕ) : ∀ {m : ℕ}, n ≤ k + m →
    p.changeOriginSeries k m = 0 := by
  intro m hm
  rw [changeOriginSeries]
  exact Finset.sum_eq_zero (fun _ _ => p.changeOriginSeriesTerm_bound hn _ _ _ hm)
/-
**FormalMultilinearSeries.changeOriginSeries_sum_eq_partialSum_of_finite** 是 Mat
hlib 中的一个引理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：changeOriginSeries_sum_eq_partialSum_of_finite (p : FormalMultilinearSerie
s 𝕜 E F) {n : Nat} (hn : forall (m : Nat), n <= m -> p m = 0) (k : Nat) : (p.cha
ngeOriginSeries k).sum = (p.changeOriginSeries k).partialSum (n - k)
参数：p : FormalMultilinearSeries 𝕜 E F；hn : forall (m : Nat), n <= m -> p m = 0；k 
: Nat。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.partialSum.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : AddComm
Monoid F]   [inst_3 : _root_.…
· 使用定理 `FormalMultilinearSeries.sum.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : AddCommMonoid 
F]   [inst_3 : _root_.…
· 使用定理 `tsum_eq_sum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [L.LeAtTop] {s
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用引理 `FormalMultilinearSeries.changeOriginSeries_finite_of_finite`：changeOrigi
nSeries_finite_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : for
all (m : Nat), n <= m -> p m = 0) (k : Nat) : for…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.le_add_of_sub_le`：∀ {a b c : ℕ}, a - b ≤ c → a ≤ c + b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
-/
lemma changeOriginSeries_sum_eq_partialSum_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (hn : ∀ (m : ℕ), n ≤ m → p m = 0) (k : ℕ) :
    (p.changeOriginSeries k).sum = (p.changeOriginSeries k).partialSum (n - k) := by
  ext x
  rw [partialSum, FormalMultilinearSeries.sum,
    tsum_eq_sum (f := fun m => p.changeOriginSeries k m (fun _ => x)) (s := Finset.range (n - k))]
  intro m hm
  rw [Finset.mem_range, not_lt] at hm
  rw [p.changeOriginSeries_finite_of_finite hn k (by rw [add_comm]; exact Nat.le_add_of_sub_le hm),
    _root_.zero_apply]

/-- If `p` is a formal multilinear series such that `p m = 0` for `n ≤ m`, then
`p.changeOrigin x k = 0` for `n ≤ k`. -/
/-
**FormalMultilinearSeries.changeOrigin_finite_of_finite** 是 Mathlib 中的一个引理，位于命名空
间 `FormalMultilinearSeries`。
形式化陈述：changeOrigin_finite_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : Nat
} (hn : forall (m : Nat), n <= m -> p m = 0) {k : Nat} (hk : n <= k) : p.changeO
rigin x k = 0
参数：p : FormalMultilinearSeries 𝕜 E F；hn : forall (m : Nat), n <= m -> p m = 0；hk
 : n <= k。
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
· 使用定理 `FormalMultilinearSeries.changeOrigin.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_
2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGrou
p E]   [inst_2 : NormedSpace 𝕜 …
· 使用引理 `FormalMultilinearSeries.changeOriginSeries_sum_eq_partialSum_of_finite`：
changeOriginSeries_sum_eq_partialSum_of_finite (p : FormalMultilinearSeries 𝕜 E 
F) {n : Nat} (hn : forall (m : Nat), n <= m -> p m = 0) (k :…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用引理 `FormalMultilinearSeries.changeOriginSeries_finite_of_finite`：changeOrigi
nSeries_finite_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : for
all (m : Nat), n <= m -> p m = 0) (k : Nat) : for…
· 使用定理 `le_add_of_le_left`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [
CanonicallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…

--- 原说明 ---
If `p` is a formal multilinear series such that `p m = 0` for `n ≤ m`, then
`p.changeOrigin x k = 0` for `n ≤ k`.
-/
lemma changeOrigin_finite_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (hn : ∀ (m : ℕ), n ≤ m → p m = 0) {k : ℕ} (hk : n ≤ k) :
    p.changeOrigin x k = 0 := by
  rw [changeOrigin, p.changeOriginSeries_sum_eq_partialSum_of_finite hn]
  apply Finset.sum_eq_zero
  intro m hm
  rw [Finset.mem_range] at hm
  rw [p.changeOriginSeries_finite_of_finite hn k (le_add_of_le_left hk), _root_.zero_apply]
/-
**FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_changeOrigin** 是 Mathlib 中
的一个定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：hasFiniteFPowerSeriesOnBall_changeOrigin (p : FormalMultilinearSeries 𝕜 E 
F) {n : Nat} (k : Nat) (hn : forall (m : Nat), n + k <= m -> p m = 0) : HasFinit
eFPowerSeriesOnBall (p.changeOrigin · k) (p.changeOriginSeries k) 0 n ⊤
参数：p : FormalMultilinearSeries 𝕜 E F；k : Nat；hn : forall (m : Nat), n + k <= m -
> p m = 0。
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
· 使用定理 `FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite`：∀ {𝕜 : Ty
pe u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用引理 `FormalMultilinearSeries.changeOriginSeries_finite_of_finite`：changeOrigi
nSeries_finite_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : for
all (m : Nat), n <= m -> p m = 0) (k : Nat) : for…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem hasFiniteFPowerSeriesOnBall_changeOrigin (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (k : ℕ) (hn : ∀ (m : ℕ), n + k ≤ m → p m = 0) :
    HasFiniteFPowerSeriesOnBall (p.changeOrigin · k) (p.changeOriginSeries k) 0 n ⊤ :=
  (p.changeOriginSeries k).hasFiniteFPowerSeriesOnBall_of_finite
    fun _ hm => p.changeOriginSeries_finite_of_finite hn k <| by grw [hm, add_comm]
/-
**FormalMultilinearSeries.changeOrigin_eval_of_finite** 是 Mathlib 中的一个定理，位于命名空间 
`FormalMultilinearSeries`。
形式化陈述：changeOrigin_eval_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} 
(hn : forall (m : Nat), n <= m -> p m = 0) (x y : E) : (p.changeOrigin x).sum y 
= p.sum (x + y)
参数：p : FormalMultilinearSeries 𝕜 E F；hn : forall (m : Nat), n <= m -> p m = 0；x 
y : E。
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
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}
, Set.InjOn f (f ⁻¹' s) → s.Finite → (f ⁻¹' s).Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_of_singleton_coe`：iUnion_of_singleton_coe (s : Set α) : ⋃ i :
 s, ({(i : α)} : Set α) = s
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.finite_iUnion`：finite_iUnion [Finite ι] {f : ι -> Set α} (H : forall
 i, (f i).Finite) : (⋃ i, f i).Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用引理 `FormalMultilinearSeries.changeOriginSeriesTerm_bound`：changeOriginSeries
Term_bound (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : forall (m : Nat),
 n <= m -> p m = 0) (k l : Nat) {s : Finse…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FormalMultilinearSeries.changeOriginIndexEquiv_apply_fst`：∀ (s : (k : ℕ)
 × (l : ℕ) × { s // s.card = l }),   (FormalMultilinearSeries.changeOriginIndexE
quiv s).fst = s.fst + s.snd.fst
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `hasSum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] [inst_2 : Fintype β] (f : β → α)   (L : optParam 
(Sum…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用引理 `FormalMultilinearSeries.changeOriginSeries_finite_of_finite`：changeOrigi
nSeries_finite_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : for
all (m : Nat), n <= m -> p m = 0) (k : Nat) : for…
· 使用定理 `le_add_of_le_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] 
[CanonicallyOrderedAdd α] {a b c : α}, a ≤ c → a ≤ b + c
（共 63 条，此处仅展示前 30 条）
-/
theorem changeOrigin_eval_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (hn : ∀ (m : ℕ), n ≤ m → p m = 0) (x y : E) :
    (p.changeOrigin x).sum y = p.sum (x + y) := by
  let f (s : Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) : F :=
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ ↦ x) fun _ ↦ y
  have finsupp : f.support.Finite := by
    apply Set.Finite.subset (s := changeOriginIndexEquiv ⁻¹' Sigma.fst ⁻¹' {m | m < n})
    · apply Set.Finite.preimage (Equiv.injective _).injOn
      simp_rw [← {m | m < n}.iUnion_of_singleton_coe, preimage_iUnion, ← range_sigmaMk]
      exact finite_iUnion fun _ ↦ finite_range _
    · refine fun s ↦ Not.imp_symm fun hs ↦ ?_
      simp only [preimage_ofPred_eq, changeOriginIndexEquiv_apply_fst, mem_ofPred, not_lt] at hs
      dsimp only [f]
      rw [changeOriginSeriesTerm_bound p hn _ _ _ hs, _root_.zero_apply, _root_.zero_apply]
  have hfkl k l : HasSum (f ⟨k, l, ·⟩) (changeOriginSeries p k l (fun _ ↦ x) fun _ ↦ y) := by
    simp_rw [changeOriginSeries, sum_apply]; apply hasSum_fintype
  have hfk k : HasSum (f ⟨k, ·⟩) (changeOrigin p x k fun _ ↦ y) := by
    have (m) (hm : m ∉ Finset.range n) : changeOriginSeries p k m (fun _ ↦ x) = 0 := by
      rw [Finset.mem_range, not_lt] at hm
      rw [changeOriginSeries_finite_of_finite _ hn _ (le_add_of_le_right hm), _root_.zero_apply]
    rw [changeOrigin, FormalMultilinearSeries.sum,
      ContinuousMultilinearMap.tsum_eval (summable_of_ne_finset_zero this)]
    refine (summable_of_ne_finset_zero (s := Finset.range n) fun m hm ↦ ?_).hasSum.sigma_of_hasSum
      (hfkl k) (summable_of_hasFiniteSupport <| finsupp.preimage sigma_mk_injective.injOn)
    rw [this m hm, _root_.zero_apply]
  have hf : HasSum f ((p.changeOrigin x).sum y) :=
    ((p.changeOrigin x).hasSum_of_finite (fun _ ↦ changeOrigin_finite_of_finite p hn) _)
      |>.sigma_of_hasSum hfk (summable_of_hasFiniteSupport finsupp)
  refine hf.unique (changeOriginIndexEquiv.symm.hasSum_iff.1 ?_)
  refine (p.hasSum_of_finite hn (x + y)).sigma_of_hasSum (fun n ↦ ?_)
    (changeOriginIndexEquiv.symm.summable_iff.2 hf.summable)
  rw [← Pi.add_def, (p n).map_add_univ (fun _ ↦ x) fun _ ↦ y]
  simp_rw [← changeOriginSeriesTerm_changeOriginIndexEquiv_symm]
  exact hasSum_fintype fun c ↦ f (changeOriginIndexEquiv.symm ⟨n, c⟩)

/-- The terms of the formal multilinear series `p.changeOrigin` are continuously polynomial
as we vary the origin -/
/-
**FormalMultilinearSeries.cpolynomialAt_changeOrigin_of_finite** 是 Mathlib 中的一个定
理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：cpolynomialAt_changeOrigin_of_finite (p : FormalMultilinearSeries 𝕜 E F) {
n : Nat} (hn : forall (m : Nat), n <= m -> p m = 0) (k : Nat) : CPolynomialAt 𝕜 
(p.changeOrigin · k) 0
参数：p : FormalMultilinearSeries 𝕜 E F；hn : forall (m : Nat), n <= m -> p m = 0；k 
: Nat。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.cpolynomialAt`：HasFiniteFPowerSeriesOnBall.c
polynomialAt (hf : HasFiniteFPowerSeriesOnBall f p x n r) : CPolynomialAt 𝕜 f x
· 使用定理 `FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_changeOrigin`：hasFin
iteFPowerSeriesOnBall_changeOrigin (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
 (k : Nat) (hn : forall (m : Nat), n + k <= m -> p m =…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b

--- 原说明 ---
The terms of the formal multilinear series `p.changeOrigin` are continuously pol
ynomial
as we vary the origin
-/
theorem cpolynomialAt_changeOrigin_of_finite (p : FormalMultilinearSeries 𝕜 E F)
    {n : ℕ} (hn : ∀ (m : ℕ), n ≤ m → p m = 0) (k : ℕ) :
    CPolynomialAt 𝕜 (p.changeOrigin · k) 0 :=
  (p.hasFiniteFPowerSeriesOnBall_changeOrigin k fun _ h ↦ hn _ (le_self_add.trans h)).cpolynomialAt

end

end FormalMultilinearSeries

section

variable {x y : E}

/-
**HasFiniteFPowerSeriesOnBall.changeOrigin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.changeOrigin (hf : HasFiniteFPowerSeriesOnBall
 f p x n r) (h : (‖y‖₊ : Real>=0∞) < r) : HasFiniteFPowerSeriesOnBall f (p.chang
eOrigin y) (x + y) n (r - ‖y‖₊) where r_le
参数：hf : HasFiniteFPowerSeriesOnBall f p x n r；h : (‖y‖₊ : Real>=0∞) < r。
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
· 使用定理 `tsub_le_tsub_right`：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b
 - c
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `FormalMultilinearSeries.changeOrigin_radius`：changeOrigin_radius : p.rad
ius - ‖x‖₊ <= (p.changeOrigin x).radius
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.changeOrigin_eval_of_finite`：changeOrigin_eval_o
f_finite (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : forall (m : Nat), n
 <= m -> p m = 0) (x y : E) : (p.changeOr…
· 使用定理 `HasFiniteFPowerSeriesOnBall.finite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `HasFiniteFPowerSeriesOnBall.sum`：HasFiniteFPowerSeriesOnBall.sum (h : Ha
sFiniteFPowerSeriesOnBall f p x n r) {y : E} (hy : y in Metric.eball (0 : E) r) 
: f (x + y) = p.sum y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_eball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : 
E} {r : ENNReal}, a ∈ Metric.eball 0 r ↔ ‖a‖ₑ < r
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `enorm_add_le`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESe
minormedAddMonoid E] (a b : E), ‖a + b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `lt_tsub_iff_right`：lt_tsub_iff_right : a < b - c ↔ a + c < b
· 使用定理 `FormalMultilinearSeries.hasSum_of_finite`：∀ {𝕜 : Type u_1} {E : Type u_2
} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup
 E]   [inst_2 : NormedSpace 𝕜 …
· 使用引理 `FormalMultilinearSeries.changeOrigin_finite_of_finite`：changeOrigin_fini
te_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : forall (m : Nat
), n <= m -> p m = 0) {k : Nat} (hk : n <= …
-/
theorem HasFiniteFPowerSeriesOnBall.changeOrigin (hf : HasFiniteFPowerSeriesOnBall f p x n r)
    (h : (‖y‖₊ : ℝ≥0∞) < r) :
    HasFiniteFPowerSeriesOnBall f (p.changeOrigin y) (x + y) n (r - ‖y‖₊) where
  r_le := (tsub_le_tsub_right hf.r_le _).trans p.changeOrigin_radius
  r_pos := by simp [h]
  finite _ hm := p.changeOrigin_finite_of_finite hf.finite hm
  hasSum {z} hz := by
    have : f (x + y + z) =
        FormalMultilinearSeries.sum (FormalMultilinearSeries.changeOrigin p y) z := by
      rw [mem_eball_zero_iff, lt_tsub_iff_right, add_comm] at hz
      rw [p.changeOrigin_eval_of_finite hf.finite, add_assoc, hf.sum]
      exact mem_eball_zero_iff.2 ((enorm_add_le _ _).trans_lt hz)
    rw [this]
    apply (p.changeOrigin y).hasSum_of_finite fun _ => p.changeOrigin_finite_of_finite hf.finite

/-- If a function admits a finite power series expansion `p` on an open ball `B (x, r)`, then
it is continuously polynomial at every point of this ball. -/
/-
**HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem (hf : HasFiniteFPowerSeri
esOnBall f p x n r) (h : y in Metric.eball x r) : CPolynomialAt 𝕜 f y
参数：hf : HasFiniteFPowerSeriesOnBall f p x n r；h : y in Metric.eball x r。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.changeOrigin`：HasFiniteFPowerSeriesOnBall.ch
angeOrigin (hf : HasFiniteFPowerSeriesOnBall f p x n r) (h : (‖y‖₊ : Real>=0∞) <
 r) : HasFiniteFPowerSeriesOnB…
· 使用定理 `HasFiniteFPowerSeriesOnBall.cpolynomialAt`：HasFiniteFPowerSeriesOnBall.c
polynomialAt (hf : HasFiniteFPowerSeriesOnBall f p x n r) : CPolynomialAt 𝕜 f x
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b

--- 原说明 ---
If a function admits a finite power series expansion `p` on an open ball `B (x, 
r)`, then
it is continuously polynomial at every point of this ball.
-/
theorem HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) (h : y ∈ Metric.eball x r) :
    CPolynomialAt 𝕜 f y := by
  have : (‖y - x‖₊ : ℝ≥0∞) < r := by simpa [edist_eq_enorm_sub] using! h
  have := hf.changeOrigin this
  rw [add_sub_cancel] at this
  exact this.cpolynomialAt
/-
**HasFiniteFPowerSeriesOnBall.cpolynomialOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.cpolynomialOn (hf : HasFiniteFPowerSeriesOnBal
l f p x n r) : CPolynomialOn 𝕜 f (Metric.eball x r)
参数：hf : HasFiniteFPowerSeriesOnBall f p x n r。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem`：HasFiniteFPowerSeriesO
nBall.cpolynomialAt_of_mem (hf : HasFiniteFPowerSeriesOnBall f p x n r) (h : y i
n Metric.eball x r) : CPolynomialAt 𝕜 …
-/
theorem HasFiniteFPowerSeriesOnBall.cpolynomialOn (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    CPolynomialOn 𝕜 f (Metric.eball x r) :=
  fun _y hy => hf.cpolynomialAt_of_mem hy

variable (𝕜 f)

/-- For any function `f` from a normed vector space to a normed vector space, the set of points
`x` such that `f` is continuously polynomial at `x` is open. -/
/-
**isOpen_cpolynomialAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_cpolynomialAt : IsOpen { x | CPolynomialAt 𝕜 f x }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem`：HasFiniteFPowerSeriesO
nBall.cpolynomialAt_of_mem (hf : HasFiniteFPowerSeriesOnBall f p x n r) (h : y i
n Metric.eball x r) : CPolynomialAt 𝕜 …

--- 原说明 ---
For any function `f` from a normed vector space to a normed vector space, the se
t of points
`x` such that `f` is continuously polynomial at `x` is open.
-/
theorem isOpen_cpolynomialAt : IsOpen { x | CPolynomialAt 𝕜 f x } := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, n, r, hr⟩
  exact mem_of_superset (Metric.eball_mem_nhds _ hr.r_pos) fun y hy => hr.cpolynomialAt_of_mem hy

variable {𝕜}
/-
**CPolynomialAt.eventually_cpolynomialAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt.eventually_cpolynomialAt {f : E -> F} {x : E} (h : CPolynomi
alAt 𝕜 f x) : forallᶠ y in 𝓝 x, CPolynomialAt 𝕜 f y
参数：h : CPolynomialAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_cpolynomialAt`：isOpen_cpolynomialAt : IsOpen { x | CPolynomialAt 
𝕜 f x }
-/
theorem CPolynomialAt.eventually_cpolynomialAt {f : E → F} {x : E} (h : CPolynomialAt 𝕜 f x) :
    ∀ᶠ y in 𝓝 x, CPolynomialAt 𝕜 f y :=
  (isOpen_cpolynomialAt 𝕜 f).mem_nhds h
/-
**CPolynomialAt.exists_mem_nhds_cpolynomialOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt.exists_mem_nhds_cpolynomialOn {f : E -> F} {x : E} (h : CPol
ynomialAt 𝕜 f x) : exists s in 𝓝 x, CPolynomialOn 𝕜 f s
参数：h : CPolynomialAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists_mem`：∀ {α : Type u} {p : α → Prop} {f : Filter 
α}, (∀ᶠ (x : α) in f, p x) → ∃ v ∈ f, ∀ y ∈ v, p y
· 使用定理 `CPolynomialAt.eventually_cpolynomialAt`：CPolynomialAt.eventually_cpolyno
mialAt {f : E -> F} {x : E} (h : CPolynomialAt 𝕜 f x) : forallᶠ y in 𝓝 x, CPolyn
omialAt 𝕜 f y
-/
theorem CPolynomialAt.exists_mem_nhds_cpolynomialOn {f : E → F} {x : E} (h : CPolynomialAt 𝕜 f x) :
    ∃ s ∈ 𝓝 x, CPolynomialOn 𝕜 f s :=
  h.eventually_cpolynomialAt.exists_mem

/-- If `f` is continuously polynomial at a point, then it is continuously polynomial in a
nonempty ball around that point. -/
/-
**CPolynomialAt.exists_ball_cpolynomialOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt.exists_ball_cpolynomialOn {f : E -> F} {x : E} (h : CPolynom
ialAt 𝕜 f x) : exists r : Real, 0 < r ∧ CPolynomialOn 𝕜 f (Metric.ball x r)
参数：h : CPolynomialAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `isOpen_cpolynomialAt`：isOpen_cpolynomialAt : IsOpen { x | CPolynomialAt 
𝕜 f x }

--- 原说明 ---
If `f` is continuously polynomial at a point, then it is continuously polynomial
 in a
nonempty ball around that point.
-/
theorem CPolynomialAt.exists_ball_cpolynomialOn {f : E → F} {x : E} (h : CPolynomialAt 𝕜 f x) :
    ∃ r : ℝ, 0 < r ∧ CPolynomialOn 𝕜 f (Metric.ball x r) :=
  Metric.isOpen_iff.mp (isOpen_cpolynomialAt _ _) _ h

end

