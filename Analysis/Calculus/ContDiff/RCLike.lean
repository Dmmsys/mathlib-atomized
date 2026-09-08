/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Higher differentiability over `ℝ` or `ℂ`
-/

public section

noncomputable section

open Set Fin Filter Function

open scoped NNReal Topology

section Real

/-!
### Results over `ℝ` or `ℂ`
  The results in this section rely on the Mean Value Theorem, and therefore hold only over `ℝ` (and
  its extension fields such as `ℂ`).
-/

variable {n : WithTop ℕ∞} {𝕂 : Type*} [RCLike 𝕂] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕂 E'] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕂 F']

/-- If a function has a Taylor series at order at least 1, then at points in the interior of the
domain of definition, the term of order 1 of this series is a strict derivative of `f`. -/
/-
**HasFTaylorSeriesUpToOn.hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFTaylorSeriesUpToOn.hasStrictFDerivAt {n : WithTop Nat∞} {s : Set E'} {
f : E' -> F'} {x : E'} {p : E' -> FormalMultilinearSeries 𝕂 E' F'} (hf : HasFTay
lorSeriesUpToOn n f p s) (hn : n != 0) (hs : s in 𝓝 x) : HasStrictFDerivAt f ((c
ontinuousMultilinearCurryFin1 𝕂 E' F') (p x 1)) x
参数：hf : HasFTaylorSeriesUpToOn n f p s；hn : n != 0；hs : s in 𝓝 x。
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
· 使用定理 `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt`：hasStrictFDerivAt_of_h
asFDerivAt_of_continuousAt (hder : forallᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hc
ont : ContinuousAt f' x) : HasStrictFD…
· 使用定理 `HasFTaylorSeriesUpToOn.eventually_hasFDerivAt`：HasFTaylorSeriesUpToOn.ev
entually_hasFDerivAt (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0) (hx : s 
in 𝓝 x) : forallᶠ y in 𝓝 x, HasFDer…
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `LinearIsometryEquiv.continuousAt`：∀ {R : Type u_1} {R₂ : Type u_2} {E : 
Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R 
→+* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `HasFTaylorSeriesUpToOn.cont`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENat.one_le_iff_ne_zero_withTop`：one_le_iff_ne_zero_withTop {n : WithTop
 Nat∞} : 1 <= n ↔ n != 0

--- 原说明 ---
If a function has a Taylor series at order at least 1, then at points in the int
erior of the
domain of definition, the term of order 1 of this series is a strict derivative 
of `f`.
-/
theorem HasFTaylorSeriesUpToOn.hasStrictFDerivAt {n : WithTop ℕ∞}
    {s : Set E'} {f : E' → F'} {x : E'}
    {p : E' → FormalMultilinearSeries 𝕂 E' F'} (hf : HasFTaylorSeriesUpToOn n f p s) (hn : n ≠ 0)
    (hs : s ∈ 𝓝 x) : HasStrictFDerivAt f ((continuousMultilinearCurryFin1 𝕂 E' F') (p x 1)) x :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hf.eventually_hasFDerivAt hn hs) <|
    (continuousMultilinearCurryFin1 𝕂 E' F').continuousAt.comp <|
      (hf.cont 1 <| ENat.one_le_iff_ne_zero_withTop.mpr hn).continuousAt hs

/-- If a function is `C^n` with `n ≠ 0` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
/-
**ContDiffAt.hasStrictFDerivAt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.hasStrictFDerivAt' {f : E' -> F'} {f' : E' ->L[𝕂] F'} {x : E'} 
(hf : ContDiffAt 𝕂 n f x) (hf' : HasFDerivAt f f' x) (hn : n != 0) : HasStrictFD
erivAt f f' x
参数：hf : ContDiffAt 𝕂 n f x；hf' : HasFDerivAt f f' x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.of_le`：ContDiffAt.of_le (h : ContDiffAt 𝕜 n f x) (hmn : m <= 
n) : ContDiffAt 𝕜 m f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENat.one_le_iff_ne_zero_withTop`：one_le_iff_ne_zero_withTop {n : WithTop
 Nat∞} : 1 <= n ↔ n != 0
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFTaylorSeriesUpToOn.hasStrictFDerivAt`：HasFTaylorSeriesUpToOn.hasStri
ctFDerivAt {n : WithTop Nat∞} {s : Set E'} {f : E' -> F'} {x : E'} {p : E' -> Fo
rmalMultilinearSeries 𝕂 E' F'}…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
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
· 使用定理 `HasFDerivAt.unique`：HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : H
asFDerivAt f f₁' x) : f' = f₁'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…

--- 原说明 ---
If a function is `C^n` with `n ≠ 0` around a point, and its derivative at that p
oint is given to
us as `f'`, then `f'` is also a strict derivative.
-/
theorem ContDiffAt.hasStrictFDerivAt' {f : E' → F'} {f' : E' →L[𝕂] F'} {x : E'}
    (hf : ContDiffAt 𝕂 n f x) (hf' : HasFDerivAt f f' x) (hn : n ≠ 0) :
    HasStrictFDerivAt f f' x := by
  rcases hf.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn) 1 le_rfl with ⟨u, H, p, hp⟩
  simp only [nhdsWithin_univ, mem_univ, insert_eq_of_mem] at H
  have := hp.hasStrictFDerivAt one_ne_zero H
  rwa [hf'.unique this.hasFDerivAt]

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
/-
**ContDiffAt.hasStrictDerivAt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.hasStrictDerivAt' {f : 𝕂 -> F'} {f' : F'} {x : 𝕂} (hf : ContDif
fAt 𝕂 n f x) (hf' : HasDerivAt f f' x) (hn : n != 0) : HasStrictDerivAt f f' x
参数：hf : ContDiffAt 𝕂 n f x；hf' : HasDerivAt f f' x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContDiffAt.hasStrictFDerivAt'`：ContDiffAt.hasStrictFDerivAt' {f : E' -> 
F'} {f' : E' ->L[𝕂] F'} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hf' : HasFDerivAt f 
f' x) (hn : n != 0)…

--- 原说明 ---
If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that p
oint is given to
us as `f'`, then `f'` is also a strict derivative.
-/
theorem ContDiffAt.hasStrictDerivAt' {f : 𝕂 → F'} {f' : F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x)
    (hf' : HasDerivAt f f' x) (hn : n ≠ 0) : HasStrictDerivAt f f' x :=
  hf.hasStrictFDerivAt' hf' hn

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
/-
**ContDiffAt.hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.hasStrictFDerivAt {f : E' -> F'} {x : E'} (hf : ContDiffAt 𝕂 n 
f x) (hn : n != 0) : HasStrictFDerivAt f (fderiv 𝕂 f x) x
参数：hf : ContDiffAt 𝕂 n f x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.hasStrictFDerivAt'`：ContDiffAt.hasStrictFDerivAt' {f : E' -> 
F'} {f' : E' ->L[𝕂] F'} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hf' : HasFDerivAt f 
f' x) (hn : n != 0)…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `ContDiffAt.differentiableAt`：ContDiffAt.differentiableAt (h : ContDiffAt
 𝕜 n f x) (hn : n != 0) : DifferentiableAt 𝕜 f x

--- 原说明 ---
If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` a
t this point
is also a strict derivative.
-/
theorem ContDiffAt.hasStrictFDerivAt {f : E' → F'} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : n ≠ 0) :
    HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.hasStrictFDerivAt' (hf.differentiableAt hn).hasFDerivAt hn

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
/-
**ContDiffAt.hasStrictDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.hasStrictDerivAt {f : 𝕂 -> F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x
) (hn : n != 0) : HasStrictDerivAt f (deriv f x) x
参数：hf : ContDiffAt 𝕂 n f x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContDiffAt.hasStrictFDerivAt`：ContDiffAt.hasStrictFDerivAt {f : E' -> F'
} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0) : HasStrictFDerivAt f (fderiv
 𝕂 f x) x

--- 原说明 ---
If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` a
t this point
is also a strict derivative.
-/
theorem ContDiffAt.hasStrictDerivAt {f : 𝕂 → F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x) (hn : n ≠ 0) :
    HasStrictDerivAt f (deriv f x) x :=
  (hf.hasStrictFDerivAt hn).hasStrictDerivAt

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
/-
**ContDiff.hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.hasStrictFDerivAt {f : E' -> F'} {x : E'} (hf : ContDiff 𝕂 n f) (
hn : n != 0) : HasStrictFDerivAt f (fderiv 𝕂 f x) x
参数：hf : ContDiff 𝕂 n f；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.hasStrictFDerivAt`：ContDiffAt.hasStrictFDerivAt {f : E' -> F'
} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0) : HasStrictFDerivAt f (fderiv
 𝕂 f x) x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x

--- 原说明 ---
If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict
 derivative.
-/
theorem ContDiff.hasStrictFDerivAt {f : E' → F'} {x : E'} (hf : ContDiff 𝕂 n f) (hn : n ≠ 0) :
    HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.contDiffAt.hasStrictFDerivAt hn

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
/-
**ContDiff.hasStrictDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.hasStrictDerivAt {f : 𝕂 -> F'} {x : 𝕂} (hf : ContDiff 𝕂 n f) (hn 
: n != 0) : HasStrictDerivAt f (deriv f x) x
参数：hf : ContDiff 𝕂 n f；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.hasStrictDerivAt`：ContDiffAt.hasStrictDerivAt {f : 𝕂 -> F'} {
x : 𝕂} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0) : HasStrictDerivAt f (deriv f x) 
x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x

--- 原说明 ---
If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict
 derivative.
-/
theorem ContDiff.hasStrictDerivAt {f : 𝕂 → F'} {x : 𝕂} (hf : ContDiff 𝕂 n f) (hn : n ≠ 0) :
    HasStrictDerivAt f (deriv f x) x :=
  hf.contDiffAt.hasStrictDerivAt hn

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {p : E → FormalMultilinearSeries ℝ E F} {s : Set E} {x : E}

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
and `‖p x 1‖₊ < K`, then `f` is `K`-Lipschitz in a neighborhood of `x` within `s`. -/
/-
**HasFTaylorSeriesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：HasFTaylorSeriesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt (hf : HasFTaylo
rSeriesUpToOn 1 f p (insert x s)) (hs : Convex Real s) (K : Real>=0) (hK : ‖p x 
1‖₊ < K) : exists t in 𝓝[s] x, LipschitzOnWith K f t
参数：hf : HasFTaylorSeriesUpToOn 1 f p (insert x s)；hs : Convex Real s；K : Real>=0
；hK : ‖p x 1‖₊ < K。
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
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `HasFTaylorSeriesUpToOn.hasFDerivWithinAt`：HasFTaylorSeriesUpToOn.hasFDer
ivWithinAt (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0) (hx : x in s) : Ha
sFDerivWithinAt f (continuousM…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `LinearIsometryEquiv.continuousAt`：∀ {R : Type u_1} {R₂ : Type u_2} {E : 
Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R 
→+* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `HasFTaylorSeriesUpToOn.cont`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.nnnorm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_
lt`：exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt (hs : Co
nvex Real s) {f : E -> G} (hder : forallᶠ y in 𝓝[s] x, HasFDeriv…
· 使用定理 `instIsRCLikeNormedField`：∀ (𝕜 : Type u_3) [h : RCLike 𝕜], IsRCLikeNormed
Field 𝕜
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is
 a convex set,
and `‖p x 1‖₊ < K`, then `f` is `K`-Lipschitz in a neighborhood of `x` within `s
`.
-/
theorem HasFTaylorSeriesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt
    (hf : HasFTaylorSeriesUpToOn 1 f p (insert x s)) (hs : Convex ℝ s) (K : ℝ≥0)
    (hK : ‖p x 1‖₊ < K) : ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  set f' := fun y => continuousMultilinearCurryFin1 ℝ E F (p y 1)
  have hder : ∀ y ∈ s, HasFDerivWithinAt f (f' y) s y := fun y hy =>
    (hf.hasFDerivWithinAt one_ne_zero (subset_insert x s hy)).mono (subset_insert x s)
  have hcont : ContinuousWithinAt f' s x :=
    (continuousMultilinearCurryFin1 ℝ E F).continuousAt.comp_continuousWithinAt
      ((hf.cont _ le_rfl _ (mem_insert _ _)).mono (subset_insert x s))
  replace hK : ‖f' x‖₊ < K := by simpa only [f', LinearIsometryEquiv.nnnorm_map]
  exact
    hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
      (eventually_nhdsWithin_iff.2 <| Eventually.of_forall hder) hcont K hK

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
then `f` is Lipschitz in a neighborhood of `x` within `s`. -/
/-
**HasFTaylorSeriesUpToOn.exists_lipschitzOnWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFTaylorSeriesUpToOn.exists_lipschitzOnWith (hf : HasFTaylorSeriesUpToOn
 1 f p (insert x s)) (hs : Convex Real s) : exists K, exists t in 𝓝[s] x, Lipsch
itzOnWith K f t
参数：hf : HasFTaylorSeriesUpToOn 1 f p (insert x s)；hs : Convex Real s。
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
· 使用定理 `HasFTaylorSeriesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt`：HasFTaylorSe
riesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt (hf : HasFTaylorSeriesUpToOn 1 f 
p (insert x s)) (hs : Convex Real s) (K : Real>=…
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal

--- 原说明 ---
If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is
 a convex set,
then `f` is Lipschitz in a neighborhood of `x` within `s`.
-/
theorem HasFTaylorSeriesUpToOn.exists_lipschitzOnWith
    (hf : HasFTaylorSeriesUpToOn 1 f p (insert x s)) (hs : Convex ℝ s) :
    ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t :=
  (exists_gt _).imp <| hf.exists_lipschitzOnWith_of_nnnorm_lt hs

/-- If `f` is `C^1` within a convex set `s` at `x`, then it is Lipschitz on a neighborhood of `x`
within `s`. -/
/-
**ContDiffWithinAt.exists_lipschitzOnWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.exists_lipschitzOnWith (hf : ContDiffWithinAt Real 1 f s 
x) (hs : Convex Real s) : exists K : Real>=0, exists t in 𝓝[s] x, LipschitzOnWit
h K f t
参数：hf : ContDiffWithinAt Real 1 f s x；hs : Convex Real s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhdsWithin_iff`：mem_nhdsWithin_iff {t : Set α} : s in 𝓝[t] x 
↔ exists ε > 0, ball x ε inter t subseteq s
· 使用定理 `HasFTaylorSeriesUpToOn.mono`：HasFTaylorSeriesUpToOn.mono (h : HasFTaylor
SeriesUpToOn n f p s) {t : Set E} (hst : t subseteq s) : HasFTaylorSeriesUpToOn 
n f p t
· 使用定理 `HasFTaylorSeriesUpToOn.exists_lipschitzOnWith`：HasFTaylorSeriesUpToOn.ex
ists_lipschitzOnWith (hf : HasFTaylorSeriesUpToOn 1 f p (insert x s)) (hs : Conv
ex Real s) : exists K, exists t in …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.insert_inter_distrib`：insert_inter_distrib (a : α) (s t : Set α) : i
nsert a (s inter t) = insert a s inter insert a t
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
· 使用定理 `nhdsWithin_restrict'`：nhdsWithin_restrict' {a : α} (s : Set α) {t : Set 
α} (h : t in 𝓝 a) : 𝓝[s] a = 𝓝[s inter t] a
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a

--- 原说明 ---
If `f` is `C^1` within a convex set `s` at `x`, then it is Lipschitz on a neighb
orhood of `x`
within `s`.
-/
theorem ContDiffWithinAt.exists_lipschitzOnWith
    (hf : ContDiffWithinAt ℝ 1 f s x) (hs : Convex ℝ s) :
    ∃ K : ℝ≥0, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  rcases hf 1 le_rfl with ⟨t, hst, p, hp⟩
  rcases Metric.mem_nhdsWithin_iff.mp hst with ⟨ε, ε0, hε⟩
  replace hp : HasFTaylorSeriesUpToOn 1 f p (Metric.ball x ε ∩ insert x s) := hp.mono hε
  clear hst hε t
  rw [← insert_eq_of_mem (Metric.mem_ball_self ε0), ← insert_inter_distrib] at hp
  rcases hp.exists_lipschitzOnWith ((convex_ball _ _).inter hs) with ⟨K, t, hst, hft⟩
  rw [inter_comm, ← nhdsWithin_restrict' _ (Metric.ball_mem_nhds _ ε0)] at hst
  exact ⟨K, t, hst, hft⟩

/-- If `f` is `C^1` at `x` and `K > ‖fderiv 𝕂 f x‖`, then `f` is `K`-Lipschitz in a neighborhood of
`x`. -/
/-
**ContDiffAt.exists_lipschitzOnWith_of_nnnorm_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.exists_lipschitzOnWith_of_nnnorm_lt {f : E' -> F'} {x : E'} (hf
 : ContDiffAt 𝕂 1 f x) (K : Real>=0) (hK : ‖fderiv 𝕂 f x‖₊ < K) : exists t in 𝓝 
x, LipschitzOnWith K f t
参数：hf : ContDiffAt 𝕂 1 f x；K : Real>=0；hK : ‖fderiv 𝕂 f x‖₊ < K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt`：HasStrictFDerivAt
.exists_lipschitzOnWith_of_nnnorm_lt (hf : HasStrictFDerivAt f f' x) (K : Real>=
0) (hK : ‖f'‖₊ < K) : exists s in 𝓝 x, Lips…
· 使用定理 `ContDiffAt.hasStrictFDerivAt`：ContDiffAt.hasStrictFDerivAt {f : E' -> F'
} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0) : HasStrictFDerivAt f (fderiv
 𝕂 f x) x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
If `f` is `C^1` at `x` and `K > ‖fderiv 𝕂 f x‖`, then `f` is `K`-Lipschitz in a 
neighborhood of
`x`.
-/
theorem ContDiffAt.exists_lipschitzOnWith_of_nnnorm_lt {f : E' → F'} {x : E'}
    (hf : ContDiffAt 𝕂 1 f x) (K : ℝ≥0) (hK : ‖fderiv 𝕂 f x‖₊ < K) :
    ∃ t ∈ 𝓝 x, LipschitzOnWith K f t :=
  (hf.hasStrictFDerivAt one_ne_zero).exists_lipschitzOnWith_of_nnnorm_lt K hK

/-- If `f` is `C^1` at `x`, then `f` is Lipschitz in a neighborhood of `x`. -/
/-
**ContDiffAt.exists_lipschitzOnWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.exists_lipschitzOnWith {f : E' -> F'} {x : E'} (hf : ContDiffAt
 𝕂 1 f x) : exists K, exists t in 𝓝 x, LipschitzOnWith K f t
参数：hf : ContDiffAt 𝕂 1 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.exists_lipschitzOnWith`：HasStrictFDerivAt.exists_lipsc
hitzOnWith (hf : HasStrictFDerivAt f f' x) : exists K, exists s in 𝓝 x, Lipschit
zOnWith K f s
· 使用定理 `ContDiffAt.hasStrictFDerivAt`：ContDiffAt.hasStrictFDerivAt {f : E' -> F'
} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0) : HasStrictFDerivAt f (fderiv
 𝕂 f x) x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
If `f` is `C^1` at `x`, then `f` is Lipschitz in a neighborhood of `x`.
-/
theorem ContDiffAt.exists_lipschitzOnWith {f : E' → F'} {x : E'} (hf : ContDiffAt 𝕂 1 f x) :
    ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t :=
  (hf.hasStrictFDerivAt one_ne_zero).exists_lipschitzOnWith

/-- If `f` is `C¹` on a convex set `s`, it is locally Lipschitz on `s`. -/
/-
**ContDiffOn.locallyLipschitzOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContDiffOn.locallyLipschitzOn {f : E -> F} {s : Set E} (hs : Convex Real s
) (hf : ContDiffOn Real 1 f s) : LocallyLipschitzOn s f
参数：hs : Convex Real s；hf : ContDiffOn Real 1 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.exists_lipschitzOnWith`：ContDiffWithinAt.exists_lipschi
tzOnWith (hf : ContDiffWithinAt Real 1 f s x) (hs : Convex Real s) : exists K : 
Real>=0, exists t in 𝓝[s] x, …

--- 原说明 ---
If `f` is `C¹` on a convex set `s`, it is locally Lipschitz on `s`.
-/
lemma ContDiffOn.locallyLipschitzOn {f : E → F} {s : Set E} (hs : Convex ℝ s)
    (hf : ContDiffOn ℝ 1 f s) : LocallyLipschitzOn s f := by
  intro x hx
  obtain ⟨K, t, ht, hf⟩ := ContDiffWithinAt.exists_lipschitzOnWith (hf x hx) hs
  use K, t

/-- If `f` is `C¹`, it is locally Lipschitz. -/
/-
**ContDiff.locallyLipschitz** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContDiff.locallyLipschitz {f : E' -> F'} (hf : ContDiff 𝕂 1 f) : LocallyLi
pschitz f
参数：hf : ContDiff 𝕂 1 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.exists_lipschitzOnWith`：ContDiffAt.exists_lipschitzOnWith {f 
: E' -> F'} {x : E'} (hf : ContDiffAt 𝕂 1 f x) : exists K, exists t in 𝓝 x, Lips
chitzOnWith K f t
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x

--- 原说明 ---
If `f` is `C¹`, it is locally Lipschitz.
-/
lemma ContDiff.locallyLipschitz {f : E' → F'} (hf : ContDiff 𝕂 1 f) : LocallyLipschitz f := by
  intro x
  rcases hf.contDiffAt.exists_lipschitzOnWith with ⟨K, t, ht, hf⟩
  use K, t

/-- If `f` is `C¹` on a convex compact set `s`, it is Lipschitz on `s`. -/
/-
**ContDiffOn.exists_lipschitzOnWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.exists_lipschitzOnWith {s : Set E} {f : E -> F} {n} (hf : ContD
iffOn Real n f s) (hn : n != 0) (hs : Convex Real s) (hs' : IsCompact s) : exist
s K, LipschitzOnWith K f s
参数：hf : ContDiffOn Real n f s；hn : n != 0；hs : Convex Real s；hs' : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`：LocallyLipschitzOn
.exists_lipschitzOnWith_of_compact {f : α -> β} {s : Set α} (hs : IsCompact s) (
hf : LocallyLipschitzOn s f) : exists K, L…
· 使用引理 `ContDiffOn.locallyLipschitzOn`：ContDiffOn.locallyLipschitzOn {f : E -> F
} {s : Set E} (hs : Convex Real s) (hf : ContDiffOn Real 1 f s) : LocallyLipschi
tzOn s f
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENat.one_le_iff_ne_zero_withTop`：one_le_iff_ne_zero_withTop {n : WithTop
 Nat∞} : 1 <= n ↔ n != 0

--- 原说明 ---
If `f` is `C¹` on a convex compact set `s`, it is Lipschitz on `s`.
-/
theorem ContDiffOn.exists_lipschitzOnWith {s : Set E} {f : E → F} {n} (hf : ContDiffOn ℝ n f s)
    (hn : n ≠ 0) (hs : Convex ℝ s) (hs' : IsCompact s) :
    ∃ K, LipschitzOnWith K f s := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs'
  exact (hf.of_le <| ENat.one_le_iff_ne_zero_withTop.2 hn).locallyLipschitzOn hs

/-- A `C^n` function with compact support is Lipschitz. -/
/-
**ContDiff.lipschitzWith_of_hasCompactSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.lipschitzWith_of_hasCompactSupport {f : E' -> F'} (hf : HasCompac
tSupport f) (h'f : ContDiff 𝕂 n f) (hn : n != 0) : exists C, LipschitzWith C f
参数：hf : HasCompactSupport f；h'f : ContDiff 𝕂 n f；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactSupport.exists_bound_of_continuous`：∀ {α : Type u_1} {E : Type
 u_2} [inst : SeminormedAddGroup E] [inst_1 : TopologicalSpace α] {f : α → E},  
 HasCompactSupport f → Continuous …
· 使用定理 `HasCompactSupport.fderiv`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [i
nst_3 : Topolo…
· 使用定理 `ContDiff.continuous_fderiv`：ContDiff.continuous_fderiv (h : ContDiff 𝕜 n
 f) (hn : n != 0) : Continuous (fderiv 𝕜 f)
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `lipschitzWith_of_nnnorm_fderiv_le`：∀ {𝕜 : Type u_3} {G : Type u_4} [inst
 : NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]   [inst_2 : NormedAddCommG
roup G] [inst_3 : Norme…
· 使用定理 `instIsRCLikeNormedField`：∀ (𝕜 : Type u_3) [h : RCLike 𝕜], IsRCLikeNormed
Field 𝕜
· 使用定理 `ContDiff.differentiable`：ContDiff.differentiable (h : ContDiff 𝕜 n f) (h
n : n != 0) : Differentiable 𝕜 f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True

--- 原说明 ---
A `C^n` function with compact support is Lipschitz.
-/
theorem ContDiff.lipschitzWith_of_hasCompactSupport {f : E' → F'}
    (hf : HasCompactSupport f) (h'f : ContDiff 𝕂 n f) (hn : n ≠ 0) :
    ∃ C, LipschitzWith C f := by
  obtain ⟨C, hC⟩ := (hf.fderiv 𝕂).exists_bound_of_continuous (h'f.continuous_fderiv hn)
  refine ⟨.mk (max C 0) (le_max_right _ _), ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (h'f.differentiable hn) (fun x ↦ ?_)
  simp [← NNReal.coe_le_coe, hC x]

end Real

