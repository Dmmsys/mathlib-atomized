/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.CPolynomial
public import Mathlib.Analysis.Analytic.Inverse
public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# Fréchet derivatives of analytic functions.

A function expressible as a power series at a point has a Fréchet derivative there.
Also the special case in terms of `deriv` when the domain is 1-dimensional.

As an application, we show that continuous multilinear maps are smooth. We also compute their
iterated derivatives, in `ContinuousMultilinearMap.iteratedFDeriv_eq`.

## Main definitions and results

* `AnalyticAt.differentiableAt` : an analytic function at a point is differentiable there.
* `AnalyticOnNhd.fderiv` : in a complete space, if a function is analytic on a
  neighborhood of a set `s`, so is its derivative.
* `AnalyticOnNhd.fderiv_of_isOpen` : if a function is analytic on a neighborhood of an
  open set `s`, so is its derivative.
* `AnalyticOn.fderivWithin` : if a function is analytic on a set of unique differentiability,
  so is its derivative within this set.
* `OpenPartialHomeomorph.analyticAt_symm` : if an open partial homeomorphism `f` is analytic at a
  point `f.symm a`, with invertible derivative, then its inverse is analytic at `a`.

## Comments on completeness

Some theorems need a complete space, some don't, for the following reason.

(1) If a function is analytic at a point `x`, then it is differentiable there (with derivative given
by the first term in the power series). There is no issue of convergence here.

(2) If a function has a power series on a ball `B (x, r)`, there is no guarantee that the power
series for the derivative will converge at `y ≠ x`, if the space is not complete. So, to deduce
that `f` is differentiable at `y`, one needs completeness in general.

(3) However, if a function `f` has a power series on a ball `B (x, r)`, and is a priori known to be
differentiable at some point `y ≠ x`, then the power series for the derivative of `f` will
automatically converge at `y`, towards the given derivative: this follows from the facts that this
is true in the completion (thanks to the previous point) and that the map to the completion is
an embedding.

(4) Therefore, if one assumes `AnalyticOn 𝕜 f s` where `s` is an open set, then `f` is analytic
therefore differentiable at every point of `s`, by (1), so by (3) the power series for its
derivative converges on whole balls. Therefore, the derivative of `f` is also analytic on `s`. The
same holds if `s` is merely a set with unique differentials.

(5) However, this does not work for `AnalyticOnNhd 𝕜 f s`, as we don't get for free
differentiability at points in a neighborhood of `s`. Therefore, the theorem that deduces
`AnalyticOnNhd 𝕜 (fderiv 𝕜 f) s` from `AnalyticOnNhd 𝕜 f s` requires completeness of the space.

-/

public section

open Filter Asymptotics Set

open scoped ENNReal Topology

universe u v

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞}
variable {f : E → F} {x : E} {s : Set E}

/-- A function which is analytic within a set is strictly differentiable there. Since we
don't have a predicate `HasStrictFDerivWithinAt`, we spell out what it would mean. -/
/-
**HasFPowerSeriesWithinAt.hasStrictFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.hasStrictFDerivWithinAt (h : HasFPowerSeriesWithin
At f p s x) : (fun y => f y.1 - f y.2 - (continuousMultilinearCurryFin1 𝕜 E F (p
 1)) (y.1 - y.2)) =o[𝓝[insert x s ×ˢ insert x s] (x, x)] fun y => y.1 - y.2
参数：h : HasFPowerSeriesWithinAt f p s x。
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
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `HasFPowerSeriesWithinAt.isBigO_image_sub_norm_mul_norm_sub`：HasFPowerSer
iesWithinAt.isBigO_image_sub_norm_mul_norm_sub (hf : HasFPowerSeriesWithinAt f p
 s x) : (fun y : E × E => f y.1 - f y.2 - p 1 fu…
· 使用定理 `Asymptotics.IsLittleO.of_norm_right`：∀ {α : Type u_1} {E : Type u_3} {F'
 : Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   
{g' : α → F'} {l : Filter…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_iff_exists_eq_mul`：isLittleO_iff_exists_eq_mul : u
 =o[l] v ↔ exists φ : α -> 𝕜, Tendsto φ l (𝓝 0) ∧ u =ᶠ[l] φ * v
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `Prod.instIsTopologicalAddGroup`：∀ {G : Type w} {H : Type x} [inst : Topo
logicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [inst_3 : Topo
logicalSpace H] [ins…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f

--- 原说明 ---
A function which is analytic within a set is strictly differentiable there. Sinc
e we
don't have a predicate `HasStrictFDerivWithinAt`, we spell out what it would mea
n.
-/
theorem HasFPowerSeriesWithinAt.hasStrictFDerivWithinAt (h : HasFPowerSeriesWithinAt f p s x) :
    (fun y ↦ f y.1 - f y.2 - (continuousMultilinearCurryFin1 𝕜 E F (p 1)) (y.1 - y.2))
      =o[𝓝[insert x s ×ˢ insert x s] (x, x)] fun y ↦ y.1 - y.2 := by
  refine h.isBigO_image_sub_norm_mul_norm_sub.trans_isLittleO (IsLittleO.of_norm_right ?_)
  refine isLittleO_iff_exists_eq_mul.2 ⟨fun y => ‖y - (x, x)‖, ?_, EventuallyEq.rfl⟩
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  refine (continuous_id.fun_sub continuous_const).norm.tendsto' _ _ ?_
  rw [_root_.id, sub_self, norm_zero]
/-
**HasFPowerSeriesAt.hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.hasStrictFDerivAt (h : HasFPowerSeriesAt f p x) : HasStr
ictFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x
参数：h : HasFPowerSeriesAt f p x。
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
· 使用定理 `HasFPowerSeriesWithinAt.hasStrictFDerivWithinAt`：HasFPowerSeriesWithinAt
.hasStrictFDerivWithinAt (h : HasFPowerSeriesWithinAt f p s x) : (fun y => f y.1
 - f y.2 - (continuousMultilinearCurr…
· 使用引理 `HasFPowerSeriesAt.hasFPowerSeriesWithinAt`：HasFPowerSeriesAt.hasFPowerSe
riesWithinAt (hf : HasFPowerSeriesAt f p x) : HasFPowerSeriesWithinAt f p s x
-/
theorem HasFPowerSeriesAt.hasStrictFDerivAt (h : HasFPowerSeriesAt f p x) :
    HasStrictFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x := by
  simpa only [hasStrictFDerivAt_iff_isLittleO, Set.insert_eq_of_mem, Set.mem_univ,
      Set.univ_prod_univ, nhdsWithin_univ]
    using (h.hasFPowerSeriesWithinAt (s := Set.univ)).hasStrictFDerivWithinAt
/-
**HasFPowerSeriesWithinAt.hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.hasFDerivWithinAt (h : HasFPowerSeriesWithinAt f p
 s x) : HasFDerivWithinAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) (insert
 x s) x
参数：h : HasFPowerSeriesWithinAt f p s x。
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
· 使用定理 `hasFDerivWithinAt_iff_isLittleO`：hasFDerivWithinAt_iff_isLittleO : HasFD
erivWithinAt f f' s x ↔ (fun x' => f x' - f x - f' (x' - x)) =o[𝓝[s] x] (fun x' 
=> x' - x)
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `nhdsWithin_prod_eq`：nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : 
Set Y) : 𝓝[s ×ˢ t] (x, y) = 𝓝[s] x ×ˢ 𝓝[t] y
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_const_nhdsWithin`：tendsto_const_nhdsWithin {l : Filter β} {s : S
et α} {a : α} (ha : a in s) : Tendsto (fun _ : β => a) l (𝓝[s] a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `HasFPowerSeriesWithinAt.hasStrictFDerivWithinAt`：HasFPowerSeriesWithinAt
.hasStrictFDerivWithinAt (h : HasFPowerSeriesWithinAt f p s x) : (fun y => f y.1
 - f y.2 - (continuousMultilinearCurr…
-/
theorem HasFPowerSeriesWithinAt.hasFDerivWithinAt (h : HasFPowerSeriesWithinAt f p s x) :
    HasFDerivWithinAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) (insert x s) x := by
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have : Tendsto (fun y ↦ (y, x)) (𝓝[insert x s] x) (𝓝[insert x s ×ˢ insert x s] (x, x)) := by
    rw [nhdsWithin_prod_eq]
    exact Tendsto.prodMk tendsto_id (tendsto_const_nhdsWithin (by simp))
  exact this (isLittleO_iff.1 h.hasStrictFDerivWithinAt hc)
/-
**HasFPowerSeriesAt.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.hasFDerivAt (h : HasFPowerSeriesAt f p x) : HasFDerivAt 
f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x
参数：h : HasFPowerSeriesAt f p x。
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
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `HasFPowerSeriesAt.hasStrictFDerivAt`：HasFPowerSeriesAt.hasStrictFDerivAt
 (h : HasFPowerSeriesAt f p x) : HasStrictFDerivAt f (continuousMultilinearCurry
Fin1 𝕜 E F (p 1)) x
-/
theorem HasFPowerSeriesAt.hasFDerivAt (h : HasFPowerSeriesAt f p x) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x :=
  h.hasStrictFDerivAt.hasFDerivAt
/-
**HasFPowerSeriesWithinAt.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.differentiableWithinAt (h : HasFPowerSeriesWithinA
t f p s x) : DifferentiableWithinAt 𝕜 f (insert x s) x
参数：h : HasFPowerSeriesWithinAt f p s x。
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
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFPowerSeriesWithinAt.hasFDerivWithinAt`：HasFPowerSeriesWithinAt.hasFD
erivWithinAt (h : HasFPowerSeriesWithinAt f p s x) : HasFDerivWithinAt f (contin
uousMultilinearCurryFin1 𝕜 E F …
-/
theorem HasFPowerSeriesWithinAt.differentiableWithinAt (h : HasFPowerSeriesWithinAt f p s x) :
    DifferentiableWithinAt 𝕜 f (insert x s) x :=
  h.hasFDerivWithinAt.differentiableWithinAt
/-
**HasFPowerSeriesAt.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.differentiableAt (h : HasFPowerSeriesAt f p x) : Differe
ntiableAt 𝕜 f x
参数：h : HasFPowerSeriesAt f p x。
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
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasFPowerSeriesAt.hasFDerivAt`：HasFPowerSeriesAt.hasFDerivAt (h : HasFPo
werSeriesAt f p x) : HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) 
x
-/
theorem HasFPowerSeriesAt.differentiableAt (h : HasFPowerSeriesAt f p x) : DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt
/-
**AnalyticWithinAt.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.differentiableWithinAt (h : AnalyticWithinAt 𝕜 f s x) : D
ifferentiableWithinAt 𝕜 f (insert x s) x
参数：h : AnalyticWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesWithinAt.differentiableWithinAt`：HasFPowerSeriesWithinAt.
differentiableWithinAt (h : HasFPowerSeriesWithinAt f p s x) : DifferentiableWit
hinAt 𝕜 f (insert x s) x
-/
theorem AnalyticWithinAt.differentiableWithinAt (h : AnalyticWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 f (insert x s) x := by
  obtain ⟨p, hp⟩ := h
  exact hp.differentiableWithinAt

@[fun_prop]
/-
**AnalyticAt.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {x : E}, AnalyticAt 𝕜 
f x → DifferentiableAt 𝕜 f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesAt.differentiableAt`：HasFPowerSeriesAt.differentiableAt (
h : HasFPowerSeriesAt f p x) : DifferentiableAt 𝕜 f x
-/
theorem AnalyticAt.differentiableAt : AnalyticAt 𝕜 f x → DifferentiableAt 𝕜 f x
  | ⟨_, hp⟩ => hp.differentiableAt
/-
**AnalyticAt.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.differentiableWithinAt (h : AnalyticAt 𝕜 f x) : DifferentiableW
ithinAt 𝕜 f s x
参数：h : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […
-/
theorem AnalyticAt.differentiableWithinAt (h : AnalyticAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x :=
  h.differentiableAt.differentiableWithinAt
/-
**HasFPowerSeriesWithinAt.fderivWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.fderivWithin_eq (h : HasFPowerSeriesWithinAt f p s
 x) (hu : UniqueDiffWithinAt 𝕜 (insert x s) x) : fderivWithin 𝕜 f (insert x s) x
 = continuousMultilinearCurryFin1 𝕜 E F (p 1)
参数：h : HasFPowerSeriesWithinAt f p s x；hu : UniqueDiffWithinAt 𝕜 (insert x s) x。
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
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFPowerSeriesWithinAt.hasFDerivWithinAt`：HasFPowerSeriesWithinAt.hasFD
erivWithinAt (h : HasFPowerSeriesWithinAt f p s x) : HasFDerivWithinAt f (contin
uousMultilinearCurryFin1 𝕜 E F …
-/
theorem HasFPowerSeriesWithinAt.fderivWithin_eq
    (h : HasFPowerSeriesWithinAt f p s x) (hu : UniqueDiffWithinAt 𝕜 (insert x s) x) :
    fderivWithin 𝕜 f (insert x s) x = continuousMultilinearCurryFin1 𝕜 E F (p 1) :=
  h.hasFDerivWithinAt.fderivWithin hu
/-
**HasFPowerSeriesAt.fderiv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.fderiv_eq (h : HasFPowerSeriesAt f p x) : fderiv 𝕜 f x =
 continuousMultilinearCurryFin1 𝕜 E F (p 1)
参数：h : HasFPowerSeriesAt f p x。
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
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFPowerSeriesAt.hasFDerivAt`：HasFPowerSeriesAt.hasFDerivAt (h : HasFPo
werSeriesAt f p x) : HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) 
x
-/
theorem HasFPowerSeriesAt.fderiv_eq (h : HasFPowerSeriesAt f p x) :
    fderiv 𝕜 f x = continuousMultilinearCurryFin1 𝕜 E F (p 1) :=
  h.hasFDerivAt.fderiv
/-
**AnalyticAt.hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.hasStrictFDerivAt (h : AnalyticAt 𝕜 f x) : HasStrictFDerivAt f 
(fderiv 𝕜 f x) x
参数：h : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HasFPowerSeriesAt.fderiv_eq`：HasFPowerSeriesAt.fderiv_eq (h : HasFPowerS
eriesAt f p x) : fderiv 𝕜 f x = continuousMultilinearCurryFin1 𝕜 E F (p 1)
· 使用定理 `HasFPowerSeriesAt.hasStrictFDerivAt`：HasFPowerSeriesAt.hasStrictFDerivAt
 (h : HasFPowerSeriesAt f p x) : HasStrictFDerivAt f (continuousMultilinearCurry
Fin1 𝕜 E F (p 1)) x
-/
theorem AnalyticAt.hasStrictFDerivAt (h : AnalyticAt 𝕜 f x) :
    HasStrictFDerivAt f (fderiv 𝕜 f x) x := by
  rcases h with ⟨p, hp⟩
  rw [hp.fderiv_eq]
  exact hp.hasStrictFDerivAt
/-
**AnalyticAt.hasStrictDerivAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.hasStrictDerivAt {f : 𝕜 -> F} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
 HasStrictDerivAt f (deriv f x) x
参数：hf : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toSpanSingleton_deriv`：toSpanSingleton_deriv : toSpanSingleton 𝕜 (deriv 
f x) = fderiv 𝕜 f x
· 使用定理 `AnalyticAt.hasStrictFDerivAt`：AnalyticAt.hasStrictFDerivAt (h : Analytic
At 𝕜 f x) : HasStrictFDerivAt f (fderiv 𝕜 f x) x
-/
lemma AnalyticAt.hasStrictDerivAt {f : 𝕜 → F} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
    HasStrictDerivAt f (deriv f x) x := by
  simpa [hasStrictDerivAt_iff_hasStrictFDerivAt, toSpanSingleton_deriv] using hf.hasStrictFDerivAt
/-
**HasFPowerSeriesWithinOnBall.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.differentiableOn [CompleteSpace F] (h : HasFPo
werSeriesWithinOnBall f p s x r) : DifferentiableOn 𝕜 f (insert x s inter Metric
.eball x r)
参数：h : HasFPowerSeriesWithinOnBall f p s x r。
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
· 使用定理 `AnalyticWithinAt.differentiableWithinAt`：AnalyticWithinAt.differentiable
WithinAt (h : AnalyticWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 f (insert x s
) x
· 使用定理 `HasFPowerSeriesWithinOnBall.analyticWithinAt_of_mem`：HasFPowerSeriesWith
inOnBall.analyticWithinAt_of_mem (hf : HasFPowerSeriesWithinOnBall f p s x r) (h
 : y in insert x s inter Metric.eball x r…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `DifferentiableWithinAt.mono`：DifferentiableWithinAt.mono (h : Differenti
ableWithinAt 𝕜 f t x) (st : s subseteq t) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `DifferentiableWithinAt.mono_of_mem_nhdsWithin`：DifferentiableWithinAt.mo
no_of_mem_nhdsWithin (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E} (hst : s i
n 𝓝[t] x) : DifferentiableWithinAt …
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
-/
theorem HasFPowerSeriesWithinOnBall.differentiableOn [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r) :
    DifferentiableOn 𝕜 f (insert x s ∩ Metric.eball x r) := by
  intro y hy
  have Z := (h.analyticWithinAt_of_mem hy).differentiableWithinAt
  rcases eq_or_ne y x with rfl | hy
  · exact Z.mono inter_subset_left
  · apply (Z.mono (subset_insert _ _)).mono_of_mem_nhdsWithin
    suffices s ∈ 𝓝[insert x s] y from nhdsWithin_mono _ inter_subset_left this
    rw [nhdsWithin_insert_of_ne hy]
    exact self_mem_nhdsWithin
/-
**HasFPowerSeriesOnBall.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.differentiableOn [CompleteSpace F] (h : HasFPowerSer
iesOnBall f p x r) : DifferentiableOn 𝕜 f (Metric.eball x r)
参数：h : HasFPowerSeriesOnBall f p x r。
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
· 使用定理 `AnalyticAt.differentiableWithinAt`：AnalyticAt.differentiableWithinAt (h 
: AnalyticAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFPowerSeriesOnBall.analyticAt_of_mem`：HasFPowerSeriesOnBall.analyticA
t_of_mem (hf : HasFPowerSeriesOnBall f p x r) (h : y in Metric.eball x r) : Anal
yticAt 𝕜 f y
-/
theorem HasFPowerSeriesOnBall.differentiableOn [CompleteSpace F]
    (h : HasFPowerSeriesOnBall f p x r) : DifferentiableOn 𝕜 f (Metric.eball x r) := fun _ hy =>
  (h.analyticAt_of_mem hy).differentiableWithinAt
/-
**HasFPowerSeriesAt.eventually_differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.eventually_differentiableAt [CompleteSpace F] (hp : HasF
PowerSeriesAt f p x) : forallᶠ z in 𝓝 x, DifferentiableAt 𝕜 f z
参数：hp : HasFPowerSeriesAt f p x。
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
· 使用定理 `DifferentiableOn.eventually_differentiableAt`：DifferentiableOn.eventuall
y_differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : forallᶠ y in 𝓝
 x, DifferentiableAt 𝕜 f y
· 使用定理 `HasFPowerSeriesOnBall.differentiableOn`：HasFPowerSeriesOnBall.differenti
ableOn [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r) : DifferentiableOn 
𝕜 f (Metric.eball x r)
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
-/
theorem HasFPowerSeriesAt.eventually_differentiableAt
    [CompleteSpace F] (hp : HasFPowerSeriesAt f p x) :
    ∀ᶠ z in 𝓝 x, DifferentiableAt 𝕜 f z := by
  obtain ⟨r, hp⟩ := hp
  exact hp.differentiableOn.eventually_differentiableAt (Metric.eball_mem_nhds _ hp.r_pos)
/-
**AnalyticOn.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.differentiableOn (h : AnalyticOn 𝕜 f s) : DifferentiableOn 𝕜 f 
s
参数：h : AnalyticOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.mono`：DifferentiableWithinAt.mono (h : Differenti
ableWithinAt 𝕜 f t x) (st : s subseteq t) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `AnalyticWithinAt.differentiableWithinAt`：AnalyticWithinAt.differentiable
WithinAt (h : AnalyticWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 f (insert x s
) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem AnalyticOn.differentiableOn (h : AnalyticOn 𝕜 f s) : DifferentiableOn 𝕜 f s :=
  fun y hy ↦ (h y hy).differentiableWithinAt.mono (by simp)
/-
**AnalyticOnNhd.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.differentiableOn (h : AnalyticOnNhd 𝕜 f s) : DifferentiableO
n 𝕜 f s
参数：h : AnalyticOnNhd 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.differentiableWithinAt`：AnalyticAt.differentiableWithinAt (h 
: AnalyticAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
-/
theorem AnalyticOnNhd.differentiableOn (h : AnalyticOnNhd 𝕜 f s) : DifferentiableOn 𝕜 f s :=
  fun y hy ↦ (h y hy).differentiableWithinAt
/-
**HasFPowerSeriesWithinOnBall.hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.hasFDerivWithinAt [CompleteSpace F] (h : HasFP
owerSeriesWithinOnBall f p s x r) {y : E} (hy : (‖y‖₊ : Real>=0∞) < r) (h'y : x 
+ y in insert x s) : HasFDerivWithinAt f (continuousMultilinearCurryFin1 𝕜 E F (
p.changeOrigin y 1)) (insert x s) (x + y)
参数：h : HasFPowerSeriesWithinOnBall f p s x r；hy : (‖y‖₊ : Real>=0∞) < r；h'y : x 
+ y in insert x s。
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
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFPowerSeriesWithinAt.hasFDerivWithinAt`：HasFPowerSeriesWithinAt.hasFD
erivWithinAt (h : HasFPowerSeriesWithinAt f p s x) : HasFDerivWithinAt f (contin
uousMultilinearCurryFin1 𝕜 E F …
· 使用定理 `HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt`：HasFPowerSeriesWith
inOnBall.hasFPowerSeriesWithinAt (hf : HasFPowerSeriesWithinOnBall f p s x r) : 
HasFPowerSeriesWithinAt f p s x
· 使用定理 `HasFPowerSeriesWithinOnBall.changeOrigin`：HasFPowerSeriesWithinOnBall.ch
angeOrigin (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : ‖y‖ₑ < r) (hy : x +
 y in insert x s) : HasFPowerS…
· 使用定理 `HasFDerivWithinAt.mono_of_mem_nhdsWithin`：HasFDerivWithinAt.mono_of_mem_
nhdsWithin (h : HasFDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasFDerivWithi
nAt f f' s x
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `nhdsWithin_insert_of_ne`：nhdsWithin_insert_of_ne [T1Space X] {x y : X} {
s : Set X} (hxy : x != y) : 𝓝[insert y s] x = 𝓝[s] x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem HasFPowerSeriesWithinOnBall.hasFDerivWithinAt [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) (h'y : x + y ∈ insert x s) :
    HasFDerivWithinAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1))
      (insert x s) (x + y) := by
  rcases eq_or_ne y 0 with rfl | h''y
  · convert! (h.changeOrigin hy h'y).hasFPowerSeriesWithinAt.hasFDerivWithinAt
    simp
  · have Z := (h.changeOrigin hy h'y).hasFPowerSeriesWithinAt.hasFDerivWithinAt
    apply (Z.mono (subset_insert _ _)).mono_of_mem_nhdsWithin
    rw [nhdsWithin_insert_of_ne]
    · exact self_mem_nhdsWithin
    · simpa using h''y
/-
**HasFPowerSeriesOnBall.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.hasFDerivAt [CompleteSpace F] (h : HasFPowerSeriesOn
Ball f p x r) {y : E} (hy : (‖y‖₊ : Real>=0∞) < r) : HasFDerivAt f (continuousMu
ltilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y)
参数：h : HasFPowerSeriesOnBall f p x r；hy : (‖y‖₊ : Real>=0∞) < r。
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
· 使用定理 `HasFPowerSeriesAt.hasFDerivAt`：HasFPowerSeriesAt.hasFDerivAt (h : HasFPo
werSeriesAt f p x) : HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) 
x
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
· 使用定理 `HasFPowerSeriesOnBall.changeOrigin`：HasFPowerSeriesOnBall.changeOrigin (
hf : HasFPowerSeriesOnBall f p x r) (h : (‖y‖₊ : Real>=0∞) < r) : HasFPowerSerie
sOnBall f (p.changeOrigi…
-/
theorem HasFPowerSeriesOnBall.hasFDerivAt [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y) :=
  (h.changeOrigin hy).hasFPowerSeriesAt.hasFDerivAt
/-
**HasFPowerSeriesWithinOnBall.fderivWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.fderivWithin_eq [CompleteSpace F] (h : HasFPow
erSeriesWithinOnBall f p s x r) {y : E} (hy : (‖y‖₊ : Real>=0∞) < r) (h'y : x + 
y in insert x s) (hu : UniqueDiffOn 𝕜 (insert x s)) : fderivWithin 𝕜 f (insert x
 s) (x + y) = continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)
参数：h : HasFPowerSeriesWithinOnBall f p s x r；hy : (‖y‖₊ : Real>=0∞) < r；h'y : x 
+ y in insert x s；hu : UniqueDiffOn 𝕜 (insert x s)。
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
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFPowerSeriesWithinOnBall.hasFDerivWithinAt`：HasFPowerSeriesWithinOnBa
ll.hasFDerivWithinAt [CompleteSpace F] (h : HasFPowerSeriesWithinOnBall f p s x 
r) {y : E} (hy : (‖y‖₊ : Real>=0∞) …
-/
theorem HasFPowerSeriesWithinOnBall.fderivWithin_eq [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) (h'y : x + y ∈ insert x s) (hu : UniqueDiffOn 𝕜 (insert x s)) :
    fderivWithin 𝕜 f (insert x s) (x + y) =
      continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1) :=
  (h.hasFDerivWithinAt hy h'y).fderivWithin (hu _ h'y)
/-
**HasFPowerSeriesOnBall.fderiv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.fderiv_eq [CompleteSpace F] (h : HasFPowerSeriesOnBa
ll f p x r) {y : E} (hy : (‖y‖₊ : Real>=0∞) < r) : fderiv 𝕜 f (x + y) = continuo
usMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)
参数：h : HasFPowerSeriesOnBall f p x r；hy : (‖y‖₊ : Real>=0∞) < r。
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
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFPowerSeriesOnBall.hasFDerivAt`：HasFPowerSeriesOnBall.hasFDerivAt [Co
mpleteSpace F] (h : HasFPowerSeriesOnBall f p x r) {y : E} (hy : (‖y‖₊ : Real>=0
∞) < r) : HasFDerivAt f…
-/
theorem HasFPowerSeriesOnBall.fderiv_eq [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    fderiv 𝕜 f (x + y) = continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1) :=
  (h.hasFDerivAt hy).fderiv

/-- If a function has a power series on a ball, then so does its derivative. -/
/-
**HasFPowerSeriesOnBall.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerSeriesOnBall`
。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   {p : FormalMultilinearSeries 𝕜 E F
} {r : ENNReal} {f : E → F} {x : E} [CompleteSpace F],   HasFPowerSeriesOnBall f
 p x r → HasFPowerSeriesOnBall (fderiv 𝕜 f) p.derivSeries x r
参数：fderiv 𝕜 f。
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
· 使用定理 `ContinuousLinearMap.comp_hasFPowerSeriesOnBall`：ContinuousLinearMap.comp
_hasFPowerSeriesOnBall (g : F ->L[𝕜] G) (h : HasFPowerSeriesOnBall f p x r) : Ha
sFPowerSeriesOnBall (g ∘ f) (g.compF…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasFPowerSeriesOnBall.comp_sub`：HasFPowerSeriesOnBall.comp_sub (hf : Has
FPowerSeriesOnBall f p x r) (y : E) : HasFPowerSeriesOnBall (fun z => f (z - y))
 p (x + y) r
· 使用定理 `HasFPowerSeriesOnBall.mono`：HasFPowerSeriesOnBall.mono (hf : HasFPowerSe
riesOnBall f p x r) (r'_pos : 0 < r') (hr : r' <= r) : HasFPowerSeriesOnBall f p
 x r'
· 使用定理 `FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin`：hasFPowerSer
iesOnBall_changeOrigin (k : Nat) (hr : 0 < p.radius) : HasFPowerSeriesOnBall (fu
n x => p.changeOrigin x k) (p.changeOriginSeries…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFPowerSeriesOnBall.fderiv_eq`：HasFPowerSeriesOnBall.fderiv_eq [Comple
teSpace F] (h : HasFPowerSeriesOnBall f p x r) {y : E} (hy : (‖y‖₊ : Real>=0∞) <
 r) : fderiv 𝕜 f (x +…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b

--- 原说明 ---
If a function has a power series on a ball, then so does its derivative.
-/
protected theorem HasFPowerSeriesOnBall.fderiv [CompleteSpace F]
    (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (fderiv 𝕜 f) p.derivSeries x r := by
  refine .congr (f := fun z ↦ continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin (z - x) 1)) ?_
    fun z hz ↦ ?_
  · refine continuousMultilinearCurryFin1 𝕜 E F
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesOnBall ?_
    simpa using! ((p.hasFPowerSeriesOnBall_changeOrigin 1
      (h.r_pos.trans_le h.r_le)).mono h.r_pos h.r_le).comp_sub x
  dsimp only
  rw [← h.fderiv_eq, add_sub_cancel]
  simpa only [edist_eq_enorm_sub, Metric.mem_eball] using! hz
/-
**FormalMultilinearSeries.fderiv_sum** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinea
rSeries`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   {p : FormalMultilinearSeries 𝕜 E F
} {x : E} [CompleteSpace F],   ‖x‖ₑ < p.radius → fderiv 𝕜 p.sum x = p.derivSerie
s.sum x
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasFPowerSeriesOnBall.sum`：HasFPowerSeriesOnBall.sum (h : HasFPowerSerie
sOnBall f p x r) {y : E} (hy : y in Metric.eball (0 : E) r) : f (x + y) = p.sum 
y
· 使用定理 `HasFPowerSeriesOnBall.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type v} […
· 使用定理 `FormalMultilinearSeries.hasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E : Typ
e u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddComm
Group E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
-/
protected theorem FormalMultilinearSeries.fderiv_sum [CompleteSpace F] (h : ‖x‖ₑ < p.radius) :
    fderiv 𝕜 p.sum x = p.derivSeries.sum x := by
  simpa using (p.hasFPowerSeriesOnBall (zero_le.trans_lt h)).fderiv.sum (by simpa using h)
/-
**FormalMultilinearSeries.hasFDerivAt_sum** 是 Mathlib 中的一个定理，位于命名空间 `FormalMulti
linearSeries`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   {p : FormalMultilinearSeries 𝕜 E F
} {x : E} [CompleteSpace F],   ‖x‖ₑ < p.radius → HasFDerivAt p.sum (p.derivSerie
s.sum x) x
参数：p.derivSeries.sum x。
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
· 使用定理 `FormalMultilinearSeries.fderiv_sum`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type v} […
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […
· 使用定理 `HasFPowerSeriesOnBall.analyticAt_of_mem`：HasFPowerSeriesOnBall.analyticA
t_of_mem (hf : HasFPowerSeriesOnBall f p x r) (h : y in Metric.eball x r) : Anal
yticAt 𝕜 f y
· 使用定理 `FormalMultilinearSeries.hasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E : Typ
e u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddComm
Group E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
-/
protected theorem FormalMultilinearSeries.hasFDerivAt_sum [CompleteSpace F] (h : ‖x‖ₑ < p.radius) :
    HasFDerivAt p.sum (p.derivSeries.sum x) x := by
  rw [← FormalMultilinearSeries.fderiv_sum h]
  exact p.hasFPowerSeriesOnBall (zero_le.trans_lt h)
    |>.analyticAt_of_mem (by simpa using h) |>.differentiableAt.hasFDerivAt

/-- If a function has a power series within a set on a ball, then so does its derivative. -/
/-
**HasFPowerSeriesWithinOnBall.fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerS
eriesWithinOnBall`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   {p : FormalMultilinearSeries 𝕜 E F
} {r : ENNReal} {f : E → F} {x : E} {s : Set E} [CompleteSpace F],   HasFPowerSe
riesWithinOnBall f p s x r →     UniqueDiffOn 𝕜 (insert x s) → HasFPowerSeriesWi
thinOnBall (fderivWithin 𝕜 f (insert x s)) p.derivSeries s x r
参数：insert x s；fderivWithin 𝕜 f (insert x s)。
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
· 使用引理 `HasFPowerSeriesWithinOnBall.congr'`：HasFPowerSeriesWithinOnBall.congr' {
f g : E -> F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : Real>
=0∞} (h : HasFPowerSerie…
· 使用定理 `ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall`：ContinuousLinearMa
p.comp_hasFPowerSeriesWithinOnBall (g : F ->L[𝕜] G) (h : HasFPowerSeriesWithinOn
Ball f p s x r) : HasFPowerSeriesWithinOnB…
· 使用引理 `HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall`：HasFPowerSeriesOnBall
.hasFPowerSeriesWithinOnBall (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSer
iesWithinOnBall f p s x r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasFPowerSeriesOnBall.comp_sub`：HasFPowerSeriesOnBall.comp_sub (hf : Has
FPowerSeriesOnBall f p x r) (y : E) : HasFPowerSeriesOnBall (fun z => f (z - y))
 p (x + y) r
· 使用定理 `HasFPowerSeriesOnBall.mono`：HasFPowerSeriesOnBall.mono (hf : HasFPowerSe
riesOnBall f p x r) (r'_pos : 0 < r') (hr : r' <= r) : HasFPowerSeriesOnBall f p
 x r'
· 使用定理 `FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin`：hasFPowerSer
iesOnBall_changeOrigin (k : Nat) (hr : 0 < p.radius) : HasFPowerSeriesOnBall (fu
n x => p.changeOrigin x k) (p.changeOriginSeries…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFPowerSeriesWithinOnBall.fderivWithin_eq`：HasFPowerSeriesWithinOnBall
.fderivWithin_eq [CompleteSpace F] (h : HasFPowerSeriesWithinOnBall f p s x r) {
y : E} (hy : (‖y‖₊ : Real>=0∞) < …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If a function has a power series within a set on a ball, then so does its deriva
tive.
-/
protected theorem HasFPowerSeriesWithinOnBall.fderivWithin [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r) (hu : UniqueDiffOn 𝕜 (insert x s)) :
    HasFPowerSeriesWithinOnBall (fderivWithin 𝕜 f (insert x s)) p.derivSeries s x r := by
  refine .congr' (f := fun z ↦ continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin (z - x) 1)) ?_
    (fun z hz ↦ ?_)
  · refine continuousMultilinearCurryFin1 𝕜 E F
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall ?_
    apply HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall
    simpa using! ((p.hasFPowerSeriesOnBall_changeOrigin 1
      (h.r_pos.trans_le h.r_le)).mono h.r_pos h.r_le).comp_sub x
  · dsimp only
    rw [← h.fderivWithin_eq _ _ hu, add_sub_cancel]
    · simpa only [edist_eq_enorm_sub, Metric.mem_eball] using! hz.2
    · simpa using! hz.1

/-- If a function has a power series within a set on a ball, then so does its derivative. For a
version without completeness, but assuming that the function is analytic on the set `s`, see
`HasFPowerSeriesWithinOnBall.fderivWithin_of_mem_of_analyticOn`. -/
/-
**HasFPowerSeriesWithinOnBall.fderivWithin_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Has
FPowerSeriesWithinOnBall`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   {p : FormalMultilinearSeries 𝕜 E F
} {r : ENNReal} {f : E → F} {x : E} {s : Set E} [CompleteSpace F],   HasFPowerSe
riesWithinOnBall f p s x r →     UniqueDiffOn 𝕜 s → x ∈ s → HasFPowerSeriesWithi
nOnBall (fderivWithin 𝕜 f s) p.derivSeries s x r
参数：fderivWithin 𝕜 f s。
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
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFPowerSeriesWithinOnBall.fderivWithin`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {F : Type v} […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If a function has a power series within a set on a ball, then so does its deriva
tive. For a
version without completeness, but assuming that the function is analytic on the 
set `s`, see
`HasFPowerSeriesWithinOnBall.fderivWithin_of_mem_of_analyticOn`.
-/
protected theorem HasFPowerSeriesWithinOnBall.fderivWithin_of_mem [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r) (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    HasFPowerSeriesWithinOnBall (fderivWithin 𝕜 f s) p.derivSeries s x r := by
  have : insert x s = s := insert_eq_of_mem hx
  rw [← this] at hu
  convert! h.fderivWithin hu
  exact this.symm

/-- If a function is analytic on a set `s`, so is its Fréchet derivative. -/
@[fun_prop]
/-
**AnalyticAt.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {x : E}   [CompleteSpace
 F], AnalyticAt 𝕜 f x → AnalyticAt 𝕜 (fderiv 𝕜 f) x
参数：fderiv 𝕜 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesOnBall.analyticAt`：HasFPowerSeriesOnBall.analyticAt (hf :
 HasFPowerSeriesOnBall f p x r) : AnalyticAt 𝕜 f x
· 使用定理 `HasFPowerSeriesOnBall.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type v} […

--- 原说明 ---
If a function is analytic on a set `s`, so is its Fréchet derivative.
-/
protected theorem AnalyticAt.fderiv [CompleteSpace F] (h : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (fderiv 𝕜 f) x := by
  rcases h with ⟨p, r, hp⟩
  exact hp.fderiv.analyticAt

/-- If a function is analytic on a set `s`, so is its Fréchet derivative. See also
`AnalyticOnNhd.fderiv_of_isOpen`, removing the completeness assumption but requiring the set
to be open. -/
/-
**AnalyticOnNhd.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticOnNhd`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {s : Set E} [CompleteS
pace F], AnalyticOnNhd 𝕜 f s → AnalyticOnNhd 𝕜 (fderiv 𝕜 f) s
参数：fderiv 𝕜 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {
E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Ty
pe v} […

--- 原说明 ---
If a function is analytic on a set `s`, so is its Fréchet derivative. See also
`AnalyticOnNhd.fderiv_of_isOpen`, removing the completeness assumption but requi
ring the set
to be open.
-/
protected theorem AnalyticOnNhd.fderiv [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (fderiv 𝕜 f) s :=
  fun y hy ↦ AnalyticAt.fderiv (h y hy)

/-- If a function is analytic on a set `s`, so are its successive Fréchet derivative. See also
`AnalyticOnNhd.iteratedFDeriv_of_isOpen`, removing the completeness assumption but requiring the set
to be open. -/
/-
**AnalyticOnNhd.iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticOnNhd`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {s : Set E} [CompleteS
pace F], AnalyticOnNhd 𝕜 f s → ∀ (n : ℕ), AnalyticOnNhd 𝕜 (iteratedFDeriv 𝕜 n f)
 s
参数：n : ℕ；iteratedFDeriv 𝕜 n f。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iteratedFDeriv_zero_eq_comp`：iteratedFDeriv_zero_eq_comp : iteratedFDeri
v 𝕜 0 f = (continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f
· 使用定理 `ContinuousLinearMap.comp_analyticOnNhd`：ContinuousLinearMap.comp_analyti
cOnNhd {s : Set E} (g : F ->L[𝕜] G) (h : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 
(g ∘ f) s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `iteratedFDeriv_succ_eq_comp_left`：iteratedFDeriv_succ_eq_comp_left {n : 
Nat} : iteratedFDeriv 𝕜 (n + 1) f = (continuousMultilinearCurryLeftEquiv 𝕜 (fun 
_ : Fin (n + 1) => E) …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AnalyticOnNhd.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type v} […
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.instFirstCountableTopologyForallOfCountable`：∀ {ι : Typ
e u_1} {X : ι → Type u_2} [Countable ι] [inst : (i : ι) → TopologicalSpace (X i)
]   [∀ (i : ι), FirstCountableTopology (X i)], Fir…
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α

--- 原说明 ---
If a function is analytic on a set `s`, so are its successive Fréchet derivative
. See also
`AnalyticOnNhd.iteratedFDeriv_of_isOpen`, removing the completeness assumption b
ut requiring the set
to be open.
-/
protected theorem AnalyticOnNhd.iteratedFDeriv [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s) (n : ℕ) :
    AnalyticOnNhd 𝕜 (iteratedFDeriv 𝕜 n f) s := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E [×0]→L[𝕜] F).comp_analyticOnNhd h
  | succ n IH =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    -- Porting note: for reasons that I do not understand at all, `?g` cannot be inlined.
    convert! ContinuousLinearMap.comp_analyticOnNhd ?g IH.fderiv
    case g => exact ↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) F).symm
    simp

/-- If a function is analytic on a neighborhood of a set `s`, then it has a Taylor series given
by the sequence of its derivatives. Note that, if the function were just analytic on `s`, then
one would have to use instead the sequence of derivatives inside the set, as in
`AnalyticOn.hasFTaylorSeriesUpToOn`. -/
/-
**AnalyticOnNhd.hasFTaylorSeriesUpToOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.hasFTaylorSeriesUpToOn [CompleteSpace F] (n : WithTop Nat∞) 
(h : AnalyticOnNhd 𝕜 f s) : HasFTaylorSeriesUpToOn n f (ftaylorSeries 𝕜 f) s
参数：n : WithTop Nat∞；h : AnalyticOnNhd 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […
· 使用定理 `AnalyticOnNhd.iteratedFDeriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type v} […
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
If a function is analytic on a neighborhood of a set `s`, then it has a Taylor s
eries given
by the sequence of its derivatives. Note that, if the function were just analyti
c on `s`, then
one would have to use instead the sequence of derivatives inside the set, as in
`AnalyticOn.hasFTaylorSeriesUpToOn`.
-/
lemma AnalyticOnNhd.hasFTaylorSeriesUpToOn [CompleteSpace F]
    (n : WithTop ℕ∞) (h : AnalyticOnNhd 𝕜 f s) :
    HasFTaylorSeriesUpToOn n f (ftaylorSeries 𝕜 f) s := by
  refine ⟨fun x _hx ↦ rfl, fun m _hm x hx ↦ ?_, fun m _hm x hx ↦ ?_⟩
  · apply HasFDerivAt.hasFDerivWithinAt
    exact ((h.iteratedFDeriv m x hx).differentiableAt).hasFDerivAt
  · apply (DifferentiableAt.continuousAt (𝕜 := 𝕜) ?_).continuousWithinAt
    exact (h.iteratedFDeriv m x hx).differentiableAt
/-
**AnalyticWithinAt.exists_hasFTaylorSeriesUpToOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.exists_hasFTaylorSeriesUpToOn [CompleteSpace F] (n : With
Top Nat∞) (h : AnalyticWithinAt 𝕜 f s x) : exists u in 𝓝[insert x s] x, exists (
p : E -> FormalMultilinearSeries 𝕜 E F), HasFTaylorSeriesUpToOn n f p u ∧ forall
 i, AnalyticOn 𝕜 (fun x => p x i) u
参数：n : WithTop Nat∞；h : AnalyticWithinAt 𝕜 f s x。
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
· 使用定理 `AnalyticWithinAt.exists_analyticAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} {F : Type u_3} [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `AnalyticAt.exists_mem_nhds_analyticOnNhd`：AnalyticAt.exists_mem_nhds_ana
lyticOnNhd (h : AnalyticAt 𝕜 f x) : exists s in 𝓝 x, AnalyticOnNhd 𝕜 f s
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用引理 `AnalyticOnNhd.hasFTaylorSeriesUpToOn`：AnalyticOnNhd.hasFTaylorSeriesUpTo
On [CompleteSpace F] (n : WithTop Nat∞) (h : AnalyticOnNhd 𝕜 f s) : HasFTaylorSe
riesUpToOn n f (ftaylorSer…
· 使用定理 `AnalyticOnNhd.mono`：AnalyticOnNhd.mono {s t : Set E} (hf : AnalyticOnNhd
 𝕜 f t) (hst : s subseteq t) : AnalyticOnNhd 𝕜 f s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `HasFTaylorSeriesUpToOn.congr`：HasFTaylorSeriesUpToOn.congr (h : HasFTayl
orSeriesUpToOn n f p s) (h₁ : forall x in s, f₁ x = f x) : HasFTaylorSeriesUpToO
n n f₁ p s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `AnalyticOn.mono`：AnalyticOn.mono {f : E -> F} {s t : Set E} (h : Analyti
cOn 𝕜 f t) (hs : s subseteq t) : AnalyticOn 𝕜 f s
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用定理 `AnalyticOnNhd.iteratedFDeriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type v} […
-/
lemma AnalyticWithinAt.exists_hasFTaylorSeriesUpToOn [CompleteSpace F]
    (n : WithTop ℕ∞) (h : AnalyticWithinAt 𝕜 f s x) :
    ∃ u ∈ 𝓝[insert x s] x, ∃ (p : E → FormalMultilinearSeries 𝕜 E F),
    HasFTaylorSeriesUpToOn n f p u ∧ ∀ i, AnalyticOn 𝕜 (fun x ↦ p x i) u := by
  rcases h.exists_analyticAt with ⟨g, -, fg, hg⟩
  rcases hg.exists_mem_nhds_analyticOnNhd with ⟨v, vx, hv⟩
  refine ⟨insert x s ∩ v, inter_mem_nhdsWithin _ vx, ftaylorSeries 𝕜 g, ?_, fun i ↦ ?_⟩
  · suffices HasFTaylorSeriesUpToOn n g (ftaylorSeries 𝕜 g) (insert x s ∩ v) from
      this.congr (fun y hy ↦ fg hy.1)
    exact AnalyticOnNhd.hasFTaylorSeriesUpToOn _ (hv.mono Set.inter_subset_right)
  · exact (hv.iteratedFDeriv i).analyticOn.mono Set.inter_subset_right

/-- If a function has a power series `p` within a set of unique differentiability, inside a ball,
and is differentiable at a point, then the derivative series of `p` is summable at a point, with
sum the given differential. Note that this theorem does not require completeness of the space. -/
/-
**HasFPowerSeriesWithinOnBall.hasSum_derivSeries_of_hasFDerivWithinAt** 是 Mathli
b 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.hasSum_derivSeries_of_hasFDerivWithinAt (h : H
asFPowerSeriesWithinOnBall f p s x r) {f' : E ->L[𝕜] F} {y : E} (hy : (‖y‖₊ : Re
al>=0∞) < r) (h'y : x + y in insert x s) (hf' : HasFDerivWithinAt f f' (insert x
 s) (x + y)) (hu : UniqueDiffOn 𝕜 (insert x s)) : HasSum (fun n => p.derivSeries
 n (fun _ => y)) f'
参数：h : HasFPowerSeriesWithinOnBall f p s x r；hy : (‖y‖₊ : Real>=0∞) < r；h'y : x 
+ y in insert x s；hf' : HasFDerivWithinAt f f' (insert x s) (x + y)；hu : UniqueD
iffOn 𝕜 (insert x s)。
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
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformSpace.Completion.instSMulCommClassOfUniformContinuousConstSMul`：∀
 (M : Type v) (N : Type w) (X : Type x) [inst : UniformSpace X] [inst_1 : SMul M
 X] [inst_2 : SMul N X]   [SMulCommClass M N X] [UniformCon…
· 使用定理 `UniformSpace.Completion.instUniformContinuousConstSMul`：∀ (M : Type v) (
X : Type x) [inst : UniformSpace X] [inst_1 : SMul M X],   UniformContinuousCons
tSMul M (UniformSpace.Completion X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Typ
e u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFi
lter β} [inst_2 : Ad…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用引理 `LinearIsometry.isEmbedding`：isEmbedding (f : F ->ₛₗᵢ[σ₁₂] E₂) : IsEmbedd
ing f
· 使用定理 `ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall`：ContinuousLinearMa
p.comp_hasFPowerSeriesWithinOnBall (g : F ->L[𝕜] G) (h : HasFPowerSeriesWithinOn
Ball f p s x r) : HasFPowerSeriesWithinOnB…
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.fderivWithin`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {F : Type v} […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `UniformSpace.Completion.instIsBoundedSMul`：∀ {α : Type u} [inst : Pseudo
MetricSpace α] {M : Type u_1} [inst_1 : Zero M] [inst_2 : Zero α] [inst_3 : SMul
 M α]   [inst_4 : PseudoMetricS…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If a function has a power series `p` within a set of unique differentiability, i
nside a ball,
and is differentiable at a point, then the derivative series of `p` is summable 
at a point, with
sum the given differential. Note that this theorem does not require completeness
 of the space.
-/
theorem HasFPowerSeriesWithinOnBall.hasSum_derivSeries_of_hasFDerivWithinAt
    (h : HasFPowerSeriesWithinOnBall f p s x r)
    {f' : E →L[𝕜] F}
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) (h'y : x + y ∈ insert x s)
    (hf' : HasFDerivWithinAt f f' (insert x s) (x + y))
    (hu : UniqueDiffOn 𝕜 (insert x s)) :
    HasSum (fun n ↦ p.derivSeries n (fun _ ↦ y)) f' := by
  /- In the completion of the space, the derivative series is summable, and its sum is a derivative
  of the function. Therefore, by uniqueness of derivatives, its sum is the image of `f'` under
  the canonical embedding. As this is an embedding, it means that there was also convergence in
  the original space, to `f'`. -/
  let F' := UniformSpace.Completion F
  let a : F →L[𝕜] F' := UniformSpace.Completion.toComplL
  let b : (E →L[𝕜] F) →ₗᵢ[𝕜] (E →L[𝕜] F') := UniformSpace.Completion.toComplₗᵢ.postcomp
  rw [← b.isEmbedding.hasSum_iff]
  have : HasFPowerSeriesWithinOnBall (a ∘ f) (a.compFormalMultilinearSeries p) s x r :=
    a.comp_hasFPowerSeriesWithinOnBall h
  have Z := (this.fderivWithin hu).hasSum h'y (by simpa [edist_zero_right] using! hy)
  have : fderivWithin 𝕜 (a ∘ f) (insert x s) (x + y) = a ∘L f' := by
    apply HasFDerivWithinAt.fderivWithin _ (hu _ h'y)
    exact a.hasFDerivAt.comp_hasFDerivWithinAt (x + y) hf'
  rw [this] at Z
  convert! Z with n
  ext v
  simp only [FormalMultilinearSeries.derivSeries, sum_apply,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    FormalMultilinearSeries.changeOriginSeries,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_coe, Function.comp_apply, sum_apply, map_sum]
  rfl

/-- If a function has a power series within a set on a ball, then so does its derivative. Version
assuming that the function is analytic on `s`. For a version without this assumption but requiring
that `F` is complete, see `HasFPowerSeriesWithinOnBall.fderivWithin_of_mem`. -/
/-
**HasFPowerSeriesWithinOnBall.fderivWithin_of_mem_of_analyticOn** 是 Mathlib 中的一个
定理，位于命名空间 `HasFPowerSeriesWithinOnBall`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   {p : FormalMultilinearSeries 𝕜 E F
} {r : ENNReal} {f : E → F} {x : E} {s : Set E},   HasFPowerSeriesWithinOnBall f
 p s x r →     AnalyticOn 𝕜 f s → UniqueDiffOn 𝕜 s → x ∈ s → HasFPowerSeriesWith
inOnBall (fderivWithin 𝕜 f s) p.derivSeries s x r
参数：fderivWithin 𝕜 f s。
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
· 使用定理 `FormalMultilinearSeries.radius_le_radius_derivSeries`：radius_le_radius_d
erivSeries : p.radius <= p.derivSeries.radius
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.hasSum_derivSeries_of_hasFDerivWithinAt`：Has
FPowerSeriesWithinOnBall.hasSum_derivSeries_of_hasFDerivWithinAt (h : HasFPowerS
eriesWithinOnBall f p s x r) {f' : E ->L[𝕜] F} {y : E} (h…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `AnalyticOn.differentiableOn`：AnalyticOn.differentiableOn (h : AnalyticOn
 𝕜 f s) : DifferentiableOn 𝕜 f s

--- 原说明 ---
If a function has a power series within a set on a ball, then so does its deriva
tive. Version
assuming that the function is analytic on `s`. For a version without this assump
tion but requiring
that `F` is complete, see `HasFPowerSeriesWithinOnBall.fderivWithin_of_mem`.
-/
protected theorem HasFPowerSeriesWithinOnBall.fderivWithin_of_mem_of_analyticOn
    (hr : HasFPowerSeriesWithinOnBall f p s x r)
    (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    HasFPowerSeriesWithinOnBall (fderivWithin 𝕜 f s) p.derivSeries s x r := by
  refine ⟨hr.r_le.trans p.radius_le_radius_derivSeries, hr.r_pos, fun {y} hy h'y ↦ ?_⟩
  apply hr.hasSum_derivSeries_of_hasFDerivWithinAt (by simpa [edist_zero_right] using! h'y) hy
  · rw [insert_eq_of_mem hx] at hy ⊢
    apply DifferentiableWithinAt.hasFDerivWithinAt
    exact h.differentiableOn _ hy
  · rwa [insert_eq_of_mem hx]

/-- If a function is analytic within a set with unique differentials, then so is its derivative.
Note that this theorem does not require completeness of the space. -/
/-
**AnalyticOn.fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {s : Set E}, AnalyticO
n 𝕜 f s → UniqueDiffOn 𝕜 s → AnalyticOn 𝕜 (fderivWithin 𝕜 f s) s
参数：fderivWithin 𝕜 f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesWithinOnBall.fderivWithin_of_mem_of_analyticOn`：∀ {𝕜 : Ty
pe u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 : NormedAddCommG
roup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} […

--- 原说明 ---
If a function is analytic within a set with unique differentials, then so is its
 derivative.
Note that this theorem does not require completeness of the space.
-/
protected theorem AnalyticOn.fderivWithin (h : AnalyticOn 𝕜 f s) (hu : UniqueDiffOn 𝕜 s) :
    AnalyticOn 𝕜 (fderivWithin 𝕜 f s) s := by
  intro x hx
  rcases h x hx with ⟨p, r, hr⟩
  refine ⟨p.derivSeries, r, hr.fderivWithin_of_mem_of_analyticOn h hu hx⟩

/-- If a function is analytic on a set `s`, so are its successive Fréchet derivative within this
set. Note that this theorem does not require completeness of the space. -/
/-
**AnalyticOn.iteratedFDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {s : Set E}, AnalyticO
n 𝕜 f s → UniqueDiffOn 𝕜 s → ∀ (n : ℕ), AnalyticOn 𝕜 (iteratedFDerivWithin 𝕜 n f
 s) s
参数：n : ℕ；iteratedFDerivWithin 𝕜 n f s。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iteratedFDerivWithin_zero_eq_comp`：iteratedFDerivWithin_zero_eq_comp : i
teratedFDerivWithin 𝕜 0 f s = (continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f
· 使用定理 `ContinuousLinearMap.comp_analyticOn`：ContinuousLinearMap.comp_analyticOn
 (g : F ->L[𝕜] G) (h : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (g ∘ f) s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `iteratedFDerivWithin_succ_eq_comp_left`：iteratedFDerivWithin_succ_eq_com
p_left {n : Nat} : iteratedFDerivWithin 𝕜 (n + 1) f s = (continuousMultilinearCu
rryLeftEquiv 𝕜 (fun _ : Fin …
· 使用引理 `AnalyticOnNhd.comp_analyticOn`：AnalyticOnNhd.comp_analyticOn {f : F -> G
} {g : E -> F} {s : Set F} {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : Analytic
On 𝕜 g t) (h : Set.…
· 使用定理 `LinearIsometryEquiv.analyticOnNhd`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
· 使用定理 `AnalyticOn.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type v} […
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ

--- 原说明 ---
If a function is analytic on a set `s`, so are its successive Fréchet derivative
 within this
set. Note that this theorem does not require completeness of the space.
-/
protected theorem AnalyticOn.iteratedFDerivWithin (h : AnalyticOn 𝕜 f s)
    (hu : UniqueDiffOn 𝕜 s) (n : ℕ) :
    AnalyticOn 𝕜 (iteratedFDerivWithin 𝕜 n f s) s := by
  induction n with
  | zero =>
    rw [iteratedFDerivWithin_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E [×0]→L[𝕜] F)
      |>.comp_analyticOn h
  | succ n IH =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]
    apply AnalyticOnNhd.comp_analyticOn _ (IH.fderivWithin hu) (mapsTo_univ _ _)
    apply LinearIsometryEquiv.analyticOnNhd
/-
**AnalyticOn.hasFTaylorSeriesUpToOn** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {s : Set E} {n : WithT
op ℕ∞},   AnalyticOn 𝕜 f s → UniqueDiffOn 𝕜 s → HasFTaylorSeriesUpToOn n f (ftay
lorSeriesWithin 𝕜 f s) s
参数：ftaylorSeriesWithin 𝕜 f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `AnalyticWithinAt.differentiableWithinAt`：AnalyticWithinAt.differentiable
WithinAt (h : AnalyticWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 f (insert x s
) x
· 使用定理 `AnalyticOn.iteratedFDerivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {F : Type v} […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `AnalyticWithinAt.continuousWithinAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F 
: Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]  
 [inst_2 : NormedSpace 𝕜 …
-/
protected lemma AnalyticOn.hasFTaylorSeriesUpToOn {n : WithTop ℕ∞}
    (h : AnalyticOn 𝕜 f s) (hu : UniqueDiffOn 𝕜 s) :
    HasFTaylorSeriesUpToOn n f (ftaylorSeriesWithin 𝕜 f s) s := by
  refine ⟨fun x _hx ↦ rfl, fun m _hm x hx ↦ ?_, fun m _hm x hx ↦ ?_⟩
  · have := (h.iteratedFDerivWithin hu m x hx).differentiableWithinAt.hasFDerivWithinAt
    rwa [insert_eq_of_mem hx] at this
  · exact (h.iteratedFDerivWithin hu m x hx).continuousWithinAt
/-
**AnalyticOn.exists_hasFTaylorSeriesUpToOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.exists_hasFTaylorSeriesUpToOn (h : AnalyticOn 𝕜 f s) (hu : Uniq
ueDiffOn 𝕜 s) : exists p : E -> FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesU
pToOn ⊤ f p s ∧ forall i, AnalyticOn 𝕜 (fun x => p x i) s
参数：h : AnalyticOn 𝕜 f s；hu : UniqueDiffOn 𝕜 s。
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
· 使用定理 `AnalyticOn.hasFTaylorSeriesUpToOn`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Type v} […
· 使用定理 `AnalyticOn.iteratedFDerivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {F : Type v} […
-/
lemma AnalyticOn.exists_hasFTaylorSeriesUpToOn
    (h : AnalyticOn 𝕜 f s) (hu : UniqueDiffOn 𝕜 s) :
    ∃ p : E → FormalMultilinearSeries 𝕜 E F,
      HasFTaylorSeriesUpToOn ⊤ f p s ∧ ∀ i, AnalyticOn 𝕜 (fun x ↦ p x i) s :=
  ⟨ftaylorSeriesWithin 𝕜 f s, h.hasFTaylorSeriesUpToOn hu, h.iteratedFDerivWithin hu⟩
/-
**AnalyticOnNhd.fderiv_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.fderiv_of_isOpen (h : AnalyticOnNhd 𝕜 f s) (hs : IsOpen s) :
 AnalyticOnNhd 𝕜 (fderiv 𝕜 f) s
参数：h : AnalyticOnNhd 𝕜 f s；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsOpen.analyticOn_iff_analyticOnNhd`：IsOpen.analyticOn_iff_analyticOnNhd
 {f : E -> F} {s : Set E} (hs : IsOpen s) : AnalyticOn 𝕜 f s ↔ AnalyticOnNhd 𝕜 f
 s
· 使用引理 `AnalyticOn.congr`：AnalyticOn.congr {f g : E -> F} {s : Set E} (hf : Anal
yticOn 𝕜 f s) (hs : EqOn g f s) : AnalyticOn 𝕜 g s
· 使用定理 `AnalyticOn.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type v} […
· 使用定理 `IsOpen.uniqueDiffOn`：IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 
𝕜 s
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fderivWithin_of_isOpen`：fderivWithin_of_isOpen (hs : IsOpen s) (hx : x i
n s) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x
-/
theorem AnalyticOnNhd.fderiv_of_isOpen (h : AnalyticOnNhd 𝕜 f s) (hs : IsOpen s) :
    AnalyticOnNhd 𝕜 (fderiv 𝕜 f) s := by
  rw [← hs.analyticOn_iff_analyticOnNhd] at h ⊢
  exact (h.fderivWithin hs.uniqueDiffOn).congr (fun x hx ↦ (fderivWithin_of_isOpen hs hx).symm)
/-
**AnalyticOnNhd.iteratedFDeriv_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.iteratedFDeriv_of_isOpen (h : AnalyticOnNhd 𝕜 f s) (hs : IsO
pen s) (n : Nat) : AnalyticOnNhd 𝕜 (iteratedFDeriv 𝕜 n f) s
参数：h : AnalyticOnNhd 𝕜 f s；hs : IsOpen s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsOpen.analyticOn_iff_analyticOnNhd`：IsOpen.analyticOn_iff_analyticOnNhd
 {f : E -> F} {s : Set E} (hs : IsOpen s) : AnalyticOn 𝕜 f s ↔ AnalyticOnNhd 𝕜 f
 s
· 使用引理 `AnalyticOn.congr`：AnalyticOn.congr {f g : E -> F} {s : Set E} (hf : Anal
yticOn 𝕜 f s) (hs : EqOn g f s) : AnalyticOn 𝕜 g s
· 使用定理 `AnalyticOn.iteratedFDerivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {F : Type v} […
· 使用定理 `IsOpen.uniqueDiffOn`：IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 
𝕜 s
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `iteratedFDerivWithin_of_isOpen`：iteratedFDerivWithin_of_isOpen (n : Nat)
 (hs : IsOpen s) : EqOn (iteratedFDerivWithin 𝕜 n f s) (iteratedFDeriv 𝕜 n f) s
-/
theorem AnalyticOnNhd.iteratedFDeriv_of_isOpen (h : AnalyticOnNhd 𝕜 f s) (hs : IsOpen s) (n : ℕ) :
    AnalyticOnNhd 𝕜 (iteratedFDeriv 𝕜 n f) s := by
  rw [← hs.analyticOn_iff_analyticOnNhd] at h ⊢
  exact (h.iteratedFDerivWithin hs.uniqueDiffOn n).congr
    (fun x hx ↦ (iteratedFDerivWithin_of_isOpen n hs hx).symm)

/-- If an open partial homeomorphism `f` is analytic at a point `a`, with invertible derivative,
then its inverse is analytic at `f a`. -/
/-
**OpenPartialHomeomorph.analyticAt_symm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.analyticAt_symm' (f : OpenPartialHomeomorph E F) {a 
: E} {i : E ≃L[𝕜] F} (h0 : a in f.source) (h : AnalyticAt 𝕜 f a) (h' : fderiv 𝕜 
f a = i) : AnalyticAt 𝕜 f.symm (f a)
参数：f : OpenPartialHomeomorph E F；h0 : a in f.source；h : AnalyticAt 𝕜 f a；h' : fd
eriv 𝕜 f a = i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFPowerSeriesAt.fderiv_eq`：HasFPowerSeriesAt.fderiv_eq (h : HasFPowerS
eriesAt f p x) : fderiv 𝕜 f x = continuousMultilinearCurryFin1 𝕜 E F (p 1)
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFPowerSeriesAt.analyticAt`：HasFPowerSeriesAt.analyticAt (hf : HasFPow
erSeriesAt f p x) : AnalyticAt 𝕜 f x
· 使用定理 `OpenPartialHomeomorph.hasFPowerSeriesAt_symm`：OpenPartialHomeomorph.hasF
PowerSeriesAt_symm (f : OpenPartialHomeomorph E F) {a : E} {i : E ≃L[𝕜] F} (h0 :
 a in f.source) {p : FormalMultili…

--- 原说明 ---
If an open partial homeomorphism `f` is analytic at a point `a`, with invertible
 derivative,
then its inverse is analytic at `f a`.
-/
theorem OpenPartialHomeomorph.analyticAt_symm' (f : OpenPartialHomeomorph E F) {a : E}
    {i : E ≃L[𝕜] F} (h0 : a ∈ f.source) (h : AnalyticAt 𝕜 f a) (h' : fderiv 𝕜 f a = i) :
    AnalyticAt 𝕜 f.symm (f a) := by
  rcases h with ⟨p, hp⟩
  have : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i := by simp [← h', hp.fderiv_eq]
  exact (f.hasFPowerSeriesAt_symm h0 hp this).analyticAt

/-- If an open partial homeomorphism `f` is analytic at a point `f.symm a`, with invertible
derivative, then its inverse is analytic at `a`. -/
/-
**OpenPartialHomeomorph.analyticAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.analyticAt_symm (f : OpenPartialHomeomorph E F) {a :
 F} {i : E ≃L[𝕜] F} (h0 : a in f.target) (h : AnalyticAt 𝕜 f (f.symm a)) (h' : f
deriv 𝕜 f (f.symm a) = i) : AnalyticAt 𝕜 f.symm a
参数：f : OpenPartialHomeomorph E F；h0 : a in f.target；h : AnalyticAt 𝕜 f (f.symm a
)；h' : fderiv 𝕜 f (f.symm a) = i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `OpenPartialHomeomorph.analyticAt_symm'`：OpenPartialHomeomorph.analyticAt
_symm' (f : OpenPartialHomeomorph E F) {a : E} {i : E ≃L[𝕜] F} (h0 : a in f.sour
ce) (h : AnalyticAt 𝕜 f a) (…

--- 原说明 ---
If an open partial homeomorphism `f` is analytic at a point `f.symm a`, with inv
ertible
derivative, then its inverse is analytic at `a`.
-/
theorem OpenPartialHomeomorph.analyticAt_symm (f : OpenPartialHomeomorph E F) {a : F}
    {i : E ≃L[𝕜] F} (h0 : a ∈ f.target) (h : AnalyticAt 𝕜 f (f.symm a))
    (h' : fderiv 𝕜 f (f.symm a) = i) :
    AnalyticAt 𝕜 f.symm a := by
  have : a = f (f.symm a) := by simp [h0]
  rw [this]
  exact f.analyticAt_symm' (by simp [h0]) h h'

end fderiv

section deriv

variable {p : FormalMultilinearSeries 𝕜 𝕜 F} {r : ℝ≥0∞}
variable {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}

/-
**HasFPowerSeriesAt.hasStrictDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerSeriesA
t`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 :
 NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {p : FormalMultilinearSeries
 𝕜 𝕜 F} {f : 𝕜 → F} {x : 𝕜},   HasFPowerSeriesAt f p x → HasStrictDerivAt f ((p 
1) fun x => 1) x
参数：(p 1) fun x => 1。
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
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesAt.hasStrictFDerivAt`：HasFPowerSeriesAt.hasStrictFDerivAt
 (h : HasFPowerSeriesAt f p x) : HasStrictFDerivAt f (continuousMultilinearCurry
Fin1 𝕜 E F (p 1)) x
-/
protected theorem HasFPowerSeriesAt.hasStrictDerivAt (h : HasFPowerSeriesAt f p x) :
    HasStrictDerivAt f (p 1 fun _ => 1) x :=
  h.hasStrictFDerivAt.hasStrictDerivAt
/-
**HasFPowerSeriesAt.hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerSeriesAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 :
 NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {p : FormalMultilinearSeries
 𝕜 𝕜 F} {f : 𝕜 → F} {x : 𝕜},   HasFPowerSeriesAt f p x → HasDerivAt f ((p 1) fun
 x => 1) x
参数：(p 1) fun x => 1。
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
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `HasFPowerSeriesAt.hasStrictDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedS
pace 𝕜 F] {p : FormalMul…
-/
protected theorem HasFPowerSeriesAt.hasDerivAt (h : HasFPowerSeriesAt f p x) :
    HasDerivAt f (p 1 fun _ => 1) x :=
  h.hasStrictDerivAt.hasDerivAt
/-
**HasFPowerSeriesAt.deriv** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerSeriesAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 :
 NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {p : FormalMultilinearSeries
 𝕜 𝕜 F} {f : 𝕜 → F} {x : 𝕜},   HasFPowerSeriesAt f p x → deriv f x = (p 1) fun x
 => 1
参数：p 1。
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
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasFPowerSeriesAt.hasDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜
 F] {p : FormalMul…
-/
protected theorem HasFPowerSeriesAt.deriv (h : HasFPowerSeriesAt f p x) :
    deriv f x = p 1 fun _ => 1 :=
  h.hasDerivAt.deriv

/-- If a function is analytic on a set `s` in a complete space, so is its derivative. -/
/-
**AnalyticOnNhd.deriv** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticOnNhd`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 :
 NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 → F} {s : Set 𝕜} [Com
pleteSpace F],   AnalyticOnNhd 𝕜 f s → AnalyticOnNhd 𝕜 (deriv f) s
参数：deriv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.comp_analyticOnNhd`：ContinuousLinearMap.comp_analyti
cOnNhd {s : Set E} (g : F ->L[𝕜] G) (h : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 
(g ∘ f) s
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `AnalyticOnNhd.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type v} […

--- 原说明 ---
If a function is analytic on a set `s` in a complete space, so is its derivative
.
-/
protected theorem AnalyticOnNhd.deriv [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (deriv f) s :=
  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_analyticOnNhd h.fderiv

/-- If a function is analytic on an open set `s`, so is its derivative. -/
/-
**AnalyticOnNhd.deriv_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.deriv_of_isOpen (h : AnalyticOnNhd 𝕜 f s) (hs : IsOpen s) : 
AnalyticOnNhd 𝕜 (deriv f) s
参数：h : AnalyticOnNhd 𝕜 f s；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.comp_analyticOnNhd`：ContinuousLinearMap.comp_analyti
cOnNhd {s : Set E} (g : F ->L[𝕜] G) (h : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 
(g ∘ f) s
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `AnalyticOnNhd.fderiv_of_isOpen`：AnalyticOnNhd.fderiv_of_isOpen (h : Anal
yticOnNhd 𝕜 f s) (hs : IsOpen s) : AnalyticOnNhd 𝕜 (fderiv 𝕜 f) s

--- 原说明 ---
If a function is analytic on an open set `s`, so is its derivative.
-/
theorem AnalyticOnNhd.deriv_of_isOpen (h : AnalyticOnNhd 𝕜 f s) (hs : IsOpen s) :
    AnalyticOnNhd 𝕜 (deriv f) s :=
  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_analyticOnNhd (h.fderiv_of_isOpen hs)

/-- If a function is analytic on a set `s`, so are its successive derivatives. -/
/-
**AnalyticOnNhd.iterated_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.iterated_deriv [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s) (
n : Nat) : AnalyticOnNhd 𝕜 (deriv^[n] f) s
参数：h : AnalyticOnNhd 𝕜 f s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `AnalyticOnNhd.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 
𝕜 → F} {s…

--- 原说明 ---
If a function is analytic on a set `s`, so are its successive derivatives.
-/
theorem AnalyticOnNhd.iterated_deriv [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s) (n : ℕ) :
    AnalyticOnNhd 𝕜 (deriv^[n] f) s := by
  induction n with
  | zero => exact h
  | succ n IH => simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv
/-
**AnalyticAt.deriv** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 :
 NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 → F} {x : 𝕜} [Complet
eSpace F], AnalyticAt 𝕜 f x → AnalyticAt 𝕜 (deriv f) x
参数：deriv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.exists_ball_analyticOnNhd`：AnalyticAt.exists_ball_analyticOnN
hd (h : AnalyticAt 𝕜 f x) : exists r : Real, 0 < r ∧ AnalyticOnNhd 𝕜 f (Metric.b
all x r)
· 使用定理 `AnalyticOnNhd.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 
𝕜 → F} {s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
@[fun_prop] protected theorem AnalyticAt.deriv [CompleteSpace F] (h : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (deriv f) x := by
  obtain ⟨r, hr, h⟩ := h.exists_ball_analyticOnNhd
  exact h.deriv x (by simp [hr])
/-
**AnalyticAt.iterated_deriv** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 :
 NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 → F} {x : 𝕜} [Complet
eSpace F],   AnalyticAt 𝕜 f x → ∀ (n : ℕ), AnalyticAt 𝕜 (deriv^[n] f) x
参数：n : ℕ；deriv^[n] f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `AnalyticAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F
 : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 →
 F} {x…
-/
@[fun_prop] theorem AnalyticAt.iterated_deriv [CompleteSpace F] (h : AnalyticAt 𝕜 f x) (n : ℕ) :
    AnalyticAt 𝕜 (deriv^[n] f) x := by
  induction n with
  | zero => exact h
  | succ n IH => simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv

end deriv
section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞} {n : ℕ}
variable {f : E → F} {x : E} {s : Set E}

/-! The case of continuously polynomial functions. We get the same differentiability
results as for analytic functions, but without the assumptions that `F` is complete. -/

/-
**HasFiniteFPowerSeriesOnBall.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.differentiableOn (h : HasFiniteFPowerSeriesOnB
all f p x n r) : DifferentiableOn 𝕜 f (Metric.eball x r)
参数：h : HasFiniteFPowerSeriesOnBall f p x n r。
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
· 使用定理 `AnalyticAt.differentiableWithinAt`：AnalyticAt.differentiableWithinAt (h 
: AnalyticAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `CPolynomialAt.analyticAt`：CPolynomialAt.analyticAt (hf : CPolynomialAt 𝕜
 f x) : AnalyticAt 𝕜 f x
· 使用定理 `HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem`：HasFiniteFPowerSeriesO
nBall.cpolynomialAt_of_mem (hf : HasFiniteFPowerSeriesOnBall f p x n r) (h : y i
n Metric.eball x r) : CPolynomialAt 𝕜 …

--- 原说明 ---
The case of continuously polynomial functions. We get the same differentiability
results as for analytic functions, but without the assumptions that `F` is compl
ete.
-/
theorem HasFiniteFPowerSeriesOnBall.differentiableOn
    (h : HasFiniteFPowerSeriesOnBall f p x n r) : DifferentiableOn 𝕜 f (Metric.eball x r) :=
  fun _ hy ↦ (h.cpolynomialAt_of_mem hy).analyticAt.differentiableWithinAt
/-
**HasFiniteFPowerSeriesOnBall.hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.hasStrictFDerivAt (h : HasFiniteFPowerSeriesOn
Ball f p x n r) {y : E} (hy : (‖y‖₊ : Real>=0∞) < r) : HasStrictFDerivAt f (cont
inuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y)
参数：h : HasFiniteFPowerSeriesOnBall f p x n r；hy : (‖y‖₊ : Real>=0∞) < r。
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
· 使用定理 `HasFPowerSeriesAt.hasStrictFDerivAt`：HasFPowerSeriesAt.hasStrictFDerivAt
 (h : HasFPowerSeriesAt f p x) : HasStrictFDerivAt f (continuousMultilinearCurry
Fin1 𝕜 E F (p 1)) x
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.changeOrigin`：HasFiniteFPowerSeriesOnBall.ch
angeOrigin (hf : HasFiniteFPowerSeriesOnBall f p x n r) (h : (‖y‖₊ : Real>=0∞) <
 r) : HasFiniteFPowerSeriesOnB…
-/
theorem HasFiniteFPowerSeriesOnBall.hasStrictFDerivAt (h : HasFiniteFPowerSeriesOnBall f p x n r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    HasStrictFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y) :=
  (h.changeOrigin hy).toHasFPowerSeriesOnBall.hasFPowerSeriesAt.hasStrictFDerivAt
/-
**HasFiniteFPowerSeriesOnBall.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.hasFDerivAt (h : HasFiniteFPowerSeriesOnBall f
 p x n r) {y : E} (hy : (‖y‖₊ : Real>=0∞) < r) : HasFDerivAt f (continuousMultil
inearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y)
参数：h : HasFiniteFPowerSeriesOnBall f p x n r；hy : (‖y‖₊ : Real>=0∞) < r。
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
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `HasFiniteFPowerSeriesOnBall.hasStrictFDerivAt`：HasFiniteFPowerSeriesOnBa
ll.hasStrictFDerivAt (h : HasFiniteFPowerSeriesOnBall f p x n r) {y : E} (hy : (
‖y‖₊ : Real>=0∞) < r) : HasStrictFD…
-/
theorem HasFiniteFPowerSeriesOnBall.hasFDerivAt (h : HasFiniteFPowerSeriesOnBall f p x n r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y) :=
  (h.hasStrictFDerivAt hy).hasFDerivAt
/-
**HasFiniteFPowerSeriesOnBall.fderiv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.fderiv_eq (h : HasFiniteFPowerSeriesOnBall f p
 x n r) {y : E} (hy : (‖y‖₊ : Real>=0∞) < r) : fderiv 𝕜 f (x + y) = continuousMu
ltilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)
参数：h : HasFiniteFPowerSeriesOnBall f p x n r；hy : (‖y‖₊ : Real>=0∞) < r。
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
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFiniteFPowerSeriesOnBall.hasFDerivAt`：HasFiniteFPowerSeriesOnBall.has
FDerivAt (h : HasFiniteFPowerSeriesOnBall f p x n r) {y : E} (hy : (‖y‖₊ : Real>
=0∞) < r) : HasFDerivAt f (co…
-/
theorem HasFiniteFPowerSeriesOnBall.fderiv_eq (h : HasFiniteFPowerSeriesOnBall f p x n r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    fderiv 𝕜 f (x + y) = continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1) :=
  (h.hasFDerivAt hy).fderiv

/-- If a function has a finite power series on a ball, then so does its derivative. -/
/-
**HasFiniteFPowerSeriesOnBall.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `HasFiniteFPowerS
eriesOnBall`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   {p : FormalMultilinearSeries 𝕜 E F
} {r : ENNReal} {n : ℕ} {f : E → F} {x : E},   HasFiniteFPowerSeriesOnBall f p x
 (n + 1) r → HasFiniteFPowerSeriesOnBall (fderiv 𝕜 f) p.derivSeries x n r
参数：n + 1；fderiv 𝕜 f。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.congr`：HasFiniteFPowerSeriesOnBall.congr (hf
 : HasFiniteFPowerSeriesOnBall f p x n r) (hg : EqOn f g (Metric.eball x r)) : H
asFiniteFPowerSeriesOnB…
· 使用定理 `ContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall`：ContinuousLinearMa
p.comp_hasFiniteFPowerSeriesOnBall (g : F ->L[𝕜] G) (h : HasFiniteFPowerSeriesOn
Ball f p x n r) : HasFiniteFPowerSeriesOnB…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasFiniteFPowerSeriesOnBall.comp_sub`：HasFiniteFPowerSeriesOnBall.comp_s
ub (hf : HasFiniteFPowerSeriesOnBall f p x n r) (y : E) : HasFiniteFPowerSeriesO
nBall (fun z => f (z - y))…
· 使用定理 `HasFiniteFPowerSeriesOnBall.mono`：HasFiniteFPowerSeriesOnBall.mono (hf :
 HasFiniteFPowerSeriesOnBall f p x n r) (r'_pos : 0 < r') (hr : r' <= r) : HasFi
niteFPowerSeriesOnBall…
· 使用定理 `FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_changeOrigin`：hasFin
iteFPowerSeriesOnBall_changeOrigin (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
 (k : Nat) (hn : forall (m : Nat), n + k <= m -> p m =…
· 使用定理 `HasFiniteFPowerSeriesOnBall.finite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFiniteFPowerSeriesOnBall.fderiv_eq`：HasFiniteFPowerSeriesOnBall.fderi
v_eq (h : HasFiniteFPowerSeriesOnBall f p x n r) {y : E} (hy : (‖y‖₊ : Real>=0∞)
 < r) : fderiv 𝕜 f (x + y) …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b

--- 原说明 ---
If a function has a finite power series on a ball, then so does its derivative.
-/
protected theorem HasFiniteFPowerSeriesOnBall.fderiv
    (h : HasFiniteFPowerSeriesOnBall f p x (n + 1) r) :
    HasFiniteFPowerSeriesOnBall (fderiv 𝕜 f) p.derivSeries x n r := by
  refine .congr (f := fun z ↦ continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin (z - x) 1)) ?_
    fun z hz ↦ ?_
  · refine continuousMultilinearCurryFin1 𝕜 E F
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall ?_
    simpa using!
      ((p.hasFiniteFPowerSeriesOnBall_changeOrigin 1 h.finite).mono h.r_pos le_top).comp_sub x
  dsimp only
  rw [← h.fderiv_eq, add_sub_cancel]
  simpa only [edist_eq_enorm_sub, Metric.mem_eball] using! hz

/-- If a function has a finite power series on a ball, then so does its derivative.
This is a variant of `HasFiniteFPowerSeriesOnBall.fderiv` where the degree of `f` is `< n`
and not `< n + 1`. -/
/-
**HasFiniteFPowerSeriesOnBall.fderiv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.fderiv' (h : HasFiniteFPowerSeriesOnBall f p x
 n r) : HasFiniteFPowerSeriesOnBall (fderiv 𝕜 f) p.derivSeries x (n - 1) r
参数：h : HasFiniteFPowerSeriesOnBall f p x n r。
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
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `HasFiniteFPowerSeriesOnBall.bound_zero_of_eq_zero`：HasFiniteFPowerSeries
OnBall.bound_zero_of_eq_zero (hf : forall y in Metric.eball x r, f y = 0) (r_pos
 : 0 < r) (hp : forall n, p n = 0) : Ha…
· 使用定理 `Filter.EventuallyEq.fderiv_eq`：Filter.EventuallyEq.fderiv_eq (h : f₁ =ᶠ[
𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 𝕜 f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyEq_iff_exists_mem`：eventuallyEq_iff_exists_mem {l : Fil
ter α} {f g : α -> β} : f =ᶠ[l] g ↔ exists s in l, EqOn f g s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_eball`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x : α
} {ε : ENNReal}, IsOpen (Metric.eball x ε)
· 使用定理 `HasFiniteFPowerSeriesOnBall.eq_zero_of_bound_zero`：HasFiniteFPowerSeries
OnBall.eq_zero_of_bound_zero (hf : HasFiniteFPowerSeriesOnBall f pf x 0 r) : for
all y in Metric.eball x r, f y = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderiv_fun_const`：fderiv_fun_const (c : F) : fderiv 𝕜 (fun _ : E => c) =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用引理 `FormalMultilinearSeries.changeOriginSeries_finite_of_finite`：changeOrigi
nSeries_finite_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : for
all (m : Nat), n <= m -> p m = 0) (k : Nat) : for…
· 使用定理 `HasFiniteFPowerSeriesOnBall.finite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
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
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If a function has a finite power series on a ball, then so does its derivative.
This is a variant of `HasFiniteFPowerSeriesOnBall.fderiv` where the degree of `f
` is `< n`
and not `< n + 1`.
-/
theorem HasFiniteFPowerSeriesOnBall.fderiv' (h : HasFiniteFPowerSeriesOnBall f p x n r) :
    HasFiniteFPowerSeriesOnBall (fderiv 𝕜 f) p.derivSeries x (n - 1) r := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [zero_tsub]
    refine HasFiniteFPowerSeriesOnBall.bound_zero_of_eq_zero (fun y hy ↦ ?_) h.r_pos fun n ↦ ?_
    · rw [Filter.EventuallyEq.fderiv_eq (f := fun _ ↦ 0)]
      · simp
      · exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨Metric.eball x r,
          Metric.isOpen_eball.mem_nhds hy, fun z hz ↦ by rw [h.eq_zero_of_bound_zero z hz]⟩
    · apply ContinuousMultilinearMap.ext; intro a
      change (continuousMultilinearCurryFin1 𝕜 E F) (p.changeOriginSeries 1 n a) = 0
      rw [p.changeOriginSeries_finite_of_finite h.finite 1 (Nat.zero_le _)]
      exact map_zero _
  · rw [← Nat.succ_pred hn] at h
    exact h.fderiv

/-- If a function is polynomial on a set `s`, so is its Fréchet derivative. -/
/-
**CPolynomialOn.fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.fderiv (h : CPolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 (fderiv 𝕜
 f) s
参数：h : CPolynomialOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFiniteFPowerSeriesOnBall.cpolynomialAt`：HasFiniteFPowerSeriesOnBall.c
polynomialAt (hf : HasFiniteFPowerSeriesOnBall f p x n r) : CPolynomialAt 𝕜 f x
· 使用定理 `HasFiniteFPowerSeriesOnBall.fderiv'`：HasFiniteFPowerSeriesOnBall.fderiv'
 (h : HasFiniteFPowerSeriesOnBall f p x n r) : HasFiniteFPowerSeriesOnBall (fder
iv 𝕜 f) p.derivSeries x (…

--- 原说明 ---
If a function is polynomial on a set `s`, so is its Fréchet derivative.
-/
theorem CPolynomialOn.fderiv (h : CPolynomialOn 𝕜 f s) :
    CPolynomialOn 𝕜 (fderiv 𝕜 f) s := by
  intro y hy
  rcases h y hy with ⟨p, r, n, hp⟩
  exact hp.fderiv'.cpolynomialAt

/-- If a function is polynomial on a set `s`, so are its successive Fréchet derivative. -/
/-
**CPolynomialOn.iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.iteratedFDeriv (h : CPolynomialOn 𝕜 f s) (n : Nat) : CPolyno
mialOn 𝕜 (iteratedFDeriv 𝕜 n f) s
参数：h : CPolynomialOn 𝕜 f s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iteratedFDeriv_zero_eq_comp`：iteratedFDeriv_zero_eq_comp : iteratedFDeri
v 𝕜 0 f = (continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f
· 使用定理 `ContinuousLinearMap.comp_cpolynomialOn`：ContinuousLinearMap.comp_cpolyno
mialOn {s : Set E} (g : F ->L[𝕜] G) (h : CPolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 
(g ∘ f) s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `iteratedFDeriv_succ_eq_comp_left`：iteratedFDeriv_succ_eq_comp_left {n : 
Nat} : iteratedFDeriv 𝕜 (n + 1) f = (continuousMultilinearCurryLeftEquiv 𝕜 (fun 
_ : Fin (n + 1) => E) …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CPolynomialOn.fderiv`：CPolynomialOn.fderiv (h : CPolynomialOn 𝕜 f s) : C
PolynomialOn 𝕜 (fderiv 𝕜 f) s

--- 原说明 ---
If a function is polynomial on a set `s`, so are its successive Fréchet derivati
ve.
-/
theorem CPolynomialOn.iteratedFDeriv (h : CPolynomialOn 𝕜 f s) (n : ℕ) :
    CPolynomialOn 𝕜 (iteratedFDeriv 𝕜 n f) s := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E [×0]→L[𝕜] F).comp_cpolynomialOn h
  | succ n IH =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    convert! ContinuousLinearMap.comp_cpolynomialOn ?g IH.fderiv
    case g => exact ↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) F).symm
    simp

end fderiv

section deriv

variable {p : FormalMultilinearSeries 𝕜 𝕜 F} {r : ℝ≥0∞}
variable {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}

/-- If a function is polynomial on a set `s`, so is its derivative. -/
/-
**CPolynomialOn.deriv** 是 Mathlib 中的一个定理，位于命名空间 `CPolynomialOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 :
 NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 → F} {s : Set 𝕜}, CPo
lynomialOn 𝕜 f s → CPolynomialOn 𝕜 (deriv f) s
参数：deriv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.comp_cpolynomialOn`：ContinuousLinearMap.comp_cpolyno
mialOn {s : Set E} (g : F ->L[𝕜] G) (h : CPolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 
(g ∘ f) s
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `CPolynomialOn.fderiv`：CPolynomialOn.fderiv (h : CPolynomialOn 𝕜 f s) : C
PolynomialOn 𝕜 (fderiv 𝕜 f) s

--- 原说明 ---
If a function is polynomial on a set `s`, so is its derivative.
-/
protected theorem CPolynomialOn.deriv (h : CPolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 (deriv f) s :=
  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_cpolynomialOn h.fderiv

/-- If a function is polynomial on a set `s`, so are its successive derivatives. -/
/-
**CPolynomialOn.iterated_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.iterated_deriv (h : CPolynomialOn 𝕜 f s) (n : Nat) : CPolyno
mialOn 𝕜 (deriv^[n] f) s
参数：h : CPolynomialOn 𝕜 f s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `CPolynomialOn.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 
𝕜 → F} {s…

--- 原说明 ---
If a function is polynomial on a set `s`, so are its successive derivatives.
-/
theorem CPolynomialOn.iterated_deriv (h : CPolynomialOn 𝕜 f s) (n : ℕ) :
    CPolynomialOn 𝕜 (deriv^[n] f) s := by
  induction n with
  | zero => exact h
  | succ n IH => simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv

end deriv

namespace ContinuousMultilinearMap

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 E F)

open FormalMultilinearSeries

/-
**ContinuousMultilinearMap.changeOriginSeries_support** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousMultilinearMap`。
形式化陈述：changeOriginSeries_support {k l : Nat} (h : k + l != Fintype.card ι) : f.t
oFormalMultilinearSeries.changeOriginSeries k l = 0
参数：h : k + l != Fintype.card ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
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
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearIsometryEquiv.map_zero`：map_zero : e 0 = 0
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem changeOriginSeries_support {k l : ℕ} (h : k + l ≠ Fintype.card ι) :
    f.toFormalMultilinearSeries.changeOriginSeries k l = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ by
    simp_rw [FormalMultilinearSeries.changeOriginSeriesTerm,
      toFormalMultilinearSeries, dif_neg h.symm, LinearIsometryEquiv.map_zero]

variable {n : WithTop ℕ∞} (x : ∀ i, E i)

open Finset in
/-
**ContinuousMultilinearMap.changeOrigin_toFormalMultilinearSeries** 是 Mathlib 中的
一个定理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：changeOrigin_toFormalMultilinearSeries [DecidableEq ι] : continuousMultili
nearCurryFin1 𝕜 (forall i, E i) F (f.toFormalMultilinearSeries.changeOrigin x 1)
 = f.linearDeriv x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousMultilinearCurryFin1_apply`：continuousMultilinearCurryFin1_app
ly (f : G [×1]->L[𝕜] G') (x : G) : continuousMultilinearCurryFin1 𝕜 G G' f x = f
 (Fin.snoc 0 x)
· 使用引理 `ContinuousMultilinearMap.linearDeriv_apply`：linearDeriv_apply : f.linear
Deriv x y = ∑ i, f (Function.update x i (y i))
· 使用定理 `FormalMultilinearSeries.changeOrigin.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_
2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGrou
p E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `FormalMultilinearSeries.sum.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : AddCommMonoid 
F]   [inst_3 : _root_.…
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Fintype.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} [inst : Fintype ι] [i
nst_1 : AddCommMonoid M] [IsEmpty ι] (f : ι → M), ∑ x, f x = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMultilinearMap.changeOriginSeries_support`：changeOriginSeries_
support {k l : Nat} (h : k + l != Fintype.card ι) : f.toFormalMultilinearSeries.
changeOriginSeries k l = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `tsum_eq_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] {f : β → α}
 (b …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `eq_tsub_iff_add_eq_of_le`：eq_tsub_iff_add_eq_of_le (h : c <= b) : a = b 
- c ↔ a + c = b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
（共 68 条，此处仅展示前 30 条）
-/
theorem changeOrigin_toFormalMultilinearSeries [DecidableEq ι] :
    continuousMultilinearCurryFin1 𝕜 (∀ i, E i) F (f.toFormalMultilinearSeries.changeOrigin x 1) =
    f.linearDeriv x := by
  ext y
  rw [continuousMultilinearCurryFin1_apply, linearDeriv_apply,
      changeOrigin, FormalMultilinearSeries.sum]
  cases isEmpty_or_nonempty ι
  · have (l : _) : 1 + l ≠ Fintype.card ι := by
      rw [add_comm, Fintype.card_eq_zero]; exact Nat.succ_ne_zero _
    simp_rw [Fintype.sum_empty, changeOriginSeries_support _ (this _), _root_.zero_apply _,
      tsum_zero]; rfl
  rw [tsum_eq_single (Fintype.card ι - 1), changeOriginSeries]; swap
  · intro m hm
    rw [Ne, eq_tsub_iff_add_eq_of_le (by exact Fintype.card_pos), add_comm] at hm
    rw [f.changeOriginSeries_support hm, _root_.zero_apply]
  rw [_root_.sum_apply, _root_.sum_apply, Fin.snoc_zero]
  simp_rw [changeOriginSeriesTerm_apply]
  refine (Fintype.sum_bijective (?_ ∘ Fintype.equivFinOfCardEq (Nat.add_sub_of_le
    Fintype.card_pos).symm) (.comp ?_ <| Equiv.bijective _) _ _ fun i ↦ ?_).symm
  · exact (⟨{·}ᶜ, by
      rw [card_compl, Fintype.card_fin, Finset.card_singleton, Nat.add_sub_cancel_left]⟩)
  · use fun _ _ ↦ (singleton_injective <| compl_injective <| Subtype.ext_iff.mp ·)
    intro ⟨s, hs⟩
    have h : #sᶜ = 1 := by rw [card_compl, hs, Fintype.card_fin, Nat.add_sub_cancel]
    obtain ⟨a, ha⟩ := card_eq_one.mp h
    exact ⟨a, Subtype.ext (compl_eq_comm.mp ha)⟩
  rw [Function.comp_apply, Subtype.coe_mk, compl_singleton, piecewise_erase_univ,
    toFormalMultilinearSeries, dif_pos (Nat.add_sub_of_le Fintype.card_pos).symm]
  simp_rw [domDomCongr_apply, compContinuousLinearMap_apply, ContinuousLinearMap.proj_apply,
    Function.update_apply, (Equiv.injective _).eq_iff, ite_apply]
  congr
  grind
/-
**ContinuousMultilinearMap.hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMultilinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 :
 NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {ι : Type u_2} {E : ι → Type
 u_3} [inst_3 : (i : ι) → NormedAddCommGroup (E i)]   [inst_4 : (i : ι) → Normed
Space 𝕜 (E i)] [inst_5 : Fintype ι] (f : ContinuousMultilinearMap 𝕜 E F) (x : (i
 : ι) → E i)   [inst_6 : DecidableEq ι], HasStrictFDerivAt (⇑f) (f.linearDeriv x
) x
参数：i : ι；E i；i : ι；E i；f : ContinuousMultilinearMap 𝕜 E F；x : (i : ι) → E i；⇑f；f
.linearDeriv x。
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
· 使用定理 `ContinuousMultilinearMap.changeOrigin_toFormalMultilinearSeries`：changeO
rigin_toFormalMultilinearSeries [DecidableEq ι] : continuousMultilinearCurryFin1
 𝕜 (forall i, E i) F (f.toFormalMultilinearSeries.cha…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasFiniteFPowerSeriesOnBall.hasStrictFDerivAt`：HasFiniteFPowerSeriesOnBa
ll.hasStrictFDerivAt (h : HasFiniteFPowerSeriesOnBall f p x n r) {y : E} (hy : (
‖y‖₊ : Real>=0∞) < r) : HasStrictFD…
· 使用定理 `ContinuousMultilinearMap.hasFiniteFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {
F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup F]
   [inst_2 : NormedSpace 𝕜 F] {ι : Type u_…
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
protected theorem hasStrictFDerivAt [DecidableEq ι] : HasStrictFDerivAt f (f.linearDeriv x) x := by
  rw [← changeOrigin_toFormalMultilinearSeries]
  convert! f.hasFiniteFPowerSeriesOnBall.hasStrictFDerivAt (y := x) ENNReal.coe_lt_top
  rw [zero_add]
/-
**ContinuousMultilinearMap.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 :
 NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {ι : Type u_2} {E : ι → Type
 u_3} [inst_3 : (i : ι) → NormedAddCommGroup (E i)]   [inst_4 : (i : ι) → Normed
Space 𝕜 (E i)] [inst_5 : Fintype ι] (f : ContinuousMultilinearMap 𝕜 E F) (x : (i
 : ι) → E i)   [inst_6 : DecidableEq ι], HasFDerivAt (⇑f) (f.linearDeriv x) x
参数：i : ι；E i；i : ι；E i；f : ContinuousMultilinearMap 𝕜 E F；x : (i : ι) → E i；⇑f；f
.linearDeriv x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMultilinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 :
 NormedSpace 𝕜 F] {ι : Type u_2}…
-/
protected theorem hasFDerivAt [DecidableEq ι] : HasFDerivAt f (f.linearDeriv x) x :=
  (f.hasStrictFDerivAt _).hasFDerivAt
/-
**ContinuousMultilinearMap.hasStrictFDerivAt_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousMultilinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 :
 NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {ι : Type u_2} {E : ι → Type
 u_3} [inst_3 : (i : ι) → NormedAddCommGroup (E i)]   [inst_4 : (i : ι) → Normed
Space 𝕜 (E i)] [inst_5 : Fintype ι] [inst_6 : DecidableEq ι]   (fa : ContinuousM
ultilinearMap 𝕜 E F × ((i : ι) → E i)),   HasStrictFDerivAt (fun fx => fx.1 fx.2
)     (ContinuousMultilinearMap.apply 𝕜 E F fa.2 ∘SL         ContinuousLinearMap
.fst 𝕜 (ContinuousMultilinearMap 𝕜 E F) ((i : ι) → E i) +       fa.1.linearDeriv
 fa.2 ∘SL ContinuousLinearMap.snd 𝕜 (ContinuousMultilinearMap 𝕜 E F) ((i : ι) → 
E i))     fa
参数：i : ι；E i；i : ι；E i；fa : ContinuousMultilinearMap 𝕜 E F × ((i : ι) → E i)；fun
 fx => fx.1 fx.2；ContinuousMultilinearMap.apply 𝕜 E F fa.2 ∘SL         Continuou
sLinearMap.fst 𝕜 (ContinuousMultilinearMap 𝕜 E F) ((i : ι) → E i) +       fa.1.l
inearDeriv fa.2 ∘SL ContinuousLinearMap.snd 𝕜 (ContinuousMultilinearMap 𝕜 E F) (
(i : ι) → E i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `ContinuousMultilinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 :
 NormedSpace 𝕜 F] {ι : Type u_2}…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasStrictFDerivAt_pi`：hasStrictFDerivAt_pi : HasStrictFDerivAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') x ↔ forall i, HasStrictFDerivAt (φ i) (φ' 
i) x
· 使用定理 `hasStrictFDerivAt_id`：hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt i
d (.id 𝕜 E) x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.prod_ext`：prod_ext {f g : M × M₂ ->L[R] M₃} (hl : f.
comp (inl _ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ 
_ _)) : f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.add_comp`：add_comp [ContinuousAdd M₃] (g₁ g₂ : M₂ ->
SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) : (g₁ + g₂) ∘SL f = g₁ ∘SL f + g₂ ∘SL f
（共 43 条，此处仅展示前 30 条）
-/
protected theorem hasStrictFDerivAt_uncurry [DecidableEq ι]
    (fa : ContinuousMultilinearMap 𝕜 E F × ∀ i, E i) :
    HasStrictFDerivAt (fun fx : ContinuousMultilinearMap 𝕜 E F × ∀ i, E i ↦ fx.1 fx.2)
      (apply 𝕜 E F fa.2 ∘L .fst _ _ _ + fa.1.linearDeriv fa.2 ∘L .snd _ _ _) fa := by
  let f := ContinuousLinearMap.id 𝕜 (ContinuousMultilinearMap 𝕜 E F)
    |>.continuousMultilinearMapOption
  have Hf := (f.hasStrictFDerivAt (fun _ ↦ fa)).comp (f := fun fx _ ↦ fx) fa
    (hasStrictFDerivAt_pi.2 fun _ ↦ hasStrictFDerivAt_id _)
  convert! Hf using 1
  ext g
  · suffices ∑ i, fa.1 (Function.update fa.2 i 0) =
        ∑ i, fa.1 fun j ↦ (Function.update (fun _ ↦ fa) (some i) (g, 0) (some j)).2 j by
      simpa [f, ContinuousLinearMap.continuousMultilinearMapOption]
    congr with i
    congr with j
    rcases eq_or_ne j i with rfl | hij <;> simp [*]
  · suffices ∑ i, fa.1 (Function.update fa.2 i (g i)) =
        ∑ x, fa.1 fun i ↦ (Function.update (fun x ↦ fa) (some x) (0, g) (some i)).2 i by
      simpa [f, ContinuousLinearMap.continuousMultilinearMapOption]
    congr with i
    congr with j
    rcases eq_or_ne j i with rfl | hij <;> simp [*]
/-
**ContinuousMultilinearMap._root_.HasStrictFDerivAt.continuousMultilinearMap_app
ly** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.HasStrictFDerivAt.continuousMultilinearMap_apply {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [DecidableEq ι] {x : G}
    {f : G → ContinuousMultilinearMap 𝕜 E F} {g : ∀ i, G → E i}
    {f' : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F} {g' : ∀ i, G →L[𝕜] E i}
    (hf : HasStrictFDerivAt f f' x) (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt (fun x ↦ f x (g · x))
      (ContinuousMultilinearMap.apply 𝕜 E F (g · x) ∘L f' +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i) x := by
  convert!
    ContinuousMultilinearMap.hasStrictFDerivAt_uncurry (f x, (g · x)) |>.comp x
      (hf.prodMk (hasStrictFDerivAt_pi.2 hg))
  ext
  simp
/-
**ContinuousMultilinearMap._root_.HasFDerivWithinAt.continuousMultilinearMap_app
ly** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.HasFDerivWithinAt.continuousMultilinearMap_apply {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [DecidableEq ι] {s : Set G} {x : G}
    {f : G → ContinuousMultilinearMap 𝕜 E F} {g : ∀ i, G → E i}
    {f' : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F} {g' : ∀ i, G →L[𝕜] E i}
    (hf : HasFDerivWithinAt f f' s x) (hg : ∀ i, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt (fun x ↦ f x (g · x))
      (ContinuousMultilinearMap.apply 𝕜 E F (g · x) ∘L f' +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i) s x := by
  convert!
    ContinuousMultilinearMap.hasStrictFDerivAt_uncurry
        (f x, (g · x)) |>.hasFDerivAt.comp_hasFDerivWithinAt
      x (hf.prodMk (hasFDerivWithinAt_pi.2 hg))
  ext
  simp
/-
**ContinuousMultilinearMap._root_.HasFDerivAt.continuousMultilinearMap_apply** 是
 Mathlib 中的一个定理，位于命名空间 `ContinuousMultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.HasFDerivAt.continuousMultilinearMap_apply {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [DecidableEq ι] {x : G}
    {f : G → ContinuousMultilinearMap 𝕜 E F} {g : ∀ i, G → E i}
    {f' : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F} {g' : ∀ i, G →L[𝕜] E i}
    (hf : HasFDerivAt f f' x) (hg : ∀ i, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt (fun x ↦ f x (g · x))
      (ContinuousMultilinearMap.apply 𝕜 E F (g · x) ∘L f' +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i) x := by
  simp only [← hasFDerivWithinAt_univ] at *
  exact hf.continuousMultilinearMap_apply hg

/-- Given `f` a multilinear map, then the derivative of `x ↦ f (g₁ x, ..., gₙ x)` at `x` applied
to a vector `v` is given by `∑ i, f (g₁ x, ..., g'ᵢ v, ..., gₙ x)`. Version inside a set. -/
/-
**ContinuousMultilinearMap._root_.HasFDerivWithinAt.multilinear_comp** 是 Mathlib
 中的一个定理，位于命名空间 `ContinuousMultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f` a multilinear map, then the derivative of `x ↦ f (g₁ x, ..., gₙ x)` at
 `x` applied
to a vector `v` is given by `∑ i, f (g₁ x, ..., g'ᵢ v, ..., gₙ x)`. Version insi
de a set.
-/
theorem _root_.HasFDerivWithinAt.multilinear_comp
    [DecidableEq ι] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {g : ∀ i, G → E i} {g' : ∀ i, G →L[𝕜] E i} {s : Set G} {x : G}
    (hg : ∀ i, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt (fun x ↦ f (fun i ↦ g i x))
      ((∑ i : ι, (f.toContinuousLinearMap (fun j ↦ g j x) i) ∘L (g' i))) s x := by
  simpa using (hasFDerivWithinAt_const f x s).continuousMultilinearMap_apply hg

/-- Given `f` a multilinear map, then the derivative of `x ↦ f (g₁ x, ..., gₙ x)` at `x` applied
to a vector `v` is given by `∑ i, f (g₁ x, ..., g'ᵢ v, ..., gₙ x)`. -/
/-
**ContinuousMultilinearMap._root_.HasFDerivAt.multilinear_comp** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousMultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f` a multilinear map, then the derivative of `x ↦ f (g₁ x, ..., gₙ x)` at
 `x` applied
to a vector `v` is given by `∑ i, f (g₁ x, ..., g'ᵢ v, ..., gₙ x)`.
-/
theorem _root_.HasFDerivAt.multilinear_comp
    [DecidableEq ι] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {g : ∀ i, G → E i} {g' : ∀ i, G →L[𝕜] E i} {x : G}
    (hg : ∀ i, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt (fun x ↦ f (fun i ↦ g i x))
      ((∑ i : ι, (f.toContinuousLinearMap (fun j ↦ g j x) i) ∘L (g' i))) x := by
  simpa using (hasFDerivAt_const f x).continuousMultilinearMap_apply hg

/-- Technical lemma used in the proof of `hasFTaylorSeriesUpTo_iteratedFDeriv`, to compare sums
over embedding of `Fin k` and `Fin (k + 1)`. -/
/-
**ContinuousMultilinearMap._root_.Equiv.succ_embeddingFinSucc_fst_symm_apply** 是
 Mathlib 中的一个引理，位于命名空间 `ContinuousMultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Technical lemma used in the proof of `hasFTaylorSeriesUpTo_iteratedFDeriv`, to c
ompare sums
over embedding of `Fin k` and `Fin (k + 1)`.
-/
private lemma _root_.Equiv.succ_embeddingFinSucc_fst_symm_apply {ι : Type*} [DecidableEq ι]
    {n : ℕ} (e : Fin (n + 1) ↪ ι) {k : ι}
    (h'k : k ∈ Set.range (Equiv.embeddingFinSucc n ι e).1) (hk : k ∈ Set.range e) :
    Fin.succ ((Equiv.embeddingFinSucc n ι e).1.toEquivRange.symm ⟨k, h'k⟩)
      = e.toEquivRange.symm ⟨k, hk⟩ := by
  rcases hk with ⟨j, rfl⟩
  have hj : j ≠ 0 := by
    rintro rfl
    simp at h'k
  simp only [Function.Embedding.toEquivRange_symm_apply_self]
  have : e j = (Equiv.embeddingFinSucc n ι e).1 (Fin.pred j hj) := by simp
  simp_rw [this]
  simp [-Equiv.embeddingFinSucc_fst]

set_option backward.isDefEq.respectTransparency false in
/-- A continuous multilinear function `f` admits a Taylor series, whose successive terms are given
by `f.iteratedFDeriv n`. This is the point of the definition of `f.iteratedFDeriv`. -/
/-
**ContinuousMultilinearMap.hasFTaylorSeriesUpTo_iteratedFDeriv** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：hasFTaylorSeriesUpTo_iteratedFDeriv : HasFTaylorSeriesUpTo ⊤ f (fun v n =>
 f.iteratedFDeriv n v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `ContinuousMultilinearMap.iteratedFDerivComponent_apply`：∀ {𝕜 : Type u} {
ι : Type v} {E₁ : ι → Type wE₁} {G : Type wG} [inst : NontriviallyNormedField 𝕜]
   [inst_1 : (i : ι) → SeminormedAddCommGrou…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `Matrix.range_empty`：range_empty (u : Fin 0 -> α) : Set.range u = ∅
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
（共 65 条，此处仅展示前 30 条）

--- 原说明 ---
A continuous multilinear function `f` admits a Taylor series, whose successive t
erms are given
by `f.iteratedFDeriv n`. This is the point of the definition of `f.iteratedFDeri
v`.
-/
theorem hasFTaylorSeriesUpTo_iteratedFDeriv :
    HasFTaylorSeriesUpTo ⊤ f (fun v n ↦ f.iteratedFDeriv n v) := by
  classical
  constructor
  · simp [ContinuousMultilinearMap.iteratedFDeriv]
  · rintro n - x
    suffices H : curryLeft (f.iteratedFDeriv (Nat.succ n) x) = (∑ e : Fin n ↪ ι,
          ((iteratedFDerivComponent f e.toEquivRange).linearDeriv
            (Pi.compRightL 𝕜 _ Subtype.val x)) ∘L (Pi.compRightL 𝕜 _ Subtype.val)) by
      have A : HasFDerivAt (f.iteratedFDeriv n) (∑ e : Fin n ↪ ι,
          ((iteratedFDerivComponent f e.toEquivRange).linearDeriv (Pi.compRightL 𝕜 _ Subtype.val x))
            ∘L (Pi.compRightL 𝕜 _ Subtype.val)) x := by
        apply HasFDerivAt.fun_sum (fun s _hs ↦ ?_)
        exact (ContinuousMultilinearMap.hasFDerivAt _ _).comp x (ContinuousLinearMap.hasFDerivAt _)
      rwa [← H] at A
    ext v m
    simp only [ContinuousMultilinearMap.iteratedFDeriv, curryLeft_apply, sum_apply,
      iteratedFDerivComponent_apply, Finset.univ_sigma_univ,
      Pi.compRightL_apply, _root_.sum_apply, ContinuousLinearMap.comp_apply, linearDeriv_apply,
      Finset.sum_sigma']
    rw [← (Equiv.embeddingFinSucc n ι).sum_comp]
    congr with e
    congr with k
    by_cases hke : k ∈ Set.range e
    · simp only [hke, ↓reduceDIte]
      split_ifs with hkf
      · simp only [← Equiv.succ_embeddingFinSucc_fst_symm_apply e hkf hke, Fin.cons_succ]
      · obtain rfl : k = e 0 := by
          rcases hke with ⟨j, rfl⟩
          simpa using hkf
        simp only [Function.Embedding.toEquivRange_symm_apply_self, Fin.cons_zero, Function.update,
          Pi.compRightL_apply]
        split_ifs with h
        · congr!
        · exfalso
          apply h
          simp_rw [← Equiv.embeddingFinSucc_snd e]
    · have hkf : k ∉ Set.range (Equiv.embeddingFinSucc n ι e).1 := by
        contrapose hke
        rw [Equiv.embeddingFinSucc_fst] at hke
        exact Set.range_comp_subset_range _ _ hke
      simp only [hke, hkf, ↓reduceDIte, Pi.compRightL,
        ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
      rw [Function.update_of_ne]
      contrapose hke
      rw [show k = _ from Subtype.ext_iff.1 hke, Equiv.embeddingFinSucc_snd e]
      exact Set.mem_range_self _
  · rintro n -
    apply continuous_finsetSum _ (fun e _ ↦ ?_)
    exact (ContinuousMultilinearMap.coe_continuous _).comp (ContinuousLinearMap.continuous _)
/-
**ContinuousMultilinearMap.iteratedFDeriv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMultilinearMap`。
形式化陈述：iteratedFDeriv_eq (n : Nat) : iteratedFDeriv 𝕜 n f = f.iteratedFDeriv n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFTaylorSeriesUpTo.eq_iteratedFDeriv`：HasFTaylorSeriesUpTo.eq_iterated
FDeriv (h : HasFTaylorSeriesUpTo n f p) {m : Nat} (hmn : m <= n) (x : E) : p x m
 = iteratedFDeriv 𝕜 m f x
· 使用定理 `ContinuousMultilinearMap.hasFTaylorSeriesUpTo_iteratedFDeriv`：hasFTaylor
SeriesUpTo_iteratedFDeriv : HasFTaylorSeriesUpTo ⊤ f (fun v n => f.iteratedFDeri
v n v)
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem iteratedFDeriv_eq (n : ℕ) :
    iteratedFDeriv 𝕜 n f = f.iteratedFDeriv n :=
  funext fun x ↦ (f.hasFTaylorSeriesUpTo_iteratedFDeriv.eq_iteratedFDeriv (m := n) le_top x).symm
/-
**ContinuousMultilinearMap.norm_iteratedFDeriv_le** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousMultilinearMap`。
形式化陈述：norm_iteratedFDeriv_le (n : Nat) (x : (i : ι) -> E i) : ‖iteratedFDeriv 𝕜 
n f x‖ <= Nat.descFactorial (Fintype.card ι) n * ‖f‖ * ‖x‖ ^ (Fintype.card ι - n
)
参数：n : Nat；x : (i : ι) -> E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.iteratedFDeriv_eq`：iteratedFDeriv_eq (n : Nat) 
: iteratedFDeriv 𝕜 n f = f.iteratedFDeriv n
· 使用引理 `ContinuousMultilinearMap.norm_iteratedFDeriv_le'`：norm_iteratedFDeriv_le
' (f : ContinuousMultilinearMap 𝕜 E₁ G) (k : Nat) (x : (i : ι) -> E₁ i) : ‖f.ite
ratedFDeriv k x‖ <= Nat.descFactorial …
-/
theorem norm_iteratedFDeriv_le (n : ℕ) (x : (i : ι) → E i) :
    ‖iteratedFDeriv 𝕜 n f x‖
      ≤ Nat.descFactorial (Fintype.card ι) n * ‖f‖ * ‖x‖ ^ (Fintype.card ι - n) := by
  rw [f.iteratedFDeriv_eq]
  exact f.norm_iteratedFDeriv_le' n x

end ContinuousMultilinearMap

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F)

open Fintype ContinuousLinearMap in
/-
**FormalMultilinearSeries.derivSeries_apply_diag** 是 Mathlib 中的一个定理，位于命名空间 `Form
alMultilinearSeries`。
形式化陈述：derivSeries_apply_diag (n : Nat) (x : E) : derivSeries p n (fun _ => x) x 
= (n + 1) • p (n + 1) fun _ => x
参数：n : Nat；x : E。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
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
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Fin.snoc_zero`：snoc_zero {α : Sort*} (p : Fin 0 -> α) (x : α) : Fin.snoc
 p x = fun _ => x
· 使用定理 `FormalMultilinearSeries.changeOriginSeriesTerm_apply`：changeOriginSeries
Term_apply (k l : Nat) (s : Finset (Fin (k + l))) (hs : s.card = l) (x y : E) : 
(p.changeOriginSeriesTerm k l s hs (fun _ …
· 使用引理 `Finset.piecewise_same`：piecewise_same : s.piecewise f f = f
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Fintype.card.eq_1`：∀ (α : Type u_4) [inst : Fintype α], Fintype.card α =
 Finset.univ.card
· 使用定理 `Fintype.card_subtype`：Fintype.card_subtype [Fintype α] (p : α -> Prop) [
Fintype {a // p a}] [DecidablePred p] : Fintype.card { x // p x } = #{x | p x}
· 使用定理 `Finset.powerset_univ`：∀ {α : Type u_1} [inst : Fintype α], Finset.univ.p
owerset = Finset.univ
（共 36 条，此处仅展示前 30 条）
-/
theorem derivSeries_apply_diag (n : ℕ) (x : E) :
    derivSeries p n (fun _ ↦ x) x = (n + 1) • p (n + 1) fun _ ↦ x := by
  simp only [derivSeries, compFormalMultilinearSeries_apply, changeOriginSeries,
    compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe,
    Function.comp_apply, map_sum, _root_.sum_apply, continuousMultilinearCurryFin1_apply,
    Matrix.zero_empty]
  convert! Finset.sum_const _
  · rw [Fin.snoc_zero, changeOriginSeriesTerm_apply, Finset.piecewise_same, add_comm]
  · rw [← card, card_subtype, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter,
      Finset.card_powersetCard, ← card, card_fin, eq_comm, add_comm, Nat.choose_succ_self_right]

@[simp]
/-
**FormalMultilinearSeries.derivSeries_coeff_one** 是 Mathlib 中的一个引理，位于命名空间 `Forma
lMultilinearSeries`。
形式化陈述：derivSeries_coeff_one (p : FormalMultilinearSeries 𝕜 𝕜 F) (n : Nat) : p.de
rivSeries.coeff n 1 = (n + 1) • p.coeff (n + 1)
参数：p : FormalMultilinearSeries 𝕜 𝕜 F；n : Nat。
该定理/引理给出了一组等式。
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
· 使用定理 `FormalMultilinearSeries.derivSeries_apply_diag`：derivSeries_apply_diag (
n : Nat) (x : E) : derivSeries p n (fun _ => x) x = (n + 1) • p (n + 1) fun _ =>
 x
-/
lemma derivSeries_coeff_one (p : FormalMultilinearSeries 𝕜 𝕜 F) (n : ℕ) :
    p.derivSeries.coeff n 1 = (n + 1) • p.coeff (n + 1) :=
  p.derivSeries_apply_diag _ _

end FormalMultilinearSeries

namespace HasFPowerSeriesOnBall

open FormalMultilinearSeries ENNReal Nat

variable {p : FormalMultilinearSeries 𝕜 E F} {f : E → F} {x : E} {r : ℝ≥0∞}
  (h : HasFPowerSeriesOnBall f p x r) (y : E)

include h in
/-
**HasFPowerSeriesOnBall.iteratedFDeriv_zero_apply_diag** 是 Mathlib 中的一个定理，位于命名空间
 `HasFPowerSeriesOnBall`。
形式化陈述：iteratedFDeriv_zero_apply_diag : iteratedFDeriv 𝕜 0 f x = p 0
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
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFPowerSeriesOnBall.coeff_zero`：HasFPowerSeriesOnBall.coeff_zero (hf :
 HasFPowerSeriesOnBall f pf x r) (v : Fin 0 -> E) : pf 0 v = f x
-/
theorem iteratedFDeriv_zero_apply_diag : iteratedFDeriv 𝕜 0 f x = p 0 := by
  ext
  simpa using (coeff_zero h _).symm

open ContinuousLinearMap
/-
**HasFPowerSeriesOnBall.factorial_smul'** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerSeri
esOnBall`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem factorial_smul' {n : ℕ} : ∀ {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] {p : FormalMultilinearSeries 𝕜 E F}
    {f : E → F}, HasFPowerSeriesOnBall f p x r →
    n ! • p n (fun _ ↦ y) = iteratedFDeriv 𝕜 n f x (fun _ ↦ y) := by
  induction n with | zero => _ | succ n ih => _ <;> intro F _ _ _ p f h
  · rw [factorial_zero, one_smul, h.iteratedFDeriv_zero_apply_diag]
  · rw [factorial_succ, mul_comm, mul_smul, ← derivSeries_apply_diag,
      ← _root_.smul_apply, ih h.fderiv, iteratedFDeriv_succ_apply_right]
    rfl

variable [CompleteSpace F]
include h

/-- The iterated derivative of an analytic function, on vectors `(y, ..., y)`, is given by `n!`
times the `n`-th term in the power series. For a more general result giving the full iterated
derivative as a sum over the permutations of `Fin n`, see
`HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum`. -/
/-
**HasFPowerSeriesOnBall.factorial_smul** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerSerie
sOnBall`。
形式化陈述：factorial_smul (n : Nat) : n ! • p n (fun _ => y) = iteratedFDeriv 𝕜 n f x
 (fun _ => y)
参数：n : Nat。
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
· 使用定理 `Nat.factorial_zero`：Nat.factorial 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFPowerSeriesOnBall.iteratedFDeriv_zero_apply_diag`：iteratedFDeriv_zer
o_apply_diag : iteratedFDeriv 𝕜 0 f x = p 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `FormalMultilinearSeries.derivSeries_apply_diag`：derivSeries_apply_diag (
n : Nat) (x : E) : derivSeries p n (fun _ => x) x = (n + 1) • p (n + 1) fun _ =>
 x
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `_private.Mathlib.Analysis.Calculus.FDeriv.Analytic.0.HasFPowerSeriesOnBa
ll.factorial_smul'`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Typ
e u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x : E} {r : E
…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `HasFPowerSeriesOnBall.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type v} […
· 使用定理 `iteratedFDeriv_succ_apply_right`：iteratedFDeriv_succ_apply_right {n : Na
t} (m : Fin (n + 1) -> E) : (iteratedFDeriv 𝕜 (n + 1) f x : (Fin (n + 1) -> E) -
> F) m = iteratedFDer…

--- 原说明 ---
The iterated derivative of an analytic function, on vectors `(y, ..., y)`, is gi
ven by `n!`
times the `n`-th term in the power series. For a more general result giving the 
full iterated
derivative as a sum over the permutations of `Fin n`, see
`HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum`.
-/
theorem factorial_smul (n : ℕ) :
    n ! • p n (fun _ ↦ y) = iteratedFDeriv 𝕜 n f x (fun _ ↦ y) := by
  cases n
  · rw [factorial_zero, one_smul, h.iteratedFDeriv_zero_apply_diag]
  · rw [factorial_succ, mul_comm, mul_smul, ← derivSeries_apply_diag,
      ← _root_.smul_apply, factorial_smul' _ h.fderiv, iteratedFDeriv_succ_apply_right]
    rfl
/-
**HasFPowerSeriesOnBall.hasSum_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 `HasFPow
erSeriesOnBall`。
形式化陈述：hasSum_iteratedFDeriv [CharZero 𝕜] {y : E} (hy : y in Metric.eball 0 r) : 
HasSum (fun n => (n ! : 𝕜)⁻¹ • iteratedFDeriv 𝕜 n f x fun _ => y) (f (x + y))
参数：hy : y in Metric.eball 0 r。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFPowerSeriesOnBall.factorial_smul`：factorial_smul (n : Nat) : n ! • p
 n (fun _ => y) = iteratedFDeriv 𝕜 n f x (fun _ => y)
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
-/
theorem hasSum_iteratedFDeriv [CharZero 𝕜] {y : E} (hy : y ∈ Metric.eball 0 r) :
    HasSum (fun n ↦ (n ! : 𝕜)⁻¹ • iteratedFDeriv 𝕜 n f x fun _ ↦ y) (f (x + y)) := by
  convert! h.hasSum hy with n
  rw [← h.factorial_smul y n, smul_comm, ← smul_assoc, nsmul_eq_mul,
    mul_inv_cancel₀ <| cast_ne_zero.mpr n.factorial_ne_zero, one_smul]

end HasFPowerSeriesOnBall

/-!
### Derivative of a linear map into multilinear maps
-/

namespace ContinuousLinearMap

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
  [Fintype ι] {H : Type*} [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

/-
**ContinuousLinearMap.hasFDerivAt_uncurry_of_multilinear** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousLinearMap`。
形式化陈述：hasFDerivAt_uncurry_of_multilinear [DecidableEq ι] (f : E ->L[𝕜] Continuou
sMultilinearMap 𝕜 G F) (v : E × Π i, G i) : HasFDerivAt (fun (p : E × Π i, G i) 
=> f p.1 p.2) ((f.flipMultilinear v.2) ∘L (.fst _ _ _) + ∑ i : ι, ((f v.1).toCon
tinuousLinearMap v.2 i) ∘L (.proj _) ∘L (.snd _ _ _)) v
参数：f : E ->L[𝕜] ContinuousMultilinearMap 𝕜 G F；v : E × Π i, G i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.continuousMultilinearMap_apply`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 :
 NormedSpace 𝕜 F] {ι : Type u_2}…
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasFDerivAt_pi'`：hasFDerivAt_pi' : HasFDerivAt Φ Φ' x ↔ forall i, HasFDe
rivAt (fun x => Φ x i) ((proj i).comp Φ') x
· 使用定理 `hasFDerivAt_snd`：hasFDerivAt_snd : HasFDerivAt (@Prod.snd E F) (snd 𝕜 E 
F) p
-/
theorem hasFDerivAt_uncurry_of_multilinear [DecidableEq ι]
    (f : E →L[𝕜] ContinuousMultilinearMap 𝕜 G F) (v : E × Π i, G i) :
    HasFDerivAt (fun (p : E × Π i, G i) ↦ f p.1 p.2)
      ((f.flipMultilinear v.2) ∘L (.fst _ _ _) +
        ∑ i : ι, ((f v.1).toContinuousLinearMap v.2 i) ∘L (.proj _) ∘L (.snd _ _ _)) v :=
  (f ∘L .fst 𝕜 E (∀ i, G i)).hasFDerivAt.continuousMultilinearMap_apply
    (hasFDerivAt_pi'.mp (hasFDerivAt_snd (E := E) (F := ∀ i, G i)))

/-- Given `f` a linear map into multilinear maps, then the derivative
of `x ↦ f (a x) (b₁ x, ..., bₙ x)` at `x` applied to a vector `v` is given by
`f (a' v) (b₁ x, ...., bₙ x) + ∑ i, f a (b₁ x, ..., b'ᵢ v, ..., bₙ x)`. Version inside a set. -/
/-
**ContinuousLinearMap._root_.HasFDerivWithinAt.linear_multilinear_comp** 是 Mathl
ib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f` a linear map into multilinear maps, then the derivative
of `x ↦ f (a x) (b₁ x, ..., bₙ x)` at `x` applied to a vector `v` is given by
`f (a' v) (b₁ x, ...., bₙ x) + ∑ i, f a (b₁ x, ..., b'ᵢ v, ..., bₙ x)`. Version 
inside a set.
-/
theorem _root_.HasFDerivWithinAt.linear_multilinear_comp
    [DecidableEq ι] {a : H → E} {a' : H →L[𝕜] E}
    {b : ∀ i, H → G i} {b' : ∀ i, H →L[𝕜] G i} {s : Set H} {x : H}
    (ha : HasFDerivWithinAt a a' s x) (hb : ∀ i, HasFDerivWithinAt (b i) (b' i) s x)
    (f : E →L[𝕜] ContinuousMultilinearMap 𝕜 G F) :
    HasFDerivWithinAt (fun y ↦ f (a y) (fun i ↦ b i y))
      ((f.flipMultilinear (fun i ↦ b i x)) ∘L a' +
        ∑ i, ((f (a x)).toContinuousLinearMap (fun j ↦ b j x) i) ∘L (b' i)) s x :=
  (f.hasFDerivAt.comp_hasFDerivWithinAt x ha).continuousMultilinearMap_apply hb

/-- Given `f` a linear map into multilinear maps, then the derivative
of `x ↦ f (a x) (b₁ x, ..., bₙ x)` at `x` applied to a vector `v` is given by
`f (a' v) (b₁ x, ...., bₙ x) + ∑ i, f a (b₁ x, ..., b'ᵢ v, ..., bₙ x)`. -/
/-
**ContinuousLinearMap._root_.HasFDerivAt.linear_multilinear_comp** 是 Mathlib 中的一
个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f` a linear map into multilinear maps, then the derivative
of `x ↦ f (a x) (b₁ x, ..., bₙ x)` at `x` applied to a vector `v` is given by
`f (a' v) (b₁ x, ...., bₙ x) + ∑ i, f a (b₁ x, ..., b'ᵢ v, ..., bₙ x)`.
-/
theorem _root_.HasFDerivAt.linear_multilinear_comp [DecidableEq ι] {a : H → E} {a' : H →L[𝕜] E}
    {b : ∀ i, H → G i} {b' : ∀ i, H →L[𝕜] G i} {x : H}
    (ha : HasFDerivAt a a' x) (hb : ∀ i, HasFDerivAt (b i) (b' i) x)
    (f : E →L[𝕜] ContinuousMultilinearMap 𝕜 G F) :
    HasFDerivAt (fun y ↦ f (a y) (fun i ↦ b i y))
      ((f.flipMultilinear (fun i ↦ b i x)) ∘L a' +
        ∑ i, ((f (a x)).toContinuousLinearMap (fun j ↦ b j x) i) ∘L (b' i)) x :=
  (f.hasFDerivAt.comp x ha).continuousMultilinearMap_apply hb

end ContinuousLinearMap

