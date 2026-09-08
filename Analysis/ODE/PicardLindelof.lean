/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Winston Yin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Picard-Lindelöf (Cauchy-Lipschitz) Theorem

We prove the (local) existence of integral curves and flows to time-dependent vector fields.

Let `f : ℝ → E → E` be a time-dependent (local) vector field on a Banach space, and let `t₀ : ℝ`
and `x₀ : E`. If `f` is Lipschitz continuous in `x` within a closed ball around `x₀` of radius
`a ≥ 0` at every `t` and continuous in `t` at every `x`, then there exists a (local) solution
`α : ℝ → E` to the initial value problem `α t₀ = x₀` and `deriv α t = f t (α t)` for all
`t ∈ Icc tmin tmax`, where `L * max (tmax - t₀) (t₀ - tmin) ≤ a`.

We actually prove a more general version of this theorem for the existence of local flows. If there
is some `r ≥ 0` such that `L * max (tmax - t₀) (t₀ - tmin) ≤ a - r`, then for every
`x ∈ closedBall x₀ r`, there exists a (local) solution `α x` with the initial condition `α t₀ = x`.
In other words, there exists a local flow `α : E → ℝ → E` defined on `closedBall x₀ r` and
`Icc tmin tmax`.

The proof relies on demonstrating the existence of a solution `α` to the following integral
equation:
$$\alpha(t) = x_0 + \int_{t_0}^t f(\tau, \alpha(\tau))\,\mathrm{d}\tau.$$
This is done via the contraction mapping theorem, applied to the space of Lipschitz continuous
functions from a closed interval to a Banach space. The needed contraction map is constructed by
repeated applications of the right-hand side of this equation.

## Main definitions and results

* `picard f t₀ x₀ α t`: the Picard iteration, applied to the curve `α`
* `IsPicardLindelof`: the structure holding the assumptions of the Picard-Lindelöf theorem

The public-facing existence theorems stated using the integral curve API are in
`Mathlib.Analysis.ODE.ExistUnique`.

## Implementation notes

* The structure `FunSpace` and theorems within this namespace are implementation details of the
  proof of the Picard-Lindelöf theorem and are not intended to be used outside of this file.
* Some sources, such as Lang, define `FunSpace` as the space of continuous functions from a closed
  interval to a closed ball. We instead define `FunSpace` here as the space of Lipschitz continuous
  functions from a closed interval. This slightly stronger condition allows us to postpone the usage
  of the completeness condition on the space `E` until the application of the contraction mapping
  theorem.
* We have chosen to formalise many of the real constants as `ℝ≥0`, so that the non-negativity of
  certain quantities constructed from them can be shown more easily. When subtraction is involved,
  especially note whether it is the usual subtraction between two reals or the truncated subtraction
  between two non-negative reals.
* In this file, We only prove the existence of a solution. For uniqueness, see
  `IsIntegralCurveOn.eqOn` and related theorems in `Mathlib/Analysis/ODE/ExistUnique.lean`.

## Tags

differential equation, dynamical system, initial value problem, Picard-Lindelöf theorem,
Cauchy-Lipschitz theorem

-/

@[expose] public section

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

/-! ## Assumptions of the Picard-Lindelöf theorem-/

/-- Prop structure holding the assumptions of the Picard-Lindelöf theorem.
`IsPicardLindelof f t₀ x₀ a r L K`, where `t₀ ∈ Icc tmin tmax`, means that the time-dependent vector
field `f` satisfies the conditions to admit an integral curve `α : ℝ → E` to `f` defined on
`Icc tmin tmax` with the initial condition `α t₀ = x`, where `‖x - x₀‖ ≤ r`. Note that the initial
point `x` is allowed to differ from the point `x₀` about which the conditions on `f` are stated. -/
/-
**IsPicardLindelof** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{E : Type u_1} →   [NormedAddCommGroup E] →     (ℝ → E → E) → {tmin tmax :
 ℝ} → ↑(Set.Icc tmin tmax) → E → NNReal → NNReal → NNReal → NNReal → Prop
参数：ℝ → E → E；Set.Icc tmin tmax。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prop structure holding the assumptions of the Picard-Lindelöf theorem.
`IsPicardLindelof f t₀ x₀ a r L K`, where `t₀ ∈ Icc tmin tmax`, means that the t
ime-dependent vector
field `f` satisfies the conditions to admit an integral curve `α : ℝ → E` to `f`
 defined on
`Icc tmin tmax` with the initial condition `α t₀ = x`, where `‖x - x₀‖ ≤ r`. Not
e that the initial
point `x` is allowed to differ from the point `x₀` about which the conditions on
 `f` are stated.
-/
structure IsPicardLindelof {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) (a r L K : ℝ≥0) : Prop where
  /-- The vector field at any time is Lipschitz with constant `K` within a closed ball. -/
  lipschitzOnWith : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ a)
  /-- The vector field is continuous in time within a closed ball. -/
  continuousOn : ∀ x ∈ closedBall x₀ a, ContinuousOn (f · x) (Icc tmin tmax)
  /-- `L` is an upper bound of the norm of the vector field. -/
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a, ‖f t x‖ ≤ L
  /-- The time interval of validity -/
  mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r

namespace ODE

/-! ## Integral equation

For any time-dependent vector field `f : ℝ → E → E`, we define an integral equation that is
equivalent to the initial value problem defined by `f`.
-/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E} {t₀ tmin tmax : ℝ}

/-- The Picard iteration. It will be shown that if `α : ℝ → E` and `picard f t₀ x₀ α` agree on an
interval containing `t₀`, then `α` is a solution to `f` with `α t₀ = x₀` on this interval. -/
/-
**ODE.picard** 是 Mathlib 中的一个定义，位于命名空间 `ODE`。
形式化陈述：picard (f : Real -> E -> E) (t₀ : Real) (x₀ : E) (α : Real -> E) : Real ->
 E
参数：f : Real -> E -> E；t₀ : Real；x₀ : E；α : Real -> E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Picard iteration. It will be shown that if `α : ℝ → E` and `picard f t₀ x₀ α
` agree on an
interval containing `t₀`, then `α` is a solution to `f` with `α t₀ = x₀` on this
 interval.
-/
noncomputable def picard (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (α : ℝ → E) : ℝ → E :=
  fun t ↦ x₀ + ∫ τ in t₀..t, f τ (α τ)

@[simp]
/-
**ODE.picard_apply** 是 Mathlib 中的一个引理，位于命名空间 `ODE`。
形式化陈述：picard_apply {x₀ : E} {t : Real} : picard f t₀ x₀ α t = x₀ + ∫ τ in t₀..t,
 f τ (α τ)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma picard_apply {x₀ : E} {t : ℝ} : picard f t₀ x₀ α t = x₀ + ∫ τ in t₀..t, f τ (α τ) := rfl
/-
**ODE.picard_apply** 是 Mathlib 中的一个引理，位于命名空间 `ODE`。
形式化陈述：picard_apply {x₀ : E} {t : Real} : picard f t₀ x₀ α t = x₀ + ∫ τ in t₀..t,
 f τ (α τ)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma picard_apply₀ {x₀ : E} : picard f t₀ x₀ α t₀ = x₀ := by simp

/-- Given a $C^n$ time-dependent vector field `f` and a $C^n$ curve `α`, the composition `f t (α t)`
is $C^n$ in `t`. -/
/-
**ODE.contDiffOn_comp** 是 Mathlib 中的一个引理，位于命名空间 `ODE`。
形式化陈述：contDiffOn_comp {n : WithTop Nat∞} (hf : ContDiffOn Real n (uncurry f) (s 
×ˢ u)) (hα : ContDiffOn Real n α s) (hmem : forall t in s, α t in u) : ContDiffO
n Real n (fun t => f t (α t)) s
参数：hf : ContDiffOn Real n (uncurry f) (s ×ˢ u)；hα : ContDiffOn Real n α s；hmem :
 forall t in s, α t in u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `ContDiffOn.prodMk`：ContDiffOn.prodMk {s : Set E} {f : E -> F} {g : E -> 
G} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x :
 E => (…
· 使用定理 `contDiffOn_id`：contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E -> E) s

--- 原说明 ---
Given a $C^n$ time-dependent vector field `f` and a $C^n$ curve `α`, the composi
tion `f t (α t)`
is $C^n$ in `t`.
-/
lemma contDiffOn_comp {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) (s ×ˢ u))
    (hα : ContDiffOn ℝ n α s) (hmem : ∀ t ∈ s, α t ∈ u) :
    ContDiffOn ℝ n (fun t ↦ f t (α t)) s := by
  simpa only [← uncurry_apply_pair f] using! hf.comp (by fun_prop) (by tauto)

/-- Given a continuous time-dependent vector field `f` and a continuous curve `α`, the composition
`f t (α t)` is continuous in `t`. -/
/-
**ODE.continuousOn_comp** 是 Mathlib 中的一个引理，位于命名空间 `ODE`。
形式化陈述：continuousOn_comp (hf : ContinuousOn (uncurry f) (s ×ˢ u)) (hα : Continuou
sOn α s) (hmem : MapsTo α s u) : ContinuousOn (fun t => f t (α t)) s
参数：hf : ContinuousOn (uncurry f) (s ×ˢ u)；hα : ContinuousOn α s；hmem : MapsTo α 
s u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_zero`：contDiffOn_zero : ContDiffOn 𝕜 0 f s ↔ ContinuousOn f s
· 使用引理 `ODE.contDiffOn_comp`：contDiffOn_comp {n : WithTop Nat∞} (hf : ContDiffOn
 Real n (uncurry f) (s ×ˢ u)) (hα : ContDiffOn Real n α s) (hmem : forall t in s
, α t in …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Given a continuous time-dependent vector field `f` and a continuous curve `α`, t
he composition
`f t (α t)` is continuous in `t`.
-/
lemma continuousOn_comp
    (hf : ContinuousOn (uncurry f) (s ×ˢ u)) (hα : ContinuousOn α s) (hmem : MapsTo α s u) :
    ContinuousOn (fun t ↦ f t (α t)) s :=
  contDiffOn_zero.mp <| (contDiffOn_comp (contDiffOn_zero.mpr hf) (contDiffOn_zero.mpr hα) hmem)

end

/-! ## Space of Lipschitz functions on a closed interval

We define the space of Lipschitz continuous functions from a closed interval. This will be shown to
be a complete metric space on which `picard` is a contracting map, leading to a fixed point that
will serve as the solution to the ODE. The domain is a closed interval in order to easily inherit
the sup metric from continuous maps on compact spaces. We cannot use functions `ℝ → E` with junk
values outside the domain, as the supremum within a closed interval will only be a pseudo-metric,
and the contracting map will fail to have a fixed point. In order to accommodate flows, we do not
require a specific initial condition. Rather, `FunSpace` contains curves whose initial condition is
within a closed ball.
-/

/-- The space of `L`-Lipschitz functions `α : Icc tmin tmax → E` -/
/-
**ODE.FunSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 `ODE`。
形式化陈述：{E : Type u_1} → [NormedAddCommGroup E] → {tmin tmax : ℝ} → ↑(Set.Icc tmin
 tmax) → E → NNReal → NNReal → Type u_1
参数：Set.Icc tmin tmax。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of `L`-Lipschitz functions `α : Icc tmin tmax → E`
-/
structure FunSpace {E : Type*} [NormedAddCommGroup E]
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) (r L : ℝ≥0) where
  /-- The domain is `Icc tmin tmax`. -/
  toFun : Icc tmin tmax → E
  lipschitzWith : LipschitzWith L toFun
  mem_closedBall₀ : toFun t₀ ∈ closedBall x₀ r

namespace FunSpace

variable {E : Type*} [NormedAddCommGroup E]

section

variable {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a r L : ℝ≥0}

/-
**ODE.FunSpace.** 是 Mathlib 中的一个实例，位于命名空间 `ODE.FunSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (FunSpace t₀ x₀ r L) fun _ ↦ Icc tmin tmax → E := ⟨fun α ↦ α.toFun⟩

@[ext]
/-
**ODE.FunSpace.ext** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：ext {α β : FunSpace t₀ x₀ r L} (h : forall t, α t = β t) : α = β
参数：h : forall t, α t = β t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ODE.FunSpace.mk.injEq`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] {t
min tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E} {r L : NNReal}   (toFun : ↑(S
et.Icc tmin…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ext {α β : FunSpace t₀ x₀ r L} (h : ∀ t, α t = β t) : α = β := by
  cases α; cases β; simp only [mk.injEq]; ext t; exact h t

/-- `FunSpace t₀ x₀ r L` contains the constant map at `x₀`. -/
/-
**ODE.FunSpace.** 是 Mathlib 中的一个实例，位于命名空间 `ODE.FunSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FunSpace t₀ x₀ r L` contains the constant map at `x₀`.
-/
instance : Inhabited (FunSpace t₀ x₀ r L) :=
  ⟨fun _ ↦ x₀, (LipschitzWith.const _).weaken zero_le, mem_closedBall_self r.2⟩
/-
**ODE.FunSpace.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ODE.FunSpace`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] {tmin tmax : ℝ} {t₀ : ↑(Set
.Icc tmin tmax)} {x₀ : E} {r L : NNReal}   (α : ODE.FunSpace t₀ x₀ L r), Continu
ous α.toFun
参数：Set.Icc tmin tmax；α : ODE.FunSpace t₀ x₀ L r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `ODE.FunSpace.lipschitzWith`：∀ {E : Type u_1} [inst : NormedAddCommGroup 
E] {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E} {r L : NNReal}   (self :
 ODE.FunSpace t₀…
-/
protected lemma continuous (α : FunSpace t₀ x₀ L r) : Continuous α := α.lipschitzWith.continuous

/-- The embedding of `FunSpace` into the space of continuous maps -/
/-
**ODE.FunSpace.toContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 `ODE.FunSpace`。
形式化陈述：toContinuousMap : FunSpace t₀ x₀ r L ↪ C(Icc tmin tmax, E)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ODE.FunSpace.continuous`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
{tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E} {r L : NNReal}   (α : ODE.F
unSpace t₀ x₀…

--- 原说明 ---
The embedding of `FunSpace` into the space of continuous maps
-/
def toContinuousMap : FunSpace t₀ x₀ r L ↪ C(Icc tmin tmax, E) :=
  ⟨fun α ↦ ⟨α, α.continuous⟩, fun α β h ↦ by cases α; cases β; simpa using h⟩

@[simp]
/-
**ODE.FunSpace.toContinuousMap_apply_eq_apply** 是 Mathlib 中的一个引理，位于命名空间 `ODE.Fun
Space`。
形式化陈述：toContinuousMap_apply_eq_apply (α : FunSpace t₀ x₀ r L) (t : Icc tmin tmax
) : α.toContinuousMap t = α t
参数：α : FunSpace t₀ x₀ r L；t : Icc tmin tmax。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousMap_apply_eq_apply (α : FunSpace t₀ x₀ r L) (t : Icc tmin tmax) :
    α.toContinuousMap t = α t := rfl

/-- When the radius is zero, a curve in `FunSpace` evaluated at `t₀` equals `x₀`. -/
/-
**ODE.FunSpace.apply_of_zero** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：apply_of_zero (α : FunSpace t₀ x₀ 0 L) : α t₀ = x₀
参数：α : FunSpace t₀ x₀ 0 L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.closedBall_zero`：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, M
etric.closedBall x 0 = {x}
· 使用定理 `ODE.FunSpace.mem_closedBall₀`：∀ {E : Type u_1} [inst : NormedAddCommGrou
p E] {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E} {r L : NNReal}   (self
 : ODE.FunSpace t₀…

--- 原说明 ---
When the radius is zero, a curve in `FunSpace` evaluated at `t₀` equals `x₀`.
-/
lemma apply_of_zero (α : FunSpace t₀ x₀ 0 L) : α t₀ = x₀ := by
  simpa using α.mem_closedBall₀

/-- The metric between two curves `α` and `β` is the supremum of the metric between `α t` and `β t`
over all `t` in the domain. This is finite when the domain is compact, such as a closed
interval in our case. -/
/-
**ODE.FunSpace.** 是 Mathlib 中的一个实例，位于命名空间 `ODE.FunSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The metric between two curves `α` and `β` is the supremum of the metric between 
`α t` and `β t`
over all `t` in the domain. This is finite when the domain is compact, such as a
 closed
interval in our case.
-/
noncomputable instance : MetricSpace (FunSpace t₀ x₀ r L) :=
  MetricSpace.induced toContinuousMap toContinuousMap.injective inferInstance
/-
**ODE.FunSpace.isUniformInducing_toContinuousMap** 是 Mathlib 中的一个引理，位于命名空间 `ODE.
FunSpace`。
形式化陈述：isUniformInducing_toContinuousMap : IsUniformInducing fun α : FunSpace t₀ 
x₀ r L => α.toContinuousMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isUniformInducing_toContinuousMap :
    IsUniformInducing fun α : FunSpace t₀ x₀ r L ↦ α.toContinuousMap := ⟨rfl⟩
/-
**ODE.FunSpace.range_toContinuousMap** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：range_toContinuousMap : range (fun α : FunSpace t₀ x₀ r L => α.toContinuou
sMap) = { α : C(Icc tmin tmax, E) | LipschitzWith L α ∧ α t₀ in closedBall x₀ r 
}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
lemma range_toContinuousMap :
    range (fun α : FunSpace t₀ x₀ r L ↦ α.toContinuousMap) =
      { α : C(Icc tmin tmax, E) | LipschitzWith L α ∧ α t₀ ∈ closedBall x₀ r } := by
  ext α
  constructor
  · rintro ⟨⟨α, hα1, hα2⟩, rfl⟩
    exact ⟨hα1, hα2⟩
  · rintro ⟨hα1, hα2⟩
    exact ⟨⟨α, hα1, hα2⟩, rfl⟩

/-- We show that `FunSpace` is complete in order to apply the contraction mapping theorem. -/
/-
**ODE.FunSpace.** 是 Mathlib 中的一个实例，位于命名空间 `ODE.FunSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We show that `FunSpace` is complete in order to apply the contraction mapping th
eorem.
-/
instance [CompleteSpace E] : CompleteSpace (FunSpace t₀ x₀ r L) := by
  rw [completeSpace_iff_isComplete_range isUniformInducing_toContinuousMap]
  apply IsClosed.isComplete
  rw [range_toContinuousMap, ofPred_and]
  apply isClosed_setOfPred_lipschitzWith L |>.preimage continuous_coeFun |>.inter
  simp_rw [mem_closedBall_iff_norm]
  exact isClosed_le (by fun_prop) (by fun_prop)

/-- Extend the domain of `α` from `Icc tmin tmax` to `ℝ` such that `α t = α tmin` for all `t ≤ tmin`
and `α t = α tmax` for all `t ≥ tmax`. -/
/-
**ODE.FunSpace.compProj** 是 Mathlib 中的一个定义，位于命名空间 `ODE.FunSpace`。
形式化陈述：compProj (α : FunSpace t₀ x₀ r L) (t : Real) : E
参数：α : FunSpace t₀ x₀ r L；t : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend the domain of `α` from `Icc tmin tmax` to `ℝ` such that `α t = α tmin` fo
r all `t ≤ tmin`
and `α t = α tmax` for all `t ≥ tmax`.
-/
noncomputable def compProj (α : FunSpace t₀ x₀ r L) (t : ℝ) : E :=
  α <| projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t

@[simp]
/-
**ODE.FunSpace.compProj_apply** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：compProj_apply {α : FunSpace t₀ x₀ r L} {t : Real} : α.compProj t = α (pro
jIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compProj_apply {α : FunSpace t₀ x₀ r L} {t : ℝ} :
    α.compProj t = α (projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t) := rfl
/-
**ODE.FunSpace.compProj_val** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：compProj_val {α : FunSpace t₀ x₀ r L} {t : Icc tmin tmax} : α.compProj t =
 α t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.projIcc_val`：projIcc_val (x : Icc a b) : projIcc a b h x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compProj_val {α : FunSpace t₀ x₀ r L} {t : Icc tmin tmax} :
    α.compProj t = α t := by simp only [compProj_apply, projIcc_val]
/-
**ODE.FunSpace.compProj_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：compProj_of_mem {α : FunSpace t₀ x₀ r L} {t : Real} (ht : t in Icc tmin tm
ax) : α.compProj t = α ⟨t, ht⟩
参数：ht : t in Icc tmin tmax。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ODE.FunSpace.compProj_apply`：compProj_apply {α : FunSpace t₀ x₀ r L} {t 
: Real} : α.compProj t = α (projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t)
· 使用定理 `Set.projIcc_of_mem`：projIcc_of_mem (hx : x in Icc a b) : projIcc a b h x
 = ⟨x, hx⟩
-/
lemma compProj_of_mem {α : FunSpace t₀ x₀ r L} {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    α.compProj t = α ⟨t, ht⟩ := by rw [compProj_apply, projIcc_of_mem]

@[continuity, fun_prop]
/-
**ODE.FunSpace.continuous_compProj** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：continuous_compProj (α : FunSpace t₀ x₀ r L) : Continuous α.compProj
参数：α : FunSpace t₀ x₀ r L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ODE.FunSpace.continuous`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
{tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E} {r L : NNReal}   (α : ODE.F
unSpace t₀ x₀…
· 使用定理 `continuous_projIcc`：continuous_projIcc : Continuous (projIcc a b h)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
lemma continuous_compProj (α : FunSpace t₀ x₀ r L) : Continuous α.compProj :=
  α.continuous.comp continuous_projIcc

/-- The image of a function in `FunSpace` is contained within a closed ball. -/
/-
**ODE.FunSpace.mem_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `ODE.FunSpace`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] {tmin tmax : ℝ} {t₀ : ↑(Set
.Icc tmin tmax)} {x₀ : E} {a r L : NNReal}   {α : ODE.FunSpace t₀ x₀ r L},   ↑L 
* max (tmax - ↑t₀) (↑t₀ - tmin) ≤ ↑a - ↑r → ∀ {t : ↑(Set.Icc tmin tmax)}, α.toFu
n t ∈ Metric.closedBall x₀ ↑a
参数：Set.Icc tmin tmax；tmax - ↑t₀；↑t₀ - tmin；Set.Icc tmin tmax。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `norm_sub_le_norm_sub_add_norm_sub`：∀ {E : Type u_5} [inst : SeminormedAd
dGroup E] (a b c : E), ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
· 使用定理 `ODE.FunSpace.lipschitzWith`：∀ {E : Type u_1} [inst : NormedAddCommGroup 
E] {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E} {r L : NNReal}   (self :
 ODE.FunSpace t₀…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closedBall_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup
 E] {a b : E} {r : ℝ}, b ∈ Metric.closedBall a r ↔ ‖b - a‖ ≤ r
· 使用定理 `ODE.FunSpace.mem_closedBall₀`：∀ {E : Type u_1} [inst : NormedAddCommGrou
p E] {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E} {r L : NNReal}   (self
 : ODE.FunSpace t₀…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `abs_sub_le_max_sub`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : L
inearOrder G] [IsOrderedAddMonoid G] {a b c : G},   a ≤ b → b ≤ c → ∀ (d : G), |
b - d| ≤…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a

--- 原说明 ---
The image of a function in `FunSpace` is contained within a closed ball.
-/
protected lemma mem_closedBall
    {α : FunSpace t₀ x₀ r L} (h : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r) {t : Icc tmin tmax} :
    α t ∈ closedBall x₀ a := by
  rw [mem_closedBall, dist_eq_norm]
  calc
    ‖α t - x₀‖ ≤ ‖α t - α t₀‖ + ‖α t₀ - x₀‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ L * |t.1 - t₀.1| + r := by
      apply add_le_add _ <| mem_closedBall_iff_norm.mp α.mem_closedBall₀
      rw [← dist_eq_norm]
      exact α.lipschitzWith.dist_le_mul t t₀
    _ ≤ L * max (tmax - t₀) (t₀ - tmin) + r := by
      gcongr
      exact abs_sub_le_max_sub t.2.1 t.2.2 _
    _ ≤ a - r + r := by gcongr
    _ = a := sub_add_cancel _ _
/-
**ODE.FunSpace.compProj_mem_closedBall** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：compProj_mem_closedBall (α : FunSpace t₀ x₀ r L) (h : L * max (tmax - t₀) 
(t₀ - tmin) <= a - r) {t : Real} : α.compProj t in closedBall x₀ a
参数：α : FunSpace t₀ x₀ r L；h : L * max (tmax - t₀) (t₀ - tmin) <= a - r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ODE.FunSpace.mem_closedBall`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E} {a r L : NNReal}   {α :
 ODE.FunSpace t₀ …
-/
lemma compProj_mem_closedBall
    (α : FunSpace t₀ x₀ r L) (h : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r) {t : ℝ} :
    α.compProj t ∈ closedBall x₀ a :=
  α.mem_closedBall h

end

/-! ## Contracting map on the space of Lipschitz functions -/

section

variable [NormedSpace ℝ E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x y : E} {a r L K : ℝ≥0}

/-- The integrand in `next` is continuous. -/
/-
**ODE.FunSpace.continuousOn_comp_compProj** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpac
e`。
形式化陈述：continuousOn_comp_compProj (hf : IsPicardLindelof f t₀ x₀ a r L K) (α : Fu
nSpace t₀ x₀ r L) : ContinuousOn (fun t' => f t' (α.compProj t')) (Icc tmin tmax
)
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；α : FunSpace t₀ x₀ r L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ODE.continuousOn_comp`：continuousOn_comp (hf : ContinuousOn (uncurry f) 
(s ×ˢ u)) (hα : ContinuousOn α s) (hmem : MapsTo α s u) : ContinuousOn (fun t =>
 f t (α t))…
· 使用定理 `continuousOn_prod_of_continuousOn_lipschitzOnWith'`：continuousOn_prod_of
_continuousOn_lipschitzOnWith' [TopologicalSpace α] [PseudoEMetricSpace β] [Pseu
doEMetricSpace γ] (f : α × β -> γ) {s : …
· 使用定理 `IsPicardLindelof.lipschitzOnWith`：∀ {E : Type u_1} [inst : NormedAddComm
Group E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   
{a r L K : NNReal},   …
· 使用定理 `IsPicardLindelof.continuousOn`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   {a 
r L K : NNReal},   …
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `ODE.FunSpace.continuous_compProj`：continuous_compProj (α : FunSpace t₀ x
₀ r L) : Continuous α.compProj
· 使用定理 `ODE.FunSpace.mem_closedBall`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E} {a r L : NNReal}   {α :
 ODE.FunSpace t₀ …
· 使用定理 `IsPicardLindelof.mul_max_le`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   {a r 
L K : NNReal}, Is…

--- 原说明 ---
The integrand in `next` is continuous.
-/
lemma continuousOn_comp_compProj (hf : IsPicardLindelof f t₀ x₀ a r L K) (α : FunSpace t₀ x₀ r L) :
    ContinuousOn (fun t' ↦ f t' (α.compProj t')) (Icc tmin tmax) :=
  continuousOn_comp
    (continuousOn_prod_of_continuousOn_lipschitzOnWith' (uncurry f) K hf.lipschitzOnWith
      hf.continuousOn)
    α.continuous_compProj.continuousOn
    fun _ _ ↦ α.mem_closedBall hf.mul_max_le

/-- The integrand in `next` is integrable. -/
/-
**ODE.FunSpace.intervalIntegrable_comp_compProj** 是 Mathlib 中的一个引理，位于命名空间 `ODE.F
unSpace`。
形式化陈述：intervalIntegrable_comp_compProj (hf : IsPicardLindelof f t₀ x₀ a r L K) (
α : FunSpace t₀ x₀ r L) (t : Icc tmin tmax) : IntervalIntegrable (fun t' => f t'
 (α.compProj t')) volume t₀ t
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；α : FunSpace t₀ x₀ r L；t : Icc tmin tma
x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `ODE.FunSpace.continuousOn_comp_compProj`：continuousOn_comp_compProj (hf 
: IsPicardLindelof f t₀ x₀ a r L K) (α : FunSpace t₀ x₀ r L) : ContinuousOn (fun
 t' => f t' (α.compProj t')) …
· 使用引理 `Set.uIcc_subset_Icc`：uIcc_subset_Icc (ha : a₁ in Icc a₂ b₂) (hb : b₁ in 
Icc a₂ b₂) : [[a₁, b₁]] subseteq Icc a₂ b₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The integrand in `next` is integrable.
-/
lemma intervalIntegrable_comp_compProj (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (α : FunSpace t₀ x₀ r L) (t : Icc tmin tmax) :
    IntervalIntegrable (fun t' ↦ f t' (α.compProj t')) volume t₀ t := by
  apply ContinuousOn.intervalIntegrable
  apply α.continuousOn_comp_compProj hf |>.mono
  exact uIcc_subset_Icc t₀.2 t.2

/-- The map on `FunSpace` defined by `picard`, some `n`-th iterate of which will be a contracting
map -/
/-
**ODE.FunSpace.next** 是 Mathlib 中的一个定义，位于命名空间 `ODE.FunSpace`。
形式化陈述：next (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r) (
α : FunSpace t₀ x₀ r L) : FunSpace t₀ x₀ r L where toFun t
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r；α : FunSpace 
t₀ x₀ r L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map on `FunSpace` defined by `picard`, some `n`-th iterate of which will be 
a contracting
map
-/
noncomputable def next (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) : FunSpace t₀ x₀ r L where
  toFun t := picard f t₀ x α.compProj t
  lipschitzWith := LipschitzWith.of_dist_le_mul fun t₁ t₂ ↦ by
    rw [dist_eq_norm, picard_apply, picard_apply, add_sub_add_left_eq_sub,
      integral_interval_sub_left (intervalIntegrable_comp_compProj hf _ t₁)
        (intervalIntegrable_comp_compProj hf _ t₂), Subtype.dist_eq, Real.dist_eq]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    -- Can `grind` do this in the future?
    have ht : t ∈ Icc tmin tmax := subset_trans uIoc_subset_uIcc (uIcc_subset_Icc t₂.2 t₁.2) ht
    exact hf.norm_le _ ht _ <| α.mem_closedBall hf.mul_max_le
  mem_closedBall₀ := by simp [hx]

@[simp]
/-
**ODE.FunSpace.next_apply** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：next_apply (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x
₀ r) (α : FunSpace t₀ x₀ r L) {t : Icc tmin tmax} : next hf hx α t = picard f t₀
 x α.compProj t
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r；α : FunSpace 
t₀ x₀ r L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma next_apply (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) {t : Icc tmin tmax} :
    next hf hx α t = picard f t₀ x α.compProj t := rfl
/-
**ODE.FunSpace.next_apply** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：next_apply (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x
₀ r) (α : FunSpace t₀ x₀ r L) {t : Icc tmin tmax} : next hf hx α t = picard f t₀
 x α.compProj t
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r；α : FunSpace 
t₀ x₀ r L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma next_apply₀ (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) : next hf hx α t₀ = x := by simp

/-- `α` is a fixed point of `next` if and only if it satisfies the integral equation
`α t = x + ∫_{t₀}^t f τ (α τ) dτ` for all `t`. -/
/-
**ODE.FunSpace.isFixedPt_next_iff** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：isFixedPt_next_iff (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in clos
edBall x₀ r) {α : FunSpace t₀ x₀ r L} : IsFixedPt (next hf hx) α ↔ forall t, α t
 = picard f t₀ x α.compProj t
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ODE.FunSpace.ext`：ext {α β : FunSpace t₀ x₀ r L} (h : forall t, α t = β 
t) : α = β
· 使用引理 `ODE.FunSpace.next_apply`：next_apply (hf : IsPicardLindelof f t₀ x₀ a r L
 K) (hx : x in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) {t : Icc tmin tmax} : n
ext hf hx α t…

--- 原说明 ---
`α` is a fixed point of `next` if and only if it satisfies the integral equation
`α t = x + ∫_{t₀}^t f τ (α τ) dτ` for all `t`.
-/
lemma isFixedPt_next_iff (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    {α : FunSpace t₀ x₀ r L} :
    IsFixedPt (next hf hx) α ↔ ∀ t, α t = picard f t₀ x α.compProj t := by
  constructor
  · exact fun hα t ↦ congrArg (· t) hα |>.symm
  · intro h
    ext t
    rw [h, next_apply]

/-- A key step in the inductive case of `dist_iterate_next_apply_le` -/
/-
**ODE.FunSpace.dist_comp_iterate_next_le** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace
`。
形式化陈述：dist_comp_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x 
in closedBall x₀ r) (n : Nat) (t : Icc tmin tmax) {α β : FunSpace t₀ x₀ r L} (h 
: dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) <= (K * |t - t₀.1|) ^ n / n
 ! * dist α β) : dist (f t ((next hf hx)^[n] α t)) (f t ((next hf hx)^[n] β t)) 
<= K ^ (n + 1) * |t - t₀.1| ^ n / n ! * dist α β
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r；n : Nat；t : I
cc tmin tmax；h : dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) <= (K * |t -
 t₀.1|) ^ n / n ! * dist α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoM
etricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {s : Set α}   {f : α →
 β}, LipschitzOnW…
· 使用定理 `IsPicardLindelof.lipschitzOnWith`：∀ {E : Type u_1} [inst : NormedAddComm
Group E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   
{a r L K : NNReal},   …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ODE.FunSpace.mem_closedBall`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E} {a r L : NNReal}   {α :
 ODE.FunSpace t₀ …
· 使用定理 `IsPicardLindelof.mul_max_le`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   {a r 
L K : NNReal}, Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r

--- 原说明 ---
A key step in the inductive case of `dist_iterate_next_apply_le`
-/
lemma dist_comp_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (n : ℕ) (t : Icc tmin tmax)
    {α β : FunSpace t₀ x₀ r L}
    (h : dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) ≤
      (K * |t - t₀.1|) ^ n / n ! * dist α β) :
    dist (f t ((next hf hx)^[n] α t)) (f t ((next hf hx)^[n] β t)) ≤
      K ^ (n + 1) * |t - t₀.1| ^ n / n ! * dist α β :=
  calc
    _ ≤ K * dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) :=
      hf.lipschitzOnWith t.1 t.2 |>.dist_le_mul
        _ (FunSpace.mem_closedBall hf.mul_max_le) _ (FunSpace.mem_closedBall hf.mul_max_le)
    _ ≤ K ^ (n + 1) * |t - t₀.1| ^ n / n ! * dist α β := by
      rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
      gcongr
      rwa [← mul_pow]

/-- A time-dependent bound on the distance between the `n`-th iterates of `next` on two curves -/
/-
**ODE.FunSpace.dist_iterate_next_apply_le** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpac
e`。
形式化陈述：dist_iterate_next_apply_le (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x
 in closedBall x₀ r) (α β : FunSpace t₀ x₀ r L) (n : Nat) (t : Icc tmin tmax) : 
dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) <= (K * |t.1 - t₀.1|) ^ n / n
 ! * dist α β
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r；α β : FunSpac
e t₀ x₀ r L；n : Nat；t : Icc tmin tmax。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ContinuousMap.dist_apply_le_dist`：dist_apply_le_dist (x : α) : dist (f x
) (g x) <= dist f g
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用引理 `ODE.FunSpace.next_apply`：next_apply (hf : IsPicardLindelof f t₀ x₀ a r L
 K) (hx : x in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) {t : Icc tmin tmax} : n
ext hf hx α t…
· 使用引理 `ODE.picard_apply`：picard_apply {x₀ : E} {t : Real} : picard f t₀ x₀ α t 
= x₀ + ∫ τ in t₀..t, f τ (α τ)
· 使用定理 `add_sub_add_left_eq_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c + a - (c + b) = a - b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_sub`：integral_sub (hf : IntervalIntegrable f μ
 a b) (hg : IntervalIntegrable g μ a b) : ∫ x in a..b, f x - g x ∂μ = (∫ x in a.
.b, f x ∂μ) - ∫ x i…
· 使用引理 `ODE.FunSpace.intervalIntegrable_comp_compProj`：intervalIntegrable_comp_c
ompProj (hf : IsPicardLindelof f t₀ x₀ a r L K) (α : FunSpace t₀ x₀ r L) (t : Ic
c tmin tmax) : IntervalIntegrable (…
· 使用定理 `intervalIntegral.norm_intervalIntegral_eq`：norm_intervalIntegral_eq (f :
 Real -> E) (a b : Real) (μ : Measure Real) : ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι 
a b, f x ∂μ‖
· 使用定理 `MeasureTheory.norm_integral_le_of_norm_le`：norm_integral_le_of_norm_le {
f : α -> G} {g : α -> Real} (hg : Integrable g μ) (h : forallᵐ x ∂μ, ‖f x‖ <= g 
x) : ‖∫ x, f x ∂μ‖ <= ∫ x, g x …
· 使用定理 `Continuous.integrableOn_uIoc`：Continuous.integrableOn_uIoc [LinearOrder 
X] [CompactIccSpace X] [T2Space X] (hf : Continuous f) : IntegrableOn f (Ι a b) 
μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
（共 82 条，此处仅展示前 30 条）

--- 原说明 ---
A time-dependent bound on the distance between the `n`-th iterates of `next` on 
two curves
-/
lemma dist_iterate_next_apply_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (α β : FunSpace t₀ x₀ r L) (n : ℕ) (t : Icc tmin tmax) :
    dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) ≤
      (K * |t.1 - t₀.1|) ^ n / n ! * dist α β := by
  induction n generalizing t with
  | zero => simpa using!
      ContinuousMap.dist_apply_le_dist (f := toContinuousMap α) (g := toContinuousMap β) _
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply,
      next_apply, picard_apply, picard_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (intervalIntegrable_comp_compProj hf _ t)
        (intervalIntegrable_comp_compProj hf _ t)]
    calc
      _ ≤ ∫ τ in uIoc t₀.1 t.1, K ^ (n + 1) * |τ - t₀| ^ n / n ! * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro t' ht'
        -- Can `grind` do this in the future?
        have ht' : t' ∈ Icc tmin tmax :=
          subset_trans uIoc_subset_uIcc (uIcc_subset_Icc t₀.2 t.2) ht'
        rw [← dist_eq_norm, compProj_of_mem, compProj_of_mem]
        exact dist_comp_iterate_next_le hf hx _ ⟨t', ht'⟩ (hn _)
      _ ≤ (K * |t.1 - t₀.1|) ^ (n + 1) / (n + 1) ! * dist α β := by
        apply le_of_abs_le
        -- critical: `integral_pow_abs_sub_uIoc`
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

/-- The `n`-th iterate of `next` is Lipschitz continuous with respect to `FunSpace`, with constant
$(K \max(t_{\mathrm{max}}, t_{\mathrm{min}})^n / n!$. -/
/-
**ODE.FunSpace.dist_iterate_next_iterate_next_le** 是 Mathlib 中的一个引理，位于命名空间 `ODE.
FunSpace`。
形式化陈述：dist_iterate_next_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K) 
(hx : x in closedBall x₀ r) (α β : FunSpace t₀ x₀ r L) (n : Nat) : dist ((next h
f hx)^[n] α) ((next hf hx)^[n] β) <= (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n !
 * dist α β
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r；α β : FunSpac
e t₀ x₀ r L；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `MetricSpace.isometry_induced`：MetricSpace.isometry_induced (f : α -> β) 
(hf : f.Injective) [m : MetricSpace β] : letI
· 使用定理 `ContinuousMap.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist f g <= C ↔ 
forall x : α, dist (f x) (g x) <= C
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `ODE.FunSpace.dist_iterate_next_apply_le`：dist_iterate_next_apply_le (hf 
: IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r) (α β : FunSpace 
t₀ x₀ r L) (n : Nat) (t : Icc…
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The `n`-th iterate of `next` is Lipschitz continuous with respect to `FunSpace`,
 with constant
$(K \max(t_{\mathrm{max}}, t_{\mathrm{min}})^n / n!$.
-/
lemma dist_iterate_next_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (α β : FunSpace t₀ x₀ r L) (n : ℕ) :
    dist ((next hf hx)^[n] α) ((next hf hx)^[n] β) ≤
      (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! * dist α β := by
  rw [← MetricSpace.isometry_induced FunSpace.toContinuousMap FunSpace.toContinuousMap.injective
    |>.dist_eq, ContinuousMap.dist_le]
  · intro t
    apply le_trans <| dist_iterate_next_apply_le hf hx α β n t
    gcongr
    exact abs_sub_le_max_sub t.2.1 t.2.2 _
  · have : 0 ≤ max (tmax - t₀) (t₀ - tmin) := le_max_of_le_left <| sub_nonneg_of_le t₀.2.2
    positivity

/-- Some `n`-th iterate of `next` is a contracting map, and its associated Lipschitz constant is
independent of the initial point. -/
/-
**ODE.FunSpace.exists_contractingWith_iterate_next** 是 Mathlib 中的一个引理，位于命名空间 `OD
E.FunSpace`。
形式化陈述：exists_contractingWith_iterate_next (hf : IsPicardLindelof f t₀ x₀ a r L K
) : exists (n : Nat) (C : Real>=0), forall (x : E) (hx : x in closedBall x₀ r), 
ContractingWith C (next hf hx)^[n]
参数：hf : IsPicardLindelof f t₀ x₀ a r L K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `FloorSemiring.tendsto_pow_div_factorial_atTop`：tendsto_pow_div_factorial
_atTop (c : K) : Tendsto (fun n => c ^ n / n !) atTop (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `LipschitzWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   (∀ (x 
y : α), dist (f x)…
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Some `n`-th iterate of `next` is a contracting map, and its associated Lipschitz
 constant is
independent of the initial point.
-/
lemma exists_contractingWith_iterate_next (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ (n : ℕ) (C : ℝ≥0), ∀ (x : E) (hx : x ∈ closedBall x₀ r),
      ContractingWith C (next hf hx)^[n] := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (tmax - t₀) (t₀ - tmin))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have : (0 : ℝ) ≤ (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! := by
    have : 0 ≤ max (tmax - t₀) (t₀ - tmin) := le_max_of_le_left <| sub_nonneg_of_le t₀.2.2
    positivity
  refine ⟨n, ⟨_, this⟩, fun x hx ↦ ?_⟩
  exact ⟨hn, LipschitzWith.of_dist_le_mul fun α β ↦ dist_iterate_next_iterate_next_le hf hx α β n⟩

/-- The map `next` has a fixed point in the space of curves. This will be used to construct a
solution `α : ℝ → E` to the ODE. -/
/-
**ODE.FunSpace.exists_isFixedPt_next** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：exists_isFixedPt_next [CompleteSpace E] (hf : IsPicardLindelof f t₀ x₀ a r
 L K) (hx : x in closedBall x₀ r) : exists α : FunSpace t₀ x₀ r L, IsFixedPt (ne
xt hf hx) α
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ODE.FunSpace.exists_contractingWith_iterate_next`：exists_contractingWith
_iterate_next (hf : IsPicardLindelof f t₀ x₀ a r L K) : exists (n : Nat) (C : Re
al>=0), forall (x : E) (hx : x in clos…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ODE.FunSpace.instCompleteSpace`：∀ {E : Type u_1} [inst : NormedAddCommGr
oup E] {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E} {r L : NNReal}   [Co
mpleteSpace E], Comp…
· 使用定理 `ContractingWith.isFixedPt_fixedPoint_iterate`：isFixedPt_fixedPoint_itera
te {n : Nat} (hf : ContractingWith K f^[n]) : IsFixedPt f (hf.fixedPoint f^[n])

--- 原说明 ---
The map `next` has a fixed point in the space of curves. This will be used to co
nstruct a
solution `α : ℝ → E` to the ODE.
-/
lemma exists_isFixedPt_next [CompleteSpace E] (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) :
    ∃ α : FunSpace t₀ x₀ r L, IsFixedPt (next hf hx) α :=
  let ⟨_, _, h⟩ := exists_contractingWith_iterate_next hf
  ⟨_, h x hx |>.isFixedPt_fixedPoint_iterate⟩

/-! ## Lipschitz continuity of the solution with respect to the initial condition

The proof relies on the fact that the repeated application of `next` to any curve `α` converges to
the fixed point of `next`, so it suffices to bound the distance between `α` and `next^[n] α`. Since
there is some `m : ℕ` such that `next^[m]` is a contracting map, it further suffices to bound the
distance between `α` and `next^[m]^[n] α`.
-/

/-- A key step in the base case of `exists_forall_closedBall_funSpace_dist_le_mul` -/
/-
**ODE.FunSpace.dist_next_next** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：dist_next_next (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBa
ll x₀ r) (hy : y in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) : dist (next hf hx
 α) (next hf hy α) = dist x y
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r；hy : y in clo
sedBall x₀ r；α : FunSpace t₀ x₀ r L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `MetricSpace.isometry_induced`：MetricSpace.isometry_induced (f : α -> β) 
(hf : f.Injective) [m : MetricSpace β] : letI
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `ContinuousMap.norm_eq_iSup_norm`：norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x
‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A key step in the base case of `exists_forall_closedBall_funSpace_dist_le_mul`
-/
lemma dist_next_next (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (hy : y ∈ closedBall x₀ r) (α : FunSpace t₀ x₀ r L) :
    dist (next hf hx α) (next hf hy α) = dist x y := by
  have : Nonempty (Icc tmin tmax) := ⟨t₀⟩ -- needed for `ciSup_const`
  rw [← MetricSpace.isometry_induced FunSpace.toContinuousMap FunSpace.toContinuousMap.injective
    |>.dist_eq, dist_eq_norm, ContinuousMap.norm_eq_iSup_norm]
  simp [add_sub_add_right_eq_sub, dist_eq_norm]
/-
**ODE.FunSpace.dist_iterate_next_le** 是 Mathlib 中的一个引理，位于命名空间 `ODE.FunSpace`。
形式化陈述：dist_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in cl
osedBall x₀ r) (α : FunSpace t₀ x₀ r L) (n : Nat) : dist α ((next hf hx)^[n] α) 
<= (∑ i in Finset.range n, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !) * dist α
 (next hf hx α)
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r；α : FunSpace 
t₀ x₀ r L；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_zero_apply`：iterate_zero_apply (x : α) : f^[0] x = x
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `dist_le_range_sum_of_dist_le`：dist_le_range_sum_of_dist_le {f : Nat -> α
} (n : Nat) {d : Nat -> Real} (hd : forall {k}, k < n -> dist (f k) (f (k + 1)) 
<= d k) : dist (f …
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)
· 使用引理 `ODE.FunSpace.dist_iterate_next_iterate_next_le`：dist_iterate_next_iterat
e_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r) (α
 β : FunSpace t₀ x₀ r L) (n : Nat) :…
-/
lemma dist_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) (n : ℕ) :
    dist α ((next hf hx)^[n] α) ≤
      (∑ i ∈ Finset.range n, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !)
        * dist α (next hf hx α) := by
  nth_rw 1 [← iterate_zero_apply (next hf hx) α]
  rw [Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i ↦ (next hf hx)^[i] α)
  intro i hi
  rw [iterate_succ_apply]
  exact dist_iterate_next_iterate_next_le hf hx _ _ i
/-
**ODE.FunSpace.dist_iterate_iterate_next_le_of_lipschitzWith** 是 Mathlib 中的一个引理，
位于命名空间 `ODE.FunSpace`。
形式化陈述：dist_iterate_iterate_next_le_of_lipschitzWith (hf : IsPicardLindelof f t₀ 
x₀ a r L K) (hx : x in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) {m : Nat} {C : 
Real>=0} (hm : LipschitzWith C (next hf hx)^[m]) (n : Nat) : dist α ((next hf hx
)^[m]^[n] α) <= (∑ i in Finset.range m, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / 
i !) * (∑ i in Finset.range n, (C : Real) ^ i) * dist α (next hf hx α)
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r；α : FunSpace 
t₀ x₀ r L；hm : LipschitzWith C (next hf hx)^[m]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_zero_apply`：iterate_zero_apply (x : α) : f^[0] x = x
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `dist_le_range_sum_of_dist_le`：dist_le_range_sum_of_dist_le {f : Nat -> α
} (n : Nat) {d : Nat -> Real} (hd : forall {k}, k < n -> dist (f k) (f (k + 1)) 
<= d k) : dist (f …
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LipschitzWith.dist_iterate_succ_le_geometric`：dist_iterate_succ_le_geome
tric {f : α -> α} (hf : LipschitzWith K f) (x n) : dist (f^[n] x) (f^[n + 1] x) 
<= dist x (f x) * (K : Real) ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `ODE.FunSpace.dist_iterate_next_le`：dist_iterate_next_le (hf : IsPicardLi
ndelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) (n 
: Nat) : dist α ((next …
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
lemma dist_iterate_iterate_next_le_of_lipschitzWith (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (α : FunSpace t₀ x₀ r L) {m : ℕ} {C : ℝ≥0}
    (hm : LipschitzWith C (next hf hx)^[m]) (n : ℕ) :
    dist α ((next hf hx)^[m]^[n] α) ≤
      (∑ i ∈ Finset.range m, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !) *
        (∑ i ∈ Finset.range n, (C : ℝ) ^ i) * dist α (next hf hx α) := by
  nth_rw 1 [← iterate_zero_apply (next hf hx) α]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i ↦ (next hf hx)^[m]^[i] α)
  intro i hi
  rw [iterate_succ_apply]
  apply le_trans <| hm.dist_iterate_succ_le_geometric α i
  rw [mul_assoc, mul_comm ((C : ℝ) ^ i), ← mul_assoc]
  gcongr
  exact dist_iterate_next_le hf hx α m

/-- The pointwise distance between any two integral curves `α` and `β` over their domains is bounded
by a constant `L'` times the distance between their respective initial points. This is the result of
taking the limit of `dist_iterate_iterate_next_le_of_lipschitzWith` as `n → ∞`. This implies that
the local solution of a vector field is Lipschitz continuous in the initial condition. -/
/-
**ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul** 是 Mathlib 中的一个引理，
位于命名空间 `ODE.FunSpace`。
形式化陈述：exists_forall_closedBall_funSpace_dist_le_mul [CompleteSpace E] (hf : IsPi
cardLindelof f t₀ x₀ a r L K) : exists L' : Real>=0, forall (x y : E) (hx : x in
 closedBall x₀ r) (hy : y in closedBall x₀ r) (α β : FunSpace t₀ x₀ r L) (_ : Is
FixedPt (next hf hx) α) (_ : IsFixedPt (next hf hy) β), dist α β <= L' * dist x 
y
参数：hf : IsPicardLindelof f t₀ x₀ a r L K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ODE.FunSpace.exists_contractingWith_iterate_next`：exists_contractingWith
_iterate_next (hf : IsPicardLindelof f t₀ x₀ a r L K) : exists (n : Nat) (C : Re
al>=0), forall (x : E) (hx : x in clos…
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_mk`：∀ (a : ℝ) (ha : 0 ≤ a), ↑(NNReal.mk a ha) = a
· 使用定理 `le_of_tendsto_of_tendsto'`：le_of_tendsto_of_tendsto' {f g : β -> α} {b :
 Filter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g 
b (𝓝 a₂)) (h : …
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
The pointwise distance between any two integral curves `α` and `β` over their do
mains is bounded
by a constant `L'` times the distance between their respective initial points. T
his is the result of
taking the limit of `dist_iterate_iterate_next_le_of_lipschitzWith` as `n → ∞`. 
This implies that
the local solution of a vector field is Lipschitz continuous in the initial cond
ition.
-/
lemma exists_forall_closedBall_funSpace_dist_le_mul [CompleteSpace E]
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ L' : ℝ≥0, ∀ (x y : E) (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r)
      (α β : FunSpace t₀ x₀ r L) (_ : IsFixedPt (next hf hx) α) (_ : IsFixedPt (next hf hy) β),
      dist α β ≤ L' * dist x y := by
  obtain ⟨m, C, h⟩ := exists_contractingWith_iterate_next hf
  let L' := (∑ i ∈ Finset.range m, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !) * (1 - C)⁻¹
  have hL' : 0 ≤ L' := by
    have : 0 ≤ max (tmax - t₀) (t₀ - tmin) := le_max_of_le_left <| sub_nonneg_of_le t₀.2.2
    positivity
  refine ⟨.mk L' hL', fun x y hx hy α β hα hβ ↦ ?_⟩
  rw [NNReal.coe_mk]
  apply le_of_tendsto_of_tendsto' (b := Filter.atTop) _ _ <|
    dist_iterate_iterate_next_le_of_lipschitzWith hf hy α (h y hy).2
  · apply Filter.Tendsto.comp (y := 𝓝 β) (tendsto_const_nhds.dist Filter.tendsto_id)
    rw [h y hy |>.fixedPoint_unique (hβ.iterate m)]
    exact h y hy |>.tendsto_iterate_fixedPoint α
  · nth_rw 1 [← hα, dist_next_next]
    apply Filter.Tendsto.mul_const
    apply Filter.Tendsto.const_mul
    convert! hasSum_geometric_of_lt_one C.2 (h y hy).1 |>.tendsto_sum_nat
    simp [NNReal.coe_sub <| le_of_lt (h y hy).1, NNReal.coe_one]

end

end FunSpace

/-! ## Properties of the integral equation -/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E} {t₀ tmin tmax : ℝ}

-- TODO: generalise to open sets and `Ici` and `Iic`
/-- If the time-dependent vector field `f` and the curve `α` are continuous, then `f t (α t)` is the
derivative of `picard f t₀ x₀ α`. -/
/-
**ODE.hasDerivWithinAt_picard_Icc** 是 Mathlib 中的一个引理，位于命名空间 `ODE`。
形式化陈述：hasDerivWithinAt_picard_Icc (ht₀ : t₀ in Icc tmin tmax) (hf : ContinuousOn
 (uncurry f) ((Icc tmin tmax) ×ˢ u)) (hα : ContinuousOn α (Icc tmin tmax)) (hmem
 : forall t in Icc tmin tmax, α t in u) (x₀ : E) {t : Real} (ht : t in Icc tmin 
tmax) : HasDerivWithinAt (picard f t₀ x₀ α) (f t (α t)) (Icc tmin tmax) t
参数：ht₀ : t₀ in Icc tmin tmax；hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u
)；hα : ContinuousOn α (Icc tmin tmax)；hmem : forall t in Icc tmin tmax, α t in u
；x₀ : E；ht : t in Icc tmin tmax。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.const_add`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] 
{f : 𝕜 → F} {f' …
· 使用定理 `intervalIntegral.integral_hasDerivWithinAt_right`：integral_hasDerivWithi
nAt_right (hf : IntervalIntegrable f volume a b) {s t : Set Real} [FTCFilter b (
𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMea…
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `ODE.continuousOn_comp`：continuousOn_comp (hf : ContinuousOn (uncurry f) 
(s ×ˢ u)) (hα : ContinuousOn α s) (hmem : MapsTo α s u) : ContinuousOn (fun t =>
 f t (α t))…
· 使用引理 `Set.uIcc_subset_Icc`：uIcc_subset_Icc (ha : a₁ in Icc a₂ b₂) (hb : b₁ in 
Icc a₂ b₂) : [[a₁, b₁]] subseteq Icc a₂ b₂
· 使用定理 `ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin`：ContinuousOn.strongl
yMeasurableAtFilter_nhdsWithin {α β : Type*} [MeasurableSpace α] [TopologicalSpa
ce α] [OpensMeasurableSpace α] [Topologi…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ

--- 原说明 ---
If the time-dependent vector field `f` and the curve `α` are continuous, then `f
 t (α t)` is the
derivative of `picard f t₀ x₀ α`.
-/
lemma hasDerivWithinAt_picard_Icc
    (ht₀ : t₀ ∈ Icc tmin tmax)
    (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (picard f t₀ x₀ α) (f t (α t)) (Icc tmin tmax) t := by
  apply HasDerivWithinAt.const_add
  have : Fact (t ∈ Icc tmin tmax) := ⟨ht⟩ -- needed to synthesise `FTCFilter` for `Icc`
  apply intervalIntegral.integral_hasDerivWithinAt_right _ -- need `CompleteSpace E` and `Icc`
    (continuousOn_comp hf hα hmem |>.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
    (continuousOn_comp hf hα hmem _ ht)
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_comp hf hα hmem |>.mono
  exact uIcc_subset_Icc ht₀ ht

/-- Converse of `hasDerivWithinAt_picard_Icc`: if `f` is the derivative along `α`, then `α`
satisfies the integral equation. -/
/-
**ODE.picard_eq_of_hasDerivAt** 是 Mathlib 中的一个引理，位于命名空间 `ODE`。
形式化陈述：picard_eq_of_hasDerivAt {t : Real} (hf : ContinuousOn (uncurry f) ((uIcc t
₀ t) ×ˢ u)) (hα : forall t' in uIcc t₀ t, HasDerivWithinAt α (f t' (α t')) (uIcc
 t₀ t) t') (hmap : MapsTo α (uIcc t₀ t) u) : picard f t₀ (α t₀) α t = α t
参数：hf : ContinuousOn (uncurry f) ((uIcc t₀ t) ×ˢ u)；hα : forall t' in uIcc t₀ t,
 HasDerivWithinAt α (f t' (α t')) (uIcc t₀ t) t'；hmap : MapsTo α (uIcc t₀ t) u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用引理 `ODE.picard_apply`：picard_apply {x₀ : E} {t : Real} : picard f t₀ x₀ α t 
= x₀ + ∫ τ in t₀..t, f τ (α τ)
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDeriv_right`：integral_eq_sub_of_h
asDeriv_right (hcont : ContinuousOn f (uIcc a b)) (hderiv : forall x in Ioo (min
 a b) (max a b), HasDerivWithinAt f (f' …
· 使用定理 `HasDerivWithinAt.continuousOn`：HasDerivWithinAt.continuousOn {f f' : 𝕜 -
> F} (h : forall x in s, HasDerivWithinAt f (f' x) s x) : ContinuousOn f s
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用引理 `ODE.continuousOn_comp`：continuousOn_comp (hf : ContinuousOn (uncurry f) 
(s ×ˢ u)) (hα : ContinuousOn α s) (hmem : MapsTo α s u) : ContinuousOn (fun t =>
 f t (α t))…

--- 原说明 ---
Converse of `hasDerivWithinAt_picard_Icc`: if `f` is the derivative along `α`, t
hen `α`
satisfies the integral equation.
-/
lemma picard_eq_of_hasDerivAt {t : ℝ}
    (hf : ContinuousOn (uncurry f) ((uIcc t₀ t) ×ˢ u))
    (hα : ∀ t' ∈ uIcc t₀ t, HasDerivWithinAt α (f t' (α t')) (uIcc t₀ t) t')
    (hmap : MapsTo α (uIcc t₀ t) u) :
    picard f t₀ (α t₀) α t = α t := by
  rw [← add_sub_cancel (α t₀) (α t), picard_apply,
    integral_eq_sub_of_hasDeriv_right (HasDerivWithinAt.continuousOn hα) _
      (continuousOn_comp hf (HasDerivWithinAt.continuousOn hα) hmap |>.intervalIntegrable)]
  intro t' ht'
  apply HasDerivAt.hasDerivWithinAt
  exact hα t' (Ioo_subset_Icc_self ht') |>.hasDerivAt <| Icc_mem_nhds ht'.1 ht'.2

/-- If the time-dependent vector field `f` is $C^n$ and the curve `α` is continuous, then
`picard f t₀ x₀ α` is also $C^n$. This version works for `n : ℕ`. -/
/-
**ODE.contDiffOn_nat_picard_Icc** 是 Mathlib 中的一个引理，位于命名空间 `ODE`。
形式化陈述：contDiffOn_nat_picard_Icc (ht₀ : t₀ in Icc tmin tmax) {n : Nat} (hf : Cont
DiffOn Real n (uncurry f) ((Icc tmin tmax) ×ˢ u)) (hα : ContinuousOn α (Icc tmin
 tmax)) (hmem : forall t in Icc tmin tmax, α t in u) (x₀ : E) (heqon : forall t 
in Icc tmin tmax, α t = picard f t₀ x₀ α t) : ContDiffOn Real n (picard f t₀ x₀ 
α) (Icc tmin tmax)
参数：ht₀ : t₀ in Icc tmin tmax；hf : ContDiffOn Real n (uncurry f) ((Icc tmin tmax)
 ×ˢ u)；hα : ContinuousOn α (Icc tmin tmax)；hmem : forall t in Icc tmin tmax, α t
 in u；x₀ : E；heqon : forall t in Icc tmin tmax, α t = picard f t₀ x₀ α t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `ODE.hasDerivWithinAt_picard_Icc`：hasDerivWithinAt_picard_Icc (ht₀ : t₀ i
n Icc tmin tmax) (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u)) (hα : Co
ntinuousOn α (Icc tmi…
· 使用定理 `ContDiffOn.continuousOn`：ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s
) : ContinuousOn f s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `HasDerivWithinAt.continuousOn`：HasDerivWithinAt.continuousOn {f f' : 𝕜 -
> F} (h : forall x in s, HasDerivWithinAt f (f' x) s x) : ContinuousOn f s
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `contDiffOn_succ_iff_derivWithin`：contDiffOn_succ_iff_derivWithin (hs : U
niqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω ->
 AnalyticOn 𝕜 f s) ∧ …
· 使用定理 `uniqueDiffOn_Icc`：uniqueDiffOn_Icc {a b : Real} (hab : a < b) : UniqueDi
ffOn Real (Icc a b)
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `ContDiffOn.congr`：ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : forall
 x in s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s
· 使用引理 `ODE.contDiffOn_comp`：contDiffOn_comp {n : WithTop Nat∞} (hf : ContDiffOn
 Real n (uncurry f) (s ×ˢ u)) (hα : ContDiffOn Real n α s) (hmem : forall t in s
, α t in …
· 使用定理 `ContDiffOn.of_succ`：ContDiffOn.of_succ (h : ContDiffOn 𝕜 (n + 1) f s) : 
ContDiffOn 𝕜 n f s
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `UniqueDiffOn.uniqueDiffWithinAt`：UniqueDiffOn.uniqueDiffWithinAt {s : Se
t E} {x} (hs : UniqueDiffOn R s) (h : x in s) : UniqueDiffWithinAt R s x
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
· 使用引理 `Set.subsingleton_Icc_of_ge`：subsingleton_Icc_of_ge (hba : b <= a) : Set.
Subsingleton (Icc a b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y
· 使用定理 `contDiffWithinAt_singleton`：contDiffWithinAt_singleton : ContDiffWithinA
t 𝕜 n f {x} x

--- 原说明 ---
If the time-dependent vector field `f` is $C^n$ and the curve `α` is continuous,
 then
`picard f t₀ x₀ α` is also $C^n$. This version works for `n : ℕ`.
-/
lemma contDiffOn_nat_picard_Icc
    (ht₀ : t₀ ∈ Icc tmin tmax) {n : ℕ}
    (hf : ContDiffOn ℝ n (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Icc tmin tmax, α t = picard f t₀ x₀ α t) :
    ContDiffOn ℝ n (picard f t₀ x₀ α) (Icc tmin tmax) := by
  by_cases hlt : tmin < tmax
  · have (t) (ht : t ∈ Icc tmin tmax) :=
      hasDerivWithinAt_picard_Icc ht₀ hf.continuousOn hα hmem x₀ ht
    induction n with
    | zero =>
      simp only [Nat.cast_zero, contDiffOn_zero] at *
      exact HasDerivWithinAt.continuousOn this
    | succ n hn =>
      simp only [Nat.cast_add, Nat.cast_one] at *
      rw [contDiffOn_succ_iff_derivWithin <| uniqueDiffOn_Icc hlt]
      refine ⟨fun t ht ↦ HasDerivWithinAt.differentiableWithinAt (this t ht), by simp, ?_⟩
      apply contDiffOn_comp hf.of_succ (ContDiffOn.congr (hn hf.of_succ) heqon) hmem |>.congr
      intro t ht
      exact HasDerivWithinAt.derivWithin (this t ht) <| (uniqueDiffOn_Icc hlt).uniqueDiffWithinAt ht
  · rw [(subsingleton_Icc_of_ge (not_lt.mp hlt)).eq_singleton_of_mem ht₀]
    intro t ht
    rw [eq_of_mem_singleton ht]
    exact contDiffWithinAt_singleton

/-- If the time-dependent vector field `f` is $C^n$ and the curve `α` is continuous, then
`picard f t₀ x₀ α` is also $C^n$. This version works for `n : ℕ∞`.

TODO: Extend to the analytic `n = ⊤` case. -/
/-
**ODE.contDiffOn_enat_picard_Icc** 是 Mathlib 中的一个引理，位于命名空间 `ODE`。
形式化陈述：contDiffOn_enat_picard_Icc (ht₀ : t₀ in Icc tmin tmax) {n : Nat∞} (hf : Co
ntDiffOn Real n (uncurry f) ((Icc tmin tmax) ×ˢ u)) (hα : ContinuousOn α (Icc tm
in tmax)) (hmem : forall t in Icc tmin tmax, α t in u) (x₀ : E) (heqon : forall 
t in Icc tmin tmax, α t = picard f t₀ x₀ α t) : ContDiffOn Real n (picard f t₀ x
₀ α) (Icc tmin tmax)
参数：ht₀ : t₀ in Icc tmin tmax；hf : ContDiffOn Real n (uncurry f) ((Icc tmin tmax)
 ×ˢ u)；hα : ContinuousOn α (Icc tmin tmax)；hmem : forall t in Icc tmin tmax, α t
 in u；x₀ : E；heqon : forall t in Icc tmin tmax, α t = picard f t₀ x₀ α t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffOn_infty`：contDiffOn_infty : ContDiffOn 𝕜 ∞ f s ↔ forall n : Nat
, ContDiffOn 𝕜 n f s
· 使用引理 `ODE.contDiffOn_nat_picard_Icc`：contDiffOn_nat_picard_Icc (ht₀ : t₀ in Ic
c tmin tmax) {n : Nat} (hf : ContDiffOn Real n (uncurry f) ((Icc tmin tmax) ×ˢ u
)) (hα : Continuous…

--- 原说明 ---
If the time-dependent vector field `f` is $C^n$ and the curve `α` is continuous,
 then
`picard f t₀ x₀ α` is also $C^n$. This version works for `n : ℕ∞`.

TODO: Extend to the analytic `n = ⊤` case.
-/
lemma contDiffOn_enat_picard_Icc
    (ht₀ : t₀ ∈ Icc tmin tmax) {n : ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Icc tmin tmax, α t = picard f t₀ x₀ α t) :
    ContDiffOn ℝ n (picard f t₀ x₀ α) (Icc tmin tmax) := by
  induction n with
  | top =>
    rw [contDiffOn_infty] at *
    exact fun k ↦ contDiffOn_nat_picard_Icc ht₀ (hf k) hα hmem x₀ heqon
  | coe n => exact contDiffOn_nat_picard_Icc ht₀ hf hα hmem x₀ heqon

/-- Solutions to ODEs defined by $C^n$ vector fields are also $C^n$. -/
/-
**ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ODE`。
形式化陈述：contDiffOn_enat_Icc_of_hasDerivWithinAt {n : Nat∞} (hf : ContDiffOn Real n
 (uncurry f) ((Icc tmin tmax) ×ˢ u)) (hα : forall t in Icc tmin tmax, HasDerivWi
thinAt α (f t (α t)) (Icc tmin tmax) t) (hmem : MapsTo α (Icc tmin tmax) u) : Co
ntDiffOn Real n α (Icc tmin tmax)
参数：hf : ContDiffOn Real n (uncurry f) ((Icc tmin tmax) ×ˢ u)；hα : forall t in Ic
c tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t；hmem : MapsTo α (I
cc tmin tmax) u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
（共 100 条，此处仅展示前 30 条）

--- 原说明 ---
Solutions to ODEs defined by $C^n$ vector fields are also $C^n$.
-/
theorem contDiffOn_enat_Icc_of_hasDerivWithinAt {n : ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t)
    (hmem : MapsTo α (Icc tmin tmax) u) :
    ContDiffOn ℝ n α (Icc tmin tmax) := by
  by_cases hlt : tmin < tmax
  · set t₀ := (tmin + tmax) / 2 with h
    have ht₀ : t₀ ∈ Icc tmin tmax := ⟨by linarith, by linarith⟩
    have : ∀ t ∈ Icc tmin tmax, α t = picard f t₀ (α t₀) α t := by
      intro t ht
      have : uIcc t₀ t ⊆ Icc tmin tmax := uIcc_subset_Icc ht₀ ht
      rw [picard_eq_of_hasDerivAt (hf.continuousOn.mono (prod_subset_prod_left this))
        (fun t' ht' ↦ hα t' (this ht') |>.mono this) (hmem.mono_left this)]
    exact contDiffOn_enat_picard_Icc ht₀ hf (HasDerivWithinAt.continuousOn hα) hmem (α t₀) this
      |>.congr this
  · rw [not_lt, le_iff_lt_or_eq] at hlt
    cases hlt with
    | inl h =>
      intro _ ht
      rw [Icc_eq_empty (not_le.mpr h)] at ht
      exfalso
      exact notMem_empty _ ht
    | inr h =>
      rw [h, Icc_self]
      intro _ ht
      rw [eq_of_mem_singleton ht]
      exact contDiffWithinAt_singleton

end

end ODE

namespace IsPicardLindelof

/-! ## Properties of `IsPicardLindelof` -/

section

variable {E : Type*} [NormedAddCommGroup E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

/-
**IsPicardLindelof.continuousOn_uncurry** 是 Mathlib 中的一个引理，位于命名空间 `IsPicardLinde
lof`。
形式化陈述：continuousOn_uncurry (hf : IsPicardLindelof f t₀ x₀ a r L K) : ContinuousO
n (uncurry f) ((Icc tmin tmax) ×ˢ (closedBall x₀ a))
参数：hf : IsPicardLindelof f t₀ x₀ a r L K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_prod_of_continuousOn_lipschitzOnWith'`：continuousOn_prod_of
_continuousOn_lipschitzOnWith' [TopologicalSpace α] [PseudoEMetricSpace β] [Pseu
doEMetricSpace γ] (f : α × β -> γ) {s : …
· 使用定理 `IsPicardLindelof.lipschitzOnWith`：∀ {E : Type u_1} [inst : NormedAddComm
Group E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   
{a r L K : NNReal},   …
· 使用定理 `IsPicardLindelof.continuousOn`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   {a 
r L K : NNReal},   …
-/
lemma continuousOn_uncurry (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ (closedBall x₀ a)) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith' _ K hf.lipschitzOnWith hf.continuousOn

/-- Shrink the Picard-Lindelöf parameters to a smaller ball and time interval. The new radius `a'`
and initial deviation `r'` can be chosen freely as long as `a' ≤ a` and the time constraint
`L * max (tmax' - t₀') (t₀' - tmin') ≤ a' - r'` is satisfied. -/
/-
**IsPicardLindelof.shrink** 是 Mathlib 中的一个引理，位于命名空间 `IsPicardLindelof`。
形式化陈述：shrink {f : Real -> E -> E} {tmin tmax tmin' tmax' : Real} {t₀ : Icc tmin 
tmax} {x₀ : E} {a r L K : Real>=0} (hf : IsPicardLindelof f t₀ x₀ a r L K) (t₀' 
: Icc tmin' tmax') (htmin : tmin <= tmin') (htmax : tmax' <= tmax) {a' r' : Real
>=0} (ha : a' <= a) (htime : L * max (tmax' - t₀') (t₀' - tmin') <= a' - r') : I
sPicardLindelof f t₀' x₀ a' r' L K where lipschitzOnWith t ht
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；t₀' : Icc tmin' tmax'；htmin : tmin <= t
min'；htmax : tmax' <= tmax；ha : a' <= a；htime : L * max (tmax' - t₀') (t₀' - tmi
n') <= a' - r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.mono`：LipschitzOnWith.mono (hf : LipschitzOnWith K f t) 
(h : s subseteq t) : LipschitzOnWith K f s
· 使用定理 `IsPicardLindelof.lipschitzOnWith`：∀ {E : Type u_1} [inst : NormedAddComm
Group E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   
{a r L K : NNReal},   …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Metric.closedBall_subset_closedBall`：closedBall_subset_closedBall (h : ε
₁ <= ε₂) : closedBall x ε₁ subseteq closedBall x ε₂
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `IsPicardLindelof.continuousOn`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   {a 
r L K : NNReal},   …
· 使用定理 `IsPicardLindelof.norm_le`：∀ {E : Type u_1} [inst : NormedAddCommGroup E]
 {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   {a r L K
 : NNReal},   …

--- 原说明 ---
Shrink the Picard-Lindelöf parameters to a smaller ball and time interval. The n
ew radius `a'`
and initial deviation `r'` can be chosen freely as long as `a' ≤ a` and the time
 constraint
`L * max (tmax' - t₀') (t₀' - tmin') ≤ a' - r'` is satisfied.
-/
lemma shrink {f : ℝ → E → E} {tmin tmax tmin' tmax' : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : E} {a r L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (t₀' : Icc tmin' tmax') (htmin : tmin ≤ tmin') (htmax : tmax' ≤ tmax)
    {a' r' : ℝ≥0} (ha : a' ≤ a)
    (htime : L * max (tmax' - t₀') (t₀' - tmin') ≤ a' - r') :
    IsPicardLindelof f t₀' x₀ a' r' L K where
  lipschitzOnWith t ht := (hf.lipschitzOnWith t ⟨htmin.trans ht.1, ht.2.trans htmax⟩).mono
    (closedBall_subset_closedBall ha)
  continuousOn x hx := (hf.continuousOn x (closedBall_subset_closedBall ha hx)).mono
    fun _ ht ↦ ⟨htmin.trans ht.1, ht.2.trans htmax⟩
  norm_le t ht x hx := hf.norm_le t ⟨htmin.trans ht.1, ht.2.trans htmax⟩ x
    (closedBall_subset_closedBall ha hx)
  mul_max_le := htime

/-- `IsPicardLindelof` is preserved when shrinking the time interval. -/
/-
**IsPicardLindelof.shrink_time** 是 Mathlib 中的一个引理，位于命名空间 `IsPicardLindelof`。
形式化陈述：shrink_time {f : Real -> E -> E} {tmin tmax tmin' tmax' : Real} {t₀ : Icc 
tmin tmax} {x₀ : E} {a r L K : Real>=0} (hf : IsPicardLindelof f t₀ x₀ a r L K) 
(t₀' : Icc tmin' tmax') (ht₀ : t₀.1 = t₀'.1) (htmin : tmin <= tmin') (htmax : tm
ax' <= tmax) : IsPicardLindelof f t₀' x₀ a r L K
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；t₀' : Icc tmin' tmax'；ht₀ : t₀.1 = t₀'.
1；htmin : tmin <= tmin'；htmax : tmax' <= tmax。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsPicardLindelof.shrink`：shrink {f : Real -> E -> E} {tmin tmax tmin' tm
ax' : Real} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : Real>=0} (hf : IsPicardLind
elof f t₀ x₀ …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `sub_le_sub`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b c d : α},   a ≤ b → c ≤ d → a - d ≤ b - c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
`IsPicardLindelof` is preserved when shrinking the time interval.
-/
lemma shrink_time {f : ℝ → E → E} {tmin tmax tmin' tmax' : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : E} {a r L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ a r L K) (t₀' : Icc tmin' tmax')
    (ht₀ : t₀.1 = t₀'.1) (htmin : tmin ≤ tmin') (htmax : tmax' ≤ tmax) :
    IsPicardLindelof f t₀' x₀ a r L K := by
  apply hf.shrink t₀' htmin htmax le_rfl
  calc L * max (tmax' - t₀') (t₀' - tmin')
    _ ≤ L * max (tmax - t₀) (t₀ - tmin) := by gcongr <;> linarith
    _ ≤ a - r := hf.mul_max_le

/-- `IsPicardLindelof` is preserved when enlarging the Lipschitz constant `K`. -/
/-
**IsPicardLindelof.weaken_lipschitz** 是 Mathlib 中的一个引理，位于命名空间 `IsPicardLindelof`
。
形式化陈述：weaken_lipschitz (hf : IsPicardLindelof f t₀ x₀ a r L K) {K' : Real>=0} (h
K : K <= K') : IsPicardLindelof f t₀ x₀ a r L K' where lipschitzOnWith t ht
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hK : K <= K'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.weaken`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {s : Set α}   {f : α → β}
, LipschitzO…
· 使用定理 `IsPicardLindelof.lipschitzOnWith`：∀ {E : Type u_1} [inst : NormedAddComm
Group E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   
{a r L K : NNReal},   …
· 使用定理 `IsPicardLindelof.continuousOn`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   {a 
r L K : NNReal},   …
· 使用定理 `IsPicardLindelof.norm_le`：∀ {E : Type u_1} [inst : NormedAddCommGroup E]
 {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   {a r L K
 : NNReal},   …
· 使用定理 `IsPicardLindelof.mul_max_le`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   {a r 
L K : NNReal}, Is…

--- 原说明 ---
`IsPicardLindelof` is preserved when enlarging the Lipschitz constant `K`.
-/
lemma weaken_lipschitz (hf : IsPicardLindelof f t₀ x₀ a r L K) {K' : ℝ≥0} (hK : K ≤ K') :
    IsPicardLindelof f t₀ x₀ a r L K' where
  lipschitzOnWith t ht := (hf.lipschitzOnWith t ht).weaken hK
  continuousOn := hf.continuousOn
  norm_le := hf.norm_le
  mul_max_le := hf.mul_max_le

/-- Given `IsPicardLindelof` on a symmetric interval `[t₀ - ε, t₀ + ε]`, if we shrink the radius
from `a` to `a'` with `a' ≤ a`, and choose any `r' < a'`, then there exists `ε' > 0` such that
`IsPicardLindelof` holds on `[t₀ - ε', t₀ + ε']` with the new parameters. -/
/-
**IsPicardLindelof.exists_shrink_radius** 是 Mathlib 中的一个引理，位于命名空间 `IsPicardLinde
lof`。
形式化陈述：exists_shrink_radius {f : Real -> E -> E} {t₀ ε : Real} (hε : 0 < ε) {x₀ :
 E} {a r L K : Real>=0} (hf : IsPicardLindelof f (tmin
参数：hε : 0 < ε。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `IsPicardLindelof.shrink`：shrink {f : Real -> E -> E} {tmin tmax tmin' tm
ax' : Real} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : Real>=0} (hf : IsPicardLind
elof f t₀ x₀ …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
（共 87 条，此处仅展示前 30 条）

--- 原说明 ---
Given `IsPicardLindelof` on a symmetric interval `[t₀ - ε, t₀ + ε]`, if we shrin
k the radius
from `a` to `a'` with `a' ≤ a`, and choose any `r' < a'`, then there exists `ε' 
> 0` such that
`IsPicardLindelof` holds on `[t₀ - ε', t₀ + ε']` with the new parameters.
-/
lemma exists_shrink_radius {f : ℝ → E → E} {t₀ ε : ℝ} (hε : 0 < ε) {x₀ : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f (tmin := t₀ - ε) (tmax := t₀ + ε)
      ⟨t₀, by simp [le_of_lt hε]⟩ x₀ a r L K)
    {a' r' : ℝ≥0} (ha : a' ≤ a) (hr : r' < a') :
    ∃ (ε' : ℝ) (hε' : 0 < ε'), IsPicardLindelof f (tmin := t₀ - ε') (tmax := t₀ + ε')
      ⟨t₀, by simp [le_of_lt hε']⟩ x₀ a' r' L K := by
  have ha'r' : (0 : ℝ) < a' - r' := by simp only [sub_pos, NNReal.coe_lt_coe, hr]
  let ε' := min ε ((a' - r') / (L + 1))
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  have hε'_le : ε' ≤ ε := min_le_left _ _
  refine ⟨ε', hε'pos, hf.shrink ⟨t₀, by simp [le_of_lt hε'pos]⟩ (by linarith) (by linarith) ha ?_⟩
  simp only [add_sub_cancel_left, sub_sub_cancel, max_self]
  calc (L : ℝ) * ε'
    _ ≤ L * ((a' - r') / (L + 1)) := by gcongr; exact min_le_right _ _
    _ = L / (L + 1) * (a' - r') := by ring
    _ ≤ 1 * (a' - r') := by gcongr; rw [div_le_one (by positivity : (0 : ℝ) < L + 1)]; linarith
    _ = a' - r' := one_mul _

/-- The special case where the vector field is independent of time -/
/-
**IsPicardLindelof.of_time_independent** 是 Mathlib 中的一个引理，位于命名空间 `IsPicardLindel
of`。
形式化陈述：of_time_independent {f : E -> E} {tmin tmax : Real} {t₀ : Icc tmin tmax} {
x₀ : E} {a r L K : Real>=0} (hb : forall x in closedBall x₀ a, ‖f x‖ <= L) (hl :
 LipschitzOnWith K f (closedBall x₀ a)) (hm : L * max (tmax - t₀) (t₀ - tmin) <=
 a - r) : (IsPicardLindelof (fun _ => f) t₀ x₀ a r L K) where lipschitzOnWith
参数：hb : forall x in closedBall x₀ a, ‖f x‖ <= L；hl : LipschitzOnWith K f (closed
Ball x₀ a)；hm : L * max (tmax - t₀) (t₀ - tmin) <= a - r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s

--- 原说明 ---
The special case where the vector field is independent of time
-/
lemma of_time_independent
    {f : E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : ℝ≥0}
    (hb : ∀ x ∈ closedBall x₀ a, ‖f x‖ ≤ L)
    (hl : LipschitzOnWith K f (closedBall x₀ a))
    (hm : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r) :
    (IsPicardLindelof (fun _ ↦ f) t₀ x₀ a r L K) where
  lipschitzOnWith := fun _ _ ↦ hl
  continuousOn := fun _ _ ↦ continuousOn_const
  norm_le := fun _ _ ↦ hb
  mul_max_le := hm

/-- A time-independent, continuously differentiable ODE satisfies the hypotheses of the
Picard-Lindelöf theorem. -/
/-
**IsPicardLindelof.of_contDiffAt_one** 是 Mathlib 中的一个引理，位于命名空间 `IsPicardLindelof
`。
形式化陈述：of_contDiffAt_one [NormedSpace Real E] {f : E -> E} {x₀ : E} (hf : ContDif
fAt Real 1 f x₀) : exists (ε : Real) (hε : 0 < ε) (a r L K : Real>=0) (_ : 0 < r
), forall (t₀ : Real), IsPicardLindelof (fun _ => f) (tmin
参数：hf : ContDiffAt Real 1 f x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.exists_lipschitzOnWith`：ContDiffAt.exists_lipschitzOnWith {f 
: E' -> F'} {x : E'} (hf : ContDiffAt 𝕂 1 f x) : exists K, exists t in 𝓝 x, Lips
chitzOnWith K f t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_le_norm_sub_add`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a 
b : E), ‖a‖ ≤ ‖a - b‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `LipschitzOnWith.norm_sub_le`：∀ {E : Type u_2} {F : Type u_3} [inst : Sem
inormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F] {f : E → F}   {C : NN
Real} {s : Set E}…
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Metric.closedBall_subset_ball`：closedBall_subset_ball (h : ε₁ < ε₂) : cl
osedBall x ε₁ subseteq ball x ε₂
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
A time-independent, continuously differentiable ODE satisfies the hypotheses of 
the
Picard-Lindelöf theorem.
-/
lemma of_contDiffAt_one [NormedSpace ℝ E]
    {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < r), ∀ (t₀ : ℝ), IsPicardLindelof (fun _ ↦ f)
      (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, (by simp [le_of_lt hε])⟩ x₀ a r L K := by
  -- Obtain ball of radius `a` within the domain in which f is `K`-lipschitz
  obtain ⟨K, s, hs, hl⟩ := hf.exists_lipschitzOnWith
  obtain ⟨a, ha : 0 < a, has⟩ := Metric.mem_nhds_iff.mp hs
  set L := K * a + ‖f x₀‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  have hb (x : E) (hx : x ∈ closedBall x₀ (a / 2)) : ‖f x‖ ≤ L := by
    rw [hL]
    calc
      ‖f x‖ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖x - x₀‖ + ‖f x₀‖ := by
        gcongr
        apply hl.norm_sub_le _ (mem_of_mem_nhds hs)
        apply subset_trans _ has hx
        exact closedBall_subset_ball <| half_lt_self ha -- this is where we need `a / 2`
      _ ≤ K * a + ‖f x₀‖ := by
        gcongr
        rw [← mem_closedBall_iff_norm]
        exact closedBall_subset_closedBall (half_le_self (le_of_lt ha)) hx
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  let ε := a / L / 2 / 2
  have hε0 : 0 < ε := by positivity
  refine ⟨ε, hε0,
    .mk (a / 2) (half_pos ha).le, (.mk (a / 2) (half_pos ha).le) / 2,
    .mk L hL0.le, K, half_pos <| half_pos ha, fun t₀ ↦ ?_⟩
  apply of_time_independent hb <|
    hl.mono <| subset_trans (closedBall_subset_ball (half_lt_self ha)) has
  simp [ε, field]
  norm_num

end

/-! ## Existence of solutions to ODEs -/

open ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, integral form. This version shows the existence
of a local solution whose initial point `x` may be different from the centre `x₀` of the closed
ball within which the properties of the vector field hold. -/
/-
**IsPicardLindelof.exists_eq_forall_mem_Icc_eq_picard** 是 Mathlib 中的一个定理，位于命名空间 
`IsPicardLindelof`。
形式化陈述：exists_eq_forall_mem_Icc_eq_picard (hf : IsPicardLindelof f t₀ x₀ a r L K)
 (hx : x in closedBall x₀ r) : exists α : Real -> E, α t₀ = x ∧ forall t in Icc 
tmin tmax, α t = ODE.picard f t₀ x α t
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ODE.FunSpace.exists_isFixedPt_next`：exists_isFixedPt_next [CompleteSpace
 E] (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r) : exists
 α : FunSpace t₀ x₀ r L,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.projIcc_val`：projIcc_val (x : Icc a b) : projIcc a b h x = x
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ODE.FunSpace.compProj_apply`：compProj_apply {α : FunSpace t₀ x₀ r L} {t 
: Real} : α.compProj t = α (projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t)
· 使用引理 `ODE.FunSpace.next_apply`：next_apply (hf : IsPicardLindelof f t₀ x₀ a r L
 K) (hx : x in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) {t : Icc tmin tmax} : n
ext hf hx α t…
· 使用定理 `Set.projIcc_of_mem`：projIcc_of_mem (hx : x in Icc a b) : projIcc a b h x
 = ⟨x, hx⟩

--- 原说明 ---
**Picard-Lindelöf (Cauchy-Lipschitz) theorem**, integral form. This version show
s the existence
of a local solution whose initial point `x` may be different from the centre `x₀
` of the closed
ball within which the properties of the vector field hold.
-/
theorem exists_eq_forall_mem_Icc_eq_picard
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧ ∀ t ∈ Icc tmin tmax, α t = ODE.picard f t₀ x α t := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨(FunSpace.next hf hx α).compProj, by simp, fun t ht ↦ ?_⟩
  rw [FunSpace.compProj_apply, FunSpace.next_apply, hα, projIcc_of_mem _ ht]

end IsPicardLindelof

