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

/--
Definition of `IsPicardLindelof` / `IsPicardLindelof` 的定义

English:
structure IsPicardLindelof
  parameters: {E : Type*} [NormedAddCommGroup E]
  axioms and operations (4):
    - lipschitzOnWith : forall t in Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ a)
    - continuousOn : forall x in closedBall x₀ a, ContinuousOn (f · x) (Icc tmin tmax)
    - norm_le : forall t in Icc tmin tmax, forall x in closedBall x₀ a, ‖f t x‖ <= L
    - mul_max_le : L * max (tmax - t₀) (t₀ - tmin) <= a - r

中文:
结构 IsPicardLindelof
  参数: {E : 类型} [NormedAddCommGroup E]
  公理与运算 (4 个):
    - lipschitzOnWith : 对任意 t in Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ a)
    - continuousOn : 对任意 x in closedBall x₀ a, ContinuousOn (f · x) (Icc tmin tmax)
    - norm_le : 对任意 t in Icc tmin tmax, 对任意 x in closedBall x₀ a, ‖f t x‖ <= L
    - mul_max_le : L * max (tmax - t₀) (t₀ - tmin) <= a - r
-/
structure IsPicardLindelof {E : Type*} [NormedAddCommGroup E]
    (f : Real -> E -> E) {tmin tmax : Real} (t₀ : Icc tmin tmax) (x₀ : E) (a r L K : Real>=0) : Prop where
  /-- The vector field at any time is Lipschitz with constant `K` within a closed ball. -/
  lipschitzOnWith : forall t in Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ a)
  /-- The vector field is continuous in time within a closed ball. -/
  continuousOn : forall x in closedBall x₀ a, ContinuousOn (f · x) (Icc tmin tmax)
  /-- `L` is an upper bound of the norm of the vector field. -/
  norm_le : forall t in Icc tmin tmax, forall x in closedBall x₀ a, ‖f t x‖ <= L
  /-- The time interval of validity -/
  mul_max_le : L * max (tmax - t₀) (t₀ - tmin) <= a - r

namespace ODE

/-! ## Integral equation

For any time-dependent vector field `f : ℝ → E → E`, we define an integral equation that is
equivalent to the initial value problem defined by `f`.
-/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {f : Real -> E -> E} {α : Real -> E} {s : Set Real} {u : Set E} {t₀ tmin tmax : Real}

/--
Definition of `picard` / `picard` 的定义

English:
definition picard
  signature: (f : Real -> E -> E) (t₀ : Real) (x₀ : E) (α : Real -> E)
  body: fun t => x₀ + ∫ τ in t₀..t, f τ (α τ)

@[simp]

中文:
定义 picard
  签名: (f : 实数 -> E -> E) (t₀ : 实数) (x₀ : E) (α : 实数 -> E)
  定义体: fun t => x₀ + ∫ τ in t₀..t, f τ (α τ)

@[simp]
-/
noncomputable def picard (f : Real -> E -> E) (t₀ : Real) (x₀ : E) (α : Real -> E) : Real -> E :=
  fun t => x₀ + ∫ τ in t₀..t, f τ (α τ)

@[simp]
/--
lemma `picard_apply` / 引理 `picard_apply`

English:
lemma picard_apply
  given: {x₀ : E} {t : Real}
  statement: picard f t₀ x₀ α t = x₀ + ∫ τ in t₀..t, f τ (α τ)
  proof: rfl

中文:
引理 picard_apply
  条件: {x₀ : E} {t : 实数}
  结论: picard f t₀ x₀ α t = x₀ + ∫ τ in t₀..t, f τ (α τ)
  证明: rfl
-/
lemma picard_apply {x₀ : E} {t : Real} : picard f t₀ x₀ α t = x₀ + ∫ τ in t₀..t, f τ (α τ) := rfl

/--
lemma `picard_apply₀` / 引理 `picard_apply₀`

English:
lemma picard_apply₀
  given: {x₀ : E}
  statement: picard f t₀ x₀ α t₀ = x₀
  proof: by simp

中文:
引理 picard_apply₀
  条件: {x₀ : E}
  结论: picard f t₀ x₀ α t₀ = x₀
  证明: by simp
-/
lemma picard_apply₀ {x₀ : E} : picard f t₀ x₀ α t₀ = x₀ := by simp

/--
lemma `contDiffOn_comp` / 引理 `contDiffOn_comp`

English:
lemma contDiffOn_comp
  statement: {n : WithTop Nat∞}
  proof: by
  simpa only [← uncurry_apply_pair f] using! hf.comp (by fun_prop) (by tauto)

中文:
引理 contDiffOn_comp
  结论: {n : WithTop 自然数∞}
  证明: by
  simpa only [← uncurry_apply_pair f] using! hf.comp (by fun_prop) (by tauto)

Depends on / 依赖: IsSplitEpi, IsSplitEpi.mk, exists_splitEpi, fun_prop, hf.comp, hf.exists_splitEpi.some.map, uncurry_apply_pair
-/
lemma contDiffOn_comp {n : WithTop Nat∞}
    (hf : ContDiffOn Real n (uncurry f) (s ×ˢ u))
    (hα : ContDiffOn Real n α s) (hmem : forall t in s, α t in u) :
    ContDiffOn Real n (fun t => f t (α t)) s := by
  simpa only [← uncurry_apply_pair f] using! hf.comp (by fun_prop) (by tauto)

/--
lemma `continuousOn_comp` / 引理 `continuousOn_comp`

English:
lemma continuousOn_comp
  proof: contDiffOn_zero.mp (contDiffOn_comp (contDiffOn_zero.mpr hf) (contDiffOn_zero.mpr hα) hmem)

中文:
引理 continuousOn_comp
  证明: contDiffOn_zero.mp (contDiffOn_comp (contDiffOn_zero.mpr hf) (contDiffOn_zero.mpr hα) hmem)

Depends on / 依赖: contDiffOn_comp, contDiffOn_zero, contDiffOn_zero.mp, contDiffOn_zero.mpr
-/
lemma continuousOn_comp
    (hf : ContinuousOn (uncurry f) (s ×ˢ u)) (hα : ContinuousOn α s) (hmem : MapsTo α s u) :
    ContinuousOn (fun t => f t (α t)) s :=
contDiffOn_zero.mp (contDiffOn_comp (contDiffOn_zero.mpr hf) (contDiffOn_zero.mpr hα) hmem)

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

/--
Definition of `FunSpace` / `FunSpace` 的定义

English:
structure FunSpace
  parameters: {E : Type*} [NormedAddCommGroup E]
  axioms and operations (3):
    - toFun : Icc tmin tmax -> E
    - lipschitzWith : LipschitzWith L toFun
    - mem_closedBall₀ : toFun t₀ in closedBall x₀ r

中文:
结构 FunSpace
  参数: {E : 类型} [NormedAddCommGroup E]
  公理与运算 (3 个):
    - toFun : Icc tmin tmax -> E
    - lipschitzWith : LipschitzWith L toFun
    - mem_closedBall₀ : toFun t₀ in closedBall x₀ r
-/
structure FunSpace {E : Type*} [NormedAddCommGroup E]
    {tmin tmax : Real} (t₀ : Icc tmin tmax) (x₀ : E) (r L : Real>=0) where
  /-- The domain is `Icc tmin tmax`. -/
  toFun : Icc tmin tmax -> E
  lipschitzWith : LipschitzWith L toFun
  mem_closedBall₀ : toFun t₀ in closedBall x₀ r

namespace FunSpace

variable {E : Type*} [NormedAddCommGroup E]

section

variable {tmin tmax : Real} {t₀ : Icc tmin tmax} {x₀ : E} {a r L : Real>=0}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (FunSpace t₀ x₀ r L) fun _ => Icc tmin tmax -> E
  body: ⟨fun α => α.toFun⟩

@[ext]

中文:
实例 :
  签名: CoeFun (FunSpace t₀ x₀ r L) fun _ => Icc tmin tmax -> E
  定义体: ⟨fun α => α.toFun⟩

@[ext]
-/
instance : CoeFun (FunSpace t₀ x₀ r L) fun _ => Icc tmin tmax -> E := ⟨fun α => α.toFun⟩

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {α β : FunSpace t₀ x₀ r L} (h : forall t, α t = β t)
  statement: α = β
  proof: by
  cases α; cases β; simp only [mk.injEq]; ext t; exact h t

中文:
引理 ext
  条件: {α β : FunSpace t₀ x₀ r L} (h : 对任意 t, α t = β t)
  结论: α = β
  证明: by
  cases α; cases β; simp only [mk.injEq]; ext t; exact h t

Depends on / 依赖: mk.injEq
-/
lemma ext {α β : FunSpace t₀ x₀ r L} (h : forall t, α t = β t) : α = β := by
  cases α; cases β; simp only [mk.injEq]; ext t; exact h t

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (FunSpace t₀ x₀ r L)
  body: ⟨fun _ => x₀, (LipschitzWith.const _).weaken zero_le, mem_closedBall_self r.2⟩

中文:
实例 :
  签名: Inhabited (FunSpace t₀ x₀ r L)
  定义体: ⟨fun _ => x₀, (LipschitzWith.const _).weaken zero_le, mem_closedBall_self r.2⟩

Depends on / 依赖: LipschitzWith, LipschitzWith.const, mem_closedBall_self, weaken, zero_le
-/
instance : Inhabited (FunSpace t₀ x₀ r L) :=
  ⟨fun _ => x₀, (LipschitzWith.const _).weaken zero_le, mem_closedBall_self r.2⟩

/--
lemma `continuous` / 引理 `continuous`

English:
lemma continuous
  given: (α : FunSpace t₀ x₀ L r)
  statement: Continuous α
  proof: α.lipschitzWith.continuous

中文:
引理 continuous
  条件: (α : FunSpace t₀ x₀ L r)
  结论: Continuous α
  证明: α.lipschitzWith.continuous
-/
protected lemma continuous (α : FunSpace t₀ x₀ L r) : Continuous α := α.lipschitzWith.continuous

/--
Definition of `toContinuousMap` / `toContinuousMap` 的定义

English:
definition toContinuousMap
  signature: : FunSpace t₀ x₀ r L ↪ C(Icc tmin tmax, E)
  body: ⟨fun α => ⟨α, α.continuous⟩, fun α β h => by cases α; cases β; simpa using h⟩

@[simp]

中文:
定义 toContinuousMap
  签名: : FunSpace t₀ x₀ r L ↪ C(Icc tmin tmax, E)
  定义体: ⟨fun α => ⟨α, α.continuous⟩, fun α β h => by cases α; cases β; simpa using h⟩

@[simp]

Depends on / 依赖: continuous
-/
def toContinuousMap : FunSpace t₀ x₀ r L ↪ C(Icc tmin tmax, E) :=
  ⟨fun α => ⟨α, α.continuous⟩, fun α β h => by cases α; cases β; simpa using h⟩

@[simp]
/--
lemma `toContinuousMap_apply_eq_apply` / 引理 `toContinuousMap_apply_eq_apply`

English:
lemma toContinuousMap_apply_eq_apply
  given: (α : FunSpace t₀ x₀ r L) (t : Icc tmin tmax)
  proof: rfl

中文:
引理 toContinuousMap_apply_eq_apply
  条件: (α : FunSpace t₀ x₀ r L) (t : Icc tmin tmax)
  证明: rfl
-/
lemma toContinuousMap_apply_eq_apply (α : FunSpace t₀ x₀ r L) (t : Icc tmin tmax) :
    α.toContinuousMap t = α t := rfl

/--
lemma `apply_of_zero` / 引理 `apply_of_zero`

English:
lemma apply_of_zero
  given: (α : FunSpace t₀ x₀ 0 L)
  statement: α t₀ = x₀
  proof: by
  simpa using α.mem_closedBall₀

中文:
引理 apply_of_zero
  条件: (α : FunSpace t₀ x₀ 0 L)
  结论: α t₀ = x₀
  证明: by
  simpa using α.mem_closedBall₀
-/
lemma apply_of_zero (α : FunSpace t₀ x₀ 0 L) : α t₀ = x₀ := by
  simpa using α.mem_closedBall₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace (FunSpace t₀ x₀ r L)
  body: MetricSpace.induced toContinuousMap toContinuousMap.injective inferInstance

中文:
实例 :
  签名: MetricSpace (FunSpace t₀ x₀ r L)
  定义体: MetricSpace.induced toContinuousMap toContinuousMap.injective inferInstance

Depends on / 依赖: MetricSpace, MetricSpace.induced, induced, injective, toContinuousMap, toContinuousMap.injective
-/
noncomputable instance : MetricSpace (FunSpace t₀ x₀ r L) :=
  MetricSpace.induced toContinuousMap toContinuousMap.injective inferInstance

/--
lemma `isUniformInducing_toContinuousMap` / 引理 `isUniformInducing_toContinuousMap`

English:
lemma isUniformInducing_toContinuousMap
  proof: ⟨rfl⟩

中文:
引理 isUniformInducing_toContinuousMap
  证明: ⟨rfl⟩
-/
lemma isUniformInducing_toContinuousMap :
    IsUniformInducing fun α : FunSpace t₀ x₀ r L => α.toContinuousMap := ⟨rfl⟩

/--
lemma `range_toContinuousMap` / 引理 `range_toContinuousMap`

English:
lemma range_toContinuousMap
  proof: by
  ext α
  constructor
  · rintro ⟨⟨α, hα1, hα2⟩, rfl⟩
    exact ⟨hα1, hα2⟩
  · rintro ⟨hα1, hα2⟩
    exact ⟨⟨α, hα1, hα2⟩, rfl⟩

中文:
引理 range_toContinuousMap
  证明: by
  ext α
  constructor
  · rintro ⟨⟨α, hα1, hα2⟩, rfl⟩
    exact ⟨hα1, hα2⟩
  · rintro ⟨hα1, hα2⟩
    exact ⟨⟨α, hα1, hα2⟩, rfl⟩
-/
lemma range_toContinuousMap :
    range (fun α : FunSpace t₀ x₀ r L => α.toContinuousMap) =
      { α : C(Icc tmin tmax, E) | LipschitzWith L α ∧ α t₀ in closedBall x₀ r } := by
  ext α
  constructor
  · rintro ⟨⟨α, hα1, hα2⟩, rfl⟩
    exact ⟨hα1, hα2⟩
  · rintro ⟨hα1, hα2⟩
    exact ⟨⟨α, hα1, hα2⟩, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteSpace
  signature: E] : CompleteSpace (FunSpace t₀ x₀ r L)
  body: by
  rw [completeSpace_iff_isComplete_range isUniformInducing_toContinuousMap]
  apply IsClosed.isComplete
  rw [range_toContinuousMap]; rw [ofPred_and]
.inter .preimage continuous_coeFun apply isClosed_setOfPred_lipschitzWith L
  simp_rw [mem_closedBall_iff_norm]
  exact isClosed_le (by fun_prop) (

中文:
实例 [CompleteSpace
  签名: E] : CompleteSpace (FunSpace t₀ x₀ r L)
  定义体: by
  rw [completeSpace_iff_isComplete_range isUniformInducing_toContinuousMap]
  apply IsClosed.isComplete
  rw [range_toContinuousMap]; rw [ofPred_and]
.inter .preimage continuous_coeFun apply isClosed_setOfPred_lipschitzWith L
  simp_rw [mem_closedBall_iff_norm]
  exact isClosed_le (by fun_prop) (

Depends on / 依赖: IsClosed, IsClosed.isComplete, completeSpace_iff_isComplete_range, continuous_coeFun, fun_prop, isClosed_le, isClosed_setOfPred_lipschitzWith, isComplete, isUniformInducing_toContinuousMap, mem_closedBall_iff_norm, ofPred_and, preimage, range_toContinuousMap, simp_rw
-/
instance [CompleteSpace E] : CompleteSpace (FunSpace t₀ x₀ r L) := by
  rw [completeSpace_iff_isComplete_range isUniformInducing_toContinuousMap]
  apply IsClosed.isComplete
  rw [range_toContinuousMap]; rw [ofPred_and]
.inter .preimage continuous_coeFun apply isClosed_setOfPred_lipschitzWith L
  simp_rw [mem_closedBall_iff_norm]
  exact isClosed_le (by fun_prop) (by fun_prop)

/--
Definition of `compProj` / `compProj` 的定义

English:
definition compProj
  signature: (α : FunSpace t₀ x₀ r L) (t : Real)
  body: α projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t

@[simp]

中文:
定义 compProj
  签名: (α : FunSpace t₀ x₀ r L) (t : 实数)
  定义体: α projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t

@[simp]

Depends on / 依赖: le_trans, projIcc
-/
noncomputable def compProj (α : FunSpace t₀ x₀ r L) (t : Real) : E :=
α projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t

@[simp]
/--
lemma `compProj_apply` / 引理 `compProj_apply`

English:
lemma compProj_apply
  given: {α : FunSpace t₀ x₀ r L} {t : Real}
  proof: rfl

中文:
引理 compProj_apply
  条件: {α : FunSpace t₀ x₀ r L} {t : 实数}
  证明: rfl
-/
lemma compProj_apply {α : FunSpace t₀ x₀ r L} {t : Real} :
    α.compProj t = α (projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t) := rfl

/--
lemma `compProj_val` / 引理 `compProj_val`

English:
lemma compProj_val
  given: {α : FunSpace t₀ x₀ r L} {t : Icc tmin tmax}
  proof: by simp only [compProj_apply, projIcc_val]

中文:
引理 compProj_val
  条件: {α : FunSpace t₀ x₀ r L} {t : Icc tmin tmax}
  证明: by simp only [compProj_apply, projIcc_val]

Depends on / 依赖: compProj_apply, projIcc_val
-/
lemma compProj_val {α : FunSpace t₀ x₀ r L} {t : Icc tmin tmax} :
    α.compProj t = α t := by simp only [compProj_apply, projIcc_val]

/--
lemma `compProj_of_mem` / 引理 `compProj_of_mem`

English:
lemma compProj_of_mem
  given: {α : FunSpace t₀ x₀ r L} {t : Real} (ht : t in Icc tmin tmax)
  proof: by rw [compProj_apply, projIcc_of_mem]

@[continuity, fun_prop]

中文:
引理 compProj_of_mem
  条件: {α : FunSpace t₀ x₀ r L} {t : 实数} (ht : t in Icc tmin tmax)
  证明: by rw [compProj_apply, projIcc_of_mem]

@[continuity, fun_prop]

Depends on / 依赖: compProj_apply, projIcc_of_mem
-/
lemma compProj_of_mem {α : FunSpace t₀ x₀ r L} {t : Real} (ht : t in Icc tmin tmax) :
    α.compProj t = α ⟨t, ht⟩ := by rw [compProj_apply, projIcc_of_mem]

@[continuity, fun_prop]
/--
lemma `continuous_compProj` / 引理 `continuous_compProj`

English:
lemma continuous_compProj
  given: (α : FunSpace t₀ x₀ r L)
  statement: Continuous α.compProj
  proof: α.continuous.comp continuous_projIcc

中文:
引理 continuous_compProj
  条件: (α : FunSpace t₀ x₀ r L)
  结论: Continuous α.compProj
  证明: α.continuous.comp continuous_projIcc

Depends on / 依赖: continuous, continuous.comp, continuous_projIcc
-/
lemma continuous_compProj (α : FunSpace t₀ x₀ r L) : Continuous α.compProj :=
  α.continuous.comp continuous_projIcc

/--
lemma `mem_closedBall` / 引理 `mem_closedBall`

English:
lemma mem_closedBall
  proof: by
  rw [mem_closedBall]; rw [dist_eq_norm]
  calc
    ‖α t - x₀‖ <= ‖α t - α t₀‖ + ‖α t₀ - x₀‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ <= L * |t.1 - t₀.1| + r := by
apply add_le_add _ mem_closedBall_iff_norm.mp α.mem_closedBall₀
      rw [← dist_eq_norm]
      exact α.lipschitzWith.dist_le_mu

中文:
引理 mem_closedBall
  证明: by
  rw [mem_closedBall]; rw [dist_eq_norm]
  calc
    ‖α t - x₀‖ <= ‖α t - α t₀‖ + ‖α t₀ - x₀‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ <= L * |t.1 - t₀.1| + r := by
apply add_le_add _ mem_closedBall_iff_norm.mp α.mem_closedBall₀
      rw [← dist_eq_norm]
      exact α.lipschitzWith.dist_le_mu
-/
protected lemma mem_closedBall
    {α : FunSpace t₀ x₀ r L} (h : L * max (tmax - t₀) (t₀ - tmin) <= a - r) {t : Icc tmin tmax} :
    α t in closedBall x₀ a := by
  rw [mem_closedBall]; rw [dist_eq_norm]
  calc
    ‖α t - x₀‖ <= ‖α t - α t₀‖ + ‖α t₀ - x₀‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ <= L * |t.1 - t₀.1| + r := by
apply add_le_add _ mem_closedBall_iff_norm.mp α.mem_closedBall₀
      rw [← dist_eq_norm]
      exact α.lipschitzWith.dist_le_mul t t₀
    _ <= L * max (tmax - t₀) (t₀ - tmin) + r := by
      gcongr
      exact abs_sub_le_max_sub t.2.1 t.2.2 _
    _ <= a - r + r := by gcongr
    _ = a := sub_add_cancel _ _

/--
lemma `compProj_mem_closedBall` / 引理 `compProj_mem_closedBall`

English:
lemma compProj_mem_closedBall
  proof: α.mem_closedBall h

中文:
引理 compProj_mem_closedBall
  证明: α.mem_closedBall h

Depends on / 依赖: mem_closedBall
-/
lemma compProj_mem_closedBall
    (α : FunSpace t₀ x₀ r L) (h : L * max (tmax - t₀) (t₀ - tmin) <= a - r) {t : Real} :
    α.compProj t in closedBall x₀ a :=
  α.mem_closedBall h

end

/-! ## Contracting map on the space of Lipschitz functions -/

section

variable [NormedSpace Real E]
  {f : Real -> E -> E} {tmin tmax : Real} {t₀ : Icc tmin tmax} {x₀ x y : E} {a r L K : Real>=0}

/--
lemma `continuousOn_comp_compProj` / 引理 `continuousOn_comp_compProj`

English:
lemma continuousOn_comp_compProj
  given: (hf : IsPicardLindelof f t₀ x₀ a r L K) (α : FunSpace t₀ x₀ r L)
  proof: continuousOn_comp
    (continuousOn_prod_of_continuousOn_lipschitzOnWith' (uncurry f) K hf.lipschitzOnWith
      hf.continuousOn)
    α.continuous_compProj.continuousOn
    fun _ _ => α.mem_closedBall hf.mul_max_le

中文:
引理 continuousOn_comp_compProj
  条件: (hf : IsPicardLindelof f t₀ x₀ a r L K) (α : FunSpace t₀ x₀ r L)
  证明: continuousOn_comp
    (continuousOn_prod_of_continuousOn_lipschitzOnWith' (uncurry f) K hf.lipschitzOnWith
      hf.continuousOn)
    α.continuous_compProj.continuousOn
    fun _ _ => α.mem_closedBall hf.mul_max_le

Depends on / 依赖: continuousOn, continuousOn_comp, continuousOn_prod_of_continuousOn_lipschitzOnWith, continuous_compProj, continuous_compProj.continuousOn, hf.continuousOn, hf.lipschitzOnWith, hf.mul_max_le, lipschitzOnWith, mem_closedBall, mul_max_le, uncurry
-/
lemma continuousOn_comp_compProj (hf : IsPicardLindelof f t₀ x₀ a r L K) (α : FunSpace t₀ x₀ r L) :
    ContinuousOn (fun t' => f t' (α.compProj t')) (Icc tmin tmax) :=
  continuousOn_comp
    (continuousOn_prod_of_continuousOn_lipschitzOnWith' (uncurry f) K hf.lipschitzOnWith
      hf.continuousOn)
    α.continuous_compProj.continuousOn
    fun _ _ => α.mem_closedBall hf.mul_max_le

/--
lemma `intervalIntegrable_comp_compProj` / 引理 `intervalIntegrable_comp_compProj`

English:
lemma intervalIntegrable_comp_compProj
  statement: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  proof: by
  apply ContinuousOn.intervalIntegrable
.mono apply α.continuousOn_comp_compProj hf
  exact uIcc_subset_Icc t₀.2 t.2

中文:
引理 intervalIntegrable_comp_compProj
  结论: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  证明: by
  apply ContinuousOn.intervalIntegrable
.mono apply α.continuousOn_comp_compProj hf
  exact uIcc_subset_Icc t₀.2 t.2

Depends on / 依赖: ContinuousOn, ContinuousOn.intervalIntegrable, continuousOn_comp_compProj, intervalIntegrable, uIcc_subset_Icc
-/
lemma intervalIntegrable_comp_compProj (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (α : FunSpace t₀ x₀ r L) (t : Icc tmin tmax) :
    IntervalIntegrable (fun t' => f t' (α.compProj t')) volume t₀ t := by
  apply ContinuousOn.intervalIntegrable
.mono apply α.continuousOn_comp_compProj hf
  exact uIcc_subset_Icc t₀.2 t.2

/--
Definition of `next` / `next` 的定义

English:
definition next
  signature: (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
  body: picard f t₀ x α.compProj t
  lipschitzWith := LipschitzWith.of_dist_le_mul fun t₁ t₂ => by
    rw [dist_eq_norm]; rw [picard_apply]; rw [picard_apply]; rw [add_sub_add_left_eq_sub]; rw [integral_interval_sub_left (intervalIntegrable_comp_compProj hf _ t₁)
        (intervalIntegrable_comp_compProj hf

中文:
定义 next
  签名: (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
  定义体: picard f t₀ x α.compProj t
  lipschitzWith := LipschitzWith.of_dist_le_mul fun t₁ t₂ => by
    rw [dist_eq_norm]; rw [picard_apply]; rw [picard_apply]; rw [add_sub_add_left_eq_sub]; rw [integral_interval_sub_left (intervalIntegrable_comp_compProj hf _ t₁)
        (intervalIntegrable_comp_compProj hf

Depends on / 依赖: compProj, picard
-/
noncomputable def next (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) : FunSpace t₀ x₀ r L where
  toFun t := picard f t₀ x α.compProj t
  lipschitzWith := LipschitzWith.of_dist_le_mul fun t₁ t₂ => by
    rw [dist_eq_norm]; rw [picard_apply]; rw [picard_apply]; rw [add_sub_add_left_eq_sub]; rw [integral_interval_sub_left (intervalIntegrable_comp_compProj hf _ t₁)
        (intervalIntegrable_comp_compProj hf _ t₂)]; rw [Subtype.dist_eq]; rw [Real.dist_eq]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    -- Can `grind` do this in the future?
    have ht : t in Icc tmin tmax := subset_trans uIoc_subset_uIcc (uIcc_subset_Icc t₂.2 t₁.2) ht
exact hf.norm_le _ ht _ α.mem_closedBall hf.mul_max_le
  mem_closedBall₀ := by simp [hx]

@[simp]
/--
lemma `next_apply` / 引理 `next_apply`

English:
lemma next_apply
  statement: (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
  proof: rfl

中文:
引理 next_apply
  结论: (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
  证明: rfl
-/
lemma next_apply (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) {t : Icc tmin tmax} :
    next hf hx α t = picard f t₀ x α.compProj t := rfl

/--
lemma `next_apply₀` / 引理 `next_apply₀`

English:
lemma next_apply₀
  statement: (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
  proof: by simp

中文:
引理 next_apply₀
  结论: (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
  证明: by simp
-/
lemma next_apply₀ (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) : next hf hx α t₀ = x := by simp

/--
lemma `isFixedPt_next_iff` / 引理 `isFixedPt_next_iff`

English:
lemma isFixedPt_next_iff
  statement: (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
  proof: by
  constructor
.symm · exact fun hα t => congrArg (· t) hα
  · intro h
    ext t
    rw [h]; rw [next_apply]

中文:
引理 isFixedPt_next_iff
  结论: (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
  证明: by
  constructor
.symm · exact fun hα t => congrArg (· t) hα
  · intro h
    ext t
    rw [h]; rw [next_apply]

Depends on / 依赖: next_apply
-/
lemma isFixedPt_next_iff (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
    {α : FunSpace t₀ x₀ r L} :
    IsFixedPt (next hf hx) α ↔ forall t, α t = picard f t₀ x α.compProj t := by
  constructor
.symm · exact fun hα t => congrArg (· t) hα
  · intro h
    ext t
    rw [h]; rw [next_apply]

/--
lemma `dist_comp_iterate_next_le` / 引理 `dist_comp_iterate_next_le`

English:
lemma dist_comp_iterate_next_le
  statement: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  proof: calc
    _ <= K * dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) :=
.dist_le_mul hf.lipschitzOnWith t.1 t.2
        _ (FunSpace.mem_closedBall hf.mul_max_le) _ (FunSpace.mem_closedBall hf.mul_max_le)
    _ <= K ^ (n + 1) * |t - t₀.1| ^ n / n ! * dist α β := by
      rw [pow_succ']; rw [mul_assoc

中文:
引理 dist_comp_iterate_next_le
  结论: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  证明: calc
    _ <= K * dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) :=
.dist_le_mul hf.lipschitzOnWith t.1 t.2
        _ (FunSpace.mem_closedBall hf.mul_max_le) _ (FunSpace.mem_closedBall hf.mul_max_le)
    _ <= K ^ (n + 1) * |t - t₀.1| ^ n / n ! * dist α β := by
      rw [pow_succ']; rw [mul_assoc

Depends on / 依赖: FunSpace, FunSpace.mem_closedBall, dist_le_mul, hf.lipschitzOnWith, hf.mul_max_le, lipschitzOnWith, mem_closedBall, mul_assoc, mul_div_assoc, mul_max_le, mul_pow, pow_succ
-/
lemma dist_comp_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x in closedBall x₀ r) (n : Nat) (t : Icc tmin tmax)
    {α β : FunSpace t₀ x₀ r L}
    (h : dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) <=
      (K * |t - t₀.1|) ^ n / n ! * dist α β) :
    dist (f t ((next hf hx)^[n] α t)) (f t ((next hf hx)^[n] β t)) <=
      K ^ (n + 1) * |t - t₀.1| ^ n / n ! * dist α β :=
  calc
    _ <= K * dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) :=
.dist_le_mul hf.lipschitzOnWith t.1 t.2
        _ (FunSpace.mem_closedBall hf.mul_max_le) _ (FunSpace.mem_closedBall hf.mul_max_le)
    _ <= K ^ (n + 1) * |t - t₀.1| ^ n / n ! * dist α β := by
      rw [pow_succ']; rw [mul_assoc]; rw [mul_div_assoc]; rw [mul_assoc]
      gcongr
      rwa [← mul_pow]

/--
lemma `dist_iterate_next_apply_le` / 引理 `dist_iterate_next_apply_le`

English:
lemma dist_iterate_next_apply_le
  statement: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  proof: by
  induction n generalizing t with
  | zero => simpa using!
      ContinuousMap.dist_apply_le_dist (f := toContinuousMap α) (g := toContinuousMap β) _
  | succ n hn =>
    rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [dist_eq_norm]; rw [next_apply]; rw [next_apply]; rw [picard_apply]; rw

中文:
引理 dist_iterate_next_apply_le
  结论: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  证明: by
  induction n generalizing t with
  | zero => simpa using!
      ContinuousMap.dist_apply_le_dist (f := toContinuousMap α) (g := toContinuousMap β) _
  | succ n hn =>
    rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [dist_eq_norm]; rw [next_apply]; rw [next_apply]; rw [picard_apply]; rw

Depends on / 依赖: ContinuousMap, ContinuousMap.dist_apply_le_dist, add_sub_add_left_eq_sub, dist_apply_le_dist, dist_eq_norm, generalizing, integral_sub, intervalIntegrable_comp_compProj, intervalIntegral, intervalIntegral.integral_sub, iterate_succ_apply, next_apply, picard_apply, toContinuousMap
-/
lemma dist_iterate_next_apply_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x in closedBall x₀ r) (α β : FunSpace t₀ x₀ r L) (n : Nat) (t : Icc tmin tmax) :
    dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) <=
      (K * |t.1 - t₀.1|) ^ n / n ! * dist α β := by
  induction n generalizing t with
  | zero => simpa using!
      ContinuousMap.dist_apply_le_dist (f := toContinuousMap α) (g := toContinuousMap β) _
  | succ n hn =>
    rw [iterate_succ_apply']; rw [iterate_succ_apply']; rw [dist_eq_norm]; rw [next_apply]; rw [next_apply]; rw [picard_apply]; rw [picard_apply]; rw [add_sub_add_left_eq_sub]; rw [← intervalIntegral.integral_sub (intervalIntegrable_comp_compProj hf _ t)
        (intervalIntegrable_comp_compProj hf _ t)]
    calc
      _ <= ∫ τ in uIoc t₀.1 t.1, K ^ (n + 1) * |τ - t₀| ^ n / n ! * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
.mono apply ae_restrict_mem measurableSet_Ioc
        intro t' ht'
        -- Can `grind` do this in the future?
        have ht' : t' in Icc tmin tmax :=
          subset_trans uIoc_subset_uIcc (uIcc_subset_Icc t₀.2 t.2) ht'
        rw [← dist_eq_norm]; rw [compProj_of_mem]; rw [compProj_of_mem]
        exact dist_comp_iterate_next_le hf hx _ ⟨t', ht'⟩ (hn _)
      _ <= (K * |t.1 - t₀.1|) ^ (n + 1) / (n + 1) ! * dist α β := by
        apply le_of_abs_le
        -- critical: `integral_pow_abs_sub_uIoc`
        rw [← intervalIntegral.abs_intervalIntegral_eq]; rw [intervalIntegral.integral_mul_const]; rw [intervalIntegral.integral_div]; rw [intervalIntegral.integral_const_mul]; rw [abs_mul]; rw [abs_div]; rw [abs_mul]; rw [intervalIntegral.abs_intervalIntegral_eq]; rw [integral_pow_abs_sub_uIoc]; rw [abs_div]; rw [abs_pow]; rw [abs_pow]; rw [abs_dist]; rw [NNReal.abs_eq]; rw [abs_abs]; rw [mul_div]; rw [div_div]; rw [← abs_mul]; rw [← Nat.cast_succ]; rw [← Nat.cast_mul]; rw [← Nat.factorial_succ]; rw [Nat.abs_cast]; rw [← mul_pow]

/--
lemma `dist_iterate_next_iterate_next_le` / 引理 `dist_iterate_next_iterate_next_le`

English:
lemma dist_iterate_next_iterate_next_le
  statement: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  proof: by
  rw [← MetricSpace.isometry_induced FunSpace.toContinuousMap FunSpace.toContinuousMap.injective
.dist_eq]; rw [ContinuousMap.dist_le]
  · intro t
apply le_trans dist_iterate_next_apply_le hf hx α β n t
    gcongr
    exact abs_sub_le_max_sub t.2.1 t.2.2 _
· have : 0 <= max (tmax - t₀) (t₀ - tmin

中文:
引理 dist_iterate_next_iterate_next_le
  结论: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  证明: by
  rw [← MetricSpace.isometry_induced FunSpace.toContinuousMap FunSpace.toContinuousMap.injective
.dist_eq]; rw [ContinuousMap.dist_le]
  · intro t
apply le_trans dist_iterate_next_apply_le hf hx α β n t
    gcongr
    exact abs_sub_le_max_sub t.2.1 t.2.2 _
· have : 0 <= max (tmax - t₀) (t₀ - tmin

Depends on / 依赖: ContinuousMap, ContinuousMap.dist_le, FunSpace, FunSpace.toContinuousMap, FunSpace.toContinuousMap.injective, MetricSpace, MetricSpace.isometry_induced, abs_sub_le_max_sub, dist_eq, dist_iterate_next_apply_le, dist_le, injective, isometry_induced, le_max_of_le_left, le_trans, sub_nonneg_of_le, toContinuousMap
-/
lemma dist_iterate_next_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x in closedBall x₀ r) (α β : FunSpace t₀ x₀ r L) (n : Nat) :
    dist ((next hf hx)^[n] α) ((next hf hx)^[n] β) <=
      (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! * dist α β := by
  rw [← MetricSpace.isometry_induced FunSpace.toContinuousMap FunSpace.toContinuousMap.injective
.dist_eq]; rw [ContinuousMap.dist_le]
  · intro t
apply le_trans dist_iterate_next_apply_le hf hx α β n t
    gcongr
    exact abs_sub_le_max_sub t.2.1 t.2.2 _
· have : 0 <= max (tmax - t₀) (t₀ - tmin) := le_max_of_le_left sub_nonneg_of_le t₀.2.2
    positivity

/--
lemma `exists_contractingWith_iterate_next` / 引理 `exists_contractingWith_iterate_next`

English:
lemma exists_contractingWith_iterate_next
  given: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  proof: by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (tmax - t₀) (t₀ - tmin))
.exists .eventually (gt_mem_nhds zero_lt_one)
  have : (0 : Real) <= (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! := by
have : 0 <= max (tmax - t₀) (t₀ - tmin) := le_max_of_le_left sub_nonneg_of_le 

中文:
引理 exists_contractingWith_iterate_next
  条件: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  证明: by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (tmax - t₀) (t₀ - tmin))
.exists .eventually (gt_mem_nhds zero_lt_one)
  have : (0 : Real) <= (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! := by
have : 0 <= max (tmax - t₀) (t₀ - tmin) := le_max_of_le_left sub_nonneg_of_le 

Depends on / 依赖: FloorSemiring, FloorSemiring.tendsto_pow_div_factorial_atTop, LipschitzWith, LipschitzWith.of_dist_le_mul, dist_iterate_next_iterate_next_le, eventually, gt_mem_nhds, le_max_of_le_left, of_dist_le_mul, sub_nonneg_of_le, tendsto_pow_div_factorial_atTop, zero_lt_one
-/
lemma exists_contractingWith_iterate_next (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    exists (n : Nat) (C : Real>=0), forall (x : E) (hx : x in closedBall x₀ r),
      ContractingWith C (next hf hx)^[n] := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (tmax - t₀) (t₀ - tmin))
.exists .eventually (gt_mem_nhds zero_lt_one)
  have : (0 : Real) <= (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! := by
have : 0 <= max (tmax - t₀) (t₀ - tmin) := le_max_of_le_left sub_nonneg_of_le t₀.2.2
    positivity
  refine ⟨n, ⟨_, this⟩, fun x hx => ?_⟩
  exact ⟨hn, LipschitzWith.of_dist_le_mul fun α β => dist_iterate_next_iterate_next_le hf hx α β n⟩

/--
lemma `exists_isFixedPt_next` / 引理 `exists_isFixedPt_next`

English:
lemma exists_isFixedPt_next
  statement: [CompleteSpace E] (hf : IsPicardLindelof f t₀ x₀ a r L K)
  proof: let ⟨_, _, h⟩ := exists_contractingWith_iterate_next hf
.isFixedPt_fixedPoint_iterate⟩ ⟨_, h x hx

中文:
引理 exists_isFixedPt_next
  结论: [CompleteSpace E] (hf : IsPicardLindelof f t₀ x₀ a r L K)
  证明: let ⟨_, _, h⟩ := exists_contractingWith_iterate_next hf
.isFixedPt_fixedPoint_iterate⟩ ⟨_, h x hx

Depends on / 依赖: exists_contractingWith_iterate_next, isFixedPt_fixedPoint_iterate
-/
lemma exists_isFixedPt_next [CompleteSpace E] (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x in closedBall x₀ r) :
    exists α : FunSpace t₀ x₀ r L, IsFixedPt (next hf hx) α :=
  let ⟨_, _, h⟩ := exists_contractingWith_iterate_next hf
.isFixedPt_fixedPoint_iterate⟩ ⟨_, h x hx

/-! ## Lipschitz continuity of the solution with respect to the initial condition

The proof relies on the fact that the repeated application of `next` to any curve `α` converges to
the fixed point of `next`, so it suffices to bound the distance between `α` and `next^[n] α`. Since
there is some `m : ℕ` such that `next^[m]` is a contracting map, it further suffices to bound the
distance between `α` and `next^[m]^[n] α`.
-/

/--
lemma `dist_next_next` / 引理 `dist_next_next`

English:
lemma dist_next_next
  statement: (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
  proof: by
  have : Nonempty (Icc tmin tmax) := ⟨t₀⟩ -- needed for `ciSup_const`
  rw [← MetricSpace.isometry_induced FunSpace.toContinuousMap FunSpace.toContinuousMap.injective
.dist_eq]; rw [dist_eq_norm]; rw [ContinuousMap.norm_eq_iSup_norm]
  simp [add_sub_add_right_eq_sub, dist_eq_norm]

中文:
引理 dist_next_next
  结论: (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
  证明: by
  have : Nonempty (Icc tmin tmax) := ⟨t₀⟩ -- needed for `ciSup_const`
  rw [← MetricSpace.isometry_induced FunSpace.toContinuousMap FunSpace.toContinuousMap.injective
.dist_eq]; rw [dist_eq_norm]; rw [ContinuousMap.norm_eq_iSup_norm]
  simp [add_sub_add_right_eq_sub, dist_eq_norm]

Depends on / 依赖: ContinuousMap, ContinuousMap.norm_eq_iSup_norm, FunSpace, FunSpace.toContinuousMap, FunSpace.toContinuousMap.injective, MetricSpace, MetricSpace.isometry_induced, Nonempty, add_sub_add_right_eq_sub, ciSup_const, dist_eq, dist_eq_norm, injective, isometry_induced, needed, norm_eq_iSup_norm, toContinuousMap
-/
lemma dist_next_next (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
    (hy : y in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) :
    dist (next hf hx α) (next hf hy α) = dist x y := by
  have : Nonempty (Icc tmin tmax) := ⟨t₀⟩ -- needed for `ciSup_const`
  rw [← MetricSpace.isometry_induced FunSpace.toContinuousMap FunSpace.toContinuousMap.injective
.dist_eq]; rw [dist_eq_norm]; rw [ContinuousMap.norm_eq_iSup_norm]
  simp [add_sub_add_right_eq_sub, dist_eq_norm]

/--
lemma `dist_iterate_next_le` / 引理 `dist_iterate_next_le`

English:
lemma dist_iterate_next_le
  statement: (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
  proof: by
  nth_rw 1 [← iterate_zero_apply (next hf hx) α]
  rw [Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i => (next hf hx)^[i] α)
  intro i hi
  rw [iterate_succ_apply]
  exact dist_iterate_next_iterate_next_le hf hx _ _ i

中文:
引理 dist_iterate_next_le
  结论: (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
  证明: by
  nth_rw 1 [← iterate_zero_apply (next hf hx) α]
  rw [Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i => (next hf hx)^[i] α)
  intro i hi
  rw [iterate_succ_apply]
  exact dist_iterate_next_iterate_next_le hf hx _ _ i

Depends on / 依赖: Finset, Finset.sum_mul, dist_iterate_next_iterate_next_le, dist_le_range_sum_of_dist_le, iterate_succ_apply, iterate_zero_apply, nth_rw, sum_mul
-/
lemma dist_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) (n : Nat) :
    dist α ((next hf hx)^[n] α) <=
      (∑ i in Finset.range n, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !)
        * dist α (next hf hx α) := by
  nth_rw 1 [← iterate_zero_apply (next hf hx) α]
  rw [Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i => (next hf hx)^[i] α)
  intro i hi
  rw [iterate_succ_apply]
  exact dist_iterate_next_iterate_next_le hf hx _ _ i

/--
lemma `dist_iterate_iterate_next_le_of_lipschitzWith` / 引理 `dist_iterate_iterate_next_le_of_lipschitzWith`

English:
lemma dist_iterate_iterate_next_le_of_lipschitzWith
  statement: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  proof: by
  nth_rw 1 [← iterate_zero_apply (next hf hx) α]
  rw [Finset.mul_sum]; rw [Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i => (next hf hx)^[m]^[i] α)
  intro i hi
  rw [iterate_succ_apply]
apply le_trans hm.dist_iterate_succ_le_geometric α i
  rw [mul_assoc]; rw [mul_comm ((C : 

中文:
引理 dist_iterate_iterate_next_le_of_lipschitzWith
  结论: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  证明: by
  nth_rw 1 [← iterate_zero_apply (next hf hx) α]
  rw [Finset.mul_sum]; rw [Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i => (next hf hx)^[m]^[i] α)
  intro i hi
  rw [iterate_succ_apply]
apply le_trans hm.dist_iterate_succ_le_geometric α i
  rw [mul_assoc]; rw [mul_comm ((C : 

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_mul, dist_iterate_next_le, dist_iterate_succ_le_geometric, dist_le_range_sum_of_dist_le, hm.dist_iterate_succ_le_geometric, iterate_succ_apply, iterate_zero_apply, le_trans, mul_assoc, mul_comm, mul_sum, nth_rw, sum_mul
-/
lemma dist_iterate_iterate_next_le_of_lipschitzWith (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) {m : Nat} {C : Real>=0}
    (hm : LipschitzWith C (next hf hx)^[m]) (n : Nat) :
    dist α ((next hf hx)^[m]^[n] α) <=
      (∑ i in Finset.range m, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !) *
        (∑ i in Finset.range n, (C : Real) ^ i) * dist α (next hf hx α) := by
  nth_rw 1 [← iterate_zero_apply (next hf hx) α]
  rw [Finset.mul_sum]; rw [Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i => (next hf hx)^[m]^[i] α)
  intro i hi
  rw [iterate_succ_apply]
apply le_trans hm.dist_iterate_succ_le_geometric α i
  rw [mul_assoc]; rw [mul_comm ((C : Real) ^ i)]; rw [← mul_assoc]
  gcongr
  exact dist_iterate_next_le hf hx α m

/--
lemma `exists_forall_closedBall_funSpace_dist_le_mul` / 引理 `exists_forall_closedBall_funSpace_dist_le_mul`

English:
lemma exists_forall_closedBall_funSpace_dist_le_mul
  statement: [CompleteSpace E]
  proof: by
  obtain ⟨m, C, h⟩ := exists_contractingWith_iterate_next hf
  let L' := (∑ i in Finset.range m, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !) * (1 - C)⁻¹
  have hL' : 0 <= L' := by
have : 0 <= max (tmax - t₀) (t₀ - tmin) := le_max_of_le_left sub_nonneg_of_le t₀.2.2
    positivity
  refine ⟨.mk L'

中文:
引理 exists_forall_closedBall_funSpace_dist_le_mul
  结论: [CompleteSpace E]
  证明: by
  obtain ⟨m, C, h⟩ := exists_contractingWith_iterate_next hf
  let L' := (∑ i in Finset.range m, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !) * (1 - C)⁻¹
  have hL' : 0 <= L' := by
have : 0 <= max (tmax - t₀) (t₀ - tmin) := le_max_of_le_left sub_nonneg_of_le t₀.2.2
    positivity
  refine ⟨.mk L'

Depends on / 依赖: Filter, Filter.Tendsto.comp, Filter.atTop, Finset, Finset.range, NNReal, NNReal.coe_mk, Tendsto, coe_mk, dist_iterate_iterate_next_le_of_lipschitzWith, exists_contractingWith_iterate_next, le_max_of_le_left, le_of_tendsto_of_tendsto, sub_nonneg_of_le
-/
lemma exists_forall_closedBall_funSpace_dist_le_mul [CompleteSpace E]
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    exists L' : Real>=0, forall (x y : E) (hx : x in closedBall x₀ r) (hy : y in closedBall x₀ r)
      (α β : FunSpace t₀ x₀ r L) (_ : IsFixedPt (next hf hx) α) (_ : IsFixedPt (next hf hy) β),
      dist α β <= L' * dist x y := by
  obtain ⟨m, C, h⟩ := exists_contractingWith_iterate_next hf
  let L' := (∑ i in Finset.range m, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !) * (1 - C)⁻¹
  have hL' : 0 <= L' := by
have : 0 <= max (tmax - t₀) (t₀ - tmin) := le_max_of_le_left sub_nonneg_of_le t₀.2.2
    positivity
  refine ⟨.mk L' hL', fun x y hx hy α β hα hβ => ?_⟩
  rw [NNReal.coe_mk]
apply le_of_tendsto_of_tendsto' (b := Filter.atTop) _ _
    dist_iterate_iterate_next_le_of_lipschitzWith hf hy α (h y hy).2
  · apply Filter.Tendsto.comp (y := 𝓝 β) (tendsto_const_nhds.dist Filter.tendsto_id)
    rw [h y hy |>.fixedPoint_unique (hβ.iterate m)]
.tendsto_iterate_fixedPoint α exact h y hy
  · nth_rw 1 [← hα, dist_next_next]
    apply Filter.Tendsto.mul_const
    apply Filter.Tendsto.const_mul
.tendsto_sum_nat convert! hasSum_geometric_of_lt_one C.2 (h y hy).1
    simp [NNReal.coe_sub <| le_of_lt (h y hy).1, NNReal.coe_one]

end

end FunSpace

/-! ## Properties of the integral equation -/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  {f : Real -> E -> E} {α : Real -> E} {s : Set Real} {u : Set E} {t₀ tmin tmax : Real}

-- TODO: generalise to open sets and `Ici` and `Iic`
/--
lemma `hasDerivWithinAt_picard_Icc` / 引理 `hasDerivWithinAt_picard_Icc`

English:
lemma hasDerivWithinAt_picard_Icc
  proof: by
  apply HasDerivWithinAt.const_add
  have : Fact (t in Icc tmin tmax) := ⟨ht⟩ -- needed to synthesise `FTCFilter` for `Icc`
  apply intervalIntegral.integral_hasDerivWithinAt_right _ -- need `CompleteSpace E` and `Icc`
    (continuousOn_comp hf hα hmem |>.stronglyMeasurableAtFilter_nhdsWithin mea

中文:
引理 hasDerivWithinAt_picard_Icc
  证明: by
  apply HasDerivWithinAt.const_add
  have : Fact (t in Icc tmin tmax) := ⟨ht⟩ -- needed to synthesise `FTCFilter` for `Icc`
  apply intervalIntegral.integral_hasDerivWithinAt_right _ -- need `CompleteSpace E` and `Icc`
    (continuousOn_comp hf hα hmem |>.stronglyMeasurableAtFilter_nhdsWithin mea

Depends on / 依赖: CompleteSpace, ContinuousOn, ContinuousOn.intervalIntegrable, FTCFilter, HasDerivWithinAt, HasDerivWithinAt.const_add, const_add, continuousOn_comp, integral_hasDerivWithinAt_right, intervalIntegrable, intervalIntegral, intervalIntegral.integral_hasDerivWithinAt_right, measurableSet_Icc, needed, stronglyMeasurableAtFilter_nhdsWithin, synthesise, uIcc_subset_Icc
-/
lemma hasDerivWithinAt_picard_Icc
    (ht₀ : t₀ in Icc tmin tmax)
    (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : forall t in Icc tmin tmax, α t in u) (x₀ : E)
    {t : Real} (ht : t in Icc tmin tmax) :
    HasDerivWithinAt (picard f t₀ x₀ α) (f t (α t)) (Icc tmin tmax) t := by
  apply HasDerivWithinAt.const_add
  have : Fact (t in Icc tmin tmax) := ⟨ht⟩ -- needed to synthesise `FTCFilter` for `Icc`
  apply intervalIntegral.integral_hasDerivWithinAt_right _ -- need `CompleteSpace E` and `Icc`
    (continuousOn_comp hf hα hmem |>.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
    (continuousOn_comp hf hα hmem _ ht)
  apply ContinuousOn.intervalIntegrable
.mono apply continuousOn_comp hf hα hmem
  exact uIcc_subset_Icc ht₀ ht

/--
lemma `picard_eq_of_hasDerivAt` / 引理 `picard_eq_of_hasDerivAt`

English:
lemma picard_eq_of_hasDerivAt
  statement: {t : Real}
  proof: by
  rw [← add_sub_cancel (α t₀) (α t)]; rw [picard_apply]; rw [integral_eq_sub_of_hasDeriv_right (HasDerivWithinAt.continuousOn hα) _
      (continuousOn_comp hf (HasDerivWithinAt.continuousOn hα) hmap |>.intervalIntegrable)]
  intro t' ht'
  apply HasDerivAt.hasDerivWithinAt
.hasDerivAt Icc_mem_nh

中文:
引理 picard_eq_of_hasDerivAt
  结论: {t : 实数}
  证明: by
  rw [← add_sub_cancel (α t₀) (α t)]; rw [picard_apply]; rw [integral_eq_sub_of_hasDeriv_right (HasDerivWithinAt.continuousOn hα) _
      (continuousOn_comp hf (HasDerivWithinAt.continuousOn hα) hmap |>.intervalIntegrable)]
  intro t' ht'
  apply HasDerivAt.hasDerivWithinAt
.hasDerivAt Icc_mem_nh

Depends on / 依赖: HasDerivAt, HasDerivAt.hasDerivWithinAt, HasDerivWithinAt, HasDerivWithinAt.continuousOn, Icc_mem_nhds, Ioo_subset_Icc_self, add_sub_cancel, continuousOn, continuousOn_comp, hasDerivAt, hasDerivWithinAt, integral_eq_sub_of_hasDeriv_right, intervalIntegrable, picard_apply
-/
lemma picard_eq_of_hasDerivAt {t : Real}
    (hf : ContinuousOn (uncurry f) ((uIcc t₀ t) ×ˢ u))
    (hα : forall t' in uIcc t₀ t, HasDerivWithinAt α (f t' (α t')) (uIcc t₀ t) t')
    (hmap : MapsTo α (uIcc t₀ t) u) :
    picard f t₀ (α t₀) α t = α t := by
  rw [← add_sub_cancel (α t₀) (α t)]; rw [picard_apply]; rw [integral_eq_sub_of_hasDeriv_right (HasDerivWithinAt.continuousOn hα) _
      (continuousOn_comp hf (HasDerivWithinAt.continuousOn hα) hmap |>.intervalIntegrable)]
  intro t' ht'
  apply HasDerivAt.hasDerivWithinAt
.hasDerivAt Icc_mem_nhds ht'.1 ht'.2 exact hα t' (Ioo_subset_Icc_self ht')

/--
lemma `contDiffOn_nat_picard_Icc` / 引理 `contDiffOn_nat_picard_Icc`

English:
lemma contDiffOn_nat_picard_Icc
  proof: by
  by_cases hlt : tmin < tmax
  · have (t) (ht : t in Icc tmin tmax) :=
      hasDerivWithinAt_picard_Icc ht₀ hf.continuousOn hα hmem x₀ ht
    induction n with
    | zero =>
      simp only [Nat.cast_zero, contDiffOn_zero] at *
      exact HasDerivWithinAt.continuousOn this
    | succ n hn =>
   

中文:
引理 contDiffOn_nat_picard_Icc
  证明: by
  by_cases hlt : tmin < tmax
  · have (t) (ht : t in Icc tmin tmax) :=
      hasDerivWithinAt_picard_Icc ht₀ hf.continuousOn hα hmem x₀ ht
    induction n with
    | zero =>
      simp only [Nat.cast_zero, contDiffOn_zero] at *
      exact HasDerivWithinAt.continuousOn this
    | succ n hn =>
   

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.continuousOn, HasDerivWithinAt.differentiableWithinAt, Nat.cast_add, Nat.cast_one, Nat.cast_zero, cast_add, cast_one, cast_zero, contDiffOn_comp, contDiffOn_succ_iff_derivWithin, contDiffOn_zero, continuousOn, differentiableWithinAt, hasDerivWithinAt_picard_Icc, hf.continuousOn, hf.of_succ, of_succ, uniqueDiffOn_Icc
-/
lemma contDiffOn_nat_picard_Icc
    (ht₀ : t₀ in Icc tmin tmax) {n : Nat}
    (hf : ContDiffOn Real n (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : forall t in Icc tmin tmax, α t in u) (x₀ : E)
    (heqon : forall t in Icc tmin tmax, α t = picard f t₀ x₀ α t) :
    ContDiffOn Real n (picard f t₀ x₀ α) (Icc tmin tmax) := by
  by_cases hlt : tmin < tmax
  · have (t) (ht : t in Icc tmin tmax) :=
      hasDerivWithinAt_picard_Icc ht₀ hf.continuousOn hα hmem x₀ ht
    induction n with
    | zero =>
      simp only [Nat.cast_zero, contDiffOn_zero] at *
      exact HasDerivWithinAt.continuousOn this
    | succ n hn =>
      simp only [Nat.cast_add, Nat.cast_one] at *
      rw [contDiffOn_succ_iff_derivWithin <| uniqueDiffOn_Icc hlt]
      refine ⟨fun t ht => HasDerivWithinAt.differentiableWithinAt (this t ht), by simp, ?_⟩
.congr apply contDiffOn_comp hf.of_succ (ContDiffOn.congr (hn hf.of_succ) heqon) hmem
      intro t ht
exact HasDerivWithinAt.derivWithin (this t ht) (uniqueDiffOn_Icc hlt).uniqueDiffWithinAt ht
  · rw [(subsingleton_Icc_of_ge (not_lt.mp hlt)).eq_singleton_of_mem ht₀]
    intro t ht
    rw [eq_of_mem_singleton ht]
    exact contDiffWithinAt_singleton

/--
lemma `contDiffOn_enat_picard_Icc` / 引理 `contDiffOn_enat_picard_Icc`

English:
lemma contDiffOn_enat_picard_Icc
  proof: by
  induction n with
  | top =>
    rw [contDiffOn_infty] at *
    exact fun k => contDiffOn_nat_picard_Icc ht₀ (hf k) hα hmem x₀ heqon
  | coe n => exact contDiffOn_nat_picard_Icc ht₀ hf hα hmem x₀ heqon

中文:
引理 contDiffOn_enat_picard_Icc
  证明: by
  induction n with
  | top =>
    rw [contDiffOn_infty] at *
    exact fun k => contDiffOn_nat_picard_Icc ht₀ (hf k) hα hmem x₀ heqon
  | coe n => exact contDiffOn_nat_picard_Icc ht₀ hf hα hmem x₀ heqon

Depends on / 依赖: contDiffOn_infty, contDiffOn_nat_picard_Icc
-/
lemma contDiffOn_enat_picard_Icc
    (ht₀ : t₀ in Icc tmin tmax) {n : Nat∞}
    (hf : ContDiffOn Real n (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : forall t in Icc tmin tmax, α t in u) (x₀ : E)
    (heqon : forall t in Icc tmin tmax, α t = picard f t₀ x₀ α t) :
    ContDiffOn Real n (picard f t₀ x₀ α) (Icc tmin tmax) := by
  induction n with
  | top =>
    rw [contDiffOn_infty] at *
    exact fun k => contDiffOn_nat_picard_Icc ht₀ (hf k) hα hmem x₀ heqon
  | coe n => exact contDiffOn_nat_picard_Icc ht₀ hf hα hmem x₀ heqon

/--
theorem `contDiffOn_enat_Icc_of_hasDerivWithinAt` / 定理 `contDiffOn_enat_Icc_of_hasDerivWithinAt`

English:
theorem contDiffOn_enat_Icc_of_hasDerivWithinAt
  statement: {n : Nat∞}
  proof: by
  by_cases hlt : tmin < tmax
  · set t₀ := (tmin + tmax) / 2 with h
    have ht₀ : t₀ in Icc tmin tmax := ⟨by linarith, by linarith⟩
    have : forall t in Icc tmin tmax, α t = picard f t₀ (α t₀) α t := by
      intro t ht
      have : uIcc t₀ t subseteq Icc tmin tmax := uIcc_subset_Icc ht₀ ht
  

中文:
定理 contDiffOn_enat_Icc_of_hasDerivWithinAt
  结论: {n : 自然数∞}
  证明: by
  by_cases hlt : tmin < tmax
  · set t₀ := (tmin + tmax) / 2 with h
    have ht₀ : t₀ in Icc tmin tmax := ⟨by linarith, by linarith⟩
    have : forall t in Icc tmin tmax, α t = picard f t₀ (α t₀) α t := by
      intro t ht
      have : uIcc t₀ t subseteq Icc tmin tmax := uIcc_subset_Icc ht₀ ht
  

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.continuousOn, contDiffOn_enat_picard_Icc, continuousOn, eqToIso, hf.continuousOn.mono, hmem.mono_left, isIso_hom, mono_left, picard, picard_eq_of_hasDerivAt, prod_subset_prod_left, subseteq, uIcc_subset_Icc
-/
theorem contDiffOn_enat_Icc_of_hasDerivWithinAt {n : Nat∞}
    (hf : ContDiffOn Real n (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : forall t in Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t)
    (hmem : MapsTo α (Icc tmin tmax) u) :
    ContDiffOn Real n α (Icc tmin tmax) := by
  by_cases hlt : tmin < tmax
  · set t₀ := (tmin + tmax) / 2 with h
    have ht₀ : t₀ in Icc tmin tmax := ⟨by linarith, by linarith⟩
    have : forall t in Icc tmin tmax, α t = picard f t₀ (α t₀) α t := by
      intro t ht
      have : uIcc t₀ t subseteq Icc tmin tmax := uIcc_subset_Icc ht₀ ht
      rw [picard_eq_of_hasDerivAt (hf.continuousOn.mono (prod_subset_prod_left this))
        (fun t' ht' => hα t' (this ht') |>.mono this) (hmem.mono_left this)]
    exact contDiffOn_enat_picard_Icc ht₀ hf (HasDerivWithinAt.continuousOn hα) hmem (α t₀) this
.congr this
  · rw [not_lt, le_iff_lt_or_eq] at hlt
    cases hlt with
    | inl h =>
      intro _ ht
      rw [Icc_eq_empty (not_le.mpr h)] at ht
      exfalso
      exact notMem_empty _ ht
    | inr h =>
      rw [h]; rw [Icc_self]
      intro _ ht
      rw [eq_of_mem_singleton ht]
      exact contDiffWithinAt_singleton

end

end ODE

namespace IsPicardLindelof

/-! ## Properties of `IsPicardLindelof` -/

section

variable {E : Type*} [NormedAddCommGroup E]
  {f : Real -> E -> E} {tmin tmax : Real} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : Real>=0}

/--
lemma `continuousOn_uncurry` / 引理 `continuousOn_uncurry`

English:
lemma continuousOn_uncurry
  given: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  proof: continuousOn_prod_of_continuousOn_lipschitzOnWith' _ K hf.lipschitzOnWith hf.continuousOn

中文:
引理 continuousOn_uncurry
  条件: (hf : IsPicardLindelof f t₀ x₀ a r L K)
  证明: continuousOn_prod_of_continuousOn_lipschitzOnWith' _ K hf.lipschitzOnWith hf.continuousOn

Depends on / 依赖: continuousOn, continuousOn_prod_of_continuousOn_lipschitzOnWith, hf.continuousOn, hf.lipschitzOnWith, lipschitzOnWith
-/
lemma continuousOn_uncurry (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ (closedBall x₀ a)) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith' _ K hf.lipschitzOnWith hf.continuousOn

/--
lemma `shrink` / 引理 `shrink`

English:
lemma shrink
  statement: {f : Real -> E -> E} {tmin tmax tmin' tmax' : Real} {t₀ : Icc tmin tmax}
  proof: (hf.lipschitzOnWith t ⟨htmin.trans ht.1, ht.2.trans htmax⟩).mono
    (closedBall_subset_closedBall ha)
  continuousOn x hx := (hf.continuousOn x (closedBall_subset_closedBall ha hx)).mono
    fun _ ht => ⟨htmin.trans ht.1, ht.2.trans htmax⟩
  norm_le t ht x hx := hf.norm_le t ⟨htmin.trans ht.1, ht.2

中文:
引理 shrink
  结论: {f : 实数 -> E -> E} {tmin tmax tmin' tmax' : 实数} {t₀ : Icc tmin tmax}
  证明: (hf.lipschitzOnWith t ⟨htmin.trans ht.1, ht.2.trans htmax⟩).mono
    (closedBall_subset_closedBall ha)
  continuousOn x hx := (hf.continuousOn x (closedBall_subset_closedBall ha hx)).mono
    fun _ ht => ⟨htmin.trans ht.1, ht.2.trans htmax⟩
  norm_le t ht x hx := hf.norm_le t ⟨htmin.trans ht.1, ht.2

Depends on / 依赖: hf.lipschitzOnWith, htmin.trans, lipschitzOnWith
-/
lemma shrink {f : Real -> E -> E} {tmin tmax tmin' tmax' : Real} {t₀ : Icc tmin tmax}
    {x₀ : E} {a r L K : Real>=0} (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (t₀' : Icc tmin' tmax') (htmin : tmin <= tmin') (htmax : tmax' <= tmax)
    {a' r' : Real>=0} (ha : a' <= a)
    (htime : L * max (tmax' - t₀') (t₀' - tmin') <= a' - r') :
    IsPicardLindelof f t₀' x₀ a' r' L K where
  lipschitzOnWith t ht := (hf.lipschitzOnWith t ⟨htmin.trans ht.1, ht.2.trans htmax⟩).mono
    (closedBall_subset_closedBall ha)
  continuousOn x hx := (hf.continuousOn x (closedBall_subset_closedBall ha hx)).mono
    fun _ ht => ⟨htmin.trans ht.1, ht.2.trans htmax⟩
  norm_le t ht x hx := hf.norm_le t ⟨htmin.trans ht.1, ht.2.trans htmax⟩ x
    (closedBall_subset_closedBall ha hx)
  mul_max_le := htime

/--
lemma `shrink_time` / 引理 `shrink_time`

English:
lemma shrink_time
  statement: {f : Real -> E -> E} {tmin tmax tmin' tmax' : Real} {t₀ : Icc tmin tmax}
  proof: by
  apply hf.shrink t₀' htmin htmax le_rfl
  calc L * max (tmax' - t₀') (t₀' - tmin')
    _ <= L * max (tmax - t₀) (t₀ - tmin) := by gcongr <;> linarith
    _ <= a - r := hf.mul_max_le

中文:
引理 shrink_time
  结论: {f : 实数 -> E -> E} {tmin tmax tmin' tmax' : 实数} {t₀ : Icc tmin tmax}
  证明: by
  apply hf.shrink t₀' htmin htmax le_rfl
  calc L * max (tmax' - t₀') (t₀' - tmin')
    _ <= L * max (tmax - t₀) (t₀ - tmin) := by gcongr <;> linarith
    _ <= a - r := hf.mul_max_le

Depends on / 依赖: hf.mul_max_le, hf.shrink, le_rfl, mul_max_le, shrink
-/
lemma shrink_time {f : Real -> E -> E} {tmin tmax tmin' tmax' : Real} {t₀ : Icc tmin tmax}
    {x₀ : E} {a r L K : Real>=0} (hf : IsPicardLindelof f t₀ x₀ a r L K) (t₀' : Icc tmin' tmax')
    (ht₀ : t₀.1 = t₀'.1) (htmin : tmin <= tmin') (htmax : tmax' <= tmax) :
    IsPicardLindelof f t₀' x₀ a r L K := by
  apply hf.shrink t₀' htmin htmax le_rfl
  calc L * max (tmax' - t₀') (t₀' - tmin')
    _ <= L * max (tmax - t₀) (t₀ - tmin) := by gcongr <;> linarith
    _ <= a - r := hf.mul_max_le

/--
lemma `weaken_lipschitz` / 引理 `weaken_lipschitz`

English:
lemma weaken_lipschitz
  given: (hf : IsPicardLindelof f t₀ x₀ a r L K) {K' : Real>=0} (hK : K <= K')
  proof: (hf.lipschitzOnWith t ht).weaken hK
  continuousOn := hf.continuousOn
  norm_le := hf.norm_le
  mul_max_le := hf.mul_max_le

中文:
引理 weaken_lipschitz
  条件: (hf : IsPicardLindelof f t₀ x₀ a r L K) {K' : 实数>=0} (hK : K <= K')
  证明: (hf.lipschitzOnWith t ht).weaken hK
  continuousOn := hf.continuousOn
  norm_le := hf.norm_le
  mul_max_le := hf.mul_max_le

Depends on / 依赖: hf.lipschitzOnWith, lipschitzOnWith, weaken
-/
lemma weaken_lipschitz (hf : IsPicardLindelof f t₀ x₀ a r L K) {K' : Real>=0} (hK : K <= K') :
    IsPicardLindelof f t₀ x₀ a r L K' where
  lipschitzOnWith t ht := (hf.lipschitzOnWith t ht).weaken hK
  continuousOn := hf.continuousOn
  norm_le := hf.norm_le
  mul_max_le := hf.mul_max_le

/--
lemma `exists_shrink_radius` / 引理 `exists_shrink_radius`

English:
lemma exists_shrink_radius
  statement: {f : Real -> E -> E} {t₀ ε : Real} (hε : 0 < ε) {x₀ : E} {a r L K : Real>=0}
  proof: by
  have ha'r' : (0 : Real) < a' - r' := by simp only [sub_pos, NNReal.coe_lt_coe, hr]
  let ε' := min ε ((a' - r') / (L + 1))
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  have hε'_le : ε' <= ε := min_le_left _ _
  refine ⟨ε', hε'pos, hf.shrink ⟨t₀, by simp [le_of_lt hε'pos]⟩ (by linarith)

中文:
引理 exists_shrink_radius
  结论: {f : 实数 -> E -> E} {t₀ ε : 实数} (hε : 0 < ε) {x₀ : E} {a r L K : 实数>=0}
  证明: by
  have ha'r' : (0 : Real) < a' - r' := by simp only [sub_pos, NNReal.coe_lt_coe, hr]
  let ε' := min ε ((a' - r') / (L + 1))
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  have hε'_le : ε' <= ε := min_le_left _ _
  refine ⟨ε', hε'pos, hf.shrink ⟨t₀, by simp [le_of_lt hε'pos]⟩ (by linarith)
-/
lemma exists_shrink_radius {f : Real -> E -> E} {t₀ ε : Real} (hε : 0 < ε) {x₀ : E} {a r L K : Real>=0}
    (hf : IsPicardLindelof f (tmin := t₀ - ε) (tmax := t₀ + ε)
      ⟨t₀, by simp [le_of_lt hε]⟩ x₀ a r L K)
    {a' r' : Real>=0} (ha : a' <= a) (hr : r' < a') :
    exists (ε' : Real) (hε' : 0 < ε'), IsPicardLindelof f (tmin := t₀ - ε') (tmax := t₀ + ε')
      ⟨t₀, by simp [le_of_lt hε']⟩ x₀ a' r' L K := by
  have ha'r' : (0 : Real) < a' - r' := by simp only [sub_pos, NNReal.coe_lt_coe, hr]
  let ε' := min ε ((a' - r') / (L + 1))
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  have hε'_le : ε' <= ε := min_le_left _ _
  refine ⟨ε', hε'pos, hf.shrink ⟨t₀, by simp [le_of_lt hε'pos]⟩ (by linarith) (by linarith) ha ?_⟩
  simp only [add_sub_cancel_left, sub_sub_cancel, max_self]
  calc (L : Real) * ε'
    _ <= L * ((a' - r') / (L + 1)) := by gcongr; exact min_le_right _ _
    _ = L / (L + 1) * (a' - r') := by ring
    _ <= 1 * (a' - r') := by gcongr; rw [div_le_one (by positivity : (0 : Real) < L + 1)]; linarith
    _ = a' - r' := one_mul _

/--
lemma `of_time_independent` / 引理 `of_time_independent`

English:
lemma of_time_independent
  proof: fun _ _ => hl
  continuousOn := fun _ _ => continuousOn_const
  norm_le := fun _ _ => hb
  mul_max_le := hm

中文:
引理 of_time_independent
  证明: fun _ _ => hl
  continuousOn := fun _ _ => continuousOn_const
  norm_le := fun _ _ => hb
  mul_max_le := hm
-/
lemma of_time_independent
    {f : E -> E} {tmin tmax : Real} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : Real>=0}
    (hb : forall x in closedBall x₀ a, ‖f x‖ <= L)
    (hl : LipschitzOnWith K f (closedBall x₀ a))
    (hm : L * max (tmax - t₀) (t₀ - tmin) <= a - r) :
    (IsPicardLindelof (fun _ => f) t₀ x₀ a r L K) where
  lipschitzOnWith := fun _ _ => hl
  continuousOn := fun _ _ => continuousOn_const
  norm_le := fun _ _ => hb
  mul_max_le := hm

/--
lemma `of_contDiffAt_one` / 引理 `of_contDiffAt_one`

English:
lemma of_contDiffAt_one
  statement: [NormedSpace Real E]
  proof: by
  -- Obtain ball of radius `a` within the domain in which f is `K`-lipschitz
  obtain ⟨K, s, hs, hl⟩ := hf.exists_lipschitzOnWith
  obtain ⟨a, ha : 0 < a, has⟩ := Metric.mem_nhds_iff.mp hs
  set L := K * a + ‖f x₀‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  have hb (x : E) (hx : x in close

中文:
引理 of_contDiffAt_one
  结论: [NormedSpace 实数 E]
  证明: by
  -- Obtain ball of radius `a` within the domain in which f is `K`-lipschitz
  obtain ⟨K, s, hs, hl⟩ := hf.exists_lipschitzOnWith
  obtain ⟨a, ha : 0 < a, has⟩ := Metric.mem_nhds_iff.mp hs
  set L := K * a + ‖f x₀‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  have hb (x : E) (hx : x in close

Depends on / 依赖: le_of_lt
-/
lemma of_contDiffAt_one [NormedSpace Real E]
    {f : E -> E} {x₀ : E} (hf : ContDiffAt Real 1 f x₀) :
    exists (ε : Real) (hε : 0 < ε) (a r L K : Real>=0) (_ : 0 < r), forall (t₀ : Real), IsPicardLindelof (fun _ => f)
      (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, (by simp [le_of_lt hε])⟩ x₀ a r L K := by
  -- Obtain ball of radius `a` within the domain in which f is `K`-lipschitz
  obtain ⟨K, s, hs, hl⟩ := hf.exists_lipschitzOnWith
  obtain ⟨a, ha : 0 < a, has⟩ := Metric.mem_nhds_iff.mp hs
  set L := K * a + ‖f x₀‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  have hb (x : E) (hx : x in closedBall x₀ (a / 2)) : ‖f x‖ <= L := by
    rw [hL]
    calc
      ‖f x‖ <= ‖f x - f x₀‖ + ‖f x₀‖ := norm_le_norm_sub_add _ _
      _ <= K * ‖x - x₀‖ + ‖f x₀‖ := by
        gcongr
        apply hl.norm_sub_le _ (mem_of_mem_nhds hs)
        apply subset_trans _ has hx
exact closedBall_subset_ball half_lt_self ha-- this is where we need `a / 2`
      _ <= K * a + ‖f x₀‖ := by
        gcongr
        rw [← mem_closedBall_iff_norm]
        exact closedBall_subset_closedBall (half_le_self (le_of_lt ha)) hx
      _ <= L := le_add_of_nonneg_right zero_le_one
  let ε := a / L / 2 / 2
  have hε0 : 0 < ε := by positivity
  refine ⟨ε, hε0,
    .mk (a / 2) (half_pos ha).le, (.mk (a / 2) (half_pos ha).le) / 2,
.mk L hL0.le, K, half_pos half_pos ha, fun t₀ => ?_⟩
apply of_time_independent hb
hl.mono subset_trans (closedBall_subset_ball (half_lt_self ha)) has
  simp [ε, field]
  norm_num

end

/-! ## Existence of solutions to ODEs -/

open ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  {f : Real -> E -> E} {tmin tmax : Real} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : Real>=0}

/--
theorem `exists_eq_forall_mem_Icc_eq_picard` / 定理 `exists_eq_forall_mem_Icc_eq_picard`

English:
theorem exists_eq_forall_mem_Icc_eq_picard
  proof: by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨(FunSpace.next hf hx α).compProj, by simp, fun t ht => ?_⟩
  rw [FunSpace.compProj_apply]; rw [FunSpace.next_apply]; rw [hα]; rw [projIcc_of_mem _ ht]

中文:
定理 exists_eq_forall_mem_Icc_eq_picard
  证明: by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨(FunSpace.next hf hx α).compProj, by simp, fun t ht => ?_⟩
  rw [FunSpace.compProj_apply]; rw [FunSpace.next_apply]; rw [hα]; rw [projIcc_of_mem _ ht]

Depends on / 依赖: FunSpace, FunSpace.compProj_apply, FunSpace.exists_isFixedPt_next, FunSpace.next, FunSpace.next_apply, compProj, compProj_apply, exists_isFixedPt_next, next_apply, projIcc_of_mem
-/
theorem exists_eq_forall_mem_Icc_eq_picard
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r) :
    exists α : Real -> E, α t₀ = x ∧ forall t in Icc tmin tmax, α t = ODE.picard f t₀ x α t := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨(FunSpace.next hf hx α).compProj, by simp, fun t ht => ?_⟩
  rw [FunSpace.compProj_apply]; rw [FunSpace.next_apply]; rw [hα]; rw [projIcc_of_mem _ ht]

end IsPicardLindelof
