/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Normed.Group.ZeroAtInfty
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Algebra.UniformFilterBasis

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Tactic.MoveAdd


/-!
# Schwartz space

This file defines the Schwartz space. Usually, the Schwartz space is defined as the set of smooth
functions $f : ℝ^n → ℂ$ such that there exists $C_{αβ} > 0$ with $$|x^α ∂^β f(x)| < C_{αβ}$$ for
all $x ∈ ℝ^n$ and for all multiindices $α, β$.
In mathlib, we use a slightly different approach and define the Schwartz space as all
smooth functions `f : E → F`, where `E` and `F` are real normed vector spaces such that for all
natural numbers `k` and `n` we have uniform bounds `‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ < C`.
This approach completely avoids using partial derivatives as well as polynomials.
We construct the topology on the Schwartz space by a family of seminorms, which are the best
constants in the above estimates. The abstract theory of topological vector spaces developed in
`SeminormFamily.moduleFilterBasis` and `WithSeminorms.toLocallyConvexSpace` turns the
Schwartz space into a locally convex topological vector space.

## Main definitions

* `SchwartzMap`: The Schwartz space is the space of smooth functions such that all derivatives
  decay faster than any power of `‖x‖`.
* `SchwartzMap.seminorm`: The family of seminorms as described above
* `SchwartzMap.compCLM`: Composition with a function on the right as a continuous linear map
  `𝓢(E, F) →L[𝕜] 𝓢(D, F)`, provided that the function is temperate and grows polynomially near
  infinity
* `SchwartzMap.integralCLM`: Integration as a continuous linear map `𝓢(ℝ, F) →L[ℝ] F`

## Main statements

* `SchwartzMap.instIsUniformAddGroup` and `SchwartzMap.instLocallyConvexSpace`: The Schwartz space
  is a locally convex topological vector space.
* `SchwartzMap.one_add_le_sup_seminorm_apply`: For a Schwartz function `f` there is a uniform bound
  on `(1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖`.

## Implementation details

The implementation of the seminorms is taken almost literally from `ContinuousLinearMap.opNorm`.

## Notation

* `𝓢(E, F)`: The Schwartz space `SchwartzMap E F` localized in `SchwartzSpace`

## Tags

Schwartz space, tempered distributions
-/

@[expose] public noncomputable section

open scoped Nat NNReal ContDiff

variable {ι 𝕜 𝕜' D E F G H V : Type*}
variable [NormedAddCommGroup E] [NormedSpace Real E]
variable [NormedAddCommGroup F] [NormedSpace Real F]

variable (E F) in
/--
Definition of `SchwartzMap` / `SchwartzMap` 的定义

English:
structure SchwartzMap
  parameters: where
  axioms and operations (3):
    - toFun : E -> F
    - smooth' : ContDiff Real ∞ toFun
    - decay' : forall k n : Nat, exists C : Real, forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n toFun x‖ <= C

中文:
结构 SchwartzMap
  参数: where
  公理与运算 (3 个):
    - toFun : E -> F
    - smooth' : ContDiff 实数 ∞ toFun
    - decay' : 对任意 k n : 自然数, 存在 C : 实数, 对任意 x, ‖x‖ ^ k * ‖iteratedFDeriv 实数 n toFun x‖ <= C
-/
structure SchwartzMap where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : E -> F
  smooth' : ContDiff Real ∞ toFun
  decay' : forall k n : Nat, exists C : Real, forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n toFun x‖ <= C

/-- A function is a Schwartz function if it is smooth and all derivatives decay faster than
  any power of `‖x‖`. -/
scoped[SchwartzMap] notation "𝓢(" E ", " F ")" => SchwartzMap E F

namespace SchwartzMap

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike 𝓢(E, F) E F where
  body: f.toFun
  coe_injective f g h := by cases f; cases g; congr

中文:
实例 instFunLike
  签名: : FunLike 𝓢(E, F) E F where
  定义体: f.toFun
  coe_injective f g h := by cases f; cases g; congr

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike 𝓢(E, F) E F where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr

/--
theorem `decay` / 定理 `decay`

English:
theorem decay
  given: (f : 𝓢(E, F)) (k n : Nat)
  proof: by
  rcases f.decay' k n with ⟨C, hC⟩
  exact ⟨max C 1, by positivity, fun x => (hC x).trans (le_max_left _ _)⟩

中文:
定理 decay
  条件: (f : 𝓢(E, F)) (k n : 自然数)
  证明: by
  rcases f.decay' k n with ⟨C, hC⟩
  exact ⟨max C 1, by positivity, fun x => (hC x).trans (le_max_left _ _)⟩

Depends on / 依赖: f.decay, le_max_left
-/
theorem decay (f : 𝓢(E, F)) (k n : Nat) :
    exists C : Real, 0 < C ∧ forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= C := by
  rcases f.decay' k n with ⟨C, hC⟩
  exact ⟨max C 1, by positivity, fun x => (hC x).trans (le_max_left _ _)⟩

/-- Every Schwartz function is smooth. -/
@[fun_prop]
/--
theorem `smooth` / 定理 `smooth`

English:
theorem smooth
  given: (f : 𝓢(E, F)) (n : Nat∞)
  statement: ContDiff Real n f
  proof: f.smooth'.of_le (mod_cast le_top)

中文:
定理 smooth
  条件: (f : 𝓢(E, F)) (n : 自然数∞)
  结论: ContDiff 实数 n f
  证明: f.smooth'.of_le (mod_cast le_top)

Depends on / 依赖: f.smooth, le_top, mod_cast, of_le, smooth
-/
theorem smooth (f : 𝓢(E, F)) (n : Nat∞) : ContDiff Real n f :=
  f.smooth'.of_le (mod_cast le_top)

/-- Every Schwartz function is smooth at any point. -/
@[fun_prop]
/--
theorem `contDiffAt` / 定理 `contDiffAt`

English:
theorem contDiffAt
  given: (f : 𝓢(E, F)) (n : Nat∞) {x : E}
  statement: ContDiffAt Real n f x
  proof: (f.smooth n).contDiffAt

中文:
定理 contDiffAt
  条件: (f : 𝓢(E, F)) (n : 自然数∞) {x : E}
  结论: ContDiffAt 实数 n f x
  证明: (f.smooth n).contDiffAt

Depends on / 依赖: contDiffAt, f.smooth, smooth
-/
theorem contDiffAt (f : 𝓢(E, F)) (n : Nat∞) {x : E} : ContDiffAt Real n f x :=
  (f.smooth n).contDiffAt

/-- Every Schwartz function is continuous. -/
@[continuity, fun_prop]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (f : 𝓢(E, F))
  statement: Continuous f
  proof: (f.smooth 0).continuous

中文:
定理 continuous
  条件: (f : 𝓢(E, F))
  结论: Continuous f
  证明: (f.smooth 0).continuous
-/
protected theorem continuous (f : 𝓢(E, F)) : Continuous f :=
  (f.smooth 0).continuous

/--
Instance `instContinuousMapClass` / 实例 `instContinuousMapClass`

English:
instance instContinuousMapClass
  signature: : ContinuousMapClass 𝓢(E, F) E F where
  body: SchwartzMap.continuous

中文:
实例 instContinuousMapClass
  签名: : ContinuousMapClass 𝓢(E, F) E F where
  定义体: SchwartzMap.continuous

Depends on / 依赖: NormedGroup, NormedGroup.toSeminormedGroup, SchwartzMap, SchwartzMap.continuous, SeminormedGroup, continuous, toSeminormedGroup
-/
instance instContinuousMapClass : ContinuousMapClass 𝓢(E, F) E F where
  map_continuous := SchwartzMap.continuous

/-- Every Schwartz function is differentiable. -/
@[fun_prop]
/--
theorem `differentiable` / 定理 `differentiable`

English:
theorem differentiable
  given: (f : 𝓢(E, F))
  statement: Differentiable Real f
  proof: (f.smooth 1).differentiable one_ne_zero

中文:
定理 differentiable
  条件: (f : 𝓢(E, F))
  结论: Differentiable 实数 f
  证明: (f.smooth 1).differentiable one_ne_zero

Depends on / 依赖: NormedCommGroup, NormedCommGroup.toSeminormedCommGroup, toSeminormedCommGroup
-/
protected theorem differentiable (f : 𝓢(E, F)) : Differentiable Real f :=
  (f.smooth 1).differentiable one_ne_zero

/-- Every Schwartz function is differentiable at any point. -/
@[fun_prop]
/--
theorem `differentiableAt` / 定理 `differentiableAt`

English:
theorem differentiableAt
  given: (f : 𝓢(E, F)) {x : E}
  statement: DifferentiableAt Real f x
  proof: f.differentiable.differentiableAt

@[ext]

中文:
定理 differentiableAt
  条件: (f : 𝓢(E, F)) {x : E}
  结论: DifferentiableAt 实数 f x
  证明: f.differentiable.differentiableAt

@[ext]

Depends on / 依赖: SeminormedCommGroup, SeminormedCommGroup.toSeminormedGroup, toSeminormedGroup
-/
protected theorem differentiableAt (f : 𝓢(E, F)) {x : E} : DifferentiableAt Real f x :=
  f.differentiable.differentiableAt

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : 𝓢(E, F)} (h : 对任意 x, (f : E -> F) x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext, NormedCommGroup, NormedCommGroup.toNormedGroup, NormedGroup, toNormedGroup
-/
theorem ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x) : f = g :=
  DFunLike.ext f g h

section IsBigO

open Asymptotics Filter

variable (f : 𝓢(E, F))

/--
theorem `isBigO_cocompact_zpow_neg_nat` / 定理 `isBigO_cocompact_zpow_neg_nat`

English:
theorem isBigO_cocompact_zpow_neg_nat
  given: (k : Nat)
  proof: by
  obtain ⟨d, _, hd'⟩ := f.decay k 0
  simp only [norm_iteratedFDeriv_zero] at hd'
  simp_rw [Asymptotics.IsBigO, Asymptotics.IsBigOWith]
  refine ⟨d, Filter.Eventually.filter_mono Filter.cocompact_le_cofinite ?_⟩
  refine (Filter.eventually_cofinite_ne 0).mono fun x hx => ?_
  rw [Real.norm_of_no

中文:
定理 isBigO_cocompact_zpow_neg_nat
  条件: (k : 自然数)
  证明: by
  obtain ⟨d, _, hd'⟩ := f.decay k 0
  simp only [norm_iteratedFDeriv_zero] at hd'
  simp_rw [Asymptotics.IsBigO, Asymptotics.IsBigOWith]
  refine ⟨d, Filter.Eventually.filter_mono Filter.cocompact_le_cofinite ?_⟩
  refine (Filter.eventually_cofinite_ne 0).mono fun x hx => ?_
  rw [Real.norm_of_no

Depends on / 依赖: Asymptotics, Asymptotics.IsBigO, Asymptotics.IsBigOWith, Eventually, Filter, Filter.Eventually.filter_mono, Filter.cocompact_le_cofinite, Filter.eventually_cofinite_ne, IsBigO, IsBigOWith, Real.norm_of_nonneg, cocompact_le_cofinite, div_eq_mul_inv, eventually_cofinite_ne, f.decay, filter_mono, norm_iteratedFDeriv_zero, norm_of_nonneg, simp_rw, zpow_neg
-/
theorem isBigO_cocompact_zpow_neg_nat (k : Nat) :
    f =O[cocompact E] (‖·‖ ^ (-k : Int)) := by
  obtain ⟨d, _, hd'⟩ := f.decay k 0
  simp only [norm_iteratedFDeriv_zero] at hd'
  simp_rw [Asymptotics.IsBigO, Asymptotics.IsBigOWith]
  refine ⟨d, Filter.Eventually.filter_mono Filter.cocompact_le_cofinite ?_⟩
  refine (Filter.eventually_cofinite_ne 0).mono fun x hx => ?_
  rw [Real.norm_of_nonneg (by positivity)]; rw [zpow_neg]; rw [← div_eq_mul_inv]; rw [le_div_iff₀' (by positivity)]
  exact hd' x

/--
theorem `isBigO_cocompact_rpow` / 定理 `isBigO_cocompact_rpow`

English:
theorem isBigO_cocompact_rpow
  given: [ProperSpace E] (s : Real)
  proof: by
  let k := ⌈-s⌉₊
  have hk : -(k : Real) <= s := neg_le.mp (Nat.le_ceil (-s))
  refine (isBigO_cocompact_zpow_neg_nat f k).trans ?_
  suffices (fun x : Real => x ^ (-k : Int)) =O[atTop] fun x : Real => x ^ s
    from this.comp_tendsto tendsto_norm_cocompact_atTop
  simp_rw [Asymptotics.IsBigO, As

中文:
定理 isBigO_cocompact_rpow
  条件: [命题erSpace E] (s : 实数)
  证明: by
  let k := ⌈-s⌉₊
  have hk : -(k : Real) <= s := neg_le.mp (Nat.le_ceil (-s))
  refine (isBigO_cocompact_zpow_neg_nat f k).trans ?_
  suffices (fun x : Real => x ^ (-k : Int)) =O[atTop] fun x : Real => x ^ s
    from this.comp_tendsto tendsto_norm_cocompact_atTop
  simp_rw [Asymptotics.IsBigO, As

Depends on / 依赖: Asymptotics, Asymptotics.IsBigO, Asymptotics.IsBigOWith, Filter, Filter.eventually_ge_atTop, IsBigO, IsBigOWith, Nat.le_ceil, Real.norm_of_nonneg, Real.rpow_intCast, comp_tendsto, eventually_ge_atTop, isBigO_cocompact_zpow_neg_nat, le_ceil, neg_le, neg_le.mp, norm_of_nonneg, one_mul, rpow_intCast, simp_rw
-/
theorem isBigO_cocompact_rpow [ProperSpace E] (s : Real) :
    f =O[cocompact E] (‖·‖ ^ s) := by
  let k := ⌈-s⌉₊
  have hk : -(k : Real) <= s := neg_le.mp (Nat.le_ceil (-s))
  refine (isBigO_cocompact_zpow_neg_nat f k).trans ?_
  suffices (fun x : Real => x ^ (-k : Int)) =O[atTop] fun x : Real => x ^ s
    from this.comp_tendsto tendsto_norm_cocompact_atTop
  simp_rw [Asymptotics.IsBigO, Asymptotics.IsBigOWith]
  refine ⟨1, (Filter.eventually_ge_atTop 1).mono fun x hx => ?_⟩
  rw [one_mul]; rw [Real.norm_of_nonneg (by positivity)]; rw [Real.norm_of_nonneg (by positivity)]; rw [← Real.rpow_intCast]; rw [Int.cast_neg]; rw [Int.cast_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hx hk

/--
theorem `isBigO_cocompact_zpow` / 定理 `isBigO_cocompact_zpow`

English:
theorem isBigO_cocompact_zpow
  given: [ProperSpace E] (k : Int)
  proof: by
  simpa only [Real.rpow_intCast] using isBigO_cocompact_rpow f k

中文:
定理 isBigO_cocompact_zpow
  条件: [命题erSpace E] (k : 整数)
  证明: by
  simpa only [Real.rpow_intCast] using isBigO_cocompact_rpow f k

Depends on / 依赖: Real.rpow_intCast, isBigO_cocompact_rpow, rpow_intCast
-/
theorem isBigO_cocompact_zpow [ProperSpace E] (k : Int) :
    f =O[cocompact E] (‖·‖ ^ k) := by
  simpa only [Real.rpow_intCast] using isBigO_cocompact_rpow f k

end IsBigO

open Filter Topology in
/--
theorem `tendsto_cocompact` / 定理 `tendsto_cocompact`

English:
theorem tendsto_cocompact
  given: [ProperSpace E] (f : 𝓢(E, F))
  proof: by
  apply (isBigO_cocompact_rpow f (-1)).trans_tendsto
  simp_rw [Real.rpow_neg_one]
  exact tendsto_norm_cocompact_atTop.inv_tendsto_atTop

中文:
定理 tendsto_cocompact
  条件: [命题erSpace E] (f : 𝓢(E, F))
  证明: by
  apply (isBigO_cocompact_rpow f (-1)).trans_tendsto
  simp_rw [Real.rpow_neg_one]
  exact tendsto_norm_cocompact_atTop.inv_tendsto_atTop

Depends on / 依赖: Real.rpow_neg_one, inv_tendsto_atTop, isBigO_cocompact_rpow, rpow_neg_one, simp_rw, tendsto_norm_cocompact_atTop, tendsto_norm_cocompact_atTop.inv_tendsto_atTop, trans_tendsto
-/
theorem tendsto_cocompact [ProperSpace E] (f : 𝓢(E, F)) :
    Tendsto f (cocompact E) (𝓝 0) := by
  apply (isBigO_cocompact_rpow f (-1)).trans_tendsto
  simp_rw [Real.rpow_neg_one]
  exact tendsto_norm_cocompact_atTop.inv_tendsto_atTop

section Aux

/--
theorem `bounds_nonempty` / 定理 `bounds_nonempty`

English:
theorem bounds_nonempty
  given: (k n : Nat) (f : 𝓢(E, F))
  proof: let ⟨M, hMp, hMb⟩ := f.decay k n
  ⟨M, le_of_lt hMp, hMb⟩

中文:
定理 bounds_nonempty
  条件: (k n : 自然数) (f : 𝓢(E, F))
  证明: let ⟨M, hMp, hMb⟩ := f.decay k n
  ⟨M, le_of_lt hMp, hMb⟩
-/
private theorem bounds_nonempty (k n : Nat) (f : 𝓢(E, F)) :
    exists c : Real, c in { c : Real | 0 <= c ∧ forall x : E, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= c } :=
  let ⟨M, hMp, hMb⟩ := f.decay k n
  ⟨M, le_of_lt hMp, hMb⟩

/--
theorem `bounds_bddBelow` / 定理 `bounds_bddBelow`

English:
theorem bounds_bddBelow
  given: (k n : Nat) (f : 𝓢(E, F))
  proof: ⟨0, fun _ ⟨hn, _⟩ => hn⟩

中文:
定理 bounds_bddBelow
  条件: (k n : 自然数) (f : 𝓢(E, F))
  证明: ⟨0, fun _ ⟨hn, _⟩ => hn⟩
-/
private theorem bounds_bddBelow (k n : Nat) (f : 𝓢(E, F)) :
    BddBelow { c | 0 <= c ∧ forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= c } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

/--
theorem `decay_add_le_aux` / 定理 `decay_add_le_aux`

English:
theorem decay_add_le_aux
  given: (k n : Nat) (f g : 𝓢(E, F)) (x : E)
  proof: by
  rw [← mul_add]
  gcongr _ * ?_
  rw [iteratedFDeriv_add_apply (f.smooth _).contDiffAt (g.smooth _).contDiffAt]
  exact norm_add_le _ _

中文:
定理 decay_add_le_aux
  条件: (k n : 自然数) (f g : 𝓢(E, F)) (x : E)
  证明: by
  rw [← mul_add]
  gcongr _ * ?_
  rw [iteratedFDeriv_add_apply (f.smooth _).contDiffAt (g.smooth _).contDiffAt]
  exact norm_add_le _ _
-/
private theorem decay_add_le_aux (k n : Nat) (f g : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv Real n ((f : E -> F) + (g : E -> F)) x‖ <=
      ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ + ‖x‖ ^ k * ‖iteratedFDeriv Real n g x‖ := by
  rw [← mul_add]
  gcongr _ * ?_
  rw [iteratedFDeriv_add_apply (f.smooth _).contDiffAt (g.smooth _).contDiffAt]
  exact norm_add_le _ _

/--
theorem `decay_neg_aux` / 定理 `decay_neg_aux`

English:
theorem decay_neg_aux
  given: (k n : Nat) (f : 𝓢(E, F)) (x : E)
  proof: by
  rw [iteratedFDeriv_neg_apply]; rw [norm_neg]

中文:
定理 decay_neg_aux
  条件: (k n : 自然数) (f : 𝓢(E, F)) (x : E)
  证明: by
  rw [iteratedFDeriv_neg_apply]; rw [norm_neg]
-/
private theorem decay_neg_aux (k n : Nat) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv Real n (-f : E -> F) x‖ = ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ := by
  rw [iteratedFDeriv_neg_apply]; rw [norm_neg]

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass Real 𝕜 F] in
/--
theorem `decay_smul_aux` / 定理 `decay_smul_aux`

English:
theorem decay_smul_aux
  given: (k n : Nat) (f : 𝓢(E, F)) (c : 𝕜) (x : E)
  proof: by
  rw [mul_comm ‖c‖]; rw [mul_assoc]; rw [iteratedFDeriv_const_smul_apply (f.smooth _).contDiffAt]; rw [norm_smul c (iteratedFDeriv Real n (⇑f) x)]

中文:
定理 decay_smul_aux
  条件: (k n : 自然数) (f : 𝓢(E, F)) (c : 𝕜) (x : E)
  证明: by
  rw [mul_comm ‖c‖]; rw [mul_assoc]; rw [iteratedFDeriv_const_smul_apply (f.smooth _).contDiffAt]; rw [norm_smul c (iteratedFDeriv Real n (⇑f) x)]
-/
private theorem decay_smul_aux (k n : Nat) (f : 𝓢(E, F)) (c : 𝕜) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv Real n (c • (f : E -> F)) x‖ =
      ‖c‖ * ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ := by
  rw [mul_comm ‖c‖]; rw [mul_assoc]; rw [iteratedFDeriv_const_smul_apply (f.smooth _).contDiffAt]; rw [norm_smul c (iteratedFDeriv Real n (⇑f) x)]

end Aux

section SeminormAux

/--
Definition of `protected` / `protected` 的定义

English:
definition protected
  signature: def seminormAux (k n : Nat) (f : 𝓢(E, F))
  body: sInf { c | 0 <= c ∧ forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= c }

中文:
定义 protected
  签名: def seminormAux (k n : 自然数) (f : 𝓢(E, F))
  定义体: sInf { c | 0 <= c ∧ forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= c }
-/
private protected def seminormAux (k n : Nat) (f : 𝓢(E, F)) : Real :=
  sInf { c | 0 <= c ∧ forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= c }

/--
theorem `seminormAux_nonneg` / 定理 `seminormAux_nonneg`

English:
theorem seminormAux_nonneg
  given: (k n : Nat) (f : 𝓢(E, F))
  statement: 0 <= f.seminormAux k n
  proof: le_csInf (bounds_nonempty k n f) fun _ ⟨hx, _⟩ => hx

中文:
定理 seminormAux_nonneg
  条件: (k n : 自然数) (f : 𝓢(E, F))
  结论: 0 <= f.seminormAux k n
  证明: le_csInf (bounds_nonempty k n f) fun _ ⟨hx, _⟩ => hx
-/
private theorem seminormAux_nonneg (k n : Nat) (f : 𝓢(E, F)) : 0 <= f.seminormAux k n :=
  le_csInf (bounds_nonempty k n f) fun _ ⟨hx, _⟩ => hx

/--
theorem `le_seminormAux` / 定理 `le_seminormAux`

English:
theorem le_seminormAux
  given: (k n : Nat) (f : 𝓢(E, F)) (x : E)
  proof: le_csInf (bounds_nonempty k n f) fun _ ⟨_, h⟩ => h x

中文:
定理 le_seminormAux
  条件: (k n : 自然数) (f : 𝓢(E, F)) (x : E)
  证明: le_csInf (bounds_nonempty k n f) fun _ ⟨_, h⟩ => h x
-/
private theorem le_seminormAux (k n : Nat) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv Real n (⇑f) x‖ <= f.seminormAux k n :=
  le_csInf (bounds_nonempty k n f) fun _ ⟨_, h⟩ => h x

/--
theorem `seminormAux_le_bound` / 定理 `seminormAux_le_bound`

English:
theorem seminormAux_le_bound
  statement: (k n : Nat) (f : 𝓢(E, F)) {M : Real} (hMp : 0 <= M)
  proof: csInf_le (bounds_bddBelow k n f) ⟨hMp, hM⟩

中文:
定理 seminormAux_le_bound
  结论: (k n : 自然数) (f : 𝓢(E, F)) {M : 实数} (hMp : 0 <= M)
  证明: csInf_le (bounds_bddBelow k n f) ⟨hMp, hM⟩
-/
private theorem seminormAux_le_bound (k n : Nat) (f : 𝓢(E, F)) {M : Real} (hMp : 0 <= M)
    (hM : forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= M) : f.seminormAux k n <= M :=
  csInf_le (bounds_bddBelow k n f) ⟨hMp, hM⟩

end SeminormAux

/-! ### Algebraic properties -/

section SMul

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass Real 𝕜 F] [NormedField 𝕜'] [NormedSpace 𝕜' F]
  [SMulCommClass Real 𝕜' F]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul 𝕜 𝓢(E, F)
  body: ⟨fun c f =>
    { toFun := c • (f : E -> F)
      smooth' := by exact (f.smooth _).const_smul c
      decay' k n := by
        use f.seminormAux k n * ‖c‖
        intro x
        calc
          ‖x‖ ^ k * ‖iteratedFDeriv Real n (c • ⇑f) x‖ = ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ * ‖c‖ := by
         

中文:
实例 instSMul
  签名: : SMul 𝕜 𝓢(E, F)
  定义体: ⟨fun c f =>
    { toFun := c • (f : E -> F)
      smooth' := by exact (f.smooth _).const_smul c
      decay' k n := by
        use f.seminormAux k n * ‖c‖
        intro x
        calc
          ‖x‖ ^ k * ‖iteratedFDeriv Real n (c • ⇑f) x‖ = ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ * ‖c‖ := by
         

Depends on / 依赖: SchwartzMap, SchwartzMap.seminormAux, const_smul, decay_smul_aux, f.le_seminormAux, f.seminormAux, f.smooth, iteratedFDeriv, le_seminormAux, mul_assoc, mul_comm, seminormAux, smooth
-/
instance instSMul : SMul 𝕜 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • (f : E -> F)
      smooth' := by exact (f.smooth _).const_smul c
      decay' k n := by
        use f.seminormAux k n * ‖c‖
        intro x
        calc
          ‖x‖ ^ k * ‖iteratedFDeriv Real n (c • ⇑f) x‖ = ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ * ‖c‖ := by
            rw [mul_comm _ ‖c‖]; rw [← mul_assoc]
            exact decay_smul_aux k n f c x
          _ <= SchwartzMap.seminormAux k n f * ‖c‖ := by
            gcongr
            apply f.le_seminormAux }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply 𝕜 𝓢(E, F) E F
  body: rfl

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

中文:
实例 :
  签名: IsSMulApply 𝕜 𝓢(E, F) E F
  定义体: rfl

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply
-/
instance : IsSMulApply 𝕜 𝓢(E, F) E F where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' F]
  body: FunLike.isScalarTower

中文:
实例 instIsScalarTower
  签名: [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' F]
  定义体: FunLike.isScalarTower

Depends on / 依赖: FunLike, FunLike.isScalarTower, isScalarTower
-/
instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' F] : IsScalarTower 𝕜 𝕜' 𝓢(E, F) :=
  FunLike.isScalarTower

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMulCommClass 𝕜 𝕜' F]
  body: FunLike.smulCommClass

中文:
实例 instSMulCommClass
  签名: [SMulCommClass 𝕜 𝕜' F]
  定义体: FunLike.smulCommClass

Depends on / 依赖: FunLike, FunLike.smulCommClass, smulCommClass
-/
instance instSMulCommClass [SMulCommClass 𝕜 𝕜' F] : SMulCommClass 𝕜 𝕜' 𝓢(E, F) :=
  FunLike.smulCommClass

/--
theorem `seminormAux_smul_le` / 定理 `seminormAux_smul_le`

English:
theorem seminormAux_smul_le
  given: (k n : Nat) (c : 𝕜) (f : 𝓢(E, F))
  proof: by
  refine (c • f).seminormAux_le_bound k n (mul_nonneg (norm_nonneg _) (seminormAux_nonneg _ _ _))
      fun x => (decay_smul_aux k n f c x).trans_le ?_
  rw [mul_assoc]
  gcongr
  exact f.le_seminormAux k n x

中文:
定理 seminormAux_smul_le
  条件: (k n : 自然数) (c : 𝕜) (f : 𝓢(E, F))
  证明: by
  refine (c • f).seminormAux_le_bound k n (mul_nonneg (norm_nonneg _) (seminormAux_nonneg _ _ _))
      fun x => (decay_smul_aux k n f c x).trans_le ?_
  rw [mul_assoc]
  gcongr
  exact f.le_seminormAux k n x
-/
private theorem seminormAux_smul_le (k n : Nat) (c : 𝕜) (f : 𝓢(E, F)) :
    (c • f).seminormAux k n <= ‖c‖ * f.seminormAux k n := by
  refine (c • f).seminormAux_le_bound k n (mul_nonneg (norm_nonneg _) (seminormAux_nonneg _ _ _))
      fun x => (decay_smul_aux k n f c x).trans_le ?_
  rw [mul_assoc]
  gcongr
  exact f.le_seminormAux k n x

/--
Instance `instNSMul` / 实例 `instNSMul`

English:
instance instNSMul
  signature: : SMul Nat 𝓢(E, F)
  body: ⟨fun c f =>
    { toFun := c • (f : E -> F)
      smooth' := by exact (f.smooth _).const_smul c
      decay' := by simpa [← Nat.cast_smul_eq_nsmul Real] using! ((c : Real) • f).decay' }⟩

中文:
实例 instNSMul
  签名: : SMul 自然数 𝓢(E, F)
  定义体: ⟨fun c f =>
    { toFun := c • (f : E -> F)
      smooth' := by exact (f.smooth _).const_smul c
      decay' := by simpa [← Nat.cast_smul_eq_nsmul Real] using! ((c : Real) • f).decay' }⟩

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, const_smul, f.smooth, smooth
-/
instance instNSMul : SMul Nat 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • (f : E -> F)
      smooth' := by exact (f.smooth _).const_smul c
      decay' := by simpa [← Nat.cast_smul_eq_nsmul Real] using! ((c : Real) • f).decay' }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply Nat 𝓢(E, F) E F
  body: rfl

中文:
实例 :
  签名: IsSMulApply 自然数 𝓢(E, F) E F
  定义体: rfl
-/
instance : IsSMulApply Nat 𝓢(E, F) E F where
  smul_apply _ _ _ := rfl

/--
Instance `instZSMul` / 实例 `instZSMul`

English:
instance instZSMul
  signature: : SMul Int 𝓢(E, F)
  body: ⟨fun c f =>
    { toFun := c • (f : E -> F)
      smooth' := by exact (f.smooth _).const_smul c
      decay' := by simpa [← Int.cast_smul_eq_zsmul Real] using! ((c : Real) • f).decay' }⟩

中文:
实例 instZSMul
  签名: : SMul 整数 𝓢(E, F)
  定义体: ⟨fun c f =>
    { toFun := c • (f : E -> F)
      smooth' := by exact (f.smooth _).const_smul c
      decay' := by simpa [← Int.cast_smul_eq_zsmul Real] using! ((c : Real) • f).decay' }⟩

Depends on / 依赖: Int.cast_smul_eq_zsmul, cast_smul_eq_zsmul, const_smul, f.smooth, smooth
-/
instance instZSMul : SMul Int 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • (f : E -> F)
      smooth' := by exact (f.smooth _).const_smul c
      decay' := by simpa [← Int.cast_smul_eq_zsmul Real] using! ((c : Real) • f).decay' }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply Int 𝓢(E, F) E F
  body: rfl

中文:
实例 :
  签名: IsSMulApply 整数 𝓢(E, F) E F
  定义体: rfl
-/
instance : IsSMulApply Int 𝓢(E, F) E F where
  smul_apply _ _ _ := rfl

end SMul

section Zero

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero 𝓢(E, F)
  body: ⟨{ toFun := fun _ => 0
      smooth' := by exact contDiff_const
      decay' := fun _ _ => ⟨1, fun _ => by simp⟩ }⟩

中文:
实例 instZero
  签名: : Zero 𝓢(E, F)
  定义体: ⟨{ toFun := fun _ => 0
      smooth' := by exact contDiff_const
      decay' := fun _ _ => ⟨1, fun _ => by simp⟩ }⟩

Depends on / 依赖: contDiff_const, smooth
-/
instance instZero : Zero 𝓢(E, F) :=
  ⟨{ toFun := fun _ => 0
      smooth' := by exact contDiff_const
      decay' := fun _ _ => ⟨1, fun _ => by simp⟩ }⟩

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited 𝓢(E, F)
  body: ⟨0⟩

中文:
实例 instInhabited
  签名: : Inhabited 𝓢(E, F)
  定义体: ⟨0⟩
-/
instance instInhabited : Inhabited 𝓢(E, F) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply 𝓢(E, F) E F
  body: rfl

@[deprecated (since := "2026-06-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-10")] alias coeFn_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

中文:
实例 :
  签名: IsZeroApply 𝓢(E, F) E F
  定义体: rfl

@[deprecated (since := "2026-06-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-10")] alias coeFn_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply
-/
instance : IsZeroApply 𝓢(E, F) E F where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-10")] alias coeFn_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

/--
theorem `seminormAux_zero` / 定理 `seminormAux_zero`

English:
theorem seminormAux_zero
  given: (k n : Nat)
  statement: (0 : 𝓢(E, F)).seminormAux k n = 0
  proof: le_antisymm (seminormAux_le_bound k n _ rfl.le fun _ => by simp [FunLike.coe_zero])
    (seminormAux_nonneg _ _ _)

中文:
定理 seminormAux_zero
  条件: (k n : 自然数)
  结论: (0 : 𝓢(E, F)).seminormAux k n = 0
  证明: le_antisymm (seminormAux_le_bound k n _ rfl.le fun _ => by simp [FunLike.coe_zero])
    (seminormAux_nonneg _ _ _)
-/
private theorem seminormAux_zero (k n : Nat) : (0 : 𝓢(E, F)).seminormAux k n = 0 :=
  le_antisymm (seminormAux_le_bound k n _ rfl.le fun _ => by simp [FunLike.coe_zero])
    (seminormAux_nonneg _ _ _)

end Zero

section Neg

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg 𝓢(E, F)
  body: ⟨fun f =>
    ⟨-f, by exact (f.smooth _).neg, fun k n => by
      use f.seminormAux k n
      intro x
      grw [f.decay_neg_aux k n x, f.le_seminormAux k n x]⟩⟩

中文:
实例 instNeg
  签名: : Neg 𝓢(E, F)
  定义体: ⟨fun f =>
    ⟨-f, by exact (f.smooth _).neg, fun k n => by
      use f.seminormAux k n
      intro x
      grw [f.decay_neg_aux k n x, f.le_seminormAux k n x]⟩⟩

Depends on / 依赖: decay_neg_aux, f.decay_neg_aux, f.le_seminormAux, f.seminormAux, f.smooth, le_seminormAux, seminormAux, smooth
-/
instance instNeg : Neg 𝓢(E, F) :=
  ⟨fun f =>
    ⟨-f, by exact (f.smooth _).neg, fun k n => by
      use f.seminormAux k n
      intro x
      grw [f.decay_neg_aux k n x, f.le_seminormAux k n x]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNegApply 𝓢(E, F) E F
  body: rfl

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply

中文:
实例 :
  签名: IsNegApply 𝓢(E, F) E F
  定义体: rfl

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply
-/
instance : IsNegApply 𝓢(E, F) E F where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply

end Neg

section Add

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add 𝓢(E, F)
  body: ⟨fun f g =>
    ⟨f + g, by exact (f.smooth _).add (g.smooth _), fun k n => by
      use f.seminormAux k n + g.seminormAux k n
      intro x
      grw [decay_add_le_aux k n f g x, f.le_seminormAux k n x, g.le_seminormAux k n x]⟩⟩

中文:
实例 instAdd
  签名: : Add 𝓢(E, F)
  定义体: ⟨fun f g =>
    ⟨f + g, by exact (f.smooth _).add (g.smooth _), fun k n => by
      use f.seminormAux k n + g.seminormAux k n
      intro x
      grw [decay_add_le_aux k n f g x, f.le_seminormAux k n x, g.le_seminormAux k n x]⟩⟩

Depends on / 依赖: decay_add_le_aux, f.le_seminormAux, f.seminormAux, f.smooth, g.le_seminormAux, g.seminormAux, g.smooth, le_seminormAux, seminormAux, smooth
-/
instance instAdd : Add 𝓢(E, F) :=
  ⟨fun f g =>
    ⟨f + g, by exact (f.smooth _).add (g.smooth _), fun k n => by
      use f.seminormAux k n + g.seminormAux k n
      intro x
      grw [decay_add_le_aux k n f g x, f.le_seminormAux k n x, g.le_seminormAux k n x]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply 𝓢(E, F) E F
  body: rfl

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply

中文:
实例 :
  签名: IsAddApply 𝓢(E, F) E F
  定义体: rfl

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply
-/
instance : IsAddApply 𝓢(E, F) E F where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply

/--
theorem `seminormAux_add_le` / 定理 `seminormAux_add_le`

English:
theorem seminormAux_add_le
  given: (k n : Nat) (f g : 𝓢(E, F))
  proof: (f + g).seminormAux_le_bound k n
    (add_nonneg (seminormAux_nonneg _ _ _) (seminormAux_nonneg _ _ _)) fun x =>
(decay_add_le_aux k n f g x).trans
      add_le_add (f.le_seminormAux k n x) (g.le_seminormAux k n x)

中文:
定理 seminormAux_add_le
  条件: (k n : 自然数) (f g : 𝓢(E, F))
  证明: (f + g).seminormAux_le_bound k n
    (add_nonneg (seminormAux_nonneg _ _ _) (seminormAux_nonneg _ _ _)) fun x =>
(decay_add_le_aux k n f g x).trans
      add_le_add (f.le_seminormAux k n x) (g.le_seminormAux k n x)
-/
private theorem seminormAux_add_le (k n : Nat) (f g : 𝓢(E, F)) :
    (f + g).seminormAux k n <= f.seminormAux k n + g.seminormAux k n :=
  (f + g).seminormAux_le_bound k n
    (add_nonneg (seminormAux_nonneg _ _ _) (seminormAux_nonneg _ _ _)) fun x =>
(decay_add_le_aux k n f g x).trans
      add_le_add (f.le_seminormAux k n x) (g.le_seminormAux k n x)

end Add

section Sub

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub 𝓢(E, F)
  body: ⟨fun f g =>
    ⟨f - g, by exact (f.smooth _).sub (g.smooth _), by
      intro k n
      refine ⟨f.seminormAux k n + g.seminormAux k n, fun x => ?_⟩
      grw [← f.le_seminormAux k n x, ← g.le_seminormAux k n x]
      rw [sub_eq_add_neg]
      rw [← decay_neg_aux k n g x]
      exact decay_add_le_au

中文:
实例 instSub
  签名: : Sub 𝓢(E, F)
  定义体: ⟨fun f g =>
    ⟨f - g, by exact (f.smooth _).sub (g.smooth _), by
      intro k n
      refine ⟨f.seminormAux k n + g.seminormAux k n, fun x => ?_⟩
      grw [← f.le_seminormAux k n x, ← g.le_seminormAux k n x]
      rw [sub_eq_add_neg]
      rw [← decay_neg_aux k n g x]
      exact decay_add_le_au

Depends on / 依赖: decay_add_le_aux, decay_neg_aux, f.le_seminormAux, f.seminormAux, f.smooth, g.le_seminormAux, g.seminormAux, g.smooth, le_seminormAux, seminormAux, smooth, sub_eq_add_neg
-/
instance instSub : Sub 𝓢(E, F) :=
  ⟨fun f g =>
    ⟨f - g, by exact (f.smooth _).sub (g.smooth _), by
      intro k n
      refine ⟨f.seminormAux k n + g.seminormAux k n, fun x => ?_⟩
      grw [← f.le_seminormAux k n x, ← g.le_seminormAux k n x]
      rw [sub_eq_add_neg]
      rw [← decay_neg_aux k n g x]
      exact decay_add_le_aux k n f (-g) x⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSubApply 𝓢(E, F) E F
  body: rfl

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply

中文:
实例 :
  签名: IsSubApply 𝓢(E, F) E F
  定义体: rfl

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply
-/
instance : IsSubApply 𝓢(E, F) E F where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply

end Sub

section AddCommGroup

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup 𝓢(E, F)
  body: fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-06-10")] protected alias sum_apply := sum_apply

中文:
实例 instAddCommGroup
  签名: : AddCommGroup 𝓢(E, F)
  定义体: fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-06-10")] protected alias sum_apply := sum_apply

Depends on / 依赖: FunLike, FunLike.addCommGroup, addCommGroup, fast_instance
-/
instance instAddCommGroup : AddCommGroup 𝓢(E, F) := fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-06-10")] protected alias sum_apply := sum_apply

variable (E F)

@[deprecated (since := "2026-06-10")] alias coeHom := FunLike.coeAddMonoidHom

variable {E F}

@[deprecated (since := "2026-06-10")] alias coe_coeHom := FunLike.coe_coeAddMonoidHom

@[deprecated (since := "2026-06-10")] alias coeHom_injective := FunLike.coeAddMonoidHom_injective

end AddCommGroup

section Module

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass Real 𝕜 F]

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: : Module 𝕜 𝓢(E, F)
  body: fast_instance% FunLike.module

中文:
实例 instModule
  签名: : Module 𝕜 𝓢(E, F)
  定义体: fast_instance% FunLike.module

Depends on / 依赖: FunLike, FunLike.module, fast_instance, module
-/
instance instModule : Module 𝕜 𝓢(E, F) := fast_instance% FunLike.module

end Module

section Seminorms

/-! ### Seminorms on Schwartz space -/


variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass Real 𝕜 F]
variable (𝕜)

/-- The seminorms of the Schwartz space given by the best constants in the definition of
`𝓢(E, F)`. -/
@[no_expose]
/--
Definition of `seminorm` / `seminorm` 的定义

English:
definition seminorm
  signature: (k n : Nat)
  body: Seminorm.ofSMulLE (SchwartzMap.seminormAux k n) (seminormAux_zero k n) (seminormAux_add_le k n)
    (seminormAux_smul_le k n)

中文:
定义 seminorm
  签名: (k n : 自然数)
  定义体: Seminorm.ofSMulLE (SchwartzMap.seminormAux k n) (seminormAux_zero k n) (seminormAux_add_le k n)
    (seminormAux_smul_le k n)
-/
protected def seminorm (k n : Nat) : Seminorm 𝕜 𝓢(E, F) :=
  Seminorm.ofSMulLE (SchwartzMap.seminormAux k n) (seminormAux_zero k n) (seminormAux_add_le k n)
    (seminormAux_smul_le k n)

/--
theorem `seminorm_apply` / 定理 `seminorm_apply`

English:
theorem seminorm_apply
  given: {k n : Nat} (f : 𝓢(E, F))
  statement: SchwartzMap.seminorm 𝕜 k n f =
  proof: by rfl

中文:
定理 seminorm_apply
  条件: {k n : 自然数} (f : 𝓢(E, F))
  结论: SchwartzMap.seminorm 𝕜 k n f =
  证明: by rfl
-/
theorem seminorm_apply {k n : Nat} (f : 𝓢(E, F)) : SchwartzMap.seminorm 𝕜 k n f =
    sInf { c | 0 <= c ∧ forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= c } := by rfl

/--
theorem `seminorm_le_bound` / 定理 `seminorm_le_bound`

English:
theorem seminorm_le_bound
  statement: (k n : Nat) (f : 𝓢(E, F)) {M : Real} (hMp : 0 <= M)
  proof: f.seminormAux_le_bound k n hMp hM

中文:
定理 seminorm_le_bound
  结论: (k n : 自然数) (f : 𝓢(E, F)) {M : 实数} (hMp : 0 <= M)
  证明: f.seminormAux_le_bound k n hMp hM

Depends on / 依赖: f.seminormAux_le_bound, seminormAux_le_bound
-/
theorem seminorm_le_bound (k n : Nat) (f : 𝓢(E, F)) {M : Real} (hMp : 0 <= M)
    (hM : forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= M) : SchwartzMap.seminorm 𝕜 k n f <= M :=
  f.seminormAux_le_bound k n hMp hM

/--
theorem `seminorm_le_bound'` / 定理 `seminorm_le_bound'`

English:
theorem seminorm_le_bound'
  statement: (k n : Nat) (f : 𝓢(Real, F)) {M : Real} (hMp : 0 <= M)
  proof: by
  refine seminorm_le_bound 𝕜 k n f hMp ?_
  simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]

中文:
定理 seminorm_le_bound'
  结论: (k n : 自然数) (f : 𝓢(实数, F)) {M : 实数} (hMp : 0 <= M)
  证明: by
  refine seminorm_le_bound 𝕜 k n f hMp ?_
  simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]

Depends on / 依赖: Real.norm_eq_abs, norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, seminorm_le_bound
-/
theorem seminorm_le_bound' (k n : Nat) (f : 𝓢(Real, F)) {M : Real} (hMp : 0 <= M)
    (hM : forall x, |x| ^ k * ‖iteratedDeriv n f x‖ <= M) : SchwartzMap.seminorm 𝕜 k n f <= M := by
  refine seminorm_le_bound 𝕜 k n f hMp ?_
  simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]

/--
theorem `le_seminorm` / 定理 `le_seminorm`

English:
theorem le_seminorm
  given: (k n : Nat) (f : 𝓢(E, F)) (x : E)
  proof: f.le_seminormAux k n x

中文:
定理 le_seminorm
  条件: (k n : 自然数) (f : 𝓢(E, F)) (x : E)
  证明: f.le_seminormAux k n x

Depends on / 依赖: f.le_seminormAux, le_seminormAux
-/
theorem le_seminorm (k n : Nat) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ <= SchwartzMap.seminorm 𝕜 k n f :=
  f.le_seminormAux k n x

/--
theorem `le_seminorm'` / 定理 `le_seminorm'`

English:
theorem le_seminorm'
  given: (k n : Nat) (f : 𝓢(Real, F)) (x : Real)
  proof: by
  have := le_seminorm 𝕜 k n f x
  rwa [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]

中文:
定理 le_seminorm'
  条件: (k n : 自然数) (f : 𝓢(实数, F)) (x : 实数)
  证明: by
  have := le_seminorm 𝕜 k n f x
  rwa [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]

Depends on / 依赖: Real.norm_eq_abs, le_seminorm, norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv
-/
theorem le_seminorm' (k n : Nat) (f : 𝓢(Real, F)) (x : Real) :
    |x| ^ k * ‖iteratedDeriv n f x‖ <= SchwartzMap.seminorm 𝕜 k n f := by
  have := le_seminorm 𝕜 k n f x
  rwa [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]

/--
theorem `norm_iteratedFDeriv_le_seminorm` / 定理 `norm_iteratedFDeriv_le_seminorm`

English:
theorem norm_iteratedFDeriv_le_seminorm
  given: (f : 𝓢(E, F)) (n : Nat) (x₀ : E)
  proof: by
  have := SchwartzMap.le_seminorm 𝕜 0 n f x₀
  rwa [pow_zero, one_mul] at this

中文:
定理 norm_iteratedFDeriv_le_seminorm
  条件: (f : 𝓢(E, F)) (n : 自然数) (x₀ : E)
  证明: by
  have := SchwartzMap.le_seminorm 𝕜 0 n f x₀
  rwa [pow_zero, one_mul] at this

Depends on / 依赖: SchwartzMap, SchwartzMap.le_seminorm, le_seminorm, one_mul, pow_zero
-/
theorem norm_iteratedFDeriv_le_seminorm (f : 𝓢(E, F)) (n : Nat) (x₀ : E) :
    ‖iteratedFDeriv Real n f x₀‖ <= (SchwartzMap.seminorm 𝕜 0 n) f := by
  have := SchwartzMap.le_seminorm 𝕜 0 n f x₀
  rwa [pow_zero, one_mul] at this

/--
theorem `norm_pow_mul_le_seminorm` / 定理 `norm_pow_mul_le_seminorm`

English:
theorem norm_pow_mul_le_seminorm
  given: (f : 𝓢(E, F)) (k : Nat) (x₀ : E)
  proof: by
  have := SchwartzMap.le_seminorm 𝕜 k 0 f x₀
  rwa [norm_iteratedFDeriv_zero] at this

中文:
定理 norm_pow_mul_le_seminorm
  条件: (f : 𝓢(E, F)) (k : 自然数) (x₀ : E)
  证明: by
  have := SchwartzMap.le_seminorm 𝕜 k 0 f x₀
  rwa [norm_iteratedFDeriv_zero] at this

Depends on / 依赖: SchwartzMap, SchwartzMap.le_seminorm, le_seminorm, norm_iteratedFDeriv_zero
-/
theorem norm_pow_mul_le_seminorm (f : 𝓢(E, F)) (k : Nat) (x₀ : E) :
    ‖x₀‖ ^ k * ‖f x₀‖ <= (SchwartzMap.seminorm 𝕜 k 0) f := by
  have := SchwartzMap.le_seminorm 𝕜 k 0 f x₀
  rwa [norm_iteratedFDeriv_zero] at this

/--
theorem `norm_le_seminorm` / 定理 `norm_le_seminorm`

English:
theorem norm_le_seminorm
  given: (f : 𝓢(E, F)) (x₀ : E)
  statement: ‖f x₀‖ <= (SchwartzMap.seminorm 𝕜 0 0) f
  proof: by
  have := norm_pow_mul_le_seminorm 𝕜 f 0 x₀
  rwa [pow_zero, one_mul] at this

中文:
定理 norm_le_seminorm
  条件: (f : 𝓢(E, F)) (x₀ : E)
  结论: ‖f x₀‖ <= (SchwartzMap.seminorm 𝕜 0 0) f
  证明: by
  have := norm_pow_mul_le_seminorm 𝕜 f 0 x₀
  rwa [pow_zero, one_mul] at this

Depends on / 依赖: norm_pow_mul_le_seminorm, one_mul, pow_zero
-/
theorem norm_le_seminorm (f : 𝓢(E, F)) (x₀ : E) : ‖f x₀‖ <= (SchwartzMap.seminorm 𝕜 0 0) f := by
  have := norm_pow_mul_le_seminorm 𝕜 f 0 x₀
  rwa [pow_zero, one_mul] at this

variable (E F)

/--
Definition of `_root_.schwartzSeminormFamily` / `_root_.schwartzSeminormFamily` 的定义

English:
definition _root_.schwartzSeminormFamily
  signature: : SeminormFamily 𝕜 𝓢(E, F) (Nat × Nat)
  body: fun m => SchwartzMap.seminorm 𝕜 m.1 m.2

@[simp]

中文:
定义 _root_.schwartzSeminormFamily
  签名: : SeminormFamily 𝕜 𝓢(E, F) (自然数 × 自然数)
  定义体: fun m => SchwartzMap.seminorm 𝕜 m.1 m.2

@[simp]

Depends on / 依赖: SchwartzMap, SchwartzMap.seminorm, seminorm
-/
def _root_.schwartzSeminormFamily : SeminormFamily 𝕜 𝓢(E, F) (Nat × Nat) :=
  fun m => SchwartzMap.seminorm 𝕜 m.1 m.2

@[simp]
/--
theorem `schwartzSeminormFamily_apply` / 定理 `schwartzSeminormFamily_apply`

English:
theorem schwartzSeminormFamily_apply
  given: (n k : Nat)
  proof: rfl

@[simp]

中文:
定理 schwartzSeminormFamily_apply
  条件: (n k : 自然数)
  证明: rfl

@[simp]
-/
theorem schwartzSeminormFamily_apply (n k : Nat) :
    schwartzSeminormFamily 𝕜 E F (n, k) = SchwartzMap.seminorm 𝕜 n k :=
  rfl

@[simp]
/--
theorem `schwartzSeminormFamily_apply_zero` / 定理 `schwartzSeminormFamily_apply_zero`

English:
theorem schwartzSeminormFamily_apply_zero
  proof: rfl

中文:
定理 schwartzSeminormFamily_apply_zero
  证明: rfl
-/
theorem schwartzSeminormFamily_apply_zero :
    schwartzSeminormFamily 𝕜 E F 0 = SchwartzMap.seminorm 𝕜 0 0 :=
  rfl

variable {𝕜 E F}

/--
theorem `one_add_le_sup_seminorm_apply` / 定理 `one_add_le_sup_seminorm_apply`

English:
theorem one_add_le_sup_seminorm_apply
  statement: {m : Nat × Nat} {k n : Nat} (hk : k <= m.1) (hn : n <= m.2)
  proof: by
  rw [add_comm]; rw [add_pow]
  simp only [one_pow, mul_one, Finset.sum_mul]
  norm_cast
  rw [← Nat.sum_range_choose m.1]
  push_cast
  rw [Finset.sum_mul]
  have hk' : Finset.range (k + 1) subseteq Finset.range (m.1 + 1) := by grind
  grw [hk']
  gcongr ∑ _i in Finset.range (m.1 + 1), ?_ with i

中文:
定理 one_add_le_sup_seminorm_apply
  结论: {m : 自然数 × 自然数} {k n : 自然数} (hk : k <= m.1) (hn : n <= m.2)
  证明: by
  rw [add_comm]; rw [add_pow]
  simp only [one_pow, mul_one, Finset.sum_mul]
  norm_cast
  rw [← Nat.sum_range_choose m.1]
  push_cast
  rw [Finset.sum_mul]
  have hk' : Finset.range (k + 1) subseteq Finset.range (m.1 + 1) := by grind
  grw [hk']
  gcongr ∑ _i in Finset.range (m.1 + 1), ?_ with i

Depends on / 依赖: Finset, Finset.le_sup_of_le, Finset.mem_Iic, Finset.mem_range_succ_iff.mp, Finset.range, Finset.sum_mul, Nat.choose, Nat.sum_range_choose, Prod.mk_le_mk, Seminorm, Seminorm.le_def, add_comm, add_pow, le_def, le_seminorm, le_sup_of_le, mem_Iic, mem_range_succ_iff, mk_le_mk, move_mul
-/
theorem one_add_le_sup_seminorm_apply {m : Nat × Nat} {k n : Nat} (hk : k <= m.1) (hn : n <= m.2)
    (f : 𝓢(E, F)) (x : E) :
    (1 + ‖x‖) ^ k * ‖iteratedFDeriv Real n f x‖ <=
      2 ^ m.1 * (Finset.Iic m).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
  rw [add_comm]; rw [add_pow]
  simp only [one_pow, mul_one, Finset.sum_mul]
  norm_cast
  rw [← Nat.sum_range_choose m.1]
  push_cast
  rw [Finset.sum_mul]
  have hk' : Finset.range (k + 1) subseteq Finset.range (m.1 + 1) := by grind
  grw [hk']
  gcongr ∑ _i in Finset.range (m.1 + 1), ?_ with i hi
  move_mul [(Nat.choose k i : Real), (Nat.choose m.1 i : Real)]
  gcongr
  grw [le_seminorm 𝕜 i n f x]
  apply Seminorm.le_def.1
  exact Finset.le_sup_of_le (Finset.mem_Iic.2 <|
    Prod.mk_le_mk.2 ⟨Finset.mem_range_succ_iff.mp hi, hn⟩) le_rfl

end Seminorms

section Topology

/-! ### The topology on the Schwartz space -/


variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass Real 𝕜 F]
variable (𝕜 E F)

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: : TopologicalSpace 𝓢(E, F)
  body: (schwartzSeminormFamily Real E F).moduleFilterBasis.topology'

中文:
实例 instTopologicalSpace
  签名: : TopologicalSpace 𝓢(E, F)
  定义体: (schwartzSeminormFamily Real E F).moduleFilterBasis.topology'

Depends on / 依赖: moduleFilterBasis, moduleFilterBasis.topology, schwartzSeminormFamily, topology
-/
instance instTopologicalSpace : TopologicalSpace 𝓢(E, F) :=
  (schwartzSeminormFamily Real E F).moduleFilterBasis.topology'

/--
theorem `_root_.schwartz_withSeminorms` / 定理 `_root_.schwartz_withSeminorms`

English:
theorem _root_.schwartz_withSeminorms
  statement: WithSeminorms (schwartzSeminormFamily 𝕜 E F)
  proof: by
  have A : WithSeminorms (schwartzSeminormFamily Real E F) := ⟨rfl⟩
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at A ⊢
  rw [A]
  rfl

中文:
定理 _root_.schwartz_withSeminorms
  结论: WithSeminorms (schwartzSeminormFamily 𝕜 E F)
  证明: by
  have A : WithSeminorms (schwartzSeminormFamily Real E F) := ⟨rfl⟩
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at A ⊢
  rw [A]
  rfl

Depends on / 依赖: SeminormFamily, SeminormFamily.withSeminorms_iff_nhds_eq_iInf, WithSeminorms, schwartzSeminormFamily, withSeminorms_iff_nhds_eq_iInf
-/
theorem _root_.schwartz_withSeminorms : WithSeminorms (schwartzSeminormFamily 𝕜 E F) := by
  have A : WithSeminorms (schwartzSeminormFamily Real E F) := ⟨rfl⟩
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at A ⊢
  rw [A]
  rfl

variable {𝕜 E F}

/--
Instance `instContinuousSMul` / 实例 `instContinuousSMul`

English:
instance instContinuousSMul
  signature: : ContinuousSMul 𝕜 𝓢(E, F)
  body: by
  rw [(schwartz_withSeminorms 𝕜 E F).withSeminorms_eq]
  exact (schwartzSeminormFamily 𝕜 E F).moduleFilterBasis.continuousSMul

中文:
实例 instContinuousSMul
  签名: : ContinuousSMul 𝕜 𝓢(E, F)
  定义体: by
  rw [(schwartz_withSeminorms 𝕜 E F).withSeminorms_eq]
  exact (schwartzSeminormFamily 𝕜 E F).moduleFilterBasis.continuousSMul

Depends on / 依赖: continuousSMul, moduleFilterBasis, moduleFilterBasis.continuousSMul, schwartzSeminormFamily, schwartz_withSeminorms, withSeminorms_eq
-/
instance instContinuousSMul : ContinuousSMul 𝕜 𝓢(E, F) := by
  rw [(schwartz_withSeminorms 𝕜 E F).withSeminorms_eq]
  exact (schwartzSeminormFamily 𝕜 E F).moduleFilterBasis.continuousSMul

/--
Instance `instIsTopologicalAddGroup` / 实例 `instIsTopologicalAddGroup`

English:
instance instIsTopologicalAddGroup
  signature: : IsTopologicalAddGroup 𝓢(E, F)
  body: (schwartzSeminormFamily Real E F).addGroupFilterBasis.isTopologicalAddGroup

中文:
实例 instIsTopologicalAddGroup
  签名: : IsTopologicalAddGroup 𝓢(E, F)
  定义体: (schwartzSeminormFamily Real E F).addGroupFilterBasis.isTopologicalAddGroup

Depends on / 依赖: addGroupFilterBasis, addGroupFilterBasis.isTopologicalAddGroup, isTopologicalAddGroup, schwartzSeminormFamily
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup 𝓢(E, F) :=
  (schwartzSeminormFamily Real E F).addGroupFilterBasis.isTopologicalAddGroup

/--
Instance `instUniformSpace` / 实例 `instUniformSpace`

English:
instance instUniformSpace
  signature: : UniformSpace 𝓢(E, F)
  body: fast_instance% (schwartzSeminormFamily Real E F).addGroupFilterBasis.uniformSpace

中文:
实例 instUniformSpace
  签名: : UniformSpace 𝓢(E, F)
  定义体: fast_instance% (schwartzSeminormFamily Real E F).addGroupFilterBasis.uniformSpace

Depends on / 依赖: addGroupFilterBasis, addGroupFilterBasis.uniformSpace, fast_instance, schwartzSeminormFamily, uniformSpace
-/
instance instUniformSpace : UniformSpace 𝓢(E, F) :=
  fast_instance% (schwartzSeminormFamily Real E F).addGroupFilterBasis.uniformSpace

/--
Instance `instIsUniformAddGroup` / 实例 `instIsUniformAddGroup`

English:
instance instIsUniformAddGroup
  signature: : IsUniformAddGroup 𝓢(E, F)
  body: (schwartzSeminormFamily Real E F).addGroupFilterBasis.isUniformAddGroup

中文:
实例 instIsUniformAddGroup
  签名: : IsUniformAddGroup 𝓢(E, F)
  定义体: (schwartzSeminormFamily Real E F).addGroupFilterBasis.isUniformAddGroup

Depends on / 依赖: addGroupFilterBasis, addGroupFilterBasis.isUniformAddGroup, isUniformAddGroup, schwartzSeminormFamily
-/
instance instIsUniformAddGroup : IsUniformAddGroup 𝓢(E, F) :=
  (schwartzSeminormFamily Real E F).addGroupFilterBasis.isUniformAddGroup

/--
Instance `instLocallyConvexSpace` / 实例 `instLocallyConvexSpace`

English:
instance instLocallyConvexSpace
  signature: : LocallyConvexSpace Real 𝓢(E, F)
  body: (schwartz_withSeminorms Real E F).toLocallyConvexSpace

中文:
实例 instLocallyConvexSpace
  签名: : LocallyConvexSpace 实数 𝓢(E, F)
  定义体: (schwartz_withSeminorms Real E F).toLocallyConvexSpace

Depends on / 依赖: schwartz_withSeminorms, toLocallyConvexSpace
-/
instance instLocallyConvexSpace : LocallyConvexSpace Real 𝓢(E, F) :=
  (schwartz_withSeminorms Real E F).toLocallyConvexSpace

/--
Instance `instFirstCountableTopology` / 实例 `instFirstCountableTopology`

English:
instance instFirstCountableTopology
  signature: : FirstCountableTopology 𝓢(E, F)
  body: (schwartz_withSeminorms Real E F).firstCountableTopology

中文:
实例 instFirstCountableTopology
  签名: : FirstCountableTopology 𝓢(E, F)
  定义体: (schwartz_withSeminorms Real E F).firstCountableTopology

Depends on / 依赖: firstCountableTopology, schwartz_withSeminorms
-/
instance instFirstCountableTopology : FirstCountableTopology 𝓢(E, F) :=
  (schwartz_withSeminorms Real E F).firstCountableTopology

end Topology

@[fun_prop]
/--
theorem `hasTemperateGrowth` / 定理 `hasTemperateGrowth`

English:
theorem hasTemperateGrowth
  given: (f : 𝓢(E, F))
  statement: Function.HasTemperateGrowth f
  proof: by
  refine ⟨smooth f ⊤, fun n => ?_⟩
  rcases f.decay 0 n with ⟨C, Cpos, hC⟩
  exact ⟨0, C, by simpa using hC⟩

中文:
定理 hasTemperateGrowth
  条件: (f : 𝓢(E, F))
  结论: Function.HasTemperateGrowth f
  证明: by
  refine ⟨smooth f ⊤, fun n => ?_⟩
  rcases f.decay 0 n with ⟨C, Cpos, hC⟩
  exact ⟨0, C, by simpa using hC⟩

Depends on / 依赖: f.decay, smooth
-/
theorem hasTemperateGrowth (f : 𝓢(E, F)) : Function.HasTemperateGrowth f := by
  refine ⟨smooth f ⊤, fun n => ?_⟩
  rcases f.decay 0 n with ⟨C, Cpos, hC⟩
  exact ⟨0, C, by simpa using hC⟩

section HasCompactSupport

/-- A smooth compactly supported function is a Schwartz function. -/
@[simps]
/--
Definition of `_root_.HasCompactSupport.toSchwartzMap` / `_root_.HasCompactSupport.toSchwartzMap` 的定义

English:
definition _root_.HasCompactSupport.toSchwartzMap
  signature: {f : E -> F} (h₁ : HasCompactSupport f)
  body: f
  smooth' := h₂
  decay' k n := by
    set g := fun x => ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖
    have hg₁ : Continuous g := by
      apply Continuous.mul (by fun_prop)
      exact (h₂.of_le (mod_cast le_top)).continuous_iteratedFDeriv'.norm
    have hg₂ : HasCompactSupport g := (h₁.iteratedFDeri

中文:
定义 _root_.HasCompactSupport.toSchwartzMap
  签名: {f : E -> F} (h₁ : HasCompactSupport f)
  定义体: f
  smooth' := h₂
  decay' k n := by
    set g := fun x => ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖
    have hg₁ : Continuous g := by
      apply Continuous.mul (by fun_prop)
      exact (h₂.of_le (mod_cast le_top)).continuous_iteratedFDeriv'.norm
    have hg₂ : HasCompactSupport g := (h₁.iteratedFDeri
-/
def _root_.HasCompactSupport.toSchwartzMap {f : E -> F} (h₁ : HasCompactSupport f)
    (h₂ : ContDiff Real ∞ f) : 𝓢(E, F) where
  toFun := f
  smooth' := h₂
  decay' k n := by
    set g := fun x => ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖
    have hg₁ : Continuous g := by
      apply Continuous.mul (by fun_prop)
      exact (h₂.of_le (mod_cast le_top)).continuous_iteratedFDeriv'.norm
    have hg₂ : HasCompactSupport g := (h₁.iteratedFDeriv _).norm.mul_left
    obtain ⟨x₀, hx₀⟩ := hg₁.exists_forall_ge_of_hasCompactSupport hg₂
    exact ⟨g x₀, hx₀⟩

end HasCompactSupport

section CLM

/-! ### Construction of continuous linear maps between Schwartz spaces -/


variable [NormedField 𝕜] [NormedField 𝕜']
variable [NormedAddCommGroup D] [NormedSpace Real D]
variable [NormedSpace 𝕜 E] [SMulCommClass Real 𝕜 E]
variable [NormedAddCommGroup G] [NormedSpace Real G] [NormedSpace 𝕜' G] [SMulCommClass Real 𝕜' G]
variable {σ : 𝕜 ->+* 𝕜'}

/--
Definition of `mkLM` / `mkLM` 的定义

English:
definition mkLM
  signature: (A : 𝓢(D, E) -> F -> G) (hadd : forall (f g : 𝓢(D, E)) (x), A (f + g) x = A f x + A g x)
  body: { toFun := A f
      smooth' := hsmooth f
      decay' := by
        intro k n
        rcases hbound ⟨k, n⟩ with ⟨s, C, _, h⟩
        exact ⟨C * (s.sup (schwartzSeminormFamily 𝕜 D E)) f, h f⟩ }
  map_add' f g := ext (hadd f g)
  map_smul' a f := ext (hsmul a f)

中文:
定义 mkLM
  签名: (A : 𝓢(D, E) -> F -> G) (hadd : 对任意 (f g : 𝓢(D, E)) (x), A (f + g) x = A f x + A g x)
  定义体: { toFun := A f
      smooth' := hsmooth f
      decay' := by
        intro k n
        rcases hbound ⟨k, n⟩ with ⟨s, C, _, h⟩
        exact ⟨C * (s.sup (schwartzSeminormFamily 𝕜 D E)) f, h f⟩ }
  map_add' f g := ext (hadd f g)
  map_smul' a f := ext (hsmul a f)

Depends on / 依赖: hbound, hsmooth, map_add, map_smul, s.sup, schwartzSeminormFamily, smooth
-/
def mkLM (A : 𝓢(D, E) -> F -> G) (hadd : forall (f g : 𝓢(D, E)) (x), A (f + g) x = A f x + A g x)
    (hsmul : forall (a : 𝕜) (f : 𝓢(D, E)) (x), A (a • f) x = σ a • A f x)
    (hsmooth : forall f : 𝓢(D, E), ContDiff Real ∞ (A f))
    (hbound : forall n : Nat × Nat, exists (s : Finset (Nat × Nat)) (C : Real), 0 <= C ∧ forall (f : 𝓢(D, E)) (x : F),
      ‖x‖ ^ n.fst * ‖iteratedFDeriv Real n.snd (A f) x‖ <= C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
    𝓢(D, E) ->ₛₗ[σ] 𝓢(F, G) where
  toFun f :=
    { toFun := A f
      smooth' := hsmooth f
      decay' := by
        intro k n
        rcases hbound ⟨k, n⟩ with ⟨s, C, _, h⟩
        exact ⟨C * (s.sup (schwartzSeminormFamily 𝕜 D E)) f, h f⟩ }
  map_add' f g := ext (hadd f g)
  map_smul' a f := ext (hsmul a f)

/--
Definition of `mkCLM` / `mkCLM` 的定义

English:
definition mkCLM
  signature: [RingHomIsometric σ] (A : 𝓢(D, E) -> F -> G)
  body: by
    change Continuous (mkLM A hadd hsmul hsmooth hbound : 𝓢(D, E) ->ₛₗ[σ] 𝓢(F, G))
    refine
      WithSeminorms.continuous_of_isBounded (schwartz_withSeminorms 𝕜 D E)
        (schwartz_withSeminorms 𝕜' F G) _ fun n => ?_
    rcases hbound n with ⟨s, C, hC, h⟩
    refine ⟨s, ⟨C, hC⟩, fun f => ?_

中文:
定义 mkCLM
  签名: [RingHomIsometric σ] (A : 𝓢(D, E) -> F -> G)
  定义体: by
    change Continuous (mkLM A hadd hsmul hsmooth hbound : 𝓢(D, E) ->ₛₗ[σ] 𝓢(F, G))
    refine
      WithSeminorms.continuous_of_isBounded (schwartz_withSeminorms 𝕜 D E)
        (schwartz_withSeminorms 𝕜' F G) _ fun n => ?_
    rcases hbound n with ⟨s, C, hC, h⟩
    refine ⟨s, ⟨C, hC⟩, fun f => ?_

Depends on / 依赖: Continuous, WithSeminorms, WithSeminorms.continuous_of_isBounded, continuous_of_isBounded, hbound, hsmooth, schwartz_withSeminorms, seminorm_le_bound, toLinearMap
-/
def mkCLM [RingHomIsometric σ] (A : 𝓢(D, E) -> F -> G)
    (hadd : forall (f g : 𝓢(D, E)) (x), A (f + g) x = A f x + A g x)
    (hsmul : forall (a : 𝕜) (f : 𝓢(D, E)) (x), A (a • f) x = σ a • A f x)
    (hsmooth : forall f : 𝓢(D, E), ContDiff Real ∞ (A f))
    (hbound : forall n : Nat × Nat, exists (s : Finset (Nat × Nat)) (C : Real), 0 <= C ∧ forall (f : 𝓢(D, E)) (x : F),
      ‖x‖ ^ n.fst * ‖iteratedFDeriv Real n.snd (A f) x‖ <= C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
    𝓢(D, E) ->SL[σ] 𝓢(F, G) where
  cont := by
    change Continuous (mkLM A hadd hsmul hsmooth hbound : 𝓢(D, E) ->ₛₗ[σ] 𝓢(F, G))
    refine
      WithSeminorms.continuous_of_isBounded (schwartz_withSeminorms 𝕜 D E)
        (schwartz_withSeminorms 𝕜' F G) _ fun n => ?_
    rcases hbound n with ⟨s, C, hC, h⟩
    refine ⟨s, ⟨C, hC⟩, fun f => ?_⟩
    exact (mkLM A hadd hsmul hsmooth hbound f).seminorm_le_bound 𝕜' n.1 n.2 (by positivity) (h f)
  toLinearMap := mkLM A hadd hsmul hsmooth hbound

/--
Definition of `mkCLMtoNormedSpace` / `mkCLMtoNormedSpace` 的定义

English:
definition mkCLMtoNormedSpace
  signature: [RingHomIsometric σ] (A : 𝓢(D, E) -> G)
  body: letI f : 𝓢(D, E) ->ₛₗ[σ] G :=
    { toFun := (A ·)
      map_add' := hadd
      map_smul' := hsmul }
  { toLinearMap := f
    cont := by
      change Continuous (LinearMap.mk _ _)
      apply WithSeminorms.continuous_normedSpace_rng G (schwartz_withSeminorms 𝕜 D E)
      rcases hbound with ⟨s, C, hC

中文:
定义 mkCLMtoNormedSpace
  签名: [RingHomIsometric σ] (A : 𝓢(D, E) -> G)
  定义体: letI f : 𝓢(D, E) ->ₛₗ[σ] G :=
    { toFun := (A ·)
      map_add' := hadd
      map_smul' := hsmul }
  { toLinearMap := f
    cont := by
      change Continuous (LinearMap.mk _ _)
      apply WithSeminorms.continuous_normedSpace_rng G (schwartz_withSeminorms 𝕜 D E)
      rcases hbound with ⟨s, C, hC

Depends on / 依赖: Continuous, LinearMap, LinearMap.mk, WithSeminorms, WithSeminorms.continuous_normedSpace_rng, continuous_normedSpace_rng, hbound, map_add, map_smul, schwartz_withSeminorms, toLinearMap
-/
def mkCLMtoNormedSpace [RingHomIsometric σ] (A : 𝓢(D, E) -> G)
    (hadd : forall (f g : 𝓢(D, E)), A (f + g) = A f + A g)
    (hsmul : forall (a : 𝕜) (f : 𝓢(D, E)), A (a • f) = σ a • A f)
    (hbound : exists (s : Finset (Nat × Nat)) (C : Real), 0 <= C ∧ forall (f : 𝓢(D, E)),
      ‖A f‖ <= C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
    𝓢(D, E) ->SL[σ] G :=
  letI f : 𝓢(D, E) ->ₛₗ[σ] G :=
    { toFun := (A ·)
      map_add' := hadd
      map_smul' := hsmul }
  { toLinearMap := f
    cont := by
      change Continuous (LinearMap.mk _ _)
      apply WithSeminorms.continuous_normedSpace_rng G (schwartz_withSeminorms 𝕜 D E)
      rcases hbound with ⟨s, C, hC, h⟩
      exact ⟨s, ⟨C, hC⟩, h⟩ }

end CLM

section EvalCLM

variable [NormedField 𝕜]
variable [NormedAddCommGroup G] [NormedSpace Real G] [NormedSpace 𝕜 G] [SMulCommClass Real 𝕜 G]

variable (𝕜 E G) in
/--
Definition of `evalCLM` / `evalCLM` 的定义

English:
definition evalCLM
  signature: (m : F)
  body: mkCLM (fun f x => f x m) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
(fun f => ContDiff.clm_apply f.2 contDiff_const) by
  rintro ⟨k, n⟩
  use {(k, n)}, ‖m‖, norm_nonneg _
  intro f x
  simp only [Finset.sup_singleton, schwartzSeminormFamily_apply]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv Real n (f · m) x‖ <=

中文:
定义 evalCLM
  签名: (m : F)
  定义体: mkCLM (fun f x => f x m) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
(fun f => ContDiff.clm_apply f.2 contDiff_const) by
  rintro ⟨k, n⟩
  use {(k, n)}, ‖m‖, norm_nonneg _
  intro f x
  simp only [Finset.sup_singleton, schwartzSeminormFamily_apply]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv Real n (f · m) x‖ <=
-/
protected def evalCLM (m : F) : 𝓢(E, F ->L[Real] G) ->L[𝕜] 𝓢(E, G) :=
  mkCLM (fun f x => f x m) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
(fun f => ContDiff.clm_apply f.2 contDiff_const) by
  rintro ⟨k, n⟩
  use {(k, n)}, ‖m‖, norm_nonneg _
  intro f x
  simp only [Finset.sup_singleton, schwartzSeminormFamily_apply]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv Real n (f · m) x‖ <= ‖x‖ ^ k * (‖m‖ * ‖iteratedFDeriv Real n f x‖) := by
      gcongr
      exact norm_iteratedFDeriv_clm_apply_const (f.smooth _).contDiffAt le_rfl
    _ <= ‖m‖ * SchwartzMap.seminorm 𝕜 k n f := by
      move_mul [‖m‖]
      gcongr
      apply le_seminorm

@[simp]
/--
theorem `evalCLM_apply_apply` / 定理 `evalCLM_apply_apply`

English:
theorem evalCLM_apply_apply
  given: (f : 𝓢(E, F ->L[Real] G)) (m : F) (x : E)
  proof: rfl

中文:
定理 evalCLM_apply_apply
  条件: (f : 𝓢(E, F ->L[实数] G)) (m : F) (x : E)
  证明: rfl
-/
theorem evalCLM_apply_apply (f : 𝓢(E, F ->L[Real] G)) (m : F) (x : E) :
    SchwartzMap.evalCLM 𝕜 E G m f x = f x m := rfl

end EvalCLM

section Multiplication

variable [NontriviallyNormedField 𝕜] [NormedAlgebra Real 𝕜]
  [NormedAddCommGroup D] [NormedSpace Real D]
  [NormedAddCommGroup G] [NormedSpace Real G]
  [NormedSpace 𝕜 F]

section bilin

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 G]

/--
Definition of `bilinLeftCLM` / `bilinLeftCLM` 的定义

English:
definition bilinLeftCLM
  signature: (B : E ->L[𝕜] F ->L[𝕜] G) {g : D -> F} (hg : g.HasTemperateGrowth)
  body: mkCLM (fun f x => B (f x) (g x))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun f => (B.bilinearRestrictScalars Real).isBoundedBilinearMap.contDiff.comp
      ((f.smooth ⊤).prodMk hg.1)) <| by
  rintro ⟨k, n⟩
  rcases hg.norm_iteratedFDeriv_le_uniform n with ⟨l, C, hC, hgrowth⟩
  use
   

中文:
定义 bilinLeftCLM
  签名: (B : E ->L[𝕜] F ->L[𝕜] G) {g : D -> F} (hg : g.HasTemperateGrowth)
  定义体: mkCLM (fun f x => B (f x) (g x))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun f => (B.bilinearRestrictScalars Real).isBoundedBilinearMap.contDiff.comp
      ((f.smooth ⊤).prodMk hg.1)) <| by
  rintro ⟨k, n⟩
  rcases hg.norm_iteratedFDeriv_le_uniform n with ⟨l, C, hC, hgrowth⟩
  use
   

Depends on / 依赖: B.bilinearRestrictScalars, ContinuousLinearMap, ContinuousLinearMap.bilinearRestrictScalars_apply_ap, Finset, Finset.Iic, bilinearRestrictScalars, bilinearRestrictScalars_apply_ap, contDiff, f.smooth, hg.norm_iteratedFDeriv_le_uniform, hgrowth, isBoundedBilinearMap, isBoundedBilinearMap.contDiff.comp, n.choose, norm_iteratedFDeriv_le_uniform, prodMk, simp_rw, smooth
-/
def bilinLeftCLM (B : E ->L[𝕜] F ->L[𝕜] G) {g : D -> F} (hg : g.HasTemperateGrowth) :
    𝓢(D, E) ->L[𝕜] 𝓢(D, G) :=
  mkCLM (fun f x => B (f x) (g x))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun f => (B.bilinearRestrictScalars Real).isBoundedBilinearMap.contDiff.comp
      ((f.smooth ⊤).prodMk hg.1)) <| by
  rintro ⟨k, n⟩
  rcases hg.norm_iteratedFDeriv_le_uniform n with ⟨l, C, hC, hgrowth⟩
  use
    Finset.Iic (l + k, n), ‖B‖ * ((n : Real) + (1 : Real)) * n.choose (n / 2) * (C * 2 ^ (l + k)),
    by positivity
  intro f x
  have hxk : 0 <= ‖x‖ ^ k := by positivity
  simp_rw [← ContinuousLinearMap.bilinearRestrictScalars_apply_apply Real B]
  have hnorm_mul :=
    ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear (B.bilinearRestrictScalars Real)
    (f.smooth ⊤) hg.1 x (n := n) (mod_cast le_top)
  grw [hnorm_mul]
  rw [ContinuousLinearMap.norm_bilinearRestrictScalars]
  move_mul [‖B‖, ‖B‖]
  gcongr ?_ * _
  rw [Finset.mul_sum]
  have : (∑ _x in Finset.range (n + 1), (1 : Real)) = n + 1 := by simp
  simp_rw [mul_assoc ((n : Real) + 1)]
  rw [← this]; rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  simp only [one_mul]
  move_mul [(Nat.choose n i : Real), (Nat.choose n (n / 2) : Real)]
  gcongr ?_ * ?_
  swap
  · norm_cast
    exact i.choose_le_middle n
  specialize hgrowth (n - i) (by simp only [tsub_le_self]) x
  grw [hgrowth]
  move_mul [C]
  gcongr ?_ * C
  rw [Finset.mem_range_succ_iff] at hi
  change i <= (l + k, n).snd at hi
  refine le_trans ?_ (one_add_le_sup_seminorm_apply le_rfl hi f x)
  rw [pow_add]
  move_mul [(1 + ‖x‖) ^ l]
  gcongr
  simp

@[simp]
/--
theorem `bilinLeftCLM_apply` / 定理 `bilinLeftCLM_apply`

English:
theorem bilinLeftCLM_apply
  statement: (B : E ->L[𝕜] F ->L[𝕜] G) {g : D -> F} (hg : g.HasTemperateGrowth)
  proof: rfl

中文:
定理 bilinLeftCLM_apply
  结论: (B : E ->L[𝕜] F ->L[𝕜] G) {g : D -> F} (hg : g.HasTemperateGrowth)
  证明: rfl
-/
theorem bilinLeftCLM_apply (B : E ->L[𝕜] F ->L[𝕜] G) {g : D -> F} (hg : g.HasTemperateGrowth)
    (f : 𝓢(D, E)) : bilinLeftCLM B hg f = fun x => B (f x) (g x) := rfl

end bilin

section smul

variable (F) in
open scoped Classical in
/--
Definition of `smulLeftCLM` / `smulLeftCLM` 的定义

English:
definition smulLeftCLM
  signature: (g : E -> 𝕜)
  body: if hg : g.HasTemperateGrowth then
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul 𝕜 𝕜).flip hg
  else 0

中文:
定义 smulLeftCLM
  签名: (g : E -> 𝕜)
  定义体: if hg : g.HasTemperateGrowth then
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul 𝕜 𝕜).flip hg
  else 0

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, HasTemperateGrowth, SchwartzMap, SchwartzMap.bilinLeftCLM, bilinLeftCLM, g.HasTemperateGrowth
-/
def smulLeftCLM (g : E -> 𝕜) : 𝓢(E, F) ->L[𝕜] 𝓢(E, F) :=
  if hg : g.HasTemperateGrowth then
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul 𝕜 𝕜).flip hg
  else 0

/--
theorem `smulLeftCLM_apply` / 定理 `smulLeftCLM_apply`

English:
theorem smulLeftCLM_apply
  given: {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F))
  proof: by
  simp [smulLeftCLM, hg]

@[simp]

中文:
定理 smulLeftCLM_apply
  条件: {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F))
  证明: by
  simp [smulLeftCLM, hg]

@[simp]

Depends on / 依赖: smulLeftCLM
-/
theorem smulLeftCLM_apply {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    smulLeftCLM F g f = fun x => g x • f x := by
  simp [smulLeftCLM, hg]

@[simp]
/--
theorem `smulLeftCLM_apply_apply` / 定理 `smulLeftCLM_apply_apply`

English:
theorem smulLeftCLM_apply_apply
  given: {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E)
  proof: by
  simp [smulLeftCLM_apply hg]

@[simp]

中文:
定理 smulLeftCLM_apply_apply
  条件: {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E)
  证明: by
  simp [smulLeftCLM_apply hg]

@[simp]

Depends on / 依赖: smulLeftCLM_apply
-/
theorem smulLeftCLM_apply_apply {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) :
    smulLeftCLM F g f x = g x • f x := by
  simp [smulLeftCLM_apply hg]

@[simp]
/--
theorem `smulLeftCLM_const` / 定理 `smulLeftCLM_const`

English:
theorem smulLeftCLM_const
  given: (c : 𝕜)
  proof: by
  ext f x
  have : (fun (_ : E) => c).HasTemperateGrowth := by fun_prop
  simp [this]

@[simp]

中文:
定理 smulLeftCLM_const
  条件: (c : 𝕜)
  证明: by
  ext f x
  have : (fun (_ : E) => c).HasTemperateGrowth := by fun_prop
  simp [this]

@[simp]

Depends on / 依赖: HasTemperateGrowth, fun_prop
-/
theorem smulLeftCLM_const (c : 𝕜) :
    smulLeftCLM F (fun (_ : E) => c) = c • ContinuousLinearMap.id 𝕜 _ := by
  ext f x
  have : (fun (_ : E) => c).HasTemperateGrowth := by fun_prop
  simp [this]

@[simp]
/--
theorem `smulLeftCLM_smulLeftCLM_apply` / 定理 `smulLeftCLM_smulLeftCLM_apply`

English:
theorem smulLeftCLM_smulLeftCLM_apply
  statement: {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth)
  proof: by
  ext x
  simp [smul_smul, hg₁, hg₂, hg₁.mul hg₂]

中文:
定理 smulLeftCLM_smulLeftCLM_apply
  结论: {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth)
  证明: by
  ext x
  simp [smul_smul, hg₁, hg₂, hg₁.mul hg₂]

Depends on / 依赖: smul_smul
-/
theorem smulLeftCLM_smulLeftCLM_apply {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, F)) :
    smulLeftCLM F g₁ (smulLeftCLM F g₂ f) = smulLeftCLM F (g₁ * g₂) f := by
  ext x
  simp [smul_smul, hg₁, hg₂, hg₁.mul hg₂]

/--
theorem `smulLeftCLM_compL_smulLeftCLM` / 定理 `smulLeftCLM_compL_smulLeftCLM`

English:
theorem smulLeftCLM_compL_smulLeftCLM
  statement: {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth)
  proof: by
  ext1 f
  exact smulLeftCLM_smulLeftCLM_apply hg₁ hg₂ f

中文:
定理 smulLeftCLM_compL_smulLeftCLM
  结论: {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth)
  证明: by
  ext1 f
  exact smulLeftCLM_smulLeftCLM_apply hg₁ hg₂ f

Depends on / 依赖: smulLeftCLM_smulLeftCLM_apply
-/
theorem smulLeftCLM_compL_smulLeftCLM {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F g₁ ∘L smulLeftCLM F g₂ = smulLeftCLM F (g₁ * g₂) := by
  ext1 f
  exact smulLeftCLM_smulLeftCLM_apply hg₁ hg₂ f

/--
theorem `smulLeftCLM_smul` / 定理 `smulLeftCLM_smul`

English:
theorem smulLeftCLM_smul
  given: {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜)
  proof: by
  have : (fun (_ : E) => c).HasTemperateGrowth := by fun_prop
  convert! (smulLeftCLM_compL_smulLeftCLM this hg).symm using 1
  simp

中文:
定理 smulLeftCLM_smul
  条件: {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜)
  证明: by
  have : (fun (_ : E) => c).HasTemperateGrowth := by fun_prop
  convert! (smulLeftCLM_compL_smulLeftCLM this hg).symm using 1
  simp

Depends on / 依赖: HasTemperateGrowth, convert, fun_prop, smulLeftCLM_compL_smulLeftCLM
-/
theorem smulLeftCLM_smul {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜) :
    smulLeftCLM F (c • g) = c • smulLeftCLM F g := by
  have : (fun (_ : E) => c).HasTemperateGrowth := by fun_prop
  convert! (smulLeftCLM_compL_smulLeftCLM this hg).symm using 1
  simp

/--
theorem `smulLeftCLM_add` / 定理 `smulLeftCLM_add`

English:
theorem smulLeftCLM_add
  statement: {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth)
  proof: by
  ext f x
  simp [hg₁, hg₂, hg₁.add hg₂, add_smul]

中文:
定理 smulLeftCLM_add
  结论: {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth)
  证明: by
  ext f x
  simp [hg₁, hg₂, hg₁.add hg₂, add_smul]

Depends on / 依赖: add_smul
-/
theorem smulLeftCLM_add {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F (g₁ + g₂) = smulLeftCLM F g₁ + smulLeftCLM F g₂ := by
  ext f x
  simp [hg₁, hg₂, hg₁.add hg₂, add_smul]

/--
theorem `smulLeftCLM_sub` / 定理 `smulLeftCLM_sub`

English:
theorem smulLeftCLM_sub
  statement: {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth)
  proof: by
  ext f x
  simp [hg₁, hg₂, hg₁.sub hg₂, sub_smul]

中文:
定理 smulLeftCLM_sub
  结论: {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth)
  证明: by
  ext f x
  simp [hg₁, hg₂, hg₁.sub hg₂, sub_smul]

Depends on / 依赖: sub_smul
-/
theorem smulLeftCLM_sub {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F (g₁ - g₂) = smulLeftCLM F g₁ - smulLeftCLM F g₂ := by
  ext f x
  simp [hg₁, hg₂, hg₁.sub hg₂, sub_smul]

/--
theorem `smulLeftCLM_neg` / 定理 `smulLeftCLM_neg`

English:
theorem smulLeftCLM_neg
  given: {g : E -> 𝕜} (hg : g.HasTemperateGrowth)
  proof: by
  ext f x
  simp [hg, hg.neg, neg_smul]

中文:
定理 smulLeftCLM_neg
  条件: {g : E -> 𝕜} (hg : g.HasTemperateGrowth)
  证明: by
  ext f x
  simp [hg, hg.neg, neg_smul]

Depends on / 依赖: hg.neg, neg_smul
-/
theorem smulLeftCLM_neg {g : E -> 𝕜} (hg : g.HasTemperateGrowth) :
    smulLeftCLM F (-g) = -smulLeftCLM F g := by
  ext f x
  simp [hg, hg.neg, neg_smul]

/--
theorem `smulLeftCLM_fun_neg` / 定理 `smulLeftCLM_fun_neg`

English:
theorem smulLeftCLM_fun_neg
  given: {g : E -> 𝕜} (hg : g.HasTemperateGrowth)
  proof: smulLeftCLM_neg hg

中文:
定理 smulLeftCLM_fun_neg
  条件: {g : E -> 𝕜} (hg : g.HasTemperateGrowth)
  证明: smulLeftCLM_neg hg

Depends on / 依赖: smulLeftCLM_neg
-/
theorem smulLeftCLM_fun_neg {g : E -> 𝕜} (hg : g.HasTemperateGrowth) :
    smulLeftCLM F (fun x => -g x) = -smulLeftCLM F g :=
  smulLeftCLM_neg hg

/--
theorem `smulLeftCLM_sum` / 定理 `smulLeftCLM_sum`

English:
theorem smulLeftCLM_sum
  given: {g : ι -> E -> 𝕜} {s : Finset ι} (hg : forall i in s, (g i).HasTemperateGrowth)
  proof: by
  ext f x
  simp +contextual [Function.HasTemperateGrowth.sum hg, Finset.sum_smul, hg]

中文:
定理 smulLeftCLM_sum
  条件: {g : ι -> E -> 𝕜} {s : Finset ι} (hg : 对任意 i in s, (g i).HasTemperateGrowth)
  证明: by
  ext f x
  simp +contextual [Function.HasTemperateGrowth.sum hg, Finset.sum_smul, hg]

Depends on / 依赖: Finset, Finset.sum_smul, Function, Function.HasTemperateGrowth.sum, HasTemperateGrowth, contextual, sum_smul
-/
theorem smulLeftCLM_sum {g : ι -> E -> 𝕜} {s : Finset ι} (hg : forall i in s, (g i).HasTemperateGrowth) :
    smulLeftCLM F (fun x => ∑ i in s, g i x) = ∑ i in s, smulLeftCLM F (g i) := by
  ext f x
  simp +contextual [Function.HasTemperateGrowth.sum hg, Finset.sum_smul, hg]

variable {𝕜' : Type*} [RCLike 𝕜'] [NormedSpace 𝕜' F]

variable (𝕜') in
/--
theorem `smulLeftCLM_ofReal` / 定理 `smulLeftCLM_ofReal`

English:
theorem smulLeftCLM_ofReal
  given: {g : E -> Real} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F))
  proof: by
  ext x
  rw [smulLeftCLM_apply_apply (by fun_prop)]; rw [smulLeftCLM_apply_apply (by fun_prop)]; rw [algebraMap_smul]

中文:
定理 smulLeftCLM_ofReal
  条件: {g : E -> 实数} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F))
  证明: by
  ext x
  rw [smulLeftCLM_apply_apply (by fun_prop)]; rw [smulLeftCLM_apply_apply (by fun_prop)]; rw [algebraMap_smul]

Depends on / 依赖: algebraMap_smul, fun_prop, smulLeftCLM, smulLeftCLM_apply_apply
-/
theorem smulLeftCLM_ofReal {g : E -> Real} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    smulLeftCLM F (fun x => RCLike.ofReal (K := 𝕜') (g x)) f = smulLeftCLM F g f := by
  ext x
  rw [smulLeftCLM_apply_apply (by fun_prop)]; rw [smulLeftCLM_apply_apply (by fun_prop)]; rw [algebraMap_smul]

/--
theorem `smulLeftCLM_real_smul` / 定理 `smulLeftCLM_real_smul`

English:
theorem smulLeftCLM_real_smul
  given: {g : E -> 𝕜'} (hg : g.HasTemperateGrowth) (c : Real)
  proof: by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜') c]; rw [smulLeftCLM_smul hg]; rw [← RCLike.real_smul_eq_coe_smul c]

中文:
定理 smulLeftCLM_real_smul
  条件: {g : E -> 𝕜'} (hg : g.HasTemperateGrowth) (c : 实数)
  证明: by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜') c]; rw [smulLeftCLM_smul hg]; rw [← RCLike.real_smul_eq_coe_smul c]

Depends on / 依赖: RCLike, RCLike.real_smul_eq_coe_smul, real_smul_eq_coe_smul, smulLeftCLM_smul
-/
theorem smulLeftCLM_real_smul {g : E -> 𝕜'} (hg : g.HasTemperateGrowth) (c : Real) :
    smulLeftCLM F (c • g) = c • smulLeftCLM F g := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜') c]; rw [smulLeftCLM_smul hg]; rw [← RCLike.real_smul_eq_coe_smul c]

/--
theorem `tsupport_smulLeftCLM_subset` / 定理 `tsupport_smulLeftCLM_subset`

English:
theorem tsupport_smulLeftCLM_subset
  given: (g : E -> 𝕜) (f : 𝓢(E, F))
  proof: by
  by_cases hg : g.HasTemperateGrowth
  · simpa [smulLeftCLM_apply hg] using
      ⟨tsupport_smul_subset_right g f, tsupport_smul_subset_left g f⟩
  · simp [smulLeftCLM, hg, FunLike.coe_zero]

中文:
定理 tsupport_smulLeftCLM_subset
  条件: (g : E -> 𝕜) (f : 𝓢(E, F))
  证明: by
  by_cases hg : g.HasTemperateGrowth
  · simpa [smulLeftCLM_apply hg] using
      ⟨tsupport_smul_subset_right g f, tsupport_smul_subset_left g f⟩
  · simp [smulLeftCLM, hg, FunLike.coe_zero]

Depends on / 依赖: FunLike, FunLike.coe_zero, HasTemperateGrowth, coe_zero, g.HasTemperateGrowth, smulLeftCLM, smulLeftCLM_apply, tsupport_smul_subset_left, tsupport_smul_subset_right
-/
theorem tsupport_smulLeftCLM_subset (g : E -> 𝕜) (f : 𝓢(E, F)) :
    tsupport (smulLeftCLM F g f) subseteq tsupport f inter tsupport g := by
  by_cases hg : g.HasTemperateGrowth
  · simpa [smulLeftCLM_apply hg] using
      ⟨tsupport_smul_subset_right g f, tsupport_smul_subset_left g f⟩
  · simp [smulLeftCLM, hg, FunLike.coe_zero]

end smul

section pairing

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 G]

/--
Definition of `pairing` / `pairing` 的定义

English:
definition pairing
  signature: (B : E ->L[𝕜] F ->L[𝕜] G)
  body: bilinLeftCLM B.flip f.hasTemperateGrowth
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

中文:
定义 pairing
  签名: (B : E ->L[𝕜] F ->L[𝕜] G)
  定义体: bilinLeftCLM B.flip f.hasTemperateGrowth
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

Depends on / 依赖: B.flip, bilinLeftCLM, f.hasTemperateGrowth, hasTemperateGrowth
-/
def pairing (B : E ->L[𝕜] F ->L[𝕜] G) : 𝓢(D, E) ->ₗ[𝕜] 𝓢(D, F) ->L[𝕜] 𝓢(D, G) where
  toFun f := bilinLeftCLM B.flip f.hasTemperateGrowth
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/--
theorem `pairing_apply` / 定理 `pairing_apply`

English:
theorem pairing_apply
  given: (B : E ->L[𝕜] F ->L[𝕜] G) (f : 𝓢(D, E)) (g : 𝓢(D, F))
  proof: rfl

@[simp]

中文:
定理 pairing_apply
  条件: (B : E ->L[𝕜] F ->L[𝕜] G) (f : 𝓢(D, E)) (g : 𝓢(D, F))
  证明: rfl

@[simp]
-/
theorem pairing_apply (B : E ->L[𝕜] F ->L[𝕜] G) (f : 𝓢(D, E)) (g : 𝓢(D, F)) :
    pairing B f g = fun x => B (f x) (g x) := rfl

@[simp]
/--
theorem `pairing_apply_apply` / 定理 `pairing_apply_apply`

English:
theorem pairing_apply_apply
  given: (B : E ->L[𝕜] F ->L[𝕜] G) (f : 𝓢(D, E)) (g : 𝓢(D, F)) (x : D)
  proof: rfl

中文:
定理 pairing_apply_apply
  条件: (B : E ->L[𝕜] F ->L[𝕜] G) (f : 𝓢(D, E)) (g : 𝓢(D, F)) (x : D)
  证明: rfl
-/
theorem pairing_apply_apply (B : E ->L[𝕜] F ->L[𝕜] G) (f : 𝓢(D, E)) (g : 𝓢(D, F)) (x : D) :
    pairing B f g x = B (f x) (g x) := rfl

/--
theorem `pairing_continuous_left` / 定理 `pairing_continuous_left`

English:
theorem pairing_continuous_left
  given: (B : E ->L[𝕜] F ->L[𝕜] G) (g : 𝓢(D, F))
  proof: (pairing B.flip g).continuous

中文:
定理 pairing_continuous_left
  条件: (B : E ->L[𝕜] F ->L[𝕜] G) (g : 𝓢(D, F))
  证明: (pairing B.flip g).continuous

Depends on / 依赖: B.flip, continuous, pairing
-/
theorem pairing_continuous_left (B : E ->L[𝕜] F ->L[𝕜] G) (g : 𝓢(D, F)) :
    Continuous (pairing B · g) := (pairing B.flip g).continuous

end pairing

open ContinuousLinearMap

variable (𝕜 F) in
/--
Definition of `smulRightCLM` / `smulRightCLM` 的定义

English:
definition smulRightCLM
  signature: (L : E ->L[Real] G ->L[Real] Real)
  body: mkCLM (fun f x => (L x).smulRight (f x)) (by intros; ext; simp)
    (by intro c g x; ext v; simpa using smul_comm (L x v) c (g x))
(by fun_prop) by
      intro ⟨k, n⟩
      use {(k + 1, n), (k, n - 1)}, 2 * ‖L‖ * (max 1 n), by positivity
      intro f x
      calc
        _ <= ‖x‖ ^ k * ∑ i in Finse

中文:
定义 smulRightCLM
  签名: (L : E ->L[实数] G ->L[实数] 实数)
  定义体: mkCLM (fun f x => (L x).smulRight (f x)) (by intros; ext; simp)
    (by intro c g x; ext v; simpa using smul_comm (L x v) c (g x))
(by fun_prop) by
      intro ⟨k, n⟩
      use {(k + 1, n), (k, n - 1)}, 2 * ‖L‖ * (max 1 n), by positivity
      intro f x
      calc
        _ <= ‖x‖ ^ k * ∑ i in Finse

Depends on / 依赖: Finset, Finset.range, f.smooth, fun_prop, intros, iteratedFDeriv, le_top, mod_cast, n.choose, norm_, norm_iteratedFDeriv_le_of_bilinear_of_le_one, smooth, smulRight, smulRightL, smul_comm
-/
def smulRightCLM (L : E ->L[Real] G ->L[Real] Real) : 𝓢(E, F) ->L[𝕜] 𝓢(E, G ->L[Real] F) :=
  mkCLM (fun f x => (L x).smulRight (f x)) (by intros; ext; simp)
    (by intro c g x; ext v; simpa using smul_comm (L x v) c (g x))
(by fun_prop) by
      intro ⟨k, n⟩
      use {(k + 1, n), (k, n - 1)}, 2 * ‖L‖ * (max 1 n), by positivity
      intro f x
      calc
        _ <= ‖x‖ ^ k * ∑ i in Finset.range (n + 1), (n.choose i) *
            ‖iteratedFDeriv Real i L x‖ * ‖iteratedFDeriv Real (n - i) f x‖ := by
          gcongr 1
          exact norm_iteratedFDeriv_le_of_bilinear_of_le_one (smulRightL Real G F)
            (by fun_prop) (f.smooth ⊤) x (mod_cast le_top) norm_smulRightL_le
        _ <= ‖x‖ ^ k *
            (‖L x‖ * ‖iteratedFDeriv Real n f x‖ + n * ‖L‖ * ‖iteratedFDeriv Real (n - 1) f x‖) := by
          gcongr 1
          rw [Finset.sum_range_succ']; rw [add_comm]
          cases n with
          | zero => simp
          | succ n =>
            have : ∑ k in Finset.range n,
                (((n + 1).choose (k + 1 + 1)) : Real) * ‖iteratedFDeriv Real (k + 1 + 1) L x‖ *
                ‖iteratedFDeriv Real (n + 1 - (k + 1 + 1)) f x‖ = 0 := by
              apply Finset.sum_eq_zero
              simp [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_const]
            simp [Finset.sum_range_succ', this]
        _ = ‖x‖ ^ k * ‖L x‖ * ‖iteratedFDeriv Real n f x‖ +
              ‖x‖ ^ k * n * ‖L‖ * ‖iteratedFDeriv Real (n - 1) f x‖ := by ring
        _ <= ‖L‖ * 1 * (SchwartzMap.seminorm 𝕜 (k + 1) n) f +
              ‖L‖ * n * (SchwartzMap.seminorm 𝕜 k (n - 1) f) := by
          grw [le_opNorm, ← le_seminorm 𝕜 (k + 1) n f x, ← le_seminorm 𝕜 k (n - 1) f x]
          apply le_of_eq
          ring
        _ <= ‖L‖ * max 1 n *
            max ((SchwartzMap.seminorm 𝕜 (k + 1) n) f) ((SchwartzMap.seminorm 𝕜 k (n - 1)) f) +
            ‖L‖ * max 1 n *
            max ((SchwartzMap.seminorm 𝕜 (k + 1) n) f) ((SchwartzMap.seminorm 𝕜 k (n - 1)) f) := by
          gcongr <;> simp
        _ = _ := by
          simp only [Finset.sup_insert, schwartzSeminormFamily_apply, Finset.sup_singleton,
            Seminorm.coe_sup, Pi.sup_apply]
          ring

@[simp]
/--
theorem `smulRightCLM_apply_apply` / 定理 `smulRightCLM_apply_apply`

English:
theorem smulRightCLM_apply_apply
  given: (L : E ->L[Real] G ->L[Real] Real) (f : 𝓢(E, F)) (x : E)
  proof: rfl

中文:
定理 smulRightCLM_apply_apply
  条件: (L : E ->L[实数] G ->L[实数] 实数) (f : 𝓢(E, F)) (x : E)
  证明: rfl
-/
theorem smulRightCLM_apply_apply (L : E ->L[Real] G ->L[Real] Real) (f : 𝓢(E, F)) (x : E) :
    smulRightCLM 𝕜 F L f x = (L x).smulRight (f x) := rfl

end Multiplication

section Comp

variable (𝕜)
variable [RCLike 𝕜]
variable [NormedAddCommGroup D] [NormedSpace Real D]
variable [NormedSpace 𝕜 F]

/--
Definition of `compCLM` / `compCLM` 的定义

English:
definition compCLM
  signature: {g : D -> E} (hg : g.HasTemperateGrowth)
  body: mkCLM (fun f => f ∘ g) (fun _ _ _ => by simp) (fun _ _ _ => rfl)
(fun f => (f.smooth ⊤).comp hg.1) by
  rintro ⟨k, n⟩
  rcases hg.norm_iteratedFDeriv_le_uniform n with ⟨l, C, hC, hgrowth⟩
  rcases hg_upper with ⟨kg, Cg, hg_upper'⟩
  have hCg : 1 <= 1 + Cg := by
    refine le_add_of_nonneg_right ?_
 

中文:
定义 compCLM
  签名: {g : D -> E} (hg : g.HasTemperateGrowth)
  定义体: mkCLM (fun f => f ∘ g) (fun _ _ _ => by simp) (fun _ _ _ => rfl)
(fun f => (f.smooth ⊤).comp hg.1) by
  rintro ⟨k, n⟩
  rcases hg.norm_iteratedFDeriv_le_uniform n with ⟨l, C, hC, hgrowth⟩
  rcases hg_upper with ⟨kg, Cg, hg_upper'⟩
  have hCg : 1 <= 1 + Cg := by
    refine le_add_of_nonneg_right ?_
 

Depends on / 依赖: Finset, Finset.Iic, f.smooth, hg.norm_iteratedFDeriv_le_uniform, hg_upper, hgrowth, le_add_of_nonneg_right, nonneg_of_mul_nonneg_left, norm_iteratedFDeriv_le_uniform, norm_zero, smooth, specialize
-/
def compCLM {g : D -> E} (hg : g.HasTemperateGrowth)
    (hg_upper : exists (k : Nat) (C : Real), forall x, ‖x‖ <= C * (1 + ‖g x‖) ^ k) : 𝓢(E, F) ->L[𝕜] 𝓢(D, F) :=
  mkCLM (fun f => f ∘ g) (fun _ _ _ => by simp) (fun _ _ _ => rfl)
(fun f => (f.smooth ⊤).comp hg.1) by
  rintro ⟨k, n⟩
  rcases hg.norm_iteratedFDeriv_le_uniform n with ⟨l, C, hC, hgrowth⟩
  rcases hg_upper with ⟨kg, Cg, hg_upper'⟩
  have hCg : 1 <= 1 + Cg := by
    refine le_add_of_nonneg_right ?_
    specialize hg_upper' 0
    rw [norm_zero] at hg_upper'
    exact nonneg_of_mul_nonneg_left hg_upper' (by positivity)
  let k' := kg * (k + l * n)
  use Finset.Iic (k', n), (1 + Cg) ^ (k + l * n) * ((C + 1) ^ n * n ! * 2 ^ k'), by positivity
  intro f x
  let seminorm_f := ((Finset.Iic (k', n)).sup (schwartzSeminormFamily 𝕜 _ _)) f
  have hg_upper'' : (1 + ‖x‖) ^ (k + l * n) <= (1 + Cg) ^ (k + l * n) * (1 + ‖g x‖) ^ k' := by
    rw [pow_mul]; rw [← mul_pow]
    gcongr
    rw [add_mul]
    refine add_le_add ?_ (hg_upper' x)
    nth_rw 1 [← one_mul (1 : Real)]
    gcongr
    apply one_le_pow₀
    simp only [le_add_iff_nonneg_right, norm_nonneg]
  have hbound (i) (hi : i <= n) :
      ‖iteratedFDeriv Real i f (g x)‖ <= 2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k' := by
    have hpos : 0 < (1 + ‖g x‖) ^ k' := by positivity
    rw [le_div_iff₀' hpos]
    change i <= (k', n).snd at hi
    exact one_add_le_sup_seminorm_apply le_rfl hi _ _
  have hgrowth' (N : Nat) (hN₁ : 1 <= N) (hN₂ : N <= n) :
      ‖iteratedFDeriv Real N g x‖ <= ((C + 1) * (1 + ‖x‖) ^ l) ^ N := by
    refine (hgrowth N hN₂ x).trans ?_
    rw [mul_pow]
    have hN₁' := (lt_of_lt_of_le zero_lt_one hN₁).ne'
    gcongr
    · exact le_trans (by simp) (le_self_pow₀ (by simp [hC]) hN₁')
    · refine le_self_pow₀ (one_le_pow₀ ?_) hN₁'
      simp only [le_add_iff_nonneg_right, norm_nonneg]
  have := norm_iteratedFDeriv_comp_le (f.smooth ⊤) hg.1 (mod_cast le_top) x hbound hgrowth'
  have hxk : ‖x‖ ^ k <= (1 + ‖x‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (by simp only [zero_le_one, le_add_iff_nonneg_left]) _
  grw [hxk, this]
  have rearrange :
    (1 + ‖x‖) ^ k *
        (n ! * (2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k') * ((C + 1) * (1 + ‖x‖) ^ l) ^ n) =
      (1 + ‖x‖) ^ (k + l * n) / (1 + ‖g x‖) ^ k' *
        ((C + 1) ^ n * n ! * 2 ^ k' * seminorm_f) := by
    rw [mul_pow]; rw [pow_add]; rw [← pow_mul]
    ring
  rw [rearrange]
  have hgxk' : 0 < (1 + ‖g x‖) ^ k' := by positivity
  rw [← div_le_iff₀ hgxk'] at hg_upper''
  grw [hg_upper'', ← mul_assoc]

/--
lemma `compCLM_apply` / 引理 `compCLM_apply`

English:
lemma compCLM_apply
  statement: {g : D -> E} (hg : g.HasTemperateGrowth)
  proof: rfl

中文:
引理 compCLM_apply
  结论: {g : D -> E} (hg : g.HasTemperateGrowth)
  证明: rfl
-/
@[simp] lemma compCLM_apply {g : D -> E} (hg : g.HasTemperateGrowth)
    (hg_upper : exists (k : Nat) (C : Real), forall x, ‖x‖ <= C * (1 + ‖g x‖) ^ k) (f : 𝓢(E, F)) :
    compCLM 𝕜 hg hg_upper f = f ∘ g := rfl

/--
Definition of `compCLMOfAntilipschitz` / `compCLMOfAntilipschitz` 的定义

English:
definition compCLMOfAntilipschitz
  signature: {K : Real>=0} {g : D -> E}
  body: by
  refine compCLM 𝕜 hg ⟨1, K * max 1 ‖g 0‖, fun x => ?_⟩
  calc
  ‖x‖ <= K * ‖g x - g 0‖ := by
    rw [← dist_zero_right]; rw [← dist_eq_norm]
    apply h'g.le_mul_dist
  _ <= K * (‖g x‖ + ‖g 0‖) := by
    gcongr
    exact norm_sub_le _ _
  _ <= K * (‖g x‖ + max 1 ‖g 0‖) := by
    gcongr
    exact

中文:
定义 compCLMOfAntilipschitz
  签名: {K : 实数>=0} {g : D -> E}
  定义体: by
  refine compCLM 𝕜 hg ⟨1, K * max 1 ‖g 0‖, fun x => ?_⟩
  calc
  ‖x‖ <= K * ‖g x - g 0‖ := by
    rw [← dist_zero_right]; rw [← dist_eq_norm]
    apply h'g.le_mul_dist
  _ <= K * (‖g x‖ + ‖g 0‖) := by
    gcongr
    exact norm_sub_le _ _
  _ <= K * (‖g x‖ + max 1 ‖g 0‖) := by
    gcongr
    exact

Depends on / 依赖: add_comm, add_le_add_iff_left, compCLM, dist_eq_norm, dist_zero_right, g.le_mul_dist, le_max_left, le_max_right, le_mul_dist, le_mul_of_one_le_right, mul_add, mul_one, norm_sub_le, pow_one
-/
def compCLMOfAntilipschitz {K : Real>=0} {g : D -> E}
    (hg : g.HasTemperateGrowth) (h'g : AntilipschitzWith K g) :
    𝓢(E, F) ->L[𝕜] 𝓢(D, F) := by
  refine compCLM 𝕜 hg ⟨1, K * max 1 ‖g 0‖, fun x => ?_⟩
  calc
  ‖x‖ <= K * ‖g x - g 0‖ := by
    rw [← dist_zero_right]; rw [← dist_eq_norm]
    apply h'g.le_mul_dist
  _ <= K * (‖g x‖ + ‖g 0‖) := by
    gcongr
    exact norm_sub_le _ _
  _ <= K * (‖g x‖ + max 1 ‖g 0‖) := by
    gcongr
    exact le_max_right _ _
  _ <= (K * max 1 ‖g 0‖ : Real) * (1 + ‖g x‖) ^ 1 := by
    simp only [mul_add, add_comm (K * ‖g x‖), pow_one, mul_one, add_le_add_iff_left]
    gcongr
    exact le_mul_of_one_le_right (by positivity) (le_max_left _ _)

/--
lemma `compCLMOfAntilipschitz_apply` / 引理 `compCLMOfAntilipschitz_apply`

English:
lemma compCLMOfAntilipschitz_apply
  statement: {K : Real>=0} {g : D -> E} (hg : g.HasTemperateGrowth)
  proof: rfl

中文:
引理 compCLMOfAntilipschitz_apply
  结论: {K : 实数>=0} {g : D -> E} (hg : g.HasTemperateGrowth)
  证明: rfl
-/
@[simp] lemma compCLMOfAntilipschitz_apply {K : Real>=0} {g : D -> E} (hg : g.HasTemperateGrowth)
    (h'g : AntilipschitzWith K g) (f : 𝓢(E, F)) :
    compCLMOfAntilipschitz 𝕜 hg h'g f = f ∘ g := rfl

/--
Definition of `compCLMOfContinuousLinearEquiv` / `compCLMOfContinuousLinearEquiv` 的定义

English:
definition compCLMOfContinuousLinearEquiv
  signature: (g : D ≃L[Real] E)
  body: compCLMOfAntilipschitz 𝕜 (g.toContinuousLinearMap.hasTemperateGrowth) g.antilipschitz

中文:
定义 compCLMOfContinuousLinearEquiv
  签名: (g : D ≃L[实数] E)
  定义体: compCLMOfAntilipschitz 𝕜 (g.toContinuousLinearMap.hasTemperateGrowth) g.antilipschitz

Depends on / 依赖: antilipschitz, compCLMOfAntilipschitz, g.antilipschitz, g.toContinuousLinearMap.hasTemperateGrowth, hasTemperateGrowth, toContinuousLinearMap
-/
def compCLMOfContinuousLinearEquiv (g : D ≃L[Real] E) :
    𝓢(E, F) ->L[𝕜] 𝓢(D, F) :=
  compCLMOfAntilipschitz 𝕜 (g.toContinuousLinearMap.hasTemperateGrowth) g.antilipschitz

/--
lemma `compCLMOfContinuousLinearEquiv_apply` / 引理 `compCLMOfContinuousLinearEquiv_apply`

English:
lemma compCLMOfContinuousLinearEquiv_apply
  given: (g : D ≃L[Real] E) (f : 𝓢(E, F))
  proof: rfl

中文:
引理 compCLMOfContinuousLinearEquiv_apply
  条件: (g : D ≃L[实数] E) (f : 𝓢(E, F))
  证明: rfl
-/
@[simp] lemma compCLMOfContinuousLinearEquiv_apply (g : D ≃L[Real] E) (f : 𝓢(E, F)) :
    compCLMOfContinuousLinearEquiv 𝕜 g f = f ∘ g := rfl

variable [NontriviallyNormedField 𝕜'] [NormedAlgebra Real 𝕜'] [NormedSpace 𝕜' F]

/--
theorem `smulLeftCLM_compCLMOfContinuousLinearEquiv` / 定理 `smulLeftCLM_compCLMOfContinuousLinearEquiv`

English:
theorem smulLeftCLM_compCLMOfContinuousLinearEquiv
  statement: {u : D -> 𝕜'} (hu : u.HasTemperateGrowth)
  proof: by
  ext x
  have hu' : (u ∘ g.symm).HasTemperateGrowth := by fun_prop
  simp [smulLeftCLM_apply_apply hu, smulLeftCLM_apply_apply hu']

中文:
定理 smulLeftCLM_compCLMOfContinuousLinearEquiv
  结论: {u : D -> 𝕜'} (hu : u.HasTemperateGrowth)
  证明: by
  ext x
  have hu' : (u ∘ g.symm).HasTemperateGrowth := by fun_prop
  simp [smulLeftCLM_apply_apply hu, smulLeftCLM_apply_apply hu']

Depends on / 依赖: HasTemperateGrowth, fun_prop, g.symm, smulLeftCLM_apply_apply
-/
theorem smulLeftCLM_compCLMOfContinuousLinearEquiv {u : D -> 𝕜'} (hu : u.HasTemperateGrowth)
    (g : D ≃L[Real] E) (f : 𝓢(E, F)) :
    smulLeftCLM F u (compCLMOfContinuousLinearEquiv 𝕜 g f) =
    compCLMOfContinuousLinearEquiv 𝕜 g (smulLeftCLM F (u ∘ g.symm) f) := by
  ext x
  have hu' : (u ∘ g.symm).HasTemperateGrowth := by fun_prop
  simp [smulLeftCLM_apply_apply hu, smulLeftCLM_apply_apply hu']

end Comp

section Postcomp

variable [RCLike 𝕜]
  [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace Real G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace Real H] [NormedSpace 𝕜 H]

/--
Definition of `postcompCLM` / `postcompCLM` 的定义

English:
definition postcompCLM
  signature: (L : F ->L[𝕜] G)
  body: mkCLM (fun f => L ∘ f) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
(fun f => (L.restrictScalars Real).contDiff.comp (f.smooth ⊤)) by
  intro ⟨k, n⟩
  use {⟨k, n⟩}, ‖L‖, by positivity
  intro f x
  simp only [Finset.sup_singleton, schwartzSeminormFamily_apply]
  calc
    _ = ‖x‖ ^ k * ‖(L.restrictS

中文:
定义 postcompCLM
  签名: (L : F ->L[𝕜] G)
  定义体: mkCLM (fun f => L ∘ f) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
(fun f => (L.restrictScalars Real).contDiff.comp (f.smooth ⊤)) by
  intro ⟨k, n⟩
  use {⟨k, n⟩}, ‖L‖, by positivity
  intro f x
  simp only [Finset.sup_singleton, schwartzSeminormFamily_apply]
  calc
    _ = ‖x‖ ^ k * ‖(L.restrictS

Depends on / 依赖: Finset, Finset.sup_singleton, L.restrictScalars, compContinuousMultilinearMap, contDiff, contDiff.comp, contDiffAt, f.smooth, iteratedFDeri, iteratedFDeriv, iteratedFDeriv_comp_left, le_top, mod_cast, restrictScalars, schwartzSeminormFamily_apply, smooth, sup_singleton
-/
def postcompCLM (L : F ->L[𝕜] G) : 𝓢(E, F) ->L[𝕜] 𝓢(E, G) :=
  mkCLM (fun f => L ∘ f) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
(fun f => (L.restrictScalars Real).contDiff.comp (f.smooth ⊤)) by
  intro ⟨k, n⟩
  use {⟨k, n⟩}, ‖L‖, by positivity
  intro f x
  simp only [Finset.sup_singleton, schwartzSeminormFamily_apply]
  calc
    _ = ‖x‖ ^ k * ‖(L.restrictScalars Real).compContinuousMultilinearMap
        (iteratedFDeriv Real n f x)‖ := by
      congr
      exact (L.restrictScalars Real).iteratedFDeriv_comp_left f.smooth'.contDiffAt (mod_cast le_top)
    _ <= ‖x‖ ^ k * (‖L‖ * ‖iteratedFDeriv Real n f x‖) := by
      gcongr
      apply (L.restrictScalars Real).norm_compContinuousMultilinearMap_le
    _ = ‖L‖ * (‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖) := by ring
    _ <= ‖L‖ * (SchwartzMap.seminorm 𝕜 k n) f := by
      grw [le_seminorm 𝕜 k n f x]

@[simp]
/--
theorem `postcompCLM_apply` / 定理 `postcompCLM_apply`

English:
theorem postcompCLM_apply
  given: (L : F ->L[𝕜] G) (f : 𝓢(E, F)) (x : E)
  statement: f.postcompCLM L x = L (f x)
  proof: rfl

@[simp]

中文:
定理 postcompCLM_apply
  条件: (L : F ->L[𝕜] G) (f : 𝓢(E, F)) (x : E)
  结论: f.postcompCLM L x = L (f x)
  证明: rfl

@[simp]
-/
theorem postcompCLM_apply (L : F ->L[𝕜] G) (f : 𝓢(E, F)) (x : E) : f.postcompCLM L x = L (f x) :=
  rfl

@[simp]
/--
theorem `postcompCLM_postcompCLM` / 定理 `postcompCLM_postcompCLM`

English:
theorem postcompCLM_postcompCLM
  given: (L₁ : F ->L[𝕜] G) (L₂ : G ->L[𝕜] H) (f : 𝓢(E, F))
  proof: rfl

中文:
定理 postcompCLM_postcompCLM
  条件: (L₁ : F ->L[𝕜] G) (L₂ : G ->L[𝕜] H) (f : 𝓢(E, F))
  证明: rfl
-/
theorem postcompCLM_postcompCLM (L₁ : F ->L[𝕜] G) (L₂ : G ->L[𝕜] H) (f : 𝓢(E, F)) :
  (f.postcompCLM L₁).postcompCLM L₂ = f.postcompCLM (L₂ ∘L L₁) := rfl

end Postcomp

section Translate

variable [RCLike 𝕜] [NormedSpace 𝕜 F]

variable (𝕜) in
/--
Definition of `compSubConstCLM` / `compSubConstCLM` 的定义

English:
definition compSubConstCLM
  signature: (a : E)
  body: compCLMOfAntilipschitz (g := fun x => x - a) (K := 1) 𝕜 (by fun_prop)
    (fun _ _ => by simp [edist_dist, dist_eq_norm])

@[simp]

中文:
定义 compSubConstCLM
  签名: (a : E)
  定义体: compCLMOfAntilipschitz (g := fun x => x - a) (K := 1) 𝕜 (by fun_prop)
    (fun _ _ => by simp [edist_dist, dist_eq_norm])

@[simp]

Depends on / 依赖: compCLMOfAntilipschitz, dist_eq_norm, edist_dist, fun_prop
-/
def compSubConstCLM (a : E) : 𝓢(E, F) ->L[𝕜] 𝓢(E, F) :=
  compCLMOfAntilipschitz (g := fun x => x - a) (K := 1) 𝕜 (by fun_prop)
    (fun _ _ => by simp [edist_dist, dist_eq_norm])

@[simp]
/--
theorem `compSubConstCLM_apply` / 定理 `compSubConstCLM_apply`

English:
theorem compSubConstCLM_apply
  given: (f : 𝓢(E, F)) (a x : E)
  proof: rfl

@[simp]

中文:
定理 compSubConstCLM_apply
  条件: (f : 𝓢(E, F)) (a x : E)
  证明: rfl

@[simp]
-/
theorem compSubConstCLM_apply (f : 𝓢(E, F)) (a x : E) :
    f.compSubConstCLM 𝕜 a x = f (x - a) := rfl

@[simp]
/--
theorem `compSubConstCLM_zero` / 定理 `compSubConstCLM_zero`

English:
theorem compSubConstCLM_zero
  statement: compSubConstCLM 𝕜 (0 : E) (F := F) = ContinuousLinearMap.id _ _
  proof: by
  ext f x
  simp

@[simp]

中文:
定理 compSubConstCLM_zero
  结论: compSubConstCLM 𝕜 (0 : E) (F := F) = ContinuousLinearMap.id _ _
  证明: by
  ext f x
  simp

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id
-/
theorem compSubConstCLM_zero : compSubConstCLM 𝕜 (0 : E) (F := F) = ContinuousLinearMap.id _ _ := by
  ext f x
  simp

@[simp]
/--
theorem `compSubConstCLM_comp` / 定理 `compSubConstCLM_comp`

English:
theorem compSubConstCLM_comp
  given: (f : 𝓢(E, F)) (a b : E)
  proof: by
  ext x
  simp only [compSubConstCLM_apply]
  congr 1
  exact (sub_add_eq_sub_sub_swap x a b).symm

中文:
定理 compSubConstCLM_comp
  条件: (f : 𝓢(E, F)) (a b : E)
  证明: by
  ext x
  simp only [compSubConstCLM_apply]
  congr 1
  exact (sub_add_eq_sub_sub_swap x a b).symm

Depends on / 依赖: compSubConstCLM_apply, sub_add_eq_sub_sub_swap
-/
theorem compSubConstCLM_comp (f : 𝓢(E, F)) (a b : E) :
    (f.compSubConstCLM 𝕜 a).compSubConstCLM 𝕜 b = f.compSubConstCLM 𝕜 (a + b) := by
  ext x
  simp only [compSubConstCLM_apply]
  congr 1
  exact (sub_add_eq_sub_sub_swap x a b).symm

end Translate

section Integration

/-! ### Integration -/


open Real Complex Filter MeasureTheory MeasureTheory.Measure Module

variable [RCLike 𝕜]
variable [NormedAddCommGroup D] [NormedSpace Real D]
variable [NormedAddCommGroup V] [NormedSpace Real V] [NormedSpace 𝕜 V]
variable [MeasurableSpace D]

variable {μ : Measure D} [hμ : HasTemperateGrowth μ]

attribute [local instance 101] secondCountableTopologyEither_of_left

variable (𝕜 μ) in
/--
lemma `integral_pow_mul_iteratedFDeriv_le` / 引理 `integral_pow_mul_iteratedFDeriv_le`

English:
lemma integral_pow_mul_iteratedFDeriv_le
  given: (f : 𝓢(D, V)) (k n : Nat)
  proof: integral_pow_mul_le_of_le_of_pow_mul_le (norm_iteratedFDeriv_le_seminorm Real _ _)
    (le_seminorm Real _ _ _)

中文:
引理 integral_pow_mul_iteratedFDeriv_le
  条件: (f : 𝓢(D, V)) (k n : 自然数)
  证明: integral_pow_mul_le_of_le_of_pow_mul_le (norm_iteratedFDeriv_le_seminorm Real _ _)
    (le_seminorm Real _ _ _)

Depends on / 依赖: integral_pow_mul_le_of_le_of_pow_mul_le, le_seminorm, norm_iteratedFDeriv_le_seminorm
-/
lemma integral_pow_mul_iteratedFDeriv_le (f : 𝓢(D, V)) (k n : Nat) :
    ∫ x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖ ∂μ <= 2 ^ μ.integrablePower *
      (∫ x, (1 + ‖x‖) ^ (- (μ.integrablePower : Real)) ∂μ) *
        (SchwartzMap.seminorm 𝕜 0 n f + SchwartzMap.seminorm 𝕜 (k + μ.integrablePower) n f) :=
  integral_pow_mul_le_of_le_of_pow_mul_le (norm_iteratedFDeriv_le_seminorm Real _ _)
    (le_seminorm Real _ _ _)

variable [BorelSpace D] [SecondCountableTopology D]

variable (μ) in
/--
lemma `integrable_pow_mul_iteratedFDeriv` / 引理 `integrable_pow_mul_iteratedFDeriv`

English:
lemma integrable_pow_mul_iteratedFDeriv
  proof: integrable_of_le_of_pow_mul_le (norm_iteratedFDeriv_le_seminorm Real _ _) (le_seminorm Real _ _ _)
    ((f.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top)).aestronglyMeasurable

中文:
引理 integrable_pow_mul_iteratedFDeriv
  证明: integrable_of_le_of_pow_mul_le (norm_iteratedFDeriv_le_seminorm Real _ _) (le_seminorm Real _ _ _)
    ((f.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top)).aestronglyMeasurable

Depends on / 依赖: aestronglyMeasurable, continuous_iteratedFDeriv, f.smooth, integrable_of_le_of_pow_mul_le, le_seminorm, le_top, mod_cast, norm_iteratedFDeriv_le_seminorm, smooth
-/
lemma integrable_pow_mul_iteratedFDeriv
    (f : 𝓢(D, V))
    (k n : Nat) : Integrable (fun x => ‖x‖ ^ k * ‖iteratedFDeriv Real n f x‖) μ :=
  integrable_of_le_of_pow_mul_le (norm_iteratedFDeriv_le_seminorm Real _ _) (le_seminorm Real _ _ _)
    ((f.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top)).aestronglyMeasurable

variable (μ) in
/--
lemma `integrable_pow_mul` / 引理 `integrable_pow_mul`

English:
lemma integrable_pow_mul
  statement: (f : 𝓢(D, V))
  proof: by
  convert! integrable_pow_mul_iteratedFDeriv μ f k 0 with x
  simp

@[fun_prop]

中文:
引理 integrable_pow_mul
  结论: (f : 𝓢(D, V))
  证明: by
  convert! integrable_pow_mul_iteratedFDeriv μ f k 0 with x
  simp

@[fun_prop]

Depends on / 依赖: convert, integrable_pow_mul_iteratedFDeriv
-/
lemma integrable_pow_mul (f : 𝓢(D, V))
    (k : Nat) : Integrable (fun x => ‖x‖ ^ k * ‖f x‖) μ := by
  convert! integrable_pow_mul_iteratedFDeriv μ f k 0 with x
  simp

@[fun_prop]
/--
lemma `integrable` / 引理 `integrable`

English:
lemma integrable
  given: (f : 𝓢(D, V))
  statement: Integrable f μ
  proof: (f.integrable_pow_mul μ 0).mono f.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun _ => by simp))

中文:
引理 integrable
  条件: (f : 𝓢(D, V))
  结论: 整数egrable f μ
  证明: (f.integrable_pow_mul μ 0).mono f.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun _ => by simp))

Depends on / 依赖: Eventually, Eventually.of_forall, aestronglyMeasurable, continuous, f.continuous.aestronglyMeasurable, f.integrable_pow_mul, integrable_pow_mul, of_forall
-/
lemma integrable (f : 𝓢(D, V)) : Integrable f μ :=
  (f.integrable_pow_mul μ 0).mono f.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun _ => by simp))

variable (𝕜 μ) in
/--
Definition of `integralCLM` / `integralCLM` 的定义

English:
definition integralCLM
  signature: : 𝓢(D, V) ->L[𝕜] V
  body: by
  refine mkCLMtoNormedSpace (∫ x, · x ∂μ)
    (fun f g => integral_add f.integrable g.integrable) (integral_smul · ·) ?_
  rcases hμ.exists_integrable with ⟨n, h⟩
  let m := (n, 0)
  use Finset.Iic m, 2 ^ n * ∫ x : D, (1 + ‖x‖) ^ (- (n : Real)) ∂μ
  refine ⟨by positivity, fun f => (norm_integral_

中文:
定义 integralCLM
  签名: : 𝓢(D, V) ->L[𝕜] V
  定义体: by
  refine mkCLMtoNormedSpace (∫ x, · x ∂μ)
    (fun f g => integral_add f.integrable g.integrable) (integral_smul · ·) ?_
  rcases hμ.exists_integrable with ⟨n, h⟩
  let m := (n, 0)
  use Finset.Iic m, 2 ^ n * ∫ x : D, (1 + ‖x‖) ^ (- (n : Real)) ∂μ
  refine ⟨by positivity, fun f => (norm_integral_

Depends on / 依赖: Finset, Finset.Iic, SchwartzMap, SchwartzMap.seminorm, exists_integrable, f.integrable, g.integrable, integrable, integral_add, integral_smul, mkCLMtoNormedSpace, norm_integral_le_integral_norm, rpow_neg, seminorm
-/
def integralCLM : 𝓢(D, V) ->L[𝕜] V := by
  refine mkCLMtoNormedSpace (∫ x, · x ∂μ)
    (fun f g => integral_add f.integrable g.integrable) (integral_smul · ·) ?_
  rcases hμ.exists_integrable with ⟨n, h⟩
  let m := (n, 0)
  use Finset.Iic m, 2 ^ n * ∫ x : D, (1 + ‖x‖) ^ (- (n : Real)) ∂μ
  refine ⟨by positivity, fun f => (norm_integral_le_integral_norm f).trans ?_⟩
  have h' : forall x, ‖f x‖ <= (1 + ‖x‖) ^ (-(n : Real)) *
      (2 ^ n * ((Finset.Iic m).sup (fun m' => SchwartzMap.seminorm 𝕜 m'.1 m'.2) f)) := by
    intro x
    rw [rpow_neg (by positivity)]; rw [← div_eq_inv_mul]; rw [le_div_iff₀' (by positivity)]; rw [rpow_natCast]
    simpa using one_add_le_sup_seminorm_apply (m := m) (k := n) (n := 0) le_rfl le_rfl f x
  apply (integral_mono (by simpa using f.integrable_pow_mul μ 0) _ h').trans
  · unfold schwartzSeminormFamily
    rw [integral_mul_const]; rw [← mul_assoc]; rw [mul_comm (2 ^ n)]
  apply h.mul_const

variable (𝕜) in
@[simp]
/--
lemma `integralCLM_apply` / 引理 `integralCLM_apply`

English:
lemma integralCLM_apply
  given: (f : 𝓢(D, V))
  statement: integralCLM 𝕜 μ f = ∫ x, f x ∂μ
  proof: by rfl

中文:
引理 integralCLM_apply
  条件: (f : 𝓢(D, V))
  结论: integralCLM 𝕜 μ f = ∫ x, f x ∂μ
  证明: by rfl
-/
lemma integralCLM_apply (f : 𝓢(D, V)) : integralCLM 𝕜 μ f = ∫ x, f x ∂μ := by rfl

end Integration

section BoundedContinuousFunction

/-! ### Inclusion into the space of bounded continuous functions -/


open scoped BoundedContinuousFunction

/--
Instance `instBoundedContinuousMapClass` / 实例 `instBoundedContinuousMapClass`

English:
instance instBoundedContinuousMapClass
  signature: : BoundedContinuousMapClass 𝓢(E, F) E F where
  body: instContinuousMapClass
  map_bounded := fun f => ⟨2 * (SchwartzMap.seminorm Real 0 0) f,
    (BoundedContinuousFunction.dist_le_two_norm' (norm_le_seminorm Real f))⟩

中文:
实例 instBoundedContinuousMapClass
  签名: : BoundedContinuousMapClass 𝓢(E, F) E F where
  定义体: instContinuousMapClass
  map_bounded := fun f => ⟨2 * (SchwartzMap.seminorm Real 0 0) f,
    (BoundedContinuousFunction.dist_le_two_norm' (norm_le_seminorm Real f))⟩

Depends on / 依赖: instContinuousMapClass
-/
instance instBoundedContinuousMapClass : BoundedContinuousMapClass 𝓢(E, F) E F where
  __ := instContinuousMapClass
  map_bounded := fun f => ⟨2 * (SchwartzMap.seminorm Real 0 0) f,
    (BoundedContinuousFunction.dist_le_two_norm' (norm_le_seminorm Real f))⟩

/--
Definition of `toBoundedContinuousFunction` / `toBoundedContinuousFunction` 的定义

English:
definition toBoundedContinuousFunction
  signature: (f : 𝓢(E, F))
  body: BoundedContinuousFunction.ofNormedAddCommGroup f (SchwartzMap.continuous f)
    (SchwartzMap.seminorm Real 0 0 f) (norm_le_seminorm Real f)

@[simp]

中文:
定义 toBoundedContinuousFunction
  签名: (f : 𝓢(E, F))
  定义体: BoundedContinuousFunction.ofNormedAddCommGroup f (SchwartzMap.continuous f)
    (SchwartzMap.seminorm Real 0 0 f) (norm_le_seminorm Real f)

@[simp]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.ofNormedAddCommGroup, SchwartzMap, SchwartzMap.continuous, SchwartzMap.seminorm, continuous, norm_le_seminorm, ofNormedAddCommGroup, seminorm
-/
def toBoundedContinuousFunction (f : 𝓢(E, F)) : E ->ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup f (SchwartzMap.continuous f)
    (SchwartzMap.seminorm Real 0 0 f) (norm_le_seminorm Real f)

@[simp]
/--
theorem `toBoundedContinuousFunction_apply` / 定理 `toBoundedContinuousFunction_apply`

English:
theorem toBoundedContinuousFunction_apply
  given: (f : 𝓢(E, F)) (x : E)
  proof: rfl

中文:
定理 toBoundedContinuousFunction_apply
  条件: (f : 𝓢(E, F)) (x : E)
  证明: rfl
-/
theorem toBoundedContinuousFunction_apply (f : 𝓢(E, F)) (x : E) :
    f.toBoundedContinuousFunction x = f x :=
  rfl

/--
Definition of `toContinuousMap` / `toContinuousMap` 的定义

English:
definition toContinuousMap
  signature: (f : 𝓢(E, F))
  body: f.toBoundedContinuousFunction.toContinuousMap

中文:
定义 toContinuousMap
  签名: (f : 𝓢(E, F))
  定义体: f.toBoundedContinuousFunction.toContinuousMap

Depends on / 依赖: f.toBoundedContinuousFunction.toContinuousMap, toBoundedContinuousFunction, toContinuousMap
-/
def toContinuousMap (f : 𝓢(E, F)) : C(E, F) :=
  f.toBoundedContinuousFunction.toContinuousMap

/--
theorem `norm_toBoundedContinuousFunction_le` / 定理 `norm_toBoundedContinuousFunction_le`

English:
theorem norm_toBoundedContinuousFunction_le
  given: (f : 𝓢(E, F))
  proof: BoundedContinuousFunction.norm_ofNormedAddCommGroup_le f.continuous (by positivity) _

中文:
定理 norm_toBoundedContinuousFunction_le
  条件: (f : 𝓢(E, F))
  证明: BoundedContinuousFunction.norm_ofNormedAddCommGroup_le f.continuous (by positivity) _

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.norm_ofNormedAddCommGroup_le, continuous, f.continuous, norm_ofNormedAddCommGroup_le
-/
theorem norm_toBoundedContinuousFunction_le (f : 𝓢(E, F)) :
    ‖f.toBoundedContinuousFunction‖ <= SchwartzMap.seminorm Real 0 0 f :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le f.continuous (by positivity) _

variable (𝕜 E F)
variable [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass Real 𝕜 F]

/--
Definition of `toBoundedContinuousFunctionCLM` / `toBoundedContinuousFunctionCLM` 的定义

English:
definition toBoundedContinuousFunctionCLM
  signature: : 𝓢(E, F) ->L[𝕜] E ->ᵇ F
  body: mkCLMtoNormedSpace toBoundedContinuousFunction (by intros; ext; simp) (by intros; ext; simp)
    (⟨{0}, 1, zero_le_one, by
      simpa [BoundedContinuousFunction.norm_le (apply_nonneg _ _)] using norm_le_seminorm 𝕜 ⟩)

@[simp]

中文:
定义 toBoundedContinuousFunctionCLM
  签名: : 𝓢(E, F) ->L[𝕜] E ->ᵇ F
  定义体: mkCLMtoNormedSpace toBoundedContinuousFunction (by intros; ext; simp) (by intros; ext; simp)
    (⟨{0}, 1, zero_le_one, by
      simpa [BoundedContinuousFunction.norm_le (apply_nonneg _ _)] using norm_le_seminorm 𝕜 ⟩)

@[simp]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.norm_le, apply_nonneg, intros, mkCLMtoNormedSpace, norm_le, norm_le_seminorm, toBoundedContinuousFunction, zero_le_one
-/
def toBoundedContinuousFunctionCLM : 𝓢(E, F) ->L[𝕜] E ->ᵇ F :=
  mkCLMtoNormedSpace toBoundedContinuousFunction (by intros; ext; simp) (by intros; ext; simp)
    (⟨{0}, 1, zero_le_one, by
      simpa [BoundedContinuousFunction.norm_le (apply_nonneg _ _)] using norm_le_seminorm 𝕜 ⟩)

@[simp]
/--
theorem `toBoundedContinuousFunctionCLM_apply` / 定理 `toBoundedContinuousFunctionCLM_apply`

English:
theorem toBoundedContinuousFunctionCLM_apply
  given: (f : 𝓢(E, F)) (x : E)
  proof: rfl

中文:
定理 toBoundedContinuousFunctionCLM_apply
  条件: (f : 𝓢(E, F)) (x : E)
  证明: rfl
-/
theorem toBoundedContinuousFunctionCLM_apply (f : 𝓢(E, F)) (x : E) :
    toBoundedContinuousFunctionCLM 𝕜 E F f x = f x :=
  rfl

/--
theorem `toBoundedContinuousFunctionCLM_injective` / 定理 `toBoundedContinuousFunctionCLM_injective`

English:
theorem toBoundedContinuousFunctionCLM_injective
  proof: fun _ _ h => DFunLike.ext _ _ fun x => DFunLike.congr_fun h x

中文:
定理 toBoundedContinuousFunctionCLM_injective
  证明: fun _ _ h => DFunLike.ext _ _ fun x => DFunLike.congr_fun h x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, DFunLike.ext, congr_fun
-/
theorem toBoundedContinuousFunctionCLM_injective :
    Function.Injective (toBoundedContinuousFunctionCLM .. : 𝓢(E, F) ->L[𝕜] E ->ᵇ F) :=
  fun _ _ h => DFunLike.ext _ _ fun x => DFunLike.congr_fun h x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T3Space 𝓢(E, F)
  body: suffices T2Space 𝓢(E, F) from inferInstance
  .of_injective_continuous (toBoundedContinuousFunctionCLM_injective Real ..)
    (ContinuousLinearMap.continuous _)

中文:
实例 :
  签名: T3Space 𝓢(E, F)
  定义体: suffices T2Space 𝓢(E, F) from inferInstance
  .of_injective_continuous (toBoundedContinuousFunctionCLM_injective Real ..)
    (ContinuousLinearMap.continuous _)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.continuous, T2Space, continuous, of_injective_continuous, toBoundedContinuousFunctionCLM_injective
-/
instance : T3Space 𝓢(E, F) :=
  suffices T2Space 𝓢(E, F) from inferInstance
  .of_injective_continuous (toBoundedContinuousFunctionCLM_injective Real ..)
    (ContinuousLinearMap.continuous _)

end BoundedContinuousFunction

section ZeroAtInfty

open scoped ZeroAtInfty

variable [ProperSpace E]

/--
Instance `instZeroAtInftyContinuousMapClass` / 实例 `instZeroAtInftyContinuousMapClass`

English:
instance instZeroAtInftyContinuousMapClass
  signature: : ZeroAtInftyContinuousMapClass 𝓢(E, F) E F where
  body: instContinuousMapClass
  zero_at_infty := tendsto_cocompact

中文:
实例 instZeroAtInftyContinuousMapClass
  签名: : ZeroAtInftyContinuousMapClass 𝓢(E, F) E F where
  定义体: instContinuousMapClass
  zero_at_infty := tendsto_cocompact

Depends on / 依赖: instContinuousMapClass
-/
instance instZeroAtInftyContinuousMapClass : ZeroAtInftyContinuousMapClass 𝓢(E, F) E F where
  __ := instContinuousMapClass
  zero_at_infty := tendsto_cocompact

/--
Definition of `toZeroAtInfty` / `toZeroAtInfty` 的定义

English:
definition toZeroAtInfty
  signature: (f : 𝓢(E, F))
  body: f
  zero_at_infty' := tendsto_cocompact f

中文:
定义 toZeroAtInfty
  签名: (f : 𝓢(E, F))
  定义体: f
  zero_at_infty' := tendsto_cocompact f
-/
def toZeroAtInfty (f : 𝓢(E, F)) : C₀(E, F) where
  toFun := f
  zero_at_infty' := tendsto_cocompact f

/--
theorem `toZeroAtInfty_apply` / 定理 `toZeroAtInfty_apply`

English:
theorem toZeroAtInfty_apply
  given: (f : 𝓢(E, F)) (x : E)
  statement: f.toZeroAtInfty x = f x
  proof: rfl

中文:
定理 toZeroAtInfty_apply
  条件: (f : 𝓢(E, F)) (x : E)
  结论: f.toZeroAtInfty x = f x
  证明: rfl
-/
@[simp] theorem toZeroAtInfty_apply (f : 𝓢(E, F)) (x : E) : f.toZeroAtInfty x = f x :=
  rfl

/--
theorem `toZeroAtInfty_toBCF` / 定理 `toZeroAtInfty_toBCF`

English:
theorem toZeroAtInfty_toBCF
  given: (f : 𝓢(E, F))
  proof: rfl

中文:
定理 toZeroAtInfty_toBCF
  条件: (f : 𝓢(E, F))
  证明: rfl
-/
@[simp] theorem toZeroAtInfty_toBCF (f : 𝓢(E, F)) :
    f.toZeroAtInfty.toBCF = f.toBoundedContinuousFunction :=
  rfl

/--
theorem `norm_toZeroAtInfty` / 定理 `norm_toZeroAtInfty`

English:
theorem norm_toZeroAtInfty
  given: (f : 𝓢(E, F))
  proof: by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]; rw [toZeroAtInfty_toBCF]

中文:
定理 norm_toZeroAtInfty
  条件: (f : 𝓢(E, F))
  证明: by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]; rw [toZeroAtInfty_toBCF]
-/
@[simp] theorem norm_toZeroAtInfty (f : 𝓢(E, F)) :
    ‖f.toZeroAtInfty‖ = ‖f.toBoundedContinuousFunction‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]; rw [toZeroAtInfty_toBCF]

variable (𝕜 E F)
variable [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass Real 𝕜 F]

/--
Definition of `toZeroAtInftyCLM` / `toZeroAtInftyCLM` 的定义

English:
definition toZeroAtInftyCLM
  signature: : 𝓢(E, F) ->L[𝕜] C₀(E, F)
  body: mkCLMtoNormedSpace toZeroAtInfty (by intros; ext; simp) (by intros; ext; simp)
    (⟨{0}, 1, zero_le_one, by simpa [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
      BoundedContinuousFunction.norm_le (apply_nonneg _ _)] using norm_le_seminorm 𝕜 ⟩)

中文:
定义 toZeroAtInftyCLM
  签名: : 𝓢(E, F) ->L[𝕜] C₀(E, F)
  定义体: mkCLMtoNormedSpace toZeroAtInfty (by intros; ext; simp) (by intros; ext; simp)
    (⟨{0}, 1, zero_le_one, by simpa [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
      BoundedContinuousFunction.norm_le (apply_nonneg _ _)] using norm_le_seminorm 𝕜 ⟩)

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.norm_le, ZeroAtInftyContinuousMap, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, apply_nonneg, intros, mkCLMtoNormedSpace, norm_le, norm_le_seminorm, norm_toBCF_eq_norm, toZeroAtInfty, zero_le_one
-/
def toZeroAtInftyCLM : 𝓢(E, F) ->L[𝕜] C₀(E, F) :=
  mkCLMtoNormedSpace toZeroAtInfty (by intros; ext; simp) (by intros; ext; simp)
    (⟨{0}, 1, zero_le_one, by simpa [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
      BoundedContinuousFunction.norm_le (apply_nonneg _ _)] using norm_le_seminorm 𝕜 ⟩)

/--
theorem `toZeroAtInftyCLM_apply` / 定理 `toZeroAtInftyCLM_apply`

English:
theorem toZeroAtInftyCLM_apply
  given: (f : 𝓢(E, F)) (x : E)
  statement: toZeroAtInftyCLM 𝕜 E F f x = f x
  proof: rfl

中文:
定理 toZeroAtInftyCLM_apply
  条件: (f : 𝓢(E, F)) (x : E)
  结论: toZeroAtInftyCLM 𝕜 E F f x = f x
  证明: rfl
-/
@[simp] theorem toZeroAtInftyCLM_apply (f : 𝓢(E, F)) (x : E) : toZeroAtInftyCLM 𝕜 E F f x = f x :=
  rfl

end ZeroAtInfty

section Lp

/-! ### Inclusion into L^p space -/

open MeasureTheory
open scoped NNReal ENNReal

variable [NormedAddCommGroup D] [MeasurableSpace D] [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass Real 𝕜 F]

variable (𝕜 F) in
/--
theorem `eLpNorm_le_seminorm` / 定理 `eLpNorm_le_seminorm`

English:
theorem eLpNorm_le_seminorm
  statement: (p : Real>=0∞) (μ : Measure E := by volume_tac)
  proof: by
  -- Apply Hölder's inequality `‖f‖_p ≤ ‖f₁‖_p * ‖f₂‖_∞` to obtain the `L^p` norm of `f = f₁ • f₂`
  -- using `f₁ = (1 + ‖x‖) ^ (-k)` and `f₂ = (1 + ‖x‖) ^ k • f x`.
  rcases hμ.exists_eLpNorm_lt_top p with ⟨k, hk⟩
  refine ⟨k, (eLpNorm (fun x => (1 + ‖x‖) ^ (-k : Real)) p μ).toNNReal * 2 ^ k, fu

中文:
定理 eLpNorm_le_seminorm
  结论: (p : 实数>=0∞) (μ : Measure E := by volume_tac)
  证明: by
  -- Apply Hölder's inequality `‖f‖_p ≤ ‖f₁‖_p * ‖f₂‖_∞` to obtain the `L^p` norm of `f = f₁ • f₂`
  -- using `f₁ = (1 + ‖x‖) ^ (-k)` and `f₂ = (1 + ‖x‖) ^ k • f x`.
  rcases hμ.exists_eLpNorm_lt_top p with ⟨k, hk⟩
  refine ⟨k, (eLpNorm (fun x => (1 + ‖x‖) ^ (-k : Real)) p μ).toNNReal * 2 ^ k, fu

Depends on / 依赖: ENNReal, ENNReal.ofReal, Finset, Finset.Iic, HasTemperateGrowth, eLpNorm, ofReal, schwartzSeminormFamily, volume_tac
-/
theorem eLpNorm_le_seminorm (p : Real>=0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] :
    exists (k : Nat) (C : Real>=0), forall (f : 𝓢(E, F)), eLpNorm f p μ <=
      C * ENNReal.ofReal ((Finset.Iic (k, 0)).sup (schwartzSeminormFamily 𝕜 E F) f) := by
  -- Apply Hölder's inequality `‖f‖_p ≤ ‖f₁‖_p * ‖f₂‖_∞` to obtain the `L^p` norm of `f = f₁ • f₂`
  -- using `f₁ = (1 + ‖x‖) ^ (-k)` and `f₂ = (1 + ‖x‖) ^ k • f x`.
  rcases hμ.exists_eLpNorm_lt_top p with ⟨k, hk⟩
  refine ⟨k, (eLpNorm (fun x => (1 + ‖x‖) ^ (-k : Real)) p μ).toNNReal * 2 ^ k, fun f => ?_⟩
  have h_one_add (x : E) : 0 < 1 + ‖x‖ := lt_add_of_pos_of_le zero_lt_one (norm_nonneg x)
  calc eLpNorm (⇑f) p μ
  _ = eLpNorm ((fun x : E => (1 + ‖x‖) ^ (-k : Real)) • fun x => (1 + ‖x‖) ^ k • f x) p μ := by
    refine congrArg (eLpNorm · p μ) (funext fun x => ?_)
    simp [(h_one_add x).ne']
  _ <= eLpNorm (fun x => (1 + ‖x‖) ^ (-k : Real)) p μ * eLpNorm (fun x => (1 + ‖x‖) ^ k • f x) ⊤ μ := by
    refine eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top p _ ?_
    refine Continuous.aestronglyMeasurable ?_
    exact .rpow_const (by fun_prop) fun x => .inl (h_one_add x).ne'
  _ <= eLpNorm (fun x => (1 + ‖x‖) ^ (-k : Real)) p μ *
      (2 ^ k * ENNReal.ofReal (((Finset.Iic (k, 0)).sup (schwartzSeminormFamily 𝕜 E F)) f)) := by
    gcongr
    refine eLpNormEssSup_le_of_ae_nnnorm_bound (ae_of_all μ fun x => ?_)
    rw [← norm_toNNReal]; rw [Real.toNNReal_le_iff_le_coe]
    simpa [norm_smul, abs_of_nonneg (h_one_add x).le] using!
      one_add_le_sup_seminorm_apply (m := (k, 0)) (le_refl k) (le_refl 0) f x
  _ = _ := by
    rw [ENNReal.coe_mul]; rw [ENNReal.coe_toNNReal hk.ne]
    simp only [ENNReal.coe_pow, ENNReal.coe_ofNat]
    ring

/--
theorem `eLpNorm_lt_top` / 定理 `eLpNorm_lt_top`

English:
theorem eLpNorm_lt_top
  statement: (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E := by volume_tac)
  proof: by
  rcases eLpNorm_le_seminorm Real F p μ with ⟨k, C, hC⟩
  exact lt_of_le_of_lt (hC f) (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)

中文:
定理 eLpNorm_lt_top
  结论: (f : 𝓢(E, F)) (p : 实数>=0∞) (μ : Measure E := by volume_tac)
  证明: by
  rcases eLpNorm_le_seminorm Real F p μ with ⟨k, C, hC⟩
  exact lt_of_le_of_lt (hC f) (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, ENNReal.mul_lt_top, ENNReal.ofReal_lt_top, HasTemperateGrowth, coe_lt_top, eLpNorm, eLpNorm_le_seminorm, lt_of_le_of_lt, mul_lt_top, ofReal_lt_top, volume_tac
-/
theorem eLpNorm_lt_top (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] : eLpNorm f p μ < ⊤ := by
  rcases eLpNorm_le_seminorm Real F p μ with ⟨k, C, hC⟩
  exact lt_of_le_of_lt (hC f) (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)

variable [SecondCountableTopologyEither E F]

/--
theorem `memLp_top` / 定理 `memLp_top`

English:
theorem memLp_top
  given: (f : 𝓢(E, F)) (μ : Measure E := by volume_tac)
  statement: MemLp f ⊤ μ
  proof: by
  rcases f.decay 0 0 with ⟨C, _, hC⟩
  refine memLp_top_of_bound f.continuous.aestronglyMeasurable C (ae_of_all μ fun x => ?_)
  simpa using hC x

中文:
定理 memLp_top
  条件: (f : 𝓢(E, F)) (μ : Measure E := by volume_tac)
  结论: MemLp f ⊤ μ
  证明: by
  rcases f.decay 0 0 with ⟨C, _, hC⟩
  refine memLp_top_of_bound f.continuous.aestronglyMeasurable C (ae_of_all μ fun x => ?_)
  simpa using hC x

Depends on / 依赖: ae_of_all, aestronglyMeasurable, continuous, f.continuous.aestronglyMeasurable, f.decay, memLp_top_of_bound, volume_tac
-/
theorem memLp_top (f : 𝓢(E, F)) (μ : Measure E := by volume_tac) : MemLp f ⊤ μ := by
  rcases f.decay 0 0 with ⟨C, _, hC⟩
  refine memLp_top_of_bound f.continuous.aestronglyMeasurable C (ae_of_all μ fun x => ?_)
  simpa using hC x

/--
theorem `memLp` / 定理 `memLp`

English:
theorem memLp
  statement: (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E := by volume_tac)
  proof: ⟨f.continuous.aestronglyMeasurable, f.eLpNorm_lt_top p μ⟩

中文:
定理 memLp
  结论: (f : 𝓢(E, F)) (p : 实数>=0∞) (μ : Measure E := by volume_tac)
  证明: ⟨f.continuous.aestronglyMeasurable, f.eLpNorm_lt_top p μ⟩

Depends on / 依赖: HasTemperateGrowth, aestronglyMeasurable, continuous, eLpNorm_lt_top, f.continuous.aestronglyMeasurable, f.eLpNorm_lt_top, volume_tac
-/
theorem memLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] : MemLp f p μ :=
  ⟨f.continuous.aestronglyMeasurable, f.eLpNorm_lt_top p μ⟩

/--
Definition of `toLp` / `toLp` 的定义

English:
definition toLp
  signature: (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]
  body: (f.memLp p μ).toLp

中文:
定义 toLp
  签名: (f : 𝓢(E, F)) (p : 实数>=0∞) (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]
  定义体: (f.memLp p μ).toLp

Depends on / 依赖: HasTemperateGrowth, f.memLp, volume_tac
-/
def toLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth] :
    Lp F p μ := (f.memLp p μ).toLp

/--
Instance `instCoeToLp` / 实例 `instCoeToLp`

English:
instance instCoeToLp
  signature: {p : Real>=0∞} {μ : Measure E} [hμ : μ.HasTemperateGrowth]
  body: (SchwartzMap.toLp · p μ)

中文:
实例 instCoeToLp
  签名: {p : 实数>=0∞} {μ : Measure E} [hμ : μ.HasTemperateGrowth]
  定义体: (SchwartzMap.toLp · p μ)

Depends on / 依赖: SchwartzMap, SchwartzMap.toLp
-/
instance instCoeToLp {p : Real>=0∞} {μ : Measure E} [hμ : μ.HasTemperateGrowth] :
    Coe 𝓢(E, F) (Lp F p μ) where
  coe := (SchwartzMap.toLp · p μ)

/--
theorem `coeFn_toLp` / 定理 `coeFn_toLp`

English:
theorem coeFn_toLp
  statement: (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E := by volume_tac)
  proof: (f.memLp p μ).coeFn_toLp

中文:
定理 coeFn_toLp
  结论: (f : 𝓢(E, F)) (p : 实数>=0∞) (μ : Measure E := by volume_tac)
  证明: (f.memLp p μ).coeFn_toLp

Depends on / 依赖: HasTemperateGrowth, coeFn_toLp, f.memLp, f.toLp, volume_tac
-/
theorem coeFn_toLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] : f.toLp p μ =ᵐ[μ] f := (f.memLp p μ).coeFn_toLp

/--
theorem `norm_toLp` / 定理 `norm_toLp`

English:
theorem norm_toLp
  given: {f : 𝓢(E, F)} {p : Real>=0∞} {μ : Measure E} [hμ : μ.HasTemperateGrowth]
  proof: by
  rw [Lp.norm_def]; rw [eLpNorm_congr_ae (coeFn_toLp f p μ)]

中文:
定理 norm_toLp
  条件: {f : 𝓢(E, F)} {p : 实数>=0∞} {μ : Measure E} [hμ : μ.HasTemperateGrowth]
  证明: by
  rw [Lp.norm_def]; rw [eLpNorm_congr_ae (coeFn_toLp f p μ)]

Depends on / 依赖: Lp.norm_def, coeFn_toLp, eLpNorm_congr_ae, norm_def
-/
theorem norm_toLp {f : 𝓢(E, F)} {p : Real>=0∞} {μ : Measure E} [hμ : μ.HasTemperateGrowth] :
    ‖f.toLp p μ‖ = ENNReal.toReal (eLpNorm f p μ) := by
  rw [Lp.norm_def]; rw [eLpNorm_congr_ae (coeFn_toLp f p μ)]

/--
theorem `norm_toLp'` / 定理 `norm_toLp'`

English:
theorem norm_toLp'
  statement: {f : 𝓢(E, F)} {p : Real>=0∞} {μ : Measure E} (hp₁ : p != 0) (hp₂ : p != ⊤)
  proof: by
  rw [norm_toLp]; rw [MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm hp₁ hp₂ (f.memLp p μ)]; rw [ENNReal.toReal_ofReal (by positivity)]

中文:
定理 norm_toLp'
  结论: {f : 𝓢(E, F)} {p : 实数>=0∞} {μ : Measure E} (hp₁ : p != 0) (hp₂ : p != ⊤)
  证明: by
  rw [norm_toLp]; rw [MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm hp₁ hp₂ (f.memLp p μ)]; rw [ENNReal.toReal_ofReal (by positivity)]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, MeasureTheory, MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm, eLpNorm_eq_integral_rpow_norm, f.memLp, norm_toLp, toReal_ofReal
-/
theorem norm_toLp' {f : 𝓢(E, F)} {p : Real>=0∞} {μ : Measure E} (hp₁ : p != 0) (hp₂ : p != ⊤)
    [hμ : μ.HasTemperateGrowth] :
    ‖f.toLp p μ‖ = (∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by
  rw [norm_toLp]; rw [MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm hp₁ hp₂ (f.memLp p μ)]; rw [ENNReal.toReal_ofReal (by positivity)]

/--
theorem `norm_toLp_one` / 定理 `norm_toLp_one`

English:
theorem norm_toLp_one
  given: {f : 𝓢(E, F)} {μ : Measure E} [hμ : μ.HasTemperateGrowth]
  proof: by
  simpa using norm_toLp' (p := 1) (by simp) (by simp)

中文:
定理 norm_toLp_one
  条件: {f : 𝓢(E, F)} {μ : Measure E} [hμ : μ.HasTemperateGrowth]
  证明: by
  simpa using norm_toLp' (p := 1) (by simp) (by simp)

Depends on / 依赖: norm_toLp
-/
theorem norm_toLp_one {f : 𝓢(E, F)} {μ : Measure E} [hμ : μ.HasTemperateGrowth] :
    ‖f.toLp 1 μ‖ = ∫ x, ‖f x‖ ∂μ := by
  simpa using norm_toLp' (p := 1) (by simp) (by simp)

/--
theorem `norm_toLp_top_le` / 定理 `norm_toLp_top_le`

English:
theorem norm_toLp_top_le
  given: {f : 𝓢(E, F)} {μ : Measure E} [hμ : μ.HasTemperateGrowth]
  proof: by
  rw [norm_toLp]; rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]; rw [ENNReal.ofReal_toReal (memLp_top f μ).eLpNorm_ne_top]
exact eLpNormEssSup_le_of_ae_bound .of_forall norm_le_seminorm Real f

中文:
定理 norm_toLp_top_le
  条件: {f : 𝓢(E, F)} {μ : Measure E} [hμ : μ.HasTemperateGrowth]
  证明: by
  rw [norm_toLp]; rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]; rw [ENNReal.ofReal_toReal (memLp_top f μ).eLpNorm_ne_top]
exact eLpNormEssSup_le_of_ae_bound .of_forall norm_le_seminorm Real f

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal_iff, ENNReal.ofReal_toReal, eLpNormEssSup_le_of_ae_bound, eLpNorm_ne_top, memLp_top, norm_le_seminorm, norm_toLp, ofReal_le_ofReal_iff, ofReal_toReal, of_forall
-/
theorem norm_toLp_top_le {f : 𝓢(E, F)} {μ : Measure E} [hμ : μ.HasTemperateGrowth] :
    ‖f.toLp ⊤ μ‖ <= SchwartzMap.seminorm Real 0 0 f := by
  rw [norm_toLp]; rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]; rw [ENNReal.ofReal_toReal (memLp_top f μ).eLpNorm_ne_top]
exact eLpNormEssSup_le_of_ae_bound .of_forall norm_le_seminorm Real f

/--
theorem `injective_toLp` / 定理 `injective_toLp`

English:
theorem injective_toLp
  statement: (p : Real>=0∞) (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]
  proof: fun f g => by simpa [toLp] using (Continuous.ae_eq_iff_eq μ f.continuous g.continuous).mp

中文:
定理 injective_toLp
  结论: (p : 实数>=0∞) (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]
  证明: fun f g => by simpa [toLp] using (Continuous.ae_eq_iff_eq μ f.continuous g.continuous).mp

Depends on / 依赖: Continuous, Continuous.ae_eq_iff_eq, Function, Function.Injective, HasTemperateGrowth, Injective, IsOpenPosMeasure, ae_eq_iff_eq, continuous, f.continuous, f.toLp, g.continuous, volume_tac
-/
theorem injective_toLp (p : Real>=0∞) (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]
    [μ.IsOpenPosMeasure] : Function.Injective (fun f : 𝓢(E, F) => f.toLp p μ) :=
  fun f g => by simpa [toLp] using (Continuous.ae_eq_iff_eq μ f.continuous g.continuous).mp

variable (𝕜 F) in
/--
theorem `norm_toLp_le_seminorm` / 定理 `norm_toLp_le_seminorm`

English:
theorem norm_toLp_le_seminorm
  statement: (p : Real>=0∞) (μ : Measure E := by volume_tac)
  proof: by
  rcases eLpNorm_le_seminorm 𝕜 F p μ with ⟨k, C, hC⟩
  refine ⟨k, C, C.coe_nonneg, fun f => ?_⟩
  rw [norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by simp [mul_nonneg]) ?_
  rw [ENNReal.ofReal_mul NNReal.zero_le_coe]
  simpa using hC f

中文:
定理 norm_toLp_le_seminorm
  结论: (p : 实数>=0∞) (μ : Measure E := by volume_tac)
  证明: by
  rcases eLpNorm_le_seminorm 𝕜 F p μ with ⟨k, C, hC⟩
  refine ⟨k, C, C.coe_nonneg, fun f => ?_⟩
  rw [norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by simp [mul_nonneg]) ?_
  rw [ENNReal.ofReal_mul NNReal.zero_le_coe]
  simpa using hC f

Depends on / 依赖: C.coe_nonneg, ENNReal, ENNReal.ofReal_mul, ENNReal.toReal_le_of_le_ofReal, Finset, Finset.Iic, HasTemperateGrowth, NNReal, NNReal.zero_le_coe, coe_nonneg, eLpNorm_le_seminorm, f.toLp, mul_nonneg, norm_toLp, ofReal_mul, schwartzSeminormFamily, toReal_le_of_le_ofReal, volume_tac, zero_le_coe
-/
theorem norm_toLp_le_seminorm (p : Real>=0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] :
    exists k C, 0 <= C ∧ forall (f : 𝓢(E, F)), ‖f.toLp p μ‖ <=
      C * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily 𝕜 E F) f := by
  rcases eLpNorm_le_seminorm 𝕜 F p μ with ⟨k, C, hC⟩
  refine ⟨k, C, C.coe_nonneg, fun f => ?_⟩
  rw [norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by simp [mul_nonneg]) ?_
  rw [ENNReal.ofReal_mul NNReal.zero_le_coe]
  simpa using hC f

variable (𝕜 F) in
/--
Definition of `toLpCLM` / `toLpCLM` 的定义

English:
definition toLpCLM
  signature: (p : Real>=0∞) [Fact (1 <= p)] (μ : Measure E := by volume_tac)
  body: mkCLMtoNormedSpace (fun f => f.toLp p μ) (fun _ _ => rfl) (fun _ _ => rfl) by
    rcases norm_toLp_le_seminorm 𝕜 F p μ with ⟨k, C, hC_pos, hC⟩
    exact ⟨Finset.Iic (k, 0), C, hC_pos, hC⟩

中文:
定义 toLpCLM
  签名: (p : 实数>=0∞) [Fact (1 <= p)] (μ : Measure E := by volume_tac)
  定义体: mkCLMtoNormedSpace (fun f => f.toLp p μ) (fun _ _ => rfl) (fun _ _ => rfl) by
    rcases norm_toLp_le_seminorm 𝕜 F p μ with ⟨k, C, hC_pos, hC⟩
    exact ⟨Finset.Iic (k, 0), C, hC_pos, hC⟩

Depends on / 依赖: Finset, Finset.Iic, HasTemperateGrowth, f.toLp, hC_pos, mkCLMtoNormedSpace, norm_toLp_le_seminorm, volume_tac
-/
def toLpCLM (p : Real>=0∞) [Fact (1 <= p)] (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] : 𝓢(E, F) ->L[𝕜] Lp F p μ :=
mkCLMtoNormedSpace (fun f => f.toLp p μ) (fun _ _ => rfl) (fun _ _ => rfl) by
    rcases norm_toLp_le_seminorm 𝕜 F p μ with ⟨k, C, hC_pos, hC⟩
    exact ⟨Finset.Iic (k, 0), C, hC_pos, hC⟩

/--
theorem `toLpCLM_apply` / 定理 `toLpCLM_apply`

English:
theorem toLpCLM_apply
  statement: {p : Real>=0∞} [Fact (1 <= p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
  proof: rfl

@[fun_prop]

中文:
定理 toLpCLM_apply
  结论: {p : 实数>=0∞} [Fact (1 <= p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
  证明: rfl

@[fun_prop]
-/
@[simp] theorem toLpCLM_apply {p : Real>=0∞} [Fact (1 <= p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
    {f : 𝓢(E, F)} : toLpCLM 𝕜 F p μ f = f.toLp p μ := rfl

@[fun_prop]
/--
theorem `continuous_toLp` / 定理 `continuous_toLp`

English:
theorem continuous_toLp
  given: {p : Real>=0∞} [Fact (1 <= p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
  proof: (toLpCLM Real F p μ).continuous

中文:
定理 continuous_toLp
  条件: {p : 实数>=0∞} [Fact (1 <= p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
  证明: (toLpCLM Real F p μ).continuous

Depends on / 依赖: continuous, toLpCLM
-/
theorem continuous_toLp {p : Real>=0∞} [Fact (1 <= p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth] :
    Continuous (fun f : 𝓢(E, F) => f.toLp p μ) := (toLpCLM Real F p μ).continuous

/--
theorem `denseRange_toLpCLM` / 定理 `denseRange_toLpCLM`

English:
theorem denseRange_toLpCLM
  statement: [FiniteDimensional Real E] [BorelSpace E] {p : Real>=0∞} (hp : p != ⊤)
  proof: by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := MemLp.exist_eLpNorm_sub_le hp hp'.out (Lp.memLp f) hε
  use (hg₁.toSchwartzMap hg₂).toLp p μ
  have : (f : E -> F) - ((hg₁.toSchwartzMap hg₂).toLp p μ : E -> F) =ᵐ[μ] (f : 

中文:
定理 denseRange_toLpCLM
  结论: [FiniteDimensional 实数 E] [BorelSpace E] {p : 实数>=0∞} (hp : p != ⊤)
  证明: by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := MemLp.exist_eLpNorm_sub_le hp hp'.out (Lp.memLp f) hε
  use (hg₁.toSchwartzMap hg₂).toLp p μ
  have : (f : E -> F) - ((hg₁.toSchwartzMap hg₂).toLp p μ : E -> F) =ᵐ[μ] (f : 

Depends on / 依赖: Lp.dist_def, Lp.memLp, MemLp.exist_eLpNorm_sub_le, Metric, Metric.mem_closedBall, Metric.nhds_basis_closedBall, Set.mem_range, coeFn_toLp, dist_def, eLpNorm_congr_ae, exist_eLpNorm_sub_le, exists_apply_eq_apply, filter_upwards, mem_closedBall, mem_closure_iff_nhds_basis, mem_range, nhds_basis_closedBall, toLpCLM_apply, toSchwartzMap, true_and
-/
theorem denseRange_toLpCLM [FiniteDimensional Real E] [BorelSpace E] {p : Real>=0∞} (hp : p != ⊤)
    [hp' : Fact (1 <= p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth] [IsFiniteMeasureOnCompacts μ] :
    DenseRange (SchwartzMap.toLpCLM Real F p μ) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := MemLp.exist_eLpNorm_sub_le hp hp'.out (Lp.memLp f) hε
  use (hg₁.toSchwartzMap hg₂).toLp p μ
  have : (f : E -> F) - ((hg₁.toSchwartzMap hg₂).toLp p μ : E -> F) =ᵐ[μ] (f : E -> F) - g := by
    filter_upwards [(hg₁.toSchwartzMap hg₂).coeFn_toLp p μ]
    simp
  simp only [Set.mem_range, toLpCLM_apply, exists_apply_eq_apply, Metric.mem_closedBall', true_and,
    Lp.dist_def, eLpNorm_congr_ae this]
  grw [hg₃, ENNReal.toReal_ofReal hε.le]
  simp

end Lp

section L2

open MeasureTheory

variable [NormedAddCommGroup H] [NormedSpace Real H] [FiniteDimensional Real H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace Complex V]

@[simp]
/--
theorem `inner_toL2_toL2_eq` / 定理 `inner_toL2_toL2_eq`

English:
theorem inner_toL2_toL2_eq
  given: (f g : 𝓢(H, V)) (μ : Measure H := by volume_tac) [μ.HasTemperateGrowth]
  proof: by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp 2 μ
  have hg_ae := g.coeFn_toLp 2 μ
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf]; rw [hg]

中文:
定理 inner_toL2_toL2_eq
  条件: (f g : 𝓢(H, V)) (μ : Measure H := by volume_tac) [μ.HasTemperateGrowth]
  证明: by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp 2 μ
  have hg_ae := g.coeFn_toLp 2 μ
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf]; rw [hg]

Depends on / 依赖: HasTemperateGrowth, coeFn_toLp, f.coeFn_toLp, f.toLp, filter_upwards, g.coeFn_toLp, g.toLp, hf_ae, hg_ae, integral_congr_ae, volume_tac
-/
theorem inner_toL2_toL2_eq (f g : 𝓢(H, V)) (μ : Measure H := by volume_tac) [μ.HasTemperateGrowth] :
    inner Complex (f.toLp 2 μ) (g.toLp 2 μ) = ∫ x, inner Complex (f x) (g x) ∂μ := by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp 2 μ
  have hg_ae := g.coeFn_toLp 2 μ
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf]; rw [hg]

end L2

end SchwartzMap
