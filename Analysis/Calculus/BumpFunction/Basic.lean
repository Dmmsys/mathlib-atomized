/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Infinitely smooth "bump" functions

A smooth bump function is an infinitely smooth function `f : E → ℝ` supported on a ball
that is equal to `1` on a ball of smaller radius.

These functions have many uses in real analysis. E.g.,

- they can be used to construct a smooth partition of unity which is a very useful tool;
- they can be used to approximate a continuous function by infinitely smooth functions.

There are two classes of spaces where bump functions are guaranteed to exist:
inner product spaces and finite-dimensional spaces.

In this file we define a typeclass `HasContDiffBump`
saying that a normed space has a family of smooth bump functions with certain properties.

We also define a structure `ContDiffBump` that holds the center and radii of the balls from above.
An element `f : ContDiffBump c` can be coerced to a function which is an infinitely smooth function
such that

- `f` is equal to `1` in `Metric.closedBall c f.rIn`;
- `support f = Metric.ball c f.rOut`;
- `0 ≤ f x ≤ 1` for all `x`.

## Main Definitions

- `ContDiffBump (c : E)`: a structure holding data needed to construct
  an infinitely smooth bump function.
- `ContDiffBumpBase (E : Type*)`: a family of infinitely smooth bump functions
  that can be used to construct coercion of a `ContDiffBump (c : E)`
  to a function.
- `HasContDiffBump (E : Type*)`: a typeclass saying that `E` has a `ContDiffBumpBase`.
  Two instances of this typeclass (for inner product spaces and for finite-dimensional spaces)
  are provided elsewhere.

## Keywords

smooth function, smooth bump function
-/

@[expose] public section
noncomputable section

open Function Set Filter
open scoped Topology Filter ContDiff

variable {E X : Type*}

/--
Definition of `ContDiffBump` / `ContDiffBump` 的定义

English:
structure ContDiffBump
  parameters: (c : E)
  axioms and operations (3):
    - (rIn(rOut) : Real)
    - rIn_pos : 0 < rIn
    - rIn_lt_rOut : rIn < rOut

中文:
结构 余ntDiffBump
  参数: (c : E)
  公理与运算 (3 个):
    - (rIn(rOut) : 实数)
    - rIn_pos : 0 < rIn
    - rIn_lt_rOut : rIn < rOut
-/
structure ContDiffBump (c : E) where
  /-- real numbers `0 < rIn < rOut` -/
  (rIn rOut : Real)
  rIn_pos : 0 < rIn
  rIn_lt_rOut : rIn < rOut

/--
Definition of `ContDiffBumpBase` / `ContDiffBumpBase` 的定义

English:
structure ContDiffBumpBase
  parameters: (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
  axioms and operations (6):
    - toFun : Real -> E -> Real
    - mem_Icc : forall (R : Real) (x : E), toFun R x in Icc (0 : Real) 1
    - symmetric : forall (R : Real) (x : E), toFun R (-x) = toFun R x
    - smooth : ContDiffOn Real ∞ (uncurry toFun) (Ioi (1 : Real) ×ˢ (univ : Set E))
    - eq_one : forall R : Real, 1 < R -> forall x : E, ‖x‖ <= 1 -> toFun R x = 1
    - support : forall R : Real, 1 < R -> Function.support (toFun R) = Metric.ball (0 : E) R

中文:
结构 余ntDiffBumpBase
  参数: (E : 类型) [赋范交换加群 E] [赋范空间 实数 E]
  公理与运算 (6 个):
    - toFun : 实数 -> E -> 实数
    - mem_Icc : 对任意 (R : 实数) (x : E), toFun R x in 闭区间 (0 : 实数) 1
    - symmetric : 对任意 (R : 实数) (x : E), toFun R (-x) = toFun R x
    - smooth : ContDiffOn 实数 ∞ (uncurry toFun) (左开右无界区间 (1 : 实数) ×ˢ (univ : 集合 E))
    - eq_one : 对任意 R : 实数, 1 < R -> 对任意 x : E, ‖x‖ <= 1 -> toFun R x = 1
    - support : 对任意 R : 实数, 1 < R -> 函数.support (toFun R) = Metric.ball (0 : E) R
-/
structure ContDiffBumpBase (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E] where
  /-- The function underlying this family of bump functions -/
  toFun : Real -> E -> Real
  mem_Icc : forall (R : Real) (x : E), toFun R x in Icc (0 : Real) 1
  symmetric : forall (R : Real) (x : E), toFun R (-x) = toFun R x
  smooth : ContDiffOn Real ∞ (uncurry toFun) (Ioi (1 : Real) ×ˢ (univ : Set E))
  eq_one : forall R : Real, 1 < R -> forall x : E, ‖x‖ <= 1 -> toFun R x = 1
  support : forall R : Real, 1 < R -> Function.support (toFun R) = Metric.ball (0 : E) R

/--
Definition of `HasContDiffBump` / `HasContDiffBump` 的定义

English:
class HasContDiffBump
  parameters: (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
  axioms and operations (1):
    - out : Nonempty (ContDiffBumpBase E)

中文:
类 有余ntDiffBump
  参数: (E : 类型) [赋范交换加群 E] [赋范空间 实数 E]
  公理与运算 (1 个):
    - out : 非空 (余ntDiffBumpBase E)
-/
class HasContDiffBump (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E] : Prop where
  out : Nonempty (ContDiffBumpBase E)

/--
Definition of `someContDiffBumpBase` / `someContDiffBumpBase` 的定义

English:
definition someContDiffBumpBase
  signature: (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
  body: Nonempty.some hb.out

中文:
定义 someContDiffBumpBase
  签名: (E : 类型) [赋范交换加群 E] [赋范空间 实数 E]
  定义体: Nonempty.some hb.out

Depends on / 依赖: Nonempty, Nonempty.some, hb.out
-/
def someContDiffBumpBase (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
    [hb : HasContDiffBump E] : ContDiffBumpBase E :=
  Nonempty.some hb.out

namespace ContDiffBump

/--
theorem `rOut_pos` / 定理 `rOut_pos`

English:
theorem rOut_pos
  given: {c : E} (f : ContDiffBump c)
  statement: 0 < f.rOut
  proof: f.rIn_pos.trans f.rIn_lt_rOut

中文:
定理 rOut_pos
  条件: {c : E} (f : 余ntDiffBump c)
  结论: 0 < f.rOut
  证明: f.rIn_pos.trans f.rIn_lt_rOut

Depends on / 依赖: f.rIn_lt_rOut, f.rIn_pos.trans, rIn_lt_rOut, rIn_pos
-/
theorem rOut_pos {c : E} (f : ContDiffBump c) : 0 < f.rOut :=
  f.rIn_pos.trans f.rIn_lt_rOut

/--
theorem `one_lt_rOut_div_rIn` / 定理 `one_lt_rOut_div_rIn`

English:
theorem one_lt_rOut_div_rIn
  given: {c : E} (f : ContDiffBump c)
  statement: 1 < f.rOut / f.rIn
  proof: by
  rw [one_lt_div f.rIn_pos]
  exact f.rIn_lt_rOut

中文:
定理 one_lt_rOut_div_rIn
  条件: {c : E} (f : 余ntDiffBump c)
  结论: 1 < f.rOut / f.rIn
  证明: by
  rw [one_lt_div f.rIn_pos]
  exact f.rIn_lt_rOut

Depends on / 依赖: f.rIn_lt_rOut, f.rIn_pos, one_lt_div, rIn_lt_rOut, rIn_pos
-/
theorem one_lt_rOut_div_rIn {c : E} (f : ContDiffBump c) : 1 < f.rOut / f.rIn := by
  rw [one_lt_div f.rIn_pos]
  exact f.rIn_lt_rOut

instance (c : E) : Inhabited (ContDiffBump c) :=
  ⟨⟨1, 2, zero_lt_one, one_lt_two⟩⟩

variable [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup X] [NormedSpace Real X]
  [HasContDiffBump E] {c : E} (f : ContDiffBump c) {x : E} {n : Nat∞}

/--
Definition of `toFun` / `toFun` 的定义

English:
definition toFun
  signature: {c : E} (f : ContDiffBump c)
  body: (someContDiffBumpBase E).toFun (f.rOut / f.rIn) ∘ fun x => (f.rIn⁻¹ • (x - c))

中文:
定义 toFun
  签名: {c : E} (f : 余ntDiffBump c)
  定义体: (someContDiffBumpBase E).toFun (f.rOut / f.rIn) ∘ fun x => (f.rIn⁻¹ • (x - c))
-/
@[coe] def toFun {c : E} (f : ContDiffBump c) : E -> Real :=
  (someContDiffBumpBase E).toFun (f.rOut / f.rIn) ∘ fun x => (f.rIn⁻¹ • (x - c))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (ContDiffBump c) fun _ => E -> Real
  body: ⟨toFun⟩

中文:
实例 :
  签名: CoeFun (余ntDiffBump c) fun _ => E -> 实数
  定义体: ⟨toFun⟩
-/
instance : CoeFun (ContDiffBump c) fun _ => E -> Real :=
  ⟨toFun⟩

/--
theorem `apply` / 定理 `apply`

English:
theorem apply
  given: (x : E)
  proof: rfl

中文:
定理 apply
  条件: (x : E)
  证明: rfl
-/
protected theorem apply (x : E) :
    f x = (someContDiffBumpBase E).toFun (f.rOut / f.rIn) (f.rIn⁻¹ • (x - c)) :=
  rfl

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: (x : E)
  statement: f (c - x) = f (c + x)
  proof: by
  simp [f.apply, ContDiffBumpBase.symmetric]

中文:
定理 sub
  条件: (x : E)
  结论: f (c - x) = f (c + x)
  证明: by
  simp [f.apply, ContDiffBumpBase.symmetric]
-/
protected theorem sub (x : E) : f (c - x) = f (c + x) := by
  simp [f.apply, ContDiffBumpBase.symmetric]

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (f : ContDiffBump (0 : E)) (x : E)
  statement: f (-x) = f x
  proof: by
  simp_rw [← zero_sub, f.sub, zero_add]

中文:
定理 neg
  条件: (f : 余ntDiffBump (0 : E)) (x : E)
  结论: f (-x) = f x
  证明: by
  simp_rw [← zero_sub, f.sub, zero_add]
-/
protected theorem neg (f : ContDiffBump (0 : E)) (x : E) : f (-x) = f x := by
  simp_rw [← zero_sub, f.sub, zero_add]

open Metric

/--
theorem `one_of_mem_closedBall` / 定理 `one_of_mem_closedBall`

English:
theorem one_of_mem_closedBall
  given: (hx : x in closedBall c f.rIn)
  statement: f x = 1
  proof: by
  apply ContDiffBumpBase.eq_one _ _ f.one_lt_rOut_div_rIn
  simpa only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg f.rIn_pos.le, ← div_eq_inv_mul,
    div_le_one f.rIn_pos] using mem_closedBall_iff_norm.1 hx

中文:
定理 one_of_mem_closedBall
  条件: (hx : x in closedBall c f.rIn)
  结论: f x = 1
  证明: by
  apply ContDiffBumpBase.eq_one _ _ f.one_lt_rOut_div_rIn
  simpa only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg f.rIn_pos.le, ← div_eq_inv_mul,
    div_le_one f.rIn_pos] using mem_closedBall_iff_norm.1 hx

Depends on / 依赖: ContDiffBumpBase, ContDiffBumpBase.eq_one, Real.norm_eq_abs, abs_inv, abs_of_nonneg, div_eq_inv_mul, div_le_one, eq_one, f.one_lt_rOut_div_rIn, f.rIn_pos, f.rIn_pos.le, mem_closedBall_iff_norm, norm_eq_abs, norm_smul, one_lt_rOut_div_rIn, rIn_pos
-/
theorem one_of_mem_closedBall (hx : x in closedBall c f.rIn) : f x = 1 := by
  apply ContDiffBumpBase.eq_one _ _ f.one_lt_rOut_div_rIn
  simpa only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg f.rIn_pos.le, ← div_eq_inv_mul,
    div_le_one f.rIn_pos] using mem_closedBall_iff_norm.1 hx

/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  statement: 0 <= f x
  proof: (ContDiffBumpBase.mem_Icc (someContDiffBumpBase E) _ _).1

中文:
定理 nonneg
  结论: 0 <= f x
  证明: (ContDiffBumpBase.mem_Icc (someContDiffBumpBase E) _ _).1

Depends on / 依赖: ContDiffBumpBase, ContDiffBumpBase.mem_Icc, mem_Icc, someContDiffBumpBase
-/
theorem nonneg : 0 <= f x :=
  (ContDiffBumpBase.mem_Icc (someContDiffBumpBase E) _ _).1

/--
theorem `nonneg'` / 定理 `nonneg'`

English:
theorem nonneg'
  given: (x : E)
  statement: 0 <= f x
  proof: f.nonneg

中文:
定理 nonneg'
  条件: (x : E)
  结论: 0 <= f x
  证明: f.nonneg

Depends on / 依赖: f.nonneg, nonneg
-/
theorem nonneg' (x : E) : 0 <= f x := f.nonneg

/--
theorem `le_one` / 定理 `le_one`

English:
theorem le_one
  statement: f x <= 1
  proof: (ContDiffBumpBase.mem_Icc (someContDiffBumpBase E) _ _).2

中文:
定理 le_one
  结论: f x <= 1
  证明: (ContDiffBumpBase.mem_Icc (someContDiffBumpBase E) _ _).2

Depends on / 依赖: ContDiffBumpBase, ContDiffBumpBase.mem_Icc, mem_Icc, someContDiffBumpBase
-/
theorem le_one : f x <= 1 :=
  (ContDiffBumpBase.mem_Icc (someContDiffBumpBase E) _ _).2

/--
theorem `support_eq` / 定理 `support_eq`

English:
theorem support_eq
  statement: Function.support f = Metric.ball c f.rOut
  proof: by
  simp only [toFun, support_comp_eq_preimage, ContDiffBumpBase.support _ _ f.one_lt_rOut_div_rIn]
  ext x
  simp only [mem_ball_iff_norm, sub_zero, norm_smul, mem_preimage, Real.norm_eq_abs, abs_inv,
    abs_of_pos f.rIn_pos, ← div_eq_inv_mul, div_lt_div_iff_of_pos_right f.rIn_pos]

中文:
定理 support_eq
  结论: 函数.support f = Metric.ball c f.rOut
  证明: by
  simp only [toFun, support_comp_eq_preimage, ContDiffBumpBase.support _ _ f.one_lt_rOut_div_rIn]
  ext x
  simp only [mem_ball_iff_norm, sub_zero, norm_smul, mem_preimage, Real.norm_eq_abs, abs_inv,
    abs_of_pos f.rIn_pos, ← div_eq_inv_mul, div_lt_div_iff_of_pos_right f.rIn_pos]

Depends on / 依赖: ContDiffBumpBase, ContDiffBumpBase.support, Real.norm_eq_abs, abs_inv, abs_of_pos, div_eq_inv_mul, div_lt_div_iff_of_pos_right, f.one_lt_rOut_div_rIn, f.rIn_pos, mem_ball_iff_norm, mem_preimage, norm_eq_abs, norm_smul, one_lt_rOut_div_rIn, rIn_pos, sub_zero, support, support_comp_eq_preimage
-/
theorem support_eq : Function.support f = Metric.ball c f.rOut := by
  simp only [toFun, support_comp_eq_preimage, ContDiffBumpBase.support _ _ f.one_lt_rOut_div_rIn]
  ext x
  simp only [mem_ball_iff_norm, sub_zero, norm_smul, mem_preimage, Real.norm_eq_abs, abs_inv,
    abs_of_pos f.rIn_pos, ← div_eq_inv_mul, div_lt_div_iff_of_pos_right f.rIn_pos]

/--
theorem `tsupport_eq` / 定理 `tsupport_eq`

English:
theorem tsupport_eq
  statement: tsupport f = closedBall c f.rOut
  proof: by
  simp_rw [tsupport, f.support_eq, closure_ball _ f.rOut_pos.ne']

中文:
定理 tsupport_eq
  结论: tsupport f = closedBall c f.rOut
  证明: by
  simp_rw [tsupport, f.support_eq, closure_ball _ f.rOut_pos.ne']

Depends on / 依赖: closure_ball, f.rOut_pos.ne, f.support_eq, rOut_pos, simp_rw, support_eq, tsupport
-/
theorem tsupport_eq : tsupport f = closedBall c f.rOut := by
  simp_rw [tsupport, f.support_eq, closure_ball _ f.rOut_pos.ne']

/--
theorem `pos_of_mem_ball` / 定理 `pos_of_mem_ball`

English:
theorem pos_of_mem_ball
  given: (hx : x in ball c f.rOut)
  statement: 0 < f x
  proof: f.nonneg.lt_of_ne' by rwa [← support_eq, mem_support] at hx

中文:
定理 pos_of_mem_ball
  条件: (hx : x in ball c f.rOut)
  结论: 0 < f x
  证明: f.nonneg.lt_of_ne' by rwa [← support_eq, mem_support] at hx

Depends on / 依赖: f.nonneg.lt_of_ne, lt_of_ne, mem_support, nonneg, support_eq
-/
theorem pos_of_mem_ball (hx : x in ball c f.rOut) : 0 < f x :=
f.nonneg.lt_of_ne' by rwa [← support_eq, mem_support] at hx

/--
theorem `zero_of_le_dist` / 定理 `zero_of_le_dist`

English:
theorem zero_of_le_dist
  given: (hx : f.rOut <= dist x c)
  statement: f x = 0
  proof: by
  rwa [← notMem_support, support_eq, mem_ball, not_lt]

中文:
定理 zero_of_le_dist
  条件: (hx : f.rOut <= dist x c)
  结论: f x = 0
  证明: by
  rwa [← notMem_support, support_eq, mem_ball, not_lt]

Depends on / 依赖: mem_ball, notMem_support, not_lt, support_eq
-/
theorem zero_of_le_dist (hx : f.rOut <= dist x c) : f x = 0 := by
  rwa [← notMem_support, support_eq, mem_ball, not_lt]

/--
theorem `hasCompactSupport` / 定理 `hasCompactSupport`

English:
theorem hasCompactSupport
  given: [FiniteDimensional Real E]
  statement: HasCompactSupport f
  proof: by
  simp_rw [HasCompactSupport, f.tsupport_eq, isCompact_closedBall]

中文:
定理 hasCompactSupport
  条件: [有限维 实数 E]
  结论: HasCompactSupport f
  证明: by
  simp_rw [HasCompactSupport, f.tsupport_eq, isCompact_closedBall]
-/
protected theorem hasCompactSupport [FiniteDimensional Real E] : HasCompactSupport f := by
  simp_rw [HasCompactSupport, f.tsupport_eq, isCompact_closedBall]

/--
theorem `eventuallyEq_one_of_mem_ball` / 定理 `eventuallyEq_one_of_mem_ball`

English:
theorem eventuallyEq_one_of_mem_ball
  given: (h : x in ball c f.rIn)
  statement: f =ᶠ[𝓝 x] 1
  proof: mem_of_superset (closedBall_mem_nhds_of_mem h) fun _ => f.one_of_mem_closedBall

中文:
定理 eventuallyEq_one_of_mem_ball
  条件: (h : x in ball c f.rIn)
  结论: f =ᶠ[𝓝 x] 1
  证明: mem_of_superset (closedBall_mem_nhds_of_mem h) fun _ => f.one_of_mem_closedBall

Depends on / 依赖: closedBall_mem_nhds_of_mem, f.one_of_mem_closedBall, mem_of_superset, one_of_mem_closedBall
-/
theorem eventuallyEq_one_of_mem_ball (h : x in ball c f.rIn) : f =ᶠ[𝓝 x] 1 :=
  mem_of_superset (closedBall_mem_nhds_of_mem h) fun _ => f.one_of_mem_closedBall

/--
theorem `eventuallyEq_one` / 定理 `eventuallyEq_one`

English:
theorem eventuallyEq_one
  statement: f =ᶠ[𝓝 c] 1
  proof: f.eventuallyEq_one_of_mem_ball (mem_ball_self f.rIn_pos)

中文:
定理 eventuallyEq_one
  结论: f =ᶠ[𝓝 c] 1
  证明: f.eventuallyEq_one_of_mem_ball (mem_ball_self f.rIn_pos)

Depends on / 依赖: eventuallyEq_one_of_mem_ball, f.eventuallyEq_one_of_mem_ball, f.rIn_pos, mem_ball_self, rIn_pos
-/
theorem eventuallyEq_one : f =ᶠ[𝓝 c] 1 :=
  f.eventuallyEq_one_of_mem_ball (mem_ball_self f.rIn_pos)

/--
theorem `_root_.ContDiffWithinAt.contDiffBump` / 定理 `_root_.ContDiffWithinAt.contDiffBump`

English:
theorem _root_.ContDiffWithinAt.contDiffBump
  statement: {c g : X -> E} {s : Set X}
  proof: by
  change ContDiffWithinAt Real n (uncurry (someContDiffBumpBase E).toFun ∘ fun x : X =>
    ((f x).rOut / (f x).rIn, (f x).rIn⁻¹ • (g x - c x))) s x
  refine (((someContDiffBumpBase E).smooth.contDiffAt ?_).of_le
    (mod_cast le_top)).comp_contDiffWithinAt x ?_
  · exact prod_mem_nhds (Ioi_mem_nhds (f x).one_lt_rOut_div_rIn) univ_mem
  · exact (hR.div hr (f x).rIn_pos.ne').prodMk ((hr.inv (f x).rIn_pos.ne').smul (hg.sub hc))

中文:
定理 _root_.ContDiffWithinAt.contDiffBump
  结论: {c g : X -> E} {s : 集合 X}
  证明: by
  change ContDiffWithinAt Real n (uncurry (someContDiffBumpBase E).toFun ∘ fun x : X =>
    ((f x).rOut / (f x).rIn, (f x).rIn⁻¹ • (g x - c x))) s x
  refine (((someContDiffBumpBase E).smooth.contDiffAt ?_).of_le
    (mod_cast le_top)).comp_contDiffWithinAt x ?_
  · exact prod_mem_nhds (Ioi_mem_nhds (f x).one_lt_rOut_div_rIn) univ_mem
  · exact (hR.div hr (f x).rIn_pos.ne').prodMk ((hr.inv (f x).rIn_pos.ne').smul (hg.sub hc))
-/
protected theorem _root_.ContDiffWithinAt.contDiffBump {c g : X -> E} {s : Set X}
    {f : forall x, ContDiffBump (c x)} {x : X} (hc : ContDiffWithinAt Real n c s x)
    (hr : ContDiffWithinAt Real n (fun x => (f x).rIn) s x)
    (hR : ContDiffWithinAt Real n (fun x => (f x).rOut) s x)
    (hg : ContDiffWithinAt Real n g s x) :
    ContDiffWithinAt Real n (fun x => f x (g x)) s x := by
  change ContDiffWithinAt Real n (uncurry (someContDiffBumpBase E).toFun ∘ fun x : X =>
    ((f x).rOut / (f x).rIn, (f x).rIn⁻¹ • (g x - c x))) s x
  refine (((someContDiffBumpBase E).smooth.contDiffAt ?_).of_le
    (mod_cast le_top)).comp_contDiffWithinAt x ?_
  · exact prod_mem_nhds (Ioi_mem_nhds (f x).one_lt_rOut_div_rIn) univ_mem
  · exact (hR.div hr (f x).rIn_pos.ne').prodMk ((hr.inv (f x).rIn_pos.ne').smul (hg.sub hc))

/-- `ContDiffBump` is `𝒞ⁿ` in all its arguments. -/
protected nonrec theorem _root_.ContDiffAt.contDiffBump {c g : X -> E} {f : forall x, ContDiffBump (c x)}
    {x : X} (hc : ContDiffAt Real n c x) (hr : ContDiffAt Real n (fun x => (f x).rIn) x)
    (hR : ContDiffAt Real n (fun x => (f x).rOut) x) (hg : ContDiffAt Real n g x) :
    ContDiffAt Real n (fun x => f x (g x)) x :=
  hc.contDiffBump hr hR hg

/--
theorem `_root_.ContDiff.contDiffBump` / 定理 `_root_.ContDiff.contDiffBump`

English:
theorem _root_.ContDiff.contDiffBump
  statement: {c g : X -> E} {f : forall x, ContDiffBump (c x)}
  proof: by
  rw [contDiff_iff_contDiffAt] at *
  exact fun x => (hc x).contDiffBump (hr x) (hR x) (hg x)

中文:
定理 _root_.连续可微.contDiffBump
  结论: {c g : X -> E} {f : 对任意 x, 余ntDiffBump (c x)}
  证明: by
  rw [contDiff_iff_contDiffAt] at *
  exact fun x => (hc x).contDiffBump (hr x) (hR x) (hg x)

Depends on / 依赖: contDiffBump, contDiff_iff_contDiffAt
-/
theorem _root_.ContDiff.contDiffBump {c g : X -> E} {f : forall x, ContDiffBump (c x)}
    (hc : ContDiff Real n c) (hr : ContDiff Real n fun x => (f x).rIn)
    (hR : ContDiff Real n fun x => (f x).rOut) (hg : ContDiff Real n g) :
    ContDiff Real n fun x => f x (g x) := by
  rw [contDiff_iff_contDiffAt] at *
  exact fun x => (hc x).contDiffBump (hr x) (hR x) (hg x)

/--
theorem `contDiff` / 定理 `contDiff`

English:
theorem contDiff
  statement: ContDiff Real n f
  proof: contDiff_const.contDiffBump contDiff_const contDiff_const contDiff_id

中文:
定理 contDiff
  结论: 连续可微 实数 n f
  证明: contDiff_const.contDiffBump contDiff_const contDiff_const contDiff_id
-/
protected theorem contDiff : ContDiff Real n f :=
  contDiff_const.contDiffBump contDiff_const contDiff_const contDiff_id

/--
theorem `contDiffAt` / 定理 `contDiffAt`

English:
theorem contDiffAt
  statement: ContDiffAt Real n f x
  proof: f.contDiff.contDiffAt

中文:
定理 contDiffAt
  结论: ContDiffAt 实数 n f x
  证明: f.contDiff.contDiffAt
-/
protected theorem contDiffAt : ContDiffAt Real n f x :=
  f.contDiff.contDiffAt

/--
theorem `contDiffWithinAt` / 定理 `contDiffWithinAt`

English:
theorem contDiffWithinAt
  given: {s : Set E}
  statement: ContDiffWithinAt Real n f s x
  proof: f.contDiffAt.contDiffWithinAt

中文:
定理 contDiffWithinAt
  条件: {s : 集合 E}
  结论: ContDiffWithinAt 实数 n f s x
  证明: f.contDiffAt.contDiffWithinAt
-/
protected theorem contDiffWithinAt {s : Set E} : ContDiffWithinAt Real n f s x :=
  f.contDiffAt.contDiffWithinAt

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: Continuous f
  proof: contDiff_zero.mp f.contDiff

中文:
定理 continuous
  结论: 连续 f
  证明: contDiff_zero.mp f.contDiff
-/
protected theorem continuous : Continuous f :=
  contDiff_zero.mp f.contDiff

end ContDiffBump
