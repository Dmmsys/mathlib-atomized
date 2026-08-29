/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Algebra.Star.Basic

/-!
# Continuity of `star`

This file defines the `ContinuousStar` typeclass, along with instances on `Pi`, `Prod`,
`MulOpposite`, and `Units`.
-/

@[expose] public section

open Filter Topology

/--
Definition of `ContinuousStar` / `ContinuousStar` 的定义

English:
class ContinuousStar
  parameters: (R : Type*) [TopologicalSpace R] [Star R]
  axioms and operations (1):
    - continuous_star : Continuous (star : R -> R)

中文:
类 余ntinuousStar
  参数: (R : 类型) [拓扑空间 R] [对合 R]
  公理与运算 (1 个):
    - continuous_star : 连续 (star : R -> R)
-/
class ContinuousStar (R : Type*) [TopologicalSpace R] [Star R] : Prop where
  /-- The `star` operator is continuous. -/
  continuous_star : Continuous (star : R -> R)

export ContinuousStar (continuous_star)

section Continuity

variable {α R : Type*} [TopologicalSpace R] [Star R] [ContinuousStar R]

/--
theorem `continuousOn_star` / 定理 `continuousOn_star`

English:
theorem continuousOn_star
  given: {s : Set R}
  statement: ContinuousOn star s
  proof: continuous_star.continuousOn

中文:
定理 continuousOn_star
  条件: {s : 集合 R}
  结论: ContinuousOn star s
  证明: continuous_star.continuousOn

Depends on / 依赖: continuousOn, continuous_star, continuous_star.continuousOn
-/
theorem continuousOn_star {s : Set R} : ContinuousOn star s :=
  continuous_star.continuousOn

/--
theorem `continuousWithinAt_star` / 定理 `continuousWithinAt_star`

English:
theorem continuousWithinAt_star
  given: {s : Set R} {x : R}
  statement: ContinuousWithinAt star s x
  proof: continuous_star.continuousWithinAt

中文:
定理 continuousWithinAt_star
  条件: {s : 集合 R} {x : R}
  结论: ContinuousWithinAt star s x
  证明: continuous_star.continuousWithinAt

Depends on / 依赖: continuousWithinAt, continuous_star, continuous_star.continuousWithinAt
-/
theorem continuousWithinAt_star {s : Set R} {x : R} : ContinuousWithinAt star s x :=
  continuous_star.continuousWithinAt

/--
theorem `continuousAt_star` / 定理 `continuousAt_star`

English:
theorem continuousAt_star
  given: {x : R}
  statement: ContinuousAt star x
  proof: continuous_star.continuousAt

中文:
定理 continuousAt_star
  条件: {x : R}
  结论: ContinuousAt star x
  证明: continuous_star.continuousAt

Depends on / 依赖: continuousAt, continuous_star, continuous_star.continuousAt
-/
theorem continuousAt_star {x : R} : ContinuousAt star x :=
  continuous_star.continuousAt

/--
theorem `tendsto_star` / 定理 `tendsto_star`

English:
theorem tendsto_star
  given: (a : R)
  statement: Tendsto star (𝓝 a) (𝓝 (star a))
  proof: continuousAt_star

中文:
定理 tendsto_star
  条件: (a : R)
  结论: 收敛 star (𝓝 a) (𝓝 (star a))
  证明: continuousAt_star

Depends on / 依赖: continuousAt_star
-/
theorem tendsto_star (a : R) : Tendsto star (𝓝 a) (𝓝 (star a)) :=
  continuousAt_star

/--
theorem `Filter.Tendsto.star` / 定理 `Filter.Tendsto.star`

English:
theorem Filter.Tendsto.star
  given: {f : α -> R} {l : Filter α} {y : R} (h : Tendsto f l (𝓝 y))
  proof: (continuous_star.tendsto y).comp h

中文:
定理 滤子.收敛.star
  条件: {f : α -> R} {l : 滤子 α} {y : R} (h : 收敛 f l (𝓝 y))
  证明: (continuous_star.tendsto y).comp h

Depends on / 依赖: continuous_star, continuous_star.tendsto, tendsto
-/
theorem Filter.Tendsto.star {f : α -> R} {l : Filter α} {y : R} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => star (f x)) l (𝓝 (star y)) :=
  (continuous_star.tendsto y).comp h

variable [TopologicalSpace α] {f : α -> R} {s : Set α} {x : α}

@[continuity, fun_prop]
/--
theorem `Continuous.star` / 定理 `Continuous.star`

English:
theorem Continuous.star
  given: (hf : Continuous f)
  statement: Continuous fun x => star (f x)
  proof: continuous_star.comp hf

@[fun_prop]

中文:
定理 连续.star
  条件: (hf : 连续 f)
  结论: 连续 fun x => star (f x)
  证明: continuous_star.comp hf

@[fun_prop]

Depends on / 依赖: continuous_star, continuous_star.comp
-/
theorem Continuous.star (hf : Continuous f) : Continuous fun x => star (f x) :=
  continuous_star.comp hf

@[fun_prop]
/--
theorem `ContinuousAt.star` / 定理 `ContinuousAt.star`

English:
theorem ContinuousAt.star
  given: (hf : ContinuousAt f x)
  statement: ContinuousAt (fun x => star (f x)) x
  proof: continuousAt_star.comp hf

@[fun_prop]

中文:
定理 ContinuousAt.star
  条件: (hf : ContinuousAt f x)
  结论: ContinuousAt (fun x => star (f x)) x
  证明: continuousAt_star.comp hf

@[fun_prop]

Depends on / 依赖: continuousAt_star, continuousAt_star.comp
-/
theorem ContinuousAt.star (hf : ContinuousAt f x) : ContinuousAt (fun x => star (f x)) x :=
  continuousAt_star.comp hf

@[fun_prop]
/--
theorem `ContinuousOn.star` / 定理 `ContinuousOn.star`

English:
theorem ContinuousOn.star
  given: (hf : ContinuousOn f s)
  statement: ContinuousOn (fun x => star (f x)) s
  proof: continuous_star.comp_continuousOn hf

中文:
定理 ContinuousOn.star
  条件: (hf : ContinuousOn f s)
  结论: ContinuousOn (fun x => star (f x)) s
  证明: continuous_star.comp_continuousOn hf

Depends on / 依赖: comp_continuousOn, continuous_star, continuous_star.comp_continuousOn
-/
theorem ContinuousOn.star (hf : ContinuousOn f s) : ContinuousOn (fun x => star (f x)) s :=
  continuous_star.comp_continuousOn hf

/--
theorem `ContinuousWithinAt.star` / 定理 `ContinuousWithinAt.star`

English:
theorem ContinuousWithinAt.star
  given: (hf : ContinuousWithinAt f s x)
  proof: Filter.Tendsto.star hf

中文:
定理 ContinuousWithinAt.star
  条件: (hf : ContinuousWithinAt f s x)
  证明: Filter.Tendsto.star hf

Depends on / 依赖: Filter, Filter.Tendsto.star, Tendsto
-/
theorem ContinuousWithinAt.star (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => star (f x)) s x :=
  Filter.Tendsto.star hf

/-- The star operation bundled as a continuous map. -/
@[simps]
/--
Definition of `starContinuousMap` / `starContinuousMap` 的定义

English:
definition starContinuousMap
  signature: : C(R, R)
  body: ⟨star, continuous_star⟩

中文:
定义 starContinuousMap
  签名: : C(R, R)
  定义体: ⟨star, continuous_star⟩

Depends on / 依赖: continuous_star
-/
def starContinuousMap : C(R, R) :=
  ⟨star, continuous_star⟩

end Continuity

section Instances

variable {R S ι : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: R] [Star S] [TopologicalSpace R] [TopologicalSpace S] [ContinuousStar R]
  body: ⟨(continuous_star.comp continuous_fst).prodMk (continuous_star.comp continuous_snd)⟩

中文:
实例 [对合
  签名: R] [对合 S] [拓扑空间 R] [拓扑空间 S] [余ntinuousStar R]
  定义体: ⟨(continuous_star.comp continuous_fst).prodMk (continuous_star.comp continuous_snd)⟩

Depends on / 依赖: continuous_fst, continuous_snd, continuous_star, continuous_star.comp, prodMk
-/
instance [Star R] [Star S] [TopologicalSpace R] [TopologicalSpace S] [ContinuousStar R]
    [ContinuousStar S] : ContinuousStar (R × S) :=
  ⟨(continuous_star.comp continuous_fst).prodMk (continuous_star.comp continuous_snd)⟩

instance {C : ι -> Type*} [forall i, TopologicalSpace (C i)] [forall i, Star (C i)]
    [forall i, ContinuousStar (C i)] : ContinuousStar (forall i, C i) where
  continuous_star := continuous_pi fun i => Continuous.star (continuous_apply i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: R] [TopologicalSpace R] [ContinuousStar R] : ContinuousStar Rᵐᵒᵖ
  body: ⟨MulOpposite.continuous_op.comp MulOpposite.continuous_unop.star⟩

中文:
实例 [对合
  签名: R] [拓扑空间 R] [余ntinuousStar R] : 余ntinuousStar Rᵐᵒᵖ
  定义体: ⟨MulOpposite.continuous_op.comp MulOpposite.continuous_unop.star⟩

Depends on / 依赖: MulOpposite, MulOpposite.continuous_op.comp, MulOpposite.continuous_unop.star, continuous_op, continuous_unop
-/
instance [Star R] [TopologicalSpace R] [ContinuousStar R] : ContinuousStar Rᵐᵒᵖ :=
⟨MulOpposite.continuous_op.comp MulOpposite.continuous_unop.star⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [StarMul R] [TopologicalSpace R] [ContinuousStar R] :
  body: ⟨continuous_induced_rng.2 Units.continuous_embedProduct.star⟩

中文:
实例 [幺半群
  签名: R] [StarMul R] [拓扑空间 R] [余ntinuousStar R] :
  定义体: ⟨continuous_induced_rng.2 Units.continuous_embedProduct.star⟩

Depends on / 依赖: Units.continuous_embedProduct.star, continuous_embedProduct, continuous_induced_rng
-/
instance [Monoid R] [StarMul R] [TopologicalSpace R] [ContinuousStar R] :
    ContinuousStar Rˣ :=
  ⟨continuous_induced_rng.2 Units.continuous_embedProduct.star⟩

end Instances
