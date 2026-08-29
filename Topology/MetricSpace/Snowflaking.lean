/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Snowflaking of a metric space

Given a (pseudo) (extended) metric space `X` and a number `0 < α ≤ 1`,
one can consider the metric given by `d x y = (dist x y) ^ α`.
The metric space determined by this new metric is said to be the `α`-snowflaking (or `α`-snowflake)
of `X`. In this file we define `Metric.Snowflaking X α hα₀ hα₁` to be a one-field structure wrapper
around `X` with metric given by this formula.

The use of the term *snowflaking* arises from the fact that if one chooses `X := Set.Icc 0 1` and
`α := log 3 / log 4`, then `Metric.Snowflaking X α … …` is isometric to the von Koch snowflake,
where we equip that space with the natural metric induced by the `α⁻¹`-Hausdorff measure of paths.

Snowflake metrics are used regularly in the geometry of metric spaces where, among other things,
they characterize doubling metrics. In particular, a metric is doubling if and only
if every `α`-snowflaking (with `0 < α < 1`) of it is bilipschitz equivalent to a subset of some
Euclidean space (the dimension of the Euclidean space depends on `α`). See [heinonen2001].

Another reason to introduce this definition is the following.
In the proof of his version of the Morse-Sard theorem,
Moreira [Moreira2001] studies maps of two variables that are Lipschitz continuous in one variable,
but satisfy a stronger assumption `‖f (a, y) - f (a, b)‖ = O(‖y - b‖ ^ (k + α))`
along the second variable, as long as `(a, b)` is one of the "interesting" points.

If we want to apply Vitali covering theorem in this context, we need to cover the set by products
`closedBall a (R ^ (k + α)) ×ˢ closedBall b R` so that both components make a similar contribution
to `‖f (x, y) - f (a, b)‖`. These sets aren't balls in the original metric
(or even subsets of balls that occupy at least a fixed fraction of the volume,
as we require in our version of Vitali theorem).

However, if we change the metric on the first component to the one introduced in this file,
then these sets become balls, and we can apply Vitali theorem.

## References
* [Carlos Gustavo T. de A. Moreira, _Hausdorff measures and the Morse-Sard theorem_]
  [Moreira2001]
-/

@[expose] public section

open scoped ENNReal NNReal Filter Uniformity Topology
open Function

noncomputable section

namespace Metric

/-- A copy of a type with metric given by `dist x y = (dist x.val y.val) ^ α`.

This is defined as a one-field structure. -/
@[ext]
/--
Definition of `Snowflaking` / `Snowflaking` 的定义

English:
structure Snowflaking
  parameters: (X : Type*) (α : Real) (hα₀ : 0 < α) (hα₁ : α <= 1)
  axioms and operations (1):
    - val : X

中文:
结构 Snowflaking
  参数: (X : 类型) (α : 实数) (hα₀ : 0 < α) (hα₁ : α <= 1)
  公理与运算 (1 个):
    - val : X
-/
structure Snowflaking (X : Type*) (α : Real) (hα₀ : 0 < α) (hα₁ : α <= 1) where
  /-- The value wrapped in `x : Snowflaking X α hα₀ hα₁`. -/
  val : X

namespace Snowflaking

variable {X : Type*} {α : Real} {hα₀ : 0 < α} {hα₁ : α <= 1}

/--
Definition of `ofSnowflaking` / `ofSnowflaking` 的定义

English:
definition ofSnowflaking
  signature: : Snowflaking X α hα₀ hα₁ ≃ X where
  body: val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 ofSnowflaking
  签名: : Snowflaking X α hα₀ hα₁ ≃ X where
  定义体: val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
-/
def ofSnowflaking : Snowflaking X α hα₀ hα₁ ≃ X where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/--
Definition of `toSnowflaking` / `toSnowflaking` 的定义

English:
definition toSnowflaking
  signature: : X ≃ Snowflaking X α hα₀ hα₁
  body: ofSnowflaking.symm

@[simp]

中文:
定义 toSnowflaking
  签名: : X ≃ Snowflaking X α hα₀ hα₁
  定义体: ofSnowflaking.symm

@[simp]

Depends on / 依赖: ofSnowflaking, ofSnowflaking.symm
-/
def toSnowflaking : X ≃ Snowflaking X α hα₀ hα₁ := ofSnowflaking.symm

@[simp]
/--
theorem `toSnowflaking.sizeOf_spec` / 定理 `toSnowflaking.sizeOf_spec`

English:
theorem toSnowflaking.sizeOf_spec
  given: [SizeOf X] (x : X)
  proof: rfl

中文:
定理 toSnowflaking.sizeOf_spec
  条件: [SizeOf X] (x : X)
  证明: rfl
-/
theorem toSnowflaking.sizeOf_spec [SizeOf X] (x : X) :
    sizeOf (toSnowflaking x : Snowflaking X α hα₀ hα₁) = 1 + sizeOf x :=
  rfl

attribute [nolint simpNF] mk.injEq

/-- This definition makes `cases x` and `induction x` use `toSnowflaking` instead of `mk`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `casesOn_toSnowflaking` / `casesOn_toSnowflaking` 的定义

English:
definition casesOn_toSnowflaking
  signature: {motive : Snowflaking X α hα₀ hα₁ -> Sort*}
  body: toSnowflaking x.val

@[simp]

中文:
定义 casesOn_toSnowflaking
  签名: {motive : Snowflaking X α hα₀ hα₁ -> 类型层*}
  定义体: toSnowflaking x.val

@[simp]

Depends on / 依赖: toSnowflaking, x.val
-/
def casesOn_toSnowflaking {motive : Snowflaking X α hα₀ hα₁ -> Sort*}
    (toSnowflaking : forall x, motive (Snowflaking.toSnowflaking x)) (x : Snowflaking X α hα₀ hα₁) :
    motive x :=
  toSnowflaking x.val

@[simp]
/--
theorem `mk_eq_toSnowflaking` / 定理 `mk_eq_toSnowflaking`

English:
theorem mk_eq_toSnowflaking
  statement: (mk : X -> Snowflaking X α hα₀ hα₁) = toSnowflaking
  proof: rfl

@[simp]

中文:
定理 mk_eq_toSnowflaking
  结论: (mk : X -> Snowflaking X α hα₀ hα₁) = toSnowflaking
  证明: rfl

@[simp]
-/
theorem mk_eq_toSnowflaking : (mk : X -> Snowflaking X α hα₀ hα₁) = toSnowflaking := rfl

@[simp]
/--
theorem `val_eq_ofSnowflaking` / 定理 `val_eq_ofSnowflaking`

English:
theorem val_eq_ofSnowflaking
  statement: (val : Snowflaking X α hα₀ hα₁ -> X) = ofSnowflaking
  proof: rfl

@[simp]

中文:
定理 val_eq_ofSnowflaking
  结论: (val : Snowflaking X α hα₀ hα₁ -> X) = ofSnowflaking
  证明: rfl

@[simp]
-/
theorem val_eq_ofSnowflaking : (val : Snowflaking X α hα₀ hα₁ -> X) = ofSnowflaking := rfl

@[simp]
/--
theorem `symm_toSnowflaking` / 定理 `symm_toSnowflaking`

English:
theorem symm_toSnowflaking
  proof: rfl

@[simp]

中文:
定理 symm_toSnowflaking
  证明: rfl

@[simp]
-/
theorem symm_toSnowflaking :
    (toSnowflaking : X ≃ Snowflaking X α hα₀ hα₁).symm = ofSnowflaking :=
  rfl

@[simp]
/--
theorem `symm_ofSnowflaking` / 定理 `symm_ofSnowflaking`

English:
theorem symm_ofSnowflaking
  proof: rfl

@[simp]

中文:
定理 symm_ofSnowflaking
  证明: rfl

@[simp]
-/
theorem symm_ofSnowflaking :
    (ofSnowflaking : Snowflaking X α hα₀ hα₁ ≃ X).symm = toSnowflaking :=
  rfl

@[simp]
/--
theorem `toSnowflaking_ofSnowflaking` / 定理 `toSnowflaking_ofSnowflaking`

English:
theorem toSnowflaking_ofSnowflaking
  given: (x : Snowflaking X α hα₀ hα₁)
  proof: rfl

@[simp]

中文:
定理 toSnowflaking_ofSnowflaking
  条件: (x : Snowflaking X α hα₀ hα₁)
  证明: rfl

@[simp]
-/
theorem toSnowflaking_ofSnowflaking (x : Snowflaking X α hα₀ hα₁) :
    toSnowflaking x.ofSnowflaking = x :=
  rfl

@[simp]
/--
theorem `ofSnowflaking_toSnowflaking` / 定理 `ofSnowflaking_toSnowflaking`

English:
theorem ofSnowflaking_toSnowflaking
  given: (x : X)
  proof: rfl

@[simp]

中文:
定理 ofSnowflaking_toSnowflaking
  条件: (x : X)
  证明: rfl

@[simp]
-/
theorem ofSnowflaking_toSnowflaking (x : X) :
    (toSnowflaking x : Snowflaking X α hα₀ hα₁).ofSnowflaking = x :=
  rfl

@[simp]
/--
theorem `ofSnowflaking_comp_toSnowflaking` / 定理 `ofSnowflaking_comp_toSnowflaking`

English:
theorem ofSnowflaking_comp_toSnowflaking
  proof: rfl

@[simp]

中文:
定理 ofSnowflaking_comp_toSnowflaking
  证明: rfl

@[simp]
-/
theorem ofSnowflaking_comp_toSnowflaking :
    (ofSnowflaking : Snowflaking X α hα₀ hα₁ -> X) ∘ toSnowflaking = id :=
  rfl

@[simp]
/--
theorem `toSnowflaking_comp_ofSnowflaking` / 定理 `toSnowflaking_comp_ofSnowflaking`

English:
theorem toSnowflaking_comp_ofSnowflaking
  proof: rfl

中文:
定理 toSnowflaking_comp_ofSnowflaking
  证明: rfl
-/
theorem toSnowflaking_comp_ofSnowflaking :
    (toSnowflaking : X -> Snowflaking X α hα₀ hα₁) ∘ ofSnowflaking = id :=
  rfl

/--
theorem `image_toSnowflaking_eq_preimage` / 定理 `image_toSnowflaking_eq_preimage`

English:
theorem image_toSnowflaking_eq_preimage
  given: (s : Set X)
  proof: toSnowflaking.image_eq_preimage_symm _

中文:
定理 image_toSnowflaking_eq_preimage
  条件: (s : 集合 X)
  证明: toSnowflaking.image_eq_preimage_symm _

Depends on / 依赖: image_eq_preimage_symm, toSnowflaking, toSnowflaking.image_eq_preimage_symm
-/
theorem image_toSnowflaking_eq_preimage (s : Set X) :
    (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) = ofSnowflaking ⁻¹' s :=
  toSnowflaking.image_eq_preimage_symm _

/--
theorem `image_ofSnowflaking_eq_preimage` / 定理 `image_ofSnowflaking_eq_preimage`

English:
theorem image_ofSnowflaking_eq_preimage
  given: (s : Set (Snowflaking X α hα₀ hα₁))
  proof: ofSnowflaking.image_eq_preimage_symm _

@[simp]

中文:
定理 image_ofSnowflaking_eq_preimage
  条件: (s : 集合 (Snowflaking X α hα₀ hα₁))
  证明: ofSnowflaking.image_eq_preimage_symm _

@[simp]

Depends on / 依赖: image_eq_preimage_symm, ofSnowflaking, ofSnowflaking.image_eq_preimage_symm
-/
theorem image_ofSnowflaking_eq_preimage (s : Set (Snowflaking X α hα₀ hα₁)) :
    ofSnowflaking '' s = toSnowflaking ⁻¹' s :=
  ofSnowflaking.image_eq_preimage_symm _

@[simp]
/--
theorem `image_toSnowflaking_image_ofSnowflaking` / 定理 `image_toSnowflaking_image_ofSnowflaking`

English:
theorem image_toSnowflaking_image_ofSnowflaking
  given: (s : Set (Snowflaking X α hα₀ hα₁))
  proof: ofSnowflaking.symm_image_image _

@[simp]

中文:
定理 image_toSnowflaking_image_ofSnowflaking
  条件: (s : 集合 (Snowflaking X α hα₀ hα₁))
  证明: ofSnowflaking.symm_image_image _

@[simp]

Depends on / 依赖: ofSnowflaking, ofSnowflaking.symm_image_image, symm_image_image
-/
theorem image_toSnowflaking_image_ofSnowflaking (s : Set (Snowflaking X α hα₀ hα₁)) :
    toSnowflaking '' ofSnowflaking '' s = s :=
  ofSnowflaking.symm_image_image _

@[simp]
/--
theorem `image_ofSnowflaking_image_toSnowflaking` / 定理 `image_ofSnowflaking_image_toSnowflaking`

English:
theorem image_ofSnowflaking_image_toSnowflaking
  given: (s : Set X)
  proof: ofSnowflaking.image_symm_image _

中文:
定理 image_ofSnowflaking_image_toSnowflaking
  条件: (s : 集合 X)
  证明: ofSnowflaking.image_symm_image _

Depends on / 依赖: image_symm_image, ofSnowflaking, ofSnowflaking.image_symm_image
-/
theorem image_ofSnowflaking_image_toSnowflaking (s : Set X) :
    ofSnowflaking '' (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) = s :=
  ofSnowflaking.image_symm_image _

/-!
### Topological space structure

The topology on `Snowflaking X α hα₀ hα₁` is induced from `X`.
-/

section TopologicalSpace

variable [TopologicalSpace X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (Snowflaking X α hα₀ hα₁)
  body: .induced Snowflaking.ofSnowflaking ‹_›

@[fun_prop]

中文:
实例 :
  签名: 拓扑空间 (Snowflaking X α hα₀ hα₁)
  定义体: .induced Snowflaking.ofSnowflaking ‹_›

@[fun_prop]

Depends on / 依赖: Snowflaking, Snowflaking.ofSnowflaking, induced, ofSnowflaking
-/
instance : TopologicalSpace (Snowflaking X α hα₀ hα₁) := .induced Snowflaking.ofSnowflaking ‹_›

@[fun_prop]
/--
theorem `continuous_ofSnowflaking` / 定理 `continuous_ofSnowflaking`

English:
theorem continuous_ofSnowflaking
  statement: Continuous (ofSnowflaking : Snowflaking X α hα₀ hα₁ -> X)
  proof: continuous_induced_dom

@[fun_prop]

中文:
定理 continuous_ofSnowflaking
  结论: 连续 (ofSnowflaking : Snowflaking X α hα₀ hα₁ -> X)
  证明: continuous_induced_dom

@[fun_prop]

Depends on / 依赖: continuous_induced_dom
-/
theorem continuous_ofSnowflaking : Continuous (ofSnowflaking : Snowflaking X α hα₀ hα₁ -> X) :=
  continuous_induced_dom

@[fun_prop]
/--
theorem `continuous_toSnowflaking` / 定理 `continuous_toSnowflaking`

English:
theorem continuous_toSnowflaking
  statement: Continuous (toSnowflaking : X -> Snowflaking X α hα₀ hα₁)
  proof: continuous_induced_rng.2 continuous_id

中文:
定理 continuous_toSnowflaking
  结论: 连续 (toSnowflaking : X -> Snowflaking X α hα₀ hα₁)
  证明: continuous_induced_rng.2 continuous_id

Depends on / 依赖: continuous_id, continuous_induced_rng
-/
theorem continuous_toSnowflaking : Continuous (toSnowflaking : X -> Snowflaking X α hα₀ hα₁) :=
  continuous_induced_rng.2 continuous_id

/-- The natural homeomorphism between `Snowflaking X α hα₀ hα₁` and `X`. -/
@[simps! -fullyApplied toEquiv apply symm_apply]
/--
Definition of `homeomorph` / `homeomorph` 的定义

English:
definition homeomorph
  signature: : Snowflaking X α hα₀ hα₁ ≃ₜ X where
  body: ofSnowflaking
  continuous_invFun := continuous_toSnowflaking

中文:
定义 homeomorph
  签名: : Snowflaking X α hα₀ hα₁ ≃ₜ X where
  定义体: ofSnowflaking
  continuous_invFun := continuous_toSnowflaking

Depends on / 依赖: ofSnowflaking
-/
def homeomorph : Snowflaking X α hα₀ hα₁ ≃ₜ X where
  toEquiv := ofSnowflaking
  continuous_invFun := continuous_toSnowflaking


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T0Space
  signature: X] : T0Space (Snowflaking X α hα₀ hα₁)
  body: homeomorph.symm.t0Space

中文:
实例 [T0空间
  签名: X] : T0空间 (Snowflaking X α hα₀ hα₁)
  定义体: homeomorph.symm.t0Space

Depends on / 依赖: homeomorph, homeomorph.symm.t0Space, t0Space
-/
instance [T0Space X] : T0Space (Snowflaking X α hα₀ hα₁) :=
  homeomorph.symm.t0Space

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: X] : T2Space (Snowflaking X α hα₀ hα₁)
  body: homeomorph.symm.t2Space

中文:
实例 [T2空间
  签名: X] : T2空间 (Snowflaking X α hα₀ hα₁)
  定义体: homeomorph.symm.t2Space

Depends on / 依赖: homeomorph, homeomorph.symm.t2Space, t2Space
-/
instance [T2Space X] : T2Space (Snowflaking X α hα₀ hα₁) :=
  homeomorph.symm.t2Space

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SecondCountableTopology
  signature: X] : SecondCountableTopology (Snowflaking X α hα₀ hα₁)
  body: homeomorph.secondCountableTopology

中文:
实例 [第二可数拓扑
  签名: X] : 第二可数拓扑 (Snowflaking X α hα₀ hα₁)
  定义体: homeomorph.secondCountableTopology

Depends on / 依赖: homeomorph, homeomorph.secondCountableTopology, secondCountableTopology
-/
instance [SecondCountableTopology X] : SecondCountableTopology (Snowflaking X α hα₀ hα₁) :=
  homeomorph.secondCountableTopology

end TopologicalSpace

/-!
### Bornology

The bornology on `Snowflaking X α hα₀ hα₁` is induced from `X`.
-/

section Bornology

variable [Bornology X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bornology (Snowflaking X α hα₀ hα₁)
  body: .induced ofSnowflaking

中文:
实例 :
  签名: 有界结构 (Snowflaking X α hα₀ hα₁)
  定义体: .induced ofSnowflaking

Depends on / 依赖: induced, ofSnowflaking
-/
instance : Bornology (Snowflaking X α hα₀ hα₁) := .induced ofSnowflaking

open Bornology

@[simp]
/--
theorem `isBounded_image_ofSnowflaking_iff` / 定理 `isBounded_image_ofSnowflaking_iff`

English:
theorem isBounded_image_ofSnowflaking_iff
  given: {s : Set (Snowflaking X α hα₀ hα₁)}
  proof: isBounded_induced.symm

@[simp]

中文:
定理 isBounded_image_ofSnowflaking_iff
  条件: {s : 集合 (Snowflaking X α hα₀ hα₁)}
  证明: isBounded_induced.symm

@[simp]

Depends on / 依赖: isBounded_induced, isBounded_induced.symm
-/
theorem isBounded_image_ofSnowflaking_iff {s : Set (Snowflaking X α hα₀ hα₁)} :
    IsBounded (ofSnowflaking '' s) ↔ IsBounded s :=
  isBounded_induced.symm

@[simp]
/--
theorem `isBounded_preimage_toSnowflaking_iff` / 定理 `isBounded_preimage_toSnowflaking_iff`

English:
theorem isBounded_preimage_toSnowflaking_iff
  given: {s : Set (Snowflaking X α hα₀ hα₁)}
  proof: by
  rw [← image_ofSnowflaking_eq_preimage]; rw [isBounded_image_ofSnowflaking_iff]

@[simp]

中文:
定理 isBounded_preimage_toSnowflaking_iff
  条件: {s : 集合 (Snowflaking X α hα₀ hα₁)}
  证明: by
  rw [← image_ofSnowflaking_eq_preimage]; rw [isBounded_image_ofSnowflaking_iff]

@[simp]

Depends on / 依赖: image_ofSnowflaking_eq_preimage, isBounded_image_ofSnowflaking_iff
-/
theorem isBounded_preimage_toSnowflaking_iff {s : Set (Snowflaking X α hα₀ hα₁)} :
    IsBounded (toSnowflaking ⁻¹' s) ↔ IsBounded s := by
  rw [← image_ofSnowflaking_eq_preimage]; rw [isBounded_image_ofSnowflaking_iff]

@[simp]
/--
theorem `isBounded_image_toSnowflaking_iff` / 定理 `isBounded_image_toSnowflaking_iff`

English:
theorem isBounded_image_toSnowflaking_iff
  given: {s : Set X}
  proof: by
  rw [← isBounded_image_ofSnowflaking_iff]; rw [image_ofSnowflaking_image_toSnowflaking]

@[simp]

中文:
定理 isBounded_image_toSnowflaking_iff
  条件: {s : 集合 X}
  证明: by
  rw [← isBounded_image_ofSnowflaking_iff]; rw [image_ofSnowflaking_image_toSnowflaking]

@[simp]

Depends on / 依赖: image_ofSnowflaking_image_toSnowflaking, isBounded_image_ofSnowflaking_iff
-/
theorem isBounded_image_toSnowflaking_iff {s : Set X} :
    IsBounded (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← isBounded_image_ofSnowflaking_iff]; rw [image_ofSnowflaking_image_toSnowflaking]

@[simp]
/--
theorem `isBounded_preimage_ofSnowflaking_iff` / 定理 `isBounded_preimage_ofSnowflaking_iff`

English:
theorem isBounded_preimage_ofSnowflaking_iff
  given: {s : Set X}
  proof: by
  rw [← image_toSnowflaking_eq_preimage]; rw [isBounded_image_toSnowflaking_iff]

中文:
定理 isBounded_preimage_ofSnowflaking_iff
  条件: {s : 集合 X}
  证明: by
  rw [← image_toSnowflaking_eq_preimage]; rw [isBounded_image_toSnowflaking_iff]

Depends on / 依赖: image_toSnowflaking_eq_preimage, isBounded_image_toSnowflaking_iff
-/
theorem isBounded_preimage_ofSnowflaking_iff {s : Set X} :
    IsBounded (ofSnowflaking ⁻¹' s : Set (Snowflaking X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← image_toSnowflaking_eq_preimage]; rw [isBounded_image_toSnowflaking_iff]

end Bornology

/-!
### Uniform space structure

The uniform space structure on `Snowflaking X α hα₀ hα₁` is induced from `X`.
-/

section UniformSpace

variable [UniformSpace X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformSpace (Snowflaking X α hα₀ hα₁)
  body: UniformSpace.comap Snowflaking.ofSnowflaking ‹_›

中文:
实例 :
  签名: 一致空间 (Snowflaking X α hα₀ hα₁)
  定义体: UniformSpace.comap Snowflaking.ofSnowflaking ‹_›

Depends on / 依赖: Snowflaking, Snowflaking.ofSnowflaking, UniformSpace, UniformSpace.comap, ofSnowflaking
-/
instance : UniformSpace (Snowflaking X α hα₀ hα₁) :=
  UniformSpace.comap Snowflaking.ofSnowflaking ‹_›

/--
theorem `uniformContinuous_ofSnowflaking` / 定理 `uniformContinuous_ofSnowflaking`

English:
theorem uniformContinuous_ofSnowflaking
  proof: uniformContinuous_comap

中文:
定理 uniformContinuous_ofSnowflaking
  证明: uniformContinuous_comap

Depends on / 依赖: uniformContinuous_comap
-/
theorem uniformContinuous_ofSnowflaking :
    UniformContinuous (ofSnowflaking : Snowflaking X α hα₀ hα₁ -> X) :=
  uniformContinuous_comap

/--
theorem `uniformContinuous_toSnowflaking` / 定理 `uniformContinuous_toSnowflaking`

English:
theorem uniformContinuous_toSnowflaking
  proof: uniformContinuous_comap' uniformContinuous_id

中文:
定理 uniformContinuous_toSnowflaking
  证明: uniformContinuous_comap' uniformContinuous_id

Depends on / 依赖: uniformContinuous_comap, uniformContinuous_id
-/
theorem uniformContinuous_toSnowflaking :
    UniformContinuous (toSnowflaking : X -> Snowflaking X α hα₀ hα₁) :=
  uniformContinuous_comap' uniformContinuous_id

/-- The natural uniform space equivalence between `Snowflaking X α hα hα₁`
and the underlying space. -/
@[simps! toEquiv apply symm_apply]
/--
Definition of `uniformEquiv` / `uniformEquiv` 的定义

English:
definition uniformEquiv
  signature: : Snowflaking X α hα₀ hα₁ ≃ᵤ X where
  body: ofSnowflaking
  uniformContinuous_toFun := uniformContinuous_ofSnowflaking
  uniformContinuous_invFun := uniformContinuous_toSnowflaking

中文:
定义 uniformEquiv
  签名: : Snowflaking X α hα₀ hα₁ ≃ᵤ X where
  定义体: ofSnowflaking
  uniformContinuous_toFun := uniformContinuous_ofSnowflaking
  uniformContinuous_invFun := uniformContinuous_toSnowflaking

Depends on / 依赖: ofSnowflaking
-/
def uniformEquiv : Snowflaking X α hα₀ hα₁ ≃ᵤ X where
  toEquiv := ofSnowflaking
  uniformContinuous_toFun := uniformContinuous_ofSnowflaking
  uniformContinuous_invFun := uniformContinuous_toSnowflaking

end UniformSpace

/-!
### Extended distance and a (pseudo) extended metric space structure

Th extended distance on `Snowflaking X α hα₀ hα₁`
is given by `edist x y = (edist x.ofSnowflaking y.ofSnowflaking) ^ α`.

If the original space is a (pseudo) extended metric space, then so is `Snowflaking X α hα₀ hα₁`.
-/

section EDist

variable [EDist X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EDist (Snowflaking X α hα₀ hα₁)
  body: edist x.ofSnowflaking y.ofSnowflaking ^ α

中文:
实例 :
  签名: EDist (Snowflaking X α hα₀ hα₁)
  定义体: edist x.ofSnowflaking y.ofSnowflaking ^ α

Depends on / 依赖: ofSnowflaking, x.ofSnowflaking, y.ofSnowflaking
-/
instance : EDist (Snowflaking X α hα₀ hα₁) where
  edist x y := edist x.ofSnowflaking y.ofSnowflaking ^ α

/--
theorem `edist_def` / 定理 `edist_def`

English:
theorem edist_def
  given: (x y : Snowflaking X α hα₀ hα₁)
  proof: rfl

@[simp]

中文:
定理 edist_def
  条件: (x y : Snowflaking X α hα₀ hα₁)
  证明: rfl

@[simp]
-/
theorem edist_def (x y : Snowflaking X α hα₀ hα₁) :
    edist x y = edist x.ofSnowflaking y.ofSnowflaking ^ α :=
  rfl

@[simp]
/--
theorem `edist_toSnowflaking_toSnowflaking` / 定理 `edist_toSnowflaking_toSnowflaking`

English:
theorem edist_toSnowflaking_toSnowflaking
  given: (x y : X)
  proof: rfl

@[simp]

中文:
定理 edist_toSnowflaking_toSnowflaking
  条件: (x y : X)
  证明: rfl

@[simp]
-/
theorem edist_toSnowflaking_toSnowflaking (x y : X) :
    edist (toSnowflaking x : Snowflaking X α hα₀ hα₁) (toSnowflaking y) = edist x y ^ α :=
  rfl

@[simp]
/--
theorem `edist_ofSnowflaking_ofSnowflaking` / 定理 `edist_ofSnowflaking_ofSnowflaking`

English:
theorem edist_ofSnowflaking_ofSnowflaking
  given: (x y : Snowflaking X α hα₀ hα₁)
  proof: by
  rw [edist_def]; rw [ENNReal.rpow_rpow_inv hα₀.ne']

中文:
定理 edist_ofSnowflaking_ofSnowflaking
  条件: (x y : Snowflaking X α hα₀ hα₁)
  证明: by
  rw [edist_def]; rw [ENNReal.rpow_rpow_inv hα₀.ne']

Depends on / 依赖: ENNReal, ENNReal.rpow_rpow_inv, edist_def, rpow_rpow_inv
-/
theorem edist_ofSnowflaking_ofSnowflaking (x y : Snowflaking X α hα₀ hα₁) :
    edist x.ofSnowflaking y.ofSnowflaking = edist x y ^ α⁻¹ := by
  rw [edist_def]; rw [ENNReal.rpow_rpow_inv hα₀.ne']

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoEMetricSpace (Snowflaking X α hα₀ hα₁)
  body: by simp [edist_def, hα₀]
  edist_comm x y := by rw [edist_def, edist_def, edist_comm]
  edist_triangle x y z := by
    simp only [edist_def]
    grw [edist_triangle x.ofSnowflaking y.ofSnowflaking z.ofSnowflaking,
      ENNReal.rpow_add_le_add_rpow _ _ hα₀.le hα₁]
  toUniformSpace := inferInstance
  uniformity_edist := by
    have H : (𝓤 X).HasBasis (0 < ·) fun x => {p | edist p.1 p.2 < x ^ (α⁻¹)} := by
      refine EMetric.mk_uniformity_basis (fun _ _ => by positivity) fun ε hε =>
        ⟨ε ^ α, by positivity, ?_⟩
      rw [ENNReal.rpow_rpow_inv hα₀.ne']
    simp (disch := positivity) [uniformity_comap, H.eq_biInf, ENNReal.rpow_lt_rpow_iff]

@[simp]

中文:
实例 :
  签名: PseudoEMetric空间 (Snowflaking X α hα₀ hα₁)
  定义体: by simp [edist_def, hα₀]
  edist_comm x y := by rw [edist_def, edist_def, edist_comm]
  edist_triangle x y z := by
    simp only [edist_def]
    grw [edist_triangle x.ofSnowflaking y.ofSnowflaking z.ofSnowflaking,
      ENNReal.rpow_add_le_add_rpow _ _ hα₀.le hα₁]
  toUniformSpace := inferInstance
  uniformity_edist := by
    have H : (𝓤 X).HasBasis (0 < ·) fun x => {p | edist p.1 p.2 < x ^ (α⁻¹)} := by
      refine EMetric.mk_uniformity_basis (fun _ _ => by positivity) fun ε hε =>
        ⟨ε ^ α, by positivity, ?_⟩
      rw [ENNReal.rpow_rpow_inv hα₀.ne']
    simp (disch := positivity) [uniformity_comap, H.eq_biInf, ENNReal.rpow_lt_rpow_iff]

@[simp]

Depends on / 依赖: EMetric, EMetric.mk_uniformity_basis, ENNReal, ENNReal.rpow_add_le_add_rpow, ENNReal.rpow_r, HasBasis, edist_comm, edist_def, edist_triangle, mk_uniformity_basis, ofSnowflaking, rpow_add_le_add_rpow, rpow_r, toUniformSpace, uniformity_edist, x.ofSnowflaking, y.ofSnowflaking, z.ofSnowflaking
-/
instance : PseudoEMetricSpace (Snowflaking X α hα₀ hα₁) where
  edist_self x := by simp [edist_def, hα₀]
  edist_comm x y := by rw [edist_def, edist_def, edist_comm]
  edist_triangle x y z := by
    simp only [edist_def]
    grw [edist_triangle x.ofSnowflaking y.ofSnowflaking z.ofSnowflaking,
      ENNReal.rpow_add_le_add_rpow _ _ hα₀.le hα₁]
  toUniformSpace := inferInstance
  uniformity_edist := by
    have H : (𝓤 X).HasBasis (0 < ·) fun x => {p | edist p.1 p.2 < x ^ (α⁻¹)} := by
      refine EMetric.mk_uniformity_basis (fun _ _ => by positivity) fun ε hε =>
        ⟨ε ^ α, by positivity, ?_⟩
      rw [ENNReal.rpow_rpow_inv hα₀.ne']
    simp (disch := positivity) [uniformity_comap, H.eq_biInf, ENNReal.rpow_lt_rpow_iff]

@[simp]
/--
theorem `preimage_ofSnowflaking_eball` / 定理 `preimage_ofSnowflaking_eball`

English:
theorem preimage_ofSnowflaking_eball
  given: (x : X) (r : Real>=0∞)
  proof: by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_lt_rpow_iff]

@[deprecated (since := "2026-01-24")]
alias preimage_ofSnowflaking_emetricBall := preimage_ofSnowflaking_eball

@[simp]

中文:
定理 preimage_ofSnowflaking_eball
  条件: (x : X) (r : 实数>=0∞)
  证明: by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_lt_rpow_iff]

@[deprecated (since := "2026-01-24")]
alias preimage_ofSnowflaking_emetricBall := preimage_ofSnowflaking_eball

@[simp]

Depends on / 依赖: ENNReal, ENNReal.rpow_lt_rpow_iff, rpow_lt_rpow_iff
-/
theorem preimage_ofSnowflaking_eball (x : X) (r : Real>=0∞) :
    ofSnowflaking ⁻¹' Metric.eball x r =
      Metric.eball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_lt_rpow_iff]

@[deprecated (since := "2026-01-24")]
alias preimage_ofSnowflaking_emetricBall := preimage_ofSnowflaking_eball

@[simp]
/--
theorem `image_toSnowflaking_eball` / 定理 `image_toSnowflaking_eball`

English:
theorem image_toSnowflaking_eball
  given: (x : X) (r : Real>=0∞)
  proof: by
  rw [image_toSnowflaking_eq_preimage]; rw [preimage_ofSnowflaking_eball]

@[deprecated (since := "2026-01-24")]
alias image_toSnowflaking_emetricBall := image_toSnowflaking_eball

@[simp]

中文:
定理 image_toSnowflaking_eball
  条件: (x : X) (r : 实数>=0∞)
  证明: by
  rw [image_toSnowflaking_eq_preimage]; rw [preimage_ofSnowflaking_eball]

@[deprecated (since := "2026-01-24")]
alias image_toSnowflaking_emetricBall := image_toSnowflaking_eball

@[simp]

Depends on / 依赖: image_toSnowflaking_eq_preimage, preimage_ofSnowflaking_eball
-/
theorem image_toSnowflaking_eball (x : X) (r : Real>=0∞) :
    toSnowflaking '' Metric.eball x r =
      Metric.eball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  rw [image_toSnowflaking_eq_preimage]; rw [preimage_ofSnowflaking_eball]

@[deprecated (since := "2026-01-24")]
alias image_toSnowflaking_emetricBall := image_toSnowflaking_eball

@[simp]
/--
theorem `preimage_toSnowflaking_eball` / 定理 `preimage_toSnowflaking_eball`

English:
theorem preimage_toSnowflaking_eball
  given: (x : Snowflaking X α hα₀ hα₁) (d : Real>=0∞)
  proof: by
  rw [toSnowflaking.preimage_eq_iff_eq_image]; rw [image_toSnowflaking_eball]; rw [toSnowflaking_ofSnowflaking]; rw [ENNReal.rpow_inv_rpow hα₀.ne']

@[deprecated (since := "2026-01-24")]
alias preimage_toSnowflaking_emetricBall := preimage_toSnowflaking_eball

@[simp]

中文:
定理 preimage_toSnowflaking_eball
  条件: (x : Snowflaking X α hα₀ hα₁) (d : 实数>=0∞)
  证明: by
  rw [toSnowflaking.preimage_eq_iff_eq_image]; rw [image_toSnowflaking_eball]; rw [toSnowflaking_ofSnowflaking]; rw [ENNReal.rpow_inv_rpow hα₀.ne']

@[deprecated (since := "2026-01-24")]
alias preimage_toSnowflaking_emetricBall := preimage_toSnowflaking_eball

@[simp]

Depends on / 依赖: ENNReal, ENNReal.rpow_inv_rpow, image_toSnowflaking_eball, preimage_eq_iff_eq_image, rpow_inv_rpow, toSnowflaking, toSnowflaking.preimage_eq_iff_eq_image, toSnowflaking_ofSnowflaking
-/
theorem preimage_toSnowflaking_eball (x : Snowflaking X α hα₀ hα₁) (d : Real>=0∞) :
    toSnowflaking ⁻¹' Metric.eball x d = Metric.eball x.ofSnowflaking (d ^ α⁻¹) := by
  rw [toSnowflaking.preimage_eq_iff_eq_image]; rw [image_toSnowflaking_eball]; rw [toSnowflaking_ofSnowflaking]; rw [ENNReal.rpow_inv_rpow hα₀.ne']

@[deprecated (since := "2026-01-24")]
alias preimage_toSnowflaking_emetricBall := preimage_toSnowflaking_eball

@[simp]
/--
theorem `image_ofSnowflaking_eball` / 定理 `image_ofSnowflaking_eball`

English:
theorem image_ofSnowflaking_eball
  given: (x : Snowflaking X α hα₀ hα₁) (d : Real>=0∞)
  proof: by
  rw [image_ofSnowflaking_eq_preimage]; rw [preimage_toSnowflaking_eball]

@[deprecated (since := "2026-01-24")]
alias image_ofSnowflaking_emetricBall := image_ofSnowflaking_eball

@[simp]

中文:
定理 image_ofSnowflaking_eball
  条件: (x : Snowflaking X α hα₀ hα₁) (d : 实数>=0∞)
  证明: by
  rw [image_ofSnowflaking_eq_preimage]; rw [preimage_toSnowflaking_eball]

@[deprecated (since := "2026-01-24")]
alias image_ofSnowflaking_emetricBall := image_ofSnowflaking_eball

@[simp]

Depends on / 依赖: image_ofSnowflaking_eq_preimage, preimage_toSnowflaking_eball
-/
theorem image_ofSnowflaking_eball (x : Snowflaking X α hα₀ hα₁) (d : Real>=0∞) :
    ofSnowflaking '' Metric.eball x d = Metric.eball x.ofSnowflaking (d ^ α⁻¹) := by
  rw [image_ofSnowflaking_eq_preimage]; rw [preimage_toSnowflaking_eball]

@[deprecated (since := "2026-01-24")]
alias image_ofSnowflaking_emetricBall := image_ofSnowflaking_eball

@[simp]
/--
theorem `preimage_ofSnowflaking_closedEBall` / 定理 `preimage_ofSnowflaking_closedEBall`

English:
theorem preimage_ofSnowflaking_closedEBall
  given: (x : X) (r : Real>=0∞)
  proof: by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_le_rpow_iff]

@[deprecated (since := "2026-01-24")]
alias preimage_ofSnowflaking_emetricClosedBall := preimage_ofSnowflaking_closedEBall

@[simp]

中文:
定理 preimage_ofSnowflaking_closedEBall
  条件: (x : X) (r : 实数>=0∞)
  证明: by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_le_rpow_iff]

@[deprecated (since := "2026-01-24")]
alias preimage_ofSnowflaking_emetricClosedBall := preimage_ofSnowflaking_closedEBall

@[simp]

Depends on / 依赖: ENNReal, ENNReal.rpow_le_rpow_iff, rpow_le_rpow_iff
-/
theorem preimage_ofSnowflaking_closedEBall (x : X) (r : Real>=0∞) :
    ofSnowflaking ⁻¹' Metric.closedEBall x r =
      Metric.closedEBall (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_le_rpow_iff]

@[deprecated (since := "2026-01-24")]
alias preimage_ofSnowflaking_emetricClosedBall := preimage_ofSnowflaking_closedEBall

@[simp]
/--
theorem `image_toSnowflaking_closedEBall` / 定理 `image_toSnowflaking_closedEBall`

English:
theorem image_toSnowflaking_closedEBall
  given: (x : X) (r : Real>=0∞)
  proof: by
  rw [image_toSnowflaking_eq_preimage]; rw [preimage_ofSnowflaking_closedEBall]

@[deprecated (since := "2026-01-24")]
alias image_toSnowflaking_emetricClosedBall := image_toSnowflaking_closedEBall

@[simp]

中文:
定理 image_toSnowflaking_closedEBall
  条件: (x : X) (r : 实数>=0∞)
  证明: by
  rw [image_toSnowflaking_eq_preimage]; rw [preimage_ofSnowflaking_closedEBall]

@[deprecated (since := "2026-01-24")]
alias image_toSnowflaking_emetricClosedBall := image_toSnowflaking_closedEBall

@[simp]

Depends on / 依赖: image_toSnowflaking_eq_preimage, preimage_ofSnowflaking_closedEBall
-/
theorem image_toSnowflaking_closedEBall (x : X) (r : Real>=0∞) :
    toSnowflaking '' Metric.closedEBall x r =
      Metric.closedEBall (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  rw [image_toSnowflaking_eq_preimage]; rw [preimage_ofSnowflaking_closedEBall]

@[deprecated (since := "2026-01-24")]
alias image_toSnowflaking_emetricClosedBall := image_toSnowflaking_closedEBall

@[simp]
/--
theorem `preimage_toSnowflaking_closedEBall` / 定理 `preimage_toSnowflaking_closedEBall`

English:
theorem preimage_toSnowflaking_closedEBall
  given: (x : Snowflaking X α hα₀ hα₁) (d : Real>=0∞)
  proof: by
  rw [toSnowflaking.preimage_eq_iff_eq_image]; rw [image_toSnowflaking_closedEBall]; rw [toSnowflaking_ofSnowflaking]; rw [ENNReal.rpow_inv_rpow hα₀.ne']

@[deprecated (since := "2026-01-24")]
alias preimage_toSnowflaking_emetricClosedBall := preimage_toSnowflaking_closedEBall

@[simp]

中文:
定理 preimage_toSnowflaking_closedEBall
  条件: (x : Snowflaking X α hα₀ hα₁) (d : 实数>=0∞)
  证明: by
  rw [toSnowflaking.preimage_eq_iff_eq_image]; rw [image_toSnowflaking_closedEBall]; rw [toSnowflaking_ofSnowflaking]; rw [ENNReal.rpow_inv_rpow hα₀.ne']

@[deprecated (since := "2026-01-24")]
alias preimage_toSnowflaking_emetricClosedBall := preimage_toSnowflaking_closedEBall

@[simp]

Depends on / 依赖: ENNReal, ENNReal.rpow_inv_rpow, image_toSnowflaking_closedEBall, preimage_eq_iff_eq_image, rpow_inv_rpow, toSnowflaking, toSnowflaking.preimage_eq_iff_eq_image, toSnowflaking_ofSnowflaking
-/
theorem preimage_toSnowflaking_closedEBall (x : Snowflaking X α hα₀ hα₁) (d : Real>=0∞) :
    toSnowflaking ⁻¹' Metric.closedEBall x d = Metric.closedEBall x.ofSnowflaking (d ^ α⁻¹) := by
  rw [toSnowflaking.preimage_eq_iff_eq_image]; rw [image_toSnowflaking_closedEBall]; rw [toSnowflaking_ofSnowflaking]; rw [ENNReal.rpow_inv_rpow hα₀.ne']

@[deprecated (since := "2026-01-24")]
alias preimage_toSnowflaking_emetricClosedBall := preimage_toSnowflaking_closedEBall

@[simp]
/--
theorem `image_ofSnowflaking_closedEBall` / 定理 `image_ofSnowflaking_closedEBall`

English:
theorem image_ofSnowflaking_closedEBall
  given: (x : Snowflaking X α hα₀ hα₁) (d : Real>=0∞)
  proof: by
  rw [image_ofSnowflaking_eq_preimage]; rw [preimage_toSnowflaking_closedEBall]

@[deprecated (since := "2026-01-24")]
alias image_ofSnowflaking_emetricClosedBall := image_ofSnowflaking_closedEBall

@[simp]

中文:
定理 image_ofSnowflaking_closedEBall
  条件: (x : Snowflaking X α hα₀ hα₁) (d : 实数>=0∞)
  证明: by
  rw [image_ofSnowflaking_eq_preimage]; rw [preimage_toSnowflaking_closedEBall]

@[deprecated (since := "2026-01-24")]
alias image_ofSnowflaking_emetricClosedBall := image_ofSnowflaking_closedEBall

@[simp]

Depends on / 依赖: image_ofSnowflaking_eq_preimage, preimage_toSnowflaking_closedEBall
-/
theorem image_ofSnowflaking_closedEBall (x : Snowflaking X α hα₀ hα₁) (d : Real>=0∞) :
    ofSnowflaking '' Metric.closedEBall x d =
      Metric.closedEBall x.ofSnowflaking (d ^ α⁻¹) := by
  rw [image_ofSnowflaking_eq_preimage]; rw [preimage_toSnowflaking_closedEBall]

@[deprecated (since := "2026-01-24")]
alias image_ofSnowflaking_emetricClosedBall := image_ofSnowflaking_closedEBall

@[simp]
/--
theorem `ediam_image_ofSnowflaking` / 定理 `ediam_image_ofSnowflaking`

English:
theorem ediam_image_ofSnowflaking
  given: (s : Set (Snowflaking X α hα₀ hα₁))
  proof: by
  refine eq_of_forall_ge_iff fun c => ?_
  simp only [ENNReal.rpow_inv_le_iff hα₀, ediam_le_iff, Set.forall_mem_image,
    edist_ofSnowflaking_ofSnowflaking]

@[simp]

中文:
定理 ediam_image_ofSnowflaking
  条件: (s : 集合 (Snowflaking X α hα₀ hα₁))
  证明: by
  refine eq_of_forall_ge_iff fun c => ?_
  simp only [ENNReal.rpow_inv_le_iff hα₀, ediam_le_iff, Set.forall_mem_image,
    edist_ofSnowflaking_ofSnowflaking]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.rpow_inv_le_iff, Set.forall_mem_image, ediam_le_iff, edist_ofSnowflaking_ofSnowflaking, eq_of_forall_ge_iff, forall_mem_image, rpow_inv_le_iff
-/
theorem ediam_image_ofSnowflaking (s : Set (Snowflaking X α hα₀ hα₁)) :
    ediam (ofSnowflaking '' s) = ediam s ^ α⁻¹ := by
  refine eq_of_forall_ge_iff fun c => ?_
  simp only [ENNReal.rpow_inv_le_iff hα₀, ediam_le_iff, Set.forall_mem_image,
    edist_ofSnowflaking_ofSnowflaking]

@[simp]
/--
theorem `ediam_preimage_toSnowflaking` / 定理 `ediam_preimage_toSnowflaking`

English:
theorem ediam_preimage_toSnowflaking
  given: (s : Set (Snowflaking X α hα₀ hα₁))
  proof: by
  rw [← image_ofSnowflaking_eq_preimage]; rw [ediam_image_ofSnowflaking]

@[simp]

中文:
定理 ediam_preimage_toSnowflaking
  条件: (s : 集合 (Snowflaking X α hα₀ hα₁))
  证明: by
  rw [← image_ofSnowflaking_eq_preimage]; rw [ediam_image_ofSnowflaking]

@[simp]

Depends on / 依赖: ediam_image_ofSnowflaking, image_ofSnowflaking_eq_preimage
-/
theorem ediam_preimage_toSnowflaking (s : Set (Snowflaking X α hα₀ hα₁)) :
    ediam (toSnowflaking ⁻¹' s) = ediam s ^ α⁻¹ := by
  rw [← image_ofSnowflaking_eq_preimage]; rw [ediam_image_ofSnowflaking]

@[simp]
/--
theorem `ediam_preimage_ofSnowflaking` / 定理 `ediam_preimage_ofSnowflaking`

English:
theorem ediam_preimage_ofSnowflaking
  given: (s : Set X)
  proof: by
  rw [← ENNReal.rpow_inv_rpow hα₀.ne' (ediam _)]; rw [← ediam_preimage_toSnowflaking]; rw [← Set.preimage_comp]; rw [ofSnowflaking_comp_toSnowflaking]; rw [Set.preimage_id]

@[simp]

中文:
定理 ediam_preimage_ofSnowflaking
  条件: (s : 集合 X)
  证明: by
  rw [← ENNReal.rpow_inv_rpow hα₀.ne' (ediam _)]; rw [← ediam_preimage_toSnowflaking]; rw [← Set.preimage_comp]; rw [ofSnowflaking_comp_toSnowflaking]; rw [Set.preimage_id]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.rpow_inv_rpow, Set.preimage_comp, Set.preimage_id, ediam_preimage_toSnowflaking, ofSnowflaking_comp_toSnowflaking, preimage_comp, preimage_id, rpow_inv_rpow
-/
theorem ediam_preimage_ofSnowflaking (s : Set X) :
    ediam (ofSnowflaking ⁻¹' s : Set (Snowflaking X α hα₀ hα₁)) = ediam s ^ α := by
  rw [← ENNReal.rpow_inv_rpow hα₀.ne' (ediam _)]; rw [← ediam_preimage_toSnowflaking]; rw [← Set.preimage_comp]; rw [ofSnowflaking_comp_toSnowflaking]; rw [Set.preimage_id]

@[simp]
/--
theorem `ediam_image_toSnowflaking` / 定理 `ediam_image_toSnowflaking`

English:
theorem ediam_image_toSnowflaking
  given: (s : Set X)
  proof: by
  simp [image_toSnowflaking_eq_preimage]

中文:
定理 ediam_image_toSnowflaking
  条件: (s : 集合 X)
  证明: by
  simp [image_toSnowflaking_eq_preimage]

Depends on / 依赖: image_toSnowflaking_eq_preimage
-/
theorem ediam_image_toSnowflaking (s : Set X) :
    ediam (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) = ediam s ^ α := by
  simp [image_toSnowflaking_eq_preimage]

end PseudoEMetricSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EMetricSpace
  signature: X] : EMetricSpace (Snowflaking X α hα₀ hα₁)
  body: .ofT0PseudoEMetricSpace _

中文:
实例 [广义度量空间
  签名: X] : 广义度量空间 (Snowflaking X α hα₀ hα₁)
  定义体: .ofT0PseudoEMetricSpace _

Depends on / 依赖: ofT0PseudoEMetricSpace
-/
instance [EMetricSpace X] : EMetricSpace (Snowflaking X α hα₀ hα₁) :=
  .ofT0PseudoEMetricSpace _


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Dist
  signature: X] : Dist (Snowflaking X α hα₀ hα₁) where
  body: dist x.ofSnowflaking y.ofSnowflaking ^ α

@[simp]

中文:
实例 [Dist
  签名: X] : Dist (Snowflaking X α hα₀ hα₁) where
  定义体: dist x.ofSnowflaking y.ofSnowflaking ^ α

@[simp]

Depends on / 依赖: ofSnowflaking, x.ofSnowflaking, y.ofSnowflaking
-/
instance [Dist X] : Dist (Snowflaking X α hα₀ hα₁) where
  dist x y := dist x.ofSnowflaking y.ofSnowflaking ^ α

@[simp]
/--
theorem `dist_toSnowflaking_toSnowflaking` / 定理 `dist_toSnowflaking_toSnowflaking`

English:
theorem dist_toSnowflaking_toSnowflaking
  given: [Dist X] (x y : X)
  proof: rfl

中文:
定理 dist_toSnowflaking_toSnowflaking
  条件: [Dist X] (x y : X)
  证明: rfl
-/
theorem dist_toSnowflaking_toSnowflaking [Dist X] (x y : X) :
    dist (toSnowflaking x : Snowflaking X α hα₀ hα₁) (toSnowflaking y) = dist x y ^ α :=
  rfl

section PseudoMetricSpace

variable [PseudoMetricSpace X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoMetricSpace (Snowflaking X α hα₀ hα₁)
  body: letI aux : PseudoMetricSpace (Snowflaking X α hα₀ hα₁) :=
    PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
      (by intro x y; cases x; cases y; rw [dist_toSnowflaking_toSnowflaking]; positivity)
      (by
        intro x y; cases x; cases y
        rw [edist_toSnowflaking_toSnowflaking]; rw [dist_toSnowflaking_toSnowflaking]; rw [← ENNReal.ofReal_rpow_of_nonneg]; rw [← edist_dist] <;> positivity)
  aux.replaceBornology fun s => by
    rw [← isBounded_preimage_toSnowflaking_iff]; rw [Metric.isBounded_iff]; rw [Metric.isBounded_iff]
    constructor
    · rintro ⟨C, hC⟩
      use C ^ α
      rintro ⟨x⟩ hx ⟨y⟩ hy
      grw [mk_eq_toSnowflaking, dist_toSnowflaking_toSnowflaking, hC hx hy]
    · rintro ⟨C, hC⟩
      use C ^ α⁻¹
      intro x hx y hy
      grw [← hC hx hy, dist_toSnowflaking_toSnowflaking, Real.rpow_rpow_inv (by positivity) hα₀.ne']

中文:
实例 :
  签名: 伪度量空间 (Snowflaking X α hα₀ hα₁)
  定义体: letI aux : PseudoMetricSpace (Snowflaking X α hα₀ hα₁) :=
    PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
      (by intro x y; cases x; cases y; rw [dist_toSnowflaking_toSnowflaking]; positivity)
      (by
        intro x y; cases x; cases y
        rw [edist_toSnowflaking_toSnowflaking]; rw [dist_toSnowflaking_toSnowflaking]; rw [← ENNReal.ofReal_rpow_of_nonneg]; rw [← edist_dist] <;> positivity)
  aux.replaceBornology fun s => by
    rw [← isBounded_preimage_toSnowflaking_iff]; rw [Metric.isBounded_iff]; rw [Metric.isBounded_iff]
    constructor
    · rintro ⟨C, hC⟩
      use C ^ α
      rintro ⟨x⟩ hx ⟨y⟩ hy
      grw [mk_eq_toSnowflaking, dist_toSnowflaking_toSnowflaking, hC hx hy]
    · rintro ⟨C, hC⟩
      use C ^ α⁻¹
      intro x hx y hy
      grw [← hC hx hy, dist_toSnowflaking_toSnowflaking, Real.rpow_rpow_inv (by positivity) hα₀.ne']

Depends on / 依赖: ENNReal, ENNReal.ofReal_rpow_of_nonneg, Metric, Metric.isBounded, Metric.isBounded_iff, PseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpaceOfDist, PseudoMetricSpace, Snowflaking, aux.replaceBornology, dist_toSnowflaking_toSnowflaking, edist_dist, edist_toSnowflaking_toSnowflaking, isBounded, isBounded_iff, isBounded_preimage_toSnowflaking_iff, ofReal_rpow_of_nonneg, replaceBornology, toPseudoMetricSpaceOfDist
-/
instance : PseudoMetricSpace (Snowflaking X α hα₀ hα₁) :=
  letI aux : PseudoMetricSpace (Snowflaking X α hα₀ hα₁) :=
    PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
      (by intro x y; cases x; cases y; rw [dist_toSnowflaking_toSnowflaking]; positivity)
      (by
        intro x y; cases x; cases y
        rw [edist_toSnowflaking_toSnowflaking]; rw [dist_toSnowflaking_toSnowflaking]; rw [← ENNReal.ofReal_rpow_of_nonneg]; rw [← edist_dist] <;> positivity)
  aux.replaceBornology fun s => by
    rw [← isBounded_preimage_toSnowflaking_iff]; rw [Metric.isBounded_iff]; rw [Metric.isBounded_iff]
    constructor
    · rintro ⟨C, hC⟩
      use C ^ α
      rintro ⟨x⟩ hx ⟨y⟩ hy
      grw [mk_eq_toSnowflaking, dist_toSnowflaking_toSnowflaking, hC hx hy]
    · rintro ⟨C, hC⟩
      use C ^ α⁻¹
      intro x hx y hy
      grw [← hC hx hy, dist_toSnowflaking_toSnowflaking, Real.rpow_rpow_inv (by positivity) hα₀.ne']

open Metric

@[simp]
/--
theorem `dist_ofSnowflaking_ofSnowflaking` / 定理 `dist_ofSnowflaking_ofSnowflaking`

English:
theorem dist_ofSnowflaking_ofSnowflaking
  given: (x y : Snowflaking X α hα₀ hα₁)
  proof: by
  cases x; cases y
  simp [Real.rpow_rpow_inv dist_nonneg hα₀.ne']

@[simp]

中文:
定理 dist_ofSnowflaking_ofSnowflaking
  条件: (x y : Snowflaking X α hα₀ hα₁)
  证明: by
  cases x; cases y
  simp [Real.rpow_rpow_inv dist_nonneg hα₀.ne']

@[simp]

Depends on / 依赖: Real.rpow_rpow_inv, dist_nonneg, rpow_rpow_inv
-/
theorem dist_ofSnowflaking_ofSnowflaking (x y : Snowflaking X α hα₀ hα₁) :
    dist x.ofSnowflaking y.ofSnowflaking = dist x y ^ α⁻¹ := by
  cases x; cases y
  simp [Real.rpow_rpow_inv dist_nonneg hα₀.ne']

@[simp]
/--
theorem `preimage_ofSnowflaking_ball` / 定理 `preimage_ofSnowflaking_ball`

English:
theorem preimage_ofSnowflaking_ball
  given: (x : X) {r : Real} (hr : 0 <= r)
  proof: by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_lt_rpow_iff]

@[simp]

中文:
定理 preimage_ofSnowflaking_ball
  条件: (x : X) {r : 实数} (hr : 0 <= r)
  证明: by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_lt_rpow_iff]

@[simp]

Depends on / 依赖: Real.rpow_lt_rpow_iff, rpow_lt_rpow_iff
-/
theorem preimage_ofSnowflaking_ball (x : X) {r : Real} (hr : 0 <= r) :
    ofSnowflaking ⁻¹' ball x r = ball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_lt_rpow_iff]

@[simp]
/--
theorem `image_toSnowflaking_ball` / 定理 `image_toSnowflaking_ball`

English:
theorem image_toSnowflaking_ball
  given: (x : X) {r : Real} (hr : 0 <= r)
  proof: by
  rw [image_toSnowflaking_eq_preimage]; rw [preimage_ofSnowflaking_ball x hr]

@[simp]

中文:
定理 image_toSnowflaking_ball
  条件: (x : X) {r : 实数} (hr : 0 <= r)
  证明: by
  rw [image_toSnowflaking_eq_preimage]; rw [preimage_ofSnowflaking_ball x hr]

@[simp]

Depends on / 依赖: image_toSnowflaking_eq_preimage, preimage_ofSnowflaking_ball
-/
theorem image_toSnowflaking_ball (x : X) {r : Real} (hr : 0 <= r) :
    toSnowflaking '' ball x r = ball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  rw [image_toSnowflaking_eq_preimage]; rw [preimage_ofSnowflaking_ball x hr]

@[simp]
/--
theorem `preimage_toSnowflaking_ball` / 定理 `preimage_toSnowflaking_ball`

English:
theorem preimage_toSnowflaking_ball
  given: (x : Snowflaking X α hα₀ hα₁) {r : Real} (hr : 0 <= r)
  proof: by
  rw [toSnowflaking.preimage_eq_iff_eq_image]; rw [image_toSnowflaking_ball _ (by positivity)]; rw [toSnowflaking_ofSnowflaking]; rw [Real.rpow_inv_rpow hr hα₀.ne']

@[simp]

中文:
定理 preimage_toSnowflaking_ball
  条件: (x : Snowflaking X α hα₀ hα₁) {r : 实数} (hr : 0 <= r)
  证明: by
  rw [toSnowflaking.preimage_eq_iff_eq_image]; rw [image_toSnowflaking_ball _ (by positivity)]; rw [toSnowflaking_ofSnowflaking]; rw [Real.rpow_inv_rpow hr hα₀.ne']

@[simp]

Depends on / 依赖: Real.rpow_inv_rpow, image_toSnowflaking_ball, preimage_eq_iff_eq_image, rpow_inv_rpow, toSnowflaking, toSnowflaking.preimage_eq_iff_eq_image, toSnowflaking_ofSnowflaking
-/
theorem preimage_toSnowflaking_ball (x : Snowflaking X α hα₀ hα₁) {r : Real} (hr : 0 <= r) :
    toSnowflaking ⁻¹' ball x r = ball x.ofSnowflaking (r ^ α⁻¹) := by
  rw [toSnowflaking.preimage_eq_iff_eq_image]; rw [image_toSnowflaking_ball _ (by positivity)]; rw [toSnowflaking_ofSnowflaking]; rw [Real.rpow_inv_rpow hr hα₀.ne']

@[simp]
/--
theorem `image_ofSnowflaking_ball` / 定理 `image_ofSnowflaking_ball`

English:
theorem image_ofSnowflaking_ball
  given: (x : Snowflaking X α hα₀ hα₁) {r : Real} (hr : 0 <= r)
  proof: by
  rw [image_ofSnowflaking_eq_preimage]; rw [preimage_toSnowflaking_ball _ hr]

@[simp]

中文:
定理 image_ofSnowflaking_ball
  条件: (x : Snowflaking X α hα₀ hα₁) {r : 实数} (hr : 0 <= r)
  证明: by
  rw [image_ofSnowflaking_eq_preimage]; rw [preimage_toSnowflaking_ball _ hr]

@[simp]

Depends on / 依赖: image_ofSnowflaking_eq_preimage, preimage_toSnowflaking_ball
-/
theorem image_ofSnowflaking_ball (x : Snowflaking X α hα₀ hα₁) {r : Real} (hr : 0 <= r) :
    ofSnowflaking '' ball x r = ball x.ofSnowflaking (r ^ α⁻¹) := by
  rw [image_ofSnowflaking_eq_preimage]; rw [preimage_toSnowflaking_ball _ hr]

@[simp]
/--
theorem `preimage_ofSnowflaking_closedBall` / 定理 `preimage_ofSnowflaking_closedBall`

English:
theorem preimage_ofSnowflaking_closedBall
  given: (x : X) {r : Real} (hr : 0 <= r)
  proof: by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_le_rpow_iff]

@[simp]

中文:
定理 preimage_ofSnowflaking_closedBall
  条件: (x : X) {r : 实数} (hr : 0 <= r)
  证明: by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_le_rpow_iff]

@[simp]

Depends on / 依赖: Real.rpow_le_rpow_iff, rpow_le_rpow_iff
-/
theorem preimage_ofSnowflaking_closedBall (x : X) {r : Real} (hr : 0 <= r) :
    ofSnowflaking ⁻¹' closedBall x r =
      closedBall (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_le_rpow_iff]

@[simp]
/--
theorem `image_toSnowflaking_closedBall` / 定理 `image_toSnowflaking_closedBall`

English:
theorem image_toSnowflaking_closedBall
  given: (x : X) {r : Real} (hr : 0 <= r)
  proof: by
  rw [image_toSnowflaking_eq_preimage]; rw [preimage_ofSnowflaking_closedBall x hr]

@[simp]

中文:
定理 image_toSnowflaking_closedBall
  条件: (x : X) {r : 实数} (hr : 0 <= r)
  证明: by
  rw [image_toSnowflaking_eq_preimage]; rw [preimage_ofSnowflaking_closedBall x hr]

@[simp]

Depends on / 依赖: image_toSnowflaking_eq_preimage, preimage_ofSnowflaking_closedBall
-/
theorem image_toSnowflaking_closedBall (x : X) {r : Real} (hr : 0 <= r) :
    toSnowflaking '' closedBall x r =
      closedBall (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  rw [image_toSnowflaking_eq_preimage]; rw [preimage_ofSnowflaking_closedBall x hr]

@[simp]
/--
theorem `preimage_toSnowflaking_closedBall` / 定理 `preimage_toSnowflaking_closedBall`

English:
theorem preimage_toSnowflaking_closedBall
  given: (x : Snowflaking X α hα₀ hα₁) {r : Real} (hr : 0 <= r)
  proof: by
  rw [toSnowflaking.preimage_eq_iff_eq_image]; rw [image_toSnowflaking_closedBall _ (by positivity)]; rw [toSnowflaking_ofSnowflaking]; rw [Real.rpow_inv_rpow hr hα₀.ne']

@[simp]

中文:
定理 preimage_toSnowflaking_closedBall
  条件: (x : Snowflaking X α hα₀ hα₁) {r : 实数} (hr : 0 <= r)
  证明: by
  rw [toSnowflaking.preimage_eq_iff_eq_image]; rw [image_toSnowflaking_closedBall _ (by positivity)]; rw [toSnowflaking_ofSnowflaking]; rw [Real.rpow_inv_rpow hr hα₀.ne']

@[simp]

Depends on / 依赖: Real.rpow_inv_rpow, image_toSnowflaking_closedBall, preimage_eq_iff_eq_image, rpow_inv_rpow, toSnowflaking, toSnowflaking.preimage_eq_iff_eq_image, toSnowflaking_ofSnowflaking
-/
theorem preimage_toSnowflaking_closedBall (x : Snowflaking X α hα₀ hα₁) {r : Real} (hr : 0 <= r) :
    toSnowflaking ⁻¹' closedBall x r = closedBall x.ofSnowflaking (r ^ α⁻¹) := by
  rw [toSnowflaking.preimage_eq_iff_eq_image]; rw [image_toSnowflaking_closedBall _ (by positivity)]; rw [toSnowflaking_ofSnowflaking]; rw [Real.rpow_inv_rpow hr hα₀.ne']

@[simp]
/--
theorem `image_ofSnowflaking_closedBall` / 定理 `image_ofSnowflaking_closedBall`

English:
theorem image_ofSnowflaking_closedBall
  given: (x : Snowflaking X α hα₀ hα₁) {r : Real} (hr : 0 <= r)
  proof: by
  rw [image_ofSnowflaking_eq_preimage]; rw [preimage_toSnowflaking_closedBall _ hr]

中文:
定理 image_ofSnowflaking_closedBall
  条件: (x : Snowflaking X α hα₀ hα₁) {r : 实数} (hr : 0 <= r)
  证明: by
  rw [image_ofSnowflaking_eq_preimage]; rw [preimage_toSnowflaking_closedBall _ hr]

Depends on / 依赖: image_ofSnowflaking_eq_preimage, preimage_toSnowflaking_closedBall
-/
theorem image_ofSnowflaking_closedBall (x : Snowflaking X α hα₀ hα₁) {r : Real} (hr : 0 <= r) :
    ofSnowflaking '' closedBall x r = closedBall x.ofSnowflaking (r ^ α⁻¹) := by
  rw [image_ofSnowflaking_eq_preimage]; rw [preimage_toSnowflaking_closedBall _ hr]

end PseudoMetricSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MetricSpace
  signature: X] : MetricSpace (Snowflaking X α hα₀ hα₁)
  body: .ofT0PseudoMetricSpace _

中文:
实例 [度量空间
  签名: X] : 度量空间 (Snowflaking X α hα₀ hα₁)
  定义体: .ofT0PseudoMetricSpace _

Depends on / 依赖: ofT0PseudoMetricSpace
-/
instance [MetricSpace X] : MetricSpace (Snowflaking X α hα₀ hα₁) :=
  .ofT0PseudoMetricSpace _

end Snowflaking
end Metric
