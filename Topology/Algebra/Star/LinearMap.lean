/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Star.LinearMap
public import Mathlib.Topology.Algebra.Module.Star

/-! # Intrinsic star operation on continuous linear maps

This file defines the star operation on continuous linear maps: `(star f) x = star (f (star x))`.
This corresponds to a map being star-preserving, i.e., a map is self-adjoint iff it
is star-preserving.

This is the continuous version of the intrinsic star on linear maps (see
`Mathlib/Algebra/Star/LinearMap.lean`).

## Implementation notes

Because there is a global `star` instance on `H →L[𝕜] H` (defined as the linear map adjoint on
Hilbert spaces), which is mathematically distinct from this `star`, we provide
this instance on `WithConv (E →L[R] F)`. -/

public section

namespace ContinuousLinearMap
variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]
  [TopologicalSpace E] [TopologicalSpace F] [ContinuousStar E] [ContinuousStar F]

open WithConv

/--
Instance `intrinsicStar` / 实例 `intrinsicStar`

English:
instance intrinsicStar
  signature: : Star (WithConv (E ->L[R] F)) where star f
  body: toConv
  { (star (toConv f.ofConv.toLinearMap)).ofConv with }

中文:
实例 intrinsicStar
  签名: : Star (WithConv (E ->L[R] F)) where star f
  定义体: toConv
  { (star (toConv f.ofConv.toLinearMap)).ofConv with }

Depends on / 依赖: toConv
-/
instance intrinsicStar : Star (WithConv (E ->L[R] F)) where star f := toConv
  { (star (toConv f.ofConv.toLinearMap)).ofConv with }

/--
theorem `intrinsicStar_apply` / 定理 `intrinsicStar_apply`

English:
theorem intrinsicStar_apply
  given: (f : WithConv (E ->L[R] F)) (x : E)
  proof: rfl

中文:
定理 intrinsicStar_apply
  条件: (f : WithConv (E ->L[R] F)) (x : E)
  证明: rfl
-/
@[simp] theorem intrinsicStar_apply (f : WithConv (E ->L[R] F)) (x : E) :
    star f x = star (f (star x)) := rfl

/--
theorem `toLinearMap_intrinsicStar` / 定理 `toLinearMap_intrinsicStar`

English:
theorem toLinearMap_intrinsicStar
  given: (f : WithConv (E ->L[R] F))
  proof: rfl

中文:
定理 toLinearMap_intrinsicStar
  条件: (f : WithConv (E ->L[R] F))
  证明: rfl
-/
@[simp] theorem toLinearMap_intrinsicStar (f : WithConv (E ->L[R] F)) :
    (star f).ofConv.toLinearMap = (star (toConv f.ofConv.toLinearMap)).ofConv := rfl

/--
theorem `IntrinsicStar.isSelfAdjoint_iff_map_star` / 定理 `IntrinsicStar.isSelfAdjoint_iff_map_star`

English:
theorem IntrinsicStar.isSelfAdjoint_iff_map_star
  given: (f : WithConv (E ->L[R] F))
  proof: by
  simp [IsSelfAdjoint, WithConv.ext_iff, ContinuousLinearMap.ext_iff, star_eq_iff_star_eq,
    eq_comm (a := f _)]

中文:
定理 IntrinsicStar.isSelfAdjoint_iff_map_star
  条件: (f : WithConv (E ->L[R] F))
  证明: by
  simp [IsSelfAdjoint, WithConv.ext_iff, ContinuousLinearMap.ext_iff, star_eq_iff_star_eq,
    eq_comm (a := f _)]
-/
theorem IntrinsicStar.isSelfAdjoint_iff_map_star (f : WithConv (E ->L[R] F)) :
    IsSelfAdjoint f ↔ forall x, f (star x) = star (f x) := by
  simp [IsSelfAdjoint, WithConv.ext_iff, ContinuousLinearMap.ext_iff, star_eq_iff_star_eq,
    eq_comm (a := f _)]

/--
theorem `IntrinsicStar.isSelfAdjoint_toLinearMap_iff` / 定理 `IntrinsicStar.isSelfAdjoint_toLinearMap_iff`

English:
theorem IntrinsicStar.isSelfAdjoint_toLinearMap_iff
  given: (f : WithConv (E ->L[R] F))
  proof: by
  simp [isSelfAdjoint_iff_map_star, LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star]

中文:
定理 IntrinsicStar.isSelfAdjoint_toLinearMap_iff
  条件: (f : WithConv (E ->L[R] F))
  证明: by
  simp [isSelfAdjoint_iff_map_star, LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star]

Depends on / 依赖: IntrinsicStar, LinearMap, LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star, isSelfAdjoint_iff_map_star
-/
theorem IntrinsicStar.isSelfAdjoint_toLinearMap_iff (f : WithConv (E ->L[R] F)) :
    IsSelfAdjoint (toConv f.ofConv.toLinearMap) ↔ IsSelfAdjoint f := by
  simp [isSelfAdjoint_iff_map_star, LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star]

/--
Instance `intrinsicInvolutiveStar` / 实例 `intrinsicInvolutiveStar`

English:
instance intrinsicInvolutiveStar
  signature: : InvolutiveStar (WithConv (E ->L[R] F)) where
  body: by ext; simp

中文:
实例 intrinsicInvolutiveStar
  签名: : InvolutiveStar (WithConv (E ->L[R] F)) where
  定义体: by ext; simp
-/
instance intrinsicInvolutiveStar : InvolutiveStar (WithConv (E ->L[R] F)) where
  star_involutive x := by ext; simp

/--
Instance `intrinsicStarAddMonoid` / 实例 `intrinsicStarAddMonoid`

English:
instance intrinsicStarAddMonoid
  signature: [ContinuousAdd F]
  body: by ext; simp

中文:
实例 intrinsicStarAddMonoid
  签名: [ContinuousAdd F]
  定义体: by ext; simp
-/
instance intrinsicStarAddMonoid [ContinuousAdd F] : StarAddMonoid (WithConv (E ->L[R] F)) where
  star_add x y := by ext; simp

/--
theorem `intrinsicStar_comp` / 定理 `intrinsicStar_comp`

English:
theorem intrinsicStar_comp
  statement: {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G]
  proof: by
  ext; simp

中文:
定理 intrinsicStar_comp
  结论: {G : 类型} [AddCommMonoid G] [Module R G] [StarAddMonoid G]
  证明: by
  ext; simp
-/
theorem intrinsicStar_comp {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G]
    [StarModule R G] [TopologicalSpace G] [ContinuousStar G] (f : WithConv (E ->L[R] F))
    (g : WithConv (G ->L[R] E)) :
    star (toConv (f.ofConv ∘L g.ofConv)) = toConv ((star f).ofConv ∘L (star g).ofConv) := by
  ext; simp

/--
theorem `intrinsicStar_comp'` / 定理 `intrinsicStar_comp'`

English:
theorem intrinsicStar_comp'
  statement: {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G]
  proof: by
  ext; simp

中文:
定理 intrinsicStar_comp'
  结论: {G : 类型} [AddCommMonoid G] [Module R G] [StarAddMonoid G]
  证明: by
  ext; simp
-/
theorem intrinsicStar_comp' {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G]
    [StarModule R G] [TopologicalSpace G] [ContinuousStar G] (f : E ->L[R] F) (g : G ->L[R] E) :
    star (toConv (f ∘L g)) = toConv ((star (toConv f)).ofConv ∘L (star (toConv g)).ofConv) := by
  ext; simp

/--
theorem `intrinsicStar_id` / 定理 `intrinsicStar_id`

English:
theorem intrinsicStar_id
  proof: by ext; simp

中文:
定理 intrinsicStar_id
  证明: by ext; simp
-/
@[simp] theorem intrinsicStar_id :
    star (toConv (ContinuousLinearMap.id R E)) = toConv (.id R E) := by ext; simp
/--
theorem `intrinsicStar_zero` / 定理 `intrinsicStar_zero`

English:
theorem intrinsicStar_zero
  statement: star (toConv (0 : E ->L[R] F)) = toConv 0
  proof: by ext; simp

中文:
定理 intrinsicStar_zero
  结论: star (toConv (0 : E ->L[R] F)) = toConv 0
  证明: by ext; simp
-/
@[simp] theorem intrinsicStar_zero : star (toConv (0 : E ->L[R] F)) = toConv 0 := by ext; simp

section starAddMonoidSemiring
variable {S : Type*} [Semiring S] [StarAddMonoid S] [StarModule S S] [Module S E] [StarModule S E]
  [TopologicalSpace S] [ContinuousStar S]

/--
theorem `intrinsicStar_toSpanSingleton` / 定理 `intrinsicStar_toSpanSingleton`

English:
theorem intrinsicStar_toSpanSingleton
  given: [ContinuousSMul S E] (a : E)
  proof: by ext; simp

中文:
定理 intrinsicStar_toSpanSingleton
  条件: [ContinuousSMul S E] (a : E)
  证明: by ext; simp
-/
@[simp] theorem intrinsicStar_toSpanSingleton [ContinuousSMul S E] (a : E) :
    star (toConv (toSpanSingleton S a)) = toConv (toSpanSingleton S (star a)) := by ext; simp

/--
theorem `intrinsicStar_smulRight` / 定理 `intrinsicStar_smulRight`

English:
theorem intrinsicStar_smulRight
  statement: [Module S F] [StarModule S F] [ContinuousSMul S F]
  proof: by
  ext; simp

中文:
定理 intrinsicStar_smulRight
  结论: [Module S F] [StarModule S F] [ContinuousSMul S F]
  证明: by
  ext; simp
-/
theorem intrinsicStar_smulRight [Module S F] [StarModule S F] [ContinuousSMul S F]
    (f : WithConv (E ->L[S] S)) (x : F) :
    star (toConv (f.ofConv.smulRight x)) = toConv ((star f).ofConv.smulRight (star x)) := by
  ext; simp

end starAddMonoidSemiring

/--
Instance `intrinsicStarModule` / 实例 `intrinsicStarModule`

English:
instance intrinsicStarModule
  signature: [SMulCommClass R R F] [ContinuousConstSMul R F]
  body: by ext; simp

中文:
实例 intrinsicStarModule
  签名: [SMulCommClass R R F] [ContinuousConstSMul R F]
  定义体: by ext; simp
-/
instance intrinsicStarModule [SMulCommClass R R F] [ContinuousConstSMul R F] :
    StarModule R (WithConv (E ->L[R] F)) where star_smul _ _ := by ext; simp

/--
lemma `intrinsicStar_eq_comp` / 引理 `intrinsicStar_eq_comp`

English:
lemma intrinsicStar_eq_comp
  statement: {R : Type*} [CommSemiring R] [StarRing R] [Module R E] [StarModule R E]
  proof: rfl

中文:
引理 intrinsicStar_eq_comp
  结论: {R : 类型} [CommSemiring R] [StarRing R] [Module R E] [StarModule R E]
  证明: rfl
-/
lemma intrinsicStar_eq_comp {R : Type*} [CommSemiring R] [StarRing R] [Module R E] [StarModule R E]
    [Module R F] [StarModule R F] (f : WithConv (E ->L[R] F)) :
    star f = toConv
      ((starL R).toContinuousLinearMap.comp (f.ofConv.comp (starL R).toContinuousLinearMap)) := rfl

end ContinuousLinearMap
