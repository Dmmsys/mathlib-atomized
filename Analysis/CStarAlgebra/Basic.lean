/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Real.Star
public import Mathlib.Topology.Algebra.Module.Star

/-!
# Normed star rings and algebras

A normed star group is a normed group with a compatible `star` which is isometric.

A C⋆-ring is a normed star group that is also a ring and that verifies the stronger
condition `‖x‖^2 ≤ ‖x⋆ * x‖` for all `x` (which actually implies equality). If a C⋆-ring is also
a star algebra, then it is a C⋆-algebra.

Note that the type classes corresponding to C⋆-algebras are defined in
`Mathlib/Analysis/CStarAlgebra/Classes`.

## TODO

- Show that `‖x⋆ * x‖ = ‖x‖^2` is equivalent to `‖x⋆ * x‖ = ‖x⋆‖ * ‖x‖`, which is used as the
  definition of C⋆-algebras in some sources (e.g. Wikipedia).

-/

@[expose] public section

assert_not_exists ContinuousLinearMap.hasOpNorm

open Topology

local postfix:max "⋆" => star

/--
Definition of `NormedStarGroup` / `NormedStarGroup` 的定义

English:
class NormedStarGroup
  parameters: (E : Type*) [SeminormedAddCommGroup E] [StarAddMonoid E]
  axioms and operations (1):
    - norm_star_le : forall x : E, ‖x⋆‖ <= ‖x‖

中文:
类 NormedStarGroup
  参数: (E : 类型) [SeminormedAddCommGroup E] [StarAddMonoid E]
  公理与运算 (1 个):
    - norm_star_le : 对任意 x : E, ‖x⋆‖ <= ‖x‖
-/
class NormedStarGroup (E : Type*) [SeminormedAddCommGroup E] [StarAddMonoid E] : Prop where
  norm_star_le : forall x : E, ‖x⋆‖ <= ‖x‖

variable {𝕜 E α : Type*}

section NormedStarGroup

variable [SeminormedAddCommGroup E] [StarAddMonoid E] [NormedStarGroup E]

@[simp]
/--
lemma `norm_star` / 引理 `norm_star`

English:
lemma norm_star
  given: (x : E)
  statement: ‖x⋆‖ = ‖x‖
  proof: le_antisymm (NormedStarGroup.norm_star_le x) (by simpa using NormedStarGroup.norm_star_le x⋆)

@[simp]

中文:
引理 norm_star
  条件: (x : E)
  结论: ‖x⋆‖ = ‖x‖
  证明: le_antisymm (NormedStarGroup.norm_star_le x) (by simpa using NormedStarGroup.norm_star_le x⋆)

@[simp]

Depends on / 依赖: NormedStarGroup, NormedStarGroup.norm_star_le, le_antisymm, norm_star_le
-/
lemma norm_star (x : E) : ‖x⋆‖ = ‖x‖ :=
  le_antisymm (NormedStarGroup.norm_star_le x) (by simpa using NormedStarGroup.norm_star_le x⋆)

@[simp]
/--
theorem `nnnorm_star` / 定理 `nnnorm_star`

English:
theorem nnnorm_star
  given: (x : E)
  statement: ‖star x‖₊ = ‖x‖₊
  proof: Subtype.ext norm_star _

中文:
定理 nnnorm_star
  条件: (x : E)
  结论: ‖star x‖₊ = ‖x‖₊
  证明: Subtype.ext norm_star _

Depends on / 依赖: Subtype, Subtype.ext, norm_star
-/
theorem nnnorm_star (x : E) : ‖star x‖₊ = ‖x‖₊ :=
Subtype.ext norm_star _

/--
Definition of `starNormedAddGroupHom` / `starNormedAddGroupHom` 的定义

English:
definition starNormedAddGroupHom
  signature: : NormedAddGroupHom E E
  body: { starAddEquiv with bound' := ⟨1, fun _ => le_trans (norm_star _).le (one_mul _).symm.le⟩ }

中文:
定义 starNormedAddGroupHom
  签名: : NormedAddGroupHom E E
  定义体: { starAddEquiv with bound' := ⟨1, fun _ => le_trans (norm_star _).le (one_mul _).symm.le⟩ }

Depends on / 依赖: le_trans, norm_star, one_mul, starAddEquiv, symm.le
-/
def starNormedAddGroupHom : NormedAddGroupHom E E :=
  { starAddEquiv with bound' := ⟨1, fun _ => le_trans (norm_star _).le (one_mul _).symm.le⟩ }

/--
theorem `star_isometry` / 定理 `star_isometry`

English:
theorem star_isometry
  statement: Isometry (star : E -> E)
  proof: show Isometry starAddEquiv from
    AddMonoidHomClass.isometry_of_norm starAddEquiv (show forall x, ‖x⋆‖ = ‖x‖ from norm_star)

中文:
定理 star_isometry
  结论: Isometry (star : E -> E)
  证明: show Isometry starAddEquiv from
    AddMonoidHomClass.isometry_of_norm starAddEquiv (show forall x, ‖x⋆‖ = ‖x‖ from norm_star)

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, Isometry, isometry_of_norm, norm_star, starAddEquiv
-/
theorem star_isometry : Isometry (star : E -> E) :=
  show Isometry starAddEquiv from
    AddMonoidHomClass.isometry_of_norm starAddEquiv (show forall x, ‖x⋆‖ = ‖x‖ from norm_star)

instance (priority := 100) NormedStarGroup.to_continuousStar : ContinuousStar E :=
  ⟨star_isometry.continuous⟩

noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedField
  signature: 𝕜] [NormedSpace 𝕜 E] [Star 𝕜] [TrivialStar 𝕜] [StarModule 𝕜 E] :
  body: norm_smul_le _ (_ : E)

中文:
实例 [NormedField
  签名: 𝕜] [NormedSpace 𝕜 E] [Star 𝕜] [TrivialStar 𝕜] [StarModule 𝕜 E] :
  定义体: norm_smul_le _ (_ : E)

Depends on / 依赖: norm_smul_le
-/
instance [NormedField 𝕜] [NormedSpace 𝕜 E] [Star 𝕜] [TrivialStar 𝕜] [StarModule 𝕜 E] :
    NormedSpace 𝕜 (selfAdjoint E) where
  norm_smul_le _ _ := norm_smul_le _ (_ : E)

variable (x : E) (r : Real)

/--
lemma `Metric.star_ball` / 引理 `Metric.star_ball`

English:
lemma Metric.star_ball
  statement: star (ball x r) = ball (star x) r
  proof: by
  simpa using star_isometry.preimage_ball (star x) r

中文:
引理 Metric.star_ball
  结论: star (ball x r) = ball (star x) r
  证明: by
  simpa using star_isometry.preimage_ball (star x) r
-/
@[simp] lemma Metric.star_ball : star (ball x r) = ball (star x) r := by
  simpa using star_isometry.preimage_ball (star x) r

/--
lemma `Metric.star_closedBall` / 引理 `Metric.star_closedBall`

English:
lemma Metric.star_closedBall
  statement: star (closedBall x r) = closedBall (star x) r
  proof: by
  simpa using star_isometry.preimage_closedBall (star x) r

中文:
引理 Metric.star_closedBall
  结论: star (closedBall x r) = closedBall (star x) r
  证明: by
  simpa using star_isometry.preimage_closedBall (star x) r
-/
@[simp] lemma Metric.star_closedBall : star (closedBall x r) = closedBall (star x) r := by
  simpa using star_isometry.preimage_closedBall (star x) r

/--
lemma `Metric.star_sphere` / 引理 `Metric.star_sphere`

English:
lemma Metric.star_sphere
  statement: star (sphere x r) = sphere (star x) r
  proof: by
  simpa using star_isometry.preimage_sphere (star x) r

中文:
引理 Metric.star_sphere
  结论: star (sphere x r) = sphere (star x) r
  证明: by
  simpa using star_isometry.preimage_sphere (star x) r
-/
@[simp] lemma Metric.star_sphere : star (sphere x r) = sphere (star x) r := by
  simpa using star_isometry.preimage_sphere (star x) r

/--
lemma `dist_star_star` / 引理 `dist_star_star`

English:
lemma dist_star_star
  given: (x y : E)
  statement: dist (star x) (star y) = dist x y
  proof: star_isometry.dist_eq x y

中文:
引理 dist_star_star
  条件: (x y : E)
  结论: dist (star x) (star y) = dist x y
  证明: star_isometry.dist_eq x y
-/
@[simp] lemma dist_star_star (x y : E) : dist (star x) (star y) = dist x y :=
  star_isometry.dist_eq x y

/--
lemma `edist_star_star` / 引理 `edist_star_star`

English:
lemma edist_star_star
  given: (x y : E)
  statement: edist (star x) (star y) = edist x y
  proof: star_isometry.edist_eq x y

中文:
引理 edist_star_star
  条件: (x y : E)
  结论: edist (star x) (star y) = edist x y
  证明: star_isometry.edist_eq x y
-/
@[simp] lemma edist_star_star (x y : E) : edist (star x) (star y) = edist x y :=
  star_isometry.edist_eq x y

/--
lemma `nndist_star_star` / 引理 `nndist_star_star`

English:
lemma nndist_star_star
  given: (x y : E)
  statement: nndist (star x) (star y) = nndist x y
  proof: star_isometry.nndist_eq x y

中文:
引理 nndist_star_star
  条件: (x y : E)
  结论: nndist (star x) (star y) = nndist x y
  证明: star_isometry.nndist_eq x y
-/
@[simp] lemma nndist_star_star (x y : E) : nndist (star x) (star y) = nndist x y :=
  star_isometry.nndist_eq x y

end NormedStarGroup

/--
Instance `RingHomIsometric.starRingEnd` / 实例 `RingHomIsometric.starRingEnd`

English:
instance RingHomIsometric.starRingEnd
  signature: [NormedCommRing E] [StarRing E] [NormedStarGroup E]
  body: ⟨@norm_star _ _ _ _⟩

中文:
实例 RingHomIsometric.starRingEnd
  签名: [NormedCommRing E] [StarRing E] [NormedStarGroup E]
  定义体: ⟨@norm_star _ _ _ _⟩

Depends on / 依赖: norm_star
-/
instance RingHomIsometric.starRingEnd [NormedCommRing E] [StarRing E] [NormedStarGroup E] :
    RingHomIsometric (starRingEnd E) :=
  ⟨@norm_star _ _ _ _⟩

/--
Definition of `CStarRing` / `CStarRing` 的定义

English:
class CStarRing
  parameters: (E : Type*) [NonUnitalNormedRing E] [StarRing E]
  axioms and operations (1):
    - norm_mul_self_le : forall x : E, ‖x‖ * ‖x‖ <= ‖x⋆ * x‖

中文:
类 CStarRing
  参数: (E : 类型) [NonUnitalNormedRing E] [StarRing E]
  公理与运算 (1 个):
    - norm_mul_self_le : 对任意 x : E, ‖x‖ * ‖x‖ <= ‖x⋆ * x‖
-/
class CStarRing (E : Type*) [NonUnitalNormedRing E] [StarRing E] : Prop where
  norm_mul_self_le : forall x : E, ‖x‖ * ‖x‖ <= ‖x⋆ * x‖

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CStarRing Real
  body: by simp

中文:
实例 :
  签名: CStarRing 实数
  定义体: by simp
-/
instance : CStarRing Real where
  norm_mul_self_le x := by simp

namespace CStarRing

section NonUnital

/--
lemma `of_le_norm_mul_star_self` / 引理 `of_le_norm_mul_star_self`

English:
lemma of_le_norm_mul_star_self
  proof: have : NormedStarGroup E :=
    { norm_star_le x := by
        obtain (hx | hx) := eq_zero_or_norm_pos x⋆
        · simp [hx]
        · refine le_of_mul_le_mul_right ?_ hx
.trans norm_mul_le _ _ } simpa [sq, mul_comm ‖x⋆‖] using h x⋆
⟨star_involutive.surjective.forall.mpr by simpa⟩

中文:
引理 of_le_norm_mul_star_self
  证明: have : NormedStarGroup E :=
    { norm_star_le x := by
        obtain (hx | hx) := eq_zero_or_norm_pos x⋆
        · simp [hx]
        · refine le_of_mul_le_mul_right ?_ hx
.trans norm_mul_le _ _ } simpa [sq, mul_comm ‖x⋆‖] using h x⋆
⟨star_involutive.surjective.forall.mpr by simpa⟩

Depends on / 依赖: NormedStarGroup, eq_zero_or_norm_pos, le_of_mul_le_mul_right, mul_comm, norm_mul_le, norm_star_le, star_involutive, star_involutive.surjective.forall.mpr, surjective
-/
lemma of_le_norm_mul_star_self
    [NonUnitalNormedRing E] [StarRing E]
    (h : forall x : E, ‖x‖ * ‖x‖ <= ‖x * x⋆‖) : CStarRing E :=
  have : NormedStarGroup E :=
    { norm_star_le x := by
        obtain (hx | hx) := eq_zero_or_norm_pos x⋆
        · simp [hx]
        · refine le_of_mul_le_mul_right ?_ hx
.trans norm_mul_le _ _ } simpa [sq, mul_comm ‖x⋆‖] using h x⋆
⟨star_involutive.surjective.forall.mpr by simpa⟩

variable [NonUnitalNormedRing E] [StarRing E] [CStarRing E]

-- see Note [lower instance priority]
/-- In a C⋆-ring, star preserves the norm. -/
instance (priority := 100) to_normedStarGroup : NormedStarGroup E where
  norm_star_le x := by
    obtain (hx | hx) := eq_zero_or_norm_pos x⋆
    · simp [hx]
    · refine le_of_mul_le_mul_right ?_ hx
.trans norm_mul_le _ _ simpa using norm_mul_self_le (x := x⋆)

/--
theorem `norm_star_mul_self` / 定理 `norm_star_mul_self`

English:
theorem norm_star_mul_self
  given: {x : E}
  statement: ‖x⋆ * x‖ = ‖x‖ * ‖x‖
  proof: le_antisymm ((norm_mul_le _ _).trans (by rw [norm_star])) (CStarRing.norm_mul_self_le x)

中文:
定理 norm_star_mul_self
  条件: {x : E}
  结论: ‖x⋆ * x‖ = ‖x‖ * ‖x‖
  证明: le_antisymm ((norm_mul_le _ _).trans (by rw [norm_star])) (CStarRing.norm_mul_self_le x)

Depends on / 依赖: CStarRing, CStarRing.norm_mul_self_le, le_antisymm, norm_mul_le, norm_mul_self_le, norm_star
-/
theorem norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x‖ * ‖x‖ :=
  le_antisymm ((norm_mul_le _ _).trans (by rw [norm_star])) (CStarRing.norm_mul_self_le x)

/--
theorem `norm_self_mul_star` / 定理 `norm_self_mul_star`

English:
theorem norm_self_mul_star
  given: {x : E}
  statement: ‖x * x⋆‖ = ‖x‖ * ‖x‖
  proof: by
  nth_rw 1 [← star_star x]
  simp only [norm_star_mul_self, norm_star]

中文:
定理 norm_self_mul_star
  条件: {x : E}
  结论: ‖x * x⋆‖ = ‖x‖ * ‖x‖
  证明: by
  nth_rw 1 [← star_star x]
  simp only [norm_star_mul_self, norm_star]

Depends on / 依赖: norm_star, norm_star_mul_self, nth_rw, star_star
-/
theorem norm_self_mul_star {x : E} : ‖x * x⋆‖ = ‖x‖ * ‖x‖ := by
  nth_rw 1 [← star_star x]
  simp only [norm_star_mul_self, norm_star]

/--
theorem `norm_star_mul_self'` / 定理 `norm_star_mul_self'`

English:
theorem norm_star_mul_self'
  given: {x : E}
  statement: ‖x⋆ * x‖ = ‖x⋆‖ * ‖x‖
  proof: by rw [norm_star_mul_self, norm_star]

中文:
定理 norm_star_mul_self'
  条件: {x : E}
  结论: ‖x⋆ * x‖ = ‖x⋆‖ * ‖x‖
  证明: by rw [norm_star_mul_self, norm_star]

Depends on / 依赖: norm_star, norm_star_mul_self
-/
theorem norm_star_mul_self' {x : E} : ‖x⋆ * x‖ = ‖x⋆‖ * ‖x‖ := by rw [norm_star_mul_self, norm_star]

/--
theorem `nnnorm_self_mul_star` / 定理 `nnnorm_self_mul_star`

English:
theorem nnnorm_self_mul_star
  given: {x : E}
  statement: ‖x * x⋆‖₊ = ‖x‖₊ * ‖x‖₊
  proof: Subtype.ext norm_self_mul_star

中文:
定理 nnnorm_self_mul_star
  条件: {x : E}
  结论: ‖x * x⋆‖₊ = ‖x‖₊ * ‖x‖₊
  证明: Subtype.ext norm_self_mul_star

Depends on / 依赖: Subtype, Subtype.ext, norm_self_mul_star
-/
theorem nnnorm_self_mul_star {x : E} : ‖x * x⋆‖₊ = ‖x‖₊ * ‖x‖₊ :=
  Subtype.ext norm_self_mul_star

/--
theorem `nnnorm_star_mul_self` / 定理 `nnnorm_star_mul_self`

English:
theorem nnnorm_star_mul_self
  given: {x : E}
  statement: ‖x⋆ * x‖₊ = ‖x‖₊ * ‖x‖₊
  proof: Subtype.ext norm_star_mul_self

中文:
定理 nnnorm_star_mul_self
  条件: {x : E}
  结论: ‖x⋆ * x‖₊ = ‖x‖₊ * ‖x‖₊
  证明: Subtype.ext norm_star_mul_self

Depends on / 依赖: Subtype, Subtype.ext, norm_star_mul_self
-/
theorem nnnorm_star_mul_self {x : E} : ‖x⋆ * x‖₊ = ‖x‖₊ * ‖x‖₊ :=
  Subtype.ext norm_star_mul_self

/--
lemma `_root_.IsSelfAdjoint.norm_mul_self` / 引理 `_root_.IsSelfAdjoint.norm_mul_self`

English:
lemma _root_.IsSelfAdjoint.norm_mul_self
  given: {x : E} (hx : IsSelfAdjoint x)
  proof: by
  simpa [sq, hx.star_eq] using CStarRing.norm_star_mul_self (x := x)

中文:
引理 _root_.IsSelfAdjoint.norm_mul_self
  条件: {x : E} (hx : IsSelfAdjoint x)
  证明: by
  simpa [sq, hx.star_eq] using CStarRing.norm_star_mul_self (x := x)

Depends on / 依赖: CStarRing, CStarRing.norm_star_mul_self, hx.star_eq, norm_star_mul_self, star_eq
-/
lemma _root_.IsSelfAdjoint.norm_mul_self {x : E} (hx : IsSelfAdjoint x) :
    ‖x * x‖ = ‖x‖ ^ 2 := by
  simpa [sq, hx.star_eq] using CStarRing.norm_star_mul_self (x := x)

/--
lemma `_root_.IsSelfAdjoint.nnnorm_mul_self` / 引理 `_root_.IsSelfAdjoint.nnnorm_mul_self`

English:
lemma _root_.IsSelfAdjoint.nnnorm_mul_self
  given: {x : E} (hx : IsSelfAdjoint x)
  proof: Subtype.ext hx.norm_mul_self

@[simp]

中文:
引理 _root_.IsSelfAdjoint.nnnorm_mul_self
  条件: {x : E} (hx : IsSelfAdjoint x)
  证明: Subtype.ext hx.norm_mul_self

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, hx.norm_mul_self, norm_mul_self
-/
lemma _root_.IsSelfAdjoint.nnnorm_mul_self {x : E} (hx : IsSelfAdjoint x) :
    ‖x * x‖₊ = ‖x‖₊ ^ 2 :=
  Subtype.ext hx.norm_mul_self

@[simp]
/--
theorem `star_mul_self_eq_zero_iff` / 定理 `star_mul_self_eq_zero_iff`

English:
theorem star_mul_self_eq_zero_iff
  given: (x : E)
  statement: x⋆ * x = 0 ↔ x = 0
  proof: by
  rw [← norm_eq_zero]; rw [norm_star_mul_self]
  exact mul_self_eq_zero.trans norm_eq_zero

中文:
定理 star_mul_self_eq_zero_iff
  条件: (x : E)
  结论: x⋆ * x = 0 ↔ x = 0
  证明: by
  rw [← norm_eq_zero]; rw [norm_star_mul_self]
  exact mul_self_eq_zero.trans norm_eq_zero

Depends on / 依赖: mul_self_eq_zero, mul_self_eq_zero.trans, norm_eq_zero, norm_star_mul_self
-/
theorem star_mul_self_eq_zero_iff (x : E) : x⋆ * x = 0 ↔ x = 0 := by
  rw [← norm_eq_zero]; rw [norm_star_mul_self]
  exact mul_self_eq_zero.trans norm_eq_zero

/--
theorem `star_mul_self_ne_zero_iff` / 定理 `star_mul_self_ne_zero_iff`

English:
theorem star_mul_self_ne_zero_iff
  given: (x : E)
  statement: x⋆ * x != 0 ↔ x != 0
  proof: by
  simp only [Ne, star_mul_self_eq_zero_iff]

@[simp]

中文:
定理 star_mul_self_ne_zero_iff
  条件: (x : E)
  结论: x⋆ * x != 0 ↔ x != 0
  证明: by
  simp only [Ne, star_mul_self_eq_zero_iff]

@[simp]

Depends on / 依赖: star_mul_self_eq_zero_iff
-/
theorem star_mul_self_ne_zero_iff (x : E) : x⋆ * x != 0 ↔ x != 0 := by
  simp only [Ne, star_mul_self_eq_zero_iff]

@[simp]
/--
theorem `mul_star_self_eq_zero_iff` / 定理 `mul_star_self_eq_zero_iff`

English:
theorem mul_star_self_eq_zero_iff
  given: (x : E)
  statement: x * x⋆ = 0 ↔ x = 0
  proof: by
  simpa only [star_eq_zero, star_star] using @star_mul_self_eq_zero_iff _ _ _ _ (star x)

中文:
定理 mul_star_self_eq_zero_iff
  条件: (x : E)
  结论: x * x⋆ = 0 ↔ x = 0
  证明: by
  simpa only [star_eq_zero, star_star] using @star_mul_self_eq_zero_iff _ _ _ _ (star x)

Depends on / 依赖: star_eq_zero, star_mul_self_eq_zero_iff, star_star
-/
theorem mul_star_self_eq_zero_iff (x : E) : x * x⋆ = 0 ↔ x = 0 := by
  simpa only [star_eq_zero, star_star] using @star_mul_self_eq_zero_iff _ _ _ _ (star x)

/--
theorem `mul_star_self_ne_zero_iff` / 定理 `mul_star_self_ne_zero_iff`

English:
theorem mul_star_self_ne_zero_iff
  given: (x : E)
  statement: x * x⋆ != 0 ↔ x != 0
  proof: by
  simp only [Ne, mul_star_self_eq_zero_iff]

中文:
定理 mul_star_self_ne_zero_iff
  条件: (x : E)
  结论: x * x⋆ != 0 ↔ x != 0
  证明: by
  simp only [Ne, mul_star_self_eq_zero_iff]

Depends on / 依赖: mul_star_self_eq_zero_iff
-/
theorem mul_star_self_ne_zero_iff (x : E) : x * x⋆ != 0 ↔ x != 0 := by
  simp only [Ne, mul_star_self_eq_zero_iff]

end NonUnital

section ProdPi

variable {ι R₁ R₂ : Type*} {R : ι -> Type*}
variable [NonUnitalNormedRing R₁] [StarRing R₁] [CStarRing R₁]
variable [NonUnitalNormedRing R₂] [StarRing R₂] [CStarRing R₂]
variable [forall i, NonUnitalNormedRing (R i)] [forall i, StarRing (R i)]

/--
Instance `_root_.Pi.starRing'` / 实例 `_root_.Pi.starRing'`

English:
instance _root_.Pi.starRing'
  signature: : StarRing (forall i, R i)
  body: inferInstance

中文:
实例 _root_.Pi.starRing'
  签名: : StarRing (对任意 i, R i)
  定义体: inferInstance
-/
instance _root_.Pi.starRing' : StarRing (forall i, R i) :=
  inferInstance

variable [Fintype ι] [forall i, CStarRing (R i)]

/--
Instance `_root_.Prod.cstarRing` / 实例 `_root_.Prod.cstarRing`

English:
instance _root_.Prod.cstarRing
  signature: : CStarRing (R₁ × R₂) where
  body: by
    dsimp only [norm]
    simp only [Prod.fst_mul, Prod.fst_star, Prod.snd_mul, Prod.snd_star, norm_star_mul_self, ← sq]
    rw [le_sup_iff]
    rcases le_total ‖x.fst‖ ‖x.snd‖ with (h | h) <;> simp [h]

中文:
实例 _root_.Prod.cstarRing
  签名: : CStarRing (R₁ × R₂) where
  定义体: by
    dsimp only [norm]
    simp only [Prod.fst_mul, Prod.fst_star, Prod.snd_mul, Prod.snd_star, norm_star_mul_self, ← sq]
    rw [le_sup_iff]
    rcases le_total ‖x.fst‖ ‖x.snd‖ with (h | h) <;> simp [h]

Depends on / 依赖: Prod.fst_mul, Prod.fst_star, Prod.snd_mul, Prod.snd_star, fst_mul, fst_star, le_sup_iff, le_total, norm_star_mul_self, snd_mul, snd_star, x.fst, x.snd
-/
instance _root_.Prod.cstarRing : CStarRing (R₁ × R₂) where
  norm_mul_self_le x := by
    dsimp only [norm]
    simp only [Prod.fst_mul, Prod.fst_star, Prod.snd_mul, Prod.snd_star, norm_star_mul_self, ← sq]
    rw [le_sup_iff]
    rcases le_total ‖x.fst‖ ‖x.snd‖ with (h | h) <;> simp [h]

/--
Instance `_root_.Pi.cstarRing` / 实例 `_root_.Pi.cstarRing`

English:
instance _root_.Pi.cstarRing
  signature: : CStarRing (forall i, R i) where
  body: by
    refine le_of_eq (Eq.symm ?_)
    simp only [norm, Pi.mul_apply, Pi.star_apply, nnnorm_star_mul_self, ← sq]
    norm_cast
    exact
      (Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x : NNReal => x ^ 2)
          (fun x y h => by simpa only [sq] using mul_le_mul' h h) (by simp)).symm

中文:
实例 _root_.Pi.cstarRing
  签名: : CStarRing (对任意 i, R i) where
  定义体: by
    refine le_of_eq (Eq.symm ?_)
    simp only [norm, Pi.mul_apply, Pi.star_apply, nnnorm_star_mul_self, ← sq]
    norm_cast
    exact
      (Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x : NNReal => x ^ 2)
          (fun x y h => by simpa only [sq] using mul_le_mul' h h) (by simp)).symm

Depends on / 依赖: Eq.symm, Finset, Finset.apply_sup_eq_sup_comp_of_linearOrder, NNReal, Pi.mul_apply, Pi.star_apply, apply_sup_eq_sup_comp_of_linearOrder, le_of_eq, mul_apply, mul_le_mul, nnnorm_star_mul_self, star_apply
-/
instance _root_.Pi.cstarRing : CStarRing (forall i, R i) where
  norm_mul_self_le x := by
    refine le_of_eq (Eq.symm ?_)
    simp only [norm, Pi.mul_apply, Pi.star_apply, nnnorm_star_mul_self, ← sq]
    norm_cast
    exact
      (Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x : NNReal => x ^ 2)
          (fun x y h => by simpa only [sq] using mul_le_mul' h h) (by simp)).symm

/--
Instance `_root_.Pi.cstarRing'` / 实例 `_root_.Pi.cstarRing'`

English:
instance _root_.Pi.cstarRing'
  signature: : CStarRing (ι -> R₁)
  body: Pi.cstarRing

中文:
实例 _root_.Pi.cstarRing'
  签名: : CStarRing (ι -> R₁)
  定义体: Pi.cstarRing

Depends on / 依赖: Pi.cstarRing, cstarRing
-/
instance _root_.Pi.cstarRing' : CStarRing (ι -> R₁) :=
  Pi.cstarRing

end ProdPi

namespace MulOpposite

instance {E : Type*} [NonUnitalNormedRing E] [StarRing E] [CStarRing E] : CStarRing Eᵐᵒᵖ where
.symm.le norm_mul_self_le x := CStarRing.norm_self_mul_star (x := MulOpposite.unop x)

end MulOpposite

section Unital


variable [NormedRing E] [StarRing E] [CStarRing E]

/--
theorem `norm_one` / 定理 `norm_one`

English:
theorem norm_one
  given: [Nontrivial E]
  statement: ‖(1 : E)‖ = 1
  proof: by
  have : 0 < ‖(1 : E)‖ := norm_pos_iff.mpr one_ne_zero
  rw [← mul_left_inj' this.ne']; rw [← norm_star_mul_self]; rw [mul_one]; rw [star_one]; rw [one_mul]

中文:
定理 norm_one
  条件: [Nontrivial E]
  结论: ‖(1 : E)‖ = 1
  证明: by
  have : 0 < ‖(1 : E)‖ := norm_pos_iff.mpr one_ne_zero
  rw [← mul_left_inj' this.ne']; rw [← norm_star_mul_self]; rw [mul_one]; rw [star_one]; rw [one_mul]

Depends on / 依赖: mul_left_inj, mul_one, norm_pos_iff, norm_pos_iff.mpr, norm_star_mul_self, one_mul, one_ne_zero, star_one, this.ne
-/
theorem norm_one [Nontrivial E] : ‖(1 : E)‖ = 1 := by
  have : 0 < ‖(1 : E)‖ := norm_pos_iff.mpr one_ne_zero
  rw [← mul_left_inj' this.ne']; rw [← norm_star_mul_self]; rw [mul_one]; rw [star_one]; rw [one_mul]

-- see Note [lower instance priority]
instance (priority := 100) [Nontrivial E] : NormOneClass E :=
  ⟨norm_one⟩

@[simp]
/--
theorem `norm_coe_unitary` / 定理 `norm_coe_unitary`

English:
theorem norm_coe_unitary
  given: [Nontrivial E] (U : unitary E)
  statement: ‖(U : E)‖ = 1
  proof: by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]; rw [one_pow 2]; rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [Unitary.coe_star_mul_self]; rw [CStarRing.norm_one]

中文:
定理 norm_coe_unitary
  条件: [Nontrivial E] (U : unitary E)
  结论: ‖(U : E)‖ = 1
  证明: by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]; rw [one_pow 2]; rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [Unitary.coe_star_mul_self]; rw [CStarRing.norm_one]

Depends on / 依赖: CStarRing, CStarRing.norm_one, CStarRing.norm_star_mul_self, Unitary, Unitary.coe_star_mul_self, coe_star_mul_self, norm_nonneg, norm_one, norm_star_mul_self, one_pow, zero_le_one
-/
theorem norm_coe_unitary [Nontrivial E] (U : unitary E) : ‖(U : E)‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]; rw [one_pow 2]; rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [Unitary.coe_star_mul_self]; rw [CStarRing.norm_one]

/--
theorem `norm_of_mem_unitary` / 定理 `norm_of_mem_unitary`

English:
theorem norm_of_mem_unitary
  given: [Nontrivial E] {U : E} (hU : U in unitary E)
  statement: ‖U‖ = 1
  proof: norm_coe_unitary ⟨U, hU⟩

@[simp]

中文:
定理 norm_of_mem_unitary
  条件: [Nontrivial E] {U : E} (hU : U in unitary E)
  结论: ‖U‖ = 1
  证明: norm_coe_unitary ⟨U, hU⟩

@[simp]

Depends on / 依赖: norm_coe_unitary
-/
theorem norm_of_mem_unitary [Nontrivial E] {U : E} (hU : U in unitary E) : ‖U‖ = 1 :=
  norm_coe_unitary ⟨U, hU⟩

@[simp]
/--
theorem `norm_coe_unitary_mul` / 定理 `norm_coe_unitary_mul`

English:
theorem norm_coe_unitary_mul
  given: (U : unitary E) (A : E)
  statement: ‖(U : E) * A‖ = ‖A‖
  proof: by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [sq, ← CStarRing.norm_star_mul_self, mul_assoc, ← mul_assoc (U : E)⋆]

@[simp]

中文:
定理 norm_coe_unitary_mul
  条件: (U : unitary E) (A : E)
  结论: ‖(U : E) * A‖ = ‖A‖
  证明: by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [sq, ← CStarRing.norm_star_mul_self, mul_assoc, ← mul_assoc (U : E)⋆]

@[simp]

Depends on / 依赖: CStarRing, CStarRing.norm_star_mul_self, mul_assoc, norm_nonneg, norm_star_mul_self
-/
theorem norm_coe_unitary_mul (U : unitary E) (A : E) : ‖(U : E) * A‖ = ‖A‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [sq, ← CStarRing.norm_star_mul_self, mul_assoc, ← mul_assoc (U : E)⋆]

@[simp]
/--
theorem `norm_unitary_smul` / 定理 `norm_unitary_smul`

English:
theorem norm_unitary_smul
  given: (U : unitary E) (A : E)
  statement: ‖U • A‖ = ‖A‖
  proof: norm_coe_unitary_mul U A

中文:
定理 norm_unitary_smul
  条件: (U : unitary E) (A : E)
  结论: ‖U • A‖ = ‖A‖
  证明: norm_coe_unitary_mul U A

Depends on / 依赖: norm_coe_unitary_mul
-/
theorem norm_unitary_smul (U : unitary E) (A : E) : ‖U • A‖ = ‖A‖ :=
  norm_coe_unitary_mul U A

/--
theorem `norm_mem_unitary_mul` / 定理 `norm_mem_unitary_mul`

English:
theorem norm_mem_unitary_mul
  given: {U : E} (A : E) (hU : U in unitary E)
  statement: ‖U * A‖ = ‖A‖
  proof: norm_coe_unitary_mul ⟨U, hU⟩ A

@[simp]

中文:
定理 norm_mem_unitary_mul
  条件: {U : E} (A : E) (hU : U in unitary E)
  结论: ‖U * A‖ = ‖A‖
  证明: norm_coe_unitary_mul ⟨U, hU⟩ A

@[simp]

Depends on / 依赖: norm_coe_unitary_mul
-/
theorem norm_mem_unitary_mul {U : E} (A : E) (hU : U in unitary E) : ‖U * A‖ = ‖A‖ :=
  norm_coe_unitary_mul ⟨U, hU⟩ A

@[simp]
/--
theorem `norm_mul_coe_unitary` / 定理 `norm_mul_coe_unitary`

English:
theorem norm_mul_coe_unitary
  given: (A : E) (U : unitary E)
  statement: ‖A * U‖ = ‖A‖
  proof: by
  simpa [← norm_star (A * U)] using norm_coe_unitary_mul (star U) (star A)

中文:
定理 norm_mul_coe_unitary
  条件: (A : E) (U : unitary E)
  结论: ‖A * U‖ = ‖A‖
  证明: by
  simpa [← norm_star (A * U)] using norm_coe_unitary_mul (star U) (star A)

Depends on / 依赖: norm_coe_unitary_mul, norm_star
-/
theorem norm_mul_coe_unitary (A : E) (U : unitary E) : ‖A * U‖ = ‖A‖ := by
  simpa [← norm_star (A * U)] using norm_coe_unitary_mul (star U) (star A)

/--
theorem `norm_mul_mem_unitary` / 定理 `norm_mul_mem_unitary`

English:
theorem norm_mul_mem_unitary
  given: (A : E) {U : E} (hU : U in unitary E)
  statement: ‖A * U‖ = ‖A‖
  proof: norm_mul_coe_unitary A ⟨U, hU⟩

中文:
定理 norm_mul_mem_unitary
  条件: (A : E) {U : E} (hU : U in unitary E)
  结论: ‖A * U‖ = ‖A‖
  证明: norm_mul_coe_unitary A ⟨U, hU⟩

Depends on / 依赖: norm_mul_coe_unitary
-/
theorem norm_mul_mem_unitary (A : E) {U : E} (hU : U in unitary E) : ‖A * U‖ = ‖A‖ :=
  norm_mul_coe_unitary A ⟨U, hU⟩

end Unital

end CStarRing

section SelfAdjoint

variable [NormedRing E] [StarRing E] [CStarRing E]

/--
theorem `IsSelfAdjoint.nnnorm_pow_two_pow` / 定理 `IsSelfAdjoint.nnnorm_pow_two_pow`

English:
theorem IsSelfAdjoint.nnnorm_pow_two_pow
  given: {x : E} (hx : IsSelfAdjoint x) (n : Nat)
  proof: by
  induction n with
  | zero => simp only [pow_zero, pow_one]
  | succ k hk =>
    rw [pow_succ']; rw [pow_mul']; rw [sq]; rw [(hx.pow (2 ^ k)).nnnorm_mul_self]; rw [hk]; rw [pow_mul']

中文:
定理 IsSelfAdjoint.nnnorm_pow_two_pow
  条件: {x : E} (hx : IsSelfAdjoint x) (n : 自然数)
  证明: by
  induction n with
  | zero => simp only [pow_zero, pow_one]
  | succ k hk =>
    rw [pow_succ']; rw [pow_mul']; rw [sq]; rw [(hx.pow (2 ^ k)).nnnorm_mul_self]; rw [hk]; rw [pow_mul']

Depends on / 依赖: hx.pow, nnnorm_mul_self, pow_mul, pow_one, pow_succ, pow_zero
-/
theorem IsSelfAdjoint.nnnorm_pow_two_pow {x : E} (hx : IsSelfAdjoint x) (n : Nat) :
    ‖x ^ 2 ^ n‖₊ = ‖x‖₊ ^ 2 ^ n := by
  induction n with
  | zero => simp only [pow_zero, pow_one]
  | succ k hk =>
    rw [pow_succ']; rw [pow_mul']; rw [sq]; rw [(hx.pow (2 ^ k)).nnnorm_mul_self]; rw [hk]; rw [pow_mul']

/--
theorem `IsSelfAdjoint.norm_pow_two_pow` / 定理 `IsSelfAdjoint.norm_pow_two_pow`

English:
theorem IsSelfAdjoint.norm_pow_two_pow
  given: {x : E} (hx : IsSelfAdjoint x) (n : Nat)
  proof: congr($(hx.nnnorm_pow_two_pow n))

中文:
定理 IsSelfAdjoint.norm_pow_two_pow
  条件: {x : E} (hx : IsSelfAdjoint x) (n : 自然数)
  证明: congr($(hx.nnnorm_pow_two_pow n))

Depends on / 依赖: hx.nnnorm_pow_two_pow, nnnorm_pow_two_pow
-/
theorem IsSelfAdjoint.norm_pow_two_pow {x : E} (hx : IsSelfAdjoint x) (n : Nat) :
    ‖x ^ 2 ^ n‖ = ‖x‖ ^ 2 ^ n :=
  congr($(hx.nnnorm_pow_two_pow n))

end SelfAdjoint

/--
theorem `IsStarProjection.norm_le` / 定理 `IsStarProjection.norm_le`

English:
theorem IsStarProjection.norm_le
  statement: [NonUnitalNormedRing E] [StarRing E] [CStarRing E]
  proof: by
  suffices ‖e‖ * (‖e‖ - 1) = 0 by grind [sub_eq_zero]
  simp [mul_sub, ← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]

中文:
定理 IsStarProjection.norm_le
  结论: [NonUnitalNormedRing E] [StarRing E] [CStarRing E]
  证明: by
  suffices ‖e‖ * (‖e‖ - 1) = 0 by grind [sub_eq_zero]
  simp [mul_sub, ← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]

Depends on / 依赖: CStarRing, CStarRing.norm_star_mul_self, he.isIdempotentElem.eq, he.isSelfAdjoint.star_eq, isIdempotentElem, isSelfAdjoint, mul_sub, norm_star_mul_self, star_eq, sub_eq_zero
-/
theorem IsStarProjection.norm_le [NonUnitalNormedRing E] [StarRing E] [CStarRing E]
    (e : E) (he : IsStarProjection e) : ‖e‖ <= 1 := by
  suffices ‖e‖ * (‖e‖ - 1) = 0 by grind [sub_eq_zero]
  simp [mul_sub, ← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]

section starₗᵢ

variable [CommSemiring 𝕜] [StarRing 𝕜]
variable [SeminormedAddCommGroup E] [StarAddMonoid E] [NormedStarGroup E]
variable [Module 𝕜 E] [StarModule 𝕜 E]

variable (𝕜) in
/--
Definition of `starₗᵢ` / `starₗᵢ` 的定义

English:
definition starₗᵢ
  signature: : E ≃ₗᵢ⋆[𝕜] E
  body: { starAddEquiv with
    map_smul' := star_smul
    norm_map' := norm_star }

@[simp]

中文:
定义 starₗᵢ
  签名: : E ≃ₗᵢ⋆[𝕜] E
  定义体: { starAddEquiv with
    map_smul' := star_smul
    norm_map' := norm_star }

@[simp]

Depends on / 依赖: map_smul, norm_map, norm_star, starAddEquiv, star_smul
-/
def starₗᵢ : E ≃ₗᵢ⋆[𝕜] E :=
  { starAddEquiv with
    map_smul' := star_smul
    norm_map' := norm_star }

@[simp]
/--
theorem `coe_starₗᵢ` / 定理 `coe_starₗᵢ`

English:
theorem coe_starₗᵢ
  statement: (starₗᵢ 𝕜 : E -> E) = star
  proof: rfl

中文:
定理 coe_starₗᵢ
  结论: (starₗᵢ 𝕜 : E -> E) = star
  证明: rfl
-/
theorem coe_starₗᵢ : (starₗᵢ 𝕜 : E -> E) = star :=
  rfl

/--
theorem `starₗᵢ_apply` / 定理 `starₗᵢ_apply`

English:
theorem starₗᵢ_apply
  given: {x : E}
  statement: starₗᵢ 𝕜 x = star x
  proof: rfl

@[simp]

中文:
定理 starₗᵢ_apply
  条件: {x : E}
  结论: starₗᵢ 𝕜 x = star x
  证明: rfl

@[simp]
-/
theorem starₗᵢ_apply {x : E} : starₗᵢ 𝕜 x = star x :=
  rfl

@[simp]
/--
theorem `symm_starₗᵢ` / 定理 `symm_starₗᵢ`

English:
theorem symm_starₗᵢ
  statement: (starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E).symm = starₗᵢ 𝕜
  proof: rfl

@[simp]

中文:
定理 symm_starₗᵢ
  结论: (starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E).symm = starₗᵢ 𝕜
  证明: rfl

@[simp]
-/
theorem symm_starₗᵢ : (starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E).symm = starₗᵢ 𝕜 :=
  rfl

@[simp]
/--
theorem `starₗᵢ_toContinuousLinearEquiv` / 定理 `starₗᵢ_toContinuousLinearEquiv`

English:
theorem starₗᵢ_toContinuousLinearEquiv
  proof: ContinuousLinearEquiv.ext rfl

@[simp]

中文:
定理 starₗᵢ_toContinuousLinearEquiv
  证明: ContinuousLinearEquiv.ext rfl

@[simp]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.ext
-/
theorem starₗᵢ_toContinuousLinearEquiv :
    (starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E).toContinuousLinearEquiv = (starL 𝕜 : E ≃L⋆[𝕜] E) :=
  ContinuousLinearEquiv.ext rfl

@[simp]
/--
theorem `toLinearEquiv_starₗᵢ` / 定理 `toLinearEquiv_starₗᵢ`

English:
theorem toLinearEquiv_starₗᵢ
  statement: (starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E).toLinearEquiv = starLinearEquiv 𝕜
  proof: rfl

中文:
定理 toLinearEquiv_starₗᵢ
  结论: (starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E).toLinearEquiv = starLinearEquiv 𝕜
  证明: rfl
-/
theorem toLinearEquiv_starₗᵢ : (starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E).toLinearEquiv = starLinearEquiv 𝕜 :=
  rfl

end starₗᵢ

namespace StarSubalgebra

example {𝕜 A : Type*} [NormedField 𝕜] [StarRing 𝕜] [SeminormedRing A] [StarRing A]
    [NormedAlgebra 𝕜 A] [StarModule 𝕜 A] (S : StarSubalgebra 𝕜 A) :
    NormedAlgebra 𝕜 S := by infer_instance

/--
Instance `to_cstarRing` / 实例 `to_cstarRing`

English:
instance to_cstarRing
  signature: {R A} [CommRing R] [StarRing R] [NormedRing A] [StarRing A] [CStarRing A]
  body: @CStarRing.norm_mul_self_le A _ _ _ x

中文:
实例 to_cstarRing
  签名: {R A} [CommRing R] [StarRing R] [NormedRing A] [StarRing A] [CStarRing A]
  定义体: @CStarRing.norm_mul_self_le A _ _ _ x

Depends on / 依赖: CStarRing, CStarRing.norm_mul_self_le, norm_mul_self_le
-/
instance to_cstarRing {R A} [CommRing R] [StarRing R] [NormedRing A] [StarRing A] [CStarRing A]
    [Algebra R A] [StarModule R A] (S : StarSubalgebra R A) : CStarRing S where
  norm_mul_self_le x := @CStarRing.norm_mul_self_le A _ _ _ x

end StarSubalgebra
