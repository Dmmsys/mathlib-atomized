/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Negation on spheres and balls

In this file we define `InvolutiveNeg` and `ContinuousNeg` instances for spheres, open balls, and
closed balls in a seminormed group.
-/

public section

open Metric Set Topology

variable {E : Type*} [i : SeminormedAddCommGroup E] {r : Real}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveNeg (sphere (0 : E) r)
  body: Subtype.map Neg.neg fun w => by simp
neg_neg x := Subtype.ext neg_neg x.1

@[simp]

中文:
实例 :
  签名: InvolutiveNeg (sphere (0 : E) r)
  定义体: Subtype.map Neg.neg fun w => by simp
neg_neg x := Subtype.ext neg_neg x.1

@[simp]

Depends on / 依赖: Neg.neg, Subtype, Subtype.map
-/
instance : InvolutiveNeg (sphere (0 : E) r) where
  neg := Subtype.map Neg.neg fun w => by simp
neg_neg x := Subtype.ext neg_neg x.1

@[simp]
/--
theorem `coe_neg_sphere` / 定理 `coe_neg_sphere`

English:
theorem coe_neg_sphere
  given: {r : Real} (v : sphere (0 : E) r)
  statement: ↑(-v) = (-v : E)
  proof: rfl

中文:
定理 coe_neg_sphere
  条件: {r : 实数} (v : sphere (0 : E) r)
  结论: ↑(-v) = (-v : E)
  证明: rfl
-/
theorem coe_neg_sphere {r : Real} (v : sphere (0 : E) r) : ↑(-v) = (-v : E) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousNeg (sphere (0 : E) r)
  body: IsInducing.subtypeVal.continuousNeg fun _ => rfl

中文:
实例 :
  签名: ContinuousNeg (sphere (0 : E) r)
  定义体: IsInducing.subtypeVal.continuousNeg fun _ => rfl

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.continuousNeg, continuousNeg, subtypeVal
-/
instance : ContinuousNeg (sphere (0 : E) r) := IsInducing.subtypeVal.continuousNeg fun _ => rfl

/-- We equip the ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : Real} : InvolutiveNeg (ball (0 : E) r) where
  neg := Subtype.map Neg.neg fun w => by simp
neg_neg x := Subtype.ext neg_neg x.1

/--
theorem `coe_neg_ball` / 定理 `coe_neg_ball`

English:
theorem coe_neg_ball
  given: {r : Real} (v : ball (0 : E) r)
  statement: ↑(-v) = (-v : E)
  proof: rfl

中文:
定理 coe_neg_ball
  条件: {r : 实数} (v : ball (0 : E) r)
  结论: ↑(-v) = (-v : E)
  证明: rfl
-/
@[simp] theorem coe_neg_ball {r : Real} (v : ball (0 : E) r) : ↑(-v) = (-v : E) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousNeg (ball (0 : E) r)
  body: IsInducing.subtypeVal.continuousNeg fun _ => rfl

中文:
实例 :
  签名: ContinuousNeg (ball (0 : E) r)
  定义体: IsInducing.subtypeVal.continuousNeg fun _ => rfl

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.continuousNeg, continuousNeg, subtypeVal
-/
instance : ContinuousNeg (ball (0 : E) r) := IsInducing.subtypeVal.continuousNeg fun _ => rfl

/-- We equip the closed ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : Real} : InvolutiveNeg (closedBall (0 : E) r) where
  neg := Subtype.map Neg.neg fun w => by simp
neg_neg x := Subtype.ext neg_neg x.1

/--
theorem `coe_neg_closedBall` / 定理 `coe_neg_closedBall`

English:
theorem coe_neg_closedBall
  given: {r : Real} (v : closedBall (0 : E) r)
  statement: ↑(-v) = (-v : E)
  proof: rfl

中文:
定理 coe_neg_closedBall
  条件: {r : 实数} (v : closedBall (0 : E) r)
  结论: ↑(-v) = (-v : E)
  证明: rfl
-/
@[simp] theorem coe_neg_closedBall {r : Real} (v : closedBall (0 : E) r) : ↑(-v) = (-v : E) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousNeg (closedBall (0 : E) r)
  body: IsInducing.subtypeVal.continuousNeg fun _ => rfl

中文:
实例 :
  签名: ContinuousNeg (closedBall (0 : E) r)
  定义体: IsInducing.subtypeVal.continuousNeg fun _ => rfl

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.continuousNeg, continuousNeg, subtypeVal
-/
instance : ContinuousNeg (closedBall (0 : E) r) := IsInducing.subtypeVal.continuousNeg fun _ => rfl
