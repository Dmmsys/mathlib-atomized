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

variable {E : Type*} [i : SeminormedAddCommGroup E] {r : ℝ}

/-- We equip the sphere, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We equip the sphere, in a seminormed group, with a formal operation of negation,
 namely the
antipodal map.
-/
instance : InvolutiveNeg (sphere (0 : E) r) where
  neg := Subtype.map Neg.neg fun w => by simp
  neg_neg x := Subtype.ext <| neg_neg x.1

@[simp]
/-
**coe_neg_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_neg_sphere {r : Real} (v : sphere (0 : E) r) : ↑(-v) = (-v : E)
参数：v : sphere (0 : E) r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg_sphere {r : ℝ} (v : sphere (0 : E) r) : ↑(-v) = (-v : E) :=
  rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousNeg (sphere (0 : E) r) := IsInducing.subtypeVal.continuousNeg fun _ => rfl

/-- We equip the ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We equip the ball, in a seminormed group, with a formal operation of negation, n
amely the
antipodal map.
-/
instance {r : ℝ} : InvolutiveNeg (ball (0 : E) r) where
  neg := Subtype.map Neg.neg fun w => by simp
  neg_neg x := Subtype.ext <| neg_neg x.1
/-
**coe_neg_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} [i : SeminormedAddCommGroup E] {r : ℝ} (v : ↑(Metric.ball
 0 r)), ↑(-v) = -↑v
参数：v : ↑(Metric.ball 0 r)；-v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_neg_ball {r : ℝ} (v : ball (0 : E) r) : ↑(-v) = (-v : E) := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousNeg (ball (0 : E) r) := IsInducing.subtypeVal.continuousNeg fun _ => rfl

/-- We equip the closed ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We equip the closed ball, in a seminormed group, with a formal operation of nega
tion, namely the
antipodal map.
-/
instance {r : ℝ} : InvolutiveNeg (closedBall (0 : E) r) where
  neg := Subtype.map Neg.neg fun w => by simp
  neg_neg x := Subtype.ext <| neg_neg x.1
/-
**coe_neg_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} [i : SeminormedAddCommGroup E] {r : ℝ} (v : ↑(Metric.clos
edBall 0 r)), ↑(-v) = -↑v
参数：v : ↑(Metric.closedBall 0 r)；-v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_neg_closedBall {r : ℝ} (v : closedBall (0 : E) r) : ↑(-v) = (-v : E) := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousNeg (closedBall (0 : E) r) := IsInducing.subtypeVal.continuousNeg fun _ => rfl
