/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Multiplication by a nonzero element in a `GroupWithZero` is a permutation.
-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

variable {G₀ : Type*}

namespace Equiv
section GroupWithZero
variable [GroupWithZero G₀]

/--
Definition of `_root_.unitsEquivNeZero` / `_root_.unitsEquivNeZero` 的定义

English:
definition _root_.unitsEquivNeZero
  signature: : G₀ˣ ≃ {a : G₀ // a != 0} where
  body: ⟨a, a.ne_zero⟩
  invFun a := Units.mk0 _ a.prop

中文:
定义 _root_.unitsEquivNeZero
  签名: : G₀ˣ ≃ {a : G₀ // a != 0} where
  定义体: ⟨a, a.ne_zero⟩
  invFun a := Units.mk0 _ a.prop
-/
@[simps] def _root_.unitsEquivNeZero : G₀ˣ ≃ {a : G₀ // a != 0} where
  toFun a := ⟨a, a.ne_zero⟩
  invFun a := Units.mk0 _ a.prop

/-- Left multiplication by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! -fullyApplied]
/--
Definition of `mulLeft₀` / `mulLeft₀` 的定义

English:
definition mulLeft₀
  signature: (a : G₀) (ha : a != 0)
  body: (Units.mk0 a ha).mulLeft

中文:
定义 mulLeft₀
  签名: (a : G₀) (ha : a != 0)
  定义体: (Units.mk0 a ha).mulLeft
-/
protected def mulLeft₀ (a : G₀) (ha : a != 0) : Perm G₀ :=
  (Units.mk0 a ha).mulLeft

/--
theorem `_root_.mulLeft_bijective₀` / 定理 `_root_.mulLeft_bijective₀`

English:
theorem _root_.mulLeft_bijective₀
  given: (a : G₀) (ha : a != 0)
  statement: Function.Bijective (a * · : G₀ -> G₀)
  proof: (Equiv.mulLeft₀ a ha).bijective

中文:
定理 _root_.mulLeft_bijective₀
  条件: (a : G₀) (ha : a != 0)
  结论: Function.Bijective (a * · : G₀ -> G₀)
  证明: (Equiv.mulLeft₀ a ha).bijective

Depends on / 依赖: Equiv.mulLeft, bijective
-/
theorem _root_.mulLeft_bijective₀ (a : G₀) (ha : a != 0) : Function.Bijective (a * · : G₀ -> G₀) :=
  (Equiv.mulLeft₀ a ha).bijective

/-- Right multiplication by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! -fullyApplied]
/--
Definition of `mulRight₀` / `mulRight₀` 的定义

English:
definition mulRight₀
  signature: (a : G₀) (ha : a != 0)
  body: (Units.mk0 a ha).mulRight

中文:
定义 mulRight₀
  签名: (a : G₀) (ha : a != 0)
  定义体: (Units.mk0 a ha).mulRight
-/
protected def mulRight₀ (a : G₀) (ha : a != 0) : Perm G₀ :=
  (Units.mk0 a ha).mulRight

/--
theorem `_root_.mulRight_bijective₀` / 定理 `_root_.mulRight_bijective₀`

English:
theorem _root_.mulRight_bijective₀
  given: (a : G₀) (ha : a != 0)
  statement: Function.Bijective ((· * a) : G₀ -> G₀)
  proof: (Equiv.mulRight₀ a ha).bijective

中文:
定理 _root_.mulRight_bijective₀
  条件: (a : G₀) (ha : a != 0)
  结论: Function.Bijective ((· * a) : G₀ -> G₀)
  证明: (Equiv.mulRight₀ a ha).bijective

Depends on / 依赖: Equiv.mulRight, bijective
-/
theorem _root_.mulRight_bijective₀ (a : G₀) (ha : a != 0) : Function.Bijective ((· * a) : G₀ -> G₀) :=
  (Equiv.mulRight₀ a ha).bijective

/-- Right division by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! +simpRhs]
/--
Definition of `divRight₀` / `divRight₀` 的定义

English:
definition divRight₀
  signature: (a : G₀) (ha : a != 0)
  body: (· / a)
  invFun := (· * a)
  left_inv _ := by simp [ha]
  right_inv _ := by simp [ha]

中文:
定义 divRight₀
  签名: (a : G₀) (ha : a != 0)
  定义体: (· / a)
  invFun := (· * a)
  left_inv _ := by simp [ha]
  right_inv _ := by simp [ha]
-/
def divRight₀ (a : G₀) (ha : a != 0) : Perm G₀ where
  toFun := (· / a)
  invFun := (· * a)
  left_inv _ := by simp [ha]
  right_inv _ := by simp [ha]

end GroupWithZero

section CommGroupWithZero
variable [CommGroupWithZero G₀]

/-- Left division by a nonzero element in a `CommGroupWithZero` is a permutation of the underlying
type. -/
@[simps! +simpRhs]
/--
Definition of `divLeft₀` / `divLeft₀` 的定义

English:
definition divLeft₀
  signature: (a : G₀) (ha : a != 0)
  body: (a / ·)
  invFun := (a / ·)
  left_inv _ := by simp [ha]
  right_inv _ := by simp [ha]

中文:
定义 divLeft₀
  签名: (a : G₀) (ha : a != 0)
  定义体: (a / ·)
  invFun := (a / ·)
  left_inv _ := by simp [ha]
  right_inv _ := by simp [ha]
-/
def divLeft₀ (a : G₀) (ha : a != 0) : Perm G₀ where
  toFun := (a / ·)
  invFun := (a / ·)
  left_inv _ := by simp [ha]
  right_inv _ := by simp [ha]

end CommGroupWithZero
end Equiv
