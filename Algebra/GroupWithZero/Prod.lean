/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Products of monoids with zero, groups with zero

In this file we define `MonoidWithZero`, `GroupWithZero`, etc... instances for `M₀ × N₀`.

## Main declarations

* `mulMonoidWithZeroHom`: Multiplication bundled as a monoid with zero homomorphism.
* `divMonoidWithZeroHom`: Division bundled as a monoid with zero homomorphism.
-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

variable {M₀ N₀ : Type*}

namespace Prod

/--
Instance `instMulZeroClass` / 实例 `instMulZeroClass`

English:
instance instMulZeroClass
  signature: [MulZeroClass M₀] [MulZeroClass N₀]
  body: by simp [Prod.mul_def]
  mul_zero := by simp [Prod.mul_def]

中文:
实例 instMulZeroClass
  签名: [乘零类 M₀] [乘零类 N₀]
  定义体: by simp [Prod.mul_def]
  mul_zero := by simp [Prod.mul_def]

Depends on / 依赖: Prod.mul_def, mul_def, mul_zero
-/
instance instMulZeroClass [MulZeroClass M₀] [MulZeroClass N₀] : MulZeroClass (M₀ × N₀) where
  zero_mul := by simp [Prod.mul_def]
  mul_zero := by simp [Prod.mul_def]

/--
Instance `instSemigroupWithZero` / 实例 `instSemigroupWithZero`

English:
instance instSemigroupWithZero
  signature: [SemigroupWithZero M₀] [SemigroupWithZero N₀]
  body: by simp
  mul_zero := by simp

中文:
实例 instSemigroupWithZero
  签名: [带零半群 M₀] [带零半群 N₀]
  定义体: by simp
  mul_zero := by simp

Depends on / 依赖: mul_zero
-/
instance instSemigroupWithZero [SemigroupWithZero M₀] [SemigroupWithZero N₀] :
    SemigroupWithZero (M₀ × N₀) where
  zero_mul := by simp
  mul_zero := by simp

/--
Instance `instMulZeroOneClass` / 实例 `instMulZeroOneClass`

English:
instance instMulZeroOneClass
  signature: [MulZeroOneClass M₀] [MulZeroOneClass N₀]
  body: by simp
  mul_zero := by simp

中文:
实例 instMulZeroOneClass
  签名: [乘零幺类 M₀] [乘零幺类 N₀]
  定义体: by simp
  mul_zero := by simp

Depends on / 依赖: mul_zero
-/
instance instMulZeroOneClass [MulZeroOneClass M₀] [MulZeroOneClass N₀] :
    MulZeroOneClass (M₀ × N₀) where
  zero_mul := by simp
  mul_zero := by simp

/--
Instance `instMonoidWithZero` / 实例 `instMonoidWithZero`

English:
instance instMonoidWithZero
  signature: [MonoidWithZero M₀] [MonoidWithZero N₀]
  body: by simp
  mul_zero := by simp

中文:
实例 instMonoidWithZero
  签名: [带零幺半群 M₀] [带零幺半群 N₀]
  定义体: by simp
  mul_zero := by simp

Depends on / 依赖: mul_zero
-/
instance instMonoidWithZero [MonoidWithZero M₀] [MonoidWithZero N₀] : MonoidWithZero (M₀ × N₀) where
  zero_mul := by simp
  mul_zero := by simp

/--
Instance `instCommMonoidWithZero` / 实例 `instCommMonoidWithZero`

English:
instance instCommMonoidWithZero
  signature: [CommMonoidWithZero M₀] [CommMonoidWithZero N₀]
  body: by simp
  mul_zero := by simp

中文:
实例 instCommMonoidWithZero
  签名: [带零交换幺半群 M₀] [带零交换幺半群 N₀]
  定义体: by simp
  mul_zero := by simp

Depends on / 依赖: mul_zero
-/
instance instCommMonoidWithZero [CommMonoidWithZero M₀] [CommMonoidWithZero N₀] :
    CommMonoidWithZero (M₀ × N₀) where
  zero_mul := by simp
  mul_zero := by simp

end Prod

variable (M₀) in
@[simp]
/--
lemma `WithZero.ofClass_withZeroUnitsEquiv` / 引理 `WithZero.ofClass_withZeroUnitsEquiv`

English:
lemma WithZero.ofClass_withZeroUnitsEquiv
  statement: [GroupWithZero M₀]
  proof: rfl

中文:
引理 WithZero.ofClass_withZeroUnitsEquiv
  结论: [带零群 M₀]
  证明: rfl
-/
lemma WithZero.ofClass_withZeroUnitsEquiv [GroupWithZero M₀]
    [DecidablePred fun x : M₀ => x = 0] :
    .ofClass WithZero.withZeroUnitsEquiv =
      WithZero.lift' (Units.coeHom M₀) :=
  rfl

/-! ### Multiplication and division as homomorphisms -/

section BundledMulDiv

/-- Multiplication as a multiplicative homomorphism with zero. -/
@[simps]
/--
Definition of `mulMonoidWithZeroHom` / `mulMonoidWithZeroHom` 的定义

English:
definition mulMonoidWithZeroHom
  signature: [CommMonoidWithZero M₀]
  body: mulMonoidHom
  map_zero' := mul_zero _

中文:
定义 mulMonoidWithZeroHom
  签名: [带零交换幺半群 M₀]
  定义体: mulMonoidHom
  map_zero' := mul_zero _

Depends on / 依赖: mulMonoidHom
-/
def mulMonoidWithZeroHom [CommMonoidWithZero M₀] : M₀ × M₀ ->*₀ M₀ where
  __ := mulMonoidHom
  map_zero' := mul_zero _

/-- Division as a multiplicative homomorphism with zero. -/
@[simps]
/--
Definition of `divMonoidWithZeroHom` / `divMonoidWithZeroHom` 的定义

English:
definition divMonoidWithZeroHom
  signature: [CommGroupWithZero M₀]
  body: divMonoidHom
  map_zero' := zero_div _

中文:
定义 divMonoidWithZeroHom
  签名: [带零交换群 M₀]
  定义体: divMonoidHom
  map_zero' := zero_div _

Depends on / 依赖: divMonoidHom
-/
def divMonoidWithZeroHom [CommGroupWithZero M₀] : M₀ × M₀ ->*₀ M₀ where
  __ := divMonoidHom
  map_zero' := zero_div _

end BundledMulDiv
