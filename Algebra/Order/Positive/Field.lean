/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Positive.Ring

/-!
# Algebraic structures on the set of positive numbers

In this file we prove that the set of positive elements of a linear ordered field is a linear
ordered commutative group.
-/

public section


variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace Positive

/--
Instance `Subtype.inv` / 实例 `Subtype.inv`

English:
instance Subtype.inv
  signature: : Inv { x : K // 0 < x }
  body: ⟨fun x => ⟨x⁻¹, inv_pos.2 x.2⟩⟩

@[simp]

中文:
实例 子类型.inv
  签名: : 取逆 { x : K // 0 < x }
  定义体: ⟨fun x => ⟨x⁻¹, inv_pos.2 x.2⟩⟩

@[simp]

Depends on / 依赖: inv_pos
-/
instance Subtype.inv : Inv { x : K // 0 < x } := ⟨fun x => ⟨x⁻¹, inv_pos.2 x.2⟩⟩

@[simp]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (x : { x : K // 0 < x })
  statement: ↑x⁻¹ = (x⁻¹ : K)
  proof: rfl

中文:
定理 coe_inv
  条件: (x : { x : K // 0 < x })
  结论: ↑x⁻¹ = (x⁻¹ : K)
  证明: rfl
-/
theorem coe_inv (x : { x : K // 0 < x }) : ↑x⁻¹ = (x⁻¹ : K) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow { x : K // 0 < x } Int
  body: ⟨fun x n => ⟨(x : K) ^ n, zpow_pos x.2 _⟩⟩

@[simp]

中文:
实例 :
  签名: 幂 { x : K // 0 < x } 整数
  定义体: ⟨fun x n => ⟨(x : K) ^ n, zpow_pos x.2 _⟩⟩

@[simp]

Depends on / 依赖: zpow_pos
-/
instance : Pow { x : K // 0 < x } Int :=
  ⟨fun x n => ⟨(x : K) ^ n, zpow_pos x.2 _⟩⟩

@[simp]
/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: (x : { x : K // 0 < x }) (n : Int)
  statement: ↑(x ^ n) = (x : K) ^ n
  proof: rfl

中文:
定理 coe_zpow
  条件: (x : { x : K // 0 < x }) (n : 整数)
  结论: ↑(x ^ n) = (x : K) ^ n
  证明: rfl
-/
theorem coe_zpow (x : { x : K // 0 < x }) (n : Int) : ↑(x ^ n) = (x : K) ^ n :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommGroup { x : K // 0 < x }
  body: Subtype.ext inv_mul_cancel₀ a.2.ne'
zpow_zero' x := Subtype.ext zpow_zero _
zpow_succ' n x := Subtype.ext DivInvMonoid.zpow_succ' _ _
zpow_neg' n x := Subtype.ext DivInvMonoid.zpow_neg' _ _

中文:
实例 :
  签名: 交换群 { x : K // 0 < x }
  定义体: Subtype.ext inv_mul_cancel₀ a.2.ne'
zpow_zero' x := Subtype.ext zpow_zero _
zpow_succ' n x := Subtype.ext DivInvMonoid.zpow_succ' _ _
zpow_neg' n x := Subtype.ext DivInvMonoid.zpow_neg' _ _

Depends on / 依赖: Subtype, Subtype.ext
-/
instance : CommGroup { x : K // 0 < x } where
inv_mul_cancel a := Subtype.ext inv_mul_cancel₀ a.2.ne'
zpow_zero' x := Subtype.ext zpow_zero _
zpow_succ' n x := Subtype.ext DivInvMonoid.zpow_succ' _ _
zpow_neg' n x := Subtype.ext DivInvMonoid.zpow_neg' _ _

end Positive
