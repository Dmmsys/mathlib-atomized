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

/-
**Positive.Subtype.inv** 是 Mathlib 中的一个定义，位于命名空间 `Positive.Subtype`。
形式化陈述：{K : Type u_1} → [inst : Field K] → [inst_1 : LinearOrder K] → [IsStrictOr
deredRing K] → Inv { x // 0 < x }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.inv : Inv { x : K // 0 < x } := ⟨fun x => ⟨x⁻¹, inv_pos.2 x.2⟩⟩

@[simp]
/-
**Positive.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Positive`。
形式化陈述：coe_inv (x : { x : K // 0 < x }) : ↑x⁻¹ = (x⁻¹ : K)
参数：x : { x : K // 0 < x }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv (x : { x : K // 0 < x }) : ↑x⁻¹ = (x⁻¹ : K) :=
  rfl
/-
**Positive.** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow { x : K // 0 < x } ℤ :=
  ⟨fun x n => ⟨(x : K) ^ n, zpow_pos x.2 _⟩⟩

@[simp]
/-
**Positive.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Positive`。
形式化陈述：coe_zpow (x : { x : K // 0 < x }) (n : Int) : ↑(x ^ n) = (x : K) ^ n
参数：x : { x : K // 0 < x }；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zpow (x : { x : K // 0 < x }) (n : ℤ) : ↑(x ^ n) = (x : K) ^ n :=
  rfl
/-
**Positive.** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommGroup { x : K // 0 < x } where
  inv_mul_cancel a := Subtype.ext <| inv_mul_cancel₀ a.2.ne'
  zpow_zero' x := Subtype.ext <| zpow_zero _
  zpow_succ' n x := Subtype.ext <| DivInvMonoid.zpow_succ' _ _
  zpow_neg' n x := Subtype.ext <| DivInvMonoid.zpow_neg' _ _

end Positive

