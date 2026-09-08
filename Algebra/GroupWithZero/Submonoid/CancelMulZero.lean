/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.Group.Submonoid.Defs

/-!
# Submagmas with zero inherit cancellations
-/

public section

namespace MulZeroMemClass

variable {M₀ : Type*} [Mul M₀] [Zero M₀] {S : Type*} [SetLike S M₀] [MulMemClass S M₀]
  [ZeroMemClass S M₀] (s : S)

/-- A submagma with zero of a left cancellative magma with zero inherits left cancellation. -/
/-
**MulZeroMemClass.isLeftCancelMulZero** 是 Mathlib 中的一个实例，位于命名空间 `MulZeroMemClass
`。
形式化陈述：isLeftCancelMulZero [IsLeftCancelMulZero M₀] : IsLeftCancelMulZero s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isLeftCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u_
3} [inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (
f : M₀ → M₀'),   Function.In…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))

--- 原说明 ---
A submagma with zero of a left cancellative magma with zero inherits left cancel
lation.
-/
instance isLeftCancelMulZero [IsLeftCancelMulZero M₀] : IsLeftCancelMulZero s :=
  Subtype.coe_injective.isLeftCancelMulZero Subtype.val rfl fun _ _ => rfl

/-- A submagma with zero of a right cancellative magma with zero inherits right cancellation. -/
/-
**MulZeroMemClass.isRightCancelMulZero** 是 Mathlib 中的一个实例，位于命名空间 `MulZeroMemClas
s`。
形式化陈述：isRightCancelMulZero [IsRightCancelMulZero M₀] : IsRightCancelMulZero s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isRightCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u
_3} [inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   
(f : M₀ → M₀'),   Function.In…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))

--- 原说明 ---
A submagma with zero of a right cancellative magma with zero inherits right canc
ellation.
-/
instance isRightCancelMulZero [IsRightCancelMulZero M₀] : IsRightCancelMulZero s :=
  Subtype.coe_injective.isRightCancelMulZero Subtype.val rfl fun _ _ => rfl

/-- A submagma with zero of a cancellative magma with zero inherits cancellation. -/
/-
**MulZeroMemClass.isCancelMulZero** 是 Mathlib 中的一个定理，位于命名空间 `MulZeroMemClass`。
形式化陈述：∀ {M₀ : Type u_1} [inst : Mul M₀] [inst_1 : Zero M₀] {S : Type u_2} [inst_
2 : SetLike S M₀] [inst_3 : MulMemClass S M₀]   [inst_4 : ZeroMemClass S M₀] (s 
: S) [IsCancelMulZero M₀], IsCancelMulZero ↥s
参数：s : S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀

--- 原说明 ---
A submagma with zero of a cancellative magma with zero inherits cancellation.
-/
instance isCancelMulZero [IsCancelMulZero M₀] : IsCancelMulZero s where

end MulZeroMemClass

