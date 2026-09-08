/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.InjSurj

/-!
# `ULift` instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `MulEquiv.ulift : ULift R ≃* R` (and its additive analogue).
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

universe u v w

variable {α : Type u} {β : Type v} {x y : ULift.{w} α}

namespace ULift

@[to_additive]
/-
**ULift.one** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：one [One α] : One (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance one [One α] : One (ULift α) :=
  ⟨⟨1⟩⟩

@[to_additive (attr := simp)]
/-
**ULift.one_down** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：one_down [One α] : (1 : ULift α).down = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_down [One α] : (1 : ULift α).down = 1 :=
  rfl

@[to_additive]
/-
**ULift.mul** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：mul [Mul α] : Mul (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mul [Mul α] : Mul (ULift α) :=
  ⟨fun f g => ⟨f.down * g.down⟩⟩

@[to_additive (attr := simp)]
/-
**ULift.mul_down** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：mul_down [Mul α] : (x * y).down = x.down * y.down
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_down [Mul α] : (x * y).down = x.down * y.down :=
  rfl

@[to_additive]
/-
**ULift.div** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：div [Div α] : Div (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance div [Div α] : Div (ULift α) :=
  ⟨fun f g => ⟨f.down / g.down⟩⟩

@[to_additive (attr := simp)]
/-
**ULift.div_down** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：div_down [Div α] : (x / y).down = x.down / y.down
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem div_down [Div α] : (x / y).down = x.down / y.down :=
  rfl

@[to_additive]
/-
**ULift.inv** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：inv [Inv α] : Inv (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inv [Inv α] : Inv (ULift α) :=
  ⟨fun f => ⟨f.down⁻¹⟩⟩

@[to_additive (attr := simp)]
/-
**ULift.inv_down** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：inv_down [Inv α] : x⁻¹.down = x.down⁻¹
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_down [Inv α] : x⁻¹.down = x.down⁻¹ :=
  rfl

@[to_additive (attr := to_additive) smul]
/-
**ULift.pow** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：pow [Pow α β] : Pow (ULift α) β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pow [Pow α β] : Pow (ULift α) β :=
  ⟨fun x n => up (x.down ^ n)⟩

@[to_additive (attr := to_additive, simp) smul_down]
/-
**ULift.pow_down** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：pow_down [Pow α β] (a : ULift.{w} α) (b : β) : (a ^ b).down = a.down ^ b
参数：a : ULift.{w} α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_down [Pow α β] (a : ULift.{w} α) (b : β) : (a ^ b).down = a.down ^ b :=
  rfl

/-- The multiplicative equivalence between `ULift α` and `α`.
-/
@[to_additive /-- The additive equivalence between `ULift α` and `α`. -/]
/-
**ULift._root_.MulEquiv.ulift** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative equivalence between `ULift α` and `α`.
-/
def _root_.MulEquiv.ulift [Mul α] : ULift α ≃* α :=
  { Equiv.ulift with map_mul' := fun _ _ => rfl }

@[to_additive]
/-
**ULift.semigroup** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：semigroup [Semigroup α] : Semigroup (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semigroup [Semigroup α] : Semigroup (ULift α) :=
  (MulEquiv.ulift.injective.semigroup _) fun _ _ => rfl

@[to_additive]
/-
**ULift.commSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：commSemigroup [CommSemigroup α] : CommSemigroup (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commSemigroup [CommSemigroup α] : CommSemigroup (ULift α) :=
  (Equiv.ulift.injective.commSemigroup _) fun _ _ => rfl

@[to_additive]
/-
**ULift.mulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：mulOneClass [MulOneClass α] : MulOneClass (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulOneClass [MulOneClass α] : MulOneClass (ULift α) :=
  Equiv.ulift.injective.mulOneClass _ rfl (by intros; rfl)

@[to_additive]
/-
**ULift.monoid** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：monoid [Monoid α] : Monoid (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoid [Monoid α] : Monoid (ULift α) :=
  Equiv.ulift.injective.monoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/-
**ULift.commMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：commMonoid [CommMonoid α] : CommMonoid (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMonoid [CommMonoid α] : CommMonoid (ULift α) :=
  Equiv.ulift.injective.commMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/-
**ULift.divInvMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：divInvMonoid [DivInvMonoid α] : DivInvMonoid (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance divInvMonoid [DivInvMonoid α] : DivInvMonoid (ULift α) :=
  Equiv.ulift.injective.divInvMonoid _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/-
**ULift.group** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：group [Group α] : Group (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance group [Group α] : Group (ULift α) :=
  Equiv.ulift.injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/-
**ULift.commGroup** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：commGroup [CommGroup α] : CommGroup (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commGroup [CommGroup α] : CommGroup (ULift α) :=
  Equiv.ulift.injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/-
**ULift.leftCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：leftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup (ULift α
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance leftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup (ULift α) :=
  Equiv.ulift.injective.leftCancelSemigroup _ fun _ _ => rfl

@[to_additive]
/-
**ULift.rightCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：rightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup (ULif
t α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup (ULift α) :=
  Equiv.ulift.injective.rightCancelSemigroup _ fun _ _ => rfl

@[to_additive]
/-
**ULift.leftCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：leftCancelMonoid [LeftCancelMonoid α] : LeftCancelMonoid (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance leftCancelMonoid [LeftCancelMonoid α] : LeftCancelMonoid (ULift α) :=
  Equiv.ulift.injective.leftCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/-
**ULift.rightCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：rightCancelMonoid [RightCancelMonoid α] : RightCancelMonoid (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rightCancelMonoid [RightCancelMonoid α] : RightCancelMonoid (ULift α) :=
  Equiv.ulift.injective.rightCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/-
**ULift.cancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：cancelMonoid [CancelMonoid α] : CancelMonoid (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance cancelMonoid [CancelMonoid α] : CancelMonoid (ULift α) :=
  Equiv.ulift.injective.cancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/-
**ULift.cancelCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：cancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance cancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid (ULift α) :=
  Equiv.ulift.injective.cancelCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
/-
**ULift.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：nontrivial [Nontrivial α] : Nontrivial (ULift α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
instance nontrivial [Nontrivial α] : Nontrivial (ULift α) :=
  Equiv.ulift.symm.injective.nontrivial

-- TODO: We don't do `IsOrderedCancelMonoid`.
-- We'd need to add instances for `ULift` in `Order.Basic`.
end ULift

