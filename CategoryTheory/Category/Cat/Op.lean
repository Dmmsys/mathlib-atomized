/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Opposites

/-!
# The dualizing functor on `Cat`

We define a (strict) functor `opFunctor` and an equivalence assigning opposite categories to
categories. We then show that this functor is strictly involutive and that it induces an
equivalence on `Cat`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Cat

/-- The endofunctor `Cat ⥤ Cat` assigning to each category its opposite category. -/
@[simps]
/-
**CategoryTheory.Cat.opFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：opFunctor : Cat.{v₁, u₁} ⥤ Cat.{v₁, u₁} where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The endofunctor `Cat ⥤ Cat` assigning to each category its opposite category.
-/
def opFunctor : Cat.{v₁, u₁} ⥤ Cat.{v₁, u₁} where
  obj C := .of Cᵒᵖ
  map F := F.toFunctor.op.toCatHom

/-- The natural isomorphism between the double application of `Cat.opFunctor` and the
identity functor on `Cat`. -/
@[simps!]
/-
**CategoryTheory.Cat.opFunctorInvolutive** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Cat`。
形式化陈述：opFunctorInvolutive : opFunctor.{v₁, u₁} ⋙ opFunctor.{v₁, u₁} ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between the double application of `Cat.opFunctor` and th
e
identity functor on `Cat`.
-/
def opFunctorInvolutive : opFunctor.{v₁, u₁} ⋙ opFunctor.{v₁, u₁} ≅ 𝟭 _ :=
  NatIso.ofComponents (fun C => .mk (unopUnop C).toCatHom (opOp C).toCatHom)

/-- The equivalence `Cat ≌ Cat` associating each category with its opposite category. -/
@[simps]
/-
**CategoryTheory.Cat.opEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat
`。
形式化陈述：opEquivalence : Cat.{v₁, u₁} ≌ Cat.{v₁, u₁} where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `Cat ≌ Cat` associating each category with its opposite category
.
-/
def opEquivalence : Cat.{v₁, u₁} ≌ Cat.{v₁, u₁} where
  functor := opFunctor
  inverse := opFunctor
  unitIso := NatIso.ofComponents (fun _ => Iso.mk (opOp _).toCatHom (unopUnop _).toCatHom)
  counitIso := NatIso.ofComponents (fun _ => Iso.mk (unopUnop _).toCatHom (opOp _).toCatHom)

end Cat

end CategoryTheory

