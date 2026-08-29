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
/--
Definition of `opFunctor` / `opFunctor` 的定义

English:
definition opFunctor
  signature: : Cat.{v₁, u₁} ⥤ Cat.{v₁, u₁} where
  body: .of Cᵒᵖ
  map F := F.toFunctor.op.toCatHom

中文:
定义 opFunctor
  签名: : Cat.{v₁, u₁} ⥤ Cat.{v₁, u₁} where
  定义体: .of Cᵒᵖ
  map F := F.toFunctor.op.toCatHom
-/
def opFunctor : Cat.{v₁, u₁} ⥤ Cat.{v₁, u₁} where
  obj C := .of Cᵒᵖ
  map F := F.toFunctor.op.toCatHom

/-- The natural isomorphism between the double application of `Cat.opFunctor` and the
identity functor on `Cat`. -/
@[simps!]
/--
Definition of `opFunctorInvolutive` / `opFunctorInvolutive` 的定义

English:
definition opFunctorInvolutive
  signature: : opFunctor.{v₁, u₁} ⋙ opFunctor.{v₁, u₁} ≅ 𝟭 _
  body: NatIso.ofComponents (fun C => .mk (unopUnop C).toCatHom (opOp C).toCatHom)

中文:
定义 opFunctorInvolutive
  签名: : opFunctor.{v₁, u₁} ⋙ opFunctor.{v₁, u₁} ≅ 𝟭 _
  定义体: NatIso.ofComponents (fun C => .mk (unopUnop C).toCatHom (opOp C).toCatHom)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, toCatHom, unopUnop
-/
def opFunctorInvolutive : opFunctor.{v₁, u₁} ⋙ opFunctor.{v₁, u₁} ≅ 𝟭 _ :=
  NatIso.ofComponents (fun C => .mk (unopUnop C).toCatHom (opOp C).toCatHom)

/-- The equivalence `Cat ≌ Cat` associating each category with its opposite category. -/
@[simps]
/--
Definition of `opEquivalence` / `opEquivalence` 的定义

English:
definition opEquivalence
  signature: : Cat.{v₁, u₁} ≌ Cat.{v₁, u₁} where
  body: opFunctor
  inverse := opFunctor
  unitIso := NatIso.ofComponents (fun _ => Iso.mk (opOp _).toCatHom (unopUnop _).toCatHom)
  counitIso := NatIso.ofComponents (fun _ => Iso.mk (unopUnop _).toCatHom (opOp _).toCatHom)

中文:
定义 opEquivalence
  签名: : Cat.{v₁, u₁} ≌ Cat.{v₁, u₁} where
  定义体: opFunctor
  inverse := opFunctor
  unitIso := NatIso.ofComponents (fun _ => Iso.mk (opOp _).toCatHom (unopUnop _).toCatHom)
  counitIso := NatIso.ofComponents (fun _ => Iso.mk (unopUnop _).toCatHom (opOp _).toCatHom)

Depends on / 依赖: opFunctor
-/
def opEquivalence : Cat.{v₁, u₁} ≌ Cat.{v₁, u₁} where
  functor := opFunctor
  inverse := opFunctor
  unitIso := NatIso.ofComponents (fun _ => Iso.mk (opOp _).toCatHom (unopUnop _).toCatHom)
  counitIso := NatIso.ofComponents (fun _ => Iso.mk (unopUnop _).toCatHom (opOp _).toCatHom)

end Cat

end CategoryTheory
