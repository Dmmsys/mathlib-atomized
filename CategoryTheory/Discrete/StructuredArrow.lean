/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Structured arrows when the target category is discrete

When `T` is a type with a unique element `t`, we show that
if `F : C ⥤ Discrete T`, then the categories
`StructuredArrow (Discrete.mk t) F` and
`CostructuredArrow (Discrete.mk t) F` are equivalent to `C`.

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {T : Type w}

namespace Discrete

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F : C ⥤ Discrete T` is a functor with `T` containing
a unique element `t`, then this is the equivalence
`StructuredArrow (Discrete.mk t) F ≌ C`. -/
/-
**CategoryTheory.Discrete.structuredArrowEquivalenceOfUnique** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Discrete`。
形式化陈述：structuredArrowEquivalenceOfUnique (F : C ⥤ Discrete T) (t : T) [Subsingle
ton T] : StructuredArrow (.mk t) F ≌ C where functor
参数：F : C ⥤ Discrete T；t : T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Discrete T` is a functor with `T` containing
a unique element `t`, then this is the equivalence
`StructuredArrow (Discrete.mk t) F ≌ C`.
-/
def structuredArrowEquivalenceOfUnique
    (F : C ⥤ Discrete T) (t : T) [Subsingleton T] :
    StructuredArrow (.mk t) F ≌ C where
  functor := StructuredArrow.proj _ _
  inverse.obj X := StructuredArrow.mk (Y := X) (eqToHom (by subsingleton))
  inverse.map f := StructuredArrow.homMk f
  unitIso := NatIso.ofComponents (fun _ ↦ StructuredArrow.isoMk (Iso.refl _))
  counitIso := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F : C ⥤ Discrete T` is a functor with `T` containing
a unique element `t`, then this is the equivalence
`CostructuredArrow F (Discrete.mk t) ≌ C`. -/
/-
**CategoryTheory.Discrete.costructuredArrowEquivalenceOfUnique** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Discrete`。
形式化陈述：costructuredArrowEquivalenceOfUnique (F : C ⥤ Discrete T) (t : T) [Subsing
leton T] : CostructuredArrow F (.mk t) ≌ C where functor
参数：F : C ⥤ Discrete T；t : T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Discrete T` is a functor with `T` containing
a unique element `t`, then this is the equivalence
`CostructuredArrow F (Discrete.mk t) ≌ C`.
-/
def costructuredArrowEquivalenceOfUnique
    (F : C ⥤ Discrete T) (t : T) [Subsingleton T] :
    CostructuredArrow F (.mk t) ≌ C where
  functor := CostructuredArrow.proj _ _
  inverse.obj X := CostructuredArrow.mk (Y := X) (eqToHom (by subsingleton))
  inverse.map f := CostructuredArrow.homMk f
  unitIso := NatIso.ofComponents (fun _ ↦ CostructuredArrow.isoMk (Iso.refl _))
  counitIso := Iso.refl _

end Discrete

end CategoryTheory

