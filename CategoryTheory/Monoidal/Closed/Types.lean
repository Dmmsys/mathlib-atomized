/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Cartesian closure of Type

Show that `Type u₁` is Cartesian closed, and `C ⥤ Type u₁` is Cartesian closed for `C` a small
category in `Type u₁`.
Note this implies that the category of presheaves on a small category `C` is Cartesian closed.
-/

@[expose] public section


namespace CategoryTheory

noncomputable section

open Category Limits MonoidalCategory

universe v₁ v₂ u₁ u₂

variable {C : Type v₂} [Category.{v₁} C]

section MonoidalClosed

/-- The adjunction `tensorLeft.obj X ⊣ coyoneda.obj (Opposite.op X)`
for any `X : Type v₁`. -/
/-
**CategoryTheory.Types.tensorProductAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Types`。
形式化陈述：(X : Type v₁) → CategoryTheory.MonoidalCategory.tensorLeft X ⊣ CategoryThe
ory.coyoneda.obj (Opposite.op X)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `tensorLeft.obj X ⊣ coyoneda.obj (Opposite.op X)`
for any `X : Type v₁`.
-/
def Types.tensorProductAdjunction (X : Type v₁) :
    tensorLeft X ⊣ coyoneda.obj (Opposite.op X) where
  unit := { app Z := ↾fun z ↦ ↾fun x => ⟨x, z⟩ }
  counit := { app _ := ↾fun xf => xf.2.hom xf.1 }
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type v₁) : (tensorLeft X).IsLeftAdjoint :=
  ⟨_, ⟨Types.tensorProductAdjunction X⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalClosed (Type v₁) := MonoidalClosed.mk
  fun X => Closed.mk _ (Types.tensorProductAdjunction X)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type v₁} [SmallCategory C] : MonoidalClosed (C ⥤ Type v₁) :=
  MonoidalClosed.mk fun F => by
    haveI : ∀ X : Type v₁, PreservesColimits (tensorLeft X) := by infer_instance
    letI : PreservesColimits (tensorLeft F) := ⟨by infer_instance⟩
    have := Presheaf.isLeftAdjoint_of_preservesColimits.{v₁} (tensorLeft F)
    exact Closed.mk _ (Adjunction.ofIsLeftAdjoint (tensorLeft F))

-- TODO: once we have `MonoidalClosed` instances for functor categories into general monoidal
-- closed categories, replace this with that, as it will be a more explicit construction.
attribute [local instance] uliftCategory in
/-- This is not a good instance because of the universe levels. Below is the instance where the
target category is `Type (max u₁ v₁)`. -/
@[instance_reducible]
/-
**CategoryTheory.cartesianClosedFunctorToTypes** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory`。
形式化陈述：cartesianClosedFunctorToTypes {C : Type u₁} [Category.{v₁} C] : MonoidalCl
osed (C ⥤ Type (max u₁ v₁ u₂))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is not a good instance because of the universe levels. Below is the instanc
e where the
target category is `Type (max u₁ v₁)`.
-/
def cartesianClosedFunctorToTypes {C : Type u₁} [Category.{v₁} C] :
    MonoidalClosed (C ⥤ Type (max u₁ v₁ u₂)) :=
  let e : (ULiftHom.{max u₁ v₁ u₂} (ULift.{max u₁ v₁ u₂} C)) ⥤ Type (max u₁ v₁ u₂) ≌
      C ⥤ Type (max u₁ v₁ u₂) :=
      Functor.asEquivalence ((Functor.whiskeringLeft _ _ _).obj
        (ULift.equivalence.trans ULiftHom.equiv).functor)
  cartesianClosedOfEquiv e

-- TODO: once we have `MonoidalClosed` instances for functor categories into general monoidal
-- closed categories, replace this with that, as it will be a more explicit construction.
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type u₁} [Category.{v₁} C] : MonoidalClosed (C ⥤ Type (max u₁ v₁)) :=
  cartesianClosedFunctorToTypes

-- TODO: once we have `MonoidalClosed` instances for functor categories into general monoidal
-- closed categories, replace this with that, as it will be a more explicit construction.
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{v₁} C] :
    MonoidalClosed (C ⥤ Type v₁) :=
  let e : (SmallModel C) ⥤ Type v₁ ≌ C ⥤ Type v₁ :=
    Functor.asEquivalence ((Functor.whiskeringLeft _ _ _).obj (equivSmallModel _).functor)
  cartesianClosedOfEquiv e

end MonoidalClosed

end

end CategoryTheory

