/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Bicategory.End
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Promoting a monoidal category to a single object bicategory.

A monoidal category can be thought of as a bicategory with a single object.

The objects of the monoidal category become the 1-morphisms,
with composition given by tensor product,
and the morphisms of the monoidal category become the 2-morphisms.

We verify that the endomorphisms of that single object recovers the original monoidal category.

One could go much further: the bicategory of monoidal categories
(equipped with monoidal functors and monoidal natural transformations)
is equivalent to the bicategory consisting of
* single object bicategories,
* pseudofunctors, and
* (oplax) natural transformations `η` such that `η.app Unit.unit = 𝟙 _`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- Promote a monoidal category to a bicategory with a single object.
(The objects of the monoidal category become the 1-morphisms,
with composition given by tensor product,
and the morphisms of the monoidal category become the 2-morphisms.)
-/
@[nolint unusedArguments]
/-
**CategoryTheory.MonoidalSingleObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：MonoidalSingleObj (C : Type u) [Category.{v} C] [MonoidalCategory C]
参数：C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promote a monoidal category to a bicategory with a single object.
(The objects of the monoidal category become the 1-morphisms,
with composition given by tensor product,
and the morphisms of the monoidal category become the 2-morphisms.)
-/
def MonoidalSingleObj (C : Type u) [Category.{v} C] [MonoidalCategory C] :=
  Unit
deriving Inhabited

open MonoidalCategory
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bicategory (MonoidalSingleObj C) where
  Hom _ _ := C
  id _ := 𝟙_ C
  comp X Y := tensorObj X Y
  whiskerLeft X _ _ f := X ◁ f
  whiskerRight f Z := f ▷ Z
  associator X Y Z := α_ X Y Z
  leftUnitor X := λ_ X
  rightUnitor X := ρ_ X
  whisker_exchange := whisker_exchange

namespace MonoidalSingleObj

/-- The unique object in the bicategory obtained by "promoting" a monoidal category. -/
@[nolint unusedArguments]
/-
**CategoryTheory.MonoidalSingleObj.star** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.MonoidalSingleObj`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.MonoidalCategory C] → CategoryTheory.MonoidalSingleObj C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique object in the bicategory obtained by "promoting" a monoidal category.
-/
protected def star : MonoidalSingleObj C :=
  Unit.unit

/-- The monoidal functor from the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
to the original monoidal category.

We subsequently show this is an equivalence.
-/
@[simps]
/-
**CategoryTheory.MonoidalSingleObj.endMonoidalStarFunctor** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.MonoidalSingleObj`。
形式化陈述：endMonoidalStarFunctor : (EndMonoidal (MonoidalSingleObj.star C)) ⥤ C wher
e obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal functor from the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
to the original monoidal category.

We subsequently show this is an equivalence.
-/
def endMonoidalStarFunctor : (EndMonoidal (MonoidalSingleObj.star C)) ⥤ C where
  obj X := X
  map f := f

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MonoidalSingleObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mo
noidalSingleObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (endMonoidalStarFunctor C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence between the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
and the original monoidal category.
-/
@[simps]
/-
**CategoryTheory.MonoidalSingleObj.endMonoidalStarFunctorEquivalence** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.MonoidalSingleObj`。
形式化陈述：endMonoidalStarFunctorEquivalence : EndMonoidal (MonoidalSingleObj.star C)
 ≌ C where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
and the original monoidal category.
-/
noncomputable def endMonoidalStarFunctorEquivalence :
    EndMonoidal (MonoidalSingleObj.star C) ≌ C where
  functor := endMonoidalStarFunctor C
  inverse :=
    { obj := fun X => X
      map := fun f => f }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
/-
**CategoryTheory.MonoidalSingleObj.endMonoidalStarFunctor_isEquivalence** 是 Math
lib 中的一个实例，位于命名空间 `CategoryTheory.MonoidalSingleObj`。
形式化陈述：endMonoidalStarFunctor_isEquivalence : (endMonoidalStarFunctor C).IsEquiva
lence
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance endMonoidalStarFunctor_isEquivalence : (endMonoidalStarFunctor C).IsEquivalence :=
  (endMonoidalStarFunctorEquivalence C).isEquivalence_functor

end MonoidalSingleObj

end CategoryTheory

