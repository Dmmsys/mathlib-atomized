/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
/-!

# Effectively enough objects in the image of a functor

We define the class `F.EffectivelyEnough` on a functor `F : C ⥤ D` which says that for every object
in `D`, there exists an effective epi to it from an object in the image of `F`.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

namespace Functor

/--
An effective presentation of an object `X` with respect to a functor `F` is the data of an effective
epimorphism of the form `F.obj p ⟶ X`.
-/
/-
**CategoryTheory.Functor.EffectivePresentation** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTh
eory.Functor C D → D → Type (max u_1 v_2)
参数：max u_1 v_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An effective presentation of an object `X` with respect to a functor `F` is the 
data of an effective
epimorphism of the form `F.obj p ⟶ X`.
-/
structure EffectivePresentation (X : D) where
  /-- The object of `C` giving the source of the effective epi -/
  p : C
  /-- The morphism `F.obj p ⟶ X` -/
  f : F.obj p ⟶ X
  /-- `f` is an effective epi -/
  effectiveEpi : EffectiveEpi f

/--
`D` has *effectively enough objects* with respect to the functor `F` if every object has an
effective presentation.
-/
/-
**CategoryTheory.Functor.EffectivelyEnough** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTh
eory.Functor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`D` has *effectively enough objects* with respect to the functor `F` if every ob
ject has an
effective presentation.
-/
class EffectivelyEnough : Prop where
  /-- For every `X : D`, there exists an object `p` of `C` with an effective epi `F.obj p ⟶ X`. -/
  presentation : ∀ (X : D), Nonempty (F.EffectivePresentation X)

variable [F.EffectivelyEnough]

/--
`F.effectiveEpiOverObj X` provides an arbitrarily chosen object in the image of `F` equipped with an
effective epimorphism `F.effectiveEpiOver : F.effectiveEpiOverObj X ⟶ X`.
-/
/-
**CategoryTheory.Functor.effectiveEpiOverObj** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor`。
形式化陈述：effectiveEpiOverObj (X : D) : D
参数：X : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EffectivelyEnough.presentation`：∀ {C : Type u_1} 
{D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : Categor
yTheory.Category.{v_2, u_2} D} {F : Categor…

--- 原说明 ---
`F.effectiveEpiOverObj X` provides an arbitrarily chosen object in the image of 
`F` equipped with an
effective epimorphism `F.effectiveEpiOver : F.effectiveEpiOverObj X ⟶ X`.
-/
noncomputable def effectiveEpiOverObj (X : D) : D :=
  F.obj (EffectivelyEnough.presentation (F := F) X).some.p

/--
The epimorphism `F.effectiveEpiOver : F.effectiveEpiOverObj X ⟶ X` from the arbitrarily chosen
object in the image of `F` over `X`.
-/
/-
**CategoryTheory.Functor.effectiveEpiOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：effectiveEpiOver (X : D) : F.effectiveEpiOverObj X ⟶ X
参数：X : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EffectivelyEnough.presentation`：∀ {C : Type u_1} 
{D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : Categor
yTheory.Category.{v_2, u_2} D} {F : Categor…

--- 原说明 ---
The epimorphism `F.effectiveEpiOver : F.effectiveEpiOverObj X ⟶ X` from the arbi
trarily chosen
object in the image of `F` over `X`.
-/
noncomputable def effectiveEpiOver (X : D) : F.effectiveEpiOverObj X ⟶ X :=
  (EffectivelyEnough.presentation X).some.f
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : D) : EffectiveEpi (F.effectiveEpiOver X) :=
  (EffectivelyEnough.presentation X).some.effectiveEpi

/-- An effective presentation of an object with respect to an equivalence of categories. -/
/-
**CategoryTheory.Functor.equivalenceEffectivePresentation** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：equivalenceEffectivePresentation (e : C ≌ D) (X : D) : EffectivePresentati
on e.functor X where p
参数：e : C ≌ D；X : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An effective presentation of an object with respect to an equivalence of categor
ies.
-/
def equivalenceEffectivePresentation (e : C ≌ D) (X : D) :
    EffectivePresentation e.functor X where
  p := e.inverse.obj X
  f := e.counit.app _
  effectiveEpi := inferInstance
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEquivalence F] : EffectivelyEnough F where
  presentation X := ⟨equivalenceEffectivePresentation F.asEquivalence X⟩

end Functor

end CategoryTheory

