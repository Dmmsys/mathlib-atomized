/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Comparison between `Subfunctor`, `MonoOver` and `Subobject`

Given a type-valued functor `F : C ⥤ Type w`, we define an equivalence
of categories `Subfunctor.equivalenceMonoOver F : Subfunctor F ≌ MonoOver F`
and an order isomorphism `Subfunctor.orderIsoSubject F : Subfunctor F ≃o Subobject F`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

namespace Subfunctor

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories `Subfunctor F ≌ MonoOver F`. -/
@[simps]
/-
**CategoryTheory.Subfunctor.equivalenceMonoOver** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Subfunctor`。
形式化陈述：equivalenceMonoOver : Subfunctor F ≌ MonoOver F where functor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.instMonoFunctorTypeι`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor C (Type w)}   (G : 
CategoryTheory.Subfunctor F), Catego…

--- 原说明 ---
The equivalence of categories `Subfunctor F ≌ MonoOver F`.
-/
noncomputable def equivalenceMonoOver : Subfunctor F ≌ MonoOver F where
  functor :=
    { obj A := MonoOver.mk A.ι
      map {A B} f := MonoOver.homMk (Subfunctor.homOfLe (leOfHom f)) }
  inverse :=
    { obj X := Subfunctor.range X.arrow
      map {X Y} f := homOfLE (by
        rw [← MonoOver.w f]
        apply range_comp_le) }
  unitIso := NatIso.ofComponents (fun A ↦ eqToIso (by simp))
  counitIso := NatIso.ofComponents
    (fun X ↦ MonoOver.isoMk ((asIso (toRange X.arrow)).symm))

variable {F} in
@[simp]
/-
**CategoryTheory.Subfunctor.range_subobjectMk_** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Subfunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma range_subobjectMk_ι (A : Subfunctor F) :
    range (Subobject.mk A.ι).arrow = A :=
  (((equivalenceMonoOver F).trans
    (ThinSkeleton.equivalence _).symm).unitIso.app A).to_eq.symm

variable {F} in
@[simp]
/-
**CategoryTheory.Subfunctor.subobjectMk_range_arrow** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Subfunctor`。
形式化陈述：subobjectMk_range_arrow (X : Subobject F) : Subobject.mk (range X.arrow).ι
 = X
参数：X : Subobject F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.to_eq`：∀ {X : Type u} [inst : PartialOrder X] {x y : 
X} (f : x ≅ y), x = y
-/
lemma subobjectMk_range_arrow (X : Subobject F) :
    Subobject.mk (range X.arrow).ι = X :=
  (((equivalenceMonoOver F).trans
    (ThinSkeleton.equivalence _).symm).counitIso.app X).to_eq

/-- The order isomorphism `Subfunctor F ≃o MonoOver F`. -/
@[simps]
/-
**CategoryTheory.Subfunctor.orderIsoSubobject** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Subfunctor`。
形式化陈述：orderIsoSubobject : Subfunctor F ≃o Subobject F where toFun A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.instMonoFunctorTypeι`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor C (Type w)}   (G : 
CategoryTheory.Subfunctor F), Catego…

--- 原说明 ---
The order isomorphism `Subfunctor F ≃o MonoOver F`.
-/
noncomputable def orderIsoSubobject : Subfunctor F ≃o Subobject F where
  toFun A := Subobject.mk A.ι
  invFun X := Subfunctor.range X.arrow
  left_inv A := by simp
  right_inv X := by simp
  map_rel_iff' {A B} := by
    constructor
    · intro h
      have : range (Subobject.mk A.ι).arrow ≤ range (Subobject.mk B.ι).arrow :=
        leOfHom (((equivalenceMonoOver F).trans
          (ThinSkeleton.equivalence _).symm).inverse.map (homOfLE h))
      simpa using this
    · intro h
      exact leOfHom (((equivalenceMonoOver F).trans
        (ThinSkeleton.equivalence _).symm).functor.map (homOfLE h))

end Subfunctor

end CategoryTheory

