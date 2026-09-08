/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Shift.SingleFunctors

/-!
# Lift of a "single functor" to a full subcategory

Let `C`, `D` and `E` be categories. Let `A` be an additive monoid.
Assume that `D` and `E` have shifts by `A` and that we have
a fully faithful functor `G : D ⥤ A` which commutes with shifts.
Given `F : SingleFunctors C E A`, and a family of functors
`Φ a : C ⥤ D` with isomorphisms `Φ a ⋙ G ≅ F.functor a` for all `a : A`,
we lift `F` in `SingleFunctor C D A`.

-/

@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {A : Type*} [AddMonoid A] [HasShift D A] [HasShift E A]
  (F : SingleFunctors C E A) (G : D ⥤ E) [G.CommShift A]
  [G.Full] [G.Faithful] (Φ : A → C ⥤ D) (hΦ : ∀ a, Φ a ⋙ G ≅ F.functor a)

namespace SingleFunctors

namespace lift

variable {F G Φ}

/-- Auxiliary definition for `SingleFunctors.lift`. -/
@[irreducible]
/-
**CategoryTheory.SingleFunctors.lift.shiftIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.SingleFunctors.lift`。
形式化陈述：shiftIso (n a a' : A) (h : n + a = a') : Φ a' ⋙ shiftFunctor D n ≅ Φ a
参数：n a a' : A；h : n + a = a'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `SingleFunctors.lift`.
-/
noncomputable def shiftIso (n a a' : A) (h : n + a = a') :
    Φ a' ⋙ shiftFunctor D n ≅ Φ a :=
  ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).preimageIso
    (associator _ _ _ ≪≫
      isoWhiskerLeft _ (G.commShiftIso n) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (hΦ a') _ ≪≫ F.shiftIso n a a' h ≪≫ (hΦ a).symm)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SingleFunctors.lift.map_shiftIso_hom_app** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.SingleFunctors.lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma map_shiftIso_hom_app (n a a' : A) (h : n + a = a') (X : C) :
    dsimp% G.map ((lift.shiftIso hΦ n a a' h).hom.app X) =
      (G.commShiftIso n).hom.app _ ≫ (shiftFunctor E n).map ((hΦ a').hom.app X) ≫
        (F.shiftIso n a a' h).hom.app X ≫ (hΦ a).inv.app X := by
  simp [shiftIso]

end lift

set_option backward.defeqAttrib.useBackward true in
/-- Let `C`, `D` and `E` be categories. Let `A` be an additive monoid.
Assume that `D` and `E` have shifts by `A` and that we have
a fully faithful functor `G : D ⥤ A` which commutes with shifts.
Given `F : SingleFunctors C E A`, and a family of functors
`Φ a : C ⥤ D` with isomorphisms `Φ a ⋙ G ≅ F.functor a` for all `a : A`,
this is a term in `SingleFunctors C D A` which is given by the functors `Φ a`
for all `a`. -/
@[simps functor]
/-
**CategoryTheory.SingleFunctors.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
ingleFunctors`。
形式化陈述：lift : SingleFunctors C D A where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `C`, `D` and `E` be categories. Let `A` be an additive monoid.
Assume that `D` and `E` have shifts by `A` and that we have
a fully faithful functor `G : D ⥤ A` which commutes with shifts.
Given `F : SingleFunctors C E A`, and a family of functors
`Φ a : C ⥤ D` with isomorphisms `Φ a ⋙ G ≅ F.functor a` for all `a : A`,
this is a term in `SingleFunctors C D A` which is given by the functors `Φ a`
for all `a`.
-/
noncomputable def lift : SingleFunctors C D A where
  functor := Φ
  shiftIso := lift.shiftIso hΦ
  shiftIso_zero a := by
    ext X
    apply G.map_injective
    simp [lift.map_shiftIso_hom_app, Functor.commShiftIso_zero]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    apply G.map_injective
    dsimp
    simp only [lift.map_shiftIso_hom_app, map_comp, commShiftIso_hom_naturality_assoc]
    rw [F.shiftIso_add n m a a' a'' ha' ha'']
    simp [commShiftIso_add, ← Functor.map_comp_assoc, -Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.SingleFunctors.map_lift_shiftIso_hom_app** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.SingleFunctors`。
形式化陈述：map_lift_shiftIso_hom_app (n a a' : A) (h : n + a = a') (X : C) : dsimp% G
.map (((lift F G Φ hΦ).shiftIso n a a' h).hom.app X) = (G.commShiftIso n).hom.ap
p _ ≫ (shiftFunctor E n).map ((hΦ a').hom.app X) ≫ (F.shiftIso n a a' h).hom.app
 X ≫ (hΦ a).inv.app X
参数：n a a' : A；h : n + a = a'；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Shift.SingleFunctorsLift.0.CategoryTheor
y.SingleFunctors.lift.map_shiftIso_hom_app`：∀ {C : Type u_1} {D : Type u_2} {E :
 Type u_3} [inst : CategoryTheory.Category.{u_7, u_1} C]   [inst_1 : CategoryThe
ory.Category.{u_6, u_2} …
-/
lemma map_lift_shiftIso_hom_app (n a a' : A) (h : n + a = a') (X : C) :
    dsimp% G.map (((lift F G Φ hΦ).shiftIso n a a' h).hom.app X) =
      (G.commShiftIso n).hom.app _ ≫ (shiftFunctor E n).map ((hΦ a').hom.app X) ≫
        (F.shiftIso n a a' h).hom.app X ≫ (hΦ a).inv.app X :=
  lift.map_shiftIso_hom_app ..

set_option backward.defeqAttrib.useBackward true in
/-- After postcomposition with the fully faithful functor `G`,
`lift F G Φ hΦ` becomes isomorphic to `F`. -/
@[simps!]
/-
**CategoryTheory.SingleFunctors.liftPostcompIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.SingleFunctors`。
形式化陈述：liftPostcompIso : (lift F G Φ hΦ).postcomp G ≅ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
After postcomposition with the fully faithful functor `G`,
`lift F G Φ hΦ` becomes isomorphic to `F`.
-/
noncomputable def liftPostcompIso : (lift F G Φ hΦ).postcomp G ≅ F :=
  isoMk (hΦ) (fun n a a' ha' ↦ by
    ext X
    have := (hΦ a).inv_hom_id_app X
    dsimp at this
    simp [map_lift_shiftIso_hom_app, this])

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SingleFunctors.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Singl
eFunctors`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] [Preadditive D] [Preadditive E] [G.Additive] (a : A)
    [(F.functor a).Additive] : ((lift F G Φ hΦ).functor a).Additive := by
  have : ((lift F G Φ hΦ).functor a ⋙ G).Additive := by
    dsimp
    rwa [Functor.additive_iff_of_iso (hΦ a)]
  exact Functor.additive_of_comp_faithful _ G

end SingleFunctors

end CategoryTheory

