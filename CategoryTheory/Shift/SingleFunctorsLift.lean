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
  [G.Full] [G.Faithful] (Φ : A -> C ⥤ D) (hΦ : forall a, Φ a ⋙ G ≅ F.functor a)

namespace SingleFunctors

namespace lift

variable {F G Φ}

/-- Auxiliary definition for `SingleFunctors.lift`. -/
@[irreducible]
/--
Definition of `shiftIso` / `shiftIso` 的定义

English:
definition shiftIso
  signature: (n a a' : A) (h : n + a = a')
  body: ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).preimageIso
    (associator _ _ _ ≪≫
      isoWhiskerLeft _ (G.commShiftIso n) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (hΦ a') _ ≪≫ F.shiftIso n a a' h ≪≫ (hΦ a).symm)

中文:
定义 shiftIso
  签名: (n a a' : A) (h : n + a = a')
  定义体: ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).preimageIso
    (associator _ _ _ ≪≫
      isoWhiskerLeft _ (G.commShiftIso n) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (hΦ a') _ ≪≫ F.shiftIso n a a' h ≪≫ (hΦ a).symm)

Depends on / 依赖: F.shiftIso, FullyFaithful, FullyFaithful.ofFullyFaithful, Functor, Functor.associator, G.commShiftIso, associator, commShiftIso, isoWhiskerLeft, isoWhiskerRight, ofFullyFaithful, preimageIso, shiftIso, whiskeringRight
-/
noncomputable def shiftIso (n a a' : A) (h : n + a = a') :
    Φ a' ⋙ shiftFunctor D n ≅ Φ a :=
  ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).preimageIso
    (associator _ _ _ ≪≫
      isoWhiskerLeft _ (G.commShiftIso n) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (hΦ a') _ ≪≫ F.shiftIso n a a' h ≪≫ (hΦ a).symm)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `map_shiftIso_hom_app` / 引理 `map_shiftIso_hom_app`

English:
lemma map_shiftIso_hom_app
  given: (n a a' : A) (h : n + a = a') (X : C)
  proof: by
  simp [shiftIso]

中文:
引理 map_shiftIso_hom_app
  条件: (n a a' : A) (h : n + a = a') (X : C)
  证明: by
  simp [shiftIso]
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
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : SingleFunctors C D A where
  body: Φ
  shiftIso := lift.shiftIso hΦ
  shiftIso_zero a := by
    ext X
    apply G.map_injective
    simp [lift.map_shiftIso_hom_app, Functor.commShiftIso_zero]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    apply G.map_injective
    dsimp
    simp only [lift.map_shiftIso_hom_app, map_comp, co

中文:
定义 lift
  签名: : SingleFunctors C D A where
  定义体: Φ
  shiftIso := lift.shiftIso hΦ
  shiftIso_zero a := by
    ext X
    apply G.map_injective
    simp [lift.map_shiftIso_hom_app, Functor.commShiftIso_zero]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    apply G.map_injective
    dsimp
    simp only [lift.map_shiftIso_hom_app, map_comp, co
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
/--
lemma `map_lift_shiftIso_hom_app` / 引理 `map_lift_shiftIso_hom_app`

English:
lemma map_lift_shiftIso_hom_app
  given: (n a a' : A) (h : n + a = a') (X : C)
  proof: lift.map_shiftIso_hom_app ..

中文:
引理 map_lift_shiftIso_hom_app
  条件: (n a a' : A) (h : n + a = a') (X : C)
  证明: lift.map_shiftIso_hom_app ..

Depends on / 依赖: lift.map_shiftIso_hom_app, map_shiftIso_hom_app
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
/--
Definition of `liftPostcompIso` / `liftPostcompIso` 的定义

English:
definition liftPostcompIso
  signature: : (lift F G Φ hΦ).postcomp G ≅ F
  body: isoMk (hΦ) (fun n a a' ha' => by
    ext X
    have := (hΦ a).inv_hom_id_app X
    dsimp at this
    simp [map_lift_shiftIso_hom_app, this])

中文:
定义 liftPostcompIso
  签名: : (lift F G Φ hΦ).postcomp G ≅ F
  定义体: isoMk (hΦ) (fun n a a' ha' => by
    ext X
    have := (hΦ a).inv_hom_id_app X
    dsimp at this
    simp [map_lift_shiftIso_hom_app, this])

Depends on / 依赖: inv_hom_id_app, map_lift_shiftIso_hom_app
-/
noncomputable def liftPostcompIso : (lift F G Φ hΦ).postcomp G ≅ F :=
  isoMk (hΦ) (fun n a a' ha' => by
    ext X
    have := (hΦ a).inv_hom_id_app X
    dsimp at this
    simp [map_lift_shiftIso_hom_app, this])

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] [Preadditive D] [Preadditive E] [G.Additive] (a
  body: by
  have : ((lift F G Φ hΦ).functor a ⋙ G).Additive := by
    dsimp
    rwa [Functor.additive_iff_of_iso (hΦ a)]
  exact Functor.additive_of_comp_faithful _ G

中文:
实例 [预加性
  签名: C] [预加性 D] [预加性 E] [G.加性] (a
  定义体: by
  have : ((lift F G Φ hΦ).functor a ⋙ G).Additive := by
    dsimp
    rwa [Functor.additive_iff_of_iso (hΦ a)]
  exact Functor.additive_of_comp_faithful _ G

Depends on / 依赖: Additive, Functor, Functor.additive_iff_of_iso, Functor.additive_of_comp_faithful, additive_iff_of_iso, additive_of_comp_faithful, functor
-/
instance [Preadditive C] [Preadditive D] [Preadditive E] [G.Additive] (a : A)
    [(F.functor a).Additive] : ((lift F G Φ hΦ).functor a).Additive := by
  have : ((lift F G Φ hΦ).functor a ⋙ G).Additive := by
    dsimp
    rwa [Functor.additive_iff_of_iso (hΦ a)]
  exact Functor.additive_of_comp_faithful _ G

end SingleFunctors

end CategoryTheory
