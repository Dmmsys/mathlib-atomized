/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The pullback of a shift by a monoid morphism

Given a shift by a monoid `B` on a category `C` and a monoid morphism `φ : A →+ B`,
we define a shift by `A` on a category `PullbackShift C φ` which is a type synonym for `C`.

If `F : C ⥤ D` is a functor between categories equipped with shifts by `B`, we define
a type synonym `PullbackShift.functor F φ` for `F`. When `F` has a `CommShift` structure
by `B`, we define a pulled back `CommShift` structure by `A` on `PullbackShift.functor F φ`.

Similarly, if `τ` is a natural transformation between functors `F,G : C ⥤ D`, we define
a type synonym
`PullbackShift.natTrans τ φ : PullbackShift.functor F φ ⟶ PullbackShift.functor G φ`.
When `τ` has a `CommShift` structure by `B` (i.e. is compatible with `CommShift` structures
on `F` and `G`), we define a pulled back `CommShift` structure by `A` on
`PullbackShift.natTrans τ φ`.

Finally, if we have an adjunction `F ⊣ G` (with `G : D ⥤ C`), we define a type synonym
`PullbackShift.adjunction adj φ : PullbackShift.functor F φ ⊣ PullbackShift.functor G φ`
and we show that, if `adj` is compatible with `CommShift` structures
on `F` and `G`, then `PullbackShift.adjunction adj φ` is also compatible with the pulled back
`CommShift` structures.
-/

@[expose] public section

namespace CategoryTheory

open Limits Category

variable (C : Type*) [Category* C] {A B : Type*} [AddMonoid A] [AddMonoid B]

/-- The category `PullbackShift C φ` is equipped with a shift such that for all `a`,
the shift functor by `a` is `shiftFunctor C (φ a)`. -/
@[nolint unusedArguments]
/--
Definition of `PullbackShift` / `PullbackShift` 的定义

English:
definition PullbackShift
  signature: [HasShift C B] (_ : A ->+ B)
  body: C
deriving Category

中文:
定义 PullbackShift
  签名: [有Shift C B] (_ : A ->+ B)
  定义体: C
deriving Category
-/
def PullbackShift [HasShift C B] (_ : A ->+ B) := C
deriving Category

attribute [local instance] endofunctorMonoidalCategory

variable [HasShift C B] (φ : A ->+ B)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasShift (PullbackShift C φ) A
  body: Discrete.addMonoidalFunctor φ ⋙ shiftMonoidalFunctor C B

中文:
实例 :
  签名: 有Shift (PullbackShift C φ) A
  定义体: Discrete.addMonoidalFunctor φ ⋙ shiftMonoidalFunctor C B

Depends on / 依赖: Discrete, Discrete.addMonoidalFunctor, addMonoidalFunctor, shiftMonoidalFunctor
-/
instance : HasShift (PullbackShift C φ) A where
  shift := Discrete.addMonoidalFunctor φ ⋙ shiftMonoidalFunctor C B

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] : HasZeroObject (PullbackShift C φ)
  body: inferInstanceAs HasZeroObject C

中文:
实例 [有ZeroObject
  签名: C] : 有ZeroObject (PullbackShift C φ)
  定义体: inferInstanceAs HasZeroObject C

Depends on / 依赖: HasZeroObject
-/
instance [HasZeroObject C] : HasZeroObject (PullbackShift C φ) :=
inferInstanceAs HasZeroObject C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] : Preadditive (PullbackShift C φ)
  body: inferInstanceAs Preadditive C

中文:
实例 [预加性
  签名: C] : 预加性 (PullbackShift C φ)
  定义体: inferInstanceAs Preadditive C

Depends on / 依赖: Preadditive
-/
instance [Preadditive C] : Preadditive (PullbackShift C φ) :=
inferInstanceAs Preadditive C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] (a
  body: inferInstanceAs (shiftFunctor C (φ a)).Additive

中文:
实例 [预加性
  签名: C] (a
  定义体: inferInstanceAs (shiftFunctor C (φ a)).Additive

Depends on / 依赖: Additive, shiftFunctor
-/
instance [Preadditive C] (a : A) [(shiftFunctor C (φ a)).Additive] :
    (shiftFunctor (PullbackShift C φ) a).Additive :=
  inferInstanceAs (shiftFunctor C (φ a)).Additive

/--
Definition of `pullbackShiftIso` / `pullbackShiftIso` 的定义

English:
definition pullbackShiftIso
  signature: (a : A) (b : B) (h : b = φ a)
  body: eqToIso (by subst h; rfl)

中文:
定义 pullbackShiftIso
  签名: (a : A) (b : B) (h : b = φ a)
  定义体: eqToIso (by subst h; rfl)

Depends on / 依赖: eqToIso
-/
def pullbackShiftIso (a : A) (b : B) (h : b = φ a) :
    shiftFunctor (PullbackShift C φ) a ≅ shiftFunctor C b := eqToIso (by subst h; rfl)

variable {C}
variable (X : PullbackShift C φ) (a₁ a₂ a₃ : A) (h : a₁ + a₂ = a₃) (b₁ b₂ b₃ : B)
  (h₁ : b₁ = φ a₁) (h₂ : b₂ = φ a₂) (h₃ : b₃ = φ a₃)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `pullbackShiftFunctorZero_inv_app` / 引理 `pullbackShiftFunctorZero_inv_app`

English:
lemma pullbackShiftFunctorZero_inv_app
  proof: by
  change (shiftFunctorZero C B).inv.app X ≫ _ = _
  dsimp [Discrete.eqToHom, Discrete.addMonoidalFunctor_ε]
  congr 2
  apply eqToHom_map

中文:
引理 pullbackShiftFunctorZero_inv_app
  证明: by
  change (shiftFunctorZero C B).inv.app X ≫ _ = _
  dsimp [Discrete.eqToHom, Discrete.addMonoidalFunctor_ε]
  congr 2
  apply eqToHom_map

Depends on / 依赖: Discrete, Discrete.addMonoidalFunctor_, Discrete.eqToHom, eqToHom, eqToHom_map, inv.app, shiftFunctorZero
-/
lemma pullbackShiftFunctorZero_inv_app :
    (shiftFunctorZero _ A).inv.app X =
      (shiftFunctorZero C B).inv.app X ≫ (pullbackShiftIso C φ 0 0 (by simp)).inv.app X := by
  change (shiftFunctorZero C B).inv.app X ≫ _ = _
  dsimp [Discrete.eqToHom, Discrete.addMonoidalFunctor_ε]
  congr 2
  apply eqToHom_map

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pullbackShiftFunctorZero_hom_app` / 引理 `pullbackShiftFunctorZero_hom_app`

English:
lemma pullbackShiftFunctorZero_hom_app
  proof: by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X)]; rw [Iso.inv_hom_id_app]; rw [pullbackShiftFunctorZero_inv_app]; rw [assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.inv_hom_id_app]
  rfl

中文:
引理 pullbackShiftFunctorZero_hom_app
  证明: by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X)]; rw [Iso.inv_hom_id_app]; rw [pullbackShiftFunctorZero_inv_app]; rw [assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.inv_hom_id_app]
  rfl

Depends on / 依赖: Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, cancel_epi, inv.app, inv_hom_id_app, inv_hom_id_app_assoc, pullbackShiftFunctorZero_inv_app, shiftFunctorZero
-/
lemma pullbackShiftFunctorZero_hom_app :
    (shiftFunctorZero _ A).hom.app X =
      (pullbackShiftIso C φ 0 0 (by simp)).hom.app X ≫ (shiftFunctorZero C B).hom.app X := by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X)]; rw [Iso.inv_hom_id_app]; rw [pullbackShiftFunctorZero_inv_app]; rw [assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.inv_hom_id_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pullbackShiftFunctorZero'_inv_app` / 引理 `pullbackShiftFunctorZero'_inv_app`

English:
lemma pullbackShiftFunctorZero'_inv_app
  proof: by
  rw [pullbackShiftFunctorZero_inv_app]
  simp only [Functor.id_obj, pullbackShiftIso, eqToIso.inv, eqToHom_app, shiftFunctorZero',
    Iso.trans_inv, NatTrans.comp_app, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, assoc]
  erw [comp_id]

中文:
引理 pullbackShiftFunctorZero'_inv_app
  证明: by
  rw [pullbackShiftFunctorZero_inv_app]
  simp only [Functor.id_obj, pullbackShiftIso, eqToIso.inv, eqToHom_app, shiftFunctorZero',
    Iso.trans_inv, NatTrans.comp_app, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, assoc]
  erw [comp_id]

Depends on / 依赖: Functor, Functor.id_obj, Iso.refl_inv, Iso.trans_inv, NatTrans, NatTrans.comp_app, NatTrans.id_app, comp_app, comp_id, eqToHom_app, eqToIso, eqToIso.inv, eqToIso_refl, id_app, id_obj, pullbackShiftFunctorZero_inv_app, pullbackShiftIso, refl_inv, shiftFunctorZero, trans_inv
-/
lemma pullbackShiftFunctorZero'_inv_app :
    (shiftFunctorZero _ A).inv.app X = (shiftFunctorZero' C (φ 0) (by rw [map_zero])).inv.app X ≫
      (pullbackShiftIso C φ 0 (φ 0) rfl).inv.app X := by
  rw [pullbackShiftFunctorZero_inv_app]
  simp only [Functor.id_obj, pullbackShiftIso, eqToIso.inv, eqToHom_app, shiftFunctorZero',
    Iso.trans_inv, NatTrans.comp_app, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, assoc]
  erw [comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pullbackShiftFunctorZero'_hom_app` / 引理 `pullbackShiftFunctorZero'_hom_app`

English:
lemma pullbackShiftFunctorZero'_hom_app
  proof: by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X)]; rw [Iso.inv_hom_id_app]; rw [pullbackShiftFunctorZero'_inv_app]; rw [assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.inv_hom_id_app]
  rfl

中文:
引理 pullbackShiftFunctorZero'_hom_app
  证明: by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X)]; rw [Iso.inv_hom_id_app]; rw [pullbackShiftFunctorZero'_inv_app]; rw [assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.inv_hom_id_app]
  rfl
-/
lemma pullbackShiftFunctorZero'_hom_app :
    (shiftFunctorZero _ A).hom.app X = (pullbackShiftIso C φ 0 (φ 0) rfl).hom.app X ≫
      (shiftFunctorZero' C (φ 0) (by rw [map_zero])).hom.app X := by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X)]; rw [Iso.inv_hom_id_app]; rw [pullbackShiftFunctorZero'_inv_app]; rw [assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.inv_hom_id_app]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `pullbackShiftFunctorAdd'_inv_app` / 引理 `pullbackShiftFunctorAdd'_inv_app`

English:
lemma pullbackShiftFunctorAdd'_inv_app
  proof: by
  subst h₁ h₂ h
  obtain rfl : b₃ = φ a₁ + φ a₂ := by rw [h₃, φ.map_add]
  simp only [NatTrans.naturality_assoc]
  erw [Functor.map_id, id_comp, id_comp, shiftFunctorAdd'_eq_shiftFunctorAdd,
    shiftFunctorAdd'_eq_shiftFunctorAdd]
  change _ ≫ _ = _
  congr 1
  rw [Discrete.addMonoidalFunctor_μ]
  dsimp [Discrete.eqToHom]
  congr 2
  apply eqToHom_map

中文:
引理 pullbackShiftFunctorAdd'_inv_app
  证明: by
  subst h₁ h₂ h
  obtain rfl : b₃ = φ a₁ + φ a₂ := by rw [h₃, φ.map_add]
  simp only [NatTrans.naturality_assoc]
  erw [Functor.map_id, id_comp, id_comp, shiftFunctorAdd'_eq_shiftFunctorAdd,
    shiftFunctorAdd'_eq_shiftFunctorAdd]
  change _ ≫ _ = _
  congr 1
  rw [Discrete.addMonoidalFunctor_μ]
  dsimp [Discrete.eqToHom]
  congr 2
  apply eqToHom_map

Depends on / 依赖: Discrete, Discrete.addMonoidalFunctor_, Discrete.eqToHom, Functor, Functor.map_id, NatTrans, NatTrans.naturality_assoc, _eq_shiftFunctorAdd, eqToHom, eqToHom_map, id_comp, map_add, map_id, naturality_assoc, shiftFunctorAdd
-/
lemma pullbackShiftFunctorAdd'_inv_app :
    (shiftFunctorAdd' _ a₁ a₂ a₃ h).inv.app X =
      (shiftFunctor (PullbackShift C φ) a₂).map ((pullbackShiftIso C φ a₁ b₁ h₁).hom.app X) ≫
        (pullbackShiftIso C φ a₂ b₂ h₂).hom.app _ ≫
        (shiftFunctorAdd' C b₁ b₂ b₃ (by rw [h₁, h₂, h₃, ← h, φ.map_add])).inv.app X ≫
        (pullbackShiftIso C φ a₃ b₃ h₃).inv.app X := by
  subst h₁ h₂ h
  obtain rfl : b₃ = φ a₁ + φ a₂ := by rw [h₃, φ.map_add]
  simp only [NatTrans.naturality_assoc]
  erw [Functor.map_id, id_comp, id_comp, shiftFunctorAdd'_eq_shiftFunctorAdd,
    shiftFunctorAdd'_eq_shiftFunctorAdd]
  change _ ≫ _ = _
  congr 1
  rw [Discrete.addMonoidalFunctor_μ]
  dsimp [Discrete.eqToHom]
  congr 2
  apply eqToHom_map

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pullbackShiftFunctorAdd'_hom_app` / 引理 `pullbackShiftFunctorAdd'_hom_app`

English:
lemma pullbackShiftFunctorAdd'_hom_app
  proof: by
  rw [← cancel_epi ((shiftFunctorAdd' _ a₁ a₂ a₃ h).inv.app X)]; rw [Iso.inv_hom_id_app]; rw [pullbackShiftFunctorAdd'_inv_app φ X a₁ a₂ a₃ h b₁ b₂ b₃ h₁ h₂ h₃]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.hom_inv_id_app_assoc]; rw [← Functor.map_comp]; rw [Iso.hom_inv_id_app]; rw [Functor.map_id]
  rfl

中文:
引理 pullbackShiftFunctorAdd'_hom_app
  证明: by
  rw [← cancel_epi ((shiftFunctorAdd' _ a₁ a₂ a₃ h).inv.app X)]; rw [Iso.inv_hom_id_app]; rw [pullbackShiftFunctorAdd'_inv_app φ X a₁ a₂ a₃ h b₁ b₂ b₃ h₁ h₂ h₃]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.hom_inv_id_app_assoc]; rw [← Functor.map_comp]; rw [Iso.hom_inv_id_app]; rw [Functor.map_id]
  rfl
-/
lemma pullbackShiftFunctorAdd'_hom_app :
    (shiftFunctorAdd' _ a₁ a₂ a₃ h).hom.app X =
      (pullbackShiftIso C φ a₃ b₃ h₃).hom.app X ≫
      (shiftFunctorAdd' C b₁ b₂ b₃ (by rw [h₁, h₂, h₃, ← h, φ.map_add])).hom.app X ≫
      (pullbackShiftIso C φ a₂ b₂ h₂).inv.app _ ≫
      (shiftFunctor (PullbackShift C φ) a₂).map ((pullbackShiftIso C φ a₁ b₁ h₁).inv.app X) := by
  rw [← cancel_epi ((shiftFunctorAdd' _ a₁ a₂ a₃ h).inv.app X)]; rw [Iso.inv_hom_id_app]; rw [pullbackShiftFunctorAdd'_inv_app φ X a₁ a₂ a₃ h b₁ b₂ b₃ h₁ h₂ h₃]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.hom_inv_id_app_assoc]; rw [← Functor.map_comp]; rw [Iso.hom_inv_id_app]; rw [Functor.map_id]
  rfl

variable {D : Type*} [Category* D] [HasShift D B] (F : C ⥤ D) [F.CommShift B]

/--
Definition of `PullbackShift.functor` / `PullbackShift.functor` 的定义

English:
definition PullbackShift.functor
  signature: : PullbackShift C φ ⥤ PullbackShift D φ
  body: F

中文:
定义 PullbackShift.functor
  签名: : PullbackShift C φ ⥤ PullbackShift D φ
  定义体: F
-/
def PullbackShift.functor : PullbackShift C φ ⥤ PullbackShift D φ := F

variable {F} in
/--
Definition of `PullbackShift.natTrans` / `PullbackShift.natTrans` 的定义

English:
definition PullbackShift.natTrans
  signature: {G : C ⥤ D} (τ : F ⟶ G)
  body: τ

中文:
定义 PullbackShift.natTrans
  签名: {G : C ⥤ D} (τ : F ⟶ G)
  定义体: τ
-/
def PullbackShift.natTrans {G : C ⥤ D} (τ : F ⟶ G) :
    PullbackShift.functor φ F ⟶ PullbackShift.functor φ G := τ

namespace Functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `commShiftPullback` / 实例 `commShiftPullback`

English:
instance commShiftPullback
  signature: : (PullbackShift.functor φ F).CommShift A where
  body: isoWhiskerRight (pullbackShiftIso C φ a (φ a) rfl) F ≪≫
    F.commShiftIso (φ a) ≪≫ isoWhiskerLeft _ (pullbackShiftIso D φ a (φ a) rfl).symm
  commShiftIso_zero := by
    ext
    dsimp
    simp only [F.commShiftIso_zero' (A := B) (φ 0) (by rw [map_zero]), CommShift.isoZero'_hom_app,
      assoc, CommShift.isoZero_hom_app, pullbackShiftFunctorZero'_hom_app, map_comp,
      pullbackShiftFunctorZero'_inv_app]
    rfl
  commShiftIso_add _ _ := by
    ext
    simp only [PullbackShift.functor, comp_obj, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      CommShift.isoAdd_hom_app, map_comp, assoc]
    rw [F.commShiftIso_add' (φ.map_add _ _).symm]; rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [pullbackShiftFunctorAdd'_hom_app φ _ _ _ _ rfl _ _ _ rfl rfl rfl]; rw [pullbackShiftFunctorAdd'_inv_app φ _ _ _ _ rfl _ _ _ rfl rfl rfl]
    simp only [CommShift.isoAdd'_hom_app, assoc, map_comp, NatTrans.naturality_assoc,
      Iso.inv_hom_id_app_assoc]
    slice_rhs 9 10 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    simp only [comp_obj, id_comp]
    rw [← Functor.comp_map F (shiftFunctor D _)]; rw [← (F.commShiftIso _).hom.naturality_assoc]
    slice_rhs 4 5 => rw [← map_comp, (pullbackShiftIso C φ _ _ rfl).hom.naturality, map_comp]
    slice_rhs 3 4 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    simp only [comp_obj, id_comp, comp_map, assoc]
    slice_rhs 3 4 => rw [← map_comp, ← map_comp, Iso.inv_hom_id_app, map_id, map_id]
    rw [id_comp]; rw [assoc]; rw [assoc]
    rfl

中文:
实例 commShiftPullback
  签名: : (PullbackShift.functor φ F).交换Shift A where
  定义体: isoWhiskerRight (pullbackShiftIso C φ a (φ a) rfl) F ≪≫
    F.commShiftIso (φ a) ≪≫ isoWhiskerLeft _ (pullbackShiftIso D φ a (φ a) rfl).symm
  commShiftIso_zero := by
    ext
    dsimp
    simp only [F.commShiftIso_zero' (A := B) (φ 0) (by rw [map_zero]), CommShift.isoZero'_hom_app,
      assoc, CommShift.isoZero_hom_app, pullbackShiftFunctorZero'_hom_app, map_comp,
      pullbackShiftFunctorZero'_inv_app]
    rfl
  commShiftIso_add _ _ := by
    ext
    simp only [PullbackShift.functor, comp_obj, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      CommShift.isoAdd_hom_app, map_comp, assoc]
    rw [F.commShiftIso_add' (φ.map_add _ _).symm]; rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [pullbackShiftFunctorAdd'_hom_app φ _ _ _ _ rfl _ _ _ rfl rfl rfl]; rw [pullbackShiftFunctorAdd'_inv_app φ _ _ _ _ rfl _ _ _ rfl rfl rfl]
    simp only [CommShift.isoAdd'_hom_app, assoc, map_comp, NatTrans.naturality_assoc,
      Iso.inv_hom_id_app_assoc]
    slice_rhs 9 10 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    simp only [comp_obj, id_comp]
    rw [← Functor.comp_map F (shiftFunctor D _)]; rw [← (F.commShiftIso _).hom.naturality_assoc]
    slice_rhs 4 5 => rw [← map_comp, (pullbackShiftIso C φ _ _ rfl).hom.naturality, map_comp]
    slice_rhs 3 4 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    simp only [comp_obj, id_comp, comp_map, assoc]
    slice_rhs 3 4 => rw [← map_comp, ← map_comp, Iso.inv_hom_id_app, map_id, map_id]
    rw [id_comp]; rw [assoc]; rw [assoc]
    rfl

Depends on / 依赖: isoWhiskerRight, pullbackShiftIso
-/
instance commShiftPullback : (PullbackShift.functor φ F).CommShift A where
  commShiftIso a := isoWhiskerRight (pullbackShiftIso C φ a (φ a) rfl) F ≪≫
    F.commShiftIso (φ a) ≪≫ isoWhiskerLeft _ (pullbackShiftIso D φ a (φ a) rfl).symm
  commShiftIso_zero := by
    ext
    dsimp
    simp only [F.commShiftIso_zero' (A := B) (φ 0) (by rw [map_zero]), CommShift.isoZero'_hom_app,
      assoc, CommShift.isoZero_hom_app, pullbackShiftFunctorZero'_hom_app, map_comp,
      pullbackShiftFunctorZero'_inv_app]
    rfl
  commShiftIso_add _ _ := by
    ext
    simp only [PullbackShift.functor, comp_obj, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      CommShift.isoAdd_hom_app, map_comp, assoc]
    rw [F.commShiftIso_add' (φ.map_add _ _).symm]; rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [pullbackShiftFunctorAdd'_hom_app φ _ _ _ _ rfl _ _ _ rfl rfl rfl]; rw [pullbackShiftFunctorAdd'_inv_app φ _ _ _ _ rfl _ _ _ rfl rfl rfl]
    simp only [CommShift.isoAdd'_hom_app, assoc, map_comp, NatTrans.naturality_assoc,
      Iso.inv_hom_id_app_assoc]
    slice_rhs 9 10 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    simp only [comp_obj, id_comp]
    rw [← Functor.comp_map F (shiftFunctor D _)]; rw [← (F.commShiftIso _).hom.naturality_assoc]
    slice_rhs 4 5 => rw [← map_comp, (pullbackShiftIso C φ _ _ rfl).hom.naturality, map_comp]
    slice_rhs 3 4 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    simp only [comp_obj, id_comp, comp_map, assoc]
    slice_rhs 3 4 => rw [← map_comp, ← map_comp, Iso.inv_hom_id_app, map_id, map_id]
    rw [id_comp]; rw [assoc]; rw [assoc]
    rfl

/--
lemma `commShiftPullback_iso_eq` / 引理 `commShiftPullback_iso_eq`

English:
lemma commShiftPullback_iso_eq
  given: (a : A) (b : B) (h : b = φ a)
  proof: by
  obtain rfl : b = φ a := h
  rfl

中文:
引理 commShiftPullback_iso_eq
  条件: (a : A) (b : B) (h : b = φ a)
  证明: by
  obtain rfl : b = φ a := h
  rfl

Depends on / 依赖: PullbackShift
-/
lemma commShiftPullback_iso_eq (a : A) (b : B) (h : b = φ a) :
    (PullbackShift.functor φ F).commShiftIso a (C := PullbackShift C φ) (D := PullbackShift D φ) =
      isoWhiskerRight (pullbackShiftIso C φ a b h) F ≪≫ (F.commShiftIso b) ≪≫
        isoWhiskerLeft F (pullbackShiftIso D φ a b h).symm := by
  obtain rfl : b = φ a := h
  rfl

end Functor

namespace NatTrans

variable {F} {G : C ⥤ D} [G.CommShift B]

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Functor in
/--
Instance `commShiftPullback` / 实例 `commShiftPullback`

English:
instance commShiftPullback
  signature: (τ : F ⟶ G) [NatTrans.CommShift τ B]
  body: by
    ext
    dsimp [PullbackShift.natTrans]
    simp only [commShiftPullback_iso_eq φ _ _ _ rfl, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, comp_app, whiskerRight_app, whiskerLeft_app,
      assoc]
    rw [← τ.naturality_assoc]
    simp [← NatTrans.shift_app_comm_assoc]

中文:
实例 commShiftPullback
  签名: (τ : F ⟶ G) [自然变换.交换Shift τ B]
  定义体: by
    ext
    dsimp [PullbackShift.natTrans]
    simp only [commShiftPullback_iso_eq φ _ _ _ rfl, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, comp_app, whiskerRight_app, whiskerLeft_app,
      assoc]
    rw [← τ.naturality_assoc]
    simp [← NatTrans.shift_app_comm_assoc]

Depends on / 依赖: Iso.symm_hom, Iso.trans_hom, NatTrans, NatTrans.shift_app_comm_assoc, PullbackShift, PullbackShift.natTrans, commShiftPullback_iso_eq, comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom, natTrans, naturality_assoc, shift_app_comm_assoc, symm_hom, trans_hom, whiskerLeft_app, whiskerRight_app
-/
instance commShiftPullback (τ : F ⟶ G) [NatTrans.CommShift τ B] :
    NatTrans.CommShift (PullbackShift.natTrans φ τ) A where
  shift_comm _ := by
    ext
    dsimp [PullbackShift.natTrans]
    simp only [commShiftPullback_iso_eq φ _ _ _ rfl, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, comp_app, whiskerRight_app, whiskerLeft_app,
      assoc]
    rw [← τ.naturality_assoc]
    simp [← NatTrans.shift_app_comm_assoc]

variable (C) in
/--
Definition of `PullbackShift.natIsoId` / `PullbackShift.natIsoId` 的定义

English:
definition PullbackShift.natIsoId
  signature: : 𝟭 (PullbackShift C φ) ≅ PullbackShift.functor φ (𝟭 C)
  body: Iso.refl _

中文:
定义 PullbackShift.natIsoId
  签名: : 𝟭 (PullbackShift C φ) ≅ PullbackShift.functor φ (𝟭 C)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def PullbackShift.natIsoId : 𝟭 (PullbackShift C φ) ≅ PullbackShift.functor φ (𝟭 C) := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.CommShift (PullbackShift.natIsoId C φ).hom A
  body: by
    ext
    simp [PullbackShift.natIsoId, Functor.commShiftPullback_iso_eq]

中文:
实例 :
  签名: 自然变换.交换Shift (PullbackShift.natIsoId C φ).hom A
  定义体: by
    ext
    simp [PullbackShift.natIsoId, Functor.commShiftPullback_iso_eq]

Depends on / 依赖: Functor, Functor.commShiftPullback_iso_eq, PullbackShift, PullbackShift.natIsoId, commShiftPullback_iso_eq, natIsoId
-/
instance : NatTrans.CommShift (PullbackShift.natIsoId C φ).hom A where
  shift_comm _ := by
    ext
    simp [PullbackShift.natIsoId, Functor.commShiftPullback_iso_eq]

variable (F) {E : Type*} [Category* E] [HasShift E B] (G : D ⥤ E) [G.CommShift B]

/--
Definition of `PullbackShift.natIsoComp` / `PullbackShift.natIsoComp` 的定义

English:
definition PullbackShift.natIsoComp
  signature: : PullbackShift.functor φ (F ⋙ G) ≅
  body: Iso.refl _

中文:
定义 PullbackShift.natIsoComp
  签名: : PullbackShift.functor φ (F ⋙ G) ≅
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def PullbackShift.natIsoComp : PullbackShift.functor φ (F ⋙ G) ≅
    PullbackShift.functor φ F ⋙ PullbackShift.functor φ G := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
Suppose that `F` and `G` have `CommShift` structure by `B`. This expresses the
compatibility between two `CommShift` structures by `A` on (synonyms of) `F ⋙ G`:
the `CommShift` structure on `PullbackShift.functor (F ⋙ G) φ` (i.e the pullback of the
composition of `CommShift` structures by `B` on `F` and `G`), and that on
`PullbackShift.functor F φ ⋙ PullbackShift.functor G φ` (i.e. the one coming from
the composition of the pulled back `CommShift` structures on `F` and `G`).
-/
open CategoryTheory.Functor in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.CommShift (PullbackShift.natIsoComp φ F G).hom A
  body: by
    ext
    dsimp [PullbackShift.natIsoComp]
    simp only [commShiftPullback_iso_eq φ _ _ _ rfl, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, comp_app, comp_obj, whiskerRight_app, Functor.comp_map,
      commShiftIso_comp_hom_app, whiskerLeft_app, assoc, map_id, comp_id, map_comp, id_comp]
    dsimp [PullbackShift.functor]
    slice_rhs 3 4 => rw [← G.map_comp, Iso.inv_hom_id_app]
    simp

中文:
实例 :
  签名: 自然变换.交换Shift (PullbackShift.natIsoComp φ F G).hom A
  定义体: by
    ext
    dsimp [PullbackShift.natIsoComp]
    simp only [commShiftPullback_iso_eq φ _ _ _ rfl, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, comp_app, comp_obj, whiskerRight_app, Functor.comp_map,
      commShiftIso_comp_hom_app, whiskerLeft_app, assoc, map_id, comp_id, map_comp, id_comp]
    dsimp [PullbackShift.functor]
    slice_rhs 3 4 => rw [← G.map_comp, Iso.inv_hom_id_app]
    simp

Depends on / 依赖: Functor, Functor.comp_map, G.map_comp, Iso.inv_hom_id_app, Iso.symm_hom, Iso.trans_hom, PullbackShift, PullbackShift.functor, PullbackShift.natIsoComp, commShiftIso_comp_hom_app, commShiftPullback_iso_eq, comp_app, comp_id, comp_map, comp_obj, functor, id_comp, inv_hom_id_app, isoWhiskerLeft_hom, isoWhiskerRight_hom
-/
instance : NatTrans.CommShift (PullbackShift.natIsoComp φ F G).hom A where
  shift_comm _ := by
    ext
    dsimp [PullbackShift.natIsoComp]
    simp only [commShiftPullback_iso_eq φ _ _ _ rfl, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, comp_app, comp_obj, whiskerRight_app, Functor.comp_map,
      commShiftIso_comp_hom_app, whiskerLeft_app, assoc, map_id, comp_id, map_comp, id_comp]
    dsimp [PullbackShift.functor]
    slice_rhs 3 4 => rw [← G.map_comp, Iso.inv_hom_id_app]
    simp

end NatTrans

set_option backward.isDefEq.respectTransparency false in
/--
The adjunction `adj`, seen as an adjunction between `PullbackShift.functor F φ`
and `PullbackShift.functor G φ`.
-/
@[simps -isSimp]
/--
Definition of `PullbackShift.adjunction` / `PullbackShift.adjunction` 的定义

English:
definition PullbackShift.adjunction
  signature: {F} {G : D ⥤ C} (adj : F ⊣ G)
  body: (NatTrans.PullbackShift.natIsoId C φ).hom ≫
    PullbackShift.natTrans φ adj.unit ≫ (NatTrans.PullbackShift.natIsoComp φ F G).hom
  counit := (NatTrans.PullbackShift.natIsoComp φ G F).inv ≫
    PullbackShift.natTrans φ adj.counit ≫ (NatTrans.PullbackShift.natIsoId D φ).inv
  left_triangle_components _ := by
    simp [PullbackShift.natTrans, NatTrans.PullbackShift.natIsoComp,
      NatTrans.PullbackShift.natIsoId, PullbackShift.functor]
  right_triangle_components _ := by
    simp [PullbackShift.natTrans, NatTrans.PullbackShift.natIsoComp,
      NatTrans.PullbackShift.natIsoId, PullbackShift.functor]

中文:
定义 PullbackShift.adjunction
  签名: {F} {G : D ⥤ C} (adj : F ⊣ G)
  定义体: (NatTrans.PullbackShift.natIsoId C φ).hom ≫
    PullbackShift.natTrans φ adj.unit ≫ (NatTrans.PullbackShift.natIsoComp φ F G).hom
  counit := (NatTrans.PullbackShift.natIsoComp φ G F).inv ≫
    PullbackShift.natTrans φ adj.counit ≫ (NatTrans.PullbackShift.natIsoId D φ).inv
  left_triangle_components _ := by
    simp [PullbackShift.natTrans, NatTrans.PullbackShift.natIsoComp,
      NatTrans.PullbackShift.natIsoId, PullbackShift.functor]
  right_triangle_components _ := by
    simp [PullbackShift.natTrans, NatTrans.PullbackShift.natIsoComp,
      NatTrans.PullbackShift.natIsoId, PullbackShift.functor]

Depends on / 依赖: NatTrans, NatTrans.PullbackShift.natIsoId, PullbackShift, natIsoId
-/
def PullbackShift.adjunction {F} {G : D ⥤ C} (adj : F ⊣ G) :
    PullbackShift.functor φ F ⊣ PullbackShift.functor φ G where
  unit := (NatTrans.PullbackShift.natIsoId C φ).hom ≫
    PullbackShift.natTrans φ adj.unit ≫ (NatTrans.PullbackShift.natIsoComp φ F G).hom
  counit := (NatTrans.PullbackShift.natIsoComp φ G F).inv ≫
    PullbackShift.natTrans φ adj.counit ≫ (NatTrans.PullbackShift.natIsoId D φ).inv
  left_triangle_components _ := by
    simp [PullbackShift.natTrans, NatTrans.PullbackShift.natIsoComp,
      NatTrans.PullbackShift.natIsoId, PullbackShift.functor]
  right_triangle_components _ := by
    simp [PullbackShift.natTrans, NatTrans.PullbackShift.natIsoComp,
      NatTrans.PullbackShift.natIsoId, PullbackShift.functor]

namespace Adjunction

variable {F} {G : D ⥤ C} (adj : F ⊣ G) [G.CommShift B]

/--
Instance `commShiftPullback` / 实例 `commShiftPullback`

English:
instance commShiftPullback
  signature: [adj.CommShift B]
  body: by
    dsimp [PullbackShift.adjunction]
    infer_instance
  commShift_counit := by
    dsimp [PullbackShift.adjunction]
    infer_instance

中文:
实例 commShiftPullback
  签名: [adj.交换Shift B]
  定义体: by
    dsimp [PullbackShift.adjunction]
    infer_instance
  commShift_counit := by
    dsimp [PullbackShift.adjunction]
    infer_instance

Depends on / 依赖: PullbackShift, PullbackShift.adjunction, adjunction, commShift_counit, infer_instance
-/
instance commShiftPullback [adj.CommShift B] : (PullbackShift.adjunction φ adj).CommShift A where
  commShift_unit := by
    dsimp [PullbackShift.adjunction]
    infer_instance
  commShift_counit := by
    dsimp [PullbackShift.adjunction]
    infer_instance

end Adjunction

end CategoryTheory
