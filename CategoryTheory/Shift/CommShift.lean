/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.CategoryTheory.NatIso

/-!
# Functors which commute with shifts

Let `C` and `D` be two categories equipped with shifts by an additive monoid `A`. In this file,
we define the notion of functor `F : C ⥤ D` which "commutes" with these shifts. The associated
type class is `[F.CommShift A]`. The data consists of commutation isomorphisms
`F.commShiftIso a : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` for all `a : A`
which satisfy a compatibility with the addition and the zero. After this was formalised in Lean,
it was found that this definition is exactly the definition which appears in Jean-Louis
Verdier's thesis (I 1.2.3/1.2.4), although the language is different. (In Verdier's thesis,
the shift is not given by a monoidal functor `Discrete A ⥤ C ⥤ C`, but by a fibred
category `C ⥤ BA`, where `BA` is the category with one object, the endomorphisms of which
identify to `A`. The choice of a cleavage for this fibered category gives the individual
shift functors.)

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Category

namespace Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  (F : C ⥤ D) (G : D ⥤ E) (A B : Type*) [AddMonoid A] [AddCommMonoid B]
  [HasShift C A] [HasShift D A] [HasShift E A]
  [HasShift C B] [HasShift D B]

namespace CommShift

/-- For any functor `F : C ⥤ D`, this is the obvious isomorphism
`shiftFunctor C (0 : A) ⋙ F ≅ F ⋙ shiftFunctor D (0 : A)` deduced from the
isomorphisms `shiftFunctorZero` on both categories `C` and `D`. -/
@[simps!]
/--
Definition of `isoZero` / `isoZero` 的定义

English:
definition isoZero
  signature: : shiftFunctor C (0 : A) ⋙ F ≅ F ⋙ shiftFunctor D (0 : A)
  body: isoWhiskerRight (shiftFunctorZero C A) F ≪≫ F.leftUnitor ≪≫
     F.rightUnitor.symm ≪≫ isoWhiskerLeft F (shiftFunctorZero D A).symm

中文:
定义 isoZero
  签名: : shiftFunctor C (0 : A) ⋙ F ≅ F ⋙ shiftFunctor D (0 : A)
  定义体: isoWhiskerRight (shiftFunctorZero C A) F ≪≫ F.leftUnitor ≪≫
     F.rightUnitor.symm ≪≫ isoWhiskerLeft F (shiftFunctorZero D A).symm

Depends on / 依赖: F.leftUnitor, F.rightUnitor.symm, isoWhiskerLeft, isoWhiskerRight, leftUnitor, rightUnitor, shiftFunctorZero
-/
noncomputable def isoZero : shiftFunctor C (0 : A) ⋙ F ≅ F ⋙ shiftFunctor D (0 : A) :=
  isoWhiskerRight (shiftFunctorZero C A) F ≪≫ F.leftUnitor ≪≫
     F.rightUnitor.symm ≪≫ isoWhiskerLeft F (shiftFunctorZero D A).symm

/-- For any functor `F : C ⥤ D` and any `a` in `A` such that `a = 0`,
this is the obvious isomorphism `shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` deduced from the
isomorphisms `shiftFunctorZero'` on both categories `C` and `D`. -/
@[simps!]
/--
Definition of `isoZero'` / `isoZero'` 的定义

English:
definition isoZero'
  signature: (a : A) (ha : a = 0)
  body: isoWhiskerRight (shiftFunctorZero' C a ha) F ≪≫ F.leftUnitor ≪≫
     F.rightUnitor.symm ≪≫ isoWhiskerLeft F (shiftFunctorZero' D a ha).symm

@[simp]

中文:
定义 isoZero'
  签名: (a : A) (ha : a = 0)
  定义体: isoWhiskerRight (shiftFunctorZero' C a ha) F ≪≫ F.leftUnitor ≪≫
     F.rightUnitor.symm ≪≫ isoWhiskerLeft F (shiftFunctorZero' D a ha).symm

@[simp]

Depends on / 依赖: F.leftUnitor, F.rightUnitor.symm, isoWhiskerLeft, isoWhiskerRight, leftUnitor, rightUnitor, shiftFunctorZero
-/
noncomputable def isoZero' (a : A) (ha : a = 0) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  isoWhiskerRight (shiftFunctorZero' C a ha) F ≪≫ F.leftUnitor ≪≫
     F.rightUnitor.symm ≪≫ isoWhiskerLeft F (shiftFunctorZero' D a ha).symm

@[simp]
/--
lemma `isoZero'_eq_isoZero` / 引理 `isoZero'_eq_isoZero`

English:
lemma isoZero'_eq_isoZero
  statement: isoZero' F A 0 rfl = isoZero F A
  proof: by
  ext; simp [isoZero', shiftFunctorZero']

中文:
引理 isoZero'_eq_isoZero
  结论: isoZero' F A 0 rfl = isoZero F A
  证明: by
  ext; simp [isoZero', shiftFunctorZero']
-/
lemma isoZero'_eq_isoZero : isoZero' F A 0 rfl = isoZero F A := by
  ext; simp [isoZero', shiftFunctorZero']

variable {F A}

/-- If a functor `F : C ⥤ D` is equipped with "commutation isomorphisms" with the
shifts by `a` and `b`, then there is a commutation isomorphism with the shift by `c` when
`a + b = c`. -/
@[simps!]
/--
Definition of `isoAdd'` / `isoAdd'` 的定义

English:
definition isoAdd'
  signature: {a b c : A} (h : a + b = c)
  body: isoWhiskerRight (shiftFunctorAdd' C _ _ _ h) F ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ e₂ ≪≫ (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e₁ _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (shiftFunctorAdd' D _ _ _ h).symm

中文:
定义 isoAdd'
  签名: {a b c : A} (h : a + b = c)
  定义体: isoWhiskerRight (shiftFunctorAdd' C _ _ _ h) F ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ e₂ ≪≫ (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e₁ _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (shiftFunctorAdd' D _ _ _ h).symm

Depends on / 依赖: Functor, Functor.associator, associator, isoWhiskerLeft, isoWhiskerRight, shiftFunctorAdd
-/
noncomputable def isoAdd' {a b c : A} (h : a + b = c)
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) :
    shiftFunctor C c ⋙ F ≅ F ⋙ shiftFunctor D c :=
  isoWhiskerRight (shiftFunctorAdd' C _ _ _ h) F ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ e₂ ≪≫ (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e₁ _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (shiftFunctorAdd' D _ _ _ h).symm

/--
Definition of `isoAdd` / `isoAdd` 的定义

English:
definition isoAdd
  signature: {a b : A}
  body: CommShift.isoAdd' rfl e₁ e₂

@[simp]

中文:
定义 isoAdd
  签名: {a b : A}
  定义体: CommShift.isoAdd' rfl e₁ e₂

@[simp]

Depends on / 依赖: CommShift, CommShift.isoAdd, isoAdd
-/
noncomputable def isoAdd {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) :
    shiftFunctor C (a + b) ⋙ F ≅ F ⋙ shiftFunctor D (a + b) :=
  CommShift.isoAdd' rfl e₁ e₂

@[simp]
/--
lemma `isoAdd_hom_app` / 引理 `isoAdd_hom_app`

English:
lemma isoAdd_hom_app
  statement: {a b : A}
  proof: by
  simp only [isoAdd, isoAdd'_hom_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

@[simp]

中文:
引理 isoAdd_hom_app
  结论: {a b : A}
  证明: by
  simp only [isoAdd, isoAdd'_hom_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

@[simp]

Depends on / 依赖: _eq_shiftFunctorAdd, _hom_app, isoAdd, shiftFunctorAdd
-/
lemma isoAdd_hom_app {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) :
      (CommShift.isoAdd e₁ e₂).hom.app X =
        F.map ((shiftFunctorAdd C a b).hom.app X) ≫ e₂.hom.app ((shiftFunctor C a).obj X) ≫
          (shiftFunctor D b).map (e₁.hom.app X) ≫ (shiftFunctorAdd D a b).inv.app (F.obj X) := by
  simp only [isoAdd, isoAdd'_hom_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

@[simp]
/--
lemma `isoAdd_inv_app` / 引理 `isoAdd_inv_app`

English:
lemma isoAdd_inv_app
  statement: {a b : A}
  proof: by
  simp only [isoAdd, isoAdd'_inv_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

中文:
引理 isoAdd_inv_app
  结论: {a b : A}
  证明: by
  simp only [isoAdd, isoAdd'_inv_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

Depends on / 依赖: _eq_shiftFunctorAdd, _inv_app, isoAdd, shiftFunctorAdd
-/
lemma isoAdd_inv_app {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) :
      (CommShift.isoAdd e₁ e₂).inv.app X = (shiftFunctorAdd D a b).hom.app (F.obj X) ≫
        (shiftFunctor D b).map (e₁.inv.app X) ≫ e₂.inv.app ((shiftFunctor C a).obj X) ≫
        F.map ((shiftFunctorAdd C a b).inv.app X) := by
  simp only [isoAdd, isoAdd'_inv_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

/--
lemma `isoAdd'_isoZero` / 引理 `isoAdd'_isoZero`

English:
lemma isoAdd'_isoZero
  statement: {a : A}
  proof: by
  ext X
  simp [shiftFunctorAdd'_add_zero_hom_app, ← Functor.map_comp_assoc,
    shiftFunctorAdd'_add_zero_inv_app]

中文:
引理 isoAdd'_isoZero
  结论: {a : A}
  证明: by
  ext X
  simp [shiftFunctorAdd'_add_zero_hom_app, ← Functor.map_comp_assoc,
    shiftFunctorAdd'_add_zero_inv_app]
-/
lemma isoAdd'_isoZero {a : A}
    (e : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a) :
    isoAdd' (add_zero a) e (isoZero F A) = e := by
  ext X
  simp [shiftFunctorAdd'_add_zero_hom_app, ← Functor.map_comp_assoc,
    shiftFunctorAdd'_add_zero_inv_app]

/--
lemma `isoZero_isoAdd'_` / 引理 `isoZero_isoAdd'_`

English:
lemma isoZero_isoAdd'_
  statement: {a : A}
  proof: by
  ext X
  have := e.hom.naturality ((shiftFunctorZero C A).inv.app X)
  dsimp at this
  simp [shiftFunctorAdd'_zero_add_hom_app,
    shiftFunctorAdd'_zero_add_inv_app, ← map_comp,
    reassoc_of% this]

中文:
引理 isoZero_isoAdd'_
  结论: {a : A}
  证明: by
  ext X
  have := e.hom.naturality ((shiftFunctorZero C A).inv.app X)
  dsimp at this
  simp [shiftFunctorAdd'_zero_add_hom_app,
    shiftFunctorAdd'_zero_add_inv_app, ← map_comp,
    reassoc_of% this]

Depends on / 依赖: _zero_add_hom_app, _zero_add_inv_app, e.hom.naturality, inv.app, map_comp, naturality, reassoc_of, shiftFunctorAdd, shiftFunctorZero
-/
lemma isoZero_isoAdd'_ {a : A}
    (e : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a) :
    isoAdd' (zero_add a) (isoZero F A) e = e := by
  ext X
  have := e.hom.naturality ((shiftFunctorZero C A).inv.app X)
  dsimp at this
  simp [shiftFunctorAdd'_zero_add_hom_app,
    shiftFunctorAdd'_zero_add_inv_app, ← map_comp,
    reassoc_of% this]

/--
lemma `isoAdd'_assoc` / 引理 `isoAdd'_assoc`

English:
lemma isoAdd'_assoc
  statement: {a b c ab bc abc : A}
  proof: by
  ext X
  have := NatTrans.naturality_2 ec.hom ((shiftFunctorAdd' C a b ab hab).app X)
  dsimp at this ⊢
  simp only [isoAdd'_hom_app, Category.assoc]
  rw [← NatTrans.naturality_assoc]; rw [← this]; rw [Category.assoc]; rw [← F.map_comp_assoc]; rw [shiftFunctorAdd'_assoc_hom_app a b c ab bc abc hab hbc h]; rw [Functor.map_comp_assoc]; rw [Category.assoc]
  simp_rw [← Functor.map_comp_assoc]
  simp [shiftFunctorAdd'_assoc_inv_app a b c ab bc abc hab hbc h]

中文:
引理 isoAdd'_assoc
  结论: {a b c ab bc abc : A}
  证明: by
  ext X
  have := NatTrans.naturality_2 ec.hom ((shiftFunctorAdd' C a b ab hab).app X)
  dsimp at this ⊢
  simp only [isoAdd'_hom_app, Category.assoc]
  rw [← NatTrans.naturality_assoc]; rw [← this]; rw [Category.assoc]; rw [← F.map_comp_assoc]; rw [shiftFunctorAdd'_assoc_hom_app a b c ab bc abc hab hbc h]; rw [Functor.map_comp_assoc]; rw [Category.assoc]
  simp_rw [← Functor.map_comp_assoc]
  simp [shiftFunctorAdd'_assoc_inv_app a b c ab bc abc hab hbc h]
-/
lemma isoAdd'_assoc {a b c ab bc abc : A}
    (ea : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (eb : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b)
    (ec : shiftFunctor C c ⋙ F ≅ F ⋙ shiftFunctor D c)
    (hab : a + b = ab) (hbc : b + c = bc) (h : a + b + c = abc) :
    isoAdd' (show ab + c = abc by rwa [← hab]) (isoAdd' hab ea eb) ec =
      isoAdd' (show a + bc = abc by grind) ea (isoAdd' hbc eb ec) := by
  ext X
  have := NatTrans.naturality_2 ec.hom ((shiftFunctorAdd' C a b ab hab).app X)
  dsimp at this ⊢
  simp only [isoAdd'_hom_app, Category.assoc]
  rw [← NatTrans.naturality_assoc]; rw [← this]; rw [Category.assoc]; rw [← F.map_comp_assoc]; rw [shiftFunctorAdd'_assoc_hom_app a b c ab bc abc hab hbc h]; rw [Functor.map_comp_assoc]; rw [Category.assoc]
  simp_rw [← Functor.map_comp_assoc]
  simp [shiftFunctorAdd'_assoc_inv_app a b c ab bc abc hab hbc h]

end CommShift

/--
Definition of `CommShift` / `CommShift` 的定义

English:
class CommShift
  parameters: (F : C ⥤ D) (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]
  axioms and operations (3):
    - commShiftIso((F) (a : A)) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
    - commShiftIso_zero((F) (A)) : commShiftIso 0 = CommShift.isoZero F A  [default: by cat_disch]
    - commShiftIso_add((F) (a b : A)) : commShiftIso (a + b) = CommShift.isoAdd (commShiftIso a) (commShiftIso b)  [default: by cat_disch]

中文:
类 交换Shift
  参数: (F : C ⥤ D) (A : 类型) [加法幺半群 A] [有Shift C A] [有Shift D A]
  公理与运算 (3 个):
    - commShiftIso((F) (a : A)) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
    - commShiftIso_zero((F) (A)) : commShiftIso 0 = 交换Shift.isoZero F A  [默认: by cat_disch]
    - commShiftIso_add((F) (a b : A)) : commShiftIso (a + b) = 交换Shift.isoAdd (commShiftIso a) (commShiftIso b)  [默认: by cat_disch]

Depends on / 依赖: CommShift, CommShift.isoAdd, cat_disch, commShiftIso, commShiftIso_add, isoAdd
-/
class CommShift (F : C ⥤ D) (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] where
  /-- The commutation isomorphisms for all `a`-shifts this functor is equipped with -/
  commShiftIso (F) (a : A) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
  commShiftIso_zero (F) (A) : commShiftIso 0 = CommShift.isoZero F A := by cat_disch
  commShiftIso_add (F) (a b : A) :
    commShiftIso (a + b) = CommShift.isoAdd (commShiftIso a) (commShiftIso b) := by cat_disch

variable {A}

export CommShift (commShiftIso commShiftIso_zero commShiftIso_add)

section

variable [F.CommShift A]

-- Note: The following two lemmas are introduced in order to have more proofs work `by simp`.
-- Indeed, `simp only [(F.commShiftIso a).hom.naturality f]` would almost never work because
-- of the compositions of functors which appear in both the source and target of
-- `F.commShiftIso a`. Otherwise, we would be forced to use `erw [NatTrans.naturality]`.

@[reassoc (attr := simp)]
/--
lemma `commShiftIso_hom_naturality` / 引理 `commShiftIso_hom_naturality`

English:
lemma commShiftIso_hom_naturality
  given: {X Y : C} (f : X ⟶ Y) (a : A)
  proof: (F.commShiftIso a).hom.naturality f

@[reassoc (attr := simp)]

中文:
引理 commShiftIso_hom_naturality
  条件: {X Y : C} (f : X ⟶ Y) (a : A)
  证明: (F.commShiftIso a).hom.naturality f

@[reassoc (attr := simp)]

Depends on / 依赖: F.commShiftIso, commShiftIso, hom.naturality, naturality
-/
lemma commShiftIso_hom_naturality {X Y : C} (f : X ⟶ Y) (a : A) :
    dsimp% F.map (f⟦a⟧') ≫ (F.commShiftIso a).hom.app Y =
      (F.commShiftIso a).hom.app X ≫ (F.map f)⟦a⟧' :=
  (F.commShiftIso a).hom.naturality f

@[reassoc (attr := simp)]
/--
lemma `commShiftIso_inv_naturality` / 引理 `commShiftIso_inv_naturality`

English:
lemma commShiftIso_inv_naturality
  given: {X Y : C} (f : X ⟶ Y) (a : A)
  proof: (F.commShiftIso a).inv.naturality f

中文:
引理 commShiftIso_inv_naturality
  条件: {X Y : C} (f : X ⟶ Y) (a : A)
  证明: (F.commShiftIso a).inv.naturality f

Depends on / 依赖: F.commShiftIso, commShiftIso, inv.naturality, naturality
-/
lemma commShiftIso_inv_naturality {X Y : C} (f : X ⟶ Y) (a : A) :
    dsimp% (F.map f)⟦a⟧' ≫ (F.commShiftIso a).inv.app Y =
      (F.commShiftIso a).inv.app X ≫ F.map (f⟦a⟧') :=
  (F.commShiftIso a).inv.naturality f

variable (A) in
set_option linter.docPrime false in
/--
lemma `commShiftIso_zero'` / 引理 `commShiftIso_zero'`

English:
lemma commShiftIso_zero'
  given: (a : A) (h : a = 0)
  proof: by
  subst h; rw [CommShift.isoZero'_eq_isoZero, commShiftIso_zero]

中文:
引理 commShiftIso_zero'
  条件: (a : A) (h : a = 0)
  证明: by
  subst h; rw [CommShift.isoZero'_eq_isoZero, commShiftIso_zero]

Depends on / 依赖: CommShift, CommShift.isoZero, _eq_isoZero, commShiftIso_zero, isoZero
-/
lemma commShiftIso_zero' (a : A) (h : a = 0) :
    F.commShiftIso a = CommShift.isoZero' F A a h := by
  subst h; rw [CommShift.isoZero'_eq_isoZero, commShiftIso_zero]

/--
lemma `commShiftIso_add'` / 引理 `commShiftIso_add'`

English:
lemma commShiftIso_add'
  given: {a b c : A} (h : a + b = c)
  proof: by
  subst h
  simp only [commShiftIso_add, CommShift.isoAdd]

中文:
引理 commShiftIso_add'
  条件: {a b c : A} (h : a + b = c)
  证明: by
  subst h
  simp only [commShiftIso_add, CommShift.isoAdd]

Depends on / 依赖: CommShift, CommShift.isoAdd, commShiftIso_add, isoAdd
-/
lemma commShiftIso_add' {a b c : A} (h : a + b = c) :
    F.commShiftIso c = CommShift.isoAdd' h (F.commShiftIso a) (F.commShiftIso b) := by
  subst h
  simp only [commShiftIso_add, CommShift.isoAdd]

end

namespace CommShift

variable (C) in
@[simps! -isSimp commShiftIso_hom_app commShiftIso_inv_app]
/--
Instance `id` / 实例 `id`

English:
instance id
  signature: : CommShift (𝟭 C) A where
  body: fun _ => rightUnitor _ ≪≫ (leftUnitor _).symm

@[simps! -isSimp commShiftIso_hom_app commShiftIso_inv_app]

中文:
实例 id
  签名: : 交换Shift (𝟭 C) A where
  定义体: fun _ => rightUnitor _ ≪≫ (leftUnitor _).symm

@[simps! -isSimp commShiftIso_hom_app commShiftIso_inv_app]

Depends on / 依赖: leftUnitor, rightUnitor
-/
instance id : CommShift (𝟭 C) A where
  commShiftIso := fun _ => rightUnitor _ ≪≫ (leftUnitor _).symm

@[simps! -isSimp commShiftIso_hom_app commShiftIso_inv_app]
/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: [F.CommShift A] [G.CommShift A]
  body: (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.commShiftIso a) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (G.commShiftIso a) ≪≫
    (Functor.associator _ _ _).symm
  commShiftIso_zero := by
    ext X
    dsimp
    simp only [id_comp, comp_id, commShiftIso_zero, isoZero_hom_app, ← Functor.map_comp_assoc,
      assoc, Iso.inv_hom_id_app, id_obj, comp_map, comp_obj]
  commShiftIso_add := fun a b => by
    ext X
    dsimp
    simp only [commShiftIso_add, isoAdd_hom_app]
    dsimp
    simp only [comp_id, id_comp, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, comp_obj]
    simp only [map_comp, assoc, commShiftIso_hom_naturality_assoc]

中文:
实例 comp
  签名: [F.交换Shift A] [G.交换Shift A]
  定义体: (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.commShiftIso a) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (G.commShiftIso a) ≪≫
    (Functor.associator _ _ _).symm
  commShiftIso_zero := by
    ext X
    dsimp
    simp only [id_comp, comp_id, commShiftIso_zero, isoZero_hom_app, ← Functor.map_comp_assoc,
      assoc, Iso.inv_hom_id_app, id_obj, comp_map, comp_obj]
  commShiftIso_add := fun a b => by
    ext X
    dsimp
    simp only [commShiftIso_add, isoAdd_hom_app]
    dsimp
    simp only [comp_id, id_comp, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, comp_obj]
    simp only [map_comp, assoc, commShiftIso_hom_naturality_assoc]

Depends on / 依赖: F.commShiftIso, Functor, Functor.associator, associator, commShiftIso, isoWhiskerRight
-/
instance comp [F.CommShift A] [G.CommShift A] : (F ⋙ G).CommShift A where
  commShiftIso a := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.commShiftIso a) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (G.commShiftIso a) ≪≫
    (Functor.associator _ _ _).symm
  commShiftIso_zero := by
    ext X
    dsimp
    simp only [id_comp, comp_id, commShiftIso_zero, isoZero_hom_app, ← Functor.map_comp_assoc,
      assoc, Iso.inv_hom_id_app, id_obj, comp_map, comp_obj]
  commShiftIso_add := fun a b => by
    ext X
    dsimp
    simp only [commShiftIso_add, isoAdd_hom_app]
    dsimp
    simp only [comp_id, id_comp, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, comp_obj]
    simp only [map_comp, assoc, commShiftIso_hom_naturality_assoc]

end CommShift

alias commShiftIso_id_hom_app := CommShift.id_commShiftIso_hom_app
alias commShiftIso_id_inv_app := CommShift.id_commShiftIso_inv_app
alias commShiftIso_comp_hom_app := CommShift.comp_commShiftIso_hom_app
alias commShiftIso_comp_inv_app := CommShift.comp_commShiftIso_inv_app

attribute [simp] commShiftIso_id_hom_app commShiftIso_id_inv_app

variable {B}

/--
lemma `map_shiftFunctorComm_hom_app` / 引理 `map_shiftFunctorComm_hom_app`

English:
lemma map_shiftFunctorComm_hom_app
  given: [F.CommShift B] (X : C) (a b : B)
  proof: by
  have eq := NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add a b)) X
  simp only [comp_obj, CommShift.isoAdd_hom_app,
    ← cancel_epi (F.map ((shiftFunctorAdd C a b).inv.app X)),
    ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp] at eq
  simp only [shiftFunctorComm_eq D a b _ rfl]
  dsimp
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, Category.assoc,
    ← reassoc_of% eq, shiftFunctorComm_eq C a b _ rfl]
  dsimp
  rw [Functor.map_comp]
  simp only [NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add' (add_comm b a))) X,
    CommShift.isoAdd'_hom_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp, comp_obj, Category.comp_id]

@[simp, reassoc]

中文:
引理 map_shiftFunctorComm_hom_app
  条件: [F.交换Shift B] (X : C) (a b : B)
  证明: by
  have eq := NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add a b)) X
  simp only [comp_obj, CommShift.isoAdd_hom_app,
    ← cancel_epi (F.map ((shiftFunctorAdd C a b).inv.app X)),
    ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp] at eq
  simp only [shiftFunctorComm_eq D a b _ rfl]
  dsimp
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, Category.assoc,
    ← reassoc_of% eq, shiftFunctorComm_eq C a b _ rfl]
  dsimp
  rw [Functor.map_comp]
  simp only [NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add' (add_comm b a))) X,
    CommShift.isoAdd'_hom_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp, comp_obj, Category.comp_id]

@[simp, reassoc]

Depends on / 依赖: Category, Category.assoc, Category.id_comp, CommShift, CommShift.isoAdd_hom_app, F.commShiftIso_add, F.map, F.map_comp_assoc, F.map_id, Functor, Functor.map_comp, Iso.hom, Iso.inv_hom_id_app, NatTrans, NatTrans.congr_app, _eq_shiftFunctorAdd, cancel_epi, commShiftIso_add, comp_obj, congr_app
-/
lemma map_shiftFunctorComm_hom_app [F.CommShift B] (X : C) (a b : B) :
    F.map ((shiftFunctorComm C a b).hom.app X) = (F.commShiftIso b).hom.app (X⟦a⟧) ≫
      ((F.commShiftIso a).hom.app X)⟦b⟧' ≫ (shiftFunctorComm D a b).hom.app (F.obj X) ≫
      ((F.commShiftIso b).inv.app X)⟦a⟧' ≫ (F.commShiftIso a).inv.app (X⟦b⟧) := by
  have eq := NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add a b)) X
  simp only [comp_obj, CommShift.isoAdd_hom_app,
    ← cancel_epi (F.map ((shiftFunctorAdd C a b).inv.app X)),
    ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp] at eq
  simp only [shiftFunctorComm_eq D a b _ rfl]
  dsimp
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, Category.assoc,
    ← reassoc_of% eq, shiftFunctorComm_eq C a b _ rfl]
  dsimp
  rw [Functor.map_comp]
  simp only [NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add' (add_comm b a))) X,
    CommShift.isoAdd'_hom_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp, comp_obj, Category.comp_id]

@[simp, reassoc]
/--
lemma `map_shiftFunctorCompIsoId_hom_app` / 引理 `map_shiftFunctorCompIsoId_hom_app`

English:
lemma map_shiftFunctorCompIsoId_hom_app
  given: [F.CommShift A] (X : C) (a b : A) (h : a + b = 0)
  proof: by
  dsimp [shiftFunctorCompIsoId]
  have eq := NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add' h)) X
  simp only [commShiftIso_zero, comp_obj, CommShift.isoZero_hom_app,
    CommShift.isoAdd'_hom_app] at eq
  rw [← cancel_epi (F.map ((shiftFunctorAdd' C a b 0 h).hom.app X))]; rw [← reassoc_of% eq]; rw [F.map_comp]
  simp only [Iso.inv_hom_id_app, id_obj, Category.comp_id, ← F.map_comp_assoc, Iso.hom_inv_id_app,
    F.map_id, Category.id_comp]

@[simp, reassoc]

中文:
引理 map_shiftFunctorCompIsoId_hom_app
  条件: [F.交换Shift A] (X : C) (a b : A) (h : a + b = 0)
  证明: by
  dsimp [shiftFunctorCompIsoId]
  have eq := NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add' h)) X
  simp only [commShiftIso_zero, comp_obj, CommShift.isoZero_hom_app,
    CommShift.isoAdd'_hom_app] at eq
  rw [← cancel_epi (F.map ((shiftFunctorAdd' C a b 0 h).hom.app X))]; rw [← reassoc_of% eq]; rw [F.map_comp]
  simp only [Iso.inv_hom_id_app, id_obj, Category.comp_id, ← F.map_comp_assoc, Iso.hom_inv_id_app,
    F.map_id, Category.id_comp]

@[simp, reassoc]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, CommShift, CommShift.isoAdd, CommShift.isoZero_hom_app, F.commShiftIso_add, F.map, F.map_comp, F.map_comp_assoc, F.map_id, Iso.hom, Iso.hom_inv_id_app, Iso.inv_hom_id_app, NatTrans, NatTrans.congr_app, _hom_app, cancel_epi, commShiftIso_add, commShiftIso_zero
-/
lemma map_shiftFunctorCompIsoId_hom_app [F.CommShift A] (X : C) (a b : A) (h : a + b = 0) :
    F.map ((shiftFunctorCompIsoId C a b h).hom.app X) =
      (F.commShiftIso b).hom.app (X⟦a⟧) ≫ ((F.commShiftIso a).hom.app X)⟦b⟧' ≫
        (shiftFunctorCompIsoId D a b h).hom.app (F.obj X) := by
  dsimp [shiftFunctorCompIsoId]
  have eq := NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add' h)) X
  simp only [commShiftIso_zero, comp_obj, CommShift.isoZero_hom_app,
    CommShift.isoAdd'_hom_app] at eq
  rw [← cancel_epi (F.map ((shiftFunctorAdd' C a b 0 h).hom.app X))]; rw [← reassoc_of% eq]; rw [F.map_comp]
  simp only [Iso.inv_hom_id_app, id_obj, Category.comp_id, ← F.map_comp_assoc, Iso.hom_inv_id_app,
    F.map_id, Category.id_comp]

@[simp, reassoc]
/--
lemma `map_shiftFunctorCompIsoId_inv_app` / 引理 `map_shiftFunctorCompIsoId_inv_app`

English:
lemma map_shiftFunctorCompIsoId_inv_app
  given: [F.CommShift A] (X : C) (a b : A) (h : a + b = 0)
  proof: by
  rw [← cancel_epi (F.map ((shiftFunctorCompIsoId C a b h).hom.app X))]; rw [← F.map_comp]; rw [Iso.hom_inv_id_app]; rw [F.map_id]; rw [map_shiftFunctorCompIsoId_hom_app]
  simp only [comp_obj, id_obj, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]

中文:
引理 map_shiftFunctorCompIsoId_inv_app
  条件: [F.交换Shift A] (X : C) (a b : A) (h : a + b = 0)
  证明: by
  rw [← cancel_epi (F.map ((shiftFunctorCompIsoId C a b h).hom.app X))]; rw [← F.map_comp]; rw [Iso.hom_inv_id_app]; rw [F.map_id]; rw [map_shiftFunctorCompIsoId_hom_app]
  simp only [comp_obj, id_obj, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]

Depends on / 依赖: Category, Category.assoc, Category.id_comp, F.map, F.map_comp, F.map_id, Functor, Functor.map_comp_assoc, Functor.map_id, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, cancel_epi, comp_obj, hom.app, hom_inv_id_app, hom_inv_id_app_assoc, id_comp, id_obj, map_comp, map_comp_assoc
-/
lemma map_shiftFunctorCompIsoId_inv_app [F.CommShift A] (X : C) (a b : A) (h : a + b = 0) :
    F.map ((shiftFunctorCompIsoId C a b h).inv.app X) =
      (shiftFunctorCompIsoId D a b h).inv.app (F.obj X) ≫
        ((F.commShiftIso a).inv.app X)⟦b⟧' ≫ (F.commShiftIso b).inv.app (X⟦a⟧) := by
  rw [← cancel_epi (F.map ((shiftFunctorCompIsoId C a b h).hom.app X))]; rw [← F.map_comp]; rw [Iso.hom_inv_id_app]; rw [F.map_id]; rw [map_shiftFunctorCompIsoId_hom_app]
  simp only [comp_obj, id_obj, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]

end Functor

namespace NatTrans

variable {C D E J : Type*} [Category* C] [Category* D] [Category* E] [Category* J]
  {F₁ F₂ F₃ : C ⥤ D} (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) (e : F₁ ≅ F₂)
    (G G' : D ⥤ E) (τ'' : G ⟶ G') (H : E ⥤ J)
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A] [HasShift J A]
  [F₁.CommShift A] [F₂.CommShift A] [F₃.CommShift A]
    [G.CommShift A] [G'.CommShift A] [H.CommShift A]

variable {A} in
/--
Definition of `CommShiftCore` / `CommShiftCore` 的定义

English:
structure CommShiftCore
  parameters: (a : A)
  axioms and operations (1):
    - shift_comm : (F₁.commShiftIso a).hom ≫ Functor.whiskerRight τ _ = Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom

中文:
结构 交换ShiftCore
  参数: (a : A)
  公理与运算 (1 个):
    - shift_comm : (F₁.commShiftIso a).hom ≫ 函子.whiskerRight τ _ = 函子.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom
-/
structure CommShiftCore (a : A) : Prop where
  shift_comm : (F₁.commShiftIso a).hom ≫ Functor.whiskerRight τ _ =
    Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom

namespace CommShiftCore

attribute [reassoc] shift_comm

section

variable {A} {a : A} (hτ : CommShiftCore τ a)

include hτ

@[reassoc]
/--
lemma `shift_app_comm` / 引理 `shift_app_comm`

English:
lemma shift_app_comm
  given: (X : C)
  proof: congr_app hτ.shift_comm X

@[reassoc]

中文:
引理 shift_app_comm
  条件: (X : C)
  证明: congr_app hτ.shift_comm X

@[reassoc]

Depends on / 依赖: congr_app, shift_comm
-/
lemma shift_app_comm (X : C) :
    (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' =
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X :=
  congr_app hτ.shift_comm X

@[reassoc]
/--
lemma `shift_app` / 引理 `shift_app`

English:
lemma shift_app
  given: (X : C)
  proof: by
  rw [← hτ.shift_app_comm]; rw [Iso.inv_hom_id_app_assoc]

@[reassoc]

中文:
引理 shift_app
  条件: (X : C)
  证明: by
  rw [← hτ.shift_app_comm]; rw [Iso.inv_hom_id_app_assoc]

@[reassoc]

Depends on / 依赖: Iso.inv_hom_id_app_assoc, inv_hom_id_app_assoc, shift_app_comm
-/
lemma shift_app (X : C) :
    (τ.app X)⟦a⟧' = (F₁.commShiftIso a).inv.app X ≫
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X := by
  rw [← hτ.shift_app_comm]; rw [Iso.inv_hom_id_app_assoc]

@[reassoc]
/--
lemma `app_shift` / 引理 `app_shift`

English:
lemma app_shift
  given: (X : C)
  proof: by
  simp [hτ.shift_app_comm_assoc τ X]

中文:
引理 app_shift
  条件: (X : C)
  证明: by
  simp [hτ.shift_app_comm_assoc τ X]

Depends on / 依赖: shift_app_comm_assoc
-/
lemma app_shift (X : C) :
    τ.app (X⟦a⟧) = (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' ≫
      (F₂.commShiftIso a).inv.app X := by
  simp [hτ.shift_app_comm_assoc τ X]

end

variable {τ}

/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  statement: CommShiftCore τ (0 : A) where
  proof: by
    ext X
    simp [Functor.commShiftIso_zero, ← NatTrans.naturality]

中文:
引理 zero
  结论: 交换ShiftCore τ (0 : A) where
  证明: by
    ext X
    simp [Functor.commShiftIso_zero, ← NatTrans.naturality]

Depends on / 依赖: Functor, Functor.commShiftIso_zero, NatTrans, NatTrans.naturality, commShiftIso_zero, naturality
-/
lemma zero : CommShiftCore τ (0 : A) where
  shift_comm := by
    ext X
    simp [Functor.commShiftIso_zero, ← NatTrans.naturality]

variable {A}

/--
lemma `add` / 引理 `add`

English:
lemma add
  given: {a b : A} (ha : CommShiftCore τ a) (hb : CommShiftCore τ b)
  proof: by
    ext X
    have := (shiftFunctorAdd D a b).inv.naturality (τ.app X)
    dsimp at this ⊢
    simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
      ← NatTrans.naturality_2 τ ((shiftFunctorAdd C a b).app X),
      Functor.comp_obj, hb.app_shift_assoc, ha.app_shift, assoc,
      (shiftFunctor D b).map_comp_assoc]
    simp [← Functor.map_comp_assoc, this]

中文:
引理 add
  条件: {a b : A} (ha : 交换ShiftCore τ a) (hb : 交换ShiftCore τ b)
  证明: by
    ext X
    have := (shiftFunctorAdd D a b).inv.naturality (τ.app X)
    dsimp at this ⊢
    simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
      ← NatTrans.naturality_2 τ ((shiftFunctorAdd C a b).app X),
      Functor.comp_obj, hb.app_shift_assoc, ha.app_shift, assoc,
      (shiftFunctor D b).map_comp_assoc]
    simp [← Functor.map_comp_assoc, this]

Depends on / 依赖: CommShift, Functor, Functor.CommShift.isoAdd_hom_app, Functor.commShiftIso_add, Functor.comp_obj, Functor.map_comp_assoc, NatTrans, NatTrans.naturality_2, app_shift, app_shift_assoc, commShiftIso_add, comp_obj, ha.app_shift, hb.app_shift_assoc, inv.naturality, isoAdd_hom_app, map_comp_assoc, naturality, naturality_2, shiftFunctor
-/
lemma add {a b : A} (ha : CommShiftCore τ a) (hb : CommShiftCore τ b) :
    CommShiftCore τ (a + b) where
  shift_comm := by
    ext X
    have := (shiftFunctorAdd D a b).inv.naturality (τ.app X)
    dsimp at this ⊢
    simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
      ← NatTrans.naturality_2 τ ((shiftFunctorAdd C a b).app X),
      Functor.comp_obj, hb.app_shift_assoc, ha.app_shift, assoc,
      (shiftFunctor D b).map_comp_assoc]
    simp [← Functor.map_comp_assoc, this]

end CommShiftCore

/--
Definition of `CommShift` / `CommShift` 的定义

English:
class CommShift
  parameters: : Prop where
  axioms and operations (1):
    - shift_comm((a : A)) : (F₁.commShiftIso a).hom ≫ Functor.whiskerRight τ _ = Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom  [default: by cat_disch]

中文:
类 交换Shift
  参数: : 命题 where
  公理与运算 (1 个):
    - shift_comm((a : A)) : (F₁.commShiftIso a).hom ≫ 函子.whiskerRight τ _ = 函子.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class CommShift : Prop where
  shift_comm (a : A) : (F₁.commShiftIso a).hom ≫ Functor.whiskerRight τ _ =
    Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom := by cat_disch

section

variable {A}

variable {τ} in
/--
lemma `CommShift.of_core` / 引理 `CommShift.of_core`

English:
lemma CommShift.of_core
  given: (h : forall (a : A), CommShiftCore τ a)
  proof: (h a).shift_comm

中文:
引理 交换Shift.of_core
  条件: (h : 对任意 (a : A), 交换ShiftCore τ a)
  证明: (h a).shift_comm

Depends on / 依赖: shift_comm
-/
lemma CommShift.of_core (h : forall (a : A), CommShiftCore τ a) :
    CommShift τ A where
  shift_comm a := (h a).shift_comm

variable [NatTrans.CommShift τ A]

@[reassoc]
/--
lemma `shift_comm` / 引理 `shift_comm`

English:
lemma shift_comm
  given: (a : A)
  proof: by
  apply CommShift.shift_comm

@[reassoc]

中文:
引理 shift_comm
  条件: (a : A)
  证明: by
  apply CommShift.shift_comm

@[reassoc]

Depends on / 依赖: CommShift, CommShift.shift_comm, shift_comm
-/
lemma shift_comm (a : A) :
    (F₁.commShiftIso a).hom ≫ Functor.whiskerRight τ _ =
      Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom := by
  apply CommShift.shift_comm

@[reassoc]
/--
lemma `shift_app_comm` / 引理 `shift_app_comm`

English:
lemma shift_app_comm
  given: (a : A) (X : C)
  proof: congr_app (shift_comm τ a) X

@[reassoc]

中文:
引理 shift_app_comm
  条件: (a : A) (X : C)
  证明: congr_app (shift_comm τ a) X

@[reassoc]

Depends on / 依赖: congr_app, shift_comm
-/
lemma shift_app_comm (a : A) (X : C) :
    (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' =
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X :=
  congr_app (shift_comm τ a) X

@[reassoc]
/--
lemma `shift_app` / 引理 `shift_app`

English:
lemma shift_app
  given: (a : A) (X : C)
  proof: by
  rw [← shift_app_comm]; rw [Iso.inv_hom_id_app_assoc]

@[reassoc]

中文:
引理 shift_app
  条件: (a : A) (X : C)
  证明: by
  rw [← shift_app_comm]; rw [Iso.inv_hom_id_app_assoc]

@[reassoc]

Depends on / 依赖: Iso.inv_hom_id_app_assoc, inv_hom_id_app_assoc, shift_app_comm
-/
lemma shift_app (a : A) (X : C) :
    (τ.app X)⟦a⟧' = (F₁.commShiftIso a).inv.app X ≫
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X := by
  rw [← shift_app_comm]; rw [Iso.inv_hom_id_app_assoc]

@[reassoc]
/--
lemma `app_shift` / 引理 `app_shift`

English:
lemma app_shift
  given: (a : A) (X : C)
  proof: by
  simp [shift_app_comm_assoc τ a X]

中文:
引理 app_shift
  条件: (a : A) (X : C)
  证明: by
  simp [shift_app_comm_assoc τ a X]

Depends on / 依赖: shift_app_comm_assoc
-/
lemma app_shift (a : A) (X : C) :
    τ.app (X⟦a⟧) = (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' ≫
      (F₂.commShiftIso a).inv.app X := by
  simp [shift_app_comm_assoc τ a X]

end

namespace CommShift

/--
Instance `of_iso_inv` / 实例 `of_iso_inv`

English:
instance of_iso_inv
  signature: [NatTrans.CommShift e.hom A]
  body: ⟨fun a => by
  ext X
  dsimp
  rw [← cancel_epi (e.hom.app (X⟦a⟧))]; rw [e.hom_inv_id_app_assoc]; rw [← shift_app_comm_assoc]; rw [← Functor.map_comp]; rw [e.hom_inv_id_app]; rw [Functor.map_id]; rw [Category.comp_id]⟩

中文:
实例 of_iso_inv
  签名: [自然变换.交换Shift e.hom A]
  定义体: ⟨fun a => by
  ext X
  dsimp
  rw [← cancel_epi (e.hom.app (X⟦a⟧))]; rw [e.hom_inv_id_app_assoc]; rw [← shift_app_comm_assoc]; rw [← Functor.map_comp]; rw [e.hom_inv_id_app]; rw [Functor.map_id]; rw [Category.comp_id]⟩

Depends on / 依赖: Category, Category.comp_id, Functor, Functor.map_comp, Functor.map_id, cancel_epi, comp_id, e.hom.app, e.hom_inv_id_app, e.hom_inv_id_app_assoc, hom_inv_id_app, hom_inv_id_app_assoc, map_comp, map_id, shift_app_comm_assoc
-/
instance of_iso_inv [NatTrans.CommShift e.hom A] :
    NatTrans.CommShift e.inv A := ⟨fun a => by
  ext X
  dsimp
  rw [← cancel_epi (e.hom.app (X⟦a⟧))]; rw [e.hom_inv_id_app_assoc]; rw [← shift_app_comm_assoc]; rw [← Functor.map_comp]; rw [e.hom_inv_id_app]; rw [Functor.map_id]; rw [Category.comp_id]⟩

/--
Instance `of_iso_symm` / 实例 `of_iso_symm`

English:
instance of_iso_symm
  signature: [NatTrans.CommShift e.hom A]
  body: NatTrans.CommShift.of_iso_inv e A

中文:
实例 of_iso_symm
  签名: [自然变换.交换Shift e.hom A]
  定义体: NatTrans.CommShift.of_iso_inv e A

Depends on / 依赖: CommShift, NatTrans, NatTrans.CommShift.of_iso_inv, of_iso_inv
-/
instance of_iso_symm [NatTrans.CommShift e.hom A] : NatTrans.CommShift e.symm.hom A :=
  NatTrans.CommShift.of_iso_inv e A

/--
lemma `of_isIso` / 引理 `of_isIso`

English:
lemma of_isIso
  given: [IsIso τ] [NatTrans.CommShift τ A]
  proof: by
  have : NatTrans.CommShift (asIso τ).hom A := by assumption
  change NatTrans.CommShift (asIso τ).inv A
  infer_instance

中文:
引理 of_isIso
  条件: [是同构 τ] [自然变换.交换Shift τ A]
  证明: by
  have : NatTrans.CommShift (asIso τ).hom A := by assumption
  change NatTrans.CommShift (asIso τ).inv A
  infer_instance

Depends on / 依赖: CommShift, NatTrans, NatTrans.CommShift, infer_instance
-/
lemma of_isIso [IsIso τ] [NatTrans.CommShift τ A] :
    NatTrans.CommShift (inv τ) A := by
  have : NatTrans.CommShift (asIso τ).hom A := by assumption
  change NatTrans.CommShift (asIso τ).inv A
  infer_instance

variable (F₁) in
/--
Instance `id` / 实例 `id`

English:
instance id
  signature: : NatTrans.CommShift (𝟙 F₁) A where

中文:
实例 id
  签名: : 自然变换.交换Shift (𝟙 F₁) A where
-/
instance id : NatTrans.CommShift (𝟙 F₁) A where

attribute [local simp] Functor.commShiftIso_comp_hom_app
  shift_app_comm shift_app_comm_assoc

/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: [NatTrans.CommShift τ A] [NatTrans.CommShift τ' A]

中文:
实例 comp
  签名: [自然变换.交换Shift τ A] [自然变换.交换Shift τ' A]
-/
instance comp [NatTrans.CommShift τ A] [NatTrans.CommShift τ' A] :
    NatTrans.CommShift (τ ≫ τ') A where

/--
Instance `whiskerRight` / 实例 `whiskerRight`

English:
instance whiskerRight
  signature: [NatTrans.CommShift τ A]
  body: ⟨fun a => by
  ext X
  simp only [Functor.whiskerRight_twice, comp_app, Functor.commShiftIso_comp_hom_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_inv_app, comp_id, id_comp, assoc, ← Functor.commShiftIso_hom_naturality, ←
    G.map_comp_assoc, shift_app_comm, Functor.whiskerLeft_app]⟩

中文:
实例 whiskerRight
  签名: [自然变换.交换Shift τ A]
  定义体: ⟨fun a => by
  ext X
  simp only [Functor.whiskerRight_twice, comp_app, Functor.commShiftIso_comp_hom_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_inv_app, comp_id, id_comp, assoc, ← Functor.commShiftIso_hom_naturality, ←
    G.map_comp_assoc, shift_app_comm, Functor.whiskerLeft_app]⟩

Depends on / 依赖: Functor, Functor.associator_hom_app, Functor.associator_inv_app, Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_hom_naturality, Functor.comp_map, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.whiskerRight_twice, G.map_comp_assoc, associator_hom_app, associator_inv_app, commShiftIso_comp_hom_app, commShiftIso_hom_naturality, comp_app, comp_id, comp_map, id_comp, map_comp_assoc, shift_app_comm
-/
instance whiskerRight [NatTrans.CommShift τ A] :
    NatTrans.CommShift (Functor.whiskerRight τ G) A := ⟨fun a => by
  ext X
  simp only [Functor.whiskerRight_twice, comp_app, Functor.commShiftIso_comp_hom_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_inv_app, comp_id, id_comp, assoc, ← Functor.commShiftIso_hom_naturality, ←
    G.map_comp_assoc, shift_app_comm, Functor.whiskerLeft_app]⟩

/--
Instance `whiskerLeft` / 实例 `whiskerLeft`

English:
instance whiskerLeft
  signature: [NatTrans.CommShift τ'' A]

中文:
实例 whiskerLeft
  签名: [自然变换.交换Shift τ'' A]
-/
instance whiskerLeft [NatTrans.CommShift τ'' A] :
    NatTrans.CommShift (Functor.whiskerLeft F₁ τ'') A where

/--
Instance `associator` / 实例 `associator`

English:
instance associator
  signature: : CommShift (Functor.associator F₁ G H).hom A where

中文:
实例 associator
  签名: : 交换Shift (函子.associator F₁ G H).hom A where
-/
instance associator : CommShift (Functor.associator F₁ G H).hom A where

/--
Instance `leftUnitor` / 实例 `leftUnitor`

English:
instance leftUnitor
  signature: : CommShift F₁.leftUnitor.hom A where

中文:
实例 leftUnitor
  签名: : 交换Shift F₁.leftUnitor.hom A where
-/
instance leftUnitor : CommShift F₁.leftUnitor.hom A where

/--
Instance `rightUnitor` / 实例 `rightUnitor`

English:
instance rightUnitor
  signature: : CommShift F₁.rightUnitor.hom A where

中文:
实例 rightUnitor
  签名: : 交换Shift F₁.rightUnitor.hom A where
-/
instance rightUnitor : CommShift F₁.rightUnitor.hom A where

end CommShift

end NatTrans

namespace Functor

namespace CommShift

variable {C D E : Type*} [Category* C] [Category* D]
  {F : C ⥤ D} {G : C ⥤ D} (e : F ≅ G)
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]
  [F.CommShift A]

/-- If `e : F ≅ G` is an isomorphism of functors and if `F` commutes with the
shift, then `G` also commutes with the shift. -/
@[simps! -isSimp commShiftIso_hom_app commShiftIso_inv_app, instance_reducible]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: : G.CommShift A where
  body: isoWhiskerLeft _ e.symm ≪≫ F.commShiftIso a ≪≫ isoWhiskerRight e _
  commShiftIso_zero := by
    ext X
    simp [F.commShiftIso_zero, ← NatTrans.naturality]
  commShiftIso_add a b := by
    ext X
    simp only [comp_obj, F.commShiftIso_add, Iso.trans_hom, isoWhiskerLeft_hom,
      Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
      isoAdd_hom_app, whiskerRight_app, assoc, map_comp, NatTrans.naturality_assoc,
      NatIso.cancel_natIso_inv_left]
    simp only [← Functor.map_comp_assoc, e.hom_inv_id_app_assoc]
    simp only [← NatTrans.naturality, comp_obj, comp_map, map_comp, assoc]

中文:
定义 ofIso
  签名: : G.交换Shift A where
  定义体: isoWhiskerLeft _ e.symm ≪≫ F.commShiftIso a ≪≫ isoWhiskerRight e _
  commShiftIso_zero := by
    ext X
    simp [F.commShiftIso_zero, ← NatTrans.naturality]
  commShiftIso_add a b := by
    ext X
    simp only [comp_obj, F.commShiftIso_add, Iso.trans_hom, isoWhiskerLeft_hom,
      Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
      isoAdd_hom_app, whiskerRight_app, assoc, map_comp, NatTrans.naturality_assoc,
      NatIso.cancel_natIso_inv_left]
    simp only [← Functor.map_comp_assoc, e.hom_inv_id_app_assoc]
    simp only [← NatTrans.naturality, comp_obj, comp_map, map_comp, assoc]

Depends on / 依赖: F.commShiftIso, commShiftIso, e.symm, isoWhiskerLeft, isoWhiskerRight
-/
def ofIso : G.CommShift A where
  commShiftIso a := isoWhiskerLeft _ e.symm ≪≫ F.commShiftIso a ≪≫ isoWhiskerRight e _
  commShiftIso_zero := by
    ext X
    simp [F.commShiftIso_zero, ← NatTrans.naturality]
  commShiftIso_add a b := by
    ext X
    simp only [comp_obj, F.commShiftIso_add, Iso.trans_hom, isoWhiskerLeft_hom,
      Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
      isoAdd_hom_app, whiskerRight_app, assoc, map_comp, NatTrans.naturality_assoc,
      NatIso.cancel_natIso_inv_left]
    simp only [← Functor.map_comp_assoc, e.hom_inv_id_app_assoc]
    simp only [← NatTrans.naturality, comp_obj, comp_map, map_comp, assoc]

/--
lemma `ofIso_compatibility` / 引理 `ofIso_compatibility`

English:
lemma ofIso_compatibility
  proof: ofIso e A
    NatTrans.CommShift e.hom A := by
  let := ofIso e A
  exact ⟨fun a => by ext; simp [ofIso_commShiftIso_hom_app]⟩

中文:
引理 ofIso_compatibility
  证明: ofIso e A
    NatTrans.CommShift e.hom A := by
  let := ofIso e A
  exact ⟨fun a => by ext; simp [ofIso_commShiftIso_hom_app]⟩
-/
lemma ofIso_compatibility :
    letI := ofIso e A
    NatTrans.CommShift e.hom A := by
  let := ofIso e A
  exact ⟨fun a => by ext; simp [ofIso_commShiftIso_hom_app]⟩

end CommShift

end Functor

namespace Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {A : Type*}

section hasShiftOfFullyFaithful

variable [AddMonoid A] [HasShift D A]
  {F : C ⥤ D} (hF : F.FullyFaithful)
  (s : A -> C ⥤ C) (i : forall i, s i ⋙ F ≅ F ⋙ shiftFunctor D i)

namespace CommShift

set_option backward.isDefEq.respectTransparency false in
/-- If `F : C ⥤ D` is a fully faithful functor which is used
to construct a shift by `A` on `C` from a shift on `D`,
then the functor `F` itself commutes with the shift by `A`. -/
@[instance_reducible]
/--
Definition of `ofHasShiftOfFullyFaithful` / `ofHasShiftOfFullyFaithful` 的定义

English:
definition ofHasShiftOfFullyFaithful
  signature: :
  body: hF.hasShift s i; F.CommShift A := by
  letI := hF.hasShift s i
  exact
  { commShiftIso := i
    commShiftIso_zero := by
      ext X
      simp [ShiftMkCore.shiftFunctorZero_eq]
    commShiftIso_add := fun a b => by
      ext X
      simp [ShiftMkCore.shiftFunctorAdd_eq, ShiftMkCore.shiftFunctor_eq,
        ← Functor.map_comp_assoc] }

中文:
定义 ofHasShiftOfFullyFaithful
  签名: :
  定义体: hF.hasShift s i; F.CommShift A := by
  letI := hF.hasShift s i
  exact
  { commShiftIso := i
    commShiftIso_zero := by
      ext X
      simp [ShiftMkCore.shiftFunctorZero_eq]
    commShiftIso_add := fun a b => by
      ext X
      simp [ShiftMkCore.shiftFunctorAdd_eq, ShiftMkCore.shiftFunctor_eq,
        ← Functor.map_comp_assoc] }

Depends on / 依赖: CommShift, F.CommShift, Functor, Functor.map_comp_assoc, ShiftMkCore, ShiftMkCore.shiftFunctorAdd_eq, ShiftMkCore.shiftFunctorZero_eq, ShiftMkCore.shiftFunctor_eq, commShiftIso, commShiftIso_add, commShiftIso_zero, hF.hasShift, hasShift, map_comp_assoc, shiftFunctorAdd_eq, shiftFunctorZero_eq, shiftFunctor_eq
-/
def ofHasShiftOfFullyFaithful :
    letI := hF.hasShift s i; F.CommShift A := by
  letI := hF.hasShift s i
  exact
  { commShiftIso := i
    commShiftIso_zero := by
      ext X
      simp [ShiftMkCore.shiftFunctorZero_eq]
    commShiftIso_add := fun a b => by
      ext X
      simp [ShiftMkCore.shiftFunctorAdd_eq, ShiftMkCore.shiftFunctor_eq,
        ← Functor.map_comp_assoc] }

end CommShift

/--
lemma `shiftFunctorIso_ofHasShiftOfFullyFaithful` / 引理 `shiftFunctorIso_ofHasShiftOfFullyFaithful`

English:
lemma shiftFunctorIso_ofHasShiftOfFullyFaithful
  given: (a : A)
  proof: hF.hasShift s i
    letI := CommShift.ofHasShiftOfFullyFaithful hF s i
    F.commShiftIso a = i a := by
  rfl

中文:
引理 shiftFunctorIso_ofHasShiftOfFullyFaithful
  条件: (a : A)
  证明: hF.hasShift s i
    letI := CommShift.ofHasShiftOfFullyFaithful hF s i
    F.commShiftIso a = i a := by
  rfl

Depends on / 依赖: hF.hasShift, hasShift
-/
lemma shiftFunctorIso_ofHasShiftOfFullyFaithful (a : A) :
    letI := hF.hasShift s i
    letI := CommShift.ofHasShiftOfFullyFaithful hF s i
    F.commShiftIso a = i a := by
  rfl

end hasShiftOfFullyFaithful

@[reassoc]
/--
lemma `map_shiftFunctorComm` / 引理 `map_shiftFunctorComm`

English:
lemma map_shiftFunctorComm
  proof: map_shiftFunctorComm_hom_app _ _ _ _

中文:
引理 map_shiftFunctorComm
  证明: map_shiftFunctorComm_hom_app _ _ _ _

Depends on / 依赖: map_shiftFunctorComm_hom_app
-/
lemma map_shiftFunctorComm
    [AddCommMonoid A] [HasShift C A] [HasShift D A]
    (F : C ⥤ D) [F.CommShift A] (X : C) (a b : A) :
    F.map ((shiftFunctorComm C a b).hom.app X) = (F.commShiftIso b).hom.app (X⟦a⟧) ≫
      ((F.commShiftIso a).hom.app X)⟦b⟧' ≫ (shiftFunctorComm D a b).hom.app (F.obj X) ≫
      ((F.commShiftIso b).inv.app X)⟦a⟧' ≫ (F.commShiftIso a).inv.app (X⟦b⟧) :=
  map_shiftFunctorComm_hom_app _ _ _ _

namespace CommShift

variable {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
  [Full G] [Faithful G]
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A]
  [G.CommShift A] [H.CommShift A]

namespace OfComp

variable {A}

/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: (a : A)
  body: ((whiskeringRight C D E).obj G).preimageIso
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e ≪≫
      H.commShiftIso a ≪≫ isoWhiskerRight e.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft F (G.commShiftIso a).symm ≪≫ (Functor.associator _ _ _).symm)

@[simp, reassoc]

中文:
定义 iso
  签名: (a : A)
  定义体: ((whiskeringRight C D E).obj G).preimageIso
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e ≪≫
      H.commShiftIso a ≪≫ isoWhiskerRight e.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft F (G.commShiftIso a).symm ≪≫ (Functor.associator _ _ _).symm)

@[simp, reassoc]

Depends on / 依赖: Functor, Functor.associator, G.commShiftIso, H.commShiftIso, associator, commShiftIso, e.symm, isoWhiskerLeft, isoWhiskerRight, preimageIso, whiskeringRight
-/
noncomputable def iso (a : A) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  ((whiskeringRight C D E).obj G).preimageIso
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e ≪≫
      H.commShiftIso a ≪≫ isoWhiskerRight e.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft F (G.commShiftIso a).symm ≪≫ (Functor.associator _ _ _).symm)

@[simp, reassoc]
/--
lemma `map_iso_hom_app` / 引理 `map_iso_hom_app`

English:
lemma map_iso_hom_app
  given: (a : A) (X : C)
  proof: by
  have h : ((whiskeringRight C D E).obj G).map (iso e a).hom = _ :=
    Functor.map_preimage _ _
  simpa using congr_app h X

@[simp, reassoc]

中文:
引理 map_iso_hom_app
  条件: (a : A) (X : C)
  证明: by
  have h : ((whiskeringRight C D E).obj G).map (iso e a).hom = _ :=
    Functor.map_preimage _ _
  simpa using congr_app h X

@[simp, reassoc]

Depends on / 依赖: Functor, Functor.map_preimage, congr_app, map_preimage, whiskeringRight
-/
lemma map_iso_hom_app (a : A) (X : C) :
    G.map ((iso e a).hom.app X) = e.hom.app (X⟦a⟧) ≫
      (H.commShiftIso a).hom.app X ≫ (e.inv.app X)⟦a⟧' ≫
      (G.commShiftIso a).inv.app (F.obj X) := by
  have h : ((whiskeringRight C D E).obj G).map (iso e a).hom = _ :=
    Functor.map_preimage _ _
  simpa using congr_app h X

@[simp, reassoc]
/--
lemma `map_iso_inv_app` / 引理 `map_iso_inv_app`

English:
lemma map_iso_inv_app
  given: (a : A) (X : C)
  proof: by
  have h : ((whiskeringRight C D E).obj G).map (iso e a).inv = _ :=
    Functor.map_preimage _ _
  simpa using congr_app h X

中文:
引理 map_iso_inv_app
  条件: (a : A) (X : C)
  证明: by
  have h : ((whiskeringRight C D E).obj G).map (iso e a).inv = _ :=
    Functor.map_preimage _ _
  simpa using congr_app h X

Depends on / 依赖: Functor, Functor.map_preimage, congr_app, map_preimage, whiskeringRight
-/
lemma map_iso_inv_app (a : A) (X : C) :
    G.map ((iso e a).inv.app X) =
      (G.commShiftIso a).hom.app (F.obj X) ≫ (e.hom.app X)⟦a⟧' ≫
      (H.commShiftIso a).inv.app X ≫ e.inv.app (X⟦a⟧) := by
  have h : ((whiskeringRight C D E).obj G).map (iso e a).inv = _ :=
    Functor.map_preimage _ _
  simpa using congr_app h X

attribute [irreducible] iso

end OfComp

/-- Given an isomorphism `e : F ⋙ G ≅ H` where `G` is fully faithful,
the functor `F` commutes with shifts by `A` if `G` and `H` do. -/
@[instance_reducible]
/--
Definition of `ofComp` / `ofComp` 的定义

English:
definition ofComp
  signature: : F.CommShift A where
  body: OfComp.iso e
  commShiftIso_zero := by
    ext X
    apply G.map_injective
    simp [G.commShiftIso_zero, H.commShiftIso_zero]
  commShiftIso_add a b := by
    ext X
    apply G.map_injective
    simp only [comp_obj, OfComp.map_iso_hom_app, H.commShiftIso_add, isoAdd_hom_app,
      G.commShiftIso_add, isoAdd_inv_app, NatTrans.naturality_assoc, comp_map, assoc,
      Iso.inv_hom_id_app_assoc, map_comp]
    simp only [← NatTrans.naturality_assoc, ← commShiftIso_inv_naturality_assoc,
      ← Functor.map_comp_assoc]
    congr 4
    simp

中文:
定义 ofComp
  签名: : F.交换Shift A where
  定义体: OfComp.iso e
  commShiftIso_zero := by
    ext X
    apply G.map_injective
    simp [G.commShiftIso_zero, H.commShiftIso_zero]
  commShiftIso_add a b := by
    ext X
    apply G.map_injective
    simp only [comp_obj, OfComp.map_iso_hom_app, H.commShiftIso_add, isoAdd_hom_app,
      G.commShiftIso_add, isoAdd_inv_app, NatTrans.naturality_assoc, comp_map, assoc,
      Iso.inv_hom_id_app_assoc, map_comp]
    simp only [← NatTrans.naturality_assoc, ← commShiftIso_inv_naturality_assoc,
      ← Functor.map_comp_assoc]
    congr 4
    simp

Depends on / 依赖: OfComp, OfComp.iso
-/
noncomputable def ofComp : F.CommShift A where
  commShiftIso := OfComp.iso e
  commShiftIso_zero := by
    ext X
    apply G.map_injective
    simp [G.commShiftIso_zero, H.commShiftIso_zero]
  commShiftIso_add a b := by
    ext X
    apply G.map_injective
    simp only [comp_obj, OfComp.map_iso_hom_app, H.commShiftIso_add, isoAdd_hom_app,
      G.commShiftIso_add, isoAdd_inv_app, NatTrans.naturality_assoc, comp_map, assoc,
      Iso.inv_hom_id_app_assoc, map_comp]
    simp only [← NatTrans.naturality_assoc, ← commShiftIso_inv_naturality_assoc,
      ← Functor.map_comp_assoc]
    congr 4
    simp

/--
lemma `ofComp_compatibility` / 引理 `ofComp_compatibility`

English:
lemma ofComp_compatibility
  proof: ofComp e
    NatTrans.CommShift e.hom A := by
  let := ofComp e
  refine ⟨fun a => ?_⟩
  ext X
  simp [commShiftIso_comp_hom_app, show F.commShiftIso a = OfComp.iso e a from rfl,
    ← Functor.map_comp]

中文:
引理 ofComp_compatibility
  证明: ofComp e
    NatTrans.CommShift e.hom A := by
  let := ofComp e
  refine ⟨fun a => ?_⟩
  ext X
  simp [commShiftIso_comp_hom_app, show F.commShiftIso a = OfComp.iso e a from rfl,
    ← Functor.map_comp]

Depends on / 依赖: ofComp
-/
lemma ofComp_compatibility :
    letI := ofComp e
    NatTrans.CommShift e.hom A := by
  let := ofComp e
  refine ⟨fun a => ?_⟩
  ext X
  simp [commShiftIso_comp_hom_app, show F.commShiftIso a = OfComp.iso e a from rfl,
    ← Functor.map_comp]

end CommShift

end Functor

/--
lemma `NatTrans.CommShift.verticalComposition` / 引理 `NatTrans.CommShift.verticalComposition`

English:
lemma NatTrans.CommShift.verticalComposition
  statement: {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
  proof: by
  subst h₁₃
  infer_instance

中文:
引理 自然变换.交换Shift.verticalComposition
  结论: {C₁ C₂ C₃ D₁ D₂ D₃ : 类型}
  证明: by
  subst h₁₃
  infer_instance

Depends on / 依赖: infer_instance
-/
lemma NatTrans.CommShift.verticalComposition {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃] [Category* D₁] [Category* D₂] [Category* D₃]
    {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₁₃ : C₁ ⥤ C₃} (α : F₁₃ ⟶ F₁₂ ⋙ F₂₃)
    {G₁₂ : D₁ ⥤ D₂} {G₂₃ : D₂ ⥤ D₃} {G₁₃ : D₁ ⥤ D₃} (β : G₁₂ ⋙ G₂₃ ⟶ G₁₃)
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
    (e₁₂ : F₁₂ ⋙ L₂ ⟶ L₁ ⋙ G₁₂) (e₂₃ : F₂₃ ⋙ L₃ ⟶ L₂ ⋙ G₂₃) (e₁₃ : F₁₃ ⋙ L₃ ⟶ L₁ ⋙ G₁₃)
    (A : Type*) [AddMonoid A] [HasShift C₁ A] [HasShift C₂ A] [HasShift C₃ A]
    [HasShift D₁ A] [HasShift D₂ A] [HasShift D₃ A]
    [F₁₂.CommShift A] [F₂₃.CommShift A] [F₁₃.CommShift A] [CommShift α A]
    [G₁₂.CommShift A] [G₂₃.CommShift A] [G₁₃.CommShift A] [CommShift β A]
    [L₁.CommShift A] [L₂.CommShift A] [L₃.CommShift A]
    [CommShift e₁₂ A] [CommShift e₂₃ A]
    (h₁₃ : e₁₃ = Functor.whiskerRight α L₃ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft F₁₂ e₂₃ ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight e₁₂ G₂₃ ≫ (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft L₁ β) : CommShift e₁₃ A := by
  subst h₁₃
  infer_instance

end CategoryTheory
