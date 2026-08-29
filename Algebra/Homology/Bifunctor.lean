/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.GradedObject.Bifunctor

/-!
# The action of a bifunctor on homological complexes

Given a bifunctor `F : C₁ ⥤ C₂ ⥤ D` and complexes shapes `c₁ : ComplexShape I₁` and
`c₂ : ComplexShape I₂`, we define a bifunctor `mapBifunctorHomologicalComplex F c₁ c₂`
of type `HomologicalComplex C₁ c₁ ⥤ HomologicalComplex C₂ c₂ ⥤ HomologicalComplex₂ D c₁ c₂`.

Then, when `K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂` and
`c : ComplexShape J` are such that we have `TotalComplexShape c₁ c₂ c`, we introduce
a typeclass `HasMapBifunctor K₁ K₂ F c` which allows to define
`mapBifunctor K₁ K₂ F c : HomologicalComplex D c` as the total complex of the
bicomplex `(((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂)`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Limits

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

namespace CategoryTheory

namespace Functor

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms D]
  (F : C₁ ⥤ C₂ ⥤ D) {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  [F.PreservesZeroMorphisms] [forall X₁, (F.obj X₁).PreservesZeroMorphisms]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {c₁} in
/-- Auxiliary definition for `mapBifunctorHomologicalComplex`. -/
@[simps!]
/--
Definition of `mapBifunctorHomologicalComplexObj` / `mapBifunctorHomologicalComplexObj` 的定义

English:
definition mapBifunctorHomologicalComplexObj
  signature: (K₁ : HomologicalComplex C₁ c₁)
  body: HomologicalComplex₂.ofGradedObject c₁ c₂
      (((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).obj K₂.X)
      (fun i₁ i₁' i₂ => (F.map (K₁.d i₁ i₁')).app (K₂.X i₂))
      (fun i₁ i₂ i₂' => (F.obj (K₁.X i₁)).map (K₂.d i₂ i₂'))
      (fun i₁ i₁' h₁ i₂ => by
        dsimp
        rw [K₁.shape _ _ h₁];

中文:
定义 mapBifunctorHomologicalComplexObj
  签名: (K₁ : HomologicalComplex C₁ c₁)
  定义体: HomologicalComplex₂.ofGradedObject c₁ c₂
      (((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).obj K₂.X)
      (fun i₁ i₁' i₂ => (F.map (K₁.d i₁ i₁')).app (K₂.X i₂))
      (fun i₁ i₂ i₂' => (F.obj (K₁.X i₁)).map (K₂.d i₂ i₂'))
      (fun i₁ i₁' h₁ i₂ => by
        dsimp
        rw [K₁.shape _ _ h₁];

Depends on / 依赖: ofGradedObject
-/
def mapBifunctorHomologicalComplexObj (K₁ : HomologicalComplex C₁ c₁) :
    HomologicalComplex C₂ c₂ ⥤ HomologicalComplex₂ D c₁ c₂ where
  obj K₂ := HomologicalComplex₂.ofGradedObject c₁ c₂
      (((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).obj K₂.X)
      (fun i₁ i₁' i₂ => (F.map (K₁.d i₁ i₁')).app (K₂.X i₂))
      (fun i₁ i₂ i₂' => (F.obj (K₁.X i₁)).map (K₂.d i₂ i₂'))
      (fun i₁ i₁' h₁ i₂ => by
        dsimp
        rw [K₁.shape _ _ h₁]; rw [Functor.map_zero]; rw [zero_app])
      (fun i₁ i₂ i₂' h₂ => by
        dsimp
        rw [K₂.shape _ _ h₂]; rw [Functor.map_zero])
      (fun i₁ i₁' i₁'' i₂ => by
        dsimp
        rw [← NatTrans.comp_app]; rw [← Functor.map_comp]; rw [HomologicalComplex.d_comp_d]; rw [Functor.map_zero]; rw [zero_app])
      (fun i₁ i₂ i₂' i₂'' => by
        dsimp
        rw [← Functor.map_comp]; rw [HomologicalComplex.d_comp_d]; rw [Functor.map_zero])
      (fun i₁ i₁' i₂ i₂' => by
        dsimp
        rw [NatTrans.naturality])
  map {K₂ K₂' φ} := HomologicalComplex₂.homMk
      (((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).map φ.f)
        (by dsimp; intros; rw [NatTrans.naturality]) (by
          dsimp
          intros
          simp only [← Functor.map_comp, φ.comm])
  map_id K₂ := by dsimp; ext; dsimp; rw [Functor.map_id]
  map_comp f g := by dsimp; ext; dsimp; rw [Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a functor `F : C₁ ⥤ C₂ ⥤ D`, this is the bifunctor which sends
`K₁ : HomologicalComplex C₁ c₁` and `K₂ : HomologicalComplex C₂ c₂` to the bicomplex
which is degree `(i₁, i₂)` consists of `(F.obj (K₁.X i₁)).obj (K₂.X i₂)`. -/
@[simps! obj_obj_X_X obj_obj_X_d obj_obj_d_f obj_map_f_f map_app_f_f]
/--
Definition of `mapBifunctorHomologicalComplex` / `mapBifunctorHomologicalComplex` 的定义

English:
definition mapBifunctorHomologicalComplex
  signature: :
  body: mapBifunctorHomologicalComplexObj F c₂
  map {K₁ K₁'} f :=
    { app := fun K₂ => HomologicalComplex₂.homMk
        (((GradedObject.mapBifunctor F I₁ I₂).map f.f).app K₂.X) (by
          intros
          dsimp
          simp only [← NatTrans.comp_app, ← F.map_comp, f.comm]) (by simp) }

中文:
定义 mapBifunctorHomologicalComplex
  签名: :
  定义体: mapBifunctorHomologicalComplexObj F c₂
  map {K₁ K₁'} f :=
    { app := fun K₂ => HomologicalComplex₂.homMk
        (((GradedObject.mapBifunctor F I₁ I₂).map f.f).app K₂.X) (by
          intros
          dsimp
          simp only [← NatTrans.comp_app, ← F.map_comp, f.comm]) (by simp) }

Depends on / 依赖: mapBifunctorHomologicalComplexObj
-/
def mapBifunctorHomologicalComplex :
    HomologicalComplex C₁ c₁ ⥤ HomologicalComplex C₂ c₂ ⥤ HomologicalComplex₂ D c₁ c₂ where
  obj := mapBifunctorHomologicalComplexObj F c₂
  map {K₁ K₁'} f :=
    { app := fun K₂ => HomologicalComplex₂.homMk
        (((GradedObject.mapBifunctor F I₁ I₂).map f.f).app K₂.X) (by
          intros
          dsimp
          simp only [← NatTrans.comp_app, ← F.map_comp, f.comm]) (by simp) }

variable {c₁ c₂}

@[simp]
/--
lemma `mapBifunctorHomologicalComplex_obj_obj_toGradedObject` / 引理 `mapBifunctorHomologicalComplex_obj_obj_toGradedObject`

English:
lemma mapBifunctorHomologicalComplex_obj_obj_toGradedObject
  proof: rfl

中文:
引理 mapBifunctorHomologicalComplex_obj_obj_toGradedObject
  证明: rfl
-/
lemma mapBifunctorHomologicalComplex_obj_obj_toGradedObject
    (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂) :
    (((mapBifunctorHomologicalComplex F c₁ c₂).obj K₁).obj K₂).toGradedObject =
      ((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).obj K₂.X := rfl

end Functor

end CategoryTheory

namespace HomologicalComplex

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [forall X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

/--
Definition of `HasMapBifunctor` / `HasMapBifunctor` 的定义

English:
abbreviation HasMapBifunctor
  body: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).HasTotal c

中文:
缩写 HasMapBifunctor
  定义体: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).HasTotal c

Depends on / 依赖: F.mapBifunctorHomologicalComplex, HasTotal, mapBifunctorHomologicalComplex
-/
abbrev HasMapBifunctor := (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).HasTotal c

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

/--
Definition of `mapBifunctor` / `mapBifunctor` 的定义

English:
abbreviation mapBifunctor
  signature: : HomologicalComplex D c
  body: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).total c

中文:
缩写 mapBifunctor
  签名: : HomologicalComplex D c
  定义体: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).total c

Depends on / 依赖: F.mapBifunctorHomologicalComplex, mapBifunctorHomologicalComplex
-/
noncomputable abbrev mapBifunctor : HomologicalComplex D c :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).total c

/--
Definition of `ιMapBifunctor` / `ιMapBifunctor` 的定义

English:
abbreviation ιMapBifunctor
  body: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).ιTotal c i₁ i₂ j h

中文:
缩写 ιMapBifunctor
  定义体: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).ιTotal c i₁ i₂ j h

Depends on / 依赖: F.mapBifunctorHomologicalComplex, mapBifunctorHomologicalComplex
-/
noncomputable abbrev ιMapBifunctor
    (i₁ : I₁) (i₂ : I₂) (j : J) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (mapBifunctor K₁ K₂ F c).X j :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).ιTotal c i₁ i₂ j h

/--
Definition of `ιMapBifunctorOrZero` / `ιMapBifunctorOrZero` 的定义

English:
abbreviation ιMapBifunctorOrZero
  signature: (i₁ : I₁) (i₂ : I₂) (j : J)
  body: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).ιTotalOrZero c i₁ i₂ j

中文:
缩写 ιMapBifunctorOrZero
  签名: (i₁ : I₁) (i₂ : I₂) (j : J)
  定义体: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).ιTotalOrZero c i₁ i₂ j

Depends on / 依赖: F.mapBifunctorHomologicalComplex, mapBifunctorHomologicalComplex
-/
noncomputable abbrev ιMapBifunctorOrZero (i₁ : I₁) (i₂ : I₂) (j : J) :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (mapBifunctor K₁ K₂ F c).X j :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).ιTotalOrZero c i₁ i₂ j

/--
lemma `ιMapBifunctorOrZero_eq` / 引理 `ιMapBifunctorOrZero_eq`

English:
lemma ιMapBifunctorOrZero_eq
  statement: (i₁ : I₁) (i₂ : I₂) (j : J)
  proof: dif_pos h

中文:
引理 ιMapBifunctorOrZero_eq
  结论: (i₁ : I₁) (i₂ : I₂) (j : J)
  证明: dif_pos h

Depends on / 依赖: dif_pos
-/
lemma ιMapBifunctorOrZero_eq (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctorOrZero K₁ K₂ F c i₁ i₂ j = ιMapBifunctor K₁ K₂ F c i₁ i₂ j h := dif_pos h

/--
lemma `ιMapBifunctorOrZero_eq_zero` / 引理 `ιMapBifunctorOrZero_eq_zero`

English:
lemma ιMapBifunctorOrZero_eq_zero
  statement: (i₁ : I₁) (i₂ : I₂) (j : J)
  proof: dif_neg h

中文:
引理 ιMapBifunctorOrZero_eq_zero
  结论: (i₁ : I₁) (i₂ : I₂) (j : J)
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
lemma ιMapBifunctorOrZero_eq_zero (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) != j) :
    ιMapBifunctorOrZero K₁ K₂ F c i₁ i₂ j = 0 := dif_neg h

section

variable {K₁ K₂ F c}
variable {A : D} {j : J}
  (f : forall (i₁ : I₁) (i₂ : I₂) (_ : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j),
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ A)

/--
Definition of `mapBifunctorDesc` / `mapBifunctorDesc` 的定义

English:
definition mapBifunctorDesc
  signature: : (mapBifunctor K₁ K₂ F c).X j ⟶ A
  body: HomologicalComplex₂.totalDesc _ f

@[reassoc (attr := simp)]

中文:
定义 mapBifunctorDesc
  签名: : (mapBifunctor K₁ K₂ F c).X j ⟶ A
  定义体: HomologicalComplex₂.totalDesc _ f

@[reassoc (attr := simp)]

Depends on / 依赖: totalDesc
-/
noncomputable def mapBifunctorDesc : (mapBifunctor K₁ K₂ F c).X j ⟶ A :=
  HomologicalComplex₂.totalDesc _ f

@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctorDesc` / 引理 `ι_mapBifunctorDesc`

English:
lemma ι_mapBifunctorDesc
  given: (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j)
  proof: by
  apply HomologicalComplex₂.ι_totalDesc

中文:
引理 ι_mapBifunctorDesc
  条件: (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j)
  证明: by
  apply HomologicalComplex₂.ι_totalDesc
-/
lemma ι_mapBifunctorDesc (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ mapBifunctorDesc f = f i₁ i₂ h := by
  apply HomologicalComplex₂.ι_totalDesc

end

namespace mapBifunctor

variable {K₁ K₂ F c} in
@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {Y : D} {j : J} {f g : (mapBifunctor K₁ K₂ F c).X j ⟶ Y}
  proof: HomologicalComplex₂.total.hom_ext _ h

中文:
引理 hom_ext
  结论: {Y : D} {j : J} {f g : (mapBifunctor K₁ K₂ F c).X j ⟶ Y}
  证明: HomologicalComplex₂.total.hom_ext _ h

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplex, HomologicalComplex.quasiIso, Localization, Localization.inverts, QuasiIso, hom_ext, inverts, quasiIso, total.hom_ext
-/
lemma hom_ext {Y : D} {j : J} {f g : (mapBifunctor K₁ K₂ F c).X j ⟶ Y}
    (h : forall (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j),
      ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ f = ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ g) :
    f = g :=
  HomologicalComplex₂.total.hom_ext _ h

section

variable (j j' : J)

/--
Definition of `D₁` / `D₁` 的定义

English:
definition D₁
  signature: :
  body: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).D₁ c j j'

中文:
定义 D₁
  签名: :
  定义体: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).D₁ c j j'

Depends on / 依赖: F.mapBifunctorHomologicalComplex, mapBifunctorHomologicalComplex
-/
noncomputable def D₁ :
    (mapBifunctor K₁ K₂ F c).X j ⟶ (mapBifunctor K₁ K₂ F c).X j' :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).D₁ c j j'

/--
Definition of `D₂` / `D₂` 的定义

English:
definition D₂
  signature: :
  body: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).D₂ c j j'

中文:
定义 D₂
  签名: :
  定义体: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).D₂ c j j'

Depends on / 依赖: F.mapBifunctorHomologicalComplex, mapBifunctorHomologicalComplex
-/
noncomputable def D₂ :
    (mapBifunctor K₁ K₂ F c).X j ⟶ (mapBifunctor K₁ K₂ F c).X j' :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).D₂ c j j'

/--
lemma `d_eq` / 引理 `d_eq`

English:
lemma d_eq
  proof: rfl

中文:
引理 d_eq
  证明: rfl
-/
lemma d_eq :
    (mapBifunctor K₁ K₂ F c).d j j' = D₁ K₁ K₂ F c j j' + D₂ K₁ K₂ F c j j' := rfl

end

section

variable (i₁ : I₁) (i₂ : I₂) (j : J)

/--
Definition of `d₁` / `d₁` 的定义

English:
definition d₁
  signature: :
  body: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).d₁ c i₁ i₂ j

中文:
定义 d₁
  签名: :
  定义体: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).d₁ c i₁ i₂ j

Depends on / 依赖: F.mapBifunctorHomologicalComplex, mapBifunctorHomologicalComplex
-/
noncomputable def d₁ :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (mapBifunctor K₁ K₂ F c).X j :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).d₁ c i₁ i₂ j

/--
Definition of `d₂` / `d₂` 的定义

English:
definition d₂
  signature: :
  body: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).d₂ c i₁ i₂ j

中文:
定义 d₂
  签名: :
  定义体: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).d₂ c i₁ i₂ j

Depends on / 依赖: F.mapBifunctorHomologicalComplex, mapBifunctorHomologicalComplex
-/
noncomputable def d₂ :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (mapBifunctor K₁ K₂ F c).X j :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).d₂ c i₁ i₂ j

/--
lemma `d₁_eq_zero` / 引理 `d₁_eq_zero`

English:
lemma d₁_eq_zero
  given: (h : ¬ c₁.Rel i₁ (c₁.next i₁))
  proof: HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h

中文:
引理 d₁_eq_zero
  条件: (h : ¬ c₁.Rel i₁ (c₁.next i₁))
  证明: HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h
-/
lemma d₁_eq_zero (h : ¬ c₁.Rel i₁ (c₁.next i₁)) :
    d₁ K₁ K₂ F c i₁ i₂ j = 0 :=
  HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h

/--
lemma `d₂_eq_zero` / 引理 `d₂_eq_zero`

English:
lemma d₂_eq_zero
  given: (h : ¬ c₂.Rel i₂ (c₂.next i₂))
  proof: HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h

中文:
引理 d₂_eq_zero
  条件: (h : ¬ c₂.Rel i₂ (c₂.next i₂))
  证明: HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h
-/
lemma d₂_eq_zero (h : ¬ c₂.Rel i₂ (c₂.next i₂)) :
    d₂ K₁ K₂ F c i₁ i₂ j = 0 :=
  HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h

/--
lemma `d₁_eq_zero'` / 引理 `d₁_eq_zero'`

English:
lemma d₁_eq_zero'
  statement: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
  proof: HomologicalComplex₂.d₁_eq_zero' _ _ h _ _ h'

中文:
引理 d₁_eq_zero'
  结论: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
  证明: HomologicalComplex₂.d₁_eq_zero' _ _ h _ _ h'
-/
lemma d₁_eq_zero' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁', i₂⟩ != j) :
    d₁ K₁ K₂ F c i₁ i₂ j = 0 :=
  HomologicalComplex₂.d₁_eq_zero' _ _ h _ _ h'

/--
lemma `d₂_eq_zero'` / 引理 `d₂_eq_zero'`

English:
lemma d₂_eq_zero'
  statement: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
  proof: HomologicalComplex₂.d₂_eq_zero' _ _ _ h _ h'

中文:
引理 d₂_eq_zero'
  结论: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
  证明: HomologicalComplex₂.d₂_eq_zero' _ _ _ h _ h'
-/
lemma d₂_eq_zero' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁, i₂'⟩ != j) :
    d₂ K₁ K₂ F c i₁ i₂ j = 0 :=
  HomologicalComplex₂.d₂_eq_zero' _ _ _ h _ h'

/--
lemma `d₁_eq'` / 引理 `d₁_eq'`

English:
lemma d₁_eq'
  given: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
  proof: HomologicalComplex₂.d₁_eq' _ _ h _ _

中文:
引理 d₁_eq'
  条件: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
  证明: HomologicalComplex₂.d₁_eq' _ _ h _ _
-/
lemma d₁_eq' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J) :
    d₁ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₁ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.map (K₁.d i₁ i₁')).app (K₂.X i₂) ≫ ιMapBifunctorOrZero K₁ K₂ F c i₁' i₂ j) :=
  HomologicalComplex₂.d₁_eq' _ _ h _ _

/--
lemma `d₂_eq'` / 引理 `d₂_eq'`

English:
lemma d₂_eq'
  given: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
  proof: HomologicalComplex₂.d₂_eq' _ _ _ h _

中文:
引理 d₂_eq'
  条件: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
  证明: HomologicalComplex₂.d₂_eq' _ _ _ h _
-/
lemma d₂_eq' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J) :
    d₂ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₂ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.obj (K₁.X i₁)).map (K₂.d i₂ i₂') ≫ ιMapBifunctorOrZero K₁ K₂ F c i₁ i₂' j) :=
  HomologicalComplex₂.d₂_eq' _ _ _ h _

/--
lemma `d₁_eq` / 引理 `d₁_eq`

English:
lemma d₁_eq
  statement: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
  proof: HomologicalComplex₂.d₁_eq _ _ h _ _ h'

中文:
引理 d₁_eq
  结论: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
  证明: HomologicalComplex₂.d₁_eq _ _ h _ _ h'
-/
lemma d₁_eq {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁', i₂⟩ = j) :
    d₁ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₁ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.map (K₁.d i₁ i₁')).app (K₂.X i₂) ≫ ιMapBifunctor K₁ K₂ F c i₁' i₂ j h') :=
  HomologicalComplex₂.d₁_eq _ _ h _ _ h'

/--
lemma `d₂_eq` / 引理 `d₂_eq`

English:
lemma d₂_eq
  statement: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
  proof: HomologicalComplex₂.d₂_eq _ _ _ h _ h'

中文:
引理 d₂_eq
  结论: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
  证明: HomologicalComplex₂.d₂_eq _ _ _ h _ h'
-/
lemma d₂_eq (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁, i₂'⟩ = j) :
    d₂ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₂ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.obj (K₁.X i₁)).map (K₂.d i₂ i₂') ≫ ιMapBifunctor K₁ K₂ F c i₁ i₂' j h') :=
  HomologicalComplex₂.d₂_eq _ _ _ h _ h'

end

section

variable (j j' : J) (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j)

@[reassoc (attr := simp)]
/--
lemma `ι_D₁` / 引理 `ι_D₁`

English:
lemma ι_D₁
  proof: by
  apply HomologicalComplex₂.ι_D₁

@[reassoc (attr := simp)]

中文:
引理 ι_D₁
  证明: by
  apply HomologicalComplex₂.ι_D₁

@[reassoc (attr := simp)]
-/
lemma ι_D₁ :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ D₁ K₁ K₂ F c j j' = d₁ K₁ K₂ F c i₁ i₂ j' := by
  apply HomologicalComplex₂.ι_D₁

@[reassoc (attr := simp)]
/--
lemma `ι_D₂` / 引理 `ι_D₂`

English:
lemma ι_D₂
  proof: by
  apply HomologicalComplex₂.ι_D₂

中文:
引理 ι_D₂
  证明: by
  apply HomologicalComplex₂.ι_D₂

Depends on / 依赖: Functor, Functor.additive_of_iso, HomotopyCategory, HomotopyCategory.subcategoryAcyclic, Localization, Localization.functor_additive_iff, Qh.commShiftIso, additive_of_iso, commShiftIso, functor_additive_iff, subcategoryAcyclic
-/
lemma ι_D₂ :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ D₂ K₁ K₂ F c j j' = d₂ K₁ K₂ F c i₁ i₂ j' := by
  apply HomologicalComplex₂.ι_D₂

end

end mapBifunctor

section

variable {K₁ K₂ L₁ L₂}

/--
Definition of `mapBifunctorMap` / `mapBifunctorMap` 的定义

English:
definition mapBifunctorMap
  signature: : mapBifunctor K₁ K₂ F c ⟶ mapBifunctor L₁ L₂ F c
  body: HomologicalComplex₂.total.map (((F.mapBifunctorHomologicalComplex c₁ c₂).map f₁).app K₂ ≫
    ((F.mapBifunctorHomologicalComplex c₁ c₂).obj L₁).map f₂) c

中文:
定义 mapBifunctorMap
  签名: : mapBifunctor K₁ K₂ F c ⟶ mapBifunctor L₁ L₂ F c
  定义体: HomologicalComplex₂.total.map (((F.mapBifunctorHomologicalComplex c₁ c₂).map f₁).app K₂ ≫
    ((F.mapBifunctorHomologicalComplex c₁ c₂).obj L₁).map f₂) c

Depends on / 依赖: F.mapBifunctorHomologicalComplex, mapBifunctorHomologicalComplex, total.map
-/
noncomputable def mapBifunctorMap : mapBifunctor K₁ K₂ F c ⟶ mapBifunctor L₁ L₂ F c :=
  HomologicalComplex₂.total.map (((F.mapBifunctorHomologicalComplex c₁ c₂).map f₁).app K₂ ≫
    ((F.mapBifunctorHomologicalComplex c₁ c₂).obj L₁).map f₂) c

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctorMap` / 引理 `ι_mapBifunctorMap`

English:
lemma ι_mapBifunctorMap
  statement: (i₁ : I₁) (i₂ : I₂) (j : J)
  proof: by
  simp [mapBifunctorMap]

中文:
引理 ι_mapBifunctorMap
  结论: (i₁ : I₁) (i₂ : I₂) (j : J)
  证明: by
  simp [mapBifunctorMap]

Depends on / 依赖: mapBifunctorMap
-/
lemma ι_mapBifunctorMap (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ (mapBifunctorMap f₁ f₂ F c).f j =
      (F.map (f₁.f i₁)).app (K₂.X i₂) ≫ (F.obj (L₁.X i₁)).map (f₂.f i₂) ≫
        ιMapBifunctor L₁ L₂ F c i₁ i₂ j h := by
  simp [mapBifunctorMap]

end

end HomologicalComplex

namespace CategoryTheory.Functor

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [forall X₁, (F.obj X₁).PreservesZeroMorphisms]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c : ComplexShape J)
  [DecidableEq J] [TotalComplexShape c₁ c₂ c]

open HomologicalComplex

/-- The bifunctor on homological complexes that is induced by a bifunctor. -/
@[simps]
/--
Definition of `map₂HomologicalComplex` / `map₂HomologicalComplex` 的定义

English:
definition map₂HomologicalComplex
  body: { obj K₂ := mapBifunctor K₁ K₂ F c
      map g := mapBifunctorMap (𝟙 K₁) g _ _ }
  map f := { app K₂ := mapBifunctorMap f (𝟙 K₂) _ _ }

中文:
定义 map₂HomologicalComplex
  定义体: { obj K₂ := mapBifunctor K₁ K₂ F c
      map g := mapBifunctorMap (𝟙 K₁) g _ _ }
  map f := { app K₂ := mapBifunctorMap f (𝟙 K₂) _ _ }

Depends on / 依赖: mapBifunctor, mapBifunctorMap
-/
noncomputable def map₂HomologicalComplex
    [forall (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂),
      HasMapBifunctor K₁ K₂ F c] :
    HomologicalComplex C₁ c₁ ⥤ HomologicalComplex C₂ c₂ ⥤ HomologicalComplex D c where
  obj K₁ :=
    { obj K₂ := mapBifunctor K₁ K₂ F c
      map g := mapBifunctorMap (𝟙 K₁) g _ _ }
  map f := { app K₂ := mapBifunctorMap f (𝟙 K₂) _ _ }

/--
Definition of `map₂CochainComplex` / `map₂CochainComplex` 的定义

English:
abbreviation map₂CochainComplex
  body: F.map₂HomologicalComplex _ _ _

中文:
缩写 map₂CochainComplex
  定义体: F.map₂HomologicalComplex _ _ _

Depends on / 依赖: F.map
-/
noncomputable abbrev map₂CochainComplex
    [forall (K₁ : CochainComplex C₁ Int) (K₂ : CochainComplex C₂ Int), HasMapBifunctor K₁ K₂ F (.up Int)] :
    CochainComplex C₁ Int ⥤ CochainComplex C₂ Int ⥤ CochainComplex D Int :=
  F.map₂HomologicalComplex _ _ _

end CategoryTheory.Functor
