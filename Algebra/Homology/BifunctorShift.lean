/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.TotalComplexShift
public import Mathlib.CategoryTheory.Shift.CommShiftTwo

/-!
# Behavior of the action of a bifunctor on cochain complexes with respect to shifts

In this file, given cochain complexes `K₁ : CochainComplex C₁ ℤ`, `K₂ : CochainComplex C₂ ℤ` and
a functor `F : C₁ ⥤ C₂ ⥤ D`, we define an isomorphism of cochain complexes in `D`:
- `CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F x` of type
  `mapBifunctor (K₁⟦x⟧) K₂ F ≅ (mapBifunctor K₁ K₂ F)⟦x⟧` for `x : ℤ`.
- `CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F y` of type
  `mapBifunctor K₁ (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦y⟧` for `y : ℤ`.

In the lemma `CochainComplex.mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso`, we obtain
that the two ways to deduce an isomorphism
`mapBifunctor (K₁⟦x⟧) (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦x + y⟧` differ by the sign
`(x * y).negOnePow`.

These definitions and properties can be summarised by saying that the bifunctor
`F.map₂CochainComplex : CochainComplex C₁ ℤ ⥤ CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ`
commutes with shifts by `ℤ`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits HomologicalComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

namespace CochainComplex

section

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂]
  (K₁ : CochainComplex C₁ Int) (K₂ : CochainComplex C₂ Int) [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [forall (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]

/--
Definition of `HasMapBifunctor` / `HasMapBifunctor` 的定义

English:
abbreviation HasMapBifunctor
  body: HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up Int)

中文:
缩写 HasMapBifunctor
  定义体: HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up Int)

Depends on / 依赖: ComplexShape, ComplexShape.up, HasMapBifunctor, HomologicalComplex, HomologicalComplex.HasMapBifunctor
-/
abbrev HasMapBifunctor := HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up Int)

/--
Definition of `mapBifunctor` / `mapBifunctor` 的定义

English:
abbreviation mapBifunctor
  signature: [HasMapBifunctor K₁ K₂ F]
  body: HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up Int)

中文:
缩写 mapBifunctor
  签名: [HasMapBifunctor K₁ K₂ F]
  定义体: HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up Int)

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplex, HomologicalComplex.mapBifunctor, mapBifunctor
-/
noncomputable abbrev mapBifunctor [HasMapBifunctor K₁ K₂ F] : CochainComplex D Int :=
  HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up Int)

/--
Definition of `ιMapBifunctor` / `ιMapBifunctor` 的定义

English:
abbreviation ιMapBifunctor
  signature: [HasMapBifunctor K₁ K₂ F] (n₁ n₂ n : Int) (h : n₁ + n₂ = n)
  body: HomologicalComplex.ιMapBifunctor K₁ K₂ F _ _ _ _ h

中文:
缩写 ιMapBifunctor
  签名: [HasMapBifunctor K₁ K₂ F] (n₁ n₂ n : 整数) (h : n₁ + n₂ = n)
  定义体: HomologicalComplex.ιMapBifunctor K₁ K₂ F _ _ _ _ h

Depends on / 依赖: HomologicalComplex
-/
noncomputable abbrev ιMapBifunctor [HasMapBifunctor K₁ K₂ F] (n₁ n₂ n : Int) (h : n₁ + n₂ = n) :
    (F.obj (K₁.X n₁)).obj (K₂.X n₂) ⟶ (mapBifunctor K₁ K₂ F).X n :=
  HomologicalComplex.ιMapBifunctor K₁ K₂ F _ _ _ _ h

end

section

variable [Preadditive C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : CochainComplex C₁ Int) (f₁ : K₁ ⟶ L₁) (K₂ : CochainComplex C₂ Int)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [forall (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms] (x : Int)
  [HasMapBifunctor K₁ K₂ F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `mapBifunctorShift₁Iso`. -/
@[simps! hom_f_f inv_f_f]
/--
Definition of `mapBifunctorHomologicalComplexShift₁Iso` / `mapBifunctorHomologicalComplexShift₁Iso` 的定义

English:
definition mapBifunctorHomologicalComplexShift₁Iso
  signature: :
  body: HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intros
    ext
    dsimp
    simp only [Linear.comp_units_smul, id_comp, Functor.map_units_smul,
      NatTrans.app_units_zsmul, comp_id])

中文:
定义 mapBifunctorHomologicalComplexShift₁Iso
  签名: :
  定义体: HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intros
    ext
    dsimp
    simp only [Linear.comp_units_smul, id_comp, Functor.map_units_smul,
      NatTrans.app_units_zsmul, comp_id])

Depends on / 依赖: Functor, Functor.isHomological_of_localization, Functor.map_units_smul, HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, Iso.refl, Linear, Linear.comp_units_smul, NatTrans, NatTrans.app_units_zsmul, app_units_zsmul, comp_id, comp_units_smul, homologyFunctor, homologyFunctorFactorsh, id_comp, intros, isHomological_of_localization, isoOfComponents, map_units_smul
-/
def mapBifunctorHomologicalComplexShift₁Iso :
    ((F.mapBifunctorHomologicalComplex _ _).obj (K₁⟦x⟧)).obj K₂ ≅
    (HomologicalComplex₂.shiftFunctor₁ D x).obj
      (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intros
    ext
    dsimp
    simp only [Linear.comp_units_smul, id_comp, Functor.map_units_smul,
      NatTrans.app_units_zsmul, comp_id])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasMapBifunctor (K₁⟦x⟧) K₂ F
  body: HomologicalComplex₂.hasTotal_of_iso (mapBifunctorHomologicalComplexShift₁Iso K₁ K₂ F x).symm _

中文:
实例 :
  签名: HasMapBifunctor (K₁⟦x⟧) K₂ F
  定义体: HomologicalComplex₂.hasTotal_of_iso (mapBifunctorHomologicalComplexShift₁Iso K₁ K₂ F x).symm _

Depends on / 依赖: hasTotal_of_iso
-/
instance : HasMapBifunctor (K₁⟦x⟧) K₂ F :=
  HomologicalComplex₂.hasTotal_of_iso (mapBifunctorHomologicalComplexShift₁Iso K₁ K₂ F x).symm _

/--
Definition of `mapBifunctorShift₁Iso` / `mapBifunctorShift₁Iso` 的定义

English:
definition mapBifunctorShift₁Iso
  signature: :
  body: HomologicalComplex₂.total.mapIso (mapBifunctorHomologicalComplexShift₁Iso K₁ K₂ F x) _ ≪≫
    (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂).totalShift₁Iso x

中文:
定义 mapBifunctorShift₁Iso
  签名: :
  定义体: HomologicalComplex₂.total.mapIso (mapBifunctorHomologicalComplexShift₁Iso K₁ K₂ F x) _ ≪≫
    (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂).totalShift₁Iso x

Depends on / 依赖: F.mapBifunctorHomologicalComplex, mapBifunctorHomologicalComplex, mapIso, total.mapIso
-/
noncomputable def mapBifunctorShift₁Iso :
    mapBifunctor (K₁⟦x⟧) K₂ F ≅ (mapBifunctor K₁ K₂ F)⟦x⟧ :=
  HomologicalComplex₂.total.mapIso (mapBifunctorHomologicalComplexShift₁Iso K₁ K₂ F x) _ ≪≫
    (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂).totalShift₁Iso x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `ι_mapBifunctorShift₁Iso_hom_f` / 引理 `ι_mapBifunctorShift₁Iso_hom_f`

English:
lemma ι_mapBifunctorShift₁Iso_hom_f
  statement: (n₁ n₂ n : Int) (h : n₁ + n₂ = n)
  proof: by
  dsimp [mapBifunctorShift₁Iso]
  simp only [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ι_totalShift₁Iso_hom_f _ _ _ _ _ _ _ hm₁ _ hm]
  simp [HomologicalComplex₂.ιTotal, HomologicalComplex₂.shiftFunctor₁XXIso,
    HomologicalComplex.XIsoOfEq, eqToHom_map]

中文:
引理 ι_mapBifunctorShift₁Iso_hom_f
  结论: (n₁ n₂ n : 整数) (h : n₁ + n₂ = n)
  证明: by
  dsimp [mapBifunctorShift₁Iso]
  simp only [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ι_totalShift₁Iso_hom_f _ _ _ _ _ _ _ hm₁ _ hm]
  simp [HomologicalComplex₂.ιTotal, HomologicalComplex₂.shiftFunctor₁XXIso,
    HomologicalComplex.XIsoOfEq, eqToHom_map]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.XIsoOfEq, XIsoOfEq, eqToHom_map
-/
lemma ι_mapBifunctorShift₁Iso_hom_f (n₁ n₂ n : Int) (h : n₁ + n₂ = n)
    (m₁ m : Int) (hm₁ : m₁ = n₁ + x) (hm : m = n + x) :
    ιMapBifunctor _ K₂ F n₁ n₂ n h ≫ (mapBifunctorShift₁Iso K₁ K₂ F x).hom.f n =
      (F.map (shiftFunctorObjXIso K₁ x n₁ m₁ hm₁).hom).app _ ≫
        ιMapBifunctor K₁ K₂ F m₁ n₂ m (by lia) ≫
          (shiftFunctorObjXIso (mapBifunctor K₁ K₂ F) x n m hm).inv := by
  dsimp [mapBifunctorShift₁Iso]
  simp only [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ι_totalShift₁Iso_hom_f _ _ _ _ _ _ _ hm₁ _ hm]
  simp [HomologicalComplex₂.ιTotal, HomologicalComplex₂.shiftFunctor₁XXIso,
    HomologicalComplex.XIsoOfEq, eqToHom_map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {K₁ L₁} in
@[reassoc (attr := simp)]
/--
lemma `mapBifunctorShift₁Iso_hom_naturality₁` / 引理 `mapBifunctorShift₁Iso_hom_naturality₁`

English:
lemma mapBifunctorShift₁Iso_hom_naturality₁
  given: [HasMapBifunctor L₁ K₂ F]
  proof: by
  ext n p q h
  simp [ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _ (p + x) (n + x) rfl rfl,
    ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ _ _ _ _ _ _ (p + x) (n + x) rfl rfl]

中文:
引理 mapBifunctorShift₁Iso_hom_naturality₁
  条件: [HasMapBifunctor L₁ K₂ F]
  证明: by
  ext n p q h
  simp [ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _ (p + x) (n + x) rfl rfl,
    ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ _ _ _ _ _ _ (p + x) (n + x) rfl rfl]
-/
lemma mapBifunctorShift₁Iso_hom_naturality₁ [HasMapBifunctor L₁ K₂ F] :
    mapBifunctorMap (f₁⟦x⟧') (𝟙 K₂) F (.up Int) ≫ (mapBifunctorShift₁Iso L₁ K₂ F x).hom =
      (mapBifunctorShift₁Iso K₁ K₂ F x).hom ≫ mapBifunctorMap f₁ (𝟙 K₂) F (.up Int)⟦x⟧' := by
  ext n p q h
  simp [ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _ (p + x) (n + x) rfl rfl,
    ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ _ _ _ _ _ _ (p + x) (n + x) rfl rfl]

end

section

variable [HasZeroMorphisms C₁] [Preadditive C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ Int) (K₂ L₂ : CochainComplex C₂ Int) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [forall (X₁ : C₁), (F.obj X₁).Additive] (y : Int)
  [HasMapBifunctor K₁ K₂ F]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `mapBifunctorShift₂Iso`. -/
@[simps! hom_f_f inv_f_f]
/--
Definition of `mapBifunctorHomologicalComplexShift₂Iso` / `mapBifunctorHomologicalComplexShift₂Iso` 的定义

English:
definition mapBifunctorHomologicalComplexShift₂Iso
  signature: :
  body: HomologicalComplex.Hom.isoOfComponents
    (fun i₁ => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)) (by
      intros
      ext
      dsimp
      simp only [id_comp, comp_id])

中文:
定义 mapBifunctorHomologicalComplexShift₂Iso
  签名: :
  定义体: HomologicalComplex.Hom.isoOfComponents
    (fun i₁ => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)) (by
      intros
      ext
      dsimp
      simp only [id_comp, comp_id])

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, Iso.refl, comp_id, id_comp, intros, isoOfComponents
-/
def mapBifunctorHomologicalComplexShift₂Iso :
    ((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj (K₂⟦y⟧) ≅
    (HomologicalComplex₂.shiftFunctor₂ D y).obj
      (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i₁ => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)) (by
      intros
      ext
      dsimp
      simp only [id_comp, comp_id])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasMapBifunctor K₁ (K₂⟦y⟧) F
  body: HomologicalComplex₂.hasTotal_of_iso (mapBifunctorHomologicalComplexShift₂Iso K₁ K₂ F y).symm _

中文:
实例 :
  签名: HasMapBifunctor K₁ (K₂⟦y⟧) F
  定义体: HomologicalComplex₂.hasTotal_of_iso (mapBifunctorHomologicalComplexShift₂Iso K₁ K₂ F y).symm _

Depends on / 依赖: hasTotal_of_iso
-/
instance : HasMapBifunctor K₁ (K₂⟦y⟧) F :=
  HomologicalComplex₂.hasTotal_of_iso (mapBifunctorHomologicalComplexShift₂Iso K₁ K₂ F y).symm _

/--
Definition of `mapBifunctorShift₂Iso` / `mapBifunctorShift₂Iso` 的定义

English:
definition mapBifunctorShift₂Iso
  signature: :
  body: HomologicalComplex₂.total.mapIso
    (mapBifunctorHomologicalComplexShift₂Iso K₁ K₂ F y) (ComplexShape.up Int) ≪≫
    (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂).totalShift₂Iso y

中文:
定义 mapBifunctorShift₂Iso
  签名: :
  定义体: HomologicalComplex₂.total.mapIso
    (mapBifunctorHomologicalComplexShift₂Iso K₁ K₂ F y) (ComplexShape.up Int) ≪≫
    (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂).totalShift₂Iso y

Depends on / 依赖: ComplexShape, ComplexShape.up, F.mapBifunctorHomologicalComplex, mapBifunctorHomologicalComplex, mapIso, total.mapIso
-/
noncomputable def mapBifunctorShift₂Iso :
    mapBifunctor K₁ (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦y⟧ :=
  HomologicalComplex₂.total.mapIso
    (mapBifunctorHomologicalComplexShift₂Iso K₁ K₂ F y) (ComplexShape.up Int) ≪≫
    (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂).totalShift₂Iso y

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `ι_mapBifunctorShift₂Iso_hom_f` / 引理 `ι_mapBifunctorShift₂Iso_hom_f`

English:
lemma ι_mapBifunctorShift₂Iso_hom_f
  statement: (n₁ n₂ n : Int) (h : n₁ + n₂ = n)
  proof: by
  dsimp [mapBifunctorShift₂Iso]
  simp only [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ι_totalShift₂Iso_hom_f _ _ _ _ _ _ _ hm₂ _ hm]
  simp [HomologicalComplex₂.ιTotal, HomologicalComplex₂.shiftFunctor₂XXIso,
    HomologicalComplex.XIsoOfEq, eqToHom_map]

中文:
引理 ι_mapBifunctorShift₂Iso_hom_f
  结论: (n₁ n₂ n : 整数) (h : n₁ + n₂ = n)
  证明: by
  dsimp [mapBifunctorShift₂Iso]
  simp only [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ι_totalShift₂Iso_hom_f _ _ _ _ _ _ _ hm₂ _ hm]
  simp [HomologicalComplex₂.ιTotal, HomologicalComplex₂.shiftFunctor₂XXIso,
    HomologicalComplex.XIsoOfEq, eqToHom_map]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.XIsoOfEq, XIsoOfEq, eqToHom_map
-/
lemma ι_mapBifunctorShift₂Iso_hom_f (n₁ n₂ n : Int) (h : n₁ + n₂ = n)
    (m₂ m : Int) (hm₂ : m₂ = n₂ + y) (hm : m = n + y) :
    ιMapBifunctor K₁ _ F n₁ n₂ n h ≫ (mapBifunctorShift₂Iso K₁ K₂ F y).hom.f n =
      (n₁ * y).negOnePow • (F.obj _).map (shiftFunctorObjXIso K₂ y n₂ m₂ hm₂).hom ≫
        ιMapBifunctor K₁ K₂ F n₁ m₂ m (by lia) ≫
        (shiftFunctorObjXIso (mapBifunctor K₁ K₂ F) y n m hm).inv := by
  dsimp [mapBifunctorShift₂Iso]
  simp only [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ι_totalShift₂Iso_hom_f _ _ _ _ _ _ _ hm₂ _ hm]
  simp [HomologicalComplex₂.ιTotal, HomologicalComplex₂.shiftFunctor₂XXIso,
    HomologicalComplex.XIsoOfEq, eqToHom_map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {K₂ L₂} in
@[reassoc (attr := simp)]
/--
lemma `mapBifunctorShift₂Iso_hom_naturality₂` / 引理 `mapBifunctorShift₂Iso_hom_naturality₂`

English:
lemma mapBifunctorShift₂Iso_hom_naturality₂
  given: [HasMapBifunctor K₁ L₂ F]
  proof: by
  ext n p q h
  simp [ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl,
    ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl]

中文:
引理 mapBifunctorShift₂Iso_hom_naturality₂
  条件: [HasMapBifunctor K₁ L₂ F]
  证明: by
  ext n p q h
  simp [ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl,
    ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl]
-/
lemma mapBifunctorShift₂Iso_hom_naturality₂ [HasMapBifunctor K₁ L₂ F] :
    mapBifunctorMap (𝟙 K₁) (f₂⟦y⟧') F (.up Int) ≫ (mapBifunctorShift₂Iso K₁ L₂ F y).hom =
      (mapBifunctorShift₂Iso K₁ K₂ F y).hom ≫ mapBifunctorMap (𝟙 K₁) f₂ F (.up Int)⟦y⟧' := by
  ext n p q h
  simp [ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl,
    ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl]

end

section

variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ Int) (K₂ : CochainComplex C₂ Int)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [forall (X₁ : C₁), (F.obj X₁).Additive] (x y : Int)
  [HasMapBifunctor K₁ K₂ F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso` / 引理 `mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso`

English:
lemma mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso
  proof: by
  ext1
  dsimp [mapBifunctorShift₁Iso, mapBifunctorShift₂Iso]
  rw [Functor.map_comp]; rw [Functor.map_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [← HomologicalComplex₂.totalShift₁Iso_hom_naturality_assoc]; rw [HomologicalComplex₂.totalShift₁Iso_hom_totalShift₂Iso_hom]; rw [← HomologicalComple

中文:
引理 mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso
  证明: by
  ext1
  dsimp [mapBifunctorShift₁Iso, mapBifunctorShift₂Iso]
  rw [Functor.map_comp]; rw [Functor.map_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [← HomologicalComplex₂.totalShift₁Iso_hom_naturality_assoc]; rw [HomologicalComplex₂.totalShift₁Iso_hom_totalShift₂Iso_hom]; rw [← HomologicalComple

Depends on / 依赖: Functor, Functor.map_comp, Linear, Linear.comp_units_smul, comp_units_smul, map_comp, map_comp_assoc, smul_left_cancel_iff, total.map_comp_assoc
-/
lemma mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso :
    mapBifunctorShift₁Iso K₁ (K₂⟦y⟧) F x ≪≫
      (CategoryTheory.shiftFunctor _ x).mapIso (mapBifunctorShift₂Iso K₁ K₂ F y) =
      (x * y).negOnePow • (mapBifunctorShift₂Iso (K₁⟦x⟧) K₂ F y ≪≫
        (CategoryTheory.shiftFunctor _ y).mapIso (mapBifunctorShift₁Iso K₁ K₂ F x) ≪≫
          (shiftFunctorComm (CochainComplex D Int) x y).app _) := by
  ext1
  dsimp [mapBifunctorShift₁Iso, mapBifunctorShift₂Iso]
  rw [Functor.map_comp]; rw [Functor.map_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [← HomologicalComplex₂.totalShift₁Iso_hom_naturality_assoc]; rw [HomologicalComplex₂.totalShift₁Iso_hom_totalShift₂Iso_hom]; rw [← HomologicalComplex₂.totalShift₂Iso_hom_naturality_assoc]; rw [Linear.comp_units_smul]; rw [Linear.comp_units_smul]; rw [smul_left_cancel_iff]; rw [← HomologicalComplex₂.total.map_comp_assoc]; rw [← HomologicalComplex₂.total.map_comp_assoc]; rw [← HomologicalComplex₂.total.map_comp_assoc]
  congr 2
  ext a b
  dsimp [HomologicalComplex₂.shiftFunctor₁₂CommIso]
  simp only [id_comp]

end

end CochainComplex

namespace CategoryTheory.Functor

variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [forall (X₁ : C₁), (F.obj X₁).Additive]
  [forall (K₁ : CochainComplex C₁ Int) (K₂ : CochainComplex C₂ Int),
    CochainComplex.HasMapBifunctor K₁ K₂ F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable instance (K₁ : CochainComplex C₁ Int) :
    (F.map₂CochainComplex.obj K₁).CommShift Int where
  commShiftIso n :=
    NatIso.ofComponents (fun K₂ => CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F n)
  commShiftIso_zero := by
    ext K₂ n
    dsimp
    ext p q h
    simp [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ F 0 p q n h q n (by lia) (by lia),
      CochainComplex.shiftFunctorZero_eq]
  commShiftIso_add a b := by
    ext K₂ n
    dsimp
    ext p q h
    dsimp at h
    simp [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ F (a + b) p q n h
        (q + a + b) (n + a + b) (by lia) (by lia),
      CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ F b p q n h _ _ rfl rfl,
      CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ F a p (q + b) (n + b)
        (by lia) (q + a + b) (n + a + b) (by lia) (by lia), smul_smul,
        ← Int.negOnePow_add, CochainComplex.shiftFunctorAdd_eq,
        add_comm (p * b), mul_add, XIsoOfEq]

/--
lemma `commShiftIso_map₂CochainComplex_hom_app` / 引理 `commShiftIso_map₂CochainComplex_hom_app`

English:
lemma commShiftIso_map₂CochainComplex_hom_app
  statement: (K₁ : CochainComplex C₁ Int)
  proof: rfl

中文:
引理 commShiftIso_map₂CochainComplex_hom_app
  结论: (K₁ : 上链复形 C₁ 整数)
  证明: rfl
-/
lemma commShiftIso_map₂CochainComplex_hom_app (K₁ : CochainComplex C₁ Int)
    (K₂ : CochainComplex C₂ Int) (n : Int) :
    ((F.map₂CochainComplex.obj K₁).commShiftIso n).hom.app K₂ =
      (CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F n).hom := rfl

/--
lemma `commShiftIso_map₂CochainComplex_inv_app` / 引理 `commShiftIso_map₂CochainComplex_inv_app`

English:
lemma commShiftIso_map₂CochainComplex_inv_app
  statement: (K₁ : CochainComplex C₁ Int)
  proof: rfl

中文:
引理 commShiftIso_map₂CochainComplex_inv_app
  结论: (K₁ : 上链复形 C₁ 整数)
  证明: rfl
-/
lemma commShiftIso_map₂CochainComplex_inv_app (K₁ : CochainComplex C₁ Int)
    (K₂ : CochainComplex C₂ Int) (n : Int) :
    ((F.map₂CochainComplex.obj K₁).commShiftIso n).inv.app K₂ =
      (CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F n).inv := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance {K₁ L₁ : CochainComplex C₁ Int} (f : K₁ ⟶ L₁) :
    NatTrans.CommShift (F.map₂CochainComplex.map f) Int where
  shift_comm n := by
    ext K₂ d
    dsimp
    ext p q h
    simp [commShiftIso_map₂CochainComplex_hom_app,
      CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + n) (d + n) rfl rfl,
      CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ _ _ _ _ _ _ (q + n) (d + n) rfl rfl]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable instance (K₂ : CochainComplex C₂ Int) :
    (F.map₂CochainComplex.flip.obj K₂).CommShift Int where
  commShiftIso n :=
    NatIso.ofComponents (fun K₁ => CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F n)
  commShiftIso_zero := by
    ext K₂ n
    dsimp
    ext p q h
    simp [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ F 0 p q n h p n
      (by lia) (by lia), CochainComplex.shiftFunctorZero_eq]
  commShiftIso_add a b := by
    ext K₂ n
    dsimp
    ext p q h
    dsimp at h
    simp [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ F (a + b) p q n h
        (p + a + b) (n + a + b) (by lia) (by lia),
      CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ F b p q n h _ _ rfl rfl,
      CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ F a (p + b) q (n + b)
        (by lia) (p + a + b) (n + a + b) (by lia) (by lia),
      CochainComplex.shiftFunctorAdd_eq, XIsoOfEq, eqToHom_map]

/--
lemma `commShiftIso_map₂CochainComplex_flip_hom_app` / 引理 `commShiftIso_map₂CochainComplex_flip_hom_app`

English:
lemma commShiftIso_map₂CochainComplex_flip_hom_app
  statement: (K₁ : CochainComplex C₁ Int)
  proof: rfl

中文:
引理 commShiftIso_map₂CochainComplex_flip_hom_app
  结论: (K₁ : 上链复形 C₁ 整数)
  证明: rfl
-/
lemma commShiftIso_map₂CochainComplex_flip_hom_app (K₁ : CochainComplex C₁ Int)
    (K₂ : CochainComplex C₂ Int) (n : Int) :
    ((F.map₂CochainComplex.flip.obj K₂).commShiftIso n).hom.app K₁ =
      (CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F n).hom := rfl

/--
lemma `commShiftIso_map₂CochainComplex_flip_inv_app` / 引理 `commShiftIso_map₂CochainComplex_flip_inv_app`

English:
lemma commShiftIso_map₂CochainComplex_flip_inv_app
  statement: (K₁ : CochainComplex C₁ Int)
  proof: rfl

中文:
引理 commShiftIso_map₂CochainComplex_flip_inv_app
  结论: (K₁ : 上链复形 C₁ 整数)
  证明: rfl
-/
lemma commShiftIso_map₂CochainComplex_flip_inv_app (K₁ : CochainComplex C₁ Int)
    (K₂ : CochainComplex C₂ Int) (n : Int) :
    ((F.map₂CochainComplex.flip.obj K₂).commShiftIso n).inv.app K₁ =
      (CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F n).inv := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance {K₂ L₂ : CochainComplex C₂ Int} (g : K₂ ⟶ L₂) :
    NatTrans.CommShift (F.map₂CochainComplex.flip.map g) Int where
  shift_comm n := by
    ext K₁ d
    dsimp
    ext p q h
    simp [commShiftIso_map₂CochainComplex_flip_hom_app,
      CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _ (p + n) (d + n) rfl rfl,
      CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ _ _ _ _ _ _ (p + n) (d + n) rfl rfl]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: by
    have := congr_arg Iso.hom
      (CochainComplex.mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso K₁ K₂ F p q)
    dsimp at this
    simp [commShiftIso_map₂CochainComplex_hom_app,
      commShiftIso_map₂CochainComplex_flip_hom_app,
      reassoc_of% this, smul_smul]

中文:
实例 :
  定义体: by
    have := congr_arg Iso.hom
      (CochainComplex.mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso K₁ K₂ F p q)
    dsimp at this
    simp [commShiftIso_map₂CochainComplex_hom_app,
      commShiftIso_map₂CochainComplex_flip_hom_app,
      reassoc_of% this, smul_smul]

Depends on / 依赖: CochainComplex, CochainComplex.mapBifunctorShift, Iso.hom, congr_arg, reassoc_of, smul_smul
-/
noncomputable instance :
    F.map₂CochainComplex.CommShift₂Int where
  comm K₁ K₂ p q := by
    have := congr_arg Iso.hom
      (CochainComplex.mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso K₁ K₂ F p q)
    dsimp at this
    simp [commShiftIso_map₂CochainComplex_hom_app,
      commShiftIso_map₂CochainComplex_flip_hom_app,
      reassoc_of% this, smul_smul]

end CategoryTheory.Functor
