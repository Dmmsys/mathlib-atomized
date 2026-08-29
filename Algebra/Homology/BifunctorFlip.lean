/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-!
# Action of the flip of a bifunctor on homological complexes

Given `K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂`,
a bifunctor `F : C₁ ⥤ C₂ ⥤ D`, and a complex shape `c` with
`[TotalComplexShape c₁ c₂ c]` and `[TotalComplexShape c₂ c₁ c]`, we define
an isomorphism `mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c`
under the additional assumption `[TotalComplexShapeSymmetry c₁ c₂ c]`.

-/

@[expose] public section

open CategoryTheory Limits

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

namespace HomologicalComplex

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (φ₁ : K₁ ⟶ L₁)
  (K₂ L₂ : HomologicalComplex C₂ c₂) (φ₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [forall X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
  [TotalComplexShapeSymmetry c₁ c₂ c]

/--
lemma `hasMapBifunctor_flip_iff` / 引理 `hasMapBifunctor_flip_iff`

English:
lemma hasMapBifunctor_flip_iff
  proof: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_hasTotal_iff c

中文:
引理 hasMapBifunctor_flip_iff
  证明: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_hasTotal_iff c

Depends on / 依赖: F.mapBifunctorHomologicalComplex, flip_hasTotal_iff, mapBifunctorHomologicalComplex
-/
lemma hasMapBifunctor_flip_iff :
    HasMapBifunctor K₂ K₁ F.flip c ↔ HasMapBifunctor K₁ K₂ F c :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_hasTotal_iff c

variable [DecidableEq J] [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasMapBifunctor K₂ K₁ F.flip c
  body: by
  rw [hasMapBifunctor_flip_iff]
  infer_instance

中文:
实例 :
  签名: HasMapBifunctor K₂ K₁ F.flip c
  定义体: by
  rw [hasMapBifunctor_flip_iff]
  infer_instance

Depends on / 依赖: hasMapBifunctor_flip_iff, infer_instance
-/
instance : HasMapBifunctor K₂ K₁ F.flip c := by
  rw [hasMapBifunctor_flip_iff]
  infer_instance

/--
Definition of `mapBifunctorFlipIso` / `mapBifunctorFlipIso` 的定义

English:
definition mapBifunctorFlipIso
  signature: :
  body: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).totalFlipIso c

@[reassoc (attr := simp)]

中文:
定义 mapBifunctorFlipIso
  签名: :
  定义体: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).totalFlipIso c

@[reassoc (attr := simp)]

Depends on / 依赖: F.mapBifunctorHomologicalComplex, mapBifunctorHomologicalComplex, totalFlipIso
-/
noncomputable def mapBifunctorFlipIso :
    mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).totalFlipIso c

@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctorFlipIso_hom` / 引理 `ι_mapBifunctorFlipIso_hom`

English:
lemma ι_mapBifunctorFlipIso_hom
  given: (i₁ : I₁) (i₂ : I₂) (j : J) (hj : c₂.π c₁ c (i₂, i₁) = j)
  proof: HomologicalComplex₂.ιTotal_totalFlipIso_f_hom
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂) c i₁ i₂ j hj

@[reassoc (attr := simp)]

中文:
引理 ι_mapBifunctorFlipIso_hom
  条件: (i₁ : I₁) (i₂ : I₂) (j : J) (hj : c₂.π c₁ c (i₂, i₁) = j)
  证明: HomologicalComplex₂.ιTotal_totalFlipIso_f_hom
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂) c i₁ i₂ j hj

@[reassoc (attr := simp)]

Depends on / 依赖: F.mapBifunctorHomologicalComplex, mapBifunctorHomologicalComplex
-/
lemma ι_mapBifunctorFlipIso_hom (i₁ : I₁) (i₂ : I₂) (j : J) (hj : c₂.π c₁ c (i₂, i₁) = j) :
    ιMapBifunctor K₂ K₁ F.flip c i₂ i₁ j hj ≫ (mapBifunctorFlipIso K₁ K₂ F c).hom.f j =
      c₁.σ c₂ c i₁ i₂ • ιMapBifunctor K₁ K₂ F c i₁ i₂ j
        (by rw [← ComplexShape.π_symm c₁ c₂ c i₁ i₂, hj]) :=
  HomologicalComplex₂.ιTotal_totalFlipIso_f_hom
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂) c i₁ i₂ j hj

@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctorFlipIso_inv` / 引理 `ι_mapBifunctorFlipIso_inv`

English:
lemma ι_mapBifunctorFlipIso_inv
  given: (i₁ : I₁) (i₂ : I₂) (j : J) (hj : c₁.π c₂ c (i₁, i₂) = j)
  proof: HomologicalComplex₂.ιTotal_totalFlipIso_f_inv
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂) c i₁ i₂ j hj

中文:
引理 ι_mapBifunctorFlipIso_inv
  条件: (i₁ : I₁) (i₂ : I₂) (j : J) (hj : c₁.π c₂ c (i₁, i₂) = j)
  证明: HomologicalComplex₂.ιTotal_totalFlipIso_f_inv
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂) c i₁ i₂ j hj

Depends on / 依赖: F.mapBifunctorHomologicalComplex, mapBifunctorHomologicalComplex
-/
lemma ι_mapBifunctorFlipIso_inv (i₁ : I₁) (i₂ : I₂) (j : J) (hj : c₁.π c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j hj ≫ (mapBifunctorFlipIso K₁ K₂ F c).inv.f j =
      c₁.σ c₂ c i₁ i₂ • ιMapBifunctor K₂ K₁ F.flip c i₂ i₁ j
        (by rw [ComplexShape.π_symm c₁ c₂ c i₁ i₂, hj]) :=
  HomologicalComplex₂.ιTotal_totalFlipIso_f_inv
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂) c i₁ i₂ j hj

/--
lemma `mapBifunctorFlipIso_flip` / 引理 `mapBifunctorFlipIso_flip`

English:
lemma mapBifunctorFlipIso_flip
  proof: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_totalFlipIso c

中文:
引理 mapBifunctorFlipIso_flip
  证明: (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_totalFlipIso c

Depends on / 依赖: F.mapBifunctorHomologicalComplex, flip_totalFlipIso, mapBifunctorHomologicalComplex
-/
lemma mapBifunctorFlipIso_flip
    [TotalComplexShapeSymmetry c₂ c₁ c] [TotalComplexShapeSymmetrySymmetry c₁ c₂ c] :
    mapBifunctorFlipIso K₂ K₁ F.flip c = (mapBifunctorFlipIso K₁ K₂ F c).symm :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_totalFlipIso c

set_option backward.isDefEq.respectTransparency false in
variable {K₁ K₂ L₁ L₂} in
@[reassoc (attr := simp)]
/--
lemma `mapBifunctorFlipIso_hom_naturality` / 引理 `mapBifunctorFlipIso_hom_naturality`

English:
lemma mapBifunctorFlipIso_hom_naturality
  proof: by
  cat_disch

中文:
引理 mapBifunctorFlipIso_hom_naturality
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma mapBifunctorFlipIso_hom_naturality :
      mapBifunctorMap φ₂ φ₁ F.flip c ≫ (mapBifunctorFlipIso L₁ L₂ F c).hom =
    (mapBifunctorFlipIso K₁ K₂ F c).hom ≫ mapBifunctorMap φ₁ φ₂ F c := by
  cat_disch

end HomologicalComplex
