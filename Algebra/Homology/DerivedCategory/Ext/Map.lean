/-
Copyright (c) 2025 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Map between Ext groups induced by an exact functor

In this file, we define the map `Ext^k (M, N) → Ext^k (F(M), F(N))`,
where `F` is an exact functor between abelian categories.

# Main Definition and results

* `CategoryTheory.Abelian.Ext.mapExactFunctor` : The map between `Ext` induced by
  `CategoryTheory.LocalizerMorphism.smallShiftedHomMap`.

* `CategoryTheory.Functor.mapExtAddHom` : Upgraded of `CategoryTheory.Abelian.Ext.mapExactFunctor`
  into an additive homomorphism.

* `CategoryTheory.Functor.mapExtLinearMap` : Upgrade of `F.mapExtAddHom` assuming `F` is linear.

* `Ext.mapExactFunctor_mk₀` : `Ext.mapExactFunctor` commutes with `Ext.mk₀`

* `Ext.mapExactFunctor_comp` : `Ext.mapExactFunctor` preserves `Ext.comp`

* `mapExactFunctor_extClass` :
  `Ext.mapExactFunctor` commutes with `ShortComplex.ShortExact.extClass`

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe t t' w w' u u' v v'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

section

open DerivedCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `DerivedCategory.map_triangleOfSESδ` / 引理 `DerivedCategory.map_triangleOfSESδ`

English:
lemma DerivedCategory.map_triangleOfSESδ
  statement: [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
  proof: by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  rw [← cancel_epi (F.mapDerivedCategory.map
    (Q.map (CochainComplex.mappingCone.descShortComplex S)))]; rw [← Functor.map_comp]; rw [descShortComplex_triangleOfSESδ]; rw [F.mapDerivedCategoryFactors_hom_naturality_assoc]; rw [← CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex]; rw [Functor.map_comp_assoc]; rw [descShortComplex_triangleOfSESδ_assoc]
  dsimp
  rw [← Functor.map_comp_assoc]
  rw [← CochainComplex.mappingCone.map_δ]; rw [Functor.map_comp_assoc]; rw [← F.mapDerivedCategoryFactors_hom_naturality_assoc]; rw [Functor.map_comp]
  simp [NatTrans.shift_app, Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app,
    ← Functor.map_comp_assoc]

中文:
引理 导出范畴.map_triangleOfSESδ
  结论: [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
  证明: by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  rw [← cancel_epi (F.mapDerivedCategory.map
    (Q.map (CochainComplex.mappingCone.descShortComplex S)))]; rw [← Functor.map_comp]; rw [descShortComplex_triangleOfSESδ]; rw [F.mapDerivedCategoryFactors_hom_naturality_assoc]; rw [← CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex]; rw [Functor.map_comp_assoc]; rw [descShortComplex_triangleOfSESδ_assoc]
  dsimp
  rw [← Functor.map_comp_assoc]
  rw [← CochainComplex.mappingCone.map_δ]; rw [Functor.map_comp_assoc]; rw [← F.mapDerivedCategoryFactors_hom_naturality_assoc]; rw [Functor.map_comp]
  simp [NatTrans.shift_app, Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app,
    ← Functor.map_comp_assoc]

Depends on / 依赖: CochainComplex, CochainComplex.map, CochainComplex.mappingCone.descShortComplex, CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex, CochainComplex.mappingCone.quasiIso_descShortComplex, F.mapDerivedCategory.map, F.mapDerivedCategoryFactors_hom_naturality_assoc, Functor, Functor.map_comp, Functor.map_comp_assoc, Q.map, cancel_epi, descShortComplex, mapDerivedCategory, mapDerivedCategoryFactors_hom_naturality_assoc, mapHomologicalComplexIso_hom_descShortComplex, map_comp, map_comp_assoc, mappingCone, quasiIso_descShortComplex
-/
lemma DerivedCategory.map_triangleOfSESδ [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    {S : ShortComplex (CochainComplex C Int)} (hS : S.ShortExact) :
    dsimp% F.mapDerivedCategory.map (triangleOfSESδ hS) =
    (F.mapDerivedCategoryFactors.hom.app S.X₃) ≫
      triangleOfSESδ (hS.map_of_exact (F.mapHomologicalComplex _)) ≫
        (F.mapDerivedCategoryFactors.inv.app S.X₁)⟦1⟧' ≫
          (F.mapDerivedCategory.commShiftIso (1 : Int)).inv.app (Q.obj S.X₁) := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  rw [← cancel_epi (F.mapDerivedCategory.map
    (Q.map (CochainComplex.mappingCone.descShortComplex S)))]; rw [← Functor.map_comp]; rw [descShortComplex_triangleOfSESδ]; rw [F.mapDerivedCategoryFactors_hom_naturality_assoc]; rw [← CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex]; rw [Functor.map_comp_assoc]; rw [descShortComplex_triangleOfSESδ_assoc]
  dsimp
  rw [← Functor.map_comp_assoc]
  rw [← CochainComplex.mappingCone.map_δ]; rw [Functor.map_comp_assoc]; rw [← F.mapDerivedCategoryFactors_hom_naturality_assoc]; rw [Functor.map_comp]
  simp [NatTrans.shift_app, Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app,
    ← Functor.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `ShortComplex.ShortExact.mapShiftedHom_singleδ'` / 引理 `ShortComplex.ShortExact.mapShiftedHom_singleδ'`

English:
lemma ShortComplex.ShortExact.mapShiftedHom_singleδ'
  proof: by
  dsimp [ShiftedHom.map, ShortComplex.ShortExact.singleδ]
  simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality,
    DerivedCategory.map_triangleOfSESδ, singleFunctorsPostcompQIso_hom_hom,
    singleFunctorsPostcompQIso_inv_hom]
  generalize_proofs _ _ _ _ _ _ h1 _ _ h2
  dsimp [CochainComplex.singleFunctors]
  rw [Functor.map_id]; rw [Category.id_comp]; rw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Functor.map_id]; rw [Functor.map_id]; rw [Category.id_comp]; rw [← Functor.map_comp]; rw [F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]; rw [dsimp% triangleOfSESδ_naturality h1 h2
      (S.mapNatTrans (F.mapCochainComplexSingleFunctor 0).hom)]; rw [← Functor.map_comp_assoc]
  simp

#adaptation_note

中文:
引理 短复形.短正合.mapShiftedHom_singleδ'
  证明: by
  dsimp [ShiftedHom.map, ShortComplex.ShortExact.singleδ]
  simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality,
    DerivedCategory.map_triangleOfSESδ, singleFunctorsPostcompQIso_hom_hom,
    singleFunctorsPostcompQIso_inv_hom]
  generalize_proofs _ _ _ _ _ _ h1 _ _ h2
  dsimp [CochainComplex.singleFunctors]
  rw [Functor.map_id]; rw [Category.id_comp]; rw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Functor.map_id]; rw [Functor.map_id]; rw [Category.id_comp]; rw [← Functor.map_comp]; rw [F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]; rw [dsimp% triangleOfSESδ_naturality h1 h2
      (S.mapNatTrans (F.mapCochainComplexSingleFunctor 0).hom)]; rw [← Functor.map_comp_assoc]
  simp

#adaptation_note

Depends on / 依赖: Category, Category.assoc, Category.id_comp, CochainComplex, CochainComplex.singleFunctors, DerivedCategory, DerivedCategory.map_triangleOfSES, Functor, Functor.commShiftIso_hom_naturality, Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc, Functor.map_comp, Functor.map_id, Iso.inv_hom_id_app_assoc, ShiftedHom, ShiftedHom.map, ShortComplex, ShortComplex.ShortExact.single, ShortExact, commShiftIso_hom_naturality, generalize_proofs
-/
lemma ShortComplex.ShortExact.mapShiftedHom_singleδ'
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    {S : ShortComplex C} (hS : S.ShortExact) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (F.mapDerivedCategorySingleFunctor 0).inv.app S.X₃ ≫
      ShiftedHom.map hS.singleδ F.mapDerivedCategory ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₁)⟦1⟧' =
    (hS.map_of_exact F).singleδ := by
  dsimp [ShiftedHom.map, ShortComplex.ShortExact.singleδ]
  simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality,
    DerivedCategory.map_triangleOfSESδ, singleFunctorsPostcompQIso_hom_hom,
    singleFunctorsPostcompQIso_inv_hom]
  generalize_proofs _ _ _ _ _ _ h1 _ _ h2
  dsimp [CochainComplex.singleFunctors]
  rw [Functor.map_id]; rw [Category.id_comp]; rw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Functor.map_id]; rw [Functor.map_id]; rw [Category.id_comp]; rw [← Functor.map_comp]; rw [F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]; rw [dsimp% triangleOfSESδ_naturality h1 h2
      (S.mapNatTrans (F.mapCochainComplexSingleFunctor 0).hom)]; rw [← Functor.map_comp_assoc]
  simp

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `ShortComplex.ShortExact.mapShiftedHom_singleδ` / 引理 `ShortComplex.ShortExact.mapShiftedHom_singleδ`

English:
lemma ShortComplex.ShortExact.mapShiftedHom_singleδ
  proof: by
  simp [← hS.mapShiftedHom_singleδ'_assoc, ← Functor.map_comp]

中文:
引理 短复形.短正合.mapShiftedHom_singleδ
  证明: by
  simp [← hS.mapShiftedHom_singleδ'_assoc, ← Functor.map_comp]

Depends on / 依赖: Functor, Functor.map_comp, _assoc, hS.mapShiftedHom_single, map_comp
-/
lemma ShortComplex.ShortExact.mapShiftedHom_singleδ
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    {S : ShortComplex C} (hS : S.ShortExact) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ShiftedHom.map hS.singleδ F.mapDerivedCategory =
      (F.mapDerivedCategorySingleFunctor 0).hom.app S.X₃ ≫
        (hS.map_of_exact F).singleδ ≫ ((F.mapDerivedCategorySingleFunctor 0).inv.app S.X₁)⟦1⟧' := by
  simp [← hS.mapShiftedHom_singleδ'_assoc, ← Functor.map_comp]

end

section Ext

open Localization

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : HasExt.{w'} D] (X Y : C) : HasSmallLocalizedShiftedHom.{w'}
  body: h (F.obj X) (F.obj Y)

中文:
实例 [h
  签名: : HasExt.{w'} D] (X Y : C) : HasSmallLocalizedShiftedHom.{w'}
  定义体: h (F.obj X) (F.obj Y)

Depends on / 依赖: F.obj
-/
instance [h : HasExt.{w'} D] (X Y : C) : HasSmallLocalizedShiftedHom.{w'}
    (HomologicalComplex.quasiIso D (ComplexShape.up Int)) Int
    ((F ⋙ CochainComplex.singleFunctor D 0).obj X)
    ((F ⋙ CochainComplex.singleFunctor D 0).obj Y) :=
  h (F.obj X) (F.obj Y)

/--
Definition of `Abelian.Ext.mapExactFunctor` / `Abelian.Ext.mapExactFunctor` 的定义

English:
definition Abelian.Ext.mapExactFunctor
  signature: [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : Nat}
  body: (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up Int)).smallShiftedHomMap
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y) f

中文:
定义 交换.Ext.mapExactFunctor
  签名: [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : 自然数}
  定义体: (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up Int)).smallShiftedHomMap
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y) f

Depends on / 依赖: ComplexShape, ComplexShape.up, F.mapCochainComplexSingleFunctor, F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism, mapCochainComplexSingleFunctor, mapHomologicalComplexUpToQuasiIsoLocalizerMorphism, smallShiftedHomMap
-/
noncomputable def Abelian.Ext.mapExactFunctor [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : Nat}
    (f : Ext.{w} X Y n) : Ext.{w'} (F.obj X) (F.obj Y) n :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up Int)).smallShiftedHomMap
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y) f

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Abelian.Ext.mapExactFunctor_hom` / 引理 `Abelian.Ext.mapExactFunctor_hom`

English:
lemma Abelian.Ext.mapExactFunctor_hom
  proof: by
  have : (e.mapExactFunctor F).hom = _ :=
    ((F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up Int)).equiv_smallShiftedHomMap DerivedCategory.Q DerivedCategory.Q
        ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
          F.mapDerivedCategory F.mapDerivedCategoryFactors.symm e)
  rw [this]; rw [← ShiftedHom.comp_mk₀ _ 0 rfl]; rw [← ShiftedHom.mk₀_comp 0 rfl]
  congr 2
  · simp [← F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  · simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      ← Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]

中文:
引理 交换.Ext.mapExactFunctor_hom
  证明: by
  have : (e.mapExactFunctor F).hom = _ :=
    ((F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up Int)).equiv_smallShiftedHomMap DerivedCategory.Q DerivedCategory.Q
        ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
          F.mapDerivedCategory F.mapDerivedCategoryFactors.symm e)
  rw [this]; rw [← ShiftedHom.comp_mk₀ _ 0 rfl]; rw [← ShiftedHom.mk₀_comp 0 rfl]
  congr 2
  · simp [← F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  · simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      ← Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]

Depends on / 依赖: ComplexShape, ComplexShape.up, DerivedCategory, DerivedCategory.Q, F.mapCochainComplexSingleFunctor, F.mapDerivedCategory, F.mapDerivedCategoryFactors.symm, F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_a, F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism, ShiftedHom, ShiftedHom.comp_mk, ShiftedHom.mk, e.mapExactFunctor, equiv_smallShiftedHomMap, mapCochainComplexSingleFunctor, mapDerivedCategory, mapDerivedCategoryFactors, mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_a, mapExactFunctor, mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
-/
lemma Abelian.Ext.mapExactFunctor_hom
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : Nat} (e : Ext X Y n) :
    (e.mapExactFunctor F).hom =
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ e.hom.map F.mapDerivedCategory ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : Int)⟧' := by
  have : (e.mapExactFunctor F).hom = _ :=
    ((F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up Int)).equiv_smallShiftedHomMap DerivedCategory.Q DerivedCategory.Q
        ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
          F.mapDerivedCategory F.mapDerivedCategoryFactors.symm e)
  rw [this]; rw [← ShiftedHom.comp_mk₀ _ 0 rfl]; rw [← ShiftedHom.mk₀_comp 0 rfl]
  congr 2
  · simp [← F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  · simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      ← Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]

section

attribute [local simp] Abelian.Ext.mapExactFunctor_hom
attribute [local instance] HasDerivedCategory.standard

variable [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : Nat)

@[simp]
/--
lemma `Abelian.Ext.mapExactFunctor_zero` / 引理 `Abelian.Ext.mapExactFunctor_zero`

English:
lemma Abelian.Ext.mapExactFunctor_zero
  statement: (0 : Ext X Y n).mapExactFunctor F = 0
  proof: by
  aesop

@[simp]

中文:
引理 交换.Ext.mapExactFunctor_zero
  结论: (0 : Ext X Y n).mapExactFunctor F = 0
  证明: by
  aesop

@[simp]
-/
lemma Abelian.Ext.mapExactFunctor_zero : (0 : Ext X Y n).mapExactFunctor F = 0 := by
  aesop

@[simp]
/--
lemma `Abelian.Ext.mapExactFunctor_add` / 引理 `Abelian.Ext.mapExactFunctor_add`

English:
lemma Abelian.Ext.mapExactFunctor_add
  given: (f g : Ext.{w} X Y n)
  proof: by
  aesop

中文:
引理 交换.Ext.mapExactFunctor_add
  条件: (f g : Ext.{w} X Y n)
  证明: by
  aesop
-/
lemma Abelian.Ext.mapExactFunctor_add (f g : Ext.{w} X Y n) :
    (f + g).mapExactFunctor F = f.mapExactFunctor F + g.mapExactFunctor F := by
  aesop

/--
Definition of `Functor.mapExtAddHom` / `Functor.mapExtAddHom` 的定义

English:
definition Functor.mapExtAddHom
  signature: (X Y : C) (n : Nat)
  body: e.mapExactFunctor F
  map_zero' := by simp
  map_add' := by simp

@[simp]

中文:
定义 函子.mapExtAddHom
  签名: (X Y : C) (n : 自然数)
  定义体: e.mapExactFunctor F
  map_zero' := by simp
  map_add' := by simp

@[simp]

Depends on / 依赖: e.mapExactFunctor, mapExactFunctor
-/
noncomputable def Functor.mapExtAddHom (X Y : C) (n : Nat) :
    Ext.{w} X Y n ->+ Ext.{w'} (F.obj X) (F.obj Y) n where
  toFun e := e.mapExactFunctor F
  map_zero' := by simp
  map_add' := by simp

@[simp]
/--
lemma `Functor.mapExtAddHom_coe` / 引理 `Functor.mapExtAddHom_coe`

English:
lemma Functor.mapExtAddHom_coe
  statement: ⇑(F.mapExtAddHom X Y n) = Ext.mapExactFunctor F
  proof: rfl

中文:
引理 函子.mapExtAddHom_coe
  结论: ⇑(F.mapExtAddHom X Y n) = Ext.mapExactFunctor F
  证明: rfl
-/
lemma Functor.mapExtAddHom_coe : ⇑(F.mapExtAddHom X Y n) = Ext.mapExactFunctor F := rfl

/--
lemma `Functor.mapExtAddHom_apply` / 引理 `Functor.mapExtAddHom_apply`

English:
lemma Functor.mapExtAddHom_apply
  given: (e : Ext X Y n)
  statement: F.mapExtAddHom X Y n e = e.mapExactFunctor F
  proof: rfl

中文:
引理 函子.mapExtAddHom_apply
  条件: (e : Ext X Y n)
  结论: F.mapExtAddHom X Y n e = e.mapExactFunctor F
  证明: rfl
-/
lemma Functor.mapExtAddHom_apply (e : Ext X Y n) : F.mapExtAddHom X Y n e = e.mapExactFunctor F :=
  rfl

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Linear R]

@[simp]
/--
lemma `Functor.mapExactFunctor_smul` / 引理 `Functor.mapExactFunctor_smul`

English:
lemma Functor.mapExactFunctor_smul
  given: (r : R) (f : Ext.{w} X Y n)
  proof: by
  aesop

中文:
引理 函子.mapExactFunctor_smul
  条件: (r : R) (f : Ext.{w} X Y n)
  证明: by
  aesop
-/
lemma Functor.mapExactFunctor_smul (r : R) (f : Ext.{w} X Y n) :
    (r • f).mapExactFunctor F = r • (f.mapExactFunctor F) := by
  aesop

/--
Definition of `Functor.mapExtLinearMap` / `Functor.mapExtLinearMap` 的定义

English:
definition Functor.mapExtLinearMap
  signature: (X Y : C) (n : Nat)
  body: F.mapExtAddHom X Y n
  map_smul' := by simp

@[simp]

中文:
定义 函子.mapExtLinearMap
  签名: (X Y : C) (n : 自然数)
  定义体: F.mapExtAddHom X Y n
  map_smul' := by simp

@[simp]

Depends on / 依赖: F.mapExtAddHom, mapExtAddHom
-/
noncomputable def Functor.mapExtLinearMap (X Y : C) (n : Nat) :
    Ext.{w} X Y n ->ₗ[R] Ext.{w'} (F.obj X) (F.obj Y) n where
  __ := F.mapExtAddHom X Y n
  map_smul' := by simp

@[simp]
/--
lemma `Functor.mapExtLinearMap_toAddMonoidHom` / 引理 `Functor.mapExtLinearMap_toAddMonoidHom`

English:
lemma Functor.mapExtLinearMap_toAddMonoidHom
  statement: F.mapExtLinearMap R X Y n = F.mapExtAddHom X Y n
  proof: rfl

中文:
引理 函子.mapExtLinearMap_toAddMonoidHom
  结论: F.mapExtLinearMap R X Y n = F.mapExtAddHom X Y n
  证明: rfl
-/
lemma Functor.mapExtLinearMap_toAddMonoidHom : F.mapExtLinearMap R X Y n = F.mapExtAddHom X Y n :=
  rfl

/--
lemma `Functor.mapExtLinearMap_coe` / 引理 `Functor.mapExtLinearMap_coe`

English:
lemma Functor.mapExtLinearMap_coe
  statement: ⇑(F.mapExtLinearMap R X Y n) = Ext.mapExactFunctor F
  proof: rfl

中文:
引理 函子.mapExtLinearMap_coe
  结论: ⇑(F.mapExtLinearMap R X Y n) = Ext.mapExactFunctor F
  证明: rfl
-/
lemma Functor.mapExtLinearMap_coe : ⇑(F.mapExtLinearMap R X Y n) = Ext.mapExactFunctor F := rfl

/--
lemma `Functor.mapExtLinearMap_apply` / 引理 `Functor.mapExtLinearMap_apply`

English:
lemma Functor.mapExtLinearMap_apply
  given: (e : Ext X Y n)
  proof: rfl

中文:
引理 函子.mapExtLinearMap_apply
  条件: (e : Ext X Y n)
  证明: rfl
-/
lemma Functor.mapExtLinearMap_apply (e : Ext X Y n) :
    F.mapExtLinearMap R X Y n e = e.mapExactFunctor F := rfl

end

namespace Abelian.Ext

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mapExactFunctor_mk₀` / 引理 `mapExactFunctor_mk₀`

English:
lemma mapExactFunctor_mk₀
  given: [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} (f : X ⟶ Y)
  proof: by
  dsimp [Ext.mapExactFunctor, mk₀]
  rw [(F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up Int)).smallShiftedHomMap_mk₀
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    (0 : Int) rfl]
  congr
  simpa only [Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism_functor,
    Functor.mapCochainComplexSingleFunctor, Iso.app_inv, Iso.app_hom] using! NatIso.naturality_1 _ f

中文:
引理 mapExactFunctor_mk₀
  条件: [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} (f : X ⟶ Y)
  证明: by
  dsimp [Ext.mapExactFunctor, mk₀]
  rw [(F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up Int)).smallShiftedHomMap_mk₀
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    (0 : Int) rfl]
  congr
  simpa only [Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism_functor,
    Functor.mapCochainComplexSingleFunctor, Iso.app_inv, Iso.app_hom] using! NatIso.naturality_1 _ f

Depends on / 依赖: Ext.mapExactFunctor, F.mapCochainComplexSingleFunctor, F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism, Functor, Functor.mapCochainComplexSingleFunctor, Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism_functor, Iso.app_hom, Iso.app_inv, NatIso, NatIso.naturality_1, app_hom, app_inv, mapCochainComplexSingleFunctor, mapExactFunctor, mapHomologicalComplexUpToQuasiIsoLocalizerMorphism, mapHomologicalComplexUpToQuasiIsoLocalizerMorphism_functor, naturality_1
-/
lemma mapExactFunctor_mk₀ [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} (f : X ⟶ Y) :
    (mk₀ f).mapExactFunctor F = mk₀ (F.map f) := by
  dsimp [Ext.mapExactFunctor, mk₀]
  rw [(F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up Int)).smallShiftedHomMap_mk₀
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    (0 : Int) rfl]
  congr
  simpa only [Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism_functor,
    Functor.mapCochainComplexSingleFunctor, Iso.app_inv, Iso.app_hom] using! NatIso.naturality_1 _ f

/--
lemma `mapExactFunctor₀` / 引理 `mapExactFunctor₀`

English:
lemma mapExactFunctor₀
  given: [HasExt.{w} C] [HasExt.{w'} D] (X Y : C)
  proof: by
  ext x
  rcases (Ext.mk₀_bijective X Y).2 x with ⟨y, hy⟩
  simp [← hy, Ext.mapExactFunctor_mk₀, Ext.homEquiv₀]

中文:
引理 mapExactFunctor₀
  条件: [HasExt.{w} C] [HasExt.{w'} D] (X Y : C)
  证明: by
  ext x
  rcases (Ext.mk₀_bijective X Y).2 x with ⟨y, hy⟩
  simp [← hy, Ext.mapExactFunctor_mk₀, Ext.homEquiv₀]

Depends on / 依赖: Ext.homEquiv, Ext.mapExactFunctor_mk, Ext.mk, F.map
-/
lemma mapExactFunctor₀ [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) :
    Ext.mapExactFunctor F (X := X) (Y := Y) = Ext.homEquiv₀.symm ∘ F.map ∘ Ext.homEquiv₀ := by
  ext x
  rcases (Ext.mk₀_bijective X Y).2 x with ⟨y, hy⟩
  simp [← hy, Ext.mapExactFunctor_mk₀, Ext.homEquiv₀]

/--
lemma `mapExactFunctor_comp` / 引理 `mapExactFunctor_comp`

English:
lemma mapExactFunctor_comp
  statement: [HasExt.{w} C] [HasExt.{w'} D] {X Y Z : C} {a b : Nat}
  proof: (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up Int)).smallShiftedHomMap_comp _
    ((F.mapCochainComplexSingleFunctor 0).app Y) _ α β (show b + a = (c : Int) by grind)

中文:
引理 mapExactFunctor_comp
  结论: [HasExt.{w} C] [HasExt.{w'} D] {X Y Z : C} {a b : 自然数}
  证明: (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up Int)).smallShiftedHomMap_comp _
    ((F.mapCochainComplexSingleFunctor 0).app Y) _ α β (show b + a = (c : Int) by grind)

Depends on / 依赖: F.mapCochainComplexSingleFunctor, F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism, mapCochainComplexSingleFunctor, mapHomologicalComplexUpToQuasiIsoLocalizerMorphism, smallShiftedHomMap_comp
-/
lemma mapExactFunctor_comp [HasExt.{w} C] [HasExt.{w'} D] {X Y Z : C} {a b : Nat}
    (α : Ext X Y a) (β : Ext Y Z b) {c : Nat} (h : a + b = c) :
    (α.comp β h).mapExactFunctor F = (α.mapExactFunctor F).comp (β.mapExactFunctor F) h :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up Int)).smallShiftedHomMap_comp _
    ((F.mapCochainComplexSingleFunctor 0).app Y) _ α β (show b + a = (c : Int) by grind)

attribute [local instance] HasDerivedCategory.standard in
/--
lemma `mapExactFunctor_extClass` / 引理 `mapExactFunctor_extClass`

English:
lemma mapExactFunctor_extClass
  statement: [HasExt.{w} C] [HasExt.{w'} D] {S : ShortComplex C}
  proof: by
  ext
  rw [Ext.mapExactFunctor_hom]; rw [hS.extClass_hom]
  exact (hS.mapShiftedHom_singleδ' F).trans (hS.map_of_exact F).extClass_hom.symm

中文:
引理 mapExactFunctor_extClass
  结论: [HasExt.{w} C] [HasExt.{w'} D] {S : 短复形 C}
  证明: by
  ext
  rw [Ext.mapExactFunctor_hom]; rw [hS.extClass_hom]
  exact (hS.mapShiftedHom_singleδ' F).trans (hS.map_of_exact F).extClass_hom.symm

Depends on / 依赖: Ext.mapExactFunctor_hom, extClass_hom, extClass_hom.symm, hS.extClass_hom, hS.mapShiftedHom_single, hS.map_of_exact, mapExactFunctor_hom, map_of_exact
-/
lemma mapExactFunctor_extClass [HasExt.{w} C] [HasExt.{w'} D] {S : ShortComplex C}
    (hS : S.ShortExact) : hS.extClass.mapExactFunctor F = (hS.map_of_exact F).extClass := by
  ext
  rw [Ext.mapExactFunctor_hom]; rw [hS.extClass_hom]
  exact (hS.mapShiftedHom_singleδ' F).trans (hS.map_of_exact F).extClass_hom.symm

end Abelian.Ext

end Ext

end CategoryTheory
