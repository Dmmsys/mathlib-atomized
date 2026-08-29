/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The distinguished triangle of a short exact sequence in an abelian category

Given a short exact short complex `S` in an abelian category, we construct
the associated distinguished triangle in the derived category:
`(singleFunctor C 0).obj S.X₁ ⟶ (singleFunctor C 0).obj S.X₂ ⟶ (singleFunctor C 0).obj S.X₃ ⟶ ...`

## TODO
* when the canonical t-structure on the derived category is formalized, refactor
  this definition to make it a particular case of the triangle induced by a short
  exact sequence in the heart of a t-structure

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open Category DerivedCategory Pretriangulated

namespace ShortComplex

variable {S : ShortComplex C} (hS : S.ShortExact)

namespace ShortExact

/--
Definition of `singleδ` / `singleδ` 的定义

English:
definition singleδ
  signature: : (singleFunctor C 0).obj S.X₃ ⟶
  body: (((SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)).hom.app S.X₃) ≫
    triangleOfSESδ (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up Int) 0)) ≫
    (((SingleFunctors.evaluation _ _ 0).mapIso
      (singleFunctorsPostcompQIso C)).inv.app S.X₁)⟦(1 : Int)⟧'

中文:
定义 singleδ
  签名: : (singleFunctor C 0).obj S.X₃ ⟶
  定义体: (((SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)).hom.app S.X₃) ≫
    triangleOfSESδ (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up Int) 0)) ≫
    (((SingleFunctors.evaluation _ _ 0).mapIso
      (singleFunctorsPostcompQIso C)).inv.app S.X₁)⟦(1 : Int)⟧'

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplex, HomologicalComplex.single, SingleFunctors, SingleFunctors.evaluation, evaluation, hS.map_of_exact, hom.app, inv.app, mapIso, map_of_exact, single, singleFunctorsPostcompQIso
-/
noncomputable def singleδ : (singleFunctor C 0).obj S.X₃ ⟶
    ((singleFunctor C 0).obj S.X₁)⟦(1 : Int)⟧ :=
  (((SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)).hom.app S.X₃) ≫
    triangleOfSESδ (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up Int) 0)) ≫
    (((SingleFunctors.evaluation _ _ 0).mapIso
      (singleFunctorsPostcompQIso C)).inv.app S.X₁)⟦(1 : Int)⟧'

/-- The (distinguished) triangle in the derived category of `C` given by a
short exact short complex in `C`. -/
@[simps!]
/--
Definition of `singleTriangle` / `singleTriangle` 的定义

English:
definition singleTriangle
  signature: : Triangle (DerivedCategory C)
  body: Triangle.mk ((singleFunctor C 0).map S.f)
    ((singleFunctor C 0).map S.g) hS.singleδ

中文:
定义 singleTriangle
  签名: : Triangle (导出范畴 C)
  定义体: Triangle.mk ((singleFunctor C 0).map S.f)
    ((singleFunctor C 0).map S.g) hS.singleδ

Depends on / 依赖: Triangle, Triangle.mk, hS.single, singleFunctor
-/
noncomputable def singleTriangle : Triangle (DerivedCategory C) :=
  Triangle.mk ((singleFunctor C 0).map S.f)
    ((singleFunctor C 0).map S.g) hS.singleδ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a short exact complex `S` in `C` that is short exact (`hS`), this is the
canonical isomorphism between the triangle `hS.singleTriangle` in the derived category
and the triangle attached to the corresponding short exact sequence of cochain complexes
after the application of the single functor. -/
@[simps!]
/--
Definition of `singleTriangleIso` / `singleTriangleIso` 的定义

English:
definition singleTriangleIso
  signature: :
  body: by
  let e := (SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)
  refine Triangle.isoMk _ _ (e.app S.X₁) (e.app S.X₂) (e.app S.X₃) ?_ ?_ ?_
  · cat_disch
  · cat_disch
  · simp [singleδ, e, ← Functor.map_comp, CochainComplex.singleFunctors]

中文:
定义 singleTriangleIso
  签名: :
  定义体: by
  let e := (SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)
  refine Triangle.isoMk _ _ (e.app S.X₁) (e.app S.X₂) (e.app S.X₃) ?_ ?_ ?_
  · cat_disch
  · cat_disch
  · simp [singleδ, e, ← Functor.map_comp, CochainComplex.singleFunctors]

Depends on / 依赖: CochainComplex, CochainComplex.singleFunctors, Functor, Functor.map_comp, SingleFunctors, SingleFunctors.evaluation, Triangle, Triangle.isoMk, cat_disch, e.app, evaluation, mapIso, map_comp, singleFunctors, singleFunctorsPostcompQIso
-/
noncomputable def singleTriangleIso :
    hS.singleTriangle ≅
      triangleOfSES (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up Int) 0)) := by
  let e := (SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)
  refine Triangle.isoMk _ _ (e.app S.X₁) (e.app S.X₂) (e.app S.X₃) ?_ ?_ ?_
  · cat_disch
  · cat_disch
  · simp [singleδ, e, ← Functor.map_comp, CochainComplex.singleFunctors]

/--
lemma `singleTriangle_distinguished` / 引理 `singleTriangle_distinguished`

English:
lemma singleTriangle_distinguished
  proof: isomorphic_distinguished _ (triangleOfSES_distinguished (hS.map_of_exact
    (HomologicalComplex.single C (ComplexShape.up Int) 0))) _ (singleTriangleIso hS)

中文:
引理 singleTriangle_distinguished
  证明: isomorphic_distinguished _ (triangleOfSES_distinguished (hS.map_of_exact
    (HomologicalComplex.single C (ComplexShape.up Int) 0))) _ (singleTriangleIso hS)

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplex, HomologicalComplex.single, hS.map_of_exact, isomorphic_distinguished, map_of_exact, single, singleTriangleIso, triangleOfSES_distinguished
-/
lemma singleTriangle_distinguished :
    hS.singleTriangle in distTriang (DerivedCategory C) :=
  isomorphic_distinguished _ (triangleOfSES_distinguished (hS.map_of_exact
    (HomologicalComplex.single C (ComplexShape.up Int) 0))) _ (singleTriangleIso hS)

variable {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism `h₁.singleTriangle h₁ ⟶ h₂.singleTriangle` that is induced by a
map of short exact sequences of objects of `C`.
-/
@[simps!]
/--
Definition of `singleTriangle.map` / `singleTriangle.map` 的定义

English:
definition singleTriangle.map
  signature: : h₁.singleTriangle ⟶ h₂.singleTriangle where
  body: (singleFunctor C 0).map f.τ₁
  hom₂ := (singleFunctor C 0).map f.τ₂
  hom₃ := (singleFunctor C 0).map f.τ₃
  comm₁ := by simp [← Functor.map_comp, f.comm₁₂]
  comm₂ := by simp [← Functor.map_comp, f.comm₂₃]
  comm₃ := by
    dsimp [singleδ]
    rw [assoc]; rw [assoc]; rw [← Functor.map_comp]; rw [← 

中文:
定义 singleTriangle.map
  签名: : h₁.singleTriangle ⟶ h₂.singleTriangle where
  定义体: (singleFunctor C 0).map f.τ₁
  hom₂ := (singleFunctor C 0).map f.τ₂
  hom₃ := (singleFunctor C 0).map f.τ₃
  comm₁ := by simp [← Functor.map_comp, f.comm₁₂]
  comm₂ := by simp [← Functor.map_comp, f.comm₂₃]
  comm₃ := by
    dsimp [singleδ]
    rw [assoc]; rw [assoc]; rw [← Functor.map_comp]; rw [← 

Depends on / 依赖: singleFunctor
-/
noncomputable def singleTriangle.map : h₁.singleTriangle ⟶ h₂.singleTriangle where
  hom₁ := (singleFunctor C 0).map f.τ₁
  hom₂ := (singleFunctor C 0).map f.τ₂
  hom₃ := (singleFunctor C 0).map f.τ₃
  comm₁ := by simp [← Functor.map_comp, f.comm₁₂]
  comm₂ := by simp [← Functor.map_comp, f.comm₂₃]
  comm₃ := by
    dsimp [singleδ]
    rw [assoc]; rw [assoc]; rw [← Functor.map_comp]; rw [← NatTrans.naturality]; rw [Functor.map_comp]
    dsimp [CochainComplex.singleFunctors]
    rw [reassoc_of% dsimp% ((triangleOfSES.map (h₁.map_of_exact _) (h₂.map_of_exact _))
      ((HomologicalComplex.single C (.up Int) 0).mapShortComplex.map f)).comm₃]
    simp

end ShortExact

end ShortComplex

end CategoryTheory
