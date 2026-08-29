/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# Singular homology

In this file, we define the singular chain complex and singular homology of a topological space.
We also calculate the homology of a totally disconnected space as an example.

-/

@[expose] public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory Limits

universe w v u

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C]
variable [Preadditive C] (n : Nat)

/--
Definition of `singularChainComplexFunctor` / `singularChainComplexFunctor` 的定义

English:
definition singularChainComplexFunctor
  signature: :
  body: SSet.chainComplexFunctor.{w} C ⋙ (Functor.whiskeringLeft _ _ _).obj TopCat.toSSet.{w}

中文:
定义 singularChainComplexFunctor
  签名: :
  定义体: SSet.chainComplexFunctor.{w} C ⋙ (Functor.whiskeringLeft _ _ _).obj TopCat.toSSet.{w}

Depends on / 依赖: Functor, Functor.whiskeringLeft, SSet.chainComplexFunctor, TopCat, TopCat.toSSet, chainComplexFunctor, toSSet, whiskeringLeft
-/
def singularChainComplexFunctor :
    C ⥤ TopCat.{w} ⥤ ChainComplex C Nat :=
  SSet.chainComplexFunctor.{w} C ⋙ (Functor.whiskeringLeft _ _ _).obj TopCat.toSSet.{w}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (singularChainComplexFunctor C).Additive
  body: by
  delta singularChainComplexFunctor
  infer_instance

中文:
实例 :
  签名: (singularChainComplexFunctor C).加性
  定义体: by
  delta singularChainComplexFunctor
  infer_instance

Depends on / 依赖: infer_instance, singularChainComplexFunctor
-/
instance : (singularChainComplexFunctor C).Additive := by
  delta singularChainComplexFunctor
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Limits.HasPullbacks
  signature: C] {X
  body: by
    dsimp [singularChainComplexFunctor, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
    apply +allowSynthFailures Functor.map_mono
    dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
    infer_instance

中文:
实例 [Limits.有Pullbacks
  签名: C] {X
  定义体: by
    dsimp [singularChainComplexFunctor, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
    apply +allowSynthFailures Functor.map_mono
    dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
    infer_instance

Depends on / 依赖: Functor, Functor.map_mono, SSet.chainComplexFunctor, SimplicialObject, SimplicialObject.whiskering, allowSynthFailures, chainComplexFunctor, infer_instance, map_mono, singularChainComplexFunctor, whiskering
-/
instance [Limits.HasPullbacks C] {X : C} :
    ((singularChainComplexFunctor C).obj X).PreservesMonomorphisms where
  preserves f _ := by
    dsimp [singularChainComplexFunctor, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
    apply +allowSynthFailures Functor.map_mono
    dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
    infer_instance

/--
Definition of `singularHomologyFunctor` / `singularHomologyFunctor` 的定义

English:
definition singularHomologyFunctor
  signature: [CategoryWithHomology C]
  body: singularChainComplexFunctor C ⋙
    (Functor.whiskeringRight _ _ _).obj (HomologicalComplex.homologyFunctor _ _ n)

中文:
定义 singularHomologyFunctor
  签名: [带同调范畴 C]
  定义体: singularChainComplexFunctor C ⋙
    (Functor.whiskeringRight _ _ _).obj (HomologicalComplex.homologyFunctor _ _ n)

Depends on / 依赖: Functor, Functor.whiskeringRight, HomologicalComplex, HomologicalComplex.homologyFunctor, homologyFunctor, singularChainComplexFunctor, whiskeringRight
-/
def singularHomologyFunctor [CategoryWithHomology C] : C ⥤ TopCat.{w} ⥤ C :=
  singularChainComplexFunctor C ⋙
    (Functor.whiskeringRight _ _ _).obj (HomologicalComplex.homologyFunctor _ _ n)

section Adjunction

open Limits _root_.SSet
open scoped Simplicial
open HomologicalComplex (eval)

/--
Definition of `singularChainComplexFunctorAdjunction` / `singularChainComplexFunctorAdjunction` 的定义

English:
definition singularChainComplexFunctorAdjunction
  signature: : (Functor.postcompose₂.obj (eval _ _ n)).obj
  body: ((SSet.chainComplexFunctorAdjunction C n).comp (sSetTopAdj.whiskerLeft _)).ofNatIsoRight
    ((evaluation TopCat C).mapIso (SSet.toTopSimplex.app _))

中文:
定义 singularChainComplexFunctorAdjunction
  签名: : (函子.postcompose₂.obj (eval _ _ n)).obj
  定义体: ((SSet.chainComplexFunctorAdjunction C n).comp (sSetTopAdj.whiskerLeft _)).ofNatIsoRight
    ((evaluation TopCat C).mapIso (SSet.toTopSimplex.app _))

Depends on / 依赖: SSet.chainComplexFunctorAdjunction, SSet.toTopSimplex.app, TopCat, chainComplexFunctorAdjunction, evaluation, mapIso, ofNatIsoRight, sSetTopAdj, sSetTopAdj.whiskerLeft, toTopSimplex, whiskerLeft
-/
def singularChainComplexFunctorAdjunction : (Functor.postcompose₂.obj (eval _ _ n)).obj
    (singularChainComplexFunctor C) ⊣ (evaluation _ _).obj (SimplexCategory.toTop.obj ⦋n⦌) :=
  ((SSet.chainComplexFunctorAdjunction C n).comp (sSetTopAdj.whiskerLeft _)).ofNatIsoRight
    ((evaluation TopCat C).mapIso (SSet.toTopSimplex.app _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `singularChainComplexFunctorAdjunction_unit_app` / 引理 `singularChainComplexFunctorAdjunction_unit_app`

English:
lemma singularChainComplexFunctorAdjunction_unit_app
  given: (R : C)
  proof: by
  dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
    Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
    Adjunction.comp, singularChainComplexFunctor,
    SSet.chainComplexFunctorAdjunction, SSet.chainComplexFunctor]
  simp [stdSimplexToTop]
  rfl

中文:
引理 singularChainComplexFunctorAdjunction_unit_app
  条件: (R : C)
  证明: by
  dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
    Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
    Adjunction.comp, singularChainComplexFunctor,
    SSet.chainComplexFunctorAdjunction, SSet.chainComplexFunctor]
  simp [stdSimplexToTop]
  rfl

Depends on / 依赖: Adjunction, Adjunction.comp, Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv, Adjunction.ofNatIsoRight, SSet.chainComplexFunctor, SSet.chainComplexFunctorAdjunction, chainComplexFunctor, chainComplexFunctorAdjunction, equivHomsetRightOfNatIso, homEquiv, ofNatIsoRight, singularChainComplexFunctor, singularChainComplexFunctorAdjunction, stdSimplexToTop
-/
lemma singularChainComplexFunctorAdjunction_unit_app (R : C) :
    (singularChainComplexFunctorAdjunction C n).unit.app R =
      Sigma.ι (fun _ => R) ((stdSimplexToTop.app ⦋n⦌).app (.op ⦋n⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) := by
  dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
    Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
    Adjunction.comp, singularChainComplexFunctor,
    SSet.chainComplexFunctorAdjunction, SSet.chainComplexFunctor]
  simp [stdSimplexToTop]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ι_singularChainComplexFunctorAdjunction_counit_app_app` / 引理 `ι_singularChainComplexFunctorAdjunction_counit_app_app`

English:
lemma ι_singularChainComplexFunctorAdjunction_counit_app_app
  given: (F : TopCat ⥤ C) (X : TopCat) (i)
  proof: by
  trans F.map (SSet.toTopSimplex.inv.app ⦋n⦌ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm i) ≫
      sSetTopAdj.counit.app X)
  · dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
      Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
      Adjunction.comp, singularChain

中文:
引理 ι_singularChainComplexFunctorAdjunction_counit_app_app
  条件: (F : 顶元素范畴 ⥤ C) (X : 顶元素范畴) (i)
  证明: by
  trans F.map (SSet.toTopSimplex.inv.app ⦋n⦌ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm i) ≫
      sSetTopAdj.counit.app X)
  · dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
      Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
      Adjunction.comp, singularChain

Depends on / 依赖: Adjunction, Adjunction.comp, Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv, Adjunction.ofNatIsoRight, F.map, SSet.chainComplexFunctor, SSet.chainComplexFunctorAdjunction, SSet.toTop.map, SSet.toTopSimplex.inv.app, SSet.yonedaEquiv.symm, chainComplexFunctor, chainComplexFunctorAdjunction, counit, equivHomsetRightOfNatIso, homEquiv, ofNatIsoRight, reassoc_of, right_triangle_components, sSetTopAdj
-/
lemma ι_singularChainComplexFunctorAdjunction_counit_app_app (F : TopCat ⥤ C) (X : TopCat) (i) :
    Sigma.ι _ i ≫ ((singularChainComplexFunctorAdjunction C n).counit.app F).app X =
      F.map i.down := by
  trans F.map (SSet.toTopSimplex.inv.app ⦋n⦌ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm i) ≫
      sSetTopAdj.counit.app X)
  · dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
      Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
      Adjunction.comp, singularChainComplexFunctor, SSet.chainComplexFunctor,
      SSet.chainComplexFunctorAdjunction]
    simp
  · congr 1
    rw [← reassoc_of% sSetTopAdj_unit_app_app_down]
    exact congr(($(sSetTopAdj.right_triangle_components X).app (.op ⦋n⦌) i).down)

end Adjunction

section TotallyDisconnectedSpace

variable (R : C) (X : TopCat.{w}) [TotallyDisconnectedSpace X]

/-- If `X` is totally disconnected,
its singular chain complex is given by `R[X] ←0- R[X] ←𝟙- R[X] ←0- R[X] ⋯`,
where `R[X]` is the coproduct of copies of `R` indexed by elements of `X`. -/
noncomputable
/--
Definition of `singularChainComplexFunctorIsoOfTotallyDisconnectedSpace` / `singularChainComplexFunctorIsoOfTotallyDisconnectedSpace` 的定义

English:
definition singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
  signature: :
  body: (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (((SimplicialObject.whiskering _ _).obj _).mapIso
    (TopCat.toSSetIsoConst X) ≪≫ Functor.constComp _ _ _) ≪≫
    AlgebraicTopology.alternatingFaceMapComplexConst.app _

中文:
定义 singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
  签名: :
  定义体: (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (((SimplicialObject.whiskering _ _).obj _).mapIso
    (TopCat.toSSetIsoConst X) ≪≫ Functor.constComp _ _ _) ≪≫
    AlgebraicTopology.alternatingFaceMapComplexConst.app _

Depends on / 依赖: AlgebraicTopology, AlgebraicTopology.alternatingFaceMapComplex, AlgebraicTopology.alternatingFaceMapComplexConst.app, Functor, Functor.constComp, SimplicialObject, SimplicialObject.whiskering, TopCat, TopCat.toSSetIsoConst, alternatingFaceMapComplex, alternatingFaceMapComplexConst, constComp, mapIso, toSSetIsoConst, whiskering
-/
def singularChainComplexFunctorIsoOfTotallyDisconnectedSpace :
    ((singularChainComplexFunctor C).obj R).obj X ≅
      (ChainComplex.alternatingConst.obj (∐ fun _ : X => R)) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (((SimplicialObject.whiskering _ _).obj _).mapIso
    (TopCat.toSSetIsoConst X) ≪≫ Functor.constComp _ _ _) ≪≫
    AlgebraicTopology.alternatingFaceMapComplexConst.app _

/--
lemma `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace` / 引理 `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace`

English:
lemma singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
  proof: have := hasCoproducts_shrink.{0, w} (C := C)
  have : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  .of_iso (ChainComplex.alternatingConst_exactAt _ _ hn)
    (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X).symm

中文:
引理 singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
  证明: have := hasCoproducts_shrink.{0, w} (C := C)
  have : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  .of_iso (ChainComplex.alternatingConst_exactAt _ _ hn)
    (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X).symm

Depends on / 依赖: ChainComplex, ChainComplex.alternatingConst_exactAt, HasZeroObject, alternatingConst_exactAt, hasCoproducts_shrink, initialIsInitial, initialIsInitial.isZero, isZero, of_iso, singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
-/
lemma singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
    (hn : n != 0) :
    (((singularChainComplexFunctor C).obj R).obj X).ExactAt n :=
  have := hasCoproducts_shrink.{0, w} (C := C)
  have : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  .of_iso (ChainComplex.alternatingConst_exactAt _ _ hn)
    (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X).symm

/--
lemma `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` / 引理 `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`

English:
lemma isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
  proof: have := hasCoproducts_shrink.{0, w} (C := C)
  have : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  (singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace C n R X hn).isZero_homology

中文:
引理 isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
  证明: have := hasCoproducts_shrink.{0, w} (C := C)
  have : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  (singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace C n R X hn).isZero_homology

Depends on / 依赖: HasZeroObject, hasCoproducts_shrink, initialIsInitial, initialIsInitial.isZero, isZero, isZero_homology, singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
-/
lemma isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    [CategoryWithHomology C] (hn : n != 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj X) :=
  have := hasCoproducts_shrink.{0, w} (C := C)
  have : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  (singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace C n R X hn).isZero_homology

/-- The zeroth singular homology of a totally disconnected space is the
free `R`-module generated by elements of `X`. -/
noncomputable
/--
Definition of `singularHomologyFunctorZeroOfTotallyDisconnectedSpace` / `singularHomologyFunctorZeroOfTotallyDisconnectedSpace` 的定义

English:
definition singularHomologyFunctorZeroOfTotallyDisconnectedSpace
  signature: [CategoryWithHomology C]
  body: have : HasZeroObject C :=
    have := hasCoproducts_shrink.{0, w} (C := C)
    ⟨_, initialIsInitial.isZero⟩
  (HomologicalComplex.homologyFunctor _ _ 0).mapIso
      (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X) ≪≫
    ChainComplex.alternatingConstHomologyZero _

中文:
定义 singularHomologyFunctorZeroOfTotallyDisconnectedSpace
  签名: [带同调范畴 C]
  定义体: have : HasZeroObject C :=
    have := hasCoproducts_shrink.{0, w} (C := C)
    ⟨_, initialIsInitial.isZero⟩
  (HomologicalComplex.homologyFunctor _ _ 0).mapIso
      (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X) ≪≫
    ChainComplex.alternatingConstHomologyZero _

Depends on / 依赖: ChainComplex, ChainComplex.alternatingConstHomologyZero, HasZeroObject, HomologicalComplex, HomologicalComplex.homologyFunctor, alternatingConstHomologyZero, hasCoproducts_shrink, homologyFunctor, initialIsInitial, initialIsInitial.isZero, isZero, mapIso, singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
-/
def singularHomologyFunctorZeroOfTotallyDisconnectedSpace [CategoryWithHomology C] :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ fun _ : X => R :=
  have : HasZeroObject C :=
    have := hasCoproducts_shrink.{0, w} (C := C)
    ⟨_, initialIsInitial.isZero⟩
  (HomologicalComplex.homologyFunctor _ _ 0).mapIso
      (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X) ≪≫
    ChainComplex.alternatingConstHomologyZero _

end TotallyDisconnectedSpace

end AlgebraicTopology
