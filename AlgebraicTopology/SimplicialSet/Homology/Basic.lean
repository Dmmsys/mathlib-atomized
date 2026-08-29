/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Simplicial homology

In this file, we define the homology of simplicial sets.
For any preadditive category `C` with coproducts of size `w` and any
object `R : C`, the simplicial chain complex of a simplicial
set `X` is denoted `X.chainComplex R`, and its homology
in degree `n : ℕ` is `X.homology R n`.

-/

@[expose] public section

open Simplicial CategoryTheory Limits

universe w v u

namespace SSet

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/--
The chain complex associated to a simplicial set, with coefficients in `R : C`.
It computes the simplicial homology of a simplicial sets with coefficients
in `R`. One can recover the ordinary simplicial chain complex when `C := Ab`
and `X := ℤ`.
-/
@[implicit_reducible]
/--
Definition of `chainComplexFunctor` / `chainComplexFunctor` 的定义

English:
definition chainComplexFunctor
  signature: : C ⥤ SSet.{w} ⥤ ChainComplex C Nat
  body: (Functor.postcompose₂.obj (AlgebraicTopology.alternatingFaceMapComplex _)).obj
    (sigmaConst ⋙ SimplicialObject.whiskering _ _)

中文:
定义 chainComplexFunctor
  签名: : C ⥤ SSet.{w} ⥤ ChainComplex C 自然数
  定义体: (Functor.postcompose₂.obj (AlgebraicTopology.alternatingFaceMapComplex _)).obj
    (sigmaConst ⋙ SimplicialObject.whiskering _ _)

Depends on / 依赖: AlgebraicTopology, AlgebraicTopology.alternatingFaceMapComplex, Functor, Functor.postcompose, SimplicialObject, SimplicialObject.whiskering, alternatingFaceMapComplex, sigmaConst, whiskering
-/
noncomputable def chainComplexFunctor : C ⥤ SSet.{w} ⥤ ChainComplex C Nat :=
  (Functor.postcompose₂.obj (AlgebraicTopology.alternatingFaceMapComplex _)).obj
    (sigmaConst ⋙ SimplicialObject.whiskering _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (chainComplexFunctor C).Additive
  body: by
  dsimp [chainComplexFunctor, SimplicialObject.whiskering]
  infer_instance

@[deprecated (since := "2026-04-05")]
alias _root_.AlgebraicTopology.SSet.singularChainComplexFunctor :=
  chainComplexFunctor

中文:
实例 :
  签名: (chainComplexFunctor C).Additive
  定义体: by
  dsimp [chainComplexFunctor, SimplicialObject.whiskering]
  infer_instance

@[deprecated (since := "2026-04-05")]
alias _root_.AlgebraicTopology.SSet.singularChainComplexFunctor :=
  chainComplexFunctor

Depends on / 依赖: SimplicialObject, SimplicialObject.whiskering, chainComplexFunctor, infer_instance, whiskering
-/
instance : (chainComplexFunctor C).Additive := by
  dsimp [chainComplexFunctor, SimplicialObject.whiskering]
  infer_instance

@[deprecated (since := "2026-04-05")]
alias _root_.AlgebraicTopology.SSet.singularChainComplexFunctor :=
  chainComplexFunctor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] SSet.chainComplexFunctor in
attribute [local simp←] _root_.SSet.yonedaEquiv_symm_comp in
/--
Definition of `chainComplexFunctorAdjunction` / `chainComplexFunctorAdjunction` 的定义

English:
definition chainComplexFunctorAdjunction
  signature: (n : Nat)
  body: Sigma.ι (fun _ : Δ[n] _⦋n⦌ => R) (SSet.stdSimplex.objEquiv (n := ⦋n⦌).symm (𝟙 ⦋n⦌))
  counit.app F := { app S := Sigma.desc fun α => F.map (SSet.yonedaEquiv.symm α) }
  right_triangle_components F := by dsimp; simp

@[deprecated (since := "2026-04-05")]
alias _root_.SSet.singularChainComplexFunctorA

中文:
定义 chainComplexFunctorAdjunction
  签名: (n : 自然数)
  定义体: Sigma.ι (fun _ : Δ[n] _⦋n⦌ => R) (SSet.stdSimplex.objEquiv (n := ⦋n⦌).symm (𝟙 ⦋n⦌))
  counit.app F := { app S := Sigma.desc fun α => F.map (SSet.yonedaEquiv.symm α) }
  right_triangle_components F := by dsimp; simp

@[deprecated (since := "2026-04-05")]
alias _root_.SSet.singularChainComplexFunctorA

Depends on / 依赖: SSet.stdSimplex.objEquiv, objEquiv, stdSimplex
-/
noncomputable def chainComplexFunctorAdjunction (n : Nat) :
    (Functor.postcompose₂.obj (HomologicalComplex.eval _ _ n)).obj
      (SSet.chainComplexFunctor C) ⊣ (evaluation _ _).obj Δ[n] where
  unit.app R := Sigma.ι (fun _ : Δ[n] _⦋n⦌ => R) (SSet.stdSimplex.objEquiv (n := ⦋n⦌).symm (𝟙 ⦋n⦌))
  counit.app F := { app S := Sigma.desc fun α => F.map (SSet.yonedaEquiv.symm α) }
  right_triangle_components F := by dsimp; simp

@[deprecated (since := "2026-04-05")]
alias _root_.SSet.singularChainComplexFunctorAdjunction :=
  SSet.chainComplexFunctorAdjunction

variable {C} (X Y Z : SSet.{w}) (f : X ⟶ Y) (g : Y ⟶ Z) (R : C)

/--
Definition of `chainComplex` / `chainComplex` 的定义

English:
abbreviation chainComplex
  signature: : ChainComplex C Nat
  body: ((SSet.chainComplexFunctor C).obj R).obj X

中文:
缩写 chainComplex
  签名: : ChainComplex C 自然数
  定义体: ((SSet.chainComplexFunctor C).obj R).obj X

Depends on / 依赖: SSet.chainComplexFunctor, chainComplexFunctor
-/
noncomputable abbrev chainComplex : ChainComplex C Nat :=
  ((SSet.chainComplexFunctor C).obj R).obj X

variable {X Y} in
/--
Definition of `chainComplexMap` / `chainComplexMap` 的定义

English:
abbreviation chainComplexMap
  signature: : X.chainComplex R ⟶ Y.chainComplex R
  body: ((SSet.chainComplexFunctor C).obj R).map f

中文:
缩写 chainComplexMap
  签名: : X.chainComplex R ⟶ Y.chainComplex R
  定义体: ((SSet.chainComplexFunctor C).obj R).map f

Depends on / 依赖: SSet.chainComplexFunctor, chainComplexFunctor
-/
noncomputable abbrev chainComplexMap : X.chainComplex R ⟶ Y.chainComplex R :=
  ((SSet.chainComplexFunctor C).obj R).map f

variable {R} in
/--
Definition of `ιChainComplex` / `ιChainComplex` 的定义

English:
definition ιChainComplex
  signature: {n : Nat} (x : X _⦋n⦌)
  body: Sigma.ι (fun (_ : X _⦋n⦌) => R) x

中文:
定义 ιChainComplex
  签名: {n : 自然数} (x : X _⦋n⦌)
  定义体: Sigma.ι (fun (_ : X _⦋n⦌) => R) x
-/
noncomputable def ιChainComplex {n : Nat} (x : X _⦋n⦌) : R ⟶ (X.chainComplex R).X n :=
  Sigma.ι (fun (_ : X _⦋n⦌) => R) x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ιChainComplex_d` / 引理 `ιChainComplex_d`

English:
lemma ιChainComplex_d
  given: {n : Nat} (x : X _⦋n + 1⦌)
  proof: by
  simp [ιChainComplex, chainComplex, chainComplexFunctor, Preadditive.comp_sum]

中文:
引理 ιChainComplex_d
  条件: {n : 自然数} (x : X _⦋n + 1⦌)
  证明: by
  simp [ιChainComplex, chainComplex, chainComplexFunctor, Preadditive.comp_sum]

Depends on / 依赖: Preadditive, Preadditive.comp_sum, chainComplex, chainComplexFunctor, comp_sum
-/
lemma ιChainComplex_d {n : Nat} (x : X _⦋n + 1⦌) :
    X.ιChainComplex x ≫ (X.chainComplex R).d (n + 1) n =
      ∑ (i : Fin (n + 2)), (-1) ^ i.val • X.ιChainComplex (X.δ i x) := by
  simp [ιChainComplex, chainComplex, chainComplexFunctor, Preadditive.comp_sum]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `ι_chainComplexMap_f` / 引理 `ι_chainComplexMap_f`

English:
lemma ι_chainComplexMap_f
  given: {n : Nat} (x : X _⦋n⦌)
  proof: by
  dsimp [chainComplexMap, chainComplexFunctor, ιChainComplex, Sigma.map',
    chainComplex, chainComplexFunctor]
  simp

中文:
引理 ι_chainComplexMap_f
  条件: {n : 自然数} (x : X _⦋n⦌)
  证明: by
  dsimp [chainComplexMap, chainComplexFunctor, ιChainComplex, Sigma.map',
    chainComplex, chainComplexFunctor]
  simp

Depends on / 依赖: Sigma.map, chainComplex, chainComplexFunctor, chainComplexMap
-/
lemma ι_chainComplexMap_f {n : Nat} (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (chainComplexMap f R).f n =
      Y.ιChainComplex (f.app _ x) := by
  dsimp [chainComplexMap, chainComplexFunctor, ιChainComplex, Sigma.map',
    chainComplex, chainComplexFunctor]
  simp

/--
Definition of `chainComplexXCofan` / `chainComplexXCofan` 的定义

English:
definition chainComplexXCofan
  signature: (n : Nat)
  body: Cofan.mk _ X.ιChainComplex

中文:
定义 chainComplexXCofan
  签名: (n : 自然数)
  定义体: Cofan.mk _ X.ιChainComplex

Depends on / 依赖: Cofan.mk
-/
noncomputable def chainComplexXCofan (n : Nat) : Cofan (fun (_ : X _⦋n⦌) => R) :=
  Cofan.mk _ X.ιChainComplex

/--
Definition of `isColimitChainComplexXCofan` / `isColimitChainComplexXCofan` 的定义

English:
definition isColimitChainComplexXCofan
  signature: (n : Nat)
  body: coproductIsCoproduct _

中文:
定义 isColimitChainComplexXCofan
  签名: (n : 自然数)
  定义体: coproductIsCoproduct _

Depends on / 依赖: coproductIsCoproduct
-/
noncomputable def isColimitChainComplexXCofan (n : Nat) : IsColimit (X.chainComplexXCofan R n) :=
  coproductIsCoproduct _

variable {X R} in
@[ext]
/--
lemma `chainComplex_hom_ext` / 引理 `chainComplex_hom_ext`

English:
lemma chainComplex_hom_ext
  statement: {n : Nat} {T : C} {f g : (X.chainComplex R).X n ⟶ T}
  proof: (X.isColimitChainComplexXCofan R n).hom_ext (fun _ => h _)

中文:
引理 chainComplex_hom_ext
  结论: {n : 自然数} {T : C} {f g : (X.chainComplex R).X n ⟶ T}
  证明: (X.isColimitChainComplexXCofan R n).hom_ext (fun _ => h _)

Depends on / 依赖: X.isColimitChainComplexXCofan, hom_ext, isColimitChainComplexXCofan
-/
lemma chainComplex_hom_ext {n : Nat} {T : C} {f g : (X.chainComplex R).X n ⟶ T}
    (h : forall (x : X _⦋n⦌), X.ιChainComplex x ≫ f = X.ιChainComplex x ≫ g) :
    f = g :=
  (X.isColimitChainComplexXCofan R n).hom_ext (fun _ => h _)

variable [CategoryWithHomology C]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev homology (n : Nat)
  body: (X.chainComplex R).homology n

中文:
缩写 noncomputable
  签名: abbrev homology (n : 自然数)
  定义体: (X.chainComplex R).homology n
-/
protected noncomputable abbrev homology (n : Nat) : C := (X.chainComplex R).homology n

variable {X Y} in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev homologyMap (n : Nat)
  body: HomologicalComplex.homologyMap (chainComplexMap f R) n

@[simp]

中文:
缩写 noncomputable
  签名: abbrev homologyMap (n : 自然数)
  定义体: HomologicalComplex.homologyMap (chainComplexMap f R) n

@[simp]
-/
protected noncomputable abbrev homologyMap (n : Nat) : X.homology R n ⟶ Y.homology R n :=
  HomologicalComplex.homologyMap (chainComplexMap f R) n

@[simp]
/--
lemma `homologyMap_id` / 引理 `homologyMap_id`

English:
lemma homologyMap_id
  given: (n : Nat)
  statement: SSet.homologyMap (𝟙 X) R n = 𝟙 _
  proof: by
  simp [SSet.homologyMap]

@[reassoc]

中文:
引理 homologyMap_id
  条件: (n : 自然数)
  结论: SSet.homologyMap (𝟙 X) R n = 𝟙 _
  证明: by
  simp [SSet.homologyMap]

@[reassoc]

Depends on / 依赖: SSet.homologyMap, homologyMap
-/
lemma homologyMap_id (n : Nat) : SSet.homologyMap (𝟙 X) R n = 𝟙 _ := by
  simp [SSet.homologyMap]

@[reassoc]
/--
lemma `homologyMap_comp` / 引理 `homologyMap_comp`

English:
lemma homologyMap_comp
  given: (n : Nat)
  proof: by
  simp [SSet.homologyMap, HomologicalComplex.homologyMap_comp]

中文:
引理 homologyMap_comp
  条件: (n : 自然数)
  证明: by
  simp [SSet.homologyMap, HomologicalComplex.homologyMap_comp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyMap_comp, SSet.homologyMap, homologyMap, homologyMap_comp
-/
lemma homologyMap_comp (n : Nat) :
    SSet.homologyMap (f ≫ g) R n = SSet.homologyMap f R n ≫ SSet.homologyMap g R n := by
  simp [SSet.homologyMap, HomologicalComplex.homologyMap_comp]

attribute [local simp] homologyMap_comp in
/-- The simplicial homology functor in degree `n` with coefficients in `R : C`. -/
@[simps]
/--
Definition of `homologyFunctor` / `homologyFunctor` 的定义

English:
definition homologyFunctor
  signature: (n : Nat)
  body: X.homology R n
  map f := SSet.homologyMap f R n

中文:
定义 homologyFunctor
  签名: (n : 自然数)
  定义体: X.homology R n
  map f := SSet.homologyMap f R n

Depends on / 依赖: X.homology, homology
-/
noncomputable def homologyFunctor (n : Nat) : SSet.{w} ⥤ C where
  obj X := X.homology R n
  map f := SSet.homologyMap f R n

end SSet
