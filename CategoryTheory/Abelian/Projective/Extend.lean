/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# Projective resolutions as cochain complexes indexed by the integers

Given a projective resolution `R` of an object `X` in an abelian category `C`,
we define `R.cochainComplex : CochainComplex C ℤ`, which is the extension
of `R.complex : ChainComplex C ℕ`, and the quasi-isomorphism
`R.π' : R.cochainComplex ⟶ (CochainComplex.singleFunctor C 0).obj X`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace ProjectiveResolution

section

variable [HasZeroObject C] [Preadditive C] {X : C}
  (R : ProjectiveResolution X)

/--
Definition of `cochainComplex` / `cochainComplex` 的定义

English:
definition cochainComplex
  signature: : CochainComplex C Int
  body: R.complex.extend ComplexShape.embeddingDownNat

中文:
定义 cochainComplex
  签名: : CochainComplex C 整数
  定义体: R.complex.extend ComplexShape.embeddingDownNat

Depends on / 依赖: ComplexShape, ComplexShape.embeddingDownNat, R.complex.extend, complex, embeddingDownNat, extend
-/
noncomputable def cochainComplex : CochainComplex C Int :=
  R.complex.extend ComplexShape.embeddingDownNat

/--
Definition of `cochainComplexXIso` / `cochainComplexXIso` 的定义

English:
definition cochainComplexXIso
  signature: (n : Int) (k : Nat) (h : -k = n := by lia)
  body: HomologicalComplex.extendXIso _ _ h

@[reassoc]

中文:
定义 cochainComplexXIso
  签名: (n : 整数) (k : 自然数) (h : -k = n := by lia)
  定义体: HomologicalComplex.extendXIso _ _ h

@[reassoc]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.extendXIso, R.cochainComplex.X, R.complex.X, cochainComplex, complex, extendXIso
-/
noncomputable def cochainComplexXIso (n : Int) (k : Nat) (h : -k = n := by lia) :
    R.cochainComplex.X n ≅ R.complex.X k :=
  HomologicalComplex.extendXIso _ _ h

@[reassoc]
/--
lemma `cochainComplex_d` / 引理 `cochainComplex_d`

English:
lemma cochainComplex_d
  given: (n₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : -k₁ = n₁ := by lia) (h₂ : -k₂ = n₂ := by lia)
  proof: HomologicalComplex.extend_d_eq _ _ h₁ h₂

中文:
引理 cochainComplex_d
  条件: (n₁ n₂ : 整数) (k₁ k₂ : 自然数) (h₁ : -k₁ = n₁ := by lia) (h₂ : -k₂ = n₂ := by lia)
  证明: HomologicalComplex.extend_d_eq _ _ h₁ h₂

Depends on / 依赖: HomologicalComplex, HomologicalComplex.extend_d_eq, R.cochainComplex.d, R.complex.d, cochainComplex, cochainComplexXIso, complex, extend_d_eq
-/
lemma cochainComplex_d (n₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : -k₁ = n₁ := by lia) (h₂ : -k₂ = n₂ := by lia) :
    R.cochainComplex.d n₁ n₂ = (cochainComplexXIso _ _ _).hom ≫
      R.complex.d k₁ k₂ ≫ (cochainComplexXIso _ _ _).inv :=
  HomologicalComplex.extend_d_eq _ _ h₁ h₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: R.cochainComplex.IsStrictlyLE 0
  body: by
  dsimp [cochainComplex]
  infer_instance

中文:
实例 :
  签名: R.cochainComplex.IsStrictlyLE 0
  定义体: by
  dsimp [cochainComplex]
  infer_instance

Depends on / 依赖: cochainComplex, infer_instance
-/
instance : R.cochainComplex.IsStrictlyLE 0 := by
  dsimp [cochainComplex]
  infer_instance

instance (n : Int) : Projective (R.cochainComplex.X n) := by
  by_cases hn : n <= 0
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hn
    exact Projective.of_iso (R.cochainComplexXIso (-k) k).symm inferInstance
  · exact IsZero.projective (CochainComplex.isZero_of_isStrictlyLE _ 0 _)

/--
Definition of `π'` / `π'` 的定义

English:
definition π'
  signature: : R.cochainComplex ⟶ (CochainComplex.singleFunctor C 0).obj X
  body: (ComplexShape.embeddingDownNat.extendFunctor C).map R.π ≫
      (HomologicalComplex.extendSingleIso _ _ _ _ (by simp)).hom

中文:
定义 π'
  签名: : R.cochainComplex ⟶ (CochainComplex.singleFunctor C 0).obj X
  定义体: (ComplexShape.embeddingDownNat.extendFunctor C).map R.π ≫
      (HomologicalComplex.extendSingleIso _ _ _ _ (by simp)).hom

Depends on / 依赖: ComplexShape, ComplexShape.embeddingDownNat.extendFunctor, HomologicalComplex, HomologicalComplex.extendSingleIso, embeddingDownNat, extendFunctor, extendSingleIso
-/
noncomputable def π' : R.cochainComplex ⟶ (CochainComplex.singleFunctor C 0).obj X :=
    (ComplexShape.embeddingDownNat.extendFunctor C).map R.π ≫
      (HomologicalComplex.extendSingleIso _ _ _ _ (by simp)).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `π'_f_zero` / 引理 `π'_f_zero`

English:
lemma π'_f_zero
  proof: by
  dsimp [π']
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by simp)]; rw [HomologicalComplex.extendSingleIso_hom_f]
  cat_disch

中文:
引理 π'_f_zero
  证明: by
  dsimp [π']
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by simp)]; rw [HomologicalComplex.extendSingleIso_hom_f]
  cat_disch
-/
lemma π'_f_zero :
    R.π'.f 0 = (R.cochainComplexXIso _ _).hom ≫ R.π.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up Int) 0 X).inv := by
  dsimp [π']
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by simp)]; rw [HomologicalComplex.extendSingleIso_hom_f]
  cat_disch

end

variable [Abelian C] {X : C} (R : ProjectiveResolution X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: QuasiIso R.π'
  body: by dsimp [π']; infer_instance

中文:
实例 :
  签名: QuasiIso R.π'
  定义体: by dsimp [π']; infer_instance

Depends on / 依赖: infer_instance
-/
instance : QuasiIso R.π' := by dsimp [π']; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: R.cochainComplex.IsGE 0
  body: by
  simp only [HomologicalComplex.isSupported_iff_of_quasiIso R.π']
  infer_instance

中文:
实例 :
  签名: R.cochainComplex.IsGE 0
  定义体: by
  simp only [HomologicalComplex.isSupported_iff_of_quasiIso R.π']
  infer_instance

Depends on / 依赖: HomologicalComplex, HomologicalComplex.isSupported_iff_of_quasiIso, infer_instance, isSupported_iff_of_quasiIso
-/
instance : R.cochainComplex.IsGE 0 := by
  simp only [HomologicalComplex.isSupported_iff_of_quasiIso R.π']
  infer_instance

namespace Hom

variable {R} {X' : C} {R' : ProjectiveResolution X'} {f : X ⟶ X'}
  (φ : Hom R R' f)

/--
Definition of `hom'` / `hom'` 的定义

English:
definition hom'
  signature: : R.cochainComplex ⟶ R'.cochainComplex
  body: HomologicalComplex.extendMap φ.hom _

中文:
定义 hom'
  签名: : R.cochainComplex ⟶ R'.cochainComplex
  定义体: HomologicalComplex.extendMap φ.hom _

Depends on / 依赖: HomologicalComplex, HomologicalComplex.extendMap, extendMap
-/
noncomputable def hom' : R.cochainComplex ⟶ R'.cochainComplex :=
  HomologicalComplex.extendMap φ.hom _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `hom'_f` / 引理 `hom'_f`

English:
lemma hom'_f
  given: (n : Int) (m : Nat) (h : -m = n)
  proof: by
  simp [hom', HomologicalComplex.extendMap_f _
    ComplexShape.embeddingDownNat (i := m) (i' := n) (by dsimp; lia),
    cochainComplexXIso]

中文:
引理 hom'_f
  条件: (n : 整数) (m : 自然数) (h : -m = n)
  证明: by
  simp [hom', HomologicalComplex.extendMap_f _
    ComplexShape.embeddingDownNat (i := m) (i' := n) (by dsimp; lia),
    cochainComplexXIso]
-/
lemma hom'_f (n : Int) (m : Nat) (h : -m = n) :
    φ.hom'.f n =
    (R.cochainComplexXIso n m h).hom ≫ φ.hom.f m ≫ (R'.cochainComplexXIso n m h).inv := by
  simp [hom', HomologicalComplex.extendMap_f _
    ComplexShape.embeddingDownNat (i := m) (i' := n) (by dsimp; lia),
    cochainComplexXIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `hom'_comp_π'` / 引理 `hom'_comp_π'`

English:
lemma hom'_comp_π'
  proof: HomologicalComplex.to_single_hom_ext (by
    simp [hom'_f _ 0 0 rfl, π'_f_zero, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors,
      HomologicalComplex.single, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq])

中文:
引理 hom'_comp_π'
  证明: HomologicalComplex.to_single_hom_ext (by
    simp [hom'_f _ 0 0 rfl, π'_f_zero, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors,
      HomologicalComplex.single, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq])
-/
lemma hom'_comp_π' :
    φ.hom' ≫ R'.π' = R.π' ≫ (CochainComplex.singleFunctor C 0).map f :=
  HomologicalComplex.to_single_hom_ext (by
    simp [hom'_f _ 0 0 rfl, π'_f_zero, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors,
      HomologicalComplex.single, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq])

end Hom

end ProjectiveResolution

end CategoryTheory
