/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.FunctorN

/-!

# Comparison with the normalized Moore complex functor

In this file, we show that when the category `A` is abelian,
there is an isomorphism `N₁_iso_normalizedMooreComplex_comp_toKaroubi` between
the functor `N₁ : SimplicialObject A ⥤ Karoubi (ChainComplex A ℕ)`
defined in `FunctorN.lean` and the composition of
`normalizedMooreComplex A` with the inclusion
`ChainComplex A ℕ ⥤ Karoubi (ChainComplex A ℕ)`.

This isomorphism shall be used in `Equivalence.lean` in order to obtain
the Dold-Kan equivalence
`CategoryTheory.Abelian.DoldKan.equivalence : SimplicialObject A ≌ ChainComplex A ℕ`
with a functor (definitionally) equal to `normalizedMooreComplex A`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Subobject CategoryTheory.Idempotents DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

universe v

variable {A : Type*} [Category* A] [Abelian A] {X : SimplicialObject A}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `HigherFacesVanish.inclusionOfMooreComplexMap` / 定理 `HigherFacesVanish.inclusionOfMooreComplexMap`

English:
theorem HigherFacesVanish.inclusionOfMooreComplexMap
  given: (n : Nat)
  proof: fun j _ => by
  dsimp [AlgebraicTopology.inclusionOfMooreComplexMap, NormalizedMooreComplex.objX]
  rw [← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ j
    (by simp))]; rw [assoc]; rw [kernelSubobject_arrow_comp]; rw [comp_zero]

中文:
定理 HigherFacesVanish.inclusionOfMooreComplexMap
  条件: (n : 自然数)
  证明: fun j _ => by
  dsimp [AlgebraicTopology.inclusionOfMooreComplexMap, NormalizedMooreComplex.objX]
  rw [← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ j
    (by simp))]; rw [assoc]; rw [kernelSubobject_arrow_comp]; rw [comp_zero]

Depends on / 依赖: AlgebraicTopology, AlgebraicTopology.inclusionOfMooreComplexMap, Finset, Finset.univ, NormalizedMooreComplex, NormalizedMooreComplex.objX, comp_zero, factorThru_arrow, finset_inf_arrow_factors, inclusionOfMooreComplexMap, kernelSubobject_arrow_comp
-/
theorem HigherFacesVanish.inclusionOfMooreComplexMap (n : Nat) :
    HigherFacesVanish (n + 1) ((inclusionOfMooreComplexMap X).f (n + 1)) := fun j _ => by
  dsimp [AlgebraicTopology.inclusionOfMooreComplexMap, NormalizedMooreComplex.objX]
  rw [← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ j
    (by simp))]; rw [assoc]; rw [kernelSubobject_arrow_comp]; rw [comp_zero]

/--
theorem `factors_normalizedMooreComplex_PInfty` / 定理 `factors_normalizedMooreComplex_PInfty`

English:
theorem factors_normalizedMooreComplex_PInfty
  given: (n : Nat)
  proof: by
  rcases n with _ | n
  · apply top_factors
  · rw [PInfty_f, NormalizedMooreComplex.objX, finset_inf_factors]
    intro i _
    apply kernelSubobject_factors
    exact (HigherFacesVanish.of_P (n + 1) n) i le_add_self

中文:
定理 factors_normalizedMooreComplex_PInfty
  条件: (n : 自然数)
  证明: by
  rcases n with _ | n
  · apply top_factors
  · rw [PInfty_f, NormalizedMooreComplex.objX, finset_inf_factors]
    intro i _
    apply kernelSubobject_factors
    exact (HigherFacesVanish.of_P (n + 1) n) i le_add_self

Depends on / 依赖: HigherFacesVanish, HigherFacesVanish.of_P, NormalizedMooreComplex, NormalizedMooreComplex.objX, PInfty_f, finset_inf_factors, kernelSubobject_factors, le_add_self, of_P, top_factors
-/
theorem factors_normalizedMooreComplex_PInfty (n : Nat) :
    Subobject.Factors (NormalizedMooreComplex.objX X n) (PInfty.f n) := by
  rcases n with _ | n
  · apply top_factors
  · rw [PInfty_f, NormalizedMooreComplex.objX, finset_inf_factors]
    intro i _
    apply kernelSubobject_factors
    exact (HigherFacesVanish.of_P (n + 1) n) i le_add_self

set_option backward.isDefEq.respectTransparency false in
/-- `PInfty` factors through the normalized Moore complex -/
@[simps!]
/--
Definition of `PInftyToNormalizedMooreComplex` / `PInftyToNormalizedMooreComplex` 的定义

English:
definition PInftyToNormalizedMooreComplex
  signature: (X : SimplicialObject A)
  body: ChainComplex.ofHom
    (fun n => factorThru _ _ (factors_normalizedMooreComplex_PInfty n)) fun n => by
    rw [← cancel_mono (NormalizedMooreComplex.objX X n).arrow]; rw [assoc]; rw [assoc]; rw [factorThru_arrow]; rw [← inclusionOfMooreComplexMap_f]; rw [NormalizedMooreComplex.obj_d]; rw [ChainCompl

中文:
定义 PInftyToNormalizedMooreComplex
  签名: (X : SimplicialObject A)
  定义体: ChainComplex.ofHom
    (fun n => factorThru _ _ (factors_normalizedMooreComplex_PInfty n)) fun n => by
    rw [← cancel_mono (NormalizedMooreComplex.objX X n).arrow]; rw [assoc]; rw [assoc]; rw [factorThru_arrow]; rw [← inclusionOfMooreComplexMap_f]; rw [NormalizedMooreComplex.obj_d]; rw [ChainCompl

Depends on / 依赖: ChainComplex, ChainComplex.ofHom, ChainComplex.of_d, NormalizedMooreComplex, NormalizedMooreComplex.objX, NormalizedMooreComplex.obj_d, alternatingFaceMapComplex_obj_d, cancel_mono, factorThru, factorThru_arrow, factorThru_arrow_assoc, factors_normalizedMooreComplex_PInfty, inclusionOfMooreComplexMap, inclusionOfMooreComplexMap_f, normalizedMooreComplex_objD, obj_d, of_d
-/
def PInftyToNormalizedMooreComplex (X : SimplicialObject A) : K[X] ⟶ N[X] :=
  ChainComplex.ofHom
    (fun n => factorThru _ _ (factors_normalizedMooreComplex_PInfty n)) fun n => by
    rw [← cancel_mono (NormalizedMooreComplex.objX X n).arrow]; rw [assoc]; rw [assoc]; rw [factorThru_arrow]; rw [← inclusionOfMooreComplexMap_f]; rw [NormalizedMooreComplex.obj_d]; rw [ChainComplex.of_d]; rw [← normalizedMooreComplex_objD]; rw [← (inclusionOfMooreComplexMap X).comm (n + 1) n]; rw [inclusionOfMooreComplexMap_f]; rw [factorThru_arrow_assoc]; rw [alternatingFaceMapComplex_obj_d]; rw [← alternatingFaceMapComplex_obj_d]
    exact PInfty.comm (n + 1) n

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap` / 定理 `PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap`

English:
theorem PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap
  given: (X : SimplicialObject A)
  proof: by cat_disch

中文:
定理 PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap
  条件: (X : SimplicialObject A)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap (X : SimplicialObject A) :
    PInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X = PInfty := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `PInftyToNormalizedMooreComplex_naturality` / 定理 `PInftyToNormalizedMooreComplex_naturality`

English:
theorem PInftyToNormalizedMooreComplex_naturality
  given: {X Y : SimplicialObject A} (f : X ⟶ Y)
  proof: by
  cat_disch

中文:
定理 PInftyToNormalizedMooreComplex_naturality
  条件: {X Y : SimplicialObject A} (f : X ⟶ Y)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem PInftyToNormalizedMooreComplex_naturality {X Y : SimplicialObject A} (f : X ⟶ Y) :
    AlternatingFaceMapComplex.map f ≫ PInftyToNormalizedMooreComplex Y =
      PInftyToNormalizedMooreComplex X ≫ NormalizedMooreComplex.map f := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `PInfty_comp_PInftyToNormalizedMooreComplex` / 定理 `PInfty_comp_PInftyToNormalizedMooreComplex`

English:
theorem PInfty_comp_PInftyToNormalizedMooreComplex
  given: (X : SimplicialObject A)
  proof: by cat_disch

@[reassoc (attr := simp)]

中文:
定理 PInfty_comp_PInftyToNormalizedMooreComplex
  条件: (X : SimplicialObject A)
  证明: by cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch
-/
theorem PInfty_comp_PInftyToNormalizedMooreComplex (X : SimplicialObject A) :
    PInfty ≫ PInftyToNormalizedMooreComplex X = PInftyToNormalizedMooreComplex X := by cat_disch

@[reassoc (attr := simp)]
/--
theorem `inclusionOfMooreComplexMap_comp_PInfty` / 定理 `inclusionOfMooreComplexMap_comp_PInfty`

English:
theorem inclusionOfMooreComplexMap_comp_PInfty
  given: (X : SimplicialObject A)
  proof: by
  ext (_ | n)
  · dsimp
    simp only [comp_id]
  · exact (HigherFacesVanish.inclusionOfMooreComplexMap n).comp_P_eq_self

中文:
定理 inclusionOfMooreComplexMap_comp_PInfty
  条件: (X : SimplicialObject A)
  证明: by
  ext (_ | n)
  · dsimp
    simp only [comp_id]
  · exact (HigherFacesVanish.inclusionOfMooreComplexMap n).comp_P_eq_self

Depends on / 依赖: HigherFacesVanish, HigherFacesVanish.inclusionOfMooreComplexMap, comp_P_eq_self, comp_id, inclusionOfMooreComplexMap
-/
theorem inclusionOfMooreComplexMap_comp_PInfty (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X := by
  ext (_ | n)
  · dsimp
    simp only [comp_id]
  · exact (HigherFacesVanish.inclusionOfMooreComplexMap n).comp_P_eq_self

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (inclusionOfMooreComplexMap X)
  body: ⟨fun _ _ hf => by
    ext n
    dsimp
    ext
    exact HomologicalComplex.congr_hom hf n⟩

中文:
实例 :
  签名: Mono (inclusionOfMooreComplexMap X)
  定义体: ⟨fun _ _ hf => by
    ext n
    dsimp
    ext
    exact HomologicalComplex.congr_hom hf n⟩

Depends on / 依赖: HomologicalComplex, HomologicalComplex.congr_hom, congr_hom
-/
instance : Mono (inclusionOfMooreComplexMap X) :=
  ⟨fun _ _ hf => by
    ext n
    dsimp
    ext
    exact HomologicalComplex.congr_hom hf n⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `splitMonoInclusionOfMooreComplexMap` / `splitMonoInclusionOfMooreComplexMap` 的定义

English:
definition splitMonoInclusionOfMooreComplexMap
  signature: (X : SimplicialObject A)
  body: PInftyToNormalizedMooreComplex X
  id := by
    simp only [← cancel_mono (inclusionOfMooreComplexMap X), assoc, id_comp,
      PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      inclusionOfMooreComplexMap_comp_PInfty]

中文:
定义 splitMonoInclusionOfMooreComplexMap
  签名: (X : SimplicialObject A)
  定义体: PInftyToNormalizedMooreComplex X
  id := by
    simp only [← cancel_mono (inclusionOfMooreComplexMap X), assoc, id_comp,
      PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      inclusionOfMooreComplexMap_comp_PInfty]

Depends on / 依赖: PInftyToNormalizedMooreComplex
-/
def splitMonoInclusionOfMooreComplexMap (X : SimplicialObject A) :
    SplitMono (inclusionOfMooreComplexMap X) where
  retraction := PInftyToNormalizedMooreComplex X
  id := by
    simp only [← cancel_mono (inclusionOfMooreComplexMap X), assoc, id_comp,
      PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      inclusionOfMooreComplexMap_comp_PInfty]

variable (A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `N₁_iso_normalizedMooreComplex_comp_toKaroubi` / `N₁_iso_normalizedMooreComplex_comp_toKaroubi` 的定义

English:
definition N₁_iso_normalizedMooreComplex_comp_toKaroubi
  signature: : N₁ ≅ normalizedMooreComplex A ⋙ toKaroubi _ where
  body: { app := fun X => { f := PInftyToNormalizedMooreComplex X } }
  inv :=
    { app := fun X => { f := inclusionOfMooreComplexMap X } }
  hom_inv_id := by
    ext X : 3
    simp only [PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      NatTrans.comp_app, Karoubi.comp_f, N₁_obj_p, NatT

中文:
定义 N₁_iso_normalizedMooreComplex_comp_toKaroubi
  签名: : N₁ ≅ normalizedMooreComplex A ⋙ toKaroubi _ where
  定义体: { app := fun X => { f := PInftyToNormalizedMooreComplex X } }
  inv :=
    { app := fun X => { f := inclusionOfMooreComplexMap X } }
  hom_inv_id := by
    ext X : 3
    simp only [PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      NatTrans.comp_app, Karoubi.comp_f, N₁_obj_p, NatT

Depends on / 依赖: Karoubi, Karoubi.comp_f, Karoubi.id_f, NatTrans, NatTrans.comp_app, NatTrans.id_app, PInftyToNormalizedMooreComplex, PInftyToNormalizedMooreComplex_com, PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap, cancel_mono, comp_app, comp_f, hom_inv_id, id_app, id_f, inclusionOfMooreComplexMap, inv_hom_id
-/
def N₁_iso_normalizedMooreComplex_comp_toKaroubi : N₁ ≅ normalizedMooreComplex A ⋙ toKaroubi _ where
  hom :=
    { app := fun X => { f := PInftyToNormalizedMooreComplex X } }
  inv :=
    { app := fun X => { f := inclusionOfMooreComplexMap X } }
  hom_inv_id := by
    ext X : 3
    simp only [PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      NatTrans.comp_app, Karoubi.comp_f, N₁_obj_p, NatTrans.id_app, Karoubi.id_f]
  inv_hom_id := by
    ext X : 3
    rw [← cancel_mono (inclusionOfMooreComplexMap X)]
    simp only [NatTrans.comp_app, Karoubi.comp_f, assoc, NatTrans.id_app, Karoubi.id_f,
      PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      inclusionOfMooreComplexMap_comp_PInfty]
    dsimp only [Functor.comp_obj, toKaroubi]
    rw [id_comp]

end DoldKan

end AlgebraicTopology
