/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SmallShiftedHom
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Morphisms from K-projective complexes in the derived category

In this file, we show that if `K : CochainComplex C ℤ` is K-projective,
then for any `L : HomotopyCategory C (.up ℤ)`, the functor `DerivedCategory.Qh`
induces a bijection from the type of morphisms `(HomotopyCategory.quotient _ _).obj K) ⟶ L`
(i.e. homotopy classes of morphisms of cochain complexes) to the type of
morphisms in the derived category.
We obtain that a morphism between `K`-projective cochain complexes is a quasi-isomorphism
iff it is a homotopy equivalence. In particular, a morphism between chain complexes
indexed by `ℕ` which consist of projective objects is a quasi-isomorphism iff
it is a homotopy equivalence.

-/

@[expose] public section

universe w v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open CategoryTheory Localization DerivedCategory

namespace CochainComplex

namespace IsKProjective

open HomologicalComplex

/--
lemma `Qh_map_bijective` / 引理 `Qh_map_bijective`

English:
lemma Qh_map_bijective
  statement: [HasDerivedCategory C]
  proof: (CochainComplex.IsKProjective.leftOrthogonal K).map_bijective_of_isTriangulated _ _

中文:
引理 Qh_map_bijective
  结论: [HasDerivedCategory C]
  证明: (CochainComplex.IsKProjective.leftOrthogonal K).map_bijective_of_isTriangulated _ _

Depends on / 依赖: CochainComplex, CochainComplex.IsKProjective.leftOrthogonal, IsKProjective, leftOrthogonal, map_bijective_of_isTriangulated
-/
lemma Qh_map_bijective [HasDerivedCategory C]
    (K : CochainComplex C Int) (L : HomotopyCategory C (.up Int))
    [K.IsKProjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient _ _).obj K ⟶ L) -> _) :=
  (CochainComplex.IsKProjective.leftOrthogonal K).map_bijective_of_isTriangulated _ _

attribute [local instance] HasDerivedCategory.standard in
/--
lemma `quasiIso_iff` / 引理 `quasiIso_iff`

English:
lemma quasiIso_iff
  given: {K L : CochainComplex C Int} [K.IsKProjective] [L.IsKProjective] (f : K ⟶ L)
  proof: by
  refine ⟨fun _ => ?_, fun hf => homotopyEquivalences_le_quasiIso _ _ _ hf⟩
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms]; rw [MorphismProperty.inverseImage_iff]; rw [MorphismProperty.isomorphisms.iff]
  obtain ⟨g, hg⟩ := (Qh_map_bijective _ _).surjective
    ((quotientCompQhIso C)

中文:
引理 quasiIso_iff
  条件: {K L : CochainComplex C 整数} [K.IsKProjective] [L.IsKProjective] (f : K ⟶ L)
  证明: by
  refine ⟨fun _ => ?_, fun hf => homotopyEquivalences_le_quasiIso _ _ _ hf⟩
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms]; rw [MorphismProperty.inverseImage_iff]; rw [MorphismProperty.isomorphisms.iff]
  obtain ⟨g, hg⟩ := (Qh_map_bijective _ _).surjective
    ((quotientCompQhIso C)

Depends on / 依赖: HomotopyCategory, HomotopyCategory.inverseImage_quotient_isomorphisms, MorphismProperty, MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff, Q.map, Qh_map_bijective, hom.app, homotopyEquivalences_le_quasiIso, injective, inv.app, inverseImage_iff, inverseImage_quotient_isomorphisms, isomorphisms, quotientCompQhIso, quotientCompQhIso_inv_naturality, surjective
-/
lemma quasiIso_iff {K L : CochainComplex C Int} [K.IsKProjective] [L.IsKProjective] (f : K ⟶ L) :
    QuasiIso f ↔ homotopyEquivalences C (.up Int) f := by
  refine ⟨fun _ => ?_, fun hf => homotopyEquivalences_le_quasiIso _ _ _ hf⟩
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms]; rw [MorphismProperty.inverseImage_iff]; rw [MorphismProperty.isomorphisms.iff]
  obtain ⟨g, hg⟩ := (Qh_map_bijective _ _).surjective
    ((quotientCompQhIso C).hom.app L ≫ inv (Q.map f) ≫ (quotientCompQhIso C).inv.app K)
  refine ⟨g, (Qh_map_bijective _ _).injective ?_, (Qh_map_bijective _ _).injective ?_⟩
  · simp [hg]
  · simp [hg, ← quotientCompQhIso_inv_naturality f, -NatTrans.naturality]

end IsKProjective

namespace HomComplex.CohomologyClass

variable (K L : CochainComplex C Int) (n : Int)
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up Int)) Int K L]

/--
lemma `bijective_toSmallShiftedHom_of_isKProjective` / 引理 `bijective_toSmallShiftedHom_of_isKProjective`

English:
lemma bijective_toSmallShiftedHom_of_isKProjective
  given: [K.IsKProjective]
  proof: by
  let := HasDerivedCategory.standard C
  rw [← Function.Bijective.of_comp_iff'
      (SmallShiftedHom.equiv _ DerivedCategory.Q).bijective]; rw [← Function.Bijective.of_comp_iff' (Iso.homCongr ((quotientCompQhIso C).symm.app K)
      ((Q.commShiftIso n).symm.app L ≪≫ (quotientCompQhIso C).symm.ap

中文:
引理 bijective_toSmallShiftedHom_of_isKProjective
  条件: [K.IsKProjective]
  证明: by
  let := HasDerivedCategory.standard C
  rw [← Function.Bijective.of_comp_iff'
      (SmallShiftedHom.equiv _ DerivedCategory.Q).bijective]; rw [← Function.Bijective.of_comp_iff' (Iso.homCongr ((quotientCompQhIso C).symm.app K)
      ((Q.commShiftIso n).symm.app L ≪≫ (quotientCompQhIso C).symm.ap

Depends on / 依赖: Bijective, CochainComplex, CochainComplex.IsKProjective.Qh_map_bijective, DerivedCategory, DerivedCategory.Q, Function, Function.Bijective.of_comp_iff, HasDerivedCategory, HasDerivedCategory.standard, IsKProjective, Iso.homCongr, Q.commShiftIso, Qh_map_bijective, ShiftedHom, ShiftedHom.map, SmallShiftedHom, SmallShiftedHom.equiv, bijective, commShiftIso, convert
-/
lemma bijective_toSmallShiftedHom_of_isKProjective [K.IsKProjective] :
    Function.Bijective (toSmallShiftedHom.{w} (K := K) (L := L) (n := n)) := by
  let := HasDerivedCategory.standard C
  rw [← Function.Bijective.of_comp_iff'
      (SmallShiftedHom.equiv _ DerivedCategory.Q).bijective]; rw [← Function.Bijective.of_comp_iff' (Iso.homCongr ((quotientCompQhIso C).symm.app K)
      ((Q.commShiftIso n).symm.app L ≪≫ (quotientCompQhIso C).symm.app (L⟦n⟧))).bijective]
  convert! (CochainComplex.IsKProjective.Qh_map_bijective _ _).comp (toHom_bijective K L n)
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp [toHom_mk, ShiftedHom.map]

variable {K L n} in
/-- When `K` is a K-projective cochain complex, cohomology classes
in `CohomologyClass K L n` identify to elements in a type `SmallShiftedHom` relatively
to quasi-isomorphisms. -/
@[simps! -isSimp]
/--
Definition of `equivOfIsKProjective` / `equivOfIsKProjective` 的定义

English:
definition equivOfIsKProjective
  signature: [K.IsKProjective]
  body: Equiv.ofBijective _ (bijective_toSmallShiftedHom_of_isKProjective _ _ _)

中文:
定义 equivOfIsKProjective
  签名: [K.IsKProjective]
  定义体: Equiv.ofBijective _ (bijective_toSmallShiftedHom_of_isKProjective _ _ _)

Depends on / 依赖: Equiv.ofBijective, bijective_toSmallShiftedHom_of_isKProjective, ofBijective
-/
noncomputable def equivOfIsKProjective [K.IsKProjective] :
    CohomologyClass K L n ≃
      SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (.up Int)) K L n :=
  Equiv.ofBijective _ (bijective_toSmallShiftedHom_of_isKProjective _ _ _)

end HomComplex.CohomologyClass

end CochainComplex

namespace ChainComplex

open HomologicalComplex

/--
lemma `quasiIso_iff_of_projective` / 引理 `quasiIso_iff_of_projective`

English:
lemma quasiIso_iff_of_projective
  statement: {K L : ChainComplex C Nat}
  proof: by
  rw [← quasiIso_extendMap_iff _ ComplexShape.embeddingDownNat]; rw [CochainComplex.IsKProjective.quasiIso_iff]; rw [homotopyEquivalences_extendMap_iff]

中文:
引理 quasiIso_iff_of_projective
  结论: {K L : ChainComplex C 自然数}
  证明: by
  rw [← quasiIso_extendMap_iff _ ComplexShape.embeddingDownNat]; rw [CochainComplex.IsKProjective.quasiIso_iff]; rw [homotopyEquivalences_extendMap_iff]

Depends on / 依赖: CochainComplex, CochainComplex.IsKProjective.quasiIso_iff, ComplexShape, ComplexShape.embeddingDownNat, IsKProjective, embeddingDownNat, homotopyEquivalences_extendMap_iff, quasiIso_extendMap_iff, quasiIso_iff
-/
lemma quasiIso_iff_of_projective {K L : ChainComplex C Nat}
    [forall n, Projective (K.X n)] [forall n, Projective (L.X n)]
    (f : K ⟶ L) :
    QuasiIso f ↔ homotopyEquivalences C (.down Nat) f := by
  rw [← quasiIso_extendMap_iff _ ComplexShape.embeddingDownNat]; rw [CochainComplex.IsKProjective.quasiIso_iff]; rw [homotopyEquivalences_extendMap_iff]

end ChainComplex
