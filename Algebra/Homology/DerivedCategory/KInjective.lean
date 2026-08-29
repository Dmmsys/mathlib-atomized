/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SmallShiftedHom
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Morphisms to K-injective complexes in the derived category

In this file, we show that if `L : CochainComplex C ℤ` is K-injective,
then for any `K : HomotopyCategory C (.up ℤ)`, the functor `DerivedCategory.Qh`
induces a bijection from the type of morphisms `K ⟶ (HomotopyCategory.quotient _ _).obj L)`
(i.e. homotopy classes of morphisms of cochain complexes) to the type of
morphisms in the derived category.
We obtain that a morphism between `K`-injective cochain complexes is a quasi-isomorphism
iff it is a homotopy equivalence. In particular, a morphism between cochain complexes
indexed by `ℕ` which consist of injective objects is a quasi-isomorphism iff
it is a homotopy equivalence.

-/

@[expose] public section

universe w v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open CategoryTheory Localization DerivedCategory

namespace CochainComplex

namespace IsKInjective

/--
lemma `Qh_map_bijective` / 引理 `Qh_map_bijective`

English:
lemma Qh_map_bijective
  statement: [HasDerivedCategory C]
  proof: (CochainComplex.IsKInjective.rightOrthogonal L).map_bijective_of_isTriangulated _ _

中文:
引理 Qh_map_bijective
  结论: [HasDerivedCategory C]
  证明: (CochainComplex.IsKInjective.rightOrthogonal L).map_bijective_of_isTriangulated _ _

Depends on / 依赖: CochainComplex, CochainComplex.IsKInjective.rightOrthogonal, IsKInjective, map_bijective_of_isTriangulated, rightOrthogonal
-/
lemma Qh_map_bijective [HasDerivedCategory C]
    (K : HomotopyCategory C (ComplexShape.up Int))
    (L : CochainComplex C Int) [L.IsKInjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      (K ⟶ (HomotopyCategory.quotient _ _).obj L) -> _) :=
  (CochainComplex.IsKInjective.rightOrthogonal L).map_bijective_of_isTriangulated _ _

open HomologicalComplex in
attribute [local instance] HasDerivedCategory.standard in
/--
lemma `quasiIso_iff` / 引理 `quasiIso_iff`

English:
lemma quasiIso_iff
  given: {K L : CochainComplex C Int} [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L)
  proof: by
  refine ⟨fun _ => ?_, fun hf => homotopyEquivalences_le_quasiIso _ _ _ hf⟩
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms]; rw [MorphismProperty.inverseImage_iff]; rw [MorphismProperty.isomorphisms.iff]
  obtain ⟨g, hg⟩ := (Qh_map_bijective _ _).surjective
    ((quotientCompQhIso C).hom.app L ≫ inv (Q.map f) ≫ (quotientCompQhIso C).inv.app K)
  refine ⟨g, (Qh_map_bijective _ _).injective ?_, (Qh_map_bijective _ _).injective ?_⟩
  · simp [hg]
  · simp [hg, ← quotientCompQhIso_inv_naturality, -NatTrans.naturality]

中文:
引理 quasiIso_iff
  条件: {K L : 上链复形 C 整数} [K.是KInjective] [L.是KInjective] (f : K ⟶ L)
  证明: by
  refine ⟨fun _ => ?_, fun hf => homotopyEquivalences_le_quasiIso _ _ _ hf⟩
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms]; rw [MorphismProperty.inverseImage_iff]; rw [MorphismProperty.isomorphisms.iff]
  obtain ⟨g, hg⟩ := (Qh_map_bijective _ _).surjective
    ((quotientCompQhIso C).hom.app L ≫ inv (Q.map f) ≫ (quotientCompQhIso C).inv.app K)
  refine ⟨g, (Qh_map_bijective _ _).injective ?_, (Qh_map_bijective _ _).injective ?_⟩
  · simp [hg]
  · simp [hg, ← quotientCompQhIso_inv_naturality, -NatTrans.naturality]

Depends on / 依赖: HomotopyCategory, HomotopyCategory.inverseImage_quotient_isomorphisms, MorphismProperty, MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff, Q.map, Qh_map_bijective, hom.app, homotopyEquivalences_le_quasiIso, injective, inv.app, inverseImage_iff, inverseImage_quotient_isomorphisms, isomorphisms, quotientCompQhIso, quotientCompQhIso_inv_naturality, surjective
-/
lemma quasiIso_iff {K L : CochainComplex C Int} [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) :
    QuasiIso f ↔ homotopyEquivalences C (.up Int) f := by
  refine ⟨fun _ => ?_, fun hf => homotopyEquivalences_le_quasiIso _ _ _ hf⟩
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms]; rw [MorphismProperty.inverseImage_iff]; rw [MorphismProperty.isomorphisms.iff]
  obtain ⟨g, hg⟩ := (Qh_map_bijective _ _).surjective
    ((quotientCompQhIso C).hom.app L ≫ inv (Q.map f) ≫ (quotientCompQhIso C).inv.app K)
  refine ⟨g, (Qh_map_bijective _ _).injective ?_, (Qh_map_bijective _ _).injective ?_⟩
  · simp [hg]
  · simp [hg, ← quotientCompQhIso_inv_naturality, -NatTrans.naturality]

end IsKInjective

namespace HomComplex.CohomologyClass

variable (K L : CochainComplex C Int) (n : Int)
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up Int)) Int K L]

/--
lemma `bijective_toSmallShiftedHom_of_isKInjective` / 引理 `bijective_toSmallShiftedHom_of_isKInjective`

English:
lemma bijective_toSmallShiftedHom_of_isKInjective
  given: [L.IsKInjective]
  proof: by
  let := HasDerivedCategory.standard C
  rw [← Function.Bijective.of_comp_iff'
      (SmallShiftedHom.equiv _ DerivedCategory.Q).bijective]; rw [← Function.Bijective.of_comp_iff' (Iso.homCongr ((quotientCompQhIso C).symm.app K)
      ((Q.commShiftIso n).symm.app L ≪≫ (quotientCompQhIso C).symm.app (L⟦n⟧))).bijective]
  convert! (CochainComplex.IsKInjective.Qh_map_bijective _ _).comp (toHom_bijective K L n)
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp [toHom_mk, ShiftedHom.map]

中文:
引理 bijective_toSmallShiftedHom_of_isKInjective
  条件: [L.是KInjective]
  证明: by
  let := HasDerivedCategory.standard C
  rw [← Function.Bijective.of_comp_iff'
      (SmallShiftedHom.equiv _ DerivedCategory.Q).bijective]; rw [← Function.Bijective.of_comp_iff' (Iso.homCongr ((quotientCompQhIso C).symm.app K)
      ((Q.commShiftIso n).symm.app L ≪≫ (quotientCompQhIso C).symm.app (L⟦n⟧))).bijective]
  convert! (CochainComplex.IsKInjective.Qh_map_bijective _ _).comp (toHom_bijective K L n)
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp [toHom_mk, ShiftedHom.map]

Depends on / 依赖: Bijective, CochainComplex, CochainComplex.IsKInjective.Qh_map_bijective, DerivedCategory, DerivedCategory.Q, Function, Function.Bijective.of_comp_iff, HasDerivedCategory, HasDerivedCategory.standard, IsKInjective, Iso.homCongr, Q.commShiftIso, Qh_map_bijective, ShiftedHom, ShiftedHom.map, SmallShiftedHom, SmallShiftedHom.equiv, bijective, commShiftIso, convert
-/
lemma bijective_toSmallShiftedHom_of_isKInjective [L.IsKInjective] :
    Function.Bijective (toSmallShiftedHom.{w} (K := K) (L := L) (n := n)) := by
  let := HasDerivedCategory.standard C
  rw [← Function.Bijective.of_comp_iff'
      (SmallShiftedHom.equiv _ DerivedCategory.Q).bijective]; rw [← Function.Bijective.of_comp_iff' (Iso.homCongr ((quotientCompQhIso C).symm.app K)
      ((Q.commShiftIso n).symm.app L ≪≫ (quotientCompQhIso C).symm.app (L⟦n⟧))).bijective]
  convert! (CochainComplex.IsKInjective.Qh_map_bijective _ _).comp (toHom_bijective K L n)
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp [toHom_mk, ShiftedHom.map]

variable {K L n} in
/-- When `L` is a K-injective cochain complex, cohomology classes
in `CohomologyClass K L n` identify to elements in a type `SmallShiftedHom` relatively
to quasi-isomorphisms. -/
@[simps! -isSimp]
/--
Definition of `equivOfIsKInjective` / `equivOfIsKInjective` 的定义

English:
definition equivOfIsKInjective
  signature: [L.IsKInjective]
  body: Equiv.ofBijective _ (bijective_toSmallShiftedHom_of_isKInjective _ _ _)

中文:
定义 equivOfIsKInjective
  签名: [L.是KInjective]
  定义体: Equiv.ofBijective _ (bijective_toSmallShiftedHom_of_isKInjective _ _ _)

Depends on / 依赖: Equiv.ofBijective, bijective_toSmallShiftedHom_of_isKInjective, ofBijective
-/
noncomputable def equivOfIsKInjective [L.IsKInjective] :
    CohomologyClass K L n ≃
      SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (.up Int)) K L n :=
  Equiv.ofBijective _ (bijective_toSmallShiftedHom_of_isKInjective _ _ _)

end HomComplex.CohomologyClass

open HomologicalComplex

/--
lemma `quasiIso_iff_of_injective` / 引理 `quasiIso_iff_of_injective`

English:
lemma quasiIso_iff_of_injective
  statement: {K L : CochainComplex C Nat}
  proof: by
  rw [← quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat]; rw [CochainComplex.IsKInjective.quasiIso_iff]; rw [homotopyEquivalences_extendMap_iff]

中文:
引理 quasiIso_iff_of_injective
  结论: {K L : 上链复形 C 自然数}
  证明: by
  rw [← quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat]; rw [CochainComplex.IsKInjective.quasiIso_iff]; rw [homotopyEquivalences_extendMap_iff]

Depends on / 依赖: CochainComplex, CochainComplex.IsKInjective.quasiIso_iff, ComplexShape, ComplexShape.embeddingUpNat, IsKInjective, embeddingUpNat, homotopyEquivalences_extendMap_iff, quasiIso_extendMap_iff, quasiIso_iff
-/
lemma quasiIso_iff_of_injective {K L : CochainComplex C Nat}
    [forall n, Injective (K.X n)] [forall n, Injective (L.X n)]
    (f : K ⟶ L) :
    QuasiIso f ↔ homotopyEquivalences C (.up Nat) f := by
  rw [← quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat]; rw [CochainComplex.IsKInjective.quasiIso_iff]; rw [homotopyEquivalences_extendMap_iff]

end CochainComplex
