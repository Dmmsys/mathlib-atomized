/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.CategoryTheory.ObjectProperty.Small


/-! # Smallness results on the category of `CommRing` -/

@[expose] public section

universe u

open CategoryTheory

namespace CommRingCat

variable {P Q : ObjectProperty CommRingCat.{u}}

/--
lemma `essentiallySmall_of_finiteType` / 引理 `essentiallySmall_of_finiteType`

English:
lemma essentiallySmall_of_finiteType
  statement: [ObjectProperty.EssentiallySmall.{u} Q]
  proof: by
  obtain ⟨Q', _, hQ'Q, hQQ'⟩ := ObjectProperty.EssentiallySmall.exists_small_le Q
  let f (S : Σ R : Subtype Q', FGAlgCatSkeleton R) : CommRingCat := .of S.2.eval.obj
  refine ⟨.ofObj f, inferInstance, fun S hS => ?_⟩
  obtain ⟨R, hR, φ, hφ⟩ := hPQ S hS
  wlog hR' : Q' R generalizing R
  · obtain

中文:
引理 essentiallySmall_of_finiteType
  结论: [ObjectProperty.EssentiallySmall.{u} Q]
  证明: by
  obtain ⟨Q', _, hQ'Q, hQQ'⟩ := ObjectProperty.EssentiallySmall.exists_small_le Q
  let f (S : Σ R : Subtype Q', FGAlgCatSkeleton R) : CommRingCat := .of S.2.eval.obj
  refine ⟨.ofObj f, inferInstance, fun S hS => ?_⟩
  obtain ⟨R, hR, φ, hφ⟩ := hPQ S hS
  wlog hR' : Q' R generalizing R
  · obtain

Depends on / 依赖: CommRingCat, EssentiallySmall, FGAlgCatSkeleton, ObjectProperty, ObjectProperty.EssentiallySmall.exists_small_le, RingEquiv, RingEquiv.to, Subtype, commRingCatIsoToRingEquiv, e.inv, e.symm.commRingCatIsoToRingEquiv.finite.finiteType, eval.obj, exists_smallRepr, exists_small_le, finite, finiteType, generalizing
-/
lemma essentiallySmall_of_finiteType [ObjectProperty.EssentiallySmall.{u} Q]
    (hPQ : forall S, P S -> exists R, Q R ∧ exists (f : R ⟶ S), f.hom.FiniteType) :
    ObjectProperty.EssentiallySmall.{u} P := by
  obtain ⟨Q', _, hQ'Q, hQQ'⟩ := ObjectProperty.EssentiallySmall.exists_small_le Q
  let f (S : Σ R : Subtype Q', FGAlgCatSkeleton R) : CommRingCat := .of S.2.eval.obj
  refine ⟨.ofObj f, inferInstance, fun S hS => ?_⟩
  obtain ⟨R, hR, φ, hφ⟩ := hPQ S hS
  wlog hR' : Q' R generalizing R
  · obtain ⟨R', hR', ⟨e⟩⟩ := hQQ' _ hR
    exact this R' (hQ'Q _ hR') (e.inv ≫ φ)
      (hφ.comp e.symm.commRingCatIsoToRingEquiv.finite.finiteType) hR'
  obtain ⟨T, e, he⟩ := hφ.exists_smallRepr
  exact ⟨_, ⟨⟨_, hR'⟩, T⟩, ⟨RingEquiv.toCommRingCatIso e.symm⟩⟩

/--
lemma `essentiallySmall_of_localizationAway` / 引理 `essentiallySmall_of_localizationAway`

English:
lemma essentiallySmall_of_localizationAway
  statement: [ObjectProperty.EssentiallySmall.{u} Q]
  proof: by
  obtain ⟨Q', _, hQ'Q, hQQ'⟩ := ObjectProperty.EssentiallySmall.exists_small_le Q
  let f (S : Σ (n : Nat) (R : Fin n -> Subtype Q'), Subring (Π i, (R i).1)) : CommRingCat := .of S.2.2
  refine ⟨.ofObj f, inferInstance, fun S hS => ?_⟩
  obtain ⟨s, hs, H⟩ := hPQ S hS
  wlog hs' : s.Finite general

中文:
引理 essentiallySmall_of_localizationAway
  结论: [ObjectProperty.EssentiallySmall.{u} Q]
  证明: by
  obtain ⟨Q', _, hQ'Q, hQQ'⟩ := ObjectProperty.EssentiallySmall.exists_small_le Q
  let f (S : Σ (n : Nat) (R : Fin n -> Subtype Q'), Subring (Π i, (R i).1)) : CommRingCat := .of S.2.2
  refine ⟨.ofObj f, inferInstance, fun S hS => ?_⟩
  obtain ⟨s, hs, H⟩ := hPQ S hS
  wlog hs' : s.Finite general

Depends on / 依赖: CommRingCat, EssentiallySmall, Finite, Ideal.span_eq_top_iff_finite, ObjectProperty, ObjectProperty.EssentiallySmall.exists_small_le, Subring, Subtype, exists_small_le, finite_toSet, generalizing, s.Finite, span_eq_top_iff_finite
-/
lemma essentiallySmall_of_localizationAway [ObjectProperty.EssentiallySmall.{u} Q]
    (hPQ : forall S, P S -> exists s : Set S, Ideal.span s = ⊤ ∧ forall f in s, Q (.of (Localization.Away f))) :
    ObjectProperty.EssentiallySmall.{u} P := by
  obtain ⟨Q', _, hQ'Q, hQQ'⟩ := ObjectProperty.EssentiallySmall.exists_small_le Q
  let f (S : Σ (n : Nat) (R : Fin n -> Subtype Q'), Subring (Π i, (R i).1)) : CommRingCat := .of S.2.2
  refine ⟨.ofObj f, inferInstance, fun S hS => ?_⟩
  obtain ⟨s, hs, H⟩ := hPQ S hS
  wlog hs' : s.Finite generalizing s
  · obtain ⟨s', hs's, hs'⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
    exact this s' hs' (fun f hf => H f (hs's hf)) s'.finite_toSet
  choose S' hS' e using fun (f : s) => hQQ' _ (H _ f.2)
  let φ : S ->+* Π i, S' (hs'.equivFin.symm i) :=
    ((RingEquiv.piCongrRight fun i => (e i).some.commRingCatIsoToRingEquiv).trans
      (RingEquiv.piCongrLeft (S' ·) hs'.equivFin.symm).symm).toRingHom.comp (algebraMap _ _)
  have hφ : Function.Injective φ := by
    dsimp only [RingHom.coe_comp, φ]
    refine (RingEquiv.injective _).comp (Localization.algebraMap_injective_of_span_eq_top _ hs)
  refine ⟨_, ⟨Nat.card s, (fun f => ⟨S' f, hS' f⟩) ∘ hs'.equivFin.symm, φ.range⟩, ⟨?_⟩⟩
  exact (RingEquiv.ofBijective φ.rangeRestrict
    ⟨φ.injective_codRestrict.mpr hφ, φ.rangeRestrict_surjective⟩).toCommRingCatIso

end CommRingCat
