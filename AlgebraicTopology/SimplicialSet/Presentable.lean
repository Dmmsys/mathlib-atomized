/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.AlgebraicTopology.SimplicialSet.RegularEpi
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Presentable.Presheaf

/-!
# Finite simplicial sets are presentable

In this file, we show that finite simplicial sets are finitely presentable,
which will allow the use of the small object argument in `SSet`.

-/

public section

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

namespace Finite

instance (n : SimplexCategory) :
    IsFinitelyPresentable.{u} (stdSimplex.{u}.obj n) :=
  inferInstanceAs (IsFinitelyPresentable.{u} (uliftYoneda.obj n))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_epi_from_isCardinalPresentable` / 引理 `exists_epi_from_isCardinalPresentable`

English:
lemma exists_epi_from_isCardinalPresentable
  given: (X : SSet.{u}) [X.Finite]
  proof: by
  refine ⟨∐ (fun (s : X.N) => Δ[s.dim]), inferInstance, ?_,
    Sigma.desc (fun s => yonedaEquiv.symm s.simplex), ?_⟩
  · apply +allowSynthFailures isCardinalPresentable_of_isColimit' _ (coproductIsCoproduct _)
    · exact hasCardinalLT_of_finite _ _ (by rfl)
    · rintro s
      dsimp
      infe

中文:
引理 exists_epi_from_isCardinalPresentable
  条件: (X : SSet.{u}) [X.Finite]
  证明: by
  refine ⟨∐ (fun (s : X.N) => Δ[s.dim]), inferInstance, ?_,
    Sigma.desc (fun s => yonedaEquiv.symm s.simplex), ?_⟩
  · apply +allowSynthFailures isCardinalPresentable_of_isColimit' _ (coproductIsCoproduct _)
    · exact hasCardinalLT_of_finite _ _ (by rfl)
    · rintro s
      dsimp
      infe

Depends on / 依赖: Cofan.mk_, Equiv.apply_symm_apply, N.iSup_subcomplex_eq_top, Sigma.desc, Subcomplex, Subcomplex.range_eq_ofSimplex, Subcomplex.range_eq_top_iff, allowSynthFailures, apply_symm_apply, colimit, coproductIsCoproduct, hasCardinalLT_of_finite, iSup_subcomplex_eq_top, infer_instance, isCardinalPresentable_of_isColimit, range_eq_ofSimplex, range_eq_top_iff, s.dim, s.simplex, simplex
-/
lemma exists_epi_from_isCardinalPresentable (X : SSet.{u}) [X.Finite] :
    exists (Y : SSet.{u}) (_ : Y.Finite) (_ : IsFinitelyPresentable.{u} Y)
      (p : Y ⟶ X), Epi p := by
  refine ⟨∐ (fun (s : X.N) => Δ[s.dim]), inferInstance, ?_,
    Sigma.desc (fun s => yonedaEquiv.symm s.simplex), ?_⟩
  · apply +allowSynthFailures isCardinalPresentable_of_isColimit' _ (coproductIsCoproduct _)
    · exact hasCardinalLT_of_finite _ _ (by rfl)
    · rintro s
      dsimp
      infer_instance
  · simp only [← Subcomplex.range_eq_top_iff, range_eq_iSup_sigma_ι,
        colimit.ι_desc, Cofan.mk_ι_app, ← N.iSup_subcomplex_eq_top,
        Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]

instance (X : SSet.{u}) [X.Finite] : IsFinitelyPresentable.{u} X := by
  obtain ⟨Y, _, _, p, _⟩ := exists_epi_from_isCardinalPresentable X
  obtain ⟨Z, _, _, q, _⟩ := exists_epi_from_isCardinalPresentable (pullback p p)
  have := Cardinal.fact_isRegular_aleph0.{u}
  have := IsRegularEpiCategory.regularEpiOfEpi p
  apply +allowSynthFailures isCardinalPresentable_of_isColimit' _
      (isCoequalizerEpiComp ((EffectiveEpi.getStruct p).isColimitCoforkOfIsPullback
        (IsPullback.of_hasPullback p p)) q) _
  · exact hasCardinalLT_of_finite _ _ (by rfl)
  · rintro (_ | _) <;> dsimp <;> infer_instance

end Finite

end SSet
