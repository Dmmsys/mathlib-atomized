/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
public import Mathlib.RingTheory.QuasiFinite.Weakly

/-! # Quasi-finite primes in polynomial algebras -/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

namespace Polynomial

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.WeaklyQuasiFiniteAt.finite_locoalization in
/--
lemma `not_weaklyQuasiFiniteAt` / 引理 `not_weaklyQuasiFiniteAt`

English:
lemma not_weaklyQuasiFiniteAt
  given: (P : Ideal R[X]) [P.IsPrime]
  statement: ¬ Algebra.WeaklyQuasiFiniteAt R P
  proof: by
  intro H
  wlog hR : IsField R
  · let p := P.under R
    obtain ⟨Q, hQ⟩ := (PrimeSpectrum.preimageEquivFiber R R[X]
        ⟨p, inferInstance⟩).symm.surjective ⟨⟨P, ‹_›⟩, rfl⟩
    have inst : Algebra.WeaklyQuasiFiniteAt p.ResidueField Q.asIdeal :=
      .baseChange P Q.asIdeal congr($(hQ.symm).1.1)
    exact this (Q.asIdeal.comap (polyEquivTensor' R p.ResidueField).toRingHom)
      inferInstance (Field.toIsField _)
  let := hR.toField
  have := Module.Finite.of_injective
    (IsScalarTower.toAlgHom R R[X] (Localization.AtPrime P)).toLinearMap
    (IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors)
  exact transcendental_X R (Algebra.IsIntegral.isIntegral X).isAlgebraic

中文:
引理 not_weaklyQuasiFiniteAt
  条件: (P : 理想 R[X]) [P.是素]
  结论: ¬ 代数.WeaklyQuasiFiniteAt R P
  证明: by
  intro H
  wlog hR : IsField R
  · let p := P.under R
    obtain ⟨Q, hQ⟩ := (PrimeSpectrum.preimageEquivFiber R R[X]
        ⟨p, inferInstance⟩).symm.surjective ⟨⟨P, ‹_›⟩, rfl⟩
    have inst : Algebra.WeaklyQuasiFiniteAt p.ResidueField Q.asIdeal :=
      .baseChange P Q.asIdeal congr($(hQ.symm).1.1)
    exact this (Q.asIdeal.comap (polyEquivTensor' R p.ResidueField).toRingHom)
      inferInstance (Field.toIsField _)
  let := hR.toField
  have := Module.Finite.of_injective
    (IsScalarTower.toAlgHom R R[X] (Localization.AtPrime P)).toLinearMap
    (IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors)
  exact transcendental_X R (Algebra.IsIntegral.isIntegral X).isAlgebraic

Depends on / 依赖: Algebra, Algebra.WeaklyQuasiFiniteAt, AtPrime, Field.toIsField, Finite, IsField, IsScalarTower, IsScalarTower.toAlgHom, Localization, Localization.AtPrime, Module, Module.Finite.of_injective, P.under, PrimeSpectrum, PrimeSpectrum.preimageEquivFiber, Q.asIdeal, Q.asIdeal.comap, ResidueField, WeaklyQuasiFiniteAt, asIdeal
-/
lemma not_weaklyQuasiFiniteAt (P : Ideal R[X]) [P.IsPrime] : ¬ Algebra.WeaklyQuasiFiniteAt R P := by
  intro H
  wlog hR : IsField R
  · let p := P.under R
    obtain ⟨Q, hQ⟩ := (PrimeSpectrum.preimageEquivFiber R R[X]
        ⟨p, inferInstance⟩).symm.surjective ⟨⟨P, ‹_›⟩, rfl⟩
    have inst : Algebra.WeaklyQuasiFiniteAt p.ResidueField Q.asIdeal :=
      .baseChange P Q.asIdeal congr($(hQ.symm).1.1)
    exact this (Q.asIdeal.comap (polyEquivTensor' R p.ResidueField).toRingHom)
      inferInstance (Field.toIsField _)
  let := hR.toField
  have := Module.Finite.of_injective
    (IsScalarTower.toAlgHom R R[X] (Localization.AtPrime P)).toLinearMap
    (IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors)
  exact transcendental_X R (Algebra.IsIntegral.isIntegral X).isAlgebraic

/--
lemma `not_quasiFiniteAt` / 引理 `not_quasiFiniteAt`

English:
lemma not_quasiFiniteAt
  given: (P : Ideal R[X]) [P.IsPrime]
  statement: ¬ Algebra.QuasiFiniteAt R P
  proof: fun _ => not_weaklyQuasiFiniteAt P inferInstance

中文:
引理 not_quasiFiniteAt
  条件: (P : 理想 R[X]) [P.是素]
  结论: ¬ 代数.QuasiFiniteAt R P
  证明: fun _ => not_weaklyQuasiFiniteAt P inferInstance

Depends on / 依赖: DFunLike, DFunLike.coe, Function, Function.const_injective, const_injective, ne_of_apply_ne, not_weaklyQuasiFiniteAt, zero_ne_one
-/
lemma not_quasiFiniteAt (P : Ideal R[X]) [P.IsPrime] : ¬ Algebra.QuasiFiniteAt R P :=
  fun _ => not_weaklyQuasiFiniteAt P inferInstance

/--
lemma `map_under_lt_comap_of_weaklyQuasiFiniteAt` / 引理 `map_under_lt_comap_of_weaklyQuasiFiniteAt`

English:
lemma map_under_lt_comap_of_weaklyQuasiFiniteAt
  proof: by
  algebraize [f.toRingHom]
  refine lt_of_le_of_ne (Ideal.map_le_iff_le_comap.mpr ?_) fun e => ?_
  · rw [Ideal.comap_comap, ← algebraMap_eq, f.comp_algebraMap]
  let := Localization.AtPrime.algebraOfLiesOver (P.under R) (P.under R[X])
  let := Localization.AtPrime.algebraOfLiesOver (P.under R[X]) P
  let := Localization.AtPrime.algebraOfLiesOver (P.under R) P
  have : Module.Finite (Ideal.under R P).ResidueField P.ResidueField :=
    Algebra.WeaklyQuasiFiniteAt.finite_residueField ..
  have : Module.Finite (P.under R).ResidueField (P.under R[X]).ResidueField :=
    .of_injective (IsScalarTower.toAlgHom _ _ P.ResidueField).toLinearMap
      (algebraMap (P.under R[X]).ResidueField P.ResidueField).injective
  have : Module.Finite (P.under R).ResidueField (RatFunc (P.under R).ResidueField) :=
    .of_surjective (residueFieldMapCAlgEquiv _ (P.under _) e.symm).toLinearMap
      (residueFieldMapCAlgEquiv _ (P.under _) e.symm).surjective
  exact RatFunc.transcendental_X (K := (P.under R).ResidueField)
    (Algebra.IsIntegral.isIntegral _).isAlgebraic

中文:
引理 map_under_lt_comap_of_weaklyQuasiFiniteAt
  证明: by
  algebraize [f.toRingHom]
  refine lt_of_le_of_ne (Ideal.map_le_iff_le_comap.mpr ?_) fun e => ?_
  · rw [Ideal.comap_comap, ← algebraMap_eq, f.comp_algebraMap]
  let := Localization.AtPrime.algebraOfLiesOver (P.under R) (P.under R[X])
  let := Localization.AtPrime.algebraOfLiesOver (P.under R[X]) P
  let := Localization.AtPrime.algebraOfLiesOver (P.under R) P
  have : Module.Finite (Ideal.under R P).ResidueField P.ResidueField :=
    Algebra.WeaklyQuasiFiniteAt.finite_residueField ..
  have : Module.Finite (P.under R).ResidueField (P.under R[X]).ResidueField :=
    .of_injective (IsScalarTower.toAlgHom _ _ P.ResidueField).toLinearMap
      (algebraMap (P.under R[X]).ResidueField P.ResidueField).injective
  have : Module.Finite (P.under R).ResidueField (RatFunc (P.under R).ResidueField) :=
    .of_surjective (residueFieldMapCAlgEquiv _ (P.under _) e.symm).toLinearMap
      (residueFieldMapCAlgEquiv _ (P.under _) e.symm).surjective
  exact RatFunc.transcendental_X (K := (P.under R).ResidueField)
    (Algebra.IsIntegral.isIntegral _).isAlgebraic

Depends on / 依赖: Algebra, Algebra.WeaklyQuasiFiniteAt.finite_residueField, AtPrime, Finite, Ideal.comap_comap, Ideal.map_le_iff_le_comap.mpr, Ideal.under, Localization, Localization.AtPrime.algebraOfLiesOver, Module, Module.Finite, P.ResidueField, P.under, ResidueField, WeaklyQuasiFiniteAt, algebraMap_eq, algebraOfLiesOver, algebraize, comap_comap, comp_algebraMap
-/
lemma map_under_lt_comap_of_weaklyQuasiFiniteAt
    (f : R[X] ->ₐ[R] S) (P : Ideal S) [P.IsPrime] [Algebra.WeaklyQuasiFiniteAt R P] :
    (P.under R).map C < P.comap (f : R[X] ->+* S) := by
  algebraize [f.toRingHom]
  refine lt_of_le_of_ne (Ideal.map_le_iff_le_comap.mpr ?_) fun e => ?_
  · rw [Ideal.comap_comap, ← algebraMap_eq, f.comp_algebraMap]
  let := Localization.AtPrime.algebraOfLiesOver (P.under R) (P.under R[X])
  let := Localization.AtPrime.algebraOfLiesOver (P.under R[X]) P
  let := Localization.AtPrime.algebraOfLiesOver (P.under R) P
  have : Module.Finite (Ideal.under R P).ResidueField P.ResidueField :=
    Algebra.WeaklyQuasiFiniteAt.finite_residueField ..
  have : Module.Finite (P.under R).ResidueField (P.under R[X]).ResidueField :=
    .of_injective (IsScalarTower.toAlgHom _ _ P.ResidueField).toLinearMap
      (algebraMap (P.under R[X]).ResidueField P.ResidueField).injective
  have : Module.Finite (P.under R).ResidueField (RatFunc (P.under R).ResidueField) :=
    .of_surjective (residueFieldMapCAlgEquiv _ (P.under _) e.symm).toLinearMap
      (residueFieldMapCAlgEquiv _ (P.under _) e.symm).surjective
  exact RatFunc.transcendental_X (K := (P.under R).ResidueField)
    (Algebra.IsIntegral.isIntegral _).isAlgebraic

/--
lemma `map_under_lt_comap_of_quasiFiniteAt` / 引理 `map_under_lt_comap_of_quasiFiniteAt`

English:
lemma map_under_lt_comap_of_quasiFiniteAt
  proof: map_under_lt_comap_of_weaklyQuasiFiniteAt f P

中文:
引理 map_under_lt_comap_of_quasiFiniteAt
  证明: map_under_lt_comap_of_weaklyQuasiFiniteAt f P

Depends on / 依赖: map_under_lt_comap_of_weaklyQuasiFiniteAt
-/
lemma map_under_lt_comap_of_quasiFiniteAt
    (f : R[X] ->ₐ[R] S) (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] :
    (P.under R).map C < P.comap (f : R[X] ->+* S) :=
  map_under_lt_comap_of_weaklyQuasiFiniteAt f P

/--
lemma `not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt` / 引理 `not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt`

English:
lemma not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt
  proof: by
  intro H
  algebraize [f.toRingHom]
  let p := P.under R
  have H' : (RingHom.ker f).map (mapRingHom (algebraMap R p.ResidueField)) = ⊥ := by
    rw [← le_bot_iff]; rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using! H hx
  let g' : p.ResidueField[X] ≃ₐ[p.ResidueField] p.Fiber S :=
    .trans ((AlgEquiv.quotientBot _ _).symm.trans (Ideal.quotientEquivAlgOfEq _ H'.symm))
      (Polynomial.fiberEquivQuotient f hf _).symm
  obtain ⟨Q, hQ⟩ := (PrimeSpectrum.preimageEquivFiber _ _
      ⟨p, inferInstance⟩).symm.surjective ⟨⟨P, ‹_›⟩, PrimeSpectrum.ext (P.over_def p).symm⟩
  have inst : Algebra.WeaklyQuasiFiniteAt p.ResidueField Q.asIdeal :=
    .baseChange P Q.asIdeal congr($(hQ.symm).1.1)
  exact Polynomial.not_weaklyQuasiFiniteAt (Q.asIdeal.comap g'.toRingHom) inferInstance

中文:
引理 not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt
  证明: by
  intro H
  algebraize [f.toRingHom]
  let p := P.under R
  have H' : (RingHom.ker f).map (mapRingHom (algebraMap R p.ResidueField)) = ⊥ := by
    rw [← le_bot_iff]; rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using! H hx
  let g' : p.ResidueField[X] ≃ₐ[p.ResidueField] p.Fiber S :=
    .trans ((AlgEquiv.quotientBot _ _).symm.trans (Ideal.quotientEquivAlgOfEq _ H'.symm))
      (Polynomial.fiberEquivQuotient f hf _).symm
  obtain ⟨Q, hQ⟩ := (PrimeSpectrum.preimageEquivFiber _ _
      ⟨p, inferInstance⟩).symm.surjective ⟨⟨P, ‹_›⟩, PrimeSpectrum.ext (P.over_def p).symm⟩
  have inst : Algebra.WeaklyQuasiFiniteAt p.ResidueField Q.asIdeal :=
    .baseChange P Q.asIdeal congr($(hQ.symm).1.1)
  exact Polynomial.not_weaklyQuasiFiniteAt (Q.asIdeal.comap g'.toRingHom) inferInstance

Depends on / 依赖: AlgEquiv, AlgEquiv.quotientBot, Ideal.map_le_iff_le_comap, Ideal.mem_map_C_iff, Ideal.quotientEquivAlgOfEq, P.under, Polynomial, Polynomial.ext_iff, Polynomial.fiberEquivQuotient, PrimeSpectrum, PrimeSpectrum.preimageEquivFiber, ResidueField, RingHom, RingHom.ker, algebraMap, algebraize, ext_iff, f.toRingHom, fiberEquivQuotient, le_bot_iff
-/
lemma not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt
    (f : R[X] ->ₐ[R] S) (hf : Function.Surjective f)
    (P : Ideal S) [P.IsPrime] [Algebra.WeaklyQuasiFiniteAt R P] :
    ¬ RingHom.ker f <= (P.under R).map C := by
  intro H
  algebraize [f.toRingHom]
  let p := P.under R
  have H' : (RingHom.ker f).map (mapRingHom (algebraMap R p.ResidueField)) = ⊥ := by
    rw [← le_bot_iff]; rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using! H hx
  let g' : p.ResidueField[X] ≃ₐ[p.ResidueField] p.Fiber S :=
    .trans ((AlgEquiv.quotientBot _ _).symm.trans (Ideal.quotientEquivAlgOfEq _ H'.symm))
      (Polynomial.fiberEquivQuotient f hf _).symm
  obtain ⟨Q, hQ⟩ := (PrimeSpectrum.preimageEquivFiber _ _
      ⟨p, inferInstance⟩).symm.surjective ⟨⟨P, ‹_›⟩, PrimeSpectrum.ext (P.over_def p).symm⟩
  have inst : Algebra.WeaklyQuasiFiniteAt p.ResidueField Q.asIdeal :=
    .baseChange P Q.asIdeal congr($(hQ.symm).1.1)
  exact Polynomial.not_weaklyQuasiFiniteAt (Q.asIdeal.comap g'.toRingHom) inferInstance

/--
lemma `not_ker_le_map_C_of_surjective_of_quasiFiniteAt` / 引理 `not_ker_le_map_C_of_surjective_of_quasiFiniteAt`

English:
lemma not_ker_le_map_C_of_surjective_of_quasiFiniteAt
  proof: not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt f hf P

中文:
引理 not_ker_le_map_C_of_surjective_of_quasiFiniteAt
  证明: not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt f hf P

Depends on / 依赖: LocallyConstant, LocallyConstant.coeFnAddMonoidHom, LocallyConstant.coe_injective.isAddTorsionFree, coeFnAddMonoidHom, coe_injective, isAddTorsionFree, not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt
-/
lemma not_ker_le_map_C_of_surjective_of_quasiFiniteAt
    (f : R[X] ->ₐ[R] S) (hf : Function.Surjective f)
    (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] :
    ¬ RingHom.ker f <= (P.under R).map C :=
  not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt f hf P

end Polynomial
