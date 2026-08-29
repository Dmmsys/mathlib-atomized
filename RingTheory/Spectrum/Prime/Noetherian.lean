/-
Copyright (c) 2020 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Andrew Yang
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.NoetherianSpace

/-!
This file proves additional properties of the prime spectrum a ring is Noetherian.
-/

public section


universe u v

namespace PrimeSpectrum

open TopologicalSpace

section IsNoetherianRing

variable (R : Type u) [CommSemiring R] [IsNoetherianRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoetherianSpace (PrimeSpectrum R)
  body: ((noetherianSpace_TFAE <| PrimeSpectrum R).out 0 1).mpr (closedsEmbedding R).dual.wellFoundedLT

中文:
实例 :
  签名: NoetherianSpace (PrimeSpectrum R)
  定义体: ((noetherianSpace_TFAE <| PrimeSpectrum R).out 0 1).mpr (closedsEmbedding R).dual.wellFoundedLT

Depends on / 依赖: PrimeSpectrum, closedsEmbedding, dual.wellFoundedLT, noetherianSpace_TFAE, wellFoundedLT
-/
instance : NoetherianSpace (PrimeSpectrum R) :=
  ((noetherianSpace_TFAE <| PrimeSpectrum R).out 0 1).mpr (closedsEmbedding R).dual.wellFoundedLT

/--
lemma `finite_setOfPred_isMin` / 引理 `finite_setOfPred_isMin`

English:
lemma finite_setOfPred_isMin
  proof: by
  have : Function.Injective (asIdeal (R := R)) := @PrimeSpectrum.ext _ _
  refine Set.Finite.of_finite_image (f := asIdeal) ?_ this.injOn
  simp_rw [isMin_iff]
  exact (minimalPrimes.finite_of_isNoetherianRing R).subset (Set.image_preimage_subset _ _)

@[deprecated (since := "2026-07-09")] alias 

中文:
引理 finite_setOfPred_isMin
  证明: by
  have : Function.Injective (asIdeal (R := R)) := @PrimeSpectrum.ext _ _
  refine Set.Finite.of_finite_image (f := asIdeal) ?_ this.injOn
  simp_rw [isMin_iff]
  exact (minimalPrimes.finite_of_isNoetherianRing R).subset (Set.image_preimage_subset _ _)

@[deprecated (since := "2026-07-09")] alias 

Depends on / 依赖: Finite, Function, Function.Injective, Injective, PrimeSpectrum, PrimeSpectrum.ext, Set.Finite.of_finite_image, Set.image_preimage_subset, asIdeal, finite_of_isNoetherianRing, image_preimage_subset, isMin_iff, minimalPrimes, minimalPrimes.finite_of_isNoetherianRing, of_finite_image, simp_rw, subset, this.injOn
-/
lemma finite_setOfPred_isMin :
    {x : PrimeSpectrum R | IsMin x}.Finite := by
  have : Function.Injective (asIdeal (R := R)) := @PrimeSpectrum.ext _ _
  refine Set.Finite.of_finite_image (f := asIdeal) ?_ this.injOn
  simp_rw [isMin_iff]
  exact (minimalPrimes.finite_of_isNoetherianRing R).subset (Set.image_preimage_subset _ _)

@[deprecated (since := "2026-07-09")] alias finite_setOf_isMin := finite_setOfPred_isMin

end IsNoetherianRing

end PrimeSpectrum

namespace IsArtinianRing

open PrimeSpectrum

variable (R : Type*) [CommRing R] [IsArtinianRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ring.KrullDimLE 0 R
  body: .mk₀ fun _ _ => inferInstance

中文:
实例 :
  签名: Ring.KrullDimLE 0 R
  定义体: .mk₀ fun _ _ => inferInstance
-/
instance : Ring.KrullDimLE 0 R := .mk₀ fun _ _ => inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology (PrimeSpectrum R)
  body: discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨inferInstance, inferInstance⟩

中文:
实例 :
  签名: DiscreteTopology (PrimeSpectrum R)
  定义体: discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨inferInstance, inferInstance⟩

Depends on / 依赖: discreteTopology_iff_finite_and_krullDimLE_zero, discreteTopology_iff_finite_and_krullDimLE_zero.mpr
-/
instance : DiscreteTopology (PrimeSpectrum R) :=
  discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨inferInstance, inferInstance⟩

variable {R} in
/--
lemma `exists_not_mem_forall_mem_of_ne` / 引理 `exists_not_mem_forall_mem_of_ne`

English:
lemma exists_not_mem_forall_mem_of_ne
  given: (p : Ideal R) [p.IsPrime]
  proof: by
  classical
  obtain ⟨r, hr⟩ := PrimeSpectrum.toPiLocalization_bijective.2 (Pi.single ⟨p, inferInstance⟩ 1)
  have : algebraMap R (Localization p.primeCompl) r = 1 := by
    simpa [PrimeSpectrum.toPiLocalization,
      -FaithfulSMul.algebraMap_eq_one_iff] using funext_iff.mp hr ⟨p, inferInstance⟩

中文:
引理 exists_not_mem_forall_mem_of_ne
  条件: (p : Ideal R) [p.IsPrime]
  证明: by
  classical
  obtain ⟨r, hr⟩ := PrimeSpectrum.toPiLocalization_bijective.2 (Pi.single ⟨p, inferInstance⟩ 1)
  have : algebraMap R (Localization p.primeCompl) r = 1 := by
    simpa [PrimeSpectrum.toPiLocalization,
      -FaithfulSMul.algebraMap_eq_one_iff] using funext_iff.mp hr ⟨p, inferInstance⟩

Depends on / 依赖: AtPrime, FaithfulSMul, FaithfulSMul.algebraMap_eq_one_iff, IsLocalization, IsLocalization.AtPrime.to_map_mem_maximal_iff, Localization, Localization.AtPrime, Pi.single, Pi.single_mul, PrimeSpectrum, PrimeSpectrum.toPiLocalization, PrimeSpectrum.toPiLocalization_bijective, PrimeSpectrum.toPiLocalization_bijective.injective, algebraMap, algebraMap_eq_one_iff, classical, funext_iff, funext_iff.mp, injective, map_mul
-/
lemma exists_not_mem_forall_mem_of_ne (p : Ideal R) [p.IsPrime] :
    exists r ∉ p, IsIdempotentElem r ∧ forall q : Ideal R, q.IsPrime -> q != p -> r in q := by
  classical
  obtain ⟨r, hr⟩ := PrimeSpectrum.toPiLocalization_bijective.2 (Pi.single ⟨p, inferInstance⟩ 1)
  have : algebraMap R (Localization p.primeCompl) r = 1 := by
    simpa [PrimeSpectrum.toPiLocalization,
      -FaithfulSMul.algebraMap_eq_one_iff] using funext_iff.mp hr ⟨p, inferInstance⟩
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p, this]
    simp
  · apply PrimeSpectrum.toPiLocalization_bijective.injective
    simp [map_mul, hr, ← Pi.single_mul]
  · intro q hq e
    have : PrimeSpectrum.mk q inferInstance != ⟨p, inferInstance⟩ := ne_of_apply_ne (·.1) e
    have : (algebraMap R (Localization.AtPrime q)) r = 0 := by
      simpa [PrimeSpectrum.toPiLocalization, this,
        -FaithfulSMul.algebraMap_eq_zero_iff] using funext_iff.mp hr ⟨q, inferInstance⟩
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q]; rw [this]
    simp

variable (F : Type*) [Field F] [Algebra F R] [Module.Finite F R]

/--
theorem `finrank_eq_sum_primeSpectrum` / 定理 `finrank_eq_sum_primeSpectrum`

English:
theorem finrank_eq_sum_primeSpectrum
  given: [Fintype (PrimeSpectrum R)]
  proof: have (p : Ideal R) [p.IsPrime] : Module.Finite F (Localization.AtPrime p) :=
    Module.Finite.of_surjective (Algebra.algHom F R (Localization.AtPrime p)).toLinearMap
      (localization_surjective p.primeCompl (Localization.AtPrime p))
  ((toPiLocalizationEquiv R).restrictScalars F).toLinearEquiv.f

中文:
定理 finrank_eq_sum_primeSpectrum
  条件: [Fintype (PrimeSpectrum R)]
  证明: have (p : Ideal R) [p.IsPrime] : Module.Finite F (Localization.AtPrime p) :=
    Module.Finite.of_surjective (Algebra.algHom F R (Localization.AtPrime p)).toLinearMap
      (localization_surjective p.primeCompl (Localization.AtPrime p))
  ((toPiLocalizationEquiv R).restrictScalars F).toLinearEquiv.f

Depends on / 依赖: Algebra, Algebra.algHom, AtPrime, Finite, IsPrime, Localization, Localization.AtPrime, Module, Module.Finite, Module.Finite.of_surjective, Module.finrank_pi_fintype, algHom, finrank_eq, finrank_pi_fintype, localization_surjective, of_surjective, p.IsPrime, p.primeCompl, primeCompl, restrictScalars
-/
theorem finrank_eq_sum_primeSpectrum [Fintype (PrimeSpectrum R)] :
    Module.finrank F R = ∑ p : PrimeSpectrum R, Module.finrank F (Localization.AtPrime p.asIdeal) :=
  have (p : Ideal R) [p.IsPrime] : Module.Finite F (Localization.AtPrime p) :=
    Module.Finite.of_surjective (Algebra.algHom F R (Localization.AtPrime p)).toLinearMap
      (localization_surjective p.primeCompl (Localization.AtPrime p))
  ((toPiLocalizationEquiv R).restrictScalars F).toLinearEquiv.finrank_eq.trans
    (Module.finrank_pi_fintype F)

end IsArtinianRing
