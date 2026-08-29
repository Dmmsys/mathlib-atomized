/-
Copyright (c) 2025 Christian Merten, Yi Song, Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Yi Song, Sihan Su
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Properties of faithfully flat algebras

An `A`-algebra `B` is faithfully flat if `B` is faithfully flat as an `A`-module. In this
file we give equivalent characterizations of faithful flatness in the algebra case.

## Main results

Let `B` be a faithfully flat `A`-algebra:

- `Ideal.comap_map_eq_self_of_faithfullyFlat`: the contraction of the extension of any ideal of
  `A` to `B` is the ideal itself.
- `Module.FaithfullyFlat.tensorProduct_mk_injective`: The natural map `M →ₗ[A] B ⊗[A] M` is
  injective for any `A`-module `M`.
- `PrimeSpectrum.comap_surjective_of_faithfullyFlat`: The map on prime spectra induced by
  a faithfully flat ring map is surjective. See also
  `Ideal.exists_isPrime_liesOver_of_faithfullyFlat` for a version stated in terms of
  `Ideal.LiesOver`.

Conversely, let `B` be a flat `A`-algebra:

- `Module.FaithfullyFlat.of_comap_surjective`: `B` is faithfully flat over `A`,
  if the induced map on prime spectra is surjective.
- `Module.FaithfullyFlat.of_flat_of_isLocalHom`: flat + local implies faithfully flat

-/

public section

universe u v

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

open TensorProduct LinearMap

/--
lemma `Module.FaithfullyFlat.of_comap_surjective` / 引理 `Module.FaithfullyFlat.of_comap_surjective`

English:
lemma Module.FaithfullyFlat.of_comap_surjective
  statement: [Flat A B]
  proof: by
  refine ⟨fun m hm => ?_⟩
  obtain ⟨m', hm'⟩ := h ⟨m, hm.isPrime⟩
  have : m = Ideal.comap (algebraMap A B) m'.asIdeal := by
    rw [← PrimeSpectrum.comap_asIdeal (algebraMap A B) m']; rw [hm']
  rw [Ideal.smul_top_eq_map]; rw [this]
  exact (Submodule.restrictScalars_eq_top_iff _ _ _).ne.mpr
fun

中文:
引理 Module.FaithfullyFlat.of_comap_surjective
  结论: [Flat A B]
  证明: by
  refine ⟨fun m hm => ?_⟩
  obtain ⟨m', hm'⟩ := h ⟨m, hm.isPrime⟩
  have : m = Ideal.comap (algebraMap A B) m'.asIdeal := by
    rw [← PrimeSpectrum.comap_asIdeal (algebraMap A B) m']; rw [hm']
  rw [Ideal.smul_top_eq_map]; rw [this]
  exact (Submodule.restrictScalars_eq_top_iff _ _ _).ne.mpr
fun

Depends on / 依赖: Ideal.comap, Ideal.map_comap_le, Ideal.smul_top_eq_map, PrimeSpectrum, PrimeSpectrum.comap_asIdeal, Submodule, Submodule.restrictScalars_eq_top_iff, algebraMap, asIdeal, comap_asIdeal, hm.isPrime, isPrime, isPrime.ne_top, map_comap_le, ne.mpr, ne_top, restrictScalars_eq_top_iff, smul_top_eq_map, top_le_iff, top_le_iff.mp
-/
lemma Module.FaithfullyFlat.of_comap_surjective [Flat A B]
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) :
    Module.FaithfullyFlat A B := by
  refine ⟨fun m hm => ?_⟩
  obtain ⟨m', hm'⟩ := h ⟨m, hm.isPrime⟩
  have : m = Ideal.comap (algebraMap A B) m'.asIdeal := by
    rw [← PrimeSpectrum.comap_asIdeal (algebraMap A B) m']; rw [hm']
  rw [Ideal.smul_top_eq_map]; rw [this]
  exact (Submodule.restrictScalars_eq_top_iff _ _ _).ne.mpr
fun top => m'.isPrime.ne_top top_le_iff.mp top ▸ Ideal.map_comap_le

/--
lemma `Module.FaithfullyFlat.of_flat_of_isLocalHom` / 引理 `Module.FaithfullyFlat.of_flat_of_isLocalHom`

English:
lemma Module.FaithfullyFlat.of_flat_of_isLocalHom
  statement: [IsLocalRing A] [IsLocalRing B] [Flat A B]
  proof: by
  refine ⟨fun m hm => ?_⟩
  rw [Ideal.smul_top_eq_map]; rw [IsLocalRing.eq_maximalIdeal hm]
  by_contra eqt
  have : Submodule.restrictScalars A (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) <=
      Submodule.restrictScalars A (IsLocalRing.maximalIdeal B) :=
    ((IsLocalRing.local_h

中文:
引理 Module.FaithfullyFlat.of_flat_of_isLocalHom
  结论: [IsLocalRing A] [IsLocalRing B] [Flat A B]
  证明: by
  refine ⟨fun m hm => ?_⟩
  rw [Ideal.smul_top_eq_map]; rw [IsLocalRing.eq_maximalIdeal hm]
  by_contra eqt
  have : Submodule.restrictScalars A (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) <=
      Submodule.restrictScalars A (IsLocalRing.maximalIdeal B) :=
    ((IsLocalRing.local_h

Depends on / 依赖: Ideal.IsPrime.ne_top, Ideal.map, Ideal.smul_top_eq_map, IsLocalRing, IsLocalRing.eq_maximalIdeal, IsLocalRing.local_hom_TFAE, IsLocalRing.maximalIdeal, IsPrime, Submodule, Submodule.restrictScalars, Submodule.restrictScalars_eq_top_iff, algebraMap, eq_maximalIdeal, local_hom_TFAE, maximalIdeal, ne_top, restrictScalars, restrictScalars_eq_top_iff, smul_top_eq_map, top_le_iff
-/
lemma Module.FaithfullyFlat.of_flat_of_isLocalHom [IsLocalRing A] [IsLocalRing B] [Flat A B]
    [IsLocalHom (algebraMap A B)] : Module.FaithfullyFlat A B := by
  refine ⟨fun m hm => ?_⟩
  rw [Ideal.smul_top_eq_map]; rw [IsLocalRing.eq_maximalIdeal hm]
  by_contra eqt
  have : Submodule.restrictScalars A (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) <=
      Submodule.restrictScalars A (IsLocalRing.maximalIdeal B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 0 2).mp ‹_›
  rw [eqt]; rw [top_le_iff]; rw [Submodule.restrictScalars_eq_top_iff] at this
  exact Ideal.IsPrime.ne_top' this

/--
Instance `Module.FaithfullyFlat.of_isIntegral_of_isDomain` / 实例 `Module.FaithfullyFlat.of_isIntegral_of_isDomain`

English:
instance Module.FaithfullyFlat.of_isIntegral_of_isDomain
  signature: [IsDomain B] [Module.Flat A B]
  body: by
  refine Module.FaithfullyFlat.of_comap_surjective fun P => ?_
  obtain ⟨P, hP₁, hP₂⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain P.1 (S := B)
    (by simp [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)])
  exact ⟨⟨P, hP₁⟩, PrimeSpectrum.ext_iff.mp

中文:
实例 Module.FaithfullyFlat.of_isIntegral_of_isDomain
  签名: [IsDomain B] [Module.Flat A B]
  定义体: by
  refine Module.FaithfullyFlat.of_comap_surjective fun P => ?_
  obtain ⟨P, hP₁, hP₂⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain P.1 (S := B)
    (by simp [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)])
  exact ⟨⟨P, hP₁⟩, PrimeSpectrum.ext_iff.mp

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, FaithfullyFlat, Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain, Module, Module.FaithfullyFlat.of_comap_surjective, PrimeSpectrum, PrimeSpectrum.ext_iff.mpr, RingHom, RingHom.injective_iff_ker_eq_bot, algebraMap_injective, exists_ideal_over_prime_of_isIntegral_of_isDomain, ext_iff, injective_iff_ker_eq_bot, of_comap_surjective
-/
instance Module.FaithfullyFlat.of_isIntegral_of_isDomain [IsDomain B] [Module.Flat A B]
    [Algebra.IsIntegral A B] [FaithfulSMul A B] :
    Module.FaithfullyFlat A B := by
  refine Module.FaithfullyFlat.of_comap_surjective fun P => ?_
  obtain ⟨P, hP₁, hP₂⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain P.1 (S := B)
    (by simp [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)])
  exact ⟨⟨P, hP₁⟩, PrimeSpectrum.ext_iff.mpr hP₂⟩

variable [Module.FaithfullyFlat A B]

/--
lemma `Module.FaithfullyFlat.tensorProduct_mk_injective` / 引理 `Module.FaithfullyFlat.tensorProduct_mk_injective`

English:
lemma Module.FaithfullyFlat.tensorProduct_mk_injective
  given: (M : Type*) [AddCommGroup M] [Module A M]
  proof: by
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective A B]
  have : (lTensor B <| TensorProduct.mk A B M 1) =
      (TensorProduct.leftComm A B B M).symm.comp (TensorProduct.mk A B (B otimes[A] M) 1) := by
    apply TensorProduct.ext'
    intro x y
    simp
  rw [this]; rw [coe_comp]; rw 

中文:
引理 Module.FaithfullyFlat.tensorProduct_mk_injective
  条件: (M : 类型) [AddCommGroup M] [Module A M]
  证明: by
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective A B]
  have : (lTensor B <| TensorProduct.mk A B M 1) =
      (TensorProduct.leftComm A B B M).symm.comp (TensorProduct.mk A B (B otimes[A] M) 1) := by
    apply TensorProduct.ext'
    intro x y
    simp
  rw [this]; rw [coe_comp]; rw 

Depends on / 依赖: Algebra, Algebra.TensorProduct.mk_one_injective_of_isScalarTower, EmbeddingLike, EmbeddingLike.comp_injective, FaithfullyFlat, LinearEquiv, LinearEquiv.coe_coe, Module, Module.FaithfullyFlat.lTensor_injective_iff_injective, TensorProduct, TensorProduct.ext, TensorProduct.leftComm, TensorProduct.mk, coe_coe, coe_comp, comp_injective, lTensor, lTensor_injective_iff_injective, leftComm, mk_one_injective_of_isScalarTower
-/
lemma Module.FaithfullyFlat.tensorProduct_mk_injective (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Injective (TensorProduct.mk A B M 1) := by
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective A B]
  have : (lTensor B <| TensorProduct.mk A B M 1) =
      (TensorProduct.leftComm A B B M).symm.comp (TensorProduct.mk A B (B otimes[A] M) 1) := by
    apply TensorProduct.ext'
    intro x y
    simp
  rw [this]; rw [coe_comp]; rw [LinearEquiv.coe_coe]; rw [EmbeddingLike.comp_injective]
  exact Algebra.TensorProduct.mk_one_injective_of_isScalarTower _

/--
Instance `Module.FaithfullyFlat.faithfulSMul` / 实例 `Module.FaithfullyFlat.faithfulSMul`

English:
instance Module.FaithfullyFlat.faithfulSMul
  signature: : FaithfulSMul A B
  body: by
  constructor
  intro a₁ a₂ ha
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) A
  simp only [TensorProduct.mk_apply]
  rw [← mul_one a₁]; rw [← mul_one a₂]
  simp only [← smul_eq_mul, ← TensorProduct.smul_tmul, ha (1 : B)]

中文:
实例 Module.FaithfullyFlat.faithfulSMul
  签名: : FaithfulSMul A B
  定义体: by
  constructor
  intro a₁ a₂ ha
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) A
  simp only [TensorProduct.mk_apply]
  rw [← mul_one a₁]; rw [← mul_one a₂]
  simp only [← smul_eq_mul, ← TensorProduct.smul_tmul, ha (1 : B)]

Depends on / 依赖: FaithfullyFlat, Module, Module.FaithfullyFlat.tensorProduct_mk_injective, TensorProduct, TensorProduct.mk_apply, TensorProduct.smul_tmul, mk_apply, mul_one, smul_eq_mul, smul_tmul, tensorProduct_mk_injective
-/
instance Module.FaithfullyFlat.faithfulSMul : FaithfulSMul A B := by
  constructor
  intro a₁ a₂ ha
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) A
  simp only [TensorProduct.mk_apply]
  rw [← mul_one a₁]; rw [← mul_one a₂]
  simp only [← smul_eq_mul, ← TensorProduct.smul_tmul, ha (1 : B)]

open Algebra.TensorProduct in
/--
lemma `Ideal.comap_map_eq_self_of_faithfullyFlat` / 引理 `Ideal.comap_map_eq_self_of_faithfullyFlat`

English:
lemma Ideal.comap_map_eq_self_of_faithfullyFlat
  given: (I : Ideal A)
  proof: by
  refine le_antisymm ?_ le_comap_map
  have inj : Function.Injective
      ((quotIdealMapEquivTensorQuot B I).symm.toLinearMap.restrictScalars _ ∘ₗ
        TensorProduct.mk A B (A ⧸ I) 1) := by
    rw [LinearMap.coe_comp]; rw [AlgEquiv.toLinearMap]; rw [← LinearEquiv.restrictScalars_toLinearMap]


中文:
引理 Ideal.comap_map_eq_self_of_faithfullyFlat
  条件: (I : Ideal A)
  证明: by
  refine le_antisymm ?_ le_comap_map
  have inj : Function.Injective
      ((quotIdealMapEquivTensorQuot B I).symm.toLinearMap.restrictScalars _ ∘ₗ
        TensorProduct.mk A B (A ⧸ I) 1) := by
    rw [LinearMap.coe_comp]; rw [AlgEquiv.toLinearMap]; rw [← LinearEquiv.restrictScalars_toLinearMap]


Depends on / 依赖: AlgEquiv, AlgEquiv.toLinearMap, FaithfullyFlat, Function, Function.Injective, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap, Injective, LinearEquiv, LinearEquiv.injective, LinearEquiv.restrictScalars_toLinearMap, LinearMap, LinearMap.coe_comp, Module, Module.FaithfullyFlat.tensorProduct_mk_injective, Quotient, TensorProduct, TensorProduct.mk, coe_comp, eq_zero_iff_mem
-/
lemma Ideal.comap_map_eq_self_of_faithfullyFlat (I : Ideal A) :
    (I.map (algebraMap A B)).comap (algebraMap A B) = I := by
  refine le_antisymm ?_ le_comap_map
  have inj : Function.Injective
      ((quotIdealMapEquivTensorQuot B I).symm.toLinearMap.restrictScalars _ ∘ₗ
        TensorProduct.mk A B (A ⧸ I) 1) := by
    rw [LinearMap.coe_comp]; rw [AlgEquiv.toLinearMap]; rw [← LinearEquiv.restrictScalars_toLinearMap]
exact (LinearEquiv.injective _).comp
      Module.FaithfullyFlat.tensorProduct_mk_injective (A ⧸ I)
  intro x hx
  rw [Ideal.mem_comap] at hx
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  apply inj
  have : ((quotIdealMapEquivTensorQuot B I).symm.toLinearEquiv.toLinearMap.restrictScalars _ ∘ₗ
      TensorProduct.mk A B (A ⧸ I) 1) x = 0 := by
    simp [← Algebra.algebraMap_eq_smul_one, hx]
  simp [this]

/--
lemma `Ideal.comap_surjective_of_faithfullyFlat` / 引理 `Ideal.comap_surjective_of_faithfullyFlat`

English:
lemma Ideal.comap_surjective_of_faithfullyFlat
  proof: fun I => ⟨I.map (algebraMap A B), comap_map_eq_self_of_faithfullyFlat I⟩

中文:
引理 Ideal.comap_surjective_of_faithfullyFlat
  证明: fun I => ⟨I.map (algebraMap A B), comap_map_eq_self_of_faithfullyFlat I⟩

Depends on / 依赖: I.map, algebraMap, comap_map_eq_self_of_faithfullyFlat
-/
lemma Ideal.comap_surjective_of_faithfullyFlat :
    Function.Surjective (Ideal.comap (algebraMap A B)) :=
  fun I => ⟨I.map (algebraMap A B), comap_map_eq_self_of_faithfullyFlat I⟩

/--
lemma `Ideal.map_injective_of_faithfullyFlat` / 引理 `Ideal.map_injective_of_faithfullyFlat`

English:
lemma Ideal.map_injective_of_faithfullyFlat
  proof: fun _ _ h => by simpa [comap_map_eq_self_of_faithfullyFlat]
    using congr_arg (Ideal.comap (algebraMap A B) ·) h

中文:
引理 Ideal.map_injective_of_faithfullyFlat
  证明: fun _ _ h => by simpa [comap_map_eq_self_of_faithfullyFlat]
    using congr_arg (Ideal.comap (algebraMap A B) ·) h

Depends on / 依赖: Ideal.comap, algebraMap, comap_map_eq_self_of_faithfullyFlat, congr_arg
-/
lemma Ideal.map_injective_of_faithfullyFlat :
    Function.Injective (map (algebraMap A B)) :=
  fun _ _ h => by simpa [comap_map_eq_self_of_faithfullyFlat]
    using congr_arg (Ideal.comap (algebraMap A B) ·) h

/--
lemma `Ideal.exists_isPrime_liesOver_of_faithfullyFlat` / 引理 `Ideal.exists_isPrime_liesOver_of_faithfullyFlat`

English:
lemma Ideal.exists_isPrime_liesOver_of_faithfullyFlat
  given: (p : Ideal A) [p.IsPrime]
  proof: by
obtain ⟨P, _, hP⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime p).mp
    p.comap_map_eq_self_of_faithfullyFlat (B := B)
  exact ⟨P, inferInstance, ⟨hP.symm⟩⟩

中文:
引理 Ideal.exists_isPrime_liesOver_of_faithfullyFlat
  条件: (p : Ideal A) [p.IsPrime]
  证明: by
obtain ⟨P, _, hP⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime p).mp
    p.comap_map_eq_self_of_faithfullyFlat (B := B)
  exact ⟨P, inferInstance, ⟨hP.symm⟩⟩

Depends on / 依赖: Ideal.comap_map_eq_self_iff_of_isPrime, comap_map_eq_self_iff_of_isPrime, comap_map_eq_self_of_faithfullyFlat, hP.symm, p.comap_map_eq_self_of_faithfullyFlat
-/
lemma Ideal.exists_isPrime_liesOver_of_faithfullyFlat (p : Ideal A) [p.IsPrime] :
    exists (P : Ideal B), P.IsPrime ∧ P.LiesOver p := by
obtain ⟨P, _, hP⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime p).mp
    p.comap_map_eq_self_of_faithfullyFlat (B := B)
  exact ⟨P, inferInstance, ⟨hP.symm⟩⟩

/--
lemma `PrimeSpectrum.comap_surjective_of_faithfullyFlat` / 引理 `PrimeSpectrum.comap_surjective_of_faithfullyFlat`

English:
lemma PrimeSpectrum.comap_surjective_of_faithfullyFlat
  proof: fun I =>
  (PrimeSpectrum.mem_range_comap_iff (algebraMap A B)).mpr
    I.asIdeal.comap_map_eq_self_of_faithfullyFlat

中文:
引理 PrimeSpectrum.comap_surjective_of_faithfullyFlat
  证明: fun I =>
  (PrimeSpectrum.mem_range_comap_iff (algebraMap A B)).mpr
    I.asIdeal.comap_map_eq_self_of_faithfullyFlat
-/
lemma PrimeSpectrum.comap_surjective_of_faithfullyFlat :
    Function.Surjective (comap (algebraMap A B)) := fun I =>
  (PrimeSpectrum.mem_range_comap_iff (algebraMap A B)).mpr
    I.asIdeal.comap_map_eq_self_of_faithfullyFlat

section IsLocalRing

variable (A B)

/--
Instance `Module.FaithfullyFlat.isLocalHom` / 实例 `Module.FaithfullyFlat.isLocalHom`

English:
instance Module.FaithfullyFlat.isLocalHom
  signature: : IsLocalHom (algebraMap A B)
  body: IsLocalHom.of_comap_surjective (algebraMap A B) PrimeSpectrum.comap_surjective_of_faithfullyFlat

中文:
实例 Module.FaithfullyFlat.isLocalHom
  签名: : IsLocalHom (algebraMap A B)
  定义体: IsLocalHom.of_comap_surjective (algebraMap A B) PrimeSpectrum.comap_surjective_of_faithfullyFlat

Depends on / 依赖: IsLocalHom, IsLocalHom.of_comap_surjective, PrimeSpectrum, PrimeSpectrum.comap_surjective_of_faithfullyFlat, algebraMap, comap_surjective_of_faithfullyFlat, of_comap_surjective
-/
instance Module.FaithfullyFlat.isLocalHom : IsLocalHom (algebraMap A B) :=
  IsLocalHom.of_comap_surjective (algebraMap A B) PrimeSpectrum.comap_surjective_of_faithfullyFlat

/--
theorem `Module.FaithfullyFlat.isLocalRing` / 定理 `Module.FaithfullyFlat.isLocalRing`

English:
theorem Module.FaithfullyFlat.isLocalRing
  given: [IsLocalRing B]
  statement: IsLocalRing A
  proof: (algebraMap A B).domain_isLocalRing

中文:
定理 Module.FaithfullyFlat.isLocalRing
  条件: [IsLocalRing B]
  结论: IsLocalRing A
  证明: (algebraMap A B).domain_isLocalRing

Depends on / 依赖: algebraMap, domain_isLocalRing
-/
theorem Module.FaithfullyFlat.isLocalRing [IsLocalRing B] : IsLocalRing A :=
  (algebraMap A B).domain_isLocalRing

end IsLocalRing
