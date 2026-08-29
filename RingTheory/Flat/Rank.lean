/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.RingHom.Flat

/-!

# Results for the rank of a finite flat algebra

In this file we study a finite, flat `R`-algebra `S` and relate injectivity and
bijectivity of `R → S` with the rank of `S` over `R`.

## Main results

- `PrimeSpectrum.comap_surjective_iff_injective_of_finite`: `Spec S → Spec R` is surjective
  if and only if `R → S` is injective.
- `Module.Flat.tfae_algebraMap_surjective`: `R → S` is surjective iff `S ⊗[R] S → S` is an
  isomorphism iff the rank of `S` is at most `1` at all primes.
- `Module.algebraMap_bijective_iff_rankAtStalk`: `S` is of constant `R`-rank `1` if and only if
  `S` is isomorphic to `R`.

-/

public section

universe u

open TensorProduct

attribute [local instance] Module.free_of_flat_of_isLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

section

variable [Module.Flat R S] [Module.Finite R S]

/--
lemma `PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap` / 引理 `PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap`

English:
lemma PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap
  given: (p : PrimeSpectrum R)
  proof: by
  rw [Module.rankAtStalk_eq]; rw [Module.finrank_pos_iff]; rw [p.nontrivial_iff_mem_rangeComap]

中文:
引理 PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap
  条件: (p : PrimeSpectrum R)
  证明: by
  rw [Module.rankAtStalk_eq]; rw [Module.finrank_pos_iff]; rw [p.nontrivial_iff_mem_rangeComap]

Depends on / 依赖: Module, Module.finrank_pos_iff, Module.rankAtStalk_eq, PrimeSpectrum, PrimeSpectrum.comap, Set.range, algebraMap, finrank_pos_iff, nontrivial_iff_mem_rangeComap, p.nontrivial_iff_mem_rangeComap, rankAtStalk_eq
-/
lemma PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap (p : PrimeSpectrum R) :
    0 < Module.rankAtStalk (R := R) S p ↔ p in Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
  rw [Module.rankAtStalk_eq]; rw [Module.finrank_pos_iff]; rw [p.nontrivial_iff_mem_rangeComap]

/--
lemma `PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective` / 引理 `PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective`

English:
lemma PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective
  proof: by
  simp_rw [rankAtStalk_pos_iff_mem_range_comap, ← Set.range_eq_univ,
    Set.eq_univ_iff_forall]

中文:
引理 PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective
  证明: by
  simp_rw [rankAtStalk_pos_iff_mem_range_comap, ← Set.range_eq_univ,
    Set.eq_univ_iff_forall]
-/
lemma PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective :
    (forall p, 0 < Module.rankAtStalk (R := R) S p) ↔
      Function.Surjective (PrimeSpectrum.comap <| algebraMap R S) := by
  simp_rw [rankAtStalk_pos_iff_mem_range_comap, ← Set.range_eq_univ,
    Set.eq_univ_iff_forall]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
lemma `PrimeSpectrum.comap_surjective_iff_injective_of_finite` / 引理 `PrimeSpectrum.comap_surjective_iff_injective_of_finite`

English:
lemma PrimeSpectrum.comap_surjective_iff_injective_of_finite
  proof: by
  refine ⟨fun h => ?_, fun h =>
    have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr h
    Algebra.IsIntegral.comap_surjective _ _⟩
  apply injective_of_isLocalization_isMaximal (fun P _ => Localization.AtPrime P)
    (fun P _ => Localization.AtPrime P otimes[R] S)
  int

中文:
引理 PrimeSpectrum.comap_surjective_iff_injective_of_finite
  证明: by
  refine ⟨fun h => ?_, fun h =>
    have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr h
    Algebra.IsIntegral.comap_surjective _ _⟩
  apply injective_of_isLocalization_isMaximal (fun P _ => Localization.AtPrime P)
    (fun P _ => Localization.AtPrime P otimes[R] S)
  int

Depends on / 依赖: Algebra, Algebra.IsIntegral.comap_surjective, AtPrime, FaithfulSMul, IsIntegral, LiesOver, Localization, Localization.AtPrime, Localization.AtPrime.algebraOfLiesOver, Nontrivial, Q.LiesOver, algebraOfLiesOver, asIdeal, comap_surjective, faithfulSMul_iff_algebraMap_injective, injective_of_isLocalization_isMaximal, otimes
-/
lemma PrimeSpectrum.comap_surjective_iff_injective_of_finite :
    (PrimeSpectrum.comap (algebraMap R S)).Surjective ↔ Function.Injective (algebraMap R S) := by
  refine ⟨fun h => ?_, fun h =>
    have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr h
    Algebra.IsIntegral.comap_surjective _ _⟩
  apply injective_of_isLocalization_isMaximal (fun P _ => Localization.AtPrime P)
    (fun P _ => Localization.AtPrime P otimes[R] S)
  intro p _
  rw [← faithfulSMul_iff_algebraMap_injective]
  obtain ⟨⟨Q, _⟩, hQ⟩ := h ⟨p, inferInstance⟩
  have : Q.LiesOver p := ⟨congr($(hQ).asIdeal).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : Nontrivial (Localization.AtPrime p otimes[R] S) := by
    let f : Localization.AtPrime p otimes[R] S ->ₐ[R] Localization.AtPrime Q :=
      Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R _ _)
        (IsScalarTower.toAlgHom R S _) (fun _ _ => Commute.all _ _)
    exact f.domain_nontrivial
  infer_instance

/--
lemma `Module.rankAtStalk_pos_iff_algebraMap_injective` / 引理 `Module.rankAtStalk_pos_iff_algebraMap_injective`

English:
lemma Module.rankAtStalk_pos_iff_algebraMap_injective
  proof: by
  rw [← PrimeSpectrum.comap_surjective_iff_injective_of_finite]; rw [PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective]

中文:
引理 Module.rankAtStalk_pos_iff_algebraMap_injective
  证明: by
  rw [← PrimeSpectrum.comap_surjective_iff_injective_of_finite]; rw [PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective]

Depends on / 依赖: Function, Function.Injective, Injective, PrimeSpectrum, PrimeSpectrum.comap_surjective_iff_injective_of_finite, PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective, algebraMap, comap_surjective_iff_injective_of_finite, contextual, rankAtStalk_pos_iff_comap_surjective, zero_zpow
-/
lemma Module.rankAtStalk_pos_iff_algebraMap_injective :
    (forall p, 0 < Module.rankAtStalk (R := R) S p) ↔ Function.Injective (algebraMap R S) := by
  rw [← PrimeSpectrum.comap_surjective_iff_injective_of_finite]; rw [PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
lemma `Module.algebraMap_surjective_of_rankAtStalk_le_one` / 引理 `Module.algebraMap_surjective_of_rankAtStalk_le_one`

English:
lemma Module.algebraMap_surjective_of_rankAtStalk_le_one
  given: (h : forall p, rankAtStalk (R := R) S p <= 1)
  proof: by
  apply surjective_of_isLocalization_isMaximal (fun P _ => Localization.AtPrime P)
    (fun P _ => Localization.AtPrime P otimes[R] S)
  intro p _
  by_cases hr : Module.rankAtStalk S ⟨p, inferInstance⟩ = 0
  · have : Subsingleton (Localization.AtPrime p otimes[R] S) := by
      apply Module.subs

中文:
引理 Module.algebraMap_surjective_of_rankAtStalk_le_one
  条件: (h : 对任意 p, rankAtStalk (R := R) S p <= 1)
  证明: by
  apply surjective_of_isLocalization_isMaximal (fun P _ => Localization.AtPrime P)
    (fun P _ => Localization.AtPrime P otimes[R] S)
  intro p _
  by_cases hr : Module.rankAtStalk S ⟨p, inferInstance⟩ = 0
  · have : Subsingleton (Localization.AtPrime p otimes[R] S) := by
      apply Module.subs
-/
lemma Module.algebraMap_surjective_of_rankAtStalk_le_one (h : forall p, rankAtStalk (R := R) S p <= 1) :
    Function.Surjective (algebraMap R S) := by
  apply surjective_of_isLocalization_isMaximal (fun P _ => Localization.AtPrime P)
    (fun P _ => Localization.AtPrime P otimes[R] S)
  intro p _
  by_cases hr : Module.rankAtStalk S ⟨p, inferInstance⟩ = 0
  · have : Subsingleton (Localization.AtPrime p otimes[R] S) := by
      apply Module.subsingleton_of_rank_zero (R := Localization.AtPrime p)
      simp [← finrank_eq_rank, ← rankAtStalk_eq_finrank_tensorProduct ⟨p, inferInstance⟩, hr]
    exact Function.surjective_to_subsingleton _
  · refine (Free.bijective_algebraMap_of_finrank_eq_one ?_).2
    grind [rankAtStalk_eq_finrank_tensorProduct ⟨p, inferInstance⟩]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
variable (R) (S) in
/--
lemma `Module.Flat.tfae_algebraMap_surjective` / 引理 `Module.Flat.tfae_algebraMap_surjective`

English:
lemma Module.Flat.tfae_algebraMap_surjective
  proof: by
  tfae_have 1 -> 2 := LinearMap.mul'_bijective_of_surjective _ _
  tfae_have 2 -> 3 := fun H p => by
    have h : rankAtStalk (S otimes[R] S) p = rankAtStalk S p ^ 2 := by
      simp [rankAtStalk_tensorProduct, sq]
    by_contra! hc
    apply Nat.succ_succ_ne_one 0
    rw [← Nat.pow_eq_self_iff h

中文:
引理 Module.Flat.tfae_algebraMap_surjective
  证明: by
  tfae_have 1 -> 2 := LinearMap.mul'_bijective_of_surjective _ _
  tfae_have 2 -> 3 := fun H p => by
    have h : rankAtStalk (S otimes[R] S) p = rankAtStalk S p ^ 2 := by
      simp [rankAtStalk_tensorProduct, sq]
    by_contra! hc
    apply Nat.succ_succ_ne_one 0
    rw [← Nat.pow_eq_self_iff h

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, Algebra, Algebra.TensorProduct.lmul, LinearMap, LinearMap.mul, Module, Module.algebraMap_surjective_of_rankAtStalk_le_one, Module.rankAtStalk_eq_of_equiv, Nat.pow_eq_self_iff, Nat.succ_succ_ne_one, TensorProduct, _bijective_of_surjective, algebraMap_surjective_of_rankAtStalk_le_one, ofBijective, otimes, pow_eq_self_iff, rankAtStalk, rankAtStalk_eq_of_equiv, rankAtStalk_tensorProduct
-/
lemma Module.Flat.tfae_algebraMap_surjective :
    [Function.Surjective (algebraMap R S),
      Function.Bijective (LinearMap.mul' R S),
      (forall p, Module.rankAtStalk (R := R) S p <= 1)].TFAE := by
  tfae_have 1 -> 2 := LinearMap.mul'_bijective_of_surjective _ _
  tfae_have 2 -> 3 := fun H p => by
    have h : rankAtStalk (S otimes[R] S) p = rankAtStalk S p ^ 2 := by
      simp [rankAtStalk_tensorProduct, sq]
    by_contra! hc
    apply Nat.succ_succ_ne_one 0
    rw [← Nat.pow_eq_self_iff hc]; rw [← h]; rw [Module.rankAtStalk_eq_of_equiv
      (AlgEquiv.ofBijective (Algebra.TensorProduct.lmul' R (S := S)) H).toLinearEquiv]
  tfae_have 3 -> 1 := Module.algebraMap_surjective_of_rankAtStalk_le_one
  tfae_finish

/--
lemma `Module.rankAtStalk_le_one_iff_surjective` / 引理 `Module.rankAtStalk_le_one_iff_surjective`

English:
lemma Module.rankAtStalk_le_one_iff_surjective
  proof: (Module.Flat.tfae_algebraMap_surjective R S).out 2 0

中文:
引理 Module.rankAtStalk_le_one_iff_surjective
  证明: (Module.Flat.tfae_algebraMap_surjective R S).out 2 0

Depends on / 依赖: Function, Function.Surjective, Surjective, algebraMap
-/
lemma Module.rankAtStalk_le_one_iff_surjective :
    (forall p, Module.rankAtStalk (R := R) S p <= 1) ↔ Function.Surjective (algebraMap R S) :=
  (Module.Flat.tfae_algebraMap_surjective R S).out 2 0

/--
lemma `Module.algebraMap_bijective_iff_rankAtStalk` / 引理 `Module.algebraMap_bijective_iff_rankAtStalk`

English:
lemma Module.algebraMap_bijective_iff_rankAtStalk
  proof: by
  rw [Function.Bijective]; rw [← rankAtStalk_pos_iff_algebraMap_injective]; rw [← rankAtStalk_le_one_iff_surjective]
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  ext p
  rw [Pi.one_apply]
  grind

alias ⟨Module.algebraMap_bijective_of_rankAtStalk, _⟩ := Module.algebraMap_bijective_iff_rankAtSta

中文:
引理 Module.algebraMap_bijective_iff_rankAtStalk
  证明: by
  rw [Function.Bijective]; rw [← rankAtStalk_pos_iff_algebraMap_injective]; rw [← rankAtStalk_le_one_iff_surjective]
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  ext p
  rw [Pi.one_apply]
  grind

alias ⟨Module.algebraMap_bijective_of_rankAtStalk, _⟩ := Module.algebraMap_bijective_iff_rankAtSta

Depends on / 依赖: Bijective, Function, Function.Bijective, Pi.one_apply, algebraMap, eq_or_ne, one_apply, rankAtStalk_le_one_iff_surjective, rankAtStalk_pos_iff_algebraMap_injective, zpow_eq_zero_iff
-/
lemma Module.algebraMap_bijective_iff_rankAtStalk :
    Module.rankAtStalk (R := R) S = 1 ↔ Function.Bijective (algebraMap R S) := by
  rw [Function.Bijective]; rw [← rankAtStalk_pos_iff_algebraMap_injective]; rw [← rankAtStalk_le_one_iff_surjective]
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  ext p
  rw [Pi.one_apply]
  grind

alias ⟨Module.algebraMap_bijective_of_rankAtStalk, _⟩ := Module.algebraMap_bijective_iff_rankAtStalk

end

section

/-- The rank of a ring homomorphism `f : R →+* S` at a prime `x` of `R` is the rank of
`S` as an `R`-module at the stalk of `x`. -/
@[expose]
/--
Definition of `RingHom.finrank` / `RingHom.finrank` 的定义

English:
definition RingHom.finrank
  signature: {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S)
  body: letI : Algebra R S := f.toAlgebra
  Module.rankAtStalk S x

@[simp]

中文:
定义 RingHom.finrank
  签名: {R S : 类型} [CommRing R] [CommRing S] (f : R ->+* S)
  定义体: letI : Algebra R S := f.toAlgebra
  Module.rankAtStalk S x

@[simp]

Depends on / 依赖: Algebra, Module, Module.rankAtStalk, f.toAlgebra, rankAtStalk, toAlgebra
-/
noncomputable def RingHom.finrank {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S)
    (x : PrimeSpectrum R) : Nat :=
  letI : Algebra R S := f.toAlgebra
  Module.rankAtStalk S x

@[simp]
/--
lemma `RingHom.finrank_algebraMap` / 引理 `RingHom.finrank_algebraMap`

English:
lemma RingHom.finrank_algebraMap
  proof: by
  ext
  rw [RingHom.finrank]; rw [toAlgebra_algebraMap]

中文:
引理 RingHom.finrank_algebraMap
  证明: by
  ext
  rw [RingHom.finrank]; rw [toAlgebra_algebraMap]

Depends on / 依赖: RingHom, RingHom.finrank, finrank, toAlgebra_algebraMap
-/
lemma RingHom.finrank_algebraMap :
    (algebraMap R S).finrank = Module.rankAtStalk (R := R) S := by
  ext
  rw [RingHom.finrank]; rw [toAlgebra_algebraMap]

/--
lemma `Algebra.rankAtStalk_eq_of_isPushout` / 引理 `Algebra.rankAtStalk_eq_of_isPushout`

English:
lemma Algebra.rankAtStalk_eq_of_isPushout
  statement: (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  proof: by
  have : IsPushout R R' S S' := Algebra.IsPushout.symm inferInstance
  have := Module.rankAtStalk_eq_of_equiv (Algebra.IsPushout.equiv R R' S S').symm.toLinearEquiv
  rw [Module.rankAtStalk_eq_of_equiv (Algebra.IsPushout.equiv R R' S S').symm.toLinearEquiv]; rw [Module.rankAtStalk_baseChange]

中文:
引理 Algebra.rankAtStalk_eq_of_isPushout
  结论: (R S : 类型) [CommRing R] [CommRing S] [Algebra R S]
  证明: by
  have : IsPushout R R' S S' := Algebra.IsPushout.symm inferInstance
  have := Module.rankAtStalk_eq_of_equiv (Algebra.IsPushout.equiv R R' S S').symm.toLinearEquiv
  rw [Module.rankAtStalk_eq_of_equiv (Algebra.IsPushout.equiv R R' S S').symm.toLinearEquiv]; rw [Module.rankAtStalk_baseChange]

Depends on / 依赖: Algebra, Algebra.IsPushout.equiv, Algebra.IsPushout.symm, IsPushout, Module, Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv, rankAtStalk_baseChange, rankAtStalk_eq_of_equiv, symm.toLinearEquiv, toLinearEquiv
-/
lemma Algebra.rankAtStalk_eq_of_isPushout (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (R' S' : Type*) [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R S R' S'] [Module.Flat R S] [Module.Finite R S] (x : PrimeSpectrum R') :
    Module.rankAtStalk S' x = Module.rankAtStalk S (PrimeSpectrum.comap (algebraMap R R') x) := by
  have : IsPushout R R' S S' := Algebra.IsPushout.symm inferInstance
  have := Module.rankAtStalk_eq_of_equiv (Algebra.IsPushout.equiv R R' S S').symm.toLinearEquiv
  rw [Module.rankAtStalk_eq_of_equiv (Algebra.IsPushout.equiv R R' S S').symm.toLinearEquiv]; rw [Module.rankAtStalk_baseChange]

/--
lemma `RingHom.finrank_comp_left_of_bijective` / 引理 `RingHom.finrank_comp_left_of_bijective`

English:
lemma RingHom.finrank_comp_left_of_bijective
  statement: {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  proof: by
  algebraize [f, g, (g.comp f)]
  have : Algebra.IsPushout R S R T := .of_bijective_right _ _ hf
  apply Algebra.rankAtStalk_eq_of_isPushout

中文:
引理 RingHom.finrank_comp_left_of_bijective
  结论: {R S T : 类型} [CommRing R] [CommRing S] [CommRing T]
  证明: by
  algebraize [f, g, (g.comp f)]
  have : Algebra.IsPushout R S R T := .of_bijective_right _ _ hf
  apply Algebra.rankAtStalk_eq_of_isPushout

Depends on / 依赖: Algebra, Algebra.IsPushout, Algebra.rankAtStalk_eq_of_isPushout, IsPushout, algebraize, g.comp, of_bijective_right, rankAtStalk_eq_of_isPushout
-/
lemma RingHom.finrank_comp_left_of_bijective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R ->+* S) (g : S ->+* T) (hf : Function.Bijective g) (h1 : f.Finite) (h2 : f.Flat)
    (x : PrimeSpectrum R) : (g.comp f).finrank x = f.finrank x := by
  algebraize [f, g, (g.comp f)]
  have : Algebra.IsPushout R S R T := .of_bijective_right _ _ hf
  apply Algebra.rankAtStalk_eq_of_isPushout

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
lemma `RingHom.finrank_comp_right_of_bijective` / 引理 `RingHom.finrank_comp_right_of_bijective`

English:
lemma RingHom.finrank_comp_right_of_bijective
  statement: {R S T : Type*} [CommRing R] [CommRing S]
  proof: by
  subst hy
  algebraize [f, g, (g.comp f)]
have : Module.Finite R T := h1.comp .of_surjective _ hg.2
  have : Module.Flat R T := (RingHom.Flat.of_bijective hg).comp h2
  have : Algebra.IsPushout R T S T := .of_bijective_left _ _ hg
  exact (Algebra.rankAtStalk_eq_of_isPushout _ _ _ _ _).symm

中文:
引理 RingHom.finrank_comp_right_of_bijective
  结论: {R S T : 类型} [CommRing R] [CommRing S]
  证明: by
  subst hy
  algebraize [f, g, (g.comp f)]
have : Module.Finite R T := h1.comp .of_surjective _ hg.2
  have : Module.Flat R T := (RingHom.Flat.of_bijective hg).comp h2
  have : Algebra.IsPushout R T S T := .of_bijective_left _ _ hg
  exact (Algebra.rankAtStalk_eq_of_isPushout _ _ _ _ _).symm

Depends on / 依赖: Algebra, Algebra.IsPushout, Algebra.rankAtStalk_eq_of_isPushout, Finite, IsPushout, Module, Module.Finite, Module.Flat, RingHom, RingHom.Flat.of_bijective, algebraize, apply_ite, contextual, g.comp, h1.comp, of_bijective, of_bijective_left, of_surjective, rankAtStalk_eq_of_isPushout, split_ifs
-/
lemma RingHom.finrank_comp_right_of_bijective {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (f : R ->+* S) (g : S ->+* T) (hg : Function.Bijective f) (h1 : g.Finite)
    (h2 : g.Flat) (y : PrimeSpectrum R) (x : PrimeSpectrum S)
    (hy : y = PrimeSpectrum.comap f x) :
    (g.comp f).finrank y = g.finrank x := by
  subst hy
  algebraize [f, g, (g.comp f)]
have : Module.Finite R T := h1.comp .of_surjective _ hg.2
  have : Module.Flat R T := (RingHom.Flat.of_bijective hg).comp h2
  have : Algebra.IsPushout R T S T := .of_bijective_left _ _ hg
  exact (Algebra.rankAtStalk_eq_of_isPushout _ _ _ _ _).symm

/--
lemma `CommRingCat.finrank_eq_of_isPushout` / 引理 `CommRingCat.finrank_eq_of_isPushout`

English:
lemma CommRingCat.finrank_eq_of_isPushout
  statement: {R S T P : CommRingCat.{u}} {f : R ⟶ S} {g : R ⟶ T}
  proof: by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
have : IsScalarTower R T P := .of_algebraMap_eq' congr($(h.1.1).hom)
  have : Algebra.IsPushout R S T P := CommRingCat.isPushout_iff_isPushout.mp h
  exact Algebra.rankAtStalk_eq_of_isPushout R S T P x

中文:
引理 CommRingCat.finrank_eq_of_isPushout
  结论: {R S T P : CommRingCat.{u}} {f : R ⟶ S} {g : R ⟶ T}
  证明: by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
have : IsScalarTower R T P := .of_algebraMap_eq' congr($(h.1.1).hom)
  have : Algebra.IsPushout R S T P := CommRingCat.isPushout_iff_isPushout.mp h
  exact Algebra.rankAtStalk_eq_of_isPushout R S T P x

Depends on / 依赖: Algebra, Algebra.IsPushout, Algebra.rankAtStalk_eq_of_isPushout, CommRingCat, CommRingCat.isPushout_iff_isPushout.mp, IsPushout, IsScalarTower, algebraize, f.hom, g.hom, inl.hom, inl.hom.comp, inr.hom, isPushout_iff_isPushout, of_algebraMap_eq, rankAtStalk_eq_of_isPushout, zpow_mul, zpow_ne_zero
-/
lemma CommRingCat.finrank_eq_of_isPushout {R S T P : CommRingCat.{u}} {f : R ⟶ S} {g : R ⟶ T}
    {inl : S ⟶ P} {inr : T ⟶ P} (h : CategoryTheory.IsPushout f g inl inr) (hf : f.hom.Flat)
    (hfin : f.hom.Finite) (x : PrimeSpectrum T) :
    inr.hom.finrank x = f.hom.finrank (PrimeSpectrum.comap g.hom x) := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
have : IsScalarTower R T P := .of_algebraMap_eq' congr($(h.1.1).hom)
  have : Algebra.IsPushout R S T P := CommRingCat.isPushout_iff_isPushout.mp h
  exact Algebra.rankAtStalk_eq_of_isPushout R S T P x

end
