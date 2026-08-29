/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Primes in an extension of localization at prime

Let `R ⊆ S` be an extension of Dedekind domains and `p` be a prime ideal of `R`. Let `Rₚ` be the
localization of `R` at the complement of `p` and `Sₚ` the localization of `S` at the (image)
of the complement of `p`.

In this file, we study the relation between the (nonzero) prime ideals of `Sₚ` and the prime
ideals of `S` above `p`. In particular, we prove that (under suitable conditions) they are in
bijection and that the residual degree and ramification index are preserved by this bijection.

## Main definitions and results

- `IsLocalization.AtPrime.mem_primesOver_of_isPrime`: The nonzero prime ideals of `Sₚ` are
  primes over the maximal ideal of `Rₚ`.

- `IsLocalization.AtPrime.equivQuotientMapOfIsMaximal`: `S ⧸ P ≃+* Sₚ ⧸ P·Sₚ` where
  `P` is a maximal ideal of `S` above `p`.

- `IsDedekindDomain.primesOverEquivPrimesOver`: the bijection between the primes over
  `p` in `S` and the primes over the maximal ideal of `Rₚ` in `Sₚ`.

- `IsDedekindDomain.primesOverEquivPrimesOver_inertiagDeg_eq`: the bijection
  `primesOverEquivPrimesOver` preserves the inertia degree.

- `IsDedekindDomain.primesOverEquivPrimesOver_ramificationIdx_eq`: the bijection
  `primesOverEquivPrimesOver` preserves the ramification index.

-/

@[expose] public section

open Algebra Module IsLocalRing Ideal Localization.AtPrime

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
  (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
  (Sₚ : Type*) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
  [Algebra Rₚ Sₚ] (P : Ideal S) [hPp : P.LiesOver p]

namespace IsLocalization.AtPrime

/--
theorem `mem_primesOver_of_isPrime` / 定理 `mem_primesOver_of_isPrime`

English:
theorem mem_primesOver_of_isPrime
  given: {Q : Ideal Sₚ} [Q.IsMaximal] [Algebra.IsIntegral Rₚ Sₚ]
  proof: by
  refine ⟨inferInstance, ?_⟩
  rw [liesOver_iff]; rw [← eq_maximalIdeal]
  exact IsMaximal.under Rₚ Q

中文:
定理 mem_primesOver_of_isPrime
  条件: {Q : Ideal Sₚ} [Q.IsMaximal] [Algebra.Is整数egral Rₚ Sₚ]
  证明: by
  refine ⟨inferInstance, ?_⟩
  rw [liesOver_iff]; rw [← eq_maximalIdeal]
  exact IsMaximal.under Rₚ Q

Depends on / 依赖: IsMaximal, IsMaximal.under, eq_maximalIdeal, liesOver_iff
-/
theorem mem_primesOver_of_isPrime {Q : Ideal Sₚ} [Q.IsMaximal] [Algebra.IsIntegral Rₚ Sₚ] :
    Q in (maximalIdeal Rₚ).primesOver Sₚ := by
  refine ⟨inferInstance, ?_⟩
  rw [liesOver_iff]; rw [← eq_maximalIdeal]
  exact IsMaximal.under Rₚ Q

/--
theorem `liesOver_comap_of_liesOver` / 定理 `liesOver_comap_of_liesOver`

English:
theorem liesOver_comap_of_liesOver
  statement: {T : Type*} [CommRing T] [Algebra R T] [Algebra Rₚ T]
  proof: by
  have : Q.LiesOver p := by
    have : (maximalIdeal Rₚ).LiesOver p := liesOver_maximalIdeal Rₚ p _
    exact LiesOver.trans Q (IsLocalRing.maximalIdeal Rₚ) p
exact comap_liesOver Q p IsScalarTower.toAlgHom R S T

include p in

中文:
定理 liesOver_comap_of_liesOver
  结论: {T : 类型} [CommRing T] [Algebra R T] [Algebra Rₚ T]
  证明: by
  have : Q.LiesOver p := by
    have : (maximalIdeal Rₚ).LiesOver p := liesOver_maximalIdeal Rₚ p _
    exact LiesOver.trans Q (IsLocalRing.maximalIdeal Rₚ) p
exact comap_liesOver Q p IsScalarTower.toAlgHom R S T

include p in

Depends on / 依赖: IsLocalRing, IsLocalRing.maximalIdeal, IsScalarTower, IsScalarTower.toAlgHom, LiesOver, LiesOver.trans, Q.LiesOver, comap_liesOver, liesOver_maximalIdeal, maximalIdeal, toAlgHom
-/
theorem liesOver_comap_of_liesOver {T : Type*} [CommRing T] [Algebra R T] [Algebra Rₚ T]
    [Algebra S T] [IsScalarTower R S T] [IsScalarTower R Rₚ T] (Q : Ideal T)
    [Q.LiesOver (maximalIdeal Rₚ)] : (comap (algebraMap S T) Q).LiesOver p := by
  have : Q.LiesOver p := by
    have : (maximalIdeal Rₚ).LiesOver p := liesOver_maximalIdeal Rₚ p _
    exact LiesOver.trans Q (IsLocalRing.maximalIdeal Rₚ) p
exact comap_liesOver Q p IsScalarTower.toAlgHom R S T

include p in
/--
theorem `liesOver_map_of_liesOver` / 定理 `liesOver_map_of_liesOver`

English:
theorem liesOver_map_of_liesOver
  statement: [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
  proof: by
  rw [liesOver_iff]; rw [eq_comm]; rw [← map_eq_maximalIdeal p]; rw [over_def P p]
  exact under_map_eq_map_under _
    (over_def P p ▸ map_eq_maximalIdeal p Rₚ ▸ maximalIdeal.isMaximal Rₚ)
    (isPrime_map_of_liesOver S p Sₚ P).ne_top

中文:
定理 liesOver_map_of_liesOver
  结论: [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
  证明: by
  rw [liesOver_iff]; rw [eq_comm]; rw [← map_eq_maximalIdeal p]; rw [over_def P p]
  exact under_map_eq_map_under _
    (over_def P p ▸ map_eq_maximalIdeal p Rₚ ▸ maximalIdeal.isMaximal Rₚ)
    (isPrime_map_of_liesOver S p Sₚ P).ne_top

Depends on / 依赖: eq_comm, isMaximal, isPrime_map_of_liesOver, liesOver_iff, map_eq_maximalIdeal, maximalIdeal, maximalIdeal.isMaximal, ne_top, over_def, under_map_eq_map_under
-/
theorem liesOver_map_of_liesOver [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
    [P.IsPrime] :
    (P.map (algebraMap S Sₚ)).LiesOver (IsLocalRing.maximalIdeal Rₚ) := by
  rw [liesOver_iff]; rw [eq_comm]; rw [← map_eq_maximalIdeal p]; rw [over_def P p]
  exact under_map_eq_map_under _
    (over_def P p ▸ map_eq_maximalIdeal p Rₚ ▸ maximalIdeal.isMaximal Rₚ)
    (isPrime_map_of_liesOver S p Sₚ P).ne_top

attribute [local instance] Ideal.Quotient.field

include p in
/--
theorem `exists_algebraMap_quot_eq_of_mem_quot` / 定理 `exists_algebraMap_quot_eq_of_mem_quot`

English:
theorem exists_algebraMap_quot_eq_of_mem_quot
  statement: [P.IsMaximal]
  proof: by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (algebraMapSubmonoid S p.primeCompl) x
  obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := P) (Ideal.Quotient.mk P s)⁻¹
  simp only [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _), Quotient.alg

中文:
定理 exists_algebraMap_quot_eq_of_mem_quot
  结论: [P.IsMaximal]
  证明: by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (algebraMapSubmonoid S p.primeCompl) x
  obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := P) (Ideal.Quotient.mk P s)⁻¹
  simp only [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _), Quotient.alg

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, IsLocalization, IsLocalization.exists_mk, IsPrime, IsScalarTower, IsScalarTower.algebraMap_eq, P.map, Quotient, Quotient.algebraMap_eq, Quotient.eq_zero_iff_mem, RingHom, RingHom.comp_apply, algebraMap, algebraMapSubmonoid, algebraMap_eq, comp_apply, eq_zero_iff_mem, exists_mk, isPrime_map_of_liesOver
-/
theorem exists_algebraMap_quot_eq_of_mem_quot [P.IsMaximal]
    (x : Sₚ ⧸ P.map (algebraMap S Sₚ)) :
    exists a, (algebraMap S (Sₚ ⧸ P.map (algebraMap S Sₚ))) a = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (algebraMapSubmonoid S p.primeCompl) x
  obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := P) (Ideal.Quotient.mk P s)⁻¹
  simp only [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _), Quotient.algebraMap_eq, RingHom.comp_apply]
  use x * s'
  rw [← sub_eq_zero]; rw [← map_sub]; rw [Quotient.eq_zero_iff_mem]
  have h₀ : (P.map (algebraMap S Sₚ)).IsPrime := isPrime_map_of_liesOver S p Sₚ P
  have h₁ : s.1 ∉ P := (Set.disjoint_left.mp <| disjoint_primeCompl_of_liesOver P p) s.prop
  have h₂ : algebraMap S Sₚ s ∉ Ideal.map (algebraMap S Sₚ) P := by
    rwa [← mem_comap, comap_map_eq_self_of_isMaximal _ h₀.ne_top]
  refine (h₀.mem_or_mem ?_).resolve_left h₂
  rw [mul_sub]; rw [mul_mk'_eq_mk'_of_mul]; rw [mk'_mul_cancel_left]; rw [← map_mul]; rw [← map_sub]; rw [← mem_comap]; rw [comap_map_eq_self_of_isMaximal _ IsPrime.ne_top']; rw [← Ideal.Quotient.eq]; rw [map_mul]; rw [map_mul]; rw [hs]; rw [mul_comm]; rw [inv_mul_cancel_right₀ (Quotient.eq_zero_iff_mem.not.mpr h₁)]

/--
Definition of `equivQuotientMapOfIsMaximal` / `equivQuotientMapOfIsMaximal` 的定义

English:
definition equivQuotientMapOfIsMaximal
  signature: [P.IsMaximal]
  body: .trans
    (Ideal.quotEquivOfEq (by
      rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _)]; rw [← RingHom.comap_ker]; rw [Quotient.algebraMap_eq]; rw [mk_ker]; rw [comap_map_eq_self_of_isMaximal _ (isPrime_map_of_liesOver S p Sₚ P).ne_top]))
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S

中文:
定义 equivQuotientMapOfIsMaximal
  签名: [P.IsMaximal]
  定义体: .trans
    (Ideal.quotEquivOfEq (by
      rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _)]; rw [← RingHom.comap_ker]; rw [Quotient.algebraMap_eq]; rw [mk_ker]; rw [comap_map_eq_self_of_isMaximal _ (isPrime_map_of_liesOver S p Sₚ P).ne_top]))
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S

Depends on / 依赖: Ideal.quotEquivOfEq, IsScalarTower, IsScalarTower.algebraMap_eq, Quotient, Quotient.algebraMap_eq, RingHom, RingHom.comap_ker, RingHom.quotientKerEquivOfSurjective, algebraMap, algebraMap_eq, comap_ker, comap_map_eq_self_of_isMaximal, exists_algebraMap_quot_eq_of_mem_quot, isPrime_map_of_liesOver, mk_ker, ne_top, quotEquivOfEq, quotientKerEquivOfSurjective
-/
noncomputable def equivQuotientMapOfIsMaximal [P.IsMaximal] :
    S ⧸ P ≃+* Sₚ ⧸ P.map (algebraMap S Sₚ) :=
  .trans
    (Ideal.quotEquivOfEq (by
      rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _)]; rw [← RingHom.comap_ker]; rw [Quotient.algebraMap_eq]; rw [mk_ker]; rw [comap_map_eq_self_of_isMaximal _ (isPrime_map_of_liesOver S p Sₚ P).ne_top]))
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ _))
      fun x => exists_algebraMap_quot_eq_of_mem_quot p Sₚ P x)

@[simp]
/--
theorem `equivQuotientMapOfIsMaximal_apply_mk` / 定理 `equivQuotientMapOfIsMaximal_apply_mk`

English:
theorem equivQuotientMapOfIsMaximal_apply_mk
  given: [P.IsMaximal] (x : S)
  proof: rfl

@[simp]

中文:
定理 equivQuotientMapOfIsMaximal_apply_mk
  条件: [P.IsMaximal] (x : S)
  证明: rfl

@[simp]
-/
theorem equivQuotientMapOfIsMaximal_apply_mk [P.IsMaximal] (x : S) :
    equivQuotientMapOfIsMaximal p Sₚ P (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ (algebraMap S Sₚ x)) := rfl

@[simp]
/--
theorem `equivQuotientMapOfIsMaximal_symm_apply_mk` / 定理 `equivQuotientMapOfIsMaximal_symm_apply_mk`

English:
theorem equivQuotientMapOfIsMaximal_symm_apply_mk
  statement: [P.IsMaximal] (x : S)
  proof: by
  have : (Ideal.map (algebraMap S Sₚ) P).IsPrime := isPrime_map_of_liesOver S p Sₚ P
  have h₁ : Ideal.Quotient.mk P ↑s != 0 :=
Quotient.eq_zero_iff_mem.not.mpr
      (Set.disjoint_left.mp <| disjoint_primeCompl_of_liesOver P p) s.prop
  have h₂ : equivQuotientMapOfIsMaximal p Sₚ P (Ideal.Quotien

中文:
定理 equivQuotientMapOfIsMaximal_symm_apply_mk
  结论: [P.IsMaximal] (x : S)
  证明: by
  have : (Ideal.map (algebraMap S Sₚ) P).IsPrime := isPrime_map_of_liesOver S p Sₚ P
  have h₁ : Ideal.Quotient.mk P ↑s != 0 :=
Quotient.eq_zero_iff_mem.not.mpr
      (Set.disjoint_left.mp <| disjoint_primeCompl_of_liesOver P p) s.prop
  have h₂ : equivQuotientMapOfIsMaximal p Sₚ P (Ideal.Quotien

Depends on / 依赖: Ideal.Quotient.mk, Ideal.map, IsPrime, Quotient, Quotient.eq_zero_iff_mem.not.mpr, RingEquiv, RingEquiv.map_ne_zero_iff, RingEquiv.symm_apply_eq, Set.disjoint_left.mp, algebraMap, disjoint_left, disjoint_primeCompl_of_liesOver, eq_zero_iff_mem, equivQuotientMapOfIsMaximal, isPrime_map_of_liesOver, map_mul, map_ne_zero_iff, map_one, mul_assoc, mul_left_inj
-/
theorem equivQuotientMapOfIsMaximal_symm_apply_mk [P.IsMaximal] (x : S)
    (s : algebraMapSubmonoid S p.primeCompl) :
    (equivQuotientMapOfIsMaximal p Sₚ P).symm (Ideal.Quotient.mk _ (mk' _ x s)) =
      (Ideal.Quotient.mk _ x) * (Ideal.Quotient.mk _ s.val)⁻¹ := by
  have : (Ideal.map (algebraMap S Sₚ) P).IsPrime := isPrime_map_of_liesOver S p Sₚ P
  have h₁ : Ideal.Quotient.mk P ↑s != 0 :=
Quotient.eq_zero_iff_mem.not.mpr
      (Set.disjoint_left.mp <| disjoint_primeCompl_of_liesOver P p) s.prop
  have h₂ : equivQuotientMapOfIsMaximal p Sₚ P (Ideal.Quotient.mk P ↑s) != 0 := by
    rwa [RingEquiv.map_ne_zero_iff]
  rw [RingEquiv.symm_apply_eq]; rw [← mul_left_inj' h₂]; rw [map_mul]; rw [mul_assoc]; rw [← map_mul]; rw [inv_mul_cancel₀ h₁]; rw [map_one]; rw [mul_one]; rw [equivQuotientMapOfIsMaximal_apply_mk]; rw [← map_mul]; rw [mk'_spec]; rw [Quotient.mk_algebraMap]; rw [equivQuotientMapOfIsMaximal_apply_mk]; rw [Quotient.mk_algebraMap]

variable [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]

/--
theorem `algebraMap_equivQuotMaximalIdeal_symm_apply` / 定理 `algebraMap_equivQuotMaximalIdeal_symm_apply`

English:
theorem algebraMap_equivQuotMaximalIdeal_symm_apply
  statement: [p.IsMaximal] [P.IsMaximal]
  proof: by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := mk'_surjective p.primeCompl x
  simp [equivQuotMaximalIdeal_symm_apply_mk, map_mul, Quotient.algebraMap_mk_of_liesOver,
    IsLocalization.algebraMap_mk' S Rₚ Sₚ]

中文:
定理 algebraMap_equivQuotMaximalIdeal_symm_apply
  结论: [p.IsMaximal] [P.IsMaximal]
  证明: by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := mk'_surjective p.primeCompl x
  simp [equivQuotMaximalIdeal_symm_apply_mk, map_mul, Quotient.algebraMap_mk_of_liesOver,
    IsLocalization.algebraMap_mk' S Rₚ Sₚ]

Depends on / 依赖: Ideal.Quotient.mk_surjective, IsLocalization, IsLocalization.algebraMap_mk, Quotient, Quotient.algebraMap_mk_of_liesOver, _surjective, algebraMap_mk, algebraMap_mk_of_liesOver, equivQuotMaximalIdeal_symm_apply_mk, map_mul, mk_surjective, p.primeCompl, primeCompl
-/
theorem algebraMap_equivQuotMaximalIdeal_symm_apply [p.IsMaximal] [P.IsMaximal]
    [(P.map (algebraMap S Sₚ)).LiesOver (maximalIdeal Rₚ)] (x : Rₚ ⧸ maximalIdeal Rₚ) :
    algebraMap (R ⧸ p) (S ⧸ P) ((equivQuotMaximalIdeal p Rₚ).symm x) =
    (equivQuotientMapOfIsMaximal p Sₚ P).symm
      (algebraMap (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ P.map (algebraMap S Sₚ)) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := mk'_surjective p.primeCompl x
  simp [equivQuotMaximalIdeal_symm_apply_mk, map_mul, Quotient.algebraMap_mk_of_liesOver,
    IsLocalization.algebraMap_mk' S Rₚ Sₚ]

-- Lean thinks that the instance [p.IsPrime] is not necessary here, but it is needed
-- for the definition of `Rₚ`.
set_option linter.unusedSectionVars false in
@[simp]
/--
theorem `equivQuotientMapMaximalIdeal_apply_mk` / 定理 `equivQuotientMapMaximalIdeal_apply_mk`

English:
theorem equivQuotientMapMaximalIdeal_apply_mk
  given: [p.IsMaximal] (x : S)
  proof: rfl

中文:
定理 equivQuotientMapMaximalIdeal_apply_mk
  条件: [p.IsMaximal] (x : S)
  证明: rfl
-/
theorem equivQuotientMapMaximalIdeal_apply_mk [p.IsMaximal] (x : S) :
    equivQuotientMapMaximalIdeal S p Rₚ Sₚ (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ (algebraMap S Sₚ x)) := rfl

/--
theorem `inertiaDeg_map_eq_inertiaDeg` / 定理 `inertiaDeg_map_eq_inertiaDeg`

English:
theorem inertiaDeg_map_eq_inertiaDeg
  statement: [p.IsMaximal] [P.IsMaximal]
  proof: by
  rw [inertiaDeg'_algebraMap]; rw [inertiaDeg'_algebraMap]
  refine Algebra.finrank_eq_of_equiv_equiv (equivQuotMaximalIdeal p Rₚ).symm
    (equivQuotientMapOfIsMaximal p Sₚ P).symm ?_
  ext x
  exact algebraMap_equivQuotMaximalIdeal_symm_apply p Rₚ Sₚ P x

include p in

中文:
定理 inertiaDeg_map_eq_inertiaDeg
  结论: [p.IsMaximal] [P.IsMaximal]
  证明: by
  rw [inertiaDeg'_algebraMap]; rw [inertiaDeg'_algebraMap]
  refine Algebra.finrank_eq_of_equiv_equiv (equivQuotMaximalIdeal p Rₚ).symm
    (equivQuotientMapOfIsMaximal p Sₚ P).symm ?_
  ext x
  exact algebraMap_equivQuotMaximalIdeal_symm_apply p Rₚ Sₚ P x

include p in

Depends on / 依赖: Algebra, Algebra.finrank_eq_of_equiv_equiv, _algebraMap, algebraMap_equivQuotMaximalIdeal_symm_apply, equivQuotMaximalIdeal, equivQuotientMapOfIsMaximal, finrank_eq_of_equiv_equiv, inertiaDeg
-/
theorem inertiaDeg_map_eq_inertiaDeg [p.IsMaximal] [P.IsMaximal]
    [(Ideal.map (algebraMap S Sₚ) P).LiesOver (maximalIdeal Rₚ)] :
    (maximalIdeal Rₚ).inertiaDeg' (P.map (algebraMap S Sₚ)) = p.inertiaDeg' P := by
  rw [inertiaDeg'_algebraMap]; rw [inertiaDeg'_algebraMap]
  refine Algebra.finrank_eq_of_equiv_equiv (equivQuotMaximalIdeal p Rₚ).symm
    (equivQuotientMapOfIsMaximal p Sₚ P).symm ?_
  ext x
  exact algebraMap_equivQuotMaximalIdeal_symm_apply p Rₚ Sₚ P x

include p in
/--
theorem `ramificationIdx_map_eq_ramificationIdx` / 定理 `ramificationIdx_map_eq_ramificationIdx`

English:
theorem ramificationIdx_map_eq_ramificationIdx
  given: [P.IsPrime]
  proof: by
  have := liesOver_map_of_liesOver p Rₚ Sₚ P
  have := IsLocalization.liesOver_map_of_isPrime_disjoint (algebraMapSubmonoid S p.primeCompl) Sₚ
    (Set.disjoint_image_left.mpr (Set.disjoint_compl_left_iff_subset.mpr hPp.over.ge))
  have := isPrime_map_of_liesOver S p Sₚ P
  rw [ramificationIdx_eq

中文:
定理 ramificationIdx_map_eq_ramificationIdx
  条件: [P.IsPrime]
  证明: by
  have := liesOver_map_of_liesOver p Rₚ Sₚ P
  have := IsLocalization.liesOver_map_of_isPrime_disjoint (algebraMapSubmonoid S p.primeCompl) Sₚ
    (Set.disjoint_image_left.mpr (Set.disjoint_compl_left_iff_subset.mpr hPp.over.ge))
  have := isPrime_map_of_liesOver S p Sₚ P
  rw [ramificationIdx_eq

Depends on / 依赖: Algebra, AtPrime, IsLocalization, IsLocalization.liesOver_map_of_isPrime_disjoint, Localization, Localization.AtPrime, Localization.AtPrime.alg, P.map, Set.disjoint_compl_left_iff_subset.mpr, Set.disjoint_image_left.mpr, algebraMap, algebraMapSubmonoid, disjoint_compl_left_iff_subset, disjoint_image_left, hPp.over.ge, isPrime_map_of_liesOver, liesOver_map_of_isPrime_disjoint, liesOver_map_of_liesOver, maximalIdeal, p.primeCompl
-/
theorem ramificationIdx_map_eq_ramificationIdx [P.IsPrime] :
    (P.map (algebraMap S Sₚ)).ramificationIdx Rₚ = P.ramificationIdx R := by
  have := liesOver_map_of_liesOver p Rₚ Sₚ P
  have := IsLocalization.liesOver_map_of_isPrime_disjoint (algebraMapSubmonoid S p.primeCompl) Sₚ
    (Set.disjoint_image_left.mpr (Set.disjoint_compl_left_iff_subset.mpr hPp.over.ge))
  have := isPrime_map_of_liesOver S p Sₚ P
  rw [ramificationIdx_eq (maximalIdeal Rₚ) (P.map (algebraMap S Sₚ))]; rw [ramificationIdx_eq p P]
  let R₁ := Localization.AtPrime (P.map (algebraMap S Sₚ))
  let R₂ := Localization.AtPrime P
  let : Algebra R₂ R₁ := Localization.AtPrime.algebraOfLiesOver P (P.map (algebraMap S Sₚ))
  have : IsLocalization.AtPrime R₁ P := by
    convert isLocalization_isLocalization_atPrime_isLocalization
      (algebraMapSubmonoid S p.primeCompl) R₁ (P.map (algebraMap S Sₚ))
    rw [← Ideal.under_def]; rw [← Ideal.over_def (P.map (algebraMap S Sₚ)) P]
  have h : Function.Bijective (algebraMap R₂ R₁) :=
    (Localization.algEquiv P.primeCompl R₁).bijective
  have key : p.map (algebraMap R R₂) =
      ((maximalIdeal Rₚ).map (algebraMap Rₚ R₁)).comap (algebraMap R₂ R₁) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p]; rw [p.map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq R R₂ R₁]; rw [← p.map_map]; rw [comap_map_of_bijective _ h]
  rw [Module.length_quotient]; rw [Module.length_quotient]; rw [key]; rw [coheight_comap_of_surjective _ h.2]

end IsLocalization.AtPrime

namespace IsDedekindDomain

open IsLocalization AtPrime

variable [IsDomain R] [IsDedekindDomain S] [IsTorsionFree R S] [Algebra R Sₚ] [IsScalarTower R S Sₚ]
  [IsScalarTower R Rₚ Sₚ]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `primesOverEquivPrimesOver` / `primesOverEquivPrimesOver` 的定义

English:
definition primesOverEquivPrimesOver
  signature: (hp : p != ⊥)
  body: ⟨map (algebraMap S Sₚ) P.1, isPrime_map_of_liesOver S p Sₚ P.1,
    liesOver_map_of_liesOver p Rₚ Sₚ P.1⟩
  map_rel_iff' {Q Q'} := by
    refine ⟨fun h => ?_, fun h => map_mono h⟩
    have : Q'.1.IsMaximal :=
      (primesOver.isPrime p Q').isMaximal (ne_bot_of_mem_primesOver hp Q'.prop)
    simpa [

中文:
定义 primesOverEquivPrimesOver
  签名: (hp : p != ⊥)
  定义体: ⟨map (algebraMap S Sₚ) P.1, isPrime_map_of_liesOver S p Sₚ P.1,
    liesOver_map_of_liesOver p Rₚ Sₚ P.1⟩
  map_rel_iff' {Q Q'} := by
    refine ⟨fun h => ?_, fun h => map_mono h⟩
    have : Q'.1.IsMaximal :=
      (primesOver.isPrime p Q').isMaximal (ne_bot_of_mem_primesOver hp Q'.prop)
    simpa [

Depends on / 依赖: algebraMap, isPrime_map_of_liesOver
-/
noncomputable def primesOverEquivPrimesOver (hp : p != ⊥) :
    p.primesOver S ≃o (maximalIdeal Rₚ).primesOver Sₚ where
  toFun P := ⟨map (algebraMap S Sₚ) P.1, isPrime_map_of_liesOver S p Sₚ P.1,
    liesOver_map_of_liesOver p Rₚ Sₚ P.1⟩
  map_rel_iff' {Q Q'} := by
    refine ⟨fun h => ?_, fun h => map_mono h⟩
    have : Q'.1.IsMaximal :=
      (primesOver.isPrime p Q').isMaximal (ne_bot_of_mem_primesOver hp Q'.prop)
    simpa [under_map_of_isMaximal S p] using le_comap_of_map_le h
  invFun Q := ⟨comap (algebraMap S Sₚ) Q.1, IsPrime.under S Q.1,
    liesOver_comap_of_liesOver p Rₚ Q.1⟩
  left_inv P := by
    have : P.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
      (ne_bot_of_mem_primesOver hp P.prop) (primesOver.isPrime p P)
exact SetCoe.ext IsLocalization.AtPrime.under_map_of_isMaximal S p Sₚ P.1
right_inv Q := SetCoe.ext map_under (algebraMapSubmonoid S p.primeCompl) Sₚ Q

@[simp]
/--
theorem `primesOverEquivPrimesOver_apply` / 定理 `primesOverEquivPrimesOver_apply`

English:
theorem primesOverEquivPrimesOver_apply
  given: (hp : p != ⊥) (P : p.primesOver S)
  proof: rfl

@[simp]

中文:
定理 primesOverEquivPrimesOver_apply
  条件: (hp : p != ⊥) (P : p.primesOver S)
  证明: rfl

@[simp]
-/
theorem primesOverEquivPrimesOver_apply (hp : p != ⊥) (P : p.primesOver S) :
    primesOverEquivPrimesOver p Rₚ Sₚ hp P = Ideal.map (algebraMap S Sₚ) P := rfl

@[simp]
/--
theorem `primesOverEquivPrimesOver_symm_apply` / 定理 `primesOverEquivPrimesOver_symm_apply`

English:
theorem primesOverEquivPrimesOver_symm_apply
  given: (hp : p != ⊥) (Q : (maximalIdeal Rₚ).primesOver Sₚ)
  proof: rfl

中文:
定理 primesOverEquivPrimesOver_symm_apply
  条件: (hp : p != ⊥) (Q : (maximalIdeal Rₚ).primesOver Sₚ)
  证明: rfl
-/
theorem primesOverEquivPrimesOver_symm_apply (hp : p != ⊥) (Q : (maximalIdeal Rₚ).primesOver Sₚ) :
    ((primesOverEquivPrimesOver p Rₚ Sₚ hp).symm Q).1 = Ideal.comap (algebraMap S Sₚ) Q := rfl

/--
theorem `primesOverEquivPrimesOver_inertiagDeg_eq` / 定理 `primesOverEquivPrimesOver_inertiagDeg_eq`

English:
theorem primesOverEquivPrimesOver_inertiagDeg_eq
  given: [p.IsMaximal] (hp : p != ⊥) (P : p.primesOver S)
  proof: by
  have : NeZero p := ⟨hp⟩
  have : P.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
    (ne_bot_of_mem_primesOver (NeZero.ne _) P.prop) inferInstance
  have : (P.1.map (algebraMap S Sₚ)).LiesOver (maximalIdeal Rₚ) := liesOver_map_of_liesOver p _ _ _
  exact inertiaDeg_map_eq_inertiaDeg p _ _

中文:
定理 primesOverEquivPrimesOver_inertiagDeg_eq
  条件: [p.IsMaximal] (hp : p != ⊥) (P : p.primesOver S)
  证明: by
  have : NeZero p := ⟨hp⟩
  have : P.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
    (ne_bot_of_mem_primesOver (NeZero.ne _) P.prop) inferInstance
  have : (P.1.map (algebraMap S Sₚ)).LiesOver (maximalIdeal Rₚ) := liesOver_map_of_liesOver p _ _ _
  exact inertiaDeg_map_eq_inertiaDeg p _ _

Depends on / 依赖: DimensionLEOne, IsMaximal, LiesOver, NeZero, NeZero.ne, P.prop, P.val.IsMaximal, Ring.DimensionLEOne.maximalOfPrime, algebraMap, inertiaDeg_map_eq_inertiaDeg, liesOver_map_of_liesOver, maximalIdeal, maximalOfPrime, ne_bot_of_mem_primesOver
-/
theorem primesOverEquivPrimesOver_inertiagDeg_eq [p.IsMaximal] (hp : p != ⊥) (P : p.primesOver S) :
    (maximalIdeal Rₚ).inertiaDeg' (primesOverEquivPrimesOver p Rₚ Sₚ hp P : Ideal Sₚ) =
      p.inertiaDeg' P.val := by
  have : NeZero p := ⟨hp⟩
  have : P.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
    (ne_bot_of_mem_primesOver (NeZero.ne _) P.prop) inferInstance
  have : (P.1.map (algebraMap S Sₚ)).LiesOver (maximalIdeal Rₚ) := liesOver_map_of_liesOver p _ _ _
  exact inertiaDeg_map_eq_inertiaDeg p _ _ _

/--
theorem `primesOverEquivPrimesOver_ramificationIdx_eq` / 定理 `primesOverEquivPrimesOver_ramificationIdx_eq`

English:
theorem primesOverEquivPrimesOver_ramificationIdx_eq
  given: (hp : p != ⊥) (P : p.primesOver S)
  proof: ramificationIdx_map_eq_ramificationIdx p _ _ _

中文:
定理 primesOverEquivPrimesOver_ramificationIdx_eq
  条件: (hp : p != ⊥) (P : p.primesOver S)
  证明: ramificationIdx_map_eq_ramificationIdx p _ _ _

Depends on / 依赖: ramificationIdx_map_eq_ramificationIdx
-/
theorem primesOverEquivPrimesOver_ramificationIdx_eq (hp : p != ⊥) (P : p.primesOver S) :
    (primesOverEquivPrimesOver p Rₚ Sₚ hp P : Ideal Sₚ).ramificationIdx Rₚ =
      P.val.ramificationIdx R :=
  ramificationIdx_map_eq_ramificationIdx p _ _ _

end IsDedekindDomain
