/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Support

/-!

# Associated primes of localized module

This file mainly proves the relation between `Ass(S⁻¹M)` and `Ass(M)`

## Main Results

* `associatedPrimes.mem_associatePrimes_of_comap_mem_associatePrimes_isLocalizedModule` :
  for an `R` module `M`, if `p` is a prime ideal of `S⁻¹R` and `p ∩ R ∈ Ass(M)` then
  `p ∈ Ass (S⁻¹M)`.

-/

public section

variable {R : Type*} [CommRing R] (S : Submonoid R) {R' : Type*} [CommRing R'] [Algebra R R']
  [hSR' : IsLocalization S R']

variable {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  (f : M ->ₗ[R] M') [IsLocalizedModule S f] [Module R' M'] [IsScalarTower R R' M']

open IsLocalRing LinearMap Submodule

namespace Module.associatedPrimes

include S f in
@[stacks 0310 "(1)"]
/--
lemma `mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule` / 引理 `mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule`

English:
lemma mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
  proof: by
  rcases ass with ⟨hp, x, hx⟩
  constructor
  · refine (IsLocalization.isPrime_iff_isPrime_disjoint S _ _).mpr
      ⟨hp, (IsLocalization.disjoint_under_iff S R' p).mpr ?_⟩
    by_contra eqtop
    simp [eqtop, Ideal.comap_top, Ideal.isPrime_iff] at hp
  · use f x
    ext t
    rcases IsLocalization.exists_mk'_eq S t with ⟨r, s, hrs⟩
    simp_rw [← hrs, Ideal.mem_radical_iff, mem_colon_singleton, ← IsLocalizedModule.mk'_one S f,
      ← IsLocalization.mk'_pow, IsLocalizedModule.mk'_smul_mk', mul_one, mem_bot,
      IsLocalizedModule.mk'_eq_zero']
    refine ⟨fun h => exists_comm.mp ⟨1, ?_⟩, fun ⟨n, t, ht⟩ => ?_⟩
    · simp only [← mem_colon_singleton, one_smul, ← mem_bot R, ← hx, ← Ideal.mem_radical_iff]
      exact hSR'.mk'_mem_iff.mp h
    · have : hSR'.mk' R' r s = hSR'.mk' R' (t.1 * r) 1 * hSR'.mk' R' 1 (t * s) := by
        rw [← hSR'.mk'_mul]; rw [mul_one]; rw [one_mul]; rw [← sub_eq_zero]; rw [← hSR'.mk'_sub]; rw [Submonoid.coe_mul]
        simp [← mul_assoc, mul_comm r t.1, IsLocalization.mk'_zero]
      rw [this]
      apply Ideal.IsTwoSided.mul_mem_of_left
      rw [IsLocalization.mk'_one]; rw [← Ideal.mem_comap]; rw [hx]
      rcases eq_zero_or_pos n with rfl | hn
      · exact Ideal.IsTwoSided.mul_mem_of_left _ ⟨1, by simpa using! ht⟩
      · use n
        rw [mem_colon_singleton]; rw [mul_pow]; rw [mul_smul]; rw [← mem_colon_singleton]
        exact Ideal.pow_mem_of_mem _ (by simpa using! ht) n hn

中文:
引理 mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
  证明: by
  rcases ass with ⟨hp, x, hx⟩
  constructor
  · refine (IsLocalization.isPrime_iff_isPrime_disjoint S _ _).mpr
      ⟨hp, (IsLocalization.disjoint_under_iff S R' p).mpr ?_⟩
    by_contra eqtop
    simp [eqtop, Ideal.comap_top, Ideal.isPrime_iff] at hp
  · use f x
    ext t
    rcases IsLocalization.exists_mk'_eq S t with ⟨r, s, hrs⟩
    simp_rw [← hrs, Ideal.mem_radical_iff, mem_colon_singleton, ← IsLocalizedModule.mk'_one S f,
      ← IsLocalization.mk'_pow, IsLocalizedModule.mk'_smul_mk', mul_one, mem_bot,
      IsLocalizedModule.mk'_eq_zero']
    refine ⟨fun h => exists_comm.mp ⟨1, ?_⟩, fun ⟨n, t, ht⟩ => ?_⟩
    · simp only [← mem_colon_singleton, one_smul, ← mem_bot R, ← hx, ← Ideal.mem_radical_iff]
      exact hSR'.mk'_mem_iff.mp h
    · have : hSR'.mk' R' r s = hSR'.mk' R' (t.1 * r) 1 * hSR'.mk' R' 1 (t * s) := by
        rw [← hSR'.mk'_mul]; rw [mul_one]; rw [one_mul]; rw [← sub_eq_zero]; rw [← hSR'.mk'_sub]; rw [Submonoid.coe_mul]
        simp [← mul_assoc, mul_comm r t.1, IsLocalization.mk'_zero]
      rw [this]
      apply Ideal.IsTwoSided.mul_mem_of_left
      rw [IsLocalization.mk'_one]; rw [← Ideal.mem_comap]; rw [hx]
      rcases eq_zero_or_pos n with rfl | hn
      · exact Ideal.IsTwoSided.mul_mem_of_left _ ⟨1, by simpa using! ht⟩
      · use n
        rw [mem_colon_singleton]; rw [mul_pow]; rw [mul_smul]; rw [← mem_colon_singleton]
        exact Ideal.pow_mem_of_mem _ (by simpa using! ht) n hn

Depends on / 依赖: Ideal.comap_top, Ideal.isPrime_iff, Ideal.mem_radical_iff, IsLocalization, IsLocalization.disjoint_under_iff, IsLocalization.exists_mk, IsLocalization.isPrime_iff_isPrime_disjoint, IsLocalization.mk, IsLocalizedModule, IsLocalizedModule.mk, _one, _pow, _smul_mk, comap_top, disjoint_under_iff, exists_mk, isPrime_iff, isPrime_iff_isPrime_disjoint, mem_bot, mem_colon_singleton
-/
lemma mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
    (p : Ideal R') (ass : p.comap (algebraMap R R') in associatedPrimes R M) :
    p in associatedPrimes R' M' := by
  rcases ass with ⟨hp, x, hx⟩
  constructor
  · refine (IsLocalization.isPrime_iff_isPrime_disjoint S _ _).mpr
      ⟨hp, (IsLocalization.disjoint_under_iff S R' p).mpr ?_⟩
    by_contra eqtop
    simp [eqtop, Ideal.comap_top, Ideal.isPrime_iff] at hp
  · use f x
    ext t
    rcases IsLocalization.exists_mk'_eq S t with ⟨r, s, hrs⟩
    simp_rw [← hrs, Ideal.mem_radical_iff, mem_colon_singleton, ← IsLocalizedModule.mk'_one S f,
      ← IsLocalization.mk'_pow, IsLocalizedModule.mk'_smul_mk', mul_one, mem_bot,
      IsLocalizedModule.mk'_eq_zero']
    refine ⟨fun h => exists_comm.mp ⟨1, ?_⟩, fun ⟨n, t, ht⟩ => ?_⟩
    · simp only [← mem_colon_singleton, one_smul, ← mem_bot R, ← hx, ← Ideal.mem_radical_iff]
      exact hSR'.mk'_mem_iff.mp h
    · have : hSR'.mk' R' r s = hSR'.mk' R' (t.1 * r) 1 * hSR'.mk' R' 1 (t * s) := by
        rw [← hSR'.mk'_mul]; rw [mul_one]; rw [one_mul]; rw [← sub_eq_zero]; rw [← hSR'.mk'_sub]; rw [Submonoid.coe_mul]
        simp [← mul_assoc, mul_comm r t.1, IsLocalization.mk'_zero]
      rw [this]
      apply Ideal.IsTwoSided.mul_mem_of_left
      rw [IsLocalization.mk'_one]; rw [← Ideal.mem_comap]; rw [hx]
      rcases eq_zero_or_pos n with rfl | hn
      · exact Ideal.IsTwoSided.mul_mem_of_left _ ⟨1, by simpa using! ht⟩
      · use n
        rw [mem_colon_singleton]; rw [mul_pow]; rw [mul_smul]; rw [← mem_colon_singleton]
        exact Ideal.pow_mem_of_mem _ (by simpa using! ht) n hn

/--
lemma `mem_associatedPrimes_atPrime_of_mem_associatedPrimes` / 引理 `mem_associatedPrimes_atPrime_of_mem_associatedPrimes`

English:
lemma mem_associatedPrimes_atPrime_of_mem_associatedPrimes
  proof: by
  apply mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)
  simpa [Localization.AtPrime.under_maximalIdeal] using ass

include S f in
@[stacks 0310 "(2)"]

中文:
引理 mem_associatedPrimes_atPrime_of_mem_associatedPrimes
  证明: by
  apply mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)
  simpa [Localization.AtPrime.under_maximalIdeal] using ass

include S f in
@[stacks 0310 "(2)"]

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime.under_maximalIdeal, LocalizedModule, LocalizedModule.mkLinearMap, mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule, mkLinearMap, p.primeCompl, primeCompl, under_maximalIdeal
-/
lemma mem_associatedPrimes_atPrime_of_mem_associatedPrimes
    {p : Ideal R} [p.IsPrime] (ass : p in associatedPrimes R M) :
    maximalIdeal (Localization.AtPrime p) in
    associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
  apply mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)
  simpa [Localization.AtPrime.under_maximalIdeal] using ass

include S f in
@[stacks 0310 "(2)"]
/--
lemma `comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg` / 引理 `comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg`

English:
lemma comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
  statement: (p : Ideal R')
  proof: by
  rcases ass with ⟨hp, x, hx⟩
  rcases fg with ⟨T, hT⟩
  rcases IsLocalizedModule.mk'_surjective S f x with ⟨⟨m, s⟩, rfl⟩
  simp only [Function.uncurry_apply_pair] at hx
  have mem (a : T) : algebraMap R R' a in p := by
    simpa [← Ideal.mem_comap, ← hT] using Ideal.subset_span a.2
  simp only [hx, Ideal.mem_radical_iff, mem_bot, mem_colon_singleton, ← map_pow, algebraMap_smul,
    ← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_eq_zero' f] at mem
  choose e g hg using mem
  refine ⟨.under R p, (∏ a, g a).1 • m, le_antisymm ?_ fun r hr => ?_⟩
  · rw [← hT, Ideal.span_le]
    intro a ha
    simp only [SetLike.mem_coe, Ideal.mem_radical_iff, mem_bot, mem_colon_singleton]
    obtain ⟨u, hu⟩ : g ⟨a, ha⟩ ∣ (∏ a, g a) := by
      apply Finset.dvd_prod_of_mem g (Finset.mem_univ ⟨a, ha⟩)
    use e ⟨a, ha⟩
    rw [hu]; rw [Submonoid.coe_mul]; rw [smul_smul]; rw [← mul_assoc]; rw [mul_comm]; rw [← smul_smul]; rw [mul_comm]; rw [← smul_smul]
    exact smul_eq_zero_of_right u.1 (hg ⟨a, ha⟩)
  · simp only [Ideal.mem_radical_iff, mem_bot, mem_colon_singleton, smul_smul] at hr
    obtain ⟨k, hk⟩ := hr
    have mem : r ^ k * (∏ a, g a).1 in Ideal.comap (algebraMap R R') p := by
      rw [hx]
      use 1
      simp_rw [pow_one, mem_colon_singleton, algebraMap_smul, ← IsLocalizedModule.mk'_smul,
        hk, IsLocalizedModule.mk'_zero, mem_bot]
    apply hp.mem_of_pow_mem k
    rw [← map_pow]
    exact ((hp.under R).mul_mem_iff_mem_or_mem.mp mem).resolve_right
      (Set.disjoint_left.mp ((IsLocalization.disjoint_under_iff S R' p).mpr hp.1) (∏ a, g a).2)

中文:
引理 comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
  结论: (p : 理想 R')
  证明: by
  rcases ass with ⟨hp, x, hx⟩
  rcases fg with ⟨T, hT⟩
  rcases IsLocalizedModule.mk'_surjective S f x with ⟨⟨m, s⟩, rfl⟩
  simp only [Function.uncurry_apply_pair] at hx
  have mem (a : T) : algebraMap R R' a in p := by
    simpa [← Ideal.mem_comap, ← hT] using Ideal.subset_span a.2
  simp only [hx, Ideal.mem_radical_iff, mem_bot, mem_colon_singleton, ← map_pow, algebraMap_smul,
    ← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_eq_zero' f] at mem
  choose e g hg using mem
  refine ⟨.under R p, (∏ a, g a).1 • m, le_antisymm ?_ fun r hr => ?_⟩
  · rw [← hT, Ideal.span_le]
    intro a ha
    simp only [SetLike.mem_coe, Ideal.mem_radical_iff, mem_bot, mem_colon_singleton]
    obtain ⟨u, hu⟩ : g ⟨a, ha⟩ ∣ (∏ a, g a) := by
      apply Finset.dvd_prod_of_mem g (Finset.mem_univ ⟨a, ha⟩)
    use e ⟨a, ha⟩
    rw [hu]; rw [Submonoid.coe_mul]; rw [smul_smul]; rw [← mul_assoc]; rw [mul_comm]; rw [← smul_smul]; rw [mul_comm]; rw [← smul_smul]
    exact smul_eq_zero_of_right u.1 (hg ⟨a, ha⟩)
  · simp only [Ideal.mem_radical_iff, mem_bot, mem_colon_singleton, smul_smul] at hr
    obtain ⟨k, hk⟩ := hr
    have mem : r ^ k * (∏ a, g a).1 in Ideal.comap (algebraMap R R') p := by
      rw [hx]
      use 1
      simp_rw [pow_one, mem_colon_singleton, algebraMap_smul, ← IsLocalizedModule.mk'_smul,
        hk, IsLocalizedModule.mk'_zero, mem_bot]
    apply hp.mem_of_pow_mem k
    rw [← map_pow]
    exact ((hp.under R).mul_mem_iff_mem_or_mem.mp mem).resolve_right
      (Set.disjoint_left.mp ((IsLocalization.disjoint_under_iff S R' p).mpr hp.1) (∏ a, g a).2)

Depends on / 依赖: Function, Function.uncurry_apply_pair, Ideal.mem_comap, Ideal.mem_radical_iff, Ideal.subset_span, IsLocalizedModule, IsLocalizedModule.mk, _eq_zero, _smul, _surjective, algebraMap, algebraMap_smul, map_pow, mem_bot, mem_colon_singleton, mem_comap, mem_radical_iff, subset_span, uncurry_apply_pair
-/
lemma comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg (p : Ideal R')
    (ass : p in associatedPrimes R' M') (fg : (p.comap (algebraMap R R')).FG) :
    p.comap (algebraMap R R') in associatedPrimes R M := by
  rcases ass with ⟨hp, x, hx⟩
  rcases fg with ⟨T, hT⟩
  rcases IsLocalizedModule.mk'_surjective S f x with ⟨⟨m, s⟩, rfl⟩
  simp only [Function.uncurry_apply_pair] at hx
  have mem (a : T) : algebraMap R R' a in p := by
    simpa [← Ideal.mem_comap, ← hT] using Ideal.subset_span a.2
  simp only [hx, Ideal.mem_radical_iff, mem_bot, mem_colon_singleton, ← map_pow, algebraMap_smul,
    ← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_eq_zero' f] at mem
  choose e g hg using mem
  refine ⟨.under R p, (∏ a, g a).1 • m, le_antisymm ?_ fun r hr => ?_⟩
  · rw [← hT, Ideal.span_le]
    intro a ha
    simp only [SetLike.mem_coe, Ideal.mem_radical_iff, mem_bot, mem_colon_singleton]
    obtain ⟨u, hu⟩ : g ⟨a, ha⟩ ∣ (∏ a, g a) := by
      apply Finset.dvd_prod_of_mem g (Finset.mem_univ ⟨a, ha⟩)
    use e ⟨a, ha⟩
    rw [hu]; rw [Submonoid.coe_mul]; rw [smul_smul]; rw [← mul_assoc]; rw [mul_comm]; rw [← smul_smul]; rw [mul_comm]; rw [← smul_smul]
    exact smul_eq_zero_of_right u.1 (hg ⟨a, ha⟩)
  · simp only [Ideal.mem_radical_iff, mem_bot, mem_colon_singleton, smul_smul] at hr
    obtain ⟨k, hk⟩ := hr
    have mem : r ^ k * (∏ a, g a).1 in Ideal.comap (algebraMap R R') p := by
      rw [hx]
      use 1
      simp_rw [pow_one, mem_colon_singleton, algebraMap_smul, ← IsLocalizedModule.mk'_smul,
        hk, IsLocalizedModule.mk'_zero, mem_bot]
    apply hp.mem_of_pow_mem k
    rw [← map_pow]
    exact ((hp.under R).mul_mem_iff_mem_or_mem.mp mem).resolve_right
      (Set.disjoint_left.mp ((IsLocalization.disjoint_under_iff S R' p).mpr hp.1) (∏ a, g a).2)

variable (R')

include S f in
open Set in
@[stacks 0310 "(3)"]
/--
lemma `preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule` / 引理 `preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule`

English:
lemma preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
  proof: by
  ext p
  exact ⟨mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule S f p,
    fun h => comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg S f p h
    ((isNoetherianRing_iff_ideal_fg R).mp ‹_› _)⟩

中文:
引理 preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
  证明: by
  ext p
  exact ⟨mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule S f p,
    fun h => comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg S f p h
    ((isNoetherianRing_iff_ideal_fg R).mp ‹_› _)⟩

Depends on / 依赖: comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg, isNoetherianRing_iff_ideal_fg, mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
-/
lemma preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    [IsNoetherianRing R] :
    (Ideal.comap (algebraMap R R')) ⁻¹' (associatedPrimes R M) = associatedPrimes R' M' := by
  ext p
  exact ⟨mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule S f p,
    fun h => comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg S f p h
    ((isNoetherianRing_iff_ideal_fg R).mp ‹_› _)⟩

set_option backward.isDefEq.respectTransparency.types false in
variable (R M) in
/--
lemma `minimalPrimes_annihilator_subset_associatedPrimes` / 引理 `minimalPrimes_annihilator_subset_associatedPrimes`

English:
lemma minimalPrimes_annihilator_subset_associatedPrimes
  given: [IsNoetherianRing R] [Module.Finite R M]
  proof: by
  intro p hp
  have prime := hp.isPrime
  let Rₚ := Localization.AtPrime p
  have : Nontrivial (LocalizedModule p.primeCompl M) := by
    simpa [← Module.mem_support_iff (p := ⟨p, prime⟩), Module.support_eq_zeroLocus] using! hp.1.2
  rcases associatedPrimes.nonempty Rₚ (LocalizedModule p.primeCompl M) with ⟨q, hq⟩
  have q_prime : q.IsPrime := IsAssociatedPrime.isPrime hq
  simp only [← preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule p.primeCompl
    Rₚ (LocalizedModule.mkLinearMap p.primeCompl M), Set.mem_preimage] at hq
  have ann_le : Module.annihilator R M <= Ideal.comap (algebraMap R Rₚ) q :=
    le_of_eq_of_le Submodule.annihilator_top.symm (IsAssociatedPrime.annihilator_le hq)
  have le : Ideal.comap (algebraMap R Rₚ) q <= p := by
    have := (IsLocalization.disjoint_under_iff p.primeCompl Rₚ q).mpr q_prime.ne_top
    simpa only [Ideal.primeCompl, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      Set.disjoint_compl_left_iff_subset] using! this
  simpa [Minimal.eq_of_le hp.out ⟨IsAssociatedPrime.isPrime hq, ann_le⟩ le] using! hq

中文:
引理 minimalPrimes_annihilator_subset_associatedPrimes
  条件: [是Noether环 R] [模.有限 R M]
  证明: by
  intro p hp
  have prime := hp.isPrime
  let Rₚ := Localization.AtPrime p
  have : Nontrivial (LocalizedModule p.primeCompl M) := by
    simpa [← Module.mem_support_iff (p := ⟨p, prime⟩), Module.support_eq_zeroLocus] using! hp.1.2
  rcases associatedPrimes.nonempty Rₚ (LocalizedModule p.primeCompl M) with ⟨q, hq⟩
  have q_prime : q.IsPrime := IsAssociatedPrime.isPrime hq
  simp only [← preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule p.primeCompl
    Rₚ (LocalizedModule.mkLinearMap p.primeCompl M), Set.mem_preimage] at hq
  have ann_le : Module.annihilator R M <= Ideal.comap (algebraMap R Rₚ) q :=
    le_of_eq_of_le Submodule.annihilator_top.symm (IsAssociatedPrime.annihilator_le hq)
  have le : Ideal.comap (algebraMap R Rₚ) q <= p := by
    have := (IsLocalization.disjoint_under_iff p.primeCompl Rₚ q).mpr q_prime.ne_top
    simpa only [Ideal.primeCompl, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      Set.disjoint_compl_left_iff_subset] using! this
  simpa [Minimal.eq_of_le hp.out ⟨IsAssociatedPrime.isPrime hq, ann_le⟩ le] using! hq

Depends on / 依赖: AtPrime, IsAssociatedPrime, IsAssociatedPrime.isPrime, IsPrime, Localization, Localization.AtPrime, LocalizedModule, LocalizedModule.mkLinearMap, Module, Module.mem_support_iff, Module.support_eq_zeroLocus, Nontrivial, associatedPrimes, associatedPrimes.nonempty, hp.isPrime, isPrime, mem_support_iff, mkLinearMap, nonempty, p.prime
-/
lemma minimalPrimes_annihilator_subset_associatedPrimes [IsNoetherianRing R] [Module.Finite R M] :
    (Module.annihilator R M).minimalPrimes subseteq associatedPrimes R M := by
  intro p hp
  have prime := hp.isPrime
  let Rₚ := Localization.AtPrime p
  have : Nontrivial (LocalizedModule p.primeCompl M) := by
    simpa [← Module.mem_support_iff (p := ⟨p, prime⟩), Module.support_eq_zeroLocus] using! hp.1.2
  rcases associatedPrimes.nonempty Rₚ (LocalizedModule p.primeCompl M) with ⟨q, hq⟩
  have q_prime : q.IsPrime := IsAssociatedPrime.isPrime hq
  simp only [← preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule p.primeCompl
    Rₚ (LocalizedModule.mkLinearMap p.primeCompl M), Set.mem_preimage] at hq
  have ann_le : Module.annihilator R M <= Ideal.comap (algebraMap R Rₚ) q :=
    le_of_eq_of_le Submodule.annihilator_top.symm (IsAssociatedPrime.annihilator_le hq)
  have le : Ideal.comap (algebraMap R Rₚ) q <= p := by
    have := (IsLocalization.disjoint_under_iff p.primeCompl Rₚ q).mpr q_prime.ne_top
    simpa only [Ideal.primeCompl, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      Set.disjoint_compl_left_iff_subset] using! this
  simpa [Minimal.eq_of_le hp.out ⟨IsAssociatedPrime.isPrime hq, ann_le⟩ le] using! hq

end Module.associatedPrimes
