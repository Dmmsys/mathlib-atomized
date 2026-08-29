/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

/-!
# UFD criteria via height `1` prime ideals and localization

## Main results
* `UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one` : Let `R` be a
  Noetherian domain. Then `R` is a UFD if and only if every height `1` prime ideal is principal.

* `UniqueFactorizationMonoid.iff_localizationAway_of_prime` : Let `R` be a Noetherian domain,
  `x ∈ R` be a prime element. Then `R` is a UFD if and only if `Rₓ` is a UFD.
-/

public section

variable {R : Type*} [CommRing R] [IsDomain R]

namespace Ideal

variable [WfDvdMonoid R] {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hxp : x ∉ p)

include hx hxp

/--
theorem `isPrincipal_of_isPrincipal_isLocalizationAway_of_prime` / 定理 `isPrincipal_of_isPrincipal_isLocalizationAway_of_prime`

English:
theorem isPrincipal_of_isPrincipal_isLocalizationAway_of_prime
  proof: by
  have := (disjoint_powers_iff_notMem_of_isPrime x).mpr hxp
  by_cases hpbot : p = ⊥
  · simp [hpbot, bot_isPrincipal]
  · have hi := IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
    have hpb : map (algebraMap R S) p != ⊥ := by simp [Ideal.map_eq_bot_iff_of_

中文:
定理 isPrincipal_of_isPrincipal_isLocalizationAway_of_prime
  证明: by
  have := (disjoint_powers_iff_notMem_of_isPrime x).mpr hxp
  by_cases hpbot : p = ⊥
  · simp [hpbot, bot_isPrincipal]
  · have hi := IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
    have hpb : map (algebraMap R S) p != ⊥ := by simp [Ideal.map_eq_bot_iff_of_

Depends on / 依赖: Ideal.map_eq_bot_iff_of_injective, IsLocalization, IsLocalization.injective, IsUnit, algebraMap, bot_isPrincipal, disjoint_powers_iff_notMem_of_isPrime, exists_reduced_fraction, hx.irreducible, hx.ne_zero, injective, irreducible, map_eq_bot_iff_of_injective, ne_zero, powers_le_nonZeroDivisors_of_noZeroDivisors, selfZPow
-/
theorem isPrincipal_of_isPrincipal_isLocalizationAway_of_prime
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S]
    (hp : (map (algebraMap R S) p).IsPrincipal) : p.IsPrincipal := by
  have := (disjoint_powers_iff_notMem_of_isPrime x).mpr hxp
  by_cases hpbot : p = ⊥
  · simp [hpbot, bot_isPrincipal]
  · have hi := IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
    have hpb : map (algebraMap R S) p != ⊥ := by simp [Ideal.map_eq_bot_iff_of_injective hi, hpbot]
    obtain ⟨g, hg⟩ := hp
have hg0 : g != 0 := fun hg0 => hpb by simp [hg0, hg]
    obtain ⟨a, n, hxa, hag⟩ := exists_reduced_fraction' x S hg0 hx.irreducible
    have hu : IsUnit (selfZPow x S n) :=
      IsUnit.of_mul_eq_one (selfZPow x S (- n)) (selfZPow_mul_neg x S n)
    refine ⟨a, Ideal.eq_of_map_algebraMap_le S x ?_ (by simp [IsPrime.mul_mem_left_iff hxp]) ?_⟩
    · simp [hg, map_span, ← span_singleton_mul_left_unit hu (algebraMap R S a), hag]
    · intro y hy
      rw [mem_span_singleton] at hy ⊢
      exact (hx.left_dvd_or_dvd_right_of_dvd_mul hy).resolve_left hxa

/--
theorem `isPrincipal_of_isPrincipal_localizationAway_of_prime` / 定理 `isPrincipal_of_isPrincipal_localizationAway_of_prime`

English:
theorem isPrincipal_of_isPrincipal_localizationAway_of_prime
  proof: p.isPrincipal_of_isPrincipal_isLocalizationAway_of_prime hx hxp (Localization.Away x) hp

中文:
定理 isPrincipal_of_isPrincipal_localizationAway_of_prime
  证明: p.isPrincipal_of_isPrincipal_isLocalizationAway_of_prime hx hxp (Localization.Away x) hp

Depends on / 依赖: Localization, Localization.Away, PreirreducibleSpace, Subsingleton, isPrincipal_of_isPrincipal_isLocalizationAway_of_prime, p.isPrincipal_of_isPrincipal_isLocalizationAway_of_prime
-/
theorem isPrincipal_of_isPrincipal_localizationAway_of_prime
    (hp : (map (algebraMap R (Localization.Away x)) p).IsPrincipal) : p.IsPrincipal :=
  p.isPrincipal_of_isPrincipal_isLocalizationAway_of_prime hx hxp (Localization.Away x) hp

end Ideal

namespace UniqueFactorizationMonoid

/--
theorem `isPrincipal_of_height_eq_one` / 定理 `isPrincipal_of_height_eq_one`

English:
theorem isPrincipal_of_height_eq_one
  statement: [UniqueFactorizationMonoid R]
  proof: by
  have hpn : p != ⊥ := p.ne_bot_of_height_eq_one hph
  obtain ⟨x, hxmem, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹_› hpn
  exact ⟨x, p.eq_span_singleton_of_height_eq_one hph hxmem hxp⟩

中文:
定理 isPrincipal_of_height_eq_one
  结论: [唯一分解幺半群 R]
  证明: by
  have hpn : p != ⊥ := p.ne_bot_of_height_eq_one hph
  obtain ⟨x, hxmem, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹_› hpn
  exact ⟨x, p.eq_span_singleton_of_height_eq_one hph hxmem hxp⟩

Depends on / 依赖: Ideal.IsPrime.exists_mem_prime_of_ne_bot, IndiscreteTopology, IsPrime, PreirreducibleSpace, eq_span_singleton_of_height_eq_one, exists_mem_prime_of_ne_bot, ne_bot_of_height_eq_one, p.eq_span_singleton_of_height_eq_one, p.ne_bot_of_height_eq_one
-/
theorem isPrincipal_of_height_eq_one [UniqueFactorizationMonoid R]
    {p : Ideal R} [p.IsPrime] (hph : p.height = 1) : p.IsPrincipal := by
  have hpn : p != ⊥ := p.ne_bot_of_height_eq_one hph
  obtain ⟨x, hxmem, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹_› hpn
  exact ⟨x, p.eq_span_singleton_of_height_eq_one hph hxmem hxp⟩

variable [IsNoetherianRing R]

/--
theorem `of_forall_isPrincipal_of_height_eq_one` / 定理 `of_forall_isPrincipal_of_height_eq_one`

English:
theorem of_forall_isPrincipal_of_height_eq_one
  proof: by
  rw [iff_exists_prime_mem_of_isPrime]
  intro I hIn _
  rcases I.ne_bot_iff.mp hIn with ⟨x, hxI, hx0⟩
  rcases Ideal.exists_minimalPrimes_le (I.span_singleton_le_iff_mem.mpr hxI) with ⟨p, hpmin, hpl⟩
  have : p.IsPrime := hpmin.isPrime
have hpn : p != ⊥ := fun hpb => hx0
Ideal.span_singleton_eq_

中文:
定理 of_对任意_isPrincipal_of_height_eq_one
  证明: by
  rw [iff_exists_prime_mem_of_isPrime]
  intro I hIn _
  rcases I.ne_bot_iff.mp hIn with ⟨x, hxI, hx0⟩
  rcases Ideal.exists_minimalPrimes_le (I.span_singleton_le_iff_mem.mpr hxI) with ⟨p, hpmin, hpl⟩
  have : p.IsPrime := hpmin.isPrime
have hpn : p != ⊥ := fun hpb => hx0
Ideal.span_singleton_eq_

Depends on / 依赖: CofiniteTopology, I.ne_bot_iff.mp, I.span_singleton_le_iff_mem.mpr, Ideal.exists_minimalPrimes_le, Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes, Ideal.span_singleton_eq_bot.mp, Infinite, IrreducibleSpace, IsPrime, IsPrincipal, Order.one_le_iff_ne_zero, bot_unique, exists_minimalPrimes_le, generat, height_le_one_of_isPrincipal_of_mem_minimalPrimes, hpmin.isPrime, hpmin.le.trans_eq, hpp.generat, iff_exists_prime_mem_of_isPrime, isPrime
-/
theorem of_forall_isPrincipal_of_height_eq_one
    (h : forall (p : Ideal R) [p.IsPrime], p.height = 1 -> p.IsPrincipal) :
    UniqueFactorizationMonoid R := by
  rw [iff_exists_prime_mem_of_isPrime]
  intro I hIn _
  rcases I.ne_bot_iff.mp hIn with ⟨x, hxI, hx0⟩
  rcases Ideal.exists_minimalPrimes_le (I.span_singleton_le_iff_mem.mpr hxI) with ⟨p, hpmin, hpl⟩
  have : p.IsPrime := hpmin.isPrime
have hpn : p != ⊥ := fun hpb => hx0
Ideal.span_singleton_eq_bot.mp bot_unique (hpmin.le.trans_eq hpb)
have hpp : p.IsPrincipal := h p le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hpmin)
      (by simpa [Order.one_le_iff_ne_zero])
  exact ⟨hpp.generator p, hpl (hpp.generator_mem p), hpp.prime_generator_of_isPrime p hpn⟩

/-- Let `R` be a Noetherian domain. Then `R` is a UFD if and only if every height `1` prime ideal is
  principal. -/
@[stacks 0AFT]
/--
theorem `iff_forall_isPrincipal_of_height_eq_one` / 定理 `iff_forall_isPrincipal_of_height_eq_one`

English:
theorem iff_forall_isPrincipal_of_height_eq_one
  proof: ⟨fun _ _ _ => isPrincipal_of_height_eq_one, of_forall_isPrincipal_of_height_eq_one⟩

中文:
定理 iff_对任意_isPrincipal_of_height_eq_one
  证明: ⟨fun _ _ _ => isPrincipal_of_height_eq_one, of_forall_isPrincipal_of_height_eq_one⟩

Depends on / 依赖: isPrincipal_of_height_eq_one, of_forall_isPrincipal_of_height_eq_one
-/
theorem iff_forall_isPrincipal_of_height_eq_one :
    UniqueFactorizationMonoid R ↔ forall (p : Ideal R) [p.IsPrime], p.height = 1 -> p.IsPrincipal :=
  ⟨fun _ _ _ => isPrincipal_of_height_eq_one, of_forall_isPrincipal_of_height_eq_one⟩

/--
theorem `iff_of_isLocalizationAway_of_prime` / 定理 `iff_of_isLocalizationAway_of_prime`

English:
theorem iff_of_isLocalizationAway_of_prime
  statement: {x : R} (hx : Prime x)
  proof: by
  have : IsDomain S := IsLocalization.Away.isDomain S hx.ne_zero
  refine ⟨fun _ => of_isLocalization (Submonoid.powers x) S, fun _ => ?_⟩
  rw [iff_forall_isPrincipal_of_height_eq_one]
  intro p hp h1
  by_cases hxp : x in p
  · exact ⟨x, p.eq_span_singleton_of_height_eq_one h1 hxp hx⟩
  · have 

中文:
定理 iff_of_isLocalizationAway_of_prime
  结论: {x : R} (hx : 素 x)
  证明: by
  have : IsDomain S := IsLocalization.Away.isDomain S hx.ne_zero
  refine ⟨fun _ => of_isLocalization (Submonoid.powers x) S, fun _ => ?_⟩
  rw [iff_forall_isPrincipal_of_height_eq_one]
  intro p hp h1
  by_cases hxp : x in p
  · exact ⟨x, p.eq_span_singleton_of_height_eq_one h1 hxp hx⟩
  · have 

Depends on / 依赖: Ideal.disjoint_powers_iff_notMem_of_isPrime, IsDomain, IsLocalization, IsLocalization.Away.isDomain, IsLocalization.isPrime_of_isPrime_disjoint, Submonoid, Submonoid.powers, disjoint_powers_iff_notMem_of_isPrime, eq_span_singleton_of_height_eq_one, hx.ne_zero, iff_forall_isPrincipal_of_height_eq_one, isDomain, isPrime_of_isPrime_disjoint, isPrincipal_of_isPrincipal_isLocalizationAway_of_prim, ne_zero, of_isLocalization, p.eq_span_singleton_of_height_eq_one, p.isPrincipal_of_isPrincipal_isLocalizationAway_of_prim, powers
-/
theorem iff_of_isLocalizationAway_of_prime {x : R} (hx : Prime x)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S] :
    UniqueFactorizationMonoid R ↔ UniqueFactorizationMonoid S := by
  have : IsDomain S := IsLocalization.Away.isDomain S hx.ne_zero
  refine ⟨fun _ => of_isLocalization (Submonoid.powers x) S, fun _ => ?_⟩
  rw [iff_forall_isPrincipal_of_height_eq_one]
  intro p hp h1
  by_cases hxp : x in p
  · exact ⟨x, p.eq_span_singleton_of_height_eq_one h1 hxp hx⟩
  · have hd := by rwa [← Ideal.disjoint_powers_iff_notMem_of_isPrime x] at hxp
    have := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x) S p hp hd
    refine p.isPrincipal_of_isPrincipal_isLocalizationAway_of_prime hx hxp S
      (isPrincipal_of_height_eq_one ?_)
    rw [← IsLocalization.height_under (Submonoid.powers x)]; rw [IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers x) S hp hd]; rw [h1]

/--
theorem `iff_localizationAway_of_prime` / 定理 `iff_localizationAway_of_prime`

English:
theorem iff_localizationAway_of_prime
  given: {x : R} (hx : Prime x)
  proof: iff_of_isLocalizationAway_of_prime hx (Localization.Away x)

中文:
定理 iff_localizationAway_of_prime
  条件: {x : R} (hx : 素 x)
  证明: iff_of_isLocalizationAway_of_prime hx (Localization.Away x)

Depends on / 依赖: Localization, Localization.Away, iff_of_isLocalizationAway_of_prime
-/
theorem iff_localizationAway_of_prime {x : R} (hx : Prime x) :
    UniqueFactorizationMonoid R ↔ UniqueFactorizationMonoid (Localization.Away x) :=
  iff_of_isLocalizationAway_of_prime hx (Localization.Away x)

end UniqueFactorizationMonoid
