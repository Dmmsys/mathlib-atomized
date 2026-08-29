/-
Copyright (c) 2021 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.Order.Atoms
public import Mathlib.Order.Hom.Bounded
/-!

# Chains of divisors

The results in this file show that in the monoid `Associates M` of a `UniqueFactorizationMonoid`
`M`, an element `a` is an n-th prime power iff its set of divisors is a strictly increasing chain
of length `n + 1`, meaning that we can find a strictly increasing bijection between `Fin (n + 1)`
and the set of factors of `a`.

## Main results
- `DivisorChain.exists_chain_of_prime_pow` : existence of a chain for prime powers.
- `DivisorChain.is_prime_pow_of_has_chain` : elements that have a chain are prime powers.
- `multiplicity_prime_eq_multiplicity_image_by_factor_orderIso` : if there is a
  monotone bijection `d` between the set of factors of `a : Associates M` and the set of factors of
  `b : Associates N` then for any prime `p ∣ a`, `multiplicity p a = multiplicity (d p) b`.
- `multiplicity_eq_multiplicity_factor_dvd_iso_of_mem_normalizedFactors` : if there is a bijection
  between the set of factors of `a : M` and `b : N` then for any prime `p ∣ a`,
  `multiplicity p a = multiplicity (d p) b`


## TODO
- Create a structure for chains of divisors.
- Simplify proof of `mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors` using
  `mem_normalizedFactors_factor_order_iso_of_mem_normalizedFactors` or vice versa.

-/

@[expose] public section

assert_not_exists Field

variable {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]

/--
theorem `Associates.isAtom_iff` / 定理 `Associates.isAtom_iff`

English:
theorem Associates.isAtom_iff
  given: {p : Associates M} (h₁ : p != 0)
  statement: IsAtom p ↔ Irreducible p
  proof: ⟨fun hp =>
    ⟨by simpa only [Associates.isUnit_iff_eq_one] using! hp.1, fun a b h =>
      (hp.le_iff.mp ⟨_, h⟩).casesOn (fun ha => Or.inl (a.isUnit_iff_eq_one.mpr ha)) fun ha =>
        Or.inr
          (show IsUnit b by
            rw [ha] at h
            apply isUnit_of_associated_mul (show As

中文:
定理 Associates.isAtom_iff
  条件: {p : Associates M} (h₁ : p != 0)
  结论: IsAtom p ↔ Irreducible p
  证明: ⟨fun hp =>
    ⟨by simpa only [Associates.isUnit_iff_eq_one] using! hp.1, fun a b h =>
      (hp.le_iff.mp ⟨_, h⟩).casesOn (fun ha => Or.inl (a.isUnit_iff_eq_one.mpr ha)) fun ha =>
        Or.inr
          (show IsUnit b by
            rw [ha] at h
            apply isUnit_of_associated_mul (show As

Depends on / 依赖: Associated, Associates, Associates.bot_eq_one, Associates.isUnit_iff_eq, Associates.isUnit_iff_eq_one, IsUnit, Or.inl, Or.inr, a.isUnit_iff_eq_one.mpr, bot_eq_one, casesOn, conv_rhs, hp.isUnit_or_isUnit, hp.le_iff.mp, isUnit_iff_eq, isUnit_iff_eq_one, isUnit_of_associated_mul, isUnit_or_isUnit, le_iff
-/
theorem Associates.isAtom_iff {p : Associates M} (h₁ : p != 0) : IsAtom p ↔ Irreducible p :=
  ⟨fun hp =>
    ⟨by simpa only [Associates.isUnit_iff_eq_one] using! hp.1, fun a b h =>
      (hp.le_iff.mp ⟨_, h⟩).casesOn (fun ha => Or.inl (a.isUnit_iff_eq_one.mpr ha)) fun ha =>
        Or.inr
          (show IsUnit b by
            rw [ha] at h
            apply isUnit_of_associated_mul (show Associated (p * b) p by conv_rhs => rw [h]) h₁)⟩,
    fun hp =>
    ⟨by simpa only [Associates.isUnit_iff_eq_one, Associates.bot_eq_one] using! hp.1,
      fun b ⟨⟨a, hab⟩, hb⟩ =>
      (hp.isUnit_or_isUnit hab).casesOn
        (fun hb => show b = ⊥ by rwa [Associates.isUnit_iff_eq_one, ← Associates.bot_eq_one] at hb)
        fun ha =>
        absurd
          (show p ∣ b from
            ⟨(ha.unit⁻¹ : Units _), by rw [hab, mul_assoc, IsUnit.mul_val_inv ha, mul_one]⟩)
          hb⟩⟩

open UniqueFactorizationMonoid Irreducible Associates

namespace DivisorChain

/--
theorem `exists_chain_of_prime_pow` / 定理 `exists_chain_of_prime_pow`

English:
theorem exists_chain_of_prime_pow
  given: {p : Associates M} {n : Nat} (hn : n != 0) (hp : Prime p)
  proof: by
  refine ⟨fun i => p ^ (i : Nat), ?_, fun n m h => ?_, @fun y => ⟨fun h => ?_, ?_⟩⟩
  · dsimp only
    rw [Fin.coe_ofNat_eq_mod]; rw [Nat.mod_eq_of_lt]; rw [pow_one]
    exact Nat.lt_succ_of_le (Nat.one_le_iff_ne_zero.mpr hn)
  · exact Associates.dvdNotUnit_iff_lt.mp
        ⟨pow_ne_zero n hp.ne_

中文:
定理 exists_chain_of_prime_pow
  条件: {p : Associates M} {n : 自然数} (hn : n != 0) (hp : Prime p)
  证明: by
  refine ⟨fun i => p ^ (i : Nat), ?_, fun n m h => ?_, @fun y => ⟨fun h => ?_, ?_⟩⟩
  · dsimp only
    rw [Fin.coe_ofNat_eq_mod]; rw [Nat.mod_eq_of_lt]; rw [pow_one]
    exact Nat.lt_succ_of_le (Nat.one_le_iff_ne_zero.mpr hn)
  · exact Associates.dvdNotUnit_iff_lt.mp
        ⟨pow_ne_zero n hp.ne_

Depends on / 依赖: Associates, Associates.dvdNotUnit_iff_lt.mp, Fin.coe_ofNat_eq_mod, Nat.lt_succ_of_le, Nat.mod_eq_of_lt, Nat.one_le_iff_ne_zero.mpr, Nat.sub_pos_of_lt, associated_iff_eq, coe_ofNat_eq_mod, dvdNotUnit_iff_lt, dvd_pow, dvd_prime_pow, dvd_rfl, h.le, hp.ne_zero, hp.not_isUnit, i_le, lt_succ_of_le, mod_eq_of_lt, ne_zero
-/
theorem exists_chain_of_prime_pow {p : Associates M} {n : Nat} (hn : n != 0) (hp : Prime p) :
    exists c : Fin (n + 1) -> Associates M,
      c 1 = p ∧ StrictMono c ∧ forall {r : Associates M}, r <= p ^ n ↔ exists i, r = c i := by
  refine ⟨fun i => p ^ (i : Nat), ?_, fun n m h => ?_, @fun y => ⟨fun h => ?_, ?_⟩⟩
  · dsimp only
    rw [Fin.coe_ofNat_eq_mod]; rw [Nat.mod_eq_of_lt]; rw [pow_one]
    exact Nat.lt_succ_of_le (Nat.one_le_iff_ne_zero.mpr hn)
  · exact Associates.dvdNotUnit_iff_lt.mp
        ⟨pow_ne_zero n hp.ne_zero, p ^ (m - n : Nat),
          not_isUnit_of_not_isUnit_dvd hp.not_isUnit (dvd_pow dvd_rfl (Nat.sub_pos_of_lt h).ne'),
          (pow_mul_pow_sub p h.le).symm⟩
  · obtain ⟨i, i_le, hi⟩ := (dvd_prime_pow hp n).1 h
    rw [associated_iff_eq] at hi
    exact ⟨⟨i, Nat.lt_succ_of_le i_le⟩, hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨p ^ (n - i : Nat), (pow_mul_pow_sub p (Nat.succ_le_succ_iff.mp i.2)).symm⟩

/--
theorem `element_of_chain_not_isUnit_of_index_ne_zero` / 定理 `element_of_chain_not_isUnit_of_index_ne_zero`

English:
theorem element_of_chain_not_isUnit_of_index_ne_zero
  statement: {n : Nat} {i : Fin (n + 1)} (i_pos : i != 0)
  proof: DvdNotUnit.not_isUnit
    (Associates.dvdNotUnit_iff_lt.2
      (h₁ <| show (0 : Fin (n + 1)) < i from Fin.pos_iff_ne_zero.mpr i_pos))

中文:
定理 element_of_chain_not_isUnit_of_index_ne_zero
  结论: {n : 自然数} {i : Fin (n + 1)} (i_pos : i != 0)
  证明: DvdNotUnit.not_isUnit
    (Associates.dvdNotUnit_iff_lt.2
      (h₁ <| show (0 : Fin (n + 1)) < i from Fin.pos_iff_ne_zero.mpr i_pos))

Depends on / 依赖: Associates, Associates.dvdNotUnit_iff_lt, DvdNotUnit, DvdNotUnit.not_isUnit, Fin.pos_iff_ne_zero.mpr, dvdNotUnit_iff_lt, i_pos, not_isUnit, pos_iff_ne_zero
-/
theorem element_of_chain_not_isUnit_of_index_ne_zero {n : Nat} {i : Fin (n + 1)} (i_pos : i != 0)
    {c : Fin (n + 1) -> Associates M} (h₁ : StrictMono c) : ¬IsUnit (c i) :=
  DvdNotUnit.not_isUnit
    (Associates.dvdNotUnit_iff_lt.2
      (h₁ <| show (0 : Fin (n + 1)) < i from Fin.pos_iff_ne_zero.mpr i_pos))

/--
theorem `first_of_chain_isUnit` / 定理 `first_of_chain_isUnit`

English:
theorem first_of_chain_isUnit
  statement: {q : Associates M} {n : Nat} {c : Fin (n + 1) -> Associates M}
  proof: by
  obtain ⟨i, hr⟩ := h₂.mp one_le
  rw [Associates.isUnit_iff_eq_one]; rw [← Associates.le_one_iff]; rw [hr]
  exact h₁.monotone (Fin.zero_le i)

中文:
定理 first_of_chain_isUnit
  结论: {q : Associates M} {n : 自然数} {c : Fin (n + 1) -> Associates M}
  证明: by
  obtain ⟨i, hr⟩ := h₂.mp one_le
  rw [Associates.isUnit_iff_eq_one]; rw [← Associates.le_one_iff]; rw [hr]
  exact h₁.monotone (Fin.zero_le i)

Depends on / 依赖: Associates, Associates.isUnit_iff_eq_one, Associates.le_one_iff, Fin.zero_le, isUnit_iff_eq_one, le_one_iff, monotone, one_le, zero_le
-/
theorem first_of_chain_isUnit {q : Associates M} {n : Nat} {c : Fin (n + 1) -> Associates M}
    (h₁ : StrictMono c) (h₂ : forall {r}, r <= q ↔ exists i, r = c i) : IsUnit (c 0) := by
  obtain ⟨i, hr⟩ := h₂.mp one_le
  rw [Associates.isUnit_iff_eq_one]; rw [← Associates.le_one_iff]; rw [hr]
  exact h₁.monotone (Fin.zero_le i)

/--
theorem `second_of_chain_is_irreducible` / 定理 `second_of_chain_is_irreducible`

English:
theorem second_of_chain_is_irreducible
  statement: {q : Associates M} {n : Nat} (hn : n != 0)
  proof: by
  rcases n with - | n; · contradiction
  refine (Associates.isAtom_iff (ne_zero_of_dvd_ne_zero hq (h₂.2 ⟨1, rfl⟩))).mp ⟨?_, fun b hb => ?_⟩
  · exact ne_bot_of_gt (h₁ zero_lt_one)
  obtain ⟨⟨i, hi⟩, rfl⟩ := h₂.1 (hb.le.trans (h₂.2 ⟨1, rfl⟩))
  cases i
  · exact (Associates.isUnit_iff_eq_one _).mp

中文:
定理 second_of_chain_is_irreducible
  结论: {q : Associates M} {n : 自然数} (hn : n != 0)
  证明: by
  rcases n with - | n; · contradiction
  refine (Associates.isAtom_iff (ne_zero_of_dvd_ne_zero hq (h₂.2 ⟨1, rfl⟩))).mp ⟨?_, fun b hb => ?_⟩
  · exact ne_bot_of_gt (h₁ zero_lt_one)
  obtain ⟨⟨i, hi⟩, rfl⟩ := h₂.1 (hb.le.trans (h₂.2 ⟨1, rfl⟩))
  cases i
  · exact (Associates.isUnit_iff_eq_one _).mp

Depends on / 依赖: Associates, Associates.isAtom_iff, Associates.isUnit_iff_eq_one, Fin.lt_def, first_of_chain_isUnit, hb.le.trans, isAtom_iff, isUnit_iff_eq_one, lt_def, lt_iff_lt, lt_iff_lt.mp, ne_bot_of_gt, ne_zero_of_dvd_ne_zero, zero_lt_one
-/
theorem second_of_chain_is_irreducible {q : Associates M} {n : Nat} (hn : n != 0)
    {c : Fin (n + 1) -> Associates M} (h₁ : StrictMono c) (h₂ : forall {r}, r <= q ↔ exists i, r = c i)
    (hq : q != 0) : Irreducible (c 1) := by
  rcases n with - | n; · contradiction
  refine (Associates.isAtom_iff (ne_zero_of_dvd_ne_zero hq (h₂.2 ⟨1, rfl⟩))).mp ⟨?_, fun b hb => ?_⟩
  · exact ne_bot_of_gt (h₁ zero_lt_one)
  obtain ⟨⟨i, hi⟩, rfl⟩ := h₂.1 (hb.le.trans (h₂.2 ⟨1, rfl⟩))
  cases i
  · exact (Associates.isUnit_iff_eq_one _).mp (first_of_chain_isUnit h₁ @h₂)
  · simpa [Fin.lt_def] using h₁.lt_iff_lt.mp hb

/--
theorem `eq_second_of_chain_of_prime_dvd` / 定理 `eq_second_of_chain_of_prime_dvd`

English:
theorem eq_second_of_chain_of_prime_dvd
  statement: {p q r : Associates M} {n : Nat} (hn : n != 0)
  proof: by
  rcases n with - | n
  · contradiction
  obtain ⟨i, rfl⟩ := h₂.1 (dvd_trans hp' hr)
  refine congr_arg c (eq_of_le_of_not_lt' ?_ fun hi => ?_)
  · rw [Fin.le_iff_val_le_val, Fin.val_one, Nat.succ_le_iff, ← Fin.val_zero (n.succ + 1), ←
      Fin.lt_def, Fin.pos_iff_ne_zero]
    rintro rfl
    exa

中文:
定理 eq_second_of_chain_of_prime_dvd
  结论: {p q r : Associates M} {n : 自然数} (hn : n != 0)
  证明: by
  rcases n with - | n
  · contradiction
  obtain ⟨i, rfl⟩ := h₂.1 (dvd_trans hp' hr)
  refine congr_arg c (eq_of_le_of_not_lt' ?_ fun hi => ?_)
  · rw [Fin.le_iff_val_le_val, Fin.val_one, Nat.succ_le_iff, ← Fin.val_zero (n.succ + 1), ←
      Fin.lt_def, Fin.pos_iff_ne_zero]
    rintro rfl
    exa

Depends on / 依赖: Associates, Associates.dvdNotUnit_iff_lt, DvdNotUnit, DvdNotUnit.not_isUnit, Fin.le_iff_val_le_val, Fin.lt_def, Fin.pos_iff_ne_zero, Fin.val_one, Fin.val_zero, Nat.succ_le_iff, congr_arg, dvdNotUnit_iff_lt, dvd_trans, eq_of_le_of_not_lt, eq_zero_or_eq_succ, first_of_chain_isUnit, hp.not_isUnit, i.eq_zero_or_eq_succ, le_iff_val_le_val, lt_def
-/
theorem eq_second_of_chain_of_prime_dvd {p q r : Associates M} {n : Nat} (hn : n != 0)
    {c : Fin (n + 1) -> Associates M} (h₁ : StrictMono c)
    (h₂ : forall {r : Associates M}, r <= q ↔ exists i, r = c i) (hp : Prime p) (hr : r ∣ q) (hp' : p ∣ r) :
    p = c 1 := by
  rcases n with - | n
  · contradiction
  obtain ⟨i, rfl⟩ := h₂.1 (dvd_trans hp' hr)
  refine congr_arg c (eq_of_le_of_not_lt' ?_ fun hi => ?_)
  · rw [Fin.le_iff_val_le_val, Fin.val_one, Nat.succ_le_iff, ← Fin.val_zero (n.succ + 1), ←
      Fin.lt_def, Fin.pos_iff_ne_zero]
    rintro rfl
    exact hp.not_isUnit (first_of_chain_isUnit h₁ @h₂)
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  · cases hi
  refine
    not_irreducible_of_not_isUnit_of_dvdNotUnit
      (DvdNotUnit.not_isUnit
        (Associates.dvdNotUnit_iff_lt.2 (h₁ (show (0 : Fin (n + 2)) < j.castSucc from ?_))))
      ?_ hp.irreducible
  · simpa using Fin.lt_def.mp hi
  · refine Associates.dvdNotUnit_iff_lt.2 (h₁ ?_)
    simpa only [Fin.coe_eq_castSucc] using Fin.castSucc_lt_succ

omit [IsCancelMulZero M]

/--
theorem `card_subset_divisors_le_length_of_chain` / 定理 `card_subset_divisors_le_length_of_chain`

English:
theorem card_subset_divisors_le_length_of_chain
  statement: {q : Associates M} {n : Nat}
  proof: by
  classical
    have mem_image : forall r : Associates M, r <= q -> r in Finset.univ.image c := by
      intro r hr
      obtain ⟨i, hi⟩ := h₂.1 hr
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩
    rw [← Finset.card_fin (n + 1)]
    exact (Finset.card_le_card fun x hx => mem_imag

中文:
定理 card_subset_divisors_le_length_of_chain
  结论: {q : Associates M} {n : 自然数}
  证明: by
  classical
    have mem_image : forall r : Associates M, r <= q -> r in Finset.univ.image c := by
      intro r hr
      obtain ⟨i, hi⟩ := h₂.1 hr
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩
    rw [← Finset.card_fin (n + 1)]
    exact (Finset.card_le_card fun x hx => mem_imag

Depends on / 依赖: Associates, Finset, Finset.card_fin, Finset.card_image_le, Finset.card_le_card, Finset.mem_image, Finset.mem_univ, Finset.univ.image, card_fin, card_image_le, card_le_card, classical, hi.symm, mem_image, mem_univ
-/
theorem card_subset_divisors_le_length_of_chain {q : Associates M} {n : Nat}
    {c : Fin (n + 1) -> Associates M} (h₂ : forall {r}, r <= q ↔ exists i, r = c i) {m : Finset (Associates M)}
    (hm : forall r, r in m -> r <= q) : m.card <= n + 1 := by
  classical
    have mem_image : forall r : Associates M, r <= q -> r in Finset.univ.image c := by
      intro r hr
      obtain ⟨i, hi⟩ := h₂.1 hr
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩
    rw [← Finset.card_fin (n + 1)]
    exact (Finset.card_le_card fun x hx => mem_image x <| hm x hx).trans Finset.card_image_le

variable [UniqueFactorizationMonoid M]

/--
theorem `element_of_chain_eq_pow_second_of_chain` / 定理 `element_of_chain_eq_pow_second_of_chain`

English:
theorem element_of_chain_eq_pow_second_of_chain
  statement: {q r : Associates M} {n : Nat} (hn : n != 0)
  proof: by
  classical
    let i := Multiset.card (normalizedFactors r)
    have hi : normalizedFactors r = Multiset.replicate i (c 1) := by
      apply Multiset.eq_replicate_of_mem
      intro b hb
      refine
        eq_second_of_chain_of_prime_dvd hn h₁ (@fun r' => h₂) (prime_of_normalized_factor b hb) 

中文:
定理 element_of_chain_eq_pow_second_of_chain
  结论: {q r : Associates M} {n : 自然数} (hn : n != 0)
  证明: by
  classical
    let i := Multiset.card (normalizedFactors r)
    have hi : normalizedFactors r = Multiset.replicate i (c 1) := by
      apply Multiset.eq_replicate_of_mem
      intro b hb
      refine
        eq_second_of_chain_of_prime_dvd hn h₁ (@fun r' => h₂) (prime_of_normalized_factor b hb) 

Depends on / 依赖: Multiset, Multiset.card, Multiset.eq_replicate_of_mem, Multiset.prod_replicate, Multiset.replicate, UniqueFactorizationMonoid, UniqueFactorizationMonoid.prod_normalizedFactors, associated_iff_eq, classical, dvd_of_mem_normalizedFactors, eq_replicate_of_mem, eq_second_of_chain_of_prime_dvd, ne_zero_of_dvd_ne_zero, normalizedFactors, prime_of_normalized_factor, prod_normalizedFactors, prod_replicate, replicate
-/
theorem element_of_chain_eq_pow_second_of_chain {q r : Associates M} {n : Nat} (hn : n != 0)
    {c : Fin (n + 1) -> Associates M} (h₁ : StrictMono c) (h₂ : forall {r}, r <= q ↔ exists i, r = c i)
    (hr : r ∣ q) (hq : q != 0) : exists i : Fin (n + 1), r = c 1 ^ (i : Nat) := by
  classical
    let i := Multiset.card (normalizedFactors r)
    have hi : normalizedFactors r = Multiset.replicate i (c 1) := by
      apply Multiset.eq_replicate_of_mem
      intro b hb
      refine
        eq_second_of_chain_of_prime_dvd hn h₁ (@fun r' => h₂) (prime_of_normalized_factor b hb) hr
          (dvd_of_mem_normalizedFactors hb)
    have H : r = c 1 ^ i := by
      have := UniqueFactorizationMonoid.prod_normalizedFactors (ne_zero_of_dvd_ne_zero hq hr)
      rw [associated_iff_eq]; rw [hi]; rw [Multiset.prod_replicate] at this
      rw [this]
    refine ⟨⟨i, ?_⟩, H⟩
    have : (Finset.univ.image fun m : Fin (i + 1) => c 1 ^ (m : Nat)).card = i + 1 := by
      conv_rhs => rw [← Finset.card_fin (i + 1)]
      cases n
      · contradiction
      rw [Finset.card_image_iff]
      refine Set.injOn_of_injective (fun m m' h => Fin.ext ?_)
      refine
        pow_injective_of_not_isUnit (element_of_chain_not_isUnit_of_index_ne_zero (by simp) h₁) ?_ h
      exact Irreducible.ne_zero (second_of_chain_is_irreducible hn h₁ (@h₂) hq)
    suffices H' : forall r in Finset.univ.image fun m : Fin (i + 1) => c 1 ^ (m : Nat), r <= q by
      simp only [← Nat.succ_le_iff, Nat.succ_eq_add_one, ← this]
      apply card_subset_divisors_le_length_of_chain (@h₂) H'
    simp only [Finset.mem_image]
    rintro r ⟨a, _, rfl⟩
    refine dvd_trans ?_ hr
    use c 1 ^ (i - (a : Nat))
    rw [pow_mul_pow_sub (c 1)]
    · exact H
    · exact Nat.succ_le_succ_iff.mp a.2

/--
theorem `eq_pow_second_of_chain_of_has_chain` / 定理 `eq_pow_second_of_chain_of_has_chain`

English:
theorem eq_pow_second_of_chain_of_has_chain
  statement: {q : Associates M} {n : Nat} (hn : n != 0)
  proof: by
  classical
    obtain ⟨i, hi'⟩ := element_of_chain_eq_pow_second_of_chain hn h₁ (@fun r => h₂) (dvd_refl q) hq
    convert! hi'
    refine (Nat.lt_succ_iff.1 i.prop).antisymm' (Nat.le_of_succ_le_succ ?_)
    calc
      n + 1 = (Finset.univ : Finset (Fin (n + 1))).card := (Finset.card_fin _).symm

中文:
定理 eq_pow_second_of_chain_of_has_chain
  结论: {q : Associates M} {n : 自然数} (hn : n != 0)
  证明: by
  classical
    obtain ⟨i, hi'⟩ := element_of_chain_eq_pow_second_of_chain hn h₁ (@fun r => h₂) (dvd_refl q) hq
    convert! hi'
    refine (Nat.lt_succ_iff.1 i.prop).antisymm' (Nat.le_of_succ_le_succ ?_)
    calc
      n + 1 = (Finset.univ : Finset (Fin (n + 1))).card := (Finset.card_fin _).symm

Depends on / 依赖: Finset, Finset.card_fin, Finset.card_image_iff.mpr, Finset.card_le_card, Finset.univ, Finset.univ.image, Nat.le_of_succ_le_succ, Nat.lt_succ_iff, antisymm, card_fin, card_image_iff, card_le_card, classical, convert, dvd_refl, element_of_chain_eq_pow_second_of_chain, i.prop, injective, injective.injOn, le_of_succ_le_succ
-/
theorem eq_pow_second_of_chain_of_has_chain {q : Associates M} {n : Nat} (hn : n != 0)
    {c : Fin (n + 1) -> Associates M} (h₁ : StrictMono c)
    (h₂ : forall {r : Associates M}, r <= q ↔ exists i, r = c i) (hq : q != 0) : q = c 1 ^ n := by
  classical
    obtain ⟨i, hi'⟩ := element_of_chain_eq_pow_second_of_chain hn h₁ (@fun r => h₂) (dvd_refl q) hq
    convert! hi'
    refine (Nat.lt_succ_iff.1 i.prop).antisymm' (Nat.le_of_succ_le_succ ?_)
    calc
      n + 1 = (Finset.univ : Finset (Fin (n + 1))).card := (Finset.card_fin _).symm
      _ = (Finset.univ.image c).card := (Finset.card_image_iff.mpr h₁.injective.injOn).symm
      _ <= (Finset.univ.image fun m : Fin (i + 1) => c 1 ^ (m : Nat)).card :=
        (Finset.card_le_card ?_)
      _ <= (Finset.univ : Finset (Fin (i + 1))).card := Finset.card_image_le
      _ = i + 1 := Finset.card_fin _
    intro r hr
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hr
    have := h₂.2 ⟨j, rfl⟩
    rw [hi'] at this
    have h := (dvd_prime_pow (show Prime (c 1) from ?_) i).1 this
    · rcases h with ⟨u, hu, hu'⟩
      refine Finset.mem_image.mpr ⟨⟨u, Nat.lt_succ_of_le hu⟩, Finset.mem_univ _, ?_⟩
      rwa [associated_iff_eq, eq_comm] at hu'
    · rw [← irreducible_iff_prime]
      exact second_of_chain_is_irreducible hn h₁ (@h₂) hq

/--
theorem `isPrimePow_of_has_chain` / 定理 `isPrimePow_of_has_chain`

English:
theorem isPrimePow_of_has_chain
  statement: {q : Associates M} {n : Nat} (hn : n != 0)
  proof: ⟨c 1, n, irreducible_iff_prime.mp (second_of_chain_is_irreducible hn h₁ (@h₂) hq),
    zero_lt_iff.mpr hn, (eq_pow_second_of_chain_of_has_chain hn h₁ (@h₂) hq).symm⟩

中文:
定理 isPrimePow_of_has_chain
  结论: {q : Associates M} {n : 自然数} (hn : n != 0)
  证明: ⟨c 1, n, irreducible_iff_prime.mp (second_of_chain_is_irreducible hn h₁ (@h₂) hq),
    zero_lt_iff.mpr hn, (eq_pow_second_of_chain_of_has_chain hn h₁ (@h₂) hq).symm⟩

Depends on / 依赖: eq_pow_second_of_chain_of_has_chain, irreducible_iff_prime, irreducible_iff_prime.mp, second_of_chain_is_irreducible, zero_lt_iff, zero_lt_iff.mpr
-/
theorem isPrimePow_of_has_chain {q : Associates M} {n : Nat} (hn : n != 0)
    {c : Fin (n + 1) -> Associates M} (h₁ : StrictMono c)
    (h₂ : forall {r : Associates M}, r <= q ↔ exists i, r = c i) (hq : q != 0) : IsPrimePow q :=
  ⟨c 1, n, irreducible_iff_prime.mp (second_of_chain_is_irreducible hn h₁ (@h₂) hq),
    zero_lt_iff.mpr hn, (eq_pow_second_of_chain_of_has_chain hn h₁ (@h₂) hq).symm⟩

end DivisorChain

variable {N : Type*} [CommMonoidWithZero N]

/--
theorem `factor_orderIso_map_one_eq_bot` / 定理 `factor_orderIso_map_one_eq_bot`

English:
theorem factor_orderIso_map_one_eq_bot
  statement: [IsCancelMulZero N] {m : Associates M} {n : Associates N}
  proof: by
  let : OrderBot { l : Associates M // l <= m } := Subtype.orderBot bot_le
  let : OrderBot { l : Associates N // l <= n } := Subtype.orderBot bot_le
  simp only [← Associates.bot_eq_one, Subtype.mk_bot, bot_le, Subtype.coe_eq_bot_iff]
  let : BotHomClass ({ l // l <= m } ≃o { l // l <= n }) _ _ 

中文:
定理 factor_orderIso_map_one_eq_bot
  结论: [IsCancelMulZero N] {m : Associates M} {n : Associates N}
  证明: by
  let : OrderBot { l : Associates M // l <= m } := Subtype.orderBot bot_le
  let : OrderBot { l : Associates N // l <= n } := Subtype.orderBot bot_le
  simp only [← Associates.bot_eq_one, Subtype.mk_bot, bot_le, Subtype.coe_eq_bot_iff]
  let : BotHomClass ({ l // l <= m } ≃o { l // l <= n }) _ _ 

Depends on / 依赖: Associates, Associates.bot_eq_one, BotHomClass, OrderBot, OrderIsoClass, OrderIsoClass.toBotHomClass, Subtype, Subtype.coe_eq_bot_iff, Subtype.mk_bot, Subtype.orderBot, bot_eq_one, bot_le, coe_eq_bot_iff, map_bot, mk_bot, orderBot, toBotHomClass
-/
theorem factor_orderIso_map_one_eq_bot [IsCancelMulZero N] {m : Associates M} {n : Associates N}
    (d : { l : Associates M // l <= m } ≃o { l : Associates N // l <= n }) :
    (d ⟨1, one_dvd m⟩ : Associates N) = 1 := by
  let : OrderBot { l : Associates M // l <= m } := Subtype.orderBot bot_le
  let : OrderBot { l : Associates N // l <= n } := Subtype.orderBot bot_le
  simp only [← Associates.bot_eq_one, Subtype.mk_bot, bot_le, Subtype.coe_eq_bot_iff]
  let : BotHomClass ({ l // l <= m } ≃o { l // l <= n }) _ _ := OrderIsoClass.toBotHomClass
  exact map_bot d

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_factor_orderIso_map_eq_one_iff` / 定理 `coe_factor_orderIso_map_eq_one_iff`

English:
theorem coe_factor_orderIso_map_eq_one_iff
  statement: [IsCancelMulZero N]
  proof: ⟨fun hu => by
    rw [show u = (d.symm ⟨d ⟨u]; rw [hu'⟩]; rw [(d ⟨u]; rw [hu'⟩).prop⟩) by
        simp only [Subtype.coe_eta]; rw [OrderIso.symm_apply_apply]; rw [Subtype.coe_mk]]
    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d.symm]
    congr, fun hu => by
    simp_rw [hu]
    conv_rhs => rw

中文:
定理 coe_factor_orderIso_map_eq_one_iff
  结论: [IsCancelMulZero N]
  证明: ⟨fun hu => by
    rw [show u = (d.symm ⟨d ⟨u]; rw [hu'⟩]; rw [(d ⟨u]; rw [hu'⟩).prop⟩) by
        simp only [Subtype.coe_eta]; rw [OrderIso.symm_apply_apply]; rw [Subtype.coe_mk]]
    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d.symm]
    congr, fun hu => by
    simp_rw [hu]
    conv_rhs => rw

Depends on / 依赖: OrderIso, OrderIso.symm_apply_apply, Subtype, Subtype.coe_eta, Subtype.coe_mk, coe_eta, coe_mk, conv_rhs, d.symm, factor_orderIso_map_one_eq_bot, simp_rw, symm_apply_apply
-/
theorem coe_factor_orderIso_map_eq_one_iff [IsCancelMulZero N]
    {m u : Associates M} {n : Associates N} (hu' : u <= m)
    (d : Set.Iic m ≃o Set.Iic n) : (d ⟨u, hu'⟩ : Associates N) = 1 ↔ u = 1 :=
  ⟨fun hu => by
    rw [show u = (d.symm ⟨d ⟨u]; rw [hu'⟩]; rw [(d ⟨u]; rw [hu'⟩).prop⟩) by
        simp only [Subtype.coe_eta]; rw [OrderIso.symm_apply_apply]; rw [Subtype.coe_mk]]
    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d.symm]
    congr, fun hu => by
    simp_rw [hu]
    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d]
    rfl⟩

section

variable [UniqueFactorizationMonoid N] [UniqueFactorizationMonoid M]

open DivisorChain


set_option linter.overlappingInstances false

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pow_image_of_prime_by_factor_orderIso_dvd` / 定理 `pow_image_of_prime_by_factor_orderIso_dvd`

English:
theorem pow_image_of_prime_by_factor_orderIso_dvd
  proof: by
  by_cases hs : s = 0
  · simp [← Associates.bot_eq_one, hs]
  suffices (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) ^ s =
      (d ⟨p ^ s, hs'⟩) by
    rw [this]
    apply Subtype.prop (d ⟨p ^ s, hs'⟩)
  obtain ⟨c₁, rfl, hc₁', hc₁''⟩ := exists_chain_of_prime_pow hs (prime_of_normalize

中文:
定理 pow_image_of_prime_by_factor_orderIso_dvd
  证明: by
  by_cases hs : s = 0
  · simp [← Associates.bot_eq_one, hs]
  suffices (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) ^ s =
      (d ⟨p ^ s, hs'⟩) by
    rw [this]
    apply Subtype.prop (d ⟨p ^ s, hs'⟩)
  obtain ⟨c₁, rfl, hc₁', hc₁''⟩ := exists_chain_of_prime_pow hs (prime_of_normalize

Depends on / 依赖: Associates, Associates.bot_eq_one, Subtype, Subtype.prop, bot_eq_one, dvd_of_mem_normalizedFactors, eq_pow_second_of_chain_of_has_c, exists_chain_of_prime_pow, le_trans, prime_of_normalized_factor
-/
theorem pow_image_of_prime_by_factor_orderIso_dvd
    {m p : Associates M} {n : Associates N} (hn : n != 0) (hp : p in normalizedFactors m)
    (d : Set.Iic m ≃o Set.Iic n) {s : Nat} (hs' : p ^ s <= m) :
    (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) ^ s <= n := by
  by_cases hs : s = 0
  · simp [← Associates.bot_eq_one, hs]
  suffices (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) ^ s =
      (d ⟨p ^ s, hs'⟩) by
    rw [this]
    apply Subtype.prop (d ⟨p ^ s, hs'⟩)
  obtain ⟨c₁, rfl, hc₁', hc₁''⟩ := exists_chain_of_prime_pow hs (prime_of_normalized_factor p hp)
  let c₂ : Fin (s + 1) -> Associates N := fun t => d ⟨c₁ t, le_trans (hc₁''.2 ⟨t, by simp⟩) hs'⟩
  have c₂_def : forall t, c₂ t = d ⟨c₁ t, _⟩ := fun t => rfl
  rw [← c₂_def]
  refine (eq_pow_second_of_chain_of_has_chain hs (fun t u h => ?_)
    (@fun r => ⟨@fun hr => ?_, ?_⟩) ?_).symm
  · rw [c₂_def, c₂_def, Subtype.coe_lt_coe, d.lt_iff_lt, Subtype.mk_lt_mk, hc₁'.lt_iff_lt]
    exact h
  · have : r <= n := hr.trans (d ⟨c₁ 1 ^ s, _⟩).2
    suffices d.symm ⟨r, this⟩ <= ⟨c₁ 1 ^ s, hs'⟩ by
      obtain ⟨i, hi⟩ := hc₁''.1 this
      use i
      simp only [c₂_def, ← hi, d.apply_symm_apply, Subtype.coe_eta, Subtype.coe_mk]
    conv_rhs => rw [← d.symm_apply_apply ⟨c₁ 1 ^ s, hs'⟩]
    rw [d.symm.le_iff_le]
    simpa only [← Subtype.coe_le_coe, Subtype.coe_mk] using hr
  · rintro ⟨i, hr⟩
    rw [hr]; rw [c₂_def]; rw [Subtype.coe_le_coe]; rw [d.le_iff_le]
    simpa [Subtype.mk_le_mk] using hc₁''.2 ⟨i, rfl⟩
  exact ne_zero_of_dvd_ne_zero hn (Subtype.prop (d ⟨c₁ 1 ^ s, _⟩))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_prime_of_factor_orderIso` / 定理 `map_prime_of_factor_orderIso`

English:
theorem map_prime_of_factor_orderIso
  statement: {m p : Associates M} {n : Associates N} (hn : n != 0)
  proof: by
  rw [← irreducible_iff_prime]
  refine (Associates.isAtom_iff <|
    ne_zero_of_dvd_ne_zero hn (d ⟨p, _⟩).prop).mp ⟨?_, fun b hb => ?_⟩
  · rw [Ne, ← Associates.isUnit_iff_eq_bot, Associates.isUnit_iff_eq_one,
      coe_factor_orderIso_map_eq_one_iff _ d]
    rintro rfl
    exact (prime_of_norma

中文:
定理 map_prime_of_factor_orderIso
  结论: {m p : Associates M} {n : Associates N} (hn : n != 0)
  证明: by
  rw [← irreducible_iff_prime]
  refine (Associates.isAtom_iff <|
    ne_zero_of_dvd_ne_zero hn (d ⟨p, _⟩).prop).mp ⟨?_, fun b hb => ?_⟩
  · rw [Ne, ← Associates.isUnit_iff_eq_bot, Associates.isUnit_iff_eq_one,
      coe_factor_orderIso_map_eq_one_iff _ d]
    rintro rfl
    exact (prime_of_norma

Depends on / 依赖: Associates, Associates.isAtom_iff, Associates.isUnit_iff_eq_bot, Associates.isUnit_iff_eq_one, Subtype, Subtype.coe_mk, coe_factor_orderIso_map_eq_one_iff, coe_mk, d.surjective, dvd_of_mem_normalizedFactors, irreducible_iff_prime, isAtom_iff, isUnit_iff_eq_bot, isUnit_iff_eq_one, isUnit_one, le_of_lt, le_trans, ne_zero_of_dvd_ne_zero, not_isUnit, prime_of_normalized_factor
-/
theorem map_prime_of_factor_orderIso {m p : Associates M} {n : Associates N} (hn : n != 0)
    (hp : p in normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    Prime (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) := by
  rw [← irreducible_iff_prime]
  refine (Associates.isAtom_iff <|
    ne_zero_of_dvd_ne_zero hn (d ⟨p, _⟩).prop).mp ⟨?_, fun b hb => ?_⟩
  · rw [Ne, ← Associates.isUnit_iff_eq_bot, Associates.isUnit_iff_eq_one,
      coe_factor_orderIso_map_eq_one_iff _ d]
    rintro rfl
    exact (prime_of_normalized_factor 1 hp).not_isUnit isUnit_one
  · have : b <= n := le_trans (le_of_lt hb) (d ⟨p, dvd_of_mem_normalizedFactors hp⟩).prop
    obtain ⟨x, hx⟩ := d.surjective ⟨b, this⟩
    rw [← Subtype.coe_mk (p := (· <= n)) b this]; rw [← hx] at hb
    let : OrderBot { l : Associates M // l <= m } := Subtype.orderBot bot_le
    let : OrderBot { l : Associates N // l <= n } := Subtype.orderBot bot_le
    suffices x = ⊥ by
      rw [this]; rw [OrderIso.map_bot d] at hx
      refine (Subtype.mk_eq_bot_iff ?_ _).mp hx.symm
      simp
    obtain ⟨a, ha⟩ := x
    rw [Subtype.mk_eq_bot_iff]
    · exact
        ((Associates.isAtom_iff <| Prime.ne_zero <| prime_of_normalized_factor p hp).mpr <|
              irreducible_of_normalized_factor p hp).right
          a (Subtype.mk_lt_mk.mp <| d.lt_iff_lt.mp hb)
    simp

/--
theorem `mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors` / 定理 `mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors`

English:
theorem mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors
  statement: {m p : Associates M}
  proof: by
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd hn (map_prime_of_factor_orderIso hn hp d).irreducible
      (d ⟨p, dvd_of_mem_normalizedFactors hp⟩).prop
  rw [associated_iff_eq] at hq'
  rwa [hq']

中文:
定理 mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors
  结论: {m p : Associates M}
  证明: by
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd hn (map_prime_of_factor_orderIso hn hp d).irreducible
      (d ⟨p, dvd_of_mem_normalizedFactors hp⟩).prop
  rw [associated_iff_eq] at hq'
  rwa [hq']

Depends on / 依赖: associated_iff_eq, dvd_of_mem_normalizedFactors, exists_mem_normalizedFactors_of_dvd, irreducible, map_prime_of_factor_orderIso
-/
theorem mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors {m p : Associates M}
    {n : Associates N} (hn : n != 0) (hp : p in normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) in normalizedFactors n := by
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd hn (map_prime_of_factor_orderIso hn hp d).irreducible
      (d ⟨p, dvd_of_mem_normalizedFactors hp⟩).prop
  rw [associated_iff_eq] at hq'
  rwa [hq']

/--
theorem `emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso` / 定理 `emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso`

English:
theorem emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso
  statement: {m p : Associates M}
  proof: by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hm : m = 0
  · simp [hm] at hp
  rw [FiniteMultiplicity.of_prime_left (prime_of_normalized_factor p hp) hm
.emultiplicity_eq_multiplicity]; rw [← pow_dvd_iff_le_emultiplicity]
  apply pow_image_of_prime_by_factor_orderIso_dvd hn hp d (pow_multiplicit

中文:
定理 emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso
  结论: {m p : Associates M}
  证明: by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hm : m = 0
  · simp [hm] at hp
  rw [FiniteMultiplicity.of_prime_left (prime_of_normalized_factor p hp) hm
.emultiplicity_eq_multiplicity]; rw [← pow_dvd_iff_le_emultiplicity]
  apply pow_image_of_prime_by_factor_orderIso_dvd hn hp d (pow_multiplicit

Depends on / 依赖: FiniteMultiplicity, FiniteMultiplicity.of_prime_left, emultiplicity_eq_multiplicity, of_prime_left, pow_dvd_iff_le_emultiplicity, pow_image_of_prime_by_factor_orderIso_dvd, pow_multiplicity_dvd, prime_of_normalized_factor
-/
theorem emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso {m p : Associates M}
    {n : Associates N} (hp : p in normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    emultiplicity p m <= emultiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hm : m = 0
  · simp [hm] at hp
  rw [FiniteMultiplicity.of_prime_left (prime_of_normalized_factor p hp) hm
.emultiplicity_eq_multiplicity]; rw [← pow_dvd_iff_le_emultiplicity]
  apply pow_image_of_prime_by_factor_orderIso_dvd hn hp d (pow_multiplicity_dvd ..)

/--
theorem `emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso` / 定理 `emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso`

English:
theorem emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso
  statement: {m p : Associates M}
  proof: by
  refine le_antisymm (emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso hp d) ?_
  suffices emultiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n <=
      emultiplicity (↑(d.symm (d ⟨p, dvd_of_mem_normalizedFactors hp⟩))) m by
    rw [d.symm_apply_apply ⟨p]; rw [dvd_of_mem_norma

中文:
定理 emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso
  结论: {m p : Associates M}
  证明: by
  refine le_antisymm (emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso hp d) ?_
  suffices emultiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n <=
      emultiplicity (↑(d.symm (d ⟨p, dvd_of_mem_normalizedFactors hp⟩))) m by
    rw [d.symm_apply_apply ⟨p]; rw [dvd_of_mem_norma

Depends on / 依赖: Associates, Classical, Classical.decEq, Subtype, Subtype.coe_eta, Subtype.coe_mk, coe_eta, coe_mk, d.symm, d.symm_apply_apply, dvd_of_mem_normalizedFactors, emultiplicity, emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso, le_antisymm, mem_normalizedFactor, symm_apply_apply
-/
theorem emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso {m p : Associates M}
    {n : Associates N} (hn : n != 0) (hp : p in normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    emultiplicity p m = emultiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n := by
  refine le_antisymm (emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso hp d) ?_
  suffices emultiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n <=
      emultiplicity (↑(d.symm (d ⟨p, dvd_of_mem_normalizedFactors hp⟩))) m by
    rw [d.symm_apply_apply ⟨p]; rw [dvd_of_mem_normalizedFactors hp⟩]; rw [Subtype.coe_mk] at this
    exact this
  let := Classical.decEq (Associates N)
  simpa only [Subtype.coe_eta] using
    emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso
      (mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors hn hp d) d.symm

end

variable [Subsingleton Mˣ] [Subsingleton Nˣ]

/-- The order isomorphism between the factors of `mk m` and the factors of `mk n` induced by a
  bijection between the factors of `m` and the factors of `n` that preserves `∣`. -/
@[simps]
/--
Definition of `mkFactorOrderIsoOfFactorDvdEquiv` / `mkFactorOrderIsoOfFactorDvdEquiv` 的定义

English:
definition mkFactorOrderIsoOfFactorDvdEquiv
  body: ⟨Associates.mk
        (d
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l
            rw [Subtype.coe_mk]; rw [associatesEquivOfUniqueUnits_apply]; rw [out_dvd_iff]
            exact hx⟩),
      mk_le_mk_iff_dvd.mpr (Subtype.prop (d ⟨associatesEquivOfUniqueUnits ↑l, _⟩

中文:
定义 mkFactorOrderIsoOfFactorDvdEquiv
  定义体: ⟨Associates.mk
        (d
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l
            rw [Subtype.coe_mk]; rw [associatesEquivOfUniqueUnits_apply]; rw [out_dvd_iff]
            exact hx⟩),
      mk_le_mk_iff_dvd.mpr (Subtype.prop (d ⟨associatesEquivOfUniqueUnits ↑l, _⟩

Depends on / 依赖: Associates, Associates.mk, Subtype, Subtype.coe_mk, Subtype.prop, associatesEquivOfUniqueUnits, associatesEquivOfUniqueUnits_apply, coe_mk, d.symm, invFun, mk_le_mk_iff_dvd, mk_le_mk_iff_dvd.mpr, out_dvd_iff
-/
def mkFactorOrderIsoOfFactorDvdEquiv
    {m : M} {n : N} {d : { l : M // l ∣ m } ≃ { l : N // l ∣ n }}
    (hd : forall l l', (d l : N) ∣ d l' ↔ (l : M) ∣ (l' : M)) :
    Set.Iic (Associates.mk m) ≃o Set.Iic (Associates.mk n) where
  toFun l :=
    ⟨Associates.mk
        (d
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l
            rw [Subtype.coe_mk]; rw [associatesEquivOfUniqueUnits_apply]; rw [out_dvd_iff]
            exact hx⟩),
      mk_le_mk_iff_dvd.mpr (Subtype.prop (d ⟨associatesEquivOfUniqueUnits ↑l, _⟩))⟩
  invFun l :=
    ⟨Associates.mk
        (d.symm
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l
            rw [Subtype.coe_mk]; rw [associatesEquivOfUniqueUnits_apply]; rw [out_dvd_iff]
            exact hx⟩),
      mk_le_mk_iff_dvd.mpr (Subtype.prop (d.symm ⟨associatesEquivOfUniqueUnits ↑l, _⟩))⟩
  left_inv := fun ⟨l, hl⟩ => by
    simp only [Subtype.coe_eta, Equiv.symm_apply_apply, Subtype.coe_mk,
      associatesEquivOfUniqueUnits_apply, mk_out, out_mk, normalize_eq]
  right_inv := fun ⟨l, hl⟩ => by
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_mk,
      associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq, mk_out]
  map_rel_iff' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Associates.mk_le_mk_iff_dvd, hd,
        associatesEquivOfUniqueUnits_apply, out_dvd_iff, mk_out]

variable [UniqueFactorizationMonoid M] [UniqueFactorizationMonoid N]

set_option linter.overlappingInstances false

/--
theorem `mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors` / 定理 `mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors`

English:
theorem mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors
  statement: {m p : M} {n : N} (hm : m != 0)
  proof: by
  suffices
    Prime (d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
            simp [dvd_of_mem_normalizedFactors hp]⟩ : N) by
    simp only [associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq,
      associatesEquivOfUniqueUnits_symm_apply] at this
    obtain ⟨q

中文:
定理 mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors
  结论: {m p : M} {n : N} (hm : m != 0)
  证明: by
  suffices
    Prime (d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
            simp [dvd_of_mem_normalizedFactors hp]⟩ : N) by
    simp only [associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq,
      associatesEquivOfUniqueUnits_symm_apply] at this
    obtain ⟨q

Depends on / 依赖: Associates, Associates.mk, associated_iff_eq, associated_iff_eq.mp, associatesE, associatesEquivOfUniqueUnits, associatesEquivOfUniqueUnits.symm, associatesEquivOfUniqueUnits_apply, associatesEquivOfUniqueUnits_symm_apply, convert, dvd_of_mem_normalizedFactors, exists_mem_normalizedFactors_of_dvd, irreducible, normalize_eq, out_mk, this.irreducible
-/
theorem mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors {m p : M} {n : N} (hm : m != 0)
    (hn : n != 0) (hp : p in normalizedFactors m) {d : { l : M // l ∣ m } ≃ { l : N // l ∣ n }}
    (hd : forall l l', (d l : N) ∣ d l' ↔ (l : M) ∣ (l' : M)) :
    ↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩) in normalizedFactors n := by
  suffices
    Prime (d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
            simp [dvd_of_mem_normalizedFactors hp]⟩ : N) by
    simp only [associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq,
      associatesEquivOfUniqueUnits_symm_apply] at this
    obtain ⟨q, hq, hq'⟩ :=
      exists_mem_normalizedFactors_of_dvd hn this.irreducible
        (d ⟨p, by apply dvd_of_mem_normalizedFactors; convert! hp⟩).prop
    rwa [associated_iff_eq.mp hq']
  have :
    Associates.mk
        (d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
              simp only [dvd_of_mem_normalizedFactors hp, associatesEquivOfUniqueUnits_apply,
                out_mk, normalize_eq, associatesEquivOfUniqueUnits_symm_apply]⟩ : N) =
      ↑(mkFactorOrderIsoOfFactorDvdEquiv hd
          ⟨associatesEquivOfUniqueUnits.symm p, by
            simp only [associatesEquivOfUniqueUnits_symm_apply]
            exact mk_dvd_mk.mpr (dvd_of_mem_normalizedFactors hp)⟩) := by
    rw [mkFactorOrderIsoOfFactorDvdEquiv_apply_coe]
  rw [← Associates.prime_mk]; rw [this]
  let := Classical.decEq (Associates M)
  refine map_prime_of_factor_orderIso (mk_ne_zero.mpr hn) ?_ _
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd (mk_ne_zero.mpr hm)
      (prime_mk.mpr (prime_of_normalized_factor p (by convert! hp))).irreducible
      (mk_le_mk_of_dvd (dvd_of_mem_normalizedFactors hp))
  simpa only [associated_iff_eq.mp hq', associatesEquivOfUniqueUnits_symm_apply] using hq

/--
theorem `emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors` / 定理 `emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors`

English:
theorem emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors
  statement: {m p : M} {n : N}
  proof: by
  apply Eq.symm
  suffices emultiplicity (Associates.mk p) (Associates.mk m) = emultiplicity (Associates.mk
    ↑(d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
      simp [dvd_of_mem_normalizedFactors hp]⟩)) (Associates.mk n) by
    simpa only [emultiplicity_mk_eq_emul

中文:
定理 emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors
  结论: {m p : M} {n : N}
  证明: by
  apply Eq.symm
  suffices emultiplicity (Associates.mk p) (Associates.mk m) = emultiplicity (Associates.mk
    ↑(d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
      simp [dvd_of_mem_normalizedFactors hp]⟩)) (Associates.mk n) by
    simpa only [emultiplicity_mk_eq_emul

Depends on / 依赖: Associates, Associates.mk, Eq.symm, associatesEquivOfUniqueUnits, associatesEquivOfUniqueUnits.symm, associatesEquivOfUniqueUnits_apply, associatesEquivOfUniqueUnits_symm_apply, dvd_of_mem_normalizedFactors, emultiplicity, emultiplicity_mk_eq_emultiplicity, normalize_eq, out_mk
-/
theorem emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors {m p : M} {n : N}
    (hm : m != 0) (hn : n != 0) (hp : p in normalizedFactors m)
    {d : { l : M // l ∣ m } ≃ { l : N // l ∣ n }} (hd : forall l l', (d l : N) ∣ d l' ↔ (l : M) ∣ l') :
    emultiplicity (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : N) n = emultiplicity p m := by
  apply Eq.symm
  suffices emultiplicity (Associates.mk p) (Associates.mk m) = emultiplicity (Associates.mk
    ↑(d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
      simp [dvd_of_mem_normalizedFactors hp]⟩)) (Associates.mk n) by
    simpa only [emultiplicity_mk_eq_emultiplicity, associatesEquivOfUniqueUnits_symm_apply,
      associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq] using this
  have : Associates.mk (d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
    simp only [dvd_of_mem_normalizedFactors hp, associatesEquivOfUniqueUnits_symm_apply,
      associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq]⟩ : N) =
    ↑(mkFactorOrderIsoOfFactorDvdEquiv hd ⟨associatesEquivOfUniqueUnits.symm p, by
      rw [associatesEquivOfUniqueUnits_symm_apply]
      exact mk_le_mk_of_dvd (dvd_of_mem_normalizedFactors hp)⟩) := by
    rw [mkFactorOrderIsoOfFactorDvdEquiv_apply_coe]
  rw [this]
  refine
    emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso (mk_ne_zero.mpr hn) ?_
      (mkFactorOrderIsoOfFactorDvdEquiv hd)
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd (mk_ne_zero.mpr hm)
      (prime_mk.mpr (prime_of_normalized_factor p hp)).irreducible
      (mk_le_mk_of_dvd (dvd_of_mem_normalizedFactors hp))
  rwa [associated_iff_eq.mp hq']
