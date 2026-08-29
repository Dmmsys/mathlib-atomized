/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Riccardo Brasca
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Cyclotomic units.

We gather miscellaneous results about units given by sums of powers of roots of unit, the so-called
*cyclotomic units*.


## Main results

* `IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime` : given an `n`-th primitive root of
  unity `ζ`, we have that `ζ - 1` and `ζ ^ j - 1` are associated for all `j` coprime with `n`.
* `IsPrimitiveRoot.associated_pow_sub_one_pow_of_coprime` : given an `n`-th primitive root of unity
  `ζ`, we have that `ζ ^ i - 1` and `ζ ^ j - 1` are associated for all `i` and `j` coprime with `n`.
* `IsPrimitiveRoot.associated_pow_add_sub_sub_one` : given an `n`-th primitive root of unity `ζ`,
  where `2 ≤ n`, we have that `ζ - 1` and `ζ ^ (i + j) - ζ ^ i` are associated for all and `j`
  coprime with `n` and all `i`.

## Implementation details

We sometimes state series of results of the form `a = u * b`, `IsUnit u` and `Associated a b`.
Often, `Associated a b` is everything one needs, and it is more convenient to use, we include the
other version for completeness.
-/

public section

open Polynomial Finset Nat

variable {n i j p : Nat} {A K : Type*} {ζ : A}

variable [CommRing A] [IsDomain A] {R : Type*} [CommRing R] [Algebra R A]

/--
theorem `sub_one_dvd_natCast_of_pow_eq_one` / 定理 `sub_one_dvd_natCast_of_pow_eq_one`

English:
theorem sub_one_dvd_natCast_of_pow_eq_one
  given: (hζ : ζ ^ n = 1) (hζ1 : ζ != 1)
  statement: ζ - 1 ∣ (n : A)
  proof: by
  have key : (n : A) = ∑ i in range n, (1 - ζ ^ i) := by
    have hgs : ∑ i in range n, ζ ^ i = 0 := by
      have := geom_sum_mul ζ n
      rw [hζ]; rw [sub_self] at this
      exact (mul_eq_zero.1 this).resolve_right fun h => hζ1 (sub_eq_zero.1 h)
    rw [Finset.sum_sub_distrib]; rw [hgs]; rw [

中文:
定理 sub_one_dvd_natCast_of_pow_eq_one
  条件: (hζ : ζ ^ n = 1) (hζ1 : ζ != 1)
  结论: ζ - 1 ∣ (n : A)
  证明: by
  have key : (n : A) = ∑ i in range n, (1 - ζ ^ i) := by
    have hgs : ∑ i in range n, ζ ^ i = 0 := by
      have := geom_sum_mul ζ n
      rw [hζ]; rw [sub_self] at this
      exact (mul_eq_zero.1 this).resolve_right fun h => hζ1 (sub_eq_zero.1 h)
    rw [Finset.sum_sub_distrib]; rw [hgs]; rw [

Depends on / 依赖: Finset, Finset.dvd_sum, Finset.sum_const, Finset.sum_sub_distrib, card_range, dvd_neg, dvd_sum, geom_sum_mul, mul_eq_zero, mul_one, neg_sub, nsmul_eq_mul, resolve_right, sub_dvd_pow_sub_pow, sub_eq_zero, sub_self, sub_zero, sum_const, sum_sub_distrib
-/
theorem sub_one_dvd_natCast_of_pow_eq_one (hζ : ζ ^ n = 1) (hζ1 : ζ != 1) : ζ - 1 ∣ (n : A) := by
  have key : (n : A) = ∑ i in range n, (1 - ζ ^ i) := by
    have hgs : ∑ i in range n, ζ ^ i = 0 := by
      have := geom_sum_mul ζ n
      rw [hζ]; rw [sub_self] at this
      exact (mul_eq_zero.1 this).resolve_right fun h => hζ1 (sub_eq_zero.1 h)
    rw [Finset.sum_sub_distrib]; rw [hgs]; rw [sub_zero]; rw [Finset.sum_const]; rw [card_range]; rw [nsmul_eq_mul]; rw [mul_one]
  rw [key]
  refine Finset.dvd_sum fun i _ => ?_
  have h : ζ - 1 ∣ ζ ^ i - 1 := by simpa using sub_dvd_pow_sub_pow ζ 1 i
  rwa [← dvd_neg, neg_sub] at h

namespace IsPrimitiveRoot

/--
theorem `associated_sub_one_pow_sub_one_of_coprime` / 定理 `associated_sub_one_pow_sub_one_of_coprime`

English:
theorem associated_sub_one_pow_sub_one_of_coprime
  given: (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n)
  proof: by
  refine associated_of_dvd_dvd ⟨∑ i in range j, ζ ^ i, (mul_geom_sum _ _).symm⟩ ?_
  match n with
  | 0 => simp_all
  | 1 => simp_all
  | n + 2 =>
      obtain ⟨m, -, hm⟩ := exists_mul_mod_eq_one_of_coprime hj (by lia)
      use ∑ i in range m, (ζ ^ j) ^ i
      rw [mul_geom_sum]; rw [← pow_mul];

中文:
定理 associated_sub_one_pow_sub_one_of_coprime
  条件: (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n)
  证明: by
  refine associated_of_dvd_dvd ⟨∑ i in range j, ζ ^ i, (mul_geom_sum _ _).symm⟩ ?_
  match n with
  | 0 => simp_all
  | 1 => simp_all
  | n + 2 =>
      obtain ⟨m, -, hm⟩ := exists_mul_mod_eq_one_of_coprime hj (by lia)
      use ∑ i in range m, (ζ ^ j) ^ i
      rw [mul_geom_sum]; rw [← pow_mul];

Depends on / 依赖: associated_of_dvd_dvd, eq_orderOf, exists_mul_mod_eq_one_of_coprime, mul_geom_sum, pow_mod_orderOf, pow_mul, pow_one
-/
theorem associated_sub_one_pow_sub_one_of_coprime (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) :
    Associated (ζ - 1) (ζ ^ j - 1) := by
  refine associated_of_dvd_dvd ⟨∑ i in range j, ζ ^ i, (mul_geom_sum _ _).symm⟩ ?_
  match n with
  | 0 => simp_all
  | 1 => simp_all
  | n + 2 =>
      obtain ⟨m, -, hm⟩ := exists_mul_mod_eq_one_of_coprime hj (by lia)
      use ∑ i in range m, (ζ ^ j) ^ i
      rw [mul_geom_sum]; rw [← pow_mul]; rw [← pow_mod_orderOf]; rw [← hζ.eq_orderOf]; rw [hm]; rw [pow_one]

/--
theorem `associated_pow_sub_one_pow_of_coprime` / 定理 `associated_pow_sub_one_pow_of_coprime`

English:
theorem associated_pow_sub_one_pow_of_coprime
  statement: (hζ : IsPrimitiveRoot ζ n)
  proof: by
  suffices forall {j}, j.Coprime n -> Associated (ζ - 1) (ζ ^ j - 1) by
    grind [Associated.trans, Associated.symm]
  exact hζ.associated_sub_one_pow_sub_one_of_coprime

中文:
定理 associated_pow_sub_one_pow_of_coprime
  结论: (hζ : IsPrimitiveRoot ζ n)
  证明: by
  suffices forall {j}, j.Coprime n -> Associated (ζ - 1) (ζ ^ j - 1) by
    grind [Associated.trans, Associated.symm]
  exact hζ.associated_sub_one_pow_sub_one_of_coprime

Depends on / 依赖: Associated, Associated.symm, Associated.trans, Coprime, associated_sub_one_pow_sub_one_of_coprime, j.Coprime
-/
theorem associated_pow_sub_one_pow_of_coprime (hζ : IsPrimitiveRoot ζ n)
    (hi : i.Coprime n) (hj : j.Coprime n) : Associated (ζ ^ j - 1) (ζ ^ i - 1) := by
  suffices forall {j}, j.Coprime n -> Associated (ζ - 1) (ζ ^ j - 1) by
    grind [Associated.trans, Associated.symm]
  exact hζ.associated_sub_one_pow_sub_one_of_coprime

/--
theorem `associated_sub_one_map_sub_one` / 定理 `associated_sub_one_map_sub_one`

English:
theorem associated_sub_one_map_sub_one
  statement: {n : Nat} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
  proof: by
  rw [map_sub]; rw [map_one]; rw [← hζ.autToPow_spec R σ]
  apply hζ.associated_sub_one_pow_sub_one_of_coprime
  exact ZMod.val_coe_unit_coprime ((autToPow R hζ) σ)

中文:
定理 associated_sub_one_map_sub_one
  结论: {n : 自然数} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
  证明: by
  rw [map_sub]; rw [map_one]; rw [← hζ.autToPow_spec R σ]
  apply hζ.associated_sub_one_pow_sub_one_of_coprime
  exact ZMod.val_coe_unit_coprime ((autToPow R hζ) σ)

Depends on / 依赖: ZMod.val_coe_unit_coprime, associated_sub_one_pow_sub_one_of_coprime, autToPow, autToPow_spec, map_one, map_sub, val_coe_unit_coprime
-/
theorem associated_sub_one_map_sub_one {n : Nat} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    (σ : A ≃ₐ[R] A) : Associated (ζ - 1) (σ (ζ - 1)) := by
  rw [map_sub]; rw [map_one]; rw [← hζ.autToPow_spec R σ]
  apply hζ.associated_sub_one_pow_sub_one_of_coprime
  exact ZMod.val_coe_unit_coprime ((autToPow R hζ) σ)

/--
theorem `associated_map_sub_one_map_sub_one` / 定理 `associated_map_sub_one_map_sub_one`

English:
theorem associated_map_sub_one_map_sub_one
  statement: {n : Nat} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
  proof: by
  rw [map_sub]; rw [map_sub]; rw [map_one]; rw [map_one]; rw [← hζ.autToPow_spec R σ]; rw [← hζ.autToPow_spec R τ]
  apply hζ.associated_pow_sub_one_pow_of_coprime <;>
  exact ZMod.val_coe_unit_coprime ((autToPow R hζ) _)

中文:
定理 associated_map_sub_one_map_sub_one
  结论: {n : 自然数} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
  证明: by
  rw [map_sub]; rw [map_sub]; rw [map_one]; rw [map_one]; rw [← hζ.autToPow_spec R σ]; rw [← hζ.autToPow_spec R τ]
  apply hζ.associated_pow_sub_one_pow_of_coprime <;>
  exact ZMod.val_coe_unit_coprime ((autToPow R hζ) _)

Depends on / 依赖: ZMod.val_coe_unit_coprime, associated_pow_sub_one_pow_of_coprime, autToPow, autToPow_spec, map_one, map_sub, val_coe_unit_coprime
-/
theorem associated_map_sub_one_map_sub_one {n : Nat} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    (σ τ : A ≃ₐ[R] A) : Associated (σ (ζ - 1)) (τ (ζ - 1)) := by
  rw [map_sub]; rw [map_sub]; rw [map_one]; rw [map_one]; rw [← hζ.autToPow_spec R σ]; rw [← hζ.autToPow_spec R τ]
  apply hζ.associated_pow_sub_one_pow_of_coprime <;>
  exact ZMod.val_coe_unit_coprime ((autToPow R hζ) _)

/--
theorem `geom_sum_isUnit` / 定理 `geom_sum_isUnit`

English:
theorem geom_sum_isUnit
  given: (hζ : IsPrimitiveRoot ζ n) (hn : 2 <= n) (hj : j.Coprime n)
  proof: by
  obtain ⟨u, hu⟩ := hζ.associated_pow_sub_one_pow_of_coprime hj (coprime_one_left n)
  convert! u.isUnit
  apply mul_right_injective₀ (show 1 - ζ != 0 by grind [sub_one_ne_zero])
  grind [mul_neg_geom_sum]

中文:
定理 geom_sum_isUnit
  条件: (hζ : IsPrimitiveRoot ζ n) (hn : 2 <= n) (hj : j.Coprime n)
  证明: by
  obtain ⟨u, hu⟩ := hζ.associated_pow_sub_one_pow_of_coprime hj (coprime_one_left n)
  convert! u.isUnit
  apply mul_right_injective₀ (show 1 - ζ != 0 by grind [sub_one_ne_zero])
  grind [mul_neg_geom_sum]

Depends on / 依赖: associated_pow_sub_one_pow_of_coprime, convert, coprime_one_left, isUnit, mul_neg_geom_sum, sub_one_ne_zero, u.isUnit
-/
theorem geom_sum_isUnit (hζ : IsPrimitiveRoot ζ n) (hn : 2 <= n) (hj : j.Coprime n) :
    IsUnit (∑ i in range j, ζ ^ i) := by
  obtain ⟨u, hu⟩ := hζ.associated_pow_sub_one_pow_of_coprime hj (coprime_one_left n)
  convert! u.isUnit
  apply mul_right_injective₀ (show 1 - ζ != 0 by grind [sub_one_ne_zero])
  grind [mul_neg_geom_sum]

/--
theorem `geom_sum_isUnit'` / 定理 `geom_sum_isUnit'`

English:
theorem geom_sum_isUnit'
  given: (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) (hj_Unit : IsUnit (j : A))
  proof: by
  match n with
  | 0 => simp_all
  | 1 => simp_all
  | n + 2 => exact geom_sum_isUnit hζ (by linarith) hj

中文:
定理 geom_sum_isUnit'
  条件: (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) (hj_Unit : IsUnit (j : A))
  证明: by
  match n with
  | 0 => simp_all
  | 1 => simp_all
  | n + 2 => exact geom_sum_isUnit hζ (by linarith) hj

Depends on / 依赖: geom_sum_isUnit
-/
theorem geom_sum_isUnit' (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) (hj_Unit : IsUnit (j : A)) :
    IsUnit (∑ i in range j, ζ ^ i) := by
  match n with
  | 0 => simp_all
  | 1 => simp_all
  | n + 2 => exact geom_sum_isUnit hζ (by linarith) hj

/--
theorem `pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one` / 定理 `pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one`

English:
theorem pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one
  statement: (hζ : IsPrimitiveRoot ζ n)
  proof: by
  grind [IsUnit.mul_val_inv, pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum, IsUnit.unit_spec]

中文:
定理 pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one
  结论: (hζ : IsPrimitiveRoot ζ n)
  证明: by
  grind [IsUnit.mul_val_inv, pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum, IsUnit.unit_spec]

Depends on / 依赖: IsUnit, IsUnit.mul_val_inv, IsUnit.unit_spec, mul_val_inv, pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum, unit_spec
-/
theorem pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one (hζ : IsPrimitiveRoot ζ n)
    (hn : 2 <= n) (hi : i.Coprime n) (hj : j.Coprime n) :
    (ζ ^ j - 1) =
      (hζ.geom_sum_isUnit hn hj).unit * (hζ.geom_sum_isUnit hn hi).unit⁻¹ * (ζ ^ i - 1) := by
  grind [IsUnit.mul_val_inv, pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum, IsUnit.unit_spec]

/--
theorem `associated_pow_add_sub_sub_one` / 定理 `associated_pow_add_sub_sub_one`

English:
theorem associated_pow_add_sub_sub_one
  statement: (hζ : IsPrimitiveRoot ζ n) (hn : 2 <= n) (i : Nat)
  proof: by
  use (hζ.isUnit (by lia)).unit ^ i * (hζ.geom_sum_isUnit hn hjn).unit
  suffices (ζ - 1) * ζ ^ i * ∑ i in range j, ζ ^ i = (ζ ^ (i + j) - ζ ^ i) by
    simp [← this, mul_assoc]
  grind [mul_geom_sum]

中文:
定理 associated_pow_add_sub_sub_one
  结论: (hζ : IsPrimitiveRoot ζ n) (hn : 2 <= n) (i : 自然数)
  证明: by
  use (hζ.isUnit (by lia)).unit ^ i * (hζ.geom_sum_isUnit hn hjn).unit
  suffices (ζ - 1) * ζ ^ i * ∑ i in range j, ζ ^ i = (ζ ^ (i + j) - ζ ^ i) by
    simp [← this, mul_assoc]
  grind [mul_geom_sum]

Depends on / 依赖: geom_sum_isUnit, isUnit, mul_assoc, mul_geom_sum
-/
theorem associated_pow_add_sub_sub_one (hζ : IsPrimitiveRoot ζ n) (hn : 2 <= n) (i : Nat)
    (hjn : j.Coprime n) : Associated (ζ - 1) (ζ ^ (i + j) - ζ ^ i) := by
  use (hζ.isUnit (by lia)).unit ^ i * (hζ.geom_sum_isUnit hn hjn).unit
  suffices (ζ - 1) * ζ ^ i * ∑ i in range j, ζ ^ i = (ζ ^ (i + j) - ζ ^ i) by
    simp [← this, mul_assoc]
  grind [mul_geom_sum]

/--
lemma `nthRootsFinset_pairwise_associated_sub_one_sub_of_prime` / 引理 `nthRootsFinset_pairwise_associated_sub_one_sub_of_prime`

English:
lemma nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
  statement: (hζ : IsPrimitiveRoot ζ p)
  proof: by
  intro η₁ hη₁ η₂ hη₂ e
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₁)
  obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₂)
  wlog hij : j <= i
  · simpa using (this h

中文:
引理 nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
  结论: (hζ : IsPrimitiveRoot ζ p)
  证明: by
  intro η₁ hη₁ η₂ hη₂ e
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₁)
  obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₂)
  wlog hij : j <= i
  · simpa using (this h

Depends on / 依赖: Coprime, NeZero, Polynomial, Polynomial.mem_nthRootsFinset, associated_pow_add_sub_sub_one, coprime_of_lt_prime, e.symm, eq_pow_of_pow_eq_one, hp.ne_zero, hp.pos, hp.two_le, mem_nthRootsFinset, ne_zero, neg_right, two_le
-/
lemma nthRootsFinset_pairwise_associated_sub_one_sub_of_prime (hζ : IsPrimitiveRoot ζ p)
    (hp : p.Prime) :
    Set.Pairwise (nthRootsFinset p (1 : A)) fun η₁ η₂ => Associated (ζ - 1) (η₁ - η₂) := by
  intro η₁ hη₁ η₂ hη₂ e
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₁)
  obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₂)
  wlog hij : j <= i
  · simpa using (this hζ ‹_› ‹_› _ hj ‹_› _ hi ‹_› e.symm (by lia)).neg_right
  have H : (i - j).Coprime p := (coprime_of_lt_prime (by grind) (by grind) hp).symm
  obtain ⟨u, h⟩ := hζ.associated_pow_add_sub_sub_one hp.two_le j H
  simp only [hij, add_tsub_cancel_of_le] at h
  rw [← h]; rw [associated_mul_unit_right_iff]

@[deprecated (since := "2026-06-23")]
alias ntRootsFinset_pairwise_associated_sub_one_sub_of_prime :=
  nthRootsFinset_pairwise_associated_sub_one_sub_of_prime

/--
lemma `sub_one_dvd_sub` / 引理 `sub_one_dvd_sub`

English:
lemma sub_one_dvd_sub
  statement: (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
  proof: by
  rcases eq_or_ne η₁ η₂ with rfl | h
  · simp
  · exact (hζ.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hp hη₁ hη₂ h).dvd

中文:
引理 sub_one_dvd_sub
  结论: (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
  证明: by
  rcases eq_or_ne η₁ η₂ with rfl | h
  · simp
  · exact (hζ.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hp hη₁ hη₂ h).dvd

Depends on / 依赖: eq_or_ne, nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
-/
lemma sub_one_dvd_sub (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
    {η₁ : A} (hη₁ : η₁ in nthRootsFinset p (1 : A))
    {η₂ : A} (hη₂ : η₂ in nthRootsFinset p (1 : A)) :
    ζ - 1 ∣ η₁ - η₂ := by
  rcases eq_or_ne η₁ η₂ with rfl | h
  · simp
  · exact (hζ.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hp hη₁ hη₂ h).dvd

/--
theorem `sub_one_dvd_natCast` / 定理 `sub_one_dvd_natCast`

English:
theorem sub_one_dvd_natCast
  given: (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n)
  statement: ζ - 1 ∣ (n : A)
  proof: sub_one_dvd_natCast_of_pow_eq_one hζ.pow_eq_one (hζ.ne_one hn)

中文:
定理 sub_one_dvd_natCast
  条件: (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n)
  结论: ζ - 1 ∣ (n : A)
  证明: sub_one_dvd_natCast_of_pow_eq_one hζ.pow_eq_one (hζ.ne_one hn)

Depends on / 依赖: ne_one, pow_eq_one, sub_one_dvd_natCast_of_pow_eq_one
-/
theorem sub_one_dvd_natCast (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) : ζ - 1 ∣ (n : A) :=
  sub_one_dvd_natCast_of_pow_eq_one hζ.pow_eq_one (hζ.ne_one hn)

end IsPrimitiveRoot
