/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# Ideals in cyclotomic fields

In this file, we prove results about ideals in cyclotomic extensions of `ℚ`.

## Main results

* `IsCyclotomicExtension.Rat.ncard_primesOver_of_prime_pow`: there is only one prime ideal above
  the prime `p` in `ℚ(ζ_pᵏ)`

* `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime_pow`: the residual degree of the prime ideal
  above `p` in `ℚ(ζ_pᵏ)` is `1`.

* `IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow`: the ramification index of the prime
  ideal above `p` in `ℚ(ζ_pᵏ)` is `p ^ (k - 1) * (p - 1)`.

* `IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd`: if the prime `p` does not divide `m`, then
  the inertia degree of `p` in `ℚ(ζₘ)` is the order of `p` modulo `m`.

* `IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd`: if the prime `p` does not divide `m`,
  then the ramification index of `p` in `ℚ(ζₘ)` is `1`.

* `IsCyclotomicExtension.Rat.inertiaDegIn_eq`: write `n = p ^ (k + 1) * m` where the prime `p` does
  not divide `m`, then the inertia degree of `p` in `ℚ(ζₙ)` is the order of `p` modulo `m`.

* `IsCyclotomicExtension.Rat.ramificationIdxIn_eq`: write `n = p ^ (k + 1) * m` where the prime `p`
  does not divide `m`, then the ramification index of `p` in `ℚ(ζₙ)` is `p ^ k * (p - 1)`.

-/

public section

namespace IsCyclotomicExtension.Rat

open Ideal NumberField RingOfIntegers

variable (n m p k : Nat) [hp : Fact (Nat.Prime p)] (K : Type*) [Field K] [NumberField K]
  (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver (span {(p : Int)})]

local notation3 "𝒑" => (span {(p : Int)})

section PrimePow

variable {K} [hK : IsCyclotomicExtension {p ^ (k + 1)} Rat K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))

/--
Instance `isPrime_span_zeta_sub_one` / 实例 `isPrime_span_zeta_sub_one`

English:
instance isPrime_span_zeta_sub_one
  signature: : IsPrime (span {hζ.toInteger - 1})
  body: by
  rw [span_singleton_prime]
  · exact hζ.zeta_sub_one_prime
  · exact Prime.ne_zero hζ.zeta_sub_one_prime

中文:
实例 isPrime_span_zeta_sub_one
  签名: : 是素 (span {hζ.to整数eger - 1})
  定义体: by
  rw [span_singleton_prime]
  · exact hζ.zeta_sub_one_prime
  · exact Prime.ne_zero hζ.zeta_sub_one_prime

Depends on / 依赖: Prime.ne_zero, ne_zero, span_singleton_prime, zeta_sub_one_prime
-/
instance isPrime_span_zeta_sub_one : IsPrime (span {hζ.toInteger - 1}) := by
  rw [span_singleton_prime]
  · exact hζ.zeta_sub_one_prime
  · exact Prime.ne_zero hζ.zeta_sub_one_prime

/--
theorem `associated_norm_zeta_sub_one` / 定理 `associated_norm_zeta_sub_one`

English:
theorem associated_norm_zeta_sub_one
  statement: Associated (Algebra.norm Int (hζ.toInteger - 1)) (p : Int)
  proof: by
  by_cases h : p = 2
  · cases k with
    | zero =>
      rw [h]; rw [zero_add]; rw [pow_one] at hK hζ
      rw [hζ.norm_toInteger_sub_one_of_eq_two]; rw [h]; rw [Int.ofNat_two]; rw [Associated.neg_left_iff]
    | succ n =>
      rw [h]; rw [add_assoc]; rw [one_add_one_eq_two] at hK hζ
      rw [

中文:
定理 associated_norm_zeta_sub_one
  结论: Associated (代数.norm 整数 (hζ.to整数eger - 1)) (p : 整数)
  证明: by
  by_cases h : p = 2
  · cases k with
    | zero =>
      rw [h]; rw [zero_add]; rw [pow_one] at hK hζ
      rw [hζ.norm_toInteger_sub_one_of_eq_two]; rw [h]; rw [Int.ofNat_two]; rw [Associated.neg_left_iff]
    | succ n =>
      rw [h]; rw [add_assoc]; rw [one_add_one_eq_two] at hK hζ
      rw [

Depends on / 依赖: Associated, Associated.neg_left_iff, Int.ofNat_two, add_assoc, neg_left_iff, norm_toInteger_sub_one_of_eq_two, norm_toInteger_sub_one_of_eq_two_pow, norm_toInteger_sub_one_of_prime_ne_two, ofNat_two, one_add_one_eq_two, pow_one, zero_add
-/
theorem associated_norm_zeta_sub_one : Associated (Algebra.norm Int (hζ.toInteger - 1)) (p : Int) := by
  by_cases h : p = 2
  · cases k with
    | zero =>
      rw [h]; rw [zero_add]; rw [pow_one] at hK hζ
      rw [hζ.norm_toInteger_sub_one_of_eq_two]; rw [h]; rw [Int.ofNat_two]; rw [Associated.neg_left_iff]
    | succ n =>
      rw [h]; rw [add_assoc]; rw [one_add_one_eq_two] at hK hζ
      rw [hζ.norm_toInteger_sub_one_of_eq_two_pow]; rw [h]; rw [Int.ofNat_two]
  · rw [hζ.norm_toInteger_sub_one_of_prime_ne_two h]

/--
theorem `zeta_sub_one_dvd_intCast_iff` / 定理 `zeta_sub_one_dvd_intCast_iff`

English:
theorem zeta_sub_one_dvd_intCast_iff
  given: {n : Int}
  proof: by
  have h := associated_norm_zeta_sub_one p k hζ
  rw [← Ideal.norm_dvd_iff (h.symm.prime (Nat.prime_iff_prime_int.mp hp.out))]
  exact h.dvd_iff_dvd_left

中文:
定理 zeta_sub_one_dvd_intCast_iff
  条件: {n : 整数}
  证明: by
  have h := associated_norm_zeta_sub_one p k hζ
  rw [← Ideal.norm_dvd_iff (h.symm.prime (Nat.prime_iff_prime_int.mp hp.out))]
  exact h.dvd_iff_dvd_left

Depends on / 依赖: Ideal.norm_dvd_iff, Nat.prime_iff_prime_int.mp, associated_norm_zeta_sub_one, dvd_iff_dvd_left, h.dvd_iff_dvd_left, h.symm.prime, hp.out, norm_dvd_iff, prime_iff_prime_int
-/
theorem zeta_sub_one_dvd_intCast_iff {n : Int} :
    hζ.toInteger - 1 ∣ (n : 𝓞 K) ↔ (p : Int) ∣ n := by
  have h := associated_norm_zeta_sub_one p k hζ
  rw [← Ideal.norm_dvd_iff (h.symm.prime (Nat.prime_iff_prime_int.mp hp.out))]
  exact h.dvd_iff_dvd_left

/--
theorem `absNorm_span_zeta_sub_one` / 定理 `absNorm_span_zeta_sub_one`

English:
theorem absNorm_span_zeta_sub_one
  statement: absNorm (span {hζ.toInteger - 1}) = p
  proof: by
simpa using congr_arg absNorm
span_singleton_eq_span_singleton.mpr associated_norm_zeta_sub_one p k hζ

中文:
定理 absNorm_span_zeta_sub_one
  结论: absNorm (span {hζ.to整数eger - 1}) = p
  证明: by
simpa using congr_arg absNorm
span_singleton_eq_span_singleton.mpr associated_norm_zeta_sub_one p k hζ

Depends on / 依赖: absNorm, associated_norm_zeta_sub_one, congr_arg, span_singleton_eq_span_singleton, span_singleton_eq_span_singleton.mpr
-/
theorem absNorm_span_zeta_sub_one : absNorm (span {hζ.toInteger - 1}) = p := by
simpa using congr_arg absNorm
span_singleton_eq_span_singleton.mpr associated_norm_zeta_sub_one p k hζ

/--
theorem `p_mem_span_zeta_sub_one` / 定理 `p_mem_span_zeta_sub_one`

English:
theorem p_mem_span_zeta_sub_one
  statement: (p : 𝓞 K) in span {hζ.toInteger - 1}
  proof: by
  convert! absNorm_mem _
  exact (absNorm_span_zeta_sub_one ..).symm

中文:
定理 p_mem_span_zeta_sub_one
  结论: (p : 𝓞 K) in span {hζ.to整数eger - 1}
  证明: by
  convert! absNorm_mem _
  exact (absNorm_span_zeta_sub_one ..).symm

Depends on / 依赖: absNorm_mem, absNorm_span_zeta_sub_one, convert
-/
theorem p_mem_span_zeta_sub_one : (p : 𝓞 K) in span {hζ.toInteger - 1} := by
  convert! absNorm_mem _
  exact (absNorm_span_zeta_sub_one ..).symm

/--
theorem `span_zeta_sub_one_ne_bot` / 定理 `span_zeta_sub_one_ne_bot`

English:
theorem span_zeta_sub_one_ne_bot
  statement: span {hζ.toInteger - 1} != ⊥
  proof: (Submodule.ne_bot_iff _).mpr ⟨p, p_mem_span_zeta_sub_one p k hζ, NeZero.natCast_ne p (𝓞 K)⟩

中文:
定理 span_zeta_sub_one_ne_bot
  结论: span {hζ.to整数eger - 1} != ⊥
  证明: (Submodule.ne_bot_iff _).mpr ⟨p, p_mem_span_zeta_sub_one p k hζ, NeZero.natCast_ne p (𝓞 K)⟩

Depends on / 依赖: NeZero, NeZero.natCast_ne, Submodule, Submodule.ne_bot_iff, natCast_ne, ne_bot_iff, p_mem_span_zeta_sub_one
-/
theorem span_zeta_sub_one_ne_bot : span {hζ.toInteger - 1} != ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨p, p_mem_span_zeta_sub_one p k hζ, NeZero.natCast_ne p (𝓞 K)⟩

/--
Instance `liesOver_span_zeta_sub_one` / 实例 `liesOver_span_zeta_sub_one`

English:
instance liesOver_span_zeta_sub_one
  signature: : (span {hζ.toInteger - 1}).LiesOver 𝒑
  body: by
  rw [liesOver_iff]
  refine IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p) IsPrime.ne_top' ?_
  rw [span_singleton_le_iff_mem]; rw [mem_comap]; rw [algebraMap_int_eq]; rw [map_natCast]
  exact p_mem_span_zeta_sub_one p k hζ

中文:
实例 liesOver_span_zeta_sub_one
  签名: : (span {hζ.to整数eger - 1}).LiesOver 𝒑
  定义体: by
  rw [liesOver_iff]
  refine IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p) IsPrime.ne_top' ?_
  rw [span_singleton_le_iff_mem]; rw [mem_comap]; rw [algebraMap_int_eq]; rw [map_natCast]
  exact p_mem_span_zeta_sub_one p k hζ

Depends on / 依赖: Int.ideal_span_isMaximal_of_prime, IsMaximal, IsMaximal.eq_of_le, IsPrime, IsPrime.ne_top, algebraMap_int_eq, eq_of_le, ideal_span_isMaximal_of_prime, liesOver_iff, map_natCast, mem_comap, ne_top, p_mem_span_zeta_sub_one, span_singleton_le_iff_mem
-/
instance liesOver_span_zeta_sub_one : (span {hζ.toInteger - 1}).LiesOver 𝒑 := by
  rw [liesOver_iff]
  refine IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p) IsPrime.ne_top' ?_
  rw [span_singleton_le_iff_mem]; rw [mem_comap]; rw [algebraMap_int_eq]; rw [map_natCast]
  exact p_mem_span_zeta_sub_one p k hζ

/--
theorem `inertiaDeg_span_zeta_sub_one` / 定理 `inertiaDeg_span_zeta_sub_one`

English:
theorem inertiaDeg_span_zeta_sub_one
  statement: inertiaDeg (span {hζ.toInteger - 1}) Int = 1
  proof: by
  have : IsMaximal (span {hζ.toInteger - 1}) := .of_liesOver_isMaximal _ 𝒑
  rw [← Nat.pow_right_inj hp.out.one_lt]; rw [pow_one]; rw [pow_inertiaDeg]; rw [absNorm_span_zeta_sub_one]

中文:
定理 inertiaDeg_span_zeta_sub_one
  结论: inertiaDeg (span {hζ.to整数eger - 1}) 整数 = 1
  证明: by
  have : IsMaximal (span {hζ.toInteger - 1}) := .of_liesOver_isMaximal _ 𝒑
  rw [← Nat.pow_right_inj hp.out.one_lt]; rw [pow_one]; rw [pow_inertiaDeg]; rw [absNorm_span_zeta_sub_one]

Depends on / 依赖: IsMaximal, Nat.pow_right_inj, absNorm_span_zeta_sub_one, hp.out.one_lt, of_liesOver_isMaximal, one_lt, pow_inertiaDeg, pow_one, pow_right_inj, toInteger
-/
theorem inertiaDeg_span_zeta_sub_one : inertiaDeg (span {hζ.toInteger - 1}) Int = 1 := by
  have : IsMaximal (span {hζ.toInteger - 1}) := .of_liesOver_isMaximal _ 𝒑
  rw [← Nat.pow_right_inj hp.out.one_lt]; rw [pow_one]; rw [pow_inertiaDeg]; rw [absNorm_span_zeta_sub_one]

attribute [local instance] FractionRing.liftAlgebra in
/--
theorem `map_eq_span_zeta_sub_one_pow` / 定理 `map_eq_span_zeta_sub_one_pow`

English:
theorem map_eq_span_zeta_sub_one_pow
  proof: by
  have : IsGalois Rat K := isGalois {p ^ (k + 1)} Rat K
  have : IsGalois (FractionRing Int) (FractionRing (𝓞 K)) := by
    refine IsGalois.of_equiv_equiv (f := (FractionRing.algEquiv Int Rat).toRingEquiv.symm)
(g := (FractionRing.algEquiv (𝓞 K) K).toRingEquiv.symm)
        RingHom.ext fun x => I

中文:
定理 map_eq_span_zeta_sub_one_pow
  证明: by
  have : IsGalois Rat K := isGalois {p ^ (k + 1)} Rat K
  have : IsGalois (FractionRing Int) (FractionRing (𝓞 K)) := by
    refine IsGalois.of_equiv_equiv (f := (FractionRing.algEquiv Int Rat).toRingEquiv.symm)
(g := (FractionRing.algEquiv (𝓞 K) K).toRingEquiv.symm)
        RingHom.ext fun x => I

Depends on / 依赖: FractionRing, FractionRing.algEquiv, IsFractionRing, IsFractionRing.algEquiv_commutes, IsGalois, IsGalois.of_equiv_equiv, RingHom, RingHom.ext, Set.image_singleton, algEquiv, algEquiv_commutes, associated_norm_zeta_sub, image_singleton, isGalois, map_span, of_equiv_equiv, span_singleton_eq_span_singleton, span_singleton_eq_span_singleton.mpr, toRingEquiv, toRingEquiv.symm
-/
theorem map_eq_span_zeta_sub_one_pow :
    (map (algebraMap Int (𝓞 K)) 𝒑) = span {hζ.toInteger - 1} ^ Module.finrank Rat K := by
  have : IsGalois Rat K := isGalois {p ^ (k + 1)} Rat K
  have : IsGalois (FractionRing Int) (FractionRing (𝓞 K)) := by
    refine IsGalois.of_equiv_equiv (f := (FractionRing.algEquiv Int Rat).toRingEquiv.symm)
(g := (FractionRing.algEquiv (𝓞 K) K).toRingEquiv.symm)
        RingHom.ext fun x => IsFractionRing.algEquiv_commutes (FractionRing.algEquiv Int Rat).symm
          (FractionRing.algEquiv (𝓞 K) K).symm _
  rw [map_span]; rw [Set.image_singleton]; rw [span_singleton_eq_span_singleton.mpr
    ((associated_norm_zeta_sub_one p k hζ).symm.map (algebraMap Int (𝓞 K)))]; rw [← Algebra.intNorm_eq_norm]; rw [Algebra.algebraMap_intNorm_of_isGalois]; rw [← prod_span_singleton]
  conv_lhs =>
    enter [2, σ]
    rw [span_singleton_eq_span_singleton.mpr
      (hζ.toInteger_isPrimitiveRoot.associated_sub_one_map_sub_one σ).symm]
  rw [Finset.prod_const]; rw [Finset.card_univ]; rw [← Fintype.card_congr (galRestrict Int Rat K (𝓞 K)).toEquiv]; rw [← Nat.card_eq_fintype_card]; rw [IsGalois.card_aut_eq_finrank]

/--
theorem `ramificationIdx_span_zeta_sub_one` / 定理 `ramificationIdx_span_zeta_sub_one`

English:
theorem ramificationIdx_span_zeta_sub_one
  proof: by
  have h := isPrime_span_zeta_sub_one p k hζ
  have hp0 : 𝒑 != ⊥ := by simpa using hp.out.ne_zero
  rw [← Nat.totient_prime_pow_succ hp.out]; rw [← finrank _ K]; rw [IsDedekindDomain.ramificationIdx_eq_multiplicity 𝒑]; rw [map_eq_span_zeta_sub_one_pow p k hζ]; rw [multiplicity_pow_self (span_zeta

中文:
定理 ramificationIdx_span_zeta_sub_one
  证明: by
  have h := isPrime_span_zeta_sub_one p k hζ
  have hp0 : 𝒑 != ⊥ := by simpa using hp.out.ne_zero
  rw [← Nat.totient_prime_pow_succ hp.out]; rw [← finrank _ K]; rw [IsDedekindDomain.ramificationIdx_eq_multiplicity 𝒑]; rw [map_eq_span_zeta_sub_one_pow p k hζ]; rw [multiplicity_pow_self (span_zeta

Depends on / 依赖: IsDedekindDomain, IsDedekindDomain.ramificationIdx_eq_multiplicity, Nat.totient_prime_pow_succ, finrank, h.ne_top, hp.out, hp.out.ne_zero, isPrime_span_zeta_sub_one, isUnit_iff, isUnit_iff.not.mpr, map_eq_span_zeta_sub_one_pow, map_ne_bot_of_ne_bot, multiplicity_pow_self, ne_top, ne_zero, ramificationIdx_eq_multiplicity, span_zeta_sub_one_ne_bot, totient_prime_pow_succ
-/
theorem ramificationIdx_span_zeta_sub_one :
    ramificationIdx (span {hζ.toInteger - 1}) Int = p ^ k * (p - 1) := by
  have h := isPrime_span_zeta_sub_one p k hζ
  have hp0 : 𝒑 != ⊥ := by simpa using hp.out.ne_zero
  rw [← Nat.totient_prime_pow_succ hp.out]; rw [← finrank _ K]; rw [IsDedekindDomain.ramificationIdx_eq_multiplicity 𝒑]; rw [map_eq_span_zeta_sub_one_pow p k hζ]; rw [multiplicity_pow_self (span_zeta_sub_one_ne_bot p k hζ) (isUnit_iff.not.mpr h.ne_top)]
  exact map_ne_bot_of_ne_bot hp0

variable (K)

include hK in
/--
theorem `ncard_primesOver_of_prime_pow` / 定理 `ncard_primesOver_of_prime_pow`

English:
theorem ncard_primesOver_of_prime_pow
  proof: by
  have : IsGalois Rat K := isGalois {p ^ (k + 1)} Rat K
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 K) Gal(K/Rat)
  have hζ := hK.zeta_spec
  have := liesOver_span_zeta_sub_one p k hζ
  rwa [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hζ.toInteger - 1}) Gal(K/R

中文:
定理 ncard_primesOver_of_prime_pow
  证明: by
  have : IsGalois Rat K := isGalois {p ^ (k + 1)} Rat K
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 K) Gal(K/Rat)
  have hζ := hK.zeta_spec
  have := liesOver_span_zeta_sub_one p k hζ
  rwa [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hζ.toInteger - 1}) Gal(K/R

Depends on / 依赖: IsGalois, IsGaloisGrou, Nat.totient_prime_pow_succ, finrank, hK.zeta_spec, h_main, hp.out, inertiaDegIn_eq_inertiaDeg, inertiaDeg_span_zeta_sub_one, isGalois, liesOver_span_zeta_sub_one, mul_one, ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn, ramificationIdxIn_eq_ramificationIdx, ramificationIdx_span_zeta_sub_one, toInteger, totient_prime_pow_succ, zeta_spec
-/
theorem ncard_primesOver_of_prime_pow :
    (primesOver 𝒑 (𝓞 K)).ncard = 1 := by
  have : IsGalois Rat K := isGalois {p ^ (k + 1)} Rat K
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 K) Gal(K/Rat)
  have hζ := hK.zeta_spec
  have := liesOver_span_zeta_sub_one p k hζ
  rwa [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hζ.toInteger - 1}) Gal(K/Rat),
    inertiaDegIn_eq_inertiaDeg 𝒑 (span {hζ.toInteger - 1}) Gal(K/Rat),
    inertiaDeg_span_zeta_sub_one,
    ramificationIdx_span_zeta_sub_one, mul_one, ← Nat.totient_prime_pow_succ hp.out,
    ← finrank _ K, IsGaloisGroup.card_eq_finrank Gal(K/Rat) Rat K, Nat.mul_eq_right] at h_main
  exact Module.finrank_pos.ne'

/--
theorem `eq_span_zeta_sub_one_of_liesOver` / 定理 `eq_span_zeta_sub_one_of_liesOver`

English:
theorem eq_span_zeta_sub_one_of_liesOver
  given: (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑]
  proof: by
  have : P in primesOver 𝒑 (𝓞 K) := ⟨hP₁, hP₂⟩
  have : span {hζ.toInteger - 1} in primesOver 𝒑 (𝓞 K) :=
    ⟨isPrime_span_zeta_sub_one p k hζ, liesOver_span_zeta_sub_one p k hζ⟩
  have := ncard_primesOver_of_prime_pow p k K
  aesop

include hK in

中文:
定理 eq_span_zeta_sub_one_of_liesOver
  条件: (P : 理想 (𝓞 K)) [hP₁ : P.是素] [hP₂ : P.LiesOver 𝒑]
  证明: by
  have : P in primesOver 𝒑 (𝓞 K) := ⟨hP₁, hP₂⟩
  have : span {hζ.toInteger - 1} in primesOver 𝒑 (𝓞 K) :=
    ⟨isPrime_span_zeta_sub_one p k hζ, liesOver_span_zeta_sub_one p k hζ⟩
  have := ncard_primesOver_of_prime_pow p k K
  aesop

include hK in

Depends on / 依赖: isPrime_span_zeta_sub_one, liesOver_span_zeta_sub_one, ncard_primesOver_of_prime_pow, primesOver, toInteger
-/
theorem eq_span_zeta_sub_one_of_liesOver (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    P = span {hζ.toInteger - 1} := by
  have : P in primesOver 𝒑 (𝓞 K) := ⟨hP₁, hP₂⟩
  have : span {hζ.toInteger - 1} in primesOver 𝒑 (𝓞 K) :=
    ⟨isPrime_span_zeta_sub_one p k hζ, liesOver_span_zeta_sub_one p k hζ⟩
  have := ncard_primesOver_of_prime_pow p k K
  aesop

include hK in
/--
theorem `inertiaDeg_eq_of_prime_pow` / 定理 `inertiaDeg_eq_of_prime_pow`

English:
theorem inertiaDeg_eq_of_prime_pow
  given: (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑]
  proof: by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P]; rw [inertiaDeg_span_zeta_sub_one]

include hK in

中文:
定理 inertiaDeg_eq_of_prime_pow
  条件: (P : 理想 (𝓞 K)) [hP₁ : P.是素] [hP₂ : P.LiesOver 𝒑]
  证明: by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P]; rw [inertiaDeg_span_zeta_sub_one]

include hK in

Depends on / 依赖: eq_span_zeta_sub_one_of_liesOver, hK.zeta_spec, inertiaDeg_span_zeta_sub_one, zeta_spec
-/
theorem inertiaDeg_eq_of_prime_pow (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    inertiaDeg P Int = 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P]; rw [inertiaDeg_span_zeta_sub_one]

include hK in
/--
theorem `ramificationIdx_eq_of_prime_pow` / 定理 `ramificationIdx_eq_of_prime_pow`

English:
theorem ramificationIdx_eq_of_prime_pow
  given: (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑]
  proof: by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P]; rw [ramificationIdx_span_zeta_sub_one]

include hK in

中文:
定理 ramificationIdx_eq_of_prime_pow
  条件: (P : 理想 (𝓞 K)) [hP₁ : P.是素] [hP₂ : P.LiesOver 𝒑]
  证明: by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P]; rw [ramificationIdx_span_zeta_sub_one]

include hK in

Depends on / 依赖: eq_span_zeta_sub_one_of_liesOver, hK.zeta_spec, ramificationIdx_span_zeta_sub_one, zeta_spec
-/
theorem ramificationIdx_eq_of_prime_pow (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    ramificationIdx P Int = p ^ k * (p - 1) := by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P]; rw [ramificationIdx_span_zeta_sub_one]

include hK in
/--
theorem `inertiaDegIn_eq_of_prime_pow` / 定理 `inertiaDegIn_eq_of_prime_pow`

English:
theorem inertiaDegIn_eq_of_prime_pow
  proof: by
  have : IsGalois Rat K := isGalois {p ^ (k + 1)} Rat K
  rw [inertiaDegIn_eq_inertiaDeg 𝒑 (span {hK.zeta_spec.toInteger - 1}) Gal(K/Rat)]; rw [inertiaDeg_span_zeta_sub_one]

include hK in

中文:
定理 inertiaDegIn_eq_of_prime_pow
  证明: by
  have : IsGalois Rat K := isGalois {p ^ (k + 1)} Rat K
  rw [inertiaDegIn_eq_inertiaDeg 𝒑 (span {hK.zeta_spec.toInteger - 1}) Gal(K/Rat)]; rw [inertiaDeg_span_zeta_sub_one]

include hK in

Depends on / 依赖: IsGalois, hK.zeta_spec.toInteger, inertiaDegIn_eq_inertiaDeg, inertiaDeg_span_zeta_sub_one, isGalois, toInteger, zeta_spec
-/
theorem inertiaDegIn_eq_of_prime_pow :
    𝒑.inertiaDegIn (𝓞 K) = 1 := by
  have : IsGalois Rat K := isGalois {p ^ (k + 1)} Rat K
  rw [inertiaDegIn_eq_inertiaDeg 𝒑 (span {hK.zeta_spec.toInteger - 1}) Gal(K/Rat)]; rw [inertiaDeg_span_zeta_sub_one]

include hK in
/--
theorem `ramificationIdxIn_eq_of_prime_pow` / 定理 `ramificationIdxIn_eq_of_prime_pow`

English:
theorem ramificationIdxIn_eq_of_prime_pow
  proof: by
  have : IsGalois Rat K := isGalois {p ^ (k + 1)} Rat K
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hK.zeta_spec.toInteger - 1}) Gal(K/Rat)]; rw [ramificationIdx_span_zeta_sub_one]

中文:
定理 ramificationIdxIn_eq_of_prime_pow
  证明: by
  have : IsGalois Rat K := isGalois {p ^ (k + 1)} Rat K
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hK.zeta_spec.toInteger - 1}) Gal(K/Rat)]; rw [ramificationIdx_span_zeta_sub_one]

Depends on / 依赖: IsGalois, hK.zeta_spec.toInteger, isGalois, ramificationIdxIn_eq_ramificationIdx, ramificationIdx_span_zeta_sub_one, toInteger, zeta_spec
-/
theorem ramificationIdxIn_eq_of_prime_pow :
    𝒑.ramificationIdxIn (𝓞 K) = p ^ k * (p - 1) := by
  have : IsGalois Rat K := isGalois {p ^ (k + 1)} Rat K
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hK.zeta_spec.toInteger - 1}) Gal(K/Rat)]; rw [ramificationIdx_span_zeta_sub_one]

end PrimePow

section Prime

variable {K} [hK : IsCyclotomicExtension {p} Rat K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/--
Instance `isPrime_span_zeta_sub_one'` / 实例 `isPrime_span_zeta_sub_one'`

English:
instance isPrime_span_zeta_sub_one'
  signature: : IsPrime (span {hζ.toInteger - 1})
  body: by
  rw [← pow_one p] at hK hζ
  exact isPrime_span_zeta_sub_one p 0 hζ

中文:
实例 isPrime_span_zeta_sub_one'
  签名: : 是素 (span {hζ.to整数eger - 1})
  定义体: by
  rw [← pow_one p] at hK hζ
  exact isPrime_span_zeta_sub_one p 0 hζ

Depends on / 依赖: isPrime_span_zeta_sub_one, pow_one
-/
instance isPrime_span_zeta_sub_one' : IsPrime (span {hζ.toInteger - 1}) := by
  rw [← pow_one p] at hK hζ
  exact isPrime_span_zeta_sub_one p 0 hζ

/--
theorem `two_not_mem_span_zeta_sub_one'` / 定理 `two_not_mem_span_zeta_sub_one'`

English:
theorem two_not_mem_span_zeta_sub_one'
  given: (h : 2 < p)
  statement: (2 : 𝓞 K) ∉ span {hζ.toInteger - 1}
  proof: by
  rw [mem_span_singleton]
  rw [← pow_one p] at hK hζ
  exact hζ.toInteger_sub_one_not_dvd_two h.ne'

omit hp hK [NumberField K] in

中文:
定理 two_not_mem_span_zeta_sub_one'
  条件: (h : 2 < p)
  结论: (2 : 𝓞 K) ∉ span {hζ.to整数eger - 1}
  证明: by
  rw [mem_span_singleton]
  rw [← pow_one p] at hK hζ
  exact hζ.toInteger_sub_one_not_dvd_two h.ne'

omit hp hK [NumberField K] in

Depends on / 依赖: h.ne, mem_span_singleton, pow_one, toInteger_sub_one_not_dvd_two
-/
theorem two_not_mem_span_zeta_sub_one' (h : 2 < p) : (2 : 𝓞 K) ∉ span {hζ.toInteger - 1} := by
  rw [mem_span_singleton]
  rw [← pow_one p] at hK hζ
  exact hζ.toInteger_sub_one_not_dvd_two h.ne'

omit hp hK [NumberField K] in
/--
lemma `associated_sub_one_of_isPrimitiveRoot` / 引理 `associated_sub_one_of_isPrimitiveRoot`

English:
lemma associated_sub_one_of_isPrimitiveRoot
  given: [NeZero p] {η : K} (hη : IsPrimitiveRoot η p)
  proof: by
  obtain ⟨i, -, hi, hζη⟩ := hζ.isPrimitiveRoot_iff.mp hη
  rw [show hη.toInteger = hζ.toInteger ^ i from RingOfIntegers.ext hζη.symm]
  exact hζ.toInteger_isPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime hi

omit [NumberField K] hK in

中文:
引理 associated_sub_one_of_isPrimitiveRoot
  条件: [NeZero p] {η : K} (hη : 是PrimitiveRoot η p)
  证明: by
  obtain ⟨i, -, hi, hζη⟩ := hζ.isPrimitiveRoot_iff.mp hη
  rw [show hη.toInteger = hζ.toInteger ^ i from RingOfIntegers.ext hζη.symm]
  exact hζ.toInteger_isPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime hi

omit [NumberField K] hK in

Depends on / 依赖: RingOfIntegers, RingOfIntegers.ext, associated_sub_one_pow_sub_one_of_coprime, isPrimitiveRoot_iff, isPrimitiveRoot_iff.mp, toInteger, toInteger_isPrimitiveRoot, toInteger_isPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime
-/
lemma associated_sub_one_of_isPrimitiveRoot [NeZero p] {η : K} (hη : IsPrimitiveRoot η p) :
    Associated (hζ.toInteger - 1) (hη.toInteger - 1) := by
  obtain ⟨i, -, hi, hζη⟩ := hζ.isPrimitiveRoot_iff.mp hη
  rw [show hη.toInteger = hζ.toInteger ^ i from RingOfIntegers.ext hζη.symm]
  exact hζ.toInteger_isPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime hi

omit [NumberField K] hK in
open Polynomial in
/--
theorem `associated_zeta_sub_one_pow_prime` / 定理 `associated_zeta_sub_one_pow_prime`

English:
theorem associated_zeta_sub_one_pow_prime
  proof: by
  rw [← eval_one_cyclotomic_prime (R := 𝓞 K) (p := p)]; rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ.toInteger_isPrimitiveRoot]; rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [← Nat.totient_prime hp.out]; rw [← hζ.toInteger_isPrimitiveRoot.card_primitiveRoots]; rw [← Finset.prod_co

中文:
定理 associated_zeta_sub_one_pow_prime
  证明: by
  rw [← eval_one_cyclotomic_prime (R := 𝓞 K) (p := p)]; rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ.toInteger_isPrimitiveRoot]; rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [← Nat.totient_prime hp.out]; rw [← hζ.toInteger_isPrimitiveRoot.card_primitiveRoots]; rw [← Finset.prod_co

Depends on / 依赖: Associated, Associated.prod, Finset, Finset.prod_const, IsPrimitiveRoot, Nat.totient_prime, RingOfIntegers, RingOfIntegers.coe_injective, associated_sub_, card_primitiveRoots, coe_injective, cyclotomic_eq_prod_X_sub_primitiveRoots, eval_C, eval_X, eval_one_cyclotomic_prime, eval_prod, eval_sub, hp.out, isPrimitiveRoot_of_mem_primitiveRoots, map_of_injective
-/
theorem associated_zeta_sub_one_pow_prime :
    Associated ((hζ.toInteger - 1) ^ (p - 1)) (p : 𝓞 K) := by
  rw [← eval_one_cyclotomic_prime (R := 𝓞 K) (p := p)]; rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ.toInteger_isPrimitiveRoot]; rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [← Nat.totient_prime hp.out]; rw [← hζ.toInteger_isPrimitiveRoot.card_primitiveRoots]; rw [← Finset.prod_const]
  refine Associated.prod _ _ _ fun η hη => ?_
  have hη' : IsPrimitiveRoot (η : K) p :=
    (isPrimitiveRoot_of_mem_primitiveRoots hη).map_of_injective RingOfIntegers.coe_injective
  simpa using (associated_sub_one_of_isPrimitiveRoot p hζ hη').neg_right

/--
theorem `isCoprime_of_not_zeta_sub_one_dvd` / 定理 `isCoprime_of_not_zeta_sub_one_dvd`

English:
theorem isCoprime_of_not_zeta_sub_one_dvd
  given: {x : 𝓞 K} (hx : ¬ hζ.toInteger - 1 ∣ x)
  proof: by
  rwa [← isCoprime_span_singleton_iff, ← span_singleton_eq_span_singleton.mpr
    (associated_zeta_sub_one_pow_prime p hζ), ← span_singleton_pow,
    IsCoprime.pow_left_iff (by grind [hp.out.one_lt]), isCoprime_iff_gcd,
    (prime_span_singleton_iff.mpr
    hζ.zeta_sub_one_prime').irreducible.gcd

中文:
定理 isCoprime_of_not_zeta_sub_one_dvd
  条件: {x : 𝓞 K} (hx : ¬ hζ.to整数eger - 1 ∣ x)
  证明: by
  rwa [← isCoprime_span_singleton_iff, ← span_singleton_eq_span_singleton.mpr
    (associated_zeta_sub_one_pow_prime p hζ), ← span_singleton_pow,
    IsCoprime.pow_left_iff (by grind [hp.out.one_lt]), isCoprime_iff_gcd,
    (prime_span_singleton_iff.mpr
    hζ.zeta_sub_one_prime').irreducible.gcd

Depends on / 依赖: IsCoprime, IsCoprime.pow_left_iff, associated_zeta_sub_one_pow_prime, dvd_span_singleton, gcd_eq_one_iff, hp.out.one_lt, irreducible, irreducible.gcd_eq_one_iff, isCoprime_iff_gcd, isCoprime_span_singleton_iff, mem_span_singleton, one_lt, pow_left_iff, prime_span_singleton_iff, prime_span_singleton_iff.mpr, span_singleton_eq_span_singleton, span_singleton_eq_span_singleton.mpr, span_singleton_pow, zeta_sub_one_prime
-/
theorem isCoprime_of_not_zeta_sub_one_dvd {x : 𝓞 K} (hx : ¬ hζ.toInteger - 1 ∣ x) :
    IsCoprime (p : 𝓞 K) x := by
  rwa [← isCoprime_span_singleton_iff, ← span_singleton_eq_span_singleton.mpr
    (associated_zeta_sub_one_pow_prime p hζ), ← span_singleton_pow,
    IsCoprime.pow_left_iff (by grind [hp.out.one_lt]), isCoprime_iff_gcd,
    (prime_span_singleton_iff.mpr
    hζ.zeta_sub_one_prime').irreducible.gcd_eq_one_iff, dvd_span_singleton, mem_span_singleton]

/--
theorem `inertiaDeg_span_zeta_sub_one'` / 定理 `inertiaDeg_span_zeta_sub_one'`

English:
theorem inertiaDeg_span_zeta_sub_one'
  statement: inertiaDeg (span {hζ.toInteger - 1}) Int = 1
  proof: by
  rw [← pow_one p] at hK hζ
  exact inertiaDeg_span_zeta_sub_one p 0 hζ

中文:
定理 inertiaDeg_span_zeta_sub_one'
  结论: inertiaDeg (span {hζ.to整数eger - 1}) 整数 = 1
  证明: by
  rw [← pow_one p] at hK hζ
  exact inertiaDeg_span_zeta_sub_one p 0 hζ

Depends on / 依赖: inertiaDeg_span_zeta_sub_one, pow_one
-/
theorem inertiaDeg_span_zeta_sub_one' : inertiaDeg (span {hζ.toInteger - 1}) Int = 1 := by
  rw [← pow_one p] at hK hζ
  exact inertiaDeg_span_zeta_sub_one p 0 hζ

/--
theorem `ramificationIdx_span_zeta_sub_one'` / 定理 `ramificationIdx_span_zeta_sub_one'`

English:
theorem ramificationIdx_span_zeta_sub_one'
  proof: by
  rw [← pow_one p] at hK hζ
  rw [ramificationIdx_span_zeta_sub_one p 0 hζ]; rw [pow_zero]; rw [one_mul]

中文:
定理 ramificationIdx_span_zeta_sub_one'
  证明: by
  rw [← pow_one p] at hK hζ
  rw [ramificationIdx_span_zeta_sub_one p 0 hζ]; rw [pow_zero]; rw [one_mul]

Depends on / 依赖: one_mul, pow_one, pow_zero, ramificationIdx_span_zeta_sub_one
-/
theorem ramificationIdx_span_zeta_sub_one' :
    ramificationIdx (span {hζ.toInteger - 1}) Int = p - 1 := by
  rw [← pow_one p] at hK hζ
  rw [ramificationIdx_span_zeta_sub_one p 0 hζ]; rw [pow_zero]; rw [one_mul]

/--
theorem `zeta_sub_one_dvd_intCast_iff'` / 定理 `zeta_sub_one_dvd_intCast_iff'`

English:
theorem zeta_sub_one_dvd_intCast_iff'
  given: {n : Int}
  proof: by
  rw [← pow_one p] at hK hζ
  exact zeta_sub_one_dvd_intCast_iff p 0 hζ

中文:
定理 zeta_sub_one_dvd_intCast_iff'
  条件: {n : 整数}
  证明: by
  rw [← pow_one p] at hK hζ
  exact zeta_sub_one_dvd_intCast_iff p 0 hζ

Depends on / 依赖: pow_one, zeta_sub_one_dvd_intCast_iff
-/
theorem zeta_sub_one_dvd_intCast_iff' {n : Int} :
    hζ.toInteger - 1 ∣ (n : 𝓞 K) ↔ (p : Int) ∣ n := by
  rw [← pow_one p] at hK hζ
  exact zeta_sub_one_dvd_intCast_iff p 0 hζ

variable (K)

include hK in
/--
theorem `ncard_primesOver_of_prime` / 定理 `ncard_primesOver_of_prime`

English:
theorem ncard_primesOver_of_prime
  proof: by
  rw [← pow_one p] at hK
  exact ncard_primesOver_of_prime_pow p 0 K

中文:
定理 ncard_primesOver_of_prime
  证明: by
  rw [← pow_one p] at hK
  exact ncard_primesOver_of_prime_pow p 0 K

Depends on / 依赖: ncard_primesOver_of_prime_pow, pow_one
-/
theorem ncard_primesOver_of_prime :
    (primesOver 𝒑 (𝓞 K)).ncard = 1 := by
  rw [← pow_one p] at hK
  exact ncard_primesOver_of_prime_pow p 0 K

/--
theorem `eq_span_zeta_sub_one_of_liesOver'` / 定理 `eq_span_zeta_sub_one_of_liesOver'`

English:
theorem eq_span_zeta_sub_one_of_liesOver'
  given: (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑]
  proof: by
  rw [← pow_one p] at hK hζ
  exact eq_span_zeta_sub_one_of_liesOver p 0 K hζ P

include hK in

中文:
定理 eq_span_zeta_sub_one_of_liesOver'
  条件: (P : 理想 (𝓞 K)) [hP₁ : P.是素] [hP₂ : P.LiesOver 𝒑]
  证明: by
  rw [← pow_one p] at hK hζ
  exact eq_span_zeta_sub_one_of_liesOver p 0 K hζ P

include hK in

Depends on / 依赖: eq_span_zeta_sub_one_of_liesOver, pow_one
-/
theorem eq_span_zeta_sub_one_of_liesOver' (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    P = span {hζ.toInteger - 1} := by
  rw [← pow_one p] at hK hζ
  exact eq_span_zeta_sub_one_of_liesOver p 0 K hζ P

include hK in
/--
theorem `inertiaDeg_eq_of_prime` / 定理 `inertiaDeg_eq_of_prime`

English:
theorem inertiaDeg_eq_of_prime
  given: (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑]
  proof: by
  rw [eq_span_zeta_sub_one_of_liesOver' p K hK.zeta_spec P]; rw [inertiaDeg_span_zeta_sub_one']

include hK in

中文:
定理 inertiaDeg_eq_of_prime
  条件: (P : 理想 (𝓞 K)) [hP₁ : P.是素] [hP₂ : P.LiesOver 𝒑]
  证明: by
  rw [eq_span_zeta_sub_one_of_liesOver' p K hK.zeta_spec P]; rw [inertiaDeg_span_zeta_sub_one']

include hK in

Depends on / 依赖: eq_span_zeta_sub_one_of_liesOver, hK.zeta_spec, inertiaDeg_span_zeta_sub_one, zeta_spec
-/
theorem inertiaDeg_eq_of_prime (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    inertiaDeg P Int = 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver' p K hK.zeta_spec P]; rw [inertiaDeg_span_zeta_sub_one']

include hK in
/--
theorem `ramificationIdx_eq_of_prime` / 定理 `ramificationIdx_eq_of_prime`

English:
theorem ramificationIdx_eq_of_prime
  given: (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑]
  proof: by
  rw [eq_span_zeta_sub_one_of_liesOver' p K hK.zeta_spec P]; rw [ramificationIdx_span_zeta_sub_one']

include hK in

中文:
定理 ramificationIdx_eq_of_prime
  条件: (P : 理想 (𝓞 K)) [hP₁ : P.是素] [hP₂ : P.LiesOver 𝒑]
  证明: by
  rw [eq_span_zeta_sub_one_of_liesOver' p K hK.zeta_spec P]; rw [ramificationIdx_span_zeta_sub_one']

include hK in

Depends on / 依赖: eq_span_zeta_sub_one_of_liesOver, hK.zeta_spec, ramificationIdx_span_zeta_sub_one, zeta_spec
-/
theorem ramificationIdx_eq_of_prime (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    ramificationIdx P Int = p - 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver' p K hK.zeta_spec P]; rw [ramificationIdx_span_zeta_sub_one']

include hK in
/--
theorem `inertiaDegIn_eq_of_prime` / 定理 `inertiaDegIn_eq_of_prime`

English:
theorem inertiaDegIn_eq_of_prime
  proof: by
  rw [← pow_one p] at hK
  exact inertiaDegIn_eq_of_prime_pow p 0 K

include hK in

中文:
定理 inertiaDegIn_eq_of_prime
  证明: by
  rw [← pow_one p] at hK
  exact inertiaDegIn_eq_of_prime_pow p 0 K

include hK in

Depends on / 依赖: inertiaDegIn_eq_of_prime_pow, pow_one
-/
theorem inertiaDegIn_eq_of_prime :
    𝒑.inertiaDegIn (𝓞 K) = 1 := by
  rw [← pow_one p] at hK
  exact inertiaDegIn_eq_of_prime_pow p 0 K

include hK in
/--
theorem `ramificationIdxIn_eq_of_prime` / 定理 `ramificationIdxIn_eq_of_prime`

English:
theorem ramificationIdxIn_eq_of_prime
  proof: by
  rw [← pow_one p] at hK
  rw [ramificationIdxIn_eq_of_prime_pow p 0]; rw [pow_zero]; rw [one_mul]

中文:
定理 ramificationIdxIn_eq_of_prime
  证明: by
  rw [← pow_one p] at hK
  rw [ramificationIdxIn_eq_of_prime_pow p 0]; rw [pow_zero]; rw [one_mul]

Depends on / 依赖: one_mul, pow_one, pow_zero, ramificationIdxIn_eq_of_prime_pow
-/
theorem ramificationIdxIn_eq_of_prime :
    𝒑.ramificationIdxIn (𝓞 K) = p - 1 := by
  rw [← pow_one p] at hK
  rw [ramificationIdxIn_eq_of_prime_pow p 0]; rw [pow_zero]; rw [one_mul]

end Prime

section notDvd

open NumberField.Ideal Polynomial

variable {m} [NeZero m] [hK : IsCyclotomicExtension {m} Rat K]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `inertiaDeg_eq_of_not_dvd` / 定理 `inertiaDeg_eq_of_not_dvd`

English:
theorem inertiaDeg_eq_of_not_dvd
  given: (hm : ¬ p ∣ m)
  proof: by
  replace hm : p.Coprime m := hp.out.coprime_iff_not_dvd.mpr hm
  let ζ := (zeta_spec m Rat K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top (zeta_spec m Rat K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod

中文:
定理 inertiaDeg_eq_of_not_dvd
  条件: (hm : ¬ p ∣ m)
  证明: by
  replace hm : p.Coprime m := hp.out.coprime_iff_not_dvd.mpr hm
  let ζ := (zeta_spec m Rat K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top (zeta_spec m Rat K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod

Depends on / 依赖: Coprime, Equiv.symm_apply_apply, Multiset, Multiset.mem_toFinset, Polynomi, Subtype, Subtype.coe_eta, adjoin_singleton_eq_top, coe_eta, coprime_iff_not_dvd, exponent, exponent_eq_one_iff, exponent_eq_one_iff.mpr, hp.out.coprime_iff_not_dvd.mpr, hp.out.not_dvd_one, inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply, mem_toFinset, not_dvd_one, p.Coprime, primesOverSpanEquivMonicFactorsMod
-/
theorem inertiaDeg_eq_of_not_dvd (hm : ¬ p ∣ m) :
    inertiaDeg P Int = orderOf (p : ZMod m) := by
  replace hm : p.Coprime m := hp.out.coprime_iff_not_dvd.mpr hm
  let ζ := (zeta_spec m Rat K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top (zeta_spec m Rat K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2
  have h₃ := inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' h₁ h₂
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at h₃
  rw [Multiset.mem_toFinset]; rw [Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic ζ.isIntegral))] at h₂
  have : P.IsMaximal := .of_liesOver_isMaximal P 𝒑
  rw [h₃]; rw [natDegree_of_dvd_cyclotomic_of_irreducible (by simp) hm (f := 1) _ h₂.1]
  · simpa using (orderOf_injective _ Units.coeHom_injective (ZMod.unitOfCoprime p hm)).symm
  · refine dvd_trans h₂.2.2 ?_
    rw [← map_cyclotomic_int]; rw [cyclotomic_eq_minpoly (zeta_spec m Rat K) (NeZero.pos _)]; rw [← (zeta_spec m Rat K).coe_toInteger]; rw [← RingOfIntegers.minpoly_coe ζ]
    simp [ζ]

/--
theorem `ramificationIdx_eq_of_not_dvd` / 定理 `ramificationIdx_eq_of_not_dvd`

English:
theorem ramificationIdx_eq_of_not_dvd
  given: (hm : ¬ p ∣ m)
  proof: by
  let ζ := (zeta_spec m Rat K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top (zeta_spec m Rat K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2
  have h₃ := ramifica

中文:
定理 ramificationIdx_eq_of_not_dvd
  条件: (hm : ¬ p ∣ m)
  证明: by
  let ζ := (zeta_spec m Rat K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top (zeta_spec m Rat K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2
  have h₃ := ramifica

Depends on / 依赖: Equiv.symm_apply_apply, Multiset, Multiset.mem_toFinset, Polynomial, Polynomial.mem_normalizedFactors_iff, Subtype, Subtype.coe_eta, adjoin_singleton_eq_top, coe_eta, exponent, exponent_eq_one_iff, exponent_eq_one_iff.mpr, hp.out.not_dvd_one, map_monic_ne_zero, mem_normalizedFactors_iff, mem_toFinset, minpoly, not_dvd_one, primesOverSpanEquivMonicFactorsMod, ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply
-/
theorem ramificationIdx_eq_of_not_dvd (hm : ¬ p ∣ m) :
    ramificationIdx P Int = 1 := by
  let ζ := (zeta_spec m Rat K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top (zeta_spec m Rat K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2
  have h₃ := ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' h₁ h₂
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at h₃
  rw [Multiset.mem_toFinset]; rw [Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic ζ.isIntegral))] at h₂
  rw [h₃]
  refine multiplicity_eq_of_emultiplicity_eq_some (le_antisymm ?_ ?_)
  · apply emultiplicity_le_one_of_separable
    · exact isUnit_iff_degree_eq_zero.not.mpr (Irreducible.degree_pos h₂.1).ne'
    · exact (zeta_spec m Rat K).toInteger_isPrimitiveRoot.separable_minpoly_mod hm
  · rw [ENat.natCast_one]
exact Order.one_le_iff_pos.mpr emultiplicity_pos_of_dvd h₂.2.2

/--
theorem `inertiaDegIn_eq_of_not_dvd` / 定理 `inertiaDegIn_eq_of_not_dvd`

English:
theorem inertiaDegIn_eq_of_not_dvd
  given: (hm : ¬ p ∣ m)
  proof: by
  have : IsGalois Rat K := isGalois {m} Rat K
  obtain ⟨⟨P, _, _⟩⟩ := 𝒑.nonempty_primesOver (S := 𝓞 K)
  rw [inertiaDegIn_eq_inertiaDeg 𝒑 P Gal(K/Rat)]; rw [inertiaDeg_eq_of_not_dvd p K P hm]

中文:
定理 inertiaDegIn_eq_of_not_dvd
  条件: (hm : ¬ p ∣ m)
  证明: by
  have : IsGalois Rat K := isGalois {m} Rat K
  obtain ⟨⟨P, _, _⟩⟩ := 𝒑.nonempty_primesOver (S := 𝓞 K)
  rw [inertiaDegIn_eq_inertiaDeg 𝒑 P Gal(K/Rat)]; rw [inertiaDeg_eq_of_not_dvd p K P hm]

Depends on / 依赖: IsGalois, inertiaDegIn_eq_inertiaDeg, inertiaDeg_eq_of_not_dvd, isGalois, nonempty_primesOver
-/
theorem inertiaDegIn_eq_of_not_dvd (hm : ¬ p ∣ m) :
    𝒑.inertiaDegIn (𝓞 K) = orderOf (p : ZMod m) := by
  have : IsGalois Rat K := isGalois {m} Rat K
  obtain ⟨⟨P, _, _⟩⟩ := 𝒑.nonempty_primesOver (S := 𝓞 K)
  rw [inertiaDegIn_eq_inertiaDeg 𝒑 P Gal(K/Rat)]; rw [inertiaDeg_eq_of_not_dvd p K P hm]

/--
theorem `ramificationIdxIn_eq_of_not_dvd` / 定理 `ramificationIdxIn_eq_of_not_dvd`

English:
theorem ramificationIdxIn_eq_of_not_dvd
  given: (hm : ¬ p ∣ m)
  proof: by
  have : IsGalois Rat K := isGalois {m} Rat K
  obtain ⟨⟨P, _, _⟩⟩ := 𝒑.nonempty_primesOver (S := 𝓞 K)
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 P Gal(K/Rat)]; rw [ramificationIdx_eq_of_not_dvd p K P hm]

中文:
定理 ramificationIdxIn_eq_of_not_dvd
  条件: (hm : ¬ p ∣ m)
  证明: by
  have : IsGalois Rat K := isGalois {m} Rat K
  obtain ⟨⟨P, _, _⟩⟩ := 𝒑.nonempty_primesOver (S := 𝓞 K)
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 P Gal(K/Rat)]; rw [ramificationIdx_eq_of_not_dvd p K P hm]

Depends on / 依赖: IsGalois, isGalois, nonempty_primesOver, ramificationIdxIn_eq_ramificationIdx, ramificationIdx_eq_of_not_dvd
-/
theorem ramificationIdxIn_eq_of_not_dvd (hm : ¬ p ∣ m) :
    𝒑.ramificationIdxIn (𝓞 K) = 1 := by
  have : IsGalois Rat K := isGalois {m} Rat K
  obtain ⟨⟨P, _, _⟩⟩ := 𝒑.nonempty_primesOver (S := 𝓞 K)
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 P Gal(K/Rat)]; rw [ramificationIdx_eq_of_not_dvd p K P hm]

end notDvd

section general

variable {m p k} [IsCyclotomicExtension {n} Rat K]

set_option backward.isDefEq.respectTransparency false in
open IntermediateField in
/--
theorem `inertiaDegIn_ramificationIdxIn_aux` / 定理 `inertiaDegIn_ramificationIdxIn_aux`

English:
theorem inertiaDegIn_ramificationIdxIn_aux
  given: (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m)
  proof: by
  have : IsAbelianGalois Rat K := IsCyclotomicExtension.isAbelianGalois {n} Rat K
  have : NeZero m := ⟨fun h => by simp [h] at hm⟩
  have : NeZero n := ⟨hn ▸ NeZero.ne (p ^ (k + 1) * m)⟩
  let ζ := zeta n Rat K
  have hζ := zeta_spec n Rat K
  -- We construct `ℚ⟮ζₘ⟯ ⊆ ℚ⟮ζₙ⟯`
  let ζₘ := ζ ^ (p ^

中文:
定理 inertiaDegIn_ramificationIdxIn_aux
  条件: (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m)
  证明: by
  have : IsAbelianGalois Rat K := IsCyclotomicExtension.isAbelianGalois {n} Rat K
  have : NeZero m := ⟨fun h => by simp [h] at hm⟩
  have : NeZero n := ⟨hn ▸ NeZero.ne (p ^ (k + 1) * m)⟩
  let ζ := zeta n Rat K
  have hζ := zeta_spec n Rat K
  -- We construct `ℚ⟮ζₘ⟯ ⊆ ℚ⟮ζₙ⟯`
  let ζₘ := ζ ^ (p ^
-/
private theorem inertiaDegIn_ramificationIdxIn_aux (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    𝒑.inertiaDegIn (𝓞 K) = orderOf (p : ZMod m) ∧
      𝒑.ramificationIdxIn (𝓞 K) = p ^ k * (p - 1) := by
  have : IsAbelianGalois Rat K := IsCyclotomicExtension.isAbelianGalois {n} Rat K
  have : NeZero m := ⟨fun h => by simp [h] at hm⟩
  have : NeZero n := ⟨hn ▸ NeZero.ne (p ^ (k + 1) * m)⟩
  let ζ := zeta n Rat K
  have hζ := zeta_spec n Rat K
  -- We construct `ℚ⟮ζₘ⟯ ⊆ ℚ⟮ζₙ⟯`
  let ζₘ := ζ ^ (p ^ (k + 1))
  have hζₘ := hζ.pow (NeZero.pos _) hn
  let Fₘ := Rat⟮ζₘ⟯
  have : IsCyclotomicExtension {m} Rat Fₘ :=
    (isCyclotomicExtension_singleton_iff_eq_adjoin _ _ _ _ hζₘ).mpr rfl
  -- A prime ideal of `Fₘ` above `𝒑`
  obtain ⟨Pₘ, _, _⟩ := exists_maximal_ideal_liesOver_of_isIntegral 𝒑 (S := 𝓞 Fₘ)
  -- We construct `ℚ⟮ζ_p^{k+1}⟯ ⊆ ℚ⟮ζₘ⟯`
  let ζₚ := ζ ^ m
  have hζₚ := hζ.pow (NeZero.pos _) (mul_comm _ m ▸ hn)
  let Fₚ := Rat⟮ζₚ⟯
  have : IsCyclotomicExtension {p ^ (k + 1)} Rat Fₚ :=
    (isCyclotomicExtension_singleton_iff_eq_adjoin _ _ _ _ hζₚ).mpr rfl
  -- A prime ideal of `Fₚ` above `𝒑`
  obtain ⟨Pₚ, hP₁, _⟩ := exists_maximal_ideal_liesOver_of_isIntegral 𝒑 (S := 𝓞 Fₚ)
  suffices Pₚ.ramificationIdxIn (𝓞 K) *
      Pₘ.inertiaDegIn (𝓞 K) * (Pₘ.primesOver (𝓞 K)).ncard = 1 by
    replace this := Nat.eq_one_of_mul_eq_one_right this
    rw [← inertiaDegIn_mul_inertiaDegIn 𝒑 Pₘ Gal(Fₘ/Rat) _ Gal(K/Rat) Gal(K/Fₘ)]; rw [← ramificationIdxIn_mul_ramificationIdxIn Pₚ Gal(Fₚ/Rat) _ Gal(K/Rat) Gal(K/Fₚ)]; rw [Nat.eq_one_of_mul_eq_one_left this]; rw [Nat.eq_one_of_mul_eq_one_right this]; rw [mul_one]; rw [mul_one]; rw [inertiaDegIn_eq_of_not_dvd p _ hm]; rw [ramificationIdxIn_eq_of_prime_pow p k Fₚ]
    exact ⟨rfl, rfl⟩
  have h_main : Module.finrank Rat Fₘ * Module.finrank Rat Fₚ = Module.finrank Rat K := by
    rw [finrank m]; rw [finrank (p ^ (k + 1))]; rw [finrank n]; rw [hn]; rw [mul_comm]; rw [Nat.totient_mul]
    exact Nat.Coprime.pow_left (k + 1) (by rwa [hp.out.coprime_iff_not_dvd])
  rwa [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank,
    ← IsGalois.card_aut_eq_finrank,
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 Fₘ) Gal(Fₘ/Rat),
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 Fₚ) Gal(Fₚ/Rat),
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 K) Gal(K/Rat),
    ← ncard_primesOver_mul_ncard_primesOver Pₘ Gal(Fₘ/Rat) (𝓞 K) Gal(K/Rat),
    ramificationIdxIn_eq_of_not_dvd p Fₘ hm, inertiaDegIn_eq_of_prime_pow p k Fₚ,
    ncard_primesOver_of_prime_pow p k Fₚ, one_mul, one_mul, mul_one, mul_assoc, mul_assoc,
    mul_right_inj' (IsDedekindDomain.primesOver_ncard_ne_zero 𝒑 _), ← mul_assoc,
    ← mul_rotate (𝒑.inertiaDegIn (𝓞 K)),
    ← inertiaDegIn_mul_inertiaDegIn 𝒑 Pₘ Gal(Fₘ/Rat) (𝓞 K) Gal(K/Rat) Gal(K/Fₘ), mul_assoc, mul_assoc,
    mul_right_inj' (inertiaDegIn_ne_zero Gal(Fₘ/Rat)), ← mul_rotate',
    ← ramificationIdxIn_mul_ramificationIdxIn (p := 𝒑) Pₚ Gal(Fₚ/Rat) (𝓞 K) Gal(K/Rat) Gal(K/Fₚ),
    eq_comm, mul_assoc, mul_eq_left₀ (ramificationIdxIn_ne_zero Gal(Fₚ/Rat)), ← mul_assoc]
    at h_main

/--
theorem `inertiaDegIn_eq` / 定理 `inertiaDegIn_eq`

English:
theorem inertiaDegIn_eq
  given: (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m)
  proof: (inertiaDegIn_ramificationIdxIn_aux n K hn hm).1

中文:
定理 inertiaDegIn_eq
  条件: (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m)
  证明: (inertiaDegIn_ramificationIdxIn_aux n K hn hm).1

Depends on / 依赖: inertiaDegIn_ramificationIdxIn_aux
-/
theorem inertiaDegIn_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    𝒑.inertiaDegIn (𝓞 K) = orderOf (p : ZMod m) :=
  (inertiaDegIn_ramificationIdxIn_aux n K hn hm).1

/--
theorem `ramificationIdxIn_eq` / 定理 `ramificationIdxIn_eq`

English:
theorem ramificationIdxIn_eq
  given: (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m)
  proof: (inertiaDegIn_ramificationIdxIn_aux n K hn hm).2

中文:
定理 ramificationIdxIn_eq
  条件: (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m)
  证明: (inertiaDegIn_ramificationIdxIn_aux n K hn hm).2

Depends on / 依赖: inertiaDegIn_ramificationIdxIn_aux
-/
theorem ramificationIdxIn_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    𝒑.ramificationIdxIn (𝓞 K) = p ^ k * (p - 1) :=
  (inertiaDegIn_ramificationIdxIn_aux n K hn hm).2

/--
theorem `inertiaDeg_eq` / 定理 `inertiaDeg_eq`

English:
theorem inertiaDeg_eq
  given: (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m)
  proof: by
  have : IsGalois Rat K := isGalois {n} Rat K
  rw [← inertiaDegIn_eq_inertiaDeg 𝒑 P Gal(K/Rat)]; rw [inertiaDegIn_eq n K hn hm]

中文:
定理 inertiaDeg_eq
  条件: (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m)
  证明: by
  have : IsGalois Rat K := isGalois {n} Rat K
  rw [← inertiaDegIn_eq_inertiaDeg 𝒑 P Gal(K/Rat)]; rw [inertiaDegIn_eq n K hn hm]

Depends on / 依赖: IsGalois, inertiaDegIn_eq, inertiaDegIn_eq_inertiaDeg, isGalois
-/
theorem inertiaDeg_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    inertiaDeg P Int = orderOf (p : ZMod m) := by
  have : IsGalois Rat K := isGalois {n} Rat K
  rw [← inertiaDegIn_eq_inertiaDeg 𝒑 P Gal(K/Rat)]; rw [inertiaDegIn_eq n K hn hm]

/--
theorem `ramificationIdx_eq` / 定理 `ramificationIdx_eq`

English:
theorem ramificationIdx_eq
  given: (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m)
  proof: by
  have : IsGalois Rat K := isGalois {n} Rat K
  rw [← ramificationIdxIn_eq_ramificationIdx 𝒑 P Gal(K/Rat)]; rw [ramificationIdxIn_eq n K hn hm]

中文:
定理 ramificationIdx_eq
  条件: (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m)
  证明: by
  have : IsGalois Rat K := isGalois {n} Rat K
  rw [← ramificationIdxIn_eq_ramificationIdx 𝒑 P Gal(K/Rat)]; rw [ramificationIdxIn_eq n K hn hm]

Depends on / 依赖: IsGalois, isGalois, ramificationIdxIn_eq, ramificationIdxIn_eq_ramificationIdx
-/
theorem ramificationIdx_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    ramificationIdx P Int = p ^ k * (p - 1) := by
  have : IsGalois Rat K := isGalois {n} Rat K
  rw [← ramificationIdxIn_eq_ramificationIdx 𝒑 P Gal(K/Rat)]; rw [ramificationIdxIn_eq n K hn hm]

end general

end IsCyclotomicExtension.Rat
