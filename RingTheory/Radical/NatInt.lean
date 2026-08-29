/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Arend Mellendijk, Jeremy Tan
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Radical.Basic

/-!
# The radical in `ℕ` and `ℤ`

## Declarations for `ℕ`

- `UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors`: The prime factors of a natural number
  are the same as the prime factors defined in `Nat.primeFactors`.
- `Nat.radical_eq_prod_primeFactors`: The radical is computable for natural numbers.
- `Nat.radical_le_self_iff`: if `n ≠ 0`, `radical n ≤ n`.
- `Nat.two_le_radical_iff`: `2 ≤ n.radical` iff `2 ≤ n`.

## Declarations for `ℤ`

- `UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs`: The prime factors of an integer
  are the same as the prime factors of its absolute value.
- `Int.radical_eq_prod_primeFactors`: The radical is computable for integers.
-/

@[expose] public section

open UniqueFactorizationMonoid


/--
lemma `UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors` / 引理 `UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors`

English:
lemma UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors
  proof: by
  ext n : 1
  rw [primeFactors]; rw [Nat.factors_eq]; rw [Nat.primeFactors]
  -- this convert is necessary because of the different DecidableEq instances
  convert! List.toFinset_coe _

中文:
引理 唯一分解幺半群.primeFactors_eq_natPrimeFactors
  证明: by
  ext n : 1
  rw [primeFactors]; rw [Nat.factors_eq]; rw [Nat.primeFactors]
  -- this convert is necessary because of the different DecidableEq instances
  convert! List.toFinset_coe _

Depends on / 依赖: Nat.factors_eq, Nat.primeFactors, factors_eq, primeFactors
-/
lemma UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors :
    primeFactors = Nat.primeFactors := by
  ext n : 1
  rw [primeFactors]; rw [Nat.factors_eq]; rw [Nat.primeFactors]
  -- this convert is necessary because of the different DecidableEq instances
  convert! List.toFinset_coe _

namespace Nat

variable {n : Nat}

/--
lemma `radical_eq_prod_primeFactors` / 引理 `radical_eq_prod_primeFactors`

English:
lemma radical_eq_prod_primeFactors
  statement: radical n = ∏ p in n.primeFactors, p
  proof: by
  simp [radical, primeFactors_eq_natPrimeFactors]

中文:
引理 radical_eq_prod_primeFactors
  结论: radical n = ∏ p in n.primeFactors, p
  证明: by
  simp [radical, primeFactors_eq_natPrimeFactors]

Depends on / 依赖: primeFactors_eq_natPrimeFactors, radical
-/
lemma radical_eq_prod_primeFactors : radical n = ∏ p in n.primeFactors, p := by
  simp [radical, primeFactors_eq_natPrimeFactors]

/--
lemma `radical_pos` / 引理 `radical_pos`

English:
lemma radical_pos
  given: (n)
  statement: 0 < radical n
  proof: pos_of_ne_zero radical_ne_zero

中文:
引理 radical_pos
  条件: (n)
  结论: 0 < radical n
  证明: pos_of_ne_zero radical_ne_zero

Depends on / 依赖: pos_of_ne_zero, radical_ne_zero
-/
lemma radical_pos (n) : 0 < radical n := pos_of_ne_zero radical_ne_zero

/--
lemma `one_lt_radical_iff` / 引理 `one_lt_radical_iff`

English:
lemma one_lt_radical_iff
  statement: 1 < radical n ↔ 1 < n
  proof: by
  have pp (p) (h : p in n.primeFactors) : 1 <= p := pos_of_mem_primeFactors h
  rw [radical_eq_prod_primeFactors]; rw [← @nonempty_primeFactors n]; rw [Finset.one_lt_prod_iff_of_one_le pp]
  exact ⟨fun ⟨p, h⟩ => ⟨p, h.1⟩, fun ⟨p, h⟩ => ⟨p, h, (mem_primeFactors.mp h).1.one_lt⟩⟩

中文:
引理 one_lt_radical_iff
  结论: 1 < radical n ↔ 1 < n
  证明: by
  have pp (p) (h : p in n.primeFactors) : 1 <= p := pos_of_mem_primeFactors h
  rw [radical_eq_prod_primeFactors]; rw [← @nonempty_primeFactors n]; rw [Finset.one_lt_prod_iff_of_one_le pp]
  exact ⟨fun ⟨p, h⟩ => ⟨p, h.1⟩, fun ⟨p, h⟩ => ⟨p, h, (mem_primeFactors.mp h).1.one_lt⟩⟩
-/
@[simp] lemma one_lt_radical_iff : 1 < radical n ↔ 1 < n := by
  have pp (p) (h : p in n.primeFactors) : 1 <= p := pos_of_mem_primeFactors h
  rw [radical_eq_prod_primeFactors]; rw [← @nonempty_primeFactors n]; rw [Finset.one_lt_prod_iff_of_one_le pp]
  exact ⟨fun ⟨p, h⟩ => ⟨p, h.1⟩, fun ⟨p, h⟩ => ⟨p, h, (mem_primeFactors.mp h).1.one_lt⟩⟩

/--
lemma `two_le_radical_iff` / 引理 `two_le_radical_iff`

English:
lemma two_le_radical_iff
  statement: 2 <= radical n ↔ 2 <= n
  proof: one_lt_radical_iff

中文:
引理 two_le_radical_iff
  结论: 2 <= radical n ↔ 2 <= n
  证明: one_lt_radical_iff
-/
@[simp] lemma two_le_radical_iff : 2 <= radical n ↔ 2 <= n := one_lt_radical_iff

/--
lemma `radical_le_one_iff` / 引理 `radical_le_one_iff`

English:
lemma radical_le_one_iff
  statement: radical n <= 1 ↔ n <= 1
  proof: by
  simpa only [not_lt] using one_lt_radical_iff.not

中文:
引理 radical_le_one_iff
  结论: radical n <= 1 ↔ n <= 1
  证明: by
  simpa only [not_lt] using one_lt_radical_iff.not
-/
@[simp] lemma radical_le_one_iff : radical n <= 1 ↔ n <= 1 := by
  simpa only [not_lt] using one_lt_radical_iff.not

/--
lemma `radical_eq_one_iff` / 引理 `radical_eq_one_iff`

English:
lemma radical_eq_one_iff
  statement: radical n = 1 ↔ n <= 1
  proof: by
  rw [← radical_le_one_iff]
  grind [radical_pos n]

中文:
引理 radical_eq_one_iff
  结论: radical n = 1 ↔ n <= 1
  证明: by
  rw [← radical_le_one_iff]
  grind [radical_pos n]
-/
@[simp] lemma radical_eq_one_iff : radical n = 1 ↔ n <= 1 := by
  rw [← radical_le_one_iff]
  grind [radical_pos n]

/--
lemma `radical_le_self_iff` / 引理 `radical_le_self_iff`

English:
lemma radical_le_self_iff
  statement: radical n <= n ↔ n != 0
  proof: ⟨by aesop, fun h => Nat.le_of_dvd (by lia) radical_dvd_self⟩

中文:
引理 radical_le_self_iff
  结论: radical n <= n ↔ n != 0
  证明: ⟨by aesop, fun h => Nat.le_of_dvd (by lia) radical_dvd_self⟩
-/
@[simp] lemma radical_le_self_iff : radical n <= n ↔ n != 0 :=
  ⟨by aesop, fun h => Nat.le_of_dvd (by lia) radical_dvd_self⟩

/--
lemma `self_lt_radical_iff` / 引理 `self_lt_radical_iff`

English:
lemma self_lt_radical_iff
  statement: n < radical n ↔ n = 0
  proof: by
  simpa only [not_le, not_not] using radical_le_self_iff.not

中文:
引理 self_lt_radical_iff
  结论: n < radical n ↔ n = 0
  证明: by
  simpa only [not_le, not_not] using radical_le_self_iff.not
-/
@[simp] lemma self_lt_radical_iff : n < radical n ↔ n = 0 := by
  simpa only [not_le, not_not] using radical_le_self_iff.not

/--
theorem `primeFactors_radical` / 定理 `primeFactors_radical`

English:
theorem primeFactors_radical
  given: (n : Nat)
  statement: (radical n).primeFactors = n.primeFactors
  proof: by
  rw [radical_eq_prod_primeFactors]; rw [primeFactors_prod_primeFactors]

中文:
定理 primeFactors_radical
  条件: (n : 自然数)
  结论: (radical n).primeFactors = n.primeFactors
  证明: by
  rw [radical_eq_prod_primeFactors]; rw [primeFactors_prod_primeFactors]

Depends on / 依赖: primeFactors_prod_primeFactors, radical_eq_prod_primeFactors
-/
theorem primeFactors_radical (n : Nat) : (radical n).primeFactors = n.primeFactors := by
  rw [radical_eq_prod_primeFactors]; rw [primeFactors_prod_primeFactors]

/--
theorem `radical_dvd_iff` / 定理 `radical_dvd_iff`

English:
theorem radical_dvd_iff
  given: {n k : Nat} (hk : k != 0)
  proof: by
  rw [radical_eq_prod_primeFactors]; rw [prod_primeFactors_dvd_iff hk]

中文:
定理 radical_dvd_iff
  条件: {n k : 自然数} (hk : k != 0)
  证明: by
  rw [radical_eq_prod_primeFactors]; rw [prod_primeFactors_dvd_iff hk]

Depends on / 依赖: prod_primeFactors_dvd_iff, radical_eq_prod_primeFactors
-/
theorem radical_dvd_iff {n k : Nat} (hk : k != 0) :
    radical n ∣ k ↔ n.primeFactors subseteq k.primeFactors := by
  rw [radical_eq_prod_primeFactors]; rw [prod_primeFactors_dvd_iff hk]

/--
theorem `dvd_radical_pow_self` / 定理 `dvd_radical_pow_self`

English:
theorem dvd_radical_pow_self
  given: {n : Nat} (hn : n != 0)
  statement: n ∣ radical n ^ n
  proof: by
  grw [radical_eq_prod_primeFactors, ← dvd_prod_primeFactors_pow_self hn]

中文:
定理 dvd_radical_pow_self
  条件: {n : 自然数} (hn : n != 0)
  结论: n ∣ radical n ^ n
  证明: by
  grw [radical_eq_prod_primeFactors, ← dvd_prod_primeFactors_pow_self hn]

Depends on / 依赖: dvd_prod_primeFactors_pow_self, radical_eq_prod_primeFactors
-/
theorem dvd_radical_pow_self {n : Nat} (hn : n != 0) : n ∣ radical n ^ n := by
  grw [radical_eq_prod_primeFactors, ← dvd_prod_primeFactors_pow_self hn]

open Qq Lean Mathlib.Meta Finset

namespace Mathlib.Meta.Positivity
open Positivity

attribute [local instance] monadLiftOptionMetaM in
/-- Positivity extension for radical. Proves radicals are nonzero. -/
@[positivity UniqueFactorizationMonoid.radical _]
meta def evalRadical : PositivityExt where eval {u α} _ _ e := do
  match e with
  | ~q(@radical _ $inst $inst' $inst'' $n) =>
    have _ := ← synthInstanceQ q(Nontrivial $α)
    assertInstancesCommute
    return .nonzero q(radical_ne_zero)
  | _ => throwError "not radical"

example : 0 < radical 100 := by positivity

end Mathlib.Meta.Positivity

end Nat

/-! ### Lemmas about integers -/

variable {z : Int}

/--
lemma `UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs` / 引理 `UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs`

English:
lemma UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs
  proof: by
  obtain rfl | hz := eq_or_ne z 0; · simp
  ext p
  rw [mem_primeFactors]; rw [mem_normalizedFactors_iff' hz]; rw [irreducible_iff_prime]; rw [Int.nonneg_iff_normalize_eq_self]; rw [Finset.mem_map]; rw [Function.Embedding.coeFn_mk]
  refine ⟨fun ⟨pp, nnp, dp⟩ => ?_, fun h => ?_⟩
  · lift p to Nat

中文:
引理 唯一分解幺半群.primeFactors_eq_primeFactors_natAbs
  证明: by
  obtain rfl | hz := eq_or_ne z 0; · simp
  ext p
  rw [mem_primeFactors]; rw [mem_normalizedFactors_iff' hz]; rw [irreducible_iff_prime]; rw [Int.nonneg_iff_normalize_eq_self]; rw [Finset.mem_map]; rw [Function.Embedding.coeFn_mk]
  refine ⟨fun ⟨pp, nnp, dp⟩ => ?_, fun h => ?_⟩
  · lift p to Nat

Depends on / 依赖: Embedding, Finset, Finset.mem_map, Function, Function.Embedding.coeFn_mk, Function.Embedding.toFun_eq_coe, Int.natCast_dvd, Int.nonneg_iff_normalize_eq_self, Nat.castEmbedding_apply, Nat.mem_primeFactors, Nat.prime_iff_prime_int, castEmbedding_apply, coeFn_mk, eq_or_ne, irreducible_iff_prime, mem_map, mem_normalizedFactors_iff, mem_primeFactors, natCast_dvd, nonneg_iff_normalize_eq_self
-/
lemma UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs :
    primeFactors z = z.natAbs.primeFactors.map Nat.castEmbedding := by
  obtain rfl | hz := eq_or_ne z 0; · simp
  ext p
  rw [mem_primeFactors]; rw [mem_normalizedFactors_iff' hz]; rw [irreducible_iff_prime]; rw [Int.nonneg_iff_normalize_eq_self]; rw [Finset.mem_map]; rw [Function.Embedding.coeFn_mk]
  refine ⟨fun ⟨pp, nnp, dp⟩ => ?_, fun h => ?_⟩
  · lift p to Nat using nnp
    rw [← Nat.prime_iff_prime_int] at pp
    rw [Int.natCast_dvd] at dp
    exact ⟨p, by simp_all, rfl⟩
  · simp_rw [Nat.mem_primeFactors, Function.Embedding.toFun_eq_coe, Nat.castEmbedding_apply] at h
    obtain ⟨n, ⟨pn, dn, -⟩, rfl⟩ := h
    rw [Int.natCast_dvd]; rw [← Nat.prime_iff_prime_int]
    exact ⟨pn, by simp, dn⟩

namespace Int

/--
lemma `radical_natAbs_eq_radical` / 引理 `radical_natAbs_eq_radical`

English:
lemma radical_natAbs_eq_radical
  statement: radical z.natAbs = radical z
  proof: by
  rw [Nat.radical_eq_prod_primeFactors]; rw [radical]
  simp [primeFactors_eq_primeFactors_natAbs]

中文:
引理 radical_natAbs_eq_radical
  结论: radical z.natAbs = radical z
  证明: by
  rw [Nat.radical_eq_prod_primeFactors]; rw [radical]
  simp [primeFactors_eq_primeFactors_natAbs]
-/
@[simp] lemma radical_natAbs_eq_radical : radical z.natAbs = radical z := by
  rw [Nat.radical_eq_prod_primeFactors]; rw [radical]
  simp [primeFactors_eq_primeFactors_natAbs]

/--
lemma `radical_eq_prod_primeFactors` / 引理 `radical_eq_prod_primeFactors`

English:
lemma radical_eq_prod_primeFactors
  statement: radical z = ∏ p in z.natAbs.primeFactors, p
  proof: by
  rw [← radical_natAbs_eq_radical]; rw [Nat.radical_eq_prod_primeFactors]

中文:
引理 radical_eq_prod_primeFactors
  结论: radical z = ∏ p in z.natAbs.primeFactors, p
  证明: by
  rw [← radical_natAbs_eq_radical]; rw [Nat.radical_eq_prod_primeFactors]

Depends on / 依赖: Nat.radical_eq_prod_primeFactors, radical_eq_prod_primeFactors, radical_natAbs_eq_radical
-/
lemma radical_eq_prod_primeFactors : radical z = ∏ p in z.natAbs.primeFactors, p := by
  rw [← radical_natAbs_eq_radical]; rw [Nat.radical_eq_prod_primeFactors]

/--
lemma `radical_pos` / 引理 `radical_pos`

English:
lemma radical_pos
  given: (z : Int)
  statement: 0 < radical z
  proof: by
  rw [← radical_natAbs_eq_radical]; rw [natCast_pos]
  exact Nat.radical_pos _

中文:
引理 radical_pos
  条件: (z : 整数)
  结论: 0 < radical z
  证明: by
  rw [← radical_natAbs_eq_radical]; rw [natCast_pos]
  exact Nat.radical_pos _

Depends on / 依赖: Nat.radical_pos, natCast_pos, radical_natAbs_eq_radical, radical_pos
-/
lemma radical_pos (z : Int) : 0 < radical z := by
  rw [← radical_natAbs_eq_radical]; rw [natCast_pos]
  exact Nat.radical_pos _

/--
lemma `one_lt_radical_iff` / 引理 `one_lt_radical_iff`

English:
lemma one_lt_radical_iff
  statement: 1 < radical z ↔ 1 < z.natAbs
  proof: by
  rw [← radical_natAbs_eq_radical]; rw [Nat.one_lt_cast]
  exact Nat.one_lt_radical_iff

中文:
引理 one_lt_radical_iff
  结论: 1 < radical z ↔ 1 < z.natAbs
  证明: by
  rw [← radical_natAbs_eq_radical]; rw [Nat.one_lt_cast]
  exact Nat.one_lt_radical_iff
-/
@[simp] lemma one_lt_radical_iff : 1 < radical z ↔ 1 < z.natAbs := by
  rw [← radical_natAbs_eq_radical]; rw [Nat.one_lt_cast]
  exact Nat.one_lt_radical_iff

/--
lemma `two_le_radical_iff` / 引理 `two_le_radical_iff`

English:
lemma two_le_radical_iff
  statement: 2 <= radical z ↔ 2 <= z.natAbs
  proof: one_lt_radical_iff

中文:
引理 two_le_radical_iff
  结论: 2 <= radical z ↔ 2 <= z.natAbs
  证明: one_lt_radical_iff
-/
@[simp] lemma two_le_radical_iff : 2 <= radical z ↔ 2 <= z.natAbs := one_lt_radical_iff

/--
lemma `radical_le_one_iff` / 引理 `radical_le_one_iff`

English:
lemma radical_le_one_iff
  statement: radical z <= 1 ↔ z.natAbs <= 1
  proof: by
  simpa only [not_lt] using one_lt_radical_iff.not

中文:
引理 radical_le_one_iff
  结论: radical z <= 1 ↔ z.natAbs <= 1
  证明: by
  simpa only [not_lt] using one_lt_radical_iff.not
-/
@[simp] lemma radical_le_one_iff : radical z <= 1 ↔ z.natAbs <= 1 := by
  simpa only [not_lt] using one_lt_radical_iff.not

/--
lemma `radical_eq_one_iff` / 引理 `radical_eq_one_iff`

English:
lemma radical_eq_one_iff
  statement: radical z = 1 ↔ z.natAbs <= 1
  proof: by
  rw [← radical_le_one_iff]
  grind [radical_pos z]

中文:
引理 radical_eq_one_iff
  结论: radical z = 1 ↔ z.natAbs <= 1
  证明: by
  rw [← radical_le_one_iff]
  grind [radical_pos z]
-/
@[simp] lemma radical_eq_one_iff : radical z = 1 ↔ z.natAbs <= 1 := by
  rw [← radical_le_one_iff]
  grind [radical_pos z]

/--
lemma `radical_natCast` / 引理 `radical_natCast`

English:
lemma radical_natCast
  given: {n : Nat}
  statement: radical (n : Int) = radical n
  proof: by
  simp [Int.radical_eq_prod_primeFactors, Nat.radical_eq_prod_primeFactors]

中文:
引理 radical_natCast
  条件: {n : 自然数}
  结论: radical (n : 整数) = radical n
  证明: by
  simp [Int.radical_eq_prod_primeFactors, Nat.radical_eq_prod_primeFactors]
-/
@[simp, norm_cast] lemma radical_natCast {n : Nat} : radical (n : Int) = radical n := by
  simp [Int.radical_eq_prod_primeFactors, Nat.radical_eq_prod_primeFactors]

end Int
