/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# The Carmichael function

## Main definitions

* `ArithmeticFunction.carmichael`: the Carmichael function `λ`,
  also known as the reduced totient function.

## Main results

* A formula for `λ n` in terms of the prime factorization of `n`, given by the following theorems:
  `carmichael_two_pow_of_le_two`, `carmichael_two_pow_of_ne_two`, `carmichael_pow_of_prime_ne_two`,
  and `carmichael_factorization`.

## Notation

We use the standard notation `λ` to represent the Carmichael function,
which is accessible in the scope `ArithmeticFunction.carmichael`.
Since the notation conflicts with the anonymous function notation, it is impossible to use this
notation in statements, but the pretty-printer will use it when showing the goal state.

## Tags

arithmetic functions, totient
-/

@[expose] public section

open Nat Monoid

variable {R : Type*}

namespace ArithmeticFunction

/--
Definition of `carmichael` / `carmichael` 的定义

English:
definition carmichael
  signature: : ArithmeticFunction Nat where
  body: rfl

@[deprecated (since := "2026-05-06")] alias Carmichael := carmichael

@[inherit_doc]
scoped[ArithmeticFunction.carmichael] notation "fun" => ArithmeticFunction.carmichael

中文:
定义 carmichael
  签名: : ArithmeticFunction 自然数 where
  定义体: rfl

@[deprecated (since := "2026-05-06")] alias Carmichael := carmichael

@[inherit_doc]
scoped[ArithmeticFunction.carmichael] notation "fun" => ArithmeticFunction.carmichael
-/
def carmichael : ArithmeticFunction Nat where
  toFun
    | 0 => 0
| n + 1 => Nat.find ExponentExists.of_finite (G := (ZMod (n + 1))ˣ)
  map_zero' := rfl

@[deprecated (since := "2026-05-06")] alias Carmichael := carmichael

@[inherit_doc]
scoped[ArithmeticFunction.carmichael] notation "fun" => ArithmeticFunction.carmichael

open scoped carmichael

/--
theorem `carmichael_eq_exponent` / 定理 `carmichael_eq_exponent`

English:
theorem carmichael_eq_exponent
  given: {n : Nat} (hn : n != 0)
  statement: carmichael n = exponent (ZMod n)ˣ
  proof: by
  cases n with | zero => contradiction | succ n =>
  change Nat.find _ = _
  grind [exponent, ExponentExists.of_finite]

中文:
定理 carmichael_eq_exponent
  条件: {n : 自然数} (hn : n != 0)
  结论: carmichael n = exponent (ZMod n)ˣ
  证明: by
  cases n with | zero => contradiction | succ n =>
  change Nat.find _ = _
  grind [exponent, ExponentExists.of_finite]

Depends on / 依赖: ExponentExists, ExponentExists.of_finite, Nat.find, exponent, of_finite
-/
theorem carmichael_eq_exponent {n : Nat} (hn : n != 0) : carmichael n = exponent (ZMod n)ˣ := by
  cases n with | zero => contradiction | succ n =>
  change Nat.find _ = _
  grind [exponent, ExponentExists.of_finite]

/--
theorem `carmichael_eq_exponent'` / 定理 `carmichael_eq_exponent'`

English:
theorem carmichael_eq_exponent'
  given: (n : Nat) [NeZero n]
  statement: carmichael n = exponent (ZMod n)ˣ
  proof: carmichael_eq_exponent NeZero.ne n

@[simp]

中文:
定理 carmichael_eq_exponent'
  条件: (n : 自然数) [NeZero n]
  结论: carmichael n = exponent (ZMod n)ˣ
  证明: carmichael_eq_exponent NeZero.ne n

@[simp]

Depends on / 依赖: NeZero, NeZero.ne, carmichael_eq_exponent
-/
theorem carmichael_eq_exponent' (n : Nat) [NeZero n] : carmichael n = exponent (ZMod n)ˣ :=
carmichael_eq_exponent NeZero.ne n

@[simp]
/--
theorem `pow_carmichael` / 定理 `pow_carmichael`

English:
theorem pow_carmichael
  given: {n : Nat} (a : (ZMod n)ˣ)
  statement: a ^ carmichael n = 1
  proof: by
  cases n
  · rw [map_zero, pow_zero]
  rw [carmichael_eq_exponent']
  exact pow_exponent_eq_one a

中文:
定理 pow_carmichael
  条件: {n : 自然数} (a : (ZMod n)ˣ)
  结论: a ^ carmichael n = 1
  证明: by
  cases n
  · rw [map_zero, pow_zero]
  rw [carmichael_eq_exponent']
  exact pow_exponent_eq_one a

Depends on / 依赖: carmichael_eq_exponent, map_zero, pow_exponent_eq_one, pow_zero
-/
theorem pow_carmichael {n : Nat} (a : (ZMod n)ˣ) : a ^ carmichael n = 1 := by
  cases n
  · rw [map_zero, pow_zero]
  rw [carmichael_eq_exponent']
  exact pow_exponent_eq_one a

/--
theorem `carmichael_dvd_totient` / 定理 `carmichael_dvd_totient`

English:
theorem carmichael_dvd_totient
  given: (n : Nat)
  statement: carmichael n ∣ n.totient
  proof: by
  cases n
  · simp
  rw [← ZMod.card_units_eq_totient]; rw [carmichael_eq_exponent']
  exact Group.exponent_dvd_card

中文:
定理 carmichael_dvd_totient
  条件: (n : 自然数)
  结论: carmichael n ∣ n.totient
  证明: by
  cases n
  · simp
  rw [← ZMod.card_units_eq_totient]; rw [carmichael_eq_exponent']
  exact Group.exponent_dvd_card

Depends on / 依赖: Group.exponent_dvd_card, ZMod.card_units_eq_totient, card_units_eq_totient, carmichael_eq_exponent, exponent_dvd_card
-/
theorem carmichael_dvd_totient (n : Nat) : carmichael n ∣ n.totient := by
  cases n
  · simp
  rw [← ZMod.card_units_eq_totient]; rw [carmichael_eq_exponent']
  exact Group.exponent_dvd_card

/--
theorem `carmichael_dvd` / 定理 `carmichael_dvd`

English:
theorem carmichael_dvd
  given: {a b : Nat} (h : a ∣ b)
  statement: carmichael a ∣ carmichael b
  proof: by
  cases b
  · simp
  rw [carmichael_eq_exponent <| ne_zero_of_dvd_ne_zero (by lia) h]; rw [carmichael_eq_exponent']
exact MonoidHom.exponent_dvd ZMod.unitsMap_surjective h

中文:
定理 carmichael_dvd
  条件: {a b : 自然数} (h : a ∣ b)
  结论: carmichael a ∣ carmichael b
  证明: by
  cases b
  · simp
  rw [carmichael_eq_exponent <| ne_zero_of_dvd_ne_zero (by lia) h]; rw [carmichael_eq_exponent']
exact MonoidHom.exponent_dvd ZMod.unitsMap_surjective h

Depends on / 依赖: MonoidHom, MonoidHom.exponent_dvd, ZMod.unitsMap_surjective, carmichael_eq_exponent, exponent_dvd, ne_zero_of_dvd_ne_zero, unitsMap_surjective
-/
theorem carmichael_dvd {a b : Nat} (h : a ∣ b) : carmichael a ∣ carmichael b := by
  cases b
  · simp
  rw [carmichael_eq_exponent <| ne_zero_of_dvd_ne_zero (by lia) h]; rw [carmichael_eq_exponent']
exact MonoidHom.exponent_dvd ZMod.unitsMap_surjective h

/--
theorem `carmichael_lcm` / 定理 `carmichael_lcm`

English:
theorem carmichael_lcm
  given: (a b : Nat)
  proof: by
  by_cases! h₀ : a = 0 ∨ b = 0
  · grind [Nat.lcm_eq_zero_iff, map_zero]
  apply dvd_antisymm
  · rw [carmichael_eq_exponent h₀.left, carmichael_eq_exponent h₀.right,
carmichael_eq_exponent lcm_ne_zero h₀.left h₀.right, ← lcm_eq_nat_lcm exponent _,
      ← exponent_prod, ← exponent_eq_of_mulEquiv .prodUnits]
exact exponent_dvd_of_monoidHom _ Units.map_injective ZMod.castHom_injective _
· have ha := carmichael_dvd Nat.dvd_lcm_left a b
have hb := carmichael_dvd Nat.dvd_lcm_right a b
    exact Nat.lcm_dvd ha hb

中文:
定理 carmichael_lcm
  条件: (a b : 自然数)
  证明: by
  by_cases! h₀ : a = 0 ∨ b = 0
  · grind [Nat.lcm_eq_zero_iff, map_zero]
  apply dvd_antisymm
  · rw [carmichael_eq_exponent h₀.left, carmichael_eq_exponent h₀.right,
carmichael_eq_exponent lcm_ne_zero h₀.left h₀.right, ← lcm_eq_nat_lcm exponent _,
      ← exponent_prod, ← exponent_eq_of_mulEquiv .prodUnits]
exact exponent_dvd_of_monoidHom _ Units.map_injective ZMod.castHom_injective _
· have ha := carmichael_dvd Nat.dvd_lcm_left a b
have hb := carmichael_dvd Nat.dvd_lcm_right a b
    exact Nat.lcm_dvd ha hb

Depends on / 依赖: Nat.dvd_lcm_left, Nat.dvd_lcm_right, Nat.lcm_dvd, Nat.lcm_eq_zero_iff, Units.map_injective, ZMod.castHom_injective, carmichael_dvd, carmichael_eq_exponent, castHom_injective, dvd_antisymm, dvd_lcm_left, dvd_lcm_right, exponent, exponent_dvd_of_monoidHom, exponent_eq_of_mulEquiv, exponent_prod, lcm_dvd, lcm_eq_nat_lcm, lcm_eq_zero_iff, lcm_ne_zero
-/
theorem carmichael_lcm (a b : Nat) :
    carmichael (Nat.lcm a b) = Nat.lcm (carmichael a) (carmichael b) := by
  by_cases! h₀ : a = 0 ∨ b = 0
  · grind [Nat.lcm_eq_zero_iff, map_zero]
  apply dvd_antisymm
  · rw [carmichael_eq_exponent h₀.left, carmichael_eq_exponent h₀.right,
carmichael_eq_exponent lcm_ne_zero h₀.left h₀.right, ← lcm_eq_nat_lcm exponent _,
      ← exponent_prod, ← exponent_eq_of_mulEquiv .prodUnits]
exact exponent_dvd_of_monoidHom _ Units.map_injective ZMod.castHom_injective _
· have ha := carmichael_dvd Nat.dvd_lcm_left a b
have hb := carmichael_dvd Nat.dvd_lcm_right a b
    exact Nat.lcm_dvd ha hb

/--
theorem `carmichael_mul` / 定理 `carmichael_mul`

English:
theorem carmichael_mul
  given: {a b : Nat} (h : Coprime a b)
  proof: h.lcm_eq_mul ▸ carmichael_lcm ..

中文:
定理 carmichael_mul
  条件: {a b : 自然数} (h : Coprime a b)
  证明: h.lcm_eq_mul ▸ carmichael_lcm ..

Depends on / 依赖: carmichael_lcm, h.lcm_eq_mul, lcm_eq_mul
-/
theorem carmichael_mul {a b : Nat} (h : Coprime a b) :
    carmichael (a * b) = Nat.lcm (carmichael a) (carmichael b) :=
  h.lcm_eq_mul ▸ carmichael_lcm ..

/--
theorem `carmichael_finset_lcm` / 定理 `carmichael_finset_lcm`

English:
theorem carmichael_finset_lcm
  given: {α : Type*} (s : Finset α) (f : α -> Nat)
  proof: by
  classical
  refine s.induction ?_ fun a s ha ih => ?_
.trans exp_eq_one_of_subsingleton · exact carmichael_eq_exponent' 1
  rw [Finset.lcm_insert]; rw [Finset.lcm_insert]; rw [← ih]
  exact carmichael_lcm ..

中文:
定理 carmichael_finset_lcm
  条件: {α : 类型} (s : 有限集 α) (f : α -> 自然数)
  证明: by
  classical
  refine s.induction ?_ fun a s ha ih => ?_
.trans exp_eq_one_of_subsingleton · exact carmichael_eq_exponent' 1
  rw [Finset.lcm_insert]; rw [Finset.lcm_insert]; rw [← ih]
  exact carmichael_lcm ..

Depends on / 依赖: Finset, Finset.lcm_insert, carmichael_eq_exponent, carmichael_lcm, classical, exp_eq_one_of_subsingleton, lcm_insert, s.induction
-/
theorem carmichael_finset_lcm {α : Type*} (s : Finset α) (f : α -> Nat) :
    carmichael (s.lcm f) = s.lcm (carmichael ∘ f) := by
  classical
  refine s.induction ?_ fun a s ha ih => ?_
.trans exp_eq_one_of_subsingleton · exact carmichael_eq_exponent' 1
  rw [Finset.lcm_insert]; rw [Finset.lcm_insert]; rw [← ih]
  exact carmichael_lcm ..

/--
theorem `carmichael_finsetProd` / 定理 `carmichael_finsetProd`

English:
theorem carmichael_finsetProd
  statement: {α : Type*} {s : Finset α} {f : α -> Nat}
  proof: s.lcm_eq_prod h ▸ carmichael_finset_lcm ..

@[deprecated (since := "2026-04-08")] alias carmichael_finset_prod := carmichael_finsetProd

中文:
定理 carmichael_finsetProd
  结论: {α : 类型} {s : 有限集 α} {f : α -> 自然数}
  证明: s.lcm_eq_prod h ▸ carmichael_finset_lcm ..

@[deprecated (since := "2026-04-08")] alias carmichael_finset_prod := carmichael_finsetProd

Depends on / 依赖: carmichael_finset_lcm, lcm_eq_prod, s.lcm_eq_prod
-/
theorem carmichael_finsetProd {α : Type*} {s : Finset α} {f : α -> Nat}
    (h : Set.Pairwise s <| Coprime.onFun f) : carmichael (s.prod f) = s.lcm (carmichael ∘ f) :=
  s.lcm_eq_prod h ▸ carmichael_finset_lcm ..

@[deprecated (since := "2026-04-08")] alias carmichael_finset_prod := carmichael_finsetProd

/--
theorem `carmichael_factorization` / 定理 `carmichael_factorization`

English:
theorem carmichael_factorization
  given: (n : Nat) [NeZero n]
  proof: by
  nth_rw 1 [← n.prod_factorization_pow_eq_self <| NeZero.ne _]
  exact carmichael_finsetProd pairwise_coprime_pow_primeFactors_factorization.set_of_subtype

中文:
定理 carmichael_factorization
  条件: (n : 自然数) [NeZero n]
  证明: by
  nth_rw 1 [← n.prod_factorization_pow_eq_self <| NeZero.ne _]
  exact carmichael_finsetProd pairwise_coprime_pow_primeFactors_factorization.set_of_subtype

Depends on / 依赖: NeZero, NeZero.ne, carmichael_finsetProd, n.prod_factorization_pow_eq_self, nth_rw, pairwise_coprime_pow_primeFactors_factorization, pairwise_coprime_pow_primeFactors_factorization.set_of_subtype, prod_factorization_pow_eq_self, set_of_subtype
-/
theorem carmichael_factorization (n : Nat) [NeZero n] :
    carmichael n = n.primeFactors.lcm fun p => carmichael (p ^ n.factorization p) := by
  nth_rw 1 [← n.prod_factorization_pow_eq_self <| NeZero.ne _]
  exact carmichael_finsetProd pairwise_coprime_pow_primeFactors_factorization.set_of_subtype

/--
theorem `carmichael_two_pow_of_le_two_eq_totient` / 定理 `carmichael_two_pow_of_le_two_eq_totient`

English:
theorem carmichael_two_pow_of_le_two_eq_totient
  given: {n : Nat} (hn : n <= 2)
  proof: by
  rw [carmichael_eq_exponent']; rw [← ZMod.card_units_eq_totient]; rw [Fintype.card_eq_nat_card]
exact IsCyclic.iff_exponent_eq_card.mp .mpr hn ZMod.isCyclic_units_two_pow_iff n

中文:
定理 carmichael_two_pow_of_le_two_eq_totient
  条件: {n : 自然数} (hn : n <= 2)
  证明: by
  rw [carmichael_eq_exponent']; rw [← ZMod.card_units_eq_totient]; rw [Fintype.card_eq_nat_card]
exact IsCyclic.iff_exponent_eq_card.mp .mpr hn ZMod.isCyclic_units_two_pow_iff n

Depends on / 依赖: Fintype, Fintype.card_eq_nat_card, IsCyclic, IsCyclic.iff_exponent_eq_card.mp, ZMod.card_units_eq_totient, ZMod.isCyclic_units_two_pow_iff, card_eq_nat_card, card_units_eq_totient, carmichael_eq_exponent, iff_exponent_eq_card, isCyclic_units_two_pow_iff
-/
theorem carmichael_two_pow_of_le_two_eq_totient {n : Nat} (hn : n <= 2) :
    carmichael (2 ^ n) = (2 ^ n).totient := by
  rw [carmichael_eq_exponent']; rw [← ZMod.card_units_eq_totient]; rw [Fintype.card_eq_nat_card]
exact IsCyclic.iff_exponent_eq_card.mp .mpr hn ZMod.isCyclic_units_two_pow_iff n

/-- Note that `2 ^ (n - 1) = 1` when `n = 0`. -/
@[simp]
/--
theorem `carmichael_two_pow_of_le_two` / 定理 `carmichael_two_pow_of_le_two`

English:
theorem carmichael_two_pow_of_le_two
  given: {n : Nat} (hn : n <= 2)
  proof: by
  rw [carmichael_two_pow_of_le_two_eq_totient hn]
  interval_cases n <;> decide

中文:
定理 carmichael_two_pow_of_le_two
  条件: {n : 自然数} (hn : n <= 2)
  证明: by
  rw [carmichael_two_pow_of_le_two_eq_totient hn]
  interval_cases n <;> decide

Depends on / 依赖: carmichael_two_pow_of_le_two_eq_totient, interval_cases
-/
theorem carmichael_two_pow_of_le_two {n : Nat} (hn : n <= 2) :
    carmichael (2 ^ n) = 2 ^ (n - 1) := by
  rw [carmichael_two_pow_of_le_two_eq_totient hn]
  interval_cases n <;> decide

/-- Note that `2 ^ (n - 2) = 1` when `n ≤ 1`. -/
@[simp]
/--
theorem `carmichael_two_pow_of_ne_two` / 定理 `carmichael_two_pow_of_ne_two`

English:
theorem carmichael_two_pow_of_ne_two
  given: {n : Nat} (hn : n != 2)
  proof: by
  by_cases hn' : n <= 2
  · grind [carmichael_two_pow_of_le_two]
.trans dvd_antisymm ?_ ?_ refine carmichael_eq_exponent' _
  · have hcard : Nat.card (ZMod (2 ^ n))ˣ = 2 ^ (n - 1) := by
      rw [card_eq_fintype_card]; rw [ZMod.card_units_eq_totient]; rw [totient_prime_pow prime_two <| by lia]; rw [Nat.add_one_sub_one]; rw [mul_one]
.mp hcard ▸ Group.exponent_dvd_nat_card have ⟨k, hk, h⟩ := dvd_prime_pow prime_two
have := IsCyclic.iff_exponent_eq_card.not.mp .not.mpr hn' ZMod.isCyclic_units_two_pow_iff n
    exact h ▸ Nat.pow_dvd_pow 2 (by grind)
· let five : (ZMod (2 ^ n))ˣ := ZMod.unitOfCoprime 5 gcd_pow_right_of_gcd_eq_one rfl
    rw [← ZMod.orderOf_five (n - 2)]; rw [show n - 2 + 2 = n by lia]; rw [show (5 : ZMod (2 ^ n)) = five by rfl]; rw [orderOf_units]
    exact order_dvd_exponent five

中文:
定理 carmichael_two_pow_of_ne_two
  条件: {n : 自然数} (hn : n != 2)
  证明: by
  by_cases hn' : n <= 2
  · grind [carmichael_two_pow_of_le_two]
.trans dvd_antisymm ?_ ?_ refine carmichael_eq_exponent' _
  · have hcard : Nat.card (ZMod (2 ^ n))ˣ = 2 ^ (n - 1) := by
      rw [card_eq_fintype_card]; rw [ZMod.card_units_eq_totient]; rw [totient_prime_pow prime_two <| by lia]; rw [Nat.add_one_sub_one]; rw [mul_one]
.mp hcard ▸ Group.exponent_dvd_nat_card have ⟨k, hk, h⟩ := dvd_prime_pow prime_two
have := IsCyclic.iff_exponent_eq_card.not.mp .not.mpr hn' ZMod.isCyclic_units_two_pow_iff n
    exact h ▸ Nat.pow_dvd_pow 2 (by grind)
· let five : (ZMod (2 ^ n))ˣ := ZMod.unitOfCoprime 5 gcd_pow_right_of_gcd_eq_one rfl
    rw [← ZMod.orderOf_five (n - 2)]; rw [show n - 2 + 2 = n by lia]; rw [show (5 : ZMod (2 ^ n)) = five by rfl]; rw [orderOf_units]
    exact order_dvd_exponent five

Depends on / 依赖: Group.exponent_dvd_nat_card, IsCyclic, IsCyclic.iff_exponent_eq_card.not.mp, Nat.add_one_sub_one, Nat.card, ZMod.card_units_eq_totient, ZMod.isCyclic_units_two_pow_iff, add_one_sub_one, card_eq_fintype_card, card_units_eq_totient, carmichael_eq_exponent, carmichael_two_pow_of_le_two, dvd_antisymm, dvd_prime_pow, exponent_dvd_nat_card, iff_exponent_eq_card, isCyclic_units_two_pow_iff, mul_one, not.mpr, prime_two
-/
theorem carmichael_two_pow_of_ne_two {n : Nat} (hn : n != 2) :
    carmichael (2 ^ n) = 2 ^ (n - 2) := by
  by_cases hn' : n <= 2
  · grind [carmichael_two_pow_of_le_two]
.trans dvd_antisymm ?_ ?_ refine carmichael_eq_exponent' _
  · have hcard : Nat.card (ZMod (2 ^ n))ˣ = 2 ^ (n - 1) := by
      rw [card_eq_fintype_card]; rw [ZMod.card_units_eq_totient]; rw [totient_prime_pow prime_two <| by lia]; rw [Nat.add_one_sub_one]; rw [mul_one]
.mp hcard ▸ Group.exponent_dvd_nat_card have ⟨k, hk, h⟩ := dvd_prime_pow prime_two
have := IsCyclic.iff_exponent_eq_card.not.mp .not.mpr hn' ZMod.isCyclic_units_two_pow_iff n
    exact h ▸ Nat.pow_dvd_pow 2 (by grind)
· let five : (ZMod (2 ^ n))ˣ := ZMod.unitOfCoprime 5 gcd_pow_right_of_gcd_eq_one rfl
    rw [← ZMod.orderOf_five (n - 2)]; rw [show n - 2 + 2 = n by lia]; rw [show (5 : ZMod (2 ^ n)) = five by rfl]; rw [orderOf_units]
    exact order_dvd_exponent five

/--
theorem `two_mul_carmichael_two_pow_of_three_le_eq_totient` / 定理 `two_mul_carmichael_two_pow_of_three_le_eq_totient`

English:
theorem two_mul_carmichael_two_pow_of_three_le_eq_totient
  given: {n : Nat} (hn : 3 <= n)
  proof: by
  rw [carmichael_two_pow_of_ne_two]; rw [← pow_succ']; rw [totient_prime_pow prime_two] <;>
  · #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc

@[simp]

中文:
定理 two_mul_carmichael_two_pow_of_three_le_eq_totient
  条件: {n : 自然数} (hn : 3 <= n)
  证明: by
  rw [carmichael_two_pow_of_ne_two]; rw [← pow_succ']; rw [totient_prime_pow prime_two] <;>
  · #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc

@[simp]

Depends on / 依赖: adaptation_note, carmichael_two_pow_of_ne_two, combination, enable, github, github.com, leanprover, pow_succ, prime_two, theory, through, totient_prime_pow
-/
theorem two_mul_carmichael_two_pow_of_three_le_eq_totient {n : Nat} (hn : 3 <= n) :
    2 * carmichael (2 ^ n) = (2 ^ n).totient := by
  rw [carmichael_two_pow_of_ne_two]; rw [← pow_succ']; rw [totient_prime_pow prime_two] <;>
  · #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc

@[simp]
/--
theorem `carmichael_pow_of_prime_ne_two` / 定理 `carmichael_pow_of_prime_ne_two`

English:
theorem carmichael_pow_of_prime_ne_two
  given: {p : Nat} (n : Nat) (hp : p.Prime) (hp₂ : p != 2)
  proof: by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [carmichael_eq_exponent']; rw [← ZMod.card_units_eq_totient]; rw [Fintype.card_eq_nat_card]
exact IsCyclic.iff_exponent_eq_card.mp ZMod.isCyclic_units_of_prime_pow p hp hp₂ n

中文:
定理 carmichael_pow_of_prime_ne_two
  条件: {p : 自然数} (n : 自然数) (hp : p.素) (hp₂ : p != 2)
  证明: by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [carmichael_eq_exponent']; rw [← ZMod.card_units_eq_totient]; rw [Fintype.card_eq_nat_card]
exact IsCyclic.iff_exponent_eq_card.mp ZMod.isCyclic_units_of_prime_pow p hp hp₂ n

Depends on / 依赖: Fintype, Fintype.card_eq_nat_card, IsCyclic, IsCyclic.iff_exponent_eq_card.mp, NeZero, ZMod.card_units_eq_totient, ZMod.isCyclic_units_of_prime_pow, card_eq_nat_card, card_units_eq_totient, carmichael_eq_exponent, hp.ne_zero, iff_exponent_eq_card, isCyclic_units_of_prime_pow, ne_zero
-/
theorem carmichael_pow_of_prime_ne_two {p : Nat} (n : Nat) (hp : p.Prime) (hp₂ : p != 2) :
    carmichael (p ^ n) = (p ^ n).totient := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [carmichael_eq_exponent']; rw [← ZMod.card_units_eq_totient]; rw [Fintype.card_eq_nat_card]
exact IsCyclic.iff_exponent_eq_card.mp ZMod.isCyclic_units_of_prime_pow p hp hp₂ n

end ArithmeticFunction
