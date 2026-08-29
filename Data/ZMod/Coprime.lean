/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Coprimality and vanishing

We show that for prime `p`, the image of an integer `a` in `ZMod p` vanishes if and only if
`a` and `p` are not coprime.
-/

public section

assert_not_exists TwoSidedIdeal

namespace ZMod

/--
theorem `eq_zero_iff_gcd_ne_one` / 定理 `eq_zero_iff_gcd_ne_one`

English:
theorem eq_zero_iff_gcd_ne_one
  given: {a : Int} {p : Nat} [pp : Fact p.Prime]
  proof: by
  rw [Ne]; rw [Int.gcd_comm]; rw [← Int.isCoprime_iff_gcd_eq_one]; rw [(Nat.prime_iff_prime_int.1 pp.1).coprime_iff_not_dvd]; rw [Classical.not_not]; rw [intCast_zmod_eq_zero_iff_dvd]

中文:
定理 eq_zero_iff_gcd_ne_one
  条件: {a : 整数} {p : 自然数} [pp : Fact p.Prime]
  证明: by
  rw [Ne]; rw [Int.gcd_comm]; rw [← Int.isCoprime_iff_gcd_eq_one]; rw [(Nat.prime_iff_prime_int.1 pp.1).coprime_iff_not_dvd]; rw [Classical.not_not]; rw [intCast_zmod_eq_zero_iff_dvd]

Depends on / 依赖: Classical, Classical.not_not, Int.gcd_comm, Int.isCoprime_iff_gcd_eq_one, Nat.prime_iff_prime_int, coprime_iff_not_dvd, gcd_comm, intCast_zmod_eq_zero_iff_dvd, isCoprime_iff_gcd_eq_one, not_not, prime_iff_prime_int
-/
theorem eq_zero_iff_gcd_ne_one {a : Int} {p : Nat} [pp : Fact p.Prime] :
    (a : ZMod p) = 0 ↔ a.gcd p != 1 := by
  rw [Ne]; rw [Int.gcd_comm]; rw [← Int.isCoprime_iff_gcd_eq_one]; rw [(Nat.prime_iff_prime_int.1 pp.1).coprime_iff_not_dvd]; rw [Classical.not_not]; rw [intCast_zmod_eq_zero_iff_dvd]

/--
theorem `ne_zero_of_gcd_eq_one` / 定理 `ne_zero_of_gcd_eq_one`

English:
theorem ne_zero_of_gcd_eq_one
  given: {a : Int} {p : Nat} (pp : p.Prime) (h : a.gcd p = 1)
  statement: (a : ZMod p) != 0
  proof: mt (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mp (Classical.not_not.mpr h)

中文:
定理 ne_zero_of_gcd_eq_one
  条件: {a : 整数} {p : 自然数} (pp : p.Prime) (h : a.gcd p = 1)
  结论: (a : ZMod p) != 0
  证明: mt (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mp (Classical.not_not.mpr h)

Depends on / 依赖: Classical, Classical.not_not.mpr, eq_zero_iff_gcd_ne_one, not_not
-/
theorem ne_zero_of_gcd_eq_one {a : Int} {p : Nat} (pp : p.Prime) (h : a.gcd p = 1) : (a : ZMod p) != 0 :=
  mt (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mp (Classical.not_not.mpr h)

/--
theorem `eq_zero_of_gcd_ne_one` / 定理 `eq_zero_of_gcd_ne_one`

English:
theorem eq_zero_of_gcd_ne_one
  given: {a : Int} {p : Nat} (pp : p.Prime) (h : a.gcd p != 1)
  statement: (a : ZMod p) = 0
  proof: (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mpr h

中文:
定理 eq_zero_of_gcd_ne_one
  条件: {a : 整数} {p : 自然数} (pp : p.Prime) (h : a.gcd p != 1)
  结论: (a : ZMod p) = 0
  证明: (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mpr h

Depends on / 依赖: eq_zero_iff_gcd_ne_one
-/
theorem eq_zero_of_gcd_ne_one {a : Int} {p : Nat} (pp : p.Prime) (h : a.gcd p != 1) : (a : ZMod p) = 0 :=
  (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mpr h

end ZMod
