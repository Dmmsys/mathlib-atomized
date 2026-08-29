/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Nat.Factors
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Unique factorization of natural numbers

## Main definitions

* `Nat.instUniqueFactorizationMonoid`: the natural numbers have unique factorization
-/

public section

assert_not_exists Field

namespace Nat

/--
Instance `instWfDvdMonoid` / 实例 `instWfDvdMonoid`

English:
instance instWfDvdMonoid
  signature: : WfDvdMonoid Nat where
  body: by
    refine RelHomClass.wellFounded
      (⟨fun x : Nat => if x = 0 then (⊤ : Nat∞) else x, ?_⟩ : DvdNotUnit ->r (· < ·)) wellFounded_lt
    intro a b h
    rcases a with - | a
    · exfalso
      revert h
      simp [DvdNotUnit]
    cases b
    · simp
    obtain ⟨h1, h2⟩ := dvd_and_not_dvd_iff.2 

中文:
实例 instWfDvdMonoid
  签名: : WfDvdMonoid 自然数 where
  定义体: by
    refine RelHomClass.wellFounded
      (⟨fun x : Nat => if x = 0 then (⊤ : Nat∞) else x, ?_⟩ : DvdNotUnit ->r (· < ·)) wellFounded_lt
    intro a b h
    rcases a with - | a
    · exfalso
      revert h
      simp [DvdNotUnit]
    cases b
    · simp
    obtain ⟨h1, h2⟩ := dvd_and_not_dvd_iff.2 

Depends on / 依赖: DvdNotUnit, Nat.le_of_dvd, Nat.succ_pos, RelHomClass, RelHomClass.wellFounded, cast_lt, dvd_and_not_dvd_iff, if_false, le_of_dvd, lt_of_le_of_ne, revert, succ_ne_zero, succ_pos, wellFounded, wellFounded_lt
-/
instance instWfDvdMonoid : WfDvdMonoid Nat where
  wf := by
    refine RelHomClass.wellFounded
      (⟨fun x : Nat => if x = 0 then (⊤ : Nat∞) else x, ?_⟩ : DvdNotUnit ->r (· < ·)) wellFounded_lt
    intro a b h
    rcases a with - | a
    · exfalso
      revert h
      simp [DvdNotUnit]
    cases b
    · simp
    obtain ⟨h1, h2⟩ := dvd_and_not_dvd_iff.2 h
    simp only [succ_ne_zero, cast_lt, if_false]
    refine lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos _) h1) fun con => h2 ?_
    rw [con]

/--
Instance `instUniqueFactorizationMonoid` / 实例 `instUniqueFactorizationMonoid`

English:
instance instUniqueFactorizationMonoid
  signature: : UniqueFactorizationMonoid Nat where
  body: Nat.irreducible_iff_prime

中文:
实例 instUniqueFactorizationMonoid
  签名: : UniqueFactorizationMonoid 自然数 where
  定义体: Nat.irreducible_iff_prime

Depends on / 依赖: Nat.irreducible_iff_prime, irreducible_iff_prime
-/
instance instUniqueFactorizationMonoid : UniqueFactorizationMonoid Nat where
  irreducible_iff_prime := Nat.irreducible_iff_prime

open UniqueFactorizationMonoid

/--
lemma `factors_eq` / 引理 `factors_eq`

English:
lemma factors_eq
  statement: forall n : Nat, normalizedFactors n = n.primeFactorsList

中文:
引理 factors_eq
  结论: 对任意 n : 自然数, normalizedFactors n = n.primeFactorsList
-/
lemma factors_eq : forall n : Nat, normalizedFactors n = n.primeFactorsList
  | 0 => by simp
  | n + 1 => by
    rw [← Multiset.rel_eq]; rw [← associated_eq_eq]
    apply UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor _
    · rw [Multiset.prod_coe, Nat.prod_primeFactorsList n.succ_ne_zero]
      exact prod_normalizedFactors n.succ_ne_zero
    · intro x hx
      rw [Nat.irreducible_iff_prime]; rw [← Nat.prime_iff]
      exact Nat.prime_of_mem_primeFactorsList hx

/--
lemma `factors_multiset_prod_of_irreducible` / 引理 `factors_multiset_prod_of_irreducible`

English:
lemma factors_multiset_prod_of_irreducible
  given: {s : Multiset Nat} (h : forall x : Nat, x in s -> Irreducible x)
  proof: by
  rw [← Multiset.rel_eq]; rw [← associated_eq_eq]
  apply UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor h
    (prod_normalizedFactors _)
  rw [Ne]; rw [Multiset.prod_eq_zero_iff]
  exact fun con => not_irreducible_zero (h 0 con)

中文:
引理 factors_multiset_prod_of_irreducible
  条件: {s : Multiset 自然数} (h : 对任意 x : 自然数, x in s -> Irreducible x)
  证明: by
  rw [← Multiset.rel_eq]; rw [← associated_eq_eq]
  apply UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor h
    (prod_normalizedFactors _)
  rw [Ne]; rw [Multiset.prod_eq_zero_iff]
  exact fun con => not_irreducible_zero (h 0 con)

Depends on / 依赖: Multiset, Multiset.prod_eq_zero_iff, Multiset.rel_eq, UniqueFactorizationMonoid, UniqueFactorizationMonoid.factors_unique, associated_eq_eq, factors_unique, irreducible_of_normalized_factor, not_irreducible_zero, prod_eq_zero_iff, prod_normalizedFactors, rel_eq
-/
lemma factors_multiset_prod_of_irreducible {s : Multiset Nat} (h : forall x : Nat, x in s -> Irreducible x) :
    normalizedFactors s.prod = s := by
  rw [← Multiset.rel_eq]; rw [← associated_eq_eq]
  apply UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor h
    (prod_normalizedFactors _)
  rw [Ne]; rw [Multiset.prod_eq_zero_iff]
  exact fun con => not_irreducible_zero (h 0 con)

end Nat
