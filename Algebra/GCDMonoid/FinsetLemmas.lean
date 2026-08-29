/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# `Finset.lcm` lemmas

## Tags

finset, lcm, prod, coprime, Rat.den
-/

public section

namespace Finset

variable {ι α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

/--
theorem `lcm_dvd_prod` / 定理 `lcm_dvd_prod`

English:
theorem lcm_dvd_prod
  given: (s : Finset ι) (f : ι -> α)
  statement: s.lcm f ∣ s.prod f
  proof: lcm_dvd fun _ => dvd_prod_of_mem _

中文:
定理 lcm_dvd_prod
  条件: (s : 有限集 ι) (f : ι -> α)
  结论: s.最小公倍数 f ∣ s.乘积 f
  证明: lcm_dvd fun _ => dvd_prod_of_mem _

Depends on / 依赖: dvd_prod_of_mem, lcm_dvd
-/
theorem lcm_dvd_prod (s : Finset ι) (f : ι -> α) : s.lcm f ∣ s.prod f :=
  lcm_dvd fun _ => dvd_prod_of_mem _

/--
theorem `associated_lcm_prod` / 定理 `associated_lcm_prod`

English:
theorem associated_lcm_prod
  given: {s : Finset ι} {f : ι -> α} (h : Set.Pairwise s <| IsRelPrime.onFun f)
  proof: associated_of_dvd_dvd (s.lcm_dvd_prod f) (s.prod_dvd_of_isRelPrime h fun _ => dvd_lcm)

中文:
定理 associated_lcm_prod
  条件: {s : 有限集 ι} {f : ι -> α} (h : 集合.两两 s <| IsRelPrime.onFun f)
  证明: associated_of_dvd_dvd (s.lcm_dvd_prod f) (s.prod_dvd_of_isRelPrime h fun _ => dvd_lcm)

Depends on / 依赖: associated_of_dvd_dvd, dvd_lcm, lcm_dvd_prod, prod_dvd_of_isRelPrime, s.lcm_dvd_prod, s.prod_dvd_of_isRelPrime
-/
theorem associated_lcm_prod {s : Finset ι} {f : ι -> α} (h : Set.Pairwise s <| IsRelPrime.onFun f) :
    Associated (s.lcm f) (s.prod f) :=
  associated_of_dvd_dvd (s.lcm_dvd_prod f) (s.prod_dvd_of_isRelPrime h fun _ => dvd_lcm)

/--
theorem `lcm_eq_prod` / 定理 `lcm_eq_prod`

English:
theorem lcm_eq_prod
  given: {s : Finset ι} {f : ι -> Nat} (h : Set.Pairwise s <| Nat.Coprime.onFun f)
  proof: by
  rw [show Nat.Coprime = IsRelPrime by ext; exact Nat.coprime_iff_isRelPrime] at h
.eq_of_normalized (normalize_eq _) (normalize_eq _) exact associated_lcm_prod h

中文:
定理 lcm_eq_prod
  条件: {s : 有限集 ι} {f : ι -> 自然数} (h : 集合.两两 s <| 自然数.Coprime.onFun f)
  证明: by
  rw [show Nat.Coprime = IsRelPrime by ext; exact Nat.coprime_iff_isRelPrime] at h
.eq_of_normalized (normalize_eq _) (normalize_eq _) exact associated_lcm_prod h

Depends on / 依赖: Coprime, IsRelPrime, Nat.Coprime, Nat.coprime_iff_isRelPrime, associated_lcm_prod, coprime_iff_isRelPrime, eq_of_normalized, normalize_eq
-/
theorem lcm_eq_prod {s : Finset ι} {f : ι -> Nat} (h : Set.Pairwise s <| Nat.Coprime.onFun f) :
    s.lcm f = s.prod f := by
  rw [show Nat.Coprime = IsRelPrime by ext; exact Nat.coprime_iff_isRelPrime] at h
.eq_of_normalized (normalize_eq _) (normalize_eq _) exact associated_lcm_prod h

/--
theorem `factorization_lcm` / 定理 `factorization_lcm`

English:
theorem factorization_lcm
  given: {f : ι -> Nat} {s : Finset ι} (hf : forall k in s, f k != 0) (p : Nat)
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ _ => simp_all [lcm_eq_nat_lcm, Nat.factorization_lcm]

中文:
定理 factorization_lcm
  条件: {f : ι -> 自然数} {s : 有限集 ι} (hf : 对任意 k in s, f k != 0) (p : 自然数)
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ _ => simp_all [lcm_eq_nat_lcm, Nat.factorization_lcm]

Depends on / 依赖: Finset, Finset.induction, Nat.factorization_lcm, classical, factorization_lcm, insert, lcm_eq_nat_lcm
-/
theorem factorization_lcm {f : ι -> Nat} {s : Finset ι} (hf : forall k in s, f k != 0) (p : Nat) :
    (s.lcm f).factorization p = s.sup fun a => (f a).factorization p := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ _ => simp_all [lcm_eq_nat_lcm, Nat.factorization_lcm]

namespace Rat

/--
theorem `den_sum_dvd_lcm_den` / 定理 `den_sum_dvd_lcm_den`

English:
theorem den_sum_dvd_lcm_den
  given: {ι : Type*} (s : Finset ι) (f : ι -> Rat)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ has ih =>
    rw [Finset.sum_insert has]; rw [Finset.lcm_insert]
    exact (Rat.add_den_dvd_lcm _ _).trans (lcm_dvd_lcm dvd_rfl ih)

中文:
定理 den_sum_dvd_lcm_den
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> 有理数)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ has ih =>
    rw [Finset.sum_insert has]; rw [Finset.lcm_insert]
    exact (Rat.add_den_dvd_lcm _ _).trans (lcm_dvd_lcm dvd_rfl ih)

Depends on / 依赖: Finset, Finset.induction_on, Finset.lcm_insert, Finset.sum_insert, Rat.add_den_dvd_lcm, add_den_dvd_lcm, classical, dvd_rfl, induction_on, insert, lcm_dvd_lcm, lcm_insert, sum_insert
-/
theorem den_sum_dvd_lcm_den {ι : Type*} (s : Finset ι) (f : ι -> Rat) :
    (∑ i in s, f i).den ∣ s.lcm (fun i => (f i).den) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ has ih =>
    rw [Finset.sum_insert has]; rw [Finset.lcm_insert]
    exact (Rat.add_den_dvd_lcm _ _).trans (lcm_dvd_lcm dvd_rfl ih)

/--
theorem `den_sum_dvd_prod_den` / 定理 `den_sum_dvd_prod_den`

English:
theorem den_sum_dvd_prod_den
  given: {ι : Type*} (s : Finset ι) (f : ι -> Rat)
  proof: (den_sum_dvd_lcm_den s f).trans s.lcm_dvd_prod _

中文:
定理 den_sum_dvd_prod_den
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> 有理数)
  证明: (den_sum_dvd_lcm_den s f).trans s.lcm_dvd_prod _

Depends on / 依赖: den_sum_dvd_lcm_den, lcm_dvd_prod, s.lcm_dvd_prod
-/
theorem den_sum_dvd_prod_den {ι : Type*} (s : Finset ι) (f : ι -> Rat) :
    (∑ i in s, f i).den ∣ ∏ i in s, (f i).den :=
(den_sum_dvd_lcm_den s f).trans s.lcm_dvd_prod _

/--
theorem `den_prod_dvd_prod_den` / 定理 `den_prod_dvd_prod_den`

English:
theorem den_prod_dvd_prod_den
  given: {ι : Type*} (s : Finset ι) (f : ι -> Rat)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ has ih =>
    simp_rw [Finset.prod_insert has]
exact (Rat.mul_den_dvd ..).trans mul_dvd_mul_left _ ih

中文:
定理 den_prod_dvd_prod_den
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> 有理数)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ has ih =>
    simp_rw [Finset.prod_insert has]
exact (Rat.mul_den_dvd ..).trans mul_dvd_mul_left _ ih

Depends on / 依赖: Finset, Finset.induction_on, Finset.prod_insert, Rat.mul_den_dvd, classical, induction_on, insert, mul_den_dvd, mul_dvd_mul_left, prod_insert, simp_rw
-/
theorem den_prod_dvd_prod_den {ι : Type*} (s : Finset ι) (f : ι -> Rat) :
    (∏ i in s, f i).den ∣ ∏ i in s, (f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ has ih =>
    simp_rw [Finset.prod_insert has]
exact (Rat.mul_den_dvd ..).trans mul_dvd_mul_left _ ih

end Rat

end Finset
