/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Teichmuller Series

Let `R` be a characteristic `p` perfect ring. In this file, we show that
every element `x` of the Witt vectors `𝕎 R` can be written as the
(`p`-adic) summation of Teichmuller series, namely
`∑ i, (teichmuller p
        (((frobeniusEquiv R p).symm ^ i) (x.coeff i)) * p ^ i)`

## Main theorems

* `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff` : `p ^ (n + 1)` divides
  `x` minus the summation of the first `n + 1` terms of the Teichmuller series.
* `WittVector.eq_of_apply_teichmuller_eq` : Given a ring `S` such that `p` is nilpotent in `S`
  and two ring maps `f g : 𝕎 R →+* S`, if they coincide on the teichmuller representatives,
  then they are equal.

## TODO
Show that the Teichmuller series is unique.
-/

public section

open Ideal Quotient
namespace WittVector

variable {p : Nat} [hp : Fact (Nat.Prime p)]

local notation "𝕎" => WittVector p

variable {R : Type*} [CommRing R]

/--
theorem `sum_coeff_eq_coeff_sum` / 定理 `sum_coeff_eq_coeff_sum`

English:
theorem sum_coeff_eq_coeff_sum
  statement: {α : Type*} {S : Finset α} (x : α -> 𝕎 R)
  proof: by
  classical
  induction S using Finset.induction generalizing n with
  | empty =>
    simp
  | insert a S' ha hind =>
    have : (forall (n : Nat), Subsingleton {r | r in S' ∧ (x r).coeff n != 0}) := by
      refine fun n => ⟨fun b c => ?_⟩
      ext
exact congrArg (fun x => x.1)
          (h n).

中文:
定理 sum_coeff_eq_coeff_sum
  结论: {α : 类型} {S : 有限集 α} (x : α -> 𝕎 R)
  证明: by
  classical
  induction S using Finset.induction generalizing n with
  | empty =>
    simp
  | insert a S' ha hind =>
    have : (forall (n : Nat), Subsingleton {r | r in S' ∧ (x r).coeff n != 0}) := by
      refine fun n => ⟨fun b c => ?_⟩
      ext
exact congrArg (fun x => x.1)
          (h n).

Depends on / 依赖: Finset, Finset.induction, Finset.sum_insert, Subsingleton, classical, generalizing, insert, not_false_eq_true, replace, subset_insert, sum_insert
-/
theorem sum_coeff_eq_coeff_sum {α : Type*} {S : Finset α} (x : α -> 𝕎 R)
    (h : forall (n : Nat), Subsingleton {r | r in S ∧ (x r).coeff n != 0}) (n : Nat) :
    (∑ s in S, x s).coeff n = ∑ (s in S), (x s).coeff n := by
  classical
  induction S using Finset.induction generalizing n with
  | empty =>
    simp
  | insert a S' ha hind =>
    have : (forall (n : Nat), Subsingleton {r | r in S' ∧ (x r).coeff n != 0}) := by
      refine fun n => ⟨fun b c => ?_⟩
      ext
exact congrArg (fun x => x.1)
          (h n).allEq ⟨b.1, S'.subset_insert a b.2.1, b.2.2⟩ ⟨c.1, S'.subset_insert a c.2.1, c.2.2⟩
    replace hind := hind this
    simp only [ha, not_false_eq_true, Finset.sum_insert]
    have : forall (n : Nat), (x a).coeff n = 0 ∨ (∑ s in S', x s).coeff n = 0 := by
      simp only [hind]
      by_contra! ⟨m, hma, hmS'⟩
      have := Finset.sum_eq_zero.mt hmS'
      push Not at this
      choose b hb hb' using this
      have : a = b :=
congrArg (fun x => x.1)
          (h m).allEq ⟨a, S'.mem_insert_self a, hma⟩ ⟨b, S'.mem_insert_of_mem hb, hb'⟩
      exact ha (this ▸ hb)
    rw [coeff_add_of_disjoint n _ _ this]; rw [hind n]

variable [CharP R p]

@[simp]
/--
theorem `teichmuller_mul_pow_coeff` / 定理 `teichmuller_mul_pow_coeff`

English:
theorem teichmuller_mul_pow_coeff
  given: (n : Nat) (x : R)
  proof: by
  simpa using WittVector.mul_pow_charP_coeff_succ (teichmuller p x) (m := 0)

中文:
定理 teichmuller_mul_pow_coeff
  条件: (n : 自然数) (x : R)
  证明: by
  simpa using WittVector.mul_pow_charP_coeff_succ (teichmuller p x) (m := 0)

Depends on / 依赖: WittVector, WittVector.mul_pow_charP_coeff_succ, mul_pow_charP_coeff_succ, teichmuller
-/
theorem teichmuller_mul_pow_coeff (n : Nat) (x : R) :
    (teichmuller p x * p ^ n).coeff n = x ^ p ^ n := by
  simpa using WittVector.mul_pow_charP_coeff_succ (teichmuller p x) (m := 0)

/--
theorem `teichmuller_mul_pow_coeff_of_ne` / 定理 `teichmuller_mul_pow_coeff_of_ne`

English:
theorem teichmuller_mul_pow_coeff_of_ne
  statement: (x : R)
  proof: by
  cases Nat.lt_or_lt_of_ne h with
  | inl h =>
    exact WittVector.mul_pow_charP_coeff_zero (teichmuller p x) h
  | inr h =>
    rw [← Nat.sub_add_cancel h.le]; rw [WittVector.mul_pow_charP_coeff_succ (teichmuller p x)]; rw [WittVector.teichmuller_coeff_pos p x (m - n) (Nat.zero_lt_sub_of_lt h)]

中文:
定理 teichmuller_mul_pow_coeff_of_ne
  结论: (x : R)
  证明: by
  cases Nat.lt_or_lt_of_ne h with
  | inl h =>
    exact WittVector.mul_pow_charP_coeff_zero (teichmuller p x) h
  | inr h =>
    rw [← Nat.sub_add_cancel h.le]; rw [WittVector.mul_pow_charP_coeff_succ (teichmuller p x)]; rw [WittVector.teichmuller_coeff_pos p x (m - n) (Nat.zero_lt_sub_of_lt h)]

Depends on / 依赖: Fact.out, Nat.Prime.ne_zero, Nat.lt_or_lt_of_ne, Nat.sub_add_cancel, Nat.zero_lt_sub_of_lt, WittVector, WittVector.mul_pow_charP_coeff_succ, WittVector.mul_pow_charP_coeff_zero, WittVector.teichmuller_coeff_pos, h.le, lt_or_lt_of_ne, mul_pow_charP_coeff_succ, mul_pow_charP_coeff_zero, ne_zero, sub_add_cancel, teichmuller, teichmuller_coeff_pos, zero_lt_sub_of_lt, zero_pow
-/
theorem teichmuller_mul_pow_coeff_of_ne (x : R)
    {m n : Nat} (h : m != n) : (teichmuller p x * p ^ n).coeff m = 0 := by
  cases Nat.lt_or_lt_of_ne h with
  | inl h =>
    exact WittVector.mul_pow_charP_coeff_zero (teichmuller p x) h
  | inr h =>
    rw [← Nat.sub_add_cancel h.le]; rw [WittVector.mul_pow_charP_coeff_succ (teichmuller p x)]; rw [WittVector.teichmuller_coeff_pos p x (m - n) (Nat.zero_lt_sub_of_lt h)]; rw [zero_pow]
    simp [Nat.Prime.ne_zero Fact.out]

variable [PerfectRing R p]

/--
theorem `dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff` / 定理 `dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff`

English:
theorem dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff
  given: (x : 𝕎 R) (n : Nat)
  proof: by
  rw [← Ideal.mem_span_singleton]; rw [mem_span_p_pow_iff_le_coeff_eq_zero]; rw [← le_coeff_eq_iff_le_sub_coeff_eq_zero]
  intro i hi
  rw [WittVector.sum_coeff_eq_coeff_sum]
  · rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hi))]
    let g := fun x : Na

中文:
定理 dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff
  条件: (x : 𝕎 R) (n : 自然数)
  证明: by
  rw [← Ideal.mem_span_singleton]; rw [mem_span_p_pow_iff_le_coeff_eq_zero]; rw [← le_coeff_eq_iff_le_sub_coeff_eq_zero]
  intro i hi
  rw [WittVector.sum_coeff_eq_coeff_sum]
  · rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hi))]
    let g := fun x : Na

Depends on / 依赖: Finset, Finset.mem_Iic, Finset.mem_Iic.mpr, Finset.mem_sdiff, Finset.mem_singleton, Finset.sum_congr, Finset.sum_eq_add_sum_sdiff_singleton_of_mem, Ideal.mem_span_singleton, Nat.lt_succ_iff.mp, Ne.intro, WittVector, WittVector.sum_coeff_eq_coeff_sum, le_coeff_eq_iff_le_sub_coeff_eq_zero, lt_succ_iff, mem_Iic, mem_sdiff, mem_singleton, mem_span_p_pow_iff_le_coeff_eq_zero, mem_span_singleton, sum_coeff_eq_coeff_sum
-/
theorem dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (x : 𝕎 R) (n : Nat) :
    (p : 𝕎 R) ^ (n + 1) ∣ x - ∑ (i <= n), (teichmuller p
        (((_root_.frobeniusEquiv R p).symm ^ i) (x.coeff i)) * p ^ i) := by
  rw [← Ideal.mem_span_singleton]; rw [mem_span_p_pow_iff_le_coeff_eq_zero]; rw [← le_coeff_eq_iff_le_sub_coeff_eq_zero]
  intro i hi
  rw [WittVector.sum_coeff_eq_coeff_sum]
  · rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hi))]
    let g := fun x : Nat => (0 : R)
    rw [Finset.sum_congr rfl (g := g)]
    · simp [g]
    · intro b hb
      simp only [Finset.mem_sdiff, Finset.mem_Iic, Finset.mem_singleton] at hb
      exact teichmuller_mul_pow_coeff_of_ne _ (Ne.intro hb.2).symm
  · refine fun n => ⟨fun ⟨a, _, ha⟩ ⟨b, _, hb⟩ => ?_⟩
    ext
    dsimp only [ne_eq, Set.mem_ofPred_eq]
    rw [← Not.imp_symm (teichmuller_mul_pow_coeff_of_ne _) ha]
    exact Not.imp_symm (teichmuller_mul_pow_coeff_of_ne _) hb

/--
theorem `eq_of_apply_teichmuller_eq` / 定理 `eq_of_apply_teichmuller_eq`

English:
theorem eq_of_apply_teichmuller_eq
  proof: by
  obtain ⟨n, hn⟩ := hp
  ext x
  obtain ⟨c, hc⟩ := (dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n)
  calc
    f x = f (x - ∑ (i <= n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) + f (∑ (i <= n), teichmuller p
        (((_root_.frobeniusEquiv R p)

中文:
定理 eq_of_apply_teichmuller_eq
  证明: by
  obtain ⟨n, hn⟩ := hp
  ext x
  obtain ⟨c, hc⟩ := (dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n)
  calc
    f x = f (x - ∑ (i <= n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) + f (∑ (i <= n), teichmuller p
        (((_root_.frobeniusEquiv R p)

Depends on / 依赖: _root_, _root_.frobeniusEq, _root_.frobeniusEquiv, dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff, frobeniusEq, frobeniusEquiv, pow_succ, teichmuller, x.coeff
-/
theorem eq_of_apply_teichmuller_eq
    {S : Type*} [CommRing S] (f g : 𝕎 R ->+* S) (hp : IsNilpotent (p : S))
    (h : forall (x : R), f (teichmuller p x) = g (teichmuller p x)) : f = g := by
  obtain ⟨n, hn⟩ := hp
  ext x
  obtain ⟨c, hc⟩ := (dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n)
  calc
    f x = f (x - ∑ (i <= n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) + f (∑ (i <= n), teichmuller p
        (((_root_.frobeniusEquiv R p).symm ^ i) (x.coeff i)) * p ^ i) := by simp
    _ = ∑ (i <= n), f (teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i))) * p ^ i := by rw [hc]; simp [pow_succ, hn]
    _ = ∑ (i <= n), g (teichmuller p
        (((_root_.frobeniusEquiv R p).symm ^ i) (x.coeff i))) * p ^ i := by simp [h]
    _ = g (x - ∑ (i <= n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) + g (∑ (i <= n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) := by rw [hc]; simp [pow_succ, hn]
    _ = g x := by simp

end WittVector
