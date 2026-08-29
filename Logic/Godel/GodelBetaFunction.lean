/-
Copyright (c) 2023 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Gödel's Beta Function Lemma

This file proves Gödel's Beta Function Lemma, used to prove the First Incompleteness Theorem. It
permits quantification over finite sequences of natural numbers in formal theories of arithmetic.
This Beta Function has no connection with the unrelated Beta Function defined in analysis. Note
that `Nat.beta` and `Nat.unbeta` provide similar functionality to `Encodable.encodeList` and
`Encodable.decodeList`. We define these separately, because it is easier to prove that `Nat.beta`
and `Nat.unbeta` are arithmetically definable, and this is hard to prove that for
`Encodable.encodeList` and `Encodable.decodeList` directly. The arithmetic
definability is needed for the proof of the First Incompleteness Theorem.

## Main result

- `beta_unbeta_coe`: Gödel's Beta Function Lemma.

## Implementation note

This code is a step towards eventually including a proof of Gödel's First Incompleteness Theorem
and other key results from the repository https://github.com/iehality/lean4-logic.

## References

* [R. Kaye, *Models of Peano arithmetic*][kaye1991]
* <https://en.wikipedia.org/wiki/G%C3%B6del%27s_%CE%B2_function>

## Tags

Gödel, beta function
-/

@[expose] public section

namespace Nat

/--
lemma `coprime_mul_succ` / 引理 `coprime_mul_succ`

English:
lemma coprime_mul_succ
  given: {n m a} (ha : m - n ∣ a)
  statement: Coprime (n * a + 1) (m * a + 1)
  proof: Nat.coprime_of_dvd fun p pp hn hm => by
    have : p ∣ (m - n) * a := by
      simpa [Nat.succ_sub_succ, ← Nat.mul_sub_right_distrib] using
        Nat.dvd_sub hm hn
    have : p ∣ a := by
      rcases (Nat.Prime.dvd_mul pp).mp this with (hp | hp)
      · exact Nat.dvd_trans hp ha
      · exact hp
 

中文:
引理 coprime_mul_succ
  条件: {n m a} (ha : m - n ∣ a)
  结论: Coprime (n * a + 1) (m * a + 1)
  证明: Nat.coprime_of_dvd fun p pp hn hm => by
    have : p ∣ (m - n) * a := by
      simpa [Nat.succ_sub_succ, ← Nat.mul_sub_right_distrib] using
        Nat.dvd_sub hm hn
    have : p ∣ a := by
      rcases (Nat.Prime.dvd_mul pp).mp this with (hp | hp)
      · exact Nat.dvd_trans hp ha
      · exact hp
 

Depends on / 依赖: Nat.Prime.dvd_mul, Nat.add_sub_cancel_left, Nat.coprime_of_dvd, Nat.dvd_sub, Nat.dvd_trans, Nat.mul_sub_right_distrib, Nat.succ_sub_succ, add_sub_cancel_left, coprime_of_dvd, dvd_mul, dvd_sub, dvd_trans, mul_left, mul_sub_right_distrib, ne_one, pp.ne_one, succ_sub_succ, this.mul_left
-/
lemma coprime_mul_succ {n m a} (ha : m - n ∣ a) : Coprime (n * a + 1) (m * a + 1) :=
  Nat.coprime_of_dvd fun p pp hn hm => by
    have : p ∣ (m - n) * a := by
      simpa [Nat.succ_sub_succ, ← Nat.mul_sub_right_distrib] using
        Nat.dvd_sub hm hn
    have : p ∣ a := by
      rcases (Nat.Prime.dvd_mul pp).mp this with (hp | hp)
      · exact Nat.dvd_trans hp ha
      · exact hp
    apply pp.ne_one
    simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hn (this.mul_left n)

variable {m : Nat}

set_option backward.privateInPublic true in
/--
Definition of `supOfSeq` / `supOfSeq` 的定义

English:
definition supOfSeq
  signature: (a : Fin m -> Nat)
  body: max m (Finset.sup .univ a) + 1

中文:
定义 supOfSeq
  签名: (a : Fin m -> 自然数)
  定义体: max m (Finset.sup .univ a) + 1
-/
private def supOfSeq (a : Fin m -> Nat) : Nat := max m (Finset.sup .univ a) + 1

set_option backward.privateInPublic true in
/--
Definition of `coprimes` / `coprimes` 的定义

English:
definition coprimes
  signature: (a : Fin m -> Nat)
  body: fun i => (i + 1) * (supOfSeq a)! + 1

中文:
定义 coprimes
  签名: (a : Fin m -> 自然数)
  定义体: fun i => (i + 1) * (supOfSeq a)! + 1
-/
private def coprimes (a : Fin m -> Nat) : Fin m -> Nat := fun i => (i + 1) * (supOfSeq a)! + 1

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `coprimes_lt` / 引理 `coprimes_lt`

English:
lemma coprimes_lt
  given: (a : Fin m -> Nat) (i)
  statement: a i < coprimes a i
  proof: by
  have h₁ : a i < supOfSeq a :=
    Nat.lt_add_one_iff.mpr (le_max_of_le_right <| Finset.le_sup (by simp))
  have h₂ : supOfSeq a <= (i + 1) * (supOfSeq a)! + 1 :=
    le_trans (self_le_factorial _) (le_trans (Nat.le_mul_of_pos_left (supOfSeq a)! (succ_pos i))
      (le_add_right _ _))
  simpa on

中文:
引理 coprimes_lt
  条件: (a : Fin m -> 自然数) (i)
  结论: a i < coprimes a i
  证明: by
  have h₁ : a i < supOfSeq a :=
    Nat.lt_add_one_iff.mpr (le_max_of_le_right <| Finset.le_sup (by simp))
  have h₂ : supOfSeq a <= (i + 1) * (supOfSeq a)! + 1 :=
    le_trans (self_le_factorial _) (le_trans (Nat.le_mul_of_pos_left (supOfSeq a)! (succ_pos i))
      (le_add_right _ _))
  simpa on

Depends on / 依赖: Finset, Finset.le_sup, Nat.le_mul_of_pos_left, Nat.lt_add_one_iff.mpr, coprimes, le_add_right, le_max_of_le_right, le_mul_of_pos_left, le_sup, le_trans, lt_add_one_iff, lt_of_lt_of_le, self_le_factorial, succ_pos, supOfSeq
-/
lemma coprimes_lt (a : Fin m -> Nat) (i) : a i < coprimes a i := by
  have h₁ : a i < supOfSeq a :=
    Nat.lt_add_one_iff.mpr (le_max_of_le_right <| Finset.le_sup (by simp))
  have h₂ : supOfSeq a <= (i + 1) * (supOfSeq a)! + 1 :=
    le_trans (self_le_factorial _) (le_trans (Nat.le_mul_of_pos_left (supOfSeq a)! (succ_pos i))
      (le_add_right _ _))
  simpa only [coprimes] using lt_of_lt_of_le h₁ h₂

open scoped Function in -- required for scoped `on` notation
/--
lemma `pairwise_coprime_coprimes` / 引理 `pairwise_coprime_coprimes`

English:
lemma pairwise_coprime_coprimes
  given: (a : Fin m -> Nat)
  statement: Pairwise (Coprime on coprimes a)
  proof: by
  intro i j hij
  wlog! ltij : i < j
  · exact (this a hij.symm (lt_of_le_of_ne ltij hij.symm)).symm
  unfold Function.onFun coprimes
  have hja : j < supOfSeq a := lt_of_lt_of_le j.prop (le_succ_of_le (le_max_left _ _))
  exact coprime_mul_succ
    (Nat.dvd_factorial (by lia)
      (by simpa onl

中文:
引理 pairwise_coprime_coprimes
  条件: (a : Fin m -> 自然数)
  结论: Pairwise (Coprime on coprimes a)
  证明: by
  intro i j hij
  wlog! ltij : i < j
  · exact (this a hij.symm (lt_of_le_of_ne ltij hij.symm)).symm
  unfold Function.onFun coprimes
  have hja : j < supOfSeq a := lt_of_lt_of_le j.prop (le_succ_of_le (le_max_left _ _))
  exact coprime_mul_succ
    (Nat.dvd_factorial (by lia)
      (by simpa onl
-/
private lemma pairwise_coprime_coprimes (a : Fin m -> Nat) : Pairwise (Coprime on coprimes a) := by
  intro i j hij
  wlog! ltij : i < j
  · exact (this a hij.symm (lt_of_le_of_ne ltij hij.symm)).symm
  unfold Function.onFun coprimes
  have hja : j < supOfSeq a := lt_of_lt_of_le j.prop (le_succ_of_le (le_max_left _ _))
  exact coprime_mul_succ
    (Nat.dvd_factorial (by lia)
      (by simpa only [Nat.succ_sub_succ] using le_of_lt (lt_of_le_of_lt (sub_le j i) hja)))

/--
Definition of `beta` / `beta` 的定义

English:
definition beta
  signature: (n i : Nat)
  body: n.unpair.1 % ((i + 1) * n.unpair.2 + 1)

中文:
定义 beta
  签名: (n i : 自然数)
  定义体: n.unpair.1 % ((i + 1) * n.unpair.2 + 1)

Depends on / 依赖: n.unpair, unpair
-/
def beta (n i : Nat) : Nat := n.unpair.1 % ((i + 1) * n.unpair.2 + 1)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `unbeta` / `unbeta` 的定义

English:
definition unbeta
  signature: (l : List Nat)
  body: (chineseRemainderOfFinset (ι := Fin l.length) (l[·]) (coprimes (l[·])) Finset.univ
    (by simp [coprimes])
    (by simpa using Set.pairwise_univ.mpr (pairwise_coprime_coprimes _)) : Nat).pair
  (supOfSeq (m := l.length) (l[·]))!

中文:
定义 unbeta
  签名: (l : List 自然数)
  定义体: (chineseRemainderOfFinset (ι := Fin l.length) (l[·]) (coprimes (l[·])) Finset.univ
    (by simp [coprimes])
    (by simpa using Set.pairwise_univ.mpr (pairwise_coprime_coprimes _)) : Nat).pair
  (supOfSeq (m := l.length) (l[·]))!

Depends on / 依赖: Finset, Finset.univ, Set.pairwise_univ.mpr, chineseRemainderOfFinset, coprimes, l.length, length, pairwise_coprime_coprimes, pairwise_univ, supOfSeq
-/
def unbeta (l : List Nat) : Nat :=
  (chineseRemainderOfFinset (ι := Fin l.length) (l[·]) (coprimes (l[·])) Finset.univ
    (by simp [coprimes])
    (by simpa using Set.pairwise_univ.mpr (pairwise_coprime_coprimes _)) : Nat).pair
  (supOfSeq (m := l.length) (l[·]))!

/--
lemma `beta_unbeta_coe` / 引理 `beta_unbeta_coe`

English:
lemma beta_unbeta_coe
  given: (l : List Nat) (i : Fin l.length)
  statement: beta (unbeta l) i = l[i]
  proof: by
  simpa [beta, unbeta, coprimes] using mod_eq_of_modEq
    ((chineseRemainderOfFinset (l[·]) (coprimes (l[·])) Finset.univ
      (by simp [coprimes])
      (by simpa using Set.pairwise_univ.mpr (pairwise_coprime_coprimes _))).prop i (by simp))
    (coprimes_lt _ _)

中文:
引理 beta_unbeta_coe
  条件: (l : List 自然数) (i : Fin l.length)
  结论: beta (unbeta l) i = l[i]
  证明: by
  simpa [beta, unbeta, coprimes] using mod_eq_of_modEq
    ((chineseRemainderOfFinset (l[·]) (coprimes (l[·])) Finset.univ
      (by simp [coprimes])
      (by simpa using Set.pairwise_univ.mpr (pairwise_coprime_coprimes _))).prop i (by simp))
    (coprimes_lt _ _)

Depends on / 依赖: Finset, Finset.univ, Set.pairwise_univ.mpr, chineseRemainderOfFinset, coprimes, coprimes_lt, mod_eq_of_modEq, pairwise_coprime_coprimes, pairwise_univ, unbeta
-/
lemma beta_unbeta_coe (l : List Nat) (i : Fin l.length) : beta (unbeta l) i = l[i] := by
  simpa [beta, unbeta, coprimes] using mod_eq_of_modEq
    ((chineseRemainderOfFinset (l[·]) (coprimes (l[·])) Finset.univ
      (by simp [coprimes])
      (by simpa using Set.pairwise_univ.mpr (pairwise_coprime_coprimes _))).prop i (by simp))
    (coprimes_lt _ _)

end Nat
