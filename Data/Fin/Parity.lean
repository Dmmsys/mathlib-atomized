/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Iván Renison
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.ZMod.Defs

/-!
# Parity in `Fin n`

In this file we prove that an element `k : Fin n` is even in `Fin n`
iff `n` is odd or `Fin.val k` is even.

We also prove a lemma about parity of `Fin.succAbove i j + Fin.predAbove j i`
which can be used to prove `d ∘ d = 0` for de Rham cohomologies.
-/

public section

open Fin

namespace Fin

open Fin.CommRing

variable {n : Nat} {k : Fin n}

/--
theorem `even_succAbove_add_predAbove` / 定理 `even_succAbove_add_predAbove`

English:
theorem even_succAbove_add_predAbove
  given: (i : Fin (n + 1)) (j : Fin n)
  proof: by
  rcases lt_or_ge j.castSucc i with hji | hij
  · have : 1 <= (i : Nat) := (Nat.zero_le j).trans_lt hji
    simp [succAbove_of_castSucc_lt _ _ hji, predAbove_of_castSucc_lt _ _ hji, this, iff_comm,
      parity_simps]
  · simp [succAbove_of_le_castSucc _ _ hij, predAbove_of_le_castSucc _ _ hij,
 

中文:
定理 even_succAbove_add_predAbove
  条件: (i : 有限集 (n + 1)) (j : 有限集 n)
  证明: by
  rcases lt_or_ge j.castSucc i with hji | hij
  · have : 1 <= (i : Nat) := (Nat.zero_le j).trans_lt hji
    simp [succAbove_of_castSucc_lt _ _ hji, predAbove_of_castSucc_lt _ _ hji, this, iff_comm,
      parity_simps]
  · simp [succAbove_of_le_castSucc _ _ hij, predAbove_of_le_castSucc _ _ hij,
 

Depends on / 依赖: Nat.not_even_iff_odd, Nat.zero_le, castSucc, iff_comm, j.castSucc, lt_or_ge, not_even_iff_odd, not_iff, not_iff_comm, parity_simps, predAbove_of_castSucc_lt, predAbove_of_le_castSucc, succAbove_of_castSucc_lt, succAbove_of_le_castSucc, trans_lt, zero_le
-/
theorem even_succAbove_add_predAbove (i : Fin (n + 1)) (j : Fin n) :
    Even (i.succAbove j + j.predAbove i : Nat) ↔ Odd (i + j : Nat) := by
  rcases lt_or_ge j.castSucc i with hji | hij
  · have : 1 <= (i : Nat) := (Nat.zero_le j).trans_lt hji
    simp [succAbove_of_castSucc_lt _ _ hji, predAbove_of_castSucc_lt _ _ hji, this, iff_comm,
      parity_simps]
  · simp [succAbove_of_le_castSucc _ _ hij, predAbove_of_le_castSucc _ _ hij,
      ← Nat.not_even_iff_odd, not_iff, not_iff_comm, parity_simps]

/--
lemma `neg_one_pow_succAbove_add_predAbove` / 引理 `neg_one_pow_succAbove_add_predAbove`

English:
lemma neg_one_pow_succAbove_add_predAbove
  statement: {R : Type*} [Monoid R] [HasDistribNeg R]
  proof: by
  rw [← neg_one_mul (_ ^ _)]; rw [← pow_succ']; rw [neg_one_pow_congr]
  rw [even_succAbove_add_predAbove]; rw [Nat.even_add_one]; rw [Nat.not_even_iff_odd]

中文:
引理 neg_one_pow_succAbove_add_predAbove
  结论: {R : 类型} [幺半群 R] [有DistribNeg R]
  证明: by
  rw [← neg_one_mul (_ ^ _)]; rw [← pow_succ']; rw [neg_one_pow_congr]
  rw [even_succAbove_add_predAbove]; rw [Nat.even_add_one]; rw [Nat.not_even_iff_odd]

Depends on / 依赖: Nat.even_add_one, Nat.not_even_iff_odd, even_add_one, even_succAbove_add_predAbove, neg_one_mul, neg_one_pow_congr, not_even_iff_odd, pow_succ
-/
lemma neg_one_pow_succAbove_add_predAbove {R : Type*} [Monoid R] [HasDistribNeg R]
    (i : Fin (n + 1)) (j : Fin n) :
    (-1 : R) ^ (i.succAbove j + j.predAbove i : Nat) = -(-1) ^ (i + j : Nat) := by
  rw [← neg_one_mul (_ ^ _)]; rw [← pow_succ']; rw [neg_one_pow_congr]
  rw [even_succAbove_add_predAbove]; rw [Nat.even_add_one]; rw [Nat.not_even_iff_odd]

/--
lemma `even_of_val` / 引理 `even_of_val`

English:
lemma even_of_val
  given: (h : Even k.val)
  statement: Even k
  proof: by
  have : NeZero n := ⟨k.pos.ne'⟩
  rw [← Fin.cast_val_eq_self k]
  exact h.natCast

中文:
引理 even_of_val
  条件: (h : Even k.val)
  结论: Even k
  证明: by
  have : NeZero n := ⟨k.pos.ne'⟩
  rw [← Fin.cast_val_eq_self k]
  exact h.natCast

Depends on / 依赖: Fin.cast_val_eq_self, NeZero, cast_val_eq_self, h.natCast, k.pos.ne, natCast
-/
lemma even_of_val (h : Even k.val) : Even k := by
  have : NeZero n := ⟨k.pos.ne'⟩
  rw [← Fin.cast_val_eq_self k]
  exact h.natCast

/--
lemma `odd_of_val` / 引理 `odd_of_val`

English:
lemma odd_of_val
  given: [NeZero n] (h : Odd k.val)
  statement: Odd k
  proof: by
  rw [← Fin.cast_val_eq_self k]
  exact h.natCast

中文:
引理 odd_of_val
  条件: [NeZero n] (h : Odd k.val)
  结论: Odd k
  证明: by
  rw [← Fin.cast_val_eq_self k]
  exact h.natCast

Depends on / 依赖: Fin.cast_val_eq_self, cast_val_eq_self, h.natCast, natCast
-/
lemma odd_of_val [NeZero n] (h : Odd k.val) : Odd k := by
  rw [← Fin.cast_val_eq_self k]
  exact h.natCast

/--
lemma `even_of_odd` / 引理 `even_of_odd`

English:
lemma even_of_odd
  given: (hn : Odd n) (k : Fin n)
  statement: Even k
  proof: by
  have : NeZero n := ⟨k.pos.ne'⟩
  rcases k.val.even_or_odd with hk | hk
  · exact even_of_val hk
  · simpa using (hk.add_odd hn).natCast (α := Fin n)

中文:
引理 even_of_odd
  条件: (hn : Odd n) (k : 有限集 n)
  结论: Even k
  证明: by
  have : NeZero n := ⟨k.pos.ne'⟩
  rcases k.val.even_or_odd with hk | hk
  · exact even_of_val hk
  · simpa using (hk.add_odd hn).natCast (α := Fin n)

Depends on / 依赖: NeZero, add_odd, even_of_val, even_or_odd, hk.add_odd, k.pos.ne, k.val.even_or_odd, natCast
-/
lemma even_of_odd (hn : Odd n) (k : Fin n) : Even k := by
  have : NeZero n := ⟨k.pos.ne'⟩
  rcases k.val.even_or_odd with hk | hk
  · exact even_of_val hk
  · simpa using (hk.add_odd hn).natCast (α := Fin n)

/--
lemma `odd_of_odd` / 引理 `odd_of_odd`

English:
lemma odd_of_odd
  given: [NeZero n] (hn : Odd n) (k : Fin n)
  statement: Odd k
  proof: by
  rcases k.val.even_or_odd with hk | hk
  · simpa using (Even.add_odd hk hn).natCast (R := Fin n)
  · exact odd_of_val hk

中文:
引理 odd_of_odd
  条件: [NeZero n] (hn : Odd n) (k : 有限集 n)
  结论: Odd k
  证明: by
  rcases k.val.even_or_odd with hk | hk
  · simpa using (Even.add_odd hk hn).natCast (R := Fin n)
  · exact odd_of_val hk

Depends on / 依赖: Even.add_odd, add_odd, even_or_odd, k.val.even_or_odd, natCast, odd_of_val
-/
lemma odd_of_odd [NeZero n] (hn : Odd n) (k : Fin n) : Odd k := by
  rcases k.val.even_or_odd with hk | hk
  · simpa using (Even.add_odd hk hn).natCast (R := Fin n)
  · exact odd_of_val hk

/--
lemma `even_iff_of_even` / 引理 `even_iff_of_even`

English:
lemma even_iff_of_even
  given: (hn : Even n)
  statement: Even k ↔ Even k.val
  proof: by
  rcases hn with ⟨n, rfl⟩
  refine ⟨?_, even_of_val⟩
  rintro ⟨l, rfl⟩
  rw [val_add_eq_ite]
  split_ifs with h <;> simp [Nat.even_sub, *]

中文:
引理 even_iff_of_even
  条件: (hn : Even n)
  结论: Even k ↔ Even k.val
  证明: by
  rcases hn with ⟨n, rfl⟩
  refine ⟨?_, even_of_val⟩
  rintro ⟨l, rfl⟩
  rw [val_add_eq_ite]
  split_ifs with h <;> simp [Nat.even_sub, *]

Depends on / 依赖: Nat.even_sub, even_of_val, even_sub, split_ifs, val_add_eq_ite
-/
lemma even_iff_of_even (hn : Even n) : Even k ↔ Even k.val := by
  rcases hn with ⟨n, rfl⟩
  refine ⟨?_, even_of_val⟩
  rintro ⟨l, rfl⟩
  rw [val_add_eq_ite]
  split_ifs with h <;> simp [Nat.even_sub, *]

/--
lemma `odd_iff_of_even` / 引理 `odd_iff_of_even`

English:
lemma odd_iff_of_even
  given: [NeZero n] (hn : Even n)
  statement: Odd k ↔ Odd k.val
  proof: by
  rcases hn with ⟨n, rfl⟩
  refine ⟨?_, odd_of_val⟩
  rintro ⟨l, rfl⟩
  rw [val_add]; rw [val_mul]; rw [coe_ofNat_eq_mod]; rw [coe_ofNat_eq_mod]
  simp only [Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod, Nat.odd_iff]
  rw [Nat.mod_mod_of_dvd _ ⟨n]; rw [(two_mul n).symm⟩]; rw [← Nat.odd_iff];

中文:
引理 odd_iff_of_even
  条件: [NeZero n] (hn : Even n)
  结论: Odd k ↔ Odd k.val
  证明: by
  rcases hn with ⟨n, rfl⟩
  refine ⟨?_, odd_of_val⟩
  rintro ⟨l, rfl⟩
  rw [val_add]; rw [val_mul]; rw [coe_ofNat_eq_mod]; rw [coe_ofNat_eq_mod]
  simp only [Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod, Nat.odd_iff]
  rw [Nat.mod_mod_of_dvd _ ⟨n]; rw [(two_mul n).symm⟩]; rw [← Nat.odd_iff];

Depends on / 依赖: Nat.add_mod_mod, Nat.mod_add_mod, Nat.mod_mod_of_dvd, Nat.mod_mul_mod, Nat.not_odd_iff_even, Nat.odd_add_one, Nat.odd_iff, add_mod_mod, coe_ofNat_eq_mod, mod_add_mod, mod_mod_of_dvd, mod_mul_mod, not_odd_iff_even, odd_add_one, odd_iff, odd_of_val, two_mul, val_add, val_mul
-/
lemma odd_iff_of_even [NeZero n] (hn : Even n) : Odd k ↔ Odd k.val := by
  rcases hn with ⟨n, rfl⟩
  refine ⟨?_, odd_of_val⟩
  rintro ⟨l, rfl⟩
  rw [val_add]; rw [val_mul]; rw [coe_ofNat_eq_mod]; rw [coe_ofNat_eq_mod]
  simp only [Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod, Nat.odd_iff]
  rw [Nat.mod_mod_of_dvd _ ⟨n]; rw [(two_mul n).symm⟩]; rw [← Nat.odd_iff]; rw [Nat.odd_add_one]; rw [Nat.not_odd_iff_even]
  simp

/--
lemma `even_iff` / 引理 `even_iff`

English:
lemma even_iff
  statement: Even k ↔ (Odd n ∨ Even k.val)
  proof: by
  refine ⟨fun hk => ?_, or_imp.mpr ⟨(even_of_odd · k), even_of_val⟩⟩
  rw [← Nat.not_even_iff_odd]; rw [← imp_iff_not_or]
  exact fun hn => (even_iff_of_even hn).mp hk

中文:
引理 even_iff
  结论: Even k ↔ (Odd n ∨ Even k.val)
  证明: by
  refine ⟨fun hk => ?_, or_imp.mpr ⟨(even_of_odd · k), even_of_val⟩⟩
  rw [← Nat.not_even_iff_odd]; rw [← imp_iff_not_or]
  exact fun hn => (even_iff_of_even hn).mp hk

Depends on / 依赖: Nat.not_even_iff_odd, even_iff_of_even, even_of_odd, even_of_val, imp_iff_not_or, not_even_iff_odd, or_imp, or_imp.mpr
-/
lemma even_iff : Even k ↔ (Odd n ∨ Even k.val) := by
  refine ⟨fun hk => ?_, or_imp.mpr ⟨(even_of_odd · k), even_of_val⟩⟩
  rw [← Nat.not_even_iff_odd]; rw [← imp_iff_not_or]
  exact fun hn => (even_iff_of_even hn).mp hk

/--
lemma `even_iff_imp` / 引理 `even_iff_imp`

English:
lemma even_iff_imp
  statement: Even k ↔ (Even n -> Even k.val)
  proof: by
  rw [imp_iff_not_or]; rw [Nat.not_even_iff_odd]
  exact even_iff

中文:
引理 even_iff_imp
  结论: Even k ↔ (Even n -> Even k.val)
  证明: by
  rw [imp_iff_not_or]; rw [Nat.not_even_iff_odd]
  exact even_iff

Depends on / 依赖: Nat.not_even_iff_odd, even_iff, imp_iff_not_or, not_even_iff_odd
-/
lemma even_iff_imp : Even k ↔ (Even n -> Even k.val) := by
  rw [imp_iff_not_or]; rw [Nat.not_even_iff_odd]
  exact even_iff

/--
lemma `odd_iff` / 引理 `odd_iff`

English:
lemma odd_iff
  given: [NeZero n]
  statement: Odd k ↔ Odd n ∨ Odd k.val
  proof: by
  refine ⟨fun hk => ?_, or_imp.mpr ⟨(odd_of_odd · k), odd_of_val⟩⟩
  rw [← Nat.not_even_iff_odd]; rw [← imp_iff_not_or]
  exact fun hn => (odd_iff_of_even hn).mp hk

中文:
引理 odd_iff
  条件: [NeZero n]
  结论: Odd k ↔ Odd n ∨ Odd k.val
  证明: by
  refine ⟨fun hk => ?_, or_imp.mpr ⟨(odd_of_odd · k), odd_of_val⟩⟩
  rw [← Nat.not_even_iff_odd]; rw [← imp_iff_not_or]
  exact fun hn => (odd_iff_of_even hn).mp hk

Depends on / 依赖: Nat.not_even_iff_odd, imp_iff_not_or, not_even_iff_odd, odd_iff_of_even, odd_of_odd, odd_of_val, or_imp, or_imp.mpr
-/
lemma odd_iff [NeZero n] : Odd k ↔ Odd n ∨ Odd k.val := by
  refine ⟨fun hk => ?_, or_imp.mpr ⟨(odd_of_odd · k), odd_of_val⟩⟩
  rw [← Nat.not_even_iff_odd]; rw [← imp_iff_not_or]
  exact fun hn => (odd_iff_of_even hn).mp hk

/--
lemma `odd_iff_imp` / 引理 `odd_iff_imp`

English:
lemma odd_iff_imp
  given: [NeZero n]
  statement: Odd k ↔ (Even n -> Odd k.val)
  proof: by
  rw [imp_iff_not_or]; rw [Nat.not_even_iff_odd]
  exact odd_iff

中文:
引理 odd_iff_imp
  条件: [NeZero n]
  结论: Odd k ↔ (Even n -> Odd k.val)
  证明: by
  rw [imp_iff_not_or]; rw [Nat.not_even_iff_odd]
  exact odd_iff

Depends on / 依赖: Nat.not_even_iff_odd, imp_iff_not_or, not_even_iff_odd, odd_iff
-/
lemma odd_iff_imp [NeZero n] : Odd k ↔ (Even n -> Odd k.val) := by
  rw [imp_iff_not_or]; rw [Nat.not_even_iff_odd]
  exact odd_iff

/--
lemma `even_iff_mod_of_even` / 引理 `even_iff_mod_of_even`

English:
lemma even_iff_mod_of_even
  given: (hn : Even n)
  statement: Even k ↔ k.val % 2 = 0
  proof: by
  rw [even_iff_of_even hn]
  exact Nat.even_iff

中文:
引理 even_iff_mod_of_even
  条件: (hn : Even n)
  结论: Even k ↔ k.val % 2 = 0
  证明: by
  rw [even_iff_of_even hn]
  exact Nat.even_iff

Depends on / 依赖: Nat.even_iff, even_iff, even_iff_of_even
-/
lemma even_iff_mod_of_even (hn : Even n) : Even k ↔ k.val % 2 = 0 := by
  rw [even_iff_of_even hn]
  exact Nat.even_iff

/--
lemma `odd_iff_mod_of_even` / 引理 `odd_iff_mod_of_even`

English:
lemma odd_iff_mod_of_even
  given: [NeZero n] (hn : Even n)
  statement: Odd k ↔ k.val % 2 = 1
  proof: by
  rw [odd_iff_of_even hn]
  exact Nat.odd_iff

中文:
引理 odd_iff_mod_of_even
  条件: [NeZero n] (hn : Even n)
  结论: Odd k ↔ k.val % 2 = 1
  证明: by
  rw [odd_iff_of_even hn]
  exact Nat.odd_iff

Depends on / 依赖: Nat.odd_iff, odd_iff, odd_iff_of_even
-/
lemma odd_iff_mod_of_even [NeZero n] (hn : Even n) : Odd k ↔ k.val % 2 = 1 := by
  rw [odd_iff_of_even hn]
  exact Nat.odd_iff

/--
lemma `not_odd_iff_even_of_even` / 引理 `not_odd_iff_even_of_even`

English:
lemma not_odd_iff_even_of_even
  given: [NeZero n] (hn : Even n)
  statement: ¬Odd k ↔ Even k
  proof: by
  rw [even_iff_of_even hn]; rw [odd_iff_of_even hn]
  exact Nat.not_odd_iff_even

中文:
引理 not_odd_iff_even_of_even
  条件: [NeZero n] (hn : Even n)
  结论: ¬Odd k ↔ Even k
  证明: by
  rw [even_iff_of_even hn]; rw [odd_iff_of_even hn]
  exact Nat.not_odd_iff_even

Depends on / 依赖: Nat.not_odd_iff_even, even_iff_of_even, not_odd_iff_even, odd_iff_of_even
-/
lemma not_odd_iff_even_of_even [NeZero n] (hn : Even n) : ¬Odd k ↔ Even k := by
  rw [even_iff_of_even hn]; rw [odd_iff_of_even hn]
  exact Nat.not_odd_iff_even

/--
lemma `not_even_iff_odd_of_even` / 引理 `not_even_iff_odd_of_even`

English:
lemma not_even_iff_odd_of_even
  given: [NeZero n] (hn : Even n)
  statement: ¬Even k ↔ Odd k
  proof: by
  rw [even_iff_of_even hn]; rw [odd_iff_of_even hn]
  exact Nat.not_even_iff_odd

中文:
引理 not_even_iff_odd_of_even
  条件: [NeZero n] (hn : Even n)
  结论: ¬Even k ↔ Odd k
  证明: by
  rw [even_iff_of_even hn]; rw [odd_iff_of_even hn]
  exact Nat.not_even_iff_odd

Depends on / 依赖: Nat.not_even_iff_odd, even_iff_of_even, not_even_iff_odd, odd_iff_of_even
-/
lemma not_even_iff_odd_of_even [NeZero n] (hn : Even n) : ¬Even k ↔ Odd k := by
  rw [even_iff_of_even hn]; rw [odd_iff_of_even hn]
  exact Nat.not_even_iff_odd

/--
lemma `odd_add_one_iff_even` / 引理 `odd_add_one_iff_even`

English:
lemma odd_add_one_iff_even
  given: [NeZero n]
  statement: Odd (k + 1) ↔ Even k
  proof: ⟨fun ⟨k, hk⟩ => add_right_cancel hk ▸ even_two_mul k, Even.add_one⟩

中文:
引理 odd_add_one_iff_even
  条件: [NeZero n]
  结论: Odd (k + 1) ↔ Even k
  证明: ⟨fun ⟨k, hk⟩ => add_right_cancel hk ▸ even_two_mul k, Even.add_one⟩

Depends on / 依赖: Even.add_one, add_one, add_right_cancel, even_two_mul
-/
lemma odd_add_one_iff_even [NeZero n] : Odd (k + 1) ↔ Even k :=
  ⟨fun ⟨k, hk⟩ => add_right_cancel hk ▸ even_two_mul k, Even.add_one⟩

/--
lemma `even_add_one_iff_odd` / 引理 `even_add_one_iff_odd`

English:
lemma even_add_one_iff_odd
  given: [NeZero n]
  statement: Even (k + 1) ↔ Odd k
  proof: ⟨fun ⟨k, hk⟩ => eq_sub_iff_add_eq.mpr hk ▸ (Even.add_self k).sub_odd odd_one, Odd.add_one⟩

中文:
引理 even_add_one_iff_odd
  条件: [NeZero n]
  结论: Even (k + 1) ↔ Odd k
  证明: ⟨fun ⟨k, hk⟩ => eq_sub_iff_add_eq.mpr hk ▸ (Even.add_self k).sub_odd odd_one, Odd.add_one⟩

Depends on / 依赖: Even.add_self, Odd.add_one, add_one, add_self, eq_sub_iff_add_eq, eq_sub_iff_add_eq.mpr, odd_one, sub_odd
-/
lemma even_add_one_iff_odd [NeZero n] : Even (k + 1) ↔ Odd k :=
  ⟨fun ⟨k, hk⟩ => eq_sub_iff_add_eq.mpr hk ▸ (Even.add_self k).sub_odd odd_one, Odd.add_one⟩

end Fin
