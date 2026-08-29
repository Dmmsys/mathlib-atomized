/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.PNat.Interval
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# The inequality `p⁻¹ + q⁻¹ + r⁻¹ > 1`

In this file we classify solutions to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`, for positive natural numbers `p`, `q`, and `r`.

The solutions are exactly of the form.
* `A' q r := {1,q,r}`
* `D' r := {2,2,r}`
* `E6 := {2,3,3}`, or `E7 := {2,3,4}`, or `E8 := {2,3,5}`

This inequality shows up in Lie theory,
in the classification of Dynkin diagrams, root systems, and semisimple Lie algebras.

## Main declarations

* `ADEInequality.A' q r`, the multiset `{1,q,r}`
* `ADEInequality.D' r`, the multiset `{2,2,r}`
* `ADEInequality.E6`, the multiset `{2,3,3}`
* `ADEInequality.E7`, the multiset `{2,3,4}`
* `ADEInequality.E8`, the multiset `{2,3,5}`
* `ADEInequality.classification`, the classification of solutions to `p⁻¹ + q⁻¹ + r⁻¹ > 1`

-/

@[expose] public section


namespace ADEInequality

open Multiset


/--
Definition of `A'` / `A'` 的定义

English:
definition A'
  signature: (q r : Nat+)
  body: {1, q, r}

中文:
定义 A'
  签名: (q r : 自然数+)
  定义体: {1, q, r}
-/
def A' (q r : Nat+) : Multiset Nat+ :=
  {1, q, r}

/--
Definition of `A` / `A` 的定义

English:
definition A
  signature: (r : Nat+)
  body: A' 1 r

中文:
定义 A
  签名: (r : 自然数+)
  定义体: A' 1 r
-/
def A (r : Nat+) : Multiset Nat+ :=
  A' 1 r

/--
Definition of `D'` / `D'` 的定义

English:
definition D'
  signature: (r : Nat+)
  body: {2, 2, r}

中文:
定义 D'
  签名: (r : 自然数+)
  定义体: {2, 2, r}
-/
def D' (r : Nat+) : Multiset Nat+ :=
  {2, 2, r}

/--
Definition of `E'` / `E'` 的定义

English:
definition E'
  signature: (r : Nat+)
  body: {2, 3, r}

中文:
定义 E'
  签名: (r : 自然数+)
  定义体: {2, 3, r}
-/
def E' (r : Nat+) : Multiset Nat+ :=
  {2, 3, r}

/--
Definition of `E6` / `E6` 的定义

English:
definition E6
  signature: : Multiset Nat+
  body: E' 3

中文:
定义 E6
  签名: : Multiset 自然数+
  定义体: E' 3
-/
def E6 : Multiset Nat+ :=
  E' 3

/--
Definition of `E7` / `E7` 的定义

English:
definition E7
  signature: : Multiset Nat+
  body: E' 4

中文:
定义 E7
  签名: : Multiset 自然数+
  定义体: E' 4
-/
def E7 : Multiset Nat+ :=
  E' 4

/--
Definition of `E8` / `E8` 的定义

English:
definition E8
  signature: : Multiset Nat+
  body: E' 5

中文:
定义 E8
  签名: : Multiset 自然数+
  定义体: E' 5
-/
def E8 : Multiset Nat+ :=
  E' 5

/--
Definition of `sumInv` / `sumInv` 的定义

English:
definition sumInv
  signature: (pqr : Multiset Nat+)
  body: Multiset.sum (pqr.map fun (x : Nat+) => x⁻¹)

中文:
定义 sumInv
  签名: (pqr : Multiset 自然数+)
  定义体: Multiset.sum (pqr.map fun (x : Nat+) => x⁻¹)

Depends on / 依赖: Multiset, Multiset.sum, pqr.map
-/
def sumInv (pqr : Multiset Nat+) : Rat :=
  Multiset.sum (pqr.map fun (x : Nat+) => x⁻¹)

/--
theorem `sumInv_pqr` / 定理 `sumInv_pqr`

English:
theorem sumInv_pqr
  given: (p q r : Nat+)
  statement: sumInv {p, q, r} = (p : Rat)⁻¹ + (q : Rat)⁻¹ + (r : Rat)⁻¹
  proof: by
  simp only [sumInv, insert_eq_cons, add_assoc, map_cons, sum_cons,
    map_singleton, sum_singleton]

中文:
定理 sumInv_pqr
  条件: (p q r : 自然数+)
  结论: sumInv {p, q, r} = (p : 有理数)⁻¹ + (q : 有理数)⁻¹ + (r : 有理数)⁻¹
  证明: by
  simp only [sumInv, insert_eq_cons, add_assoc, map_cons, sum_cons,
    map_singleton, sum_singleton]

Depends on / 依赖: add_assoc, insert_eq_cons, map_cons, map_singleton, sumInv, sum_cons, sum_singleton
-/
theorem sumInv_pqr (p q r : Nat+) : sumInv {p, q, r} = (p : Rat)⁻¹ + (q : Rat)⁻¹ + (r : Rat)⁻¹ := by
  simp only [sumInv, insert_eq_cons, add_assoc, map_cons, sum_cons,
    map_singleton, sum_singleton]

/--
Definition of `Admissible` / `Admissible` 的定义

English:
definition Admissible
  signature: (pqr : Multiset Nat+)
  body: (exists q r, A' q r = pqr) ∨ (exists r, D' r = pqr) ∨ E' 3 = pqr ∨ E' 4 = pqr ∨ E' 5 = pqr

中文:
定义 Admissible
  签名: (pqr : Multiset 自然数+)
  定义体: (exists q r, A' q r = pqr) ∨ (exists r, D' r = pqr) ∨ E' 3 = pqr ∨ E' 4 = pqr ∨ E' 5 = pqr
-/
def Admissible (pqr : Multiset Nat+) : Prop :=
  (exists q r, A' q r = pqr) ∨ (exists r, D' r = pqr) ∨ E' 3 = pqr ∨ E' 4 = pqr ∨ E' 5 = pqr

/--
theorem `admissible_A'` / 定理 `admissible_A'`

English:
theorem admissible_A'
  given: (q r : Nat+)
  statement: Admissible (A' q r)
  proof: Or.inl ⟨q, r, rfl⟩

中文:
定理 admissible_A'
  条件: (q r : 自然数+)
  结论: Admissible (A' q r)
  证明: Or.inl ⟨q, r, rfl⟩

Depends on / 依赖: Or.inl
-/
theorem admissible_A' (q r : Nat+) : Admissible (A' q r) :=
  Or.inl ⟨q, r, rfl⟩

/--
theorem `admissible_D'` / 定理 `admissible_D'`

English:
theorem admissible_D'
  given: (n : Nat+)
  statement: Admissible (D' n)
  proof: Or.inr Or.inl ⟨n, rfl⟩

中文:
定理 admissible_D'
  条件: (n : 自然数+)
  结论: Admissible (D' n)
  证明: Or.inr Or.inl ⟨n, rfl⟩

Depends on / 依赖: Or.inl, Or.inr
-/
theorem admissible_D' (n : Nat+) : Admissible (D' n) :=
Or.inr Or.inl ⟨n, rfl⟩

/--
theorem `admissible_E'3` / 定理 `admissible_E'3`

English:
theorem admissible_E'3
  statement: Admissible (E' 3)
  proof: Or.inr Or.inr Or.inl rfl

中文:
定理 admissible_E'3
  结论: Admissible (E' 3)
  证明: Or.inr Or.inr Or.inl rfl

Depends on / 依赖: Or.inl, Or.inr
-/
theorem admissible_E'3 : Admissible (E' 3) :=
Or.inr Or.inr Or.inl rfl

/--
theorem `admissible_E'4` / 定理 `admissible_E'4`

English:
theorem admissible_E'4
  statement: Admissible (E' 4)
  proof: Or.inr Or.inr Or.inr Or.inl rfl

中文:
定理 admissible_E'4
  结论: Admissible (E' 4)
  证明: Or.inr Or.inr Or.inr Or.inl rfl
-/
theorem admissible_E'4 : Admissible (E' 4) :=
Or.inr Or.inr Or.inr Or.inl rfl

/--
theorem `admissible_E'5` / 定理 `admissible_E'5`

English:
theorem admissible_E'5
  statement: Admissible (E' 5)
  proof: Or.inr Or.inr Or.inr Or.inr rfl

中文:
定理 admissible_E'5
  结论: Admissible (E' 5)
  证明: Or.inr Or.inr Or.inr Or.inr rfl
-/
theorem admissible_E'5 : Admissible (E' 5) :=
Or.inr Or.inr Or.inr Or.inr rfl

/--
theorem `admissible_E6` / 定理 `admissible_E6`

English:
theorem admissible_E6
  statement: Admissible E6
  proof: admissible_E'3

中文:
定理 admissible_E6
  结论: Admissible E6
  证明: admissible_E'3

Depends on / 依赖: admissible_E
-/
theorem admissible_E6 : Admissible E6 :=
  admissible_E'3

/--
theorem `admissible_E7` / 定理 `admissible_E7`

English:
theorem admissible_E7
  statement: Admissible E7
  proof: admissible_E'4

中文:
定理 admissible_E7
  结论: Admissible E7
  证明: admissible_E'4

Depends on / 依赖: admissible_E
-/
theorem admissible_E7 : Admissible E7 :=
  admissible_E'4

/--
theorem `admissible_E8` / 定理 `admissible_E8`

English:
theorem admissible_E8
  statement: Admissible E8
  proof: admissible_E'5

中文:
定理 admissible_E8
  结论: Admissible E8
  证明: admissible_E'5

Depends on / 依赖: admissible_E
-/
theorem admissible_E8 : Admissible E8 :=
  admissible_E'5

/--
theorem `Admissible.one_lt_sumInv` / 定理 `Admissible.one_lt_sumInv`

English:
theorem Admissible.one_lt_sumInv
  given: {pqr : Multiset Nat+}
  statement: Admissible pqr -> 1 < sumInv pqr
  proof: by
  rw [Admissible]
  rintro (⟨p', q', H⟩ | ⟨n, H⟩ | H | H | H)
  · rw [← H, A', sumInv_pqr, add_assoc]
    simp only [lt_add_iff_pos_right, PNat.one_coe, inv_one, Nat.cast_one]
    apply add_pos <;> simp only [PNat.pos, Nat.cast_pos, inv_pos]
  · rw [← H, D', sumInv_pqr]
    norm_num
  all_goals
    rw [← H]; rw [E']; rw [sumInv_pqr]
    norm_num

中文:
定理 Admissible.one_lt_sumInv
  条件: {pqr : Multiset 自然数+}
  结论: Admissible pqr -> 1 < sumInv pqr
  证明: by
  rw [Admissible]
  rintro (⟨p', q', H⟩ | ⟨n, H⟩ | H | H | H)
  · rw [← H, A', sumInv_pqr, add_assoc]
    simp only [lt_add_iff_pos_right, PNat.one_coe, inv_one, Nat.cast_one]
    apply add_pos <;> simp only [PNat.pos, Nat.cast_pos, inv_pos]
  · rw [← H, D', sumInv_pqr]
    norm_num
  all_goals
    rw [← H]; rw [E']; rw [sumInv_pqr]
    norm_num

Depends on / 依赖: Admissible, Nat.cast_one, Nat.cast_pos, PNat.one_coe, PNat.pos, add_assoc, add_pos, all_goals, cast_one, cast_pos, inv_one, inv_pos, lt_add_iff_pos_right, one_coe, sumInv_pqr
-/
theorem Admissible.one_lt_sumInv {pqr : Multiset Nat+} : Admissible pqr -> 1 < sumInv pqr := by
  rw [Admissible]
  rintro (⟨p', q', H⟩ | ⟨n, H⟩ | H | H | H)
  · rw [← H, A', sumInv_pqr, add_assoc]
    simp only [lt_add_iff_pos_right, PNat.one_coe, inv_one, Nat.cast_one]
    apply add_pos <;> simp only [PNat.pos, Nat.cast_pos, inv_pos]
  · rw [← H, D', sumInv_pqr]
    norm_num
  all_goals
    rw [← H]; rw [E']; rw [sumInv_pqr]
    norm_num

/--
theorem `lt_three` / 定理 `lt_three`

English:
theorem lt_three
  given: {p q r : Nat+} (hpq : p <= q) (hqr : q <= r) (H : 1 < sumInv {p, q, r})
  statement: p < 3
  proof: by
  contrapose! H
  rw [sumInv_pqr]
  have h3q := H.trans hpq
  have h3r := h3q.trans hqr
  have hp : (p : Rat)⁻¹ <= 3⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast H)
  have hq : (q : Rat)⁻¹ <= 3⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast h3q)
  have hr : (r : Rat)⁻¹ <= 3⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast h3r)
  calc
    (p : Rat)⁻¹ + (q : Rat)⁻¹ + (r : Rat)⁻¹ <= 3⁻¹ + 3⁻¹ + 3⁻¹ := add_le_add (add_le_add hp hq) hr
    _ = 1 := by norm_num

中文:
定理 lt_three
  条件: {p q r : 自然数+} (hpq : p <= q) (hqr : q <= r) (H : 1 < sumInv {p, q, r})
  结论: p < 3
  证明: by
  contrapose! H
  rw [sumInv_pqr]
  have h3q := H.trans hpq
  have h3r := h3q.trans hqr
  have hp : (p : Rat)⁻¹ <= 3⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast H)
  have hq : (q : Rat)⁻¹ <= 3⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast h3q)
  have hr : (r : Rat)⁻¹ <= 3⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast h3r)
  calc
    (p : Rat)⁻¹ + (q : Rat)⁻¹ + (r : Rat)⁻¹ <= 3⁻¹ + 3⁻¹ + 3⁻¹ := add_le_add (add_le_add hp hq) hr
    _ = 1 := by norm_num

Depends on / 依赖: H.trans, add_le_add, contrapose, h3q.trans, sumInv_pqr
-/
theorem lt_three {p q r : Nat+} (hpq : p <= q) (hqr : q <= r) (H : 1 < sumInv {p, q, r}) : p < 3 := by
  contrapose! H
  rw [sumInv_pqr]
  have h3q := H.trans hpq
  have h3r := h3q.trans hqr
  have hp : (p : Rat)⁻¹ <= 3⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast H)
  have hq : (q : Rat)⁻¹ <= 3⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast h3q)
  have hr : (r : Rat)⁻¹ <= 3⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast h3r)
  calc
    (p : Rat)⁻¹ + (q : Rat)⁻¹ + (r : Rat)⁻¹ <= 3⁻¹ + 3⁻¹ + 3⁻¹ := add_le_add (add_le_add hp hq) hr
    _ = 1 := by norm_num

/--
theorem `lt_four` / 定理 `lt_four`

English:
theorem lt_four
  given: {q r : Nat+} (hqr : q <= r) (H : 1 < sumInv {2, q, r})
  statement: q < 4
  proof: by
  contrapose! H
  rw [sumInv_pqr]
  have h4r := H.trans hqr
  have hq : (q : Rat)⁻¹ <= 4⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast H)
  have hr : (r : Rat)⁻¹ <= 4⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast h4r)
  calc
    (2⁻¹ + (q : Rat)⁻¹ + (r : Rat)⁻¹) <= 2⁻¹ + 4⁻¹ + 4⁻¹ := add_le_add (add_le_add le_rfl hq) hr
    _ = 1 := by norm_num

中文:
定理 lt_four
  条件: {q r : 自然数+} (hqr : q <= r) (H : 1 < sumInv {2, q, r})
  结论: q < 4
  证明: by
  contrapose! H
  rw [sumInv_pqr]
  have h4r := H.trans hqr
  have hq : (q : Rat)⁻¹ <= 4⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast H)
  have hr : (r : Rat)⁻¹ <= 4⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast h4r)
  calc
    (2⁻¹ + (q : Rat)⁻¹ + (r : Rat)⁻¹) <= 2⁻¹ + 4⁻¹ + 4⁻¹ := add_le_add (add_le_add le_rfl hq) hr
    _ = 1 := by norm_num

Depends on / 依赖: H.trans, add_le_add, contrapose, le_rfl, sumInv_pqr
-/
theorem lt_four {q r : Nat+} (hqr : q <= r) (H : 1 < sumInv {2, q, r}) : q < 4 := by
  contrapose! H
  rw [sumInv_pqr]
  have h4r := H.trans hqr
  have hq : (q : Rat)⁻¹ <= 4⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast H)
  have hr : (r : Rat)⁻¹ <= 4⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast h4r)
  calc
    (2⁻¹ + (q : Rat)⁻¹ + (r : Rat)⁻¹) <= 2⁻¹ + 4⁻¹ + 4⁻¹ := add_le_add (add_le_add le_rfl hq) hr
    _ = 1 := by norm_num

/--
theorem `lt_six` / 定理 `lt_six`

English:
theorem lt_six
  given: {r : Nat+} (H : 1 < sumInv {2, 3, r})
  statement: r < 6
  proof: by
  contrapose! H
  rw [sumInv_pqr]
  have hr : (r : Rat)⁻¹ <= 6⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast H)
  calc
    (2⁻¹ + 3⁻¹ + (r : Rat)⁻¹ : Rat) <= 2⁻¹ + 3⁻¹ + 6⁻¹ := add_le_add (add_le_add le_rfl le_rfl) hr
    _ = 1 := by norm_num

中文:
定理 lt_six
  条件: {r : 自然数+} (H : 1 < sumInv {2, 3, r})
  结论: r < 6
  证明: by
  contrapose! H
  rw [sumInv_pqr]
  have hr : (r : Rat)⁻¹ <= 6⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast H)
  calc
    (2⁻¹ + 3⁻¹ + (r : Rat)⁻¹ : Rat) <= 2⁻¹ + 3⁻¹ + 6⁻¹ := add_le_add (add_le_add le_rfl le_rfl) hr
    _ = 1 := by norm_num

Depends on / 依赖: add_le_add, contrapose, le_rfl, sumInv_pqr
-/
theorem lt_six {r : Nat+} (H : 1 < sumInv {2, 3, r}) : r < 6 := by
  contrapose! H
  rw [sumInv_pqr]
  have hr : (r : Rat)⁻¹ <= 6⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast H)
  calc
    (2⁻¹ + 3⁻¹ + (r : Rat)⁻¹ : Rat) <= 2⁻¹ + 3⁻¹ + 6⁻¹ := add_le_add (add_le_add le_rfl le_rfl) hr
    _ = 1 := by norm_num

/--
theorem `admissible_of_one_lt_sumInv_aux'` / 定理 `admissible_of_one_lt_sumInv_aux'`

English:
theorem admissible_of_one_lt_sumInv_aux'
  statement: {p q r : Nat+} (hpq : p <= q) (hqr : q <= r)
  proof: by
  have hp3 : p < 3 := lt_three hpq hqr H
  -- Porting note: `interval_cases` doesn't support `ℕ+` yet.
  replace hp3 := Finset.mem_Iio.mpr hp3
  conv at hp3 => change p in ({1, 2} : Multiset Nat+)
  fin_cases hp3
  · exact admissible_A' q r
  have hq4 : q < 4 := lt_four hqr H
  replace hq4 := Finset.mem_Ico.mpr ⟨hpq, hq4⟩; clear hpq
  conv at hq4 => change q in ({2, 3} : Multiset Nat+)
  fin_cases hq4
  · exact admissible_D' r
  have hr6 : r < 6 := lt_six H
  replace hr6 := Finset.mem_Ico.mpr ⟨hqr, hr6⟩; clear hqr
  conv at hr6 => change r in ({3, 4, 5} : Multiset Nat+)
  fin_cases hr6
  · exact admissible_E6
  · exact admissible_E7
  · exact admissible_E8

中文:
定理 admissible_of_one_lt_sumInv_aux'
  结论: {p q r : 自然数+} (hpq : p <= q) (hqr : q <= r)
  证明: by
  have hp3 : p < 3 := lt_three hpq hqr H
  -- Porting note: `interval_cases` doesn't support `ℕ+` yet.
  replace hp3 := Finset.mem_Iio.mpr hp3
  conv at hp3 => change p in ({1, 2} : Multiset Nat+)
  fin_cases hp3
  · exact admissible_A' q r
  have hq4 : q < 4 := lt_four hqr H
  replace hq4 := Finset.mem_Ico.mpr ⟨hpq, hq4⟩; clear hpq
  conv at hq4 => change q in ({2, 3} : Multiset Nat+)
  fin_cases hq4
  · exact admissible_D' r
  have hr6 : r < 6 := lt_six H
  replace hr6 := Finset.mem_Ico.mpr ⟨hqr, hr6⟩; clear hqr
  conv at hr6 => change r in ({3, 4, 5} : Multiset Nat+)
  fin_cases hr6
  · exact admissible_E6
  · exact admissible_E7
  · exact admissible_E8

Depends on / 依赖: lt_three
-/
theorem admissible_of_one_lt_sumInv_aux' {p q r : Nat+} (hpq : p <= q) (hqr : q <= r)
    (H : 1 < sumInv {p, q, r}) : Admissible {p, q, r} := by
  have hp3 : p < 3 := lt_three hpq hqr H
  -- Porting note: `interval_cases` doesn't support `ℕ+` yet.
  replace hp3 := Finset.mem_Iio.mpr hp3
  conv at hp3 => change p in ({1, 2} : Multiset Nat+)
  fin_cases hp3
  · exact admissible_A' q r
  have hq4 : q < 4 := lt_four hqr H
  replace hq4 := Finset.mem_Ico.mpr ⟨hpq, hq4⟩; clear hpq
  conv at hq4 => change q in ({2, 3} : Multiset Nat+)
  fin_cases hq4
  · exact admissible_D' r
  have hr6 : r < 6 := lt_six H
  replace hr6 := Finset.mem_Ico.mpr ⟨hqr, hr6⟩; clear hqr
  conv at hr6 => change r in ({3, 4, 5} : Multiset Nat+)
  fin_cases hr6
  · exact admissible_E6
  · exact admissible_E7
  · exact admissible_E8

/--
theorem `admissible_of_one_lt_sumInv_aux` / 定理 `admissible_of_one_lt_sumInv_aux`

English:
theorem admissible_of_one_lt_sumInv_aux
  proof: by simpa using hs.pairwise
    exact admissible_of_one_lt_sumInv_aux' hpq hqr H

中文:
定理 admissible_of_one_lt_sumInv_aux
  证明: by simpa using hs.pairwise
    exact admissible_of_one_lt_sumInv_aux' hpq hqr H

Depends on / 依赖: admissible_of_one_lt_sumInv_aux, hs.pairwise, pairwise
-/
theorem admissible_of_one_lt_sumInv_aux :
    forall {pqr : List Nat+} (_ : pqr.SortedLE) (_ : pqr.length = 3) (_ : 1 < sumInv pqr),
      Admissible pqr
  | [p, q, r], hs, _, H => by
    obtain ⟨⟨hpq, -⟩, hqr⟩ : (p <= q ∧ p <= r) ∧ q <= r := by simpa using hs.pairwise
    exact admissible_of_one_lt_sumInv_aux' hpq hqr H

/--
theorem `admissible_of_one_lt_sumInv` / 定理 `admissible_of_one_lt_sumInv`

English:
theorem admissible_of_one_lt_sumInv
  given: {p q r : Nat+} (H : 1 < sumInv {p, q, r})
  proof: by
  simp only [Admissible]
  let S := sort (α := Nat+) {p, q, r}
  have hS : S.SortedLE := (pairwise_sort _ _).sortedLE
  have hpqr : ({p, q, r} : Multiset Nat+) = S := (sort_eq {p, q, r} LE.le).symm
  rw [hpqr]
  rw [hpqr] at H
  apply admissible_of_one_lt_sumInv_aux hS _ H
  simp only [S, insert_eq_cons, length_sort, card_cons, card_singleton]

中文:
定理 admissible_of_one_lt_sumInv
  条件: {p q r : 自然数+} (H : 1 < sumInv {p, q, r})
  证明: by
  simp only [Admissible]
  let S := sort (α := Nat+) {p, q, r}
  have hS : S.SortedLE := (pairwise_sort _ _).sortedLE
  have hpqr : ({p, q, r} : Multiset Nat+) = S := (sort_eq {p, q, r} LE.le).symm
  rw [hpqr]
  rw [hpqr] at H
  apply admissible_of_one_lt_sumInv_aux hS _ H
  simp only [S, insert_eq_cons, length_sort, card_cons, card_singleton]

Depends on / 依赖: Admissible, LE.le, Multiset, S.SortedLE, SortedLE, admissible_of_one_lt_sumInv_aux, card_cons, card_singleton, insert_eq_cons, length_sort, pairwise_sort, sort_eq, sortedLE
-/
theorem admissible_of_one_lt_sumInv {p q r : Nat+} (H : 1 < sumInv {p, q, r}) :
    Admissible {p, q, r} := by
  simp only [Admissible]
  let S := sort (α := Nat+) {p, q, r}
  have hS : S.SortedLE := (pairwise_sort _ _).sortedLE
  have hpqr : ({p, q, r} : Multiset Nat+) = S := (sort_eq {p, q, r} LE.le).symm
  rw [hpqr]
  rw [hpqr] at H
  apply admissible_of_one_lt_sumInv_aux hS _ H
  simp only [S, insert_eq_cons, length_sort, card_cons, card_singleton]

/--
theorem `classification` / 定理 `classification`

English:
theorem classification
  given: (p q r : Nat+)
  statement: 1 < sumInv {p, q, r} ↔ Admissible {p, q, r}
  proof: ⟨admissible_of_one_lt_sumInv, Admissible.one_lt_sumInv⟩

中文:
定理 classification
  条件: (p q r : 自然数+)
  结论: 1 < sumInv {p, q, r} ↔ Admissible {p, q, r}
  证明: ⟨admissible_of_one_lt_sumInv, Admissible.one_lt_sumInv⟩

Depends on / 依赖: Admissible, Admissible.one_lt_sumInv, admissible_of_one_lt_sumInv, one_lt_sumInv
-/
theorem classification (p q r : Nat+) : 1 < sumInv {p, q, r} ↔ Admissible {p, q, r} :=
  ⟨admissible_of_one_lt_sumInv, Admissible.one_lt_sumInv⟩

end ADEInequality
