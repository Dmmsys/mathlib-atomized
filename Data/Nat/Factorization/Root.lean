/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.Factorization.Defs

/-!
# Roots of natural numbers, rounded up and down

This file defines the flooring and ceiling root of a natural number.
`Nat.floorRoot n a`/`Nat.ceilRoot n a`, the `n`-th flooring/ceiling root of `a`, is the natural
number whose `p`-adic valuation is the floor/ceil of the `p`-adic valuation of `a`.

For example the `2`-nd flooring and ceiling roots of `2^3 * 3^2 * 5` are `2 * 3` and `2^2 * 3 * 5`
respectively. Note this is **not** the `n`-th root of `a` as a real number, rounded up or down.

These operations are respectively the right and left adjoints to the map `a ↦ a ^ n` where `ℕ` is
ordered by divisibility. This is useful because it lets us characterise the numbers `a` whose `n`-th
power divide `n` as the divisors of some fixed number (aka `floorRoot n b`). See
`Nat.pow_dvd_iff_dvd_floorRoot`. Similarly, it lets us characterise the `b` whose `n`-th power is a
multiple of `a` as the multiples of some fixed number (aka `ceilRoot n a`). See
`Nat.dvd_pow_iff_ceilRoot_dvd`.

## TODO

* `norm_num` extension
-/

@[expose] public section

open Finsupp

namespace Nat
variable {a b n : Nat}

/--
Definition of `floorRoot` / `floorRoot` 的定义

English:
definition floorRoot
  signature: (n a : Nat)
  body: if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k => p ^ (k / n)

中文:
定义 floorRoot
  签名: (n a : 自然数)
  定义体: if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k => p ^ (k / n)

Depends on / 依赖: a.factorization.prod, factorization
-/
def floorRoot (n a : Nat) : Nat :=
  if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k => p ^ (k / n)

/--
lemma `floorRoot_def` / 引理 `floorRoot_def`

English:
lemma floorRoot_def
  proof: by
  unfold floorRoot; split_ifs with h <;> simp [Finsupp.floorDiv_def, prod_mapRange_index pow_zero]

中文:
引理 floorRoot_def
  证明: by
  unfold floorRoot; split_ifs with h <;> simp [Finsupp.floorDiv_def, prod_mapRange_index pow_zero]

Depends on / 依赖: Finsupp, Finsupp.floorDiv_def, floorDiv_def, floorRoot, pow_zero, prod_mapRange_index, split_ifs
-/
lemma floorRoot_def :
    floorRoot n a = if n = 0 ∨ a = 0 then 0 else (a.factorization ⌊/⌋ n).prod (· ^ ·) := by
  unfold floorRoot; split_ifs with h <;> simp [Finsupp.floorDiv_def, prod_mapRange_index pow_zero]

/--
lemma `floorRoot_zero_left` / 引理 `floorRoot_zero_left`

English:
lemma floorRoot_zero_left
  given: (a : Nat)
  statement: floorRoot 0 a = 0
  proof: by simp [floorRoot]

中文:
引理 floorRoot_zero_left
  条件: (a : 自然数)
  结论: floorRoot 0 a = 0
  证明: by simp [floorRoot]
-/
@[simp] lemma floorRoot_zero_left (a : Nat) : floorRoot 0 a = 0 := by simp [floorRoot]
/--
lemma `floorRoot_zero_right` / 引理 `floorRoot_zero_right`

English:
lemma floorRoot_zero_right
  given: (n : Nat)
  statement: floorRoot n 0 = 0
  proof: by simp [floorRoot]

中文:
引理 floorRoot_zero_right
  条件: (n : 自然数)
  结论: floorRoot n 0 = 0
  证明: by simp [floorRoot]
-/
@[simp] lemma floorRoot_zero_right (n : Nat) : floorRoot n 0 = 0 := by simp [floorRoot]
/--
lemma `floorRoot_one_left` / 引理 `floorRoot_one_left`

English:
lemma floorRoot_one_left
  given: (a : Nat)
  statement: floorRoot 1 a = a
  proof: by
  simp [floorRoot]; split_ifs <;> simp [*]

中文:
引理 floorRoot_one_left
  条件: (a : 自然数)
  结论: floorRoot 1 a = a
  证明: by
  simp [floorRoot]; split_ifs <;> simp [*]
-/
@[simp] lemma floorRoot_one_left (a : Nat) : floorRoot 1 a = a := by
  simp [floorRoot]; split_ifs <;> simp [*]
/--
lemma `floorRoot_one_right` / 引理 `floorRoot_one_right`

English:
lemma floorRoot_one_right
  given: (hn : n != 0)
  statement: floorRoot n 1 = 1
  proof: by simp [floorRoot, hn]

中文:
引理 floorRoot_one_right
  条件: (hn : n != 0)
  结论: floorRoot n 1 = 1
  证明: by simp [floorRoot, hn]
-/
@[simp] lemma floorRoot_one_right (hn : n != 0) : floorRoot n 1 = 1 := by simp [floorRoot, hn]

/--
lemma `floorRoot_pow_self` / 引理 `floorRoot_pow_self`

English:
lemma floorRoot_pow_self
  given: (hn : n != 0) (a : Nat)
  statement: floorRoot n (a ^ n) = a
  proof: by
  simp [floorRoot_def, pos_iff_ne_zero.2, hn]; split_ifs <;> simp [*]

中文:
引理 floorRoot_pow_self
  条件: (hn : n != 0) (a : 自然数)
  结论: floorRoot n (a ^ n) = a
  证明: by
  simp [floorRoot_def, pos_iff_ne_zero.2, hn]; split_ifs <;> simp [*]
-/
@[simp] lemma floorRoot_pow_self (hn : n != 0) (a : Nat) : floorRoot n (a ^ n) = a := by
  simp [floorRoot_def, pos_iff_ne_zero.2, hn]; split_ifs <;> simp [*]

/--
lemma `floorRoot_ne_zero` / 引理 `floorRoot_ne_zero`

English:
lemma floorRoot_ne_zero
  statement: floorRoot n a != 0 ↔ n != 0 ∧ a != 0
  proof: by
  simp +contextual [floorRoot, not_or]

中文:
引理 floorRoot_ne_zero
  结论: floorRoot n a != 0 ↔ n != 0 ∧ a != 0
  证明: by
  simp +contextual [floorRoot, not_or]

Depends on / 依赖: contextual, floorRoot, not_or
-/
lemma floorRoot_ne_zero : floorRoot n a != 0 ↔ n != 0 ∧ a != 0 := by
  simp +contextual [floorRoot, not_or]

/--
lemma `floorRoot_eq_zero` / 引理 `floorRoot_eq_zero`

English:
lemma floorRoot_eq_zero
  statement: floorRoot n a = 0 ↔ n = 0 ∨ a = 0
  proof: floorRoot_ne_zero.not_right.trans by simp only [not_and_or, ne_eq, not_not]

中文:
引理 floorRoot_eq_zero
  结论: floorRoot n a = 0 ↔ n = 0 ∨ a = 0
  证明: floorRoot_ne_zero.not_right.trans by simp only [not_and_or, ne_eq, not_not]
-/
@[simp] lemma floorRoot_eq_zero : floorRoot n a = 0 ↔ n = 0 ∨ a = 0 :=
floorRoot_ne_zero.not_right.trans by simp only [not_and_or, ne_eq, not_not]

/--
lemma `factorization_floorRoot` / 引理 `factorization_floorRoot`

English:
lemma factorization_floorRoot
  given: (n a : Nat)
  proof: by
  rw [floorRoot_def]
  split_ifs with h
  · obtain rfl | rfl := h <;> simp
  apply a.factorization_prod_pow_eq_self_of_le_factorization
.trans smul_floorDiv_le (by lia) exact le_self_nsmul (by simp) (by lia)

中文:
引理 factorization_floorRoot
  条件: (n a : 自然数)
  证明: by
  rw [floorRoot_def]
  split_ifs with h
  · obtain rfl | rfl := h <;> simp
  apply a.factorization_prod_pow_eq_self_of_le_factorization
.trans smul_floorDiv_le (by lia) exact le_self_nsmul (by simp) (by lia)
-/
@[simp] lemma factorization_floorRoot (n a : Nat) :
    (floorRoot n a).factorization = a.factorization ⌊/⌋ n := by
  rw [floorRoot_def]
  split_ifs with h
  · obtain rfl | rfl := h <;> simp
  apply a.factorization_prod_pow_eq_self_of_le_factorization
.trans smul_floorDiv_le (by lia) exact le_self_nsmul (by simp) (by lia)

/--
lemma `pow_dvd_iff_dvd_floorRoot` / 引理 `pow_dvd_iff_dvd_floorRoot`

English:
lemma pow_dvd_iff_dvd_floorRoot
  statement: a ^ n ∣ b ↔ a ∣ floorRoot n b
  proof: by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  obtain rfl | ha := eq_or_ne a 0
  · simp [hn]
  rw [← factorization_le_iff_dvd (pow_ne_zero _ ha) hb]; rw [← factorization_le_iff_dvd ha (floorRoot_ne_zero.2 ⟨hn]; rw [hb⟩)]; rw [factorization_pow]; rw [factorization_floorRoot]; rw [le_floorDiv_iff_smul_le (β := Nat ->₀ Nat) (pos_iff_ne_zero.2 hn)]

中文:
引理 pow_dvd_iff_dvd_floorRoot
  结论: a ^ n ∣ b ↔ a ∣ floorRoot n b
  证明: by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  obtain rfl | ha := eq_or_ne a 0
  · simp [hn]
  rw [← factorization_le_iff_dvd (pow_ne_zero _ ha) hb]; rw [← factorization_le_iff_dvd ha (floorRoot_ne_zero.2 ⟨hn]; rw [hb⟩)]; rw [factorization_pow]; rw [factorization_floorRoot]; rw [le_floorDiv_iff_smul_le (β := Nat ->₀ Nat) (pos_iff_ne_zero.2 hn)]

Depends on / 依赖: eq_or_ne, factorization_floorRoot, factorization_le_iff_dvd, factorization_pow, floorRoot_ne_zero, le_floorDiv_iff_smul_le, pos_iff_ne_zero, pow_ne_zero
-/
lemma pow_dvd_iff_dvd_floorRoot : a ^ n ∣ b ↔ a ∣ floorRoot n b := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  obtain rfl | ha := eq_or_ne a 0
  · simp [hn]
  rw [← factorization_le_iff_dvd (pow_ne_zero _ ha) hb]; rw [← factorization_le_iff_dvd ha (floorRoot_ne_zero.2 ⟨hn]; rw [hb⟩)]; rw [factorization_pow]; rw [factorization_floorRoot]; rw [le_floorDiv_iff_smul_le (β := Nat ->₀ Nat) (pos_iff_ne_zero.2 hn)]

/--
lemma `floorRoot_pow_dvd` / 引理 `floorRoot_pow_dvd`

English:
lemma floorRoot_pow_dvd
  statement: floorRoot n a ^ n ∣ a
  proof: pow_dvd_iff_dvd_floorRoot.2 dvd_rfl

中文:
引理 floorRoot_pow_dvd
  结论: floorRoot n a ^ n ∣ a
  证明: pow_dvd_iff_dvd_floorRoot.2 dvd_rfl

Depends on / 依赖: dvd_rfl, pow_dvd_iff_dvd_floorRoot
-/
lemma floorRoot_pow_dvd : floorRoot n a ^ n ∣ a := pow_dvd_iff_dvd_floorRoot.2 dvd_rfl

/--
Definition of `ceilRoot` / `ceilRoot` 的定义

English:
definition ceilRoot
  signature: (n a : Nat)
  body: if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k => p ^ ((k + n - 1) / n)

中文:
定义 ceilRoot
  签名: (n a : 自然数)
  定义体: if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k => p ^ ((k + n - 1) / n)

Depends on / 依赖: a.factorization.prod, factorization
-/
def ceilRoot (n a : Nat) : Nat :=
  if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k => p ^ ((k + n - 1) / n)

/--
lemma `ceilRoot_def` / 引理 `ceilRoot_def`

English:
lemma ceilRoot_def
  proof: by
  unfold ceilRoot
  split_ifs with h <;>
    simp [Finsupp.ceilDiv_def, prod_mapRange_index pow_zero, Nat.ceilDiv_eq_add_pred_div]

中文:
引理 ceilRoot_def
  证明: by
  unfold ceilRoot
  split_ifs with h <;>
    simp [Finsupp.ceilDiv_def, prod_mapRange_index pow_zero, Nat.ceilDiv_eq_add_pred_div]

Depends on / 依赖: Finsupp, Finsupp.ceilDiv_def, Nat.ceilDiv_eq_add_pred_div, ceilDiv_def, ceilDiv_eq_add_pred_div, ceilRoot, pow_zero, prod_mapRange_index, split_ifs
-/
lemma ceilRoot_def :
    ceilRoot n a = if n = 0 ∨ a = 0 then 0 else (a.factorization ⌈/⌉ n).prod (· ^ ·) := by
  unfold ceilRoot
  split_ifs with h <;>
    simp [Finsupp.ceilDiv_def, prod_mapRange_index pow_zero, Nat.ceilDiv_eq_add_pred_div]

/--
lemma `ceilRoot_zero_left` / 引理 `ceilRoot_zero_left`

English:
lemma ceilRoot_zero_left
  given: (a : Nat)
  statement: ceilRoot 0 a = 0
  proof: by simp [ceilRoot]

中文:
引理 ceilRoot_zero_left
  条件: (a : 自然数)
  结论: ceilRoot 0 a = 0
  证明: by simp [ceilRoot]
-/
@[simp] lemma ceilRoot_zero_left (a : Nat) : ceilRoot 0 a = 0 := by simp [ceilRoot]
/--
lemma `ceilRoot_zero_right` / 引理 `ceilRoot_zero_right`

English:
lemma ceilRoot_zero_right
  given: (n : Nat)
  statement: ceilRoot n 0 = 0
  proof: by simp [ceilRoot]

中文:
引理 ceilRoot_zero_right
  条件: (n : 自然数)
  结论: ceilRoot n 0 = 0
  证明: by simp [ceilRoot]
-/
@[simp] lemma ceilRoot_zero_right (n : Nat) : ceilRoot n 0 = 0 := by simp [ceilRoot]
/--
lemma `ceilRoot_one_left` / 引理 `ceilRoot_one_left`

English:
lemma ceilRoot_one_left
  given: (a : Nat)
  statement: ceilRoot 1 a = a
  proof: by
  simp [ceilRoot]; split_ifs <;> simp [*]

中文:
引理 ceilRoot_one_left
  条件: (a : 自然数)
  结论: ceilRoot 1 a = a
  证明: by
  simp [ceilRoot]; split_ifs <;> simp [*]
-/
@[simp] lemma ceilRoot_one_left (a : Nat) : ceilRoot 1 a = a := by
  simp [ceilRoot]; split_ifs <;> simp [*]
/--
lemma `ceilRoot_one_right` / 引理 `ceilRoot_one_right`

English:
lemma ceilRoot_one_right
  given: (hn : n != 0)
  statement: ceilRoot n 1 = 1
  proof: by simp [ceilRoot, hn]

中文:
引理 ceilRoot_one_right
  条件: (hn : n != 0)
  结论: ceilRoot n 1 = 1
  证明: by simp [ceilRoot, hn]
-/
@[simp] lemma ceilRoot_one_right (hn : n != 0) : ceilRoot n 1 = 1 := by simp [ceilRoot, hn]

/--
lemma `ceilRoot_pow_self` / 引理 `ceilRoot_pow_self`

English:
lemma ceilRoot_pow_self
  given: (hn : n != 0) (a : Nat)
  statement: ceilRoot n (a ^ n) = a
  proof: by
  simp [ceilRoot_def, pos_iff_ne_zero.2, hn]; split_ifs <;> simp [*]

中文:
引理 ceilRoot_pow_self
  条件: (hn : n != 0) (a : 自然数)
  结论: ceilRoot n (a ^ n) = a
  证明: by
  simp [ceilRoot_def, pos_iff_ne_zero.2, hn]; split_ifs <;> simp [*]
-/
@[simp] lemma ceilRoot_pow_self (hn : n != 0) (a : Nat) : ceilRoot n (a ^ n) = a := by
  simp [ceilRoot_def, pos_iff_ne_zero.2, hn]; split_ifs <;> simp [*]

/--
lemma `ceilRoot_ne_zero` / 引理 `ceilRoot_ne_zero`

English:
lemma ceilRoot_ne_zero
  statement: ceilRoot n a != 0 ↔ n != 0 ∧ a != 0
  proof: by
  simp +contextual [ceilRoot_def, not_or]

中文:
引理 ceilRoot_ne_zero
  结论: ceilRoot n a != 0 ↔ n != 0 ∧ a != 0
  证明: by
  simp +contextual [ceilRoot_def, not_or]

Depends on / 依赖: ceilRoot_def, contextual, not_or
-/
lemma ceilRoot_ne_zero : ceilRoot n a != 0 ↔ n != 0 ∧ a != 0 := by
  simp +contextual [ceilRoot_def, not_or]

/--
lemma `ceilRoot_eq_zero` / 引理 `ceilRoot_eq_zero`

English:
lemma ceilRoot_eq_zero
  statement: ceilRoot n a = 0 ↔ n = 0 ∨ a = 0
  proof: ceilRoot_ne_zero.not_right.trans by simp only [not_and_or, ne_eq, not_not]

中文:
引理 ceilRoot_eq_zero
  结论: ceilRoot n a = 0 ↔ n = 0 ∨ a = 0
  证明: ceilRoot_ne_zero.not_right.trans by simp only [not_and_or, ne_eq, not_not]
-/
@[simp] lemma ceilRoot_eq_zero : ceilRoot n a = 0 ↔ n = 0 ∨ a = 0 :=
ceilRoot_ne_zero.not_right.trans by simp only [not_and_or, ne_eq, not_not]

/--
lemma `factorization_ceilRoot` / 引理 `factorization_ceilRoot`

English:
lemma factorization_ceilRoot
  given: (n a : Nat)
  proof: by
  rw [ceilRoot_def]
  split_ifs with h
  · obtain rfl | rfl := h <;> simp
  refine prod_pow_factorization_eq_self fun p hp => ?_
  have : p.Prime ∧ p ∣ a ∧ ¬a = 0 := by simpa using support_ceilDiv_subset hp
  exact this.1

中文:
引理 factorization_ceilRoot
  条件: (n a : 自然数)
  证明: by
  rw [ceilRoot_def]
  split_ifs with h
  · obtain rfl | rfl := h <;> simp
  refine prod_pow_factorization_eq_self fun p hp => ?_
  have : p.Prime ∧ p ∣ a ∧ ¬a = 0 := by simpa using support_ceilDiv_subset hp
  exact this.1
-/
@[simp] lemma factorization_ceilRoot (n a : Nat) :
    (ceilRoot n a).factorization = a.factorization ⌈/⌉ n := by
  rw [ceilRoot_def]
  split_ifs with h
  · obtain rfl | rfl := h <;> simp
  refine prod_pow_factorization_eq_self fun p hp => ?_
  have : p.Prime ∧ p ∣ a ∧ ¬a = 0 := by simpa using support_ceilDiv_subset hp
  exact this.1

/--
lemma `dvd_pow_iff_ceilRoot_dvd` / 引理 `dvd_pow_iff_ceilRoot_dvd`

English:
lemma dvd_pow_iff_ceilRoot_dvd
  given: (hn : n != 0)
  statement: a ∣ b ^ n ↔ ceilRoot n a ∣ b
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · aesop
  obtain rfl | hb := eq_or_ne b 0
  · simp [hn]
  rw [← factorization_le_iff_dvd ha (pow_ne_zero _ hb)]; rw [← factorization_le_iff_dvd (ceilRoot_ne_zero.2 ⟨hn]; rw [ha⟩) hb]; rw [factorization_pow]; rw [factorization_ceilRoot]; rw [ceilDiv_le_iff_le_smul (β := Nat ->₀ Nat) (pos_iff_ne_zero.2 hn)]

中文:
引理 dvd_pow_iff_ceilRoot_dvd
  条件: (hn : n != 0)
  结论: a ∣ b ^ n ↔ ceilRoot n a ∣ b
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · aesop
  obtain rfl | hb := eq_or_ne b 0
  · simp [hn]
  rw [← factorization_le_iff_dvd ha (pow_ne_zero _ hb)]; rw [← factorization_le_iff_dvd (ceilRoot_ne_zero.2 ⟨hn]; rw [ha⟩) hb]; rw [factorization_pow]; rw [factorization_ceilRoot]; rw [ceilDiv_le_iff_le_smul (β := Nat ->₀ Nat) (pos_iff_ne_zero.2 hn)]

Depends on / 依赖: ceilDiv_le_iff_le_smul, ceilRoot_ne_zero, eq_or_ne, factorization_ceilRoot, factorization_le_iff_dvd, factorization_pow, pos_iff_ne_zero, pow_ne_zero
-/
lemma dvd_pow_iff_ceilRoot_dvd (hn : n != 0) : a ∣ b ^ n ↔ ceilRoot n a ∣ b := by
  obtain rfl | ha := eq_or_ne a 0
  · aesop
  obtain rfl | hb := eq_or_ne b 0
  · simp [hn]
  rw [← factorization_le_iff_dvd ha (pow_ne_zero _ hb)]; rw [← factorization_le_iff_dvd (ceilRoot_ne_zero.2 ⟨hn]; rw [ha⟩) hb]; rw [factorization_pow]; rw [factorization_ceilRoot]; rw [ceilDiv_le_iff_le_smul (β := Nat ->₀ Nat) (pos_iff_ne_zero.2 hn)]

/--
lemma `dvd_ceilRoot_pow` / 引理 `dvd_ceilRoot_pow`

English:
lemma dvd_ceilRoot_pow
  given: (hn : n != 0)
  statement: a ∣ ceilRoot n a ^ n
  proof: (dvd_pow_iff_ceilRoot_dvd hn).2 dvd_rfl

中文:
引理 dvd_ceilRoot_pow
  条件: (hn : n != 0)
  结论: a ∣ ceilRoot n a ^ n
  证明: (dvd_pow_iff_ceilRoot_dvd hn).2 dvd_rfl

Depends on / 依赖: dvd_pow_iff_ceilRoot_dvd, dvd_rfl
-/
lemma dvd_ceilRoot_pow (hn : n != 0) : a ∣ ceilRoot n a ^ n :=
  (dvd_pow_iff_ceilRoot_dvd hn).2 dvd_rfl

end Nat
