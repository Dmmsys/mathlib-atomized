/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Monoid

/-!
# Numbers are frequently ModEq to fixed numbers

In this file we prove that `m ≡ d [MOD n]` frequently as `m → ∞`.
-/

public section


open Filter

namespace Nat

/--
theorem `frequently_modEq` / 定理 `frequently_modEq`

English:
theorem frequently_modEq
  given: {n : Nat} (h : n != 0) (d : Nat)
  statement: existsᶠ m in atTop, m ≡ d [MOD n]
  proof: ((tendsto_add_atTop_nat d).comp (tendsto_id.nsmul_atTop h.bot_lt)).frequently
    Frequently.of_forall fun m => by simp [Nat.modEq_iff_dvd]

中文:
定理 frequently_modEq
  条件: {n : 自然数} (h : n != 0) (d : 自然数)
  结论: 存在ᶠ m in atTop, m ≡ d [MOD n]
  证明: ((tendsto_add_atTop_nat d).comp (tendsto_id.nsmul_atTop h.bot_lt)).frequently
    Frequently.of_forall fun m => by simp [Nat.modEq_iff_dvd]

Depends on / 依赖: Frequently, Frequently.of_forall, Nat.modEq_iff_dvd, bot_lt, frequently, h.bot_lt, modEq_iff_dvd, nsmul_atTop, of_forall, tendsto_add_atTop_nat, tendsto_id, tendsto_id.nsmul_atTop
-/
theorem frequently_modEq {n : Nat} (h : n != 0) (d : Nat) : existsᶠ m in atTop, m ≡ d [MOD n] :=
((tendsto_add_atTop_nat d).comp (tendsto_id.nsmul_atTop h.bot_lt)).frequently
    Frequently.of_forall fun m => by simp [Nat.modEq_iff_dvd]

/--
theorem `frequently_mod_eq` / 定理 `frequently_mod_eq`

English:
theorem frequently_mod_eq
  given: {d n : Nat} (h : d < n)
  statement: existsᶠ m in atTop, m % n = d
  proof: by
  simpa only [Nat.ModEq, mod_eq_of_lt h] using frequently_modEq h.ne_bot d

中文:
定理 frequently_mod_eq
  条件: {d n : 自然数} (h : d < n)
  结论: 存在ᶠ m in atTop, m % n = d
  证明: by
  simpa only [Nat.ModEq, mod_eq_of_lt h] using frequently_modEq h.ne_bot d

Depends on / 依赖: Nat.ModEq, frequently_modEq, h.ne_bot, mod_eq_of_lt, ne_bot
-/
theorem frequently_mod_eq {d n : Nat} (h : d < n) : existsᶠ m in atTop, m % n = d := by
  simpa only [Nat.ModEq, mod_eq_of_lt h] using frequently_modEq h.ne_bot d

/--
theorem `frequently_even` / 定理 `frequently_even`

English:
theorem frequently_even
  statement: existsᶠ m : Nat in atTop, Even m
  proof: by
  simpa only [even_iff] using frequently_mod_eq zero_lt_two

中文:
定理 frequently_even
  结论: 存在ᶠ m : 自然数 in atTop, Even m
  证明: by
  simpa only [even_iff] using frequently_mod_eq zero_lt_two

Depends on / 依赖: even_iff, frequently_mod_eq, zero_lt_two
-/
theorem frequently_even : existsᶠ m : Nat in atTop, Even m := by
  simpa only [even_iff] using frequently_mod_eq zero_lt_two

/--
theorem `frequently_odd` / 定理 `frequently_odd`

English:
theorem frequently_odd
  statement: existsᶠ m : Nat in atTop, Odd m
  proof: by
  simpa only [odd_iff] using frequently_mod_eq one_lt_two

中文:
定理 frequently_odd
  结论: 存在ᶠ m : 自然数 in atTop, Odd m
  证明: by
  simpa only [odd_iff] using frequently_mod_eq one_lt_two

Depends on / 依赖: frequently_mod_eq, odd_iff, one_lt_two
-/
theorem frequently_odd : existsᶠ m : Nat in atTop, Odd m := by
  simpa only [odd_iff] using frequently_mod_eq one_lt_two

end Nat

/--
theorem `Filter.nonneg_of_eventually_pow_nonneg` / 定理 `Filter.nonneg_of_eventually_pow_nonneg`

English:
theorem Filter.nonneg_of_eventually_pow_nonneg
  statement: {α : Type*}
  proof: let ⟨_n, ho, hn⟩ := (Nat.frequently_odd.and_eventually h).exists
  ho.pow_nonneg_iff.1 hn

中文:
定理 滤子.nonneg_of_eventually_pow_nonneg
  结论: {α : 类型}
  证明: let ⟨_n, ho, hn⟩ := (Nat.frequently_odd.and_eventually h).exists
  ho.pow_nonneg_iff.1 hn

Depends on / 依赖: Nat.frequently_odd.and_eventually, and_eventually, frequently_odd, ho.pow_nonneg_iff, pow_nonneg_iff
-/
theorem Filter.nonneg_of_eventually_pow_nonneg {α : Type*}
    [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}
    (h : forallᶠ n in atTop, 0 <= a ^ (n : Nat)) : 0 <= a :=
  let ⟨_n, ho, hn⟩ := (Nat.frequently_odd.and_eventually h).exists
  ho.pow_nonneg_iff.1 hn
