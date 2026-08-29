/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Basic
public import Mathlib.Logic.Nontrivial.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Tactic.GCongr.Core

/-!
# Basic operations on the natural numbers

This file builds on `Mathlib/Data/Nat/Init.lean` by adding basic lemmas on natural numbers
depending on Mathlib definitions.

See note [foundational algebra order theory].
-/

public section

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid

open Function

namespace Nat
variable {a b c d m n k : Nat} {p : Nat -> Prop}

-- TODO: Move the `LinearOrder ℕ` instance to `Order.Nat` (https://github.com/leanprover-community/mathlib4/pull/13092).
/--
Instance `instLinearOrder` / 实例 `instLinearOrder`

English:
instance instLinearOrder
  signature: : LinearOrder Nat where
  body: Nat.le
  le_refl := @Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  lt := Nat.lt
  lt_iff_le_not_ge := @Nat.lt_iff_le_and_not_ge
  toDecidableLT := inferInstance
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance

中文:
实例 instLinearOrder
  签名: : 线性序 自然数 where
  定义体: Nat.le
  le_refl := @Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  lt := Nat.lt
  lt_iff_le_not_ge := @Nat.lt_iff_le_and_not_ge
  toDecidableLT := inferInstance
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance

Depends on / 依赖: Nat.le
-/
instance instLinearOrder : LinearOrder Nat where
  le := Nat.le
  le_refl := @Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  lt := Nat.lt
  lt_iff_le_not_ge := @Nat.lt_iff_le_and_not_ge
  toDecidableLT := inferInstance
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance

-- Shortcut instances
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder Nat
  body: inferInstance

中文:
实例 :
  签名: 预序 自然数
  定义体: inferInstance
-/
instance : Preorder Nat := inferInstance
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder Nat
  body: inferInstance

中文:
实例 :
  签名: 偏序 自然数
  定义体: inferInstance
-/
instance : PartialOrder Nat := inferInstance

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: : Nontrivial Nat
  body: ⟨⟨0, 1, Nat.zero_ne_one⟩⟩

中文:
实例 instNontrivial
  签名: : 非平凡 自然数
  定义体: ⟨⟨0, 1, Nat.zero_ne_one⟩⟩

Depends on / 依赖: Nat.zero_ne_one, zero_ne_one
-/
instance instNontrivial : Nontrivial Nat := ⟨⟨0, 1, Nat.zero_ne_one⟩⟩

attribute [gcongr] Nat.succ_le_succ Nat.div_le_div_right Nat.div_le_div


/--
lemma `succ_injective` / 引理 `succ_injective`

English:
lemma succ_injective
  statement: Injective Nat.succ
  proof: @succ.inj

中文:
引理 succ_injective
  结论: 单射 自然数.succ
  证明: @succ.inj

Depends on / 依赖: succ.inj
-/
lemma succ_injective : Injective Nat.succ := @succ.inj


/--
theorem `div_right_comm` / 定理 `div_right_comm`

English:
theorem div_right_comm
  given: (a b c : Nat)
  statement: a / b / c = a / c / b
  proof: by
  rw [Nat.div_div_eq_div_mul]; rw [Nat.mul_comm]; rw [← Nat.div_div_eq_div_mul]

中文:
定理 div_right_comm
  条件: (a b c : 自然数)
  结论: a / b / c = a / c / b
  证明: by
  rw [Nat.div_div_eq_div_mul]; rw [Nat.mul_comm]; rw [← Nat.div_div_eq_div_mul]
-/
protected theorem div_right_comm (a b c : Nat) : a / b / c = a / c / b := by
  rw [Nat.div_div_eq_div_mul]; rw [Nat.mul_comm]; rw [← Nat.div_div_eq_div_mul]


/--
lemma `pow_left_injective` / 引理 `pow_left_injective`

English:
lemma pow_left_injective
  given: (hn : n != 0)
  statement: Injective (fun a : Nat => a ^ n)
  proof: by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_left hn]

中文:
引理 pow_left_injective
  条件: (hn : n != 0)
  结论: 单射 (fun a : 自然数 => a ^ n)
  证明: by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_left hn]

Depends on / 依赖: Injective, Nat.pow_le_pow_iff_left, le_antisymm_iff, pow_le_pow_iff_left
-/
lemma pow_left_injective (hn : n != 0) : Injective (fun a : Nat => a ^ n) := by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_left hn]

/--
lemma `pow_right_injective` / 引理 `pow_right_injective`

English:
lemma pow_right_injective
  given: (ha : 2 <= a)
  statement: Injective (a ^ ·)
  proof: by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_right ha]

中文:
引理 pow_right_injective
  条件: (ha : 2 <= a)
  结论: 单射 (a ^ ·)
  证明: by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_right ha]
-/
protected lemma pow_right_injective (ha : 2 <= a) : Injective (a ^ ·) := by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_right ha]

/--
theorem `pow_sub_one` / 定理 `pow_sub_one`

English:
theorem pow_sub_one
  given: {x a : Nat} (hx : x != 0) (ha : a != 0)
  proof: by
  rw [← Nat.pow_div (one_le_iff_ne_zero.mpr ha) (Nat.pos_iff_ne_zero.mpr hx)]; rw [Nat.pow_one]

中文:
定理 pow_sub_one
  条件: {x a : 自然数} (hx : x != 0) (ha : a != 0)
  证明: by
  rw [← Nat.pow_div (one_le_iff_ne_zero.mpr ha) (Nat.pos_iff_ne_zero.mpr hx)]; rw [Nat.pow_one]
-/
protected theorem pow_sub_one {x a : Nat} (hx : x != 0) (ha : a != 0) :
    x ^ (a - 1) = x ^ a / x := by
  rw [← Nat.pow_div (one_le_iff_ne_zero.mpr ha) (Nat.pos_iff_ne_zero.mpr hx)]; rw [Nat.pow_one]


/--
lemma `leRecOn_injective` / 引理 `leRecOn_injective`

English:
lemma leRecOn_injective
  statement: {C : Nat -> Sort*} {n m} (hnm : n <= m) (next : forall {k}, C k -> C (k + 1))
  proof: by
  induction hnm with
  | refl =>
    intro x y H
    rwa [leRecOn_self, leRecOn_self] at H
  | step hnm ih =>
    intro x y H
    rw [leRecOn_succ hnm]; rw [leRecOn_succ hnm] at H
    exact ih (Hnext _ H)

中文:
引理 leRecOn_injective
  结论: {C : 自然数 -> 类型层*} {n m} (hnm : n <= m) (next : 对任意 {k}, C k -> C (k + 1))
  证明: by
  induction hnm with
  | refl =>
    intro x y H
    rwa [leRecOn_self, leRecOn_self] at H
  | step hnm ih =>
    intro x y H
    rw [leRecOn_succ hnm]; rw [leRecOn_succ hnm] at H
    exact ih (Hnext _ H)

Depends on / 依赖: leRecOn_self, leRecOn_succ
-/
lemma leRecOn_injective {C : Nat -> Sort*} {n m} (hnm : n <= m) (next : forall {k}, C k -> C (k + 1))
    (Hnext : forall n, Injective (@next n)) : Injective (@leRecOn C n m hnm next) := by
  induction hnm with
  | refl =>
    intro x y H
    rwa [leRecOn_self, leRecOn_self] at H
  | step hnm ih =>
    intro x y H
    rw [leRecOn_succ hnm]; rw [leRecOn_succ hnm] at H
    exact ih (Hnext _ H)

/--
lemma `leRecOn_surjective` / 引理 `leRecOn_surjective`

English:
lemma leRecOn_surjective
  statement: {C : Nat -> Sort*} {n m} (hnm : n <= m) (next : forall {k}, C k -> C (k + 1))
  proof: by
  induction hnm with
  | refl =>
    intro x
    refine ⟨x, ?_⟩
    rw [leRecOn_self]
  | step hnm ih =>
    intro x
    obtain ⟨w, rfl⟩ := Hnext _ x
    obtain ⟨x, rfl⟩ := ih w
    refine ⟨x, ?_⟩
    rw [leRecOn_succ]

中文:
引理 leRecOn_surjective
  结论: {C : 自然数 -> 类型层*} {n m} (hnm : n <= m) (next : 对任意 {k}, C k -> C (k + 1))
  证明: by
  induction hnm with
  | refl =>
    intro x
    refine ⟨x, ?_⟩
    rw [leRecOn_self]
  | step hnm ih =>
    intro x
    obtain ⟨w, rfl⟩ := Hnext _ x
    obtain ⟨x, rfl⟩ := ih w
    refine ⟨x, ?_⟩
    rw [leRecOn_succ]

Depends on / 依赖: leRecOn_self, leRecOn_succ
-/
lemma leRecOn_surjective {C : Nat -> Sort*} {n m} (hnm : n <= m) (next : forall {k}, C k -> C (k + 1))
    (Hnext : forall n, Surjective (@next n)) : Surjective (@leRecOn C n m hnm next) := by
  induction hnm with
  | refl =>
    intro x
    refine ⟨x, ?_⟩
    rw [leRecOn_self]
  | step hnm ih =>
    intro x
    obtain ⟨w, rfl⟩ := Hnext _ x
    obtain ⟨x, rfl⟩ := ih w
    refine ⟨x, ?_⟩
    rw [leRecOn_succ]


/--
lemma `set_induction_bounded` / 引理 `set_induction_bounded`

English:
lemma set_induction_bounded
  statement: {S : Set Nat} (hk : k in S) (h_ind : forall k : Nat, k in S -> k + 1 in S)
  proof: @leRecOn (fun n => n in S) k n hnk @h_ind hk

中文:
引理 set_induction_bounded
  结论: {S : 集合 自然数} (hk : k in S) (h_ind : 对任意 k : 自然数, k in S -> k + 1 in S)
  证明: @leRecOn (fun n => n in S) k n hnk @h_ind hk

Depends on / 依赖: h_ind, leRecOn
-/
lemma set_induction_bounded {S : Set Nat} (hk : k in S) (h_ind : forall k : Nat, k in S -> k + 1 in S)
    (hnk : k <= n) : n in S :=
  @leRecOn (fun n => n in S) k n hnk @h_ind hk

/--
lemma `set_induction` / 引理 `set_induction`

English:
lemma set_induction
  given: {S : Set Nat} (hb : 0 in S) (h_ind : forall k : Nat, k in S -> k + 1 in S) (n : Nat)
  proof: set_induction_bounded hb h_ind (zero_le n)

中文:
引理 set_induction
  条件: {S : 集合 自然数} (hb : 0 in S) (h_ind : 对任意 k : 自然数, k in S -> k + 1 in S) (n : 自然数)
  证明: set_induction_bounded hb h_ind (zero_le n)

Depends on / 依赖: h_ind, set_induction_bounded, zero_le
-/
lemma set_induction {S : Set Nat} (hb : 0 in S) (h_ind : forall k : Nat, k in S -> k + 1 in S) (n : Nat) :
    n in S :=
  set_induction_bounded hb h_ind (zero_le n)

/-! ### `mod`, `dvd` -/

/--
lemma `dvd_left_injective` / 引理 `dvd_left_injective`

English:
lemma dvd_left_injective
  statement: Function.Injective ((· ∣ ·) : Nat -> Nat -> Prop)
  proof: fun _ _ h =>
  dvd_right_iff_eq.mp fun a => iff_of_eq (congr_fun h a)

@[simp]

中文:
引理 dvd_left_injective
  结论: 函数.单射 ((· ∣ ·) : 自然数 -> 自然数 -> 命题)
  证明: fun _ _ h =>
  dvd_right_iff_eq.mp fun a => iff_of_eq (congr_fun h a)

@[simp]
-/
lemma dvd_left_injective : Function.Injective ((· ∣ ·) : Nat -> Nat -> Prop) := fun _ _ h =>
  dvd_right_iff_eq.mp fun a => iff_of_eq (congr_fun h a)

@[simp]
/--
lemma `dvd_sub_self_left` / 引理 `dvd_sub_self_left`

English:
lemma dvd_sub_self_left
  given: {n m : Nat}
  proof: by
  rcases le_or_gt n m with h | h
  · simp [h]
  · rcases eq_or_ne m 0 with rfl | hm
    · simp
    · simp only [hm, h.not_ge, or_self, iff_false]
      refine not_dvd_of_pos_of_lt ?_ ?_ <;>
      grind

@[simp]

中文:
引理 dvd_sub_self_left
  条件: {n m : 自然数}
  证明: by
  rcases le_or_gt n m with h | h
  · simp [h]
  · rcases eq_or_ne m 0 with rfl | hm
    · simp
    · simp only [hm, h.not_ge, or_self, iff_false]
      refine not_dvd_of_pos_of_lt ?_ ?_ <;>
      grind

@[simp]
-/
protected lemma dvd_sub_self_left {n m : Nat} :
    n ∣ n - m ↔ m = 0 ∨ n <= m := by
  rcases le_or_gt n m with h | h
  · simp [h]
  · rcases eq_or_ne m 0 with rfl | hm
    · simp
    · simp only [hm, h.not_ge, or_self, iff_false]
      refine not_dvd_of_pos_of_lt ?_ ?_ <;>
      grind

@[simp]
/--
lemma `dvd_sub_self_right` / 引理 `dvd_sub_self_right`

English:
lemma dvd_sub_self_right
  given: {n m : Nat}
  proof: by
  rcases le_or_gt m n with h | h
  · simp [h]
  · simp [dvd_sub_iff_left (le_of_lt h) (Nat.dvd_refl _), h.not_ge]

中文:
引理 dvd_sub_self_right
  条件: {n m : 自然数}
  证明: by
  rcases le_or_gt m n with h | h
  · simp [h]
  · simp [dvd_sub_iff_left (le_of_lt h) (Nat.dvd_refl _), h.not_ge]
-/
protected lemma dvd_sub_self_right {n m : Nat} :
    n ∣ m - n ↔ n ∣ m ∨ m <= n := by
  rcases le_or_gt m n with h | h
  · simp [h]
  · simp [dvd_sub_iff_left (le_of_lt h) (Nat.dvd_refl _), h.not_ge]


/--
lemma `mul_le_pow` / 引理 `mul_le_pow`

English:
lemma mul_le_pow
  given: {a : Nat} (ha : a != 1) (b : Nat)
  proof: by
  cases b with
  | zero => exact Nat.zero_le _
  | succ b =>
      obtain rfl | ha0 : a = 0 ∨ a > 0 := a.eq_zero_or_pos
      · rw [Nat.zero_mul]; exact Nat.zero_le _
      · have ha1 : a > 1 := Nat.lt_of_le_of_ne ha0 ha.symm
        rw [Nat.pow_succ']; exact Nat.mul_le_mul_left a (Nat.lt_pow_self ha1)

中文:
引理 mul_le_pow
  条件: {a : 自然数} (ha : a != 1) (b : 自然数)
  证明: by
  cases b with
  | zero => exact Nat.zero_le _
  | succ b =>
      obtain rfl | ha0 : a = 0 ∨ a > 0 := a.eq_zero_or_pos
      · rw [Nat.zero_mul]; exact Nat.zero_le _
      · have ha1 : a > 1 := Nat.lt_of_le_of_ne ha0 ha.symm
        rw [Nat.pow_succ']; exact Nat.mul_le_mul_left a (Nat.lt_pow_self ha1)

Depends on / 依赖: Nat.lt_of_le_of_ne, Nat.lt_pow_self, Nat.mul_le_mul_left, Nat.pow_succ, Nat.zero_le, Nat.zero_mul, a.eq_zero_or_pos, eq_zero_or_pos, ha.symm, lt_of_le_of_ne, lt_pow_self, mul_le_mul_left, pow_succ, zero_le, zero_mul
-/
lemma mul_le_pow {a : Nat} (ha : a != 1) (b : Nat) :
    a * b <= a ^ b := by
  cases b with
  | zero => exact Nat.zero_le _
  | succ b =>
      obtain rfl | ha0 : a = 0 ∨ a > 0 := a.eq_zero_or_pos
      · rw [Nat.zero_mul]; exact Nat.zero_le _
      · have ha1 : a > 1 := Nat.lt_of_le_of_ne ha0 ha.symm
        rw [Nat.pow_succ']; exact Nat.mul_le_mul_left a (Nat.lt_pow_self ha1)

/--
lemma `two_mul_sq_add_one_le_two_pow_two_mul` / 引理 `two_mul_sq_add_one_le_two_pow_two_mul`

English:
lemma two_mul_sq_add_one_le_two_pow_two_mul
  given: (k : Nat)
  statement: 2 * k ^ 2 + 1 <= 2 ^ (2 * k)
  proof: by
  obtain rfl | hk : k = 0 ∨ k > 0 := k.eq_zero_or_pos
  · decide
  · have hk0 : 0 < 2 * k ^ 2 := Nat.mul_pos Nat.two_pos (Nat.pow_pos hk)
    calc 2 * k ^ 2
      _ < 2 * k ^ 2 + 2 * k ^ 2 := Nat.lt_add_of_pos_left hk0
      _ = (2 * k) ^ 2 := by rw [Nat.mul_pow, ← Nat.add_mul]
      _ <= (2 ^ k) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_pow (by decide : 2 != 1) _) 2
      _ = 2 ^ (2 * k) := (Nat.pow_mul' _ _ _).symm

中文:
引理 two_mul_sq_add_one_le_two_pow_two_mul
  条件: (k : 自然数)
  结论: 2 * k ^ 2 + 1 <= 2 ^ (2 * k)
  证明: by
  obtain rfl | hk : k = 0 ∨ k > 0 := k.eq_zero_or_pos
  · decide
  · have hk0 : 0 < 2 * k ^ 2 := Nat.mul_pos Nat.two_pos (Nat.pow_pos hk)
    calc 2 * k ^ 2
      _ < 2 * k ^ 2 + 2 * k ^ 2 := Nat.lt_add_of_pos_left hk0
      _ = (2 * k) ^ 2 := by rw [Nat.mul_pow, ← Nat.add_mul]
      _ <= (2 ^ k) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_pow (by decide : 2 != 1) _) 2
      _ = 2 ^ (2 * k) := (Nat.pow_mul' _ _ _).symm

Depends on / 依赖: Nat.add_mul, Nat.lt_add_of_pos_left, Nat.mul_le_pow, Nat.mul_pos, Nat.mul_pow, Nat.pow_le_pow_left, Nat.pow_mul, Nat.pow_pos, Nat.two_pos, add_mul, eq_zero_or_pos, k.eq_zero_or_pos, lt_add_of_pos_left, mul_le_pow, mul_pos, mul_pow, pow_le_pow_left, pow_mul, pow_pos, two_pos
-/
lemma two_mul_sq_add_one_le_two_pow_two_mul (k : Nat) : 2 * k ^ 2 + 1 <= 2 ^ (2 * k) := by
  obtain rfl | hk : k = 0 ∨ k > 0 := k.eq_zero_or_pos
  · decide
  · have hk0 : 0 < 2 * k ^ 2 := Nat.mul_pos Nat.two_pos (Nat.pow_pos hk)
    calc 2 * k ^ 2
      _ < 2 * k ^ 2 + 2 * k ^ 2 := Nat.lt_add_of_pos_left hk0
      _ = (2 * k) ^ 2 := by rw [Nat.mul_pow, ← Nat.add_mul]
      _ <= (2 ^ k) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_pow (by decide : 2 != 1) _) 2
      _ = 2 ^ (2 * k) := (Nat.pow_mul' _ _ _).symm

end Nat
