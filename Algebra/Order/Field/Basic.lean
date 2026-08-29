/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Set.Monotone
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Tactic.Positivity.Core

/-!
# Lemmas about (linear) ordered (semi)fields
-/

@[expose] public section


open Function OrderDual

variable {ι α β : Type*}

section PartialOrderedSemifield

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : Int}

attribute [local instance] PosMulReflectLT.toMulPosReflectLT

/-!
### Relating one division and involving `1`
-/

@[bound]
/--
theorem `le_div_self` / 定理 `le_div_self`

English:
theorem le_div_self
  given: (ha : 0 <= a) (hb₀ : 0 < b) (hb₁ : b <= 1)
  statement: a <= a / b
  proof: by
  simpa only [div_one] using div_le_div_of_nonneg_left ha hb₀ hb₁

中文:
定理 le_div_self
  条件: (ha : 0 <= a) (hb₀ : 0 < b) (hb₁ : b <= 1)
  结论: a <= a / b
  证明: by
  simpa only [div_one] using div_le_div_of_nonneg_left ha hb₀ hb₁

Depends on / 依赖: div_le_div_of_nonneg_left, div_one
-/
theorem le_div_self (ha : 0 <= a) (hb₀ : 0 < b) (hb₁ : b <= 1) : a <= a / b := by
  simpa only [div_one] using div_le_div_of_nonneg_left ha hb₀ hb₁

/--
theorem `one_le_div` / 定理 `one_le_div`

English:
theorem one_le_div
  given: (hb : 0 < b)
  statement: 1 <= a / b ↔ b <= a
  proof: by rw [le_div_iff₀ hb, one_mul]

中文:
定理 one_le_div
  条件: (hb : 0 < b)
  结论: 1 <= a / b ↔ b <= a
  证明: by rw [le_div_iff₀ hb, one_mul]

Depends on / 依赖: one_mul
-/
theorem one_le_div (hb : 0 < b) : 1 <= a / b ↔ b <= a := by rw [le_div_iff₀ hb, one_mul]

/--
theorem `div_le_one` / 定理 `div_le_one`

English:
theorem div_le_one
  given: (hb : 0 < b)
  statement: a / b <= 1 ↔ a <= b
  proof: by rw [div_le_iff₀ hb, one_mul]

中文:
定理 div_le_one
  条件: (hb : 0 < b)
  结论: a / b <= 1 ↔ a <= b
  证明: by rw [div_le_iff₀ hb, one_mul]

Depends on / 依赖: one_mul
-/
theorem div_le_one (hb : 0 < b) : a / b <= 1 ↔ a <= b := by rw [div_le_iff₀ hb, one_mul]

/--
theorem `one_lt_div` / 定理 `one_lt_div`

English:
theorem one_lt_div
  given: (hb : 0 < b)
  statement: 1 < a / b ↔ b < a
  proof: by rw [lt_div_iff₀ hb, one_mul]

中文:
定理 one_lt_div
  条件: (hb : 0 < b)
  结论: 1 < a / b ↔ b < a
  证明: by rw [lt_div_iff₀ hb, one_mul]

Depends on / 依赖: one_mul
-/
theorem one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a := by rw [lt_div_iff₀ hb, one_mul]

/--
theorem `div_lt_one` / 定理 `div_lt_one`

English:
theorem div_lt_one
  given: (hb : 0 < b)
  statement: a / b < 1 ↔ a < b
  proof: by rw [div_lt_iff₀ hb, one_mul]

中文:
定理 div_lt_one
  条件: (hb : 0 < b)
  结论: a / b < 1 ↔ a < b
  证明: by rw [div_lt_iff₀ hb, one_mul]

Depends on / 依赖: one_mul
-/
theorem div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b := by rw [div_lt_iff₀ hb, one_mul]

/--
theorem `one_div_le` / 定理 `one_div_le`

English:
theorem one_div_le
  given: (ha : 0 < a) (hb : 0 < b)
  statement: 1 / a <= b ↔ 1 / b <= a
  proof: by
  simpa using inv_le_comm₀ ha hb

中文:
定理 one_div_le
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: 1 / a <= b ↔ 1 / b <= a
  证明: by
  simpa using inv_le_comm₀ ha hb
-/
theorem one_div_le (ha : 0 < a) (hb : 0 < b) : 1 / a <= b ↔ 1 / b <= a := by
  simpa using inv_le_comm₀ ha hb

/--
theorem `one_div_lt` / 定理 `one_div_lt`

English:
theorem one_div_lt
  given: (ha : 0 < a) (hb : 0 < b)
  statement: 1 / a < b ↔ 1 / b < a
  proof: by
  simpa using inv_lt_comm₀ ha hb

中文:
定理 one_div_lt
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: 1 / a < b ↔ 1 / b < a
  证明: by
  simpa using inv_lt_comm₀ ha hb
-/
theorem one_div_lt (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a := by
  simpa using inv_lt_comm₀ ha hb

/--
theorem `le_one_div` / 定理 `le_one_div`

English:
theorem le_one_div
  given: (ha : 0 < a) (hb : 0 < b)
  statement: a <= 1 / b ↔ b <= 1 / a
  proof: by
  simpa using le_inv_comm₀ ha hb

中文:
定理 le_one_div
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: a <= 1 / b ↔ b <= 1 / a
  证明: by
  simpa using le_inv_comm₀ ha hb
-/
theorem le_one_div (ha : 0 < a) (hb : 0 < b) : a <= 1 / b ↔ b <= 1 / a := by
  simpa using le_inv_comm₀ ha hb

/--
theorem `lt_one_div` / 定理 `lt_one_div`

English:
theorem lt_one_div
  given: (ha : 0 < a) (hb : 0 < b)
  statement: a < 1 / b ↔ b < 1 / a
  proof: by
  simpa using lt_inv_comm₀ ha hb

中文:
定理 lt_one_div
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: a < 1 / b ↔ b < 1 / a
  证明: by
  simpa using lt_inv_comm₀ ha hb
-/
theorem lt_one_div (ha : 0 < a) (hb : 0 < b) : a < 1 / b ↔ b < 1 / a := by
  simpa using lt_inv_comm₀ ha hb

/--
lemma `Bound.one_lt_div_of_pos_of_lt` / 引理 `Bound.one_lt_div_of_pos_of_lt`

English:
lemma Bound.one_lt_div_of_pos_of_lt
  given: (b0 : 0 < b)
  statement: b < a -> 1 < a / b
  proof: (one_lt_div b0).mpr

中文:
引理 Bound.one_lt_div_of_pos_of_lt
  条件: (b0 : 0 < b)
  结论: b < a -> 1 < a / b
  证明: (one_lt_div b0).mpr
-/
@[bound] lemma Bound.one_lt_div_of_pos_of_lt (b0 : 0 < b) : b < a -> 1 < a / b := (one_lt_div b0).mpr

/--
lemma `Bound.div_lt_one_of_pos_of_lt` / 引理 `Bound.div_lt_one_of_pos_of_lt`

English:
lemma Bound.div_lt_one_of_pos_of_lt
  given: (b0 : 0 < b)
  statement: a < b -> a / b < 1
  proof: (div_lt_one b0).mpr

中文:
引理 Bound.div_lt_one_of_pos_of_lt
  条件: (b0 : 0 < b)
  结论: a < b -> a / b < 1
  证明: (div_lt_one b0).mpr
-/
@[bound] lemma Bound.div_lt_one_of_pos_of_lt (b0 : 0 < b) : a < b -> a / b < 1 := (div_lt_one b0).mpr


/--
theorem `one_div_le_one_div_of_le` / 定理 `one_div_le_one_div_of_le`

English:
theorem one_div_le_one_div_of_le
  given: (ha : 0 < a) (h : a <= b)
  statement: 1 / b <= 1 / a
  proof: by
  simpa using inv_anti₀ ha h

中文:
定理 one_div_le_one_div_of_le
  条件: (ha : 0 < a) (h : a <= b)
  结论: 1 / b <= 1 / a
  证明: by
  simpa using inv_anti₀ ha h
-/
theorem one_div_le_one_div_of_le (ha : 0 < a) (h : a <= b) : 1 / b <= 1 / a := by
  simpa using inv_anti₀ ha h

/--
theorem `one_div_lt_one_div_of_lt` / 定理 `one_div_lt_one_div_of_lt`

English:
theorem one_div_lt_one_div_of_lt
  given: (ha : 0 < a) (h : a < b)
  statement: 1 / b < 1 / a
  proof: by
  rwa [lt_div_iff₀' ha, ← div_eq_mul_one_div, div_lt_one (ha.trans h)]

中文:
定理 one_div_lt_one_div_of_lt
  条件: (ha : 0 < a) (h : a < b)
  结论: 1 / b < 1 / a
  证明: by
  rwa [lt_div_iff₀' ha, ← div_eq_mul_one_div, div_lt_one (ha.trans h)]

Depends on / 依赖: div_eq_mul_one_div, div_lt_one, ha.trans
-/
theorem one_div_lt_one_div_of_lt (ha : 0 < a) (h : a < b) : 1 / b < 1 / a := by
  rwa [lt_div_iff₀' ha, ← div_eq_mul_one_div, div_lt_one (ha.trans h)]

/--
theorem `le_of_one_div_le_one_div` / 定理 `le_of_one_div_le_one_div`

English:
theorem le_of_one_div_le_one_div
  given: (ha : 0 < a) (h : 1 / a <= 1 / b)
  statement: b <= a
  proof: by
  simpa using one_div_le_one_div_of_le (by simpa) h

中文:
定理 le_of_one_div_le_one_div
  条件: (ha : 0 < a) (h : 1 / a <= 1 / b)
  结论: b <= a
  证明: by
  simpa using one_div_le_one_div_of_le (by simpa) h

Depends on / 依赖: one_div_le_one_div_of_le
-/
theorem le_of_one_div_le_one_div (ha : 0 < a) (h : 1 / a <= 1 / b) : b <= a := by
  simpa using one_div_le_one_div_of_le (by simpa) h

/--
theorem `lt_of_one_div_lt_one_div` / 定理 `lt_of_one_div_lt_one_div`

English:
theorem lt_of_one_div_lt_one_div
  given: (ha : 0 < a) (h : 1 / a < 1 / b)
  statement: b < a
  proof: by
  simpa using one_div_lt_one_div_of_lt (by simpa) h

中文:
定理 lt_of_one_div_lt_one_div
  条件: (ha : 0 < a) (h : 1 / a < 1 / b)
  结论: b < a
  证明: by
  simpa using one_div_lt_one_div_of_lt (by simpa) h

Depends on / 依赖: one_div_lt_one_div_of_lt
-/
theorem lt_of_one_div_lt_one_div (ha : 0 < a) (h : 1 / a < 1 / b) : b < a := by
  simpa using one_div_lt_one_div_of_lt (by simpa) h

variable [IsStrictOrderedRing α]

@[bound]
/--
theorem `div_le_self` / 定理 `div_le_self`

English:
theorem div_le_self
  given: (ha : 0 <= a) (hb : 1 <= b)
  statement: a / b <= a
  proof: by
  simpa only [div_one] using div_le_div_of_nonneg_left ha zero_lt_one hb

@[bound]

中文:
定理 div_le_self
  条件: (ha : 0 <= a) (hb : 1 <= b)
  结论: a / b <= a
  证明: by
  simpa only [div_one] using div_le_div_of_nonneg_left ha zero_lt_one hb

@[bound]

Depends on / 依赖: div_le_div_of_nonneg_left, div_one, zero_lt_one
-/
theorem div_le_self (ha : 0 <= a) (hb : 1 <= b) : a / b <= a := by
  simpa only [div_one] using div_le_div_of_nonneg_left ha zero_lt_one hb

@[bound]
/--
theorem `div_lt_self` / 定理 `div_lt_self`

English:
theorem div_lt_self
  given: (ha : 0 < a) (hb : 1 < b)
  statement: a / b < a
  proof: by
  simpa only [div_one] using div_lt_div_of_pos_left ha zero_lt_one hb

中文:
定理 div_lt_self
  条件: (ha : 0 < a) (hb : 1 < b)
  结论: a / b < a
  证明: by
  simpa only [div_one] using div_lt_div_of_pos_left ha zero_lt_one hb

Depends on / 依赖: div_lt_div_of_pos_left, div_one, zero_lt_one
-/
theorem div_lt_self (ha : 0 < a) (hb : 1 < b) : a / b < a := by
  simpa only [div_one] using div_lt_div_of_pos_left ha zero_lt_one hb

/--
theorem `one_div_le_one_div` / 定理 `one_div_le_one_div`

English:
theorem one_div_le_one_div
  given: (ha : 0 < a) (hb : 0 < b)
  statement: 1 / a <= 1 / b ↔ b <= a
  proof: div_le_div_iff_of_pos_left zero_lt_one ha hb

中文:
定理 one_div_le_one_div
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: 1 / a <= 1 / b ↔ b <= a
  证明: div_le_div_iff_of_pos_left zero_lt_one ha hb

Depends on / 依赖: div_le_div_iff_of_pos_left, zero_lt_one
-/
theorem one_div_le_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a <= 1 / b ↔ b <= a :=
  div_le_div_iff_of_pos_left zero_lt_one ha hb

/--
theorem `one_div_lt_one_div` / 定理 `one_div_lt_one_div`

English:
theorem one_div_lt_one_div
  given: (ha : 0 < a) (hb : 0 < b)
  statement: 1 / a < 1 / b ↔ b < a
  proof: div_lt_div_iff_of_pos_left zero_lt_one ha hb

中文:
定理 one_div_lt_one_div
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: 1 / a < 1 / b ↔ b < a
  证明: div_lt_div_iff_of_pos_left zero_lt_one ha hb

Depends on / 依赖: div_lt_div_iff_of_pos_left, zero_lt_one
-/
theorem one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a < 1 / b ↔ b < a :=
  div_lt_div_iff_of_pos_left zero_lt_one ha hb

/--
theorem `one_lt_one_div` / 定理 `one_lt_one_div`

English:
theorem one_lt_one_div
  given: (h1 : 0 < a) (h2 : a < 1)
  statement: 1 < 1 / a
  proof: by
  rwa [lt_one_div (@zero_lt_one α _ _ _ _ _) h1, one_div_one]

中文:
定理 one_lt_one_div
  条件: (h1 : 0 < a) (h2 : a < 1)
  结论: 1 < 1 / a
  证明: by
  rwa [lt_one_div (@zero_lt_one α _ _ _ _ _) h1, one_div_one]

Depends on / 依赖: lt_one_div, one_div_one, zero_lt_one
-/
theorem one_lt_one_div (h1 : 0 < a) (h2 : a < 1) : 1 < 1 / a := by
  rwa [lt_one_div (@zero_lt_one α _ _ _ _ _) h1, one_div_one]

/--
theorem `one_le_one_div` / 定理 `one_le_one_div`

English:
theorem one_le_one_div
  given: (h1 : 0 < a) (h2 : a <= 1)
  statement: 1 <= 1 / a
  proof: by
  rwa [le_one_div (@zero_lt_one α _ _ _ _ _) h1, one_div_one]

中文:
定理 one_le_one_div
  条件: (h1 : 0 < a) (h2 : a <= 1)
  结论: 1 <= 1 / a
  证明: by
  rwa [le_one_div (@zero_lt_one α _ _ _ _ _) h1, one_div_one]

Depends on / 依赖: le_one_div, one_div_one, zero_lt_one
-/
theorem one_le_one_div (h1 : 0 < a) (h2 : a <= 1) : 1 <= 1 / a := by
  rwa [le_one_div (@zero_lt_one α _ _ _ _ _) h1, one_div_one]


/--
theorem `half_pos` / 定理 `half_pos`

English:
theorem half_pos
  given: (h : 0 < a)
  statement: 0 < a / 2
  proof: div_pos h zero_lt_two

中文:
定理 half_pos
  条件: (h : 0 < a)
  结论: 0 < a / 2
  证明: div_pos h zero_lt_two

Depends on / 依赖: div_pos, zero_lt_two
-/
theorem half_pos (h : 0 < a) : 0 < a / 2 :=
  div_pos h zero_lt_two

/--
theorem `one_half_pos` / 定理 `one_half_pos`

English:
theorem one_half_pos
  statement: (0 : α) < 1 / 2
  proof: half_pos zero_lt_one

@[simp]

中文:
定理 one_half_pos
  结论: (0 : α) < 1 / 2
  证明: half_pos zero_lt_one

@[simp]

Depends on / 依赖: half_pos, zero_lt_one
-/
theorem one_half_pos : (0 : α) < 1 / 2 :=
  half_pos zero_lt_one

@[simp]
/--
theorem `half_le_self_iff` / 定理 `half_le_self_iff`

English:
theorem half_le_self_iff
  statement: a / 2 <= a ↔ 0 <= a
  proof: by
  rw [div_le_iff₀ (zero_lt_two' α)]; rw [mul_two]; rw [le_add_iff_nonneg_left]

@[simp]

中文:
定理 half_le_self_iff
  结论: a / 2 <= a ↔ 0 <= a
  证明: by
  rw [div_le_iff₀ (zero_lt_two' α)]; rw [mul_two]; rw [le_add_iff_nonneg_left]

@[simp]

Depends on / 依赖: le_add_iff_nonneg_left, mul_two, zero_lt_two
-/
theorem half_le_self_iff : a / 2 <= a ↔ 0 <= a := by
  rw [div_le_iff₀ (zero_lt_two' α)]; rw [mul_two]; rw [le_add_iff_nonneg_left]

@[simp]
/--
theorem `half_lt_self_iff` / 定理 `half_lt_self_iff`

English:
theorem half_lt_self_iff
  statement: a / 2 < a ↔ 0 < a
  proof: by
  rw [div_lt_iff₀ (zero_lt_two' α)]; rw [mul_two]; rw [lt_add_iff_pos_left]

alias ⟨_, half_le_self⟩ := half_le_self_iff

alias ⟨_, half_lt_self⟩ := half_lt_self_iff

alias div_two_lt_of_pos := half_lt_self

中文:
定理 half_lt_self_iff
  结论: a / 2 < a ↔ 0 < a
  证明: by
  rw [div_lt_iff₀ (zero_lt_two' α)]; rw [mul_two]; rw [lt_add_iff_pos_left]

alias ⟨_, half_le_self⟩ := half_le_self_iff

alias ⟨_, half_lt_self⟩ := half_lt_self_iff

alias div_two_lt_of_pos := half_lt_self

Depends on / 依赖: lt_add_iff_pos_left, mul_two, zero_lt_two
-/
theorem half_lt_self_iff : a / 2 < a ↔ 0 < a := by
  rw [div_lt_iff₀ (zero_lt_two' α)]; rw [mul_two]; rw [lt_add_iff_pos_left]

alias ⟨_, half_le_self⟩ := half_le_self_iff

alias ⟨_, half_lt_self⟩ := half_lt_self_iff

alias div_two_lt_of_pos := half_lt_self

/--
theorem `one_half_lt_one` / 定理 `one_half_lt_one`

English:
theorem one_half_lt_one
  statement: (1 / 2 : α) < 1
  proof: half_lt_self zero_lt_one

中文:
定理 one_half_lt_one
  结论: (1 / 2 : α) < 1
  证明: half_lt_self zero_lt_one

Depends on / 依赖: half_lt_self, zero_lt_one
-/
theorem one_half_lt_one : (1 / 2 : α) < 1 :=
  half_lt_self zero_lt_one

/--
theorem `two_inv_lt_one` / 定理 `two_inv_lt_one`

English:
theorem two_inv_lt_one
  statement: (2⁻¹ : α) < 1
  proof: (one_div _).symm.trans_lt one_half_lt_one

中文:
定理 two_inv_lt_one
  结论: (2⁻¹ : α) < 1
  证明: (one_div _).symm.trans_lt one_half_lt_one

Depends on / 依赖: one_div, one_half_lt_one, symm.trans_lt, trans_lt
-/
theorem two_inv_lt_one : (2⁻¹ : α) < 1 :=
  (one_div _).symm.trans_lt one_half_lt_one

/--
theorem `left_lt_add_div_two` / 定理 `left_lt_add_div_two`

English:
theorem left_lt_add_div_two
  statement: a < (a + b) / 2 ↔ a < b
  proof: by simp [lt_div_iff₀, mul_two]

中文:
定理 left_lt_add_div_two
  结论: a < (a + b) / 2 ↔ a < b
  证明: by simp [lt_div_iff₀, mul_two]

Depends on / 依赖: mul_two
-/
theorem left_lt_add_div_two : a < (a + b) / 2 ↔ a < b := by simp [lt_div_iff₀, mul_two]

/--
theorem `add_div_two_lt_right` / 定理 `add_div_two_lt_right`

English:
theorem add_div_two_lt_right
  statement: (a + b) / 2 < b ↔ a < b
  proof: by simp [div_lt_iff₀, mul_two]

omit [PosMulReflectLT α] in

中文:
定理 add_div_two_lt_right
  结论: (a + b) / 2 < b ↔ a < b
  证明: by simp [div_lt_iff₀, mul_two]

omit [PosMulReflectLT α] in

Depends on / 依赖: mul_two
-/
theorem add_div_two_lt_right : (a + b) / 2 < b ↔ a < b := by simp [div_lt_iff₀, mul_two]

omit [PosMulReflectLT α] in
/--
theorem `add_thirds` / 定理 `add_thirds`

English:
theorem add_thirds
  given: (a : α)
  statement: a / 3 + a / 3 + a / 3 = a
  proof: by
  rw [← add_div]; rw [← add_div]; rw [← two_mul]; rw [← add_one_mul 2 a]; rw [two_add_one_eq_three]; rw [mul_div_cancel_left₀ a three_ne_zero]

中文:
定理 add_thirds
  条件: (a : α)
  结论: a / 3 + a / 3 + a / 3 = a
  证明: by
  rw [← add_div]; rw [← add_div]; rw [← two_mul]; rw [← add_one_mul 2 a]; rw [two_add_one_eq_three]; rw [mul_div_cancel_left₀ a three_ne_zero]

Depends on / 依赖: add_div, add_one_mul, three_ne_zero, two_add_one_eq_three, two_mul
-/
theorem add_thirds (a : α) : a / 3 + a / 3 + a / 3 = a := by
  rw [← add_div]; rw [← add_div]; rw [← two_mul]; rw [← add_one_mul 2 a]; rw [two_add_one_eq_three]; rw [mul_div_cancel_left₀ a three_ne_zero]


/--
lemma `div_pos_iff_of_pos_left` / 引理 `div_pos_iff_of_pos_left`

English:
lemma div_pos_iff_of_pos_left
  given: (ha : 0 < a)
  statement: 0 < a / b ↔ 0 < b
  proof: by
  simp only [div_eq_mul_inv, mul_pos_iff_of_pos_left ha, inv_pos]

中文:
引理 div_pos_iff_of_pos_left
  条件: (ha : 0 < a)
  结论: 0 < a / b ↔ 0 < b
  证明: by
  simp only [div_eq_mul_inv, mul_pos_iff_of_pos_left ha, inv_pos]
-/
@[simp] lemma div_pos_iff_of_pos_left (ha : 0 < a) : 0 < a / b ↔ 0 < b := by
  simp only [div_eq_mul_inv, mul_pos_iff_of_pos_left ha, inv_pos]

/--
lemma `div_pos_iff_of_pos_right` / 引理 `div_pos_iff_of_pos_right`

English:
lemma div_pos_iff_of_pos_right
  given: (hb : 0 < b)
  statement: 0 < a / b ↔ 0 < a
  proof: by
  simp only [div_eq_mul_inv, mul_pos_iff_of_pos_right (inv_pos.2 hb)]

中文:
引理 div_pos_iff_of_pos_right
  条件: (hb : 0 < b)
  结论: 0 < a / b ↔ 0 < a
  证明: by
  simp only [div_eq_mul_inv, mul_pos_iff_of_pos_right (inv_pos.2 hb)]
-/
@[simp] lemma div_pos_iff_of_pos_right (hb : 0 < b) : 0 < a / b ↔ 0 < a := by
  simp only [div_eq_mul_inv, mul_pos_iff_of_pos_right (inv_pos.2 hb)]

/--
theorem `div_mul_le_div_mul_of_div_le_div` / 定理 `div_mul_le_div_mul_of_div_le_div`

English:
theorem div_mul_le_div_mul_of_div_le_div
  given: (h : a / b <= c / d) (he : 0 <= e)
  proof: by
  rw [div_mul_eq_div_mul_one_div]; rw [div_mul_eq_div_mul_one_div]
  gcongr
  exact one_div_nonneg.2 he

omit [IsStrictOrderedRing α] in

中文:
定理 div_mul_le_div_mul_of_div_le_div
  条件: (h : a / b <= c / d) (he : 0 <= e)
  证明: by
  rw [div_mul_eq_div_mul_one_div]; rw [div_mul_eq_div_mul_one_div]
  gcongr
  exact one_div_nonneg.2 he

omit [IsStrictOrderedRing α] in

Depends on / 依赖: div_mul_eq_div_mul_one_div, one_div_nonneg
-/
theorem div_mul_le_div_mul_of_div_le_div (h : a / b <= c / d) (he : 0 <= e) :
    a / (b * e) <= c / (d * e) := by
  rw [div_mul_eq_div_mul_one_div]; rw [div_mul_eq_div_mul_one_div]
  gcongr
  exact one_div_nonneg.2 he

omit [IsStrictOrderedRing α] in
/--
theorem `mul_le_mul_of_mul_div_le` / 定理 `mul_le_mul_of_mul_div_le`

English:
theorem mul_le_mul_of_mul_div_le
  given: (h : a * (b / c) <= d) (hc : 0 < c)
  statement: b * a <= d * c
  proof: by
  rw [← mul_div_assoc] at h
  rwa [mul_comm b, ← div_le_iff₀ hc]

omit [IsStrictOrderedRing α] in

中文:
定理 mul_le_mul_of_mul_div_le
  条件: (h : a * (b / c) <= d) (hc : 0 < c)
  结论: b * a <= d * c
  证明: by
  rw [← mul_div_assoc] at h
  rwa [mul_comm b, ← div_le_iff₀ hc]

omit [IsStrictOrderedRing α] in

Depends on / 依赖: mul_comm, mul_div_assoc
-/
theorem mul_le_mul_of_mul_div_le (h : a * (b / c) <= d) (hc : 0 < c) : b * a <= d * c := by
  rw [← mul_div_assoc] at h
  rwa [mul_comm b, ← div_le_iff₀ hc]

omit [IsStrictOrderedRing α] in
/--
lemma `monotone_div_right_of_nonneg` / 引理 `monotone_div_right_of_nonneg`

English:
lemma monotone_div_right_of_nonneg
  given: (ha : 0 <= a)
  statement: Monotone (· / a)
  proof: fun _b _c hbc => div_le_div_of_nonneg_right hbc ha

omit [IsStrictOrderedRing α] in

中文:
引理 monotone_div_right_of_nonneg
  条件: (ha : 0 <= a)
  结论: 递增 (· / a)
  证明: fun _b _c hbc => div_le_div_of_nonneg_right hbc ha

omit [IsStrictOrderedRing α] in

Depends on / 依赖: div_le_div_of_nonneg_right
-/
lemma monotone_div_right_of_nonneg (ha : 0 <= a) : Monotone (· / a) :=
  fun _b _c hbc => div_le_div_of_nonneg_right hbc ha

omit [IsStrictOrderedRing α] in
/--
lemma `strictMono_div_right_of_pos` / 引理 `strictMono_div_right_of_pos`

English:
lemma strictMono_div_right_of_pos
  given: (ha : 0 < a)
  statement: StrictMono (· / a)
  proof: fun _b _c hbc => div_lt_div_of_pos_right hbc ha

omit [IsStrictOrderedRing α] in

中文:
引理 strictMono_div_right_of_pos
  条件: (ha : 0 < a)
  结论: 严格递增 (· / a)
  证明: fun _b _c hbc => div_lt_div_of_pos_right hbc ha

omit [IsStrictOrderedRing α] in

Depends on / 依赖: div_lt_div_of_pos_right
-/
lemma strictMono_div_right_of_pos (ha : 0 < a) : StrictMono (· / a) :=
  fun _b _c hbc => div_lt_div_of_pos_right hbc ha

omit [IsStrictOrderedRing α] in
/--
theorem `Monotone.div_const` / 定理 `Monotone.div_const`

English:
theorem Monotone.div_const
  statement: {β : Type*} [Preorder β] {f : β -> α} (hf : Monotone f) {c : α}
  proof: (monotone_div_right_of_nonneg hc).comp hf

中文:
定理 递增.div_const
  结论: {β : 类型} [预序 β] {f : β -> α} (hf : 递增 f) {c : α}
  证明: (monotone_div_right_of_nonneg hc).comp hf

Depends on / 依赖: monotone_div_right_of_nonneg
-/
theorem Monotone.div_const {β : Type*} [Preorder β] {f : β -> α} (hf : Monotone f) {c : α}
    (hc : 0 <= c) : Monotone fun x => f x / c := (monotone_div_right_of_nonneg hc).comp hf

/--
theorem `StrictMono.div_const` / 定理 `StrictMono.div_const`

English:
theorem StrictMono.div_const
  statement: {β : Type*} [Preorder β] {f : β -> α} (hf : StrictMono f) {c : α}
  proof: by
  simpa only [div_eq_mul_inv] using hf.mul_const (inv_pos.2 hc)

中文:
定理 严格递增.div_const
  结论: {β : 类型} [预序 β] {f : β -> α} (hf : 严格递增 f) {c : α}
  证明: by
  simpa only [div_eq_mul_inv] using hf.mul_const (inv_pos.2 hc)

Depends on / 依赖: div_eq_mul_inv, hf.mul_const, inv_pos, mul_const
-/
theorem StrictMono.div_const {β : Type*} [Preorder β] {f : β -> α} (hf : StrictMono f) {c : α}
    (hc : 0 < c) : StrictMono fun x => f x / c := by
  simpa only [div_eq_mul_inv] using hf.mul_const (inv_pos.2 hc)

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedSemiField.toDenselyOrdered : DenselyOrdered α where
  dense a₁ a₂ h :=
    ⟨(a₁ + a₂) / 2,
      calc
        a₁ = (a₁ + a₁) / 2 := (add_self_div_two a₁).symm
        _ < (a₁ + a₂) / 2 := by gcongr; exact zero_lt_two,
      calc
        (a₁ + a₂) / 2 < (a₂ + a₂) / 2 := by gcongr; exact zero_lt_two
        _ = a₂ := add_self_div_two a₂
        ⟩

/--
theorem `one_div_strictAntiOn` / 定理 `one_div_strictAntiOn`

English:
theorem one_div_strictAntiOn
  statement: StrictAntiOn (fun x : α => 1 / x) (Set.Ioi 0)
  proof: fun _ x1 _ y1 xy => (one_div_lt_one_div (Set.mem_Ioi.mp y1) (Set.mem_Ioi.mp x1)).mpr xy

中文:
定理 one_div_strictAntiOn
  结论: StrictAntiOn (fun x : α => 1 / x) (集合.左开右无界区间 0)
  证明: fun _ x1 _ y1 xy => (one_div_lt_one_div (Set.mem_Ioi.mp y1) (Set.mem_Ioi.mp x1)).mpr xy

Depends on / 依赖: Set.mem_Ioi.mp, mem_Ioi, one_div_lt_one_div
-/
theorem one_div_strictAntiOn : StrictAntiOn (fun x : α => 1 / x) (Set.Ioi 0) :=
  fun _ x1 _ y1 xy => (one_div_lt_one_div (Set.mem_Ioi.mp y1) (Set.mem_Ioi.mp x1)).mpr xy

/--
theorem `one_div_pow_le_one_div_pow_of_le` / 定理 `one_div_pow_le_one_div_pow_of_le`

English:
theorem one_div_pow_le_one_div_pow_of_le
  given: (a1 : 1 <= a) {m n : Nat} (mn : m <= n)
  proof: by
  refine (one_div_le_one_div ?_ ?_).mpr (pow_right_mono₀ a1 mn) <;>
    exact pow_pos (zero_lt_one.trans_le a1) _

中文:
定理 one_div_pow_le_one_div_pow_of_le
  条件: (a1 : 1 <= a) {m n : 自然数} (mn : m <= n)
  证明: by
  refine (one_div_le_one_div ?_ ?_).mpr (pow_right_mono₀ a1 mn) <;>
    exact pow_pos (zero_lt_one.trans_le a1) _

Depends on / 依赖: one_div_le_one_div, pow_pos, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem one_div_pow_le_one_div_pow_of_le (a1 : 1 <= a) {m n : Nat} (mn : m <= n) :
    1 / a ^ n <= 1 / a ^ m := by
  refine (one_div_le_one_div ?_ ?_).mpr (pow_right_mono₀ a1 mn) <;>
    exact pow_pos (zero_lt_one.trans_le a1) _

/--
theorem `one_div_pow_lt_one_div_pow_of_lt` / 定理 `one_div_pow_lt_one_div_pow_of_lt`

English:
theorem one_div_pow_lt_one_div_pow_of_lt
  given: (a1 : 1 < a) {m n : Nat} (mn : m < n)
  proof: by
  refine (one_div_lt_one_div ?_ ?_).2 (pow_lt_pow_right₀ a1 mn) <;>
    exact pow_pos (zero_lt_one.trans a1) _

中文:
定理 one_div_pow_lt_one_div_pow_of_lt
  条件: (a1 : 1 < a) {m n : 自然数} (mn : m < n)
  证明: by
  refine (one_div_lt_one_div ?_ ?_).2 (pow_lt_pow_right₀ a1 mn) <;>
    exact pow_pos (zero_lt_one.trans a1) _

Depends on / 依赖: one_div_lt_one_div, pow_pos, zero_lt_one, zero_lt_one.trans
-/
theorem one_div_pow_lt_one_div_pow_of_lt (a1 : 1 < a) {m n : Nat} (mn : m < n) :
    1 / a ^ n < 1 / a ^ m := by
  refine (one_div_lt_one_div ?_ ?_).2 (pow_lt_pow_right₀ a1 mn) <;>
    exact pow_pos (zero_lt_one.trans a1) _

/--
theorem `one_div_pow_anti` / 定理 `one_div_pow_anti`

English:
theorem one_div_pow_anti
  given: (a1 : 1 <= a)
  statement: Antitone fun n : Nat => 1 / a ^ n
  proof: fun _ _ =>
  one_div_pow_le_one_div_pow_of_le a1

中文:
定理 one_div_pow_anti
  条件: (a1 : 1 <= a)
  结论: 递减 fun n : 自然数 => 1 / a ^ n
  证明: fun _ _ =>
  one_div_pow_le_one_div_pow_of_le a1
-/
theorem one_div_pow_anti (a1 : 1 <= a) : Antitone fun n : Nat => 1 / a ^ n := fun _ _ =>
  one_div_pow_le_one_div_pow_of_le a1

/--
theorem `one_div_pow_strictAnti` / 定理 `one_div_pow_strictAnti`

English:
theorem one_div_pow_strictAnti
  given: (a1 : 1 < a)
  statement: StrictAnti fun n : Nat => 1 / a ^ n
  proof: fun _ _ =>
  one_div_pow_lt_one_div_pow_of_lt a1

omit [IsStrictOrderedRing α] in

中文:
定理 one_div_pow_strictAnti
  条件: (a1 : 1 < a)
  结论: 严格递减 fun n : 自然数 => 1 / a ^ n
  证明: fun _ _ =>
  one_div_pow_lt_one_div_pow_of_lt a1

omit [IsStrictOrderedRing α] in
-/
theorem one_div_pow_strictAnti (a1 : 1 < a) : StrictAnti fun n : Nat => 1 / a ^ n := fun _ _ =>
  one_div_pow_lt_one_div_pow_of_lt a1

omit [IsStrictOrderedRing α] in
/--
theorem `inv_strictAntiOn` / 定理 `inv_strictAntiOn`

English:
theorem inv_strictAntiOn
  statement: StrictAntiOn (fun x : α => x⁻¹) (Set.Ioi 0)
  proof: fun _ hx _ hy xy =>
  (inv_lt_inv₀ hy hx).2 xy

中文:
定理 inv_strictAntiOn
  结论: StrictAntiOn (fun x : α => x⁻¹) (集合.左开右无界区间 0)
  证明: fun _ hx _ hy xy =>
  (inv_lt_inv₀ hy hx).2 xy
-/
theorem inv_strictAntiOn : StrictAntiOn (fun x : α => x⁻¹) (Set.Ioi 0) := fun _ hx _ hy xy =>
  (inv_lt_inv₀ hy hx).2 xy

/--
theorem `inv_pow_le_inv_pow_of_le` / 定理 `inv_pow_le_inv_pow_of_le`

English:
theorem inv_pow_le_inv_pow_of_le
  given: (a1 : 1 <= a) {m n : Nat} (mn : m <= n)
  statement: (a ^ n)⁻¹ <= (a ^ m)⁻¹
  proof: by
  convert one_div_pow_le_one_div_pow_of_le a1 mn <;> simp

中文:
定理 inv_pow_le_inv_pow_of_le
  条件: (a1 : 1 <= a) {m n : 自然数} (mn : m <= n)
  结论: (a ^ n)⁻¹ <= (a ^ m)⁻¹
  证明: by
  convert one_div_pow_le_one_div_pow_of_le a1 mn <;> simp

Depends on / 依赖: convert, one_div_pow_le_one_div_pow_of_le
-/
theorem inv_pow_le_inv_pow_of_le (a1 : 1 <= a) {m n : Nat} (mn : m <= n) : (a ^ n)⁻¹ <= (a ^ m)⁻¹ := by
  convert one_div_pow_le_one_div_pow_of_le a1 mn <;> simp

/--
theorem `inv_pow_lt_inv_pow_of_lt` / 定理 `inv_pow_lt_inv_pow_of_lt`

English:
theorem inv_pow_lt_inv_pow_of_lt
  given: (a1 : 1 < a) {m n : Nat} (mn : m < n)
  statement: (a ^ n)⁻¹ < (a ^ m)⁻¹
  proof: by
  convert one_div_pow_lt_one_div_pow_of_lt a1 mn <;> simp

中文:
定理 inv_pow_lt_inv_pow_of_lt
  条件: (a1 : 1 < a) {m n : 自然数} (mn : m < n)
  结论: (a ^ n)⁻¹ < (a ^ m)⁻¹
  证明: by
  convert one_div_pow_lt_one_div_pow_of_lt a1 mn <;> simp

Depends on / 依赖: convert, one_div_pow_lt_one_div_pow_of_lt
-/
theorem inv_pow_lt_inv_pow_of_lt (a1 : 1 < a) {m n : Nat} (mn : m < n) : (a ^ n)⁻¹ < (a ^ m)⁻¹ := by
  convert one_div_pow_lt_one_div_pow_of_lt a1 mn <;> simp

/--
theorem `inv_pow_anti` / 定理 `inv_pow_anti`

English:
theorem inv_pow_anti
  given: (a1 : 1 <= a)
  statement: Antitone fun n : Nat => (a ^ n)⁻¹
  proof: fun _ _ =>
  inv_pow_le_inv_pow_of_le a1

中文:
定理 inv_pow_anti
  条件: (a1 : 1 <= a)
  结论: 递减 fun n : 自然数 => (a ^ n)⁻¹
  证明: fun _ _ =>
  inv_pow_le_inv_pow_of_le a1
-/
theorem inv_pow_anti (a1 : 1 <= a) : Antitone fun n : Nat => (a ^ n)⁻¹ := fun _ _ =>
  inv_pow_le_inv_pow_of_le a1

/--
theorem `inv_pow_strictAnti` / 定理 `inv_pow_strictAnti`

English:
theorem inv_pow_strictAnti
  given: (a1 : 1 < a)
  statement: StrictAnti fun n : Nat => (a ^ n)⁻¹
  proof: fun _ _ =>
  inv_pow_lt_inv_pow_of_lt a1

中文:
定理 inv_pow_strictAnti
  条件: (a1 : 1 < a)
  结论: 严格递减 fun n : 自然数 => (a ^ n)⁻¹
  证明: fun _ _ =>
  inv_pow_lt_inv_pow_of_lt a1
-/
theorem inv_pow_strictAnti (a1 : 1 < a) : StrictAnti fun n : Nat => (a ^ n)⁻¹ := fun _ _ =>
  inv_pow_lt_inv_pow_of_lt a1

/--
theorem `le_iff_forall_one_lt_le_mul₀` / 定理 `le_iff_forall_one_lt_le_mul₀`

English:
theorem le_iff_forall_one_lt_le_mul₀
  statement: {α : Type*}
  proof: by
refine ⟨fun h _ hε => h.trans le_mul_of_one_le_right hb hε.le, fun h => ?_⟩
  obtain rfl | hb := hb.eq_or_lt
  · simp_rw [zero_mul] at h
    exact h 2 one_lt_two
  refine le_of_forall_gt_imp_ge_of_dense fun x hbx => ?_
  convert h (x / b) ((one_lt_div hb).mpr hbx)
  rw [mul_div_cancel₀ _ hb.ne']

中文:
定理 le_iff_对任意_one_lt_le_mul₀
  结论: {α : 类型}
  证明: by
refine ⟨fun h _ hε => h.trans le_mul_of_one_le_right hb hε.le, fun h => ?_⟩
  obtain rfl | hb := hb.eq_or_lt
  · simp_rw [zero_mul] at h
    exact h 2 one_lt_two
  refine le_of_forall_gt_imp_ge_of_dense fun x hbx => ?_
  convert h (x / b) ((one_lt_div hb).mpr hbx)
  rw [mul_div_cancel₀ _ hb.ne']

Depends on / 依赖: convert, eq_or_lt, h.trans, hb.eq_or_lt, hb.ne, le_mul_of_one_le_right, le_of_forall_gt_imp_ge_of_dense, one_lt_div, one_lt_two, simp_rw, zero_mul
-/
theorem le_iff_forall_one_lt_le_mul₀ {α : Type*}
    [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} (hb : 0 <= b) : a <= b ↔ forall ε, 1 < ε -> a <= b * ε := by
refine ⟨fun h _ hε => h.trans le_mul_of_one_le_right hb hε.le, fun h => ?_⟩
  obtain rfl | hb := hb.eq_or_lt
  · simp_rw [zero_mul] at h
    exact h 2 one_lt_two
  refine le_of_forall_gt_imp_ge_of_dense fun x hbx => ?_
  convert h (x / b) ((one_lt_div hb).mpr hbx)
  rw [mul_div_cancel₀ _ hb.ne']

/--
theorem `div_nat_le_self_of_nonnneg` / 定理 `div_nat_le_self_of_nonnneg`

English:
theorem div_nat_le_self_of_nonnneg
  given: (ha : 0 <= a) (n : Nat)
  statement: a / n <= a
  proof: if h : n = 0 then by simpa [h]
  else div_le_self ha (n.one_le_cast_iff_ne_zero.mpr h)

中文:
定理 div_nat_le_self_of_nonnneg
  条件: (ha : 0 <= a) (n : 自然数)
  结论: a / n <= a
  证明: if h : n = 0 then by simpa [h]
  else div_le_self ha (n.one_le_cast_iff_ne_zero.mpr h)

Depends on / 依赖: div_le_self, n.one_le_cast_iff_ne_zero.mpr, one_le_cast_iff_ne_zero
-/
theorem div_nat_le_self_of_nonnneg (ha : 0 <= a) (n : Nat) : a / n <= a :=
  if h : n = 0 then by simpa [h]
  else div_le_self ha (n.one_le_cast_iff_ne_zero.mpr h)

/--
theorem `div_nat_lt_self_of_pos_of_two_le` / 定理 `div_nat_lt_self_of_pos_of_two_le`

English:
theorem div_nat_lt_self_of_pos_of_two_le
  given: (ha : 0 < a) {n : Nat} (hn : 2 <= n)
  statement: a / n < a
  proof: div_lt_self ha (n.one_lt_cast.mpr hn)

中文:
定理 div_nat_lt_self_of_pos_of_two_le
  条件: (ha : 0 < a) {n : 自然数} (hn : 2 <= n)
  结论: a / n < a
  证明: div_lt_self ha (n.one_lt_cast.mpr hn)

Depends on / 依赖: div_lt_self, n.one_lt_cast.mpr, one_lt_cast
-/
theorem div_nat_lt_self_of_pos_of_two_le (ha : 0 < a) {n : Nat} (hn : 2 <= n) : a / n < a :=
  div_lt_self ha (n.one_lt_cast.mpr hn)



/--
theorem `IsGLB.mul_left` / 定理 `IsGLB.mul_left`

English:
theorem IsGLB.mul_left
  given: {s : Set α} (ha : 0 <= a) (hs : IsGLB s b)
  proof: by
  rcases lt_or_eq_of_le ha with (ha | rfl)
  · exact (OrderIso.mulLeft₀ _ ha).isGLB_image'.2 hs
  · simp_rw [zero_mul]
    rw [hs.nonempty.image_const]
    exact isGLB_singleton

中文:
定理 IsGLB.mul_left
  条件: {s : 集合 α} (ha : 0 <= a) (hs : IsGLB s b)
  证明: by
  rcases lt_or_eq_of_le ha with (ha | rfl)
  · exact (OrderIso.mulLeft₀ _ ha).isGLB_image'.2 hs
  · simp_rw [zero_mul]
    rw [hs.nonempty.image_const]
    exact isGLB_singleton

Depends on / 依赖: OrderIso, OrderIso.mulLeft, hs.nonempty.image_const, image_const, isGLB_image, isGLB_singleton, lt_or_eq_of_le, nonempty, simp_rw, zero_mul
-/
theorem IsGLB.mul_left {s : Set α} (ha : 0 <= a) (hs : IsGLB s b) :
    IsGLB ((fun b => a * b) '' s) (a * b) := by
  rcases lt_or_eq_of_le ha with (ha | rfl)
  · exact (OrderIso.mulLeft₀ _ ha).isGLB_image'.2 hs
  · simp_rw [zero_mul]
    rw [hs.nonempty.image_const]
    exact isGLB_singleton

/--
theorem `IsGLB.mul_right` / 定理 `IsGLB.mul_right`

English:
theorem IsGLB.mul_right
  given: {s : Set α} (ha : 0 <= a) (hs : IsGLB s b)
  proof: by simpa [mul_comm] using hs.mul_left ha

中文:
定理 IsGLB.mul_right
  条件: {s : 集合 α} (ha : 0 <= a) (hs : IsGLB s b)
  证明: by simpa [mul_comm] using hs.mul_left ha

Depends on / 依赖: hs.mul_left, mul_comm, mul_left
-/
theorem IsGLB.mul_right {s : Set α} (ha : 0 <= a) (hs : IsGLB s b) :
    IsGLB ((fun b => b * a) '' s) (b * a) := by simpa [mul_comm] using hs.mul_left ha



/--
theorem `IsLUB.mul_left` / 定理 `IsLUB.mul_left`

English:
theorem IsLUB.mul_left
  given: {s : Set α} (ha : 0 <= a) (hs : IsLUB s b)
  proof: by
  obtain ha | rfl := ha.lt_or_eq
  · exact (OrderIso.mulLeft₀ _ ha).isLUB_image'.2 hs
  · simp_rw [zero_mul]
    obtain rfl | ne := s.eq_empty_or_nonempty
    · simp only [Set.image_empty, isLUB_empty_iff] at hs ⊢
      have hb := hs (b + b)
      rw [le_add_iff_nonneg_right] at hb
      exact hs.mono hb
    rw [ne.image_const]
    exact isLUB_singleton

中文:
定理 IsLUB.mul_left
  条件: {s : 集合 α} (ha : 0 <= a) (hs : IsLUB s b)
  证明: by
  obtain ha | rfl := ha.lt_or_eq
  · exact (OrderIso.mulLeft₀ _ ha).isLUB_image'.2 hs
  · simp_rw [zero_mul]
    obtain rfl | ne := s.eq_empty_or_nonempty
    · simp only [Set.image_empty, isLUB_empty_iff] at hs ⊢
      have hb := hs (b + b)
      rw [le_add_iff_nonneg_right] at hb
      exact hs.mono hb
    rw [ne.image_const]
    exact isLUB_singleton

Depends on / 依赖: OrderIso, OrderIso.mulLeft, Set.image_empty, eq_empty_or_nonempty, ha.lt_or_eq, hs.mono, image_const, image_empty, isLUB_empty_iff, isLUB_image, isLUB_singleton, le_add_iff_nonneg_right, lt_or_eq, ne.image_const, s.eq_empty_or_nonempty, simp_rw, zero_mul
-/
theorem IsLUB.mul_left {s : Set α} (ha : 0 <= a) (hs : IsLUB s b) :
    IsLUB ((fun b => a * b) '' s) (a * b) := by
  obtain ha | rfl := ha.lt_or_eq
  · exact (OrderIso.mulLeft₀ _ ha).isLUB_image'.2 hs
  · simp_rw [zero_mul]
    obtain rfl | ne := s.eq_empty_or_nonempty
    · simp only [Set.image_empty, isLUB_empty_iff] at hs ⊢
      have hb := hs (b + b)
      rw [le_add_iff_nonneg_right] at hb
      exact hs.mono hb
    rw [ne.image_const]
    exact isLUB_singleton

/--
theorem `IsLUB.mul_right` / 定理 `IsLUB.mul_right`

English:
theorem IsLUB.mul_right
  given: {s : Set α} (ha : 0 <= a) (hs : IsLUB s b)
  proof: by simpa [mul_comm] using hs.mul_left ha

中文:
定理 IsLUB.mul_right
  条件: {s : 集合 α} (ha : 0 <= a) (hs : IsLUB s b)
  证明: by simpa [mul_comm] using hs.mul_left ha

Depends on / 依赖: hs.mul_left, mul_comm, mul_left
-/
theorem IsLUB.mul_right {s : Set α} (ha : 0 <= a) (hs : IsLUB s b) :
    IsLUB ((fun b => b * a) '' s) (b * a) := by simpa [mul_comm] using hs.mul_left ha

end PartialOrderedSemifield

section LinearOrderedSemifield

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d e : α}

/--
theorem `exists_pos_mul_lt` / 定理 `exists_pos_mul_lt`

English:
theorem exists_pos_mul_lt
  given: {a : α} (h : 0 < a) (b : α)
  statement: exists c : α, 0 < c ∧ b * c < a
  proof: by
  have : 0 < a / max (b + 1) 1 := div_pos h (lt_max_iff.2 (Or.inr zero_lt_one))
  refine ⟨a / max (b + 1) 1, this, ?_⟩
  rw [← lt_div_iff₀ this]; rw [div_div_cancel₀ h.ne']
  exact lt_max_iff.2 (Or.inl <| lt_add_one _)

中文:
定理 存在_pos_mul_lt
  条件: {a : α} (h : 0 < a) (b : α)
  结论: 存在 c : α, 0 < c ∧ b * c < a
  证明: by
  have : 0 < a / max (b + 1) 1 := div_pos h (lt_max_iff.2 (Or.inr zero_lt_one))
  refine ⟨a / max (b + 1) 1, this, ?_⟩
  rw [← lt_div_iff₀ this]; rw [div_div_cancel₀ h.ne']
  exact lt_max_iff.2 (Or.inl <| lt_add_one _)

Depends on / 依赖: Or.inl, Or.inr, div_pos, h.ne, lt_add_one, lt_max_iff, zero_lt_one
-/
theorem exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : exists c : α, 0 < c ∧ b * c < a := by
  have : 0 < a / max (b + 1) 1 := div_pos h (lt_max_iff.2 (Or.inr zero_lt_one))
  refine ⟨a / max (b + 1) 1, this, ?_⟩
  rw [← lt_div_iff₀ this]; rw [div_div_cancel₀ h.ne']
  exact lt_max_iff.2 (Or.inl <| lt_add_one _)

/--
theorem `exists_pos_lt_mul` / 定理 `exists_pos_lt_mul`

English:
theorem exists_pos_lt_mul
  given: {a : α} (h : 0 < a) (b : α)
  statement: exists c : α, 0 < c ∧ b < c * a
  proof: let ⟨c, hc₀, hc⟩ := exists_pos_mul_lt h b;
  ⟨c⁻¹, inv_pos.2 hc₀, by rwa [← div_eq_inv_mul, lt_div_iff₀ hc₀]⟩

中文:
定理 存在_pos_lt_mul
  条件: {a : α} (h : 0 < a) (b : α)
  结论: 存在 c : α, 0 < c ∧ b < c * a
  证明: let ⟨c, hc₀, hc⟩ := exists_pos_mul_lt h b;
  ⟨c⁻¹, inv_pos.2 hc₀, by rwa [← div_eq_inv_mul, lt_div_iff₀ hc₀]⟩

Depends on / 依赖: div_eq_inv_mul, exists_pos_mul_lt, inv_pos
-/
theorem exists_pos_lt_mul {a : α} (h : 0 < a) (b : α) : exists c : α, 0 < c ∧ b < c * a :=
  let ⟨c, hc₀, hc⟩ := exists_pos_mul_lt h b;
  ⟨c⁻¹, inv_pos.2 hc₀, by rwa [← div_eq_inv_mul, lt_div_iff₀ hc₀]⟩

/--
theorem `min_div_div_right` / 定理 `min_div_div_right`

English:
theorem min_div_div_right
  given: {c : α} (hc : 0 <= c) (a b : α)
  statement: min (a / c) (b / c) = min a b / c
  proof: (monotone_div_right_of_nonneg hc).map_min.symm

中文:
定理 min_div_div_right
  条件: {c : α} (hc : 0 <= c) (a b : α)
  结论: 最小值 (a / c) (b / c) = 最小值 a b / c
  证明: (monotone_div_right_of_nonneg hc).map_min.symm

Depends on / 依赖: map_min, map_min.symm, monotone_div_right_of_nonneg
-/
theorem min_div_div_right {c : α} (hc : 0 <= c) (a b : α) : min (a / c) (b / c) = min a b / c :=
  (monotone_div_right_of_nonneg hc).map_min.symm

/--
theorem `max_div_div_right` / 定理 `max_div_div_right`

English:
theorem max_div_div_right
  given: {c : α} (hc : 0 <= c) (a b : α)
  statement: max (a / c) (b / c) = max a b / c
  proof: (monotone_div_right_of_nonneg hc).map_max.symm

中文:
定理 max_div_div_right
  条件: {c : α} (hc : 0 <= c) (a b : α)
  结论: 最大值 (a / c) (b / c) = 最大值 a b / c
  证明: (monotone_div_right_of_nonneg hc).map_max.symm

Depends on / 依赖: map_max, map_max.symm, monotone_div_right_of_nonneg
-/
theorem max_div_div_right {c : α} (hc : 0 <= c) (a b : α) : max (a / c) (b / c) = max a b / c :=
  (monotone_div_right_of_nonneg hc).map_max.symm

end LinearOrderedSemifield

section PartialOrderedField

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : Int}

attribute [local instance] PosMulReflectLT.toMulPosReflectLT

/-! ### Lemmas about pos, nonneg, nonpos, neg -/

/--
theorem `inv_lt_zero'` / 定理 `inv_lt_zero'`

English:
theorem inv_lt_zero'
  statement: a⁻¹ < 0 ↔ a < 0
  proof: by
  rw [← neg_pos]; rw [← inv_neg]; rw [inv_pos]; rw [neg_pos]

中文:
定理 inv_lt_zero'
  结论: a⁻¹ < 0 ↔ a < 0
  证明: by
  rw [← neg_pos]; rw [← inv_neg]; rw [inv_pos]; rw [neg_pos]

Depends on / 依赖: inv_neg, inv_pos, neg_pos
-/
theorem inv_lt_zero' : a⁻¹ < 0 ↔ a < 0 := by
  rw [← neg_pos]; rw [← inv_neg]; rw [inv_pos]; rw [neg_pos]

/--
theorem `inv_nonpos'` / 定理 `inv_nonpos'`

English:
theorem inv_nonpos'
  statement: a⁻¹ <= 0 ↔ a <= 0
  proof: by
  grind [inv_lt_zero', le_iff_eq_or_lt]

中文:
定理 inv_nonpos'
  结论: a⁻¹ <= 0 ↔ a <= 0
  证明: by
  grind [inv_lt_zero', le_iff_eq_or_lt]

Depends on / 依赖: inv_lt_zero, le_iff_eq_or_lt
-/
theorem inv_nonpos' : a⁻¹ <= 0 ↔ a <= 0 := by
  grind [inv_lt_zero', le_iff_eq_or_lt]

/--
theorem `div_nonneg_of_nonpos` / 定理 `div_nonneg_of_nonpos`

English:
theorem div_nonneg_of_nonpos
  given: (ha : a <= 0) (hb : b <= 0)
  statement: 0 <= a / b
  proof: div_eq_mul_inv a b ▸ mul_nonneg_of_nonpos_of_nonpos ha (inv_nonpos'.2 hb)

中文:
定理 div_nonneg_of_nonpos
  条件: (ha : a <= 0) (hb : b <= 0)
  结论: 0 <= a / b
  证明: div_eq_mul_inv a b ▸ mul_nonneg_of_nonpos_of_nonpos ha (inv_nonpos'.2 hb)

Depends on / 依赖: div_eq_mul_inv, inv_nonpos, mul_nonneg_of_nonpos_of_nonpos
-/
theorem div_nonneg_of_nonpos (ha : a <= 0) (hb : b <= 0) : 0 <= a / b :=
  div_eq_mul_inv a b ▸ mul_nonneg_of_nonpos_of_nonpos ha (inv_nonpos'.2 hb)

/--
theorem `div_pos_of_neg_of_neg` / 定理 `div_pos_of_neg_of_neg`

English:
theorem div_pos_of_neg_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: 0 < a / b
  proof: div_eq_mul_inv a b ▸ mul_pos_of_neg_of_neg ha (inv_lt_zero'.2 hb)

中文:
定理 div_pos_of_neg_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: 0 < a / b
  证明: div_eq_mul_inv a b ▸ mul_pos_of_neg_of_neg ha (inv_lt_zero'.2 hb)

Depends on / 依赖: div_eq_mul_inv, inv_lt_zero, mul_pos_of_neg_of_neg
-/
theorem div_pos_of_neg_of_neg (ha : a < 0) (hb : b < 0) : 0 < a / b :=
  div_eq_mul_inv a b ▸ mul_pos_of_neg_of_neg ha (inv_lt_zero'.2 hb)

/--
theorem `div_neg_of_neg_of_pos` / 定理 `div_neg_of_neg_of_pos`

English:
theorem div_neg_of_neg_of_pos
  given: (ha : a < 0) (hb : 0 < b)
  statement: a / b < 0
  proof: div_eq_mul_inv a b ▸ mul_neg_of_neg_of_pos ha (inv_pos.2 hb)

中文:
定理 div_neg_of_neg_of_pos
  条件: (ha : a < 0) (hb : 0 < b)
  结论: a / b < 0
  证明: div_eq_mul_inv a b ▸ mul_neg_of_neg_of_pos ha (inv_pos.2 hb)

Depends on / 依赖: div_eq_mul_inv, inv_pos, mul_neg_of_neg_of_pos
-/
theorem div_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a / b < 0 :=
  div_eq_mul_inv a b ▸ mul_neg_of_neg_of_pos ha (inv_pos.2 hb)

/--
theorem `div_neg_of_pos_of_neg` / 定理 `div_neg_of_pos_of_neg`

English:
theorem div_neg_of_pos_of_neg
  given: (ha : 0 < a) (hb : b < 0)
  statement: a / b < 0
  proof: div_eq_mul_inv a b ▸ mul_neg_of_pos_of_neg ha (inv_lt_zero'.2 hb)

中文:
定理 div_neg_of_pos_of_neg
  条件: (ha : 0 < a) (hb : b < 0)
  结论: a / b < 0
  证明: div_eq_mul_inv a b ▸ mul_neg_of_pos_of_neg ha (inv_lt_zero'.2 hb)

Depends on / 依赖: div_eq_mul_inv, inv_lt_zero, mul_neg_of_pos_of_neg
-/
theorem div_neg_of_pos_of_neg (ha : 0 < a) (hb : b < 0) : a / b < 0 :=
  div_eq_mul_inv a b ▸ mul_neg_of_pos_of_neg ha (inv_lt_zero'.2 hb)


/--
theorem `div_le_iff_of_neg` / 定理 `div_le_iff_of_neg`

English:
theorem div_le_iff_of_neg
  given: (hc : c < 0)
  statement: b / c <= a ↔ a * c <= b where
  proof: div_mul_cancel₀ b (ne_of_lt hc) ▸ mul_le_mul_of_nonpos_right h hc.le
  mpr h := calc
    a = a * c * (1 / c) := mul_mul_div a (ne_of_lt hc)
_ >= b * (1 / c) := mul_le_mul_of_nonpos_right h inv_eq_one_div c ▸ (inv_lt_zero'.2 hc).le
    _ = b / c := (div_eq_mul_one_div b c).symm

中文:
定理 div_le_iff_of_neg
  条件: (hc : c < 0)
  结论: b / c <= a ↔ a * c <= b where
  证明: div_mul_cancel₀ b (ne_of_lt hc) ▸ mul_le_mul_of_nonpos_right h hc.le
  mpr h := calc
    a = a * c * (1 / c) := mul_mul_div a (ne_of_lt hc)
_ >= b * (1 / c) := mul_le_mul_of_nonpos_right h inv_eq_one_div c ▸ (inv_lt_zero'.2 hc).le
    _ = b / c := (div_eq_mul_one_div b c).symm

Depends on / 依赖: hc.le, mul_le_mul_of_nonpos_right, ne_of_lt
-/
theorem div_le_iff_of_neg (hc : c < 0) : b / c <= a ↔ a * c <= b where
  mp h := div_mul_cancel₀ b (ne_of_lt hc) ▸ mul_le_mul_of_nonpos_right h hc.le
  mpr h := calc
    a = a * c * (1 / c) := mul_mul_div a (ne_of_lt hc)
_ >= b * (1 / c) := mul_le_mul_of_nonpos_right h inv_eq_one_div c ▸ (inv_lt_zero'.2 hc).le
    _ = b / c := (div_eq_mul_one_div b c).symm

/--
theorem `div_le_iff_of_neg'` / 定理 `div_le_iff_of_neg'`

English:
theorem div_le_iff_of_neg'
  given: (hc : c < 0)
  statement: b / c <= a ↔ c * a <= b
  proof: by
  rw [mul_comm]; rw [div_le_iff_of_neg hc]

中文:
定理 div_le_iff_of_neg'
  条件: (hc : c < 0)
  结论: b / c <= a ↔ c * a <= b
  证明: by
  rw [mul_comm]; rw [div_le_iff_of_neg hc]

Depends on / 依赖: div_le_iff_of_neg, mul_comm
-/
theorem div_le_iff_of_neg' (hc : c < 0) : b / c <= a ↔ c * a <= b := by
  rw [mul_comm]; rw [div_le_iff_of_neg hc]

/--
theorem `le_div_iff_of_neg` / 定理 `le_div_iff_of_neg`

English:
theorem le_div_iff_of_neg
  given: (hc : c < 0)
  statement: a <= b / c ↔ b <= a * c
  proof: by
  rw [← neg_neg c]; rw [mul_neg]; rw [div_neg]; rw [le_neg]; rw [div_le_iff₀ (neg_pos.2 hc)]; rw [neg_mul]

中文:
定理 le_div_iff_of_neg
  条件: (hc : c < 0)
  结论: a <= b / c ↔ b <= a * c
  证明: by
  rw [← neg_neg c]; rw [mul_neg]; rw [div_neg]; rw [le_neg]; rw [div_le_iff₀ (neg_pos.2 hc)]; rw [neg_mul]

Depends on / 依赖: div_neg, le_neg, mul_neg, neg_mul, neg_neg, neg_pos
-/
theorem le_div_iff_of_neg (hc : c < 0) : a <= b / c ↔ b <= a * c := by
  rw [← neg_neg c]; rw [mul_neg]; rw [div_neg]; rw [le_neg]; rw [div_le_iff₀ (neg_pos.2 hc)]; rw [neg_mul]

/--
theorem `le_div_iff_of_neg'` / 定理 `le_div_iff_of_neg'`

English:
theorem le_div_iff_of_neg'
  given: (hc : c < 0)
  statement: a <= b / c ↔ b <= c * a
  proof: by
  rw [mul_comm]; rw [le_div_iff_of_neg hc]

中文:
定理 le_div_iff_of_neg'
  条件: (hc : c < 0)
  结论: a <= b / c ↔ b <= c * a
  证明: by
  rw [mul_comm]; rw [le_div_iff_of_neg hc]

Depends on / 依赖: le_div_iff_of_neg, mul_comm
-/
theorem le_div_iff_of_neg' (hc : c < 0) : a <= b / c ↔ b <= c * a := by
  rw [mul_comm]; rw [le_div_iff_of_neg hc]

/--
theorem `div_lt_iff_of_neg` / 定理 `div_lt_iff_of_neg`

English:
theorem div_lt_iff_of_neg
  given: (hc : c < 0)
  statement: b / c < a ↔ a * c < b where
  proof: div_mul_cancel₀ b (ne_of_lt hc) ▸ mul_lt_mul_of_neg_right h hc
  mpr h := calc
.symm a = a * c * c⁻¹ := mul_inv_cancel_right₀ hc.ne _
_ > b * c⁻¹ := mul_lt_mul_of_neg_right h inv_lt_zero'.2 hc
.symm _ = b / c := division_def b c

中文:
定理 div_lt_iff_of_neg
  条件: (hc : c < 0)
  结论: b / c < a ↔ a * c < b where
  证明: div_mul_cancel₀ b (ne_of_lt hc) ▸ mul_lt_mul_of_neg_right h hc
  mpr h := calc
.symm a = a * c * c⁻¹ := mul_inv_cancel_right₀ hc.ne _
_ > b * c⁻¹ := mul_lt_mul_of_neg_right h inv_lt_zero'.2 hc
.symm _ = b / c := division_def b c

Depends on / 依赖: mul_lt_mul_of_neg_right, ne_of_lt
-/
theorem div_lt_iff_of_neg (hc : c < 0) : b / c < a ↔ a * c < b where
  mp h := div_mul_cancel₀ b (ne_of_lt hc) ▸ mul_lt_mul_of_neg_right h hc
  mpr h := calc
.symm a = a * c * c⁻¹ := mul_inv_cancel_right₀ hc.ne _
_ > b * c⁻¹ := mul_lt_mul_of_neg_right h inv_lt_zero'.2 hc
.symm _ = b / c := division_def b c

/--
theorem `div_lt_iff_of_neg'` / 定理 `div_lt_iff_of_neg'`

English:
theorem div_lt_iff_of_neg'
  given: (hc : c < 0)
  statement: b / c < a ↔ c * a < b
  proof: by
  rw [mul_comm]; rw [div_lt_iff_of_neg hc]

中文:
定理 div_lt_iff_of_neg'
  条件: (hc : c < 0)
  结论: b / c < a ↔ c * a < b
  证明: by
  rw [mul_comm]; rw [div_lt_iff_of_neg hc]

Depends on / 依赖: div_lt_iff_of_neg, mul_comm
-/
theorem div_lt_iff_of_neg' (hc : c < 0) : b / c < a ↔ c * a < b := by
  rw [mul_comm]; rw [div_lt_iff_of_neg hc]

/--
theorem `lt_div_iff_of_neg` / 定理 `lt_div_iff_of_neg`

English:
theorem lt_div_iff_of_neg
  given: (hc : c < 0)
  statement: a < b / c ↔ b < a * c
  proof: by
  rw [← neg_neg c]; rw [mul_neg]; rw [div_neg]; rw [lt_neg]; rw [div_lt_iff₀ (neg_pos.2 hc)]; rw [neg_mul]

中文:
定理 lt_div_iff_of_neg
  条件: (hc : c < 0)
  结论: a < b / c ↔ b < a * c
  证明: by
  rw [← neg_neg c]; rw [mul_neg]; rw [div_neg]; rw [lt_neg]; rw [div_lt_iff₀ (neg_pos.2 hc)]; rw [neg_mul]

Depends on / 依赖: div_neg, lt_neg, mul_neg, neg_mul, neg_neg, neg_pos
-/
theorem lt_div_iff_of_neg (hc : c < 0) : a < b / c ↔ b < a * c := by
  rw [← neg_neg c]; rw [mul_neg]; rw [div_neg]; rw [lt_neg]; rw [div_lt_iff₀ (neg_pos.2 hc)]; rw [neg_mul]

/--
theorem `lt_div_iff_of_neg'` / 定理 `lt_div_iff_of_neg'`

English:
theorem lt_div_iff_of_neg'
  given: (hc : c < 0)
  statement: a < b / c ↔ b < c * a
  proof: by
  rw [mul_comm]; rw [lt_div_iff_of_neg hc]

中文:
定理 lt_div_iff_of_neg'
  条件: (hc : c < 0)
  结论: a < b / c ↔ b < c * a
  证明: by
  rw [mul_comm]; rw [lt_div_iff_of_neg hc]

Depends on / 依赖: lt_div_iff_of_neg, mul_comm
-/
theorem lt_div_iff_of_neg' (hc : c < 0) : a < b / c ↔ b < c * a := by
  rw [mul_comm]; rw [lt_div_iff_of_neg hc]

/--
theorem `div_le_one_of_ge` / 定理 `div_le_one_of_ge`

English:
theorem div_le_one_of_ge
  given: (h : b <= a) (hb : b <= 0)
  statement: a / b <= 1
  proof: by
  simpa only [neg_div_neg_eq] using div_le_one_of_le₀ (neg_le_neg h) (neg_nonneg_of_nonpos hb)

中文:
定理 div_le_one_of_ge
  条件: (h : b <= a) (hb : b <= 0)
  结论: a / b <= 1
  证明: by
  simpa only [neg_div_neg_eq] using div_le_one_of_le₀ (neg_le_neg h) (neg_nonneg_of_nonpos hb)

Depends on / 依赖: neg_div_neg_eq, neg_le_neg, neg_nonneg_of_nonpos
-/
theorem div_le_one_of_ge (h : b <= a) (hb : b <= 0) : a / b <= 1 := by
  simpa only [neg_div_neg_eq] using div_le_one_of_le₀ (neg_le_neg h) (neg_nonneg_of_nonpos hb)


/--
theorem `inv_le_inv_of_neg` / 定理 `inv_le_inv_of_neg`

English:
theorem inv_le_inv_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: a⁻¹ <= b⁻¹ ↔ b <= a
  proof: by
  rw [← one_div]; rw [div_le_iff_of_neg ha]; rw [← div_eq_inv_mul]; rw [div_le_iff_of_neg hb]; rw [one_mul]

中文:
定理 inv_le_inv_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: a⁻¹ <= b⁻¹ ↔ b <= a
  证明: by
  rw [← one_div]; rw [div_le_iff_of_neg ha]; rw [← div_eq_inv_mul]; rw [div_le_iff_of_neg hb]; rw [one_mul]

Depends on / 依赖: div_eq_inv_mul, div_le_iff_of_neg, one_div, one_mul
-/
theorem inv_le_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ <= b⁻¹ ↔ b <= a := by
  rw [← one_div]; rw [div_le_iff_of_neg ha]; rw [← div_eq_inv_mul]; rw [div_le_iff_of_neg hb]; rw [one_mul]

/--
theorem `inv_le_of_neg` / 定理 `inv_le_of_neg`

English:
theorem inv_le_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: a⁻¹ <= b ↔ b⁻¹ <= a
  proof: by
  rw [← inv_le_inv_of_neg hb (inv_lt_zero'.2 ha)]; rw [inv_inv]

中文:
定理 inv_le_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: a⁻¹ <= b ↔ b⁻¹ <= a
  证明: by
  rw [← inv_le_inv_of_neg hb (inv_lt_zero'.2 ha)]; rw [inv_inv]

Depends on / 依赖: inv_inv, inv_le_inv_of_neg, inv_lt_zero
-/
theorem inv_le_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ <= b ↔ b⁻¹ <= a := by
  rw [← inv_le_inv_of_neg hb (inv_lt_zero'.2 ha)]; rw [inv_inv]

/--
theorem `le_inv_of_neg` / 定理 `le_inv_of_neg`

English:
theorem le_inv_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: a <= b⁻¹ ↔ b <= a⁻¹
  proof: by
  rw [← inv_le_inv_of_neg (inv_lt_zero'.2 hb) ha]; rw [inv_inv]

中文:
定理 le_inv_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: a <= b⁻¹ ↔ b <= a⁻¹
  证明: by
  rw [← inv_le_inv_of_neg (inv_lt_zero'.2 hb) ha]; rw [inv_inv]

Depends on / 依赖: inv_inv, inv_le_inv_of_neg, inv_lt_zero
-/
theorem le_inv_of_neg (ha : a < 0) (hb : b < 0) : a <= b⁻¹ ↔ b <= a⁻¹ := by
  rw [← inv_le_inv_of_neg (inv_lt_zero'.2 hb) ha]; rw [inv_inv]

/--
theorem `inv_lt_inv_of_neg` / 定理 `inv_lt_inv_of_neg`

English:
theorem inv_lt_inv_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: a⁻¹ < b⁻¹ ↔ b < a
  proof: by
  have := div_lt_iff_of_neg ha (b := 1) (a := b⁻¹)
  rwa [one_div, mul_comm b⁻¹, ← division_def, div_lt_iff_of_neg hb, one_mul] at this

中文:
定理 inv_lt_inv_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: a⁻¹ < b⁻¹ ↔ b < a
  证明: by
  have := div_lt_iff_of_neg ha (b := 1) (a := b⁻¹)
  rwa [one_div, mul_comm b⁻¹, ← division_def, div_lt_iff_of_neg hb, one_mul] at this

Depends on / 依赖: div_lt_iff_of_neg, division_def, mul_comm, one_div, one_mul
-/
theorem inv_lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b⁻¹ ↔ b < a := by
  have := div_lt_iff_of_neg ha (b := 1) (a := b⁻¹)
  rwa [one_div, mul_comm b⁻¹, ← division_def, div_lt_iff_of_neg hb, one_mul] at this

/--
theorem `inv_lt_of_neg` / 定理 `inv_lt_of_neg`

English:
theorem inv_lt_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: a⁻¹ < b ↔ b⁻¹ < a
  proof: by
  simpa using inv_lt_inv_of_neg ha (inv_lt_zero'.2 hb)

中文:
定理 inv_lt_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: a⁻¹ < b ↔ b⁻¹ < a
  证明: by
  simpa using inv_lt_inv_of_neg ha (inv_lt_zero'.2 hb)

Depends on / 依赖: inv_lt_inv_of_neg, inv_lt_zero
-/
theorem inv_lt_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b ↔ b⁻¹ < a := by
  simpa using inv_lt_inv_of_neg ha (inv_lt_zero'.2 hb)

/--
theorem `lt_inv_of_neg` / 定理 `lt_inv_of_neg`

English:
theorem lt_inv_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: a < b⁻¹ ↔ b < a⁻¹
  proof: by
  simpa using inv_lt_inv_of_neg (inv_lt_zero'.2 ha) hb

中文:
定理 lt_inv_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: a < b⁻¹ ↔ b < a⁻¹
  证明: by
  simpa using inv_lt_inv_of_neg (inv_lt_zero'.2 ha) hb

Depends on / 依赖: inv_lt_inv_of_neg, inv_lt_zero
-/
theorem lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a < b⁻¹ ↔ b < a⁻¹ := by
  simpa using inv_lt_inv_of_neg (inv_lt_zero'.2 ha) hb



/--
theorem `sub_inv_antitoneOn_Ioi` / 定理 `sub_inv_antitoneOn_Ioi`

English:
theorem sub_inv_antitoneOn_Ioi
  proof: antitoneOn_iff_forall_lt.mpr fun _ ha _ hb hab =>
.mpr sub_le_sub (le_of_lt hab) le_rfl inv_le_inv₀ (sub_pos.mpr hb) (sub_pos.mpr ha)

中文:
定理 sub_inv_antitoneOn_Ioi
  证明: antitoneOn_iff_forall_lt.mpr fun _ ha _ hb hab =>
.mpr sub_le_sub (le_of_lt hab) le_rfl inv_le_inv₀ (sub_pos.mpr hb) (sub_pos.mpr ha)

Depends on / 依赖: antitoneOn_iff_forall_lt, antitoneOn_iff_forall_lt.mpr, le_of_lt, le_rfl, sub_le_sub, sub_pos, sub_pos.mpr
-/
theorem sub_inv_antitoneOn_Ioi :
    AntitoneOn (fun x => (x - c)⁻¹) (Set.Ioi c) :=
  antitoneOn_iff_forall_lt.mpr fun _ ha _ hb hab =>
.mpr sub_le_sub (le_of_lt hab) le_rfl inv_le_inv₀ (sub_pos.mpr hb) (sub_pos.mpr ha)

/--
theorem `sub_inv_antitoneOn_Iio` / 定理 `sub_inv_antitoneOn_Iio`

English:
theorem sub_inv_antitoneOn_Iio
  proof: antitoneOn_iff_forall_lt.mpr fun _ ha _ hb hab =>
.mpr sub_le_sub (le_of_lt hab) le_rfl inv_le_inv_of_neg (sub_neg.mpr hb) (sub_neg.mpr ha)

中文:
定理 sub_inv_antitoneOn_Iio
  证明: antitoneOn_iff_forall_lt.mpr fun _ ha _ hb hab =>
.mpr sub_le_sub (le_of_lt hab) le_rfl inv_le_inv_of_neg (sub_neg.mpr hb) (sub_neg.mpr ha)

Depends on / 依赖: antitoneOn_iff_forall_lt, antitoneOn_iff_forall_lt.mpr, inv_le_inv_of_neg, le_of_lt, le_rfl, sub_le_sub, sub_neg, sub_neg.mpr
-/
theorem sub_inv_antitoneOn_Iio :
    AntitoneOn (fun x => (x - c)⁻¹) (Set.Iio c) :=
  antitoneOn_iff_forall_lt.mpr fun _ ha _ hb hab =>
.mpr sub_le_sub (le_of_lt hab) le_rfl inv_le_inv_of_neg (sub_neg.mpr hb) (sub_neg.mpr ha)

/--
theorem `sub_inv_antitoneOn_Icc_right` / 定理 `sub_inv_antitoneOn_Icc_right`

English:
theorem sub_inv_antitoneOn_Icc_right
  given: (ha : c < a)
  proof: by
  by_cases hab : a <= b
· exact sub_inv_antitoneOn_Ioi.mono (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

中文:
定理 sub_inv_antitoneOn_Icc_right
  条件: (ha : c < a)
  证明: by
  by_cases hab : a <= b
· exact sub_inv_antitoneOn_Ioi.mono (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

Depends on / 依赖: Icc_subset_Ioi_iff, Set.Icc_subset_Ioi_iff, Set.Subsingleton.antitoneOn, Subsingleton, antitoneOn, sub_inv_antitoneOn_Ioi, sub_inv_antitoneOn_Ioi.mono
-/
theorem sub_inv_antitoneOn_Icc_right (ha : c < a) :
    AntitoneOn (fun x => (x - c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a <= b
· exact sub_inv_antitoneOn_Ioi.mono (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

/--
theorem `sub_inv_antitoneOn_Icc_left` / 定理 `sub_inv_antitoneOn_Icc_left`

English:
theorem sub_inv_antitoneOn_Icc_left
  given: (ha : b < c)
  proof: by
  by_cases hab : a <= b
· exact sub_inv_antitoneOn_Iio.mono (Set.Icc_subset_Iio_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

中文:
定理 sub_inv_antitoneOn_Icc_left
  条件: (ha : b < c)
  证明: by
  by_cases hab : a <= b
· exact sub_inv_antitoneOn_Iio.mono (Set.Icc_subset_Iio_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

Depends on / 依赖: Icc_subset_Iio_iff, Set.Icc_subset_Iio_iff, Set.Subsingleton.antitoneOn, Subsingleton, antitoneOn, sub_inv_antitoneOn_Iio, sub_inv_antitoneOn_Iio.mono
-/
theorem sub_inv_antitoneOn_Icc_left (ha : b < c) :
    AntitoneOn (fun x => (x - c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a <= b
· exact sub_inv_antitoneOn_Iio.mono (Set.Icc_subset_Iio_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

/--
theorem `inv_antitoneOn_Ioi` / 定理 `inv_antitoneOn_Ioi`

English:
theorem inv_antitoneOn_Ioi
  proof: by
  convert! sub_inv_antitoneOn_Ioi (α := α)
  exact (sub_zero _).symm

中文:
定理 inv_antitoneOn_Ioi
  证明: by
  convert! sub_inv_antitoneOn_Ioi (α := α)
  exact (sub_zero _).symm

Depends on / 依赖: convert, sub_inv_antitoneOn_Ioi, sub_zero
-/
theorem inv_antitoneOn_Ioi :
    AntitoneOn (fun x : α => x⁻¹) (Set.Ioi 0) := by
  convert! sub_inv_antitoneOn_Ioi (α := α)
  exact (sub_zero _).symm

/--
theorem `inv_antitoneOn_Iio` / 定理 `inv_antitoneOn_Iio`

English:
theorem inv_antitoneOn_Iio
  proof: by
  convert! sub_inv_antitoneOn_Iio (α := α)
  exact (sub_zero _).symm

中文:
定理 inv_antitoneOn_Iio
  证明: by
  convert! sub_inv_antitoneOn_Iio (α := α)
  exact (sub_zero _).symm

Depends on / 依赖: convert, sub_inv_antitoneOn_Iio, sub_zero
-/
theorem inv_antitoneOn_Iio :
    AntitoneOn (fun x : α => x⁻¹) (Set.Iio 0) := by
  convert! sub_inv_antitoneOn_Iio (α := α)
  exact (sub_zero _).symm

/--
theorem `inv_antitoneOn_Icc_right` / 定理 `inv_antitoneOn_Icc_right`

English:
theorem inv_antitoneOn_Icc_right
  given: (ha : 0 < a)
  proof: by
  convert! sub_inv_antitoneOn_Icc_right ha
  exact (sub_zero _).symm

中文:
定理 inv_antitoneOn_Icc_right
  条件: (ha : 0 < a)
  证明: by
  convert! sub_inv_antitoneOn_Icc_right ha
  exact (sub_zero _).symm

Depends on / 依赖: convert, sub_inv_antitoneOn_Icc_right, sub_zero
-/
theorem inv_antitoneOn_Icc_right (ha : 0 < a) :
    AntitoneOn (fun x : α => x⁻¹) (Set.Icc a b) := by
  convert! sub_inv_antitoneOn_Icc_right ha
  exact (sub_zero _).symm

/--
theorem `inv_antitoneOn_Icc_left` / 定理 `inv_antitoneOn_Icc_left`

English:
theorem inv_antitoneOn_Icc_left
  given: (hb : b < 0)
  proof: by
  convert! sub_inv_antitoneOn_Icc_left hb
  exact (sub_zero _).symm

中文:
定理 inv_antitoneOn_Icc_left
  条件: (hb : b < 0)
  证明: by
  convert! sub_inv_antitoneOn_Icc_left hb
  exact (sub_zero _).symm

Depends on / 依赖: convert, sub_inv_antitoneOn_Icc_left, sub_zero
-/
theorem inv_antitoneOn_Icc_left (hb : b < 0) :
    AntitoneOn (fun x : α => x⁻¹) (Set.Icc a b) := by
  convert! sub_inv_antitoneOn_Icc_left hb
  exact (sub_zero _).symm



/--
theorem `div_le_div_of_nonpos_of_le` / 定理 `div_le_div_of_nonpos_of_le`

English:
theorem div_le_div_of_nonpos_of_le
  given: (hc : c <= 0) (h : b <= a)
  statement: a / c <= b / c
  proof: by
  rw [div_eq_mul_inv a c]; rw [div_eq_mul_inv b c]
  exact mul_le_mul_of_nonpos_right h (inv_nonpos'.2 hc)

中文:
定理 div_le_div_of_nonpos_of_le
  条件: (hc : c <= 0) (h : b <= a)
  结论: a / c <= b / c
  证明: by
  rw [div_eq_mul_inv a c]; rw [div_eq_mul_inv b c]
  exact mul_le_mul_of_nonpos_right h (inv_nonpos'.2 hc)

Depends on / 依赖: div_eq_mul_inv, inv_nonpos, mul_le_mul_of_nonpos_right
-/
theorem div_le_div_of_nonpos_of_le (hc : c <= 0) (h : b <= a) : a / c <= b / c := by
  rw [div_eq_mul_inv a c]; rw [div_eq_mul_inv b c]
  exact mul_le_mul_of_nonpos_right h (inv_nonpos'.2 hc)

/--
theorem `div_lt_div_of_neg_of_lt` / 定理 `div_lt_div_of_neg_of_lt`

English:
theorem div_lt_div_of_neg_of_lt
  given: (hc : c < 0) (h : b < a)
  statement: a / c < b / c
  proof: by
  rw [div_eq_mul_inv a c]; rw [div_eq_mul_inv b c]
  exact mul_lt_mul_of_neg_right h (inv_lt_zero'.2 hc)

中文:
定理 div_lt_div_of_neg_of_lt
  条件: (hc : c < 0) (h : b < a)
  结论: a / c < b / c
  证明: by
  rw [div_eq_mul_inv a c]; rw [div_eq_mul_inv b c]
  exact mul_lt_mul_of_neg_right h (inv_lt_zero'.2 hc)

Depends on / 依赖: div_eq_mul_inv, inv_lt_zero, mul_lt_mul_of_neg_right
-/
theorem div_lt_div_of_neg_of_lt (hc : c < 0) (h : b < a) : a / c < b / c := by
  rw [div_eq_mul_inv a c]; rw [div_eq_mul_inv b c]
  exact mul_lt_mul_of_neg_right h (inv_lt_zero'.2 hc)

/--
theorem `div_le_div_right_of_neg` / 定理 `div_le_div_right_of_neg`

English:
theorem div_le_div_right_of_neg
  given: (hc : c < 0)
  statement: a / c <= b / c ↔ b <= a
  proof: by
  rw [div_le_iff_of_neg hc]; rw [div_mul_cancel₀ _ hc.ne]

中文:
定理 div_le_div_right_of_neg
  条件: (hc : c < 0)
  结论: a / c <= b / c ↔ b <= a
  证明: by
  rw [div_le_iff_of_neg hc]; rw [div_mul_cancel₀ _ hc.ne]

Depends on / 依赖: div_le_iff_of_neg, hc.ne
-/
theorem div_le_div_right_of_neg (hc : c < 0) : a / c <= b / c ↔ b <= a := by
  rw [div_le_iff_of_neg hc]; rw [div_mul_cancel₀ _ hc.ne]

/--
theorem `div_lt_div_right_of_neg` / 定理 `div_lt_div_right_of_neg`

English:
theorem div_lt_div_right_of_neg
  given: (hc : c < 0)
  statement: a / c < b / c ↔ b < a
  proof: by
  rw [div_lt_iff_of_neg hc]; rw [div_mul_cancel₀ _ hc.ne]

中文:
定理 div_lt_div_right_of_neg
  条件: (hc : c < 0)
  结论: a / c < b / c ↔ b < a
  证明: by
  rw [div_lt_iff_of_neg hc]; rw [div_mul_cancel₀ _ hc.ne]

Depends on / 依赖: div_lt_iff_of_neg, hc.ne
-/
theorem div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a := by
  rw [div_lt_iff_of_neg hc]; rw [div_mul_cancel₀ _ hc.ne]



/--
theorem `one_le_div_of_neg` / 定理 `one_le_div_of_neg`

English:
theorem one_le_div_of_neg
  given: (hb : b < 0)
  statement: 1 <= a / b ↔ a <= b
  proof: by rw [le_div_iff_of_neg hb, one_mul]

中文:
定理 one_le_div_of_neg
  条件: (hb : b < 0)
  结论: 1 <= a / b ↔ a <= b
  证明: by rw [le_div_iff_of_neg hb, one_mul]

Depends on / 依赖: le_div_iff_of_neg, one_mul
-/
theorem one_le_div_of_neg (hb : b < 0) : 1 <= a / b ↔ a <= b := by rw [le_div_iff_of_neg hb, one_mul]

/--
theorem `div_le_one_of_neg` / 定理 `div_le_one_of_neg`

English:
theorem div_le_one_of_neg
  given: (hb : b < 0)
  statement: a / b <= 1 ↔ b <= a
  proof: by rw [div_le_iff_of_neg hb, one_mul]

中文:
定理 div_le_one_of_neg
  条件: (hb : b < 0)
  结论: a / b <= 1 ↔ b <= a
  证明: by rw [div_le_iff_of_neg hb, one_mul]

Depends on / 依赖: div_le_iff_of_neg, one_mul
-/
theorem div_le_one_of_neg (hb : b < 0) : a / b <= 1 ↔ b <= a := by rw [div_le_iff_of_neg hb, one_mul]

/--
theorem `one_lt_div_of_neg` / 定理 `one_lt_div_of_neg`

English:
theorem one_lt_div_of_neg
  given: (hb : b < 0)
  statement: 1 < a / b ↔ a < b
  proof: by rw [lt_div_iff_of_neg hb, one_mul]

中文:
定理 one_lt_div_of_neg
  条件: (hb : b < 0)
  结论: 1 < a / b ↔ a < b
  证明: by rw [lt_div_iff_of_neg hb, one_mul]

Depends on / 依赖: lt_div_iff_of_neg, one_mul
-/
theorem one_lt_div_of_neg (hb : b < 0) : 1 < a / b ↔ a < b := by rw [lt_div_iff_of_neg hb, one_mul]

/--
theorem `div_lt_one_of_neg` / 定理 `div_lt_one_of_neg`

English:
theorem div_lt_one_of_neg
  given: (hb : b < 0)
  statement: a / b < 1 ↔ b < a
  proof: by rw [div_lt_iff_of_neg hb, one_mul]

中文:
定理 div_lt_one_of_neg
  条件: (hb : b < 0)
  结论: a / b < 1 ↔ b < a
  证明: by rw [div_lt_iff_of_neg hb, one_mul]

Depends on / 依赖: div_lt_iff_of_neg, one_mul
-/
theorem div_lt_one_of_neg (hb : b < 0) : a / b < 1 ↔ b < a := by rw [div_lt_iff_of_neg hb, one_mul]

/--
theorem `one_div_le_of_neg` / 定理 `one_div_le_of_neg`

English:
theorem one_div_le_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: 1 / a <= b ↔ 1 / b <= a
  proof: by
  simpa using inv_le_of_neg ha hb

中文:
定理 one_div_le_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: 1 / a <= b ↔ 1 / b <= a
  证明: by
  simpa using inv_le_of_neg ha hb

Depends on / 依赖: inv_le_of_neg
-/
theorem one_div_le_of_neg (ha : a < 0) (hb : b < 0) : 1 / a <= b ↔ 1 / b <= a := by
  simpa using inv_le_of_neg ha hb

/--
theorem `one_div_lt_of_neg` / 定理 `one_div_lt_of_neg`

English:
theorem one_div_lt_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: 1 / a < b ↔ 1 / b < a
  proof: by
  simpa using inv_lt_of_neg ha hb

中文:
定理 one_div_lt_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: 1 / a < b ↔ 1 / b < a
  证明: by
  simpa using inv_lt_of_neg ha hb

Depends on / 依赖: inv_lt_of_neg
-/
theorem one_div_lt_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < b ↔ 1 / b < a := by
  simpa using inv_lt_of_neg ha hb

/--
theorem `le_one_div_of_neg` / 定理 `le_one_div_of_neg`

English:
theorem le_one_div_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: a <= 1 / b ↔ b <= 1 / a
  proof: by
  simpa using le_inv_of_neg ha hb

中文:
定理 le_one_div_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: a <= 1 / b ↔ b <= 1 / a
  证明: by
  simpa using le_inv_of_neg ha hb

Depends on / 依赖: le_inv_of_neg
-/
theorem le_one_div_of_neg (ha : a < 0) (hb : b < 0) : a <= 1 / b ↔ b <= 1 / a := by
  simpa using le_inv_of_neg ha hb

/--
theorem `lt_one_div_of_neg` / 定理 `lt_one_div_of_neg`

English:
theorem lt_one_div_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: a < 1 / b ↔ b < 1 / a
  proof: by
  simpa using lt_inv_of_neg ha hb

中文:
定理 lt_one_div_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: a < 1 / b ↔ b < 1 / a
  证明: by
  simpa using lt_inv_of_neg ha hb

Depends on / 依赖: lt_inv_of_neg
-/
theorem lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : a < 1 / b ↔ b < 1 / a := by
  simpa using lt_inv_of_neg ha hb



/--
theorem `one_div_le_one_div_of_neg_of_le` / 定理 `one_div_le_one_div_of_neg_of_le`

English:
theorem one_div_le_one_div_of_neg_of_le
  given: (hb : b < 0) (h : a <= b)
  statement: 1 / b <= 1 / a
  proof: by
  rwa [div_le_iff_of_neg' hb, ← div_eq_mul_one_div, div_le_one_of_neg (h.trans_lt hb)]

中文:
定理 one_div_le_one_div_of_neg_of_le
  条件: (hb : b < 0) (h : a <= b)
  结论: 1 / b <= 1 / a
  证明: by
  rwa [div_le_iff_of_neg' hb, ← div_eq_mul_one_div, div_le_one_of_neg (h.trans_lt hb)]

Depends on / 依赖: div_eq_mul_one_div, div_le_iff_of_neg, div_le_one_of_neg, h.trans_lt, trans_lt
-/
theorem one_div_le_one_div_of_neg_of_le (hb : b < 0) (h : a <= b) : 1 / b <= 1 / a := by
  rwa [div_le_iff_of_neg' hb, ← div_eq_mul_one_div, div_le_one_of_neg (h.trans_lt hb)]

/--
theorem `one_div_lt_one_div_of_neg_of_lt` / 定理 `one_div_lt_one_div_of_neg_of_lt`

English:
theorem one_div_lt_one_div_of_neg_of_lt
  given: (hb : b < 0) (h : a < b)
  statement: 1 / b < 1 / a
  proof: by
  rwa [div_lt_iff_of_neg' hb, ← div_eq_mul_one_div, div_lt_one_of_neg (h.trans hb)]

中文:
定理 one_div_lt_one_div_of_neg_of_lt
  条件: (hb : b < 0) (h : a < b)
  结论: 1 / b < 1 / a
  证明: by
  rwa [div_lt_iff_of_neg' hb, ← div_eq_mul_one_div, div_lt_one_of_neg (h.trans hb)]

Depends on / 依赖: div_eq_mul_one_div, div_lt_iff_of_neg, div_lt_one_of_neg, h.trans
-/
theorem one_div_lt_one_div_of_neg_of_lt (hb : b < 0) (h : a < b) : 1 / b < 1 / a := by
  rwa [div_lt_iff_of_neg' hb, ← div_eq_mul_one_div, div_lt_one_of_neg (h.trans hb)]

/--
theorem `le_of_neg_of_one_div_le_one_div` / 定理 `le_of_neg_of_one_div_le_one_div`

English:
theorem le_of_neg_of_one_div_le_one_div
  given: (hb : b < 0) (h : 1 / a <= 1 / b)
  statement: b <= a
  proof: by
  simpa using one_div_le_one_div_of_neg_of_le (one_div b ▸ inv_lt_zero'.2 hb) h

中文:
定理 le_of_neg_of_one_div_le_one_div
  条件: (hb : b < 0) (h : 1 / a <= 1 / b)
  结论: b <= a
  证明: by
  simpa using one_div_le_one_div_of_neg_of_le (one_div b ▸ inv_lt_zero'.2 hb) h

Depends on / 依赖: inv_lt_zero, one_div, one_div_le_one_div_of_neg_of_le
-/
theorem le_of_neg_of_one_div_le_one_div (hb : b < 0) (h : 1 / a <= 1 / b) : b <= a := by
  simpa using one_div_le_one_div_of_neg_of_le (one_div b ▸ inv_lt_zero'.2 hb) h

/--
theorem `lt_of_neg_of_one_div_lt_one_div` / 定理 `lt_of_neg_of_one_div_lt_one_div`

English:
theorem lt_of_neg_of_one_div_lt_one_div
  given: (hb : b < 0) (h : 1 / a < 1 / b)
  statement: b < a
  proof: by
  simpa using one_div_lt_one_div_of_neg_of_lt (one_div b ▸ inv_lt_zero'.2 hb) h

中文:
定理 lt_of_neg_of_one_div_lt_one_div
  条件: (hb : b < 0) (h : 1 / a < 1 / b)
  结论: b < a
  证明: by
  simpa using one_div_lt_one_div_of_neg_of_lt (one_div b ▸ inv_lt_zero'.2 hb) h

Depends on / 依赖: inv_lt_zero, one_div, one_div_lt_one_div_of_neg_of_lt
-/
theorem lt_of_neg_of_one_div_lt_one_div (hb : b < 0) (h : 1 / a < 1 / b) : b < a := by
  simpa using one_div_lt_one_div_of_neg_of_lt (one_div b ▸ inv_lt_zero'.2 hb) h

/--
theorem `one_div_le_one_div_of_neg` / 定理 `one_div_le_one_div_of_neg`

English:
theorem one_div_le_one_div_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: 1 / a <= 1 / b ↔ b <= a
  proof: by
  simpa [one_div] using inv_le_inv_of_neg ha hb

中文:
定理 one_div_le_one_div_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: 1 / a <= 1 / b ↔ b <= a
  证明: by
  simpa [one_div] using inv_le_inv_of_neg ha hb

Depends on / 依赖: inv_le_inv_of_neg, one_div
-/
theorem one_div_le_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a <= 1 / b ↔ b <= a := by
  simpa [one_div] using inv_le_inv_of_neg ha hb

/--
theorem `one_div_lt_one_div_of_neg` / 定理 `one_div_lt_one_div_of_neg`

English:
theorem one_div_lt_one_div_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: 1 / a < 1 / b ↔ b < a
  proof: by
  simpa [one_div] using inv_lt_inv_of_neg ha hb

中文:
定理 one_div_lt_one_div_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: 1 / a < 1 / b ↔ b < a
  证明: by
  simpa [one_div] using inv_lt_inv_of_neg ha hb

Depends on / 依赖: LinearOrderedCommMonoidWithZero, LinearOrderedCommMonoidWithZero.toMulPosStrictMono, inv_lt_inv_of_neg, one_div, toMulPosStrictMono
-/
theorem one_div_lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < 1 / b ↔ b < a := by
  simpa [one_div] using inv_lt_inv_of_neg ha hb

/--
theorem `one_div_lt_neg_one` / 定理 `one_div_lt_neg_one`

English:
theorem one_div_lt_neg_one
  given: (h1 : a < 0) (h2 : -1 < a)
  statement: 1 / a < -1
  proof: suffices 1 / a < 1 / -1 by rwa [one_div_neg_one_eq_neg_one] at this
  one_div_lt_one_div_of_neg_of_lt h1 h2

中文:
定理 one_div_lt_neg_one
  条件: (h1 : a < 0) (h2 : -1 < a)
  结论: 1 / a < -1
  证明: suffices 1 / a < 1 / -1 by rwa [one_div_neg_one_eq_neg_one] at this
  one_div_lt_one_div_of_neg_of_lt h1 h2

Depends on / 依赖: LinearOrderedCommMonoidWithZero, LinearOrderedCommMonoidWithZero.toIsOrderedMonoid, one_div_lt_one_div_of_neg_of_lt, one_div_neg_one_eq_neg_one, toIsOrderedMonoid
-/
theorem one_div_lt_neg_one (h1 : a < 0) (h2 : -1 < a) : 1 / a < -1 :=
  suffices 1 / a < 1 / -1 by rwa [one_div_neg_one_eq_neg_one] at this
  one_div_lt_one_div_of_neg_of_lt h1 h2

/--
theorem `one_div_le_neg_one` / 定理 `one_div_le_neg_one`

English:
theorem one_div_le_neg_one
  given: (h1 : a < 0) (h2 : -1 <= a)
  statement: 1 / a <= -1
  proof: suffices 1 / a <= 1 / -1 by rwa [one_div_neg_one_eq_neg_one] at this
  one_div_le_one_div_of_neg_of_le h1 h2

中文:
定理 one_div_le_neg_one
  条件: (h1 : a < 0) (h2 : -1 <= a)
  结论: 1 / a <= -1
  证明: suffices 1 / a <= 1 / -1 by rwa [one_div_neg_one_eq_neg_one] at this
  one_div_le_one_div_of_neg_of_le h1 h2

Depends on / 依赖: IsCancelMulZero, one_div_le_one_div_of_neg_of_le, one_div_neg_one_eq_neg_one
-/
theorem one_div_le_neg_one (h1 : a < 0) (h2 : -1 <= a) : 1 / a <= -1 :=
  suffices 1 / a <= 1 / -1 by rwa [one_div_neg_one_eq_neg_one] at this
  one_div_le_one_div_of_neg_of_le h1 h2

/-! ### Results about halving -/

omit [PosMulReflectLT α] in
/--
theorem `sub_self_div_two` / 定理 `sub_self_div_two`

English:
theorem sub_self_div_two
  given: (a : α)
  statement: a - a / 2 = a / 2
  proof: by
  grind

omit [PosMulReflectLT α] in

中文:
定理 sub_self_div_two
  条件: (a : α)
  结论: a - a / 2 = a / 2
  证明: by
  grind

omit [PosMulReflectLT α] in
-/
theorem sub_self_div_two (a : α) : a - a / 2 = a / 2 := by
  grind

omit [PosMulReflectLT α] in
/--
theorem `div_two_sub_self` / 定理 `div_two_sub_self`

English:
theorem div_two_sub_self
  given: (a : α)
  statement: a / 2 - a = -(a / 2)
  proof: by
  grind

中文:
定理 div_two_sub_self
  条件: (a : α)
  结论: a / 2 - a = -(a / 2)
  证明: by
  grind

Depends on / 依赖: LinearOrderedCommMonoidWithZero, LinearOrderedCommMonoidWithZero.toIsMulTorsionFree, toIsMulTorsionFree
-/
theorem div_two_sub_self (a : α) : a / 2 - a = -(a / 2) := by
  grind

/--
theorem `add_sub_div_two_lt` / 定理 `add_sub_div_two_lt`

English:
theorem add_sub_div_two_lt
  given: (h : a < b)
  statement: a + (b - a) / 2 < b
  proof: by
  rwa [← div_sub_div_same, sub_eq_add_neg, add_comm (b / 2), ← add_assoc, ← sub_eq_add_neg, ←
    lt_sub_iff_add_lt, sub_self_div_two, sub_self_div_two,
    div_lt_div_iff_of_pos_right (zero_lt_two' α)]

中文:
定理 add_sub_div_two_lt
  条件: (h : a < b)
  结论: a + (b - a) / 2 < b
  证明: by
  rwa [← div_sub_div_same, sub_eq_add_neg, add_comm (b / 2), ← add_assoc, ← sub_eq_add_neg, ←
    lt_sub_iff_add_lt, sub_self_div_two, sub_self_div_two,
    div_lt_div_iff_of_pos_right (zero_lt_two' α)]

Depends on / 依赖: add_assoc, add_comm, div_lt_div_iff_of_pos_right, div_sub_div_same, lt_sub_iff_add_lt, sub_eq_add_neg, sub_self_div_two, zero_lt_two
-/
theorem add_sub_div_two_lt (h : a < b) : a + (b - a) / 2 < b := by
  rwa [← div_sub_div_same, sub_eq_add_neg, add_comm (b / 2), ← add_assoc, ← sub_eq_add_neg, ←
    lt_sub_iff_add_lt, sub_self_div_two, sub_self_div_two,
    div_lt_div_iff_of_pos_right (zero_lt_two' α)]

/--
theorem `sub_one_div_inv_le_two` / 定理 `sub_one_div_inv_le_two`

English:
theorem sub_one_div_inv_le_two
  given: (a2 : 2 <= a)
  statement: (1 - 1 / a)⁻¹ <= 2
  proof: by
  -- Take inverses on both sides to obtain `2⁻¹ ≤ 1 - 1 / a`
  refine (inv_anti₀ (inv_pos.2 <| zero_lt_two' α) ?_).trans_eq (inv_inv (2 : α))
  -- move `1 / a` to the left and `2⁻¹` to the right.
  rw [le_sub_iff_add_le]; rw [add_comm]; rw [← le_sub_iff_add_le]
  -- take inverses on both sides and use the assumption `2 ≤ a`.
  convert (one_div a).le.trans (inv_anti₀ zero_lt_two a2)
    -- show `1 - 1 / 2 = 1 / 2`.

  -- show `1 - 1 / 2 = 1 / 2`.
  rw [sub_eq_iff_eq_add]; rw [← two_mul]; rw [mul_inv_cancel₀ two_ne_zero]

中文:
定理 sub_one_div_inv_le_two
  条件: (a2 : 2 <= a)
  结论: (1 - 1 / a)⁻¹ <= 2
  证明: by
  -- Take inverses on both sides to obtain `2⁻¹ ≤ 1 - 1 / a`
  refine (inv_anti₀ (inv_pos.2 <| zero_lt_two' α) ?_).trans_eq (inv_inv (2 : α))
  -- move `1 / a` to the left and `2⁻¹` to the right.
  rw [le_sub_iff_add_le]; rw [add_comm]; rw [← le_sub_iff_add_le]
  -- take inverses on both sides and use the assumption `2 ≤ a`.
  convert (one_div a).le.trans (inv_anti₀ zero_lt_two a2)
    -- show `1 - 1 / 2 = 1 / 2`.

  -- show `1 - 1 / 2 = 1 / 2`.
  rw [sub_eq_iff_eq_add]; rw [← two_mul]; rw [mul_inv_cancel₀ two_ne_zero]
-/
theorem sub_one_div_inv_le_two (a2 : 2 <= a) : (1 - 1 / a)⁻¹ <= 2 := by
  -- Take inverses on both sides to obtain `2⁻¹ ≤ 1 - 1 / a`
  refine (inv_anti₀ (inv_pos.2 <| zero_lt_two' α) ?_).trans_eq (inv_inv (2 : α))
  -- move `1 / a` to the left and `2⁻¹` to the right.
  rw [le_sub_iff_add_le]; rw [add_comm]; rw [← le_sub_iff_add_le]
  -- take inverses on both sides and use the assumption `2 ≤ a`.
  convert (one_div a).le.trans (inv_anti₀ zero_lt_two a2)
    -- show `1 - 1 / 2 = 1 / 2`.

  -- show `1 - 1 / 2 = 1 / 2`.
  rw [sub_eq_iff_eq_add]; rw [← two_mul]; rw [mul_inv_cancel₀ two_ne_zero]

/-! ### Miscellaneous lemmas -/


omit [PosMulReflectLT α] in
/--
theorem `mul_sub_mul_div_mul_neg_iff` / 定理 `mul_sub_mul_div_mul_neg_iff`

English:
theorem mul_sub_mul_div_mul_neg_iff
  given: (hc : c != 0) (hd : d != 0)
  proof: by
  rw [mul_comm b c]; rw [← div_sub_div _ _ hc hd]; rw [sub_lt_zero]

omit [PosMulReflectLT α] in

中文:
定理 mul_sub_mul_div_mul_neg_iff
  条件: (hc : c != 0) (hd : d != 0)
  证明: by
  rw [mul_comm b c]; rw [← div_sub_div _ _ hc hd]; rw [sub_lt_zero]

omit [PosMulReflectLT α] in

Depends on / 依赖: div_sub_div, mul_comm, sub_lt_zero
-/
theorem mul_sub_mul_div_mul_neg_iff (hc : c != 0) (hd : d != 0) :
    (a * d - b * c) / (c * d) < 0 ↔ a / c < b / d := by
  rw [mul_comm b c]; rw [← div_sub_div _ _ hc hd]; rw [sub_lt_zero]

omit [PosMulReflectLT α] in
/--
theorem `mul_sub_mul_div_mul_nonpos_iff` / 定理 `mul_sub_mul_div_mul_nonpos_iff`

English:
theorem mul_sub_mul_div_mul_nonpos_iff
  given: (hc : c != 0) (hd : d != 0)
  proof: by
  rw [mul_comm b c]; rw [← div_sub_div _ _ hc hd]; rw [sub_nonpos]

alias ⟨div_lt_div_of_mul_sub_mul_div_neg, mul_sub_mul_div_mul_neg⟩ := mul_sub_mul_div_mul_neg_iff

alias ⟨div_le_div_of_mul_sub_mul_div_nonpos, mul_sub_mul_div_mul_nonpos⟩ :=
  mul_sub_mul_div_mul_nonpos_iff

中文:
定理 mul_sub_mul_div_mul_nonpos_iff
  条件: (hc : c != 0) (hd : d != 0)
  证明: by
  rw [mul_comm b c]; rw [← div_sub_div _ _ hc hd]; rw [sub_nonpos]

alias ⟨div_lt_div_of_mul_sub_mul_div_neg, mul_sub_mul_div_mul_neg⟩ := mul_sub_mul_div_mul_neg_iff

alias ⟨div_le_div_of_mul_sub_mul_div_nonpos, mul_sub_mul_div_mul_nonpos⟩ :=
  mul_sub_mul_div_mul_nonpos_iff

Depends on / 依赖: div_sub_div, mul_comm, sub_nonpos
-/
theorem mul_sub_mul_div_mul_nonpos_iff (hc : c != 0) (hd : d != 0) :
    (a * d - b * c) / (c * d) <= 0 ↔ a / c <= b / d := by
  rw [mul_comm b c]; rw [← div_sub_div _ _ hc hd]; rw [sub_nonpos]

alias ⟨div_lt_div_of_mul_sub_mul_div_neg, mul_sub_mul_div_mul_neg⟩ := mul_sub_mul_div_mul_neg_iff

alias ⟨div_le_div_of_mul_sub_mul_div_nonpos, mul_sub_mul_div_mul_nonpos⟩ :=
  mul_sub_mul_div_mul_nonpos_iff

/--
theorem `exists_add_lt_and_pos_of_lt` / 定理 `exists_add_lt_and_pos_of_lt`

English:
theorem exists_add_lt_and_pos_of_lt
  given: (h : b < a)
  statement: exists c, b + c < a ∧ 0 < c
  proof: ⟨(a - b) / 2, add_sub_div_two_lt h, div_pos (sub_pos_of_lt h) zero_lt_two⟩

中文:
定理 存在_add_lt_and_pos_of_lt
  条件: (h : b < a)
  结论: 存在 c, b + c < a ∧ 0 < c
  证明: ⟨(a - b) / 2, add_sub_div_two_lt h, div_pos (sub_pos_of_lt h) zero_lt_two⟩

Depends on / 依赖: add_sub_div_two_lt, div_pos, sub_pos_of_lt, zero_lt_two
-/
theorem exists_add_lt_and_pos_of_lt (h : b < a) : exists c, b + c < a ∧ 0 < c :=
  ⟨(a - b) / 2, add_sub_div_two_lt h, div_pos (sub_pos_of_lt h) zero_lt_two⟩

end PartialOrderedField

section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d : α} {n : Int}

/--
theorem `div_pos_iff` / 定理 `div_pos_iff`

English:
theorem div_pos_iff
  statement: 0 < a / b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0
  proof: by
  simp only [division_def, mul_pos_iff, inv_pos, inv_lt_zero]

中文:
定理 div_pos_iff
  结论: 0 < a / b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0
  证明: by
  simp only [division_def, mul_pos_iff, inv_pos, inv_lt_zero]

Depends on / 依赖: division_def, inv_lt_zero, inv_pos, mul_pos_iff
-/
theorem div_pos_iff : 0 < a / b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  simp only [division_def, mul_pos_iff, inv_pos, inv_lt_zero]

/--
theorem `div_neg_iff` / 定理 `div_neg_iff`

English:
theorem div_neg_iff
  statement: a / b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b
  proof: by
  simp [division_def, mul_neg_iff]

中文:
定理 div_neg_iff
  结论: a / b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b
  证明: by
  simp [division_def, mul_neg_iff]

Depends on / 依赖: division_def, mul_neg_iff
-/
theorem div_neg_iff : a / b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  simp [division_def, mul_neg_iff]

/--
theorem `div_nonneg_iff` / 定理 `div_nonneg_iff`

English:
theorem div_nonneg_iff
  statement: 0 <= a / b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
  proof: by
  simp [division_def, mul_nonneg_iff]

中文:
定理 div_nonneg_iff
  结论: 0 <= a / b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
  证明: by
  simp [division_def, mul_nonneg_iff]

Depends on / 依赖: division_def, mul_nonneg_iff
-/
theorem div_nonneg_iff : 0 <= a / b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0 := by
  simp [division_def, mul_nonneg_iff]

/--
theorem `div_nonpos_iff` / 定理 `div_nonpos_iff`

English:
theorem div_nonpos_iff
  statement: a / b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b
  proof: by
  simp [division_def, mul_nonpos_iff]

中文:
定理 div_nonpos_iff
  结论: a / b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b
  证明: by
  simp [division_def, mul_nonpos_iff]

Depends on / 依赖: division_def, mul_nonpos_iff
-/
theorem div_nonpos_iff : a / b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b := by
  simp [division_def, mul_nonpos_iff]

/--
theorem `one_lt_div_iff` / 定理 `one_lt_div_iff`

English:
theorem one_lt_div_iff
  statement: 1 < a / b ↔ 0 < b ∧ b < a ∨ b < 0 ∧ a < b
  proof: by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, one_lt_div_of_neg]
  · simp [zero_le_one]
  · simp [hb, hb.not_gt, one_lt_div]

中文:
定理 one_lt_div_iff
  结论: 1 < a / b ↔ 0 < b ∧ b < a ∨ b < 0 ∧ a < b
  证明: by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, one_lt_div_of_neg]
  · simp [zero_le_one]
  · simp [hb, hb.not_gt, one_lt_div]

Depends on / 依赖: hb.not_gt, lt_trichotomy, not_gt, one_lt_div, one_lt_div_of_neg, zero_le_one
-/
theorem one_lt_div_iff : 1 < a / b ↔ 0 < b ∧ b < a ∨ b < 0 ∧ a < b := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, one_lt_div_of_neg]
  · simp [zero_le_one]
  · simp [hb, hb.not_gt, one_lt_div]

/--
theorem `one_le_div_iff` / 定理 `one_le_div_iff`

English:
theorem one_le_div_iff
  statement: 1 <= a / b ↔ 0 < b ∧ b <= a ∨ b < 0 ∧ a <= b
  proof: by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, one_le_div_of_neg]
  · simp [zero_lt_one.not_ge]
  · simp [hb, hb.not_gt, one_le_div]

中文:
定理 one_le_div_iff
  结论: 1 <= a / b ↔ 0 < b ∧ b <= a ∨ b < 0 ∧ a <= b
  证明: by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, one_le_div_of_neg]
  · simp [zero_lt_one.not_ge]
  · simp [hb, hb.not_gt, one_le_div]

Depends on / 依赖: hb.not_gt, lt_trichotomy, not_ge, not_gt, one_le_div, one_le_div_of_neg, zero_lt_one, zero_lt_one.not_ge
-/
theorem one_le_div_iff : 1 <= a / b ↔ 0 < b ∧ b <= a ∨ b < 0 ∧ a <= b := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, one_le_div_of_neg]
  · simp [zero_lt_one.not_ge]
  · simp [hb, hb.not_gt, one_le_div]

/--
theorem `div_lt_one_iff` / 定理 `div_lt_one_iff`

English:
theorem div_lt_one_iff
  statement: a / b < 1 ↔ 0 < b ∧ a < b ∨ b = 0 ∨ b < 0 ∧ b < a
  proof: by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, hb.ne, div_lt_one_of_neg]
  · simp [zero_lt_one]
  · simp [hb, hb.not_gt, div_lt_one, hb.ne.symm]

中文:
定理 div_lt_one_iff
  结论: a / b < 1 ↔ 0 < b ∧ a < b ∨ b = 0 ∨ b < 0 ∧ b < a
  证明: by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, hb.ne, div_lt_one_of_neg]
  · simp [zero_lt_one]
  · simp [hb, hb.not_gt, div_lt_one, hb.ne.symm]

Depends on / 依赖: div_lt_one, div_lt_one_of_neg, hb.ne, hb.ne.symm, hb.not_gt, lt_trichotomy, not_gt, zero_lt_one
-/
theorem div_lt_one_iff : a / b < 1 ↔ 0 < b ∧ a < b ∨ b = 0 ∨ b < 0 ∧ b < a := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, hb.ne, div_lt_one_of_neg]
  · simp [zero_lt_one]
  · simp [hb, hb.not_gt, div_lt_one, hb.ne.symm]

/--
theorem `div_le_one_iff` / 定理 `div_le_one_iff`

English:
theorem div_le_one_iff
  statement: a / b <= 1 ↔ 0 < b ∧ a <= b ∨ b = 0 ∨ b < 0 ∧ b <= a
  proof: by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, hb.ne, div_le_one_of_neg]
  · simp [zero_le_one]
  · simp [hb, hb.not_gt, div_le_one, hb.ne.symm]

中文:
定理 div_le_one_iff
  结论: a / b <= 1 ↔ 0 < b ∧ a <= b ∨ b = 0 ∨ b < 0 ∧ b <= a
  证明: by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, hb.ne, div_le_one_of_neg]
  · simp [zero_le_one]
  · simp [hb, hb.not_gt, div_le_one, hb.ne.symm]

Depends on / 依赖: div_le_one, div_le_one_of_neg, hb.ne, hb.ne.symm, hb.not_gt, lt_trichotomy, not_gt, zero_le_one
-/
theorem div_le_one_iff : a / b <= 1 ↔ 0 < b ∧ a <= b ∨ b = 0 ∨ b < 0 ∧ b <= a := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, hb.ne, div_le_one_of_neg]
  · simp [zero_le_one]
  · simp [hb, hb.not_gt, div_le_one, hb.ne.symm]

/--
theorem `le_of_forall_sub_le` / 定理 `le_of_forall_sub_le`

English:
theorem le_of_forall_sub_le
  given: (h : forall ε > 0, b - ε <= a)
  statement: b <= a
  proof: by
  contrapose! h
  simpa only [@and_comm ((0 : α) < _), lt_sub_iff_add_lt, gt_iff_lt] using
    exists_add_lt_and_pos_of_lt h

中文:
定理 le_of_对任意_sub_le
  条件: (h : 对任意 ε > 0, b - ε <= a)
  结论: b <= a
  证明: by
  contrapose! h
  simpa only [@and_comm ((0 : α) < _), lt_sub_iff_add_lt, gt_iff_lt] using
    exists_add_lt_and_pos_of_lt h

Depends on / 依赖: and_comm, contrapose, exists_add_lt_and_pos_of_lt, gt_iff_lt, lt_sub_iff_add_lt
-/
theorem le_of_forall_sub_le (h : forall ε > 0, b - ε <= a) : b <= a := by
  contrapose! h
  simpa only [@and_comm ((0 : α) < _), lt_sub_iff_add_lt, gt_iff_lt] using
    exists_add_lt_and_pos_of_lt h

/--
lemma `exists_lt_mul_left_of_nonneg` / 引理 `exists_lt_mul_left_of_nonneg`

English:
lemma exists_lt_mul_left_of_nonneg
  given: {a b c : α} (ha : 0 <= a) (hc : 0 <= c) (h : c < a * b)
  proof: by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  obtain ⟨a', ha', a_a'⟩ := exists_between ((div_lt_iff₀ hb).2 h)
  exact ⟨a', ⟨(div_nonneg hc hb.le).trans ha'.le, a_a'⟩, (div_lt_iff₀ hb).1 ha'⟩

中文:
引理 存在_lt_mul_left_of_nonneg
  条件: {a b c : α} (ha : 0 <= a) (hc : 0 <= c) (h : c < a * b)
  证明: by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  obtain ⟨a', ha', a_a'⟩ := exists_between ((div_lt_iff₀ hb).2 h)
  exact ⟨a', ⟨(div_nonneg hc hb.le).trans ha'.le, a_a'⟩, (div_lt_iff₀ hb).1 ha'⟩
-/
private lemma exists_lt_mul_left_of_nonneg {a b c : α} (ha : 0 <= a) (hc : 0 <= c) (h : c < a * b) :
    exists a' in Set.Ico 0 a, c < a' * b := by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  obtain ⟨a', ha', a_a'⟩ := exists_between ((div_lt_iff₀ hb).2 h)
  exact ⟨a', ⟨(div_nonneg hc hb.le).trans ha'.le, a_a'⟩, (div_lt_iff₀ hb).1 ha'⟩

/--
lemma `exists_lt_mul_right_of_nonneg` / 引理 `exists_lt_mul_right_of_nonneg`

English:
lemma exists_lt_mul_right_of_nonneg
  given: {a b c : α} (ha : 0 <= a) (hc : 0 <= c) (h : c < a * b)
  proof: by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  simp_rw [mul_comm a] at h ⊢
  exact exists_lt_mul_left_of_nonneg hb.le hc h

中文:
引理 存在_lt_mul_right_of_nonneg
  条件: {a b c : α} (ha : 0 <= a) (hc : 0 <= c) (h : c < a * b)
  证明: by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  simp_rw [mul_comm a] at h ⊢
  exact exists_lt_mul_left_of_nonneg hb.le hc h
-/
private lemma exists_lt_mul_right_of_nonneg {a b c : α} (ha : 0 <= a) (hc : 0 <= c) (h : c < a * b) :
    exists b' in Set.Ico 0 b, c < a * b' := by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  simp_rw [mul_comm a] at h ⊢
  exact exists_lt_mul_left_of_nonneg hb.le hc h

/--
lemma `exists_mul_left_lt₀` / 引理 `exists_mul_left_lt₀`

English:
lemma exists_mul_left_lt₀
  given: {a b c : α} (hc : a * b < c)
  statement: exists a' > a, a' * b < c
  proof: by
  rcases le_or_gt b 0 with hb | hb
  · obtain ⟨a', ha'⟩ := exists_gt a
    exact ⟨a', ha', hc.trans_le' (antitone_mul_right hb ha'.le)⟩
  · obtain ⟨a', ha', hc'⟩ := exists_between ((lt_div_iff₀ hb).2 hc)
    exact ⟨a', ha', (lt_div_iff₀ hb).1 hc'⟩

中文:
引理 存在_mul_left_lt₀
  条件: {a b c : α} (hc : a * b < c)
  结论: 存在 a' > a, a' * b < c
  证明: by
  rcases le_or_gt b 0 with hb | hb
  · obtain ⟨a', ha'⟩ := exists_gt a
    exact ⟨a', ha', hc.trans_le' (antitone_mul_right hb ha'.le)⟩
  · obtain ⟨a', ha', hc'⟩ := exists_between ((lt_div_iff₀ hb).2 hc)
    exact ⟨a', ha', (lt_div_iff₀ hb).1 hc'⟩
-/
private lemma exists_mul_left_lt₀ {a b c : α} (hc : a * b < c) : exists a' > a, a' * b < c := by
  rcases le_or_gt b 0 with hb | hb
  · obtain ⟨a', ha'⟩ := exists_gt a
    exact ⟨a', ha', hc.trans_le' (antitone_mul_right hb ha'.le)⟩
  · obtain ⟨a', ha', hc'⟩ := exists_between ((lt_div_iff₀ hb).2 hc)
    exact ⟨a', ha', (lt_div_iff₀ hb).1 hc'⟩

/--
lemma `exists_mul_right_lt₀` / 引理 `exists_mul_right_lt₀`

English:
lemma exists_mul_right_lt₀
  given: {a b c : α} (hc : a * b < c)
  statement: exists b' > b, a * b' < c
  proof: by
  simp_rw [mul_comm a] at hc ⊢; exact exists_mul_left_lt₀ hc

中文:
引理 存在_mul_right_lt₀
  条件: {a b c : α} (hc : a * b < c)
  结论: 存在 b' > b, a * b' < c
  证明: by
  simp_rw [mul_comm a] at hc ⊢; exact exists_mul_left_lt₀ hc
-/
private lemma exists_mul_right_lt₀ {a b c : α} (hc : a * b < c) : exists b' > b, a * b' < c := by
  simp_rw [mul_comm a] at hc ⊢; exact exists_mul_left_lt₀ hc

/--
lemma `le_mul_of_forall_lt₀` / 引理 `le_mul_of_forall_lt₀`

English:
lemma le_mul_of_forall_lt₀
  given: {a b c : α} (h : forall a' > a, forall b' > b, c <= a' * b')
  statement: c <= a * b
  proof: by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_mul_left_lt₀ hd
  obtain ⟨b', hb', hd⟩ := exists_mul_right_lt₀ hd
  exact (h a' ha' b' hb').trans hd.le

中文:
引理 le_mul_of_对任意_lt₀
  条件: {a b c : α} (h : 对任意 a' > a, 对任意 b' > b, c <= a' * b')
  结论: c <= a * b
  证明: by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_mul_left_lt₀ hd
  obtain ⟨b', hb', hd⟩ := exists_mul_right_lt₀ hd
  exact (h a' ha' b' hb').trans hd.le

Depends on / 依赖: WithBot, WithZero, hd.le, le_of_forall_gt_imp_ge_of_dense
-/
lemma le_mul_of_forall_lt₀ {a b c : α} (h : forall a' > a, forall b' > b, c <= a' * b') : c <= a * b := by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_mul_left_lt₀ hd
  obtain ⟨b', hb', hd⟩ := exists_mul_right_lt₀ hd
  exact (h a' ha' b' hb').trans hd.le

/--
lemma `mul_le_of_forall_lt_of_nonneg` / 引理 `mul_le_of_forall_lt_of_nonneg`

English:
lemma mul_le_of_forall_lt_of_nonneg
  statement: {a b c : α} (ha : 0 <= a) (hc : 0 <= c)
  proof: by
  refine le_of_forall_lt_imp_le_of_dense fun d d_ab => ?_
  rcases lt_or_ge d 0 with hd | hd
  · exact hd.le.trans hc
  obtain ⟨a', ha', d_ab⟩ := exists_lt_mul_left_of_nonneg ha hd d_ab
  obtain ⟨b', hb', d_ab⟩ := exists_lt_mul_right_of_nonneg ha'.1 hd d_ab
  exact d_ab.le.trans (h a' ha'.1 ha'.2 b' hb'.1 hb'.2)

  -- surely there is an easier proof of this, or we already have something like it somewhere.
  -- It doesn't even need `α` to be a field, so it doesn't belong in this file.

中文:
引理 mul_le_of_对任意_lt_of_nonneg
  结论: {a b c : α} (ha : 0 <= a) (hc : 0 <= c)
  证明: by
  refine le_of_forall_lt_imp_le_of_dense fun d d_ab => ?_
  rcases lt_or_ge d 0 with hd | hd
  · exact hd.le.trans hc
  obtain ⟨a', ha', d_ab⟩ := exists_lt_mul_left_of_nonneg ha hd d_ab
  obtain ⟨b', hb', d_ab⟩ := exists_lt_mul_right_of_nonneg ha'.1 hd d_ab
  exact d_ab.le.trans (h a' ha'.1 ha'.2 b' hb'.1 hb'.2)

  -- surely there is an easier proof of this, or we already have something like it somewhere.
  -- It doesn't even need `α` to be a field, so it doesn't belong in this file.

Depends on / 依赖: d_ab, d_ab.le.trans, exists_lt_mul_left_of_nonneg, exists_lt_mul_right_of_nonneg, hd.le.trans, le_of_forall_lt_imp_le_of_dense, lt_or_ge
-/
lemma mul_le_of_forall_lt_of_nonneg {a b c : α} (ha : 0 <= a) (hc : 0 <= c)
    (h : forall a' >= 0, a' < a -> forall b' >= 0, b' < b -> a' * b' <= c) : a * b <= c := by
  refine le_of_forall_lt_imp_le_of_dense fun d d_ab => ?_
  rcases lt_or_ge d 0 with hd | hd
  · exact hd.le.trans hc
  obtain ⟨a', ha', d_ab⟩ := exists_lt_mul_left_of_nonneg ha hd d_ab
  obtain ⟨b', hb', d_ab⟩ := exists_lt_mul_right_of_nonneg ha'.1 hd d_ab
  exact d_ab.le.trans (h a' ha'.1 ha'.2 b' hb'.1 hb'.2)

  -- surely there is an easier proof of this, or we already have something like it somewhere.
  -- It doesn't even need `α` to be a field, so it doesn't belong in this file.
/--
theorem `mul_self_inj_of_nonneg` / 定理 `mul_self_inj_of_nonneg`

English:
theorem mul_self_inj_of_nonneg
  statement: {α : Type*} [CommRing α] [NoZeroDivisors α] [PartialOrder α]
  proof: by
  have := fun h => le_antisymm (neg_nonneg.mp h) b0
  grind [sq_sub_sq, mul_eq_zero, add_eq_zero_iff_eq_neg]

中文:
定理 mul_self_inj_of_nonneg
  结论: {α : 类型} [交换环 α] [无零因子 α] [偏序 α]
  证明: by
  have := fun h => le_antisymm (neg_nonneg.mp h) b0
  grind [sq_sub_sq, mul_eq_zero, add_eq_zero_iff_eq_neg]

Depends on / 依赖: add_eq_zero_iff_eq_neg, le_antisymm, mul_eq_zero, neg_nonneg, neg_nonneg.mp, sq_sub_sq
-/
theorem mul_self_inj_of_nonneg {α : Type*} [CommRing α] [NoZeroDivisors α] [PartialOrder α]
    [IsStrictOrderedRing α] {a b : α} (a0 : 0 <= a) (b0 : 0 <= b) :
    a * a = b * b ↔ a = b := by
  have := fun h => le_antisymm (neg_nonneg.mp h) b0
  grind [sq_sub_sq, mul_eq_zero, add_eq_zero_iff_eq_neg]

/--
theorem `min_div_div_right_of_nonpos` / 定理 `min_div_div_right_of_nonpos`

English:
theorem min_div_div_right_of_nonpos
  given: (hc : c <= 0) (a b : α)
  statement: min (a / c) (b / c) = max a b / c
  proof: Eq.symm Antitone.map_max fun _ _ => div_le_div_of_nonpos_of_le hc

中文:
定理 min_div_div_right_of_nonpos
  条件: (hc : c <= 0) (a b : α)
  结论: 最小值 (a / c) (b / c) = 最大值 a b / c
  证明: Eq.symm Antitone.map_max fun _ _ => div_le_div_of_nonpos_of_le hc

Depends on / 依赖: Antitone, Antitone.map_max, Eq.symm, div_le_div_of_nonpos_of_le, map_max
-/
theorem min_div_div_right_of_nonpos (hc : c <= 0) (a b : α) : min (a / c) (b / c) = max a b / c :=
Eq.symm Antitone.map_max fun _ _ => div_le_div_of_nonpos_of_le hc

/--
theorem `max_div_div_right_of_nonpos` / 定理 `max_div_div_right_of_nonpos`

English:
theorem max_div_div_right_of_nonpos
  given: (hc : c <= 0) (a b : α)
  statement: max (a / c) (b / c) = min a b / c
  proof: Eq.symm Antitone.map_min fun _ _ => div_le_div_of_nonpos_of_le hc

@[simp, grind =]

中文:
定理 max_div_div_right_of_nonpos
  条件: (hc : c <= 0) (a b : α)
  结论: 最大值 (a / c) (b / c) = 最小值 a b / c
  证明: Eq.symm Antitone.map_min fun _ _ => div_le_div_of_nonpos_of_le hc

@[simp, grind =]

Depends on / 依赖: Antitone, Antitone.map_min, Eq.symm, div_le_div_of_nonpos_of_le, map_min
-/
theorem max_div_div_right_of_nonpos (hc : c <= 0) (a b : α) : max (a / c) (b / c) = min a b / c :=
Eq.symm Antitone.map_min fun _ _ => div_le_div_of_nonpos_of_le hc

@[simp, grind =]
/--
theorem `abs_inv` / 定理 `abs_inv`

English:
theorem abs_inv
  given: (a : α)
  statement: |a⁻¹| = |a|⁻¹
  proof: map_inv₀ (absHom : α ->*₀ α) a

@[grind =]

中文:
定理 abs_inv
  条件: (a : α)
  结论: |a⁻¹| = |a|⁻¹
  证明: map_inv₀ (absHom : α ->*₀ α) a

@[grind =]

Depends on / 依赖: absHom
-/
theorem abs_inv (a : α) : |a⁻¹| = |a|⁻¹ :=
  map_inv₀ (absHom : α ->*₀ α) a

@[grind =]
/--
theorem `abs_div` / 定理 `abs_div`

English:
theorem abs_div
  given: (a b : α)
  statement: |a / b| = |a| / |b|
  proof: map_div₀ (absHom : α ->*₀ α) a b

中文:
定理 abs_div
  条件: (a b : α)
  结论: |a / b| = |a| / |b|
  证明: map_div₀ (absHom : α ->*₀ α) a b

Depends on / 依赖: absHom
-/
theorem abs_div (a b : α) : |a / b| = |a| / |b| :=
  map_div₀ (absHom : α ->*₀ α) a b

/--
theorem `abs_one_div` / 定理 `abs_one_div`

English:
theorem abs_one_div
  given: (a : α)
  statement: |1 / a| = 1 / |a|
  proof: by rw [abs_div, abs_one]

中文:
定理 abs_one_div
  条件: (a : α)
  结论: |1 / a| = 1 / |a|
  证明: by rw [abs_div, abs_one]

Depends on / 依赖: abs_div, abs_one
-/
theorem abs_one_div (a : α) : |1 / a| = 1 / |a| := by rw [abs_div, abs_one]

/--
theorem `uniform_continuous_npow_on_bounded` / 定理 `uniform_continuous_npow_on_bounded`

English:
theorem uniform_continuous_npow_on_bounded
  given: (B : α) {ε : α} (hε : 0 < ε) (n : Nat)
  proof: by
  wlog! B_pos : 0 < B generalizing B
  · have ⟨δ, δ_pos, cont⟩ := this 1 zero_lt_one
    exact ⟨δ, δ_pos, fun q r hr => cont q r (hr.trans (B_pos.trans zero_le_one))⟩
have pos : 0 < 1 + ↑n * (B + 1) ^ (n - 1) := zero_lt_one.trans_le le_add_of_nonneg_right
mul_nonneg n.cast_nonneg (pow_pos (B_pos.trans <| lt_add_of_pos_right _ zero_lt_one) _).le
  refine ⟨min 1 (ε / (1 + n * (B + 1) ^ (n - 1))), lt_min zero_lt_one (div_pos hε pos),
    fun q r hr hqr => (abs_pow_sub_pow_le ..).trans_lt ?_⟩
  rw [le_inf_iff]; rw [le_div_iff₀ pos]; rw [mul_one_add]; rw [← mul_assoc] at hqr
  obtain h | h := (abs_nonneg (q - r)).eq_or_lt
  · simpa only [← h, zero_mul] using hε
  refine (lt_of_le_of_lt ?_ <| lt_add_of_pos_left _ h).trans_le hqr.2
  gcongr
  · exact mul_nonneg (abs_nonneg _) n.cast_nonneg
  · exact (abs_nonneg _).trans le_sup_left
  refine max_le ?_ (hr.trans <| le_add_of_nonneg_right zero_le_one)
  exact add_sub_cancel r q ▸ (abs_add_le ..).trans (add_le_add hr hqr.1)

中文:
定理 uniform_continuous_npow_on_bounded
  条件: (B : α) {ε : α} (hε : 0 < ε) (n : 自然数)
  证明: by
  wlog! B_pos : 0 < B generalizing B
  · have ⟨δ, δ_pos, cont⟩ := this 1 zero_lt_one
    exact ⟨δ, δ_pos, fun q r hr => cont q r (hr.trans (B_pos.trans zero_le_one))⟩
have pos : 0 < 1 + ↑n * (B + 1) ^ (n - 1) := zero_lt_one.trans_le le_add_of_nonneg_right
mul_nonneg n.cast_nonneg (pow_pos (B_pos.trans <| lt_add_of_pos_right _ zero_lt_one) _).le
  refine ⟨min 1 (ε / (1 + n * (B + 1) ^ (n - 1))), lt_min zero_lt_one (div_pos hε pos),
    fun q r hr hqr => (abs_pow_sub_pow_le ..).trans_lt ?_⟩
  rw [le_inf_iff]; rw [le_div_iff₀ pos]; rw [mul_one_add]; rw [← mul_assoc] at hqr
  obtain h | h := (abs_nonneg (q - r)).eq_or_lt
  · simpa only [← h, zero_mul] using hε
  refine (lt_of_le_of_lt ?_ <| lt_add_of_pos_left _ h).trans_le hqr.2
  gcongr
  · exact mul_nonneg (abs_nonneg _) n.cast_nonneg
  · exact (abs_nonneg _).trans le_sup_left
  refine max_le ?_ (hr.trans <| le_add_of_nonneg_right zero_le_one)
  exact add_sub_cancel r q ▸ (abs_add_le ..).trans (add_le_add hr hqr.1)

Depends on / 依赖: B_pos, B_pos.trans, abs_pow_sub_pow_le, cast_nonneg, div_pos, generalizing, hr.trans, le_add_of_nonneg_right, le_inf_iff, lt_add_of_pos_right, lt_min, mul_nonneg, n.cast_nonneg, pow_pos, trans_le, trans_lt, zero_le_one, zero_lt_one, zero_lt_one.trans_le
-/
theorem uniform_continuous_npow_on_bounded (B : α) {ε : α} (hε : 0 < ε) (n : Nat) :
    exists δ > 0, forall q r : α, |r| <= B -> |q - r| <= δ -> |q ^ n - r ^ n| < ε := by
  wlog! B_pos : 0 < B generalizing B
  · have ⟨δ, δ_pos, cont⟩ := this 1 zero_lt_one
    exact ⟨δ, δ_pos, fun q r hr => cont q r (hr.trans (B_pos.trans zero_le_one))⟩
have pos : 0 < 1 + ↑n * (B + 1) ^ (n - 1) := zero_lt_one.trans_le le_add_of_nonneg_right
mul_nonneg n.cast_nonneg (pow_pos (B_pos.trans <| lt_add_of_pos_right _ zero_lt_one) _).le
  refine ⟨min 1 (ε / (1 + n * (B + 1) ^ (n - 1))), lt_min zero_lt_one (div_pos hε pos),
    fun q r hr hqr => (abs_pow_sub_pow_le ..).trans_lt ?_⟩
  rw [le_inf_iff]; rw [le_div_iff₀ pos]; rw [mul_one_add]; rw [← mul_assoc] at hqr
  obtain h | h := (abs_nonneg (q - r)).eq_or_lt
  · simpa only [← h, zero_mul] using hε
  refine (lt_of_le_of_lt ?_ <| lt_add_of_pos_left _ h).trans_le hqr.2
  gcongr
  · exact mul_nonneg (abs_nonneg _) n.cast_nonneg
  · exact (abs_nonneg _).trans le_sup_left
  refine max_le ?_ (hr.trans <| le_add_of_nonneg_right zero_le_one)
  exact add_sub_cancel r q ▸ (abs_add_le ..).trans (add_le_add hr hqr.1)

/--
lemma `two_mul_le_add_mul_sq` / 引理 `two_mul_le_add_mul_sq`

English:
lemma two_mul_le_add_mul_sq
  given: {ε : α} (hε : 0 < ε)
  proof: by
  have h : 2 * (ε * a) * b <= (ε * a) ^ 2 + b ^ 2 := two_mul_le_add_sq (ε * a) b
  calc 2 * a * b
  _ = 2 * a * b * (ε * ε⁻¹) := by rw [mul_inv_cancel₀ hε.ne', mul_one]
  _ = (2 * (ε * a) * b) * ε⁻¹ := by simp_rw [mul_assoc, mul_comm ε, mul_assoc]
  _ <= ((ε * a) ^ 2 + b ^ 2) * ε⁻¹ := by gcongr; exact inv_nonneg.mpr hε.le
  _ = ε * a ^ 2 + ε⁻¹ * b ^ 2 := by
    rw [mul_comm _ ε⁻¹]; rw [mul_pow]; rw [mul_add]; rw [← mul_assoc]; rw [pow_two]; rw [← mul_assoc]; rw [inv_mul_cancel₀ hε.ne']; rw [one_mul]

中文:
引理 two_mul_le_add_mul_sq
  条件: {ε : α} (hε : 0 < ε)
  证明: by
  have h : 2 * (ε * a) * b <= (ε * a) ^ 2 + b ^ 2 := two_mul_le_add_sq (ε * a) b
  calc 2 * a * b
  _ = 2 * a * b * (ε * ε⁻¹) := by rw [mul_inv_cancel₀ hε.ne', mul_one]
  _ = (2 * (ε * a) * b) * ε⁻¹ := by simp_rw [mul_assoc, mul_comm ε, mul_assoc]
  _ <= ((ε * a) ^ 2 + b ^ 2) * ε⁻¹ := by gcongr; exact inv_nonneg.mpr hε.le
  _ = ε * a ^ 2 + ε⁻¹ * b ^ 2 := by
    rw [mul_comm _ ε⁻¹]; rw [mul_pow]; rw [mul_add]; rw [← mul_assoc]; rw [pow_two]; rw [← mul_assoc]; rw [inv_mul_cancel₀ hε.ne']; rw [one_mul]

Depends on / 依赖: inv_nonneg, inv_nonneg.mpr, mul_add, mul_assoc, mul_comm, mul_one, mul_pow, one_mul, pow_two, simp_rw, two_mul_le_add_sq
-/
lemma two_mul_le_add_mul_sq {ε : α} (hε : 0 < ε) :
    2 * a * b <= ε * a ^ 2 + ε⁻¹ * b ^ 2 := by
  have h : 2 * (ε * a) * b <= (ε * a) ^ 2 + b ^ 2 := two_mul_le_add_sq (ε * a) b
  calc 2 * a * b
  _ = 2 * a * b * (ε * ε⁻¹) := by rw [mul_inv_cancel₀ hε.ne', mul_one]
  _ = (2 * (ε * a) * b) * ε⁻¹ := by simp_rw [mul_assoc, mul_comm ε, mul_assoc]
  _ <= ((ε * a) ^ 2 + b ^ 2) * ε⁻¹ := by gcongr; exact inv_nonneg.mpr hε.le
  _ = ε * a ^ 2 + ε⁻¹ * b ^ 2 := by
    rw [mul_comm _ ε⁻¹]; rw [mul_pow]; rw [mul_add]; rw [← mul_assoc]; rw [pow_two]; rw [← mul_assoc]; rw [inv_mul_cancel₀ hε.ne']; rw [one_mul]

end LinearOrderedField

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

section PositivityExt

variable {α : Type*} [GroupWithZero α] [PartialOrder α]
variable {a b : α}

/--
lemma `div_nonneg_of_pos_of_nonneg` / 引理 `div_nonneg_of_pos_of_nonneg`

English:
lemma div_nonneg_of_pos_of_nonneg
  given: [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b)
  proof: div_nonneg ha.le hb

中文:
引理 div_nonneg_of_pos_of_nonneg
  条件: [正乘反映严格偏序 α] (ha : 0 < a) (hb : 0 <= b)
  证明: div_nonneg ha.le hb

Depends on / 依赖: WithBot, WithZero, div_nonneg, ha.le, instLT
-/
lemma div_nonneg_of_pos_of_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) :
    0 <= a / b :=
  div_nonneg ha.le hb

/--
lemma `div_nonneg_of_nonneg_of_pos` / 引理 `div_nonneg_of_nonneg_of_pos`

English:
lemma div_nonneg_of_nonneg_of_pos
  given: [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b)
  proof: div_nonneg ha hb.le

中文:
引理 div_nonneg_of_nonneg_of_pos
  条件: [正乘反映严格偏序 α] (ha : 0 <= a) (hb : 0 < b)
  证明: div_nonneg ha hb.le

Depends on / 依赖: div_nonneg, hb.le
-/
lemma div_nonneg_of_nonneg_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) :
    0 <= a / b :=
  div_nonneg ha hb.le

/--
lemma `div_ne_zero_of_pos_of_ne_zero` / 引理 `div_ne_zero_of_pos_of_ne_zero`

English:
lemma div_ne_zero_of_pos_of_ne_zero
  given: (ha : 0 < a) (hb : b != 0)
  statement: a / b != 0
  proof: div_ne_zero ha.ne' hb

中文:
引理 div_ne_zero_of_pos_of_ne_zero
  条件: (ha : 0 < a) (hb : b != 0)
  结论: a / b != 0
  证明: div_ne_zero ha.ne' hb

Depends on / 依赖: div_ne_zero, ha.ne
-/
lemma div_ne_zero_of_pos_of_ne_zero (ha : 0 < a) (hb : b != 0) : a / b != 0 :=
  div_ne_zero ha.ne' hb

/--
lemma `div_ne_zero_of_ne_zero_of_pos` / 引理 `div_ne_zero_of_ne_zero_of_pos`

English:
lemma div_ne_zero_of_ne_zero_of_pos
  given: (ha : a != 0) (hb : 0 < b)
  statement: a / b != 0
  proof: div_ne_zero ha hb.ne'

中文:
引理 div_ne_zero_of_ne_zero_of_pos
  条件: (ha : a != 0) (hb : 0 < b)
  结论: a / b != 0
  证明: div_ne_zero ha hb.ne'

Depends on / 依赖: div_ne_zero, hb.ne
-/
lemma div_ne_zero_of_ne_zero_of_pos (ha : a != 0) (hb : 0 < b) : a / b != 0 :=
  div_ne_zero ha hb.ne'

/--
lemma `zpow_zero_pos` / 引理 `zpow_zero_pos`

English:
lemma zpow_zero_pos
  statement: {α : Type*} [Semifield α] [PartialOrder α] [IsStrictOrderedRing α]
  proof: zero_lt_one.trans_eq (zpow_zero a).symm

中文:
引理 zpow_zero_pos
  结论: {α : 类型} [半域 α] [偏序 α] [是StrictOrdered环 α]
  证明: zero_lt_one.trans_eq (zpow_zero a).symm

Depends on / 依赖: trans_eq, zero_lt_one, zero_lt_one.trans_eq, zpow_zero
-/
lemma zpow_zero_pos {α : Type*} [Semifield α] [PartialOrder α] [IsStrictOrderedRing α]
    (a : α) : 0 < a ^ (0 : Int) :=
  zero_lt_one.trans_eq (zpow_zero a).symm

/-- The `positivity` extension which identifies expressions of the form `a / b`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ / _] meta def evalDiv : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app (f : Q($α -> $α -> $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not /"
let _e_eq : e =Q f a b := ⟨⟩
  trace[Tactic.positivity.zeroness] "evalDiv: {a} divided by {b}"
  let _a ← synthInstanceQ q(Semifield $α)
let ⟨_f_eq⟩ ← withDefault withNewMCtxDepth assertDefEqQ q($f) q(HDiv.hDiv)
  match (dependent := true) pα? with
  | none =>
    match ← core zα pα? a, ← core zα pα? b with
    | .nonzero pa, .nonzero pb =>
      let _a ← synthInstanceQ q(GroupWithZero $α)
      assumeInstancesCommute
      pure (.nonzero q(div_ne_zero $pa $pb))
    | _, _ => pure .none
  | some pα =>
    let _a ← synthInstanceQ q(GroupWithZero $α)
    let _a ← synthInstanceQ q(PosMulReflectLT $α)
    assumeInstancesCommute
    let ra ← core zα pα a; let rb ← core zα pα b
    match ra, rb with
    | .positive pa, .positive pb => pure (.positive q(div_pos $pa $pb))
    | .positive pa, .nonnegative pb => pure (.nonnegative q(div_nonneg_of_pos_of_nonneg $pa $pb))
    | .nonnegative pa, .positive pb => pure (.nonnegative q(div_nonneg_of_nonneg_of_pos $pa $pb))
    | .nonnegative pa, .nonnegative pb => pure (.nonnegative q(div_nonneg $pa $pb))
    | .positive pa, .nonzero pb => pure (.nonzero q(div_ne_zero_of_pos_of_ne_zero $pa $pb))
    | .nonzero pa, .positive pb => pure (.nonzero q(div_ne_zero_of_ne_zero_of_pos $pa $pb))
    | .nonzero pa, .nonzero pb => pure (.nonzero q(div_ne_zero $pa $pb))
    | _, _ => pure .none

/-- The `positivity` extension which identifies expressions of the form `a⁻¹`,
such that `positivity` successfully recognises `a`. -/
@[positivity _⁻¹]
meta def evalInv : PositivityExt where eval {u α} zα pα? e := do
  let .app (f : Q($α -> $α)) (a : Q($α)) ← withReducible (whnf e) | throwError "not ⁻¹"
let _e_eq : e =Q f a := ⟨⟩
  let _a ← synthInstanceQ q(Semifield $α)
let ⟨_f_eq⟩ ← withDefault withNewMCtxDepth assertDefEqQ q($f) q(Inv.inv)
  match (dependent := true) pα? with
  | none =>
    match ← core zα pα? a with
    | .nonzero pa =>
      let _a ← synthInstanceQ q(GroupWithZero $α)
      assumeInstancesCommute
      pure (.nonzero q(inv_ne_zero $pa))
    | _ => pure .none
  | some pα =>
    let _a ← synthInstanceQ q(GroupWithZero $α)
    let _a ← synthInstanceQ q(PartialOrder $α)
    let _a ← synthInstanceQ q(PosMulReflectLT $α)
    assumeInstancesCommute
    let ra ← core zα (some pα) a
    match ra with
    | .positive pa =>
      assumeInstancesCommute
      pure (.positive q(inv_pos_of_pos $pa))
    | .nonnegative pa =>
      assumeInstancesCommute
      pure (.nonnegative q(inv_nonneg_of_nonneg $pa))
    | .nonzero pa => pure (.nonzero q(inv_ne_zero $pa))
    | .none => pure .none

/-- The `positivity` extension which identifies expressions of the form `a ^ (0:ℤ)`. -/
@[positivity _ ^ (0 : Int), Pow.pow _ (0 : Int)]
meta def evalPowZeroInt : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  let .app (.app _ (a : Q($α))) _ ← withReducible (whnf e) | throwError "not ^"
  let _a ← synthInstanceQ q(Semifield $α)
  let _a ← synthInstanceQ q(LinearOrder $α)
  let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
  assumeInstancesCommute
  let ⟨_a⟩ ← Qq.assertDefEqQ q($e) q($a ^ (0 : Int))
  pure (.positive q(zpow_zero_pos $a))

end PositivityExt

end Mathlib.Meta.Positivity
