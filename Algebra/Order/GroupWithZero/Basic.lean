/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Tactic.Monotonicity.Attr

import Mathlib.Data.Set.Function
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Util.CompileInductive

/-!
# Lemmas on the monotone multiplication typeclasses

This file builds on `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean` by proving several
lemmas that do not immediately follow from the typeclass specifications.
-/

public section

open Function

variable {α M₀ G₀ : Type*}

section MulZeroClass

variable [MulZeroClass α] {a b c d : α}

section Preorder

variable [Preorder α]

/--
theorem `Left.mul_pos` / 定理 `Left.mul_pos`

English:
theorem Left.mul_pos
  given: [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b)
  statement: 0 < a * b
  proof: by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

alias mul_pos := Left.mul_pos

中文:
定理 Left.mul_pos
  条件: [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b)
  结论: 0 < a * b
  证明: by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

alias mul_pos := Left.mul_pos

Depends on / 依赖: mul_lt_mul_of_pos_left, mul_zero
-/
theorem Left.mul_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

alias mul_pos := Left.mul_pos

/--
theorem `mul_neg_of_pos_of_neg` / 定理 `mul_neg_of_pos_of_neg`

English:
theorem mul_neg_of_pos_of_neg
  given: [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0)
  statement: a * b < 0
  proof: by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

@[simp]

中文:
定理 mul_neg_of_pos_of_neg
  条件: [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0)
  结论: a * b < 0
  证明: by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

@[simp]

Depends on / 依赖: mul_lt_mul_of_pos_left, mul_zero
-/
theorem mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

@[simp]
/--
theorem `mul_pos_iff_of_pos_left` / 定理 `mul_pos_iff_of_pos_left`

English:
theorem mul_pos_iff_of_pos_left
  given: [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < a)
  proof: by simpa using mul_lt_mul_iff_right₀ (b := 0) h

中文:
定理 mul_pos_iff_of_pos_left
  条件: [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < a)
  证明: by simpa using mul_lt_mul_iff_right₀ (b := 0) h

Depends on / 依赖: CovariantClass, Group.covconv_swap, covconv_swap
-/
theorem mul_pos_iff_of_pos_left [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < a) :
    0 < a * b ↔ 0 < b := by simpa using mul_lt_mul_iff_right₀ (b := 0) h

/--
theorem `Right.mul_pos` / 定理 `Right.mul_pos`

English:
theorem Right.mul_pos
  given: [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b)
  statement: 0 < a * b
  proof: by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

中文:
定理 Right.mul_pos
  条件: [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b)
  结论: 0 < a * b
  证明: by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

Depends on / 依赖: mul_lt_mul_of_pos_right, zero_mul
-/
theorem Right.mul_pos [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

/--
theorem `mul_neg_of_neg_of_pos` / 定理 `mul_neg_of_neg_of_pos`

English:
theorem mul_neg_of_neg_of_pos
  given: [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b)
  statement: a * b < 0
  proof: by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

@[simp]

中文:
定理 mul_neg_of_neg_of_pos
  条件: [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b)
  结论: a * b < 0
  证明: by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

@[simp]

Depends on / 依赖: mul_lt_mul_of_pos_right, zero_mul
-/
theorem mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

@[simp]
/--
theorem `mul_pos_iff_of_pos_right` / 定理 `mul_pos_iff_of_pos_right`

English:
theorem mul_pos_iff_of_pos_right
  given: [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < b)
  proof: by simpa using mul_lt_mul_iff_left₀ (b := 0) h

中文:
定理 mul_pos_iff_of_pos_right
  条件: [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < b)
  证明: by simpa using mul_lt_mul_iff_left₀ (b := 0) h
-/
theorem mul_pos_iff_of_pos_right [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < b) :
    0 < a * b ↔ 0 < a := by simpa using mul_lt_mul_iff_left₀ (b := 0) h

/--
theorem `Left.mul_nonneg` / 定理 `Left.mul_nonneg`

English:
theorem Left.mul_nonneg
  given: [PosMulMono α] (ha : 0 <= a) (hb : 0 <= b)
  statement: 0 <= a * b
  proof: by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

alias mul_nonneg := Left.mul_nonneg

中文:
定理 Left.mul_nonneg
  条件: [PosMulMono α] (ha : 0 <= a) (hb : 0 <= b)
  结论: 0 <= a * b
  证明: by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

alias mul_nonneg := Left.mul_nonneg

Depends on / 依赖: mul_le_mul_of_nonneg_left, mul_zero
-/
theorem Left.mul_nonneg [PosMulMono α] (ha : 0 <= a) (hb : 0 <= b) : 0 <= a * b := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

alias mul_nonneg := Left.mul_nonneg

/--
theorem `mul_nonpos_of_nonneg_of_nonpos` / 定理 `mul_nonpos_of_nonneg_of_nonpos`

English:
theorem mul_nonpos_of_nonneg_of_nonpos
  given: [PosMulMono α] (ha : 0 <= a) (hb : b <= 0)
  statement: a * b <= 0
  proof: by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

中文:
定理 mul_nonpos_of_nonneg_of_nonpos
  条件: [PosMulMono α] (ha : 0 <= a) (hb : b <= 0)
  结论: a * b <= 0
  证明: by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

Depends on / 依赖: mul_le_mul_of_nonneg_left, mul_zero
-/
theorem mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0 := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

/--
theorem `Right.mul_nonneg` / 定理 `Right.mul_nonneg`

English:
theorem Right.mul_nonneg
  given: [MulPosMono α] (ha : 0 <= a) (hb : 0 <= b)
  statement: 0 <= a * b
  proof: by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

中文:
定理 Right.mul_nonneg
  条件: [MulPosMono α] (ha : 0 <= a) (hb : 0 <= b)
  结论: 0 <= a * b
  证明: by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

Depends on / 依赖: mul_le_mul_of_nonneg_right, zero_mul
-/
theorem Right.mul_nonneg [MulPosMono α] (ha : 0 <= a) (hb : 0 <= b) : 0 <= a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

/--
theorem `mul_nonpos_of_nonpos_of_nonneg` / 定理 `mul_nonpos_of_nonpos_of_nonneg`

English:
theorem mul_nonpos_of_nonpos_of_nonneg
  given: [MulPosMono α] (ha : a <= 0) (hb : 0 <= b)
  statement: a * b <= 0
  proof: by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

中文:
定理 mul_nonpos_of_nonpos_of_nonneg
  条件: [MulPosMono α] (ha : a <= 0) (hb : 0 <= b)
  结论: a * b <= 0
  证明: by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

Depends on / 依赖: mul_le_mul_of_nonneg_right, zero_mul
-/
theorem mul_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0 := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

/--
theorem `pos_of_mul_pos_right` / 定理 `pos_of_mul_pos_right`

English:
theorem pos_of_mul_pos_right
  given: [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 <= a)
  statement: 0 < b
  proof: lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha

中文:
定理 pos_of_mul_pos_right
  条件: [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 <= a)
  结论: 0 < b
  证明: lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha

Depends on / 依赖: lt_of_mul_lt_mul_left, mul_zero
-/
theorem pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 <= a) : 0 < b :=
  lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha

/--
theorem `pos_of_mul_pos_left` / 定理 `pos_of_mul_pos_left`

English:
theorem pos_of_mul_pos_left
  given: [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 <= b)
  statement: 0 < a
  proof: lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb

中文:
定理 pos_of_mul_pos_left
  条件: [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 <= b)
  结论: 0 < a
  证明: lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb

Depends on / 依赖: lt_of_mul_lt_mul_right, zero_mul
-/
theorem pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 <= b) : 0 < a :=
  lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb

/--
theorem `pos_iff_pos_of_mul_pos` / 定理 `pos_iff_pos_of_mul_pos`

English:
theorem pos_iff_pos_of_mul_pos
  given: [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < a * b)
  proof: ⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩

中文:
定理 pos_iff_pos_of_mul_pos
  条件: [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < a * b)
  证明: ⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩

Depends on / 依赖: le_of_lt, pos_of_mul_pos_left, pos_of_mul_pos_right
-/
theorem pos_iff_pos_of_mul_pos [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < a * b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩

/--
theorem `Left.mul_lt_mul_of_nonneg` / 定理 `Left.mul_lt_mul_of_nonneg`

English:
theorem Left.mul_lt_mul_of_nonneg
  statement: [PosMulStrictMono α] [MulPosMono α]
  proof: mul_lt_mul_of_le_of_lt_of_nonneg_of_pos h₁.le h₂ c0 (a0.trans_lt h₁)

中文:
定理 Left.mul_lt_mul_of_nonneg
  结论: [PosMulStrictMono α] [MulPosMono α]
  证明: mul_lt_mul_of_le_of_lt_of_nonneg_of_pos h₁.le h₂ c0 (a0.trans_lt h₁)

Depends on / 依赖: a0.trans_lt, mul_lt_mul_of_le_of_lt_of_nonneg_of_pos, trans_lt
-/
theorem Left.mul_lt_mul_of_nonneg [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 <= a) (c0 : 0 <= c) : a * c < b * d :=
  mul_lt_mul_of_le_of_lt_of_nonneg_of_pos h₁.le h₂ c0 (a0.trans_lt h₁)

/--
theorem `Right.mul_lt_mul_of_nonneg` / 定理 `Right.mul_lt_mul_of_nonneg`

English:
theorem Right.mul_lt_mul_of_nonneg
  statement: [PosMulMono α] [MulPosStrictMono α]
  proof: mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h₁ h₂.le a0 (c0.trans_lt h₂)

alias mul_lt_mul_of_nonneg := Left.mul_lt_mul_of_nonneg

alias mul_lt_mul'' := Left.mul_lt_mul_of_nonneg

中文:
定理 Right.mul_lt_mul_of_nonneg
  结论: [PosMulMono α] [MulPosStrictMono α]
  证明: mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h₁ h₂.le a0 (c0.trans_lt h₂)

alias mul_lt_mul_of_nonneg := Left.mul_lt_mul_of_nonneg

alias mul_lt_mul'' := Left.mul_lt_mul_of_nonneg

Depends on / 依赖: c0.trans_lt, mul_lt_mul_of_lt_of_le_of_nonneg_of_pos, trans_lt
-/
theorem Right.mul_lt_mul_of_nonneg [PosMulMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 <= a) (c0 : 0 <= c) : a * c < b * d :=
  mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h₁ h₂.le a0 (c0.trans_lt h₂)

alias mul_lt_mul_of_nonneg := Left.mul_lt_mul_of_nonneg

alias mul_lt_mul'' := Left.mul_lt_mul_of_nonneg
attribute [gcongr] mul_lt_mul''

/--
theorem `mul_self_le_mul_self` / 定理 `mul_self_le_mul_self`

English:
theorem mul_self_le_mul_self
  given: [PosMulMono α] [MulPosMono α] (ha : 0 <= a) (hab : a <= b)
  proof: mul_le_mul hab hab ha ha.trans hab

中文:
定理 mul_self_le_mul_self
  条件: [PosMulMono α] [MulPosMono α] (ha : 0 <= a) (hab : a <= b)
  证明: mul_le_mul hab hab ha ha.trans hab

Depends on / 依赖: ha.trans, mul_le_mul
-/
theorem mul_self_le_mul_self [PosMulMono α] [MulPosMono α] (ha : 0 <= a) (hab : a <= b) :
    a * a <= b * b :=
mul_le_mul hab hab ha ha.trans hab

end Preorder

section PartialOrder

/-- Local notation for the positive elements of a type `α`. -/
local notation3 "α>0" => { x : α // 0 < x }

variable [PartialOrder α]

/--
theorem `posMulMono_iff_covariant_pos` / 定理 `posMulMono_iff_covariant_pos`

English:
theorem posMulMono_iff_covariant_pos
  proof: PosMulMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_left a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· <= ·) _ ⟨_, ha⟩ _ _ hbc }

中文:
定理 posMulMono_iff_covariant_pos
  证明: PosMulMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_left a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· <= ·) _ ⟨_, ha⟩ _ _ hbc }

Depends on / 依赖: PosMulMono, PosMulMono.to_covariantClass_pos_mul_le, to_covariantClass_pos_mul_le
-/
theorem posMulMono_iff_covariant_pos :
    PosMulMono α ↔ CovariantClass α>0 α (fun x y => x * y) (· <= ·) where
  mp _ := PosMulMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_left a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· <= ·) _ ⟨_, ha⟩ _ _ hbc }

/--
theorem `mulPosMono_iff_covariant_pos` / 定理 `mulPosMono_iff_covariant_pos`

English:
theorem mulPosMono_iff_covariant_pos
  proof: MulPosMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_right a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· <= ·) _ ⟨_, ha⟩ _ _ hbc }

中文:
定理 mulPosMono_iff_covariant_pos
  证明: MulPosMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_right a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· <= ·) _ ⟨_, ha⟩ _ _ hbc }

Depends on / 依赖: MulPosMono, MulPosMono.to_covariantClass_pos_mul_le, to_covariantClass_pos_mul_le
-/
theorem mulPosMono_iff_covariant_pos :
    MulPosMono α ↔ CovariantClass α>0 α (fun x y => y * x) (· <= ·) where
  mp _ := MulPosMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_right a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· <= ·) _ ⟨_, ha⟩ _ _ hbc }

/--
theorem `posMulReflectLT_iff_contravariant_pos` / 定理 `posMulReflectLT_iff_contravariant_pos`

English:
theorem posMulReflectLT_iff_contravariant_pos
  proof: ⟨@PosMulReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

中文:
定理 posMulReflectLT_iff_contravariant_pos
  证明: ⟨@PosMulReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

Depends on / 依赖: ContravariantClass, ContravariantClass.elim, PosMulReflectLT, PosMulReflectLT.to_contravariantClass_pos_mul_lt, a.prop.eq_or_lt, eq_or_lt, to_contravariantClass_pos_mul_lt
-/
theorem posMulReflectLT_iff_contravariant_pos :
    PosMulReflectLT α ↔ ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨@PosMulReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

/--
theorem `mulPosReflectLT_iff_contravariant_pos` / 定理 `mulPosReflectLT_iff_contravariant_pos`

English:
theorem mulPosReflectLT_iff_contravariant_pos
  proof: ⟨@MulPosReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

中文:
定理 mulPosReflectLT_iff_contravariant_pos
  证明: ⟨@MulPosReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

Depends on / 依赖: ContravariantClass, ContravariantClass.elim, MulPosReflectLT, MulPosReflectLT.to_contravariantClass_pos_mul_lt, a.prop.eq_or_lt, eq_or_lt, to_contravariantClass_pos_mul_lt
-/
theorem mulPosReflectLT_iff_contravariant_pos :
    MulPosReflectLT α ↔ ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨@MulPosReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulMono [PosMulStrictMono α] : PosMulMono α :=
  posMulMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosMono [MulPosStrictMono α] : MulPosMono α :=
  mulPosMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- see Note [lower instance priority]
instance (priority := 100) PosMulReflectLE.toPosMulReflectLT [PosMulReflectLE α] :
    PosMulReflectLT α :=
  posMulReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
(le_of_mul_le_mul_of_pos_left h.le a.2).lt_of_ne by
        rintro rfl
        simp at h⟩

-- see Note [lower instance priority]
instance (priority := 100) MulPosReflectLE.toMulPosReflectLT [MulPosReflectLE α] :
    MulPosReflectLT α :=
  mulPosReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
(le_of_mul_le_mul_of_pos_right h.le a.2).lt_of_ne by
        rintro rfl
        simp at h⟩

/--
theorem `mul_left_cancel_iff_of_pos` / 定理 `mul_left_cancel_iff_of_pos`

English:
theorem mul_left_cancel_iff_of_pos
  given: [PosMulReflectLE α] (a0 : 0 < a)
  statement: a * b = a * c ↔ b = c
  proof: ⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm
    le_of_mul_le_mul_of_pos_left h.ge a0, congr_arg _⟩

中文:
定理 mul_left_cancel_iff_of_pos
  条件: [PosMulReflectLE α] (a0 : 0 < a)
  结论: a * b = a * c ↔ b = c
  证明: ⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm
    le_of_mul_le_mul_of_pos_left h.ge a0, congr_arg _⟩

Depends on / 依赖: antisymm, congr_arg, h.ge, h.le, le_of_mul_le_mul_of_pos_left
-/
theorem mul_left_cancel_iff_of_pos [PosMulReflectLE α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm
    le_of_mul_le_mul_of_pos_left h.ge a0, congr_arg _⟩

/--
theorem `mul_right_cancel_iff_of_pos` / 定理 `mul_right_cancel_iff_of_pos`

English:
theorem mul_right_cancel_iff_of_pos
  given: [MulPosReflectLE α] (b0 : 0 < b)
  statement: a * b = c * b ↔ a = c
  proof: ⟨fun h => (le_of_mul_le_mul_of_pos_right h.le b0).antisymm
    le_of_mul_le_mul_of_pos_right h.ge b0, congr_arg (· * b)⟩

中文:
定理 mul_right_cancel_iff_of_pos
  条件: [MulPosReflectLE α] (b0 : 0 < b)
  结论: a * b = c * b ↔ a = c
  证明: ⟨fun h => (le_of_mul_le_mul_of_pos_right h.le b0).antisymm
    le_of_mul_le_mul_of_pos_right h.ge b0, congr_arg (· * b)⟩

Depends on / 依赖: antisymm, congr_arg, h.ge, h.le, le_of_mul_le_mul_of_pos_right
-/
theorem mul_right_cancel_iff_of_pos [MulPosReflectLE α] (b0 : 0 < b) : a * b = c * b ↔ a = c :=
⟨fun h => (le_of_mul_le_mul_of_pos_right h.le b0).antisymm
    le_of_mul_le_mul_of_pos_right h.ge b0, congr_arg (· * b)⟩

/--
theorem `mul_eq_mul_iff_eq_and_eq_of_pos` / 定理 `mul_eq_mul_iff_eq_and_eq_of_pos`

English:
theorem mul_eq_mul_iff_eq_and_eq_of_pos
  statement: [PosMulStrictMono α] [MulPosStrictMono α]
  proof: by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab => h.not_lt ?_, fun hcd => h.not_lt ?_⟩
  · exact (mul_le_mul_of_nonneg_left hcd a0.le).trans_lt (mul_lt_mul_of_pos_right hab d0)
  · exact (mul_lt_mul_of_pos_left hcd a0).trans_

中文:
定理 mul_eq_mul_iff_eq_and_eq_of_pos
  结论: [PosMulStrictMono α] [MulPosStrictMono α]
  证明: by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab => h.not_lt ?_, fun hcd => h.not_lt ?_⟩
  · exact (mul_le_mul_of_nonneg_left hcd a0.le).trans_lt (mul_lt_mul_of_pos_right hab d0)
  · exact (mul_lt_mul_of_pos_left hcd a0).trans_

Depends on / 依赖: a0.le, d0.le, eq_iff_le_not_lt, h.not_lt, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, mul_lt_mul_of_pos_left, mul_lt_mul_of_pos_right, not_lt, trans_le, trans_lt, true_and
-/
theorem mul_eq_mul_iff_eq_and_eq_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a <= b) (hcd : c <= d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab => h.not_lt ?_, fun hcd => h.not_lt ?_⟩
  · exact (mul_le_mul_of_nonneg_left hcd a0.le).trans_lt (mul_lt_mul_of_pos_right hab d0)
  · exact (mul_lt_mul_of_pos_left hcd a0).trans_le (mul_le_mul_of_nonneg_right hab d0.le)

/--
theorem `mul_eq_mul_iff_eq_and_eq_of_pos'` / 定理 `mul_eq_mul_iff_eq_and_eq_of_pos'`

English:
theorem mul_eq_mul_iff_eq_and_eq_of_pos'
  statement: [PosMulStrictMono α] [MulPosStrictMono α]
  proof: by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab => h.not_lt ?_, fun hcd => h.not_lt ?_⟩
  · exact (mul_lt_mul_of_pos_right hab c0).trans_le (mul_le_mul_of_nonneg_left hcd b0.le)
  · exact (mul_le_mul_of_nonneg_right hab c0.le)

中文:
定理 mul_eq_mul_iff_eq_and_eq_of_pos'
  结论: [PosMulStrictMono α] [MulPosStrictMono α]
  证明: by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab => h.not_lt ?_, fun hcd => h.not_lt ?_⟩
  · exact (mul_lt_mul_of_pos_right hab c0).trans_le (mul_le_mul_of_nonneg_left hcd b0.le)
  · exact (mul_le_mul_of_nonneg_right hab c0.le)

Depends on / 依赖: b0.le, c0.le, eq_iff_le_not_lt, h.not_lt, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, mul_lt_mul_of_pos_left, mul_lt_mul_of_pos_right, not_lt, trans_le, trans_lt, true_and
-/
theorem mul_eq_mul_iff_eq_and_eq_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a <= b) (hcd : c <= d) (b0 : 0 < b) (c0 : 0 < c) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab => h.not_lt ?_, fun hcd => h.not_lt ?_⟩
  · exact (mul_lt_mul_of_pos_right hab c0).trans_le (mul_le_mul_of_nonneg_left hcd b0.le)
  · exact (mul_le_mul_of_nonneg_right hab c0.le).trans_lt (mul_lt_mul_of_pos_left hcd b0)

/--
theorem `eq_and_eq_of_pos_of_le_of_mul_le_mul` / 定理 `eq_and_eq_of_pos_of_le_of_mul_le_mul`

English:
theorem eq_and_eq_of_pos_of_le_of_mul_le_mul
  statement: [PosMulReflectLE α] [MulPosReflectLE α]
  proof: by
  refine ⟨le_antisymm hab ?_, le_antisymm hcd ?_⟩
  · grw [hcd] at h
· exact le_of_mul_le_mul_of_pos_right h hc.trans_le hcd
    · exact ha.le
  · grw [hab] at h
· exact le_of_mul_le_mul_of_pos_left h ha.trans_le hab
    · exact hc.le

中文:
定理 eq_and_eq_of_pos_of_le_of_mul_le_mul
  结论: [PosMulReflectLE α] [MulPosReflectLE α]
  证明: by
  refine ⟨le_antisymm hab ?_, le_antisymm hcd ?_⟩
  · grw [hcd] at h
· exact le_of_mul_le_mul_of_pos_right h hc.trans_le hcd
    · exact ha.le
  · grw [hab] at h
· exact le_of_mul_le_mul_of_pos_left h ha.trans_le hab
    · exact hc.le

Depends on / 依赖: ha.le, ha.trans_le, hc.le, hc.trans_le, le_antisymm, le_of_mul_le_mul_of_pos_left, le_of_mul_le_mul_of_pos_right, trans_le
-/
theorem eq_and_eq_of_pos_of_le_of_mul_le_mul [PosMulReflectLE α] [MulPosReflectLE α]
    [PosMulMono α] [MulPosMono α] (ha : 0 < a) (hc : 0 < c) (hab : a <= b) (hcd : c <= d)
    (h : b * d <= a * c) : a = b ∧ c = d := by
  refine ⟨le_antisymm hab ?_, le_antisymm hcd ?_⟩
  · grw [hcd] at h
· exact le_of_mul_le_mul_of_pos_right h hc.trans_le hcd
    · exact ha.le
  · grw [hab] at h
· exact le_of_mul_le_mul_of_pos_left h ha.trans_le hab
    · exact hc.le

end PartialOrder

section LinearOrder

variable [LinearOrder α]

/--
theorem `pos_and_pos_or_neg_and_neg_of_mul_pos` / 定理 `pos_and_pos_or_neg_and_neg_of_mul_pos`

English:
theorem pos_and_pos_or_neg_and_neg_of_mul_pos
  given: [PosMulMono α] [MulPosMono α] (hab : 0 < a * b)
  proof: by
  rcases lt_trichotomy a 0 with (ha | rfl | ha)
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_mul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_non

中文:
定理 pos_and_pos_or_neg_and_neg_of_mul_pos
  条件: [PosMulMono α] [MulPosMono α] (hab : 0 < a * b)
  证明: by
  rcases lt_trichotomy a 0 with (ha | rfl | ha)
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_mul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_non

Depends on / 依赖: Or.inl, Or.inr, ha.le, hab.false.elim, lt_imp_lt_of_le_imp_le, lt_trichotomy, mul_nonpos_of_nonneg_of_nonpos, mul_nonpos_of_nonpos_of_nonneg, zero_mul
-/
theorem pos_and_pos_or_neg_and_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rcases lt_trichotomy a 0 with (ha | rfl | ha)
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_mul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hb

/--
theorem `neg_of_mul_pos_right` / 定理 `neg_of_mul_pos_right`

English:
theorem neg_of_mul_pos_right
  given: [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a <= 0)
  statement: b < 0
  proof: ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_ge ha).2

中文:
定理 neg_of_mul_pos_right
  条件: [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a <= 0)
  结论: b < 0
  证明: ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_ge ha).2

Depends on / 依赖: not_ge, pos_and_pos_or_neg_and_neg_of_mul_pos, resolve_left
-/
theorem neg_of_mul_pos_right [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a <= 0) : b < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_ge ha).2

/--
theorem `neg_of_mul_pos_left` / 定理 `neg_of_mul_pos_left`

English:
theorem neg_of_mul_pos_left
  given: [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b <= 0)
  statement: a < 0
  proof: ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_ge ha).1

中文:
定理 neg_of_mul_pos_left
  条件: [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b <= 0)
  结论: a < 0
  证明: ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_ge ha).1

Depends on / 依赖: not_ge, pos_and_pos_or_neg_and_neg_of_mul_pos, resolve_left
-/
theorem neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b <= 0) : a < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_ge ha).1

/--
theorem `neg_iff_neg_of_mul_pos` / 定理 `neg_iff_neg_of_mul_pos`

English:
theorem neg_iff_neg_of_mul_pos
  given: [PosMulMono α] [MulPosMono α] (hab : 0 < a * b)
  statement: a < 0 ↔ b < 0
  proof: ⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩

中文:
定理 neg_iff_neg_of_mul_pos
  条件: [PosMulMono α] [MulPosMono α] (hab : 0 < a * b)
  结论: a < 0 ↔ b < 0
  证明: ⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩

Depends on / 依赖: le_of_lt, neg_of_mul_pos_left, neg_of_mul_pos_right
-/
theorem neg_iff_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : a < 0 ↔ b < 0 :=
  ⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩

/--
theorem `Left.neg_of_mul_neg_right` / 定理 `Left.neg_of_mul_neg_right`

English:
theorem Left.neg_of_mul_neg_right
  given: [PosMulMono α] (h : a * b < 0) (a0 : 0 <= a)
  statement: b < 0
  proof: lt_of_not_ge fun b0 : b >= 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_right := Left.neg_of_mul_neg_right

中文:
定理 Left.neg_of_mul_neg_right
  条件: [PosMulMono α] (h : a * b < 0) (a0 : 0 <= a)
  结论: b < 0
  证明: lt_of_not_ge fun b0 : b >= 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_right := Left.neg_of_mul_neg_right

Depends on / 依赖: Left.mul_nonneg, lt_of_not_ge, mul_nonneg, not_gt
-/
theorem Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (a0 : 0 <= a) : b < 0 :=
  lt_of_not_ge fun b0 : b >= 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_right := Left.neg_of_mul_neg_right

/--
theorem `Right.neg_of_mul_neg_right` / 定理 `Right.neg_of_mul_neg_right`

English:
theorem Right.neg_of_mul_neg_right
  given: [MulPosMono α] (h : a * b < 0) (a0 : 0 <= a)
  statement: b < 0
  proof: lt_of_not_ge fun b0 : b >= 0 => (Right.mul_nonneg a0 b0).not_gt h

中文:
定理 Right.neg_of_mul_neg_right
  条件: [MulPosMono α] (h : a * b < 0) (a0 : 0 <= a)
  结论: b < 0
  证明: lt_of_not_ge fun b0 : b >= 0 => (Right.mul_nonneg a0 b0).not_gt h

Depends on / 依赖: Right.mul_nonneg, lt_of_not_ge, mul_nonneg, not_gt
-/
theorem Right.neg_of_mul_neg_right [MulPosMono α] (h : a * b < 0) (a0 : 0 <= a) : b < 0 :=
  lt_of_not_ge fun b0 : b >= 0 => (Right.mul_nonneg a0 b0).not_gt h

/--
theorem `Left.neg_of_mul_neg_left` / 定理 `Left.neg_of_mul_neg_left`

English:
theorem Left.neg_of_mul_neg_left
  given: [PosMulMono α] (h : a * b < 0) (b0 : 0 <= b)
  statement: a < 0
  proof: lt_of_not_ge fun a0 : a >= 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_left := Left.neg_of_mul_neg_left

中文:
定理 Left.neg_of_mul_neg_left
  条件: [PosMulMono α] (h : a * b < 0) (b0 : 0 <= b)
  结论: a < 0
  证明: lt_of_not_ge fun a0 : a >= 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_left := Left.neg_of_mul_neg_left

Depends on / 依赖: Left.mul_nonneg, lt_of_not_ge, mul_nonneg, not_gt
-/
theorem Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (b0 : 0 <= b) : a < 0 :=
  lt_of_not_ge fun a0 : a >= 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_left := Left.neg_of_mul_neg_left

/--
theorem `Right.neg_of_mul_neg_left` / 定理 `Right.neg_of_mul_neg_left`

English:
theorem Right.neg_of_mul_neg_left
  given: [MulPosMono α] (h : a * b < 0) (b0 : 0 <= b)
  statement: a < 0
  proof: lt_of_not_ge fun a0 : a >= 0 => (Right.mul_nonneg a0 b0).not_gt h

中文:
定理 Right.neg_of_mul_neg_left
  条件: [MulPosMono α] (h : a * b < 0) (b0 : 0 <= b)
  结论: a < 0
  证明: lt_of_not_ge fun a0 : a >= 0 => (Right.mul_nonneg a0 b0).not_gt h

Depends on / 依赖: Right.mul_nonneg, lt_of_not_ge, mul_nonneg, not_gt
-/
theorem Right.neg_of_mul_neg_left [MulPosMono α] (h : a * b < 0) (b0 : 0 <= b) : a < 0 :=
  lt_of_not_ge fun a0 : a >= 0 => (Right.mul_nonneg a0 b0).not_gt h

end LinearOrder

end MulZeroClass

section MulOneClass

variable [MulOneClass α] [Zero α] {a b c d : α}

section Preorder

variable [Preorder α]


/--
lemma `one_lt_of_lt_mul_left₀` / 引理 `one_lt_of_lt_mul_left₀`

English:
lemma one_lt_of_lt_mul_left₀
  given: [PosMulReflectLT α] (ha : 0 <= a) (h : a < a * b)
  statement: 1 < b
  proof: lt_of_mul_lt_mul_left (by simpa) ha

中文:
引理 one_lt_of_lt_mul_left₀
  条件: [PosMulReflectLT α] (ha : 0 <= a) (h : a < a * b)
  结论: 1 < b
  证明: lt_of_mul_lt_mul_left (by simpa) ha

Depends on / 依赖: lt_of_mul_lt_mul_left
-/
lemma one_lt_of_lt_mul_left₀ [PosMulReflectLT α] (ha : 0 <= a) (h : a < a * b) : 1 < b :=
  lt_of_mul_lt_mul_left (by simpa) ha

/--
lemma `one_lt_of_lt_mul_right₀` / 引理 `one_lt_of_lt_mul_right₀`

English:
lemma one_lt_of_lt_mul_right₀
  given: [MulPosReflectLT α] (hb : 0 <= b) (h : b < a * b)
  statement: 1 < a
  proof: lt_of_mul_lt_mul_right (by simpa) hb

中文:
引理 one_lt_of_lt_mul_right₀
  条件: [MulPosReflectLT α] (hb : 0 <= b) (h : b < a * b)
  结论: 1 < a
  证明: lt_of_mul_lt_mul_right (by simpa) hb

Depends on / 依赖: lt_of_mul_lt_mul_right
-/
lemma one_lt_of_lt_mul_right₀ [MulPosReflectLT α] (hb : 0 <= b) (h : b < a * b) : 1 < a :=
  lt_of_mul_lt_mul_right (by simpa) hb

/--
lemma `one_le_of_le_mul_left₀` / 引理 `one_le_of_le_mul_left₀`

English:
lemma one_le_of_le_mul_left₀
  given: [PosMulReflectLE α] (ha : 0 < a) (h : a <= a * b)
  statement: 1 <= b
  proof: le_of_mul_le_mul_left (by simpa) ha

中文:
引理 one_le_of_le_mul_left₀
  条件: [PosMulReflectLE α] (ha : 0 < a) (h : a <= a * b)
  结论: 1 <= b
  证明: le_of_mul_le_mul_left (by simpa) ha

Depends on / 依赖: le_of_mul_le_mul_left
-/
lemma one_le_of_le_mul_left₀ [PosMulReflectLE α] (ha : 0 < a) (h : a <= a * b) : 1 <= b :=
  le_of_mul_le_mul_left (by simpa) ha

/--
lemma `one_le_of_le_mul_right₀` / 引理 `one_le_of_le_mul_right₀`

English:
lemma one_le_of_le_mul_right₀
  given: [MulPosReflectLE α] (hb : 0 < b) (h : b <= a * b)
  statement: 1 <= a
  proof: le_of_mul_le_mul_right (by simpa) hb

@[simp]

中文:
引理 one_le_of_le_mul_right₀
  条件: [MulPosReflectLE α] (hb : 0 < b) (h : b <= a * b)
  结论: 1 <= a
  证明: le_of_mul_le_mul_right (by simpa) hb

@[simp]

Depends on / 依赖: le_of_mul_le_mul_right
-/
lemma one_le_of_le_mul_right₀ [MulPosReflectLE α] (hb : 0 < b) (h : b <= a * b) : 1 <= a :=
  le_of_mul_le_mul_right (by simpa) hb

@[simp]
/--
lemma `le_mul_iff_one_le_right` / 引理 `le_mul_iff_one_le_right`

English:
lemma le_mul_iff_one_le_right
  given: [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a)
  statement: a <= a * b ↔ 1 <= b
  proof: Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]

中文:
引理 le_mul_iff_one_le_right
  条件: [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a)
  结论: a <= a * b ↔ 1 <= b
  证明: Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]

Depends on / 依赖: Iff.trans, mul_one
-/
lemma le_mul_iff_one_le_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a <= a * b ↔ 1 <= b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]
/--
theorem `lt_mul_iff_one_lt_right` / 定理 `lt_mul_iff_one_lt_right`

English:
theorem lt_mul_iff_one_lt_right
  given: [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a)
  proof: Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

@[simp]

中文:
定理 lt_mul_iff_one_lt_right
  条件: [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a)
  证明: Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

@[simp]

Depends on / 依赖: Iff.trans, mul_one
-/
theorem lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

@[simp]
/--
lemma `mul_le_iff_le_one_right` / 引理 `mul_le_iff_le_one_right`

English:
lemma mul_le_iff_le_one_right
  given: [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a)
  statement: a * b <= a ↔ b <= 1
  proof: Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]

中文:
引理 mul_le_iff_le_one_right
  条件: [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a)
  结论: a * b <= a ↔ b <= 1
  证明: Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]

Depends on / 依赖: Iff.trans, mul_one
-/
lemma mul_le_iff_le_one_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a * b <= a ↔ b <= 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]
/--
theorem `mul_lt_iff_lt_one_right` / 定理 `mul_lt_iff_lt_one_right`

English:
theorem mul_lt_iff_lt_one_right
  given: [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a)
  proof: Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

中文:
定理 mul_lt_iff_lt_one_right
  条件: [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a)
  证明: Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

Depends on / 依赖: Iff.trans, mul_one
-/
theorem mul_lt_iff_lt_one_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`, assuming right covariance. -/

@[simp]
/--
lemma `le_mul_iff_one_le_left` / 引理 `le_mul_iff_one_le_left`

English:
lemma le_mul_iff_one_le_left
  given: [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a)
  statement: a <= b * a ↔ 1 <= b
  proof: Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ a0)

@[simp]

中文:
引理 le_mul_iff_one_le_left
  条件: [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a)
  结论: a <= b * a ↔ 1 <= b
  证明: Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ a0)

@[simp]

Depends on / 依赖: Iff.trans, one_mul
-/
lemma le_mul_iff_one_le_left [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : a <= b * a ↔ 1 <= b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ a0)

@[simp]
/--
theorem `lt_mul_iff_one_lt_left` / 定理 `lt_mul_iff_one_lt_left`

English:
theorem lt_mul_iff_one_lt_left
  given: [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a)
  proof: Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ a0)

@[simp]

中文:
定理 lt_mul_iff_one_lt_left
  条件: [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a)
  证明: Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ a0)

@[simp]

Depends on / 依赖: Iff.trans, one_mul
-/
theorem lt_mul_iff_one_lt_left [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ a0)

@[simp]
/--
lemma `mul_le_iff_le_one_left` / 引理 `mul_le_iff_le_one_left`

English:
lemma mul_le_iff_le_one_left
  given: [MulPosMono α] [MulPosReflectLE α] (b0 : 0 < b)
  statement: a * b <= b ↔ a <= 1
  proof: Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ b0)

@[simp]

中文:
引理 mul_le_iff_le_one_left
  条件: [MulPosMono α] [MulPosReflectLE α] (b0 : 0 < b)
  结论: a * b <= b ↔ a <= 1
  证明: Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ b0)

@[simp]

Depends on / 依赖: Iff.trans, one_mul
-/
lemma mul_le_iff_le_one_left [MulPosMono α] [MulPosReflectLE α] (b0 : 0 < b) : a * b <= b ↔ a <= 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ b0)

@[simp]
/--
theorem `mul_lt_iff_lt_one_left` / 定理 `mul_lt_iff_lt_one_left`

English:
theorem mul_lt_iff_lt_one_left
  given: [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < b)
  proof: Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ b0)

中文:
定理 mul_lt_iff_lt_one_left
  条件: [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < b)
  证明: Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ b0)

Depends on / 依赖: ExistsMulOfLE, Group.existsMulOfLE, Iff.trans, existsMulOfLE, one_mul
-/
theorem mul_lt_iff_lt_one_left [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < b) :
    a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ b0)


/--
theorem `mul_le_of_le_one_left` / 定理 `mul_le_of_le_one_left`

English:
theorem mul_le_of_le_one_left
  given: [MulPosMono α] (hb : 0 <= b) (h : a <= 1)
  statement: a * b <= b
  proof: by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

中文:
定理 mul_le_of_le_one_left
  条件: [MulPosMono α] (hb : 0 <= b) (h : a <= 1)
  结论: a * b <= b
  证明: by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

Depends on / 依赖: mul_le_mul_of_nonneg_right, one_mul
-/
theorem mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b) (h : a <= 1) : a * b <= b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

/--
theorem `le_mul_of_one_le_left` / 定理 `le_mul_of_one_le_left`

English:
theorem le_mul_of_one_le_left
  given: [MulPosMono α] (hb : 0 <= b) (h : 1 <= a)
  statement: b <= a * b
  proof: by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

中文:
定理 le_mul_of_one_le_left
  条件: [MulPosMono α] (hb : 0 <= b) (h : 1 <= a)
  结论: b <= a * b
  证明: by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

Depends on / 依赖: mul_le_mul_of_nonneg_right, one_mul
-/
theorem le_mul_of_one_le_left [MulPosMono α] (hb : 0 <= b) (h : 1 <= a) : b <= a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

/--
theorem `mul_le_of_le_one_right` / 定理 `mul_le_of_le_one_right`

English:
theorem mul_le_of_le_one_right
  given: [PosMulMono α] (ha : 0 <= a) (h : b <= 1)
  statement: a * b <= a
  proof: by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

中文:
定理 mul_le_of_le_one_right
  条件: [PosMulMono α] (ha : 0 <= a) (h : b <= 1)
  结论: a * b <= a
  证明: by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

Depends on / 依赖: mul_le_mul_of_nonneg_left, mul_one
-/
theorem mul_le_of_le_one_right [PosMulMono α] (ha : 0 <= a) (h : b <= 1) : a * b <= a := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

/--
theorem `le_mul_of_one_le_right` / 定理 `le_mul_of_one_le_right`

English:
theorem le_mul_of_one_le_right
  given: [PosMulMono α] (ha : 0 <= a) (h : 1 <= b)
  statement: a <= a * b
  proof: by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

中文:
定理 le_mul_of_one_le_right
  条件: [PosMulMono α] (ha : 0 <= a) (h : 1 <= b)
  结论: a <= a * b
  证明: by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

Depends on / 依赖: mul_le_mul_of_nonneg_left, mul_one
-/
theorem le_mul_of_one_le_right [PosMulMono α] (ha : 0 <= a) (h : 1 <= b) : a <= a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

/--
theorem `mul_lt_of_lt_one_left` / 定理 `mul_lt_of_lt_one_left`

English:
theorem mul_lt_of_lt_one_left
  given: [MulPosStrictMono α] (hb : 0 < b) (h : a < 1)
  statement: a * b < b
  proof: by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

中文:
定理 mul_lt_of_lt_one_left
  条件: [MulPosStrictMono α] (hb : 0 < b) (h : a < 1)
  结论: a * b < b
  证明: by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

Depends on / 依赖: mul_lt_mul_of_pos_right, one_mul
-/
theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 0 < b) (h : a < 1) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

/--
theorem `lt_mul_of_one_lt_left` / 定理 `lt_mul_of_one_lt_left`

English:
theorem lt_mul_of_one_lt_left
  given: [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a)
  statement: b < a * b
  proof: by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

中文:
定理 lt_mul_of_one_lt_left
  条件: [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a)
  结论: b < a * b
  证明: by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

Depends on / 依赖: mul_lt_mul_of_pos_right, one_mul
-/
theorem lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

/--
theorem `mul_lt_of_lt_one_right` / 定理 `mul_lt_of_lt_one_right`

English:
theorem mul_lt_of_lt_one_right
  given: [PosMulStrictMono α] (ha : 0 < a) (h : b < 1)
  statement: a * b < a
  proof: by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

中文:
定理 mul_lt_of_lt_one_right
  条件: [PosMulStrictMono α] (ha : 0 < a) (h : b < 1)
  结论: a * b < a
  证明: by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

Depends on / 依赖: mul_lt_mul_of_pos_left, mul_one
-/
theorem mul_lt_of_lt_one_right [PosMulStrictMono α] (ha : 0 < a) (h : b < 1) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

/--
theorem `lt_mul_of_one_lt_right` / 定理 `lt_mul_of_one_lt_right`

English:
theorem lt_mul_of_one_lt_right
  given: [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b)
  statement: a < a * b
  proof: by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

中文:
定理 lt_mul_of_one_lt_right
  条件: [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b)
  结论: a < a * b
  证明: by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

Depends on / 依赖: mul_lt_mul_of_pos_left, mul_one
-/
theorem lt_mul_of_one_lt_right [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

end Preorder

end MulOneClass

section MulZero

variable [Mul M₀] [Zero M₀] [Preorder M₀] [Preorder α] {f g : α -> M₀}

/--
lemma `Monotone.mul` / 引理 `Monotone.mul`

English:
lemma Monotone.mul
  statement: [PosMulMono M₀] [MulPosMono M₀] (hf : Monotone f) (hg : Monotone g)
  proof: fun _ _ h => mul_le_mul (hf h) (hg h) (hg₀ _) (hf₀ _)

中文:
引理 Monotone.mul
  结论: [PosMulMono M₀] [MulPosMono M₀] (hf : Monotone f) (hg : Monotone g)
  证明: fun _ _ h => mul_le_mul (hf h) (hg h) (hg₀ _) (hf₀ _)

Depends on / 依赖: mul_le_mul
-/
lemma Monotone.mul [PosMulMono M₀] [MulPosMono M₀] (hf : Monotone f) (hg : Monotone g)
    (hf₀ : forall x, 0 <= f x) (hg₀ : forall x, 0 <= g x) : Monotone (f * g) :=
  fun _ _ h => mul_le_mul (hf h) (hg h) (hg₀ _) (hf₀ _)

/--
lemma `MonotoneOn.mul` / 引理 `MonotoneOn.mul`

English:
lemma MonotoneOn.mul
  statement: [PosMulMono M₀] [MulPosMono M₀] {s : Set α} (hf : MonotoneOn f s)
  proof: fun _ ha _ hb h => mul_le_mul (hf ha hb h) (hg ha hb h) (hg₀ _ ha) (hf₀ _ hb)

中文:
引理 MonotoneOn.mul
  结论: [PosMulMono M₀] [MulPosMono M₀] {s : Set α} (hf : MonotoneOn f s)
  证明: fun _ ha _ hb h => mul_le_mul (hf ha hb h) (hg ha hb h) (hg₀ _ ha) (hf₀ _ hb)

Depends on / 依赖: mul_le_mul
-/
lemma MonotoneOn.mul [PosMulMono M₀] [MulPosMono M₀] {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) (hf₀ : forall x in s, 0 <= f x) (hg₀ : forall x in s, 0 <= g x) :
    MonotoneOn (f * g) s :=
  fun _ ha _ hb h => mul_le_mul (hf ha hb h) (hg ha hb h) (hg₀ _ ha) (hf₀ _ hb)

end MulZero

section MonoidWithZero
variable [MonoidWithZero M₀]

section Preorder
variable [Preorder M₀] {a b : M₀} {m n : Nat}

/--
lemma `pow_succ_nonneg` / 引理 `pow_succ_nonneg`

English:
lemma pow_succ_nonneg
  given: [PosMulMono M₀] (ha : 0 <= a)
  statement: forall n, 0 <= a ^ (n + 1)

中文:
引理 pow_succ_nonneg
  条件: [PosMulMono M₀] (ha : 0 <= a)
  结论: 对任意 n, 0 <= a ^ (n + 1)
-/
@[simp] lemma pow_succ_nonneg [PosMulMono M₀] (ha : 0 <= a) : forall n, 0 <= a ^ (n + 1)
  | 0 => (pow_one a).symm ▸ ha
  | _ + 1 => pow_succ a _ ▸ mul_nonneg (pow_succ_nonneg ha _) ha

/--
lemma `pow_nonneg` / 引理 `pow_nonneg`

English:
lemma pow_nonneg
  given: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 0 <= a)
  statement: forall n, 0 <= a ^ n

中文:
引理 pow_nonneg
  条件: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 0 <= a)
  结论: 对任意 n, 0 <= a ^ n
-/
@[simp] lemma pow_nonneg [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 0 <= a) : forall n, 0 <= a ^ n
  | 0 => pow_zero a ▸ zero_le_one
  | n + 1 => pow_succ a n ▸ mul_nonneg (pow_nonneg ha _) ha

/--
lemma `zero_pow_le_one` / 引理 `zero_pow_le_one`

English:
lemma zero_pow_le_one
  given: [ZeroLEOneClass M₀]
  statement: forall n : Nat, (0 : M₀) ^ n <= 1

中文:
引理 zero_pow_le_one
  条件: [ZeroLEOneClass M₀]
  结论: 对任意 n : 自然数, (0 : M₀) ^ n <= 1
-/
lemma zero_pow_le_one [ZeroLEOneClass M₀] : forall n : Nat, (0 : M₀) ^ n <= 1
  | 0 => (pow_zero _).le
  | n + 1 => by rw [zero_pow n.succ_ne_zero]; exact zero_le_one

/--
lemma `pow_right_anti₀` / 引理 `pow_right_anti₀`

English:
lemma pow_right_anti₀
  given: [PosMulMono M₀] (ha₀ : 0 <= a) (ha₁ : a <= 1)
  statement: Antitone (fun n : Nat => a ^ n)
  proof: antitone_nat_of_succ_le fun n => by
    have : ZeroLEOneClass M₀ := ⟨ha₀.trans ha₁⟩
    rw [← mul_one (a ^ n)]; rw [pow_succ]
    gcongr
    exact pow_nonneg ha₀ n

中文:
引理 pow_right_anti₀
  条件: [PosMulMono M₀] (ha₀ : 0 <= a) (ha₁ : a <= 1)
  结论: Antitone (fun n : 自然数 => a ^ n)
  证明: antitone_nat_of_succ_le fun n => by
    have : ZeroLEOneClass M₀ := ⟨ha₀.trans ha₁⟩
    rw [← mul_one (a ^ n)]; rw [pow_succ]
    gcongr
    exact pow_nonneg ha₀ n

Depends on / 依赖: ZeroLEOneClass, antitone_nat_of_succ_le, mul_one, pow_nonneg, pow_succ
-/
lemma pow_right_anti₀ [PosMulMono M₀] (ha₀ : 0 <= a) (ha₁ : a <= 1) : Antitone (fun n : Nat => a ^ n) :=
  antitone_nat_of_succ_le fun n => by
    have : ZeroLEOneClass M₀ := ⟨ha₀.trans ha₁⟩
    rw [← mul_one (a ^ n)]; rw [pow_succ]
    gcongr
    exact pow_nonneg ha₀ n

/--
lemma `pow_le_pow_of_le_one` / 引理 `pow_le_pow_of_le_one`

English:
lemma pow_le_pow_of_le_one
  statement: [PosMulMono M₀] (ha₀ : 0 <= a) (ha₁ : a <= 1) {m n : Nat}
  proof: pow_right_anti₀ ha₀ ha₁ hmn

中文:
引理 pow_le_pow_of_le_one
  结论: [PosMulMono M₀] (ha₀ : 0 <= a) (ha₁ : a <= 1) {m n : 自然数}
  证明: pow_right_anti₀ ha₀ ha₁ hmn
-/
lemma pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 <= a) (ha₁ : a <= 1) {m n : Nat}
    (hmn : m <= n) : a ^ n <= a ^ m := pow_right_anti₀ ha₀ ha₁ hmn

/--
lemma `pow_le_of_le_one` / 引理 `pow_le_of_le_one`

English:
lemma pow_le_of_le_one
  given: [PosMulMono M₀] (h₀ : 0 <= a) (h₁ : a <= 1) (hn : n != 0)
  statement: a ^ n <= a
  proof: (pow_one a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zero hn))

中文:
引理 pow_le_of_le_one
  条件: [PosMulMono M₀] (h₀ : 0 <= a) (h₁ : a <= 1) (hn : n != 0)
  结论: a ^ n <= a
  证明: (pow_one a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zero hn))

Depends on / 依赖: Nat.pos_of_ne_zero, pos_of_ne_zero, pow_le_pow_of_le_one, pow_one
-/
lemma pow_le_of_le_one [PosMulMono M₀] (h₀ : 0 <= a) (h₁ : a <= 1) (hn : n != 0) : a ^ n <= a :=
  (pow_one a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zero hn))

/--
lemma `sq_le` / 引理 `sq_le`

English:
lemma sq_le
  given: [PosMulMono M₀] (h₀ : 0 <= a) (h₁ : a <= 1)
  statement: a ^ 2 <= a
  proof: pow_le_of_le_one h₀ h₁ two_ne_zero

中文:
引理 sq_le
  条件: [PosMulMono M₀] (h₀ : 0 <= a) (h₁ : a <= 1)
  结论: a ^ 2 <= a
  证明: pow_le_of_le_one h₀ h₁ two_ne_zero

Depends on / 依赖: pow_le_of_le_one, two_ne_zero
-/
lemma sq_le [PosMulMono M₀] (h₀ : 0 <= a) (h₁ : a <= 1) : a ^ 2 <= a :=
  pow_le_of_le_one h₀ h₁ two_ne_zero

/--
lemma `pow_le_one₀` / 引理 `pow_le_one₀`

English:
lemma pow_le_one₀
  given: [PosMulMono M₀] {n : Nat} (ha₀ : 0 <= a) (ha₁ : a <= 1)
  statement: a ^ n <= 1
  proof: pow_zero a ▸ pow_right_anti₀ ha₀ ha₁ (Nat.zero_le n)

中文:
引理 pow_le_one₀
  条件: [PosMulMono M₀] {n : 自然数} (ha₀ : 0 <= a) (ha₁ : a <= 1)
  结论: a ^ n <= 1
  证明: pow_zero a ▸ pow_right_anti₀ ha₀ ha₁ (Nat.zero_le n)

Depends on / 依赖: Nat.zero_le, pow_zero, zero_le
-/
lemma pow_le_one₀ [PosMulMono M₀] {n : Nat} (ha₀ : 0 <= a) (ha₁ : a <= 1) : a ^ n <= 1 :=
  pow_zero a ▸ pow_right_anti₀ ha₀ ha₁ (Nat.zero_le n)

/--
lemma `one_le_mul_of_one_le_of_one_le` / 引理 `one_le_mul_of_one_le_of_one_le`

English:
lemma one_le_mul_of_one_le_of_one_le
  given: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hb : 1 <= b)
  proof: ha.trans le_mul_of_one_le_right (zero_le_one.trans ha) hb

中文:
引理 one_le_mul_of_one_le_of_one_le
  条件: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hb : 1 <= b)
  证明: ha.trans le_mul_of_one_le_right (zero_le_one.trans ha) hb

Depends on / 依赖: ha.trans, le_mul_of_one_le_right, zero_le_one, zero_le_one.trans
-/
lemma one_le_mul_of_one_le_of_one_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hb : 1 <= b) :
(1 : M₀) <= a * b := ha.trans le_mul_of_one_le_right (zero_le_one.trans ha) hb

/--
lemma `one_lt_mul_of_le_of_lt` / 引理 `one_lt_mul_of_le_of_lt`

English:
lemma one_lt_mul_of_le_of_lt
  given: [ZeroLEOneClass M₀] [MulPosMono M₀] (ha : 1 <= a) (hb : 1 < b)
  proof: hb.trans_le le_mul_of_one_le_left (zero_le_one.trans hb.le) ha

中文:
引理 one_lt_mul_of_le_of_lt
  条件: [ZeroLEOneClass M₀] [MulPosMono M₀] (ha : 1 <= a) (hb : 1 < b)
  证明: hb.trans_le le_mul_of_one_le_left (zero_le_one.trans hb.le) ha

Depends on / 依赖: hb.le, hb.trans_le, le_mul_of_one_le_left, trans_le, zero_le_one, zero_le_one.trans
-/
lemma one_lt_mul_of_le_of_lt [ZeroLEOneClass M₀] [MulPosMono M₀] (ha : 1 <= a) (hb : 1 < b) :
1 < a * b := hb.trans_le le_mul_of_one_le_left (zero_le_one.trans hb.le) ha

/--
lemma `one_lt_mul_of_lt_of_le` / 引理 `one_lt_mul_of_lt_of_le`

English:
lemma one_lt_mul_of_lt_of_le
  given: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) (hb : 1 <= b)
  proof: ha.trans_le le_mul_of_one_le_right (zero_le_one.trans ha.le) hb

alias one_lt_mul := one_lt_mul_of_le_of_lt

中文:
引理 one_lt_mul_of_lt_of_le
  条件: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) (hb : 1 <= b)
  证明: ha.trans_le le_mul_of_one_le_right (zero_le_one.trans ha.le) hb

alias one_lt_mul := one_lt_mul_of_le_of_lt

Depends on / 依赖: ha.le, ha.trans_le, le_mul_of_one_le_right, trans_le, zero_le_one, zero_le_one.trans
-/
lemma one_lt_mul_of_lt_of_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) (hb : 1 <= b) :
1 < a * b := ha.trans_le le_mul_of_one_le_right (zero_le_one.trans ha.le) hb

alias one_lt_mul := one_lt_mul_of_le_of_lt

/--
lemma `mul_lt_one_of_nonneg_of_lt_one_left` / 引理 `mul_lt_one_of_nonneg_of_lt_one_left`

English:
lemma mul_lt_one_of_nonneg_of_lt_one_left
  given: [PosMulMono M₀] (ha₀ : 0 <= a) (ha : a < 1) (hb : b <= 1)
  proof: (mul_le_of_le_one_right ha₀ hb).trans_lt ha

中文:
引理 mul_lt_one_of_nonneg_of_lt_one_left
  条件: [PosMulMono M₀] (ha₀ : 0 <= a) (ha : a < 1) (hb : b <= 1)
  证明: (mul_le_of_le_one_right ha₀ hb).trans_lt ha

Depends on / 依赖: mul_le_of_le_one_right, trans_lt
-/
lemma mul_lt_one_of_nonneg_of_lt_one_left [PosMulMono M₀] (ha₀ : 0 <= a) (ha : a < 1) (hb : b <= 1) :
    a * b < 1 := (mul_le_of_le_one_right ha₀ hb).trans_lt ha

/--
lemma `mul_lt_one_of_nonneg_of_lt_one_right` / 引理 `mul_lt_one_of_nonneg_of_lt_one_right`

English:
lemma mul_lt_one_of_nonneg_of_lt_one_right
  given: [MulPosMono M₀] (ha : a <= 1) (hb₀ : 0 <= b) (hb : b < 1)
  proof: (mul_le_of_le_one_left hb₀ ha).trans_lt hb

@[bound]

中文:
引理 mul_lt_one_of_nonneg_of_lt_one_right
  条件: [MulPosMono M₀] (ha : a <= 1) (hb₀ : 0 <= b) (hb : b < 1)
  证明: (mul_le_of_le_one_left hb₀ ha).trans_lt hb

@[bound]

Depends on / 依赖: mul_le_of_le_one_left, trans_lt
-/
lemma mul_lt_one_of_nonneg_of_lt_one_right [MulPosMono M₀] (ha : a <= 1) (hb₀ : 0 <= b) (hb : b < 1) :
    a * b < 1 := (mul_le_of_le_one_left hb₀ ha).trans_lt hb

@[bound]
/--
lemma `Bound.one_lt_mul` / 引理 `Bound.one_lt_mul`

English:
lemma Bound.one_lt_mul
  given: [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀]
  proof: by
  rintro (⟨ha, hb⟩ | ⟨ha, hb⟩); exacts [one_lt_mul ha hb, one_lt_mul_of_lt_of_le ha hb]

@[bound]

中文:
引理 Bound.one_lt_mul
  条件: [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀]
  证明: by
  rintro (⟨ha, hb⟩ | ⟨ha, hb⟩); exacts [one_lt_mul ha hb, one_lt_mul_of_lt_of_le ha hb]

@[bound]
-/
protected lemma Bound.one_lt_mul [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀] :
    1 <= a ∧ 1 < b ∨ 1 < a ∧ 1 <= b -> 1 < a * b := by
  rintro (⟨ha, hb⟩ | ⟨ha, hb⟩); exacts [one_lt_mul ha hb, one_lt_mul_of_lt_of_le ha hb]

@[bound]
/--
lemma `mul_le_one₀` / 引理 `mul_le_one₀`

English:
lemma mul_le_one₀
  given: [MulPosMono M₀] (ha : a <= 1) (hb₀ : 0 <= b) (hb : b <= 1)
  statement: a * b <= 1
  proof: (mul_le_mul_of_nonneg_right ha hb₀).trans by rwa [one_mul]

中文:
引理 mul_le_one₀
  条件: [MulPosMono M₀] (ha : a <= 1) (hb₀ : 0 <= b) (hb : b <= 1)
  结论: a * b <= 1
  证明: (mul_le_mul_of_nonneg_right ha hb₀).trans by rwa [one_mul]

Depends on / 依赖: mul_le_mul_of_nonneg_right, one_mul
-/
lemma mul_le_one₀ [MulPosMono M₀] (ha : a <= 1) (hb₀ : 0 <= b) (hb : b <= 1) : a * b <= 1 :=
(mul_le_mul_of_nonneg_right ha hb₀).trans by rwa [one_mul]

/--
lemma `pow_lt_one₀` / 引理 `pow_lt_one₀`

English:
lemma pow_lt_one₀
  given: [PosMulMono M₀] (h₀ : 0 <= a) (h₁ : a < 1)
  statement: forall {n : Nat}, n != 0 -> a ^ n < 1

中文:
引理 pow_lt_one₀
  条件: [PosMulMono M₀] (h₀ : 0 <= a) (h₁ : a < 1)
  结论: 对任意 {n : 自然数}, n != 0 -> a ^ n < 1
-/
lemma pow_lt_one₀ [PosMulMono M₀] (h₀ : 0 <= a) (h₁ : a < 1) : forall {n : Nat}, n != 0 -> a ^ n < 1
  | 0, h => (h rfl).elim
  | n + 1, _ => by
    rw [pow_succ']; exact mul_lt_one_of_nonneg_of_lt_one_left h₀ h₁ (pow_le_one₀ h₀ h₁.le)

/--
lemma `pow_right_mono₀` / 引理 `pow_right_mono₀`

English:
lemma pow_right_mono₀
  given: [ZeroLEOneClass M₀] [PosMulMono M₀] (h : 1 <= a)
  statement: Monotone (a ^ ·)
  proof: monotone_nat_of_le_succ fun n => by
    rw [pow_succ]; exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans h) _) h

中文:
引理 pow_right_mono₀
  条件: [ZeroLEOneClass M₀] [PosMulMono M₀] (h : 1 <= a)
  结论: Monotone (a ^ ·)
  证明: monotone_nat_of_le_succ fun n => by
    rw [pow_succ]; exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans h) _) h

Depends on / 依赖: le_mul_of_one_le_right, monotone_nat_of_le_succ, pow_nonneg, pow_succ, zero_le_one, zero_le_one.trans
-/
lemma pow_right_mono₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (h : 1 <= a) : Monotone (a ^ ·) :=
  monotone_nat_of_le_succ fun n => by
    rw [pow_succ]; exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans h) _) h

/--
lemma `one_le_pow₀` / 引理 `one_le_pow₀`

English:
lemma one_le_pow₀
  given: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) {n : Nat}
  statement: 1 <= a ^ n
  proof: pow_zero a ▸ pow_right_mono₀ ha n.zero_le

中文:
引理 one_le_pow₀
  条件: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) {n : 自然数}
  结论: 1 <= a ^ n
  证明: pow_zero a ▸ pow_right_mono₀ ha n.zero_le

Depends on / 依赖: n.zero_le, pow_zero, zero_le
-/
lemma one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) {n : Nat} : 1 <= a ^ n :=
  pow_zero a ▸ pow_right_mono₀ ha n.zero_le

/--
lemma `one_lt_pow₀` / 引理 `one_lt_pow₀`

English:
lemma one_lt_pow₀
  given: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a)
  statement: forall {n : Nat}, n != 0 -> 1 < a ^ n

中文:
引理 one_lt_pow₀
  条件: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a)
  结论: 对任意 {n : 自然数}, n != 0 -> 1 < a ^ n
-/
lemma one_lt_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) : forall {n : Nat}, n != 0 -> 1 < a ^ n
  | 0, h => (h rfl).elim
  | n + 1, _ => by rw [pow_succ']; exact one_lt_mul_of_lt_of_le ha (one_le_pow₀ ha.le)

/-- `bound` lemma for branching on `1 ≤ a ∨ a ≤ 1` when proving `a ^ n ≤ a ^ m` -/
@[bound]
/--
lemma `Bound.pow_le_pow_right_of_le_one_or_one_le` / 引理 `Bound.pow_le_pow_right_of_le_one_or_one_le`

English:
lemma Bound.pow_le_pow_right_of_le_one_or_one_le
  statement: [ZeroLEOneClass M₀] [PosMulMono M₀]
  proof: by
  obtain ⟨a1, nm⟩ | ⟨a0, a1, mn⟩ := h
  · exact pow_right_mono₀ a1 nm
  · exact pow_le_pow_of_le_one a0 a1 mn

@[gcongr]

中文:
引理 Bound.pow_le_pow_right_of_le_one_or_one_le
  结论: [ZeroLEOneClass M₀] [PosMulMono M₀]
  证明: by
  obtain ⟨a1, nm⟩ | ⟨a0, a1, mn⟩ := h
  · exact pow_right_mono₀ a1 nm
  · exact pow_le_pow_of_le_one a0 a1 mn

@[gcongr]

Depends on / 依赖: pow_le_pow_of_le_one
-/
lemma Bound.pow_le_pow_right_of_le_one_or_one_le [ZeroLEOneClass M₀] [PosMulMono M₀]
    (h : 1 <= a ∧ n <= m ∨ 0 <= a ∧ a <= 1 ∧ m <= n) :
    a ^ n <= a ^ m := by
  obtain ⟨a1, nm⟩ | ⟨a0, a1, mn⟩ := h
  · exact pow_right_mono₀ a1 nm
  · exact pow_le_pow_of_le_one a0 a1 mn

@[gcongr]
/--
lemma `pow_le_pow_right₀` / 引理 `pow_le_pow_right₀`

English:
lemma pow_le_pow_right₀
  given: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hmn : m <= n)
  proof: pow_right_mono₀ ha hmn

中文:
引理 pow_le_pow_right₀
  条件: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hmn : m <= n)
  证明: pow_right_mono₀ ha hmn
-/
lemma pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hmn : m <= n) :
    a ^ m <= a ^ n :=
  pow_right_mono₀ ha hmn

/--
lemma `le_self_pow₀` / 引理 `le_self_pow₀`

English:
lemma le_self_pow₀
  given: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hn : n != 0)
  statement: a <= a ^ n
  proof: by
simpa only [pow_one] using pow_le_pow_right₀ ha Nat.pos_iff_ne_zero.2 hn

中文:
引理 le_self_pow₀
  条件: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hn : n != 0)
  结论: a <= a ^ n
  证明: by
simpa only [pow_one] using pow_le_pow_right₀ ha Nat.pos_iff_ne_zero.2 hn

Depends on / 依赖: Nat.pos_iff_ne_zero, pos_iff_ne_zero, pow_one
-/
lemma le_self_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hn : n != 0) : a <= a ^ n := by
simpa only [pow_one] using pow_le_pow_right₀ ha Nat.pos_iff_ne_zero.2 hn

/-- The `bound` tactic can't handle `m ≠ 0` goals yet, so we express as `0 < m` -/
@[bound]
/--
lemma `Bound.le_self_pow_of_pos` / 引理 `Bound.le_self_pow_of_pos`

English:
lemma Bound.le_self_pow_of_pos
  given: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hn : 0 < n)
  proof: le_self_pow₀ ha hn.ne'

@[mono, gcongr, bound]

中文:
引理 Bound.le_self_pow_of_pos
  条件: [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hn : 0 < n)
  证明: le_self_pow₀ ha hn.ne'

@[mono, gcongr, bound]

Depends on / 依赖: hn.ne
-/
lemma Bound.le_self_pow_of_pos [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hn : 0 < n) :
    a <= a ^ n := le_self_pow₀ ha hn.ne'

@[mono, gcongr, bound]
/--
theorem `pow_le_pow_left₀` / 定理 `pow_le_pow_left₀`

English:
theorem pow_le_pow_left₀
  statement: [PosMulMono M₀] [MulPosMono M₀]

中文:
定理 pow_le_pow_left₀
  结论: [PosMulMono M₀] [MulPosMono M₀]
-/
theorem pow_le_pow_left₀ [PosMulMono M₀] [MulPosMono M₀]
    (ha : 0 <= a) (hab : a <= b) : forall n, a ^ n <= b ^ n
  | 0 => by simp
  | 1 => by simpa using hab
  | n + 2 => by simpa only [pow_succ']
      using mul_le_mul hab (pow_le_pow_left₀ ha hab _) (pow_succ_nonneg ha _) (ha.trans hab)

/--
lemma `pow_left_monotoneOn` / 引理 `pow_left_monotoneOn`

English:
lemma pow_left_monotoneOn
  given: [PosMulMono M₀] [MulPosMono M₀]
  proof: fun _a ha _b _ hab => pow_le_pow_left₀ ha hab _

中文:
引理 pow_left_monotoneOn
  条件: [PosMulMono M₀] [MulPosMono M₀]
  证明: fun _a ha _b _ hab => pow_le_pow_left₀ ha hab _
-/
lemma pow_left_monotoneOn [PosMulMono M₀] [MulPosMono M₀] :
    MonotoneOn (fun a : M₀ => a ^ n) {x | 0 <= x} :=
  fun _a ha _b _ hab => pow_le_pow_left₀ ha hab _

variable [Preorder α] {f g : α -> M₀}

/--
lemma `monotone_mul_left_of_nonneg` / 引理 `monotone_mul_left_of_nonneg`

English:
lemma monotone_mul_left_of_nonneg
  given: [PosMulMono M₀] (ha : 0 <= a)
  statement: Monotone fun x => a * x
  proof: fun _ _ h => mul_le_mul_of_nonneg_left h ha

中文:
引理 monotone_mul_left_of_nonneg
  条件: [PosMulMono M₀] (ha : 0 <= a)
  结论: Monotone fun x => a * x
  证明: fun _ _ h => mul_le_mul_of_nonneg_left h ha

Depends on / 依赖: mul_le_mul_of_nonneg_left
-/
lemma monotone_mul_left_of_nonneg [PosMulMono M₀] (ha : 0 <= a) : Monotone fun x => a * x :=
  fun _ _ h => mul_le_mul_of_nonneg_left h ha

/--
lemma `monotone_mul_right_of_nonneg` / 引理 `monotone_mul_right_of_nonneg`

English:
lemma monotone_mul_right_of_nonneg
  given: [MulPosMono M₀] (ha : 0 <= a)
  statement: Monotone fun x => x * a
  proof: fun _ _ h => mul_le_mul_of_nonneg_right h ha

中文:
引理 monotone_mul_right_of_nonneg
  条件: [MulPosMono M₀] (ha : 0 <= a)
  结论: Monotone fun x => x * a
  证明: fun _ _ h => mul_le_mul_of_nonneg_right h ha

Depends on / 依赖: mul_le_mul_of_nonneg_right
-/
lemma monotone_mul_right_of_nonneg [MulPosMono M₀] (ha : 0 <= a) : Monotone fun x => x * a :=
  fun _ _ h => mul_le_mul_of_nonneg_right h ha

/--
lemma `Monotone.mul_const` / 引理 `Monotone.mul_const`

English:
lemma Monotone.mul_const
  given: [MulPosMono M₀] (hf : Monotone f) (ha : 0 <= a)
  proof: (monotone_mul_right_of_nonneg ha).comp hf

中文:
引理 Monotone.mul_const
  条件: [MulPosMono M₀] (hf : Monotone f) (ha : 0 <= a)
  证明: (monotone_mul_right_of_nonneg ha).comp hf

Depends on / 依赖: monotone_mul_right_of_nonneg
-/
lemma Monotone.mul_const [MulPosMono M₀] (hf : Monotone f) (ha : 0 <= a) :
    Monotone fun x => f x * a := (monotone_mul_right_of_nonneg ha).comp hf

/--
lemma `Monotone.const_mul` / 引理 `Monotone.const_mul`

English:
lemma Monotone.const_mul
  given: [PosMulMono M₀] (hf : Monotone f) (ha : 0 <= a)
  proof: (monotone_mul_left_of_nonneg ha).comp hf

中文:
引理 Monotone.const_mul
  条件: [PosMulMono M₀] (hf : Monotone f) (ha : 0 <= a)
  证明: (monotone_mul_left_of_nonneg ha).comp hf

Depends on / 依赖: monotone_mul_left_of_nonneg
-/
lemma Monotone.const_mul [PosMulMono M₀] (hf : Monotone f) (ha : 0 <= a) :
    Monotone fun x => a * f x := (monotone_mul_left_of_nonneg ha).comp hf

/--
lemma `Antitone.mul_const` / 引理 `Antitone.mul_const`

English:
lemma Antitone.mul_const
  given: [MulPosMono M₀] (hf : Antitone f) (ha : 0 <= a)
  proof: (monotone_mul_right_of_nonneg ha).comp_antitone hf

中文:
引理 Antitone.mul_const
  条件: [MulPosMono M₀] (hf : Antitone f) (ha : 0 <= a)
  证明: (monotone_mul_right_of_nonneg ha).comp_antitone hf

Depends on / 依赖: comp_antitone, monotone_mul_right_of_nonneg
-/
lemma Antitone.mul_const [MulPosMono M₀] (hf : Antitone f) (ha : 0 <= a) :
    Antitone fun x => f x * a := (monotone_mul_right_of_nonneg ha).comp_antitone hf

/--
lemma `Antitone.const_mul` / 引理 `Antitone.const_mul`

English:
lemma Antitone.const_mul
  given: [PosMulMono M₀] (hf : Antitone f) (ha : 0 <= a)
  proof: (monotone_mul_left_of_nonneg ha).comp_antitone hf

中文:
引理 Antitone.const_mul
  条件: [PosMulMono M₀] (hf : Antitone f) (ha : 0 <= a)
  证明: (monotone_mul_left_of_nonneg ha).comp_antitone hf

Depends on / 依赖: comp_antitone, monotone_mul_left_of_nonneg
-/
lemma Antitone.const_mul [PosMulMono M₀] (hf : Antitone f) (ha : 0 <= a) :
    Antitone fun x => a * f x := (monotone_mul_left_of_nonneg ha).comp_antitone hf

end Preorder

section PartialOrder
variable [PartialOrder M₀] {a b c d : M₀} {m n : Nat}

/--
lemma `mul_self_lt_mul_self` / 引理 `mul_self_lt_mul_self`

English:
lemma mul_self_lt_mul_self
  given: [PosMulStrictMono M₀] [MulPosMono M₀] (ha : 0 <= a) (hab : a < b)
  proof: mul_lt_mul' hab.le hab ha ha.trans_lt hab

中文:
引理 mul_self_lt_mul_self
  条件: [PosMulStrictMono M₀] [MulPosMono M₀] (ha : 0 <= a) (hab : a < b)
  证明: mul_lt_mul' hab.le hab ha ha.trans_lt hab

Depends on / 依赖: ha.trans_lt, hab.le, mul_lt_mul, trans_lt
-/
lemma mul_self_lt_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] (ha : 0 <= a) (hab : a < b) :
a * a < b * b := mul_lt_mul' hab.le hab ha ha.trans_lt hab

-- In the next lemma, we used to write `Set.Ici 0` instead of `{x | 0 ≤ x}`.
-- As this lemma is not used outside this file,
-- and the import for `Set.Ici` is not otherwise needed until later,
-- we choose not to use it here.
/--
lemma `strictMonoOn_mul_self` / 引理 `strictMonoOn_mul_self`

English:
lemma strictMonoOn_mul_self
  given: [PosMulStrictMono M₀] [MulPosMono M₀]
  proof: fun _ hx _ _ hxy => mul_self_lt_mul_self hx hxy

中文:
引理 strictMonoOn_mul_self
  条件: [PosMulStrictMono M₀] [MulPosMono M₀]
  证明: fun _ hx _ _ hxy => mul_self_lt_mul_self hx hxy

Depends on / 依赖: mul_self_lt_mul_self
-/
lemma strictMonoOn_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] :
    StrictMonoOn (fun x => x * x) {x : M₀ | 0 <= x} := fun _ hx _ _ hxy => mul_self_lt_mul_self hx hxy

-- See Note [decidable namespace]
/--
lemma `Decidable.mul_lt_mul''` / 引理 `Decidable.mul_lt_mul''`

English:
lemma Decidable.mul_lt_mul''
  statement: [PosMulMono M₀] [PosMulStrictMono M₀] [MulPosStrictMono M₀]
  proof: h4.lt_or_eq_dec.elim (fun b0 => mul_lt_mul h1 h2.le b0 <| h3.trans h1.le) fun b0 => by
    rw [← b0]; rw [mul_zero]; exact mul_pos (h3.trans_lt h1) (h4.trans_lt h2)

中文:
引理 Decidable.mul_lt_mul''
  结论: [PosMulMono M₀] [PosMulStrictMono M₀] [MulPosStrictMono M₀]
  证明: h4.lt_or_eq_dec.elim (fun b0 => mul_lt_mul h1 h2.le b0 <| h3.trans h1.le) fun b0 => by
    rw [← b0]; rw [mul_zero]; exact mul_pos (h3.trans_lt h1) (h4.trans_lt h2)
-/
protected lemma Decidable.mul_lt_mul'' [PosMulMono M₀] [PosMulStrictMono M₀] [MulPosStrictMono M₀]
    [DecidableLE M₀] (h1 : a < c) (h2 : b < d) (h3 : 0 <= a) (h4 : 0 <= b) : a * b < c * d :=
  h4.lt_or_eq_dec.elim (fun b0 => mul_lt_mul h1 h2.le b0 <| h3.trans h1.le) fun b0 => by
    rw [← b0]; rw [mul_zero]; exact mul_pos (h3.trans_lt h1) (h4.trans_lt h2)

/--
lemma `lt_mul_left` / 引理 `lt_mul_left`

English:
lemma lt_mul_left
  given: [MulPosStrictMono M₀] (ha : 0 < a) (hb : 1 < b)
  statement: a < b * a
  proof: by
  simpa using mul_lt_mul_of_pos_right hb ha

中文:
引理 lt_mul_left
  条件: [MulPosStrictMono M₀] (ha : 0 < a) (hb : 1 < b)
  结论: a < b * a
  证明: by
  simpa using mul_lt_mul_of_pos_right hb ha

Depends on / 依赖: mul_lt_mul_of_pos_right
-/
lemma lt_mul_left [MulPosStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < b * a := by
  simpa using mul_lt_mul_of_pos_right hb ha

/--
lemma `lt_mul_right` / 引理 `lt_mul_right`

English:
lemma lt_mul_right
  given: [PosMulStrictMono M₀] (ha : 0 < a) (hb : 1 < b)
  statement: a < a * b
  proof: by
  simpa using mul_lt_mul_of_pos_left hb ha

中文:
引理 lt_mul_right
  条件: [PosMulStrictMono M₀] (ha : 0 < a) (hb : 1 < b)
  结论: a < a * b
  证明: by
  simpa using mul_lt_mul_of_pos_left hb ha

Depends on / 依赖: mul_lt_mul_of_pos_left
-/
lemma lt_mul_right [PosMulStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < a * b := by
  simpa using mul_lt_mul_of_pos_left hb ha

/--
lemma `lt_mul_self` / 引理 `lt_mul_self`

English:
lemma lt_mul_self
  given: [ZeroLEOneClass M₀] [MulPosStrictMono M₀] (ha : 1 < a)
  statement: a < a * a
  proof: lt_mul_left (ha.trans_le' zero_le_one) ha

中文:
引理 lt_mul_self
  条件: [ZeroLEOneClass M₀] [MulPosStrictMono M₀] (ha : 1 < a)
  结论: a < a * a
  证明: lt_mul_left (ha.trans_le' zero_le_one) ha

Depends on / 依赖: ha.trans_le, lt_mul_left, trans_le, zero_le_one
-/
lemma lt_mul_self [ZeroLEOneClass M₀] [MulPosStrictMono M₀] (ha : 1 < a) : a < a * a :=
  lt_mul_left (ha.trans_le' zero_le_one) ha

/--
lemma `sq_pos_of_pos` / 引理 `sq_pos_of_pos`

English:
lemma sq_pos_of_pos
  given: [PosMulStrictMono M₀] (ha : 0 < a)
  statement: 0 < a ^ 2
  proof: by
  simpa only [sq] using mul_pos ha ha

中文:
引理 sq_pos_of_pos
  条件: [PosMulStrictMono M₀] (ha : 0 < a)
  结论: 0 < a ^ 2
  证明: by
  simpa only [sq] using mul_pos ha ha

Depends on / 依赖: mul_pos
-/
lemma sq_pos_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : 0 < a ^ 2 := by
  simpa only [sq] using mul_pos ha ha

section strict_mono
variable [PosMulStrictMono M₀]

/--
lemma `pow_succ_pos` / 引理 `pow_succ_pos`

English:
lemma pow_succ_pos
  given: (ha : 0 < a)
  statement: forall n, 0 < a ^ (n + 1)

中文:
引理 pow_succ_pos
  条件: (ha : 0 < a)
  结论: 对任意 n, 0 < a ^ (n + 1)
-/
@[simp] lemma pow_succ_pos (ha : 0 < a) : forall n, 0 < a ^ (n + 1)
  | 0 => by simpa using ha
  | _ + 1 => pow_succ a _ ▸ mul_pos (pow_succ_pos ha _) ha

/--
lemma `pow_pos` / 引理 `pow_pos`

English:
lemma pow_pos
  given: [ZeroLEOneClass M₀] (ha : 0 < a)
  statement: forall n, 0 < a ^ n

中文:
引理 pow_pos
  条件: [ZeroLEOneClass M₀] (ha : 0 < a)
  结论: 对任意 n, 0 < a ^ n
-/
@[simp] lemma pow_pos [ZeroLEOneClass M₀] (ha : 0 < a) : forall n, 0 < a ^ n
  | 0 => by nontriviality; rw [pow_zero]; exact zero_lt_one
  | _ + 1 => pow_succ a _ ▸ mul_pos (pow_pos ha _) ha

@[gcongr, bound]
/--
lemma `pow_lt_pow_left₀` / 引理 `pow_lt_pow_left₀`

English:
lemma pow_lt_pow_left₀
  statement: [MulPosMono M₀] (hab : a < b)

中文:
引理 pow_lt_pow_left₀
  结论: [MulPosMono M₀] (hab : a < b)
-/
lemma pow_lt_pow_left₀ [MulPosMono M₀] (hab : a < b)
    (ha : 0 <= a) : forall {n : Nat}, n != 0 -> a ^ n < b ^ n
  | 1, _ => by simpa using hab
  | n + 2, _ => by
    simpa only [pow_succ] using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
      (pow_le_pow_left₀ ha hab.le _) hab ha (pow_succ_pos (ha.trans_lt hab) _)

/--
lemma `pow_left_strictMonoOn₀` / 引理 `pow_left_strictMonoOn₀`

English:
lemma pow_left_strictMonoOn₀
  given: [MulPosMono M₀] (hn : n != 0)
  proof: fun _a ha _b _ hab => pow_lt_pow_left₀ hab ha hn

中文:
引理 pow_left_strictMonoOn₀
  条件: [MulPosMono M₀] (hn : n != 0)
  证明: fun _a ha _b _ hab => pow_lt_pow_left₀ hab ha hn
-/
lemma pow_left_strictMonoOn₀ [MulPosMono M₀] (hn : n != 0) :
    StrictMonoOn (· ^ n : M₀ -> M₀) {a | 0 <= a} :=
  fun _a ha _b _ hab => pow_lt_pow_left₀ hab ha hn

section ZeroLEOneClass

variable [ZeroLEOneClass M₀]

/--
lemma `pow_right_strictMono₀` / 引理 `pow_right_strictMono₀`

English:
lemma pow_right_strictMono₀
  given: (h : 1 < a)
  statement: StrictMono (a ^ ·)
  proof: strictMono_nat_of_lt_succ fun n => by
    simpa only [one_mul, pow_succ] using lt_mul_right (pow_pos (zero_le_one.trans_lt h) _) h

@[gcongr]

中文:
引理 pow_right_strictMono₀
  条件: (h : 1 < a)
  结论: StrictMono (a ^ ·)
  证明: strictMono_nat_of_lt_succ fun n => by
    simpa only [one_mul, pow_succ] using lt_mul_right (pow_pos (zero_le_one.trans_lt h) _) h

@[gcongr]

Depends on / 依赖: lt_mul_right, one_mul, pow_pos, pow_succ, strictMono_nat_of_lt_succ, trans_lt, zero_le_one, zero_le_one.trans_lt
-/
lemma pow_right_strictMono₀ (h : 1 < a) : StrictMono (a ^ ·) :=
  strictMono_nat_of_lt_succ fun n => by
    simpa only [one_mul, pow_succ] using lt_mul_right (pow_pos (zero_le_one.trans_lt h) _) h

@[gcongr]
/--
lemma `pow_lt_pow_right₀` / 引理 `pow_lt_pow_right₀`

English:
lemma pow_lt_pow_right₀
  given: (h : 1 < a) (hmn : m < n)
  statement: a ^ m < a ^ n
  proof: pow_right_strictMono₀ h hmn

中文:
引理 pow_lt_pow_right₀
  条件: (h : 1 < a) (hmn : m < n)
  结论: a ^ m < a ^ n
  证明: pow_right_strictMono₀ h hmn
-/
lemma pow_lt_pow_right₀ (h : 1 < a) (hmn : m < n) : a ^ m < a ^ n := pow_right_strictMono₀ h hmn

/--
lemma `pow_lt_pow_iff_right₀` / 引理 `pow_lt_pow_iff_right₀`

English:
lemma pow_lt_pow_iff_right₀
  given: (h : 1 < a)
  statement: a ^ n < a ^ m ↔ n < m
  proof: (pow_right_strictMono₀ h).lt_iff_lt

中文:
引理 pow_lt_pow_iff_right₀
  条件: (h : 1 < a)
  结论: a ^ n < a ^ m ↔ n < m
  证明: (pow_right_strictMono₀ h).lt_iff_lt

Depends on / 依赖: lt_iff_lt
-/
lemma pow_lt_pow_iff_right₀ (h : 1 < a) : a ^ n < a ^ m ↔ n < m :=
  (pow_right_strictMono₀ h).lt_iff_lt

/--
lemma `pow_le_pow_iff_right₀` / 引理 `pow_le_pow_iff_right₀`

English:
lemma pow_le_pow_iff_right₀
  given: (h : 1 < a)
  statement: a ^ n <= a ^ m ↔ n <= m
  proof: (pow_right_strictMono₀ h).le_iff_le

中文:
引理 pow_le_pow_iff_right₀
  条件: (h : 1 < a)
  结论: a ^ n <= a ^ m ↔ n <= m
  证明: (pow_right_strictMono₀ h).le_iff_le

Depends on / 依赖: le_iff_le
-/
lemma pow_le_pow_iff_right₀ (h : 1 < a) : a ^ n <= a ^ m ↔ n <= m :=
  (pow_right_strictMono₀ h).le_iff_le

/--
lemma `lt_self_pow₀` / 引理 `lt_self_pow₀`

English:
lemma lt_self_pow₀
  given: (h : 1 < a) (hm : 1 < m)
  statement: a < a ^ m
  proof: by
  simpa only [pow_one] using pow_lt_pow_right₀ h hm

中文:
引理 lt_self_pow₀
  条件: (h : 1 < a) (hm : 1 < m)
  结论: a < a ^ m
  证明: by
  simpa only [pow_one] using pow_lt_pow_right₀ h hm

Depends on / 依赖: pow_one
-/
lemma lt_self_pow₀ (h : 1 < a) (hm : 1 < m) : a < a ^ m := by
  simpa only [pow_one] using pow_lt_pow_right₀ h hm

end ZeroLEOneClass

/--
lemma `pow_right_strictAnti₀` / 引理 `pow_right_strictAnti₀`

English:
lemma pow_right_strictAnti₀
  given: (h₀ : 0 < a) (h₁ : a < 1)
  statement: StrictAnti (a ^ ·)
  proof: strictAnti_nat_of_succ_lt fun n => by
    have : ZeroLEOneClass M₀ := ⟨(h₀.trans h₁).le⟩
    simpa only [pow_succ, mul_one] using mul_lt_mul_of_pos_left h₁ (pow_pos h₀ n)

中文:
引理 pow_right_strictAnti₀
  条件: (h₀ : 0 < a) (h₁ : a < 1)
  结论: StrictAnti (a ^ ·)
  证明: strictAnti_nat_of_succ_lt fun n => by
    have : ZeroLEOneClass M₀ := ⟨(h₀.trans h₁).le⟩
    simpa only [pow_succ, mul_one] using mul_lt_mul_of_pos_left h₁ (pow_pos h₀ n)

Depends on / 依赖: ZeroLEOneClass, mul_lt_mul_of_pos_left, mul_one, pow_pos, pow_succ, strictAnti_nat_of_succ_lt
-/
lemma pow_right_strictAnti₀ (h₀ : 0 < a) (h₁ : a < 1) : StrictAnti (a ^ ·) :=
  strictAnti_nat_of_succ_lt fun n => by
    have : ZeroLEOneClass M₀ := ⟨(h₀.trans h₁).le⟩
    simpa only [pow_succ, mul_one] using mul_lt_mul_of_pos_left h₁ (pow_pos h₀ n)

/--
lemma `pow_le_pow_iff_right_of_lt_one₀` / 引理 `pow_le_pow_iff_right_of_lt_one₀`

English:
lemma pow_le_pow_iff_right_of_lt_one₀
  given: (ha₀ : 0 < a) (ha₁ : a < 1)
  statement: a ^ m <= a ^ n ↔ n <= m
  proof: (pow_right_strictAnti₀ ha₀ ha₁).le_iff_ge

中文:
引理 pow_le_pow_iff_right_of_lt_one₀
  条件: (ha₀ : 0 < a) (ha₁ : a < 1)
  结论: a ^ m <= a ^ n ↔ n <= m
  证明: (pow_right_strictAnti₀ ha₀ ha₁).le_iff_ge

Depends on / 依赖: le_iff_ge
-/
lemma pow_le_pow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ m <= a ^ n ↔ n <= m :=
  (pow_right_strictAnti₀ ha₀ ha₁).le_iff_ge

/--
lemma `pow_lt_pow_iff_right_of_lt_one₀` / 引理 `pow_lt_pow_iff_right_of_lt_one₀`

English:
lemma pow_lt_pow_iff_right_of_lt_one₀
  given: (h₀ : 0 < a) (h₁ : a < 1)
  statement: a ^ m < a ^ n ↔ n < m
  proof: (pow_right_strictAnti₀ h₀ h₁).lt_iff_gt

中文:
引理 pow_lt_pow_iff_right_of_lt_one₀
  条件: (h₀ : 0 < a) (h₁ : a < 1)
  结论: a ^ m < a ^ n ↔ n < m
  证明: (pow_right_strictAnti₀ h₀ h₁).lt_iff_gt

Depends on / 依赖: lt_iff_gt
-/
lemma pow_lt_pow_iff_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) : a ^ m < a ^ n ↔ n < m :=
  (pow_right_strictAnti₀ h₀ h₁).lt_iff_gt

/--
lemma `pow_lt_pow_right_of_lt_one₀` / 引理 `pow_lt_pow_right_of_lt_one₀`

English:
lemma pow_lt_pow_right_of_lt_one₀
  given: (h₀ : 0 < a) (h₁ : a < 1) (hmn : m < n)
  statement: a ^ n < a ^ m
  proof: (pow_lt_pow_iff_right_of_lt_one₀ h₀ h₁).2 hmn

中文:
引理 pow_lt_pow_right_of_lt_one₀
  条件: (h₀ : 0 < a) (h₁ : a < 1) (hmn : m < n)
  结论: a ^ n < a ^ m
  证明: (pow_lt_pow_iff_right_of_lt_one₀ h₀ h₁).2 hmn
-/
lemma pow_lt_pow_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  (pow_lt_pow_iff_right_of_lt_one₀ h₀ h₁).2 hmn

/--
lemma `pow_lt_self_of_lt_one₀` / 引理 `pow_lt_self_of_lt_one₀`

English:
lemma pow_lt_self_of_lt_one₀
  given: (h₀ : 0 < a) (h₁ : a < 1) (hn : 1 < n)
  statement: a ^ n < a
  proof: by
  simpa only [pow_one] using pow_lt_pow_right_of_lt_one₀ h₀ h₁ hn

中文:
引理 pow_lt_self_of_lt_one₀
  条件: (h₀ : 0 < a) (h₁ : a < 1) (hn : 1 < n)
  结论: a ^ n < a
  证明: by
  simpa only [pow_one] using pow_lt_pow_right_of_lt_one₀ h₀ h₁ hn

Depends on / 依赖: pow_one
-/
lemma pow_lt_self_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) (hn : 1 < n) : a ^ n < a := by
  simpa only [pow_one] using pow_lt_pow_right_of_lt_one₀ h₀ h₁ hn

end strict_mono

variable [Preorder α] {f g : α -> M₀}

/--
lemma `strictMono_mul_left_of_pos` / 引理 `strictMono_mul_left_of_pos`

English:
lemma strictMono_mul_left_of_pos
  given: [PosMulStrictMono M₀] (ha : 0 < a)
  proof: fun _ _ b_lt_c => mul_lt_mul_of_pos_left b_lt_c ha

中文:
引理 strictMono_mul_left_of_pos
  条件: [PosMulStrictMono M₀] (ha : 0 < a)
  证明: fun _ _ b_lt_c => mul_lt_mul_of_pos_left b_lt_c ha

Depends on / 依赖: b_lt_c, mul_lt_mul_of_pos_left
-/
lemma strictMono_mul_left_of_pos [PosMulStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x => a * x := fun _ _ b_lt_c => mul_lt_mul_of_pos_left b_lt_c ha

/--
lemma `strictMono_mul_right_of_pos` / 引理 `strictMono_mul_right_of_pos`

English:
lemma strictMono_mul_right_of_pos
  given: [MulPosStrictMono M₀] (ha : 0 < a)
  proof: fun _ _ b_lt_c => mul_lt_mul_of_pos_right b_lt_c ha

中文:
引理 strictMono_mul_right_of_pos
  条件: [MulPosStrictMono M₀] (ha : 0 < a)
  证明: fun _ _ b_lt_c => mul_lt_mul_of_pos_right b_lt_c ha

Depends on / 依赖: b_lt_c, mul_lt_mul_of_pos_right
-/
lemma strictMono_mul_right_of_pos [MulPosStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x => x * a := fun _ _ b_lt_c => mul_lt_mul_of_pos_right b_lt_c ha

/--
lemma `StrictMono.mul_const` / 引理 `StrictMono.mul_const`

English:
lemma StrictMono.mul_const
  given: [MulPosStrictMono M₀] (hf : StrictMono f) (ha : 0 < a)
  proof: (strictMono_mul_right_of_pos ha).comp hf

中文:
引理 StrictMono.mul_const
  条件: [MulPosStrictMono M₀] (hf : StrictMono f) (ha : 0 < a)
  证明: (strictMono_mul_right_of_pos ha).comp hf

Depends on / 依赖: strictMono_mul_right_of_pos
-/
lemma StrictMono.mul_const [MulPosStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x => f x * a := (strictMono_mul_right_of_pos ha).comp hf

/--
lemma `StrictMono.const_mul` / 引理 `StrictMono.const_mul`

English:
lemma StrictMono.const_mul
  given: [PosMulStrictMono M₀] (hf : StrictMono f) (ha : 0 < a)
  proof: (strictMono_mul_left_of_pos ha).comp hf

中文:
引理 StrictMono.const_mul
  条件: [PosMulStrictMono M₀] (hf : StrictMono f) (ha : 0 < a)
  证明: (strictMono_mul_left_of_pos ha).comp hf

Depends on / 依赖: strictMono_mul_left_of_pos
-/
lemma StrictMono.const_mul [PosMulStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x => a * f x := (strictMono_mul_left_of_pos ha).comp hf

/--
lemma `StrictAnti.mul_const` / 引理 `StrictAnti.mul_const`

English:
lemma StrictAnti.mul_const
  given: [MulPosStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a)
  proof: (strictMono_mul_right_of_pos ha).comp_strictAnti hf

中文:
引理 StrictAnti.mul_const
  条件: [MulPosStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a)
  证明: (strictMono_mul_right_of_pos ha).comp_strictAnti hf

Depends on / 依赖: comp_strictAnti, strictMono_mul_right_of_pos
-/
lemma StrictAnti.mul_const [MulPosStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x => f x * a := (strictMono_mul_right_of_pos ha).comp_strictAnti hf

/--
lemma `StrictAnti.const_mul` / 引理 `StrictAnti.const_mul`

English:
lemma StrictAnti.const_mul
  given: [PosMulStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a)
  proof: (strictMono_mul_left_of_pos ha).comp_strictAnti hf

中文:
引理 StrictAnti.const_mul
  条件: [PosMulStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a)
  证明: (strictMono_mul_left_of_pos ha).comp_strictAnti hf

Depends on / 依赖: comp_strictAnti, strictMono_mul_left_of_pos
-/
lemma StrictAnti.const_mul [PosMulStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x => a * f x := (strictMono_mul_left_of_pos ha).comp_strictAnti hf

/--
lemma `StrictMono.mul_monotone` / 引理 `StrictMono.mul_monotone`

English:
lemma StrictMono.mul_monotone
  statement: [PosMulMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
  proof: fun _ _ h => mul_lt_mul (hf h) (hg h.le) (hg₀ _) (hf₀ _)

中文:
引理 StrictMono.mul_monotone
  结论: [PosMulMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
  证明: fun _ _ h => mul_lt_mul (hf h) (hg h.le) (hg₀ _) (hf₀ _)

Depends on / 依赖: h.le, mul_lt_mul
-/
lemma StrictMono.mul_monotone [PosMulMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : Monotone g) (hf₀ : forall x, 0 <= f x) (hg₀ : forall x, 0 < g x) :
    StrictMono (f * g) := fun _ _ h => mul_lt_mul (hf h) (hg h.le) (hg₀ _) (hf₀ _)

/--
lemma `Monotone.mul_strictMono` / 引理 `Monotone.mul_strictMono`

English:
lemma Monotone.mul_strictMono
  statement: [PosMulStrictMono M₀] [MulPosMono M₀] (hf : Monotone f)
  proof: fun _ _ h => mul_lt_mul' (hf h.le) (hg h) (hg₀ _) (hf₀ _)

中文:
引理 Monotone.mul_strictMono
  结论: [PosMulStrictMono M₀] [MulPosMono M₀] (hf : Monotone f)
  证明: fun _ _ h => mul_lt_mul' (hf h.le) (hg h) (hg₀ _) (hf₀ _)

Depends on / 依赖: h.le, mul_lt_mul
-/
lemma Monotone.mul_strictMono [PosMulStrictMono M₀] [MulPosMono M₀] (hf : Monotone f)
    (hg : StrictMono g) (hf₀ : forall x, 0 < f x) (hg₀ : forall x, 0 <= g x) :
    StrictMono (f * g) := fun _ _ h => mul_lt_mul' (hf h.le) (hg h) (hg₀ _) (hf₀ _)

/--
lemma `StrictMono.mul` / 引理 `StrictMono.mul`

English:
lemma StrictMono.mul
  statement: [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
  proof: fun _ _ h => mul_lt_mul'' (hf h) (hg h) (hf₀ _) (hg₀ _)

中文:
引理 StrictMono.mul
  结论: [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
  证明: fun _ _ h => mul_lt_mul'' (hf h) (hg h) (hf₀ _) (hg₀ _)

Depends on / 依赖: mul_lt_mul
-/
lemma StrictMono.mul [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : StrictMono g) (hf₀ : forall x, 0 <= f x) (hg₀ : forall x, 0 <= g x) :
    StrictMono (f * g) := fun _ _ h => mul_lt_mul'' (hf h) (hg h) (hf₀ _) (hg₀ _)

end PartialOrder

section LinearOrder
variable [LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀}
  {m n : Nat}

/--
lemma `pow_le_pow_iff_left₀` / 引理 `pow_le_pow_iff_left₀`

English:
lemma pow_le_pow_iff_left₀
  given: [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b) (hn : n != 0)
  proof: (pow_left_strictMonoOn₀ hn).le_iff_le ha hb

中文:
引理 pow_le_pow_iff_left₀
  条件: [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b) (hn : n != 0)
  证明: (pow_left_strictMonoOn₀ hn).le_iff_le ha hb

Depends on / 依赖: le_iff_le
-/
lemma pow_le_pow_iff_left₀ [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b) (hn : n != 0) :
    a ^ n <= b ^ n ↔ a <= b :=
  (pow_left_strictMonoOn₀ hn).le_iff_le ha hb

/--
lemma `pow_lt_pow_iff_left₀` / 引理 `pow_lt_pow_iff_left₀`

English:
lemma pow_lt_pow_iff_left₀
  given: [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b) (hn : n != 0)
  proof: (pow_left_strictMonoOn₀ hn).lt_iff_lt ha hb

@[simp]

中文:
引理 pow_lt_pow_iff_left₀
  条件: [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b) (hn : n != 0)
  证明: (pow_left_strictMonoOn₀ hn).lt_iff_lt ha hb

@[simp]

Depends on / 依赖: lt_iff_lt
-/
lemma pow_lt_pow_iff_left₀ [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b) (hn : n != 0) :
    a ^ n < b ^ n ↔ a < b :=
  (pow_left_strictMonoOn₀ hn).lt_iff_lt ha hb

@[simp]
/--
lemma `pow_left_inj₀` / 引理 `pow_left_inj₀`

English:
lemma pow_left_inj₀
  given: [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b) (hn : n != 0)
  proof: (pow_left_strictMonoOn₀ hn).eq_iff_eq ha hb

中文:
引理 pow_left_inj₀
  条件: [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b) (hn : n != 0)
  证明: (pow_left_strictMonoOn₀ hn).eq_iff_eq ha hb

Depends on / 依赖: eq_iff_eq
-/
lemma pow_left_inj₀ [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b) (hn : n != 0) :
    a ^ n = b ^ n ↔ a = b :=
  (pow_left_strictMonoOn₀ hn).eq_iff_eq ha hb

section ZeroLEOneClass

variable [ZeroLEOneClass M₀]

/--
lemma `pow_right_injective₀` / 引理 `pow_right_injective₀`

English:
lemma pow_right_injective₀
  given: (ha₀ : 0 < a) (ha₁ : a != 1)
  statement: Injective (a ^ ·)
  proof: by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (pow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (pow_right_strictMono₀ ha₁).injective

@[simp]

中文:
引理 pow_right_injective₀
  条件: (ha₀ : 0 < a) (ha₁ : a != 1)
  结论: Injective (a ^ ·)
  证明: by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (pow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (pow_right_strictMono₀ ha₁).injective

@[simp]

Depends on / 依赖: injective, lt_or_gt
-/
lemma pow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a != 1) : Injective (a ^ ·) := by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (pow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (pow_right_strictMono₀ ha₁).injective

@[simp]
/--
lemma `pow_right_inj₀` / 引理 `pow_right_inj₀`

English:
lemma pow_right_inj₀
  given: (ha₀ : 0 < a) (ha₁ : a != 1)
  statement: a ^ m = a ^ n ↔ m = n
  proof: (pow_right_injective₀ ha₀ ha₁).eq_iff

中文:
引理 pow_right_inj₀
  条件: (ha₀ : 0 < a) (ha₁ : a != 1)
  结论: a ^ m = a ^ n ↔ m = n
  证明: (pow_right_injective₀ ha₀ ha₁).eq_iff

Depends on / 依赖: eq_iff
-/
lemma pow_right_inj₀ (ha₀ : 0 < a) (ha₁ : a != 1) : a ^ m = a ^ n ↔ m = n :=
  (pow_right_injective₀ ha₀ ha₁).eq_iff

/--
lemma `pow_le_one_iff_of_nonneg` / 引理 `pow_le_one_iff_of_nonneg`

English:
lemma pow_le_one_iff_of_nonneg
  given: (ha : 0 <= a) (hn : n != 0)
  statement: a ^ n <= 1 ↔ a <= 1
  proof: by
  refine ⟨fun h => ?_, pow_le_one₀ ha⟩
  contrapose! h
  exact one_lt_pow₀ h hn

中文:
引理 pow_le_one_iff_of_nonneg
  条件: (ha : 0 <= a) (hn : n != 0)
  结论: a ^ n <= 1 ↔ a <= 1
  证明: by
  refine ⟨fun h => ?_, pow_le_one₀ ha⟩
  contrapose! h
  exact one_lt_pow₀ h hn

Depends on / 依赖: contrapose
-/
lemma pow_le_one_iff_of_nonneg (ha : 0 <= a) (hn : n != 0) : a ^ n <= 1 ↔ a <= 1 := by
  refine ⟨fun h => ?_, pow_le_one₀ ha⟩
  contrapose! h
  exact one_lt_pow₀ h hn

/--
lemma `one_le_pow_iff_of_nonneg` / 引理 `one_le_pow_iff_of_nonneg`

English:
lemma one_le_pow_iff_of_nonneg
  given: (ha : 0 <= a) (hn : n != 0)
  statement: 1 <= a ^ n ↔ 1 <= a
  proof: by
  refine ⟨fun h => ?_, fun h => one_le_pow₀ h⟩
  contrapose! h
  exact pow_lt_one₀ ha h hn

中文:
引理 one_le_pow_iff_of_nonneg
  条件: (ha : 0 <= a) (hn : n != 0)
  结论: 1 <= a ^ n ↔ 1 <= a
  证明: by
  refine ⟨fun h => ?_, fun h => one_le_pow₀ h⟩
  contrapose! h
  exact pow_lt_one₀ ha h hn

Depends on / 依赖: contrapose
-/
lemma one_le_pow_iff_of_nonneg (ha : 0 <= a) (hn : n != 0) : 1 <= a ^ n ↔ 1 <= a := by
  refine ⟨fun h => ?_, fun h => one_le_pow₀ h⟩
  contrapose! h
  exact pow_lt_one₀ ha h hn

/--
lemma `pow_lt_one_iff_of_nonneg` / 引理 `pow_lt_one_iff_of_nonneg`

English:
lemma pow_lt_one_iff_of_nonneg
  given: (ha : 0 <= a) (hn : n != 0)
  statement: a ^ n < 1 ↔ a < 1
  proof: lt_iff_lt_of_le_iff_le (one_le_pow_iff_of_nonneg ha hn)

中文:
引理 pow_lt_one_iff_of_nonneg
  条件: (ha : 0 <= a) (hn : n != 0)
  结论: a ^ n < 1 ↔ a < 1
  证明: lt_iff_lt_of_le_iff_le (one_le_pow_iff_of_nonneg ha hn)

Depends on / 依赖: lt_iff_lt_of_le_iff_le, one_le_pow_iff_of_nonneg
-/
lemma pow_lt_one_iff_of_nonneg (ha : 0 <= a) (hn : n != 0) : a ^ n < 1 ↔ a < 1 :=
  lt_iff_lt_of_le_iff_le (one_le_pow_iff_of_nonneg ha hn)

/--
lemma `one_lt_pow_iff_of_nonneg` / 引理 `one_lt_pow_iff_of_nonneg`

English:
lemma one_lt_pow_iff_of_nonneg
  given: (ha : 0 <= a) (hn : n != 0)
  statement: 1 < a ^ n ↔ 1 < a
  proof: by
  simp only [← not_le, pow_le_one_iff_of_nonneg ha hn]

中文:
引理 one_lt_pow_iff_of_nonneg
  条件: (ha : 0 <= a) (hn : n != 0)
  结论: 1 < a ^ n ↔ 1 < a
  证明: by
  simp only [← not_le, pow_le_one_iff_of_nonneg ha hn]

Depends on / 依赖: not_le, pow_le_one_iff_of_nonneg
-/
lemma one_lt_pow_iff_of_nonneg (ha : 0 <= a) (hn : n != 0) : 1 < a ^ n ↔ 1 < a := by
  simp only [← not_le, pow_le_one_iff_of_nonneg ha hn]

/--
lemma `pow_eq_one_iff_of_nonneg` / 引理 `pow_eq_one_iff_of_nonneg`

English:
lemma pow_eq_one_iff_of_nonneg
  given: (ha : 0 <= a) (hn : n != 0)
  statement: a ^ n = 1 ↔ a = 1
  proof: by
  simp only [le_antisymm_iff, pow_le_one_iff_of_nonneg ha hn, one_le_pow_iff_of_nonneg ha hn]

中文:
引理 pow_eq_one_iff_of_nonneg
  条件: (ha : 0 <= a) (hn : n != 0)
  结论: a ^ n = 1 ↔ a = 1
  证明: by
  simp only [le_antisymm_iff, pow_le_one_iff_of_nonneg ha hn, one_le_pow_iff_of_nonneg ha hn]

Depends on / 依赖: le_antisymm_iff, one_le_pow_iff_of_nonneg, pow_le_one_iff_of_nonneg
-/
lemma pow_eq_one_iff_of_nonneg (ha : 0 <= a) (hn : n != 0) : a ^ n = 1 ↔ a = 1 := by
  simp only [le_antisymm_iff, pow_le_one_iff_of_nonneg ha hn, one_le_pow_iff_of_nonneg ha hn]

/--
lemma `sq_le_one_iff₀` / 引理 `sq_le_one_iff₀`

English:
lemma sq_le_one_iff₀
  given: (ha : 0 <= a)
  statement: a ^ 2 <= 1 ↔ a <= 1
  proof: pow_le_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

中文:
引理 sq_le_one_iff₀
  条件: (ha : 0 <= a)
  结论: a ^ 2 <= 1 ↔ a <= 1
  证明: pow_le_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

Depends on / 依赖: Nat.succ_ne_zero, pow_le_one_iff_of_nonneg, succ_ne_zero
-/
lemma sq_le_one_iff₀ (ha : 0 <= a) : a ^ 2 <= 1 ↔ a <= 1 :=
  pow_le_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

/--
lemma `sq_lt_one_iff₀` / 引理 `sq_lt_one_iff₀`

English:
lemma sq_lt_one_iff₀
  given: (ha : 0 <= a)
  statement: a ^ 2 < 1 ↔ a < 1
  proof: pow_lt_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

中文:
引理 sq_lt_one_iff₀
  条件: (ha : 0 <= a)
  结论: a ^ 2 < 1 ↔ a < 1
  证明: pow_lt_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

Depends on / 依赖: Nat.succ_ne_zero, pow_lt_one_iff_of_nonneg, succ_ne_zero
-/
lemma sq_lt_one_iff₀ (ha : 0 <= a) : a ^ 2 < 1 ↔ a < 1 :=
  pow_lt_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

/--
lemma `one_le_sq_iff₀` / 引理 `one_le_sq_iff₀`

English:
lemma one_le_sq_iff₀
  given: (ha : 0 <= a)
  statement: 1 <= a ^ 2 ↔ 1 <= a
  proof: one_le_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

中文:
引理 one_le_sq_iff₀
  条件: (ha : 0 <= a)
  结论: 1 <= a ^ 2 ↔ 1 <= a
  证明: one_le_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

Depends on / 依赖: Nat.succ_ne_zero, one_le_pow_iff_of_nonneg, succ_ne_zero
-/
lemma one_le_sq_iff₀ (ha : 0 <= a) : 1 <= a ^ 2 ↔ 1 <= a :=
  one_le_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

/--
lemma `one_lt_sq_iff₀` / 引理 `one_lt_sq_iff₀`

English:
lemma one_lt_sq_iff₀
  given: (ha : 0 <= a)
  statement: 1 < a ^ 2 ↔ 1 < a
  proof: one_lt_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

中文:
引理 one_lt_sq_iff₀
  条件: (ha : 0 <= a)
  结论: 1 < a ^ 2 ↔ 1 < a
  证明: one_lt_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

Depends on / 依赖: Nat.succ_ne_zero, one_lt_pow_iff_of_nonneg, succ_ne_zero
-/
lemma one_lt_sq_iff₀ (ha : 0 <= a) : 1 < a ^ 2 ↔ 1 < a :=
  one_lt_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

end ZeroLEOneClass

variable [MulPosMono M₀]

/--
lemma `lt_of_pow_lt_pow_left₀` / 引理 `lt_of_pow_lt_pow_left₀`

English:
lemma lt_of_pow_lt_pow_left₀
  given: (n : Nat) (hb : 0 <= b) (h : a ^ n < b ^ n)
  statement: a < b
  proof: lt_of_not_ge fun hn => not_lt_of_ge (pow_le_pow_left₀ hb hn _) h

中文:
引理 lt_of_pow_lt_pow_left₀
  条件: (n : 自然数) (hb : 0 <= b) (h : a ^ n < b ^ n)
  结论: a < b
  证明: lt_of_not_ge fun hn => not_lt_of_ge (pow_le_pow_left₀ hb hn _) h

Depends on / 依赖: lt_of_not_ge, not_lt_of_ge
-/
lemma lt_of_pow_lt_pow_left₀ (n : Nat) (hb : 0 <= b) (h : a ^ n < b ^ n) : a < b :=
  lt_of_not_ge fun hn => not_lt_of_ge (pow_le_pow_left₀ hb hn _) h

/--
lemma `le_of_pow_le_pow_left₀` / 引理 `le_of_pow_le_pow_left₀`

English:
lemma le_of_pow_le_pow_left₀
  given: (hn : n != 0) (hb : 0 <= b) (h : a ^ n <= b ^ n)
  statement: a <= b
  proof: le_of_not_gt fun h1 => not_le_of_gt (pow_lt_pow_left₀ h1 hb hn) h

中文:
引理 le_of_pow_le_pow_left₀
  条件: (hn : n != 0) (hb : 0 <= b) (h : a ^ n <= b ^ n)
  结论: a <= b
  证明: le_of_not_gt fun h1 => not_le_of_gt (pow_lt_pow_left₀ h1 hb hn) h

Depends on / 依赖: le_of_not_gt, not_le_of_gt
-/
lemma le_of_pow_le_pow_left₀ (hn : n != 0) (hb : 0 <= b) (h : a ^ n <= b ^ n) : a <= b :=
  le_of_not_gt fun h1 => not_le_of_gt (pow_lt_pow_left₀ h1 hb hn) h

/--
lemma `sq_eq_sq₀` / 引理 `sq_eq_sq₀`

English:
lemma sq_eq_sq₀
  given: (ha : 0 <= a) (hb : 0 <= b)
  statement: a ^ 2 = b ^ 2 ↔ a = b
  proof: by
  simp [ha, hb]

中文:
引理 sq_eq_sq₀
  条件: (ha : 0 <= a) (hb : 0 <= b)
  结论: a ^ 2 = b ^ 2 ↔ a = b
  证明: by
  simp [ha, hb]
-/
lemma sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b := by
  simp [ha, hb]

/--
lemma `lt_of_mul_self_lt_mul_self₀` / 引理 `lt_of_mul_self_lt_mul_self₀`

English:
lemma lt_of_mul_self_lt_mul_self₀
  given: (hb : 0 <= b)
  statement: a * a < b * b -> a < b
  proof: by
  simp only [← sq]
  exact lt_of_pow_lt_pow_left₀ _ hb

中文:
引理 lt_of_mul_self_lt_mul_self₀
  条件: (hb : 0 <= b)
  结论: a * a < b * b -> a < b
  证明: by
  simp only [← sq]
  exact lt_of_pow_lt_pow_left₀ _ hb
-/
lemma lt_of_mul_self_lt_mul_self₀ (hb : 0 <= b) : a * a < b * b -> a < b := by
  simp only [← sq]
  exact lt_of_pow_lt_pow_left₀ _ hb

/--
lemma `sq_lt_sq₀` / 引理 `sq_lt_sq₀`

English:
lemma sq_lt_sq₀
  given: (ha : 0 <= a) (hb : 0 <= b)
  statement: a ^ 2 < b ^ 2 ↔ a < b
  proof: pow_lt_pow_iff_left₀ ha hb two_ne_zero

中文:
引理 sq_lt_sq₀
  条件: (ha : 0 <= a) (hb : 0 <= b)
  结论: a ^ 2 < b ^ 2 ↔ a < b
  证明: pow_lt_pow_iff_left₀ ha hb two_ne_zero

Depends on / 依赖: two_ne_zero
-/
lemma sq_lt_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 < b ^ 2 ↔ a < b :=
  pow_lt_pow_iff_left₀ ha hb two_ne_zero

/--
lemma `sq_le_sq₀` / 引理 `sq_le_sq₀`

English:
lemma sq_le_sq₀
  given: (ha : 0 <= a) (hb : 0 <= b)
  statement: a ^ 2 <= b ^ 2 ↔ a <= b
  proof: pow_le_pow_iff_left₀ ha hb two_ne_zero

中文:
引理 sq_le_sq₀
  条件: (ha : 0 <= a) (hb : 0 <= b)
  结论: a ^ 2 <= b ^ 2 ↔ a <= b
  证明: pow_le_pow_iff_left₀ ha hb two_ne_zero

Depends on / 依赖: two_ne_zero
-/
lemma sq_le_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 <= b ^ 2 ↔ a <= b :=
  pow_le_pow_iff_left₀ ha hb two_ne_zero

end MonoidWithZero.LinearOrder

section CancelMonoidWithZero

variable [MonoidWithZero α]

section PartialOrder

variable [PartialOrder α]

/--
theorem `PosMulMono.toPosMulStrictMono` / 定理 `PosMulMono.toPosMulStrictMono`

English:
theorem PosMulMono.toPosMulStrictMono
  given: [IsLeftCancelMulZero α] [PosMulMono α]
  proof: (mul_le_mul_of_nonneg_left hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_left_cancel₀ ha.ne')

中文:
定理 PosMulMono.toPosMulStrictMono
  条件: [IsLeftCancelMulZero α] [PosMulMono α]
  证明: (mul_le_mul_of_nonneg_left hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_left_cancel₀ ha.ne')

Depends on / 依赖: ha.le, ha.ne, hbc.le, hbc.ne, lt_of_ne, mul_le_mul_of_nonneg_left
-/
theorem PosMulMono.toPosMulStrictMono [IsLeftCancelMulZero α] [PosMulMono α] :
    PosMulStrictMono α where
  mul_lt_mul_of_pos_left _a ha _b _c hbc :=
    (mul_le_mul_of_nonneg_left hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_left_cancel₀ ha.ne')

/--
theorem `posMulMono_iff_posMulStrictMono` / 定理 `posMulMono_iff_posMulStrictMono`

English:
theorem posMulMono_iff_posMulStrictMono
  given: [IsLeftCancelMulZero α]
  proof: ⟨(·.toPosMulStrictMono), (·.toPosMulMono)⟩

中文:
定理 posMulMono_iff_posMulStrictMono
  条件: [IsLeftCancelMulZero α]
  证明: ⟨(·.toPosMulStrictMono), (·.toPosMulMono)⟩

Depends on / 依赖: toPosMulMono, toPosMulStrictMono
-/
theorem posMulMono_iff_posMulStrictMono [IsLeftCancelMulZero α] :
    PosMulMono α ↔ PosMulStrictMono α :=
  ⟨(·.toPosMulStrictMono), (·.toPosMulMono)⟩

/--
theorem `MulPosMono.toMulPosStrictMono` / 定理 `MulPosMono.toMulPosStrictMono`

English:
theorem MulPosMono.toMulPosStrictMono
  given: [IsRightCancelMulZero α] [MulPosMono α]
  proof: (mul_le_mul_of_nonneg_right hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_right_cancel₀ ha.ne')

中文:
定理 MulPosMono.toMulPosStrictMono
  条件: [IsRightCancelMulZero α] [MulPosMono α]
  证明: (mul_le_mul_of_nonneg_right hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_right_cancel₀ ha.ne')

Depends on / 依赖: ha.le, ha.ne, hbc.le, hbc.ne, lt_of_ne, mul_le_mul_of_nonneg_right
-/
theorem MulPosMono.toMulPosStrictMono [IsRightCancelMulZero α] [MulPosMono α] :
    MulPosStrictMono α where
  mul_lt_mul_of_pos_right _a ha _b _c hbc :=
    (mul_le_mul_of_nonneg_right hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_right_cancel₀ ha.ne')

/--
theorem `mulPosMono_iff_mulPosStrictMono` / 定理 `mulPosMono_iff_mulPosStrictMono`

English:
theorem mulPosMono_iff_mulPosStrictMono
  given: [IsRightCancelMulZero α]
  proof: ⟨(·.toMulPosStrictMono), (·.toMulPosMono)⟩

中文:
定理 mulPosMono_iff_mulPosStrictMono
  条件: [IsRightCancelMulZero α]
  证明: ⟨(·.toMulPosStrictMono), (·.toMulPosMono)⟩

Depends on / 依赖: toMulPosMono, toMulPosStrictMono
-/
theorem mulPosMono_iff_mulPosStrictMono [IsRightCancelMulZero α] :
    MulPosMono α ↔ MulPosStrictMono α :=
  ⟨(·.toMulPosStrictMono), (·.toMulPosMono)⟩

/--
theorem `PosMulReflectLT.toPosMulReflectLE` / 定理 `PosMulReflectLT.toPosMulReflectLE`

English:
theorem PosMulReflectLT.toPosMulReflectLE
  given: [IsLeftCancelMulZero α] [PosMulReflectLT α]
  proof: fun x _ _ h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.ne.symm) fun h' =>
      (lt_of_mul_lt_mul_left h' x.2.le).le

中文:
定理 PosMulReflectLT.toPosMulReflectLE
  条件: [IsLeftCancelMulZero α] [PosMulReflectLT α]
  证明: fun x _ _ h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.ne.symm) fun h' =>
      (lt_of_mul_lt_mul_left h' x.2.le).le
-/
theorem PosMulReflectLT.toPosMulReflectLE [IsLeftCancelMulZero α] [PosMulReflectLT α] :
    PosMulReflectLE α where
  elim := fun x _ _ h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.ne.symm) fun h' =>
      (lt_of_mul_lt_mul_left h' x.2.le).le

/--
theorem `posMulReflectLE_iff_posMulReflectLT` / 定理 `posMulReflectLE_iff_posMulReflectLT`

English:
theorem posMulReflectLE_iff_posMulReflectLT
  given: [IsLeftCancelMulZero α]
  proof: ⟨(·.toPosMulReflectLT), (·.toPosMulReflectLE)⟩

中文:
定理 posMulReflectLE_iff_posMulReflectLT
  条件: [IsLeftCancelMulZero α]
  证明: ⟨(·.toPosMulReflectLT), (·.toPosMulReflectLE)⟩

Depends on / 依赖: toPosMulReflectLE, toPosMulReflectLT
-/
theorem posMulReflectLE_iff_posMulReflectLT [IsLeftCancelMulZero α] :
    PosMulReflectLE α ↔ PosMulReflectLT α :=
  ⟨(·.toPosMulReflectLT), (·.toPosMulReflectLE)⟩

/--
theorem `MulPosReflectLT.toMulPosReflectLE` / 定理 `MulPosReflectLT.toMulPosReflectLE`

English:
theorem MulPosReflectLT.toMulPosReflectLE
  given: [IsRightCancelMulZero α] [MulPosReflectLT α]
  proof: fun x _ _ h => h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm) fun h' =>
    (lt_of_mul_lt_mul_right h' x.2.le).le

中文:
定理 MulPosReflectLT.toMulPosReflectLE
  条件: [IsRightCancelMulZero α] [MulPosReflectLT α]
  证明: fun x _ _ h => h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm) fun h' =>
    (lt_of_mul_lt_mul_right h' x.2.le).le

Depends on / 依赖: eq_or_lt, h.eq_or_lt.elim, le_of_eq, ne.symm
-/
theorem MulPosReflectLT.toMulPosReflectLE [IsRightCancelMulZero α] [MulPosReflectLT α] :
    MulPosReflectLE α where
  elim := fun x _ _ h => h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm) fun h' =>
    (lt_of_mul_lt_mul_right h' x.2.le).le

/--
theorem `mulPosReflectLE_iff_mulPosReflectLT` / 定理 `mulPosReflectLE_iff_mulPosReflectLT`

English:
theorem mulPosReflectLE_iff_mulPosReflectLT
  given: [IsRightCancelMulZero α]
  proof: ⟨(·.toMulPosReflectLT), (·.toMulPosReflectLE)⟩

中文:
定理 mulPosReflectLE_iff_mulPosReflectLT
  条件: [IsRightCancelMulZero α]
  证明: ⟨(·.toMulPosReflectLT), (·.toMulPosReflectLE)⟩

Depends on / 依赖: toMulPosReflectLE, toMulPosReflectLT
-/
theorem mulPosReflectLE_iff_mulPosReflectLT [IsRightCancelMulZero α] :
    MulPosReflectLE α ↔ MulPosReflectLT α :=
  ⟨(·.toMulPosReflectLT), (·.toMulPosReflectLE)⟩

end PartialOrder

end CancelMonoidWithZero

section GroupWithZero
variable [GroupWithZero G₀]

section Preorder
variable [Preorder G₀] {a b c : G₀}

/--
lemma `mul_inv_left_le` / 引理 `mul_inv_left_le`

English:
lemma mul_inv_left_le
  given: (hb : 0 <= b)
  statement: a * (a⁻¹ * b) <= b
  proof: by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

中文:
引理 mul_inv_left_le
  条件: (hb : 0 <= b)
  结论: a * (a⁻¹ * b) <= b
  证明: by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
lemma mul_inv_left_le (hb : 0 <= b) : a * (a⁻¹ * b) <= b := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/--
lemma `le_mul_inv_left` / 引理 `le_mul_inv_left`

English:
lemma le_mul_inv_left
  given: (hb : b <= 0)
  statement: b <= a * (a⁻¹ * b)
  proof: by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

中文:
引理 le_mul_inv_left
  条件: (hb : b <= 0)
  结论: b <= a * (a⁻¹ * b)
  证明: by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
lemma le_mul_inv_left (hb : b <= 0) : b <= a * (a⁻¹ * b) := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/--
lemma `inv_mul_left_le` / 引理 `inv_mul_left_le`

English:
lemma inv_mul_left_le
  given: (hb : 0 <= b)
  statement: a⁻¹ * (a * b) <= b
  proof: by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

中文:
引理 inv_mul_left_le
  条件: (hb : 0 <= b)
  结论: a⁻¹ * (a * b) <= b
  证明: by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
lemma inv_mul_left_le (hb : 0 <= b) : a⁻¹ * (a * b) <= b := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/--
lemma `le_inv_mul_left` / 引理 `le_inv_mul_left`

English:
lemma le_inv_mul_left
  given: (hb : b <= 0)
  statement: b <= a⁻¹ * (a * b)
  proof: by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

中文:
引理 le_inv_mul_left
  条件: (hb : b <= 0)
  结论: b <= a⁻¹ * (a * b)
  证明: by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
lemma le_inv_mul_left (hb : b <= 0) : b <= a⁻¹ * (a * b) := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/--
lemma `mul_inv_right_le` / 引理 `mul_inv_right_le`

English:
lemma mul_inv_right_le
  given: (ha : 0 <= a)
  statement: a * b * b⁻¹ <= a
  proof: by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

中文:
引理 mul_inv_right_le
  条件: (ha : 0 <= a)
  结论: a * b * b⁻¹ <= a
  证明: by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
lemma mul_inv_right_le (ha : 0 <= a) : a * b * b⁻¹ <= a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/--
lemma `le_mul_inv_right` / 引理 `le_mul_inv_right`

English:
lemma le_mul_inv_right
  given: (ha : a <= 0)
  statement: a <= a * b * b⁻¹
  proof: by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

中文:
引理 le_mul_inv_right
  条件: (ha : a <= 0)
  结论: a <= a * b * b⁻¹
  证明: by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
lemma le_mul_inv_right (ha : a <= 0) : a <= a * b * b⁻¹ := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/--
lemma `inv_mul_right_le` / 引理 `inv_mul_right_le`

English:
lemma inv_mul_right_le
  given: (ha : 0 <= a)
  statement: a * b⁻¹ * b <= a
  proof: by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

中文:
引理 inv_mul_right_le
  条件: (ha : 0 <= a)
  结论: a * b⁻¹ * b <= a
  证明: by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
lemma inv_mul_right_le (ha : 0 <= a) : a * b⁻¹ * b <= a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/--
lemma `le_inv_mul_right` / 引理 `le_inv_mul_right`

English:
lemma le_inv_mul_right
  given: (ha : a <= 0)
  statement: a <= a * b⁻¹ * b
  proof: by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

中文:
引理 le_inv_mul_right
  条件: (ha : a <= 0)
  结论: a <= a * b⁻¹ * b
  证明: by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
lemma le_inv_mul_right (ha : a <= 0) : a <= a * b⁻¹ * b := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/--
lemma `mul_div_mul_right_le` / 引理 `mul_div_mul_right_le`

English:
lemma mul_div_mul_right_le
  given: (h : 0 <= a / b)
  statement: a * c / (b * c) <= a / b
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]

中文:
引理 mul_div_mul_right_le
  条件: (h : 0 <= a / b)
  结论: a * c / (b * c) <= a / b
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]

Depends on / 依赖: eq_or_ne, mul_div_mul_right
-/
lemma mul_div_mul_right_le (h : 0 <= a / b) : a * c / (b * c) <= a / b := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]

/--
lemma `le_mul_div_mul_right` / 引理 `le_mul_div_mul_right`

English:
lemma le_mul_div_mul_right
  given: (h : a / b <= 0)
  statement: a / b <= a * c / (b * c)
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]

中文:
引理 le_mul_div_mul_right
  条件: (h : a / b <= 0)
  结论: a / b <= a * c / (b * c)
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]

Depends on / 依赖: eq_or_ne, mul_div_mul_right
-/
lemma le_mul_div_mul_right (h : a / b <= 0) : a / b <= a * c / (b * c) := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]

end Preorder

section Preorder
variable [Preorder G₀] [ZeroLEOneClass G₀] {a b c : G₀}

/--
lemma `div_self_le_one` / 引理 `div_self_le_one`

English:
lemma div_self_le_one
  given: (a : G₀)
  statement: a / a <= 1
  proof: by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

中文:
引理 div_self_le_one
  条件: (a : G₀)
  结论: a / a <= 1
  证明: by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
lemma div_self_le_one (a : G₀) : a / a <= 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/--
lemma `mul_inv_le_one` / 引理 `mul_inv_le_one`

English:
lemma mul_inv_le_one
  statement: a * a⁻¹ <= 1
  proof: by simpa only [div_eq_mul_inv] using div_self_le_one a

中文:
引理 mul_inv_le_one
  结论: a * a⁻¹ <= 1
  证明: by simpa only [div_eq_mul_inv] using div_self_le_one a

Depends on / 依赖: div_eq_mul_inv, div_self_le_one
-/
lemma mul_inv_le_one : a * a⁻¹ <= 1 := by simpa only [div_eq_mul_inv] using div_self_le_one a

/--
lemma `inv_mul_le_one` / 引理 `inv_mul_le_one`

English:
lemma inv_mul_le_one
  statement: a⁻¹ * a <= 1
  proof: by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

中文:
引理 inv_mul_le_one
  结论: a⁻¹ * a <= 1
  证明: by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
lemma inv_mul_le_one : a⁻¹ * a <= 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

end Preorder

section PartialOrder
variable [PartialOrder G₀]

section PosMulReflectLT

variable [PosMulReflectLT G₀] {a b c : G₀}

/--
lemma `inv_pos` / 引理 `inv_pos`

English:
lemma inv_pos
  statement: 0 < a⁻¹ ↔ 0 < a
  proof: by
  suffices forall a : G₀, 0 < a -> 0 < a⁻¹ from ⟨fun h => inv_inv a ▸ this _ h, this a⟩
  intro a ha
  apply lt_of_mul_lt_mul_left _ ha.le
  apply lt_of_mul_lt_mul_left _ ha.le
  simpa [ha.ne']

alias ⟨_, inv_pos_of_pos⟩ := inv_pos

中文:
引理 inv_pos
  结论: 0 < a⁻¹ ↔ 0 < a
  证明: by
  suffices forall a : G₀, 0 < a -> 0 < a⁻¹ from ⟨fun h => inv_inv a ▸ this _ h, this a⟩
  intro a ha
  apply lt_of_mul_lt_mul_left _ ha.le
  apply lt_of_mul_lt_mul_left _ ha.le
  simpa [ha.ne']

alias ⟨_, inv_pos_of_pos⟩ := inv_pos
-/
@[simp] lemma inv_pos : 0 < a⁻¹ ↔ 0 < a := by
  suffices forall a : G₀, 0 < a -> 0 < a⁻¹ from ⟨fun h => inv_inv a ▸ this _ h, this a⟩
  intro a ha
  apply lt_of_mul_lt_mul_left _ ha.le
  apply lt_of_mul_lt_mul_left _ ha.le
  simpa [ha.ne']

alias ⟨_, inv_pos_of_pos⟩ := inv_pos

/--
lemma `inv_nonneg` / 引理 `inv_nonneg`

English:
lemma inv_nonneg
  statement: 0 <= a⁻¹ ↔ 0 <= a
  proof: by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

alias ⟨_, inv_nonneg_of_nonneg⟩ := inv_nonneg

中文:
引理 inv_nonneg
  结论: 0 <= a⁻¹ ↔ 0 <= a
  证明: by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

alias ⟨_, inv_nonneg_of_nonneg⟩ := inv_nonneg
-/
@[simp] lemma inv_nonneg : 0 <= a⁻¹ ↔ 0 <= a := by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

alias ⟨_, inv_nonneg_of_nonneg⟩ := inv_nonneg

/--
lemma `one_div_pos` / 引理 `one_div_pos`

English:
lemma one_div_pos
  statement: 0 < 1 / a ↔ 0 < a
  proof: one_div a ▸ inv_pos

中文:
引理 one_div_pos
  结论: 0 < 1 / a ↔ 0 < a
  证明: one_div a ▸ inv_pos

Depends on / 依赖: inv_pos, one_div
-/
lemma one_div_pos : 0 < 1 / a ↔ 0 < a := one_div a ▸ inv_pos
/--
lemma `one_div_nonneg` / 引理 `one_div_nonneg`

English:
lemma one_div_nonneg
  statement: 0 <= 1 / a ↔ 0 <= a
  proof: one_div a ▸ inv_nonneg

中文:
引理 one_div_nonneg
  结论: 0 <= 1 / a ↔ 0 <= a
  证明: one_div a ▸ inv_nonneg

Depends on / 依赖: inv_nonneg, one_div
-/
lemma one_div_nonneg : 0 <= 1 / a ↔ 0 <= a := one_div a ▸ inv_nonneg

variable (G₀) in
/--
theorem `PosMulReflectLT.toPosMulStrictMono` / 定理 `PosMulReflectLT.toPosMulStrictMono`

English:
theorem PosMulReflectLT.toPosMulStrictMono
  statement: PosMulStrictMono G₀ where
  proof: lt_of_mul_lt_mul_left (by simpa [ha.ne']) (inv_pos_of_pos ha).le

中文:
定理 PosMulReflectLT.toPosMulStrictMono
  结论: PosMulStrictMono G₀ where
  证明: lt_of_mul_lt_mul_left (by simpa [ha.ne']) (inv_pos_of_pos ha).le

Depends on / 依赖: ha.ne, inv_pos_of_pos, lt_of_mul_lt_mul_left
-/
theorem PosMulReflectLT.toPosMulStrictMono : PosMulStrictMono G₀ where
  mul_lt_mul_of_pos_left a ha b c hbc :=
    lt_of_mul_lt_mul_left (by simpa [ha.ne']) (inv_pos_of_pos ha).le

variable (G₀) in
/--
theorem `MulPosReflectLE.of_posMulReflectLT_of_mulPosMono` / 定理 `MulPosReflectLE.of_posMulReflectLT_of_mulPosMono`

English:
theorem MulPosReflectLE.of_posMulReflectLT_of_mulPosMono
  given: [MulPosMono G₀]
  statement: MulPosReflectLE G₀ where
  proof: by
    rintro ⟨a, ha⟩ b c h
    simpa [ha.ne'] using mul_le_mul_of_nonneg_right h (inv_nonneg.2 ha.le)

中文:
定理 MulPosReflectLE.of_posMulReflectLT_of_mulPosMono
  条件: [MulPosMono G₀]
  结论: MulPosReflectLE G₀ where
  证明: by
    rintro ⟨a, ha⟩ b c h
    simpa [ha.ne'] using mul_le_mul_of_nonneg_right h (inv_nonneg.2 ha.le)

Depends on / 依赖: ha.le, ha.ne, inv_nonneg, mul_le_mul_of_nonneg_right
-/
theorem MulPosReflectLE.of_posMulReflectLT_of_mulPosMono [MulPosMono G₀] : MulPosReflectLE G₀ where
  elim := by
    rintro ⟨a, ha⟩ b c h
    simpa [ha.ne'] using mul_le_mul_of_nonneg_right h (inv_nonneg.2 ha.le)

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulReflectLT.toPosMulReflectLE

/--
lemma `div_pos` / 引理 `div_pos`

English:
lemma div_pos
  given: (ha : 0 < a) (hb : 0 < b)
  statement: 0 < a / b
  proof: by
  rw [div_eq_mul_inv]; exact mul_pos ha (inv_pos.2 hb)

中文:
引理 div_pos
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: 0 < a / b
  证明: by
  rw [div_eq_mul_inv]; exact mul_pos ha (inv_pos.2 hb)

Depends on / 依赖: div_eq_mul_inv, inv_pos, mul_pos
-/
lemma div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_eq_mul_inv]; exact mul_pos ha (inv_pos.2 hb)

/--
lemma `div_nonneg` / 引理 `div_nonneg`

English:
lemma div_nonneg
  given: (ha : 0 <= a) (hb : 0 <= b)
  statement: 0 <= a / b
  proof: by
  rw [div_eq_mul_inv]; exact mul_nonneg ha (inv_nonneg.2 hb)

中文:
引理 div_nonneg
  条件: (ha : 0 <= a) (hb : 0 <= b)
  结论: 0 <= a / b
  证明: by
  rw [div_eq_mul_inv]; exact mul_nonneg ha (inv_nonneg.2 hb)

Depends on / 依赖: div_eq_mul_inv, inv_nonneg, mul_nonneg
-/
lemma div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b := by
  rw [div_eq_mul_inv]; exact mul_nonneg ha (inv_nonneg.2 hb)

/--
lemma `le_inv_mul_iff₀` / 引理 `le_inv_mul_iff₀`

English:
lemma le_inv_mul_iff₀
  given: (hc : 0 < c)
  statement: a <= c⁻¹ * b ↔ c * a <= b
  proof: by
  rw [← mul_le_mul_iff_of_pos_left hc]; rw [mul_inv_cancel_left₀ hc.ne']

中文:
引理 le_inv_mul_iff₀
  条件: (hc : 0 < c)
  结论: a <= c⁻¹ * b ↔ c * a <= b
  证明: by
  rw [← mul_le_mul_iff_of_pos_left hc]; rw [mul_inv_cancel_left₀ hc.ne']

Depends on / 依赖: hc.ne, mul_le_mul_iff_of_pos_left
-/
lemma le_inv_mul_iff₀ (hc : 0 < c) : a <= c⁻¹ * b ↔ c * a <= b := by
  rw [← mul_le_mul_iff_of_pos_left hc]; rw [mul_inv_cancel_left₀ hc.ne']

/--
lemma `inv_mul_le_iff₀` / 引理 `inv_mul_le_iff₀`

English:
lemma inv_mul_le_iff₀
  given: (hc : 0 < c)
  statement: c⁻¹ * b <= a ↔ b <= c * a
  proof: by
  rw [← mul_le_mul_iff_of_pos_left hc]; rw [mul_inv_cancel_left₀ hc.ne']

中文:
引理 inv_mul_le_iff₀
  条件: (hc : 0 < c)
  结论: c⁻¹ * b <= a ↔ b <= c * a
  证明: by
  rw [← mul_le_mul_iff_of_pos_left hc]; rw [mul_inv_cancel_left₀ hc.ne']

Depends on / 依赖: hc.ne, mul_le_mul_iff_of_pos_left
-/
lemma inv_mul_le_iff₀ (hc : 0 < c) : c⁻¹ * b <= a ↔ b <= c * a := by
  rw [← mul_le_mul_iff_of_pos_left hc]; rw [mul_inv_cancel_left₀ hc.ne']

/--
lemma `one_le_inv_mul₀` / 引理 `one_le_inv_mul₀`

English:
lemma one_le_inv_mul₀
  given: (ha : 0 < a)
  statement: 1 <= a⁻¹ * b ↔ a <= b
  proof: by rw [le_inv_mul_iff₀ ha, mul_one]

中文:
引理 one_le_inv_mul₀
  条件: (ha : 0 < a)
  结论: 1 <= a⁻¹ * b ↔ a <= b
  证明: by rw [le_inv_mul_iff₀ ha, mul_one]

Depends on / 依赖: mul_one
-/
lemma one_le_inv_mul₀ (ha : 0 < a) : 1 <= a⁻¹ * b ↔ a <= b := by rw [le_inv_mul_iff₀ ha, mul_one]
/--
lemma `inv_mul_le_one₀` / 引理 `inv_mul_le_one₀`

English:
lemma inv_mul_le_one₀
  given: (ha : 0 < a)
  statement: a⁻¹ * b <= 1 ↔ b <= a
  proof: by rw [inv_mul_le_iff₀ ha, mul_one]

中文:
引理 inv_mul_le_one₀
  条件: (ha : 0 < a)
  结论: a⁻¹ * b <= 1 ↔ b <= a
  证明: by rw [inv_mul_le_iff₀ ha, mul_one]

Depends on / 依赖: mul_one
-/
lemma inv_mul_le_one₀ (ha : 0 < a) : a⁻¹ * b <= 1 ↔ b <= a := by rw [inv_mul_le_iff₀ ha, mul_one]

/--
lemma `inv_le_iff_one_le_mul₀'` / 引理 `inv_le_iff_one_le_mul₀'`

English:
lemma inv_le_iff_one_le_mul₀'
  given: (ha : 0 < a)
  statement: a⁻¹ <= b ↔ 1 <= a * b
  proof: by
  rw [← inv_mul_le_iff₀ ha]; rw [mul_one]

中文:
引理 inv_le_iff_one_le_mul₀'
  条件: (ha : 0 < a)
  结论: a⁻¹ <= b ↔ 1 <= a * b
  证明: by
  rw [← inv_mul_le_iff₀ ha]; rw [mul_one]

Depends on / 依赖: mul_one
-/
lemma inv_le_iff_one_le_mul₀' (ha : 0 < a) : a⁻¹ <= b ↔ 1 <= a * b := by
  rw [← inv_mul_le_iff₀ ha]; rw [mul_one]

/--
lemma `one_le_inv₀` / 引理 `one_le_inv₀`

English:
lemma one_le_inv₀
  given: (ha : 0 < a)
  statement: 1 <= a⁻¹ ↔ a <= 1
  proof: by simpa using one_le_inv_mul₀ ha (b := 1)

中文:
引理 one_le_inv₀
  条件: (ha : 0 < a)
  结论: 1 <= a⁻¹ ↔ a <= 1
  证明: by simpa using one_le_inv_mul₀ ha (b := 1)
-/
lemma one_le_inv₀ (ha : 0 < a) : 1 <= a⁻¹ ↔ a <= 1 := by simpa using one_le_inv_mul₀ ha (b := 1)
/--
lemma `inv_le_one₀` / 引理 `inv_le_one₀`

English:
lemma inv_le_one₀
  given: (ha : 0 < a)
  statement: a⁻¹ <= 1 ↔ 1 <= a
  proof: by simpa using inv_mul_le_one₀ ha (b := 1)

@[bound] alias ⟨_, Bound.one_le_inv₀⟩ := one_le_inv₀

中文:
引理 inv_le_one₀
  条件: (ha : 0 < a)
  结论: a⁻¹ <= 1 ↔ 1 <= a
  证明: by simpa using inv_mul_le_one₀ ha (b := 1)

@[bound] alias ⟨_, Bound.one_le_inv₀⟩ := one_le_inv₀
-/
lemma inv_le_one₀ (ha : 0 < a) : a⁻¹ <= 1 ↔ 1 <= a := by simpa using inv_mul_le_one₀ ha (b := 1)

@[bound] alias ⟨_, Bound.one_le_inv₀⟩ := one_le_inv₀

/--
lemma `mul_le_of_le_inv_mul₀` / 引理 `mul_le_of_le_inv_mul₀`

English:
lemma mul_le_of_le_inv_mul₀
  given: (hb : 0 <= b) (hc : 0 <= c) (h : a <= c⁻¹ * b)
  statement: c * a <= b
  proof: by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_inv_mul_iff₀ hc] at h

中文:
引理 mul_le_of_le_inv_mul₀
  条件: (hb : 0 <= b) (hc : 0 <= c) (h : a <= c⁻¹ * b)
  结论: c * a <= b
  证明: by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_inv_mul_iff₀ hc] at h

Depends on / 依赖: eq_or_lt, hc.eq_or_lt
-/
lemma mul_le_of_le_inv_mul₀ (hb : 0 <= b) (hc : 0 <= c) (h : a <= c⁻¹ * b) : c * a <= b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_inv_mul_iff₀ hc] at h

/--
lemma `inv_mul_le_of_le_mul₀` / 引理 `inv_mul_le_of_le_mul₀`

English:
lemma inv_mul_le_of_le_mul₀
  given: (hb : 0 <= b) (hc : 0 <= c) (h : a <= b * c)
  statement: b⁻¹ * a <= c
  proof: by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [inv_mul_le_iff₀ hb]

中文:
引理 inv_mul_le_of_le_mul₀
  条件: (hb : 0 <= b) (hc : 0 <= c) (h : a <= b * c)
  结论: b⁻¹ * a <= c
  证明: by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [inv_mul_le_iff₀ hb]

Depends on / 依赖: eq_or_lt, hb.eq_or_lt
-/
lemma inv_mul_le_of_le_mul₀ (hb : 0 <= b) (hc : 0 <= c) (h : a <= b * c) : b⁻¹ * a <= c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [inv_mul_le_iff₀ hb]

/--
lemma `lt_inv_mul_iff₀` / 引理 `lt_inv_mul_iff₀`

English:
lemma lt_inv_mul_iff₀
  given: (hc : 0 < c)
  statement: a < c⁻¹ * b ↔ c * a < b
  proof: by
  rw [← mul_lt_mul_iff_of_pos_left hc]; rw [mul_inv_cancel_left₀ hc.ne']

中文:
引理 lt_inv_mul_iff₀
  条件: (hc : 0 < c)
  结论: a < c⁻¹ * b ↔ c * a < b
  证明: by
  rw [← mul_lt_mul_iff_of_pos_left hc]; rw [mul_inv_cancel_left₀ hc.ne']

Depends on / 依赖: hc.ne, mul_lt_mul_iff_of_pos_left
-/
lemma lt_inv_mul_iff₀ (hc : 0 < c) : a < c⁻¹ * b ↔ c * a < b := by
  rw [← mul_lt_mul_iff_of_pos_left hc]; rw [mul_inv_cancel_left₀ hc.ne']

/--
lemma `inv_mul_lt_iff₀` / 引理 `inv_mul_lt_iff₀`

English:
lemma inv_mul_lt_iff₀
  given: (hc : 0 < c)
  statement: c⁻¹ * b < a ↔ b < c * a
  proof: by
  rw [← mul_lt_mul_iff_of_pos_left hc]; rw [mul_inv_cancel_left₀ hc.ne']

中文:
引理 inv_mul_lt_iff₀
  条件: (hc : 0 < c)
  结论: c⁻¹ * b < a ↔ b < c * a
  证明: by
  rw [← mul_lt_mul_iff_of_pos_left hc]; rw [mul_inv_cancel_left₀ hc.ne']

Depends on / 依赖: hc.ne, mul_lt_mul_iff_of_pos_left
-/
lemma inv_mul_lt_iff₀ (hc : 0 < c) : c⁻¹ * b < a ↔ b < c * a := by
  rw [← mul_lt_mul_iff_of_pos_left hc]; rw [mul_inv_cancel_left₀ hc.ne']

/--
lemma `inv_lt_iff_one_lt_mul₀'` / 引理 `inv_lt_iff_one_lt_mul₀'`

English:
lemma inv_lt_iff_one_lt_mul₀'
  given: (ha : 0 < a)
  statement: a⁻¹ < b ↔ 1 < a * b
  proof: by
  rw [← inv_mul_lt_iff₀ ha]; rw [mul_one]

中文:
引理 inv_lt_iff_one_lt_mul₀'
  条件: (ha : 0 < a)
  结论: a⁻¹ < b ↔ 1 < a * b
  证明: by
  rw [← inv_mul_lt_iff₀ ha]; rw [mul_one]

Depends on / 依赖: mul_one
-/
lemma inv_lt_iff_one_lt_mul₀' (ha : 0 < a) : a⁻¹ < b ↔ 1 < a * b := by
  rw [← inv_mul_lt_iff₀ ha]; rw [mul_one]

/--
lemma `one_lt_inv_mul₀` / 引理 `one_lt_inv_mul₀`

English:
lemma one_lt_inv_mul₀
  given: (ha : 0 < a)
  statement: 1 < a⁻¹ * b ↔ a < b
  proof: by rw [lt_inv_mul_iff₀ ha, mul_one]

中文:
引理 one_lt_inv_mul₀
  条件: (ha : 0 < a)
  结论: 1 < a⁻¹ * b ↔ a < b
  证明: by rw [lt_inv_mul_iff₀ ha, mul_one]

Depends on / 依赖: mul_one
-/
lemma one_lt_inv_mul₀ (ha : 0 < a) : 1 < a⁻¹ * b ↔ a < b := by rw [lt_inv_mul_iff₀ ha, mul_one]
/--
lemma `inv_mul_lt_one₀` / 引理 `inv_mul_lt_one₀`

English:
lemma inv_mul_lt_one₀
  given: (ha : 0 < a)
  statement: a⁻¹ * b < 1 ↔ b < a
  proof: by rw [inv_mul_lt_iff₀ ha, mul_one]

中文:
引理 inv_mul_lt_one₀
  条件: (ha : 0 < a)
  结论: a⁻¹ * b < 1 ↔ b < a
  证明: by rw [inv_mul_lt_iff₀ ha, mul_one]

Depends on / 依赖: mul_one
-/
lemma inv_mul_lt_one₀ (ha : 0 < a) : a⁻¹ * b < 1 ↔ b < a := by rw [inv_mul_lt_iff₀ ha, mul_one]

/--
lemma `one_lt_inv₀` / 引理 `one_lt_inv₀`

English:
lemma one_lt_inv₀
  given: (ha : 0 < a)
  statement: 1 < a⁻¹ ↔ a < 1
  proof: by simpa using one_lt_inv_mul₀ ha (b := 1)

中文:
引理 one_lt_inv₀
  条件: (ha : 0 < a)
  结论: 1 < a⁻¹ ↔ a < 1
  证明: by simpa using one_lt_inv_mul₀ ha (b := 1)
-/
lemma one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1 := by simpa using one_lt_inv_mul₀ ha (b := 1)
/--
lemma `inv_lt_one₀` / 引理 `inv_lt_one₀`

English:
lemma inv_lt_one₀
  given: (ha : 0 < a)
  statement: a⁻¹ < 1 ↔ 1 < a
  proof: by simpa using inv_mul_lt_one₀ ha (b := 1)

中文:
引理 inv_lt_one₀
  条件: (ha : 0 < a)
  结论: a⁻¹ < 1 ↔ 1 < a
  证明: by simpa using inv_mul_lt_one₀ ha (b := 1)
-/
lemma inv_lt_one₀ (ha : 0 < a) : a⁻¹ < 1 ↔ 1 < a := by simpa using inv_mul_lt_one₀ ha (b := 1)

section ZeroLEOneClass

variable [ZeroLEOneClass G₀]

@[bound]
/--
lemma `inv_lt_one_of_one_lt₀` / 引理 `inv_lt_one_of_one_lt₀`

English:
lemma inv_lt_one_of_one_lt₀
  given: (ha : 1 < a)
  statement: a⁻¹ < 1
  proof: (inv_lt_one₀ <| zero_lt_one.trans ha).2 ha

中文:
引理 inv_lt_one_of_one_lt₀
  条件: (ha : 1 < a)
  结论: a⁻¹ < 1
  证明: (inv_lt_one₀ <| zero_lt_one.trans ha).2 ha

Depends on / 依赖: zero_lt_one, zero_lt_one.trans
-/
lemma inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1 := (inv_lt_one₀ <| zero_lt_one.trans ha).2 ha

/--
lemma `one_lt_inv_iff₀` / 引理 `one_lt_inv_iff₀`

English:
lemma one_lt_inv_iff₀
  statement: 1 < a⁻¹ ↔ 0 < a ∧ a < 1 where
  proof: ⟨inv_pos.1 (zero_lt_one.trans h), inv_inv a ▸ (inv_lt_one₀ <| zero_lt_one.trans h).2 h⟩
  mpr h := (one_lt_inv₀ h.1).2 h.2

@[bound]

中文:
引理 one_lt_inv_iff₀
  结论: 1 < a⁻¹ ↔ 0 < a ∧ a < 1 where
  证明: ⟨inv_pos.1 (zero_lt_one.trans h), inv_inv a ▸ (inv_lt_one₀ <| zero_lt_one.trans h).2 h⟩
  mpr h := (one_lt_inv₀ h.1).2 h.2

@[bound]

Depends on / 依赖: inv_inv, inv_pos, zero_lt_one, zero_lt_one.trans
-/
lemma one_lt_inv_iff₀ : 1 < a⁻¹ ↔ 0 < a ∧ a < 1 where
  mp h := ⟨inv_pos.1 (zero_lt_one.trans h), inv_inv a ▸ (inv_lt_one₀ <| zero_lt_one.trans h).2 h⟩
  mpr h := (one_lt_inv₀ h.1).2 h.2

@[bound]
/--
lemma `inv_le_one_of_one_le₀` / 引理 `inv_le_one_of_one_le₀`

English:
lemma inv_le_one_of_one_le₀
  given: (ha : 1 <= a)
  statement: a⁻¹ <= 1
  proof: (inv_le_one₀ <| zero_lt_one.trans_le ha).2 ha

中文:
引理 inv_le_one_of_one_le₀
  条件: (ha : 1 <= a)
  结论: a⁻¹ <= 1
  证明: (inv_le_one₀ <| zero_lt_one.trans_le ha).2 ha

Depends on / 依赖: trans_le, zero_lt_one, zero_lt_one.trans_le
-/
lemma inv_le_one_of_one_le₀ (ha : 1 <= a) : a⁻¹ <= 1 :=
  (inv_le_one₀ <| zero_lt_one.trans_le ha).2 ha

/--
lemma `one_le_inv_iff₀` / 引理 `one_le_inv_iff₀`

English:
lemma one_le_inv_iff₀
  statement: 1 <= a⁻¹ ↔ 0 < a ∧ a <= 1 where
  proof: ⟨inv_pos.1 (zero_lt_one.trans_le h),
    inv_inv a ▸ (inv_le_one₀ <| zero_lt_one.trans_le h).2 h⟩
  mpr h := (one_le_inv₀ h.1).2 h.2

@[bound]

中文:
引理 one_le_inv_iff₀
  结论: 1 <= a⁻¹ ↔ 0 < a ∧ a <= 1 where
  证明: ⟨inv_pos.1 (zero_lt_one.trans_le h),
    inv_inv a ▸ (inv_le_one₀ <| zero_lt_one.trans_le h).2 h⟩
  mpr h := (one_le_inv₀ h.1).2 h.2

@[bound]

Depends on / 依赖: inv_pos, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
lemma one_le_inv_iff₀ : 1 <= a⁻¹ ↔ 0 < a ∧ a <= 1 where
  mp h := ⟨inv_pos.1 (zero_lt_one.trans_le h),
    inv_inv a ▸ (inv_le_one₀ <| zero_lt_one.trans_le h).2 h⟩
  mpr h := (one_le_inv₀ h.1).2 h.2

@[bound]
/--
lemma `inv_mul_le_one_of_le₀` / 引理 `inv_mul_le_one_of_le₀`

English:
lemma inv_mul_le_one_of_le₀
  given: (h : a <= b) (hb : 0 <= b)
  statement: b⁻¹ * a <= 1
  proof: inv_mul_le_of_le_mul₀ hb zero_le_one by rwa [mul_one]

中文:
引理 inv_mul_le_one_of_le₀
  条件: (h : a <= b) (hb : 0 <= b)
  结论: b⁻¹ * a <= 1
  证明: inv_mul_le_of_le_mul₀ hb zero_le_one by rwa [mul_one]

Depends on / 依赖: mul_one, zero_le_one
-/
lemma inv_mul_le_one_of_le₀ (h : a <= b) (hb : 0 <= b) : b⁻¹ * a <= 1 :=
inv_mul_le_of_le_mul₀ hb zero_le_one by rwa [mul_one]

section ZPow
variable {m n : Int}

/--
lemma `zpow_nonneg` / 引理 `zpow_nonneg`

English:
lemma zpow_nonneg
  given: (ha : 0 <= a)
  statement: forall n : Int, 0 <= a ^ n

中文:
引理 zpow_nonneg
  条件: (ha : 0 <= a)
  结论: 对任意 n : 整数, 0 <= a ^ n
-/
lemma zpow_nonneg (ha : 0 <= a) : forall n : Int, 0 <= a ^ n
  | (n : Nat) => by rw [zpow_natCast]; exact pow_nonneg ha _
  | -(n + 1 : Nat) => by rw [zpow_neg, inv_nonneg, zpow_natCast]; exact pow_nonneg ha _

/--
lemma `zpow_pos` / 引理 `zpow_pos`

English:
lemma zpow_pos
  given: (ha : 0 < a)
  statement: forall n : Int, 0 < a ^ n

中文:
引理 zpow_pos
  条件: (ha : 0 < a)
  结论: 对任意 n : 整数, 0 < a ^ n
-/
lemma zpow_pos (ha : 0 < a) : forall n : Int, 0 < a ^ n
  | (n : Nat) => by rw [zpow_natCast]; exact pow_pos ha _
  | -(n + 1 : Nat) => by rw [zpow_neg, inv_pos, zpow_natCast]; exact pow_pos ha _

/--
lemma `zpow_right_mono₀` / 引理 `zpow_right_mono₀`

English:
lemma zpow_right_mono₀
  given: (ha : 1 <= a)
  statement: Monotone fun n : Int => a ^ n
  proof: by
  refine monotone_int_of_le_succ fun n => ?_
  rw [zpow_add_one₀ (zero_lt_one.trans_le ha).ne']
  exact le_mul_of_one_le_right (zpow_nonneg (zero_le_one.trans ha) _) ha

中文:
引理 zpow_right_mono₀
  条件: (ha : 1 <= a)
  结论: Monotone fun n : 整数 => a ^ n
  证明: by
  refine monotone_int_of_le_succ fun n => ?_
  rw [zpow_add_one₀ (zero_lt_one.trans_le ha).ne']
  exact le_mul_of_one_le_right (zpow_nonneg (zero_le_one.trans ha) _) ha

Depends on / 依赖: le_mul_of_one_le_right, monotone_int_of_le_succ, trans_le, zero_le_one, zero_le_one.trans, zero_lt_one, zero_lt_one.trans_le, zpow_nonneg
-/
lemma zpow_right_mono₀ (ha : 1 <= a) : Monotone fun n : Int => a ^ n := by
  refine monotone_int_of_le_succ fun n => ?_
  rw [zpow_add_one₀ (zero_lt_one.trans_le ha).ne']
  exact le_mul_of_one_le_right (zpow_nonneg (zero_le_one.trans ha) _) ha

/--
lemma `zpow_right_anti₀` / 引理 `zpow_right_anti₀`

English:
lemma zpow_right_anti₀
  given: (ha₀ : 0 < a) (ha₁ : a <= 1)
  statement: Antitone fun n : Int => a ^ n
  proof: by
  refine antitone_int_of_succ_le fun n => ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_le_of_le_one_right (zpow_nonneg ha₀.le _) ha₁

中文:
引理 zpow_right_anti₀
  条件: (ha₀ : 0 < a) (ha₁ : a <= 1)
  结论: Antitone fun n : 整数 => a ^ n
  证明: by
  refine antitone_int_of_succ_le fun n => ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_le_of_le_one_right (zpow_nonneg ha₀.le _) ha₁

Depends on / 依赖: antitone_int_of_succ_le, mul_le_of_le_one_right, zpow_nonneg
-/
lemma zpow_right_anti₀ (ha₀ : 0 < a) (ha₁ : a <= 1) : Antitone fun n : Int => a ^ n := by
  refine antitone_int_of_succ_le fun n => ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_le_of_le_one_right (zpow_nonneg ha₀.le _) ha₁

/--
lemma `zpow_right_strictMono₀` / 引理 `zpow_right_strictMono₀`

English:
lemma zpow_right_strictMono₀
  given: (ha : 1 < a)
  statement: StrictMono fun n : Int => a ^ n
  proof: by
  refine strictMono_int_of_lt_succ fun n => ?_
  rw [zpow_add_one₀ (zero_lt_one.trans ha).ne']
  exact lt_mul_of_one_lt_right (zpow_pos (zero_lt_one.trans ha) _) ha

中文:
引理 zpow_right_strictMono₀
  条件: (ha : 1 < a)
  结论: StrictMono fun n : 整数 => a ^ n
  证明: by
  refine strictMono_int_of_lt_succ fun n => ?_
  rw [zpow_add_one₀ (zero_lt_one.trans ha).ne']
  exact lt_mul_of_one_lt_right (zpow_pos (zero_lt_one.trans ha) _) ha

Depends on / 依赖: lt_mul_of_one_lt_right, strictMono_int_of_lt_succ, zero_lt_one, zero_lt_one.trans, zpow_pos
-/
lemma zpow_right_strictMono₀ (ha : 1 < a) : StrictMono fun n : Int => a ^ n := by
  refine strictMono_int_of_lt_succ fun n => ?_
  rw [zpow_add_one₀ (zero_lt_one.trans ha).ne']
  exact lt_mul_of_one_lt_right (zpow_pos (zero_lt_one.trans ha) _) ha

/--
lemma `zpow_right_strictAnti₀` / 引理 `zpow_right_strictAnti₀`

English:
lemma zpow_right_strictAnti₀
  given: (ha₀ : 0 < a) (ha₁ : a < 1)
  statement: StrictAnti fun n : Int => a ^ n
  proof: by
  refine strictAnti_int_of_succ_lt fun n => ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_lt_of_lt_one_right (zpow_pos ha₀ _) ha₁

@[gcongr]

中文:
引理 zpow_right_strictAnti₀
  条件: (ha₀ : 0 < a) (ha₁ : a < 1)
  结论: StrictAnti fun n : 整数 => a ^ n
  证明: by
  refine strictAnti_int_of_succ_lt fun n => ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_lt_of_lt_one_right (zpow_pos ha₀ _) ha₁

@[gcongr]

Depends on / 依赖: mul_lt_of_lt_one_right, strictAnti_int_of_succ_lt, zpow_pos
-/
lemma zpow_right_strictAnti₀ (ha₀ : 0 < a) (ha₁ : a < 1) : StrictAnti fun n : Int => a ^ n := by
  refine strictAnti_int_of_succ_lt fun n => ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_lt_of_lt_one_right (zpow_pos ha₀ _) ha₁

@[gcongr]
/--
lemma `zpow_le_zpow_right₀` / 引理 `zpow_le_zpow_right₀`

English:
lemma zpow_le_zpow_right₀
  given: (ha : 1 <= a) (hmn : m <= n)
  statement: a ^ m <= a ^ n
  proof: zpow_right_mono₀ ha hmn

中文:
引理 zpow_le_zpow_right₀
  条件: (ha : 1 <= a) (hmn : m <= n)
  结论: a ^ m <= a ^ n
  证明: zpow_right_mono₀ ha hmn
-/
lemma zpow_le_zpow_right₀ (ha : 1 <= a) (hmn : m <= n) : a ^ m <= a ^ n := zpow_right_mono₀ ha hmn

/--
lemma `zpow_le_zpow_right_of_le_one₀` / 引理 `zpow_le_zpow_right_of_le_one₀`

English:
lemma zpow_le_zpow_right_of_le_one₀
  given: (ha₀ : 0 < a) (ha₁ : a <= 1) (hmn : m <= n)
  statement: a ^ n <= a ^ m
  proof: zpow_right_anti₀ ha₀ ha₁ hmn

中文:
引理 zpow_le_zpow_right_of_le_one₀
  条件: (ha₀ : 0 < a) (ha₁ : a <= 1) (hmn : m <= n)
  结论: a ^ n <= a ^ m
  证明: zpow_right_anti₀ ha₀ ha₁ hmn
-/
lemma zpow_le_zpow_right_of_le_one₀ (ha₀ : 0 < a) (ha₁ : a <= 1) (hmn : m <= n) : a ^ n <= a ^ m :=
  zpow_right_anti₀ ha₀ ha₁ hmn

/--
lemma `one_le_zpow₀` / 引理 `one_le_zpow₀`

English:
lemma one_le_zpow₀
  given: (ha : 1 <= a) (hn : 0 <= n)
  statement: 1 <= a ^ n
  proof: by simpa using zpow_right_mono₀ ha hn

中文:
引理 one_le_zpow₀
  条件: (ha : 1 <= a) (hn : 0 <= n)
  结论: 1 <= a ^ n
  证明: by simpa using zpow_right_mono₀ ha hn
-/
lemma one_le_zpow₀ (ha : 1 <= a) (hn : 0 <= n) : 1 <= a ^ n := by simpa using zpow_right_mono₀ ha hn

/--
lemma `zpow_le_one₀` / 引理 `zpow_le_one₀`

English:
lemma zpow_le_one₀
  given: (ha₀ : 0 < a) (ha₁ : a <= 1) (hn : 0 <= n)
  statement: a ^ n <= 1
  proof: by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

中文:
引理 zpow_le_one₀
  条件: (ha₀ : 0 < a) (ha₁ : a <= 1) (hn : 0 <= n)
  结论: a ^ n <= 1
  证明: by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn
-/
lemma zpow_le_one₀ (ha₀ : 0 < a) (ha₁ : a <= 1) (hn : 0 <= n) : a ^ n <= 1 := by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

/--
lemma `zpow_le_one_of_nonpos₀` / 引理 `zpow_le_one_of_nonpos₀`

English:
lemma zpow_le_one_of_nonpos₀
  given: (ha : 1 <= a) (hn : n <= 0)
  statement: a ^ n <= 1
  proof: by
  simpa using zpow_right_mono₀ ha hn

中文:
引理 zpow_le_one_of_nonpos₀
  条件: (ha : 1 <= a) (hn : n <= 0)
  结论: a ^ n <= 1
  证明: by
  simpa using zpow_right_mono₀ ha hn
-/
lemma zpow_le_one_of_nonpos₀ (ha : 1 <= a) (hn : n <= 0) : a ^ n <= 1 := by
  simpa using zpow_right_mono₀ ha hn

/--
lemma `one_le_zpow_of_nonpos₀` / 引理 `one_le_zpow_of_nonpos₀`

English:
lemma one_le_zpow_of_nonpos₀
  given: (ha₀ : 0 < a) (ha₁ : a <= 1) (hn : n <= 0)
  statement: 1 <= a ^ n
  proof: by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

@[gcongr]

中文:
引理 one_le_zpow_of_nonpos₀
  条件: (ha₀ : 0 < a) (ha₁ : a <= 1) (hn : n <= 0)
  结论: 1 <= a ^ n
  证明: by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

@[gcongr]
-/
lemma one_le_zpow_of_nonpos₀ (ha₀ : 0 < a) (ha₁ : a <= 1) (hn : n <= 0) : 1 <= a ^ n := by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

@[gcongr]
/--
lemma `zpow_lt_zpow_right₀` / 引理 `zpow_lt_zpow_right₀`

English:
lemma zpow_lt_zpow_right₀
  given: (ha : 1 < a) (hmn : m < n)
  statement: a ^ m < a ^ n
  proof: zpow_right_strictMono₀ ha hmn

中文:
引理 zpow_lt_zpow_right₀
  条件: (ha : 1 < a) (hmn : m < n)
  结论: a ^ m < a ^ n
  证明: zpow_right_strictMono₀ ha hmn
-/
lemma zpow_lt_zpow_right₀ (ha : 1 < a) (hmn : m < n) : a ^ m < a ^ n :=
  zpow_right_strictMono₀ ha hmn

/--
lemma `zpow_lt_zpow_right_of_lt_one₀` / 引理 `zpow_lt_zpow_right_of_lt_one₀`

English:
lemma zpow_lt_zpow_right_of_lt_one₀
  given: (ha₀ : 0 < a) (ha₁ : a < 1) (hmn : m < n)
  statement: a ^ n < a ^ m
  proof: zpow_right_strictAnti₀ ha₀ ha₁ hmn

中文:
引理 zpow_lt_zpow_right_of_lt_one₀
  条件: (ha₀ : 0 < a) (ha₁ : a < 1) (hmn : m < n)
  结论: a ^ n < a ^ m
  证明: zpow_right_strictAnti₀ ha₀ ha₁ hmn
-/
lemma zpow_lt_zpow_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  zpow_right_strictAnti₀ ha₀ ha₁ hmn

/--
lemma `one_lt_zpow₀` / 引理 `one_lt_zpow₀`

English:
lemma one_lt_zpow₀
  given: (ha : 1 < a) (hn : 0 < n)
  statement: 1 < a ^ n
  proof: by
  simpa using zpow_right_strictMono₀ ha hn

中文:
引理 one_lt_zpow₀
  条件: (ha : 1 < a) (hn : 0 < n)
  结论: 1 < a ^ n
  证明: by
  simpa using zpow_right_strictMono₀ ha hn
-/
lemma one_lt_zpow₀ (ha : 1 < a) (hn : 0 < n) : 1 < a ^ n := by
  simpa using zpow_right_strictMono₀ ha hn

/--
lemma `zpow_lt_one₀` / 引理 `zpow_lt_one₀`

English:
lemma zpow_lt_one₀
  given: (ha₀ : 0 < a) (ha₁ : a < 1) (hn : 0 < n)
  statement: a ^ n < 1
  proof: by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn

中文:
引理 zpow_lt_one₀
  条件: (ha₀ : 0 < a) (ha₁ : a < 1) (hn : 0 < n)
  结论: a ^ n < 1
  证明: by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn
-/
lemma zpow_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hn : 0 < n) : a ^ n < 1 := by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn

/--
lemma `zpow_lt_one_of_neg₀` / 引理 `zpow_lt_one_of_neg₀`

English:
lemma zpow_lt_one_of_neg₀
  given: (ha : 1 < a) (hn : n < 0)
  statement: a ^ n < 1
  proof: by
  simpa using zpow_right_strictMono₀ ha hn

中文:
引理 zpow_lt_one_of_neg₀
  条件: (ha : 1 < a) (hn : n < 0)
  结论: a ^ n < 1
  证明: by
  simpa using zpow_right_strictMono₀ ha hn
-/
lemma zpow_lt_one_of_neg₀ (ha : 1 < a) (hn : n < 0) : a ^ n < 1 := by
  simpa using zpow_right_strictMono₀ ha hn

/--
lemma `one_lt_zpow_of_neg₀` / 引理 `one_lt_zpow_of_neg₀`

English:
lemma one_lt_zpow_of_neg₀
  given: (ha₀ : 0 < a) (ha₁ : a < 1) (hn : n < 0)
  statement: 1 < a ^ n
  proof: by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn

中文:
引理 one_lt_zpow_of_neg₀
  条件: (ha₀ : 0 < a) (ha₁ : a < 1) (hn : n < 0)
  结论: 1 < a ^ n
  证明: by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn
-/
lemma one_lt_zpow_of_neg₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hn : n < 0) : 1 < a ^ n := by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn

/--
lemma `zpow_le_zpow_iff_right₀` / 引理 `zpow_le_zpow_iff_right₀`

English:
lemma zpow_le_zpow_iff_right₀
  given: (ha : 1 < a)
  statement: a ^ m <= a ^ n ↔ m <= n
  proof: (zpow_right_strictMono₀ ha).le_iff_le

中文:
引理 zpow_le_zpow_iff_right₀
  条件: (ha : 1 < a)
  结论: a ^ m <= a ^ n ↔ m <= n
  证明: (zpow_right_strictMono₀ ha).le_iff_le
-/
@[simp] lemma zpow_le_zpow_iff_right₀ (ha : 1 < a) : a ^ m <= a ^ n ↔ m <= n :=
  (zpow_right_strictMono₀ ha).le_iff_le

/--
lemma `zpow_lt_zpow_iff_right₀` / 引理 `zpow_lt_zpow_iff_right₀`

English:
lemma zpow_lt_zpow_iff_right₀
  given: (ha : 1 < a)
  statement: a ^ m < a ^ n ↔ m < n
  proof: (zpow_right_strictMono₀ ha).lt_iff_lt

中文:
引理 zpow_lt_zpow_iff_right₀
  条件: (ha : 1 < a)
  结论: a ^ m < a ^ n ↔ m < n
  证明: (zpow_right_strictMono₀ ha).lt_iff_lt
-/
@[simp] lemma zpow_lt_zpow_iff_right₀ (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_right_strictMono₀ ha).lt_iff_lt

/--
lemma `zpow_le_zpow_iff_right_of_lt_one₀` / 引理 `zpow_le_zpow_iff_right_of_lt_one₀`

English:
lemma zpow_le_zpow_iff_right_of_lt_one₀
  given: (ha₀ : 0 < a) (ha₁ : a < 1)
  proof: (zpow_right_strictAnti₀ ha₀ ha₁).le_iff_ge

中文:
引理 zpow_le_zpow_iff_right_of_lt_one₀
  条件: (ha₀ : 0 < a) (ha₁ : a < 1)
  证明: (zpow_right_strictAnti₀ ha₀ ha₁).le_iff_ge

Depends on / 依赖: le_iff_ge
-/
lemma zpow_le_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) :
    a ^ m <= a ^ n ↔ n <= m := (zpow_right_strictAnti₀ ha₀ ha₁).le_iff_ge

/--
lemma `zpow_lt_zpow_iff_right_of_lt_one₀` / 引理 `zpow_lt_zpow_iff_right_of_lt_one₀`

English:
lemma zpow_lt_zpow_iff_right_of_lt_one₀
  given: (ha₀ : 0 < a) (ha₁ : a < 1)
  proof: (zpow_right_strictAnti₀ ha₀ ha₁).lt_iff_gt

中文:
引理 zpow_lt_zpow_iff_right_of_lt_one₀
  条件: (ha₀ : 0 < a) (ha₁ : a < 1)
  证明: (zpow_right_strictAnti₀ ha₀ ha₁).lt_iff_gt

Depends on / 依赖: lt_iff_gt
-/
lemma zpow_lt_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) :
    a ^ m < a ^ n ↔ n < m := (zpow_right_strictAnti₀ ha₀ ha₁).lt_iff_gt

/--
lemma `one_le_zpow_iff_right₀` / 引理 `one_le_zpow_iff_right₀`

English:
lemma one_le_zpow_iff_right₀
  given: (ha : 1 < a)
  statement: 1 <= a ^ n ↔ 0 <= n
  proof: by
  simp [← zpow_le_zpow_iff_right₀ ha]

中文:
引理 one_le_zpow_iff_right₀
  条件: (ha : 1 < a)
  结论: 1 <= a ^ n ↔ 0 <= n
  证明: by
  simp [← zpow_le_zpow_iff_right₀ ha]
-/
@[simp] lemma one_le_zpow_iff_right₀ (ha : 1 < a) : 1 <= a ^ n ↔ 0 <= n := by
  simp [← zpow_le_zpow_iff_right₀ ha]

/--
lemma `one_lt_zpow_iff_right₀` / 引理 `one_lt_zpow_iff_right₀`

English:
lemma one_lt_zpow_iff_right₀
  given: (ha : 1 < a)
  statement: 1 < a ^ n ↔ 0 < n
  proof: by
  simp [← zpow_lt_zpow_iff_right₀ ha]

中文:
引理 one_lt_zpow_iff_right₀
  条件: (ha : 1 < a)
  结论: 1 < a ^ n ↔ 0 < n
  证明: by
  simp [← zpow_lt_zpow_iff_right₀ ha]
-/
@[simp] lemma one_lt_zpow_iff_right₀ (ha : 1 < a) : 1 < a ^ n ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right₀ ha]

/--
lemma `one_le_zpow_iff_right_of_lt_one₀` / 引理 `one_le_zpow_iff_right_of_lt_one₀`

English:
lemma one_le_zpow_iff_right_of_lt_one₀
  given: (ha₀ : 0 < a) (ha₁ : a < 1)
  statement: 1 <= a ^ n ↔ n <= 0
  proof: by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

中文:
引理 one_le_zpow_iff_right_of_lt_one₀
  条件: (ha₀ : 0 < a) (ha₁ : a < 1)
  结论: 1 <= a ^ n ↔ n <= 0
  证明: by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]
-/
@[simp] lemma one_le_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : 1 <= a ^ n ↔ n <= 0 := by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

/--
lemma `one_lt_zpow_iff_right_of_lt_one₀` / 引理 `one_lt_zpow_iff_right_of_lt_one₀`

English:
lemma one_lt_zpow_iff_right_of_lt_one₀
  given: (ha₀ : 0 < a) (ha₁ : a < 1)
  statement: 1 < a ^ n ↔ n < 0
  proof: by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

中文:
引理 one_lt_zpow_iff_right_of_lt_one₀
  条件: (ha₀ : 0 < a) (ha₁ : a < 1)
  结论: 1 < a ^ n ↔ n < 0
  证明: by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]
-/
@[simp] lemma one_lt_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : 1 < a ^ n ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

/--
lemma `zpow_le_one_iff_right₀` / 引理 `zpow_le_one_iff_right₀`

English:
lemma zpow_le_one_iff_right₀
  given: (ha : 1 < a)
  statement: a ^ n <= 1 ↔ n <= 0
  proof: by
  simp [← zpow_le_zpow_iff_right₀ ha]

中文:
引理 zpow_le_one_iff_right₀
  条件: (ha : 1 < a)
  结论: a ^ n <= 1 ↔ n <= 0
  证明: by
  simp [← zpow_le_zpow_iff_right₀ ha]
-/
@[simp] lemma zpow_le_one_iff_right₀ (ha : 1 < a) : a ^ n <= 1 ↔ n <= 0 := by
  simp [← zpow_le_zpow_iff_right₀ ha]

/--
lemma `zpow_lt_one_iff_right₀` / 引理 `zpow_lt_one_iff_right₀`

English:
lemma zpow_lt_one_iff_right₀
  given: (ha : 1 < a)
  statement: a ^ n < 1 ↔ n < 0
  proof: by
  simp [← zpow_lt_zpow_iff_right₀ ha]

中文:
引理 zpow_lt_one_iff_right₀
  条件: (ha : 1 < a)
  结论: a ^ n < 1 ↔ n < 0
  证明: by
  simp [← zpow_lt_zpow_iff_right₀ ha]
-/
@[simp] lemma zpow_lt_one_iff_right₀ (ha : 1 < a) : a ^ n < 1 ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right₀ ha]

/--
lemma `zpow_le_one_iff_right_of_lt_one₀` / 引理 `zpow_le_one_iff_right_of_lt_one₀`

English:
lemma zpow_le_one_iff_right_of_lt_one₀
  given: (ha₀ : 0 < a) (ha₁ : a < 1)
  statement: a ^ n <= 1 ↔ 0 <= n
  proof: by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

中文:
引理 zpow_le_one_iff_right_of_lt_one₀
  条件: (ha₀ : 0 < a) (ha₁ : a < 1)
  结论: a ^ n <= 1 ↔ 0 <= n
  证明: by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]
-/
@[simp] lemma zpow_le_one_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ n <= 1 ↔ 0 <= n := by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

/--
lemma `zpow_lt_one_iff_right_of_lt_one₀` / 引理 `zpow_lt_one_iff_right_of_lt_one₀`

English:
lemma zpow_lt_one_iff_right_of_lt_one₀
  given: (ha₀ : 0 < a) (ha₁ : a < 1)
  statement: a ^ n < 1 ↔ 0 < n
  proof: by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

中文:
引理 zpow_lt_one_iff_right_of_lt_one₀
  条件: (ha₀ : 0 < a) (ha₁ : a < 1)
  结论: a ^ n < 1 ↔ 0 < n
  证明: by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]
-/
@[simp] lemma zpow_lt_one_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ n < 1 ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

end ZPow

end ZeroLEOneClass

section MulPosMono

variable [MulPosMono G₀] {n : Int}

/--
lemma `zpow_left_monoOn₀` / 引理 `zpow_left_monoOn₀`

English:
lemma zpow_left_monoOn₀
  given: (hn : 0 <= n)
  statement: MonotoneOn (fun a : G₀ => a ^ n) {a | 0 <= a}
  proof: by
  lift n to Nat using hn; simpa using pow_left_monotoneOn

中文:
引理 zpow_left_monoOn₀
  条件: (hn : 0 <= n)
  结论: MonotoneOn (fun a : G₀ => a ^ n) {a | 0 <= a}
  证明: by
  lift n to Nat using hn; simpa using pow_left_monotoneOn

Depends on / 依赖: pow_left_monotoneOn
-/
lemma zpow_left_monoOn₀ (hn : 0 <= n) : MonotoneOn (fun a : G₀ => a ^ n) {a | 0 <= a} := by
  lift n to Nat using hn; simpa using pow_left_monotoneOn

/--
lemma `zpow_left_strictMonoOn₀` / 引理 `zpow_left_strictMonoOn₀`

English:
lemma zpow_left_strictMonoOn₀
  given: (hn : 0 < n)
  statement: StrictMonoOn (fun a : G₀ => a ^ n) {a | 0 <= a}
  proof: by
  lift n to Nat using hn.le; simpa using pow_left_strictMonoOn₀ (by lia)

中文:
引理 zpow_left_strictMonoOn₀
  条件: (hn : 0 < n)
  结论: StrictMonoOn (fun a : G₀ => a ^ n) {a | 0 <= a}
  证明: by
  lift n to Nat using hn.le; simpa using pow_left_strictMonoOn₀ (by lia)

Depends on / 依赖: hn.le
-/
lemma zpow_left_strictMonoOn₀ (hn : 0 < n) : StrictMonoOn (fun a : G₀ => a ^ n) {a | 0 <= a} := by
  lift n to Nat using hn.le; simpa using pow_left_strictMonoOn₀ (by lia)

/--
lemma `zpow_le_zpow_left₀` / 引理 `zpow_le_zpow_left₀`

English:
lemma zpow_le_zpow_left₀
  given: (hn : 0 <= n) (ha : 0 <= a) (h : a <= b)
  statement: a ^ n <= b ^ n
  proof: zpow_left_monoOn₀ (G₀ := G₀) hn ha (by grind) h

中文:
引理 zpow_le_zpow_left₀
  条件: (hn : 0 <= n) (ha : 0 <= a) (h : a <= b)
  结论: a ^ n <= b ^ n
  证明: zpow_left_monoOn₀ (G₀ := G₀) hn ha (by grind) h
-/
lemma zpow_le_zpow_left₀ (hn : 0 <= n) (ha : 0 <= a) (h : a <= b) : a ^ n <= b ^ n :=
  zpow_left_monoOn₀ (G₀ := G₀) hn ha (by grind) h

/--
lemma `zpow_lt_zpow_left₀` / 引理 `zpow_lt_zpow_left₀`

English:
lemma zpow_lt_zpow_left₀
  given: (hn : 0 < n) (ha : 0 <= a) (h : a < b)
  statement: a ^ n < b ^ n
  proof: zpow_left_strictMonoOn₀ (G₀ := G₀) hn ha (by grind) h

中文:
引理 zpow_lt_zpow_left₀
  条件: (hn : 0 < n) (ha : 0 <= a) (h : a < b)
  结论: a ^ n < b ^ n
  证明: zpow_left_strictMonoOn₀ (G₀ := G₀) hn ha (by grind) h
-/
lemma zpow_lt_zpow_left₀ (hn : 0 < n) (ha : 0 <= a) (h : a < b) : a ^ n < b ^ n :=
  zpow_left_strictMonoOn₀ (G₀ := G₀) hn ha (by grind) h

end MulPosMono

end PosMulReflectLT

section MulPosReflectLT
variable [MulPosReflectLT G₀] {a b c : G₀}

namespace Right

/--
lemma `inv_pos` / 引理 `inv_pos`

English:
lemma inv_pos
  statement: 0 < a⁻¹ ↔ 0 < a
  proof: by
  suffices forall a : G₀, 0 < a -> 0 < a⁻¹ from ⟨fun h => inv_inv a ▸ this _ h, this a⟩
  intro a ha
  apply lt_of_mul_lt_mul_right _ ha.le
  apply lt_of_mul_lt_mul_right _ ha.le
  simpa [ha.ne']

中文:
引理 inv_pos
  结论: 0 < a⁻¹ ↔ 0 < a
  证明: by
  suffices forall a : G₀, 0 < a -> 0 < a⁻¹ from ⟨fun h => inv_inv a ▸ this _ h, this a⟩
  intro a ha
  apply lt_of_mul_lt_mul_right _ ha.le
  apply lt_of_mul_lt_mul_right _ ha.le
  simpa [ha.ne']

Depends on / 依赖: ha.le, ha.ne, inv_inv, lt_of_mul_lt_mul_right
-/
lemma inv_pos : 0 < a⁻¹ ↔ 0 < a := by
  suffices forall a : G₀, 0 < a -> 0 < a⁻¹ from ⟨fun h => inv_inv a ▸ this _ h, this a⟩
  intro a ha
  apply lt_of_mul_lt_mul_right _ ha.le
  apply lt_of_mul_lt_mul_right _ ha.le
  simpa [ha.ne']

variable (G₀) in
/--
theorem `_root_.MulPosReflectLT.toMulPosStrictMono` / 定理 `_root_.MulPosReflectLT.toMulPosStrictMono`

English:
theorem _root_.MulPosReflectLT.toMulPosStrictMono
  statement: MulPosStrictMono G₀ where
  proof: lt_of_mul_lt_mul_right (by simpa [ha.ne']) (inv_pos.2 ha).le

中文:
定理 _root_.MulPosReflectLT.toMulPosStrictMono
  结论: MulPosStrictMono G₀ where
  证明: lt_of_mul_lt_mul_right (by simpa [ha.ne']) (inv_pos.2 ha).le

Depends on / 依赖: ha.ne, inv_pos, lt_of_mul_lt_mul_right
-/
theorem _root_.MulPosReflectLT.toMulPosStrictMono : MulPosStrictMono G₀ where
  mul_lt_mul_of_pos_right a ha b c hbc :=
    lt_of_mul_lt_mul_right (by simpa [ha.ne']) (inv_pos.2 ha).le

/--
lemma `inv_nonneg` / 引理 `inv_nonneg`

English:
lemma inv_nonneg
  statement: 0 <= a⁻¹ ↔ 0 <= a
  proof: by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

中文:
引理 inv_nonneg
  结论: 0 <= a⁻¹ ↔ 0 <= a
  证明: by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

Depends on / 依赖: inv_pos, le_iff_eq_or_lt, zero_eq_inv
-/
lemma inv_nonneg : 0 <= a⁻¹ ↔ 0 <= a := by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

end Right

attribute [local instance] PosMulReflectLT.toPosMulStrictMono
  MulPosReflectLT.toMulPosStrictMono MulPosReflectLT.toMulPosReflectLE

/--
lemma `div_nonpos_of_nonpos_of_nonneg` / 引理 `div_nonpos_of_nonpos_of_nonneg`

English:
lemma div_nonpos_of_nonpos_of_nonneg
  given: (ha : a <= 0) (hb : 0 <= b)
  statement: a / b <= 0
  proof: by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonpos_of_nonneg ha (Right.inv_nonneg.2 hb)

中文:
引理 div_nonpos_of_nonpos_of_nonneg
  条件: (ha : a <= 0) (hb : 0 <= b)
  结论: a / b <= 0
  证明: by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonpos_of_nonneg ha (Right.inv_nonneg.2 hb)

Depends on / 依赖: Right.inv_nonneg, div_eq_mul_inv, inv_nonneg, mul_nonpos_of_nonpos_of_nonneg
-/
lemma div_nonpos_of_nonpos_of_nonneg (ha : a <= 0) (hb : 0 <= b) : a / b <= 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonpos_of_nonneg ha (Right.inv_nonneg.2 hb)

/--
lemma `le_mul_inv_iff₀` / 引理 `le_mul_inv_iff₀`

English:
lemma le_mul_inv_iff₀
  given: (hc : 0 < c)
  statement: a <= b * c⁻¹ ↔ a * c <= b
  proof: by
  rw [← mul_le_mul_iff_of_pos_right hc]; rw [inv_mul_cancel_right₀ hc.ne']

中文:
引理 le_mul_inv_iff₀
  条件: (hc : 0 < c)
  结论: a <= b * c⁻¹ ↔ a * c <= b
  证明: by
  rw [← mul_le_mul_iff_of_pos_right hc]; rw [inv_mul_cancel_right₀ hc.ne']

Depends on / 依赖: hc.ne, mul_le_mul_iff_of_pos_right
-/
lemma le_mul_inv_iff₀ (hc : 0 < c) : a <= b * c⁻¹ ↔ a * c <= b := by
  rw [← mul_le_mul_iff_of_pos_right hc]; rw [inv_mul_cancel_right₀ hc.ne']

/--
lemma `mul_inv_le_iff₀` / 引理 `mul_inv_le_iff₀`

English:
lemma mul_inv_le_iff₀
  given: (hc : 0 < c)
  statement: b * c⁻¹ <= a ↔ b <= a * c
  proof: by
  rw [← mul_le_mul_iff_of_pos_right hc]; rw [inv_mul_cancel_right₀ hc.ne']

中文:
引理 mul_inv_le_iff₀
  条件: (hc : 0 < c)
  结论: b * c⁻¹ <= a ↔ b <= a * c
  证明: by
  rw [← mul_le_mul_iff_of_pos_right hc]; rw [inv_mul_cancel_right₀ hc.ne']

Depends on / 依赖: hc.ne, mul_le_mul_iff_of_pos_right
-/
lemma mul_inv_le_iff₀ (hc : 0 < c) : b * c⁻¹ <= a ↔ b <= a * c := by
  rw [← mul_le_mul_iff_of_pos_right hc]; rw [inv_mul_cancel_right₀ hc.ne']

/--
lemma `lt_mul_inv_iff₀` / 引理 `lt_mul_inv_iff₀`

English:
lemma lt_mul_inv_iff₀
  given: (hc : 0 < c)
  statement: a < b * c⁻¹ ↔ a * c < b
  proof: by
  rw [← mul_lt_mul_iff_of_pos_right hc]; rw [inv_mul_cancel_right₀ hc.ne']

中文:
引理 lt_mul_inv_iff₀
  条件: (hc : 0 < c)
  结论: a < b * c⁻¹ ↔ a * c < b
  证明: by
  rw [← mul_lt_mul_iff_of_pos_right hc]; rw [inv_mul_cancel_right₀ hc.ne']

Depends on / 依赖: hc.ne, mul_lt_mul_iff_of_pos_right
-/
lemma lt_mul_inv_iff₀ (hc : 0 < c) : a < b * c⁻¹ ↔ a * c < b := by
  rw [← mul_lt_mul_iff_of_pos_right hc]; rw [inv_mul_cancel_right₀ hc.ne']

/--
lemma `mul_inv_lt_iff₀` / 引理 `mul_inv_lt_iff₀`

English:
lemma mul_inv_lt_iff₀
  given: (hc : 0 < c)
  statement: b * c⁻¹ < a ↔ b < a * c
  proof: by
  rw [← mul_lt_mul_iff_of_pos_right hc]; rw [inv_mul_cancel_right₀ hc.ne']

中文:
引理 mul_inv_lt_iff₀
  条件: (hc : 0 < c)
  结论: b * c⁻¹ < a ↔ b < a * c
  证明: by
  rw [← mul_lt_mul_iff_of_pos_right hc]; rw [inv_mul_cancel_right₀ hc.ne']

Depends on / 依赖: hc.ne, mul_lt_mul_iff_of_pos_right
-/
lemma mul_inv_lt_iff₀ (hc : 0 < c) : b * c⁻¹ < a ↔ b < a * c := by
  rw [← mul_lt_mul_iff_of_pos_right hc]; rw [inv_mul_cancel_right₀ hc.ne']

/--
lemma `le_div_iff₀` / 引理 `le_div_iff₀`

English:
lemma le_div_iff₀
  given: (hc : 0 < c)
  statement: a <= b / c ↔ a * c <= b
  proof: by
  rw [div_eq_mul_inv]; rw [le_mul_inv_iff₀ hc]

中文:
引理 le_div_iff₀
  条件: (hc : 0 < c)
  结论: a <= b / c ↔ a * c <= b
  证明: by
  rw [div_eq_mul_inv]; rw [le_mul_inv_iff₀ hc]

Depends on / 依赖: div_eq_mul_inv
-/
lemma le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b := by
  rw [div_eq_mul_inv]; rw [le_mul_inv_iff₀ hc]

/--
lemma `div_le_iff₀` / 引理 `div_le_iff₀`

English:
lemma div_le_iff₀
  given: (hc : 0 < c)
  statement: b / c <= a ↔ b <= a * c
  proof: by
  rw [div_eq_mul_inv]; rw [mul_inv_le_iff₀ hc]

中文:
引理 div_le_iff₀
  条件: (hc : 0 < c)
  结论: b / c <= a ↔ b <= a * c
  证明: by
  rw [div_eq_mul_inv]; rw [mul_inv_le_iff₀ hc]

Depends on / 依赖: div_eq_mul_inv
-/
lemma div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c := by
  rw [div_eq_mul_inv]; rw [mul_inv_le_iff₀ hc]

/--
lemma `lt_div_iff₀` / 引理 `lt_div_iff₀`

English:
lemma lt_div_iff₀
  given: (hc : 0 < c)
  statement: a < b / c ↔ a * c < b
  proof: by
  rw [div_eq_mul_inv]; rw [lt_mul_inv_iff₀ hc]

中文:
引理 lt_div_iff₀
  条件: (hc : 0 < c)
  结论: a < b / c ↔ a * c < b
  证明: by
  rw [div_eq_mul_inv]; rw [lt_mul_inv_iff₀ hc]

Depends on / 依赖: div_eq_mul_inv
-/
lemma lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b := by
  rw [div_eq_mul_inv]; rw [lt_mul_inv_iff₀ hc]

/--
lemma `div_lt_iff₀` / 引理 `div_lt_iff₀`

English:
lemma div_lt_iff₀
  given: (hc : 0 < c)
  statement: b / c < a ↔ b < a * c
  proof: by
  rw [div_eq_mul_inv]; rw [mul_inv_lt_iff₀ hc]

中文:
引理 div_lt_iff₀
  条件: (hc : 0 < c)
  结论: b / c < a ↔ b < a * c
  证明: by
  rw [div_eq_mul_inv]; rw [mul_inv_lt_iff₀ hc]

Depends on / 依赖: div_eq_mul_inv
-/
lemma div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c := by
  rw [div_eq_mul_inv]; rw [mul_inv_lt_iff₀ hc]

/--
lemma `div_le_div_iff_of_pos_right` / 引理 `div_le_div_iff_of_pos_right`

English:
lemma div_le_div_iff_of_pos_right
  given: (hc : 0 < c)
  statement: a / c <= b / c ↔ a <= b
  proof: by
  rw [div_le_iff₀ hc]; rw [div_mul_cancel₀ _ hc.ne']

中文:
引理 div_le_div_iff_of_pos_right
  条件: (hc : 0 < c)
  结论: a / c <= b / c ↔ a <= b
  证明: by
  rw [div_le_iff₀ hc]; rw [div_mul_cancel₀ _ hc.ne']

Depends on / 依赖: hc.ne
-/
lemma div_le_div_iff_of_pos_right (hc : 0 < c) : a / c <= b / c ↔ a <= b := by
  rw [div_le_iff₀ hc]; rw [div_mul_cancel₀ _ hc.ne']

/--
lemma `div_lt_div_iff_of_pos_right` / 引理 `div_lt_div_iff_of_pos_right`

English:
lemma div_lt_div_iff_of_pos_right
  given: (hc : 0 < c)
  statement: a / c < b / c ↔ a < b
  proof: by
  rw [div_lt_iff₀ hc]; rw [div_mul_cancel₀ _ hc.ne']

中文:
引理 div_lt_div_iff_of_pos_right
  条件: (hc : 0 < c)
  结论: a / c < b / c ↔ a < b
  证明: by
  rw [div_lt_iff₀ hc]; rw [div_mul_cancel₀ _ hc.ne']

Depends on / 依赖: hc.ne
-/
lemma div_lt_div_iff_of_pos_right (hc : 0 < c) : a / c < b / c ↔ a < b := by
  rw [div_lt_iff₀ hc]; rw [div_mul_cancel₀ _ hc.ne']

/--
lemma `inv_le_iff_one_le_mul₀` / 引理 `inv_le_iff_one_le_mul₀`

English:
lemma inv_le_iff_one_le_mul₀
  given: (ha : 0 < a)
  statement: a⁻¹ <= b ↔ 1 <= b * a
  proof: by
  rw [← mul_inv_le_iff₀ ha]; rw [one_mul]

中文:
引理 inv_le_iff_one_le_mul₀
  条件: (ha : 0 < a)
  结论: a⁻¹ <= b ↔ 1 <= b * a
  证明: by
  rw [← mul_inv_le_iff₀ ha]; rw [one_mul]

Depends on / 依赖: one_mul
-/
lemma inv_le_iff_one_le_mul₀ (ha : 0 < a) : a⁻¹ <= b ↔ 1 <= b * a := by
  rw [← mul_inv_le_iff₀ ha]; rw [one_mul]

/--
lemma `inv_lt_iff_one_lt_mul₀` / 引理 `inv_lt_iff_one_lt_mul₀`

English:
lemma inv_lt_iff_one_lt_mul₀
  given: (ha : 0 < a)
  statement: a⁻¹ < b ↔ 1 < b * a
  proof: by
  rw [← mul_inv_lt_iff₀ ha]; rw [one_mul]

中文:
引理 inv_lt_iff_one_lt_mul₀
  条件: (ha : 0 < a)
  结论: a⁻¹ < b ↔ 1 < b * a
  证明: by
  rw [← mul_inv_lt_iff₀ ha]; rw [one_mul]

Depends on / 依赖: one_mul
-/
lemma inv_lt_iff_one_lt_mul₀ (ha : 0 < a) : a⁻¹ < b ↔ 1 < b * a := by
  rw [← mul_inv_lt_iff₀ ha]; rw [one_mul]

/--
lemma `one_le_div₀` / 引理 `one_le_div₀`

English:
lemma one_le_div₀
  given: (hb : 0 < b)
  statement: 1 <= a / b ↔ b <= a
  proof: by rw [le_div_iff₀ hb, one_mul]

中文:
引理 one_le_div₀
  条件: (hb : 0 < b)
  结论: 1 <= a / b ↔ b <= a
  证明: by rw [le_div_iff₀ hb, one_mul]

Depends on / 依赖: one_mul
-/
lemma one_le_div₀ (hb : 0 < b) : 1 <= a / b ↔ b <= a := by rw [le_div_iff₀ hb, one_mul]
/--
lemma `one_lt_div₀` / 引理 `one_lt_div₀`

English:
lemma one_lt_div₀
  given: (hb : 0 < b)
  statement: 1 < a / b ↔ b < a
  proof: by rw [lt_div_iff₀ hb, one_mul]

中文:
引理 one_lt_div₀
  条件: (hb : 0 < b)
  结论: 1 < a / b ↔ b < a
  证明: by rw [lt_div_iff₀ hb, one_mul]

Depends on / 依赖: one_mul
-/
lemma one_lt_div₀ (hb : 0 < b) : 1 < a / b ↔ b < a := by rw [lt_div_iff₀ hb, one_mul]
/--
lemma `div_le_one₀` / 引理 `div_le_one₀`

English:
lemma div_le_one₀
  given: (hb : 0 < b)
  statement: a / b <= 1 ↔ a <= b
  proof: by rw [div_le_iff₀ hb, one_mul]

中文:
引理 div_le_one₀
  条件: (hb : 0 < b)
  结论: a / b <= 1 ↔ a <= b
  证明: by rw [div_le_iff₀ hb, one_mul]

Depends on / 依赖: one_mul
-/
lemma div_le_one₀ (hb : 0 < b) : a / b <= 1 ↔ a <= b := by rw [div_le_iff₀ hb, one_mul]
/--
lemma `div_lt_one₀` / 引理 `div_lt_one₀`

English:
lemma div_lt_one₀
  given: (hb : 0 < b)
  statement: a / b < 1 ↔ a < b
  proof: by rw [div_lt_iff₀ hb, one_mul]

中文:
引理 div_lt_one₀
  条件: (hb : 0 < b)
  结论: a / b < 1 ↔ a < b
  证明: by rw [div_lt_iff₀ hb, one_mul]

Depends on / 依赖: one_mul
-/
lemma div_lt_one₀ (hb : 0 < b) : a / b < 1 ↔ a < b := by rw [div_lt_iff₀ hb, one_mul]

/--
lemma `mul_le_of_le_mul_inv₀` / 引理 `mul_le_of_le_mul_inv₀`

English:
lemma mul_le_of_le_mul_inv₀
  given: (hb : 0 <= b) (hc : 0 <= c) (h : a <= b * c⁻¹)
  statement: a * c <= b
  proof: by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_mul_inv_iff₀ hc] at h

中文:
引理 mul_le_of_le_mul_inv₀
  条件: (hb : 0 <= b) (hc : 0 <= c) (h : a <= b * c⁻¹)
  结论: a * c <= b
  证明: by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_mul_inv_iff₀ hc] at h

Depends on / 依赖: eq_or_lt, hc.eq_or_lt
-/
lemma mul_le_of_le_mul_inv₀ (hb : 0 <= b) (hc : 0 <= c) (h : a <= b * c⁻¹) : a * c <= b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_mul_inv_iff₀ hc] at h

/--
lemma `mul_inv_le_of_le_mul₀` / 引理 `mul_inv_le_of_le_mul₀`

English:
lemma mul_inv_le_of_le_mul₀
  given: (hb : 0 <= b) (hc : 0 <= c) (h : a <= c * b)
  statement: a * b⁻¹ <= c
  proof: by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [mul_inv_le_iff₀ hb]

中文:
引理 mul_inv_le_of_le_mul₀
  条件: (hb : 0 <= b) (hc : 0 <= c) (h : a <= c * b)
  结论: a * b⁻¹ <= c
  证明: by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [mul_inv_le_iff₀ hb]

Depends on / 依赖: eq_or_lt, hb.eq_or_lt
-/
lemma mul_inv_le_of_le_mul₀ (hb : 0 <= b) (hc : 0 <= c) (h : a <= c * b) : a * b⁻¹ <= c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [mul_inv_le_iff₀ hb]

/--
lemma `mul_le_of_le_div₀` / 引理 `mul_le_of_le_div₀`

English:
lemma mul_le_of_le_div₀
  given: (hb : 0 <= b) (hc : 0 <= c) (h : a <= b / c)
  statement: a * c <= b
  proof: mul_le_of_le_mul_inv₀ hb hc (div_eq_mul_inv b _ ▸ h)

中文:
引理 mul_le_of_le_div₀
  条件: (hb : 0 <= b) (hc : 0 <= c) (h : a <= b / c)
  结论: a * c <= b
  证明: mul_le_of_le_mul_inv₀ hb hc (div_eq_mul_inv b _ ▸ h)

Depends on / 依赖: div_eq_mul_inv
-/
lemma mul_le_of_le_div₀ (hb : 0 <= b) (hc : 0 <= c) (h : a <= b / c) : a * c <= b :=
  mul_le_of_le_mul_inv₀ hb hc (div_eq_mul_inv b _ ▸ h)

/--
lemma `div_le_of_le_mul₀` / 引理 `div_le_of_le_mul₀`

English:
lemma div_le_of_le_mul₀
  given: (hb : 0 <= b) (hc : 0 <= c) (h : a <= c * b)
  statement: a / b <= c
  proof: div_eq_mul_inv a _ ▸ mul_inv_le_of_le_mul₀ hb hc h

@[bound]

中文:
引理 div_le_of_le_mul₀
  条件: (hb : 0 <= b) (hc : 0 <= c) (h : a <= c * b)
  结论: a / b <= c
  证明: div_eq_mul_inv a _ ▸ mul_inv_le_of_le_mul₀ hb hc h

@[bound]

Depends on / 依赖: div_eq_mul_inv
-/
lemma div_le_of_le_mul₀ (hb : 0 <= b) (hc : 0 <= c) (h : a <= c * b) : a / b <= c :=
  div_eq_mul_inv a _ ▸ mul_inv_le_of_le_mul₀ hb hc h

@[bound]
/--
lemma `mul_inv_le_one_of_le₀` / 引理 `mul_inv_le_one_of_le₀`

English:
lemma mul_inv_le_one_of_le₀
  given: [ZeroLEOneClass G₀] (h : a <= b) (hb : 0 <= b)
  statement: a * b⁻¹ <= 1
  proof: mul_inv_le_of_le_mul₀ hb zero_le_one by rwa [one_mul]

@[bound]

中文:
引理 mul_inv_le_one_of_le₀
  条件: [ZeroLEOneClass G₀] (h : a <= b) (hb : 0 <= b)
  结论: a * b⁻¹ <= 1
  证明: mul_inv_le_of_le_mul₀ hb zero_le_one by rwa [one_mul]

@[bound]

Depends on / 依赖: one_mul, zero_le_one
-/
lemma mul_inv_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (hb : 0 <= b) : a * b⁻¹ <= 1 :=
mul_inv_le_of_le_mul₀ hb zero_le_one by rwa [one_mul]

@[bound]
/--
lemma `div_le_one_of_le₀` / 引理 `div_le_one_of_le₀`

English:
lemma div_le_one_of_le₀
  given: [ZeroLEOneClass G₀] (h : a <= b) (hb : 0 <= b)
  statement: a / b <= 1
  proof: div_le_of_le_mul₀ hb zero_le_one by rwa [one_mul]

@[mono, gcongr, bound]

中文:
引理 div_le_one_of_le₀
  条件: [ZeroLEOneClass G₀] (h : a <= b) (hb : 0 <= b)
  结论: a / b <= 1
  证明: div_le_of_le_mul₀ hb zero_le_one by rwa [one_mul]

@[mono, gcongr, bound]

Depends on / 依赖: one_mul, zero_le_one
-/
lemma div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (hb : 0 <= b) : a / b <= 1 :=
div_le_of_le_mul₀ hb zero_le_one by rwa [one_mul]

@[mono, gcongr, bound]
/--
lemma `div_le_div_of_nonneg_right` / 引理 `div_le_div_of_nonneg_right`

English:
lemma div_le_div_of_nonneg_right
  given: (hab : a <= b) (hc : 0 <= c)
  statement: a / c <= b / c
  proof: by
  rw [div_eq_mul_inv a c]; rw [div_eq_mul_inv b c]
  gcongr; exact Right.inv_nonneg.2 hc

@[gcongr, bound]

中文:
引理 div_le_div_of_nonneg_right
  条件: (hab : a <= b) (hc : 0 <= c)
  结论: a / c <= b / c
  证明: by
  rw [div_eq_mul_inv a c]; rw [div_eq_mul_inv b c]
  gcongr; exact Right.inv_nonneg.2 hc

@[gcongr, bound]

Depends on / 依赖: Right.inv_nonneg, div_eq_mul_inv, inv_nonneg
-/
lemma div_le_div_of_nonneg_right (hab : a <= b) (hc : 0 <= c) : a / c <= b / c := by
  rw [div_eq_mul_inv a c]; rw [div_eq_mul_inv b c]
  gcongr; exact Right.inv_nonneg.2 hc

@[gcongr, bound]
/--
lemma `div_lt_div_of_pos_right` / 引理 `div_lt_div_of_pos_right`

English:
lemma div_lt_div_of_pos_right
  given: (h : a < b) (hc : 0 < c)
  statement: a / c < b / c
  proof: by
  rw [div_eq_mul_inv a c]; rw [div_eq_mul_inv b c]
  exact mul_lt_mul_of_pos_right h (Right.inv_pos.2 hc)

中文:
引理 div_lt_div_of_pos_right
  条件: (h : a < b) (hc : 0 < c)
  结论: a / c < b / c
  证明: by
  rw [div_eq_mul_inv a c]; rw [div_eq_mul_inv b c]
  exact mul_lt_mul_of_pos_right h (Right.inv_pos.2 hc)

Depends on / 依赖: Right.inv_pos, div_eq_mul_inv, inv_pos, mul_lt_mul_of_pos_right
-/
lemma div_lt_div_of_pos_right (h : a < b) (hc : 0 < c) : a / c < b / c := by
  rw [div_eq_mul_inv a c]; rw [div_eq_mul_inv b c]
  exact mul_lt_mul_of_pos_right h (Right.inv_pos.2 hc)

end MulPosReflectLT

section Both

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulReflectLT.toPosMulReflectLE
  MulPosReflectLT.toMulPosStrictMono MulPosReflectLT.toMulPosReflectLE

/--
lemma `inv_le_inv₀` / 引理 `inv_le_inv₀`

English:
lemma inv_le_inv₀
  given: (ha : 0 < a) (hb : 0 < b)
  statement: a⁻¹ <= b⁻¹ ↔ b <= a
  proof: by
  rw [inv_le_iff_one_le_mul₀' ha]; rw [le_mul_inv_iff₀ hb]; rw [one_mul]

中文:
引理 inv_le_inv₀
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: a⁻¹ <= b⁻¹ ↔ b <= a
  证明: by
  rw [inv_le_iff_one_le_mul₀' ha]; rw [le_mul_inv_iff₀ hb]; rw [one_mul]

Depends on / 依赖: one_mul
-/
lemma inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b⁻¹ ↔ b <= a := by
  rw [inv_le_iff_one_le_mul₀' ha]; rw [le_mul_inv_iff₀ hb]; rw [one_mul]

/--
lemma `inv_lt_inv₀` / 引理 `inv_lt_inv₀`

English:
lemma inv_lt_inv₀
  given: (ha : 0 < a) (hb : 0 < b)
  statement: a⁻¹ < b⁻¹ ↔ b < a
  proof: by
  rw [inv_lt_iff_one_lt_mul₀' ha]; rw [lt_mul_inv_iff₀ hb]; rw [one_mul]

@[gcongr, bound]

中文:
引理 inv_lt_inv₀
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: a⁻¹ < b⁻¹ ↔ b < a
  证明: by
  rw [inv_lt_iff_one_lt_mul₀' ha]; rw [lt_mul_inv_iff₀ hb]; rw [one_mul]

@[gcongr, bound]

Depends on / 依赖: one_mul
-/
lemma inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a := by
  rw [inv_lt_iff_one_lt_mul₀' ha]; rw [lt_mul_inv_iff₀ hb]; rw [one_mul]

@[gcongr, bound]
/--
lemma `inv_anti₀` / 引理 `inv_anti₀`

English:
lemma inv_anti₀
  given: (hb : 0 < b) (hba : b <= a)
  statement: a⁻¹ <= b⁻¹
  proof: (inv_le_inv₀ (hb.trans_le hba) hb).2 hba

@[gcongr, bound]

中文:
引理 inv_anti₀
  条件: (hb : 0 < b) (hba : b <= a)
  结论: a⁻¹ <= b⁻¹
  证明: (inv_le_inv₀ (hb.trans_le hba) hb).2 hba

@[gcongr, bound]

Depends on / 依赖: hb.trans_le, trans_le
-/
lemma inv_anti₀ (hb : 0 < b) (hba : b <= a) : a⁻¹ <= b⁻¹ := (inv_le_inv₀ (hb.trans_le hba) hb).2 hba

@[gcongr, bound]
/--
lemma `inv_strictAnti₀` / 引理 `inv_strictAnti₀`

English:
lemma inv_strictAnti₀
  given: (hb : 0 < b) (hba : b < a)
  statement: a⁻¹ < b⁻¹
  proof: (inv_lt_inv₀ (hb.trans hba) hb).2 hba

中文:
引理 inv_strictAnti₀
  条件: (hb : 0 < b) (hba : b < a)
  结论: a⁻¹ < b⁻¹
  证明: (inv_lt_inv₀ (hb.trans hba) hb).2 hba

Depends on / 依赖: hb.trans
-/
lemma inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹ :=
  (inv_lt_inv₀ (hb.trans hba) hb).2 hba

/--
lemma `strictAntiOn_inv_pos` / 引理 `strictAntiOn_inv_pos`

English:
lemma strictAntiOn_inv_pos
  statement: StrictAntiOn (fun x : G₀ => x⁻¹) {r | 0 < r}
  proof: fun ⦃_⦄ ha ⦃_⦄ _ h => inv_strictAnti₀ (Set.mem_ofPred.mp ha) h

中文:
引理 strictAntiOn_inv_pos
  结论: StrictAntiOn (fun x : G₀ => x⁻¹) {r | 0 < r}
  证明: fun ⦃_⦄ ha ⦃_⦄ _ h => inv_strictAnti₀ (Set.mem_ofPred.mp ha) h

Depends on / 依赖: Set.mem_ofPred.mp, mem_ofPred
-/
lemma strictAntiOn_inv_pos : StrictAntiOn (fun x : G₀ => x⁻¹) {r | 0 < r} :=
  fun ⦃_⦄ ha ⦃_⦄ _ h => inv_strictAnti₀ (Set.mem_ofPred.mp ha) h

/--
lemma `antitoneOn_inv_pos` / 引理 `antitoneOn_inv_pos`

English:
lemma antitoneOn_inv_pos
  statement: AntitoneOn (fun x : G₀ => x⁻¹) {r | 0 < r}
  proof: strictAntiOn_inv_pos.antitoneOn

中文:
引理 antitoneOn_inv_pos
  结论: AntitoneOn (fun x : G₀ => x⁻¹) {r | 0 < r}
  证明: strictAntiOn_inv_pos.antitoneOn

Depends on / 依赖: antitoneOn, strictAntiOn_inv_pos, strictAntiOn_inv_pos.antitoneOn
-/
lemma antitoneOn_inv_pos : AntitoneOn (fun x : G₀ => x⁻¹) {r | 0 < r} :=
  strictAntiOn_inv_pos.antitoneOn

/--
lemma `inv_le_comm₀` / 引理 `inv_le_comm₀`

English:
lemma inv_le_comm₀
  given: (ha : 0 < a) (hb : 0 < b)
  statement: a⁻¹ <= b ↔ b⁻¹ <= a
  proof: by
  rw [← inv_le_inv₀ hb (inv_pos.2 ha)]; rw [inv_inv]

中文:
引理 inv_le_comm₀
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: a⁻¹ <= b ↔ b⁻¹ <= a
  证明: by
  rw [← inv_le_inv₀ hb (inv_pos.2 ha)]; rw [inv_inv]

Depends on / 依赖: inv_inv, inv_pos
-/
lemma inv_le_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b ↔ b⁻¹ <= a := by
  rw [← inv_le_inv₀ hb (inv_pos.2 ha)]; rw [inv_inv]

/--
lemma `inv_lt_comm₀` / 引理 `inv_lt_comm₀`

English:
lemma inv_lt_comm₀
  given: (ha : 0 < a) (hb : 0 < b)
  statement: a⁻¹ < b ↔ b⁻¹ < a
  proof: by
  rw [← inv_lt_inv₀ hb (inv_pos.2 ha)]; rw [inv_inv]

中文:
引理 inv_lt_comm₀
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: a⁻¹ < b ↔ b⁻¹ < a
  证明: by
  rw [← inv_lt_inv₀ hb (inv_pos.2 ha)]; rw [inv_inv]

Depends on / 依赖: inv_inv, inv_pos
-/
lemma inv_lt_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a := by
  rw [← inv_lt_inv₀ hb (inv_pos.2 ha)]; rw [inv_inv]

/--
lemma `inv_le_of_inv_le₀` / 引理 `inv_le_of_inv_le₀`

English:
lemma inv_le_of_inv_le₀
  given: (ha : 0 < a) (h : a⁻¹ <= b)
  statement: b⁻¹ <= a
  proof: (inv_le_comm₀ ha <| (inv_pos.2 ha).trans_le h).1 h

中文:
引理 inv_le_of_inv_le₀
  条件: (ha : 0 < a) (h : a⁻¹ <= b)
  结论: b⁻¹ <= a
  证明: (inv_le_comm₀ ha <| (inv_pos.2 ha).trans_le h).1 h

Depends on / 依赖: inv_pos, trans_le
-/
lemma inv_le_of_inv_le₀ (ha : 0 < a) (h : a⁻¹ <= b) : b⁻¹ <= a :=
  (inv_le_comm₀ ha <| (inv_pos.2 ha).trans_le h).1 h

/--
lemma `inv_lt_of_inv_lt₀` / 引理 `inv_lt_of_inv_lt₀`

English:
lemma inv_lt_of_inv_lt₀
  given: (ha : 0 < a) (h : a⁻¹ < b)
  statement: b⁻¹ < a
  proof: (inv_lt_comm₀ ha <| (inv_pos.2 ha).trans h).1 h

中文:
引理 inv_lt_of_inv_lt₀
  条件: (ha : 0 < a) (h : a⁻¹ < b)
  结论: b⁻¹ < a
  证明: (inv_lt_comm₀ ha <| (inv_pos.2 ha).trans h).1 h

Depends on / 依赖: inv_pos
-/
lemma inv_lt_of_inv_lt₀ (ha : 0 < a) (h : a⁻¹ < b) : b⁻¹ < a :=
  (inv_lt_comm₀ ha <| (inv_pos.2 ha).trans h).1 h

/--
lemma `le_inv_comm₀` / 引理 `le_inv_comm₀`

English:
lemma le_inv_comm₀
  given: (ha : 0 < a) (hb : 0 < b)
  statement: a <= b⁻¹ ↔ b <= a⁻¹
  proof: by
  rw [← inv_le_inv₀ (inv_pos.2 hb) ha]; rw [inv_inv]

中文:
引理 le_inv_comm₀
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: a <= b⁻¹ ↔ b <= a⁻¹
  证明: by
  rw [← inv_le_inv₀ (inv_pos.2 hb) ha]; rw [inv_inv]

Depends on / 依赖: inv_inv, inv_pos
-/
lemma le_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a <= b⁻¹ ↔ b <= a⁻¹ := by
  rw [← inv_le_inv₀ (inv_pos.2 hb) ha]; rw [inv_inv]

/--
lemma `lt_inv_comm₀` / 引理 `lt_inv_comm₀`

English:
lemma lt_inv_comm₀
  given: (ha : 0 < a) (hb : 0 < b)
  statement: a < b⁻¹ ↔ b < a⁻¹
  proof: by
  rw [← inv_lt_inv₀ (inv_pos.2 hb) ha]; rw [inv_inv]

中文:
引理 lt_inv_comm₀
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: a < b⁻¹ ↔ b < a⁻¹
  证明: by
  rw [← inv_lt_inv₀ (inv_pos.2 hb) ha]; rw [inv_inv]

Depends on / 依赖: inv_inv, inv_pos
-/
lemma lt_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ := by
  rw [← inv_lt_inv₀ (inv_pos.2 hb) ha]; rw [inv_inv]

/--
lemma `le_inv_of_le_inv₀` / 引理 `le_inv_of_le_inv₀`

English:
lemma le_inv_of_le_inv₀
  given: (ha : 0 < a) (h : a <= b⁻¹)
  statement: b <= a⁻¹
  proof: (le_inv_comm₀ ha <| inv_pos.1 <| ha.trans_le h).1 h

中文:
引理 le_inv_of_le_inv₀
  条件: (ha : 0 < a) (h : a <= b⁻¹)
  结论: b <= a⁻¹
  证明: (le_inv_comm₀ ha <| inv_pos.1 <| ha.trans_le h).1 h

Depends on / 依赖: ha.trans_le, inv_pos, trans_le
-/
lemma le_inv_of_le_inv₀ (ha : 0 < a) (h : a <= b⁻¹) : b <= a⁻¹ :=
  (le_inv_comm₀ ha <| inv_pos.1 <| ha.trans_le h).1 h

/--
lemma `lt_inv_of_lt_inv₀` / 引理 `lt_inv_of_lt_inv₀`

English:
lemma lt_inv_of_lt_inv₀
  given: (ha : 0 < a) (h : a < b⁻¹)
  statement: b < a⁻¹
  proof: (lt_inv_comm₀ ha <| inv_pos.1 <| ha.trans h).1 h

中文:
引理 lt_inv_of_lt_inv₀
  条件: (ha : 0 < a) (h : a < b⁻¹)
  结论: b < a⁻¹
  证明: (lt_inv_comm₀ ha <| inv_pos.1 <| ha.trans h).1 h

Depends on / 依赖: ha.trans, inv_pos
-/
lemma lt_inv_of_lt_inv₀ (ha : 0 < a) (h : a < b⁻¹) : b < a⁻¹ :=
  (lt_inv_comm₀ ha <| inv_pos.1 <| ha.trans h).1 h

/--
lemma `div_le_div_iff_of_pos_left` / 引理 `div_le_div_iff_of_pos_left`

English:
lemma div_le_div_iff_of_pos_left
  given: (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  proof: by
  simp only [div_eq_mul_inv, mul_le_mul_iff_right₀ ha, inv_le_inv₀ hb hc]

中文:
引理 div_le_div_iff_of_pos_left
  条件: (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  证明: by
  simp only [div_eq_mul_inv, mul_le_mul_iff_right₀ ha, inv_le_inv₀ hb hc]

Depends on / 依赖: div_eq_mul_inv
-/
lemma div_le_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b <= a / c ↔ c <= b := by
  simp only [div_eq_mul_inv, mul_le_mul_iff_right₀ ha, inv_le_inv₀ hb hc]

/--
lemma `div_lt_div_iff_of_pos_left` / 引理 `div_lt_div_iff_of_pos_left`

English:
lemma div_lt_div_iff_of_pos_left
  given: (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  statement: a / b < a / c ↔ c < b
  proof: lt_iff_lt_of_le_iff_le' (div_le_div_iff_of_pos_left ha hc hb)
    (div_le_div_iff_of_pos_left ha hb hc)

中文:
引理 div_lt_div_iff_of_pos_left
  条件: (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  结论: a / b < a / c ↔ c < b
  证明: lt_iff_lt_of_le_iff_le' (div_le_div_iff_of_pos_left ha hc hb)
    (div_le_div_iff_of_pos_left ha hb hc)

Depends on / 依赖: div_le_div_iff_of_pos_left, lt_iff_lt_of_le_iff_le
-/
lemma div_lt_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b :=
  lt_iff_lt_of_le_iff_le' (div_le_div_iff_of_pos_left ha hc hb)
    (div_le_div_iff_of_pos_left ha hb hc)

-- Not a `mono` lemma b/c `div_le_div₀` is strictly more general
/--
lemma `div_le_div_of_nonneg_left` / 引理 `div_le_div_of_nonneg_left`

English:
lemma div_le_div_of_nonneg_left
  given: (ha : 0 <= a) (hc : 0 < c) (h : c <= b)
  statement: a / b <= a / c
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  gcongr
  exacts [ha, hc]

@[gcongr, bound]

中文:
引理 div_le_div_of_nonneg_left
  条件: (ha : 0 <= a) (hc : 0 < c) (h : c <= b)
  结论: a / b <= a / c
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  gcongr
  exacts [ha, hc]

@[gcongr, bound]

Depends on / 依赖: div_eq_mul_inv, exacts
-/
lemma div_le_div_of_nonneg_left (ha : 0 <= a) (hc : 0 < c) (h : c <= b) : a / b <= a / c := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  gcongr
  exacts [ha, hc]

@[gcongr, bound]
/--
lemma `div_lt_div_of_pos_left` / 引理 `div_lt_div_of_pos_left`

English:
lemma div_lt_div_of_pos_left
  given: (ha : 0 < a) (hc : 0 < c) (h : c < b)
  statement: a / b < a / c
  proof: (div_lt_div_iff_of_pos_left ha (hc.trans h) hc).mpr h

@[mono, gcongr, bound]

中文:
引理 div_lt_div_of_pos_left
  条件: (ha : 0 < a) (hc : 0 < c) (h : c < b)
  结论: a / b < a / c
  证明: (div_lt_div_iff_of_pos_left ha (hc.trans h) hc).mpr h

@[mono, gcongr, bound]

Depends on / 依赖: div_lt_div_iff_of_pos_left, hc.trans
-/
lemma div_lt_div_of_pos_left (ha : 0 < a) (hc : 0 < c) (h : c < b) : a / b < a / c :=
  (div_lt_div_iff_of_pos_left ha (hc.trans h) hc).mpr h

@[mono, gcongr, bound]
/--
lemma `div_le_div₀` / 引理 `div_le_div₀`

English:
lemma div_le_div₀
  given: (hc : 0 <= c) (hac : a <= c) (hd : 0 < d) (hdb : d <= b)
  statement: a / b <= c / d
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  gcongr
  exacts [inv_nonneg.2 <| hd.le.trans hdb, hc, hd]

@[gcongr]

中文:
引理 div_le_div₀
  条件: (hc : 0 <= c) (hac : a <= c) (hd : 0 < d) (hdb : d <= b)
  结论: a / b <= c / d
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  gcongr
  exacts [inv_nonneg.2 <| hd.le.trans hdb, hc, hd]

@[gcongr]

Depends on / 依赖: div_eq_mul_inv, exacts, hd.le.trans, inv_nonneg
-/
lemma div_le_div₀ (hc : 0 <= c) (hac : a <= c) (hd : 0 < d) (hdb : d <= b) : a / b <= c / d := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  gcongr
  exacts [inv_nonneg.2 <| hd.le.trans hdb, hc, hd]

@[gcongr]
/--
lemma `div_lt_div₀` / 引理 `div_lt_div₀`

English:
lemma div_lt_div₀
  given: (hac : a < c) (hdb : d <= b) (hc : 0 <= c) (hd : 0 < d)
  statement: a / b < c / d
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  apply mul_lt_mul hac (by gcongr; assumption) _ hc
  exact inv_pos.2 (hd.trans_le hdb)

中文:
引理 div_lt_div₀
  条件: (hac : a < c) (hdb : d <= b) (hc : 0 <= c) (hd : 0 < d)
  结论: a / b < c / d
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  apply mul_lt_mul hac (by gcongr; assumption) _ hc
  exact inv_pos.2 (hd.trans_le hdb)

Depends on / 依赖: div_eq_mul_inv, hd.trans_le, inv_pos, mul_lt_mul, trans_le
-/
lemma div_lt_div₀ (hac : a < c) (hdb : d <= b) (hc : 0 <= c) (hd : 0 < d) : a / b < c / d := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  apply mul_lt_mul hac (by gcongr; assumption) _ hc
  exact inv_pos.2 (hd.trans_le hdb)

/--
lemma `div_lt_div₀'` / 引理 `div_lt_div₀'`

English:
lemma div_lt_div₀'
  given: (hac : a <= c) (hdb : d < b) (hc : 0 < c) (hd : 0 < d)
  statement: a / b < c / d
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact mul_lt_mul' hac ((inv_lt_inv₀ (hd.trans hdb) hd).2 hdb)
    (inv_nonneg.2 <| hd.le.trans hdb.le) hc

中文:
引理 div_lt_div₀'
  条件: (hac : a <= c) (hdb : d < b) (hc : 0 < c) (hd : 0 < d)
  结论: a / b < c / d
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact mul_lt_mul' hac ((inv_lt_inv₀ (hd.trans hdb) hd).2 hdb)
    (inv_nonneg.2 <| hd.le.trans hdb.le) hc

Depends on / 依赖: div_eq_mul_inv, hd.le.trans, hd.trans, hdb.le, inv_nonneg, mul_lt_mul
-/
lemma div_lt_div₀' (hac : a <= c) (hdb : d < b) (hc : 0 < c) (hd : 0 < d) : a / b < c / d := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact mul_lt_mul' hac ((inv_lt_inv₀ (hd.trans hdb) hd).2 hdb)
    (inv_nonneg.2 <| hd.le.trans hdb.le) hc

end Both

end PartialOrder

section LinearOrder
variable [LinearOrder G₀] {a b c d : G₀}

section PosMulMono
variable [PosMulMono G₀]

/--
lemma `inv_neg''` / 引理 `inv_neg''`

English:
lemma inv_neg''
  statement: a⁻¹ < 0 ↔ a < 0
  proof: by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_le, inv_nonneg]

中文:
引理 inv_neg''
  结论: a⁻¹ < 0 ↔ a < 0
  证明: by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_le, inv_nonneg]
-/
@[simp] lemma inv_neg'' : a⁻¹ < 0 ↔ a < 0 := by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_le, inv_nonneg]

/--
lemma `inv_nonpos` / 引理 `inv_nonpos`

English:
lemma inv_nonpos
  statement: a⁻¹ <= 0 ↔ a <= 0
  proof: by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_lt, inv_pos]

alias inv_lt_zero := inv_neg''

中文:
引理 inv_nonpos
  结论: a⁻¹ <= 0 ↔ a <= 0
  证明: by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_lt, inv_pos]

alias inv_lt_zero := inv_neg''
-/
@[simp] lemma inv_nonpos : a⁻¹ <= 0 ↔ a <= 0 := by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_lt, inv_pos]

alias inv_lt_zero := inv_neg''

/--
lemma `one_div_neg` / 引理 `one_div_neg`

English:
lemma one_div_neg
  statement: 1 / a < 0 ↔ a < 0
  proof: one_div a ▸ inv_neg''

中文:
引理 one_div_neg
  结论: 1 / a < 0 ↔ a < 0
  证明: one_div a ▸ inv_neg''

Depends on / 依赖: inv_neg, one_div
-/
lemma one_div_neg : 1 / a < 0 ↔ a < 0 := one_div a ▸ inv_neg''
/--
lemma `one_div_nonpos` / 引理 `one_div_nonpos`

English:
lemma one_div_nonpos
  statement: 1 / a <= 0 ↔ a <= 0
  proof: one_div a ▸ inv_nonpos

中文:
引理 one_div_nonpos
  结论: 1 / a <= 0 ↔ a <= 0
  证明: one_div a ▸ inv_nonpos

Depends on / 依赖: inv_nonpos, one_div
-/
lemma one_div_nonpos : 1 / a <= 0 ↔ a <= 0 := one_div a ▸ inv_nonpos

/--
lemma `div_nonpos_of_nonneg_of_nonpos` / 引理 `div_nonpos_of_nonneg_of_nonpos`

English:
lemma div_nonpos_of_nonneg_of_nonpos
  given: (ha : 0 <= a) (hb : b <= 0)
  statement: a / b <= 0
  proof: by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)

中文:
引理 div_nonpos_of_nonneg_of_nonpos
  条件: (ha : 0 <= a) (hb : b <= 0)
  结论: a / b <= 0
  证明: by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)

Depends on / 依赖: div_eq_mul_inv, inv_nonpos, mul_nonpos_of_nonneg_of_nonpos
-/
lemma div_nonpos_of_nonneg_of_nonpos (ha : 0 <= a) (hb : b <= 0) : a / b <= 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)

/--
lemma `neg_of_div_neg_right` / 引理 `neg_of_div_neg_right`

English:
lemma neg_of_div_neg_right
  given: (h : a / b < 0) (ha : 0 <= a)
  statement: b < 0
  proof: have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun hb => (div_nonneg ha hb).not_gt h

中文:
引理 neg_of_div_neg_right
  条件: (h : a / b < 0) (ha : 0 <= a)
  结论: b < 0
  证明: have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun hb => (div_nonneg ha hb).not_gt h

Depends on / 依赖: PosMulMono, PosMulMono.toPosMulReflectLT, div_nonneg, lt_of_not_ge, not_gt, toPosMulReflectLT
-/
lemma neg_of_div_neg_right (h : a / b < 0) (ha : 0 <= a) : b < 0 :=
  have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun hb => (div_nonneg ha hb).not_gt h

/--
lemma `neg_of_div_neg_left` / 引理 `neg_of_div_neg_left`

English:
lemma neg_of_div_neg_left
  given: (h : a / b < 0) (hb : 0 <= b)
  statement: a < 0
  proof: have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun ha => (div_nonneg ha hb).not_gt h

中文:
引理 neg_of_div_neg_left
  条件: (h : a / b < 0) (hb : 0 <= b)
  结论: a < 0
  证明: have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun ha => (div_nonneg ha hb).not_gt h

Depends on / 依赖: PosMulMono, PosMulMono.toPosMulReflectLT, div_nonneg, lt_of_not_ge, not_gt, toPosMulReflectLT
-/
lemma neg_of_div_neg_left (h : a / b < 0) (hb : 0 <= b) : a < 0 :=
  have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun ha => (div_nonneg ha hb).not_gt h

end PosMulMono

variable {m n : Int}

section ZeroLEOne

variable [PosMulStrictMono G₀]

variable [ZeroLEOneClass G₀]

/--
lemma `inv_lt_one_iff₀` / 引理 `inv_lt_one_iff₀`

English:
lemma inv_lt_one_iff₀
  statement: a⁻¹ < 1 ↔ a <= 0 ∨ 1 < a
  proof: by
  simp_rw [← not_le, one_le_inv_iff₀, not_and_or, not_lt]

中文:
引理 inv_lt_one_iff₀
  结论: a⁻¹ < 1 ↔ a <= 0 ∨ 1 < a
  证明: by
  simp_rw [← not_le, one_le_inv_iff₀, not_and_or, not_lt]

Depends on / 依赖: not_and_or, not_le, not_lt, simp_rw
-/
lemma inv_lt_one_iff₀ : a⁻¹ < 1 ↔ a <= 0 ∨ 1 < a := by
  simp_rw [← not_le, one_le_inv_iff₀, not_and_or, not_lt]

/--
lemma `inv_le_one_iff₀` / 引理 `inv_le_one_iff₀`

English:
lemma inv_le_one_iff₀
  statement: a⁻¹ <= 1 ↔ a <= 0 ∨ 1 <= a
  proof: by
  simp only [← not_lt, one_lt_inv_iff₀, not_and_or]

中文:
引理 inv_le_one_iff₀
  结论: a⁻¹ <= 1 ↔ a <= 0 ∨ 1 <= a
  证明: by
  simp only [← not_lt, one_lt_inv_iff₀, not_and_or]

Depends on / 依赖: not_and_or, not_lt
-/
lemma inv_le_one_iff₀ : a⁻¹ <= 1 ↔ a <= 0 ∨ 1 <= a := by
  simp only [← not_lt, one_lt_inv_iff₀, not_and_or]

/--
lemma `zpow_right_injective₀` / 引理 `zpow_right_injective₀`

English:
lemma zpow_right_injective₀
  given: (ha₀ : 0 < a) (ha₁ : a != 1)
  statement: Injective fun n : Int => a ^ n
  proof: by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (zpow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (zpow_right_strictMono₀ ha₁).injective

中文:
引理 zpow_right_injective₀
  条件: (ha₀ : 0 < a) (ha₁ : a != 1)
  结论: Injective fun n : 整数 => a ^ n
  证明: by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (zpow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (zpow_right_strictMono₀ ha₁).injective

Depends on / 依赖: injective, lt_or_gt
-/
lemma zpow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a != 1) : Injective fun n : Int => a ^ n := by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (zpow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (zpow_right_strictMono₀ ha₁).injective

/--
lemma `zpow_right_inj₀` / 引理 `zpow_right_inj₀`

English:
lemma zpow_right_inj₀
  given: (ha₀ : 0 < a) (ha₁ : a != 1)
  statement: a ^ m = a ^ n ↔ m = n
  proof: (zpow_right_injective₀ ha₀ ha₁).eq_iff

中文:
引理 zpow_right_inj₀
  条件: (ha₀ : 0 < a) (ha₁ : a != 1)
  结论: a ^ m = a ^ n ↔ m = n
  证明: (zpow_right_injective₀ ha₀ ha₁).eq_iff
-/
@[simp] lemma zpow_right_inj₀ (ha₀ : 0 < a) (ha₁ : a != 1) : a ^ m = a ^ n ↔ m = n :=
  (zpow_right_injective₀ ha₀ ha₁).eq_iff

/--
lemma `zpow_eq_one_iff_right₀` / 引理 `zpow_eq_one_iff_right₀`

English:
lemma zpow_eq_one_iff_right₀
  given: (ha₀ : 0 <= a) (ha₁ : a != 1) {n : Int}
  statement: a ^ n = 1 ↔ n = 0
  proof: by
  obtain rfl | ha₀ := ha₀.eq_or_lt
  · exact zero_zpow_eq_one₀
  simpa using zpow_right_inj₀ ha₀ ha₁ (n := 0)

中文:
引理 zpow_eq_one_iff_right₀
  条件: (ha₀ : 0 <= a) (ha₁ : a != 1) {n : 整数}
  结论: a ^ n = 1 ↔ n = 0
  证明: by
  obtain rfl | ha₀ := ha₀.eq_or_lt
  · exact zero_zpow_eq_one₀
  simpa using zpow_right_inj₀ ha₀ ha₁ (n := 0)

Depends on / 依赖: eq_or_lt
-/
lemma zpow_eq_one_iff_right₀ (ha₀ : 0 <= a) (ha₁ : a != 1) {n : Int} : a ^ n = 1 ↔ n = 0 := by
  obtain rfl | ha₀ := ha₀.eq_or_lt
  · exact zero_zpow_eq_one₀
  simpa using zpow_right_inj₀ ha₀ ha₁ (n := 0)

end ZeroLEOne

section MulPosMono

variable [PosMulReflectLT G₀] [MulPosMono G₀]

/--
lemma `zpow_le_zpow_iff_left₀` / 引理 `zpow_le_zpow_iff_left₀`

English:
lemma zpow_le_zpow_iff_left₀
  given: (ha : 0 <= a) (hb : 0 <= b) (hn : 0 < n)
  statement: a ^ n <= b ^ n ↔ a <= b
  proof: (zpow_left_strictMonoOn₀ (G₀ := G₀) hn).le_iff_le ha hb

中文:
引理 zpow_le_zpow_iff_left₀
  条件: (ha : 0 <= a) (hb : 0 <= b) (hn : 0 < n)
  结论: a ^ n <= b ^ n ↔ a <= b
  证明: (zpow_left_strictMonoOn₀ (G₀ := G₀) hn).le_iff_le ha hb

Depends on / 依赖: le_iff_le
-/
lemma zpow_le_zpow_iff_left₀ (ha : 0 <= a) (hb : 0 <= b) (hn : 0 < n) : a ^ n <= b ^ n ↔ a <= b :=
  (zpow_left_strictMonoOn₀ (G₀ := G₀) hn).le_iff_le ha hb

/--
lemma `zpow_lt_zpow_iff_left₀` / 引理 `zpow_lt_zpow_iff_left₀`

English:
lemma zpow_lt_zpow_iff_left₀
  given: (ha : 0 <= a) (hb : 0 <= b) (hn : 0 < n)
  statement: a ^ n < b ^ n ↔ a < b
  proof: (zpow_left_strictMonoOn₀ (G₀ := G₀) hn).lt_iff_lt ha hb

中文:
引理 zpow_lt_zpow_iff_left₀
  条件: (ha : 0 <= a) (hb : 0 <= b) (hn : 0 < n)
  结论: a ^ n < b ^ n ↔ a < b
  证明: (zpow_left_strictMonoOn₀ (G₀ := G₀) hn).lt_iff_lt ha hb

Depends on / 依赖: lt_iff_lt
-/
lemma zpow_lt_zpow_iff_left₀ (ha : 0 <= a) (hb : 0 <= b) (hn : 0 < n) : a ^ n < b ^ n ↔ a < b :=
  (zpow_left_strictMonoOn₀ (G₀ := G₀) hn).lt_iff_lt ha hb

end MulPosMono

section PosMulStrictMono
variable [PosMulStrictMono G₀] [MulPosMono G₀]

/--
lemma `zpow_left_injOn₀` / 引理 `zpow_left_injOn₀`

English:
lemma zpow_left_injOn₀
  statement: forall {n : Int}, n != 0 -> {a | 0 <= a}.InjOn fun a : G₀ => a ^ n

中文:
引理 zpow_left_injOn₀
  结论: 对任意 {n : 整数}, n != 0 -> {a | 0 <= a}.InjOn fun a : G₀ => a ^ n
-/
lemma zpow_left_injOn₀ : forall {n : Int}, n != 0 -> {a | 0 <= a}.InjOn fun a : G₀ => a ^ n
  | (n + 1 : Nat), _ => by simpa using! mod_cast (pow_left_strictMonoOn₀ n.succ_ne_zero).injOn
  | .negSucc n, _ => by
    simpa using! inv_injective.comp_injOn (pow_left_strictMonoOn₀ n.succ_ne_zero).injOn

/--
lemma `zpow_left_inj₀` / 引理 `zpow_left_inj₀`

English:
lemma zpow_left_inj₀
  given: (ha : 0 <= a) (hb : 0 <= b) (hn : n != 0)
  proof: (zpow_left_injOn₀ hn).eq_iff ha hb

中文:
引理 zpow_left_inj₀
  条件: (ha : 0 <= a) (hb : 0 <= b) (hn : n != 0)
  证明: (zpow_left_injOn₀ hn).eq_iff ha hb

Depends on / 依赖: eq_iff
-/
lemma zpow_left_inj₀ (ha : 0 <= a) (hb : 0 <= b) (hn : n != 0) :
    a ^ n = b ^ n ↔ a = b := (zpow_left_injOn₀ hn).eq_iff ha hb

end PosMulStrictMono
end GroupWithZero.LinearOrder

section CommGroupWithZero

section Preorder
variable [CommGroupWithZero G₀] [Preorder G₀] {a b c : G₀}

/--
lemma `mul_div_mul_left_le` / 引理 `mul_div_mul_left_le`

English:
lemma mul_div_mul_left_le
  given: (h : 0 <= a / b)
  statement: c * a / (c * b) <= a / b
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

中文:
引理 mul_div_mul_left_le
  条件: (h : 0 <= a / b)
  结论: c * a / (c * b) <= a / b
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

Depends on / 依赖: eq_or_ne, mul_div_mul_left
-/
lemma mul_div_mul_left_le (h : 0 <= a / b) : c * a / (c * b) <= a / b := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

/--
lemma `le_mul_div_mul_left` / 引理 `le_mul_div_mul_left`

English:
lemma le_mul_div_mul_left
  given: (h : a / b <= 0)
  statement: a / b <= c * a / (c * b)
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

中文:
引理 le_mul_div_mul_left
  条件: (h : a / b <= 0)
  结论: a / b <= c * a / (c * b)
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

Depends on / 依赖: eq_or_ne, mul_div_mul_left
-/
lemma le_mul_div_mul_left (h : a / b <= 0) : a / b <= c * a / (c * b) := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

end Preorder

variable [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c d : G₀}

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulMono.toMulPosMono
  PosMulStrictMono.toMulPosStrictMono PosMulReflectLT.toMulPosReflectLT

/--
lemma `le_inv_mul_iff₀'` / 引理 `le_inv_mul_iff₀'`

English:
lemma le_inv_mul_iff₀'
  given: (hc : 0 < c)
  statement: a <= c⁻¹ * b ↔ a * c <= b
  proof: by
  rw [le_inv_mul_iff₀ hc]; rw [mul_comm]

中文:
引理 le_inv_mul_iff₀'
  条件: (hc : 0 < c)
  结论: a <= c⁻¹ * b ↔ a * c <= b
  证明: by
  rw [le_inv_mul_iff₀ hc]; rw [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma le_inv_mul_iff₀' (hc : 0 < c) : a <= c⁻¹ * b ↔ a * c <= b := by
  rw [le_inv_mul_iff₀ hc]; rw [mul_comm]

/--
lemma `inv_mul_le_iff₀'` / 引理 `inv_mul_le_iff₀'`

English:
lemma inv_mul_le_iff₀'
  given: (hc : 0 < c)
  statement: c⁻¹ * b <= a ↔ b <= a * c
  proof: by
  rw [inv_mul_le_iff₀ hc]; rw [mul_comm]

中文:
引理 inv_mul_le_iff₀'
  条件: (hc : 0 < c)
  结论: c⁻¹ * b <= a ↔ b <= a * c
  证明: by
  rw [inv_mul_le_iff₀ hc]; rw [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma inv_mul_le_iff₀' (hc : 0 < c) : c⁻¹ * b <= a ↔ b <= a * c := by
  rw [inv_mul_le_iff₀ hc]; rw [mul_comm]

/--
lemma `le_mul_inv_iff₀'` / 引理 `le_mul_inv_iff₀'`

English:
lemma le_mul_inv_iff₀'
  given: (hc : 0 < c)
  statement: a <= b * c⁻¹ ↔ c * a <= b
  proof: by
  rw [le_mul_inv_iff₀ hc]; rw [mul_comm]

中文:
引理 le_mul_inv_iff₀'
  条件: (hc : 0 < c)
  结论: a <= b * c⁻¹ ↔ c * a <= b
  证明: by
  rw [le_mul_inv_iff₀ hc]; rw [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma le_mul_inv_iff₀' (hc : 0 < c) : a <= b * c⁻¹ ↔ c * a <= b := by
  rw [le_mul_inv_iff₀ hc]; rw [mul_comm]

/--
lemma `mul_inv_le_iff₀'` / 引理 `mul_inv_le_iff₀'`

English:
lemma mul_inv_le_iff₀'
  given: (hc : 0 < c)
  statement: b * c⁻¹ <= a ↔ b <= c * a
  proof: by
  rw [mul_inv_le_iff₀ hc]; rw [mul_comm]

中文:
引理 mul_inv_le_iff₀'
  条件: (hc : 0 < c)
  结论: b * c⁻¹ <= a ↔ b <= c * a
  证明: by
  rw [mul_inv_le_iff₀ hc]; rw [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma mul_inv_le_iff₀' (hc : 0 < c) : b * c⁻¹ <= a ↔ b <= c * a := by
  rw [mul_inv_le_iff₀ hc]; rw [mul_comm]

/--
lemma `div_le_div_iff₀` / 引理 `div_le_div_iff₀`

English:
lemma div_le_div_iff₀
  given: (hb : 0 < b) (hd : 0 < d)
  statement: a / b <= c / d ↔ a * d <= c * b
  proof: by
  rw [div_le_iff₀ hb]; rw [← mul_div_right_comm]; rw [le_div_iff₀ hd]

中文:
引理 div_le_div_iff₀
  条件: (hb : 0 < b) (hd : 0 < d)
  结论: a / b <= c / d ↔ a * d <= c * b
  证明: by
  rw [div_le_iff₀ hb]; rw [← mul_div_right_comm]; rw [le_div_iff₀ hd]

Depends on / 依赖: mul_div_right_comm
-/
lemma div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b <= c / d ↔ a * d <= c * b := by
  rw [div_le_iff₀ hb]; rw [← mul_div_right_comm]; rw [le_div_iff₀ hd]

/--
lemma `le_div_iff₀'` / 引理 `le_div_iff₀'`

English:
lemma le_div_iff₀'
  given: (hc : 0 < c)
  statement: a <= b / c ↔ c * a <= b
  proof: by
  rw [le_div_iff₀ hc]; rw [mul_comm]

中文:
引理 le_div_iff₀'
  条件: (hc : 0 < c)
  结论: a <= b / c ↔ c * a <= b
  证明: by
  rw [le_div_iff₀ hc]; rw [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b := by
  rw [le_div_iff₀ hc]; rw [mul_comm]

/--
lemma `div_le_iff₀'` / 引理 `div_le_iff₀'`

English:
lemma div_le_iff₀'
  given: (hc : 0 < c)
  statement: b / c <= a ↔ b <= c * a
  proof: by
  rw [div_le_iff₀ hc]; rw [mul_comm]

中文:
引理 div_le_iff₀'
  条件: (hc : 0 < c)
  结论: b / c <= a ↔ b <= c * a
  证明: by
  rw [div_le_iff₀ hc]; rw [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma div_le_iff₀' (hc : 0 < c) : b / c <= a ↔ b <= c * a := by
  rw [div_le_iff₀ hc]; rw [mul_comm]

/--
lemma `le_div_comm₀` / 引理 `le_div_comm₀`

English:
lemma le_div_comm₀
  given: (ha : 0 < a) (hc : 0 < c)
  statement: a <= b / c ↔ c <= b / a
  proof: by
  rw [le_div_iff₀ ha]; rw [le_div_iff₀' hc]

中文:
引理 le_div_comm₀
  条件: (ha : 0 < a) (hc : 0 < c)
  结论: a <= b / c ↔ c <= b / a
  证明: by
  rw [le_div_iff₀ ha]; rw [le_div_iff₀' hc]
-/
lemma le_div_comm₀ (ha : 0 < a) (hc : 0 < c) : a <= b / c ↔ c <= b / a := by
  rw [le_div_iff₀ ha]; rw [le_div_iff₀' hc]

/--
lemma `div_le_comm₀` / 引理 `div_le_comm₀`

English:
lemma div_le_comm₀
  given: (hb : 0 < b) (hc : 0 < c)
  statement: a / b <= c ↔ a / c <= b
  proof: by
  rw [div_le_iff₀ hb]; rw [div_le_iff₀' hc]

中文:
引理 div_le_comm₀
  条件: (hb : 0 < b) (hc : 0 < c)
  结论: a / b <= c ↔ a / c <= b
  证明: by
  rw [div_le_iff₀ hb]; rw [div_le_iff₀' hc]
-/
lemma div_le_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b <= c ↔ a / c <= b := by
  rw [div_le_iff₀ hb]; rw [div_le_iff₀' hc]

/--
lemma `lt_inv_mul_iff₀'` / 引理 `lt_inv_mul_iff₀'`

English:
lemma lt_inv_mul_iff₀'
  given: (hc : 0 < c)
  statement: a < c⁻¹ * b ↔ a * c < b
  proof: by
  rw [lt_inv_mul_iff₀ hc]; rw [mul_comm]

中文:
引理 lt_inv_mul_iff₀'
  条件: (hc : 0 < c)
  结论: a < c⁻¹ * b ↔ a * c < b
  证明: by
  rw [lt_inv_mul_iff₀ hc]; rw [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma lt_inv_mul_iff₀' (hc : 0 < c) : a < c⁻¹ * b ↔ a * c < b := by
  rw [lt_inv_mul_iff₀ hc]; rw [mul_comm]

/--
lemma `inv_mul_lt_iff₀'` / 引理 `inv_mul_lt_iff₀'`

English:
lemma inv_mul_lt_iff₀'
  given: (hc : 0 < c)
  statement: c⁻¹ * b < a ↔ b < a * c
  proof: by
  rw [inv_mul_lt_iff₀ hc]; rw [mul_comm]

中文:
引理 inv_mul_lt_iff₀'
  条件: (hc : 0 < c)
  结论: c⁻¹ * b < a ↔ b < a * c
  证明: by
  rw [inv_mul_lt_iff₀ hc]; rw [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma inv_mul_lt_iff₀' (hc : 0 < c) : c⁻¹ * b < a ↔ b < a * c := by
  rw [inv_mul_lt_iff₀ hc]; rw [mul_comm]

/--
lemma `lt_mul_inv_iff₀'` / 引理 `lt_mul_inv_iff₀'`

English:
lemma lt_mul_inv_iff₀'
  given: (hc : 0 < c)
  statement: a < b * c⁻¹ ↔ c * a < b
  proof: by
  rw [lt_mul_inv_iff₀ hc]; rw [mul_comm]

中文:
引理 lt_mul_inv_iff₀'
  条件: (hc : 0 < c)
  结论: a < b * c⁻¹ ↔ c * a < b
  证明: by
  rw [lt_mul_inv_iff₀ hc]; rw [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma lt_mul_inv_iff₀' (hc : 0 < c) : a < b * c⁻¹ ↔ c * a < b := by
  rw [lt_mul_inv_iff₀ hc]; rw [mul_comm]

/--
lemma `mul_inv_lt_iff₀'` / 引理 `mul_inv_lt_iff₀'`

English:
lemma mul_inv_lt_iff₀'
  given: (hc : 0 < c)
  statement: b * c⁻¹ < a ↔ b < c * a
  proof: by
  rw [mul_inv_lt_iff₀ hc]; rw [mul_comm]

中文:
引理 mul_inv_lt_iff₀'
  条件: (hc : 0 < c)
  结论: b * c⁻¹ < a ↔ b < c * a
  证明: by
  rw [mul_inv_lt_iff₀ hc]; rw [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma mul_inv_lt_iff₀' (hc : 0 < c) : b * c⁻¹ < a ↔ b < c * a := by
  rw [mul_inv_lt_iff₀ hc]; rw [mul_comm]

/--
lemma `div_lt_div_iff₀` / 引理 `div_lt_div_iff₀`

English:
lemma div_lt_div_iff₀
  given: (hb : 0 < b) (hd : 0 < d)
  statement: a / b < c / d ↔ a * d < c * b
  proof: by
  rw [div_lt_iff₀ hb]; rw [← mul_div_right_comm]; rw [lt_div_iff₀ hd]

中文:
引理 div_lt_div_iff₀
  条件: (hb : 0 < b) (hd : 0 < d)
  结论: a / b < c / d ↔ a * d < c * b
  证明: by
  rw [div_lt_iff₀ hb]; rw [← mul_div_right_comm]; rw [lt_div_iff₀ hd]

Depends on / 依赖: mul_div_right_comm
-/
lemma div_lt_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b < c / d ↔ a * d < c * b := by
  rw [div_lt_iff₀ hb]; rw [← mul_div_right_comm]; rw [lt_div_iff₀ hd]

/--
lemma `lt_div_iff₀'` / 引理 `lt_div_iff₀'`

English:
lemma lt_div_iff₀'
  given: (hc : 0 < c)
  statement: a < b / c ↔ c * a < b
  proof: by
  rw [lt_div_iff₀ hc]; rw [mul_comm]

中文:
引理 lt_div_iff₀'
  条件: (hc : 0 < c)
  结论: a < b / c ↔ c * a < b
  证明: by
  rw [lt_div_iff₀ hc]; rw [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b := by
  rw [lt_div_iff₀ hc]; rw [mul_comm]

/--
lemma `div_lt_iff₀'` / 引理 `div_lt_iff₀'`

English:
lemma div_lt_iff₀'
  given: (hc : 0 < c)
  statement: b / c < a ↔ b < c * a
  proof: by
  rw [div_lt_iff₀ hc]; rw [mul_comm]

中文:
引理 div_lt_iff₀'
  条件: (hc : 0 < c)
  结论: b / c < a ↔ b < c * a
  证明: by
  rw [div_lt_iff₀ hc]; rw [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a := by
  rw [div_lt_iff₀ hc]; rw [mul_comm]

/--
lemma `lt_div_comm₀` / 引理 `lt_div_comm₀`

English:
lemma lt_div_comm₀
  given: (ha : 0 < a) (hc : 0 < c)
  statement: a < b / c ↔ c < b / a
  proof: by
  rw [lt_div_iff₀ ha]; rw [lt_div_iff₀' hc]

中文:
引理 lt_div_comm₀
  条件: (ha : 0 < a) (hc : 0 < c)
  结论: a < b / c ↔ c < b / a
  证明: by
  rw [lt_div_iff₀ ha]; rw [lt_div_iff₀' hc]
-/
lemma lt_div_comm₀ (ha : 0 < a) (hc : 0 < c) : a < b / c ↔ c < b / a := by
  rw [lt_div_iff₀ ha]; rw [lt_div_iff₀' hc]

/--
lemma `div_lt_comm₀` / 引理 `div_lt_comm₀`

English:
lemma div_lt_comm₀
  given: (hb : 0 < b) (hc : 0 < c)
  statement: a / b < c ↔ a / c < b
  proof: by
  rw [div_lt_iff₀ hb]; rw [div_lt_iff₀' hc]

中文:
引理 div_lt_comm₀
  条件: (hb : 0 < b) (hc : 0 < c)
  结论: a / b < c ↔ a / c < b
  证明: by
  rw [div_lt_iff₀ hb]; rw [div_lt_iff₀' hc]
-/
lemma div_lt_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b < c ↔ a / c < b := by
  rw [div_lt_iff₀ hb]; rw [div_lt_iff₀' hc]

end CommGroupWithZero
