/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Conversion from WithTop to Base Type

For types α that are instances of `Zero`, we provide a convenient conversion, `WithTop.untop₀`, that
maps elements `a : WithTop α` to `α`, by mapping `⊤` to zero.

For settings where `α` has additional structure, we provide a large number of simplifier lemmas,
akin to those that already exists for `ENat.toNat`.
-/

@[expose] public section

namespace WithTop
variable {α : Type*}

section Zero
variable [Zero α]

/--
Definition of `untop₀` / `untop₀` 的定义

English:
definition untop₀
  signature: (a : WithTop α)
  body: a.untopD 0

中文:
定义 untop₀
  签名: (a : WithTop α)
  定义体: a.untopD 0

Depends on / 依赖: a.untopD, untopD
-/
def untop₀ (a : WithTop α) : α := a.untopD 0

/-!
## Simplifying Lemmas in cases where α is an Instance of Zero
-/

@[simp]
/--
lemma `untop₀_eq_zero` / 引理 `untop₀_eq_zero`

English:
lemma untop₀_eq_zero
  given: {a : WithTop α}
  proof: by simp [untop₀]

@[simp]

中文:
引理 untop₀_eq_zero
  条件: {a : WithTop α}
  证明: by simp [untop₀]

@[simp]
-/
lemma untop₀_eq_zero {a : WithTop α} :
    a.untop₀ = 0 ↔ a = 0 ∨ a = ⊤ := by simp [untop₀]

@[simp]
/--
lemma `untop₀_top` / 引理 `untop₀_top`

English:
lemma untop₀_top
  statement: untop₀ ⊤ = (0 : α)
  proof: by simp [untop₀]

@[simp]

中文:
引理 untop₀_top
  结论: untop₀ ⊤ = (0 : α)
  证明: by simp [untop₀]

@[simp]
-/
lemma untop₀_top : untop₀ ⊤ = (0 : α) := by simp [untop₀]

@[simp]
/--
lemma `untop₀_zero` / 引理 `untop₀_zero`

English:
lemma untop₀_zero
  statement: untop₀ 0 = (0 : α)
  proof: by simp [untop₀]

@[simp]

中文:
引理 untop₀_zero
  结论: untop₀ 0 = (0 : α)
  证明: by simp [untop₀]

@[simp]
-/
lemma untop₀_zero : untop₀ 0 = (0 : α) := by simp [untop₀]

@[simp]
/--
lemma `untop₀_coe` / 引理 `untop₀_coe`

English:
lemma untop₀_coe
  given: (a : α)
  statement: (a : WithTop α).untop₀ = a
  proof: rfl

中文:
引理 untop₀_coe
  条件: (a : α)
  结论: (a : WithTop α).untop₀ = a
  证明: rfl
-/
lemma untop₀_coe (a : α) : (a : WithTop α).untop₀ = a := rfl

/--
lemma `coe_untop₀_of_ne_top` / 引理 `coe_untop₀_of_ne_top`

English:
lemma coe_untop₀_of_ne_top
  given: {a : WithTop α} (ha : a != ⊤)
  proof: by
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 ha
  simp [← hb]

中文:
引理 coe_untop₀_of_ne_top
  条件: {a : WithTop α} (ha : a != ⊤)
  证明: by
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 ha
  simp [← hb]

Depends on / 依赖: WithTop, WithTop.ne_top_iff_exists, ne_top_iff_exists
-/
lemma coe_untop₀_of_ne_top {a : WithTop α} (ha : a != ⊤) :
    a.untop₀ = a := by
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 ha
  simp [← hb]

end Zero

/-!
## Simplifying Lemmas involving addition and negation
-/

@[simp]
/--
lemma `untopD_add` / 引理 `untopD_add`

English:
lemma untopD_add
  given: [Add α] {a b : WithTop α} {c : α} (ha : a != ⊤) (hb : b != ⊤)
  proof: by
  lift a to α using ha
  lift b to α using hb
  simp [← coe_add]

@[simp]

中文:
引理 untopD_add
  条件: [加法 α] {a b : WithTop α} {c : α} (ha : a != ⊤) (hb : b != ⊤)
  证明: by
  lift a to α using ha
  lift b to α using hb
  simp [← coe_add]

@[simp]

Depends on / 依赖: coe_add
-/
lemma untopD_add [Add α] {a b : WithTop α} {c : α} (ha : a != ⊤) (hb : b != ⊤) :
    (a + b).untopD c = a.untopD c + b.untopD c := by
  lift a to α using ha
  lift b to α using hb
  simp [← coe_add]

@[simp]
/--
lemma `untop₀_add` / 引理 `untop₀_add`

English:
lemma untop₀_add
  given: [AddZeroClass α] {a b : WithTop α} (ha : a != ⊤) (hb : b != ⊤)
  proof: untopD_add ha hb

@[simp]

中文:
引理 untop₀_add
  条件: [加法零类 α] {a b : WithTop α} (ha : a != ⊤) (hb : b != ⊤)
  证明: untopD_add ha hb

@[simp]

Depends on / 依赖: untopD_add
-/
lemma untop₀_add [AddZeroClass α] {a b : WithTop α} (ha : a != ⊤) (hb : b != ⊤) :
    (a + b).untop₀ = a.untop₀ + b.untop₀ := untopD_add ha hb

@[simp]
/--
lemma `untop₀_natCast` / 引理 `untop₀_natCast`

English:
lemma untop₀_natCast
  given: [AddMonoidWithOne α] (n : Nat)
  statement: untop₀ (n : WithTop α) = n
  proof: rfl

@[simp]

中文:
引理 untop₀_natCast
  条件: [加法带幺幺半群 α] (n : 自然数)
  结论: untop₀ (n : WithTop α) = n
  证明: rfl

@[simp]
-/
lemma untop₀_natCast [AddMonoidWithOne α] (n : Nat) : untop₀ (n : WithTop α) = n := rfl

@[simp]
/--
theorem `untop₀_one` / 定理 `untop₀_one`

English:
theorem untop₀_one
  given: {α : Type*} [AddMonoidWithOne α]
  proof: by
  convert WithTop.untop₀_natCast 1
  all_goals exact Nat.cast_one.symm

@[simp]

中文:
定理 untop₀_one
  条件: {α : 类型} [加法带幺幺半群 α]
  证明: by
  convert WithTop.untop₀_natCast 1
  all_goals exact Nat.cast_one.symm

@[simp]

Depends on / 依赖: Nat.cast_one.symm, WithTop, WithTop.untop, all_goals, cast_one, convert
-/
theorem untop₀_one {α : Type*} [AddMonoidWithOne α] :
    (1 : WithTop α).untop₀ = 1 := by
  convert WithTop.untop₀_natCast 1
  all_goals exact Nat.cast_one.symm

@[simp]
/--
lemma `untop₀_ofNat` / 引理 `untop₀_ofNat`

English:
lemma untop₀_ofNat
  given: [AddMonoidWithOne α] (n : Nat) [n.AtLeastTwo]
  proof: rfl

@[simp]

中文:
引理 untop₀_of自然数
  条件: [加法带幺幺半群 α] (n : 自然数) [n.AtLeastTwo]
  证明: rfl

@[simp]
-/
lemma untop₀_ofNat [AddMonoidWithOne α] (n : Nat) [n.AtLeastTwo] :
    untop₀ (ofNat(n) : WithTop α) = ofNat(n) := rfl

@[simp]
/--
lemma `untop₀_neg` / 引理 `untop₀_neg`

English:
lemma untop₀_neg
  given: [AddCommGroup α]
  statement: forall a : WithTop α, (-a).untop₀ = -a.untop₀

中文:
引理 untop₀_neg
  条件: [加法交换群 α]
  结论: 对任意 a : WithTop α, (-a).untop₀ = -a.untop₀
-/
lemma untop₀_neg [AddCommGroup α] : forall a : WithTop α, (-a).untop₀ = -a.untop₀
  | ⊤ => by simp
  | (a : α) => rfl

@[simp]
/--
lemma `untop₀_mul` / 引理 `untop₀_mul`

English:
lemma untop₀_mul
  given: [DecidableEq α] [MulZeroClass α] (a b : WithTop α)
  proof: untopD_zero_mul a b

中文:
引理 untop₀_mul
  条件: [DecidableEq α] [乘零类 α] (a b : WithTop α)
  证明: untopD_zero_mul a b

Depends on / 依赖: untopD_zero_mul
-/
lemma untop₀_mul [DecidableEq α] [MulZeroClass α] (a b : WithTop α) :
    (a * b).untop₀ = a.untop₀ * b.untop₀ := untopD_zero_mul a b

section OrderedAddCommGroup

variable [AddCommGroup α] [PartialOrder α] {a b : WithTop α}

/--
lemma `untop₀_nonneg` / 引理 `untop₀_nonneg`

English:
lemma untop₀_nonneg
  statement: 0 <= a.untop₀ ↔ 0 <= a
  proof: by
  cases a with
  | top => tauto
  | coe a => simp

中文:
引理 untop₀_nonneg
  结论: 0 <= a.untop₀ ↔ 0 <= a
  证明: by
  cases a with
  | top => tauto
  | coe a => simp
-/
@[simp] lemma untop₀_nonneg : 0 <= a.untop₀ ↔ 0 <= a := by
  cases a with
  | top => tauto
  | coe a => simp

/--
theorem `le_of_untop₀_le_untop₀` / 定理 `le_of_untop₀_le_untop₀`

English:
theorem le_of_untop₀_le_untop₀
  given: (ha : a != ⊤) (h : a.untop₀ <= b.untop₀)
  statement: a <= b
  proof: by
  lift a to α using ha
  by_cases hb : b = ⊤
  · simp_all
  lift b to α using hb
  simp_all

中文:
定理 le_of_untop₀_le_untop₀
  条件: (ha : a != ⊤) (h : a.untop₀ <= b.untop₀)
  结论: a <= b
  证明: by
  lift a to α using ha
  by_cases hb : b = ⊤
  · simp_all
  lift b to α using hb
  simp_all
-/
theorem le_of_untop₀_le_untop₀ (ha : a != ⊤) (h : a.untop₀ <= b.untop₀) : a <= b := by
  lift a to α using ha
  by_cases hb : b = ⊤
  · simp_all
  lift b to α using hb
  simp_all

/--
theorem `untop₀_le_untop₀` / 定理 `untop₀_le_untop₀`

English:
theorem untop₀_le_untop₀
  given: (hb : b != ⊤) (h : a <= b)
  statement: a.untop₀ <= b.untop₀
  proof: by
  lift b to α using hb
  by_cases ha : a = ⊤
  · simp_all
  lift a to α using ha
  simp_all

中文:
定理 untop₀_le_untop₀
  条件: (hb : b != ⊤) (h : a <= b)
  结论: a.untop₀ <= b.untop₀
  证明: by
  lift b to α using hb
  by_cases ha : a = ⊤
  · simp_all
  lift a to α using ha
  simp_all
-/
@[simp, gcongr] theorem untop₀_le_untop₀ (hb : b != ⊤) (h : a <= b) : a.untop₀ <= b.untop₀ := by
  lift b to α using hb
  by_cases ha : a = ⊤
  · simp_all
  lift a to α using ha
  simp_all

/--
theorem `untop₀_le_untop₀_iff` / 定理 `untop₀_le_untop₀_iff`

English:
theorem untop₀_le_untop₀_iff
  given: (ha : a != ⊤) (hb : b != ⊤)
  proof: by
  lift a to α using ha
  lift b to α using hb
  simp

中文:
定理 untop₀_le_untop₀_iff
  条件: (ha : a != ⊤) (hb : b != ⊤)
  证明: by
  lift a to α using ha
  lift b to α using hb
  simp
-/
theorem untop₀_le_untop₀_iff (ha : a != ⊤) (hb : b != ⊤) :
    a.untop₀ <= b.untop₀ ↔ a <= b := by
  lift a to α using ha
  lift b to α using hb
  simp

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [AddCommGroup α] [LinearOrder α] {a b : WithTop α}

/--
theorem `untop₀_max` / 定理 `untop₀_max`

English:
theorem untop₀_max
  given: (ha : a != ⊤) (hb : b != ⊤)
  proof: by
  lift a to α using ha
  lift b to α using hb
  simp only [untop₀_coe]
  by_cases h : a <= b
  · simp [max_eq_right h, max_eq_right (coe_le_coe.mpr h)]
  rw [not_le] at h
  simp [max_eq_left h.le, max_eq_left (coe_lt_coe.mpr h).le]

中文:
定理 untop₀_max
  条件: (ha : a != ⊤) (hb : b != ⊤)
  证明: by
  lift a to α using ha
  lift b to α using hb
  simp only [untop₀_coe]
  by_cases h : a <= b
  · simp [max_eq_right h, max_eq_right (coe_le_coe.mpr h)]
  rw [not_le] at h
  simp [max_eq_left h.le, max_eq_left (coe_lt_coe.mpr h).le]
-/
@[simp] theorem untop₀_max (ha : a != ⊤) (hb : b != ⊤) :
    (max a b).untop₀ = max a.untop₀ b.untop₀ := by
  lift a to α using ha
  lift b to α using hb
  simp only [untop₀_coe]
  by_cases h : a <= b
  · simp [max_eq_right h, max_eq_right (coe_le_coe.mpr h)]
  rw [not_le] at h
  simp [max_eq_left h.le, max_eq_left (coe_lt_coe.mpr h).le]

/--
theorem `untop₀_min` / 定理 `untop₀_min`

English:
theorem untop₀_min
  given: (ha : a != ⊤) (hb : b != ⊤)
  proof: by
  lift a to α using ha
  lift b to α using hb
  norm_cast

中文:
定理 untop₀_min
  条件: (ha : a != ⊤) (hb : b != ⊤)
  证明: by
  lift a to α using ha
  lift b to α using hb
  norm_cast
-/
@[simp] theorem untop₀_min (ha : a != ⊤) (hb : b != ⊤) :
    (min a b).untop₀ = min a.untop₀ b.untop₀ := by
  lift a to α using ha
  lift b to α using hb
  norm_cast

end LinearOrderedAddCommGroup

end WithTop
