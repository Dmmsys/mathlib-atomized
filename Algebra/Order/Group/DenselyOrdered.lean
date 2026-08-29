/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Lemmas about densely linearly ordered groups.
-/

public section

variable {α : Type*}

section DenselyOrdered

variable [Group α] [LinearOrder α]
variable [MulLeftMono α]
variable [DenselyOrdered α] {a b : α}

@[to_additive]
/--
theorem `le_of_forall_lt_one_mul_le` / 定理 `le_of_forall_lt_one_mul_le`

English:
theorem le_of_forall_lt_one_mul_le
  given: (h : forall ε < 1, a * ε <= b)
  statement: a <= b
  proof: le_of_forall_one_lt_le_mul (α := αᵒᵈ) h

@[to_additive]

中文:
定理 le_of_forall_lt_one_mul_le
  条件: (h : 对任意 ε < 1, a * ε <= b)
  结论: a <= b
  证明: le_of_forall_one_lt_le_mul (α := αᵒᵈ) h

@[to_additive]

Depends on / 依赖: le_of_forall_one_lt_le_mul
-/
theorem le_of_forall_lt_one_mul_le (h : forall ε < 1, a * ε <= b) : a <= b :=
  le_of_forall_one_lt_le_mul (α := αᵒᵈ) h

@[to_additive]
/--
theorem `le_of_forall_one_lt_div_le` / 定理 `le_of_forall_one_lt_div_le`

English:
theorem le_of_forall_one_lt_div_le
  given: (h : forall ε : α, 1 < ε -> a / ε <= b)
  statement: a <= b
  proof: le_of_forall_lt_one_mul_le fun ε ε1 => by
    simpa only [div_eq_mul_inv, inv_inv] using h ε⁻¹ (Left.one_lt_inv_iff.2 ε1)

@[to_additive]

中文:
定理 le_of_forall_one_lt_div_le
  条件: (h : 对任意 ε : α, 1 < ε -> a / ε <= b)
  结论: a <= b
  证明: le_of_forall_lt_one_mul_le fun ε ε1 => by
    simpa only [div_eq_mul_inv, inv_inv] using h ε⁻¹ (Left.one_lt_inv_iff.2 ε1)

@[to_additive]

Depends on / 依赖: Left.one_lt_inv_iff, div_eq_mul_inv, inv_inv, le_of_forall_lt_one_mul_le, one_lt_inv_iff
-/
theorem le_of_forall_one_lt_div_le (h : forall ε : α, 1 < ε -> a / ε <= b) : a <= b :=
  le_of_forall_lt_one_mul_le fun ε ε1 => by
    simpa only [div_eq_mul_inv, inv_inv] using h ε⁻¹ (Left.one_lt_inv_iff.2 ε1)

@[to_additive]
/--
theorem `le_iff_forall_lt_one_mul_le` / 定理 `le_iff_forall_lt_one_mul_le`

English:
theorem le_iff_forall_lt_one_mul_le
  statement: a <= b ↔ forall ε < 1, a * ε <= b
  proof: le_iff_forall_one_lt_le_mul (α := αᵒᵈ)

中文:
定理 le_iff_forall_lt_one_mul_le
  结论: a <= b ↔ 对任意 ε < 1, a * ε <= b
  证明: le_iff_forall_one_lt_le_mul (α := αᵒᵈ)

Depends on / 依赖: le_iff_forall_one_lt_le_mul
-/
theorem le_iff_forall_lt_one_mul_le : a <= b ↔ forall ε < 1, a * ε <= b :=
  le_iff_forall_one_lt_le_mul (α := αᵒᵈ)

end DenselyOrdered

section DenselyOrdered

@[to_additive]
/--
lemma `exists_lt_mul_left` / 引理 `exists_lt_mul_left`

English:
lemma exists_lt_mul_left
  statement: [Group α] [LT α] [DenselyOrdered α]
  proof: by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul.1 hc'⟩

@[to_additive]

中文:
引理 exists_lt_mul_left
  结论: [Group α] [LT α] [DenselyOrdered α]
  证明: by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul.1 hc'⟩

@[to_additive]
-/
private lemma exists_lt_mul_left [Group α] [LT α] [DenselyOrdered α]
    [MulRightStrictMono α] {a b c : α} (hc : c < a * b) :
    exists a' < a, c < a' * b := by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul.1 hc'⟩

@[to_additive]
/--
lemma `exists_lt_mul_right` / 引理 `exists_lt_mul_right`

English:
lemma exists_lt_mul_right
  statement: [CommGroup α] [LT α] [DenselyOrdered α]
  proof: by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul'.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul'.1 hc'⟩

@[to_additive]

中文:
引理 exists_lt_mul_right
  结论: [CommGroup α] [LT α] [DenselyOrdered α]
  证明: by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul'.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul'.1 hc'⟩

@[to_additive]
-/
private lemma exists_lt_mul_right [CommGroup α] [LT α] [DenselyOrdered α]
    [MulLeftStrictMono α] {a b c : α} (hc : c < a * b) :
    exists b' < b, c < a * b' := by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul'.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul'.1 hc'⟩

@[to_additive]
/--
lemma `exists_mul_left_lt` / 引理 `exists_mul_left_lt`

English:
lemma exists_mul_left_lt
  statement: [Group α] [LT α] [DenselyOrdered α]
  proof: by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt.1 hc'⟩

@[to_additive]

中文:
引理 exists_mul_left_lt
  结论: [Group α] [LT α] [DenselyOrdered α]
  证明: by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt.1 hc'⟩

@[to_additive]
-/
private lemma exists_mul_left_lt [Group α] [LT α] [DenselyOrdered α]
    [MulRightStrictMono α] {a b c : α} (hc : a * b < c) :
    exists a' > a, a' * b < c := by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt.1 hc'⟩

@[to_additive]
/--
lemma `exists_mul_right_lt` / 引理 `exists_mul_right_lt`

English:
lemma exists_mul_right_lt
  statement: [CommGroup α] [LT α] [DenselyOrdered α]
  proof: by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt'.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt'.1 hc'⟩

@[to_additive]

中文:
引理 exists_mul_right_lt
  结论: [CommGroup α] [LT α] [DenselyOrdered α]
  证明: by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt'.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt'.1 hc'⟩

@[to_additive]
-/
private lemma exists_mul_right_lt [CommGroup α] [LT α] [DenselyOrdered α]
    [MulLeftStrictMono α] {a b c : α} (hc : a * b < c) :
    exists b' > b, a * b' < c := by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt'.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt'.1 hc'⟩

@[to_additive]
/--
lemma `le_mul_of_forall_lt` / 引理 `le_mul_of_forall_lt`

English:
lemma le_mul_of_forall_lt
  statement: [CommGroup α] [LinearOrder α] [MulLeftMono α]
  proof: by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_mul_left_lt hd
  obtain ⟨b', hb', hd⟩ := exists_mul_right_lt hd
  exact (h a' ha' b' hb').trans hd.le

@[to_additive]

中文:
引理 le_mul_of_forall_lt
  结论: [CommGroup α] [LinearOrder α] [MulLeftMono α]
  证明: by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_mul_left_lt hd
  obtain ⟨b', hb', hd⟩ := exists_mul_right_lt hd
  exact (h a' ha' b' hb').trans hd.le

@[to_additive]

Depends on / 依赖: exists_mul_left_lt, exists_mul_right_lt, hd.le, le_of_forall_gt_imp_ge_of_dense
-/
lemma le_mul_of_forall_lt [CommGroup α] [LinearOrder α] [MulLeftMono α]
    [DenselyOrdered α] {a b c : α} (h : forall a' > a, forall b' > b, c <= a' * b') :
    c <= a * b := by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_mul_left_lt hd
  obtain ⟨b', hb', hd⟩ := exists_mul_right_lt hd
  exact (h a' ha' b' hb').trans hd.le

@[to_additive]
/--
lemma `mul_le_of_forall_lt` / 引理 `mul_le_of_forall_lt`

English:
lemma mul_le_of_forall_lt
  statement: [CommGroup α] [LinearOrder α] [MulLeftMono α]
  proof: by
  refine le_of_forall_lt_imp_le_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_mul_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_mul_right hd
  exact hd.le.trans (h a' ha' b' hb')

中文:
引理 mul_le_of_forall_lt
  结论: [CommGroup α] [LinearOrder α] [MulLeftMono α]
  证明: by
  refine le_of_forall_lt_imp_le_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_mul_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_mul_right hd
  exact hd.le.trans (h a' ha' b' hb')

Depends on / 依赖: exists_lt_mul_left, exists_lt_mul_right, hd.le.trans, le_of_forall_lt_imp_le_of_dense
-/
lemma mul_le_of_forall_lt [CommGroup α] [LinearOrder α] [MulLeftMono α]
    [DenselyOrdered α] {a b c : α} (h : forall a' < a, forall b' < b, a' * b' <= c) :
    a * b <= c := by
  refine le_of_forall_lt_imp_le_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_mul_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_mul_right hd
  exact hd.le.trans (h a' ha' b' hb')

end DenselyOrdered

variable {M : Type*} [LinearOrder M] [DenselyOrdered M] {x : M}

section Monoid
variable [CommMonoid M] [ExistsMulOfLE M] [IsOrderedCancelMonoid M]

@[to_additive]
/--
theorem `exists_pow_two_le_of_one_lt` / 定理 `exists_pow_two_le_of_one_lt`

English:
theorem exists_pow_two_le_of_one_lt
  given: (hx : 1 < x)
  statement: exists y : M, 1 < y ∧ y ^ 2 <= x
  proof: by
  obtain ⟨y, hy, hyx⟩ := exists_between hx
  obtain hyx | hxy := le_total (y ^ 2) x
  · exact ⟨y, hy, hyx⟩
  obtain ⟨z, hz, rfl⟩ := exists_one_lt_mul_of_lt' hyx
  exact ⟨z, hz, by simpa [pow_succ] using hxy⟩

@[to_additive]

中文:
定理 exists_pow_two_le_of_one_lt
  条件: (hx : 1 < x)
  结论: 存在 y : M, 1 < y ∧ y ^ 2 <= x
  证明: by
  obtain ⟨y, hy, hyx⟩ := exists_between hx
  obtain hyx | hxy := le_total (y ^ 2) x
  · exact ⟨y, hy, hyx⟩
  obtain ⟨z, hz, rfl⟩ := exists_one_lt_mul_of_lt' hyx
  exact ⟨z, hz, by simpa [pow_succ] using hxy⟩

@[to_additive]
-/
private theorem exists_pow_two_le_of_one_lt (hx : 1 < x) : exists y : M, 1 < y ∧ y ^ 2 <= x := by
  obtain ⟨y, hy, hyx⟩ := exists_between hx
  obtain hyx | hxy := le_total (y ^ 2) x
  · exact ⟨y, hy, hyx⟩
  obtain ⟨z, hz, rfl⟩ := exists_one_lt_mul_of_lt' hyx
  exact ⟨z, hz, by simpa [pow_succ] using hxy⟩

@[to_additive]
/--
theorem `exists_pow_lt_of_one_lt` / 定理 `exists_pow_lt_of_one_lt`

English:
theorem exists_pow_lt_of_one_lt
  given: (hx : 1 < x)
  statement: forall n : Nat, exists y : M, 1 < y ∧ y ^ n < x
  proof: exists_pow_lt_of_one_lt hx (n + 1)
    obtain ⟨z, hz, hzy⟩ := exists_pow_two_le_of_one_lt hy
    refine ⟨z, hz, hyx.trans_le' ?_⟩
    calc z ^ (n + 2)
      _ <= z ^ (2 * (n + 1)) := pow_right_monotone hz.le (by lia)
      _ = (z ^ 2) ^ (n + 1) := by rw [pow_mul]
      _ <= y ^ (n + 1) := pow_le_pow

中文:
定理 exists_pow_lt_of_one_lt
  条件: (hx : 1 < x)
  结论: 对任意 n : 自然数, 存在 y : M, 1 < y ∧ y ^ n < x
  证明: exists_pow_lt_of_one_lt hx (n + 1)
    obtain ⟨z, hz, hzy⟩ := exists_pow_two_le_of_one_lt hy
    refine ⟨z, hz, hyx.trans_le' ?_⟩
    calc z ^ (n + 2)
      _ <= z ^ (2 * (n + 1)) := pow_right_monotone hz.le (by lia)
      _ = (z ^ 2) ^ (n + 1) := by rw [pow_mul]
      _ <= y ^ (n + 1) := pow_le_pow

Depends on / 依赖: exists_pow_lt_of_one_lt
-/
theorem exists_pow_lt_of_one_lt (hx : 1 < x) : forall n : Nat, exists y : M, 1 < y ∧ y ^ n < x
  | 0 => ⟨x, by simpa⟩
  | 1 => by simpa using exists_between hx
  | n + 2 => by
    obtain ⟨y, hy, hyx⟩ := exists_pow_lt_of_one_lt hx (n + 1)
    obtain ⟨z, hz, hzy⟩ := exists_pow_two_le_of_one_lt hy
    refine ⟨z, hz, hyx.trans_le' ?_⟩
    calc z ^ (n + 2)
      _ <= z ^ (2 * (n + 1)) := pow_right_monotone hz.le (by lia)
      _ = (z ^ 2) ^ (n + 1) := by rw [pow_mul]
      _ <= y ^ (n + 1) := pow_le_pow_left' hzy (n + 1)

end Monoid

section Group
variable [CommGroup M] [IsOrderedCancelMonoid M]

@[to_additive]
/--
theorem `exists_lt_pow_of_lt_one` / 定理 `exists_lt_pow_of_lt_one`

English:
theorem exists_lt_pow_of_lt_one
  given: (hx : x < 1) (n : Nat)
  statement: exists y : M, y < 1 ∧ x < y ^ n
  proof: by
  obtain ⟨y, hy, hy'⟩ := exists_pow_lt_of_one_lt (one_lt_inv_of_inv hx) n
  use y⁻¹, inv_lt_one_of_one_lt hy
  simpa [lt_inv'] using hy'

中文:
定理 exists_lt_pow_of_lt_one
  条件: (hx : x < 1) (n : 自然数)
  结论: 存在 y : M, y < 1 ∧ x < y ^ n
  证明: by
  obtain ⟨y, hy, hy'⟩ := exists_pow_lt_of_one_lt (one_lt_inv_of_inv hx) n
  use y⁻¹, inv_lt_one_of_one_lt hy
  simpa [lt_inv'] using hy'

Depends on / 依赖: exists_pow_lt_of_one_lt, inv_lt_one_of_one_lt, lt_inv, one_lt_inv_of_inv
-/
theorem exists_lt_pow_of_lt_one (hx : x < 1) (n : Nat) : exists y : M, y < 1 ∧ x < y ^ n := by
  obtain ⟨y, hy, hy'⟩ := exists_pow_lt_of_one_lt (one_lt_inv_of_inv hx) n
  use y⁻¹, inv_lt_one_of_one_lt hy
  simpa [lt_inv'] using hy'

end Group
