/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Ring.Parity

/-!
# Lemmas about rings of characteristic two

This file contains results about `CharP R 2`, in the `CharTwo` namespace.

The lemmas in this file with a `_sq` suffix are just special cases of the `_pow_char` lemmas
elsewhere, with a shorter name for ease of discovery, and no need for a `[Fact (Prime 2)]` argument.
-/

public section

-- TODO: `assert_not_exists Field` is added because of `Mathlib.GroupTheory.OrderOfElement`.
-- If you want to import fields here, please refactor the import hierarchy for
-- `Mathlib.GroupTheory.OrderOfElement`.
assert_not_exists Algebra LinearMap Field

variable {R ι : Type*}

namespace CharTwo

section AddMonoidWithOne

variable [AddMonoidWithOne R]

/--
theorem `of_one_ne_zero_of_two_eq_zero` / 定理 `of_one_ne_zero_of_two_eq_zero`

English:
theorem of_one_ne_zero_of_two_eq_zero
  given: (h₁ : (1 : R) != 0) (h₂ : (2 : R) = 0)
  statement: CharP R 2 where
  proof: by
    obtain hn | hn := Nat.even_or_odd n
    · simp_rw [hn.two_dvd, iff_true]
      exact natCast_eq_zero_of_even_of_two_eq_zero hn h₂
    · simp_rw [hn.not_two_dvd_nat, iff_false]
      rwa [natCast_eq_one_of_odd_of_two_eq_zero hn h₂]

中文:
定理 of_one_ne_zero_of_two_eq_zero
  条件: (h₁ : (1 : R) != 0) (h₂ : (2 : R) = 0)
  结论: 特征p R 2 where
  证明: by
    obtain hn | hn := Nat.even_or_odd n
    · simp_rw [hn.two_dvd, iff_true]
      exact natCast_eq_zero_of_even_of_two_eq_zero hn h₂
    · simp_rw [hn.not_two_dvd_nat, iff_false]
      rwa [natCast_eq_one_of_odd_of_two_eq_zero hn h₂]

Depends on / 依赖: Nat.even_or_odd, even_or_odd, hn.not_two_dvd_nat, hn.two_dvd, iff_false, iff_true, natCast_eq_one_of_odd_of_two_eq_zero, natCast_eq_zero_of_even_of_two_eq_zero, not_two_dvd_nat, simp_rw, two_dvd
-/
theorem of_one_ne_zero_of_two_eq_zero (h₁ : (1 : R) != 0) (h₂ : (2 : R) = 0) : CharP R 2 where
  cast_eq_zero_iff n := by
    obtain hn | hn := Nat.even_or_odd n
    · simp_rw [hn.two_dvd, iff_true]
      exact natCast_eq_zero_of_even_of_two_eq_zero hn h₂
    · simp_rw [hn.not_two_dvd_nat, iff_false]
      rwa [natCast_eq_one_of_odd_of_two_eq_zero hn h₂]

variable [CharP R 2]

@[scoped simp]
/--
theorem `two_eq_zero` / 定理 `two_eq_zero`

English:
theorem two_eq_zero
  statement: (2 : R) = 0
  proof: by
  rw [← Nat.cast_two]; rw [CharP.cast_eq_zero]

中文:
定理 two_eq_zero
  结论: (2 : R) = 0
  证明: by
  rw [← Nat.cast_two]; rw [CharP.cast_eq_zero]

Depends on / 依赖: CharP.cast_eq_zero, Nat.cast_two, cast_eq_zero, cast_two
-/
theorem two_eq_zero : (2 : R) = 0 := by
  rw [← Nat.cast_two]; rw [CharP.cast_eq_zero]

/--
theorem `natCast_eq_ite` / 定理 `natCast_eq_ite`

English:
theorem natCast_eq_ite
  given: (n : Nat)
  statement: (n : R) = if Even n then 0 else 1
  proof: by
  induction n <;> aesop (add simp [one_add_one_eq_two])

@[simp]

中文:
定理 natCast_eq_ite
  条件: (n : 自然数)
  结论: (n : R) = if Even n then 0 else 1
  证明: by
  induction n <;> aesop (add simp [one_add_one_eq_two])

@[simp]

Depends on / 依赖: one_add_one_eq_two
-/
theorem natCast_eq_ite (n : Nat) : (n : R) = if Even n then 0 else 1 := by
  induction n <;> aesop (add simp [one_add_one_eq_two])

@[simp]
/--
theorem `range_natCast` / 定理 `range_natCast`

English:
theorem range_natCast
  statement: Set.range ((↑) : Nat -> R) = {0, 1}
  proof: by
  rw [funext natCast_eq_ite]; rw [Set.range_ite_const]
  · use 0; simp
  · use 1; simp

中文:
定理 range_natCast
  结论: 集合.range ((↑) : 自然数 -> R) = {0, 1}
  证明: by
  rw [funext natCast_eq_ite]; rw [Set.range_ite_const]
  · use 0; simp
  · use 1; simp

Depends on / 依赖: Set.range_ite_const, natCast_eq_ite, range_ite_const
-/
theorem range_natCast : Set.range ((↑) : Nat -> R) = {0, 1} := by
  rw [funext natCast_eq_ite]; rw [Set.range_ite_const]
  · use 0; simp
  · use 1; simp

variable (R) in
/--
theorem `natCast_cases` / 定理 `natCast_cases`

English:
theorem natCast_cases
  given: (n : Nat)
  statement: (n : R) = 0 ∨ (n : R) = 1
  proof: range_natCast.le (Set.mem_range_self _)

中文:
定理 natCast_cases
  条件: (n : 自然数)
  结论: (n : R) = 0 ∨ (n : R) = 1
  证明: range_natCast.le (Set.mem_range_self _)

Depends on / 依赖: Set.mem_range_self, mem_range_self, range_natCast, range_natCast.le
-/
theorem natCast_cases (n : Nat) : (n : R) = 0 ∨ (n : R) = 1 :=
  range_natCast.le (Set.mem_range_self _)

/--
theorem `natCast_eq_mod` / 定理 `natCast_eq_mod`

English:
theorem natCast_eq_mod
  given: (n : Nat)
  statement: (n : R) = (n % 2 : Nat)
  proof: by
  simp [natCast_eq_ite, Nat.even_iff]

@[scoped simp]

中文:
定理 natCast_eq_mod
  条件: (n : 自然数)
  结论: (n : R) = (n % 2 : 自然数)
  证明: by
  simp [natCast_eq_ite, Nat.even_iff]

@[scoped simp]

Depends on / 依赖: Nat.even_iff, even_iff, natCast_eq_ite
-/
theorem natCast_eq_mod (n : Nat) : (n : R) = (n % 2 : Nat) := by
  simp [natCast_eq_ite, Nat.even_iff]

@[scoped simp]
/--
theorem `ofNat_eq_mod` / 定理 `ofNat_eq_mod`

English:
theorem ofNat_eq_mod
  given: (n : Nat) [n.AtLeastTwo]
  statement: (OfNat.ofNat n : R) = (ofNat(n) % 2 : Nat)
  proof: natCast_eq_mod n

example : (37 : R) = 1 := by simp

中文:
定理 of自然数_eq_mod
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (Of自然数.of自然数 n : R) = (of自然数(n) % 2 : 自然数)
  证明: natCast_eq_mod n

example : (37 : R) = 1 := by simp

Depends on / 依赖: natCast_eq_mod
-/
theorem ofNat_eq_mod (n : Nat) [n.AtLeastTwo] : (OfNat.ofNat n : R) = (ofNat(n) % 2 : Nat) :=
  natCast_eq_mod n

example : (37 : R) = 1 := by simp

end AddMonoidWithOne

section Semiring

variable [Semiring R] [CharP R 2]

@[scoped simp]
/--
theorem `add_self_eq_zero` / 定理 `add_self_eq_zero`

English:
theorem add_self_eq_zero
  given: (x : R)
  statement: x + x = 0
  proof: by rw [← two_mul x, two_eq_zero, zero_mul]

@[scoped simp]

中文:
定理 add_self_eq_zero
  条件: (x : R)
  结论: x + x = 0
  证明: by rw [← two_mul x, two_eq_zero, zero_mul]

@[scoped simp]

Depends on / 依赖: two_eq_zero, two_mul, zero_mul
-/
theorem add_self_eq_zero (x : R) : x + x = 0 := by rw [← two_mul x, two_eq_zero, zero_mul]

@[scoped simp]
/--
theorem `two_nsmul` / 定理 `two_nsmul`

English:
theorem two_nsmul
  given: (x : R)
  statement: 2 • x = 0
  proof: by rw [two_nsmul, add_self_eq_zero]

@[scoped simp]

中文:
定理 two_nsmul
  条件: (x : R)
  结论: 2 • x = 0
  证明: by rw [two_nsmul, add_self_eq_zero]

@[scoped simp]
-/
protected theorem two_nsmul (x : R) : 2 • x = 0 := by rw [two_nsmul, add_self_eq_zero]

@[scoped simp]
/--
theorem `add_cancel_left` / 定理 `add_cancel_left`

English:
theorem add_cancel_left
  given: (a b : R)
  statement: a + (a + b) = b
  proof: by
  rw [← add_assoc]; rw [add_self_eq_zero]; rw [zero_add]

@[scoped simp]

中文:
定理 add_cancel_left
  条件: (a b : R)
  结论: a + (a + b) = b
  证明: by
  rw [← add_assoc]; rw [add_self_eq_zero]; rw [zero_add]

@[scoped simp]
-/
protected theorem add_cancel_left (a b : R) : a + (a + b) = b := by
  rw [← add_assoc]; rw [add_self_eq_zero]; rw [zero_add]

@[scoped simp]
/--
theorem `add_cancel_right` / 定理 `add_cancel_right`

English:
theorem add_cancel_right
  given: (a b : R)
  statement: a + b + b = a
  proof: by
  rw [add_assoc]; rw [add_self_eq_zero]; rw [add_zero]

中文:
定理 add_cancel_right
  条件: (a b : R)
  结论: a + b + b = a
  证明: by
  rw [add_assoc]; rw [add_self_eq_zero]; rw [add_zero]
-/
protected theorem add_cancel_right (a b : R) : a + b + b = a := by
  rw [add_assoc]; rw [add_self_eq_zero]; rw [add_zero]

end Semiring

section Ring

variable [Ring R] [CharP R 2]

@[scoped simp]
/--
theorem `neg_eq` / 定理 `neg_eq`

English:
theorem neg_eq
  given: (x : R)
  statement: -x = x
  proof: by
  rw [neg_eq_iff_add_eq_zero]; rw [add_self_eq_zero]

中文:
定理 neg_eq
  条件: (x : R)
  结论: -x = x
  证明: by
  rw [neg_eq_iff_add_eq_zero]; rw [add_self_eq_zero]

Depends on / 依赖: add_self_eq_zero, neg_eq_iff_add_eq_zero
-/
theorem neg_eq (x : R) : -x = x := by
  rw [neg_eq_iff_add_eq_zero]; rw [add_self_eq_zero]

/--
theorem `neg_eq'` / 定理 `neg_eq'`

English:
theorem neg_eq'
  statement: Neg.neg = (id : R -> R)
  proof: funext neg_eq

@[scoped simp]

中文:
定理 neg_eq'
  结论: 取负.neg = (id : R -> R)
  证明: funext neg_eq

@[scoped simp]

Depends on / 依赖: neg_eq
-/
theorem neg_eq' : Neg.neg = (id : R -> R) :=
  funext neg_eq

@[scoped simp]
/--
theorem `sub_eq_add` / 定理 `sub_eq_add`

English:
theorem sub_eq_add
  given: (x y : R)
  statement: x - y = x + y
  proof: by rw [sub_eq_add_neg, neg_eq]

中文:
定理 sub_eq_add
  条件: (x y : R)
  结论: x - y = x + y
  证明: by rw [sub_eq_add_neg, neg_eq]

Depends on / 依赖: neg_eq, sub_eq_add_neg
-/
theorem sub_eq_add (x y : R) : x - y = x + y := by rw [sub_eq_add_neg, neg_eq]

/--
theorem `add_eq_iff_eq_add` / 定理 `add_eq_iff_eq_add`

English:
theorem add_eq_iff_eq_add
  given: {a b c : R}
  statement: a + b = c ↔ a = c + b
  proof: by
  rw [← sub_eq_iff_eq_add]; rw [sub_eq_add]

中文:
定理 add_eq_iff_eq_add
  条件: {a b c : R}
  结论: a + b = c ↔ a = c + b
  证明: by
  rw [← sub_eq_iff_eq_add]; rw [sub_eq_add]

Depends on / 依赖: sub_eq_add, sub_eq_iff_eq_add
-/
theorem add_eq_iff_eq_add {a b c : R} : a + b = c ↔ a = c + b := by
  rw [← sub_eq_iff_eq_add]; rw [sub_eq_add]

/--
theorem `eq_add_iff_add_eq` / 定理 `eq_add_iff_add_eq`

English:
theorem eq_add_iff_add_eq
  given: {a b c : R}
  statement: a = b + c ↔ a + c = b
  proof: by
  rw [← eq_sub_iff_add_eq]; rw [sub_eq_add]

@[scoped simp]

中文:
定理 eq_add_iff_add_eq
  条件: {a b c : R}
  结论: a = b + c ↔ a + c = b
  证明: by
  rw [← eq_sub_iff_add_eq]; rw [sub_eq_add]

@[scoped simp]

Depends on / 依赖: eq_sub_iff_add_eq, sub_eq_add
-/
theorem eq_add_iff_add_eq {a b c : R} : a = b + c ↔ a + c = b := by
  rw [← eq_sub_iff_add_eq]; rw [sub_eq_add]

@[scoped simp]
/--
theorem `two_zsmul` / 定理 `two_zsmul`

English:
theorem two_zsmul
  given: (x : R)
  statement: (2 : Int) • x = 0
  proof: by
  rw [two_zsmul]; rw [add_self_eq_zero]

中文:
定理 two_zsmul
  条件: (x : R)
  结论: (2 : 整数) • x = 0
  证明: by
  rw [two_zsmul]; rw [add_self_eq_zero]
-/
protected theorem two_zsmul (x : R) : (2 : Int) • x = 0 := by
  rw [two_zsmul]; rw [add_self_eq_zero]

/--
theorem `add_eq_zero` / 定理 `add_eq_zero`

English:
theorem add_eq_zero
  given: {a b : R}
  statement: a + b = 0 ↔ a = b
  proof: by
  rw [← CharTwo.sub_eq_add]; rw [sub_eq_iff_eq_add]; rw [zero_add]

中文:
定理 add_eq_zero
  条件: {a b : R}
  结论: a + b = 0 ↔ a = b
  证明: by
  rw [← CharTwo.sub_eq_add]; rw [sub_eq_iff_eq_add]; rw [zero_add]
-/
protected theorem add_eq_zero {a b : R} : a + b = 0 ↔ a = b := by
  rw [← CharTwo.sub_eq_add]; rw [sub_eq_iff_eq_add]; rw [zero_add]

/--
theorem `intCast_eq_ite` / 定理 `intCast_eq_ite`

English:
theorem intCast_eq_ite
  given: (n : Int)
  statement: (n : R) = if Even n then 0 else 1
  proof: by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simpa using natCast_eq_ite n

@[simp]

中文:
定理 intCast_eq_ite
  条件: (n : 整数)
  结论: (n : R) = if Even n then 0 else 1
  证明: by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simpa using natCast_eq_ite n

@[simp]

Depends on / 依赖: eq_nat_or_neg, n.eq_nat_or_neg, natCast_eq_ite
-/
theorem intCast_eq_ite (n : Int) : (n : R) = if Even n then 0 else 1 := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simpa using natCast_eq_ite n

@[simp]
/--
theorem `range_intCast` / 定理 `range_intCast`

English:
theorem range_intCast
  statement: Set.range ((↑) : Int -> R) = {0, 1}
  proof: by
  rw [funext intCast_eq_ite]; rw [Set.range_ite_const]
  · use 0; simp
  · use 1; simp

中文:
定理 range_intCast
  结论: 集合.range ((↑) : 整数 -> R) = {0, 1}
  证明: by
  rw [funext intCast_eq_ite]; rw [Set.range_ite_const]
  · use 0; simp
  · use 1; simp

Depends on / 依赖: Set.range_ite_const, intCast_eq_ite, range_ite_const
-/
theorem range_intCast : Set.range ((↑) : Int -> R) = {0, 1} := by
  rw [funext intCast_eq_ite]; rw [Set.range_ite_const]
  · use 0; simp
  · use 1; simp

variable (R) in
/--
theorem `intCast_cases` / 定理 `intCast_cases`

English:
theorem intCast_cases
  given: (n : Int)
  statement: (n : R) = 0 ∨ (n : R) = 1
  proof: (Set.ext_iff.1 range_intCast _).1 (Set.mem_range_self _)

中文:
定理 intCast_cases
  条件: (n : 整数)
  结论: (n : R) = 0 ∨ (n : R) = 1
  证明: (Set.ext_iff.1 range_intCast _).1 (Set.mem_range_self _)

Depends on / 依赖: Set.ext_iff, Set.mem_range_self, ext_iff, mem_range_self, range_intCast
-/
theorem intCast_cases (n : Int) : (n : R) = 0 ∨ (n : R) = 1 :=
  (Set.ext_iff.1 range_intCast _).1 (Set.mem_range_self _)

/--
theorem `intCast_eq_mod` / 定理 `intCast_eq_mod`

English:
theorem intCast_eq_mod
  given: (n : Int)
  statement: (n : R) = (n % 2 : Int)
  proof: by
  simp [intCast_eq_ite, Int.even_iff]

中文:
定理 intCast_eq_mod
  条件: (n : 整数)
  结论: (n : R) = (n % 2 : 整数)
  证明: by
  simp [intCast_eq_ite, Int.even_iff]

Depends on / 依赖: Int.even_iff, even_iff, intCast_eq_ite
-/
theorem intCast_eq_mod (n : Int) : (n : R) = (n % 2 : Int) := by
  simp [intCast_eq_ite, Int.even_iff]

end Ring

section CommSemiring

variable [CommSemiring R] [CharP R 2]

/--
theorem `add_sq` / 定理 `add_sq`

English:
theorem add_sq
  given: (x y : R)
  statement: (x + y) ^ 2 = x ^ 2 + y ^ 2
  proof: by
  simp [add_pow_two]

中文:
定理 add_sq
  条件: (x y : R)
  结论: (x + y) ^ 2 = x ^ 2 + y ^ 2
  证明: by
  simp [add_pow_two]

Depends on / 依赖: add_pow_two
-/
theorem add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  simp [add_pow_two]

/--
theorem `add_mul_self` / 定理 `add_mul_self`

English:
theorem add_mul_self
  given: (x y : R)
  statement: (x + y) * (x + y) = x * x + y * y
  proof: by
  rw [← pow_two]; rw [← pow_two]; rw [← pow_two]; rw [add_sq]

中文:
定理 add_mul_self
  条件: (x y : R)
  结论: (x + y) * (x + y) = x * x + y * y
  证明: by
  rw [← pow_two]; rw [← pow_two]; rw [← pow_two]; rw [add_sq]

Depends on / 依赖: add_sq, pow_two
-/
theorem add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y := by
  rw [← pow_two]; rw [← pow_two]; rw [← pow_two]; rw [add_sq]

/--
Definition of `sqAddMonoidHom` / `sqAddMonoidHom` 的定义

English:
definition sqAddMonoidHom
  signature: : R ->+ R where
  body: (· ^ 2)
  map_zero' := zero_pow two_ne_zero
  map_add' := add_sq

中文:
定义 sqAddMonoidHom
  签名: : R ->+ R where
  定义体: (· ^ 2)
  map_zero' := zero_pow two_ne_zero
  map_add' := add_sq
-/
private def sqAddMonoidHom : R ->+ R where
  toFun := (· ^ 2)
  map_zero' := zero_pow two_ne_zero
  map_add' := add_sq

/--
theorem `list_sum_sq` / 定理 `list_sum_sq`

English:
theorem list_sum_sq
  given: (l : List R)
  statement: l.sum ^ 2 = (l.map (· ^ 2)).sum
  proof: map_list_sum sqAddMonoidHom _

中文:
定理 list_sum_sq
  条件: (l : 列表 R)
  结论: l.求和 ^ 2 = (l.map (· ^ 2)).求和
  证明: map_list_sum sqAddMonoidHom _

Depends on / 依赖: map_list_sum, sqAddMonoidHom
-/
theorem list_sum_sq (l : List R) : l.sum ^ 2 = (l.map (· ^ 2)).sum :=
  map_list_sum sqAddMonoidHom _

/--
theorem `list_sum_mul_self` / 定理 `list_sum_mul_self`

English:
theorem list_sum_mul_self
  given: (l : List R)
  statement: l.sum * l.sum = (List.map (fun x => x * x) l).sum
  proof: by
  simp_rw [← pow_two, list_sum_sq]

中文:
定理 list_sum_mul_self
  条件: (l : 列表 R)
  结论: l.求和 * l.求和 = (列表.map (fun x => x * x) l).求和
  证明: by
  simp_rw [← pow_two, list_sum_sq]

Depends on / 依赖: list_sum_sq, pow_two, simp_rw
-/
theorem list_sum_mul_self (l : List R) : l.sum * l.sum = (List.map (fun x => x * x) l).sum := by
  simp_rw [← pow_two, list_sum_sq]

/--
theorem `multiset_sum_sq` / 定理 `multiset_sum_sq`

English:
theorem multiset_sum_sq
  given: (l : Multiset R)
  statement: l.sum ^ 2 = (l.map (· ^ 2)).sum
  proof: map_multiset_sum sqAddMonoidHom _

中文:
定理 multiset_sum_sq
  条件: (l : Multiset R)
  结论: l.求和 ^ 2 = (l.map (· ^ 2)).求和
  证明: map_multiset_sum sqAddMonoidHom _

Depends on / 依赖: map_multiset_sum, sqAddMonoidHom
-/
theorem multiset_sum_sq (l : Multiset R) : l.sum ^ 2 = (l.map (· ^ 2)).sum :=
  map_multiset_sum sqAddMonoidHom _

/--
theorem `multiset_sum_mul_self` / 定理 `multiset_sum_mul_self`

English:
theorem multiset_sum_mul_self
  given: (l : Multiset R)
  proof: by simp_rw [← pow_two, multiset_sum_sq]

中文:
定理 multiset_sum_mul_self
  条件: (l : Multiset R)
  证明: by simp_rw [← pow_two, multiset_sum_sq]

Depends on / 依赖: multiset_sum_sq, pow_two, simp_rw
-/
theorem multiset_sum_mul_self (l : Multiset R) :
    l.sum * l.sum = (Multiset.map (fun x => x * x) l).sum := by simp_rw [← pow_two, multiset_sum_sq]

/--
theorem `sum_sq` / 定理 `sum_sq`

English:
theorem sum_sq
  given: (s : Finset ι) (f : ι -> R)
  statement: (∑ i in s, f i) ^ 2 = ∑ i in s, f i ^ 2
  proof: map_sum sqAddMonoidHom _ _

中文:
定理 sum_sq
  条件: (s : 有限集 ι) (f : ι -> R)
  结论: (∑ i in s, f i) ^ 2 = ∑ i in s, f i ^ 2
  证明: map_sum sqAddMonoidHom _ _

Depends on / 依赖: map_sum, sqAddMonoidHom
-/
theorem sum_sq (s : Finset ι) (f : ι -> R) : (∑ i in s, f i) ^ 2 = ∑ i in s, f i ^ 2 :=
  map_sum sqAddMonoidHom _ _

/--
theorem `sum_mul_self` / 定理 `sum_mul_self`

English:
theorem sum_mul_self
  given: (s : Finset ι) (f : ι -> R)
  proof: by simp_rw [← pow_two, sum_sq]

中文:
定理 sum_mul_self
  条件: (s : 有限集 ι) (f : ι -> R)
  证明: by simp_rw [← pow_two, sum_sq]

Depends on / 依赖: pow_two, simp_rw, sum_sq
-/
theorem sum_mul_self (s : Finset ι) (f : ι -> R) :
    ((∑ i in s, f i) * ∑ i in s, f i) = ∑ i in s, f i * f i := by simp_rw [← pow_two, sum_sq]

end CommSemiring

section CommRing

variable [CommRing R] [CharP R 2] [NoZeroDivisors R]

/--
theorem `sq_injective` / 定理 `sq_injective`

English:
theorem sq_injective
  statement: Function.Injective fun x : R => x ^ 2
  proof: by
  intro x y h
  rwa [← CharTwo.add_eq_zero, ← add_sq, pow_eq_zero_iff two_ne_zero, CharTwo.add_eq_zero] at h

@[scoped simp]

中文:
定理 sq_injective
  结论: 函数.单射 fun x : R => x ^ 2
  证明: by
  intro x y h
  rwa [← CharTwo.add_eq_zero, ← add_sq, pow_eq_zero_iff two_ne_zero, CharTwo.add_eq_zero] at h

@[scoped simp]

Depends on / 依赖: CharTwo, CharTwo.add_eq_zero, add_eq_zero, add_sq, pow_eq_zero_iff, two_ne_zero
-/
theorem sq_injective : Function.Injective fun x : R => x ^ 2 := by
  intro x y h
  rwa [← CharTwo.add_eq_zero, ← add_sq, pow_eq_zero_iff two_ne_zero, CharTwo.add_eq_zero] at h

@[scoped simp]
/--
theorem `sq_inj` / 定理 `sq_inj`

English:
theorem sq_inj
  given: {x y : R}
  statement: x ^ 2 = y ^ 2 ↔ x = y
  proof: sq_injective.eq_iff

中文:
定理 sq_inj
  条件: {x y : R}
  结论: x ^ 2 = y ^ 2 ↔ x = y
  证明: sq_injective.eq_iff

Depends on / 依赖: eq_iff, sq_injective, sq_injective.eq_iff
-/
theorem sq_inj {x y : R} : x ^ 2 = y ^ 2 ↔ x = y :=
  sq_injective.eq_iff

end CommRing

@[deprecated (since := "2026-02-05")]
alias CommRing.sq_injective := sq_injective

@[deprecated (since := "2026-02-05")]
alias CommRing.sq_inj := sq_inj

end CharTwo

section ringChar

variable [Ring R]

/--
theorem `neg_one_eq_one_iff` / 定理 `neg_one_eq_one_iff`

English:
theorem neg_one_eq_one_iff
  given: [Nontrivial R]
  statement: (-1 : R) = 1 ↔ ringChar R = 2
  proof: by
  refine ⟨fun h => ?_, fun h => @CharTwo.neg_eq _ _ (ringChar.of_eq h) 1⟩
  rw [eq_comm]; rw [← sub_eq_zero]; rw [sub_neg_eq_add]; rw [← Nat.cast_one]; rw [← Nat.cast_add] at h
  exact ((Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h)).resolve_left CharP.ringChar_ne_one

中文:
定理 neg_one_eq_one_iff
  条件: [非平凡 R]
  结论: (-1 : R) = 1 ↔ ringChar R = 2
  证明: by
  refine ⟨fun h => ?_, fun h => @CharTwo.neg_eq _ _ (ringChar.of_eq h) 1⟩
  rw [eq_comm]; rw [← sub_eq_zero]; rw [sub_neg_eq_add]; rw [← Nat.cast_one]; rw [← Nat.cast_add] at h
  exact ((Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h)).resolve_left CharP.ringChar_ne_one

Depends on / 依赖: CharP.ringChar_ne_one, CharTwo, CharTwo.neg_eq, Nat.cast_add, Nat.cast_one, Nat.dvd_prime, Nat.prime_two, cast_add, cast_one, dvd_prime, eq_comm, neg_eq, of_eq, prime_two, resolve_left, ringChar, ringChar.dvd, ringChar.of_eq, ringChar_ne_one, sub_eq_zero
-/
theorem neg_one_eq_one_iff [Nontrivial R] : (-1 : R) = 1 ↔ ringChar R = 2 := by
  refine ⟨fun h => ?_, fun h => @CharTwo.neg_eq _ _ (ringChar.of_eq h) 1⟩
  rw [eq_comm]; rw [← sub_eq_zero]; rw [sub_neg_eq_add]; rw [← Nat.cast_one]; rw [← Nat.cast_add] at h
  exact ((Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h)).resolve_left CharP.ringChar_ne_one

end ringChar
