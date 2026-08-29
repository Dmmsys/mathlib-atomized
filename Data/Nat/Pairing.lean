/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Set.Lattice.Image

/-!
# Naturals pairing function

This file defines a pairing function for the naturals as follows:
```text
 0 1 4 9 16
 2 3 5 10 17
 6 7 8 11 18
12 13 14 15 19
20 21 22 23 24
```

It has the advantage of being monotone in both directions and sending `⟦0, n^2 - 1⟧` to
`⟦0, n - 1⟧²`.
-/

@[expose] public section

assert_not_exists Monoid

open Prod Decidable Function

namespace Nat

/-- Pairing function for the natural numbers. -/
@[pp_nodot]
/--
Definition of `pair` / `pair` 的定义

English:
definition pair
  signature: (a b : Nat)
  body: if a < b then b * b + a else a * a + a + b

中文:
定义 pair
  签名: (a b : 自然数)
  定义体: if a < b then b * b + a else a * a + a + b
-/
def pair (a b : Nat) : Nat :=
  if a < b then b * b + a else a * a + a + b

/-- Unpairing function for the natural numbers. -/
@[pp_nodot]
/--
Definition of `unpair` / `unpair` 的定义

English:
definition unpair
  signature: (n : Nat)
  body: let s := sqrt n
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)

@[simp]

中文:
定义 unpair
  签名: (n : 自然数)
  定义体: let s := sqrt n
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)

@[simp]
-/
def unpair (n : Nat) : Nat × Nat :=
  let s := sqrt n
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)

@[simp]
/--
theorem `pair_unpair` / 定理 `pair_unpair`

English:
theorem pair_unpair
  given: (n : Nat)
  statement: pair (unpair n).1 (unpair n).2 = n
  proof: by
  dsimp only [unpair]; let s := sqrt n
  have sm : s * s + (n - s * s) = n := Nat.add_sub_cancel' (sqrt_le _)
  split_ifs with h
  · simp [s, pair, h, sm]
  · have hl : n - s * s - s <= s := Nat.sub_le_iff_le_add.2
      (Nat.sub_le_iff_le_add'.2 <| by rw [← Nat.add_assoc]; apply sqrt_le_add)
   

中文:
定理 pair_unpair
  条件: (n : 自然数)
  结论: pair (unpair n).1 (unpair n).2 = n
  证明: by
  dsimp only [unpair]; let s := sqrt n
  have sm : s * s + (n - s * s) = n := Nat.add_sub_cancel' (sqrt_le _)
  split_ifs with h
  · simp [s, pair, h, sm]
  · have hl : n - s * s - s <= s := Nat.sub_le_iff_le_add.2
      (Nat.sub_le_iff_le_add'.2 <| by rw [← Nat.add_assoc]; apply sqrt_le_add)
   

Depends on / 依赖: Nat.add_assoc, Nat.add_sub_cancel, Nat.sub_le_iff_le_add, add_assoc, add_sub_cancel, hl.not_gt, le_of_not_gt, not_gt, split_ifs, sqrt_le, sqrt_le_add, sub_le_iff_le_add, unpair
-/
theorem pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 = n := by
  dsimp only [unpair]; let s := sqrt n
  have sm : s * s + (n - s * s) = n := Nat.add_sub_cancel' (sqrt_le _)
  split_ifs with h
  · simp [s, pair, h, sm]
  · have hl : n - s * s - s <= s := Nat.sub_le_iff_le_add.2
      (Nat.sub_le_iff_le_add'.2 <| by rw [← Nat.add_assoc]; apply sqrt_le_add)
    simp [s, pair, hl.not_gt, Nat.add_assoc, Nat.add_sub_cancel' (le_of_not_gt h), sm]

/--
theorem `pair_eq_of_unpair_eq` / 定理 `pair_eq_of_unpair_eq`

English:
theorem pair_eq_of_unpair_eq
  given: {n a b} (H : unpair n = (a, b))
  statement: pair a b = n
  proof: by
  simpa [H] using pair_unpair n

@[simp]

中文:
定理 pair_eq_of_unpair_eq
  条件: {n a b} (H : unpair n = (a, b))
  结论: pair a b = n
  证明: by
  simpa [H] using pair_unpair n

@[simp]

Depends on / 依赖: pair_unpair
-/
theorem pair_eq_of_unpair_eq {n a b} (H : unpair n = (a, b)) : pair a b = n := by
  simpa [H] using pair_unpair n

@[simp]
/--
theorem `unpair_pair` / 定理 `unpair_pair`

English:
theorem unpair_pair
  given: (a b : Nat)
  statement: unpair (pair a b) = (a, b)
  proof: by
  dsimp only [pair]; split_ifs with h
  · show unpair (b * b + a) = (a, b)
    have be : sqrt (b * b + a) = b := sqrt_add_eq _ (le_trans (le_of_lt h) (Nat.le_add_left _ _))
    simp [unpair, be, Nat.add_sub_cancel_left, h]
  · show unpair (a * a + a + b) = (a, b)
    have ae : sqrt (a * a + (a + 

中文:
定理 unpair_pair
  条件: (a b : 自然数)
  结论: unpair (pair a b) = (a, b)
  证明: by
  dsimp only [pair]; split_ifs with h
  · show unpair (b * b + a) = (a, b)
    have be : sqrt (b * b + a) = b := sqrt_add_eq _ (le_trans (le_of_lt h) (Nat.le_add_left _ _))
    simp [unpair, be, Nat.add_sub_cancel_left, h]
  · show unpair (a * a + a + b) = (a, b)
    have ae : sqrt (a * a + (a + 

Depends on / 依赖: Nat.add_assoc, Nat.add_le_add_left, Nat.add_sub_cancel_left, Nat.le_add_left, add_assoc, add_le_add_left, add_sub_cancel_left, le_add_left, le_of_lt, le_of_not_gt, le_trans, split_ifs, sqrt_add_eq, unpair
-/
theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a, b) := by
  dsimp only [pair]; split_ifs with h
  · show unpair (b * b + a) = (a, b)
    have be : sqrt (b * b + a) = b := sqrt_add_eq _ (le_trans (le_of_lt h) (Nat.le_add_left _ _))
    simp [unpair, be, Nat.add_sub_cancel_left, h]
  · show unpair (a * a + a + b) = (a, b)
    have ae : sqrt (a * a + (a + b)) = a := by
      rw [sqrt_add_eq]
      exact Nat.add_le_add_left (le_of_not_gt h) _
    simp [unpair, ae, Nat.add_assoc, Nat.add_sub_cancel_left]

/-- An equivalence between `ℕ × ℕ` and `ℕ`. -/
@[simps -fullyApplied]
/--
Definition of `pairEquiv` / `pairEquiv` 的定义

English:
definition pairEquiv
  signature: : Nat × Nat ≃ Nat
  body: ⟨uncurry pair, unpair, fun ⟨a, b⟩ => unpair_pair a b, pair_unpair⟩

中文:
定义 pairEquiv
  签名: : 自然数 × 自然数 ≃ 自然数
  定义体: ⟨uncurry pair, unpair, fun ⟨a, b⟩ => unpair_pair a b, pair_unpair⟩

Depends on / 依赖: pair_unpair, uncurry, unpair, unpair_pair
-/
def pairEquiv : Nat × Nat ≃ Nat :=
  ⟨uncurry pair, unpair, fun ⟨a, b⟩ => unpair_pair a b, pair_unpair⟩

/--
theorem `surjective_unpair` / 定理 `surjective_unpair`

English:
theorem surjective_unpair
  statement: Surjective unpair
  proof: pairEquiv.symm.surjective

@[simp]

中文:
定理 surjective_unpair
  结论: 满射 unpair
  证明: pairEquiv.symm.surjective

@[simp]

Depends on / 依赖: pairEquiv, pairEquiv.symm.surjective, surjective
-/
theorem surjective_unpair : Surjective unpair :=
  pairEquiv.symm.surjective

@[simp]
/--
theorem `pair_eq_pair` / 定理 `pair_eq_pair`

English:
theorem pair_eq_pair
  given: {a b c d : Nat}
  statement: pair a b = pair c d ↔ a = c ∧ b = d
  proof: pairEquiv.injective.eq_iff.trans (@Prod.ext_iff Nat Nat (a, b) (c, d))

中文:
定理 pair_eq_pair
  条件: {a b c d : 自然数}
  结论: pair a b = pair c d ↔ a = c ∧ b = d
  证明: pairEquiv.injective.eq_iff.trans (@Prod.ext_iff Nat Nat (a, b) (c, d))

Depends on / 依赖: Prod.ext_iff, eq_iff, ext_iff, injective, pairEquiv, pairEquiv.injective.eq_iff.trans
-/
theorem pair_eq_pair {a b c d : Nat} : pair a b = pair c d ↔ a = c ∧ b = d :=
  pairEquiv.injective.eq_iff.trans (@Prod.ext_iff Nat Nat (a, b) (c, d))

/--
theorem `unpair_lt` / 定理 `unpair_lt`

English:
theorem unpair_lt
  given: {n : Nat} (n1 : 1 <= n)
  statement: (unpair n).1 < n
  proof: by
  let s := sqrt n
  simp only [unpair]
  by_cases h : n - s * s < s <;> simp only [h, ↓reduceIte, gt_iff_lt, s]
  · exact lt_of_lt_of_le h (sqrt_le_self _)
  · simp only [not_lt] at h
    have s0 : 0 < s := sqrt_pos.2 n1
    exact lt_of_le_of_lt h (Nat.sub_lt n1 (Nat.mul_pos s0 s0))

@[simp]

中文:
定理 unpair_lt
  条件: {n : 自然数} (n1 : 1 <= n)
  结论: (unpair n).1 < n
  证明: by
  let s := sqrt n
  simp only [unpair]
  by_cases h : n - s * s < s <;> simp only [h, ↓reduceIte, gt_iff_lt, s]
  · exact lt_of_lt_of_le h (sqrt_le_self _)
  · simp only [not_lt] at h
    have s0 : 0 < s := sqrt_pos.2 n1
    exact lt_of_le_of_lt h (Nat.sub_lt n1 (Nat.mul_pos s0 s0))

@[simp]

Depends on / 依赖: Nat.mul_pos, Nat.sub_lt, gt_iff_lt, lt_of_le_of_lt, lt_of_lt_of_le, mul_pos, not_lt, reduceIte, sqrt_le_self, sqrt_pos, sub_lt, unpair
-/
theorem unpair_lt {n : Nat} (n1 : 1 <= n) : (unpair n).1 < n := by
  let s := sqrt n
  simp only [unpair]
  by_cases h : n - s * s < s <;> simp only [h, ↓reduceIte, gt_iff_lt, s]
  · exact lt_of_lt_of_le h (sqrt_le_self _)
  · simp only [not_lt] at h
    have s0 : 0 < s := sqrt_pos.2 n1
    exact lt_of_le_of_lt h (Nat.sub_lt n1 (Nat.mul_pos s0 s0))

@[simp]
/--
theorem `unpair_zero` / 定理 `unpair_zero`

English:
theorem unpair_zero
  statement: unpair 0 = 0
  proof: by
  rw [unpair]
  simp

中文:
定理 unpair_zero
  结论: unpair 0 = 0
  证明: by
  rw [unpair]
  simp

Depends on / 依赖: unpair
-/
theorem unpair_zero : unpair 0 = 0 := by
  rw [unpair]
  simp

/--
theorem `unpair_left_le` / 定理 `unpair_left_le`

English:
theorem unpair_left_le
  statement: forall n : Nat, (unpair n).1 <= n

中文:
定理 unpair_left_le
  结论: 对任意 n : 自然数, (unpair n).1 <= n
-/
theorem unpair_left_le : forall n : Nat, (unpair n).1 <= n
  | 0 => by simp
  | _ + 1 => le_of_lt (unpair_lt (Nat.succ_pos _))

/--
theorem `left_le_pair` / 定理 `left_le_pair`

English:
theorem left_le_pair
  given: (a b : Nat)
  statement: a <= pair a b
  proof: by simpa using unpair_left_le (pair a b)

中文:
定理 left_le_pair
  条件: (a b : 自然数)
  结论: a <= pair a b
  证明: by simpa using unpair_left_le (pair a b)

Depends on / 依赖: unpair_left_le
-/
theorem left_le_pair (a b : Nat) : a <= pair a b := by simpa using unpair_left_le (pair a b)

/--
theorem `right_le_pair` / 定理 `right_le_pair`

English:
theorem right_le_pair
  given: (a b : Nat)
  statement: b <= pair a b
  proof: by
  by_cases h : a < b
  · simpa [pair, h] using le_trans (le_mul_self _) (Nat.le_add_right _ _)
  · simp [pair, h]

中文:
定理 right_le_pair
  条件: (a b : 自然数)
  结论: b <= pair a b
  证明: by
  by_cases h : a < b
  · simpa [pair, h] using le_trans (le_mul_self _) (Nat.le_add_right _ _)
  · simp [pair, h]

Depends on / 依赖: Nat.le_add_right, le_add_right, le_mul_self, le_trans
-/
theorem right_le_pair (a b : Nat) : b <= pair a b := by
  by_cases h : a < b
  · simpa [pair, h] using le_trans (le_mul_self _) (Nat.le_add_right _ _)
  · simp [pair, h]

/--
theorem `unpair_right_le` / 定理 `unpair_right_le`

English:
theorem unpair_right_le
  given: (n : Nat)
  statement: (unpair n).2 <= n
  proof: by
  simpa using right_le_pair n.unpair.1 n.unpair.2

中文:
定理 unpair_right_le
  条件: (n : 自然数)
  结论: (unpair n).2 <= n
  证明: by
  simpa using right_le_pair n.unpair.1 n.unpair.2

Depends on / 依赖: n.unpair, right_le_pair, unpair
-/
theorem unpair_right_le (n : Nat) : (unpair n).2 <= n := by
  simpa using right_le_pair n.unpair.1 n.unpair.2

/--
theorem `pair_lt_pair_left` / 定理 `pair_lt_pair_left`

English:
theorem pair_lt_pair_left
  given: {a₁ a₂} (b) (h : a₁ < a₂)
  statement: pair a₁ b < pair a₂ b
  proof: by
  by_cases h₁ : a₁ < b <;> simp only [pair, h₁, ↓reduceIte, Nat.add_assoc]
  · by_cases h₂ : a₂ < b
    · simp [h₂, h]
    simp only [h₂, ↓reduceIte]
    apply Nat.add_lt_add_of_le_of_lt
    · exact Nat.mul_self_le_mul_self (not_lt.mp h₂)
    · exact Nat.lt_add_right _ h
  · simp at h₁
    simp o

中文:
定理 pair_lt_pair_left
  条件: {a₁ a₂} (b) (h : a₁ < a₂)
  结论: pair a₁ b < pair a₂ b
  证明: by
  by_cases h₁ : a₁ < b <;> simp only [pair, h₁, ↓reduceIte, Nat.add_assoc]
  · by_cases h₂ : a₂ < b
    · simp [h₂, h]
    simp only [h₂, ↓reduceIte]
    apply Nat.add_lt_add_of_le_of_lt
    · exact Nat.mul_self_le_mul_self (not_lt.mp h₂)
    · exact Nat.lt_add_right _ h
  · simp at h₁
    simp o

Depends on / 依赖: Nat.add_assoc, Nat.add_lt_add_of_le_of_lt, Nat.add_lt_add_right, Nat.lt_add_right, Nat.mul_self_le_mul_self, Nat.mul_self_lt_mul_self, add_assoc, add_lt_add, add_lt_add_of_le_of_lt, add_lt_add_right, ite_false, lt_add_right, lt_of_le_of_lt, mul_self_le_mul_self, mul_self_lt_mul_self, not_lt, not_lt.mp, not_lt_of_gt, reduceIte
-/
theorem pair_lt_pair_left {a₁ a₂} (b) (h : a₁ < a₂) : pair a₁ b < pair a₂ b := by
  by_cases h₁ : a₁ < b <;> simp only [pair, h₁, ↓reduceIte, Nat.add_assoc]
  · by_cases h₂ : a₂ < b
    · simp [h₂, h]
    simp only [h₂, ↓reduceIte]
    apply Nat.add_lt_add_of_le_of_lt
    · exact Nat.mul_self_le_mul_self (not_lt.mp h₂)
    · exact Nat.lt_add_right _ h
  · simp at h₁
    simp only [not_lt_of_gt (lt_of_le_of_lt h₁ h), ite_false]
    apply add_lt_add
    · exact Nat.mul_self_lt_mul_self h
    · apply Nat.add_lt_add_right; assumption

/--
theorem `pair_lt_pair_right` / 定理 `pair_lt_pair_right`

English:
theorem pair_lt_pair_right
  given: (a) {b₁ b₂} (h : b₁ < b₂)
  statement: pair a b₁ < pair a b₂
  proof: by
  by_cases h₁ : a < b₁
  · simpa [pair, h₁, Nat.add_assoc, lt_trans h₁ h, h] using mul_self_lt_mul_self h
  · simp only [pair, h₁, ↓reduceIte, Nat.add_assoc]
    by_cases h₂ : a < b₂; swap; · simp [h₂, h]
    simp only [h₂, ↓reduceIte]
    rw [Nat.add_comm]; rw [Nat.add_comm _ a]; rw [Nat.add_ass

中文:
定理 pair_lt_pair_right
  条件: (a) {b₁ b₂} (h : b₁ < b₂)
  结论: pair a b₁ < pair a b₂
  证明: by
  by_cases h₁ : a < b₁
  · simpa [pair, h₁, Nat.add_assoc, lt_trans h₁ h, h] using mul_self_lt_mul_self h
  · simp only [pair, h₁, ↓reduceIte, Nat.add_assoc]
    by_cases h₂ : a < b₂; swap; · simp [h₂, h]
    simp only [h₂, ↓reduceIte]
    rw [Nat.add_comm]; rw [Nat.add_comm _ a]; rw [Nat.add_ass

Depends on / 依赖: Nat.add_assoc, Nat.add_comm, Nat.add_lt_add_iff_left, Nat.le_add_left, add_assoc, add_comm, add_lt_add_iff_left, le_add_left, le_trans, lt_trans, mul_self_lt_mul_self, not_lt, not_lt.mp, reduceIte, sqrt_add_eq, sqrt_lt
-/
theorem pair_lt_pair_right (a) {b₁ b₂} (h : b₁ < b₂) : pair a b₁ < pair a b₂ := by
  by_cases h₁ : a < b₁
  · simpa [pair, h₁, Nat.add_assoc, lt_trans h₁ h, h] using mul_self_lt_mul_self h
  · simp only [pair, h₁, ↓reduceIte, Nat.add_assoc]
    by_cases h₂ : a < b₂; swap; · simp [h₂, h]
    simp only [h₂, ↓reduceIte]
    rw [Nat.add_comm]; rw [Nat.add_comm _ a]; rw [Nat.add_assoc]; rw [Nat.add_lt_add_iff_left]
    rwa [Nat.add_comm, ← sqrt_lt, sqrt_add_eq]
    exact le_trans (not_lt.mp h₁) (Nat.le_add_left _ _)

/--
theorem `pair_lt_max_add_one_sq` / 定理 `pair_lt_max_add_one_sq`

English:
theorem pair_lt_max_add_one_sq
  given: (m n : Nat)
  statement: pair m n < (max m n + 1) ^ 2
  proof: by
  simp only [pair, Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.add_assoc]
  split_ifs <;> simp [Nat.le_of_lt, not_lt.1, *] <;> lia

中文:
定理 pair_lt_max_add_one_sq
  条件: (m n : 自然数)
  结论: pair m n < (最大值 m n + 1) ^ 2
  证明: by
  simp only [pair, Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.add_assoc]
  split_ifs <;> simp [Nat.le_of_lt, not_lt.1, *] <;> lia

Depends on / 依赖: Nat.add_assoc, Nat.add_mul, Nat.le_of_lt, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.pow_two, add_assoc, add_mul, le_of_lt, mul_add, mul_one, not_lt, one_mul, pow_two, split_ifs
-/
theorem pair_lt_max_add_one_sq (m n : Nat) : pair m n < (max m n + 1) ^ 2 := by
  simp only [pair, Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.add_assoc]
  split_ifs <;> simp [Nat.le_of_lt, not_lt.1, *] <;> lia

/--
theorem `max_sq_add_min_le_pair` / 定理 `max_sq_add_min_le_pair`

English:
theorem max_sq_add_min_le_pair
  given: (m n : Nat)
  statement: max m n ^ 2 + min m n <= pair m n
  proof: by
  rw [pair]
  rcases lt_or_ge m n with h | h
  · rw [if_pos h, max_eq_right h.le, min_eq_left h.le, Nat.pow_two]
  rw [if_neg h.not_gt]; rw [max_eq_left h]; rw [min_eq_right h]; rw [Nat.pow_two]; rw [Nat.add_assoc]; rw [Nat.add_le_add_iff_left]
  exact Nat.le_add_left _ _

中文:
定理 max_sq_add_min_le_pair
  条件: (m n : 自然数)
  结论: 最大值 m n ^ 2 + 最小值 m n <= pair m n
  证明: by
  rw [pair]
  rcases lt_or_ge m n with h | h
  · rw [if_pos h, max_eq_right h.le, min_eq_left h.le, Nat.pow_two]
  rw [if_neg h.not_gt]; rw [max_eq_left h]; rw [min_eq_right h]; rw [Nat.pow_two]; rw [Nat.add_assoc]; rw [Nat.add_le_add_iff_left]
  exact Nat.le_add_left _ _

Depends on / 依赖: Nat.add_assoc, Nat.add_le_add_iff_left, Nat.le_add_left, Nat.pow_two, add_assoc, add_le_add_iff_left, h.le, h.not_gt, if_neg, if_pos, le_add_left, lt_or_ge, max_eq_left, max_eq_right, min_eq_left, min_eq_right, not_gt, pow_two
-/
theorem max_sq_add_min_le_pair (m n : Nat) : max m n ^ 2 + min m n <= pair m n := by
  rw [pair]
  rcases lt_or_ge m n with h | h
  · rw [if_pos h, max_eq_right h.le, min_eq_left h.le, Nat.pow_two]
  rw [if_neg h.not_gt]; rw [max_eq_left h]; rw [min_eq_right h]; rw [Nat.pow_two]; rw [Nat.add_assoc]; rw [Nat.add_le_add_iff_left]
  exact Nat.le_add_left _ _

/--
theorem `add_le_pair` / 定理 `add_le_pair`

English:
theorem add_le_pair
  given: (m n : Nat)
  statement: m + n <= pair m n
  proof: by
  simp only [pair, Nat.add_assoc]
  split_ifs
  · have := le_mul_self n
    lia
  · exact Nat.le_add_left _ _

中文:
定理 add_le_pair
  条件: (m n : 自然数)
  结论: m + n <= pair m n
  证明: by
  simp only [pair, Nat.add_assoc]
  split_ifs
  · have := le_mul_self n
    lia
  · exact Nat.le_add_left _ _

Depends on / 依赖: Nat.add_assoc, Nat.le_add_left, add_assoc, le_add_left, le_mul_self, split_ifs
-/
theorem add_le_pair (m n : Nat) : m + n <= pair m n := by
  simp only [pair, Nat.add_assoc]
  split_ifs
  · have := le_mul_self n
    lia
  · exact Nat.le_add_left _ _

/--
theorem `unpair_add_le` / 定理 `unpair_add_le`

English:
theorem unpair_add_le
  given: (n : Nat)
  statement: (unpair n).1 + (unpair n).2 <= n
  proof: (add_le_pair _ _).trans_eq (pair_unpair _)

中文:
定理 unpair_add_le
  条件: (n : 自然数)
  结论: (unpair n).1 + (unpair n).2 <= n
  证明: (add_le_pair _ _).trans_eq (pair_unpair _)

Depends on / 依赖: add_le_pair, pair_unpair, trans_eq
-/
theorem unpair_add_le (n : Nat) : (unpair n).1 + (unpair n).2 <= n :=
  (add_le_pair _ _).trans_eq (pair_unpair _)

end Nat

open Nat

section CompleteLattice

@[to_dual]
/--
theorem `iSup_unpair` / 定理 `iSup_unpair`

English:
theorem iSup_unpair
  given: {α} [CompleteLattice α] (f : Nat -> Nat -> α)
  proof: by
  rw [← (iSup_prod : ⨆ i : Nat × Nat]; rw [f i.1 i.2 = _)]; rw [← Nat.surjective_unpair.iSup_comp]

中文:
定理 iSup_unpair
  条件: {α} [完备格 α] (f : 自然数 -> 自然数 -> α)
  证明: by
  rw [← (iSup_prod : ⨆ i : Nat × Nat]; rw [f i.1 i.2 = _)]; rw [← Nat.surjective_unpair.iSup_comp]

Depends on / 依赖: Nat.surjective_unpair.iSup_comp, iSup_comp, iSup_prod, surjective_unpair
-/
theorem iSup_unpair {α} [CompleteLattice α] (f : Nat -> Nat -> α) :
    ⨆ n : Nat, f n.unpair.1 n.unpair.2 = ⨆ (i : Nat) (j : Nat), f i j := by
  rw [← (iSup_prod : ⨆ i : Nat × Nat]; rw [f i.1 i.2 = _)]; rw [← Nat.surjective_unpair.iSup_comp]

end CompleteLattice

namespace Set

/--
theorem `iUnion_unpair_prod` / 定理 `iUnion_unpair_prod`

English:
theorem iUnion_unpair_prod
  given: {α β} {s : Nat -> Set α} {t : Nat -> Set β}
  proof: by
  rw [← Set.iUnion_prod]
  exact surjective_unpair.iUnion_comp (fun x => s x.fst ×ˢ t x.snd)

中文:
定理 iUnion_unpair_prod
  条件: {α β} {s : 自然数 -> 集合 α} {t : 自然数 -> 集合 β}
  证明: by
  rw [← Set.iUnion_prod]
  exact surjective_unpair.iUnion_comp (fun x => s x.fst ×ˢ t x.snd)

Depends on / 依赖: Set.iUnion_prod, iUnion_comp, iUnion_prod, surjective_unpair, surjective_unpair.iUnion_comp, x.fst, x.snd
-/
theorem iUnion_unpair_prod {α β} {s : Nat -> Set α} {t : Nat -> Set β} :
    ⋃ n : Nat, s n.unpair.fst ×ˢ t n.unpair.snd = (⋃ n, s n) ×ˢ ⋃ n, t n := by
  rw [← Set.iUnion_prod]
  exact surjective_unpair.iUnion_comp (fun x => s x.fst ×ˢ t x.snd)

/--
theorem `iUnion_unpair` / 定理 `iUnion_unpair`

English:
theorem iUnion_unpair
  given: {α} (f : Nat -> Nat -> Set α)
  proof: iSup_unpair f

中文:
定理 iUnion_unpair
  条件: {α} (f : 自然数 -> 自然数 -> 集合 α)
  证明: iSup_unpair f

Depends on / 依赖: iSup_unpair
-/
theorem iUnion_unpair {α} (f : Nat -> Nat -> Set α) :
    ⋃ n : Nat, f n.unpair.1 n.unpair.2 = ⋃ (i : Nat) (j : Nat), f i j :=
  iSup_unpair f

/--
theorem `iInter_unpair` / 定理 `iInter_unpair`

English:
theorem iInter_unpair
  given: {α} (f : Nat -> Nat -> Set α)
  proof: iInf_unpair f

中文:
定理 i整数er_unpair
  条件: {α} (f : 自然数 -> 自然数 -> 集合 α)
  证明: iInf_unpair f

Depends on / 依赖: iInf_unpair
-/
theorem iInter_unpair {α} (f : Nat -> Nat -> Set α) :
    ⋂ n : Nat, f n.unpair.1 n.unpair.2 = ⋂ (i : Nat) (j : Nat), f i j :=
  iInf_unpair f

end Set
