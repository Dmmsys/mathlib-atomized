/-
Copyright (c) 2025 Beibei Xiong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beibei Xiong, Yu Shao, Weijie Jiang, Zhengfeng Yang
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# Stirling Numbers

This file defines Stirling numbers of the first and second kinds, proves their fundamental
recurrence relations, and establishes some of their key properties and identities.

## The Stirling numbers of the first kind

The unsigned Stirling numbers of the first kind, represent the number of ways
to partition `n` distinct elements into `k` non-empty cycles.

## The Stirling numbers of the second kind

The Stirling numbers of the second kind, represent the number of ways to partition
`n` distinct elements into `k` non-empty subsets.

## Main definitions

* `Nat.stirlingFirst`: the number of ways to partition `n` distinct elements into `k` non-empty
  cycles, defined by the recursive relationship it satisfies.
* `Nat.stirlingSecond`: the number of ways to partition `n` distinct elements into `k` non-empty
  subsets, defined by the recursive relationship it satisfies.

## References

* [Knuth, *The Art of Computer Programming*, Volume 1, §1.2.6][knuth1997]
-/

@[expose] public section

open Nat

namespace Nat

/--
Definition of `stirlingFirst` / `stirlingFirst` 的定义

English:
definition stirlingFirst
  signature: : Nat -> Nat -> Nat

中文:
定义 stirlingFirst
  签名: : 自然数 -> 自然数 -> 自然数
-/
def stirlingFirst : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * stirlingFirst n (k + 1) + stirlingFirst n k

@[simp]
/--
theorem `stirlingFirst_zero` / 定理 `stirlingFirst_zero`

English:
theorem stirlingFirst_zero
  statement: stirlingFirst 0 0 = 1
  proof: rfl

@[simp]

中文:
定理 stirlingFirst_zero
  结论: stirlingFirst 0 0 = 1
  证明: rfl

@[simp]
-/
theorem stirlingFirst_zero : stirlingFirst 0 0 = 1 :=
  rfl

@[simp]
/--
theorem `stirlingFirst_zero_succ` / 定理 `stirlingFirst_zero_succ`

English:
theorem stirlingFirst_zero_succ
  given: (k : Nat)
  statement: stirlingFirst 0 (succ k) = 0
  proof: rfl

@[simp]

中文:
定理 stirlingFirst_zero_succ
  条件: (k : 自然数)
  结论: stirlingFirst 0 (succ k) = 0
  证明: rfl

@[simp]
-/
theorem stirlingFirst_zero_succ (k : Nat) : stirlingFirst 0 (succ k) = 0 :=
  rfl

@[simp]
/--
theorem `stirlingFirst_succ_zero` / 定理 `stirlingFirst_succ_zero`

English:
theorem stirlingFirst_succ_zero
  given: (n : Nat)
  statement: stirlingFirst (succ n) 0 = 0
  proof: rfl

中文:
定理 stirlingFirst_succ_zero
  条件: (n : 自然数)
  结论: stirlingFirst (succ n) 0 = 0
  证明: rfl
-/
theorem stirlingFirst_succ_zero (n : Nat) : stirlingFirst (succ n) 0 = 0 :=
  rfl

/--
theorem `stirlingFirst_succ_left` / 定理 `stirlingFirst_succ_left`

English:
theorem stirlingFirst_succ_left
  given: (n k : Nat) (hk : k != 0)
  proof: by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hk)
  rfl

中文:
定理 stirlingFirst_succ_left
  条件: (n k : 自然数) (hk : k != 0)
  证明: by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hk)
  rfl

Depends on / 依赖: Nat.exists_eq_add_of_le, Nat.pos_of_ne_zero, exists_eq_add_of_le, pos_of_ne_zero
-/
theorem stirlingFirst_succ_left (n k : Nat) (hk : k != 0) :
    stirlingFirst (n + 1) k = n * stirlingFirst n k + stirlingFirst n (k - 1) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hk)
  rfl

/--
theorem `stirlingFirst_succ_right` / 定理 `stirlingFirst_succ_right`

English:
theorem stirlingFirst_succ_right
  given: (n k : Nat) (hn : n != 0)
  proof: by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hn)
  rfl

中文:
定理 stirlingFirst_succ_right
  条件: (n k : 自然数) (hn : n != 0)
  证明: by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hn)
  rfl

Depends on / 依赖: Nat.exists_eq_add_of_le, Nat.pos_of_ne_zero, exists_eq_add_of_le, pos_of_ne_zero
-/
theorem stirlingFirst_succ_right (n k : Nat) (hn : n != 0) :
    stirlingFirst n (k + 1) =
      (n - 1) * stirlingFirst (n - 1) (k + 1) + stirlingFirst (n - 1) k := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hn)
  rfl

/--
theorem `stirlingFirst_succ_succ` / 定理 `stirlingFirst_succ_succ`

English:
theorem stirlingFirst_succ_succ
  given: (n k : Nat)
  proof: by
  rfl

中文:
定理 stirlingFirst_succ_succ
  条件: (n k : 自然数)
  证明: by
  rfl
-/
theorem stirlingFirst_succ_succ (n k : Nat) :
    stirlingFirst (n + 1) (k + 1) = n * stirlingFirst n (k + 1) + stirlingFirst n k := by
  rfl

/--
theorem `stirlingFirst_eq_zero_of_lt` / 定理 `stirlingFirst_eq_zero_of_lt`

English:
theorem stirlingFirst_eq_zero_of_lt
  statement: forall {n k : Nat}, n < k -> stirlingFirst n k = 0

中文:
定理 stirlingFirst_eq_zero_of_lt
  结论: 对任意 {n k : 自然数}, n < k -> stirlingFirst n k = 0
-/
theorem stirlingFirst_eq_zero_of_lt : forall {n k : Nat}, n < k -> stirlingFirst n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => by rw [stirlingFirst]
  | n + 1, k + 1, hk => by
    rw [stirlingFirst_succ_succ]; rw [stirlingFirst_eq_zero_of_lt (Nat.lt_of_succ_lt_succ hk)]; rw [stirlingFirst_eq_zero_of_lt (Nat.lt_of_succ_lt hk)]; rw [mul_zero]

/--
theorem `stirlingFirst_self` / 定理 `stirlingFirst_self`

English:
theorem stirlingFirst_self
  given: (n : Nat)
  statement: stirlingFirst n n = 1
  proof: by
  induction n <;> simp only [*, stirlingFirst, stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self _),
    mul_zero]

中文:
定理 stirlingFirst_self
  条件: (n : 自然数)
  结论: stirlingFirst n n = 1
  证明: by
  induction n <;> simp only [*, stirlingFirst, stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self _),
    mul_zero]

Depends on / 依赖: Nat.lt_succ_self, lt_succ_self, mul_zero, stirlingFirst, stirlingFirst_eq_zero_of_lt
-/
theorem stirlingFirst_self (n : Nat) : stirlingFirst n n = 1 := by
  induction n <;> simp only [*, stirlingFirst, stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self _),
    mul_zero]

/--
theorem `stirlingFirst_succ_self_left` / 定理 `stirlingFirst_succ_self_left`

English:
theorem stirlingFirst_succ_self_left
  given: (n : Nat)
  statement: stirlingFirst (n + 1) n = (n + 1).choose 2
  proof: by
  induction n with
  | zero => simp only [zero_add, stirlingFirst_succ_zero, choose_succ_self]
  | succ n ih =>
    rw [stirlingFirst_succ_succ]; rw [ih]; rw [stirlingFirst_self]; rw [mul_one]; rw [Nat.choose_succ_succ (n + 1)]; rw [Nat.choose_one_right]

中文:
定理 stirlingFirst_succ_self_left
  条件: (n : 自然数)
  结论: stirlingFirst (n + 1) n = (n + 1).choose 2
  证明: by
  induction n with
  | zero => simp only [zero_add, stirlingFirst_succ_zero, choose_succ_self]
  | succ n ih =>
    rw [stirlingFirst_succ_succ]; rw [ih]; rw [stirlingFirst_self]; rw [mul_one]; rw [Nat.choose_succ_succ (n + 1)]; rw [Nat.choose_one_right]

Depends on / 依赖: Nat.choose_one_right, Nat.choose_succ_succ, choose_one_right, choose_succ_self, choose_succ_succ, mul_one, stirlingFirst_self, stirlingFirst_succ_succ, stirlingFirst_succ_zero, zero_add
-/
theorem stirlingFirst_succ_self_left (n : Nat) : stirlingFirst (n + 1) n = (n + 1).choose 2 := by
  induction n with
  | zero => simp only [zero_add, stirlingFirst_succ_zero, choose_succ_self]
  | succ n ih =>
    rw [stirlingFirst_succ_succ]; rw [ih]; rw [stirlingFirst_self]; rw [mul_one]; rw [Nat.choose_succ_succ (n + 1)]; rw [Nat.choose_one_right]

/--
theorem `stirlingFirst_one_right` / 定理 `stirlingFirst_one_right`

English:
theorem stirlingFirst_one_right
  given: (n : Nat)
  statement: stirlingFirst (n + 1) 1 = n.factorial
  proof: by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [stirlingFirst_succ_succ]; rw [zero_add]; rw [hn]; rw [stirlingFirst_succ_zero]
    simp [Nat.factorial_succ]

中文:
定理 stirlingFirst_one_right
  条件: (n : 自然数)
  结论: stirlingFirst (n + 1) 1 = n.factorial
  证明: by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [stirlingFirst_succ_succ]; rw [zero_add]; rw [hn]; rw [stirlingFirst_succ_zero]
    simp [Nat.factorial_succ]

Depends on / 依赖: Nat.factorial_succ, factorial_succ, stirlingFirst_succ_succ, stirlingFirst_succ_zero, zero_add
-/
theorem stirlingFirst_one_right (n : Nat) : stirlingFirst (n + 1) 1 = n.factorial := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [stirlingFirst_succ_succ]; rw [zero_add]; rw [hn]; rw [stirlingFirst_succ_zero]
    simp [Nat.factorial_succ]


/--
Definition of `stirlingSecond` / `stirlingSecond` 的定义

English:
definition stirlingSecond
  signature: : Nat -> Nat -> Nat

中文:
定义 stirlingSecond
  签名: : 自然数 -> 自然数 -> 自然数

Depends on / 依赖: Functor, LawfulFunctor, ofLawfulFunctor
-/
def stirlingSecond : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
    (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k

@[simp]
/--
theorem `stirlingSecond_zero` / 定理 `stirlingSecond_zero`

English:
theorem stirlingSecond_zero
  statement: stirlingSecond 0 0 = 1
  proof: rfl

@[simp]

中文:
定理 stirlingSecond_zero
  结论: stirlingSecond 0 0 = 1
  证明: rfl

@[simp]
-/
theorem stirlingSecond_zero : stirlingSecond 0 0 = 1 :=
  rfl

@[simp]
/--
theorem `stirlingSecond_zero_succ` / 定理 `stirlingSecond_zero_succ`

English:
theorem stirlingSecond_zero_succ
  given: (k : Nat)
  statement: stirlingSecond 0 (succ k) = 0
  proof: rfl

@[simp]

中文:
定理 stirlingSecond_zero_succ
  条件: (k : 自然数)
  结论: stirlingSecond 0 (succ k) = 0
  证明: rfl

@[simp]
-/
theorem stirlingSecond_zero_succ (k : Nat) : stirlingSecond 0 (succ k) = 0 :=
  rfl

@[simp]
/--
theorem `stirlingSecond_succ_zero` / 定理 `stirlingSecond_succ_zero`

English:
theorem stirlingSecond_succ_zero
  given: (n : Nat)
  statement: stirlingSecond (succ n) 0 = 0
  proof: rfl

中文:
定理 stirlingSecond_succ_zero
  条件: (n : 自然数)
  结论: stirlingSecond (succ n) 0 = 0
  证明: rfl
-/
theorem stirlingSecond_succ_zero (n : Nat) : stirlingSecond (succ n) 0 = 0 :=
  rfl

/--
theorem `stirlingSecond_succ_left` / 定理 `stirlingSecond_succ_left`

English:
theorem stirlingSecond_succ_left
  given: (n k : Nat) (hk : k != 0)
  proof: by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hk)
  rfl

中文:
定理 stirlingSecond_succ_left
  条件: (n k : 自然数) (hk : k != 0)
  证明: by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hk)
  rfl

Depends on / 依赖: Nat.exists_eq_add_of_le, Nat.pos_of_ne_zero, exists_eq_add_of_le, pos_of_ne_zero
-/
theorem stirlingSecond_succ_left (n k : Nat) (hk : k != 0) :
    stirlingSecond (n + 1) k = k * stirlingSecond n k + stirlingSecond n (k - 1) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hk)
  rfl

/--
theorem `stirlingSecond_succ_right` / 定理 `stirlingSecond_succ_right`

English:
theorem stirlingSecond_succ_right
  given: (n k : Nat) (hn : n != 0)
  proof: by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hn)
  rfl

中文:
定理 stirlingSecond_succ_right
  条件: (n k : 自然数) (hn : n != 0)
  证明: by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hn)
  rfl

Depends on / 依赖: Nat.exists_eq_add_of_le, Nat.pos_of_ne_zero, Part.fix, exists_eq_add_of_le, pos_of_ne_zero
-/
theorem stirlingSecond_succ_right (n k : Nat) (hn : n != 0) :
    stirlingSecond n (k + 1) =
      (k + 1) * stirlingSecond (n - 1) (k + 1) + stirlingSecond (n - 1) k := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hn)
  rfl

/--
theorem `stirlingSecond_succ_succ` / 定理 `stirlingSecond_succ_succ`

English:
theorem stirlingSecond_succ_succ
  given: (n k : Nat)
  proof: rfl

中文:
定理 stirlingSecond_succ_succ
  条件: (n k : 自然数)
  证明: rfl
-/
theorem stirlingSecond_succ_succ (n k : Nat) :
    stirlingSecond (n + 1) (k + 1) =
      (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k := rfl

/--
theorem `stirlingSecond_eq_zero_of_lt` / 定理 `stirlingSecond_eq_zero_of_lt`

English:
theorem stirlingSecond_eq_zero_of_lt
  statement: forall {n k : Nat}, n < k -> stirlingSecond n k = 0

中文:
定理 stirlingSecond_eq_zero_of_lt
  结论: 对任意 {n k : 自然数}, n < k -> stirlingSecond n k = 0
-/
theorem stirlingSecond_eq_zero_of_lt : forall {n k : Nat}, n < k -> stirlingSecond n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => by rw [stirlingSecond]
  | n + 1, k + 1, hk => by
    simp only [stirlingSecond_succ_succ, stirlingSecond_eq_zero_of_lt (Nat.lt_of_succ_lt_succ hk),
      stirlingSecond_eq_zero_of_lt (Nat.lt_of_succ_lt hk), mul_zero]

/--
theorem `stirlingSecond_self` / 定理 `stirlingSecond_self`

English:
theorem stirlingSecond_self
  given: (n : Nat)
  statement: stirlingSecond n n = 1
  proof: by
  induction n <;> simp only [*, stirlingSecond, stirlingSecond_eq_zero_of_lt (lt_succ_self _),
    mul_zero]

中文:
定理 stirlingSecond_self
  条件: (n : 自然数)
  结论: stirlingSecond n n = 1
  证明: by
  induction n <;> simp only [*, stirlingSecond, stirlingSecond_eq_zero_of_lt (lt_succ_self _),
    mul_zero]

Depends on / 依赖: lt_succ_self, mul_zero, stirlingSecond, stirlingSecond_eq_zero_of_lt
-/
theorem stirlingSecond_self (n : Nat) : stirlingSecond n n = 1 := by
  induction n <;> simp only [*, stirlingSecond, stirlingSecond_eq_zero_of_lt (lt_succ_self _),
    mul_zero]

/--
theorem `stirlingSecond_one_right` / 定理 `stirlingSecond_one_right`

English:
theorem stirlingSecond_one_right
  given: (n : Nat)
  statement: stirlingSecond (n + 1) 1 = 1
  proof: by
  induction n with
  | zero => rfl
  | succ n ih => rw [stirlingSecond, stirlingSecond_succ_zero, ih]

中文:
定理 stirlingSecond_one_right
  条件: (n : 自然数)
  结论: stirlingSecond (n + 1) 1 = 1
  证明: by
  induction n with
  | zero => rfl
  | succ n ih => rw [stirlingSecond, stirlingSecond_succ_zero, ih]

Depends on / 依赖: stirlingSecond, stirlingSecond_succ_zero
-/
theorem stirlingSecond_one_right (n : Nat) : stirlingSecond (n + 1) 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stirlingSecond, stirlingSecond_succ_zero, ih]

/--
theorem `stirlingSecond_succ_self_left` / 定理 `stirlingSecond_succ_self_left`

English:
theorem stirlingSecond_succ_self_left
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp only [zero_add, stirlingSecond_succ_zero, choose_succ_self]
  | succ n ih =>
    rw [stirlingSecond_succ_succ]; rw [ih]; rw [stirlingSecond_self]; rw [mul_one]; rw [Nat.choose_succ_succ (n + 1)]; rw [Nat.choose_one_right]

中文:
定理 stirlingSecond_succ_self_left
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp only [zero_add, stirlingSecond_succ_zero, choose_succ_self]
  | succ n ih =>
    rw [stirlingSecond_succ_succ]; rw [ih]; rw [stirlingSecond_self]; rw [mul_one]; rw [Nat.choose_succ_succ (n + 1)]; rw [Nat.choose_one_right]

Depends on / 依赖: Nat.choose_one_right, Nat.choose_succ_succ, choose_one_right, choose_succ_self, choose_succ_succ, mul_one, stirlingSecond_self, stirlingSecond_succ_succ, stirlingSecond_succ_zero, zero_add
-/
theorem stirlingSecond_succ_self_left (n : Nat) :
    stirlingSecond (n + 1) n = (n + 1).choose 2 := by
  induction n with
  | zero => simp only [zero_add, stirlingSecond_succ_zero, choose_succ_self]
  | succ n ih =>
    rw [stirlingSecond_succ_succ]; rw [ih]; rw [stirlingSecond_self]; rw [mul_one]; rw [Nat.choose_succ_succ (n + 1)]; rw [Nat.choose_one_right]

end Nat
