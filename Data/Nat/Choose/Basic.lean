/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Stuart Presnell, Antoine Chambert-Loir,
  María-Inés de Frutos—Fernández
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Binomial coefficients

This file defines binomial coefficients and proves simple lemmas (i.e. those not
requiring more imports).
For the lemma that `n.choose k` counts the `k`-element-subsets of an `n`-element set,
see `Finset.card_powersetCard` in `Mathlib/Data/Finset/Powerset.lean`.

## Main definition and results

* `Nat.choose`: binomial coefficients, defined inductively
* `Nat.choose_eq_factorial_div_factorial`: a proof that `choose n k = n! / (k! * (n - k)!)`
* `Nat.choose_symm`: symmetry of binomial coefficients
* `Nat.choose_le_succ_of_lt_half_left`: `choose n k` is increasing for small values of `k`
* `Nat.choose_le_middle`: `choose n r` is maximised when `r` is `n/2`
* `Nat.descFactorial_eq_factorial_mul_choose`: Relates binomial coefficients to the descending
  factorial. This is used to prove `Nat.choose_le_pow` and variants. We provide similar statements
  for the ascending factorial.
* `Nat.multichoose`: whereas `choose` counts combinations, `multichoose` counts multicombinations.
  The fact that this is indeed the correct counting function for multisets is proved in
  `Sym.card_sym_eq_multichoose` in `Data.Sym.Card`.
* `Nat.multichoose_eq` : a proof that `multichoose n k = (n + k - 1).choose k`.
  This is central to the "stars and bars" technique in informal mathematics, where we switch between
  counting multisets of size `k` over an alphabet of size `n` to counting strings of `k` elements
  ("stars") separated by `n-1` dividers ("bars"). See `Data.Sym.Card` for more detail.

## Tags

binomial coefficient, combination, multicombination, stars and bars
-/

@[expose] public section

namespace Nat

/--
Definition of `choose` / `choose` 的定义

English:
definition choose
  signature: : Nat -> Nat -> Nat

中文:
定义 choose
  签名: : 自然数 -> 自然数 -> 自然数
-/
def choose : Nat -> Nat -> Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

@[simp, grind =]
/--
theorem `choose_zero_right` / 定理 `choose_zero_right`

English:
theorem choose_zero_right
  given: (n : Nat)
  statement: choose n 0 = 1
  proof: by cases n <;> rfl

@[simp, grind =]

中文:
定理 choose_zero_right
  条件: (n : 自然数)
  结论: choose n 0 = 1
  证明: by cases n <;> rfl

@[simp, grind =]
-/
theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl

@[simp, grind =]
/--
theorem `choose_zero_succ` / 定理 `choose_zero_succ`

English:
theorem choose_zero_succ
  given: (k : Nat)
  statement: choose 0 (succ k) = 0
  proof: rfl

@[grind =]

中文:
定理 choose_zero_succ
  条件: (k : 自然数)
  结论: choose 0 (succ k) = 0
  证明: rfl

@[grind =]
-/
theorem choose_zero_succ (k : Nat) : choose 0 (succ k) = 0 :=
  rfl

@[grind =]
/--
theorem `choose_succ_succ` / 定理 `choose_succ_succ`

English:
theorem choose_succ_succ
  given: (n k : Nat)
  statement: choose (succ n) (succ k) = choose n k + choose n (succ k)
  proof: rfl

中文:
定理 choose_succ_succ
  条件: (n k : 自然数)
  结论: choose (succ n) (succ k) = choose n k + choose n (succ k)
  证明: rfl
-/
theorem choose_succ_succ (n k : Nat) : choose (succ n) (succ k) = choose n k + choose n (succ k) :=
  rfl

/--
theorem `choose_succ_succ'` / 定理 `choose_succ_succ'`

English:
theorem choose_succ_succ'
  given: (n k : Nat)
  statement: choose (n + 1) (k + 1) = choose n k + choose n (k + 1)
  proof: rfl

中文:
定理 choose_succ_succ'
  条件: (n k : 自然数)
  结论: choose (n + 1) (k + 1) = choose n k + choose n (k + 1)
  证明: rfl
-/
theorem choose_succ_succ' (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) :=
  rfl

/--
theorem `choose_succ_left` / 定理 `choose_succ_left`

English:
theorem choose_succ_left
  given: (n k : Nat) (hk : 0 < k)
  proof: by
  obtain ⟨l, rfl⟩ : exists l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rfl

中文:
定理 choose_succ_left
  条件: (n k : 自然数) (hk : 0 < k)
  证明: by
  obtain ⟨l, rfl⟩ : exists l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rfl

Depends on / 依赖: Nat.exists_eq_add_of_le, exists_eq_add_of_le
-/
theorem choose_succ_left (n k : Nat) (hk : 0 < k) :
    choose (n + 1) k = choose n (k - 1) + choose n k := by
  obtain ⟨l, rfl⟩ : exists l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rfl

/--
theorem `choose_succ_right` / 定理 `choose_succ_right`

English:
theorem choose_succ_right
  given: (n k : Nat) (hn : 0 < n)
  proof: by
  obtain ⟨l, rfl⟩ : exists l, n = l + 1 := Nat.exists_eq_add_of_le' hn
  rfl

中文:
定理 choose_succ_right
  条件: (n k : 自然数) (hn : 0 < n)
  证明: by
  obtain ⟨l, rfl⟩ : exists l, n = l + 1 := Nat.exists_eq_add_of_le' hn
  rfl

Depends on / 依赖: Nat.exists_eq_add_of_le, exists_eq_add_of_le
-/
theorem choose_succ_right (n k : Nat) (hn : 0 < n) :
    choose n (k + 1) = choose (n - 1) k + choose (n - 1) (k + 1) := by
  obtain ⟨l, rfl⟩ : exists l, n = l + 1 := Nat.exists_eq_add_of_le' hn
  rfl

/--
theorem `choose_eq_choose_pred_add` / 定理 `choose_eq_choose_pred_add`

English:
theorem choose_eq_choose_pred_add
  given: {n k : Nat} (hn : 0 < n) (hk : 0 < k)
  proof: by
  obtain ⟨l, rfl⟩ : exists l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rw [choose_succ_right _ _ hn]; rw [Nat.add_one_sub_one]

@[grind <=]

中文:
定理 choose_eq_choose_pred_add
  条件: {n k : 自然数} (hn : 0 < n) (hk : 0 < k)
  证明: by
  obtain ⟨l, rfl⟩ : exists l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rw [choose_succ_right _ _ hn]; rw [Nat.add_one_sub_one]

@[grind <=]

Depends on / 依赖: Nat.add_one_sub_one, Nat.exists_eq_add_of_le, add_one_sub_one, choose_succ_right, exists_eq_add_of_le
-/
theorem choose_eq_choose_pred_add {n k : Nat} (hn : 0 < n) (hk : 0 < k) :
    choose n k = choose (n - 1) (k - 1) + choose (n - 1) k := by
  obtain ⟨l, rfl⟩ : exists l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rw [choose_succ_right _ _ hn]; rw [Nat.add_one_sub_one]

@[grind <=]
/--
theorem `choose_eq_zero_of_lt` / 定理 `choose_eq_zero_of_lt`

English:
theorem choose_eq_zero_of_lt
  statement: forall {n k}, n < k -> choose n k = 0
  proof: lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := lt_of_succ_lt hk
    rw [choose_succ_succ]; rw [choose_eq_zero_of_lt hnk]; rw [choose_eq_zero_of_lt hnk1]

@[simp]

中文:
定理 choose_eq_zero_of_lt
  结论: 对任意 {n k}, n < k -> choose n k = 0
  证明: lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := lt_of_succ_lt hk
    rw [choose_succ_succ]; rw [choose_eq_zero_of_lt hnk]; rw [choose_eq_zero_of_lt hnk1]

@[simp]

Depends on / 依赖: lt_of_succ_lt_succ
-/
theorem choose_eq_zero_of_lt : forall {n k}, n < k -> choose n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => choose_zero_succ _
  | n + 1, k + 1, hk => by
    have hnk : n < k := lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := lt_of_succ_lt hk
    rw [choose_succ_succ]; rw [choose_eq_zero_of_lt hnk]; rw [choose_eq_zero_of_lt hnk1]

@[simp]
/--
theorem `choose_self` / 定理 `choose_self`

English:
theorem choose_self
  given: (n : Nat)
  statement: choose n n = 1
  proof: by
  induction n <;> grind

@[simp]

中文:
定理 choose_self
  条件: (n : 自然数)
  结论: choose n n = 1
  证明: by
  induction n <;> grind

@[simp]
-/
theorem choose_self (n : Nat) : choose n n = 1 := by
  induction n <;> grind

@[simp]
/--
theorem `choose_succ_self` / 定理 `choose_succ_self`

English:
theorem choose_succ_self
  given: (n : Nat)
  statement: choose n (succ n) = 0
  proof: choose_eq_zero_of_lt (lt_succ_self _)

@[simp]

中文:
定理 choose_succ_self
  条件: (n : 自然数)
  结论: choose n (succ n) = 0
  证明: choose_eq_zero_of_lt (lt_succ_self _)

@[simp]

Depends on / 依赖: choose_eq_zero_of_lt, lt_succ_self
-/
theorem choose_succ_self (n : Nat) : choose n (succ n) = 0 :=
  choose_eq_zero_of_lt (lt_succ_self _)

@[simp]
/--
lemma `choose_one_right` / 引理 `choose_one_right`

English:
lemma choose_one_right
  given: (n : Nat)
  statement: choose n 1 = n
  proof: by induction n <;> simp [*, choose, Nat.add_comm]

中文:
引理 choose_one_right
  条件: (n : 自然数)
  结论: choose n 1 = n
  证明: by induction n <;> simp [*, choose, Nat.add_comm]

Depends on / 依赖: Nat.add_comm, add_comm
-/
lemma choose_one_right (n : Nat) : choose n 1 = n := by induction n <;> simp [*, choose, Nat.add_comm]

-- The `n + 1`-st triangle number is `n` more than the `n`-th triangle number
/--
theorem `triangle_succ` / 定理 `triangle_succ`

English:
theorem triangle_succ
  given: (n : Nat)
  statement: (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n
  proof: by
  rw [← add_mul_div_left]; rw [Nat.mul_comm 2 n]; rw [← Nat.mul_add]; rw [Nat.add_sub_cancel]; rw [Nat.mul_comm]
  cases n <;> rfl; apply zero_lt_succ

中文:
定理 triangle_succ
  条件: (n : 自然数)
  结论: (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n
  证明: by
  rw [← add_mul_div_left]; rw [Nat.mul_comm 2 n]; rw [← Nat.mul_add]; rw [Nat.add_sub_cancel]; rw [Nat.mul_comm]
  cases n <;> rfl; apply zero_lt_succ

Depends on / 依赖: Nat.add_sub_cancel, Nat.mul_add, Nat.mul_comm, add_mul_div_left, add_sub_cancel, mul_add, mul_comm, zero_lt_succ
-/
theorem triangle_succ (n : Nat) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  rw [← add_mul_div_left]; rw [Nat.mul_comm 2 n]; rw [← Nat.mul_add]; rw [Nat.add_sub_cancel]; rw [Nat.mul_comm]
  cases n <;> rfl; apply zero_lt_succ

/--
theorem `choose_two_right` / 定理 `choose_two_right`

English:
theorem choose_two_right
  given: (n : Nat)
  statement: choose n 2 = n * (n - 1) / 2
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [triangle_succ n]; rw [choose]; rw [ih]
    simp [Nat.add_comm]

中文:
定理 choose_two_right
  条件: (n : 自然数)
  结论: choose n 2 = n * (n - 1) / 2
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [triangle_succ n]; rw [choose]; rw [ih]
    simp [Nat.add_comm]

Depends on / 依赖: Nat.add_comm, add_comm, triangle_succ
-/
theorem choose_two_right (n : Nat) : choose n 2 = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [triangle_succ n]; rw [choose]; rw [ih]
    simp [Nat.add_comm]

/--
theorem `choose_pos` / 定理 `choose_pos`

English:
theorem choose_pos
  statement: forall {n k}, k <= n -> 0 < choose n k

中文:
定理 choose_pos
  结论: 对任意 {n k}, k <= n -> 0 < choose n k
-/
theorem choose_pos : forall {n k}, k <= n -> 0 < choose n k
  | 0, _, hk => by rw [Nat.eq_zero_of_le_zero hk]; decide
  | n + 1, 0, _ => by simp
  | _ + 1, _ + 1, hk => Nat.add_pos_left (choose_pos (le_of_succ_le_succ hk)) _

/--
theorem `choose_eq_zero_iff` / 定理 `choose_eq_zero_iff`

English:
theorem choose_eq_zero_iff
  given: {n k : Nat}
  statement: n.choose k = 0 ↔ n < k
  proof: ⟨fun h => lt_of_not_ge (mt Nat.choose_pos h.symm.not_lt), Nat.choose_eq_zero_of_lt⟩

中文:
定理 choose_eq_zero_iff
  条件: {n k : 自然数}
  结论: n.choose k = 0 ↔ n < k
  证明: ⟨fun h => lt_of_not_ge (mt Nat.choose_pos h.symm.not_lt), Nat.choose_eq_zero_of_lt⟩

Depends on / 依赖: Nat.choose_eq_zero_of_lt, Nat.choose_pos, choose_eq_zero_of_lt, choose_pos, h.symm.not_lt, lt_of_not_ge, not_lt
-/
theorem choose_eq_zero_iff {n k : Nat} : n.choose k = 0 ↔ n < k :=
  ⟨fun h => lt_of_not_ge (mt Nat.choose_pos h.symm.not_lt), Nat.choose_eq_zero_of_lt⟩

/--
theorem `choose_ne_zero_iff` / 定理 `choose_ne_zero_iff`

English:
theorem choose_ne_zero_iff
  given: {n k : Nat}
  statement: n.choose k != 0 ↔ k <= n
  proof: not_iff_not.1 by simp [choose_eq_zero_iff]

中文:
定理 choose_ne_zero_iff
  条件: {n k : 自然数}
  结论: n.choose k != 0 ↔ k <= n
  证明: not_iff_not.1 by simp [choose_eq_zero_iff]

Depends on / 依赖: choose_eq_zero_iff, not_iff_not
-/
theorem choose_ne_zero_iff {n k : Nat} : n.choose k != 0 ↔ k <= n :=
not_iff_not.1 by simp [choose_eq_zero_iff]

/--
lemma `choose_ne_zero` / 引理 `choose_ne_zero`

English:
lemma choose_ne_zero
  given: {n k : Nat} (h : k <= n)
  statement: n.choose k != 0
  proof: (choose_pos h).ne'

中文:
引理 choose_ne_zero
  条件: {n k : 自然数} (h : k <= n)
  结论: n.choose k != 0
  证明: (choose_pos h).ne'

Depends on / 依赖: choose_pos
-/
lemma choose_ne_zero {n k : Nat} (h : k <= n) : n.choose k != 0 :=
  (choose_pos h).ne'

/--
theorem `add_one_mul_choose_eq` / 定理 `add_one_mul_choose_eq`

English:
theorem add_one_mul_choose_eq
  statement: forall n k, (n + 1) * choose n k = choose (n + 1) (k + 1) * (k + 1)

中文:
定理 add_one_mul_choose_eq
  结论: 对任意 n k, (n + 1) * choose n k = choose (n + 1) (k + 1) * (k + 1)
-/
theorem add_one_mul_choose_eq : forall n k, (n + 1) * choose n k = choose (n + 1) (k + 1) * (k + 1)
  | 0, 0 => by decide
  | 0, k + 1 => by simp [choose]
  | n + 1, 0 => by simp [choose, mul_succ, Nat.add_comm]
  | n + 1, k + 1 => by
    rw [choose_succ_succ' (n + 1) (k + 1)]; rw [Nat.add_mul _ _ (k + 1 + 1)]; rw [← add_one_mul_choose_eq n]; rw [mul_add_one]; rw [← add_one_mul_choose_eq n]; rw [Nat.add_right_comm _ _ (_ * _)]; rw [← Nat.mul_add]; rw [← choose_succ_succ']; rw [← add_one_mul]

/--
theorem `choose_mul_factorial_mul_factorial` / 定理 `choose_mul_factorial_mul_factorial`

English:
theorem choose_mul_factorial_mul_factorial
  statement: forall {n k}, k <= n -> choose n k * k ! * (n - k)! = n !
  proof: by
        rw [← choose_mul_factorial_mul_factorial (le_of_succ_le_succ hk)]
        simp [factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h₁ : (n - k)! = (n - k) * (n - k.succ)! := by
        rw [← succ_sub_succ]; rw [succ_sub (le_of_lt_succ hk₁)]; rw [factorial_succ]
      have h₂ : choose n (succ k) * k.succ ! * ((n - k) * (n - k.succ)!) = (n - k) * n ! := by
        rw [← choose_mul_factorial_mul_factorial (le_of_lt_succ hk₁)]
        simp [factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h₃ : k * n ! <= n * n ! := Nat.mul_le_mul_right _ (le_of_succ_le_succ hk)
      rw [choose_succ_succ]; rw [Nat.add_mul]; rw [Nat.add_mul]; rw [succ_sub_succ]; rw [h]; rw [h₁]; rw [h₂]; rw [Nat.add_mul]; rw [Nat.mul_sub_right_distrib]; rw [factorial_succ]; rw [← Nat.add_sub_assoc h₃]; rw [Nat.add_assoc]; rw [← Nat.add_mul]; rw [Nat.add_sub_cancel_left]; rw [Nat.add_comm]
    · rw [hk₁]; simp [Nat.mul_comm, choose, Nat.sub_self]

中文:
定理 choose_mul_factorial_mul_factorial
  结论: 对任意 {n k}, k <= n -> choose n k * k ! * (n - k)! = n !
  证明: by
        rw [← choose_mul_factorial_mul_factorial (le_of_succ_le_succ hk)]
        simp [factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h₁ : (n - k)! = (n - k) * (n - k.succ)! := by
        rw [← succ_sub_succ]; rw [succ_sub (le_of_lt_succ hk₁)]; rw [factorial_succ]
      have h₂ : choose n (succ k) * k.succ ! * ((n - k) * (n - k.succ)!) = (n - k) * n ! := by
        rw [← choose_mul_factorial_mul_factorial (le_of_lt_succ hk₁)]
        simp [factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h₃ : k * n ! <= n * n ! := Nat.mul_le_mul_right _ (le_of_succ_le_succ hk)
      rw [choose_succ_succ]; rw [Nat.add_mul]; rw [Nat.add_mul]; rw [succ_sub_succ]; rw [h]; rw [h₁]; rw [h₂]; rw [Nat.add_mul]; rw [Nat.mul_sub_right_distrib]; rw [factorial_succ]; rw [← Nat.add_sub_assoc h₃]; rw [Nat.add_assoc]; rw [← Nat.add_mul]; rw [Nat.add_sub_cancel_left]; rw [Nat.add_comm]
    · rw [hk₁]; simp [Nat.mul_comm, choose, Nat.sub_self]

Depends on / 依赖: Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, choose_mul_factorial_mul_factorial, factorial_succ, k.succ, le_of_lt_succ, le_of_succ_le_succ, mul_assoc, mul_comm, mul_left_comm, succ_sub, succ_sub_succ
-/
theorem choose_mul_factorial_mul_factorial : forall {n k}, k <= n -> choose n k * k ! * (n - k)! = n !
  | 0, _, hk => by simp [Nat.eq_zero_of_le_zero hk]
  | n + 1, 0, _ => by simp
  | n + 1, succ k, hk => by
    rcases lt_or_eq_of_le hk with hk₁ | hk₁
    · have h : choose n k * k.succ ! * (n - k)! = (k + 1) * n ! := by
        rw [← choose_mul_factorial_mul_factorial (le_of_succ_le_succ hk)]
        simp [factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h₁ : (n - k)! = (n - k) * (n - k.succ)! := by
        rw [← succ_sub_succ]; rw [succ_sub (le_of_lt_succ hk₁)]; rw [factorial_succ]
      have h₂ : choose n (succ k) * k.succ ! * ((n - k) * (n - k.succ)!) = (n - k) * n ! := by
        rw [← choose_mul_factorial_mul_factorial (le_of_lt_succ hk₁)]
        simp [factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h₃ : k * n ! <= n * n ! := Nat.mul_le_mul_right _ (le_of_succ_le_succ hk)
      rw [choose_succ_succ]; rw [Nat.add_mul]; rw [Nat.add_mul]; rw [succ_sub_succ]; rw [h]; rw [h₁]; rw [h₂]; rw [Nat.add_mul]; rw [Nat.mul_sub_right_distrib]; rw [factorial_succ]; rw [← Nat.add_sub_assoc h₃]; rw [Nat.add_assoc]; rw [← Nat.add_mul]; rw [Nat.add_sub_cancel_left]; rw [Nat.add_comm]
    · rw [hk₁]; simp [Nat.mul_comm, choose, Nat.sub_self]

/--
theorem `choose_mul` / 定理 `choose_mul`

English:
theorem choose_mul
  given: {n k s : Nat} (hsk : s <= k)
  proof: by
  obtain hnk | hkn := lt_or_ge n k
  · grind
  have h : 0 < (n - k)! * (k - s)! * s ! := by apply_rules [factorial_pos, Nat.mul_pos]
  apply Nat.mul_right_cancel h
  calc
    _ = n.choose s * s ! * ((n - s).choose (k - s) * (k - s)! * (n - s - (k - s))!) := by
      grind [choose_mul_factorial_mul_factorial]
    _ = n.choose s * (n - s).choose (k - s) * ((n - k)! * (k - s)! * s !) := by
      grind

中文:
定理 choose_mul
  条件: {n k s : 自然数} (hsk : s <= k)
  证明: by
  obtain hnk | hkn := lt_or_ge n k
  · grind
  have h : 0 < (n - k)! * (k - s)! * s ! := by apply_rules [factorial_pos, Nat.mul_pos]
  apply Nat.mul_right_cancel h
  calc
    _ = n.choose s * s ! * ((n - s).choose (k - s) * (k - s)! * (n - s - (k - s))!) := by
      grind [choose_mul_factorial_mul_factorial]
    _ = n.choose s * (n - s).choose (k - s) * ((n - k)! * (k - s)! * s !) := by
      grind

Depends on / 依赖: Nat.mul_pos, Nat.mul_right_cancel, apply_rules, choose_mul_factorial_mul_factorial, factorial_pos, lt_or_ge, mul_pos, mul_right_cancel, n.choose
-/
theorem choose_mul {n k s : Nat} (hsk : s <= k) :
    n.choose k * k.choose s = n.choose s * (n - s).choose (k - s) := by
  obtain hnk | hkn := lt_or_ge n k
  · grind
  have h : 0 < (n - k)! * (k - s)! * s ! := by apply_rules [factorial_pos, Nat.mul_pos]
  apply Nat.mul_right_cancel h
  calc
    _ = n.choose s * s ! * ((n - s).choose (k - s) * (k - s)! * (n - s - (k - s))!) := by
      grind [choose_mul_factorial_mul_factorial]
    _ = n.choose s * (n - s).choose (k - s) * ((n - k)! * (k - s)! * s !) := by
      grind

/--
theorem `choose_eq_factorial_div_factorial` / 定理 `choose_eq_factorial_div_factorial`

English:
theorem choose_eq_factorial_div_factorial
  given: {n k : Nat} (hk : k <= n)
  proof: by
  rw [← choose_mul_factorial_mul_factorial hk]; rw [Nat.mul_assoc]
  exact (mul_div_left _ (Nat.mul_pos (factorial_pos _) (factorial_pos _))).symm

中文:
定理 choose_eq_factorial_div_factorial
  条件: {n k : 自然数} (hk : k <= n)
  证明: by
  rw [← choose_mul_factorial_mul_factorial hk]; rw [Nat.mul_assoc]
  exact (mul_div_left _ (Nat.mul_pos (factorial_pos _) (factorial_pos _))).symm

Depends on / 依赖: Nat.mul_assoc, Nat.mul_pos, choose_mul_factorial_mul_factorial, factorial_pos, mul_assoc, mul_div_left, mul_pos
-/
theorem choose_eq_factorial_div_factorial {n k : Nat} (hk : k <= n) :
    choose n k = n ! / (k ! * (n - k)!) := by
  rw [← choose_mul_factorial_mul_factorial hk]; rw [Nat.mul_assoc]
  exact (mul_div_left _ (Nat.mul_pos (factorial_pos _) (factorial_pos _))).symm

/--
theorem `add_choose` / 定理 `add_choose`

English:
theorem add_choose
  given: (i j : Nat)
  statement: (i + j).choose j = (i + j)! / (i ! * j !)
  proof: by
  rw [choose_eq_factorial_div_factorial (Nat.le_add_left j i)]; rw [Nat.add_sub_cancel_right]; rw [Nat.mul_comm]

中文:
定理 add_choose
  条件: (i j : 自然数)
  结论: (i + j).choose j = (i + j)! / (i ! * j !)
  证明: by
  rw [choose_eq_factorial_div_factorial (Nat.le_add_left j i)]; rw [Nat.add_sub_cancel_right]; rw [Nat.mul_comm]

Depends on / 依赖: Nat.add_sub_cancel_right, Nat.le_add_left, Nat.mul_comm, add_sub_cancel_right, choose_eq_factorial_div_factorial, le_add_left, mul_comm
-/
theorem add_choose (i j : Nat) : (i + j).choose j = (i + j)! / (i ! * j !) := by
  rw [choose_eq_factorial_div_factorial (Nat.le_add_left j i)]; rw [Nat.add_sub_cancel_right]; rw [Nat.mul_comm]

/--
theorem `add_choose_mul_factorial_mul_factorial` / 定理 `add_choose_mul_factorial_mul_factorial`

English:
theorem add_choose_mul_factorial_mul_factorial
  given: (i j : Nat)
  proof: by
  rw [← choose_mul_factorial_mul_factorial (Nat.le_add_left _ _)]; rw [Nat.add_sub_cancel_right]; rw [Nat.mul_right_comm]

中文:
定理 add_choose_mul_factorial_mul_factorial
  条件: (i j : 自然数)
  证明: by
  rw [← choose_mul_factorial_mul_factorial (Nat.le_add_left _ _)]; rw [Nat.add_sub_cancel_right]; rw [Nat.mul_right_comm]

Depends on / 依赖: Nat.add_sub_cancel_right, Nat.le_add_left, Nat.mul_right_comm, add_sub_cancel_right, choose_mul_factorial_mul_factorial, le_add_left, mul_right_comm
-/
theorem add_choose_mul_factorial_mul_factorial (i j : Nat) :
    (i + j).choose j * i ! * j ! = (i + j)! := by
  rw [← choose_mul_factorial_mul_factorial (Nat.le_add_left _ _)]; rw [Nat.add_sub_cancel_right]; rw [Nat.mul_right_comm]

/--
theorem `factorial_mul_factorial_dvd_factorial` / 定理 `factorial_mul_factorial_dvd_factorial`

English:
theorem factorial_mul_factorial_dvd_factorial
  given: {n k : Nat} (hk : k <= n)
  statement: k ! * (n - k)! ∣ n !
  proof: by
  rw [← choose_mul_factorial_mul_factorial hk]; rw [Nat.mul_assoc]; exact Nat.dvd_mul_left _ _

中文:
定理 factorial_mul_factorial_dvd_factorial
  条件: {n k : 自然数} (hk : k <= n)
  结论: k ! * (n - k)! ∣ n !
  证明: by
  rw [← choose_mul_factorial_mul_factorial hk]; rw [Nat.mul_assoc]; exact Nat.dvd_mul_left _ _

Depends on / 依赖: Nat.dvd_mul_left, Nat.mul_assoc, choose_mul_factorial_mul_factorial, dvd_mul_left, mul_assoc
-/
theorem factorial_mul_factorial_dvd_factorial {n k : Nat} (hk : k <= n) : k ! * (n - k)! ∣ n ! := by
  rw [← choose_mul_factorial_mul_factorial hk]; rw [Nat.mul_assoc]; exact Nat.dvd_mul_left _ _

/--
theorem `factorial_mul_factorial_dvd_factorial_add` / 定理 `factorial_mul_factorial_dvd_factorial_add`

English:
theorem factorial_mul_factorial_dvd_factorial_add
  given: (i j : Nat)
  statement: i ! * j ! ∣ (i + j)!
  proof: by
  suffices i ! * (i + j - i)! ∣ (i + j)! by
    rwa [Nat.add_sub_cancel_left i j] at this
  exact factorial_mul_factorial_dvd_factorial (Nat.le_add_right _ _)

@[simp]

中文:
定理 factorial_mul_factorial_dvd_factorial_add
  条件: (i j : 自然数)
  结论: i ! * j ! ∣ (i + j)!
  证明: by
  suffices i ! * (i + j - i)! ∣ (i + j)! by
    rwa [Nat.add_sub_cancel_left i j] at this
  exact factorial_mul_factorial_dvd_factorial (Nat.le_add_right _ _)

@[simp]

Depends on / 依赖: Nat.add_sub_cancel_left, Nat.le_add_right, add_sub_cancel_left, factorial_mul_factorial_dvd_factorial, le_add_right
-/
theorem factorial_mul_factorial_dvd_factorial_add (i j : Nat) : i ! * j ! ∣ (i + j)! := by
  suffices i ! * (i + j - i)! ∣ (i + j)! by
    rwa [Nat.add_sub_cancel_left i j] at this
  exact factorial_mul_factorial_dvd_factorial (Nat.le_add_right _ _)

@[simp]
/--
theorem `choose_symm` / 定理 `choose_symm`

English:
theorem choose_symm
  given: {n k : Nat} (hk : k <= n)
  statement: choose n (n - k) = choose n k
  proof: by
  rw [choose_eq_factorial_div_factorial hk]; rw [choose_eq_factorial_div_factorial (Nat.sub_le _ _)]; rw [Nat.sub_sub_self hk]; rw [Nat.mul_comm]

中文:
定理 choose_symm
  条件: {n k : 自然数} (hk : k <= n)
  结论: choose n (n - k) = choose n k
  证明: by
  rw [choose_eq_factorial_div_factorial hk]; rw [choose_eq_factorial_div_factorial (Nat.sub_le _ _)]; rw [Nat.sub_sub_self hk]; rw [Nat.mul_comm]

Depends on / 依赖: Nat.mul_comm, Nat.sub_le, Nat.sub_sub_self, choose_eq_factorial_div_factorial, mul_comm, sub_le, sub_sub_self
-/
theorem choose_symm {n k : Nat} (hk : k <= n) : choose n (n - k) = choose n k := by
  rw [choose_eq_factorial_div_factorial hk]; rw [choose_eq_factorial_div_factorial (Nat.sub_le _ _)]; rw [Nat.sub_sub_self hk]; rw [Nat.mul_comm]

/--
theorem `choose_symm_of_eq_add` / 定理 `choose_symm_of_eq_add`

English:
theorem choose_symm_of_eq_add
  given: {n a b : Nat} (h : n = a + b)
  statement: Nat.choose n a = Nat.choose n b
  proof: by
  suffices choose n (n - b) = choose n b by
    rw [h]; rw [Nat.add_sub_cancel_right] at this; rwa [h]
  exact choose_symm (h ▸ le_add_left _ _)

中文:
定理 choose_symm_of_eq_add
  条件: {n a b : 自然数} (h : n = a + b)
  结论: 自然数.choose n a = 自然数.choose n b
  证明: by
  suffices choose n (n - b) = choose n b by
    rw [h]; rw [Nat.add_sub_cancel_right] at this; rwa [h]
  exact choose_symm (h ▸ le_add_left _ _)

Depends on / 依赖: Nat.add_sub_cancel_right, add_sub_cancel_right, choose_symm, le_add_left
-/
theorem choose_symm_of_eq_add {n a b : Nat} (h : n = a + b) : Nat.choose n a = Nat.choose n b := by
  suffices choose n (n - b) = choose n b by
    rw [h]; rw [Nat.add_sub_cancel_right] at this; rwa [h]
  exact choose_symm (h ▸ le_add_left _ _)

/--
theorem `choose_symm_add` / 定理 `choose_symm_add`

English:
theorem choose_symm_add
  given: {a b : Nat}
  statement: choose (a + b) a = choose (a + b) b
  proof: choose_symm_of_eq_add rfl

中文:
定理 choose_symm_add
  条件: {a b : 自然数}
  结论: choose (a + b) a = choose (a + b) b
  证明: choose_symm_of_eq_add rfl

Depends on / 依赖: choose_symm_of_eq_add
-/
theorem choose_symm_add {a b : Nat} : choose (a + b) a = choose (a + b) b :=
  choose_symm_of_eq_add rfl

/--
theorem `choose_symm_half` / 定理 `choose_symm_half`

English:
theorem choose_symm_half
  given: (m : Nat)
  statement: choose (2 * m + 1) (m + 1) = choose (2 * m + 1) m
  proof: by
  apply choose_symm_of_eq_add
  rw [Nat.add_comm m 1]; rw [Nat.add_assoc 1 m m]; rw [Nat.add_comm (2 * m) 1]; rw [Nat.two_mul m]

中文:
定理 choose_symm_half
  条件: (m : 自然数)
  结论: choose (2 * m + 1) (m + 1) = choose (2 * m + 1) m
  证明: by
  apply choose_symm_of_eq_add
  rw [Nat.add_comm m 1]; rw [Nat.add_assoc 1 m m]; rw [Nat.add_comm (2 * m) 1]; rw [Nat.two_mul m]

Depends on / 依赖: Nat.add_assoc, Nat.add_comm, Nat.two_mul, add_assoc, add_comm, choose_symm_of_eq_add, two_mul
-/
theorem choose_symm_half (m : Nat) : choose (2 * m + 1) (m + 1) = choose (2 * m + 1) m := by
  apply choose_symm_of_eq_add
  rw [Nat.add_comm m 1]; rw [Nat.add_assoc 1 m m]; rw [Nat.add_comm (2 * m) 1]; rw [Nat.two_mul m]

/--
theorem `choose_succ_right_eq` / 定理 `choose_succ_right_eq`

English:
theorem choose_succ_right_eq
  given: (n k : Nat)
  statement: choose n (k + 1) * (k + 1) = choose n k * (n - k)
  proof: by
  have e : (n + 1) * choose n k = choose n (k + 1) * (k + 1) + choose n k * (k + 1) := by
    rw [← Nat.add_mul]; rw [Nat.add_comm (choose _ _)]; rw [← choose_succ_succ]; rw [add_one_mul_choose_eq]
  rw [← Nat.sub_eq_of_eq_add e]; rw [Nat.mul_comm]; rw [← Nat.mul_sub_left_distrib]; rw [Nat.add_sub_add_right]

@[simp, grind =]

中文:
定理 choose_succ_right_eq
  条件: (n k : 自然数)
  结论: choose n (k + 1) * (k + 1) = choose n k * (n - k)
  证明: by
  have e : (n + 1) * choose n k = choose n (k + 1) * (k + 1) + choose n k * (k + 1) := by
    rw [← Nat.add_mul]; rw [Nat.add_comm (choose _ _)]; rw [← choose_succ_succ]; rw [add_one_mul_choose_eq]
  rw [← Nat.sub_eq_of_eq_add e]; rw [Nat.mul_comm]; rw [← Nat.mul_sub_left_distrib]; rw [Nat.add_sub_add_right]

@[simp, grind =]

Depends on / 依赖: Nat.add_comm, Nat.add_mul, Nat.add_sub_add_right, Nat.mul_comm, Nat.mul_sub_left_distrib, Nat.sub_eq_of_eq_add, add_comm, add_mul, add_one_mul_choose_eq, add_sub_add_right, choose_succ_succ, mul_comm, mul_sub_left_distrib, sub_eq_of_eq_add
-/
theorem choose_succ_right_eq (n k : Nat) : choose n (k + 1) * (k + 1) = choose n k * (n - k) := by
  have e : (n + 1) * choose n k = choose n (k + 1) * (k + 1) + choose n k * (k + 1) := by
    rw [← Nat.add_mul]; rw [Nat.add_comm (choose _ _)]; rw [← choose_succ_succ]; rw [add_one_mul_choose_eq]
  rw [← Nat.sub_eq_of_eq_add e]; rw [Nat.mul_comm]; rw [← Nat.mul_sub_left_distrib]; rw [Nat.add_sub_add_right]

@[simp, grind =]
/--
theorem `choose_succ_self_right` / 定理 `choose_succ_self_right`

English:
theorem choose_succ_self_right
  statement: forall n : Nat, (n + 1).choose n = n + 1

中文:
定理 choose_succ_self_right
  结论: 对任意 n : 自然数, (n + 1).choose n = n + 1
-/
theorem choose_succ_self_right : forall n : Nat, (n + 1).choose n = n + 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_succ_self_right n, choose_self]

/--
theorem `choose_mul_succ_eq` / 定理 `choose_mul_succ_eq`

English:
theorem choose_mul_succ_eq
  given: (n k : Nat)
  statement: n.choose k * (n + 1) = (n + 1).choose k * (n + 1 - k)
  proof: by
  cases k with
  | zero => simp
  | succ k =>
    obtain hk | hk := le_or_gt (k + 1) (n + 1)
    · rw [choose_succ_succ, Nat.add_mul, succ_sub_succ, ← choose_succ_right_eq, ← succ_sub_succ,
        Nat.mul_sub_left_distrib, Nat.add_sub_cancel' (Nat.mul_le_mul_left _ hk)]
    · rw [choose_eq_zero_of_lt hk, choose_eq_zero_of_lt (n.lt_succ_self.trans hk), Nat.zero_mul,
        Nat.zero_mul]

中文:
定理 choose_mul_succ_eq
  条件: (n k : 自然数)
  结论: n.choose k * (n + 1) = (n + 1).choose k * (n + 1 - k)
  证明: by
  cases k with
  | zero => simp
  | succ k =>
    obtain hk | hk := le_or_gt (k + 1) (n + 1)
    · rw [choose_succ_succ, Nat.add_mul, succ_sub_succ, ← choose_succ_right_eq, ← succ_sub_succ,
        Nat.mul_sub_left_distrib, Nat.add_sub_cancel' (Nat.mul_le_mul_left _ hk)]
    · rw [choose_eq_zero_of_lt hk, choose_eq_zero_of_lt (n.lt_succ_self.trans hk), Nat.zero_mul,
        Nat.zero_mul]

Depends on / 依赖: Nat.add_mul, Nat.add_sub_cancel, Nat.mul_le_mul_left, Nat.mul_sub_left_distrib, Nat.zero_mul, add_mul, add_sub_cancel, choose_eq_zero_of_lt, choose_succ_right_eq, choose_succ_succ, le_or_gt, lt_succ_self, mul_le_mul_left, mul_sub_left_distrib, n.lt_succ_self.trans, succ_sub_succ, zero_mul
-/
theorem choose_mul_succ_eq (n k : Nat) : n.choose k * (n + 1) = (n + 1).choose k * (n + 1 - k) := by
  cases k with
  | zero => simp
  | succ k =>
    obtain hk | hk := le_or_gt (k + 1) (n + 1)
    · rw [choose_succ_succ, Nat.add_mul, succ_sub_succ, ← choose_succ_right_eq, ← succ_sub_succ,
        Nat.mul_sub_left_distrib, Nat.add_sub_cancel' (Nat.mul_le_mul_left _ hk)]
    · rw [choose_eq_zero_of_lt hk, choose_eq_zero_of_lt (n.lt_succ_self.trans hk), Nat.zero_mul,
        Nat.zero_mul]

/--
theorem `choose_mul_add` / 定理 `choose_mul_add`

English:
theorem choose_mul_add
  given: {m n : Nat} (hn : n != 0)
  proof: by
  rw [← Nat.mul_left_inj (Nat.mul_ne_zero (factorial_ne_zero (m * n)) (factorial_ne_zero n))]
  set p := n - 1
  have hp : n = p + 1 := (succ_pred_eq_of_ne_zero hn).symm
  simp only [hp, add_succ_sub_one]
  calc
    (m * (p + 1) + (p + 1)).choose (p + 1) * ((m * (p + 1))! * (p + 1)!)
      = (m * (p + 1) + (p + 1)).choose (p + 1) * (m * (p + 1))! * (p + 1)! := by lia
    _ = (m * (p + 1) + (p + 1))! := by rw [add_choose_mul_factorial_mul_factorial]
    _ = ((m * (p + 1) + p) + 1)! := by lia
    _ = ((m * (p + 1) + p) + 1) * (m * (p + 1) + p)! := by rw [factorial_succ]
    _ = (m * (p + 1) + p)! * ((p + 1) * (m + 1)) := by lia
    _ = ((m * (p + 1) + p).choose p * (m * (p + 1))! * (p)!) * ((p + 1) * (m + 1)) := by
      rw [add_choose_mul_factorial_mul_factorial]
    _ = (m * (p + 1) + p).choose p * (m * (p + 1))! * (((p + 1) * (p)!) * (m + 1)) := by lia
    _ = (m * (p + 1) + p).choose p * (m * (p + 1))! * ((p + 1)! * (m + 1)) := by rw [factorial_succ]
    _ = (m + 1) * (m * (p + 1) + p).choose p * ((m * (p + 1))! * (p + 1)!) := by lia

中文:
定理 choose_mul_add
  条件: {m n : 自然数} (hn : n != 0)
  证明: by
  rw [← Nat.mul_left_inj (Nat.mul_ne_zero (factorial_ne_zero (m * n)) (factorial_ne_zero n))]
  set p := n - 1
  have hp : n = p + 1 := (succ_pred_eq_of_ne_zero hn).symm
  simp only [hp, add_succ_sub_one]
  calc
    (m * (p + 1) + (p + 1)).choose (p + 1) * ((m * (p + 1))! * (p + 1)!)
      = (m * (p + 1) + (p + 1)).choose (p + 1) * (m * (p + 1))! * (p + 1)! := by lia
    _ = (m * (p + 1) + (p + 1))! := by rw [add_choose_mul_factorial_mul_factorial]
    _ = ((m * (p + 1) + p) + 1)! := by lia
    _ = ((m * (p + 1) + p) + 1) * (m * (p + 1) + p)! := by rw [factorial_succ]
    _ = (m * (p + 1) + p)! * ((p + 1) * (m + 1)) := by lia
    _ = ((m * (p + 1) + p).choose p * (m * (p + 1))! * (p)!) * ((p + 1) * (m + 1)) := by
      rw [add_choose_mul_factorial_mul_factorial]
    _ = (m * (p + 1) + p).choose p * (m * (p + 1))! * (((p + 1) * (p)!) * (m + 1)) := by lia
    _ = (m * (p + 1) + p).choose p * (m * (p + 1))! * ((p + 1)! * (m + 1)) := by rw [factorial_succ]
    _ = (m + 1) * (m * (p + 1) + p).choose p * ((m * (p + 1))! * (p + 1)!) := by lia

Depends on / 依赖: Nat.mul_left_inj, Nat.mul_ne_zero, add_choose_mul_factorial_mul_factorial, add_succ_sub_one, factorial_ne_zero, mul_left_inj, mul_ne_zero, succ_pred_eq_of_ne_zero
-/
theorem choose_mul_add {m n : Nat} (hn : n != 0) :
    (m * n + n).choose n = (m + 1) * (m * n + n - 1).choose (n - 1) := by
  rw [← Nat.mul_left_inj (Nat.mul_ne_zero (factorial_ne_zero (m * n)) (factorial_ne_zero n))]
  set p := n - 1
  have hp : n = p + 1 := (succ_pred_eq_of_ne_zero hn).symm
  simp only [hp, add_succ_sub_one]
  calc
    (m * (p + 1) + (p + 1)).choose (p + 1) * ((m * (p + 1))! * (p + 1)!)
      = (m * (p + 1) + (p + 1)).choose (p + 1) * (m * (p + 1))! * (p + 1)! := by lia
    _ = (m * (p + 1) + (p + 1))! := by rw [add_choose_mul_factorial_mul_factorial]
    _ = ((m * (p + 1) + p) + 1)! := by lia
    _ = ((m * (p + 1) + p) + 1) * (m * (p + 1) + p)! := by rw [factorial_succ]
    _ = (m * (p + 1) + p)! * ((p + 1) * (m + 1)) := by lia
    _ = ((m * (p + 1) + p).choose p * (m * (p + 1))! * (p)!) * ((p + 1) * (m + 1)) := by
      rw [add_choose_mul_factorial_mul_factorial]
    _ = (m * (p + 1) + p).choose p * (m * (p + 1))! * (((p + 1) * (p)!) * (m + 1)) := by lia
    _ = (m * (p + 1) + p).choose p * (m * (p + 1))! * ((p + 1)! * (m + 1)) := by rw [factorial_succ]
    _ = (m + 1) * (m * (p + 1) + p).choose p * ((m * (p + 1))! * (p + 1)!) := by lia

/--
theorem `choose_mul_right` / 定理 `choose_mul_right`

English:
theorem choose_mul_right
  given: {m n : Nat} (hn : n != 0)
  proof: by
  by_cases hm : m = 0
  · simp only [hm, Nat.zero_mul, Nat.choose_eq_zero_iff]
    exact Nat.pos_of_ne_zero hn
  · set p := m - 1; have hp : m = p + 1 := (succ_pred_eq_of_ne_zero hm).symm
    simp only [hp]
    rw [Nat.add_mul]; rw [Nat.one_mul]; rw [choose_mul_add hn]

中文:
定理 choose_mul_right
  条件: {m n : 自然数} (hn : n != 0)
  证明: by
  by_cases hm : m = 0
  · simp only [hm, Nat.zero_mul, Nat.choose_eq_zero_iff]
    exact Nat.pos_of_ne_zero hn
  · set p := m - 1; have hp : m = p + 1 := (succ_pred_eq_of_ne_zero hm).symm
    simp only [hp]
    rw [Nat.add_mul]; rw [Nat.one_mul]; rw [choose_mul_add hn]

Depends on / 依赖: Nat.add_mul, Nat.choose_eq_zero_iff, Nat.one_mul, Nat.pos_of_ne_zero, Nat.zero_mul, add_mul, choose_eq_zero_iff, choose_mul_add, one_mul, pos_of_ne_zero, succ_pred_eq_of_ne_zero, zero_mul
-/
theorem choose_mul_right {m n : Nat} (hn : n != 0) :
    (m * n).choose n = m * (m * n - 1).choose (n - 1) := by
  by_cases hm : m = 0
  · simp only [hm, Nat.zero_mul, Nat.choose_eq_zero_iff]
    exact Nat.pos_of_ne_zero hn
  · set p := m - 1; have hp : m = p + 1 := (succ_pred_eq_of_ne_zero hm).symm
    simp only [hp]
    rw [Nat.add_mul]; rw [Nat.one_mul]; rw [choose_mul_add hn]

/--
theorem `ascFactorial_eq_factorial_mul_choose` / 定理 `ascFactorial_eq_factorial_mul_choose`

English:
theorem ascFactorial_eq_factorial_mul_choose
  given: (n k : Nat)
  proof: by
  rw [Nat.mul_comm]
  apply Nat.mul_right_cancel (n + k - k).factorial_pos
  rw [choose_mul_factorial_mul_factorial <| Nat.le_add_left k n]; rw [Nat.add_sub_cancel_right]; rw [← factorial_mul_ascFactorial]; rw [Nat.mul_comm]

中文:
定理 ascFactorial_eq_factorial_mul_choose
  条件: (n k : 自然数)
  证明: by
  rw [Nat.mul_comm]
  apply Nat.mul_right_cancel (n + k - k).factorial_pos
  rw [choose_mul_factorial_mul_factorial <| Nat.le_add_left k n]; rw [Nat.add_sub_cancel_right]; rw [← factorial_mul_ascFactorial]; rw [Nat.mul_comm]

Depends on / 依赖: Nat.add_sub_cancel_right, Nat.le_add_left, Nat.mul_comm, Nat.mul_right_cancel, add_sub_cancel_right, choose_mul_factorial_mul_factorial, factorial_mul_ascFactorial, factorial_pos, le_add_left, mul_comm, mul_right_cancel
-/
theorem ascFactorial_eq_factorial_mul_choose (n k : Nat) :
    (n + 1).ascFactorial k = k ! * (n + k).choose k := by
  rw [Nat.mul_comm]
  apply Nat.mul_right_cancel (n + k - k).factorial_pos
  rw [choose_mul_factorial_mul_factorial <| Nat.le_add_left k n]; rw [Nat.add_sub_cancel_right]; rw [← factorial_mul_ascFactorial]; rw [Nat.mul_comm]

/--
theorem `ascFactorial_eq_factorial_mul_choose'` / 定理 `ascFactorial_eq_factorial_mul_choose'`

English:
theorem ascFactorial_eq_factorial_mul_choose'
  given: (n k : Nat)
  proof: by
  cases n
  · cases k
    · rw [ascFactorial_zero, choose_zero_right, factorial_zero, Nat.mul_one]
    · simp only [zero_ascFactorial, Nat.zero_add, succ_sub_succ_eq_sub,
        Nat.sub_zero, choose_succ_self, Nat.mul_zero]
  rw [ascFactorial_eq_factorial_mul_choose]
  simp only [succ_add_sub_one]

中文:
定理 ascFactorial_eq_factorial_mul_choose'
  条件: (n k : 自然数)
  证明: by
  cases n
  · cases k
    · rw [ascFactorial_zero, choose_zero_right, factorial_zero, Nat.mul_one]
    · simp only [zero_ascFactorial, Nat.zero_add, succ_sub_succ_eq_sub,
        Nat.sub_zero, choose_succ_self, Nat.mul_zero]
  rw [ascFactorial_eq_factorial_mul_choose]
  simp only [succ_add_sub_one]

Depends on / 依赖: Nat.mul_one, Nat.mul_zero, Nat.sub_zero, Nat.zero_add, ascFactorial_eq_factorial_mul_choose, ascFactorial_zero, choose_succ_self, choose_zero_right, factorial_zero, mul_one, mul_zero, sub_zero, succ_add_sub_one, succ_sub_succ_eq_sub, zero_add, zero_ascFactorial
-/
theorem ascFactorial_eq_factorial_mul_choose' (n k : Nat) :
    n.ascFactorial k = k ! * (n + k - 1).choose k := by
  cases n
  · cases k
    · rw [ascFactorial_zero, choose_zero_right, factorial_zero, Nat.mul_one]
    · simp only [zero_ascFactorial, Nat.zero_add, succ_sub_succ_eq_sub,
        Nat.sub_zero, choose_succ_self, Nat.mul_zero]
  rw [ascFactorial_eq_factorial_mul_choose]
  simp only [succ_add_sub_one]

/--
theorem `factorial_dvd_ascFactorial` / 定理 `factorial_dvd_ascFactorial`

English:
theorem factorial_dvd_ascFactorial
  given: (n k : Nat)
  statement: k ! ∣ n.ascFactorial k
  proof: ⟨(n + k - 1).choose k, ascFactorial_eq_factorial_mul_choose' _ _⟩

中文:
定理 factorial_dvd_ascFactorial
  条件: (n k : 自然数)
  结论: k ! ∣ n.ascFactorial k
  证明: ⟨(n + k - 1).choose k, ascFactorial_eq_factorial_mul_choose' _ _⟩

Depends on / 依赖: ascFactorial_eq_factorial_mul_choose
-/
theorem factorial_dvd_ascFactorial (n k : Nat) : k ! ∣ n.ascFactorial k :=
  ⟨(n + k - 1).choose k, ascFactorial_eq_factorial_mul_choose' _ _⟩

/--
theorem `choose_eq_asc_factorial_div_factorial` / 定理 `choose_eq_asc_factorial_div_factorial`

English:
theorem choose_eq_asc_factorial_div_factorial
  given: (n k : Nat)
  proof: by
  apply Nat.mul_left_cancel k.factorial_pos
  rw [← ascFactorial_eq_factorial_mul_choose]
  exact (Nat.mul_div_cancel' <| factorial_dvd_ascFactorial _ _).symm

中文:
定理 choose_eq_asc_factorial_div_factorial
  条件: (n k : 自然数)
  证明: by
  apply Nat.mul_left_cancel k.factorial_pos
  rw [← ascFactorial_eq_factorial_mul_choose]
  exact (Nat.mul_div_cancel' <| factorial_dvd_ascFactorial _ _).symm

Depends on / 依赖: Nat.mul_div_cancel, Nat.mul_left_cancel, ascFactorial_eq_factorial_mul_choose, factorial_dvd_ascFactorial, factorial_pos, k.factorial_pos, mul_div_cancel, mul_left_cancel
-/
theorem choose_eq_asc_factorial_div_factorial (n k : Nat) :
    (n + k).choose k = (n + 1).ascFactorial k / k ! := by
  apply Nat.mul_left_cancel k.factorial_pos
  rw [← ascFactorial_eq_factorial_mul_choose]
  exact (Nat.mul_div_cancel' <| factorial_dvd_ascFactorial _ _).symm

/--
theorem `choose_eq_asc_factorial_div_factorial'` / 定理 `choose_eq_asc_factorial_div_factorial'`

English:
theorem choose_eq_asc_factorial_div_factorial'
  given: (n k : Nat)
  proof: Nat.eq_div_of_mul_eq_right k.factorial_ne_zero (ascFactorial_eq_factorial_mul_choose' _ _).symm

中文:
定理 choose_eq_asc_factorial_div_factorial'
  条件: (n k : 自然数)
  证明: Nat.eq_div_of_mul_eq_right k.factorial_ne_zero (ascFactorial_eq_factorial_mul_choose' _ _).symm

Depends on / 依赖: Nat.eq_div_of_mul_eq_right, ascFactorial_eq_factorial_mul_choose, eq_div_of_mul_eq_right, factorial_ne_zero, k.factorial_ne_zero
-/
theorem choose_eq_asc_factorial_div_factorial' (n k : Nat) :
    (n + k - 1).choose k = n.ascFactorial k / k ! :=
  Nat.eq_div_of_mul_eq_right k.factorial_ne_zero (ascFactorial_eq_factorial_mul_choose' _ _).symm

/--
theorem `descFactorial_eq_factorial_mul_choose` / 定理 `descFactorial_eq_factorial_mul_choose`

English:
theorem descFactorial_eq_factorial_mul_choose
  given: (n k : Nat)
  statement: n.descFactorial k = k ! * n.choose k
  proof: by
  obtain h | h := Nat.lt_or_ge n k
  · rw [descFactorial_eq_zero_iff_lt.2 h, choose_eq_zero_of_lt h, Nat.mul_zero]
  rw [Nat.mul_comm]
  apply Nat.mul_right_cancel (n - k).factorial_pos
  rw [choose_mul_factorial_mul_factorial h]; rw [← factorial_mul_descFactorial h]; rw [Nat.mul_comm]

中文:
定理 descFactorial_eq_factorial_mul_choose
  条件: (n k : 自然数)
  结论: n.descFactorial k = k ! * n.choose k
  证明: by
  obtain h | h := Nat.lt_or_ge n k
  · rw [descFactorial_eq_zero_iff_lt.2 h, choose_eq_zero_of_lt h, Nat.mul_zero]
  rw [Nat.mul_comm]
  apply Nat.mul_right_cancel (n - k).factorial_pos
  rw [choose_mul_factorial_mul_factorial h]; rw [← factorial_mul_descFactorial h]; rw [Nat.mul_comm]

Depends on / 依赖: Nat.lt_or_ge, Nat.mul_comm, Nat.mul_right_cancel, Nat.mul_zero, choose_eq_zero_of_lt, choose_mul_factorial_mul_factorial, descFactorial_eq_zero_iff_lt, factorial_mul_descFactorial, factorial_pos, lt_or_ge, mul_comm, mul_right_cancel, mul_zero
-/
theorem descFactorial_eq_factorial_mul_choose (n k : Nat) : n.descFactorial k = k ! * n.choose k := by
  obtain h | h := Nat.lt_or_ge n k
  · rw [descFactorial_eq_zero_iff_lt.2 h, choose_eq_zero_of_lt h, Nat.mul_zero]
  rw [Nat.mul_comm]
  apply Nat.mul_right_cancel (n - k).factorial_pos
  rw [choose_mul_factorial_mul_factorial h]; rw [← factorial_mul_descFactorial h]; rw [Nat.mul_comm]

/--
theorem `factorial_dvd_descFactorial` / 定理 `factorial_dvd_descFactorial`

English:
theorem factorial_dvd_descFactorial
  given: (n k : Nat)
  statement: k ! ∣ n.descFactorial k
  proof: ⟨n.choose k, descFactorial_eq_factorial_mul_choose _ _⟩

中文:
定理 factorial_dvd_descFactorial
  条件: (n k : 自然数)
  结论: k ! ∣ n.descFactorial k
  证明: ⟨n.choose k, descFactorial_eq_factorial_mul_choose _ _⟩

Depends on / 依赖: descFactorial_eq_factorial_mul_choose, n.choose
-/
theorem factorial_dvd_descFactorial (n k : Nat) : k ! ∣ n.descFactorial k :=
  ⟨n.choose k, descFactorial_eq_factorial_mul_choose _ _⟩

/--
theorem `choose_eq_descFactorial_div_factorial` / 定理 `choose_eq_descFactorial_div_factorial`

English:
theorem choose_eq_descFactorial_div_factorial
  given: (n k : Nat)
  statement: n.choose k = n.descFactorial k / k !
  proof: Nat.eq_div_of_mul_eq_right k.factorial_ne_zero (descFactorial_eq_factorial_mul_choose _ _).symm

中文:
定理 choose_eq_descFactorial_div_factorial
  条件: (n k : 自然数)
  结论: n.choose k = n.descFactorial k / k !
  证明: Nat.eq_div_of_mul_eq_right k.factorial_ne_zero (descFactorial_eq_factorial_mul_choose _ _).symm

Depends on / 依赖: Nat.eq_div_of_mul_eq_right, descFactorial_eq_factorial_mul_choose, eq_div_of_mul_eq_right, factorial_ne_zero, k.factorial_ne_zero
-/
theorem choose_eq_descFactorial_div_factorial (n k : Nat) : n.choose k = n.descFactorial k / k ! :=
  Nat.eq_div_of_mul_eq_right k.factorial_ne_zero (descFactorial_eq_factorial_mul_choose _ _).symm

/--
Definition of `fast_choose` / `fast_choose` 的定义

English:
definition fast_choose
  signature: n k
  body: Nat.descFactorial n k / Nat.factorial k

中文:
定义 fast_choose
  签名: n k
  定义体: Nat.descFactorial n k / Nat.factorial k

Depends on / 依赖: Nat.descFactorial, Nat.factorial, descFactorial, factorial
-/
def fast_choose n k := Nat.descFactorial n k / Nat.factorial k

/--
lemma `choose_eq_fast_choose` / 引理 `choose_eq_fast_choose`

English:
lemma choose_eq_fast_choose
  statement: Nat.choose = fast_choose
  proof: funext (fun _ => funext (Nat.choose_eq_descFactorial_div_factorial _))

中文:
引理 choose_eq_fast_choose
  结论: 自然数.choose = fast_choose
  证明: funext (fun _ => funext (Nat.choose_eq_descFactorial_div_factorial _))
-/
@[csimp] lemma choose_eq_fast_choose : Nat.choose = fast_choose :=
  funext (fun _ => funext (Nat.choose_eq_descFactorial_div_factorial _))


/-! ### Inequalities -/


/--
theorem `choose_le_succ_of_lt_half_left` / 定理 `choose_le_succ_of_lt_half_left`

English:
theorem choose_le_succ_of_lt_half_left
  given: {r n : Nat} (h : r < n / 2)
  proof: by
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.sub_pos_of_lt (h.trans_le (n.div_le_self 2)))
  rw [← choose_succ_right_eq]
  apply Nat.mul_le_mul_left
  rw [← Nat.lt_iff_add_one_le]; rw [Nat.lt_sub_iff_add_lt]; rw [← Nat.mul_two]
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h Nat.zero_lt_two) (n.div_mul_le_self 2)

中文:
定理 choose_le_succ_of_lt_half_left
  条件: {r n : 自然数} (h : r < n / 2)
  证明: by
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.sub_pos_of_lt (h.trans_le (n.div_le_self 2)))
  rw [← choose_succ_right_eq]
  apply Nat.mul_le_mul_left
  rw [← Nat.lt_iff_add_one_le]; rw [Nat.lt_sub_iff_add_lt]; rw [← Nat.mul_two]
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h Nat.zero_lt_two) (n.div_mul_le_self 2)

Depends on / 依赖: Nat.le_of_mul_le_mul_right, Nat.lt_iff_add_one_le, Nat.lt_sub_iff_add_lt, Nat.mul_le_mul_left, Nat.mul_lt_mul_of_pos_right, Nat.mul_two, Nat.sub_pos_of_lt, Nat.zero_lt_two, choose_succ_right_eq, div_le_self, div_mul_le_self, h.trans_le, le_of_mul_le_mul_right, lt_iff_add_one_le, lt_of_lt_of_le, lt_sub_iff_add_lt, mul_le_mul_left, mul_lt_mul_of_pos_right, mul_two, n.div_le_self
-/
theorem choose_le_succ_of_lt_half_left {r n : Nat} (h : r < n / 2) :
    choose n r <= choose n (r + 1) := by
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.sub_pos_of_lt (h.trans_le (n.div_le_self 2)))
  rw [← choose_succ_right_eq]
  apply Nat.mul_le_mul_left
  rw [← Nat.lt_iff_add_one_le]; rw [Nat.lt_sub_iff_add_lt]; rw [← Nat.mul_two]
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h Nat.zero_lt_two) (n.div_mul_le_self 2)

/--
theorem `choose_le_middle_of_le_half_left` / 定理 `choose_le_middle_of_le_half_left`

English:
theorem choose_le_middle_of_le_half_left
  given: {n r : Nat} (hr : r <= n / 2)
  proof: by
  induction hr using decreasingInduction with
  | self => rfl
  | of_succ k hk ih => exact (choose_le_succ_of_lt_half_left hk).trans ih

中文:
定理 choose_le_middle_of_le_half_left
  条件: {n r : 自然数} (hr : r <= n / 2)
  证明: by
  induction hr using decreasingInduction with
  | self => rfl
  | of_succ k hk ih => exact (choose_le_succ_of_lt_half_left hk).trans ih
-/
private theorem choose_le_middle_of_le_half_left {n r : Nat} (hr : r <= n / 2) :
    choose n r <= choose n (n / 2) := by
  induction hr using decreasingInduction with
  | self => rfl
  | of_succ k hk ih => exact (choose_le_succ_of_lt_half_left hk).trans ih

/--
theorem `choose_le_middle` / 定理 `choose_le_middle`

English:
theorem choose_le_middle
  given: (r n : Nat)
  statement: choose n r <= choose n (n / 2)
  proof: by
  rcases le_or_gt r n with b | b
  · rcases le_or_gt r (n / 2) with a | h
    · apply choose_le_middle_of_le_half_left a
    · rw [← choose_symm b]
      apply choose_le_middle_of_le_half_left
      lia
  · rw [choose_eq_zero_of_lt b]
    apply zero_le

中文:
定理 choose_le_middle
  条件: (r n : 自然数)
  结论: choose n r <= choose n (n / 2)
  证明: by
  rcases le_or_gt r n with b | b
  · rcases le_or_gt r (n / 2) with a | h
    · apply choose_le_middle_of_le_half_left a
    · rw [← choose_symm b]
      apply choose_le_middle_of_le_half_left
      lia
  · rw [choose_eq_zero_of_lt b]
    apply zero_le

Depends on / 依赖: choose_eq_zero_of_lt, choose_le_middle_of_le_half_left, choose_symm, le_or_gt, zero_le
-/
theorem choose_le_middle (r n : Nat) : choose n r <= choose n (n / 2) := by
  rcases le_or_gt r n with b | b
  · rcases le_or_gt r (n / 2) with a | h
    · apply choose_le_middle_of_le_half_left a
    · rw [← choose_symm b]
      apply choose_le_middle_of_le_half_left
      lia
  · rw [choose_eq_zero_of_lt b]
    apply zero_le



/--
theorem `choose_le_succ` / 定理 `choose_le_succ`

English:
theorem choose_le_succ
  given: (a c : Nat)
  statement: choose a c <= choose a.succ c
  proof: by
  cases c <;> grind

中文:
定理 choose_le_succ
  条件: (a c : 自然数)
  结论: choose a c <= choose a.succ c
  证明: by
  cases c <;> grind
-/
theorem choose_le_succ (a c : Nat) : choose a c <= choose a.succ c := by
  cases c <;> grind

/--
theorem `choose_le_add` / 定理 `choose_le_add`

English:
theorem choose_le_add
  given: (a b c : Nat)
  statement: choose a c <= choose (a + b) c
  proof: by
  induction b with
  | zero => simp
  | succ b_n b_ih => exact b_ih.trans (choose_le_succ (a + b_n) c)

@[gcongr]

中文:
定理 choose_le_add
  条件: (a b c : 自然数)
  结论: choose a c <= choose (a + b) c
  证明: by
  induction b with
  | zero => simp
  | succ b_n b_ih => exact b_ih.trans (choose_le_succ (a + b_n) c)

@[gcongr]

Depends on / 依赖: b_ih, b_ih.trans, choose_le_succ
-/
theorem choose_le_add (a b c : Nat) : choose a c <= choose (a + b) c := by
  induction b with
  | zero => simp
  | succ b_n b_ih => exact b_ih.trans (choose_le_succ (a + b_n) c)

@[gcongr]
/--
theorem `choose_le_choose` / 定理 `choose_le_choose`

English:
theorem choose_le_choose
  given: {a b : Nat} (c : Nat) (h : a <= b)
  statement: choose a c <= choose b c
  proof: Nat.add_sub_cancel' h ▸ choose_le_add a (b - a) c

中文:
定理 choose_le_choose
  条件: {a b : 自然数} (c : 自然数) (h : a <= b)
  结论: choose a c <= choose b c
  证明: Nat.add_sub_cancel' h ▸ choose_le_add a (b - a) c

Depends on / 依赖: Nat.add_sub_cancel, add_sub_cancel, choose_le_add
-/
theorem choose_le_choose {a b : Nat} (c : Nat) (h : a <= b) : choose a c <= choose b c :=
  Nat.add_sub_cancel' h ▸ choose_le_add a (b - a) c

/--
theorem `choose_mono` / 定理 `choose_mono`

English:
theorem choose_mono
  given: (b : Nat)
  statement: Monotone fun a => choose a b
  proof: fun _ _ => choose_le_choose b

中文:
定理 choose_mono
  条件: (b : 自然数)
  结论: 递增 fun a => choose a b
  证明: fun _ _ => choose_le_choose b

Depends on / 依赖: choose_le_choose
-/
theorem choose_mono (b : Nat) : Monotone fun a => choose a b := fun _ _ => choose_le_choose b

/--
theorem `choose_eq_one_iff` / 定理 `choose_eq_one_iff`

English:
theorem choose_eq_one_iff
  given: {n k : Nat}
  statement: n.choose k = 1 ↔ k = 0 ∨ n = k
  proof: by
  rcases lt_trichotomy k n with hk | rfl | hk
  · grind [k.choose_mono hk]
  · simp
  · grind

中文:
定理 choose_eq_one_iff
  条件: {n k : 自然数}
  结论: n.choose k = 1 ↔ k = 0 ∨ n = k
  证明: by
  rcases lt_trichotomy k n with hk | rfl | hk
  · grind [k.choose_mono hk]
  · simp
  · grind

Depends on / 依赖: choose_mono, k.choose_mono, lt_trichotomy
-/
theorem choose_eq_one_iff {n k : Nat} : n.choose k = 1 ↔ k = 0 ∨ n = k := by
  rcases lt_trichotomy k n with hk | rfl | hk
  · grind [k.choose_mono hk]
  · simp
  · grind

/-! #### Multichoose

Whereas `choose n k` is the number of subsets of cardinality `k` from a type of cardinality `n`,
`multichoose n k` is the number of multisets of cardinality `k` from a type of cardinality `n`.

Alternatively, whereas `choose n k` counts the number of combinations,
i.e. ways to select `k` items (up to permutation) from `n` items without replacement,
`multichoose n k` counts the number of multicombinations,
i.e. ways to select `k` items (up to permutation) from `n` items with replacement.

Note that `multichoose` is *not* the multinomial coefficient, although it can be computed
in terms of multinomial coefficients. For details see https://mathworld.wolfram.com/Multichoose.html

-/

/--
Definition of `multichoose` / `multichoose` 的定义

English:
definition multichoose
  signature: : Nat -> Nat -> Nat

中文:
定义 multichoose
  签名: : 自然数 -> 自然数 -> 自然数
-/
def multichoose : Nat -> Nat -> Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 =>
    multichoose n (k + 1) + multichoose (n + 1) k

@[simp]
/--
theorem `multichoose_zero_right` / 定理 `multichoose_zero_right`

English:
theorem multichoose_zero_right
  given: (n : Nat)
  statement: multichoose n 0 = 1
  proof: by cases n <;> simp [multichoose]

@[simp]

中文:
定理 multichoose_zero_right
  条件: (n : 自然数)
  结论: multichoose n 0 = 1
  证明: by cases n <;> simp [multichoose]

@[simp]

Depends on / 依赖: multichoose
-/
theorem multichoose_zero_right (n : Nat) : multichoose n 0 = 1 := by cases n <;> simp [multichoose]

@[simp]
/--
theorem `multichoose_zero_succ` / 定理 `multichoose_zero_succ`

English:
theorem multichoose_zero_succ
  given: (k : Nat)
  statement: multichoose 0 (k + 1) = 0
  proof: by simp [multichoose]

中文:
定理 multichoose_zero_succ
  条件: (k : 自然数)
  结论: multichoose 0 (k + 1) = 0
  证明: by simp [multichoose]

Depends on / 依赖: multichoose
-/
theorem multichoose_zero_succ (k : Nat) : multichoose 0 (k + 1) = 0 := by simp [multichoose]

/--
theorem `multichoose_succ_succ` / 定理 `multichoose_succ_succ`

English:
theorem multichoose_succ_succ
  given: (n k : Nat)
  proof: by
  simp [multichoose]

@[simp]

中文:
定理 multichoose_succ_succ
  条件: (n k : 自然数)
  证明: by
  simp [multichoose]

@[simp]

Depends on / 依赖: multichoose
-/
theorem multichoose_succ_succ (n k : Nat) :
    multichoose (n + 1) (k + 1) = multichoose n (k + 1) + multichoose (n + 1) k := by
  simp [multichoose]

@[simp]
/--
theorem `multichoose_one` / 定理 `multichoose_one`

English:
theorem multichoose_one
  given: (k : Nat)
  statement: multichoose 1 k = 1
  proof: by
  induction k with
  | zero => simp
  | succ k IH => simp [multichoose_succ_succ 0 k, IH]

@[simp]

中文:
定理 multichoose_one
  条件: (k : 自然数)
  结论: multichoose 1 k = 1
  证明: by
  induction k with
  | zero => simp
  | succ k IH => simp [multichoose_succ_succ 0 k, IH]

@[simp]

Depends on / 依赖: multichoose_succ_succ
-/
theorem multichoose_one (k : Nat) : multichoose 1 k = 1 := by
  induction k with
  | zero => simp
  | succ k IH => simp [multichoose_succ_succ 0 k, IH]

@[simp]
/--
theorem `multichoose_two` / 定理 `multichoose_two`

English:
theorem multichoose_two
  given: (k : Nat)
  statement: multichoose 2 k = k + 1
  proof: by
  induction k with
  | zero => simp
  | succ k IH => rw [multichoose, IH]; simp [Nat.add_comm]

@[simp]

中文:
定理 multichoose_two
  条件: (k : 自然数)
  结论: multichoose 2 k = k + 1
  证明: by
  induction k with
  | zero => simp
  | succ k IH => rw [multichoose, IH]; simp [Nat.add_comm]

@[simp]

Depends on / 依赖: Nat.add_comm, add_comm, multichoose
-/
theorem multichoose_two (k : Nat) : multichoose 2 k = k + 1 := by
  induction k with
  | zero => simp
  | succ k IH => rw [multichoose, IH]; simp [Nat.add_comm]

@[simp]
/--
theorem `multichoose_one_right` / 定理 `multichoose_one_right`

English:
theorem multichoose_one_right
  given: (n : Nat)
  statement: multichoose n 1 = n
  proof: by
  induction n with
  | zero => simp
  | succ n IH => simp [multichoose_succ_succ n 0, IH]

中文:
定理 multichoose_one_right
  条件: (n : 自然数)
  结论: multichoose n 1 = n
  证明: by
  induction n with
  | zero => simp
  | succ n IH => simp [multichoose_succ_succ n 0, IH]

Depends on / 依赖: multichoose_succ_succ
-/
theorem multichoose_one_right (n : Nat) : multichoose n 1 = n := by
  induction n with
  | zero => simp
  | succ n IH => simp [multichoose_succ_succ n 0, IH]

/--
theorem `multichoose_eq` / 定理 `multichoose_eq`

English:
theorem multichoose_eq
  statement: forall n k : Nat, multichoose n k = (n + k - 1).choose k
  proof: Nat.add_lt_add_right (Nat.lt_succ_self _) _
    have : (n + 1) + k < (n + 1) + (k + 1) := Nat.add_lt_add_left (Nat.lt_succ_self _) _
    rw [multichoose_succ_succ]; rw [Nat.add_comm]; rw [Nat.succ_add_sub_one]; rw [← Nat.add_assoc]; rw [Nat.choose_succ_succ]
    simp [multichoose_eq n (k + 1), multichoose_eq (n + 1) k]

中文:
定理 multichoose_eq
  结论: 对任意 n k : 自然数, multichoose n k = (n + k - 1).choose k
  证明: Nat.add_lt_add_right (Nat.lt_succ_self _) _
    have : (n + 1) + k < (n + 1) + (k + 1) := Nat.add_lt_add_left (Nat.lt_succ_self _) _
    rw [multichoose_succ_succ]; rw [Nat.add_comm]; rw [Nat.succ_add_sub_one]; rw [← Nat.add_assoc]; rw [Nat.choose_succ_succ]
    simp [multichoose_eq n (k + 1), multichoose_eq (n + 1) k]

Depends on / 依赖: Nat.add_lt_add_right, Nat.lt_succ_self, add_lt_add_right, lt_succ_self
-/
theorem multichoose_eq : forall n k : Nat, multichoose n k = (n + k - 1).choose k
  | _, 0 => by simp
  | 0, k + 1 => by simp
  | n + 1, k + 1 => by
    have : n + (k + 1) < (n + 1) + (k + 1) := Nat.add_lt_add_right (Nat.lt_succ_self _) _
    have : (n + 1) + k < (n + 1) + (k + 1) := Nat.add_lt_add_left (Nat.lt_succ_self _) _
    rw [multichoose_succ_succ]; rw [Nat.add_comm]; rw [Nat.succ_add_sub_one]; rw [← Nat.add_assoc]; rw [Nat.choose_succ_succ]
    simp [multichoose_eq n (k + 1), multichoose_eq (n + 1) k]

end Nat
