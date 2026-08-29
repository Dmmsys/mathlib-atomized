/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Bound.Attribute

/-!
# Basic lemmas about ordered rings
-/

@[expose] public section

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton

open Function Int

variable {α M R : Type*}

/--
theorem `IsSquare.nonneg` / 定理 `IsSquare.nonneg`

English:
theorem IsSquare.nonneg
  statement: [Semiring R] [LinearOrder R]
  proof: by
  rcases h with ⟨y, rfl⟩
  exact mul_self_nonneg y

@[simp]

中文:
定理 IsSquare.nonneg
  结论: [半环 R] [线性序 R]
  证明: by
  rcases h with ⟨y, rfl⟩
  exact mul_self_nonneg y

@[simp]

Depends on / 依赖: mul_self_nonneg
-/
theorem IsSquare.nonneg [Semiring R] [LinearOrder R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    {x : R} (h : IsSquare x) : 0 <= x := by
  rcases h with ⟨y, rfl⟩
  exact mul_self_nonneg y

@[simp]
/--
lemma `not_isSquare_of_neg` / 引理 `not_isSquare_of_neg`

English:
lemma not_isSquare_of_neg
  statement: [Semiring R] [LinearOrder R]
  proof: (h.not_ge ·.nonneg)

中文:
引理 not_isSquare_of_neg
  结论: [半环 R] [线性序 R]
  证明: (h.not_ge ·.nonneg)

Depends on / 依赖: h.not_ge, nonneg, not_ge
-/
lemma not_isSquare_of_neg [Semiring R] [LinearOrder R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    {x : R} (h : x < 0) : ¬ IsSquare x :=
  (h.not_ge ·.nonneg)

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {a b x y : R} {n : Nat}

/--
theorem `pow_add_pow_le` / 定理 `pow_add_pow_le`

English:
theorem pow_add_pow_le
  given: (hx : 0 <= x) (hy : 0 <= y) (hn : n != 0)
  statement: x ^ n + y ^ n <= (x + y) ^ n
  proof: by
  rcases Nat.exists_eq_add_one_of_ne_zero hn with ⟨k, rfl⟩
  induction k with
  | zero => simp only [zero_add, pow_one, le_refl]
  | succ k ih =>
    let n := k.succ
    have h1 := add_nonneg (mul_nonneg hx (pow_nonneg hy n)) (mul_nonneg hy (pow_nonneg hx n))
    have h2 := add_nonneg hx hy
    c

中文:
定理 pow_add_pow_le
  条件: (hx : 0 <= x) (hy : 0 <= y) (hn : n != 0)
  结论: x ^ n + y ^ n <= (x + y) ^ n
  证明: by
  rcases Nat.exists_eq_add_one_of_ne_zero hn with ⟨k, rfl⟩
  induction k with
  | zero => simp only [zero_add, pow_one, le_refl]
  | succ k ih =>
    let n := k.succ
    have h1 := add_nonneg (mul_nonneg hx (pow_nonneg hy n)) (mul_nonneg hy (pow_nonneg hx n))
    have h2 := add_nonneg hx hy
    c

Depends on / 依赖: Nat.exists_eq_add_one_of_ne_zero, add_mul, add_nonneg, exists_eq_add_one_of_ne_zero, k.succ, le_add_of_nonneg_right, le_refl, mul_add, mul_nonneg, pow_nonneg, pow_one, pow_succ, zero_add
-/
theorem pow_add_pow_le (hx : 0 <= x) (hy : 0 <= y) (hn : n != 0) : x ^ n + y ^ n <= (x + y) ^ n := by
  rcases Nat.exists_eq_add_one_of_ne_zero hn with ⟨k, rfl⟩
  induction k with
  | zero => simp only [zero_add, pow_one, le_refl]
  | succ k ih =>
    let n := k.succ
    have h1 := add_nonneg (mul_nonneg hx (pow_nonneg hy n)) (mul_nonneg hy (pow_nonneg hx n))
    have h2 := add_nonneg hx hy
    calc
      x ^ (n + 1) + y ^ (n + 1) <= x * x ^ n + y * y ^ n + (x * y ^ n + y * x ^ n) := by
        rw [pow_succ' _ n]; rw [pow_succ' _ n]
        exact le_add_of_nonneg_right h1
      _ = (x + y) * (x ^ n + y ^ n) := by
        rw [add_mul]; rw [mul_add]; rw [mul_add]; rw [add_comm (y * x ^ n)]; rw [← add_assoc]; rw [← add_assoc]; rw [add_assoc (x * x ^ n) (x * y ^ n)]; rw [add_comm (x * y ^ n) (y * y ^ n)]; rw [← add_assoc]
      _ <= (x + y) ^ (n + 1) := by
        rw [pow_succ' _ n]
        gcongr; exact ih (Nat.succ_ne_zero k)

attribute [bound] pow_le_one₀ one_le_pow₀

/--
lemma `pow_add_pow_le'` / 引理 `pow_add_pow_le'`

English:
lemma pow_add_pow_le'
  given: (ha : 0 <= a) (hb : 0 <= b)
  statement: a ^ n + b ^ n <= 2 * (a + b) ^ n
  proof: by
  rw [two_mul]
  gcongr <;> try assumption
  exacts [le_add_of_nonneg_right hb, le_add_of_nonneg_left ha]

中文:
引理 pow_add_pow_le'
  条件: (ha : 0 <= a) (hb : 0 <= b)
  结论: a ^ n + b ^ n <= 2 * (a + b) ^ n
  证明: by
  rw [two_mul]
  gcongr <;> try assumption
  exacts [le_add_of_nonneg_right hb, le_add_of_nonneg_left ha]

Depends on / 依赖: exacts, le_add_of_nonneg_left, le_add_of_nonneg_right, two_mul
-/
lemma pow_add_pow_le' (ha : 0 <= a) (hb : 0 <= b) : a ^ n + b ^ n <= 2 * (a + b) ^ n := by
  rw [two_mul]
  gcongr <;> try assumption
  exacts [le_add_of_nonneg_right hb, le_add_of_nonneg_left ha]

end OrderedSemiring

section StrictOrderedRing
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] {a : R}

/--
lemma `sq_pos_of_neg` / 引理 `sq_pos_of_neg`

English:
lemma sq_pos_of_neg
  given: (ha : a < 0)
  statement: 0 < a ^ 2
  proof: by rw [sq]; exact mul_pos_of_neg_of_neg ha ha

中文:
引理 sq_pos_of_neg
  条件: (ha : a < 0)
  结论: 0 < a ^ 2
  证明: by rw [sq]; exact mul_pos_of_neg_of_neg ha ha

Depends on / 依赖: mul_pos_of_neg_of_neg
-/
lemma sq_pos_of_neg (ha : a < 0) : 0 < a ^ 2 := by rw [sq]; exact mul_pos_of_neg_of_neg ha ha

end StrictOrderedRing

section LinearOrderedSemiring

section IsOrderedRing

variable [Semiring R] [LinearOrder R] [IsOrderedRing R] [ExistsAddOfLE R] {m n : Nat}

/--
lemma `Even.pow_nonneg` / 引理 `Even.pow_nonneg`

English:
lemma Even.pow_nonneg
  given: (hn : Even n) (a : R)
  statement: 0 <= a ^ n
  proof: by
  obtain ⟨k, rfl⟩ := hn; rw [pow_add]; exact mul_self_nonneg _

中文:
引理 Even.pow_nonneg
  条件: (hn : Even n) (a : R)
  结论: 0 <= a ^ n
  证明: by
  obtain ⟨k, rfl⟩ := hn; rw [pow_add]; exact mul_self_nonneg _
-/
protected lemma Even.pow_nonneg (hn : Even n) (a : R) : 0 <= a ^ n := by
  obtain ⟨k, rfl⟩ := hn; rw [pow_add]; exact mul_self_nonneg _

/--
lemma `pow_four_le_pow_two_of_pow_two_le` / 引理 `pow_four_le_pow_two_of_pow_two_le`

English:
lemma pow_four_le_pow_two_of_pow_two_le
  given: {a b : R} (h : a ^ 2 <= b)
  statement: a ^ 4 <= b ^ 2
  proof: (pow_mul a 2 2).symm ▸ pow_le_pow_left₀ (sq_nonneg a) h 2

中文:
引理 pow_four_le_pow_two_of_pow_two_le
  条件: {a b : R} (h : a ^ 2 <= b)
  结论: a ^ 4 <= b ^ 2
  证明: (pow_mul a 2 2).symm ▸ pow_le_pow_left₀ (sq_nonneg a) h 2

Depends on / 依赖: pow_mul, sq_nonneg
-/
lemma pow_four_le_pow_two_of_pow_two_le {a b : R} (h : a ^ 2 <= b) : a ^ 4 <= b ^ 2 :=
  (pow_mul a 2 2).symm ▸ pow_le_pow_left₀ (sq_nonneg a) h 2

end IsOrderedRing

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a b : R} {m n : Nat}

/--
Definition of `IsNonarchimedean` / `IsNonarchimedean` 的定义

English:
definition IsNonarchimedean
  signature: {α : Type*} [Add α] (f : α -> R)
  body: forall a b : α, f (a + b) <= f a ⊔ f b

中文:
定义 IsNonarchimedean
  签名: {α : 类型} [加法 α] (f : α -> R)
  定义体: forall a b : α, f (a + b) <= f a ⊔ f b
-/
def IsNonarchimedean {α : Type*} [Add α] (f : α -> R) : Prop := forall a b : α, f (a + b) <= f a ⊔ f b

/-!
### Lemmas for canonically linear ordered semirings or linear ordered rings

The slightly unusual typeclass assumptions `[IsStrictOrderedRing R] [ExistsAddOfLE R]` cover two
more familiar settings:
* linearly ordered rings, e.g. `ℤ`, `ℚ` or `ℝ`
* canonically ordered semirings, e.g. `ℕ`, `ℚ≥0` or `ℝ≥0`
-/

variable [ExistsAddOfLE R]

/--
lemma `add_sq_le` / 引理 `add_sq_le`

English:
lemma add_sq_le
  statement: (a + b) ^ 2 <= 2 * (a ^ 2 + b ^ 2)
  proof: by
  calc
    (a + b) ^ 2 = a ^ 2 + b ^ 2 + (a * b + b * a) := by
        simp_rw [pow_succ', pow_zero, mul_one, add_mul, mul_add, add_comm (b * a), add_add_add_comm]
    _ <= a ^ 2 + b ^ 2 + (a * a + b * b) := add_le_add_right ?_ _
    _ = _ := by simp_rw [pow_succ', pow_zero, mul_one, two_mul]
  c

中文:
引理 add_sq_le
  结论: (a + b) ^ 2 <= 2 * (a ^ 2 + b ^ 2)
  证明: by
  calc
    (a + b) ^ 2 = a ^ 2 + b ^ 2 + (a * b + b * a) := by
        simp_rw [pow_succ', pow_zero, mul_one, add_mul, mul_add, add_comm (b * a), add_add_add_comm]
    _ <= a ^ 2 + b ^ 2 + (a * a + b * b) := add_le_add_right ?_ _
    _ = _ := by simp_rw [pow_succ', pow_zero, mul_one, two_mul]
  c

Depends on / 依赖: add_add_add_comm, add_comm, add_le_add_right, add_mul, le_total, mul_add, mul_add_mul_le_mul_add_mul, mul_one, pow_succ, pow_zero, simp_rw, two_mul
-/
lemma add_sq_le : (a + b) ^ 2 <= 2 * (a ^ 2 + b ^ 2) := by
  calc
    (a + b) ^ 2 = a ^ 2 + b ^ 2 + (a * b + b * a) := by
        simp_rw [pow_succ', pow_zero, mul_one, add_mul, mul_add, add_comm (b * a), add_add_add_comm]
    _ <= a ^ 2 + b ^ 2 + (a * a + b * b) := add_le_add_right ?_ _
    _ = _ := by simp_rw [pow_succ', pow_zero, mul_one, two_mul]
  cases le_total a b
  · exact mul_add_mul_le_mul_add_mul ‹_› ‹_›
  · exact mul_add_mul_le_mul_add_mul' ‹_› ‹_›

-- TODO: Use `gcongr`, `positivity`, `ring` once those tactics are made available here
/--
lemma `add_pow_le` / 引理 `add_pow_le`

English:
lemma add_pow_le
  given: (ha : 0 <= a) (hb : 0 <= b)
  statement: forall n, (a + b) ^ n <= 2 ^ (n - 1) * (a ^ n + b ^ n)
  proof: mul_le_mul_of_nonneg_right (add_pow_le ha hb (n + 1)) add_nonneg ha hb
      _ = 2 ^ n * (a ^ (n + 2) + b ^ (n + 2) + (a ^ (n + 1) * b + b ^ (n + 1) * a)) := by
          rw [mul_assoc]; rw [mul_add]; rw [add_mul]; rw [add_mul]; rw [← pow_succ]; rw [← pow_succ]; rw [add_comm _ (b ^ _)]; rw [add_add_

中文:
引理 add_pow_le
  条件: (ha : 0 <= a) (hb : 0 <= b)
  结论: 对任意 n, (a + b) ^ n <= 2 ^ (n - 1) * (a ^ n + b ^ n)
  证明: mul_le_mul_of_nonneg_right (add_pow_le ha hb (n + 1)) add_nonneg ha hb
      _ = 2 ^ n * (a ^ (n + 2) + b ^ (n + 2) + (a ^ (n + 1) * b + b ^ (n + 1) * a)) := by
          rw [mul_assoc]; rw [mul_add]; rw [add_mul]; rw [add_mul]; rw [← pow_succ]; rw [← pow_succ]; rw [add_comm _ (b ^ _)]; rw [add_add_

Depends on / 依赖: add_add_add_comm, add_comm, add_mul, add_nonneg, add_pow_le, le_total, mul_add, mul_assoc, mul_le_mul_of_nonneg_right, pow_nonneg, pow_succ, zero_le_two
-/
lemma add_pow_le (ha : 0 <= a) (hb : 0 <= b) : forall n, (a + b) ^ n <= 2 ^ (n - 1) * (a ^ n + b ^ n)
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [pow_succ]
    calc
      _ <= 2 ^ n * (a ^ (n + 1) + b ^ (n + 1)) * (a + b) :=
mul_le_mul_of_nonneg_right (add_pow_le ha hb (n + 1)) add_nonneg ha hb
      _ = 2 ^ n * (a ^ (n + 2) + b ^ (n + 2) + (a ^ (n + 1) * b + b ^ (n + 1) * a)) := by
          rw [mul_assoc]; rw [mul_add]; rw [add_mul]; rw [add_mul]; rw [← pow_succ]; rw [← pow_succ]; rw [add_comm _ (b ^ _)]; rw [add_add_add_comm]; rw [add_comm (_ * a)]
      _ <= 2 ^ n * (a ^ (n + 2) + b ^ (n + 2) + (a ^ (n + 1) * a + b ^ (n + 1) * b)) := by
        gcongr _ * (_ + _ + ?_)
        · exact pow_nonneg zero_le_two _
        obtain hab | hba := le_total a b
        · exact mul_add_mul_le_mul_add_mul (by gcongr) hab
        · exact mul_add_mul_le_mul_add_mul' (by gcongr) hba
      _ = _ := by simp only [← pow_succ, ← two_mul, ← mul_assoc]; rfl

/--
lemma `Even.add_pow_le` / 引理 `Even.add_pow_le`

English:
lemma Even.add_pow_le
  given: (hn : Even n)
  proof: by
  obtain ⟨n, rfl⟩ := hn
  rw [← two_mul]; rw [pow_mul]
  calc
    _ <= (2 * (a ^ 2 + b ^ 2)) ^ n := pow_le_pow_left₀ (sq_nonneg _) add_sq_le _
    _ = 2 ^ n * (a ^ 2 + b ^ 2) ^ n := by -- TODO: Should be `Nat.cast_commute`
        rw [Commute.mul_pow]; simp [Commute, SemiconjBy, two_mul, mul_two]

中文:
引理 Even.add_pow_le
  条件: (hn : Even n)
  证明: by
  obtain ⟨n, rfl⟩ := hn
  rw [← two_mul]; rw [pow_mul]
  calc
    _ <= (2 * (a ^ 2 + b ^ 2)) ^ n := pow_le_pow_left₀ (sq_nonneg _) add_sq_le _
    _ = 2 ^ n * (a ^ 2 + b ^ 2) ^ n := by -- TODO: Should be `Nat.cast_commute`
        rw [Commute.mul_pow]; simp [Commute, SemiconjBy, two_mul, mul_two]
-/
protected lemma Even.add_pow_le (hn : Even n) :
    (a + b) ^ n <= 2 ^ (n - 1) * (a ^ n + b ^ n) := by
  obtain ⟨n, rfl⟩ := hn
  rw [← two_mul]; rw [pow_mul]
  calc
    _ <= (2 * (a ^ 2 + b ^ 2)) ^ n := pow_le_pow_left₀ (sq_nonneg _) add_sq_le _
    _ = 2 ^ n * (a ^ 2 + b ^ 2) ^ n := by -- TODO: Should be `Nat.cast_commute`
        rw [Commute.mul_pow]; simp [Commute, SemiconjBy, two_mul, mul_two]
    _ <= 2 ^ n * (2 ^ (n - 1) * ((a ^ 2) ^ n + (b ^ 2) ^ n)) := mul_le_mul_of_nonneg_left
(add_pow_le (sq_nonneg _) (sq_nonneg _) _) pow_nonneg (zero_le_two (α := R)) _
    _ = _ := by
      simp only [← mul_assoc, ← pow_add, ← pow_mul]
      cases n
      · rfl
      · simp [Nat.two_mul]

/--
lemma `Even.pow_pos` / 引理 `Even.pow_pos`

English:
lemma Even.pow_pos
  given: (hn : Even n) (ha : a != 0)
  statement: 0 < a ^ n
  proof: (hn.pow_nonneg _).lt_of_ne' (pow_ne_zero _ ha)

中文:
引理 Even.pow_pos
  条件: (hn : Even n) (ha : a != 0)
  结论: 0 < a ^ n
  证明: (hn.pow_nonneg _).lt_of_ne' (pow_ne_zero _ ha)

Depends on / 依赖: hn.pow_nonneg, lt_of_ne, pow_ne_zero, pow_nonneg
-/
lemma Even.pow_pos (hn : Even n) (ha : a != 0) : 0 < a ^ n :=
  (hn.pow_nonneg _).lt_of_ne' (pow_ne_zero _ ha)

/--
lemma `Even.pow_pos_iff` / 引理 `Even.pow_pos_iff`

English:
lemma Even.pow_pos_iff
  given: (hn : Even n) (h₀ : n != 0)
  statement: 0 < a ^ n ↔ a != 0
  proof: by
  obtain ⟨k, rfl⟩ := hn; rw [pow_add, mul_self_pos, pow_ne_zero_iff (by simpa using h₀)]

中文:
引理 Even.pow_pos_iff
  条件: (hn : Even n) (h₀ : n != 0)
  结论: 0 < a ^ n ↔ a != 0
  证明: by
  obtain ⟨k, rfl⟩ := hn; rw [pow_add, mul_self_pos, pow_ne_zero_iff (by simpa using h₀)]

Depends on / 依赖: mul_self_pos, pow_add, pow_ne_zero_iff
-/
lemma Even.pow_pos_iff (hn : Even n) (h₀ : n != 0) : 0 < a ^ n ↔ a != 0 := by
  obtain ⟨k, rfl⟩ := hn; rw [pow_add, mul_self_pos, pow_ne_zero_iff (by simpa using h₀)]

/--
lemma `Odd.pow_neg_iff` / 引理 `Odd.pow_neg_iff`

English:
lemma Odd.pow_neg_iff
  given: (hn : Odd n)
  statement: a ^ n < 0 ↔ a < 0
  proof: by
  refine ⟨lt_imp_lt_of_le_imp_le (pow_nonneg · _), fun ha => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ]
  exact mul_neg_of_pos_of_neg ((even_two_mul _).pow_pos ha.ne) ha

中文:
引理 Odd.pow_neg_iff
  条件: (hn : Odd n)
  结论: a ^ n < 0 ↔ a < 0
  证明: by
  refine ⟨lt_imp_lt_of_le_imp_le (pow_nonneg · _), fun ha => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ]
  exact mul_neg_of_pos_of_neg ((even_two_mul _).pow_pos ha.ne) ha

Depends on / 依赖: even_two_mul, ha.ne, lt_imp_lt_of_le_imp_le, mul_neg_of_pos_of_neg, pow_nonneg, pow_pos, pow_succ
-/
lemma Odd.pow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0 := by
  refine ⟨lt_imp_lt_of_le_imp_le (pow_nonneg · _), fun ha => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ]
  exact mul_neg_of_pos_of_neg ((even_two_mul _).pow_pos ha.ne) ha

/--
lemma `Odd.pow_nonneg_iff` / 引理 `Odd.pow_nonneg_iff`

English:
lemma Odd.pow_nonneg_iff
  given: (hn : Odd n)
  statement: 0 <= a ^ n ↔ 0 <= a
  proof: le_iff_le_iff_lt_iff_lt.2 hn.pow_neg_iff

中文:
引理 Odd.pow_nonneg_iff
  条件: (hn : Odd n)
  结论: 0 <= a ^ n ↔ 0 <= a
  证明: le_iff_le_iff_lt_iff_lt.2 hn.pow_neg_iff

Depends on / 依赖: hn.pow_neg_iff, le_iff_le_iff_lt_iff_lt, pow_neg_iff
-/
lemma Odd.pow_nonneg_iff (hn : Odd n) : 0 <= a ^ n ↔ 0 <= a :=
  le_iff_le_iff_lt_iff_lt.2 hn.pow_neg_iff

/--
lemma `Odd.pow_nonpos_iff` / 引理 `Odd.pow_nonpos_iff`

English:
lemma Odd.pow_nonpos_iff
  given: (hn : Odd n)
  statement: a ^ n <= 0 ↔ a <= 0
  proof: by
  rw [le_iff_lt_or_eq]; rw [le_iff_lt_or_eq]; rw [hn.pow_neg_iff]; rw [pow_eq_zero_iff]
  rintro rfl; simp at hn

中文:
引理 Odd.pow_nonpos_iff
  条件: (hn : Odd n)
  结论: a ^ n <= 0 ↔ a <= 0
  证明: by
  rw [le_iff_lt_or_eq]; rw [le_iff_lt_or_eq]; rw [hn.pow_neg_iff]; rw [pow_eq_zero_iff]
  rintro rfl; simp at hn

Depends on / 依赖: hn.pow_neg_iff, le_iff_lt_or_eq, pow_eq_zero_iff, pow_neg_iff
-/
lemma Odd.pow_nonpos_iff (hn : Odd n) : a ^ n <= 0 ↔ a <= 0 := by
  rw [le_iff_lt_or_eq]; rw [le_iff_lt_or_eq]; rw [hn.pow_neg_iff]; rw [pow_eq_zero_iff]
  rintro rfl; simp at hn

/--
lemma `Odd.pow_pos_iff` / 引理 `Odd.pow_pos_iff`

English:
lemma Odd.pow_pos_iff
  given: (hn : Odd n)
  statement: 0 < a ^ n ↔ 0 < a
  proof: lt_iff_lt_of_le_iff_le hn.pow_nonpos_iff

alias ⟨_, Odd.pow_nonpos⟩ := Odd.pow_nonpos_iff
alias ⟨_, Odd.pow_neg⟩ := Odd.pow_neg_iff

中文:
引理 Odd.pow_pos_iff
  条件: (hn : Odd n)
  结论: 0 < a ^ n ↔ 0 < a
  证明: lt_iff_lt_of_le_iff_le hn.pow_nonpos_iff

alias ⟨_, Odd.pow_nonpos⟩ := Odd.pow_nonpos_iff
alias ⟨_, Odd.pow_neg⟩ := Odd.pow_neg_iff

Depends on / 依赖: hn.pow_nonpos_iff, lt_iff_lt_of_le_iff_le, pow_nonpos_iff
-/
lemma Odd.pow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a := lt_iff_lt_of_le_iff_le hn.pow_nonpos_iff

alias ⟨_, Odd.pow_nonpos⟩ := Odd.pow_nonpos_iff
alias ⟨_, Odd.pow_neg⟩ := Odd.pow_neg_iff

/--
lemma `Odd.strictMono_pow` / 引理 `Odd.strictMono_pow`

English:
lemma Odd.strictMono_pow
  given: (hn : Odd n)
  statement: StrictMono fun a : R => a ^ n
  proof: by
  have hn₀ : n != 0 := by rintro rfl; simp [Odd] at hn
  intro a b hab
  obtain ha | ha := le_total 0 a
  · exact pow_lt_pow_left₀ hab ha hn₀
  obtain hb | hb := lt_or_ge 0 b
  · exact (hn.pow_nonpos ha).trans_lt (pow_pos hb _)
  obtain ⟨c, hac⟩ := exists_add_of_le ha
  obtain ⟨d, hbd⟩ := exists_

中文:
引理 Odd.strictMono_pow
  条件: (hn : Odd n)
  结论: 严格递增 fun a : R => a ^ n
  证明: by
  have hn₀ : n != 0 := by rintro rfl; simp [Odd] at hn
  intro a b hab
  obtain ha | ha := le_total 0 a
  · exact pow_lt_pow_left₀ hab ha hn₀
  obtain hb | hb := lt_or_ge 0 b
  · exact (hn.pow_nonpos ha).trans_lt (pow_pos hb _)
  obtain ⟨c, hac⟩ := exists_add_of_le ha
  obtain ⟨d, hbd⟩ := exists_

Depends on / 依赖: add_assoc, exists_add_of_le, hb.trans_eq, hn.pow_add_pow_eq_zero, hn.pow_nonpos, le_total, lt_of_add_lt_add_right, lt_or_ge, nonneg_of_le_add_right, pow_add_pow_eq_zero, pow_nonpos, pow_pos, trans_eq, trans_lt
-/
lemma Odd.strictMono_pow (hn : Odd n) : StrictMono fun a : R => a ^ n := by
  have hn₀ : n != 0 := by rintro rfl; simp [Odd] at hn
  intro a b hab
  obtain ha | ha := le_total 0 a
  · exact pow_lt_pow_left₀ hab ha hn₀
  obtain hb | hb := lt_or_ge 0 b
  · exact (hn.pow_nonpos ha).trans_lt (pow_pos hb _)
  obtain ⟨c, hac⟩ := exists_add_of_le ha
  obtain ⟨d, hbd⟩ := exists_add_of_le hb
  have hd := nonneg_of_le_add_right (hb.trans_eq hbd)
  refine lt_of_add_lt_add_right (a := c ^ n + d ^ n) ?_
  dsimp
  calc
    a ^ n + (c ^ n + d ^ n) = d ^ n := by
      rw [← add_assoc]; rw [hn.pow_add_pow_eq_zero hac.symm]; rw [zero_add]
    _ < c ^ n := pow_lt_pow_left₀ ?_ hd hn₀
    _ = b ^ n + (c ^ n + d ^ n) := by rw [add_left_comm, hn.pow_add_pow_eq_zero hbd.symm, add_zero]
  refine lt_of_add_lt_add_right (a := a + b) ?_
  rwa [add_rotate', ← hbd, add_zero, add_left_comm, ← add_assoc, ← hac, zero_add]

/--
lemma `Odd.pow_injective` / 引理 `Odd.pow_injective`

English:
lemma Odd.pow_injective
  given: {n : Nat} (hn : Odd n)
  statement: Injective (· ^ n : R -> R)
  proof: hn.strictMono_pow.injective

中文:
引理 Odd.pow_injective
  条件: {n : 自然数} (hn : Odd n)
  结论: 单射 (· ^ n : R -> R)
  证明: hn.strictMono_pow.injective

Depends on / 依赖: hn.strictMono_pow.injective, injective, strictMono_pow
-/
lemma Odd.pow_injective {n : Nat} (hn : Odd n) : Injective (· ^ n : R -> R) :=
  hn.strictMono_pow.injective

/--
lemma `Odd.pow_lt_pow` / 引理 `Odd.pow_lt_pow`

English:
lemma Odd.pow_lt_pow
  given: {n : Nat} (hn : Odd n) {a b : R}
  statement: a ^ n < b ^ n ↔ a < b
  proof: hn.strictMono_pow.lt_iff_lt

中文:
引理 Odd.pow_lt_pow
  条件: {n : 自然数} (hn : Odd n) {a b : R}
  结论: a ^ n < b ^ n ↔ a < b
  证明: hn.strictMono_pow.lt_iff_lt

Depends on / 依赖: hn.strictMono_pow.lt_iff_lt, lt_iff_lt, strictMono_pow
-/
lemma Odd.pow_lt_pow {n : Nat} (hn : Odd n) {a b : R} : a ^ n < b ^ n ↔ a < b :=
  hn.strictMono_pow.lt_iff_lt

/--
lemma `Odd.pow_le_pow` / 引理 `Odd.pow_le_pow`

English:
lemma Odd.pow_le_pow
  given: {n : Nat} (hn : Odd n) {a b : R}
  statement: a ^ n <= b ^ n ↔ a <= b
  proof: hn.strictMono_pow.le_iff_le

中文:
引理 Odd.pow_le_pow
  条件: {n : 自然数} (hn : Odd n) {a b : R}
  结论: a ^ n <= b ^ n ↔ a <= b
  证明: hn.strictMono_pow.le_iff_le

Depends on / 依赖: hn.strictMono_pow.le_iff_le, le_iff_le, strictMono_pow
-/
lemma Odd.pow_le_pow {n : Nat} (hn : Odd n) {a b : R} : a ^ n <= b ^ n ↔ a <= b :=
  hn.strictMono_pow.le_iff_le

/--
lemma `Odd.pow_inj` / 引理 `Odd.pow_inj`

English:
lemma Odd.pow_inj
  given: {n : Nat} (hn : Odd n) {a b : R}
  statement: a ^ n = b ^ n ↔ a = b
  proof: hn.pow_injective.eq_iff

中文:
引理 Odd.pow_inj
  条件: {n : 自然数} (hn : Odd n) {a b : R}
  结论: a ^ n = b ^ n ↔ a = b
  证明: hn.pow_injective.eq_iff

Depends on / 依赖: eq_iff, hn.pow_injective.eq_iff, pow_injective
-/
lemma Odd.pow_inj {n : Nat} (hn : Odd n) {a b : R} : a ^ n = b ^ n ↔ a = b :=
  hn.pow_injective.eq_iff

/--
lemma `sq_pos_iff` / 引理 `sq_pos_iff`

English:
lemma sq_pos_iff
  given: {a : R}
  statement: 0 < a ^ 2 ↔ a != 0
  proof: even_two.pow_pos_iff two_ne_zero

alias ⟨_, sq_pos_of_ne_zero⟩ := sq_pos_iff
alias pow_two_pos_of_ne_zero := sq_pos_of_ne_zero

中文:
引理 sq_pos_iff
  条件: {a : R}
  结论: 0 < a ^ 2 ↔ a != 0
  证明: even_two.pow_pos_iff two_ne_zero

alias ⟨_, sq_pos_of_ne_zero⟩ := sq_pos_iff
alias pow_two_pos_of_ne_zero := sq_pos_of_ne_zero

Depends on / 依赖: even_two, even_two.pow_pos_iff, pow_pos_iff, two_ne_zero
-/
lemma sq_pos_iff {a : R} : 0 < a ^ 2 ↔ a != 0 := even_two.pow_pos_iff two_ne_zero

alias ⟨_, sq_pos_of_ne_zero⟩ := sq_pos_iff
alias pow_two_pos_of_ne_zero := sq_pos_of_ne_zero

end LinearOrderedSemiring
