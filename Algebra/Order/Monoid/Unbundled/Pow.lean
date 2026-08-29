/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Lemmas about the interaction of power operations with order in terms of `CovariantClass`
-/

public section

open Function

variable {β G M : Type*}

section Monoid

variable [Monoid M]

section Preorder

variable [Preorder M]

namespace Left

variable [MulLeftMono M] {a : M}

@[to_additive Left.nsmul_nonneg]
/--
theorem `one_le_pow_of_le` / 定理 `one_le_pow_of_le`

English:
theorem one_le_pow_of_le
  given: (ha : 1 <= a)
  statement: forall n : Nat, 1 <= a ^ n

中文:
定理 one_le_pow_of_le
  条件: (ha : 1 <= a)
  结论: 对任意 n : 自然数, 1 <= a ^ n
-/
theorem one_le_pow_of_le (ha : 1 <= a) : forall n : Nat, 1 <= a ^ n
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ]
    exact one_le_mul (one_le_pow_of_le ha k) ha

@[to_additive nsmul_nonpos]
/--
theorem `pow_le_one_of_le` / 定理 `pow_le_one_of_le`

English:
theorem pow_le_one_of_le
  given: (ha : a <= 1) (n : Nat)
  statement: a ^ n <= 1
  proof: one_le_pow_of_le (M := Mᵒᵈ) ha n

@[to_additive nsmul_neg]

中文:
定理 pow_le_one_of_le
  条件: (ha : a <= 1) (n : 自然数)
  结论: a ^ n <= 1
  证明: one_le_pow_of_le (M := Mᵒᵈ) ha n

@[to_additive nsmul_neg]

Depends on / 依赖: one_le_pow_of_le
-/
theorem pow_le_one_of_le (ha : a <= 1) (n : Nat) : a ^ n <= 1 := one_le_pow_of_le (M := Mᵒᵈ) ha n

@[to_additive nsmul_neg]
/--
theorem `pow_lt_one_of_lt` / 定理 `pow_lt_one_of_lt`

English:
theorem pow_lt_one_of_lt
  given: {a : M} {n : Nat} (h : a < 1) (hn : n != 0)
  statement: a ^ n < 1
  proof: by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
  rw [pow_succ']
  exact mul_lt_one_of_lt_of_le h (pow_le_one_of_le h.le _)

中文:
定理 pow_lt_one_of_lt
  条件: {a : M} {n : 自然数} (h : a < 1) (hn : n != 0)
  结论: a ^ n < 1
  证明: by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
  rw [pow_succ']
  exact mul_lt_one_of_lt_of_le h (pow_le_one_of_le h.le _)

Depends on / 依赖: Nat.exists_eq_succ_of_ne_zero, exists_eq_succ_of_ne_zero, h.le, mul_lt_one_of_lt_of_le, pow_le_one_of_le, pow_succ
-/
theorem pow_lt_one_of_lt {a : M} {n : Nat} (h : a < 1) (hn : n != 0) : a ^ n < 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
  rw [pow_succ']
  exact mul_lt_one_of_lt_of_le h (pow_le_one_of_le h.le _)

end Left

@[to_additive nsmul_nonneg] alias one_le_pow_of_one_le' := Left.one_le_pow_of_le
@[to_additive nsmul_nonpos] alias pow_le_one' := Left.pow_le_one_of_le
@[to_additive nsmul_neg] alias pow_lt_one' := Left.pow_lt_one_of_lt

section Left

variable [MulLeftMono M] {a : M} {n : Nat}

@[to_additive nsmul_left_monotone]
/--
theorem `pow_right_monotone` / 定理 `pow_right_monotone`

English:
theorem pow_right_monotone
  given: (ha : 1 <= a)
  statement: Monotone fun n : Nat => a ^ n
  proof: monotone_nat_of_le_succ fun n => by rw [pow_succ]; exact le_mul_of_one_le_right' ha

中文:
定理 pow_right_monotone
  条件: (ha : 1 <= a)
  结论: Monotone fun n : 自然数 => a ^ n
  证明: monotone_nat_of_le_succ fun n => by rw [pow_succ]; exact le_mul_of_one_le_right' ha

Depends on / 依赖: le_mul_of_one_le_right, monotone_nat_of_le_succ, pow_succ
-/
theorem pow_right_monotone (ha : 1 <= a) : Monotone fun n : Nat => a ^ n :=
  monotone_nat_of_le_succ fun n => by rw [pow_succ]; exact le_mul_of_one_le_right' ha

-- `gcongr low` so that we prefer `Set.pow_subset_pow` and `Finset.pow_subset_pow`
@[to_additive (attr := gcongr low) nsmul_le_nsmul_left]
/--
theorem `pow_le_pow_right'` / 定理 `pow_le_pow_right'`

English:
theorem pow_le_pow_right'
  given: {n m : Nat} (ha : 1 <= a) (h : n <= m)
  statement: a ^ n <= a ^ m
  proof: pow_right_monotone ha h

@[to_additive nsmul_le_nsmul_left_of_nonpos]

中文:
定理 pow_le_pow_right'
  条件: {n m : 自然数} (ha : 1 <= a) (h : n <= m)
  结论: a ^ n <= a ^ m
  证明: pow_right_monotone ha h

@[to_additive nsmul_le_nsmul_left_of_nonpos]

Depends on / 依赖: pow_right_monotone
-/
theorem pow_le_pow_right' {n m : Nat} (ha : 1 <= a) (h : n <= m) : a ^ n <= a ^ m :=
  pow_right_monotone ha h

@[to_additive nsmul_le_nsmul_left_of_nonpos]
/--
theorem `pow_le_pow_right_of_le_one'` / 定理 `pow_le_pow_right_of_le_one'`

English:
theorem pow_le_pow_right_of_le_one'
  given: {n m : Nat} (ha : a <= 1) (h : n <= m)
  statement: a ^ m <= a ^ n
  proof: pow_le_pow_right' (M := Mᵒᵈ) ha h

@[to_additive nsmul_pos]

中文:
定理 pow_le_pow_right_of_le_one'
  条件: {n m : 自然数} (ha : a <= 1) (h : n <= m)
  结论: a ^ m <= a ^ n
  证明: pow_le_pow_right' (M := Mᵒᵈ) ha h

@[to_additive nsmul_pos]

Depends on / 依赖: pow_le_pow_right
-/
theorem pow_le_pow_right_of_le_one' {n m : Nat} (ha : a <= 1) (h : n <= m) : a ^ m <= a ^ n :=
  pow_le_pow_right' (M := Mᵒᵈ) ha h

@[to_additive nsmul_pos]
/--
theorem `one_lt_pow'` / 定理 `one_lt_pow'`

English:
theorem one_lt_pow'
  given: (ha : 1 < a) {k : Nat} (hk : k != 0)
  statement: 1 < a ^ k
  proof: pow_lt_one' (M := Mᵒᵈ) ha hk

@[to_additive]

中文:
定理 one_lt_pow'
  条件: (ha : 1 < a) {k : 自然数} (hk : k != 0)
  结论: 1 < a ^ k
  证明: pow_lt_one' (M := Mᵒᵈ) ha hk

@[to_additive]

Depends on / 依赖: pow_lt_one
-/
theorem one_lt_pow' (ha : 1 < a) {k : Nat} (hk : k != 0) : 1 < a ^ k :=
  pow_lt_one' (M := Mᵒᵈ) ha hk

@[to_additive]
/--
lemma `le_self_pow` / 引理 `le_self_pow`

English:
lemma le_self_pow
  given: (ha : 1 <= a) (hn : n != 0)
  statement: a <= a ^ n
  proof: by
  simpa using pow_le_pow_right' ha (Nat.one_le_iff_ne_zero.2 hn)

中文:
引理 le_self_pow
  条件: (ha : 1 <= a) (hn : n != 0)
  结论: a <= a ^ n
  证明: by
  simpa using pow_le_pow_right' ha (Nat.one_le_iff_ne_zero.2 hn)

Depends on / 依赖: Nat.one_le_iff_ne_zero, one_le_iff_ne_zero, pow_le_pow_right
-/
lemma le_self_pow (ha : 1 <= a) (hn : n != 0) : a <= a ^ n := by
  simpa using pow_le_pow_right' ha (Nat.one_le_iff_ne_zero.2 hn)

end Left

section LeftLt

variable [MulLeftStrictMono M] {a : M} {n m : Nat}

@[to_additive nsmul_left_strictMono]
/--
theorem `pow_right_strictMono'` / 定理 `pow_right_strictMono'`

English:
theorem pow_right_strictMono'
  given: (ha : 1 < a)
  statement: StrictMono ((a ^ ·) : Nat -> M)
  proof: strictMono_nat_of_lt_succ fun n => by rw [pow_succ]; exact lt_mul_of_one_lt_right' (a ^ n) ha

@[to_additive (attr := gcongr) nsmul_lt_nsmul_left]

中文:
定理 pow_right_strictMono'
  条件: (ha : 1 < a)
  结论: StrictMono ((a ^ ·) : 自然数 -> M)
  证明: strictMono_nat_of_lt_succ fun n => by rw [pow_succ]; exact lt_mul_of_one_lt_right' (a ^ n) ha

@[to_additive (attr := gcongr) nsmul_lt_nsmul_left]

Depends on / 依赖: lt_mul_of_one_lt_right, pow_succ, strictMono_nat_of_lt_succ
-/
theorem pow_right_strictMono' (ha : 1 < a) : StrictMono ((a ^ ·) : Nat -> M) :=
  strictMono_nat_of_lt_succ fun n => by rw [pow_succ]; exact lt_mul_of_one_lt_right' (a ^ n) ha

@[to_additive (attr := gcongr) nsmul_lt_nsmul_left]
/--
theorem `pow_lt_pow_right'` / 定理 `pow_lt_pow_right'`

English:
theorem pow_lt_pow_right'
  given: (ha : 1 < a) (h : n < m)
  statement: a ^ n < a ^ m
  proof: pow_right_strictMono' ha h

中文:
定理 pow_lt_pow_right'
  条件: (ha : 1 < a) (h : n < m)
  结论: a ^ n < a ^ m
  证明: pow_right_strictMono' ha h

Depends on / 依赖: pow_right_strictMono
-/
theorem pow_lt_pow_right' (ha : 1 < a) (h : n < m) : a ^ n < a ^ m :=
  pow_right_strictMono' ha h

end LeftLt

section Right

variable [MulRightMono M] {x : M}

@[to_additive Right.nsmul_nonneg]
/--
theorem `Right.one_le_pow_of_le` / 定理 `Right.one_le_pow_of_le`

English:
theorem Right.one_le_pow_of_le
  given: (hx : 1 <= x)
  statement: forall {n : Nat}, 1 <= x ^ n

中文:
定理 Right.one_le_pow_of_le
  条件: (hx : 1 <= x)
  结论: 对任意 {n : 自然数}, 1 <= x ^ n
-/
theorem Right.one_le_pow_of_le (hx : 1 <= x) : forall {n : Nat}, 1 <= x ^ n
  | 0 => (pow_zero _).ge
  | n + 1 => by
    rw [pow_succ]
    exact Right.one_le_mul (Right.one_le_pow_of_le hx) hx

@[to_additive Right.nsmul_nonpos]
/--
theorem `Right.pow_le_one_of_le` / 定理 `Right.pow_le_one_of_le`

English:
theorem Right.pow_le_one_of_le
  given: (hx : x <= 1) {n : Nat}
  statement: x ^ n <= 1
  proof: Right.one_le_pow_of_le (M := Mᵒᵈ) hx

@[to_additive Right.nsmul_neg]

中文:
定理 Right.pow_le_one_of_le
  条件: (hx : x <= 1) {n : 自然数}
  结论: x ^ n <= 1
  证明: Right.one_le_pow_of_le (M := Mᵒᵈ) hx

@[to_additive Right.nsmul_neg]

Depends on / 依赖: Right.one_le_pow_of_le, one_le_pow_of_le
-/
theorem Right.pow_le_one_of_le (hx : x <= 1) {n : Nat} : x ^ n <= 1 :=
  Right.one_le_pow_of_le (M := Mᵒᵈ) hx

@[to_additive Right.nsmul_neg]
/--
theorem `Right.pow_lt_one_of_lt` / 定理 `Right.pow_lt_one_of_lt`

English:
theorem Right.pow_lt_one_of_lt
  given: {n : Nat} {x : M} (hn : 0 < n) (h : x < 1)
  statement: x ^ n < 1
  proof: by
  rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨k, rfl⟩
  rw [pow_succ]
  exact mul_lt_one_of_le_of_lt (pow_le_one_of_le h.le) h

中文:
定理 Right.pow_lt_one_of_lt
  条件: {n : 自然数} {x : M} (hn : 0 < n) (h : x < 1)
  结论: x ^ n < 1
  证明: by
  rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨k, rfl⟩
  rw [pow_succ]
  exact mul_lt_one_of_le_of_lt (pow_le_one_of_le h.le) h

Depends on / 依赖: Nat.exists_eq_succ_of_ne_zero, exists_eq_succ_of_ne_zero, h.le, hn.ne, mul_lt_one_of_le_of_lt, pow_le_one_of_le, pow_succ
-/
theorem Right.pow_lt_one_of_lt {n : Nat} {x : M} (hn : 0 < n) (h : x < 1) : x ^ n < 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨k, rfl⟩
  rw [pow_succ]
  exact mul_lt_one_of_le_of_lt (pow_le_one_of_le h.le) h

/-- This lemma is useful in non-cancellative monoids, like sets under pointwise operations. -/
@[to_additive
/-- This lemma is useful in non-cancellative monoids, like sets under pointwise operations. -/]
/--
lemma `pow_le_pow_mul_of_sq_le_mul` / 引理 `pow_le_pow_mul_of_sq_le_mul`

English:
lemma pow_le_pow_mul_of_sq_le_mul
  given: [MulLeftMono M] {a b : M} (hab : a ^ 2 <= b * a)
  proof: by rw [pow_succ]
      _ <= b ^ n * a * a := by grw [pow_le_pow_mul_of_sq_le_mul hab (by lia)]; simp
      _ = b ^ n * a ^ 2 := by rw [mul_assoc, sq]
      _ <= b ^ n * (b * a) := by grw [hab]
      _ = b ^ (n + 1) * a := by rw [← mul_assoc, ← pow_succ]

中文:
引理 pow_le_pow_mul_of_sq_le_mul
  条件: [MulLeftMono M] {a b : M} (hab : a ^ 2 <= b * a)
  证明: by rw [pow_succ]
      _ <= b ^ n * a * a := by grw [pow_le_pow_mul_of_sq_le_mul hab (by lia)]; simp
      _ = b ^ n * a ^ 2 := by rw [mul_assoc, sq]
      _ <= b ^ n * (b * a) := by grw [hab]
      _ = b ^ (n + 1) * a := by rw [← mul_assoc, ← pow_succ]

Depends on / 依赖: mul_assoc, pow_le_pow_mul_of_sq_le_mul, pow_succ
-/
lemma pow_le_pow_mul_of_sq_le_mul [MulLeftMono M] {a b : M} (hab : a ^ 2 <= b * a) :
    forall {n}, n != 0 -> a ^ n <= b ^ (n - 1) * a
  | 1, _ => by simp
  | n + 2, _ => by
    calc
      a ^ (n + 2) = a ^ (n + 1) * a := by rw [pow_succ]
      _ <= b ^ n * a * a := by grw [pow_le_pow_mul_of_sq_le_mul hab (by lia)]; simp
      _ = b ^ n * a ^ 2 := by rw [mul_assoc, sq]
      _ <= b ^ n * (b * a) := by grw [hab]
      _ = b ^ (n + 1) * a := by rw [← mul_assoc, ← pow_succ]

end Right

section CovariantLTSwap

variable [Preorder β] [MulLeftStrictMono M] [MulRightStrictMono M] {f : β -> M} {n : Nat}

@[to_additive StrictMono.const_nsmul]
/--
theorem `StrictMono.pow_const` / 定理 `StrictMono.pow_const`

English:
theorem StrictMono.pow_const
  given: (hf : StrictMono f)
  statement: forall {n : Nat}, n != 0 -> StrictMono (f · ^ n)

中文:
定理 StrictMono.pow_const
  条件: (hf : StrictMono f)
  结论: 对任意 {n : 自然数}, n != 0 -> StrictMono (f · ^ n)
-/
theorem StrictMono.pow_const (hf : StrictMono f) : forall {n : Nat}, n != 0 -> StrictMono (f · ^ n)
  | 0, hn => (hn rfl).elim
  | 1, _ => by simpa
| Nat.succ Nat.succ n, _ => by
    simpa only [pow_succ] using (hf.pow_const n.succ_ne_zero).mul' hf

/-- See also `pow_left_strictMonoOn₀`. -/
@[to_additive nsmul_right_strictMono]
/--
theorem `pow_left_strictMono` / 定理 `pow_left_strictMono`

English:
theorem pow_left_strictMono
  given: (hn : n != 0)
  statement: StrictMono (· ^ n : M -> M)
  proof: strictMono_id.pow_const hn

@[to_additive (attr := mono, gcongr) nsmul_lt_nsmul_right]

中文:
定理 pow_left_strictMono
  条件: (hn : n != 0)
  结论: StrictMono (· ^ n : M -> M)
  证明: strictMono_id.pow_const hn

@[to_additive (attr := mono, gcongr) nsmul_lt_nsmul_right]

Depends on / 依赖: pow_const, strictMono_id, strictMono_id.pow_const
-/
theorem pow_left_strictMono (hn : n != 0) : StrictMono (· ^ n : M -> M) := strictMono_id.pow_const hn

@[to_additive (attr := mono, gcongr) nsmul_lt_nsmul_right]
/--
lemma `pow_lt_pow_left'` / 引理 `pow_lt_pow_left'`

English:
lemma pow_lt_pow_left'
  given: (hn : n != 0) {a b : M} (hab : a < b)
  statement: a ^ n < b ^ n
  proof: pow_left_strictMono hn hab

中文:
引理 pow_lt_pow_left'
  条件: (hn : n != 0) {a b : M} (hab : a < b)
  结论: a ^ n < b ^ n
  证明: pow_left_strictMono hn hab

Depends on / 依赖: pow_left_strictMono
-/
lemma pow_lt_pow_left' (hn : n != 0) {a b : M} (hab : a < b) : a ^ n < b ^ n :=
  pow_left_strictMono hn hab

end CovariantLTSwap

section CovariantLESwap

variable [Preorder β] [MulLeftMono M] [MulRightMono M]

@[to_additive (attr := mono, gcongr) nsmul_le_nsmul_right]
/--
theorem `pow_le_pow_left'` / 定理 `pow_le_pow_left'`

English:
theorem pow_le_pow_left'
  given: {a b : M} (hab : a <= b)
  statement: forall i : Nat, a ^ i <= b ^ i

中文:
定理 pow_le_pow_left'
  条件: {a b : M} (hab : a <= b)
  结论: 对任意 i : 自然数, a ^ i <= b ^ i
-/
theorem pow_le_pow_left' {a b : M} (hab : a <= b) : forall i : Nat, a ^ i <= b ^ i
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ]; rw [pow_succ]
    exact mul_le_mul' (pow_le_pow_left' hab k) hab

@[to_additive Monotone.const_nsmul]
/--
theorem `Monotone.pow_const` / 定理 `Monotone.pow_const`

English:
theorem Monotone.pow_const
  given: {f : β -> M} (hf : Monotone f)
  statement: forall n : Nat, Monotone fun a => f a ^ n

中文:
定理 Monotone.pow_const
  条件: {f : β -> M} (hf : Monotone f)
  结论: 对任意 n : 自然数, Monotone fun a => f a ^ n
-/
theorem Monotone.pow_const {f : β -> M} (hf : Monotone f) : forall n : Nat, Monotone fun a => f a ^ n
  | 0 => by simpa using monotone_const
  | n + 1 => by
    simp_rw [pow_succ]
    exact (Monotone.pow_const hf _).mul' hf

@[to_additive nsmul_right_mono]
/--
theorem `pow_left_mono` / 定理 `pow_left_mono`

English:
theorem pow_left_mono
  given: (n : Nat)
  statement: Monotone fun a : M => a ^ n
  proof: monotone_id.pow_const _

中文:
定理 pow_left_mono
  条件: (n : 自然数)
  结论: Monotone fun a : M => a ^ n
  证明: monotone_id.pow_const _

Depends on / 依赖: monotone_id, monotone_id.pow_const, pow_const
-/
theorem pow_left_mono (n : Nat) : Monotone fun a : M => a ^ n := monotone_id.pow_const _

-- `gcongr low` so that we prefer `Set.pow_subset_pow` and `Finset.pow_subset_pow`
@[to_additive (attr := gcongr low)]
/--
lemma `pow_le_pow` / 引理 `pow_le_pow`

English:
lemma pow_le_pow
  given: {a b : M} (hab : a <= b) (ht : 1 <= b) {m n : Nat} (hmn : m <= n)
  statement: a ^ m <= b ^ n
  proof: (pow_le_pow_left' hab _).trans (pow_le_pow_right' ht hmn)

中文:
引理 pow_le_pow
  条件: {a b : M} (hab : a <= b) (ht : 1 <= b) {m n : 自然数} (hmn : m <= n)
  结论: a ^ m <= b ^ n
  证明: (pow_le_pow_left' hab _).trans (pow_le_pow_right' ht hmn)

Depends on / 依赖: pow_le_pow_left, pow_le_pow_right
-/
lemma pow_le_pow {a b : M} (hab : a <= b) (ht : 1 <= b) {m n : Nat} (hmn : m <= n) : a ^ m <= b ^ n :=
  (pow_le_pow_left' hab _).trans (pow_le_pow_right' ht hmn)

end CovariantLESwap

end Preorder

section SemilatticeSup
variable [SemilatticeSup M] [MulLeftMono M] [MulRightMono M] {a b : M} {n : Nat}

/--
lemma `le_pow_sup` / 引理 `le_pow_sup`

English:
lemma le_pow_sup
  statement: a ^ n ⊔ b ^ n <= (a ⊔ b) ^ n
  proof: sup_le (pow_le_pow_left' le_sup_left _) (pow_le_pow_left' le_sup_right _)

中文:
引理 le_pow_sup
  结论: a ^ n ⊔ b ^ n <= (a ⊔ b) ^ n
  证明: sup_le (pow_le_pow_left' le_sup_left _) (pow_le_pow_left' le_sup_right _)

Depends on / 依赖: le_sup_left, le_sup_right, pow_le_pow_left, sup_le
-/
lemma le_pow_sup : a ^ n ⊔ b ^ n <= (a ⊔ b) ^ n :=
  sup_le (pow_le_pow_left' le_sup_left _) (pow_le_pow_left' le_sup_right _)

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf M] [MulLeftMono M] [MulRightMono M] {a b : M} {n : Nat}

/--
lemma `pow_inf_le` / 引理 `pow_inf_le`

English:
lemma pow_inf_le
  statement: (a ⊓ b) ^ n <= a ^ n ⊓ b ^ n
  proof: le_inf (pow_le_pow_left' inf_le_left _) (pow_le_pow_left' inf_le_right _)

中文:
引理 pow_inf_le
  结论: (a ⊓ b) ^ n <= a ^ n ⊓ b ^ n
  证明: le_inf (pow_le_pow_left' inf_le_left _) (pow_le_pow_left' inf_le_right _)

Depends on / 依赖: inf_le_left, inf_le_right, le_inf, pow_le_pow_left
-/
lemma pow_inf_le : (a ⊓ b) ^ n <= a ^ n ⊓ b ^ n :=
  le_inf (pow_le_pow_left' inf_le_left _) (pow_le_pow_left' inf_le_right _)

end SemilatticeInf

section LinearOrder

variable [LinearOrder M]

section CovariantLE

variable [MulLeftMono M]

-- This generalises to lattices. See `pow_two_semiclosed`
@[to_additive nsmul_nonneg_iff]
/--
theorem `one_le_pow_iff` / 定理 `one_le_pow_iff`

English:
theorem one_le_pow_iff
  given: {x : M} {n : Nat} (hn : n != 0)
  statement: 1 <= x ^ n ↔ 1 <= x
  proof: ⟨le_imp_le_of_lt_imp_lt fun h => pow_lt_one' h hn, fun h => one_le_pow_of_one_le' h n⟩

@[to_additive]

中文:
定理 one_le_pow_iff
  条件: {x : M} {n : 自然数} (hn : n != 0)
  结论: 1 <= x ^ n ↔ 1 <= x
  证明: ⟨le_imp_le_of_lt_imp_lt fun h => pow_lt_one' h hn, fun h => one_le_pow_of_one_le' h n⟩

@[to_additive]

Depends on / 依赖: le_imp_le_of_lt_imp_lt, one_le_pow_of_one_le, pow_lt_one
-/
theorem one_le_pow_iff {x : M} {n : Nat} (hn : n != 0) : 1 <= x ^ n ↔ 1 <= x :=
  ⟨le_imp_le_of_lt_imp_lt fun h => pow_lt_one' h hn, fun h => one_le_pow_of_one_le' h n⟩

@[to_additive]
/--
theorem `pow_le_one_iff` / 定理 `pow_le_one_iff`

English:
theorem pow_le_one_iff
  given: {x : M} {n : Nat} (hn : n != 0)
  statement: x ^ n <= 1 ↔ x <= 1
  proof: one_le_pow_iff (M := Mᵒᵈ) hn

@[to_additive nsmul_pos_iff]

中文:
定理 pow_le_one_iff
  条件: {x : M} {n : 自然数} (hn : n != 0)
  结论: x ^ n <= 1 ↔ x <= 1
  证明: one_le_pow_iff (M := Mᵒᵈ) hn

@[to_additive nsmul_pos_iff]

Depends on / 依赖: one_le_pow_iff
-/
theorem pow_le_one_iff {x : M} {n : Nat} (hn : n != 0) : x ^ n <= 1 ↔ x <= 1 :=
  one_le_pow_iff (M := Mᵒᵈ) hn

@[to_additive nsmul_pos_iff]
/--
theorem `one_lt_pow_iff` / 定理 `one_lt_pow_iff`

English:
theorem one_lt_pow_iff
  given: {x : M} {n : Nat} (hn : n != 0)
  statement: 1 < x ^ n ↔ 1 < x
  proof: lt_iff_lt_of_le_iff_le (pow_le_one_iff hn)

@[to_additive]

中文:
定理 one_lt_pow_iff
  条件: {x : M} {n : 自然数} (hn : n != 0)
  结论: 1 < x ^ n ↔ 1 < x
  证明: lt_iff_lt_of_le_iff_le (pow_le_one_iff hn)

@[to_additive]

Depends on / 依赖: lt_iff_lt_of_le_iff_le, pow_le_one_iff
-/
theorem one_lt_pow_iff {x : M} {n : Nat} (hn : n != 0) : 1 < x ^ n ↔ 1 < x :=
  lt_iff_lt_of_le_iff_le (pow_le_one_iff hn)

@[to_additive]
/--
theorem `pow_lt_one_iff` / 定理 `pow_lt_one_iff`

English:
theorem pow_lt_one_iff
  given: {x : M} {n : Nat} (hn : n != 0)
  statement: x ^ n < 1 ↔ x < 1
  proof: lt_iff_lt_of_le_iff_le (one_le_pow_iff hn)

中文:
定理 pow_lt_one_iff
  条件: {x : M} {n : 自然数} (hn : n != 0)
  结论: x ^ n < 1 ↔ x < 1
  证明: lt_iff_lt_of_le_iff_le (one_le_pow_iff hn)

Depends on / 依赖: lt_iff_lt_of_le_iff_le, one_le_pow_iff
-/
theorem pow_lt_one_iff {x : M} {n : Nat} (hn : n != 0) : x ^ n < 1 ↔ x < 1 :=
  lt_iff_lt_of_le_iff_le (one_le_pow_iff hn)

end CovariantLE

section CovariantLT

variable [MulLeftStrictMono M] {a : M} {m n : Nat}

@[to_additive nsmul_le_nsmul_iff_left]
/--
theorem `pow_le_pow_iff_right'` / 定理 `pow_le_pow_iff_right'`

English:
theorem pow_le_pow_iff_right'
  given: (ha : 1 < a)
  statement: a ^ m <= a ^ n ↔ m <= n
  proof: (pow_right_strictMono' ha).le_iff_le

@[to_additive nsmul_lt_nsmul_iff_left]

中文:
定理 pow_le_pow_iff_right'
  条件: (ha : 1 < a)
  结论: a ^ m <= a ^ n ↔ m <= n
  证明: (pow_right_strictMono' ha).le_iff_le

@[to_additive nsmul_lt_nsmul_iff_left]

Depends on / 依赖: le_iff_le, pow_right_strictMono
-/
theorem pow_le_pow_iff_right' (ha : 1 < a) : a ^ m <= a ^ n ↔ m <= n :=
  (pow_right_strictMono' ha).le_iff_le

@[to_additive nsmul_lt_nsmul_iff_left]
/--
theorem `pow_lt_pow_iff_right'` / 定理 `pow_lt_pow_iff_right'`

English:
theorem pow_lt_pow_iff_right'
  given: (ha : 1 < a)
  statement: a ^ m < a ^ n ↔ m < n
  proof: (pow_right_strictMono' ha).lt_iff_lt

中文:
定理 pow_lt_pow_iff_right'
  条件: (ha : 1 < a)
  结论: a ^ m < a ^ n ↔ m < n
  证明: (pow_right_strictMono' ha).lt_iff_lt

Depends on / 依赖: lt_iff_lt, pow_right_strictMono
-/
theorem pow_lt_pow_iff_right' (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (pow_right_strictMono' ha).lt_iff_lt

end CovariantLT

section CovariantLESwap

variable [MulLeftMono M] [MulRightMono M]

@[to_additive lt_of_nsmul_lt_nsmul_right]
/--
theorem `lt_of_pow_lt_pow_left'` / 定理 `lt_of_pow_lt_pow_left'`

English:
theorem lt_of_pow_lt_pow_left'
  given: {a b : M} (n : Nat)
  statement: a ^ n < b ^ n -> a < b
  proof: (pow_left_mono _).reflect_lt

@[to_additive min_lt_of_add_lt_two_nsmul]

中文:
定理 lt_of_pow_lt_pow_left'
  条件: {a b : M} (n : 自然数)
  结论: a ^ n < b ^ n -> a < b
  证明: (pow_left_mono _).reflect_lt

@[to_additive min_lt_of_add_lt_two_nsmul]

Depends on / 依赖: pow_left_mono, reflect_lt
-/
theorem lt_of_pow_lt_pow_left' {a b : M} (n : Nat) : a ^ n < b ^ n -> a < b :=
  (pow_left_mono _).reflect_lt

@[to_additive min_lt_of_add_lt_two_nsmul]
/--
theorem `min_lt_of_mul_lt_sq` / 定理 `min_lt_of_mul_lt_sq`

English:
theorem min_lt_of_mul_lt_sq
  given: {a b c : M} (h : a * b < c ^ 2)
  statement: min a b < c
  proof: by
  simpa using min_lt_max_of_mul_lt_mul (h.trans_eq <| pow_two _)

@[to_additive lt_max_of_two_nsmul_lt_add]

中文:
定理 min_lt_of_mul_lt_sq
  条件: {a b c : M} (h : a * b < c ^ 2)
  结论: min a b < c
  证明: by
  simpa using min_lt_max_of_mul_lt_mul (h.trans_eq <| pow_two _)

@[to_additive lt_max_of_two_nsmul_lt_add]

Depends on / 依赖: h.trans_eq, min_lt_max_of_mul_lt_mul, pow_two, trans_eq
-/
theorem min_lt_of_mul_lt_sq {a b c : M} (h : a * b < c ^ 2) : min a b < c := by
  simpa using min_lt_max_of_mul_lt_mul (h.trans_eq <| pow_two _)

@[to_additive lt_max_of_two_nsmul_lt_add]
/--
theorem `lt_max_of_sq_lt_mul` / 定理 `lt_max_of_sq_lt_mul`

English:
theorem lt_max_of_sq_lt_mul
  given: {a b c : M} (h : a ^ 2 < b * c)
  statement: a < max b c
  proof: by
  simpa using min_lt_max_of_mul_lt_mul ((pow_two _).symm.trans_lt h)

中文:
定理 lt_max_of_sq_lt_mul
  条件: {a b c : M} (h : a ^ 2 < b * c)
  结论: a < max b c
  证明: by
  simpa using min_lt_max_of_mul_lt_mul ((pow_two _).symm.trans_lt h)

Depends on / 依赖: min_lt_max_of_mul_lt_mul, pow_two, symm.trans_lt, trans_lt
-/
theorem lt_max_of_sq_lt_mul {a b c : M} (h : a ^ 2 < b * c) : a < max b c := by
  simpa using min_lt_max_of_mul_lt_mul ((pow_two _).symm.trans_lt h)

end CovariantLESwap

section CovariantLTSwap

variable [MulLeftStrictMono M] [MulRightStrictMono M]

@[to_additive nsmul_le_nsmul_iff_right]
/--
theorem `pow_le_pow_iff_left` / 定理 `pow_le_pow_iff_left`

English:
theorem pow_le_pow_iff_left
  given: {a b : M} {n : Nat} (hn : n != 0)
  statement: a ^ n <= b ^ n ↔ a <= b
  proof: (pow_left_strictMono hn).le_iff_le

@[to_additive le_of_nsmul_le_nsmul_right]
alias ⟨le_of_pow_le_pow_left', _⟩ := pow_le_pow_iff_left

@[to_additive min_le_of_add_le_two_nsmul]

中文:
定理 pow_le_pow_iff_left
  条件: {a b : M} {n : 自然数} (hn : n != 0)
  结论: a ^ n <= b ^ n ↔ a <= b
  证明: (pow_left_strictMono hn).le_iff_le

@[to_additive le_of_nsmul_le_nsmul_right]
alias ⟨le_of_pow_le_pow_left', _⟩ := pow_le_pow_iff_left

@[to_additive min_le_of_add_le_two_nsmul]

Depends on / 依赖: le_iff_le, pow_left_strictMono
-/
theorem pow_le_pow_iff_left {a b : M} {n : Nat} (hn : n != 0) : a ^ n <= b ^ n ↔ a <= b :=
  (pow_left_strictMono hn).le_iff_le

@[to_additive le_of_nsmul_le_nsmul_right]
alias ⟨le_of_pow_le_pow_left', _⟩ := pow_le_pow_iff_left

@[to_additive min_le_of_add_le_two_nsmul]
/--
theorem `min_le_of_mul_le_sq` / 定理 `min_le_of_mul_le_sq`

English:
theorem min_le_of_mul_le_sq
  given: {a b c : M} (h : a * b <= c ^ 2)
  statement: min a b <= c
  proof: by
  simpa using min_le_max_of_mul_le_mul (h.trans_eq <| pow_two _)

@[to_additive le_max_of_two_nsmul_le_add]

中文:
定理 min_le_of_mul_le_sq
  条件: {a b c : M} (h : a * b <= c ^ 2)
  结论: min a b <= c
  证明: by
  simpa using min_le_max_of_mul_le_mul (h.trans_eq <| pow_two _)

@[to_additive le_max_of_two_nsmul_le_add]

Depends on / 依赖: h.trans_eq, min_le_max_of_mul_le_mul, pow_two, trans_eq
-/
theorem min_le_of_mul_le_sq {a b c : M} (h : a * b <= c ^ 2) : min a b <= c := by
  simpa using min_le_max_of_mul_le_mul (h.trans_eq <| pow_two _)

@[to_additive le_max_of_two_nsmul_le_add]
/--
theorem `le_max_of_sq_le_mul` / 定理 `le_max_of_sq_le_mul`

English:
theorem le_max_of_sq_le_mul
  given: {a b c : M} (h : a ^ 2 <= b * c)
  statement: a <= max b c
  proof: by
  simpa using min_le_max_of_mul_le_mul ((pow_two _).symm.trans_le h)

中文:
定理 le_max_of_sq_le_mul
  条件: {a b c : M} (h : a ^ 2 <= b * c)
  结论: a <= max b c
  证明: by
  simpa using min_le_max_of_mul_le_mul ((pow_two _).symm.trans_le h)

Depends on / 依赖: min_le_max_of_mul_le_mul, pow_two, symm.trans_le, trans_le
-/
theorem le_max_of_sq_le_mul {a b c : M} (h : a ^ 2 <= b * c) : a <= max b c := by
  simpa using min_le_max_of_mul_le_mul ((pow_two _).symm.trans_le h)

end CovariantLTSwap

@[to_additive Left.nsmul_neg_iff]
/--
theorem `Left.pow_lt_one_iff'` / 定理 `Left.pow_lt_one_iff'`

English:
theorem Left.pow_lt_one_iff'
  given: [MulLeftStrictMono M] {n : Nat} {x : M} (hn : 0 < n)
  proof: haveI := mulLeftMono_of_mulLeftStrictMono M
  pow_lt_one_iff hn.ne'

中文:
定理 Left.pow_lt_one_iff'
  条件: [MulLeftStrictMono M] {n : 自然数} {x : M} (hn : 0 < n)
  证明: haveI := mulLeftMono_of_mulLeftStrictMono M
  pow_lt_one_iff hn.ne'

Depends on / 依赖: hn.ne, mulLeftMono_of_mulLeftStrictMono, pow_lt_one_iff
-/
theorem Left.pow_lt_one_iff' [MulLeftStrictMono M] {n : Nat} {x : M} (hn : 0 < n) :
    x ^ n < 1 ↔ x < 1 :=
  haveI := mulLeftMono_of_mulLeftStrictMono M
  pow_lt_one_iff hn.ne'

/--
theorem `Left.pow_lt_one_iff` / 定理 `Left.pow_lt_one_iff`

English:
theorem Left.pow_lt_one_iff
  given: [MulLeftStrictMono M] {n : Nat} {x : M} (hn : 0 < n)
  proof: Left.pow_lt_one_iff' hn

@[to_additive]

中文:
定理 Left.pow_lt_one_iff
  条件: [MulLeftStrictMono M] {n : 自然数} {x : M} (hn : 0 < n)
  证明: Left.pow_lt_one_iff' hn

@[to_additive]

Depends on / 依赖: Left.pow_lt_one_iff, pow_lt_one_iff
-/
theorem Left.pow_lt_one_iff [MulLeftStrictMono M] {n : Nat} {x : M} (hn : 0 < n) :
    x ^ n < 1 ↔ x < 1 := Left.pow_lt_one_iff' hn

@[to_additive]
/--
theorem `Right.pow_lt_one_iff` / 定理 `Right.pow_lt_one_iff`

English:
theorem Right.pow_lt_one_iff
  statement: [MulRightStrictMono M] {n : Nat} {x : M}
  proof: haveI := mulRightMono_of_mulRightStrictMono M
⟨fun H => not_le.mp fun k => H.not_ge Right.one_le_pow_of_le k, Right.pow_lt_one_of_lt hn⟩

@[to_additive]

中文:
定理 Right.pow_lt_one_iff
  结论: [MulRightStrictMono M] {n : 自然数} {x : M}
  证明: haveI := mulRightMono_of_mulRightStrictMono M
⟨fun H => not_le.mp fun k => H.not_ge Right.one_le_pow_of_le k, Right.pow_lt_one_of_lt hn⟩

@[to_additive]

Depends on / 依赖: H.not_ge, Right.one_le_pow_of_le, Right.pow_lt_one_of_lt, mulRightMono_of_mulRightStrictMono, not_ge, not_le, not_le.mp, one_le_pow_of_le, pow_lt_one_of_lt
-/
theorem Right.pow_lt_one_iff [MulRightStrictMono M] {n : Nat} {x : M}
    (hn : 0 < n) : x ^ n < 1 ↔ x < 1 :=
  haveI := mulRightMono_of_mulRightStrictMono M
⟨fun H => not_le.mp fun k => H.not_ge Right.one_le_pow_of_le k, Right.pow_lt_one_of_lt hn⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulLeftStrictMono
  signature: M] [MulRightStrictMono M] : IsMulTorsionFree M where
  body: (pow_left_strictMono hn).injective

中文:
实例 [MulLeftStrictMono
  签名: M] [MulRightStrictMono M] : IsMulTorsionFree M where
  定义体: (pow_left_strictMono hn).injective

Depends on / 依赖: injective, pow_left_strictMono
-/
instance [MulLeftStrictMono M] [MulRightStrictMono M] : IsMulTorsionFree M where
  pow_left_injective _ hn := (pow_left_strictMono hn).injective

end LinearOrder

end Monoid

section DivInvMonoid

variable [DivInvMonoid G] [Preorder G] [MulLeftMono G]

@[to_additive zsmul_nonneg]
/--
theorem `one_le_zpow` / 定理 `one_le_zpow`

English:
theorem one_le_zpow
  given: {x : G} (H : 1 <= x) {n : Int} (hn : 0 <= n)
  statement: 1 <= x ^ n
  proof: by
  lift n to Nat using hn
  rw [zpow_natCast]
  apply one_le_pow_of_one_le' H

@[to_additive zsmul_pos]

中文:
定理 one_le_zpow
  条件: {x : G} (H : 1 <= x) {n : 整数} (hn : 0 <= n)
  结论: 1 <= x ^ n
  证明: by
  lift n to Nat using hn
  rw [zpow_natCast]
  apply one_le_pow_of_one_le' H

@[to_additive zsmul_pos]

Depends on / 依赖: one_le_pow_of_one_le, zpow_natCast
-/
theorem one_le_zpow {x : G} (H : 1 <= x) {n : Int} (hn : 0 <= n) : 1 <= x ^ n := by
  lift n to Nat using hn
  rw [zpow_natCast]
  apply one_le_pow_of_one_le' H

@[to_additive zsmul_pos]
/--
lemma `one_lt_zpow` / 引理 `one_lt_zpow`

English:
lemma one_lt_zpow
  given: {x : G} (hx : 1 < x) {n : Int} (hn : 0 < n)
  statement: 1 < x ^ n
  proof: by
  lift n to Nat using Int.le_of_lt hn
  rw [zpow_natCast]
  exact one_lt_pow' hx (Int.natCast_pos.mp hn).ne'

中文:
引理 one_lt_zpow
  条件: {x : G} (hx : 1 < x) {n : 整数} (hn : 0 < n)
  结论: 1 < x ^ n
  证明: by
  lift n to Nat using Int.le_of_lt hn
  rw [zpow_natCast]
  exact one_lt_pow' hx (Int.natCast_pos.mp hn).ne'

Depends on / 依赖: Int.le_of_lt, Int.natCast_pos.mp, le_of_lt, natCast_pos, one_lt_pow, zpow_natCast
-/
lemma one_lt_zpow {x : G} (hx : 1 < x) {n : Int} (hn : 0 < n) : 1 < x ^ n := by
  lift n to Nat using Int.le_of_lt hn
  rw [zpow_natCast]
  exact one_lt_pow' hx (Int.natCast_pos.mp hn).ne'

end DivInvMonoid
