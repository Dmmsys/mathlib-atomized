/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yaël Dillies, Yury Kudryashov
-/
module

public import Mathlib.Data.Nat.BinaryRec
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Natural number logarithms

This file defines two `ℕ`-valued analogs of the logarithm of `n` with base `b`:
* `log b n`: Lower logarithm, or floor **log**. Greatest `k` such that `b^k ≤ n`.
* `clog b n`: Upper logarithm, or **c**eil **log**. Least `k` such that `n ≤ b^k`.

These are interesting because, for `1 < b`, `Nat.log b` and `Nat.clog b` are respectively right and
left adjoints of `(b ^ ·)`. See `le_log_iff_pow_le` and `clog_le_iff_le_pow`.

## Implementation notes

We define both functions using recursion on `b`.
In order to compute, e.g., `Nat.log b n`, we compute `e = Nat.log (b * b) n` first,
then figure out whether the answer is `2 * e` or `2 * e + 1`.
The actual implementations use fuel recursion so that `(by decide : Nat.log 2 20 = 4)` works.

Adapted from https://downloads.haskell.org/~ghc/9.0.1/docs/html/libraries/ghc-bignum-1.0/GHC-Num-BigNat.html#v:bigNatLogBase-35-

Note a tail-recursive version of `Nat.log` is also possible:
```
def logTR (b n : ℕ) : ℕ :=
  let rec go : ℕ → ℕ → ℕ | n, acc => if h : b ≤ n ∧ 1 < b then go (n / b) (acc + 1) else acc
  decreasing_by
    have : n / b < n := Nat.div_lt_self (by lia) h.2
    decreasing_trivial
  go n 0
```
but performs worse for large numbers than `Nat.log`:
```
#eval Nat.logTR 2 (2 ^ 1000000)
#eval Nat.log 2 (2 ^ 1000000)
```
-/

@[expose] public section

assert_not_exists OrderTop

namespace Nat

/-! ### Floor logarithm -/


/-- `log b n`, is the logarithm of natural number `n` in base `b`. It returns the largest `k : ℕ`
such that `b^k ≤ n`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot]
/--
Definition of `log` / `log` 的定义

English:
definition log
  signature: (b n : Nat)
  body: if b <= 1 then 0 else (go b n).2 where
  /-- An auxiliary definition for `Nat.log`.

  For `b > 1`, `n ≠ 0`, `n < b ^ fuel`, `Nat.log.go n b fuel = (n / b ^ b.log n, b.log n)`. -/
  go : Nat -> Nat -> Nat × Nat
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then
      (n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e) else (q / b, 2 * e + 1)

中文:
定义 log
  签名: (b n : 自然数)
  定义体: if b <= 1 then 0 else (go b n).2 where
  /-- An auxiliary definition for `Nat.log`.

  For `b > 1`, `n ≠ 0`, `n < b ^ fuel`, `Nat.log.go n b fuel = (n / b ^ b.log n, b.log n)`. -/
  go : Nat -> Nat -> Nat × Nat
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then
      (n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e) else (q / b, 2 * e + 1)
-/
def log (b n : Nat) : Nat :=
  if b <= 1 then 0 else (go b n).2 where
  /-- An auxiliary definition for `Nat.log`.

  For `b > 1`, `n ≠ 0`, `n < b ^ fuel`, `Nat.log.go n b fuel = (n / b ^ b.log n, b.log n)`. -/
  go : Nat -> Nat -> Nat × Nat
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then
      (n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e) else (q / b, 2 * e + 1)

/--
theorem `log_of_left_le_one` / 定理 `log_of_left_le_one`

English:
theorem log_of_left_le_one
  given: {b : Nat} (hb : b <= 1) (n)
  statement: log b n = 0
  proof: by
  rw [log]; rw [if_pos hb]

中文:
定理 log_of_left_le_one
  条件: {b : 自然数} (hb : b <= 1) (n)
  结论: log b n = 0
  证明: by
  rw [log]; rw [if_pos hb]

Depends on / 依赖: if_pos
-/
theorem log_of_left_le_one {b : Nat} (hb : b <= 1) (n) : log b n = 0 := by
  rw [log]; rw [if_pos hb]

/--
theorem `log_of_lt` / 定理 `log_of_lt`

English:
theorem log_of_lt
  given: {b n : Nat} (hb : n < b)
  statement: log b n = 0
  proof: by
  fun_cases log with
  | case1 => rfl
  | case2 => fun_cases log.go with grind

中文:
定理 log_of_lt
  条件: {b n : 自然数} (hb : n < b)
  结论: log b n = 0
  证明: by
  fun_cases log with
  | case1 => rfl
  | case2 => fun_cases log.go with grind

Depends on / 依赖: fun_cases, log.go
-/
theorem log_of_lt {b n : Nat} (hb : n < b) : log b n = 0 := by
  fun_cases log with
  | case1 => rfl
  | case2 => fun_cases log.go with grind

/--
theorem `log.go_aux` / 定理 `log.go_aux`

English:
theorem log.go_aux
  given: {n b fuel : Nat} (hb : 1 < b) (hfuel : n < b ^ (fuel + 1)) (hbn : b <= n)
  proof: by
  obtain hfuel₀ : fuel != 0 := by rintro rfl; simp [Nat.not_lt_of_le hbn] at hfuel
  rw [← Nat.pow_two]; rw [← Nat.pow_mul]
exact Nat.lt_of_lt_of_le hfuel Nat.pow_le_pow_right (by grind) (by grind)

中文:
定理 log.go_aux
  条件: {n b fuel : 自然数} (hb : 1 < b) (hfuel : n < b ^ (fuel + 1)) (hbn : b <= n)
  证明: by
  obtain hfuel₀ : fuel != 0 := by rintro rfl; simp [Nat.not_lt_of_le hbn] at hfuel
  rw [← Nat.pow_two]; rw [← Nat.pow_mul]
exact Nat.lt_of_lt_of_le hfuel Nat.pow_le_pow_right (by grind) (by grind)
-/
private theorem log.go_aux {n b fuel : Nat} (hb : 1 < b) (hfuel : n < b ^ (fuel + 1)) (hbn : b <= n) :
    n < (b * b) ^ fuel := by
  obtain hfuel₀ : fuel != 0 := by rintro rfl; simp [Nat.not_lt_of_le hbn] at hfuel
  rw [← Nat.pow_two]; rw [← Nat.pow_mul]
exact Nat.lt_of_lt_of_le hfuel Nat.pow_le_pow_right (by grind) (by grind)

/--
lemma `log.go_spec` / 引理 `log.go_spec`

English:
lemma log.go_spec
  given: {b n fuel : Nat} (hb : 1 < b) (hn : n != 0) (hfuel : n < b ^ fuel)
  proof: by
  induction fuel generalizing b with
  | zero => simp_all
  | succ fuel ih =>
    cases Nat.lt_or_ge n b with
    | inl hnb =>
      simp [go, hnb, one_le_iff_ne_zero, hn]
    | inr hnb =>
      rcases ih (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hb hb) (go_aux hb hfuel hnb)
        with ⟨ih₁, ih₂, ih₃⟩
      simp_all only [go, if_neg (Nat.not_lt_of_le hnb), ← Nat.pow_two, ← Nat.pow_mul,
        Nat.div_lt_iff_lt_mul, Nat.pow_pos (Nat.zero_lt_of_lt hb), Nat.div_div_eq_div_mul,
        ← Nat.pow_add_one, ← Nat.pow_add_one', Nat.mul_add_one]
      split <;> simp_all

中文:
引理 log.go_spec
  条件: {b n fuel : 自然数} (hb : 1 < b) (hn : n != 0) (hfuel : n < b ^ fuel)
  证明: by
  induction fuel generalizing b with
  | zero => simp_all
  | succ fuel ih =>
    cases Nat.lt_or_ge n b with
    | inl hnb =>
      simp [go, hnb, one_le_iff_ne_zero, hn]
    | inr hnb =>
      rcases ih (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hb hb) (go_aux hb hfuel hnb)
        with ⟨ih₁, ih₂, ih₃⟩
      simp_all only [go, if_neg (Nat.not_lt_of_le hnb), ← Nat.pow_two, ← Nat.pow_mul,
        Nat.div_lt_iff_lt_mul, Nat.pow_pos (Nat.zero_lt_of_lt hb), Nat.div_div_eq_div_mul,
        ← Nat.pow_add_one, ← Nat.pow_add_one', Nat.mul_add_one]
      split <;> simp_all

Depends on / 依赖: Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul, Nat.lt_or_ge, Nat.mul_add_one, Nat.mul_lt_mul_of_lt_of_lt, Nat.not_lt_of_le, Nat.one_mul, Nat.pow_add_one, Nat.pow_mul, Nat.pow_pos, Nat.pow_two, Nat.zero_lt_of_lt, div_div_eq_div_mul, div_lt_iff_lt_mul, generalizing, go_aux, if_neg, lt_or_ge, mul_add_one, mul_lt_mul_of_lt_of_lt
-/
lemma log.go_spec {b n fuel : Nat} (hb : 1 < b) (hn : n != 0) (hfuel : n < b ^ fuel) :
    (log.go n b fuel).1 = n / b ^ (log.go n b fuel).2 ∧
      b ^ (log.go n b fuel).2 <= n ∧ n < b ^ ((log.go n b fuel).2 + 1) := by
  induction fuel generalizing b with
  | zero => simp_all
  | succ fuel ih =>
    cases Nat.lt_or_ge n b with
    | inl hnb =>
      simp [go, hnb, one_le_iff_ne_zero, hn]
    | inr hnb =>
      rcases ih (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hb hb) (go_aux hb hfuel hnb)
        with ⟨ih₁, ih₂, ih₃⟩
      simp_all only [go, if_neg (Nat.not_lt_of_le hnb), ← Nat.pow_two, ← Nat.pow_mul,
        Nat.div_lt_iff_lt_mul, Nat.pow_pos (Nat.zero_lt_of_lt hb), Nat.div_div_eq_div_mul,
        ← Nat.pow_add_one, ← Nat.pow_add_one', Nat.mul_add_one]
      split <;> simp_all

/--
theorem `log_lt_iff_lt_pow` / 定理 `log_lt_iff_lt_pow`

English:
theorem log_lt_iff_lt_pow
  given: {b : Nat} (hb : 1 < b) {x y : Nat} (hy : y != 0)
  proof: by
  rcases log.go_spec hb hy (Nat.lt_pow_self hb) with ⟨-, H₁, H₂⟩
  rw [log]; rw [if_neg (Nat.not_le_of_lt hb)]
  cases Nat.lt_or_ge (log.go y b y).snd x with
  | inl h =>
exact iff_of_true h Nat.lt_of_lt_of_le H₂ Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) h
  | inr h =>
refine iff_of_false (Nat.not_lt_of_ge h) Nat.not_lt_of_ge Nat.le_trans ?_ H₁
    exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) h

@[simp]

中文:
定理 log_lt_iff_lt_pow
  条件: {b : 自然数} (hb : 1 < b) {x y : 自然数} (hy : y != 0)
  证明: by
  rcases log.go_spec hb hy (Nat.lt_pow_self hb) with ⟨-, H₁, H₂⟩
  rw [log]; rw [if_neg (Nat.not_le_of_lt hb)]
  cases Nat.lt_or_ge (log.go y b y).snd x with
  | inl h =>
exact iff_of_true h Nat.lt_of_lt_of_le H₂ Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) h
  | inr h =>
refine iff_of_false (Nat.not_lt_of_ge h) Nat.not_lt_of_ge Nat.le_trans ?_ H₁
    exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) h

@[simp]

Depends on / 依赖: Nat.le_trans, Nat.lt_of_lt_of_le, Nat.lt_or_ge, Nat.lt_pow_self, Nat.not_le_of_lt, Nat.not_lt_of_ge, Nat.pow_le_pow_right, Nat.zero_lt_of_lt, go_spec, if_neg, iff_of_false, iff_of_true, le_trans, log.go, log.go_spec, lt_of_lt_of_le, lt_or_ge, lt_pow_self, not_le_of_lt, not_lt_of_ge
-/
theorem log_lt_iff_lt_pow {b : Nat} (hb : 1 < b) {x y : Nat} (hy : y != 0) :
    log b y < x ↔ y < b ^ x := by
  rcases log.go_spec hb hy (Nat.lt_pow_self hb) with ⟨-, H₁, H₂⟩
  rw [log]; rw [if_neg (Nat.not_le_of_lt hb)]
  cases Nat.lt_or_ge (log.go y b y).snd x with
  | inl h =>
exact iff_of_true h Nat.lt_of_lt_of_le H₂ Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) h
  | inr h =>
refine iff_of_false (Nat.not_lt_of_ge h) Nat.not_lt_of_ge Nat.le_trans ?_ H₁
    exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) h

@[simp]
/--
theorem `log_eq_zero_iff` / 定理 `log_eq_zero_iff`

English:
theorem log_eq_zero_iff
  given: {b n : Nat}
  statement: log b n = 0 ↔ n < b ∨ b <= 1
  proof: by
  rcases Nat.lt_or_ge 1 b with hb | hb
  · rcases eq_or_ne n 0 with rfl | hn
    · grind [log_of_lt]
    · rw [← Nat.lt_one_iff, log_lt_iff_lt_pow hb hn, Nat.pow_one, or_iff_left (Nat.not_le_of_lt hb)]
  · simp [hb, log_of_left_le_one]

@[simp]

中文:
定理 log_eq_zero_iff
  条件: {b n : 自然数}
  结论: log b n = 0 ↔ n < b ∨ b <= 1
  证明: by
  rcases Nat.lt_or_ge 1 b with hb | hb
  · rcases eq_or_ne n 0 with rfl | hn
    · grind [log_of_lt]
    · rw [← Nat.lt_one_iff, log_lt_iff_lt_pow hb hn, Nat.pow_one, or_iff_left (Nat.not_le_of_lt hb)]
  · simp [hb, log_of_left_le_one]

@[simp]

Depends on / 依赖: Nat.lt_one_iff, Nat.lt_or_ge, Nat.not_le_of_lt, Nat.pow_one, eq_or_ne, log_lt_iff_lt_pow, log_of_left_le_one, log_of_lt, lt_one_iff, lt_or_ge, not_le_of_lt, or_iff_left, pow_one
-/
theorem log_eq_zero_iff {b n : Nat} : log b n = 0 ↔ n < b ∨ b <= 1 := by
  rcases Nat.lt_or_ge 1 b with hb | hb
  · rcases eq_or_ne n 0 with rfl | hn
    · grind [log_of_lt]
    · rw [← Nat.lt_one_iff, log_lt_iff_lt_pow hb hn, Nat.pow_one, or_iff_left (Nat.not_le_of_lt hb)]
  · simp [hb, log_of_left_le_one]

@[simp]
/--
theorem `log_pos_iff` / 定理 `log_pos_iff`

English:
theorem log_pos_iff
  given: {b n : Nat}
  statement: 0 < log b n ↔ b <= n ∧ 1 < b
  proof: by
  rw [Nat.pos_iff_ne_zero]; rw [Ne]; rw [log_eq_zero_iff]; rw [not_or]; rw [not_lt]; rw [not_le]

@[bound]

中文:
定理 log_pos_iff
  条件: {b n : 自然数}
  结论: 0 < log b n ↔ b <= n ∧ 1 < b
  证明: by
  rw [Nat.pos_iff_ne_zero]; rw [Ne]; rw [log_eq_zero_iff]; rw [not_or]; rw [not_lt]; rw [not_le]

@[bound]

Depends on / 依赖: Nat.pos_iff_ne_zero, log_eq_zero_iff, not_le, not_lt, not_or, pos_iff_ne_zero
-/
theorem log_pos_iff {b n : Nat} : 0 < log b n ↔ b <= n ∧ 1 < b := by
  rw [Nat.pos_iff_ne_zero]; rw [Ne]; rw [log_eq_zero_iff]; rw [not_or]; rw [not_lt]; rw [not_le]

@[bound]
/--
theorem `log_pos` / 定理 `log_pos`

English:
theorem log_pos
  given: {b n : Nat} (hb : 1 < b) (hbn : b <= n)
  statement: 0 < log b n
  proof: log_pos_iff.2 ⟨hbn, hb⟩

中文:
定理 log_pos
  条件: {b n : 自然数} (hb : 1 < b) (hbn : b <= n)
  结论: 0 < log b n
  证明: log_pos_iff.2 ⟨hbn, hb⟩

Depends on / 依赖: log_pos_iff
-/
theorem log_pos {b n : Nat} (hb : 1 < b) (hbn : b <= n) : 0 < log b n :=
  log_pos_iff.2 ⟨hbn, hb⟩

/--
theorem `log_of_one_lt_of_le` / 定理 `log_of_one_lt_of_le`

English:
theorem log_of_one_lt_of_le
  given: {b n : Nat} (h : 1 < b) (hn : b <= n)
  statement: log b n = log b (n / b) + 1
  proof: by
  apply eq_of_forall_gt_iff
  rintro (_ | c)
  · simp
  · have : n / b != 0 := by simp [*, Nat.ne_zero_of_lt h]
    rw [log_lt_iff_lt_pow]; rw [Nat.add_lt_add_iff_right]; rw [log_lt_iff_lt_pow]; rw [Nat.pow_add_one]; rw [Nat.div_lt_iff_lt_mul] <;> grind

中文:
定理 log_of_one_lt_of_le
  条件: {b n : 自然数} (h : 1 < b) (hn : b <= n)
  结论: log b n = log b (n / b) + 1
  证明: by
  apply eq_of_forall_gt_iff
  rintro (_ | c)
  · simp
  · have : n / b != 0 := by simp [*, Nat.ne_zero_of_lt h]
    rw [log_lt_iff_lt_pow]; rw [Nat.add_lt_add_iff_right]; rw [log_lt_iff_lt_pow]; rw [Nat.pow_add_one]; rw [Nat.div_lt_iff_lt_mul] <;> grind

Depends on / 依赖: Nat.add_lt_add_iff_right, Nat.div_lt_iff_lt_mul, Nat.ne_zero_of_lt, Nat.pow_add_one, add_lt_add_iff_right, div_lt_iff_lt_mul, eq_of_forall_gt_iff, log_lt_iff_lt_pow, ne_zero_of_lt, pow_add_one
-/
theorem log_of_one_lt_of_le {b n : Nat} (h : 1 < b) (hn : b <= n) : log b n = log b (n / b) + 1 := by
  apply eq_of_forall_gt_iff
  rintro (_ | c)
  · simp
  · have : n / b != 0 := by simp [*, Nat.ne_zero_of_lt h]
    rw [log_lt_iff_lt_pow]; rw [Nat.add_lt_add_iff_right]; rw [log_lt_iff_lt_pow]; rw [Nat.pow_add_one]; rw [Nat.div_lt_iff_lt_mul] <;> grind

/--
lemma `log_zero_left` / 引理 `log_zero_left`

English:
lemma log_zero_left
  statement: forall n, log 0 n = 0
  proof: log_of_left_le_one Nat.zero_le _

@[simp]

中文:
引理 log_zero_left
  结论: 对任意 n, log 0 n = 0
  证明: log_of_left_le_one Nat.zero_le _

@[simp]
-/
@[simp] lemma log_zero_left : forall n, log 0 n = 0 := log_of_left_le_one Nat.zero_le _

@[simp]
/--
theorem `log_zero_right` / 定理 `log_zero_right`

English:
theorem log_zero_right
  given: (b : Nat)
  statement: log b 0 = 0
  proof: log_eq_zero_iff.2 (le_total 1 b)

@[simp]

中文:
定理 log_zero_right
  条件: (b : 自然数)
  结论: log b 0 = 0
  证明: log_eq_zero_iff.2 (le_total 1 b)

@[simp]

Depends on / 依赖: le_total, log_eq_zero_iff
-/
theorem log_zero_right (b : Nat) : log b 0 = 0 :=
  log_eq_zero_iff.2 (le_total 1 b)

@[simp]
/--
theorem `log_one_left` / 定理 `log_one_left`

English:
theorem log_one_left
  statement: forall n, log 1 n = 0
  proof: log_of_left_le_one le_rfl

@[simp]

中文:
定理 log_one_left
  结论: 对任意 n, log 1 n = 0
  证明: log_of_left_le_one le_rfl

@[simp]

Depends on / 依赖: le_rfl, log_of_left_le_one
-/
theorem log_one_left : forall n, log 1 n = 0 :=
  log_of_left_le_one le_rfl

@[simp]
/--
theorem `log_one_right` / 定理 `log_one_right`

English:
theorem log_one_right
  given: (b : Nat)
  statement: log b 1 = 0
  proof: log_eq_zero_iff.2 (lt_or_ge _ _)

中文:
定理 log_one_right
  条件: (b : 自然数)
  结论: log b 1 = 0
  证明: log_eq_zero_iff.2 (lt_or_ge _ _)

Depends on / 依赖: log_eq_zero_iff, lt_or_ge
-/
theorem log_one_right (b : Nat) : log b 1 = 0 :=
  log_eq_zero_iff.2 (lt_or_ge _ _)

/--
theorem `le_log_iff_pow_le` / 定理 `le_log_iff_pow_le`

English:
theorem le_log_iff_pow_le
  given: {b : Nat} (hb : 1 < b) {x y : Nat} (hy : y != 0)
  proof: le_iff_le_iff_lt_iff_lt.mpr log_lt_iff_lt_pow hb hy

中文:
定理 le_log_iff_pow_le
  条件: {b : 自然数} (hb : 1 < b) {x y : 自然数} (hy : y != 0)
  证明: le_iff_le_iff_lt_iff_lt.mpr log_lt_iff_lt_pow hb hy

Depends on / 依赖: le_iff_le_iff_lt_iff_lt, le_iff_le_iff_lt_iff_lt.mpr, log_lt_iff_lt_pow
-/
theorem le_log_iff_pow_le {b : Nat} (hb : 1 < b) {x y : Nat} (hy : y != 0) :
    x <= log b y ↔ b ^ x <= y :=
le_iff_le_iff_lt_iff_lt.mpr log_lt_iff_lt_pow hb hy

/--
theorem `pow_le_of_le_log` / 定理 `pow_le_of_le_log`

English:
theorem pow_le_of_le_log
  given: {b x y : Nat} (hy : y != 0) (h : x <= log b y)
  statement: b ^ x <= y
  proof: by
  refine (le_or_gt b 1).elim (fun hb => ?_) fun hb => (le_log_iff_pow_le hb hy).1 h
  rw [log_of_left_le_one hb]; rw [Nat.le_zero] at h
  rwa [h, Nat.pow_zero, one_le_iff_ne_zero]

中文:
定理 pow_le_of_le_log
  条件: {b x y : 自然数} (hy : y != 0) (h : x <= log b y)
  结论: b ^ x <= y
  证明: by
  refine (le_or_gt b 1).elim (fun hb => ?_) fun hb => (le_log_iff_pow_le hb hy).1 h
  rw [log_of_left_le_one hb]; rw [Nat.le_zero] at h
  rwa [h, Nat.pow_zero, one_le_iff_ne_zero]

Depends on / 依赖: Nat.le_zero, Nat.pow_zero, le_log_iff_pow_le, le_or_gt, le_zero, log_of_left_le_one, one_le_iff_ne_zero, pow_zero
-/
theorem pow_le_of_le_log {b x y : Nat} (hy : y != 0) (h : x <= log b y) : b ^ x <= y := by
  refine (le_or_gt b 1).elim (fun hb => ?_) fun hb => (le_log_iff_pow_le hb hy).1 h
  rw [log_of_left_le_one hb]; rw [Nat.le_zero] at h
  rwa [h, Nat.pow_zero, one_le_iff_ne_zero]

/--
theorem `le_log_of_pow_le` / 定理 `le_log_of_pow_le`

English:
theorem le_log_of_pow_le
  given: {b x y : Nat} (hb : 1 < b) (h : b ^ x <= y)
  statement: x <= log b y
  proof: by
  rcases ne_or_eq y 0 with (hy | rfl)
  exacts [(le_log_iff_pow_le hb hy).2 h, (h.not_gt (Nat.pow_pos (Nat.zero_lt_one.trans hb))).elim]

中文:
定理 le_log_of_pow_le
  条件: {b x y : 自然数} (hb : 1 < b) (h : b ^ x <= y)
  结论: x <= log b y
  证明: by
  rcases ne_or_eq y 0 with (hy | rfl)
  exacts [(le_log_iff_pow_le hb hy).2 h, (h.not_gt (Nat.pow_pos (Nat.zero_lt_one.trans hb))).elim]

Depends on / 依赖: Nat.pow_pos, Nat.zero_lt_one.trans, exacts, h.not_gt, le_log_iff_pow_le, ne_or_eq, not_gt, pow_pos, zero_lt_one
-/
theorem le_log_of_pow_le {b x y : Nat} (hb : 1 < b) (h : b ^ x <= y) : x <= log b y := by
  rcases ne_or_eq y 0 with (hy | rfl)
  exacts [(le_log_iff_pow_le hb hy).2 h, (h.not_gt (Nat.pow_pos (Nat.zero_lt_one.trans hb))).elim]

/--
theorem `pow_log_le_self` / 定理 `pow_log_le_self`

English:
theorem pow_log_le_self
  given: (b : Nat) {x : Nat} (hx : x != 0)
  statement: b ^ log b x <= x
  proof: pow_le_of_le_log hx le_rfl

中文:
定理 pow_log_le_self
  条件: (b : 自然数) {x : 自然数} (hx : x != 0)
  结论: b ^ log b x <= x
  证明: pow_le_of_le_log hx le_rfl

Depends on / 依赖: le_rfl, pow_le_of_le_log
-/
theorem pow_log_le_self (b : Nat) {x : Nat} (hx : x != 0) : b ^ log b x <= x :=
  pow_le_of_le_log hx le_rfl

/--
theorem `log_lt_of_lt_pow` / 定理 `log_lt_of_lt_pow`

English:
theorem log_lt_of_lt_pow
  given: {b x y : Nat} (hy : y != 0)
  statement: y < b ^ x -> log b y < x
  proof: lt_imp_lt_of_le_imp_le (pow_le_of_le_log hy)

中文:
定理 log_lt_of_lt_pow
  条件: {b x y : 自然数} (hy : y != 0)
  结论: y < b ^ x -> log b y < x
  证明: lt_imp_lt_of_le_imp_le (pow_le_of_le_log hy)

Depends on / 依赖: lt_imp_lt_of_le_imp_le, pow_le_of_le_log
-/
theorem log_lt_of_lt_pow {b x y : Nat} (hy : y != 0) : y < b ^ x -> log b y < x :=
  lt_imp_lt_of_le_imp_le (pow_le_of_le_log hy)

/--
theorem `log_lt_of_lt_pow'` / 定理 `log_lt_of_lt_pow'`

English:
theorem log_lt_of_lt_pow'
  given: {b x y : Nat} (hx : x != 0) (hlt : y < b ^ x)
  statement: log b y < x
  proof: by
  rcases eq_or_ne y 0 with rfl | hy
  · grind [log_zero_right]
  · exact log_lt_of_lt_pow hy hlt

中文:
定理 log_lt_of_lt_pow'
  条件: {b x y : 自然数} (hx : x != 0) (hlt : y < b ^ x)
  结论: log b y < x
  证明: by
  rcases eq_or_ne y 0 with rfl | hy
  · grind [log_zero_right]
  · exact log_lt_of_lt_pow hy hlt

Depends on / 依赖: eq_or_ne, log_lt_of_lt_pow, log_zero_right
-/
theorem log_lt_of_lt_pow' {b x y : Nat} (hx : x != 0) (hlt : y < b ^ x) : log b y < x := by
  rcases eq_or_ne y 0 with rfl | hy
  · grind [log_zero_right]
  · exact log_lt_of_lt_pow hy hlt

/--
theorem `lt_pow_of_log_lt` / 定理 `lt_pow_of_log_lt`

English:
theorem lt_pow_of_log_lt
  given: {b x y : Nat} (hb : 1 < b)
  statement: log b y < x -> y < b ^ x
  proof: lt_imp_lt_of_le_imp_le (le_log_of_pow_le hb)

中文:
定理 lt_pow_of_log_lt
  条件: {b x y : 自然数} (hb : 1 < b)
  结论: log b y < x -> y < b ^ x
  证明: lt_imp_lt_of_le_imp_le (le_log_of_pow_le hb)

Depends on / 依赖: le_log_of_pow_le, lt_imp_lt_of_le_imp_le
-/
theorem lt_pow_of_log_lt {b x y : Nat} (hb : 1 < b) : log b y < x -> y < b ^ x :=
  lt_imp_lt_of_le_imp_le (le_log_of_pow_le hb)

/--
lemma `log_lt_self` / 引理 `log_lt_self`

English:
lemma log_lt_self
  given: (b : Nat) {x : Nat} (hx : x != 0)
  statement: log b x < x
  proof: match le_or_gt b 1 with
  | .inl h => log_of_left_le_one h x ▸ Nat.pos_iff_ne_zero.2 hx
| .inr h => log_lt_of_lt_pow hx Nat.lt_pow_self h

中文:
引理 log_lt_self
  条件: (b : 自然数) {x : 自然数} (hx : x != 0)
  结论: log b x < x
  证明: match le_or_gt b 1 with
  | .inl h => log_of_left_le_one h x ▸ Nat.pos_iff_ne_zero.2 hx
| .inr h => log_lt_of_lt_pow hx Nat.lt_pow_self h

Depends on / 依赖: Nat.lt_pow_self, Nat.pos_iff_ne_zero, le_or_gt, log_lt_of_lt_pow, log_of_left_le_one, lt_pow_self, pos_iff_ne_zero
-/
lemma log_lt_self (b : Nat) {x : Nat} (hx : x != 0) : log b x < x :=
  match le_or_gt b 1 with
  | .inl h => log_of_left_le_one h x ▸ Nat.pos_iff_ne_zero.2 hx
| .inr h => log_lt_of_lt_pow hx Nat.lt_pow_self h

/--
lemma `log_le_self` / 引理 `log_le_self`

English:
lemma log_le_self
  given: (b x : Nat)
  statement: log b x <= x
  proof: if hx : x = 0 then by simp [hx]
  else (log_lt_self b hx).le

中文:
引理 log_le_self
  条件: (b x : 自然数)
  结论: log b x <= x
  证明: if hx : x = 0 then by simp [hx]
  else (log_lt_self b hx).le

Depends on / 依赖: log_lt_self
-/
lemma log_le_self (b x : Nat) : log b x <= x :=
  if hx : x = 0 then by simp [hx]
  else (log_lt_self b hx).le

/--
theorem `lt_pow_succ_log_self` / 定理 `lt_pow_succ_log_self`

English:
theorem lt_pow_succ_log_self
  given: {b : Nat} (hb : 1 < b) (x : Nat)
  statement: x < b ^ (log b x).succ
  proof: lt_pow_of_log_lt hb (lt_succ_self _)

中文:
定理 lt_pow_succ_log_self
  条件: {b : 自然数} (hb : 1 < b) (x : 自然数)
  结论: x < b ^ (log b x).succ
  证明: lt_pow_of_log_lt hb (lt_succ_self _)

Depends on / 依赖: lt_pow_of_log_lt, lt_succ_self
-/
theorem lt_pow_succ_log_self {b : Nat} (hb : 1 < b) (x : Nat) : x < b ^ (log b x).succ :=
  lt_pow_of_log_lt hb (lt_succ_self _)

/--
theorem `log_eq_iff` / 定理 `log_eq_iff`

English:
theorem log_eq_iff
  given: {b m n : Nat} (h : m != 0 ∨ 1 < b ∧ n != 0)
  proof: by
  rcases em (1 < b ∧ n != 0) with (⟨hb, hn⟩ | hbn)
  · rw [le_antisymm_iff, ← Nat.lt_succ_iff, le_log_iff_pow_le, log_lt_iff_lt_pow,
      and_comm] <;> assumption
  have hm : m != 0 := h.resolve_right hbn
  rw [not_and_or]; rw [not_lt]; rw [Ne]; rw [not_not] at hbn
  rcases hbn with (hb | rfl)
  · obtain rfl | rfl := le_one_iff_eq_zero_or_eq_one.1 hb <;>
      simp only [log_zero_left, log_one_left] <;> lia
  · simp [@eq_comm _ 0, hm]

中文:
定理 log_eq_iff
  条件: {b m n : 自然数} (h : m != 0 ∨ 1 < b ∧ n != 0)
  证明: by
  rcases em (1 < b ∧ n != 0) with (⟨hb, hn⟩ | hbn)
  · rw [le_antisymm_iff, ← Nat.lt_succ_iff, le_log_iff_pow_le, log_lt_iff_lt_pow,
      and_comm] <;> assumption
  have hm : m != 0 := h.resolve_right hbn
  rw [not_and_or]; rw [not_lt]; rw [Ne]; rw [not_not] at hbn
  rcases hbn with (hb | rfl)
  · obtain rfl | rfl := le_one_iff_eq_zero_or_eq_one.1 hb <;>
      simp only [log_zero_left, log_one_left] <;> lia
  · simp [@eq_comm _ 0, hm]

Depends on / 依赖: Nat.lt_succ_iff, and_comm, eq_comm, h.resolve_right, le_antisymm_iff, le_log_iff_pow_le, le_one_iff_eq_zero_or_eq_one, log_lt_iff_lt_pow, log_one_left, log_zero_left, lt_succ_iff, not_and_or, not_lt, not_not, resolve_right
-/
theorem log_eq_iff {b m n : Nat} (h : m != 0 ∨ 1 < b ∧ n != 0) :
    log b n = m ↔ b ^ m <= n ∧ n < b ^ (m + 1) := by
  rcases em (1 < b ∧ n != 0) with (⟨hb, hn⟩ | hbn)
  · rw [le_antisymm_iff, ← Nat.lt_succ_iff, le_log_iff_pow_le, log_lt_iff_lt_pow,
      and_comm] <;> assumption
  have hm : m != 0 := h.resolve_right hbn
  rw [not_and_or]; rw [not_lt]; rw [Ne]; rw [not_not] at hbn
  rcases hbn with (hb | rfl)
  · obtain rfl | rfl := le_one_iff_eq_zero_or_eq_one.1 hb <;>
      simp only [log_zero_left, log_one_left] <;> lia
  · simp [@eq_comm _ 0, hm]

/--
theorem `log_eq_of_pow_le_of_lt_pow` / 定理 `log_eq_of_pow_le_of_lt_pow`

English:
theorem log_eq_of_pow_le_of_lt_pow
  given: {b m n : Nat} (h₁ : b ^ m <= n) (h₂ : n < b ^ (m + 1))
  proof: by
  rcases eq_or_ne m 0 with (rfl | hm)
  · rw [Nat.pow_one] at h₂
    exact log_of_lt h₂
  · exact (log_eq_iff (Or.inl hm)).2 ⟨h₁, h₂⟩

@[simp]

中文:
定理 log_eq_of_pow_le_of_lt_pow
  条件: {b m n : 自然数} (h₁ : b ^ m <= n) (h₂ : n < b ^ (m + 1))
  证明: by
  rcases eq_or_ne m 0 with (rfl | hm)
  · rw [Nat.pow_one] at h₂
    exact log_of_lt h₂
  · exact (log_eq_iff (Or.inl hm)).2 ⟨h₁, h₂⟩

@[simp]

Depends on / 依赖: Nat.pow_one, Or.inl, eq_or_ne, log_eq_iff, log_of_lt, pow_one
-/
theorem log_eq_of_pow_le_of_lt_pow {b m n : Nat} (h₁ : b ^ m <= n) (h₂ : n < b ^ (m + 1)) :
    log b n = m := by
  rcases eq_or_ne m 0 with (rfl | hm)
  · rw [Nat.pow_one] at h₂
    exact log_of_lt h₂
  · exact (log_eq_iff (Or.inl hm)).2 ⟨h₁, h₂⟩

@[simp]
/--
theorem `log_pow` / 定理 `log_pow`

English:
theorem log_pow
  given: {b : Nat} (hb : 1 < b) (x : Nat)
  statement: log b (b ^ x) = x
  proof: log_eq_of_pow_le_of_lt_pow le_rfl (Nat.pow_lt_pow_right hb x.lt_succ_self)

中文:
定理 log_pow
  条件: {b : 自然数} (hb : 1 < b) (x : 自然数)
  结论: log b (b ^ x) = x
  证明: log_eq_of_pow_le_of_lt_pow le_rfl (Nat.pow_lt_pow_right hb x.lt_succ_self)

Depends on / 依赖: Nat.pow_lt_pow_right, le_rfl, log_eq_of_pow_le_of_lt_pow, lt_succ_self, pow_lt_pow_right, x.lt_succ_self
-/
theorem log_pow {b : Nat} (hb : 1 < b) (x : Nat) : log b (b ^ x) = x :=
  log_eq_of_pow_le_of_lt_pow le_rfl (Nat.pow_lt_pow_right hb x.lt_succ_self)

/--
theorem `log_eq_one_iff'` / 定理 `log_eq_one_iff'`

English:
theorem log_eq_one_iff'
  given: {b n : Nat}
  statement: log b n = 1 ↔ b <= n ∧ n < b * b
  proof: by
  rw [log_eq_iff (Or.inl Nat.one_ne_zero)]; rw [Nat.pow_add]; rw [Nat.pow_one]

中文:
定理 log_eq_one_iff'
  条件: {b n : 自然数}
  结论: log b n = 1 ↔ b <= n ∧ n < b * b
  证明: by
  rw [log_eq_iff (Or.inl Nat.one_ne_zero)]; rw [Nat.pow_add]; rw [Nat.pow_one]

Depends on / 依赖: Nat.one_ne_zero, Nat.pow_add, Nat.pow_one, Or.inl, log_eq_iff, one_ne_zero, pow_add, pow_one
-/
theorem log_eq_one_iff' {b n : Nat} : log b n = 1 ↔ b <= n ∧ n < b * b := by
  rw [log_eq_iff (Or.inl Nat.one_ne_zero)]; rw [Nat.pow_add]; rw [Nat.pow_one]

/--
theorem `log_eq_one_iff` / 定理 `log_eq_one_iff`

English:
theorem log_eq_one_iff
  given: {b n : Nat}
  statement: log b n = 1 ↔ n < b * b ∧ 1 < b ∧ b <= n
  proof: log_eq_one_iff'.trans
    ⟨fun h => ⟨h.2, lt_mul_self_iff.1 (h.1.trans_lt h.2), h.1⟩, fun h => ⟨h.2.2, h.1⟩⟩

@[simp]

中文:
定理 log_eq_one_iff
  条件: {b n : 自然数}
  结论: log b n = 1 ↔ n < b * b ∧ 1 < b ∧ b <= n
  证明: log_eq_one_iff'.trans
    ⟨fun h => ⟨h.2, lt_mul_self_iff.1 (h.1.trans_lt h.2), h.1⟩, fun h => ⟨h.2.2, h.1⟩⟩

@[simp]

Depends on / 依赖: log_eq_one_iff, lt_mul_self_iff, trans_lt
-/
theorem log_eq_one_iff {b n : Nat} : log b n = 1 ↔ n < b * b ∧ 1 < b ∧ b <= n :=
  log_eq_one_iff'.trans
    ⟨fun h => ⟨h.2, lt_mul_self_iff.1 (h.1.trans_lt h.2), h.1⟩, fun h => ⟨h.2.2, h.1⟩⟩

@[simp]
/--
theorem `log_mul_base` / 定理 `log_mul_base`

English:
theorem log_mul_base
  given: {b n : Nat} (hb : 1 < b) (hn : n != 0)
  statement: log b (n * b) = log b n + 1
  proof: by
  apply log_eq_of_pow_le_of_lt_pow <;> rw [pow_succ', Nat.mul_comm b]
  exacts [Nat.mul_le_mul_right _ (pow_log_le_self _ hn),
    (Nat.mul_lt_mul_right (Nat.zero_lt_one.trans hb)).2 (lt_pow_succ_log_self hb _)]

中文:
定理 log_mul_base
  条件: {b n : 自然数} (hb : 1 < b) (hn : n != 0)
  结论: log b (n * b) = log b n + 1
  证明: by
  apply log_eq_of_pow_le_of_lt_pow <;> rw [pow_succ', Nat.mul_comm b]
  exacts [Nat.mul_le_mul_right _ (pow_log_le_self _ hn),
    (Nat.mul_lt_mul_right (Nat.zero_lt_one.trans hb)).2 (lt_pow_succ_log_self hb _)]

Depends on / 依赖: Nat.mul_comm, Nat.mul_le_mul_right, Nat.mul_lt_mul_right, Nat.zero_lt_one.trans, exacts, log_eq_of_pow_le_of_lt_pow, lt_pow_succ_log_self, mul_comm, mul_le_mul_right, mul_lt_mul_right, pow_log_le_self, pow_succ, zero_lt_one
-/
theorem log_mul_base {b n : Nat} (hb : 1 < b) (hn : n != 0) : log b (n * b) = log b n + 1 := by
  apply log_eq_of_pow_le_of_lt_pow <;> rw [pow_succ', Nat.mul_comm b]
  exacts [Nat.mul_le_mul_right _ (pow_log_le_self _ hn),
    (Nat.mul_lt_mul_right (Nat.zero_lt_one.trans hb)).2 (lt_pow_succ_log_self hb _)]

/--
theorem `pow_log_le_add_one` / 定理 `pow_log_le_add_one`

English:
theorem pow_log_le_add_one
  given: (b : Nat)
  statement: forall x, b ^ log b x <= x + 1

中文:
定理 pow_log_le_add_one
  条件: (b : 自然数)
  结论: 对任意 x, b ^ log b x <= x + 1
-/
theorem pow_log_le_add_one (b : Nat) : forall x, b ^ log b x <= x + 1
  | 0 => by rw [log_zero_right, Nat.pow_zero]
  | x + 1 => (pow_log_le_self b x.succ_ne_zero).trans (x + 1).le_succ

/--
theorem `log_monotone` / 定理 `log_monotone`

English:
theorem log_monotone
  given: {b : Nat}
  statement: Monotone (log b)
  proof: by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb]
    exact zero_le _
  · exact le_log_of_pow_le hb (pow_log_le_add_one _ _)

@[mono, gcongr]

中文:
定理 log_monotone
  条件: {b : 自然数}
  结论: 递增 (log b)
  证明: by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb]
    exact zero_le _
  · exact le_log_of_pow_le hb (pow_log_le_add_one _ _)

@[mono, gcongr]

Depends on / 依赖: le_log_of_pow_le, le_or_gt, log_of_left_le_one, monotone_nat_of_le_succ, pow_log_le_add_one, zero_le
-/
theorem log_monotone {b : Nat} : Monotone (log b) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb]
    exact zero_le _
  · exact le_log_of_pow_le hb (pow_log_le_add_one _ _)

@[mono, gcongr]
/--
theorem `log_mono_right` / 定理 `log_mono_right`

English:
theorem log_mono_right
  given: {b n m : Nat} (h : n <= m)
  statement: log b n <= log b m
  proof: log_monotone h

中文:
定理 log_mono_right
  条件: {b n m : 自然数} (h : n <= m)
  结论: log b n <= log b m
  证明: log_monotone h

Depends on / 依赖: log_monotone
-/
theorem log_mono_right {b n m : Nat} (h : n <= m) : log b n <= log b m :=
  log_monotone h

/--
theorem `log_lt_log_succ_iff` / 定理 `log_lt_log_succ_iff`

English:
theorem log_lt_log_succ_iff
  given: {b n : Nat} (hb : 1 < b) (hn : n != 0)
  proof: by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · apply le_antisymm _ (Nat.lt_pow_of_log_lt hb H)
    exact Nat.pow_log_le_self b (Ne.symm (Nat.zero_ne_add_one n))
  · apply Nat.log_lt_of_lt_pow hn
    simp [H]

中文:
定理 log_lt_log_succ_iff
  条件: {b n : 自然数} (hb : 1 < b) (hn : n != 0)
  证明: by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · apply le_antisymm _ (Nat.lt_pow_of_log_lt hb H)
    exact Nat.pow_log_le_self b (Ne.symm (Nat.zero_ne_add_one n))
  · apply Nat.log_lt_of_lt_pow hn
    simp [H]

Depends on / 依赖: Nat.log_lt_of_lt_pow, Nat.lt_pow_of_log_lt, Nat.pow_log_le_self, Nat.zero_ne_add_one, Ne.symm, le_antisymm, log_lt_of_lt_pow, lt_pow_of_log_lt, pow_log_le_self, zero_ne_add_one
-/
theorem log_lt_log_succ_iff {b n : Nat} (hb : 1 < b) (hn : n != 0) :
    log b n < log b (n + 1) ↔ b ^ log b (n + 1) = n + 1 := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · apply le_antisymm _ (Nat.lt_pow_of_log_lt hb H)
    exact Nat.pow_log_le_self b (Ne.symm (Nat.zero_ne_add_one n))
  · apply Nat.log_lt_of_lt_pow hn
    simp [H]

/--
theorem `log_eq_log_succ_iff` / 定理 `log_eq_log_succ_iff`

English:
theorem log_eq_log_succ_iff
  given: {b n : Nat} (hb : 1 < b) (hn : n != 0)
  proof: by
  rw [ne_eq]; rw [← log_lt_log_succ_iff hb hn]; rw [not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun _ => log_monotone (le_add_right n 1)

中文:
定理 log_eq_log_succ_iff
  条件: {b n : 自然数} (hb : 1 < b) (hn : n != 0)
  证明: by
  rw [ne_eq]; rw [← log_lt_log_succ_iff hb hn]; rw [not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun _ => log_monotone (le_add_right n 1)

Depends on / 依赖: and_iff_right_iff_imp, le_add_right, le_antisymm_iff, log_lt_log_succ_iff, log_monotone, ne_eq, not_lt
-/
theorem log_eq_log_succ_iff {b n : Nat} (hb : 1 < b) (hn : n != 0) :
    log b n = log b (n + 1) ↔ b ^ log b (n + 1) != n + 1 := by
  rw [ne_eq]; rw [← log_lt_log_succ_iff hb hn]; rw [not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun _ => log_monotone (le_add_right n 1)

/--
theorem `log_anti_left` / 定理 `log_anti_left`

English:
theorem log_anti_left
  given: {b c n : Nat} (hc : 1 < c) (hb : c <= b)
  statement: log b n <= log c n
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn); · rw [log_zero_right, log_zero_right]
  apply le_log_of_pow_le hc
  calc
    c ^ log b n <= b ^ log b n := Nat.pow_le_pow_left hb _
    _ <= n := pow_log_le_self _ hn

中文:
定理 log_anti_left
  条件: {b c n : 自然数} (hc : 1 < c) (hb : c <= b)
  结论: log b n <= log c n
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn); · rw [log_zero_right, log_zero_right]
  apply le_log_of_pow_le hc
  calc
    c ^ log b n <= b ^ log b n := Nat.pow_le_pow_left hb _
    _ <= n := pow_log_le_self _ hn

Depends on / 依赖: Nat.pow_le_pow_left, eq_or_ne, le_log_of_pow_le, log_zero_right, pow_le_pow_left, pow_log_le_self
-/
theorem log_anti_left {b c n : Nat} (hc : 1 < c) (hb : c <= b) : log b n <= log c n := by
  rcases eq_or_ne n 0 with (rfl | hn); · rw [log_zero_right, log_zero_right]
  apply le_log_of_pow_le hc
  calc
    c ^ log b n <= b ^ log b n := Nat.pow_le_pow_left hb _
    _ <= n := pow_log_le_self _ hn

/--
theorem `log_antitone_left` / 定理 `log_antitone_left`

English:
theorem log_antitone_left
  given: {n : Nat}
  statement: AntitoneOn (fun b => log b n) (Set.Ioi 1)
  proof: fun _ hc _ _ hb =>
  log_anti_left (Set.mem_Iio.1 hc) hb

@[gcongr, mono]

中文:
定理 log_antitone_left
  条件: {n : 自然数}
  结论: AntitoneOn (fun b => log b n) (集合.左开右无界区间 1)
  证明: fun _ hc _ _ hb =>
  log_anti_left (Set.mem_Iio.1 hc) hb

@[gcongr, mono]
-/
theorem log_antitone_left {n : Nat} : AntitoneOn (fun b => log b n) (Set.Ioi 1) := fun _ hc _ _ hb =>
  log_anti_left (Set.mem_Iio.1 hc) hb

@[gcongr, mono]
/--
theorem `log_mono` / 定理 `log_mono`

English:
theorem log_mono
  given: {b c m n : Nat} (hc : 1 < c) (hb : c <= b) (hmn : m <= n)
  proof: (log_anti_left hc hb).trans by gcongr

@[simp]

中文:
定理 log_mono
  条件: {b c m n : 自然数} (hc : 1 < c) (hb : c <= b) (hmn : m <= n)
  证明: (log_anti_left hc hb).trans by gcongr

@[simp]

Depends on / 依赖: log_anti_left
-/
theorem log_mono {b c m n : Nat} (hc : 1 < c) (hb : c <= b) (hmn : m <= n) :
    log b m <= log c n :=
(log_anti_left hc hb).trans by gcongr

@[simp]
/--
theorem `log_div_base` / 定理 `log_div_base`

English:
theorem log_div_base
  given: (b n : Nat)
  statement: log b (n / b) = log b n - 1
  proof: by
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb, Nat.zero_sub]
  rcases lt_or_ge n b with h | h
  · rw [div_eq_of_lt h, log_of_lt h, log_zero_right]
  rw [log_of_one_lt_of_le hb h]; rw [Nat.add_sub_cancel_right]

中文:
定理 log_div_base
  条件: (b n : 自然数)
  结论: log b (n / b) = log b n - 1
  证明: by
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb, Nat.zero_sub]
  rcases lt_or_ge n b with h | h
  · rw [div_eq_of_lt h, log_of_lt h, log_zero_right]
  rw [log_of_one_lt_of_le hb h]; rw [Nat.add_sub_cancel_right]

Depends on / 依赖: Nat.add_sub_cancel_right, Nat.zero_sub, add_sub_cancel_right, div_eq_of_lt, le_or_gt, log_of_left_le_one, log_of_lt, log_of_one_lt_of_le, log_zero_right, lt_or_ge, zero_sub
-/
theorem log_div_base (b n : Nat) : log b (n / b) = log b n - 1 := by
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb, Nat.zero_sub]
  rcases lt_or_ge n b with h | h
  · rw [div_eq_of_lt h, log_of_lt h, log_zero_right]
  rw [log_of_one_lt_of_le hb h]; rw [Nat.add_sub_cancel_right]

/--
lemma `log_div_base_pow` / 引理 `log_div_base_pow`

English:
lemma log_div_base_pow
  given: (b n k : Nat)
  statement: log b (n / b ^ k) = log b n - k
  proof: by
  induction k with
  | zero => grind
  | succ k hk => rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, log_div_base, hk, sub_add_eq]

@[simp]

中文:
引理 log_div_base_pow
  条件: (b n k : 自然数)
  结论: log b (n / b ^ k) = log b n - k
  证明: by
  induction k with
  | zero => grind
  | succ k hk => rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, log_div_base, hk, sub_add_eq]

@[simp]

Depends on / 依赖: Nat.div_div_eq_div_mul, Nat.pow_succ, div_div_eq_div_mul, log_div_base, pow_succ, sub_add_eq
-/
lemma log_div_base_pow (b n k : Nat) : log b (n / b ^ k) = log b n - k := by
  induction k with
  | zero => grind
  | succ k hk => rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, log_div_base, hk, sub_add_eq]

@[simp]
/--
theorem `log_div_mul_self` / 定理 `log_div_mul_self`

English:
theorem log_div_mul_self
  given: (b n : Nat)
  statement: log b (n / b * b) = log b n
  proof: by
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb]
  rcases lt_or_ge n b with h | h
  · rw [div_eq_of_lt h, Nat.zero_mul, log_zero_right, log_of_lt h]
  rw [log_mul_base hb (Nat.div_pos h (by lia)).ne']; rw [log_div_base]; rw [Nat.sub_add_cancel (succ_le_iff.2 <| log_pos hb h)]

中文:
定理 log_div_mul_self
  条件: (b n : 自然数)
  结论: log b (n / b * b) = log b n
  证明: by
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb]
  rcases lt_or_ge n b with h | h
  · rw [div_eq_of_lt h, Nat.zero_mul, log_zero_right, log_of_lt h]
  rw [log_mul_base hb (Nat.div_pos h (by lia)).ne']; rw [log_div_base]; rw [Nat.sub_add_cancel (succ_le_iff.2 <| log_pos hb h)]

Depends on / 依赖: Nat.div_pos, Nat.sub_add_cancel, Nat.zero_mul, div_eq_of_lt, div_pos, le_or_gt, log_div_base, log_mul_base, log_of_left_le_one, log_of_lt, log_pos, log_zero_right, lt_or_ge, sub_add_cancel, succ_le_iff, zero_mul
-/
theorem log_div_mul_self (b n : Nat) : log b (n / b * b) = log b n := by
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb]
  rcases lt_or_ge n b with h | h
  · rw [div_eq_of_lt h, Nat.zero_mul, log_zero_right, log_of_lt h]
  rw [log_mul_base hb (Nat.div_pos h (by lia)).ne']; rw [log_div_base]; rw [Nat.sub_add_cancel (succ_le_iff.2 <| log_pos hb h)]

/--
theorem `add_pred_div_lt` / 定理 `add_pred_div_lt`

English:
theorem add_pred_div_lt
  given: {b n : Nat} (hb : 1 < b) (hn : 2 <= n)
  statement: (n + b - 1) / b < n
  proof: by
  rw [div_lt_iff_lt_mul (by lia)]; rw [← succ_le_iff]; rw [← pred_eq_sub_one]; rw [succ_pred_eq_of_pos (by lia)]
  exact Nat.add_le_mul hn hb

中文:
定理 add_pred_div_lt
  条件: {b n : 自然数} (hb : 1 < b) (hn : 2 <= n)
  结论: (n + b - 1) / b < n
  证明: by
  rw [div_lt_iff_lt_mul (by lia)]; rw [← succ_le_iff]; rw [← pred_eq_sub_one]; rw [succ_pred_eq_of_pos (by lia)]
  exact Nat.add_le_mul hn hb

Depends on / 依赖: Nat.add_le_mul, add_le_mul, div_lt_iff_lt_mul, pred_eq_sub_one, succ_le_iff, succ_pred_eq_of_pos
-/
theorem add_pred_div_lt {b n : Nat} (hb : 1 < b) (hn : 2 <= n) : (n + b - 1) / b < n := by
  rw [div_lt_iff_lt_mul (by lia)]; rw [← succ_le_iff]; rw [← pred_eq_sub_one]; rw [succ_pred_eq_of_pos (by lia)]
  exact Nat.add_le_mul hn hb

/--
lemma `log_two_bit` / 引理 `log_two_bit`

English:
lemma log_two_bit
  given: {b n} (hn : n != 0)
  statement: Nat.log 2 (n.bit b) = Nat.log 2 n + 1
  proof: by
  rw [← log_div_mul_self]; rw [bit_div_two]; rw [log_mul_base Nat.one_lt_two hn]

中文:
引理 log_two_bit
  条件: {b n} (hn : n != 0)
  结论: 自然数.log 2 (n.bit b) = 自然数.log 2 n + 1
  证明: by
  rw [← log_div_mul_self]; rw [bit_div_two]; rw [log_mul_base Nat.one_lt_two hn]

Depends on / 依赖: Nat.one_lt_two, bit_div_two, log_div_mul_self, log_mul_base, one_lt_two
-/
lemma log_two_bit {b n} (hn : n != 0) : Nat.log 2 (n.bit b) = Nat.log 2 n + 1 := by
  rw [← log_div_mul_self]; rw [bit_div_two]; rw [log_mul_base Nat.one_lt_two hn]

/--
lemma `log2_eq_log_two` / 引理 `log2_eq_log_two`

English:
lemma log2_eq_log_two
  given: {n : Nat}
  statement: Nat.log2 n = Nat.log 2 n
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [log2_zero, log_zero_right]
  apply eq_of_forall_le_iff
  intro m
  rw [Nat.le_log2 hn]; rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn]

@[simp]

中文:
引理 log2_eq_log_two
  条件: {n : 自然数}
  结论: 自然数.log2 n = 自然数.log 2 n
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [log2_zero, log_zero_right]
  apply eq_of_forall_le_iff
  intro m
  rw [Nat.le_log2 hn]; rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn]

@[simp]

Depends on / 依赖: Nat.le_log2, Nat.le_log_iff_pow_le, Nat.one_lt_two, eq_of_forall_le_iff, eq_or_ne, le_log2, le_log_iff_pow_le, log2_zero, log_zero_right, one_lt_two
-/
lemma log2_eq_log_two {n : Nat} : Nat.log2 n = Nat.log 2 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [log2_zero, log_zero_right]
  apply eq_of_forall_le_iff
  intro m
  rw [Nat.le_log2 hn]; rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn]

@[simp]
/--
lemma `log_pow_left` / 引理 `log_pow_left`

English:
lemma log_pow_left
  given: (b k n : Nat)
  statement: log (b ^ k) n = log b n / k
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rcases k.eq_zero_or_pos with rfl | hk
    · simp
    · rcases Nat.lt_or_ge 1 b with hb | hb
      · refine eq_of_forall_le_iff fun c => ?_
        rw [le_log_iff_pow_le (Nat.one_lt_pow (Nat.ne_of_gt hk) hb) hn]; rw [Nat.le_div_iff_mul_le hk]; rw [le_log_iff_pow_le hb hn]; rw [Nat.pow_mul']
      · rw [log_of_left_le_one hb, Nat.zero_div, log_of_left_le_one]
        rwa [Nat.pow_le_one_iff (Nat.ne_of_gt hk)]

中文:
引理 log_pow_left
  条件: (b k n : 自然数)
  结论: log (b ^ k) n = log b n / k
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rcases k.eq_zero_or_pos with rfl | hk
    · simp
    · rcases Nat.lt_or_ge 1 b with hb | hb
      · refine eq_of_forall_le_iff fun c => ?_
        rw [le_log_iff_pow_le (Nat.one_lt_pow (Nat.ne_of_gt hk) hb) hn]; rw [Nat.le_div_iff_mul_le hk]; rw [le_log_iff_pow_le hb hn]; rw [Nat.pow_mul']
      · rw [log_of_left_le_one hb, Nat.zero_div, log_of_left_le_one]
        rwa [Nat.pow_le_one_iff (Nat.ne_of_gt hk)]

Depends on / 依赖: Nat.le_div_iff_mul_le, Nat.lt_or_ge, Nat.ne_of_gt, Nat.one_lt_pow, Nat.pow_le_one_iff, Nat.pow_mul, Nat.zero_div, eq_of_forall_le_iff, eq_or_ne, eq_zero_or_pos, k.eq_zero_or_pos, le_div_iff_mul_le, le_log_iff_pow_le, log_of_left_le_one, lt_or_ge, ne_of_gt, one_lt_pow, pow_le_one_iff, pow_mul, zero_div
-/
lemma log_pow_left (b k n : Nat) : log (b ^ k) n = log b n / k := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rcases k.eq_zero_or_pos with rfl | hk
    · simp
    · rcases Nat.lt_or_ge 1 b with hb | hb
      · refine eq_of_forall_le_iff fun c => ?_
        rw [le_log_iff_pow_le (Nat.one_lt_pow (Nat.ne_of_gt hk) hb) hn]; rw [Nat.le_div_iff_mul_le hk]; rw [le_log_iff_pow_le hb hn]; rw [Nat.pow_mul']
      · rw [log_of_left_le_one hb, Nat.zero_div, log_of_left_le_one]
        rwa [Nat.pow_le_one_iff (Nat.ne_of_gt hk)]

/-! ### Ceil logarithm -/


/-- `clog b n`, is the upper logarithm of natural number `n` in base `b`. It returns the smallest
`k : ℕ` such that `n ≤ b^k`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot]
/--
Definition of `clog` / `clog` 的定义

English:
definition clog
  signature: (b n : Nat)
  body: if 1 < b ∧ 1 < n then (go b n).2 + 1 else 0 where
  /-- An auxiliary definition for `Nat.clog`.

  For `n > 1`, `b > 1`, `n ≤ b ^ fuel`, returns `(b ^ clog b n / n, clog b n - 1)`.
  -/
  go : Nat -> Nat -> Nat × Nat
  | b, 0 => (b / n, 0)
  | b, fuel + 1 =>
    if n <= b then (b / n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e + 1) else (q / b, 2 * e)

中文:
定义 clog
  签名: (b n : 自然数)
  定义体: if 1 < b ∧ 1 < n then (go b n).2 + 1 else 0 where
  /-- An auxiliary definition for `Nat.clog`.

  For `n > 1`, `b > 1`, `n ≤ b ^ fuel`, returns `(b ^ clog b n / n, clog b n - 1)`.
  -/
  go : Nat -> Nat -> Nat × Nat
  | b, 0 => (b / n, 0)
  | b, fuel + 1 =>
    if n <= b then (b / n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e + 1) else (q / b, 2 * e)
-/
def clog (b n : Nat) : Nat :=
  if 1 < b ∧ 1 < n then (go b n).2 + 1 else 0 where
  /-- An auxiliary definition for `Nat.clog`.

  For `n > 1`, `b > 1`, `n ≤ b ^ fuel`, returns `(b ^ clog b n / n, clog b n - 1)`.
  -/
  go : Nat -> Nat -> Nat × Nat
  | b, 0 => (b / n, 0)
  | b, fuel + 1 =>
    if n <= b then (b / n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e + 1) else (q / b, 2 * e)

/--
theorem `clog_of_left_le_one` / 定理 `clog_of_left_le_one`

English:
theorem clog_of_left_le_one
  given: {b : Nat} (hb : b <= 1) (n : Nat)
  statement: clog b n = 0
  proof: by
  grind [clog]

中文:
定理 clog_of_left_le_one
  条件: {b : 自然数} (hb : b <= 1) (n : 自然数)
  结论: clog b n = 0
  证明: by
  grind [clog]
-/
theorem clog_of_left_le_one {b : Nat} (hb : b <= 1) (n : Nat) : clog b n = 0 := by
  grind [clog]

/--
theorem `clog_of_right_le_one` / 定理 `clog_of_right_le_one`

English:
theorem clog_of_right_le_one
  given: {n : Nat} (hn : n <= 1) (b : Nat)
  statement: clog b n = 0
  proof: by
  grind [clog]

中文:
定理 clog_of_right_le_one
  条件: {n : 自然数} (hn : n <= 1) (b : 自然数)
  结论: clog b n = 0
  证明: by
  grind [clog]
-/
theorem clog_of_right_le_one {n : Nat} (hn : n <= 1) (b : Nat) : clog b n = 0 := by
  grind [clog]

/--
lemma `clog_zero_left` / 引理 `clog_zero_left`

English:
lemma clog_zero_left
  given: (n : Nat)
  statement: clog 0 n = 0
  proof: clog_of_left_le_one (Nat.zero_le _) _

中文:
引理 clog_zero_left
  条件: (n : 自然数)
  结论: clog 0 n = 0
  证明: clog_of_left_le_one (Nat.zero_le _) _
-/
@[simp] lemma clog_zero_left (n : Nat) : clog 0 n = 0 := clog_of_left_le_one (Nat.zero_le _) _

/--
lemma `clog_zero_right` / 引理 `clog_zero_right`

English:
lemma clog_zero_right
  given: (b : Nat)
  statement: clog b 0 = 0
  proof: clog_of_right_le_one (Nat.zero_le _) _

@[simp]

中文:
引理 clog_zero_right
  条件: (b : 自然数)
  结论: clog b 0 = 0
  证明: clog_of_right_le_one (Nat.zero_le _) _

@[simp]
-/
@[simp] lemma clog_zero_right (b : Nat) : clog b 0 = 0 := clog_of_right_le_one (Nat.zero_le _) _

@[simp]
/--
theorem `clog_one_left` / 定理 `clog_one_left`

English:
theorem clog_one_left
  given: (n : Nat)
  statement: clog 1 n = 0
  proof: clog_of_left_le_one le_rfl _

@[simp]

中文:
定理 clog_one_left
  条件: (n : 自然数)
  结论: clog 1 n = 0
  证明: clog_of_left_le_one le_rfl _

@[simp]

Depends on / 依赖: clog_of_left_le_one, le_rfl
-/
theorem clog_one_left (n : Nat) : clog 1 n = 0 :=
  clog_of_left_le_one le_rfl _

@[simp]
/--
theorem `clog_one_right` / 定理 `clog_one_right`

English:
theorem clog_one_right
  given: (b : Nat)
  statement: clog b 1 = 0
  proof: clog_of_right_le_one le_rfl _

中文:
定理 clog_one_right
  条件: (b : 自然数)
  结论: clog b 1 = 0
  证明: clog_of_right_le_one le_rfl _

Depends on / 依赖: clog_of_right_le_one, le_rfl
-/
theorem clog_one_right (b : Nat) : clog b 1 = 0 :=
  clog_of_right_le_one le_rfl _

/--
theorem `clog.go_spec` / 定理 `clog.go_spec`

English:
theorem clog.go_spec
  given: {n b fuel} (hn : 1 < n) (hb : 1 < b) (hfuel : n < b ^ fuel)
  proof: by
  induction fuel generalizing b with
  | zero => simp_all
  | succ fuel ih =>
    cases Nat.lt_or_ge b n with
    | inr hbn => simp_all [go]
    | inl hbn =>
      rcases ih (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hb hb)
        (log.go_aux hb hfuel (Nat.le_of_lt hbn)) with ⟨ih₁, ih₂, ih₃⟩
      simp_all only [go, if_neg (Nat.not_le_of_gt hbn), ← Nat.pow_two, ← Nat.pow_mul,
        Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hbn), Nat.div_div_eq_div_mul,
        Nat.mul_comm n b, Nat.mul_add_one, @Nat.pow_add_one' _ (2 * _ + 1),
        Nat.mul_lt_mul_left, Nat.mul_div_mul_left, Nat.zero_lt_of_lt hb]
      split <;> simp_all [Nat.mul_add_one, Nat.pow_add_one']

中文:
定理 clog.go_spec
  条件: {n b fuel} (hn : 1 < n) (hb : 1 < b) (hfuel : n < b ^ fuel)
  证明: by
  induction fuel generalizing b with
  | zero => simp_all
  | succ fuel ih =>
    cases Nat.lt_or_ge b n with
    | inr hbn => simp_all [go]
    | inl hbn =>
      rcases ih (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hb hb)
        (log.go_aux hb hfuel (Nat.le_of_lt hbn)) with ⟨ih₁, ih₂, ih₃⟩
      simp_all only [go, if_neg (Nat.not_le_of_gt hbn), ← Nat.pow_two, ← Nat.pow_mul,
        Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hbn), Nat.div_div_eq_div_mul,
        Nat.mul_comm n b, Nat.mul_add_one, @Nat.pow_add_one' _ (2 * _ + 1),
        Nat.mul_lt_mul_left, Nat.mul_div_mul_left, Nat.zero_lt_of_lt hb]
      split <;> simp_all [Nat.mul_add_one, Nat.pow_add_one']

Depends on / 依赖: Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul, Nat.le_of_lt, Nat.lt_or_ge, Nat.mul_add_one, Nat.mul_comm, Nat.mul_lt_mul_, Nat.mul_lt_mul_of_lt_of_lt, Nat.not_le_of_gt, Nat.one_mul, Nat.pow_add_one, Nat.pow_mul, Nat.pow_two, Nat.zero_lt_of_lt, div_div_eq_div_mul, div_lt_iff_lt_mul, generalizing, go_aux, if_neg, le_of_lt
-/
theorem clog.go_spec {n b fuel} (hn : 1 < n) (hb : 1 < b) (hfuel : n < b ^ fuel) :
    (go n b fuel).1 = b ^ ((go n b fuel).2 + 1) / n ∧
      b ^ (go n b fuel).2 < n ∧ n <= b ^ ((go n b fuel).2 + 1) := by
  induction fuel generalizing b with
  | zero => simp_all
  | succ fuel ih =>
    cases Nat.lt_or_ge b n with
    | inr hbn => simp_all [go]
    | inl hbn =>
      rcases ih (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hb hb)
        (log.go_aux hb hfuel (Nat.le_of_lt hbn)) with ⟨ih₁, ih₂, ih₃⟩
      simp_all only [go, if_neg (Nat.not_le_of_gt hbn), ← Nat.pow_two, ← Nat.pow_mul,
        Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hbn), Nat.div_div_eq_div_mul,
        Nat.mul_comm n b, Nat.mul_add_one, @Nat.pow_add_one' _ (2 * _ + 1),
        Nat.mul_lt_mul_left, Nat.mul_div_mul_left, Nat.zero_lt_of_lt hb]
      split <;> simp_all [Nat.mul_add_one, Nat.pow_add_one']

/--
theorem `clog_le_iff_le_pow` / 定理 `clog_le_iff_le_pow`

English:
theorem clog_le_iff_le_pow
  given: {b : Nat} (hb : 1 < b) {x y : Nat}
  statement: clog b x <= y ↔ x <= b ^ y
  proof: by
  fun_cases clog with
  | case1 h =>
    rcases clog.go_spec h.2 hb (Nat.lt_pow_self hb) with ⟨-, H₁, H₂⟩
    cases Nat.lt_or_ge (clog.go x b x).2 y with
    | inl hy =>
      rw [← Nat.add_one_le_iff] at hy
exact iff_of_true hy Nat.le_trans H₂ Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) hy
    | inr hy =>
      apply_rules [iff_of_false, Nat.not_le_of_gt, Nat.lt_add_one_of_le]
      exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) hy) H₁
  | case2 h => grind [Nat.one_le_pow]

中文:
定理 clog_le_iff_le_pow
  条件: {b : 自然数} (hb : 1 < b) {x y : 自然数}
  结论: clog b x <= y ↔ x <= b ^ y
  证明: by
  fun_cases clog with
  | case1 h =>
    rcases clog.go_spec h.2 hb (Nat.lt_pow_self hb) with ⟨-, H₁, H₂⟩
    cases Nat.lt_or_ge (clog.go x b x).2 y with
    | inl hy =>
      rw [← Nat.add_one_le_iff] at hy
exact iff_of_true hy Nat.le_trans H₂ Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) hy
    | inr hy =>
      apply_rules [iff_of_false, Nat.not_le_of_gt, Nat.lt_add_one_of_le]
      exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) hy) H₁
  | case2 h => grind [Nat.one_le_pow]

Depends on / 依赖: Nat.add_one_le_iff, Nat.le_trans, Nat.lt_add_one_of_le, Nat.lt_of_le_of_lt, Nat.lt_or_ge, Nat.lt_pow_self, Nat.not_le_of_gt, Nat.one_le_pow, Nat.pow_le_pow_right, Nat.zero_lt_of_lt, add_one_le_iff, apply_rules, clog.go, clog.go_spec, fun_cases, go_spec, iff_of_false, iff_of_true, le_trans, lt_add_one_of_le
-/
theorem clog_le_iff_le_pow {b : Nat} (hb : 1 < b) {x y : Nat} : clog b x <= y ↔ x <= b ^ y := by
  fun_cases clog with
  | case1 h =>
    rcases clog.go_spec h.2 hb (Nat.lt_pow_self hb) with ⟨-, H₁, H₂⟩
    cases Nat.lt_or_ge (clog.go x b x).2 y with
    | inl hy =>
      rw [← Nat.add_one_le_iff] at hy
exact iff_of_true hy Nat.le_trans H₂ Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) hy
    | inr hy =>
      apply_rules [iff_of_false, Nat.not_le_of_gt, Nat.lt_add_one_of_le]
      exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) hy) H₁
  | case2 h => grind [Nat.one_le_pow]

/--
theorem `clog_pos` / 定理 `clog_pos`

English:
theorem clog_pos
  given: {b n : Nat} (hb : 1 < b) (hn : 1 < n)
  statement: 0 < clog b n
  proof: by
  rw [clog]; rw [if_pos]
  exacts [Nat.succ_pos _, ⟨hb, hn⟩]

中文:
定理 clog_pos
  条件: {b n : 自然数} (hb : 1 < b) (hn : 1 < n)
  结论: 0 < clog b n
  证明: by
  rw [clog]; rw [if_pos]
  exacts [Nat.succ_pos _, ⟨hb, hn⟩]

Depends on / 依赖: Nat.succ_pos, exacts, if_pos, succ_pos
-/
theorem clog_pos {b n : Nat} (hb : 1 < b) (hn : 1 < n) : 0 < clog b n := by
  rw [clog]; rw [if_pos]
  exacts [Nat.succ_pos _, ⟨hb, hn⟩]

/--
theorem `clog_of_one_lt` / 定理 `clog_of_one_lt`

English:
theorem clog_of_one_lt
  given: {b n : Nat} (hb : 1 < b) (hn : 1 < n)
  proof: by
  apply eq_of_forall_ge_iff
  rintro (_ | c)
  · simp [Nat.ne_of_gt <| clog_pos hb hn]
  · simp only [clog_le_iff_le_pow, Nat.pow_add_one, Nat.add_le_add_iff_right, Nat.zero_lt_of_lt hb,
      div_le_iff_le_mul, hb]
    grind

中文:
定理 clog_of_one_lt
  条件: {b n : 自然数} (hb : 1 < b) (hn : 1 < n)
  证明: by
  apply eq_of_forall_ge_iff
  rintro (_ | c)
  · simp [Nat.ne_of_gt <| clog_pos hb hn]
  · simp only [clog_le_iff_le_pow, Nat.pow_add_one, Nat.add_le_add_iff_right, Nat.zero_lt_of_lt hb,
      div_le_iff_le_mul, hb]
    grind

Depends on / 依赖: Nat.add_le_add_iff_right, Nat.ne_of_gt, Nat.pow_add_one, Nat.zero_lt_of_lt, add_le_add_iff_right, clog_le_iff_le_pow, clog_pos, div_le_iff_le_mul, eq_of_forall_ge_iff, ne_of_gt, pow_add_one, zero_lt_of_lt
-/
theorem clog_of_one_lt {b n : Nat} (hb : 1 < b) (hn : 1 < n) :
    clog b n = clog b ((n + b - 1) / b) + 1 := by
  apply eq_of_forall_ge_iff
  rintro (_ | c)
  · simp [Nat.ne_of_gt <| clog_pos hb hn]
  · simp only [clog_le_iff_le_pow, Nat.pow_add_one, Nat.add_le_add_iff_right, Nat.zero_lt_of_lt hb,
      div_le_iff_le_mul, hb]
    grind

/--
theorem `clog_of_two_le` / 定理 `clog_of_two_le`

English:
theorem clog_of_two_le
  given: {b n : Nat} (hb : 1 < b) (hn : 2 <= n)
  proof: clog_of_one_lt hb hn

中文:
定理 clog_of_two_le
  条件: {b n : 自然数} (hb : 1 < b) (hn : 2 <= n)
  证明: clog_of_one_lt hb hn

Depends on / 依赖: clog_of_one_lt
-/
theorem clog_of_two_le {b n : Nat} (hb : 1 < b) (hn : 2 <= n) :
    clog b n = clog b ((n + b - 1) / b) + 1 :=
  clog_of_one_lt hb hn

/--
theorem `clog_eq_one` / 定理 `clog_eq_one`

English:
theorem clog_eq_one
  given: {b n : Nat} (hn : 2 <= n) (h : n <= b)
  statement: clog b n = 1
  proof: by
  rw [clog_of_two_le (hn.trans h) hn]; rw [clog_of_right_le_one]
  rw [← Nat.lt_succ_iff]; rw [Nat.div_lt_iff_lt_mul] <;> lia

中文:
定理 clog_eq_one
  条件: {b n : 自然数} (hn : 2 <= n) (h : n <= b)
  结论: clog b n = 1
  证明: by
  rw [clog_of_two_le (hn.trans h) hn]; rw [clog_of_right_le_one]
  rw [← Nat.lt_succ_iff]; rw [Nat.div_lt_iff_lt_mul] <;> lia

Depends on / 依赖: Nat.div_lt_iff_lt_mul, Nat.lt_succ_iff, clog_of_right_le_one, clog_of_two_le, div_lt_iff_lt_mul, hn.trans, lt_succ_iff
-/
theorem clog_eq_one {b n : Nat} (hn : 2 <= n) (h : n <= b) : clog b n = 1 := by
  rw [clog_of_two_le (hn.trans h) hn]; rw [clog_of_right_le_one]
  rw [← Nat.lt_succ_iff]; rw [Nat.div_lt_iff_lt_mul] <;> lia

/--
theorem `clog_le_of_le_pow` / 定理 `clog_le_of_le_pow`

English:
theorem clog_le_of_le_pow
  given: {b x y : Nat} (h : x <= b ^ y)
  statement: clog b x <= y
  proof: by
  rcases Nat.lt_or_ge 1 b with hb | hb
  · rwa [clog_le_iff_le_pow hb]
  · grind [clog_of_left_le_one]

中文:
定理 clog_le_of_le_pow
  条件: {b x y : 自然数} (h : x <= b ^ y)
  结论: clog b x <= y
  证明: by
  rcases Nat.lt_or_ge 1 b with hb | hb
  · rwa [clog_le_iff_le_pow hb]
  · grind [clog_of_left_le_one]

Depends on / 依赖: Nat.lt_or_ge, clog_le_iff_le_pow, clog_of_left_le_one, lt_or_ge
-/
theorem clog_le_of_le_pow {b x y : Nat} (h : x <= b ^ y) : clog b x <= y := by
  rcases Nat.lt_or_ge 1 b with hb | hb
  · rwa [clog_le_iff_le_pow hb]
  · grind [clog_of_left_le_one]

/--
theorem `lt_clog_iff_pow_lt` / 定理 `lt_clog_iff_pow_lt`

English:
theorem lt_clog_iff_pow_lt
  given: {b : Nat} (hb : 1 < b) {x y : Nat}
  statement: y < clog b x ↔ b ^ y < x
  proof: lt_iff_lt_of_le_iff_le (clog_le_iff_le_pow hb)

中文:
定理 lt_clog_iff_pow_lt
  条件: {b : 自然数} (hb : 1 < b) {x y : 自然数}
  结论: y < clog b x ↔ b ^ y < x
  证明: lt_iff_lt_of_le_iff_le (clog_le_iff_le_pow hb)

Depends on / 依赖: clog_le_iff_le_pow, lt_iff_lt_of_le_iff_le
-/
theorem lt_clog_iff_pow_lt {b : Nat} (hb : 1 < b) {x y : Nat} : y < clog b x ↔ b ^ y < x :=
  lt_iff_lt_of_le_iff_le (clog_le_iff_le_pow hb)

/--
theorem `pow_lt_of_lt_clog` / 定理 `pow_lt_of_lt_clog`

English:
theorem pow_lt_of_lt_clog
  given: {b x y : Nat} (h : y < clog b x)
  statement: b ^ y < x
  proof: lt_imp_lt_of_le_imp_le clog_le_of_le_pow h

@[simp]

中文:
定理 pow_lt_of_lt_clog
  条件: {b x y : 自然数} (h : y < clog b x)
  结论: b ^ y < x
  证明: lt_imp_lt_of_le_imp_le clog_le_of_le_pow h

@[simp]

Depends on / 依赖: clog_le_of_le_pow, lt_imp_lt_of_le_imp_le
-/
theorem pow_lt_of_lt_clog {b x y : Nat} (h : y < clog b x) : b ^ y < x :=
  lt_imp_lt_of_le_imp_le clog_le_of_le_pow h

@[simp]
/--
theorem `clog_pow` / 定理 `clog_pow`

English:
theorem clog_pow
  given: (b x : Nat) (hb : 1 < b)
  statement: clog b (b ^ x) = x
  proof: eq_of_forall_ge_iff fun z => by rw [clog_le_iff_le_pow hb, Nat.pow_le_pow_iff_right hb]

中文:
定理 clog_pow
  条件: (b x : 自然数) (hb : 1 < b)
  结论: clog b (b ^ x) = x
  证明: eq_of_forall_ge_iff fun z => by rw [clog_le_iff_le_pow hb, Nat.pow_le_pow_iff_right hb]

Depends on / 依赖: Nat.pow_le_pow_iff_right, clog_le_iff_le_pow, eq_of_forall_ge_iff, pow_le_pow_iff_right
-/
theorem clog_pow (b x : Nat) (hb : 1 < b) : clog b (b ^ x) = x :=
  eq_of_forall_ge_iff fun z => by rw [clog_le_iff_le_pow hb, Nat.pow_le_pow_iff_right hb]

/--
theorem `pow_pred_clog_lt_self` / 定理 `pow_pred_clog_lt_self`

English:
theorem pow_pred_clog_lt_self
  given: {b : Nat} (hb : 1 < b) {x : Nat} (hx : 1 < x)
  proof: by
  rw [← lt_clog_iff_pow_lt hb]
  exact pred_lt (clog_pos hb hx).ne'

中文:
定理 pow_pred_clog_lt_self
  条件: {b : 自然数} (hb : 1 < b) {x : 自然数} (hx : 1 < x)
  证明: by
  rw [← lt_clog_iff_pow_lt hb]
  exact pred_lt (clog_pos hb hx).ne'

Depends on / 依赖: clog_pos, lt_clog_iff_pow_lt, pred_lt
-/
theorem pow_pred_clog_lt_self {b : Nat} (hb : 1 < b) {x : Nat} (hx : 1 < x) :
    b ^ (clog b x).pred < x := by
  rw [← lt_clog_iff_pow_lt hb]
  exact pred_lt (clog_pos hb hx).ne'

/--
theorem `le_pow_clog` / 定理 `le_pow_clog`

English:
theorem le_pow_clog
  given: {b : Nat} (hb : 1 < b) (x : Nat)
  statement: x <= b ^ clog b x
  proof: (clog_le_iff_le_pow hb).1 le_rfl

@[mono, gcongr]

中文:
定理 le_pow_clog
  条件: {b : 自然数} (hb : 1 < b) (x : 自然数)
  结论: x <= b ^ clog b x
  证明: (clog_le_iff_le_pow hb).1 le_rfl

@[mono, gcongr]

Depends on / 依赖: clog_le_iff_le_pow, le_rfl
-/
theorem le_pow_clog {b : Nat} (hb : 1 < b) (x : Nat) : x <= b ^ clog b x :=
  (clog_le_iff_le_pow hb).1 le_rfl

@[mono, gcongr]
/--
theorem `clog_mono_right` / 定理 `clog_mono_right`

English:
theorem clog_mono_right
  given: (b : Nat) {n m : Nat} (h : n <= m)
  statement: clog b n <= clog b m
  proof: by
  rcases le_or_gt b 1 with hb | hb
  · rw [clog_of_left_le_one hb]
    exact zero_le _
  · rw [clog_le_iff_le_pow hb]
    exact h.trans (le_pow_clog hb _)

中文:
定理 clog_mono_right
  条件: (b : 自然数) {n m : 自然数} (h : n <= m)
  结论: clog b n <= clog b m
  证明: by
  rcases le_or_gt b 1 with hb | hb
  · rw [clog_of_left_le_one hb]
    exact zero_le _
  · rw [clog_le_iff_le_pow hb]
    exact h.trans (le_pow_clog hb _)

Depends on / 依赖: clog_le_iff_le_pow, clog_of_left_le_one, h.trans, le_or_gt, le_pow_clog, zero_le
-/
theorem clog_mono_right (b : Nat) {n m : Nat} (h : n <= m) : clog b n <= clog b m := by
  rcases le_or_gt b 1 with hb | hb
  · rw [clog_of_left_le_one hb]
    exact zero_le _
  · rw [clog_le_iff_le_pow hb]
    exact h.trans (le_pow_clog hb _)

/--
theorem `clog_anti_left` / 定理 `clog_anti_left`

English:
theorem clog_anti_left
  given: {b c n : Nat} (hc : 1 < c) (hb : c <= b)
  statement: clog b n <= clog c n
  proof: by
  rw [clog_le_iff_le_pow (lt_of_lt_of_le hc hb)]
  calc
    n <= c ^ clog c n := le_pow_clog hc _
    _ <= b ^ clog c n := Nat.pow_le_pow_left hb _

中文:
定理 clog_anti_left
  条件: {b c n : 自然数} (hc : 1 < c) (hb : c <= b)
  结论: clog b n <= clog c n
  证明: by
  rw [clog_le_iff_le_pow (lt_of_lt_of_le hc hb)]
  calc
    n <= c ^ clog c n := le_pow_clog hc _
    _ <= b ^ clog c n := Nat.pow_le_pow_left hb _

Depends on / 依赖: Nat.pow_le_pow_left, clog_le_iff_le_pow, le_pow_clog, lt_of_lt_of_le, pow_le_pow_left
-/
theorem clog_anti_left {b c n : Nat} (hc : 1 < c) (hb : c <= b) : clog b n <= clog c n := by
  rw [clog_le_iff_le_pow (lt_of_lt_of_le hc hb)]
  calc
    n <= c ^ clog c n := le_pow_clog hc _
    _ <= b ^ clog c n := Nat.pow_le_pow_left hb _

/--
theorem `clog_monotone` / 定理 `clog_monotone`

English:
theorem clog_monotone
  given: (b : Nat)
  statement: Monotone (clog b)
  proof: fun _ _ => clog_mono_right _

中文:
定理 clog_monotone
  条件: (b : 自然数)
  结论: 递增 (clog b)
  证明: fun _ _ => clog_mono_right _

Depends on / 依赖: clog_mono_right
-/
theorem clog_monotone (b : Nat) : Monotone (clog b) := fun _ _ => clog_mono_right _

/--
theorem `clog_antitone_left` / 定理 `clog_antitone_left`

English:
theorem clog_antitone_left
  given: {n : Nat}
  statement: AntitoneOn (fun b : Nat => clog b n) (Set.Ioi 1)
  proof: fun _ hc _ _ hb => clog_anti_left (Set.mem_Iio.1 hc) hb

@[mono, gcongr]

中文:
定理 clog_antitone_left
  条件: {n : 自然数}
  结论: AntitoneOn (fun b : 自然数 => clog b n) (集合.左开右无界区间 1)
  证明: fun _ hc _ _ hb => clog_anti_left (Set.mem_Iio.1 hc) hb

@[mono, gcongr]

Depends on / 依赖: Set.mem_Iio, clog_anti_left, mem_Iio
-/
theorem clog_antitone_left {n : Nat} : AntitoneOn (fun b : Nat => clog b n) (Set.Ioi 1) :=
  fun _ hc _ _ hb => clog_anti_left (Set.mem_Iio.1 hc) hb

@[mono, gcongr]
/--
theorem `clog_mono` / 定理 `clog_mono`

English:
theorem clog_mono
  given: {b c m n : Nat} (hc : 1 < c) (hb : c <= b) (hmn : m <= n)
  proof: (clog_anti_left hc hb).trans by gcongr

@[simp]

中文:
定理 clog_mono
  条件: {b c m n : 自然数} (hc : 1 < c) (hb : c <= b) (hmn : m <= n)
  证明: (clog_anti_left hc hb).trans by gcongr

@[simp]

Depends on / 依赖: clog_anti_left
-/
theorem clog_mono {b c m n : Nat} (hc : 1 < c) (hb : c <= b) (hmn : m <= n) :
    clog b m <= clog c n :=
(clog_anti_left hc hb).trans by gcongr

@[simp]
/--
theorem `log_le_clog` / 定理 `log_le_clog`

English:
theorem log_le_clog
  given: (b n : Nat)
  statement: log b n <= clog b n
  proof: by
  obtain hb | hb := le_or_gt b 1
  · rw [log_of_left_le_one hb]
    exact zero_le _
  cases n with
  | zero =>
    rw [log_zero_right]
    exact zero_le _
  | succ n =>
    exact (Nat.pow_le_pow_iff_right hb).1
      ((pow_log_le_self b n.succ_ne_zero).trans <| le_pow_clog hb _)

中文:
定理 log_le_clog
  条件: (b n : 自然数)
  结论: log b n <= clog b n
  证明: by
  obtain hb | hb := le_or_gt b 1
  · rw [log_of_left_le_one hb]
    exact zero_le _
  cases n with
  | zero =>
    rw [log_zero_right]
    exact zero_le _
  | succ n =>
    exact (Nat.pow_le_pow_iff_right hb).1
      ((pow_log_le_self b n.succ_ne_zero).trans <| le_pow_clog hb _)

Depends on / 依赖: Nat.pow_le_pow_iff_right, le_or_gt, le_pow_clog, log_of_left_le_one, log_zero_right, n.succ_ne_zero, pow_le_pow_iff_right, pow_log_le_self, succ_ne_zero, zero_le
-/
theorem log_le_clog (b n : Nat) : log b n <= clog b n := by
  obtain hb | hb := le_or_gt b 1
  · rw [log_of_left_le_one hb]
    exact zero_le _
  cases n with
  | zero =>
    rw [log_zero_right]
    exact zero_le _
  | succ n =>
    exact (Nat.pow_le_pow_iff_right hb).1
      ((pow_log_le_self b n.succ_ne_zero).trans <| le_pow_clog hb _)

/--
theorem `clog_lt_clog_succ_iff` / 定理 `clog_lt_clog_succ_iff`

English:
theorem clog_lt_clog_succ_iff
  given: {b n : Nat} (hb : 1 < b)
  proof: by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · apply le_antisymm _ (le_pow_clog hb n)
    apply le_of_lt_succ
    exact (lt_clog_iff_pow_lt hb).mp H
  · rw [lt_clog_iff_pow_lt hb, H]
    exact n.lt_add_one

中文:
定理 clog_lt_clog_succ_iff
  条件: {b n : 自然数} (hb : 1 < b)
  证明: by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · apply le_antisymm _ (le_pow_clog hb n)
    apply le_of_lt_succ
    exact (lt_clog_iff_pow_lt hb).mp H
  · rw [lt_clog_iff_pow_lt hb, H]
    exact n.lt_add_one

Depends on / 依赖: le_antisymm, le_of_lt_succ, le_pow_clog, lt_add_one, lt_clog_iff_pow_lt, n.lt_add_one
-/
theorem clog_lt_clog_succ_iff {b n : Nat} (hb : 1 < b) :
    clog b n < clog b (n + 1) ↔ b ^ clog b n = n := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · apply le_antisymm _ (le_pow_clog hb n)
    apply le_of_lt_succ
    exact (lt_clog_iff_pow_lt hb).mp H
  · rw [lt_clog_iff_pow_lt hb, H]
    exact n.lt_add_one

/--
theorem `clog_eq_clog_succ_iff` / 定理 `clog_eq_clog_succ_iff`

English:
theorem clog_eq_clog_succ_iff
  given: {b n : Nat} (hb : 1 < b)
  proof: by
  rw [ne_eq]; rw [← clog_lt_clog_succ_iff hb]; rw [not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun _ => clog_monotone b (le_add_right n 1)

中文:
定理 clog_eq_clog_succ_iff
  条件: {b n : 自然数} (hb : 1 < b)
  证明: by
  rw [ne_eq]; rw [← clog_lt_clog_succ_iff hb]; rw [not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun _ => clog_monotone b (le_add_right n 1)

Depends on / 依赖: and_iff_right_iff_imp, clog_lt_clog_succ_iff, clog_monotone, le_add_right, le_antisymm_iff, ne_eq, not_lt
-/
theorem clog_eq_clog_succ_iff {b n : Nat} (hb : 1 < b) :
    clog b n = clog b (n + 1) ↔ b ^ clog b n != n := by
  rw [ne_eq]; rw [← clog_lt_clog_succ_iff hb]; rw [not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun _ => clog_monotone b (le_add_right n 1)

/--
theorem `clog_pow_left` / 定理 `clog_pow_left`

English:
theorem clog_pow_left
  given: (b k n : Nat)
  statement: clog (b ^ k) n = (clog b n + (k - 1)) / k
  proof: by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  · rcases Nat.lt_or_ge 1 b with hb | hb
    · refine eq_of_forall_lt_iff fun c => ?_
      rw [lt_clog_iff_pow_lt (Nat.one_lt_pow (Nat.ne_of_gt hk) hb)]; rw [Nat.lt_div_iff_mul_lt hk]; rw [Nat.add_sub_cancel]; rw [lt_clog_iff_pow_lt hb]; rw [Nat.pow_mul']
    · suffices (k - 1) / k = 0 by grind [clog_of_left_le_one, Nat.pow_le_one_iff]
      apply Nat.div_eq_of_lt
      grind

中文:
定理 clog_pow_left
  条件: (b k n : 自然数)
  结论: clog (b ^ k) n = (clog b n + (k - 1)) / k
  证明: by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  · rcases Nat.lt_or_ge 1 b with hb | hb
    · refine eq_of_forall_lt_iff fun c => ?_
      rw [lt_clog_iff_pow_lt (Nat.one_lt_pow (Nat.ne_of_gt hk) hb)]; rw [Nat.lt_div_iff_mul_lt hk]; rw [Nat.add_sub_cancel]; rw [lt_clog_iff_pow_lt hb]; rw [Nat.pow_mul']
    · suffices (k - 1) / k = 0 by grind [clog_of_left_le_one, Nat.pow_le_one_iff]
      apply Nat.div_eq_of_lt
      grind

Depends on / 依赖: Nat.add_sub_cancel, Nat.div_eq_of_lt, Nat.lt_div_iff_mul_lt, Nat.lt_or_ge, Nat.ne_of_gt, Nat.one_lt_pow, Nat.pow_le_one_iff, Nat.pow_mul, add_sub_cancel, clog_of_left_le_one, div_eq_of_lt, eq_of_forall_lt_iff, eq_zero_or_pos, k.eq_zero_or_pos, lt_clog_iff_pow_lt, lt_div_iff_mul_lt, lt_or_ge, ne_of_gt, one_lt_pow, pow_le_one_iff
-/
theorem clog_pow_left (b k n : Nat) : clog (b ^ k) n = (clog b n + (k - 1)) / k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  · rcases Nat.lt_or_ge 1 b with hb | hb
    · refine eq_of_forall_lt_iff fun c => ?_
      rw [lt_clog_iff_pow_lt (Nat.one_lt_pow (Nat.ne_of_gt hk) hb)]; rw [Nat.lt_div_iff_mul_lt hk]; rw [Nat.add_sub_cancel]; rw [lt_clog_iff_pow_lt hb]; rw [Nat.pow_mul']
    · suffices (k - 1) / k = 0 by grind [clog_of_left_le_one, Nat.pow_le_one_iff]
      apply Nat.div_eq_of_lt
      grind

end Nat
