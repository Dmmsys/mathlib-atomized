/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Absolute values in ordered groups

The absolute value of an element in a group which is also a lattice is its supremum with its
negation. This generalizes the usual absolute value on real numbers (`|x| = max x (-x)`).

## Notation

- `|a|`: The *absolute value* of an element `a` of an additive lattice ordered group
- `|a|ₘ`: The *absolute value* of an element `a` of a multiplicative lattice ordered group
-/

public section

open Function

variable {G : Type*}

section LinearOrderedCommGroup
variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

/--
lemma `mabs_pow` / 引理 `mabs_pow`

English:
lemma mabs_pow
  given: (n : Nat) (a : G)
  statement: |a ^ n|ₘ = |a|ₘ ^ n
  proof: by
  obtain ha | ha := le_total a 1
  · rw [mabs_of_le_one ha, ← mabs_inv, ← inv_pow, mabs_of_one_le]
    exact one_le_pow_of_one_le' (one_le_inv'.2 ha) n
  · rw [mabs_of_one_le ha, mabs_of_one_le (one_le_pow_of_one_le' ha n)]

中文:
引理 mabs_pow
  条件: (n : 自然数) (a : G)
  结论: |a ^ n|ₘ = |a|ₘ ^ n
  证明: by
  obtain ha | ha := le_total a 1
  · rw [mabs_of_le_one ha, ← mabs_inv, ← inv_pow, mabs_of_one_le]
    exact one_le_pow_of_one_le' (one_le_inv'.2 ha) n
  · rw [mabs_of_one_le ha, mabs_of_one_le (one_le_pow_of_one_le' ha n)]
-/
@[to_additive] lemma mabs_pow (n : Nat) (a : G) : |a ^ n|ₘ = |a|ₘ ^ n := by
  obtain ha | ha := le_total a 1
  · rw [mabs_of_le_one ha, ← mabs_inv, ← inv_pow, mabs_of_one_le]
    exact one_le_pow_of_one_le' (one_le_inv'.2 ha) n
  · rw [mabs_of_one_le ha, mabs_of_one_le (one_le_pow_of_one_le' ha n)]

/--
lemma `mabs_mul_eq_mul_mabs_le` / 引理 `mabs_mul_eq_mul_mabs_le`

English:
lemma mabs_mul_eq_mul_mabs_le
  given: (hab : a <= b)
  proof: by
  obtain ha | ha := le_or_gt 1 a <;> obtain hb | hb := le_or_gt 1 b
  · simp [ha, hb, mabs_of_one_le, one_le_mul ha hb]
  · exact (lt_irrefl (1 : G) <| ha.trans_lt <| hab.trans_lt hb).elim
  swap
  · simp [ha.le, hb.le, mabs_of_le_one, mul_le_one', mul_comm]
  have : (|a * b|ₘ = a⁻¹ * b ↔ b <= 1)

中文:
引理 mabs_mul_eq_mul_mabs_le
  条件: (hab : a <= b)
  证明: by
  obtain ha | ha := le_or_gt 1 a <;> obtain hb | hb := le_or_gt 1 b
  · simp [ha, hb, mabs_of_one_le, one_le_mul ha hb]
  · exact (lt_irrefl (1 : G) <| ha.trans_lt <| hab.trans_lt hb).elim
  swap
  · simp [ha.le, hb.le, mabs_of_le_one, mul_le_one', mul_comm]
  have : (|a * b|ₘ = a⁻¹ * b ↔ b <= 1)
-/
@[to_additive] private lemma mabs_mul_eq_mul_mabs_le (hab : a <= b) :
    |a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 <= a ∧ 1 <= b ∨ a <= 1 ∧ b <= 1 := by
  obtain ha | ha := le_or_gt 1 a <;> obtain hb | hb := le_or_gt 1 b
  · simp [ha, hb, mabs_of_one_le, one_le_mul ha hb]
  · exact (lt_irrefl (1 : G) <| ha.trans_lt <| hab.trans_lt hb).elim
  swap
  · simp [ha.le, hb.le, mabs_of_le_one, mul_le_one', mul_comm]
  have : (|a * b|ₘ = a⁻¹ * b ↔ b <= 1) ↔
    (|a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 <= a ∧ 1 <= b ∨ a <= 1 ∧ b <= 1) := by
    simp [ha.le, ha.not_ge, hb, mabs_of_le_one, mabs_of_one_le]
  refine this.mp ⟨fun h => ?_, fun h => by simp only [h.antisymm hb, mabs_of_lt_one ha, mul_one]⟩
  obtain ab | ab := le_or_gt (a * b) 1
  · refine (eq_one_of_inv_eq' ?_).le
    rwa [mabs_of_le_one ab, mul_inv_rev, mul_comm, mul_right_inj] at h
  · rw [mabs_of_one_lt ab, mul_left_inj] at h
    rw [eq_one_of_inv_eq' h.symm] at ha
    cases ha.false

/--
lemma `mabs_mul_eq_mul_mabs_iff` / 引理 `mabs_mul_eq_mul_mabs_iff`

English:
lemma mabs_mul_eq_mul_mabs_iff
  given: (a b : G)
  proof: by
  obtain ab | ab := le_total a b
  · exact mabs_mul_eq_mul_mabs_le ab
  · simpa only [mul_comm, and_comm] using mabs_mul_eq_mul_mabs_le ab

@[to_additive]

中文:
引理 mabs_mul_eq_mul_mabs_iff
  条件: (a b : G)
  证明: by
  obtain ab | ab := le_total a b
  · exact mabs_mul_eq_mul_mabs_le ab
  · simpa only [mul_comm, and_comm] using mabs_mul_eq_mul_mabs_le ab

@[to_additive]
-/
@[to_additive] lemma mabs_mul_eq_mul_mabs_iff (a b : G) :
    |a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 <= a ∧ 1 <= b ∨ a <= 1 ∧ b <= 1 := by
  obtain ab | ab := le_total a b
  · exact mabs_mul_eq_mul_mabs_le ab
  · simpa only [mul_comm, and_comm] using mabs_mul_eq_mul_mabs_le ab

@[to_additive]
/--
theorem `mabs_le` / 定理 `mabs_le`

English:
theorem mabs_le
  statement: |a|ₘ <= b ↔ b⁻¹ <= a ∧ a <= b
  proof: by rw [mabs_le', and_comm, inv_le']

@[to_additive]

中文:
定理 mabs_le
  结论: |a|ₘ <= b ↔ b⁻¹ <= a ∧ a <= b
  证明: by rw [mabs_le', and_comm, inv_le']

@[to_additive]

Depends on / 依赖: and_comm, inv_le, mabs_le
-/
theorem mabs_le : |a|ₘ <= b ↔ b⁻¹ <= a ∧ a <= b := by rw [mabs_le', and_comm, inv_le']

@[to_additive]
/--
theorem `le_mabs'` / 定理 `le_mabs'`

English:
theorem le_mabs'
  statement: a <= |b|ₘ ↔ b <= a⁻¹ ∨ a <= b
  proof: by rw [le_mabs, or_comm, le_inv']

@[to_additive]

中文:
定理 le_mabs'
  结论: a <= |b|ₘ ↔ b <= a⁻¹ ∨ a <= b
  证明: by rw [le_mabs, or_comm, le_inv']

@[to_additive]

Depends on / 依赖: le_inv, le_mabs, or_comm
-/
theorem le_mabs' : a <= |b|ₘ ↔ b <= a⁻¹ ∨ a <= b := by rw [le_mabs, or_comm, le_inv']

@[to_additive]
/--
theorem `inv_le_of_mabs_le` / 定理 `inv_le_of_mabs_le`

English:
theorem inv_le_of_mabs_le
  given: (h : |a|ₘ <= b)
  statement: b⁻¹ <= a
  proof: (mabs_le.mp h).1

@[to_additive]

中文:
定理 inv_le_of_mabs_le
  条件: (h : |a|ₘ <= b)
  结论: b⁻¹ <= a
  证明: (mabs_le.mp h).1

@[to_additive]

Depends on / 依赖: mabs_le, mabs_le.mp
-/
theorem inv_le_of_mabs_le (h : |a|ₘ <= b) : b⁻¹ <= a :=
  (mabs_le.mp h).1

@[to_additive]
/--
theorem `le_of_mabs_le` / 定理 `le_of_mabs_le`

English:
theorem le_of_mabs_le
  given: (h : |a|ₘ <= b)
  statement: a <= b
  proof: (mabs_le.mp h).2

@[to_additive]

中文:
定理 le_of_mabs_le
  条件: (h : |a|ₘ <= b)
  结论: a <= b
  证明: (mabs_le.mp h).2

@[to_additive]

Depends on / 依赖: mabs_le, mabs_le.mp
-/
theorem le_of_mabs_le (h : |a|ₘ <= b) : a <= b :=
  (mabs_le.mp h).2

@[to_additive]
/--
theorem `mabs_mul'` / 定理 `mabs_mul'`

English:
theorem mabs_mul'
  given: (a b : G)
  statement: |a|ₘ <= |b|ₘ * |b * a|ₘ
  proof: by simpa using mabs_mul_le b⁻¹ (b * a)

@[to_additive]

中文:
定理 mabs_mul'
  条件: (a b : G)
  结论: |a|ₘ <= |b|ₘ * |b * a|ₘ
  证明: by simpa using mabs_mul_le b⁻¹ (b * a)

@[to_additive]

Depends on / 依赖: mabs_mul_le
-/
theorem mabs_mul' (a b : G) : |a|ₘ <= |b|ₘ * |b * a|ₘ := by simpa using mabs_mul_le b⁻¹ (b * a)

@[to_additive]
/--
theorem `mabs_div` / 定理 `mabs_div`

English:
theorem mabs_div
  given: (a b : G)
  statement: |a / b|ₘ <= |a|ₘ * |b|ₘ
  proof: by
  rw [div_eq_mul_inv]; rw [← mabs_inv b]
  exact mabs_mul_le a _

@[to_additive]

中文:
定理 mabs_div
  条件: (a b : G)
  结论: |a / b|ₘ <= |a|ₘ * |b|ₘ
  证明: by
  rw [div_eq_mul_inv]; rw [← mabs_inv b]
  exact mabs_mul_le a _

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, mabs_inv, mabs_mul_le
-/
theorem mabs_div (a b : G) : |a / b|ₘ <= |a|ₘ * |b|ₘ := by
  rw [div_eq_mul_inv]; rw [← mabs_inv b]
  exact mabs_mul_le a _

@[to_additive]
/--
theorem `mabs_div_le_iff` / 定理 `mabs_div_le_iff`

English:
theorem mabs_div_le_iff
  statement: |a / b|ₘ <= c ↔ a / b <= c ∧ b / a <= c
  proof: by
  rw [mabs_le]; rw [inv_le_div_iff_le_mul]; rw [div_le_iff_le_mul']; rw [and_comm]; rw [div_le_iff_le_mul']

@[to_additive]

中文:
定理 mabs_div_le_iff
  结论: |a / b|ₘ <= c ↔ a / b <= c ∧ b / a <= c
  证明: by
  rw [mabs_le]; rw [inv_le_div_iff_le_mul]; rw [div_le_iff_le_mul']; rw [and_comm]; rw [div_le_iff_le_mul']

@[to_additive]

Depends on / 依赖: and_comm, div_le_iff_le_mul, inv_le_div_iff_le_mul, mabs_le
-/
theorem mabs_div_le_iff : |a / b|ₘ <= c ↔ a / b <= c ∧ b / a <= c := by
  rw [mabs_le]; rw [inv_le_div_iff_le_mul]; rw [div_le_iff_le_mul']; rw [and_comm]; rw [div_le_iff_le_mul']

@[to_additive]
/--
theorem `mabs_div_lt_iff` / 定理 `mabs_div_lt_iff`

English:
theorem mabs_div_lt_iff
  statement: |a / b|ₘ < c ↔ a / b < c ∧ b / a < c
  proof: by
  rw [mabs_lt]; rw [inv_lt_div_iff_lt_mul']; rw [div_lt_iff_lt_mul']; rw [and_comm]; rw [div_lt_iff_lt_mul']

@[to_additive]

中文:
定理 mabs_div_lt_iff
  结论: |a / b|ₘ < c ↔ a / b < c ∧ b / a < c
  证明: by
  rw [mabs_lt]; rw [inv_lt_div_iff_lt_mul']; rw [div_lt_iff_lt_mul']; rw [and_comm]; rw [div_lt_iff_lt_mul']

@[to_additive]

Depends on / 依赖: and_comm, div_lt_iff_lt_mul, inv_lt_div_iff_lt_mul, mabs_lt
-/
theorem mabs_div_lt_iff : |a / b|ₘ < c ↔ a / b < c ∧ b / a < c := by
  rw [mabs_lt]; rw [inv_lt_div_iff_lt_mul']; rw [div_lt_iff_lt_mul']; rw [and_comm]; rw [div_lt_iff_lt_mul']

@[to_additive]
/--
theorem `div_le_of_mabs_div_le_left` / 定理 `div_le_of_mabs_div_le_left`

English:
theorem div_le_of_mabs_div_le_left
  given: (h : |a / b|ₘ <= c)
  statement: b / c <= a
  proof: div_le_comm.1 (mabs_div_le_iff.1 h).2

@[to_additive]

中文:
定理 div_le_of_mabs_div_le_left
  条件: (h : |a / b|ₘ <= c)
  结论: b / c <= a
  证明: div_le_comm.1 (mabs_div_le_iff.1 h).2

@[to_additive]

Depends on / 依赖: div_le_comm, mabs_div_le_iff
-/
theorem div_le_of_mabs_div_le_left (h : |a / b|ₘ <= c) : b / c <= a :=
div_le_comm.1 (mabs_div_le_iff.1 h).2

@[to_additive]
/--
theorem `div_le_of_mabs_div_le_right` / 定理 `div_le_of_mabs_div_le_right`

English:
theorem div_le_of_mabs_div_le_right
  given: (h : |a / b|ₘ <= c)
  statement: a / c <= b
  proof: div_le_of_mabs_div_le_left (mabs_div_comm a b ▸ h)

@[to_additive]

中文:
定理 div_le_of_mabs_div_le_right
  条件: (h : |a / b|ₘ <= c)
  结论: a / c <= b
  证明: div_le_of_mabs_div_le_left (mabs_div_comm a b ▸ h)

@[to_additive]

Depends on / 依赖: div_le_of_mabs_div_le_left, mabs_div_comm
-/
theorem div_le_of_mabs_div_le_right (h : |a / b|ₘ <= c) : a / c <= b :=
  div_le_of_mabs_div_le_left (mabs_div_comm a b ▸ h)

@[to_additive]
/--
theorem `div_lt_of_mabs_div_lt_left` / 定理 `div_lt_of_mabs_div_lt_left`

English:
theorem div_lt_of_mabs_div_lt_left
  given: (h : |a / b|ₘ < c)
  statement: b / c < a
  proof: div_lt_comm.1 (mabs_div_lt_iff.1 h).2

@[to_additive]

中文:
定理 div_lt_of_mabs_div_lt_left
  条件: (h : |a / b|ₘ < c)
  结论: b / c < a
  证明: div_lt_comm.1 (mabs_div_lt_iff.1 h).2

@[to_additive]

Depends on / 依赖: div_lt_comm, mabs_div_lt_iff
-/
theorem div_lt_of_mabs_div_lt_left (h : |a / b|ₘ < c) : b / c < a :=
div_lt_comm.1 (mabs_div_lt_iff.1 h).2

@[to_additive]
/--
theorem `div_lt_of_mabs_div_lt_right` / 定理 `div_lt_of_mabs_div_lt_right`

English:
theorem div_lt_of_mabs_div_lt_right
  given: (h : |a / b|ₘ < c)
  statement: a / c < b
  proof: div_lt_of_mabs_div_lt_left (mabs_div_comm a b ▸ h)

@[to_additive]

中文:
定理 div_lt_of_mabs_div_lt_right
  条件: (h : |a / b|ₘ < c)
  结论: a / c < b
  证明: div_lt_of_mabs_div_lt_left (mabs_div_comm a b ▸ h)

@[to_additive]

Depends on / 依赖: div_lt_of_mabs_div_lt_left, mabs_div_comm
-/
theorem div_lt_of_mabs_div_lt_right (h : |a / b|ₘ < c) : a / c < b :=
  div_lt_of_mabs_div_lt_left (mabs_div_comm a b ▸ h)

@[to_additive]
/--
theorem `mabs_div_mabs_le_mabs_div` / 定理 `mabs_div_mabs_le_mabs_div`

English:
theorem mabs_div_mabs_le_mabs_div
  given: (a b : G)
  statement: |a|ₘ / |b|ₘ <= |a / b|ₘ
  proof: div_le_iff_le_mul.2
    calc
      |a|ₘ = |a / b * b|ₘ := by rw [div_mul_cancel]
      _ <= |a / b|ₘ * |b|ₘ := mabs_mul_le _ _

@[to_additive]

中文:
定理 mabs_div_mabs_le_mabs_div
  条件: (a b : G)
  结论: |a|ₘ / |b|ₘ <= |a / b|ₘ
  证明: div_le_iff_le_mul.2
    calc
      |a|ₘ = |a / b * b|ₘ := by rw [div_mul_cancel]
      _ <= |a / b|ₘ * |b|ₘ := mabs_mul_le _ _

@[to_additive]

Depends on / 依赖: div_le_iff_le_mul, div_mul_cancel, mabs_mul_le
-/
theorem mabs_div_mabs_le_mabs_div (a b : G) : |a|ₘ / |b|ₘ <= |a / b|ₘ :=
div_le_iff_le_mul.2
    calc
      |a|ₘ = |a / b * b|ₘ := by rw [div_mul_cancel]
      _ <= |a / b|ₘ * |b|ₘ := mabs_mul_le _ _

@[to_additive]
/--
theorem `mabs_div_mabs_le_mabs_mul` / 定理 `mabs_div_mabs_le_mabs_mul`

English:
theorem mabs_div_mabs_le_mabs_mul
  given: (a b : G)
  statement: |a|ₘ / |b|ₘ <= |a * b|ₘ
  proof: mabs_inv b ▸ div_inv_eq_mul a b ▸ mabs_div_mabs_le_mabs_div a b⁻¹

@[to_additive]

中文:
定理 mabs_div_mabs_le_mabs_mul
  条件: (a b : G)
  结论: |a|ₘ / |b|ₘ <= |a * b|ₘ
  证明: mabs_inv b ▸ div_inv_eq_mul a b ▸ mabs_div_mabs_le_mabs_div a b⁻¹

@[to_additive]

Depends on / 依赖: div_inv_eq_mul, mabs_div_mabs_le_mabs_div, mabs_inv
-/
theorem mabs_div_mabs_le_mabs_mul (a b : G) : |a|ₘ / |b|ₘ <= |a * b|ₘ :=
  mabs_inv b ▸ div_inv_eq_mul a b ▸ mabs_div_mabs_le_mabs_div a b⁻¹

@[to_additive]
/--
theorem `mabs_mabs_div_mabs_le_mabs_div` / 定理 `mabs_mabs_div_mabs_le_mabs_div`

English:
theorem mabs_mabs_div_mabs_le_mabs_div
  given: (a b : G)
  statement: |(|a|ₘ / |b|ₘ)|ₘ <= |a / b|ₘ
  proof: mabs_div_le_iff.2
    ⟨mabs_div_mabs_le_mabs_div _ _, by rw [mabs_div_comm]; apply mabs_div_mabs_le_mabs_div⟩

中文:
定理 mabs_mabs_div_mabs_le_mabs_div
  条件: (a b : G)
  结论: |(|a|ₘ / |b|ₘ)|ₘ <= |a / b|ₘ
  证明: mabs_div_le_iff.2
    ⟨mabs_div_mabs_le_mabs_div _ _, by rw [mabs_div_comm]; apply mabs_div_mabs_le_mabs_div⟩

Depends on / 依赖: mabs_div_comm, mabs_div_le_iff, mabs_div_mabs_le_mabs_div
-/
theorem mabs_mabs_div_mabs_le_mabs_div (a b : G) : |(|a|ₘ / |b|ₘ)|ₘ <= |a / b|ₘ :=
  mabs_div_le_iff.2
    ⟨mabs_div_mabs_le_mabs_div _ _, by rw [mabs_div_comm]; apply mabs_div_mabs_le_mabs_div⟩

/-- `|a / b|ₘ ≤ n` if `1 ≤ a ≤ n` and `1 ≤ b ≤ n`. -/
@[to_additive /-- `|a - b| ≤ n` if `0 ≤ a ≤ n` and `0 ≤ b ≤ n`. -/]
/--
theorem `mabs_div_le_of_one_le_of_le` / 定理 `mabs_div_le_of_one_le_of_le`

English:
theorem mabs_div_le_of_one_le_of_le
  statement: {a b n : G} (one_le_a : 1 <= a) (a_le_n : a <= n)
  proof: by
  rw [mabs_div_le_iff]; rw [div_le_iff_le_mul]; rw [div_le_iff_le_mul]
  exact ⟨le_mul_of_le_of_one_le a_le_n one_le_b, le_mul_of_le_of_one_le b_le_n one_le_a⟩

中文:
定理 mabs_div_le_of_one_le_of_le
  结论: {a b n : G} (one_le_a : 1 <= a) (a_le_n : a <= n)
  证明: by
  rw [mabs_div_le_iff]; rw [div_le_iff_le_mul]; rw [div_le_iff_le_mul]
  exact ⟨le_mul_of_le_of_one_le a_le_n one_le_b, le_mul_of_le_of_one_le b_le_n one_le_a⟩

Depends on / 依赖: a_le_n, b_le_n, div_le_iff_le_mul, le_mul_of_le_of_one_le, mabs_div_le_iff, one_le_a, one_le_b
-/
theorem mabs_div_le_of_one_le_of_le {a b n : G} (one_le_a : 1 <= a) (a_le_n : a <= n)
    (one_le_b : 1 <= b) (b_le_n : b <= n) : |a / b|ₘ <= n := by
  rw [mabs_div_le_iff]; rw [div_le_iff_le_mul]; rw [div_le_iff_le_mul]
  exact ⟨le_mul_of_le_of_one_le a_le_n one_le_b, le_mul_of_le_of_one_le b_le_n one_le_a⟩

/-- `|a / b|ₘ < n` if `1 ≤ a < n` and `1 ≤ b < n`. -/
@[to_additive /-- `|a - b| < n` if `0 ≤ a < n` and `0 ≤ b < n`. -/]
/--
theorem `mabs_div_lt_of_one_le_of_lt` / 定理 `mabs_div_lt_of_one_le_of_lt`

English:
theorem mabs_div_lt_of_one_le_of_lt
  statement: {a b n : G} (one_le_a : 1 <= a) (a_lt_n : a < n)
  proof: by
  rw [mabs_div_lt_iff]; rw [div_lt_iff_lt_mul]; rw [div_lt_iff_lt_mul]
  exact ⟨lt_mul_of_lt_of_one_le a_lt_n one_le_b, lt_mul_of_lt_of_one_le b_lt_n one_le_a⟩

@[to_additive]

中文:
定理 mabs_div_lt_of_one_le_of_lt
  结论: {a b n : G} (one_le_a : 1 <= a) (a_lt_n : a < n)
  证明: by
  rw [mabs_div_lt_iff]; rw [div_lt_iff_lt_mul]; rw [div_lt_iff_lt_mul]
  exact ⟨lt_mul_of_lt_of_one_le a_lt_n one_le_b, lt_mul_of_lt_of_one_le b_lt_n one_le_a⟩

@[to_additive]

Depends on / 依赖: a_lt_n, b_lt_n, div_lt_iff_lt_mul, lt_mul_of_lt_of_one_le, mabs_div_lt_iff, one_le_a, one_le_b
-/
theorem mabs_div_lt_of_one_le_of_lt {a b n : G} (one_le_a : 1 <= a) (a_lt_n : a < n)
    (one_le_b : 1 <= b) (b_lt_n : b < n) : |a / b|ₘ < n := by
  rw [mabs_div_lt_iff]; rw [div_lt_iff_lt_mul]; rw [div_lt_iff_lt_mul]
  exact ⟨lt_mul_of_lt_of_one_le a_lt_n one_le_b, lt_mul_of_lt_of_one_le b_lt_n one_le_a⟩

@[to_additive]
/--
theorem `mabs_eq` / 定理 `mabs_eq`

English:
theorem mabs_eq
  given: (hb : 1 <= b)
  statement: |a|ₘ = b ↔ a = b ∨ a = b⁻¹
  proof: by
  refine ⟨eq_or_eq_inv_of_mabs_eq, ?_⟩
  rintro (rfl | rfl) <;> simp only [mabs_inv, mabs_of_one_le hb]

@[to_additive]

中文:
定理 mabs_eq
  条件: (hb : 1 <= b)
  结论: |a|ₘ = b ↔ a = b ∨ a = b⁻¹
  证明: by
  refine ⟨eq_or_eq_inv_of_mabs_eq, ?_⟩
  rintro (rfl | rfl) <;> simp only [mabs_inv, mabs_of_one_le hb]

@[to_additive]

Depends on / 依赖: eq_or_eq_inv_of_mabs_eq, mabs_inv, mabs_of_one_le
-/
theorem mabs_eq (hb : 1 <= b) : |a|ₘ = b ↔ a = b ∨ a = b⁻¹ := by
  refine ⟨eq_or_eq_inv_of_mabs_eq, ?_⟩
  rintro (rfl | rfl) <;> simp only [mabs_inv, mabs_of_one_le hb]

@[to_additive]
/--
theorem `mabs_le_max_mabs_mabs` / 定理 `mabs_le_max_mabs_mabs`

English:
theorem mabs_le_max_mabs_mabs
  given: (hab : a <= b) (hbc : b <= c)
  statement: |b|ₘ <= max |a|ₘ |c|ₘ
  proof: mabs_le'.2
    ⟨by simp [hbc.trans (le_mabs_self c)], by
      simp [(inv_le_inv_iff.mpr hab).trans (inv_le_mabs a)]⟩

omit [IsOrderedMonoid G] in
@[to_additive]

中文:
定理 mabs_le_max_mabs_mabs
  条件: (hab : a <= b) (hbc : b <= c)
  结论: |b|ₘ <= max |a|ₘ |c|ₘ
  证明: mabs_le'.2
    ⟨by simp [hbc.trans (le_mabs_self c)], by
      simp [(inv_le_inv_iff.mpr hab).trans (inv_le_mabs a)]⟩

omit [IsOrderedMonoid G] in
@[to_additive]

Depends on / 依赖: hbc.trans, inv_le_inv_iff, inv_le_inv_iff.mpr, inv_le_mabs, le_mabs_self, mabs_le
-/
theorem mabs_le_max_mabs_mabs (hab : a <= b) (hbc : b <= c) : |b|ₘ <= max |a|ₘ |c|ₘ :=
  mabs_le'.2
    ⟨by simp [hbc.trans (le_mabs_self c)], by
      simp [(inv_le_inv_iff.mpr hab).trans (inv_le_mabs a)]⟩

omit [IsOrderedMonoid G] in
@[to_additive]
/--
theorem `min_mabs_mabs_le_mabs_max` / 定理 `min_mabs_mabs_le_mabs_max`

English:
theorem min_mabs_mabs_le_mabs_max
  statement: min |a|ₘ |b|ₘ <= |max a b|ₘ
  proof: (le_total a b).elim (fun h => (min_le_right _ _).trans_eq <| congr_arg _ (max_eq_right h).symm)
fun h => (min_le_left _ _).trans_eq congr_arg _ (max_eq_left h).symm

omit [IsOrderedMonoid G] in
@[to_additive]

中文:
定理 min_mabs_mabs_le_mabs_max
  结论: min |a|ₘ |b|ₘ <= |max a b|ₘ
  证明: (le_total a b).elim (fun h => (min_le_right _ _).trans_eq <| congr_arg _ (max_eq_right h).symm)
fun h => (min_le_left _ _).trans_eq congr_arg _ (max_eq_left h).symm

omit [IsOrderedMonoid G] in
@[to_additive]

Depends on / 依赖: congr_arg, le_total, max_eq_left, max_eq_right, min_le_left, min_le_right, trans_eq
-/
theorem min_mabs_mabs_le_mabs_max : min |a|ₘ |b|ₘ <= |max a b|ₘ :=
  (le_total a b).elim (fun h => (min_le_right _ _).trans_eq <| congr_arg _ (max_eq_right h).symm)
fun h => (min_le_left _ _).trans_eq congr_arg _ (max_eq_left h).symm

omit [IsOrderedMonoid G] in
@[to_additive]
/--
theorem `min_mabs_mabs_le_mabs_min` / 定理 `min_mabs_mabs_le_mabs_min`

English:
theorem min_mabs_mabs_le_mabs_min
  statement: min |a|ₘ |b|ₘ <= |min a b|ₘ
  proof: (le_total a b).elim (fun h => (min_le_left _ _).trans_eq <| congr_arg _ (min_eq_left h).symm)
fun h => (min_le_right _ _).trans_eq congr_arg _ (min_eq_right h).symm

omit [IsOrderedMonoid G] in
@[to_additive]

中文:
定理 min_mabs_mabs_le_mabs_min
  结论: min |a|ₘ |b|ₘ <= |min a b|ₘ
  证明: (le_total a b).elim (fun h => (min_le_left _ _).trans_eq <| congr_arg _ (min_eq_left h).symm)
fun h => (min_le_right _ _).trans_eq congr_arg _ (min_eq_right h).symm

omit [IsOrderedMonoid G] in
@[to_additive]

Depends on / 依赖: congr_arg, le_total, min_eq_left, min_eq_right, min_le_left, min_le_right, trans_eq
-/
theorem min_mabs_mabs_le_mabs_min : min |a|ₘ |b|ₘ <= |min a b|ₘ :=
  (le_total a b).elim (fun h => (min_le_left _ _).trans_eq <| congr_arg _ (min_eq_left h).symm)
fun h => (min_le_right _ _).trans_eq congr_arg _ (min_eq_right h).symm

omit [IsOrderedMonoid G] in
@[to_additive]
/--
theorem `mabs_max_le_max_mabs_mabs` / 定理 `mabs_max_le_max_mabs_mabs`

English:
theorem mabs_max_le_max_mabs_mabs
  statement: |max a b|ₘ <= max |a|ₘ |b|ₘ
  proof: (le_total a b).elim (fun h => (congr_arg _ <| max_eq_right h).trans_le <| le_max_right _ _)
fun h => (congr_arg _ <| max_eq_left h).trans_le le_max_left _ _

omit [IsOrderedMonoid G] in
@[to_additive]

中文:
定理 mabs_max_le_max_mabs_mabs
  结论: |max a b|ₘ <= max |a|ₘ |b|ₘ
  证明: (le_total a b).elim (fun h => (congr_arg _ <| max_eq_right h).trans_le <| le_max_right _ _)
fun h => (congr_arg _ <| max_eq_left h).trans_le le_max_left _ _

omit [IsOrderedMonoid G] in
@[to_additive]

Depends on / 依赖: congr_arg, le_max_left, le_max_right, le_total, max_eq_left, max_eq_right, trans_le
-/
theorem mabs_max_le_max_mabs_mabs : |max a b|ₘ <= max |a|ₘ |b|ₘ :=
  (le_total a b).elim (fun h => (congr_arg _ <| max_eq_right h).trans_le <| le_max_right _ _)
fun h => (congr_arg _ <| max_eq_left h).trans_le le_max_left _ _

omit [IsOrderedMonoid G] in
@[to_additive]
/--
theorem `mabs_min_le_max_mabs_mabs` / 定理 `mabs_min_le_max_mabs_mabs`

English:
theorem mabs_min_le_max_mabs_mabs
  statement: |min a b|ₘ <= max |a|ₘ |b|ₘ
  proof: (le_total a b).elim (fun h => (congr_arg _ <| min_eq_left h).trans_le <| le_max_left _ _) fun h =>
(congr_arg _ <| min_eq_right h).trans_le le_max_right _ _

@[to_additive]

中文:
定理 mabs_min_le_max_mabs_mabs
  结论: |min a b|ₘ <= max |a|ₘ |b|ₘ
  证明: (le_total a b).elim (fun h => (congr_arg _ <| min_eq_left h).trans_le <| le_max_left _ _) fun h =>
(congr_arg _ <| min_eq_right h).trans_le le_max_right _ _

@[to_additive]

Depends on / 依赖: congr_arg, le_max_left, le_max_right, le_total, min_eq_left, min_eq_right, trans_le
-/
theorem mabs_min_le_max_mabs_mabs : |min a b|ₘ <= max |a|ₘ |b|ₘ :=
  (le_total a b).elim (fun h => (congr_arg _ <| min_eq_left h).trans_le <| le_max_left _ _) fun h =>
(congr_arg _ <| min_eq_right h).trans_le le_max_right _ _

@[to_additive]
/--
theorem `eq_of_mabs_div_eq_one` / 定理 `eq_of_mabs_div_eq_one`

English:
theorem eq_of_mabs_div_eq_one
  given: {a b : G} (h : |a / b|ₘ = 1)
  statement: a = b
  proof: div_eq_one.1 mabs_eq_one.1 h

@[to_additive]

中文:
定理 eq_of_mabs_div_eq_one
  条件: {a b : G} (h : |a / b|ₘ = 1)
  结论: a = b
  证明: div_eq_one.1 mabs_eq_one.1 h

@[to_additive]

Depends on / 依赖: div_eq_one, mabs_eq_one
-/
theorem eq_of_mabs_div_eq_one {a b : G} (h : |a / b|ₘ = 1) : a = b :=
div_eq_one.1 mabs_eq_one.1 h

@[to_additive]
/--
theorem `mabs_div_le` / 定理 `mabs_div_le`

English:
theorem mabs_div_le
  given: (a b c : G)
  statement: |a / c|ₘ <= |a / b|ₘ * |b / c|ₘ
  proof: calc
    |a / c|ₘ = |a / b * (b / c)|ₘ := by rw [div_mul_div_cancel]
    _ <= |a / b|ₘ * |b / c|ₘ := mabs_mul_le _ _

@[to_additive]

中文:
定理 mabs_div_le
  条件: (a b c : G)
  结论: |a / c|ₘ <= |a / b|ₘ * |b / c|ₘ
  证明: calc
    |a / c|ₘ = |a / b * (b / c)|ₘ := by rw [div_mul_div_cancel]
    _ <= |a / b|ₘ * |b / c|ₘ := mabs_mul_le _ _

@[to_additive]

Depends on / 依赖: div_mul_div_cancel, mabs_mul_le
-/
theorem mabs_div_le (a b c : G) : |a / c|ₘ <= |a / b|ₘ * |b / c|ₘ :=
  calc
    |a / c|ₘ = |a / b * (b / c)|ₘ := by rw [div_mul_div_cancel]
    _ <= |a / b|ₘ * |b / c|ₘ := mabs_mul_le _ _

@[to_additive]
/--
theorem `mabs_div_le_max_div` / 定理 `mabs_div_le_max_div`

English:
theorem mabs_div_le_max_div
  given: {a b c : G} (hac : a <= b) (hcd : b <= c) (d : G)
  proof: by
  rcases le_total d b with h | h
  · rw [mabs_of_one_le <| one_le_div'.mpr h]
exact le_max_of_le_left div_le_div_right' hcd _
  · rw [mabs_of_le_one <| div_le_one'.mpr h, inv_div]
exact le_max_of_le_right div_le_div_left' hac _

@[to_additive]

中文:
定理 mabs_div_le_max_div
  条件: {a b c : G} (hac : a <= b) (hcd : b <= c) (d : G)
  证明: by
  rcases le_total d b with h | h
  · rw [mabs_of_one_le <| one_le_div'.mpr h]
exact le_max_of_le_left div_le_div_right' hcd _
  · rw [mabs_of_le_one <| div_le_one'.mpr h, inv_div]
exact le_max_of_le_right div_le_div_left' hac _

@[to_additive]

Depends on / 依赖: div_le_div_left, div_le_div_right, div_le_one, inv_div, le_max_of_le_left, le_max_of_le_right, le_total, mabs_of_le_one, mabs_of_one_le, one_le_div
-/
theorem mabs_div_le_max_div {a b c : G} (hac : a <= b) (hcd : b <= c) (d : G) :
    |b / d|ₘ <= max (c / d) (d / a) := by
  rcases le_total d b with h | h
  · rw [mabs_of_one_le <| one_le_div'.mpr h]
exact le_max_of_le_left div_le_div_right' hcd _
  · rw [mabs_of_le_one <| div_le_one'.mpr h, inv_div]
exact le_max_of_le_right div_le_div_left' hac _

@[to_additive]
/--
theorem `mabs_mul_three` / 定理 `mabs_mul_three`

English:
theorem mabs_mul_three
  given: (a b c : G)
  statement: |a * b * c|ₘ <= |a|ₘ * |b|ₘ * |c|ₘ
  proof: by
  grw [mabs_mul_le, mabs_mul_le]

@[to_additive]

中文:
定理 mabs_mul_three
  条件: (a b c : G)
  结论: |a * b * c|ₘ <= |a|ₘ * |b|ₘ * |c|ₘ
  证明: by
  grw [mabs_mul_le, mabs_mul_le]

@[to_additive]

Depends on / 依赖: mabs_mul_le
-/
theorem mabs_mul_three (a b c : G) : |a * b * c|ₘ <= |a|ₘ * |b|ₘ * |c|ₘ := by
  grw [mabs_mul_le, mabs_mul_le]

@[to_additive]
/--
theorem `mabs_div_le_of_le_of_le` / 定理 `mabs_div_le_of_le_of_le`

English:
theorem mabs_div_le_of_le_of_le
  statement: {a b lb ub : G} (hal : lb <= a) (hau : a <= ub) (hbl : lb <= b)
  proof: mabs_div_le_iff.2 ⟨div_le_div'' hau hbl, div_le_div'' hbu hal⟩

@[to_additive]

中文:
定理 mabs_div_le_of_le_of_le
  结论: {a b lb ub : G} (hal : lb <= a) (hau : a <= ub) (hbl : lb <= b)
  证明: mabs_div_le_iff.2 ⟨div_le_div'' hau hbl, div_le_div'' hbu hal⟩

@[to_additive]

Depends on / 依赖: div_le_div, mabs_div_le_iff
-/
theorem mabs_div_le_of_le_of_le {a b lb ub : G} (hal : lb <= a) (hau : a <= ub) (hbl : lb <= b)
    (hbu : b <= ub) : |a / b|ₘ <= ub / lb :=
  mabs_div_le_iff.2 ⟨div_le_div'' hau hbl, div_le_div'' hbu hal⟩

@[to_additive]
/--
theorem `eq_of_mabs_div_le_one` / 定理 `eq_of_mabs_div_le_one`

English:
theorem eq_of_mabs_div_le_one
  given: (h : |a / b|ₘ <= 1)
  statement: a = b
  proof: eq_of_mabs_div_eq_one (le_antisymm h (one_le_mabs (a / b)))

@[to_additive]

中文:
定理 eq_of_mabs_div_le_one
  条件: (h : |a / b|ₘ <= 1)
  结论: a = b
  证明: eq_of_mabs_div_eq_one (le_antisymm h (one_le_mabs (a / b)))

@[to_additive]

Depends on / 依赖: eq_of_mabs_div_eq_one, le_antisymm, one_le_mabs
-/
theorem eq_of_mabs_div_le_one (h : |a / b|ₘ <= 1) : a = b :=
  eq_of_mabs_div_eq_one (le_antisymm h (one_le_mabs (a / b)))

@[to_additive]
/--
lemma `eq_of_mabs_div_lt_all` / 引理 `eq_of_mabs_div_lt_all`

English:
lemma eq_of_mabs_div_lt_all
  given: {x y : G} (h : forall ε > 1, |x / y|ₘ < ε)
  statement: x = y
  proof: eq_of_mabs_div_le_one le_of_forall_gt h

@[to_additive]

中文:
引理 eq_of_mabs_div_lt_all
  条件: {x y : G} (h : 对任意 ε > 1, |x / y|ₘ < ε)
  结论: x = y
  证明: eq_of_mabs_div_le_one le_of_forall_gt h

@[to_additive]

Depends on / 依赖: eq_of_mabs_div_le_one, le_of_forall_gt
-/
lemma eq_of_mabs_div_lt_all {x y : G} (h : forall ε > 1, |x / y|ₘ < ε) : x = y :=
eq_of_mabs_div_le_one le_of_forall_gt h

@[to_additive]
/--
lemma `eq_of_mabs_div_le_all` / 引理 `eq_of_mabs_div_le_all`

English:
lemma eq_of_mabs_div_le_all
  given: [DenselyOrdered G] {x y : G} (h : forall ε > 1, |x / y|ₘ <= ε)
  statement: x = y
  proof: eq_of_mabs_div_le_one forall_gt_imp_ge_iff_le_of_dense.mp h

@[to_additive]

中文:
引理 eq_of_mabs_div_le_all
  条件: [DenselyOrdered G] {x y : G} (h : 对任意 ε > 1, |x / y|ₘ <= ε)
  结论: x = y
  证明: eq_of_mabs_div_le_one forall_gt_imp_ge_iff_le_of_dense.mp h

@[to_additive]

Depends on / 依赖: eq_of_mabs_div_le_one, forall_gt_imp_ge_iff_le_of_dense, forall_gt_imp_ge_iff_le_of_dense.mp
-/
lemma eq_of_mabs_div_le_all [DenselyOrdered G] {x y : G} (h : forall ε > 1, |x / y|ₘ <= ε) : x = y :=
eq_of_mabs_div_le_one forall_gt_imp_ge_iff_le_of_dense.mp h

@[to_additive]
/--
theorem `mabs_div_le_one` / 定理 `mabs_div_le_one`

English:
theorem mabs_div_le_one
  statement: |a / b|ₘ <= 1 ↔ a = b
  proof: ⟨eq_of_mabs_div_le_one, by rintro rfl; rw [div_self', mabs_one]⟩

@[to_additive]

中文:
定理 mabs_div_le_one
  结论: |a / b|ₘ <= 1 ↔ a = b
  证明: ⟨eq_of_mabs_div_le_one, by rintro rfl; rw [div_self', mabs_one]⟩

@[to_additive]

Depends on / 依赖: div_self, eq_of_mabs_div_le_one, mabs_one
-/
theorem mabs_div_le_one : |a / b|ₘ <= 1 ↔ a = b :=
  ⟨eq_of_mabs_div_le_one, by rintro rfl; rw [div_self', mabs_one]⟩

@[to_additive]
/--
theorem `mabs_div_pos` / 定理 `mabs_div_pos`

English:
theorem mabs_div_pos
  statement: 1 < |a / b|ₘ ↔ a != b
  proof: not_le.symm.trans mabs_div_le_one.not

@[to_additive (attr := simp)]

中文:
定理 mabs_div_pos
  结论: 1 < |a / b|ₘ ↔ a != b
  证明: not_le.symm.trans mabs_div_le_one.not

@[to_additive (attr := simp)]

Depends on / 依赖: mabs_div_le_one, mabs_div_le_one.not, not_le, not_le.symm.trans
-/
theorem mabs_div_pos : 1 < |a / b|ₘ ↔ a != b :=
  not_le.symm.trans mabs_div_le_one.not

@[to_additive (attr := simp)]
/--
theorem `mabs_eq_self` / 定理 `mabs_eq_self`

English:
theorem mabs_eq_self
  statement: |a|ₘ = a ↔ 1 <= a
  proof: by
  rw [mabs_eq_max_inv]; rw [max_eq_left_iff]; rw [inv_le_self_iff]

@[to_additive (attr := simp)]

中文:
定理 mabs_eq_self
  结论: |a|ₘ = a ↔ 1 <= a
  证明: by
  rw [mabs_eq_max_inv]; rw [max_eq_left_iff]; rw [inv_le_self_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_le_self_iff, mabs_eq_max_inv, max_eq_left_iff
-/
theorem mabs_eq_self : |a|ₘ = a ↔ 1 <= a := by
  rw [mabs_eq_max_inv]; rw [max_eq_left_iff]; rw [inv_le_self_iff]

@[to_additive (attr := simp)]
/--
theorem `mabs_eq_inv_self` / 定理 `mabs_eq_inv_self`

English:
theorem mabs_eq_inv_self
  statement: |a|ₘ = a⁻¹ ↔ a <= 1
  proof: by
  rw [mabs_eq_max_inv]; rw [max_eq_right_iff]; rw [le_inv_self_iff]

中文:
定理 mabs_eq_inv_self
  结论: |a|ₘ = a⁻¹ ↔ a <= 1
  证明: by
  rw [mabs_eq_max_inv]; rw [max_eq_right_iff]; rw [le_inv_self_iff]

Depends on / 依赖: le_inv_self_iff, mabs_eq_max_inv, max_eq_right_iff
-/
theorem mabs_eq_inv_self : |a|ₘ = a⁻¹ ↔ a <= 1 := by
  rw [mabs_eq_max_inv]; rw [max_eq_right_iff]; rw [le_inv_self_iff]

/-- For an element `a` of a multiplicative linear ordered group,
either `|a|ₘ = a` and `1 ≤ a`, or `|a|ₘ = a⁻¹` and `a < 1`. -/
@[to_additive
  /-- For an element `a` of an additive linear ordered group,
  either `|a| = a` and `0 ≤ a`, or `|a| = -a` and `a < 0`.
  Use cases on this lemma to automate linarith in inequalities -/]
/--
theorem `mabs_cases` / 定理 `mabs_cases`

English:
theorem mabs_cases
  given: (a : G)
  statement: |a|ₘ = a ∧ 1 <= a ∨ |a|ₘ = a⁻¹ ∧ a < 1
  proof: by
  cases le_or_gt 1 a <;> simp [*, le_of_lt]

@[to_additive (attr := simp)]

中文:
定理 mabs_cases
  条件: (a : G)
  结论: |a|ₘ = a ∧ 1 <= a ∨ |a|ₘ = a⁻¹ ∧ a < 1
  证明: by
  cases le_or_gt 1 a <;> simp [*, le_of_lt]

@[to_additive (attr := simp)]

Depends on / 依赖: le_of_lt, le_or_gt
-/
theorem mabs_cases (a : G) : |a|ₘ = a ∧ 1 <= a ∨ |a|ₘ = a⁻¹ ∧ a < 1 := by
  cases le_or_gt 1 a <;> simp [*, le_of_lt]

@[to_additive (attr := simp)]
/--
theorem `max_one_mul_max_inv_one_eq_mabs_self` / 定理 `max_one_mul_max_inv_one_eq_mabs_self`

English:
theorem max_one_mul_max_inv_one_eq_mabs_self
  given: (a : G)
  statement: max a 1 * max a⁻¹ 1 = |a|ₘ
  proof: by
  symm
  rcases le_total 1 a with (ha | ha) <;> simp [ha]

中文:
定理 max_one_mul_max_inv_one_eq_mabs_self
  条件: (a : G)
  结论: max a 1 * max a⁻¹ 1 = |a|ₘ
  证明: by
  symm
  rcases le_total 1 a with (ha | ha) <;> simp [ha]

Depends on / 依赖: le_total
-/
theorem max_one_mul_max_inv_one_eq_mabs_self (a : G) : max a 1 * max a⁻¹ 1 = |a|ₘ := by
  symm
  rcases le_total 1 a with (ha | ha) <;> simp [ha]

end LinearOrderedCommGroup

section LinearOrderedAddCommGroup

variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] {a b c : G}

@[to_additive]
/--
theorem `apply_abs_le_mul_of_one_le'` / 定理 `apply_abs_le_mul_of_one_le'`

English:
theorem apply_abs_le_mul_of_one_le'
  statement: {H : Type*} [MulOneClass H] [LE H]
  proof: (le_total a 0).rec (fun ha => (abs_of_nonpos ha).symm ▸ le_mul_of_one_le_left' h₁) fun ha =>
    (abs_of_nonneg ha).symm ▸ le_mul_of_one_le_right' h₂

@[to_additive]

中文:
定理 apply_abs_le_mul_of_one_le'
  结论: {H : 类型} [MulOneClass H] [LE H]
  证明: (le_total a 0).rec (fun ha => (abs_of_nonpos ha).symm ▸ le_mul_of_one_le_left' h₁) fun ha =>
    (abs_of_nonneg ha).symm ▸ le_mul_of_one_le_right' h₂

@[to_additive]

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, le_mul_of_one_le_left, le_mul_of_one_le_right, le_total
-/
theorem apply_abs_le_mul_of_one_le' {H : Type*} [MulOneClass H] [LE H]
    [MulLeftMono H] [MulRightMono H] {f : G -> H}
    {a : G} (h₁ : 1 <= f a) (h₂ : 1 <= f (-a)) : f |a| <= f a * f (-a) :=
  (le_total a 0).rec (fun ha => (abs_of_nonpos ha).symm ▸ le_mul_of_one_le_left' h₁) fun ha =>
    (abs_of_nonneg ha).symm ▸ le_mul_of_one_le_right' h₂

@[to_additive]
/--
theorem `apply_abs_le_mul_of_one_le` / 定理 `apply_abs_le_mul_of_one_le`

English:
theorem apply_abs_le_mul_of_one_le
  statement: {H : Type*} [MulOneClass H] [LE H]
  proof: apply_abs_le_mul_of_one_le' (h _) (h _)

中文:
定理 apply_abs_le_mul_of_one_le
  结论: {H : 类型} [MulOneClass H] [LE H]
  证明: apply_abs_le_mul_of_one_le' (h _) (h _)

Depends on / 依赖: apply_abs_le_mul_of_one_le
-/
theorem apply_abs_le_mul_of_one_le {H : Type*} [MulOneClass H] [LE H]
    [MulLeftMono H] [MulRightMono H] {f : G -> H}
    (h : forall x, 1 <= f x) (a : G) : f |a| <= f a * f (-a) :=
  apply_abs_le_mul_of_one_le' (h _) (h _)

end LinearOrderedAddCommGroup
