/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Lemmas for units in an ordered monoid
-/

public section

variable {M : Type*} [Monoid M] [LE M]

namespace Units

section MulLeftMono
variable [MulLeftMono M] (u : Mˣ) {a b : M}

/--
theorem `mulLECancellable_val` / 定理 `mulLECancellable_val`

English:
theorem mulLECancellable_val
  statement: MulLECancellable (↑u : M)
  proof: fun _ _ h => by
  simpa using mul_le_mul_right h ↑u⁻¹

中文:
定理 mulLECancellable_val
  结论: MulLECancellable (↑u : M)
  证明: fun _ _ h => by
  simpa using mul_le_mul_right h ↑u⁻¹

Depends on / 依赖: mul_le_mul_right
-/
theorem mulLECancellable_val : MulLECancellable (↑u : M) := fun _ _ h => by
  simpa using mul_le_mul_right h ↑u⁻¹

/--
theorem `mul_le_mul_iff_left` / 定理 `mul_le_mul_iff_left`

English:
theorem mul_le_mul_iff_left
  statement: u * a <= u * b ↔ a <= b
  proof: u.mulLECancellable_val.mul_le_mul_iff_left

中文:
定理 mul_le_mul_iff_left
  结论: u * a <= u * b ↔ a <= b
  证明: u.mulLECancellable_val.mul_le_mul_iff_left
-/
private theorem mul_le_mul_iff_left : u * a <= u * b ↔ a <= b :=
  u.mulLECancellable_val.mul_le_mul_iff_left

/--
theorem `inv_mul_le_iff` / 定理 `inv_mul_le_iff`

English:
theorem inv_mul_le_iff
  statement: u⁻¹ * a <= b ↔ a <= u * b
  proof: by
  rw [← u.mul_le_mul_iff_left]; rw [mul_inv_cancel_left]

中文:
定理 inv_mul_le_iff
  结论: u⁻¹ * a <= b ↔ a <= u * b
  证明: by
  rw [← u.mul_le_mul_iff_left]; rw [mul_inv_cancel_left]

Depends on / 依赖: mul_inv_cancel_left, mul_le_mul_iff_left, u.mul_le_mul_iff_left
-/
theorem inv_mul_le_iff : u⁻¹ * a <= b ↔ a <= u * b := by
  rw [← u.mul_le_mul_iff_left]; rw [mul_inv_cancel_left]

/--
theorem `le_inv_mul_iff` / 定理 `le_inv_mul_iff`

English:
theorem le_inv_mul_iff
  statement: a <= u⁻¹ * b ↔ u * a <= b
  proof: by
  rw [← u.mul_le_mul_iff_left]; rw [mul_inv_cancel_left]

中文:
定理 le_inv_mul_iff
  结论: a <= u⁻¹ * b ↔ u * a <= b
  证明: by
  rw [← u.mul_le_mul_iff_left]; rw [mul_inv_cancel_left]

Depends on / 依赖: mul_inv_cancel_left, mul_le_mul_iff_left, u.mul_le_mul_iff_left
-/
theorem le_inv_mul_iff : a <= u⁻¹ * b ↔ u * a <= b := by
  rw [← u.mul_le_mul_iff_left]; rw [mul_inv_cancel_left]

/--
theorem `one_le_inv` / 定理 `one_le_inv`

English:
theorem one_le_inv
  statement: (1 : M) <= u⁻¹ ↔ (u : M) <= 1
  proof: by
  rw [← u.mul_le_mul_iff_left]; rw [mul_one]; rw [mul_inv]

中文:
定理 one_le_inv
  结论: (1 : M) <= u⁻¹ ↔ (u : M) <= 1
  证明: by
  rw [← u.mul_le_mul_iff_left]; rw [mul_one]; rw [mul_inv]
-/
@[simp] theorem one_le_inv : (1 : M) <= u⁻¹ ↔ (u : M) <= 1 := by
  rw [← u.mul_le_mul_iff_left]; rw [mul_one]; rw [mul_inv]

/--
theorem `inv_le_one` / 定理 `inv_le_one`

English:
theorem inv_le_one
  statement: u⁻¹ <= (1 : M) ↔ (1 : M) <= u
  proof: by
  rw [← u.mul_le_mul_iff_left]; rw [mul_one]; rw [mul_inv]

中文:
定理 inv_le_one
  结论: u⁻¹ <= (1 : M) ↔ (1 : M) <= u
  证明: by
  rw [← u.mul_le_mul_iff_left]; rw [mul_one]; rw [mul_inv]
-/
@[simp] theorem inv_le_one : u⁻¹ <= (1 : M) ↔ (1 : M) <= u := by
  rw [← u.mul_le_mul_iff_left]; rw [mul_one]; rw [mul_inv]

/--
theorem `one_le_inv_mul` / 定理 `one_le_inv_mul`

English:
theorem one_le_inv_mul
  statement: 1 <= u⁻¹ * a ↔ u <= a
  proof: by
  rw [u.le_inv_mul_iff]; rw [mul_one]

中文:
定理 one_le_inv_mul
  结论: 1 <= u⁻¹ * a ↔ u <= a
  证明: by
  rw [u.le_inv_mul_iff]; rw [mul_one]

Depends on / 依赖: le_inv_mul_iff, mul_one, u.le_inv_mul_iff
-/
theorem one_le_inv_mul : 1 <= u⁻¹ * a ↔ u <= a := by
  rw [u.le_inv_mul_iff]; rw [mul_one]

/--
theorem `inv_mul_le_one` / 定理 `inv_mul_le_one`

English:
theorem inv_mul_le_one
  statement: u⁻¹ * a <= 1 ↔ a <= u
  proof: by
  rw [u.inv_mul_le_iff]; rw [mul_one]

alias ⟨le_mul_of_inv_mul_le, inv_mul_le_of_le_mul⟩ := inv_mul_le_iff
alias ⟨mul_le_of_le_inv_mul, le_inv_mul_of_mul_le⟩ := le_inv_mul_iff
alias ⟨le_of_one_le_inv, one_le_inv_of_le⟩ := one_le_inv
alias ⟨le_of_inv_le_one, inv_le_one_of_le⟩ := inv_le_one
alias ⟨le_of_one_le_inv_mul, one_le_inv_mul_of_le⟩ := one_le_inv_mul
alias ⟨le_of_inv_mul_le_one, inv_mul_le_one_of_le⟩ := inv_mul_le_one

中文:
定理 inv_mul_le_one
  结论: u⁻¹ * a <= 1 ↔ a <= u
  证明: by
  rw [u.inv_mul_le_iff]; rw [mul_one]

alias ⟨le_mul_of_inv_mul_le, inv_mul_le_of_le_mul⟩ := inv_mul_le_iff
alias ⟨mul_le_of_le_inv_mul, le_inv_mul_of_mul_le⟩ := le_inv_mul_iff
alias ⟨le_of_one_le_inv, one_le_inv_of_le⟩ := one_le_inv
alias ⟨le_of_inv_le_one, inv_le_one_of_le⟩ := inv_le_one
alias ⟨le_of_one_le_inv_mul, one_le_inv_mul_of_le⟩ := one_le_inv_mul
alias ⟨le_of_inv_mul_le_one, inv_mul_le_one_of_le⟩ := inv_mul_le_one

Depends on / 依赖: inv_mul_le_iff, mul_one, u.inv_mul_le_iff
-/
theorem inv_mul_le_one : u⁻¹ * a <= 1 ↔ a <= u := by
  rw [u.inv_mul_le_iff]; rw [mul_one]

alias ⟨le_mul_of_inv_mul_le, inv_mul_le_of_le_mul⟩ := inv_mul_le_iff
alias ⟨mul_le_of_le_inv_mul, le_inv_mul_of_mul_le⟩ := le_inv_mul_iff
alias ⟨le_of_one_le_inv, one_le_inv_of_le⟩ := one_le_inv
alias ⟨le_of_inv_le_one, inv_le_one_of_le⟩ := inv_le_one
alias ⟨le_of_one_le_inv_mul, one_le_inv_mul_of_le⟩ := one_le_inv_mul
alias ⟨le_of_inv_mul_le_one, inv_mul_le_one_of_le⟩ := inv_mul_le_one

end MulLeftMono

section MulRightMono
variable [MulRightMono M] {a b : M} (u : Mˣ)

/--
theorem `mul_le_mul_iff_right` / 定理 `mul_le_mul_iff_right`

English:
theorem mul_le_mul_iff_right
  statement: a * u <= b * u ↔ a <= b
  proof: ⟨(by simpa using mul_le_mul_left · ↑u⁻¹), (mul_le_mul_left · _)⟩

中文:
定理 mul_le_mul_iff_right
  结论: a * u <= b * u ↔ a <= b
  证明: ⟨(by simpa using mul_le_mul_left · ↑u⁻¹), (mul_le_mul_left · _)⟩
-/
private theorem mul_le_mul_iff_right : a * u <= b * u ↔ a <= b :=
  ⟨(by simpa using mul_le_mul_left · ↑u⁻¹), (mul_le_mul_left · _)⟩

/--
theorem `mul_inv_le_iff` / 定理 `mul_inv_le_iff`

English:
theorem mul_inv_le_iff
  statement: a * u⁻¹ <= b ↔ a <= b * u
  proof: by
  rw [← u.mul_le_mul_iff_right]; rw [u.inv_mul_cancel_right]

中文:
定理 mul_inv_le_iff
  结论: a * u⁻¹ <= b ↔ a <= b * u
  证明: by
  rw [← u.mul_le_mul_iff_right]; rw [u.inv_mul_cancel_right]

Depends on / 依赖: inv_mul_cancel_right, mul_le_mul_iff_right, u.inv_mul_cancel_right, u.mul_le_mul_iff_right
-/
theorem mul_inv_le_iff : a * u⁻¹ <= b ↔ a <= b * u := by
  rw [← u.mul_le_mul_iff_right]; rw [u.inv_mul_cancel_right]

/--
theorem `le_mul_inv_iff` / 定理 `le_mul_inv_iff`

English:
theorem le_mul_inv_iff
  statement: a <= b * u⁻¹ ↔ a * u <= b
  proof: by
  rw [← u.mul_le_mul_iff_right]; rw [inv_mul_cancel_right]

中文:
定理 le_mul_inv_iff
  结论: a <= b * u⁻¹ ↔ a * u <= b
  证明: by
  rw [← u.mul_le_mul_iff_right]; rw [inv_mul_cancel_right]

Depends on / 依赖: inv_mul_cancel_right, mul_le_mul_iff_right, u.mul_le_mul_iff_right
-/
theorem le_mul_inv_iff : a <= b * u⁻¹ ↔ a * u <= b := by
  rw [← u.mul_le_mul_iff_right]; rw [inv_mul_cancel_right]

/--
theorem `one_le_mul_inv` / 定理 `one_le_mul_inv`

English:
theorem one_le_mul_inv
  statement: 1 <= a * u⁻¹ ↔ u <= a
  proof: by
  rw [u.le_mul_inv_iff]; rw [one_mul]

中文:
定理 one_le_mul_inv
  结论: 1 <= a * u⁻¹ ↔ u <= a
  证明: by
  rw [u.le_mul_inv_iff]; rw [one_mul]

Depends on / 依赖: le_mul_inv_iff, one_mul, u.le_mul_inv_iff
-/
theorem one_le_mul_inv : 1 <= a * u⁻¹ ↔ u <= a := by
  rw [u.le_mul_inv_iff]; rw [one_mul]

/--
theorem `mul_inv_le_one` / 定理 `mul_inv_le_one`

English:
theorem mul_inv_le_one
  statement: a * u⁻¹ <= 1 ↔ a <= u
  proof: by
  rw [u.mul_inv_le_iff]; rw [one_mul]

alias ⟨le_mul_of_mul_inv_le, mul_inv_le_of_le_mul⟩ := mul_inv_le_iff
alias ⟨mul_le_of_le_mul_inv, le_mul_inv_of_mul_le⟩ := le_mul_inv_iff
alias ⟨le_of_one_le_mul_inv, one_le_mul_inv_of_le⟩ := one_le_mul_inv
alias ⟨le_of_mul_inv_le_one, mul_inv_le_one_of_le⟩ := mul_inv_le_one

中文:
定理 mul_inv_le_one
  结论: a * u⁻¹ <= 1 ↔ a <= u
  证明: by
  rw [u.mul_inv_le_iff]; rw [one_mul]

alias ⟨le_mul_of_mul_inv_le, mul_inv_le_of_le_mul⟩ := mul_inv_le_iff
alias ⟨mul_le_of_le_mul_inv, le_mul_inv_of_mul_le⟩ := le_mul_inv_iff
alias ⟨le_of_one_le_mul_inv, one_le_mul_inv_of_le⟩ := one_le_mul_inv
alias ⟨le_of_mul_inv_le_one, mul_inv_le_one_of_le⟩ := mul_inv_le_one

Depends on / 依赖: mul_inv_le_iff, one_mul, u.mul_inv_le_iff
-/
theorem mul_inv_le_one : a * u⁻¹ <= 1 ↔ a <= u := by
  rw [u.mul_inv_le_iff]; rw [one_mul]

alias ⟨le_mul_of_mul_inv_le, mul_inv_le_of_le_mul⟩ := mul_inv_le_iff
alias ⟨mul_le_of_le_mul_inv, le_mul_inv_of_mul_le⟩ := le_mul_inv_iff
alias ⟨le_of_one_le_mul_inv, one_le_mul_inv_of_le⟩ := one_le_mul_inv
alias ⟨le_of_mul_inv_le_one, mul_inv_le_one_of_le⟩ := mul_inv_le_one

end MulRightMono

end Units

namespace IsUnit

section MulLeftMono
variable [MulLeftMono M] {a b c : M} (ha : IsUnit a)

include ha

/--
theorem `mulLECancellable` / 定理 `mulLECancellable`

English:
theorem mulLECancellable
  statement: MulLECancellable a
  proof: ha.unit.mulLECancellable_val

中文:
定理 mulLECancellable
  结论: MulLECancellable a
  证明: ha.unit.mulLECancellable_val

Depends on / 依赖: ha.unit.mulLECancellable_val, mulLECancellable_val
-/
theorem mulLECancellable : MulLECancellable a :=
  ha.unit.mulLECancellable_val

/--
theorem `mul_le_mul_left` / 定理 `mul_le_mul_left`

English:
theorem mul_le_mul_left
  statement: a * b <= a * c ↔ b <= c
  proof: ha.unit.mul_le_mul_iff_left

alias ⟨le_of_mul_le_mul_left, _⟩ := mul_le_mul_left

中文:
定理 mul_le_mul_left
  结论: a * b <= a * c ↔ b <= c
  证明: ha.unit.mul_le_mul_iff_left

alias ⟨le_of_mul_le_mul_left, _⟩ := mul_le_mul_left

Depends on / 依赖: ha.unit.mul_le_mul_iff_left, mul_le_mul_iff_left
-/
theorem mul_le_mul_left : a * b <= a * c ↔ b <= c :=
  ha.unit.mul_le_mul_iff_left

alias ⟨le_of_mul_le_mul_left, _⟩ := mul_le_mul_left

end MulLeftMono

section MulRightMono
variable [MulRightMono M] {a b c : M} (hc : IsUnit c)

include hc

/--
theorem `mul_le_mul_right` / 定理 `mul_le_mul_right`

English:
theorem mul_le_mul_right
  statement: a * c <= b * c ↔ a <= b
  proof: hc.unit.mul_le_mul_iff_right

alias ⟨le_of_mul_le_mul_right, _⟩ := mul_le_mul_right

中文:
定理 mul_le_mul_right
  结论: a * c <= b * c ↔ a <= b
  证明: hc.unit.mul_le_mul_iff_right

alias ⟨le_of_mul_le_mul_right, _⟩ := mul_le_mul_right

Depends on / 依赖: hc.unit.mul_le_mul_iff_right, mul_le_mul_iff_right
-/
theorem mul_le_mul_right : a * c <= b * c ↔ a <= b :=
  hc.unit.mul_le_mul_iff_right

alias ⟨le_of_mul_le_mul_right, _⟩ := mul_le_mul_right

end MulRightMono

end IsUnit
