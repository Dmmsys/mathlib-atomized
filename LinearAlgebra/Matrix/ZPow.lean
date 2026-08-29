/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Integer powers of square matrices

In this file, we define integer power of matrices, relying on
the nonsingular inverse definition for negative powers.

## Implementation details

The main definition is a direct recursive call on the integer inductive type,
as provided by the `DivInvMonoid.Pow` default implementation.
The lemma names are taken from `Algebra.GroupWithZero.Power`.

## Tags

matrix inverse, matrix powers
-/

public section


open Matrix

namespace Matrix

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

local notation "M" => Matrix n' n' R
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DivInvMonoid (Matrix n' n' R)
  body: inferInstance
  __ : Inv M := inferInstance

中文:
实例 :
  签名: DivInvMonoid (Matrix n' n' R)
  定义体: inferInstance
  __ : Inv M := inferInstance
-/
noncomputable instance : DivInvMonoid (Matrix n' n' R) where
  __ : Monoid M := inferInstance
  __ : Inv M := inferInstance

section NatPow

@[simp]
/--
theorem `inv_pow'` / 定理 `inv_pow'`

English:
theorem inv_pow'
  given: (A : M) (n : Nat)
  statement: A⁻¹ ^ n = (A ^ n)⁻¹
  proof: by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ A, mul_inv_rev, ← ih, ← pow_succ']

中文:
定理 inv_pow'
  条件: (A : M) (n : 自然数)
  结论: A⁻¹ ^ n = (A ^ n)⁻¹
  证明: by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ A, mul_inv_rev, ← ih, ← pow_succ']

Depends on / 依赖: mul_inv_rev, pow_succ
-/
theorem inv_pow' (A : M) (n : Nat) : A⁻¹ ^ n = (A ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ A, mul_inv_rev, ← ih, ← pow_succ']

/--
theorem `pow_sub'` / 定理 `pow_sub'`

English:
theorem pow_sub'
  given: (A : M) {m n : Nat} (ha : IsUnit A.det) (h : n <= m)
  proof: by
  rw [← tsub_add_cancel_of_le h]; rw [pow_add]; rw [Matrix.mul_assoc]; rw [mul_nonsing_inv]; rw [tsub_add_cancel_of_le h]; rw [Matrix.mul_one]
  simpa using ha.pow n

中文:
定理 pow_sub'
  条件: (A : M) {m n : 自然数} (ha : IsUnit A.det) (h : n <= m)
  证明: by
  rw [← tsub_add_cancel_of_le h]; rw [pow_add]; rw [Matrix.mul_assoc]; rw [mul_nonsing_inv]; rw [tsub_add_cancel_of_le h]; rw [Matrix.mul_one]
  simpa using ha.pow n

Depends on / 依赖: Matrix, Matrix.mul_assoc, Matrix.mul_one, ha.pow, mul_assoc, mul_nonsing_inv, mul_one, pow_add, tsub_add_cancel_of_le
-/
theorem pow_sub' (A : M) {m n : Nat} (ha : IsUnit A.det) (h : n <= m) :
    A ^ (m - n) = A ^ m * (A ^ n)⁻¹ := by
  rw [← tsub_add_cancel_of_le h]; rw [pow_add]; rw [Matrix.mul_assoc]; rw [mul_nonsing_inv]; rw [tsub_add_cancel_of_le h]; rw [Matrix.mul_one]
  simpa using ha.pow n

/--
theorem `pow_inv_comm'` / 定理 `pow_inv_comm'`

English:
theorem pow_inv_comm'
  given: (A : M) (m n : Nat)
  statement: A⁻¹ ^ m * A ^ n = A ^ n * A⁻¹ ^ m
  proof: by
  induction n generalizing m with
  | zero => simp
  | succ n IH =>
    rcases m with m | m
    · simp
    rcases nonsing_inv_cancel_or_zero A with ⟨h, h'⟩ | h
    · calc
        A⁻¹ ^ (m + 1) * A ^ (n + 1) = A⁻¹ ^ m * (A⁻¹ * A) * A ^ n := by
          simp only [pow_succ A⁻¹, pow_succ' A, Matrix

中文:
定理 pow_inv_comm'
  条件: (A : M) (m n : 自然数)
  结论: A⁻¹ ^ m * A ^ n = A ^ n * A⁻¹ ^ m
  证明: by
  induction n generalizing m with
  | zero => simp
  | succ n IH =>
    rcases m with m | m
    · simp
    rcases nonsing_inv_cancel_or_zero A with ⟨h, h'⟩ | h
    · calc
        A⁻¹ ^ (m + 1) * A ^ (n + 1) = A⁻¹ ^ m * (A⁻¹ * A) * A ^ n := by
          simp only [pow_succ A⁻¹, pow_succ' A, Matrix

Depends on / 依赖: Matrix, Matrix.mul_assoc, Matrix.mul_one, generalizing, mul_assoc, mul_one, nonsing_inv_cancel_or_zero, pow_succ
-/
theorem pow_inv_comm' (A : M) (m n : Nat) : A⁻¹ ^ m * A ^ n = A ^ n * A⁻¹ ^ m := by
  induction n generalizing m with
  | zero => simp
  | succ n IH =>
    rcases m with m | m
    · simp
    rcases nonsing_inv_cancel_or_zero A with ⟨h, h'⟩ | h
    · calc
        A⁻¹ ^ (m + 1) * A ^ (n + 1) = A⁻¹ ^ m * (A⁻¹ * A) * A ^ n := by
          simp only [pow_succ A⁻¹, pow_succ' A, Matrix.mul_assoc]
        _ = A ^ n * A⁻¹ ^ m := by simp only [h, Matrix.mul_one, IH m]
        _ = A ^ n * (A * A⁻¹) * A⁻¹ ^ m := by simp only [h', Matrix.mul_one]
        _ = A ^ (n + 1) * A⁻¹ ^ (m + 1) := by
          simp only [pow_succ A, pow_succ' A⁻¹, Matrix.mul_assoc]
    · simp [h]

end NatPow

section ZPow

open Int

@[simp]
/--
theorem `one_zpow` / 定理 `one_zpow`

English:
theorem one_zpow
  statement: forall n : Int, (1 : M) ^ n = 1

中文:
定理 one_zpow
  结论: 对任意 n : 整数, (1 : M) ^ n = 1
-/
theorem one_zpow : forall n : Int, (1 : M) ^ n = 1
  | (n : Nat) => by rw [zpow_natCast, one_pow]
  | -[n+1] => by rw [zpow_negSucc, one_pow, inv_one]

/--
theorem `zero_zpow` / 定理 `zero_zpow`

English:
theorem zero_zpow
  statement: forall z : Int, z != 0 -> (0 : M) ^ z = 0

中文:
定理 zero_zpow
  结论: 对任意 z : 整数, z != 0 -> (0 : M) ^ z = 0
-/
theorem zero_zpow : forall z : Int, z != 0 -> (0 : M) ^ z = 0
  | (n : Nat), h => by
    rw [zpow_natCast]; rw [zero_pow]
    exact mod_cast h
  | -[n+1], _ => by simp [zero_pow n.succ_ne_zero]

/--
theorem `zero_zpow_eq` / 定理 `zero_zpow_eq`

English:
theorem zero_zpow_eq
  given: (n : Int)
  statement: (0 : M) ^ n = if n = 0 then 1 else 0
  proof: by
  split_ifs with h
  · rw [h, zpow_zero]
  · rw [zero_zpow _ h]

中文:
定理 zero_zpow_eq
  条件: (n : 整数)
  结论: (0 : M) ^ n = if n = 0 then 1 else 0
  证明: by
  split_ifs with h
  · rw [h, zpow_zero]
  · rw [zero_zpow _ h]

Depends on / 依赖: split_ifs, zero_zpow, zpow_zero
-/
theorem zero_zpow_eq (n : Int) : (0 : M) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, zpow_zero]
  · rw [zero_zpow _ h]

/--
theorem `inv_zpow` / 定理 `inv_zpow`

English:
theorem inv_zpow
  given: (A : M)
  statement: forall n : Int, A⁻¹ ^ n = (A ^ n)⁻¹

中文:
定理 inv_zpow
  条件: (A : M)
  结论: 对任意 n : 整数, A⁻¹ ^ n = (A ^ n)⁻¹
-/
theorem inv_zpow (A : M) : forall n : Int, A⁻¹ ^ n = (A ^ n)⁻¹
  | (n : Nat) => by rw [zpow_natCast, zpow_natCast, inv_pow']
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, inv_pow']

@[simp]
/--
theorem `zpow_neg_one` / 定理 `zpow_neg_one`

English:
theorem zpow_neg_one
  given: (A : M)
  statement: A ^ (-1 : Int) = A⁻¹
  proof: by
  simpa using DivInvMonoid.zpow_neg' 0 A

@[simp]

中文:
定理 zpow_neg_one
  条件: (A : M)
  结论: A ^ (-1 : 整数) = A⁻¹
  证明: by
  simpa using DivInvMonoid.zpow_neg' 0 A

@[simp]

Depends on / 依赖: DivInvMonoid, DivInvMonoid.zpow_neg, zpow_neg
-/
theorem zpow_neg_one (A : M) : A ^ (-1 : Int) = A⁻¹ := by
  simpa using DivInvMonoid.zpow_neg' 0 A

@[simp]
/--
theorem `zpow_neg_natCast` / 定理 `zpow_neg_natCast`

English:
theorem zpow_neg_natCast
  given: (A : M) (n : Nat)
  statement: A ^ (-n : Int) = (A ^ n)⁻¹
  proof: by
  cases n
  · simp
  · exact DivInvMonoid.zpow_neg' _ _

中文:
定理 zpow_neg_natCast
  条件: (A : M) (n : 自然数)
  结论: A ^ (-n : 整数) = (A ^ n)⁻¹
  证明: by
  cases n
  · simp
  · exact DivInvMonoid.zpow_neg' _ _

Depends on / 依赖: DivInvMonoid, DivInvMonoid.zpow_neg, zpow_neg
-/
theorem zpow_neg_natCast (A : M) (n : Nat) : A ^ (-n : Int) = (A ^ n)⁻¹ := by
  cases n
  · simp
  · exact DivInvMonoid.zpow_neg' _ _

/--
theorem `_root_.IsUnit.det_zpow` / 定理 `_root_.IsUnit.det_zpow`

English:
theorem _root_.IsUnit.det_zpow
  given: {A : M} (h : IsUnit A.det) (n : Int)
  statement: IsUnit (A ^ n).det
  proof: by
  rcases n with n | n
  · simpa using h.pow n
  · simpa using h.pow n.succ

中文:
定理 _root_.IsUnit.det_zpow
  条件: {A : M} (h : IsUnit A.det) (n : 整数)
  结论: IsUnit (A ^ n).det
  证明: by
  rcases n with n | n
  · simpa using h.pow n
  · simpa using h.pow n.succ

Depends on / 依赖: h.pow, n.succ
-/
theorem _root_.IsUnit.det_zpow {A : M} (h : IsUnit A.det) (n : Int) : IsUnit (A ^ n).det := by
  rcases n with n | n
  · simpa using h.pow n
  · simpa using h.pow n.succ

/--
theorem `isUnit_det_zpow_iff` / 定理 `isUnit_det_zpow_iff`

English:
theorem isUnit_det_zpow_iff
  given: {A : M} {z : Int}
  statement: IsUnit (A ^ z).det ↔ IsUnit A.det ∨ z = 0
  proof: by
  induction z with
  | zero => simp
  | succ z =>
    rw [← Int.natCast_succ]; rw [zpow_natCast]; rw [det_pow]; rw [isUnit_pow_succ_iff]; rw [← Int.ofNat_zero]; rw [Int.ofNat_inj]
    simp
  | pred z =>
    rw [← neg_add']; rw [← Int.natCast_succ]; rw [zpow_neg_natCast]; rw [isUnit_nonsing_inv_de

中文:
定理 isUnit_det_zpow_iff
  条件: {A : M} {z : 整数}
  结论: IsUnit (A ^ z).det ↔ IsUnit A.det ∨ z = 0
  证明: by
  induction z with
  | zero => simp
  | succ z =>
    rw [← Int.natCast_succ]; rw [zpow_natCast]; rw [det_pow]; rw [isUnit_pow_succ_iff]; rw [← Int.ofNat_zero]; rw [Int.ofNat_inj]
    simp
  | pred z =>
    rw [← neg_add']; rw [← Int.natCast_succ]; rw [zpow_neg_natCast]; rw [isUnit_nonsing_inv_de

Depends on / 依赖: Int.natCast_succ, Int.ofNat_inj, Int.ofNat_zero, det_pow, isUnit_nonsing_inv_det_iff, isUnit_pow_succ_iff, natCast_succ, neg_add, neg_eq_zero, ofNat_inj, ofNat_zero, zpow_natCast, zpow_neg_natCast
-/
theorem isUnit_det_zpow_iff {A : M} {z : Int} : IsUnit (A ^ z).det ↔ IsUnit A.det ∨ z = 0 := by
  induction z with
  | zero => simp
  | succ z =>
    rw [← Int.natCast_succ]; rw [zpow_natCast]; rw [det_pow]; rw [isUnit_pow_succ_iff]; rw [← Int.ofNat_zero]; rw [Int.ofNat_inj]
    simp
  | pred z =>
    rw [← neg_add']; rw [← Int.natCast_succ]; rw [zpow_neg_natCast]; rw [isUnit_nonsing_inv_det_iff]; rw [det_pow]; rw [isUnit_pow_succ_iff]; rw [neg_eq_zero]; rw [← Int.ofNat_zero]; rw [Int.ofNat_inj]
    simp

/--
theorem `zpow_neg` / 定理 `zpow_neg`

English:
theorem zpow_neg
  given: {A : M} (h : IsUnit A.det)
  statement: forall n : Int, A ^ (-n) = (A ^ n)⁻¹

中文:
定理 zpow_neg
  条件: {A : M} (h : IsUnit A.det)
  结论: 对任意 n : 整数, A ^ (-n) = (A ^ n)⁻¹
-/
theorem zpow_neg {A : M} (h : IsUnit A.det) : forall n : Int, A ^ (-n) = (A ^ n)⁻¹
  | (n : Nat) => zpow_neg_natCast _ _
  | -[n+1] => by
    rw [zpow_negSucc]; rw [neg_negSucc]; rw [zpow_natCast]; rw [nonsing_inv_nonsing_inv]
    rw [det_pow]
    exact h.pow _

/--
theorem `inv_zpow'` / 定理 `inv_zpow'`

English:
theorem inv_zpow'
  given: {A : M} (h : IsUnit A.det) (n : Int)
  statement: A⁻¹ ^ n = A ^ (-n)
  proof: by
  rw [zpow_neg h]; rw [inv_zpow]

中文:
定理 inv_zpow'
  条件: {A : M} (h : IsUnit A.det) (n : 整数)
  结论: A⁻¹ ^ n = A ^ (-n)
  证明: by
  rw [zpow_neg h]; rw [inv_zpow]

Depends on / 依赖: inv_zpow, zpow_neg
-/
theorem inv_zpow' {A : M} (h : IsUnit A.det) (n : Int) : A⁻¹ ^ n = A ^ (-n) := by
  rw [zpow_neg h]; rw [inv_zpow]

/--
theorem `zpow_add_one` / 定理 `zpow_add_one`

English:
theorem zpow_add_one
  given: {A : M} (h : IsUnit A.det)
  statement: forall n : Int, A ^ (n + 1) = A ^ n * A
  proof: by
        rw [neg_add]; rw [neg_add_cancel_right]; rw [zpow_neg h]; rw [zpow_natCast]
      _ = (A * A ^ n)⁻¹ * A := by
        rw [mul_inv_rev]; rw [Matrix.mul_assoc]; rw [nonsing_inv_mul _ h]; rw [Matrix.mul_one]
      _ = A ^ (-(n + 1 : Int)) * A := by
        rw [zpow_neg h]; rw [← Int.natCast_

中文:
定理 zpow_add_one
  条件: {A : M} (h : IsUnit A.det)
  结论: 对任意 n : 整数, A ^ (n + 1) = A ^ n * A
  证明: by
        rw [neg_add]; rw [neg_add_cancel_right]; rw [zpow_neg h]; rw [zpow_natCast]
      _ = (A * A ^ n)⁻¹ * A := by
        rw [mul_inv_rev]; rw [Matrix.mul_assoc]; rw [nonsing_inv_mul _ h]; rw [Matrix.mul_one]
      _ = A ^ (-(n + 1 : Int)) * A := by
        rw [zpow_neg h]; rw [← Int.natCast_

Depends on / 依赖: Int.natCast_succ, Matrix, Matrix.mul_assoc, Matrix.mul_one, mul_assoc, mul_inv_rev, mul_one, natCast_succ, neg_add, neg_add_cancel_right, nonsing_inv_mul, pow_succ, zpow_natCast, zpow_neg
-/
theorem zpow_add_one {A : M} (h : IsUnit A.det) : forall n : Int, A ^ (n + 1) = A ^ n * A
  | (n : Nat) => by simp only [← Nat.cast_succ, pow_succ, zpow_natCast]
  | -[n+1] =>
    calc
      A ^ (-(n + 1) + 1 : Int) = (A ^ n)⁻¹ := by
        rw [neg_add]; rw [neg_add_cancel_right]; rw [zpow_neg h]; rw [zpow_natCast]
      _ = (A * A ^ n)⁻¹ * A := by
        rw [mul_inv_rev]; rw [Matrix.mul_assoc]; rw [nonsing_inv_mul _ h]; rw [Matrix.mul_one]
      _ = A ^ (-(n + 1 : Int)) * A := by
        rw [zpow_neg h]; rw [← Int.natCast_succ]; rw [zpow_natCast]; rw [pow_succ']

/--
theorem `zpow_sub_one` / 定理 `zpow_sub_one`

English:
theorem zpow_sub_one
  given: {A : M} (h : IsUnit A.det) (n : Int)
  statement: A ^ (n - 1) = A ^ n * A⁻¹
  proof: calc
    A ^ (n - 1) = A ^ (n - 1) * A * A⁻¹ := by
      rw [mul_assoc]; rw [mul_nonsing_inv _ h]; rw [mul_one]
    _ = A ^ n * A⁻¹ := by rw [← zpow_add_one h, sub_add_cancel]

中文:
定理 zpow_sub_one
  条件: {A : M} (h : IsUnit A.det) (n : 整数)
  结论: A ^ (n - 1) = A ^ n * A⁻¹
  证明: calc
    A ^ (n - 1) = A ^ (n - 1) * A * A⁻¹ := by
      rw [mul_assoc]; rw [mul_nonsing_inv _ h]; rw [mul_one]
    _ = A ^ n * A⁻¹ := by rw [← zpow_add_one h, sub_add_cancel]

Depends on / 依赖: mul_assoc, mul_nonsing_inv, mul_one, sub_add_cancel, zpow_add_one
-/
theorem zpow_sub_one {A : M} (h : IsUnit A.det) (n : Int) : A ^ (n - 1) = A ^ n * A⁻¹ :=
  calc
    A ^ (n - 1) = A ^ (n - 1) * A * A⁻¹ := by
      rw [mul_assoc]; rw [mul_nonsing_inv _ h]; rw [mul_one]
    _ = A ^ n * A⁻¹ := by rw [← zpow_add_one h, sub_add_cancel]

/--
theorem `zpow_add` / 定理 `zpow_add`

English:
theorem zpow_add
  given: {A : M} (ha : IsUnit A.det) (m n : Int)
  statement: A ^ (m + n) = A ^ m * A ^ n
  proof: by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← add_assoc, zpow_add_one ha, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one ha, ← mul_assoc, ← ihn, ← zpow_sub_one ha, add_sub_assoc]

中文:
定理 zpow_add
  条件: {A : M} (ha : IsUnit A.det) (m n : 整数)
  结论: A ^ (m + n) = A ^ m * A ^ n
  证明: by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← add_assoc, zpow_add_one ha, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one ha, ← mul_assoc, ← ihn, ← zpow_sub_one ha, add_sub_assoc]

Depends on / 依赖: add_assoc, add_sub_assoc, mul_assoc, zpow_add_one, zpow_sub_one
-/
theorem zpow_add {A : M} (ha : IsUnit A.det) (m n : Int) : A ^ (m + n) = A ^ m * A ^ n := by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← add_assoc, zpow_add_one ha, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one ha, ← mul_assoc, ← ihn, ← zpow_sub_one ha, add_sub_assoc]

/--
theorem `zpow_add_of_nonpos` / 定理 `zpow_add_of_nonpos`

English:
theorem zpow_add_of_nonpos
  given: {A : M} {m n : Int} (hm : m <= 0) (hn : n <= 0)
  proof: by
  rcases nonsing_inv_cancel_or_zero A with (⟨h, _⟩ | h)
  · exact zpow_add (isUnit_det_of_left_inverse h) m n
  · obtain ⟨k, rfl⟩ := exists_eq_neg_ofNat hm
    obtain ⟨l, rfl⟩ := exists_eq_neg_ofNat hn
    simp_rw [← neg_add, ← Int.natCast_add, zpow_neg_natCast, ← inv_pow', h, pow_add]

中文:
定理 zpow_add_of_nonpos
  条件: {A : M} {m n : 整数} (hm : m <= 0) (hn : n <= 0)
  证明: by
  rcases nonsing_inv_cancel_or_zero A with (⟨h, _⟩ | h)
  · exact zpow_add (isUnit_det_of_left_inverse h) m n
  · obtain ⟨k, rfl⟩ := exists_eq_neg_ofNat hm
    obtain ⟨l, rfl⟩ := exists_eq_neg_ofNat hn
    simp_rw [← neg_add, ← Int.natCast_add, zpow_neg_natCast, ← inv_pow', h, pow_add]

Depends on / 依赖: Int.natCast_add, exists_eq_neg_ofNat, inv_pow, isUnit_det_of_left_inverse, natCast_add, neg_add, nonsing_inv_cancel_or_zero, pow_add, simp_rw, zpow_add, zpow_neg_natCast
-/
theorem zpow_add_of_nonpos {A : M} {m n : Int} (hm : m <= 0) (hn : n <= 0) :
    A ^ (m + n) = A ^ m * A ^ n := by
  rcases nonsing_inv_cancel_or_zero A with (⟨h, _⟩ | h)
  · exact zpow_add (isUnit_det_of_left_inverse h) m n
  · obtain ⟨k, rfl⟩ := exists_eq_neg_ofNat hm
    obtain ⟨l, rfl⟩ := exists_eq_neg_ofNat hn
    simp_rw [← neg_add, ← Int.natCast_add, zpow_neg_natCast, ← inv_pow', h, pow_add]

/--
theorem `zpow_add_of_nonneg` / 定理 `zpow_add_of_nonneg`

English:
theorem zpow_add_of_nonneg
  given: {A : M} {m n : Int} (hm : 0 <= m) (hn : 0 <= n)
  proof: by
  obtain ⟨k, rfl⟩ := eq_ofNat_of_zero_le hm
  obtain ⟨l, rfl⟩ := eq_ofNat_of_zero_le hn
  rw [← Int.natCast_add]; rw [zpow_natCast]; rw [zpow_natCast]; rw [zpow_natCast]; rw [pow_add]

中文:
定理 zpow_add_of_nonneg
  条件: {A : M} {m n : 整数} (hm : 0 <= m) (hn : 0 <= n)
  证明: by
  obtain ⟨k, rfl⟩ := eq_ofNat_of_zero_le hm
  obtain ⟨l, rfl⟩ := eq_ofNat_of_zero_le hn
  rw [← Int.natCast_add]; rw [zpow_natCast]; rw [zpow_natCast]; rw [zpow_natCast]; rw [pow_add]

Depends on / 依赖: Int.natCast_add, eq_ofNat_of_zero_le, natCast_add, pow_add, zpow_natCast
-/
theorem zpow_add_of_nonneg {A : M} {m n : Int} (hm : 0 <= m) (hn : 0 <= n) :
    A ^ (m + n) = A ^ m * A ^ n := by
  obtain ⟨k, rfl⟩ := eq_ofNat_of_zero_le hm
  obtain ⟨l, rfl⟩ := eq_ofNat_of_zero_le hn
  rw [← Int.natCast_add]; rw [zpow_natCast]; rw [zpow_natCast]; rw [zpow_natCast]; rw [pow_add]

/--
theorem `zpow_one_add` / 定理 `zpow_one_add`

English:
theorem zpow_one_add
  given: {A : M} (h : IsUnit A.det) (i : Int)
  statement: A ^ (1 + i) = A * A ^ i
  proof: by
  rw [zpow_add h]; rw [zpow_one]

中文:
定理 zpow_one_add
  条件: {A : M} (h : IsUnit A.det) (i : 整数)
  结论: A ^ (1 + i) = A * A ^ i
  证明: by
  rw [zpow_add h]; rw [zpow_one]

Depends on / 依赖: zpow_add, zpow_one
-/
theorem zpow_one_add {A : M} (h : IsUnit A.det) (i : Int) : A ^ (1 + i) = A * A ^ i := by
  rw [zpow_add h]; rw [zpow_one]

/--
theorem `SemiconjBy.zpow_right` / 定理 `SemiconjBy.zpow_right`

English:
theorem SemiconjBy.zpow_right
  statement: {A X Y : M} (hx : IsUnit X.det) (hy : IsUnit Y.det)
  proof: by
      rw [det_pow]
      exact hx.pow n.succ
    have hy' : IsUnit (Y ^ n.succ).det := by
      rw [det_pow]
      exact hy.pow n.succ
    rw [zpow_negSucc]; rw [zpow_negSucc]; rw [nonsing_inv_apply _ hx']; rw [nonsing_inv_apply _ hy']; rw [SemiconjBy]
    refine (isRegular_of_isLeftRegular_det h

中文:
定理 SemiconjBy.zpow_right
  结论: {A X Y : M} (hx : IsUnit X.det) (hy : IsUnit Y.det)
  证明: by
      rw [det_pow]
      exact hx.pow n.succ
    have hy' : IsUnit (Y ^ n.succ).det := by
      rw [det_pow]
      exact hy.pow n.succ
    rw [zpow_negSucc]; rw [zpow_negSucc]; rw [nonsing_inv_apply _ hx']; rw [nonsing_inv_apply _ hy']; rw [SemiconjBy]
    refine (isRegular_of_isLeftRegular_det h

Depends on / 依赖: IsUnit, Matrix, Matrix.mul_assoc, Matrix.mul_smul, SemiconjBy, det_pow, h.pow_right, hx.pow, hy.pow, isRegular, isRegular.left, isRegular_of_isLeftRegular_det, mul_adjugate, mul_assoc, mul_smul, n.succ, nonsing_inv_apply, pow_right, zpow_negSucc
-/
theorem SemiconjBy.zpow_right {A X Y : M} (hx : IsUnit X.det) (hy : IsUnit Y.det)
    (h : SemiconjBy A X Y) : forall m : Int, SemiconjBy A (X ^ m) (Y ^ m)
  | (n : Nat) => by simp [h.pow_right n]
  | -[n+1] => by
    have hx' : IsUnit (X ^ n.succ).det := by
      rw [det_pow]
      exact hx.pow n.succ
    have hy' : IsUnit (Y ^ n.succ).det := by
      rw [det_pow]
      exact hy.pow n.succ
    rw [zpow_negSucc]; rw [zpow_negSucc]; rw [nonsing_inv_apply _ hx']; rw [nonsing_inv_apply _ hy']; rw [SemiconjBy]
    refine (isRegular_of_isLeftRegular_det hy'.isRegular.left).left ?_
    dsimp only
    rw [← mul_assoc]; rw [← (h.pow_right n.succ).eq]; rw [mul_assoc]; rw [Matrix.mul_smul]; rw [mul_adjugate]; rw [← Matrix.mul_assoc]; rw [Matrix.mul_smul (Y ^ _) (↑hy'.unit⁻¹ : R)]; rw [mul_adjugate]; rw [smul_smul]; rw [smul_smul]; rw [hx'.val_inv_mul]; rw [hy'.val_inv_mul]; rw [one_smul]; rw [Matrix.mul_one]; rw [Matrix.one_mul]

/--
theorem `Commute.zpow_right` / 定理 `Commute.zpow_right`

English:
theorem Commute.zpow_right
  given: {A B : M} (h : Commute A B) (m : Int)
  statement: Commute A (B ^ m)
  proof: by
  rcases nonsing_inv_cancel_or_zero B with (⟨hB, _⟩ | hB)
  · refine SemiconjBy.zpow_right ?_ ?_ h _ <;> exact isUnit_det_of_left_inverse hB
  · cases m
    · simpa using h.pow_right _
    · simp [← inv_pow', hB]

中文:
定理 Commute.zpow_right
  条件: {A B : M} (h : Commute A B) (m : 整数)
  结论: Commute A (B ^ m)
  证明: by
  rcases nonsing_inv_cancel_or_zero B with (⟨hB, _⟩ | hB)
  · refine SemiconjBy.zpow_right ?_ ?_ h _ <;> exact isUnit_det_of_left_inverse hB
  · cases m
    · simpa using h.pow_right _
    · simp [← inv_pow', hB]
-/
theorem Commute.zpow_right {A B : M} (h : Commute A B) (m : Int) : Commute A (B ^ m) := by
  rcases nonsing_inv_cancel_or_zero B with (⟨hB, _⟩ | hB)
  · refine SemiconjBy.zpow_right ?_ ?_ h _ <;> exact isUnit_det_of_left_inverse hB
  · cases m
    · simpa using h.pow_right _
    · simp [← inv_pow', hB]

/--
theorem `Commute.zpow_left` / 定理 `Commute.zpow_left`

English:
theorem Commute.zpow_left
  given: {A B : M} (h : Commute A B) (m : Int)
  statement: Commute (A ^ m) B
  proof: (Commute.zpow_right h.symm m).symm

中文:
定理 Commute.zpow_left
  条件: {A B : M} (h : Commute A B) (m : 整数)
  结论: Commute (A ^ m) B
  证明: (Commute.zpow_right h.symm m).symm
-/
theorem Commute.zpow_left {A B : M} (h : Commute A B) (m : Int) : Commute (A ^ m) B :=
  (Commute.zpow_right h.symm m).symm

/--
theorem `Commute.zpow_zpow` / 定理 `Commute.zpow_zpow`

English:
theorem Commute.zpow_zpow
  given: {A B : M} (h : Commute A B) (m n : Int)
  statement: Commute (A ^ m) (B ^ n)
  proof: Commute.zpow_right (Commute.zpow_left h _) _

中文:
定理 Commute.zpow_zpow
  条件: {A B : M} (h : Commute A B) (m n : 整数)
  结论: Commute (A ^ m) (B ^ n)
  证明: Commute.zpow_right (Commute.zpow_left h _) _

Depends on / 依赖: Commute, Commute.zpow_left, Commute.zpow_right, zpow_left, zpow_right
-/
theorem Commute.zpow_zpow {A B : M} (h : Commute A B) (m n : Int) : Commute (A ^ m) (B ^ n) :=
  Commute.zpow_right (Commute.zpow_left h _) _

/--
theorem `Commute.zpow_self` / 定理 `Commute.zpow_self`

English:
theorem Commute.zpow_self
  given: (A : M) (n : Int)
  statement: Commute (A ^ n) A
  proof: Commute.zpow_left (Commute.refl A) _

中文:
定理 Commute.zpow_self
  条件: (A : M) (n : 整数)
  结论: Commute (A ^ n) A
  证明: Commute.zpow_left (Commute.refl A) _

Depends on / 依赖: Commute, Commute.refl, Commute.zpow_left, zpow_left
-/
theorem Commute.zpow_self (A : M) (n : Int) : Commute (A ^ n) A :=
  Commute.zpow_left (Commute.refl A) _

/--
theorem `Commute.self_zpow` / 定理 `Commute.self_zpow`

English:
theorem Commute.self_zpow
  given: (A : M) (n : Int)
  statement: Commute A (A ^ n)
  proof: Commute.zpow_right (Commute.refl A) _

中文:
定理 Commute.self_zpow
  条件: (A : M) (n : 整数)
  结论: Commute A (A ^ n)
  证明: Commute.zpow_right (Commute.refl A) _

Depends on / 依赖: Commute, Commute.refl, Commute.zpow_right, zpow_right
-/
theorem Commute.self_zpow (A : M) (n : Int) : Commute A (A ^ n) :=
  Commute.zpow_right (Commute.refl A) _

/--
theorem `Commute.zpow_zpow_self` / 定理 `Commute.zpow_zpow_self`

English:
theorem Commute.zpow_zpow_self
  given: (A : M) (m n : Int)
  statement: Commute (A ^ m) (A ^ n)
  proof: Commute.zpow_zpow (Commute.refl A) _ _

中文:
定理 Commute.zpow_zpow_self
  条件: (A : M) (m n : 整数)
  结论: Commute (A ^ m) (A ^ n)
  证明: Commute.zpow_zpow (Commute.refl A) _ _

Depends on / 依赖: Commute, Commute.refl, Commute.zpow_zpow, zpow_zpow
-/
theorem Commute.zpow_zpow_self (A : M) (m n : Int) : Commute (A ^ m) (A ^ n) :=
  Commute.zpow_zpow (Commute.refl A) _ _

/--
theorem `zpow_add_one_of_ne_neg_one` / 定理 `zpow_add_one_of_ne_neg_one`

English:
theorem zpow_add_one_of_ne_neg_one
  given: {A : M}
  statement: forall n : Int, n != -1 -> A ^ (n + 1) = A ^ n * A

中文:
定理 zpow_add_one_of_ne_neg_one
  条件: {A : M}
  结论: 对任意 n : 整数, n != -1 -> A ^ (n + 1) = A ^ n * A
-/
theorem zpow_add_one_of_ne_neg_one {A : M} : forall n : Int, n != -1 -> A ^ (n + 1) = A ^ n * A
  | (n : Nat), _ => by simp only [pow_succ, ← Nat.cast_succ, zpow_natCast]
  | -1, h => absurd rfl h
  | -((n : Nat) + 2), _ => by
    rcases nonsing_inv_cancel_or_zero A with (⟨h, _⟩ | h)
    · apply zpow_add_one (isUnit_det_of_left_inverse h)
    · change A ^ (-((n + 1 : Nat) : Int)) = A ^ (-((n + 2 : Nat) : Int)) * A
      simp_rw [zpow_neg_natCast, ← inv_pow', h, zero_pow <| Nat.succ_ne_zero _, zero_mul]

/--
theorem `zpow_mul` / 定理 `zpow_mul`

English:
theorem zpow_mul
  given: (A : M) (h : IsUnit A.det)
  statement: forall m n : Int, A ^ (m * n) = (A ^ m) ^ n

中文:
定理 zpow_mul
  条件: (A : M) (h : IsUnit A.det)
  结论: 对任意 m n : 整数, A ^ (m * n) = (A ^ m) ^ n
-/
theorem zpow_mul (A : M) (h : IsUnit A.det) : forall m n : Int, A ^ (m * n) = (A ^ m) ^ n
  | (m : Nat), (n : Nat) => by
    rw [zpow_natCast]; rw [zpow_natCast]; rw [← pow_mul]; rw [← zpow_natCast]; rw [Int.natCast_mul]
  | (m : Nat), -[n+1] => by
    rw [zpow_natCast]; rw [zpow_negSucc]; rw [← pow_mul]; rw [ofNat_mul_negSucc]; rw [zpow_neg_natCast]
  | -[m+1], (n : Nat) => by
    rw [zpow_natCast]; rw [zpow_negSucc]; rw [← inv_pow']; rw [← pow_mul]; rw [negSucc_mul_ofNat]; rw [zpow_neg_natCast]; rw [inv_pow']
  | -[m+1], -[n+1] => by
    rw [zpow_negSucc]; rw [zpow_negSucc]; rw [negSucc_mul_negSucc]; rw [← Int.natCast_mul]; rw [zpow_natCast]; rw [inv_pow']; rw [← pow_mul]; rw [nonsing_inv_nonsing_inv]
    rw [det_pow]
    exact h.pow _

/--
theorem `zpow_mul'` / 定理 `zpow_mul'`

English:
theorem zpow_mul'
  given: (A : M) (h : IsUnit A.det) (m n : Int)
  statement: A ^ (m * n) = (A ^ n) ^ m
  proof: by
  rw [mul_comm]; rw [zpow_mul _ h]


@[simp, norm_cast]

中文:
定理 zpow_mul'
  条件: (A : M) (h : IsUnit A.det) (m n : 整数)
  结论: A ^ (m * n) = (A ^ n) ^ m
  证明: by
  rw [mul_comm]; rw [zpow_mul _ h]


@[simp, norm_cast]

Depends on / 依赖: mul_comm, zpow_mul
-/
theorem zpow_mul' (A : M) (h : IsUnit A.det) (m n : Int) : A ^ (m * n) = (A ^ n) ^ m := by
  rw [mul_comm]; rw [zpow_mul _ h]


@[simp, norm_cast]
/--
theorem `coe_units_zpow` / 定理 `coe_units_zpow`

English:
theorem coe_units_zpow
  given: (u : Mˣ)
  statement: forall n : Int, ((u ^ n : Mˣ) : M) = (u : M) ^ n

中文:
定理 coe_units_zpow
  条件: (u : Mˣ)
  结论: 对任意 n : 整数, ((u ^ n : Mˣ) : M) = (u : M) ^ n
-/
theorem coe_units_zpow (u : Mˣ) : forall n : Int, ((u ^ n : Mˣ) : M) = (u : M) ^ n
  | (n : Nat) => by rw [zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
  | -[k+1] => by
    rw [zpow_negSucc]; rw [zpow_negSucc]; rw [← inv_pow]; rw [u⁻¹.val_pow_eq_pow_val]; rw [← inv_pow']; rw [coe_units_inv]

/--
theorem `zpow_ne_zero_of_isUnit_det` / 定理 `zpow_ne_zero_of_isUnit_det`

English:
theorem zpow_ne_zero_of_isUnit_det
  statement: [Nonempty n'] [Nontrivial R] {A : M} (ha : IsUnit A.det)
  proof: by
  have := ha.det_zpow z
  contrapose this
  rw [this]; rw [det_zero]
  exact not_isUnit_zero

中文:
定理 zpow_ne_zero_of_isUnit_det
  结论: [Nonempty n'] [Nontrivial R] {A : M} (ha : IsUnit A.det)
  证明: by
  have := ha.det_zpow z
  contrapose this
  rw [this]; rw [det_zero]
  exact not_isUnit_zero

Depends on / 依赖: contrapose, det_zero, det_zpow, ha.det_zpow, not_isUnit_zero
-/
theorem zpow_ne_zero_of_isUnit_det [Nonempty n'] [Nontrivial R] {A : M} (ha : IsUnit A.det)
    (z : Int) : A ^ z != 0 := by
  have := ha.det_zpow z
  contrapose this
  rw [this]; rw [det_zero]
  exact not_isUnit_zero

/--
theorem `zpow_sub` / 定理 `zpow_sub`

English:
theorem zpow_sub
  given: {A : M} (ha : IsUnit A.det) (z1 z2 : Int)
  statement: A ^ (z1 - z2) = A ^ z1 / A ^ z2
  proof: by
  rw [sub_eq_add_neg]; rw [zpow_add ha]; rw [zpow_neg ha]; rw [div_eq_mul_inv]

中文:
定理 zpow_sub
  条件: {A : M} (ha : IsUnit A.det) (z1 z2 : 整数)
  结论: A ^ (z1 - z2) = A ^ z1 / A ^ z2
  证明: by
  rw [sub_eq_add_neg]; rw [zpow_add ha]; rw [zpow_neg ha]; rw [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, sub_eq_add_neg, zpow_add, zpow_neg
-/
theorem zpow_sub {A : M} (ha : IsUnit A.det) (z1 z2 : Int) : A ^ (z1 - z2) = A ^ z1 / A ^ z2 := by
  rw [sub_eq_add_neg]; rw [zpow_add ha]; rw [zpow_neg ha]; rw [div_eq_mul_inv]

/--
theorem `Commute.mul_zpow` / 定理 `Commute.mul_zpow`

English:
theorem Commute.mul_zpow
  given: {A B : M} (h : Commute A B)
  statement: forall i : Int, (A * B) ^ i = A ^ i * B ^ i

中文:
定理 Commute.mul_zpow
  条件: {A B : M} (h : Commute A B)
  结论: 对任意 i : 整数, (A * B) ^ i = A ^ i * B ^ i
-/
theorem Commute.mul_zpow {A B : M} (h : Commute A B) : forall i : Int, (A * B) ^ i = A ^ i * B ^ i
  | (n : Nat) => by simp [h.mul_pow n]
  | -[n+1] => by
    rw [zpow_negSucc]; rw [zpow_negSucc]; rw [zpow_negSucc]; rw [← mul_inv_rev]; rw [h.mul_pow n.succ]; rw [(h.pow_pow _ _).eq]

/--
theorem `zpow_neg_mul_zpow_self` / 定理 `zpow_neg_mul_zpow_self`

English:
theorem zpow_neg_mul_zpow_self
  given: (n : Int) {A : M} (h : IsUnit A.det)
  statement: A ^ (-n) * A ^ n = 1
  proof: by
  rw [zpow_neg h]; rw [nonsing_inv_mul _ (h.det_zpow _)]

中文:
定理 zpow_neg_mul_zpow_self
  条件: (n : 整数) {A : M} (h : IsUnit A.det)
  结论: A ^ (-n) * A ^ n = 1
  证明: by
  rw [zpow_neg h]; rw [nonsing_inv_mul _ (h.det_zpow _)]

Depends on / 依赖: det_zpow, h.det_zpow, nonsing_inv_mul, zpow_neg
-/
theorem zpow_neg_mul_zpow_self (n : Int) {A : M} (h : IsUnit A.det) : A ^ (-n) * A ^ n = 1 := by
  rw [zpow_neg h]; rw [nonsing_inv_mul _ (h.det_zpow _)]

/--
theorem `one_div_pow` / 定理 `one_div_pow`

English:
theorem one_div_pow
  given: {A : M} (n : Nat)
  statement: (1 / A) ^ n = 1 / A ^ n
  proof: by simp only [one_div, inv_pow']

中文:
定理 one_div_pow
  条件: {A : M} (n : 自然数)
  结论: (1 / A) ^ n = 1 / A ^ n
  证明: by simp only [one_div, inv_pow']

Depends on / 依赖: inv_pow, one_div
-/
theorem one_div_pow {A : M} (n : Nat) : (1 / A) ^ n = 1 / A ^ n := by simp only [one_div, inv_pow']

/--
theorem `one_div_zpow` / 定理 `one_div_zpow`

English:
theorem one_div_zpow
  given: {A : M} (n : Int)
  statement: (1 / A) ^ n = 1 / A ^ n
  proof: by simp only [one_div, inv_zpow]

@[simp]

中文:
定理 one_div_zpow
  条件: {A : M} (n : 整数)
  结论: (1 / A) ^ n = 1 / A ^ n
  证明: by simp only [one_div, inv_zpow]

@[simp]

Depends on / 依赖: inv_zpow, one_div
-/
theorem one_div_zpow {A : M} (n : Int) : (1 / A) ^ n = 1 / A ^ n := by simp only [one_div, inv_zpow]

@[simp]
/--
theorem `transpose_zpow` / 定理 `transpose_zpow`

English:
theorem transpose_zpow
  given: (A : M)
  statement: forall n : Int, (A ^ n)ᵀ = Aᵀ ^ n

中文:
定理 transpose_zpow
  条件: (A : M)
  结论: 对任意 n : 整数, (A ^ n)ᵀ = Aᵀ ^ n
-/
theorem transpose_zpow (A : M) : forall n : Int, (A ^ n)ᵀ = Aᵀ ^ n
  | (n : Nat) => by rw [zpow_natCast, zpow_natCast, transpose_pow]
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, transpose_nonsing_inv, transpose_pow]

@[simp]
/--
theorem `conjTranspose_zpow` / 定理 `conjTranspose_zpow`

English:
theorem conjTranspose_zpow
  given: [StarRing R] (A : M)
  statement: forall n : Int, (A ^ n)ᴴ = Aᴴ ^ n

中文:
定理 conjTranspose_zpow
  条件: [StarRing R] (A : M)
  结论: 对任意 n : 整数, (A ^ n)ᴴ = Aᴴ ^ n
-/
theorem conjTranspose_zpow [StarRing R] (A : M) : forall n : Int, (A ^ n)ᴴ = Aᴴ ^ n
  | (n : Nat) => by rw [zpow_natCast, zpow_natCast, conjTranspose_pow]
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, conjTranspose_nonsing_inv, conjTranspose_pow]

/--
theorem `IsSymm.zpow` / 定理 `IsSymm.zpow`

English:
theorem IsSymm.zpow
  given: {A : M} (h : A.IsSymm) (k : Int)
  proof: by
  rw [IsSymm]; rw [transpose_zpow]; rw [h]

中文:
定理 IsSymm.zpow
  条件: {A : M} (h : A.IsSymm) (k : 整数)
  证明: by
  rw [IsSymm]; rw [transpose_zpow]; rw [h]

Depends on / 依赖: IsSymm, transpose_zpow
-/
theorem IsSymm.zpow {A : M} (h : A.IsSymm) (k : Int) :
    (A ^ k).IsSymm := by
  rw [IsSymm]; rw [transpose_zpow]; rw [h]

end ZPow

end Matrix
