/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Definition of well-known power series

In this file we define the following power series:

* `PowerSeries.invUnitsSub`: given `u : Rˣ`, this is the series for `1 / (u - x)`.
  It is given by `∑ n, x ^ n /ₚ u ^ (n + 1)`.

* `PowerSeries.invOneSubPow`: given a commutative ring `S` and a number `d : ℕ`,
  `PowerSeries.invOneSubPow S d` is the multiplicative inverse of `(1 - X) ^ d` in `S⟦X⟧ˣ`.
  When `d` is `0`, `PowerSeries.invOneSubPow S d` will just be `1`. When `d` is positive,
  `PowerSeries.invOneSubPow S d` will be `∑ n, Nat.choose (d - 1 + n) (d - 1)`.

* `PowerSeries.sin`, `PowerSeries.cos`, `PowerSeries.exp` : power series for sin, cosine, and
  exponential functions.
-/

@[expose] public section


namespace PowerSeries

section Ring

variable {R S : Type*} [Ring R] [Ring S]

/--
Definition of `invUnitsSub` / `invUnitsSub` 的定义

English:
definition invUnitsSub
  signature: (u : Rˣ)
  body: mk fun n => 1 /ₚ u ^ (n + 1)

@[simp]

中文:
定义 invUnitsSub
  签名: (u : Rˣ)
  定义体: mk fun n => 1 /ₚ u ^ (n + 1)

@[simp]
-/
def invUnitsSub (u : Rˣ) : PowerSeries R :=
  mk fun n => 1 /ₚ u ^ (n + 1)

@[simp]
/--
theorem `coeff_invUnitsSub` / 定理 `coeff_invUnitsSub`

English:
theorem coeff_invUnitsSub
  given: (u : Rˣ) (n : Nat)
  statement: coeff n (invUnitsSub u) = 1 /ₚ u ^ (n + 1)
  proof: coeff_mk _ _

@[simp]

中文:
定理 coeff_invUnitsSub
  条件: (u : Rˣ) (n : 自然数)
  结论: coeff n (invUnitsSub u) = 1 /ₚ u ^ (n + 1)
  证明: coeff_mk _ _

@[simp]

Depends on / 依赖: coeff_mk
-/
theorem coeff_invUnitsSub (u : Rˣ) (n : Nat) : coeff n (invUnitsSub u) = 1 /ₚ u ^ (n + 1) :=
  coeff_mk _ _

@[simp]
/--
theorem `constantCoeff_invUnitsSub` / 定理 `constantCoeff_invUnitsSub`

English:
theorem constantCoeff_invUnitsSub
  given: (u : Rˣ)
  statement: constantCoeff (invUnitsSub u) = 1 /ₚ u
  proof: by
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_invUnitsSub]; rw [zero_add]; rw [pow_one]

@[simp]

中文:
定理 constantCoeff_invUnitsSub
  条件: (u : Rˣ)
  结论: constantCoeff (invUnitsSub u) = 1 /ₚ u
  证明: by
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_invUnitsSub]; rw [zero_add]; rw [pow_one]

@[simp]

Depends on / 依赖: coeff_invUnitsSub, coeff_zero_eq_constantCoeff_apply, pow_one, zero_add
-/
theorem constantCoeff_invUnitsSub (u : Rˣ) : constantCoeff (invUnitsSub u) = 1 /ₚ u := by
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_invUnitsSub]; rw [zero_add]; rw [pow_one]

@[simp]
/--
theorem `invUnitsSub_mul_X` / 定理 `invUnitsSub_mul_X`

English:
theorem invUnitsSub_mul_X
  given: (u : Rˣ)
  statement: invUnitsSub u * X = invUnitsSub u * C (u : R) - 1
  proof: by
  ext (_ | n)
  · simp
  · simp [pow_succ']

@[simp]

中文:
定理 invUnitsSub_mul_X
  条件: (u : Rˣ)
  结论: invUnitsSub u * X = invUnitsSub u * C (u : R) - 1
  证明: by
  ext (_ | n)
  · simp
  · simp [pow_succ']

@[simp]

Depends on / 依赖: pow_succ
-/
theorem invUnitsSub_mul_X (u : Rˣ) : invUnitsSub u * X = invUnitsSub u * C (u : R) - 1 := by
  ext (_ | n)
  · simp
  · simp [pow_succ']

@[simp]
/--
theorem `invUnitsSub_mul_sub` / 定理 `invUnitsSub_mul_sub`

English:
theorem invUnitsSub_mul_sub
  given: (u : Rˣ)
  statement: invUnitsSub u * (C (u : R) - X) = 1
  proof: by
  simp [mul_sub, sub_sub_cancel]

中文:
定理 invUnitsSub_mul_sub
  条件: (u : Rˣ)
  结论: invUnitsSub u * (C (u : R) - X) = 1
  证明: by
  simp [mul_sub, sub_sub_cancel]

Depends on / 依赖: mul_sub, sub_sub_cancel
-/
theorem invUnitsSub_mul_sub (u : Rˣ) : invUnitsSub u * (C (u : R) - X) = 1 := by
  simp [mul_sub, sub_sub_cancel]

/--
theorem `map_invUnitsSub` / 定理 `map_invUnitsSub`

English:
theorem map_invUnitsSub
  given: (f : R ->+* S) (u : Rˣ)
  proof: by
  ext
  simp only [← map_pow, coeff_map, coeff_invUnitsSub, one_divp]
  rfl

中文:
定理 map_invUnitsSub
  条件: (f : R ->+* S) (u : Rˣ)
  证明: by
  ext
  simp only [← map_pow, coeff_map, coeff_invUnitsSub, one_divp]
  rfl

Depends on / 依赖: coeff_invUnitsSub, coeff_map, map_pow, one_divp
-/
theorem map_invUnitsSub (f : R ->+* S) (u : Rˣ) :
    map f (invUnitsSub u) = invUnitsSub (Units.map (f : R ->* S) u) := by
  ext
  simp only [← map_pow, coeff_map, coeff_invUnitsSub, one_divp]
  rfl

end Ring

section invOneSubPow

variable (S : Type*) [CommRing S] (d : Nat)

/--
theorem `mk_one_mul_one_sub_eq_one` / 定理 `mk_one_mul_one_sub_eq_one`

English:
theorem mk_one_mul_one_sub_eq_one
  statement: (mk 1 : S⟦X⟧) * (1 - X) = 1
  proof: by
  rw [mul_comm]; rw [PowerSeries.ext_iff]
  intro n
  cases n with
  | zero => simp
  | succ n => simp [sub_mul]

中文:
定理 mk_one_mul_one_sub_eq_one
  结论: (mk 1 : S⟦X⟧) * (1 - X) = 1
  证明: by
  rw [mul_comm]; rw [PowerSeries.ext_iff]
  intro n
  cases n with
  | zero => simp
  | succ n => simp [sub_mul]

Depends on / 依赖: PowerSeries, PowerSeries.ext_iff, ext_iff, mul_comm, sub_mul
-/
theorem mk_one_mul_one_sub_eq_one : (mk 1 : S⟦X⟧) * (1 - X) = 1 := by
  rw [mul_comm]; rw [PowerSeries.ext_iff]
  intro n
  cases n with
  | zero => simp
  | succ n => simp [sub_mul]

/--
theorem `mk_one_pow_eq_mk_choose_add` / 定理 `mk_one_pow_eq_mk_choose_add`

English:
theorem mk_one_pow_eq_mk_choose_add
  proof: by
  induction d with
  | zero => ext; simp
  | succ d hd =>
      ext n
      rw [pow_add]; rw [hd]; rw [pow_one]; rw [mul_comm]; rw [coeff_mul]
      simp_rw [coeff_mk, Pi.one_apply, one_mul]
      norm_cast
      rw [Finset.sum_antidiagonal_choose_add]; rw [add_right_comm]

中文:
定理 mk_one_pow_eq_mk_choose_add
  证明: by
  induction d with
  | zero => ext; simp
  | succ d hd =>
      ext n
      rw [pow_add]; rw [hd]; rw [pow_one]; rw [mul_comm]; rw [coeff_mul]
      simp_rw [coeff_mk, Pi.one_apply, one_mul]
      norm_cast
      rw [Finset.sum_antidiagonal_choose_add]; rw [add_right_comm]

Depends on / 依赖: Finset, Finset.sum_antidiagonal_choose_add, Pi.one_apply, add_right_comm, coeff_mk, coeff_mul, mul_comm, one_apply, one_mul, pow_add, pow_one, simp_rw, sum_antidiagonal_choose_add
-/
theorem mk_one_pow_eq_mk_choose_add :
    (mk 1 : S⟦X⟧) ^ (d + 1) = (mk fun n => Nat.choose (d + n) d : S⟦X⟧) := by
  induction d with
  | zero => ext; simp
  | succ d hd =>
      ext n
      rw [pow_add]; rw [hd]; rw [pow_one]; rw [mul_comm]; rw [coeff_mul]
      simp_rw [coeff_mk, Pi.one_apply, one_mul]
      norm_cast
      rw [Finset.sum_antidiagonal_choose_add]; rw [add_right_comm]

/--
Definition of `invOneSubPow` / `invOneSubPow` 的定义

English:
definition invOneSubPow
  signature: : Nat -> S⟦X⟧ˣ

中文:
定义 invOneSubPow
  签名: : 自然数 -> S⟦X⟧ˣ

Depends on / 依赖: Nat.choose
-/
noncomputable def invOneSubPow : Nat -> S⟦X⟧ˣ
  | 0 => 1
  | d + 1 => {
    val := mk fun n => Nat.choose (d + n) d
    inv := (1 - X) ^ (d + 1)
    val_inv := by
      rw [← mk_one_pow_eq_mk_choose_add]; rw [← mul_pow]; rw [mk_one_mul_one_sub_eq_one]; rw [one_pow]
    inv_val := by
      rw [← mk_one_pow_eq_mk_choose_add]; rw [← mul_pow]; rw [mul_comm]; rw [mk_one_mul_one_sub_eq_one]; rw [one_pow]
    }

/--
theorem `invOneSubPow_zero` / 定理 `invOneSubPow_zero`

English:
theorem invOneSubPow_zero
  statement: invOneSubPow S 0 = 1
  proof: by
  delta invOneSubPow
  simp only

中文:
定理 invOneSubPow_zero
  结论: invOneSubPow S 0 = 1
  证明: by
  delta invOneSubPow
  simp only

Depends on / 依赖: invOneSubPow
-/
theorem invOneSubPow_zero : invOneSubPow S 0 = 1 := by
  delta invOneSubPow
  simp only

/--
theorem `invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos` / 定理 `invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos`

English:
theorem invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos
  given: (h : 0 < d)
  proof: by
  rw [← Nat.sub_one_add_one_eq_of_pos h]; rw [invOneSubPow]; rw [add_tsub_cancel_right]

中文:
定理 invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos
  条件: (h : 0 < d)
  证明: by
  rw [← Nat.sub_one_add_one_eq_of_pos h]; rw [invOneSubPow]; rw [add_tsub_cancel_right]

Depends on / 依赖: Nat.sub_one_add_one_eq_of_pos, add_tsub_cancel_right, invOneSubPow, sub_one_add_one_eq_of_pos
-/
theorem invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos (h : 0 < d) :
    (invOneSubPow S d).val = (mk fun n => Nat.choose (d - 1 + n) (d - 1) : S⟦X⟧) := by
  rw [← Nat.sub_one_add_one_eq_of_pos h]; rw [invOneSubPow]; rw [add_tsub_cancel_right]

/--
theorem `invOneSubPow_val_succ_eq_mk_add_choose` / 定理 `invOneSubPow_val_succ_eq_mk_add_choose`

English:
theorem invOneSubPow_val_succ_eq_mk_add_choose
  proof: rfl

中文:
定理 invOneSubPow_val_succ_eq_mk_add_choose
  证明: rfl
-/
theorem invOneSubPow_val_succ_eq_mk_add_choose :
    (invOneSubPow S (d + 1)).val = (mk fun n => Nat.choose (d + n) d : S⟦X⟧) := rfl

/--
theorem `invOneSubPow_val_one_eq_invUnitSub_one` / 定理 `invOneSubPow_val_one_eq_invUnitSub_one`

English:
theorem invOneSubPow_val_one_eq_invUnitSub_one
  proof: by
  simp [invOneSubPow, invUnitsSub]

中文:
定理 invOneSubPow_val_one_eq_invUnitSub_one
  证明: by
  simp [invOneSubPow, invUnitsSub]

Depends on / 依赖: invOneSubPow, invUnitsSub
-/
theorem invOneSubPow_val_one_eq_invUnitSub_one :
    (invOneSubPow S 1).val = invUnitsSub (1 : Sˣ) := by
  simp [invOneSubPow, invUnitsSub]

/--
theorem `invOneSubPow_eq_inv_one_sub_pow` / 定理 `invOneSubPow_eq_inv_one_sub_pow`

English:
theorem invOneSubPow_eq_inv_one_sub_pow
  proof: by
  induction d with
| zero => exact Eq.symm pow_zero _
  | succ d _ =>
      rw [inv_pow]
      exact (DivisionMonoid.inv_eq_of_mul _ (invOneSubPow S (d + 1)) <| by
        rw [← Units.val_eq_one]; rw [Units.val_mul]; rw [Units.val_pow_eq_pow_val]
        exact (invOneSubPow S (d + 1)).inv_val).symm

中文:
定理 invOneSubPow_eq_inv_one_sub_pow
  证明: by
  induction d with
| zero => exact Eq.symm pow_zero _
  | succ d _ =>
      rw [inv_pow]
      exact (DivisionMonoid.inv_eq_of_mul _ (invOneSubPow S (d + 1)) <| by
        rw [← Units.val_eq_one]; rw [Units.val_mul]; rw [Units.val_pow_eq_pow_val]
        exact (invOneSubPow S (d + 1)).inv_val).symm

Depends on / 依赖: DivisionMonoid, DivisionMonoid.inv_eq_of_mul, Eq.symm, Units.val_eq_one, Units.val_mul, Units.val_pow_eq_pow_val, invOneSubPow, inv_eq_of_mul, inv_pow, inv_val, pow_zero, val_eq_one, val_mul, val_pow_eq_pow_val
-/
theorem invOneSubPow_eq_inv_one_sub_pow :
    invOneSubPow S d =
      (Units.mkOfMulEqOne (1 - X) (mk 1 : S⟦X⟧) <|
        Eq.trans (mul_comm _ _) (mk_one_mul_one_sub_eq_one S))⁻¹ ^ d := by
  induction d with
| zero => exact Eq.symm pow_zero _
  | succ d _ =>
      rw [inv_pow]
      exact (DivisionMonoid.inv_eq_of_mul _ (invOneSubPow S (d + 1)) <| by
        rw [← Units.val_eq_one]; rw [Units.val_mul]; rw [Units.val_pow_eq_pow_val]
        exact (invOneSubPow S (d + 1)).inv_val).symm

/--
theorem `invOneSubPow_inv_eq_one_sub_pow` / 定理 `invOneSubPow_inv_eq_one_sub_pow`

English:
theorem invOneSubPow_inv_eq_one_sub_pow
  proof: by
  induction d with
| zero => exact Eq.symm pow_zero _
  | succ d => rfl

中文:
定理 invOneSubPow_inv_eq_one_sub_pow
  证明: by
  induction d with
| zero => exact Eq.symm pow_zero _
  | succ d => rfl

Depends on / 依赖: Eq.symm, pow_zero
-/
theorem invOneSubPow_inv_eq_one_sub_pow :
    (invOneSubPow S d).inv = (1 - X : S⟦X⟧) ^ d := by
  induction d with
| zero => exact Eq.symm pow_zero _
  | succ d => rfl

/--
theorem `invOneSubPow_inv_zero_eq_one` / 定理 `invOneSubPow_inv_zero_eq_one`

English:
theorem invOneSubPow_inv_zero_eq_one
  statement: (invOneSubPow S 0).inv = 1
  proof: by
  delta invOneSubPow
  simp only [Units.inv_eq_val_inv, inv_one, Units.val_one]

中文:
定理 invOneSubPow_inv_zero_eq_one
  结论: (invOneSubPow S 0).inv = 1
  证明: by
  delta invOneSubPow
  simp only [Units.inv_eq_val_inv, inv_one, Units.val_one]

Depends on / 依赖: Units.inv_eq_val_inv, Units.val_one, invOneSubPow, inv_eq_val_inv, inv_one, val_one
-/
theorem invOneSubPow_inv_zero_eq_one : (invOneSubPow S 0).inv = 1 := by
  delta invOneSubPow
  simp only [Units.inv_eq_val_inv, inv_one, Units.val_one]

/--
theorem `mk_add_choose_mul_one_sub_pow_eq_one` / 定理 `mk_add_choose_mul_one_sub_pow_eq_one`

English:
theorem mk_add_choose_mul_one_sub_pow_eq_one
  proof: (invOneSubPow S (d + 1)).val_inv

中文:
定理 mk_add_choose_mul_one_sub_pow_eq_one
  证明: (invOneSubPow S (d + 1)).val_inv

Depends on / 依赖: invOneSubPow, val_inv
-/
theorem mk_add_choose_mul_one_sub_pow_eq_one :
    (mk fun n => Nat.choose (d + n) d : S⟦X⟧) * ((1 - X) ^ (d + 1)) = 1 :=
  (invOneSubPow S (d + 1)).val_inv

/--
theorem `invOneSubPow_add` / 定理 `invOneSubPow_add`

English:
theorem invOneSubPow_add
  given: (e : Nat)
  proof: by
  simp_rw [invOneSubPow_eq_inv_one_sub_pow, pow_add]

中文:
定理 invOneSubPow_add
  条件: (e : 自然数)
  证明: by
  simp_rw [invOneSubPow_eq_inv_one_sub_pow, pow_add]

Depends on / 依赖: invOneSubPow_eq_inv_one_sub_pow, pow_add, simp_rw
-/
theorem invOneSubPow_add (e : Nat) :
    invOneSubPow S (d + e) = invOneSubPow S d * invOneSubPow S e := by
  simp_rw [invOneSubPow_eq_inv_one_sub_pow, pow_add]

/--
theorem `one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val` / 定理 `one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val`

English:
theorem one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val
  given: (e : Nat)
  proof: by
  simp [invOneSubPow_add, Units.val_mul, mul_comm, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow]

中文:
定理 one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val
  条件: (e : 自然数)
  证明: by
  simp [invOneSubPow_add, Units.val_mul, mul_comm, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow]

Depends on / 依赖: Units.val_mul, invOneSubPow_add, invOneSubPow_inv_eq_one_sub_pow, mul_assoc, mul_comm, val_mul
-/
theorem one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val (e : Nat) :
    (1 - X) ^ e * (invOneSubPow S (d + e)).val = (invOneSubPow S d).val := by
  simp [invOneSubPow_add, Units.val_mul, mul_comm, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow]

/--
theorem `one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow` / 定理 `one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow`

English:
theorem one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow
  given: (e : Nat)
  proof: by
  simp [pow_add, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow S e]

中文:
定理 one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow
  条件: (e : 自然数)
  证明: by
  simp [pow_add, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow S e]

Depends on / 依赖: invOneSubPow_inv_eq_one_sub_pow, mul_assoc, pow_add
-/
theorem one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow (e : Nat) :
    (1 - X) ^ (d + e) * (invOneSubPow S e).val = (1 - X) ^ d := by
  simp [pow_add, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow S e]

end invOneSubPow

section Field

variable (A A' : Type*) [Ring A] [Ring A'] [Algebra Rat A] [Algebra Rat A']

open Nat

/--
Definition of `sin` / `sin` 的定义

English:
definition sin
  signature: : PowerSeries A
  body: mk fun n => if Even n then 0 else algebraMap Rat A ((-1) ^ (n / 2) / n !)

中文:
定义 sin
  签名: : 幂级数 A
  定义体: mk fun n => if Even n then 0 else algebraMap Rat A ((-1) ^ (n / 2) / n !)

Depends on / 依赖: algebraMap
-/
def sin : PowerSeries A :=
  mk fun n => if Even n then 0 else algebraMap Rat A ((-1) ^ (n / 2) / n !)

/--
Definition of `cos` / `cos` 的定义

English:
definition cos
  signature: : PowerSeries A
  body: mk fun n => if Even n then algebraMap Rat A ((-1) ^ (n / 2) / n !) else 0

中文:
定义 cos
  签名: : 幂级数 A
  定义体: mk fun n => if Even n then algebraMap Rat A ((-1) ^ (n / 2) / n !) else 0

Depends on / 依赖: algebraMap
-/
def cos : PowerSeries A :=
  mk fun n => if Even n then algebraMap Rat A ((-1) ^ (n / 2) / n !) else 0

variable {A A'} (n : Nat) (f : A ->+* A')

@[simp]
/--
theorem `map_sin` / 定理 `map_sin`

English:
theorem map_sin
  statement: map f (sin A) = sin A'
  proof: by
  ext
  simp [sin, apply_ite f]

@[simp]

中文:
定理 map_sin
  结论: map f (sin A) = sin A'
  证明: by
  ext
  simp [sin, apply_ite f]

@[simp]

Depends on / 依赖: apply_ite
-/
theorem map_sin : map f (sin A) = sin A' := by
  ext
  simp [sin, apply_ite f]

@[simp]
/--
theorem `map_cos` / 定理 `map_cos`

English:
theorem map_cos
  statement: map f (cos A) = cos A'
  proof: by
  ext
  simp [cos, apply_ite f]

中文:
定理 map_cos
  结论: map f (cos A) = cos A'
  证明: by
  ext
  simp [cos, apply_ite f]

Depends on / 依赖: apply_ite
-/
theorem map_cos : map f (cos A) = cos A' := by
  ext
  simp [cos, apply_ite f]

end Field


end PowerSeries
