/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Pell's equation and Matiyasevic's theorem

This file solves Pell's equation, i.e. integer solutions to `x ^ 2 - d * y ^ 2 = 1`
*in the special case that `d = a ^ 2 - 1`*.
This is then applied to prove Matiyasevic's theorem that the power
function is Diophantine, which is the last key ingredient in the solution to Hilbert's tenth
problem. For the definition of Diophantine function, see `NumberTheory.Dioph`.

For results on Pell's equation for arbitrary (positive, non-square) `d`, see
`NumberTheory.Pell`.

## Main definition

* `pell` is a function assigning to a natural number `n` the `n`-th solution to Pell's equation
  constructed recursively from the initial solution `(0, 1)`.

## Main statements

* `eq_pell` shows that every solution to Pell's equation is recursively obtained using `pell`
* `matiyasevic` shows that a certain system of Diophantine equations has a solution if and only if
  the first variable is the `x`-component in a solution to Pell's equation - the key step towards
  Hilbert's tenth problem in Davis' version of Matiyasevic's theorem.
* `eq_pow_of_pell` shows that the power function is Diophantine.

## Implementation notes

The proof of Matiyasevic's theorem doesn't follow Matiyasevic's original account of using Fibonacci
numbers but instead Davis' variant of using solutions to Pell's equation.

## References

* [M. Carneiro, _A Lean formalization of Matiyasevič's theorem_][carneiro2018matiyasevic]
* [M. Davis, _Hilbert's tenth problem is unsolvable_][MR317916]

## Tags

Pell's equation, Matiyasevic's theorem, Hilbert's tenth problem

-/

@[expose] public section


namespace Pell

open Nat

section

variable {d : Int}

/--
Definition of `IsPell` / `IsPell` 的定义

English:
definition IsPell
  signature: : Int√d -> Prop

中文:
定义 IsPell
  签名: : 整数√d -> 命题
-/
def IsPell : Int√d -> Prop
  | ⟨x, y⟩ => x * x - d * y * y = 1

/--
theorem `isPell_norm` / 定理 `isPell_norm`

English:
theorem isPell_norm
  statement: forall {b : Int√d}, IsPell b ↔ b * star b = 1

中文:
定理 isPell_norm
  结论: 对任意 {b : 整数√d}, IsPell b ↔ b * star b = 1
-/
theorem isPell_norm : forall {b : Int√d}, IsPell b ↔ b * star b = 1
  | ⟨x, y⟩ => by simp [Zsqrtd.ext_iff, IsPell, mul_comm]; ring_nf

/--
theorem `isPell_iff_mem_unitary` / 定理 `isPell_iff_mem_unitary`

English:
theorem isPell_iff_mem_unitary
  statement: forall {b : Int√d}, IsPell b ↔ b in unitary (Int√d)

中文:
定理 isPell_iff_mem_unitary
  结论: 对任意 {b : 整数√d}, IsPell b ↔ b in unitary (整数√d)
-/
theorem isPell_iff_mem_unitary : forall {b : Int√d}, IsPell b ↔ b in unitary (Int√d)
  | ⟨x, y⟩ => by rw [Unitary.mem_iff, isPell_norm, mul_comm (star _), and_self_iff]

/--
theorem `isPell_mul` / 定理 `isPell_mul`

English:
theorem isPell_mul
  given: {b c : Int√d} (hb : IsPell b) (hc : IsPell c)
  statement: IsPell (b * c)
  proof: isPell_norm.2 (by simp [mul_comm, mul_left_comm c, mul_assoc,
    star_mul, isPell_norm.1 hb, isPell_norm.1 hc])

中文:
定理 isPell_mul
  条件: {b c : 整数√d} (hb : IsPell b) (hc : IsPell c)
  结论: IsPell (b * c)
  证明: isPell_norm.2 (by simp [mul_comm, mul_left_comm c, mul_assoc,
    star_mul, isPell_norm.1 hb, isPell_norm.1 hc])

Depends on / 依赖: isPell_norm, mul_assoc, mul_comm, mul_left_comm, star_mul
-/
theorem isPell_mul {b c : Int√d} (hb : IsPell b) (hc : IsPell c) : IsPell (b * c) :=
  isPell_norm.2 (by simp [mul_comm, mul_left_comm c, mul_assoc,
    star_mul, isPell_norm.1 hb, isPell_norm.1 hc])

/--
theorem `isPell_star` / 定理 `isPell_star`

English:
theorem isPell_star
  statement: forall {b : Int√d}, IsPell b ↔ IsPell (star b)

中文:
定理 isPell_star
  结论: 对任意 {b : 整数√d}, IsPell b ↔ IsPell (star b)
-/
theorem isPell_star : forall {b : Int√d}, IsPell b ↔ IsPell (star b)
  | ⟨x, y⟩ => by simp [IsPell]

end

section

variable {a : Nat} (a1 : 1 < a)

set_option backward.privateInPublic true in
/--
Definition of `d` / `d` 的定义

English:
definition d
  signature: (_a1 : 1 < a)
  body: a * a - 1

中文:
定义 d
  签名: (_a1 : 1 < a)
  定义体: a * a - 1
-/
private def d (_a1 : 1 < a) :=
  a * a - 1

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/--
theorem `d_pos` / 定理 `d_pos`

English:
theorem d_pos
  statement: 0 < d a1
  proof: tsub_pos_of_lt (mul_lt_mul a1 (le_of_lt a1) (by decide) (Nat.zero_le _) : 1 * 1 < a * a)

中文:
定理 d_pos
  结论: 0 < d a1
  证明: tsub_pos_of_lt (mul_lt_mul a1 (le_of_lt a1) (by decide) (Nat.zero_le _) : 1 * 1 < a * a)

Depends on / 依赖: Nat.zero_le, le_of_lt, mul_lt_mul, tsub_pos_of_lt, zero_le
-/
theorem d_pos : 0 < d a1 :=
  tsub_pos_of_lt (mul_lt_mul a1 (le_of_lt a1) (by decide) (Nat.zero_le _) : 1 * 1 < a * a)

-- TODO(lint): Fix double namespace issue
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
--@[nolint dup_namespace]
/--
Definition of `pell` / `pell` 的定义

English:
definition pell
  signature: : Nat -> Nat × Nat

中文:
定义 pell
  签名: : 自然数 -> 自然数 × 自然数
-/
def pell : Nat -> Nat × Nat
  | 0 => (1, 0)
  | n + 1 => ((pell n).1 * a + d a1 * (pell n).2, (pell n).1 + (pell n).2 * a)

/--
Definition of `xn` / `xn` 的定义

English:
definition xn
  signature: (n : Nat)
  body: (pell a1 n).1

中文:
定义 xn
  签名: (n : 自然数)
  定义体: (pell a1 n).1
-/
def xn (n : Nat) : Nat :=
  (pell a1 n).1

/--
Definition of `yn` / `yn` 的定义

English:
definition yn
  signature: (n : Nat)
  body: (pell a1 n).2

@[simp]

中文:
定义 yn
  签名: (n : 自然数)
  定义体: (pell a1 n).2

@[simp]
-/
def yn (n : Nat) : Nat :=
  (pell a1 n).2

@[simp]
/--
theorem `pell_val` / 定理 `pell_val`

English:
theorem pell_val
  given: (n : Nat)
  statement: pell a1 n = (xn a1 n, yn a1 n)
  proof: show pell a1 n = ((pell a1 n).1, (pell a1 n).2) from
    match pell a1 n with
    | (_, _) => rfl

@[simp]

中文:
定理 pell_val
  条件: (n : 自然数)
  结论: pell a1 n = (xn a1 n, yn a1 n)
  证明: show pell a1 n = ((pell a1 n).1, (pell a1 n).2) from
    match pell a1 n with
    | (_, _) => rfl

@[simp]
-/
theorem pell_val (n : Nat) : pell a1 n = (xn a1 n, yn a1 n) :=
  show pell a1 n = ((pell a1 n).1, (pell a1 n).2) from
    match pell a1 n with
    | (_, _) => rfl

@[simp]
/--
theorem `xn_zero` / 定理 `xn_zero`

English:
theorem xn_zero
  statement: xn a1 0 = 1
  proof: rfl

@[simp]

中文:
定理 xn_zero
  结论: xn a1 0 = 1
  证明: rfl

@[simp]
-/
theorem xn_zero : xn a1 0 = 1 :=
  rfl

@[simp]
/--
theorem `yn_zero` / 定理 `yn_zero`

English:
theorem yn_zero
  statement: yn a1 0 = 0
  proof: rfl

中文:
定理 yn_zero
  结论: yn a1 0 = 0
  证明: rfl
-/
theorem yn_zero : yn a1 0 = 0 :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/--
theorem `xn_succ` / 定理 `xn_succ`

English:
theorem xn_succ
  given: (n : Nat)
  statement: xn a1 (n + 1) = xn a1 n * a + d a1 * yn a1 n
  proof: rfl

@[simp]

中文:
定理 xn_succ
  条件: (n : 自然数)
  结论: xn a1 (n + 1) = xn a1 n * a + d a1 * yn a1 n
  证明: rfl

@[simp]
-/
theorem xn_succ (n : Nat) : xn a1 (n + 1) = xn a1 n * a + d a1 * yn a1 n :=
  rfl

@[simp]
/--
theorem `yn_succ` / 定理 `yn_succ`

English:
theorem yn_succ
  given: (n : Nat)
  statement: yn a1 (n + 1) = xn a1 n + yn a1 n * a
  proof: rfl

中文:
定理 yn_succ
  条件: (n : 自然数)
  结论: yn a1 (n + 1) = xn a1 n + yn a1 n * a
  证明: rfl
-/
theorem yn_succ (n : Nat) : yn a1 (n + 1) = xn a1 n + yn a1 n * a :=
  rfl

/--
theorem `xn_one` / 定理 `xn_one`

English:
theorem xn_one
  statement: xn a1 1 = a
  proof: by simp

中文:
定理 xn_one
  结论: xn a1 1 = a
  证明: by simp
-/
theorem xn_one : xn a1 1 = a := by simp

/--
theorem `yn_one` / 定理 `yn_one`

English:
theorem yn_one
  statement: yn a1 1 = 1
  proof: by simp

中文:
定理 yn_one
  结论: yn a1 1 = 1
  证明: by simp
-/
theorem yn_one : yn a1 1 = 1 := by simp

/--
Definition of `xz` / `xz` 的定义

English:
definition xz
  signature: (n : Nat)
  body: xn a1 n

中文:
定义 xz
  签名: (n : 自然数)
  定义体: xn a1 n
-/
def xz (n : Nat) : Int :=
  xn a1 n

/--
Definition of `yz` / `yz` 的定义

English:
definition yz
  signature: (n : Nat)
  body: yn a1 n

中文:
定义 yz
  签名: (n : 自然数)
  定义体: yn a1 n
-/
def yz (n : Nat) : Int :=
  yn a1 n

section

/--
Definition of `az` / `az` 的定义

English:
definition az
  signature: (a : Nat)
  body: a

中文:
定义 az
  签名: (a : 自然数)
  定义体: a
-/
def az (a : Nat) : Int :=
  a

end

include a1 in
/--
theorem `asq_pos` / 定理 `asq_pos`

English:
theorem asq_pos
  statement: 0 < a * a
  proof: le_trans (le_of_lt a1)
    (by have := @Nat.mul_le_mul_left 1 a a (le_of_lt a1); rwa [mul_one] at this)

中文:
定理 asq_pos
  结论: 0 < a * a
  证明: le_trans (le_of_lt a1)
    (by have := @Nat.mul_le_mul_left 1 a a (le_of_lt a1); rwa [mul_one] at this)

Depends on / 依赖: Nat.mul_le_mul_left, le_of_lt, le_trans, mul_le_mul_left, mul_one
-/
theorem asq_pos : 0 < a * a :=
  le_trans (le_of_lt a1)
    (by have := @Nat.mul_le_mul_left 1 a a (le_of_lt a1); rwa [mul_one] at this)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `dz_val` / 定理 `dz_val`

English:
theorem dz_val
  statement: ↑(d a1) = az a * az a - 1
  proof: have : 1 <= a * a := asq_pos a1
  by rw [Pell.d, Int.ofNat_sub this]; rfl

中文:
定理 dz_val
  结论: ↑(d a1) = az a * az a - 1
  证明: have : 1 <= a * a := asq_pos a1
  by rw [Pell.d, Int.ofNat_sub this]; rfl

Depends on / 依赖: Int.ofNat_sub, Pell.d, asq_pos, ofNat_sub
-/
theorem dz_val : ↑(d a1) = az a * az a - 1 :=
  have : 1 <= a * a := asq_pos a1
  by rw [Pell.d, Int.ofNat_sub this]; rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/--
theorem `xz_succ` / 定理 `xz_succ`

English:
theorem xz_succ
  given: (n : Nat)
  statement: (xz a1 (n + 1)) = xz a1 n * az a + d a1 * yz a1 n
  proof: rfl

@[simp]

中文:
定理 xz_succ
  条件: (n : 自然数)
  结论: (xz a1 (n + 1)) = xz a1 n * az a + d a1 * yz a1 n
  证明: rfl

@[simp]
-/
theorem xz_succ (n : Nat) : (xz a1 (n + 1)) = xz a1 n * az a + d a1 * yz a1 n :=
  rfl

@[simp]
/--
theorem `yz_succ` / 定理 `yz_succ`

English:
theorem yz_succ
  given: (n : Nat)
  statement: yz a1 (n + 1) = xz a1 n + yz a1 n * az a
  proof: rfl

中文:
定理 yz_succ
  条件: (n : 自然数)
  结论: yz a1 (n + 1) = xz a1 n + yz a1 n * az a
  证明: rfl
-/
theorem yz_succ (n : Nat) : yz a1 (n + 1) = xz a1 n + yz a1 n * az a :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `pellZd` / `pellZd` 的定义

English:
definition pellZd
  signature: (n : Nat)
  body: ⟨xn a1 n, yn a1 n⟩

@[simp]

中文:
定义 pellZd
  签名: (n : 自然数)
  定义体: ⟨xn a1 n, yn a1 n⟩

@[simp]
-/
def pellZd (n : Nat) : Int√(d a1) :=
  ⟨xn a1 n, yn a1 n⟩

@[simp]
/--
theorem `re_pellZd` / 定理 `re_pellZd`

English:
theorem re_pellZd
  given: (n : Nat)
  statement: (pellZd a1 n).re = xn a1 n
  proof: rfl

@[simp]

中文:
定理 re_pellZd
  条件: (n : 自然数)
  结论: (pellZd a1 n).re = xn a1 n
  证明: rfl

@[simp]
-/
theorem re_pellZd (n : Nat) : (pellZd a1 n).re = xn a1 n :=
  rfl

@[simp]
/--
theorem `im_pellZd` / 定理 `im_pellZd`

English:
theorem im_pellZd
  given: (n : Nat)
  statement: (pellZd a1 n).im = yn a1 n
  proof: rfl

中文:
定理 im_pellZd
  条件: (n : 自然数)
  结论: (pellZd a1 n).im = yn a1 n
  证明: rfl
-/
theorem im_pellZd (n : Nat) : (pellZd a1 n).im = yn a1 n :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `isPell_nat` / 定理 `isPell_nat`

English:
theorem isPell_nat
  given: {x y : Nat}
  statement: IsPell (⟨x, y⟩ : Int√(d a1)) ↔ x * x - d a1 * y * y = 1
  proof: ⟨fun h =>
    (Nat.cast_inj (R := Int)).1
      (by rw [Int.ofNat_sub (Int.le_of_ofNat_le_ofNat <| Int.le.intro_sub _ h)]; exact h),
    fun h =>
    show ((x * x : Nat) - (d a1 * y * y : Nat) : Int) = 1 by
      rw [← Int.ofNat_sub <| le_of_lt <| Nat.lt_of_sub_eq_succ h]; rw [h]; rfl⟩

@[simp]

中文:
定理 isPell_nat
  条件: {x y : 自然数}
  结论: IsPell (⟨x, y⟩ : 整数√(d a1)) ↔ x * x - d a1 * y * y = 1
  证明: ⟨fun h =>
    (Nat.cast_inj (R := Int)).1
      (by rw [Int.ofNat_sub (Int.le_of_ofNat_le_ofNat <| Int.le.intro_sub _ h)]; exact h),
    fun h =>
    show ((x * x : Nat) - (d a1 * y * y : Nat) : Int) = 1 by
      rw [← Int.ofNat_sub <| le_of_lt <| Nat.lt_of_sub_eq_succ h]; rw [h]; rfl⟩

@[simp]

Depends on / 依赖: Int.le.intro_sub, Int.le_of_ofNat_le_ofNat, Int.ofNat_sub, Nat.cast_inj, Nat.lt_of_sub_eq_succ, cast_inj, intro_sub, le_of_lt, le_of_ofNat_le_ofNat, lt_of_sub_eq_succ, ofNat_sub
-/
theorem isPell_nat {x y : Nat} : IsPell (⟨x, y⟩ : Int√(d a1)) ↔ x * x - d a1 * y * y = 1 :=
  ⟨fun h =>
    (Nat.cast_inj (R := Int)).1
      (by rw [Int.ofNat_sub (Int.le_of_ofNat_le_ofNat <| Int.le.intro_sub _ h)]; exact h),
    fun h =>
    show ((x * x : Nat) - (d a1 * y * y : Nat) : Int) = 1 by
      rw [← Int.ofNat_sub <| le_of_lt <| Nat.lt_of_sub_eq_succ h]; rw [h]; rfl⟩

@[simp]
/--
theorem `pellZd_succ` / 定理 `pellZd_succ`

English:
theorem pellZd_succ
  given: (n : Nat)
  statement: pellZd a1 (n + 1) = pellZd a1 n * ⟨a, 1⟩
  proof: by ext <;> simp

中文:
定理 pellZd_succ
  条件: (n : 自然数)
  结论: pellZd a1 (n + 1) = pellZd a1 n * ⟨a, 1⟩
  证明: by ext <;> simp
-/
theorem pellZd_succ (n : Nat) : pellZd a1 (n + 1) = pellZd a1 n * ⟨a, 1⟩ := by ext <;> simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `isPell_one` / 定理 `isPell_one`

English:
theorem isPell_one
  statement: IsPell (⟨a, 1⟩ : Int√(d a1))
  proof: show az a * az a - d a1 * 1 * 1 = 1 by simp [dz_val]

中文:
定理 isPell_one
  结论: IsPell (⟨a, 1⟩ : 整数√(d a1))
  证明: show az a * az a - d a1 * 1 * 1 = 1 by simp [dz_val]

Depends on / 依赖: dz_val
-/
theorem isPell_one : IsPell (⟨a, 1⟩ : Int√(d a1)) :=
  show az a * az a - d a1 * 1 * 1 = 1 by simp [dz_val]

/--
theorem `isPell_pellZd` / 定理 `isPell_pellZd`

English:
theorem isPell_pellZd
  statement: forall n : Nat, IsPell (pellZd a1 n)
  proof: isPell_one a1
    simpa using Pell.isPell_mul (isPell_pellZd n) o

中文:
定理 isPell_pellZd
  结论: 对任意 n : 自然数, IsPell (pellZd a1 n)
  证明: isPell_one a1
    simpa using Pell.isPell_mul (isPell_pellZd n) o

Depends on / 依赖: isPell_one
-/
theorem isPell_pellZd : forall n : Nat, IsPell (pellZd a1 n)
  | 0 => rfl
  | n + 1 => by
    let o := isPell_one a1
    simpa using Pell.isPell_mul (isPell_pellZd n) o

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/--
theorem `pell_eqz` / 定理 `pell_eqz`

English:
theorem pell_eqz
  given: (n : Nat)
  statement: xz a1 n * xz a1 n - d a1 * yz a1 n * yz a1 n = 1
  proof: isPell_pellZd a1 n

中文:
定理 pell_eqz
  条件: (n : 自然数)
  结论: xz a1 n * xz a1 n - d a1 * yz a1 n * yz a1 n = 1
  证明: isPell_pellZd a1 n

Depends on / 依赖: isPell_pellZd
-/
theorem pell_eqz (n : Nat) : xz a1 n * xz a1 n - d a1 * yz a1 n * yz a1 n = 1 :=
  isPell_pellZd a1 n

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/--
theorem `pell_eq` / 定理 `pell_eq`

English:
theorem pell_eq
  given: (n : Nat)
  statement: xn a1 n * xn a1 n - d a1 * yn a1 n * yn a1 n = 1
  proof: let pn := pell_eqz a1 n
  have h : (↑(xn a1 n * xn a1 n) : Int) - ↑(d a1 * yn a1 n * yn a1 n) = 1 := by
    repeat' rw [Int.natCast_mul]; exact pn
  have hl : d a1 * yn a1 n * yn a1 n <= xn a1 n * xn a1 n :=
Nat.cast_le.1 Int.le.intro _ add_eq_of_eq_sub' Eq.symm h
  (Nat.cast_inj (R := Int)).1 (by r

中文:
定理 pell_eq
  条件: (n : 自然数)
  结论: xn a1 n * xn a1 n - d a1 * yn a1 n * yn a1 n = 1
  证明: let pn := pell_eqz a1 n
  have h : (↑(xn a1 n * xn a1 n) : Int) - ↑(d a1 * yn a1 n * yn a1 n) = 1 := by
    repeat' rw [Int.natCast_mul]; exact pn
  have hl : d a1 * yn a1 n * yn a1 n <= xn a1 n * xn a1 n :=
Nat.cast_le.1 Int.le.intro _ add_eq_of_eq_sub' Eq.symm h
  (Nat.cast_inj (R := Int)).1 (by r

Depends on / 依赖: Eq.symm, Int.le.intro, Int.natCast_mul, Int.ofNat_sub, Nat.cast_inj, Nat.cast_le, add_eq_of_eq_sub, cast_inj, cast_le, natCast_mul, ofNat_sub, pell_eqz, repeat
-/
theorem pell_eq (n : Nat) : xn a1 n * xn a1 n - d a1 * yn a1 n * yn a1 n = 1 :=
  let pn := pell_eqz a1 n
  have h : (↑(xn a1 n * xn a1 n) : Int) - ↑(d a1 * yn a1 n * yn a1 n) = 1 := by
    repeat' rw [Int.natCast_mul]; exact pn
  have hl : d a1 * yn a1 n * yn a1 n <= xn a1 n * xn a1 n :=
Nat.cast_le.1 Int.le.intro _ add_eq_of_eq_sub' Eq.symm h
  (Nat.cast_inj (R := Int)).1 (by rw [Int.ofNat_sub hl]; exact h)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `dnsq` / 实例 `dnsq`

English:
instance dnsq
  signature: : Zsqrtd.Nonsquare (d a1)
  body: ⟨fun n h =>
    have : n * n + 1 = a * a := by rw [← h]; exact Nat.succ_pred_eq_of_pos (asq_pos a1)
    have na : n < a := Nat.mul_self_lt_mul_self_iff.1 (by rw [← this]; exact Nat.lt_succ_self _)
    have : (n + 1) * (n + 1) <= n * n + 1 := by rw [this]; exact Nat.mul_self_le_mul_self na
    have :

中文:
实例 dnsq
  签名: : Zsqrtd.Nonsquare (d a1)
  定义体: ⟨fun n h =>
    have : n * n + 1 = a * a := by rw [← h]; exact Nat.succ_pred_eq_of_pos (asq_pos a1)
    have na : n < a := Nat.mul_self_lt_mul_self_iff.1 (by rw [← this]; exact Nat.lt_succ_self _)
    have : (n + 1) * (n + 1) <= n * n + 1 := by rw [this]; exact Nat.mul_self_le_mul_self na
    have :

Depends on / 依赖: Nat.eq_zero_of_le_zero, Nat.le_add_left, Nat.le_of_add_le_add_right, Nat.lt_succ_self, Nat.mul_self_le_mul_self, Nat.mul_self_lt_mul_self_iff, Nat.ne_of_gt, Nat.succ_pred_eq_of_pos, asq_pos, d_pos, eq_zero_of_le_zero, le_add_left, le_of_add_le_add_right, lt_succ_self, mul_self_le_mul_self, mul_self_lt_mul_self_iff, ne_of_gt, ring_nf, succ_pred_eq_of_pos
-/
instance dnsq : Zsqrtd.Nonsquare (d a1) :=
  ⟨fun n h =>
    have : n * n + 1 = a * a := by rw [← h]; exact Nat.succ_pred_eq_of_pos (asq_pos a1)
    have na : n < a := Nat.mul_self_lt_mul_self_iff.1 (by rw [← this]; exact Nat.lt_succ_self _)
    have : (n + 1) * (n + 1) <= n * n + 1 := by rw [this]; exact Nat.mul_self_le_mul_self na
    have : n + n <= 0 :=
      @Nat.le_of_add_le_add_right _ (n * n + 1) _ (by ring_nf at this ⊢; assumption)
Nat.ne_of_gt (d_pos a1) by
      rwa [Nat.eq_zero_of_le_zero ((Nat.le_add_left _ _).trans this)] at h⟩

/--
theorem `xn_ge_a_pow` / 定理 `xn_ge_a_pow`

English:
theorem xn_ge_a_pow
  statement: forall n : Nat, a ^ n <= xn a1 n

中文:
定理 xn_ge_a_pow
  结论: 对任意 n : 自然数, a ^ n <= xn a1 n
-/
theorem xn_ge_a_pow : forall n : Nat, a ^ n <= xn a1 n
  | 0 => le_refl 1
  | n + 1 => by
    simp only [_root_.pow_succ, xn_succ]
    exact le_trans (Nat.mul_le_mul_right _ (xn_ge_a_pow n)) (Nat.le_add_right _ _)

/--
theorem `n_lt_xn` / 定理 `n_lt_xn`

English:
theorem n_lt_xn
  given: (n)
  statement: n < xn a1 n
  proof: lt_of_lt_of_le (Nat.lt_pow_self a1) (xn_ge_a_pow a1 n)

中文:
定理 n_lt_xn
  条件: (n)
  结论: n < xn a1 n
  证明: lt_of_lt_of_le (Nat.lt_pow_self a1) (xn_ge_a_pow a1 n)

Depends on / 依赖: Nat.lt_pow_self, lt_of_lt_of_le, lt_pow_self, xn_ge_a_pow
-/
theorem n_lt_xn (n) : n < xn a1 n :=
  lt_of_lt_of_le (Nat.lt_pow_self a1) (xn_ge_a_pow a1 n)

/--
theorem `x_pos` / 定理 `x_pos`

English:
theorem x_pos
  given: (n)
  statement: 0 < xn a1 n
  proof: lt_of_le_of_lt (Nat.zero_le n) (n_lt_xn a1 n)

中文:
定理 x_pos
  条件: (n)
  结论: 0 < xn a1 n
  证明: lt_of_le_of_lt (Nat.zero_le n) (n_lt_xn a1 n)

Depends on / 依赖: Nat.zero_le, lt_of_le_of_lt, n_lt_xn, zero_le
-/
theorem x_pos (n) : 0 < xn a1 n :=
  lt_of_le_of_lt (Nat.zero_le n) (n_lt_xn a1 n)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `eq_pell_lem` / 定理 `eq_pell_lem`

English:
theorem eq_pell_lem
  statement: forall (n) (b : Int√(d a1)), 1 <= b -> IsPell b ->
  proof: trivial
    have am1p : (0 : Int√(d a1)) <= ⟨a, -1⟩ := show (_ : Nat) <= _ by simp [d]
    have a1m : (⟨a, 1⟩ * ⟨a, -1⟩ : Int√(d a1)) = 1 := isPell_norm.1 (isPell_one a1)
    if ha : (⟨↑a, 1⟩ : Int√(d a1)) <= b then
      let ⟨m, e⟩ :=
        eq_pell_lem n (b * ⟨a, -1⟩) (by rw [← a1m]; exact mul_le

中文:
定理 eq_pell_lem
  结论: 对任意 (n) (b : 整数√(d a1)), 1 <= b -> IsPell b ->
  证明: trivial
    have am1p : (0 : Int√(d a1)) <= ⟨a, -1⟩ := show (_ : Nat) <= _ by simp [d]
    have a1m : (⟨a, 1⟩ * ⟨a, -1⟩ : Int√(d a1)) = 1 := isPell_norm.1 (isPell_one a1)
    if ha : (⟨↑a, 1⟩ : Int√(d a1)) <= b then
      let ⟨m, e⟩ :=
        eq_pell_lem n (b * ⟨a, -1⟩) (by rw [← a1m]; exact mul_le
-/
theorem eq_pell_lem : forall (n) (b : Int√(d a1)), 1 <= b -> IsPell b ->
    b <= pellZd a1 n -> exists n, b = pellZd a1 n
  | 0, _ => fun h1 _ hl => ⟨0, le_antisymm hl h1⟩
  | n + 1, b => fun h1 hp h =>
    have a1p : (0 : Int√(d a1)) <= ⟨a, 1⟩ := trivial
    have am1p : (0 : Int√(d a1)) <= ⟨a, -1⟩ := show (_ : Nat) <= _ by simp [d]
    have a1m : (⟨a, 1⟩ * ⟨a, -1⟩ : Int√(d a1)) = 1 := isPell_norm.1 (isPell_one a1)
    if ha : (⟨↑a, 1⟩ : Int√(d a1)) <= b then
      let ⟨m, e⟩ :=
        eq_pell_lem n (b * ⟨a, -1⟩) (by rw [← a1m]; exact mul_le_mul_of_nonneg_right ha am1p)
          (isPell_mul hp (isPell_star.1 (isPell_one a1)))
          (by
            have t := mul_le_mul_of_nonneg_right h am1p
            rwa [pellZd_succ, mul_assoc, a1m, mul_one] at t)
      ⟨m + 1, by
        rw [show b = b * ⟨a]; rw [-1⟩ * ⟨a]; rw [1⟩ by rw [mul_assoc]; rw [Eq.trans (mul_comm _ _) a1m]; simp,
          pellZd_succ, e]⟩
    else
      suffices ¬1 < b from ⟨0, show b = 1 from (Or.resolve_left (lt_or_eq_of_le h1) this).symm⟩
      fun h1l => by
      obtain ⟨x, y⟩ := b
      exact by
        have bm : (_ * ⟨_, _⟩ : Int√d a1) = 1 := Pell.isPell_norm.1 hp
        have y0l : (0 : Int√d a1) < ⟨x - x, y - -y⟩ :=
          sub_lt_sub h1l fun hn : (1 : Int√d a1) <= ⟨x, -y⟩ => by
            have t := mul_le_mul_of_nonneg_left hn (le_trans zero_le_one h1)
            rw [bm]; rw [mul_one] at t
            exact h1l t
        have yl2 : (⟨_, _⟩ : Int√_) < ⟨_, _⟩ :=
          show (⟨x, y⟩ - ⟨x, -y⟩ : Int√d a1) < ⟨a, 1⟩ - ⟨a, -1⟩ from
            sub_lt_sub ha fun hn : (⟨x, -y⟩ : Int√d a1) <= ⟨a, -1⟩ => by
              have t := mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hn (le_trans zero_le_one h1)) a1p
              rw [bm]; rw [one_mul]; rw [mul_assoc]; rw [Eq.trans (mul_comm _ _) a1m]; rw [mul_one] at t
              exact ha t
        simp only [sub_self, sub_neg_eq_add] at y0l; simp only [Zsqrtd.re_neg, add_neg_cancel,
          Zsqrtd.im_neg, neg_neg] at yl2
        exact
          match y, y0l, (yl2 : (⟨_, _⟩ : Int√_) < ⟨_, _⟩) with
          | 0, y0l, _ => y0l (le_refl 0)
          | (y + 1 : Nat), _, yl2 =>
            yl2
              (Zsqrtd.le_of_le_le (by simp)
                (let t := Int.ofNat_le_ofNat_of_le (Nat.succ_pos y)
                add_le_add t t))
          | Int.negSucc _, y0l, _ => y0l trivial

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `eq_pellZd` / 定理 `eq_pellZd`

English:
theorem eq_pellZd
  given: (b : Int√(d a1)) (b1 : 1 <= b) (hp : IsPell b)
  statement: exists n, b = pellZd a1 n
  proof: let ⟨n, h⟩ := @Zsqrtd.le_arch (d a1) b
eq_pell_lem a1 n b b1 hp
h.trans by
      rw [Zsqrtd.natCast_val]
      exact
        Zsqrtd.le_of_le_le (Int.ofNat_le_ofNat_of_le <| le_of_lt <| n_lt_xn _ _)
          (Int.natCast_nonneg _)

中文:
定理 eq_pellZd
  条件: (b : 整数√(d a1)) (b1 : 1 <= b) (hp : IsPell b)
  结论: 存在 n, b = pellZd a1 n
  证明: let ⟨n, h⟩ := @Zsqrtd.le_arch (d a1) b
eq_pell_lem a1 n b b1 hp
h.trans by
      rw [Zsqrtd.natCast_val]
      exact
        Zsqrtd.le_of_le_le (Int.ofNat_le_ofNat_of_le <| le_of_lt <| n_lt_xn _ _)
          (Int.natCast_nonneg _)

Depends on / 依赖: Int.natCast_nonneg, Int.ofNat_le_ofNat_of_le, Zsqrtd, Zsqrtd.le_arch, Zsqrtd.le_of_le_le, Zsqrtd.natCast_val, eq_pell_lem, h.trans, le_arch, le_of_le_le, le_of_lt, n_lt_xn, natCast_nonneg, natCast_val, ofNat_le_ofNat_of_le
-/
theorem eq_pellZd (b : Int√(d a1)) (b1 : 1 <= b) (hp : IsPell b) : exists n, b = pellZd a1 n :=
  let ⟨n, h⟩ := @Zsqrtd.le_arch (d a1) b
eq_pell_lem a1 n b b1 hp
h.trans by
      rw [Zsqrtd.natCast_val]
      exact
        Zsqrtd.le_of_le_le (Int.ofNat_le_ofNat_of_le <| le_of_lt <| n_lt_xn _ _)
          (Int.natCast_nonneg _)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `eq_pell` / 定理 `eq_pell`

English:
theorem eq_pell
  given: {x y : Nat} (hp : x * x - d a1 * y * y = 1)
  statement: exists n, x = xn a1 n ∧ y = yn a1 n
  proof: have : (1 : Int√(d a1)) <= ⟨x, y⟩ :=
    match x, hp with
    | 0, (hp : 0 - _ = 1) => by rw [zero_tsub] at hp; contradiction
    | x + 1, _hp =>
      Zsqrtd.le_of_le_le (Int.ofNat_le_ofNat_of_le <| Nat.succ_pos x) (Int.natCast_nonneg _)
  let ⟨m, e⟩ := eq_pellZd a1 ⟨x, y⟩ this ((isPell_nat a1).2 h

中文:
定理 eq_pell
  条件: {x y : 自然数} (hp : x * x - d a1 * y * y = 1)
  结论: 存在 n, x = xn a1 n ∧ y = yn a1 n
  证明: have : (1 : Int√(d a1)) <= ⟨x, y⟩ :=
    match x, hp with
    | 0, (hp : 0 - _ = 1) => by rw [zero_tsub] at hp; contradiction
    | x + 1, _hp =>
      Zsqrtd.le_of_le_le (Int.ofNat_le_ofNat_of_le <| Nat.succ_pos x) (Int.natCast_nonneg _)
  let ⟨m, e⟩ := eq_pellZd a1 ⟨x, y⟩ this ((isPell_nat a1).2 h

Depends on / 依赖: Int.natCast_nonneg, Int.ofNat_le_ofNat_of_le, Nat.succ_pos, Zsqrtd, Zsqrtd.le_of_le_le, eq_pellZd, isPell_nat, le_of_le_le, natCast_nonneg, ofNat_le_ofNat_of_le, succ_pos, zero_tsub
-/
theorem eq_pell {x y : Nat} (hp : x * x - d a1 * y * y = 1) : exists n, x = xn a1 n ∧ y = yn a1 n :=
  have : (1 : Int√(d a1)) <= ⟨x, y⟩ :=
    match x, hp with
    | 0, (hp : 0 - _ = 1) => by rw [zero_tsub] at hp; contradiction
    | x + 1, _hp =>
      Zsqrtd.le_of_le_le (Int.ofNat_le_ofNat_of_le <| Nat.succ_pos x) (Int.natCast_nonneg _)
  let ⟨m, e⟩ := eq_pellZd a1 ⟨x, y⟩ this ((isPell_nat a1).2 hp)
  ⟨m,
    match x, y, e with
    | _, _, rfl => ⟨rfl, rfl⟩⟩

/--
theorem `pellZd_add` / 定理 `pellZd_add`

English:
theorem pellZd_add
  given: (m)
  statement: forall n, pellZd a1 (m + n) = pellZd a1 m * pellZd a1 n

中文:
定理 pellZd_add
  条件: (m)
  结论: 对任意 n, pellZd a1 (m + n) = pellZd a1 m * pellZd a1 n
-/
theorem pellZd_add (m) : forall n, pellZd a1 (m + n) = pellZd a1 m * pellZd a1 n
  | 0 => (mul_one _).symm
  | n + 1 => by rw [← add_assoc, pellZd_succ, pellZd_succ, pellZd_add _ n, ← mul_assoc]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `xn_add` / 定理 `xn_add`

English:
theorem xn_add
  given: (m n)
  statement: xn a1 (m + n) = xn a1 m * xn a1 n + d a1 * yn a1 m * yn a1 n
  proof: by
  injection pellZd_add a1 m n with h _
  zify
  rw [h]
  simp [pellZd]

中文:
定理 xn_add
  条件: (m n)
  结论: xn a1 (m + n) = xn a1 m * xn a1 n + d a1 * yn a1 m * yn a1 n
  证明: by
  injection pellZd_add a1 m n with h _
  zify
  rw [h]
  simp [pellZd]

Depends on / 依赖: injection, pellZd, pellZd_add
-/
theorem xn_add (m n) : xn a1 (m + n) = xn a1 m * xn a1 n + d a1 * yn a1 m * yn a1 n := by
  injection pellZd_add a1 m n with h _
  zify
  rw [h]
  simp [pellZd]

/--
theorem `yn_add` / 定理 `yn_add`

English:
theorem yn_add
  given: (m n)
  statement: yn a1 (m + n) = xn a1 m * yn a1 n + yn a1 m * xn a1 n
  proof: by
  injection pellZd_add a1 m n with _ h
  zify
  rw [h]
  simp [pellZd]

中文:
定理 yn_add
  条件: (m n)
  结论: yn a1 (m + n) = xn a1 m * yn a1 n + yn a1 m * xn a1 n
  证明: by
  injection pellZd_add a1 m n with _ h
  zify
  rw [h]
  simp [pellZd]

Depends on / 依赖: injection, pellZd, pellZd_add
-/
theorem yn_add (m n) : yn a1 (m + n) = xn a1 m * yn a1 n + yn a1 m * xn a1 n := by
  injection pellZd_add a1 m n with _ h
  zify
  rw [h]
  simp [pellZd]

/--
theorem `pellZd_sub` / 定理 `pellZd_sub`

English:
theorem pellZd_sub
  given: {m n} (h : n <= m)
  statement: pellZd a1 (m - n) = pellZd a1 m * star (pellZd a1 n)
  proof: by
  let t := pellZd_add a1 n (m - n)
  rw [add_tsub_cancel_of_le h] at t
  rw [t]; rw [mul_comm (pellZd _ n) _]; rw [mul_assoc]; rw [isPell_norm.1 (isPell_pellZd _ _)]; rw [mul_one]

中文:
定理 pellZd_sub
  条件: {m n} (h : n <= m)
  结论: pellZd a1 (m - n) = pellZd a1 m * star (pellZd a1 n)
  证明: by
  let t := pellZd_add a1 n (m - n)
  rw [add_tsub_cancel_of_le h] at t
  rw [t]; rw [mul_comm (pellZd _ n) _]; rw [mul_assoc]; rw [isPell_norm.1 (isPell_pellZd _ _)]; rw [mul_one]

Depends on / 依赖: add_tsub_cancel_of_le, isPell_norm, isPell_pellZd, mul_assoc, mul_comm, mul_one, pellZd, pellZd_add
-/
theorem pellZd_sub {m n} (h : n <= m) : pellZd a1 (m - n) = pellZd a1 m * star (pellZd a1 n) := by
  let t := pellZd_add a1 n (m - n)
  rw [add_tsub_cancel_of_le h] at t
  rw [t]; rw [mul_comm (pellZd _ n) _]; rw [mul_assoc]; rw [isPell_norm.1 (isPell_pellZd _ _)]; rw [mul_one]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `xz_sub` / 定理 `xz_sub`

English:
theorem xz_sub
  given: {m n} (h : n <= m)
  proof: by
  rw [sub_eq_add_neg]; rw [← mul_neg]
  exact congr_arg Zsqrtd.re (pellZd_sub a1 h)

中文:
定理 xz_sub
  条件: {m n} (h : n <= m)
  证明: by
  rw [sub_eq_add_neg]; rw [← mul_neg]
  exact congr_arg Zsqrtd.re (pellZd_sub a1 h)

Depends on / 依赖: Zsqrtd, Zsqrtd.re, congr_arg, mul_neg, pellZd_sub, sub_eq_add_neg
-/
theorem xz_sub {m n} (h : n <= m) :
    xz a1 (m - n) = xz a1 m * xz a1 n - d a1 * yz a1 m * yz a1 n := by
  rw [sub_eq_add_neg]; rw [← mul_neg]
  exact congr_arg Zsqrtd.re (pellZd_sub a1 h)

/--
theorem `yz_sub` / 定理 `yz_sub`

English:
theorem yz_sub
  given: {m n} (h : n <= m)
  statement: yz a1 (m - n) = xz a1 n * yz a1 m - xz a1 m * yz a1 n
  proof: by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [mul_comm]; rw [add_comm]
  exact congr_arg Zsqrtd.im (pellZd_sub a1 h)

中文:
定理 yz_sub
  条件: {m n} (h : n <= m)
  结论: yz a1 (m - n) = xz a1 n * yz a1 m - xz a1 m * yz a1 n
  证明: by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [mul_comm]; rw [add_comm]
  exact congr_arg Zsqrtd.im (pellZd_sub a1 h)

Depends on / 依赖: Zsqrtd, Zsqrtd.im, add_comm, congr_arg, mul_comm, mul_neg, pellZd_sub, sub_eq_add_neg
-/
theorem yz_sub {m n} (h : n <= m) : yz a1 (m - n) = xz a1 n * yz a1 m - xz a1 m * yz a1 n := by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [mul_comm]; rw [add_comm]
  exact congr_arg Zsqrtd.im (pellZd_sub a1 h)

/--
theorem `xy_coprime` / 定理 `xy_coprime`

English:
theorem xy_coprime
  given: (n)
  statement: (xn a1 n).Coprime (yn a1 n)
  proof: Nat.coprime_of_dvd' fun k _ kx ky => by
    let p := pell_eq a1 n
    rw [← p]
    exact Nat.dvd_sub (kx.mul_left _) (ky.mul_left _)

中文:
定理 xy_coprime
  条件: (n)
  结论: (xn a1 n).Coprime (yn a1 n)
  证明: Nat.coprime_of_dvd' fun k _ kx ky => by
    let p := pell_eq a1 n
    rw [← p]
    exact Nat.dvd_sub (kx.mul_left _) (ky.mul_left _)

Depends on / 依赖: Nat.coprime_of_dvd, Nat.dvd_sub, coprime_of_dvd, dvd_sub, kx.mul_left, ky.mul_left, mul_left, pell_eq
-/
theorem xy_coprime (n) : (xn a1 n).Coprime (yn a1 n) :=
  Nat.coprime_of_dvd' fun k _ kx ky => by
    let p := pell_eq a1 n
    rw [← p]
    exact Nat.dvd_sub (kx.mul_left _) (ky.mul_left _)

/--
theorem `strictMono_y` / 定理 `strictMono_y`

English:
theorem strictMono_y
  statement: StrictMono (yn a1)
  proof: Or.elim (lt_or_eq_of_le <| Nat.le_of_succ_le_succ h) (fun hl => le_of_lt <| strictMono_y hl)
        fun e => by rw [e]
    simp only [yn_succ, gt_iff_lt]; refine lt_of_le_of_lt ?_ (Nat.lt_add_of_pos_left <| x_pos a1 n)
    rw [← mul_one (yn a1 m)]
    exact mul_le_mul this (le_of_lt a1) (Nat.zero_l

中文:
定理 strictMono_y
  结论: 严格递增 (yn a1)
  证明: Or.elim (lt_or_eq_of_le <| Nat.le_of_succ_le_succ h) (fun hl => le_of_lt <| strictMono_y hl)
        fun e => by rw [e]
    simp only [yn_succ, gt_iff_lt]; refine lt_of_le_of_lt ?_ (Nat.lt_add_of_pos_left <| x_pos a1 n)
    rw [← mul_one (yn a1 m)]
    exact mul_le_mul this (le_of_lt a1) (Nat.zero_l

Depends on / 依赖: Nat.le_of_succ_le_succ, Nat.lt_add_of_pos_left, Nat.zero_le, Or.elim, gt_iff_lt, le_of_lt, le_of_succ_le_succ, lt_add_of_pos_left, lt_of_le_of_lt, lt_or_eq_of_le, mul_le_mul, mul_one, strictMono_y, x_pos, yn_succ, zero_le
-/
theorem strictMono_y : StrictMono (yn a1)
| _, 0, h => absurd h Nat.not_lt_zero _
  | m, n + 1, h => by
    have : yn a1 m <= yn a1 n :=
      Or.elim (lt_or_eq_of_le <| Nat.le_of_succ_le_succ h) (fun hl => le_of_lt <| strictMono_y hl)
        fun e => by rw [e]
    simp only [yn_succ, gt_iff_lt]; refine lt_of_le_of_lt ?_ (Nat.lt_add_of_pos_left <| x_pos a1 n)
    rw [← mul_one (yn a1 m)]
    exact mul_le_mul this (le_of_lt a1) (Nat.zero_le _) (Nat.zero_le _)

/--
theorem `strictMono_x` / 定理 `strictMono_x`

English:
theorem strictMono_x
  statement: StrictMono (xn a1)
  proof: Or.elim (lt_or_eq_of_le <| Nat.le_of_succ_le_succ h) (fun hl => le_of_lt <| strictMono_x hl)
        fun e => by rw [e]
    simp only [xn_succ, gt_iff_lt]
    refine lt_of_lt_of_le (lt_of_le_of_lt this ?_) (Nat.le_add_right _ _)
    have t := Nat.mul_lt_mul_of_pos_left a1 (x_pos a1 n)
    rwa [mul_o

中文:
定理 strictMono_x
  结论: 严格递增 (xn a1)
  证明: Or.elim (lt_or_eq_of_le <| Nat.le_of_succ_le_succ h) (fun hl => le_of_lt <| strictMono_x hl)
        fun e => by rw [e]
    simp only [xn_succ, gt_iff_lt]
    refine lt_of_lt_of_le (lt_of_le_of_lt this ?_) (Nat.le_add_right _ _)
    have t := Nat.mul_lt_mul_of_pos_left a1 (x_pos a1 n)
    rwa [mul_o

Depends on / 依赖: Nat.le_add_right, Nat.le_of_succ_le_succ, Nat.mul_lt_mul_of_pos_left, Or.elim, gt_iff_lt, le_add_right, le_of_lt, le_of_succ_le_succ, lt_of_le_of_lt, lt_of_lt_of_le, lt_or_eq_of_le, mul_lt_mul_of_pos_left, mul_one, strictMono_x, x_pos, xn_succ
-/
theorem strictMono_x : StrictMono (xn a1)
| _, 0, h => absurd h Nat.not_lt_zero _
  | m, n + 1, h => by
    have : xn a1 m <= xn a1 n :=
      Or.elim (lt_or_eq_of_le <| Nat.le_of_succ_le_succ h) (fun hl => le_of_lt <| strictMono_x hl)
        fun e => by rw [e]
    simp only [xn_succ, gt_iff_lt]
    refine lt_of_lt_of_le (lt_of_le_of_lt this ?_) (Nat.le_add_right _ _)
    have t := Nat.mul_lt_mul_of_pos_left a1 (x_pos a1 n)
    rwa [mul_one] at t

/--
theorem `yn_ge_n` / 定理 `yn_ge_n`

English:
theorem yn_ge_n
  statement: forall n, n <= yn a1 n

中文:
定理 yn_ge_n
  结论: 对任意 n, n <= yn a1 n
-/
theorem yn_ge_n : forall n, n <= yn a1 n
  | 0 => Nat.zero_le _
  | n + 1 =>
    show n < yn a1 (n + 1) from lt_of_le_of_lt (yn_ge_n n) (strictMono_y a1 <| Nat.lt_succ_self n)

/--
theorem `y_mul_dvd` / 定理 `y_mul_dvd`

English:
theorem y_mul_dvd
  given: (n)
  statement: forall k, yn a1 n ∣ yn a1 (n * k)

中文:
定理 y_mul_dvd
  条件: (n)
  结论: 对任意 k, yn a1 n ∣ yn a1 (n * k)
-/
theorem y_mul_dvd (n) : forall k, yn a1 n ∣ yn a1 (n * k)
  | 0 => dvd_zero _
  | k + 1 => by
    rw [Nat.mul_succ]; rw [yn_add]; exact dvd_add (dvd_mul_left _ _) ((y_mul_dvd _ k).mul_right _)

/--
theorem `y_dvd_iff` / 定理 `y_dvd_iff`

English:
theorem y_dvd_iff
  given: (m n)
  statement: yn a1 m ∣ yn a1 n ↔ m ∣ n
  proof: ⟨fun h =>
Nat.dvd_of_mod_eq_zero
      (Nat.eq_zero_or_pos _).resolve_right fun hp => by
        have co : Nat.Coprime (yn a1 m) (xn a1 (m * (n / m))) :=
Nat.Coprime.symm (xy_coprime a1 _).coprime_dvd_right (y_mul_dvd a1 m (n / m))
        have m0 : 0 < m :=
          m.eq_zero_or_pos.resolve_left f

中文:
定理 y_dvd_iff
  条件: (m n)
  结论: yn a1 m ∣ yn a1 n ↔ m ∣ n
  证明: ⟨fun h =>
Nat.dvd_of_mod_eq_zero
      (Nat.eq_zero_or_pos _).resolve_right fun hp => by
        have co : Nat.Coprime (yn a1 m) (xn a1 (m * (n / m))) :=
Nat.Coprime.symm (xy_coprime a1 _).coprime_dvd_right (y_mul_dvd a1 m (n / m))
        have m0 : 0 < m :=
          m.eq_zero_or_pos.resolve_left f

Depends on / 依赖: Coprime, Nat.Coprime, Nat.Coprime.symm, Nat.dvd_of_mod_eq_zero, Nat.eq_zero_or_pos, Nat.mod_add_div, Nat.mod_lt, Nat.mod_zero, _root_, _root_.ne_of_lt, coprime_dvd_right, dvd_of_mod_eq_zero, eq_zero_of_zero_dvd, eq_zero_or_pos, m.eq_zero_or_pos.resolve_left, mod_add_div, mod_lt, mod_zero, ne_of_lt, not_le_of_gt
-/
theorem y_dvd_iff (m n) : yn a1 m ∣ yn a1 n ↔ m ∣ n :=
  ⟨fun h =>
Nat.dvd_of_mod_eq_zero
      (Nat.eq_zero_or_pos _).resolve_right fun hp => by
        have co : Nat.Coprime (yn a1 m) (xn a1 (m * (n / m))) :=
Nat.Coprime.symm (xy_coprime a1 _).coprime_dvd_right (y_mul_dvd a1 m (n / m))
        have m0 : 0 < m :=
          m.eq_zero_or_pos.resolve_left fun e => by
            rw [e]; rw [Nat.mod_zero] at hp;rw [e] at h
            exact _root_.ne_of_lt (strictMono_y a1 hp) (eq_zero_of_zero_dvd h).symm
        rw [← Nat.mod_add_div n m]; rw [yn_add] at h
        exact
          not_le_of_gt (strictMono_y _ <| Nat.mod_lt n m0)
            (Nat.le_of_dvd (strictMono_y _ hp) <|
co.dvd_of_dvd_mul_right
                (Nat.dvd_add_iff_right <| (y_mul_dvd _ _ _).mul_left _).2 h),
    fun ⟨k, e⟩ => by rw [e]; apply y_mul_dvd⟩

/--
theorem `xy_modEq_yn` / 定理 `xy_modEq_yn`

English:
theorem xy_modEq_yn
  given: (n)
  proof: xy_modEq_yn n k
    have L : xn a1 (n * k) * xn a1 n + d a1 * yn a1 (n * k) * yn a1 n ≡
        xn a1 n ^ k * xn a1 n + 0 [MOD yn a1 n ^ 2] := by
      gcongr
      rw [modEq_zero_iff_dvd]; rw [sq]
      gcongr
      apply dvd_mul_of_dvd_right
      rw [← modEq_zero_iff_dvd]
      refine (hy.of_dvd 

中文:
定理 xy_modEq_yn
  条件: (n)
  证明: xy_modEq_yn n k
    have L : xn a1 (n * k) * xn a1 n + d a1 * yn a1 (n * k) * yn a1 n ≡
        xn a1 n ^ k * xn a1 n + 0 [MOD yn a1 n ^ 2] := by
      gcongr
      rw [modEq_zero_iff_dvd]; rw [sq]
      gcongr
      apply dvd_mul_of_dvd_right
      rw [← modEq_zero_iff_dvd]
      refine (hy.of_dvd 

Depends on / 依赖: xy_modEq_yn
-/
theorem xy_modEq_yn (n) :
    forall k, xn a1 (n * k) ≡ xn a1 n ^ k [MOD yn a1 n ^ 2] ∧ yn a1 (n * k) ≡
        k * xn a1 n ^ (k - 1) * yn a1 n [MOD yn a1 n ^ 3]
  | 0 => by simp [Nat.ModEq.refl]
  | k + 1 => by
    let ⟨hx, hy⟩ := xy_modEq_yn n k
    have L : xn a1 (n * k) * xn a1 n + d a1 * yn a1 (n * k) * yn a1 n ≡
        xn a1 n ^ k * xn a1 n + 0 [MOD yn a1 n ^ 2] := by
      gcongr
      rw [modEq_zero_iff_dvd]; rw [sq]
      gcongr
      apply dvd_mul_of_dvd_right
      rw [← modEq_zero_iff_dvd]
      refine (hy.of_dvd <| dvd_pow_self _ <| by decide).trans ?_
      simp [modEq_zero_iff_dvd]
    have R : xn a1 (n * k) * yn a1 n + yn a1 (n * k) * xn a1 n ≡
        xn a1 n ^ k * yn a1 n + k * xn a1 n ^ k * yn a1 n [MOD yn a1 n ^ 3] := by
      gcongr ?_ + ?_
      · rw [_root_.pow_succ]
        exact hx.mul_right' _
      · have : k * xn a1 n ^ (k - 1) * yn a1 n * xn a1 n = k * xn a1 n ^ k * yn a1 n := by
          rcases k with - | k <;> simp [_root_.pow_succ]; ring_nf
        rw [← this]
        gcongr
    rw [add_tsub_cancel_right]; rw [Nat.mul_succ]; rw [xn_add]; rw [yn_add]; rw [pow_succ (xn _ n)]; rw [Nat.succ_mul]; rw [add_comm (k * xn _ n ^ k) (xn _ n ^ k)]; rw [right_distrib]
    exact ⟨L, R⟩

/--
theorem `ysq_dvd_yy` / 定理 `ysq_dvd_yy`

English:
theorem ysq_dvd_yy
  given: (n)
  statement: yn a1 n * yn a1 n ∣ yn a1 (n * yn a1 n)
  proof: modEq_zero_iff_dvd.1
    ((xy_modEq_yn a1 n (yn a1 n)).right.of_dvd <| by simp [_root_.pow_succ]).trans
      (modEq_zero_iff_dvd.2 <| by simp [mul_dvd_mul_left, mul_assoc])

中文:
定理 ysq_dvd_yy
  条件: (n)
  结论: yn a1 n * yn a1 n ∣ yn a1 (n * yn a1 n)
  证明: modEq_zero_iff_dvd.1
    ((xy_modEq_yn a1 n (yn a1 n)).right.of_dvd <| by simp [_root_.pow_succ]).trans
      (modEq_zero_iff_dvd.2 <| by simp [mul_dvd_mul_left, mul_assoc])

Depends on / 依赖: _root_, _root_.pow_succ, modEq_zero_iff_dvd, mul_assoc, mul_dvd_mul_left, of_dvd, pow_succ, right.of_dvd, xy_modEq_yn
-/
theorem ysq_dvd_yy (n) : yn a1 n * yn a1 n ∣ yn a1 (n * yn a1 n) :=
modEq_zero_iff_dvd.1
    ((xy_modEq_yn a1 n (yn a1 n)).right.of_dvd <| by simp [_root_.pow_succ]).trans
      (modEq_zero_iff_dvd.2 <| by simp [mul_dvd_mul_left, mul_assoc])

/--
theorem `dvd_of_ysq_dvd` / 定理 `dvd_of_ysq_dvd`

English:
theorem dvd_of_ysq_dvd
  given: {n t} (h : yn a1 n * yn a1 n ∣ yn a1 t)
  statement: yn a1 n ∣ t
  proof: have nt : n ∣ t := (y_dvd_iff a1 n t).1 dvd_of_mul_left_dvd h
  n.eq_zero_or_pos.elim (fun n0 => by rwa [n0] at nt ⊢) fun n0l : 0 < n => by
    let ⟨k, ke⟩ := nt
    have : yn a1 n ∣ k * xn a1 n ^ (k - 1) :=
Nat.dvd_of_mul_dvd_mul_right (strictMono_y a1 n0l)
modEq_zero_iff_dvd.1 by
          have xm

中文:
定理 dvd_of_ysq_dvd
  条件: {n t} (h : yn a1 n * yn a1 n ∣ yn a1 t)
  结论: yn a1 n ∣ t
  证明: have nt : n ∣ t := (y_dvd_iff a1 n t).1 dvd_of_mul_left_dvd h
  n.eq_zero_or_pos.elim (fun n0 => by rwa [n0] at nt ⊢) fun n0l : 0 < n => by
    let ⟨k, ke⟩ := nt
    have : yn a1 n ∣ k * xn a1 n ^ (k - 1) :=
Nat.dvd_of_mul_dvd_mul_right (strictMono_y a1 n0l)
modEq_zero_iff_dvd.1 by
          have xm

Depends on / 依赖: Nat.dvd_of_mul_dvd_mul_right, _root_, _root_.pow_succ, dvd_mul_of_dvd_right, dvd_of_dvd_mul_right, dvd_of_mul_dvd_mul_right, dvd_of_mul_left_dvd, eq_zero_or_pos, h.modEq_zero_nat, modEq_zero_iff_dvd, modEq_zero_nat, n.eq_zero_or_pos.elim, of_dvd, pow_left, pow_succ, strictMono_y, symm.dvd_of_dvd_mul_right, symm.trans, xm.of_dvd, xy_coprime
-/
theorem dvd_of_ysq_dvd {n t} (h : yn a1 n * yn a1 n ∣ yn a1 t) : yn a1 n ∣ t :=
have nt : n ∣ t := (y_dvd_iff a1 n t).1 dvd_of_mul_left_dvd h
  n.eq_zero_or_pos.elim (fun n0 => by rwa [n0] at nt ⊢) fun n0l : 0 < n => by
    let ⟨k, ke⟩ := nt
    have : yn a1 n ∣ k * xn a1 n ^ (k - 1) :=
Nat.dvd_of_mul_dvd_mul_right (strictMono_y a1 n0l)
modEq_zero_iff_dvd.1 by
          have xm := (xy_modEq_yn a1 n k).right; rw [← ke] at xm
          exact (xm.of_dvd <| by simp [_root_.pow_succ]).symm.trans h.modEq_zero_nat
    rw [ke]
    exact dvd_mul_of_dvd_right (((xy_coprime _ _).pow_left _).symm.dvd_of_dvd_mul_right this) _

/--
theorem `pellZd_succ_succ` / 定理 `pellZd_succ_succ`

English:
theorem pellZd_succ_succ
  given: (n)
  proof: by
  ext <;> simp [dz_val, az] <;> ring_nf

中文:
定理 pellZd_succ_succ
  条件: (n)
  证明: by
  ext <;> simp [dz_val, az] <;> ring_nf

Depends on / 依赖: dz_val, ring_nf
-/
theorem pellZd_succ_succ (n) :
    pellZd a1 (n + 2) + pellZd a1 n = (2 * a : Nat) * pellZd a1 (n + 1) := by
  ext <;> simp [dz_val, az] <;> ring_nf

/--
theorem `xy_succ_succ` / 定理 `xy_succ_succ`

English:
theorem xy_succ_succ
  given: (n)
  proof: by
  have := pellZd_succ_succ a1 n; unfold pellZd at this
  rw [Zsqrtd.nsmul_val (2 * a : Nat)] at this
  injection this with h₁ h₂
  grind

中文:
定理 xy_succ_succ
  条件: (n)
  证明: by
  have := pellZd_succ_succ a1 n; unfold pellZd at this
  rw [Zsqrtd.nsmul_val (2 * a : Nat)] at this
  injection this with h₁ h₂
  grind

Depends on / 依赖: Zsqrtd, Zsqrtd.nsmul_val, injection, nsmul_val, pellZd, pellZd_succ_succ
-/
theorem xy_succ_succ (n) :
    xn a1 (n + 2) + xn a1 n =
      2 * a * xn a1 (n + 1) ∧ yn a1 (n + 2) + yn a1 n = 2 * a * yn a1 (n + 1) := by
  have := pellZd_succ_succ a1 n; unfold pellZd at this
  rw [Zsqrtd.nsmul_val (2 * a : Nat)] at this
  injection this with h₁ h₂
  grind

/--
theorem `xn_succ_succ` / 定理 `xn_succ_succ`

English:
theorem xn_succ_succ
  given: (n)
  statement: xn a1 (n + 2) + xn a1 n = 2 * a * xn a1 (n + 1)
  proof: (xy_succ_succ a1 n).1

中文:
定理 xn_succ_succ
  条件: (n)
  结论: xn a1 (n + 2) + xn a1 n = 2 * a * xn a1 (n + 1)
  证明: (xy_succ_succ a1 n).1

Depends on / 依赖: xy_succ_succ
-/
theorem xn_succ_succ (n) : xn a1 (n + 2) + xn a1 n = 2 * a * xn a1 (n + 1) :=
  (xy_succ_succ a1 n).1

/--
theorem `yn_succ_succ` / 定理 `yn_succ_succ`

English:
theorem yn_succ_succ
  given: (n)
  statement: yn a1 (n + 2) + yn a1 n = 2 * a * yn a1 (n + 1)
  proof: (xy_succ_succ a1 n).2

中文:
定理 yn_succ_succ
  条件: (n)
  结论: yn a1 (n + 2) + yn a1 n = 2 * a * yn a1 (n + 1)
  证明: (xy_succ_succ a1 n).2

Depends on / 依赖: xy_succ_succ
-/
theorem yn_succ_succ (n) : yn a1 (n + 2) + yn a1 n = 2 * a * yn a1 (n + 1) :=
  (xy_succ_succ a1 n).2

/--
theorem `xz_succ_succ` / 定理 `xz_succ_succ`

English:
theorem xz_succ_succ
  given: (n)
  statement: xz a1 (n + 2) = (2 * a : Nat) * xz a1 (n + 1) - xz a1 n
  proof: eq_sub_of_add_eq by delta xz; rw [← Int.natCast_add, ← Int.natCast_mul, xn_succ_succ]

中文:
定理 xz_succ_succ
  条件: (n)
  结论: xz a1 (n + 2) = (2 * a : 自然数) * xz a1 (n + 1) - xz a1 n
  证明: eq_sub_of_add_eq by delta xz; rw [← Int.natCast_add, ← Int.natCast_mul, xn_succ_succ]

Depends on / 依赖: Int.natCast_add, Int.natCast_mul, eq_sub_of_add_eq, natCast_add, natCast_mul, xn_succ_succ
-/
theorem xz_succ_succ (n) : xz a1 (n + 2) = (2 * a : Nat) * xz a1 (n + 1) - xz a1 n :=
eq_sub_of_add_eq by delta xz; rw [← Int.natCast_add, ← Int.natCast_mul, xn_succ_succ]

/--
theorem `yz_succ_succ` / 定理 `yz_succ_succ`

English:
theorem yz_succ_succ
  given: (n)
  statement: yz a1 (n + 2) = (2 * a : Nat) * yz a1 (n + 1) - yz a1 n
  proof: eq_sub_of_add_eq by delta yz; rw [← Int.natCast_add, ← Int.natCast_mul, yn_succ_succ]

中文:
定理 yz_succ_succ
  条件: (n)
  结论: yz a1 (n + 2) = (2 * a : 自然数) * yz a1 (n + 1) - yz a1 n
  证明: eq_sub_of_add_eq by delta yz; rw [← Int.natCast_add, ← Int.natCast_mul, yn_succ_succ]

Depends on / 依赖: Int.natCast_add, Int.natCast_mul, eq_sub_of_add_eq, natCast_add, natCast_mul, yn_succ_succ
-/
theorem yz_succ_succ (n) : yz a1 (n + 2) = (2 * a : Nat) * yz a1 (n + 1) - yz a1 n :=
eq_sub_of_add_eq by delta yz; rw [← Int.natCast_add, ← Int.natCast_mul, yn_succ_succ]

/--
theorem `yn_modEq_a_sub_one` / 定理 `yn_modEq_a_sub_one`

English:
theorem yn_modEq_a_sub_one
  statement: forall n, yn a1 n ≡ n [MOD a - 1]

中文:
定理 yn_modEq_a_sub_one
  结论: 对任意 n, yn a1 n ≡ n [MOD a - 1]
-/
theorem yn_modEq_a_sub_one : forall n, yn a1 n ≡ n [MOD a - 1]
  | 0 => by simp [Nat.ModEq.refl]
  | 1 => by simp [Nat.ModEq.refl]
  | n + 2 =>
(yn_modEq_a_sub_one n).add_right_cancel by
      rw [yn_succ_succ]; rw [(by ring : n + 2 + n = 2 * (n + 1))]
      exact ((modEq_sub a1.le).mul_left 2).mul (yn_modEq_a_sub_one (n + 1))

/--
theorem `yn_modEq_two` / 定理 `yn_modEq_two`

English:
theorem yn_modEq_two
  statement: forall n, yn a1 n ≡ n [MOD 2]

中文:
定理 yn_modEq_two
  结论: 对任意 n, yn a1 n ≡ n [MOD 2]
-/
theorem yn_modEq_two : forall n, yn a1 n ≡ n [MOD 2]
  | 0 => by rfl
  | 1 => by simp [Nat.ModEq.refl]
  | n + 2 =>
(yn_modEq_two n).add_right_cancel by
      rw [yn_succ_succ]; rw [mul_assoc]; rw [(by ring : n + 2 + n = 2 * (n + 1))]
      exact (dvd_mul_right 2 _).modEq_zero_nat.trans (dvd_mul_right 2 _).zero_modEq_nat

section

/--
theorem `x_sub_y_dvd_pow_lem` / 定理 `x_sub_y_dvd_pow_lem`

English:
theorem x_sub_y_dvd_pow_lem
  given: (y2 y1 y0 yn1 yn0 xn1 xn0 ay a2 : Int)
  proof: by
  ring

中文:
定理 x_sub_y_dvd_pow_lem
  条件: (y2 y1 y0 yn1 yn0 xn1 xn0 ay a2 : 整数)
  证明: by
  ring
-/
theorem x_sub_y_dvd_pow_lem (y2 y1 y0 yn1 yn0 xn1 xn0 ay a2 : Int) :
    (a2 * yn1 - yn0) * ay + y2 - (a2 * xn1 - xn0) =
      y2 - a2 * y1 + y0 + a2 * (yn1 * ay + y1 - xn1) - (yn0 * ay + y0 - xn0) := by
  ring

end

/--
theorem `x_sub_y_dvd_pow` / 定理 `x_sub_y_dvd_pow`

English:
theorem x_sub_y_dvd_pow
  given: (y : Nat)
  proof: ⟨-↑(y ^ n), by
        simp [_root_.pow_succ, mul_comm, mul_left_comm]
        ring⟩
    rw [xz_succ_succ]; rw [yz_succ_succ]; rw [x_sub_y_dvd_pow_lem ↑(y ^ (n + 2)) ↑(y ^ (n + 1)) ↑(y ^ n)]
    exact _root_.dvd_sub (dvd_add this <| (x_sub_y_dvd_pow _ (n + 1)).mul_left _)
      (x_sub_y_dvd_pow _ n)

中文:
定理 x_sub_y_dvd_pow
  条件: (y : 自然数)
  证明: ⟨-↑(y ^ n), by
        simp [_root_.pow_succ, mul_comm, mul_left_comm]
        ring⟩
    rw [xz_succ_succ]; rw [yz_succ_succ]; rw [x_sub_y_dvd_pow_lem ↑(y ^ (n + 2)) ↑(y ^ (n + 1)) ↑(y ^ n)]
    exact _root_.dvd_sub (dvd_add this <| (x_sub_y_dvd_pow _ (n + 1)).mul_left _)
      (x_sub_y_dvd_pow _ n)

Depends on / 依赖: _root_, _root_.dvd_sub, _root_.pow_succ, dvd_add, dvd_sub, mul_comm, mul_left, mul_left_comm, pow_succ, x_sub_y_dvd_pow, x_sub_y_dvd_pow_lem, xz_succ_succ, yz_succ_succ
-/
theorem x_sub_y_dvd_pow (y : Nat) :
    forall n, (2 * a * y - y * y - 1 : Int) ∣ yz a1 n * (a - y) + ↑(y ^ n) - xz a1 n
  | 0 => by simp [xz, yz]
  | 1 => by simp [xz, yz]
  | n + 2 => by
    have : (2 * a * y - y * y - 1 : Int) ∣ ↑(y ^ (n + 2)) - ↑(2 * a) * ↑(y ^ (n + 1)) + ↑(y ^ n) :=
      ⟨-↑(y ^ n), by
        simp [_root_.pow_succ, mul_comm, mul_left_comm]
        ring⟩
    rw [xz_succ_succ]; rw [yz_succ_succ]; rw [x_sub_y_dvd_pow_lem ↑(y ^ (n + 2)) ↑(y ^ (n + 1)) ↑(y ^ n)]
    exact _root_.dvd_sub (dvd_add this <| (x_sub_y_dvd_pow _ (n + 1)).mul_left _)
      (x_sub_y_dvd_pow _ n)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `xn_modEq_x2n_add_lem` / 定理 `xn_modEq_x2n_add_lem`

English:
theorem xn_modEq_x2n_add_lem
  given: (n j)
  statement: xn a1 n ∣ d a1 * yn a1 n * (yn a1 n * xn a1 j) + xn a1 j
  proof: by
  have h1 : d a1 * yn a1 n * (yn a1 n * xn a1 j) + xn a1 j =
      (d a1 * yn a1 n * yn a1 n + 1) * xn a1 j := by
    simp [add_mul, mul_assoc]
  have h2 : d a1 * yn a1 n * yn a1 n + 1 = xn a1 n * xn a1 n := by
    zify at *
    apply add_eq_of_eq_sub' (Eq.symm (pell_eqz a1 n))
  rw [h2] at h1; r

中文:
定理 xn_modEq_x2n_add_lem
  条件: (n j)
  结论: xn a1 n ∣ d a1 * yn a1 n * (yn a1 n * xn a1 j) + xn a1 j
  证明: by
  have h1 : d a1 * yn a1 n * (yn a1 n * xn a1 j) + xn a1 j =
      (d a1 * yn a1 n * yn a1 n + 1) * xn a1 j := by
    simp [add_mul, mul_assoc]
  have h2 : d a1 * yn a1 n * yn a1 n + 1 = xn a1 n * xn a1 n := by
    zify at *
    apply add_eq_of_eq_sub' (Eq.symm (pell_eqz a1 n))
  rw [h2] at h1; r

Depends on / 依赖: Eq.symm, add_eq_of_eq_sub, add_mul, dvd_mul_right, mul_assoc, pell_eqz
-/
theorem xn_modEq_x2n_add_lem (n j) : xn a1 n ∣ d a1 * yn a1 n * (yn a1 n * xn a1 j) + xn a1 j := by
  have h1 : d a1 * yn a1 n * (yn a1 n * xn a1 j) + xn a1 j =
      (d a1 * yn a1 n * yn a1 n + 1) * xn a1 j := by
    simp [add_mul, mul_assoc]
  have h2 : d a1 * yn a1 n * yn a1 n + 1 = xn a1 n * xn a1 n := by
    zify at *
    apply add_eq_of_eq_sub' (Eq.symm (pell_eqz a1 n))
  rw [h2] at h1; rw [h1, mul_assoc]; exact dvd_mul_right _ _

/--
theorem `xn_modEq_x2n_add` / 定理 `xn_modEq_x2n_add`

English:
theorem xn_modEq_x2n_add
  given: (n j)
  statement: xn a1 (2 * n + j) + xn a1 j ≡ 0 [MOD xn a1 n]
  proof: by
  rw [two_mul]; rw [add_assoc]; rw [xn_add]; rw [add_assoc]; rw [← zero_add 0]
  refine (dvd_mul_right (xn a1 n) (xn a1 (n + j))).modEq_zero_nat.add ?_
  rw [yn_add]; rw [left_distrib]; rw [add_assoc]; rw [← zero_add 0]
  exact
    ((dvd_mul_right _ _).mul_left _).modEq_zero_nat.add (xn_modEq_x2n

中文:
定理 xn_modEq_x2n_add
  条件: (n j)
  结论: xn a1 (2 * n + j) + xn a1 j ≡ 0 [MOD xn a1 n]
  证明: by
  rw [two_mul]; rw [add_assoc]; rw [xn_add]; rw [add_assoc]; rw [← zero_add 0]
  refine (dvd_mul_right (xn a1 n) (xn a1 (n + j))).modEq_zero_nat.add ?_
  rw [yn_add]; rw [left_distrib]; rw [add_assoc]; rw [← zero_add 0]
  exact
    ((dvd_mul_right _ _).mul_left _).modEq_zero_nat.add (xn_modEq_x2n

Depends on / 依赖: add_assoc, dvd_mul_right, left_distrib, modEq_zero_nat, modEq_zero_nat.add, mul_left, two_mul, xn_add, xn_modEq_x2n_add_lem, yn_add, zero_add
-/
theorem xn_modEq_x2n_add (n j) : xn a1 (2 * n + j) + xn a1 j ≡ 0 [MOD xn a1 n] := by
  rw [two_mul]; rw [add_assoc]; rw [xn_add]; rw [add_assoc]; rw [← zero_add 0]
  refine (dvd_mul_right (xn a1 n) (xn a1 (n + j))).modEq_zero_nat.add ?_
  rw [yn_add]; rw [left_distrib]; rw [add_assoc]; rw [← zero_add 0]
  exact
    ((dvd_mul_right _ _).mul_left _).modEq_zero_nat.add (xn_modEq_x2n_add_lem _ _ _).modEq_zero_nat

/--
theorem `xn_modEq_x2n_sub_lem` / 定理 `xn_modEq_x2n_sub_lem`

English:
theorem xn_modEq_x2n_sub_lem
  given: {n j} (h : j <= n)
  statement: xn a1 (2 * n - j) + xn a1 j ≡ 0 [MOD xn a1 n]
  proof: by
  have h1 : xz a1 n ∣ d a1 * yz a1 n * yz a1 (n - j) + xz a1 j := by
    rw [yz_sub _ h]; rw [mul_sub_left_distrib]; rw [sub_add_eq_add_sub]
    exact
      dvd_sub
        (by
          delta xz; delta yz
          rw [mul_comm (xn _ _ : Int)]
          exact mod_cast (xn_modEq_x2n_add_lem _ n j

中文:
定理 xn_modEq_x2n_sub_lem
  条件: {n j} (h : j <= n)
  结论: xn a1 (2 * n - j) + xn a1 j ≡ 0 [MOD xn a1 n]
  证明: by
  have h1 : xz a1 n ∣ d a1 * yz a1 n * yz a1 (n - j) + xz a1 j := by
    rw [yz_sub _ h]; rw [mul_sub_left_distrib]; rw [sub_add_eq_add_sub]
    exact
      dvd_sub
        (by
          delta xz; delta yz
          rw [mul_comm (xn _ _ : Int)]
          exact mod_cast (xn_modEq_x2n_add_lem _ n j

Depends on / 依赖: Int.natCast_dvd_natCast, add_assoc, add_tsub_assoc_of_le, dvd_mul_right, dvd_sub, modEq_zero_nat, modEq_zero_nat.add, mod_cast, mul_comm, mul_left, mul_sub_left_distrib, natCast_dvd_natCast, sub_add_eq_add_sub, two_mul, xn_add, xn_modEq_x2n_add_lem, yz_sub, zero_add
-/
theorem xn_modEq_x2n_sub_lem {n j} (h : j <= n) : xn a1 (2 * n - j) + xn a1 j ≡ 0 [MOD xn a1 n] := by
  have h1 : xz a1 n ∣ d a1 * yz a1 n * yz a1 (n - j) + xz a1 j := by
    rw [yz_sub _ h]; rw [mul_sub_left_distrib]; rw [sub_add_eq_add_sub]
    exact
      dvd_sub
        (by
          delta xz; delta yz
          rw [mul_comm (xn _ _ : Int)]
          exact mod_cast (xn_modEq_x2n_add_lem _ n j))
        ((dvd_mul_right _ _).mul_left _)
  rw [two_mul]; rw [add_tsub_assoc_of_le h]; rw [xn_add]; rw [add_assoc]; rw [← zero_add 0]
  exact
    (dvd_mul_right _ _).modEq_zero_nat.add
      (Int.natCast_dvd_natCast.1 <| by simpa [xz, yz] using h1).modEq_zero_nat

/--
theorem `xn_modEq_x2n_sub` / 定理 `xn_modEq_x2n_sub`

English:
theorem xn_modEq_x2n_sub
  given: {n j} (h : j <= 2 * n)
  statement: xn a1 (2 * n - j) + xn a1 j ≡ 0 [MOD xn a1 n]
  proof: (le_total j n).elim (xn_modEq_x2n_sub_lem a1) fun jn => by
    have : 2 * n - j + j <= n + j := by
      rw [tsub_add_cancel_of_le h]; rw [two_mul]; exact Nat.add_le_add_left jn _
    let t := xn_modEq_x2n_sub_lem a1 (Nat.le_of_add_le_add_right this)
    rwa [tsub_tsub_cancel_of_le h, add_comm] at t

中文:
定理 xn_modEq_x2n_sub
  条件: {n j} (h : j <= 2 * n)
  结论: xn a1 (2 * n - j) + xn a1 j ≡ 0 [MOD xn a1 n]
  证明: (le_total j n).elim (xn_modEq_x2n_sub_lem a1) fun jn => by
    have : 2 * n - j + j <= n + j := by
      rw [tsub_add_cancel_of_le h]; rw [two_mul]; exact Nat.add_le_add_left jn _
    let t := xn_modEq_x2n_sub_lem a1 (Nat.le_of_add_le_add_right this)
    rwa [tsub_tsub_cancel_of_le h, add_comm] at t

Depends on / 依赖: Nat.add_le_add_left, Nat.le_of_add_le_add_right, add_comm, add_le_add_left, le_of_add_le_add_right, le_total, tsub_add_cancel_of_le, tsub_tsub_cancel_of_le, two_mul, xn_modEq_x2n_sub_lem
-/
theorem xn_modEq_x2n_sub {n j} (h : j <= 2 * n) : xn a1 (2 * n - j) + xn a1 j ≡ 0 [MOD xn a1 n] :=
  (le_total j n).elim (xn_modEq_x2n_sub_lem a1) fun jn => by
    have : 2 * n - j + j <= n + j := by
      rw [tsub_add_cancel_of_le h]; rw [two_mul]; exact Nat.add_le_add_left jn _
    let t := xn_modEq_x2n_sub_lem a1 (Nat.le_of_add_le_add_right this)
    rwa [tsub_tsub_cancel_of_le h, add_comm] at t

/--
theorem `xn_modEq_x4n_add` / 定理 `xn_modEq_x4n_add`

English:
theorem xn_modEq_x4n_add
  given: (n j)
  statement: xn a1 (4 * n + j) ≡ xn a1 j [MOD xn a1 n]
  proof: ModEq.add_right_cancel' (xn a1 (2 * n + j)) by
    refine @ModEq.trans _ _ 0 _ ?_ (by rw [add_comm]; exact (xn_modEq_x2n_add _ _ _).symm)
    rw [show 4 * n = 2 * n + 2 * n from right_distrib 2 2 n]; rw [add_assoc]
    apply xn_modEq_x2n_add

中文:
定理 xn_modEq_x4n_add
  条件: (n j)
  结论: xn a1 (4 * n + j) ≡ xn a1 j [MOD xn a1 n]
  证明: ModEq.add_right_cancel' (xn a1 (2 * n + j)) by
    refine @ModEq.trans _ _ 0 _ ?_ (by rw [add_comm]; exact (xn_modEq_x2n_add _ _ _).symm)
    rw [show 4 * n = 2 * n + 2 * n from right_distrib 2 2 n]; rw [add_assoc]
    apply xn_modEq_x2n_add

Depends on / 依赖: ModEq.add_right_cancel, ModEq.trans, add_assoc, add_comm, add_right_cancel, right_distrib, xn_modEq_x2n_add
-/
theorem xn_modEq_x4n_add (n j) : xn a1 (4 * n + j) ≡ xn a1 j [MOD xn a1 n] :=
ModEq.add_right_cancel' (xn a1 (2 * n + j)) by
    refine @ModEq.trans _ _ 0 _ ?_ (by rw [add_comm]; exact (xn_modEq_x2n_add _ _ _).symm)
    rw [show 4 * n = 2 * n + 2 * n from right_distrib 2 2 n]; rw [add_assoc]
    apply xn_modEq_x2n_add

/--
theorem `xn_modEq_x4n_sub` / 定理 `xn_modEq_x4n_sub`

English:
theorem xn_modEq_x4n_sub
  given: {n j} (h : j <= 2 * n)
  statement: xn a1 (4 * n - j) ≡ xn a1 j [MOD xn a1 n]
  proof: have h' : j <= 2 * n := le_trans h (by rw [Nat.succ_mul])
ModEq.add_right_cancel' (xn a1 (2 * n - j)) by
    refine @ModEq.trans _ _ 0 _ ?_ (by rw [add_comm]; exact (xn_modEq_x2n_sub _ h).symm)
    rw [show 4 * n = 2 * n + 2 * n from right_distrib 2 2 n]; rw [add_tsub_assoc_of_le h']
    apply xn_mo

中文:
定理 xn_modEq_x4n_sub
  条件: {n j} (h : j <= 2 * n)
  结论: xn a1 (4 * n - j) ≡ xn a1 j [MOD xn a1 n]
  证明: have h' : j <= 2 * n := le_trans h (by rw [Nat.succ_mul])
ModEq.add_right_cancel' (xn a1 (2 * n - j)) by
    refine @ModEq.trans _ _ 0 _ ?_ (by rw [add_comm]; exact (xn_modEq_x2n_sub _ h).symm)
    rw [show 4 * n = 2 * n + 2 * n from right_distrib 2 2 n]; rw [add_tsub_assoc_of_le h']
    apply xn_mo

Depends on / 依赖: ModEq.add_right_cancel, ModEq.trans, Nat.succ_mul, add_comm, add_right_cancel, add_tsub_assoc_of_le, le_trans, right_distrib, succ_mul, xn_modEq_x2n_add, xn_modEq_x2n_sub
-/
theorem xn_modEq_x4n_sub {n j} (h : j <= 2 * n) : xn a1 (4 * n - j) ≡ xn a1 j [MOD xn a1 n] :=
  have h' : j <= 2 * n := le_trans h (by rw [Nat.succ_mul])
ModEq.add_right_cancel' (xn a1 (2 * n - j)) by
    refine @ModEq.trans _ _ 0 _ ?_ (by rw [add_comm]; exact (xn_modEq_x2n_sub _ h).symm)
    rw [show 4 * n = 2 * n + 2 * n from right_distrib 2 2 n]; rw [add_tsub_assoc_of_le h']
    apply xn_modEq_x2n_add

/--
theorem `eq_of_xn_modEq_lem1` / 定理 `eq_of_xn_modEq_lem1`

English:
theorem eq_of_xn_modEq_lem1
  given: {i n}
  statement: forall {j}, i < j -> j < n -> xn a1 i % xn a1 n < xn a1 j % xn a1 n

中文:
定理 eq_of_xn_modEq_lem1
  条件: {i n}
  结论: 对任意 {j}, i < j -> j < n -> xn a1 i % xn a1 n < xn a1 j % xn a1 n
-/
theorem eq_of_xn_modEq_lem1 {i n} : forall {j}, i < j -> j < n -> xn a1 i % xn a1 n < xn a1 j % xn a1 n
  | 0, ij, _ => absurd ij (Nat.not_lt_zero _)
  | j + 1, ij, jn => by
    suffices xn a1 j % xn a1 n < xn a1 (j + 1) % xn a1 n from
      (lt_or_eq_of_le (Nat.le_of_succ_le_succ ij)).elim
        (fun h => lt_trans (eq_of_xn_modEq_lem1 h (le_of_lt jn)) this) fun h => by
        rw [h]; exact this
    rw [Nat.mod_eq_of_lt (strictMono_x _ (Nat.lt_of_succ_lt jn))]; rw [Nat.mod_eq_of_lt (strictMono_x _ jn)]
    exact strictMono_x _ (Nat.lt_succ_self _)

/--
theorem `eq_of_xn_modEq_lem2` / 定理 `eq_of_xn_modEq_lem2`

English:
theorem eq_of_xn_modEq_lem2
  given: {n} (h : 2 * xn a1 n = xn a1 (n + 1))
  statement: a = 2 ∧ n = 0
  proof: by
  rw [xn_succ]; rw [mul_comm] at h
  have : n = 0 :=
    n.eq_zero_or_pos.resolve_right fun np =>
      _root_.ne_of_lt
        (lt_of_le_of_lt (Nat.mul_le_mul_left _ a1)
          (Nat.lt_add_of_pos_right <| mul_pos (d_pos a1) (strictMono_y a1 np)))
        h
  cases this; simp at h; exact ⟨h.sy

中文:
定理 eq_of_xn_modEq_lem2
  条件: {n} (h : 2 * xn a1 n = xn a1 (n + 1))
  结论: a = 2 ∧ n = 0
  证明: by
  rw [xn_succ]; rw [mul_comm] at h
  have : n = 0 :=
    n.eq_zero_or_pos.resolve_right fun np =>
      _root_.ne_of_lt
        (lt_of_le_of_lt (Nat.mul_le_mul_left _ a1)
          (Nat.lt_add_of_pos_right <| mul_pos (d_pos a1) (strictMono_y a1 np)))
        h
  cases this; simp at h; exact ⟨h.sy

Depends on / 依赖: Nat.lt_add_of_pos_right, Nat.mul_le_mul_left, _root_, _root_.ne_of_lt, d_pos, eq_zero_or_pos, h.symm, lt_add_of_pos_right, lt_of_le_of_lt, mul_comm, mul_le_mul_left, mul_pos, n.eq_zero_or_pos.resolve_right, ne_of_lt, resolve_right, strictMono_y, xn_succ
-/
theorem eq_of_xn_modEq_lem2 {n} (h : 2 * xn a1 n = xn a1 (n + 1)) : a = 2 ∧ n = 0 := by
  rw [xn_succ]; rw [mul_comm] at h
  have : n = 0 :=
    n.eq_zero_or_pos.resolve_right fun np =>
      _root_.ne_of_lt
        (lt_of_le_of_lt (Nat.mul_le_mul_left _ a1)
          (Nat.lt_add_of_pos_right <| mul_pos (d_pos a1) (strictMono_y a1 np)))
        h
  cases this; simp at h; exact ⟨h.symm, rfl⟩

/--
theorem `eq_of_xn_modEq_lem3` / 定理 `eq_of_xn_modEq_lem3`

English:
theorem eq_of_xn_modEq_lem3
  given: {i n} (npos : 0 < n)
  proof: fun k kn k2n => by
      let k2nl : 2 * n - k < n := by lia
have xle : xn a1 (2 * n - k) <= xn a1 n := le_of_lt strictMono_x a1 k2nl
      suffices xn a1 k % xn a1 n = xn a1 n - xn a1 (2 * n - k) by rw [this, Int.ofNat_sub xle]
      rw [← Nat.mod_eq_of_lt (Nat.sub_lt (x_pos a1 n) (x_pos a1 (2 * n -

中文:
定理 eq_of_xn_modEq_lem3
  条件: {i n} (npos : 0 < n)
  证明: fun k kn k2n => by
      let k2nl : 2 * n - k < n := by lia
have xle : xn a1 (2 * n - k) <= xn a1 n := le_of_lt strictMono_x a1 k2nl
      suffices xn a1 k % xn a1 n = xn a1 n - xn a1 (2 * n - k) by rw [this, Int.ofNat_sub xle]
      rw [← Nat.mod_eq_of_lt (Nat.sub_lt (x_pos a1 n) (x_pos a1 (2 * n -

Depends on / 依赖: Int.ofNat_sub, ModEq.add_right_cancel, Nat.mod_eq_of_lt, Nat.sub_lt, add_right_cancel, dvd_rfl, dvd_rfl.zero_modEq_nat, k2nl.le, le_of_lt, lt_trichotomy, mod_eq_of_lt, ofNat_sub, strictMono_x, sub_lt, t.trans, tsub_add_cancel_of_le, tsub_tsub_cancel_of_le, x_pos, xn_modEq_x2n_sub_lem, zero_modEq_nat
-/
theorem eq_of_xn_modEq_lem3 {i n} (npos : 0 < n) :
    forall {j}, i < j -> j <= 2 * n -> j != n -> ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2) ->
        xn a1 i % xn a1 n < xn a1 j % xn a1 n
  | 0, ij, _, _, _ => absurd ij (Nat.not_lt_zero _)
  | j + 1, ij, j2n, jnn, ntriv =>
    have lem2 : forall k > n, k <= 2 * n -> (↑(xn a1 k % xn a1 n) : Int) =
        xn a1 n - xn a1 (2 * n - k) := fun k kn k2n => by
      let k2nl : 2 * n - k < n := by lia
have xle : xn a1 (2 * n - k) <= xn a1 n := le_of_lt strictMono_x a1 k2nl
      suffices xn a1 k % xn a1 n = xn a1 n - xn a1 (2 * n - k) by rw [this, Int.ofNat_sub xle]
      rw [← Nat.mod_eq_of_lt (Nat.sub_lt (x_pos a1 n) (x_pos a1 (2 * n - k)))]
      apply ModEq.add_right_cancel' (xn a1 (2 * n - k))
      rw [tsub_add_cancel_of_le xle]
      have t := xn_modEq_x2n_sub_lem a1 k2nl.le
      rw [tsub_tsub_cancel_of_le k2n] at t
      exact t.trans dvd_rfl.zero_modEq_nat
    (lt_trichotomy j n).elim (fun jn : j < n => eq_of_xn_modEq_lem1 _ ij (lt_of_le_of_ne jn jnn))
      fun o =>
      o.elim
        (fun jn : j = n => by
          cases jn
          apply Int.lt_of_ofNat_lt_ofNat
          rw [lem2 (n + 1) (Nat.lt_succ_self _) j2n]; rw [show 2 * n - (n + 1) = n - 1 by
              rw [two_mul]; rw [tsub_add_eq_tsub_tsub]; rw [add_tsub_cancel_right]]
          refine lt_sub_left_of_add_lt (Int.ofNat_lt_ofNat_of_lt ?_)
rcases lt_or_eq_of_le Nat.le_of_succ_le_succ ij with lin | ein
          · rw [Nat.mod_eq_of_lt (strictMono_x _ lin)]
            have ll : xn a1 (n - 1) + xn a1 (n - 1) <= xn a1 n := by
              rw [← two_mul]; rw [mul_comm]; rw [show xn a1 n = xn a1 (n - 1 + 1) by rw [tsub_add_cancel_of_le (succ_le_of_lt npos)],
                xn_succ]
              exact le_trans (Nat.mul_le_mul_left _ a1) (Nat.le_add_right _ _)
            have npm : (n - 1).succ = n := Nat.succ_pred_eq_of_pos npos
            have il : i <= n - 1 := by
              apply Nat.le_of_succ_le_succ
              rw [npm]
              exact lin
            rcases lt_or_eq_of_le il with ill | ile
            · exact lt_of_lt_of_le (Nat.add_lt_add_left (strictMono_x a1 ill) _) ll
            · rw [ile]
              apply lt_of_le_of_ne ll
              rw [← two_mul]
              exact fun e =>
ntriv by
                  let ⟨a2, s1⟩ :=
                    @eq_of_xn_modEq_lem2 _ a1 (n - 1)
                      (by rwa [tsub_add_cancel_of_le (succ_le_of_lt npos)])
                  have n1 : n = 1 := le_antisymm (tsub_eq_zero_iff_le.mp s1) npos
                  rw [ile]; rw [a2]; rw [n1]; exact ⟨rfl, rfl, rfl, rfl⟩
          · rw [ein, Nat.mod_self, add_zero]
            exact strictMono_x _ (Nat.pred_lt npos.ne'))
        fun jn : j > n =>
        have lem1 : j != n -> xn a1 j % xn a1 n < xn a1 (j + 1) % xn a1 n ->
            xn a1 i % xn a1 n < xn a1 (j + 1) % xn a1 n :=
          fun jn s =>
          (lt_or_eq_of_le (Nat.le_of_succ_le_succ ij)).elim
            (fun h =>
              lt_trans
                (eq_of_xn_modEq_lem3 npos h (le_of_lt (Nat.lt_of_succ_le j2n)) jn
                    fun ⟨_, n1, _, j2⟩ => by
                      rw [n1]; rw [j2] at j2n; exact absurd j2n (by decide))
                s)
            fun h => by rw [h]; exact s
lem1 (_root_.ne_of_gt jn)
Int.lt_of_ofNat_lt_ofNat by
            rw [lem2 j jn (le_of_lt j2n)]; rw [lem2 (j + 1) (Nat.le_succ_of_le jn) j2n]
            refine sub_lt_sub_left (Int.ofNat_lt_ofNat_of_lt <| strictMono_x _ ?_) _
            rw [Nat.sub_succ]
            exact Nat.pred_lt (_root_.ne_of_gt <| tsub_pos_of_lt j2n)

/--
theorem `eq_of_xn_modEq_le` / 定理 `eq_of_xn_modEq_le`

English:
theorem eq_of_xn_modEq_le
  statement: {i j n} (ij : i <= j) (j2n : j <= 2 * n)
  proof: if npos : n = 0 then by simp_all
  else
    (lt_or_eq_of_le ij).resolve_left fun ij' =>
      if jn : j = n then by
        refine _root_.ne_of_gt ?_ h
        rw [jn]; rw [Nat.mod_self]
        have x0 : 0 < xn a1 0 % xn a1 n := by
          rw [Nat.mod_eq_of_lt (strictMono_x a1 (Nat.pos_of_ne_zero

中文:
定理 eq_of_xn_modEq_le
  结论: {i j n} (ij : i <= j) (j2n : j <= 2 * n)
  证明: if npos : n = 0 then by simp_all
  else
    (lt_or_eq_of_le ij).resolve_left fun ij' =>
      if jn : j = n then by
        refine _root_.ne_of_gt ?_ h
        rw [jn]; rw [Nat.mod_self]
        have x0 : 0 < xn a1 0 % xn a1 n := by
          rw [Nat.mod_eq_of_lt (strictMono_x a1 (Nat.pos_of_ne_zero

Depends on / 依赖: Nat.mod_eq_of_lt, Nat.mod_self, Nat.pos_of_ne_zero, Nat.succ_pos, _root_, _root_.ne_of_gt, _root_.ne_of_lt, eq_of_xn_modEq_lem3, le_trans, lt_or_eq_of_le, mod_eq_of_lt, mod_self, ne_of_gt, ne_of_lt, pos_of_ne_zero, resolve_left, strictMono_x, succ_pos, x0.trans
-/
theorem eq_of_xn_modEq_le {i j n} (ij : i <= j) (j2n : j <= 2 * n)
    (h : xn a1 i ≡ xn a1 j [MOD xn a1 n])
    (ntriv : ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2)) : i = j :=
  if npos : n = 0 then by simp_all
  else
    (lt_or_eq_of_le ij).resolve_left fun ij' =>
      if jn : j = n then by
        refine _root_.ne_of_gt ?_ h
        rw [jn]; rw [Nat.mod_self]
        have x0 : 0 < xn a1 0 % xn a1 n := by
          rw [Nat.mod_eq_of_lt (strictMono_x a1 (Nat.pos_of_ne_zero npos))]
          exact Nat.succ_pos _
        rcases i with - | i
        · exact x0
        rw [jn] at ij'
        exact
          x0.trans
            (eq_of_xn_modEq_lem3 _ (Nat.pos_of_ne_zero npos) (Nat.succ_pos _) (le_trans ij j2n)
              (_root_.ne_of_lt ij') fun ⟨_, n1, _, i2⟩ => by
              rw [n1]; rw [i2] at ij'; exact absurd ij' (by decide))
      else _root_.ne_of_lt (eq_of_xn_modEq_lem3 a1 (Nat.pos_of_ne_zero npos) ij' j2n jn ntriv) h

/--
theorem `eq_of_xn_modEq` / 定理 `eq_of_xn_modEq`

English:
theorem eq_of_xn_modEq
  statement: {i j n} (i2n : i <= 2 * n) (j2n : j <= 2 * n)
  proof: (le_total i j).elim
    (fun ij => eq_of_xn_modEq_le a1 ij j2n h fun ⟨a2, n1, i0, j2⟩ => (ntriv a2 n1).left i0 j2)
    fun ij =>
    (eq_of_xn_modEq_le a1 ij i2n h.symm fun ⟨a2, n1, j0, i2⟩ => (ntriv a2 n1).right i2 j0).symm

中文:
定理 eq_of_xn_modEq
  结论: {i j n} (i2n : i <= 2 * n) (j2n : j <= 2 * n)
  证明: (le_total i j).elim
    (fun ij => eq_of_xn_modEq_le a1 ij j2n h fun ⟨a2, n1, i0, j2⟩ => (ntriv a2 n1).left i0 j2)
    fun ij =>
    (eq_of_xn_modEq_le a1 ij i2n h.symm fun ⟨a2, n1, j0, i2⟩ => (ntriv a2 n1).right i2 j0).symm

Depends on / 依赖: eq_of_xn_modEq_le, h.symm, le_total
-/
theorem eq_of_xn_modEq {i j n} (i2n : i <= 2 * n) (j2n : j <= 2 * n)
    (h : xn a1 i ≡ xn a1 j [MOD xn a1 n])
    (ntriv : a = 2 -> n = 1 -> (i = 0 -> j != 2) ∧ (i = 2 -> j != 0)) : i = j :=
  (le_total i j).elim
    (fun ij => eq_of_xn_modEq_le a1 ij j2n h fun ⟨a2, n1, i0, j2⟩ => (ntriv a2 n1).left i0 j2)
    fun ij =>
    (eq_of_xn_modEq_le a1 ij i2n h.symm fun ⟨a2, n1, j0, i2⟩ => (ntriv a2 n1).right i2 j0).symm

/--
theorem `eq_of_xn_modEq'` / 定理 `eq_of_xn_modEq'`

English:
theorem eq_of_xn_modEq'
  statement: {i j n} (ipos : 0 < i) (hin : i <= n) (j4n : j <= 4 * n)
  proof: have i2n : i <= 2 * n := by apply le_trans hin; rw [two_mul]; apply Nat.le_add_left
  (le_or_gt j (2 * n)).imp
    (fun j2n : j <= 2 * n =>
      eq_of_xn_modEq a1 j2n i2n h fun _ n1 =>
        ⟨fun _ i2 => by rw [n1, i2] at hin; exact absurd hin (by decide), fun _ i0 =>
          _root_.ne_of_gt ip

中文:
定理 eq_of_xn_modEq'
  结论: {i j n} (ipos : 0 < i) (hin : i <= n) (j4n : j <= 4 * n)
  证明: have i2n : i <= 2 * n := by apply le_trans hin; rw [two_mul]; apply Nat.le_add_left
  (le_or_gt j (2 * n)).imp
    (fun j2n : j <= 2 * n =>
      eq_of_xn_modEq a1 j2n i2n h fun _ n1 =>
        ⟨fun _ i2 => by rw [n1, i2] at hin; exact absurd hin (by decide), fun _ i0 =>
          _root_.ne_of_gt ip

Depends on / 依赖: Nat.le_add_left, _root_, _root_.ne_of_gt, absurd, add_tsub_cancel_of_le, eq_of_xn_modEq, h.symm.trans, le_add_left, le_or_gt, le_trans, ne_of_gt, tsub_tsub, two_mul, xn_modEq_x4n_sub
-/
theorem eq_of_xn_modEq' {i j n} (ipos : 0 < i) (hin : i <= n) (j4n : j <= 4 * n)
    (h : xn a1 j ≡ xn a1 i [MOD xn a1 n]) : j = i ∨ j + i = 4 * n :=
  have i2n : i <= 2 * n := by apply le_trans hin; rw [two_mul]; apply Nat.le_add_left
  (le_or_gt j (2 * n)).imp
    (fun j2n : j <= 2 * n =>
      eq_of_xn_modEq a1 j2n i2n h fun _ n1 =>
        ⟨fun _ i2 => by rw [n1, i2] at hin; exact absurd hin (by decide), fun _ i0 =>
          _root_.ne_of_gt ipos i0⟩)
    fun j2n : 2 * n < j =>
    suffices i = 4 * n - j by rw [this, add_tsub_cancel_of_le j4n]
    have j42n : 4 * n - j <= 2 * n := by lia
    eq_of_xn_modEq a1 i2n j42n
      (h.symm.trans <| by
        let t := xn_modEq_x4n_sub a1 j42n
        rwa [tsub_tsub_cancel_of_le j4n] at t)
      (by lia)

/--
theorem `modEq_of_xn_modEq` / 定理 `modEq_of_xn_modEq`

English:
theorem modEq_of_xn_modEq
  statement: {i j n} (ipos : 0 < i) (hin : i <= n)
  proof: let j' := j % (4 * n)
  have n4 : 0 < 4 * n := mul_pos (by decide) (ipos.trans_le hin)
  have jl : j' < 4 * n := Nat.mod_lt _ n4
  have jj : j ≡ j' [MOD 4 * n] := by delta ModEq; rw [Nat.mod_eq_of_lt jl]
  have : forall j q, xn a1 (j + 4 * n * q) ≡ xn a1 j [MOD xn a1 n] := by
    intro j q; inductio

中文:
定理 modEq_of_xn_modEq
  结论: {i j n} (ipos : 0 < i) (hin : i <= n)
  证明: let j' := j % (4 * n)
  have n4 : 0 < 4 * n := mul_pos (by decide) (ipos.trans_le hin)
  have jl : j' < 4 * n := Nat.mod_lt _ n4
  have jj : j ≡ j' [MOD 4 * n] := by delta ModEq; rw [Nat.mod_eq_of_lt jl]
  have : forall j q, xn a1 (j + 4 * n * q) ≡ xn a1 j [MOD xn a1 n] := by
    intro j q; inductio

Depends on / 依赖: ModEq.refl, Nat.mod_eq_of_lt, Nat.mod_lt, Nat.mul_succ, Or.imp, add_assoc, add_comm, ipos.trans_le, mod_eq_of_lt, mod_lt, mul_pos, mul_succ, trans_le, xn_modEq_x4n_add
-/
theorem modEq_of_xn_modEq {i j n} (ipos : 0 < i) (hin : i <= n)
    (h : xn a1 j ≡ xn a1 i [MOD xn a1 n]) :
    j ≡ i [MOD 4 * n] ∨ j + i ≡ 0 [MOD 4 * n] :=
  let j' := j % (4 * n)
  have n4 : 0 < 4 * n := mul_pos (by decide) (ipos.trans_le hin)
  have jl : j' < 4 * n := Nat.mod_lt _ n4
  have jj : j ≡ j' [MOD 4 * n] := by delta ModEq; rw [Nat.mod_eq_of_lt jl]
  have : forall j q, xn a1 (j + 4 * n * q) ≡ xn a1 j [MOD xn a1 n] := by
    intro j q; induction q with
    | zero => simp [ModEq.refl]
    | succ q IH =>
      rw [Nat.mul_succ]; rw [← add_assoc]; rw [add_comm]
      exact (xn_modEq_x4n_add _ _ _).trans IH
  Or.imp (fun ji : j' = i => by rwa [← ji])
    (fun ji : j' + i = 4 * n =>
(jj.add_right _).trans by
        rw [ji]
        exact dvd_rfl.modEq_zero_nat)
    (eq_of_xn_modEq' a1 ipos hin jl.le <|
      (h.symm.trans <| by
          rw [← Nat.mod_add_div j (4 * n)]
          exact this j' _).symm)

end

/--
theorem `xy_modEq_of_modEq` / 定理 `xy_modEq_of_modEq`

English:
theorem xy_modEq_of_modEq
  given: {a b c} (a1 : 1 < a) (b1 : 1 < b) (h : a ≡ b [MOD c])

中文:
定理 xy_modEq_of_modEq
  条件: {a b c} (a1 : 1 < a) (b1 : 1 < b) (h : a ≡ b [MOD c])
-/
theorem xy_modEq_of_modEq {a b c} (a1 : 1 < a) (b1 : 1 < b) (h : a ≡ b [MOD c]) :
    forall n, xn a1 n ≡ xn b1 n [MOD c] ∧ yn a1 n ≡ yn b1 n [MOD c]
  | 0 => by simp [Nat.ModEq.refl]
  | 1 => by simpa [Nat.ModEq.refl]
  | n + 2 =>
⟨(xy_modEq_of_modEq a1 b1 h n).left.add_right_cancel by
        rw [xn_succ_succ a1]; rw [xn_succ_succ b1]
        exact (h.mul_left _).mul (xy_modEq_of_modEq _ _ h (n + 1)).left,
(xy_modEq_of_modEq a1 b1 h n).right.add_right_cancel by
        rw [yn_succ_succ a1]; rw [yn_succ_succ b1]
        exact (h.mul_left _).mul (xy_modEq_of_modEq _ _ h (n + 1)).right⟩

/--
theorem `matiyasevic` / 定理 `matiyasevic`

English:
theorem matiyasevic
  given: {a k x y}
  proof: ⟨fun ⟨a1, hx, hy⟩ => by
    rw [← hx]; rw [← hy]
    refine ⟨a1,
        (Nat.eq_zero_or_pos k).elim (fun k0 => by rw [k0]; exact ⟨le_rfl, Or.inl ⟨rfl, rfl⟩⟩)
          fun kpos => ?_⟩
    exact
      let x := xn a1 k
      let y := yn a1 k
      let m := 2 * (k * y)
      let u := xn a1 m
      let

中文:
定理 matiyasevic
  条件: {a k x y}
  证明: ⟨fun ⟨a1, hx, hy⟩ => by
    rw [← hx]; rw [← hy]
    refine ⟨a1,
        (Nat.eq_zero_or_pos k).elim (fun k0 => by rw [k0]; exact ⟨le_rfl, Or.inl ⟨rfl, rfl⟩⟩)
          fun kpos => ?_⟩
    exact
      let x := xn a1 k
      let y := yn a1 k
      let m := 2 * (k * y)
      let u := xn a1 m
      let

Depends on / 依赖: Coprime, Nat.Coprime, Nat.eq_zero_or_pos, Or.inl, dvd_mul_left, dvd_mul_right, eq_zero_or_pos, le_rfl, modEq_zero_, modEq_zero_iff_dvd, y_dvd_iff, yn_ge_n, yn_modEq_two, ysq_dvd_yy
-/
theorem matiyasevic {a k x y} :
    (exists a1 : 1 < a, xn a1 k = x ∧ yn a1 k = y) ↔
      1 < a ∧ k <= y ∧ (x = 1 ∧ y = 0 ∨
        exists u v s t b : Nat,
          x * x - (a * a - 1) * y * y = 1 ∧ u * u - (a * a - 1) * v * v = 1 ∧
          s * s - (b * b - 1) * t * t = 1 ∧ 1 < b ∧ b ≡ 1 [MOD 4 * y] ∧
          b ≡ a [MOD u] ∧ 0 < v ∧ y * y ∣ v ∧ s ≡ x [MOD u] ∧ t ≡ k [MOD 4 * y]) :=
  ⟨fun ⟨a1, hx, hy⟩ => by
    rw [← hx]; rw [← hy]
    refine ⟨a1,
        (Nat.eq_zero_or_pos k).elim (fun k0 => by rw [k0]; exact ⟨le_rfl, Or.inl ⟨rfl, rfl⟩⟩)
          fun kpos => ?_⟩
    exact
      let x := xn a1 k
      let y := yn a1 k
      let m := 2 * (k * y)
      let u := xn a1 m
      let v := yn a1 m
      have ky : k <= y := yn_ge_n a1 k
have yv : y * y ∣ v := (ysq_dvd_yy a1 k).trans (y_dvd_iff _ _ _).2 dvd_mul_left _ _
      have uco : Nat.Coprime u (4 * y) :=
        have : 2 ∣ v :=
modEq_zero_iff_dvd.1 (yn_modEq_two _ _).trans (dvd_mul_right _ _).modEq_zero_nat
        have : Nat.Coprime u 2 := (xy_coprime a1 m).coprime_dvd_right this
(this.mul_right this).mul_right
          (xy_coprime _ _).coprime_dvd_right (dvd_of_mul_left_dvd yv)
      let ⟨b, ba, bm1⟩ := chineseRemainder uco a 1
      have m1 : 1 < m :=
        have : 0 < k * y := mul_pos kpos (strictMono_y a1 kpos)
        Nat.mul_le_mul_left 2 this
      have vp : 0 < v := strictMono_y a1 (lt_trans zero_lt_one m1)
      have b1 : 1 < b :=
        have : xn a1 1 < u := strictMono_x a1 m1
        have : a < u := by simpa using this
lt_of_lt_of_le a1 by
          delta ModEq at ba; rw [Nat.mod_eq_of_lt this] at ba; rw [← ba]
          apply Nat.mod_le
      let s := xn b1 k
      let t := yn b1 k
      have sx : s ≡ x [MOD u] := (xy_modEq_of_modEq b1 a1 ba k).left
      have tk : t ≡ k [MOD 4 * y] :=
        have : 4 * y ∣ b - 1 :=
Int.natCast_dvd_natCast.1 by rw [Int.ofNat_sub (le_of_lt b1)]; exact bm1.symm.dvd
        (yn_modEq_a_sub_one _ _).of_dvd this
      ⟨ky,
        Or.inr
          ⟨u, v, s, t, b, pell_eq _ _, pell_eq _ _, pell_eq _ _, b1, bm1, ba, vp, yv, sx, tk⟩⟩,
    fun ⟨a1, ky, o⟩ =>
    ⟨a1,
      match o with
      | Or.inl ⟨x1, y0⟩ => by
        rw [y0] at ky; rw [Nat.eq_zero_of_le_zero ky, x1, y0]; exact ⟨rfl, rfl⟩
      | Or.inr ⟨u, v, s, t, b, xy, uv, st, b1, rem⟩ =>
        match x, y, eq_pell a1 xy, u, v, eq_pell a1 uv, s, t, eq_pell b1 st, rem, ky with
        | _, _, ⟨i, rfl, rfl⟩, _, _, ⟨n, rfl, rfl⟩, _, _, ⟨j, rfl, rfl⟩,
          ⟨(bm1 : b ≡ 1 [MOD 4 * yn a1 i]), (ba : b ≡ a [MOD xn a1 n]), (vp : 0 < yn a1 n),
            (yv : yn a1 i * yn a1 i ∣ yn a1 n), (sx : xn b1 j ≡ xn a1 i [MOD xn a1 n]),
            (tk : yn b1 j ≡ k [MOD 4 * yn a1 i])⟩,
          (ky : k <= yn a1 i) =>
          (Nat.eq_zero_or_pos i).elim
            (fun i0 => by
              simp only [i0, yn_zero, nonpos_iff_eq_zero] at ky; rw [i0, ky]; exact ⟨rfl, rfl⟩)
            fun ipos => by
            suffices i = k by rw [this]; exact ⟨rfl, rfl⟩
            clear o rem xy uv st
            have iln : i <= n :=
              le_of_not_gt fun hin =>
                not_lt_of_ge (Nat.le_of_dvd vp (dvd_of_mul_left_dvd yv)) (strictMono_y a1 hin)
            have yd : 4 * yn a1 i ∣ 4 * n := by gcongr; exact dvd_of_ysq_dvd a1 yv
            have jk : j ≡ k [MOD 4 * yn a1 i] :=
              have : 4 * yn a1 i ∣ b - 1 :=
Int.natCast_dvd_natCast.1 by rw [Int.ofNat_sub (le_of_lt b1)]; exact bm1.symm.dvd
              ((yn_modEq_a_sub_one b1 _).of_dvd this).symm.trans tk
            have ki : k + i < 4 * yn a1 i :=
lt_of_le_of_lt (_root_.add_le_add ky (yn_ge_n a1 i)) by
                rw [← two_mul]
                exact Nat.mul_lt_mul_of_pos_right (by decide) (strictMono_y a1 ipos)
            have ji : j ≡ i [MOD 4 * n] :=
              have : xn a1 j ≡ xn a1 i [MOD xn a1 n] :=
                (xy_modEq_of_modEq b1 a1 ba j).left.symm.trans sx
              (modEq_of_xn_modEq a1 ipos iln this).resolve_right
                fun ji : j + i ≡ 0 [MOD 4 * n] =>
not_le_of_gt ki
Nat.le_of_dvd (lt_of_lt_of_le ipos <| Nat.le_add_left _ _)
modEq_zero_iff_dvd.1 (jk.symm.add_right i).trans ji.of_dvd yd
            have : i % (4 * yn a1 i) = k % (4 * yn a1 i) := (ji.of_dvd yd).symm.trans jk
            rwa [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_add_left _ _) ki),
              Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_add_right _ _) ki)] at this⟩⟩

/--
theorem `eq_pow_of_pell_lem` / 定理 `eq_pow_of_pell_lem`

English:
theorem eq_pow_of_pell_lem
  given: {a y k : Nat} (hy0 : y != 0) (hk0 : k != 0) (hyk : y ^ k < a)
  proof: have hya : y < a := (Nat.le_self_pow hk0 _).trans_lt hyk
  calc
    (↑(y ^ k) : Int) < a := Nat.cast_lt.2 hyk
    _ <= (a : Int) ^ 2 - (a - 1 : Int) ^ 2 - 1 := by lia
    _ <= (a : Int) ^ 2 - (a - y : Int) ^ 2 - 1 := by
      have := hya.le
      gcongr <;> norm_cast <;> lia
    _ = 2 * a * y - y * 

中文:
定理 eq_pow_of_pell_lem
  条件: {a y k : 自然数} (hy0 : y != 0) (hk0 : k != 0) (hyk : y ^ k < a)
  证明: have hya : y < a := (Nat.le_self_pow hk0 _).trans_lt hyk
  calc
    (↑(y ^ k) : Int) < a := Nat.cast_lt.2 hyk
    _ <= (a : Int) ^ 2 - (a - 1 : Int) ^ 2 - 1 := by lia
    _ <= (a : Int) ^ 2 - (a - y : Int) ^ 2 - 1 := by
      have := hya.le
      gcongr <;> norm_cast <;> lia
    _ = 2 * a * y - y * 

Depends on / 依赖: Nat.cast_lt, Nat.le_self_pow, cast_lt, hya.le, le_self_pow, trans_lt
-/
theorem eq_pow_of_pell_lem {a y k : Nat} (hy0 : y != 0) (hk0 : k != 0) (hyk : y ^ k < a) :
    (↑(y ^ k) : Int) < 2 * a * y - y * y - 1 :=
  have hya : y < a := (Nat.le_self_pow hk0 _).trans_lt hyk
  calc
    (↑(y ^ k) : Int) < a := Nat.cast_lt.2 hyk
    _ <= (a : Int) ^ 2 - (a - 1 : Int) ^ 2 - 1 := by lia
    _ <= (a : Int) ^ 2 - (a - y : Int) ^ 2 - 1 := by
      have := hya.le
      gcongr <;> norm_cast <;> lia
    _ = 2 * a * y - y * y - 1 := by ring

/--
theorem `eq_pow_of_pell` / 定理 `eq_pow_of_pell`

English:
theorem eq_pow_of_pell
  given: {m n k}
  proof: by
  constructor
  · rintro rfl
    refine k.eq_zero_or_pos.imp (fun k0 : k = 0 => k0.symm ▸ ⟨rfl, rfl⟩) fun hk => ⟨hk, ?_⟩
    refine n.eq_zero_or_pos.imp (fun n0 : n = 0 => n0.symm ▸ ⟨rfl, zero_pow hk.ne'⟩)
      fun hn => ⟨hn, ?_⟩
    set w := max n k
    have nw : n <= w := le_max_left _ _
    h

中文:
定理 eq_pow_of_pell
  条件: {m n k}
  证明: by
  constructor
  · rintro rfl
    refine k.eq_zero_or_pos.imp (fun k0 : k = 0 => k0.symm ▸ ⟨rfl, rfl⟩) fun hk => ⟨hk, ?_⟩
    refine n.eq_zero_or_pos.imp (fun n0 : n = 0 => n0.symm ▸ ⟨rfl, zero_pow hk.ne'⟩)
      fun hn => ⟨hn, ?_⟩
    set w := max n k
    have nw : n <= w := le_max_left _ _
    h

Depends on / 依赖: Nat.succ_lt_succ, eq_zero_or_pos, hk.ne, hn.trans_le, k.eq_zero_or_pos.imp, k0.symm, le_max_left, le_max_right, n.eq_zero_or_pos.imp, n0.symm, n_lt_xn, nw.trans, strictMono_x, succ_lt_succ, trans_le, zero_pow
-/
theorem eq_pow_of_pell {m n k} :
    n ^ k = m ↔ k = 0 ∧ m = 1 ∨ 0 < k ∧ (n = 0 ∧ m = 0 ∨
      0 < n ∧ exists (w a t z : Nat) (a1 : 1 < a), xn a1 k ≡ yn a1 k * (a - n) + m [MOD t] ∧
      2 * a * n = t + (n * n + 1) ∧ m < t ∧
      n <= w ∧ k <= w ∧ a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1) := by
  constructor
  · rintro rfl
    refine k.eq_zero_or_pos.imp (fun k0 : k = 0 => k0.symm ▸ ⟨rfl, rfl⟩) fun hk => ⟨hk, ?_⟩
    refine n.eq_zero_or_pos.imp (fun n0 : n = 0 => n0.symm ▸ ⟨rfl, zero_pow hk.ne'⟩)
      fun hn => ⟨hn, ?_⟩
    set w := max n k
    have nw : n <= w := le_max_left _ _
    have kw : k <= w := le_max_right _ _
    have wpos : 0 < w := hn.trans_le nw
    have w1 : 1 < w + 1 := Nat.succ_lt_succ wpos
    set a := xn w1 w
    have a1 : 1 < a := strictMono_x w1 wpos
    have na : n <= a := nw.trans (n_lt_xn w1 w).le
    set x := xn a1 k
    set y := yn a1 k
    obtain ⟨z, ze⟩ : w ∣ yn w1 w :=
      modEq_zero_iff_dvd.1 ((yn_modEq_a_sub_one w1 w).trans dvd_rfl.modEq_zero_nat)
    have nt : (↑(n ^ k) : Int) < 2 * a * n - n * n - 1 := by
      refine eq_pow_of_pell_lem hn.ne' hk.ne' ?_
      calc
        n ^ k <= n ^ w := Nat.pow_le_pow_right hn kw
        _ < (w + 1) ^ w := Nat.pow_lt_pow_left (Nat.lt_succ_of_le nw) wpos.ne'
        _ <= a := xn_ge_a_pow w1 w
    lift (2 * a * n - n * n - 1 : Int) to Nat using (Nat.cast_nonneg _).trans nt.le with t te
    have tm : x ≡ y * (a - n) + n ^ k [MOD t] := by
      apply modEq_of_dvd
      rw [Int.natCast_add]; rw [Int.natCast_mul]; rw [Int.ofNat_sub na]; rw [te]
      exact x_sub_y_dvd_pow a1 n k
    have ta : 2 * a * n = t + (n * n + 1) := by
      zify
      lia
    have zp : a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1 := ze ▸ pell_eq w1 w
    exact ⟨w, a, t, z, a1, tm, ta, Nat.cast_lt.1 nt, nw, kw, zp⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hk0, ⟨rfl, rfl⟩ | ⟨hn0, w, a, t, z, a1, tm, ta, mt, nw, kw, zp⟩⟩)
    · exact _root_.pow_zero n
    · exact zero_pow hk0.ne'
    have hw0 : 0 < w := hn0.trans_le nw
    have hw1 : 1 < w + 1 := Nat.succ_lt_succ hw0
    rcases eq_pell hw1 zp with ⟨j, rfl, yj⟩
    have hj0 : 0 < j := by
      apply Nat.pos_of_ne_zero
      rintro rfl
      exact lt_irrefl 1 a1
    have wj : w <= j :=
      Nat.le_of_dvd hj0
        (modEq_zero_iff_dvd.1 <|
(yn_modEq_a_sub_one hw1 j).symm.trans modEq_zero_iff_dvd.2 ⟨z, yj.symm⟩)
    have hnka : n ^ k < xn hw1 j := calc
      n ^ k <= n ^ j := Nat.pow_le_pow_right hn0 (le_trans kw wj)
      _ < (w + 1) ^ j := Nat.pow_lt_pow_left (Nat.lt_succ_of_le nw) hj0.ne'
      _ <= xn hw1 j := xn_ge_a_pow hw1 j
    have nt : (↑(n ^ k) : Int) < 2 * xn hw1 j * n - n * n - 1 :=
      eq_pow_of_pell_lem hn0.ne' hk0.ne' hnka
    have na : n <= xn hw1 j := (Nat.le_self_pow hk0.ne' _).trans hnka.le
    have te : (t : Int) = 2 * xn hw1 j * n - n * n - 1 := by
      rw [sub_sub]; rw [eq_sub_iff_add_eq]
      exact mod_cast ta.symm
    have : xn a1 k ≡ yn a1 k * (xn hw1 j - n) + n ^ k [MOD t] := by
      apply modEq_of_dvd
      rw [te]; rw [Nat.cast_add]; rw [Nat.cast_mul]; rw [Int.ofNat_sub na]
      exact x_sub_y_dvd_pow a1 n k
    have : n ^ k % t = m % t := (this.symm.trans tm).add_left_cancel' _
    rw [← te] at nt
    rwa [Nat.mod_eq_of_lt (Nat.cast_lt.1 nt), Nat.mod_eq_of_lt mt] at this

end Pell
