/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

meta import Batteries.Data.Float.Rat -- shake: keep (for `#eval` sanity check)
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Positivity

/-!
# Chudnovsky's formula for π

This file defines the infinite sum in Chudnovsky's formula for computing `π⁻¹`.
It does not (yet!) contain a proof; anyone is welcome to adopt this problem,
but at present we are a long way off.

## Main definitions

* `chudnovskySum`: The infinite sum in Chudnovsky's formula

## Future work

* Use this formula to give approximations for `π`.
* Prove the sum equals `π⁻¹`, as stated using `proof_wanted` below.
* Show that each imaginary quadratic field of class number 1 (corresponding to Heegner numbers)
  gives a Ramanujan type formula, and that this is the formula coming from 163,
  with `j ((1 + √-163) / 2) = -640320^3`, and the other magic constants coming from
  Eisenstein series.

## References
* [Milla, *A detailed proof of the Chudnovsky formula*][Milla_2018]
* [Chen and Glebov, *On Chudnovsky--Ramanujan type formulae*][Chen_Glebov_2018]

-/

@[expose] public section

open scoped Real
open Nat

/--
Definition of `chudnovskyNum` / `chudnovskyNum` 的定义

English:
definition chudnovskyNum
  signature: (n : Nat)
  body: (-1 : Int) ^ n * (6 * n)! * (545140134 * n + 13591409)

中文:
定义 chudnovskyNum
  签名: (n : 自然数)
  定义体: (-1 : Int) ^ n * (6 * n)! * (545140134 * n + 13591409)
-/
def chudnovskyNum (n : Nat) : Int :=
  (-1 : Int) ^ n * (6 * n)! * (545140134 * n + 13591409)

/--
Definition of `chudnovskyDenom` / `chudnovskyDenom` 的定义

English:
definition chudnovskyDenom
  signature: (n : Nat)
  body: (3 * n)! * (n)! ^ 3 * 640320 ^ (3 * n)

中文:
定义 chudnovskyDenom
  签名: (n : 自然数)
  定义体: (3 * n)! * (n)! ^ 3 * 640320 ^ (3 * n)
-/
def chudnovskyDenom (n : Nat) : Nat :=
  (3 * n)! * (n)! ^ 3 * 640320 ^ (3 * n)

/--
Definition of `chudnovskyTerm` / `chudnovskyTerm` 的定义

English:
definition chudnovskyTerm
  signature: (n : Nat)
  body: chudnovskyNum n / chudnovskyDenom n

中文:
定义 chudnovskyTerm
  签名: (n : 自然数)
  定义体: chudnovskyNum n / chudnovskyDenom n

Depends on / 依赖: chudnovskyDenom, chudnovskyNum
-/
def chudnovskyTerm (n : Nat) : Rat :=
  chudnovskyNum n / chudnovskyDenom n

-- Sanity check that when calculated in `Float` we get the right answer:
/-- info: 3.141593 -/
#guard_msgs in
#eval 1 / (12 / (640320 : Float) ^ (3 / 2) *
  (List.ofFn fun n : Fin 37 => (chudnovskyTerm n).toFloat).sum)

/--
Definition of `chudnovskySum` / `chudnovskySum` 的定义

English:
definition chudnovskySum
  signature: : Real
  body: 12 / (640320 : Real) ^ (3 / 2 : Real) * ∑' n : Nat, (chudnovskyTerm n : Real)

中文:
定义 chudnovskySum
  签名: : 实数
  定义体: 12 / (640320 : Real) ^ (3 / 2 : Real) * ∑' n : Nat, (chudnovskyTerm n : Real)

Depends on / 依赖: chudnovskyTerm
-/
noncomputable def chudnovskySum : Real :=
  12 / (640320 : Real) ^ (3 / 2 : Real) * ∑' n : Nat, (chudnovskyTerm n : Real)

/-- **Chudnovsky's formula**: The sum equals `π⁻¹` -/
proof_wanted chudnovskySum_eq_pi_inv : chudnovskySum = π⁻¹
