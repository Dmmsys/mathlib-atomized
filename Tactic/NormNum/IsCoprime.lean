/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD

/-! # `norm_num` extension for `IsCoprime`

This module defines a `norm_num` extension for `IsCoprime` over `ℤ`.

(While `IsCoprime` is defined over `ℕ`, since it uses Bezout's identity with `ℕ` coefficients
it does not correspond to the usual notion of coprime.)
-/

public meta section

namespace Mathlib.Meta

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

/--
theorem `int_not_isCoprime_helper` / 定理 `int_not_isCoprime_helper`

English:
theorem int_not_isCoprime_helper
  statement: (x y : Int) (d : Nat) (hd : Int.gcd x y = d)
  proof: by
  rw [Int.isCoprime_iff_gcd_eq_one]; rw [hd]
  exact Nat.ne_of_beq_eq_false h

中文:
定理 int_not_isCoprime_helper
  结论: (x y : 整数) (d : 自然数) (hd : 整数.最大公约数 x y = d)
  证明: by
  rw [Int.isCoprime_iff_gcd_eq_one]; rw [hd]
  exact Nat.ne_of_beq_eq_false h

Depends on / 依赖: Int.isCoprime_iff_gcd_eq_one, Nat.ne_of_beq_eq_false, isCoprime_iff_gcd_eq_one, ne_of_beq_eq_false
-/
theorem int_not_isCoprime_helper (x y : Int) (d : Nat) (hd : Int.gcd x y = d)
    (h : Nat.beq d 1 = false) : ¬ IsCoprime x y := by
  rw [Int.isCoprime_iff_gcd_eq_one]; rw [hd]
  exact Nat.ne_of_beq_eq_false h

/--
theorem `isInt_isCoprime` / 定理 `isInt_isCoprime`

English:
theorem isInt_isCoprime
  statement: {x y nx ny : Int} ->

中文:
定理 is整数_isCoprime
  结论: {x y nx ny : 整数} ->
-/
theorem isInt_isCoprime : {x y nx ny : Int} ->
    IsInt x nx -> IsInt y ny -> IsCoprime nx ny -> IsCoprime x y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h

/--
theorem `isInt_not_isCoprime` / 定理 `isInt_not_isCoprime`

English:
theorem isInt_not_isCoprime
  statement: {x y nx ny : Int} ->

中文:
定理 is整数_not_isCoprime
  结论: {x y nx ny : 整数} ->
-/
theorem isInt_not_isCoprime : {x y nx ny : Int} ->
    IsInt x nx -> IsInt y ny -> ¬ IsCoprime nx ny -> ¬ IsCoprime x y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h

/--
Definition of `proveIntIsCoprime` / `proveIntIsCoprime` 的定义

English:
definition proveIntIsCoprime
  signature: (ex ey : Q(Int))
  body: let ⟨ed, pf⟩ := proveIntGCD ex ey
  if ed.natLit! = 1 then
    have pf' : Q(Int.gcd $ex $ey = 1) := pf
    Sum.inl q(Int.isCoprime_iff_gcd_eq_one.mpr $pf')
  else
    have h : Q(Nat.beq $ed 1 = false) := (q(Eq.refl false) : Expr)
    Sum.inr q(int_not_isCoprime_helper $ex $ey $ed $pf $h)

中文:
定义 prove整数IsCoprime
  签名: (ex ey : Q(整数))
  定义体: let ⟨ed, pf⟩ := proveIntGCD ex ey
  if ed.natLit! = 1 then
    have pf' : Q(Int.gcd $ex $ey = 1) := pf
    Sum.inl q(Int.isCoprime_iff_gcd_eq_one.mpr $pf')
  else
    have h : Q(Nat.beq $ed 1 = false) := (q(Eq.refl false) : Expr)
    Sum.inr q(int_not_isCoprime_helper $ex $ey $ed $pf $h)

Depends on / 依赖: Eq.refl, Int.gcd, Int.isCoprime_iff_gcd_eq_one.mpr, Nat.beq, Sum.inl, Sum.inr, ed.natLit, int_not_isCoprime_helper, isCoprime_iff_gcd_eq_one, natLit, proveIntGCD
-/
def proveIntIsCoprime (ex ey : Q(Int)) : Q(IsCoprime $ex $ey) oplus Q(¬ IsCoprime $ex $ey) :=
  let ⟨ed, pf⟩ := proveIntGCD ex ey
  if ed.natLit! = 1 then
    have pf' : Q(Int.gcd $ex $ey = 1) := pf
    Sum.inl q(Int.isCoprime_iff_gcd_eq_one.mpr $pf')
  else
    have h : Q(Nat.beq $ed 1 = false) := (q(Eq.refl false) : Expr)
    Sum.inr q(int_not_isCoprime_helper $ex $ey $ed $pf $h)

/-- Evaluates the `IsCoprime` predicate over `ℤ`. -/
@[norm_num IsCoprime (_ : Int) (_ : Int)]
/--
Definition of `evalIntIsCoprime` / `evalIntIsCoprime` 的定义

English:
definition evalIntIsCoprime
  signature: : NormNumExt where eval {_ _} e
  body: do
  let .app (.app _ (x : Q(Int))) (y : Q(Int)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
  match proveIntIsCoprime ex ey with
  | .inl pf =>
    have pf' : Q(IsCoprime $x $y) := q(isInt_isCoprime $p $q $pf)
    return .isTrue pf'
  | .inr pf =>
    have pf' : Q(¬ IsCoprime $x $y) := q(isInt_not_isCoprime $p $q $pf)
    return .isFalse pf'

中文:
定义 eval整数IsCoprime
  签名: : NormNumExt where eval {_ _} e
  定义体: do
  let .app (.app _ (x : Q(Int))) (y : Q(Int)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
  match proveIntIsCoprime ex ey with
  | .inl pf =>
    have pf' : Q(IsCoprime $x $y) := q(isInt_isCoprime $p $q $pf)
    return .isTrue pf'
  | .inr pf =>
    have pf' : Q(¬ IsCoprime $x $y) := q(isInt_not_isCoprime $p $q $pf)
    return .isFalse pf'
-/
def evalIntIsCoprime : NormNumExt where eval {_ _} e := do
  let .app (.app _ (x : Q(Int))) (y : Q(Int)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
  match proveIntIsCoprime ex ey with
  | .inl pf =>
    have pf' : Q(IsCoprime $x $y) := q(isInt_isCoprime $p $q $pf)
    return .isTrue pf'
  | .inr pf =>
    have pf' : Q(¬ IsCoprime $x $y) := q(isInt_not_isCoprime $p $q $pf)
    return .isFalse pf'

end NormNum

end Mathlib.Meta
