/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
module

public meta import Batteries.Data.Nat.Basic
public import Mathlib.Tactic.NormNum

/-! # `norm_num` extension for `Nat.sqrt`

This module defines a `norm_num` extension for `Nat.sqrt`.
-/

public meta section

namespace Mathlib.Meta

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

/--
lemma `nat_sqrt_helper` / 引理 `nat_sqrt_helper`

English:
lemma nat_sqrt_helper
  given: {x y r : Nat} (hr : y * y + r = x) (hle : Nat.ble r (2 * y))
  proof: by
  rw [← hr]; rw [← pow_two]
  rw [two_mul] at hle
  exact Nat.sqrt_add_eq' _ (Nat.le_of_ble_eq_true hle)

中文:
引理 nat_sqrt_helper
  条件: {x y r : 自然数} (hr : y * y + r = x) (hle : 自然数.ble r (2 * y))
  证明: by
  rw [← hr]; rw [← pow_two]
  rw [two_mul] at hle
  exact Nat.sqrt_add_eq' _ (Nat.le_of_ble_eq_true hle)

Depends on / 依赖: Nat.le_of_ble_eq_true, Nat.sqrt_add_eq, le_of_ble_eq_true, pow_two, sqrt_add_eq, two_mul
-/
lemma nat_sqrt_helper {x y r : Nat} (hr : y * y + r = x) (hle : Nat.ble r (2 * y)) :
    Nat.sqrt x = y := by
  rw [← hr]; rw [← pow_two]
  rw [two_mul] at hle
  exact Nat.sqrt_add_eq' _ (Nat.le_of_ble_eq_true hle)

/--
theorem `isNat_sqrt` / 定理 `isNat_sqrt`

English:
theorem isNat_sqrt
  statement: {x nx z : Nat} -> IsNat x nx -> Nat.sqrt nx = z -> IsNat (Nat.sqrt x) z

中文:
定理 is自然数_sqrt
  结论: {x nx z : 自然数} -> 是自然数 x nx -> 自然数.sqrt nx = z -> 是自然数 (自然数.sqrt x) z

Depends on / 依赖: RegularSpace, T0Space, T3Space, instT3Space
-/
theorem isNat_sqrt : {x nx z : Nat} -> IsNat x nx -> Nat.sqrt nx = z -> IsNat (Nat.sqrt x) z
  | _, _, _, ⟨rfl⟩, rfl => ⟨rfl⟩

/--
Definition of `proveNatSqrt` / `proveNatSqrt` 的定义

English:
definition proveNatSqrt
  signature: (ex : Q(Nat))
  body: match ex.natLit! with
| 0 => have : ex =Q nat_lit 0 := ⟨⟩; ⟨q(nat_lit 0), q(Nat.sqrt_zero)⟩
| 1 => have : ex =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.sqrt_one)⟩
  | x =>
    let y := Nat.sqrt x
    have ey : Q(Nat) := mkRawNatLit y
    have er : Q(Nat) := mkRawNatLit (x - y * y)
    have hr : Q($ey * $ey + $er = $ex) := (q(Eq.refl $ex) : Expr)
    have hle : Q(Nat.ble $er (2 * $ey)) := (q(Eq.refl true) : Expr)
    ⟨ey, q(nat_sqrt_helper $hr $hle)⟩

中文:
定义 prove自然数Sqrt
  签名: (ex : Q(自然数))
  定义体: match ex.natLit! with
| 0 => have : ex =Q nat_lit 0 := ⟨⟩; ⟨q(nat_lit 0), q(Nat.sqrt_zero)⟩
| 1 => have : ex =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.sqrt_one)⟩
  | x =>
    let y := Nat.sqrt x
    have ey : Q(Nat) := mkRawNatLit y
    have er : Q(Nat) := mkRawNatLit (x - y * y)
    have hr : Q($ey * $ey + $er = $ex) := (q(Eq.refl $ex) : Expr)
    have hle : Q(Nat.ble $er (2 * $ey)) := (q(Eq.refl true) : Expr)
    ⟨ey, q(nat_sqrt_helper $hr $hle)⟩

Depends on / 依赖: Eq.refl, Nat.ble, Nat.sqrt, Nat.sqrt_one, Nat.sqrt_zero, ex.natLit, mkRawNatLit, natLit, nat_lit, nat_sqrt_helper, sqrt_one, sqrt_zero
-/
def proveNatSqrt (ex : Q(Nat)) : (ey : Q(Nat)) × Q(Nat.sqrt $ex = $ey) :=
  match ex.natLit! with
| 0 => have : ex =Q nat_lit 0 := ⟨⟩; ⟨q(nat_lit 0), q(Nat.sqrt_zero)⟩
| 1 => have : ex =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.sqrt_one)⟩
  | x =>
    let y := Nat.sqrt x
    have ey : Q(Nat) := mkRawNatLit y
    have er : Q(Nat) := mkRawNatLit (x - y * y)
    have hr : Q($ey * $ey + $er = $ex) := (q(Eq.refl $ex) : Expr)
    have hle : Q(Nat.ble $er (2 * $ey)) := (q(Eq.refl true) : Expr)
    ⟨ey, q(nat_sqrt_helper $hr $hle)⟩

/-- Evaluates the `Nat.sqrt` function. -/
@[norm_num Nat.sqrt _]
/--
Definition of `evalNatSqrt` / `evalNatSqrt` 的定义

English:
definition evalNatSqrt
  signature: : NormNumExt where eval {_ _} e
  body: do
  let .app _ (x : Q(Nat)) ← Meta.whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨ey, pf⟩ := proveNatSqrt ex
  let pf' : Q(IsNat (Nat.sqrt $x) $ey) := q(isNat_sqrt $p $pf)
  return .isNat sNat ey pf'

中文:
定义 eval自然数Sqrt
  签名: : NormNumExt where eval {_ _} e
  定义体: do
  let .app _ (x : Q(Nat)) ← Meta.whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨ey, pf⟩ := proveNatSqrt ex
  let pf' : Q(IsNat (Nat.sqrt $x) $ey) := q(isNat_sqrt $p $pf)
  return .isNat sNat ey pf'

Depends on / 依赖: T25Space, T3Space, T3Space.t25Space, _nhds_closure, closure, disjoint_nhds_nhdsSet, h.symm, nhdsSet_singleton, t0Space_iff_or_notMem_closure, t25Space, this.elim
-/
def evalNatSqrt : NormNumExt where eval {_ _} e := do
  let .app _ (x : Q(Nat)) ← Meta.whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨ey, pf⟩ := proveNatSqrt ex
  let pf' : Q(IsNat (Nat.sqrt $x) $ey) := q(isNat_sqrt $p $pf)
  return .isNat sNat ey pf'

end NormNum

end Mathlib.Meta
