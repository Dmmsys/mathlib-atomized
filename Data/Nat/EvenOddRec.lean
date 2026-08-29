/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.BinaryRec

/-! # A recursion principle based on even and odd numbers. -/

@[expose] public section

namespace Nat

/-- Recursion principle on even and odd numbers: if we have `P 0`, and for all `i : ℕ` we can
extend from `P i` to both `P (2 * i)` and `P (2 * i + 1)`, then we have `P n` for all `n : ℕ`.
This is nothing more than a wrapper around `Nat.binaryRec`, to avoid having to switch to
dealing with `bit0` and `bit1`. -/
@[elab_as_elim]
/--
Definition of `evenOddRec` / `evenOddRec` 的定义

English:
definition evenOddRec
  signature: {P : Nat -> Sort*} (h0 : P 0) (h_even : forall n, P n -> P (2 * n))
  body: binaryRec h0 (fun
    | false, i, hi => (h_even i hi : P (2 * i))
    | true, i, hi => (h_odd i hi : P (2 * i + 1))) n

@[simp]

中文:
定义 evenOddRec
  签名: {P : 自然数 -> Sort*} (h0 : P 0) (h_even : 对任意 n, P n -> P (2 * n))
  定义体: binaryRec h0 (fun
    | false, i, hi => (h_even i hi : P (2 * i))
    | true, i, hi => (h_odd i hi : P (2 * i + 1))) n

@[simp]

Depends on / 依赖: binaryRec, h_even, h_odd
-/
def evenOddRec {P : Nat -> Sort*} (h0 : P 0) (h_even : forall n, P n -> P (2 * n))
    (h_odd : forall n, P n -> P (2 * n + 1)) (n : Nat) : P n :=
  binaryRec h0 (fun
    | false, i, hi => (h_even i hi : P (2 * i))
    | true, i, hi => (h_odd i hi : P (2 * i + 1))) n

@[simp]
/--
theorem `evenOddRec_zero` / 定理 `evenOddRec_zero`

English:
theorem evenOddRec_zero
  statement: {P : Nat -> Sort*} (h0 : P 0) (h_even : forall i, P i -> P (2 * i))
  proof: binaryRec_zero _ _

@[simp]

中文:
定理 evenOddRec_zero
  结论: {P : 自然数 -> Sort*} (h0 : P 0) (h_even : 对任意 i, P i -> P (2 * i))
  证明: binaryRec_zero _ _

@[simp]

Depends on / 依赖: binaryRec_zero
-/
theorem evenOddRec_zero {P : Nat -> Sort*} (h0 : P 0) (h_even : forall i, P i -> P (2 * i))
    (h_odd : forall i, P i -> P (2 * i + 1)) : evenOddRec h0 h_even h_odd 0 = h0 :=
  binaryRec_zero _ _

@[simp]
/--
theorem `evenOddRec_even` / 定理 `evenOddRec_even`

English:
theorem evenOddRec_even
  statement: {P : Nat -> Sort*} (h0 : P 0) (h_even : forall i, P i -> P (2 * i))
  proof: by
  apply binaryRec_eq false n
  simp [H]

@[simp]

中文:
定理 evenOddRec_even
  结论: {P : 自然数 -> Sort*} (h0 : P 0) (h_even : 对任意 i, P i -> P (2 * i))
  证明: by
  apply binaryRec_eq false n
  simp [H]

@[simp]

Depends on / 依赖: binaryRec_eq
-/
theorem evenOddRec_even {P : Nat -> Sort*} (h0 : P 0) (h_even : forall i, P i -> P (2 * i))
    (h_odd : forall i, P i -> P (2 * i + 1)) (H : h_even 0 h0 = h0) (n : Nat) :
    (2 * n).evenOddRec h0 h_even h_odd = h_even n (evenOddRec h0 h_even h_odd n) := by
  apply binaryRec_eq false n
  simp [H]

@[simp]
/--
theorem `evenOddRec_odd` / 定理 `evenOddRec_odd`

English:
theorem evenOddRec_odd
  statement: {P : Nat -> Sort*} (h0 : P 0) (h_even : forall i, P i -> P (2 * i))
  proof: by
  apply binaryRec_eq true n
  simp [H]

中文:
定理 evenOddRec_odd
  结论: {P : 自然数 -> Sort*} (h0 : P 0) (h_even : 对任意 i, P i -> P (2 * i))
  证明: by
  apply binaryRec_eq true n
  simp [H]

Depends on / 依赖: binaryRec_eq
-/
theorem evenOddRec_odd {P : Nat -> Sort*} (h0 : P 0) (h_even : forall i, P i -> P (2 * i))
    (h_odd : forall i, P i -> P (2 * i + 1)) (H : h_even 0 h0 = h0) (n : Nat) :
    (2 * n + 1).evenOddRec h0 h_even h_odd = h_odd n (evenOddRec h0 h_even h_odd n) := by
  apply binaryRec_eq true n
  simp [H]

/-- Strong recursion principle on even and odd numbers: if for all `i : ℕ` we can prove `P (2 * i)`
from `P j` for all `j < 2 * i` and we can prove `P (2 * i + 1)` from `P j` for all `j < 2 * i + 1`,
then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
/--
Definition of `evenOddStrongRec` / `evenOddStrongRec` 的定义

English:
definition evenOddStrongRec
  signature: {P : Nat -> Sort*}
  body: n.strongRecOn fun m ih => m.even_or_odd'.choose_spec.by_cases
    (fun h => h.symm ▸ h_even m.even_or_odd'.choose <| h ▸ ih)
    (fun h => h.symm ▸ h_odd m.even_or_odd'.choose <| h ▸ ih)

中文:
定义 evenOddStrongRec
  签名: {P : 自然数 -> Sort*}
  定义体: n.strongRecOn fun m ih => m.even_or_odd'.choose_spec.by_cases
    (fun h => h.symm ▸ h_even m.even_or_odd'.choose <| h ▸ ih)
    (fun h => h.symm ▸ h_odd m.even_or_odd'.choose <| h ▸ ih)

Depends on / 依赖: choose_spec, choose_spec.by_cases, even_or_odd, h.symm, h_even, h_odd, m.even_or_odd, n.strongRecOn, strongRecOn
-/
noncomputable def evenOddStrongRec {P : Nat -> Sort*}
    (h_even : forall n : Nat, (forall k < 2 * n, P k) -> P (2 * n))
    (h_odd : forall n : Nat, (forall k < 2 * n + 1, P k) -> P (2 * n + 1)) (n : Nat) : P n :=
  n.strongRecOn fun m ih => m.even_or_odd'.choose_spec.by_cases
    (fun h => h.symm ▸ h_even m.even_or_odd'.choose <| h ▸ ih)
    (fun h => h.symm ▸ h_odd m.even_or_odd'.choose <| h ▸ ih)

end Nat
