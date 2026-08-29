/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Ring.Int.Parity -- shake: keep (Qq dependency)
public import Mathlib.Tactic.NormNum.Core

/-!
# `norm_num` extensions for `Even` and `Odd`

In this file we provide `norm_num` extensions for `Even n` and `Odd n`,
where `n : ℕ` or `n : ℤ`.
-/

public meta section

namespace Mathlib.Meta.NormNum

open Qq

/-- `norm_num` extension for `Even`.

Works for `ℕ` and `ℤ`. -/
@[norm_num Even _]
/--
Definition of `evalEven` / `evalEven` 的定义

English:
definition evalEven
  signature: : NormNumExt where eval {u αP} e
  body: do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@Even Nat _ $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 0) q(Even $a) q((@Nat.even_iff $a).symm)
    return .ofBoolResult r
  | 0, ~q(Prop), ~q(@Even Int _ $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIf

中文:
定义 evalEven
  签名: : NormNumExt where eval {u αP} e
  定义体: do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@Even Nat _ $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 0) q(Even $a) q((@Nat.even_iff $a).symm)
    return .ofBoolResult r
  | 0, ~q(Prop), ~q(@Even Int _ $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIf

Depends on / 依赖: CompletelyNormalSpace, CompletelyNormalSpace.toNormalSpace, toNormalSpace
-/
def evalEven : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@Even Nat _ $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 0) q(Even $a) q((@Nat.even_iff $a).symm)
    return .ofBoolResult r
  | 0, ~q(Prop), ~q(@Even Int _ $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 0) q(Even $a) q((@Int.even_iff $a).symm)
    return .ofBoolResult r
  | _, _, _ => failure

/-- `norm_num` extension for `Odd`.

Works for `ℕ` and `ℤ`. -/
@[norm_num Odd _]
/--
Definition of `evalOdd` / `evalOdd` 的定义

English:
definition evalOdd
  signature: : NormNumExt where eval {u αP} e
  body: do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@Odd Nat $inst $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 1) q(Odd $a) q((@Nat.odd_iff $a).symm)
    return .ofBoolResult r
  | 0, ~q(Prop), ~q(@Odd Int $inst $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBool

中文:
定义 evalOdd
  签名: : NormNumExt where eval {u αP} e
  定义体: do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@Odd Nat $inst $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 1) q(Odd $a) q((@Nat.odd_iff $a).symm)
    return .ofBoolResult r
  | 0, ~q(Prop), ~q(@Odd Int $inst $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBool
-/
def evalOdd : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@Odd Nat $inst $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 1) q(Odd $a) q((@Nat.odd_iff $a).symm)
    return .ofBoolResult r
  | 0, ~q(Prop), ~q(@Odd Int $inst $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 1) q(Odd $a) q((@Int.odd_iff $a).symm)
    return .ofBoolResult r
  | _ => failure

end Mathlib.Meta.NormNum
