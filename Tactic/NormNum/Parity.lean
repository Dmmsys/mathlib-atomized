/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Ring.Int.Parity  -- shake: keep (Qq dependency)
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
/-
**Mathlib.Meta.NormNum.evalEven** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`
。
形式化陈述：evalEven : NormNumExt where eval {u αP} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`norm_num` extension for `Even`.

Works for `ℕ` and `ℤ`.
-/
def evalEven : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@Even ℕ _ $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 0) q(Even $a) q((@Nat.even_iff $a).symm)
    return .ofBoolResult r
  | 0, ~q(Prop), ~q(@Even ℤ _ $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 0) q(Even $a) q((@Int.even_iff $a).symm)
    return .ofBoolResult r
  | _, _, _ => failure

/-- `norm_num` extension for `Odd`.

Works for `ℕ` and `ℤ`. -/
@[norm_num Odd _]
/-
**Mathlib.Meta.NormNum.evalOdd** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：evalOdd : NormNumExt where eval {u αP} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`norm_num` extension for `Odd`.

Works for `ℕ` and `ℤ`.
-/
def evalOdd : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@Odd ℕ $inst $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 1) q(Odd $a) q((@Nat.odd_iff $a).symm)
    return .ofBoolResult r
  | 0, ~q(Prop), ~q(@Odd ℤ $inst $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 1) q(Odd $a) q((@Int.odd_iff $a).symm)
    return .ofBoolResult r
  | _ => failure

end Mathlib.Meta.NormNum

