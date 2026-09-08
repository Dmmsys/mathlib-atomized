/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.NormNum.DivMod

/-!
# `norm_num` extensions for `Nat.ModEq` and `Int.ModEq`

In this file we define `norm_num` extensions for `a ≡ b [MOD n]` and `a ≡ b [ZMOD n]`.
-/

public meta section

namespace Mathlib.Meta.NormNum

open Qq

/-- `norm_num` extension for `Nat.ModEq`. -/
@[norm_num _ ≡ _ [MOD _]]
/-
**Mathlib.Meta.NormNum.evalNatModEq** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：evalNatModEq : NormNumExt where eval {u αP} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`norm_num` extension for `Nat.ModEq`.
-/
def evalNatModEq : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q($a ≡ $b [MOD $n]) =>
    let ⟨b, pb⟩ ← deriveBoolOfIff _ e q(Nat.modEq_iff_dvd.symm)
    return .ofBoolResult pb
  | _, _, _ => failure

/-- `norm_num` extension for `Int.ModEq`. -/
@[norm_num _ ≡ _ [ZMOD _]]
/-
**Mathlib.Meta.NormNum.evalIntModEq** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：evalIntModEq : NormNumExt where eval {u αP} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`norm_num` extension for `Int.ModEq`.
-/
def evalIntModEq : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q($a ≡ $b [ZMOD $n]) =>
    let ⟨b, pb⟩ ← deriveBoolOfIff _ e q(Int.modEq_iff_dvd.symm)
    return .ofBoolResult pb
  | _, _, _ => failure

end Mathlib.Meta.NormNum

