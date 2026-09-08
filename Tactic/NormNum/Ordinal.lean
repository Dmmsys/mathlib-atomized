/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public meta import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.SetTheory.Ordinal.Exponential
public import Mathlib.Tactic.NormNum.Basic

/-!
# `norm_num` extensions for Ordinals

The default `norm_num` extensions for many operators requires a semiring,
which without a right distributive law, ordinals do not have.

We must therefore define new extensions for them.
-/

public meta section

namespace Mathlib.Meta.NormNum
open Lean Lean.Meta Qq Ordinal

/- The `guard_msgs` in this file are for checking whether the current default extensions have been
updated and the extensions in this file are no longer needed. -/

/-- info: 12 * 5 -/
#guard_msgs in
#norm_num (12 : Ordinal.{0}) * (5 : Ordinal.{0})

/-
**Mathlib.Meta.NormNum.isNat_ordinalMul.** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta
.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isNat_ordinalMul.{u} : ∀ {a b : Ordinal.{u}} {an bn rn : ℕ},
    IsNat a an → IsNat b bn → an * bn = rn → IsNat (a * b) rn
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm <| natCast_mul ..⟩

/-- The `norm_num` extension for multiplication on ordinals. -/
@[norm_num (_ : Ordinal) * (_ : Ordinal)]
/-
**Mathlib.Meta.NormNum.evalOrdinalMul** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：evalOrdinalMul : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension for multiplication on ordinals.
-/
def evalOrdinalMul : NormNumExt where
  eval {u α} e := do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) * ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      have rn : Q(ℕ) := mkRawNatLit (an.natLit! * bn.natLit!)
      have : ($an * $bn) =Q $rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalMul $pa $pb (.refl $rn)))
    | _, _ => throwError "not multiplication on ordinals"

/-- info: 5 ≤ 12 -/
#guard_msgs in
#norm_num (5 : Ordinal.{0}) ≤ 12

/-- info: 5 < 12 -/
#guard_msgs in
#norm_num (5 : Ordinal.{0}) < 12

/-
**Mathlib.Meta.NormNum.isNat_ordinalLE_true.** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.
Meta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isNat_ordinalLE_true.{u} : ∀ {a b : Ordinal.{u}} {an bn : ℕ},
    IsNat a an → IsNat b bn → decide (an ≤ bn) = true → a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Nat.cast_le.mpr <| of_decide_eq_true h
/-
**Mathlib.Meta.NormNum.isNat_ordinalLE_false.** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib
.Meta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isNat_ordinalLE_false.{u} : ∀ {a b : Ordinal.{u}} {an bn : ℕ},
    IsNat a an → IsNat b bn → decide (an ≤ bn) = false → ¬a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => not_iff_not.mpr Nat.cast_le |>.mpr <| of_decide_eq_false h
/-
**Mathlib.Meta.NormNum.isNat_ordinalLT_true.** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.
Meta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isNat_ordinalLT_true.{u} : ∀ {a b : Ordinal.{u}} {an bn : ℕ},
    IsNat a an → IsNat b bn → decide (an < bn) = true → a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Nat.cast_lt.mpr <| of_decide_eq_true h
/-
**Mathlib.Meta.NormNum.isNat_ordinalLT_false.** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib
.Meta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isNat_ordinalLT_false.{u} : ∀ {a b : Ordinal.{u}} {an bn : ℕ},
    IsNat a an → IsNat b bn → decide (an < bn) = false → ¬a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => not_iff_not.mpr Nat.cast_lt |>.mpr <| of_decide_eq_false h

/-- The `norm_num` extension for inequality on ordinals. -/
@[norm_num (_ : Ordinal) ≤ (_ : Ordinal)]
/-
**Mathlib.Meta.NormNum.evalOrdinalLE** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：evalOrdinalLE : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension for inequality on ordinals.
-/
def evalOrdinalLE : NormNumExt where
  eval {u α} e := do
    let ⟨_⟩ ← assertLevelDefEqQ u ql(0)
    match α, e with
    | ~q(Prop), ~q(($a : Ordinal) ≤ ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u_1}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      if an.natLit! ≤ bn.natLit! then
        have : decide ($an ≤ $bn) =Q true := ⟨⟩
        pure (.isTrue q(isNat_ordinalLE_true $pa $pb $this))
      else
        have : decide ($an ≤ $bn) =Q false := ⟨⟩
        pure (.isFalse q(isNat_ordinalLE_false $pa $pb $this))
    | _, _ => throwError "not inequality on ordinals"

/-- The `norm_num` extension for strict inequality on ordinals. -/
@[norm_num (_ : Ordinal) < (_ : Ordinal)]
/-
**Mathlib.Meta.NormNum.evalOrdinalLT** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：evalOrdinalLT : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension for strict inequality on ordinals.
-/
def evalOrdinalLT : NormNumExt where
  eval {u α} e := do
    let ⟨_⟩ ← assertLevelDefEqQ u ql(0)
    match α, e with
    | ~q(Prop), ~q(($a : Ordinal) < ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u_1}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      if an.natLit! < bn.natLit! then
        have : decide ($an < $bn) =Q true := ⟨⟩
        pure (.isTrue q(isNat_ordinalLT_true $pa $pb $this))
      else
        have : decide ($an < $bn) =Q false := ⟨⟩
        pure (.isFalse q(isNat_ordinalLT_false $pa $pb $this))
    | _, _ => throwError "not strict inequality on ordinals"

/-- info: 12 - 5 -/
#guard_msgs in
#norm_num (12 : Ordinal.{0}) - 5

/-
**Mathlib.Meta.NormNum.isNat_ordinalSub.** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta
.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isNat_ordinalSub.{u} : ∀ {a b : Ordinal.{u}} {an bn rn : ℕ},
    IsNat a an → IsNat b bn → an - bn = rn → IsNat (a - b) rn
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm <| natCast_sub ..⟩

/-- The `norm_num` extension for subtraction on ordinals. -/
@[norm_num (_ : Ordinal) - (_ : Ordinal)]
/-
**Mathlib.Meta.NormNum.evalOrdinalSub** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：evalOrdinalSub : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension for subtraction on ordinals.
-/
def evalOrdinalSub : NormNumExt where
  eval {u α} e := do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) - ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      have rn : Q(ℕ) := mkRawNatLit (an.natLit! - bn.natLit!)
      have : ($an - $bn) =Q $rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalSub $pa $pb (.refl $rn)))
    | _, _ => throwError "not subtration on ordinals"

/-- info: 12 / 5 -/
#guard_msgs in
#norm_num (12 : Ordinal.{0}) / 5

/-
**Mathlib.Meta.NormNum.isNat_ordinalDiv.** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta
.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isNat_ordinalDiv.{u} : ∀ {a b : Ordinal.{u}} {an bn rn : ℕ},
    IsNat a an → IsNat b bn → an / bn = rn → IsNat (a / b) rn
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm <| natCast_div ..⟩

/-- The `norm_num` extension for division on ordinals. -/
@[norm_num (_ : Ordinal) / (_ : Ordinal)]
/-
**Mathlib.Meta.NormNum.evalOrdinalDiv** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：evalOrdinalDiv : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension for division on ordinals.
-/
def evalOrdinalDiv : NormNumExt where
  eval {u α} e := do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) / ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      have rn : Q(ℕ) := mkRawNatLit (an.natLit! / bn.natLit!)
      have : ($an / $bn) =Q $rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalDiv $pa $pb (.refl $rn)))
    | _, _ => throwError "not division on ordinals"

/-- info: 12 % 5 -/
#guard_msgs in
#norm_num (12 : Ordinal.{0}) % 5

/-
**Mathlib.Meta.NormNum.isNat_ordinalMod.** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta
.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isNat_ordinalMod.{u} : ∀ {a b : Ordinal.{u}} {an bn rn : ℕ},
    IsNat a an → IsNat b bn → an % bn = rn → IsNat (a % b) rn
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm <| natCast_mod ..⟩

/-- The `norm_num` extension for modulo on ordinals. -/
@[norm_num (_ : Ordinal) % (_ : Ordinal)]
/-
**Mathlib.Meta.NormNum.evalOrdinalMod** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：evalOrdinalMod : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension for modulo on ordinals.
-/
def evalOrdinalMod : NormNumExt where
  eval {u α} e := do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) % ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      have rn : Q(ℕ) := mkRawNatLit (an.natLit! % bn.natLit!)
      have : ($an % $bn) =Q $rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalMod $pa $pb (.refl $rn)))
    | _, _ => throwError "not modulo on ordinals"
/-
**Mathlib.Meta.NormNum.isNat_ordinalOPow.** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Met
a.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isNat_ordinalOPow.{u} : ∀ {a b : Ordinal.{u}} {an bn rn : ℕ},
    IsNat a an → IsNat b bn → an ^ bn = rn → IsNat (a ^ b) rn
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(opow_natCast ..).trans (natCast_pow ..).symm⟩

/-- The `norm_num` extension for homogeneous power on ordinals. -/
@[norm_num (_ : Ordinal) ^ (_ : Ordinal)]
/-
**Mathlib.Meta.NormNum.evalOrdinalOPow** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：evalOrdinalOPow : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension for homogeneous power on ordinals.
-/
def evalOrdinalOPow : NormNumExt where
  eval {u α} e := do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) ^ ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      have rn : Q(ℕ) := mkRawNatLit (an.natLit! ^ bn.natLit!)
      have : ($an ^ $bn) =Q $rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalOPow $pa $pb (.refl $rn)))
    | _, _ => throwError "not homogeneous power on ordinals"

/-- info: 12 ^ 2 -/
#guard_msgs in
#norm_num (12 : Ordinal.{0}) ^ (2 : ℕ)

/-
**Mathlib.Meta.NormNum.isNat_ordinalNPow.** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Met
a.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isNat_ordinalNPow.{u} : ∀ {a : Ordinal.{u}} {b an bn rn : ℕ},
    IsNat a an → IsNat b bn → an ^ bn = rn → IsNat (a ^ b) rn
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm <| natCast_pow ..⟩

/-- The `norm_num` extension for natural power on ordinals. -/
@[norm_num (_ : Ordinal) ^ (_ : ℕ)]
/-
**Mathlib.Meta.NormNum.evalOrdinalNPow** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：evalOrdinalNPow : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension for natural power on ordinals.
-/
def evalOrdinalNPow : NormNumExt where
  eval {u α} e := do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) ^ ($b : ℕ)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b q(inferInstance)
      have rn : Q(ℕ) := mkRawNatLit (an.natLit! ^ bn.natLit!)
      have : ($an ^ $bn) =Q $rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalNPow $pa $pb (.refl $rn)))
    | _, _ => throwError "not natural power on ordinals"

end Mathlib.Meta.NormNum

