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

/--
lemma `isNat_ordinalMul.` / 引理 `isNat_ordinalMul.`

English:
lemma isNat_ordinalMul.{u}
  statement: forall {a b : Ordinal.{u}} {an bn rn : Nat},

中文:
引理 isNat_ordinalMul.{u}
  结论: 对任意 {a b : Ordinal.{u}} {an bn rn : 自然数},
-/
lemma isNat_ordinalMul.{u} : forall {a b : Ordinal.{u}} {an bn rn : Nat},
    IsNat a an -> IsNat b bn -> an * bn = rn -> IsNat (a * b) rn
| _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm natCast_mul ..⟩

/-- The `norm_num` extension for multiplication on ordinals. -/
@[norm_num (_ : Ordinal) * (_ : Ordinal)]
/--
Definition of `evalOrdinalMul` / `evalOrdinalMul` 的定义

English:
definition evalOrdinalMul
  signature: : NormNumExt where
  body: do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) * ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← d

中文:
定义 evalOrdinalMul
  签名: : NormNumExt where
  定义体: do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) * ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← d
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
      have rn : Q(Nat) := mkRawNatLit (an.natLit! * bn.natLit!)
have : ($an * $bn) =Q rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalMul $pa $pb (.refl $rn)))
    | _, _ => throwError "not multiplication on ordinals"

/-- info: 5 ≤ 12 -/
#guard_msgs in
#norm_num (5 : Ordinal.{0}) <= 12

/-- info: 5 < 12 -/
#guard_msgs in
#norm_num (5 : Ordinal.{0}) < 12

/--
lemma `isNat_ordinalLE_true.` / 引理 `isNat_ordinalLE_true.`

English:
lemma isNat_ordinalLE_true.{u}
  statement: forall {a b : Ordinal.{u}} {an bn : Nat},

中文:
引理 isNat_ordinalLE_true.{u}
  结论: 对任意 {a b : Ordinal.{u}} {an bn : 自然数},
-/
lemma isNat_ordinalLE_true.{u} : forall {a b : Ordinal.{u}} {an bn : Nat},
    IsNat a an -> IsNat b bn -> decide (an <= bn) = true -> a <= b
| _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Nat.cast_le.mpr of_decide_eq_true h

/--
lemma `isNat_ordinalLE_false.` / 引理 `isNat_ordinalLE_false.`

English:
lemma isNat_ordinalLE_false.{u}
  statement: forall {a b : Ordinal.{u}} {an bn : Nat},

中文:
引理 isNat_ordinalLE_false.{u}
  结论: 对任意 {a b : Ordinal.{u}} {an bn : 自然数},
-/
lemma isNat_ordinalLE_false.{u} : forall {a b : Ordinal.{u}} {an bn : Nat},
    IsNat a an -> IsNat b bn -> decide (an <= bn) = false -> ¬a <= b
.mpr of_decide_eq_false h | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => not_iff_not.mpr Nat.cast_le

/--
lemma `isNat_ordinalLT_true.` / 引理 `isNat_ordinalLT_true.`

English:
lemma isNat_ordinalLT_true.{u}
  statement: forall {a b : Ordinal.{u}} {an bn : Nat},

中文:
引理 isNat_ordinalLT_true.{u}
  结论: 对任意 {a b : Ordinal.{u}} {an bn : 自然数},
-/
lemma isNat_ordinalLT_true.{u} : forall {a b : Ordinal.{u}} {an bn : Nat},
    IsNat a an -> IsNat b bn -> decide (an < bn) = true -> a < b
| _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Nat.cast_lt.mpr of_decide_eq_true h

/--
lemma `isNat_ordinalLT_false.` / 引理 `isNat_ordinalLT_false.`

English:
lemma isNat_ordinalLT_false.{u}
  statement: forall {a b : Ordinal.{u}} {an bn : Nat},

中文:
引理 isNat_ordinalLT_false.{u}
  结论: 对任意 {a b : Ordinal.{u}} {an bn : 自然数},
-/
lemma isNat_ordinalLT_false.{u} : forall {a b : Ordinal.{u}} {an bn : Nat},
    IsNat a an -> IsNat b bn -> decide (an < bn) = false -> ¬a < b
.mpr of_decide_eq_false h | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => not_iff_not.mpr Nat.cast_lt

/-- The `norm_num` extension for inequality on ordinals. -/
@[norm_num (_ : Ordinal) <= (_ : Ordinal)]
/--
Definition of `evalOrdinalLE` / `evalOrdinalLE` 的定义

English:
definition evalOrdinalLE
  signature: : NormNumExt where
  body: do
    let ⟨_⟩ ← assertLevelDefEqQ u ql(0)
    match α, e with
    | ~q(Prop), ~q(($a : Ordinal) <= ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u_1}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      if an.natLit! <= bn.natLit! then
    

中文:
定义 evalOrdinalLE
  签名: : NormNumExt where
  定义体: do
    let ⟨_⟩ ← assertLevelDefEqQ u ql(0)
    match α, e with
    | ~q(Prop), ~q(($a : Ordinal) <= ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u_1}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      if an.natLit! <= bn.natLit! then
    
-/
def evalOrdinalLE : NormNumExt where
  eval {u α} e := do
    let ⟨_⟩ ← assertLevelDefEqQ u ql(0)
    match α, e with
    | ~q(Prop), ~q(($a : Ordinal) <= ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u_1}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      if an.natLit! <= bn.natLit! then
        have : decide ($an <= $bn) =Q true := ⟨⟩
        pure (.isTrue q(isNat_ordinalLE_true $pa $pb $this))
      else
        have : decide ($an <= $bn) =Q false := ⟨⟩
        pure (.isFalse q(isNat_ordinalLE_false $pa $pb $this))
    | _, _ => throwError "not inequality on ordinals"

/-- The `norm_num` extension for strict inequality on ordinals. -/
@[norm_num (_ : Ordinal) < (_ : Ordinal)]
/--
Definition of `evalOrdinalLT` / `evalOrdinalLT` 的定义

English:
definition evalOrdinalLT
  signature: : NormNumExt where
  body: do
    let ⟨_⟩ ← assertLevelDefEqQ u ql(0)
    match α, e with
    | ~q(Prop), ~q(($a : Ordinal) < ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u_1}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      if an.natLit! < bn.natLit! then
      

中文:
定义 evalOrdinalLT
  签名: : NormNumExt where
  定义体: do
    let ⟨_⟩ ← assertLevelDefEqQ u ql(0)
    match α, e with
    | ~q(Prop), ~q(($a : Ordinal) < ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u_1}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b i
      if an.natLit! < bn.natLit! then
      
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

/--
lemma `isNat_ordinalSub.` / 引理 `isNat_ordinalSub.`

English:
lemma isNat_ordinalSub.{u}
  statement: forall {a b : Ordinal.{u}} {an bn rn : Nat},

中文:
引理 isNat_ordinalSub.{u}
  结论: 对任意 {a b : Ordinal.{u}} {an bn rn : 自然数},

Depends on / 依赖: And.right, _closure_eq_self, closed_nhdsSet_basis
-/
lemma isNat_ordinalSub.{u} : forall {a b : Ordinal.{u}} {an bn rn : Nat},
    IsNat a an -> IsNat b bn -> an - bn = rn -> IsNat (a - b) rn
| _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm natCast_sub ..⟩

/-- The `norm_num` extension for subtraction on ordinals. -/
@[norm_num (_ : Ordinal) - (_ : Ordinal)]
/--
Definition of `evalOrdinalSub` / `evalOrdinalSub` 的定义

English:
definition evalOrdinalSub
  signature: : NormNumExt where
  body: do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) - ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← d

中文:
定义 evalOrdinalSub
  签名: : NormNumExt where
  定义体: do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) - ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← d
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
      have rn : Q(Nat) := mkRawNatLit (an.natLit! - bn.natLit!)
have : ($an - $bn) =Q rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalSub $pa $pb (.refl $rn)))
    | _, _ => throwError "not subtration on ordinals"

/-- info: 12 / 5 -/
#guard_msgs in
#norm_num (12 : Ordinal.{0}) / 5

/--
lemma `isNat_ordinalDiv.` / 引理 `isNat_ordinalDiv.`

English:
lemma isNat_ordinalDiv.{u}
  statement: forall {a b : Ordinal.{u}} {an bn rn : Nat},

中文:
引理 isNat_ordinalDiv.{u}
  结论: 对任意 {a b : Ordinal.{u}} {an bn rn : 自然数},
-/
lemma isNat_ordinalDiv.{u} : forall {a b : Ordinal.{u}} {an bn rn : Nat},
    IsNat a an -> IsNat b bn -> an / bn = rn -> IsNat (a / b) rn
| _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm natCast_div ..⟩

/-- The `norm_num` extension for division on ordinals. -/
@[norm_num (_ : Ordinal) / (_ : Ordinal)]
/--
Definition of `evalOrdinalDiv` / `evalOrdinalDiv` 的定义

English:
definition evalOrdinalDiv
  signature: : NormNumExt where
  body: do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) / ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← d

中文:
定义 evalOrdinalDiv
  签名: : NormNumExt where
  定义体: do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) / ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← d

Depends on / 依赖: CompactSpace, NormalSpace, NormalSpace.of_compactSpace_r1Space, R1Space, of_compactSpace_r1Space
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
      have rn : Q(Nat) := mkRawNatLit (an.natLit! / bn.natLit!)
have : ($an / $bn) =Q rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalDiv $pa $pb (.refl $rn)))
    | _, _ => throwError "not division on ordinals"

/-- info: 12 % 5 -/
#guard_msgs in
#norm_num (12 : Ordinal.{0}) % 5

/--
lemma `isNat_ordinalMod.` / 引理 `isNat_ordinalMod.`

English:
lemma isNat_ordinalMod.{u}
  statement: forall {a b : Ordinal.{u}} {an bn rn : Nat},

中文:
引理 isNat_ordinalMod.{u}
  结论: 对任意 {a b : Ordinal.{u}} {an bn rn : 自然数},

Depends on / 依赖: NormalSpace, NormalSpace.of_regularSpace_lindelofSpace, of_regularSpace_lindelofSpace
-/
lemma isNat_ordinalMod.{u} : forall {a b : Ordinal.{u}} {an bn rn : Nat},
    IsNat a an -> IsNat b bn -> an % bn = rn -> IsNat (a % b) rn
| _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm natCast_mod ..⟩

/-- The `norm_num` extension for modulo on ordinals. -/
@[norm_num (_ : Ordinal) % (_ : Ordinal)]
/--
Definition of `evalOrdinalMod` / `evalOrdinalMod` 的定义

English:
definition evalOrdinalMod
  signature: : NormNumExt where
  body: do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) % ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← d

中文:
定义 evalOrdinalMod
  签名: : NormNumExt where
  定义体: do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) % ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← d

Depends on / 依赖: NormalSpace, NormalSpace.of_regularSpace_secondCountableTopology, of_regularSpace_secondCountableTopology
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
      have rn : Q(Nat) := mkRawNatLit (an.natLit! % bn.natLit!)
have : ($an % $bn) =Q rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalMod $pa $pb (.refl $rn)))
    | _, _ => throwError "not modulo on ordinals"

/--
lemma `isNat_ordinalOPow.` / 引理 `isNat_ordinalOPow.`

English:
lemma isNat_ordinalOPow.{u}
  statement: forall {a b : Ordinal.{u}} {an bn rn : Nat},

中文:
引理 isNat_ordinalOPow.{u}
  结论: 对任意 {a b : Ordinal.{u}} {an bn rn : 自然数},

Depends on / 依赖: NormalSpace, T1Space, T4Space
-/
lemma isNat_ordinalOPow.{u} : forall {a b : Ordinal.{u}} {an bn rn : Nat},
    IsNat a an -> IsNat b bn -> an ^ bn = rn -> IsNat (a ^ b) rn
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(opow_natCast ..).trans (natCast_pow ..).symm⟩

/-- The `norm_num` extension for homogeneous power on ordinals. -/
@[norm_num (_ : Ordinal) ^ (_ : Ordinal)]
/--
Definition of `evalOrdinalOPow` / `evalOrdinalOPow` 的定义

English:
definition evalOrdinalOPow
  signature: : NormNumExt where
  body: do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) ^ ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← d

中文:
定义 evalOrdinalOPow
  签名: : NormNumExt where
  定义体: do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) ^ ($b : Ordinal)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← d

Depends on / 依赖: T3Space, T4Space, T4Space.t3Space, t3Space
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
      have rn : Q(Nat) := mkRawNatLit (an.natLit! ^ bn.natLit!)
have : ($an ^ $bn) =Q rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalOPow $pa $pb (.refl $rn)))
    | _, _ => throwError "not homogeneous power on ordinals"

/-- info: 12 ^ 2 -/
#guard_msgs in
#norm_num (12 : Ordinal.{0}) ^ (2 : Nat)

/--
lemma `isNat_ordinalNPow.` / 引理 `isNat_ordinalNPow.`

English:
lemma isNat_ordinalNPow.{u}
  statement: forall {a : Ordinal.{u}} {b an bn rn : Nat},

中文:
引理 isNat_ordinalNPow.{u}
  结论: 对任意 {a : Ordinal.{u}} {b an bn rn : 自然数},
-/
lemma isNat_ordinalNPow.{u} : forall {a : Ordinal.{u}} {b an bn rn : Nat},
    IsNat a an -> IsNat b bn -> an ^ bn = rn -> IsNat (a ^ b) rn
| _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨Eq.symm natCast_pow ..⟩

/-- The `norm_num` extension for natural power on ordinals. -/
@[norm_num (_ : Ordinal) ^ (_ : Nat)]
/--
Definition of `evalOrdinalNPow` / `evalOrdinalNPow` 的定义

English:
definition evalOrdinalNPow
  signature: : NormNumExt where
  body: do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) ^ ($b : Nat)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriv

中文:
定义 evalOrdinalNPow
  签名: : NormNumExt where
  定义体: do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) ^ ($b : Nat)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriv
-/
def evalOrdinalNPow : NormNumExt where
  eval {u α} e := do
    let some u' := u.dec | throwError "level is not succ"
    haveI' : u =QL u' + 1 := ⟨⟩
    match α, e with
    | ~q(Ordinal.{u'}), ~q(($a : Ordinal) ^ ($b : Nat)) =>
      let i : Q(AddMonoidWithOne Ordinal.{u'}) := q(inferInstance)
      let ⟨an, pa⟩ ← deriveNat a i
      let ⟨bn, pb⟩ ← deriveNat b q(inferInstance)
      have rn : Q(Nat) := mkRawNatLit (an.natLit! ^ bn.natLit!)
have : ($an ^ $bn) =Q rn := ⟨⟩
      pure (.isNat i rn q(isNat_ordinalNPow $pa $pb (.refl $rn)))
    | _, _ => throwError "not natural power on ordinals"

end Mathlib.Meta.NormNum
