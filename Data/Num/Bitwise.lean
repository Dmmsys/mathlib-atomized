/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Num.Basic
public import Mathlib.Data.Vector.Basic

/-!
# Bitwise operations using binary representation of integers

## Definitions

* bitwise operations for `PosNum` and `Num`,
* `SNum`, a type that represents integers as a bit string with a sign bit at the end,
* arithmetic operations for `SNum`.
-/

@[expose] public section

open List (Vector)

namespace PosNum

/--
Definition of `lor` / `lor` 的定义

English:
definition lor
  signature: : PosNum -> PosNum -> PosNum

中文:
定义 lor
  签名: : PosNum -> PosNum -> PosNum
-/
def lor : PosNum -> PosNum -> PosNum
  | 1, bit0 q => bit1 q
  | 1, q => q
  | bit0 p, 1 => bit1 p
  | p, 1 => p
  | bit0 p, bit0 q => bit0 (lor p q)
  | bit0 p, bit1 q => bit1 (lor p q)
  | bit1 p, bit0 q => bit1 (lor p q)
  | bit1 p, bit1 q => bit1 (lor p q)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrOp PosNum
  body: PosNum.lor

中文:
实例 :
  签名: OrOp PosNum
  定义体: PosNum.lor

Depends on / 依赖: PosNum, PosNum.lor
-/
instance : OrOp PosNum where or := PosNum.lor

/--
lemma `lor_eq_or` / 引理 `lor_eq_or`

English:
lemma lor_eq_or
  given: (p q : PosNum)
  statement: p.lor q = p ||| q
  proof: rfl

中文:
引理 lor_eq_or
  条件: (p q : PosNum)
  结论: p.lor q = p ||| q
  证明: rfl
-/
@[simp] lemma lor_eq_or (p q : PosNum) : p.lor q = p ||| q := rfl

/--
Definition of `land` / `land` 的定义

English:
definition land
  signature: : PosNum -> PosNum -> Num

中文:
定义 land
  签名: : PosNum -> PosNum -> Num
-/
def land : PosNum -> PosNum -> Num
  | 1, bit0 _ => 0
  | 1, _ => 1
  | bit0 _, 1 => 0
  | _, 1 => 1
  | bit0 p, bit0 q => Num.bit0 (land p q)
  | bit0 p, bit1 q => Num.bit0 (land p q)
  | bit1 p, bit0 q => Num.bit0 (land p q)
  | bit1 p, bit1 q => Num.bit1 (land p q)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HAnd PosNum PosNum Num
  body: PosNum.land

中文:
实例 :
  签名: HAnd PosNum PosNum Num
  定义体: PosNum.land

Depends on / 依赖: PosNum, PosNum.land
-/
instance : HAnd PosNum PosNum Num where hAnd := PosNum.land

/--
lemma `land_eq_and` / 引理 `land_eq_and`

English:
lemma land_eq_and
  given: (p q : PosNum)
  statement: p.land q = p &&& q
  proof: rfl

中文:
引理 land_eq_and
  条件: (p q : PosNum)
  结论: p.land q = p &&& q
  证明: rfl
-/
@[simp] lemma land_eq_and (p q : PosNum) : p.land q = p &&& q := rfl

/--
Definition of `ldiff` / `ldiff` 的定义

English:
definition ldiff
  signature: : PosNum -> PosNum -> Num

中文:
定义 ldiff
  签名: : PosNum -> PosNum -> Num
-/
def ldiff : PosNum -> PosNum -> Num
  | 1, bit0 _ => 1
  | 1, _ => 0
  | bit0 p, 1 => Num.pos (bit0 p)
  | bit1 p, 1 => Num.pos (bit0 p)
  | bit0 p, bit0 q => Num.bit0 (ldiff p q)
  | bit0 p, bit1 q => Num.bit0 (ldiff p q)
  | bit1 p, bit0 q => Num.bit1 (ldiff p q)
  | bit1 p, bit1 q => Num.bit0 (ldiff p q)

/--
Definition of `lxor` / `lxor` 的定义

English:
definition lxor
  signature: : PosNum -> PosNum -> Num

中文:
定义 lxor
  签名: : PosNum -> PosNum -> Num
-/
def lxor : PosNum -> PosNum -> Num
  | 1, 1 => 0
  | 1, bit0 q => Num.pos (bit1 q)
  | 1, bit1 q => Num.pos (bit0 q)
  | bit0 p, 1 => Num.pos (bit1 p)
  | bit1 p, 1 => Num.pos (bit0 p)
  | bit0 p, bit0 q => Num.bit0 (lxor p q)
  | bit0 p, bit1 q => Num.bit1 (lxor p q)
  | bit1 p, bit0 q => Num.bit1 (lxor p q)
  | bit1 p, bit1 q => Num.bit0 (lxor p q)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HXor PosNum PosNum Num
  body: PosNum.lxor

中文:
实例 :
  签名: HXor PosNum PosNum Num
  定义体: PosNum.lxor

Depends on / 依赖: PosNum, PosNum.lxor
-/
instance : HXor PosNum PosNum Num where hXor := PosNum.lxor

/--
lemma `lxor_eq_xor` / 引理 `lxor_eq_xor`

English:
lemma lxor_eq_xor
  given: (p q : PosNum)
  statement: p.lxor q = p ^^^ q
  proof: rfl

中文:
引理 lxor_eq_xor
  条件: (p q : PosNum)
  结论: p.lxor q = p ^^^ q
  证明: rfl
-/
@[simp] lemma lxor_eq_xor (p q : PosNum) : p.lxor q = p ^^^ q := rfl

/--
Definition of `testBit` / `testBit` 的定义

English:
definition testBit
  signature: : PosNum -> Nat -> Bool

中文:
定义 testBit
  签名: : PosNum -> 自然数 -> 布尔
-/
def testBit : PosNum -> Nat -> Bool
  | 1, 0 => true
  | 1, _ => false
  | bit0 _, 0 => false
  | bit0 p, n + 1 => testBit p n
  | bit1 _, 0 => true
  | bit1 p, n + 1 => testBit p n

/--
Definition of `oneBits` / `oneBits` 的定义

English:
definition oneBits
  signature: : PosNum -> Nat -> List Nat

中文:
定义 oneBits
  签名: : PosNum -> 自然数 -> List 自然数
-/
def oneBits : PosNum -> Nat -> List Nat
  | 1, d => [d]
  | bit0 p, d => oneBits p (d + 1)
  | bit1 p, d => d :: oneBits p (d + 1)

/--
Definition of `shiftl` / `shiftl` 的定义

English:
definition shiftl
  signature: : PosNum -> Nat -> PosNum

中文:
定义 shiftl
  签名: : PosNum -> 自然数 -> PosNum
-/
def shiftl : PosNum -> Nat -> PosNum
  | p, 0 => p
  | p, n + 1 => shiftl p.bit0 n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HShiftLeft PosNum Nat PosNum
  body: PosNum.shiftl

中文:
实例 :
  签名: HShiftLeft PosNum 自然数 PosNum
  定义体: PosNum.shiftl

Depends on / 依赖: PosNum, PosNum.shiftl, shiftl
-/
instance : HShiftLeft PosNum Nat PosNum where hShiftLeft := PosNum.shiftl

/--
lemma `shiftl_eq_shiftLeft` / 引理 `shiftl_eq_shiftLeft`

English:
lemma shiftl_eq_shiftLeft
  given: (p : PosNum) (n : Nat)
  statement: p.shiftl n = p <<< n
  proof: rfl

中文:
引理 shiftl_eq_shiftLeft
  条件: (p : PosNum) (n : 自然数)
  结论: p.shiftl n = p <<< n
  证明: rfl
-/
@[simp] lemma shiftl_eq_shiftLeft (p : PosNum) (n : Nat) : p.shiftl n = p <<< n := rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
-- This shows that the tail-recursive definition is the same as the more naïve recursion.
/--
theorem `shiftl_succ_eq_bit0_shiftl` / 定理 `shiftl_succ_eq_bit0_shiftl`

English:
theorem shiftl_succ_eq_bit0_shiftl
  statement: forall (p : PosNum) (n : Nat), p <<< n.succ = bit0 (p <<< n)

中文:
定理 shiftl_succ_eq_bit0_shiftl
  结论: 对任意 (p : PosNum) (n : 自然数), p <<< n.succ = bit0 (p <<< n)
-/
theorem shiftl_succ_eq_bit0_shiftl : forall (p : PosNum) (n : Nat), p <<< n.succ = bit0 (p <<< n)
  | _, 0 => rfl
  | p, .succ n => shiftl_succ_eq_bit0_shiftl p.bit0 n

/--
Definition of `shiftr` / `shiftr` 的定义

English:
definition shiftr
  signature: : PosNum -> Nat -> Num

中文:
定义 shiftr
  签名: : PosNum -> 自然数 -> Num
-/
def shiftr : PosNum -> Nat -> Num
  | p, 0 => Num.pos p
  | 1, _ => 0
  | bit0 p, n + 1 => shiftr p n
  | bit1 p, n + 1 => shiftr p n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HShiftRight PosNum Nat Num
  body: PosNum.shiftr

中文:
实例 :
  签名: HShiftRight PosNum 自然数 Num
  定义体: PosNum.shiftr

Depends on / 依赖: PosNum, PosNum.shiftr, shiftr
-/
instance : HShiftRight PosNum Nat Num where hShiftRight := PosNum.shiftr

/--
lemma `shiftr_eq_shiftRight` / 引理 `shiftr_eq_shiftRight`

English:
lemma shiftr_eq_shiftRight
  given: (p : PosNum) (n : Nat)
  statement: p.shiftr n = p >>> n
  proof: rfl

中文:
引理 shiftr_eq_shiftRight
  条件: (p : PosNum) (n : 自然数)
  结论: p.shiftr n = p >>> n
  证明: rfl
-/
@[simp] lemma shiftr_eq_shiftRight (p : PosNum) (n : Nat) : p.shiftr n = p >>> n := rfl

end PosNum

namespace Num

/--
Definition of `lor` / `lor` 的定义

English:
definition lor
  signature: : Num -> Num -> Num

中文:
定义 lor
  签名: : Num -> Num -> Num
-/
protected def lor : Num -> Num -> Num
  | 0, q => q
  | p, 0 => p
  | pos p, pos q => pos (p ||| q)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrOp Num
  body: Num.lor

中文:
实例 :
  签名: OrOp Num
  定义体: Num.lor

Depends on / 依赖: Num.lor
-/
instance : OrOp Num where or := Num.lor

/--
lemma `lor_eq_or` / 引理 `lor_eq_or`

English:
lemma lor_eq_or
  given: (p q : Num)
  statement: p.lor q = p ||| q
  proof: rfl

中文:
引理 lor_eq_or
  条件: (p q : Num)
  结论: p.lor q = p ||| q
  证明: rfl
-/
@[simp] lemma lor_eq_or (p q : Num) : p.lor q = p ||| q := rfl

/--
Definition of `land` / `land` 的定义

English:
definition land
  signature: : Num -> Num -> Num

中文:
定义 land
  签名: : Num -> Num -> Num
-/
def land : Num -> Num -> Num
  | 0, _ => 0
  | _, 0 => 0
  | pos p, pos q => p &&& q

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AndOp Num
  body: Num.land

中文:
实例 :
  签名: AndOp Num
  定义体: Num.land

Depends on / 依赖: Num.land
-/
instance : AndOp Num where and := Num.land

/--
lemma `land_eq_and` / 引理 `land_eq_and`

English:
lemma land_eq_and
  given: (p q : Num)
  statement: p.land q = p &&& q
  proof: rfl

中文:
引理 land_eq_and
  条件: (p q : Num)
  结论: p.land q = p &&& q
  证明: rfl
-/
@[simp] lemma land_eq_and (p q : Num) : p.land q = p &&& q := rfl

/--
Definition of `ldiff` / `ldiff` 的定义

English:
definition ldiff
  signature: : Num -> Num -> Num

中文:
定义 ldiff
  签名: : Num -> Num -> Num
-/
def ldiff : Num -> Num -> Num
  | 0, _ => 0
  | p, 0 => p
  | pos p, pos q => p.ldiff q

/--
Definition of `lxor` / `lxor` 的定义

English:
definition lxor
  signature: : Num -> Num -> Num

中文:
定义 lxor
  签名: : Num -> Num -> Num
-/
def lxor : Num -> Num -> Num
  | 0, q => q
  | p, 0 => p
  | pos p, pos q => p ^^^ q

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: XorOp Num
  body: Num.lxor

中文:
实例 :
  签名: XorOp Num
  定义体: Num.lxor

Depends on / 依赖: Num.lxor
-/
instance : XorOp Num where xor := Num.lxor

/--
lemma `lxor_eq_xor` / 引理 `lxor_eq_xor`

English:
lemma lxor_eq_xor
  given: (p q : Num)
  statement: p.lxor q = p ^^^ q
  proof: rfl

中文:
引理 lxor_eq_xor
  条件: (p q : Num)
  结论: p.lxor q = p ^^^ q
  证明: rfl
-/
@[simp] lemma lxor_eq_xor (p q : Num) : p.lxor q = p ^^^ q := rfl

/--
Definition of `shiftl` / `shiftl` 的定义

English:
definition shiftl
  signature: : Num -> Nat -> Num

中文:
定义 shiftl
  签名: : Num -> 自然数 -> Num
-/
def shiftl : Num -> Nat -> Num
  | 0, _ => 0
  | pos p, n => pos (p <<< n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HShiftLeft Num Nat Num
  body: Num.shiftl

中文:
实例 :
  签名: HShiftLeft Num 自然数 Num
  定义体: Num.shiftl

Depends on / 依赖: Num.shiftl, shiftl
-/
instance : HShiftLeft Num Nat Num where hShiftLeft := Num.shiftl

/--
lemma `shiftl_eq_shiftLeft` / 引理 `shiftl_eq_shiftLeft`

English:
lemma shiftl_eq_shiftLeft
  given: (p : Num) (n : Nat)
  statement: p.shiftl n = p <<< n
  proof: rfl

中文:
引理 shiftl_eq_shiftLeft
  条件: (p : Num) (n : 自然数)
  结论: p.shiftl n = p <<< n
  证明: rfl
-/
@[simp] lemma shiftl_eq_shiftLeft (p : Num) (n : Nat) : p.shiftl n = p <<< n := rfl

/--
Definition of `shiftr` / `shiftr` 的定义

English:
definition shiftr
  signature: : Num -> Nat -> Num

中文:
定义 shiftr
  签名: : Num -> 自然数 -> Num
-/
def shiftr : Num -> Nat -> Num
  | 0, _ => 0
  | pos p, n => p >>> n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HShiftRight Num Nat Num
  body: Num.shiftr

中文:
实例 :
  签名: HShiftRight Num 自然数 Num
  定义体: Num.shiftr

Depends on / 依赖: Num.shiftr, shiftr
-/
instance : HShiftRight Num Nat Num where hShiftRight := Num.shiftr

/--
lemma `shiftr_eq_shiftRight` / 引理 `shiftr_eq_shiftRight`

English:
lemma shiftr_eq_shiftRight
  given: (p : Num) (n : Nat)
  statement: p.shiftr n = p >>> n
  proof: rfl

中文:
引理 shiftr_eq_shiftRight
  条件: (p : Num) (n : 自然数)
  结论: p.shiftr n = p >>> n
  证明: rfl
-/
@[simp] lemma shiftr_eq_shiftRight (p : Num) (n : Nat) : p.shiftr n = p >>> n := rfl

/--
Definition of `testBit` / `testBit` 的定义

English:
definition testBit
  signature: : Num -> Nat -> Bool

中文:
定义 testBit
  签名: : Num -> 自然数 -> 布尔
-/
def testBit : Num -> Nat -> Bool
  | 0, _ => false
  | pos p, n => p.testBit n

/--
Definition of `oneBits` / `oneBits` 的定义

English:
definition oneBits
  signature: : Num -> List Nat

中文:
定义 oneBits
  签名: : Num -> List 自然数
-/
def oneBits : Num -> List Nat
  | 0 => []
  | pos p => p.oneBits 0

end Num

/--
Inductive type `NzsNum` / 归纳类型 `NzsNum`

English:
inductive NzsNum
  parameters: : Type
  constructors (2):
    - msb: Bool -> NzsNum
    - bit: Bool -> NzsNum -> NzsNum

中文:
归纳类型 NzsNum
  参数: : Type
  构造子 (2 个):
    - msb: 布尔 -> NzsNum
    - bit: 布尔 -> NzsNum -> NzsNum

Depends on / 依赖: Algebra, Algebra.TensorProduct.liftEquivRight, TensorProduct, liftEquivRight, of_equiv
-/
inductive NzsNum : Type
  | msb : Bool -> NzsNum
  /-- Add a bit at the end of a `NzsNum`. -/
  | bit : Bool -> NzsNum -> NzsNum
  deriving DecidableEq

/--
Inductive type `SNum` / 归纳类型 `SNum`

English:
inductive SNum
  parameters: : Type
  constructors (2):
    - zero: Bool -> SNum
    - nz: NzsNum -> SNum

中文:
归纳类型 SNum
  参数: : Type
  构造子 (2 个):
    - zero: 布尔 -> SNum
    - nz: NzsNum -> SNum
-/
inductive SNum : Type
  | zero : Bool -> SNum
  | nz : NzsNum -> SNum
  deriving DecidableEq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe NzsNum SNum
  body: ⟨SNum.nz⟩

中文:
实例 :
  签名: Coe NzsNum SNum
  定义体: ⟨SNum.nz⟩

Depends on / 依赖: SNum.nz
-/
instance : Coe NzsNum SNum :=
  ⟨SNum.nz⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero SNum
  body: ⟨SNum.zero false⟩

中文:
实例 :
  签名: Zero SNum
  定义体: ⟨SNum.zero false⟩

Depends on / 依赖: SNum.zero
-/
instance : Zero SNum :=
  ⟨SNum.zero false⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One NzsNum
  body: ⟨NzsNum.msb true⟩

中文:
实例 :
  签名: One NzsNum
  定义体: ⟨NzsNum.msb true⟩

Depends on / 依赖: NzsNum, NzsNum.msb
-/
instance : One NzsNum :=
  ⟨NzsNum.msb true⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One SNum
  body: ⟨SNum.nz 1⟩

中文:
实例 :
  签名: One SNum
  定义体: ⟨SNum.nz 1⟩

Depends on / 依赖: SNum.nz
-/
instance : One SNum :=
  ⟨SNum.nz 1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited NzsNum
  body: ⟨1⟩

中文:
实例 :
  签名: Inhabited NzsNum
  定义体: ⟨1⟩
-/
instance : Inhabited NzsNum :=
  ⟨1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited SNum
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited SNum
  定义体: ⟨0⟩
-/
instance : Inhabited SNum :=
  ⟨0⟩

/-!
The `SNum` representation uses a bit string, essentially a list of 0 (`false`) and 1 (`true`) bits,
and the negation of the MSB is sign-extended to all higher bits.
-/


namespace NzsNum

@[inherit_doc]
scoped notation a "::" b => bit a b

/--
Definition of `sign` / `sign` 的定义

English:
definition sign
  signature: : NzsNum -> Bool

中文:
定义 sign
  签名: : NzsNum -> 布尔

Depends on / 依赖: Algebra, toSubalgebra
-/
def sign : NzsNum -> Bool
  | msb b => not b
  | _ :: p => sign p

/-- Bitwise `not` for `NzsNum`. -/
@[match_pattern]
/--
Definition of `not` / `not` 的定义

English:
definition not
  signature: : NzsNum -> NzsNum

中文:
定义 not
  签名: : NzsNum -> NzsNum

Depends on / 依赖: Algebra, toSubalgebra
-/
def not : NzsNum -> NzsNum
  | msb b => msb (Not b)
  | b :: p => Not b :: not p

@[inherit_doc]
scoped prefix:100 "~" => not

/--
Definition of `bit0` / `bit0` 的定义

English:
definition bit0
  signature: : NzsNum -> NzsNum
  body: bit false

中文:
定义 bit0
  签名: : NzsNum -> NzsNum
  定义体: bit false
-/
def bit0 : NzsNum -> NzsNum :=
  bit false

/--
Definition of `bit1` / `bit1` 的定义

English:
definition bit1
  signature: : NzsNum -> NzsNum
  body: bit true

中文:
定义 bit1
  签名: : NzsNum -> NzsNum
  定义体: bit true
-/
def bit1 : NzsNum -> NzsNum :=
  bit true

/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: : NzsNum -> Bool

中文:
定义 head
  签名: : NzsNum -> 布尔
-/
def head : NzsNum -> Bool
  | msb b => b
  | b :: _ => b

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: : NzsNum -> SNum

中文:
定义 tail
  签名: : NzsNum -> SNum
-/
def tail : NzsNum -> SNum
  | msb b => SNum.zero (Not b)
  | _ :: p => p

end NzsNum

namespace SNum

open NzsNum

/--
Definition of `sign` / `sign` 的定义

English:
definition sign
  signature: : SNum -> Bool

中文:
定义 sign
  签名: : SNum -> 布尔
-/
def sign : SNum -> Bool
  | zero z => z
  | nz p => p.sign

/-- Bitwise `not` for `SNum`. -/
@[match_pattern]
/--
Definition of `not` / `not` 的定义

English:
definition not
  signature: : SNum -> SNum

中文:
定义 not
  签名: : SNum -> SNum
-/
def not : SNum -> SNum
  | zero z => zero (Not z)
  | nz p => ~p

-- Higher `priority` so that `~1 : SNum` is unambiguous.
@[inherit_doc]
scoped prefix:100 (priority := default + 1) "~" => not

/-- Add a bit at the end of a `SNum`. This mimics `NzsNum.bit`. -/
@[match_pattern]
/--
Definition of `bit` / `bit` 的定义

English:
definition bit
  signature: : Bool -> SNum -> SNum

中文:
定义 bit
  签名: : 布尔 -> SNum -> SNum
-/
def bit : Bool -> SNum -> SNum
  | b, zero z => if b = z then zero b else msb b
  | b, nz p => p.bit b

@[inherit_doc]
scoped notation a "::" b => bit a b

/--
Definition of `bit0` / `bit0` 的定义

English:
definition bit0
  signature: : SNum -> SNum
  body: bit false

中文:
定义 bit0
  签名: : SNum -> SNum
  定义体: bit false
-/
def bit0 : SNum -> SNum :=
  bit false

/--
Definition of `bit1` / `bit1` 的定义

English:
definition bit1
  signature: : SNum -> SNum
  body: bit true

中文:
定义 bit1
  签名: : SNum -> SNum
  定义体: bit true
-/
def bit1 : SNum -> SNum :=
  bit true

/--
theorem `bit_zero` / 定理 `bit_zero`

English:
theorem bit_zero
  given: (b : Bool)
  statement: (b :: zero b) = zero b
  proof: by cases b <;> rfl

中文:
定理 bit_zero
  条件: (b : 布尔)
  结论: (b :: zero b) = zero b
  证明: by cases b <;> rfl
-/
theorem bit_zero (b : Bool) : (b :: zero b) = zero b := by cases b <;> rfl

/--
theorem `bit_one` / 定理 `bit_one`

English:
theorem bit_one
  given: (b : Bool)
  statement: (b :: zero (Not b)) = msb b
  proof: by cases b <;> rfl

中文:
定理 bit_one
  条件: (b : 布尔)
  结论: (b :: zero (Not b)) = msb b
  证明: by cases b <;> rfl
-/
theorem bit_one (b : Bool) : (b :: zero (Not b)) = msb b := by cases b <;> rfl

end SNum

namespace NzsNum

open SNum

/--
Definition of `drec'` / `drec'` 的定义

English:
definition drec'
  signature: {C : SNum -> Sort*} (z : forall b, C (SNum.zero b)) (s : forall b p, C p -> C (b :: p))

中文:
定义 drec'
  签名: {C : SNum -> Sort*} (z : 对任意 b, C (SNum.zero b)) (s : 对任意 b p, C p -> C (b :: p))
-/
def drec' {C : SNum -> Sort*} (z : forall b, C (SNum.zero b)) (s : forall b p, C p -> C (b :: p)) :
    forall p : NzsNum, C p
  | msb b => by rw [← bit_one]; exact s b (SNum.zero (Not b)) (z (Not b))
  | bit b p => s b p (drec' z s p)

end NzsNum

namespace SNum

open NzsNum

/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: : SNum -> Bool

中文:
定义 head
  签名: : SNum -> 布尔
-/
def head : SNum -> Bool
  | zero z => z
  | nz p => p.head

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: : SNum -> SNum

中文:
定义 tail
  签名: : SNum -> SNum
-/
def tail : SNum -> SNum
  | zero z => zero z
  | nz p => p.tail

/--
Definition of `drec'` / `drec'` 的定义

English:
definition drec'
  signature: {C : SNum -> Sort*} (z : forall b, C (SNum.zero b)) (s : forall b p, C p -> C (b :: p))

中文:
定义 drec'
  签名: {C : SNum -> Sort*} (z : 对任意 b, C (SNum.zero b)) (s : 对任意 b p, C p -> C (b :: p))
-/
def drec' {C : SNum -> Sort*} (z : forall b, C (SNum.zero b)) (s : forall b p, C p -> C (b :: p)) : forall p, C p
  | zero b => z b
  | nz p => p.drec' z s

/--
Definition of `rec'` / `rec'` 的定义

English:
definition rec'
  signature: {α} (z : Bool -> α) (s : Bool -> SNum -> α -> α)
  body: drec' z s

中文:
定义 rec'
  签名: {α} (z : 布尔 -> α) (s : 布尔 -> SNum -> α -> α)
  定义体: drec' z s
-/
def rec' {α} (z : Bool -> α) (s : Bool -> SNum -> α -> α) : SNum -> α :=
  drec' z s

/--
Definition of `testBit` / `testBit` 的定义

English:
definition testBit
  signature: : Nat -> SNum -> Bool

中文:
定义 testBit
  签名: : 自然数 -> SNum -> 布尔
-/
def testBit : Nat -> SNum -> Bool
  | 0, p => head p
  | n + 1, p => testBit n (tail p)

/--
Definition of `succ` / `succ` 的定义

English:
definition succ
  signature: : SNum -> SNum
  body: rec' (fun b => cond b 0 1) fun b p succp => cond b (false :: succp) (true :: p)

中文:
定义 succ
  签名: : SNum -> SNum
  定义体: rec' (fun b => cond b 0 1) fun b p succp => cond b (false :: succp) (true :: p)
-/
def succ : SNum -> SNum :=
  rec' (fun b => cond b 0 1) fun b p succp => cond b (false :: succp) (true :: p)

/--
Definition of `pred` / `pred` 的定义

English:
definition pred
  signature: : SNum -> SNum
  body: rec' (fun b => cond b (~1) (~0)) fun b p predp => cond b (false :: p) (true :: predp)

中文:
定义 pred
  签名: : SNum -> SNum
  定义体: rec' (fun b => cond b (~1) (~0)) fun b p predp => cond b (false :: p) (true :: predp)
-/
def pred : SNum -> SNum :=
  rec' (fun b => cond b (~1) (~0)) fun b p predp => cond b (false :: p) (true :: predp)

/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: (n : SNum)
  body: succ (~n)

中文:
定义 neg
  签名: (n : SNum)
  定义体: succ (~n)
-/
protected def neg (n : SNum) : SNum :=
  succ (~n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg SNum
  body: ⟨SNum.neg⟩

中文:
实例 :
  签名: Neg SNum
  定义体: ⟨SNum.neg⟩

Depends on / 依赖: SNum.neg
-/
instance : Neg SNum :=
  ⟨SNum.neg⟩

/--
Definition of `czAdd` / `czAdd` 的定义

English:
definition czAdd
  signature: : Bool -> Bool -> SNum -> SNum

中文:
定义 czAdd
  签名: : 布尔 -> 布尔 -> SNum -> SNum
-/
def czAdd : Bool -> Bool -> SNum -> SNum
  | false, false, p => p
  | false, true, p => pred p
  | true, false, p => succ p
  | true, true, p => p

end SNum

namespace SNum

/--
Definition of `bits` / `bits` 的定义

English:
definition bits
  signature: : SNum -> forall n, List.Vector Bool n

中文:
定义 bits
  签名: : SNum -> 对任意 n, List.Vector 布尔 n
-/
def bits : SNum -> forall n, List.Vector Bool n
  | _, 0 => Vector.nil
  | p, n + 1 => head p ::ᵥ bits (tail p) n

/--
Definition of `cAdd` / `cAdd` 的定义

English:
definition cAdd
  signature: : SNum -> SNum -> Bool -> SNum
  body: rec' (fun a p c => czAdd c a p) fun a p IH =>
    rec' (fun b c => czAdd c b (a :: p)) fun b q _ c => Bool.xor3 a b c :: IH q (Bool.carry a b c)

中文:
定义 cAdd
  签名: : SNum -> SNum -> 布尔 -> SNum
  定义体: rec' (fun a p c => czAdd c a p) fun a p IH =>
    rec' (fun b c => czAdd c b (a :: p)) fun b q _ c => Bool.xor3 a b c :: IH q (Bool.carry a b c)

Depends on / 依赖: Bool.carry, Bool.xor3
-/
def cAdd : SNum -> SNum -> Bool -> SNum :=
  rec' (fun a p c => czAdd c a p) fun a p IH =>
    rec' (fun b c => czAdd c b (a :: p)) fun b q _ c => Bool.xor3 a b c :: IH q (Bool.carry a b c)

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: (a b : SNum)
  body: cAdd a b false

中文:
定义 add
  签名: (a b : SNum)
  定义体: cAdd a b false
-/
protected def add (a b : SNum) : SNum :=
  cAdd a b false

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add SNum
  body: ⟨SNum.add⟩

中文:
实例 :
  签名: Add SNum
  定义体: ⟨SNum.add⟩

Depends on / 依赖: SNum.add
-/
instance : Add SNum :=
  ⟨SNum.add⟩

/--
Definition of `sub` / `sub` 的定义

English:
definition sub
  signature: (a b : SNum)
  body: a + -b

中文:
定义 sub
  签名: (a b : SNum)
  定义体: a + -b
-/
protected def sub (a b : SNum) : SNum :=
  a + -b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub SNum
  body: ⟨SNum.sub⟩

中文:
实例 :
  签名: Sub SNum
  定义体: ⟨SNum.sub⟩

Depends on / 依赖: SNum.sub
-/
instance : Sub SNum :=
  ⟨SNum.sub⟩

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: (a : SNum)
  body: rec' (fun b => cond b (-a) 0) fun b _ IH => cond b (bit0 IH + a) (bit0 IH)

中文:
定义 mul
  签名: (a : SNum)
  定义体: rec' (fun b => cond b (-a) 0) fun b _ IH => cond b (bit0 IH + a) (bit0 IH)
-/
protected def mul (a : SNum) : SNum -> SNum :=
  rec' (fun b => cond b (-a) 0) fun b _ IH => cond b (bit0 IH + a) (bit0 IH)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul SNum
  body: ⟨SNum.mul⟩

中文:
实例 :
  签名: Mul SNum
  定义体: ⟨SNum.mul⟩

Depends on / 依赖: SNum.mul
-/
instance : Mul SNum :=
  ⟨SNum.mul⟩

end SNum
