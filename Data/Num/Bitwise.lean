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

/-- Bitwise "or" for `PosNum`. -/
/-
**PosNum.lor** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → PosNum → PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bitwise "or" for `PosNum`.
-/
def lor : PosNum → PosNum → PosNum
  | 1, bit0 q => bit1 q
  | 1, q => q
  | bit0 p, 1 => bit1 p
  | p, 1 => p
  | bit0 p, bit0 q => bit0 (lor p q)
  | bit0 p, bit1 q => bit1 (lor p q)
  | bit1 p, bit0 q => bit1 (lor p q)
  | bit1 p, bit1 q => bit1 (lor p q)
/-
**PosNum.** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrOp PosNum where or := PosNum.lor
/-
**PosNum.lor_eq_or** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (p q : PosNum), p.lor q = p ||| q
参数：p q : PosNum。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lor_eq_or (p q : PosNum) : p.lor q = p ||| q := rfl

/-- Bitwise "and" for `PosNum`. -/
/-
**PosNum.land** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → PosNum → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bitwise "and" for `PosNum`.
-/
def land : PosNum → PosNum → Num
  | 1, bit0 _ => 0
  | 1, _ => 1
  | bit0 _, 1 => 0
  | _, 1 => 1
  | bit0 p, bit0 q => Num.bit0 (land p q)
  | bit0 p, bit1 q => Num.bit0 (land p q)
  | bit1 p, bit0 q => Num.bit0 (land p q)
  | bit1 p, bit1 q => Num.bit1 (land p q)
/-
**PosNum.** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HAnd PosNum PosNum Num where hAnd := PosNum.land
/-
**PosNum.land_eq_and** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (p q : PosNum), p.land q = p &&& q
参数：p q : PosNum。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma land_eq_and (p q : PosNum) : p.land q = p &&& q := rfl

/-- Bitwise `fun a b ↦ a && !b` for `PosNum`. For example, `ldiff 5 9 = 4`:
```
 101
1001
----
 100
```
-/
/-
**PosNum.ldiff** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → PosNum → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bitwise `fun a b ↦ a && !b` for `PosNum`. For example, `ldiff 5 9 = 4`:
```
 101
1001
----
 100
```
-/
def ldiff : PosNum → PosNum → Num
  | 1, bit0 _ => 1
  | 1, _ => 0
  | bit0 p, 1 => Num.pos (bit0 p)
  | bit1 p, 1 => Num.pos (bit0 p)
  | bit0 p, bit0 q => Num.bit0 (ldiff p q)
  | bit0 p, bit1 q => Num.bit0 (ldiff p q)
  | bit1 p, bit0 q => Num.bit1 (ldiff p q)
  | bit1 p, bit1 q => Num.bit0 (ldiff p q)

/-- Bitwise "xor" for `PosNum`. -/
/-
**PosNum.lxor** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → PosNum → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bitwise "xor" for `PosNum`.
-/
def lxor : PosNum → PosNum → Num
  | 1, 1 => 0
  | 1, bit0 q => Num.pos (bit1 q)
  | 1, bit1 q => Num.pos (bit0 q)
  | bit0 p, 1 => Num.pos (bit1 p)
  | bit1 p, 1 => Num.pos (bit0 p)
  | bit0 p, bit0 q => Num.bit0 (lxor p q)
  | bit0 p, bit1 q => Num.bit1 (lxor p q)
  | bit1 p, bit0 q => Num.bit1 (lxor p q)
  | bit1 p, bit1 q => Num.bit0 (lxor p q)
/-
**PosNum.** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HXor PosNum PosNum Num where hXor := PosNum.lxor
/-
**PosNum.lxor_eq_xor** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (p q : PosNum), p.lxor q = p ^^^ q
参数：p q : PosNum。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lxor_eq_xor (p q : PosNum) : p.lxor q = p ^^^ q := rfl

/-- `a.testBit n` is `true` iff the `n`-th bit (starting from the LSB) in the binary representation
of `a` is active. If the size of `a` is less than `n`, this evaluates to `false`. -/
/-
**PosNum.testBit** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → ℕ → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a.testBit n` is `true` iff the `n`-th bit (starting from the LSB) in the binary
 representation
of `a` is active. If the size of `a` is less than `n`, this evaluates to `false`
.
-/
def testBit : PosNum → Nat → Bool
  | 1, 0 => true
  | 1, _ => false
  | bit0 _, 0 => false
  | bit0 p, n + 1 => testBit p n
  | bit1 _, 0 => true
  | bit1 p, n + 1 => testBit p n

/-- `n.oneBits 0` is the list of indices of active bits in the binary representation of `n`. -/
/-
**PosNum.oneBits** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → ℕ → List ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n.oneBits 0` is the list of indices of active bits in the binary representation
 of `n`.
-/
def oneBits : PosNum → Nat → List Nat
  | 1, d => [d]
  | bit0 p, d => oneBits p (d + 1)
  | bit1 p, d => d :: oneBits p (d + 1)

/-- Left-shift the binary representation of a `PosNum`. -/
/-
**PosNum.shiftl** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → ℕ → PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left-shift the binary representation of a `PosNum`.
-/
def shiftl : PosNum → Nat → PosNum
  | p, 0 => p
  | p, n + 1 => shiftl p.bit0 n
/-
**PosNum.** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HShiftLeft PosNum Nat PosNum where hShiftLeft := PosNum.shiftl
/-
**PosNum.shiftl_eq_shiftLeft** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (p : PosNum) (n : ℕ), p.shiftl n = p <<< n
参数：p : PosNum；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma shiftl_eq_shiftLeft (p : PosNum) (n : Nat) : p.shiftl n = p <<< n := rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
-- This shows that the tail-recursive definition is the same as the more naïve recursion.
/-
**PosNum.shiftl_succ_eq_bit0_shiftl** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (p : PosNum) (n : ℕ), p <<< n.succ = (p <<< n).bit0
参数：p : PosNum；n : ℕ；p <<< n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem shiftl_succ_eq_bit0_shiftl : ∀ (p : PosNum) (n : Nat), p <<< n.succ = bit0 (p <<< n)
  | _, 0       => rfl
  | p, .succ n => shiftl_succ_eq_bit0_shiftl p.bit0 n

/-- Right-shift the binary representation of a `PosNum`. -/
/-
**PosNum.shiftr** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → ℕ → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right-shift the binary representation of a `PosNum`.
-/
def shiftr : PosNum → Nat → Num
  | p, 0 => Num.pos p
  | 1, _ => 0
  | bit0 p, n + 1 => shiftr p n
  | bit1 p, n + 1 => shiftr p n
/-
**PosNum.** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HShiftRight PosNum Nat Num where hShiftRight := PosNum.shiftr
/-
**PosNum.shiftr_eq_shiftRight** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (p : PosNum) (n : ℕ), p.shiftr n = p >>> n
参数：p : PosNum；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma shiftr_eq_shiftRight (p : PosNum) (n : Nat) : p.shiftr n = p >>> n := rfl

end PosNum

namespace Num

/-- Bitwise "or" for `Num`. -/
/-
**Num.lor** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bitwise "or" for `Num`.
-/
protected def lor : Num → Num → Num
  | 0, q => q
  | p, 0 => p
  | pos p, pos q => pos (p ||| q)
/-
**Num.** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrOp Num where or := Num.lor
/-
**Num.lor_eq_or** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (p q : Num), p.lor q = p ||| q
参数：p q : Num。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lor_eq_or (p q : Num) : p.lor q = p ||| q := rfl

/-- Bitwise "and" for `Num`. -/
/-
**Num.land** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bitwise "and" for `Num`.
-/
def land : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | pos p, pos q => p &&& q
/-
**Num.** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AndOp Num where and := Num.land
/-
**Num.land_eq_and** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (p q : Num), p.land q = p &&& q
参数：p q : Num。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma land_eq_and (p q : Num) : p.land q = p &&& q := rfl

/-- Bitwise `fun a b ↦ a && !b` for `Num`. For example, `ldiff 5 9 = 4`:
```
 101
1001
----
 100
```
-/
/-
**Num.ldiff** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bitwise `fun a b ↦ a && !b` for `Num`. For example, `ldiff 5 9 = 4`:
```
 101
1001
----
 100
```
-/
def ldiff : Num → Num → Num
  | 0, _ => 0
  | p, 0 => p
  | pos p, pos q => p.ldiff q

/-- Bitwise "xor" for `Num`. -/
/-
**Num.lxor** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bitwise "xor" for `Num`.
-/
def lxor : Num → Num → Num
  | 0, q => q
  | p, 0 => p
  | pos p, pos q => p ^^^ q
/-
**Num.** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : XorOp Num where xor := Num.lxor
/-
**Num.lxor_eq_xor** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (p q : Num), p.lxor q = p ^^^ q
参数：p q : Num。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lxor_eq_xor (p q : Num) : p.lxor q = p ^^^ q := rfl

/-- Left-shift the binary representation of a `Num`. -/
/-
**Num.shiftl** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → ℕ → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left-shift the binary representation of a `Num`.
-/
def shiftl : Num → Nat → Num
  | 0, _ => 0
  | pos p, n => pos (p <<< n)
/-
**Num.** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HShiftLeft Num Nat Num where hShiftLeft := Num.shiftl
/-
**Num.shiftl_eq_shiftLeft** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (p : Num) (n : ℕ), p.shiftl n = p <<< n
参数：p : Num；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma shiftl_eq_shiftLeft (p : Num) (n : Nat) : p.shiftl n = p <<< n := rfl

/-- Right-shift the binary representation of a `Num`. -/
/-
**Num.shiftr** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → ℕ → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right-shift the binary representation of a `Num`.
-/
def shiftr : Num → Nat → Num
  | 0, _ => 0
  | pos p, n => p >>> n
/-
**Num.** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HShiftRight Num Nat Num where hShiftRight := Num.shiftr
/-
**Num.shiftr_eq_shiftRight** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (p : Num) (n : ℕ), p.shiftr n = p >>> n
参数：p : Num；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma shiftr_eq_shiftRight (p : Num) (n : Nat) : p.shiftr n = p >>> n := rfl

/-- `a.testBit n` is `true` iff the `n`-th bit (starting from the LSB) in the binary representation
of `a` is active. If the size of `a` is less than `n`, this evaluates to `false`. -/
/-
**Num.testBit** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → ℕ → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a.testBit n` is `true` iff the `n`-th bit (starting from the LSB) in the binary
 representation
of `a` is active. If the size of `a` is less than `n`, this evaluates to `false`
.
-/
def testBit : Num → Nat → Bool
  | 0, _ => false
  | pos p, n => p.testBit n

/-- `n.oneBits` is the list of indices of active bits in the binary representation of `n`. -/
/-
**Num.oneBits** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → List ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n.oneBits` is the list of indices of active bits in the binary representation o
f `n`.
-/
def oneBits : Num → List Nat
  | 0 => []
  | pos p => p.oneBits 0

end Num

/-- This is a nonzero (and "non minus one") version of `SNum`.
See the documentation of `SNum` for more details. -/
/-
**NzsNum** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a nonzero (and "non minus one") version of `SNum`.
See the documentation of `SNum` for more details.
-/
inductive NzsNum : Type
  | msb : Bool → NzsNum
  /-- Add a bit at the end of a `NzsNum`. -/
  | bit : Bool → NzsNum → NzsNum
  deriving DecidableEq

/--
Alternative representation of integers using a sign bit at the end.
The convention on sign here is to have the argument to `msb` denote
the sign of the MSB itself, with all higher bits set to the negation
of this sign. The result is interpreted in two's complement.

```
13  = ..0001101(base 2) = nz (bit1 (bit0 (bit1 (msb true))))
-13 = ..1110011(base 2) = nz (bit1 (bit1 (bit0 (msb false))))
```

  As with `Num`, a special case must be added for zero, which has no msb,
but by two's complement symmetry there is a second special case for -1.
Here the `Bool` field indicates the sign of the number.

```
0  = ..0000000(base 2) = zero false
-1 = ..1111111(base 2) = zero true
``` -/
/-
**SNum** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative representation of integers using a sign bit at the end.
The convention on sign here is to have the argument to `msb` denote
the sign of the MSB itself, with all higher bits set to the negation
of this sign. The result is interpreted in two's complement.

```
13  = ..0001101(base 2) = nz (bit1 (bit0 (bit1 (msb true))))
-13 = ..1110011(base 2) = nz (bit1 (bit1 (bit0 (msb false))))
```

  As with `Num`, a special case must be added for zero, which has no msb,
but by two's complement symmetry there is a second special case for -1.
Here the `Bool` field indicates the sign of the number.

```
0  = ..0000000(base 2) = zero false
-1 = ..1111111(base 2) = zero true
```
-/
inductive SNum : Type
  | zero : Bool → SNum
  | nz : NzsNum → SNum
  deriving DecidableEq
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe NzsNum SNum :=
  ⟨SNum.nz⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero SNum :=
  ⟨SNum.zero false⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One NzsNum :=
  ⟨NzsNum.msb true⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One SNum :=
  ⟨SNum.nz 1⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited NzsNum :=
  ⟨1⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- Sign of a `NzsNum`. -/
/-
**NzsNum.sign** 是 Mathlib 中的一个定义，位于命名空间 `NzsNum`。
形式化陈述：NzsNum → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sign of a `NzsNum`.
-/
def sign : NzsNum → Bool
  | msb b => not b
  | _ :: p => sign p

/-- Bitwise `not` for `NzsNum`. -/
@[match_pattern]
/-
**NzsNum.not** 是 Mathlib 中的一个定义，位于命名空间 `NzsNum`。
形式化陈述：NzsNum → NzsNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bitwise `not` for `NzsNum`.
-/
def not : NzsNum → NzsNum
  | msb b => msb (Not b)
  | b :: p => Not b :: not p

@[inherit_doc]
scoped prefix:100 "~" => not

/-- Add an inactive bit at the end of a `NzsNum`. This mimics `PosNum.bit0`. -/
/-
**NzsNum.bit0** 是 Mathlib 中的一个定义，位于命名空间 `NzsNum`。
形式化陈述：bit0 : NzsNum -> NzsNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Add an inactive bit at the end of a `NzsNum`. This mimics `PosNum.bit0`.
-/
def bit0 : NzsNum → NzsNum :=
  bit false

/-- Add an active bit at the end of a `NzsNum`. This mimics `PosNum.bit1`. -/
/-
**NzsNum.bit1** 是 Mathlib 中的一个定义，位于命名空间 `NzsNum`。
形式化陈述：bit1 : NzsNum -> NzsNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Add an active bit at the end of a `NzsNum`. This mimics `PosNum.bit1`.
-/
def bit1 : NzsNum → NzsNum :=
  bit true

/-- The `head` of a `NzsNum` is the Boolean value of its LSB. -/
/-
**NzsNum.head** 是 Mathlib 中的一个定义，位于命名空间 `NzsNum`。
形式化陈述：NzsNum → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `head` of a `NzsNum` is the Boolean value of its LSB.
-/
def head : NzsNum → Bool
  | msb b => b
  | b :: _ => b

/-- The `tail` of a `NzsNum` is the `SNum` obtained by removing the LSB.
Edge cases: `tail 1 = 0` and `tail (-2) = -1`. -/
/-
**NzsNum.tail** 是 Mathlib 中的一个定义，位于命名空间 `NzsNum`。
形式化陈述：NzsNum → SNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `tail` of a `NzsNum` is the `SNum` obtained by removing the LSB.
Edge cases: `tail 1 = 0` and `tail (-2) = -1`.
-/
def tail : NzsNum → SNum
  | msb b => SNum.zero (Not b)
  | _ :: p => p

end NzsNum

namespace SNum

open NzsNum

/-- Sign of a `SNum`. -/
/-
**SNum.sign** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：SNum → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sign of a `SNum`.
-/
def sign : SNum → Bool
  | zero z => z
  | nz p => p.sign

/-- Bitwise `not` for `SNum`. -/
@[match_pattern]
/-
**SNum.not** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：SNum → SNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bitwise `not` for `SNum`.
-/
def not : SNum → SNum
  | zero z => zero (Not z)
  | nz p => ~p

-- Higher `priority` so that `~1 : SNum` is unambiguous.
@[inherit_doc]
scoped prefix:100 (priority := default + 1) "~" => not

/-- Add a bit at the end of a `SNum`. This mimics `NzsNum.bit`. -/
@[match_pattern]
/-
**SNum.bit** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：Bool → SNum → SNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Add a bit at the end of a `SNum`. This mimics `NzsNum.bit`.
-/
def bit : Bool → SNum → SNum
  | b, zero z => if b = z then zero b else msb b
  | b, nz p => p.bit b

@[inherit_doc]
scoped notation a "::" b => bit a b

/-- Add an inactive bit at the end of a `SNum`. This mimics `ZNum.bit0`. -/
/-
**SNum.bit0** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：bit0 : SNum -> SNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Add an inactive bit at the end of a `SNum`. This mimics `ZNum.bit0`.
-/
def bit0 : SNum → SNum :=
  bit false

/-- Add an active bit at the end of a `SNum`. This mimics `ZNum.bit1`. -/
/-
**SNum.bit1** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：bit1 : SNum -> SNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Add an active bit at the end of a `SNum`. This mimics `ZNum.bit1`.
-/
def bit1 : SNum → SNum :=
  bit true
/-
**SNum.bit_zero** 是 Mathlib 中的一个定理，位于命名空间 `SNum`。
形式化陈述：bit_zero (b : Bool) : (b :: zero b) = zero b
参数：b : Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bit_zero (b : Bool) : (b :: zero b) = zero b := by cases b <;> rfl
/-
**SNum.bit_one** 是 Mathlib 中的一个定理，位于命名空间 `SNum`。
形式化陈述：bit_one (b : Bool) : (b :: zero (Not b)) = msb b
参数：b : Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bit_one (b : Bool) : (b :: zero (Not b)) = msb b := by cases b <;> rfl

end SNum

namespace NzsNum

open SNum

/-- A dependent induction principle for `NzsNum`, with base cases `0 : SNum` and `(-1) : SNum`. -/
/-
**NzsNum.drec'** 是 Mathlib 中的一个定义，位于命名空间 `NzsNum`。
形式化陈述：{C : SNum → Sort u_1} →   ((b : Bool) → C (SNum.zero b)) → ((b : Bool) → (
p : SNum) → C p → C (SNum.bit b p)) → (p : NzsNum) → C (SNum.nz p)
参数：(b : Bool) → C (SNum.zero b)；(b : Bool) → (p : SNum) → C p → C (SNum.bit b p)
；p : NzsNum；SNum.nz p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A dependent induction principle for `NzsNum`, with base cases `0 : SNum` and `(-
1) : SNum`.
-/
def drec' {C : SNum → Sort*} (z : ∀ b, C (SNum.zero b)) (s : ∀ b p, C p → C (b :: p)) :
    ∀ p : NzsNum, C p
  | msb b => by rw [← bit_one]; exact s b (SNum.zero (Not b)) (z (Not b))
  | bit b p => s b p (drec' z s p)

end NzsNum

namespace SNum

open NzsNum

/-- The `head` of a `SNum` is the Boolean value of its LSB. -/
/-
**SNum.head** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：SNum → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `head` of a `SNum` is the Boolean value of its LSB.
-/
def head : SNum → Bool
  | zero z => z
  | nz p => p.head

/-- The `tail` of a `SNum` is obtained by removing the LSB.
Edge cases: `tail 1 = 0`, `tail (-2) = -1`, `tail 0 = 0` and `tail (-1) = -1`. -/
/-
**SNum.tail** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：SNum → SNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `tail` of a `SNum` is obtained by removing the LSB.
Edge cases: `tail 1 = 0`, `tail (-2) = -1`, `tail 0 = 0` and `tail (-1) = -1`.
-/
def tail : SNum → SNum
  | zero z => zero z
  | nz p => p.tail

/-- A dependent induction principle for `SNum` which avoids relying on `NzsNum`. -/
/-
**SNum.drec'** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：{C : SNum → Sort u_1} →   ((b : Bool) → C (SNum.zero b)) → ((b : Bool) → (
p : SNum) → C p → C (SNum.bit b p)) → (p : SNum) → C p
参数：(b : Bool) → C (SNum.zero b)；(b : Bool) → (p : SNum) → C p → C (SNum.bit b p)
；p : SNum。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A dependent induction principle for `SNum` which avoids relying on `NzsNum`.
-/
def drec' {C : SNum → Sort*} (z : ∀ b, C (SNum.zero b)) (s : ∀ b p, C p → C (b :: p)) : ∀ p, C p
  | zero b => z b
  | nz p => p.drec' z s

/-- An induction principle for `SNum` which avoids relying on `NzsNum`. -/
/-
**SNum.rec'** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：rec' {α} (z : Bool -> α) (s : Bool -> SNum -> α -> α) : SNum -> α
参数：z : Bool -> α；s : Bool -> SNum -> α -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An induction principle for `SNum` which avoids relying on `NzsNum`.
-/
def rec' {α} (z : Bool → α) (s : Bool → SNum → α → α) : SNum → α :=
  drec' z s

/-- `SNum.testBit n a` is `true` iff the `n`-th bit (starting from the LSB) of `a` is active.
If the size of `a` is less than `n`, this evaluates to `false`. -/
/-
**SNum.testBit** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：ℕ → SNum → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SNum.testBit n a` is `true` iff the `n`-th bit (starting from the LSB) of `a` i
s active.
If the size of `a` is less than `n`, this evaluates to `false`.
-/
def testBit : Nat → SNum → Bool
  | 0, p => head p
  | n + 1, p => testBit n (tail p)

/-- The successor of a `SNum` (i.e. the operation adding one). -/
/-
**SNum.succ** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：succ : SNum -> SNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The successor of a `SNum` (i.e. the operation adding one).
-/
def succ : SNum → SNum :=
  rec' (fun b ↦ cond b 0 1) fun b p succp ↦ cond b (false :: succp) (true :: p)

/-- The predecessor of a `SNum` (i.e. the operation of removing one). -/
/-
**SNum.pred** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：pred : SNum -> SNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predecessor of a `SNum` (i.e. the operation of removing one).
-/
def pred : SNum → SNum :=
  rec' (fun b ↦ cond b (~1) (~0)) fun b p predp ↦ cond b (false :: p) (true :: predp)

/-- The opposite of a `SNum`. -/
/-
**SNum.neg** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：SNum → SNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a `SNum`.
-/
protected def neg (n : SNum) : SNum :=
  succ (~n)
/-
**SNum.** 是 Mathlib 中的一个实例，位于命名空间 `SNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg SNum :=
  ⟨SNum.neg⟩

/-- `SNum.czAdd a b n` is `n + a - b` (where `a` and `b` should be read as either 0 or 1).
This is useful to implement the carry system in `cAdd`. -/
/-
**SNum.czAdd** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：Bool → Bool → SNum → SNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SNum.czAdd a b n` is `n + a - b` (where `a` and `b` should be read as either 0 
or 1).
This is useful to implement the carry system in `cAdd`.
-/
def czAdd : Bool → Bool → SNum → SNum
  | false, false, p => p
  | false, true, p => pred p
  | true, false, p => succ p
  | true, true, p => p

end SNum

namespace SNum

/-- `a.bits n` is the vector of the `n` first bits of `a` (starting from the LSB). -/
/-
**SNum.bits** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：SNum → (n : ℕ) → List.Vector Bool n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a.bits n` is the vector of the `n` first bits of `a` (starting from the LSB).
-/
def bits : SNum → ∀ n, List.Vector Bool n
  | _, 0 => Vector.nil
  | p, n + 1 => head p ::ᵥ bits (tail p) n

/-- `SNum.cAdd n m a` is `n + m + a` (where `a` should be read as either 0 or 1).
`a` represents a carry bit. -/
/-
**SNum.cAdd** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：cAdd : SNum -> SNum -> Bool -> SNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SNum.cAdd n m a` is `n + m + a` (where `a` should be read as either 0 or 1).
`a` represents a carry bit.
-/
def cAdd : SNum → SNum → Bool → SNum :=
  rec' (fun a p c ↦ czAdd c a p) fun a p IH ↦
    rec' (fun b c ↦ czAdd c b (a :: p)) fun b q _ c ↦ Bool.xor3 a b c :: IH q (Bool.carry a b c)

/-- Add two `SNum`s. -/
/-
**SNum.add** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：SNum → SNum → SNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Add two `SNum`s.
-/
protected def add (a b : SNum) : SNum :=
  cAdd a b false
/-
**SNum.** 是 Mathlib 中的一个实例，位于命名空间 `SNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add SNum :=
  ⟨SNum.add⟩

/-- Subtract two `SNum`s. -/
/-
**SNum.sub** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：SNum → SNum → SNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subtract two `SNum`s.
-/
protected def sub (a b : SNum) : SNum :=
  a + -b
/-
**SNum.** 是 Mathlib 中的一个实例，位于命名空间 `SNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub SNum :=
  ⟨SNum.sub⟩

/-- Multiply two `SNum`s. -/
/-
**SNum.mul** 是 Mathlib 中的一个定义，位于命名空间 `SNum`。
形式化陈述：SNum → SNum → SNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiply two `SNum`s.
-/
protected def mul (a : SNum) : SNum → SNum :=
  rec' (fun b ↦ cond b (-a) 0) fun b _ IH ↦ cond b (bit0 IH + a) (bit0 IH)
/-
**SNum.** 是 Mathlib 中的一个实例，位于命名空间 `SNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul SNum :=
  ⟨SNum.mul⟩

end SNum

