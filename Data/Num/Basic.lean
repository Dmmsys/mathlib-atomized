/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Lean.Linter.Deprecated
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.BinaryRec

/-!
# Binary representation of integers using inductive types

Note: Unlike in Coq, where this representation is preferred because of
the reliance on kernel reduction, in Lean this representation is discouraged
in favor of the "Peano" natural numbers `Nat`, and the purpose of this
collection of theorems is to show the equivalence of the different approaches.
-/

@[expose] public section

/-- The type of positive binary numbers.

```
13 = 1101(base 2) = bit1 (bit0 (bit1 one))
``` -/
/-
**PosNum** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of positive binary numbers.

```
13 = 1101(base 2) = bit1 (bit0 (bit1 one))
```
-/
inductive PosNum : Type
  | one : PosNum
  | bit1 : PosNum → PosNum
  | bit0 : PosNum → PosNum
  deriving DecidableEq
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One PosNum :=
  ⟨PosNum.one⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited PosNum :=
  ⟨1⟩

/-- The type of nonnegative binary numbers, using `PosNum`.

```
13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one)))
``` -/
/-
**Num** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of nonnegative binary numbers, using `PosNum`.

```
13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one)))
```
-/
inductive Num : Type
  | zero : Num
  | pos : PosNum → Num
  deriving DecidableEq
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero Num :=
  ⟨Num.zero⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One Num :=
  ⟨Num.pos 1⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Num :=
  ⟨0⟩

/-- Representation of integers using trichotomy around zero.

```
13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one)))
-13 = -1101(base 2) = neg (bit1 (bit0 (bit1 one)))
``` -/
/-
**ZNum** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Representation of integers using trichotomy around zero.

```
13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one)))
-13 = -1101(base 2) = neg (bit1 (bit0 (bit1 one)))
```
-/
inductive ZNum : Type
  | zero : ZNum
  | pos : PosNum → ZNum
  | neg : PosNum → ZNum
  deriving DecidableEq
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero ZNum :=
  ⟨ZNum.zero⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One ZNum :=
  ⟨ZNum.pos 1⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited ZNum :=
  ⟨0⟩

namespace PosNum

/-- `bit b n` appends the bit `b` to the end of `n`, where `bit tt x = x1` and `bit ff x = x0`. -/
/-
**PosNum.bit** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：bit (b : Bool) : PosNum -> PosNum
参数：b : Bool。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bit b n` appends the bit `b` to the end of `n`, where `bit tt x = x1` and `bit 
ff x = x0`.
-/
def bit (b : Bool) : PosNum → PosNum :=
  cond b bit1 bit0

/-- The successor of a `PosNum`. -/
/-
**PosNum.succ** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The successor of a `PosNum`.
-/
def succ : PosNum → PosNum
  | 1 => bit0 one
  | bit1 n => bit0 (succ n)
  | bit0 n => bit1 n

/-- Returns a Boolean for whether the `PosNum` is `one`. -/
/-
**PosNum.isOne** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns a Boolean for whether the `PosNum` is `one`.
-/
def isOne : PosNum → Bool
  | 1 => true
  | _ => false

/-- Addition of two `PosNum`s. -/
/-
**PosNum.add** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → PosNum → PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Addition of two `PosNum`s.
-/
protected def add : PosNum → PosNum → PosNum
  | 1, b => succ b
  | a, 1 => succ a
  | bit0 a, bit0 b => bit0 (PosNum.add a b)
  | bit1 a, bit1 b => bit0 (succ (PosNum.add a b))
  | bit0 a, bit1 b => bit1 (PosNum.add a b)
  | bit1 a, bit0 b => bit1 (PosNum.add a b)
/-
**PosNum.** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add PosNum :=
  ⟨PosNum.add⟩

/-- The predecessor of a `PosNum` as a `Num`. -/
/-
**PosNum.pred'** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 => rfl | bit0 n 
=> have : Nat.succ ↑(pred' n) = ↑n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predecessor of a `PosNum` as a `Num`.
-/
def pred' : PosNum → Num
  | 1 => 0
  | bit0 n => Num.pos (Num.casesOn (pred' n) 1 bit1)
  | bit1 n => Num.pos (bit0 n)

/-- The predecessor of a `PosNum` as a `PosNum`. This means that `pred 1 = 1`. -/
/-
**PosNum.pred** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：pred (a : PosNum) : PosNum
参数：a : PosNum。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n

--- 原说明 ---
The predecessor of a `PosNum` as a `PosNum`. This means that `pred 1 = 1`.
-/
def pred (a : PosNum) : PosNum :=
  Num.casesOn (pred' a) 1 id

/-- The number of bits of a `PosNum`, as a `PosNum`. -/
/-
**PosNum.size** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The number of bits of a `PosNum`, as a `PosNum`.
-/
def size : PosNum → PosNum
  | 1 => 1
  | bit0 n => succ (size n)
  | bit1 n => succ (size n)

/-- The number of bits of a `PosNum`, as a `Nat`. -/
/-
**PosNum.natSize** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The number of bits of a `PosNum`, as a `Nat`.
-/
def natSize : PosNum → Nat
  | 1 => 1
  | bit0 n => Nat.succ (natSize n)
  | bit1 n => Nat.succ (natSize n)

/-- Multiplication of two `PosNum`s. -/
/-
**PosNum.mul** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → PosNum → PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of two `PosNum`s.
-/
protected def mul (a : PosNum) : PosNum → PosNum
  | 1 => a
  | bit0 b => bit0 (PosNum.mul a b)
  | bit1 b => bit0 (PosNum.mul a b) + a
/-
**PosNum.** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul PosNum :=
  ⟨PosNum.mul⟩

/-- `ofNatSucc n` is the `PosNum` corresponding to `n + 1`. -/
/-
**PosNum.ofNatSucc** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：ℕ → PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofNatSucc n` is the `PosNum` corresponding to `n + 1`.
-/
def ofNatSucc : ℕ → PosNum
  | 0 => 1
  | Nat.succ n => succ (ofNatSucc n)

/-- `ofNat n` is the `PosNum` corresponding to `n`, except for `ofNat 0 = 1`. -/
/-
**PosNum.ofNat** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：ofNat (n : Nat) : PosNum
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofNat n` is the `PosNum` corresponding to `n`, except for `ofNat 0 = 1`.
-/
def ofNat (n : ℕ) : PosNum :=
  ofNatSucc (Nat.pred n)
/-
**PosNum.** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {n : ℕ} : OfNat PosNum (n + 1) where
  ofNat := ofNat (n + 1)

open Ordering

/-- Ordering of `PosNum`s. -/
/-
**PosNum.cmp** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → PosNum → Ordering
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ordering of `PosNum`s.
-/
def cmp : PosNum → PosNum → Ordering
  | 1, 1 => eq
  | _, 1 => gt
  | 1, _ => lt
  | bit0 a, bit0 b => cmp a b
  | bit0 a, bit1 b => Ordering.casesOn (cmp a b) lt lt gt
  | bit1 a, bit0 b => Ordering.casesOn (cmp a b) lt gt gt
  | bit1 a, bit1 b => cmp a b
/-
**PosNum.** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LT PosNum :=
  ⟨fun a b => cmp a b = Ordering.lt⟩
/-
**PosNum.** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE PosNum :=
  ⟨fun a b => ¬b < a⟩
/-
**PosNum.decidableLT** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：DecidableLT PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLT : DecidableLT PosNum
  | a, b => by dsimp [LT.lt]; infer_instance
/-
**PosNum.decidableLE** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：DecidableLE PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLE : DecidableLE PosNum
  | a, b => by dsimp [LE.le]; infer_instance

end PosNum

section

variable {α : Type*} [One α] [Add α]

/-- `castPosNum` casts a `PosNum` into any type which has `1` and `+`. -/
@[coe]
/-
**castPosNum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α : Type u_1} → [One α] → [Add α] → PosNum → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`castPosNum` casts a `PosNum` into any type which has `1` and `+`.
-/
def castPosNum : PosNum → α
  | 1 => 1
  | PosNum.bit0 a => castPosNum a + castPosNum a
  | PosNum.bit1 a => castPosNum a + castPosNum a + 1

/-- `castNum` casts a `Num` into any type which has `0`, `1` and `+`. -/
@[coe]
/-
**castNum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α : Type u_1} → [One α] → [Add α] → [Zero α] → Num → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`castNum` casts a `Num` into any type which has `0`, `1` and `+`.
-/
def castNum [Zero α] : Num → α
  | 0 => 0
  | Num.pos p => castPosNum p

-- see Note [coercion into rings]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) posNumCoe : CoeHTCT PosNum α :=
  ⟨castPosNum⟩

-- see Note [coercion into rings]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) numNatCoe [Zero α] : CoeHTCT Num α :=
  ⟨castNum⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Repr PosNum :=
  ⟨fun n _ => repr (n : ℕ)⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Repr Num :=
  ⟨fun n _ => repr (n : ℕ)⟩

end

namespace Num

open PosNum

/-- The successor of a `Num` as a `PosNum`. -/
/-
**Num.succ'** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The successor of a `Num` as a `PosNum`.
-/
def succ' : Num → PosNum
  | 0 => 1
  | pos p => succ p

/-- The successor of a `Num` as a `Num`. -/
/-
**Num.succ** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：succ (n : Num) : Num
参数：n : Num。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The successor of a `Num` as a `Num`.
-/
def succ (n : Num) : Num :=
  pos (succ' n)

/-- Addition of two `Num`s. -/
/-
**Num.add** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Addition of two `Num`s.
-/
protected def add : Num → Num → Num
  | 0, a => a
  | b, 0 => b
  | pos a, pos b => pos (a + b)
/-
**Num.** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add Num :=
  ⟨Num.add⟩

/-- `bit0 n` appends a `0` to the end of `n`, where `bit0 n = n0`. -/
/-
**Num.bit0** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bit0 n` appends a `0` to the end of `n`, where `bit0 n = n0`.
-/
protected def bit0 : Num → Num
  | 0 => 0
  | pos n => pos (PosNum.bit0 n)

/-- `bit1 n` appends a `1` to the end of `n`, where `bit1 n = n1`. -/
/-
**Num.bit1** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bit1 n` appends a `1` to the end of `n`, where `bit1 n = n1`.
-/
protected def bit1 : Num → Num
  | 0 => 1
  | pos n => pos (PosNum.bit1 n)

/-- `bit b n` appends the bit `b` to the end of `n`, where `bit tt x = x1` and `bit ff x = x0`. -/
/-
**Num.bit** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：bit (b : Bool) : Num -> Num
参数：b : Bool。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bit b n` appends the bit `b` to the end of `n`, where `bit tt x = x1` and `bit 
ff x = x0`.
-/
def bit (b : Bool) : Num → Num :=
  cond b Num.bit1 Num.bit0

/-- The number of bits required to represent a `Num`, as a `Num`. `size 0` is defined to be `0`. -/
/-
**Num.size** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The number of bits required to represent a `Num`, as a `Num`. `size 0` is define
d to be `0`.
-/
def size : Num → Num
  | 0 => 0
  | pos n => pos (PosNum.size n)

/-- The number of bits required to represent a `Num`, as a `Nat`. `size 0` is defined to be `0`. -/
/-
**Num.natSize** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The number of bits required to represent a `Num`, as a `Nat`. `size 0` is define
d to be `0`.
-/
def natSize : Num → Nat
  | 0 => 0
  | pos n => PosNum.natSize n

/-- Multiplication of two `Num`s. -/
/-
**Num.mul** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of two `Num`s.
-/
protected def mul : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | pos a, pos b => pos (a * b)
/-
**Num.** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul Num :=
  ⟨Num.mul⟩

open Ordering

/-- Ordering of `Num`s. -/
/-
**Num.cmp** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num → Ordering
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ordering of `Num`s.
-/
def cmp : Num → Num → Ordering
  | 0, 0 => eq
  | _, 0 => gt
  | 0, _ => lt
  | pos a, pos b => PosNum.cmp a b
/-
**Num.** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LT Num :=
  ⟨fun a b => cmp a b = Ordering.lt⟩
/-
**Num.** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE Num :=
  ⟨fun a b => ¬b < a⟩
/-
**Num.decidableLT** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：DecidableLT Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLT : DecidableLT Num
  | a, b => by dsimp [LT.lt]; infer_instance
/-
**Num.decidableLE** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：DecidableLE Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLE : DecidableLE Num
  | a, b => by dsimp [LE.le]; infer_instance

/-- Converts a `Num` to a `ZNum`. -/
/-
**Num.toZNum** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → ZNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `Num` to a `ZNum`.
-/
def toZNum : Num → ZNum
  | 0 => 0
  | pos a => ZNum.pos a

/-- Converts `x : Num` to `-x : ZNum`. -/
/-
**Num.toZNumNeg** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → ZNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts `x : Num` to `-x : ZNum`.
-/
def toZNumNeg : Num → ZNum
  | 0 => 0
  | pos a => ZNum.neg a

/-- Converts a `Nat` to a `Num`. -/
/-
**Num.ofNat'** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：ofNat' : Nat -> Num
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `Nat` to a `Num`.
-/
def ofNat' : ℕ → Num :=
  Nat.binaryRec 0 (fun b _ => cond b Num.bit1 Num.bit0)

end Num

namespace ZNum

open PosNum

/-- The negation of a `ZNum`. -/
/-
**ZNum.zNeg** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：ZNum → ZNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The negation of a `ZNum`.
-/
def zNeg : ZNum → ZNum
  | 0 => 0
  | pos a => neg a
  | neg a => pos a
/-
**ZNum.** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg ZNum :=
  ⟨zNeg⟩

/-- The absolute value of a `ZNum` as a `Num`. -/
/-
**ZNum.abs** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：ZNum → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The absolute value of a `ZNum` as a `Num`.
-/
def abs : ZNum → Num
  | 0 => 0
  | pos a => Num.pos a
  | neg a => Num.pos a

/-- The successor of a `ZNum`. -/
/-
**ZNum.succ** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：ZNum → ZNum
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n

--- 原说明 ---
The successor of a `ZNum`.
-/
def succ : ZNum → ZNum
  | 0 => 1
  | pos a => pos (PosNum.succ a)
  | neg a => (PosNum.pred' a).toZNumNeg

/-- The predecessor of a `ZNum`. -/
/-
**ZNum.pred** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：ZNum → ZNum
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n

--- 原说明 ---
The predecessor of a `ZNum`.
-/
def pred : ZNum → ZNum
  | 0 => neg 1
  | pos a => (PosNum.pred' a).toZNum
  | neg a => neg (PosNum.succ a)

/-- `bit0 n` appends a `0` to the end of `n`, where `bit0 n = n0`. -/
/-
**ZNum.bit0** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：ZNum → ZNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bit0 n` appends a `0` to the end of `n`, where `bit0 n = n0`.
-/
protected def bit0 : ZNum → ZNum
  | 0 => 0
  | pos n => pos (PosNum.bit0 n)
  | neg n => neg (PosNum.bit0 n)

/-- `bit1 x` appends a `1` to the end of `x`, mapping `x` to `2 * x + 1`. -/
/-
**ZNum.bit1** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：ZNum → ZNum
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n

--- 原说明 ---
`bit1 x` appends a `1` to the end of `x`, mapping `x` to `2 * x + 1`.
-/
protected def bit1 : ZNum → ZNum
  | 0 => 1
  | pos n => pos (PosNum.bit1 n)
  | neg n => neg (Num.casesOn (pred' n) 1 PosNum.bit1)

/-- `bitm1 x` appends a `1` to the end of `x`, mapping `x` to `2 * x - 1`. -/
/-
**ZNum.bitm1** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：ZNum → ZNum
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n

--- 原说明 ---
`bitm1 x` appends a `1` to the end of `x`, mapping `x` to `2 * x - 1`.
-/
protected def bitm1 : ZNum → ZNum
  | 0 => neg 1
  | pos n => pos (Num.casesOn (pred' n) 1 PosNum.bit1)
  | neg n => neg (PosNum.bit1 n)

/-- Converts an `Int` to a `ZNum`. -/
/-
**ZNum.ofInt'** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：ℤ → ZNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts an `Int` to a `ZNum`.
-/
def ofInt' : ℤ → ZNum
  | Int.ofNat n => Num.toZNum (Num.ofNat' n)
  | Int.negSucc n => Num.toZNumNeg (Num.ofNat' (n + 1))

end ZNum

namespace PosNum

open ZNum

/-- Subtraction of two `PosNum`s, producing a `ZNum`. -/
/-
**PosNum.sub'** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum
参数：a : PosNum。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subtraction of two `PosNum`s, producing a `ZNum`.
-/
def sub' : PosNum → PosNum → ZNum
  | a, 1 => (pred' a).toZNum
  | 1, b => (pred' b).toZNumNeg
  | bit0 a, bit0 b => (sub' a b).bit0
  | bit0 a, bit1 b => (sub' a b).bitm1
  | bit1 a, bit0 b => (sub' a b).bit1
  | bit1 a, bit1 b => (sub' a b).bit0

/-- Converts a `ZNum` to `Option PosNum`, where it is `some` if the `ZNum` was positive and `none`
  otherwise. -/
/-
**PosNum.ofZNum'** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：ZNum → Option PosNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `ZNum` to `Option PosNum`, where it is `some` if the `ZNum` was posit
ive and `none`
  otherwise.
-/
def ofZNum' : ZNum → Option PosNum
  | ZNum.pos p => some p
  | _ => none

/-- Converts a `ZNum` to a `PosNum`, mapping all out of range values to `1`. -/
/-
**PosNum.ofZNum** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：ofZNum : ZNum -> PosNum | ZNum.pos p => p | _ => 1  /-- Subtraction of `Po
sNum`s, where if `a < b`, then `a - b = 1`. -/ protected def sub (a b : PosNum) 
: PosNum
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `ZNum` to a `PosNum`, mapping all out of range values to `1`.
-/
def ofZNum : ZNum → PosNum
  | ZNum.pos p => p
  | _ => 1

/-- Subtraction of `PosNum`s, where if `a < b`, then `a - b = 1`. -/
/-
**PosNum.sub** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：PosNum → PosNum → PosNum
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.sub'`：sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum

--- 原说明 ---
Subtraction of `PosNum`s, where if `a < b`, then `a - b = 1`.
-/
protected def sub (a b : PosNum) : PosNum :=
  match sub' a b with
  | ZNum.pos p => p
  | _ => 1
/-
**PosNum.** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub PosNum :=
  ⟨PosNum.sub⟩

end PosNum

namespace Num

/-- The predecessor of a `Num` as an `Option Num`, where `ppred 0 = none` -/
/-
**Num.ppred** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Option Num
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n

--- 原说明 ---
The predecessor of a `Num` as an `Option Num`, where `ppred 0 = none`
-/
def ppred : Num → Option Num
  | 0 => none
  | pos p => some p.pred'

/-- The predecessor of a `Num` as a `Num`, where `pred 0 = 0`. -/
/-
**Num.pred** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n

--- 原说明 ---
The predecessor of a `Num` as a `Num`, where `pred 0 = 0`.
-/
def pred : Num → Num
  | 0 => 0
  | pos p => p.pred'

/-- Divides a `Num` by `2` -/
/-
**Num.div2** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Divides a `Num` by `2`
-/
def div2 : Num → Num
  | 0 => 0
  | 1 => 0
  | pos (PosNum.bit0 p) => pos p
  | pos (PosNum.bit1 p) => pos p

/-- Converts a `ZNum` to an `Option Num`, where `ofZNum' p = none` if `p < 0`. -/
/-
**Num.ofZNum'** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：ZNum → Option Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `ZNum` to an `Option Num`, where `ofZNum' p = none` if `p < 0`.
-/
def ofZNum' : ZNum → Option Num
  | 0 => some 0
  | ZNum.pos p => some (pos p)
  | ZNum.neg _ => none

/-- Converts a `ZNum` to an `Option Num`, where `ofZNum p = 0` if `p < 0`. -/
/-
**Num.ofZNum** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：ZNum → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `ZNum` to an `Option Num`, where `ofZNum p = 0` if `p < 0`.
-/
def ofZNum : ZNum → Num
  | ZNum.pos p => pos p
  | _ => 0

/-- Subtraction of two `Num`s, producing a `ZNum`. -/
/-
**Num.sub'** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num → ZNum
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.sub'`：sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum

--- 原说明 ---
Subtraction of two `Num`s, producing a `ZNum`.
-/
def sub' : Num → Num → ZNum
  | 0, 0 => 0
  | pos a, 0 => ZNum.pos a
  | 0, pos b => ZNum.neg b
  | pos a, pos b => a.sub' b

/-- Subtraction of two `Num`s, producing an `Option Num`. -/
/-
**Num.psub** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：psub (a b : Num) : Option Num
参数：a b : Num。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subtraction of two `Num`s, producing an `Option Num`.
-/
def psub (a b : Num) : Option Num :=
  ofZNum' (sub' a b)

/-- Subtraction of two `Num`s, where if `a < b`, `a - b = 0`. -/
/-
**Num.sub** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subtraction of two `Num`s, where if `a < b`, `a - b = 0`.
-/
protected def sub (a b : Num) : Num :=
  ofZNum (sub' a b)
/-
**Num.** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub Num :=
  ⟨Num.sub⟩

end Num

namespace ZNum

open PosNum

/-- Addition of `ZNum`s. -/
/-
**ZNum.add** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：ZNum → ZNum → ZNum
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.sub'`：sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum

--- 原说明 ---
Addition of `ZNum`s.
-/
protected def add : ZNum → ZNum → ZNum
  | 0, a => a
  | b, 0 => b
  | pos a, pos b => pos (a + b)
  | pos a, neg b => sub' a b
  | neg a, pos b => sub' b a
  | neg a, neg b => neg (a + b)
/-
**ZNum.** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add ZNum :=
  ⟨ZNum.add⟩

/-- Multiplication of `ZNum`s. -/
/-
**ZNum.mul** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：ZNum → ZNum → ZNum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of `ZNum`s.
-/
protected def mul : ZNum → ZNum → ZNum
  | 0, _ => 0
  | _, 0 => 0
  | pos a, pos b => pos (a * b)
  | pos a, neg b => neg (a * b)
  | neg a, pos b => neg (a * b)
  | neg a, neg b => pos (a * b)
/-
**ZNum.** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul ZNum :=
  ⟨ZNum.mul⟩

open Ordering

/-- Ordering on `ZNum`s. -/
/-
**ZNum.cmp** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：ZNum → ZNum → Ordering
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ordering on `ZNum`s.
-/
def cmp : ZNum → ZNum → Ordering
  | 0, 0 => eq
  | pos a, pos b => PosNum.cmp a b
  | neg a, neg b => PosNum.cmp b a
  | pos _, _ => gt
  | neg _, _ => lt
  | _, pos _ => lt
  | _, neg _ => gt
/-
**ZNum.** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LT ZNum :=
  ⟨fun a b => cmp a b = Ordering.lt⟩
/-
**ZNum.** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE ZNum :=
  ⟨fun a b => ¬b < a⟩
/-
**ZNum.decidableLT** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
形式化陈述：decidableLT : DecidableLT ZNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLT : DecidableLT ZNum :=
  inferInstanceAs <| DecidableRel fun a b => cmp a b = Ordering.lt
/-
**ZNum.decidableLE** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
形式化陈述：decidableLE : DecidableLE ZNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLE : DecidableLE ZNum :=
  inferInstanceAs <| DecidableRel fun a b => ¬b < a

end ZNum

namespace PosNum

/-- Auxiliary definition for `PosNum.divMod`. -/
/-
**PosNum.divModAux** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：divModAux (d : PosNum) (q r : Num) : Num × Num
参数：d : PosNum；q r : Num。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `PosNum.divMod`.
-/
def divModAux (d : PosNum) (q r : Num) : Num × Num :=
  match Num.ofZNum' (Num.sub' r (Num.pos d)) with
  | some r' => (Num.bit1 q, r')
  | none => (Num.bit0 q, r)

/-- `divMod x y = (y / x, y % x)`. -/
/-
**PosNum.divMod** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：divMod (d : PosNum) : PosNum -> Num × Num | bit0 n => let (q, r₁)
参数：d : PosNum。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`divMod x y = (y / x, y % x)`.
-/
def divMod (d : PosNum) : PosNum → Num × Num
  | bit0 n =>
    let (q, r₁) := divMod d n
    divModAux d q (Num.bit0 r₁)
  | bit1 n =>
    let (q, r₁) := divMod d n
    divModAux d q (Num.bit1 r₁)
  | 1 => divModAux d 0 1

/-- Division of `PosNum` -/
/-
**PosNum.div'** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：div' (n d : PosNum) : Num
参数：n d : PosNum。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Division of `PosNum`
-/
def div' (n d : PosNum) : Num :=
  (divMod d n).1

/-- Modulus of `PosNum`s. -/
/-
**PosNum.mod'** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
形式化陈述：mod' (n d : PosNum) : Num
参数：n d : PosNum。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Modulus of `PosNum`s.
-/
def mod' (n d : PosNum) : Num :=
  (divMod d n).2

/-- Auxiliary definition for `sqrtAux`. -/
/-
**PosNum.sqrtAux1** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `sqrtAux`.
-/
private def sqrtAux1 (b : PosNum) (r n : Num) : Num × Num :=
  match Num.ofZNum' (n.sub' (r + Num.pos b)) with
  | some n' => (r.div2 + Num.pos b, n')
  | none => (r.div2, n)

/-- Auxiliary definition for a `sqrt` function which is not currently implemented. -/
/-
**PosNum.sqrtAux** 是 Mathlib 中的一个定义，位于命名空间 `PosNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for a `sqrt` function which is not currently implemented.
-/
private def sqrtAux : PosNum → Num → Num → Num
  | b@(bit0 b') => fun r n => let (r', n') := sqrtAux1 b r n; sqrtAux b' r' n'
  | b@(bit1 b') => fun r n => let (r', n') := sqrtAux1 b r n; sqrtAux b' r' n'
  | 1 => fun r n => (sqrtAux1 1 r n).1

end PosNum

namespace Num

/-- Division of `Num`s, where `x / 0 = 0`. -/
/-
**Num.div** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Division of `Num`s, where `x / 0 = 0`.
-/
def div : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | pos n, pos d => PosNum.div' n d

/-- Modulus of `Num`s. -/
/-
**Num.mod** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：Num → Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Modulus of `Num`s.
-/
def mod : Num → Num → Num
  | 0, _ => 0
  | n, 0 => n
  | pos n, pos d => PosNum.mod' n d
/-
**Num.** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div Num :=
  ⟨Num.div⟩
/-
**Num.** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mod Num :=
  ⟨Num.mod⟩

/-- Auxiliary definition for `Num.gcd`. -/
/-
**Num.gcdAux** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：ℕ → Num → Num → Num
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Num.gcd`.
-/
def gcdAux : Nat → Num → Num → Num
  | 0, _, b => b
  | Nat.succ _, 0, b => b
  | Nat.succ n, a, b => gcdAux n (b % a) a

/-- Greatest Common Divisor (GCD) of two `Num`s. -/
/-
**Num.gcd** 是 Mathlib 中的一个定义，位于命名空间 `Num`。
形式化陈述：gcd (a b : Num) : Num
参数：a b : Num。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Greatest Common Divisor (GCD) of two `Num`s.
-/
def gcd (a b : Num) : Num :=
  if a ≤ b then gcdAux (a.natSize + b.natSize) a b else gcdAux (b.natSize + a.natSize) b a

end Num

namespace ZNum

/-- Division of `ZNum`, where `x / 0 = 0`. -/
/-
**ZNum.div** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：ZNum → ZNum → ZNum
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n

--- 原说明 ---
Division of `ZNum`, where `x / 0 = 0`.
-/
def div : ZNum → ZNum → ZNum
  | 0, _ => 0
  | _, 0 => 0
  | pos n, pos d => Num.toZNum (PosNum.div' n d)
  | pos n, neg d => Num.toZNumNeg (PosNum.div' n d)
  | neg n, pos d => neg (PosNum.pred' n / Num.pos d).succ'
  | neg n, neg d => pos (PosNum.pred' n / Num.pos d).succ'

/-- Modulus of `ZNum`s. -/
/-
**ZNum.mod** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：ZNum → ZNum → ZNum
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n

--- 原说明 ---
Modulus of `ZNum`s.
-/
def mod : ZNum → ZNum → ZNum
  | 0, _ => 0
  | pos n, d => Num.toZNum (Num.pos n % d.abs)
  | neg n, d => d.abs.sub' (PosNum.pred' n % d.abs).succ
/-
**ZNum.** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div ZNum :=
  ⟨ZNum.div⟩
/-
**ZNum.** 是 Mathlib 中的一个实例，位于命名空间 `ZNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mod ZNum :=
  ⟨ZNum.mod⟩

/-- Greatest Common Divisor (GCD) of two `ZNum`s. -/
/-
**ZNum.gcd** 是 Mathlib 中的一个定义，位于命名空间 `ZNum`。
形式化陈述：gcd (a b : ZNum) : Num
参数：a b : ZNum。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Greatest Common Divisor (GCD) of two `ZNum`s.
-/
def gcd (a b : ZNum) : Num :=
  a.abs.gcd b.abs

end ZNum

section
variable {α : Type*} [Zero α] [One α] [Add α] [Neg α]

/-- `castZNum` casts a `ZNum` into any type which has `0`, `1`, `+` and `neg` -/
@[coe]
/-
**castZNum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α : Type u_1} → [Zero α] → [One α] → [Add α] → [Neg α] → ZNum → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`castZNum` casts a `ZNum` into any type which has `0`, `1`, `+` and `neg`
-/
def castZNum : ZNum → α
  | 0 => 0
  | ZNum.pos p => p
  | ZNum.neg p => -p

-- see Note [coercion into rings]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) znumCoe : CoeHTCT ZNum α :=
  ⟨castZNum⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Repr ZNum :=
  ⟨fun n _ => repr (n : ℤ)⟩

end

