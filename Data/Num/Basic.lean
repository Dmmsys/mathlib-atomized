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

/--
Inductive type `PosNum` / 归纳类型 `PosNum`

English:
inductive PosNum
  parameters: : Type
  constructors (3):
    - one: PosNum
    - bit1: PosNum -> PosNum
    - bit0: PosNum -> PosNum

中文:
归纳类型 PosNum
  参数: : 类型
  构造子 (3 个):
    - one: PosNum
    - bit1: PosNum -> PosNum
    - bit0: PosNum -> PosNum
-/
inductive PosNum : Type
  | one : PosNum
  | bit1 : PosNum -> PosNum
  | bit0 : PosNum -> PosNum
  deriving DecidableEq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One PosNum
  body: ⟨PosNum.one⟩

中文:
实例 :
  签名: 幺 PosNum
  定义体: ⟨PosNum.one⟩
-/
instance : One PosNum :=
  ⟨PosNum.one⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited PosNum
  body: ⟨1⟩

中文:
实例 :
  签名: 可居 PosNum
  定义体: ⟨1⟩
-/
instance : Inhabited PosNum :=
  ⟨1⟩

/--
Inductive type `Num` / 归纳类型 `Num`

English:
inductive Num
  parameters: : Type
  constructors (2):
    - zero: Num
    - pos: PosNum -> Num

中文:
归纳类型 Num
  参数: : 类型
  构造子 (2 个):
    - zero: Num
    - pos: PosNum -> Num
-/
inductive Num : Type
  | zero : Num
  | pos : PosNum -> Num
  deriving DecidableEq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero Num
  body: ⟨Num.zero⟩

中文:
实例 :
  签名: 零 Num
  定义体: ⟨Num.zero⟩
-/
instance : Zero Num :=
  ⟨Num.zero⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One Num
  body: ⟨Num.pos 1⟩

中文:
实例 :
  签名: 幺 Num
  定义体: ⟨Num.pos 1⟩

Depends on / 依赖: Num.pos
-/
instance : One Num :=
  ⟨Num.pos 1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Num
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 Num
  定义体: ⟨0⟩
-/
instance : Inhabited Num :=
  ⟨0⟩

/--
Inductive type `ZNum` / 归纳类型 `ZNum`

English:
inductive ZNum
  parameters: : Type
  constructors (3):
    - zero: ZNum
    - pos: PosNum -> ZNum
    - neg: PosNum -> ZNum

中文:
归纳类型 ZNum
  参数: : 类型
  构造子 (3 个):
    - zero: ZNum
    - pos: PosNum -> ZNum
    - neg: PosNum -> ZNum
-/
inductive ZNum : Type
  | zero : ZNum
  | pos : PosNum -> ZNum
  | neg : PosNum -> ZNum
  deriving DecidableEq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero ZNum
  body: ⟨ZNum.zero⟩

中文:
实例 :
  签名: 零 ZNum
  定义体: ⟨ZNum.zero⟩
-/
instance : Zero ZNum :=
  ⟨ZNum.zero⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One ZNum
  body: ⟨ZNum.pos 1⟩

中文:
实例 :
  签名: 幺 ZNum
  定义体: ⟨ZNum.pos 1⟩
-/
instance : One ZNum :=
  ⟨ZNum.pos 1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited ZNum
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 ZNum
  定义体: ⟨0⟩
-/
instance : Inhabited ZNum :=
  ⟨0⟩

namespace PosNum

/--
Definition of `bit` / `bit` 的定义

English:
definition bit
  signature: (b : Bool)
  body: cond b bit1 bit0

中文:
定义 bit
  签名: (b : 布尔值)
  定义体: cond b bit1 bit0
-/
def bit (b : Bool) : PosNum -> PosNum :=
  cond b bit1 bit0

/--
Definition of `succ` / `succ` 的定义

English:
definition succ
  signature: : PosNum -> PosNum

中文:
定义 succ
  签名: : PosNum -> PosNum
-/
def succ : PosNum -> PosNum
  | 1 => bit0 one
  | bit1 n => bit0 (succ n)
  | bit0 n => bit1 n

/--
Definition of `isOne` / `isOne` 的定义

English:
definition isOne
  signature: : PosNum -> Bool

中文:
定义 isOne
  签名: : PosNum -> 布尔值

Depends on / 依赖: AlgEquiv, AlgEquiv.apply_symm_apply, algebraMap_apply, algebraMap_extendRightEquiv, apply_symm_apply
-/
def isOne : PosNum -> Bool
  | 1 => true
  | _ => false

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: : PosNum -> PosNum -> PosNum

中文:
定义 add
  签名: : PosNum -> PosNum -> PosNum
-/
protected def add : PosNum -> PosNum -> PosNum
  | 1, b => succ b
  | a, 1 => succ a
  | bit0 a, bit0 b => bit0 (PosNum.add a b)
  | bit1 a, bit1 b => bit0 (succ (PosNum.add a b))
  | bit0 a, bit1 b => bit1 (PosNum.add a b)
  | bit1 a, bit0 b => bit1 (PosNum.add a b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add PosNum
  body: ⟨PosNum.add⟩

中文:
实例 :
  签名: 加法 PosNum
  定义体: ⟨PosNum.add⟩

Depends on / 依赖: PosNum, PosNum.add
-/
instance : Add PosNum :=
  ⟨PosNum.add⟩

/--
Definition of `pred'` / `pred'` 的定义

English:
definition pred'
  signature: : PosNum -> Num

中文:
定义 pred'
  签名: : PosNum -> Num
-/
def pred' : PosNum -> Num
  | 1 => 0
  | bit0 n => Num.pos (Num.casesOn (pred' n) 1 bit1)
  | bit1 n => Num.pos (bit0 n)

/--
Definition of `pred` / `pred` 的定义

English:
definition pred
  signature: (a : PosNum)
  body: Num.casesOn (pred' a) 1 id

中文:
定义 pred
  签名: (a : PosNum)
  定义体: Num.casesOn (pred' a) 1 id

Depends on / 依赖: Num.casesOn, casesOn
-/
def pred (a : PosNum) : PosNum :=
  Num.casesOn (pred' a) 1 id

/--
Definition of `size` / `size` 的定义

English:
definition size
  signature: : PosNum -> PosNum

中文:
定义 size
  签名: : PosNum -> PosNum
-/
def size : PosNum -> PosNum
  | 1 => 1
  | bit0 n => succ (size n)
  | bit1 n => succ (size n)

/--
Definition of `natSize` / `natSize` 的定义

English:
definition natSize
  signature: : PosNum -> Nat

中文:
定义 natSize
  签名: : PosNum -> 自然数
-/
def natSize : PosNum -> Nat
  | 1 => 1
  | bit0 n => Nat.succ (natSize n)
  | bit1 n => Nat.succ (natSize n)

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: (a : PosNum)

中文:
定义 mul
  签名: (a : PosNum)
-/
protected def mul (a : PosNum) : PosNum -> PosNum
  | 1 => a
  | bit0 b => bit0 (PosNum.mul a b)
  | bit1 b => bit0 (PosNum.mul a b) + a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul PosNum
  body: ⟨PosNum.mul⟩

中文:
实例 :
  签名: 乘法 PosNum
  定义体: ⟨PosNum.mul⟩

Depends on / 依赖: PosNum, PosNum.mul
-/
instance : Mul PosNum :=
  ⟨PosNum.mul⟩

/--
Definition of `ofNatSucc` / `ofNatSucc` 的定义

English:
definition ofNatSucc
  signature: : Nat -> PosNum

中文:
定义 of自然数Succ
  签名: : 自然数 -> PosNum
-/
def ofNatSucc : Nat -> PosNum
  | 0 => 1
  | Nat.succ n => succ (ofNatSucc n)

/--
Definition of `ofNat` / `ofNat` 的定义

English:
definition ofNat
  signature: (n : Nat)
  body: ofNatSucc (Nat.pred n)

中文:
定义 of自然数
  签名: (n : 自然数)
  定义体: ofNatSucc (Nat.pred n)

Depends on / 依赖: Nat.pred, ofNatSucc
-/
def ofNat (n : Nat) : PosNum :=
  ofNatSucc (Nat.pred n)

instance (priority := low) {n : Nat} : OfNat PosNum (n + 1) where
  ofNat := ofNat (n + 1)

open Ordering

/--
Definition of `cmp` / `cmp` 的定义

English:
definition cmp
  signature: : PosNum -> PosNum -> Ordering

中文:
定义 cmp
  签名: : PosNum -> PosNum -> Ordering
-/
def cmp : PosNum -> PosNum -> Ordering
  | 1, 1 => eq
  | _, 1 => gt
  | 1, _ => lt
  | bit0 a, bit0 b => cmp a b
  | bit0 a, bit1 b => Ordering.casesOn (cmp a b) lt lt gt
  | bit1 a, bit0 b => Ordering.casesOn (cmp a b) lt gt gt
  | bit1 a, bit1 b => cmp a b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT PosNum
  body: ⟨fun a b => cmp a b = Ordering.lt⟩

中文:
实例 :
  签名: LT PosNum
  定义体: ⟨fun a b => cmp a b = Ordering.lt⟩

Depends on / 依赖: Ordering, Ordering.lt
-/
instance : LT PosNum :=
  ⟨fun a b => cmp a b = Ordering.lt⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE PosNum
  body: ⟨fun a b => ¬b < a⟩

中文:
实例 :
  签名: LE PosNum
  定义体: ⟨fun a b => ¬b < a⟩
-/
instance : LE PosNum :=
  ⟨fun a b => ¬b < a⟩

/--
Instance `decidableLT` / 实例 `decidableLT`

English:
instance decidableLT
  signature: : DecidableLT PosNum

中文:
实例 decidableLT
  签名: : DecidableLT PosNum
-/
instance decidableLT : DecidableLT PosNum
  | a, b => by dsimp [LT.lt]; infer_instance

/--
Instance `decidableLE` / 实例 `decidableLE`

English:
instance decidableLE
  signature: : DecidableLE PosNum

中文:
实例 decidableLE
  签名: : DecidableLE PosNum
-/
instance decidableLE : DecidableLE PosNum
  | a, b => by dsimp [LE.le]; infer_instance

end PosNum

section

variable {α : Type*} [One α] [Add α]

/-- `castPosNum` casts a `PosNum` into any type which has `1` and `+`. -/
@[coe]
/--
Definition of `castPosNum` / `castPosNum` 的定义

English:
definition castPosNum
  signature: : PosNum -> α

中文:
定义 castPosNum
  签名: : PosNum -> α
-/
def castPosNum : PosNum -> α
  | 1 => 1
  | PosNum.bit0 a => castPosNum a + castPosNum a
  | PosNum.bit1 a => castPosNum a + castPosNum a + 1

/-- `castNum` casts a `Num` into any type which has `0`, `1` and `+`. -/
@[coe]
/--
Definition of `castNum` / `castNum` 的定义

English:
definition castNum
  signature: [Zero α]

中文:
定义 castNum
  签名: [零 α]
-/
def castNum [Zero α] : Num -> α
  | 0 => 0
  | Num.pos p => castPosNum p

-- see Note [coercion into rings]
instance (priority := 900) posNumCoe : CoeHTCT PosNum α :=
  ⟨castPosNum⟩

-- see Note [coercion into rings]
instance (priority := 900) numNatCoe [Zero α] : CoeHTCT Num α :=
  ⟨castNum⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Repr PosNum
  body: ⟨fun n _ => repr (n : Nat)⟩

中文:
实例 :
  签名: Repr PosNum
  定义体: ⟨fun n _ => repr (n : Nat)⟩
-/
instance : Repr PosNum :=
  ⟨fun n _ => repr (n : Nat)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Repr Num
  body: ⟨fun n _ => repr (n : Nat)⟩

中文:
实例 :
  签名: Repr Num
  定义体: ⟨fun n _ => repr (n : Nat)⟩
-/
instance : Repr Num :=
  ⟨fun n _ => repr (n : Nat)⟩

end

namespace Num

open PosNum

/--
Definition of `succ'` / `succ'` 的定义

English:
definition succ'
  signature: : Num -> PosNum

中文:
定义 succ'
  签名: : Num -> PosNum
-/
def succ' : Num -> PosNum
  | 0 => 1
  | pos p => succ p

/--
Definition of `succ` / `succ` 的定义

English:
definition succ
  signature: (n : Num)
  body: pos (succ' n)

中文:
定义 succ
  签名: (n : Num)
  定义体: pos (succ' n)
-/
def succ (n : Num) : Num :=
  pos (succ' n)

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: : Num -> Num -> Num

中文:
定义 add
  签名: : Num -> Num -> Num
-/
protected def add : Num -> Num -> Num
  | 0, a => a
  | b, 0 => b
  | pos a, pos b => pos (a + b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add Num
  body: ⟨Num.add⟩

中文:
实例 :
  签名: 加法 Num
  定义体: ⟨Num.add⟩

Depends on / 依赖: Num.add
-/
instance : Add Num :=
  ⟨Num.add⟩

/--
Definition of `bit0` / `bit0` 的定义

English:
definition bit0
  signature: : Num -> Num

中文:
定义 bit0
  签名: : Num -> Num
-/
protected def bit0 : Num -> Num
  | 0 => 0
  | pos n => pos (PosNum.bit0 n)

/--
Definition of `bit1` / `bit1` 的定义

English:
definition bit1
  signature: : Num -> Num

中文:
定义 bit1
  签名: : Num -> Num
-/
protected def bit1 : Num -> Num
  | 0 => 1
  | pos n => pos (PosNum.bit1 n)

/--
Definition of `bit` / `bit` 的定义

English:
definition bit
  signature: (b : Bool)
  body: cond b Num.bit1 Num.bit0

中文:
定义 bit
  签名: (b : 布尔值)
  定义体: cond b Num.bit1 Num.bit0

Depends on / 依赖: Num.bit0, Num.bit1
-/
def bit (b : Bool) : Num -> Num :=
  cond b Num.bit1 Num.bit0

/--
Definition of `size` / `size` 的定义

English:
definition size
  signature: : Num -> Num

中文:
定义 size
  签名: : Num -> Num
-/
def size : Num -> Num
  | 0 => 0
  | pos n => pos (PosNum.size n)

/--
Definition of `natSize` / `natSize` 的定义

English:
definition natSize
  signature: : Num -> Nat

中文:
定义 natSize
  签名: : Num -> 自然数
-/
def natSize : Num -> Nat
  | 0 => 0
  | pos n => PosNum.natSize n

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : Num -> Num -> Num

中文:
定义 mul
  签名: : Num -> Num -> Num
-/
protected def mul : Num -> Num -> Num
  | 0, _ => 0
  | _, 0 => 0
  | pos a, pos b => pos (a * b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul Num
  body: ⟨Num.mul⟩

中文:
实例 :
  签名: 乘法 Num
  定义体: ⟨Num.mul⟩

Depends on / 依赖: Num.mul
-/
instance : Mul Num :=
  ⟨Num.mul⟩

open Ordering

/--
Definition of `cmp` / `cmp` 的定义

English:
definition cmp
  signature: : Num -> Num -> Ordering

中文:
定义 cmp
  签名: : Num -> Num -> Ordering
-/
def cmp : Num -> Num -> Ordering
  | 0, 0 => eq
  | _, 0 => gt
  | 0, _ => lt
  | pos a, pos b => PosNum.cmp a b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT Num
  body: ⟨fun a b => cmp a b = Ordering.lt⟩

中文:
实例 :
  签名: LT Num
  定义体: ⟨fun a b => cmp a b = Ordering.lt⟩

Depends on / 依赖: Ordering, Ordering.lt
-/
instance : LT Num :=
  ⟨fun a b => cmp a b = Ordering.lt⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE Num
  body: ⟨fun a b => ¬b < a⟩

中文:
实例 :
  签名: LE Num
  定义体: ⟨fun a b => ¬b < a⟩
-/
instance : LE Num :=
  ⟨fun a b => ¬b < a⟩

/--
Instance `decidableLT` / 实例 `decidableLT`

English:
instance decidableLT
  signature: : DecidableLT Num

中文:
实例 decidableLT
  签名: : DecidableLT Num
-/
instance decidableLT : DecidableLT Num
  | a, b => by dsimp [LT.lt]; infer_instance

/--
Instance `decidableLE` / 实例 `decidableLE`

English:
instance decidableLE
  signature: : DecidableLE Num

中文:
实例 decidableLE
  签名: : DecidableLE Num
-/
instance decidableLE : DecidableLE Num
  | a, b => by dsimp [LE.le]; infer_instance

/--
Definition of `toZNum` / `toZNum` 的定义

English:
definition toZNum
  signature: : Num -> ZNum

中文:
定义 toZNum
  签名: : Num -> ZNum
-/
def toZNum : Num -> ZNum
  | 0 => 0
  | pos a => ZNum.pos a

/--
Definition of `toZNumNeg` / `toZNumNeg` 的定义

English:
definition toZNumNeg
  signature: : Num -> ZNum

中文:
定义 toZNumNeg
  签名: : Num -> ZNum
-/
def toZNumNeg : Num -> ZNum
  | 0 => 0
  | pos a => ZNum.neg a

/--
Definition of `ofNat'` / `ofNat'` 的定义

English:
definition ofNat'
  signature: : Nat -> Num
  body: Nat.binaryRec 0 (fun b _ => cond b Num.bit1 Num.bit0)

中文:
定义 of自然数'
  签名: : 自然数 -> Num
  定义体: Nat.binaryRec 0 (fun b _ => cond b Num.bit1 Num.bit0)

Depends on / 依赖: Nat.binaryRec, Num.bit0, Num.bit1, binaryRec
-/
def ofNat' : Nat -> Num :=
  Nat.binaryRec 0 (fun b _ => cond b Num.bit1 Num.bit0)

end Num

namespace ZNum

open PosNum

/--
Definition of `zNeg` / `zNeg` 的定义

English:
definition zNeg
  signature: : ZNum -> ZNum

中文:
定义 zNeg
  签名: : ZNum -> ZNum
-/
def zNeg : ZNum -> ZNum
  | 0 => 0
  | pos a => neg a
  | neg a => pos a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg ZNum
  body: ⟨zNeg⟩

中文:
实例 :
  签名: 取负 ZNum
  定义体: ⟨zNeg⟩
-/
instance : Neg ZNum :=
  ⟨zNeg⟩

/--
Definition of `abs` / `abs` 的定义

English:
definition abs
  signature: : ZNum -> Num

中文:
定义 abs
  签名: : ZNum -> Num
-/
def abs : ZNum -> Num
  | 0 => 0
  | pos a => Num.pos a
  | neg a => Num.pos a

/--
Definition of `succ` / `succ` 的定义

English:
definition succ
  signature: : ZNum -> ZNum

中文:
定义 succ
  签名: : ZNum -> ZNum
-/
def succ : ZNum -> ZNum
  | 0 => 1
  | pos a => pos (PosNum.succ a)
  | neg a => (PosNum.pred' a).toZNumNeg

/--
Definition of `pred` / `pred` 的定义

English:
definition pred
  signature: : ZNum -> ZNum

中文:
定义 pred
  签名: : ZNum -> ZNum
-/
def pred : ZNum -> ZNum
  | 0 => neg 1
  | pos a => (PosNum.pred' a).toZNum
  | neg a => neg (PosNum.succ a)

/--
Definition of `bit0` / `bit0` 的定义

English:
definition bit0
  signature: : ZNum -> ZNum

中文:
定义 bit0
  签名: : ZNum -> ZNum
-/
protected def bit0 : ZNum -> ZNum
  | 0 => 0
  | pos n => pos (PosNum.bit0 n)
  | neg n => neg (PosNum.bit0 n)

/--
Definition of `bit1` / `bit1` 的定义

English:
definition bit1
  signature: : ZNum -> ZNum

中文:
定义 bit1
  签名: : ZNum -> ZNum
-/
protected def bit1 : ZNum -> ZNum
  | 0 => 1
  | pos n => pos (PosNum.bit1 n)
  | neg n => neg (Num.casesOn (pred' n) 1 PosNum.bit1)

/--
Definition of `bitm1` / `bitm1` 的定义

English:
definition bitm1
  signature: : ZNum -> ZNum

中文:
定义 bitm1
  签名: : ZNum -> ZNum
-/
protected def bitm1 : ZNum -> ZNum
  | 0 => neg 1
  | pos n => pos (Num.casesOn (pred' n) 1 PosNum.bit1)
  | neg n => neg (PosNum.bit1 n)

/--
Definition of `ofInt'` / `ofInt'` 的定义

English:
definition ofInt'
  signature: : Int -> ZNum

中文:
定义 of整数'
  签名: : 整数 -> ZNum
-/
def ofInt' : Int -> ZNum
  | Int.ofNat n => Num.toZNum (Num.ofNat' n)
  | Int.negSucc n => Num.toZNumNeg (Num.ofNat' (n + 1))

end ZNum

namespace PosNum

open ZNum

/--
Definition of `sub'` / `sub'` 的定义

English:
definition sub'
  signature: : PosNum -> PosNum -> ZNum

中文:
定义 sub'
  签名: : PosNum -> PosNum -> ZNum
-/
def sub' : PosNum -> PosNum -> ZNum
  | a, 1 => (pred' a).toZNum
  | 1, b => (pred' b).toZNumNeg
  | bit0 a, bit0 b => (sub' a b).bit0
  | bit0 a, bit1 b => (sub' a b).bitm1
  | bit1 a, bit0 b => (sub' a b).bit1
  | bit1 a, bit1 b => (sub' a b).bit0

/--
Definition of `ofZNum'` / `ofZNum'` 的定义

English:
definition ofZNum'
  signature: : ZNum -> Option PosNum

中文:
定义 ofZNum'
  签名: : ZNum -> 选项类型 PosNum
-/
def ofZNum' : ZNum -> Option PosNum
  | ZNum.pos p => some p
  | _ => none

/--
Definition of `ofZNum` / `ofZNum` 的定义

English:
definition ofZNum
  signature: : ZNum -> PosNum

中文:
定义 ofZNum
  签名: : ZNum -> PosNum

Depends on / 依赖: ZNum.pos
-/
def ofZNum : ZNum -> PosNum
  | ZNum.pos p => p
  | _ => 1

/--
Definition of `sub` / `sub` 的定义

English:
definition sub
  signature: (a b : PosNum)
  body: match sub' a b with
  | ZNum.pos p => p
  | _ => 1

中文:
定义 sub
  签名: (a b : PosNum)
  定义体: match sub' a b with
  | ZNum.pos p => p
  | _ => 1
-/
protected def sub (a b : PosNum) : PosNum :=
  match sub' a b with
  | ZNum.pos p => p
  | _ => 1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub PosNum
  body: ⟨PosNum.sub⟩

中文:
实例 :
  签名: 减法 PosNum
  定义体: ⟨PosNum.sub⟩

Depends on / 依赖: PosNum, PosNum.sub
-/
instance : Sub PosNum :=
  ⟨PosNum.sub⟩

end PosNum

namespace Num

/--
Definition of `ppred` / `ppred` 的定义

English:
definition ppred
  signature: : Num -> Option Num

中文:
定义 ppred
  签名: : Num -> 选项类型 Num
-/
def ppred : Num -> Option Num
  | 0 => none
  | pos p => some p.pred'

/--
Definition of `pred` / `pred` 的定义

English:
definition pred
  signature: : Num -> Num

中文:
定义 pred
  签名: : Num -> Num
-/
def pred : Num -> Num
  | 0 => 0
  | pos p => p.pred'

/--
Definition of `div2` / `div2` 的定义

English:
definition div2
  signature: : Num -> Num

中文:
定义 div2
  签名: : Num -> Num
-/
def div2 : Num -> Num
  | 0 => 0
  | 1 => 0
  | pos (PosNum.bit0 p) => pos p
  | pos (PosNum.bit1 p) => pos p

/--
Definition of `ofZNum'` / `ofZNum'` 的定义

English:
definition ofZNum'
  signature: : ZNum -> Option Num

中文:
定义 ofZNum'
  签名: : ZNum -> 选项类型 Num
-/
def ofZNum' : ZNum -> Option Num
  | 0 => some 0
  | ZNum.pos p => some (pos p)
  | ZNum.neg _ => none

/--
Definition of `ofZNum` / `ofZNum` 的定义

English:
definition ofZNum
  signature: : ZNum -> Num

中文:
定义 ofZNum
  签名: : ZNum -> Num
-/
def ofZNum : ZNum -> Num
  | ZNum.pos p => pos p
  | _ => 0

/--
Definition of `sub'` / `sub'` 的定义

English:
definition sub'
  signature: : Num -> Num -> ZNum

中文:
定义 sub'
  签名: : Num -> Num -> ZNum
-/
def sub' : Num -> Num -> ZNum
  | 0, 0 => 0
  | pos a, 0 => ZNum.pos a
  | 0, pos b => ZNum.neg b
  | pos a, pos b => a.sub' b

/--
Definition of `psub` / `psub` 的定义

English:
definition psub
  signature: (a b : Num)
  body: ofZNum' (sub' a b)

中文:
定义 psub
  签名: (a b : Num)
  定义体: ofZNum' (sub' a b)

Depends on / 依赖: ofZNum
-/
def psub (a b : Num) : Option Num :=
  ofZNum' (sub' a b)

/--
Definition of `sub` / `sub` 的定义

English:
definition sub
  signature: (a b : Num)
  body: ofZNum (sub' a b)

中文:
定义 sub
  签名: (a b : Num)
  定义体: ofZNum (sub' a b)
-/
protected def sub (a b : Num) : Num :=
  ofZNum (sub' a b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub Num
  body: ⟨Num.sub⟩

中文:
实例 :
  签名: 减法 Num
  定义体: ⟨Num.sub⟩

Depends on / 依赖: Num.sub
-/
instance : Sub Num :=
  ⟨Num.sub⟩

end Num

namespace ZNum

open PosNum

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: : ZNum -> ZNum -> ZNum

中文:
定义 add
  签名: : ZNum -> ZNum -> ZNum
-/
protected def add : ZNum -> ZNum -> ZNum
  | 0, a => a
  | b, 0 => b
  | pos a, pos b => pos (a + b)
  | pos a, neg b => sub' a b
  | neg a, pos b => sub' b a
  | neg a, neg b => neg (a + b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add ZNum
  body: ⟨ZNum.add⟩

中文:
实例 :
  签名: 加法 ZNum
  定义体: ⟨ZNum.add⟩

Depends on / 依赖: ZNum.add
-/
instance : Add ZNum :=
  ⟨ZNum.add⟩

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : ZNum -> ZNum -> ZNum

中文:
定义 mul
  签名: : ZNum -> ZNum -> ZNum
-/
protected def mul : ZNum -> ZNum -> ZNum
  | 0, _ => 0
  | _, 0 => 0
  | pos a, pos b => pos (a * b)
  | pos a, neg b => neg (a * b)
  | neg a, pos b => neg (a * b)
  | neg a, neg b => pos (a * b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul ZNum
  body: ⟨ZNum.mul⟩

中文:
实例 :
  签名: 乘法 ZNum
  定义体: ⟨ZNum.mul⟩

Depends on / 依赖: ZNum.mul
-/
instance : Mul ZNum :=
  ⟨ZNum.mul⟩

open Ordering

/--
Definition of `cmp` / `cmp` 的定义

English:
definition cmp
  signature: : ZNum -> ZNum -> Ordering

中文:
定义 cmp
  签名: : ZNum -> ZNum -> Ordering
-/
def cmp : ZNum -> ZNum -> Ordering
  | 0, 0 => eq
  | pos a, pos b => PosNum.cmp a b
  | neg a, neg b => PosNum.cmp b a
  | pos _, _ => gt
  | neg _, _ => lt
  | _, pos _ => lt
  | _, neg _ => gt

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT ZNum
  body: ⟨fun a b => cmp a b = Ordering.lt⟩

中文:
实例 :
  签名: LT ZNum
  定义体: ⟨fun a b => cmp a b = Ordering.lt⟩

Depends on / 依赖: Ordering, Ordering.lt
-/
instance : LT ZNum :=
  ⟨fun a b => cmp a b = Ordering.lt⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE ZNum
  body: ⟨fun a b => ¬b < a⟩

中文:
实例 :
  签名: LE ZNum
  定义体: ⟨fun a b => ¬b < a⟩
-/
instance : LE ZNum :=
  ⟨fun a b => ¬b < a⟩

/--
Instance `decidableLT` / 实例 `decidableLT`

English:
instance decidableLT
  signature: : DecidableLT ZNum
  body: inferInstanceAs DecidableRel fun a b => cmp a b = Ordering.lt

中文:
实例 decidableLT
  签名: : DecidableLT ZNum
  定义体: inferInstanceAs DecidableRel fun a b => cmp a b = Ordering.lt

Depends on / 依赖: DecidableRel, Ordering, Ordering.lt
-/
instance decidableLT : DecidableLT ZNum :=
inferInstanceAs DecidableRel fun a b => cmp a b = Ordering.lt

/--
Instance `decidableLE` / 实例 `decidableLE`

English:
instance decidableLE
  signature: : DecidableLE ZNum
  body: inferInstanceAs DecidableRel fun a b => ¬b < a

中文:
实例 decidableLE
  签名: : DecidableLE ZNum
  定义体: inferInstanceAs DecidableRel fun a b => ¬b < a

Depends on / 依赖: DecidableRel
-/
instance decidableLE : DecidableLE ZNum :=
inferInstanceAs DecidableRel fun a b => ¬b < a

end ZNum

namespace PosNum

/--
Definition of `divModAux` / `divModAux` 的定义

English:
definition divModAux
  signature: (d : PosNum) (q r : Num)
  body: match Num.ofZNum' (Num.sub' r (Num.pos d)) with
  | some r' => (Num.bit1 q, r')
  | none => (Num.bit0 q, r)

中文:
定义 divModAux
  签名: (d : PosNum) (q r : Num)
  定义体: match Num.ofZNum' (Num.sub' r (Num.pos d)) with
  | some r' => (Num.bit1 q, r')
  | none => (Num.bit0 q, r)

Depends on / 依赖: Num.bit0, Num.bit1, Num.ofZNum, Num.pos, Num.sub, ofZNum
-/
def divModAux (d : PosNum) (q r : Num) : Num × Num :=
  match Num.ofZNum' (Num.sub' r (Num.pos d)) with
  | some r' => (Num.bit1 q, r')
  | none => (Num.bit0 q, r)

/--
Definition of `divMod` / `divMod` 的定义

English:
definition divMod
  signature: (d : PosNum)
  body: divMod d n
    divModAux d q (Num.bit0 r₁)
  | bit1 n =>
    let (q, r₁) := divMod d n
    divModAux d q (Num.bit1 r₁)
  | 1 => divModAux d 0 1

中文:
定义 divMod
  签名: (d : PosNum)
  定义体: divMod d n
    divModAux d q (Num.bit0 r₁)
  | bit1 n =>
    let (q, r₁) := divMod d n
    divModAux d q (Num.bit1 r₁)
  | 1 => divModAux d 0 1

Depends on / 依赖: divMod
-/
def divMod (d : PosNum) : PosNum -> Num × Num
  | bit0 n =>
    let (q, r₁) := divMod d n
    divModAux d q (Num.bit0 r₁)
  | bit1 n =>
    let (q, r₁) := divMod d n
    divModAux d q (Num.bit1 r₁)
  | 1 => divModAux d 0 1

/--
Definition of `div'` / `div'` 的定义

English:
definition div'
  signature: (n d : PosNum)
  body: (divMod d n).1

中文:
定义 div'
  签名: (n d : PosNum)
  定义体: (divMod d n).1

Depends on / 依赖: divMod
-/
def div' (n d : PosNum) : Num :=
  (divMod d n).1

/--
Definition of `mod'` / `mod'` 的定义

English:
definition mod'
  signature: (n d : PosNum)
  body: (divMod d n).2

中文:
定义 mod'
  签名: (n d : PosNum)
  定义体: (divMod d n).2

Depends on / 依赖: divMod
-/
def mod' (n d : PosNum) : Num :=
  (divMod d n).2

/--
Definition of `sqrtAux1` / `sqrtAux1` 的定义

English:
definition sqrtAux1
  signature: (b : PosNum) (r n : Num)
  body: match Num.ofZNum' (n.sub' (r + Num.pos b)) with
  | some n' => (r.div2 + Num.pos b, n')
  | none => (r.div2, n)

中文:
定义 sqrtAux1
  签名: (b : PosNum) (r n : Num)
  定义体: match Num.ofZNum' (n.sub' (r + Num.pos b)) with
  | some n' => (r.div2 + Num.pos b, n')
  | none => (r.div2, n)
-/
private def sqrtAux1 (b : PosNum) (r n : Num) : Num × Num :=
  match Num.ofZNum' (n.sub' (r + Num.pos b)) with
  | some n' => (r.div2 + Num.pos b, n')
  | none => (r.div2, n)

/--
Definition of `sqrtAux` / `sqrtAux` 的定义

English:
definition sqrtAux
  signature: : PosNum -> Num -> Num -> Num
  body: sqrtAux1 b r n; sqrtAux b' r' n'
  | b@(bit1 b') => fun r n => let (r', n') := sqrtAux1 b r n; sqrtAux b' r' n'
  | 1 => fun r n => (sqrtAux1 1 r n).1

中文:
定义 sqrtAux
  签名: : PosNum -> Num -> Num -> Num
  定义体: sqrtAux1 b r n; sqrtAux b' r' n'
  | b@(bit1 b') => fun r n => let (r', n') := sqrtAux1 b r n; sqrtAux b' r' n'
  | 1 => fun r n => (sqrtAux1 1 r n).1
-/
private def sqrtAux : PosNum -> Num -> Num -> Num
  | b@(bit0 b') => fun r n => let (r', n') := sqrtAux1 b r n; sqrtAux b' r' n'
  | b@(bit1 b') => fun r n => let (r', n') := sqrtAux1 b r n; sqrtAux b' r' n'
  | 1 => fun r n => (sqrtAux1 1 r n).1

end PosNum

namespace Num

/--
Definition of `div` / `div` 的定义

English:
definition div
  signature: : Num -> Num -> Num

中文:
定义 div
  签名: : Num -> Num -> Num
-/
def div : Num -> Num -> Num
  | 0, _ => 0
  | _, 0 => 0
  | pos n, pos d => PosNum.div' n d

/--
Definition of `mod` / `mod` 的定义

English:
definition mod
  signature: : Num -> Num -> Num

中文:
定义 mod
  签名: : Num -> Num -> Num
-/
def mod : Num -> Num -> Num
  | 0, _ => 0
  | n, 0 => n
  | pos n, pos d => PosNum.mod' n d

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div Num
  body: ⟨Num.div⟩

中文:
实例 :
  签名: 除法 Num
  定义体: ⟨Num.div⟩

Depends on / 依赖: Num.div
-/
instance : Div Num :=
  ⟨Num.div⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mod Num
  body: ⟨Num.mod⟩

中文:
实例 :
  签名: 取模 Num
  定义体: ⟨Num.mod⟩

Depends on / 依赖: Num.mod
-/
instance : Mod Num :=
  ⟨Num.mod⟩

/--
Definition of `gcdAux` / `gcdAux` 的定义

English:
definition gcdAux
  signature: : Nat -> Num -> Num -> Num

中文:
定义 gcdAux
  签名: : 自然数 -> Num -> Num -> Num
-/
def gcdAux : Nat -> Num -> Num -> Num
  | 0, _, b => b
  | Nat.succ _, 0, b => b
  | Nat.succ n, a, b => gcdAux n (b % a) a

/--
Definition of `gcd` / `gcd` 的定义

English:
definition gcd
  signature: (a b : Num)
  body: if a <= b then gcdAux (a.natSize + b.natSize) a b else gcdAux (b.natSize + a.natSize) b a

中文:
定义 最大公约数
  签名: (a b : Num)
  定义体: if a <= b then gcdAux (a.natSize + b.natSize) a b else gcdAux (b.natSize + a.natSize) b a

Depends on / 依赖: a.natSize, b.natSize, gcdAux, natSize
-/
def gcd (a b : Num) : Num :=
  if a <= b then gcdAux (a.natSize + b.natSize) a b else gcdAux (b.natSize + a.natSize) b a

end Num

namespace ZNum

/--
Definition of `div` / `div` 的定义

English:
definition div
  signature: : ZNum -> ZNum -> ZNum

中文:
定义 div
  签名: : ZNum -> ZNum -> ZNum
-/
def div : ZNum -> ZNum -> ZNum
  | 0, _ => 0
  | _, 0 => 0
  | pos n, pos d => Num.toZNum (PosNum.div' n d)
  | pos n, neg d => Num.toZNumNeg (PosNum.div' n d)
  | neg n, pos d => neg (PosNum.pred' n / Num.pos d).succ'
  | neg n, neg d => pos (PosNum.pred' n / Num.pos d).succ'

/--
Definition of `mod` / `mod` 的定义

English:
definition mod
  signature: : ZNum -> ZNum -> ZNum

中文:
定义 mod
  签名: : ZNum -> ZNum -> ZNum
-/
def mod : ZNum -> ZNum -> ZNum
  | 0, _ => 0
  | pos n, d => Num.toZNum (Num.pos n % d.abs)
  | neg n, d => d.abs.sub' (PosNum.pred' n % d.abs).succ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div ZNum
  body: ⟨ZNum.div⟩

中文:
实例 :
  签名: 除法 ZNum
  定义体: ⟨ZNum.div⟩

Depends on / 依赖: ZNum.div
-/
instance : Div ZNum :=
  ⟨ZNum.div⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mod ZNum
  body: ⟨ZNum.mod⟩

中文:
实例 :
  签名: 取模 ZNum
  定义体: ⟨ZNum.mod⟩

Depends on / 依赖: ZNum.mod
-/
instance : Mod ZNum :=
  ⟨ZNum.mod⟩

/--
Definition of `gcd` / `gcd` 的定义

English:
definition gcd
  signature: (a b : ZNum)
  body: a.abs.gcd b.abs

中文:
定义 最大公约数
  签名: (a b : ZNum)
  定义体: a.abs.gcd b.abs

Depends on / 依赖: a.abs.gcd, b.abs
-/
def gcd (a b : ZNum) : Num :=
  a.abs.gcd b.abs

end ZNum

section
variable {α : Type*} [Zero α] [One α] [Add α] [Neg α]

/-- `castZNum` casts a `ZNum` into any type which has `0`, `1`, `+` and `neg` -/
@[coe]
/--
Definition of `castZNum` / `castZNum` 的定义

English:
definition castZNum
  signature: : ZNum -> α

中文:
定义 castZNum
  签名: : ZNum -> α
-/
def castZNum : ZNum -> α
  | 0 => 0
  | ZNum.pos p => p
  | ZNum.neg p => -p

-- see Note [coercion into rings]
instance (priority := 900) znumCoe : CoeHTCT ZNum α :=
  ⟨castZNum⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Repr ZNum
  body: ⟨fun n _ => repr (n : Int)⟩

中文:
实例 :
  签名: Repr ZNum
  定义体: ⟨fun n _ => repr (n : Int)⟩
-/
instance : Repr ZNum :=
  ⟨fun n _ => repr (n : Int)⟩

end
