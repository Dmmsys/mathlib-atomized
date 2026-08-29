/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Order.Basic

/-!
# Typeclass expressing `0 ≤ 1`.
-/

public section

variable {α : Type*}

open Function

/--
Definition of `ZeroLEOneClass` / `ZeroLEOneClass` 的定义

English:
class ZeroLEOneClass
  parameters: (α : Type*) [Zero α] [One α] [LE α]
  axioms and operations (1):
    - zero_le_one : (0 : α) <= 1

中文:
类 ZeroLEOneClass
  参数: (α : 类型) [Zero α] [One α] [LE α]
  公理与运算 (1 个):
    - zero_le_one : (0 : α) <= 1
-/
class ZeroLEOneClass (α : Type*) [Zero α] [One α] [LE α] : Prop where
  /-- Zero is less than or equal to one. -/
  zero_le_one : (0 : α) <= 1

/--
lemma `zero_le_one` / 引理 `zero_le_one`

English:
lemma zero_le_one
  given: [Zero α] [One α] [LE α] [ZeroLEOneClass α]
  statement: (0 : α) <= 1
  proof: ZeroLEOneClass.zero_le_one

中文:
引理 zero_le_one
  条件: [Zero α] [One α] [LE α] [ZeroLEOneClass α]
  结论: (0 : α) <= 1
  证明: ZeroLEOneClass.zero_le_one
-/
@[simp] lemma zero_le_one [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) <= 1 :=
  ZeroLEOneClass.zero_le_one

/--
Instance `ZeroLEOneClass.factZeroLeOne` / 实例 `ZeroLEOneClass.factZeroLeOne`

English:
instance ZeroLEOneClass.factZeroLeOne
  signature: [Zero α] [One α] [LE α] [ZeroLEOneClass α]
  body: zero_le_one

中文:
实例 ZeroLEOneClass.factZeroLeOne
  签名: [Zero α] [One α] [LE α] [ZeroLEOneClass α]
  定义体: zero_le_one

Depends on / 依赖: zero_le_one
-/
instance ZeroLEOneClass.factZeroLeOne [Zero α] [One α] [LE α] [ZeroLEOneClass α] :
    Fact ((0 : α) <= 1) where
  out := zero_le_one

/--
lemma `zero_le_one'` / 引理 `zero_le_one'`

English:
lemma zero_le_one'
  given: (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α]
  statement: (0 : α) <= 1
  proof: zero_le_one

中文:
引理 zero_le_one'
  条件: (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α]
  结论: (0 : α) <= 1
  证明: zero_le_one

Depends on / 依赖: zero_le_one
-/
lemma zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) <= 1 :=
  zero_le_one

/--
Instance `Prod.instZeroLEOneClass` / 实例 `Prod.instZeroLEOneClass`

English:
instance Prod.instZeroLEOneClass
  signature: {R S : Type*} [Zero R] [One R] [LE R] [ZeroLEOneClass R]
  body: ⟨⟨zero_le_one, zero_le_one⟩⟩

中文:
实例 Prod.instZeroLEOneClass
  签名: {R S : 类型} [Zero R] [One R] [LE R] [ZeroLEOneClass R]
  定义体: ⟨⟨zero_le_one, zero_le_one⟩⟩

Depends on / 依赖: zero_le_one
-/
instance Prod.instZeroLEOneClass {R S : Type*} [Zero R] [One R] [LE R] [ZeroLEOneClass R]
    [Zero S] [One S] [LE S] [ZeroLEOneClass S] : ZeroLEOneClass (R × S) :=
  ⟨⟨zero_le_one, zero_le_one⟩⟩

/--
Instance `Pi.instZeroLEOneClass` / 实例 `Pi.instZeroLEOneClass`

English:
instance Pi.instZeroLEOneClass
  signature: {ι : Type*} {R : ι -> Type*} [forall i, Zero (R i)] [forall i, One (R i)]
  body: ⟨fun _ => zero_le_one⟩

中文:
实例 Pi.instZeroLEOneClass
  签名: {ι : 类型} {R : ι -> 类型} [对任意 i, Zero (R i)] [对任意 i, One (R i)]
  定义体: ⟨fun _ => zero_le_one⟩

Depends on / 依赖: zero_le_one
-/
instance Pi.instZeroLEOneClass {ι : Type*} {R : ι -> Type*} [forall i, Zero (R i)] [forall i, One (R i)]
    [forall i, LE (R i)] [forall i, ZeroLEOneClass (R i)] : ZeroLEOneClass (forall i, R i) :=
  ⟨fun _ => zero_le_one⟩

section
variable [Zero α] [One α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

/--
lemma `zero_lt_one` / 引理 `zero_lt_one`

English:
lemma zero_lt_one
  statement: (0 : α) < 1
  proof: zero_le_one.lt_of_ne (NeZero.ne' 1)

中文:
引理 zero_lt_one
  结论: (0 : α) < 1
  证明: zero_le_one.lt_of_ne (NeZero.ne' 1)
-/
@[simp] lemma zero_lt_one : (0 : α) < 1 := zero_le_one.lt_of_ne (NeZero.ne' 1)

/--
Instance `ZeroLEOneClass.factZeroLtOne` / 实例 `ZeroLEOneClass.factZeroLtOne`

English:
instance ZeroLEOneClass.factZeroLtOne
  signature: : Fact ((0 : α) < 1) where
  body: zero_lt_one

中文:
实例 ZeroLEOneClass.factZeroLtOne
  签名: : Fact ((0 : α) < 1) where
  定义体: zero_lt_one

Depends on / 依赖: zero_lt_one
-/
instance ZeroLEOneClass.factZeroLtOne : Fact ((0 : α) < 1) where
  out := zero_lt_one

variable (α)

/--
lemma `zero_lt_one'` / 引理 `zero_lt_one'`

English:
lemma zero_lt_one'
  statement: (0 : α) < 1
  proof: zero_lt_one

中文:
引理 zero_lt_one'
  结论: (0 : α) < 1
  证明: zero_lt_one

Depends on / 依赖: zero_lt_one
-/
lemma zero_lt_one' : (0 : α) < 1 := zero_lt_one

end

alias one_pos := zero_lt_one

/--
Instance `Nat.instZeroLEOneClass` / 实例 `Nat.instZeroLEOneClass`

English:
instance Nat.instZeroLEOneClass
  signature: : ZeroLEOneClass Nat
  body: ⟨Nat.le_of_lt Nat.zero_lt_one⟩

中文:
实例 Nat.instZeroLEOneClass
  签名: : ZeroLEOneClass 自然数
  定义体: ⟨Nat.le_of_lt Nat.zero_lt_one⟩

Depends on / 依赖: Nat.le_of_lt, Nat.zero_lt_one, le_of_lt, zero_lt_one
-/
instance Nat.instZeroLEOneClass : ZeroLEOneClass Nat := ⟨Nat.le_of_lt Nat.zero_lt_one⟩
/--
Instance `Int.instZeroLEOneClass` / 实例 `Int.instZeroLEOneClass`

English:
instance Int.instZeroLEOneClass
  signature: : ZeroLEOneClass Int
  body: ⟨Int.le_of_lt Int.zero_lt_one⟩

中文:
实例 Int.instZeroLEOneClass
  签名: : ZeroLEOneClass 整数
  定义体: ⟨Int.le_of_lt Int.zero_lt_one⟩

Depends on / 依赖: Int.le_of_lt, Int.zero_lt_one, le_of_lt, zero_lt_one
-/
instance Int.instZeroLEOneClass : ZeroLEOneClass Int := ⟨Int.le_of_lt Int.zero_lt_one⟩
/--
Instance `Rat.instZeroLEOneClass` / 实例 `Rat.instZeroLEOneClass`

English:
instance Rat.instZeroLEOneClass
  signature: : ZeroLEOneClass Rat
  body: ⟨by decide⟩

中文:
实例 Rat.instZeroLEOneClass
  签名: : ZeroLEOneClass Rat
  定义体: ⟨by decide⟩
-/
instance Rat.instZeroLEOneClass : ZeroLEOneClass Rat := ⟨by decide⟩
