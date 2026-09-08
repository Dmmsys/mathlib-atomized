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

/-- Typeclass for expressing that the `0` of a type is less or equal to its `1`. -/
/-
**ZeroLEOneClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [Zero α] → [One α] → [LE α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for expressing that the `0` of a type is less or equal to its `1`.
-/
class ZeroLEOneClass (α : Type*) [Zero α] [One α] [LE α] : Prop where
  /-- Zero is less than or equal to one. -/
  zero_le_one : (0 : α) ≤ 1

/-- `zero_le_one` with the type argument implicit. -/
/-
**zero_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : LE α] [ZeroLEO
neClass α], 0 ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroLEOneClass.zero_le_one`：∀ {α : Type u_2} {inst : Zero α} {inst_1 : O
ne α} {inst_2 : LE α} [self : ZeroLEOneClass α], 0 ≤ 1

--- 原说明 ---
`zero_le_one` with the type argument implicit.
-/
@[simp] lemma zero_le_one [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  ZeroLEOneClass.zero_le_one
/-
**ZeroLEOneClass.factZeroLeOne** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ZeroLEOneClass.factZeroLeOne [Zero α] [One α] [LE α] [ZeroLEOneClass α] : 
Fact ((0 : α) <= 1) where out
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroLEOneClass.zero_le_one`：∀ {α : Type u_2} {inst : Zero α} {inst_1 : O
ne α} {inst_2 : LE α} [self : ZeroLEOneClass α], 0 ≤ 1
-/
instance ZeroLEOneClass.factZeroLeOne [Zero α] [One α] [LE α] [ZeroLEOneClass α] :
    Fact ((0 : α) ≤ 1) where
  out := zero_le_one

/-- `zero_le_one` with the type argument explicit. -/
/-
**zero_le_one'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) <= 1
参数：α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1

--- 原说明 ---
`zero_le_one` with the type argument explicit.
-/
lemma zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  zero_le_one
/-
**Prod.instZeroLEOneClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instZeroLEOneClass {R S : Type*} [Zero R] [One R] [LE R] [ZeroLEOneCl
ass R] [Zero S] [One S] [LE S] [ZeroLEOneClass S] : ZeroLEOneClass (R × S)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
instance Prod.instZeroLEOneClass {R S : Type*} [Zero R] [One R] [LE R] [ZeroLEOneClass R]
    [Zero S] [One S] [LE S] [ZeroLEOneClass S] : ZeroLEOneClass (R × S) :=
  ⟨⟨zero_le_one, zero_le_one⟩⟩
/-
**Pi.instZeroLEOneClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instZeroLEOneClass {ι : Type*} {R : ι -> Type*} [forall i, Zero (R i)] 
[forall i, One (R i)] [forall i, LE (R i)] [forall i, ZeroLEOneClass (R i)] : Ze
roLEOneClass (forall i, R i)
参数：R i；R i；R i；R i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
instance Pi.instZeroLEOneClass {ι : Type*} {R : ι → Type*} [∀ i, Zero (R i)] [∀ i, One (R i)]
    [∀ i, LE (R i)] [∀ i, ZeroLEOneClass (R i)] : ZeroLEOneClass (∀ i, R i) :=
  ⟨fun _ ↦ zero_le_one⟩

section
variable [Zero α] [One α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

/-- See `zero_lt_one'` for a version with the type explicit. -/
/-
**zero_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : PartialOrder α
] [ZeroLEOneClass α] [NeZero 1], 0 < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `NeZero.ne'`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], 0 ≠
 n

--- 原说明 ---
See `zero_lt_one'` for a version with the type explicit.
-/
@[simp] lemma zero_lt_one : (0 : α) < 1 := zero_le_one.lt_of_ne (NeZero.ne' 1)
/-
**ZeroLEOneClass.factZeroLtOne** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ZeroLEOneClass.factZeroLtOne : Fact ((0 : α) < 1) where out
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1

--- 原说明 ---
See `zero_lt_one'` for a version with the type explicit.
-/
instance ZeroLEOneClass.factZeroLtOne : Fact ((0 : α) < 1) where
  out := zero_lt_one

variable (α)

/-- See `zero_lt_one` for a version with the type implicit. -/
/-
**zero_lt_one'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_lt_one' : (0 : α) < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1

--- 原说明 ---
See `zero_lt_one` for a version with the type implicit.
-/
lemma zero_lt_one' : (0 : α) < 1 := zero_lt_one

end

alias one_pos := zero_lt_one

/-
**Nat.instZeroLEOneClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nat.instZeroLEOneClass : ZeroLEOneClass Nat
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.zero_lt_one`：0 < 1
-/
instance Nat.instZeroLEOneClass : ZeroLEOneClass Nat := ⟨Nat.le_of_lt Nat.zero_lt_one⟩
/-
**Int.instZeroLEOneClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.instZeroLEOneClass : ZeroLEOneClass Int
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le_of_lt`：∀ {a b : ℤ}, a < b → a ≤ b
· 使用定理 `Int.zero_lt_one`：0 < 1
-/
instance Int.instZeroLEOneClass : ZeroLEOneClass Int := ⟨Int.le_of_lt Int.zero_lt_one⟩
/-
**Rat.instZeroLEOneClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Rat.instZeroLEOneClass : ZeroLEOneClass Rat
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
instance Rat.instZeroLEOneClass : ZeroLEOneClass Rat := ⟨by decide⟩
