/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Yury Kudryashov
-/
module

public import Mathlib.Data.Nat.Notation

/-! # Definition and notation for positive natural numbers -/

@[expose] public section

/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
/-
**PNat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PNat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored.
-/
def PNat := { n : ℕ // 0 < n } deriving DecidableEq

@[inherit_doc]
notation "ℕ+" => PNat

/-- The underlying natural number -/
@[coe]
/-
**PNat.val** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PNat.val : Nat+ -> Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying natural number
-/
def PNat.val : ℕ+ → ℕ := Subtype.val
/-
**coePNatNat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：coePNatNat : Coe Nat+ Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coePNatNat : Coe ℕ+ ℕ :=
  ⟨PNat.val⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Repr ℕ+ :=
  ⟨fun n n' => reprPrec n.1 n'⟩
