/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.ModelTheory.Semantics

/-!
# Presburger arithmetic

This file defines the first-order language of Presburger arithmetic as (0,1,+).

## Main Definitions

- `FirstOrder.Language.presburger`: the language of Presburger arithmetic.

## TODO

- Generalize `presburger.sum` (maybe also `NatCast` and `SMul`) for classes like
  `FirstOrder.Language.IsOrdered`.
- Define the theory of Presburger arithmetic and prove its properties (quantifier elimination,
  completeness, etc).
-/

@[expose] public section

variable {α : Type*}

namespace FirstOrder

/--
Inductive type `presburgerFunc` / 归纳类型 `presburgerFunc`

English:
inductive presburgerFunc
  parameters: : Nat -> Type
  constructors (3):
    - zero: presburgerFunc 0
    - one: presburgerFunc 0
    - add: presburgerFunc 2

中文:
归纳类型 presburgerFunc
  参数: : 自然数 -> 类型
  构造子 (3 个):
    - zero: presburgerFunc 0
    - one: presburgerFunc 0
    - add: presburgerFunc 2
-/
inductive presburgerFunc : Nat -> Type
  | zero : presburgerFunc 0
  | one : presburgerFunc 0
  | add : presburgerFunc 2
  deriving DecidableEq

/--
Definition of `Language.presburger` / `Language.presburger` 的定义

English:
definition Language.presburger
  signature: : Language
  body: { Functions := presburgerFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

中文:
定义 Language.presburger
  签名: : Language
  定义体: { Functions := presburgerFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

Depends on / 依赖: Functions, Relations, presburgerFunc
-/
def Language.presburger : Language :=
  { Functions := presburgerFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

namespace Language.presburger

variable {t t₁ t₂ : presburger.Term α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (presburger.Term α)
  body: Constants.term .zero

中文:
实例 :
  签名: 零 (presburger.项 α)
  定义体: Constants.term .zero

Depends on / 依赖: Constants, Constants.term
-/
instance : Zero (presburger.Term α) where
  zero := Constants.term .zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (presburger.Term α)
  body: Constants.term .one

中文:
实例 :
  签名: 幺 (presburger.项 α)
  定义体: Constants.term .one

Depends on / 依赖: Constants, Constants.term
-/
instance : One (presburger.Term α) where
  one := Constants.term .one

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (presburger.Term α)
  body: Functions.apply₂ .add

中文:
实例 :
  签名: 加法 (presburger.项 α)
  定义体: Functions.apply₂ .add

Depends on / 依赖: Functions, Functions.apply
-/
instance : Add (presburger.Term α) where
  add := Functions.apply₂ .add

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (presburger.Term α)
  body: Nat.unaryCast

中文:
实例 :
  签名: 自然数嵌入 (presburger.项 α)
  定义体: Nat.unaryCast

Depends on / 依赖: Nat.unaryCast, unaryCast
-/
instance : NatCast (presburger.Term α) where
  natCast := Nat.unaryCast

/--
theorem `natCast_zero` / 定理 `natCast_zero`

English:
theorem natCast_zero
  statement: (0 : Nat) = (0 : presburger.Term α)
  proof: rfl

中文:
定理 natCast_zero
  结论: (0 : 自然数) = (0 : presburger.项 α)
  证明: rfl
-/
@[simp, norm_cast] theorem natCast_zero : (0 : Nat) = (0 : presburger.Term α) := rfl

/--
theorem `natCast_succ` / 定理 `natCast_succ`

English:
theorem natCast_succ
  given: (n : Nat)
  statement: (n + 1 : Nat) = (n : presburger.Term α) + 1
  proof: rfl

中文:
定理 natCast_succ
  条件: (n : 自然数)
  结论: (n + 1 : 自然数) = (n : presburger.项 α) + 1
  证明: rfl
-/
@[simp, norm_cast] theorem natCast_succ (n : Nat) : (n + 1 : Nat) = (n : presburger.Term α) + 1 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat (presburger.Term α)
  body: nsmulRec

中文:
实例 :
  签名: 标量乘法 自然数 (presburger.项 α)
  定义体: nsmulRec

Depends on / 依赖: nsmulRec
-/
instance : SMul Nat (presburger.Term α) where
  smul := nsmulRec

/--
theorem `zero_nsmul` / 定理 `zero_nsmul`

English:
theorem zero_nsmul
  statement: 0 • t = 0
  proof: rfl

中文:
定理 zero_nsmul
  结论: 0 • t = 0
  证明: rfl
-/
@[simp] theorem zero_nsmul : 0 • t = 0 := rfl

/--
theorem `succ_nsmul` / 定理 `succ_nsmul`

English:
theorem succ_nsmul
  given: {n : Nat}
  statement: (n + 1) • t = n • t + t
  proof: rfl

中文:
定理 succ_nsmul
  条件: {n : 自然数}
  结论: (n + 1) • t = n • t + t
  证明: rfl
-/
@[simp] theorem succ_nsmul {n : Nat} : (n + 1) • t = n • t + t := rfl

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: {β : Type*} (s : Finset β) (f : β -> presburger.Term α)
  body: (s.toList.map f).sum

中文:
定义 求和
  签名: {β : 类型} (s : 有限集 β) (f : β -> presburger.项 α)
  定义体: (s.toList.map f).sum

Depends on / 依赖: s.toList.map, toList
-/
noncomputable def sum {β : Type*} (s : Finset β) (f : β -> presburger.Term α) : presburger.Term α :=
  (s.toList.map f).sum

variable {M : Type*} {v : α -> M}

section

variable [Zero M] [One M] [Add M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: presburger.Structure M

中文:
实例 :
  签名: presburger.结构 M
-/
instance : presburger.Structure M where
  funMap
  | .zero, _ => 0
  | .one, v => 1
  | .add, v => v 0 + v 1

/--
theorem `funMap_zero` / 定理 `funMap_zero`

English:
theorem funMap_zero
  given: {v}
  proof: rfl

中文:
定理 funMap_zero
  条件: {v}
  证明: rfl
-/
@[simp] theorem funMap_zero {v} :
    Structure.funMap (L := presburger) (M := M) presburgerFunc.zero v = 0 := rfl

/--
theorem `funMap_one` / 定理 `funMap_one`

English:
theorem funMap_one
  given: {v}
  proof: rfl

中文:
定理 funMap_one
  条件: {v}
  证明: rfl
-/
@[simp] theorem funMap_one {v} :
    Structure.funMap (L := presburger) (M := M) presburgerFunc.one v = 1 := rfl

/--
theorem `funMap_add` / 定理 `funMap_add`

English:
theorem funMap_add
  given: {v}
  proof: rfl

中文:
定理 funMap_add
  条件: {v}
  证明: rfl
-/
@[simp] theorem funMap_add {v} :
    Structure.funMap (L := presburger) (M := M) presburgerFunc.add v = v 0 + v 1 := rfl

/--
theorem `realize_zero` / 定理 `realize_zero`

English:
theorem realize_zero
  statement: Term.realize v (0 : presburger.Term α) = 0
  proof: rfl

中文:
定理 realize_zero
  结论: 项.realize v (0 : presburger.项 α) = 0
  证明: rfl
-/
@[simp] theorem realize_zero : Term.realize v (0 : presburger.Term α) = 0 := rfl

/--
theorem `realize_one` / 定理 `realize_one`

English:
theorem realize_one
  statement: Term.realize v (1 : presburger.Term α) = 1
  proof: rfl

中文:
定理 realize_one
  结论: 项.realize v (1 : presburger.项 α) = 1
  证明: rfl
-/
@[simp] theorem realize_one : Term.realize v (1 : presburger.Term α) = 1 := rfl

/--
theorem `realize_add` / 定理 `realize_add`

English:
theorem realize_add
  proof: rfl

中文:
定理 realize_add
  证明: rfl
-/
@[simp] theorem realize_add :
    Term.realize v (t₁ + t₂) = Term.realize v t₁ + Term.realize v t₂ := rfl

end

/--
theorem `realize_natCast` / 定理 `realize_natCast`

English:
theorem realize_natCast
  given: [AddMonoidWithOne M] {n : Nat}
  proof: by
  induction n with simp [*]

中文:
定理 realize_natCast
  条件: [加法带幺幺半群 M] {n : 自然数}
  证明: by
  induction n with simp [*]
-/
@[simp] theorem realize_natCast [AddMonoidWithOne M] {n : Nat} :
    Term.realize v (n : presburger.Term α) = n := by
  induction n with simp [*]

/--
theorem `realize_nsmul` / 定理 `realize_nsmul`

English:
theorem realize_nsmul
  given: [AddMonoidWithOne M] {n : Nat}
  proof: by
  induction n with simp [*, add_nsmul]

中文:
定理 realize_nsmul
  条件: [加法带幺幺半群 M] {n : 自然数}
  证明: by
  induction n with simp [*, add_nsmul]
-/
@[simp] theorem realize_nsmul [AddMonoidWithOne M] {n : Nat} :
    Term.realize v (n • t) = n • Term.realize v t := by
  induction n with simp [*, add_nsmul]

/--
theorem `realize_sum` / 定理 `realize_sum`

English:
theorem realize_sum
  statement: [AddCommMonoidWithOne M]
  proof: by
  classical
  simp only [sum]
  conv => rhs; rw [← s.toList_toFinset, List.sum_toFinset _ s.nodup_toList]
  generalize s.toList = l
  induction l with simp [*]

中文:
定理 realize_sum
  结论: [加法交换带幺幺半群 M]
  证明: by
  classical
  simp only [sum]
  conv => rhs; rw [← s.toList_toFinset, List.sum_toFinset _ s.nodup_toList]
  generalize s.toList = l
  induction l with simp [*]
-/
@[simp] theorem realize_sum [AddCommMonoidWithOne M]
    {β : Type*} {s : Finset β} {f : β -> presburger.Term α} :
    Term.realize v (sum s f) = ∑ i in s, Term.realize v (f i) := by
  classical
  simp only [sum]
  conv => rhs; rw [← s.toList_toFinset, List.sum_toFinset _ s.nodup_toList]
  generalize s.toList = l
  induction l with simp [*]

end FirstOrder.Language.presburger
