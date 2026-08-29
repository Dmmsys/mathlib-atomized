/-
Copyright (c) 2015 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
module

public import Mathlib.Data.W.Basic

/-!
# Examples of W-types

We take the view of W types as inductive types.
Given `α : Type` and `β : α → Type`, the W type determined by this data, `WType β`, is the
inductively with constructors from `α` and arities of each constructor `a : α` given by `β a`.

This file contains `Nat` and `List` as examples of W types.

## Main results
* `WType.equivNat`: the construction of the naturals as a W-type is equivalent to `Nat`
* `WType.equivList`: the construction of lists on a type `γ` as a W-type is equivalent to `List γ`
-/

@[expose] public section


universe u v

namespace WType

-- For "W_type"

section Nat

/--
Inductive type `Natα` / 归纳类型 `Natα`

English:
inductive Natα
  parameters: : Type
  constructors (2):
    - zero: Natα
    - succ: Natα

中文:
归纳类型 自然数α
  参数: : 类型
  构造子 (2 个):
    - zero: 自然数α
    - succ: 自然数α
-/
inductive Natα : Type
  | zero : Natα
  | succ : Natα

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Natα
  body: ⟨Natα.zero⟩

中文:
实例 :
  签名: 可居 自然数α
  定义体: ⟨Natα.zero⟩
-/
instance : Inhabited Natα :=
  ⟨Natα.zero⟩

/--
Definition of `Natβ` / `Natβ` 的定义

English:
definition Natβ
  signature: : Natα -> Type

中文:
定义 自然数β
  签名: : 自然数α -> 类型
-/
def Natβ : Natα -> Type
  | Natα.zero => Empty
  | Natα.succ => Unit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Natβ Natα.succ)
  body: ⟨()⟩

中文:
实例 :
  签名: 可居 (自然数β 自然数α.succ)
  定义体: ⟨()⟩
-/
instance : Inhabited (Natβ Natα.succ) :=
  ⟨()⟩

/-- The isomorphism from the naturals to its corresponding `WType` -/
@[simp]
/--
Definition of `ofNat` / `ofNat` 的定义

English:
definition ofNat
  signature: : Nat -> WType Natβ

中文:
定义 of自然数
  签名: : 自然数 -> WType 自然数β
-/
def ofNat : Nat -> WType Natβ
  | Nat.zero => ⟨Natα.zero, Empty.elim⟩
  | Nat.succ n => ⟨Natα.succ, fun _ => ofNat n⟩

/-- The isomorphism from the `WType` of the naturals to the naturals -/
@[simp]
/--
Definition of `toNat` / `toNat` 的定义

English:
definition toNat
  signature: : WType Natβ -> Nat

中文:
定义 to自然数
  签名: : WType 自然数β -> 自然数
-/
def toNat : WType Natβ -> Nat
  | WType.mk Natα.zero _ => 0
  | WType.mk Natα.succ f => (f ()).toNat.succ

/--
theorem `leftInverse_nat` / 定理 `leftInverse_nat`

English:
theorem leftInverse_nat
  statement: Function.LeftInverse ofNat toNat

中文:
定理 leftInverse_nat
  结论: 函数.左逆 of自然数 to自然数
-/
theorem leftInverse_nat : Function.LeftInverse ofNat toNat
  | WType.mk Natα.zero f => by
    rw [toNat]; rw [ofNat]
    congr
    ext x
    cases x
  | WType.mk Natα.succ f => by
    simp only [toNat, ofNat, leftInverse_nat (f ()), mk.injEq, heq_eq_eq, true_and]
    rfl

/--
theorem `rightInverse_nat` / 定理 `rightInverse_nat`

English:
theorem rightInverse_nat
  statement: Function.RightInverse ofNat toNat

中文:
定理 rightInverse_nat
  结论: 函数.右逆 of自然数 to自然数
-/
theorem rightInverse_nat : Function.RightInverse ofNat toNat
  | Nat.zero => rfl
  | Nat.succ n => by rw [ofNat, toNat, rightInverse_nat n]

/--
Definition of `equivNat` / `equivNat` 的定义

English:
definition equivNat
  signature: : WType Natβ ≃ Nat where
  body: toNat
  invFun := ofNat
  left_inv := leftInverse_nat
  right_inv := rightInverse_nat

中文:
定义 equiv自然数
  签名: : WType 自然数β ≃ 自然数 where
  定义体: toNat
  invFun := ofNat
  left_inv := leftInverse_nat
  right_inv := rightInverse_nat
-/
def equivNat : WType Natβ ≃ Nat where
  toFun := toNat
  invFun := ofNat
  left_inv := leftInverse_nat
  right_inv := rightInverse_nat

open Sum PUnit

/-- `WType.Natα` is equivalent to `PUnit ⊕ PUnit`.
This is useful when considering the associated polynomial endofunctor.
-/
@[simps]
/--
Definition of `NatαEquivPUnitSumPUnit` / `NatαEquivPUnitSumPUnit` 的定义

English:
definition NatαEquivPUnitSumPUnit
  signature: : Natα ≃ PUnit.{u + 1} oplus PUnit where
  body: match c with
    | Natα.zero => inl unit
    | Natα.succ => inr unit
  invFun b :=
    match b with
    | inl _ => Natα.zero
    | inr _ => Natα.succ
  left_inv c :=
    match c with
    | Natα.zero => rfl
    | Natα.succ => rfl
  right_inv b :=
    match b with
    | inl _ => rfl
    | inr _ => rfl

中文:
定义 自然数αEquivPUnitSumPUnit
  签名: : 自然数α ≃ 命题单元.{u + 1} oplus 命题单元 where
  定义体: match c with
    | Natα.zero => inl unit
    | Natα.succ => inr unit
  invFun b :=
    match b with
    | inl _ => Natα.zero
    | inr _ => Natα.succ
  left_inv c :=
    match c with
    | Natα.zero => rfl
    | Natα.succ => rfl
  right_inv b :=
    match b with
    | inl _ => rfl
    | inr _ => rfl

Depends on / 依赖: invFun, left_inv, right_inv
-/
def NatαEquivPUnitSumPUnit : Natα ≃ PUnit.{u + 1} oplus PUnit where
  toFun c :=
    match c with
    | Natα.zero => inl unit
    | Natα.succ => inr unit
  invFun b :=
    match b with
    | inl _ => Natα.zero
    | inr _ => Natα.succ
  left_inv c :=
    match c with
    | Natα.zero => rfl
    | Natα.succ => rfl
  right_inv b :=
    match b with
    | inl _ => rfl
    | inr _ => rfl

end Nat

section List

variable (γ : Type u)

/--
Inductive type `Listα` / 归纳类型 `Listα`

English:
inductive Listα
  parameters: : Type u
  constructors (2):
    - nil: Listα
    - cons: γ -> Listα

中文:
归纳类型 Listα
  参数: : 类型u
  构造子 (2 个):
    - nil: Listα
    - cons: γ -> Listα
-/
inductive Listα : Type u
  | nil : Listα
  | cons : γ -> Listα

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Listα γ)
  body: ⟨Listα.nil⟩

中文:
实例 :
  签名: 可居 (Listα γ)
  定义体: ⟨Listα.nil⟩
-/
instance : Inhabited (Listα γ) :=
  ⟨Listα.nil⟩

/--
Definition of `Listβ` / `Listβ` 的定义

English:
definition Listβ
  signature: : Listα γ -> Type u

中文:
定义 Listβ
  签名: : Listα γ -> 类型u
-/
def Listβ : Listα γ -> Type u
  | Listα.nil => PEmpty
  | Listα.cons _ => PUnit

instance (hd : γ) : Inhabited (Listβ γ (Listα.cons hd)) :=
  ⟨PUnit.unit⟩

/-- The isomorphism from lists to the `WType` construction of lists -/
@[simp]
/--
Definition of `ofList` / `ofList` 的定义

English:
definition ofList
  signature: : List γ -> WType (Listβ γ)

中文:
定义 ofList
  签名: : 列表 γ -> WType (Listβ γ)
-/
def ofList : List γ -> WType (Listβ γ)
  | List.nil => ⟨Listα.nil, PEmpty.elim⟩
  | List.cons hd tl => ⟨Listα.cons hd, fun _ => ofList tl⟩

/-- The isomorphism from the `WType` construction of lists to lists -/
@[simp]
/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: : WType (Listβ γ) -> List γ

中文:
定义 toList
  签名: : WType (Listβ γ) -> 列表 γ
-/
def toList : WType (Listβ γ) -> List γ
  | WType.mk Listα.nil _ => []
  | WType.mk (Listα.cons hd) f => hd :: (f PUnit.unit).toList

set_option backward.isDefEq.respectTransparency false in
/--
theorem `leftInverse_list` / 定理 `leftInverse_list`

English:
theorem leftInverse_list
  statement: Function.LeftInverse (ofList γ) (toList _)

中文:
定理 leftInverse_list
  结论: 函数.左逆 (ofList γ) (toList _)
-/
theorem leftInverse_list : Function.LeftInverse (ofList γ) (toList _)
  | WType.mk Listα.nil f => by
    simp only [toList, ofList, mk.injEq, heq_eq_eq, true_and]
    ext x
    cases x
  | WType.mk (Listα.cons x) f => by
    simp only [toList, ofList, leftInverse_list (f PUnit.unit), mk.injEq, heq_eq_eq, true_and]
    rfl

/--
theorem `rightInverse_list` / 定理 `rightInverse_list`

English:
theorem rightInverse_list
  statement: Function.RightInverse (ofList γ) (toList _)

中文:
定理 rightInverse_list
  结论: 函数.右逆 (ofList γ) (toList _)
-/
theorem rightInverse_list : Function.RightInverse (ofList γ) (toList _)
  | List.nil => rfl
  | List.cons hd tl => by simp [rightInverse_list tl]

/--
Definition of `equivList` / `equivList` 的定义

English:
definition equivList
  signature: : WType (Listβ γ) ≃ List γ where
  body: toList _
  invFun := ofList _
  left_inv := leftInverse_list _
  right_inv := rightInverse_list _

中文:
定义 equivList
  签名: : WType (Listβ γ) ≃ 列表 γ where
  定义体: toList _
  invFun := ofList _
  left_inv := leftInverse_list _
  right_inv := rightInverse_list _

Depends on / 依赖: toList
-/
def equivList : WType (Listβ γ) ≃ List γ where
  toFun := toList _
  invFun := ofList _
  left_inv := leftInverse_list _
  right_inv := rightInverse_list _

/--
Definition of `ListαEquivPUnitSum` / `ListαEquivPUnitSum` 的定义

English:
definition ListαEquivPUnitSum
  signature: : Listα γ ≃ PUnit.{v + 1} oplus γ where
  body: match c with
    | Listα.nil => Sum.inl PUnit.unit
    | Listα.cons x => Sum.inr x
  invFun := Sum.elim (fun _ => Listα.nil) Listα.cons
  left_inv c :=
    match c with
    | Listα.nil => rfl
    | Listα.cons _ => rfl
  right_inv x :=
    match x with
    | Sum.inl PUnit.unit => rfl
    | Sum.inr _ 

中文:
定义 ListαEquivPUnitSum
  签名: : Listα γ ≃ 命题单元.{v + 1} oplus γ where
  定义体: match c with
    | Listα.nil => Sum.inl PUnit.unit
    | Listα.cons x => Sum.inr x
  invFun := Sum.elim (fun _ => Listα.nil) Listα.cons
  left_inv c :=
    match c with
    | Listα.nil => rfl
    | Listα.cons _ => rfl
  right_inv x :=
    match x with
    | Sum.inl PUnit.unit => rfl
    | Sum.inr _ 

Depends on / 依赖: PUnit.unit, Sum.elim, Sum.inl, Sum.inr, invFun, left_inv, right_inv
-/
def ListαEquivPUnitSum : Listα γ ≃ PUnit.{v + 1} oplus γ where
  toFun c :=
    match c with
    | Listα.nil => Sum.inl PUnit.unit
    | Listα.cons x => Sum.inr x
  invFun := Sum.elim (fun _ => Listα.nil) Listα.cons
  left_inv c :=
    match c with
    | Listα.nil => rfl
    | Listα.cons _ => rfl
  right_inv x :=
    match x with
    | Sum.inl PUnit.unit => rfl
    | Sum.inr _ => rfl

end List

end WType
