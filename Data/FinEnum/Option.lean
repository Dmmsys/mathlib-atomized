/-
Copyright (c) 2024 Tom Kranz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Kranz
-/
module

public import Mathlib.Data.FinEnum
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# FinEnum instance for Option

Provides a recursor for FinEnum types like `Fintype.truncRecEmptyOption`, but capable of producing
non-truncated data.

## TODO
* recreate rest of `Mathlib/Data/Fintype/Option.lean`
-/

@[expose] public section

namespace FinEnum
universe u v

/-- Inserting an `Option.none` anywhere in an enumeration yields another enumeration. -/
@[instance_reducible]
/-
**FinEnum.insertNone** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum`。
形式化陈述：insertNone (α : Type u) [FinEnum α] (i : Fin (card α + 1)) : FinEnum (Opti
on α) where card
参数：α : Type u；i : Fin (card α + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Inserting an `Option.none` anywhere in an enumeration yields another enumeration
.
-/
def insertNone (α : Type u) [FinEnum α] (i : Fin (card α + 1)) : FinEnum (Option α) where
  card := card α + 1
  equiv := equiv.optionCongr.trans <| finSuccEquiv' i |>.symm

/-- This is an arbitrary choice of insertion rank for a default instance.
It keeps the mapping of the existing `α`-inhabitants intact, modulo `Fin.castSucc`. -/
/-
**FinEnum.instFinEnumOptionLast** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
形式化陈述：instFinEnumOptionLast (α : Type u) [FinEnum α] : FinEnum (Option α)
参数：α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an arbitrary choice of insertion rank for a default instance.
It keeps the mapping of the existing `α`-inhabitants intact, modulo `Fin.castSuc
c`.
-/
instance instFinEnumOptionLast (α : Type u) [FinEnum α] : FinEnum (Option α) :=
  insertNone α (Fin.last _)

open Fin.NatCast in -- TODO: refactor the proof to avoid needing this.
/-- A recursor principle for finite-and-enumerable types, analogous to `Nat.rec`.
It effectively says that every `FinEnum` is either `Empty` or `Option α`, up to an `Equiv` mediated
by `Fin`s of equal cardinality.
In contrast to the `Fintype` case, data can be transported along such an `Equiv`.
Also, since order matters, the choice of element that gets replaced by `Option.none` has
to be provided for every step.

Since every `FinEnum` instance implies a `Fintype` instance and `Prop` is squashed already,
`Fintype.induction_empty_option` can be used if a `Prop` needs to be constructed.
Cf. `Data.Fintype.Option`
-/
/-
**FinEnum.recEmptyOption** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum`。
形式化陈述：recEmptyOption {P : Type u -> Sort v} (finChoice : (n : Nat) -> Fin (n + 1
)) (congr : {α β : Type u} -> (_ : FinEnum α) -> (_ : FinEnum β) -> card β = car
d α -> P α -> P β) (empty : P PEmpty.{u + 1}) (option : {α : Type u} -> FinEnum 
α -> P α -> P (Option α)) (α : Type u) [FinEnum α] : P α
参数：finChoice : (n : Nat) -> Fin (n + 1)；congr : {α β : Type u} -> (_ : FinEnum α
) -> (_ : FinEnum β) -> card β = card α -> P α -> P β；empty : P PEmpty.{u + 1}；o
ption : {α : Type u} -> FinEnum α -> P α -> P (Option α)；α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor principle for finite-and-enumerable types, analogous to `Nat.rec`.
It effectively says that every `FinEnum` is either `Empty` or `Option α`, up to 
an `Equiv` mediated
by `Fin`s of equal cardinality.
In contrast to the `Fintype` case, data can be transported along such an `Equiv`
.
Also, since order matters, the choice of element that gets replaced by `Option.n
one` has
to be provided for every step.

Since every `FinEnum` instance implies a `Fintype` instance and `Prop` is squash
ed already,
`Fintype.induction_empty_option` can be used if a `Prop` needs to be constructed
.
Cf. `Data.Fintype.Option`
-/
def recEmptyOption {P : Type u → Sort v}
    (finChoice : (n : ℕ) → Fin (n + 1))
    (congr : {α β : Type u} → (_ : FinEnum α) → (_ : FinEnum β) → card β = card α → P α → P β)
    (empty : P PEmpty.{u + 1})
    (option : {α : Type u} → FinEnum α → P α → P (Option α))
    (α : Type u) [FinEnum α] :
    P α :=
  match cardeq : card α with
  | 0 => congr _ _ cardeq empty
  | n + 1 =>
    let fN := ULift.instFinEnum (α := Fin n)
    have : card (ULift.{u} <| Fin n) = n := card_ulift.trans card_fin
    congr (insertNone _ <| finChoice n) _
      (cardeq.trans <| congrArg Nat.succ this.symm) <|
        option fN (recEmptyOption finChoice congr empty option _)
termination_by card α

/--
For an empty type, the recursion principle evaluates to whatever `congr`
makes of the base case.
-/
/-
**FinEnum.recEmptyOption_of_card_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：recEmptyOption_of_card_eq_zero {P : Type u -> Sort v} (finChoice : (n : Na
t) -> Fin (n + 1)) (congr : {α β : Type u} -> (_ : FinEnum α) -> (_ : FinEnum β)
 -> card β = card α -> P α -> P β) (empty : P PEmpty.{u + 1}) (option : {α : Typ
e u} -> FinEnum α -> P α -> P (Option α)) (α : Type u) [FinEnum α] (h : card α =
 0) (_ : FinEnum PEmpty.{u + 1}) : recEmptyOption finChoice congr empty option α
 = congr _ _ (h.trans card_eq_zero.symm) empty
参数：finChoice : (n : Nat) -> Fin (n + 1)；congr : {α β : Type u} -> (_ : FinEnum α
) -> (_ : FinEnum β) -> card β = card α -> P α -> P β；empty : P PEmpty.{u + 1}；o
ption : {α : Type u} -> FinEnum α -> P α -> P (Option α)；α : Type u；h : card α =
 0；_ : FinEnum PEmpty.{u + 1}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FinEnum.card_eq_zero`：card_eq_zero {α : Type u} [FinEnum α] [IsEmpty α] 
: card α = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FinEnum.recEmptyOption.eq_def`：∀ {P : Type u → Sort v} (finChoice : (n :
 ℕ) → Fin (n + 1))   (congr : {α β : Type u} → (x : FinEnum α) → (x_1 : FinEnum 
β) → FinEnum.card β…
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
For an empty type, the recursion principle evaluates to whatever `congr`
makes of the base case.
-/
theorem recEmptyOption_of_card_eq_zero {P : Type u → Sort v}
    (finChoice : (n : ℕ) → Fin (n + 1))
    (congr : {α β : Type u} → (_ : FinEnum α) → (_ : FinEnum β) → card β = card α → P α → P β)
    (empty : P PEmpty.{u + 1})
    (option : {α : Type u} → FinEnum α → P α → P (Option α))
    (α : Type u) [FinEnum α] (h : card α = 0) (_ : FinEnum PEmpty.{u + 1}) :
    recEmptyOption finChoice congr empty option α =
      congr _ _ (h.trans card_eq_zero.symm) empty := by
  unfold recEmptyOption
  split
  · congr 1; exact Subsingleton.allEq _ _
  · exact Nat.noConfusion <| h.symm.trans ‹_›

open Fin.NatCast in -- TODO: refactor the proof to avoid needing this.
/--
For a type with positive `card`, the recursion principle evaluates to whatever
`congr` makes of the step result, where `Option.none` has been inserted into the
`(finChoice (card α - 1))`th rank of the enumeration.
-/
/-
**FinEnum.recEmptyOption_of_card_pos** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：recEmptyOption_of_card_pos {P : Type u -> Sort v} (finChoice : (n : Nat) -
> Fin (n + 1)) (congr : {α β : Type u} -> (_ : FinEnum α) -> (_ : FinEnum β) -> 
card β = card α -> P α -> P β) (empty : P PEmpty.{u + 1}) (option : {α : Type u}
 -> FinEnum α -> P α -> P (Option α)) (α : Type u) [FinEnum α] (h : 0 < card α) 
: recEmptyOption finChoice congr empty option α = congr (insertNone _ <| finChoi
ce (card α - 1)) ‹_› (congrArg (· + 1) card_fin |>.trans <| (card α).succ_pred_e
q_of_pos h).symm (option U
参数：finChoice : (n : Nat) -> Fin (n + 1)；congr : {α β : Type u} -> (_ : FinEnum α
) -> (_ : FinEnum β) -> card β = card α -> P α -> P β；empty : P PEmpty.{u + 1}；o
ption : {α : Type u} -> FinEnum α -> P α -> P (Option α)；α : Type u；h : 0 < card
 α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FinEnum.card_fin`：card_fin {n} [FinEnum (Fin n)] : card (Fin n) = n
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `FinEnum.recEmptyOption.eq_def`：∀ {P : Type u → Sort v} (finChoice : (n :
 ℕ) → Fin (n + 1))   (congr : {α β : Type u} → (x : FinEnum α) → (x_1 : FinEnum 
β) → FinEnum.card β…
· 使用定理 `Nat.lt_irrefl`：∀ (n : ℕ), ¬n < n
· 使用定理 `Nat.succ.inj`：∀ {m n : ℕ}, m.succ = n.succ → m = n

--- 原说明 ---
For a type with positive `card`, the recursion principle evaluates to whatever
`congr` makes of the step result, where `Option.none` has been inserted into the
`(finChoice (card α - 1))`th rank of the enumeration.
-/
theorem recEmptyOption_of_card_pos {P : Type u → Sort v}
    (finChoice : (n : ℕ) → Fin (n + 1))
    (congr : {α β : Type u} → (_ : FinEnum α) → (_ : FinEnum β) → card β = card α → P α → P β)
    (empty : P PEmpty.{u + 1})
    (option : {α : Type u} → FinEnum α → P α → P (Option α))
    (α : Type u) [FinEnum α] (h : 0 < card α) :
    recEmptyOption finChoice congr empty option α =
      congr (insertNone _ <| finChoice (card α - 1)) ‹_›
        (congrArg (· + 1) card_fin |>.trans <| (card α).succ_pred_eq_of_pos h).symm
        (option ULift.instFinEnum <|
          recEmptyOption finChoice congr empty option (ULift.{u} <| Fin (card α - 1))) := by
  conv => lhs; unfold recEmptyOption
  split
  · exact absurd (‹_› ▸ h) (card α).lt_irrefl
  · rcases Nat.succ.inj <| (card α).succ_pred_eq_of_pos h |>.trans ‹_› with rfl; rfl

/-- A recursor principle for finite-and-enumerable types, analogous to `Nat.recOn`.
It effectively says that every `FinEnum` is either `Empty` or `Option α`, up to an `Equiv` mediated
by `Fin`s of equal cardinality.
In contrast to the `Fintype` case, data can be transported along such an `Equiv`.
Also, since order matters, the choice of element that gets replaced by `Option.none` has
to be provided for every step.
-/
/-
**FinEnum.recOnEmptyOption** 是 Mathlib 中的一个缩写定义，位于命名空间 `FinEnum`。
形式化陈述：recOnEmptyOption {P : Type u -> Sort v} {α : Type u} (aenum : FinEnum α) (
finChoice : (n : Nat) -> Fin (n + 1)) (congr : {α β : Type u} -> (_ : FinEnum α)
 -> (_ : FinEnum β) -> card β = card α -> P α -> P β) (empty : P PEmpty.{u + 1})
 (option : {α : Type u} -> FinEnum α -> P α -> P (Option α)) : P α
参数：aenum : FinEnum α；finChoice : (n : Nat) -> Fin (n + 1)；congr : {α β : Type u}
 -> (_ : FinEnum α) -> (_ : FinEnum β) -> card β = card α -> P α -> P β；empty : 
P PEmpty.{u + 1}；option : {α : Type u} -> FinEnum α -> P α -> P (Option α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor principle for finite-and-enumerable types, analogous to `Nat.recOn`.
It effectively says that every `FinEnum` is either `Empty` or `Option α`, up to 
an `Equiv` mediated
by `Fin`s of equal cardinality.
In contrast to the `Fintype` case, data can be transported along such an `Equiv`
.
Also, since order matters, the choice of element that gets replaced by `Option.n
one` has
to be provided for every step.
-/
abbrev recOnEmptyOption {P : Type u → Sort v}
    {α : Type u} (aenum : FinEnum α)
    (finChoice : (n : ℕ) → Fin (n + 1))
    (congr : {α β : Type u} → (_ : FinEnum α) → (_ : FinEnum β) → card β = card α → P α → P β)
    (empty : P PEmpty.{u + 1})
    (option : {α : Type u} → FinEnum α → P α → P (Option α)) :
    P α :=
  @recEmptyOption P finChoice congr empty option α aenum

end FinEnum

