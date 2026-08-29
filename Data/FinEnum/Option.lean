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
/--
Definition of `insertNone` / `insertNone` 的定义

English:
definition insertNone
  signature: (α : Type u) [FinEnum α] (i : Fin (card α + 1))
  body: card α + 1
equiv := equiv.optionCongr.trans .symm finSuccEquiv' i

中文:
定义 insertNone
  签名: (α : 类型u) [FinEnum α] (i : 有限集 (card α + 1))
  定义体: card α + 1
equiv := equiv.optionCongr.trans .symm finSuccEquiv' i
-/
def insertNone (α : Type u) [FinEnum α] (i : Fin (card α + 1)) : FinEnum (Option α) where
  card := card α + 1
equiv := equiv.optionCongr.trans .symm finSuccEquiv' i

/--
Instance `instFinEnumOptionLast` / 实例 `instFinEnumOptionLast`

English:
instance instFinEnumOptionLast
  signature: (α : Type u) [FinEnum α]
  body: insertNone α (Fin.last _)

中文:
实例 instFinEnumOptionLast
  签名: (α : 类型u) [FinEnum α]
  定义体: insertNone α (Fin.last _)

Depends on / 依赖: Fin.last, insertNone
-/
instance instFinEnumOptionLast (α : Type u) [FinEnum α] : FinEnum (Option α) :=
  insertNone α (Fin.last _)

open Fin.NatCast in -- TODO: refactor the proof to avoid needing this.
/--
Definition of `recEmptyOption` / `recEmptyOption` 的定义

English:
definition recEmptyOption
  signature: {P : Type u -> Sort v}
  body: match cardeq : card α with
  | 0 => congr _ _ cardeq empty
  | n + 1 =>
    let fN := ULift.instFinEnum (α := Fin n)
    have : card (ULift.{u} <| Fin n) = n := card_ulift.trans card_fin
    congr (insertNone _ <| finChoice n) _
(cardeq.trans <| congrArg Nat.succ this.symm)
        option fN (recEmptyOption finChoice congr empty option _)
termination_by card α

中文:
定义 recEmptyOption
  签名: {P : 类型u -> 类型层 v}
  定义体: match cardeq : card α with
  | 0 => congr _ _ cardeq empty
  | n + 1 =>
    let fN := ULift.instFinEnum (α := Fin n)
    have : card (ULift.{u} <| Fin n) = n := card_ulift.trans card_fin
    congr (insertNone _ <| finChoice n) _
(cardeq.trans <| congrArg Nat.succ this.symm)
        option fN (recEmptyOption finChoice congr empty option _)
termination_by card α

Depends on / 依赖: Nat.succ, ULift.instFinEnum, card_fin, card_ulift, card_ulift.trans, cardeq, cardeq.trans, finChoice, insertNone, instFinEnum, option, recEmptyOption, termination_by, this.symm
-/
def recEmptyOption {P : Type u -> Sort v}
    (finChoice : (n : Nat) -> Fin (n + 1))
    (congr : {α β : Type u} -> (_ : FinEnum α) -> (_ : FinEnum β) -> card β = card α -> P α -> P β)
    (empty : P PEmpty.{u + 1})
    (option : {α : Type u} -> FinEnum α -> P α -> P (Option α))
    (α : Type u) [FinEnum α] :
    P α :=
  match cardeq : card α with
  | 0 => congr _ _ cardeq empty
  | n + 1 =>
    let fN := ULift.instFinEnum (α := Fin n)
    have : card (ULift.{u} <| Fin n) = n := card_ulift.trans card_fin
    congr (insertNone _ <| finChoice n) _
(cardeq.trans <| congrArg Nat.succ this.symm)
        option fN (recEmptyOption finChoice congr empty option _)
termination_by card α

/--
theorem `recEmptyOption_of_card_eq_zero` / 定理 `recEmptyOption_of_card_eq_zero`

English:
theorem recEmptyOption_of_card_eq_zero
  statement: {P : Type u -> Sort v}
  proof: by
  unfold recEmptyOption
  split
  · congr 1; exact Subsingleton.allEq _ _
· exact Nat.noConfusion h.symm.trans ‹_›

中文:
定理 recEmptyOption_of_card_eq_zero
  结论: {P : 类型u -> 类型层 v}
  证明: by
  unfold recEmptyOption
  split
  · congr 1; exact Subsingleton.allEq _ _
· exact Nat.noConfusion h.symm.trans ‹_›

Depends on / 依赖: Nat.noConfusion, Subsingleton, Subsingleton.allEq, h.symm.trans, noConfusion, recEmptyOption
-/
theorem recEmptyOption_of_card_eq_zero {P : Type u -> Sort v}
    (finChoice : (n : Nat) -> Fin (n + 1))
    (congr : {α β : Type u} -> (_ : FinEnum α) -> (_ : FinEnum β) -> card β = card α -> P α -> P β)
    (empty : P PEmpty.{u + 1})
    (option : {α : Type u} -> FinEnum α -> P α -> P (Option α))
    (α : Type u) [FinEnum α] (h : card α = 0) (_ : FinEnum PEmpty.{u + 1}) :
    recEmptyOption finChoice congr empty option α =
      congr _ _ (h.trans card_eq_zero.symm) empty := by
  unfold recEmptyOption
  split
  · congr 1; exact Subsingleton.allEq _ _
· exact Nat.noConfusion h.symm.trans ‹_›

open Fin.NatCast in -- TODO: refactor the proof to avoid needing this.
/--
theorem `recEmptyOption_of_card_pos` / 定理 `recEmptyOption_of_card_pos`

English:
theorem recEmptyOption_of_card_pos
  statement: {P : Type u -> Sort v}
  proof: by
  conv => lhs; unfold recEmptyOption
  split
  · exact absurd (‹_› ▸ h) (card α).lt_irrefl
· rcases Nat.succ.inj .trans ‹_› with rfl; rfl (card α).succ_pred_eq_of_pos h

中文:
定理 recEmptyOption_of_card_pos
  结论: {P : 类型u -> 类型层 v}
  证明: by
  conv => lhs; unfold recEmptyOption
  split
  · exact absurd (‹_› ▸ h) (card α).lt_irrefl
· rcases Nat.succ.inj .trans ‹_› with rfl; rfl (card α).succ_pred_eq_of_pos h

Depends on / 依赖: Nat.succ.inj, absurd, lt_irrefl, recEmptyOption, succ_pred_eq_of_pos
-/
theorem recEmptyOption_of_card_pos {P : Type u -> Sort v}
    (finChoice : (n : Nat) -> Fin (n + 1))
    (congr : {α β : Type u} -> (_ : FinEnum α) -> (_ : FinEnum β) -> card β = card α -> P α -> P β)
    (empty : P PEmpty.{u + 1})
    (option : {α : Type u} -> FinEnum α -> P α -> P (Option α))
    (α : Type u) [FinEnum α] (h : 0 < card α) :
    recEmptyOption finChoice congr empty option α =
      congr (insertNone _ <| finChoice (card α - 1)) ‹_›
        (congrArg (· + 1) card_fin |>.trans <| (card α).succ_pred_eq_of_pos h).symm
        (option ULift.instFinEnum <|
          recEmptyOption finChoice congr empty option (ULift.{u} <| Fin (card α - 1))) := by
  conv => lhs; unfold recEmptyOption
  split
  · exact absurd (‹_› ▸ h) (card α).lt_irrefl
· rcases Nat.succ.inj .trans ‹_› with rfl; rfl (card α).succ_pred_eq_of_pos h

/--
Definition of `recOnEmptyOption` / `recOnEmptyOption` 的定义

English:
abbreviation recOnEmptyOption
  signature: {P : Type u -> Sort v}
  body: @recEmptyOption P finChoice congr empty option α aenum

中文:
缩写 recOnEmptyOption
  签名: {P : 类型u -> 类型层 v}
  定义体: @recEmptyOption P finChoice congr empty option α aenum

Depends on / 依赖: finChoice, option, recEmptyOption
-/
abbrev recOnEmptyOption {P : Type u -> Sort v}
    {α : Type u} (aenum : FinEnum α)
    (finChoice : (n : Nat) -> Fin (n + 1))
    (congr : {α β : Type u} -> (_ : FinEnum α) -> (_ : FinEnum β) -> card β = card α -> P α -> P β)
    (empty : P PEmpty.{u + 1})
    (option : {α : Type u} -> FinEnum α -> P α -> P (Option α)) :
    P α :=
  @recEmptyOption P finChoice congr empty option α aenum

end FinEnum
