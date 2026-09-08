/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Basic

/-!
# Sorting a finite type

This file provides two equivalences for linearly ordered fintypes:
* `monoEquivOfFin`: Order isomorphism between `α` and `Fin (card α)`.
* `finSumEquivOfFinset`: Equivalence between `α` and `Fin m ⊕ Fin n` where `m` and `n` are
  respectively the cardinalities of some `Finset α` and its complement.
-/

@[expose] public section


open Finset

/-- Given a linearly ordered fintype `α` of cardinal `k`, the order isomorphism
`monoEquivOfFin α h` is the increasing bijection between `Fin k` and `α`. Here, `h` is a proof
that the cardinality of `α` is `k`. We use this instead of an isomorphism `Fin (card α) ≃o α` to
avoid casting issues in further uses of this function. -/
/-
**monoEquivOfFin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：monoEquivOfFin (α : Type*) [Fintype α] [LinearOrder α] {k : Nat} (h : Fint
ype.card α = k) : Fin k ≃o α
参数：α : Type*；h : Fintype.card α = k。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)

--- 原说明 ---
Given a linearly ordered fintype `α` of cardinal `k`, the order isomorphism
`monoEquivOfFin α h` is the increasing bijection between `Fin k` and `α`. Here, 
`h` is a proof
that the cardinality of `α` is `k`. We use this instead of an isomorphism `Fin (
card α) ≃o α` to
avoid casting issues in further uses of this function.
-/
def monoEquivOfFin (α : Type*) [Fintype α] [LinearOrder α] {k : ℕ} (h : Fintype.card α = k) :
    Fin k ≃o α :=
  (univ.orderIsoOfFin h).trans <| (OrderIso.setCongr _ _ coe_univ).trans OrderIso.Set.univ

variable {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] {m n : ℕ} {s : Finset α}

/-- If `α` is a linearly ordered fintype, `s : Finset α` has cardinality `m` and its complement has
cardinality `n`, then `Fin m ⊕ Fin n ≃ α`. The equivalence sends elements of `Fin m` to
elements of `s` and elements of `Fin n` to elements of `sᶜ` while preserving order on each
"half" of `Fin m ⊕ Fin n` (using `Set.orderIsoOfFin`). -/
/-
**finSumEquivOfFinset** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finSumEquivOfFinset (hm : #s = m) (hn : #sᶜ = n) : Fin m oplus Fin n ≃ α
参数：hm : #s = m；hn : #sᶜ = n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ

--- 原说明 ---
If `α` is a linearly ordered fintype, `s : Finset α` has cardinality `m` and its
 complement has
cardinality `n`, then `Fin m ⊕ Fin n ≃ α`. The equivalence sends elements of `Fi
n m` to
elements of `s` and elements of `Fin n` to elements of `sᶜ` while preserving ord
er on each
"half" of `Fin m ⊕ Fin n` (using `Set.orderIsoOfFin`).
-/
def finSumEquivOfFinset (hm : #s = m) (hn : #sᶜ = n) : Fin m ⊕ Fin n ≃ α :=
  calc
    Fin m ⊕ Fin n ≃ (s : Set α) ⊕ (sᶜ : Set α) :=
      Equiv.sumCongr (s.orderIsoOfFin hm).toEquiv <|
        (sᶜ.orderIsoOfFin hn).toEquiv.trans <| Equiv.setCongr s.coe_compl
    _ ≃ α := Equiv.Set.sumCompl _

@[simp]
/-
**finSumEquivOfFinset_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSumEquivOfFinset_inl (hm : #s = m) (hn : #sᶜ = n) (i : Fin m) : finSumE
quivOfFinset hm hn (Sum.inl i) = s.orderEmbOfFin hm i
参数：hm : #s = m；hn : #sᶜ = n；i : Fin m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finSumEquivOfFinset_inl (hm : #s = m) (hn : #sᶜ = n) (i : Fin m) :
    finSumEquivOfFinset hm hn (Sum.inl i) = s.orderEmbOfFin hm i :=
  rfl

@[simp]
/-
**finSumEquivOfFinset_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSumEquivOfFinset_inr (hm : #s = m) (hn : #sᶜ = n) (i : Fin n) : finSumE
quivOfFinset hm hn (Sum.inr i) = sᶜ.orderEmbOfFin hn i
参数：hm : #s = m；hn : #sᶜ = n；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finSumEquivOfFinset_inr (hm : #s = m) (hn : #sᶜ = n) (i : Fin n) :
    finSumEquivOfFinset hm hn (Sum.inr i) = sᶜ.orderEmbOfFin hn i :=
  rfl
