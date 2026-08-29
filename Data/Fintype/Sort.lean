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

/--
Definition of `monoEquivOfFin` / `monoEquivOfFin` 的定义

English:
definition monoEquivOfFin
  signature: (α : Type*) [Fintype α] [LinearOrder α] {k : Nat} (h : Fintype.card α = k)
  body: (univ.orderIsoOfFin h).trans (OrderIso.setCongr _ _ coe_univ).trans OrderIso.Set.univ

中文:
定义 monoEquivOfFin
  签名: (α : 类型) [有限类型 α] [线性序 α] {k : 自然数} (h : 有限类型.card α = k)
  定义体: (univ.orderIsoOfFin h).trans (OrderIso.setCongr _ _ coe_univ).trans OrderIso.Set.univ

Depends on / 依赖: OrderIso, OrderIso.Set.univ, OrderIso.setCongr, coe_univ, orderIsoOfFin, setCongr, univ.orderIsoOfFin
-/
def monoEquivOfFin (α : Type*) [Fintype α] [LinearOrder α] {k : Nat} (h : Fintype.card α = k) :
    Fin k ≃o α :=
(univ.orderIsoOfFin h).trans (OrderIso.setCongr _ _ coe_univ).trans OrderIso.Set.univ

variable {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] {m n : Nat} {s : Finset α}

/--
Definition of `finSumEquivOfFinset` / `finSumEquivOfFinset` 的定义

English:
definition finSumEquivOfFinset
  signature: (hm : #s = m) (hn : #sᶜ = n)
  body: calc
    Fin m oplus Fin n ≃ (s : Set α) oplus (sᶜ : Set α) :=
Equiv.sumCongr (s.orderIsoOfFin hm).toEquiv
(sᶜ.orderIsoOfFin hn).toEquiv.trans Equiv.setCongr s.coe_compl
    _ ≃ α := Equiv.Set.sumCompl _

@[simp]

中文:
定义 finSumEquivOfFinset
  签名: (hm : #s = m) (hn : #sᶜ = n)
  定义体: calc
    Fin m oplus Fin n ≃ (s : Set α) oplus (sᶜ : Set α) :=
Equiv.sumCongr (s.orderIsoOfFin hm).toEquiv
(sᶜ.orderIsoOfFin hn).toEquiv.trans Equiv.setCongr s.coe_compl
    _ ≃ α := Equiv.Set.sumCompl _

@[simp]

Depends on / 依赖: Equiv.Set.sumCompl, Equiv.setCongr, Equiv.sumCongr, coe_compl, orderIsoOfFin, s.coe_compl, s.orderIsoOfFin, setCongr, sumCompl, sumCongr, toEquiv, toEquiv.trans
-/
def finSumEquivOfFinset (hm : #s = m) (hn : #sᶜ = n) : Fin m oplus Fin n ≃ α :=
  calc
    Fin m oplus Fin n ≃ (s : Set α) oplus (sᶜ : Set α) :=
Equiv.sumCongr (s.orderIsoOfFin hm).toEquiv
(sᶜ.orderIsoOfFin hn).toEquiv.trans Equiv.setCongr s.coe_compl
    _ ≃ α := Equiv.Set.sumCompl _

@[simp]
/--
theorem `finSumEquivOfFinset_inl` / 定理 `finSumEquivOfFinset_inl`

English:
theorem finSumEquivOfFinset_inl
  given: (hm : #s = m) (hn : #sᶜ = n) (i : Fin m)
  proof: rfl

@[simp]

中文:
定理 finSumEquivOfFinset_inl
  条件: (hm : #s = m) (hn : #sᶜ = n) (i : 有限集 m)
  证明: rfl

@[simp]
-/
theorem finSumEquivOfFinset_inl (hm : #s = m) (hn : #sᶜ = n) (i : Fin m) :
    finSumEquivOfFinset hm hn (Sum.inl i) = s.orderEmbOfFin hm i :=
  rfl

@[simp]
/--
theorem `finSumEquivOfFinset_inr` / 定理 `finSumEquivOfFinset_inr`

English:
theorem finSumEquivOfFinset_inr
  given: (hm : #s = m) (hn : #sᶜ = n) (i : Fin n)
  proof: rfl

中文:
定理 finSumEquivOfFinset_inr
  条件: (hm : #s = m) (hn : #sᶜ = n) (i : 有限集 n)
  证明: rfl
-/
theorem finSumEquivOfFinset_inr (hm : #s = m) (hn : #sᶜ = n) (i : Fin n) :
    finSumEquivOfFinset hm hn (Sum.inr i) = sᶜ.orderEmbOfFin hn i :=
  rfl
