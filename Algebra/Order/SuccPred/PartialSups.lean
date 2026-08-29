/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Oliver Butterley, Lua Viana Reis
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Order.PartialSups
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# `PartialSups` in a `SuccAddOrder`

Basic results concerning `PartialSups` which follow with minimal assumptions beyond the fact that
the `PartialSup` is defined over a `SuccAddOrder`.
-/

public section

open Finset

variable {α ι : Type*} [SemilatticeSup α] [LinearOrder ι]

@[simp]
/--
lemma `partialSups_add_one` / 引理 `partialSups_add_one`

English:
lemma partialSups_add_one
  statement: [Add ι] [One ι] [LocallyFiniteOrderBot ι] [SuccAddOrder ι]
  proof: Order.succ_eq_add_one i ▸ partialSups_succ f i

中文:
引理 partialSups_add_one
  结论: [加法 ι] [幺 ι] [LocallyFiniteOrderBot ι] [SuccAdd序 ι]
  证明: Order.succ_eq_add_one i ▸ partialSups_succ f i

Depends on / 依赖: Order.succ_eq_add_one, partialSups_succ, succ_eq_add_one
-/
lemma partialSups_add_one [Add ι] [One ι] [LocallyFiniteOrderBot ι] [SuccAddOrder ι]
    (f : ι -> α) (i : ι) : partialSups f (i + 1) = partialSups f i ⊔ f (i + 1) :=
  Order.succ_eq_add_one i ▸ partialSups_succ f i

/--
lemma `partialSups_succ'` / 引理 `partialSups_succ'`

English:
lemma partialSups_succ'
  statement: {α : Type*} [SemilatticeSup α] [LocallyFiniteOrder ι]
  proof: by
  refine Succ.rec (by simp) (fun j _ h => ?_) (bot_le (a := i))
  have : (partialSups (f ∘ Order.succ)) (Order.succ j) =
      ((partialSups (f ∘ Order.succ)) j ⊔ (f ∘ Order.succ) (Order.succ j)) := by simp
  simp [this, h, sup_assoc]

中文:
引理 partialSups_succ'
  结论: {α : 类型} [SemilatticeSup α] [局部有限序 ι]
  证明: by
  refine Succ.rec (by simp) (fun j _ h => ?_) (bot_le (a := i))
  have : (partialSups (f ∘ Order.succ)) (Order.succ j) =
      ((partialSups (f ∘ Order.succ)) j ⊔ (f ∘ Order.succ) (Order.succ j)) := by simp
  simp [this, h, sup_assoc]

Depends on / 依赖: Order.succ, Succ.rec, bot_le, partialSups, sup_assoc
-/
lemma partialSups_succ' {α : Type*} [SemilatticeSup α] [LocallyFiniteOrder ι]
    [SuccOrder ι] [OrderBot ι] (f : ι -> α) (i : ι) :
    (partialSups f) (Order.succ i) = f ⊥ ⊔ (partialSups (f ∘ Order.succ)) i := by
  refine Succ.rec (by simp) (fun j _ h => ?_) (bot_le (a := i))
  have : (partialSups (f ∘ Order.succ)) (Order.succ j) =
      ((partialSups (f ∘ Order.succ)) j ⊔ (f ∘ Order.succ) (Order.succ j)) := by simp
  simp [this, h, sup_assoc]

/--
lemma `partialSups_add_one'` / 引理 `partialSups_add_one'`

English:
lemma partialSups_add_one'
  statement: [Add ι] [One ι] [OrderBot ι] [LocallyFiniteOrder ι]
  proof: by
  simpa [← Order.succ_eq_add_one] using partialSups_succ' f i

中文:
引理 partialSups_add_one'
  结论: [加法 ι] [幺 ι] [有底序 ι] [局部有限序 ι]
  证明: by
  simpa [← Order.succ_eq_add_one] using partialSups_succ' f i

Depends on / 依赖: Order.succ_eq_add_one, partialSups_succ, succ_eq_add_one
-/
lemma partialSups_add_one' [Add ι] [One ι] [OrderBot ι] [LocallyFiniteOrder ι]
    [SuccAddOrder ι] (f : ι -> α) (i : ι) :
    partialSups f (i + 1) = f ⊥ ⊔ partialSups (f ∘ (fun k => k + 1)) i := by
  simpa [← Order.succ_eq_add_one] using partialSups_succ' f i
