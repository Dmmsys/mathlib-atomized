/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.Prod
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Limits of intervals along filters

This file contains some lemmas about how filters `Ixx` behave as the endpoints tend to `±∞`.

-/

public section

namespace Finset

open Filter

section Asymmetric

variable {α : Type*} [Preorder α] [LocallyFiniteOrder α]

/--
lemma `tendsto_Icc_atBot_prod_atTop` / 引理 `tendsto_Icc_atBot_prod_atTop`

English:
lemma tendsto_Icc_atBot_prod_atTop
  proof: by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ => (eventually_le_atBot i).prod_mk (eventually_ge_atTop i)

中文:
引理 tendsto_Icc_atBot_prod_atTop
  证明: by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ => (eventually_le_atBot i).prod_mk (eventually_ge_atTop i)

Depends on / 依赖: Set.subset_def, coe_subset, eventually_and, eventually_ge_atTop, eventually_le_atBot, prod_mk, subset_def, tendsto_atTop
-/
lemma tendsto_Icc_atBot_prod_atTop :
    Tendsto (fun p : α × α => Icc p.1 p.2) (atBot ×ˢ atTop) atTop := by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ => (eventually_le_atBot i).prod_mk (eventually_ge_atTop i)

/--
lemma `tendsto_Ioc_atBot_prod_atTop` / 引理 `tendsto_Ioc_atBot_prod_atTop`

English:
lemma tendsto_Ioc_atBot_prod_atTop
  given: [NoBotOrder α]
  proof: by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ => (eventually_lt_atBot i).prod_mk (eventually_ge_atTop i)

中文:
引理 tendsto_Ioc_atBot_prod_atTop
  条件: [NoBotOrder α]
  证明: by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ => (eventually_lt_atBot i).prod_mk (eventually_ge_atTop i)

Depends on / 依赖: Set.subset_def, coe_subset, eventually_and, eventually_ge_atTop, eventually_lt_atBot, prod_mk, subset_def, tendsto_atTop
-/
lemma tendsto_Ioc_atBot_prod_atTop [NoBotOrder α] :
    Tendsto (fun p : α × α => Ioc p.1 p.2) (atBot ×ˢ atTop) atTop := by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ => (eventually_lt_atBot i).prod_mk (eventually_ge_atTop i)

/--
lemma `tendsto_Ico_atBot_prod_atTop` / 引理 `tendsto_Ico_atBot_prod_atTop`

English:
lemma tendsto_Ico_atBot_prod_atTop
  given: [NoTopOrder α]
  proof: by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ => (eventually_le_atBot i).prod_mk (eventually_gt_atTop i)

中文:
引理 tendsto_Ico_atBot_prod_atTop
  条件: [NoTopOrder α]
  证明: by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ => (eventually_le_atBot i).prod_mk (eventually_gt_atTop i)

Depends on / 依赖: Set.subset_def, coe_subset, eventually_and, eventually_gt_atTop, eventually_le_atBot, prod_mk, subset_def, tendsto_atTop
-/
lemma tendsto_Ico_atBot_prod_atTop [NoTopOrder α] :
    Tendsto (fun p : α × α => Finset.Ico p.1 p.2) (atBot ×ˢ atTop) atTop := by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ => (eventually_le_atBot i).prod_mk (eventually_gt_atTop i)

/--
lemma `tendsto_Ioo_atBot_prod_atTop` / 引理 `tendsto_Ioo_atBot_prod_atTop`

English:
lemma tendsto_Ioo_atBot_prod_atTop
  given: [NoBotOrder α] [NoTopOrder α]
  proof: by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ => (eventually_lt_atBot i).prod_mk (eventually_gt_atTop i)

中文:
引理 tendsto_Ioo_atBot_prod_atTop
  条件: [NoBotOrder α] [NoTopOrder α]
  证明: by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ => (eventually_lt_atBot i).prod_mk (eventually_gt_atTop i)

Depends on / 依赖: Set.subset_def, coe_subset, eventually_and, eventually_gt_atTop, eventually_lt_atBot, prod_mk, subset_def, tendsto_atTop
-/
lemma tendsto_Ioo_atBot_prod_atTop [NoBotOrder α] [NoTopOrder α] :
    Tendsto (fun p : α × α => Finset.Ioo p.1 p.2) (atBot ×ˢ atTop) atTop := by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ => (eventually_lt_atBot i).prod_mk (eventually_gt_atTop i)

end Asymmetric

section Symmetric

variable {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  [LocallyFiniteOrder α]

/--
lemma `tendsto_Icc_neg_atTop_atTop` / 引理 `tendsto_Icc_neg_atTop_atTop`

English:
lemma tendsto_Icc_neg_atTop_atTop
  proof: tendsto_Icc_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

中文:
引理 tendsto_Icc_neg_atTop_atTop
  证明: tendsto_Icc_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

Depends on / 依赖: prodMk, tendsto_Icc_atBot_prod_atTop, tendsto_Icc_atBot_prod_atTop.comp, tendsto_id, tendsto_neg_atTop_atBot, tendsto_neg_atTop_atBot.prodMk
-/
lemma tendsto_Icc_neg_atTop_atTop :
    Tendsto (fun a : α => Icc (-a) a) atTop atTop :=
  tendsto_Icc_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

/--
lemma `tendsto_Ioc_neg_atTop_atTop` / 引理 `tendsto_Ioc_neg_atTop_atTop`

English:
lemma tendsto_Ioc_neg_atTop_atTop
  given: [NoBotOrder α]
  proof: tendsto_Ioc_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

中文:
引理 tendsto_Ioc_neg_atTop_atTop
  条件: [NoBotOrder α]
  证明: tendsto_Ioc_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

Depends on / 依赖: prodMk, tendsto_Ioc_atBot_prod_atTop, tendsto_Ioc_atBot_prod_atTop.comp, tendsto_id, tendsto_neg_atTop_atBot, tendsto_neg_atTop_atBot.prodMk
-/
lemma tendsto_Ioc_neg_atTop_atTop [NoBotOrder α] :
    Tendsto (fun a : α => Ioc (-a) a) atTop atTop :=
  tendsto_Ioc_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

/--
lemma `tendsto_Ico_neg_atTop_atTop` / 引理 `tendsto_Ico_neg_atTop_atTop`

English:
lemma tendsto_Ico_neg_atTop_atTop
  given: [NoTopOrder α]
  proof: tendsto_Ico_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

中文:
引理 tendsto_Ico_neg_atTop_atTop
  条件: [NoTopOrder α]
  证明: tendsto_Ico_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

Depends on / 依赖: prodMk, tendsto_Ico_atBot_prod_atTop, tendsto_Ico_atBot_prod_atTop.comp, tendsto_id, tendsto_neg_atTop_atBot, tendsto_neg_atTop_atBot.prodMk
-/
lemma tendsto_Ico_neg_atTop_atTop [NoTopOrder α] :
    Tendsto (fun a : α => Ico (-a) a) atTop atTop :=
  tendsto_Ico_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

/--
lemma `tendsto_Ioo_neg_atTop_atTop` / 引理 `tendsto_Ioo_neg_atTop_atTop`

English:
lemma tendsto_Ioo_neg_atTop_atTop
  given: [NoBotOrder α] [NoTopOrder α]
  proof: tendsto_Ioo_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

中文:
引理 tendsto_Ioo_neg_atTop_atTop
  条件: [NoBotOrder α] [NoTopOrder α]
  证明: tendsto_Ioo_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

Depends on / 依赖: prodMk, tendsto_Ioo_atBot_prod_atTop, tendsto_Ioo_atBot_prod_atTop.comp, tendsto_id, tendsto_neg_atTop_atBot, tendsto_neg_atTop_atBot.prodMk
-/
lemma tendsto_Ioo_neg_atTop_atTop [NoBotOrder α] [NoTopOrder α] :
    Tendsto (fun a : α => Ioo (-a) a) atTop atTop :=
  tendsto_Ioo_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

end Symmetric

section NatCast

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [LocallyFiniteOrder R]
  [Archimedean R]

/--
lemma `tendsto_Icc_neg` / 引理 `tendsto_Icc_neg`

English:
lemma tendsto_Icc_neg
  proof: tendsto_Icc_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

中文:
引理 tendsto_Icc_neg
  证明: tendsto_Icc_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

Depends on / 依赖: tendsto_Icc_neg_atTop_atTop, tendsto_Icc_neg_atTop_atTop.comp, tendsto_natCast_atTop_atTop
-/
lemma tendsto_Icc_neg :
    Tendsto (fun n : Nat => Icc (-n : R) n) atTop atTop :=
  tendsto_Icc_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

variable [Nontrivial R]

/--
lemma `tendsto_Ioc_neg` / 引理 `tendsto_Ioc_neg`

English:
lemma tendsto_Ioc_neg
  statement: Tendsto (fun n : Nat => Ioc (-n : R) n) atTop atTop
  proof: tendsto_Ioc_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

中文:
引理 tendsto_Ioc_neg
  结论: Tendsto (fun n : 自然数 => Ioc (-n : R) n) atTop atTop
  证明: tendsto_Ioc_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

Depends on / 依赖: tendsto_Ioc_neg_atTop_atTop, tendsto_Ioc_neg_atTop_atTop.comp, tendsto_natCast_atTop_atTop
-/
lemma tendsto_Ioc_neg : Tendsto (fun n : Nat => Ioc (-n : R) n) atTop atTop :=
  tendsto_Ioc_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

/--
lemma `tendsto_Ico_neg` / 引理 `tendsto_Ico_neg`

English:
lemma tendsto_Ico_neg
  statement: Tendsto (fun n : Nat => Ico (-n : R) n) atTop atTop
  proof: tendsto_Ico_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

中文:
引理 tendsto_Ico_neg
  结论: Tendsto (fun n : 自然数 => Ico (-n : R) n) atTop atTop
  证明: tendsto_Ico_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

Depends on / 依赖: tendsto_Ico_neg_atTop_atTop, tendsto_Ico_neg_atTop_atTop.comp, tendsto_natCast_atTop_atTop
-/
lemma tendsto_Ico_neg : Tendsto (fun n : Nat => Ico (-n : R) n) atTop atTop :=
  tendsto_Ico_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

/--
lemma `tendsto_Ioo_neg` / 引理 `tendsto_Ioo_neg`

English:
lemma tendsto_Ioo_neg
  statement: Tendsto (fun n : Nat => Ioo (-n : R) n) atTop atTop
  proof: tendsto_Ioo_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

中文:
引理 tendsto_Ioo_neg
  结论: Tendsto (fun n : 自然数 => Ioo (-n : R) n) atTop atTop
  证明: tendsto_Ioo_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

Depends on / 依赖: tendsto_Ioo_neg_atTop_atTop, tendsto_Ioo_neg_atTop_atTop.comp, tendsto_natCast_atTop_atTop
-/
lemma tendsto_Ioo_neg : Tendsto (fun n : Nat => Ioo (-n : R) n) atTop atTop :=
  tendsto_Ioo_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

end NatCast

end Finset
