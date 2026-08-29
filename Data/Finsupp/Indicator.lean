/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finsupp.Single

/-!
# Building finitely supported functions off finsets

This file defines `Finsupp.indicator` to help create finsupps from finsets.

## Main declarations

* `Finsupp.indicator`: Turns a map from a `Finset` into a `Finsupp` from the entire type.
-/

@[expose] public section


noncomputable section

open Finset Function

variable {ι α : Type*}

namespace Finsupp

variable [Zero α] {s t : Finset ι} (f : forall i in s, α) {i : ι}

/--
Definition of `indicator` / `indicator` 的定义

English:
definition indicator
  signature: (s : Finset ι) (f : forall i in s, α)
  body: haveI := Classical.decEq ι
    if H : i in s then f i H else 0
  support :=
    haveI := Classical.decEq α
    ({i | f i.1 i.2 != 0} : Finset s).map (Embedding.subtype _)
  mem_support_toFun i := by
    simp

中文:
定义 indicator
  签名: (s : 有限集 ι) (f : 对任意 i in s, α)
  定义体: haveI := Classical.decEq ι
    if H : i in s then f i H else 0
  support :=
    haveI := Classical.decEq α
    ({i | f i.1 i.2 != 0} : Finset s).map (Embedding.subtype _)
  mem_support_toFun i := by
    simp

Depends on / 依赖: Classical, Classical.decEq, Embedding, Embedding.subtype, Finset, mem_support_toFun, subtype, support
-/
def indicator (s : Finset ι) (f : forall i in s, α) : ι ->₀ α where
  toFun i :=
    haveI := Classical.decEq ι
    if H : i in s then f i H else 0
  support :=
    haveI := Classical.decEq α
    ({i | f i.1 i.2 != 0} : Finset s).map (Embedding.subtype _)
  mem_support_toFun i := by
    simp

/--
theorem `indicator_of_mem` / 定理 `indicator_of_mem`

English:
theorem indicator_of_mem
  given: (hi : i in s) (f : forall i in s, α)
  statement: indicator s f i = f i hi
  proof: @dif_pos _ (id _) hi _ _ _

中文:
定理 indicator_of_mem
  条件: (hi : i in s) (f : 对任意 i in s, α)
  结论: indicator s f i = f i hi
  证明: @dif_pos _ (id _) hi _ _ _

Depends on / 依赖: dif_pos
-/
theorem indicator_of_mem (hi : i in s) (f : forall i in s, α) : indicator s f i = f i hi :=
  @dif_pos _ (id _) hi _ _ _

/--
theorem `indicator_of_notMem` / 定理 `indicator_of_notMem`

English:
theorem indicator_of_notMem
  given: (hi : i ∉ s) (f : forall i in s, α)
  statement: indicator s f i = 0
  proof: @dif_neg _ (id _) hi _ _ _

中文:
定理 indicator_of_notMem
  条件: (hi : i ∉ s) (f : 对任意 i in s, α)
  结论: indicator s f i = 0
  证明: @dif_neg _ (id _) hi _ _ _

Depends on / 依赖: dif_neg
-/
theorem indicator_of_notMem (hi : i ∉ s) (f : forall i in s, α) : indicator s f i = 0 :=
  @dif_neg _ (id _) hi _ _ _

variable (s i)

@[simp]
/--
theorem `indicator_apply` / 定理 `indicator_apply`

English:
theorem indicator_apply
  given: [DecidableEq ι]
  statement: indicator s f i = if hi : i in s then f i hi else 0
  proof: by
  simp only [indicator, ne_eq, coe_mk]
  congr

中文:
定理 indicator_apply
  条件: [DecidableEq ι]
  结论: indicator s f i = if hi : i in s then f i hi else 0
  证明: by
  simp only [indicator, ne_eq, coe_mk]
  congr

Depends on / 依赖: coe_mk, indicator, ne_eq
-/
theorem indicator_apply [DecidableEq ι] : indicator s f i = if hi : i in s then f i hi else 0 := by
  simp only [indicator, ne_eq, coe_mk]
  congr

/--
theorem `indicator_injective` / 定理 `indicator_injective`

English:
theorem indicator_injective
  statement: Injective fun f : forall i in s, α => indicator s f
  proof: by
  intro a b h
  ext i hi
  rw [← indicator_of_mem hi a]; rw [← indicator_of_mem hi b]
  exact DFunLike.congr_fun h i

中文:
定理 indicator_injective
  结论: 单射 fun f : 对任意 i in s, α => indicator s f
  证明: by
  intro a b h
  ext i hi
  rw [← indicator_of_mem hi a]; rw [← indicator_of_mem hi b]
  exact DFunLike.congr_fun h i

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, indicator_of_mem
-/
theorem indicator_injective : Injective fun f : forall i in s, α => indicator s f := by
  intro a b h
  ext i hi
  rw [← indicator_of_mem hi a]; rw [← indicator_of_mem hi b]
  exact DFunLike.congr_fun h i

/--
theorem `support_indicator_subset` / 定理 `support_indicator_subset`

English:
theorem support_indicator_subset
  statement: (indicator s f).support subseteq s
  proof: by
  intro i hi
  rw [mem_support_iff] at hi
  by_contra h
  exact hi (indicator_of_notMem h _)

中文:
定理 support_indicator_subset
  结论: (indicator s f).support subseteq s
  证明: by
  intro i hi
  rw [mem_support_iff] at hi
  by_contra h
  exact hi (indicator_of_notMem h _)

Depends on / 依赖: indicator_of_notMem, mem_support_iff
-/
theorem support_indicator_subset : (indicator s f).support subseteq s := by
  intro i hi
  rw [mem_support_iff] at hi
  by_contra h
  exact hi (indicator_of_notMem h _)

/--
lemma `indicator_singleton` / 引理 `indicator_singleton`

English:
lemma indicator_singleton
  given: (a : ι) (f : forall j in ({a} : Finset ι), α)
  proof: by
  classical
  ext j
  simp only [single_apply, indicator_apply, mem_singleton, @eq_comm _ a j]
  split_ifs with h <;> simp [h]

@[deprecated indicator_singleton (since := "2026-04-27")]

中文:
引理 indicator_singleton
  条件: (a : ι) (f : 对任意 j in ({a} : 有限集 ι), α)
  证明: by
  classical
  ext j
  simp only [single_apply, indicator_apply, mem_singleton, @eq_comm _ a j]
  split_ifs with h <;> simp [h]

@[deprecated indicator_singleton (since := "2026-04-27")]

Depends on / 依赖: classical, eq_comm, indicator_apply, mem_singleton, single_apply, split_ifs
-/
lemma indicator_singleton (a : ι) (f : forall j in ({a} : Finset ι), α) :
    indicator {a} f = single a (f a (mem_singleton_self a)) := by
  classical
  ext j
  simp only [single_apply, indicator_apply, mem_singleton, @eq_comm _ a j]
  split_ifs with h <;> simp [h]

@[deprecated indicator_singleton (since := "2026-04-27")]
/--
lemma `single_eq_indicator` / 引理 `single_eq_indicator`

English:
lemma single_eq_indicator
  given: (b : α)
  statement: single i b = indicator {i} (fun _ _ => b)
  proof: (indicator_singleton i (fun _ _ => b)).symm

中文:
引理 single_eq_indicator
  条件: (b : α)
  结论: single i b = indicator {i} (fun _ _ => b)
  证明: (indicator_singleton i (fun _ _ => b)).symm

Depends on / 依赖: indicator_singleton
-/
lemma single_eq_indicator (b : α) : single i b = indicator {i} (fun _ _ => b) :=
  (indicator_singleton i (fun _ _ => b)).symm

/--
theorem `indicator_eq_set_indicator` / 定理 `indicator_eq_set_indicator`

English:
theorem indicator_eq_set_indicator
  given: (s : Finset ι) (g : ι -> α)
  proof: by
  classical
  ext i
  simp [indicator_apply, Set.indicator_apply]

中文:
定理 indicator_eq_set_indicator
  条件: (s : 有限集 ι) (g : ι -> α)
  证明: by
  classical
  ext i
  simp [indicator_apply, Set.indicator_apply]

Depends on / 依赖: Set.indicator_apply, classical, indicator_apply
-/
theorem indicator_eq_set_indicator (s : Finset ι) (g : ι -> α) :
    ⇑(indicator s (fun i _ => g i)) = Set.indicator ↑s g := by
  classical
  ext i
  simp [indicator_apply, Set.indicator_apply]

/--
theorem `indicator_indicator` / 定理 `indicator_indicator`

English:
theorem indicator_indicator
  given: [DecidableEq ι]
  proof: by
  grind [indicator_apply]

中文:
定理 indicator_indicator
  条件: [DecidableEq ι]
  证明: by
  grind [indicator_apply]

Depends on / 依赖: XgcdType, XgcdType.w, add_right_comm, indicator_apply
-/
theorem indicator_indicator [DecidableEq ι] :
    indicator t (fun i _ => indicator s f i) =
      indicator (s inter t) (fun i hi => f i (Finset.mem_of_mem_inter_left hi)) := by
  grind [indicator_apply]

/--
theorem `eq_indicator_iff` / 定理 `eq_indicator_iff`

English:
theorem eq_indicator_iff
  given: {g : ι -> α}
  proof: by
  classical
  suffices g.support subseteq s ∧ (forall i (hi : i in s), f i hi = g i) ↔
      (forall i, if hi : i in s then f i hi = g i else g i = 0) by
    simp only [this, funext_iff, indicator_apply]
    grind
  rw [Set.subset_def]; rw [and_comm]
  have : (forall (i : ι), if hi : i in s then 

中文:
定理 eq_indicator_iff
  条件: {g : ι -> α}
  证明: by
  classical
  suffices g.support subseteq s ∧ (forall i (hi : i in s), f i hi = g i) ↔
      (forall i, if hi : i in s then f i hi = g i else g i = 0) by
    simp only [this, funext_iff, indicator_apply]
    grind
  rw [Set.subset_def]; rw [and_comm]
  have : (forall (i : ι), if hi : i in s then 

Depends on / 依赖: Set.subset_def, XgcdType, XgcdType.z, add_assoc, and_comm, classical, funext_iff, g.support, indicator_apply, not_imp_comm, subset_def, subseteq, support
-/
theorem eq_indicator_iff {g : ι -> α} :
    g = indicator s f ↔ g.support subseteq s ∧ forall ⦃i⦄ (hi : i in s), f i hi = g i := by
  classical
  suffices g.support subseteq s ∧ (forall i (hi : i in s), f i hi = g i) ↔
      (forall i, if hi : i in s then f i hi = g i else g i = 0) by
    simp only [this, funext_iff, indicator_apply]
    grind
  rw [Set.subset_def]; rw [and_comm]
  have : (forall (i : ι), if hi : i in s then f i hi = g i else g i = 0) ↔
      ((forall (i : ι) (hi : i in s), f i hi = g i) ∧ forall i (hi : i ∉ s), g i = 0) := by grind
  simp [this, not_imp_comm]

/--
theorem `eq_indicator_self_iff` / 定理 `eq_indicator_self_iff`

English:
theorem eq_indicator_self_iff
  given: {d : ι ->₀ α}
  statement: (d = indicator s fun i _ => d i) ↔ d.support subseteq s
  proof: by
  grind [indicator]

中文:
定理 eq_indicator_self_iff
  条件: {d : ι ->₀ α}
  结论: (d = indicator s fun i _ => d i) ↔ d.support subseteq s
  证明: by
  grind [indicator]

Depends on / 依赖: indicator
-/
theorem eq_indicator_self_iff {d : ι ->₀ α} : (d = indicator s fun i _ => d i) ↔ d.support subseteq s := by
  grind [indicator]

end Finsupp
