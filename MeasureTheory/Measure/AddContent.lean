/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.SetSemiring
public import Mathlib.MeasureTheory.OuterMeasure.Induced
public import Mathlib.Tactic.FinCases

/-!
# Additive Contents

An additive content `m` on a set of sets `C` is a set function with value 0 at the empty set which
is finitely additive on `C`. That means that for any finset `I` of pairwise disjoint sets in `C`
such that `⋃₀ I ∈ C`, `m (⋃₀ I) = ∑ s ∈ I, m s`.

Mathlib also has a definition of contents over compact sets: see `MeasureTheory.Content`.
A `Content` is in particular an `AddContent` on the set of compact sets.

## Main definitions

* `MeasureTheory.AddContent G C`: additive contents over the set of sets `C` taking values in the
  additive monoid `G`.
* `MeasureTheory.AddContent.IsSigmaSubadditive`: an `AddContent` with values in `ℝ≥0∞` is
  σ-subadditive if `m (⋃ i, f i) ≤ ∑' i, m (f i)` for any sequence of sets `f` in `C`
  such that `⋃ i, f i ∈ C`.

## Main statements

Let `m` be an `AddContent C` with values in `ℝ≥0∞`. If `C` is a set semi-ring (`IsSetSemiring C`)
we have the properties

* `MeasureTheory.sum_addContent_le_of_subset`: if `I` is a finset of pairwise disjoint sets in `C`
  and `⋃₀ I ⊆ t` for `t ∈ C`, then `∑ s ∈ I, m s ≤ m t`.
* `MeasureTheory.addContent_mono`: if `s ⊆ t` for two sets in `C`, then `m s ≤ m t`.
* `MeasureTheory.addContent_sUnion_le_sum`: an `AddContent C` on a `SetSemiring C` is
  sub-additive.
* `MeasureTheory.addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le`: if an
  `AddContent` is σ-subadditive on a semi-ring of sets, then it is σ-additive.
* `MeasureTheory.addContent_union'`: if `s, t ∈ C` are disjoint and `s ∪ t ∈ C`,
  then `m (s ∪ t) = m s + m t`.
  If `C` is a set ring (`IsSetRing`), then `addContent_union` gives the same conclusion without the
  hypothesis `s ∪ t ∈ C` (since it is a consequence of `IsSetRing C`).

If `C` is a set ring (`MeasureTheory.IsSetRing C`), we have

* `MeasureTheory.addContent_union_le`: for `s, t ∈ C`, `m (s ∪ t) ≤ m s + m t`
* `MeasureTheory.addContent_le_sdiff`: for `s, t ∈ C`, `m s - m t ≤ m (s \ t)`
* `IsSetRing.addContent_of_union`: a function on a ring of sets which is additive on pairs of
  disjoint sets defines an additive content
* `addContent_iUnion_eq_sum_of_tendsto_zero`: if an additive content is continuous at `∅`, then
  its value on a countable disjoint union is the sum of the values
* `MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum`: if an `AddContent` is
  σ-additive on a set ring, then it is σ-subadditive.

We define a specific example of `AddContent`, called `AddContent.onIoc`, on the semiring of sets
made of open-closed intervals, mapping `(a, b]` to `f b - f a`.
-/

@[expose] public section

open Set Finset Function Filter

open scoped ENNReal Topology Function

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α} {I : Finset (Set α)}
  {G : Type*} [AddCommMonoid G]

variable (G) in
/--
Definition of `AddContent` / `AddContent` 的定义

English:
structure AddContent
  parameters: (C : Set (Set α))
  axioms and operations (3):
    - toFun : Set α -> G
    - empty' : toFun ∅ = 0
    - sUnion'((I : Finset (Set α)) (_h_ss : ↑I subseteq C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id) (_h_mem : ⋃₀ ↑I in C)) : toFun (⋃₀ I) = ∑ u in I, toFun u

中文:
结构 加法内容
  参数: (C : 集合 (集合 α))
  公理与运算 (3 个):
    - toFun : 集合 α -> G
    - empty' : toFun ∅ = 0
    - sUnion'((I : 有限集 (集合 α)) (_h_ss : ↑I subseteq C) (_h_dis : PairwiseDisjoint (I : 集合 (集合 α)) id) (_h_mem : ⋃₀ ↑I in C)) : toFun (⋃₀ I) = ∑ u in I, toFun u
-/
structure AddContent (C : Set (Set α)) where
  /-- The value of the content on a set. -/
  toFun : Set α -> G
  empty' : toFun ∅ = 0
  sUnion' (I : Finset (Set α)) (_h_ss : ↑I subseteq C)
      (_h_dis : PairwiseDisjoint (I : Set (Set α)) id) (_h_mem : ⋃₀ ↑I in C) :
    toFun (⋃₀ I) = ∑ u in I, toFun u

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (AddContent G C)
  body: ⟨{toFun := fun _ => 0
    empty' := by simp
    sUnion' := by simp }⟩

中文:
实例 :
  签名: 可居 (加法内容 G C)
  定义体: ⟨{toFun := fun _ => 0
    empty' := by simp
    sUnion' := by simp }⟩

Depends on / 依赖: sUnion
-/
instance : Inhabited (AddContent G C) :=
  ⟨{toFun := fun _ => 0
    empty' := by simp
    sUnion' := by simp }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (AddContent G C) (Set α) G
  body: m.toFun s
  coe_injective m m' _ := by
    cases m
    cases m'
    congr

中文:
实例 :
  签名: 函数状 (加法内容 G C) (集合 α) G
  定义体: m.toFun s
  coe_injective m m' _ := by
    cases m
    cases m'
    congr

Depends on / 依赖: m.toFun
-/
instance : FunLike (AddContent G C) (Set α) G where
  coe m s := m.toFun s
  coe_injective m m' _ := by
    cases m
    cases m'
    congr

variable {m m' : AddContent G C}

/--
lemma `AddContent.ext` / 引理 `AddContent.ext`

English:
lemma AddContent.ext
  given: (h : forall s, m s = m' s)
  statement: m = m'
  proof: DFunLike.ext _ _ h

中文:
引理 加法内容.ext
  条件: (h : 对任意 s, m s = m' s)
  结论: m = m'
  证明: DFunLike.ext _ _ h
-/
@[ext] protected lemma AddContent.ext (h : forall s, m s = m' s) : m = m' :=
  DFunLike.ext _ _ h

/--
lemma `addContent_empty` / 引理 `addContent_empty`

English:
lemma addContent_empty
  statement: m ∅ = 0
  proof: m.empty'

中文:
引理 addContent_empty
  结论: m ∅ = 0
  证明: m.empty'
-/
@[simp] lemma addContent_empty : m ∅ = 0 := m.empty'

/--
lemma `addContent_sUnion` / 引理 `addContent_sUnion`

English:
lemma addContent_sUnion
  statement: (h_ss : ↑I subseteq C)
  proof: m.sUnion' I h_ss h_dis h_mem

中文:
引理 addContent_sUnion
  结论: (h_ss : ↑I subseteq C)
  证明: m.sUnion' I h_ss h_dis h_mem

Depends on / 依赖: h_dis, h_mem, h_ss, m.sUnion, sUnion
-/
lemma addContent_sUnion (h_ss : ↑I subseteq C)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) (h_mem : ⋃₀ ↑I in C) :
    m (⋃₀ I) = ∑ u in I, m u :=
  m.sUnion' I h_ss h_dis h_mem

/--
lemma `addContent_biUnion` / 引理 `addContent_biUnion`

English:
lemma addContent_biUnion
  statement: {ι : Type*} {a : Finset ι} {f : ι -> Set α} (hf : forall i in a, f i in C)
  proof: by
  have A : ⋃ i in a, f i = ⋃₀ (a.image f) := by simp
  rw [A]; rw [addContent_sUnion]; rotate_left
  · grind
  · simpa using! h_dis.image
  · rwa [← A]
  rw [sum_image_of_pairwise_eq_zero]
  refine h_dis.imp ?_
  grind [Set.bot_eq_empty (α := α), addContent_empty]

中文:
引理 addContent_biUnion
  结论: {ι : 类型} {a : 有限集 ι} {f : ι -> 集合 α} (hf : 对任意 i in a, f i in C)
  证明: by
  have A : ⋃ i in a, f i = ⋃₀ (a.image f) := by simp
  rw [A]; rw [addContent_sUnion]; rotate_left
  · grind
  · simpa using! h_dis.image
  · rwa [← A]
  rw [sum_image_of_pairwise_eq_zero]
  refine h_dis.imp ?_
  grind [Set.bot_eq_empty (α := α), addContent_empty]

Depends on / 依赖: Set.bot_eq_empty, a.image, addContent_empty, addContent_sUnion, bot_eq_empty, h_dis, h_dis.image, h_dis.imp, rotate_left, sum_image_of_pairwise_eq_zero
-/
lemma addContent_biUnion {ι : Type*} {a : Finset ι} {f : ι -> Set α} (hf : forall i in a, f i in C)
    (h_dis : PairwiseDisjoint ↑a f) (h_mem : ⋃ i in a, f i in C) :
    m (⋃ i in a, f i) = ∑ i in a, m (f i) := by
  have A : ⋃ i in a, f i = ⋃₀ (a.image f) := by simp
  rw [A]; rw [addContent_sUnion]; rotate_left
  · grind
  · simpa using! h_dis.image
  · rwa [← A]
  rw [sum_image_of_pairwise_eq_zero]
  refine h_dis.imp ?_
  grind [Set.bot_eq_empty (α := α), addContent_empty]

/--
lemma `addContent_iUnion` / 引理 `addContent_iUnion`

English:
lemma addContent_iUnion
  statement: {ι : Type*} [Fintype ι] {f : ι -> Set α} (hf : forall i, f i in C)
  proof: by
  convert! addContent_biUnion (a := Finset.univ) (f := f) (m := m) ?_ ?_ ?_ using 1
  · simp
  · simpa
  · simpa [Set.PairwiseDisjoint, Set.pairwise_univ] using h_dis
  · simpa

中文:
引理 addContent_iUnion
  结论: {ι : 类型} [有限类型 ι] {f : ι -> 集合 α} (hf : 对任意 i, f i in C)
  证明: by
  convert! addContent_biUnion (a := Finset.univ) (f := f) (m := m) ?_ ?_ ?_ using 1
  · simp
  · simpa
  · simpa [Set.PairwiseDisjoint, Set.pairwise_univ] using h_dis
  · simpa

Depends on / 依赖: Finset, Finset.univ, PairwiseDisjoint, Set.PairwiseDisjoint, Set.pairwise_univ, addContent_biUnion, convert, h_dis, pairwise_univ
-/
lemma addContent_iUnion {ι : Type*} [Fintype ι] {f : ι -> Set α} (hf : forall i, f i in C)
    (h_dis : Pairwise (Disjoint on f)) (h_mem : ⋃ i, f i in C) :
    m (⋃ i, f i) = ∑ i, m (f i) := by
  convert! addContent_biUnion (a := Finset.univ) (f := f) (m := m) ?_ ?_ ?_ using 1
  · simp
  · simpa
  · simpa [Set.PairwiseDisjoint, Set.pairwise_univ] using h_dis
  · simpa

/--
lemma `addContent_union'` / 引理 `addContent_union'`

English:
lemma addContent_union'
  given: (hs : s in C) (ht : t in C) (hst : s union t in C) (h_dis : Disjoint s t)
  proof: by
  have A : s union t = ⋃ i, ![s, t] i := by ext; simp
  convert! addContent_iUnion (f := ![s, t]) (m := m) (fun i => ?_) (fun i j hij => ?_) ?_ using 2
  · simp [Fin.univ_castSuccEmb, add_comm]
  · fin_cases i <;> simpa
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed all four
    cases. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
    the new canonicalizer; a minimization would help. The original proof was:
    `fin_cases i <;> fin_cases j <;> grind` -/
    fin_cases i <;> fin_cases j
    · grind
    · assumption
    · exact h_dis.symm
    · grind
  · rwa [← A]

中文:
引理 addContent_union'
  条件: (hs : s in C) (ht : t in C) (hst : s union t in C) (h_dis : Disjoint s t)
  证明: by
  have A : s union t = ⋃ i, ![s, t] i := by ext; simp
  convert! addContent_iUnion (f := ![s, t]) (m := m) (fun i => ?_) (fun i j hij => ?_) ?_ using 2
  · simp [Fin.univ_castSuccEmb, add_comm]
  · fin_cases i <;> simpa
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed all four
    cases. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
    the new canonicalizer; a minimization would help. The original proof was:
    `fin_cases i <;> fin_cases j <;> grind` -/
    fin_cases i <;> fin_cases j
    · grind
    · assumption
    · exact h_dis.symm
    · grind
  · rwa [← A]

Depends on / 依赖: Before, Fin.univ_castSuccEmb, Mathlib, adaptation_note, addContent_iUnion, add_comm, canonicalizer, closed, convert, directed, fin_cases, github, github.com, leanprover, normalizer, problem, replacing, univ_castSuccEmb, whether
-/
lemma addContent_union' (hs : s in C) (ht : t in C) (hst : s union t in C) (h_dis : Disjoint s t) :
    m (s union t) = m s + m t := by
  have A : s union t = ⋃ i, ![s, t] i := by ext; simp
  convert! addContent_iUnion (f := ![s, t]) (m := m) (fun i => ?_) (fun i j hij => ?_) ?_ using 2
  · simp [Fin.univ_castSuccEmb, add_comm]
  · fin_cases i <;> simpa
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed all four
    cases. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
    the new canonicalizer; a minimization would help. The original proof was:
    `fin_cases i <;> fin_cases j <;> grind` -/
    fin_cases i <;> fin_cases j
    · grind
    · assumption
    · exact h_dis.symm
    · grind
  · rwa [← A]

/--
Definition of `AddContent.IsSigmaSubadditive` / `AddContent.IsSigmaSubadditive` 的定义

English:
definition AddContent.IsSigmaSubadditive
  signature: (m : AddContent Real>=0∞ C)
  body: forall ⦃f : Nat -> Set α⦄ (_hf : forall i, f i in C) (_hf_Union : (⋃ i, f i) in C), m (⋃ i, f i) <= ∑' i, m (f i)

中文:
定义 加法内容.IsSigmaSubadditive
  签名: (m : 加法内容 实数>=0∞ C)
  定义体: forall ⦃f : Nat -> Set α⦄ (_hf : forall i, f i in C) (_hf_Union : (⋃ i, f i) in C), m (⋃ i, f i) <= ∑' i, m (f i)

Depends on / 依赖: _hf_Union
-/
def AddContent.IsSigmaSubadditive (m : AddContent Real>=0∞ C) : Prop :=
  forall ⦃f : Nat -> Set α⦄ (_hf : forall i, f i in C) (_hf_Union : (⋃ i, f i) in C), m (⋃ i, f i) <= ∑' i, m (f i)

section IsSetSemiring

/--
lemma `addContent_eq_add_disjointOfDiffUnion_of_subset` / 引理 `addContent_eq_add_disjointOfDiffUnion_of_subset`

English:
lemma addContent_eq_add_disjointOfDiffUnion_of_subset
  statement: (hC : IsSetSemiring C)
  proof: by
  conv_lhs => rw [← hC.sUnion_union_disjointOfDiffUnion_of_subset hs hI hI_ss]
  rw [addContent_sUnion]
  · rw [sum_union]
    exact hC.disjoint_disjointOfDiffUnion hs hI
  · rw [coe_union]
    exact Set.union_subset hI (hC.disjointOfDiffUnion_subset hs hI)
  · rw [coe_union]
    exact hC.pairwiseDisjoint_union_disjointOfDiffUnion hs hI h_dis
  · rwa [hC.sUnion_union_disjointOfDiffUnion_of_subset hs hI hI_ss]

中文:
引理 addContent_eq_add_disjointOfDiffUnion_of_subset
  结论: (hC : 是SetSemiring C)
  证明: by
  conv_lhs => rw [← hC.sUnion_union_disjointOfDiffUnion_of_subset hs hI hI_ss]
  rw [addContent_sUnion]
  · rw [sum_union]
    exact hC.disjoint_disjointOfDiffUnion hs hI
  · rw [coe_union]
    exact Set.union_subset hI (hC.disjointOfDiffUnion_subset hs hI)
  · rw [coe_union]
    exact hC.pairwiseDisjoint_union_disjointOfDiffUnion hs hI h_dis
  · rwa [hC.sUnion_union_disjointOfDiffUnion_of_subset hs hI hI_ss]

Depends on / 依赖: Set.union_subset, addContent_sUnion, coe_union, conv_lhs, disjointOfDiffUnion_subset, disjoint_disjointOfDiffUnion, hC.disjointOfDiffUnion_subset, hC.disjoint_disjointOfDiffUnion, hC.pairwiseDisjoint_union_disjointOfDiffUnion, hC.sUnion_union_disjointOfDiffUnion_of_subset, hI_ss, h_dis, pairwiseDisjoint_union_disjointOfDiffUnion, sUnion_union_disjointOfDiffUnion_of_subset, sum_union, union_subset
-/
lemma addContent_eq_add_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C)
    (hs : s in C) (hI : ↑I subseteq C) (hI_ss : forall t in I, t subseteq s)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) :
    m s = ∑ i in I, m i + ∑ i in hC.disjointOfDiffUnion hs hI, m i := by
  conv_lhs => rw [← hC.sUnion_union_disjointOfDiffUnion_of_subset hs hI hI_ss]
  rw [addContent_sUnion]
  · rw [sum_union]
    exact hC.disjoint_disjointOfDiffUnion hs hI
  · rw [coe_union]
    exact Set.union_subset hI (hC.disjointOfDiffUnion_subset hs hI)
  · rw [coe_union]
    exact hC.pairwiseDisjoint_union_disjointOfDiffUnion hs hI h_dis
  · rwa [hC.sUnion_union_disjointOfDiffUnion_of_subset hs hI hI_ss]

/--
theorem `eq_add_disjointOfDiff_of_subset` / 定理 `eq_add_disjointOfDiff_of_subset`

English:
theorem eq_add_disjointOfDiff_of_subset
  statement: (hC : IsSetSemiring C)
  proof: by
  conv_lhs => rw [← hC.sUnion_insert_disjointOfDiff ht hs hst]
  rw [← coe_insert]; rw [addContent_sUnion]
  · rw [sum_insert]
    exact hC.notMem_disjointOfDiff ht hs
  · rw [coe_insert]
    exact Set.insert_subset hs (hC.subset_disjointOfDiff ht hs)
  · rw [coe_insert]
    exact hC.pairwiseDisjoint_insert_disjointOfDiff ht hs
  · rw [coe_insert]
    rwa [hC.sUnion_insert_disjointOfDiff ht hs hst]

中文:
定理 eq_add_disjointOfDiff_of_subset
  结论: (hC : 是SetSemiring C)
  证明: by
  conv_lhs => rw [← hC.sUnion_insert_disjointOfDiff ht hs hst]
  rw [← coe_insert]; rw [addContent_sUnion]
  · rw [sum_insert]
    exact hC.notMem_disjointOfDiff ht hs
  · rw [coe_insert]
    exact Set.insert_subset hs (hC.subset_disjointOfDiff ht hs)
  · rw [coe_insert]
    exact hC.pairwiseDisjoint_insert_disjointOfDiff ht hs
  · rw [coe_insert]
    rwa [hC.sUnion_insert_disjointOfDiff ht hs hst]

Depends on / 依赖: Set.insert_subset, addContent_sUnion, coe_insert, conv_lhs, hC.notMem_disjointOfDiff, hC.pairwiseDisjoint_insert_disjointOfDiff, hC.sUnion_insert_disjointOfDiff, hC.subset_disjointOfDiff, insert_subset, notMem_disjointOfDiff, pairwiseDisjoint_insert_disjointOfDiff, sUnion_insert_disjointOfDiff, subset_disjointOfDiff, sum_insert
-/
theorem eq_add_disjointOfDiff_of_subset (hC : IsSetSemiring C)
    (hs : s in C) (ht : t in C) (hst : s subseteq t) :
    m t = m s + ∑ i in hC.disjointOfDiff ht hs, m i := by
  conv_lhs => rw [← hC.sUnion_insert_disjointOfDiff ht hs hst]
  rw [← coe_insert]; rw [addContent_sUnion]
  · rw [sum_insert]
    exact hC.notMem_disjointOfDiff ht hs
  · rw [coe_insert]
    exact Set.insert_subset hs (hC.subset_disjointOfDiff ht hs)
  · rw [coe_insert]
    exact hC.pairwiseDisjoint_insert_disjointOfDiff ht hs
  · rw [coe_insert]
    rwa [hC.sUnion_insert_disjointOfDiff ht hs hst]

/--
theorem `sum_addContent_eq_of_sUnion_eq` / 定理 `sum_addContent_eq_of_sUnion_eq`

English:
theorem sum_addContent_eq_of_sUnion_eq
  statement: (hC : IsSetSemiring C) (J J' : Finset (Set α))
  proof: by
  calc ∑ s in J, m s
  _ = ∑ s in J, (∑ t in J', m (s inter t)) := by
    apply Finset.sum_congr rfl (fun s hs => ?_)
    have : s = ⋃ t in J', s inter t := by
      simp_rw [← Finset.set_biUnion_coe, ← inter_iUnion, left_eq_inter, ← sUnion_eq_biUnion, ← h]
      exact subset_sUnion_of_mem hs
    nth_rewrite 1 [this]
    apply addContent_biUnion
    · exact fun t ht => hC.inter_mem _ (hJ hs) _ (hJ' ht)
    · exact hJ'disj.mono fun _ => by simp
    · rw [← this]
      exact hJ hs
  _ = ∑ t in J', (∑ s in J, m (s inter t)) := sum_comm
  _ = ∑ t in J', m t := by
    apply Finset.sum_congr rfl (fun t ht => ?_)
    have : t = ⋃ s in J, s inter t := by
      simp_rw [← Finset.set_biUnion_coe, ← iUnion_inter, right_eq_inter, ← sUnion_eq_biUnion, h]
      exact subset_sUnion_of_mem ht
    nth_rewrite 2 [this]
    apply (addContent_biUnion _ _ _).symm
    · exact fun s hs => hC.inter_mem _ (hJ hs) _ (hJ' ht)
    · exact hJdisj.mono fun _ => by simp
    · rw [← this]
      exact hJ' ht

中文:
定理 sum_addContent_eq_of_sUnion_eq
  结论: (hC : 是SetSemiring C) (J J' : 有限集 (集合 α))
  证明: by
  calc ∑ s in J, m s
  _ = ∑ s in J, (∑ t in J', m (s inter t)) := by
    apply Finset.sum_congr rfl (fun s hs => ?_)
    have : s = ⋃ t in J', s inter t := by
      simp_rw [← Finset.set_biUnion_coe, ← inter_iUnion, left_eq_inter, ← sUnion_eq_biUnion, ← h]
      exact subset_sUnion_of_mem hs
    nth_rewrite 1 [this]
    apply addContent_biUnion
    · exact fun t ht => hC.inter_mem _ (hJ hs) _ (hJ' ht)
    · exact hJ'disj.mono fun _ => by simp
    · rw [← this]
      exact hJ hs
  _ = ∑ t in J', (∑ s in J, m (s inter t)) := sum_comm
  _ = ∑ t in J', m t := by
    apply Finset.sum_congr rfl (fun t ht => ?_)
    have : t = ⋃ s in J, s inter t := by
      simp_rw [← Finset.set_biUnion_coe, ← iUnion_inter, right_eq_inter, ← sUnion_eq_biUnion, h]
      exact subset_sUnion_of_mem ht
    nth_rewrite 2 [this]
    apply (addContent_biUnion _ _ _).symm
    · exact fun s hs => hC.inter_mem _ (hJ hs) _ (hJ' ht)
    · exact hJdisj.mono fun _ => by simp
    · rw [← this]
      exact hJ' ht

Depends on / 依赖: Finset, Finset.set_biUnion_coe, Finset.sum_congr, addContent_biUnion, disj.mono, hC.inter_mem, inter_iUnion, inter_mem, left_eq_inter, nth_rewrite, sUnion_eq_biUnion, set_biUnion_coe, simp_rw, subset_sUnion_of_mem, sum_comm, sum_congr
-/
theorem sum_addContent_eq_of_sUnion_eq (hC : IsSetSemiring C) (J J' : Finset (Set α))
    (hJ : ↑J subseteq C) (hJdisj : PairwiseDisjoint (J : Set (Set α)) id)
    (hJ' : ↑J' subseteq C) (hJ'disj : PairwiseDisjoint (J' : Set (Set α)) id)
    (h : ⋃₀ (J : Set (Set α)) = ⋃₀ J') :
    ∑ s in J, m s = ∑ t in J', m t := by
  calc ∑ s in J, m s
  _ = ∑ s in J, (∑ t in J', m (s inter t)) := by
    apply Finset.sum_congr rfl (fun s hs => ?_)
    have : s = ⋃ t in J', s inter t := by
      simp_rw [← Finset.set_biUnion_coe, ← inter_iUnion, left_eq_inter, ← sUnion_eq_biUnion, ← h]
      exact subset_sUnion_of_mem hs
    nth_rewrite 1 [this]
    apply addContent_biUnion
    · exact fun t ht => hC.inter_mem _ (hJ hs) _ (hJ' ht)
    · exact hJ'disj.mono fun _ => by simp
    · rw [← this]
      exact hJ hs
  _ = ∑ t in J', (∑ s in J, m (s inter t)) := sum_comm
  _ = ∑ t in J', m t := by
    apply Finset.sum_congr rfl (fun t ht => ?_)
    have : t = ⋃ s in J, s inter t := by
      simp_rw [← Finset.set_biUnion_coe, ← iUnion_inter, right_eq_inter, ← sUnion_eq_biUnion, h]
      exact subset_sUnion_of_mem ht
    nth_rewrite 2 [this]
    apply (addContent_biUnion _ _ _).symm
    · exact fun s hs => hC.inter_mem _ (hJ hs) _ (hJ' ht)
    · exact hJdisj.mono fun _ => by simp
    · rw [← this]
      exact hJ' ht

open scoped Classical in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def AddContent.supClosureFun (m : AddContent G C) (s : Set α)
  body: if h : exists (J : Finset (Set α)), ↑J subseteq C ∧ (PairwiseDisjoint (J : Set (Set α)) id) ∧ s = ⋃₀ ↑J
    then ∑ s in h.choose, m s
  else 0

中文:
定义 noncomputable
  签名: def 加法内容.supClosureFun (m : 加法内容 G C) (s : 集合 α)
  定义体: if h : exists (J : Finset (Set α)), ↑J subseteq C ∧ (PairwiseDisjoint (J : Set (Set α)) id) ∧ s = ⋃₀ ↑J
    then ∑ s in h.choose, m s
  else 0
-/
private noncomputable def AddContent.supClosureFun (m : AddContent G C) (s : Set α) : G :=
  if h : exists (J : Finset (Set α)), ↑J subseteq C ∧ (PairwiseDisjoint (J : Set (Set α)) id) ∧ s = ⋃₀ ↑J
    then ∑ s in h.choose, m s
  else 0

/--
lemma `AddContent.supClosureFun_apply` / 引理 `AddContent.supClosureFun_apply`

English:
lemma AddContent.supClosureFun_apply
  statement: (hC : IsSetSemiring C)
  proof: by
  have h : exists (J : Finset (Set α)), ↑J subseteq C ∧ (PairwiseDisjoint (J : Set (Set α)) id) ∧ s = ⋃₀ ↑J :=
    ⟨J, hJ, h'J, hs⟩
  simp only [supClosureFun, h, ↓reduceDIte]
  apply sum_addContent_eq_of_sUnion_eq hC _ _ h.choose_spec.1 h.choose_spec.2.1 hJ h'J
  rw [← hs]
  exact h.choose_spec.2.2.symm

中文:
引理 加法内容.supClosureFun_apply
  结论: (hC : 是SetSemiring C)
  证明: by
  have h : exists (J : Finset (Set α)), ↑J subseteq C ∧ (PairwiseDisjoint (J : Set (Set α)) id) ∧ s = ⋃₀ ↑J :=
    ⟨J, hJ, h'J, hs⟩
  simp only [supClosureFun, h, ↓reduceDIte]
  apply sum_addContent_eq_of_sUnion_eq hC _ _ h.choose_spec.1 h.choose_spec.2.1 hJ h'J
  rw [← hs]
  exact h.choose_spec.2.2.symm
-/
private lemma AddContent.supClosureFun_apply (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} {J : Finset (Set α)}
    (hJ : ↑J subseteq C) (h'J : PairwiseDisjoint (J : Set (Set α)) id) (hs : s = ⋃₀ ↑J) :
    m.supClosureFun s = ∑ s in J, m s := by
  have h : exists (J : Finset (Set α)), ↑J subseteq C ∧ (PairwiseDisjoint (J : Set (Set α)) id) ∧ s = ⋃₀ ↑J :=
    ⟨J, hJ, h'J, hs⟩
  simp only [supClosureFun, h, ↓reduceDIte]
  apply sum_addContent_eq_of_sUnion_eq hC _ _ h.choose_spec.1 h.choose_spec.2.1 hJ h'J
  rw [← hs]
  exact h.choose_spec.2.2.symm

/--
lemma `AddContent.supClosureFun_apply_of_mem` / 引理 `AddContent.supClosureFun_apply_of_mem`

English:
lemma AddContent.supClosureFun_apply_of_mem
  statement: (hC : IsSetSemiring C)
  proof: by
  have : m.supClosureFun s = ∑ t in {s}, m t :=
    m.supClosureFun_apply hC (by simp [hs]) (by simp) (by simp)
  simp [this]

中文:
引理 加法内容.supClosureFun_apply_of_mem
  结论: (hC : 是SetSemiring C)
  证明: by
  have : m.supClosureFun s = ∑ t in {s}, m t :=
    m.supClosureFun_apply hC (by simp [hs]) (by simp) (by simp)
  simp [this]
-/
private lemma AddContent.supClosureFun_apply_of_mem (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} (hs : s in C) :
    m.supClosureFun s = m s := by
  have : m.supClosureFun s = ∑ t in {s}, m t :=
    m.supClosureFun_apply hC (by simp [hs]) (by simp) (by simp)
  simp [this]

/--
Definition of `AddContent.supClosure` / `AddContent.supClosure` 的定义

English:
definition AddContent.supClosure
  signature: (m : AddContent G C) (hC : IsSetSemiring C)
  body: m.supClosureFun
  empty' := by rw [m.supClosureFun_apply_of_mem hC hC.empty_mem, addContent_empty]
  sUnion' I hI h'I hh'I := by
    choose! J hJC using fun s (hs : s in I) => hC.mem_supClosure_iff.mp (hI hs)
    let K : Finpartition (I.sup id) := Finpartition.combine J h'I.supIndep
    rw [← sSup_eq_sUnion]; rw [← sup_id_eq_sSup]; rw [← K.sup_parts]; rw [sup_id_eq_sSup]; rw [sSup_eq_sUnion]; rw [m.supClosureFun_apply hC (by simpa [K] using hJC) K.supIndep.pairwiseDisjoint rfl,
      Finpartition.sum_combine]
refine Finset.sum_congr rfl fun i hi => Eq.symm
      m.supClosureFun_apply hC (hJC i hi) (J i).supIndep.pairwiseDisjoint ?_
    rw [← sSup_eq_sUnion]; rw [← sup_id_eq_sSup]; rw [(J i).sup_parts]

中文:
定义 加法内容.supClosure
  签名: (m : 加法内容 G C) (hC : 是SetSemiring C)
  定义体: m.supClosureFun
  empty' := by rw [m.supClosureFun_apply_of_mem hC hC.empty_mem, addContent_empty]
  sUnion' I hI h'I hh'I := by
    choose! J hJC using fun s (hs : s in I) => hC.mem_supClosure_iff.mp (hI hs)
    let K : Finpartition (I.sup id) := Finpartition.combine J h'I.supIndep
    rw [← sSup_eq_sUnion]; rw [← sup_id_eq_sSup]; rw [← K.sup_parts]; rw [sup_id_eq_sSup]; rw [sSup_eq_sUnion]; rw [m.supClosureFun_apply hC (by simpa [K] using hJC) K.supIndep.pairwiseDisjoint rfl,
      Finpartition.sum_combine]
refine Finset.sum_congr rfl fun i hi => Eq.symm
      m.supClosureFun_apply hC (hJC i hi) (J i).supIndep.pairwiseDisjoint ?_
    rw [← sSup_eq_sUnion]; rw [← sup_id_eq_sSup]; rw [(J i).sup_parts]
-/
@[no_expose] noncomputable def AddContent.supClosure (m : AddContent G C) (hC : IsSetSemiring C) :
    AddContent G (supClosure C) where
  toFun := m.supClosureFun
  empty' := by rw [m.supClosureFun_apply_of_mem hC hC.empty_mem, addContent_empty]
  sUnion' I hI h'I hh'I := by
    choose! J hJC using fun s (hs : s in I) => hC.mem_supClosure_iff.mp (hI hs)
    let K : Finpartition (I.sup id) := Finpartition.combine J h'I.supIndep
    rw [← sSup_eq_sUnion]; rw [← sup_id_eq_sSup]; rw [← K.sup_parts]; rw [sup_id_eq_sSup]; rw [sSup_eq_sUnion]; rw [m.supClosureFun_apply hC (by simpa [K] using hJC) K.supIndep.pairwiseDisjoint rfl,
      Finpartition.sum_combine]
refine Finset.sum_congr rfl fun i hi => Eq.symm
      m.supClosureFun_apply hC (hJC i hi) (J i).supIndep.pairwiseDisjoint ?_
    rw [← sSup_eq_sUnion]; rw [← sup_id_eq_sSup]; rw [(J i).sup_parts]

/--
lemma `AddContent.supClosure_apply` / 引理 `AddContent.supClosure_apply`

English:
lemma AddContent.supClosure_apply
  statement: (hC : IsSetSemiring C)
  proof: m.supClosureFun_apply hC hJ h'J hs

中文:
引理 加法内容.supClosure_apply
  结论: (hC : 是SetSemiring C)
  证明: m.supClosureFun_apply hC hJ h'J hs

Depends on / 依赖: m.supClosureFun_apply, supClosureFun_apply
-/
lemma AddContent.supClosure_apply (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} {J : Finset (Set α)}
    (hJ : ↑J subseteq C) (h'J : PairwiseDisjoint (J : Set (Set α)) id) (hs : s = ⋃₀ ↑J) :
    m.supClosure hC s = ∑ s in J, m s :=
  m.supClosureFun_apply hC hJ h'J hs

/--
lemma `AddContent.supClosure_apply_finpartition` / 引理 `AddContent.supClosure_apply_finpartition`

English:
lemma AddContent.supClosure_apply_finpartition
  statement: (hC : IsSetSemiring C)
  proof: by
  rw [m.supClosure_apply _ hJ J.disjoint]
  nth_rewrite 1 [← J.sup_parts, Finset.sup_set_eq_biUnion, sUnion_eq_biUnion]
  simp

中文:
引理 加法内容.supClosure_apply_finpartition
  结论: (hC : 是SetSemiring C)
  证明: by
  rw [m.supClosure_apply _ hJ J.disjoint]
  nth_rewrite 1 [← J.sup_parts, Finset.sup_set_eq_biUnion, sUnion_eq_biUnion]
  simp

Depends on / 依赖: Finset, Finset.sup_set_eq_biUnion, J.disjoint, J.sup_parts, disjoint, m.supClosure_apply, nth_rewrite, sUnion_eq_biUnion, supClosure_apply, sup_parts, sup_set_eq_biUnion
-/
lemma AddContent.supClosure_apply_finpartition (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} {J : Finpartition s} (hJ : ↑J.parts subseteq C) :
    m.supClosure hC s = ∑ s in J.parts, m s := by
  rw [m.supClosure_apply _ hJ J.disjoint]
  nth_rewrite 1 [← J.sup_parts, Finset.sup_set_eq_biUnion, sUnion_eq_biUnion]
  simp

/--
lemma `AddContent.supClosure_apply_of_mem` / 引理 `AddContent.supClosure_apply_of_mem`

English:
lemma AddContent.supClosure_apply_of_mem
  statement: (hC : IsSetSemiring C)
  proof: m.supClosureFun_apply_of_mem hC hs

中文:
引理 加法内容.supClosure_apply_of_mem
  结论: (hC : 是SetSemiring C)
  证明: m.supClosureFun_apply_of_mem hC hs

Depends on / 依赖: m.supClosureFun_apply_of_mem, supClosureFun_apply_of_mem
-/
lemma AddContent.supClosure_apply_of_mem (hC : IsSetSemiring C)
    (m : AddContent G C) {s : Set α} (hs : s in C) :
    m.supClosure hC s = m s :=
  m.supClosureFun_apply_of_mem hC hs

variable [PartialOrder G] [CanonicallyOrderedAdd G]

/--
lemma `sum_addContent_le_of_subset` / 引理 `sum_addContent_le_of_subset`

English:
lemma sum_addContent_le_of_subset
  statement: (hC : IsSetSemiring C)
  proof: by
  rw [addContent_eq_add_disjointOfDiffUnion_of_subset hC ht h_ss hJt h_dis]
  exact le_add_right le_rfl

中文:
引理 sum_addContent_le_of_subset
  结论: (hC : 是SetSemiring C)
  证明: by
  rw [addContent_eq_add_disjointOfDiffUnion_of_subset hC ht h_ss hJt h_dis]
  exact le_add_right le_rfl

Depends on / 依赖: addContent_eq_add_disjointOfDiffUnion_of_subset, h_dis, h_ss, le_add_right, le_rfl
-/
lemma sum_addContent_le_of_subset (hC : IsSetSemiring C)
    (h_ss : ↑I subseteq C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
    (ht : t in C) (hJt : forall s in I, s subseteq t) :
    ∑ u in I, m u <= m t := by
  rw [addContent_eq_add_disjointOfDiffUnion_of_subset hC ht h_ss hJt h_dis]
  exact le_add_right le_rfl

/--
lemma `addContent_mono` / 引理 `addContent_mono`

English:
lemma addContent_mono
  statement: (hC : IsSetSemiring C) (hs : s in C) (ht : t in C)
  proof: by
  have h := sum_addContent_le_of_subset (m := m) hC (I := {s}) ?_ ?_ ht ?_
  · simpa only [sum_singleton] using h
  · rwa [singleton_subset_set_iff]
  · simp only [coe_singleton, pairwiseDisjoint_singleton]
  · simp [hst]

中文:
引理 addContent_mono
  结论: (hC : 是SetSemiring C) (hs : s in C) (ht : t in C)
  证明: by
  have h := sum_addContent_le_of_subset (m := m) hC (I := {s}) ?_ ?_ ht ?_
  · simpa only [sum_singleton] using h
  · rwa [singleton_subset_set_iff]
  · simp only [coe_singleton, pairwiseDisjoint_singleton]
  · simp [hst]

Depends on / 依赖: coe_singleton, pairwiseDisjoint_singleton, singleton_subset_set_iff, sum_addContent_le_of_subset, sum_singleton
-/
lemma addContent_mono (hC : IsSetSemiring C) (hs : s in C) (ht : t in C)
    (hst : s subseteq t) :
    m s <= m t := by
  have h := sum_addContent_le_of_subset (m := m) hC (I := {s}) ?_ ?_ ht ?_
  · simpa only [sum_singleton] using h
  · rwa [singleton_subset_set_iff]
  · simp only [coe_singleton, pairwiseDisjoint_singleton]
  · simp [hst]

/--
lemma `addContent_le_sum_of_subset_sUnion` / 引理 `addContent_le_sum_of_subset_sUnion`

English:
lemma addContent_le_sum_of_subset_sUnion
  statement: {m : AddContent G C} (hC : IsSetSemiring C)
  proof: by
  simp_rw +singlePass [← sSup_eq_sUnion, sSup_eq_iSup', SetLike.coe_sort_coe,
    ← J.equivFin.symm.iSup_comp, iSup_eq_iUnion, ← iUnion_disjointed] at htJ
  set f := disjointed fun j => (J.equivFin.symm j).1
  have h1 : forall j, f j in supClosure C :=
    hC.isSetRing_supClosure.disjointed_mem fun j =>
subset_supClosure h_ss (J.equivFin.symm j).2
  have h2 : Pairwise (Disjoint on f) := disjoint_disjointed _
  have h3 : ⋃ i, f i in supClosure C :=
    supClosed_supClosure.iSup_mem (subset_supClosure hC.empty_mem) h1
  grw [← m.supClosure_apply_of_mem hC ht,
    addContent_mono hC.isSetRing_supClosure.isSetSemiring (subset_supClosure ht) h3 htJ,
    addContent_iUnion h1 h2 h3, ← J.sum_attach, Finset.attach_eq_univ, ← J.equivFin.symm.sum_comp]
  gcongr with j -
  rw [← m.supClosure_apply_of_mem hC (h_ss (J.equivFin.symm _).2)]
  exact addContent_mono hC.isSetRing_supClosure.isSetSemiring (h1 j)
    (subset_supClosure (h_ss (J.equivFin.symm j).2)) (disjointed_subset _ j)

中文:
引理 addContent_le_sum_of_subset_sUnion
  结论: {m : 加法内容 G C} (hC : 是SetSemiring C)
  证明: by
  simp_rw +singlePass [← sSup_eq_sUnion, sSup_eq_iSup', SetLike.coe_sort_coe,
    ← J.equivFin.symm.iSup_comp, iSup_eq_iUnion, ← iUnion_disjointed] at htJ
  set f := disjointed fun j => (J.equivFin.symm j).1
  have h1 : forall j, f j in supClosure C :=
    hC.isSetRing_supClosure.disjointed_mem fun j =>
subset_supClosure h_ss (J.equivFin.symm j).2
  have h2 : Pairwise (Disjoint on f) := disjoint_disjointed _
  have h3 : ⋃ i, f i in supClosure C :=
    supClosed_supClosure.iSup_mem (subset_supClosure hC.empty_mem) h1
  grw [← m.supClosure_apply_of_mem hC ht,
    addContent_mono hC.isSetRing_supClosure.isSetSemiring (subset_supClosure ht) h3 htJ,
    addContent_iUnion h1 h2 h3, ← J.sum_attach, Finset.attach_eq_univ, ← J.equivFin.symm.sum_comp]
  gcongr with j -
  rw [← m.supClosure_apply_of_mem hC (h_ss (J.equivFin.symm _).2)]
  exact addContent_mono hC.isSetRing_supClosure.isSetSemiring (h1 j)
    (subset_supClosure (h_ss (J.equivFin.symm j).2)) (disjointed_subset _ j)

Depends on / 依赖: Disjoint, J.equivFin.symm, J.equivFin.symm.iSup_comp, Pairwise, SetLike, SetLike.coe_sort_coe, coe_sort_coe, disjoint_disjointed, disjointed, disjointed_mem, empty_mem, equivFin, hC.empty_mem, hC.isSetRing_supClosure.disjointed_mem, h_ss, iSup_comp, iSup_eq_iUnion, iSup_mem, iUnion_disjointed, isSetRing_supClosure
-/
lemma addContent_le_sum_of_subset_sUnion {m : AddContent G C} (hC : IsSetSemiring C)
    {J : Finset (Set α)} (h_ss : ↑J subseteq C) (ht : t in C) (htJ : t subseteq ⋃₀ ↑J) :
    m t <= ∑ u in J, m u := by
  simp_rw +singlePass [← sSup_eq_sUnion, sSup_eq_iSup', SetLike.coe_sort_coe,
    ← J.equivFin.symm.iSup_comp, iSup_eq_iUnion, ← iUnion_disjointed] at htJ
  set f := disjointed fun j => (J.equivFin.symm j).1
  have h1 : forall j, f j in supClosure C :=
    hC.isSetRing_supClosure.disjointed_mem fun j =>
subset_supClosure h_ss (J.equivFin.symm j).2
  have h2 : Pairwise (Disjoint on f) := disjoint_disjointed _
  have h3 : ⋃ i, f i in supClosure C :=
    supClosed_supClosure.iSup_mem (subset_supClosure hC.empty_mem) h1
  grw [← m.supClosure_apply_of_mem hC ht,
    addContent_mono hC.isSetRing_supClosure.isSetSemiring (subset_supClosure ht) h3 htJ,
    addContent_iUnion h1 h2 h3, ← J.sum_attach, Finset.attach_eq_univ, ← J.equivFin.symm.sum_comp]
  gcongr with j -
  rw [← m.supClosure_apply_of_mem hC (h_ss (J.equivFin.symm _).2)]
  exact addContent_mono hC.isSetRing_supClosure.isSetSemiring (h1 j)
    (subset_supClosure (h_ss (J.equivFin.symm j).2)) (disjointed_subset _ j)

/--
lemma `addContent_sUnion_le_sum` / 引理 `addContent_sUnion_le_sum`

English:
lemma addContent_sUnion_le_sum
  statement: {m : AddContent G C} (hC : IsSetSemiring C)
  proof: addContent_le_sum_of_subset_sUnion hC h_ss h_mem subset_rfl

中文:
引理 addContent_sUnion_le_sum
  结论: {m : 加法内容 G C} (hC : 是SetSemiring C)
  证明: addContent_le_sum_of_subset_sUnion hC h_ss h_mem subset_rfl

Depends on / 依赖: addContent_le_sum_of_subset_sUnion, h_mem, h_ss, subset_rfl
-/
lemma addContent_sUnion_le_sum {m : AddContent G C} (hC : IsSetSemiring C)
    (J : Finset (Set α)) (h_ss : ↑J subseteq C) (h_mem : ⋃₀ ↑J in C) :
    m (⋃₀ ↑J) <= ∑ u in J, m u :=
  addContent_le_sum_of_subset_sUnion hC h_ss h_mem subset_rfl

/--
theorem `addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le` / 定理 `addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le`

English:
theorem addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le
  statement: {m : AddContent Real>=0∞ C}
  proof: by
  refine le_antisymm (m_subadd f hf hf_Union hf_disj) ?_
  refine ENNReal.summable.tsum_le_of_sum_le fun I => ?_
  rw [← Finset.sum_image_of_disjoint addContent_empty (hf_disj.pairwiseDisjoint _)]
  refine sum_addContent_le_of_subset hC (I := I.image f) ?_ ?_ hf_Union ?_
  · simp only [coe_image, Set.image_subset_iff]
    refine (subset_preimage_image f I).trans (preimage_mono ?_)
    rintro i ⟨j, _, rfl⟩
    exact hf j
  · simp only [coe_image]
    intro s hs t ht hst
    rw [Set.mem_image] at hs ht
    obtain ⟨i, _, rfl⟩ := hs
    obtain ⟨j, _, rfl⟩ := ht
    have hij : i != j := by intro h_eq; rw [h_eq] at hst; exact hst rfl
    exact hf_disj hij
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun i _ => subset_iUnion _ i

中文:
定理 addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le
  结论: {m : 加法内容 实数>=0∞ C}
  证明: by
  refine le_antisymm (m_subadd f hf hf_Union hf_disj) ?_
  refine ENNReal.summable.tsum_le_of_sum_le fun I => ?_
  rw [← Finset.sum_image_of_disjoint addContent_empty (hf_disj.pairwiseDisjoint _)]
  refine sum_addContent_le_of_subset hC (I := I.image f) ?_ ?_ hf_Union ?_
  · simp only [coe_image, Set.image_subset_iff]
    refine (subset_preimage_image f I).trans (preimage_mono ?_)
    rintro i ⟨j, _, rfl⟩
    exact hf j
  · simp only [coe_image]
    intro s hs t ht hst
    rw [Set.mem_image] at hs ht
    obtain ⟨i, _, rfl⟩ := hs
    obtain ⟨j, _, rfl⟩ := ht
    have hij : i != j := by intro h_eq; rw [h_eq] at hst; exact hst rfl
    exact hf_disj hij
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun i _ => subset_iUnion _ i

Depends on / 依赖: ENNReal, ENNReal.summable.tsum_le_of_sum_le, Finset, Finset.sum_image_of_disjoint, I.image, Set.image_subset_iff, Set.mem_image, addContent_empty, coe_image, hf_Union, hf_disj, hf_disj.pairwiseDisjoint, image_subset_iff, le_antisymm, m_subadd, mem_image, pairwiseDisjoint, preimage_mono, subset_preimage_image, sum_addContent_le_of_subset
-/
theorem addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le {m : AddContent Real>=0∞ C}
    (hC : IsSetSemiring C)
    -- TODO: `m_subadd` is in fact equivalent to `m.IsSigmaSubadditive`.
    (m_subadd : forall (f : Nat -> Set α) (_ : forall i, f i in C) (_ : ⋃ i, f i in C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) <= ∑' i, m (f i))
    (f : Nat -> Set α) (hf : forall i, f i in C) (hf_Union : (⋃ i, f i) in C)
    (hf_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  refine le_antisymm (m_subadd f hf hf_Union hf_disj) ?_
  refine ENNReal.summable.tsum_le_of_sum_le fun I => ?_
  rw [← Finset.sum_image_of_disjoint addContent_empty (hf_disj.pairwiseDisjoint _)]
  refine sum_addContent_le_of_subset hC (I := I.image f) ?_ ?_ hf_Union ?_
  · simp only [coe_image, Set.image_subset_iff]
    refine (subset_preimage_image f I).trans (preimage_mono ?_)
    rintro i ⟨j, _, rfl⟩
    exact hf j
  · simp only [coe_image]
    intro s hs t ht hst
    rw [Set.mem_image] at hs ht
    obtain ⟨i, _, rfl⟩ := hs
    obtain ⟨j, _, rfl⟩ := ht
    have hij : i != j := by intro h_eq; rw [h_eq] at hst; exact hst rfl
    exact hf_disj hij
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun i _ => subset_iUnion _ i

/--
theorem `addContent_iUnion_eq_tsum_of_disjoint_of_IsSigmaSubadditive` / 定理 `addContent_iUnion_eq_tsum_of_disjoint_of_IsSigmaSubadditive`

English:
theorem addContent_iUnion_eq_tsum_of_disjoint_of_IsSigmaSubadditive
  statement: {m : AddContent Real>=0∞ C}
  proof: addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le hC
    (fun _ hf hf_Union _ => m_subadd hf hf_Union) f hf hf_Union hf_disj

中文:
定理 addContent_iUnion_eq_tsum_of_disjoint_of_IsSigmaSubadditive
  结论: {m : 加法内容 实数>=0∞ C}
  证明: addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le hC
    (fun _ hf hf_Union _ => m_subadd hf hf_Union) f hf hf_Union hf_disj

Depends on / 依赖: addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le, hf_Union, hf_disj, m_subadd
-/
theorem addContent_iUnion_eq_tsum_of_disjoint_of_IsSigmaSubadditive {m : AddContent Real>=0∞ C}
    (hC : IsSetSemiring C) (m_subadd : m.IsSigmaSubadditive)
    (f : Nat -> Set α) (hf : forall i, f i in C) (hf_Union : (⋃ i, f i) in C)
    (hf_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) :=
  addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le hC
    (fun _ hf hf_Union _ => m_subadd hf hf_Union) f hf hf_Union hf_disj

end IsSetSemiring

section OnIoc

variable [LinearOrder α] {G : Type*} [AddCommGroup G]

open scoped Classical in
/--
Definition of `AddContent.onIocAux` / `AddContent.onIocAux` 的定义

English:
definition AddContent.onIocAux
  signature: (f : α -> G) (s : Set α)
  body: if h : exists (p : α × α), p.1 <= p.2 ∧ s = Set.Ioc p.1 p.2
    then f h.choose.2 - f h.choose.1 else 0

中文:
定义 加法内容.onIocAux
  签名: (f : α -> G) (s : 集合 α)
  定义体: if h : exists (p : α × α), p.1 <= p.2 ∧ s = Set.Ioc p.1 p.2
    then f h.choose.2 - f h.choose.1 else 0

Depends on / 依赖: Set.Ioc, h.choose
-/
noncomputable def AddContent.onIocAux (f : α -> G) (s : Set α) : G :=
  if h : exists (p : α × α), p.1 <= p.2 ∧ s = Set.Ioc p.1 p.2
    then f h.choose.2 - f h.choose.1 else 0

/--
lemma `AddContent.onIocAux_apply` / 引理 `AddContent.onIocAux_apply`

English:
lemma AddContent.onIocAux_apply
  given: {f : α -> G} {u v : α} (h : u <= v)
  proof: by
  have h' : exists (p : α × α), p.1 <= p.2 ∧ Ioc u v = Ioc p.1 p.2 := ⟨(u, v), h, rfl⟩
  simp only [onIocAux, h', ↓reduceDIte]
  set u' := h'.choose.1
  set v' := h'.choose.2
  have hu'v' : u' <= v' ∧ Ioc u v = Ioc u' v' := h'.choose_spec
  rcases h.eq_or_lt with rfl | huv
  · grind [Set.Ioc_eq_empty_iff]
  rw [Ioc_eq_Ioc_iff (Or.inl huv)] at hu'v'
  grind

中文:
引理 加法内容.onIocAux_apply
  条件: {f : α -> G} {u v : α} (h : u <= v)
  证明: by
  have h' : exists (p : α × α), p.1 <= p.2 ∧ Ioc u v = Ioc p.1 p.2 := ⟨(u, v), h, rfl⟩
  simp only [onIocAux, h', ↓reduceDIte]
  set u' := h'.choose.1
  set v' := h'.choose.2
  have hu'v' : u' <= v' ∧ Ioc u v = Ioc u' v' := h'.choose_spec
  rcases h.eq_or_lt with rfl | huv
  · grind [Set.Ioc_eq_empty_iff]
  rw [Ioc_eq_Ioc_iff (Or.inl huv)] at hu'v'
  grind

Depends on / 依赖: Ioc_eq_Ioc_iff, Ioc_eq_empty_iff, Or.inl, Set.Ioc_eq_empty_iff, choose_spec, eq_or_lt, h.eq_or_lt, onIocAux, reduceDIte
-/
lemma AddContent.onIocAux_apply {f : α -> G} {u v : α} (h : u <= v) :
    AddContent.onIocAux f (Ioc u v) = f v - f u := by
  have h' : exists (p : α × α), p.1 <= p.2 ∧ Ioc u v = Ioc p.1 p.2 := ⟨(u, v), h, rfl⟩
  simp only [onIocAux, h', ↓reduceDIte]
  set u' := h'.choose.1
  set v' := h'.choose.2
  have hu'v' : u' <= v' ∧ Ioc u v = Ioc u' v' := h'.choose_spec
  rcases h.eq_or_lt with rfl | huv
  · grind [Set.Ioc_eq_empty_iff]
  rw [Ioc_eq_Ioc_iff (Or.inl huv)] at hu'v'
  grind

/--
lemma `AddContent.onIocAux_empty` / 引理 `AddContent.onIocAux_empty`

English:
lemma AddContent.onIocAux_empty
  given: (f : α -> G)
  proof: by
  classical
  rw [onIocAux]; rw [dite_eq_right_iff]
  grind [Set.Ioc_eq_empty_iff]

中文:
引理 加法内容.onIocAux_empty
  条件: (f : α -> G)
  证明: by
  classical
  rw [onIocAux]; rw [dite_eq_right_iff]
  grind [Set.Ioc_eq_empty_iff]

Depends on / 依赖: Ioc_eq_empty_iff, Set.Ioc_eq_empty_iff, classical, dite_eq_right_iff, onIocAux
-/
lemma AddContent.onIocAux_empty (f : α -> G) :
    AddContent.onIocAux f ∅ = 0 := by
  classical
  rw [onIocAux]; rw [dite_eq_right_iff]
  grind [Set.Ioc_eq_empty_iff]

/--
Definition of `AddContent.onIoc` / `AddContent.onIoc` 的定义

English:
definition AddContent.onIoc
  signature: (f : α -> G)
  body: AddContent.onIocAux f
  empty' := AddContent.onIocAux_empty f
  sUnion' := by
    /- Consider a finite union of open-closed intervals whose union is again an open-closed
    interval `(u, v]`. We have to show that the sum of `f b - f a` over the intervals gives
    `f v - f u`. Informally, `(u, v]` is an ordered
    union `(a₀, a₁] ∪ (a₁, a₂] ∪ ... ∪ (a_{n-1}, aₙ]` and there is a telescoping sum.
    For the formal argument, we argue by induction on the number of intervals, and remove the
    right-most one (i.e., the one that contains `v`) to reduce to one interval less. Denoting
    this right-most interval by `(u', v]`, then the union of the other intervals
    is exactly `(u, u']`. From this and the induction assumption, the conclusion follows. -/
    intro I hI h'I h''I
    induction hn : Finset.card I generalizing I with
    | zero =>
      have : I = ∅ := by grind
      simp [this, onIocAux_empty f]
    | succ n ih =>
      rcases h''I with ⟨u, v, huv, h'uv⟩
      -- If the interval `(u, v]` is empty, i.e., `u = v`, then the result is easy.
      rcases huv.eq_or_lt with rfl | huv
      · have : onIocAux f (Set.Ioc u u) = ∑ u in I, 0 := by simp [onIocAux_empty f]
        rw [h'uv]; rw [this]
        apply Finset.sum_congr rfl fun i hi => ?_
        have : i = ∅ := by grind [sUnion_eq_empty]
        grind [onIocAux_empty]
      -- otherwise, `v` is in `(u, v]`, therefore it belongs to some interval `(u', v']`
      -- featuring in the union.
      have : v in ⋃₀ ↑I := by simp [h'uv, huv]
      obtain ⟨t, tI, ht⟩ : exists t in I, v in t := by simpa using this
      rcases hI tI with ⟨u', v', hu'v', rfl⟩
      -- we have `u ≤ u'` and `v' = v` since `(u', v']` is part of the union, and therefore
      -- contained in `(u, v]`.
      have ⟨_, uu'⟩ : v' <= v ∧ u <= u' := (Ioc_subset_Ioc_iff (by grind)).1 (by grind)
      obtain rfl : v = v' := by grind
      rw [h'uv]; rw [onIocAux_apply huv.le]
      -- let us remove the right-most interval `(u', v]` from the union, and let `I'` be the
      -- remaining set of intervals.
      let I' := I.erase (Set.Ioc u' v)
      have I'I : I' subseteq I := erase_subset (Set.Ioc u' v) I
      have I_eq_insert : I = insert (Set.Ioc u' v) I' := by simp [I', tI]
      -- the intervals in `I'` cover exactly `(u, u']`.
      have UI' : ⋃₀ ↑I' = Ioc u u' := by
        have : (Ioc u' v union ⋃₀ ↑I') \ Ioc u' v = ⋃₀ ↑I' := by
          refine Disjoint.sup_sdiff_cancel_left ?_
          simp only [coe_erase, disjoint_sUnion_right, Set.mem_sdiff, mem_singleton_iff, and_imp,
            I']
          intro u hu hu'
          exact (h'I hu tI hu').symm
        simp only [I_eq_insert, coe_insert, sUnion_insert] at h'uv
        grind
      -- by the inductive assumption, the sum over `I'` is exactly `f u' - f u`.
      have IH : onIocAux f (⋃₀ ↑I') = ∑ u in I', onIocAux f u :=
        ih _ (Subset.trans I'I hI) (h'I.subset I'I) (by grind) (by grind)
      -- the conclusion follows.
      rw [I_eq_insert]; rw [sum_insert]; rw [← IH]; rw [UI']; rw [onIocAux_apply hu'v']; rw [onIocAux_apply uu']
      · simp
      · simp [I']

中文:
定义 加法内容.onIoc
  签名: (f : α -> G)
  定义体: AddContent.onIocAux f
  empty' := AddContent.onIocAux_empty f
  sUnion' := by
    /- Consider a finite union of open-closed intervals whose union is again an open-closed
    interval `(u, v]`. We have to show that the sum of `f b - f a` over the intervals gives
    `f v - f u`. Informally, `(u, v]` is an ordered
    union `(a₀, a₁] ∪ (a₁, a₂] ∪ ... ∪ (a_{n-1}, aₙ]` and there is a telescoping sum.
    For the formal argument, we argue by induction on the number of intervals, and remove the
    right-most one (i.e., the one that contains `v`) to reduce to one interval less. Denoting
    this right-most interval by `(u', v]`, then the union of the other intervals
    is exactly `(u, u']`. From this and the induction assumption, the conclusion follows. -/
    intro I hI h'I h''I
    induction hn : Finset.card I generalizing I with
    | zero =>
      have : I = ∅ := by grind
      simp [this, onIocAux_empty f]
    | succ n ih =>
      rcases h''I with ⟨u, v, huv, h'uv⟩
      -- If the interval `(u, v]` is empty, i.e., `u = v`, then the result is easy.
      rcases huv.eq_or_lt with rfl | huv
      · have : onIocAux f (Set.Ioc u u) = ∑ u in I, 0 := by simp [onIocAux_empty f]
        rw [h'uv]; rw [this]
        apply Finset.sum_congr rfl fun i hi => ?_
        have : i = ∅ := by grind [sUnion_eq_empty]
        grind [onIocAux_empty]
      -- otherwise, `v` is in `(u, v]`, therefore it belongs to some interval `(u', v']`
      -- featuring in the union.
      have : v in ⋃₀ ↑I := by simp [h'uv, huv]
      obtain ⟨t, tI, ht⟩ : exists t in I, v in t := by simpa using this
      rcases hI tI with ⟨u', v', hu'v', rfl⟩
      -- we have `u ≤ u'` and `v' = v` since `(u', v']` is part of the union, and therefore
      -- contained in `(u, v]`.
      have ⟨_, uu'⟩ : v' <= v ∧ u <= u' := (Ioc_subset_Ioc_iff (by grind)).1 (by grind)
      obtain rfl : v = v' := by grind
      rw [h'uv]; rw [onIocAux_apply huv.le]
      -- let us remove the right-most interval `(u', v]` from the union, and let `I'` be the
      -- remaining set of intervals.
      let I' := I.erase (Set.Ioc u' v)
      have I'I : I' subseteq I := erase_subset (Set.Ioc u' v) I
      have I_eq_insert : I = insert (Set.Ioc u' v) I' := by simp [I', tI]
      -- the intervals in `I'` cover exactly `(u, u']`.
      have UI' : ⋃₀ ↑I' = Ioc u u' := by
        have : (Ioc u' v union ⋃₀ ↑I') \ Ioc u' v = ⋃₀ ↑I' := by
          refine Disjoint.sup_sdiff_cancel_left ?_
          simp only [coe_erase, disjoint_sUnion_right, Set.mem_sdiff, mem_singleton_iff, and_imp,
            I']
          intro u hu hu'
          exact (h'I hu tI hu').symm
        simp only [I_eq_insert, coe_insert, sUnion_insert] at h'uv
        grind
      -- by the inductive assumption, the sum over `I'` is exactly `f u' - f u`.
      have IH : onIocAux f (⋃₀ ↑I') = ∑ u in I', onIocAux f u :=
        ih _ (Subset.trans I'I hI) (h'I.subset I'I) (by grind) (by grind)
      -- the conclusion follows.
      rw [I_eq_insert]; rw [sum_insert]; rw [← IH]; rw [UI']; rw [onIocAux_apply hu'v']; rw [onIocAux_apply uu']
      · simp
      · simp [I']

Depends on / 依赖: AddContent, AddContent.onIocAux, onIocAux
-/
noncomputable def AddContent.onIoc (f : α -> G) :
    AddContent G {s : Set α | exists u v, u <= v ∧ s = Set.Ioc u v} where
  toFun := AddContent.onIocAux f
  empty' := AddContent.onIocAux_empty f
  sUnion' := by
    /- Consider a finite union of open-closed intervals whose union is again an open-closed
    interval `(u, v]`. We have to show that the sum of `f b - f a` over the intervals gives
    `f v - f u`. Informally, `(u, v]` is an ordered
    union `(a₀, a₁] ∪ (a₁, a₂] ∪ ... ∪ (a_{n-1}, aₙ]` and there is a telescoping sum.
    For the formal argument, we argue by induction on the number of intervals, and remove the
    right-most one (i.e., the one that contains `v`) to reduce to one interval less. Denoting
    this right-most interval by `(u', v]`, then the union of the other intervals
    is exactly `(u, u']`. From this and the induction assumption, the conclusion follows. -/
    intro I hI h'I h''I
    induction hn : Finset.card I generalizing I with
    | zero =>
      have : I = ∅ := by grind
      simp [this, onIocAux_empty f]
    | succ n ih =>
      rcases h''I with ⟨u, v, huv, h'uv⟩
      -- If the interval `(u, v]` is empty, i.e., `u = v`, then the result is easy.
      rcases huv.eq_or_lt with rfl | huv
      · have : onIocAux f (Set.Ioc u u) = ∑ u in I, 0 := by simp [onIocAux_empty f]
        rw [h'uv]; rw [this]
        apply Finset.sum_congr rfl fun i hi => ?_
        have : i = ∅ := by grind [sUnion_eq_empty]
        grind [onIocAux_empty]
      -- otherwise, `v` is in `(u, v]`, therefore it belongs to some interval `(u', v']`
      -- featuring in the union.
      have : v in ⋃₀ ↑I := by simp [h'uv, huv]
      obtain ⟨t, tI, ht⟩ : exists t in I, v in t := by simpa using this
      rcases hI tI with ⟨u', v', hu'v', rfl⟩
      -- we have `u ≤ u'` and `v' = v` since `(u', v']` is part of the union, and therefore
      -- contained in `(u, v]`.
      have ⟨_, uu'⟩ : v' <= v ∧ u <= u' := (Ioc_subset_Ioc_iff (by grind)).1 (by grind)
      obtain rfl : v = v' := by grind
      rw [h'uv]; rw [onIocAux_apply huv.le]
      -- let us remove the right-most interval `(u', v]` from the union, and let `I'` be the
      -- remaining set of intervals.
      let I' := I.erase (Set.Ioc u' v)
      have I'I : I' subseteq I := erase_subset (Set.Ioc u' v) I
      have I_eq_insert : I = insert (Set.Ioc u' v) I' := by simp [I', tI]
      -- the intervals in `I'` cover exactly `(u, u']`.
      have UI' : ⋃₀ ↑I' = Ioc u u' := by
        have : (Ioc u' v union ⋃₀ ↑I') \ Ioc u' v = ⋃₀ ↑I' := by
          refine Disjoint.sup_sdiff_cancel_left ?_
          simp only [coe_erase, disjoint_sUnion_right, Set.mem_sdiff, mem_singleton_iff, and_imp,
            I']
          intro u hu hu'
          exact (h'I hu tI hu').symm
        simp only [I_eq_insert, coe_insert, sUnion_insert] at h'uv
        grind
      -- by the inductive assumption, the sum over `I'` is exactly `f u' - f u`.
      have IH : onIocAux f (⋃₀ ↑I') = ∑ u in I', onIocAux f u :=
        ih _ (Subset.trans I'I hI) (h'I.subset I'I) (by grind) (by grind)
      -- the conclusion follows.
      rw [I_eq_insert]; rw [sum_insert]; rw [← IH]; rw [UI']; rw [onIocAux_apply hu'v']; rw [onIocAux_apply uu']
      · simp
      · simp [I']

/--
lemma `AddContent.onIoc_apply` / 引理 `AddContent.onIoc_apply`

English:
lemma AddContent.onIoc_apply
  given: {f : α -> G} {u v : α} (h : u <= v)
  proof: AddContent.onIocAux_apply h

中文:
引理 加法内容.onIoc_apply
  条件: {f : α -> G} {u v : α} (h : u <= v)
  证明: AddContent.onIocAux_apply h

Depends on / 依赖: AddContent, AddContent.onIocAux_apply, onIocAux_apply
-/
lemma AddContent.onIoc_apply {f : α -> G} {u v : α} (h : u <= v) :
    AddContent.onIoc f (Ioc u v) = f v - f u :=
  AddContent.onIocAux_apply h

end OnIoc

section AddContentExtend

/-- An additive content obtained from another one on the same semiring of sets by setting the value
of each set not in the semiring at `∞`. -/
protected noncomputable
/--
Definition of `AddContent.extend` / `AddContent.extend` 的定义

English:
definition AddContent.extend
  signature: (hC : IsSetSemiring C) (m : AddContent Real>=0∞ C)
  body: extend (fun x (_ : x in C) => m x)
  empty' := by rw [extend_eq, addContent_empty]; exact hC.empty_mem
  sUnion' I h_ss h_dis h_mem := by
    rw [extend_eq]
    swap; · exact h_mem
    rw [addContent_sUnion h_ss h_dis h_mem]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [extend_eq]
    exact h_ss hs

中文:
定义 加法内容.extend
  签名: (hC : 是SetSemiring C) (m : 加法内容 实数>=0∞ C)
  定义体: extend (fun x (_ : x in C) => m x)
  empty' := by rw [extend_eq, addContent_empty]; exact hC.empty_mem
  sUnion' I h_ss h_dis h_mem := by
    rw [extend_eq]
    swap; · exact h_mem
    rw [addContent_sUnion h_ss h_dis h_mem]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [extend_eq]
    exact h_ss hs

Depends on / 依赖: extend
-/
def AddContent.extend (hC : IsSetSemiring C) (m : AddContent Real>=0∞ C) : AddContent Real>=0∞ C where
  toFun := extend (fun x (_ : x in C) => m x)
  empty' := by rw [extend_eq, addContent_empty]; exact hC.empty_mem
  sUnion' I h_ss h_dis h_mem := by
    rw [extend_eq]
    swap; · exact h_mem
    rw [addContent_sUnion h_ss h_dis h_mem]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [extend_eq]
    exact h_ss hs

/--
theorem `AddContent.extend_eq_extend` / 定理 `AddContent.extend_eq_extend`

English:
theorem AddContent.extend_eq_extend
  given: (hC : IsSetSemiring C) (m : AddContent Real>=0∞ C)
  proof: rfl

中文:
定理 加法内容.extend_eq_extend
  条件: (hC : 是SetSemiring C) (m : 加法内容 实数>=0∞ C)
  证明: rfl
-/
protected theorem AddContent.extend_eq_extend (hC : IsSetSemiring C) (m : AddContent Real>=0∞ C) :
    m.extend hC = extend (fun x (_ : x in C) => m x) := rfl

/--
theorem `AddContent.extend_eq` / 定理 `AddContent.extend_eq`

English:
theorem AddContent.extend_eq
  given: (hC : IsSetSemiring C) (m : AddContent Real>=0∞ C) (hs : s in C)
  proof: by
  rwa [m.extend_eq_extend, extend_eq]

中文:
定理 加法内容.extend_eq
  条件: (hC : 是SetSemiring C) (m : 加法内容 实数>=0∞ C) (hs : s in C)
  证明: by
  rwa [m.extend_eq_extend, extend_eq]
-/
protected theorem AddContent.extend_eq (hC : IsSetSemiring C) (m : AddContent Real>=0∞ C) (hs : s in C) :
    m.extend hC s = m s := by
  rwa [m.extend_eq_extend, extend_eq]

/--
theorem `AddContent.extend_eq_top` / 定理 `AddContent.extend_eq_top`

English:
theorem AddContent.extend_eq_top
  proof: by
  rwa [m.extend_eq_extend, extend_eq_top]

中文:
定理 加法内容.extend_eq_top
  证明: by
  rwa [m.extend_eq_extend, extend_eq_top]
-/
protected theorem AddContent.extend_eq_top
    (hC : IsSetSemiring C) (m : AddContent Real>=0∞ C) (hs : s ∉ C) :
    m.extend hC s = ∞ := by
  rwa [m.extend_eq_extend, extend_eq_top]

end AddContentExtend

section IsSetRing

/--
lemma `addContent_union` / 引理 `addContent_union`

English:
lemma addContent_union
  statement: (hC : IsSetRing C) (hs : s in C) (ht : t in C)
  proof: addContent_union' hs ht (hC.union_mem hs ht) h_dis

中文:
引理 addContent_union
  结论: (hC : 是集合环 C) (hs : s in C) (ht : t in C)
  证明: addContent_union' hs ht (hC.union_mem hs ht) h_dis

Depends on / 依赖: addContent_union, hC.union_mem, h_dis, union_mem
-/
lemma addContent_union (hC : IsSetRing C) (hs : s in C) (ht : t in C)
    (h_dis : Disjoint s t) :
    m (s union t) = m s + m t :=
  addContent_union' hs ht (hC.union_mem hs ht) h_dis

/--
lemma `addContent_biUnion_eq` / 引理 `addContent_biUnion_eq`

English:
lemma addContent_biUnion_eq
  statement: {ι : Type*} (hC : IsSetRing C) {s : ι -> Set α}
  proof: by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S hiS h =>
    rw [Finset.sum_insert hiS]
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    simp only [Finset.coe_insert, Set.pairwiseDisjoint_insert] at hS
    rw [← h hs.2 hS.1]
    refine addContent_union hC hs.1 (hC.biUnion_mem S hs.2) ?_
    rw [disjoint_iUnion₂_right]
    exact fun j hjS => hS.2 j hjS (ne_of_mem_of_not_mem hjS hiS).symm

中文:
引理 addContent_biUnion_eq
  结论: {ι : 类型} (hC : 是集合环 C) {s : ι -> 集合 α}
  证明: by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S hiS h =>
    rw [Finset.sum_insert hiS]
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    simp only [Finset.coe_insert, Set.pairwiseDisjoint_insert] at hS
    rw [← h hs.2 hS.1]
    refine addContent_union hC hs.1 (hC.biUnion_mem S hs.2) ?_
    rw [disjoint_iUnion₂_right]
    exact fun j hjS => hS.2 j hjS (ne_of_mem_of_not_mem hjS hiS).symm

Depends on / 依赖: Finset, Finset.coe_insert, Finset.induction, Finset.mem_coe, Finset.mem_insert, Finset.sum_insert, Set.biUnion_insert, Set.pairwiseDisjoint_insert, addContent_union, biUnion_insert, biUnion_mem, classical, coe_insert, forall_eq_or_imp, hC.biUnion_mem, insert, mem_coe, mem_insert, ne_of_mem_of_not_mem, pairwiseDisjoint_insert
-/
lemma addContent_biUnion_eq {ι : Type*} (hC : IsSetRing C) {s : ι -> Set α}
    {S : Finset ι} (hs : forall n in S, s n in C) (hS : (S : Set ι).PairwiseDisjoint s) :
    m (⋃ i in S, s i) = ∑ i in S, m (s i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S hiS h =>
    rw [Finset.sum_insert hiS]
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    simp only [Finset.coe_insert, Set.pairwiseDisjoint_insert] at hS
    rw [← h hs.2 hS.1]
    refine addContent_union hC hs.1 (hC.biUnion_mem S hs.2) ?_
    rw [disjoint_iUnion₂_right]
    exact fun j hjS => hS.2 j hjS (ne_of_mem_of_not_mem hjS hiS).symm

/--
lemma `addContent_accumulate` / 引理 `addContent_accumulate`

English:
lemma addContent_accumulate
  statement: (m : AddContent G C) (hC : IsSetRing C)
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ]; rw [← hn]; rw [Set.accumulate_succ]; rw [addContent_union hC _ (hsC _)]
    · exact Set.disjoint_accumulate hs_disj (Nat.lt_succ_self n)
    · exact hC.accumulate_mem hsC n

中文:
引理 addContent_accumulate
  结论: (m : 加法内容 G C) (hC : 是集合环 C)
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ]; rw [← hn]; rw [Set.accumulate_succ]; rw [addContent_union hC _ (hsC _)]
    · exact Set.disjoint_accumulate hs_disj (Nat.lt_succ_self n)
    · exact hC.accumulate_mem hsC n

Depends on / 依赖: Finset, Finset.sum_range_succ, Nat.lt_succ_self, Set.accumulate_succ, Set.disjoint_accumulate, accumulate_mem, accumulate_succ, addContent_union, disjoint_accumulate, hC.accumulate_mem, hs_disj, lt_succ_self, sum_range_succ
-/
lemma addContent_accumulate (m : AddContent G C) (hC : IsSetRing C)
    {s : Nat -> Set α} (hs_disj : Pairwise (Disjoint on s)) (hsC : forall i, s i in C) (n : Nat) :
      m (Set.accumulate s n) = ∑ i in Finset.range (n + 1), m (s i) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ]; rw [← hn]; rw [Set.accumulate_succ]; rw [addContent_union hC _ (hsC _)]
    · exact Set.disjoint_accumulate hs_disj (Nat.lt_succ_self n)
    · exact hC.accumulate_mem hsC n

/--
Definition of `IsSetRing.addContent_of_union` / `IsSetRing.addContent_of_union` 的定义

English:
definition IsSetRing.addContent_of_union
  signature: (m : Set α -> G) (hC : IsSetRing C) (m_empty : m ∅ = 0)
  body: m
  empty' := m_empty
  sUnion' I h_ss h_dis h_mem := by
    induction I using Finset.induction with
    | empty => simp only [Finset.coe_empty, Set.sUnion_empty, Finset.sum_empty, m_empty]
    | insert s I hsI h =>
      rw [Finset.coe_insert] at *
      rw [Set.insert_subset_iff] at h_ss
      rw [Set.pairwiseDisjoint_insert_of_notMem] at h_dis
      swap; · exact hsI
      have h_sUnion_mem : ⋃₀ ↑I in C := by
        rw [Set.sUnion_eq_biUnion]
        apply hC.biUnion_mem
        intro n hn
        exact h_ss.2 hn
      rw [Set.sUnion_insert]; rw [m_add h_ss.1 h_sUnion_mem (Set.disjoint_sUnion_right.mpr h_dis.2)]; rw [Finset.sum_insert hsI]; rw [h h_ss.2 h_dis.1]
      rwa [Set.sUnion_insert] at h_mem

中文:
定义 是集合环.addContent_of_union
  签名: (m : 集合 α -> G) (hC : 是集合环 C) (m_empty : m ∅ = 0)
  定义体: m
  empty' := m_empty
  sUnion' I h_ss h_dis h_mem := by
    induction I using Finset.induction with
    | empty => simp only [Finset.coe_empty, Set.sUnion_empty, Finset.sum_empty, m_empty]
    | insert s I hsI h =>
      rw [Finset.coe_insert] at *
      rw [Set.insert_subset_iff] at h_ss
      rw [Set.pairwiseDisjoint_insert_of_notMem] at h_dis
      swap; · exact hsI
      have h_sUnion_mem : ⋃₀ ↑I in C := by
        rw [Set.sUnion_eq_biUnion]
        apply hC.biUnion_mem
        intro n hn
        exact h_ss.2 hn
      rw [Set.sUnion_insert]; rw [m_add h_ss.1 h_sUnion_mem (Set.disjoint_sUnion_right.mpr h_dis.2)]; rw [Finset.sum_insert hsI]; rw [h h_ss.2 h_dis.1]
      rwa [Set.sUnion_insert] at h_mem
-/
def IsSetRing.addContent_of_union (m : Set α -> G) (hC : IsSetRing C) (m_empty : m ∅ = 0)
    (m_add : forall {s t : Set α} (_hs : s in C) (_ht : t in C), Disjoint s t -> m (s union t) = m s + m t) :
    AddContent G C where
  toFun := m
  empty' := m_empty
  sUnion' I h_ss h_dis h_mem := by
    induction I using Finset.induction with
    | empty => simp only [Finset.coe_empty, Set.sUnion_empty, Finset.sum_empty, m_empty]
    | insert s I hsI h =>
      rw [Finset.coe_insert] at *
      rw [Set.insert_subset_iff] at h_ss
      rw [Set.pairwiseDisjoint_insert_of_notMem] at h_dis
      swap; · exact hsI
      have h_sUnion_mem : ⋃₀ ↑I in C := by
        rw [Set.sUnion_eq_biUnion]
        apply hC.biUnion_mem
        intro n hn
        exact h_ss.2 hn
      rw [Set.sUnion_insert]; rw [m_add h_ss.1 h_sUnion_mem (Set.disjoint_sUnion_right.mpr h_dis.2)]; rw [Finset.sum_insert hsI]; rw [h h_ss.2 h_dis.1]
      rwa [Set.sUnion_insert] at h_mem

variable [PartialOrder G] [CanonicallyOrderedAdd G]

/--
lemma `addContent_union_le` / 引理 `addContent_union_le`

English:
lemma addContent_union_le
  given: (hC : IsSetRing C) (hs : s in C) (ht : t in C)
  proof: by
  rw [← union_sdiff_self]; rw [addContent_union hC hs (hC.sdiff_mem ht hs)]
  · exact add_le_add_right (addContent_mono hC.isSetSemiring (hC.sdiff_mem ht hs) ht sdiff_subset) _
  · rw [Set.disjoint_iff_inter_eq_empty, inter_sdiff_self]

中文:
引理 addContent_union_le
  条件: (hC : 是集合环 C) (hs : s in C) (ht : t in C)
  证明: by
  rw [← union_sdiff_self]; rw [addContent_union hC hs (hC.sdiff_mem ht hs)]
  · exact add_le_add_right (addContent_mono hC.isSetSemiring (hC.sdiff_mem ht hs) ht sdiff_subset) _
  · rw [Set.disjoint_iff_inter_eq_empty, inter_sdiff_self]

Depends on / 依赖: Set.disjoint_iff_inter_eq_empty, addContent_mono, addContent_union, add_le_add_right, disjoint_iff_inter_eq_empty, hC.isSetSemiring, hC.sdiff_mem, inter_sdiff_self, isSetSemiring, sdiff_mem, sdiff_subset, union_sdiff_self
-/
lemma addContent_union_le (hC : IsSetRing C) (hs : s in C) (ht : t in C) :
    m (s union t) <= m s + m t := by
  rw [← union_sdiff_self]; rw [addContent_union hC hs (hC.sdiff_mem ht hs)]
  · exact add_le_add_right (addContent_mono hC.isSetSemiring (hC.sdiff_mem ht hs) ht sdiff_subset) _
  · rw [Set.disjoint_iff_inter_eq_empty, inter_sdiff_self]

/--
lemma `addContent_biUnion_le` / 引理 `addContent_biUnion_le`

English:
lemma addContent_biUnion_le
  statement: {ι : Type*} (hC : IsSetRing C) {s : ι -> Set α}
  proof: by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S hiS h =>
    rw [Finset.sum_insert hiS]
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    refine (addContent_union_le hC hs.1 (hC.biUnion_mem S hs.2)).trans ?_
    exact add_le_add le_rfl (h hs.2)

中文:
引理 addContent_biUnion_le
  结论: {ι : 类型} (hC : 是集合环 C) {s : ι -> 集合 α}
  证明: by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S hiS h =>
    rw [Finset.sum_insert hiS]
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    refine (addContent_union_le hC hs.1 (hC.biUnion_mem S hs.2)).trans ?_
    exact add_le_add le_rfl (h hs.2)

Depends on / 依赖: Finset, Finset.coe_insert, Finset.induction, Finset.mem_coe, Finset.mem_insert, Finset.sum_insert, Set.biUnion_insert, addContent_union_le, add_le_add, biUnion_insert, biUnion_mem, classical, coe_insert, forall_eq_or_imp, hC.biUnion_mem, insert, le_rfl, mem_coe, mem_insert, simp_rw
-/
lemma addContent_biUnion_le {ι : Type*} (hC : IsSetRing C) {s : ι -> Set α}
    {S : Finset ι} (hs : forall n in S, s n in C) :
    m (⋃ i in S, s i) <= ∑ i in S, m (s i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S hiS h =>
    rw [Finset.sum_insert hiS]
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    refine (addContent_union_le hC hs.1 (hC.biUnion_mem S hs.2)).trans ?_
    exact add_le_add le_rfl (h hs.2)

/--
lemma `le_addContent_sdiff` / 引理 `le_addContent_sdiff`

English:
lemma le_addContent_sdiff
  given: (m : AddContent Real>=0∞ C) (hC : IsSetRing C) (hs : s in C) (ht : t in C)
  proof: by
  conv_lhs => rw [← inter_union_sdiff s t]
  rw [addContent_union hC (hC.inter_mem hs ht) (hC.sdiff_mem hs ht) disjoint_inf_sdiff]; rw [add_comm]
  refine add_tsub_le_assoc.trans_eq ?_
  rw [tsub_eq_zero_of_le
    (addContent_mono hC.isSetSemiring (hC.inter_mem hs ht) ht inter_subset_right)]; rw [add_zero]

@[deprecated (since := "2026-06-03")] alias le_addContent_diff := le_addContent_sdiff

中文:
引理 le_addContent_sdiff
  条件: (m : 加法内容 实数>=0∞ C) (hC : 是集合环 C) (hs : s in C) (ht : t in C)
  证明: by
  conv_lhs => rw [← inter_union_sdiff s t]
  rw [addContent_union hC (hC.inter_mem hs ht) (hC.sdiff_mem hs ht) disjoint_inf_sdiff]; rw [add_comm]
  refine add_tsub_le_assoc.trans_eq ?_
  rw [tsub_eq_zero_of_le
    (addContent_mono hC.isSetSemiring (hC.inter_mem hs ht) ht inter_subset_right)]; rw [add_zero]

@[deprecated (since := "2026-06-03")] alias le_addContent_diff := le_addContent_sdiff

Depends on / 依赖: addContent_mono, addContent_union, add_comm, add_tsub_le_assoc, add_tsub_le_assoc.trans_eq, add_zero, conv_lhs, disjoint_inf_sdiff, hC.inter_mem, hC.isSetSemiring, hC.sdiff_mem, inter_mem, inter_subset_right, inter_union_sdiff, isSetSemiring, sdiff_mem, trans_eq, tsub_eq_zero_of_le
-/
lemma le_addContent_sdiff (m : AddContent Real>=0∞ C) (hC : IsSetRing C) (hs : s in C) (ht : t in C) :
    m s - m t <= m (s \ t) := by
  conv_lhs => rw [← inter_union_sdiff s t]
  rw [addContent_union hC (hC.inter_mem hs ht) (hC.sdiff_mem hs ht) disjoint_inf_sdiff]; rw [add_comm]
  refine add_tsub_le_assoc.trans_eq ?_
  rw [tsub_eq_zero_of_le
    (addContent_mono hC.isSetSemiring (hC.inter_mem hs ht) ht inter_subset_right)]; rw [add_zero]

@[deprecated (since := "2026-06-03")] alias le_addContent_diff := le_addContent_sdiff

/--
lemma `addContent_sdiff_of_ne_top` / 引理 `addContent_sdiff_of_ne_top`

English:
lemma addContent_sdiff_of_ne_top
  statement: (m : AddContent Real>=0∞ C) (hC : IsSetRing C)
  proof: by
  have h_union : m (t union s \ t) = m t + m (s \ t) :=
    addContent_union hC ht (hC.sdiff_mem hs ht) disjoint_sdiff_self_right
  simp_rw [Set.union_sdiff_self, Set.union_eq_right.mpr hts] at h_union
  rw [h_union]; rw [ENNReal.add_sub_cancel_left (hm_ne_top _ ht)]

@[deprecated (since := "2026-06-03")] alias addContent_diff_of_ne_top := addContent_sdiff_of_ne_top

中文:
引理 addContent_sdiff_of_ne_top
  结论: (m : 加法内容 实数>=0∞ C) (hC : 是集合环 C)
  证明: by
  have h_union : m (t union s \ t) = m t + m (s \ t) :=
    addContent_union hC ht (hC.sdiff_mem hs ht) disjoint_sdiff_self_right
  simp_rw [Set.union_sdiff_self, Set.union_eq_right.mpr hts] at h_union
  rw [h_union]; rw [ENNReal.add_sub_cancel_left (hm_ne_top _ ht)]

@[deprecated (since := "2026-06-03")] alias addContent_diff_of_ne_top := addContent_sdiff_of_ne_top

Depends on / 依赖: ENNReal, ENNReal.add_sub_cancel_left, Set.union_eq_right.mpr, Set.union_sdiff_self, addContent_union, add_sub_cancel_left, disjoint_sdiff_self_right, hC.sdiff_mem, h_union, hm_ne_top, sdiff_mem, simp_rw, union_eq_right, union_sdiff_self
-/
lemma addContent_sdiff_of_ne_top (m : AddContent Real>=0∞ C) (hC : IsSetRing C)
    (hm_ne_top : forall s in C, m s != ∞)
    {s t : Set α} (hs : s in C) (ht : t in C) (hts : t subseteq s) :
    m (s \ t) = m s - m t := by
  have h_union : m (t union s \ t) = m t + m (s \ t) :=
    addContent_union hC ht (hC.sdiff_mem hs ht) disjoint_sdiff_self_right
  simp_rw [Set.union_sdiff_self, Set.union_eq_right.mpr hts] at h_union
  rw [h_union]; rw [ENNReal.add_sub_cancel_left (hm_ne_top _ ht)]

@[deprecated (since := "2026-06-03")] alias addContent_diff_of_ne_top := addContent_sdiff_of_ne_top

/--
theorem `addContent_iUnion_eq_sum_of_tendsto_zero` / 定理 `addContent_iUnion_eq_sum_of_tendsto_zero`

English:
theorem addContent_iUnion_eq_sum_of_tendsto_zero
  statement: (hC : IsSetRing C) (m : AddContent Real>=0∞ C)
  proof: by
  -- We use the continuity of `m` at `∅` on the sequence `n ↦ (⋃ i, f i) \ (Set.accumulate f n)`
  let s : Nat -> Set α := fun n => (⋃ i, f i) \ Set.accumulate f n
  have hCs n : s n in C := hC.sdiff_mem hUf (hC.accumulate_mem hf n)
  have h_tendsto : Tendsto (fun n => m (s n)) atTop (𝓝 0) := by
    refine hm_tendsto hCs ?_ ?_
    · intro i j hij x hxj
      rw [Set.mem_sdiff] at hxj ⊢
      exact ⟨hxj.1, fun hxi => hxj.2 (Set.monotone_accumulate hij hxi)⟩
    · simp_rw [s, Set.sdiff_eq]
      rw [Set.iInter_inter_distrib]; rw [Set.iInter_const]; rw [← Set.compl_iUnion]; rw [Set.iUnion_accumulate]
      exact Set.inter_compl_self _
  have hmsn n : m (s n) = m (⋃ i, f i) - ∑ i in Finset.range (n + 1), m (f i) := by
    rw [addContent_sdiff_of_ne_top m hC hm_ne_top hUf (hC.accumulate_mem hf n)
      (Set.accumulate_subset_iUnion _)]; rw [addContent_accumulate m hC h_disj hf n]
  simp_rw [hmsn] at h_tendsto
  refine tendsto_nhds_unique ?_ (ENNReal.tendsto_nat_tsum fun i => m (f i))
  refine (Filter.tendsto_add_atTop_iff_nat 1).mp ?_
  rwa [ENNReal.tendsto_const_sub_nhds_zero_iff (hm_ne_top _ hUf) (fun n => ?_)] at h_tendsto
  rw [← addContent_accumulate m hC h_disj hf]
  exact addContent_mono hC.isSetSemiring (hC.accumulate_mem hf n) hUf
    (Set.accumulate_subset_iUnion _)

中文:
定理 addContent_iUnion_eq_sum_of_tendsto_zero
  结论: (hC : 是集合环 C) (m : 加法内容 实数>=0∞ C)
  证明: by
  -- We use the continuity of `m` at `∅` on the sequence `n ↦ (⋃ i, f i) \ (Set.accumulate f n)`
  let s : Nat -> Set α := fun n => (⋃ i, f i) \ Set.accumulate f n
  have hCs n : s n in C := hC.sdiff_mem hUf (hC.accumulate_mem hf n)
  have h_tendsto : Tendsto (fun n => m (s n)) atTop (𝓝 0) := by
    refine hm_tendsto hCs ?_ ?_
    · intro i j hij x hxj
      rw [Set.mem_sdiff] at hxj ⊢
      exact ⟨hxj.1, fun hxi => hxj.2 (Set.monotone_accumulate hij hxi)⟩
    · simp_rw [s, Set.sdiff_eq]
      rw [Set.iInter_inter_distrib]; rw [Set.iInter_const]; rw [← Set.compl_iUnion]; rw [Set.iUnion_accumulate]
      exact Set.inter_compl_self _
  have hmsn n : m (s n) = m (⋃ i, f i) - ∑ i in Finset.range (n + 1), m (f i) := by
    rw [addContent_sdiff_of_ne_top m hC hm_ne_top hUf (hC.accumulate_mem hf n)
      (Set.accumulate_subset_iUnion _)]; rw [addContent_accumulate m hC h_disj hf n]
  simp_rw [hmsn] at h_tendsto
  refine tendsto_nhds_unique ?_ (ENNReal.tendsto_nat_tsum fun i => m (f i))
  refine (Filter.tendsto_add_atTop_iff_nat 1).mp ?_
  rwa [ENNReal.tendsto_const_sub_nhds_zero_iff (hm_ne_top _ hUf) (fun n => ?_)] at h_tendsto
  rw [← addContent_accumulate m hC h_disj hf]
  exact addContent_mono hC.isSetSemiring (hC.accumulate_mem hf n) hUf
    (Set.accumulate_subset_iUnion _)
-/
theorem addContent_iUnion_eq_sum_of_tendsto_zero (hC : IsSetRing C) (m : AddContent Real>=0∞ C)
    (hm_ne_top : forall s in C, m s != ∞)
    (hm_tendsto : forall ⦃s : Nat -> Set α⦄ (_ : forall n, s n in C),
      Antitone s -> (⋂ n, s n) = ∅ -> Tendsto (fun n => m (s n)) atTop (𝓝 0))
    ⦃f : Nat -> Set α⦄ (hf : forall i, f i in C) (hUf : (⋃ i, f i) in C)
    (h_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  -- We use the continuity of `m` at `∅` on the sequence `n ↦ (⋃ i, f i) \ (Set.accumulate f n)`
  let s : Nat -> Set α := fun n => (⋃ i, f i) \ Set.accumulate f n
  have hCs n : s n in C := hC.sdiff_mem hUf (hC.accumulate_mem hf n)
  have h_tendsto : Tendsto (fun n => m (s n)) atTop (𝓝 0) := by
    refine hm_tendsto hCs ?_ ?_
    · intro i j hij x hxj
      rw [Set.mem_sdiff] at hxj ⊢
      exact ⟨hxj.1, fun hxi => hxj.2 (Set.monotone_accumulate hij hxi)⟩
    · simp_rw [s, Set.sdiff_eq]
      rw [Set.iInter_inter_distrib]; rw [Set.iInter_const]; rw [← Set.compl_iUnion]; rw [Set.iUnion_accumulate]
      exact Set.inter_compl_self _
  have hmsn n : m (s n) = m (⋃ i, f i) - ∑ i in Finset.range (n + 1), m (f i) := by
    rw [addContent_sdiff_of_ne_top m hC hm_ne_top hUf (hC.accumulate_mem hf n)
      (Set.accumulate_subset_iUnion _)]; rw [addContent_accumulate m hC h_disj hf n]
  simp_rw [hmsn] at h_tendsto
  refine tendsto_nhds_unique ?_ (ENNReal.tendsto_nat_tsum fun i => m (f i))
  refine (Filter.tendsto_add_atTop_iff_nat 1).mp ?_
  rwa [ENNReal.tendsto_const_sub_nhds_zero_iff (hm_ne_top _ hUf) (fun n => ?_)] at h_tendsto
  rw [← addContent_accumulate m hC h_disj hf]
  exact addContent_mono hC.isSetSemiring (hC.accumulate_mem hf n) hUf
    (Set.accumulate_subset_iUnion _)

/--
theorem `tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum` / 定理 `tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum`

English:
theorem tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum
  proof: by
  rw [← iUnion_disjointed]; rw [m_iUnion _ (hC.disjointed_mem hf) (by rwa [iUnion_disjointed])
      (disjoint_disjointed f)]
  have h n : m (f n) = ∑ i in range (n + 1), m (disjointed f i) := by
    nth_rw 1 [← addContent_accumulate _ hC (disjoint_disjointed f) (hC.disjointed_mem hf),
    ← hf_mono.partialSups_eq, ← partialSups_disjointed, partialSups_eq_biSup, accumulate]
    rfl
  simp_rw [h]
  refine (tendsto_add_atTop_iff_nat (f := (fun k => ∑ i in range k, m (disjointed f i))) 1).2 ?_
  exact ENNReal.tendsto_nat_tsum _

中文:
定理 tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum
  证明: by
  rw [← iUnion_disjointed]; rw [m_iUnion _ (hC.disjointed_mem hf) (by rwa [iUnion_disjointed])
      (disjoint_disjointed f)]
  have h n : m (f n) = ∑ i in range (n + 1), m (disjointed f i) := by
    nth_rw 1 [← addContent_accumulate _ hC (disjoint_disjointed f) (hC.disjointed_mem hf),
    ← hf_mono.partialSups_eq, ← partialSups_disjointed, partialSups_eq_biSup, accumulate]
    rfl
  simp_rw [h]
  refine (tendsto_add_atTop_iff_nat (f := (fun k => ∑ i in range k, m (disjointed f i))) 1).2 ?_
  exact ENNReal.tendsto_nat_tsum _

Depends on / 依赖: ENNReal, ENNReal.tendsto_nat_t, accumulate, addContent_accumulate, disjoint_disjointed, disjointed, disjointed_mem, hC.disjointed_mem, hf_mono, hf_mono.partialSups_eq, iUnion_disjointed, m_iUnion, nth_rw, partialSups_disjointed, partialSups_eq, partialSups_eq_biSup, simp_rw, tendsto_add_atTop_iff_nat, tendsto_nat_t
-/
theorem tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum
    {m : AddContent Real>=0∞ C} (hC : IsSetRing C)
    (m_iUnion : forall (f : Nat -> Set α) (_ : forall i, f i in C) (_ : (⋃ i, f i) in C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i))
    ⦃f : Nat -> Set α⦄ (hf_mono : Monotone f) (hf : forall i, f i in C) (hf_Union : ⋃ i, f i in C) :
    Tendsto (fun n => m (f n)) atTop (𝓝 (m (⋃ i, f i))) := by
  rw [← iUnion_disjointed]; rw [m_iUnion _ (hC.disjointed_mem hf) (by rwa [iUnion_disjointed])
      (disjoint_disjointed f)]
  have h n : m (f n) = ∑ i in range (n + 1), m (disjointed f i) := by
    nth_rw 1 [← addContent_accumulate _ hC (disjoint_disjointed f) (hC.disjointed_mem hf),
    ← hf_mono.partialSups_eq, ← partialSups_disjointed, partialSups_eq_biSup, accumulate]
    rfl
  simp_rw [h]
  refine (tendsto_add_atTop_iff_nat (f := (fun k => ∑ i in range k, m (disjointed f i))) 1).2 ?_
  exact ENNReal.tendsto_nat_tsum _

/--
theorem `isSigmaSubadditive_of_addContent_iUnion_eq_tsum` / 定理 `isSigmaSubadditive_of_addContent_iUnion_eq_tsum`

English:
theorem isSigmaSubadditive_of_addContent_iUnion_eq_tsum
  statement: {m : AddContent Real>=0∞ C} (hC : IsSetRing C)
  proof: by
  intro f hf hf_Union
  have h_tendsto : Tendsto (fun n => m (partialSups f n)) atTop (𝓝 (m (⋃ i, f i))) := by
    rw [← iSup_eq_iUnion]; rw [← iSup_partialSups_eq]
    refine tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum hC m_iUnion
      (partialSups_monotone f) (hC.partialSups_mem hf) ?_
    rwa [← iSup_eq_iUnion, iSup_partialSups_eq]
  have h_tendsto' : Tendsto (fun n => ∑ i in range (n + 1), m (f i)) atTop (𝓝 (∑' i, m (f i))) := by
    rw [tendsto_add_atTop_iff_nat (f := (fun k => ∑ i in range k]; rw [m (f i))) 1]
    exact ENNReal.tendsto_nat_tsum _
  refine le_of_tendsto_of_tendsto' h_tendsto h_tendsto' fun _ => ?_
  rw [partialSups_eq_biUnion_range]
  exact addContent_biUnion_le hC (fun _ _ => hf _)

中文:
定理 isSigmaSubadditive_of_addContent_iUnion_eq_tsum
  结论: {m : 加法内容 实数>=0∞ C} (hC : 是集合环 C)
  证明: by
  intro f hf hf_Union
  have h_tendsto : Tendsto (fun n => m (partialSups f n)) atTop (𝓝 (m (⋃ i, f i))) := by
    rw [← iSup_eq_iUnion]; rw [← iSup_partialSups_eq]
    refine tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum hC m_iUnion
      (partialSups_monotone f) (hC.partialSups_mem hf) ?_
    rwa [← iSup_eq_iUnion, iSup_partialSups_eq]
  have h_tendsto' : Tendsto (fun n => ∑ i in range (n + 1), m (f i)) atTop (𝓝 (∑' i, m (f i))) := by
    rw [tendsto_add_atTop_iff_nat (f := (fun k => ∑ i in range k]; rw [m (f i))) 1]
    exact ENNReal.tendsto_nat_tsum _
  refine le_of_tendsto_of_tendsto' h_tendsto h_tendsto' fun _ => ?_
  rw [partialSups_eq_biUnion_range]
  exact addContent_biUnion_le hC (fun _ _ => hf _)

Depends on / 依赖: Tendsto, hC.partialSups_mem, h_tendsto, hf_Union, iSup_eq_iUnion, iSup_partialSups_eq, m_iUnion, partialSups, partialSups_mem, partialSups_monotone, tendsto_add_atTop_iff_nat, tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum
-/
theorem isSigmaSubadditive_of_addContent_iUnion_eq_tsum {m : AddContent Real>=0∞ C} (hC : IsSetRing C)
    (m_iUnion : forall (f : Nat -> Set α) (_ : forall i, f i in C) (_ : (⋃ i, f i) in C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i)) :
    m.IsSigmaSubadditive := by
  intro f hf hf_Union
  have h_tendsto : Tendsto (fun n => m (partialSups f n)) atTop (𝓝 (m (⋃ i, f i))) := by
    rw [← iSup_eq_iUnion]; rw [← iSup_partialSups_eq]
    refine tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum hC m_iUnion
      (partialSups_monotone f) (hC.partialSups_mem hf) ?_
    rwa [← iSup_eq_iUnion, iSup_partialSups_eq]
  have h_tendsto' : Tendsto (fun n => ∑ i in range (n + 1), m (f i)) atTop (𝓝 (∑' i, m (f i))) := by
    rw [tendsto_add_atTop_iff_nat (f := (fun k => ∑ i in range k]; rw [m (f i))) 1]
    exact ENNReal.tendsto_nat_tsum _
  refine le_of_tendsto_of_tendsto' h_tendsto h_tendsto' fun _ => ?_
  rw [partialSups_eq_biUnion_range]
  exact addContent_biUnion_le hC (fun _ _ => hf _)

/--
theorem `addContent_iUnion_eq_tsum_of_addContent_iUnion_eq_iSup` / 定理 `addContent_iUnion_eq_tsum_of_addContent_iUnion_eq_iSup`

English:
theorem addContent_iUnion_eq_tsum_of_addContent_iUnion_eq_iSup
  proof: calc
    m (⋃ i, s i) = m (⋃ i, accumulate s i) := by simp
    _ = ⨆ i, m (accumulate s i) :=
      hm_iSup (fun n => IsSetRing.accumulate_mem hC hs n) monotone_accumulate
    _ = ⨆ i, ∑ j in range (i + 1), m (s j) :=
      iSup_congr fun i => addContent_accumulate m hC hd hs i
    _ = ∑' i, m (s i) :=
      (ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1)).symm

中文:
定理 addContent_iUnion_eq_tsum_of_addContent_iUnion_eq_iSup
  证明: calc
    m (⋃ i, s i) = m (⋃ i, accumulate s i) := by simp
    _ = ⨆ i, m (accumulate s i) :=
      hm_iSup (fun n => IsSetRing.accumulate_mem hC hs n) monotone_accumulate
    _ = ⨆ i, ∑ j in range (i + 1), m (s j) :=
      iSup_congr fun i => addContent_accumulate m hC hd hs i
    _ = ∑' i, m (s i) :=
      (ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1)).symm

Depends on / 依赖: ENNReal, ENNReal.tsum_eq_iSup_nat, IsSetRing, IsSetRing.accumulate_mem, accumulate, accumulate_mem, addContent_accumulate, hm_iSup, iSup_congr, monotone_accumulate, tendsto_add_atTop_nat, tsum_eq_iSup_nat
-/
theorem addContent_iUnion_eq_tsum_of_addContent_iUnion_eq_iSup
    (hC : IsSetRing C) (m : AddContent Real>=0∞ C)
    {s : Nat -> Set α} (hd : Pairwise (Disjoint on s)) (hs : forall i, s i in C)
    (hm_iSup : forall ⦃s : Nat -> Set α⦄, (forall n, s n in C) -> Monotone s -> m (⋃ n, s n) = ⨆ n, m (s n)) :
    m (⋃ i, s i) = ∑' i, m (s i) :=
  calc
    m (⋃ i, s i) = m (⋃ i, accumulate s i) := by simp
    _ = ⨆ i, m (accumulate s i) :=
      hm_iSup (fun n => IsSetRing.accumulate_mem hC hs n) monotone_accumulate
    _ = ⨆ i, ∑ j in range (i + 1), m (s j) :=
      iSup_congr fun i => addContent_accumulate m hC hd hs i
    _ = ∑' i, m (s i) :=
      (ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1)).symm

end IsSetRing

end MeasureTheory
