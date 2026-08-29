/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Reid Barton
-/
module

public import Mathlib.Topology.Separation.Regular

/-!
# The shrinking lemma

In this file we prove a few versions of the shrinking lemma. The lemma says that in a normal
topological space a point finite open covering can be “shrunk”: for a point finite open covering
`u : ι → Set X` there exists a refinement `v : ι → Set X` such that `closure (v i) ⊆ u i`.

For finite or countable coverings this lemma can be proved without the axiom of choice, see
[ncatlab](https://ncatlab.org/nlab/show/shrinking+lemma) for details. We only formalize the most
general result that works for any covering but needs the axiom of choice.

We prove two versions of the lemma:

* `exists_subset_iUnion_closure_subset` deals with a covering of a closed set in a normal space;
* `exists_iUnion_eq_closure_subset` deals with a covering of the whole space.

## Tags

normal space, shrinking lemma
-/

@[expose] public section

open Set Function

noncomputable section

variable {ι X : Type*} [TopologicalSpace X]

namespace ShrinkingLemma

-- the trivial refinement needs `u` to be a covering
/--
Definition of `PartialRefinement` / `PartialRefinement` 的定义

English:
structure PartialRefinement
  parameters: (u : ι -> Set X) (s : Set X) (p : Set X -> Prop)
  axioms and operations (7):
    - toFun : ι -> Set X
    - carrier : Set ι
    - isOpen : forall i, IsOpen (toFun i)
    - subset_iUnion : s subseteq ⋃ i, toFun i
    - closure_subset : forall {i}, i in carrier -> closure (toFun i) subseteq u i
    - pred_of_mem({i} (hi : i in carrier)) : p (toFun i)
    - apply_eq : forall {i}, i ∉ carrier -> toFun i = u i

中文:
结构 PartialRefinement
  参数: (u : ι -> 集合 X) (s : 集合 X) (p : 集合 X -> 命题)
  公理与运算 (7 个):
    - toFun : ι -> 集合 X
    - carrier : 集合 ι
    - isOpen : 对任意 i, 是开集 (toFun i)
    - subset_iUnion : s subseteq ⋃ i, toFun i
    - closure_subset : 对任意 {i}, i in carrier -> closure (toFun i) subseteq u i
    - pred_of_mem({i} (hi : i in carrier)) : p (toFun i)
    - apply_eq : 对任意 {i}, i ∉ carrier -> toFun i = u i
-/
@[ext] structure PartialRefinement (u : ι -> Set X) (s : Set X) (p : Set X -> Prop) where
  /-- A family of sets that form a partial refinement of `u`. -/
  toFun : ι -> Set X
  /-- The set of indexes `i` such that `i`-th set is already shrunk. -/
  carrier : Set ι
  /-- Each set from the partially refined family is open. -/
  protected isOpen : forall i, IsOpen (toFun i)
  /-- The partially refined family still covers the set. -/
  subset_iUnion : s subseteq ⋃ i, toFun i
  /-- For each `i ∈ carrier`, the original set includes the closure of the refined set. -/
  closure_subset : forall {i}, i in carrier -> closure (toFun i) subseteq u i
  /-- For each `i ∈ carrier`, the refined set satisfies `p`. -/
  pred_of_mem {i} (hi : i in carrier) : p (toFun i)
  /-- Sets that correspond to `i ∉ carrier` are not modified. -/
  apply_eq : forall {i}, i ∉ carrier -> toFun i = u i

namespace PartialRefinement

variable {u : ι -> Set X} {s : Set X} {p : Set X -> Prop}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (PartialRefinement u s p) fun _ => ι -> Set X
  body: ⟨toFun⟩

中文:
实例 :
  签名: CoeFun (PartialRefinement u s p) fun _ => ι -> 集合 X
  定义体: ⟨toFun⟩
-/
instance : CoeFun (PartialRefinement u s p) fun _ => ι -> Set X := ⟨toFun⟩

/--
theorem `subset` / 定理 `subset`

English:
theorem subset
  given: (v : PartialRefinement u s p) (i : ι)
  statement: v i subseteq u i
  proof: by
  classical
  exact if h : i in v.carrier then subset_closure.trans (v.closure_subset h) else (v.apply_eq h).le

中文:
定理 subset
  条件: (v : PartialRefinement u s p) (i : ι)
  结论: v i subseteq u i
  证明: by
  classical
  exact if h : i in v.carrier then subset_closure.trans (v.closure_subset h) else (v.apply_eq h).le
-/
protected theorem subset (v : PartialRefinement u s p) (i : ι) : v i subseteq u i := by
  classical
  exact if h : i in v.carrier then subset_closure.trans (v.closure_subset h) else (v.apply_eq h).le

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (PartialRefinement u s p)
  body: v₁.carrier subseteq v₂.carrier ∧ forall i in v₁.carrier, v₁ i = v₂ i
  le_refl _ := ⟨Subset.refl _, fun _ _ => rfl⟩
  le_trans _ _ _ h₁₂ h₂₃ :=
    ⟨Subset.trans h₁₂.1 h₂₃.1, fun i hi => (h₁₂.2 i hi).trans (h₂₃.2 i <| h₁₂.1 hi)⟩
  le_antisymm v₁ v₂ h₁₂ h₂₁ :=
    have hc : v₁.carrier = v₂.carrier := Subset.antisymm h₁₂.1 h₂₁.1
    PartialRefinement.ext
      (funext fun x =>
        if hx : x in v₁.carrier then h₁₂.2 _ hx
        else (v₁.apply_eq hx).trans (Eq.symm <| v₂.apply_eq <| hc ▸ hx))
      hc

中文:
实例 :
  签名: 偏序 (PartialRefinement u s p)
  定义体: v₁.carrier subseteq v₂.carrier ∧ forall i in v₁.carrier, v₁ i = v₂ i
  le_refl _ := ⟨Subset.refl _, fun _ _ => rfl⟩
  le_trans _ _ _ h₁₂ h₂₃ :=
    ⟨Subset.trans h₁₂.1 h₂₃.1, fun i hi => (h₁₂.2 i hi).trans (h₂₃.2 i <| h₁₂.1 hi)⟩
  le_antisymm v₁ v₂ h₁₂ h₂₁ :=
    have hc : v₁.carrier = v₂.carrier := Subset.antisymm h₁₂.1 h₂₁.1
    PartialRefinement.ext
      (funext fun x =>
        if hx : x in v₁.carrier then h₁₂.2 _ hx
        else (v₁.apply_eq hx).trans (Eq.symm <| v₂.apply_eq <| hc ▸ hx))
      hc

Depends on / 依赖: carrier, subseteq
-/
instance : PartialOrder (PartialRefinement u s p) where
  le v₁ v₂ := v₁.carrier subseteq v₂.carrier ∧ forall i in v₁.carrier, v₁ i = v₂ i
  le_refl _ := ⟨Subset.refl _, fun _ _ => rfl⟩
  le_trans _ _ _ h₁₂ h₂₃ :=
    ⟨Subset.trans h₁₂.1 h₂₃.1, fun i hi => (h₁₂.2 i hi).trans (h₂₃.2 i <| h₁₂.1 hi)⟩
  le_antisymm v₁ v₂ h₁₂ h₂₁ :=
    have hc : v₁.carrier = v₂.carrier := Subset.antisymm h₁₂.1 h₂₁.1
    PartialRefinement.ext
      (funext fun x =>
        if hx : x in v₁.carrier then h₁₂.2 _ hx
        else (v₁.apply_eq hx).trans (Eq.symm <| v₂.apply_eq <| hc ▸ hx))
      hc

/--
theorem `apply_eq_of_chain` / 定理 `apply_eq_of_chain`

English:
theorem apply_eq_of_chain
  statement: {c : Set (PartialRefinement u s p)} (hc : IsChain (· <= ·) c) {v₁ v₂}
  proof: (hc.total h₁ h₂).elim (fun hle => hle.2 _ hi₁) (fun hle => (hle.2 _ hi₂).symm)

中文:
定理 apply_eq_of_chain
  结论: {c : 集合 (PartialRefinement u s p)} (hc : IsChain (· <= ·) c) {v₁ v₂}
  证明: (hc.total h₁ h₂).elim (fun hle => hle.2 _ hi₁) (fun hle => (hle.2 _ hi₂).symm)

Depends on / 依赖: hc.total
-/
theorem apply_eq_of_chain {c : Set (PartialRefinement u s p)} (hc : IsChain (· <= ·) c) {v₁ v₂}
    (h₁ : v₁ in c) (h₂ : v₂ in c) {i} (hi₁ : i in v₁.carrier) (hi₂ : i in v₂.carrier) :
    v₁ i = v₂ i :=
  (hc.total h₁ h₂).elim (fun hle => hle.2 _ hi₁) (fun hle => (hle.2 _ hi₂).symm)

/--
Definition of `chainSupCarrier` / `chainSupCarrier` 的定义

English:
definition chainSupCarrier
  signature: (c : Set (PartialRefinement u s p))
  body: ⋃ v in c, carrier v

中文:
定义 chainSupCarrier
  签名: (c : 集合 (PartialRefinement u s p))
  定义体: ⋃ v in c, carrier v

Depends on / 依赖: carrier
-/
def chainSupCarrier (c : Set (PartialRefinement u s p)) : Set ι :=
  ⋃ v in c, carrier v

open scoped Classical in
/--
Definition of `find` / `find` 的定义

English:
definition find
  signature: (c : Set (PartialRefinement u s p)) (ne : c.Nonempty) (i : ι)
  body: if hi : exists v in c, i in carrier v then hi.choose else ne.some

中文:
定义 find
  签名: (c : 集合 (PartialRefinement u s p)) (ne : c.非空) (i : ι)
  定义体: if hi : exists v in c, i in carrier v then hi.choose else ne.some

Depends on / 依赖: carrier, hi.choose, ne.some
-/
def find (c : Set (PartialRefinement u s p)) (ne : c.Nonempty) (i : ι) : PartialRefinement u s p :=
  if hi : exists v in c, i in carrier v then hi.choose else ne.some

/--
theorem `find_mem` / 定理 `find_mem`

English:
theorem find_mem
  given: {c : Set (PartialRefinement u s p)} (i : ι) (ne : c.Nonempty)
  proof: by
  rw [find]
  split_ifs with h
  exacts [h.choose_spec.1, ne.some_mem]

中文:
定理 find_mem
  条件: {c : 集合 (PartialRefinement u s p)} (i : ι) (ne : c.非空)
  证明: by
  rw [find]
  split_ifs with h
  exacts [h.choose_spec.1, ne.some_mem]

Depends on / 依赖: choose_spec, exacts, h.choose_spec, ne.some_mem, some_mem, split_ifs
-/
theorem find_mem {c : Set (PartialRefinement u s p)} (i : ι) (ne : c.Nonempty) :
    find c ne i in c := by
  rw [find]
  split_ifs with h
  exacts [h.choose_spec.1, ne.some_mem]

/--
theorem `mem_find_carrier_iff` / 定理 `mem_find_carrier_iff`

English:
theorem mem_find_carrier_iff
  given: {c : Set (PartialRefinement u s p)} {i : ι} (ne : c.Nonempty)
  proof: by
  rw [find]
  split_ifs with h
  · have := h.choose_spec
    exact iff_of_true this.2 (mem_iUnion₂.2 ⟨_, this.1, this.2⟩)
  · push Not at h
    refine iff_of_false (h _ ne.some_mem) ?_
    simpa only [chainSupCarrier, mem_iUnion₂, not_exists]

中文:
定理 mem_find_carrier_iff
  条件: {c : 集合 (PartialRefinement u s p)} {i : ι} (ne : c.非空)
  证明: by
  rw [find]
  split_ifs with h
  · have := h.choose_spec
    exact iff_of_true this.2 (mem_iUnion₂.2 ⟨_, this.1, this.2⟩)
  · push Not at h
    refine iff_of_false (h _ ne.some_mem) ?_
    simpa only [chainSupCarrier, mem_iUnion₂, not_exists]

Depends on / 依赖: chainSupCarrier, choose_spec, h.choose_spec, iff_of_false, iff_of_true, ne.some_mem, not_exists, some_mem, split_ifs
-/
theorem mem_find_carrier_iff {c : Set (PartialRefinement u s p)} {i : ι} (ne : c.Nonempty) :
    i in (find c ne i).carrier ↔ i in chainSupCarrier c := by
  rw [find]
  split_ifs with h
  · have := h.choose_spec
    exact iff_of_true this.2 (mem_iUnion₂.2 ⟨_, this.1, this.2⟩)
  · push Not at h
    refine iff_of_false (h _ ne.some_mem) ?_
    simpa only [chainSupCarrier, mem_iUnion₂, not_exists]

/--
theorem `find_apply_of_mem` / 定理 `find_apply_of_mem`

English:
theorem find_apply_of_mem
  statement: {c : Set (PartialRefinement u s p)} (hc : IsChain (· <= ·) c)
  proof: apply_eq_of_chain hc (find_mem _ _) hv ((mem_find_carrier_iff _).2 <| mem_iUnion₂.2 ⟨v, hv, hi⟩)
    hi

中文:
定理 find_apply_of_mem
  结论: {c : 集合 (PartialRefinement u s p)} (hc : IsChain (· <= ·) c)
  证明: apply_eq_of_chain hc (find_mem _ _) hv ((mem_find_carrier_iff _).2 <| mem_iUnion₂.2 ⟨v, hv, hi⟩)
    hi

Depends on / 依赖: apply_eq_of_chain, find_mem, mem_find_carrier_iff
-/
theorem find_apply_of_mem {c : Set (PartialRefinement u s p)} (hc : IsChain (· <= ·) c)
    (ne : c.Nonempty) {i v} (hv : v in c) (hi : i in carrier v) : find c ne i i = v i :=
  apply_eq_of_chain hc (find_mem _ _) hv ((mem_find_carrier_iff _).2 <| mem_iUnion₂.2 ⟨v, hv, hi⟩)
    hi

/--
Definition of `chainSup` / `chainSup` 的定义

English:
definition chainSup
  signature: (c : Set (PartialRefinement u s p)) (hc : IsChain (· <= ·) c) (ne : c.Nonempty)
  body: find c ne i i
  carrier := chainSupCarrier c
  isOpen i := (find _ _ _).isOpen i
subset_iUnion x hxs := mem_iUnion.2 by
    rcases em (exists i, i ∉ chainSupCarrier c ∧ x in u i) with (⟨i, hi, hxi⟩ | hx)
    · use i
      simpa only [(find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)]
    · simp_rw [not_exists, not_and, not_imp_not, chainSupCarrier, mem_iUnion₂] at hx
      have : Nonempty (PartialRefinement u s p) := ⟨ne.some⟩
      choose! v hvc hiv using hx
      rcases (hfin x hxs).exists_maximalFor v _ (mem_iUnion.1 (hU hxs)) with
        ⟨i, hxi : x in u i, hmax : forall j, x in u j -> v i <= v j -> v j <= v i⟩
      rcases mem_iUnion.1 ((v i).subset_iUnion hxs) with ⟨j, hj⟩
      use j
      have hj' : x in u j := (v i).subset _ hj
      have : v j <= v i := (hc.total (hvc _ hxi) (hvc _ hj')).elim (hmax j hj') id
      simpa only [find_apply_of_mem hc ne (hvc _ hxi) (this.1 <| hiv _ hj')]
  closure_subset hi := (find c ne _).closure_subset ((mem_find_carrier_iff _).2 hi)
  pred_of_mem {i} hi := by
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hi
    simp only [mem_iUnion, exists_prop] at hv
    rw [find_apply_of_mem hc ne hv.1 hv.2]
    exact v.pred_of_mem hv.2
  apply_eq hi := (find c ne _).apply_eq (mt (mem_find_carrier_iff _).1 hi)

中文:
定义 chainSup
  签名: (c : 集合 (PartialRefinement u s p)) (hc : IsChain (· <= ·) c) (ne : c.非空)
  定义体: find c ne i i
  carrier := chainSupCarrier c
  isOpen i := (find _ _ _).isOpen i
subset_iUnion x hxs := mem_iUnion.2 by
    rcases em (exists i, i ∉ chainSupCarrier c ∧ x in u i) with (⟨i, hi, hxi⟩ | hx)
    · use i
      simpa only [(find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)]
    · simp_rw [not_exists, not_and, not_imp_not, chainSupCarrier, mem_iUnion₂] at hx
      have : Nonempty (PartialRefinement u s p) := ⟨ne.some⟩
      choose! v hvc hiv using hx
      rcases (hfin x hxs).exists_maximalFor v _ (mem_iUnion.1 (hU hxs)) with
        ⟨i, hxi : x in u i, hmax : forall j, x in u j -> v i <= v j -> v j <= v i⟩
      rcases mem_iUnion.1 ((v i).subset_iUnion hxs) with ⟨j, hj⟩
      use j
      have hj' : x in u j := (v i).subset _ hj
      have : v j <= v i := (hc.total (hvc _ hxi) (hvc _ hj')).elim (hmax j hj') id
      simpa only [find_apply_of_mem hc ne (hvc _ hxi) (this.1 <| hiv _ hj')]
  closure_subset hi := (find c ne _).closure_subset ((mem_find_carrier_iff _).2 hi)
  pred_of_mem {i} hi := by
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hi
    simp only [mem_iUnion, exists_prop] at hv
    rw [find_apply_of_mem hc ne hv.1 hv.2]
    exact v.pred_of_mem hv.2
  apply_eq hi := (find c ne _).apply_eq (mt (mem_find_carrier_iff _).1 hi)
-/
def chainSup (c : Set (PartialRefinement u s p)) (hc : IsChain (· <= ·) c) (ne : c.Nonempty)
    (hfin : forall x in s, { i | x in u i }.Finite) (hU : s subseteq ⋃ i, u i) : PartialRefinement u s p where
  toFun i := find c ne i i
  carrier := chainSupCarrier c
  isOpen i := (find _ _ _).isOpen i
subset_iUnion x hxs := mem_iUnion.2 by
    rcases em (exists i, i ∉ chainSupCarrier c ∧ x in u i) with (⟨i, hi, hxi⟩ | hx)
    · use i
      simpa only [(find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)]
    · simp_rw [not_exists, not_and, not_imp_not, chainSupCarrier, mem_iUnion₂] at hx
      have : Nonempty (PartialRefinement u s p) := ⟨ne.some⟩
      choose! v hvc hiv using hx
      rcases (hfin x hxs).exists_maximalFor v _ (mem_iUnion.1 (hU hxs)) with
        ⟨i, hxi : x in u i, hmax : forall j, x in u j -> v i <= v j -> v j <= v i⟩
      rcases mem_iUnion.1 ((v i).subset_iUnion hxs) with ⟨j, hj⟩
      use j
      have hj' : x in u j := (v i).subset _ hj
      have : v j <= v i := (hc.total (hvc _ hxi) (hvc _ hj')).elim (hmax j hj') id
      simpa only [find_apply_of_mem hc ne (hvc _ hxi) (this.1 <| hiv _ hj')]
  closure_subset hi := (find c ne _).closure_subset ((mem_find_carrier_iff _).2 hi)
  pred_of_mem {i} hi := by
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hi
    simp only [mem_iUnion, exists_prop] at hv
    rw [find_apply_of_mem hc ne hv.1 hv.2]
    exact v.pred_of_mem hv.2
  apply_eq hi := (find c ne _).apply_eq (mt (mem_find_carrier_iff _).1 hi)

/--
theorem `le_chainSup` / 定理 `le_chainSup`

English:
theorem le_chainSup
  statement: {c : Set (PartialRefinement u s p)} (hc : IsChain (· <= ·) c) (ne : c.Nonempty)
  proof: ⟨fun _ hi => mem_biUnion hv hi, fun _ hi => (find_apply_of_mem hc _ hv hi).symm⟩

中文:
定理 le_chainSup
  结论: {c : 集合 (PartialRefinement u s p)} (hc : IsChain (· <= ·) c) (ne : c.非空)
  证明: ⟨fun _ hi => mem_biUnion hv hi, fun _ hi => (find_apply_of_mem hc _ hv hi).symm⟩

Depends on / 依赖: find_apply_of_mem, mem_biUnion
-/
theorem le_chainSup {c : Set (PartialRefinement u s p)} (hc : IsChain (· <= ·) c) (ne : c.Nonempty)
    (hfin : forall x in s, { i | x in u i }.Finite) (hU : s subseteq ⋃ i, u i) {v} (hv : v in c) :
    v <= chainSup c hc ne hfin hU :=
  ⟨fun _ hi => mem_biUnion hv hi, fun _ hi => (find_apply_of_mem hc _ hv hi).symm⟩

/--
theorem `exists_gt` / 定理 `exists_gt`

English:
theorem exists_gt
  statement: [NormalSpace X] (v : PartialRefinement u s ⊤) (hs : IsClosed s)
  proof: by
  have I : (s inter ⋂ (j) (_ : j != i), (v j)ᶜ) subseteq v i := by
    simp only [subset_def, mem_inter_iff, mem_iInter, and_imp]
    intro x hxs H
    rcases mem_iUnion.1 (v.subset_iUnion hxs) with ⟨j, hj⟩
    exact (em (j = i)).elim (fun h => h ▸ hj) fun h => (H j h hj).elim
  have C : IsClosed (s inter ⋂ (j) (_ : j != i), (v j)ᶜ) :=
    IsClosed.inter hs (isClosed_biInter fun _ _ => isClosed_compl_iff.2 <| v.isOpen _)
  rcases normal_exists_closure_subset C (v.isOpen i) I with ⟨vi, ovi, hvi, cvi⟩
  classical
  refine ⟨⟨update v i vi, insert i v.carrier, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*, v.isOpen]
  · refine fun x hx => mem_iUnion.2 ?_
    by_cases! h : exists j != i, x in v j
    · rcases h with ⟨j, hji, hj⟩
      use j
      rwa [update_of_ne hji]
    · use i
      rw [update_self]
      exact hvi ⟨hx, mem_biInter h⟩
  · rintro j (rfl | hj)
    · rwa [update_self, ← v.apply_eq hi]
    · rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
      exact v.closure_subset hj
  · exact fun _ => trivial
  · intro j hj
    rw [mem_insert_iff]; rw [not_or] at hj
    rw [update_of_ne hj.1]; rw [v.apply_eq hj.2]
  · refine ⟨subset_insert _ _, fun j hj => ?_⟩
    exact (update_of_ne (ne_of_mem_of_not_mem hj hi) _ _).symm
  · exact fun hle => hi (hle.1 <| mem_insert _ _)

中文:
定理 存在_gt
  结论: [正规空间 X] (v : PartialRefinement u s ⊤) (hs : 是闭集 s)
  证明: by
  have I : (s inter ⋂ (j) (_ : j != i), (v j)ᶜ) subseteq v i := by
    simp only [subset_def, mem_inter_iff, mem_iInter, and_imp]
    intro x hxs H
    rcases mem_iUnion.1 (v.subset_iUnion hxs) with ⟨j, hj⟩
    exact (em (j = i)).elim (fun h => h ▸ hj) fun h => (H j h hj).elim
  have C : IsClosed (s inter ⋂ (j) (_ : j != i), (v j)ᶜ) :=
    IsClosed.inter hs (isClosed_biInter fun _ _ => isClosed_compl_iff.2 <| v.isOpen _)
  rcases normal_exists_closure_subset C (v.isOpen i) I with ⟨vi, ovi, hvi, cvi⟩
  classical
  refine ⟨⟨update v i vi, insert i v.carrier, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*, v.isOpen]
  · refine fun x hx => mem_iUnion.2 ?_
    by_cases! h : exists j != i, x in v j
    · rcases h with ⟨j, hji, hj⟩
      use j
      rwa [update_of_ne hji]
    · use i
      rw [update_self]
      exact hvi ⟨hx, mem_biInter h⟩
  · rintro j (rfl | hj)
    · rwa [update_self, ← v.apply_eq hi]
    · rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
      exact v.closure_subset hj
  · exact fun _ => trivial
  · intro j hj
    rw [mem_insert_iff]; rw [not_or] at hj
    rw [update_of_ne hj.1]; rw [v.apply_eq hj.2]
  · refine ⟨subset_insert _ _, fun j hj => ?_⟩
    exact (update_of_ne (ne_of_mem_of_not_mem hj hi) _ _).symm
  · exact fun hle => hi (hle.1 <| mem_insert _ _)

Depends on / 依赖: IsClosed, IsClosed.inter, and_imp, classical, isClosed_biInter, isClosed_compl_iff, isOpen, mem_iInter, mem_iUnion, mem_inter_iff, normal_exists_closure_subset, subset_def, subset_iUnion, subseteq, v.isOpen, v.subset_iUnion
-/
theorem exists_gt [NormalSpace X] (v : PartialRefinement u s ⊤) (hs : IsClosed s)
    (i : ι) (hi : i ∉ v.carrier) :
    exists v' : PartialRefinement u s ⊤, v < v' := by
  have I : (s inter ⋂ (j) (_ : j != i), (v j)ᶜ) subseteq v i := by
    simp only [subset_def, mem_inter_iff, mem_iInter, and_imp]
    intro x hxs H
    rcases mem_iUnion.1 (v.subset_iUnion hxs) with ⟨j, hj⟩
    exact (em (j = i)).elim (fun h => h ▸ hj) fun h => (H j h hj).elim
  have C : IsClosed (s inter ⋂ (j) (_ : j != i), (v j)ᶜ) :=
    IsClosed.inter hs (isClosed_biInter fun _ _ => isClosed_compl_iff.2 <| v.isOpen _)
  rcases normal_exists_closure_subset C (v.isOpen i) I with ⟨vi, ovi, hvi, cvi⟩
  classical
  refine ⟨⟨update v i vi, insert i v.carrier, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*, v.isOpen]
  · refine fun x hx => mem_iUnion.2 ?_
    by_cases! h : exists j != i, x in v j
    · rcases h with ⟨j, hji, hj⟩
      use j
      rwa [update_of_ne hji]
    · use i
      rw [update_self]
      exact hvi ⟨hx, mem_biInter h⟩
  · rintro j (rfl | hj)
    · rwa [update_self, ← v.apply_eq hi]
    · rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
      exact v.closure_subset hj
  · exact fun _ => trivial
  · intro j hj
    rw [mem_insert_iff]; rw [not_or] at hj
    rw [update_of_ne hj.1]; rw [v.apply_eq hj.2]
  · refine ⟨subset_insert _ _, fun j hj => ?_⟩
    exact (update_of_ne (ne_of_mem_of_not_mem hj hi) _ _).symm
  · exact fun hle => hi (hle.1 <| mem_insert _ _)

end PartialRefinement

end ShrinkingLemma

section NormalSpace

open ShrinkingLemma

variable {u : ι -> Set X} {s : Set X} [NormalSpace X]

/--
theorem `exists_subset_iUnion_closure_subset` / 定理 `exists_subset_iUnion_closure_subset`

English:
theorem exists_subset_iUnion_closure_subset
  statement: (hs : IsClosed s) (uo : forall i, IsOpen (u i))
  proof: by
  have : Nonempty (PartialRefinement u s ⊤) :=
    ⟨⟨u, ∅, uo, us, False.elim, False.elim, fun _ => rfl⟩⟩
  have : forall c : Set (PartialRefinement u s ⊤),
      IsChain (· <= ·) c -> c.Nonempty -> exists ub, forall v in c, v <= ub :=
    fun c hc ne => ⟨.chainSup c hc ne uf us, fun v hv => PartialRefinement.le_chainSup _ _ _ _ hv⟩
  rcases zorn_le_nonempty this with ⟨v, hv⟩
  suffices forall i, i in v.carrier from
    ⟨v, v.subset_iUnion, fun i => v.isOpen _, fun i => v.closure_subset (this i)⟩
  intro i; by_contra hi
  rcases v.exists_gt hs i hi with ⟨v', hlt⟩
  exact hv.not_lt hlt

中文:
定理 存在_subset_iUnion_closure_subset
  结论: (hs : 是闭集 s) (uo : 对任意 i, 是开集 (u i))
  证明: by
  have : Nonempty (PartialRefinement u s ⊤) :=
    ⟨⟨u, ∅, uo, us, False.elim, False.elim, fun _ => rfl⟩⟩
  have : forall c : Set (PartialRefinement u s ⊤),
      IsChain (· <= ·) c -> c.Nonempty -> exists ub, forall v in c, v <= ub :=
    fun c hc ne => ⟨.chainSup c hc ne uf us, fun v hv => PartialRefinement.le_chainSup _ _ _ _ hv⟩
  rcases zorn_le_nonempty this with ⟨v, hv⟩
  suffices forall i, i in v.carrier from
    ⟨v, v.subset_iUnion, fun i => v.isOpen _, fun i => v.closure_subset (this i)⟩
  intro i; by_contra hi
  rcases v.exists_gt hs i hi with ⟨v', hlt⟩
  exact hv.not_lt hlt

Depends on / 依赖: False.elim, IsChain, Nonempty, PartialRefinement, PartialRefinement.le_chainSup, c.Nonempty, carrier, chainSup, closure_subset, isOpen, le_chainSup, subset_iUnion, v.carrier, v.closure_subset, v.isOpen, v.subset_iUnion, zorn_le_nonempty
-/
theorem exists_subset_iUnion_closure_subset (hs : IsClosed s) (uo : forall i, IsOpen (u i))
    (uf : forall x in s, { i | x in u i }.Finite) (us : s subseteq ⋃ i, u i) :
    exists v : ι -> Set X, s subseteq iUnion v ∧ (forall i, IsOpen (v i)) ∧ forall i, closure (v i) subseteq u i := by
  have : Nonempty (PartialRefinement u s ⊤) :=
    ⟨⟨u, ∅, uo, us, False.elim, False.elim, fun _ => rfl⟩⟩
  have : forall c : Set (PartialRefinement u s ⊤),
      IsChain (· <= ·) c -> c.Nonempty -> exists ub, forall v in c, v <= ub :=
    fun c hc ne => ⟨.chainSup c hc ne uf us, fun v hv => PartialRefinement.le_chainSup _ _ _ _ hv⟩
  rcases zorn_le_nonempty this with ⟨v, hv⟩
  suffices forall i, i in v.carrier from
    ⟨v, v.subset_iUnion, fun i => v.isOpen _, fun i => v.closure_subset (this i)⟩
  intro i; by_contra hi
  rcases v.exists_gt hs i hi with ⟨v', hlt⟩
  exact hv.not_lt hlt

/--
theorem `exists_subset_iUnion_closed_subset` / 定理 `exists_subset_iUnion_closed_subset`

English:
theorem exists_subset_iUnion_closed_subset
  statement: (hs : IsClosed s) (uo : forall i, IsOpen (u i))
  proof: let ⟨v, hsv, _, hv⟩ := exists_subset_iUnion_closure_subset hs uo uf us
  ⟨fun i => closure (v i), Subset.trans hsv (iUnion_mono fun _ => subset_closure),
    fun _ => isClosed_closure, hv⟩

中文:
定理 存在_subset_iUnion_closed_subset
  结论: (hs : 是闭集 s) (uo : 对任意 i, 是开集 (u i))
  证明: let ⟨v, hsv, _, hv⟩ := exists_subset_iUnion_closure_subset hs uo uf us
  ⟨fun i => closure (v i), Subset.trans hsv (iUnion_mono fun _ => subset_closure),
    fun _ => isClosed_closure, hv⟩

Depends on / 依赖: Subset, Subset.trans, closure, exists_subset_iUnion_closure_subset, iUnion_mono, isClosed_closure, subset_closure
-/
theorem exists_subset_iUnion_closed_subset (hs : IsClosed s) (uo : forall i, IsOpen (u i))
    (uf : forall x in s, { i | x in u i }.Finite) (us : s subseteq ⋃ i, u i) :
    exists v : ι -> Set X, s subseteq iUnion v ∧ (forall i, IsClosed (v i)) ∧ forall i, v i subseteq u i :=
  let ⟨v, hsv, _, hv⟩ := exists_subset_iUnion_closure_subset hs uo uf us
  ⟨fun i => closure (v i), Subset.trans hsv (iUnion_mono fun _ => subset_closure),
    fun _ => isClosed_closure, hv⟩

/--
theorem `exists_iUnion_eq_closure_subset` / 定理 `exists_iUnion_eq_closure_subset`

English:
theorem exists_iUnion_eq_closure_subset
  statement: (uo : forall i, IsOpen (u i)) (uf : forall x, { i | x in u i }.Finite)
  proof: let ⟨v, vU, hv⟩ := exists_subset_iUnion_closure_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

中文:
定理 存在_iUnion_eq_closure_subset
  结论: (uo : 对任意 i, 是开集 (u i)) (uf : 对任意 x, { i | x in u i }.有限)
  证明: let ⟨v, vU, hv⟩ := exists_subset_iUnion_closure_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

Depends on / 依赖: exists_subset_iUnion_closure_subset, isClosed_univ, uU.ge, univ_subset_iff
-/
theorem exists_iUnion_eq_closure_subset (uo : forall i, IsOpen (u i)) (uf : forall x, { i | x in u i }.Finite)
    (uU : ⋃ i, u i = univ) :
    exists v : ι -> Set X, iUnion v = univ ∧ (forall i, IsOpen (v i)) ∧ forall i, closure (v i) subseteq u i :=
  let ⟨v, vU, hv⟩ := exists_subset_iUnion_closure_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

/--
theorem `exists_iUnion_eq_closed_subset` / 定理 `exists_iUnion_eq_closed_subset`

English:
theorem exists_iUnion_eq_closed_subset
  statement: (uo : forall i, IsOpen (u i)) (uf : forall x, { i | x in u i }.Finite)
  proof: let ⟨v, vU, hv⟩ := exists_subset_iUnion_closed_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

中文:
定理 存在_iUnion_eq_closed_subset
  结论: (uo : 对任意 i, 是开集 (u i)) (uf : 对任意 x, { i | x in u i }.有限)
  证明: let ⟨v, vU, hv⟩ := exists_subset_iUnion_closed_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

Depends on / 依赖: exists_subset_iUnion_closed_subset, isClosed_univ, uU.ge, univ_subset_iff
-/
theorem exists_iUnion_eq_closed_subset (uo : forall i, IsOpen (u i)) (uf : forall x, { i | x in u i }.Finite)
    (uU : ⋃ i, u i = univ) :
    exists v : ι -> Set X, iUnion v = univ ∧ (forall i, IsClosed (v i)) ∧ forall i, v i subseteq u i :=
  let ⟨v, vU, hv⟩ := exists_subset_iUnion_closed_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

end NormalSpace

section T2LocallyCompactSpace

open ShrinkingLemma

variable {u : ι -> Set X} {s : Set X} [T2Space X] [LocallyCompactSpace X]

/--
theorem `exists_gt_t2space` / 定理 `exists_gt_t2space`

English:
theorem exists_gt_t2space
  statement: (v : PartialRefinement u s (fun w => IsCompact (closure w)))
  proof: by
  -- take `v i` such that `closure (v i)` is compact
  set si := s inter (⋃ j != i, v j)ᶜ with hsi
  simp only [ne_eq, compl_iUnion] at hsi
  have hsic : IsCompact si := by
    apply IsCompact.of_isClosed_subset hs _ Set.inter_subset_left
    · have : IsOpen (⋃ j != i, v j) := by
        apply isOpen_biUnion
        intro j _
        exact v.isOpen j
      exact IsClosed.inter (IsCompact.isClosed hs) (IsOpen.isClosed_compl this)
  have : si subseteq v i := by
    intro x hx
    have (j) (hj : j != i) : x ∉ v j := by
      rw [hsi] at hx
      apply Set.notMem_of_mem_compl
      have hsi' : x in (⋂ i_1, ⋂ (_ : ¬i_1 = i), (v.toFun i_1)ᶜ) := Set.mem_of_mem_inter_right hx
      rw [ne_eq] at hj
      rw [Set.mem_iInter₂] at hsi'
      exact hsi' j hj
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
      (v.subset_iUnion (Set.mem_of_mem_inter_left hx))
    obtain rfl : j = i := by
      by_contra! h
      exact this j h hj
    exact hj
  obtain ⟨vi, hvi⟩ := exists_open_between_and_isCompact_closure hsic (v.isOpen i) this
  classical
  refine ⟨⟨update v i vi, insert i v.carrier, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro j
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*, v.isOpen]
  · refine fun x hx => mem_iUnion.2 ?_
    by_cases! h : exists j != i, x in v j
    · rcases h with ⟨j, hji, hj⟩
      use j
      rwa [update_of_ne hji]
    · use i
      rw [update_self]
      apply hvi.2.1
      rw [hsi]
      exact ⟨hx, mem_iInter₂_of_mem h⟩
  · rintro j (rfl | hj)
    · rw [update_self]
exact subset_trans hvi.2.2.1 PartialRefinement.subset v j
    · rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
      exact v.closure_subset hj
  · intro j hj
    rw [mem_insert_iff] at hj
    by_cases h : j = i
    · rw [← h]
      simp only [update_self]
      exact hvi.2.2.2
    · apply hj.elim
      · intro hji
        exact False.elim (h hji)
      · intro hjmemv
        rw [update_of_ne h]
        exact v.pred_of_mem hjmemv
  · intro j hj
    rw [mem_insert_iff]; rw [not_or] at hj
    rw [update_of_ne hj.1]; rw [v.apply_eq hj.2]
  · refine ⟨subset_insert _ _, fun j hj => ?_⟩
    exact (update_of_ne (ne_of_mem_of_not_mem hj hi) _ _).symm
  · exact fun hle => hi (hle.1 <| mem_insert _ _)
  · simp only [update_self]
    exact hvi.2.2.2

中文:
定理 存在_gt_t2space
  结论: (v : PartialRefinement u s (fun w => 是紧集 (closure w)))
  证明: by
  -- take `v i` such that `closure (v i)` is compact
  set si := s inter (⋃ j != i, v j)ᶜ with hsi
  simp only [ne_eq, compl_iUnion] at hsi
  have hsic : IsCompact si := by
    apply IsCompact.of_isClosed_subset hs _ Set.inter_subset_left
    · have : IsOpen (⋃ j != i, v j) := by
        apply isOpen_biUnion
        intro j _
        exact v.isOpen j
      exact IsClosed.inter (IsCompact.isClosed hs) (IsOpen.isClosed_compl this)
  have : si subseteq v i := by
    intro x hx
    have (j) (hj : j != i) : x ∉ v j := by
      rw [hsi] at hx
      apply Set.notMem_of_mem_compl
      have hsi' : x in (⋂ i_1, ⋂ (_ : ¬i_1 = i), (v.toFun i_1)ᶜ) := Set.mem_of_mem_inter_right hx
      rw [ne_eq] at hj
      rw [Set.mem_iInter₂] at hsi'
      exact hsi' j hj
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
      (v.subset_iUnion (Set.mem_of_mem_inter_left hx))
    obtain rfl : j = i := by
      by_contra! h
      exact this j h hj
    exact hj
  obtain ⟨vi, hvi⟩ := exists_open_between_and_isCompact_closure hsic (v.isOpen i) this
  classical
  refine ⟨⟨update v i vi, insert i v.carrier, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro j
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*, v.isOpen]
  · refine fun x hx => mem_iUnion.2 ?_
    by_cases! h : exists j != i, x in v j
    · rcases h with ⟨j, hji, hj⟩
      use j
      rwa [update_of_ne hji]
    · use i
      rw [update_self]
      apply hvi.2.1
      rw [hsi]
      exact ⟨hx, mem_iInter₂_of_mem h⟩
  · rintro j (rfl | hj)
    · rw [update_self]
exact subset_trans hvi.2.2.1 PartialRefinement.subset v j
    · rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
      exact v.closure_subset hj
  · intro j hj
    rw [mem_insert_iff] at hj
    by_cases h : j = i
    · rw [← h]
      simp only [update_self]
      exact hvi.2.2.2
    · apply hj.elim
      · intro hji
        exact False.elim (h hji)
      · intro hjmemv
        rw [update_of_ne h]
        exact v.pred_of_mem hjmemv
  · intro j hj
    rw [mem_insert_iff]; rw [not_or] at hj
    rw [update_of_ne hj.1]; rw [v.apply_eq hj.2]
  · refine ⟨subset_insert _ _, fun j hj => ?_⟩
    exact (update_of_ne (ne_of_mem_of_not_mem hj hi) _ _).symm
  · exact fun hle => hi (hle.1 <| mem_insert _ _)
  · simp only [update_self]
    exact hvi.2.2.2
-/
theorem exists_gt_t2space (v : PartialRefinement u s (fun w => IsCompact (closure w)))
    (hs : IsCompact s) (i : ι) (hi : i ∉ v.carrier) :
    exists v' : PartialRefinement u s (fun w => IsCompact (closure w)),
      v < v' ∧ IsCompact (closure (v' i)) := by
  -- take `v i` such that `closure (v i)` is compact
  set si := s inter (⋃ j != i, v j)ᶜ with hsi
  simp only [ne_eq, compl_iUnion] at hsi
  have hsic : IsCompact si := by
    apply IsCompact.of_isClosed_subset hs _ Set.inter_subset_left
    · have : IsOpen (⋃ j != i, v j) := by
        apply isOpen_biUnion
        intro j _
        exact v.isOpen j
      exact IsClosed.inter (IsCompact.isClosed hs) (IsOpen.isClosed_compl this)
  have : si subseteq v i := by
    intro x hx
    have (j) (hj : j != i) : x ∉ v j := by
      rw [hsi] at hx
      apply Set.notMem_of_mem_compl
      have hsi' : x in (⋂ i_1, ⋂ (_ : ¬i_1 = i), (v.toFun i_1)ᶜ) := Set.mem_of_mem_inter_right hx
      rw [ne_eq] at hj
      rw [Set.mem_iInter₂] at hsi'
      exact hsi' j hj
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
      (v.subset_iUnion (Set.mem_of_mem_inter_left hx))
    obtain rfl : j = i := by
      by_contra! h
      exact this j h hj
    exact hj
  obtain ⟨vi, hvi⟩ := exists_open_between_and_isCompact_closure hsic (v.isOpen i) this
  classical
  refine ⟨⟨update v i vi, insert i v.carrier, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro j
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*, v.isOpen]
  · refine fun x hx => mem_iUnion.2 ?_
    by_cases! h : exists j != i, x in v j
    · rcases h with ⟨j, hji, hj⟩
      use j
      rwa [update_of_ne hji]
    · use i
      rw [update_self]
      apply hvi.2.1
      rw [hsi]
      exact ⟨hx, mem_iInter₂_of_mem h⟩
  · rintro j (rfl | hj)
    · rw [update_self]
exact subset_trans hvi.2.2.1 PartialRefinement.subset v j
    · rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
      exact v.closure_subset hj
  · intro j hj
    rw [mem_insert_iff] at hj
    by_cases h : j = i
    · rw [← h]
      simp only [update_self]
      exact hvi.2.2.2
    · apply hj.elim
      · intro hji
        exact False.elim (h hji)
      · intro hjmemv
        rw [update_of_ne h]
        exact v.pred_of_mem hjmemv
  · intro j hj
    rw [mem_insert_iff]; rw [not_or] at hj
    rw [update_of_ne hj.1]; rw [v.apply_eq hj.2]
  · refine ⟨subset_insert _ _, fun j hj => ?_⟩
    exact (update_of_ne (ne_of_mem_of_not_mem hj hi) _ _).symm
  · exact fun hle => hi (hle.1 <| mem_insert _ _)
  · simp only [update_self]
    exact hvi.2.2.2

/--
theorem `exists_subset_iUnion_closure_subset_t2space` / 定理 `exists_subset_iUnion_closure_subset_t2space`

English:
theorem exists_subset_iUnion_closure_subset_t2space
  statement: (hs : IsCompact s) (uo : forall i, IsOpen (u i))
  proof: by
  have : Nonempty (PartialRefinement u s (fun w => IsCompact (closure w))) :=
    ⟨⟨u, ∅, uo, us, False.elim, False.elim, fun _ => rfl⟩⟩
  have : forall c : Set (PartialRefinement u s (fun w => IsCompact (closure w))),
      IsChain (· <= ·) c -> c.Nonempty -> exists ub, forall v in c, v <= ub :=
    fun c hc ne => ⟨.chainSup c hc ne uf us, fun v hv => PartialRefinement.le_chainSup _ _ _ _ hv⟩
  rcases zorn_le_nonempty this with ⟨v, hv⟩
  suffices forall i, i in v.carrier from
    ⟨v, v.subset_iUnion, fun i => v.isOpen _, fun i => v.closure_subset (this i), ?_⟩
  · intro i
    exact v.pred_of_mem (this i)
  · intro i
    by_contra! hi
    rcases exists_gt_t2space v hs i hi with ⟨v', hlt, _⟩
    exact hv.not_lt hlt

中文:
定理 存在_subset_iUnion_closure_subset_t2space
  结论: (hs : 是紧集 s) (uo : 对任意 i, 是开集 (u i))
  证明: by
  have : Nonempty (PartialRefinement u s (fun w => IsCompact (closure w))) :=
    ⟨⟨u, ∅, uo, us, False.elim, False.elim, fun _ => rfl⟩⟩
  have : forall c : Set (PartialRefinement u s (fun w => IsCompact (closure w))),
      IsChain (· <= ·) c -> c.Nonempty -> exists ub, forall v in c, v <= ub :=
    fun c hc ne => ⟨.chainSup c hc ne uf us, fun v hv => PartialRefinement.le_chainSup _ _ _ _ hv⟩
  rcases zorn_le_nonempty this with ⟨v, hv⟩
  suffices forall i, i in v.carrier from
    ⟨v, v.subset_iUnion, fun i => v.isOpen _, fun i => v.closure_subset (this i), ?_⟩
  · intro i
    exact v.pred_of_mem (this i)
  · intro i
    by_contra! hi
    rcases exists_gt_t2space v hs i hi with ⟨v', hlt, _⟩
    exact hv.not_lt hlt

Depends on / 依赖: False.elim, IsChain, IsCompact, Nonempty, PartialRefinement, PartialRefinement.le_chainSup, c.Nonempty, carrier, chainSup, closure, le_chainSup, subset_iUnion, v.carrier, v.isOpe, v.subset_iUnion, zorn_le_nonempty
-/
theorem exists_subset_iUnion_closure_subset_t2space (hs : IsCompact s) (uo : forall i, IsOpen (u i))
    (uf : forall x in s, { i | x in u i }.Finite) (us : s subseteq ⋃ i, u i) :
    exists v : ι -> Set X, s subseteq iUnion v ∧ (forall i, IsOpen (v i)) ∧ (forall i, closure (v i) subseteq u i)
      ∧ (forall i, IsCompact (closure (v i))) := by
  have : Nonempty (PartialRefinement u s (fun w => IsCompact (closure w))) :=
    ⟨⟨u, ∅, uo, us, False.elim, False.elim, fun _ => rfl⟩⟩
  have : forall c : Set (PartialRefinement u s (fun w => IsCompact (closure w))),
      IsChain (· <= ·) c -> c.Nonempty -> exists ub, forall v in c, v <= ub :=
    fun c hc ne => ⟨.chainSup c hc ne uf us, fun v hv => PartialRefinement.le_chainSup _ _ _ _ hv⟩
  rcases zorn_le_nonempty this with ⟨v, hv⟩
  suffices forall i, i in v.carrier from
    ⟨v, v.subset_iUnion, fun i => v.isOpen _, fun i => v.closure_subset (this i), ?_⟩
  · intro i
    exact v.pred_of_mem (this i)
  · intro i
    by_contra! hi
    rcases exists_gt_t2space v hs i hi with ⟨v', hlt, _⟩
    exact hv.not_lt hlt

/--
theorem `exists_subset_iUnion_compact_subset_t2space` / 定理 `exists_subset_iUnion_compact_subset_t2space`

English:
theorem exists_subset_iUnion_compact_subset_t2space
  statement: (hs : IsCompact s) (uo : forall i, IsOpen (u i))
  proof: by
  let ⟨v, hsv, _, hv⟩ := exists_subset_iUnion_closure_subset_t2space hs uo uf us
  use fun i => closure (v i)
  refine ⟨?_, ?_, hv⟩
  · exact Subset.trans hsv (iUnion_mono fun _ => subset_closure)
  · simp only [isClosed_closure, implies_true]

中文:
定理 存在_subset_iUnion_compact_subset_t2space
  结论: (hs : 是紧集 s) (uo : 对任意 i, 是开集 (u i))
  证明: by
  let ⟨v, hsv, _, hv⟩ := exists_subset_iUnion_closure_subset_t2space hs uo uf us
  use fun i => closure (v i)
  refine ⟨?_, ?_, hv⟩
  · exact Subset.trans hsv (iUnion_mono fun _ => subset_closure)
  · simp only [isClosed_closure, implies_true]

Depends on / 依赖: Subset, Subset.trans, closure, exists_subset_iUnion_closure_subset_t2space, iUnion_mono, implies_true, isClosed_closure, subset_closure
-/
theorem exists_subset_iUnion_compact_subset_t2space (hs : IsCompact s) (uo : forall i, IsOpen (u i))
    (uf : forall x in s, { i | x in u i }.Finite) (us : s subseteq ⋃ i, u i) :
    exists v : ι -> Set X, s subseteq iUnion v ∧ (forall i, IsClosed (v i)) ∧ (forall i, v i subseteq u i)
      ∧ forall i, IsCompact (v i) := by
  let ⟨v, hsv, _, hv⟩ := exists_subset_iUnion_closure_subset_t2space hs uo uf us
  use fun i => closure (v i)
  refine ⟨?_, ?_, hv⟩
  · exact Subset.trans hsv (iUnion_mono fun _ => subset_closure)
  · simp only [isClosed_closure, implies_true]

end T2LocallyCompactSpace
