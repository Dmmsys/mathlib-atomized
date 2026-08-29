/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Data.PFun

/-!
# `Tendsto` for relations and partial functions

This file generalizes `Filter` definitions from functions to partial functions and relations.

## Considering functions and partial functions as relations

A function `f : α → β` can be considered as the relation `Rel α β` which relates `x` and `f x` for
all `x`, and nothing else. This relation is called `Function.Graph f`.

A partial function `f : α →. β` can be considered as the relation `Rel α β` which relates `x` and
`f x` for all `x` for which `f x` exists, and nothing else. This relation is called
`PFun.Graph' f`.

In this regard, a function is a relation for which every element in `α` is related to exactly one
element in `β` and a partial function is a relation for which every element in `α` is related to at
most one element in `β`.

This file leverages this analogy to generalize `Filter` definitions from functions to partial
functions and relations.

## Notes

`Set.preimage` can be generalized to relations in two ways:
* `Rel.preimage` returns the image of the set under the inverse relation.
* `Rel.core` returns the set of elements that are only related to those in the set.

Both generalizations are sensible in the context of filters, so `Filter.comap` and `Filter.Tendsto`
get two generalizations each.

We first take care of relations. Then the definitions for partial functions are taken as special
cases of the definitions for relations.
-/

@[expose] public section


universe u v w

namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w}

open Filter

/-! ### Relations -/


/--
Definition of `rmap` / `rmap` 的定义

English:
definition rmap
  signature: (r : SetRel α β) (l : Filter α)
  body: { s | r.core s in l }
  univ_sets := by simp
  sets_of_superset hs st := mem_of_superset hs (SetRel.core_mono st)
  inter_sets hs ht := by
    simp only [Set.mem_ofPred_eq]
    convert! inter_mem hs ht
    rw [← SetRel.core_inter]

中文:
定义 rmap
  签名: (r : SetRel α β) (l : 滤子 α)
  定义体: { s | r.core s in l }
  univ_sets := by simp
  sets_of_superset hs st := mem_of_superset hs (SetRel.core_mono st)
  inter_sets hs ht := by
    simp only [Set.mem_ofPred_eq]
    convert! inter_mem hs ht
    rw [← SetRel.core_inter]

Depends on / 依赖: r.core
-/
def rmap (r : SetRel α β) (l : Filter α) : Filter β where
  sets := { s | r.core s in l }
  univ_sets := by simp
  sets_of_superset hs st := mem_of_superset hs (SetRel.core_mono st)
  inter_sets hs ht := by
    simp only [Set.mem_ofPred_eq]
    convert! inter_mem hs ht
    rw [← SetRel.core_inter]

/--
theorem `rmap_sets` / 定理 `rmap_sets`

English:
theorem rmap_sets
  given: (r : SetRel α β) (l : Filter α)
  statement: (l.rmap r).sets = r.core ⁻¹' l.sets
  proof: rfl

@[simp]

中文:
定理 rmap_sets
  条件: (r : SetRel α β) (l : 滤子 α)
  结论: (l.rmap r).sets = r.core ⁻¹' l.sets
  证明: rfl

@[simp]
-/
theorem rmap_sets (r : SetRel α β) (l : Filter α) : (l.rmap r).sets = r.core ⁻¹' l.sets :=
  rfl

@[simp]
/--
theorem `mem_rmap` / 定理 `mem_rmap`

English:
theorem mem_rmap
  given: (r : SetRel α β) (l : Filter α) (s : Set β)
  statement: s in l.rmap r ↔ r.core s in l
  proof: Iff.rfl

@[simp]

中文:
定理 mem_rmap
  条件: (r : SetRel α β) (l : 滤子 α) (s : 集合 β)
  结论: s in l.rmap r ↔ r.core s in l
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_rmap (r : SetRel α β) (l : Filter α) (s : Set β) : s in l.rmap r ↔ r.core s in l :=
  Iff.rfl

@[simp]
/--
theorem `rmap_rmap` / 定理 `rmap_rmap`

English:
theorem rmap_rmap
  given: (r : SetRel α β) (s : SetRel β γ) (l : Filter α)
  proof: filter_eq by simp [rmap_sets, Set.preimage, SetRel.core_comp]

@[simp]

中文:
定理 rmap_rmap
  条件: (r : SetRel α β) (s : SetRel β γ) (l : 滤子 α)
  证明: filter_eq by simp [rmap_sets, Set.preimage, SetRel.core_comp]

@[simp]

Depends on / 依赖: Set.preimage, SetRel, SetRel.core_comp, core_comp, filter_eq, preimage, rmap_sets
-/
theorem rmap_rmap (r : SetRel α β) (s : SetRel β γ) (l : Filter α) :
    rmap s (rmap r l) = rmap (r.comp s) l :=
filter_eq by simp [rmap_sets, Set.preimage, SetRel.core_comp]

@[simp]
/--
theorem `rmap_compose` / 定理 `rmap_compose`

English:
theorem rmap_compose
  given: (r : SetRel α β) (s : SetRel β γ)
  statement: rmap s ∘ rmap r = rmap (r.comp s)
  proof: funext rmap_rmap _ _

中文:
定理 rmap_compose
  条件: (r : SetRel α β) (s : SetRel β γ)
  结论: rmap s ∘ rmap r = rmap (r.comp s)
  证明: funext rmap_rmap _ _

Depends on / 依赖: rmap_rmap
-/
theorem rmap_compose (r : SetRel α β) (s : SetRel β γ) : rmap s ∘ rmap r = rmap (r.comp s) :=
funext rmap_rmap _ _

/--
Definition of `RTendsto` / `RTendsto` 的定义

English:
definition RTendsto
  signature: (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β)
  body: l₁.rmap r <= l₂

中文:
定义 RTendsto
  签名: (r : SetRel α β) (l₁ : 滤子 α) (l₂ : 滤子 β)
  定义体: l₁.rmap r <= l₂

Depends on / 依赖: e.symm
-/
def RTendsto (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.rmap r <= l₂

/--
theorem `rtendsto_def` / 定理 `rtendsto_def`

English:
theorem rtendsto_def
  given: (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β)
  proof: Iff.rfl

中文:
定理 rtendsto_def
  条件: (r : SetRel α β) (l₁ : 滤子 α) (l₂ : 滤子 β)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem rtendsto_def (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :
    RTendsto r l₁ l₂ ↔ forall s in l₂, r.core s in l₁ :=
  Iff.rfl

/--
Definition of `rcomap` / `rcomap` 的定义

English:
definition rcomap
  signature: (r : SetRel α β) (f : Filter β)
  body: SetRel.image {(s, t) : _ × _ | r.core s subseteq t} f.sets
  univ_sets := ⟨Set.univ, univ_mem, Set.subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' inter b', inter_mem ha₁ hb₁, (r.core_inter a' b').subset.trans (Set.inter_subset_inter ha₂ hb₂)⟩

中文:
定义 rcomap
  签名: (r : SetRel α β) (f : 滤子 β)
  定义体: SetRel.image {(s, t) : _ × _ | r.core s subseteq t} f.sets
  univ_sets := ⟨Set.univ, univ_mem, Set.subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' inter b', inter_mem ha₁ hb₁, (r.core_inter a' b').subset.trans (Set.inter_subset_inter ha₂ hb₂)⟩

Depends on / 依赖: SetRel, SetRel.image, f.sets, r.core, subseteq
-/
def rcomap (r : SetRel α β) (f : Filter β) : Filter α where
  sets := SetRel.image {(s, t) : _ × _ | r.core s subseteq t} f.sets
  univ_sets := ⟨Set.univ, univ_mem, Set.subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' inter b', inter_mem ha₁ hb₁, (r.core_inter a' b').subset.trans (Set.inter_subset_inter ha₂ hb₂)⟩

/--
theorem `rcomap_sets` / 定理 `rcomap_sets`

English:
theorem rcomap_sets
  given: (r : SetRel α β) (f : Filter β)
  proof: rfl

中文:
定理 rcomap_sets
  条件: (r : SetRel α β) (f : 滤子 β)
  证明: rfl
-/
theorem rcomap_sets (r : SetRel α β) (f : Filter β) :
    (rcomap r f).sets = SetRel.image {(s, t) : _ × _ | r.core s subseteq t} f.sets :=
  rfl

/--
theorem `rcomap_rcomap` / 定理 `rcomap_rcomap`

English:
theorem rcomap_rcomap
  given: (r : SetRel α β) (s : SetRel β γ) (l : Filter γ)
  proof: filter_eq by
    ext t
    simp only [rcomap_sets, SetRel.image, Filter.mem_sets, Set.mem_ofPred_eq, SetRel.core_comp]
    constructor
    · rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
      exact ⟨v, vsets, Set.Subset.trans (SetRel.core_mono hv) h⟩
    rintro ⟨t, tsets, ht⟩
    exact ⟨SetRel.core s t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩

@[simp]

中文:
定理 rcomap_rcomap
  条件: (r : SetRel α β) (s : SetRel β γ) (l : 滤子 γ)
  证明: filter_eq by
    ext t
    simp only [rcomap_sets, SetRel.image, Filter.mem_sets, Set.mem_ofPred_eq, SetRel.core_comp]
    constructor
    · rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
      exact ⟨v, vsets, Set.Subset.trans (SetRel.core_mono hv) h⟩
    rintro ⟨t, tsets, ht⟩
    exact ⟨SetRel.core s t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩

@[simp]

Depends on / 依赖: Filter, Filter.mem_sets, Set.Subset.rfl, Set.Subset.trans, Set.mem_ofPred_eq, SetRel, SetRel.core, SetRel.core_comp, SetRel.core_mono, SetRel.image, Subset, core_comp, core_mono, filter_eq, mem_ofPred_eq, mem_sets, rcomap_sets
-/
theorem rcomap_rcomap (r : SetRel α β) (s : SetRel β γ) (l : Filter γ) :
    rcomap r (rcomap s l) = rcomap (r.comp s) l :=
filter_eq by
    ext t
    simp only [rcomap_sets, SetRel.image, Filter.mem_sets, Set.mem_ofPred_eq, SetRel.core_comp]
    constructor
    · rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
      exact ⟨v, vsets, Set.Subset.trans (SetRel.core_mono hv) h⟩
    rintro ⟨t, tsets, ht⟩
    exact ⟨SetRel.core s t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩

@[simp]
/--
theorem `rcomap_compose` / 定理 `rcomap_compose`

English:
theorem rcomap_compose
  given: (r : SetRel α β) (s : SetRel β γ)
  proof: funext rcomap_rcomap _ _

中文:
定理 rcomap_compose
  条件: (r : SetRel α β) (s : SetRel β γ)
  证明: funext rcomap_rcomap _ _

Depends on / 依赖: rcomap_rcomap
-/
theorem rcomap_compose (r : SetRel α β) (s : SetRel β γ) :
    rcomap r ∘ rcomap s = rcomap (r.comp s) :=
funext rcomap_rcomap _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `rtendsto_iff_le_rcomap` / 定理 `rtendsto_iff_le_rcomap`

English:
theorem rtendsto_iff_le_rcomap
  given: (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β)
  proof: by
  rw [rtendsto_def]
  simp_rw [← l₂.mem_sets]
  constructor
  · simpa [Filter.le_def, rcomap, SetRel.mem_image]
      using fun h s t tl₂ => mem_of_superset (h t tl₂)
  · simpa [Filter.le_def, rcomap, SetRel.mem_image]
      using fun h t tl₂ => h _ t tl₂ Set.Subset.rfl

中文:
定理 rtendsto_iff_le_rcomap
  条件: (r : SetRel α β) (l₁ : 滤子 α) (l₂ : 滤子 β)
  证明: by
  rw [rtendsto_def]
  simp_rw [← l₂.mem_sets]
  constructor
  · simpa [Filter.le_def, rcomap, SetRel.mem_image]
      using fun h s t tl₂ => mem_of_superset (h t tl₂)
  · simpa [Filter.le_def, rcomap, SetRel.mem_image]
      using fun h t tl₂ => h _ t tl₂ Set.Subset.rfl

Depends on / 依赖: Filter, Filter.le_def, Set.Subset.rfl, SetRel, SetRel.mem_image, Subset, le_def, mem_image, mem_of_superset, mem_sets, rcomap, rtendsto_def, simp_rw
-/
theorem rtendsto_iff_le_rcomap (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :
    RTendsto r l₁ l₂ ↔ l₁ <= l₂.rcomap r := by
  rw [rtendsto_def]
  simp_rw [← l₂.mem_sets]
  constructor
  · simpa [Filter.le_def, rcomap, SetRel.mem_image]
      using fun h s t tl₂ => mem_of_superset (h t tl₂)
  · simpa [Filter.le_def, rcomap, SetRel.mem_image]
      using fun h t tl₂ => h _ t tl₂ Set.Subset.rfl

-- Interestingly, there does not seem to be a way to express this relation using a forward map.
-- Given a filter `f` on `α`, we want a filter `f'` on `β` such that `r.preimage s ∈ f` if
-- and only if `s ∈ f'`. But the intersection of two sets satisfying the lhs may be empty.
/--
Definition of `rcomap'` / `rcomap'` 的定义

English:
definition rcomap'
  signature: (r : SetRel α β) (f : Filter β)
  body: SetRel.image {(s, t) : _ × _ | r.preimage s subseteq t} f.sets
  univ_sets := ⟨Set.univ, univ_mem, Set.subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' inter b', inter_mem ha₁ hb₁, r.preimage_inter_subset.trans (Set.inter_subset_inter ha₂ hb₂)⟩

@[simp]

中文:
定义 rcomap'
  签名: (r : SetRel α β) (f : 滤子 β)
  定义体: SetRel.image {(s, t) : _ × _ | r.preimage s subseteq t} f.sets
  univ_sets := ⟨Set.univ, univ_mem, Set.subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' inter b', inter_mem ha₁ hb₁, r.preimage_inter_subset.trans (Set.inter_subset_inter ha₂ hb₂)⟩

@[simp]

Depends on / 依赖: SetRel, SetRel.image, f.sets, preimage, r.preimage, subseteq
-/
def rcomap' (r : SetRel α β) (f : Filter β) : Filter α where
  sets := SetRel.image {(s, t) : _ × _ | r.preimage s subseteq t} f.sets
  univ_sets := ⟨Set.univ, univ_mem, Set.subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' inter b', inter_mem ha₁ hb₁, r.preimage_inter_subset.trans (Set.inter_subset_inter ha₂ hb₂)⟩

@[simp]
/--
theorem `mem_rcomap'` / 定理 `mem_rcomap'`

English:
theorem mem_rcomap'
  given: (r : SetRel α β) (l : Filter β) (s : Set α)
  proof: Iff.rfl

中文:
定理 mem_rcomap'
  条件: (r : SetRel α β) (l : 滤子 β) (s : 集合 α)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_rcomap' (r : SetRel α β) (l : Filter β) (s : Set α) :
    s in l.rcomap' r ↔ exists t in l, r.preimage t subseteq s :=
  Iff.rfl

/--
theorem `rcomap'_sets` / 定理 `rcomap'_sets`

English:
theorem rcomap'_sets
  given: (r : SetRel α β) (f : Filter β)
  proof: rfl

@[simp]

中文:
定理 rcomap'_sets
  条件: (r : SetRel α β) (f : 滤子 β)
  证明: rfl

@[simp]
-/
theorem rcomap'_sets (r : SetRel α β) (f : Filter β) :
    (rcomap' r f).sets = SetRel.image {(s, t) | r.preimage s subseteq t} f.sets :=
  rfl

@[simp]
/--
theorem `rcomap'_rcomap'` / 定理 `rcomap'_rcomap'`

English:
theorem rcomap'_rcomap'
  given: (r : SetRel α β) (s : SetRel β γ) (l : Filter γ)
  proof: Filter.ext fun t => by
    simp only [mem_rcomap', SetRel.preimage_comp]
    constructor
    · rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
      exact ⟨v, vsets, (SetRel.preimage_mono hv).trans h⟩
    rintro ⟨t, tsets, ht⟩
    exact ⟨s.preimage t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩

@[simp]

中文:
定理 rcomap'_rcomap'
  条件: (r : SetRel α β) (s : SetRel β γ) (l : 滤子 γ)
  证明: Filter.ext fun t => by
    simp only [mem_rcomap', SetRel.preimage_comp]
    constructor
    · rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
      exact ⟨v, vsets, (SetRel.preimage_mono hv).trans h⟩
    rintro ⟨t, tsets, ht⟩
    exact ⟨s.preimage t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩

@[simp]
-/
theorem rcomap'_rcomap' (r : SetRel α β) (s : SetRel β γ) (l : Filter γ) :
    rcomap' r (rcomap' s l) = rcomap' (r.comp s) l :=
  Filter.ext fun t => by
    simp only [mem_rcomap', SetRel.preimage_comp]
    constructor
    · rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
      exact ⟨v, vsets, (SetRel.preimage_mono hv).trans h⟩
    rintro ⟨t, tsets, ht⟩
    exact ⟨s.preimage t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩

@[simp]
/--
theorem `rcomap'_compose` / 定理 `rcomap'_compose`

English:
theorem rcomap'_compose
  given: (r : SetRel α β) (s : SetRel β γ)
  proof: funext rcomap'_rcomap' _ _

中文:
定理 rcomap'_compose
  条件: (r : SetRel α β) (s : SetRel β γ)
  证明: funext rcomap'_rcomap' _ _
-/
theorem rcomap'_compose (r : SetRel α β) (s : SetRel β γ) :
    rcomap' r ∘ rcomap' s = rcomap' (r.comp s) :=
funext rcomap'_rcomap' _ _

/--
Definition of `RTendsto'` / `RTendsto'` 的定义

English:
definition RTendsto'
  signature: (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β)
  body: l₁ <= l₂.rcomap' r

中文:
定义 RTendsto'
  签名: (r : SetRel α β) (l₁ : 滤子 α) (l₂ : 滤子 β)
  定义体: l₁ <= l₂.rcomap' r

Depends on / 依赖: rcomap
-/
def RTendsto' (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁ <= l₂.rcomap' r

set_option backward.isDefEq.respectTransparency false in
/--
theorem `rtendsto'_def` / 定理 `rtendsto'_def`

English:
theorem rtendsto'_def
  given: (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β)
  proof: by
  unfold RTendsto' rcomap'; constructor
  · simpa [le_def, SetRel.mem_image] using fun h s hs => h _ _ hs Set.Subset.rfl
  · simpa [le_def, SetRel.mem_image] using fun h s t ht => mem_of_superset (h t ht)

中文:
定理 rtendsto'_def
  条件: (r : SetRel α β) (l₁ : 滤子 α) (l₂ : 滤子 β)
  证明: by
  unfold RTendsto' rcomap'; constructor
  · simpa [le_def, SetRel.mem_image] using fun h s hs => h _ _ hs Set.Subset.rfl
  · simpa [le_def, SetRel.mem_image] using fun h s t ht => mem_of_superset (h t ht)

Depends on / 依赖: RTendsto, Set.Subset.rfl, SetRel, SetRel.mem_image, Subset, le_def, mem_image, mem_of_superset, rcomap
-/
theorem rtendsto'_def (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :
    RTendsto' r l₁ l₂ ↔ forall s in l₂, r.preimage s in l₁ := by
  unfold RTendsto' rcomap'; constructor
  · simpa [le_def, SetRel.mem_image] using fun h s hs => h _ _ hs Set.Subset.rfl
  · simpa [le_def, SetRel.mem_image] using fun h s t ht => mem_of_superset (h t ht)

/--
theorem `tendsto_iff_rtendsto` / 定理 `tendsto_iff_rtendsto`

English:
theorem tendsto_iff_rtendsto
  given: (l₁ : Filter α) (l₂ : Filter β) (f : α -> β)
  proof: by
  simp [tendsto_def, Function.graph, rtendsto_def, SetRel.core, Set.preimage]

中文:
定理 tendsto_iff_rtendsto
  条件: (l₁ : 滤子 α) (l₂ : 滤子 β) (f : α -> β)
  证明: by
  simp [tendsto_def, Function.graph, rtendsto_def, SetRel.core, Set.preimage]

Depends on / 依赖: Function, Function.graph, Set.preimage, SetRel, SetRel.core, preimage, rtendsto_def, tendsto_def
-/
theorem tendsto_iff_rtendsto (l₁ : Filter α) (l₂ : Filter β) (f : α -> β) :
    Tendsto f l₁ l₂ ↔ RTendsto (Function.graph f) l₁ l₂ := by
  simp [tendsto_def, Function.graph, rtendsto_def, SetRel.core, Set.preimage]

/--
theorem `tendsto_iff_rtendsto'` / 定理 `tendsto_iff_rtendsto'`

English:
theorem tendsto_iff_rtendsto'
  given: (l₁ : Filter α) (l₂ : Filter β) (f : α -> β)
  proof: by
  simp [tendsto_def, Function.graph, rtendsto'_def, SetRel.preimage, Set.preimage]

中文:
定理 tendsto_iff_rtendsto'
  条件: (l₁ : 滤子 α) (l₂ : 滤子 β) (f : α -> β)
  证明: by
  simp [tendsto_def, Function.graph, rtendsto'_def, SetRel.preimage, Set.preimage]

Depends on / 依赖: Function, Function.graph, Set.preimage, SetRel, SetRel.preimage, _def, preimage, rtendsto, tendsto_def
-/
theorem tendsto_iff_rtendsto' (l₁ : Filter α) (l₂ : Filter β) (f : α -> β) :
    Tendsto f l₁ l₂ ↔ RTendsto' (Function.graph f) l₁ l₂ := by
  simp [tendsto_def, Function.graph, rtendsto'_def, SetRel.preimage, Set.preimage]

/-! ### Partial functions -/


/--
Definition of `pmap` / `pmap` 的定义

English:
definition pmap
  signature: (f : α ->. β) (l : Filter α)
  body: Filter.rmap f.graph' l

@[simp]

中文:
定义 pmap
  签名: (f : α ->. β) (l : 滤子 α)
  定义体: Filter.rmap f.graph' l

@[simp]

Depends on / 依赖: Filter, Filter.rmap, f.graph
-/
def pmap (f : α ->. β) (l : Filter α) : Filter β :=
  Filter.rmap f.graph' l

@[simp]
/--
theorem `mem_pmap` / 定理 `mem_pmap`

English:
theorem mem_pmap
  given: (f : α ->. β) (l : Filter α) (s : Set β)
  statement: s in l.pmap f ↔ f.core s in l
  proof: Iff.rfl

中文:
定理 mem_pmap
  条件: (f : α ->. β) (l : 滤子 α) (s : 集合 β)
  结论: s in l.pmap f ↔ f.core s in l
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_pmap (f : α ->. β) (l : Filter α) (s : Set β) : s in l.pmap f ↔ f.core s in l :=
  Iff.rfl

/--
Definition of `PTendsto` / `PTendsto` 的定义

English:
definition PTendsto
  signature: (f : α ->. β) (l₁ : Filter α) (l₂ : Filter β)
  body: l₁.pmap f <= l₂

中文:
定义 PTendsto
  签名: (f : α ->. β) (l₁ : 滤子 α) (l₂ : 滤子 β)
  定义体: l₁.pmap f <= l₂
-/
def PTendsto (f : α ->. β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.pmap f <= l₂

/--
theorem `ptendsto_def` / 定理 `ptendsto_def`

English:
theorem ptendsto_def
  given: (f : α ->. β) (l₁ : Filter α) (l₂ : Filter β)
  proof: Iff.rfl

中文:
定理 ptendsto_def
  条件: (f : α ->. β) (l₁ : 滤子 α) (l₂ : 滤子 β)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ptendsto_def (f : α ->. β) (l₁ : Filter α) (l₂ : Filter β) :
    PTendsto f l₁ l₂ ↔ forall s in l₂, f.core s in l₁ :=
  Iff.rfl

/--
theorem `ptendsto_iff_rtendsto` / 定理 `ptendsto_iff_rtendsto`

English:
theorem ptendsto_iff_rtendsto
  given: (l₁ : Filter α) (l₂ : Filter β) (f : α ->. β)
  proof: Iff.rfl

中文:
定理 ptendsto_iff_rtendsto
  条件: (l₁ : 滤子 α) (l₂ : 滤子 β) (f : α ->. β)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ptendsto_iff_rtendsto (l₁ : Filter α) (l₂ : Filter β) (f : α ->. β) :
    PTendsto f l₁ l₂ ↔ RTendsto f.graph' l₁ l₂ :=
  Iff.rfl

/--
theorem `pmap_res` / 定理 `pmap_res`

English:
theorem pmap_res
  given: (l : Filter α) (s : Set α) (f : α -> β)
  proof: by
  ext t
  simp only [PFun.core_res, mem_pmap, mem_map, mem_inf_principal, imp_iff_not_or]
  rfl

中文:
定理 pmap_res
  条件: (l : 滤子 α) (s : 集合 α) (f : α -> β)
  证明: by
  ext t
  simp only [PFun.core_res, mem_pmap, mem_map, mem_inf_principal, imp_iff_not_or]
  rfl

Depends on / 依赖: PFun.core_res, core_res, imp_iff_not_or, mem_inf_principal, mem_map, mem_pmap
-/
theorem pmap_res (l : Filter α) (s : Set α) (f : α -> β) :
    pmap (PFun.res f s) l = map f (l ⊓ 𝓟 s) := by
  ext t
  simp only [PFun.core_res, mem_pmap, mem_map, mem_inf_principal, imp_iff_not_or]
  rfl

/--
theorem `tendsto_iff_ptendsto` / 定理 `tendsto_iff_ptendsto`

English:
theorem tendsto_iff_ptendsto
  given: (l₁ : Filter α) (l₂ : Filter β) (s : Set α) (f : α -> β)
  proof: by
  simp only [Tendsto, PTendsto, pmap_res]

中文:
定理 tendsto_iff_ptendsto
  条件: (l₁ : 滤子 α) (l₂ : 滤子 β) (s : 集合 α) (f : α -> β)
  证明: by
  simp only [Tendsto, PTendsto, pmap_res]

Depends on / 依赖: PTendsto, Tendsto, pmap_res
-/
theorem tendsto_iff_ptendsto (l₁ : Filter α) (l₂ : Filter β) (s : Set α) (f : α -> β) :
    Tendsto f (l₁ ⊓ 𝓟 s) l₂ ↔ PTendsto (PFun.res f s) l₁ l₂ := by
  simp only [Tendsto, PTendsto, pmap_res]

/--
theorem `tendsto_iff_ptendsto_univ` / 定理 `tendsto_iff_ptendsto_univ`

English:
theorem tendsto_iff_ptendsto_univ
  given: (l₁ : Filter α) (l₂ : Filter β) (f : α -> β)
  proof: by
  rw [← tendsto_iff_ptendsto]
  simp [principal_univ]

中文:
定理 tendsto_iff_ptendsto_univ
  条件: (l₁ : 滤子 α) (l₂ : 滤子 β) (f : α -> β)
  证明: by
  rw [← tendsto_iff_ptendsto]
  simp [principal_univ]

Depends on / 依赖: principal_univ, tendsto_iff_ptendsto
-/
theorem tendsto_iff_ptendsto_univ (l₁ : Filter α) (l₂ : Filter β) (f : α -> β) :
    Tendsto f l₁ l₂ ↔ PTendsto (PFun.res f Set.univ) l₁ l₂ := by
  rw [← tendsto_iff_ptendsto]
  simp [principal_univ]

/--
Definition of `pcomap'` / `pcomap'` 的定义

English:
definition pcomap'
  signature: (f : α ->. β) (l : Filter β)
  body: Filter.rcomap' f.graph' l

中文:
定义 pcomap'
  签名: (f : α ->. β) (l : 滤子 β)
  定义体: Filter.rcomap' f.graph' l

Depends on / 依赖: Filter, Filter.rcomap, f.graph, rcomap
-/
def pcomap' (f : α ->. β) (l : Filter β) : Filter α :=
  Filter.rcomap' f.graph' l

/--
Definition of `PTendsto'` / `PTendsto'` 的定义

English:
definition PTendsto'
  signature: (f : α ->. β) (l₁ : Filter α) (l₂ : Filter β)
  body: l₁ <= l₂.rcomap' f.graph'

中文:
定义 PTendsto'
  签名: (f : α ->. β) (l₁ : 滤子 α) (l₂ : 滤子 β)
  定义体: l₁ <= l₂.rcomap' f.graph'

Depends on / 依赖: f.graph, rcomap
-/
def PTendsto' (f : α ->. β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁ <= l₂.rcomap' f.graph'

/--
theorem `ptendsto'_def` / 定理 `ptendsto'_def`

English:
theorem ptendsto'_def
  given: (f : α ->. β) (l₁ : Filter α) (l₂ : Filter β)
  proof: rtendsto'_def _ _ _

中文:
定理 ptendsto'_def
  条件: (f : α ->. β) (l₁ : 滤子 α) (l₂ : 滤子 β)
  证明: rtendsto'_def _ _ _

Depends on / 依赖: _def, rtendsto
-/
theorem ptendsto'_def (f : α ->. β) (l₁ : Filter α) (l₂ : Filter β) :
    PTendsto' f l₁ l₂ ↔ forall s in l₂, f.preimage s in l₁ :=
  rtendsto'_def _ _ _

/--
theorem `ptendsto_of_ptendsto'` / 定理 `ptendsto_of_ptendsto'`

English:
theorem ptendsto_of_ptendsto'
  given: {f : α ->. β} {l₁ : Filter α} {l₂ : Filter β}
  proof: by
  rw [ptendsto_def]; rw [ptendsto'_def]
  exact fun h s sl₂ => mem_of_superset (h s sl₂) (PFun.preimage_subset_core _ _)

中文:
定理 ptendsto_of_ptendsto'
  条件: {f : α ->. β} {l₁ : 滤子 α} {l₂ : 滤子 β}
  证明: by
  rw [ptendsto_def]; rw [ptendsto'_def]
  exact fun h s sl₂ => mem_of_superset (h s sl₂) (PFun.preimage_subset_core _ _)

Depends on / 依赖: PFun.preimage_subset_core, _def, mem_of_superset, preimage_subset_core, ptendsto, ptendsto_def
-/
theorem ptendsto_of_ptendsto' {f : α ->. β} {l₁ : Filter α} {l₂ : Filter β} :
    PTendsto' f l₁ l₂ -> PTendsto f l₁ l₂ := by
  rw [ptendsto_def]; rw [ptendsto'_def]
  exact fun h s sl₂ => mem_of_superset (h s sl₂) (PFun.preimage_subset_core _ _)

/--
theorem `ptendsto'_of_ptendsto` / 定理 `ptendsto'_of_ptendsto`

English:
theorem ptendsto'_of_ptendsto
  given: {f : α ->. β} {l₁ : Filter α} {l₂ : Filter β} (h : f.Dom in l₁)
  proof: by
  rw [ptendsto_def]; rw [ptendsto'_def]
  intro h' s sl₂
  rw [PFun.preimage_eq]
  exact inter_mem (h' s sl₂) h

中文:
定理 ptendsto'_of_ptendsto
  条件: {f : α ->. β} {l₁ : 滤子 α} {l₂ : 滤子 β} (h : f.Dom in l₁)
  证明: by
  rw [ptendsto_def]; rw [ptendsto'_def]
  intro h' s sl₂
  rw [PFun.preimage_eq]
  exact inter_mem (h' s sl₂) h
-/
theorem ptendsto'_of_ptendsto {f : α ->. β} {l₁ : Filter α} {l₂ : Filter β} (h : f.Dom in l₁) :
    PTendsto f l₁ l₂ -> PTendsto' f l₁ l₂ := by
  rw [ptendsto_def]; rw [ptendsto'_def]
  intro h' s sl₂
  rw [PFun.preimage_eq]
  exact inter_mem (h' s sl₂) h

end Filter
