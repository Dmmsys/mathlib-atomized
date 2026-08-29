/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Order.SuccPred.Relation
public import Mathlib.Topology.Order.OrderClosed

/-!
# Connected subsets of topological spaces

In this file we define connected subsets of a topological spaces and various other properties and
classes related to connectivity.

## Main definitions

We define the following properties for sets in a topological space:

* `IsConnected`: a nonempty set that has no non-trivial open partition.
  See also the section below in the module doc.
* `connectedComponent` is the connected component of an element in the space.

We also have a class stating that the whole space satisfies that property: `ConnectedSpace`

## On the definition of connected sets/spaces

In informal mathematics, connected spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `IsPreconnected`.
In other words, the only difference is whether the empty space counts as connected.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.
-/

@[expose] public section

open Set Function Topology TopologicalSpace Relation

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι -> Type*} [TopologicalSpace α]
  {s t u v : Set α}

section Preconnected

/--
Definition of `IsPreconnected` / `IsPreconnected` 的定义

English:
definition IsPreconnected
  signature: (s : Set α)
  body: forall u v : Set α, IsOpen u -> IsOpen v -> s subseteq u union v -> (s inter u).Nonempty -> (s inter v).Nonempty ->
    (s inter (u inter v)).Nonempty

中文:
定义 是预连通
  签名: (s : 集合 α)
  定义体: forall u v : Set α, IsOpen u -> IsOpen v -> s subseteq u union v -> (s inter u).Nonempty -> (s inter v).Nonempty ->
    (s inter (u inter v)).Nonempty

Depends on / 依赖: IsOpen, Nonempty, subseteq
-/
def IsPreconnected (s : Set α) : Prop :=
  forall u v : Set α, IsOpen u -> IsOpen v -> s subseteq u union v -> (s inter u).Nonempty -> (s inter v).Nonempty ->
    (s inter (u inter v)).Nonempty

/--
Definition of `IsConnected` / `IsConnected` 的定义

English:
definition IsConnected
  signature: (s : Set α)
  body: s.Nonempty ∧ IsPreconnected s

中文:
定义 是连通
  签名: (s : 集合 α)
  定义体: s.Nonempty ∧ IsPreconnected s

Depends on / 依赖: IsPreconnected, Nonempty, s.Nonempty
-/
def IsConnected (s : Set α) : Prop :=
  s.Nonempty ∧ IsPreconnected s

/--
theorem `IsConnected.nonempty` / 定理 `IsConnected.nonempty`

English:
theorem IsConnected.nonempty
  given: {s : Set α} (h : IsConnected s)
  statement: s.Nonempty
  proof: h.1

中文:
定理 是连通.nonempty
  条件: {s : 集合 α} (h : 是连通 s)
  结论: s.非空
  证明: h.1
-/
theorem IsConnected.nonempty {s : Set α} (h : IsConnected s) : s.Nonempty :=
  h.1

/--
theorem `IsConnected.isPreconnected` / 定理 `IsConnected.isPreconnected`

English:
theorem IsConnected.isPreconnected
  given: {s : Set α} (h : IsConnected s)
  statement: IsPreconnected s
  proof: h.2

中文:
定理 是连通.isPreconnected
  条件: {s : 集合 α} (h : 是连通 s)
  结论: 是预连通 s
  证明: h.2
-/
theorem IsConnected.isPreconnected {s : Set α} (h : IsConnected s) : IsPreconnected s :=
  h.2

/--
theorem `IsPreirreducible.isPreconnected` / 定理 `IsPreirreducible.isPreconnected`

English:
theorem IsPreirreducible.isPreconnected
  given: {s : Set α} (H : IsPreirreducible s)
  statement: IsPreconnected s
  proof: fun _ _ hu hv _ => H _ _ hu hv

中文:
定理 IsPreirreducible.isPreconnected
  条件: {s : 集合 α} (H : IsPreirreducible s)
  结论: 是预连通 s
  证明: fun _ _ hu hv _ => H _ _ hu hv
-/
theorem IsPreirreducible.isPreconnected {s : Set α} (H : IsPreirreducible s) : IsPreconnected s :=
  fun _ _ hu hv _ => H _ _ hu hv

/--
theorem `IsIrreducible.isConnected` / 定理 `IsIrreducible.isConnected`

English:
theorem IsIrreducible.isConnected
  given: {s : Set α} (H : IsIrreducible s)
  statement: IsConnected s
  proof: ⟨H.nonempty, H.isPreirreducible.isPreconnected⟩

中文:
定理 是不可约.isConnected
  条件: {s : 集合 α} (H : 是不可约 s)
  结论: 是连通 s
  证明: ⟨H.nonempty, H.isPreirreducible.isPreconnected⟩

Depends on / 依赖: H.isPreirreducible.isPreconnected, H.nonempty, isPreconnected, isPreirreducible, nonempty
-/
theorem IsIrreducible.isConnected {s : Set α} (H : IsIrreducible s) : IsConnected s :=
  ⟨H.nonempty, H.isPreirreducible.isPreconnected⟩

/--
theorem `isPreconnected_empty` / 定理 `isPreconnected_empty`

English:
theorem isPreconnected_empty
  statement: IsPreconnected (∅ : Set α)
  proof: isPreirreducible_empty.isPreconnected

中文:
定理 isPreconnected_empty
  结论: 是预连通 (∅ : 集合 α)
  证明: isPreirreducible_empty.isPreconnected

Depends on / 依赖: isPreconnected, isPreirreducible_empty, isPreirreducible_empty.isPreconnected
-/
theorem isPreconnected_empty : IsPreconnected (∅ : Set α) :=
  isPreirreducible_empty.isPreconnected

/--
theorem `isConnected_singleton` / 定理 `isConnected_singleton`

English:
theorem isConnected_singleton
  given: {x}
  statement: IsConnected ({x} : Set α)
  proof: isIrreducible_singleton.isConnected

中文:
定理 isConnected_singleton
  条件: {x}
  结论: 是连通 ({x} : 集合 α)
  证明: isIrreducible_singleton.isConnected

Depends on / 依赖: isConnected, isIrreducible_singleton, isIrreducible_singleton.isConnected
-/
theorem isConnected_singleton {x} : IsConnected ({x} : Set α) :=
  isIrreducible_singleton.isConnected

/--
theorem `isPreconnected_singleton` / 定理 `isPreconnected_singleton`

English:
theorem isPreconnected_singleton
  given: {x}
  statement: IsPreconnected ({x} : Set α)
  proof: isConnected_singleton.isPreconnected

中文:
定理 isPreconnected_singleton
  条件: {x}
  结论: 是预连通 ({x} : 集合 α)
  证明: isConnected_singleton.isPreconnected

Depends on / 依赖: isConnected_singleton, isConnected_singleton.isPreconnected, isPreconnected
-/
theorem isPreconnected_singleton {x} : IsPreconnected ({x} : Set α) :=
  isConnected_singleton.isPreconnected

/--
theorem `Set.Subsingleton.isPreconnected` / 定理 `Set.Subsingleton.isPreconnected`

English:
theorem Set.Subsingleton.isPreconnected
  given: {s : Set α} (hs : s.Subsingleton)
  statement: IsPreconnected s
  proof: hs.induction_on isPreconnected_empty fun _ => isPreconnected_singleton

中文:
定理 集合.子单例.isPreconnected
  条件: {s : 集合 α} (hs : s.子单例)
  结论: 是预连通 s
  证明: hs.induction_on isPreconnected_empty fun _ => isPreconnected_singleton

Depends on / 依赖: hs.induction_on, induction_on, isPreconnected_empty, isPreconnected_singleton
-/
theorem Set.Subsingleton.isPreconnected {s : Set α} (hs : s.Subsingleton) : IsPreconnected s :=
  hs.induction_on isPreconnected_empty fun _ => isPreconnected_singleton

/--
theorem `isPreconnected_of_forall` / 定理 `isPreconnected_of_forall`

English:
theorem isPreconnected_of_forall
  statement: {s : Set α} (x : α)
  proof: by
  rintro u v hu hv hs ⟨z, zs, zu⟩ ⟨y, ys, yv⟩
  have xs : x in s := by
    rcases H y ys with ⟨t, ts, xt, -, -⟩
    exact ts xt
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: use `wlog xu : x ∈ u := hs xs using u v y z, v u z y`
  cases hs xs with
  | inl xu =>
    rcases H y ys with ⟨t, ts, xt, yt, ht⟩
    have := ht u v hu hv (ts.trans hs) ⟨x, xt, xu⟩ ⟨y, yt, yv⟩
    exact this.imp fun z hz => ⟨ts hz.1, hz.2⟩
  | inr xv =>
    rcases H z zs with ⟨t, ts, xt, zt, ht⟩
    have := ht v u hv hu (ts.trans <| by rwa [union_comm]) ⟨x, xt, xv⟩ ⟨z, zt, zu⟩
    exact this.imp fun _ h => ⟨ts h.1, h.2.2, h.2.1⟩

中文:
定理 isPreconnected_of_对任意
  结论: {s : 集合 α} (x : α)
  证明: by
  rintro u v hu hv hs ⟨z, zs, zu⟩ ⟨y, ys, yv⟩
  have xs : x in s := by
    rcases H y ys with ⟨t, ts, xt, -, -⟩
    exact ts xt
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: use `wlog xu : x ∈ u := hs xs using u v y z, v u z y`
  cases hs xs with
  | inl xu =>
    rcases H y ys with ⟨t, ts, xt, yt, ht⟩
    have := ht u v hu hv (ts.trans hs) ⟨x, xt, xu⟩ ⟨y, yt, yv⟩
    exact this.imp fun z hz => ⟨ts hz.1, hz.2⟩
  | inr xv =>
    rcases H z zs with ⟨t, ts, xt, zt, ht⟩
    have := ht v u hv hu (ts.trans <| by rwa [union_comm]) ⟨x, xt, xv⟩ ⟨z, zt, zu⟩
    exact this.imp fun _ h => ⟨ts h.1, h.2.2, h.2.1⟩
-/
theorem isPreconnected_of_forall {s : Set α} (x : α)
    (H : forall y in s, exists t, t subseteq s ∧ x in t ∧ y in t ∧ IsPreconnected t) : IsPreconnected s := by
  rintro u v hu hv hs ⟨z, zs, zu⟩ ⟨y, ys, yv⟩
  have xs : x in s := by
    rcases H y ys with ⟨t, ts, xt, -, -⟩
    exact ts xt
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: use `wlog xu : x ∈ u := hs xs using u v y z, v u z y`
  cases hs xs with
  | inl xu =>
    rcases H y ys with ⟨t, ts, xt, yt, ht⟩
    have := ht u v hu hv (ts.trans hs) ⟨x, xt, xu⟩ ⟨y, yt, yv⟩
    exact this.imp fun z hz => ⟨ts hz.1, hz.2⟩
  | inr xv =>
    rcases H z zs with ⟨t, ts, xt, zt, ht⟩
    have := ht v u hv hu (ts.trans <| by rwa [union_comm]) ⟨x, xt, xv⟩ ⟨z, zt, zu⟩
    exact this.imp fun _ h => ⟨ts h.1, h.2.2, h.2.1⟩

/--
theorem `isPreconnected_of_forall_pair` / 定理 `isPreconnected_of_forall_pair`

English:
theorem isPreconnected_of_forall_pair
  statement: {s : Set α}
  proof: by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
  exacts [isPreconnected_empty, isPreconnected_of_forall x fun y => H x hx y]

中文:
定理 isPreconnected_of_对任意_pair
  结论: {s : 集合 α}
  证明: by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
  exacts [isPreconnected_empty, isPreconnected_of_forall x fun y => H x hx y]

Depends on / 依赖: eq_empty_or_nonempty, exacts, isPreconnected_empty, isPreconnected_of_forall
-/
theorem isPreconnected_of_forall_pair {s : Set α}
    (H : forall x in s, forall y in s, exists t, t subseteq s ∧ x in t ∧ y in t ∧ IsPreconnected t) :
    IsPreconnected s := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
  exacts [isPreconnected_empty, isPreconnected_of_forall x fun y => H x hx y]

/--
theorem `isPreconnected_sUnion` / 定理 `isPreconnected_sUnion`

English:
theorem isPreconnected_sUnion
  statement: (x : α) (c : Set (Set α)) (H1 : forall s in c, x in s)
  proof: by
  apply isPreconnected_of_forall x
  rintro y ⟨s, sc, ys⟩
  exact ⟨s, subset_sUnion_of_mem sc, H1 s sc, ys, H2 s sc⟩

中文:
定理 isPreconnected_sUnion
  结论: (x : α) (c : 集合 (集合 α)) (H1 : 对任意 s in c, x in s)
  证明: by
  apply isPreconnected_of_forall x
  rintro y ⟨s, sc, ys⟩
  exact ⟨s, subset_sUnion_of_mem sc, H1 s sc, ys, H2 s sc⟩

Depends on / 依赖: isPreconnected_of_forall, subset_sUnion_of_mem
-/
theorem isPreconnected_sUnion (x : α) (c : Set (Set α)) (H1 : forall s in c, x in s)
    (H2 : forall s in c, IsPreconnected s) : IsPreconnected (⋃₀ c) := by
  apply isPreconnected_of_forall x
  rintro y ⟨s, sc, ys⟩
  exact ⟨s, subset_sUnion_of_mem sc, H1 s sc, ys, H2 s sc⟩

/--
theorem `isPreconnected_iUnion` / 定理 `isPreconnected_iUnion`

English:
theorem isPreconnected_iUnion
  statement: {ι : Sort*} {s : ι -> Set α} (h₁ : (⋂ i, s i).Nonempty)
  proof: Exists.elim h₁ fun f hf => isPreconnected_sUnion f _ hf (forall_mem_range.2 h₂)

中文:
定理 isPreconnected_iUnion
  结论: {ι : 类型层*} {s : ι -> 集合 α} (h₁ : (⋂ i, s i).非空)
  证明: Exists.elim h₁ fun f hf => isPreconnected_sUnion f _ hf (forall_mem_range.2 h₂)

Depends on / 依赖: Exists, Exists.elim, forall_mem_range, isPreconnected_sUnion
-/
theorem isPreconnected_iUnion {ι : Sort*} {s : ι -> Set α} (h₁ : (⋂ i, s i).Nonempty)
    (h₂ : forall i, IsPreconnected (s i)) : IsPreconnected (⋃ i, s i) :=
  Exists.elim h₁ fun f hf => isPreconnected_sUnion f _ hf (forall_mem_range.2 h₂)

/--
theorem `IsPreconnected.union` / 定理 `IsPreconnected.union`

English:
theorem IsPreconnected.union
  statement: (x : α) {s t : Set α} (H1 : x in s) (H2 : x in t) (H3 : IsPreconnected s)
  proof: sUnion_pair s t ▸ isPreconnected_sUnion x {s, t} (by rintro r (rfl | rfl | h) <;> assumption)
    (by rintro r (rfl | rfl | h) <;> assumption)

中文:
定理 是预连通.union
  结论: (x : α) {s t : 集合 α} (H1 : x in s) (H2 : x in t) (H3 : 是预连通 s)
  证明: sUnion_pair s t ▸ isPreconnected_sUnion x {s, t} (by rintro r (rfl | rfl | h) <;> assumption)
    (by rintro r (rfl | rfl | h) <;> assumption)

Depends on / 依赖: isPreconnected_sUnion, sUnion_pair
-/
theorem IsPreconnected.union (x : α) {s t : Set α} (H1 : x in s) (H2 : x in t) (H3 : IsPreconnected s)
    (H4 : IsPreconnected t) : IsPreconnected (s union t) :=
  sUnion_pair s t ▸ isPreconnected_sUnion x {s, t} (by rintro r (rfl | rfl | h) <;> assumption)
    (by rintro r (rfl | rfl | h) <;> assumption)

/--
theorem `IsPreconnected.union'` / 定理 `IsPreconnected.union'`

English:
theorem IsPreconnected.union'
  statement: {s t : Set α} (H : (s inter t).Nonempty) (hs : IsPreconnected s)
  proof: by
  rcases H with ⟨x, hxs, hxt⟩
  exact hs.union x hxs hxt ht

中文:
定理 是预连通.union'
  结论: {s t : 集合 α} (H : (s inter t).非空) (hs : 是预连通 s)
  证明: by
  rcases H with ⟨x, hxs, hxt⟩
  exact hs.union x hxs hxt ht

Depends on / 依赖: hs.union
-/
theorem IsPreconnected.union' {s t : Set α} (H : (s inter t).Nonempty) (hs : IsPreconnected s)
    (ht : IsPreconnected t) : IsPreconnected (s union t) := by
  rcases H with ⟨x, hxs, hxt⟩
  exact hs.union x hxs hxt ht

/--
theorem `IsConnected.union` / 定理 `IsConnected.union`

English:
theorem IsConnected.union
  statement: {s t : Set α} (H : (s inter t).Nonempty) (Hs : IsConnected s)
  proof: by
  rcases H with ⟨x, hx⟩
  refine ⟨⟨x, mem_union_left t (mem_of_mem_inter_left hx)⟩, ?_⟩
  exact Hs.isPreconnected.union x (mem_of_mem_inter_left hx) (mem_of_mem_inter_right hx)
    Ht.isPreconnected

中文:
定理 是连通.union
  结论: {s t : 集合 α} (H : (s inter t).非空) (Hs : 是连通 s)
  证明: by
  rcases H with ⟨x, hx⟩
  refine ⟨⟨x, mem_union_left t (mem_of_mem_inter_left hx)⟩, ?_⟩
  exact Hs.isPreconnected.union x (mem_of_mem_inter_left hx) (mem_of_mem_inter_right hx)
    Ht.isPreconnected

Depends on / 依赖: Hs.isPreconnected.union, Ht.isPreconnected, isPreconnected, mem_of_mem_inter_left, mem_of_mem_inter_right, mem_union_left
-/
theorem IsConnected.union {s t : Set α} (H : (s inter t).Nonempty) (Hs : IsConnected s)
    (Ht : IsConnected t) : IsConnected (s union t) := by
  rcases H with ⟨x, hx⟩
  refine ⟨⟨x, mem_union_left t (mem_of_mem_inter_left hx)⟩, ?_⟩
  exact Hs.isPreconnected.union x (mem_of_mem_inter_left hx) (mem_of_mem_inter_right hx)
    Ht.isPreconnected

/--
theorem `IsPreconnected.sUnion_directed` / 定理 `IsPreconnected.sUnion_directed`

English:
theorem IsPreconnected.sUnion_directed
  statement: {S : Set (Set α)} (K : DirectedOn (· subseteq ·) S)
  proof: by
  rintro u v hu hv Huv ⟨a, ⟨s, hsS, has⟩, hau⟩ ⟨b, ⟨t, htS, hbt⟩, hbv⟩
  obtain ⟨r, hrS, hsr, htr⟩ : exists r in S, s subseteq r ∧ t subseteq r := K s hsS t htS
  have Hnuv : (r inter (u inter v)).Nonempty :=
    H _ hrS u v hu hv ((subset_sUnion_of_mem hrS).trans Huv) ⟨a, hsr has, hau⟩ ⟨b, htr hbt, hbv⟩
  have Kruv : r inter (u inter v) subseteq ⋃₀ S inter (u inter v) := inter_subset_inter_left _ (subset_sUnion_of_mem hrS)
  exact Hnuv.mono Kruv

中文:
定理 是预连通.sUnion_directed
  结论: {S : 集合 (集合 α)} (K : DirectedOn (· subseteq ·) S)
  证明: by
  rintro u v hu hv Huv ⟨a, ⟨s, hsS, has⟩, hau⟩ ⟨b, ⟨t, htS, hbt⟩, hbv⟩
  obtain ⟨r, hrS, hsr, htr⟩ : exists r in S, s subseteq r ∧ t subseteq r := K s hsS t htS
  have Hnuv : (r inter (u inter v)).Nonempty :=
    H _ hrS u v hu hv ((subset_sUnion_of_mem hrS).trans Huv) ⟨a, hsr has, hau⟩ ⟨b, htr hbt, hbv⟩
  have Kruv : r inter (u inter v) subseteq ⋃₀ S inter (u inter v) := inter_subset_inter_left _ (subset_sUnion_of_mem hrS)
  exact Hnuv.mono Kruv

Depends on / 依赖: Hnuv.mono, Nonempty, inter_subset_inter_left, subset_sUnion_of_mem, subseteq
-/
theorem IsPreconnected.sUnion_directed {S : Set (Set α)} (K : DirectedOn (· subseteq ·) S)
    (H : forall s in S, IsPreconnected s) : IsPreconnected (⋃₀ S) := by
  rintro u v hu hv Huv ⟨a, ⟨s, hsS, has⟩, hau⟩ ⟨b, ⟨t, htS, hbt⟩, hbv⟩
  obtain ⟨r, hrS, hsr, htr⟩ : exists r in S, s subseteq r ∧ t subseteq r := K s hsS t htS
  have Hnuv : (r inter (u inter v)).Nonempty :=
    H _ hrS u v hu hv ((subset_sUnion_of_mem hrS).trans Huv) ⟨a, hsr has, hau⟩ ⟨b, htr hbt, hbv⟩
  have Kruv : r inter (u inter v) subseteq ⋃₀ S inter (u inter v) := inter_subset_inter_left _ (subset_sUnion_of_mem hrS)
  exact Hnuv.mono Kruv

/--
theorem `IsPreconnected.biUnion_of_reflTransGen` / 定理 `IsPreconnected.biUnion_of_reflTransGen`

English:
theorem IsPreconnected.biUnion_of_reflTransGen
  statement: {ι : Type*} {t : Set ι} {s : ι -> Set α}
  proof: by
  let R := fun i j : ι => (s i inter s j).Nonempty ∧ i in t
  have P : forall i, i in t -> forall j, j in t -> ReflTransGen R i j ->
      exists p, p subseteq t ∧ i in p ∧ j in p ∧ IsPreconnected (⋃ j in p, s j) := fun i hi j hj h => by
    induction h with
    | refl =>
      refine ⟨{i}, singleton_subset_iff.mpr hi, mem_singleton i, mem_singleton i, ?_⟩
      rw [biUnion_singleton]
      exact H i hi
    | @tail j k _ hjk ih =>
      obtain ⟨p, hpt, hip, hjp, hp⟩ := ih hjk.2
      refine ⟨insert k p, insert_subset_iff.mpr ⟨hj, hpt⟩, mem_insert_of_mem k hip,
        mem_insert k p, ?_⟩
      rw [biUnion_insert]
      refine (H k hj).union' (hjk.1.mono ?_) hp
      rw [inter_comm]
      exact inter_subset_inter_right _ (subset_biUnion_of_mem hjp)
  refine isPreconnected_of_forall_pair ?_
  intro x hx y hy
  obtain ⟨i : ι, hi : i in t, hxi : x in s i⟩ := mem_iUnion₂.1 hx
  obtain ⟨j : ι, hj : j in t, hyj : y in s j⟩ := mem_iUnion₂.1 hy
  obtain ⟨p, hpt, hip, hjp, hp⟩ := P i hi j hj (K i hi j hj)
  exact ⟨⋃ j in p, s j, biUnion_subset_biUnion_left hpt, mem_biUnion hip hxi,
    mem_biUnion hjp hyj, hp⟩

中文:
定理 是预连通.biUnion_of_reflTransGen
  结论: {ι : 类型} {t : 集合 ι} {s : ι -> 集合 α}
  证明: by
  let R := fun i j : ι => (s i inter s j).Nonempty ∧ i in t
  have P : forall i, i in t -> forall j, j in t -> ReflTransGen R i j ->
      exists p, p subseteq t ∧ i in p ∧ j in p ∧ IsPreconnected (⋃ j in p, s j) := fun i hi j hj h => by
    induction h with
    | refl =>
      refine ⟨{i}, singleton_subset_iff.mpr hi, mem_singleton i, mem_singleton i, ?_⟩
      rw [biUnion_singleton]
      exact H i hi
    | @tail j k _ hjk ih =>
      obtain ⟨p, hpt, hip, hjp, hp⟩ := ih hjk.2
      refine ⟨insert k p, insert_subset_iff.mpr ⟨hj, hpt⟩, mem_insert_of_mem k hip,
        mem_insert k p, ?_⟩
      rw [biUnion_insert]
      refine (H k hj).union' (hjk.1.mono ?_) hp
      rw [inter_comm]
      exact inter_subset_inter_right _ (subset_biUnion_of_mem hjp)
  refine isPreconnected_of_forall_pair ?_
  intro x hx y hy
  obtain ⟨i : ι, hi : i in t, hxi : x in s i⟩ := mem_iUnion₂.1 hx
  obtain ⟨j : ι, hj : j in t, hyj : y in s j⟩ := mem_iUnion₂.1 hy
  obtain ⟨p, hpt, hip, hjp, hp⟩ := P i hi j hj (K i hi j hj)
  exact ⟨⋃ j in p, s j, biUnion_subset_biUnion_left hpt, mem_biUnion hip hxi,
    mem_biUnion hjp hyj, hp⟩

Depends on / 依赖: IsPreconnected, Nonempty, ReflTransGen, biUnion_singleton, insert, insert_subset_iff, insert_subset_iff.mpr, mem_ins, mem_singleton, singleton_subset_iff, singleton_subset_iff.mpr, subseteq
-/
theorem IsPreconnected.biUnion_of_reflTransGen {ι : Type*} {t : Set ι} {s : ι -> Set α}
    (H : forall i in t, IsPreconnected (s i))
    (K : forall i, i in t -> forall j, j in t -> ReflTransGen (fun i j => (s i inter s j).Nonempty ∧ i in t) i j) :
    IsPreconnected (⋃ n in t, s n) := by
  let R := fun i j : ι => (s i inter s j).Nonempty ∧ i in t
  have P : forall i, i in t -> forall j, j in t -> ReflTransGen R i j ->
      exists p, p subseteq t ∧ i in p ∧ j in p ∧ IsPreconnected (⋃ j in p, s j) := fun i hi j hj h => by
    induction h with
    | refl =>
      refine ⟨{i}, singleton_subset_iff.mpr hi, mem_singleton i, mem_singleton i, ?_⟩
      rw [biUnion_singleton]
      exact H i hi
    | @tail j k _ hjk ih =>
      obtain ⟨p, hpt, hip, hjp, hp⟩ := ih hjk.2
      refine ⟨insert k p, insert_subset_iff.mpr ⟨hj, hpt⟩, mem_insert_of_mem k hip,
        mem_insert k p, ?_⟩
      rw [biUnion_insert]
      refine (H k hj).union' (hjk.1.mono ?_) hp
      rw [inter_comm]
      exact inter_subset_inter_right _ (subset_biUnion_of_mem hjp)
  refine isPreconnected_of_forall_pair ?_
  intro x hx y hy
  obtain ⟨i : ι, hi : i in t, hxi : x in s i⟩ := mem_iUnion₂.1 hx
  obtain ⟨j : ι, hj : j in t, hyj : y in s j⟩ := mem_iUnion₂.1 hy
  obtain ⟨p, hpt, hip, hjp, hp⟩ := P i hi j hj (K i hi j hj)
  exact ⟨⋃ j in p, s j, biUnion_subset_biUnion_left hpt, mem_biUnion hip hxi,
    mem_biUnion hjp hyj, hp⟩

/--
theorem `IsConnected.biUnion_of_reflTransGen` / 定理 `IsConnected.biUnion_of_reflTransGen`

English:
theorem IsConnected.biUnion_of_reflTransGen
  statement: {ι : Type*} {t : Set ι} {s : ι -> Set α}
  proof: ⟨nonempty_biUnion.2 ⟨ht.some, ht.some_mem, (H _ ht.some_mem).nonempty⟩,
    IsPreconnected.biUnion_of_reflTransGen (fun i hi => (H i hi).isPreconnected) K⟩

中文:
定理 是连通.biUnion_of_reflTransGen
  结论: {ι : 类型} {t : 集合 ι} {s : ι -> 集合 α}
  证明: ⟨nonempty_biUnion.2 ⟨ht.some, ht.some_mem, (H _ ht.some_mem).nonempty⟩,
    IsPreconnected.biUnion_of_reflTransGen (fun i hi => (H i hi).isPreconnected) K⟩

Depends on / 依赖: IsPreconnected, IsPreconnected.biUnion_of_reflTransGen, biUnion_of_reflTransGen, ht.some, ht.some_mem, isPreconnected, nonempty, nonempty_biUnion, some_mem
-/
theorem IsConnected.biUnion_of_reflTransGen {ι : Type*} {t : Set ι} {s : ι -> Set α}
    (ht : t.Nonempty) (H : forall i in t, IsConnected (s i))
    (K : forall i, i in t -> forall j, j in t -> ReflTransGen (fun i j : ι => (s i inter s j).Nonempty ∧ i in t) i j) :
    IsConnected (⋃ n in t, s n) :=
⟨nonempty_biUnion.2 ⟨ht.some, ht.some_mem, (H _ ht.some_mem).nonempty⟩,
    IsPreconnected.biUnion_of_reflTransGen (fun i hi => (H i hi).isPreconnected) K⟩

/--
theorem `IsPreconnected.iUnion_of_reflTransGen` / 定理 `IsPreconnected.iUnion_of_reflTransGen`

English:
theorem IsPreconnected.iUnion_of_reflTransGen
  statement: {ι : Type*} {s : ι -> Set α}
  proof: by
  rw [← biUnion_univ]
  exact IsPreconnected.biUnion_of_reflTransGen (fun i _ => H i) fun i _ j _ => by
    simpa [mem_univ] using K i j

中文:
定理 是预连通.iUnion_of_reflTransGen
  结论: {ι : 类型} {s : ι -> 集合 α}
  证明: by
  rw [← biUnion_univ]
  exact IsPreconnected.biUnion_of_reflTransGen (fun i _ => H i) fun i _ j _ => by
    simpa [mem_univ] using K i j

Depends on / 依赖: IsPreconnected, IsPreconnected.biUnion_of_reflTransGen, biUnion_of_reflTransGen, biUnion_univ, mem_univ
-/
theorem IsPreconnected.iUnion_of_reflTransGen {ι : Type*} {s : ι -> Set α}
    (H : forall i, IsPreconnected (s i))
    (K : forall i j, ReflTransGen (fun i j : ι => (s i inter s j).Nonempty) i j) :
    IsPreconnected (⋃ n, s n) := by
  rw [← biUnion_univ]
  exact IsPreconnected.biUnion_of_reflTransGen (fun i _ => H i) fun i _ j _ => by
    simpa [mem_univ] using K i j

/--
theorem `IsConnected.iUnion_of_reflTransGen` / 定理 `IsConnected.iUnion_of_reflTransGen`

English:
theorem IsConnected.iUnion_of_reflTransGen
  statement: {ι : Type*} [Nonempty ι] {s : ι -> Set α}
  proof: ⟨nonempty_iUnion.2 Nonempty.elim ‹_› fun i : ι => ⟨i, (H _).nonempty⟩,
    IsPreconnected.iUnion_of_reflTransGen (fun i => (H i).isPreconnected) K⟩

中文:
定理 是连通.iUnion_of_reflTransGen
  结论: {ι : 类型} [非空 ι] {s : ι -> 集合 α}
  证明: ⟨nonempty_iUnion.2 Nonempty.elim ‹_› fun i : ι => ⟨i, (H _).nonempty⟩,
    IsPreconnected.iUnion_of_reflTransGen (fun i => (H i).isPreconnected) K⟩

Depends on / 依赖: IsPreconnected, IsPreconnected.iUnion_of_reflTransGen, Nonempty, Nonempty.elim, iUnion_of_reflTransGen, isPreconnected, nonempty, nonempty_iUnion
-/
theorem IsConnected.iUnion_of_reflTransGen {ι : Type*} [Nonempty ι] {s : ι -> Set α}
    (H : forall i, IsConnected (s i))
    (K : forall i j, ReflTransGen (fun i j : ι => (s i inter s j).Nonempty) i j) : IsConnected (⋃ n, s n) :=
⟨nonempty_iUnion.2 Nonempty.elim ‹_› fun i : ι => ⟨i, (H _).nonempty⟩,
    IsPreconnected.iUnion_of_reflTransGen (fun i => (H i).isPreconnected) K⟩

/--
lemma `IsPreconnected.transGen_of_iUnion` / 引理 `IsPreconnected.transGen_of_iUnion`

English:
lemma IsPreconnected.transGen_of_iUnion
  statement: {ι : Type*} {s : ι -> Set α}
  proof: by
  by_contra hij
  let S : Set ι := {k | TransGen (fun a b => (s a inter s b).Nonempty) i k}
  let U : Set α := ⋃ k in S, s k
  let V : Set α := ⋃ k in Sᶜ, s k
  have hsplit : (⋃ n, s n) = U union V := iSup_split s (· in S)
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  let hi_S : i in S := Relation.TransGen.single ⟨a, ha, ha⟩
  have hUne : ((⋃ n, s n) inter U).Nonempty := ⟨a, mem_iUnion_of_mem i ha, mem_iUnion₂_of_mem hi_S ha⟩
  have hVne : ((⋃ n, s n) inter V).Nonempty := ⟨b, mem_iUnion_of_mem j hb, mem_iUnion₂_of_mem hij hb⟩
  obtain ⟨x, -, hxU, hxV⟩ := hs U V (isOpen_biUnion fun i a => hs' i)
    (isOpen_biUnion fun i a => hs' i) hsplit.le hUne hVne
  simp only [mem_iUnion, exists_prop, mem_compl_iff, U, V] at hxU hxV
  obtain ⟨k, hk, hxk⟩ := hxU
  obtain ⟨l, hl, hxl⟩ := hxV
  exact hl (hk.tail ⟨x, hxk, hxl⟩)

中文:
引理 是预连通.transGen_of_iUnion
  结论: {ι : 类型} {s : ι -> 集合 α}
  证明: by
  by_contra hij
  let S : Set ι := {k | TransGen (fun a b => (s a inter s b).Nonempty) i k}
  let U : Set α := ⋃ k in S, s k
  let V : Set α := ⋃ k in Sᶜ, s k
  have hsplit : (⋃ n, s n) = U union V := iSup_split s (· in S)
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  let hi_S : i in S := Relation.TransGen.single ⟨a, ha, ha⟩
  have hUne : ((⋃ n, s n) inter U).Nonempty := ⟨a, mem_iUnion_of_mem i ha, mem_iUnion₂_of_mem hi_S ha⟩
  have hVne : ((⋃ n, s n) inter V).Nonempty := ⟨b, mem_iUnion_of_mem j hb, mem_iUnion₂_of_mem hij hb⟩
  obtain ⟨x, -, hxU, hxV⟩ := hs U V (isOpen_biUnion fun i a => hs' i)
    (isOpen_biUnion fun i a => hs' i) hsplit.le hUne hVne
  simp only [mem_iUnion, exists_prop, mem_compl_iff, U, V] at hxU hxV
  obtain ⟨k, hk, hxk⟩ := hxU
  obtain ⟨l, hl, hxl⟩ := hxV
  exact hl (hk.tail ⟨x, hxk, hxl⟩)

Depends on / 依赖: Nonempty, Relation, Relation.TransGen.single, TransGen, hi_S, hsplit, iSup_split, mem_iUnion, mem_iUnion_of_mem, single
-/
lemma IsPreconnected.transGen_of_iUnion {ι : Type*} {s : ι -> Set α}
    (hs : IsPreconnected (⋃ n, s n)) (hs' : forall i, IsOpen (s i)) (i j : ι) (hi : (s i).Nonempty)
    (hj : (s j).Nonempty) : TransGen (fun a b => (s a inter s b).Nonempty) i j := by
  by_contra hij
  let S : Set ι := {k | TransGen (fun a b => (s a inter s b).Nonempty) i k}
  let U : Set α := ⋃ k in S, s k
  let V : Set α := ⋃ k in Sᶜ, s k
  have hsplit : (⋃ n, s n) = U union V := iSup_split s (· in S)
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  let hi_S : i in S := Relation.TransGen.single ⟨a, ha, ha⟩
  have hUne : ((⋃ n, s n) inter U).Nonempty := ⟨a, mem_iUnion_of_mem i ha, mem_iUnion₂_of_mem hi_S ha⟩
  have hVne : ((⋃ n, s n) inter V).Nonempty := ⟨b, mem_iUnion_of_mem j hb, mem_iUnion₂_of_mem hij hb⟩
  obtain ⟨x, -, hxU, hxV⟩ := hs U V (isOpen_biUnion fun i a => hs' i)
    (isOpen_biUnion fun i a => hs' i) hsplit.le hUne hVne
  simp only [mem_iUnion, exists_prop, mem_compl_iff, U, V] at hxU hxV
  obtain ⟨k, hk, hxk⟩ := hxU
  obtain ⟨l, hl, hxl⟩ := hxV
  exact hl (hk.tail ⟨x, hxk, hxl⟩)

section SuccOrder

open Order

variable [LinearOrder β] [SuccOrder β] [IsSuccArchimedean β]

/--
theorem `IsPreconnected.iUnion_of_chain` / 定理 `IsPreconnected.iUnion_of_chain`

English:
theorem IsPreconnected.iUnion_of_chain
  statement: {s : β -> Set α} (H : forall n, IsPreconnected (s n))
  proof: IsPreconnected.iUnion_of_reflTransGen H fun _ _ =>
    reflTransGen_of_succ _ (fun i _ => K i) (by grind)

中文:
定理 是预连通.iUnion_of_chain
  结论: {s : β -> 集合 α} (H : 对任意 n, 是预连通 (s n))
  证明: IsPreconnected.iUnion_of_reflTransGen H fun _ _ =>
    reflTransGen_of_succ _ (fun i _ => K i) (by grind)

Depends on / 依赖: IsPreconnected, IsPreconnected.iUnion_of_reflTransGen, iUnion_of_reflTransGen, reflTransGen_of_succ
-/
theorem IsPreconnected.iUnion_of_chain {s : β -> Set α} (H : forall n, IsPreconnected (s n))
    (K : forall n, (s n inter s (succ n)).Nonempty) : IsPreconnected (⋃ n, s n) :=
  IsPreconnected.iUnion_of_reflTransGen H fun _ _ =>
    reflTransGen_of_succ _ (fun i _ => K i) (by grind)

/--
theorem `IsConnected.iUnion_of_chain` / 定理 `IsConnected.iUnion_of_chain`

English:
theorem IsConnected.iUnion_of_chain
  statement: [Nonempty β] {s : β -> Set α} (H : forall n, IsConnected (s n))
  proof: IsConnected.iUnion_of_reflTransGen H fun _ _ => reflTransGen_of_succ _ (fun i _ => K i) (by grind)

中文:
定理 是连通.iUnion_of_chain
  结论: [非空 β] {s : β -> 集合 α} (H : 对任意 n, 是连通 (s n))
  证明: IsConnected.iUnion_of_reflTransGen H fun _ _ => reflTransGen_of_succ _ (fun i _ => K i) (by grind)

Depends on / 依赖: IsConnected, IsConnected.iUnion_of_reflTransGen, iUnion_of_reflTransGen, reflTransGen_of_succ
-/
theorem IsConnected.iUnion_of_chain [Nonempty β] {s : β -> Set α} (H : forall n, IsConnected (s n))
    (K : forall n, (s n inter s (succ n)).Nonempty) : IsConnected (⋃ n, s n) :=
  IsConnected.iUnion_of_reflTransGen H fun _ _ => reflTransGen_of_succ _ (fun i _ => K i) (by grind)

/--
theorem `IsPreconnected.biUnion_of_chain` / 定理 `IsPreconnected.biUnion_of_chain`

English:
theorem IsPreconnected.biUnion_of_chain
  statement: {s : β -> Set α} {t : Set β} (ht : OrdConnected t)
  proof: by
  have h1 : forall {i j k : β}, i in t -> j in t -> k in Ico i j -> k in t := fun hi hj hk =>
    ht.out hi hj (Ico_subset_Icc_self hk)
  have h2 : forall {i j k : β}, i in t -> j in t -> k in Ico i j -> succ k in t := fun hi hj hk =>
ht.out hi hj ⟨hk.1.trans le_succ _, succ_le_of_lt hk.2⟩
  have h3 : forall {i j k : β}, i in t -> j in t -> k in Ico i j -> (s k inter s (succ k)).Nonempty :=
    fun hi hj hk => K _ (h1 hi hj hk) (h2 hi hj hk)
  refine IsPreconnected.biUnion_of_reflTransGen H fun i hi j hj => ?_
  exact reflTransGen_of_succ _ (fun k hk => ⟨h3 hi hj hk, h1 hi hj hk⟩) fun k hk =>
      ⟨by rw [inter_comm]; exact h3 hj hi hk, h2 hj hi hk⟩

中文:
定理 是预连通.biUnion_of_chain
  结论: {s : β -> 集合 α} {t : 集合 β} (ht : 序连通 t)
  证明: by
  have h1 : forall {i j k : β}, i in t -> j in t -> k in Ico i j -> k in t := fun hi hj hk =>
    ht.out hi hj (Ico_subset_Icc_self hk)
  have h2 : forall {i j k : β}, i in t -> j in t -> k in Ico i j -> succ k in t := fun hi hj hk =>
ht.out hi hj ⟨hk.1.trans le_succ _, succ_le_of_lt hk.2⟩
  have h3 : forall {i j k : β}, i in t -> j in t -> k in Ico i j -> (s k inter s (succ k)).Nonempty :=
    fun hi hj hk => K _ (h1 hi hj hk) (h2 hi hj hk)
  refine IsPreconnected.biUnion_of_reflTransGen H fun i hi j hj => ?_
  exact reflTransGen_of_succ _ (fun k hk => ⟨h3 hi hj hk, h1 hi hj hk⟩) fun k hk =>
      ⟨by rw [inter_comm]; exact h3 hj hi hk, h2 hj hi hk⟩

Depends on / 依赖: Ico_subset_Icc_self, IsPreconnected, IsPreconnected.biUnion_of_reflTransGen, Nonempty, biUnion_of_reflTransGen, ht.out, le_succ, succ_le_of_lt
-/
theorem IsPreconnected.biUnion_of_chain {s : β -> Set α} {t : Set β} (ht : OrdConnected t)
    (H : forall n in t, IsPreconnected (s n))
    (K : forall n : β, n in t -> succ n in t -> (s n inter s (succ n)).Nonempty) :
    IsPreconnected (⋃ n in t, s n) := by
  have h1 : forall {i j k : β}, i in t -> j in t -> k in Ico i j -> k in t := fun hi hj hk =>
    ht.out hi hj (Ico_subset_Icc_self hk)
  have h2 : forall {i j k : β}, i in t -> j in t -> k in Ico i j -> succ k in t := fun hi hj hk =>
ht.out hi hj ⟨hk.1.trans le_succ _, succ_le_of_lt hk.2⟩
  have h3 : forall {i j k : β}, i in t -> j in t -> k in Ico i j -> (s k inter s (succ k)).Nonempty :=
    fun hi hj hk => K _ (h1 hi hj hk) (h2 hi hj hk)
  refine IsPreconnected.biUnion_of_reflTransGen H fun i hi j hj => ?_
  exact reflTransGen_of_succ _ (fun k hk => ⟨h3 hi hj hk, h1 hi hj hk⟩) fun k hk =>
      ⟨by rw [inter_comm]; exact h3 hj hi hk, h2 hj hi hk⟩

/--
theorem `IsConnected.biUnion_of_chain` / 定理 `IsConnected.biUnion_of_chain`

English:
theorem IsConnected.biUnion_of_chain
  statement: {s : β -> Set α} {t : Set β} (hnt : t.Nonempty)
  proof: ⟨nonempty_biUnion.2 ⟨hnt.some, hnt.some_mem, (H _ hnt.some_mem).nonempty⟩,
    IsPreconnected.biUnion_of_chain ht (fun i hi => (H i hi).isPreconnected) K⟩

中文:
定理 是连通.biUnion_of_chain
  结论: {s : β -> 集合 α} {t : 集合 β} (hnt : t.非空)
  证明: ⟨nonempty_biUnion.2 ⟨hnt.some, hnt.some_mem, (H _ hnt.some_mem).nonempty⟩,
    IsPreconnected.biUnion_of_chain ht (fun i hi => (H i hi).isPreconnected) K⟩

Depends on / 依赖: IsPreconnected, IsPreconnected.biUnion_of_chain, biUnion_of_chain, hnt.some, hnt.some_mem, isPreconnected, nonempty, nonempty_biUnion, some_mem
-/
theorem IsConnected.biUnion_of_chain {s : β -> Set α} {t : Set β} (hnt : t.Nonempty)
    (ht : OrdConnected t) (H : forall n in t, IsConnected (s n))
    (K : forall n : β, n in t -> succ n in t -> (s n inter s (succ n)).Nonempty) : IsConnected (⋃ n in t, s n) :=
⟨nonempty_biUnion.2 ⟨hnt.some, hnt.some_mem, (H _ hnt.some_mem).nonempty⟩,
    IsPreconnected.biUnion_of_chain ht (fun i hi => (H i hi).isPreconnected) K⟩

end SuccOrder

/--
theorem `IsPreconnected.subset_closure` / 定理 `IsPreconnected.subset_closure`

English:
theorem IsPreconnected.subset_closure
  statement: {s : Set α} {t : Set α} (H : IsPreconnected s)
  proof: fun u v hu hv htuv ⟨_y, hyt, hyu⟩ ⟨_z, hzt, hzv⟩ =>
  let ⟨p, hpu, hps⟩ := mem_closure_iff.1 (Ktcs hyt) u hu hyu
  let ⟨q, hqv, hqs⟩ := mem_closure_iff.1 (Ktcs hzt) v hv hzv
  let ⟨r, hrs, hruv⟩ := H u v hu hv (Subset.trans Kst htuv) ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩
  ⟨r, Kst hrs, hruv⟩

中文:
定理 是预连通.subset_closure
  结论: {s : 集合 α} {t : 集合 α} (H : 是预连通 s)
  证明: fun u v hu hv htuv ⟨_y, hyt, hyu⟩ ⟨_z, hzt, hzv⟩ =>
  let ⟨p, hpu, hps⟩ := mem_closure_iff.1 (Ktcs hyt) u hu hyu
  let ⟨q, hqv, hqs⟩ := mem_closure_iff.1 (Ktcs hzt) v hv hzv
  let ⟨r, hrs, hruv⟩ := H u v hu hv (Subset.trans Kst htuv) ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩
  ⟨r, Kst hrs, hruv⟩
-/
protected theorem IsPreconnected.subset_closure {s : Set α} {t : Set α} (H : IsPreconnected s)
    (Kst : s subseteq t) (Ktcs : t subseteq closure s) : IsPreconnected t :=
  fun u v hu hv htuv ⟨_y, hyt, hyu⟩ ⟨_z, hzt, hzv⟩ =>
  let ⟨p, hpu, hps⟩ := mem_closure_iff.1 (Ktcs hyt) u hu hyu
  let ⟨q, hqv, hqs⟩ := mem_closure_iff.1 (Ktcs hzt) v hv hzv
  let ⟨r, hrs, hruv⟩ := H u v hu hv (Subset.trans Kst htuv) ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩
  ⟨r, Kst hrs, hruv⟩

/--
theorem `IsConnected.subset_closure` / 定理 `IsConnected.subset_closure`

English:
theorem IsConnected.subset_closure
  statement: {s : Set α} {t : Set α} (H : IsConnected s)
  proof: ⟨Nonempty.mono Kst H.left, IsPreconnected.subset_closure H.right Kst Ktcs⟩

中文:
定理 是连通.subset_closure
  结论: {s : 集合 α} {t : 集合 α} (H : 是连通 s)
  证明: ⟨Nonempty.mono Kst H.left, IsPreconnected.subset_closure H.right Kst Ktcs⟩
-/
protected theorem IsConnected.subset_closure {s : Set α} {t : Set α} (H : IsConnected s)
    (Kst : s subseteq t) (Ktcs : t subseteq closure s) : IsConnected t :=
  ⟨Nonempty.mono Kst H.left, IsPreconnected.subset_closure H.right Kst Ktcs⟩

/--
theorem `IsPreconnected.closure` / 定理 `IsPreconnected.closure`

English:
theorem IsPreconnected.closure
  given: {s : Set α} (H : IsPreconnected s)
  proof: IsPreconnected.subset_closure H subset_closure Subset.rfl

中文:
定理 是预连通.closure
  条件: {s : 集合 α} (H : 是预连通 s)
  证明: IsPreconnected.subset_closure H subset_closure Subset.rfl
-/
protected theorem IsPreconnected.closure {s : Set α} (H : IsPreconnected s) :
    IsPreconnected (closure s) :=
  IsPreconnected.subset_closure H subset_closure Subset.rfl

/--
theorem `IsConnected.closure` / 定理 `IsConnected.closure`

English:
theorem IsConnected.closure
  given: {s : Set α} (H : IsConnected s)
  statement: IsConnected (closure s)
  proof: IsConnected.subset_closure H subset_closure Subset.rfl

中文:
定理 是连通.closure
  条件: {s : 集合 α} (H : 是连通 s)
  结论: 是连通 (closure s)
  证明: IsConnected.subset_closure H subset_closure Subset.rfl
-/
protected theorem IsConnected.closure {s : Set α} (H : IsConnected s) : IsConnected (closure s) :=
IsConnected.subset_closure H subset_closure Subset.rfl

/--
theorem `IsPreconnected.image` / 定理 `IsPreconnected.image`

English:
theorem IsPreconnected.image
  statement: [TopologicalSpace β] {s : Set α} (H : IsPreconnected s)
  proof: by
  -- Unfold/destruct definitions in hypotheses
  rintro u v hu hv huv ⟨_, ⟨x, xs, rfl⟩, xu⟩ ⟨_, ⟨y, ys, rfl⟩, yv⟩
  rcases continuousOn_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuousOn_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  -- Reformulate `huv : f '' s ⊆ u ∪ v` in terms of `u'` and `v'`
  replace huv : s subseteq u' union v' := by
    rw [image_subset_iff]; rw [preimage_union] at huv
    replace huv := subset_inter huv Subset.rfl
    rw [union_inter_distrib_right]; rw [u'_eq]; rw [v'_eq]; rw [← union_inter_distrib_right] at huv
    exact (subset_inter_iff.1 huv).1
  -- Now `s ⊆ u' ∪ v'`, so we can apply `‹IsPreconnected s›`
  obtain ⟨z, hz⟩ : (s inter (u' inter v')).Nonempty := by
    refine H u' v' hu' hv' huv ⟨x, ?_⟩ ⟨y, ?_⟩ <;> rw [inter_comm]
    exacts [u'_eq ▸ ⟨xu, xs⟩, v'_eq ▸ ⟨yv, ys⟩]
  rw [← inter_self s]; rw [inter_assoc]; rw [inter_left_comm s u']; rw [← inter_assoc]; rw [inter_comm s]; rw [inter_comm s]; rw [← u'_eq]; rw [← v'_eq] at hz
  exact ⟨f z, ⟨z, hz.1.2, rfl⟩, hz.1.1, hz.2.1⟩

中文:
定理 是预连通.像
  结论: [拓扑空间 β] {s : 集合 α} (H : 是预连通 s)
  证明: by
  -- Unfold/destruct definitions in hypotheses
  rintro u v hu hv huv ⟨_, ⟨x, xs, rfl⟩, xu⟩ ⟨_, ⟨y, ys, rfl⟩, yv⟩
  rcases continuousOn_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuousOn_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  -- Reformulate `huv : f '' s ⊆ u ∪ v` in terms of `u'` and `v'`
  replace huv : s subseteq u' union v' := by
    rw [image_subset_iff]; rw [preimage_union] at huv
    replace huv := subset_inter huv Subset.rfl
    rw [union_inter_distrib_right]; rw [u'_eq]; rw [v'_eq]; rw [← union_inter_distrib_right] at huv
    exact (subset_inter_iff.1 huv).1
  -- Now `s ⊆ u' ∪ v'`, so we can apply `‹IsPreconnected s›`
  obtain ⟨z, hz⟩ : (s inter (u' inter v')).Nonempty := by
    refine H u' v' hu' hv' huv ⟨x, ?_⟩ ⟨y, ?_⟩ <;> rw [inter_comm]
    exacts [u'_eq ▸ ⟨xu, xs⟩, v'_eq ▸ ⟨yv, ys⟩]
  rw [← inter_self s]; rw [inter_assoc]; rw [inter_left_comm s u']; rw [← inter_assoc]; rw [inter_comm s]; rw [inter_comm s]; rw [← u'_eq]; rw [← v'_eq] at hz
  exact ⟨f z, ⟨z, hz.1.2, rfl⟩, hz.1.1, hz.2.1⟩
-/
protected theorem IsPreconnected.image [TopologicalSpace β] {s : Set α} (H : IsPreconnected s)
    (f : α -> β) (hf : ContinuousOn f s) : IsPreconnected (f '' s) := by
  -- Unfold/destruct definitions in hypotheses
  rintro u v hu hv huv ⟨_, ⟨x, xs, rfl⟩, xu⟩ ⟨_, ⟨y, ys, rfl⟩, yv⟩
  rcases continuousOn_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuousOn_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  -- Reformulate `huv : f '' s ⊆ u ∪ v` in terms of `u'` and `v'`
  replace huv : s subseteq u' union v' := by
    rw [image_subset_iff]; rw [preimage_union] at huv
    replace huv := subset_inter huv Subset.rfl
    rw [union_inter_distrib_right]; rw [u'_eq]; rw [v'_eq]; rw [← union_inter_distrib_right] at huv
    exact (subset_inter_iff.1 huv).1
  -- Now `s ⊆ u' ∪ v'`, so we can apply `‹IsPreconnected s›`
  obtain ⟨z, hz⟩ : (s inter (u' inter v')).Nonempty := by
    refine H u' v' hu' hv' huv ⟨x, ?_⟩ ⟨y, ?_⟩ <;> rw [inter_comm]
    exacts [u'_eq ▸ ⟨xu, xs⟩, v'_eq ▸ ⟨yv, ys⟩]
  rw [← inter_self s]; rw [inter_assoc]; rw [inter_left_comm s u']; rw [← inter_assoc]; rw [inter_comm s]; rw [inter_comm s]; rw [← u'_eq]; rw [← v'_eq] at hz
  exact ⟨f z, ⟨z, hz.1.2, rfl⟩, hz.1.1, hz.2.1⟩

/--
theorem `IsConnected.image` / 定理 `IsConnected.image`

English:
theorem IsConnected.image
  statement: [TopologicalSpace β] {s : Set α} (H : IsConnected s) (f : α -> β)
  proof: ⟨image_nonempty.mpr H.nonempty, H.isPreconnected.image f hf⟩

中文:
定理 是连通.像
  结论: [拓扑空间 β] {s : 集合 α} (H : 是连通 s) (f : α -> β)
  证明: ⟨image_nonempty.mpr H.nonempty, H.isPreconnected.image f hf⟩
-/
protected theorem IsConnected.image [TopologicalSpace β] {s : Set α} (H : IsConnected s) (f : α -> β)
    (hf : ContinuousOn f s) : IsConnected (f '' s) :=
  ⟨image_nonempty.mpr H.nonempty, H.isPreconnected.image f hf⟩

/--
theorem `isPreconnected_closed_iff` / 定理 `isPreconnected_closed_iff`

English:
theorem isPreconnected_closed_iff
  given: {s : Set α}
  proof: ⟨by
      rintro h t t' ht ht' htt' ⟨x, xs, xt⟩ ⟨y, ys, yt'⟩
      rw [← not_disjoint_iff_nonempty_inter]; rw [← subset_compl_iff_disjoint_right]; rw [compl_inter]
      intro h'
      have xt' : x ∉ t' := (h' xs).resolve_left (absurd xt)
      have yt : y ∉ t := (h' ys).resolve_right (absurd yt')
      have := h _ _ ht.isOpen_compl ht'.isOpen_compl h' ⟨y, ys, yt⟩ ⟨x, xs, xt'⟩
      rw [← compl_union] at this
      exact this.ne_empty htt'.disjoint_compl_right.inter_eq,
    by
      rintro h u v hu hv huv ⟨x, xs, xu⟩ ⟨y, ys, yv⟩
      rw [← not_disjoint_iff_nonempty_inter]; rw [← subset_compl_iff_disjoint_right]; rw [compl_inter]
      intro h'
      have xv : x ∉ v := (h' xs).elim (absurd xu) id
      have yu : y ∉ u := (h' ys).elim id (absurd yv)
      have := h _ _ hu.isClosed_compl hv.isClosed_compl h' ⟨y, ys, yu⟩ ⟨x, xs, xv⟩
      rw [← compl_union] at this
      exact this.ne_empty huv.disjoint_compl_right.inter_eq⟩

中文:
定理 isPreconnected_closed_iff
  条件: {s : 集合 α}
  证明: ⟨by
      rintro h t t' ht ht' htt' ⟨x, xs, xt⟩ ⟨y, ys, yt'⟩
      rw [← not_disjoint_iff_nonempty_inter]; rw [← subset_compl_iff_disjoint_right]; rw [compl_inter]
      intro h'
      have xt' : x ∉ t' := (h' xs).resolve_left (absurd xt)
      have yt : y ∉ t := (h' ys).resolve_right (absurd yt')
      have := h _ _ ht.isOpen_compl ht'.isOpen_compl h' ⟨y, ys, yt⟩ ⟨x, xs, xt'⟩
      rw [← compl_union] at this
      exact this.ne_empty htt'.disjoint_compl_right.inter_eq,
    by
      rintro h u v hu hv huv ⟨x, xs, xu⟩ ⟨y, ys, yv⟩
      rw [← not_disjoint_iff_nonempty_inter]; rw [← subset_compl_iff_disjoint_right]; rw [compl_inter]
      intro h'
      have xv : x ∉ v := (h' xs).elim (absurd xu) id
      have yu : y ∉ u := (h' ys).elim id (absurd yv)
      have := h _ _ hu.isClosed_compl hv.isClosed_compl h' ⟨y, ys, yu⟩ ⟨x, xs, xv⟩
      rw [← compl_union] at this
      exact this.ne_empty huv.disjoint_compl_right.inter_eq⟩

Depends on / 依赖: absurd, compl_inter, compl_union, disjoint_compl_right, disjoint_compl_right.inter_eq, ht.isOpen_compl, inter_eq, isOpen_compl, ne_empty, not_disjoint_iff_, not_disjoint_iff_nonempty_inter, resolve_left, resolve_right, subset_compl_iff_disjoint_right, this.ne_empty
-/
theorem isPreconnected_closed_iff {s : Set α} :
    IsPreconnected s ↔ forall t t', IsClosed t -> IsClosed t' ->
      s subseteq t union t' -> (s inter t).Nonempty -> (s inter t').Nonempty -> (s inter (t inter t')).Nonempty :=
  ⟨by
      rintro h t t' ht ht' htt' ⟨x, xs, xt⟩ ⟨y, ys, yt'⟩
      rw [← not_disjoint_iff_nonempty_inter]; rw [← subset_compl_iff_disjoint_right]; rw [compl_inter]
      intro h'
      have xt' : x ∉ t' := (h' xs).resolve_left (absurd xt)
      have yt : y ∉ t := (h' ys).resolve_right (absurd yt')
      have := h _ _ ht.isOpen_compl ht'.isOpen_compl h' ⟨y, ys, yt⟩ ⟨x, xs, xt'⟩
      rw [← compl_union] at this
      exact this.ne_empty htt'.disjoint_compl_right.inter_eq,
    by
      rintro h u v hu hv huv ⟨x, xs, xu⟩ ⟨y, ys, yv⟩
      rw [← not_disjoint_iff_nonempty_inter]; rw [← subset_compl_iff_disjoint_right]; rw [compl_inter]
      intro h'
      have xv : x ∉ v := (h' xs).elim (absurd xu) id
      have yu : y ∉ u := (h' ys).elim id (absurd yv)
      have := h _ _ hu.isClosed_compl hv.isClosed_compl h' ⟨y, ys, yu⟩ ⟨x, xs, xv⟩
      rw [← compl_union] at this
      exact this.ne_empty huv.disjoint_compl_right.inter_eq⟩

/--
theorem `Topology.IsInducing.isPreconnected_image` / 定理 `Topology.IsInducing.isPreconnected_image`

English:
theorem Topology.IsInducing.isPreconnected_image
  statement: [TopologicalSpace β] {s : Set α} {f : α -> β}
  proof: by
  refine ⟨fun h => ?_, fun h => h.image _ hf.continuous.continuousOn⟩
  rintro u v hu' hv' huv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
  rcases hf.isOpen_iff.1 hu' with ⟨u, hu, rfl⟩
  rcases hf.isOpen_iff.1 hv' with ⟨v, hv, rfl⟩
  replace huv : f '' s subseteq u union v := by rwa [image_subset_iff]
  rcases h u v hu hv huv ⟨f x, mem_image_of_mem _ hxs, hxu⟩ ⟨f y, mem_image_of_mem _ hys, hyv⟩ with
    ⟨_, ⟨z, hzs, rfl⟩, hzuv⟩
  exact ⟨z, hzs, hzuv⟩

中文:
定理 拓扑.是Inducing.isPreconnected_image
  结论: [拓扑空间 β] {s : 集合 α} {f : α -> β}
  证明: by
  refine ⟨fun h => ?_, fun h => h.image _ hf.continuous.continuousOn⟩
  rintro u v hu' hv' huv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
  rcases hf.isOpen_iff.1 hu' with ⟨u, hu, rfl⟩
  rcases hf.isOpen_iff.1 hv' with ⟨v, hv, rfl⟩
  replace huv : f '' s subseteq u union v := by rwa [image_subset_iff]
  rcases h u v hu hv huv ⟨f x, mem_image_of_mem _ hxs, hxu⟩ ⟨f y, mem_image_of_mem _ hys, hyv⟩ with
    ⟨_, ⟨z, hzs, rfl⟩, hzuv⟩
  exact ⟨z, hzs, hzuv⟩

Depends on / 依赖: continuous, continuousOn, h.image, hf.continuous.continuousOn, hf.isOpen_iff, image_subset_iff, isOpen_iff, mem_image_of_mem, replace, subseteq
-/
theorem Topology.IsInducing.isPreconnected_image [TopologicalSpace β] {s : Set α} {f : α -> β}
    (hf : IsInducing f) : IsPreconnected (f '' s) ↔ IsPreconnected s := by
  refine ⟨fun h => ?_, fun h => h.image _ hf.continuous.continuousOn⟩
  rintro u v hu' hv' huv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
  rcases hf.isOpen_iff.1 hu' with ⟨u, hu, rfl⟩
  rcases hf.isOpen_iff.1 hv' with ⟨v, hv, rfl⟩
  replace huv : f '' s subseteq u union v := by rwa [image_subset_iff]
  rcases h u v hu hv huv ⟨f x, mem_image_of_mem _ hxs, hxu⟩ ⟨f y, mem_image_of_mem _ hys, hyv⟩ with
    ⟨_, ⟨z, hzs, rfl⟩, hzuv⟩
  exact ⟨z, hzs, hzuv⟩


/--
theorem `IsPreconnected.preimage_of_isOpenMap` / 定理 `IsPreconnected.preimage_of_isOpenMap`

English:
theorem IsPreconnected.preimage_of_isOpenMap
  statement: [TopologicalSpace β] {f : α -> β} {s : Set β}
  proof: fun u v hu hv hsuv hsu hsv => by
  replace hsf : f '' f ⁻¹' s = s := image_preimage_eq_of_subset hsf
  obtain ⟨_, has, ⟨a, hau, rfl⟩, hav⟩ : (s inter (f '' u inter f '' v)).Nonempty := by
    refine hs (f '' u) (f '' v) (hf u hu) (hf v hv) ?_ ?_ ?_
    · simpa only [hsf, image_union] using image_mono (f := f) hsuv
    · simpa only [image_preimage_inter] using hsu.image f
    · simpa only [image_preimage_inter] using hsv.image f
  · exact ⟨a, has, hau, hinj.mem_set_image.1 hav⟩

中文:
定理 是预连通.preimage_of_isOpenMap
  结论: [拓扑空间 β] {f : α -> β} {s : 集合 β}
  证明: fun u v hu hv hsuv hsu hsv => by
  replace hsf : f '' f ⁻¹' s = s := image_preimage_eq_of_subset hsf
  obtain ⟨_, has, ⟨a, hau, rfl⟩, hav⟩ : (s inter (f '' u inter f '' v)).Nonempty := by
    refine hs (f '' u) (f '' v) (hf u hu) (hf v hv) ?_ ?_ ?_
    · simpa only [hsf, image_union] using image_mono (f := f) hsuv
    · simpa only [image_preimage_inter] using hsu.image f
    · simpa only [image_preimage_inter] using hsv.image f
  · exact ⟨a, has, hau, hinj.mem_set_image.1 hav⟩

Depends on / 依赖: Nonempty, hinj.mem_set_image, hsu.image, hsv.image, image_mono, image_preimage_eq_of_subset, image_preimage_inter, image_union, mem_set_image, replace
-/
theorem IsPreconnected.preimage_of_isOpenMap [TopologicalSpace β] {f : α -> β} {s : Set β}
    (hs : IsPreconnected s) (hinj : Function.Injective f) (hf : IsOpenMap f) (hsf : s subseteq range f) :
    IsPreconnected (f ⁻¹' s) := fun u v hu hv hsuv hsu hsv => by
  replace hsf : f '' f ⁻¹' s = s := image_preimage_eq_of_subset hsf
  obtain ⟨_, has, ⟨a, hau, rfl⟩, hav⟩ : (s inter (f '' u inter f '' v)).Nonempty := by
    refine hs (f '' u) (f '' v) (hf u hu) (hf v hv) ?_ ?_ ?_
    · simpa only [hsf, image_union] using image_mono (f := f) hsuv
    · simpa only [image_preimage_inter] using hsu.image f
    · simpa only [image_preimage_inter] using hsv.image f
  · exact ⟨a, has, hau, hinj.mem_set_image.1 hav⟩

/--
theorem `IsPreconnected.preimage_of_isClosedMap` / 定理 `IsPreconnected.preimage_of_isClosedMap`

English:
theorem IsPreconnected.preimage_of_isClosedMap
  statement: [TopologicalSpace β] {s : Set β}
  proof: isPreconnected_closed_iff.2 fun u v hu hv hsuv hsu hsv => by
    replace hsf : f '' f ⁻¹' s = s := image_preimage_eq_of_subset hsf
    obtain ⟨_, has, ⟨a, hau, rfl⟩, hav⟩ : (s inter (f '' u inter f '' v)).Nonempty := by
      refine isPreconnected_closed_iff.1 hs (f '' u) (f '' v) (hf u hu) (hf v hv) ?_ ?_ ?_
      · simpa only [hsf, image_union] using image_mono (f := f) hsuv
      · simpa only [image_preimage_inter] using hsu.image f
      · simpa only [image_preimage_inter] using hsv.image f
    · exact ⟨a, has, hau, hinj.mem_set_image.1 hav⟩

中文:
定理 是预连通.preimage_of_isClosedMap
  结论: [拓扑空间 β] {s : 集合 β}
  证明: isPreconnected_closed_iff.2 fun u v hu hv hsuv hsu hsv => by
    replace hsf : f '' f ⁻¹' s = s := image_preimage_eq_of_subset hsf
    obtain ⟨_, has, ⟨a, hau, rfl⟩, hav⟩ : (s inter (f '' u inter f '' v)).Nonempty := by
      refine isPreconnected_closed_iff.1 hs (f '' u) (f '' v) (hf u hu) (hf v hv) ?_ ?_ ?_
      · simpa only [hsf, image_union] using image_mono (f := f) hsuv
      · simpa only [image_preimage_inter] using hsu.image f
      · simpa only [image_preimage_inter] using hsv.image f
    · exact ⟨a, has, hau, hinj.mem_set_image.1 hav⟩

Depends on / 依赖: Nonempty, hinj.mem_s, hsu.image, hsv.image, image_mono, image_preimage_eq_of_subset, image_preimage_inter, image_union, isPreconnected_closed_iff, mem_s, replace
-/
theorem IsPreconnected.preimage_of_isClosedMap [TopologicalSpace β] {s : Set β}
    (hs : IsPreconnected s) {f : α -> β} (hinj : Function.Injective f) (hf : IsClosedMap f)
    (hsf : s subseteq range f) : IsPreconnected (f ⁻¹' s) :=
  isPreconnected_closed_iff.2 fun u v hu hv hsuv hsu hsv => by
    replace hsf : f '' f ⁻¹' s = s := image_preimage_eq_of_subset hsf
    obtain ⟨_, has, ⟨a, hau, rfl⟩, hav⟩ : (s inter (f '' u inter f '' v)).Nonempty := by
      refine isPreconnected_closed_iff.1 hs (f '' u) (f '' v) (hf u hu) (hf v hv) ?_ ?_ ?_
      · simpa only [hsf, image_union] using image_mono (f := f) hsuv
      · simpa only [image_preimage_inter] using hsu.image f
      · simpa only [image_preimage_inter] using hsv.image f
    · exact ⟨a, has, hau, hinj.mem_set_image.1 hav⟩

/--
theorem `IsConnected.preimage_of_isOpenMap` / 定理 `IsConnected.preimage_of_isOpenMap`

English:
theorem IsConnected.preimage_of_isOpenMap
  statement: [TopologicalSpace β] {s : Set β} (hs : IsConnected s)
  proof: ⟨hs.nonempty.preimage' hsf, hs.isPreconnected.preimage_of_isOpenMap hinj hf hsf⟩

中文:
定理 是连通.preimage_of_isOpenMap
  结论: [拓扑空间 β] {s : 集合 β} (hs : 是连通 s)
  证明: ⟨hs.nonempty.preimage' hsf, hs.isPreconnected.preimage_of_isOpenMap hinj hf hsf⟩

Depends on / 依赖: hs.isPreconnected.preimage_of_isOpenMap, hs.nonempty.preimage, isPreconnected, nonempty, preimage, preimage_of_isOpenMap
-/
theorem IsConnected.preimage_of_isOpenMap [TopologicalSpace β] {s : Set β} (hs : IsConnected s)
    {f : α -> β} (hinj : Function.Injective f) (hf : IsOpenMap f) (hsf : s subseteq range f) :
    IsConnected (f ⁻¹' s) :=
  ⟨hs.nonempty.preimage' hsf, hs.isPreconnected.preimage_of_isOpenMap hinj hf hsf⟩

/--
theorem `IsConnected.preimage_of_isClosedMap` / 定理 `IsConnected.preimage_of_isClosedMap`

English:
theorem IsConnected.preimage_of_isClosedMap
  statement: [TopologicalSpace β] {s : Set β} (hs : IsConnected s)
  proof: ⟨hs.nonempty.preimage' hsf, hs.isPreconnected.preimage_of_isClosedMap hinj hf hsf⟩

中文:
定理 是连通.preimage_of_isClosedMap
  结论: [拓扑空间 β] {s : 集合 β} (hs : 是连通 s)
  证明: ⟨hs.nonempty.preimage' hsf, hs.isPreconnected.preimage_of_isClosedMap hinj hf hsf⟩

Depends on / 依赖: hs.isPreconnected.preimage_of_isClosedMap, hs.nonempty.preimage, isPreconnected, nonempty, preimage, preimage_of_isClosedMap
-/
theorem IsConnected.preimage_of_isClosedMap [TopologicalSpace β] {s : Set β} (hs : IsConnected s)
    {f : α -> β} (hinj : Function.Injective f) (hf : IsClosedMap f) (hsf : s subseteq range f) :
    IsConnected (f ⁻¹' s) :=
  ⟨hs.nonempty.preimage' hsf, hs.isPreconnected.preimage_of_isClosedMap hinj hf hsf⟩

/--
theorem `IsPreconnected.subset_or_subset` / 定理 `IsPreconnected.subset_or_subset`

English:
theorem IsPreconnected.subset_or_subset
  statement: (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v)
  proof: by
  specialize hs u v hu hv hsuv
  obtain hsu | hsu := (s inter u).eq_empty_or_nonempty
  · exact Or.inr ((Set.disjoint_iff_inter_eq_empty.2 hsu).subset_right_of_subset_union hsuv)
  · replace hs := mt (hs hsu)
    simp_rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty,
      disjoint_iff_inter_eq_empty.1 huv] at hs
    exact Or.inl ((hs s.disjoint_empty).subset_left_of_subset_union hsuv)

中文:
定理 是预连通.subset_or_subset
  结论: (hu : 是开集 u) (hv : 是开集 v) (huv : Disjoint u v)
  证明: by
  specialize hs u v hu hv hsuv
  obtain hsu | hsu := (s inter u).eq_empty_or_nonempty
  · exact Or.inr ((Set.disjoint_iff_inter_eq_empty.2 hsu).subset_right_of_subset_union hsuv)
  · replace hs := mt (hs hsu)
    simp_rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty,
      disjoint_iff_inter_eq_empty.1 huv] at hs
    exact Or.inl ((hs s.disjoint_empty).subset_left_of_subset_union hsuv)

Depends on / 依赖: Or.inl, Or.inr, Set.disjoint_iff_inter_eq_empty, Set.not_nonempty_iff_eq_empty, disjoint_empty, disjoint_iff_inter_eq_empty, eq_empty_or_nonempty, not_nonempty_iff_eq_empty, replace, s.disjoint_empty, simp_rw, specialize, subset_left_of_subset_union, subset_right_of_subset_union
-/
theorem IsPreconnected.subset_or_subset (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v)
    (hsuv : s subseteq u union v) (hs : IsPreconnected s) : s subseteq u ∨ s subseteq v := by
  specialize hs u v hu hv hsuv
  obtain hsu | hsu := (s inter u).eq_empty_or_nonempty
  · exact Or.inr ((Set.disjoint_iff_inter_eq_empty.2 hsu).subset_right_of_subset_union hsuv)
  · replace hs := mt (hs hsu)
    simp_rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty,
      disjoint_iff_inter_eq_empty.1 huv] at hs
    exact Or.inl ((hs s.disjoint_empty).subset_left_of_subset_union hsuv)

section OrderClosedTopology

variable [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] {f : α -> β} {b : β}

/--
lemma `IsPreconnected.mapsTo_Ioi_or_Iio` / 引理 `IsPreconnected.mapsTo_Ioi_or_Iio`

English:
lemma IsPreconnected.mapsTo_Ioi_or_Iio
  statement: (hs : IsPreconnected s) (hf : ContinuousOn f s)
  proof: by
  simpa [mapsTo_iff_image_subset] using
    (hs.image f hf).subset_or_subset isOpen_Ioi isOpen_Iio (by grind) (by grind)

中文:
引理 是预连通.mapsTo_Ioi_or_Iio
  结论: (hs : 是预连通 s) (hf : ContinuousOn f s)
  证明: by
  simpa [mapsTo_iff_image_subset] using
    (hs.image f hf).subset_or_subset isOpen_Ioi isOpen_Iio (by grind) (by grind)

Depends on / 依赖: hs.image, isOpen_Iio, isOpen_Ioi, mapsTo_iff_image_subset, subset_or_subset
-/
lemma IsPreconnected.mapsTo_Ioi_or_Iio (hs : IsPreconnected s) (hf : ContinuousOn f s)
    (hfb : forall x in s, f x != b) : Set.MapsTo f s (Set.Ioi b) ∨ Set.MapsTo f s (Set.Iio b) := by
  simpa [mapsTo_iff_image_subset] using
    (hs.image f hf).subset_or_subset isOpen_Ioi isOpen_Iio (by grind) (by grind)

/--
lemma `IsPreconnected.lt_of_ne` / 引理 `IsPreconnected.lt_of_ne`

English:
lemma IsPreconnected.lt_of_ne
  statement: (hs : IsPreconnected s) (hf : ContinuousOn f s)
  proof: (hs.mapsTo_Ioi_or_Iio hf hfb).resolve_right (not_forall₂_of_exists₂_not (by grind)) hx

中文:
引理 是预连通.lt_of_ne
  结论: (hs : 是预连通 s) (hf : ContinuousOn f s)
  证明: (hs.mapsTo_Ioi_or_Iio hf hfb).resolve_right (not_forall₂_of_exists₂_not (by grind)) hx

Depends on / 依赖: hs.mapsTo_Ioi_or_Iio, mapsTo_Ioi_or_Iio, resolve_right
-/
lemma IsPreconnected.lt_of_ne (hs : IsPreconnected s) (hf : ContinuousOn f s)
    (hfb : forall x in s, f x != b) (hfx : exists x in s, b < f x) {x : α} (hx : x in s) : b < f x :=
  (hs.mapsTo_Ioi_or_Iio hf hfb).resolve_right (not_forall₂_of_exists₂_not (by grind)) hx

/--
lemma `IsPreconnected.gt_of_ne` / 引理 `IsPreconnected.gt_of_ne`

English:
lemma IsPreconnected.gt_of_ne
  statement: (hs : IsPreconnected s) (hf : ContinuousOn f s)
  proof: (hs.mapsTo_Ioi_or_Iio hf hfb).resolve_left (not_forall₂_of_exists₂_not (by grind)) hx

中文:
引理 是预连通.gt_of_ne
  结论: (hs : 是预连通 s) (hf : ContinuousOn f s)
  证明: (hs.mapsTo_Ioi_or_Iio hf hfb).resolve_left (not_forall₂_of_exists₂_not (by grind)) hx

Depends on / 依赖: hs.mapsTo_Ioi_or_Iio, mapsTo_Ioi_or_Iio, resolve_left
-/
lemma IsPreconnected.gt_of_ne (hs : IsPreconnected s) (hf : ContinuousOn f s)
    (hfb : forall x in s, f x != b) (hfx : exists x in s, f x < b) {x : α} (hx : x in s) : f x < b :=
  (hs.mapsTo_Ioi_or_Iio hf hfb).resolve_left (not_forall₂_of_exists₂_not (by grind)) hx

end OrderClosedTopology

/--
theorem `IsPreconnected.subset_left_of_subset_union` / 定理 `IsPreconnected.subset_left_of_subset_union`

English:
theorem IsPreconnected.subset_left_of_subset_union
  statement: (hu : IsOpen u) (hv : IsOpen v)
  proof: Disjoint.subset_left_of_subset_union hsuv
    (by
      by_contra hsv
      rw [not_disjoint_iff_nonempty_inter] at hsv
      obtain ⟨x, _, hx⟩ := hs u v hu hv hsuv hsu hsv
      exact Set.disjoint_iff.1 huv hx)

中文:
定理 是预连通.subset_left_of_subset_union
  结论: (hu : 是开集 u) (hv : 是开集 v)
  证明: Disjoint.subset_left_of_subset_union hsuv
    (by
      by_contra hsv
      rw [not_disjoint_iff_nonempty_inter] at hsv
      obtain ⟨x, _, hx⟩ := hs u v hu hv hsuv hsu hsv
      exact Set.disjoint_iff.1 huv hx)

Depends on / 依赖: Disjoint, Disjoint.subset_left_of_subset_union, Set.disjoint_iff, disjoint_iff, not_disjoint_iff_nonempty_inter, subset_left_of_subset_union
-/
theorem IsPreconnected.subset_left_of_subset_union (hu : IsOpen u) (hv : IsOpen v)
    (huv : Disjoint u v) (hsuv : s subseteq u union v) (hsu : (s inter u).Nonempty) (hs : IsPreconnected s) :
    s subseteq u :=
  Disjoint.subset_left_of_subset_union hsuv
    (by
      by_contra hsv
      rw [not_disjoint_iff_nonempty_inter] at hsv
      obtain ⟨x, _, hx⟩ := hs u v hu hv hsuv hsu hsv
      exact Set.disjoint_iff.1 huv hx)

/--
theorem `IsPreconnected.subset_right_of_subset_union` / 定理 `IsPreconnected.subset_right_of_subset_union`

English:
theorem IsPreconnected.subset_right_of_subset_union
  statement: (hu : IsOpen u) (hv : IsOpen v)
  proof: hs.subset_left_of_subset_union hv hu huv.symm (union_comm u v ▸ hsuv) hsv

中文:
定理 是预连通.subset_right_of_subset_union
  结论: (hu : 是开集 u) (hv : 是开集 v)
  证明: hs.subset_left_of_subset_union hv hu huv.symm (union_comm u v ▸ hsuv) hsv

Depends on / 依赖: hs.subset_left_of_subset_union, huv.symm, subset_left_of_subset_union, union_comm
-/
theorem IsPreconnected.subset_right_of_subset_union (hu : IsOpen u) (hv : IsOpen v)
    (huv : Disjoint u v) (hsuv : s subseteq u union v) (hsv : (s inter v).Nonempty) (hs : IsPreconnected s) :
    s subseteq v :=
  hs.subset_left_of_subset_union hv hu huv.symm (union_comm u v ▸ hsuv) hsv

/--
theorem `IsPreconnected.subset_of_closure_inter_subset` / 定理 `IsPreconnected.subset_of_closure_inter_subset`

English:
theorem IsPreconnected.subset_of_closure_inter_subset
  statement: (hs : IsPreconnected s) (hu : IsOpen u)
  proof: by
  have A : s subseteq u union (closure u)ᶜ := by
    intro x hx
    by_cases xu : x in u
    · exact Or.inl xu
    · right
      intro h'x
      exact xu (h (mem_inter h'x hx))
  apply hs.subset_left_of_subset_union hu isClosed_closure.isOpen_compl _ A h'u
  exact disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)

中文:
定理 是预连通.subset_of_closure_inter_subset
  结论: (hs : 是预连通 s) (hu : 是开集 u)
  证明: by
  have A : s subseteq u union (closure u)ᶜ := by
    intro x hx
    by_cases xu : x in u
    · exact Or.inl xu
    · right
      intro h'x
      exact xu (h (mem_inter h'x hx))
  apply hs.subset_left_of_subset_union hu isClosed_closure.isOpen_compl _ A h'u
  exact disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)

Depends on / 依赖: Or.inl, closure, compl_subset_compl, disjoint_compl_right, disjoint_compl_right.mono_right, hs.subset_left_of_subset_union, isClosed_closure, isClosed_closure.isOpen_compl, isOpen_compl, mem_inter, mono_right, subset_closure, subset_left_of_subset_union, subseteq
-/
theorem IsPreconnected.subset_of_closure_inter_subset (hs : IsPreconnected s) (hu : IsOpen u)
    (h'u : (s inter u).Nonempty) (h : closure u inter s subseteq u) : s subseteq u := by
  have A : s subseteq u union (closure u)ᶜ := by
    intro x hx
    by_cases xu : x in u
    · exact Or.inl xu
    · right
      intro h'x
      exact xu (h (mem_inter h'x hx))
  apply hs.subset_left_of_subset_union hu isClosed_closure.isOpen_compl _ A h'u
  exact disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)

/--
theorem `IsPreconnected.prod` / 定理 `IsPreconnected.prod`

English:
theorem IsPreconnected.prod
  statement: [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsPreconnected s)
  proof: by
  apply isPreconnected_of_forall_pair
  rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩
  refine ⟨Prod.mk a₁ '' t union flip Prod.mk b₂ '' s, ?_, .inl ⟨b₁, hb₁, rfl⟩, .inr ⟨a₂, ha₂, rfl⟩, ?_⟩
  · rintro _ (⟨y, hy, rfl⟩ | ⟨x, hx, rfl⟩)
    exacts [⟨ha₁, hy⟩, ⟨hx, hb₂⟩]
  · exact (ht.image _ (by fun_prop)).union (a₁, b₂) ⟨b₂, hb₂, rfl⟩
      ⟨a₁, ha₁, rfl⟩ (hs.image _ (Continuous.prodMk_left _).continuousOn)

中文:
定理 是预连通.乘积
  结论: [拓扑空间 β] {s : 集合 α} {t : 集合 β} (hs : 是预连通 s)
  证明: by
  apply isPreconnected_of_forall_pair
  rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩
  refine ⟨Prod.mk a₁ '' t union flip Prod.mk b₂ '' s, ?_, .inl ⟨b₁, hb₁, rfl⟩, .inr ⟨a₂, ha₂, rfl⟩, ?_⟩
  · rintro _ (⟨y, hy, rfl⟩ | ⟨x, hx, rfl⟩)
    exacts [⟨ha₁, hy⟩, ⟨hx, hb₂⟩]
  · exact (ht.image _ (by fun_prop)).union (a₁, b₂) ⟨b₂, hb₂, rfl⟩
      ⟨a₁, ha₁, rfl⟩ (hs.image _ (Continuous.prodMk_left _).continuousOn)
-/
theorem IsPreconnected.prod [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsPreconnected s)
    (ht : IsPreconnected t) : IsPreconnected (s ×ˢ t) := by
  apply isPreconnected_of_forall_pair
  rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩
  refine ⟨Prod.mk a₁ '' t union flip Prod.mk b₂ '' s, ?_, .inl ⟨b₁, hb₁, rfl⟩, .inr ⟨a₂, ha₂, rfl⟩, ?_⟩
  · rintro _ (⟨y, hy, rfl⟩ | ⟨x, hx, rfl⟩)
    exacts [⟨ha₁, hy⟩, ⟨hx, hb₂⟩]
  · exact (ht.image _ (by fun_prop)).union (a₁, b₂) ⟨b₂, hb₂, rfl⟩
      ⟨a₁, ha₁, rfl⟩ (hs.image _ (Continuous.prodMk_left _).continuousOn)

/--
theorem `IsConnected.prod` / 定理 `IsConnected.prod`

English:
theorem IsConnected.prod
  statement: [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsConnected s)
  proof: ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩

中文:
定理 是连通.乘积
  结论: [拓扑空间 β] {s : 集合 α} {t : 集合 β} (hs : 是连通 s)
  证明: ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩
-/
theorem IsConnected.prod [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsConnected s)
    (ht : IsConnected t) : IsConnected (s ×ˢ t) :=
  ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩

/--
theorem `isPreconnected_univ_pi` / 定理 `isPreconnected_univ_pi`

English:
theorem isPreconnected_univ_pi
  statement: [forall i, TopologicalSpace (X i)] {s : forall i, Set (X i)}
  proof: by
  rintro u v uo vo hsuv ⟨f, hfs, hfu⟩ ⟨g, hgs, hgv⟩
  classical
  rcases exists_finset_piecewise_mem_of_mem_nhds (uo.mem_nhds hfu) g with ⟨I, hI⟩
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨g, hgs, ⟨?_, hgv⟩⟩
    simpa using hI
  | insert i I _ ihI =>
    rw [Finset.piecewise_insert] at hI
    have := I.piecewise_mem_set_pi hfs hgs
    refine (hsuv this).elim ihI fun h => ?_
    set S := update (I.piecewise f g) i '' s i
    have hsub : S subseteq pi univ s := by
      refine image_subset_iff.2 fun z hz => ?_
      rwa [update_preimage_univ_pi]
      exact fun j _ => this j trivial
    have hconn : IsPreconnected S :=
      (hs i).image _ (continuous_const.update i continuous_id).continuousOn
    have hSu : (S inter u).Nonempty := ⟨_, mem_image_of_mem _ (hfs _ trivial), hI⟩
    have hSv : (S inter v).Nonempty := ⟨_, ⟨_, this _ trivial, update_eq_self _ _⟩, h⟩
    refine (hconn u v uo vo (hsub.trans hsuv) hSu hSv).mono ?_
    exact inter_subset_inter_left _ hsub

@[simp]

中文:
定理 isPreconnected_univ_pi
  结论: [对任意 i, 拓扑空间 (X i)] {s : 对任意 i, 集合 (X i)}
  证明: by
  rintro u v uo vo hsuv ⟨f, hfs, hfu⟩ ⟨g, hgs, hgv⟩
  classical
  rcases exists_finset_piecewise_mem_of_mem_nhds (uo.mem_nhds hfu) g with ⟨I, hI⟩
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨g, hgs, ⟨?_, hgv⟩⟩
    simpa using hI
  | insert i I _ ihI =>
    rw [Finset.piecewise_insert] at hI
    have := I.piecewise_mem_set_pi hfs hgs
    refine (hsuv this).elim ihI fun h => ?_
    set S := update (I.piecewise f g) i '' s i
    have hsub : S subseteq pi univ s := by
      refine image_subset_iff.2 fun z hz => ?_
      rwa [update_preimage_univ_pi]
      exact fun j _ => this j trivial
    have hconn : IsPreconnected S :=
      (hs i).image _ (continuous_const.update i continuous_id).continuousOn
    have hSu : (S inter u).Nonempty := ⟨_, mem_image_of_mem _ (hfs _ trivial), hI⟩
    have hSv : (S inter v).Nonempty := ⟨_, ⟨_, this _ trivial, update_eq_self _ _⟩, h⟩
    refine (hconn u v uo vo (hsub.trans hsuv) hSu hSv).mono ?_
    exact inter_subset_inter_left _ hsub

@[simp]

Depends on / 依赖: Finset, Finset.induction_on, Finset.piecewise_insert, I.piecewise, I.piecewise_mem_set_pi, classical, exists_finset_piecewise_mem_of_mem_nhds, image_subset_iff, induction_on, insert, mem_nhds, piecewise, piecewise_insert, piecewise_mem_set_pi, subseteq, uo.mem_nhds, update
-/
theorem isPreconnected_univ_pi [forall i, TopologicalSpace (X i)] {s : forall i, Set (X i)}
    (hs : forall i, IsPreconnected (s i)) : IsPreconnected (pi univ s) := by
  rintro u v uo vo hsuv ⟨f, hfs, hfu⟩ ⟨g, hgs, hgv⟩
  classical
  rcases exists_finset_piecewise_mem_of_mem_nhds (uo.mem_nhds hfu) g with ⟨I, hI⟩
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨g, hgs, ⟨?_, hgv⟩⟩
    simpa using hI
  | insert i I _ ihI =>
    rw [Finset.piecewise_insert] at hI
    have := I.piecewise_mem_set_pi hfs hgs
    refine (hsuv this).elim ihI fun h => ?_
    set S := update (I.piecewise f g) i '' s i
    have hsub : S subseteq pi univ s := by
      refine image_subset_iff.2 fun z hz => ?_
      rwa [update_preimage_univ_pi]
      exact fun j _ => this j trivial
    have hconn : IsPreconnected S :=
      (hs i).image _ (continuous_const.update i continuous_id).continuousOn
    have hSu : (S inter u).Nonempty := ⟨_, mem_image_of_mem _ (hfs _ trivial), hI⟩
    have hSv : (S inter v).Nonempty := ⟨_, ⟨_, this _ trivial, update_eq_self _ _⟩, h⟩
    refine (hconn u v uo vo (hsub.trans hsuv) hSu hSv).mono ?_
    exact inter_subset_inter_left _ hsub

@[simp]
/--
theorem `isConnected_univ_pi` / 定理 `isConnected_univ_pi`

English:
theorem isConnected_univ_pi
  given: [forall i, TopologicalSpace (X i)] {s : forall i, Set (X i)}
  proof: by
  simp only [IsConnected, ← univ_pi_nonempty_iff, forall_and, and_congr_right_iff]
  refine fun hne => ⟨fun hc i => ?_, isPreconnected_univ_pi⟩
  rw [← eval_image_univ_pi hne]
  exact hc.image _ (continuous_apply _).continuousOn

中文:
定理 isConnected_univ_pi
  条件: [对任意 i, 拓扑空间 (X i)] {s : 对任意 i, 集合 (X i)}
  证明: by
  simp only [IsConnected, ← univ_pi_nonempty_iff, forall_and, and_congr_right_iff]
  refine fun hne => ⟨fun hc i => ?_, isPreconnected_univ_pi⟩
  rw [← eval_image_univ_pi hne]
  exact hc.image _ (continuous_apply _).continuousOn

Depends on / 依赖: IsConnected, and_congr_right_iff, continuousOn, continuous_apply, eval_image_univ_pi, forall_and, hc.image, isPreconnected_univ_pi, univ_pi_nonempty_iff
-/
theorem isConnected_univ_pi [forall i, TopologicalSpace (X i)] {s : forall i, Set (X i)} :
    IsConnected (pi univ s) ↔ forall i, IsConnected (s i) := by
  simp only [IsConnected, ← univ_pi_nonempty_iff, forall_and, and_congr_right_iff]
  refine fun hne => ⟨fun hc i => ?_, isPreconnected_univ_pi⟩
  rw [← eval_image_univ_pi hne]
  exact hc.image _ (continuous_apply _).continuousOn

/--
Definition of `connectedComponent` / `connectedComponent` 的定义

English:
definition connectedComponent
  signature: (x : α)
  body: ⋃₀ { s : Set α | IsPreconnected s ∧ x in s }

中文:
定义 connectedComponent
  签名: (x : α)
  定义体: ⋃₀ { s : Set α | IsPreconnected s ∧ x in s }

Depends on / 依赖: IsPreconnected
-/
def connectedComponent (x : α) : Set α :=
  ⋃₀ { s : Set α | IsPreconnected s ∧ x in s }

open scoped Classical in
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `connectedComponentIn` / `connectedComponentIn` 的定义

English:
definition connectedComponentIn
  signature: (F : Set α) (x : α)
  body: if h : x in F then (↑) '' connectedComponent (⟨x, h⟩ : F) else ∅

中文:
定义 connectedComponentIn
  签名: (F : 集合 α) (x : α)
  定义体: if h : x in F then (↑) '' connectedComponent (⟨x, h⟩ : F) else ∅

Depends on / 依赖: connectedComponent
-/
noncomputable def connectedComponentIn (F : Set α) (x : α) : Set α :=
  if h : x in F then (↑) '' connectedComponent (⟨x, h⟩ : F) else ∅

/--
theorem `connectedComponentIn_eq_image` / 定理 `connectedComponentIn_eq_image`

English:
theorem connectedComponentIn_eq_image
  given: {F : Set α} {x : α} (h : x in F)
  proof: dif_pos h

中文:
定理 connectedComponentIn_eq_image
  条件: {F : 集合 α} {x : α} (h : x in F)
  证明: dif_pos h

Depends on / 依赖: dif_pos
-/
theorem connectedComponentIn_eq_image {F : Set α} {x : α} (h : x in F) :
    connectedComponentIn F x = (↑) '' connectedComponent (⟨x, h⟩ : F) :=
  dif_pos h

/--
theorem `connectedComponentIn_eq_empty` / 定理 `connectedComponentIn_eq_empty`

English:
theorem connectedComponentIn_eq_empty
  given: {F : Set α} {x : α} (h : x ∉ F)
  proof: dif_neg h

中文:
定理 connectedComponentIn_eq_empty
  条件: {F : 集合 α} {x : α} (h : x ∉ F)
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
theorem connectedComponentIn_eq_empty {F : Set α} {x : α} (h : x ∉ F) :
    connectedComponentIn F x = ∅ :=
  dif_neg h

/--
theorem `mem_connectedComponent` / 定理 `mem_connectedComponent`

English:
theorem mem_connectedComponent
  given: {x : α}
  statement: x in connectedComponent x
  proof: mem_sUnion_of_mem (mem_singleton x) ⟨isPreconnected_singleton, mem_singleton x⟩

中文:
定理 mem_connectedComponent
  条件: {x : α}
  结论: x in connectedComponent x
  证明: mem_sUnion_of_mem (mem_singleton x) ⟨isPreconnected_singleton, mem_singleton x⟩

Depends on / 依赖: isPreconnected_singleton, mem_sUnion_of_mem, mem_singleton
-/
theorem mem_connectedComponent {x : α} : x in connectedComponent x :=
  mem_sUnion_of_mem (mem_singleton x) ⟨isPreconnected_singleton, mem_singleton x⟩

/--
theorem `mem_connectedComponentIn` / 定理 `mem_connectedComponentIn`

English:
theorem mem_connectedComponentIn
  given: {x : α} {F : Set α} (hx : x in F)
  proof: by
  simp [connectedComponentIn_eq_image hx, mem_connectedComponent, hx]

中文:
定理 mem_connectedComponentIn
  条件: {x : α} {F : 集合 α} (hx : x in F)
  证明: by
  simp [connectedComponentIn_eq_image hx, mem_connectedComponent, hx]

Depends on / 依赖: connectedComponentIn_eq_image, mem_connectedComponent
-/
theorem mem_connectedComponentIn {x : α} {F : Set α} (hx : x in F) :
    x in connectedComponentIn F x := by
  simp [connectedComponentIn_eq_image hx, mem_connectedComponent, hx]

/--
theorem `connectedComponent_nonempty` / 定理 `connectedComponent_nonempty`

English:
theorem connectedComponent_nonempty
  given: {x : α}
  statement: (connectedComponent x).Nonempty
  proof: ⟨x, mem_connectedComponent⟩

中文:
定理 connectedComponent_nonempty
  条件: {x : α}
  结论: (connectedComponent x).非空
  证明: ⟨x, mem_connectedComponent⟩

Depends on / 依赖: mem_connectedComponent
-/
theorem connectedComponent_nonempty {x : α} : (connectedComponent x).Nonempty :=
  ⟨x, mem_connectedComponent⟩

/--
theorem `connectedComponentIn_nonempty_iff` / 定理 `connectedComponentIn_nonempty_iff`

English:
theorem connectedComponentIn_nonempty_iff
  given: {x : α} {F : Set α}
  proof: by
  rw [connectedComponentIn]
  split_ifs <;> simp [connectedComponent_nonempty, *]

中文:
定理 connectedComponentIn_nonempty_iff
  条件: {x : α} {F : 集合 α}
  证明: by
  rw [connectedComponentIn]
  split_ifs <;> simp [connectedComponent_nonempty, *]

Depends on / 依赖: connectedComponentIn, connectedComponent_nonempty, split_ifs
-/
theorem connectedComponentIn_nonempty_iff {x : α} {F : Set α} :
    (connectedComponentIn F x).Nonempty ↔ x in F := by
  rw [connectedComponentIn]
  split_ifs <;> simp [connectedComponent_nonempty, *]

/--
theorem `connectedComponentIn_subset` / 定理 `connectedComponentIn_subset`

English:
theorem connectedComponentIn_subset
  given: (F : Set α) (x : α)
  statement: connectedComponentIn F x subseteq F
  proof: by
  rw [connectedComponentIn]
  split_ifs <;> simp

中文:
定理 connectedComponentIn_subset
  条件: (F : 集合 α) (x : α)
  结论: connectedComponentIn F x subseteq F
  证明: by
  rw [connectedComponentIn]
  split_ifs <;> simp

Depends on / 依赖: connectedComponentIn, split_ifs
-/
theorem connectedComponentIn_subset (F : Set α) (x : α) : connectedComponentIn F x subseteq F := by
  rw [connectedComponentIn]
  split_ifs <;> simp

/--
theorem `isPreconnected_connectedComponent` / 定理 `isPreconnected_connectedComponent`

English:
theorem isPreconnected_connectedComponent
  given: {x : α}
  statement: IsPreconnected (connectedComponent x)
  proof: isPreconnected_sUnion x _ (fun _ => And.right) fun _ => And.left

中文:
定理 isPreconnected_connectedComponent
  条件: {x : α}
  结论: 是预连通 (connectedComponent x)
  证明: isPreconnected_sUnion x _ (fun _ => And.right) fun _ => And.left

Depends on / 依赖: And.left, And.right, isPreconnected_sUnion
-/
theorem isPreconnected_connectedComponent {x : α} : IsPreconnected (connectedComponent x) :=
  isPreconnected_sUnion x _ (fun _ => And.right) fun _ => And.left

/--
theorem `isPreconnected_connectedComponentIn` / 定理 `isPreconnected_connectedComponentIn`

English:
theorem isPreconnected_connectedComponentIn
  given: {x : α} {F : Set α}
  proof: by
  rw [connectedComponentIn]; split_ifs
  · exact IsInducing.subtypeVal.isPreconnected_image.mpr isPreconnected_connectedComponent
  · exact isPreconnected_empty

中文:
定理 isPreconnected_connectedComponentIn
  条件: {x : α} {F : 集合 α}
  证明: by
  rw [connectedComponentIn]; split_ifs
  · exact IsInducing.subtypeVal.isPreconnected_image.mpr isPreconnected_connectedComponent
  · exact isPreconnected_empty

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.isPreconnected_image.mpr, connectedComponentIn, isPreconnected_connectedComponent, isPreconnected_empty, isPreconnected_image, split_ifs, subtypeVal
-/
theorem isPreconnected_connectedComponentIn {x : α} {F : Set α} :
    IsPreconnected (connectedComponentIn F x) := by
  rw [connectedComponentIn]; split_ifs
  · exact IsInducing.subtypeVal.isPreconnected_image.mpr isPreconnected_connectedComponent
  · exact isPreconnected_empty

/--
theorem `isConnected_connectedComponent` / 定理 `isConnected_connectedComponent`

English:
theorem isConnected_connectedComponent
  given: {x : α}
  statement: IsConnected (connectedComponent x)
  proof: ⟨⟨x, mem_connectedComponent⟩, isPreconnected_connectedComponent⟩

中文:
定理 isConnected_connectedComponent
  条件: {x : α}
  结论: 是连通 (connectedComponent x)
  证明: ⟨⟨x, mem_connectedComponent⟩, isPreconnected_connectedComponent⟩

Depends on / 依赖: isPreconnected_connectedComponent, mem_connectedComponent
-/
theorem isConnected_connectedComponent {x : α} : IsConnected (connectedComponent x) :=
  ⟨⟨x, mem_connectedComponent⟩, isPreconnected_connectedComponent⟩

/--
theorem `isConnected_connectedComponentIn_iff` / 定理 `isConnected_connectedComponentIn_iff`

English:
theorem isConnected_connectedComponentIn_iff
  given: {x : α} {F : Set α}
  proof: by
  simp_rw [← connectedComponentIn_nonempty_iff, IsConnected, isPreconnected_connectedComponentIn,
    and_true]

中文:
定理 isConnected_connectedComponentIn_iff
  条件: {x : α} {F : 集合 α}
  证明: by
  simp_rw [← connectedComponentIn_nonempty_iff, IsConnected, isPreconnected_connectedComponentIn,
    and_true]

Depends on / 依赖: IsConnected, and_true, connectedComponentIn_nonempty_iff, isPreconnected_connectedComponentIn, simp_rw
-/
theorem isConnected_connectedComponentIn_iff {x : α} {F : Set α} :
    IsConnected (connectedComponentIn F x) ↔ x in F := by
  simp_rw [← connectedComponentIn_nonempty_iff, IsConnected, isPreconnected_connectedComponentIn,
    and_true]

/--
theorem `IsPreconnected.subset_connectedComponent` / 定理 `IsPreconnected.subset_connectedComponent`

English:
theorem IsPreconnected.subset_connectedComponent
  statement: {x : α} {s : Set α} (H1 : IsPreconnected s)
  proof: fun _z hz => mem_sUnion_of_mem hz ⟨H1, H2⟩

中文:
定理 是预连通.subset_connectedComponent
  结论: {x : α} {s : 集合 α} (H1 : 是预连通 s)
  证明: fun _z hz => mem_sUnion_of_mem hz ⟨H1, H2⟩

Depends on / 依赖: mem_sUnion_of_mem
-/
theorem IsPreconnected.subset_connectedComponent {x : α} {s : Set α} (H1 : IsPreconnected s)
    (H2 : x in s) : s subseteq connectedComponent x := fun _z hz => mem_sUnion_of_mem hz ⟨H1, H2⟩

/--
theorem `IsPreconnected.subset_connectedComponentIn` / 定理 `IsPreconnected.subset_connectedComponentIn`

English:
theorem IsPreconnected.subset_connectedComponentIn
  statement: {x : α} {F : Set α} (hs : IsPreconnected s)
  proof: by
  have : IsPreconnected (((↑) : F -> α) ⁻¹' s) := by
    refine IsInducing.subtypeVal.isPreconnected_image.mp ?_
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hsF]
  have h2xs : (⟨x, hsF hxs⟩ : F) in (↑) ⁻¹' s := by
    rw [mem_preimage]
    exact hxs
  have := this.subset_connectedComponent h2xs
  rw [connectedComponentIn_eq_image (hsF hxs)]
  refine Subset.trans ?_ (image_mono this)
  rw [Subtype.image_preimage_coe]; rw [inter_eq_right.mpr hsF]

中文:
定理 是预连通.subset_connectedComponentIn
  结论: {x : α} {F : 集合 α} (hs : 是预连通 s)
  证明: by
  have : IsPreconnected (((↑) : F -> α) ⁻¹' s) := by
    refine IsInducing.subtypeVal.isPreconnected_image.mp ?_
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hsF]
  have h2xs : (⟨x, hsF hxs⟩ : F) in (↑) ⁻¹' s := by
    rw [mem_preimage]
    exact hxs
  have := this.subset_connectedComponent h2xs
  rw [connectedComponentIn_eq_image (hsF hxs)]
  refine Subset.trans ?_ (image_mono this)
  rw [Subtype.image_preimage_coe]; rw [inter_eq_right.mpr hsF]

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.isPreconnected_image.mp, IsPreconnected, Subset, Subset.trans, Subtype, Subtype.image_preimage_coe, connectedComponentIn_eq_image, image_mono, image_preimage_coe, inter_eq_right, inter_eq_right.mpr, isPreconnected_image, mem_preimage, subset_connectedComponent, subtypeVal, this.subset_connectedComponent
-/
theorem IsPreconnected.subset_connectedComponentIn {x : α} {F : Set α} (hs : IsPreconnected s)
    (hxs : x in s) (hsF : s subseteq F) : s subseteq connectedComponentIn F x := by
  have : IsPreconnected (((↑) : F -> α) ⁻¹' s) := by
    refine IsInducing.subtypeVal.isPreconnected_image.mp ?_
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hsF]
  have h2xs : (⟨x, hsF hxs⟩ : F) in (↑) ⁻¹' s := by
    rw [mem_preimage]
    exact hxs
  have := this.subset_connectedComponent h2xs
  rw [connectedComponentIn_eq_image (hsF hxs)]
  refine Subset.trans ?_ (image_mono this)
  rw [Subtype.image_preimage_coe]; rw [inter_eq_right.mpr hsF]

/--
theorem `IsConnected.subset_connectedComponent` / 定理 `IsConnected.subset_connectedComponent`

English:
theorem IsConnected.subset_connectedComponent
  statement: {x : α} {s : Set α} (H1 : IsConnected s)
  proof: H1.2.subset_connectedComponent H2

中文:
定理 是连通.subset_connectedComponent
  结论: {x : α} {s : 集合 α} (H1 : 是连通 s)
  证明: H1.2.subset_connectedComponent H2

Depends on / 依赖: subset_connectedComponent
-/
theorem IsConnected.subset_connectedComponent {x : α} {s : Set α} (H1 : IsConnected s)
    (H2 : x in s) : s subseteq connectedComponent x :=
  H1.2.subset_connectedComponent H2

/--
theorem `IsPreconnected.connectedComponentIn` / 定理 `IsPreconnected.connectedComponentIn`

English:
theorem IsPreconnected.connectedComponentIn
  statement: {x : α} {F : Set α} (h : IsPreconnected F)
  proof: (connectedComponentIn_subset F x).antisymm (h.subset_connectedComponentIn hx subset_rfl)

中文:
定理 是预连通.connectedComponentIn
  结论: {x : α} {F : 集合 α} (h : 是预连通 F)
  证明: (connectedComponentIn_subset F x).antisymm (h.subset_connectedComponentIn hx subset_rfl)

Depends on / 依赖: antisymm, connectedComponentIn_subset, h.subset_connectedComponentIn, subset_connectedComponentIn, subset_rfl
-/
theorem IsPreconnected.connectedComponentIn {x : α} {F : Set α} (h : IsPreconnected F)
    (hx : x in F) : connectedComponentIn F x = F :=
  (connectedComponentIn_subset F x).antisymm (h.subset_connectedComponentIn hx subset_rfl)

/--
theorem `connectedComponent_eq` / 定理 `connectedComponent_eq`

English:
theorem connectedComponent_eq
  given: {x y : α} (h : y in connectedComponent x)
  proof: eq_of_subset_of_subset (isConnected_connectedComponent.subset_connectedComponent h)
    (isConnected_connectedComponent.subset_connectedComponent
      (Set.mem_of_mem_of_subset mem_connectedComponent
        (isConnected_connectedComponent.subset_connectedComponent h)))

中文:
定理 connectedComponent_eq
  条件: {x y : α} (h : y in connectedComponent x)
  证明: eq_of_subset_of_subset (isConnected_connectedComponent.subset_connectedComponent h)
    (isConnected_connectedComponent.subset_connectedComponent
      (Set.mem_of_mem_of_subset mem_connectedComponent
        (isConnected_connectedComponent.subset_connectedComponent h)))

Depends on / 依赖: Set.mem_of_mem_of_subset, eq_of_subset_of_subset, isConnected_connectedComponent, isConnected_connectedComponent.subset_connectedComponent, mem_connectedComponent, mem_of_mem_of_subset, subset_connectedComponent
-/
theorem connectedComponent_eq {x y : α} (h : y in connectedComponent x) :
    connectedComponent x = connectedComponent y :=
  eq_of_subset_of_subset (isConnected_connectedComponent.subset_connectedComponent h)
    (isConnected_connectedComponent.subset_connectedComponent
      (Set.mem_of_mem_of_subset mem_connectedComponent
        (isConnected_connectedComponent.subset_connectedComponent h)))

/--
theorem `connectedComponent_eq_iff_mem` / 定理 `connectedComponent_eq_iff_mem`

English:
theorem connectedComponent_eq_iff_mem
  given: {x y : α}
  proof: ⟨fun h => h ▸ mem_connectedComponent, fun h => (connectedComponent_eq h).symm⟩

中文:
定理 connectedComponent_eq_iff_mem
  条件: {x y : α}
  证明: ⟨fun h => h ▸ mem_connectedComponent, fun h => (connectedComponent_eq h).symm⟩

Depends on / 依赖: connectedComponent_eq, mem_connectedComponent
-/
theorem connectedComponent_eq_iff_mem {x y : α} :
    connectedComponent x = connectedComponent y ↔ x in connectedComponent y :=
  ⟨fun h => h ▸ mem_connectedComponent, fun h => (connectedComponent_eq h).symm⟩

/--
theorem `connectedComponentIn_eq` / 定理 `connectedComponentIn_eq`

English:
theorem connectedComponentIn_eq
  given: {x y : α} {F : Set α} (h : y in connectedComponentIn F x)
  proof: by
  have hx : x in F := connectedComponentIn_nonempty_iff.mp ⟨y, h⟩
  simp_rw [connectedComponentIn_eq_image hx] at h ⊢
  obtain ⟨⟨y, hy⟩, h2y, rfl⟩ := h
  simp_rw [connectedComponentIn_eq_image hy, connectedComponent_eq h2y]

中文:
定理 connectedComponentIn_eq
  条件: {x y : α} {F : 集合 α} (h : y in connectedComponentIn F x)
  证明: by
  have hx : x in F := connectedComponentIn_nonempty_iff.mp ⟨y, h⟩
  simp_rw [connectedComponentIn_eq_image hx] at h ⊢
  obtain ⟨⟨y, hy⟩, h2y, rfl⟩ := h
  simp_rw [connectedComponentIn_eq_image hy, connectedComponent_eq h2y]

Depends on / 依赖: connectedComponentIn_eq_image, connectedComponentIn_nonempty_iff, connectedComponentIn_nonempty_iff.mp, connectedComponent_eq, simp_rw
-/
theorem connectedComponentIn_eq {x y : α} {F : Set α} (h : y in connectedComponentIn F x) :
    connectedComponentIn F x = connectedComponentIn F y := by
  have hx : x in F := connectedComponentIn_nonempty_iff.mp ⟨y, h⟩
  simp_rw [connectedComponentIn_eq_image hx] at h ⊢
  obtain ⟨⟨y, hy⟩, h2y, rfl⟩ := h
  simp_rw [connectedComponentIn_eq_image hy, connectedComponent_eq h2y]

/--
theorem `connectedComponentIn_univ` / 定理 `connectedComponentIn_univ`

English:
theorem connectedComponentIn_univ
  given: (x : α)
  statement: connectedComponentIn univ x = connectedComponent x
  proof: subset_antisymm
    (isPreconnected_connectedComponentIn.subset_connectedComponent <|
      mem_connectedComponentIn trivial)
    (isPreconnected_connectedComponent.subset_connectedComponentIn mem_connectedComponent <|
      subset_univ _)

中文:
定理 connectedComponentIn_univ
  条件: (x : α)
  结论: connectedComponentIn univ x = connectedComponent x
  证明: subset_antisymm
    (isPreconnected_connectedComponentIn.subset_connectedComponent <|
      mem_connectedComponentIn trivial)
    (isPreconnected_connectedComponent.subset_connectedComponentIn mem_connectedComponent <|
      subset_univ _)

Depends on / 依赖: isPreconnected_connectedComponent, isPreconnected_connectedComponent.subset_connectedComponentIn, isPreconnected_connectedComponentIn, isPreconnected_connectedComponentIn.subset_connectedComponent, mem_connectedComponent, mem_connectedComponentIn, subset_antisymm, subset_connectedComponent, subset_connectedComponentIn, subset_univ
-/
theorem connectedComponentIn_univ (x : α) : connectedComponentIn univ x = connectedComponent x :=
  subset_antisymm
    (isPreconnected_connectedComponentIn.subset_connectedComponent <|
      mem_connectedComponentIn trivial)
    (isPreconnected_connectedComponent.subset_connectedComponentIn mem_connectedComponent <|
      subset_univ _)

/--
theorem `connectedComponent_disjoint` / 定理 `connectedComponent_disjoint`

English:
theorem connectedComponent_disjoint
  given: {x y : α} (h : connectedComponent x != connectedComponent y)
  proof: Set.disjoint_left.2 fun _ h1 h2 =>
    h ((connectedComponent_eq h1).trans (connectedComponent_eq h2).symm)

中文:
定理 connectedComponent_disjoint
  条件: {x y : α} (h : connectedComponent x != connectedComponent y)
  证明: Set.disjoint_left.2 fun _ h1 h2 =>
    h ((connectedComponent_eq h1).trans (connectedComponent_eq h2).symm)

Depends on / 依赖: Set.disjoint_left, connectedComponent_eq, disjoint_left
-/
theorem connectedComponent_disjoint {x y : α} (h : connectedComponent x != connectedComponent y) :
    Disjoint (connectedComponent x) (connectedComponent y) :=
  Set.disjoint_left.2 fun _ h1 h2 =>
    h ((connectedComponent_eq h1).trans (connectedComponent_eq h2).symm)

/--
theorem `isClosed_connectedComponent` / 定理 `isClosed_connectedComponent`

English:
theorem isClosed_connectedComponent
  given: {x : α}
  statement: IsClosed (connectedComponent x)
  proof: closure_subset_iff_isClosed.1
isConnected_connectedComponent.closure.subset_connectedComponent
      subset_closure mem_connectedComponent

中文:
定理 isClosed_connectedComponent
  条件: {x : α}
  结论: 是闭集 (connectedComponent x)
  证明: closure_subset_iff_isClosed.1
isConnected_connectedComponent.closure.subset_connectedComponent
      subset_closure mem_connectedComponent

Depends on / 依赖: closure, closure_subset_iff_isClosed, isConnected_connectedComponent, isConnected_connectedComponent.closure.subset_connectedComponent, mem_connectedComponent, subset_closure, subset_connectedComponent
-/
theorem isClosed_connectedComponent {x : α} : IsClosed (connectedComponent x) :=
closure_subset_iff_isClosed.1
isConnected_connectedComponent.closure.subset_connectedComponent
      subset_closure mem_connectedComponent

/--
theorem `Continuous.image_connectedComponent_subset` / 定理 `Continuous.image_connectedComponent_subset`

English:
theorem Continuous.image_connectedComponent_subset
  statement: [TopologicalSpace β] {f : α -> β}
  proof: (isConnected_connectedComponent.image f h.continuousOn).subset_connectedComponent
    ((mem_image f (connectedComponent a) (f a)).2 ⟨a, mem_connectedComponent, rfl⟩)

中文:
定理 连续.image_connectedComponent_subset
  结论: [拓扑空间 β] {f : α -> β}
  证明: (isConnected_connectedComponent.image f h.continuousOn).subset_connectedComponent
    ((mem_image f (connectedComponent a) (f a)).2 ⟨a, mem_connectedComponent, rfl⟩)

Depends on / 依赖: connectedComponent, continuousOn, h.continuousOn, isConnected_connectedComponent, isConnected_connectedComponent.image, mem_connectedComponent, mem_image, subset_connectedComponent
-/
theorem Continuous.image_connectedComponent_subset [TopologicalSpace β] {f : α -> β}
    (h : Continuous f) (a : α) : f '' connectedComponent a subseteq connectedComponent (f a) :=
  (isConnected_connectedComponent.image f h.continuousOn).subset_connectedComponent
    ((mem_image f (connectedComponent a) (f a)).2 ⟨a, mem_connectedComponent, rfl⟩)

/--
theorem `ContinuousOn.image_connectedComponentIn_subset` / 定理 `ContinuousOn.image_connectedComponentIn_subset`

English:
theorem ContinuousOn.image_connectedComponentIn_subset
  statement: [TopologicalSpace β] {f : α -> β} {s : Set α}
  proof: (isPreconnected_connectedComponentIn.image _ <| hf.mono <| connectedComponentIn_subset _ _)
.subset_connectedComponentIn (mem_image_of_mem _ <| mem_connectedComponentIn hx)
      (image_mono <| connectedComponentIn_subset _ _)

@[deprecated ContinuousOn.image_connectedComponentIn_subset (since := "2026-07-27")]

中文:
定理 ContinuousOn.image_connectedComponentIn_subset
  结论: [拓扑空间 β] {f : α -> β} {s : 集合 α}
  证明: (isPreconnected_connectedComponentIn.image _ <| hf.mono <| connectedComponentIn_subset _ _)
.subset_connectedComponentIn (mem_image_of_mem _ <| mem_connectedComponentIn hx)
      (image_mono <| connectedComponentIn_subset _ _)

@[deprecated ContinuousOn.image_connectedComponentIn_subset (since := "2026-07-27")]

Depends on / 依赖: connectedComponentIn_subset, hf.mono, image_mono, isPreconnected_connectedComponentIn, isPreconnected_connectedComponentIn.image, mem_connectedComponentIn, mem_image_of_mem, subset_connectedComponentIn
-/
theorem ContinuousOn.image_connectedComponentIn_subset [TopologicalSpace β] {f : α -> β} {s : Set α}
    {a : α} (hf : ContinuousOn f s) (hx : a in s) :
    f '' connectedComponentIn s a subseteq connectedComponentIn (f '' s) (f a) :=
  (isPreconnected_connectedComponentIn.image _ <| hf.mono <| connectedComponentIn_subset _ _)
.subset_connectedComponentIn (mem_image_of_mem _ <| mem_connectedComponentIn hx)
      (image_mono <| connectedComponentIn_subset _ _)

@[deprecated ContinuousOn.image_connectedComponentIn_subset (since := "2026-07-27")]
/--
theorem `Continuous.image_connectedComponentIn_subset` / 定理 `Continuous.image_connectedComponentIn_subset`

English:
theorem Continuous.image_connectedComponentIn_subset
  statement: [TopologicalSpace β] {f : α -> β} {s : Set α}
  proof: hf.continuousOn.image_connectedComponentIn_subset hx

中文:
定理 连续.image_connectedComponentIn_subset
  结论: [拓扑空间 β] {f : α -> β} {s : 集合 α}
  证明: hf.continuousOn.image_connectedComponentIn_subset hx

Depends on / 依赖: continuousOn, hf.continuousOn.image_connectedComponentIn_subset, image_connectedComponentIn_subset
-/
theorem Continuous.image_connectedComponentIn_subset [TopologicalSpace β] {f : α -> β} {s : Set α}
    {a : α} (hf : Continuous f) (hx : a in s) :
    f '' connectedComponentIn s a subseteq connectedComponentIn (f '' s) (f a) :=
  hf.continuousOn.image_connectedComponentIn_subset hx

/--
theorem `Continuous.mapsTo_connectedComponent` / 定理 `Continuous.mapsTo_connectedComponent`

English:
theorem Continuous.mapsTo_connectedComponent
  statement: [TopologicalSpace β] {f : α -> β} (h : Continuous f)
  proof: mapsTo_iff_image_subset.2 h.image_connectedComponent_subset a

中文:
定理 连续.mapsTo_connectedComponent
  结论: [拓扑空间 β] {f : α -> β} (h : 连续 f)
  证明: mapsTo_iff_image_subset.2 h.image_connectedComponent_subset a

Depends on / 依赖: h.image_connectedComponent_subset, image_connectedComponent_subset, mapsTo_iff_image_subset
-/
theorem Continuous.mapsTo_connectedComponent [TopologicalSpace β] {f : α -> β} (h : Continuous f)
    (a : α) : MapsTo f (connectedComponent a) (connectedComponent (f a)) :=
mapsTo_iff_image_subset.2 h.image_connectedComponent_subset a

/--
theorem `ContinuousOn.mapsTo_connectedComponentIn` / 定理 `ContinuousOn.mapsTo_connectedComponentIn`

English:
theorem ContinuousOn.mapsTo_connectedComponentIn
  statement: [TopologicalSpace β] {f : α -> β} {s : Set α}
  proof: mapsTo_iff_image_subset.2 h.image_connectedComponentIn_subset hx

@[deprecated ContinuousOn.mapsTo_connectedComponentIn (since := "2026-07-27")]

中文:
定理 ContinuousOn.mapsTo_connectedComponentIn
  结论: [拓扑空间 β] {f : α -> β} {s : 集合 α}
  证明: mapsTo_iff_image_subset.2 h.image_connectedComponentIn_subset hx

@[deprecated ContinuousOn.mapsTo_connectedComponentIn (since := "2026-07-27")]

Depends on / 依赖: h.image_connectedComponentIn_subset, image_connectedComponentIn_subset, mapsTo_iff_image_subset
-/
theorem ContinuousOn.mapsTo_connectedComponentIn [TopologicalSpace β] {f : α -> β} {s : Set α}
    (h : ContinuousOn f s) {a : α} (hx : a in s) :
    MapsTo f (connectedComponentIn s a) (connectedComponentIn (f '' s) (f a)) :=
mapsTo_iff_image_subset.2 h.image_connectedComponentIn_subset hx

@[deprecated ContinuousOn.mapsTo_connectedComponentIn (since := "2026-07-27")]
/--
theorem `Continuous.mapsTo_connectedComponentIn` / 定理 `Continuous.mapsTo_connectedComponentIn`

English:
theorem Continuous.mapsTo_connectedComponentIn
  statement: [TopologicalSpace β] {f : α -> β} {s : Set α}
  proof: h.continuousOn.mapsTo_connectedComponentIn hx

中文:
定理 连续.mapsTo_connectedComponentIn
  结论: [拓扑空间 β] {f : α -> β} {s : 集合 α}
  证明: h.continuousOn.mapsTo_connectedComponentIn hx

Depends on / 依赖: continuousOn, h.continuousOn.mapsTo_connectedComponentIn, mapsTo_connectedComponentIn
-/
theorem Continuous.mapsTo_connectedComponentIn [TopologicalSpace β] {f : α -> β} {s : Set α}
    (h : Continuous f) {a : α} (hx : a in s) :
    MapsTo f (connectedComponentIn s a) (connectedComponentIn (f '' s) (f a)) :=
  h.continuousOn.mapsTo_connectedComponentIn hx

/--
theorem `connectedComponent_prod` / 定理 `connectedComponent_prod`

English:
theorem connectedComponent_prod
  given: [TopologicalSpace β] (x : α) (y : β)
  proof: subset_antisymm
    (fun _ hp => ⟨continuous_fst.mapsTo_connectedComponent (x, y) hp,
      continuous_snd.mapsTo_connectedComponent (x, y) hp⟩)
    (isPreconnected_connectedComponent.prod isPreconnected_connectedComponent
.subset_connectedComponent ⟨mem_connectedComponent, mem_connectedComponent⟩)

中文:
定理 connectedComponent_prod
  条件: [拓扑空间 β] (x : α) (y : β)
  证明: subset_antisymm
    (fun _ hp => ⟨continuous_fst.mapsTo_connectedComponent (x, y) hp,
      continuous_snd.mapsTo_connectedComponent (x, y) hp⟩)
    (isPreconnected_connectedComponent.prod isPreconnected_connectedComponent
.subset_connectedComponent ⟨mem_connectedComponent, mem_connectedComponent⟩)

Depends on / 依赖: continuous_fst, continuous_fst.mapsTo_connectedComponent, continuous_snd, continuous_snd.mapsTo_connectedComponent, isPreconnected_connectedComponent, isPreconnected_connectedComponent.prod, mapsTo_connectedComponent, mem_connectedComponent, subset_antisymm, subset_connectedComponent
-/
theorem connectedComponent_prod [TopologicalSpace β] (x : α) (y : β) :
    connectedComponent (x, y) = connectedComponent x ×ˢ connectedComponent y :=
  subset_antisymm
    (fun _ hp => ⟨continuous_fst.mapsTo_connectedComponent (x, y) hp,
      continuous_snd.mapsTo_connectedComponent (x, y) hp⟩)
    (isPreconnected_connectedComponent.prod isPreconnected_connectedComponent
.subset_connectedComponent ⟨mem_connectedComponent, mem_connectedComponent⟩)

/--
theorem `connectedComponent_pi` / 定理 `connectedComponent_pi`

English:
theorem connectedComponent_pi
  given: [forall i, TopologicalSpace (X i)] (x : forall i, X i)
  proof: subset_antisymm (fun _ hy i _ => (continuous_apply i).mapsTo_connectedComponent x hy)
    (isPreconnected_univ_pi (fun _ => isPreconnected_connectedComponent)
.subset_connectedComponent fun _ _ => mem_connectedComponent)

中文:
定理 connectedComponent_pi
  条件: [对任意 i, 拓扑空间 (X i)] (x : 对任意 i, X i)
  证明: subset_antisymm (fun _ hy i _ => (continuous_apply i).mapsTo_connectedComponent x hy)
    (isPreconnected_univ_pi (fun _ => isPreconnected_connectedComponent)
.subset_connectedComponent fun _ _ => mem_connectedComponent)

Depends on / 依赖: continuous_apply, isPreconnected_connectedComponent, isPreconnected_univ_pi, mapsTo_connectedComponent, mem_connectedComponent, subset_antisymm, subset_connectedComponent
-/
theorem connectedComponent_pi [forall i, TopologicalSpace (X i)] (x : forall i, X i) :
    connectedComponent x = univ.pi fun i => connectedComponent (x i) :=
  subset_antisymm (fun _ hy i _ => (continuous_apply i).mapsTo_connectedComponent x hy)
    (isPreconnected_univ_pi (fun _ => isPreconnected_connectedComponent)
.subset_connectedComponent fun _ _ => mem_connectedComponent)

/--
theorem `irreducibleComponent_subset_connectedComponent` / 定理 `irreducibleComponent_subset_connectedComponent`

English:
theorem irreducibleComponent_subset_connectedComponent
  given: {x : α}
  proof: isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent mem_irreducibleComponent

@[gcongr, mono]

中文:
定理 irreducibleComponent_subset_connectedComponent
  条件: {x : α}
  证明: isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent mem_irreducibleComponent

@[gcongr, mono]

Depends on / 依赖: isConnected, isIrreducible_irreducibleComponent, isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent, mem_irreducibleComponent, subset_connectedComponent
-/
theorem irreducibleComponent_subset_connectedComponent {x : α} :
    irreducibleComponent x subseteq connectedComponent x :=
  isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent mem_irreducibleComponent

@[gcongr, mono]
/--
theorem `connectedComponentIn_mono` / 定理 `connectedComponentIn_mono`

English:
theorem connectedComponentIn_mono
  given: (x : α) {F G : Set α} (h : F subseteq G)
  proof: by
  by_cases hx : x in F
  · rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image (h hx), ←
      show ((↑) : G -> α) ∘ inclusion h = (↑) from rfl, image_comp]
    exact image_mono ((continuous_inclusion h).image_connectedComponent_subset ⟨x, hx⟩)
  · rw [connectedComponentIn_eq_empty hx]
    exact Set.empty_subset _

中文:
定理 connectedComponentIn_mono
  条件: (x : α) {F G : 集合 α} (h : F subseteq G)
  证明: by
  by_cases hx : x in F
  · rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image (h hx), ←
      show ((↑) : G -> α) ∘ inclusion h = (↑) from rfl, image_comp]
    exact image_mono ((continuous_inclusion h).image_connectedComponent_subset ⟨x, hx⟩)
  · rw [connectedComponentIn_eq_empty hx]
    exact Set.empty_subset _

Depends on / 依赖: Set.empty_subset, connectedComponentIn_eq_empty, connectedComponentIn_eq_image, continuous_inclusion, empty_subset, image_comp, image_connectedComponent_subset, image_mono, inclusion
-/
theorem connectedComponentIn_mono (x : α) {F G : Set α} (h : F subseteq G) :
    connectedComponentIn F x subseteq connectedComponentIn G x := by
  by_cases hx : x in F
  · rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image (h hx), ←
      show ((↑) : G -> α) ∘ inclusion h = (↑) from rfl, image_comp]
    exact image_mono ((continuous_inclusion h).image_connectedComponent_subset ⟨x, hx⟩)
  · rw [connectedComponentIn_eq_empty hx]
    exact Set.empty_subset _

/--
theorem `ContinuousOn.preimage_connectedComponentIn` / 定理 `ContinuousOn.preimage_connectedComponentIn`

English:
theorem ContinuousOn.preimage_connectedComponentIn
  statement: [TopologicalSpace β] {f : α -> β} {F : Set β}
  proof: by
  refine subset_antisymm (fun z hz => ?_) (iUnion₂_subset fun x hx z hz => ?_)
  · exact mem_biUnion hz (mem_connectedComponentIn (connectedComponentIn_subset F y hz))
  · rw [mem_preimage, connectedComponentIn_eq hx]
    exact connectedComponentIn_mono _ (image_preimage_subset f F)
      (hf.mapsTo_connectedComponentIn (connectedComponentIn_subset F y hx) hz)

中文:
定理 ContinuousOn.preimage_connectedComponentIn
  结论: [拓扑空间 β] {f : α -> β} {F : 集合 β}
  证明: by
  refine subset_antisymm (fun z hz => ?_) (iUnion₂_subset fun x hx z hz => ?_)
  · exact mem_biUnion hz (mem_connectedComponentIn (connectedComponentIn_subset F y hz))
  · rw [mem_preimage, connectedComponentIn_eq hx]
    exact connectedComponentIn_mono _ (image_preimage_subset f F)
      (hf.mapsTo_connectedComponentIn (connectedComponentIn_subset F y hx) hz)

Depends on / 依赖: connectedComponentIn_eq, connectedComponentIn_mono, connectedComponentIn_subset, hf.mapsTo_connectedComponentIn, image_preimage_subset, mapsTo_connectedComponentIn, mem_biUnion, mem_connectedComponentIn, mem_preimage, subset_antisymm
-/
theorem ContinuousOn.preimage_connectedComponentIn [TopologicalSpace β] {f : α -> β} {F : Set β}
    (hf : ContinuousOn f (f ⁻¹' F)) (y : β) :
    f ⁻¹' connectedComponentIn F y =
      ⋃ x in f ⁻¹' connectedComponentIn F y, connectedComponentIn (f ⁻¹' F) x := by
  refine subset_antisymm (fun z hz => ?_) (iUnion₂_subset fun x hx z hz => ?_)
  · exact mem_biUnion hz (mem_connectedComponentIn (connectedComponentIn_subset F y hz))
  · rw [mem_preimage, connectedComponentIn_eq hx]
    exact connectedComponentIn_mono _ (image_preimage_subset f F)
      (hf.mapsTo_connectedComponentIn (connectedComponentIn_subset F y hx) hz)

/--
theorem `Continuous.preimage_connectedComponent` / 定理 `Continuous.preimage_connectedComponent`

English:
theorem Continuous.preimage_connectedComponent
  statement: [TopologicalSpace β] {f : α -> β}
  proof: by
  simpa [connectedComponentIn_univ] using
    hf.continuousOn.preimage_connectedComponentIn (F := univ) y

中文:
定理 连续.preimage_connectedComponent
  结论: [拓扑空间 β] {f : α -> β}
  证明: by
  simpa [connectedComponentIn_univ] using
    hf.continuousOn.preimage_connectedComponentIn (F := univ) y

Depends on / 依赖: connectedComponentIn_univ, continuousOn, hf.continuousOn.preimage_connectedComponentIn, preimage_connectedComponentIn
-/
theorem Continuous.preimage_connectedComponent [TopologicalSpace β] {f : α -> β}
    (hf : Continuous f) (y : β) :
    f ⁻¹' connectedComponent y = ⋃ x in f ⁻¹' connectedComponent y, connectedComponent x := by
  simpa [connectedComponentIn_univ] using
    hf.continuousOn.preimage_connectedComponentIn (F := univ) y

/--
Definition of `PreconnectedSpace` / `PreconnectedSpace` 的定义

English:
class PreconnectedSpace
  parameters: (α : Type u) [TopologicalSpace α]
  axioms and operations (1):
    - isPreconnected_univ : IsPreconnected (univ : Set α)

中文:
类 预连通空间
  参数: (α : 类型u) [拓扑空间 α]
  公理与运算 (1 个):
    - isPreconnected_univ : 是预连通 (univ : 集合 α)
-/
class PreconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a preconnected space is a preconnected set. -/
  isPreconnected_univ : IsPreconnected (univ : Set α)

export PreconnectedSpace (isPreconnected_univ)

/-- A connected space is a nonempty one where there is no non-trivial open partition. -/
@[wikidata Q1491995, mk_iff]
/--
Definition of `ConnectedSpace` / `ConnectedSpace` 的定义

English:
class ConnectedSpace
  parameters: (α : Type u) [TopologicalSpace α]
  extends: PreconnectedSpace α
  axioms and operations (1):
    - toNonempty : Nonempty α

中文:
类 连通空间
  参数: (α : 类型u) [拓扑空间 α]
  继承: 预连通空间 α
  公理与运算 (1 个):
    - toNonempty : 非空 α
-/
class ConnectedSpace (α : Type u) [TopologicalSpace α] : Prop extends PreconnectedSpace α where
  /-- A connected space is nonempty. -/
  toNonempty : Nonempty α

attribute [instance 50] ConnectedSpace.toNonempty -- see Note [lower instance priority]

-- see Note [lower instance priority]
/--
theorem `isConnected_univ` / 定理 `isConnected_univ`

English:
theorem isConnected_univ
  given: [ConnectedSpace α]
  statement: IsConnected (univ : Set α)
  proof: ⟨univ_nonempty, isPreconnected_univ⟩

中文:
定理 isConnected_univ
  条件: [连通空间 α]
  结论: 是连通 (univ : 集合 α)
  证明: ⟨univ_nonempty, isPreconnected_univ⟩

Depends on / 依赖: isPreconnected_univ, univ_nonempty
-/
theorem isConnected_univ [ConnectedSpace α] : IsConnected (univ : Set α) :=
  ⟨univ_nonempty, isPreconnected_univ⟩

/--
lemma `preconnectedSpace_iff_univ` / 引理 `preconnectedSpace_iff_univ`

English:
lemma preconnectedSpace_iff_univ
  statement: PreconnectedSpace α ↔ IsPreconnected (univ : Set α)
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
引理 preconnectedSpace_iff_univ
  结论: 预连通空间 α ↔ 是预连通 (univ : 集合 α)
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
lemma preconnectedSpace_iff_univ : PreconnectedSpace α ↔ IsPreconnected (univ : Set α) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
lemma `connectedSpace_iff_univ` / 引理 `connectedSpace_iff_univ`

English:
lemma connectedSpace_iff_univ
  statement: ConnectedSpace α ↔ IsConnected (univ : Set α)
  proof: ⟨fun h => ⟨univ_nonempty, h.1.1⟩,
   fun h => ConnectedSpace.mk (toPreconnectedSpace := ⟨h.2⟩) ⟨h.1.some⟩⟩

中文:
引理 connectedSpace_iff_univ
  结论: 连通空间 α ↔ 是连通 (univ : 集合 α)
  证明: ⟨fun h => ⟨univ_nonempty, h.1.1⟩,
   fun h => ConnectedSpace.mk (toPreconnectedSpace := ⟨h.2⟩) ⟨h.1.some⟩⟩

Depends on / 依赖: ConnectedSpace, ConnectedSpace.mk, toPreconnectedSpace, univ_nonempty
-/
lemma connectedSpace_iff_univ : ConnectedSpace α ↔ IsConnected (univ : Set α) :=
  ⟨fun h => ⟨univ_nonempty, h.1.1⟩,
   fun h => ConnectedSpace.mk (toPreconnectedSpace := ⟨h.2⟩) ⟨h.1.some⟩⟩

/--
theorem `isPreconnected_range` / 定理 `isPreconnected_range`

English:
theorem isPreconnected_range
  statement: [TopologicalSpace β] [PreconnectedSpace α] {f : α -> β}
  proof: @image_univ _ _ f ▸ isPreconnected_univ.image _ h.continuousOn

中文:
定理 isPreconnected_range
  结论: [拓扑空间 β] [预连通空间 α] {f : α -> β}
  证明: @image_univ _ _ f ▸ isPreconnected_univ.image _ h.continuousOn

Depends on / 依赖: continuousOn, h.continuousOn, image_univ, isPreconnected_univ, isPreconnected_univ.image
-/
theorem isPreconnected_range [TopologicalSpace β] [PreconnectedSpace α] {f : α -> β}
    (h : Continuous f) : IsPreconnected (range f) :=
  @image_univ _ _ f ▸ isPreconnected_univ.image _ h.continuousOn

/--
theorem `isConnected_range` / 定理 `isConnected_range`

English:
theorem isConnected_range
  given: [TopologicalSpace β] [ConnectedSpace α] {f : α -> β} (h : Continuous f)
  proof: ⟨range_nonempty f, isPreconnected_range h⟩

中文:
定理 isConnected_range
  条件: [拓扑空间 β] [连通空间 α] {f : α -> β} (h : 连续 f)
  证明: ⟨range_nonempty f, isPreconnected_range h⟩

Depends on / 依赖: isPreconnected_range, range_nonempty
-/
theorem isConnected_range [TopologicalSpace β] [ConnectedSpace α] {f : α -> β} (h : Continuous f) :
    IsConnected (range f) :=
  ⟨range_nonempty f, isPreconnected_range h⟩

/--
theorem `Function.Surjective.connectedSpace` / 定理 `Function.Surjective.connectedSpace`

English:
theorem Function.Surjective.connectedSpace
  statement: [ConnectedSpace α] [TopologicalSpace β]
  proof: by
  rw [connectedSpace_iff_univ]; rw [← hf.range_eq]
  exact isConnected_range hf'

中文:
定理 函数.满射.connectedSpace
  结论: [连通空间 α] [拓扑空间 β]
  证明: by
  rw [connectedSpace_iff_univ]; rw [← hf.range_eq]
  exact isConnected_range hf'

Depends on / 依赖: connectedSpace_iff_univ, hf.range_eq, isConnected_range, range_eq
-/
theorem Function.Surjective.connectedSpace [ConnectedSpace α] [TopologicalSpace β]
    {f : α -> β} (hf : Surjective f) (hf' : Continuous f) : ConnectedSpace β := by
  rw [connectedSpace_iff_univ]; rw [← hf.range_eq]
  exact isConnected_range hf'

/--
lemma `Homeomorph.connectedSpace_iff` / 引理 `Homeomorph.connectedSpace_iff`

English:
lemma Homeomorph.connectedSpace_iff
  given: [TopologicalSpace β] (e : α ≃ₜ β)
  proof: ⟨fun _ => e.surjective.connectedSpace e.continuous,
    fun _ => e.symm.surjective.connectedSpace e.symm.continuous⟩

中文:
引理 同胚.connectedSpace_iff
  条件: [拓扑空间 β] (e : α ≃ₜ β)
  证明: ⟨fun _ => e.surjective.connectedSpace e.continuous,
    fun _ => e.symm.surjective.connectedSpace e.symm.continuous⟩

Depends on / 依赖: connectedSpace, continuous, e.continuous, e.surjective.connectedSpace, e.symm.continuous, e.symm.surjective.connectedSpace, surjective
-/
lemma Homeomorph.connectedSpace_iff [TopologicalSpace β] (e : α ≃ₜ β) :
    ConnectedSpace α ↔ ConnectedSpace β :=
  ⟨fun _ => e.surjective.connectedSpace e.continuous,
    fun _ => e.symm.surjective.connectedSpace e.symm.continuous⟩

/--
Instance `Quotient.instConnectedSpace` / 实例 `Quotient.instConnectedSpace`

English:
instance Quotient.instConnectedSpace
  signature: {s : Setoid α} [ConnectedSpace α]
  body: Quotient.mk'_surjective.connectedSpace continuous_coinduced_rng

中文:
实例 商.instConnectedSpace
  签名: {s : 集合等价关系 α} [连通空间 α]
  定义体: Quotient.mk'_surjective.connectedSpace continuous_coinduced_rng

Depends on / 依赖: Quotient, Quotient.mk, _surjective, _surjective.connectedSpace, connectedSpace, continuous_coinduced_rng
-/
instance Quotient.instConnectedSpace {s : Setoid α} [ConnectedSpace α] :
    ConnectedSpace (Quotient s) :=
  Quotient.mk'_surjective.connectedSpace continuous_coinduced_rng

/--
theorem `DenseRange.preconnectedSpace` / 定理 `DenseRange.preconnectedSpace`

English:
theorem DenseRange.preconnectedSpace
  statement: [TopologicalSpace β] [PreconnectedSpace α] {f : α -> β}
  proof: ⟨hf.closure_eq ▸ (isPreconnected_range hc).closure⟩

中文:
定理 DenseRange.preconnectedSpace
  结论: [拓扑空间 β] [预连通空间 α] {f : α -> β}
  证明: ⟨hf.closure_eq ▸ (isPreconnected_range hc).closure⟩

Depends on / 依赖: closure, closure_eq, hf.closure_eq, isPreconnected_range
-/
theorem DenseRange.preconnectedSpace [TopologicalSpace β] [PreconnectedSpace α] {f : α -> β}
    (hf : DenseRange f) (hc : Continuous f) : PreconnectedSpace β :=
  ⟨hf.closure_eq ▸ (isPreconnected_range hc).closure⟩

/--
theorem `connectedSpace_iff_connectedComponent` / 定理 `connectedSpace_iff_connectedComponent`

English:
theorem connectedSpace_iff_connectedComponent
  proof: by
  constructor
  · rintro ⟨⟨x⟩⟩
    exact
⟨x, eq_univ_of_univ_subset isPreconnected_univ.subset_connectedComponent (mem_univ x)⟩
  · rintro ⟨x, h⟩
    have : PreconnectedSpace α :=
      ⟨by rw [← h]; exact isPreconnected_connectedComponent⟩
    exact ⟨⟨x⟩⟩

中文:
定理 connectedSpace_iff_connectedComponent
  证明: by
  constructor
  · rintro ⟨⟨x⟩⟩
    exact
⟨x, eq_univ_of_univ_subset isPreconnected_univ.subset_connectedComponent (mem_univ x)⟩
  · rintro ⟨x, h⟩
    have : PreconnectedSpace α :=
      ⟨by rw [← h]; exact isPreconnected_connectedComponent⟩
    exact ⟨⟨x⟩⟩

Depends on / 依赖: PreconnectedSpace, eq_univ_of_univ_subset, isPreconnected_connectedComponent, isPreconnected_univ, isPreconnected_univ.subset_connectedComponent, mem_univ, subset_connectedComponent
-/
theorem connectedSpace_iff_connectedComponent :
    ConnectedSpace α ↔ exists x : α, connectedComponent x = univ := by
  constructor
  · rintro ⟨⟨x⟩⟩
    exact
⟨x, eq_univ_of_univ_subset isPreconnected_univ.subset_connectedComponent (mem_univ x)⟩
  · rintro ⟨x, h⟩
    have : PreconnectedSpace α :=
      ⟨by rw [← h]; exact isPreconnected_connectedComponent⟩
    exact ⟨⟨x⟩⟩

/--
theorem `preconnectedSpace_iff_connectedComponent` / 定理 `preconnectedSpace_iff_connectedComponent`

English:
theorem preconnectedSpace_iff_connectedComponent
  proof: by
  constructor
  · intro h x
exact eq_univ_of_univ_subset isPreconnected_univ.subset_connectedComponent (mem_univ x)
  · intro h
    rcases isEmpty_or_nonempty α with hα | hα
    · exact ⟨by rw [univ_eq_empty_iff.mpr hα]; exact isPreconnected_empty⟩
    · exact ⟨by rw [← h (Classical.choice hα)]; exact isPreconnected_connectedComponent⟩

@[simp]

中文:
定理 preconnectedSpace_iff_connectedComponent
  证明: by
  constructor
  · intro h x
exact eq_univ_of_univ_subset isPreconnected_univ.subset_connectedComponent (mem_univ x)
  · intro h
    rcases isEmpty_or_nonempty α with hα | hα
    · exact ⟨by rw [univ_eq_empty_iff.mpr hα]; exact isPreconnected_empty⟩
    · exact ⟨by rw [← h (Classical.choice hα)]; exact isPreconnected_connectedComponent⟩

@[simp]

Depends on / 依赖: Classical, Classical.choice, choice, eq_univ_of_univ_subset, isEmpty_or_nonempty, isPreconnected_connectedComponent, isPreconnected_empty, isPreconnected_univ, isPreconnected_univ.subset_connectedComponent, mem_univ, subset_connectedComponent, univ_eq_empty_iff, univ_eq_empty_iff.mpr
-/
theorem preconnectedSpace_iff_connectedComponent :
    PreconnectedSpace α ↔ forall x : α, connectedComponent x = univ := by
  constructor
  · intro h x
exact eq_univ_of_univ_subset isPreconnected_univ.subset_connectedComponent (mem_univ x)
  · intro h
    rcases isEmpty_or_nonempty α with hα | hα
    · exact ⟨by rw [univ_eq_empty_iff.mpr hα]; exact isPreconnected_empty⟩
    · exact ⟨by rw [← h (Classical.choice hα)]; exact isPreconnected_connectedComponent⟩

@[simp]
/--
theorem `PreconnectedSpace.connectedComponent_eq_univ` / 定理 `PreconnectedSpace.connectedComponent_eq_univ`

English:
theorem PreconnectedSpace.connectedComponent_eq_univ
  statement: {X : Type*} [TopologicalSpace X]
  proof: preconnectedSpace_iff_connectedComponent.mp h x

中文:
定理 预连通空间.connectedComponent_eq_univ
  结论: {X : 类型} [拓扑空间 X]
  证明: preconnectedSpace_iff_connectedComponent.mp h x

Depends on / 依赖: preconnectedSpace_iff_connectedComponent, preconnectedSpace_iff_connectedComponent.mp
-/
theorem PreconnectedSpace.connectedComponent_eq_univ {X : Type*} [TopologicalSpace X]
    [h : PreconnectedSpace X] (x : X) : connectedComponent x = univ :=
  preconnectedSpace_iff_connectedComponent.mp h x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: β] [PreconnectedSpace α] [PreconnectedSpace β] :
  body: ⟨by
    rw [← univ_prod_univ]
    exact isPreconnected_univ.prod isPreconnected_univ⟩

中文:
实例 [拓扑空间
  签名: β] [预连通空间 α] [预连通空间 β] :
  定义体: ⟨by
    rw [← univ_prod_univ]
    exact isPreconnected_univ.prod isPreconnected_univ⟩

Depends on / 依赖: isPreconnected_univ, isPreconnected_univ.prod, univ_prod_univ
-/
instance [TopologicalSpace β] [PreconnectedSpace α] [PreconnectedSpace β] :
    PreconnectedSpace (α × β) :=
  ⟨by
    rw [← univ_prod_univ]
    exact isPreconnected_univ.prod isPreconnected_univ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: β] [ConnectedSpace α] [ConnectedSpace β] : ConnectedSpace (α × β)
  body: ⟨inferInstance⟩

中文:
实例 [拓扑空间
  签名: β] [连通空间 α] [连通空间 β] : 连通空间 (α × β)
  定义体: ⟨inferInstance⟩
-/
instance [TopologicalSpace β] [ConnectedSpace α] [ConnectedSpace β] : ConnectedSpace (α × β) :=
  ⟨inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, TopologicalSpace (X i)] [forall i, PreconnectedSpace (X i)] :
  body: ⟨by rw [← pi_univ univ]; exact isPreconnected_univ_pi fun i => isPreconnected_univ⟩

中文:
实例 [对任意
  签名: i, 拓扑空间 (X i)] [对任意 i, 预连通空间 (X i)] :
  定义体: ⟨by rw [← pi_univ univ]; exact isPreconnected_univ_pi fun i => isPreconnected_univ⟩

Depends on / 依赖: isPreconnected_univ, isPreconnected_univ_pi, pi_univ
-/
instance [forall i, TopologicalSpace (X i)] [forall i, PreconnectedSpace (X i)] :
    PreconnectedSpace (forall i, X i) :=
  ⟨by rw [← pi_univ univ]; exact isPreconnected_univ_pi fun i => isPreconnected_univ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, TopologicalSpace (X i)] [forall i, ConnectedSpace (X i)] : ConnectedSpace (forall i, X i)
  body: ⟨inferInstance⟩

中文:
实例 [对任意
  签名: i, 拓扑空间 (X i)] [对任意 i, 连通空间 (X i)] : 连通空间 (对任意 i, X i)
  定义体: ⟨inferInstance⟩
-/
instance [forall i, TopologicalSpace (X i)] [forall i, ConnectedSpace (X i)] : ConnectedSpace (forall i, X i) :=
  ⟨inferInstance⟩

-- see Note [lower instance priority]
instance (priority := 100) PreirreducibleSpace.preconnectedSpace (α : Type u) [TopologicalSpace α]
    [PreirreducibleSpace α] : PreconnectedSpace α :=
  ⟨isPreirreducible_univ.isPreconnected⟩

-- see Note [lower instance priority]
instance (priority := 100) IrreducibleSpace.connectedSpace (α : Type u) [TopologicalSpace α]
    [IrreducibleSpace α] : ConnectedSpace α where toNonempty := IrreducibleSpace.toNonempty

/--
theorem `Subtype.preconnectedSpace` / 定理 `Subtype.preconnectedSpace`

English:
theorem Subtype.preconnectedSpace
  given: {s : Set α} (h : IsPreconnected s)
  statement: PreconnectedSpace s where
  proof: by
    rwa [← IsInducing.subtypeVal.isPreconnected_image, image_univ, Subtype.range_val]

中文:
定理 子类型.preconnectedSpace
  条件: {s : 集合 α} (h : 是预连通 s)
  结论: 预连通空间 s where
  证明: by
    rwa [← IsInducing.subtypeVal.isPreconnected_image, image_univ, Subtype.range_val]

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.isPreconnected_image, Subtype, Subtype.range_val, image_univ, isPreconnected_image, range_val, subtypeVal
-/
theorem Subtype.preconnectedSpace {s : Set α} (h : IsPreconnected s) : PreconnectedSpace s where
  isPreconnected_univ := by
    rwa [← IsInducing.subtypeVal.isPreconnected_image, image_univ, Subtype.range_val]

/--
theorem `Subtype.connectedSpace` / 定理 `Subtype.connectedSpace`

English:
theorem Subtype.connectedSpace
  given: {s : Set α} (h : IsConnected s)
  statement: ConnectedSpace s where
  proof: Subtype.preconnectedSpace h.isPreconnected
  toNonempty := h.nonempty.to_subtype

中文:
定理 子类型.connectedSpace
  条件: {s : 集合 α} (h : 是连通 s)
  结论: 连通空间 s where
  证明: Subtype.preconnectedSpace h.isPreconnected
  toNonempty := h.nonempty.to_subtype

Depends on / 依赖: Subtype, Subtype.preconnectedSpace, h.isPreconnected, isPreconnected, preconnectedSpace
-/
theorem Subtype.connectedSpace {s : Set α} (h : IsConnected s) : ConnectedSpace s where
  toPreconnectedSpace := Subtype.preconnectedSpace h.isPreconnected
  toNonempty := h.nonempty.to_subtype

/--
theorem `isPreconnected_iff_preconnectedSpace` / 定理 `isPreconnected_iff_preconnectedSpace`

English:
theorem isPreconnected_iff_preconnectedSpace
  given: {s : Set α}
  statement: IsPreconnected s ↔ PreconnectedSpace s
  proof: ⟨Subtype.preconnectedSpace, fun h => by
    simpa using isPreconnected_univ.image ((↑) : s -> α) continuous_subtype_val.continuousOn⟩

中文:
定理 isPreconnected_iff_preconnectedSpace
  条件: {s : 集合 α}
  结论: 是预连通 s ↔ 预连通空间 s
  证明: ⟨Subtype.preconnectedSpace, fun h => by
    simpa using isPreconnected_univ.image ((↑) : s -> α) continuous_subtype_val.continuousOn⟩

Depends on / 依赖: Subtype, Subtype.preconnectedSpace, continuousOn, continuous_subtype_val, continuous_subtype_val.continuousOn, isPreconnected_univ, isPreconnected_univ.image, preconnectedSpace
-/
theorem isPreconnected_iff_preconnectedSpace {s : Set α} : IsPreconnected s ↔ PreconnectedSpace s :=
  ⟨Subtype.preconnectedSpace, fun h => by
    simpa using isPreconnected_univ.image ((↑) : s -> α) continuous_subtype_val.continuousOn⟩

/--
theorem `isConnected_iff_connectedSpace` / 定理 `isConnected_iff_connectedSpace`

English:
theorem isConnected_iff_connectedSpace
  given: {s : Set α}
  statement: IsConnected s ↔ ConnectedSpace s
  proof: ⟨Subtype.connectedSpace, fun h =>
    ⟨nonempty_subtype.mp h.2, isPreconnected_iff_preconnectedSpace.mpr h.1⟩⟩

中文:
定理 isConnected_iff_connectedSpace
  条件: {s : 集合 α}
  结论: 是连通 s ↔ 连通空间 s
  证明: ⟨Subtype.connectedSpace, fun h =>
    ⟨nonempty_subtype.mp h.2, isPreconnected_iff_preconnectedSpace.mpr h.1⟩⟩

Depends on / 依赖: Subtype, Subtype.connectedSpace, connectedSpace, isPreconnected_iff_preconnectedSpace, isPreconnected_iff_preconnectedSpace.mpr, nonempty_subtype, nonempty_subtype.mp
-/
theorem isConnected_iff_connectedSpace {s : Set α} : IsConnected s ↔ ConnectedSpace s :=
  ⟨Subtype.connectedSpace, fun h =>
    ⟨nonempty_subtype.mp h.2, isPreconnected_iff_preconnectedSpace.mpr h.1⟩⟩

end Preconnected
