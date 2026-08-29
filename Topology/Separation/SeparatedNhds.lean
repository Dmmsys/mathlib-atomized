/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Continuous
public import Mathlib.Topology.NhdsSet

/-!
# Separated neighbourhoods

This file defines the predicates `SeparatedNhds` and `HasSeparatingCover`, which are used in
formulating separation axioms for topological spaces.

## Main definitions

* `SeparatedNhds`: Two `Set`s are separated by neighbourhoods if they are contained in disjoint
  open sets.
* `HasSeparatingCover`: A set has a countable cover that can be used with
  `hasSeparatingCovers_iff_separatedNhds` to witness when two `Set`s have `SeparatedNhds`.

## References

* <https://en.wikipedia.org/wiki/Separation_axiom>
* [Willard's *General Topology*][zbMATH02107988]
-/

@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

/--
Definition of `SeparatedNhds` / `SeparatedNhds` 的定义

English:
definition SeparatedNhds
  signature: : Set X -> Set X -> Prop
  body: fun s t : Set X =>
  exists U V : Set X, IsOpen U ∧ IsOpen V ∧ s subseteq U ∧ t subseteq V ∧ Disjoint U V

中文:
定义 SeparatedNhds
  签名: : Set X -> Set X -> 命题
  定义体: fun s t : Set X =>
  exists U V : Set X, IsOpen U ∧ IsOpen V ∧ s subseteq U ∧ t subseteq V ∧ Disjoint U V
-/
def SeparatedNhds : Set X -> Set X -> Prop := fun s t : Set X =>
  exists U V : Set X, IsOpen U ∧ IsOpen V ∧ s subseteq U ∧ t subseteq V ∧ Disjoint U V

/--
theorem `separatedNhds_iff_disjoint` / 定理 `separatedNhds_iff_disjoint`

English:
theorem separatedNhds_iff_disjoint
  given: {s t : Set X}
  statement: SeparatedNhds s t ↔ Disjoint (𝓝ˢ s) (𝓝ˢ t)
  proof: by
  simp only [(hasBasis_nhdsSet s).disjoint_iff (hasBasis_nhdsSet t), SeparatedNhds, ←
    exists_and_left, and_assoc, and_comm, and_left_comm]

alias ⟨SeparatedNhds.disjoint_nhdsSet, _⟩ := separatedNhds_iff_disjoint

中文:
定理 separatedNhds_iff_disjoint
  条件: {s t : Set X}
  结论: SeparatedNhds s t ↔ Disjoint (𝓝ˢ s) (𝓝ˢ t)
  证明: by
  simp only [(hasBasis_nhdsSet s).disjoint_iff (hasBasis_nhdsSet t), SeparatedNhds, ←
    exists_and_left, and_assoc, and_comm, and_left_comm]

alias ⟨SeparatedNhds.disjoint_nhdsSet, _⟩ := separatedNhds_iff_disjoint

Depends on / 依赖: SeparatedNhds, and_assoc, and_comm, and_left_comm, disjoint_iff, exists_and_left, hasBasis_nhdsSet
-/
theorem separatedNhds_iff_disjoint {s t : Set X} : SeparatedNhds s t ↔ Disjoint (𝓝ˢ s) (𝓝ˢ t) := by
  simp only [(hasBasis_nhdsSet s).disjoint_iff (hasBasis_nhdsSet t), SeparatedNhds, ←
    exists_and_left, and_assoc, and_comm, and_left_comm]

alias ⟨SeparatedNhds.disjoint_nhdsSet, _⟩ := separatedNhds_iff_disjoint

/--
Definition of `HasSeparatingCover` / `HasSeparatingCover` 的定义

English:
definition HasSeparatingCover
  signature: : Set X -> Set X -> Prop
  body: fun s t =>
  exists u : Nat -> Set X, s subseteq ⋃ n, u n ∧ forall n, IsOpen (u n) ∧ Disjoint (closure (u n)) t

中文:
定义 HasSeparatingCover
  签名: : Set X -> Set X -> 命题
  定义体: fun s t =>
  exists u : Nat -> Set X, s subseteq ⋃ n, u n ∧ forall n, IsOpen (u n) ∧ Disjoint (closure (u n)) t
-/
def HasSeparatingCover : Set X -> Set X -> Prop := fun s t =>
  exists u : Nat -> Set X, s subseteq ⋃ n, u n ∧ forall n, IsOpen (u n) ∧ Disjoint (closure (u n)) t

/--
theorem `hasSeparatingCovers_iff_separatedNhds` / 定理 `hasSeparatingCovers_iff_separatedNhds`

English:
theorem hasSeparatingCovers_iff_separatedNhds
  given: {s t : Set X}
  proof: by
  constructor
  · rintro ⟨⟨u, u_cov, u_props⟩, ⟨v, v_cov, v_props⟩⟩
    have open_lemma : forall (u₀ a : Nat -> Set X), (forall n, IsOpen (u₀ n)) ->
      IsOpen (⋃ n, u₀ n \ closure (a n)) := fun _ _ u₀i_open =>
        isOpen_iUnion fun i => (u₀i_open i).sdiff isClosed_closure
    have cover_le

中文:
定理 hasSeparatingCovers_iff_separatedNhds
  条件: {s t : Set X}
  证明: by
  constructor
  · rintro ⟨⟨u, u_cov, u_props⟩, ⟨v, v_cov, v_props⟩⟩
    have open_lemma : forall (u₀ a : Nat -> Set X), (forall n, IsOpen (u₀ n)) ->
      IsOpen (⋃ n, u₀ n \ closure (a n)) := fun _ _ u₀i_open =>
        isOpen_iUnion fun i => (u₀i_open i).sdiff isClosed_closure
    have cover_le

Depends on / 依赖: Disjoint, IsOpen, closure, cover_lemma, isClosed_closure, isOpen_iUnion, open_lemma, subseteq, u_cov, u_props, v_cov, v_props
-/
theorem hasSeparatingCovers_iff_separatedNhds {s t : Set X} :
    HasSeparatingCover s t ∧ HasSeparatingCover t s ↔ SeparatedNhds s t := by
  constructor
  · rintro ⟨⟨u, u_cov, u_props⟩, ⟨v, v_cov, v_props⟩⟩
    have open_lemma : forall (u₀ a : Nat -> Set X), (forall n, IsOpen (u₀ n)) ->
      IsOpen (⋃ n, u₀ n \ closure (a n)) := fun _ _ u₀i_open =>
        isOpen_iUnion fun i => (u₀i_open i).sdiff isClosed_closure
    have cover_lemma : forall (h₀ : Set X) (u₀ v₀ : Nat -> Set X),
        (h₀ subseteq ⋃ n, u₀ n) -> (forall n, Disjoint (closure (v₀ n)) h₀) ->
        (h₀ subseteq ⋃ n, u₀ n \ closure (⋃ m <= n, v₀ m)) :=
        fun h₀ u₀ v₀ h₀_cov dis x xinh => by
      rcases h₀_cov xinh with ⟨un, ⟨n, rfl⟩, xinun⟩
      simp only [mem_iUnion]
      refine ⟨n, xinun, ?_⟩
      simp_all only [closure_iUnion₂_le_nat, disjoint_right, mem_iUnion,
        exists_false, not_false_eq_true]
    refine
      ⟨⋃ n : Nat, u n \ (closure (⋃ m <= n, v m)),
       ⋃ n : Nat, v n \ (closure (⋃ m <= n, u m)),
       open_lemma u (fun n => ⋃ m <= n, v m) (fun n => (u_props n).1),
       open_lemma v (fun n => ⋃ m <= n, u m) (fun n => (v_props n).1),
       cover_lemma s u v u_cov (fun n => (v_props n).2),
       cover_lemma t v u v_cov (fun n => (u_props n).2),
       ?_⟩
    rw [Set.disjoint_left]
    rintro x ⟨un, ⟨n, rfl⟩, xinun⟩
    suffices forall (m : Nat), x in v m -> x in closure (⋃ m' in {m' | m' <= m}, u m') by simpa
    intro m xinvm
    have n_le_m : n <= m := by
      by_contra m_gt_n
      exact xinun.2 (subset_closure (mem_biUnion (le_of_lt (not_le.mp m_gt_n)) xinvm))
    exact subset_closure (mem_biUnion n_le_m xinun.1)
  · rintro ⟨U, V, U_open, V_open, h_sub_U, k_sub_V, UV_dis⟩
    exact
      ⟨⟨fun _ => U,
        h_sub_U.trans (iUnion_const U).symm.subset,
        fun _ =>
          ⟨U_open, disjoint_of_subset (fun ⦃a⦄ a => a) k_sub_V (UV_dis.closure_left V_open)⟩⟩,
       ⟨fun _ => V,
        k_sub_V.trans (iUnion_const V).symm.subset,
        fun _ =>
          ⟨V_open, disjoint_of_subset (fun ⦃a⦄ a => a) h_sub_U (UV_dis.closure_right U_open).symm⟩⟩⟩

/--
theorem `Set.hasSeparatingCover_empty_left` / 定理 `Set.hasSeparatingCover_empty_left`

English:
theorem Set.hasSeparatingCover_empty_left
  given: (s : Set X)
  statement: HasSeparatingCover ∅ s
  proof: ⟨fun _ => ∅, empty_subset (⋃ _, ∅),
   fun _ => ⟨isOpen_empty, by simp only [closure_empty, empty_disjoint]⟩⟩

中文:
定理 Set.hasSeparatingCover_empty_left
  条件: (s : Set X)
  结论: HasSeparatingCover ∅ s
  证明: ⟨fun _ => ∅, empty_subset (⋃ _, ∅),
   fun _ => ⟨isOpen_empty, by simp only [closure_empty, empty_disjoint]⟩⟩

Depends on / 依赖: closure_empty, empty_disjoint, empty_subset, isOpen_empty
-/
theorem Set.hasSeparatingCover_empty_left (s : Set X) : HasSeparatingCover ∅ s :=
  ⟨fun _ => ∅, empty_subset (⋃ _, ∅),
   fun _ => ⟨isOpen_empty, by simp only [closure_empty, empty_disjoint]⟩⟩

/--
theorem `Set.hasSeparatingCover_empty_right` / 定理 `Set.hasSeparatingCover_empty_right`

English:
theorem Set.hasSeparatingCover_empty_right
  given: (s : Set X)
  statement: HasSeparatingCover s ∅
  proof: ⟨fun _ => univ, (subset_univ s).trans univ.iUnion_const.symm.subset,
   fun _ => ⟨isOpen_univ, by apply disjoint_empty⟩⟩

中文:
定理 Set.hasSeparatingCover_empty_right
  条件: (s : Set X)
  结论: HasSeparatingCover s ∅
  证明: ⟨fun _ => univ, (subset_univ s).trans univ.iUnion_const.symm.subset,
   fun _ => ⟨isOpen_univ, by apply disjoint_empty⟩⟩

Depends on / 依赖: disjoint_empty, iUnion_const, isOpen_univ, subset, subset_univ, univ.iUnion_const.symm.subset
-/
theorem Set.hasSeparatingCover_empty_right (s : Set X) : HasSeparatingCover s ∅ :=
  ⟨fun _ => univ, (subset_univ s).trans univ.iUnion_const.symm.subset,
   fun _ => ⟨isOpen_univ, by apply disjoint_empty⟩⟩

/--
theorem `HasSeparatingCover.mono` / 定理 `HasSeparatingCover.mono`

English:
theorem HasSeparatingCover.mono
  statement: {s₁ s₂ t₁ t₂ : Set X} (sc_st : HasSeparatingCover s₂ t₂)
  proof: by
  obtain ⟨u, u_cov, u_props⟩ := sc_st
  exact
    ⟨u,
     s_sub.trans u_cov,
     fun n =>
       ⟨(u_props n).1,
        disjoint_of_subset (fun ⦃_⦄ a => a) t_sub (u_props n).2⟩⟩

中文:
定理 HasSeparatingCover.mono
  结论: {s₁ s₂ t₁ t₂ : Set X} (sc_st : HasSeparatingCover s₂ t₂)
  证明: by
  obtain ⟨u, u_cov, u_props⟩ := sc_st
  exact
    ⟨u,
     s_sub.trans u_cov,
     fun n =>
       ⟨(u_props n).1,
        disjoint_of_subset (fun ⦃_⦄ a => a) t_sub (u_props n).2⟩⟩

Depends on / 依赖: disjoint_of_subset, s_sub, s_sub.trans, sc_st, t_sub, u_cov, u_props
-/
theorem HasSeparatingCover.mono {s₁ s₂ t₁ t₂ : Set X} (sc_st : HasSeparatingCover s₂ t₂)
    (s_sub : s₁ subseteq s₂) (t_sub : t₁ subseteq t₂) : HasSeparatingCover s₁ t₁ := by
  obtain ⟨u, u_cov, u_props⟩ := sc_st
  exact
    ⟨u,
     s_sub.trans u_cov,
     fun n =>
       ⟨(u_props n).1,
        disjoint_of_subset (fun ⦃_⦄ a => a) t_sub (u_props n).2⟩⟩

namespace SeparatedNhds

variable {s s₁ s₂ t t₁ t₂ u : Set X}

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  statement: SeparatedNhds s t -> SeparatedNhds t s
  proof: fun ⟨U, V, oU, oV, aU, bV, UV⟩ =>
  ⟨V, U, oV, oU, bV, aU, Disjoint.symm UV⟩

中文:
定理 symm
  结论: SeparatedNhds s t -> SeparatedNhds t s
  证明: fun ⟨U, V, oU, oV, aU, bV, UV⟩ =>
  ⟨V, U, oV, oU, bV, aU, Disjoint.symm UV⟩
-/
theorem symm : SeparatedNhds s t -> SeparatedNhds t s := fun ⟨U, V, oU, oV, aU, bV, UV⟩ =>
  ⟨V, U, oV, oU, bV, aU, Disjoint.symm UV⟩

/--
theorem `comm` / 定理 `comm`

English:
theorem comm
  given: (s t : Set X)
  statement: SeparatedNhds s t ↔ SeparatedNhds t s
  proof: ⟨symm, symm⟩

中文:
定理 comm
  条件: (s t : Set X)
  结论: SeparatedNhds s t ↔ SeparatedNhds t s
  证明: ⟨symm, symm⟩
-/
theorem comm (s t : Set X) : SeparatedNhds s t ↔ SeparatedNhds t s :=
  ⟨symm, symm⟩

/--
theorem `preimage` / 定理 `preimage`

English:
theorem preimage
  statement: [TopologicalSpace Y] {f : X -> Y} {s t : Set Y} (h : SeparatedNhds s t)
  proof: let ⟨U, V, oU, oV, sU, tV, UV⟩ := h
  ⟨f ⁻¹' U, f ⁻¹' V, oU.preimage hf, oV.preimage hf, preimage_mono sU, preimage_mono tV,
    UV.preimage f⟩

中文:
定理 preimage
  结论: [TopologicalSpace Y] {f : X -> Y} {s t : Set Y} (h : SeparatedNhds s t)
  证明: let ⟨U, V, oU, oV, sU, tV, UV⟩ := h
  ⟨f ⁻¹' U, f ⁻¹' V, oU.preimage hf, oV.preimage hf, preimage_mono sU, preimage_mono tV,
    UV.preimage f⟩

Depends on / 依赖: UV.preimage, oU.preimage, oV.preimage, preimage, preimage_mono
-/
theorem preimage [TopologicalSpace Y] {f : X -> Y} {s t : Set Y} (h : SeparatedNhds s t)
    (hf : Continuous f) : SeparatedNhds (f ⁻¹' s) (f ⁻¹' t) :=
  let ⟨U, V, oU, oV, sU, tV, UV⟩ := h
  ⟨f ⁻¹' U, f ⁻¹' V, oU.preimage hf, oV.preimage hf, preimage_mono sU, preimage_mono tV,
    UV.preimage f⟩

/--
theorem `disjoint` / 定理 `disjoint`

English:
theorem disjoint
  given: (h : SeparatedNhds s t)
  statement: Disjoint s t
  proof: let ⟨_, _, _, _, hsU, htV, hd⟩ := h; hd.mono hsU htV

中文:
定理 disjoint
  条件: (h : SeparatedNhds s t)
  结论: Disjoint s t
  证明: let ⟨_, _, _, _, hsU, htV, hd⟩ := h; hd.mono hsU htV
-/
protected theorem disjoint (h : SeparatedNhds s t) : Disjoint s t :=
  let ⟨_, _, _, _, hsU, htV, hd⟩ := h; hd.mono hsU htV

/--
theorem `disjoint_closure_left` / 定理 `disjoint_closure_left`

English:
theorem disjoint_closure_left
  given: (h : SeparatedNhds s t)
  statement: Disjoint (closure s) t
  proof: let ⟨_U, _V, _, hV, hsU, htV, hd⟩ := h
  (hd.closure_left hV).mono (closure_mono hsU) htV

中文:
定理 disjoint_closure_left
  条件: (h : SeparatedNhds s t)
  结论: Disjoint (closure s) t
  证明: let ⟨_U, _V, _, hV, hsU, htV, hd⟩ := h
  (hd.closure_left hV).mono (closure_mono hsU) htV

Depends on / 依赖: closure_left, closure_mono, hd.closure_left
-/
theorem disjoint_closure_left (h : SeparatedNhds s t) : Disjoint (closure s) t :=
  let ⟨_U, _V, _, hV, hsU, htV, hd⟩ := h
  (hd.closure_left hV).mono (closure_mono hsU) htV

/--
theorem `disjoint_closure_right` / 定理 `disjoint_closure_right`

English:
theorem disjoint_closure_right
  given: (h : SeparatedNhds s t)
  statement: Disjoint s (closure t)
  proof: h.symm.disjoint_closure_left.symm

中文:
定理 disjoint_closure_right
  条件: (h : SeparatedNhds s t)
  结论: Disjoint s (closure t)
  证明: h.symm.disjoint_closure_left.symm

Depends on / 依赖: disjoint_closure_left, h.symm.disjoint_closure_left.symm
-/
theorem disjoint_closure_right (h : SeparatedNhds s t) : Disjoint s (closure t) :=
  h.symm.disjoint_closure_left.symm

/--
theorem `empty_right` / 定理 `empty_right`

English:
theorem empty_right
  given: (s : Set X)
  statement: SeparatedNhds s ∅
  proof: ⟨_, _, isOpen_univ, isOpen_empty, fun a _ => mem_univ a, Subset.rfl, disjoint_empty _⟩

中文:
定理 empty_right
  条件: (s : Set X)
  结论: SeparatedNhds s ∅
  证明: ⟨_, _, isOpen_univ, isOpen_empty, fun a _ => mem_univ a, Subset.rfl, disjoint_empty _⟩
-/
@[simp] theorem empty_right (s : Set X) : SeparatedNhds s ∅ :=
  ⟨_, _, isOpen_univ, isOpen_empty, fun a _ => mem_univ a, Subset.rfl, disjoint_empty _⟩

/--
theorem `empty_left` / 定理 `empty_left`

English:
theorem empty_left
  given: (s : Set X)
  statement: SeparatedNhds ∅ s
  proof: (empty_right _).symm

中文:
定理 empty_left
  条件: (s : Set X)
  结论: SeparatedNhds ∅ s
  证明: (empty_right _).symm
-/
@[simp] theorem empty_left (s : Set X) : SeparatedNhds ∅ s :=
  (empty_right _).symm

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (h : SeparatedNhds s₂ t₂) (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂)
  statement: SeparatedNhds s₁ t₁
  proof: let ⟨U, V, hU, hV, hsU, htV, hd⟩ := h
  ⟨U, V, hU, hV, hs.trans hsU, ht.trans htV, hd⟩

中文:
定理 mono
  条件: (h : SeparatedNhds s₂ t₂) (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂)
  结论: SeparatedNhds s₁ t₁
  证明: let ⟨U, V, hU, hV, hsU, htV, hd⟩ := h
  ⟨U, V, hU, hV, hs.trans hsU, ht.trans htV, hd⟩

Depends on / 依赖: hs.trans, ht.trans
-/
theorem mono (h : SeparatedNhds s₂ t₂) (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : SeparatedNhds s₁ t₁ :=
  let ⟨U, V, hU, hV, hsU, htV, hd⟩ := h
  ⟨U, V, hU, hV, hs.trans hsU, ht.trans htV, hd⟩

/--
theorem `union_left` / 定理 `union_left`

English:
theorem union_left
  statement: SeparatedNhds s u -> SeparatedNhds t u -> SeparatedNhds (s union t) u
  proof: by
  simpa only [separatedNhds_iff_disjoint, nhdsSet_union, disjoint_sup_left] using And.intro

中文:
定理 union_left
  结论: SeparatedNhds s u -> SeparatedNhds t u -> SeparatedNhds (s union t) u
  证明: by
  simpa only [separatedNhds_iff_disjoint, nhdsSet_union, disjoint_sup_left] using And.intro

Depends on / 依赖: And.intro, disjoint_sup_left, nhdsSet_union, separatedNhds_iff_disjoint
-/
theorem union_left : SeparatedNhds s u -> SeparatedNhds t u -> SeparatedNhds (s union t) u := by
  simpa only [separatedNhds_iff_disjoint, nhdsSet_union, disjoint_sup_left] using And.intro

/--
theorem `union_right` / 定理 `union_right`

English:
theorem union_right
  given: (ht : SeparatedNhds s t) (hu : SeparatedNhds s u)
  statement: SeparatedNhds s (t union u)
  proof: (ht.symm.union_left hu.symm).symm

中文:
定理 union_right
  条件: (ht : SeparatedNhds s t) (hu : SeparatedNhds s u)
  结论: SeparatedNhds s (t union u)
  证明: (ht.symm.union_left hu.symm).symm

Depends on / 依赖: ht.symm.union_left, hu.symm, union_left
-/
theorem union_right (ht : SeparatedNhds s t) (hu : SeparatedNhds s u) : SeparatedNhds s (t union u) :=
  (ht.symm.union_left hu.symm).symm

/--
lemma `isOpen_left_of_isOpen_union` / 引理 `isOpen_left_of_isOpen_union`

English:
lemma isOpen_left_of_isOpen_union
  given: (hst : SeparatedNhds s t) (hst' : IsOpen (s union t))
  statement: IsOpen s
  proof: by
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ := hst
  suffices s = (s union t) inter u from this ▸ hst'.inter hu
  rw [union_inter_distrib_right]; rw [(huv.symm.mono_left htv).inter_eq]; rw [union_empty]; rw [inter_eq_left.2 hsu]

中文:
引理 isOpen_left_of_isOpen_union
  条件: (hst : SeparatedNhds s t) (hst' : IsOpen (s union t))
  结论: IsOpen s
  证明: by
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ := hst
  suffices s = (s union t) inter u from this ▸ hst'.inter hu
  rw [union_inter_distrib_right]; rw [(huv.symm.mono_left htv).inter_eq]; rw [union_empty]; rw [inter_eq_left.2 hsu]

Depends on / 依赖: huv.symm.mono_left, inter_eq, inter_eq_left, mono_left, union_empty, union_inter_distrib_right
-/
lemma isOpen_left_of_isOpen_union (hst : SeparatedNhds s t) (hst' : IsOpen (s union t)) : IsOpen s := by
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ := hst
  suffices s = (s union t) inter u from this ▸ hst'.inter hu
  rw [union_inter_distrib_right]; rw [(huv.symm.mono_left htv).inter_eq]; rw [union_empty]; rw [inter_eq_left.2 hsu]

/--
lemma `isOpen_right_of_isOpen_union` / 引理 `isOpen_right_of_isOpen_union`

English:
lemma isOpen_right_of_isOpen_union
  given: (hst : SeparatedNhds s t) (hst' : IsOpen (s union t))
  statement: IsOpen t
  proof: hst.symm.isOpen_left_of_isOpen_union (union_comm _ _ ▸ hst')

中文:
引理 isOpen_right_of_isOpen_union
  条件: (hst : SeparatedNhds s t) (hst' : IsOpen (s union t))
  结论: IsOpen t
  证明: hst.symm.isOpen_left_of_isOpen_union (union_comm _ _ ▸ hst')

Depends on / 依赖: hst.symm.isOpen_left_of_isOpen_union, isOpen_left_of_isOpen_union, union_comm
-/
lemma isOpen_right_of_isOpen_union (hst : SeparatedNhds s t) (hst' : IsOpen (s union t)) : IsOpen t :=
  hst.symm.isOpen_left_of_isOpen_union (union_comm _ _ ▸ hst')

/--
lemma `isOpen_union_iff` / 引理 `isOpen_union_iff`

English:
lemma isOpen_union_iff
  given: (hst : SeparatedNhds s t)
  statement: IsOpen (s union t) ↔ IsOpen s ∧ IsOpen t
  proof: ⟨fun h => ⟨hst.isOpen_left_of_isOpen_union h, hst.isOpen_right_of_isOpen_union h⟩,
    fun ⟨h1, h2⟩ => h1.union h2⟩

中文:
引理 isOpen_union_iff
  条件: (hst : SeparatedNhds s t)
  结论: IsOpen (s union t) ↔ IsOpen s ∧ IsOpen t
  证明: ⟨fun h => ⟨hst.isOpen_left_of_isOpen_union h, hst.isOpen_right_of_isOpen_union h⟩,
    fun ⟨h1, h2⟩ => h1.union h2⟩

Depends on / 依赖: h1.union, hst.isOpen_left_of_isOpen_union, hst.isOpen_right_of_isOpen_union, isOpen_left_of_isOpen_union, isOpen_right_of_isOpen_union
-/
lemma isOpen_union_iff (hst : SeparatedNhds s t) : IsOpen (s union t) ↔ IsOpen s ∧ IsOpen t :=
  ⟨fun h => ⟨hst.isOpen_left_of_isOpen_union h, hst.isOpen_right_of_isOpen_union h⟩,
    fun ⟨h1, h2⟩ => h1.union h2⟩

/--
lemma `isClosed_left_of_isClosed_union` / 引理 `isClosed_left_of_isClosed_union`

English:
lemma isClosed_left_of_isClosed_union
  given: (hst : SeparatedNhds s t) (hst' : IsClosed (s union t))
  proof: by
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ := hst
  rw [← isOpen_compl_iff] at hst' ⊢
  suffices sᶜ = (s union t)ᶜ union v from this ▸ hst'.union hv
  rw [← compl_inj_iff]; rw [Set.compl_union]; rw [compl_compl]; rw [compl_compl]; rw [union_inter_distrib_right]; rw [(disjoint_compl_right.mono_left ht

中文:
引理 isClosed_left_of_isClosed_union
  条件: (hst : SeparatedNhds s t) (hst' : IsClosed (s union t))
  证明: by
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ := hst
  rw [← isOpen_compl_iff] at hst' ⊢
  suffices sᶜ = (s union t)ᶜ union v from this ▸ hst'.union hv
  rw [← compl_inj_iff]; rw [Set.compl_union]; rw [compl_compl]; rw [compl_compl]; rw [union_inter_distrib_right]; rw [(disjoint_compl_right.mono_left ht

Depends on / 依赖: Set.compl_union, compl_compl, compl_inj_iff, compl_union, disjoint_compl_right, disjoint_compl_right.mono_left, huv.mono_left, inter_eq, isOpen_compl_iff, left_eq_inter, mono_left, subset_compl_comm, subset_compl_left, union_empty, union_inter_distrib_right
-/
lemma isClosed_left_of_isClosed_union (hst : SeparatedNhds s t) (hst' : IsClosed (s union t)) :
    IsClosed s := by
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ := hst
  rw [← isOpen_compl_iff] at hst' ⊢
  suffices sᶜ = (s union t)ᶜ union v from this ▸ hst'.union hv
  rw [← compl_inj_iff]; rw [Set.compl_union]; rw [compl_compl]; rw [compl_compl]; rw [union_inter_distrib_right]; rw [(disjoint_compl_right.mono_left htv).inter_eq]; rw [union_empty]; rw [left_eq_inter]; rw [subset_compl_comm]
  exact (huv.mono_left hsu).subset_compl_left

/--
lemma `isClosed_right_of_isClosed_union` / 引理 `isClosed_right_of_isClosed_union`

English:
lemma isClosed_right_of_isClosed_union
  given: (hst : SeparatedNhds s t) (hst' : IsClosed (s union t))
  proof: hst.symm.isClosed_left_of_isClosed_union (union_comm _ _ ▸ hst')

中文:
引理 isClosed_right_of_isClosed_union
  条件: (hst : SeparatedNhds s t) (hst' : IsClosed (s union t))
  证明: hst.symm.isClosed_left_of_isClosed_union (union_comm _ _ ▸ hst')

Depends on / 依赖: hst.symm.isClosed_left_of_isClosed_union, isClosed_left_of_isClosed_union, union_comm
-/
lemma isClosed_right_of_isClosed_union (hst : SeparatedNhds s t) (hst' : IsClosed (s union t)) :
    IsClosed t :=
  hst.symm.isClosed_left_of_isClosed_union (union_comm _ _ ▸ hst')

/--
lemma `isClosed_union_iff` / 引理 `isClosed_union_iff`

English:
lemma isClosed_union_iff
  given: (hst : SeparatedNhds s t)
  statement: IsClosed (s union t) ↔ IsClosed s ∧ IsClosed t
  proof: ⟨fun h => ⟨hst.isClosed_left_of_isClosed_union h, hst.isClosed_right_of_isClosed_union h⟩,
    fun ⟨h1, h2⟩ => h1.union h2⟩

中文:
引理 isClosed_union_iff
  条件: (hst : SeparatedNhds s t)
  结论: IsClosed (s union t) ↔ IsClosed s ∧ IsClosed t
  证明: ⟨fun h => ⟨hst.isClosed_left_of_isClosed_union h, hst.isClosed_right_of_isClosed_union h⟩,
    fun ⟨h1, h2⟩ => h1.union h2⟩

Depends on / 依赖: h1.union, hst.isClosed_left_of_isClosed_union, hst.isClosed_right_of_isClosed_union, isClosed_left_of_isClosed_union, isClosed_right_of_isClosed_union
-/
lemma isClosed_union_iff (hst : SeparatedNhds s t) : IsClosed (s union t) ↔ IsClosed s ∧ IsClosed t :=
  ⟨fun h => ⟨hst.isClosed_left_of_isClosed_union h, hst.isClosed_right_of_isClosed_union h⟩,
    fun ⟨h1, h2⟩ => h1.union h2⟩

end SeparatedNhds

end Separation
