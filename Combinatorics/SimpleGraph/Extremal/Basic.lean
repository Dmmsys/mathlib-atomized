/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Extremal graph theory

This file introduces basic definitions for extremal graph theory, including extremal numbers.

## Main definitions

* `SimpleGraph.IsExtremal` is the predicate that `G` has the maximum number of edges of any simple
  graph, with fixed vertices, satisfying `p`.

* `SimpleGraph.extremalNumber` is the maximum number of edges in a `H`-free simple graph on `n`
  vertices.

  If `H` is contained in all simple graphs on `n` vertices, then this is `0`.
-/

@[expose] public section

assert_not_exists Field

open Finset Fintype

namespace SimpleGraph

section IsExtremal

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/--
Definition of `IsExtremal` / `IsExtremal` 的定义

English:
definition IsExtremal
  signature: (G : SimpleGraph V) [DecidableRel G.Adj] (p : SimpleGraph V -> Prop)
  body: p G ∧ forall ⦃G' : SimpleGraph V⦄ [DecidableRel G'.Adj], p G' -> #G'.edgeFinset <= #G.edgeFinset

中文:
定义 IsExtremal
  签名: (G : SimpleGraph V) [DecidableRel G.Adj] (p : SimpleGraph V -> 命题)
  定义体: p G ∧ forall ⦃G' : SimpleGraph V⦄ [DecidableRel G'.Adj], p G' -> #G'.edgeFinset <= #G.edgeFinset

Depends on / 依赖: DecidableRel, G.edgeFinset, SimpleGraph, edgeFinset
-/
def IsExtremal (G : SimpleGraph V) [DecidableRel G.Adj] (p : SimpleGraph V -> Prop) :=
  p G ∧ forall ⦃G' : SimpleGraph V⦄ [DecidableRel G'.Adj], p G' -> #G'.edgeFinset <= #G.edgeFinset

/--
lemma `IsExtremal.prop` / 引理 `IsExtremal.prop`

English:
lemma IsExtremal.prop
  given: {p : SimpleGraph V -> Prop} (h : G.IsExtremal p)
  statement: p G
  proof: h.1

中文:
引理 IsExtremal.prop
  条件: {p : SimpleGraph V -> 命题} (h : G.IsExtremal p)
  结论: p G
  证明: h.1
-/
lemma IsExtremal.prop {p : SimpleGraph V -> Prop} (h : G.IsExtremal p) : p G := h.1

/--
theorem `exists_isExtremal_iff_exists` / 定理 `exists_isExtremal_iff_exists`

English:
theorem exists_isExtremal_iff_exists
  given: (p : SimpleGraph V -> Prop)
  proof: by
  classical
  refine ⟨fun ⟨_, _, h⟩ => ⟨_, h.1⟩, fun ⟨G, hp⟩ => ?_⟩
  obtain ⟨G', hp', h⟩ := by
    apply exists_max_image { G | p G } (#·.edgeFinset)
    use G, by simpa using hp
  use G', inferInstanceAs (DecidableRel G'.Adj)
  exact ⟨by simpa using hp', fun _ _ hp => by convert! h _ (by simpa 

中文:
定理 exists_isExtremal_iff_exists
  条件: (p : SimpleGraph V -> 命题)
  证明: by
  classical
  refine ⟨fun ⟨_, _, h⟩ => ⟨_, h.1⟩, fun ⟨G, hp⟩ => ?_⟩
  obtain ⟨G', hp', h⟩ := by
    apply exists_max_image { G | p G } (#·.edgeFinset)
    use G, by simpa using hp
  use G', inferInstanceAs (DecidableRel G'.Adj)
  exact ⟨by simpa using hp', fun _ _ hp => by convert! h _ (by simpa 

Depends on / 依赖: DecidableRel, classical, convert, edgeFinset, exists_max_image
-/
theorem exists_isExtremal_iff_exists (p : SimpleGraph V -> Prop) :
    (exists G : SimpleGraph V, exists _ : DecidableRel G.Adj, G.IsExtremal p) ↔ exists G, p G := by
  classical
  refine ⟨fun ⟨_, _, h⟩ => ⟨_, h.1⟩, fun ⟨G, hp⟩ => ?_⟩
  obtain ⟨G', hp', h⟩ := by
    apply exists_max_image { G | p G } (#·.edgeFinset)
    use G, by simpa using hp
  use G', inferInstanceAs (DecidableRel G'.Adj)
  exact ⟨by simpa using hp', fun _ _ hp => by convert! h _ (by simpa using hp)⟩

/--
theorem `exists_isExtremal_free` / 定理 `exists_isExtremal_free`

English:
theorem exists_isExtremal_free
  given: {W : Type*} {H : SimpleGraph W} (h : H != ⊥)
  proof: (exists_isExtremal_iff_exists H.Free).mpr ⟨⊥, free_bot h⟩

中文:
定理 exists_isExtremal_free
  条件: {W : 类型} {H : SimpleGraph W} (h : H != ⊥)
  证明: (exists_isExtremal_iff_exists H.Free).mpr ⟨⊥, free_bot h⟩

Depends on / 依赖: H.Free, exists_isExtremal_iff_exists, free_bot
-/
theorem exists_isExtremal_free {W : Type*} {H : SimpleGraph W} (h : H != ⊥) :
    exists G : SimpleGraph V, exists _ : DecidableRel G.Adj, G.IsExtremal H.Free :=
  (exists_isExtremal_iff_exists H.Free).mpr ⟨⊥, free_bot h⟩

open scoped Classical in
/--
theorem `IsExtremal.le_iff_eq` / 定理 `IsExtremal.le_iff_eq`

English:
theorem IsExtremal.le_iff_eq
  proof: ⟨fun hGH => edgeFinset_inj.1
    eq_of_subset_of_card_le (edgeFinset_subset_edgeFinset.2 hGH) (hG.2 hH), le_of_eq⟩

中文:
定理 IsExtremal.le_iff_eq
  证明: ⟨fun hGH => edgeFinset_inj.1
    eq_of_subset_of_card_le (edgeFinset_subset_edgeFinset.2 hGH) (hG.2 hH), le_of_eq⟩

Depends on / 依赖: edgeFinset_inj, edgeFinset_subset_edgeFinset, eq_of_subset_of_card_le, le_of_eq
-/
theorem IsExtremal.le_iff_eq
    {p : SimpleGraph V -> Prop} (hG : G.IsExtremal p) {H : SimpleGraph V} (hH : p H) :
    G <= H ↔ G = H :=
⟨fun hGH => edgeFinset_inj.1
    eq_of_subset_of_card_le (edgeFinset_subset_edgeFinset.2 hGH) (hG.2 hH), le_of_eq⟩

end IsExtremal

section ExtremalNumber

open scoped Classical in
/--
Definition of `extremalNumber` / `extremalNumber` 的定义

English:
definition extremalNumber
  signature: (n : Nat) {W : Type*} (H : SimpleGraph W)
  body: sup { G : SimpleGraph (Fin n) | H.Free G } (#·.edgeFinset)

中文:
定义 extremalNumber
  签名: (n : 自然数) {W : 类型} (H : SimpleGraph W)
  定义体: sup { G : SimpleGraph (Fin n) | H.Free G } (#·.edgeFinset)

Depends on / 依赖: H.Free, SimpleGraph, edgeFinset
-/
noncomputable def extremalNumber (n : Nat) {W : Type*} (H : SimpleGraph W) : Nat :=
  sup { G : SimpleGraph (Fin n) | H.Free G } (#·.edgeFinset)

variable {n : Nat} {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

open scoped Classical in
/--
theorem `extremalNumber_of_fintypeCard_eq` / 定理 `extremalNumber_of_fintypeCard_eq`

English:
theorem extremalNumber_of_fintypeCard_eq
  given: [Fintype V] (hc : card V = n)
  proof: by
  let e := Fintype.equivFinOfCardEq hc
  rw [extremalNumber]; rw [le_antisymm_iff]
  and_intros
  on_goal 1 =>
    replace e := e.symm
  all_goals
  rw [Finset.sup_le_iff]
  intro G h
  have h' : G.map e in univ.filter (H.Free ·) := by
    rw [mem_filter]; rw [← free_congr .refl (.map e G)]
    s

中文:
定理 extremalNumber_of_fintypeCard_eq
  条件: [Fintype V] (hc : card V = n)
  证明: by
  let e := Fintype.equivFinOfCardEq hc
  rw [extremalNumber]; rw [le_antisymm_iff]
  and_intros
  on_goal 1 =>
    replace e := e.symm
  all_goals
  rw [Finset.sup_le_iff]
  intro G h
  have h' : G.map e in univ.filter (H.Free ·) := by
    rw [mem_filter]; rw [← free_congr .refl (.map e G)]
    s

Depends on / 依赖: Finset, Finset.sup_le_iff, Fintype, Fintype.equivFinOfCardEq, G.map, H.Free, Iso.card_edgeFinset_eq, all_goals, and_intros, card_edgeFinset_eq, convert, e.symm, edgeFinset, equivFinOfCardEq, extremalNumber, filter, free_congr, le_antisymm_iff, le_sup, mem_filter
-/
theorem extremalNumber_of_fintypeCard_eq [Fintype V] (hc : card V = n) :
    extremalNumber n H = sup { G : SimpleGraph V | H.Free G } (#·.edgeFinset) := by
  let e := Fintype.equivFinOfCardEq hc
  rw [extremalNumber]; rw [le_antisymm_iff]
  and_intros
  on_goal 1 =>
    replace e := e.symm
  all_goals
  rw [Finset.sup_le_iff]
  intro G h
  have h' : G.map e in univ.filter (H.Free ·) := by
    rw [mem_filter]; rw [← free_congr .refl (.map e G)]
    simpa using h
  rw [Iso.card_edgeFinset_eq (.map e G)]
  convert! @le_sup _ _ _ _ {G | H.Free G} (#·.edgeFinset) _ h'

variable [Fintype V] [DecidableRel G.Adj]

/--
theorem `card_edgeFinset_le_extremalNumber` / 定理 `card_edgeFinset_le_extremalNumber`

English:
theorem card_edgeFinset_le_extremalNumber
  given: (h : H.Free G)
  proof: by
  rw [extremalNumber_of_fintypeCard_eq rfl]
  convert! @le_sup _ _ _ _ {G | H.Free G} (#·.edgeFinset) G (by simpa using h)

中文:
定理 card_edgeFinset_le_extremalNumber
  条件: (h : H.Free G)
  证明: by
  rw [extremalNumber_of_fintypeCard_eq rfl]
  convert! @le_sup _ _ _ _ {G | H.Free G} (#·.edgeFinset) G (by simpa using h)

Depends on / 依赖: H.Free, convert, edgeFinset, extremalNumber_of_fintypeCard_eq, le_sup
-/
theorem card_edgeFinset_le_extremalNumber (h : H.Free G) :
    #G.edgeFinset <= extremalNumber (card V) H := by
  rw [extremalNumber_of_fintypeCard_eq rfl]
  convert! @le_sup _ _ _ _ {G | H.Free G} (#·.edgeFinset) G (by simpa using h)

/--
theorem `IsContained.of_extremalNumber_lt_card_edgeFinset` / 定理 `IsContained.of_extremalNumber_lt_card_edgeFinset`

English:
theorem IsContained.of_extremalNumber_lt_card_edgeFinset
  proof: by
  contrapose h; push Not
  exact card_edgeFinset_le_extremalNumber h

中文:
定理 IsContained.of_extremalNumber_lt_card_edgeFinset
  证明: by
  contrapose h; push Not
  exact card_edgeFinset_le_extremalNumber h

Depends on / 依赖: card_edgeFinset_le_extremalNumber, contrapose
-/
theorem IsContained.of_extremalNumber_lt_card_edgeFinset
    (h : extremalNumber (card V) H < #G.edgeFinset) : H ⊑ G := by
  contrapose h; push Not
  exact card_edgeFinset_le_extremalNumber h

/--
theorem `extremalNumber_le_iff` / 定理 `extremalNumber_le_iff`

English:
theorem extremalNumber_le_iff
  given: (H : SimpleGraph W) (m : Nat)
  proof: by
  simp_rw [extremalNumber_of_fintypeCard_eq rfl, Finset.sup_le_iff, mem_filter_univ]
  exact ⟨fun h _ _ h' => by convert! h _ h', fun h _ h' => by convert! h h'⟩

中文:
定理 extremalNumber_le_iff
  条件: (H : SimpleGraph W) (m : 自然数)
  证明: by
  simp_rw [extremalNumber_of_fintypeCard_eq rfl, Finset.sup_le_iff, mem_filter_univ]
  exact ⟨fun h _ _ h' => by convert! h _ h', fun h _ h' => by convert! h h'⟩

Depends on / 依赖: Finset, Finset.sup_le_iff, convert, extremalNumber_of_fintypeCard_eq, mem_filter_univ, simp_rw, sup_le_iff
-/
theorem extremalNumber_le_iff (H : SimpleGraph W) (m : Nat) :
    extremalNumber (card V) H <= m ↔
      forall ⦃G : SimpleGraph V⦄ [DecidableRel G.Adj], H.Free G -> #G.edgeFinset <= m := by
  simp_rw [extremalNumber_of_fintypeCard_eq rfl, Finset.sup_le_iff, mem_filter_univ]
  exact ⟨fun h _ _ h' => by convert! h _ h', fun h _ h' => by convert! h h'⟩

/--
theorem `lt_extremalNumber_iff` / 定理 `lt_extremalNumber_iff`

English:
theorem lt_extremalNumber_iff
  given: (H : SimpleGraph W) (m : Nat)
  proof: by
  simp_rw [extremalNumber_of_fintypeCard_eq rfl, Finset.lt_sup_iff, mem_filter_univ]
  exact ⟨fun ⟨_, h, h'⟩ => ⟨_, _, h, h'⟩, fun ⟨_, _, h, h'⟩ => ⟨_, h, by convert!
    h'⟩⟩

中文:
定理 lt_extremalNumber_iff
  条件: (H : SimpleGraph W) (m : 自然数)
  证明: by
  simp_rw [extremalNumber_of_fintypeCard_eq rfl, Finset.lt_sup_iff, mem_filter_univ]
  exact ⟨fun ⟨_, h, h'⟩ => ⟨_, _, h, h'⟩, fun ⟨_, _, h, h'⟩ => ⟨_, h, by convert!
    h'⟩⟩

Depends on / 依赖: Finset, Finset.lt_sup_iff, convert, extremalNumber_of_fintypeCard_eq, lt_sup_iff, mem_filter_univ, simp_rw
-/
theorem lt_extremalNumber_iff (H : SimpleGraph W) (m : Nat) :
    m < extremalNumber (card V) H ↔
      exists G : SimpleGraph V, exists _ : DecidableRel G.Adj, H.Free G ∧ m < #G.edgeFinset := by
  simp_rw [extremalNumber_of_fintypeCard_eq rfl, Finset.lt_sup_iff, mem_filter_univ]
  exact ⟨fun ⟨_, h, h'⟩ => ⟨_, _, h, h'⟩, fun ⟨_, _, h, h'⟩ => ⟨_, h, by convert!
    h'⟩⟩

variable {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]

@[inherit_doc extremalNumber_le_iff]
/--
theorem `extremalNumber_le_iff_of_nonneg` / 定理 `extremalNumber_le_iff_of_nonneg`

English:
theorem extremalNumber_le_iff_of_nonneg
  given: (H : SimpleGraph W) {m : R} (h : 0 <= m)
  proof: by
  simp_rw [← Nat.le_floor_iff h]
  exact extremalNumber_le_iff H ⌊m⌋₊

@[inherit_doc lt_extremalNumber_iff]

中文:
定理 extremalNumber_le_iff_of_nonneg
  条件: (H : SimpleGraph W) {m : R} (h : 0 <= m)
  证明: by
  simp_rw [← Nat.le_floor_iff h]
  exact extremalNumber_le_iff H ⌊m⌋₊

@[inherit_doc lt_extremalNumber_iff]

Depends on / 依赖: Nat.le_floor_iff, extremalNumber_le_iff, le_floor_iff, simp_rw
-/
theorem extremalNumber_le_iff_of_nonneg (H : SimpleGraph W) {m : R} (h : 0 <= m) :
    extremalNumber (card V) H <= m ↔
      forall ⦃G : SimpleGraph V⦄ [DecidableRel G.Adj], H.Free G -> #G.edgeFinset <= m := by
  simp_rw [← Nat.le_floor_iff h]
  exact extremalNumber_le_iff H ⌊m⌋₊

@[inherit_doc lt_extremalNumber_iff]
/--
theorem `lt_extremalNumber_iff_of_nonneg` / 定理 `lt_extremalNumber_iff_of_nonneg`

English:
theorem lt_extremalNumber_iff_of_nonneg
  given: (H : SimpleGraph W) {m : R} (h : 0 <= m)
  proof: by
  simp_rw [← Nat.floor_lt h]
  exact lt_extremalNumber_iff H ⌊m⌋₊

中文:
定理 lt_extremalNumber_iff_of_nonneg
  条件: (H : SimpleGraph W) {m : R} (h : 0 <= m)
  证明: by
  simp_rw [← Nat.floor_lt h]
  exact lt_extremalNumber_iff H ⌊m⌋₊

Depends on / 依赖: Nat.floor_lt, floor_lt, lt_extremalNumber_iff, simp_rw
-/
theorem lt_extremalNumber_iff_of_nonneg (H : SimpleGraph W) {m : R} (h : 0 <= m) :
    m < extremalNumber (card V) H ↔
      exists G : SimpleGraph V, exists _ : DecidableRel G.Adj, H.Free G ∧ m < #G.edgeFinset := by
  simp_rw [← Nat.floor_lt h]
  exact lt_extremalNumber_iff H ⌊m⌋₊

/--
theorem `IsContained.extremalNumber_le` / 定理 `IsContained.extremalNumber_le`

English:
theorem IsContained.extremalNumber_le
  given: {W' : Type*} {H' : SimpleGraph W'} (h : H' ⊑ H)
  proof: by
  rw [← Fintype.card_fin n]; rw [extremalNumber_le_iff]
  intro _ _ h'
  contrapose! h'
  exact h.trans (IsContained.of_extremalNumber_lt_card_edgeFinset h')

中文:
定理 IsContained.extremalNumber_le
  条件: {W' : 类型} {H' : SimpleGraph W'} (h : H' ⊑ H)
  证明: by
  rw [← Fintype.card_fin n]; rw [extremalNumber_le_iff]
  intro _ _ h'
  contrapose! h'
  exact h.trans (IsContained.of_extremalNumber_lt_card_edgeFinset h')

Depends on / 依赖: Fintype, Fintype.card_fin, IsContained, IsContained.of_extremalNumber_lt_card_edgeFinset, card_fin, contrapose, extremalNumber_le_iff, h.trans, of_extremalNumber_lt_card_edgeFinset
-/
theorem IsContained.extremalNumber_le {W' : Type*} {H' : SimpleGraph W'} (h : H' ⊑ H) :
    extremalNumber n H' <= extremalNumber n H := by
  rw [← Fintype.card_fin n]; rw [extremalNumber_le_iff]
  intro _ _ h'
  contrapose! h'
  exact h.trans (IsContained.of_extremalNumber_lt_card_edgeFinset h')

/-- If `H₁ ≃g H₂`, then `extremalNumber n H₁` equals `extremalNumber n H₂`. -/
@[congr]
/--
theorem `extremalNumber_congr` / 定理 `extremalNumber_congr`

English:
theorem extremalNumber_congr
  statement: {n₁ n₂ : Nat} {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁}
  proof: by
  rw [h]; rw [le_antisymm_iff]
  and_intros
  on_goal 2 =>
    replace e := e.symm
  all_goals
    rw [← Fintype.card_fin n₂]; rw [extremalNumber_le_iff]
    intro G _ h
    apply card_edgeFinset_le_extremalNumber
    contrapose h
    exact h.trans' ⟨e.toCopy⟩

中文:
定理 extremalNumber_congr
  结论: {n₁ n₂ : 自然数} {W₁ W₂ : 类型} {H₁ : SimpleGraph W₁}
  证明: by
  rw [h]; rw [le_antisymm_iff]
  and_intros
  on_goal 2 =>
    replace e := e.symm
  all_goals
    rw [← Fintype.card_fin n₂]; rw [extremalNumber_le_iff]
    intro G _ h
    apply card_edgeFinset_le_extremalNumber
    contrapose h
    exact h.trans' ⟨e.toCopy⟩

Depends on / 依赖: Fintype, Fintype.card_fin, all_goals, and_intros, card_edgeFinset_le_extremalNumber, card_fin, contrapose, e.symm, e.toCopy, extremalNumber_le_iff, h.trans, le_antisymm_iff, on_goal, replace, toCopy
-/
theorem extremalNumber_congr {n₁ n₂ : Nat} {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁}
    {H₂ : SimpleGraph W₂} (h : n₁ = n₂) (e : H₁ ≃g H₂) :
    extremalNumber n₁ H₁ = extremalNumber n₂ H₂ := by
  rw [h]; rw [le_antisymm_iff]
  and_intros
  on_goal 2 =>
    replace e := e.symm
  all_goals
    rw [← Fintype.card_fin n₂]; rw [extremalNumber_le_iff]
    intro G _ h
    apply card_edgeFinset_le_extremalNumber
    contrapose h
    exact h.trans' ⟨e.toCopy⟩

/--
theorem `extremalNumber_congr_right` / 定理 `extremalNumber_congr_right`

English:
theorem extremalNumber_congr_right
  statement: {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
  proof: extremalNumber_congr rfl e

中文:
定理 extremalNumber_congr_right
  结论: {W₁ W₂ : 类型} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
  证明: extremalNumber_congr rfl e

Depends on / 依赖: extremalNumber_congr
-/
theorem extremalNumber_congr_right {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (e : H₁ ≃g H₂) : extremalNumber n H₁ = extremalNumber n H₂ := extremalNumber_congr rfl e

/--
theorem `isExtremal_free_iff` / 定理 `isExtremal_free_iff`

English:
theorem isExtremal_free_iff
  proof: by
  rw [IsExtremal]; rw [and_congr_right_iff]; rw [← extremalNumber_le_iff]
  exact fun h => ⟨eq_of_le_of_ge (card_edgeFinset_le_extremalNumber h), ge_of_eq⟩

中文:
定理 isExtremal_free_iff
  证明: by
  rw [IsExtremal]; rw [and_congr_right_iff]; rw [← extremalNumber_le_iff]
  exact fun h => ⟨eq_of_le_of_ge (card_edgeFinset_le_extremalNumber h), ge_of_eq⟩

Depends on / 依赖: IsExtremal, and_congr_right_iff, card_edgeFinset_le_extremalNumber, eq_of_le_of_ge, extremalNumber_le_iff, ge_of_eq
-/
theorem isExtremal_free_iff :
    G.IsExtremal H.Free ↔ H.Free G ∧ #G.edgeFinset = extremalNumber (card V) H := by
  rw [IsExtremal]; rw [and_congr_right_iff]; rw [← extremalNumber_le_iff]
  exact fun h => ⟨eq_of_le_of_ge (card_edgeFinset_le_extremalNumber h), ge_of_eq⟩

/--
lemma `card_edgeFinset_of_isExtremal_free` / 引理 `card_edgeFinset_of_isExtremal_free`

English:
lemma card_edgeFinset_of_isExtremal_free
  given: (h : G.IsExtremal H.Free)
  proof: (isExtremal_free_iff.mp h).2

中文:
引理 card_edgeFinset_of_isExtremal_free
  条件: (h : G.IsExtremal H.Free)
  证明: (isExtremal_free_iff.mp h).2

Depends on / 依赖: isExtremal_free_iff, isExtremal_free_iff.mp
-/
lemma card_edgeFinset_of_isExtremal_free (h : G.IsExtremal H.Free) :
    #G.edgeFinset = extremalNumber (card V) H := (isExtremal_free_iff.mp h).2

/--
theorem `card_edgeFinset_deleteIncidenceSet_le_extremalNumber` / 定理 `card_edgeFinset_deleteIncidenceSet_le_extremalNumber`

English:
theorem card_edgeFinset_deleteIncidenceSet_le_extremalNumber
  proof: by
  rw [← card_edgeFinset_induce_compl_singleton]; rw [← @card_unique ({v} : Set V)]; rw [← card_compl_set]
  apply card_edgeFinset_le_extremalNumber
  contrapose h
  exact h.trans ⟨Copy.induce G {v}ᶜ⟩

中文:
定理 card_edgeFinset_deleteIncidenceSet_le_extremalNumber
  证明: by
  rw [← card_edgeFinset_induce_compl_singleton]; rw [← @card_unique ({v} : Set V)]; rw [← card_compl_set]
  apply card_edgeFinset_le_extremalNumber
  contrapose h
  exact h.trans ⟨Copy.induce G {v}ᶜ⟩

Depends on / 依赖: Copy.induce, card_compl_set, card_edgeFinset_induce_compl_singleton, card_edgeFinset_le_extremalNumber, card_unique, contrapose, h.trans, induce
-/
theorem card_edgeFinset_deleteIncidenceSet_le_extremalNumber
    [DecidableEq V] (h : H.Free G) (v : V) :
    #(G.deleteIncidenceSet v).edgeFinset <= extremalNumber (card V - 1) H := by
  rw [← card_edgeFinset_induce_compl_singleton]; rw [← @card_unique ({v} : Set V)]; rw [← card_compl_set]
  apply card_edgeFinset_le_extremalNumber
  contrapose h
  exact h.trans ⟨Copy.induce G {v}ᶜ⟩

end ExtremalNumber

end SimpleGraph
