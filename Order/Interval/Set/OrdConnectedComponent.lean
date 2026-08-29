/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Data.Set.Lattice.Image

/-!
# Order connected components of a set

In this file we define `Set.ordConnectedComponent s x` to be the set of `y` such that
`Set.uIcc x y ⊆ s` and prove some basic facts about this definition. At the moment of writing,
this construction is used only to prove that any linear order with order topology is a T₅ space,
so we only add API needed for this lemma.
-/

@[expose] public section


open Interval Function OrderDual

namespace Set

variable {α : Type*} [LinearOrder α] {s t : Set α} {x y z : α}

/--
Definition of `ordConnectedComponent` / `ordConnectedComponent` 的定义

English:
definition ordConnectedComponent
  signature: (s : Set α) (x : α)
  body: { y | [[x, y]] subseteq s }

中文:
定义 ordConnectedComponent
  签名: (s : 集合 α) (x : α)
  定义体: { y | [[x, y]] subseteq s }

Depends on / 依赖: subseteq
-/
def ordConnectedComponent (s : Set α) (x : α) : Set α :=
  { y | [[x, y]] subseteq s }

/--
theorem `mem_ordConnectedComponent` / 定理 `mem_ordConnectedComponent`

English:
theorem mem_ordConnectedComponent
  statement: y in ordConnectedComponent s x ↔ [[x, y]] subseteq s
  proof: Iff.rfl

中文:
定理 mem_ordConnectedComponent
  结论: y in ordConnectedComponent s x ↔ [[x, y]] subseteq s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_ordConnectedComponent : y in ordConnectedComponent s x ↔ [[x, y]] subseteq s :=
  Iff.rfl

/--
theorem `dual_ordConnectedComponent` / 定理 `dual_ordConnectedComponent`

English:
theorem dual_ordConnectedComponent
  proof: ext (Surjective.forall toDual.surjective).2 fun x => by simp [mem_ordConnectedComponent]

中文:
定理 dual_ordConnectedComponent
  证明: ext (Surjective.forall toDual.surjective).2 fun x => by simp [mem_ordConnectedComponent]

Depends on / 依赖: Surjective, Surjective.forall, mem_ordConnectedComponent, surjective, toDual, toDual.surjective
-/
theorem dual_ordConnectedComponent :
    ordConnectedComponent (ofDual ⁻¹' s) (toDual x) = ofDual ⁻¹' ordConnectedComponent s x :=
ext (Surjective.forall toDual.surjective).2 fun x => by simp [mem_ordConnectedComponent]

/--
theorem `ordConnectedComponent_subset` / 定理 `ordConnectedComponent_subset`

English:
theorem ordConnectedComponent_subset
  statement: ordConnectedComponent s x subseteq s
  proof: fun _ hy =>
  hy right_mem_uIcc

中文:
定理 ordConnectedComponent_subset
  结论: ordConnectedComponent s x subseteq s
  证明: fun _ hy =>
  hy right_mem_uIcc
-/
theorem ordConnectedComponent_subset : ordConnectedComponent s x subseteq s := fun _ hy =>
  hy right_mem_uIcc

/--
theorem `subset_ordConnectedComponent` / 定理 `subset_ordConnectedComponent`

English:
theorem subset_ordConnectedComponent
  given: {t} [h : OrdConnected s] (hs : x in s) (ht : s subseteq t)
  proof: fun _ hy => (h.uIcc_subset hs hy).trans ht

@[simp]

中文:
定理 subset_ordConnectedComponent
  条件: {t} [h : 序连通 s] (hs : x in s) (ht : s subseteq t)
  证明: fun _ hy => (h.uIcc_subset hs hy).trans ht

@[simp]

Depends on / 依赖: h.uIcc_subset, uIcc_subset
-/
theorem subset_ordConnectedComponent {t} [h : OrdConnected s] (hs : x in s) (ht : s subseteq t) :
    s subseteq ordConnectedComponent t x := fun _ hy => (h.uIcc_subset hs hy).trans ht

@[simp]
/--
theorem `self_mem_ordConnectedComponent` / 定理 `self_mem_ordConnectedComponent`

English:
theorem self_mem_ordConnectedComponent
  statement: x in ordConnectedComponent s x ↔ x in s
  proof: by
  rw [mem_ordConnectedComponent]; rw [uIcc_self]; rw [singleton_subset_iff]

@[simp]

中文:
定理 self_mem_ordConnectedComponent
  结论: x in ordConnectedComponent s x ↔ x in s
  证明: by
  rw [mem_ordConnectedComponent]; rw [uIcc_self]; rw [singleton_subset_iff]

@[simp]

Depends on / 依赖: mem_ordConnectedComponent, singleton_subset_iff, uIcc_self
-/
theorem self_mem_ordConnectedComponent : x in ordConnectedComponent s x ↔ x in s := by
  rw [mem_ordConnectedComponent]; rw [uIcc_self]; rw [singleton_subset_iff]

@[simp]
/--
theorem `nonempty_ordConnectedComponent` / 定理 `nonempty_ordConnectedComponent`

English:
theorem nonempty_ordConnectedComponent
  statement: (ordConnectedComponent s x).Nonempty ↔ x in s
  proof: ⟨fun ⟨_, hy⟩ => hy left_mem_uIcc, fun h => ⟨x, self_mem_ordConnectedComponent.2 h⟩⟩

@[simp]

中文:
定理 nonempty_ordConnectedComponent
  结论: (ordConnectedComponent s x).非空 ↔ x in s
  证明: ⟨fun ⟨_, hy⟩ => hy left_mem_uIcc, fun h => ⟨x, self_mem_ordConnectedComponent.2 h⟩⟩

@[simp]

Depends on / 依赖: left_mem_uIcc, self_mem_ordConnectedComponent
-/
theorem nonempty_ordConnectedComponent : (ordConnectedComponent s x).Nonempty ↔ x in s :=
⟨fun ⟨_, hy⟩ => hy left_mem_uIcc, fun h => ⟨x, self_mem_ordConnectedComponent.2 h⟩⟩

@[simp]
/--
theorem `ordConnectedComponent_eq_empty` / 定理 `ordConnectedComponent_eq_empty`

English:
theorem ordConnectedComponent_eq_empty
  statement: ordConnectedComponent s x = ∅ ↔ x ∉ s
  proof: by
  rw [← not_nonempty_iff_eq_empty]; rw [nonempty_ordConnectedComponent]

@[simp]

中文:
定理 ordConnectedComponent_eq_empty
  结论: ordConnectedComponent s x = ∅ ↔ x ∉ s
  证明: by
  rw [← not_nonempty_iff_eq_empty]; rw [nonempty_ordConnectedComponent]

@[simp]

Depends on / 依赖: nonempty_ordConnectedComponent, not_nonempty_iff_eq_empty
-/
theorem ordConnectedComponent_eq_empty : ordConnectedComponent s x = ∅ ↔ x ∉ s := by
  rw [← not_nonempty_iff_eq_empty]; rw [nonempty_ordConnectedComponent]

@[simp]
/--
theorem `ordConnectedComponent_empty` / 定理 `ordConnectedComponent_empty`

English:
theorem ordConnectedComponent_empty
  statement: ordConnectedComponent ∅ x = ∅
  proof: ordConnectedComponent_eq_empty.2 (notMem_empty x)

@[simp]

中文:
定理 ordConnectedComponent_empty
  结论: ordConnectedComponent ∅ x = ∅
  证明: ordConnectedComponent_eq_empty.2 (notMem_empty x)

@[simp]

Depends on / 依赖: notMem_empty, ordConnectedComponent_eq_empty
-/
theorem ordConnectedComponent_empty : ordConnectedComponent ∅ x = ∅ :=
  ordConnectedComponent_eq_empty.2 (notMem_empty x)

@[simp]
/--
theorem `ordConnectedComponent_univ` / 定理 `ordConnectedComponent_univ`

English:
theorem ordConnectedComponent_univ
  statement: ordConnectedComponent univ x = univ
  proof: by
  simp [ordConnectedComponent]

中文:
定理 ordConnectedComponent_univ
  结论: ordConnectedComponent univ x = univ
  证明: by
  simp [ordConnectedComponent]

Depends on / 依赖: ordConnectedComponent
-/
theorem ordConnectedComponent_univ : ordConnectedComponent univ x = univ := by
  simp [ordConnectedComponent]

/--
theorem `ordConnectedComponent_inter` / 定理 `ordConnectedComponent_inter`

English:
theorem ordConnectedComponent_inter
  given: (s t : Set α) (x : α)
  proof: by
  simp [ordConnectedComponent, ofPred_and]

中文:
定理 ordConnectedComponent_inter
  条件: (s t : 集合 α) (x : α)
  证明: by
  simp [ordConnectedComponent, ofPred_and]

Depends on / 依赖: IsTwoSided, ofPred_and, ordConnectedComponent
-/
theorem ordConnectedComponent_inter (s t : Set α) (x : α) :
    ordConnectedComponent (s inter t) x = ordConnectedComponent s x inter ordConnectedComponent t x := by
  simp [ordConnectedComponent, ofPred_and]

/--
theorem `mem_ordConnectedComponent_comm` / 定理 `mem_ordConnectedComponent_comm`

English:
theorem mem_ordConnectedComponent_comm
  proof: by
  rw [mem_ordConnectedComponent]; rw [mem_ordConnectedComponent]; rw [uIcc_comm]

中文:
定理 mem_ordConnectedComponent_comm
  证明: by
  rw [mem_ordConnectedComponent]; rw [mem_ordConnectedComponent]; rw [uIcc_comm]

Depends on / 依赖: mem_ordConnectedComponent, uIcc_comm
-/
theorem mem_ordConnectedComponent_comm :
    y in ordConnectedComponent s x ↔ x in ordConnectedComponent s y := by
  rw [mem_ordConnectedComponent]; rw [mem_ordConnectedComponent]; rw [uIcc_comm]

/--
theorem `mem_ordConnectedComponent_trans` / 定理 `mem_ordConnectedComponent_trans`

English:
theorem mem_ordConnectedComponent_trans
  statement: (hxy : y in ordConnectedComponent s x)
  proof: calc
    [[x, z]] subseteq [[x, y]] union [[y, z]] := uIcc_subset_uIcc_union_uIcc
    _ subseteq s := union_subset hxy hyz

中文:
定理 mem_ordConnectedComponent_trans
  结论: (hxy : y in ordConnectedComponent s x)
  证明: calc
    [[x, z]] subseteq [[x, y]] union [[y, z]] := uIcc_subset_uIcc_union_uIcc
    _ subseteq s := union_subset hxy hyz

Depends on / 依赖: subseteq, uIcc_subset_uIcc_union_uIcc, union_subset
-/
theorem mem_ordConnectedComponent_trans (hxy : y in ordConnectedComponent s x)
    (hyz : z in ordConnectedComponent s y) : z in ordConnectedComponent s x :=
  calc
    [[x, z]] subseteq [[x, y]] union [[y, z]] := uIcc_subset_uIcc_union_uIcc
    _ subseteq s := union_subset hxy hyz

/--
theorem `ordConnectedComponent_eq` / 定理 `ordConnectedComponent_eq`

English:
theorem ordConnectedComponent_eq
  given: (h : [[x, y]] subseteq s)
  proof: ext fun _ =>
    ⟨mem_ordConnectedComponent_trans (mem_ordConnectedComponent_comm.2 h),
      mem_ordConnectedComponent_trans h⟩

中文:
定理 ordConnectedComponent_eq
  条件: (h : [[x, y]] subseteq s)
  证明: ext fun _ =>
    ⟨mem_ordConnectedComponent_trans (mem_ordConnectedComponent_comm.2 h),
      mem_ordConnectedComponent_trans h⟩

Depends on / 依赖: mem_ordConnectedComponent_comm, mem_ordConnectedComponent_trans
-/
theorem ordConnectedComponent_eq (h : [[x, y]] subseteq s) :
    ordConnectedComponent s x = ordConnectedComponent s y :=
  ext fun _ =>
    ⟨mem_ordConnectedComponent_trans (mem_ordConnectedComponent_comm.2 h),
      mem_ordConnectedComponent_trans h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrdConnected (ordConnectedComponent s x)
  body: ordConnected_of_uIcc_subset_left fun _ hy _ hz => (uIcc_subset_uIcc_left hz).trans hy

中文:
实例 :
  签名: 序连通 (ordConnectedComponent s x)
  定义体: ordConnected_of_uIcc_subset_left fun _ hy _ hz => (uIcc_subset_uIcc_left hz).trans hy

Depends on / 依赖: ordConnected_of_uIcc_subset_left, uIcc_subset_uIcc_left
-/
instance : OrdConnected (ordConnectedComponent s x) :=
  ordConnected_of_uIcc_subset_left fun _ hy _ hz => (uIcc_subset_uIcc_left hz).trans hy

/--
Definition of `ordConnectedProj` / `ordConnectedProj` 的定义

English:
definition ordConnectedProj
  signature: (s : Set α)
  body: fun x : s =>
  (nonempty_ordConnectedComponent.2 x.2).some

中文:
定义 ordConnectedProj
  签名: (s : 集合 α)
  定义体: fun x : s =>
  (nonempty_ordConnectedComponent.2 x.2).some
-/
noncomputable def ordConnectedProj (s : Set α) : s -> α := fun x : s =>
  (nonempty_ordConnectedComponent.2 x.2).some

/--
theorem `ordConnectedProj_mem_ordConnectedComponent` / 定理 `ordConnectedProj_mem_ordConnectedComponent`

English:
theorem ordConnectedProj_mem_ordConnectedComponent
  given: (s : Set α) (x : s)
  proof: Nonempty.some_mem _

中文:
定理 ordConnectedProj_mem_ordConnectedComponent
  条件: (s : 集合 α) (x : s)
  证明: Nonempty.some_mem _

Depends on / 依赖: Nonempty, Nonempty.some_mem, some_mem
-/
theorem ordConnectedProj_mem_ordConnectedComponent (s : Set α) (x : s) :
    ordConnectedProj s x in ordConnectedComponent s x :=
  Nonempty.some_mem _

/--
theorem `mem_ordConnectedComponent_ordConnectedProj` / 定理 `mem_ordConnectedComponent_ordConnectedProj`

English:
theorem mem_ordConnectedComponent_ordConnectedProj
  given: (s : Set α) (x : s)
  proof: mem_ordConnectedComponent_comm.2 ordConnectedProj_mem_ordConnectedComponent s x

@[simp]

中文:
定理 mem_ordConnectedComponent_ordConnectedProj
  条件: (s : 集合 α) (x : s)
  证明: mem_ordConnectedComponent_comm.2 ordConnectedProj_mem_ordConnectedComponent s x

@[simp]

Depends on / 依赖: mem_ordConnectedComponent_comm, ordConnectedProj_mem_ordConnectedComponent
-/
theorem mem_ordConnectedComponent_ordConnectedProj (s : Set α) (x : s) :
    ↑x in ordConnectedComponent s (ordConnectedProj s x) :=
mem_ordConnectedComponent_comm.2 ordConnectedProj_mem_ordConnectedComponent s x

@[simp]
/--
theorem `ordConnectedComponent_ordConnectedProj` / 定理 `ordConnectedComponent_ordConnectedProj`

English:
theorem ordConnectedComponent_ordConnectedProj
  given: (s : Set α) (x : s)
  proof: ordConnectedComponent_eq mem_ordConnectedComponent_ordConnectedProj _ _

@[simp]

中文:
定理 ordConnectedComponent_ordConnectedProj
  条件: (s : 集合 α) (x : s)
  证明: ordConnectedComponent_eq mem_ordConnectedComponent_ordConnectedProj _ _

@[simp]

Depends on / 依赖: mem_ordConnectedComponent_ordConnectedProj, ordConnectedComponent_eq
-/
theorem ordConnectedComponent_ordConnectedProj (s : Set α) (x : s) :
    ordConnectedComponent s (ordConnectedProj s x) = ordConnectedComponent s x :=
ordConnectedComponent_eq mem_ordConnectedComponent_ordConnectedProj _ _

@[simp]
/--
theorem `ordConnectedProj_eq` / 定理 `ordConnectedProj_eq`

English:
theorem ordConnectedProj_eq
  given: {x y : s}
  proof: by
  constructor <;> intro h
  · rw [← mem_ordConnectedComponent, ← ordConnectedComponent_ordConnectedProj, h,
      ordConnectedComponent_ordConnectedProj, self_mem_ordConnectedComponent]
    exact y.2
  · simp only [ordConnectedProj, ordConnectedComponent_eq h]

中文:
定理 ordConnectedProj_eq
  条件: {x y : s}
  证明: by
  constructor <;> intro h
  · rw [← mem_ordConnectedComponent, ← ordConnectedComponent_ordConnectedProj, h,
      ordConnectedComponent_ordConnectedProj, self_mem_ordConnectedComponent]
    exact y.2
  · simp only [ordConnectedProj, ordConnectedComponent_eq h]

Depends on / 依赖: mem_ordConnectedComponent, ordConnectedComponent_eq, ordConnectedComponent_ordConnectedProj, ordConnectedProj, self_mem_ordConnectedComponent
-/
theorem ordConnectedProj_eq {x y : s} :
    ordConnectedProj s x = ordConnectedProj s y ↔ [[(x : α), y]] subseteq s := by
  constructor <;> intro h
  · rw [← mem_ordConnectedComponent, ← ordConnectedComponent_ordConnectedProj, h,
      ordConnectedComponent_ordConnectedProj, self_mem_ordConnectedComponent]
    exact y.2
  · simp only [ordConnectedProj, ordConnectedComponent_eq h]

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `ordConnectedSection` / `ordConnectedSection` 的定义

English:
definition ordConnectedSection
  signature: (s : Set α)
  body: range ordConnectedProj s

中文:
定义 ordConnectedSection
  签名: (s : 集合 α)
  定义体: range ordConnectedProj s

Depends on / 依赖: ordConnectedProj
-/
noncomputable def ordConnectedSection (s : Set α) : Set α :=
range ordConnectedProj s

/--
theorem `dual_ordConnectedSection` / 定理 `dual_ordConnectedSection`

English:
theorem dual_ordConnectedSection
  given: (s : Set α)
  proof: by
  simp only [ordConnectedSection]
  simp +unfoldPartialApp only [ordConnectedProj]
  ext x
  simp only [mem_range, Subtype.exists, mem_preimage, OrderDual.exists, dual_ordConnectedComponent,
    ofDual_toDual]
  tauto

中文:
定理 dual_ordConnectedSection
  条件: (s : 集合 α)
  证明: by
  simp only [ordConnectedSection]
  simp +unfoldPartialApp only [ordConnectedProj]
  ext x
  simp only [mem_range, Subtype.exists, mem_preimage, OrderDual.exists, dual_ordConnectedComponent,
    ofDual_toDual]
  tauto

Depends on / 依赖: OrderDual, OrderDual.exists, Subtype, Subtype.exists, dual_ordConnectedComponent, mem_preimage, mem_range, ofDual_toDual, ordConnectedProj, ordConnectedSection, unfoldPartialApp
-/
theorem dual_ordConnectedSection (s : Set α) :
    ordConnectedSection (ofDual ⁻¹' s) = ofDual ⁻¹' ordConnectedSection s := by
  simp only [ordConnectedSection]
  simp +unfoldPartialApp only [ordConnectedProj]
  ext x
  simp only [mem_range, Subtype.exists, mem_preimage, OrderDual.exists, dual_ordConnectedComponent,
    ofDual_toDual]
  tauto

/--
theorem `ordConnectedSection_subset` / 定理 `ordConnectedSection_subset`

English:
theorem ordConnectedSection_subset
  statement: ordConnectedSection s subseteq s
  proof: range_subset_iff.2 fun _ => ordConnectedComponent_subset Nonempty.some_mem _

中文:
定理 ordConnectedSection_subset
  结论: ordConnectedSection s subseteq s
  证明: range_subset_iff.2 fun _ => ordConnectedComponent_subset Nonempty.some_mem _

Depends on / 依赖: Nonempty, Nonempty.some_mem, ordConnectedComponent_subset, range_subset_iff, some_mem
-/
theorem ordConnectedSection_subset : ordConnectedSection s subseteq s :=
range_subset_iff.2 fun _ => ordConnectedComponent_subset Nonempty.some_mem _

/--
theorem `eq_of_mem_ordConnectedSection_of_uIcc_subset` / 定理 `eq_of_mem_ordConnectedSection_of_uIcc_subset`

English:
theorem eq_of_mem_ordConnectedSection_of_uIcc_subset
  statement: (hx : x in ordConnectedSection s)
  proof: by
  rcases hx with ⟨x, rfl⟩; rcases hy with ⟨y, rfl⟩
  exact
    ordConnectedProj_eq.2
      (mem_ordConnectedComponent_trans
        (mem_ordConnectedComponent_trans (ordConnectedProj_mem_ordConnectedComponent _ _) h)
        (mem_ordConnectedComponent_ordConnectedProj _ _))

中文:
定理 eq_of_mem_ordConnectedSection_of_uIcc_subset
  结论: (hx : x in ordConnectedSection s)
  证明: by
  rcases hx with ⟨x, rfl⟩; rcases hy with ⟨y, rfl⟩
  exact
    ordConnectedProj_eq.2
      (mem_ordConnectedComponent_trans
        (mem_ordConnectedComponent_trans (ordConnectedProj_mem_ordConnectedComponent _ _) h)
        (mem_ordConnectedComponent_ordConnectedProj _ _))

Depends on / 依赖: mem_ordConnectedComponent_ordConnectedProj, mem_ordConnectedComponent_trans, ordConnectedProj_eq, ordConnectedProj_mem_ordConnectedComponent
-/
theorem eq_of_mem_ordConnectedSection_of_uIcc_subset (hx : x in ordConnectedSection s)
    (hy : y in ordConnectedSection s) (h : [[x, y]] subseteq s) : x = y := by
  rcases hx with ⟨x, rfl⟩; rcases hy with ⟨y, rfl⟩
  exact
    ordConnectedProj_eq.2
      (mem_ordConnectedComponent_trans
        (mem_ordConnectedComponent_trans (ordConnectedProj_mem_ordConnectedComponent _ _) h)
        (mem_ordConnectedComponent_ordConnectedProj _ _))

/--
Definition of `ordSeparatingSet` / `ordSeparatingSet` 的定义

English:
definition ordSeparatingSet
  signature: (s t : Set α)
  body: (⋃ x in s, ordConnectedComponent tᶜ x) inter ⋃ x in t, ordConnectedComponent sᶜ x

中文:
定义 ordSeparatingSet
  签名: (s t : 集合 α)
  定义体: (⋃ x in s, ordConnectedComponent tᶜ x) inter ⋃ x in t, ordConnectedComponent sᶜ x

Depends on / 依赖: ordConnectedComponent
-/
def ordSeparatingSet (s t : Set α) : Set α :=
  (⋃ x in s, ordConnectedComponent tᶜ x) inter ⋃ x in t, ordConnectedComponent sᶜ x

/--
theorem `ordSeparatingSet_comm` / 定理 `ordSeparatingSet_comm`

English:
theorem ordSeparatingSet_comm
  given: (s t : Set α)
  statement: ordSeparatingSet s t = ordSeparatingSet t s
  proof: inter_comm _ _

中文:
定理 ordSeparatingSet_comm
  条件: (s t : 集合 α)
  结论: ordSeparatingSet s t = ordSeparatingSet t s
  证明: inter_comm _ _

Depends on / 依赖: inter_comm
-/
theorem ordSeparatingSet_comm (s t : Set α) : ordSeparatingSet s t = ordSeparatingSet t s :=
  inter_comm _ _

/--
theorem `disjoint_left_ordSeparatingSet` / 定理 `disjoint_left_ordSeparatingSet`

English:
theorem disjoint_left_ordSeparatingSet
  statement: Disjoint s (ordSeparatingSet s t)
  proof: Disjoint.inter_right' _
    disjoint_iUnion₂_right.2 fun _ _ =>
disjoint_compl_right.mono_right ordConnectedComponent_subset

中文:
定理 disjoint_left_ordSeparatingSet
  结论: Disjoint s (ordSeparatingSet s t)
  证明: Disjoint.inter_right' _
    disjoint_iUnion₂_right.2 fun _ _ =>
disjoint_compl_right.mono_right ordConnectedComponent_subset

Depends on / 依赖: Disjoint, Disjoint.inter_right, disjoint_compl_right, disjoint_compl_right.mono_right, inter_right, mono_right, ordConnectedComponent_subset
-/
theorem disjoint_left_ordSeparatingSet : Disjoint s (ordSeparatingSet s t) :=
Disjoint.inter_right' _
    disjoint_iUnion₂_right.2 fun _ _ =>
disjoint_compl_right.mono_right ordConnectedComponent_subset

/--
theorem `disjoint_right_ordSeparatingSet` / 定理 `disjoint_right_ordSeparatingSet`

English:
theorem disjoint_right_ordSeparatingSet
  statement: Disjoint t (ordSeparatingSet s t)
  proof: ordSeparatingSet_comm t s ▸ disjoint_left_ordSeparatingSet

中文:
定理 disjoint_right_ordSeparatingSet
  结论: Disjoint t (ordSeparatingSet s t)
  证明: ordSeparatingSet_comm t s ▸ disjoint_left_ordSeparatingSet

Depends on / 依赖: disjoint_left_ordSeparatingSet, ordSeparatingSet_comm
-/
theorem disjoint_right_ordSeparatingSet : Disjoint t (ordSeparatingSet s t) :=
  ordSeparatingSet_comm t s ▸ disjoint_left_ordSeparatingSet

/--
theorem `dual_ordSeparatingSet` / 定理 `dual_ordSeparatingSet`

English:
theorem dual_ordSeparatingSet
  proof: by
  simp only [ordSeparatingSet, mem_preimage, ← toDual.surjective.iUnion_comp, ofDual_toDual,
    dual_ordConnectedComponent, ← preimage_compl, preimage_inter, preimage_iUnion]

中文:
定理 dual_ordSeparatingSet
  证明: by
  simp only [ordSeparatingSet, mem_preimage, ← toDual.surjective.iUnion_comp, ofDual_toDual,
    dual_ordConnectedComponent, ← preimage_compl, preimage_inter, preimage_iUnion]

Depends on / 依赖: dual_ordConnectedComponent, iUnion_comp, mem_preimage, ofDual_toDual, ordSeparatingSet, preimage_compl, preimage_iUnion, preimage_inter, surjective, toDual, toDual.surjective.iUnion_comp
-/
theorem dual_ordSeparatingSet :
    ordSeparatingSet (ofDual ⁻¹' s) (ofDual ⁻¹' t) = ofDual ⁻¹' ordSeparatingSet s t := by
  simp only [ordSeparatingSet, mem_preimage, ← toDual.surjective.iUnion_comp, ofDual_toDual,
    dual_ordConnectedComponent, ← preimage_compl, preimage_inter, preimage_iUnion]

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `ordT5Nhd` / `ordT5Nhd` 的定义

English:
definition ordT5Nhd
  signature: (s t : Set α)
  body: ⋃ x in s, ordConnectedComponent (tᶜ inter (ordConnectedSection <| ordSeparatingSet s t)ᶜ) x

中文:
定义 ordT5Nhd
  签名: (s t : 集合 α)
  定义体: ⋃ x in s, ordConnectedComponent (tᶜ inter (ordConnectedSection <| ordSeparatingSet s t)ᶜ) x

Depends on / 依赖: ordConnectedComponent, ordConnectedSection, ordSeparatingSet
-/
noncomputable def ordT5Nhd (s t : Set α) : Set α :=
  ⋃ x in s, ordConnectedComponent (tᶜ inter (ordConnectedSection <| ordSeparatingSet s t)ᶜ) x

/--
theorem `disjoint_ordT5Nhd` / 定理 `disjoint_ordT5Nhd`

English:
theorem disjoint_ordT5Nhd
  statement: Disjoint (ordT5Nhd s t) (ordT5Nhd t s)
  proof: by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx₁, hx₂⟩
  rcases mem_iUnion₂.1 hx₁ with ⟨a, has, ha⟩
  clear hx₁
  rcases mem_iUnion₂.1 hx₂ with ⟨b, hbt, hb⟩
  clear hx₂
  rw [mem_ordConnectedComponent]; rw [subset_inter_iff] at ha hb
  wlog hab : a <= b with H
  · exact H b hbt hb a has ha (le_of_not_ge hab)
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  have hsub : [[a, b]] subseteq (ordSeparatingSet s t).ordConnectedSectionᶜ := by
    rw [ordSeparatingSet_comm]; rw [uIcc_comm] at hb'
    calc
      [[a, b]] subseteq [[a, x]] union [[x, b]] := uIcc_subset_uIcc_union_uIcc
      _ subseteq (ordSeparatingSet s t).ordConnectedSectionᶜ := union_subset ha' hb'
  clear ha' hb'
  rcases le_total x a with hxa | hax
  · exact hb (Icc_subset_uIcc' ⟨hxa, hab⟩) has
  rcases le_total b x with hbx | hxb
  · exact ha (Icc_subset_uIcc ⟨hab, hbx⟩) hbt
  have h' : x in ordSeparatingSet s t := ⟨mem_iUnion₂.2 ⟨a, has, ha⟩, mem_iUnion₂.2 ⟨b, hbt, hb⟩⟩
  lift x to ordSeparatingSet s t using h'
  suffices ordConnectedComponent (ordSeparatingSet s t) x subseteq [[a, b]] from
    hsub (this <| ordConnectedProj_mem_ordConnectedComponent _ x) (mem_range_self _)
  rintro y hy
  rw [uIcc_of_le hab]; rw [mem_Icc]; rw [← not_lt]; rw [← not_lt]
  have sol1 := fun (hya : y < a) =>
      (disjoint_left (t := ordSeparatingSet s t)).1 disjoint_left_ordSeparatingSet has
        (hy <| Icc_subset_uIcc' ⟨hya.le, hax⟩)
  have sol2 := fun (hby : b < y) =>
      (disjoint_left (t := ordSeparatingSet s t)).1 disjoint_right_ordSeparatingSet hbt
        (hy <| Icc_subset_uIcc ⟨hxb, hby.le⟩)
  exact ⟨sol1, sol2⟩

中文:
定理 disjoint_ordT5Nhd
  结论: Disjoint (ordT5Nhd s t) (ordT5Nhd t s)
  证明: by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx₁, hx₂⟩
  rcases mem_iUnion₂.1 hx₁ with ⟨a, has, ha⟩
  clear hx₁
  rcases mem_iUnion₂.1 hx₂ with ⟨b, hbt, hb⟩
  clear hx₂
  rw [mem_ordConnectedComponent]; rw [subset_inter_iff] at ha hb
  wlog hab : a <= b with H
  · exact H b hbt hb a has ha (le_of_not_ge hab)
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  have hsub : [[a, b]] subseteq (ordSeparatingSet s t).ordConnectedSectionᶜ := by
    rw [ordSeparatingSet_comm]; rw [uIcc_comm] at hb'
    calc
      [[a, b]] subseteq [[a, x]] union [[x, b]] := uIcc_subset_uIcc_union_uIcc
      _ subseteq (ordSeparatingSet s t).ordConnectedSectionᶜ := union_subset ha' hb'
  clear ha' hb'
  rcases le_total x a with hxa | hax
  · exact hb (Icc_subset_uIcc' ⟨hxa, hab⟩) has
  rcases le_total b x with hbx | hxb
  · exact ha (Icc_subset_uIcc ⟨hab, hbx⟩) hbt
  have h' : x in ordSeparatingSet s t := ⟨mem_iUnion₂.2 ⟨a, has, ha⟩, mem_iUnion₂.2 ⟨b, hbt, hb⟩⟩
  lift x to ordSeparatingSet s t using h'
  suffices ordConnectedComponent (ordSeparatingSet s t) x subseteq [[a, b]] from
    hsub (this <| ordConnectedProj_mem_ordConnectedComponent _ x) (mem_range_self _)
  rintro y hy
  rw [uIcc_of_le hab]; rw [mem_Icc]; rw [← not_lt]; rw [← not_lt]
  have sol1 := fun (hya : y < a) =>
      (disjoint_left (t := ordSeparatingSet s t)).1 disjoint_left_ordSeparatingSet has
        (hy <| Icc_subset_uIcc' ⟨hya.le, hax⟩)
  have sol2 := fun (hby : b < y) =>
      (disjoint_left (t := ordSeparatingSet s t)).1 disjoint_right_ordSeparatingSet hbt
        (hy <| Icc_subset_uIcc ⟨hxb, hby.le⟩)
  exact ⟨sol1, sol2⟩

Depends on / 依赖: disjoint_iff_inf_le, le_of_not_ge, mem_ordConnectedComponent, ordSeparatingSet, ordSeparatingSet_comm, subset_inter_iff, subseteq, uIcc_comm
-/
theorem disjoint_ordT5Nhd : Disjoint (ordT5Nhd s t) (ordT5Nhd t s) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx₁, hx₂⟩
  rcases mem_iUnion₂.1 hx₁ with ⟨a, has, ha⟩
  clear hx₁
  rcases mem_iUnion₂.1 hx₂ with ⟨b, hbt, hb⟩
  clear hx₂
  rw [mem_ordConnectedComponent]; rw [subset_inter_iff] at ha hb
  wlog hab : a <= b with H
  · exact H b hbt hb a has ha (le_of_not_ge hab)
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  have hsub : [[a, b]] subseteq (ordSeparatingSet s t).ordConnectedSectionᶜ := by
    rw [ordSeparatingSet_comm]; rw [uIcc_comm] at hb'
    calc
      [[a, b]] subseteq [[a, x]] union [[x, b]] := uIcc_subset_uIcc_union_uIcc
      _ subseteq (ordSeparatingSet s t).ordConnectedSectionᶜ := union_subset ha' hb'
  clear ha' hb'
  rcases le_total x a with hxa | hax
  · exact hb (Icc_subset_uIcc' ⟨hxa, hab⟩) has
  rcases le_total b x with hbx | hxb
  · exact ha (Icc_subset_uIcc ⟨hab, hbx⟩) hbt
  have h' : x in ordSeparatingSet s t := ⟨mem_iUnion₂.2 ⟨a, has, ha⟩, mem_iUnion₂.2 ⟨b, hbt, hb⟩⟩
  lift x to ordSeparatingSet s t using h'
  suffices ordConnectedComponent (ordSeparatingSet s t) x subseteq [[a, b]] from
    hsub (this <| ordConnectedProj_mem_ordConnectedComponent _ x) (mem_range_self _)
  rintro y hy
  rw [uIcc_of_le hab]; rw [mem_Icc]; rw [← not_lt]; rw [← not_lt]
  have sol1 := fun (hya : y < a) =>
      (disjoint_left (t := ordSeparatingSet s t)).1 disjoint_left_ordSeparatingSet has
        (hy <| Icc_subset_uIcc' ⟨hya.le, hax⟩)
  have sol2 := fun (hby : b < y) =>
      (disjoint_left (t := ordSeparatingSet s t)).1 disjoint_right_ordSeparatingSet hbt
        (hy <| Icc_subset_uIcc ⟨hxb, hby.le⟩)
  exact ⟨sol1, sol2⟩

end Set
