/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen, Patrick Massot, Wen Yang, Johan Commelin
-/
module

public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Partition.Finpartition

/-!
# Equivalence relations: partitions

This file comprises properties of equivalence relations viewed as partitions.
There are two implementations of partitions here:
* A collection `c : Set (Set α)` of sets is a partition of `α` if `∅ ∉ c` and each element `a : α`
  belongs to a unique set `b ∈ c`. This is expressed as `IsPartition c`
* An indexed partition is a map `s : ι → Set α` whose image is a partition. This is
  expressed as `IndexedPartition s`.

Of course both implementations are related to `Quotient` and `Setoid`.

`Setoid.isPartition.partition` and `Finpartition.isPartition_parts` furnish
a link between `Setoid.IsPartition` and `Finpartition`.

## TODO

Could the design of `Finpartition` inform the one of `Setoid.IsPartition`? Maybe bundling it and
changing it from `Set (Set α)` to `Set α` where `[Lattice α] [OrderBot α]` would make it more
usable.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation, partition, equivalence class
-/

@[expose] public section


namespace Setoid

variable {α : Type*}

/--
theorem `eq_of_mem_eqv_class` / 定理 `eq_of_mem_eqv_class`

English:
theorem eq_of_mem_eqv_class
  statement: {c : Set (Set α)} (H : forall a, exists! b in c, a in b) {x b b'}
  proof: (H x).unique ⟨hc, hb⟩ ⟨hc', hb'⟩

中文:
定理 eq_of_mem_eqv_class
  结论: {c : 集合 (集合 α)} (H : 对任意 a, 存在! b in c, a in b) {x b b'}
  证明: (H x).unique ⟨hc, hb⟩ ⟨hc', hb'⟩

Depends on / 依赖: unique
-/
theorem eq_of_mem_eqv_class {c : Set (Set α)} (H : forall a, exists! b in c, a in b) {x b b'}
    (hc : b in c) (hb : x in b) (hc' : b' in c) (hb' : x in b') : b = b' :=
  (H x).unique ⟨hc, hb⟩ ⟨hc', hb'⟩

/-- Makes an equivalence relation from a set of sets partitioning α. -/
@[instance_reducible]
/--
Definition of `mkClasses` / `mkClasses` 的定义

English:
definition mkClasses
  signature: (c : Set (Set α)) (H : forall a, exists! b in c, a in b)
  body: forall s in c, x in s -> y in s
  iseqv.refl := fun _ _ _ hx => hx
  iseqv.symm := fun {x _y} h s hs hy => by
    obtain ⟨t, ⟨ht, hx⟩, _⟩ := H x
    rwa [eq_of_mem_eqv_class H hs hy ht (h t ht hx)]
  iseqv.trans := fun {_x _ _} h1 h2 s hs hx => h2 s hs (h1 s hs hx)

中文:
定义 mkClasses
  签名: (c : 集合 (集合 α)) (H : 对任意 a, 存在! b in c, a in b)
  定义体: forall s in c, x in s -> y in s
  iseqv.refl := fun _ _ _ hx => hx
  iseqv.symm := fun {x _y} h s hs hy => by
    obtain ⟨t, ⟨ht, hx⟩, _⟩ := H x
    rwa [eq_of_mem_eqv_class H hs hy ht (h t ht hx)]
  iseqv.trans := fun {_x _ _} h1 h2 s hs hx => h2 s hs (h1 s hs hx)
-/
def mkClasses (c : Set (Set α)) (H : forall a, exists! b in c, a in b) : Setoid α where
  r x y := forall s in c, x in s -> y in s
  iseqv.refl := fun _ _ _ hx => hx
  iseqv.symm := fun {x _y} h s hs hy => by
    obtain ⟨t, ⟨ht, hx⟩, _⟩ := H x
    rwa [eq_of_mem_eqv_class H hs hy ht (h t ht hx)]
  iseqv.trans := fun {_x _ _} h1 h2 s hs hx => h2 s hs (h1 s hs hx)

/--
Definition of `classes` / `classes` 的定义

English:
definition classes
  signature: (r : Setoid α)
  body: { s | exists y, s = { x | r x y } }

中文:
定义 classes
  签名: (r : 集合等价关系 α)
  定义体: { s | exists y, s = { x | r x y } }
-/
def classes (r : Setoid α) : Set (Set α) :=
  { s | exists y, s = { x | r x y } }

/--
theorem `mem_classes` / 定理 `mem_classes`

English:
theorem mem_classes
  given: (r : Setoid α) (y)
  statement: { x | r x y } in r.classes
  proof: ⟨y, rfl⟩

中文:
定理 mem_classes
  条件: (r : 集合等价关系 α) (y)
  结论: { x | r x y } in r.classes
  证明: ⟨y, rfl⟩
-/
theorem mem_classes (r : Setoid α) (y) : { x | r x y } in r.classes :=
  ⟨y, rfl⟩

/--
theorem `classes_ker_subset_fiber_set` / 定理 `classes_ker_subset_fiber_set`

English:
theorem classes_ker_subset_fiber_set
  given: {β : Type*} (f : α -> β)
  proof: by
  rintro s ⟨x, rfl⟩
  rw [Set.mem_range]
  exact ⟨f x, rfl⟩

中文:
定理 classes_ker_subset_fiber_set
  条件: {β : 类型} (f : α -> β)
  证明: by
  rintro s ⟨x, rfl⟩
  rw [Set.mem_range]
  exact ⟨f x, rfl⟩

Depends on / 依赖: Set.mem_range, mem_range
-/
theorem classes_ker_subset_fiber_set {β : Type*} (f : α -> β) :
    (Setoid.ker f).classes subseteq Set.range fun y => { x | f x = y } := by
  rintro s ⟨x, rfl⟩
  rw [Set.mem_range]
  exact ⟨f x, rfl⟩

/--
theorem `finite_classes_ker` / 定理 `finite_classes_ker`

English:
theorem finite_classes_ker
  given: {α β : Type*} [Finite β] (f : α -> β)
  statement: (Setoid.ker f).classes.Finite
  proof: (Set.finite_range _).subset classes_ker_subset_fiber_set f

中文:
定理 finite_classes_ker
  条件: {α β : 类型} [有限 β] (f : α -> β)
  结论: (集合等价关系.ker f).classes.有限
  证明: (Set.finite_range _).subset classes_ker_subset_fiber_set f

Depends on / 依赖: Set.finite_range, classes_ker_subset_fiber_set, finite_range, subset
-/
theorem finite_classes_ker {α β : Type*} [Finite β] (f : α -> β) : (Setoid.ker f).classes.Finite :=
(Set.finite_range _).subset classes_ker_subset_fiber_set f

/--
theorem `card_classes_ker_le` / 定理 `card_classes_ker_le`

English:
theorem card_classes_ker_le
  statement: {α β : Type*} [Fintype β] (f : α -> β)
  proof: by
  exact
      le_trans (Set.card_le_card (classes_ker_subset_fiber_set f)) (Fintype.card_range_le _)

中文:
定理 card_classes_ker_le
  结论: {α β : 类型} [有限类型 β] (f : α -> β)
  证明: by
  exact
      le_trans (Set.card_le_card (classes_ker_subset_fiber_set f)) (Fintype.card_range_le _)

Depends on / 依赖: Fintype, Fintype.card_range_le, Set.card_le_card, card_le_card, card_range_le, classes_ker_subset_fiber_set, le_trans
-/
theorem card_classes_ker_le {α β : Type*} [Fintype β] (f : α -> β)
    [Fintype (Setoid.ker f).classes] : Fintype.card (Setoid.ker f).classes <= Fintype.card β := by
  exact
      le_trans (Set.card_le_card (classes_ker_subset_fiber_set f)) (Fintype.card_range_le _)

/--
theorem `eq_iff_classes_eq` / 定理 `eq_iff_classes_eq`

English:
theorem eq_iff_classes_eq
  given: {r₁ r₂ : Setoid α}
  proof: ⟨fun h _x => h ▸ rfl, fun h => ext fun x => Set.ext_iff.1 h x⟩

中文:
定理 eq_iff_classes_eq
  条件: {r₁ r₂ : 集合等价关系 α}
  证明: ⟨fun h _x => h ▸ rfl, fun h => ext fun x => Set.ext_iff.1 h x⟩

Depends on / 依赖: Set.ext_iff, ext_iff
-/
theorem eq_iff_classes_eq {r₁ r₂ : Setoid α} :
    r₁ = r₂ ↔ forall x, { y | r₁ x y } = { y | r₂ x y } :=
⟨fun h _x => h ▸ rfl, fun h => ext fun x => Set.ext_iff.1 h x⟩

/--
theorem `rel_iff_exists_classes` / 定理 `rel_iff_exists_classes`

English:
theorem rel_iff_exists_classes
  given: (r : Setoid α) {x y}
  statement: r x y ↔ exists c in r.classes, x in c ∧ y in c
  proof: ⟨fun h => ⟨_, r.mem_classes y, h, r.refl' y⟩, fun ⟨c, ⟨z, hz⟩, hx, hy⟩ => by
    subst c
    exact r.trans' hx (r.symm' hy)⟩

中文:
定理 rel_iff_存在_classes
  条件: (r : 集合等价关系 α) {x y}
  结论: r x y ↔ 存在 c in r.classes, x in c ∧ y in c
  证明: ⟨fun h => ⟨_, r.mem_classes y, h, r.refl' y⟩, fun ⟨c, ⟨z, hz⟩, hx, hy⟩ => by
    subst c
    exact r.trans' hx (r.symm' hy)⟩

Depends on / 依赖: mem_classes, r.mem_classes, r.refl, r.symm, r.trans
-/
theorem rel_iff_exists_classes (r : Setoid α) {x y} : r x y ↔ exists c in r.classes, x in c ∧ y in c :=
  ⟨fun h => ⟨_, r.mem_classes y, h, r.refl' y⟩, fun ⟨c, ⟨z, hz⟩, hx, hy⟩ => by
    subst c
    exact r.trans' hx (r.symm' hy)⟩

/--
theorem `classes_inj` / 定理 `classes_inj`

English:
theorem classes_inj
  given: {r₁ r₂ : Setoid α}
  statement: r₁ = r₂ ↔ r₁.classes = r₂.classes
  proof: ⟨fun h => h ▸ rfl, fun h => ext fun a b => by simp only [rel_iff_exists_classes, h]⟩

中文:
定理 classes_inj
  条件: {r₁ r₂ : 集合等价关系 α}
  结论: r₁ = r₂ ↔ r₁.classes = r₂.classes
  证明: ⟨fun h => h ▸ rfl, fun h => ext fun a b => by simp only [rel_iff_exists_classes, h]⟩

Depends on / 依赖: rel_iff_exists_classes
-/
theorem classes_inj {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ r₁.classes = r₂.classes :=
  ⟨fun h => h ▸ rfl, fun h => ext fun a b => by simp only [rel_iff_exists_classes, h]⟩

/--
theorem `empty_notMem_classes` / 定理 `empty_notMem_classes`

English:
theorem empty_notMem_classes
  given: {r : Setoid α}
  statement: ∅ ∉ r.classes
  proof: fun ⟨y, hy⟩ =>
Set.notMem_empty y hy.symm ▸ r.refl' y

中文:
定理 empty_notMem_classes
  条件: {r : 集合等价关系 α}
  结论: ∅ ∉ r.classes
  证明: fun ⟨y, hy⟩ =>
Set.notMem_empty y hy.symm ▸ r.refl' y
-/
theorem empty_notMem_classes {r : Setoid α} : ∅ ∉ r.classes := fun ⟨y, hy⟩ =>
Set.notMem_empty y hy.symm ▸ r.refl' y

/--
theorem `classes_eqv_classes` / 定理 `classes_eqv_classes`

English:
theorem classes_eqv_classes
  given: {r : Setoid α} (a)
  statement: exists! b in r.classes, a in b
  proof: ExistsUnique.intro { x | r x a } ⟨r.mem_classes a, r.refl' _⟩ by
    rintro y ⟨⟨_, rfl⟩, ha⟩
    ext x
    exact ⟨fun hx => r.trans' hx (r.symm' ha), fun hx => r.trans' hx ha⟩

中文:
定理 classes_eqv_classes
  条件: {r : 集合等价关系 α} (a)
  结论: 存在! b in r.classes, a in b
  证明: ExistsUnique.intro { x | r x a } ⟨r.mem_classes a, r.refl' _⟩ by
    rintro y ⟨⟨_, rfl⟩, ha⟩
    ext x
    exact ⟨fun hx => r.trans' hx (r.symm' ha), fun hx => r.trans' hx ha⟩

Depends on / 依赖: ExistsUnique, ExistsUnique.intro, mem_classes, r.mem_classes, r.refl, r.symm, r.trans
-/
theorem classes_eqv_classes {r : Setoid α} (a) : exists! b in r.classes, a in b :=
ExistsUnique.intro { x | r x a } ⟨r.mem_classes a, r.refl' _⟩ by
    rintro y ⟨⟨_, rfl⟩, ha⟩
    ext x
    exact ⟨fun hx => r.trans' hx (r.symm' ha), fun hx => r.trans' hx ha⟩

/--
theorem `eq_of_mem_classes` / 定理 `eq_of_mem_classes`

English:
theorem eq_of_mem_classes
  statement: {r : Setoid α} {x b} (hc : b in r.classes) (hb : x in b) {b'}
  proof: eq_of_mem_eqv_class classes_eqv_classes hc hb hc' hb'

中文:
定理 eq_of_mem_classes
  结论: {r : 集合等价关系 α} {x b} (hc : b in r.classes) (hb : x in b) {b'}
  证明: eq_of_mem_eqv_class classes_eqv_classes hc hb hc' hb'

Depends on / 依赖: classes_eqv_classes, eq_of_mem_eqv_class
-/
theorem eq_of_mem_classes {r : Setoid α} {x b} (hc : b in r.classes) (hb : x in b) {b'}
    (hc' : b' in r.classes) (hb' : x in b') : b = b' :=
  eq_of_mem_eqv_class classes_eqv_classes hc hb hc' hb'

/--
theorem `eq_eqv_class_of_mem` / 定理 `eq_eqv_class_of_mem`

English:
theorem eq_eqv_class_of_mem
  statement: {c : Set (Set α)} (H : forall a, exists! b in c, a in b) {s y}
  proof: by
  ext x
  constructor
  · intro hx _s' hs' hx'
    rwa [eq_of_mem_eqv_class H hs' hx' hs hx]
  · intro hx
    obtain ⟨b', ⟨hc, hb'⟩, _⟩ := H x
    rwa [eq_of_mem_eqv_class H hs hy hc (hx b' hc hb')]

中文:
定理 eq_eqv_class_of_mem
  结论: {c : 集合 (集合 α)} (H : 对任意 a, 存在! b in c, a in b) {s y}
  证明: by
  ext x
  constructor
  · intro hx _s' hs' hx'
    rwa [eq_of_mem_eqv_class H hs' hx' hs hx]
  · intro hx
    obtain ⟨b', ⟨hc, hb'⟩, _⟩ := H x
    rwa [eq_of_mem_eqv_class H hs hy hc (hx b' hc hb')]

Depends on / 依赖: eq_of_mem_eqv_class
-/
theorem eq_eqv_class_of_mem {c : Set (Set α)} (H : forall a, exists! b in c, a in b) {s y}
    (hs : s in c) (hy : y in s) : s = { x | mkClasses c H x y } := by
  ext x
  constructor
  · intro hx _s' hs' hx'
    rwa [eq_of_mem_eqv_class H hs' hx' hs hx]
  · intro hx
    obtain ⟨b', ⟨hc, hb'⟩, _⟩ := H x
    rwa [eq_of_mem_eqv_class H hs hy hc (hx b' hc hb')]

/--
theorem `eqv_class_mem` / 定理 `eqv_class_mem`

English:
theorem eqv_class_mem
  given: {c : Set (Set α)} (H : forall a, exists! b in c, a in b) {y}
  proof: (H y).elim fun _ hc _ => eq_eqv_class_of_mem H hc.1 hc.2 ▸ hc.1

中文:
定理 eqv_class_mem
  条件: {c : 集合 (集合 α)} (H : 对任意 a, 存在! b in c, a in b) {y}
  证明: (H y).elim fun _ hc _ => eq_eqv_class_of_mem H hc.1 hc.2 ▸ hc.1

Depends on / 依赖: eq_eqv_class_of_mem
-/
theorem eqv_class_mem {c : Set (Set α)} (H : forall a, exists! b in c, a in b) {y} :
    { x | mkClasses c H x y } in c :=
  (H y).elim fun _ hc _ => eq_eqv_class_of_mem H hc.1 hc.2 ▸ hc.1

/--
theorem `eqv_class_mem'` / 定理 `eqv_class_mem'`

English:
theorem eqv_class_mem'
  given: {c : Set (Set α)} (H : forall a, exists! b in c, a in b) {x}
  proof: by
  convert! @Setoid.eqv_class_mem _ _ H x using 3
  rw [Setoid.comm']

中文:
定理 eqv_class_mem'
  条件: {c : 集合 (集合 α)} (H : 对任意 a, 存在! b in c, a in b) {x}
  证明: by
  convert! @Setoid.eqv_class_mem _ _ H x using 3
  rw [Setoid.comm']

Depends on / 依赖: Setoid, Setoid.comm, Setoid.eqv_class_mem, convert, eqv_class_mem
-/
theorem eqv_class_mem' {c : Set (Set α)} (H : forall a, exists! b in c, a in b) {x} :
    { y : α | mkClasses c H x y } in c := by
  convert! @Setoid.eqv_class_mem _ _ H x using 3
  rw [Setoid.comm']

/--
theorem `eqv_classes_disjoint` / 定理 `eqv_classes_disjoint`

English:
theorem eqv_classes_disjoint
  given: {c : Set (Set α)} (H : forall a, exists! b in c, a in b)
  proof: fun _b₁ h₁ _b₂ h₂ h =>
  Set.disjoint_left.2 fun x hx1 hx2 =>
(H x).elim fun _b _hc _hx => h eq_of_mem_eqv_class H h₁ hx1 h₂ hx2

中文:
定理 eqv_classes_disjoint
  条件: {c : 集合 (集合 α)} (H : 对任意 a, 存在! b in c, a in b)
  证明: fun _b₁ h₁ _b₂ h₂ h =>
  Set.disjoint_left.2 fun x hx1 hx2 =>
(H x).elim fun _b _hc _hx => h eq_of_mem_eqv_class H h₁ hx1 h₂ hx2
-/
theorem eqv_classes_disjoint {c : Set (Set α)} (H : forall a, exists! b in c, a in b) :
    c.PairwiseDisjoint id := fun _b₁ h₁ _b₂ h₂ h =>
  Set.disjoint_left.2 fun x hx1 hx2 =>
(H x).elim fun _b _hc _hx => h eq_of_mem_eqv_class H h₁ hx1 h₂ hx2

/--
theorem `eqv_classes_of_disjoint_union` / 定理 `eqv_classes_of_disjoint_union`

English:
theorem eqv_classes_of_disjoint_union
  statement: {c : Set (Set α)} (hu : Set.sUnion c = @Set.univ α)
  proof: let ⟨b, hc, ha⟩ := Set.mem_sUnion.1 show a in _ by rw [hu]; exact Set.mem_univ a
  ExistsUnique.intro b ⟨hc, ha⟩ fun _ hc' => H.elim_set hc'.1 hc _ hc'.2 ha

中文:
定理 eqv_classes_of_disjoint_union
  结论: {c : 集合 (集合 α)} (hu : 集合.集合并集 c = @集合.univ α)
  证明: let ⟨b, hc, ha⟩ := Set.mem_sUnion.1 show a in _ by rw [hu]; exact Set.mem_univ a
  ExistsUnique.intro b ⟨hc, ha⟩ fun _ hc' => H.elim_set hc'.1 hc _ hc'.2 ha

Depends on / 依赖: ExistsUnique, ExistsUnique.intro, H.elim_set, Set.mem_sUnion, Set.mem_univ, elim_set, mem_sUnion, mem_univ
-/
theorem eqv_classes_of_disjoint_union {c : Set (Set α)} (hu : Set.sUnion c = @Set.univ α)
    (H : c.PairwiseDisjoint id) (a) : exists! b in c, a in b :=
let ⟨b, hc, ha⟩ := Set.mem_sUnion.1 show a in _ by rw [hu]; exact Set.mem_univ a
  ExistsUnique.intro b ⟨hc, ha⟩ fun _ hc' => H.elim_set hc'.1 hc _ hc'.2 ha

/-- Makes an equivalence relation from a set of disjoints sets covering α. -/
@[instance_reducible]
/--
Definition of `setoidOfDisjointUnion` / `setoidOfDisjointUnion` 的定义

English:
definition setoidOfDisjointUnion
  signature: {c : Set (Set α)} (hu : Set.sUnion c = @Set.univ α)
  body: Setoid.mkClasses c eqv_classes_of_disjoint_union hu H

中文:
定义 setoidOfDisjointUnion
  签名: {c : 集合 (集合 α)} (hu : 集合.集合并集 c = @集合.univ α)
  定义体: Setoid.mkClasses c eqv_classes_of_disjoint_union hu H

Depends on / 依赖: Setoid, Setoid.mkClasses, eqv_classes_of_disjoint_union, mkClasses
-/
def setoidOfDisjointUnion {c : Set (Set α)} (hu : Set.sUnion c = @Set.univ α)
    (H : c.PairwiseDisjoint id) : Setoid α :=
Setoid.mkClasses c eqv_classes_of_disjoint_union hu H

/--
theorem `mkClasses_classes` / 定理 `mkClasses_classes`

English:
theorem mkClasses_classes
  given: (r : Setoid α)
  statement: mkClasses r.classes classes_eqv_classes = r
  proof: ext fun x _y =>
    ⟨fun h => r.symm' (h { z | r z x } (r.mem_classes x) <| r.refl' x), fun h _b hb hx =>
      eq_of_mem_classes (r.mem_classes x) (r.refl' x) hb hx ▸ r.symm' h⟩

@[simp]

中文:
定理 mkClasses_classes
  条件: (r : 集合等价关系 α)
  结论: mkClasses r.classes classes_eqv_classes = r
  证明: ext fun x _y =>
    ⟨fun h => r.symm' (h { z | r z x } (r.mem_classes x) <| r.refl' x), fun h _b hb hx =>
      eq_of_mem_classes (r.mem_classes x) (r.refl' x) hb hx ▸ r.symm' h⟩

@[simp]

Depends on / 依赖: eq_of_mem_classes, mem_classes, r.mem_classes, r.refl, r.symm
-/
theorem mkClasses_classes (r : Setoid α) : mkClasses r.classes classes_eqv_classes = r :=
  ext fun x _y =>
    ⟨fun h => r.symm' (h { z | r z x } (r.mem_classes x) <| r.refl' x), fun h _b hb hx =>
      eq_of_mem_classes (r.mem_classes x) (r.refl' x) hb hx ▸ r.symm' h⟩

@[simp]
/--
theorem `sUnion_classes` / 定理 `sUnion_classes`

English:
theorem sUnion_classes
  given: (r : Setoid α)
  statement: ⋃₀ r.classes = Set.univ
  proof: Set.eq_univ_of_forall fun x => Set.mem_sUnion.2 ⟨{ y | r y x }, ⟨x, rfl⟩, Setoid.refl _⟩

中文:
定理 sUnion_classes
  条件: (r : 集合等价关系 α)
  结论: ⋃₀ r.classes = 集合.univ
  证明: Set.eq_univ_of_forall fun x => Set.mem_sUnion.2 ⟨{ y | r y x }, ⟨x, rfl⟩, Setoid.refl _⟩

Depends on / 依赖: Set.eq_univ_of_forall, Set.mem_sUnion, Setoid, Setoid.refl, eq_univ_of_forall, mem_sUnion
-/
theorem sUnion_classes (r : Setoid α) : ⋃₀ r.classes = Set.univ :=
  Set.eq_univ_of_forall fun x => Set.mem_sUnion.2 ⟨{ y | r y x }, ⟨x, rfl⟩, Setoid.refl _⟩

/--
Definition of `quotientEquivClasses` / `quotientEquivClasses` 的定义

English:
definition quotientEquivClasses
  signature: (r : Setoid α)
  body: by
  let f (a : α) : Setoid.classes r := ⟨{ x | r x a }, Setoid.mem_classes r a⟩
  have f_respects_relation (a b : α) (a_rel_b : r a b) : f a = f b := by
    rw [Subtype.mk.injEq]
    exact Setoid.eq_of_mem_classes (Setoid.mem_classes r a) (Setoid.symm a_rel_b)
        (Setoid.mem_classes r b) (Seto

中文:
定义 quotientEquivClasses
  签名: (r : 集合等价关系 α)
  定义体: by
  let f (a : α) : Setoid.classes r := ⟨{ x | r x a }, Setoid.mem_classes r a⟩
  have f_respects_relation (a b : α) (a_rel_b : r a b) : f a = f b := by
    rw [Subtype.mk.injEq]
    exact Setoid.eq_of_mem_classes (Setoid.mem_classes r a) (Setoid.symm a_rel_b)
        (Setoid.mem_classes r b) (Seto

Depends on / 依赖: Equiv.ofBijective, Quot.lift, Quotient, Quotient.ind, Setoid, Setoid.classes, Setoid.eq_of_mem_classes, Setoid.mem_classes, Setoid.refl, Setoid.symm, Subtype, Subtype.mk.injEq, a_rel_b, classes, eq_of_mem_classes, f_respects_relation, h_eq, mem_classes, ofBijective
-/
noncomputable def quotientEquivClasses (r : Setoid α) : Quotient r ≃ Setoid.classes r := by
  let f (a : α) : Setoid.classes r := ⟨{ x | r x a }, Setoid.mem_classes r a⟩
  have f_respects_relation (a b : α) (a_rel_b : r a b) : f a = f b := by
    rw [Subtype.mk.injEq]
    exact Setoid.eq_of_mem_classes (Setoid.mem_classes r a) (Setoid.symm a_rel_b)
        (Setoid.mem_classes r b) (Setoid.refl b)
  apply Equiv.ofBijective (Quot.lift f f_respects_relation)
  constructor
  · intro (q_a : Quotient r) (q_b : Quotient r) h_eq
    induction q_a using Quotient.ind with | _ a
    induction q_b using Quotient.ind with | _ b
    simp only [f, Quotient.lift_mk, Subtype.ext_iff] at h_eq
    apply Quotient.sound
    change a in { x | r x b }
    rw [← h_eq]
    exact Setoid.refl a
  · rw [Quot.surjective_lift]
    intro ⟨c, a, hc⟩
    exact ⟨a, Subtype.ext hc.symm⟩

@[simp]
/--
lemma `quotientEquivClasses_mk_eq` / 引理 `quotientEquivClasses_mk_eq`

English:
lemma quotientEquivClasses_mk_eq
  given: (r : Setoid α) (a : α)
  proof: (@Subtype.ext_iff _ _ _ ⟨{ x | r x a }, Setoid.mem_classes r a⟩).mp rfl

中文:
引理 quotientEquivClasses_mk_eq
  条件: (r : 集合等价关系 α) (a : α)
  证明: (@Subtype.ext_iff _ _ _ ⟨{ x | r x a }, Setoid.mem_classes r a⟩).mp rfl

Depends on / 依赖: Setoid, Setoid.mem_classes, Subtype, Subtype.ext_iff, ext_iff, mem_classes
-/
lemma quotientEquivClasses_mk_eq (r : Setoid α) (a : α) :
    (quotientEquivClasses r (Quotient.mk r a) : Set α) = { x | r x a } :=
  (@Subtype.ext_iff _ _ _ ⟨{ x | r x a }, Setoid.mem_classes r a⟩).mp rfl

section Partition

/--
Definition of `IsPartition` / `IsPartition` 的定义

English:
definition IsPartition
  signature: (c : Set (Set α))
  body: ∅ ∉ c ∧ forall a, exists! b in c, a in b

中文:
定义 IsPartition
  签名: (c : 集合 (集合 α))
  定义体: ∅ ∉ c ∧ forall a, exists! b in c, a in b
-/
def IsPartition (c : Set (Set α)) := ∅ ∉ c ∧ forall a, exists! b in c, a in b

/--
theorem `nonempty_of_mem_partition` / 定理 `nonempty_of_mem_partition`

English:
theorem nonempty_of_mem_partition
  given: {c : Set (Set α)} (hc : IsPartition c) {s} (h : s in c)
  proof: Set.nonempty_iff_ne_empty.2 fun hs0 => hc.1 hs0 ▸ h

中文:
定理 nonempty_of_mem_partition
  条件: {c : 集合 (集合 α)} (hc : IsPartition c) {s} (h : s in c)
  证明: Set.nonempty_iff_ne_empty.2 fun hs0 => hc.1 hs0 ▸ h

Depends on / 依赖: Set.nonempty_iff_ne_empty, nonempty_iff_ne_empty
-/
theorem nonempty_of_mem_partition {c : Set (Set α)} (hc : IsPartition c) {s} (h : s in c) :
    s.Nonempty :=
Set.nonempty_iff_ne_empty.2 fun hs0 => hc.1 hs0 ▸ h

/--
theorem `isPartition_classes` / 定理 `isPartition_classes`

English:
theorem isPartition_classes
  given: (r : Setoid α)
  statement: IsPartition r.classes
  proof: ⟨empty_notMem_classes, classes_eqv_classes⟩

中文:
定理 isPartition_classes
  条件: (r : 集合等价关系 α)
  结论: IsPartition r.classes
  证明: ⟨empty_notMem_classes, classes_eqv_classes⟩

Depends on / 依赖: classes_eqv_classes, empty_notMem_classes
-/
theorem isPartition_classes (r : Setoid α) : IsPartition r.classes :=
  ⟨empty_notMem_classes, classes_eqv_classes⟩

/--
theorem `IsPartition.pairwiseDisjoint` / 定理 `IsPartition.pairwiseDisjoint`

English:
theorem IsPartition.pairwiseDisjoint
  given: {c : Set (Set α)} (hc : IsPartition c)
  proof: eqv_classes_disjoint hc.2

中文:
定理 IsPartition.pairwiseDisjoint
  条件: {c : 集合 (集合 α)} (hc : IsPartition c)
  证明: eqv_classes_disjoint hc.2

Depends on / 依赖: eqv_classes_disjoint
-/
theorem IsPartition.pairwiseDisjoint {c : Set (Set α)} (hc : IsPartition c) :
    c.PairwiseDisjoint id :=
  eqv_classes_disjoint hc.2

/--
lemma `_root_.Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty` / 引理 `_root_.Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty`

English:
lemma _root_.Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty
  statement: {α : Type*} {s : Set (Set α)}
  proof: by
  refine ⟨h₃, fun a => existsUnique_of_exists_of_unique (h₂ a) ?_⟩
  intro b₁ b₂ hb₁ hb₂
  apply h₁.elim hb₁.1 hb₂.1
  simp only [Set.not_disjoint_iff]
  exact ⟨a, hb₁.2, hb₂.2⟩

中文:
引理 _root_.集合.PairwiseDisjoint.isPartition_of_存在_of_ne_empty
  结论: {α : 类型} {s : 集合 (集合 α)}
  证明: by
  refine ⟨h₃, fun a => existsUnique_of_exists_of_unique (h₂ a) ?_⟩
  intro b₁ b₂ hb₁ hb₂
  apply h₁.elim hb₁.1 hb₂.1
  simp only [Set.not_disjoint_iff]
  exact ⟨a, hb₁.2, hb₂.2⟩

Depends on / 依赖: Set.not_disjoint_iff, existsUnique_of_exists_of_unique, not_disjoint_iff
-/
lemma _root_.Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty {α : Type*} {s : Set (Set α)}
    (h₁ : s.PairwiseDisjoint id) (h₂ : forall a : α, exists x in s, a in x) (h₃ : ∅ ∉ s) :
    Setoid.IsPartition s := by
  refine ⟨h₃, fun a => existsUnique_of_exists_of_unique (h₂ a) ?_⟩
  intro b₁ b₂ hb₁ hb₂
  apply h₁.elim hb₁.1 hb₂.1
  simp only [Set.not_disjoint_iff]
  exact ⟨a, hb₁.2, hb₂.2⟩

/--
theorem `IsPartition.sUnion_eq_univ` / 定理 `IsPartition.sUnion_eq_univ`

English:
theorem IsPartition.sUnion_eq_univ
  given: {c : Set (Set α)} (hc : IsPartition c)
  statement: ⋃₀ c = Set.univ
  proof: Set.eq_univ_of_forall fun x =>
Set.mem_sUnion.2
      let ⟨t, ht⟩ := hc.2 x
      ⟨t, by
        simp only at ht
        tauto⟩

中文:
定理 IsPartition.sUnion_eq_univ
  条件: {c : 集合 (集合 α)} (hc : IsPartition c)
  结论: ⋃₀ c = 集合.univ
  证明: Set.eq_univ_of_forall fun x =>
Set.mem_sUnion.2
      let ⟨t, ht⟩ := hc.2 x
      ⟨t, by
        simp only at ht
        tauto⟩

Depends on / 依赖: Set.eq_univ_of_forall, Set.mem_sUnion, eq_univ_of_forall, mem_sUnion
-/
theorem IsPartition.sUnion_eq_univ {c : Set (Set α)} (hc : IsPartition c) : ⋃₀ c = Set.univ :=
  Set.eq_univ_of_forall fun x =>
Set.mem_sUnion.2
      let ⟨t, ht⟩ := hc.2 x
      ⟨t, by
        simp only at ht
        tauto⟩

/--
theorem `exists_of_mem_partition` / 定理 `exists_of_mem_partition`

English:
theorem exists_of_mem_partition
  given: {c : Set (Set α)} (hc : IsPartition c) {s} (hs : s in c)
  proof: let ⟨y, hy⟩ := nonempty_of_mem_partition hc hs
  ⟨y, eq_eqv_class_of_mem hc.2 hs hy⟩

中文:
定理 存在_of_mem_partition
  条件: {c : 集合 (集合 α)} (hc : IsPartition c) {s} (hs : s in c)
  证明: let ⟨y, hy⟩ := nonempty_of_mem_partition hc hs
  ⟨y, eq_eqv_class_of_mem hc.2 hs hy⟩

Depends on / 依赖: eq_eqv_class_of_mem, nonempty_of_mem_partition
-/
theorem exists_of_mem_partition {c : Set (Set α)} (hc : IsPartition c) {s} (hs : s in c) :
    exists y, s = { x | mkClasses c hc.2 x y } :=
  let ⟨y, hy⟩ := nonempty_of_mem_partition hc hs
  ⟨y, eq_eqv_class_of_mem hc.2 hs hy⟩

/--
theorem `classes_mkClasses` / 定理 `classes_mkClasses`

English:
theorem classes_mkClasses
  given: (c : Set (Set α)) (hc : IsPartition c)
  proof: by
  ext s
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨b, ⟨hb, hy⟩, _⟩ := hc.2 y
    rwa [← eq_eqv_class_of_mem _ hb hy]
  · exact exists_of_mem_partition hc

中文:
定理 classes_mkClasses
  条件: (c : 集合 (集合 α)) (hc : IsPartition c)
  证明: by
  ext s
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨b, ⟨hb, hy⟩, _⟩ := hc.2 y
    rwa [← eq_eqv_class_of_mem _ hb hy]
  · exact exists_of_mem_partition hc

Depends on / 依赖: eq_eqv_class_of_mem, exists_of_mem_partition
-/
theorem classes_mkClasses (c : Set (Set α)) (hc : IsPartition c) :
    (mkClasses c hc.2).classes = c := by
  ext s
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨b, ⟨hb, hy⟩, _⟩ := hc.2 y
    rwa [← eq_eqv_class_of_mem _ hb hy]
  · exact exists_of_mem_partition hc

/--
Definition of `Partitions` / `Partitions` 的定义

English:
definition Partitions
  signature: (α : Type*)
  body: Subtype (@IsPartition α)

中文:
定义 Partitions
  签名: (α : 类型)
  定义体: Subtype (@IsPartition α)

Depends on / 依赖: IsPartition, Subtype
-/
def Partitions (α : Type*) : Type _ := Subtype (@IsPartition α)

/--
Definition of `Partitions.toSet` / `Partitions.toSet` 的定义

English:
definition Partitions.toSet
  signature: (p : Partitions α)
  body: Subtype.val p

中文:
定义 Partitions.toSet
  签名: (p : Partitions α)
  定义体: Subtype.val p

Depends on / 依赖: Subtype, Subtype.val
-/
def Partitions.toSet (p : Partitions α) : Set (Set α) :=
  Subtype.val p

/--
lemma `Partitions.ext_iff` / 引理 `Partitions.ext_iff`

English:
lemma Partitions.ext_iff
  given: (p q : Partitions α)
  statement: p = q ↔ p.toSet = q.toSet
  proof: Subtype.ext_iff

中文:
引理 Partitions.ext_iff
  条件: (p q : Partitions α)
  结论: p = q ↔ p.toSet = q.toSet
  证明: Subtype.ext_iff

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
lemma Partitions.ext_iff (p q : Partitions α) : p = q ↔ p.toSet = q.toSet :=
  Subtype.ext_iff

/--
lemma `Partitions.isPartition` / 引理 `Partitions.isPartition`

English:
lemma Partitions.isPartition
  given: (p : Partitions α)
  statement: IsPartition p.toSet
  proof: p.2

中文:
引理 Partitions.isPartition
  条件: (p : Partitions α)
  结论: IsPartition p.toSet
  证明: p.2
-/
lemma Partitions.isPartition (p : Partitions α) : IsPartition p.toSet := p.2

/--
Instance `Partition.le` / 实例 `Partition.le`

English:
instance Partition.le
  signature: : LE (Partitions α)
  body: ⟨fun x y => mkClasses x.toSet x.isPartition.2 <= mkClasses y.toSet y.isPartition.2⟩

中文:
实例 分拆.le
  签名: : LE (Partitions α)
  定义体: ⟨fun x y => mkClasses x.toSet x.isPartition.2 <= mkClasses y.toSet y.isPartition.2⟩

Depends on / 依赖: isPartition, mkClasses, x.isPartition, x.toSet, y.isPartition, y.toSet
-/
instance Partition.le : LE (Partitions α) :=
  ⟨fun x y => mkClasses x.toSet x.isPartition.2 <= mkClasses y.toSet y.isPartition.2⟩

/--
Instance `Partition.partialOrder` / 实例 `Partition.partialOrder`

English:
instance Partition.partialOrder
  signature: : PartialOrder (Partitions α) where
  body: x <= y ∧ ¬y <= x
  le_refl _ := @le_refl (Setoid α) _ _
  le_trans _ _ _ := @le_trans (Setoid α) _ _ _ _
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm x y hx hy := by
    let h := @le_antisymm (Setoid α) _ _ _ hx hy
    rw [Partitions.ext_iff]; rw [← classes_mkClasses x.toSet x.isPartition]; rw [←

中文:
实例 分拆.partialOrder
  签名: : 偏序 (Partitions α) where
  定义体: x <= y ∧ ¬y <= x
  le_refl _ := @le_refl (Setoid α) _ _
  le_trans _ _ _ := @le_trans (Setoid α) _ _ _ _
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm x y hx hy := by
    let h := @le_antisymm (Setoid α) _ _ _ hx hy
    rw [Partitions.ext_iff]; rw [← classes_mkClasses x.toSet x.isPartition]; rw [←
-/
instance Partition.partialOrder : PartialOrder (Partitions α) where
  lt x y := x <= y ∧ ¬y <= x
  le_refl _ := @le_refl (Setoid α) _ _
  le_trans _ _ _ := @le_trans (Setoid α) _ _ _ _
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm x y hx hy := by
    let h := @le_antisymm (Setoid α) _ _ _ hx hy
    rw [Partitions.ext_iff]; rw [← classes_mkClasses x.toSet x.isPartition]; rw [← classes_mkClasses y.toSet y.isPartition]; rw [h]

set_option backward.isDefEq.respectTransparency.types false in
variable (α) in
/--
Definition of `Partition.orderIso` / `Partition.orderIso` 的定义

English:
definition Partition.orderIso
  signature: : Setoid α ≃o Partitions α where
  body: ⟨r.classes, empty_notMem_classes, classes_eqv_classes⟩
  invFun C := mkClasses C.1 C.2.2
  left_inv := mkClasses_classes
  right_inv C := by
    rw [Partitions.ext_iff]; rw [← classes_mkClasses C.toSet C.isPartition]
    rfl
  map_rel_iff' {r s} := by
    conv_rhs => rw [← mkClasses_classes r, ← mkC

中文:
定义 分拆.orderIso
  签名: : 集合等价关系 α ≃o Partitions α where
  定义体: ⟨r.classes, empty_notMem_classes, classes_eqv_classes⟩
  invFun C := mkClasses C.1 C.2.2
  left_inv := mkClasses_classes
  right_inv C := by
    rw [Partitions.ext_iff]; rw [← classes_mkClasses C.toSet C.isPartition]
    rfl
  map_rel_iff' {r s} := by
    conv_rhs => rw [← mkClasses_classes r, ← mkC
-/
protected def Partition.orderIso : Setoid α ≃o Partitions α where
  toFun r := ⟨r.classes, empty_notMem_classes, classes_eqv_classes⟩
  invFun C := mkClasses C.1 C.2.2
  left_inv := mkClasses_classes
  right_inv C := by
    rw [Partitions.ext_iff]; rw [← classes_mkClasses C.toSet C.isPartition]
    rfl
  map_rel_iff' {r s} := by
    conv_rhs => rw [← mkClasses_classes r, ← mkClasses_classes s]
    rfl

/--
Instance `Partition.completeLattice` / 实例 `Partition.completeLattice`

English:
instance Partition.completeLattice
  signature: : CompleteLattice (Partitions α)
  body: GaloisInsertion.liftCompleteLattice
@OrderIso.toGaloisInsertion _ (Partitions α) _ (PartialOrder.toPreorder)
      Partition.orderIso α

中文:
实例 分拆.completeLattice
  签名: : 完备格 (Partitions α)
  定义体: GaloisInsertion.liftCompleteLattice
@OrderIso.toGaloisInsertion _ (Partitions α) _ (PartialOrder.toPreorder)
      Partition.orderIso α

Depends on / 依赖: GaloisInsertion, GaloisInsertion.liftCompleteLattice, OrderIso, OrderIso.toGaloisInsertion, PartialOrder, PartialOrder.toPreorder, Partition, Partition.orderIso, Partitions, liftCompleteLattice, orderIso, toGaloisInsertion, toPreorder
-/
instance Partition.completeLattice : CompleteLattice (Partitions α) :=
GaloisInsertion.liftCompleteLattice
@OrderIso.toGaloisInsertion _ (Partitions α) _ (PartialOrder.toPreorder)
      Partition.orderIso α

end Partition

/-- A finite setoid partition furnishes a finpartition -/
@[simps]
/--
Definition of `IsPartition.finpartition` / `IsPartition.finpartition` 的定义

English:
definition IsPartition.finpartition
  signature: {c : Finset (Set α)} (hc : Setoid.IsPartition (c : Set (Set α)))
  body: c
supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr eqv_classes_disjoint hc.2
  sup_parts := c.sup_id_set_eq_sUnion.trans hc.sUnion_eq_univ
  bot_notMem := hc.left

中文:
定义 IsPartition.finpartition
  签名: {c : 有限集 (集合 α)} (hc : 集合等价关系.IsPartition (c : 集合 (集合 α)))
  定义体: c
supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr eqv_classes_disjoint hc.2
  sup_parts := c.sup_id_set_eq_sUnion.trans hc.sUnion_eq_univ
  bot_notMem := hc.left
-/
def IsPartition.finpartition {c : Finset (Set α)} (hc : Setoid.IsPartition (c : Set (Set α))) :
    Finpartition (Set.univ : Set α) where
  parts := c
supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr eqv_classes_disjoint hc.2
  sup_parts := c.sup_id_set_eq_sUnion.trans hc.sUnion_eq_univ
  bot_notMem := hc.left

end Setoid

/--
theorem `Finpartition.isPartition_parts` / 定理 `Finpartition.isPartition_parts`

English:
theorem Finpartition.isPartition_parts
  given: {α} (f : Finpartition (Set.univ : Set α))
  proof: ⟨f.bot_notMem,
    Setoid.eqv_classes_of_disjoint_union (f.parts.sup_id_set_eq_sUnion.symm.trans f.sup_parts)
      f.supIndep.pairwiseDisjoint⟩

中文:
定理 有限分拆.isPartition_parts
  条件: {α} (f : 有限分拆 (集合.univ : 集合 α))
  证明: ⟨f.bot_notMem,
    Setoid.eqv_classes_of_disjoint_union (f.parts.sup_id_set_eq_sUnion.symm.trans f.sup_parts)
      f.supIndep.pairwiseDisjoint⟩

Depends on / 依赖: Setoid, Setoid.eqv_classes_of_disjoint_union, bot_notMem, eqv_classes_of_disjoint_union, f.bot_notMem, f.parts.sup_id_set_eq_sUnion.symm.trans, f.supIndep.pairwiseDisjoint, f.sup_parts, pairwiseDisjoint, supIndep, sup_id_set_eq_sUnion, sup_parts
-/
theorem Finpartition.isPartition_parts {α} (f : Finpartition (Set.univ : Set α)) :
    Setoid.IsPartition (f.parts : Set (Set α)) :=
  ⟨f.bot_notMem,
    Setoid.eqv_classes_of_disjoint_union (f.parts.sup_id_set_eq_sUnion.symm.trans f.sup_parts)
      f.supIndep.pairwiseDisjoint⟩

/--
Definition of `IndexedPartition` / `IndexedPartition` 的定义

English:
structure IndexedPartition
  parameters: {ι α : Type*} (s : ι -> Set α)
  axioms and operations (5):
    - eq_of_mem : forall {x i j}, x in s i -> x in s j -> i = j
    - some : ι -> α
    - some_mem : forall i, some i in s i
    - index : α -> ι
    - mem_index : forall x, x in s (index x)

中文:
结构 IndexedPartition
  参数: {ι α : 类型} (s : ι -> 集合 α)
  公理与运算 (5 个):
    - eq_of_mem : 对任意 {x i j}, x in s i -> x in s j -> i = j
    - some : ι -> α
    - some_mem : 对任意 i, some i in s i
    - index : α -> ι
    - mem_index : 对任意 x, x in s (index x)
-/
structure IndexedPartition {ι α : Type*} (s : ι -> Set α) where
  /-- two indexes are equal if they are equal in membership -/
  eq_of_mem : forall {x i j}, x in s i -> x in s j -> i = j
  /-- sends an index to an element of the corresponding set -/
  some : ι -> α
  /-- membership invariance for `some` -/
  some_mem : forall i, some i in s i
  /-- index for type `α` -/
  index : α -> ι
  /-- membership invariance for `index` -/
  mem_index : forall x, x in s (index x)

open scoped Function -- required for scoped `on` notation

/--
Definition of `IndexedPartition.mk'` / `IndexedPartition.mk'` 的定义

English:
definition IndexedPartition.mk'
  signature: {ι α : Type*} (s : ι -> Set α)
  body: by_contradiction fun h => (dis h).le_bot ⟨hxi, hxj⟩
  some i := (nonempty i).some
  some_mem i := (nonempty i).choose_spec
  index x := (ex x).choose
  mem_index x := (ex x).choose_spec

中文:
定义 IndexedPartition.mk'
  签名: {ι α : 类型} (s : ι -> 集合 α)
  定义体: by_contradiction fun h => (dis h).le_bot ⟨hxi, hxj⟩
  some i := (nonempty i).some
  some_mem i := (nonempty i).choose_spec
  index x := (ex x).choose
  mem_index x := (ex x).choose_spec

Depends on / 依赖: by_contradiction, choose_spec, le_bot, mem_index, nonempty, some_mem
-/
noncomputable def IndexedPartition.mk' {ι α : Type*} (s : ι -> Set α)
    (dis : Pairwise (Disjoint on s)) (nonempty : forall i, (s i).Nonempty)
    (ex : forall x, exists i, x in s i) : IndexedPartition s where
  eq_of_mem {_x _i _j} hxi hxj := by_contradiction fun h => (dis h).le_bot ⟨hxi, hxj⟩
  some i := (nonempty i).some
  some_mem i := (nonempty i).choose_spec
  index x := (ex x).choose
  mem_index x := (ex x).choose_spec

namespace IndexedPartition

open Set

variable {ι α : Type*} {s : ι -> Set α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: ι] [Inhabited α] : Inhabited (IndexedPartition fun _i
  body: ⟨{ eq_of_mem := fun {_x _i _j} _hi _hj => Subsingleton.elim _ _
      some := default
      some_mem := Set.mem_univ
      index := default
      mem_index := Set.mem_univ }⟩

中文:
实例 [唯一
  签名: ι] [可居 α] : 可居 (IndexedPartition fun _i
  定义体: ⟨{ eq_of_mem := fun {_x _i _j} _hi _hj => Subsingleton.elim _ _
      some := default
      some_mem := Set.mem_univ
      index := default
      mem_index := Set.mem_univ }⟩

Depends on / 依赖: Set.mem_univ, Subsingleton, Subsingleton.elim, eq_of_mem, mem_index, mem_univ, some_mem
-/
instance [Unique ι] [Inhabited α] : Inhabited (IndexedPartition fun _i : ι => (Set.univ : Set α)) :=
  ⟨{ eq_of_mem := fun {_x _i _j} _hi _hj => Subsingleton.elim _ _
      some := default
      some_mem := Set.mem_univ
      index := default
      mem_index := Set.mem_univ }⟩

attribute [simp] some_mem

variable (hs : IndexedPartition s)

include hs in
/--
theorem `exists_mem` / 定理 `exists_mem`

English:
theorem exists_mem
  given: (x : α)
  statement: exists i, x in s i
  proof: ⟨hs.index x, hs.mem_index x⟩

include hs in

中文:
定理 存在_mem
  条件: (x : α)
  结论: 存在 i, x in s i
  证明: ⟨hs.index x, hs.mem_index x⟩

include hs in

Depends on / 依赖: hs.index, hs.mem_index, mem_index
-/
theorem exists_mem (x : α) : exists i, x in s i :=
  ⟨hs.index x, hs.mem_index x⟩

include hs in
/--
theorem `iUnion` / 定理 `iUnion`

English:
theorem iUnion
  statement: ⋃ i, s i = univ
  proof: by
  ext x
  simp [hs.exists_mem x]

include hs in

中文:
定理 iUnion
  结论: ⋃ i, s i = univ
  证明: by
  ext x
  simp [hs.exists_mem x]

include hs in

Depends on / 依赖: exists_mem, hs.exists_mem
-/
theorem iUnion : ⋃ i, s i = univ := by
  ext x
  simp [hs.exists_mem x]

include hs in
/--
theorem `disjoint` / 定理 `disjoint`

English:
theorem disjoint
  statement: Pairwise (Disjoint on s)
  proof: fun {_i _j} h =>
  disjoint_left.mpr fun {_x} hxi hxj => h (hs.eq_of_mem hxi hxj)

中文:
定理 disjoint
  结论: 两两 (Disjoint on s)
  证明: fun {_i _j} h =>
  disjoint_left.mpr fun {_x} hxi hxj => h (hs.eq_of_mem hxi hxj)
-/
theorem disjoint : Pairwise (Disjoint on s) := fun {_i _j} h =>
  disjoint_left.mpr fun {_x} hxi hxj => h (hs.eq_of_mem hxi hxj)

/--
theorem `mem_iff_index_eq` / 定理 `mem_iff_index_eq`

English:
theorem mem_iff_index_eq
  given: {x i}
  statement: x in s i ↔ hs.index x = i
  proof: ⟨fun hxi => (hs.eq_of_mem hxi (hs.mem_index x)).symm, fun h => h ▸ hs.mem_index _⟩

中文:
定理 mem_iff_index_eq
  条件: {x i}
  结论: x in s i ↔ hs.index x = i
  证明: ⟨fun hxi => (hs.eq_of_mem hxi (hs.mem_index x)).symm, fun h => h ▸ hs.mem_index _⟩

Depends on / 依赖: eq_of_mem, hs.eq_of_mem, hs.mem_index, mem_index
-/
theorem mem_iff_index_eq {x i} : x in s i ↔ hs.index x = i :=
  ⟨fun hxi => (hs.eq_of_mem hxi (hs.mem_index x)).symm, fun h => h ▸ hs.mem_index _⟩

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: (i)
  statement: s i = { x | hs.index x = i }
  proof: Set.ext fun _ => hs.mem_iff_index_eq

中文:
定理 eq
  条件: (i)
  结论: s i = { x | hs.index x = i }
  证明: Set.ext fun _ => hs.mem_iff_index_eq

Depends on / 依赖: Set.ext, hs.mem_iff_index_eq, mem_iff_index_eq
-/
theorem eq (i) : s i = { x | hs.index x = i } :=
  Set.ext fun _ => hs.mem_iff_index_eq

/--
Definition of `setoid` / `setoid` 的定义

English:
abbreviation setoid
  signature: (hs : IndexedPartition s)
  body: Setoid.ker hs.index

@[simp]

中文:
缩写 setoid
  签名: (hs : IndexedPartition s)
  定义体: Setoid.ker hs.index

@[simp]
-/
protected abbrev setoid (hs : IndexedPartition s) : Setoid α :=
  Setoid.ker hs.index

@[simp]
/--
theorem `index_some` / 定理 `index_some`

English:
theorem index_some
  given: (i : ι)
  statement: hs.index (hs.some i) = i
  proof: (mem_iff_index_eq _).1 hs.some_mem i

中文:
定理 index_some
  条件: (i : ι)
  结论: hs.index (hs.some i) = i
  证明: (mem_iff_index_eq _).1 hs.some_mem i

Depends on / 依赖: hs.some_mem, mem_iff_index_eq, some_mem
-/
theorem index_some (i : ι) : hs.index (hs.some i) = i :=
(mem_iff_index_eq _).1 hs.some_mem i

/--
theorem `some_index` / 定理 `some_index`

English:
theorem some_index
  given: (x : α)
  statement: hs.setoid (hs.some (hs.index x)) x
  proof: hs.index_some (hs.index x)

中文:
定理 some_index
  条件: (x : α)
  结论: hs.setoid (hs.some (hs.index x)) x
  证明: hs.index_some (hs.index x)

Depends on / 依赖: hs.index, hs.index_some, index_some
-/
theorem some_index (x : α) : hs.setoid (hs.some (hs.index x)) x :=
  hs.index_some (hs.index x)

/--
Definition of `Quotient` / `Quotient` 的定义

English:
definition Quotient
  body: Quotient hs.setoid

中文:
定义 商
  定义体: Quotient hs.setoid
-/
protected def Quotient :=
  Quotient hs.setoid

/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: : α -> hs.Quotient
  body: Quotient.mk''

中文:
定义 proj
  签名: : α -> hs.商
  定义体: Quotient.mk''

Depends on / 依赖: Quotient, Quotient.mk
-/
def proj : α -> hs.Quotient :=
  Quotient.mk''

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited hs.Quotient
  body: ⟨hs.proj default⟩

中文:
实例 [可居
  签名: α] : 可居 hs.商
  定义体: ⟨hs.proj default⟩

Depends on / 依赖: hs.proj
-/
instance [Inhabited α] : Inhabited hs.Quotient :=
  ⟨hs.proj default⟩

/--
theorem `proj_eq_iff` / 定理 `proj_eq_iff`

English:
theorem proj_eq_iff
  given: {x y : α}
  statement: hs.proj x = hs.proj y ↔ hs.index x = hs.index y
  proof: Quotient.eq''

@[simp]

中文:
定理 proj_eq_iff
  条件: {x y : α}
  结论: hs.proj x = hs.proj y ↔ hs.index x = hs.index y
  证明: Quotient.eq''

@[simp]

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem proj_eq_iff {x y : α} : hs.proj x = hs.proj y ↔ hs.index x = hs.index y :=
  Quotient.eq''

@[simp]
/--
theorem `proj_some_index` / 定理 `proj_some_index`

English:
theorem proj_some_index
  given: (x : α)
  statement: hs.proj (hs.some (hs.index x)) = hs.proj x
  proof: Quotient.eq''.2 (hs.some_index x)

中文:
定理 proj_some_index
  条件: (x : α)
  结论: hs.proj (hs.some (hs.index x)) = hs.proj x
  证明: Quotient.eq''.2 (hs.some_index x)

Depends on / 依赖: Quotient, Quotient.eq, hs.some_index, some_index
-/
theorem proj_some_index (x : α) : hs.proj (hs.some (hs.index x)) = hs.proj x :=
  Quotient.eq''.2 (hs.some_index x)

/--
Definition of `equivQuotient` / `equivQuotient` 的定义

English:
definition equivQuotient
  signature: : ι ≃ hs.Quotient
  body: (Setoid.quotientKerEquivOfRightInverse hs.index hs.some <| hs.index_some).symm

@[simp]

中文:
定义 equivQuotient
  签名: : ι ≃ hs.商
  定义体: (Setoid.quotientKerEquivOfRightInverse hs.index hs.some <| hs.index_some).symm

@[simp]

Depends on / 依赖: Setoid, Setoid.quotientKerEquivOfRightInverse, hs.index, hs.index_some, hs.some, index_some, quotientKerEquivOfRightInverse
-/
def equivQuotient : ι ≃ hs.Quotient :=
  (Setoid.quotientKerEquivOfRightInverse hs.index hs.some <| hs.index_some).symm

@[simp]
/--
theorem `equivQuotient_index_apply` / 定理 `equivQuotient_index_apply`

English:
theorem equivQuotient_index_apply
  given: (x : α)
  statement: hs.equivQuotient (hs.index x) = hs.proj x
  proof: hs.proj_eq_iff.mpr (some_index hs x)

@[simp]

中文:
定理 equivQuotient_index_apply
  条件: (x : α)
  结论: hs.equivQuotient (hs.index x) = hs.proj x
  证明: hs.proj_eq_iff.mpr (some_index hs x)

@[simp]

Depends on / 依赖: hs.proj_eq_iff.mpr, proj_eq_iff, some_index
-/
theorem equivQuotient_index_apply (x : α) : hs.equivQuotient (hs.index x) = hs.proj x :=
  hs.proj_eq_iff.mpr (some_index hs x)

@[simp]
/--
theorem `equivQuotient_symm_proj_apply` / 定理 `equivQuotient_symm_proj_apply`

English:
theorem equivQuotient_symm_proj_apply
  given: (x : α)
  statement: hs.equivQuotient.symm (hs.proj x) = hs.index x
  proof: rfl

中文:
定理 equivQuotient_symm_proj_apply
  条件: (x : α)
  结论: hs.equivQuotient.symm (hs.proj x) = hs.index x
  证明: rfl
-/
theorem equivQuotient_symm_proj_apply (x : α) : hs.equivQuotient.symm (hs.proj x) = hs.index x :=
  rfl

/--
theorem `equivQuotient_index` / 定理 `equivQuotient_index`

English:
theorem equivQuotient_index
  statement: hs.equivQuotient ∘ hs.index = hs.proj
  proof: funext hs.equivQuotient_index_apply

中文:
定理 equivQuotient_index
  结论: hs.equivQuotient ∘ hs.index = hs.proj
  证明: funext hs.equivQuotient_index_apply

Depends on / 依赖: equivQuotient_index_apply, hs.equivQuotient_index_apply
-/
theorem equivQuotient_index : hs.equivQuotient ∘ hs.index = hs.proj :=
  funext hs.equivQuotient_index_apply

/--
Definition of `out` / `out` 的定义

English:
definition out
  signature: : hs.Quotient ↪ α
  body: hs.equivQuotient.symm.toEmbedding.trans ⟨hs.some, Function.LeftInverse.injective hs.index_some⟩

中文:
定义 out
  签名: : hs.商 ↪ α
  定义体: hs.equivQuotient.symm.toEmbedding.trans ⟨hs.some, Function.LeftInverse.injective hs.index_some⟩

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, equivQuotient, hs.equivQuotient.symm.toEmbedding.trans, hs.index_some, hs.some, index_some, injective, toEmbedding
-/
def out : hs.Quotient ↪ α :=
  hs.equivQuotient.symm.toEmbedding.trans ⟨hs.some, Function.LeftInverse.injective hs.index_some⟩

/-- This lemma is analogous to `Quotient.mk_out'`. -/
@[simp]
/--
theorem `out_proj` / 定理 `out_proj`

English:
theorem out_proj
  given: (x : α)
  statement: hs.out (hs.proj x) = hs.some (hs.index x)
  proof: rfl

中文:
定理 out_proj
  条件: (x : α)
  结论: hs.out (hs.proj x) = hs.some (hs.index x)
  证明: rfl
-/
theorem out_proj (x : α) : hs.out (hs.proj x) = hs.some (hs.index x) :=
  rfl

/--
theorem `index_out` / 定理 `index_out`

English:
theorem index_out
  given: (x : hs.Quotient)
  statement: hs.index x.out = hs.index (hs.out x)
  proof: Quotient.inductionOn' x fun x => (Setoid.ker_apply_mk_out x).trans (hs.index_some _).symm

中文:
定理 index_out
  条件: (x : hs.商)
  结论: hs.index x.out = hs.index (hs.out x)
  证明: Quotient.inductionOn' x fun x => (Setoid.ker_apply_mk_out x).trans (hs.index_some _).symm

Depends on / 依赖: Quotient, Quotient.inductionOn, Setoid, Setoid.ker_apply_mk_out, hs.index_some, index_some, inductionOn, ker_apply_mk_out
-/
theorem index_out (x : hs.Quotient) : hs.index x.out = hs.index (hs.out x) :=
  Quotient.inductionOn' x fun x => (Setoid.ker_apply_mk_out x).trans (hs.index_some _).symm

/-- This lemma is analogous to `Quotient.out_eq'`. -/
@[simp]
/--
theorem `proj_out` / 定理 `proj_out`

English:
theorem proj_out
  given: (x : hs.Quotient)
  statement: hs.proj (hs.out x) = x
  proof: Quotient.inductionOn' x fun x => Quotient.sound' hs.some_index x

中文:
定理 proj_out
  条件: (x : hs.商)
  结论: hs.proj (hs.out x) = x
  证明: Quotient.inductionOn' x fun x => Quotient.sound' hs.some_index x

Depends on / 依赖: Quotient, Quotient.inductionOn, Quotient.sound, hs.some_index, inductionOn, some_index
-/
theorem proj_out (x : hs.Quotient) : hs.proj (hs.out x) = x :=
Quotient.inductionOn' x fun x => Quotient.sound' hs.some_index x

/--
theorem `class_of` / 定理 `class_of`

English:
theorem class_of
  given: {x : α}
  statement: Set.ofPred (hs.setoid x) = s (hs.index x)
  proof: Set.ext fun _y => eq_comm.trans hs.mem_iff_index_eq.symm

中文:
定理 class_of
  条件: {x : α}
  结论: 集合.ofPred (hs.setoid x) = s (hs.index x)
  证明: Set.ext fun _y => eq_comm.trans hs.mem_iff_index_eq.symm

Depends on / 依赖: Set.ext, eq_comm, eq_comm.trans, hs.mem_iff_index_eq.symm, mem_iff_index_eq
-/
theorem class_of {x : α} : Set.ofPred (hs.setoid x) = s (hs.index x) :=
  Set.ext fun _y => eq_comm.trans hs.mem_iff_index_eq.symm

/--
theorem `proj_fiber` / 定理 `proj_fiber`

English:
theorem proj_fiber
  given: (x : hs.Quotient)
  statement: hs.proj ⁻¹' {x} = s (hs.equivQuotient.symm x)
  proof: Quotient.inductionOn' x fun x => by
    ext y
    simp only [Set.mem_preimage, hs.mem_iff_index_eq]
    exact Quotient.eq''

中文:
定理 proj_fiber
  条件: (x : hs.商)
  结论: hs.proj ⁻¹' {x} = s (hs.equivQuotient.symm x)
  证明: Quotient.inductionOn' x fun x => by
    ext y
    simp only [Set.mem_preimage, hs.mem_iff_index_eq]
    exact Quotient.eq''

Depends on / 依赖: Quotient, Quotient.eq, Quotient.inductionOn, Set.mem_preimage, hs.mem_iff_index_eq, inductionOn, mem_iff_index_eq, mem_preimage
-/
theorem proj_fiber (x : hs.Quotient) : hs.proj ⁻¹' {x} = s (hs.equivQuotient.symm x) :=
  Quotient.inductionOn' x fun x => by
    ext y
    simp only [Set.mem_preimage, hs.mem_iff_index_eq]
    exact Quotient.eq''

/--
Definition of `piecewise` / `piecewise` 的定义

English:
definition piecewise
  signature: {β : Type*} (f : ι -> α -> β)
  body: fun x => f (hs.index x) x

中文:
定义 piecewise
  签名: {β : 类型} (f : ι -> α -> β)
  定义体: fun x => f (hs.index x) x

Depends on / 依赖: hs.index
-/
def piecewise {β : Type*} (f : ι -> α -> β) : α -> β := fun x => f (hs.index x) x

/--
lemma `piecewise_apply` / 引理 `piecewise_apply`

English:
lemma piecewise_apply
  given: {β : Type*} {f : ι -> α -> β} (x : α)
  statement: hs.piecewise f x = f (hs.index x) x
  proof: rfl

中文:
引理 piecewise_apply
  条件: {β : 类型} {f : ι -> α -> β} (x : α)
  结论: hs.piecewise f x = f (hs.index x) x
  证明: rfl
-/
lemma piecewise_apply {β : Type*} {f : ι -> α -> β} (x : α) : hs.piecewise f x = f (hs.index x) x :=
  rfl

open Function

variable {β : Type*} {f : ι -> α -> β}

/--
theorem `piecewise_inj` / 定理 `piecewise_inj`

English:
theorem piecewise_inj
  statement: (h_injOn : forall i, InjOn (f i) (s i))
  proof: by
  intro x y h
  suffices hs.index x = hs.index y by
    apply h_injOn (hs.index x) (hs.mem_index x) (this ▸ hs.mem_index y)
    simpa only [piecewise_apply, this] using h
  apply h_disjoint.elim trivial trivial
  contrapose! h
  exact h.ne_of_mem (mem_image_of_mem _ (hs.mem_index x)) (mem_image_o

中文:
定理 piecewise_inj
  结论: (h_injOn : 对任意 i, 单射限制 (f i) (s i))
  证明: by
  intro x y h
  suffices hs.index x = hs.index y by
    apply h_injOn (hs.index x) (hs.mem_index x) (this ▸ hs.mem_index y)
    simpa only [piecewise_apply, this] using h
  apply h_disjoint.elim trivial trivial
  contrapose! h
  exact h.ne_of_mem (mem_image_of_mem _ (hs.mem_index x)) (mem_image_o

Depends on / 依赖: contrapose, h.ne_of_mem, h_disjoint, h_disjoint.elim, h_injOn, hs.index, hs.mem_index, mem_image_of_mem, mem_index, ne_of_mem, piecewise_apply
-/
theorem piecewise_inj (h_injOn : forall i, InjOn (f i) (s i))
    (h_disjoint : PairwiseDisjoint (univ : Set ι) fun i => (f i) '' (s i)) :
    Injective (piecewise hs f) := by
  intro x y h
  suffices hs.index x = hs.index y by
    apply h_injOn (hs.index x) (hs.mem_index x) (this ▸ hs.mem_index y)
    simpa only [piecewise_apply, this] using h
  apply h_disjoint.elim trivial trivial
  contrapose! h
  exact h.ne_of_mem (mem_image_of_mem _ (hs.mem_index x)) (mem_image_of_mem _ (hs.mem_index y))

/--
theorem `piecewise_bij` / 定理 `piecewise_bij`

English:
theorem piecewise_bij
  statement: {t : ι -> Set β} (ht : IndexedPartition t)
  proof: by
  set g := piecewise hs f with hg
  have hg_bij (i) : BijOn g (s i) (t i) := by
    refine (hf i).congr fun x hx => ?_
    rw [hg]; rw [piecewise_apply]; rw [hs.mem_iff_index_eq.mp hx]
  have hg_inj : InjOn g (⋃ i, s i) := by
    refine injOn_of_injective (piecewise_inj hs (fun i => BijOn.injOn (

中文:
定理 piecewise_bij
  结论: {t : ι -> 集合 β} (ht : IndexedPartition t)
  证明: by
  set g := piecewise hs f with hg
  have hg_bij (i) : BijOn g (s i) (t i) := by
    refine (hf i).congr fun x hx => ?_
    rw [hg]; rw [piecewise_apply]; rw [hs.mem_iff_index_eq.mp hx]
  have hg_inj : InjOn g (⋃ i, s i) := by
    refine injOn_of_injective (piecewise_inj hs (fun i => BijOn.injOn (

Depends on / 依赖: BijOn.image_eq, BijOn.injOn, bijOn_iUnion, bijOn_univ, disjoint, hg_bij, hg_inj, hs.iUnion, hs.mem_iff_index_eq.mp, ht.disjoint, ht.iUnion, iUnion, image_eq, injOn_of_injective, mem_iff_index_eq, piecewise, piecewise_apply, piecewise_inj
-/
theorem piecewise_bij {t : ι -> Set β} (ht : IndexedPartition t)
    (hf : forall i, BijOn (f i) (s i) (t i)) :
    Bijective (piecewise hs f) := by
  set g := piecewise hs f with hg
  have hg_bij (i) : BijOn g (s i) (t i) := by
    refine (hf i).congr fun x hx => ?_
    rw [hg]; rw [piecewise_apply]; rw [hs.mem_iff_index_eq.mp hx]
  have hg_inj : InjOn g (⋃ i, s i) := by
    refine injOn_of_injective (piecewise_inj hs (fun i => BijOn.injOn (hf i)) ?_)
    simp only [fun i => BijOn.image_eq (hf i)]
    rintro i - j - hij
    exact ht.disjoint hij
  rw [← bijOn_univ]; rw [← hs.iUnion]; rw [← ht.iUnion]
  exact bijOn_iUnion hg_bij hg_inj

/--
theorem `piecewise_preimage` / 定理 `piecewise_preimage`

English:
theorem piecewise_preimage
  given: (f : ι -> α -> β) (t : Set β)
  proof: by
  refine ext fun x => ⟨fun hx => ?_, fun ⟨a, ⟨i, hi⟩, ha⟩ => ?_⟩
  · rw [mem_preimage, piecewise_apply, ← mem_preimage] at hx
    exact mem_iUnion_of_mem (hs.index x) (mem_inter (hs.mem_index x) hx)
  · rw [← hi, ← (mem_iff_index_eq hs).mp ha.1] at ha
    simp_all [piecewise_apply]

中文:
定理 piecewise_preimage
  条件: (f : ι -> α -> β) (t : 集合 β)
  证明: by
  refine ext fun x => ⟨fun hx => ?_, fun ⟨a, ⟨i, hi⟩, ha⟩ => ?_⟩
  · rw [mem_preimage, piecewise_apply, ← mem_preimage] at hx
    exact mem_iUnion_of_mem (hs.index x) (mem_inter (hs.mem_index x) hx)
  · rw [← hi, ← (mem_iff_index_eq hs).mp ha.1] at ha
    simp_all [piecewise_apply]

Depends on / 依赖: hs.index, hs.mem_index, mem_iUnion_of_mem, mem_iff_index_eq, mem_index, mem_inter, mem_preimage, piecewise_apply
-/
theorem piecewise_preimage (f : ι -> α -> β) (t : Set β) :
    hs.piecewise f ⁻¹' t = ⋃ i, s i inter (f i ⁻¹' t) := by
  refine ext fun x => ⟨fun hx => ?_, fun ⟨a, ⟨i, hi⟩, ha⟩ => ?_⟩
  · rw [mem_preimage, piecewise_apply, ← mem_preimage] at hx
    exact mem_iUnion_of_mem (hs.index x) (mem_inter (hs.mem_index x) hx)
  · rw [← hi, ← (mem_iff_index_eq hs).mp ha.1] at ha
    simp_all [piecewise_apply]

/--
theorem `range_piecewise` / 定理 `range_piecewise`

English:
theorem range_piecewise
  given: (f : ι -> α -> β)
  statement: range (hs.piecewise f) = ⋃ i, f i '' s i
  proof: by
  refine ext fun x => ⟨?_, fun ⟨t, ⟨i, hi⟩, ht⟩ => ?_⟩
  · rintro ⟨x, rfl⟩
    exact mem_iUnion_of_mem (hs.index x) ⟨x, hs.mem_index x, rfl⟩
  · simp only [← hi, mem_image] at ht
    obtain ⟨a, ha1, ha2⟩ := ht
    refine ⟨a, ?_⟩
    simp only [hs.mem_iff_index_eq] at ha1
    simpa [hs.mem_iff_ind

中文:
定理 range_piecewise
  条件: (f : ι -> α -> β)
  结论: range (hs.piecewise f) = ⋃ i, f i '' s i
  证明: by
  refine ext fun x => ⟨?_, fun ⟨t, ⟨i, hi⟩, ht⟩ => ?_⟩
  · rintro ⟨x, rfl⟩
    exact mem_iUnion_of_mem (hs.index x) ⟨x, hs.mem_index x, rfl⟩
  · simp only [← hi, mem_image] at ht
    obtain ⟨a, ha1, ha2⟩ := ht
    refine ⟨a, ?_⟩
    simp only [hs.mem_iff_index_eq] at ha1
    simpa [hs.mem_iff_ind

Depends on / 依赖: hs.index, hs.mem_iff_index_eq, hs.mem_index, mem_iUnion_of_mem, mem_iff_index_eq, mem_image, mem_index
-/
theorem range_piecewise (f : ι -> α -> β) : range (hs.piecewise f) = ⋃ i, f i '' s i := by
  refine ext fun x => ⟨?_, fun ⟨t, ⟨i, hi⟩, ht⟩ => ?_⟩
  · rintro ⟨x, rfl⟩
    exact mem_iUnion_of_mem (hs.index x) ⟨x, hs.mem_index x, rfl⟩
  · simp only [← hi, mem_image] at ht
    obtain ⟨a, ha1, ha2⟩ := ht
    refine ⟨a, ?_⟩
    simp only [hs.mem_iff_index_eq] at ha1
    simpa [hs.mem_iff_index_eq, ← ha1] using! ha2

/--
theorem `range_piecewise_subset` / 定理 `range_piecewise_subset`

English:
theorem range_piecewise_subset
  given: (f : ι -> α -> β)
  statement: range (hs.piecewise f) subseteq ⋃ i, range (f i)
  proof: fun x ⟨y, hy⟩ => by simpa [IndexedPartition.piecewise_apply] using ⟨hs.index y, y, hy⟩

中文:
定理 range_piecewise_subset
  条件: (f : ι -> α -> β)
  结论: range (hs.piecewise f) subseteq ⋃ i, range (f i)
  证明: fun x ⟨y, hy⟩ => by simpa [IndexedPartition.piecewise_apply] using ⟨hs.index y, y, hy⟩

Depends on / 依赖: IndexedPartition, IndexedPartition.piecewise_apply, hs.index, piecewise_apply
-/
theorem range_piecewise_subset (f : ι -> α -> β) : range (hs.piecewise f) subseteq ⋃ i, range (f i) :=
  fun x ⟨y, hy⟩ => by simpa [IndexedPartition.piecewise_apply] using ⟨hs.index y, y, hy⟩

/--
Definition of `coarserPartition` / `coarserPartition` 的定义

English:
definition coarserPartition
  signature: (hs : IndexedPartition s) {κ : Type*} (g : ι -> κ)
  body: by
    obtain ⟨a, ⟨c, hc⟩, ha⟩ := hxi
    obtain ⟨b, ⟨d, hd⟩, hb⟩ := hxj
    grind =>
      instantiate [mem_iUnion]
      have hb : x in s d
      have ha : x in s c
      have : c = d := hs.eq_of_mem ha hb
      finish
  some k := hs.some ((singleton_nonempty k).preimage hg).some
  some_mem k := b

中文:
定义 coarserPartition
  签名: (hs : IndexedPartition s) {κ : 类型} (g : ι -> κ)
  定义体: by
    obtain ⟨a, ⟨c, hc⟩, ha⟩ := hxi
    obtain ⟨b, ⟨d, hd⟩, hb⟩ := hxj
    grind =>
      instantiate [mem_iUnion]
      have hb : x in s d
      have ha : x in s c
      have : c = d := hs.eq_of_mem ha hb
      finish
  some k := hs.some ((singleton_nonempty k).preimage hg).some
  some_mem k := b

Depends on / 依赖: eq_of_mem, exists_prop, finish, hs.eq_of_mem, hs.some, hs.some_mem, instantiate, mem_iUnion, mem_iUnion_of_mem, mem_preimage, mem_singleton_iff, preimage, singleton_n, singleton_nonempty, some_mem
-/
noncomputable def coarserPartition (hs : IndexedPartition s) {κ : Type*} (g : ι -> κ)
    (hg : g.Surjective) :
    IndexedPartition (fun k : κ => ⋃ i in g ⁻¹' {k}, s i) where
  eq_of_mem {x _i _j} hxi hxj := by
    obtain ⟨a, ⟨c, hc⟩, ha⟩ := hxi
    obtain ⟨b, ⟨d, hd⟩, hb⟩ := hxj
    grind =>
      instantiate [mem_iUnion]
      have hb : x in s d
      have ha : x in s c
      have : c = d := hs.eq_of_mem ha hb
      finish
  some k := hs.some ((singleton_nonempty k).preimage hg).some
  some_mem k := by
    refine mem_iUnion_of_mem ((singleton_nonempty k).preimage hg).some ?_
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, exists_prop]
    constructor
    · simpa using ((singleton_nonempty k).preimage hg).some_mem
    · exact hs.some_mem ((singleton_nonempty k).preimage hg).some
  index x := g (hs.index x)
  mem_index x := mem_iUnion_of_mem (hs.index x) (by simp [hs.mem_index])

end IndexedPartition
