/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Enum

/-!
# Club sets and stationary sets

A subset of a well-ordered type `α` is called a **club set** when it is closed in the order topology
and cofinal. If `α` has no maximum, then an equivalent condition is that `α` is closed and
unbounded; hence the name.

A **stationary set** is a set which intersects all club sets.

## Implementation notes

To avoid importing topology in the ordinals, we spell out the closure property using `DirSupClosed`.
For any type equipped with the Scott-Hausdorff topology (which includes well-orders with the order
topology), `DirSupClosed s` and `IsClosed s` are equivalent predicates.
-/

public section

universe u v

open Cardinal Order Set

variable {α : Type v} {s t : Set α} {x : α} [LinearOrder α]

/-- A club set is a set that is closed under suprema and that is cofinal. -/
@[mk_iff]
/--
Definition of `IsClub` / `IsClub` 的定义

English:
structure IsClub
  parameters: {α : Type*} [LinearOrder α] (s : Set α)
  axioms and operations (2):
    - dirSupClosed : DirSupClosed s
    - isCofinal : IsCofinal s

中文:
结构 IsClub
  参数: {α : 类型} [LinearOrder α] (s : Set α)
  公理与运算 (2 个):
    - dirSupClosed : DirSupClosed s
    - isCofinal : IsCofinal s
-/
structure IsClub {α : Type*} [LinearOrder α] (s : Set α) where
  /-- Club sets are closed under suprema. If `α` is a well-order with the order topology, this
  condition is equivalent to `IsClosed s`. -/
  dirSupClosed : DirSupClosed s
  /-- Club sets are cofinal. If `α` has no maximum, this condition is equivalent to `¬ BddAbove s`.
  See `not_bddAbove_iff_isCofinal`. -/
  isCofinal : IsCofinal s

namespace IsClub

@[simp]
/--
theorem `of_isEmpty` / 定理 `of_isEmpty`

English:
theorem of_isEmpty
  given: [IsEmpty α] {s : Set α}
  statement: IsClub s
  proof: ⟨.of_isEmpty, .of_isEmpty⟩

@[simp]

中文:
定理 of_isEmpty
  条件: [IsEmpty α] {s : Set α}
  结论: IsClub s
  证明: ⟨.of_isEmpty, .of_isEmpty⟩

@[simp]

Depends on / 依赖: of_isEmpty
-/
theorem of_isEmpty [IsEmpty α] {s : Set α} : IsClub s :=
  ⟨.of_isEmpty, .of_isEmpty⟩

@[simp]
/--
theorem `univ` / 定理 `univ`

English:
theorem univ
  statement: IsClub (α := α) .univ
  proof: ⟨.univ, .univ⟩

中文:
定理 univ
  结论: IsClub (α := α) .univ
  证明: ⟨.univ, .univ⟩
-/
protected theorem univ : IsClub (α := α) .univ :=
  ⟨.univ, .univ⟩

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  given: [Nonempty α] (hs : IsClub s)
  statement: s.Nonempty
  proof: hs.isCofinal.nonempty

中文:
定理 nonempty
  条件: [Nonempty α] (hs : IsClub s)
  结论: s.Nonempty
  证明: hs.isCofinal.nonempty
-/
protected theorem nonempty [Nonempty α] (hs : IsClub s) : s.Nonempty :=
  hs.isCofinal.nonempty

/--
theorem `_root_.isClub_empty_iff` / 定理 `_root_.isClub_empty_iff`

English:
theorem _root_.isClub_empty_iff
  statement: IsClub (α := α) ∅ ↔ IsEmpty α
  proof: ⟨fun h => isCofinal_empty_iff.1 h.isCofinal, fun _ => .of_isEmpty⟩

中文:
定理 _root_.isClub_empty_iff
  结论: IsClub (α := α) ∅ ↔ IsEmpty α
  证明: ⟨fun h => isCofinal_empty_iff.1 h.isCofinal, fun _ => .of_isEmpty⟩

Depends on / 依赖: IsEmpty
-/
theorem _root_.isClub_empty_iff : IsClub (α := α) ∅ ↔ IsEmpty α :=
  ⟨fun h => isCofinal_empty_iff.1 h.isCofinal, fun _ => .of_isEmpty⟩

/--
theorem `union` / 定理 `union`

English:
theorem union
  given: (hs : IsClub s) (ht : IsClub t)
  statement: IsClub (s union t)
  proof: ⟨hs.dirSupClosed.union ht.dirSupClosed, hs.isCofinal.mono Set.subset_union_left⟩

中文:
定理 union
  条件: (hs : IsClub s) (ht : IsClub t)
  结论: IsClub (s union t)
  证明: ⟨hs.dirSupClosed.union ht.dirSupClosed, hs.isCofinal.mono Set.subset_union_left⟩
-/
protected theorem union (hs : IsClub s) (ht : IsClub t) : IsClub (s union t) :=
  ⟨hs.dirSupClosed.union ht.dirSupClosed, hs.isCofinal.mono Set.subset_union_left⟩

/--
theorem `isLUB_mem` / 定理 `isLUB_mem`

English:
theorem isLUB_mem
  given: (hs : IsClub s) (ht : t subseteq s) (ht₀ : t.Nonempty) (hx : IsLUB t x)
  statement: x in s
  proof: hs.dirSupClosed ht ht₀ (.of_linearOrder _) hx

中文:
定理 isLUB_mem
  条件: (hs : IsClub s) (ht : t subseteq s) (ht₀ : t.Nonempty) (hx : IsLUB t x)
  结论: x in s
  证明: hs.dirSupClosed ht ht₀ (.of_linearOrder _) hx

Depends on / 依赖: dirSupClosed, hs.dirSupClosed, of_linearOrder
-/
theorem isLUB_mem (hs : IsClub s) (ht : t subseteq s) (ht₀ : t.Nonempty) (hx : IsLUB t x) : x in s :=
  hs.dirSupClosed ht ht₀ (.of_linearOrder _) hx

/--
theorem `csSup_mem` / 定理 `csSup_mem`

English:
theorem csSup_mem
  statement: {α} [ConditionallyCompleteLinearOrder α] {s t : Set α}
  proof: hs.isLUB_mem ht ht₀ (isLUB_csSup ht₀ ht₁)

中文:
定理 csSup_mem
  结论: {α} [ConditionallyCompleteLinearOrder α] {s t : Set α}
  证明: hs.isLUB_mem ht ht₀ (isLUB_csSup ht₀ ht₁)

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_zmultiples_iff.mp, AddSubgroup.zmultiples_zero_eq_bot, Real.dist_eq, Submodule, Subsingleton, Subsingleton.discreteTopology, abs_mul, discreteTopology, discreteTopology_iff_isOpen_singleton_zero, dist_eq, eq_or_ne, hs.isLUB_mem, isLUB_csSup, isLUB_mem, isOpen_ball, isOpen_induced_iff, mem_zmultiples_iff, zmultiples_zero_eq_bot
-/
theorem csSup_mem {α} [ConditionallyCompleteLinearOrder α] {s t : Set α}
    (hs : IsClub s) (ht : t subseteq s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup t in s :=
  hs.isLUB_mem ht ht₀ (isLUB_csSup ht₀ ht₁)

/--
theorem `sInter_of_orderTop` / 定理 `sInter_of_orderTop`

English:
theorem sInter_of_orderTop
  given: {s : Set (Set α)} [OrderTop α] (hs : forall x in s, IsClub x)
  proof: by
  refine ⟨.sInter fun x hx => (hs x hx).dirSupClosed, ?_⟩
  rw [isCofinal_iff_top_mem]; rw [mem_sInter]
  exact fun x hx => (hs x hx).isCofinal.top_mem

中文:
定理 sInter_of_orderTop
  条件: {s : Set (Set α)} [OrderTop α] (hs : 对任意 x in s, IsClub x)
  证明: by
  refine ⟨.sInter fun x hx => (hs x hx).dirSupClosed, ?_⟩
  rw [isCofinal_iff_top_mem]; rw [mem_sInter]
  exact fun x hx => (hs x hx).isCofinal.top_mem

Depends on / 依赖: dirSupClosed, isCofinal, isCofinal.top_mem, isCofinal_iff_top_mem, mem_sInter, sInter, top_mem
-/
theorem sInter_of_orderTop {s : Set (Set α)} [OrderTop α] (hs : forall x in s, IsClub x) :
    IsClub (⋂₀ s) := by
  refine ⟨.sInter fun x hx => (hs x hx).dirSupClosed, ?_⟩
  rw [isCofinal_iff_top_mem]; rw [mem_sInter]
  exact fun x hx => (hs x hx).isCofinal.top_mem

/--
theorem `iInter_of_orderTop` / 定理 `iInter_of_orderTop`

English:
theorem iInter_of_orderTop
  given: {ι : Type*} {f : ι -> Set α} [OrderTop α] (hs : forall i, IsClub (f i))
  proof: by
  rw [← sInter_range]
  exact .sInter_of_orderTop (by simpa)

中文:
定理 iInter_of_orderTop
  条件: {ι : 类型} {f : ι -> Set α} [OrderTop α] (hs : 对任意 i, IsClub (f i))
  证明: by
  rw [← sInter_range]
  exact .sInter_of_orderTop (by simpa)

Depends on / 依赖: sInter_of_orderTop, sInter_range
-/
theorem iInter_of_orderTop {ι : Type*} {f : ι -> Set α} [OrderTop α] (hs : forall i, IsClub (f i)) :
    IsClub (⋂ i, f i) := by
  rw [← sInter_range]
  exact .sInter_of_orderTop (by simpa)

/--
theorem `sInter_of_cof_le_one` / 定理 `sInter_of_cof_le_one`

English:
theorem sInter_of_cof_le_one
  given: {s : Set (Set α)} (hα : cof α <= 1) (hs : forall x in s, IsClub x)
  proof: by
  cases isEmpty_or_nonempty α; · simp
  cases topOrderOrNoTopOrder α
  · exact .sInter_of_orderTop hs
  · cases one_lt_cof.not_ge hα

中文:
定理 sInter_of_cof_le_one
  条件: {s : Set (Set α)} (hα : cof α <= 1) (hs : 对任意 x in s, IsClub x)
  证明: by
  cases isEmpty_or_nonempty α; · simp
  cases topOrderOrNoTopOrder α
  · exact .sInter_of_orderTop hs
  · cases one_lt_cof.not_ge hα

Depends on / 依赖: isEmpty_or_nonempty, not_ge, one_lt_cof, one_lt_cof.not_ge, sInter_of_orderTop, topOrderOrNoTopOrder
-/
theorem sInter_of_cof_le_one {s : Set (Set α)} (hα : cof α <= 1) (hs : forall x in s, IsClub x) :
    IsClub (⋂₀ s) := by
  cases isEmpty_or_nonempty α; · simp
  cases topOrderOrNoTopOrder α
  · exact .sInter_of_orderTop hs
  · cases one_lt_cof.not_ge hα

/--
theorem `iInter_of_cof_le_one` / 定理 `iInter_of_cof_le_one`

English:
theorem iInter_of_cof_le_one
  given: {ι : Type*} {f : ι -> Set α} (hα : cof α <= 1) (hs : forall i, IsClub (f i))
  proof: by
  rw [← sInter_range]
  exact .sInter_of_cof_le_one hα (by simpa)

中文:
定理 iInter_of_cof_le_one
  条件: {ι : 类型} {f : ι -> Set α} (hα : cof α <= 1) (hs : 对任意 i, IsClub (f i))
  证明: by
  rw [← sInter_range]
  exact .sInter_of_cof_le_one hα (by simpa)

Depends on / 依赖: sInter_of_cof_le_one, sInter_range
-/
theorem iInter_of_cof_le_one {ι : Type*} {f : ι -> Set α} (hα : cof α <= 1) (hs : forall i, IsClub (f i)) :
    IsClub (⋂ i, f i) := by
  rw [← sInter_range]
  exact .sInter_of_cof_le_one hα (by simpa)

section WellFoundedLT
variable [WellFoundedLT α]

attribute [local instance]
  WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot

/--
theorem `sInter` / 定理 `sInter`

English:
theorem sInter
  statement: {s : Set (Set α)} (hα : cof α != ℵ₀) (hsα : #s < cof α)
  proof: by
  cases isEmpty_or_nonempty α; · simp
  obtain hα | hα := hα.lt_or_gt
  · exact .sInter_of_cof_le_one (cof_lt_aleph0_iff.1 hα) hs
  refine ⟨.sInter fun x hx => (hs x hx).dirSupClosed, fun a => ?_⟩
  choose f hf using fun x : s => (hs _ x.2).isCofinal
  let g : Nat -> α := Nat.rec a fun _ IH => sS

中文:
定理 sInter
  结论: {s : Set (Set α)} (hα : cof α != ℵ₀) (hsα : #s < cof α)
  证明: by
  cases isEmpty_or_nonempty α; · simp
  obtain hα | hα := hα.lt_or_gt
  · exact .sInter_of_cof_le_one (cof_lt_aleph0_iff.1 hα) hs
  refine ⟨.sInter fun x hx => (hs x hx).dirSupClosed, fun a => ?_⟩
  choose f hf using fun x : s => (hs _ x.2).isCofinal
  let g : Nat -> α := Nat.rec a fun _ IH => sS
-/
protected theorem sInter {s : Set (Set α)} (hα : cof α != ℵ₀) (hsα : #s < cof α)
    (hs : forall x in s, IsClub x) : IsClub (⋂₀ s) := by
  cases isEmpty_or_nonempty α; · simp
  obtain hα | hα := hα.lt_or_gt
  · exact .sInter_of_cof_le_one (cof_lt_aleph0_iff.1 hα) hs
  refine ⟨.sInter fun x hx => (hs x hx).dirSupClosed, fun a => ?_⟩
  choose f hf using fun x : s => (hs _ x.2).isCofinal
  let g : Nat -> α := Nat.rec a fun _ IH => sSup (.range (f · IH))
  have hg : BddAbove (.range g) := by
    refine .of_not_isCofinal fun hg => (cof_le hg).not_gt (hα.trans_le' ?_)
    simpa using mk_range_le_lift (f := g)
  refine ⟨_, fun t ht => ?_, le_csSup hg ⟨0, rfl⟩⟩
  apply (hs t ht).isLUB_mem (t := .range fun n => f ⟨t, ht⟩ (g n)) _ (range_nonempty _)
  · refine ⟨?_, fun b hb => csSup_le' ?_⟩ <;> rintro _ ⟨n, rfl⟩
    · apply (le_csSup (.of_not_isCofinal _) _).trans (le_csSup hg ⟨n + 1, rfl⟩)
      · exact fun hg' => (cof_le hg').not_gt (mk_range_le.trans_lt hsα)
      · use ⟨t, ht⟩
· exact (hf ⟨t, ht⟩ _).2.trans hb ⟨_, rfl⟩
  · grind

/--
theorem `iInter` / 定理 `iInter`

English:
theorem iInter
  statement: {ι : Type u} {f : ι -> Set α} (hα : cof α != ℵ₀)
  proof: by
  rw [← sInter_range]
  refine IsClub.sInter hα ?_ (by simpa)
  rw [← Cardinal.lift_lt]
  exact mk_range_le_lift.trans_lt hι

中文:
定理 iInter
  结论: {ι : 类型u} {f : ι -> Set α} (hα : cof α != ℵ₀)
  证明: by
  rw [← sInter_range]
  refine IsClub.sInter hα ?_ (by simpa)
  rw [← Cardinal.lift_lt]
  exact mk_range_le_lift.trans_lt hι
-/
protected theorem iInter {ι : Type u} {f : ι -> Set α} (hα : cof α != ℵ₀)
    (hι : Cardinal.lift.{v} #ι < Cardinal.lift.{u} (cof α)) (hf : forall i, IsClub (f i)) :
    IsClub (⋂ i, f i) := by
  rw [← sInter_range]
  refine IsClub.sInter hα ?_ (by simpa)
  rw [← Cardinal.lift_lt]
  exact mk_range_le_lift.trans_lt hι

/--
theorem `sInter_of_countable` / 定理 `sInter_of_countable`

English:
theorem sInter_of_countable
  statement: {s : Set (Set α)} (hα : cof α != ℵ₀) (hsα : s.Countable)
  proof: by
  obtain hα | hα := hα.lt_or_gt
  · apply IsClub.sInter_of_cof_le_one _ hs
    rwa [← cof_lt_aleph0_iff]
  · apply IsClub.sInter hα.ne' (hα.trans_le' _) hs
    rwa [le_aleph0_iff_set_countable]

中文:
定理 sInter_of_countable
  结论: {s : Set (Set α)} (hα : cof α != ℵ₀) (hsα : s.Countable)
  证明: by
  obtain hα | hα := hα.lt_or_gt
  · apply IsClub.sInter_of_cof_le_one _ hs
    rwa [← cof_lt_aleph0_iff]
  · apply IsClub.sInter hα.ne' (hα.trans_le' _) hs
    rwa [le_aleph0_iff_set_countable]

Depends on / 依赖: IsClub, IsClub.sInter, IsClub.sInter_of_cof_le_one, cof_lt_aleph0_iff, le_aleph0_iff_set_countable, lt_or_gt, sInter, sInter_of_cof_le_one, trans_le
-/
theorem sInter_of_countable {s : Set (Set α)} (hα : cof α != ℵ₀) (hsα : s.Countable)
    (hs : forall x in s, IsClub x) : IsClub (⋂₀ s) := by
  obtain hα | hα := hα.lt_or_gt
  · apply IsClub.sInter_of_cof_le_one _ hs
    rwa [← cof_lt_aleph0_iff]
  · apply IsClub.sInter hα.ne' (hα.trans_le' _) hs
    rwa [le_aleph0_iff_set_countable]

/--
theorem `iInter_of_countable` / 定理 `iInter_of_countable`

English:
theorem iInter_of_countable
  statement: {ι : Sort*} {f : ι -> Set α} [Countable ι] (hα : cof α != ℵ₀)
  proof: by
  rw [← sInter_range]
  apply IsClub.sInter_of_countable hα (countable_range f)
  simpa

中文:
定理 iInter_of_countable
  结论: {ι : Sort*} {f : ι -> Set α} [Countable ι] (hα : cof α != ℵ₀)
  证明: by
  rw [← sInter_range]
  apply IsClub.sInter_of_countable hα (countable_range f)
  simpa

Depends on / 依赖: IsClub, IsClub.sInter_of_countable, countable_range, sInter_of_countable, sInter_range
-/
theorem iInter_of_countable {ι : Sort*} {f : ι -> Set α} [Countable ι] (hα : cof α != ℵ₀)
    (hf : forall i, IsClub (f i)) : IsClub (⋂ i, f i) := by
  rw [← sInter_range]
  apply IsClub.sInter_of_countable hα (countable_range f)
  simpa

/--
theorem `inter` / 定理 `inter`

English:
theorem inter
  given: (hα : cof α != ℵ₀) (hs : IsClub s) (ht : IsClub t)
  statement: IsClub (s inter t)
  proof: by
  simpa [hs, ht] using IsClub.sInter_of_countable (s := {s, t}) hα

中文:
定理 inter
  条件: (hα : cof α != ℵ₀) (hs : IsClub s) (ht : IsClub t)
  结论: IsClub (s inter t)
  证明: by
  simpa [hs, ht] using IsClub.sInter_of_countable (s := {s, t}) hα
-/
protected theorem inter (hα : cof α != ℵ₀) (hs : IsClub s) (ht : IsClub t) : IsClub (s inter t) := by
  simpa [hs, ht] using IsClub.sInter_of_countable (s := {s, t}) hα

/--
theorem `_root_.Order.IsNormal.isClub_range` / 定理 `_root_.Order.IsNormal.isClub_range`

English:
theorem _root_.Order.IsNormal.isClub_range
  given: {f : α -> α} (hf : IsNormal f)
  statement: IsClub (.range f)
  proof: ⟨hf.dirSupClosed_range, fun x => ⟨_, ⟨x, rfl⟩, hf.strictMono.le_apply⟩⟩

中文:
定理 _root_.Order.IsNormal.isClub_range
  条件: {f : α -> α} (hf : IsNormal f)
  结论: IsClub (.range f)
  证明: ⟨hf.dirSupClosed_range, fun x => ⟨_, ⟨x, rfl⟩, hf.strictMono.le_apply⟩⟩

Depends on / 依赖: dirSupClosed_range, hf.dirSupClosed_range, hf.strictMono.le_apply, le_apply, strictMono
-/
theorem _root_.Order.IsNormal.isClub_range {f : α -> α} (hf : IsNormal f) : IsClub (.range f) :=
  ⟨hf.dirSupClosed_range, fun x => ⟨_, ⟨x, rfl⟩, hf.strictMono.le_apply⟩⟩

/--
theorem `_root_.Order.IsNormal.isClub_fixedPoints` / 定理 `_root_.Order.IsNormal.isClub_fixedPoints`

English:
theorem _root_.Order.IsNormal.isClub_fixedPoints
  given: {f : α -> α} (hα : cof α != ℵ₀) (hf : IsNormal f)
  proof: by
  cases isEmpty_or_nonempty α; · simp
  refine ⟨fun s hs hs₀ _ a ha => (hf.map_isLUB ha hs₀).unique ?_, fun a => ?_⟩
  · rwa [image_congr hs, image_id']
  · cases topOrderOrNoTopOrder α with
    | inl => use ⊤; simpa using! hf.strictMono.id_le ⊤
    | inr h =>
      rw [noTopOrder_iff_noMaxOrder]

中文:
定理 _root_.Order.IsNormal.isClub_fixedPoints
  条件: {f : α -> α} (hα : cof α != ℵ₀) (hf : IsNormal f)
  证明: by
  cases isEmpty_or_nonempty α; · simp
  refine ⟨fun s hs hs₀ _ a ha => (hf.map_isLUB ha hs₀).unique ?_, fun a => ?_⟩
  · rwa [image_congr hs, image_id']
  · cases topOrderOrNoTopOrder α with
    | inl => use ⊤; simpa using! hf.strictMono.id_le ⊤
    | inr h =>
      rw [noTopOrder_iff_noMaxOrder]

Depends on / 依赖: BddAbove, aleph0_le_cof, aleph0_le_cof.lt_of_ne, cof_le, hf.iSup_iterate_mem_fixedPoints, hf.map_isLUB, hf.strictMono.id_le, iSup_iterate_mem_fixedPoints, id_le, image_congr, image_id, isEmpty_or_nonempty, le_csSup, lt_of_ne, map_isLUB, noTopOrder_iff_noMaxOrder, not_gt, of_not_isCofinal, strictMono, topOrderOrNoTopOrder
-/
theorem _root_.Order.IsNormal.isClub_fixedPoints {f : α -> α} (hα : cof α != ℵ₀) (hf : IsNormal f) :
    IsClub f.fixedPoints := by
  cases isEmpty_or_nonempty α; · simp
  refine ⟨fun s hs hs₀ _ a ha => (hf.map_isLUB ha hs₀).unique ?_, fun a => ?_⟩
  · rwa [image_congr hs, image_id']
  · cases topOrderOrNoTopOrder α with
    | inl => use ⊤; simpa using! hf.strictMono.id_le ⊤
    | inr h =>
      rw [noTopOrder_iff_noMaxOrder] at h
      suffices BddAbove (.range fun n => f^[n] a) from
        ⟨_, hf.iSup_iterate_mem_fixedPoints a this, le_csSup this ⟨0, rfl⟩⟩
      refine .of_not_isCofinal fun h => (cof_le h).not_gt
        ((aleph0_le_cof.lt_of_ne' hα).trans_le' ?_)
      simpa using mk_range_le_lift (f := fun n : Nat => f^[n] a)

/--
theorem `_root_.Order.isNormal_enum_iff_isClub` / 定理 `_root_.Order.isNormal_enum_iff_isClub`

English:
theorem _root_.Order.isNormal_enum_iff_isClub
  statement: [IsRegularCardinalOrder α]
  proof: by
  simp_rw [isClub_iff, hs, and_true, isNormal_enum_iff_dirSupClosed]

中文:
定理 _root_.Order.isNormal_enum_iff_isClub
  结论: [IsRegularCardinalOrder α]
  证明: by
  simp_rw [isClub_iff, hs, and_true, isNormal_enum_iff_dirSupClosed]

Depends on / 依赖: and_true, isClub_iff, isNormal_enum_iff_dirSupClosed, simp_rw
-/
theorem _root_.Order.isNormal_enum_iff_isClub [IsRegularCardinalOrder α]
    {s : Set α} {hs : IsCofinal s} : IsNormal (Subtype.val ∘ enum s hs) ↔ IsClub s := by
  simp_rw [isClub_iff, hs, and_true, isNormal_enum_iff_dirSupClosed]

/--
theorem `isNormal_enum` / 定理 `isNormal_enum`

English:
theorem isNormal_enum
  given: [IsRegularCardinalOrder α] {s : Set α} (hs : IsClub s)
  proof: isNormal_enum_iff_isClub.2 hs

中文:
定理 isNormal_enum
  条件: [IsRegularCardinalOrder α] {s : Set α} (hs : IsClub s)
  证明: isNormal_enum_iff_isClub.2 hs

Depends on / 依赖: isNormal_enum_iff_isClub
-/
theorem isNormal_enum [IsRegularCardinalOrder α] {s : Set α} (hs : IsClub s) :
    IsNormal (Subtype.val ∘ enum s hs.isCofinal) :=
  isNormal_enum_iff_isClub.2 hs

end WellFoundedLT
end IsClub

/-! ### Stationary sets -/

/-- A set is called stationary when it intersects all club sets. -/
@[expose]
/--
Definition of `IsStationary` / `IsStationary` 的定义

English:
definition IsStationary
  signature: (s : Set α)
  body: forall ⦃t⦄, IsClub t -> (s inter t).Nonempty

中文:
定义 IsStationary
  签名: (s : Set α)
  定义体: forall ⦃t⦄, IsClub t -> (s inter t).Nonempty

Depends on / 依赖: IsClub, Nonempty
-/
def IsStationary (s : Set α) : Prop :=
  forall ⦃t⦄, IsClub t -> (s inter t).Nonempty

/--
theorem `not_isStationary_iff` / 定理 `not_isStationary_iff`

English:
theorem not_isStationary_iff
  statement: ¬ IsStationary s ↔ exists t, IsClub t ∧ Disjoint s t
  proof: by
  simp [IsStationary, disjoint_iff, not_nonempty_iff_eq_empty]

@[gcongr]

中文:
定理 not_isStationary_iff
  结论: ¬ IsStationary s ↔ 存在 t, IsClub t ∧ Disjoint s t
  证明: by
  simp [IsStationary, disjoint_iff, not_nonempty_iff_eq_empty]

@[gcongr]

Depends on / 依赖: IsStationary, disjoint_iff, not_nonempty_iff_eq_empty
-/
theorem not_isStationary_iff : ¬ IsStationary s ↔ exists t, IsClub t ∧ Disjoint s t := by
  simp [IsStationary, disjoint_iff, not_nonempty_iff_eq_empty]

@[gcongr]
/--
theorem `IsStationary.mono` / 定理 `IsStationary.mono`

English:
theorem IsStationary.mono
  given: (hs : IsStationary s) (h : s subseteq t)
  statement: IsStationary t
  proof: fun _u hu => (hs hu).mono (inter_subset_inter_left _ h)

中文:
定理 IsStationary.mono
  条件: (hs : IsStationary s) (h : s subseteq t)
  结论: IsStationary t
  证明: fun _u hu => (hs hu).mono (inter_subset_inter_left _ h)

Depends on / 依赖: inter_subset_inter_left
-/
theorem IsStationary.mono (hs : IsStationary s) (h : s subseteq t) : IsStationary t :=
  fun _u hu => (hs hu).mono (inter_subset_inter_left _ h)

/--
theorem `IsStationary.nonempty` / 定理 `IsStationary.nonempty`

English:
theorem IsStationary.nonempty
  given: (hs : IsStationary s)
  statement: s.Nonempty
  proof: by
  simpa using hs .univ

中文:
定理 IsStationary.nonempty
  条件: (hs : IsStationary s)
  结论: s.Nonempty
  证明: by
  simpa using hs .univ
-/
theorem IsStationary.nonempty (hs : IsStationary s) : s.Nonempty := by
  simpa using hs .univ

/--
theorem `isStationary_univ_iff` / 定理 `isStationary_univ_iff`

English:
theorem isStationary_univ_iff
  statement: IsStationary (.univ (α := α)) ↔ Nonempty α
  proof: by
  simp [IsStationary, ← not_imp_not (b := IsClub _), not_nonempty_iff_eq_empty,
    isClub_empty_iff]

@[simp]

中文:
定理 isStationary_univ_iff
  结论: IsStationary (.univ (α := α)) ↔ Nonempty α
  证明: by
  simp [IsStationary, ← not_imp_not (b := IsClub _), not_nonempty_iff_eq_empty,
    isClub_empty_iff]

@[simp]

Depends on / 依赖: IsClub, IsStationary, Nonempty, isClub_empty_iff, not_imp_not, not_nonempty_iff_eq_empty
-/
theorem isStationary_univ_iff : IsStationary (.univ (α := α)) ↔ Nonempty α := by
  simp [IsStationary, ← not_imp_not (b := IsClub _), not_nonempty_iff_eq_empty,
    isClub_empty_iff]

@[simp]
/--
theorem `IsStationary.univ` / 定理 `IsStationary.univ`

English:
theorem IsStationary.univ
  given: [Nonempty α]
  statement: IsStationary (.univ (α := α))
  proof: isStationary_univ_iff.2 ‹_›

@[simp]

中文:
定理 IsStationary.univ
  条件: [Nonempty α]
  结论: IsStationary (.univ (α := α))
  证明: isStationary_univ_iff.2 ‹_›

@[simp]
-/
protected theorem IsStationary.univ [Nonempty α] : IsStationary (.univ (α := α)) :=
  isStationary_univ_iff.2 ‹_›

@[simp]
/--
theorem `not_isStationary_empty` / 定理 `not_isStationary_empty`

English:
theorem not_isStationary_empty
  statement: ¬ IsStationary (∅ : Set α)
  proof: by
  intro h
  simpa using h .univ

@[simp]

中文:
定理 not_isStationary_empty
  结论: ¬ IsStationary (∅ : Set α)
  证明: by
  intro h
  simpa using h .univ

@[simp]
-/
theorem not_isStationary_empty : ¬ IsStationary (∅ : Set α) := by
  intro h
  simpa using h .univ

@[simp]
/--
theorem `not_isStationary_of_isEmpty` / 定理 `not_isStationary_of_isEmpty`

English:
theorem not_isStationary_of_isEmpty
  given: [IsEmpty α]
  statement: ¬ IsStationary s
  proof: s.eq_empty_of_isEmpty ▸ not_isStationary_empty

中文:
定理 not_isStationary_of_isEmpty
  条件: [IsEmpty α]
  结论: ¬ IsStationary s
  证明: s.eq_empty_of_isEmpty ▸ not_isStationary_empty

Depends on / 依赖: eq_empty_of_isEmpty, not_isStationary_empty, s.eq_empty_of_isEmpty
-/
theorem not_isStationary_of_isEmpty [IsEmpty α] : ¬ IsStationary s :=
  s.eq_empty_of_isEmpty ▸ not_isStationary_empty

/--
theorem `IsStationary.of_not_isCofinal_compl` / 定理 `IsStationary.of_not_isCofinal_compl`

English:
theorem IsStationary.of_not_isCofinal_compl
  given: (hs : ¬ IsCofinal sᶜ)
  statement: IsStationary s
  proof: by
  intro t ht
  obtain ⟨a, ha⟩ := not_isCofinal_iff.1 hs
  obtain ⟨b, hb, hb'⟩ := ht.isCofinal a
  refine ⟨b, ?_, hb⟩
  contrapose! ha
  exact ⟨b, ha, hb'⟩

中文:
定理 IsStationary.of_not_isCofinal_compl
  条件: (hs : ¬ IsCofinal sᶜ)
  结论: IsStationary s
  证明: by
  intro t ht
  obtain ⟨a, ha⟩ := not_isCofinal_iff.1 hs
  obtain ⟨b, hb, hb'⟩ := ht.isCofinal a
  refine ⟨b, ?_, hb⟩
  contrapose! ha
  exact ⟨b, ha, hb'⟩

Depends on / 依赖: contrapose, ht.isCofinal, isCofinal, not_isCofinal_iff
-/
theorem IsStationary.of_not_isCofinal_compl (hs : ¬ IsCofinal sᶜ) : IsStationary s := by
  intro t ht
  obtain ⟨a, ha⟩ := not_isCofinal_iff.1 hs
  obtain ⟨b, hb, hb'⟩ := ht.isCofinal a
  refine ⟨b, ?_, hb⟩
  contrapose! ha
  exact ⟨b, ha, hb'⟩

/--
theorem `isStationary_sUnion_iff_of_cof_le_one` / 定理 `isStationary_sUnion_iff_of_cof_le_one`

English:
theorem isStationary_sUnion_iff_of_cof_le_one
  given: {s : Set (Set α)} (hα : cof α <= 1)
  proof: by
    contrapose! h
    simp_rw [not_isStationary_iff] at h ⊢
    choose f hf hxf using h
    refine ⟨⋂ x : s, f _ x.2, ?_, ?_⟩
    · apply IsClub.iInter_of_cof_le_one hα
      simpa
    · rw [disjoint_sUnion_left]
      exact fun x hx => (hxf _ hx).mono_right (iInter_subset _ ⟨x, hx⟩)
  mpr := fun

中文:
定理 isStationary_sUnion_iff_of_cof_le_one
  条件: {s : Set (Set α)} (hα : cof α <= 1)
  证明: by
    contrapose! h
    simp_rw [not_isStationary_iff] at h ⊢
    choose f hf hxf using h
    refine ⟨⋂ x : s, f _ x.2, ?_, ?_⟩
    · apply IsClub.iInter_of_cof_le_one hα
      simpa
    · rw [disjoint_sUnion_left]
      exact fun x hx => (hxf _ hx).mono_right (iInter_subset _ ⟨x, hx⟩)
  mpr := fun

Depends on / 依赖: IsClub, IsClub.iInter_of_cof_le_one, contrapose, disjoint_sUnion_left, hx.mono, iInter_of_cof_le_one, iInter_subset, mono_right, not_isStationary_iff, simp_rw, subset_sUnion_of_mem
-/
theorem isStationary_sUnion_iff_of_cof_le_one {s : Set (Set α)} (hα : cof α <= 1) :
    IsStationary (⋃₀ s) ↔ exists x in s, IsStationary x where
  mp h := by
    contrapose! h
    simp_rw [not_isStationary_iff] at h ⊢
    choose f hf hxf using h
    refine ⟨⋂ x : s, f _ x.2, ?_, ?_⟩
    · apply IsClub.iInter_of_cof_le_one hα
      simpa
    · rw [disjoint_sUnion_left]
      exact fun x hx => (hxf _ hx).mono_right (iInter_subset _ ⟨x, hx⟩)
  mpr := fun ⟨x, hxs, hx⟩ => hx.mono (subset_sUnion_of_mem hxs)

/--
theorem `isStationary_iUnion_iff_of_cof_le_one` / 定理 `isStationary_iUnion_iff_of_cof_le_one`

English:
theorem isStationary_iUnion_iff_of_cof_le_one
  given: {ι : Sort*} {f : ι -> Set α} (hα : cof α <= 1)
  proof: by
  rw [← sUnion_range]; rw [isStationary_sUnion_iff_of_cof_le_one hα]
  simp

中文:
定理 isStationary_iUnion_iff_of_cof_le_one
  条件: {ι : Sort*} {f : ι -> Set α} (hα : cof α <= 1)
  证明: by
  rw [← sUnion_range]; rw [isStationary_sUnion_iff_of_cof_le_one hα]
  simp

Depends on / 依赖: isStationary_sUnion_iff_of_cof_le_one, sUnion_range
-/
theorem isStationary_iUnion_iff_of_cof_le_one {ι : Sort*} {f : ι -> Set α} (hα : cof α <= 1) :
    IsStationary (⋃ i, f i) ↔ exists i, IsStationary (f i) := by
  rw [← sUnion_range]; rw [isStationary_sUnion_iff_of_cof_le_one hα]
  simp

/--
theorem `isStationary_sUnion_iff_of_orderTop` / 定理 `isStationary_sUnion_iff_of_orderTop`

English:
theorem isStationary_sUnion_iff_of_orderTop
  given: [OrderTop α] {s : Set (Set α)}
  proof: isStationary_sUnion_iff_of_cof_le_one (by simp)

中文:
定理 isStationary_sUnion_iff_of_orderTop
  条件: [OrderTop α] {s : Set (Set α)}
  证明: isStationary_sUnion_iff_of_cof_le_one (by simp)

Depends on / 依赖: isStationary_sUnion_iff_of_cof_le_one
-/
theorem isStationary_sUnion_iff_of_orderTop [OrderTop α] {s : Set (Set α)} :
    IsStationary (⋃₀ s) ↔ exists x in s, IsStationary x :=
  isStationary_sUnion_iff_of_cof_le_one (by simp)

/--
theorem `isStationary_iUnion_iff_of_orderTop` / 定理 `isStationary_iUnion_iff_of_orderTop`

English:
theorem isStationary_iUnion_iff_of_orderTop
  given: [OrderTop α] {ι : Sort*} {f : ι -> Set α}
  proof: isStationary_iUnion_iff_of_cof_le_one (by simp)

中文:
定理 isStationary_iUnion_iff_of_orderTop
  条件: [OrderTop α] {ι : Sort*} {f : ι -> Set α}
  证明: isStationary_iUnion_iff_of_cof_le_one (by simp)

Depends on / 依赖: isStationary_iUnion_iff_of_cof_le_one
-/
theorem isStationary_iUnion_iff_of_orderTop [OrderTop α] {ι : Sort*} {f : ι -> Set α} :
    IsStationary (⋃ i, f i) ↔ exists i, IsStationary (f i) :=
  isStationary_iUnion_iff_of_cof_le_one (by simp)

section WellFoundedLT
variable [WellFoundedLT α]

/--
theorem `IsClub.isStationary` / 定理 `IsClub.isStationary`

English:
theorem IsClub.isStationary
  given: [Nonempty α] (hα : cof α != ℵ₀) (hs : IsClub s)
  statement: IsStationary s
  proof: fun _ ht => (hs.inter hα ht).nonempty

中文:
定理 IsClub.isStationary
  条件: [Nonempty α] (hα : cof α != ℵ₀) (hs : IsClub s)
  结论: IsStationary s
  证明: fun _ ht => (hs.inter hα ht).nonempty

Depends on / 依赖: hs.inter, nonempty
-/
theorem IsClub.isStationary [Nonempty α] (hα : cof α != ℵ₀) (hs : IsClub s) : IsStationary s :=
  fun _ ht => (hs.inter hα ht).nonempty

/--
theorem `isStationary_sUnion_iff` / 定理 `isStationary_sUnion_iff`

English:
theorem isStationary_sUnion_iff
  given: {s : Set (Set α)} (hα : cof α != ℵ₀) (hsα : #s < cof α)
  proof: by
    contrapose! h
    simp_rw [not_isStationary_iff] at h ⊢
    choose f hf hxf using h
    refine ⟨⋂ x : s, f _ x.2, ?_, ?_⟩
    · apply IsClub.iInter hα <;> simpa
    · rw [disjoint_sUnion_left]
      exact fun x hx => (hxf _ hx).mono_right (iInter_subset _ ⟨x, hx⟩)
  mpr := fun ⟨x, hxs, hx⟩ =>

中文:
定理 isStationary_sUnion_iff
  条件: {s : Set (Set α)} (hα : cof α != ℵ₀) (hsα : #s < cof α)
  证明: by
    contrapose! h
    simp_rw [not_isStationary_iff] at h ⊢
    choose f hf hxf using h
    refine ⟨⋂ x : s, f _ x.2, ?_, ?_⟩
    · apply IsClub.iInter hα <;> simpa
    · rw [disjoint_sUnion_left]
      exact fun x hx => (hxf _ hx).mono_right (iInter_subset _ ⟨x, hx⟩)
  mpr := fun ⟨x, hxs, hx⟩ =>

Depends on / 依赖: IsClub, IsClub.iInter, contrapose, disjoint_sUnion_left, hx.mono, iInter, iInter_subset, mono_right, not_isStationary_iff, simp_rw, subset_sUnion_of_mem
-/
theorem isStationary_sUnion_iff {s : Set (Set α)} (hα : cof α != ℵ₀) (hsα : #s < cof α) :
    IsStationary (⋃₀ s) ↔ exists x in s, IsStationary x where
  mp h := by
    contrapose! h
    simp_rw [not_isStationary_iff] at h ⊢
    choose f hf hxf using h
    refine ⟨⋂ x : s, f _ x.2, ?_, ?_⟩
    · apply IsClub.iInter hα <;> simpa
    · rw [disjoint_sUnion_left]
      exact fun x hx => (hxf _ hx).mono_right (iInter_subset _ ⟨x, hx⟩)
  mpr := fun ⟨x, hxs, hx⟩ => hx.mono (subset_sUnion_of_mem hxs)

/--
theorem `isStationary_iUnion_iff` / 定理 `isStationary_iUnion_iff`

English:
theorem isStationary_iUnion_iff
  statement: {ι : Type u} {f : ι -> Set α} (hα : cof α != ℵ₀)
  proof: by
  rw [← sUnion_range]; rw [isStationary_sUnion_iff hα]
  · simp
  · rw [← Cardinal.lift_lt]
    exact mk_range_le_lift.trans_lt hι

中文:
定理 isStationary_iUnion_iff
  结论: {ι : 类型u} {f : ι -> Set α} (hα : cof α != ℵ₀)
  证明: by
  rw [← sUnion_range]; rw [isStationary_sUnion_iff hα]
  · simp
  · rw [← Cardinal.lift_lt]
    exact mk_range_le_lift.trans_lt hι

Depends on / 依赖: Cardinal, Cardinal.lift_lt, isStationary_sUnion_iff, lift_lt, mk_range_le_lift, mk_range_le_lift.trans_lt, sUnion_range, trans_lt
-/
theorem isStationary_iUnion_iff {ι : Type u} {f : ι -> Set α} (hα : cof α != ℵ₀)
    (hι : lift.{v} #ι < lift.{u} (cof α)) : IsStationary (⋃ i, f i) ↔ exists i, IsStationary (f i) := by
  rw [← sUnion_range]; rw [isStationary_sUnion_iff hα]
  · simp
  · rw [← Cardinal.lift_lt]
    exact mk_range_le_lift.trans_lt hι

/--
theorem `isStationary_sUnion_iff_of_countable` / 定理 `isStationary_sUnion_iff_of_countable`

English:
theorem isStationary_sUnion_iff_of_countable
  statement: {s : Set (Set α)} (hα : cof α != ℵ₀)
  proof: by
  obtain hα | hα := hα.lt_or_gt
  · apply isStationary_sUnion_iff_of_cof_le_one
    rwa [← cof_lt_aleph0_iff]
  · apply isStationary_sUnion_iff hα.ne' (hα.trans_le' _)
    rwa [le_aleph0_iff_set_countable]

中文:
定理 isStationary_sUnion_iff_of_countable
  结论: {s : Set (Set α)} (hα : cof α != ℵ₀)
  证明: by
  obtain hα | hα := hα.lt_or_gt
  · apply isStationary_sUnion_iff_of_cof_le_one
    rwa [← cof_lt_aleph0_iff]
  · apply isStationary_sUnion_iff hα.ne' (hα.trans_le' _)
    rwa [le_aleph0_iff_set_countable]

Depends on / 依赖: cof_lt_aleph0_iff, isStationary_sUnion_iff, isStationary_sUnion_iff_of_cof_le_one, le_aleph0_iff_set_countable, lt_or_gt, trans_le
-/
theorem isStationary_sUnion_iff_of_countable {s : Set (Set α)} (hα : cof α != ℵ₀)
    (hsα : s.Countable) : IsStationary (⋃₀ s) ↔ exists x in s, IsStationary x := by
  obtain hα | hα := hα.lt_or_gt
  · apply isStationary_sUnion_iff_of_cof_le_one
    rwa [← cof_lt_aleph0_iff]
  · apply isStationary_sUnion_iff hα.ne' (hα.trans_le' _)
    rwa [le_aleph0_iff_set_countable]

/--
theorem `isStationary_iUnion_iff_of_countable` / 定理 `isStationary_iUnion_iff_of_countable`

English:
theorem isStationary_iUnion_iff_of_countable
  statement: {ι : Sort*} {f : ι -> Set α} [Countable ι]
  proof: by
  rw [← sUnion_range]; rw [isStationary_sUnion_iff_of_countable hα (countable_range f)]
  simp

中文:
定理 isStationary_iUnion_iff_of_countable
  结论: {ι : Sort*} {f : ι -> Set α} [Countable ι]
  证明: by
  rw [← sUnion_range]; rw [isStationary_sUnion_iff_of_countable hα (countable_range f)]
  simp

Depends on / 依赖: countable_range, isStationary_sUnion_iff_of_countable, sUnion_range
-/
theorem isStationary_iUnion_iff_of_countable {ι : Sort*} {f : ι -> Set α} [Countable ι]
    (hα : cof α != ℵ₀) : IsStationary (⋃ i, f i) ↔ exists i, IsStationary (f i) := by
  rw [← sUnion_range]; rw [isStationary_sUnion_iff_of_countable hα (countable_range f)]
  simp

/--
theorem `isStationary_union_iff` / 定理 `isStationary_union_iff`

English:
theorem isStationary_union_iff
  given: (hα : cof α != ℵ₀)
  proof: by
  simpa using isStationary_sUnion_iff_of_countable (s := {s, t}) hα

中文:
定理 isStationary_union_iff
  条件: (hα : cof α != ℵ₀)
  证明: by
  simpa using isStationary_sUnion_iff_of_countable (s := {s, t}) hα

Depends on / 依赖: isStationary_sUnion_iff_of_countable
-/
theorem isStationary_union_iff (hα : cof α != ℵ₀) :
    IsStationary (s union t) ↔ IsStationary s ∨ IsStationary t := by
  simpa using isStationary_sUnion_iff_of_countable (s := {s, t}) hα

end WellFoundedLT
