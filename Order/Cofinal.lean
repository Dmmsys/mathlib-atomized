/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.WellFounded

import Mathlib.Data.Set.Lattice

/-!
# Cofinal sets

A set `s` in an ordered type `α` is cofinal when for every `a : α` there exists an element of `s`
greater or equal to it. This file provides a basic API for the `IsCofinal` predicate.

For the cofinality of a set as a cardinal, see `Mathlib/SetTheory/Cardinal/Cofinality/Basic.lean`.

## TODO

- Deprecate `Order.Cofinal` in favor of this predicate.
-/

public section

open Set

variable {α β : Type*}

section LE
variable [LE α]

/--
theorem `IsCofinal.of_isEmpty` / 定理 `IsCofinal.of_isEmpty`

English:
theorem IsCofinal.of_isEmpty
  given: [IsEmpty α] {s : Set α}
  statement: IsCofinal s
  proof: fun a => isEmptyElim a

中文:
定理 IsCofinal.of_isEmpty
  条件: [是空 α] {s : 集合 α}
  结论: IsCofinal s
  证明: fun a => isEmptyElim a

Depends on / 依赖: isEmptyElim
-/
theorem IsCofinal.of_isEmpty [IsEmpty α] {s : Set α} : IsCofinal s :=
  fun a => isEmptyElim a

/--
theorem `isCofinal_empty_iff` / 定理 `isCofinal_empty_iff`

English:
theorem isCofinal_empty_iff
  statement: IsCofinal (∅ : Set α) ↔ IsEmpty α
  proof: by
  refine ⟨fun h => ⟨fun a => ?_⟩, fun h => .of_isEmpty⟩
  simpa using h a

中文:
定理 isCofinal_empty_iff
  结论: IsCofinal (∅ : 集合 α) ↔ 是空 α
  证明: by
  refine ⟨fun h => ⟨fun a => ?_⟩, fun h => .of_isEmpty⟩
  simpa using h a

Depends on / 依赖: of_isEmpty
-/
theorem isCofinal_empty_iff : IsCofinal (∅ : Set α) ↔ IsEmpty α := by
  refine ⟨fun h => ⟨fun a => ?_⟩, fun h => .of_isEmpty⟩
  simpa using h a

/--
theorem `IsCofinal.nonempty` / 定理 `IsCofinal.nonempty`

English:
theorem IsCofinal.nonempty
  given: [Nonempty α] {s : Set α} (hs : IsCofinal s)
  statement: s.Nonempty
  proof: by
  inhabit α
  exact (hs default).imp fun _ => And.left

@[simp]

中文:
定理 IsCofinal.nonempty
  条件: [非空 α] {s : 集合 α} (hs : IsCofinal s)
  结论: s.非空
  证明: by
  inhabit α
  exact (hs default).imp fun _ => And.left

@[simp]

Depends on / 依赖: And.left, inhabit, map_one, toMonoidHom, toMonoidHom.map_one
-/
theorem IsCofinal.nonempty [Nonempty α] {s : Set α} (hs : IsCofinal s) : s.Nonempty := by
  inhabit α
  exact (hs default).imp fun _ => And.left

@[simp]
/--
theorem `isCofinal_singleton_iff` / 定理 `isCofinal_singleton_iff`

English:
theorem isCofinal_singleton_iff
  given: {x : α}
  statement: IsCofinal {x} ↔ IsTop x
  proof: by
  simp [IsCofinal, IsTop]

中文:
定理 isCofinal_singleton_iff
  条件: {x : α}
  结论: IsCofinal {x} ↔ IsTop x
  证明: by
  simp [IsCofinal, IsTop]

Depends on / 依赖: IsCofinal
-/
theorem isCofinal_singleton_iff {x : α} : IsCofinal {x} ↔ IsTop x := by
  simp [IsCofinal, IsTop]

/--
theorem `IsCofinal.singleton_top` / 定理 `IsCofinal.singleton_top`

English:
theorem IsCofinal.singleton_top
  given: [OrderTop α]
  statement: IsCofinal {(⊤ : α)}
  proof: by
  simp

中文:
定理 IsCofinal.singleton_top
  条件: [有顶序 α]
  结论: IsCofinal {(⊤ : α)}
  证明: by
  simp
-/
theorem IsCofinal.singleton_top [OrderTop α] : IsCofinal {(⊤ : α)} := by
  simp

/--
theorem `IsCofinal.mono` / 定理 `IsCofinal.mono`

English:
theorem IsCofinal.mono
  given: {s t : Set α} (h : s subseteq t) (hs : IsCofinal s)
  statement: IsCofinal t
  proof: by
  intro a
  obtain ⟨b, hb, hb'⟩ := hs a
  exact ⟨b, h hb, hb'⟩

中文:
定理 IsCofinal.mono
  条件: {s t : 集合 α} (h : s subseteq t) (hs : IsCofinal s)
  结论: IsCofinal t
  证明: by
  intro a
  obtain ⟨b, hb, hb'⟩ := hs a
  exact ⟨b, h hb, hb'⟩
-/
theorem IsCofinal.mono {s t : Set α} (h : s subseteq t) (hs : IsCofinal s) : IsCofinal t := by
  intro a
  obtain ⟨b, hb, hb'⟩ := hs a
  exact ⟨b, h hb, hb'⟩

end LE

section Preorder
variable [Preorder α] [Preorder β]

@[simp]
/--
theorem `IsCofinal.univ` / 定理 `IsCofinal.univ`

English:
theorem IsCofinal.univ
  statement: IsCofinal (@univ α)
  proof: fun a => ⟨a, ⟨⟩, le_rfl⟩

中文:
定理 IsCofinal.univ
  结论: IsCofinal (@univ α)
  证明: fun a => ⟨a, ⟨⟩, le_rfl⟩

Depends on / 依赖: le_rfl
-/
theorem IsCofinal.univ : IsCofinal (@univ α) :=
  fun a => ⟨a, ⟨⟩, le_rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited {s : Set α // IsCofinal s}
  body: ⟨_, .univ⟩

中文:
实例 :
  签名: 可居 {s : 集合 α // IsCofinal s}
  定义体: ⟨_, .univ⟩
-/
instance : Inhabited {s : Set α // IsCofinal s} :=
  ⟨_, .univ⟩

/--
theorem `IsCofinal.image` / 定理 `IsCofinal.image`

English:
theorem IsCofinal.image
  statement: {f : α -> β} {s : Set α} (hs : IsCofinal s)
  proof: by
  intro a
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hf' a
  obtain ⟨c, hc, hc'⟩ := hs b
  exact ⟨_, mem_image_of_mem f hc, hb.trans (hf hc')⟩

中文:
定理 IsCofinal.像
  结论: {f : α -> β} {s : 集合 α} (hs : IsCofinal s)
  证明: by
  intro a
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hf' a
  obtain ⟨c, hc, hc'⟩ := hs b
  exact ⟨_, mem_image_of_mem f hc, hb.trans (hf hc')⟩

Depends on / 依赖: hb.trans, mem_image_of_mem
-/
theorem IsCofinal.image {f : α -> β} {s : Set α} (hs : IsCofinal s)
    (hf : Monotone f) (hf' : IsCofinal (.range f)) : IsCofinal (f '' s) := by
  intro a
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hf' a
  obtain ⟨c, hc, hc'⟩ := hs b
  exact ⟨_, mem_image_of_mem f hc, hb.trans (hf hc')⟩

/--
theorem `IsCofinal.trans` / 定理 `IsCofinal.trans`

English:
theorem IsCofinal.trans
  given: {s : Set α} {t : Set s} (hs : IsCofinal s) (ht : IsCofinal t)
  proof: ht.image (Subtype.mono_coe _) (by simpa)

中文:
定理 IsCofinal.trans
  条件: {s : 集合 α} {t : 集合 s} (hs : IsCofinal s) (ht : IsCofinal t)
  证明: ht.image (Subtype.mono_coe _) (by simpa)

Depends on / 依赖: Subtype, Subtype.mono_coe, ht.image, mono_coe
-/
theorem IsCofinal.trans {s : Set α} {t : Set s} (hs : IsCofinal s) (ht : IsCofinal t) :
    IsCofinal (Subtype.val '' t) :=
  ht.image (Subtype.mono_coe _) (by simpa)

/--
theorem `GaloisConnection.isCofinal_range` / 定理 `GaloisConnection.isCofinal_range`

English:
theorem GaloisConnection.isCofinal_range
  given: {f : β -> α} {g : α -> β} (h : GaloisConnection f g)
  proof: fun a => ⟨_, mem_range_self _, le_u_l h a⟩

中文:
定理 GaloisConnection.isCofinal_range
  条件: {f : β -> α} {g : α -> β} (h : GaloisConnection f g)
  证明: fun a => ⟨_, mem_range_self _, le_u_l h a⟩

Depends on / 依赖: le_u_l, mem_range_self
-/
theorem GaloisConnection.isCofinal_range {f : β -> α} {g : α -> β} (h : GaloisConnection f g) :
    IsCofinal (range g) :=
  fun a => ⟨_, mem_range_self _, le_u_l h a⟩

/--
theorem `GaloisConnection.map_isCofinal` / 定理 `GaloisConnection.map_isCofinal`

English:
theorem GaloisConnection.map_isCofinal
  statement: {f : β -> α} {g : α -> β}
  proof: hs.image h.monotone_u h.isCofinal_range

@[deprecated (since := "2026-03-15")]
alias GaloisConnection.map_cofinal := GaloisConnection.map_isCofinal

中文:
定理 GaloisConnection.map_isCofinal
  结论: {f : β -> α} {g : α -> β}
  证明: hs.image h.monotone_u h.isCofinal_range

@[deprecated (since := "2026-03-15")]
alias GaloisConnection.map_cofinal := GaloisConnection.map_isCofinal

Depends on / 依赖: h.isCofinal_range, h.monotone_u, hs.image, isCofinal_range, monotone_u
-/
theorem GaloisConnection.map_isCofinal {f : β -> α} {g : α -> β}
    (h : GaloisConnection f g) {s : Set α} (hs : IsCofinal s) : IsCofinal (g '' s) :=
  hs.image h.monotone_u h.isCofinal_range

@[deprecated (since := "2026-03-15")]
alias GaloisConnection.map_cofinal := GaloisConnection.map_isCofinal

/--
theorem `OrderIso.map_isCofinal` / 定理 `OrderIso.map_isCofinal`

English:
theorem OrderIso.map_isCofinal
  given: (e : α ≃o β) {s : Set α} (hs : IsCofinal s)
  statement: IsCofinal (e '' s)
  proof: e.symm.to_galoisConnection.map_isCofinal hs

@[simp]

中文:
定理 OrderIso.map_isCofinal
  条件: (e : α ≃o β) {s : 集合 α} (hs : IsCofinal s)
  结论: IsCofinal (e '' s)
  证明: e.symm.to_galoisConnection.map_isCofinal hs

@[simp]

Depends on / 依赖: e.symm.to_galoisConnection.map_isCofinal, f.toFun, map_isCofinal, to_galoisConnection
-/
theorem OrderIso.map_isCofinal (e : α ≃o β) {s : Set α} (hs : IsCofinal s) : IsCofinal (e '' s) :=
  e.symm.to_galoisConnection.map_isCofinal hs

@[simp]
/--
theorem `OrderIso.map_isCofinal_iff` / 定理 `OrderIso.map_isCofinal_iff`

English:
theorem OrderIso.map_isCofinal_iff
  given: (e : α ≃o β) {s : Set α}
  statement: IsCofinal (e '' s) ↔ IsCofinal s
  proof: ⟨fun hs => by simpa using e.symm.map_isCofinal hs, e.map_isCofinal⟩

@[deprecated (since := "2026-03-15")]
alias OrderIso.map_cofinal := OrderIso.map_isCofinal

中文:
定理 OrderIso.map_isCofinal_iff
  条件: (e : α ≃o β) {s : 集合 α}
  结论: IsCofinal (e '' s) ↔ IsCofinal s
  证明: ⟨fun hs => by simpa using e.symm.map_isCofinal hs, e.map_isCofinal⟩

@[deprecated (since := "2026-03-15")]
alias OrderIso.map_cofinal := OrderIso.map_isCofinal

Depends on / 依赖: e.map_isCofinal, e.symm.map_isCofinal, map_isCofinal
-/
theorem OrderIso.map_isCofinal_iff (e : α ≃o β) {s : Set α} : IsCofinal (e '' s) ↔ IsCofinal s :=
  ⟨fun hs => by simpa using e.symm.map_isCofinal hs, e.map_isCofinal⟩

@[deprecated (since := "2026-03-15")]
alias OrderIso.map_cofinal := OrderIso.map_isCofinal

/--
theorem `isCofinal_iff_iUnion_Iic_eq_univ` / 定理 `isCofinal_iff_iUnion_Iic_eq_univ`

English:
theorem isCofinal_iff_iUnion_Iic_eq_univ
  given: {s : Set α}
  proof: by
  simp [IsCofinal, eq_univ_iff_forall]

中文:
定理 isCofinal_iff_iUnion_Iic_eq_univ
  条件: {s : 集合 α}
  证明: by
  simp [IsCofinal, eq_univ_iff_forall]

Depends on / 依赖: IsCofinal, eq_univ_iff_forall
-/
theorem isCofinal_iff_iUnion_Iic_eq_univ {s : Set α} :
    IsCofinal s ↔ ⋃ i in s, Iic i = univ := by
  simp [IsCofinal, eq_univ_iff_forall]

/--
theorem `isCofinal_iff_iUnion_Iio_eq_univ` / 定理 `isCofinal_iff_iUnion_Iio_eq_univ`

English:
theorem isCofinal_iff_iUnion_Iio_eq_univ
  given: [NoMaxOrder α] {s : Set α}
  proof: by
    rw [isCofinal_iff_iUnion_Iic_eq_univ]; rw [← univ_subset_iff]; rw [← hs]
    gcongr
    exact Iio_subset_Iic_self
  mp hs := by
    simp_rw [eq_univ_iff_forall, mem_iUnion, exists_prop]
    intro x
    obtain ⟨y, hy⟩ := exists_gt x
    obtain ⟨z, hz, hz'⟩ := hs y
    exact ⟨z, hz, hy.trans_le hz'⟩

中文:
定理 isCofinal_iff_iUnion_Iio_eq_univ
  条件: [NoMax序 α] {s : 集合 α}
  证明: by
    rw [isCofinal_iff_iUnion_Iic_eq_univ]; rw [← univ_subset_iff]; rw [← hs]
    gcongr
    exact Iio_subset_Iic_self
  mp hs := by
    simp_rw [eq_univ_iff_forall, mem_iUnion, exists_prop]
    intro x
    obtain ⟨y, hy⟩ := exists_gt x
    obtain ⟨z, hz, hz'⟩ := hs y
    exact ⟨z, hz, hy.trans_le hz'⟩

Depends on / 依赖: Iio_subset_Iic_self, eq_univ_iff_forall, exists_gt, exists_prop, hy.trans_le, isCofinal_iff_iUnion_Iic_eq_univ, mem_iUnion, simp_rw, trans_le, univ_subset_iff
-/
theorem isCofinal_iff_iUnion_Iio_eq_univ [NoMaxOrder α] {s : Set α} :
    IsCofinal s ↔ ⋃ i in s, Iio i = univ where
  mpr hs := by
    rw [isCofinal_iff_iUnion_Iic_eq_univ]; rw [← univ_subset_iff]; rw [← hs]
    gcongr
    exact Iio_subset_Iic_self
  mp hs := by
    simp_rw [eq_univ_iff_forall, mem_iUnion, exists_prop]
    intro x
    obtain ⟨y, hy⟩ := exists_gt x
    obtain ⟨z, hz, hz'⟩ := hs y
    exact ⟨z, hz, hy.trans_le hz'⟩

end Preorder

section PartialOrder
variable [PartialOrder α]

/--
theorem `IsCofinal.mem_of_isMax` / 定理 `IsCofinal.mem_of_isMax`

English:
theorem IsCofinal.mem_of_isMax
  given: {s : Set α} {a : α} (ha : IsMax a) (hs : IsCofinal s)
  statement: a in s
  proof: by
  obtain ⟨b, hb, hb'⟩ := hs a
  rwa [ha.eq_of_ge hb'] at hb

中文:
定理 IsCofinal.mem_of_isMax
  条件: {s : 集合 α} {a : α} (ha : IsMax a) (hs : IsCofinal s)
  结论: a in s
  证明: by
  obtain ⟨b, hb, hb'⟩ := hs a
  rwa [ha.eq_of_ge hb'] at hb

Depends on / 依赖: eq_of_ge, f.map_add, ha.eq_of_ge, map_add
-/
theorem IsCofinal.mem_of_isMax {s : Set α} {a : α} (ha : IsMax a) (hs : IsCofinal s) : a in s := by
  obtain ⟨b, hb, hb'⟩ := hs a
  rwa [ha.eq_of_ge hb'] at hb

/--
theorem `IsCofinal.top_mem` / 定理 `IsCofinal.top_mem`

English:
theorem IsCofinal.top_mem
  given: [OrderTop α] {s : Set α} (hs : IsCofinal s)
  statement: ⊤ in s
  proof: hs.mem_of_isMax isMax_top

@[simp]

中文:
定理 IsCofinal.top_mem
  条件: [有顶序 α] {s : 集合 α} (hs : IsCofinal s)
  结论: ⊤ in s
  证明: hs.mem_of_isMax isMax_top

@[simp]

Depends on / 依赖: hs.mem_of_isMax, isMax_top, mem_of_isMax
-/
theorem IsCofinal.top_mem [OrderTop α] {s : Set α} (hs : IsCofinal s) : ⊤ in s :=
  hs.mem_of_isMax isMax_top

@[simp]
/--
theorem `isCofinal_iff_top_mem` / 定理 `isCofinal_iff_top_mem`

English:
theorem isCofinal_iff_top_mem
  given: [OrderTop α] {s : Set α}
  statement: IsCofinal s ↔ ⊤ in s
  proof: ⟨IsCofinal.top_mem, fun hs _ => ⟨⊤, hs, le_top⟩⟩

中文:
定理 isCofinal_iff_top_mem
  条件: [有顶序 α] {s : 集合 α}
  结论: IsCofinal s ↔ ⊤ in s
  证明: ⟨IsCofinal.top_mem, fun hs _ => ⟨⊤, hs, le_top⟩⟩

Depends on / 依赖: IsCofinal, IsCofinal.top_mem, le_top, top_mem
-/
theorem isCofinal_iff_top_mem [OrderTop α] {s : Set α} : IsCofinal s ↔ ⊤ in s :=
  ⟨IsCofinal.top_mem, fun hs _ => ⟨⊤, hs, le_top⟩⟩

end PartialOrder

section LinearOrder
variable [LinearOrder α]

/--
theorem `not_isCofinal_iff` / 定理 `not_isCofinal_iff`

English:
theorem not_isCofinal_iff
  given: {s : Set α}
  statement: ¬ IsCofinal s ↔ exists x, forall y in s, y < x
  proof: by
  simp [IsCofinal]

中文:
定理 not_isCofinal_iff
  条件: {s : 集合 α}
  结论: ¬ IsCofinal s ↔ 存在 x, 对任意 y in s, y < x
  证明: by
  simp [IsCofinal]

Depends on / 依赖: IsCofinal
-/
theorem not_isCofinal_iff {s : Set α} : ¬ IsCofinal s ↔ exists x, forall y in s, y < x := by
  simp [IsCofinal]

/--
theorem `BddAbove.of_not_isCofinal` / 定理 `BddAbove.of_not_isCofinal`

English:
theorem BddAbove.of_not_isCofinal
  given: {s : Set α} (h : ¬ IsCofinal s)
  statement: BddAbove s
  proof: by
  rw [not_isCofinal_iff] at h
  obtain ⟨x, h⟩ := h
  exact ⟨x, fun y hy => (h y hy).le⟩

中文:
定理 BddAbove.of_not_isCofinal
  条件: {s : 集合 α} (h : ¬ IsCofinal s)
  结论: BddAbove s
  证明: by
  rw [not_isCofinal_iff] at h
  obtain ⟨x, h⟩ := h
  exact ⟨x, fun y hy => (h y hy).le⟩

Depends on / 依赖: not_isCofinal_iff
-/
theorem BddAbove.of_not_isCofinal {s : Set α} (h : ¬ IsCofinal s) : BddAbove s := by
  rw [not_isCofinal_iff] at h
  obtain ⟨x, h⟩ := h
  exact ⟨x, fun y hy => (h y hy).le⟩

/--
theorem `IsCofinal.of_not_bddAbove` / 定理 `IsCofinal.of_not_bddAbove`

English:
theorem IsCofinal.of_not_bddAbove
  given: {s : Set α} (h : ¬ BddAbove s)
  statement: IsCofinal s
  proof: by
  contrapose h
  exact .of_not_isCofinal h

中文:
定理 IsCofinal.of_not_bddAbove
  条件: {s : 集合 α} (h : ¬ BddAbove s)
  结论: IsCofinal s
  证明: by
  contrapose h
  exact .of_not_isCofinal h

Depends on / 依赖: contrapose, of_not_isCofinal
-/
theorem IsCofinal.of_not_bddAbove {s : Set α} (h : ¬ BddAbove s) : IsCofinal s := by
  contrapose h
  exact .of_not_isCofinal h

/--
theorem `not_isCofinal_iff_bddAbove` / 定理 `not_isCofinal_iff_bddAbove`

English:
theorem not_isCofinal_iff_bddAbove
  given: [NoMaxOrder α] {s : Set α}
  statement: ¬ IsCofinal s ↔ BddAbove s
  proof: by
  use .of_not_isCofinal
  rw [not_isCofinal_iff]
  rintro ⟨x, h⟩
  obtain ⟨z, hz⟩ := exists_gt x
  exact ⟨z, fun y hy => (h hy).trans_lt hz⟩

中文:
定理 not_isCofinal_iff_bddAbove
  条件: [NoMax序 α] {s : 集合 α}
  结论: ¬ IsCofinal s ↔ BddAbove s
  证明: by
  use .of_not_isCofinal
  rw [not_isCofinal_iff]
  rintro ⟨x, h⟩
  obtain ⟨z, hz⟩ := exists_gt x
  exact ⟨z, fun y hy => (h hy).trans_lt hz⟩

Depends on / 依赖: exists_gt, not_isCofinal_iff, of_not_isCofinal, trans_lt
-/
theorem not_isCofinal_iff_bddAbove [NoMaxOrder α] {s : Set α} : ¬ IsCofinal s ↔ BddAbove s := by
  use .of_not_isCofinal
  rw [not_isCofinal_iff]
  rintro ⟨x, h⟩
  obtain ⟨z, hz⟩ := exists_gt x
  exact ⟨z, fun y hy => (h hy).trans_lt hz⟩

/--
theorem `not_bddAbove_iff_isCofinal` / 定理 `not_bddAbove_iff_isCofinal`

English:
theorem not_bddAbove_iff_isCofinal
  given: [NoMaxOrder α] {s : Set α}
  statement: ¬ BddAbove s ↔ IsCofinal s
  proof: not_iff_comm.1 not_isCofinal_iff_bddAbove

中文:
定理 not_bddAbove_iff_isCofinal
  条件: [NoMax序 α] {s : 集合 α}
  结论: ¬ BddAbove s ↔ IsCofinal s
  证明: not_iff_comm.1 not_isCofinal_iff_bddAbove

Depends on / 依赖: not_iff_comm, not_isCofinal_iff_bddAbove
-/
theorem not_bddAbove_iff_isCofinal [NoMaxOrder α] {s : Set α} : ¬ BddAbove s ↔ IsCofinal s :=
  not_iff_comm.1 not_isCofinal_iff_bddAbove

/--
theorem `isCofinal_setOfPred_imp_lt` / 定理 `isCofinal_setOfPred_imp_lt`

English:
theorem isCofinal_setOfPred_imp_lt
  given: (r : α -> α -> Prop) [h : IsWellFounded α r]
  proof: by
  intro a
  obtain ⟨b, hb, hb'⟩ := h.wf.has_min (Set.Ici a) Set.nonempty_Ici
  refine ⟨b, fun c hc => ?_, hb⟩
  by_contra! hc'
  exact hb' c (hb.trans hc') hc

@[deprecated (since := "2026-07-09")] alias isCofinal_setOf_imp_lt := isCofinal_setOfPred_imp_lt

中文:
定理 isCofinal_setOfPred_imp_lt
  条件: (r : α -> α -> 命题) [h : 是良基 α r]
  证明: by
  intro a
  obtain ⟨b, hb, hb'⟩ := h.wf.has_min (Set.Ici a) Set.nonempty_Ici
  refine ⟨b, fun c hc => ?_, hb⟩
  by_contra! hc'
  exact hb' c (hb.trans hc') hc

@[deprecated (since := "2026-07-09")] alias isCofinal_setOf_imp_lt := isCofinal_setOfPred_imp_lt

Depends on / 依赖: Set.Ici, Set.nonempty_Ici, h.wf.has_min, has_min, hb.trans, nonempty_Ici
-/
theorem isCofinal_setOfPred_imp_lt (r : α -> α -> Prop) [h : IsWellFounded α r] :
    IsCofinal { a | forall b, r b a -> b < a } := by
  intro a
  obtain ⟨b, hb, hb'⟩ := h.wf.has_min (Set.Ici a) Set.nonempty_Ici
  refine ⟨b, fun c hc => ?_, hb⟩
  by_contra! hc'
  exact hb' c (hb.trans hc') hc

@[deprecated (since := "2026-07-09")] alias isCofinal_setOf_imp_lt := isCofinal_setOfPred_imp_lt

/--
theorem `isCofinal_range_of_strictMono` / 定理 `isCofinal_range_of_strictMono`

English:
theorem isCofinal_range_of_strictMono
  given: [WellFoundedLT α] {f : α -> α} (hf : StrictMono f)
  proof: fun x => ⟨_, ⟨x, rfl⟩, hf.le_apply⟩

中文:
定理 isCofinal_range_of_strictMono
  条件: [WellFoundedLT α] {f : α -> α} (hf : 严格递增 f)
  证明: fun x => ⟨_, ⟨x, rfl⟩, hf.le_apply⟩

Depends on / 依赖: hf.le_apply, le_apply
-/
theorem isCofinal_range_of_strictMono [WellFoundedLT α] {f : α -> α} (hf : StrictMono f) :
    IsCofinal (range f) :=
  fun x => ⟨_, ⟨x, rfl⟩, hf.le_apply⟩

end LinearOrder
