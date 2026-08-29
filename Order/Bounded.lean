/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.RelClasses
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Bounds.Defs

/-!
# Bounded and unbounded sets

We prove miscellaneous lemmas about bounded and unbounded sets. Many of these are just variations on
the same ideas, or similar results with a few minor differences. The file is divided into these
different general ideas.
-/

deprecated_module "Use the following replacements:
- `BddAbove` for `Set.Bounded (· <= ·)`
- `BddBelow` for `Set.Bounded (· >= ·)`
- `IsCofinal` for `Set.Unbounded (· < ·)` in a linear order
- `IsCoinitial` for `Set.Unbounded (· > ·)` in a linear order" (since := "2026-04-16")

public section

assert_not_exists RelIso

namespace Set

variable {α : Type*} {r : α -> α -> Prop} {s t : Set α}



/--
theorem `Bounded.mono` / 定理 `Bounded.mono`

English:
theorem Bounded.mono
  given: (hst : s subseteq t) (hs : Bounded r t)
  statement: Bounded r s
  proof: hs.imp fun _ ha b hb => ha b (hst hb)

中文:
定理 有界.mono
  条件: (hst : s subseteq t) (hs : 有界 r t)
  结论: 有界 r s
  证明: hs.imp fun _ ha b hb => ha b (hst hb)

Depends on / 依赖: hs.imp
-/
theorem Bounded.mono (hst : s subseteq t) (hs : Bounded r t) : Bounded r s :=
  hs.imp fun _ ha b hb => ha b (hst hb)

/--
theorem `Unbounded.mono` / 定理 `Unbounded.mono`

English:
theorem Unbounded.mono
  given: (hst : s subseteq t) (hs : Unbounded r s)
  statement: Unbounded r t
  proof: fun a =>
  let ⟨b, hb, hb'⟩ := hs a
  ⟨b, hst hb, hb'⟩

中文:
定理 Unbounded.mono
  条件: (hst : s subseteq t) (hs : Unbounded r s)
  结论: Unbounded r t
  证明: fun a =>
  let ⟨b, hb, hb'⟩ := hs a
  ⟨b, hst hb, hb'⟩
-/
theorem Unbounded.mono (hst : s subseteq t) (hs : Unbounded r s) : Unbounded r t := fun a =>
  let ⟨b, hb, hb'⟩ := hs a
  ⟨b, hst hb, hb'⟩



/--
theorem `unbounded_le_of_forall_exists_lt` / 定理 `unbounded_le_of_forall_exists_lt`

English:
theorem unbounded_le_of_forall_exists_lt
  given: [Preorder α] (h : forall a, exists b in s, a < b)
  proof: fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => hba.not_gt hb'⟩

中文:
定理 unbounded_le_of_对任意_存在_lt
  条件: [预序 α] (h : 对任意 a, 存在 b in s, a < b)
  证明: fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => hba.not_gt hb'⟩
-/
theorem unbounded_le_of_forall_exists_lt [Preorder α] (h : forall a, exists b in s, a < b) :
    Unbounded (· <= ·) s := fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => hba.not_gt hb'⟩

/--
theorem `unbounded_le_iff` / 定理 `unbounded_le_iff`

English:
theorem unbounded_le_iff
  given: [LinearOrder α]
  statement: Unbounded (· <= ·) s ↔ forall a, exists b in s, a < b
  proof: by
  simp only [Unbounded, not_le]

中文:
定理 unbounded_le_iff
  条件: [线性序 α]
  结论: Unbounded (· <= ·) s ↔ 对任意 a, 存在 b in s, a < b
  证明: by
  simp only [Unbounded, not_le]

Depends on / 依赖: Unbounded, not_le
-/
theorem unbounded_le_iff [LinearOrder α] : Unbounded (· <= ·) s ↔ forall a, exists b in s, a < b := by
  simp only [Unbounded, not_le]

/--
theorem `unbounded_lt_of_forall_exists_le` / 定理 `unbounded_lt_of_forall_exists_le`

English:
theorem unbounded_lt_of_forall_exists_le
  given: [Preorder α] (h : forall a, exists b in s, a <= b)
  proof: fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => hba.not_ge hb'⟩

中文:
定理 unbounded_lt_of_对任意_存在_le
  条件: [预序 α] (h : 对任意 a, 存在 b in s, a <= b)
  证明: fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => hba.not_ge hb'⟩
-/
theorem unbounded_lt_of_forall_exists_le [Preorder α] (h : forall a, exists b in s, a <= b) :
    Unbounded (· < ·) s := fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => hba.not_ge hb'⟩

/--
theorem `unbounded_lt_iff` / 定理 `unbounded_lt_iff`

English:
theorem unbounded_lt_iff
  given: [LinearOrder α]
  statement: Unbounded (· < ·) s ↔ forall a, exists b in s, a <= b
  proof: by
  simp only [Unbounded, not_lt]

中文:
定理 unbounded_lt_iff
  条件: [线性序 α]
  结论: Unbounded (· < ·) s ↔ 对任意 a, 存在 b in s, a <= b
  证明: by
  simp only [Unbounded, not_lt]

Depends on / 依赖: Unbounded, not_lt
-/
theorem unbounded_lt_iff [LinearOrder α] : Unbounded (· < ·) s ↔ forall a, exists b in s, a <= b := by
  simp only [Unbounded, not_lt]

/--
theorem `unbounded_ge_of_forall_exists_gt` / 定理 `unbounded_ge_of_forall_exists_gt`

English:
theorem unbounded_ge_of_forall_exists_gt
  given: [Preorder α] (h : forall a, exists b in s, b < a)
  proof: @unbounded_le_of_forall_exists_lt αᵒᵈ _ _ h

中文:
定理 unbounded_ge_of_对任意_存在_gt
  条件: [预序 α] (h : 对任意 a, 存在 b in s, b < a)
  证明: @unbounded_le_of_forall_exists_lt αᵒᵈ _ _ h

Depends on / 依赖: unbounded_le_of_forall_exists_lt
-/
theorem unbounded_ge_of_forall_exists_gt [Preorder α] (h : forall a, exists b in s, b < a) :
    Unbounded (· >= ·) s :=
  @unbounded_le_of_forall_exists_lt αᵒᵈ _ _ h

/--
theorem `unbounded_ge_iff` / 定理 `unbounded_ge_iff`

English:
theorem unbounded_ge_iff
  given: [LinearOrder α]
  statement: Unbounded (· >= ·) s ↔ forall a, exists b in s, b < a
  proof: ⟨fun h a =>
    let ⟨b, hb, hba⟩ := h a
    ⟨b, hb, lt_of_not_ge hba⟩,
    unbounded_ge_of_forall_exists_gt⟩

中文:
定理 unbounded_ge_iff
  条件: [线性序 α]
  结论: Unbounded (· >= ·) s ↔ 对任意 a, 存在 b in s, b < a
  证明: ⟨fun h a =>
    let ⟨b, hb, hba⟩ := h a
    ⟨b, hb, lt_of_not_ge hba⟩,
    unbounded_ge_of_forall_exists_gt⟩

Depends on / 依赖: lt_of_not_ge, unbounded_ge_of_forall_exists_gt
-/
theorem unbounded_ge_iff [LinearOrder α] : Unbounded (· >= ·) s ↔ forall a, exists b in s, b < a :=
  ⟨fun h a =>
    let ⟨b, hb, hba⟩ := h a
    ⟨b, hb, lt_of_not_ge hba⟩,
    unbounded_ge_of_forall_exists_gt⟩

/--
theorem `unbounded_gt_of_forall_exists_ge` / 定理 `unbounded_gt_of_forall_exists_ge`

English:
theorem unbounded_gt_of_forall_exists_ge
  given: [Preorder α] (h : forall a, exists b in s, b <= a)
  proof: fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => not_le_of_gt hba hb'⟩

中文:
定理 unbounded_gt_of_对任意_存在_ge
  条件: [预序 α] (h : 对任意 a, 存在 b in s, b <= a)
  证明: fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => not_le_of_gt hba hb'⟩
-/
theorem unbounded_gt_of_forall_exists_ge [Preorder α] (h : forall a, exists b in s, b <= a) :
    Unbounded (· > ·) s := fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => not_le_of_gt hba hb'⟩

/--
theorem `unbounded_gt_iff` / 定理 `unbounded_gt_iff`

English:
theorem unbounded_gt_iff
  given: [LinearOrder α]
  statement: Unbounded (· > ·) s ↔ forall a, exists b in s, b <= a
  proof: ⟨fun h a =>
    let ⟨b, hb, hba⟩ := h a
    ⟨b, hb, le_of_not_gt hba⟩,
    unbounded_gt_of_forall_exists_ge⟩

中文:
定理 unbounded_gt_iff
  条件: [线性序 α]
  结论: Unbounded (· > ·) s ↔ 对任意 a, 存在 b in s, b <= a
  证明: ⟨fun h a =>
    let ⟨b, hb, hba⟩ := h a
    ⟨b, hb, le_of_not_gt hba⟩,
    unbounded_gt_of_forall_exists_ge⟩

Depends on / 依赖: le_of_not_gt, unbounded_gt_of_forall_exists_ge
-/
theorem unbounded_gt_iff [LinearOrder α] : Unbounded (· > ·) s ↔ forall a, exists b in s, b <= a :=
  ⟨fun h a =>
    let ⟨b, hb, hba⟩ := h a
    ⟨b, hb, le_of_not_gt hba⟩,
    unbounded_gt_of_forall_exists_ge⟩

/-! ### Relation between boundedness by strict and nonstrict orders. -/




/--
theorem `Bounded.rel_mono` / 定理 `Bounded.rel_mono`

English:
theorem Bounded.rel_mono
  given: {r' : α -> α -> Prop} (h : Bounded r s) (hrr' : r <= r')
  statement: Bounded r' s
  proof: let ⟨a, ha⟩ := h
  ⟨a, fun b hb => hrr' b a (ha b hb)⟩

中文:
定理 有界.rel_mono
  条件: {r' : α -> α -> 命题} (h : 有界 r s) (hrr' : r <= r')
  结论: 有界 r' s
  证明: let ⟨a, ha⟩ := h
  ⟨a, fun b hb => hrr' b a (ha b hb)⟩
-/
theorem Bounded.rel_mono {r' : α -> α -> Prop} (h : Bounded r s) (hrr' : r <= r') : Bounded r' s :=
  let ⟨a, ha⟩ := h
  ⟨a, fun b hb => hrr' b a (ha b hb)⟩

/--
theorem `bounded_le_of_bounded_lt` / 定理 `bounded_le_of_bounded_lt`

English:
theorem bounded_le_of_bounded_lt
  given: [Preorder α] (h : Bounded (· < ·) s)
  statement: Bounded (· <= ·) s
  proof: h.rel_mono fun _ _ => le_of_lt

中文:
定理 bounded_le_of_bounded_lt
  条件: [预序 α] (h : 有界 (· < ·) s)
  结论: 有界 (· <= ·) s
  证明: h.rel_mono fun _ _ => le_of_lt

Depends on / 依赖: h.rel_mono, le_of_lt, rel_mono
-/
theorem bounded_le_of_bounded_lt [Preorder α] (h : Bounded (· < ·) s) : Bounded (· <= ·) s :=
  h.rel_mono fun _ _ => le_of_lt

/--
theorem `Unbounded.rel_mono` / 定理 `Unbounded.rel_mono`

English:
theorem Unbounded.rel_mono
  given: {r' : α -> α -> Prop} (hr : r' <= r) (h : Unbounded r s)
  statement: Unbounded r' s
  proof: fun a =>
  let ⟨b, hb, hba⟩ := h a
  ⟨b, hb, fun hba' => hba (hr b a hba')⟩

中文:
定理 Unbounded.rel_mono
  条件: {r' : α -> α -> 命题} (hr : r' <= r) (h : Unbounded r s)
  结论: Unbounded r' s
  证明: fun a =>
  let ⟨b, hb, hba⟩ := h a
  ⟨b, hb, fun hba' => hba (hr b a hba')⟩
-/
theorem Unbounded.rel_mono {r' : α -> α -> Prop} (hr : r' <= r) (h : Unbounded r s) : Unbounded r' s :=
  fun a =>
  let ⟨b, hb, hba⟩ := h a
  ⟨b, hb, fun hba' => hba (hr b a hba')⟩

/--
theorem `unbounded_lt_of_unbounded_le` / 定理 `unbounded_lt_of_unbounded_le`

English:
theorem unbounded_lt_of_unbounded_le
  given: [Preorder α] (h : Unbounded (· <= ·) s)
  statement: Unbounded (· < ·) s
  proof: h.rel_mono fun _ _ => le_of_lt

中文:
定理 unbounded_lt_of_unbounded_le
  条件: [预序 α] (h : Unbounded (· <= ·) s)
  结论: Unbounded (· < ·) s
  证明: h.rel_mono fun _ _ => le_of_lt

Depends on / 依赖: h.rel_mono, le_of_lt, rel_mono
-/
theorem unbounded_lt_of_unbounded_le [Preorder α] (h : Unbounded (· <= ·) s) : Unbounded (· < ·) s :=
  h.rel_mono fun _ _ => le_of_lt

/--
theorem `bounded_le_iff_bounded_lt` / 定理 `bounded_le_iff_bounded_lt`

English:
theorem bounded_le_iff_bounded_lt
  given: [Preorder α] [NoMaxOrder α]
  proof: by
  refine ⟨fun h => ?_, bounded_le_of_bounded_lt⟩
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := exists_gt a
  exact ⟨b, fun c hc => lt_of_le_of_lt (ha c hc) hb⟩

中文:
定理 bounded_le_iff_bounded_lt
  条件: [预序 α] [NoMax序 α]
  证明: by
  refine ⟨fun h => ?_, bounded_le_of_bounded_lt⟩
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := exists_gt a
  exact ⟨b, fun c hc => lt_of_le_of_lt (ha c hc) hb⟩

Depends on / 依赖: bounded_le_of_bounded_lt, exists_gt, lt_of_le_of_lt
-/
theorem bounded_le_iff_bounded_lt [Preorder α] [NoMaxOrder α] :
    Bounded (· <= ·) s ↔ Bounded (· < ·) s := by
  refine ⟨fun h => ?_, bounded_le_of_bounded_lt⟩
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := exists_gt a
  exact ⟨b, fun c hc => lt_of_le_of_lt (ha c hc) hb⟩

/--
theorem `unbounded_lt_iff_unbounded_le` / 定理 `unbounded_lt_iff_unbounded_le`

English:
theorem unbounded_lt_iff_unbounded_le
  given: [Preorder α] [NoMaxOrder α]
  proof: by
  simp_rw [← not_bounded_iff, bounded_le_iff_bounded_lt]

中文:
定理 unbounded_lt_iff_unbounded_le
  条件: [预序 α] [NoMax序 α]
  证明: by
  simp_rw [← not_bounded_iff, bounded_le_iff_bounded_lt]

Depends on / 依赖: bounded_le_iff_bounded_lt, not_bounded_iff, simp_rw
-/
theorem unbounded_lt_iff_unbounded_le [Preorder α] [NoMaxOrder α] :
    Unbounded (· < ·) s ↔ Unbounded (· <= ·) s := by
  simp_rw [← not_bounded_iff, bounded_le_iff_bounded_lt]



/--
theorem `bounded_ge_of_bounded_gt` / 定理 `bounded_ge_of_bounded_gt`

English:
theorem bounded_ge_of_bounded_gt
  given: [Preorder α] (h : Bounded (· > ·) s)
  statement: Bounded (· >= ·) s
  proof: let ⟨a, ha⟩ := h
  ⟨a, fun b hb => le_of_lt (ha b hb)⟩

中文:
定理 bounded_ge_of_bounded_gt
  条件: [预序 α] (h : 有界 (· > ·) s)
  结论: 有界 (· >= ·) s
  证明: let ⟨a, ha⟩ := h
  ⟨a, fun b hb => le_of_lt (ha b hb)⟩

Depends on / 依赖: le_of_lt
-/
theorem bounded_ge_of_bounded_gt [Preorder α] (h : Bounded (· > ·) s) : Bounded (· >= ·) s :=
  let ⟨a, ha⟩ := h
  ⟨a, fun b hb => le_of_lt (ha b hb)⟩

/--
theorem `unbounded_gt_of_unbounded_ge` / 定理 `unbounded_gt_of_unbounded_ge`

English:
theorem unbounded_gt_of_unbounded_ge
  given: [Preorder α] (h : Unbounded (· >= ·) s)
  statement: Unbounded (· > ·) s
  proof: fun a =>
  let ⟨b, hb, hba⟩ := h a
  ⟨b, hb, fun hba' => hba (le_of_lt hba')⟩

中文:
定理 unbounded_gt_of_unbounded_ge
  条件: [预序 α] (h : Unbounded (· >= ·) s)
  结论: Unbounded (· > ·) s
  证明: fun a =>
  let ⟨b, hb, hba⟩ := h a
  ⟨b, hb, fun hba' => hba (le_of_lt hba')⟩

Depends on / 依赖: le_of_lt
-/
theorem unbounded_gt_of_unbounded_ge [Preorder α] (h : Unbounded (· >= ·) s) : Unbounded (· > ·) s :=
  fun a =>
  let ⟨b, hb, hba⟩ := h a
  ⟨b, hb, fun hba' => hba (le_of_lt hba')⟩

/--
theorem `bounded_ge_iff_bounded_gt` / 定理 `bounded_ge_iff_bounded_gt`

English:
theorem bounded_ge_iff_bounded_gt
  given: [Preorder α] [NoMinOrder α]
  proof: @bounded_le_iff_bounded_lt αᵒᵈ _ _ _

中文:
定理 bounded_ge_iff_bounded_gt
  条件: [预序 α] [NoMin序 α]
  证明: @bounded_le_iff_bounded_lt αᵒᵈ _ _ _

Depends on / 依赖: bounded_le_iff_bounded_lt
-/
theorem bounded_ge_iff_bounded_gt [Preorder α] [NoMinOrder α] :
    Bounded (· >= ·) s ↔ Bounded (· > ·) s :=
  @bounded_le_iff_bounded_lt αᵒᵈ _ _ _

/--
theorem `unbounded_gt_iff_unbounded_ge` / 定理 `unbounded_gt_iff_unbounded_ge`

English:
theorem unbounded_gt_iff_unbounded_ge
  given: [Preorder α] [NoMinOrder α]
  proof: @unbounded_lt_iff_unbounded_le αᵒᵈ _ _ _

中文:
定理 unbounded_gt_iff_unbounded_ge
  条件: [预序 α] [NoMin序 α]
  证明: @unbounded_lt_iff_unbounded_le αᵒᵈ _ _ _

Depends on / 依赖: unbounded_lt_iff_unbounded_le
-/
theorem unbounded_gt_iff_unbounded_ge [Preorder α] [NoMinOrder α] :
    Unbounded (· > ·) s ↔ Unbounded (· >= ·) s :=
  @unbounded_lt_iff_unbounded_le αᵒᵈ _ _ _



/--
theorem `unbounded_le_univ` / 定理 `unbounded_le_univ`

English:
theorem unbounded_le_univ
  given: [LE α] [NoTopOrder α]
  statement: Unbounded (· <= ·) (@Set.univ α)
  proof: fun a =>
  let ⟨b, hb⟩ := exists_not_le a
  ⟨b, ⟨⟩, hb⟩

中文:
定理 unbounded_le_univ
  条件: [LE α] [无顶序 α]
  结论: Unbounded (· <= ·) (@集合.univ α)
  证明: fun a =>
  let ⟨b, hb⟩ := exists_not_le a
  ⟨b, ⟨⟩, hb⟩
-/
theorem unbounded_le_univ [LE α] [NoTopOrder α] : Unbounded (· <= ·) (@Set.univ α) := fun a =>
  let ⟨b, hb⟩ := exists_not_le a
  ⟨b, ⟨⟩, hb⟩

/--
theorem `unbounded_lt_univ` / 定理 `unbounded_lt_univ`

English:
theorem unbounded_lt_univ
  given: [Preorder α] [NoTopOrder α]
  statement: Unbounded (· < ·) (@Set.univ α)
  proof: unbounded_lt_of_unbounded_le unbounded_le_univ

中文:
定理 unbounded_lt_univ
  条件: [预序 α] [无顶序 α]
  结论: Unbounded (· < ·) (@集合.univ α)
  证明: unbounded_lt_of_unbounded_le unbounded_le_univ

Depends on / 依赖: unbounded_le_univ, unbounded_lt_of_unbounded_le
-/
theorem unbounded_lt_univ [Preorder α] [NoTopOrder α] : Unbounded (· < ·) (@Set.univ α) :=
  unbounded_lt_of_unbounded_le unbounded_le_univ

/--
theorem `unbounded_ge_univ` / 定理 `unbounded_ge_univ`

English:
theorem unbounded_ge_univ
  given: [LE α] [NoBotOrder α]
  statement: Unbounded (· >= ·) (@Set.univ α)
  proof: fun a =>
  let ⟨b, hb⟩ := exists_not_ge a
  ⟨b, ⟨⟩, hb⟩

中文:
定理 unbounded_ge_univ
  条件: [LE α] [无底序 α]
  结论: Unbounded (· >= ·) (@集合.univ α)
  证明: fun a =>
  let ⟨b, hb⟩ := exists_not_ge a
  ⟨b, ⟨⟩, hb⟩
-/
theorem unbounded_ge_univ [LE α] [NoBotOrder α] : Unbounded (· >= ·) (@Set.univ α) := fun a =>
  let ⟨b, hb⟩ := exists_not_ge a
  ⟨b, ⟨⟩, hb⟩

/--
theorem `unbounded_gt_univ` / 定理 `unbounded_gt_univ`

English:
theorem unbounded_gt_univ
  given: [Preorder α] [NoBotOrder α]
  statement: Unbounded (· > ·) (@Set.univ α)
  proof: unbounded_gt_of_unbounded_ge unbounded_ge_univ

中文:
定理 unbounded_gt_univ
  条件: [预序 α] [无底序 α]
  结论: Unbounded (· > ·) (@集合.univ α)
  证明: unbounded_gt_of_unbounded_ge unbounded_ge_univ

Depends on / 依赖: unbounded_ge_univ, unbounded_gt_of_unbounded_ge
-/
theorem unbounded_gt_univ [Preorder α] [NoBotOrder α] : Unbounded (· > ·) (@Set.univ α) :=
  unbounded_gt_of_unbounded_ge unbounded_ge_univ



/--
theorem `bounded_self` / 定理 `bounded_self`

English:
theorem bounded_self
  given: (a : α)
  statement: Bounded r { b | r b a }
  proof: ⟨a, fun _ => id⟩

中文:
定理 bounded_self
  条件: (a : α)
  结论: 有界 r { b | r b a }
  证明: ⟨a, fun _ => id⟩
-/
theorem bounded_self (a : α) : Bounded r { b | r b a } :=
  ⟨a, fun _ => id⟩



/--
theorem `bounded_lt_Iio` / 定理 `bounded_lt_Iio`

English:
theorem bounded_lt_Iio
  given: [Preorder α] (a : α)
  statement: Bounded (· < ·) (Iio a)
  proof: bounded_self a

中文:
定理 bounded_lt_Iio
  条件: [预序 α] (a : α)
  结论: 有界 (· < ·) (左无界右开区间 a)
  证明: bounded_self a

Depends on / 依赖: bounded_self
-/
theorem bounded_lt_Iio [Preorder α] (a : α) : Bounded (· < ·) (Iio a) :=
  bounded_self a

/--
theorem `bounded_le_Iio` / 定理 `bounded_le_Iio`

English:
theorem bounded_le_Iio
  given: [Preorder α] (a : α)
  statement: Bounded (· <= ·) (Iio a)
  proof: bounded_le_of_bounded_lt (bounded_lt_Iio a)

中文:
定理 bounded_le_Iio
  条件: [预序 α] (a : α)
  结论: 有界 (· <= ·) (左无界右开区间 a)
  证明: bounded_le_of_bounded_lt (bounded_lt_Iio a)

Depends on / 依赖: bounded_le_of_bounded_lt, bounded_lt_Iio
-/
theorem bounded_le_Iio [Preorder α] (a : α) : Bounded (· <= ·) (Iio a) :=
  bounded_le_of_bounded_lt (bounded_lt_Iio a)

/--
theorem `bounded_le_Iic` / 定理 `bounded_le_Iic`

English:
theorem bounded_le_Iic
  given: [Preorder α] (a : α)
  statement: Bounded (· <= ·) (Iic a)
  proof: bounded_self a

中文:
定理 bounded_le_Iic
  条件: [预序 α] (a : α)
  结论: 有界 (· <= ·) (左无界右闭区间 a)
  证明: bounded_self a

Depends on / 依赖: bounded_self
-/
theorem bounded_le_Iic [Preorder α] (a : α) : Bounded (· <= ·) (Iic a) :=
  bounded_self a

/--
theorem `bounded_lt_Iic` / 定理 `bounded_lt_Iic`

English:
theorem bounded_lt_Iic
  given: [Preorder α] [NoMaxOrder α] (a : α)
  statement: Bounded (· < ·) (Iic a)
  proof: by
  simp only [← bounded_le_iff_bounded_lt, bounded_le_Iic]

中文:
定理 bounded_lt_Iic
  条件: [预序 α] [NoMax序 α] (a : α)
  结论: 有界 (· < ·) (左无界右闭区间 a)
  证明: by
  simp only [← bounded_le_iff_bounded_lt, bounded_le_Iic]

Depends on / 依赖: bounded_le_Iic, bounded_le_iff_bounded_lt
-/
theorem bounded_lt_Iic [Preorder α] [NoMaxOrder α] (a : α) : Bounded (· < ·) (Iic a) := by
  simp only [← bounded_le_iff_bounded_lt, bounded_le_Iic]

/--
theorem `bounded_gt_Ioi` / 定理 `bounded_gt_Ioi`

English:
theorem bounded_gt_Ioi
  given: [Preorder α] (a : α)
  statement: Bounded (· > ·) (Ioi a)
  proof: bounded_self a

中文:
定理 bounded_gt_Ioi
  条件: [预序 α] (a : α)
  结论: 有界 (· > ·) (左开右无界区间 a)
  证明: bounded_self a

Depends on / 依赖: bounded_self
-/
theorem bounded_gt_Ioi [Preorder α] (a : α) : Bounded (· > ·) (Ioi a) :=
  bounded_self a

/--
theorem `bounded_ge_Ioi` / 定理 `bounded_ge_Ioi`

English:
theorem bounded_ge_Ioi
  given: [Preorder α] (a : α)
  statement: Bounded (· >= ·) (Ioi a)
  proof: bounded_ge_of_bounded_gt (bounded_gt_Ioi a)

中文:
定理 bounded_ge_Ioi
  条件: [预序 α] (a : α)
  结论: 有界 (· >= ·) (左开右无界区间 a)
  证明: bounded_ge_of_bounded_gt (bounded_gt_Ioi a)

Depends on / 依赖: bounded_ge_of_bounded_gt, bounded_gt_Ioi
-/
theorem bounded_ge_Ioi [Preorder α] (a : α) : Bounded (· >= ·) (Ioi a) :=
  bounded_ge_of_bounded_gt (bounded_gt_Ioi a)

/--
theorem `bounded_ge_Ici` / 定理 `bounded_ge_Ici`

English:
theorem bounded_ge_Ici
  given: [Preorder α] (a : α)
  statement: Bounded (· >= ·) (Ici a)
  proof: bounded_self a

中文:
定理 bounded_ge_Ici
  条件: [预序 α] (a : α)
  结论: 有界 (· >= ·) (左闭右无界区间 a)
  证明: bounded_self a

Depends on / 依赖: bounded_self
-/
theorem bounded_ge_Ici [Preorder α] (a : α) : Bounded (· >= ·) (Ici a) :=
  bounded_self a

/--
theorem `bounded_gt_Ici` / 定理 `bounded_gt_Ici`

English:
theorem bounded_gt_Ici
  given: [Preorder α] [NoMinOrder α] (a : α)
  statement: Bounded (· > ·) (Ici a)
  proof: by
  simp only [← bounded_ge_iff_bounded_gt, bounded_ge_Ici]

中文:
定理 bounded_gt_Ici
  条件: [预序 α] [NoMin序 α] (a : α)
  结论: 有界 (· > ·) (左闭右无界区间 a)
  证明: by
  simp only [← bounded_ge_iff_bounded_gt, bounded_ge_Ici]

Depends on / 依赖: bounded_ge_Ici, bounded_ge_iff_bounded_gt
-/
theorem bounded_gt_Ici [Preorder α] [NoMinOrder α] (a : α) : Bounded (· > ·) (Ici a) := by
  simp only [← bounded_ge_iff_bounded_gt, bounded_ge_Ici]



/--
theorem `bounded_lt_Ioo` / 定理 `bounded_lt_Ioo`

English:
theorem bounded_lt_Ioo
  given: [Preorder α] (a b : α)
  statement: Bounded (· < ·) (Ioo a b)
  proof: (bounded_lt_Iio b).mono Set.Ioo_subset_Iio_self

中文:
定理 bounded_lt_Ioo
  条件: [预序 α] (a b : α)
  结论: 有界 (· < ·) (开区间 a b)
  证明: (bounded_lt_Iio b).mono Set.Ioo_subset_Iio_self

Depends on / 依赖: Ioo_subset_Iio_self, Set.Ioo_subset_Iio_self, bounded_lt_Iio
-/
theorem bounded_lt_Ioo [Preorder α] (a b : α) : Bounded (· < ·) (Ioo a b) :=
  (bounded_lt_Iio b).mono Set.Ioo_subset_Iio_self

/--
theorem `bounded_lt_Ico` / 定理 `bounded_lt_Ico`

English:
theorem bounded_lt_Ico
  given: [Preorder α] (a b : α)
  statement: Bounded (· < ·) (Ico a b)
  proof: (bounded_lt_Iio b).mono Set.Ico_subset_Iio_self

中文:
定理 bounded_lt_Ico
  条件: [预序 α] (a b : α)
  结论: 有界 (· < ·) (左闭右开区间 a b)
  证明: (bounded_lt_Iio b).mono Set.Ico_subset_Iio_self

Depends on / 依赖: Ico_subset_Iio_self, Set.Ico_subset_Iio_self, bounded_lt_Iio
-/
theorem bounded_lt_Ico [Preorder α] (a b : α) : Bounded (· < ·) (Ico a b) :=
  (bounded_lt_Iio b).mono Set.Ico_subset_Iio_self

/--
theorem `bounded_lt_Ioc` / 定理 `bounded_lt_Ioc`

English:
theorem bounded_lt_Ioc
  given: [Preorder α] [NoMaxOrder α] (a b : α)
  statement: Bounded (· < ·) (Ioc a b)
  proof: (bounded_lt_Iic b).mono Set.Ioc_subset_Iic_self

中文:
定理 bounded_lt_Ioc
  条件: [预序 α] [NoMax序 α] (a b : α)
  结论: 有界 (· < ·) (左开右闭区间 a b)
  证明: (bounded_lt_Iic b).mono Set.Ioc_subset_Iic_self

Depends on / 依赖: Ioc_subset_Iic_self, Set.Ioc_subset_Iic_self, bounded_lt_Iic
-/
theorem bounded_lt_Ioc [Preorder α] [NoMaxOrder α] (a b : α) : Bounded (· < ·) (Ioc a b) :=
  (bounded_lt_Iic b).mono Set.Ioc_subset_Iic_self

/--
theorem `bounded_lt_Icc` / 定理 `bounded_lt_Icc`

English:
theorem bounded_lt_Icc
  given: [Preorder α] [NoMaxOrder α] (a b : α)
  statement: Bounded (· < ·) (Icc a b)
  proof: (bounded_lt_Iic b).mono Set.Icc_subset_Iic_self

中文:
定理 bounded_lt_Icc
  条件: [预序 α] [NoMax序 α] (a b : α)
  结论: 有界 (· < ·) (闭区间 a b)
  证明: (bounded_lt_Iic b).mono Set.Icc_subset_Iic_self

Depends on / 依赖: Icc_subset_Iic_self, Set.Icc_subset_Iic_self, bounded_lt_Iic
-/
theorem bounded_lt_Icc [Preorder α] [NoMaxOrder α] (a b : α) : Bounded (· < ·) (Icc a b) :=
  (bounded_lt_Iic b).mono Set.Icc_subset_Iic_self

/--
theorem `bounded_le_Ioo` / 定理 `bounded_le_Ioo`

English:
theorem bounded_le_Ioo
  given: [Preorder α] (a b : α)
  statement: Bounded (· <= ·) (Ioo a b)
  proof: (bounded_le_Iio b).mono Set.Ioo_subset_Iio_self

中文:
定理 bounded_le_Ioo
  条件: [预序 α] (a b : α)
  结论: 有界 (· <= ·) (开区间 a b)
  证明: (bounded_le_Iio b).mono Set.Ioo_subset_Iio_self

Depends on / 依赖: Ioo_subset_Iio_self, Set.Ioo_subset_Iio_self, bounded_le_Iio
-/
theorem bounded_le_Ioo [Preorder α] (a b : α) : Bounded (· <= ·) (Ioo a b) :=
  (bounded_le_Iio b).mono Set.Ioo_subset_Iio_self

/--
theorem `bounded_le_Ico` / 定理 `bounded_le_Ico`

English:
theorem bounded_le_Ico
  given: [Preorder α] (a b : α)
  statement: Bounded (· <= ·) (Ico a b)
  proof: (bounded_le_Iio b).mono Set.Ico_subset_Iio_self

中文:
定理 bounded_le_Ico
  条件: [预序 α] (a b : α)
  结论: 有界 (· <= ·) (左闭右开区间 a b)
  证明: (bounded_le_Iio b).mono Set.Ico_subset_Iio_self

Depends on / 依赖: Ico_subset_Iio_self, Set.Ico_subset_Iio_self, bounded_le_Iio
-/
theorem bounded_le_Ico [Preorder α] (a b : α) : Bounded (· <= ·) (Ico a b) :=
  (bounded_le_Iio b).mono Set.Ico_subset_Iio_self

/--
theorem `bounded_le_Ioc` / 定理 `bounded_le_Ioc`

English:
theorem bounded_le_Ioc
  given: [Preorder α] (a b : α)
  statement: Bounded (· <= ·) (Ioc a b)
  proof: (bounded_le_Iic b).mono Set.Ioc_subset_Iic_self

中文:
定理 bounded_le_Ioc
  条件: [预序 α] (a b : α)
  结论: 有界 (· <= ·) (左开右闭区间 a b)
  证明: (bounded_le_Iic b).mono Set.Ioc_subset_Iic_self

Depends on / 依赖: Ioc_subset_Iic_self, Set.Ioc_subset_Iic_self, bounded_le_Iic
-/
theorem bounded_le_Ioc [Preorder α] (a b : α) : Bounded (· <= ·) (Ioc a b) :=
  (bounded_le_Iic b).mono Set.Ioc_subset_Iic_self

/--
theorem `bounded_le_Icc` / 定理 `bounded_le_Icc`

English:
theorem bounded_le_Icc
  given: [Preorder α] (a b : α)
  statement: Bounded (· <= ·) (Icc a b)
  proof: (bounded_le_Iic b).mono Set.Icc_subset_Iic_self

中文:
定理 bounded_le_Icc
  条件: [预序 α] (a b : α)
  结论: 有界 (· <= ·) (闭区间 a b)
  证明: (bounded_le_Iic b).mono Set.Icc_subset_Iic_self

Depends on / 依赖: Icc_subset_Iic_self, Set.Icc_subset_Iic_self, bounded_le_Iic
-/
theorem bounded_le_Icc [Preorder α] (a b : α) : Bounded (· <= ·) (Icc a b) :=
  (bounded_le_Iic b).mono Set.Icc_subset_Iic_self

/--
theorem `bounded_gt_Ioo` / 定理 `bounded_gt_Ioo`

English:
theorem bounded_gt_Ioo
  given: [Preorder α] (a b : α)
  statement: Bounded (· > ·) (Ioo a b)
  proof: (bounded_gt_Ioi a).mono Set.Ioo_subset_Ioi_self

中文:
定理 bounded_gt_Ioo
  条件: [预序 α] (a b : α)
  结论: 有界 (· > ·) (开区间 a b)
  证明: (bounded_gt_Ioi a).mono Set.Ioo_subset_Ioi_self

Depends on / 依赖: Ioo_subset_Ioi_self, Set.Ioo_subset_Ioi_self, bounded_gt_Ioi
-/
theorem bounded_gt_Ioo [Preorder α] (a b : α) : Bounded (· > ·) (Ioo a b) :=
  (bounded_gt_Ioi a).mono Set.Ioo_subset_Ioi_self

/--
theorem `bounded_gt_Ioc` / 定理 `bounded_gt_Ioc`

English:
theorem bounded_gt_Ioc
  given: [Preorder α] (a b : α)
  statement: Bounded (· > ·) (Ioc a b)
  proof: (bounded_gt_Ioi a).mono Set.Ioc_subset_Ioi_self

中文:
定理 bounded_gt_Ioc
  条件: [预序 α] (a b : α)
  结论: 有界 (· > ·) (左开右闭区间 a b)
  证明: (bounded_gt_Ioi a).mono Set.Ioc_subset_Ioi_self

Depends on / 依赖: Ioc_subset_Ioi_self, Set.Ioc_subset_Ioi_self, bounded_gt_Ioi
-/
theorem bounded_gt_Ioc [Preorder α] (a b : α) : Bounded (· > ·) (Ioc a b) :=
  (bounded_gt_Ioi a).mono Set.Ioc_subset_Ioi_self

/--
theorem `bounded_gt_Ico` / 定理 `bounded_gt_Ico`

English:
theorem bounded_gt_Ico
  given: [Preorder α] [NoMinOrder α] (a b : α)
  statement: Bounded (· > ·) (Ico a b)
  proof: (bounded_gt_Ici a).mono Set.Ico_subset_Ici_self

中文:
定理 bounded_gt_Ico
  条件: [预序 α] [NoMin序 α] (a b : α)
  结论: 有界 (· > ·) (左闭右开区间 a b)
  证明: (bounded_gt_Ici a).mono Set.Ico_subset_Ici_self

Depends on / 依赖: Ico_subset_Ici_self, Set.Ico_subset_Ici_self, bounded_gt_Ici
-/
theorem bounded_gt_Ico [Preorder α] [NoMinOrder α] (a b : α) : Bounded (· > ·) (Ico a b) :=
  (bounded_gt_Ici a).mono Set.Ico_subset_Ici_self

/--
theorem `bounded_gt_Icc` / 定理 `bounded_gt_Icc`

English:
theorem bounded_gt_Icc
  given: [Preorder α] [NoMinOrder α] (a b : α)
  statement: Bounded (· > ·) (Icc a b)
  proof: (bounded_gt_Ici a).mono Set.Icc_subset_Ici_self

中文:
定理 bounded_gt_Icc
  条件: [预序 α] [NoMin序 α] (a b : α)
  结论: 有界 (· > ·) (闭区间 a b)
  证明: (bounded_gt_Ici a).mono Set.Icc_subset_Ici_self

Depends on / 依赖: Icc_subset_Ici_self, Set.Icc_subset_Ici_self, bounded_gt_Ici
-/
theorem bounded_gt_Icc [Preorder α] [NoMinOrder α] (a b : α) : Bounded (· > ·) (Icc a b) :=
  (bounded_gt_Ici a).mono Set.Icc_subset_Ici_self

/--
theorem `bounded_ge_Ioo` / 定理 `bounded_ge_Ioo`

English:
theorem bounded_ge_Ioo
  given: [Preorder α] (a b : α)
  statement: Bounded (· >= ·) (Ioo a b)
  proof: (bounded_ge_Ioi a).mono Set.Ioo_subset_Ioi_self

中文:
定理 bounded_ge_Ioo
  条件: [预序 α] (a b : α)
  结论: 有界 (· >= ·) (开区间 a b)
  证明: (bounded_ge_Ioi a).mono Set.Ioo_subset_Ioi_self

Depends on / 依赖: Ioo_subset_Ioi_self, Set.Ioo_subset_Ioi_self, bounded_ge_Ioi
-/
theorem bounded_ge_Ioo [Preorder α] (a b : α) : Bounded (· >= ·) (Ioo a b) :=
  (bounded_ge_Ioi a).mono Set.Ioo_subset_Ioi_self

/--
theorem `bounded_ge_Ioc` / 定理 `bounded_ge_Ioc`

English:
theorem bounded_ge_Ioc
  given: [Preorder α] (a b : α)
  statement: Bounded (· >= ·) (Ioc a b)
  proof: (bounded_ge_Ioi a).mono Set.Ioc_subset_Ioi_self

中文:
定理 bounded_ge_Ioc
  条件: [预序 α] (a b : α)
  结论: 有界 (· >= ·) (左开右闭区间 a b)
  证明: (bounded_ge_Ioi a).mono Set.Ioc_subset_Ioi_self

Depends on / 依赖: Ioc_subset_Ioi_self, Set.Ioc_subset_Ioi_self, bounded_ge_Ioi
-/
theorem bounded_ge_Ioc [Preorder α] (a b : α) : Bounded (· >= ·) (Ioc a b) :=
  (bounded_ge_Ioi a).mono Set.Ioc_subset_Ioi_self

/--
theorem `bounded_ge_Ico` / 定理 `bounded_ge_Ico`

English:
theorem bounded_ge_Ico
  given: [Preorder α] (a b : α)
  statement: Bounded (· >= ·) (Ico a b)
  proof: (bounded_ge_Ici a).mono Set.Ico_subset_Ici_self

中文:
定理 bounded_ge_Ico
  条件: [预序 α] (a b : α)
  结论: 有界 (· >= ·) (左闭右开区间 a b)
  证明: (bounded_ge_Ici a).mono Set.Ico_subset_Ici_self

Depends on / 依赖: Ico_subset_Ici_self, Set.Ico_subset_Ici_self, bounded_ge_Ici
-/
theorem bounded_ge_Ico [Preorder α] (a b : α) : Bounded (· >= ·) (Ico a b) :=
  (bounded_ge_Ici a).mono Set.Ico_subset_Ici_self

/--
theorem `bounded_ge_Icc` / 定理 `bounded_ge_Icc`

English:
theorem bounded_ge_Icc
  given: [Preorder α] (a b : α)
  statement: Bounded (· >= ·) (Icc a b)
  proof: (bounded_ge_Ici a).mono Set.Icc_subset_Ici_self

中文:
定理 bounded_ge_Icc
  条件: [预序 α] (a b : α)
  结论: 有界 (· >= ·) (闭区间 a b)
  证明: (bounded_ge_Ici a).mono Set.Icc_subset_Ici_self

Depends on / 依赖: Icc_subset_Ici_self, Set.Icc_subset_Ici_self, bounded_ge_Ici
-/
theorem bounded_ge_Icc [Preorder α] (a b : α) : Bounded (· >= ·) (Icc a b) :=
  (bounded_ge_Ici a).mono Set.Icc_subset_Ici_self



/--
theorem `unbounded_le_Ioi` / 定理 `unbounded_le_Ioi`

English:
theorem unbounded_le_Ioi
  given: [SemilatticeSup α] [NoMaxOrder α] (a : α)
  proof: fun b =>
  let ⟨c, hc⟩ := exists_gt (a ⊔ b)
  ⟨c, le_sup_left.trans_lt hc, (le_sup_right.trans_lt hc).not_ge⟩

中文:
定理 unbounded_le_Ioi
  条件: [SemilatticeSup α] [NoMax序 α] (a : α)
  证明: fun b =>
  let ⟨c, hc⟩ := exists_gt (a ⊔ b)
  ⟨c, le_sup_left.trans_lt hc, (le_sup_right.trans_lt hc).not_ge⟩
-/
theorem unbounded_le_Ioi [SemilatticeSup α] [NoMaxOrder α] (a : α) :
    Unbounded (· <= ·) (Ioi a) := fun b =>
  let ⟨c, hc⟩ := exists_gt (a ⊔ b)
  ⟨c, le_sup_left.trans_lt hc, (le_sup_right.trans_lt hc).not_ge⟩

/--
theorem `unbounded_le_Ici` / 定理 `unbounded_le_Ici`

English:
theorem unbounded_le_Ici
  given: [SemilatticeSup α] [NoMaxOrder α] (a : α)
  proof: (unbounded_le_Ioi a).mono Set.Ioi_subset_Ici_self

中文:
定理 unbounded_le_Ici
  条件: [SemilatticeSup α] [NoMax序 α] (a : α)
  证明: (unbounded_le_Ioi a).mono Set.Ioi_subset_Ici_self

Depends on / 依赖: Ioi_subset_Ici_self, Set.Ioi_subset_Ici_self, unbounded_le_Ioi
-/
theorem unbounded_le_Ici [SemilatticeSup α] [NoMaxOrder α] (a : α) :
    Unbounded (· <= ·) (Ici a) :=
  (unbounded_le_Ioi a).mono Set.Ioi_subset_Ici_self

/--
theorem `unbounded_lt_Ioi` / 定理 `unbounded_lt_Ioi`

English:
theorem unbounded_lt_Ioi
  given: [SemilatticeSup α] [NoMaxOrder α] (a : α)
  proof: unbounded_lt_of_unbounded_le (unbounded_le_Ioi a)

中文:
定理 unbounded_lt_Ioi
  条件: [SemilatticeSup α] [NoMax序 α] (a : α)
  证明: unbounded_lt_of_unbounded_le (unbounded_le_Ioi a)

Depends on / 依赖: unbounded_le_Ioi, unbounded_lt_of_unbounded_le
-/
theorem unbounded_lt_Ioi [SemilatticeSup α] [NoMaxOrder α] (a : α) :
    Unbounded (· < ·) (Ioi a) :=
  unbounded_lt_of_unbounded_le (unbounded_le_Ioi a)

/--
theorem `unbounded_lt_Ici` / 定理 `unbounded_lt_Ici`

English:
theorem unbounded_lt_Ici
  given: [SemilatticeSup α] (a : α)
  statement: Unbounded (· < ·) (Ici a)
  proof: fun b =>
  ⟨a ⊔ b, le_sup_left, le_sup_right.not_gt⟩

中文:
定理 unbounded_lt_Ici
  条件: [SemilatticeSup α] (a : α)
  结论: Unbounded (· < ·) (左闭右无界区间 a)
  证明: fun b =>
  ⟨a ⊔ b, le_sup_left, le_sup_right.not_gt⟩
-/
theorem unbounded_lt_Ici [SemilatticeSup α] (a : α) : Unbounded (· < ·) (Ici a) := fun b =>
  ⟨a ⊔ b, le_sup_left, le_sup_right.not_gt⟩



/--
theorem `bounded_inter_not` / 定理 `bounded_inter_not`

English:
theorem bounded_inter_not
  given: (H : forall a b, exists m, forall c, r c a ∨ r c b -> r c m) (a : α)
  proof: by
  refine ⟨?_, Bounded.mono inter_subset_left⟩
  rintro ⟨b, hb⟩
  obtain ⟨m, hm⟩ := H a b
  exact ⟨m, fun c hc => hm c (or_iff_not_imp_left.2 fun hca => hb c ⟨hc, hca⟩)⟩

中文:
定理 bounded_inter_not
  条件: (H : 对任意 a b, 存在 m, 对任意 c, r c a ∨ r c b -> r c m) (a : α)
  证明: by
  refine ⟨?_, Bounded.mono inter_subset_left⟩
  rintro ⟨b, hb⟩
  obtain ⟨m, hm⟩ := H a b
  exact ⟨m, fun c hc => hm c (or_iff_not_imp_left.2 fun hca => hb c ⟨hc, hca⟩)⟩

Depends on / 依赖: Bounded, Bounded.mono, inter_subset_left, or_iff_not_imp_left
-/
theorem bounded_inter_not (H : forall a b, exists m, forall c, r c a ∨ r c b -> r c m) (a : α) :
    Bounded r (s inter { b | ¬r b a }) ↔ Bounded r s := by
  refine ⟨?_, Bounded.mono inter_subset_left⟩
  rintro ⟨b, hb⟩
  obtain ⟨m, hm⟩ := H a b
  exact ⟨m, fun c hc => hm c (or_iff_not_imp_left.2 fun hca => hb c ⟨hc, hca⟩)⟩

/--
theorem `unbounded_inter_not` / 定理 `unbounded_inter_not`

English:
theorem unbounded_inter_not
  given: (H : forall a b, exists m, forall c, r c a ∨ r c b -> r c m) (a : α)
  proof: by
  simp_rw [← not_bounded_iff, bounded_inter_not H]

中文:
定理 unbounded_inter_not
  条件: (H : 对任意 a b, 存在 m, 对任意 c, r c a ∨ r c b -> r c m) (a : α)
  证明: by
  simp_rw [← not_bounded_iff, bounded_inter_not H]

Depends on / 依赖: bounded_inter_not, not_bounded_iff, simp_rw
-/
theorem unbounded_inter_not (H : forall a b, exists m, forall c, r c a ∨ r c b -> r c m) (a : α) :
    Unbounded r (s inter { b | ¬r b a }) ↔ Unbounded r s := by
  simp_rw [← not_bounded_iff, bounded_inter_not H]



/--
theorem `bounded_le_inter_not_le` / 定理 `bounded_le_inter_not_le`

English:
theorem bounded_le_inter_not_le
  given: [SemilatticeSup α] (a : α)
  proof: bounded_inter_not (fun x y => ⟨x ⊔ y, fun _ h => h.elim le_sup_of_le_left le_sup_of_le_right⟩) a

中文:
定理 bounded_le_inter_not_le
  条件: [SemilatticeSup α] (a : α)
  证明: bounded_inter_not (fun x y => ⟨x ⊔ y, fun _ h => h.elim le_sup_of_le_left le_sup_of_le_right⟩) a

Depends on / 依赖: bounded_inter_not, h.elim, le_sup_of_le_left, le_sup_of_le_right
-/
theorem bounded_le_inter_not_le [SemilatticeSup α] (a : α) :
    Bounded (· <= ·) (s inter { b | ¬b <= a }) ↔ Bounded (· <= ·) s :=
  bounded_inter_not (fun x y => ⟨x ⊔ y, fun _ h => h.elim le_sup_of_le_left le_sup_of_le_right⟩) a

/--
theorem `unbounded_le_inter_not_le` / 定理 `unbounded_le_inter_not_le`

English:
theorem unbounded_le_inter_not_le
  given: [SemilatticeSup α] (a : α)
  proof: by
  rw [← not_bounded_iff]; rw [← not_bounded_iff]; rw [not_iff_not]
  exact bounded_le_inter_not_le a

中文:
定理 unbounded_le_inter_not_le
  条件: [SemilatticeSup α] (a : α)
  证明: by
  rw [← not_bounded_iff]; rw [← not_bounded_iff]; rw [not_iff_not]
  exact bounded_le_inter_not_le a

Depends on / 依赖: bounded_le_inter_not_le, not_bounded_iff, not_iff_not
-/
theorem unbounded_le_inter_not_le [SemilatticeSup α] (a : α) :
    Unbounded (· <= ·) (s inter { b | ¬b <= a }) ↔ Unbounded (· <= ·) s := by
  rw [← not_bounded_iff]; rw [← not_bounded_iff]; rw [not_iff_not]
  exact bounded_le_inter_not_le a

/--
theorem `bounded_le_inter_lt` / 定理 `bounded_le_inter_lt`

English:
theorem bounded_le_inter_lt
  given: [LinearOrder α] (a : α)
  proof: by
  simp_rw [← not_le, bounded_le_inter_not_le]

中文:
定理 bounded_le_inter_lt
  条件: [线性序 α] (a : α)
  证明: by
  simp_rw [← not_le, bounded_le_inter_not_le]

Depends on / 依赖: bounded_le_inter_not_le, not_le, simp_rw
-/
theorem bounded_le_inter_lt [LinearOrder α] (a : α) :
    Bounded (· <= ·) (s inter { b | a < b }) ↔ Bounded (· <= ·) s := by
  simp_rw [← not_le, bounded_le_inter_not_le]

/--
theorem `unbounded_le_inter_lt` / 定理 `unbounded_le_inter_lt`

English:
theorem unbounded_le_inter_lt
  given: [LinearOrder α] (a : α)
  proof: by
  convert! @unbounded_le_inter_not_le _ s _ a
  exact lt_iff_not_ge

中文:
定理 unbounded_le_inter_lt
  条件: [线性序 α] (a : α)
  证明: by
  convert! @unbounded_le_inter_not_le _ s _ a
  exact lt_iff_not_ge

Depends on / 依赖: convert, lt_iff_not_ge, unbounded_le_inter_not_le
-/
theorem unbounded_le_inter_lt [LinearOrder α] (a : α) :
    Unbounded (· <= ·) (s inter { b | a < b }) ↔ Unbounded (· <= ·) s := by
  convert! @unbounded_le_inter_not_le _ s _ a
  exact lt_iff_not_ge

/--
theorem `bounded_le_inter_le` / 定理 `bounded_le_inter_le`

English:
theorem bounded_le_inter_le
  given: [LinearOrder α] (a : α)
  proof: by
  refine ⟨?_, Bounded.mono Set.inter_subset_left⟩
  rw [← @bounded_le_inter_lt _ s _ a]
  exact Bounded.mono fun x ⟨hx, hx'⟩ => ⟨hx, le_of_lt hx'⟩

中文:
定理 bounded_le_inter_le
  条件: [线性序 α] (a : α)
  证明: by
  refine ⟨?_, Bounded.mono Set.inter_subset_left⟩
  rw [← @bounded_le_inter_lt _ s _ a]
  exact Bounded.mono fun x ⟨hx, hx'⟩ => ⟨hx, le_of_lt hx'⟩

Depends on / 依赖: Bounded, Bounded.mono, Set.inter_subset_left, bounded_le_inter_lt, inter_subset_left, le_of_lt
-/
theorem bounded_le_inter_le [LinearOrder α] (a : α) :
    Bounded (· <= ·) (s inter { b | a <= b }) ↔ Bounded (· <= ·) s := by
  refine ⟨?_, Bounded.mono Set.inter_subset_left⟩
  rw [← @bounded_le_inter_lt _ s _ a]
  exact Bounded.mono fun x ⟨hx, hx'⟩ => ⟨hx, le_of_lt hx'⟩

/--
theorem `unbounded_le_inter_le` / 定理 `unbounded_le_inter_le`

English:
theorem unbounded_le_inter_le
  given: [LinearOrder α] (a : α)
  proof: by
  rw [← not_bounded_iff]; rw [← not_bounded_iff]; rw [not_iff_not]
  exact bounded_le_inter_le a

中文:
定理 unbounded_le_inter_le
  条件: [线性序 α] (a : α)
  证明: by
  rw [← not_bounded_iff]; rw [← not_bounded_iff]; rw [not_iff_not]
  exact bounded_le_inter_le a

Depends on / 依赖: bounded_le_inter_le, not_bounded_iff, not_iff_not
-/
theorem unbounded_le_inter_le [LinearOrder α] (a : α) :
    Unbounded (· <= ·) (s inter { b | a <= b }) ↔ Unbounded (· <= ·) s := by
  rw [← not_bounded_iff]; rw [← not_bounded_iff]; rw [not_iff_not]
  exact bounded_le_inter_le a



/--
theorem `bounded_lt_inter_not_lt` / 定理 `bounded_lt_inter_not_lt`

English:
theorem bounded_lt_inter_not_lt
  given: [SemilatticeSup α] (a : α)
  proof: bounded_inter_not (fun x y => ⟨x ⊔ y, fun _ h => h.elim lt_sup_of_lt_left lt_sup_of_lt_right⟩) a

中文:
定理 bounded_lt_inter_not_lt
  条件: [SemilatticeSup α] (a : α)
  证明: bounded_inter_not (fun x y => ⟨x ⊔ y, fun _ h => h.elim lt_sup_of_lt_left lt_sup_of_lt_right⟩) a

Depends on / 依赖: bounded_inter_not, h.elim, lt_sup_of_lt_left, lt_sup_of_lt_right
-/
theorem bounded_lt_inter_not_lt [SemilatticeSup α] (a : α) :
    Bounded (· < ·) (s inter { b | ¬b < a }) ↔ Bounded (· < ·) s :=
  bounded_inter_not (fun x y => ⟨x ⊔ y, fun _ h => h.elim lt_sup_of_lt_left lt_sup_of_lt_right⟩) a

/--
theorem `unbounded_lt_inter_not_lt` / 定理 `unbounded_lt_inter_not_lt`

English:
theorem unbounded_lt_inter_not_lt
  given: [SemilatticeSup α] (a : α)
  proof: by
  rw [← not_bounded_iff]; rw [← not_bounded_iff]; rw [not_iff_not]
  exact bounded_lt_inter_not_lt a

中文:
定理 unbounded_lt_inter_not_lt
  条件: [SemilatticeSup α] (a : α)
  证明: by
  rw [← not_bounded_iff]; rw [← not_bounded_iff]; rw [not_iff_not]
  exact bounded_lt_inter_not_lt a

Depends on / 依赖: bounded_lt_inter_not_lt, not_bounded_iff, not_iff_not
-/
theorem unbounded_lt_inter_not_lt [SemilatticeSup α] (a : α) :
    Unbounded (· < ·) (s inter { b | ¬b < a }) ↔ Unbounded (· < ·) s := by
  rw [← not_bounded_iff]; rw [← not_bounded_iff]; rw [not_iff_not]
  exact bounded_lt_inter_not_lt a

/--
theorem `bounded_lt_inter_le` / 定理 `bounded_lt_inter_le`

English:
theorem bounded_lt_inter_le
  given: [LinearOrder α] (a : α)
  proof: by
  convert! @bounded_lt_inter_not_lt _ s _ a
  exact not_lt.symm

中文:
定理 bounded_lt_inter_le
  条件: [线性序 α] (a : α)
  证明: by
  convert! @bounded_lt_inter_not_lt _ s _ a
  exact not_lt.symm

Depends on / 依赖: bounded_lt_inter_not_lt, convert, not_lt, not_lt.symm
-/
theorem bounded_lt_inter_le [LinearOrder α] (a : α) :
    Bounded (· < ·) (s inter { b | a <= b }) ↔ Bounded (· < ·) s := by
  convert! @bounded_lt_inter_not_lt _ s _ a
  exact not_lt.symm

/--
theorem `unbounded_lt_inter_le` / 定理 `unbounded_lt_inter_le`

English:
theorem unbounded_lt_inter_le
  given: [LinearOrder α] (a : α)
  proof: by
  convert! @unbounded_lt_inter_not_lt _ s _ a
  exact not_lt.symm

中文:
定理 unbounded_lt_inter_le
  条件: [线性序 α] (a : α)
  证明: by
  convert! @unbounded_lt_inter_not_lt _ s _ a
  exact not_lt.symm

Depends on / 依赖: convert, not_lt, not_lt.symm, unbounded_lt_inter_not_lt
-/
theorem unbounded_lt_inter_le [LinearOrder α] (a : α) :
    Unbounded (· < ·) (s inter { b | a <= b }) ↔ Unbounded (· < ·) s := by
  convert! @unbounded_lt_inter_not_lt _ s _ a
  exact not_lt.symm

/--
theorem `bounded_lt_inter_lt` / 定理 `bounded_lt_inter_lt`

English:
theorem bounded_lt_inter_lt
  given: [LinearOrder α] [NoMaxOrder α] (a : α)
  proof: by
  rw [← bounded_le_iff_bounded_lt]; rw [← bounded_le_iff_bounded_lt]
  exact bounded_le_inter_lt a

中文:
定理 bounded_lt_inter_lt
  条件: [线性序 α] [NoMax序 α] (a : α)
  证明: by
  rw [← bounded_le_iff_bounded_lt]; rw [← bounded_le_iff_bounded_lt]
  exact bounded_le_inter_lt a

Depends on / 依赖: bounded_le_iff_bounded_lt, bounded_le_inter_lt
-/
theorem bounded_lt_inter_lt [LinearOrder α] [NoMaxOrder α] (a : α) :
    Bounded (· < ·) (s inter { b | a < b }) ↔ Bounded (· < ·) s := by
  rw [← bounded_le_iff_bounded_lt]; rw [← bounded_le_iff_bounded_lt]
  exact bounded_le_inter_lt a

/--
theorem `unbounded_lt_inter_lt` / 定理 `unbounded_lt_inter_lt`

English:
theorem unbounded_lt_inter_lt
  given: [LinearOrder α] [NoMaxOrder α] (a : α)
  proof: by
  rw [← not_bounded_iff]; rw [← not_bounded_iff]; rw [not_iff_not]
  exact bounded_lt_inter_lt a

中文:
定理 unbounded_lt_inter_lt
  条件: [线性序 α] [NoMax序 α] (a : α)
  证明: by
  rw [← not_bounded_iff]; rw [← not_bounded_iff]; rw [not_iff_not]
  exact bounded_lt_inter_lt a

Depends on / 依赖: bounded_lt_inter_lt, not_bounded_iff, not_iff_not
-/
theorem unbounded_lt_inter_lt [LinearOrder α] [NoMaxOrder α] (a : α) :
    Unbounded (· < ·) (s inter { b | a < b }) ↔ Unbounded (· < ·) s := by
  rw [← not_bounded_iff]; rw [← not_bounded_iff]; rw [not_iff_not]
  exact bounded_lt_inter_lt a



/--
theorem `bounded_ge_inter_not_ge` / 定理 `bounded_ge_inter_not_ge`

English:
theorem bounded_ge_inter_not_ge
  given: [SemilatticeInf α] (a : α)
  proof: @bounded_le_inter_not_le αᵒᵈ s _ a

中文:
定理 bounded_ge_inter_not_ge
  条件: [SemilatticeInf α] (a : α)
  证明: @bounded_le_inter_not_le αᵒᵈ s _ a

Depends on / 依赖: bounded_le_inter_not_le
-/
theorem bounded_ge_inter_not_ge [SemilatticeInf α] (a : α) :
    Bounded (· >= ·) (s inter { b | ¬a <= b }) ↔ Bounded (· >= ·) s :=
  @bounded_le_inter_not_le αᵒᵈ s _ a

/--
theorem `unbounded_ge_inter_not_ge` / 定理 `unbounded_ge_inter_not_ge`

English:
theorem unbounded_ge_inter_not_ge
  given: [SemilatticeInf α] (a : α)
  proof: @unbounded_le_inter_not_le αᵒᵈ s _ a

中文:
定理 unbounded_ge_inter_not_ge
  条件: [SemilatticeInf α] (a : α)
  证明: @unbounded_le_inter_not_le αᵒᵈ s _ a

Depends on / 依赖: unbounded_le_inter_not_le
-/
theorem unbounded_ge_inter_not_ge [SemilatticeInf α] (a : α) :
    Unbounded (· >= ·) (s inter { b | ¬a <= b }) ↔ Unbounded (· >= ·) s :=
  @unbounded_le_inter_not_le αᵒᵈ s _ a

/--
theorem `bounded_ge_inter_gt` / 定理 `bounded_ge_inter_gt`

English:
theorem bounded_ge_inter_gt
  given: [LinearOrder α] (a : α)
  proof: @bounded_le_inter_lt αᵒᵈ s _ a

中文:
定理 bounded_ge_inter_gt
  条件: [线性序 α] (a : α)
  证明: @bounded_le_inter_lt αᵒᵈ s _ a

Depends on / 依赖: bounded_le_inter_lt
-/
theorem bounded_ge_inter_gt [LinearOrder α] (a : α) :
    Bounded (· >= ·) (s inter { b | b < a }) ↔ Bounded (· >= ·) s :=
  @bounded_le_inter_lt αᵒᵈ s _ a

/--
theorem `unbounded_ge_inter_gt` / 定理 `unbounded_ge_inter_gt`

English:
theorem unbounded_ge_inter_gt
  given: [LinearOrder α] (a : α)
  proof: @unbounded_le_inter_lt αᵒᵈ s _ a

中文:
定理 unbounded_ge_inter_gt
  条件: [线性序 α] (a : α)
  证明: @unbounded_le_inter_lt αᵒᵈ s _ a

Depends on / 依赖: unbounded_le_inter_lt
-/
theorem unbounded_ge_inter_gt [LinearOrder α] (a : α) :
    Unbounded (· >= ·) (s inter { b | b < a }) ↔ Unbounded (· >= ·) s :=
  @unbounded_le_inter_lt αᵒᵈ s _ a

/--
theorem `bounded_ge_inter_ge` / 定理 `bounded_ge_inter_ge`

English:
theorem bounded_ge_inter_ge
  given: [LinearOrder α] (a : α)
  proof: @bounded_le_inter_le αᵒᵈ s _ a

中文:
定理 bounded_ge_inter_ge
  条件: [线性序 α] (a : α)
  证明: @bounded_le_inter_le αᵒᵈ s _ a

Depends on / 依赖: bounded_le_inter_le
-/
theorem bounded_ge_inter_ge [LinearOrder α] (a : α) :
    Bounded (· >= ·) (s inter { b | b <= a }) ↔ Bounded (· >= ·) s :=
  @bounded_le_inter_le αᵒᵈ s _ a

/--
theorem `unbounded_ge_iff_unbounded_inter_ge` / 定理 `unbounded_ge_iff_unbounded_inter_ge`

English:
theorem unbounded_ge_iff_unbounded_inter_ge
  given: [LinearOrder α] (a : α)
  proof: @unbounded_le_inter_le αᵒᵈ s _ a

中文:
定理 unbounded_ge_iff_unbounded_inter_ge
  条件: [线性序 α] (a : α)
  证明: @unbounded_le_inter_le αᵒᵈ s _ a

Depends on / 依赖: unbounded_le_inter_le
-/
theorem unbounded_ge_iff_unbounded_inter_ge [LinearOrder α] (a : α) :
    Unbounded (· >= ·) (s inter { b | b <= a }) ↔ Unbounded (· >= ·) s :=
  @unbounded_le_inter_le αᵒᵈ s _ a



/--
theorem `bounded_gt_inter_not_gt` / 定理 `bounded_gt_inter_not_gt`

English:
theorem bounded_gt_inter_not_gt
  given: [SemilatticeInf α] (a : α)
  proof: @bounded_lt_inter_not_lt αᵒᵈ s _ a

中文:
定理 bounded_gt_inter_not_gt
  条件: [SemilatticeInf α] (a : α)
  证明: @bounded_lt_inter_not_lt αᵒᵈ s _ a

Depends on / 依赖: bounded_lt_inter_not_lt
-/
theorem bounded_gt_inter_not_gt [SemilatticeInf α] (a : α) :
    Bounded (· > ·) (s inter { b | ¬a < b }) ↔ Bounded (· > ·) s :=
  @bounded_lt_inter_not_lt αᵒᵈ s _ a

/--
theorem `unbounded_gt_inter_not_gt` / 定理 `unbounded_gt_inter_not_gt`

English:
theorem unbounded_gt_inter_not_gt
  given: [SemilatticeInf α] (a : α)
  proof: @unbounded_lt_inter_not_lt αᵒᵈ s _ a

中文:
定理 unbounded_gt_inter_not_gt
  条件: [SemilatticeInf α] (a : α)
  证明: @unbounded_lt_inter_not_lt αᵒᵈ s _ a

Depends on / 依赖: unbounded_lt_inter_not_lt
-/
theorem unbounded_gt_inter_not_gt [SemilatticeInf α] (a : α) :
    Unbounded (· > ·) (s inter { b | ¬a < b }) ↔ Unbounded (· > ·) s :=
  @unbounded_lt_inter_not_lt αᵒᵈ s _ a

/--
theorem `bounded_gt_inter_ge` / 定理 `bounded_gt_inter_ge`

English:
theorem bounded_gt_inter_ge
  given: [LinearOrder α] (a : α)
  proof: @bounded_lt_inter_le αᵒᵈ s _ a

中文:
定理 bounded_gt_inter_ge
  条件: [线性序 α] (a : α)
  证明: @bounded_lt_inter_le αᵒᵈ s _ a

Depends on / 依赖: bounded_lt_inter_le
-/
theorem bounded_gt_inter_ge [LinearOrder α] (a : α) :
    Bounded (· > ·) (s inter { b | b <= a }) ↔ Bounded (· > ·) s :=
  @bounded_lt_inter_le αᵒᵈ s _ a

/--
theorem `unbounded_inter_ge` / 定理 `unbounded_inter_ge`

English:
theorem unbounded_inter_ge
  given: [LinearOrder α] (a : α)
  proof: @unbounded_lt_inter_le αᵒᵈ s _ a

中文:
定理 unbounded_inter_ge
  条件: [线性序 α] (a : α)
  证明: @unbounded_lt_inter_le αᵒᵈ s _ a

Depends on / 依赖: unbounded_lt_inter_le
-/
theorem unbounded_inter_ge [LinearOrder α] (a : α) :
    Unbounded (· > ·) (s inter { b | b <= a }) ↔ Unbounded (· > ·) s :=
  @unbounded_lt_inter_le αᵒᵈ s _ a

/--
theorem `bounded_gt_inter_gt` / 定理 `bounded_gt_inter_gt`

English:
theorem bounded_gt_inter_gt
  given: [LinearOrder α] [NoMinOrder α] (a : α)
  proof: @bounded_lt_inter_lt αᵒᵈ s _ _ a

中文:
定理 bounded_gt_inter_gt
  条件: [线性序 α] [NoMin序 α] (a : α)
  证明: @bounded_lt_inter_lt αᵒᵈ s _ _ a

Depends on / 依赖: bounded_lt_inter_lt
-/
theorem bounded_gt_inter_gt [LinearOrder α] [NoMinOrder α] (a : α) :
    Bounded (· > ·) (s inter { b | b < a }) ↔ Bounded (· > ·) s :=
  @bounded_lt_inter_lt αᵒᵈ s _ _ a

/--
theorem `unbounded_gt_inter_gt` / 定理 `unbounded_gt_inter_gt`

English:
theorem unbounded_gt_inter_gt
  given: [LinearOrder α] [NoMinOrder α] (a : α)
  proof: @unbounded_lt_inter_lt αᵒᵈ s _ _ a

中文:
定理 unbounded_gt_inter_gt
  条件: [线性序 α] [NoMin序 α] (a : α)
  证明: @unbounded_lt_inter_lt αᵒᵈ s _ _ a

Depends on / 依赖: unbounded_lt_inter_lt
-/
theorem unbounded_gt_inter_gt [LinearOrder α] [NoMinOrder α] (a : α) :
    Unbounded (· > ·) (s inter { b | b < a }) ↔ Unbounded (· > ·) s :=
  @unbounded_lt_inter_lt αᵒᵈ s _ _ a

end Set
