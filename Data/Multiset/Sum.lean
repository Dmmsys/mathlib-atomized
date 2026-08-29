/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Multiset

/-!
# Disjoint sum of multisets

This file defines the disjoint sum of two multisets as `Multiset (α ⊕ β)`. Beware not to confuse
with the `Multiset.sum` operation which computes the additive sum.

## Main declarations

* `Multiset.disjSum`: `s.disjSum t` is the disjoint sum of `s` and `t`.
-/

@[expose] public section


open Sum

namespace Multiset

variable {α β γ : Type*} (s : Multiset α) (t : Multiset β)

/--
Definition of `disjSum` / `disjSum` 的定义

English:
definition disjSum
  signature: : Multiset (α oplus β)
  body: s.map inl + t.map inr

@[simp]

中文:
定义 disjSum
  签名: : Multiset (α oplus β)
  定义体: s.map inl + t.map inr

@[simp]

Depends on / 依赖: s.map, t.map
-/
def disjSum : Multiset (α oplus β) :=
  s.map inl + t.map inr

@[simp]
/--
theorem `zero_disjSum` / 定理 `zero_disjSum`

English:
theorem zero_disjSum
  statement: (0 : Multiset α).disjSum t = t.map inr
  proof: Multiset.zero_add _

@[simp]

中文:
定理 zero_disjSum
  结论: (0 : Multiset α).disjSum t = t.map inr
  证明: Multiset.zero_add _

@[simp]

Depends on / 依赖: Multiset, Multiset.zero_add, zero_add
-/
theorem zero_disjSum : (0 : Multiset α).disjSum t = t.map inr :=
  Multiset.zero_add _

@[simp]
/--
theorem `disjSum_zero` / 定理 `disjSum_zero`

English:
theorem disjSum_zero
  statement: s.disjSum (0 : Multiset β) = s.map inl
  proof: Multiset.add_zero _

@[simp]

中文:
定理 disjSum_zero
  结论: s.disjSum (0 : Multiset β) = s.map inl
  证明: Multiset.add_zero _

@[simp]

Depends on / 依赖: Multiset, Multiset.add_zero, add_zero
-/
theorem disjSum_zero : s.disjSum (0 : Multiset β) = s.map inl :=
  Multiset.add_zero _

@[simp]
/--
theorem `card_disjSum` / 定理 `card_disjSum`

English:
theorem card_disjSum
  statement: Multiset.card (s.disjSum t) = Multiset.card s + Multiset.card t
  proof: by
  rw [disjSum]; rw [card_add]; rw [card_map]; rw [card_map]

中文:
定理 card_disjSum
  结论: Multiset.card (s.disjSum t) = Multiset.card s + Multiset.card t
  证明: by
  rw [disjSum]; rw [card_add]; rw [card_map]; rw [card_map]

Depends on / 依赖: card_add, card_map, disjSum
-/
theorem card_disjSum : Multiset.card (s.disjSum t) = Multiset.card s + Multiset.card t := by
  rw [disjSum]; rw [card_add]; rw [card_map]; rw [card_map]

variable {s t} {s₁ s₂ : Multiset α} {t₁ t₂ : Multiset β} {a : α} {b : β} {x : α oplus β}

/--
theorem `mem_disjSum` / 定理 `mem_disjSum`

English:
theorem mem_disjSum
  statement: x in s.disjSum t ↔ (exists a, a in s ∧ inl a = x) ∨ exists b, b in t ∧ inr b = x
  proof: by
  simp_rw [disjSum, mem_add, mem_map]

@[simp]

中文:
定理 mem_disjSum
  结论: x in s.disjSum t ↔ (存在 a, a in s ∧ inl a = x) ∨ 存在 b, b in t ∧ inr b = x
  证明: by
  simp_rw [disjSum, mem_add, mem_map]

@[simp]

Depends on / 依赖: disjSum, mem_add, mem_map, simp_rw
-/
theorem mem_disjSum : x in s.disjSum t ↔ (exists a, a in s ∧ inl a = x) ∨ exists b, b in t ∧ inr b = x := by
  simp_rw [disjSum, mem_add, mem_map]

@[simp]
/--
theorem `inl_mem_disjSum` / 定理 `inl_mem_disjSum`

English:
theorem inl_mem_disjSum
  statement: inl a in s.disjSum t ↔ a in s
  proof: by
  rw [mem_disjSum]; rw [or_iff_left]
  · simp only [inl.injEq, exists_eq_right]
  rintro ⟨b, _, hb⟩
  exact inr_ne_inl hb

@[simp]

中文:
定理 inl_mem_disjSum
  结论: inl a in s.disjSum t ↔ a in s
  证明: by
  rw [mem_disjSum]; rw [or_iff_left]
  · simp only [inl.injEq, exists_eq_right]
  rintro ⟨b, _, hb⟩
  exact inr_ne_inl hb

@[simp]

Depends on / 依赖: exists_eq_right, inl.injEq, inr_ne_inl, mem_disjSum, or_iff_left
-/
theorem inl_mem_disjSum : inl a in s.disjSum t ↔ a in s := by
  rw [mem_disjSum]; rw [or_iff_left]
  · simp only [inl.injEq, exists_eq_right]
  rintro ⟨b, _, hb⟩
  exact inr_ne_inl hb

@[simp]
/--
theorem `inr_mem_disjSum` / 定理 `inr_mem_disjSum`

English:
theorem inr_mem_disjSum
  statement: inr b in s.disjSum t ↔ b in t
  proof: by
  rw [mem_disjSum]; rw [or_iff_right]
  · simp only [inr.injEq, exists_eq_right]
  rintro ⟨a, _, ha⟩
  exact inl_ne_inr ha

中文:
定理 inr_mem_disjSum
  结论: inr b in s.disjSum t ↔ b in t
  证明: by
  rw [mem_disjSum]; rw [or_iff_right]
  · simp only [inr.injEq, exists_eq_right]
  rintro ⟨a, _, ha⟩
  exact inl_ne_inr ha

Depends on / 依赖: exists_eq_right, inl_ne_inr, inr.injEq, mem_disjSum, or_iff_right
-/
theorem inr_mem_disjSum : inr b in s.disjSum t ↔ b in t := by
  rw [mem_disjSum]; rw [or_iff_right]
  · simp only [inr.injEq, exists_eq_right]
  rintro ⟨a, _, ha⟩
  exact inl_ne_inr ha

/--
theorem `disjSum_mono` / 定理 `disjSum_mono`

English:
theorem disjSum_mono
  given: (hs : s₁ <= s₂) (ht : t₁ <= t₂)
  statement: s₁.disjSum t₁ <= s₂.disjSum t₂
  proof: add_le_add (map_le_map hs) (map_le_map ht)

中文:
定理 disjSum_mono
  条件: (hs : s₁ <= s₂) (ht : t₁ <= t₂)
  结论: s₁.disjSum t₁ <= s₂.disjSum t₂
  证明: add_le_add (map_le_map hs) (map_le_map ht)

Depends on / 依赖: add_le_add, map_le_map
-/
theorem disjSum_mono (hs : s₁ <= s₂) (ht : t₁ <= t₂) : s₁.disjSum t₁ <= s₂.disjSum t₂ :=
  add_le_add (map_le_map hs) (map_le_map ht)

/--
theorem `disjSum_mono_left` / 定理 `disjSum_mono_left`

English:
theorem disjSum_mono_left
  given: (t : Multiset β)
  statement: Monotone fun s : Multiset α => s.disjSum t
  proof: fun _ _ hs => Multiset.add_le_add_right (map_le_map hs)

中文:
定理 disjSum_mono_left
  条件: (t : Multiset β)
  结论: Monotone fun s : Multiset α => s.disjSum t
  证明: fun _ _ hs => Multiset.add_le_add_right (map_le_map hs)

Depends on / 依赖: Multiset, Multiset.add_le_add_right, add_le_add_right, map_le_map
-/
theorem disjSum_mono_left (t : Multiset β) : Monotone fun s : Multiset α => s.disjSum t :=
  fun _ _ hs => Multiset.add_le_add_right (map_le_map hs)

/--
theorem `disjSum_mono_right` / 定理 `disjSum_mono_right`

English:
theorem disjSum_mono_right
  given: (s : Multiset α)
  proof: fun _ _ ht =>
  Multiset.add_le_add_left (map_le_map ht)

中文:
定理 disjSum_mono_right
  条件: (s : Multiset α)
  证明: fun _ _ ht =>
  Multiset.add_le_add_left (map_le_map ht)
-/
theorem disjSum_mono_right (s : Multiset α) :
    Monotone (s.disjSum : Multiset β -> Multiset (α oplus β)) := fun _ _ ht =>
  Multiset.add_le_add_left (map_le_map ht)

/--
theorem `disjSum_lt_disjSum_of_lt_of_le` / 定理 `disjSum_lt_disjSum_of_lt_of_le`

English:
theorem disjSum_lt_disjSum_of_lt_of_le
  given: (hs : s₁ < s₂) (ht : t₁ <= t₂)
  proof: add_lt_add_of_lt_of_le (map_lt_map hs) (map_le_map ht)

中文:
定理 disjSum_lt_disjSum_of_lt_of_le
  条件: (hs : s₁ < s₂) (ht : t₁ <= t₂)
  证明: add_lt_add_of_lt_of_le (map_lt_map hs) (map_le_map ht)

Depends on / 依赖: add_lt_add_of_lt_of_le, map_le_map, map_lt_map
-/
theorem disjSum_lt_disjSum_of_lt_of_le (hs : s₁ < s₂) (ht : t₁ <= t₂) :
    s₁.disjSum t₁ < s₂.disjSum t₂ :=
  add_lt_add_of_lt_of_le (map_lt_map hs) (map_le_map ht)

/--
theorem `disjSum_lt_disjSum_of_le_of_lt` / 定理 `disjSum_lt_disjSum_of_le_of_lt`

English:
theorem disjSum_lt_disjSum_of_le_of_lt
  given: (hs : s₁ <= s₂) (ht : t₁ < t₂)
  proof: add_lt_add_of_le_of_lt (map_le_map hs) (map_lt_map ht)

中文:
定理 disjSum_lt_disjSum_of_le_of_lt
  条件: (hs : s₁ <= s₂) (ht : t₁ < t₂)
  证明: add_lt_add_of_le_of_lt (map_le_map hs) (map_lt_map ht)

Depends on / 依赖: add_lt_add_of_le_of_lt, map_le_map, map_lt_map
-/
theorem disjSum_lt_disjSum_of_le_of_lt (hs : s₁ <= s₂) (ht : t₁ < t₂) :
    s₁.disjSum t₁ < s₂.disjSum t₂ :=
  add_lt_add_of_le_of_lt (map_le_map hs) (map_lt_map ht)

/--
theorem `disjSum_strictMono_left` / 定理 `disjSum_strictMono_left`

English:
theorem disjSum_strictMono_left
  given: (t : Multiset β)
  statement: StrictMono fun s : Multiset α => s.disjSum t
  proof: fun _ _ hs => disjSum_lt_disjSum_of_lt_of_le hs le_rfl

中文:
定理 disjSum_strictMono_left
  条件: (t : Multiset β)
  结论: StrictMono fun s : Multiset α => s.disjSum t
  证明: fun _ _ hs => disjSum_lt_disjSum_of_lt_of_le hs le_rfl

Depends on / 依赖: disjSum_lt_disjSum_of_lt_of_le, le_rfl
-/
theorem disjSum_strictMono_left (t : Multiset β) : StrictMono fun s : Multiset α => s.disjSum t :=
  fun _ _ hs => disjSum_lt_disjSum_of_lt_of_le hs le_rfl

/--
theorem `disjSum_strictMono_right` / 定理 `disjSum_strictMono_right`

English:
theorem disjSum_strictMono_right
  given: (s : Multiset α)
  proof: fun _ _ =>
  disjSum_lt_disjSum_of_le_of_lt le_rfl

中文:
定理 disjSum_strictMono_right
  条件: (s : Multiset α)
  证明: fun _ _ =>
  disjSum_lt_disjSum_of_le_of_lt le_rfl
-/
theorem disjSum_strictMono_right (s : Multiset α) :
    StrictMono (s.disjSum : Multiset β -> Multiset (α oplus β)) := fun _ _ =>
  disjSum_lt_disjSum_of_le_of_lt le_rfl

/--
theorem `Nodup.disjSum` / 定理 `Nodup.disjSum`

English:
theorem Nodup.disjSum
  given: (hs : s.Nodup) (ht : t.Nodup)
  statement: (s.disjSum t).Nodup
  proof: by
  refine ((hs.map inl_injective).add_iff <| ht.map inr_injective).2 ?_
  rw [disjoint_map_map]
  exact fun _ _ _ _ => inr_ne_inl.symm

中文:
定理 Nodup.disjSum
  条件: (hs : s.Nodup) (ht : t.Nodup)
  结论: (s.disjSum t).Nodup
  证明: by
  refine ((hs.map inl_injective).add_iff <| ht.map inr_injective).2 ?_
  rw [disjoint_map_map]
  exact fun _ _ _ _ => inr_ne_inl.symm

Depends on / 依赖: _terminates, h.get
-/
protected theorem Nodup.disjSum (hs : s.Nodup) (ht : t.Nodup) : (s.disjSum t).Nodup := by
  refine ((hs.map inl_injective).add_iff <| ht.map inr_injective).2 ?_
  rw [disjoint_map_map]
  exact fun _ _ _ _ => inr_ne_inl.symm

/--
theorem `map_disjSum` / 定理 `map_disjSum`

English:
theorem map_disjSum
  given: (f : α oplus β -> γ)
  proof: by
  simp_rw [disjSum, map_add, map_map, Function.comp_def]

中文:
定理 map_disjSum
  条件: (f : α oplus β -> γ)
  证明: by
  simp_rw [disjSum, map_add, map_map, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, disjSum, map_add, map_map, simp_rw
-/
theorem map_disjSum (f : α oplus β -> γ) :
    (s.disjSum t).map f = s.map (f <| .inl ·) + t.map (f <| .inr ·) := by
  simp_rw [disjSum, map_add, map_map, Function.comp_def]

end Multiset
