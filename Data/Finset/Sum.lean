/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.Multiset.Sum

/-!
# Disjoint sum of finsets

This file defines the disjoint sum of two finsets as `Finset (α ⊕ β)`. Beware not to confuse with
the `Finset.sum` operation which computes the additive sum.

## Main declarations

* `Finset.disjSum`: `s.disjSum t` is the disjoint sum of `s` and `t`.
* `Finset.toLeft`: Given a finset of elements `α ⊕ β`, extracts all the elements of the form `α`.
* `Finset.toRight`: Given a finset of elements `α ⊕ β`, extracts all the elements of the form `β`.
-/

@[expose] public section

open Function Multiset Sum

namespace Finset

variable {α β γ : Type*} (s : Finset α) (t : Finset β)

/--
Definition of `disjSum` / `disjSum` 的定义

English:
definition disjSum
  signature: : Finset (α oplus β)
  body: ⟨s.1.disjSum t.1, s.2.disjSum t.2⟩

@[simp]

中文:
定义 disjSum
  签名: : Finset (α oplus β)
  定义体: ⟨s.1.disjSum t.1, s.2.disjSum t.2⟩

@[simp]

Depends on / 依赖: disjSum
-/
def disjSum : Finset (α oplus β) :=
  ⟨s.1.disjSum t.1, s.2.disjSum t.2⟩

@[simp]
/--
theorem `val_disjSum` / 定理 `val_disjSum`

English:
theorem val_disjSum
  statement: (s.disjSum t).1 = s.1.disjSum t.1
  proof: rfl

@[simp]

中文:
定理 val_disjSum
  结论: (s.disjSum t).1 = s.1.disjSum t.1
  证明: rfl

@[simp]
-/
theorem val_disjSum : (s.disjSum t).1 = s.1.disjSum t.1 :=
  rfl

@[simp]
/--
theorem `empty_disjSum` / 定理 `empty_disjSum`

English:
theorem empty_disjSum
  statement: (∅ : Finset α).disjSum t = t.map Embedding.inr
  proof: val_inj.1 Multiset.zero_disjSum _

@[simp]

中文:
定理 empty_disjSum
  结论: (∅ : Finset α).disjSum t = t.map Embedding.inr
  证明: val_inj.1 Multiset.zero_disjSum _

@[simp]

Depends on / 依赖: Multiset, Multiset.zero_disjSum, val_inj, zero_disjSum
-/
theorem empty_disjSum : (∅ : Finset α).disjSum t = t.map Embedding.inr :=
val_inj.1 Multiset.zero_disjSum _

@[simp]
/--
theorem `disjSum_empty` / 定理 `disjSum_empty`

English:
theorem disjSum_empty
  statement: s.disjSum (∅ : Finset β) = s.map Embedding.inl
  proof: val_inj.1 Multiset.disjSum_zero _

@[simp]

中文:
定理 disjSum_empty
  结论: s.disjSum (∅ : Finset β) = s.map Embedding.inl
  证明: val_inj.1 Multiset.disjSum_zero _

@[simp]

Depends on / 依赖: Multiset, Multiset.disjSum_zero, disjSum_zero, val_inj
-/
theorem disjSum_empty : s.disjSum (∅ : Finset β) = s.map Embedding.inl :=
val_inj.1 Multiset.disjSum_zero _

@[simp]
/--
theorem `card_disjSum` / 定理 `card_disjSum`

English:
theorem card_disjSum
  statement: (s.disjSum t).card = s.card + t.card
  proof: Multiset.card_disjSum _ _

中文:
定理 card_disjSum
  结论: (s.disjSum t).card = s.card + t.card
  证明: Multiset.card_disjSum _ _

Depends on / 依赖: Multiset, Multiset.card_disjSum, card_disjSum
-/
theorem card_disjSum : (s.disjSum t).card = s.card + t.card :=
  Multiset.card_disjSum _ _

/--
theorem `disjoint_map_inl_map_inr` / 定理 `disjoint_map_inl_map_inr`

English:
theorem disjoint_map_inl_map_inr
  statement: Disjoint (s.map Embedding.inl) (t.map Embedding.inr)
  proof: by
  simp_rw [disjoint_left, mem_map]
  rintro x ⟨a, _, rfl⟩ ⟨b, _, ⟨⟩⟩

@[simp]

中文:
定理 disjoint_map_inl_map_inr
  结论: Disjoint (s.map Embedding.inl) (t.map Embedding.inr)
  证明: by
  simp_rw [disjoint_left, mem_map]
  rintro x ⟨a, _, rfl⟩ ⟨b, _, ⟨⟩⟩

@[simp]

Depends on / 依赖: disjoint_left, mem_map, simp_rw
-/
theorem disjoint_map_inl_map_inr : Disjoint (s.map Embedding.inl) (t.map Embedding.inr) := by
  simp_rw [disjoint_left, mem_map]
  rintro x ⟨a, _, rfl⟩ ⟨b, _, ⟨⟩⟩

@[simp]
/--
theorem `map_inl_disjUnion_map_inr` / 定理 `map_inl_disjUnion_map_inr`

English:
theorem map_inl_disjUnion_map_inr
  proof: rfl

中文:
定理 map_inl_disjUnion_map_inr
  证明: rfl
-/
theorem map_inl_disjUnion_map_inr :
    (s.map Embedding.inl).disjUnion (t.map Embedding.inr) (disjoint_map_inl_map_inr _ _) =
      s.disjSum t :=
  rfl

variable {s t} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} {a : α} {b : β} {x : α oplus β}

/--
theorem `mem_disjSum` / 定理 `mem_disjSum`

English:
theorem mem_disjSum
  statement: x in s.disjSum t ↔ (exists a, a in s ∧ inl a = x) ∨ exists b, b in t ∧ inr b = x
  proof: Multiset.mem_disjSum

@[simp]

中文:
定理 mem_disjSum
  结论: x in s.disjSum t ↔ (存在 a, a in s ∧ inl a = x) ∨ 存在 b, b in t ∧ inr b = x
  证明: Multiset.mem_disjSum

@[simp]

Depends on / 依赖: Multiset, Multiset.mem_disjSum, mem_disjSum
-/
theorem mem_disjSum : x in s.disjSum t ↔ (exists a, a in s ∧ inl a = x) ∨ exists b, b in t ∧ inr b = x :=
  Multiset.mem_disjSum

@[simp]
/--
theorem `inl_mem_disjSum` / 定理 `inl_mem_disjSum`

English:
theorem inl_mem_disjSum
  statement: inl a in s.disjSum t ↔ a in s
  proof: Multiset.inl_mem_disjSum

@[simp]

中文:
定理 inl_mem_disjSum
  结论: inl a in s.disjSum t ↔ a in s
  证明: Multiset.inl_mem_disjSum

@[simp]

Depends on / 依赖: Multiset, Multiset.inl_mem_disjSum, inl_mem_disjSum
-/
theorem inl_mem_disjSum : inl a in s.disjSum t ↔ a in s :=
  Multiset.inl_mem_disjSum

@[simp]
/--
theorem `inr_mem_disjSum` / 定理 `inr_mem_disjSum`

English:
theorem inr_mem_disjSum
  statement: inr b in s.disjSum t ↔ b in t
  proof: Multiset.inr_mem_disjSum

@[simp]

中文:
定理 inr_mem_disjSum
  结论: inr b in s.disjSum t ↔ b in t
  证明: Multiset.inr_mem_disjSum

@[simp]

Depends on / 依赖: Multiset, Multiset.inr_mem_disjSum, inr_mem_disjSum
-/
theorem inr_mem_disjSum : inr b in s.disjSum t ↔ b in t :=
  Multiset.inr_mem_disjSum

@[simp]
/--
theorem `disjSum_eq_empty` / 定理 `disjSum_eq_empty`

English:
theorem disjSum_eq_empty
  statement: s.disjSum t = ∅ ↔ s = ∅ ∧ t = ∅
  proof: by simp [Finset.ext_iff]

中文:
定理 disjSum_eq_empty
  结论: s.disjSum t = ∅ ↔ s = ∅ ∧ t = ∅
  证明: by simp [Finset.ext_iff]

Depends on / 依赖: Finset, Finset.ext_iff, ext_iff
-/
theorem disjSum_eq_empty : s.disjSum t = ∅ ↔ s = ∅ ∧ t = ∅ := by simp [Finset.ext_iff]

/--
theorem `disjSum_mono` / 定理 `disjSum_mono`

English:
theorem disjSum_mono
  given: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂)
  statement: s₁.disjSum t₁ subseteq s₂.disjSum t₂
  proof: val_le_iff.1 Multiset.disjSum_mono (val_le_iff.2 hs) (val_le_iff.2 ht)

中文:
定理 disjSum_mono
  条件: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂)
  结论: s₁.disjSum t₁ subseteq s₂.disjSum t₂
  证明: val_le_iff.1 Multiset.disjSum_mono (val_le_iff.2 hs) (val_le_iff.2 ht)

Depends on / 依赖: Multiset, Multiset.disjSum_mono, disjSum_mono, val_le_iff
-/
theorem disjSum_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s₁.disjSum t₁ subseteq s₂.disjSum t₂ :=
val_le_iff.1 Multiset.disjSum_mono (val_le_iff.2 hs) (val_le_iff.2 ht)

/--
theorem `disjSum_mono_left` / 定理 `disjSum_mono_left`

English:
theorem disjSum_mono_left
  given: (t : Finset β)
  statement: Monotone fun s : Finset α => s.disjSum t
  proof: fun _ _ hs => disjSum_mono hs Subset.rfl

中文:
定理 disjSum_mono_left
  条件: (t : Finset β)
  结论: Monotone fun s : Finset α => s.disjSum t
  证明: fun _ _ hs => disjSum_mono hs Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, disjSum_mono
-/
theorem disjSum_mono_left (t : Finset β) : Monotone fun s : Finset α => s.disjSum t :=
  fun _ _ hs => disjSum_mono hs Subset.rfl

/--
theorem `disjSum_mono_right` / 定理 `disjSum_mono_right`

English:
theorem disjSum_mono_right
  given: (s : Finset α)
  statement: Monotone (s.disjSum : Finset β -> Finset (α oplus β))
  proof: fun _ _ => disjSum_mono Subset.rfl

中文:
定理 disjSum_mono_right
  条件: (s : Finset α)
  结论: Monotone (s.disjSum : Finset β -> Finset (α oplus β))
  证明: fun _ _ => disjSum_mono Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, disjSum_mono
-/
theorem disjSum_mono_right (s : Finset α) : Monotone (s.disjSum : Finset β -> Finset (α oplus β)) :=
  fun _ _ => disjSum_mono Subset.rfl

/--
theorem `disjSum_ssubset_disjSum_of_ssubset_of_subset` / 定理 `disjSum_ssubset_disjSum_of_ssubset_of_subset`

English:
theorem disjSum_ssubset_disjSum_of_ssubset_of_subset
  given: (hs : s₁ ⊂ s₂) (ht : t₁ subseteq t₂)
  proof: val_lt_iff.1 disjSum_lt_disjSum_of_lt_of_le (val_lt_iff.2 hs) (val_le_iff.2 ht)

中文:
定理 disjSum_ssubset_disjSum_of_ssubset_of_subset
  条件: (hs : s₁ ⊂ s₂) (ht : t₁ subseteq t₂)
  证明: val_lt_iff.1 disjSum_lt_disjSum_of_lt_of_le (val_lt_iff.2 hs) (val_le_iff.2 ht)

Depends on / 依赖: disjSum_lt_disjSum_of_lt_of_le, val_le_iff, val_lt_iff
-/
theorem disjSum_ssubset_disjSum_of_ssubset_of_subset (hs : s₁ ⊂ s₂) (ht : t₁ subseteq t₂) :
    s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
val_lt_iff.1 disjSum_lt_disjSum_of_lt_of_le (val_lt_iff.2 hs) (val_le_iff.2 ht)

/--
theorem `disjSum_ssubset_disjSum_of_subset_of_ssubset` / 定理 `disjSum_ssubset_disjSum_of_subset_of_ssubset`

English:
theorem disjSum_ssubset_disjSum_of_subset_of_ssubset
  given: (hs : s₁ subseteq s₂) (ht : t₁ ⊂ t₂)
  proof: val_lt_iff.1 disjSum_lt_disjSum_of_le_of_lt (val_le_iff.2 hs) (val_lt_iff.2 ht)

中文:
定理 disjSum_ssubset_disjSum_of_subset_of_ssubset
  条件: (hs : s₁ subseteq s₂) (ht : t₁ ⊂ t₂)
  证明: val_lt_iff.1 disjSum_lt_disjSum_of_le_of_lt (val_le_iff.2 hs) (val_lt_iff.2 ht)

Depends on / 依赖: disjSum_lt_disjSum_of_le_of_lt, val_le_iff, val_lt_iff
-/
theorem disjSum_ssubset_disjSum_of_subset_of_ssubset (hs : s₁ subseteq s₂) (ht : t₁ ⊂ t₂) :
    s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
val_lt_iff.1 disjSum_lt_disjSum_of_le_of_lt (val_le_iff.2 hs) (val_lt_iff.2 ht)

/--
theorem `disjSum_strictMono_left` / 定理 `disjSum_strictMono_left`

English:
theorem disjSum_strictMono_left
  given: (t : Finset β)
  statement: StrictMono fun s : Finset α => s.disjSum t
  proof: fun _ _ hs => disjSum_ssubset_disjSum_of_ssubset_of_subset hs Subset.rfl

中文:
定理 disjSum_strictMono_left
  条件: (t : Finset β)
  结论: StrictMono fun s : Finset α => s.disjSum t
  证明: fun _ _ hs => disjSum_ssubset_disjSum_of_ssubset_of_subset hs Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, disjSum_ssubset_disjSum_of_ssubset_of_subset
-/
theorem disjSum_strictMono_left (t : Finset β) : StrictMono fun s : Finset α => s.disjSum t :=
  fun _ _ hs => disjSum_ssubset_disjSum_of_ssubset_of_subset hs Subset.rfl

/--
theorem `disjSum_strictMono_right` / 定理 `disjSum_strictMono_right`

English:
theorem disjSum_strictMono_right
  given: (s : Finset α)
  proof: fun _ _ =>
  disjSum_ssubset_disjSum_of_subset_of_ssubset Subset.rfl

中文:
定理 disjSum_strictMono_right
  条件: (s : Finset α)
  证明: fun _ _ =>
  disjSum_ssubset_disjSum_of_subset_of_ssubset Subset.rfl
-/
theorem disjSum_strictMono_right (s : Finset α) :
    StrictMono (s.disjSum : Finset β -> Finset (α oplus β)) := fun _ _ =>
  disjSum_ssubset_disjSum_of_subset_of_ssubset Subset.rfl

/--
lemma `disjSum_inj` / 引理 `disjSum_inj`

English:
lemma disjSum_inj
  given: {α β : Type*} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β}
  proof: by
  simp [Finset.ext_iff]

中文:
引理 disjSum_inj
  条件: {α β : 类型} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β}
  证明: by
  simp [Finset.ext_iff]
-/
@[simp] lemma disjSum_inj {α β : Type*} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} :
    s₁.disjSum t₁ = s₂.disjSum t₂ ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp [Finset.ext_iff]

/--
lemma `Injective2_disjSum` / 引理 `Injective2_disjSum`

English:
lemma Injective2_disjSum
  given: {α β : Type*}
  statement: Function.Injective2 (@disjSum α β)
  proof: fun _ _ _ _ => by simp [Finset.ext_iff]

中文:
引理 Injective2_disjSum
  条件: {α β : 类型}
  结论: Function.Injective2 (@disjSum α β)
  证明: fun _ _ _ _ => by simp [Finset.ext_iff]

Depends on / 依赖: Finset, Finset.ext_iff, ext_iff
-/
lemma Injective2_disjSum {α β : Type*} : Function.Injective2 (@disjSum α β) :=
  fun _ _ _ _ => by simp [Finset.ext_iff]

/--
Definition of `toLeft` / `toLeft` 的定义

English:
definition toLeft
  signature: (u : Finset (α oplus β))
  body: u.filterMap (Sum.elim some fun _ => none) (by clear x; aesop)

中文:
定义 toLeft
  签名: (u : Finset (α oplus β))
  定义体: u.filterMap (Sum.elim some fun _ => none) (by clear x; aesop)

Depends on / 依赖: Sum.elim, filterMap, u.filterMap
-/
def toLeft (u : Finset (α oplus β)) : Finset α :=
  u.filterMap (Sum.elim some fun _ => none) (by clear x; aesop)

/--
Definition of `toRight` / `toRight` 的定义

English:
definition toRight
  signature: (u : Finset (α oplus β))
  body: u.filterMap (Sum.elim (fun _ => none) some) (by clear x; aesop)

中文:
定义 toRight
  签名: (u : Finset (α oplus β))
  定义体: u.filterMap (Sum.elim (fun _ => none) some) (by clear x; aesop)

Depends on / 依赖: Sum.elim, filterMap, u.filterMap
-/
def toRight (u : Finset (α oplus β)) : Finset β :=
  u.filterMap (Sum.elim (fun _ => none) some) (by clear x; aesop)

variable {u v : Finset (α oplus β)} {a : α} {b : β}

/--
lemma `mem_toLeft` / 引理 `mem_toLeft`

English:
lemma mem_toLeft
  statement: a in u.toLeft ↔ .inl a in u
  proof: by simp [toLeft]

中文:
引理 mem_toLeft
  结论: a in u.toLeft ↔ .inl a in u
  证明: by simp [toLeft]
-/
@[simp] lemma mem_toLeft : a in u.toLeft ↔ .inl a in u := by simp [toLeft]
/--
lemma `mem_toRight` / 引理 `mem_toRight`

English:
lemma mem_toRight
  statement: b in u.toRight ↔ .inr b in u
  proof: by simp [toRight]

@[gcongr]

中文:
引理 mem_toRight
  结论: b in u.toRight ↔ .inr b in u
  证明: by simp [toRight]

@[gcongr]
-/
@[simp] lemma mem_toRight : b in u.toRight ↔ .inr b in u := by simp [toRight]

@[gcongr]
/--
lemma `toLeft_subset_toLeft` / 引理 `toLeft_subset_toLeft`

English:
lemma toLeft_subset_toLeft
  statement: u subseteq v -> u.toLeft subseteq v.toLeft
  proof: fun h _ => by simpa only [mem_toLeft] using @h _

@[gcongr]

中文:
引理 toLeft_subset_toLeft
  结论: u subseteq v -> u.toLeft subseteq v.toLeft
  证明: fun h _ => by simpa only [mem_toLeft] using @h _

@[gcongr]

Depends on / 依赖: mem_toLeft
-/
lemma toLeft_subset_toLeft : u subseteq v -> u.toLeft subseteq v.toLeft :=
  fun h _ => by simpa only [mem_toLeft] using @h _

@[gcongr]
/--
lemma `toRight_subset_toRight` / 引理 `toRight_subset_toRight`

English:
lemma toRight_subset_toRight
  statement: u subseteq v -> u.toRight subseteq v.toRight
  proof: fun h _ => by simpa only [mem_toRight] using @h _

中文:
引理 toRight_subset_toRight
  结论: u subseteq v -> u.toRight subseteq v.toRight
  证明: fun h _ => by simpa only [mem_toRight] using @h _

Depends on / 依赖: mem_toRight
-/
lemma toRight_subset_toRight : u subseteq v -> u.toRight subseteq v.toRight :=
  fun h _ => by simpa only [mem_toRight] using @h _

/--
lemma `toLeft_monotone` / 引理 `toLeft_monotone`

English:
lemma toLeft_monotone
  statement: Monotone (@toLeft α β)
  proof: fun _ _ => toLeft_subset_toLeft

中文:
引理 toLeft_monotone
  结论: Monotone (@toLeft α β)
  证明: fun _ _ => toLeft_subset_toLeft

Depends on / 依赖: toLeft_subset_toLeft
-/
lemma toLeft_monotone : Monotone (@toLeft α β) := fun _ _ => toLeft_subset_toLeft
/--
lemma `toRight_monotone` / 引理 `toRight_monotone`

English:
lemma toRight_monotone
  statement: Monotone (@toRight α β)
  proof: fun _ _ => toRight_subset_toRight

中文:
引理 toRight_monotone
  结论: Monotone (@toRight α β)
  证明: fun _ _ => toRight_subset_toRight

Depends on / 依赖: toRight_subset_toRight
-/
lemma toRight_monotone : Monotone (@toRight α β) := fun _ _ => toRight_subset_toRight

/--
lemma `toLeft_disjSum_toRight` / 引理 `toLeft_disjSum_toRight`

English:
lemma toLeft_disjSum_toRight
  statement: u.toLeft.disjSum u.toRight = u
  proof: by
  ext (x | x) <;> simp

中文:
引理 toLeft_disjSum_toRight
  结论: u.toLeft.disjSum u.toRight = u
  证明: by
  ext (x | x) <;> simp
-/
lemma toLeft_disjSum_toRight : u.toLeft.disjSum u.toRight = u := by
  ext (x | x) <;> simp

/--
lemma `card_toLeft_add_card_toRight` / 引理 `card_toLeft_add_card_toRight`

English:
lemma card_toLeft_add_card_toRight
  statement: #u.toLeft + #u.toRight = #u
  proof: by
  rw [← card_disjSum]; rw [toLeft_disjSum_toRight]

中文:
引理 card_toLeft_add_card_toRight
  结论: #u.toLeft + #u.toRight = #u
  证明: by
  rw [← card_disjSum]; rw [toLeft_disjSum_toRight]

Depends on / 依赖: card_disjSum, toLeft_disjSum_toRight
-/
lemma card_toLeft_add_card_toRight : #u.toLeft + #u.toRight = #u := by
  rw [← card_disjSum]; rw [toLeft_disjSum_toRight]

/--
lemma `card_toLeft_le` / 引理 `card_toLeft_le`

English:
lemma card_toLeft_le
  statement: #u.toLeft <= #u
  proof: (Nat.le_add_right _ _).trans_eq card_toLeft_add_card_toRight

中文:
引理 card_toLeft_le
  结论: #u.toLeft <= #u
  证明: (Nat.le_add_right _ _).trans_eq card_toLeft_add_card_toRight

Depends on / 依赖: Nat.le_add_right, card_toLeft_add_card_toRight, le_add_right, trans_eq
-/
lemma card_toLeft_le : #u.toLeft <= #u :=
  (Nat.le_add_right _ _).trans_eq card_toLeft_add_card_toRight

/--
lemma `card_toRight_le` / 引理 `card_toRight_le`

English:
lemma card_toRight_le
  statement: #u.toRight <= #u
  proof: (Nat.le_add_left _ _).trans_eq card_toLeft_add_card_toRight

中文:
引理 card_toRight_le
  结论: #u.toRight <= #u
  证明: (Nat.le_add_left _ _).trans_eq card_toLeft_add_card_toRight

Depends on / 依赖: Nat.le_add_left, card_toLeft_add_card_toRight, le_add_left, trans_eq
-/
lemma card_toRight_le : #u.toRight <= #u :=
  (Nat.le_add_left _ _).trans_eq card_toLeft_add_card_toRight

/--
lemma `toLeft_disjSum` / 引理 `toLeft_disjSum`

English:
lemma toLeft_disjSum
  statement: (s.disjSum t).toLeft = s
  proof: by ext x; simp

中文:
引理 toLeft_disjSum
  结论: (s.disjSum t).toLeft = s
  证明: by ext x; simp
-/
@[simp] lemma toLeft_disjSum : (s.disjSum t).toLeft = s := by ext x; simp

/--
lemma `toRight_disjSum` / 引理 `toRight_disjSum`

English:
lemma toRight_disjSum
  statement: (s.disjSum t).toRight = t
  proof: by ext x; simp

中文:
引理 toRight_disjSum
  结论: (s.disjSum t).toRight = t
  证明: by ext x; simp
-/
@[simp] lemma toRight_disjSum : (s.disjSum t).toRight = t := by ext x; simp

/--
lemma `disjSum_eq_iff` / 引理 `disjSum_eq_iff`

English:
lemma disjSum_eq_iff
  statement: s.disjSum t = u ↔ s = u.toLeft ∧ t = u.toRight
  proof: ⟨fun h => by simp [← h], fun h => by simp [h, toLeft_disjSum_toRight]⟩

中文:
引理 disjSum_eq_iff
  结论: s.disjSum t = u ↔ s = u.toLeft ∧ t = u.toRight
  证明: ⟨fun h => by simp [← h], fun h => by simp [h, toLeft_disjSum_toRight]⟩

Depends on / 依赖: toLeft_disjSum_toRight
-/
lemma disjSum_eq_iff : s.disjSum t = u ↔ s = u.toLeft ∧ t = u.toRight :=
  ⟨fun h => by simp [← h], fun h => by simp [h, toLeft_disjSum_toRight]⟩

/--
lemma `eq_disjSum_iff` / 引理 `eq_disjSum_iff`

English:
lemma eq_disjSum_iff
  statement: u = s.disjSum t ↔ u.toLeft = s ∧ u.toRight = t
  proof: ⟨fun h => by simp [h], fun h => by simp [← h, toLeft_disjSum_toRight]⟩

中文:
引理 eq_disjSum_iff
  结论: u = s.disjSum t ↔ u.toLeft = s ∧ u.toRight = t
  证明: ⟨fun h => by simp [h], fun h => by simp [← h, toLeft_disjSum_toRight]⟩

Depends on / 依赖: toLeft_disjSum_toRight
-/
lemma eq_disjSum_iff : u = s.disjSum t ↔ u.toLeft = s ∧ u.toRight = t :=
  ⟨fun h => by simp [h], fun h => by simp [← h, toLeft_disjSum_toRight]⟩

/--
lemma `disjSum_subset` / 引理 `disjSum_subset`

English:
lemma disjSum_subset
  statement: s.disjSum t subseteq u ↔ s subseteq u.toLeft ∧ t subseteq u.toRight
  proof: by simp [subset_iff]

中文:
引理 disjSum_subset
  结论: s.disjSum t subseteq u ↔ s subseteq u.toLeft ∧ t subseteq u.toRight
  证明: by simp [subset_iff]

Depends on / 依赖: subset_iff
-/
lemma disjSum_subset : s.disjSum t subseteq u ↔ s subseteq u.toLeft ∧ t subseteq u.toRight := by simp [subset_iff]
/--
lemma `subset_disjSum` / 引理 `subset_disjSum`

English:
lemma subset_disjSum
  statement: u subseteq s.disjSum t ↔ u.toLeft subseteq s ∧ u.toRight subseteq t
  proof: by simp [subset_iff]

中文:
引理 subset_disjSum
  结论: u subseteq s.disjSum t ↔ u.toLeft subseteq s ∧ u.toRight subseteq t
  证明: by simp [subset_iff]

Depends on / 依赖: subset_iff
-/
lemma subset_disjSum : u subseteq s.disjSum t ↔ u.toLeft subseteq s ∧ u.toRight subseteq t := by simp [subset_iff]

/--
lemma `subset_map_inl` / 引理 `subset_map_inl`

English:
lemma subset_map_inl
  statement: u subseteq s.map .inl ↔ u.toLeft subseteq s ∧ u.toRight = ∅
  proof: by
  simp [← disjSum_empty, subset_disjSum]

中文:
引理 subset_map_inl
  结论: u subseteq s.map .inl ↔ u.toLeft subseteq s ∧ u.toRight = ∅
  证明: by
  simp [← disjSum_empty, subset_disjSum]

Depends on / 依赖: disjSum_empty, subset_disjSum
-/
lemma subset_map_inl : u subseteq s.map .inl ↔ u.toLeft subseteq s ∧ u.toRight = ∅ := by
  simp [← disjSum_empty, subset_disjSum]

/--
lemma `subset_map_inr` / 引理 `subset_map_inr`

English:
lemma subset_map_inr
  statement: u subseteq t.map .inr ↔ u.toLeft = ∅ ∧ u.toRight subseteq t
  proof: by
  simp [← empty_disjSum, subset_disjSum]

中文:
引理 subset_map_inr
  结论: u subseteq t.map .inr ↔ u.toLeft = ∅ ∧ u.toRight subseteq t
  证明: by
  simp [← empty_disjSum, subset_disjSum]

Depends on / 依赖: empty_disjSum, subset_disjSum
-/
lemma subset_map_inr : u subseteq t.map .inr ↔ u.toLeft = ∅ ∧ u.toRight subseteq t := by
  simp [← empty_disjSum, subset_disjSum]

/--
lemma `map_inl_subset_iff_subset_toLeft` / 引理 `map_inl_subset_iff_subset_toLeft`

English:
lemma map_inl_subset_iff_subset_toLeft
  statement: s.map .inl subseteq u ↔ s subseteq u.toLeft
  proof: by
  simp [← disjSum_empty, disjSum_subset]

中文:
引理 map_inl_subset_iff_subset_toLeft
  结论: s.map .inl subseteq u ↔ s subseteq u.toLeft
  证明: by
  simp [← disjSum_empty, disjSum_subset]

Depends on / 依赖: disjSum_empty, disjSum_subset
-/
lemma map_inl_subset_iff_subset_toLeft : s.map .inl subseteq u ↔ s subseteq u.toLeft := by
  simp [← disjSum_empty, disjSum_subset]

/--
lemma `map_inr_subset_iff_subset_toRight` / 引理 `map_inr_subset_iff_subset_toRight`

English:
lemma map_inr_subset_iff_subset_toRight
  statement: t.map .inr subseteq u ↔ t subseteq u.toRight
  proof: by
  simp [← empty_disjSum, disjSum_subset]

中文:
引理 map_inr_subset_iff_subset_toRight
  结论: t.map .inr subseteq u ↔ t subseteq u.toRight
  证明: by
  simp [← empty_disjSum, disjSum_subset]

Depends on / 依赖: disjSum_subset, empty_disjSum
-/
lemma map_inr_subset_iff_subset_toRight : t.map .inr subseteq u ↔ t subseteq u.toRight := by
  simp [← empty_disjSum, disjSum_subset]

/--
lemma `gc_map_inl_toLeft` / 引理 `gc_map_inl_toLeft`

English:
lemma gc_map_inl_toLeft
  statement: GaloisConnection (·.map (.inl : α ↪ α oplus β)) toLeft
  proof: fun _ _ => map_inl_subset_iff_subset_toLeft

中文:
引理 gc_map_inl_toLeft
  结论: GaloisConnection (·.map (.inl : α ↪ α oplus β)) toLeft
  证明: fun _ _ => map_inl_subset_iff_subset_toLeft

Depends on / 依赖: map_inl_subset_iff_subset_toLeft
-/
lemma gc_map_inl_toLeft : GaloisConnection (·.map (.inl : α ↪ α oplus β)) toLeft :=
  fun _ _ => map_inl_subset_iff_subset_toLeft

/--
lemma `gc_map_inr_toRight` / 引理 `gc_map_inr_toRight`

English:
lemma gc_map_inr_toRight
  statement: GaloisConnection (·.map (.inr : β ↪ α oplus β)) toRight
  proof: fun _ _ => map_inr_subset_iff_subset_toRight

中文:
引理 gc_map_inr_toRight
  结论: GaloisConnection (·.map (.inr : β ↪ α oplus β)) toRight
  证明: fun _ _ => map_inr_subset_iff_subset_toRight

Depends on / 依赖: map_inr_subset_iff_subset_toRight
-/
lemma gc_map_inr_toRight : GaloisConnection (·.map (.inr : β ↪ α oplus β)) toRight :=
  fun _ _ => map_inr_subset_iff_subset_toRight

/--
lemma `toLeft_map_sumComm` / 引理 `toLeft_map_sumComm`

English:
lemma toLeft_map_sumComm
  statement: (u.map (Equiv.sumComm _ _).toEmbedding).toLeft = u.toRight
  proof: by
  ext x; simp

中文:
引理 toLeft_map_sumComm
  结论: (u.map (Equiv.sumComm _ _).toEmbedding).toLeft = u.toRight
  证明: by
  ext x; simp
-/
@[simp] lemma toLeft_map_sumComm : (u.map (Equiv.sumComm _ _).toEmbedding).toLeft = u.toRight := by
  ext x; simp

/--
lemma `toRight_map_sumComm` / 引理 `toRight_map_sumComm`

English:
lemma toRight_map_sumComm
  statement: (u.map (Equiv.sumComm _ _).toEmbedding).toRight = u.toLeft
  proof: by
  ext x; simp

中文:
引理 toRight_map_sumComm
  结论: (u.map (Equiv.sumComm _ _).toEmbedding).toRight = u.toLeft
  证明: by
  ext x; simp
-/
@[simp] lemma toRight_map_sumComm : (u.map (Equiv.sumComm _ _).toEmbedding).toRight = u.toLeft := by
  ext x; simp

/--
lemma `toLeft_cons_inl` / 引理 `toLeft_cons_inl`

English:
lemma toLeft_cons_inl
  given: (ha)
  proof: by ext y; simp

中文:
引理 toLeft_cons_inl
  条件: (ha)
  证明: by ext y; simp
-/
@[simp] lemma toLeft_cons_inl (ha) :
    (cons (inl a) u ha).toLeft = cons a u.toLeft (by simpa) := by ext y; simp
/--
lemma `toLeft_cons_inr` / 引理 `toLeft_cons_inr`

English:
lemma toLeft_cons_inr
  given: (hb)
  proof: by ext y; simp

中文:
引理 toLeft_cons_inr
  条件: (hb)
  证明: by ext y; simp
-/
@[simp] lemma toLeft_cons_inr (hb) :
    (cons (inr b) u hb).toLeft = u.toLeft := by ext y; simp
/--
lemma `toRight_cons_inl` / 引理 `toRight_cons_inl`

English:
lemma toRight_cons_inl
  given: (ha)
  proof: by ext y; simp

中文:
引理 toRight_cons_inl
  条件: (ha)
  证明: by ext y; simp
-/
@[simp] lemma toRight_cons_inl (ha) :
    (cons (inl a) u ha).toRight = u.toRight := by ext y; simp
/--
lemma `toRight_cons_inr` / 引理 `toRight_cons_inr`

English:
lemma toRight_cons_inr
  given: (hb)
  proof: by ext y; simp

中文:
引理 toRight_cons_inr
  条件: (hb)
  证明: by ext y; simp
-/
@[simp] lemma toRight_cons_inr (hb) :
    (cons (inr b) u hb).toRight = cons b u.toRight (by simpa) := by ext y; simp

section
variable [DecidableEq α] [DecidableEq β]

/--
lemma `toLeft_image_swap` / 引理 `toLeft_image_swap`

English:
lemma toLeft_image_swap
  statement: (u.image Sum.swap).toLeft = u.toRight
  proof: by
  ext x; simp

中文:
引理 toLeft_image_swap
  结论: (u.image Sum.swap).toLeft = u.toRight
  证明: by
  ext x; simp
-/
lemma toLeft_image_swap : (u.image Sum.swap).toLeft = u.toRight := by
  ext x; simp

/--
lemma `toRight_image_swap` / 引理 `toRight_image_swap`

English:
lemma toRight_image_swap
  statement: (u.image Sum.swap).toRight = u.toLeft
  proof: by
  ext x; simp

中文:
引理 toRight_image_swap
  结论: (u.image Sum.swap).toRight = u.toLeft
  证明: by
  ext x; simp
-/
lemma toRight_image_swap : (u.image Sum.swap).toRight = u.toLeft := by
  ext x; simp

/--
lemma `toLeft_insert_inl` / 引理 `toLeft_insert_inl`

English:
lemma toLeft_insert_inl
  statement: (insert (inl a) u).toLeft = insert a u.toLeft
  proof: by ext y; simp

中文:
引理 toLeft_insert_inl
  结论: (insert (inl a) u).toLeft = insert a u.toLeft
  证明: by ext y; simp
-/
@[simp] lemma toLeft_insert_inl : (insert (inl a) u).toLeft = insert a u.toLeft := by ext y; simp
/--
lemma `toLeft_insert_inr` / 引理 `toLeft_insert_inr`

English:
lemma toLeft_insert_inr
  statement: (insert (inr b) u).toLeft = u.toLeft
  proof: by ext y; simp

中文:
引理 toLeft_insert_inr
  结论: (insert (inr b) u).toLeft = u.toLeft
  证明: by ext y; simp
-/
@[simp] lemma toLeft_insert_inr : (insert (inr b) u).toLeft = u.toLeft := by ext y; simp
/--
lemma `toRight_insert_inl` / 引理 `toRight_insert_inl`

English:
lemma toRight_insert_inl
  statement: (insert (inl a) u).toRight = u.toRight
  proof: by ext y; simp

中文:
引理 toRight_insert_inl
  结论: (insert (inl a) u).toRight = u.toRight
  证明: by ext y; simp
-/
@[simp] lemma toRight_insert_inl : (insert (inl a) u).toRight = u.toRight := by ext y; simp
/--
lemma `toRight_insert_inr` / 引理 `toRight_insert_inr`

English:
lemma toRight_insert_inr
  statement: (insert (inr b) u).toRight = insert b u.toRight
  proof: by ext y; simp

中文:
引理 toRight_insert_inr
  结论: (insert (inr b) u).toRight = insert b u.toRight
  证明: by ext y; simp
-/
@[simp] lemma toRight_insert_inr : (insert (inr b) u).toRight = insert b u.toRight := by ext y; simp

/--
lemma `toLeft_inter` / 引理 `toLeft_inter`

English:
lemma toLeft_inter
  statement: (u inter v).toLeft = u.toLeft inter v.toLeft
  proof: by ext x; simp

中文:
引理 toLeft_inter
  结论: (u inter v).toLeft = u.toLeft inter v.toLeft
  证明: by ext x; simp
-/
lemma toLeft_inter : (u inter v).toLeft = u.toLeft inter v.toLeft := by ext x; simp
/--
lemma `toRight_inter` / 引理 `toRight_inter`

English:
lemma toRight_inter
  statement: (u inter v).toRight = u.toRight inter v.toRight
  proof: by ext x; simp

中文:
引理 toRight_inter
  结论: (u inter v).toRight = u.toRight inter v.toRight
  证明: by ext x; simp
-/
lemma toRight_inter : (u inter v).toRight = u.toRight inter v.toRight := by ext x; simp

/--
lemma `toLeft_union` / 引理 `toLeft_union`

English:
lemma toLeft_union
  statement: (u union v).toLeft = u.toLeft union v.toLeft
  proof: by ext x; simp

中文:
引理 toLeft_union
  结论: (u union v).toLeft = u.toLeft union v.toLeft
  证明: by ext x; simp
-/
lemma toLeft_union : (u union v).toLeft = u.toLeft union v.toLeft := by ext x; simp
/--
lemma `toRight_union` / 引理 `toRight_union`

English:
lemma toRight_union
  statement: (u union v).toRight = u.toRight union v.toRight
  proof: by ext x; simp

中文:
引理 toRight_union
  结论: (u union v).toRight = u.toRight union v.toRight
  证明: by ext x; simp
-/
lemma toRight_union : (u union v).toRight = u.toRight union v.toRight := by ext x; simp

/--
lemma `toLeft_sdiff` / 引理 `toLeft_sdiff`

English:
lemma toLeft_sdiff
  statement: (u \ v).toLeft = u.toLeft \ v.toLeft
  proof: by ext x; simp

中文:
引理 toLeft_sdiff
  结论: (u \ v).toLeft = u.toLeft \ v.toLeft
  证明: by ext x; simp
-/
lemma toLeft_sdiff : (u \ v).toLeft = u.toLeft \ v.toLeft := by ext x; simp
/--
lemma `toRight_sdiff` / 引理 `toRight_sdiff`

English:
lemma toRight_sdiff
  statement: (u \ v).toRight = u.toRight \ v.toRight
  proof: by ext x; simp

中文:
引理 toRight_sdiff
  结论: (u \ v).toRight = u.toRight \ v.toRight
  证明: by ext x; simp
-/
lemma toRight_sdiff : (u \ v).toRight = u.toRight \ v.toRight := by ext x; simp

end

set_option backward.isDefEq.respectTransparency false in
/-- Finsets on sum types are equivalent to pairs of finsets on each summand. -/
@[simps apply_fst apply_snd]
/--
Definition of `sumEquiv` / `sumEquiv` 的定义

English:
definition sumEquiv
  signature: {α β : Type*}
  body: (s.toLeft, s.toRight)
  invFun s := disjSum s.1 s.2
  left_inv s := toLeft_disjSum_toRight
  right_inv s := by simp
  map_rel_iff' := by simp [← Finset.coe_subset, Set.subset_def]

@[simp]

中文:
定义 sumEquiv
  签名: {α β : 类型}
  定义体: (s.toLeft, s.toRight)
  invFun s := disjSum s.1 s.2
  left_inv s := toLeft_disjSum_toRight
  right_inv s := by simp
  map_rel_iff' := by simp [← Finset.coe_subset, Set.subset_def]

@[simp]

Depends on / 依赖: s.toLeft, s.toRight, toLeft, toRight
-/
def sumEquiv {α β : Type*} : Finset (α oplus β) ≃o Finset α × Finset β where
  toFun s := (s.toLeft, s.toRight)
  invFun s := disjSum s.1 s.2
  left_inv s := toLeft_disjSum_toRight
  right_inv s := by simp
  map_rel_iff' := by simp [← Finset.coe_subset, Set.subset_def]

@[simp]
/--
lemma `sumEquiv_symm_apply` / 引理 `sumEquiv_symm_apply`

English:
lemma sumEquiv_symm_apply
  given: {α β : Type*} (s : Finset α × Finset β)
  proof: rfl

中文:
引理 sumEquiv_symm_apply
  条件: {α β : 类型} (s : Finset α × Finset β)
  证明: rfl
-/
lemma sumEquiv_symm_apply {α β : Type*} (s : Finset α × Finset β) :
    sumEquiv.symm s = disjSum s.1 s.2 := rfl

/--
theorem `map_disjSum` / 定理 `map_disjSum`

English:
theorem map_disjSum
  given: (f : α oplus β ↪ γ)
  proof: val_injective Multiset.map_disjSum _

中文:
定理 map_disjSum
  条件: (f : α oplus β ↪ γ)
  证明: val_injective Multiset.map_disjSum _

Depends on / 依赖: Multiset, Multiset.map_disjSum, map_disjSum, val_injective
-/
theorem map_disjSum (f : α oplus β ↪ γ) :
    (s.disjSum t).map f =
      (s.map (.trans .inl f)).disjUnion (t.map (.trans .inr f)) (by
        as_aux_lemma =>
          simpa only [← map_map]
            using (Finset.disjoint_map f).2 (disjoint_map_inl_map_inr _ _)) :=
val_injective Multiset.map_disjSum _

/--
lemma `fold_disjSum` / 引理 `fold_disjSum`

English:
lemma fold_disjSum
  statement: (s : Finset α) (t : Finset β) (f : α oplus β -> γ) (b₁ b₂ : γ) (op : γ -> γ -> γ)
  proof: by
  simp_rw [fold, disjSum, Multiset.map_disjSum, fold_add]

中文:
引理 fold_disjSum
  结论: (s : Finset α) (t : Finset β) (f : α oplus β -> γ) (b₁ b₂ : γ) (op : γ -> γ -> γ)
  证明: by
  simp_rw [fold, disjSum, Multiset.map_disjSum, fold_add]

Depends on / 依赖: Multiset, Multiset.map_disjSum, disjSum, fold_add, map_disjSum, simp_rw
-/
lemma fold_disjSum (s : Finset α) (t : Finset β) (f : α oplus β -> γ) (b₁ b₂ : γ) (op : γ -> γ -> γ)
    [Std.Commutative op] [Std.Associative op] :
    (s.disjSum t).fold op (op b₁ b₂) f =
      op (s.fold op b₁ (f <| .inl ·)) (t.fold op b₂ (f <| .inr ·)) := by
  simp_rw [fold, disjSum, Multiset.map_disjSum, fold_add]

end Finset
