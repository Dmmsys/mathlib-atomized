/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finset.Sups
public import Mathlib.Logic.Function.Iterate

/-!
# Shadows

This file defines shadows of a set family. The shadow of a set family is the set family of sets we
get by removing any element from any set of the original family. If one pictures `Finset α` as a big
hypercube (each dimension being membership of a given element), then taking the shadow corresponds
to projecting each finset down once in all available directions.

## Main definitions

* `Finset.shadow`: The shadow of a set family. Everything we can get by removing a new element from
  some set.
* `Finset.upShadow`: The upper shadow of a set family. Everything we can get by adding an element
  to some set.

## Notation

We define notation in scope `FinsetFamily`:
* `∂ 𝒜`: Shadow of `𝒜`.
* `∂⁺ 𝒜`: Upper shadow of `𝒜`.

We also maintain the convention that `a, b : α` are elements of the ground type, `s, t : Finset α`
are finsets, and `𝒜, ℬ : Finset (Finset α)` are finset families.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, set family
-/

@[expose] public section


open Finset Nat

variable {α : Type*}

namespace Finset

section Shadow

variable [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s t : Finset α} {a : α} {k r : Nat}

/--
Definition of `shadow` / `shadow` 的定义

English:
definition shadow
  signature: (𝒜 : Finset (Finset α))
  body: 𝒜.sup fun s => s.image (erase s)

@[inherit_doc] scoped[FinsetFamily] notation:max "∂" => Finset.shadow

中文:
定义 shadow
  签名: (𝒜 : Finset (Finset α))
  定义体: 𝒜.sup fun s => s.image (erase s)

@[inherit_doc] scoped[FinsetFamily] notation:max "∂" => Finset.shadow

Depends on / 依赖: s.image
-/
def shadow (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.sup fun s => s.image (erase s)

@[inherit_doc] scoped[FinsetFamily] notation:max "∂" => Finset.shadow

open FinsetFamily

/-- The shadow of the empty set is empty. -/
@[simp]
/--
theorem `shadow_empty` / 定理 `shadow_empty`

English:
theorem shadow_empty
  statement: ∂ (∅ : Finset (Finset α)) = ∅
  proof: rfl

中文:
定理 shadow_empty
  结论: ∂ (∅ : Finset (Finset α)) = ∅
  证明: rfl
-/
theorem shadow_empty : ∂ (∅ : Finset (Finset α)) = ∅ :=
  rfl

/--
lemma `shadow_iterate_empty` / 引理 `shadow_iterate_empty`

English:
lemma shadow_iterate_empty
  given: (k : Nat)
  statement: ∂^[k] (∅ : Finset (Finset α)) = ∅
  proof: by
  induction k <;> simp [*, shadow_empty]

@[simp]

中文:
引理 shadow_iterate_empty
  条件: (k : 自然数)
  结论: ∂^[k] (∅ : Finset (Finset α)) = ∅
  证明: by
  induction k <;> simp [*, shadow_empty]

@[simp]
-/
@[simp] lemma shadow_iterate_empty (k : Nat) : ∂^[k] (∅ : Finset (Finset α)) = ∅ := by
  induction k <;> simp [*, shadow_empty]

@[simp]
/--
theorem `shadow_singleton_empty` / 定理 `shadow_singleton_empty`

English:
theorem shadow_singleton_empty
  statement: ∂ ({∅} : Finset (Finset α)) = ∅
  proof: rfl

@[simp]

中文:
定理 shadow_singleton_empty
  结论: ∂ ({∅} : Finset (Finset α)) = ∅
  证明: rfl

@[simp]
-/
theorem shadow_singleton_empty : ∂ ({∅} : Finset (Finset α)) = ∅ :=
  rfl

@[simp]
/--
theorem `shadow_singleton` / 定理 `shadow_singleton`

English:
theorem shadow_singleton
  given: (a : α)
  statement: ∂ {{a}} = {∅}
  proof: by
  simp [shadow]

中文:
定理 shadow_singleton
  条件: (a : α)
  结论: ∂ {{a}} = {∅}
  证明: by
  simp [shadow]

Depends on / 依赖: shadow
-/
theorem shadow_singleton (a : α) : ∂ {{a}} = {∅} := by
  simp [shadow]

/-- The shadow is monotone. -/
@[gcongr, mono]
/--
theorem `shadow_monotone` / 定理 `shadow_monotone`

English:
theorem shadow_monotone
  statement: Monotone (shadow : Finset (Finset α) -> Finset (Finset α))
  proof: fun _ _ =>
  sup_mono

中文:
定理 shadow_monotone
  结论: Monotone (shadow : Finset (Finset α) -> Finset (Finset α))
  证明: fun _ _ =>
  sup_mono
-/
theorem shadow_monotone : Monotone (shadow : Finset (Finset α) -> Finset (Finset α)) := fun _ _ =>
  sup_mono

/--
lemma `shadow_mono` / 引理 `shadow_mono`

English:
lemma shadow_mono
  given: (h𝒜ℬ : 𝒜 subseteq ℬ)
  statement: ∂ 𝒜 subseteq ∂ ℬ
  proof: shadow_monotone h𝒜ℬ

中文:
引理 shadow_mono
  条件: (h𝒜ℬ : 𝒜 subseteq ℬ)
  结论: ∂ 𝒜 subseteq ∂ ℬ
  证明: shadow_monotone h𝒜ℬ
-/
@[gcongr] lemma shadow_mono (h𝒜ℬ : 𝒜 subseteq ℬ) : ∂ 𝒜 subseteq ∂ ℬ := shadow_monotone h𝒜ℬ

/--
lemma `mem_shadow_iff` / 引理 `mem_shadow_iff`

English:
lemma mem_shadow_iff
  statement: t in ∂ 𝒜 ↔ exists s in 𝒜, exists a in s, erase s a = t
  proof: by
  simp only [shadow, mem_sup, mem_image]

中文:
引理 mem_shadow_iff
  结论: t in ∂ 𝒜 ↔ 存在 s in 𝒜, 存在 a in s, erase s a = t
  证明: by
  simp only [shadow, mem_sup, mem_image]

Depends on / 依赖: mem_image, mem_sup, shadow
-/
lemma mem_shadow_iff : t in ∂ 𝒜 ↔ exists s in 𝒜, exists a in s, erase s a = t := by
  simp only [shadow, mem_sup, mem_image]

/--
theorem `erase_mem_shadow` / 定理 `erase_mem_shadow`

English:
theorem erase_mem_shadow
  given: (hs : s in 𝒜) (ha : a in s)
  statement: erase s a in ∂ 𝒜
  proof: mem_shadow_iff.2 ⟨s, hs, a, ha, rfl⟩

中文:
定理 erase_mem_shadow
  条件: (hs : s in 𝒜) (ha : a in s)
  结论: erase s a in ∂ 𝒜
  证明: mem_shadow_iff.2 ⟨s, hs, a, ha, rfl⟩

Depends on / 依赖: mem_shadow_iff
-/
theorem erase_mem_shadow (hs : s in 𝒜) (ha : a in s) : erase s a in ∂ 𝒜 :=
  mem_shadow_iff.2 ⟨s, hs, a, ha, rfl⟩

/--
lemma `mem_shadow_iff_exists_sdiff` / 引理 `mem_shadow_iff_exists_sdiff`

English:
lemma mem_shadow_iff_exists_sdiff
  statement: t in ∂ 𝒜 ↔ exists s in 𝒜, t subseteq s ∧ #(s \ t) = 1
  proof: by
  simp_rw [mem_shadow_iff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase]

中文:
引理 mem_shadow_iff_exists_sdiff
  结论: t in ∂ 𝒜 ↔ 存在 s in 𝒜, t subseteq s ∧ #(s \ t) = 1
  证明: by
  simp_rw [mem_shadow_iff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase]

Depends on / 依赖: covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase, mem_shadow_iff, simp_rw
-/
lemma mem_shadow_iff_exists_sdiff : t in ∂ 𝒜 ↔ exists s in 𝒜, t subseteq s ∧ #(s \ t) = 1 := by
  simp_rw [mem_shadow_iff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase]

/--
lemma `mem_shadow_iff_insert_mem` / 引理 `mem_shadow_iff_insert_mem`

English:
lemma mem_shadow_iff_insert_mem
  statement: t in ∂ 𝒜 ↔ exists a ∉ t, insert a t in 𝒜
  proof: by
  simp_rw [mem_shadow_iff_exists_sdiff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert]
  aesop

中文:
引理 mem_shadow_iff_insert_mem
  结论: t in ∂ 𝒜 ↔ 存在 a ∉ t, insert a t in 𝒜
  证明: by
  simp_rw [mem_shadow_iff_exists_sdiff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert]
  aesop

Depends on / 依赖: covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert, mem_shadow_iff_exists_sdiff, simp_rw
-/
lemma mem_shadow_iff_insert_mem : t in ∂ 𝒜 ↔ exists a ∉ t, insert a t in 𝒜 := by
  simp_rw [mem_shadow_iff_exists_sdiff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert]
  aesop

/--
lemma `mem_shadow_iff_exists_mem_card_add_one` / 引理 `mem_shadow_iff_exists_mem_card_add_one`

English:
lemma mem_shadow_iff_exists_mem_card_add_one
  statement: t in ∂ 𝒜 ↔ exists s in 𝒜, t subseteq s ∧ #s = #t + 1
  proof: by
refine mem_shadow_iff_exists_sdiff.trans exists_congr fun t => and_congr_right fun _ =>
    and_congr_right fun hst => ?_
  rw [card_sdiff_of_subset hst]; rw [tsub_eq_iff_eq_add_of_le]; rw [add_comm]
  exact card_mono hst

中文:
引理 mem_shadow_iff_exists_mem_card_add_one
  结论: t in ∂ 𝒜 ↔ 存在 s in 𝒜, t subseteq s ∧ #s = #t + 1
  证明: by
refine mem_shadow_iff_exists_sdiff.trans exists_congr fun t => and_congr_right fun _ =>
    and_congr_right fun hst => ?_
  rw [card_sdiff_of_subset hst]; rw [tsub_eq_iff_eq_add_of_le]; rw [add_comm]
  exact card_mono hst

Depends on / 依赖: add_comm, and_congr_right, card_mono, card_sdiff_of_subset, exists_congr, mem_shadow_iff_exists_sdiff, mem_shadow_iff_exists_sdiff.trans, tsub_eq_iff_eq_add_of_le
-/
lemma mem_shadow_iff_exists_mem_card_add_one : t in ∂ 𝒜 ↔ exists s in 𝒜, t subseteq s ∧ #s = #t + 1 := by
refine mem_shadow_iff_exists_sdiff.trans exists_congr fun t => and_congr_right fun _ =>
    and_congr_right fun hst => ?_
  rw [card_sdiff_of_subset hst]; rw [tsub_eq_iff_eq_add_of_le]; rw [add_comm]
  exact card_mono hst

/--
lemma `mem_shadow_iterate_iff_exists_card` / 引理 `mem_shadow_iterate_iff_exists_card`

English:
lemma mem_shadow_iterate_iff_exists_card
  proof: by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    simp only [mem_shadow_iff_insert_mem, ih, Function.iterate_succ_apply', card_eq_succ]
    aesop

中文:
引理 mem_shadow_iterate_iff_exists_card
  证明: by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    simp only [mem_shadow_iff_insert_mem, ih, Function.iterate_succ_apply', card_eq_succ]
    aesop

Depends on / 依赖: Function, Function.iterate_succ_apply, card_eq_succ, generalizing, iterate_succ_apply, mem_shadow_iff_insert_mem
-/
lemma mem_shadow_iterate_iff_exists_card :
    t in ∂^[k] 𝒜 ↔ exists u : Finset α, #u = k ∧ Disjoint t u ∧ t union u in 𝒜 := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    simp only [mem_shadow_iff_insert_mem, ih, Function.iterate_succ_apply', card_eq_succ]
    aesop

/--
lemma `mem_shadow_iterate_iff_exists_sdiff` / 引理 `mem_shadow_iterate_iff_exists_sdiff`

English:
lemma mem_shadow_iterate_iff_exists_sdiff
  statement: t in ∂^[k] 𝒜 ↔ exists s in 𝒜, t subseteq s ∧ #(s \ t) = k
  proof: by
  rw [mem_shadow_iterate_iff_exists_card]
  constructor
  · rintro ⟨u, rfl, htu, hsuA⟩
    exact ⟨_, hsuA, subset_union_left, by rw [union_sdiff_cancel_left htu]⟩
  · rintro ⟨s, hs, hts, rfl⟩
    refine ⟨s \ t, rfl, disjoint_sdiff, ?_⟩
    rwa [union_sdiff_self_eq_union, union_eq_right.2 hts]

中文:
引理 mem_shadow_iterate_iff_exists_sdiff
  结论: t in ∂^[k] 𝒜 ↔ 存在 s in 𝒜, t subseteq s ∧ #(s \ t) = k
  证明: by
  rw [mem_shadow_iterate_iff_exists_card]
  constructor
  · rintro ⟨u, rfl, htu, hsuA⟩
    exact ⟨_, hsuA, subset_union_left, by rw [union_sdiff_cancel_left htu]⟩
  · rintro ⟨s, hs, hts, rfl⟩
    refine ⟨s \ t, rfl, disjoint_sdiff, ?_⟩
    rwa [union_sdiff_self_eq_union, union_eq_right.2 hts]

Depends on / 依赖: disjoint_sdiff, mem_shadow_iterate_iff_exists_card, subset_union_left, union_eq_right, union_sdiff_cancel_left, union_sdiff_self_eq_union
-/
lemma mem_shadow_iterate_iff_exists_sdiff : t in ∂^[k] 𝒜 ↔ exists s in 𝒜, t subseteq s ∧ #(s \ t) = k := by
  rw [mem_shadow_iterate_iff_exists_card]
  constructor
  · rintro ⟨u, rfl, htu, hsuA⟩
    exact ⟨_, hsuA, subset_union_left, by rw [union_sdiff_cancel_left htu]⟩
  · rintro ⟨s, hs, hts, rfl⟩
    refine ⟨s \ t, rfl, disjoint_sdiff, ?_⟩
    rwa [union_sdiff_self_eq_union, union_eq_right.2 hts]

/--
lemma `mem_shadow_iterate_iff_exists_mem_card_add` / 引理 `mem_shadow_iterate_iff_exists_mem_card_add`

English:
lemma mem_shadow_iterate_iff_exists_mem_card_add
  proof: by
refine mem_shadow_iterate_iff_exists_sdiff.trans exists_congr fun t => and_congr_right fun _ =>
    and_congr_right fun hst => ?_
  rw [card_sdiff_of_subset hst]; rw [tsub_eq_iff_eq_add_of_le]; rw [add_comm]
  exact card_mono hst

中文:
引理 mem_shadow_iterate_iff_exists_mem_card_add
  证明: by
refine mem_shadow_iterate_iff_exists_sdiff.trans exists_congr fun t => and_congr_right fun _ =>
    and_congr_right fun hst => ?_
  rw [card_sdiff_of_subset hst]; rw [tsub_eq_iff_eq_add_of_le]; rw [add_comm]
  exact card_mono hst

Depends on / 依赖: add_comm, and_congr_right, card_mono, card_sdiff_of_subset, exists_congr, mem_shadow_iterate_iff_exists_sdiff, mem_shadow_iterate_iff_exists_sdiff.trans, tsub_eq_iff_eq_add_of_le
-/
lemma mem_shadow_iterate_iff_exists_mem_card_add :
    t in ∂^[k] 𝒜 ↔ exists s in 𝒜, t subseteq s ∧ #s = #t + k := by
refine mem_shadow_iterate_iff_exists_sdiff.trans exists_congr fun t => and_congr_right fun _ =>
    and_congr_right fun hst => ?_
  rw [card_sdiff_of_subset hst]; rw [tsub_eq_iff_eq_add_of_le]; rw [add_comm]
  exact card_mono hst

/--
theorem `_root_.Set.Sized.shadow` / 定理 `_root_.Set.Sized.shadow`

English:
theorem _root_.Set.Sized.shadow
  given: (h𝒜 : (𝒜 : Set (Finset α)).Sized r)
  proof: by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_shadow_iff.1 h
  rw [card_erase_of_mem hi]; rw [h𝒜 hA]

中文:
定理 _root_.Set.Sized.shadow
  条件: (h𝒜 : (𝒜 : Set (Finset α)).Sized r)
  证明: by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_shadow_iff.1 h
  rw [card_erase_of_mem hi]; rw [h𝒜 hA]
-/
protected theorem _root_.Set.Sized.shadow (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂ 𝒜 : Set (Finset α)).Sized (r - 1) := by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_shadow_iff.1 h
  rw [card_erase_of_mem hi]; rw [h𝒜 hA]

/--
lemma `_root_.Set.Sized.shadow_iterate` / 引理 `_root_.Set.Sized.shadow_iterate`

English:
lemma _root_.Set.Sized.shadow_iterate
  given: (h𝒜 : (𝒜 : Set (Finset α)).Sized r)
  proof: by
  simp_rw [Set.Sized, mem_coe, mem_shadow_iterate_iff_exists_sdiff]
  rintro t ⟨s, hs, hts, rfl⟩
  rw [card_sdiff_of_subset hts]; rw [← h𝒜 hs]; rw [Nat.sub_sub_self (card_le_card hts)]

中文:
引理 _root_.Set.Sized.shadow_iterate
  条件: (h𝒜 : (𝒜 : Set (Finset α)).Sized r)
  证明: by
  simp_rw [Set.Sized, mem_coe, mem_shadow_iterate_iff_exists_sdiff]
  rintro t ⟨s, hs, hts, rfl⟩
  rw [card_sdiff_of_subset hts]; rw [← h𝒜 hs]; rw [Nat.sub_sub_self (card_le_card hts)]

Depends on / 依赖: Nat.sub_sub_self, Set.Sized, card_le_card, card_sdiff_of_subset, mem_coe, mem_shadow_iterate_iff_exists_sdiff, simp_rw, sub_sub_self
-/
lemma _root_.Set.Sized.shadow_iterate (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂^[k] 𝒜 : Set (Finset α)).Sized (r - k) := by
  simp_rw [Set.Sized, mem_coe, mem_shadow_iterate_iff_exists_sdiff]
  rintro t ⟨s, hs, hts, rfl⟩
  rw [card_sdiff_of_subset hts]; rw [← h𝒜 hs]; rw [Nat.sub_sub_self (card_le_card hts)]

/--
theorem `sized_shadow_iff` / 定理 `sized_shadow_iff`

English:
theorem sized_shadow_iff
  given: (h : ∅ ∉ 𝒜)
  proof: by
  refine ⟨fun h𝒜 s hs => ?_, Set.Sized.shadow⟩
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 (ne_of_mem_of_not_mem hs h)
  rw [← h𝒜 (erase_mem_shadow hs ha)]; rw [card_erase_add_one ha]

中文:
定理 sized_shadow_iff
  条件: (h : ∅ ∉ 𝒜)
  证明: by
  refine ⟨fun h𝒜 s hs => ?_, Set.Sized.shadow⟩
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 (ne_of_mem_of_not_mem hs h)
  rw [← h𝒜 (erase_mem_shadow hs ha)]; rw [card_erase_add_one ha]

Depends on / 依赖: Set.Sized.shadow, card_erase_add_one, erase_mem_shadow, ne_of_mem_of_not_mem, nonempty_iff_ne_empty, shadow
-/
theorem sized_shadow_iff (h : ∅ ∉ 𝒜) :
    (∂ 𝒜 : Set (Finset α)).Sized r ↔ (𝒜 : Set (Finset α)).Sized (r + 1) := by
  refine ⟨fun h𝒜 s hs => ?_, Set.Sized.shadow⟩
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 (ne_of_mem_of_not_mem hs h)
  rw [← h𝒜 (erase_mem_shadow hs ha)]; rw [card_erase_add_one ha]

/--
lemma `exists_subset_of_mem_shadow` / 引理 `exists_subset_of_mem_shadow`

English:
lemma exists_subset_of_mem_shadow
  given: (hs : t in ∂ 𝒜)
  statement: exists s in 𝒜, t subseteq s
  proof: let ⟨t, ht, hst⟩ := mem_shadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hst.1⟩

中文:
引理 exists_subset_of_mem_shadow
  条件: (hs : t in ∂ 𝒜)
  结论: 存在 s in 𝒜, t subseteq s
  证明: let ⟨t, ht, hst⟩ := mem_shadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hst.1⟩

Depends on / 依赖: mem_shadow_iff_exists_mem_card_add_one
-/
lemma exists_subset_of_mem_shadow (hs : t in ∂ 𝒜) : exists s in 𝒜, t subseteq s :=
  let ⟨t, ht, hst⟩ := mem_shadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hst.1⟩

end Shadow

open FinsetFamily

section UpShadow

variable [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {s t : Finset α} {a : α} {k r : Nat}

/--
Definition of `upShadow` / `upShadow` 的定义

English:
definition upShadow
  signature: (𝒜 : Finset (Finset α))
  body: 𝒜.sup fun s => sᶜ.image fun a => insert a s

@[inherit_doc] scoped[FinsetFamily] notation:max "∂⁺ " => Finset.upShadow

中文:
定义 upShadow
  签名: (𝒜 : Finset (Finset α))
  定义体: 𝒜.sup fun s => sᶜ.image fun a => insert a s

@[inherit_doc] scoped[FinsetFamily] notation:max "∂⁺ " => Finset.upShadow

Depends on / 依赖: insert
-/
def upShadow (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.sup fun s => sᶜ.image fun a => insert a s

@[inherit_doc] scoped[FinsetFamily] notation:max "∂⁺ " => Finset.upShadow

/-- The upper shadow of the empty set is empty. -/
@[simp]
/--
theorem `upShadow_empty` / 定理 `upShadow_empty`

English:
theorem upShadow_empty
  statement: ∂⁺ (∅ : Finset (Finset α)) = ∅
  proof: rfl

中文:
定理 upShadow_empty
  结论: ∂⁺ (∅ : Finset (Finset α)) = ∅
  证明: rfl
-/
theorem upShadow_empty : ∂⁺ (∅ : Finset (Finset α)) = ∅ :=
  rfl

/-- The upper shadow is monotone. -/
@[gcongr, mono]
/--
theorem `upShadow_monotone` / 定理 `upShadow_monotone`

English:
theorem upShadow_monotone
  statement: Monotone (upShadow : Finset (Finset α) -> Finset (Finset α))
  proof: fun _ _ => sup_mono

中文:
定理 upShadow_monotone
  结论: Monotone (upShadow : Finset (Finset α) -> Finset (Finset α))
  证明: fun _ _ => sup_mono

Depends on / 依赖: sup_mono
-/
theorem upShadow_monotone : Monotone (upShadow : Finset (Finset α) -> Finset (Finset α)) :=
  fun _ _ => sup_mono

/--
lemma `mem_upShadow_iff` / 引理 `mem_upShadow_iff`

English:
lemma mem_upShadow_iff
  statement: t in ∂⁺ 𝒜 ↔ exists s in 𝒜, exists a ∉ s, insert a s = t
  proof: by
  simp_rw [upShadow, mem_sup, mem_image, mem_compl]

中文:
引理 mem_upShadow_iff
  结论: t in ∂⁺ 𝒜 ↔ 存在 s in 𝒜, 存在 a ∉ s, insert a s = t
  证明: by
  simp_rw [upShadow, mem_sup, mem_image, mem_compl]

Depends on / 依赖: mem_compl, mem_image, mem_sup, simp_rw, upShadow
-/
lemma mem_upShadow_iff : t in ∂⁺ 𝒜 ↔ exists s in 𝒜, exists a ∉ s, insert a s = t := by
  simp_rw [upShadow, mem_sup, mem_image, mem_compl]

/--
theorem `insert_mem_upShadow` / 定理 `insert_mem_upShadow`

English:
theorem insert_mem_upShadow
  given: (hs : s in 𝒜) (ha : a ∉ s)
  statement: insert a s in ∂⁺ 𝒜
  proof: mem_upShadow_iff.2 ⟨s, hs, a, ha, rfl⟩

中文:
定理 insert_mem_upShadow
  条件: (hs : s in 𝒜) (ha : a ∉ s)
  结论: insert a s in ∂⁺ 𝒜
  证明: mem_upShadow_iff.2 ⟨s, hs, a, ha, rfl⟩

Depends on / 依赖: mem_upShadow_iff
-/
theorem insert_mem_upShadow (hs : s in 𝒜) (ha : a ∉ s) : insert a s in ∂⁺ 𝒜 :=
  mem_upShadow_iff.2 ⟨s, hs, a, ha, rfl⟩

/--
lemma `mem_upShadow_iff_exists_sdiff` / 引理 `mem_upShadow_iff_exists_sdiff`

English:
lemma mem_upShadow_iff_exists_sdiff
  statement: t in ∂⁺ 𝒜 ↔ exists s in 𝒜, s subseteq t ∧ #(t \ s) = 1
  proof: by
  simp_rw [mem_upShadow_iff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert]

中文:
引理 mem_upShadow_iff_exists_sdiff
  结论: t in ∂⁺ 𝒜 ↔ 存在 s in 𝒜, s subseteq t ∧ #(t \ s) = 1
  证明: by
  simp_rw [mem_upShadow_iff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert]

Depends on / 依赖: covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert, mem_upShadow_iff, simp_rw
-/
lemma mem_upShadow_iff_exists_sdiff : t in ∂⁺ 𝒜 ↔ exists s in 𝒜, s subseteq t ∧ #(t \ s) = 1 := by
  simp_rw [mem_upShadow_iff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert]

/--
lemma `mem_upShadow_iff_erase_mem` / 引理 `mem_upShadow_iff_erase_mem`

English:
lemma mem_upShadow_iff_erase_mem
  statement: t in ∂⁺ 𝒜 ↔ exists a, a in t ∧ erase t a in 𝒜
  proof: by
  simp_rw [mem_upShadow_iff_exists_sdiff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase]
  aesop

中文:
引理 mem_upShadow_iff_erase_mem
  结论: t in ∂⁺ 𝒜 ↔ 存在 a, a in t ∧ erase t a in 𝒜
  证明: by
  simp_rw [mem_upShadow_iff_exists_sdiff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase]
  aesop

Depends on / 依赖: covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase, mem_upShadow_iff_exists_sdiff, simp_rw
-/
lemma mem_upShadow_iff_erase_mem : t in ∂⁺ 𝒜 ↔ exists a, a in t ∧ erase t a in 𝒜 := by
  simp_rw [mem_upShadow_iff_exists_sdiff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase]
  aesop

/--
lemma `mem_upShadow_iff_exists_mem_card_add_one` / 引理 `mem_upShadow_iff_exists_mem_card_add_one`

English:
lemma mem_upShadow_iff_exists_mem_card_add_one
  proof: by
refine mem_upShadow_iff_exists_sdiff.trans exists_congr fun t => and_congr_right fun _ =>
    and_congr_right fun hst => ?_
  rw [card_sdiff_of_subset hst]; rw [tsub_eq_iff_eq_add_of_le]; rw [add_comm]
  exact card_mono hst

中文:
引理 mem_upShadow_iff_exists_mem_card_add_one
  证明: by
refine mem_upShadow_iff_exists_sdiff.trans exists_congr fun t => and_congr_right fun _ =>
    and_congr_right fun hst => ?_
  rw [card_sdiff_of_subset hst]; rw [tsub_eq_iff_eq_add_of_le]; rw [add_comm]
  exact card_mono hst

Depends on / 依赖: add_comm, and_congr_right, card_mono, card_sdiff_of_subset, exists_congr, mem_upShadow_iff_exists_sdiff, mem_upShadow_iff_exists_sdiff.trans, tsub_eq_iff_eq_add_of_le
-/
lemma mem_upShadow_iff_exists_mem_card_add_one :
    t in ∂⁺ 𝒜 ↔ exists s in 𝒜, s subseteq t ∧ #t = #s + 1 := by
refine mem_upShadow_iff_exists_sdiff.trans exists_congr fun t => and_congr_right fun _ =>
    and_congr_right fun hst => ?_
  rw [card_sdiff_of_subset hst]; rw [tsub_eq_iff_eq_add_of_le]; rw [add_comm]
  exact card_mono hst

/--
lemma `mem_upShadow_iterate_iff_exists_card` / 引理 `mem_upShadow_iterate_iff_exists_card`

English:
lemma mem_upShadow_iterate_iff_exists_card
  proof: by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    simp only [mem_upShadow_iff_erase_mem, ih, Function.iterate_succ_apply', card_eq_succ,
      subset_erase, erase_sdiff_comm, ← sdiff_insert]
    constructor
    · rintro ⟨a, hat, u, rfl, ⟨hut, hau⟩, htu⟩
      exact ⟨_, ⟨_, _

中文:
引理 mem_upShadow_iterate_iff_exists_card
  证明: by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    simp only [mem_upShadow_iff_erase_mem, ih, Function.iterate_succ_apply', card_eq_succ,
      subset_erase, erase_sdiff_comm, ← sdiff_insert]
    constructor
    · rintro ⟨a, hat, u, rfl, ⟨hut, hau⟩, htu⟩
      exact ⟨_, ⟨_, _

Depends on / 依赖: Function, Function.iterate_succ_apply, card_eq_succ, erase_sdiff_comm, generalizing, insert_subset, insert_subset_iff, iterate_succ_apply, mem_upShadow_iff_erase_mem, sdiff_insert, subset_erase
-/
lemma mem_upShadow_iterate_iff_exists_card :
    t in ∂⁺^[k] 𝒜 ↔ exists u : Finset α, #u = k ∧ u subseteq t ∧ t \ u in 𝒜 := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    simp only [mem_upShadow_iff_erase_mem, ih, Function.iterate_succ_apply', card_eq_succ,
      subset_erase, erase_sdiff_comm, ← sdiff_insert]
    constructor
    · rintro ⟨a, hat, u, rfl, ⟨hut, hau⟩, htu⟩
      exact ⟨_, ⟨_, _, hau, rfl, rfl⟩, insert_subset hat hut, htu⟩
    · rintro ⟨_, ⟨a, u, hau, rfl, rfl⟩, hut, htu⟩
      rw [insert_subset_iff] at hut
      exact ⟨a, hut.1, _, rfl, ⟨hut.2, hau⟩, htu⟩

/--
lemma `mem_upShadow_iterate_iff_exists_sdiff` / 引理 `mem_upShadow_iterate_iff_exists_sdiff`

English:
lemma mem_upShadow_iterate_iff_exists_sdiff
  statement: t in ∂⁺^[k] 𝒜 ↔ exists s in 𝒜, s subseteq t ∧ #(t \ s) = k
  proof: by
  rw [mem_upShadow_iterate_iff_exists_card]
  constructor
  · rintro ⟨u, rfl, hut, htu⟩
    exact ⟨_, htu, sdiff_subset, by rw [sdiff_sdiff_eq_self hut]⟩
  · rintro ⟨s, hs, hst, rfl⟩
    exact ⟨_, rfl, sdiff_subset, by rwa [sdiff_sdiff_eq_self hst]⟩

中文:
引理 mem_upShadow_iterate_iff_exists_sdiff
  结论: t in ∂⁺^[k] 𝒜 ↔ 存在 s in 𝒜, s subseteq t ∧ #(t \ s) = k
  证明: by
  rw [mem_upShadow_iterate_iff_exists_card]
  constructor
  · rintro ⟨u, rfl, hut, htu⟩
    exact ⟨_, htu, sdiff_subset, by rw [sdiff_sdiff_eq_self hut]⟩
  · rintro ⟨s, hs, hst, rfl⟩
    exact ⟨_, rfl, sdiff_subset, by rwa [sdiff_sdiff_eq_self hst]⟩

Depends on / 依赖: mem_upShadow_iterate_iff_exists_card, sdiff_sdiff_eq_self, sdiff_subset
-/
lemma mem_upShadow_iterate_iff_exists_sdiff : t in ∂⁺^[k] 𝒜 ↔ exists s in 𝒜, s subseteq t ∧ #(t \ s) = k := by
  rw [mem_upShadow_iterate_iff_exists_card]
  constructor
  · rintro ⟨u, rfl, hut, htu⟩
    exact ⟨_, htu, sdiff_subset, by rw [sdiff_sdiff_eq_self hut]⟩
  · rintro ⟨s, hs, hst, rfl⟩
    exact ⟨_, rfl, sdiff_subset, by rwa [sdiff_sdiff_eq_self hst]⟩

/--
lemma `mem_upShadow_iterate_iff_exists_mem_card_add` / 引理 `mem_upShadow_iterate_iff_exists_mem_card_add`

English:
lemma mem_upShadow_iterate_iff_exists_mem_card_add
  proof: by
refine mem_upShadow_iterate_iff_exists_sdiff.trans exists_congr fun t => and_congr_right fun _ =>
    and_congr_right fun hst => ?_
  rw [card_sdiff_of_subset hst]; rw [tsub_eq_iff_eq_add_of_le]; rw [add_comm]
  exact card_mono hst

中文:
引理 mem_upShadow_iterate_iff_exists_mem_card_add
  证明: by
refine mem_upShadow_iterate_iff_exists_sdiff.trans exists_congr fun t => and_congr_right fun _ =>
    and_congr_right fun hst => ?_
  rw [card_sdiff_of_subset hst]; rw [tsub_eq_iff_eq_add_of_le]; rw [add_comm]
  exact card_mono hst

Depends on / 依赖: add_comm, and_congr_right, card_mono, card_sdiff_of_subset, exists_congr, mem_upShadow_iterate_iff_exists_sdiff, mem_upShadow_iterate_iff_exists_sdiff.trans, tsub_eq_iff_eq_add_of_le
-/
lemma mem_upShadow_iterate_iff_exists_mem_card_add :
    t in ∂⁺^[k] 𝒜 ↔ exists s in 𝒜, s subseteq t ∧ #t = #s + k := by
refine mem_upShadow_iterate_iff_exists_sdiff.trans exists_congr fun t => and_congr_right fun _ =>
    and_congr_right fun hst => ?_
  rw [card_sdiff_of_subset hst]; rw [tsub_eq_iff_eq_add_of_le]; rw [add_comm]
  exact card_mono hst

/--
lemma `_root_.Set.Sized.upShadow` / 引理 `_root_.Set.Sized.upShadow`

English:
lemma _root_.Set.Sized.upShadow
  given: (h𝒜 : (𝒜 : Set (Finset α)).Sized r)
  proof: by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_upShadow_iff.1 h
  rw [card_insert_of_notMem hi]; rw [h𝒜 hA]

中文:
引理 _root_.Set.Sized.upShadow
  条件: (h𝒜 : (𝒜 : Set (Finset α)).Sized r)
  证明: by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_upShadow_iff.1 h
  rw [card_insert_of_notMem hi]; rw [h𝒜 hA]
-/
protected lemma _root_.Set.Sized.upShadow (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂⁺ 𝒜 : Set (Finset α)).Sized (r + 1) := by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_upShadow_iff.1 h
  rw [card_insert_of_notMem hi]; rw [h𝒜 hA]

/--
theorem `exists_subset_of_mem_upShadow` / 定理 `exists_subset_of_mem_upShadow`

English:
theorem exists_subset_of_mem_upShadow
  given: (hs : s in ∂⁺ 𝒜)
  statement: exists t in 𝒜, t subseteq s
  proof: let ⟨t, ht, hts, _⟩ := mem_upShadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hts⟩

中文:
定理 exists_subset_of_mem_upShadow
  条件: (hs : s in ∂⁺ 𝒜)
  结论: 存在 t in 𝒜, t subseteq s
  证明: let ⟨t, ht, hts, _⟩ := mem_upShadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hts⟩

Depends on / 依赖: mem_upShadow_iff_exists_mem_card_add_one
-/
theorem exists_subset_of_mem_upShadow (hs : s in ∂⁺ 𝒜) : exists t in 𝒜, t subseteq s :=
  let ⟨t, ht, hts, _⟩ := mem_upShadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hts⟩

/--
theorem `mem_upShadow_iff_exists_mem_card_add` / 定理 `mem_upShadow_iff_exists_mem_card_add`

English:
theorem mem_upShadow_iff_exists_mem_card_add
  proof: by
  induction k generalizing 𝒜 s with
  | zero =>
    refine ⟨fun hs => ⟨s, hs, Subset.refl _, rfl⟩, ?_⟩
    rintro ⟨t, ht, hst, hcard⟩
    rwa [← eq_of_subset_of_card_le hst hcard.ge]
  | succ k ih =>
    simp only [Function.comp_apply, Function.iterate_succ]
    refine ih.trans ?_
    clear ih
  

中文:
定理 mem_upShadow_iff_exists_mem_card_add
  证明: by
  induction k generalizing 𝒜 s with
  | zero =>
    refine ⟨fun hs => ⟨s, hs, Subset.refl _, rfl⟩, ?_⟩
    rintro ⟨t, ht, hst, hcard⟩
    rwa [← eq_of_subset_of_card_le hst hcard.ge]
  | succ k ih =>
    simp only [Function.comp_apply, Function.iterate_succ]
    refine ih.trans ?_
    clear ih
  

Depends on / 依赖: Function, Function.comp_apply, Function.iterate_succ, Subset, Subset.refl, add_right_comm, comp_apply, eq_of_subset_of_card_le, generalizing, hcard.ge, hcardst, hcardtu, hut.trans, ih.trans, iterate_succ, mem_upShadow_iff_exists_mem_card_add_one
-/
theorem mem_upShadow_iff_exists_mem_card_add :
    s in ∂⁺ ^[k] 𝒜 ↔ exists t in 𝒜, t subseteq s ∧ #t + k = #s := by
  induction k generalizing 𝒜 s with
  | zero =>
    refine ⟨fun hs => ⟨s, hs, Subset.refl _, rfl⟩, ?_⟩
    rintro ⟨t, ht, hst, hcard⟩
    rwa [← eq_of_subset_of_card_le hst hcard.ge]
  | succ k ih =>
    simp only [Function.comp_apply, Function.iterate_succ]
    refine ih.trans ?_
    clear ih
    constructor
    · rintro ⟨t, ht, hts, hcardst⟩
      obtain ⟨u, hu, hut, hcardtu⟩ := mem_upShadow_iff_exists_mem_card_add_one.1 ht
      refine ⟨u, hu, hut.trans hts, ?_⟩
      rw [← hcardst]; rw [hcardtu]; rw [add_right_comm]
      rfl
    · rintro ⟨t, ht, hts, hcard⟩
      obtain ⟨u, htu, hus, hu⟩ := Finset.exists_subsuperset_card_eq hts (Nat.le_add_right _ 1)
        (by lia)
      refine ⟨u, mem_upShadow_iff_exists_mem_card_add_one.2 ⟨t, ht, htu, hu⟩, hus, ?_⟩
      rw [hu]; rw [← hcard]; rw [add_right_comm]
      rfl

/--
lemma `shadow_compls` / 引理 `shadow_compls`

English:
lemma shadow_compls
  statement: ∂ 𝒜ᶜˢ = (∂⁺ 𝒜)ᶜˢ
  proof: by
  ext s
  simp only [mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [← compl_involutive.eq_iff]

中文:
引理 shadow_compls
  结论: ∂ 𝒜ᶜˢ = (∂⁺ 𝒜)ᶜˢ
  证明: by
  ext s
  simp only [mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [← compl_involutive.eq_iff]
-/
@[simp] lemma shadow_compls : ∂ 𝒜ᶜˢ = (∂⁺ 𝒜)ᶜˢ := by
  ext s
  simp only [mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [← compl_involutive.eq_iff]

/--
lemma `upShadow_compls` / 引理 `upShadow_compls`

English:
lemma upShadow_compls
  statement: ∂⁺ 𝒜ᶜˢ = (∂ 𝒜)ᶜˢ
  proof: by
  ext s
  simp only [mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [← compl_involutive.eq_iff]

中文:
引理 upShadow_compls
  结论: ∂⁺ 𝒜ᶜˢ = (∂ 𝒜)ᶜˢ
  证明: by
  ext s
  simp only [mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [← compl_involutive.eq_iff]
-/
@[simp] lemma upShadow_compls : ∂⁺ 𝒜ᶜˢ = (∂ 𝒜)ᶜˢ := by
  ext s
  simp only [mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [← compl_involutive.eq_iff]

end UpShadow

end Finset
