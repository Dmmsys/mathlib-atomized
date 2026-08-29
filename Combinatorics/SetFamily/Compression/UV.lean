/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SetFamily.Shadow

/-!
# UV-compressions

This file defines UV-compression. It is an operation on a set family that reduces its shadow.

UV-compressing `a : α` along `u v : α` means replacing `a` by `(a ⊔ u) \ v` if `a` and `u` are
disjoint and `v ≤ a`. In some sense, it's moving `a` from `v` to `u`.

UV-compressions are immensely useful to prove the Kruskal-Katona theorem. The idea is that
compressing a set family might decrease the size of its shadow, so iterated compressions hopefully
minimise the shadow.

## Main declarations

* `UV.compress`: `compress u v a` is `a` compressed along `u` and `v`.
* `UV.compression`: `compression u v s` is the compression of the set family `s` along `u` and `v`.
  It is the compressions of the elements of `s` whose compression is not already in `s` along with
  the element whose compression is already in `s`. This way of splitting into what moves and what
  does not ensures the compression doesn't squash the set family, which is proved by
  `UV.card_compression`.
* `UV.card_shadow_compression_le`: Compressing reduces the size of the shadow. This is a key fact in
  the proof of Kruskal-Katona.

## Notation

`𝓒` (typed with `\MCC`) is notation for `UV.compression` in scope `FinsetFamily`.

## Notes

Even though our emphasis is on `Finset α`, we define UV-compressions more generally in a generalized
Boolean algebra, so that one can use it for `Set α`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, UV-compression, shadow
-/

@[expose] public section


open Finset

variable {α : Type*}

/--
theorem `sup_sdiff_injOn` / 定理 `sup_sdiff_injOn`

English:
theorem sup_sdiff_injOn
  given: [GeneralizedBooleanAlgebra α] (u v : α)
  proof: by
  rintro a ha b hb hab
  have h : ((a ⊔ u) \ v) \ u ⊔ v = ((b ⊔ u) \ v) \ u ⊔ v := by
    dsimp at hab
    rw [hab]
  rwa [sdiff_sdiff_comm, ha.1.symm.sup_sdiff_cancel_right, sdiff_sdiff_comm,
    hb.1.symm.sup_sdiff_cancel_right, sdiff_sup_cancel ha.2, sdiff_sup_cancel hb.2] at h

中文:
定理 sup_sdiff_injOn
  条件: [Generalized布尔ean代数 α] (u v : α)
  证明: by
  rintro a ha b hb hab
  have h : ((a ⊔ u) \ v) \ u ⊔ v = ((b ⊔ u) \ v) \ u ⊔ v := by
    dsimp at hab
    rw [hab]
  rwa [sdiff_sdiff_comm, ha.1.symm.sup_sdiff_cancel_right, sdiff_sdiff_comm,
    hb.1.symm.sup_sdiff_cancel_right, sdiff_sup_cancel ha.2, sdiff_sup_cancel hb.2] at h

Depends on / 依赖: sdiff_sdiff_comm, sdiff_sup_cancel, sup_sdiff_cancel_right, symm.sup_sdiff_cancel_right
-/
theorem sup_sdiff_injOn [GeneralizedBooleanAlgebra α] (u v : α) :
    { x | Disjoint u x ∧ v <= x }.InjOn fun x => (x ⊔ u) \ v := by
  rintro a ha b hb hab
  have h : ((a ⊔ u) \ v) \ u ⊔ v = ((b ⊔ u) \ v) \ u ⊔ v := by
    dsimp at hab
    rw [hab]
  rwa [sdiff_sdiff_comm, ha.1.symm.sup_sdiff_cancel_right, sdiff_sdiff_comm,
    hb.1.symm.sup_sdiff_cancel_right, sdiff_sup_cancel ha.2, sdiff_sup_cancel hb.2] at h

-- The namespace is here to distinguish from other compressions.
namespace UV

/-! ### UV-compression in generalized Boolean algebras -/


section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] [DecidableRel (@Disjoint α _ _)]
  [DecidableLE α] {s : Finset α} {u v a : α}

/--
Definition of `compress` / `compress` 的定义

English:
definition compress
  signature: (u v a : α)
  body: if Disjoint u a ∧ v <= a then (a ⊔ u) \ v else a

中文:
定义 compress
  签名: (u v a : α)
  定义体: if Disjoint u a ∧ v <= a then (a ⊔ u) \ v else a

Depends on / 依赖: Disjoint
-/
def compress (u v a : α) : α :=
  if Disjoint u a ∧ v <= a then (a ⊔ u) \ v else a

/--
theorem `compress_of_disjoint_of_le` / 定理 `compress_of_disjoint_of_le`

English:
theorem compress_of_disjoint_of_le
  given: (hua : Disjoint u a) (hva : v <= a)
  proof: if_pos ⟨hua, hva⟩

中文:
定理 compress_of_disjoint_of_le
  条件: (hua : Disjoint u a) (hva : v <= a)
  证明: if_pos ⟨hua, hva⟩

Depends on / 依赖: if_pos
-/
theorem compress_of_disjoint_of_le (hua : Disjoint u a) (hva : v <= a) :
    compress u v a = (a ⊔ u) \ v :=
  if_pos ⟨hua, hva⟩

/--
theorem `compress_of_disjoint_of_le'` / 定理 `compress_of_disjoint_of_le'`

English:
theorem compress_of_disjoint_of_le'
  given: (hva : Disjoint v a) (hua : u <= a)
  proof: by
  rw [compress_of_disjoint_of_le disjoint_sdiff_self_right
      (le_sdiff.2 ⟨(le_sup_right : v <= a ⊔ v)]; rw [hva.mono_right hua⟩)]; rw [sdiff_sup_cancel (le_sup_of_le_left hua)]; rw [hva.symm.sup_sdiff_cancel_right]

@[simp, grind =]

中文:
定理 compress_of_disjoint_of_le'
  条件: (hva : Disjoint v a) (hua : u <= a)
  证明: by
  rw [compress_of_disjoint_of_le disjoint_sdiff_self_right
      (le_sdiff.2 ⟨(le_sup_right : v <= a ⊔ v)]; rw [hva.mono_right hua⟩)]; rw [sdiff_sup_cancel (le_sup_of_le_left hua)]; rw [hva.symm.sup_sdiff_cancel_right]

@[simp, grind =]

Depends on / 依赖: compress_of_disjoint_of_le, disjoint_sdiff_self_right, hva.mono_right, hva.symm.sup_sdiff_cancel_right, le_sdiff, le_sup_of_le_left, le_sup_right, mono_right, sdiff_sup_cancel, sup_sdiff_cancel_right
-/
theorem compress_of_disjoint_of_le' (hva : Disjoint v a) (hua : u <= a) :
    compress u v ((a ⊔ v) \ u) = a := by
  rw [compress_of_disjoint_of_le disjoint_sdiff_self_right
      (le_sdiff.2 ⟨(le_sup_right : v <= a ⊔ v)]; rw [hva.mono_right hua⟩)]; rw [sdiff_sup_cancel (le_sup_of_le_left hua)]; rw [hva.symm.sup_sdiff_cancel_right]

@[simp, grind =]
/--
theorem `compress_self` / 定理 `compress_self`

English:
theorem compress_self
  given: (u a : α)
  statement: compress u u a = a
  proof: by
  unfold compress
  split_ifs with h
  · exact h.1.symm.sup_sdiff_cancel_right
  · rfl

中文:
定理 compress_self
  条件: (u a : α)
  结论: compress u u a = a
  证明: by
  unfold compress
  split_ifs with h
  · exact h.1.symm.sup_sdiff_cancel_right
  · rfl

Depends on / 依赖: compress, split_ifs, sup_sdiff_cancel_right, symm.sup_sdiff_cancel_right
-/
theorem compress_self (u a : α) : compress u u a = a := by
  unfold compress
  split_ifs with h
  · exact h.1.symm.sup_sdiff_cancel_right
  · rfl

/-- An element can be compressed to any other element by removing/adding the differences. -/
@[simp]
/--
theorem `compress_sdiff_sdiff` / 定理 `compress_sdiff_sdiff`

English:
theorem compress_sdiff_sdiff
  given: (a b : α)
  statement: compress (a \ b) (b \ a) b = a
  proof: by
  refine (compress_of_disjoint_of_le disjoint_sdiff_self_left sdiff_le).trans ?_
  rw [sup_sdiff_self_right]; rw [sup_sdiff]; rw [disjoint_sdiff_self_right.sdiff_eq_left]; rw [sup_eq_right]
  exact sdiff_sdiff_le

中文:
定理 compress_sdiff_sdiff
  条件: (a b : α)
  结论: compress (a \ b) (b \ a) b = a
  证明: by
  refine (compress_of_disjoint_of_le disjoint_sdiff_self_left sdiff_le).trans ?_
  rw [sup_sdiff_self_right]; rw [sup_sdiff]; rw [disjoint_sdiff_self_right.sdiff_eq_left]; rw [sup_eq_right]
  exact sdiff_sdiff_le

Depends on / 依赖: compress_of_disjoint_of_le, disjoint_sdiff_self_left, disjoint_sdiff_self_right, disjoint_sdiff_self_right.sdiff_eq_left, sdiff_eq_left, sdiff_le, sdiff_sdiff_le, sup_eq_right, sup_sdiff, sup_sdiff_self_right
-/
theorem compress_sdiff_sdiff (a b : α) : compress (a \ b) (b \ a) b = a := by
  refine (compress_of_disjoint_of_le disjoint_sdiff_self_left sdiff_le).trans ?_
  rw [sup_sdiff_self_right]; rw [sup_sdiff]; rw [disjoint_sdiff_self_right.sdiff_eq_left]; rw [sup_eq_right]
  exact sdiff_sdiff_le

/-- Compressing an element is idempotent. -/
@[simp]
/--
theorem `compress_idem` / 定理 `compress_idem`

English:
theorem compress_idem
  given: (u v a : α)
  statement: compress u v (compress u v a) = compress u v a
  proof: by
  unfold compress
  split_ifs with h h'
  · rw [le_sdiff_right.1 h'.2, sdiff_bot, sdiff_bot, sup_assoc, sup_idem]
  · rfl
  · rfl

中文:
定理 compress_idem
  条件: (u v a : α)
  结论: compress u v (compress u v a) = compress u v a
  证明: by
  unfold compress
  split_ifs with h h'
  · rw [le_sdiff_right.1 h'.2, sdiff_bot, sdiff_bot, sup_assoc, sup_idem]
  · rfl
  · rfl

Depends on / 依赖: compress, le_sdiff_right, sdiff_bot, split_ifs, sup_assoc, sup_idem
-/
theorem compress_idem (u v a : α) : compress u v (compress u v a) = compress u v a := by
  unfold compress
  split_ifs with h h'
  · rw [le_sdiff_right.1 h'.2, sdiff_bot, sdiff_bot, sup_assoc, sup_idem]
  · rfl
  · rfl

variable [DecidableEq α]

/--
Definition of `compression` / `compression` 的定义

English:
definition compression
  signature: (u v : α) (s : Finset α)
  body: {a in s | compress u v a in s} union {a in s.image <| compress u v | a ∉ s}

@[inherit_doc]
scoped[FinsetFamily] notation "𝓒 " => UV.compression

中文:
定义 compression
  签名: (u v : α) (s : 有限集 α)
  定义体: {a in s | compress u v a in s} union {a in s.image <| compress u v | a ∉ s}

@[inherit_doc]
scoped[FinsetFamily] notation "𝓒 " => UV.compression

Depends on / 依赖: compress, s.image
-/
def compression (u v : α) (s : Finset α) :=
  {a in s | compress u v a in s} union {a in s.image <| compress u v | a ∉ s}

@[inherit_doc]
scoped[FinsetFamily] notation "𝓒 " => UV.compression

open scoped FinsetFamily

/--
Definition of `IsCompressed` / `IsCompressed` 的定义

English:
definition IsCompressed
  signature: (u v : α) (s : Finset α)
  body: 𝓒 u v s = s

中文:
定义 IsCompressed
  签名: (u v : α) (s : 有限集 α)
  定义体: 𝓒 u v s = s
-/
def IsCompressed (u v : α) (s : Finset α) :=
  𝓒 u v s = s

/--
theorem `compress_injOn` / 定理 `compress_injOn`

English:
theorem compress_injOn
  statement: Set.InjOn (compress u v) ↑{a in s | compress u v a ∉ s}
  proof: by
  intro a ha b hb hab
  rw [mem_coe]; rw [mem_filter] at ha hb
  rw [compress] at ha hab
  split_ifs at ha hab with has
  · rw [compress] at hb hab
    split_ifs at hb hab with hbs
    · exact sup_sdiff_injOn u v has hbs hab
    · exact (hb.2 hb.1).elim
  · exact (ha.2 ha.1).elim

中文:
定理 compress_injOn
  结论: 集合.单射限制 (compress u v) ↑{a in s | compress u v a ∉ s}
  证明: by
  intro a ha b hb hab
  rw [mem_coe]; rw [mem_filter] at ha hb
  rw [compress] at ha hab
  split_ifs at ha hab with has
  · rw [compress] at hb hab
    split_ifs at hb hab with hbs
    · exact sup_sdiff_injOn u v has hbs hab
    · exact (hb.2 hb.1).elim
  · exact (ha.2 ha.1).elim

Depends on / 依赖: compress, mem_coe, mem_filter, split_ifs, sup_sdiff_injOn
-/
theorem compress_injOn : Set.InjOn (compress u v) ↑{a in s | compress u v a ∉ s} := by
  intro a ha b hb hab
  rw [mem_coe]; rw [mem_filter] at ha hb
  rw [compress] at ha hab
  split_ifs at ha hab with has
  · rw [compress] at hb hab
    split_ifs at hb hab with hbs
    · exact sup_sdiff_injOn u v has hbs hab
    · exact (hb.2 hb.1).elim
  · exact (ha.2 ha.1).elim

/--
theorem `mem_compression` / 定理 `mem_compression`

English:
theorem mem_compression
  proof: by
  simp_rw [compression, mem_union, mem_filter, mem_image, and_comm]

中文:
定理 mem_compression
  证明: by
  simp_rw [compression, mem_union, mem_filter, mem_image, and_comm]

Depends on / 依赖: and_comm, compression, mem_filter, mem_image, mem_union, simp_rw
-/
theorem mem_compression :
    a in 𝓒 u v s ↔ a in s ∧ compress u v a in s ∨ a ∉ s ∧ exists b in s, compress u v b = a := by
  simp_rw [compression, mem_union, mem_filter, mem_image, and_comm]

/--
theorem `IsCompressed.eq` / 定理 `IsCompressed.eq`

English:
theorem IsCompressed.eq
  given: (h : IsCompressed u v s)
  statement: 𝓒 u v s = s
  proof: h

@[simp]

中文:
定理 IsCompressed.eq
  条件: (h : IsCompressed u v s)
  结论: 𝓒 u v s = s
  证明: h

@[simp]
-/
protected theorem IsCompressed.eq (h : IsCompressed u v s) : 𝓒 u v s = s := h

@[simp]
/--
theorem `compression_self` / 定理 `compression_self`

English:
theorem compression_self
  given: (u : α) (s : Finset α)
  statement: 𝓒 u u s = s
  proof: by
  grind [mem_compression]

中文:
定理 compression_self
  条件: (u : α) (s : 有限集 α)
  结论: 𝓒 u u s = s
  证明: by
  grind [mem_compression]

Depends on / 依赖: mem_compression
-/
theorem compression_self (u : α) (s : Finset α) : 𝓒 u u s = s := by
  grind [mem_compression]

/--
theorem `isCompressed_self` / 定理 `isCompressed_self`

English:
theorem isCompressed_self
  given: (u : α) (s : Finset α)
  statement: IsCompressed u u s
  proof: compression_self u s

中文:
定理 isCompressed_self
  条件: (u : α) (s : 有限集 α)
  结论: IsCompressed u u s
  证明: compression_self u s

Depends on / 依赖: compression_self
-/
theorem isCompressed_self (u : α) (s : Finset α) : IsCompressed u u s := compression_self u s

/--
theorem `compress_disjoint` / 定理 `compress_disjoint`

English:
theorem compress_disjoint
  proof: disjoint_left.2 fun _a ha₁ ha₂ => (mem_filter.1 ha₂).2 (mem_filter.1 ha₁).1

中文:
定理 compress_disjoint
  证明: disjoint_left.2 fun _a ha₁ ha₂ => (mem_filter.1 ha₂).2 (mem_filter.1 ha₁).1

Depends on / 依赖: disjoint_left, mem_filter
-/
theorem compress_disjoint :
    Disjoint {a in s | compress u v a in s} {a in s.image <| compress u v | a ∉ s} :=
  disjoint_left.2 fun _a ha₁ ha₂ => (mem_filter.1 ha₂).2 (mem_filter.1 ha₁).1

/--
theorem `compress_mem_compression` / 定理 `compress_mem_compression`

English:
theorem compress_mem_compression
  given: (ha : a in s)
  statement: compress u v a in 𝓒 u v s
  proof: by
  rw [mem_compression]
  by_cases h : compress u v a in s
  · rw [compress_idem]
    exact Or.inl ⟨h, h⟩
  · exact Or.inr ⟨h, a, ha, rfl⟩

中文:
定理 compress_mem_compression
  条件: (ha : a in s)
  结论: compress u v a in 𝓒 u v s
  证明: by
  rw [mem_compression]
  by_cases h : compress u v a in s
  · rw [compress_idem]
    exact Or.inl ⟨h, h⟩
  · exact Or.inr ⟨h, a, ha, rfl⟩

Depends on / 依赖: Or.inl, Or.inr, compress, compress_idem, mem_compression
-/
theorem compress_mem_compression (ha : a in s) : compress u v a in 𝓒 u v s := by
  rw [mem_compression]
  by_cases h : compress u v a in s
  · rw [compress_idem]
    exact Or.inl ⟨h, h⟩
  · exact Or.inr ⟨h, a, ha, rfl⟩

-- This is a special case of `compress_mem_compression` once we have `compression_idem`.
/--
theorem `compress_mem_compression_of_mem_compression` / 定理 `compress_mem_compression_of_mem_compression`

English:
theorem compress_mem_compression_of_mem_compression
  given: (ha : a in 𝓒 u v s)
  proof: by
  rw [mem_compression] at ha ⊢
  simp only [compress_idem]
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact Or.inl ⟨ha, ha⟩
  · exact Or.inr ⟨by rwa [compress_idem], b, hb, (compress_idem _ _ _).symm⟩

中文:
定理 compress_mem_compression_of_mem_compression
  条件: (ha : a in 𝓒 u v s)
  证明: by
  rw [mem_compression] at ha ⊢
  simp only [compress_idem]
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact Or.inl ⟨ha, ha⟩
  · exact Or.inr ⟨by rwa [compress_idem], b, hb, (compress_idem _ _ _).symm⟩

Depends on / 依赖: Or.inl, Or.inr, compress_idem, mem_compression
-/
theorem compress_mem_compression_of_mem_compression (ha : a in 𝓒 u v s) :
    compress u v a in 𝓒 u v s := by
  rw [mem_compression] at ha ⊢
  simp only [compress_idem]
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact Or.inl ⟨ha, ha⟩
  · exact Or.inr ⟨by rwa [compress_idem], b, hb, (compress_idem _ _ _).symm⟩

/-- Compressing a family is idempotent. -/
@[simp]
/--
theorem `compression_idem` / 定理 `compression_idem`

English:
theorem compression_idem
  given: (u v : α) (s : Finset α)
  statement: 𝓒 u v (𝓒 u v s) = 𝓒 u v s
  proof: by
  have h : {a in 𝓒 u v s | compress u v a ∉ 𝓒 u v s} = ∅ :=
filter_false_of_mem fun a ha h => h compress_mem_compression_of_mem_compression ha
  rw [compression]; rw [filter_image]; rw [h]; rw [image_empty]; rw [← h]
  exact filter_union_filter_not_eq _ (compression u v s)

中文:
定理 compression_idem
  条件: (u v : α) (s : 有限集 α)
  结论: 𝓒 u v (𝓒 u v s) = 𝓒 u v s
  证明: by
  have h : {a in 𝓒 u v s | compress u v a ∉ 𝓒 u v s} = ∅ :=
filter_false_of_mem fun a ha h => h compress_mem_compression_of_mem_compression ha
  rw [compression]; rw [filter_image]; rw [h]; rw [image_empty]; rw [← h]
  exact filter_union_filter_not_eq _ (compression u v s)

Depends on / 依赖: compress, compress_mem_compression_of_mem_compression, compression, filter_false_of_mem, filter_image, filter_union_filter_not_eq, image_empty
-/
theorem compression_idem (u v : α) (s : Finset α) : 𝓒 u v (𝓒 u v s) = 𝓒 u v s := by
  have h : {a in 𝓒 u v s | compress u v a ∉ 𝓒 u v s} = ∅ :=
filter_false_of_mem fun a ha h => h compress_mem_compression_of_mem_compression ha
  rw [compression]; rw [filter_image]; rw [h]; rw [image_empty]; rw [← h]
  exact filter_union_filter_not_eq _ (compression u v s)

/-- Compressing a family doesn't change its size. -/
@[simp]
/--
theorem `card_compression` / 定理 `card_compression`

English:
theorem card_compression
  given: (u v : α) (s : Finset α)
  statement: #(𝓒 u v s) = #s
  proof: by
  rw [compression]; rw [card_union_of_disjoint compress_disjoint]; rw [filter_image]; rw [card_image_of_injOn compress_injOn]; rw [← card_union_of_disjoint (disjoint_filter_filter_not s _ _)]; rw [filter_union_filter_not_eq]

中文:
定理 card_compression
  条件: (u v : α) (s : 有限集 α)
  结论: #(𝓒 u v s) = #s
  证明: by
  rw [compression]; rw [card_union_of_disjoint compress_disjoint]; rw [filter_image]; rw [card_image_of_injOn compress_injOn]; rw [← card_union_of_disjoint (disjoint_filter_filter_not s _ _)]; rw [filter_union_filter_not_eq]

Depends on / 依赖: card_image_of_injOn, card_union_of_disjoint, compress_disjoint, compress_injOn, compression, disjoint_filter_filter_not, filter_image, filter_union_filter_not_eq
-/
theorem card_compression (u v : α) (s : Finset α) : #(𝓒 u v s) = #s := by
  rw [compression]; rw [card_union_of_disjoint compress_disjoint]; rw [filter_image]; rw [card_image_of_injOn compress_injOn]; rw [← card_union_of_disjoint (disjoint_filter_filter_not s _ _)]; rw [filter_union_filter_not_eq]

/--
theorem `le_of_mem_compression_of_notMem` / 定理 `le_of_mem_compression_of_notMem`

English:
theorem le_of_mem_compression_of_notMem
  given: (h : a in 𝓒 u v s) (ha : a ∉ s)
  statement: u <= a
  proof: by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba with h
  · rw [← hba, le_sdiff]
    exact ⟨le_sup_right, h.1.mono_right h.2⟩
  · cases ne_of_mem_of_not_mem hb ha hba

中文:
定理 le_of_mem_compression_of_notMem
  条件: (h : a in 𝓒 u v s) (ha : a ∉ s)
  结论: u <= a
  证明: by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba with h
  · rw [← hba, le_sdiff]
    exact ⟨le_sup_right, h.1.mono_right h.2⟩
  · cases ne_of_mem_of_not_mem hb ha hba

Depends on / 依赖: compress, le_sdiff, le_sup_right, mem_compression, mono_right, ne_of_mem_of_not_mem, split_ifs
-/
theorem le_of_mem_compression_of_notMem (h : a in 𝓒 u v s) (ha : a ∉ s) : u <= a := by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba with h
  · rw [← hba, le_sdiff]
    exact ⟨le_sup_right, h.1.mono_right h.2⟩
  · cases ne_of_mem_of_not_mem hb ha hba

/--
theorem `disjoint_of_mem_compression_of_notMem` / 定理 `disjoint_of_mem_compression_of_notMem`

English:
theorem disjoint_of_mem_compression_of_notMem
  given: (h : a in 𝓒 u v s) (ha : a ∉ s)
  statement: Disjoint v a
  proof: by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba
  · rw [← hba]
    exact disjoint_sdiff_self_right
  · cases ne_of_mem_of_not_mem hb ha hba

中文:
定理 disjoint_of_mem_compression_of_notMem
  条件: (h : a in 𝓒 u v s) (ha : a ∉ s)
  结论: Disjoint v a
  证明: by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba
  · rw [← hba]
    exact disjoint_sdiff_self_right
  · cases ne_of_mem_of_not_mem hb ha hba

Depends on / 依赖: compress, disjoint_sdiff_self_right, mem_compression, ne_of_mem_of_not_mem, split_ifs
-/
theorem disjoint_of_mem_compression_of_notMem (h : a in 𝓒 u v s) (ha : a ∉ s) : Disjoint v a := by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba
  · rw [← hba]
    exact disjoint_sdiff_self_right
  · cases ne_of_mem_of_not_mem hb ha hba

/--
theorem `sup_sdiff_mem_of_mem_compression_of_notMem` / 定理 `sup_sdiff_mem_of_mem_compression_of_notMem`

English:
theorem sup_sdiff_mem_of_mem_compression_of_notMem
  given: (h : a in 𝓒 u v s) (ha : a ∉ s)
  proof: by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba with h
  · rwa [← hba, sdiff_sup_cancel (le_sup_of_le_left h.2), sup_sdiff_right_self,
      h.1.symm.sdiff_eq_left]
  · cases ne_of_mem_of_not_mem hb ha hba

中文:
定理 sup_sdiff_mem_of_mem_compression_of_notMem
  条件: (h : a in 𝓒 u v s) (ha : a ∉ s)
  证明: by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba with h
  · rwa [← hba, sdiff_sup_cancel (le_sup_of_le_left h.2), sup_sdiff_right_self,
      h.1.symm.sdiff_eq_left]
  · cases ne_of_mem_of_not_mem hb ha hba

Depends on / 依赖: compress, le_sup_of_le_left, mem_compression, ne_of_mem_of_not_mem, sdiff_eq_left, sdiff_sup_cancel, split_ifs, sup_sdiff_right_self, symm.sdiff_eq_left
-/
theorem sup_sdiff_mem_of_mem_compression_of_notMem (h : a in 𝓒 u v s) (ha : a ∉ s) :
    (a ⊔ v) \ u in s := by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba with h
  · rwa [← hba, sdiff_sup_cancel (le_sup_of_le_left h.2), sup_sdiff_right_self,
      h.1.symm.sdiff_eq_left]
  · cases ne_of_mem_of_not_mem hb ha hba

/--
theorem `sup_sdiff_mem_of_mem_compression` / 定理 `sup_sdiff_mem_of_mem_compression`

English:
theorem sup_sdiff_mem_of_mem_compression
  given: (ha : a in 𝓒 u v s) (hva : v <= a) (hua : Disjoint u a)
  proof: by
  rw [mem_compression]; rw [compress_of_disjoint_of_le hua hva] at ha
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact ha
  have hu : u = ⊥ := by
    suffices Disjoint u (u \ v) by rwa [(hua.mono_right hva).sdiff_eq_left, disjoint_self] at this
    refine hua.mono_right ?_
    rw [← compress_id

中文:
定理 sup_sdiff_mem_of_mem_compression
  条件: (ha : a in 𝓒 u v s) (hva : v <= a) (hua : Disjoint u a)
  证明: by
  rw [mem_compression]; rw [compress_of_disjoint_of_le hua hva] at ha
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact ha
  have hu : u = ⊥ := by
    suffices Disjoint u (u \ v) by rwa [(hua.mono_right hva).sdiff_eq_left, disjoint_self] at this
    refine hua.mono_right ?_
    rw [← compress_id

Depends on / 依赖: Disjoint, Disjoint.mono_right, compress_idem, compress_of_disjoint_of_le, disjoint_self, hua.mono_right, le_sup_right, mem_compression, mono_right, sdiff_eq_left, sdiff_le_sdiff_right
-/
theorem sup_sdiff_mem_of_mem_compression (ha : a in 𝓒 u v s) (hva : v <= a) (hua : Disjoint u a) :
    (a ⊔ u) \ v in s := by
  rw [mem_compression]; rw [compress_of_disjoint_of_le hua hva] at ha
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact ha
  have hu : u = ⊥ := by
    suffices Disjoint u (u \ v) by rwa [(hua.mono_right hva).sdiff_eq_left, disjoint_self] at this
    refine hua.mono_right ?_
    rw [← compress_idem]; rw [compress_of_disjoint_of_le hua hva]
    exact sdiff_le_sdiff_right le_sup_right
  have hv : v = ⊥ := by
    rw [← disjoint_self]
    apply Disjoint.mono_right hva
    rw [← compress_idem]; rw [compress_of_disjoint_of_le hua hva]
    exact disjoint_sdiff_self_right
  rwa [hu, hv, compress_self, sup_bot_eq, sdiff_bot]

/--
theorem `mem_of_mem_compression` / 定理 `mem_of_mem_compression`

English:
theorem mem_of_mem_compression
  given: (ha : a in 𝓒 u v s) (hva : v <= a) (hvu : v = ⊥ -> u = ⊥)
  proof: by
  rw [mem_compression] at ha
  obtain ha | ⟨_, b, hb, h⟩ := ha
  · exact ha.1
  unfold compress at h
  split_ifs at h
  · rw [← h, le_sdiff_right] at hva
    rwa [← h, hvu hva, hva, sup_bot_eq, sdiff_bot]
  · rwa [← h]

中文:
定理 mem_of_mem_compression
  条件: (ha : a in 𝓒 u v s) (hva : v <= a) (hvu : v = ⊥ -> u = ⊥)
  证明: by
  rw [mem_compression] at ha
  obtain ha | ⟨_, b, hb, h⟩ := ha
  · exact ha.1
  unfold compress at h
  split_ifs at h
  · rw [← h, le_sdiff_right] at hva
    rwa [← h, hvu hva, hva, sup_bot_eq, sdiff_bot]
  · rwa [← h]

Depends on / 依赖: compress, le_sdiff_right, mem_compression, sdiff_bot, split_ifs, sup_bot_eq
-/
theorem mem_of_mem_compression (ha : a in 𝓒 u v s) (hva : v <= a) (hvu : v = ⊥ -> u = ⊥) :
    a in s := by
  rw [mem_compression] at ha
  obtain ha | ⟨_, b, hb, h⟩ := ha
  · exact ha.1
  unfold compress at h
  split_ifs at h
  · rw [← h, le_sdiff_right] at hva
    rwa [← h, hvu hva, hva, sup_bot_eq, sdiff_bot]
  · rwa [← h]

end GeneralizedBooleanAlgebra

/-! ### UV-compression on finsets -/

open FinsetFamily

variable [DecidableEq α] {𝒜 : Finset (Finset α)} {u v : Finset α} {r : Nat}

/--
theorem `card_compress` / 定理 `card_compress`

English:
theorem card_compress
  given: (huv : #u = #v) (a : Finset α)
  statement: #(compress u v a) = #a
  proof: by
  unfold compress
  split_ifs with h
  · rw [card_sdiff_of_subset (h.2.trans le_sup_left), sup_eq_union,
      card_union_of_disjoint h.1.symm, huv, add_tsub_cancel_right]
  · rfl

中文:
定理 card_compress
  条件: (huv : #u = #v) (a : 有限集 α)
  结论: #(compress u v a) = #a
  证明: by
  unfold compress
  split_ifs with h
  · rw [card_sdiff_of_subset (h.2.trans le_sup_left), sup_eq_union,
      card_union_of_disjoint h.1.symm, huv, add_tsub_cancel_right]
  · rfl

Depends on / 依赖: add_tsub_cancel_right, card_sdiff_of_subset, card_union_of_disjoint, compress, le_sup_left, split_ifs, sup_eq_union
-/
theorem card_compress (huv : #u = #v) (a : Finset α) : #(compress u v a) = #a := by
  unfold compress
  split_ifs with h
  · rw [card_sdiff_of_subset (h.2.trans le_sup_left), sup_eq_union,
      card_union_of_disjoint h.1.symm, huv, add_tsub_cancel_right]
  · rfl

/--
lemma `_root_.Set.Sized.uvCompression` / 引理 `_root_.Set.Sized.uvCompression`

English:
lemma _root_.Set.Sized.uvCompression
  given: (huv : #u = #v) (h𝒜 : (𝒜 : Set (Finset α)).Sized r)
  proof: by
  simp_rw [Set.Sized, mem_coe, mem_compression]
  rintro s (hs | ⟨huvt, t, ht, rfl⟩)
  · exact h𝒜 hs.1
  · rw [card_compress huv, h𝒜 ht]

中文:
引理 _root_.集合.Sized.uvCompression
  条件: (huv : #u = #v) (h𝒜 : (𝒜 : 集合 (有限集 α)).Sized r)
  证明: by
  simp_rw [Set.Sized, mem_coe, mem_compression]
  rintro s (hs | ⟨huvt, t, ht, rfl⟩)
  · exact h𝒜 hs.1
  · rw [card_compress huv, h𝒜 ht]

Depends on / 依赖: Set.Sized, card_compress, mem_coe, mem_compression, simp_rw
-/
lemma _root_.Set.Sized.uvCompression (huv : #u = #v) (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (𝓒 u v 𝒜 : Set (Finset α)).Sized r := by
  simp_rw [Set.Sized, mem_coe, mem_compression]
  rintro s (hs | ⟨huvt, t, ht, rfl⟩)
  · exact h𝒜 hs.1
  · rw [card_compress huv, h𝒜 ht]

/--
theorem `aux` / 定理 `aux`

English:
theorem aux
  given: (huv : forall x in u, exists y in v, IsCompressed (u.erase x) (v.erase y) 𝒜)
  proof: by
  grind

中文:
定理 aux
  条件: (huv : 对任意 x in u, 存在 y in v, IsCompressed (u.erase x) (v.erase y) 𝒜)
  证明: by
  grind
-/
private theorem aux (huv : forall x in u, exists y in v, IsCompressed (u.erase x) (v.erase y) 𝒜) :
    v = ∅ -> u = ∅ := by
  grind

/--
theorem `shadow_compression_subset_compression_shadow` / 定理 `shadow_compression_subset_compression_shadow`

English:
theorem shadow_compression_subset_compression_shadow
  statement: (u v : Finset α)
  proof: by
  set 𝒜' := 𝓒 u v 𝒜
  suffices H : forall s in ∂ 𝒜',
      s ∉ ∂ 𝒜 -> u subseteq s ∧ Disjoint v s ∧ (s union v) \ u in ∂ 𝒜 ∧ (s union v) \ u ∉ ∂ 𝒜' by
    rintro s hs'
    rw [mem_compression]
    by_cases hs : s in 𝒜.shadow
    swap
    · obtain ⟨hus, hvs, h, _⟩ := H _ hs' hs
      exact Or.inr 

中文:
定理 shadow_compression_subset_compression_shadow
  结论: (u v : 有限集 α)
  证明: by
  set 𝒜' := 𝓒 u v 𝒜
  suffices H : forall s in ∂ 𝒜',
      s ∉ ∂ 𝒜 -> u subseteq s ∧ Disjoint v s ∧ (s union v) \ u in ∂ 𝒜 ∧ (s union v) \ u ∉ ∂ 𝒜' by
    rintro s hs'
    rw [mem_compression]
    by_cases hs : s in 𝒜.shadow
    swap
    · obtain ⟨hus, hvs, h, _⟩ := H _ hs' hs
      exact Or.inr 

Depends on / 依赖: Disjoint, Or.inl, Or.inr, compress, compress_of_disjoint_of_le, mem_compression, mem_shadow_iff, notMem_erase, notMem_mono, shadow, split_ifs, subseteq
-/
theorem shadow_compression_subset_compression_shadow (u v : Finset α)
    (huv : forall x in u, exists y in v, IsCompressed (u.erase x) (v.erase y) 𝒜) :
    ∂ (𝓒 u v 𝒜) subseteq 𝓒 u v (∂ 𝒜) := by
  set 𝒜' := 𝓒 u v 𝒜
  suffices H : forall s in ∂ 𝒜',
      s ∉ ∂ 𝒜 -> u subseteq s ∧ Disjoint v s ∧ (s union v) \ u in ∂ 𝒜 ∧ (s union v) \ u ∉ ∂ 𝒜' by
    rintro s hs'
    rw [mem_compression]
    by_cases hs : s in 𝒜.shadow
    swap
    · obtain ⟨hus, hvs, h, _⟩ := H _ hs' hs
      exact Or.inr ⟨hs, _, h, compress_of_disjoint_of_le' hvs hus⟩
    refine Or.inl ⟨hs, ?_⟩
    rw [compress]
    split_ifs with huvs
    swap
    · exact hs
    rw [mem_shadow_iff] at hs'
    obtain ⟨t, Ht, a, hat, rfl⟩ := hs'
    have hav : a ∉ v := notMem_mono huvs.2 (notMem_erase a t)
    have hvt : v <= t := huvs.2.trans (erase_subset _ t)
    have ht : t in 𝒜 := mem_of_mem_compression Ht hvt (aux huv)
    by_cases hau : a in u
    · obtain ⟨b, hbv, Hcomp⟩ := huv a hau
      refine mem_shadow_iff_insert_mem.2 ⟨b, notMem_sdiff_of_mem_right hbv, ?_⟩
      rw [← Hcomp.eq] at ht
      have hsb :=
        sup_sdiff_mem_of_mem_compression ht ((erase_subset _ _).trans hvt)
          (disjoint_erase_comm.2 huvs.1)
      rwa [sup_eq_union, sdiff_erase (mem_union_left _ <| hvt hbv), union_erase_of_mem hat, ←
        erase_union_of_mem hau] at hsb
    · refine mem_shadow_iff.2
        ⟨(t ⊔ u) \ v,
sup_sdiff_mem_of_mem_compression Ht hvt disjoint_of_erase_right hau huvs.1, a, ?_, ?_⟩
      · rw [sup_eq_union, mem_sdiff, mem_union]
        exact ⟨Or.inl hat, hav⟩
      · simp [← erase_sdiff_comm, erase_union_distrib, erase_eq_of_notMem hau]
  intro s hs𝒜' hs𝒜
  -- This is going to be useful a couple of times so let's name it.
  have m : forall y, y ∉ s -> insert y s ∉ 𝒜 := fun y h a => hs𝒜 (mem_shadow_iff_insert_mem.2 ⟨y, h, a⟩)
  obtain ⟨x, _, _⟩ := mem_shadow_iff_insert_mem.1 hs𝒜'
  have hus : u subseteq insert x s := le_of_mem_compression_of_notMem ‹_ in 𝒜'› (m _ ‹x ∉ s›)
  have hvs : Disjoint v (insert x s) := disjoint_of_mem_compression_of_notMem ‹_› (m _ ‹x ∉ s›)
  have : (insert x s union v) \ u in 𝒜 := sup_sdiff_mem_of_mem_compression_of_notMem ‹_› (m _ ‹x ∉ s›)
  have hsv : Disjoint s v := hvs.symm.mono_left (subset_insert _ _)
  have hvu : Disjoint v u := disjoint_of_subset_right hus hvs
  have hxv : x ∉ v := disjoint_right.1 hvs (mem_insert_self _ _)
  have : v \ u = v := ‹Disjoint v u›.sdiff_eq_left
  -- The first key part is that `x ∉ u`
  have : x ∉ u := by
    intro hxu
    obtain ⟨y, hyv, hxy⟩ := huv x hxu
    -- If `x ∈ u`, we can get `y ∈ v` so that `𝒜` is `(u.erase x, v.erase y)`-compressed
    apply m y (disjoint_right.1 hsv hyv)
    -- and we will use this `y` to contradict `m`, so we would like to show `insert y s ∈ 𝒜`.
    -- We do this by showing the below
    have : ((insert x s union v) \ u union erase u x) \ erase v y in 𝒜 := by
      refine
        sup_sdiff_mem_of_mem_compression (by rwa [hxy.eq]) ?_
          (disjoint_of_subset_left (erase_subset _ _) disjoint_sdiff)
      rw [union_sdiff_distrib]; rw [‹v \ u = v›]
      exact (erase_subset _ _).trans subset_union_right
    -- and then arguing that it's the same
    convert! this using 1
    rw [sdiff_union_erase_cancel (hus.trans subset_union_left) ‹x in u›]; rw [erase_union_distrib]; rw [erase_insert ‹x ∉ s›]; rw [erase_eq_of_notMem ‹x ∉ v›]; rw [sdiff_erase (mem_union_right _ hyv)]; rw [union_sdiff_cancel_right hsv]
  -- Now that this is done, it's immediate that `u ⊆ s`
  have hus : u subseteq s := by rwa [← erase_eq_of_notMem ‹x ∉ u›, ← subset_insert_iff]
  -- and we already had that `v` and `s` are disjoint,
  -- so it only remains to get `(s ∪ v) \ u ∈ ∂ 𝒜 \ ∂ 𝒜'`
  simp_rw [mem_shadow_iff_insert_mem]
  refine ⟨hus, hsv.symm, ⟨x, ?_, ?_⟩, ?_⟩
  -- `(s ∪ v) \ u ∈ ∂ 𝒜` is pretty direct:
  · exact notMem_sdiff_of_notMem_left (notMem_union.2 ⟨‹x ∉ s›, ‹x ∉ v›⟩)
  · rwa [← insert_sdiff_of_notMem _ ‹x ∉ u›, ← insert_union]
  -- For (s ∪ v) \ u ∉ ∂ 𝒜', we split up based on w ∈ u
  rintro ⟨w, hwB, hw𝒜'⟩
  have : v subseteq insert w ((s union v) \ u) :=
    (subset_sdiff.2 ⟨subset_union_right, hvu⟩).trans (subset_insert _ _)
  by_cases hwu : w in u
  -- If `w ∈ u`, we find `z ∈ v`, and contradict `m` again
  · obtain ⟨z, hz, hxy⟩ := huv w hwu
    apply m z (disjoint_right.1 hsv hz)
    have : insert w ((s union v) \ u) in 𝒜 := mem_of_mem_compression hw𝒜' ‹_› (aux huv)
    have : (insert w ((s union v) \ u) union erase u w) \ erase v z in 𝒜 := by
      refine sup_sdiff_mem_of_mem_compression (by rwa [hxy.eq]) ((erase_subset _ _).trans ‹_›) ?_
      rw [← sdiff_erase (mem_union_left _ <| hus hwu)]
      exact disjoint_sdiff
    convert! this using 1
    rw [insert_union_comm]; rw [insert_erase ‹w in u›]; rw [sdiff_union_of_subset (hus.trans subset_union_left)]; rw [sdiff_erase (mem_union_right _ ‹z in v›)]; rw [union_sdiff_cancel_right hsv]
  -- If `w ∉ u`, we contradict `m` again
  rw [mem_sdiff]; rw [← Classical.not_imp]; rw [Classical.not_not] at hwB
  apply m w (hwu ∘ hwB ∘ mem_union_left _)
  have : (insert w ((s union v) \ u) union u) \ v in 𝒜 :=
    sup_sdiff_mem_of_mem_compression ‹insert w ((s union v) \ u) in 𝒜'› ‹_›
      (disjoint_insert_right.2 ⟨‹_›, disjoint_sdiff⟩)
  convert! this using 1
  rw [insert_union]; rw [sdiff_union_of_subset (hus.trans subset_union_left)]; rw [insert_sdiff_of_notMem _ (hwu ∘ hwB ∘ mem_union_right _)]; rw [union_sdiff_cancel_right hsv]

/--
theorem `card_shadow_compression_le` / 定理 `card_shadow_compression_le`

English:
theorem card_shadow_compression_le
  statement: (u v : Finset α)
  proof: (card_le_card <| shadow_compression_subset_compression_shadow _ _ huv).trans
    (card_compression _ _ _).le

中文:
定理 card_shadow_compression_le
  结论: (u v : 有限集 α)
  证明: (card_le_card <| shadow_compression_subset_compression_shadow _ _ huv).trans
    (card_compression _ _ _).le

Depends on / 依赖: card_compression, card_le_card, shadow_compression_subset_compression_shadow
-/
theorem card_shadow_compression_le (u v : Finset α)
    (huv : forall x in u, exists y in v, IsCompressed (u.erase x) (v.erase y) 𝒜) :
    #(∂ (𝓒 u v 𝒜)) <= #(∂ 𝒜) :=
  (card_le_card <| shadow_compression_subset_compression_shadow _ _ huv).trans
    (card_compression _ _ _).le

end UV
