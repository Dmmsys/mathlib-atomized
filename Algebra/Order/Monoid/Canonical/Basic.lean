/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic

/-!
# Extra lemmas about canonically ordered monoids
-/

public section

namespace Set
variable {α : Type*} [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {β : Type*} {f : α -> β} {k : α}

/--
theorem `range_add_eq_image_Ici` / 定理 `range_add_eq_image_Ici`

English:
theorem range_add_eq_image_Ici
  statement: range (fun x => f (x + k)) = f '' Ici k
  proof: Set.ext fun x => ⟨fun ⟨y, hfy⟩ => ⟨y + k, self_le_add_left k y, hfy⟩,
    fun ⟨y, hy, hfy⟩ => ⟨y - k, by simpa [tsub_add_cancel_of_le hy] using hfy⟩⟩

中文:
定理 range_add_eq_image_Ici
  结论: range (fun x => f (x + k)) = f '' Ici k
  证明: Set.ext fun x => ⟨fun ⟨y, hfy⟩ => ⟨y + k, self_le_add_left k y, hfy⟩,
    fun ⟨y, hy, hfy⟩ => ⟨y - k, by simpa [tsub_add_cancel_of_le hy] using hfy⟩⟩

Depends on / 依赖: Set.ext, self_le_add_left, tsub_add_cancel_of_le
-/
theorem range_add_eq_image_Ici : range (fun x => f (x + k)) = f '' Ici k :=
  Set.ext fun x => ⟨fun ⟨y, hfy⟩ => ⟨y + k, self_le_add_left k y, hfy⟩,
    fun ⟨y, hy, hfy⟩ => ⟨y - k, by simpa [tsub_add_cancel_of_le hy] using hfy⟩⟩

end Set

section LinearOrder
variable {α : Type*} [LinearOrder α] {P : α -> Prop} {a b c : α}

section Add
variable [Add α] [CanonicallyOrderedAdd α]

/--
theorem `lt_add_iff_lt_left_or_exists_lt` / 定理 `lt_add_iff_lt_left_or_exists_lt`

English:
theorem lt_add_iff_lt_left_or_exists_lt
  given: [AddLeftReflectLT α] [IsLeftCancelAdd α]
  proof: by
  obtain h | h := lt_or_ge a b
  · have : a < b + c := h.trans_le (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp

中文:
定理 lt_add_iff_lt_left_or_exists_lt
  条件: [AddLeftReflectLT α] [IsLeftCancelAdd α]
  证明: by
  obtain h | h := lt_or_ge a b
  · have : a < b + c := h.trans_le (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp

Depends on / 依赖: exists_add_of_le, h.trans_le, le_self_add, lt_or_ge, trans_le
-/
theorem lt_add_iff_lt_left_or_exists_lt [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    a < b + c ↔ a < b ∨ exists d < c, a = b + d := by
  obtain h | h := lt_or_ge a b
  · have : a < b + c := h.trans_le (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp

/--
theorem `forall_lt_add_iff_lt_left` / 定理 `forall_lt_add_iff_lt_left`

English:
theorem forall_lt_add_iff_lt_left
  given: [AddLeftReflectLT α] [IsLeftCancelAdd α]
  proof: by
  simp_rw [lt_add_iff_lt_left_or_exists_lt]
  aesop

中文:
定理 forall_lt_add_iff_lt_left
  条件: [AddLeftReflectLT α] [IsLeftCancelAdd α]
  证明: by
  simp_rw [lt_add_iff_lt_left_or_exists_lt]
  aesop

Depends on / 依赖: lt_add_iff_lt_left_or_exists_lt, simp_rw
-/
theorem forall_lt_add_iff_lt_left [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    (forall a < b + c, P a) ↔ (forall a < b, P a) ∧ (forall d < c, P (b + d)) := by
  simp_rw [lt_add_iff_lt_left_or_exists_lt]
  aesop

/--
theorem `exists_lt_add_iff_lt_left` / 定理 `exists_lt_add_iff_lt_left`

English:
theorem exists_lt_add_iff_lt_left
  given: [AddLeftReflectLT α] [IsLeftCancelAdd α]
  proof: by
  simp_rw [lt_add_iff_lt_left_or_exists_lt]
  aesop

中文:
定理 exists_lt_add_iff_lt_left
  条件: [AddLeftReflectLT α] [IsLeftCancelAdd α]
  证明: by
  simp_rw [lt_add_iff_lt_left_or_exists_lt]
  aesop

Depends on / 依赖: lt_add_iff_lt_left_or_exists_lt, simp_rw
-/
theorem exists_lt_add_iff_lt_left [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    (exists a < b + c, P a) ↔ (exists a < b, P a) ∨ (exists d < c, P (b + d)) := by
  simp_rw [lt_add_iff_lt_left_or_exists_lt]
  aesop

/--
theorem `le_add_iff_lt_left_or_exists_le` / 定理 `le_add_iff_lt_left_or_exists_le`

English:
theorem le_add_iff_lt_left_or_exists_le
  given: [AddLeftMono α] [IsLeftCancelAdd α]
  proof: by
  obtain h | h := lt_or_ge a b
  · have : a <= b + c := h.le.trans (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp

中文:
定理 le_add_iff_lt_left_or_exists_le
  条件: [AddLeftMono α] [IsLeftCancelAdd α]
  证明: by
  obtain h | h := lt_or_ge a b
  · have : a <= b + c := h.le.trans (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp

Depends on / 依赖: exists_add_of_le, h.le.trans, le_self_add, lt_or_ge
-/
theorem le_add_iff_lt_left_or_exists_le [AddLeftMono α] [IsLeftCancelAdd α] :
    a <= b + c ↔ a < b ∨ exists d <= c, a = b + d := by
  obtain h | h := lt_or_ge a b
  · have : a <= b + c := h.le.trans (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp

/--
theorem `forall_le_add_iff_le_left` / 定理 `forall_le_add_iff_le_left`

English:
theorem forall_le_add_iff_le_left
  given: [AddLeftMono α] [IsLeftCancelAdd α]
  proof: by
  simp_rw [le_add_iff_lt_left_or_exists_le]
  aesop

中文:
定理 forall_le_add_iff_le_left
  条件: [AddLeftMono α] [IsLeftCancelAdd α]
  证明: by
  simp_rw [le_add_iff_lt_left_or_exists_le]
  aesop

Depends on / 依赖: le_add_iff_lt_left_or_exists_le, simp_rw
-/
theorem forall_le_add_iff_le_left [AddLeftMono α] [IsLeftCancelAdd α] :
    (forall a <= b + c, P a) ↔ (forall a < b, P a) ∧ (forall d <= c, P (b + d)) := by
  simp_rw [le_add_iff_lt_left_or_exists_le]
  aesop

/--
theorem `exists_le_add_iff_le_left` / 定理 `exists_le_add_iff_le_left`

English:
theorem exists_le_add_iff_le_left
  given: [AddLeftMono α] [IsLeftCancelAdd α]
  proof: by
  simp_rw [le_add_iff_lt_left_or_exists_le]
  aesop

中文:
定理 exists_le_add_iff_le_left
  条件: [AddLeftMono α] [IsLeftCancelAdd α]
  证明: by
  simp_rw [le_add_iff_lt_left_or_exists_le]
  aesop

Depends on / 依赖: le_add_iff_lt_left_or_exists_le, simp_rw
-/
theorem exists_le_add_iff_le_left [AddLeftMono α] [IsLeftCancelAdd α] :
    (exists a <= b + c, P a) ↔ (exists a < b, P a) ∨ (exists d <= c, P (b + d)) := by
  simp_rw [le_add_iff_lt_left_or_exists_le]
  aesop

end Add

section AddCommMagma
variable [AddCommMagma α] [CanonicallyOrderedAdd α]

/--
theorem `lt_add_iff_lt_right_or_exists_lt` / 定理 `lt_add_iff_lt_right_or_exists_lt`

English:
theorem lt_add_iff_lt_right_or_exists_lt
  given: [AddLeftReflectLT α] [IsLeftCancelAdd α]
  proof: by
  rw [add_comm]; rw [lt_add_iff_lt_left_or_exists_lt]
  simp_rw [add_comm]

中文:
定理 lt_add_iff_lt_right_or_exists_lt
  条件: [AddLeftReflectLT α] [IsLeftCancelAdd α]
  证明: by
  rw [add_comm]; rw [lt_add_iff_lt_left_or_exists_lt]
  simp_rw [add_comm]

Depends on / 依赖: add_comm, lt_add_iff_lt_left_or_exists_lt, simp_rw
-/
theorem lt_add_iff_lt_right_or_exists_lt [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    a < b + c ↔ a < c ∨ exists d < b, a = d + c := by
  rw [add_comm]; rw [lt_add_iff_lt_left_or_exists_lt]
  simp_rw [add_comm]

/--
theorem `forall_lt_add_iff_lt_right` / 定理 `forall_lt_add_iff_lt_right`

English:
theorem forall_lt_add_iff_lt_right
  given: [AddLeftReflectLT α] [IsLeftCancelAdd α]
  proof: by
  simp_rw [lt_add_iff_lt_right_or_exists_lt]
  aesop

中文:
定理 forall_lt_add_iff_lt_right
  条件: [AddLeftReflectLT α] [IsLeftCancelAdd α]
  证明: by
  simp_rw [lt_add_iff_lt_right_or_exists_lt]
  aesop

Depends on / 依赖: lt_add_iff_lt_right_or_exists_lt, simp_rw
-/
theorem forall_lt_add_iff_lt_right [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    (forall a < b + c, P a) ↔ (forall a < c, P a) ∧ (forall d < b, P (d + c)) := by
  simp_rw [lt_add_iff_lt_right_or_exists_lt]
  aesop

/--
theorem `exists_lt_add_iff_lt_right` / 定理 `exists_lt_add_iff_lt_right`

English:
theorem exists_lt_add_iff_lt_right
  given: [AddLeftReflectLT α] [IsLeftCancelAdd α]
  proof: by
  simp_rw [lt_add_iff_lt_right_or_exists_lt]
  aesop

中文:
定理 exists_lt_add_iff_lt_right
  条件: [AddLeftReflectLT α] [IsLeftCancelAdd α]
  证明: by
  simp_rw [lt_add_iff_lt_right_or_exists_lt]
  aesop

Depends on / 依赖: lt_add_iff_lt_right_or_exists_lt, simp_rw
-/
theorem exists_lt_add_iff_lt_right [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    (exists a < b + c, P a) ↔ (exists a < c, P a) ∨ (exists d < b, P (d + c)) := by
  simp_rw [lt_add_iff_lt_right_or_exists_lt]
  aesop

/--
theorem `le_add_iff_lt_right_or_exists_le` / 定理 `le_add_iff_lt_right_or_exists_le`

English:
theorem le_add_iff_lt_right_or_exists_le
  given: [AddLeftMono α] [IsLeftCancelAdd α]
  proof: by
  rw [add_comm]; rw [le_add_iff_lt_left_or_exists_le]
  simp_rw [add_comm]

中文:
定理 le_add_iff_lt_right_or_exists_le
  条件: [AddLeftMono α] [IsLeftCancelAdd α]
  证明: by
  rw [add_comm]; rw [le_add_iff_lt_left_or_exists_le]
  simp_rw [add_comm]

Depends on / 依赖: add_comm, le_add_iff_lt_left_or_exists_le, simp_rw
-/
theorem le_add_iff_lt_right_or_exists_le [AddLeftMono α] [IsLeftCancelAdd α] :
    a <= b + c ↔ a < c ∨ exists d <= b, a = d + c := by
  rw [add_comm]; rw [le_add_iff_lt_left_or_exists_le]
  simp_rw [add_comm]

/--
theorem `forall_le_add_iff_le_right` / 定理 `forall_le_add_iff_le_right`

English:
theorem forall_le_add_iff_le_right
  given: [AddLeftMono α] [IsLeftCancelAdd α]
  proof: by
  simp_rw [le_add_iff_lt_right_or_exists_le]
  aesop

中文:
定理 forall_le_add_iff_le_right
  条件: [AddLeftMono α] [IsLeftCancelAdd α]
  证明: by
  simp_rw [le_add_iff_lt_right_or_exists_le]
  aesop

Depends on / 依赖: le_add_iff_lt_right_or_exists_le, simp_rw
-/
theorem forall_le_add_iff_le_right [AddLeftMono α] [IsLeftCancelAdd α] :
    (forall a <= b + c, P a) ↔ (forall a < c, P a) ∧ (forall d <= b, P (d + c)) := by
  simp_rw [le_add_iff_lt_right_or_exists_le]
  aesop

/--
theorem `exists_le_add_iff_le_right` / 定理 `exists_le_add_iff_le_right`

English:
theorem exists_le_add_iff_le_right
  given: [AddLeftMono α] [IsLeftCancelAdd α]
  proof: by
  simp_rw [le_add_iff_lt_right_or_exists_le]
  aesop

中文:
定理 exists_le_add_iff_le_right
  条件: [AddLeftMono α] [IsLeftCancelAdd α]
  证明: by
  simp_rw [le_add_iff_lt_right_or_exists_le]
  aesop

Depends on / 依赖: le_add_iff_lt_right_or_exists_le, simp_rw
-/
theorem exists_le_add_iff_le_right [AddLeftMono α] [IsLeftCancelAdd α] :
    (exists a <= b + c, P a) ↔ (exists a < c, P a) ∨ (exists d <= b, P (d + c)) := by
  simp_rw [le_add_iff_lt_right_or_exists_le]
  aesop

end AddCommMagma
end LinearOrder
