/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Order.MinMax

/-!
# Extra lemmas about intervals

This file contains lemmas about intervals that cannot be included into
`Mathlib/Order/Interval/Set/Basic.lean` because this would create an `import` cycle. Namely, lemmas
in this file can use definitions from `Data.Set.Lattice`, including `Disjoint`.

We consider various intersections and unions of half infinite intervals.
-/

public section


universe u v w

variable {ι : Sort u} {α : Type v} {β : Type w}

open Set

open OrderDual (toDual)

namespace Set

section Preorder

variable [Preorder α] {a b c : α}

to_dual_name_hint Disjoint Disjoint, Left Right

@[to_dual (attr := simp)]
/--
theorem `Iic_disjoint_Ioi` / 定理 `Iic_disjoint_Ioi`

English:
theorem Iic_disjoint_Ioi
  given: (h : a <= b)
  statement: Disjoint (Iic a) (Ioi b)
  proof: disjoint_left.mpr fun _ ha hb => (h.trans_lt hb).not_ge ha

@[to_dual (attr := simp)]

中文:
定理 Iic_disjoint_Ioi
  条件: (h : a <= b)
  结论: Disjoint (Iic a) (Ioi b)
  证明: disjoint_left.mpr fun _ ha hb => (h.trans_lt hb).not_ge ha

@[to_dual (attr := simp)]

Depends on / 依赖: disjoint_left, disjoint_left.mpr, h.trans_lt, not_ge, trans_lt
-/
theorem Iic_disjoint_Ioi (h : a <= b) : Disjoint (Iic a) (Ioi b) :=
  disjoint_left.mpr fun _ ha hb => (h.trans_lt hb).not_ge ha

@[to_dual (attr := simp)]
/--
theorem `Iio_disjoint_Ici` / 定理 `Iio_disjoint_Ici`

English:
theorem Iio_disjoint_Ici
  given: (h : a <= b)
  statement: Disjoint (Iio a) (Ici b)
  proof: disjoint_left.mpr fun _ ha hb => (h.trans_lt' ha).not_ge hb

@[simp]

中文:
定理 Iio_disjoint_Ici
  条件: (h : a <= b)
  结论: Disjoint (Iio a) (Ici b)
  证明: disjoint_left.mpr fun _ ha hb => (h.trans_lt' ha).not_ge hb

@[simp]

Depends on / 依赖: disjoint_left, disjoint_left.mpr, h.trans_lt, not_ge, trans_lt
-/
theorem Iio_disjoint_Ici (h : a <= b) : Disjoint (Iio a) (Ici b) :=
  disjoint_left.mpr fun _ ha hb => (h.trans_lt' ha).not_ge hb

@[simp]
/--
theorem `Iic_disjoint_Ioc` / 定理 `Iic_disjoint_Ioc`

English:
theorem Iic_disjoint_Ioc
  given: (h : a <= b)
  statement: Disjoint (Iic a) (Ioc b c)
  proof: (Iic_disjoint_Ioi h).mono le_rfl Ioc_subset_Ioi_self

@[simp]

中文:
定理 Iic_disjoint_Ioc
  条件: (h : a <= b)
  结论: Disjoint (Iic a) (Ioc b c)
  证明: (Iic_disjoint_Ioi h).mono le_rfl Ioc_subset_Ioi_self

@[simp]

Depends on / 依赖: Iic_disjoint_Ioi, Ioc_subset_Ioi_self, le_rfl
-/
theorem Iic_disjoint_Ioc (h : a <= b) : Disjoint (Iic a) (Ioc b c) :=
  (Iic_disjoint_Ioi h).mono le_rfl Ioc_subset_Ioi_self

@[simp]
/--
theorem `Ioc_disjoint_Ioc_of_le` / 定理 `Ioc_disjoint_Ioc_of_le`

English:
theorem Ioc_disjoint_Ioc_of_le
  given: {d : α} (h : b <= c)
  statement: Disjoint (Ioc a b) (Ioc c d)
  proof: (Iic_disjoint_Ioc h).mono Ioc_subset_Iic_self le_rfl

@[simp]

中文:
定理 Ioc_disjoint_Ioc_of_le
  条件: {d : α} (h : b <= c)
  结论: Disjoint (Ioc a b) (Ioc c d)
  证明: (Iic_disjoint_Ioc h).mono Ioc_subset_Iic_self le_rfl

@[simp]

Depends on / 依赖: Iic_disjoint_Ioc, Ioc_subset_Iic_self, le_rfl
-/
theorem Ioc_disjoint_Ioc_of_le {d : α} (h : b <= c) : Disjoint (Ioc a b) (Ioc c d) :=
  (Iic_disjoint_Ioc h).mono Ioc_subset_Iic_self le_rfl

@[simp]
/--
theorem `Ico_disjoint_Ico_same` / 定理 `Ico_disjoint_Ico_same`

English:
theorem Ico_disjoint_Ico_same
  statement: Disjoint (Ico a b) (Ico b c)
  proof: disjoint_left.mpr fun _ hab hbc => hab.2.not_ge hbc.1

@[to_dual (attr := simp)]

中文:
定理 Ico_disjoint_Ico_same
  结论: Disjoint (Ico a b) (Ico b c)
  证明: disjoint_left.mpr fun _ hab hbc => hab.2.not_ge hbc.1

@[to_dual (attr := simp)]

Depends on / 依赖: disjoint_left, disjoint_left.mpr, not_ge
-/
theorem Ico_disjoint_Ico_same : Disjoint (Ico a b) (Ico b c) :=
  disjoint_left.mpr fun _ hab hbc => hab.2.not_ge hbc.1

@[to_dual (attr := simp)]
/--
theorem `Ici_disjoint_Iic` / 定理 `Ici_disjoint_Iic`

English:
theorem Ici_disjoint_Iic
  statement: Disjoint (Ici a) (Iic b) ↔ ¬a <= b
  proof: by
  rw [Set.disjoint_iff_inter_eq_empty]; rw [Ici_inter_Iic]; rw [Icc_eq_empty_iff]

@[simp]

中文:
定理 Ici_disjoint_Iic
  结论: Disjoint (Ici a) (Iic b) ↔ ¬a <= b
  证明: by
  rw [Set.disjoint_iff_inter_eq_empty]; rw [Ici_inter_Iic]; rw [Icc_eq_empty_iff]

@[simp]

Depends on / 依赖: Icc_eq_empty_iff, Ici_inter_Iic, Set.disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty
-/
theorem Ici_disjoint_Iic : Disjoint (Ici a) (Iic b) ↔ ¬a <= b := by
  rw [Set.disjoint_iff_inter_eq_empty]; rw [Ici_inter_Iic]; rw [Icc_eq_empty_iff]

@[simp]
/--
theorem `Ioc_disjoint_Ioi` / 定理 `Ioc_disjoint_Ioi`

English:
theorem Ioc_disjoint_Ioi
  given: (h : b <= c)
  statement: Disjoint (Ioc a b) (Ioi c)
  proof: disjoint_left.mpr (fun _ hx hy => (hx.2.trans h).not_gt hy)

中文:
定理 Ioc_disjoint_Ioi
  条件: (h : b <= c)
  结论: Disjoint (Ioc a b) (Ioi c)
  证明: disjoint_left.mpr (fun _ hx hy => (hx.2.trans h).not_gt hy)

Depends on / 依赖: disjoint_left, disjoint_left.mpr, not_gt
-/
theorem Ioc_disjoint_Ioi (h : b <= c) : Disjoint (Ioc a b) (Ioi c) :=
  disjoint_left.mpr (fun _ hx hy => (hx.2.trans h).not_gt hy)

/--
theorem `Ioc_disjoint_Ioi_same` / 定理 `Ioc_disjoint_Ioi_same`

English:
theorem Ioc_disjoint_Ioi_same
  statement: Disjoint (Ioc a b) (Ioi b)
  proof: Ioc_disjoint_Ioi le_rfl

@[to_dual]

中文:
定理 Ioc_disjoint_Ioi_same
  结论: Disjoint (Ioc a b) (Ioi b)
  证明: Ioc_disjoint_Ioi le_rfl

@[to_dual]

Depends on / 依赖: Ioc_disjoint_Ioi, le_rfl
-/
theorem Ioc_disjoint_Ioi_same : Disjoint (Ioc a b) (Ioi b) :=
  Ioc_disjoint_Ioi le_rfl

@[to_dual]
/--
theorem `Ioi_disjoint_Iio_of_not_lt` / 定理 `Ioi_disjoint_Iio_of_not_lt`

English:
theorem Ioi_disjoint_Iio_of_not_lt
  given: (h : ¬a < b)
  statement: Disjoint (Ioi a) (Iio b)
  proof: disjoint_left.mpr fun _ hx hy => h (hx.trans hy)

@[to_dual]

中文:
定理 Ioi_disjoint_Iio_of_not_lt
  条件: (h : ¬a < b)
  结论: Disjoint (Ioi a) (Iio b)
  证明: disjoint_left.mpr fun _ hx hy => h (hx.trans hy)

@[to_dual]

Depends on / 依赖: disjoint_left, disjoint_left.mpr, hx.trans
-/
theorem Ioi_disjoint_Iio_of_not_lt (h : ¬a < b) : Disjoint (Ioi a) (Iio b) :=
  disjoint_left.mpr fun _ hx hy => h (hx.trans hy)

@[to_dual]
/--
theorem `Ioi_disjoint_Iio_of_le` / 定理 `Ioi_disjoint_Iio_of_le`

English:
theorem Ioi_disjoint_Iio_of_le
  given: (h : a <= b)
  statement: Disjoint (Ioi b) (Iio a)
  proof: Ioi_disjoint_Iio_of_not_lt (not_lt_of_ge h)

@[to_dual]

中文:
定理 Ioi_disjoint_Iio_of_le
  条件: (h : a <= b)
  结论: Disjoint (Ioi b) (Iio a)
  证明: Ioi_disjoint_Iio_of_not_lt (not_lt_of_ge h)

@[to_dual]

Depends on / 依赖: Ioi_disjoint_Iio_of_not_lt, not_lt_of_ge
-/
theorem Ioi_disjoint_Iio_of_le (h : a <= b) : Disjoint (Ioi b) (Iio a) :=
  Ioi_disjoint_Iio_of_not_lt (not_lt_of_ge h)

@[to_dual]
/--
theorem `Ioi_disjoint_Iio_same` / 定理 `Ioi_disjoint_Iio_same`

English:
theorem Ioi_disjoint_Iio_same
  statement: Disjoint (Ioi a) (Iio a)
  proof: Ioi_disjoint_Iio_of_le le_rfl

@[to_dual (attr := simp)]

中文:
定理 Ioi_disjoint_Iio_same
  结论: Disjoint (Ioi a) (Iio a)
  证明: Ioi_disjoint_Iio_of_le le_rfl

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_disjoint_Iio_of_le, le_rfl
-/
theorem Ioi_disjoint_Iio_same : Disjoint (Ioi a) (Iio a) :=
  Ioi_disjoint_Iio_of_le le_rfl

@[to_dual (attr := simp)]
/--
theorem `Ioi_disjoint_Iio_iff` / 定理 `Ioi_disjoint_Iio_iff`

English:
theorem Ioi_disjoint_Iio_iff
  given: [DenselyOrdered α]
  statement: Disjoint (Ioi a) (Iio b) ↔ ¬a < b
  proof: ⟨fun h hab => (exists_between hab).elim
    fun _ hc => h.notMem_of_mem_left hc.left hc.right,
    Ioi_disjoint_Iio_of_not_lt⟩

@[to_dual (attr := simp)]

中文:
定理 Ioi_disjoint_Iio_iff
  条件: [DenselyOrdered α]
  结论: Disjoint (Ioi a) (Iio b) ↔ ¬a < b
  证明: ⟨fun h hab => (exists_between hab).elim
    fun _ hc => h.notMem_of_mem_left hc.left hc.right,
    Ioi_disjoint_Iio_of_not_lt⟩

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_disjoint_Iio_of_not_lt, exists_between, h.notMem_of_mem_left, hc.left, hc.right, notMem_of_mem_left
-/
theorem Ioi_disjoint_Iio_iff [DenselyOrdered α] : Disjoint (Ioi a) (Iio b) ↔ ¬a < b :=
  ⟨fun h hab => (exists_between hab).elim
    fun _ hc => h.notMem_of_mem_left hc.left hc.right,
    Ioi_disjoint_Iio_of_not_lt⟩

@[to_dual (attr := simp)]
/--
theorem `iUnion_Iic` / 定理 `iUnion_Iic`

English:
theorem iUnion_Iic
  statement: ⋃ a : α, Iic a = univ
  proof: iUnion_eq_univ_iff.2 fun x => ⟨x, self_mem_Iic⟩

@[to_dual (attr := simp)]

中文:
定理 iUnion_Iic
  结论: ⋃ a : α, Iic a = univ
  证明: iUnion_eq_univ_iff.2 fun x => ⟨x, self_mem_Iic⟩

@[to_dual (attr := simp)]

Depends on / 依赖: iUnion_eq_univ_iff, self_mem_Iic
-/
theorem iUnion_Iic : ⋃ a : α, Iic a = univ :=
  iUnion_eq_univ_iff.2 fun x => ⟨x, self_mem_Iic⟩

@[to_dual (attr := simp)]
/--
theorem `iUnion_Icc_right` / 定理 `iUnion_Icc_right`

English:
theorem iUnion_Icc_right
  given: (a : α)
  statement: ⋃ b, Icc a b = Ici a
  proof: by
  simp only [← Ici_inter_Iic, ← inter_iUnion, iUnion_Iic, inter_univ]

@[to_dual (attr := simp)]

中文:
定理 iUnion_Icc_right
  条件: (a : α)
  结论: ⋃ b, Icc a b = Ici a
  证明: by
  simp only [← Ici_inter_Iic, ← inter_iUnion, iUnion_Iic, inter_univ]

@[to_dual (attr := simp)]

Depends on / 依赖: Ici_inter_Iic, iUnion_Iic, inter_iUnion, inter_univ
-/
theorem iUnion_Icc_right (a : α) : ⋃ b, Icc a b = Ici a := by
  simp only [← Ici_inter_Iic, ← inter_iUnion, iUnion_Iic, inter_univ]

@[to_dual (attr := simp)]
/--
theorem `iUnion_Ioc_right` / 定理 `iUnion_Ioc_right`

English:
theorem iUnion_Ioc_right
  given: (a : α)
  statement: ⋃ b, Ioc a b = Ioi a
  proof: by
  simp only [← Ioi_inter_Iic, ← inter_iUnion, iUnion_Iic, inter_univ]

@[to_dual (attr := simp)]

中文:
定理 iUnion_Ioc_right
  条件: (a : α)
  结论: ⋃ b, Ioc a b = Ioi a
  证明: by
  simp only [← Ioi_inter_Iic, ← inter_iUnion, iUnion_Iic, inter_univ]

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_inter_Iic, iUnion_Iic, inter_iUnion, inter_univ
-/
theorem iUnion_Ioc_right (a : α) : ⋃ b, Ioc a b = Ioi a := by
  simp only [← Ioi_inter_Iic, ← inter_iUnion, iUnion_Iic, inter_univ]

@[to_dual (attr := simp)]
/--
theorem `iUnion_Iio` / 定理 `iUnion_Iio`

English:
theorem iUnion_Iio
  given: [NoMaxOrder α]
  statement: ⋃ a : α, Iio a = univ
  proof: iUnion_eq_univ_iff.2 exists_gt

@[to_dual (attr := simp)]

中文:
定理 iUnion_Iio
  条件: [NoMaxOrder α]
  结论: ⋃ a : α, Iio a = univ
  证明: iUnion_eq_univ_iff.2 exists_gt

@[to_dual (attr := simp)]

Depends on / 依赖: exists_gt, iUnion_eq_univ_iff
-/
theorem iUnion_Iio [NoMaxOrder α] : ⋃ a : α, Iio a = univ :=
  iUnion_eq_univ_iff.2 exists_gt

@[to_dual (attr := simp)]
/--
theorem `iUnion_Ico_right` / 定理 `iUnion_Ico_right`

English:
theorem iUnion_Ico_right
  given: [NoMaxOrder α] (a : α)
  statement: ⋃ b, Ico a b = Ici a
  proof: by
  simp only [← Ici_inter_Iio, ← inter_iUnion, iUnion_Iio, inter_univ]

@[to_dual (attr := simp)]

中文:
定理 iUnion_Ico_right
  条件: [NoMaxOrder α] (a : α)
  结论: ⋃ b, Ico a b = Ici a
  证明: by
  simp only [← Ici_inter_Iio, ← inter_iUnion, iUnion_Iio, inter_univ]

@[to_dual (attr := simp)]

Depends on / 依赖: Ici_inter_Iio, iUnion_Iio, inter_iUnion, inter_univ
-/
theorem iUnion_Ico_right [NoMaxOrder α] (a : α) : ⋃ b, Ico a b = Ici a := by
  simp only [← Ici_inter_Iio, ← inter_iUnion, iUnion_Iio, inter_univ]

@[to_dual (attr := simp)]
/--
theorem `iUnion_Ioo_right` / 定理 `iUnion_Ioo_right`

English:
theorem iUnion_Ioo_right
  given: [NoMaxOrder α] (a : α)
  statement: ⋃ b, Ioo a b = Ioi a
  proof: by
  simp only [← Ioi_inter_Iio, ← inter_iUnion, iUnion_Iio, inter_univ]

中文:
定理 iUnion_Ioo_right
  条件: [NoMaxOrder α] (a : α)
  结论: ⋃ b, Ioo a b = Ioi a
  证明: by
  simp only [← Ioi_inter_Iio, ← inter_iUnion, iUnion_Iio, inter_univ]

Depends on / 依赖: Ioi_inter_Iio, iUnion_Iio, inter_iUnion, inter_univ
-/
theorem iUnion_Ioo_right [NoMaxOrder α] (a : α) : ⋃ b, Ioo a b = Ioi a := by
  simp only [← Ioi_inter_Iio, ← inter_iUnion, iUnion_Iio, inter_univ]

end Preorder

section LinearOrder

variable [LinearOrder α] {a₁ a₂ b₁ b₂ : α}

@[simp]
/--
theorem `Ico_disjoint_Ico` / 定理 `Ico_disjoint_Ico`

English:
theorem Ico_disjoint_Ico
  statement: Disjoint (Ico a₁ a₂) (Ico b₁ b₂) ↔ min a₂ b₂ <= max a₁ b₁
  proof: by
  simp_rw [Set.disjoint_iff_inter_eq_empty, Ico_inter_Ico, Ico_eq_empty_iff, not_lt]

@[simp]

中文:
定理 Ico_disjoint_Ico
  结论: Disjoint (Ico a₁ a₂) (Ico b₁ b₂) ↔ min a₂ b₂ <= max a₁ b₁
  证明: by
  simp_rw [Set.disjoint_iff_inter_eq_empty, Ico_inter_Ico, Ico_eq_empty_iff, not_lt]

@[simp]

Depends on / 依赖: Ico_eq_empty_iff, Ico_inter_Ico, Set.disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty, not_lt, simp_rw
-/
theorem Ico_disjoint_Ico : Disjoint (Ico a₁ a₂) (Ico b₁ b₂) ↔ min a₂ b₂ <= max a₁ b₁ := by
  simp_rw [Set.disjoint_iff_inter_eq_empty, Ico_inter_Ico, Ico_eq_empty_iff, not_lt]

@[simp]
/--
theorem `Ioc_disjoint_Ioc` / 定理 `Ioc_disjoint_Ioc`

English:
theorem Ioc_disjoint_Ioc
  statement: Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ <= max a₁ b₁
  proof: by
  have h : _ ↔ min (toDual a₁) (toDual b₁) <= max (toDual a₂) (toDual b₂) := Ico_disjoint_Ico
  simpa only [Ico_toDual] using! h

@[simp]

中文:
定理 Ioc_disjoint_Ioc
  结论: Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ <= max a₁ b₁
  证明: by
  have h : _ ↔ min (toDual a₁) (toDual b₁) <= max (toDual a₂) (toDual b₂) := Ico_disjoint_Ico
  simpa only [Ico_toDual] using! h

@[simp]

Depends on / 依赖: Ico_disjoint_Ico, Ico_toDual, toDual
-/
theorem Ioc_disjoint_Ioc : Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ <= max a₁ b₁ := by
  have h : _ ↔ min (toDual a₁) (toDual b₁) <= max (toDual a₂) (toDual b₂) := Ico_disjoint_Ico
  simpa only [Ico_toDual] using! h

@[simp]
/--
theorem `Ioo_disjoint_Ioo` / 定理 `Ioo_disjoint_Ioo`

English:
theorem Ioo_disjoint_Ioo
  given: [DenselyOrdered α]
  proof: by
  simp_rw [Set.disjoint_iff_inter_eq_empty, Ioo_inter_Ioo, Ioo_eq_empty_iff, not_lt]

中文:
定理 Ioo_disjoint_Ioo
  条件: [DenselyOrdered α]
  证明: by
  simp_rw [Set.disjoint_iff_inter_eq_empty, Ioo_inter_Ioo, Ioo_eq_empty_iff, not_lt]

Depends on / 依赖: Ioo_eq_empty_iff, Ioo_inter_Ioo, Set.disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty, not_lt, simp_rw
-/
theorem Ioo_disjoint_Ioo [DenselyOrdered α] :
    Disjoint (Set.Ioo a₁ a₂) (Set.Ioo b₁ b₂) ↔ min a₂ b₂ <= max a₁ b₁ := by
  simp_rw [Set.disjoint_iff_inter_eq_empty, Ioo_inter_Ioo, Ioo_eq_empty_iff, not_lt]

/--
theorem `eq_of_Ico_disjoint` / 定理 `eq_of_Ico_disjoint`

English:
theorem eq_of_Ico_disjoint
  statement: {x₁ x₂ y₁ y₂ : α} (h : Disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂)
  proof: by
  rw [Ico_disjoint_Ico]; rw [min_eq_left (le_of_lt h2.2)]; rw [le_max_iff] at h
  apply le_antisymm h2.1
  exact h.elim (fun h => absurd hx (not_lt_of_ge h)) id

@[simp]

中文:
定理 eq_of_Ico_disjoint
  结论: {x₁ x₂ y₁ y₂ : α} (h : Disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂)
  证明: by
  rw [Ico_disjoint_Ico]; rw [min_eq_left (le_of_lt h2.2)]; rw [le_max_iff] at h
  apply le_antisymm h2.1
  exact h.elim (fun h => absurd hx (not_lt_of_ge h)) id

@[simp]

Depends on / 依赖: Ico_disjoint_Ico, absurd, h.elim, le_antisymm, le_max_iff, le_of_lt, min_eq_left, not_lt_of_ge
-/
theorem eq_of_Ico_disjoint {x₁ x₂ y₁ y₂ : α} (h : Disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂)
    (h2 : x₂ in Ico y₁ y₂) : y₁ = x₂ := by
  rw [Ico_disjoint_Ico]; rw [min_eq_left (le_of_lt h2.2)]; rw [le_max_iff] at h
  apply le_antisymm h2.1
  exact h.elim (fun h => absurd hx (not_lt_of_ge h)) id

@[simp]
/--
theorem `iUnion_Ico_eq_Iio_self_iff` / 定理 `iUnion_Ico_eq_Iio_self_iff`

English:
theorem iUnion_Ico_eq_Iio_self_iff
  given: {f : ι -> α} {a : α}
  proof: by
  simp [← Ici_inter_Iio, ← iUnion_inter, subset_def]

@[simp]

中文:
定理 iUnion_Ico_eq_Iio_self_iff
  条件: {f : ι -> α} {a : α}
  证明: by
  simp [← Ici_inter_Iio, ← iUnion_inter, subset_def]

@[simp]

Depends on / 依赖: Ici_inter_Iio, iUnion_inter, subset_def
-/
theorem iUnion_Ico_eq_Iio_self_iff {f : ι -> α} {a : α} :
    ⋃ i, Ico (f i) a = Iio a ↔ forall x < a, exists i, f i <= x := by
  simp [← Ici_inter_Iio, ← iUnion_inter, subset_def]

@[simp]
/--
theorem `iUnion_Ioc_eq_Ioi_self_iff` / 定理 `iUnion_Ioc_eq_Ioi_self_iff`

English:
theorem iUnion_Ioc_eq_Ioi_self_iff
  given: {f : ι -> α} {a : α}
  proof: by
  simp [← Ioi_inter_Iic, ← inter_iUnion, subset_def]

@[to_dual (attr := simp)]

中文:
定理 iUnion_Ioc_eq_Ioi_self_iff
  条件: {f : ι -> α} {a : α}
  证明: by
  simp [← Ioi_inter_Iic, ← inter_iUnion, subset_def]

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_inter_Iic, inter_iUnion, subset_def
-/
theorem iUnion_Ioc_eq_Ioi_self_iff {f : ι -> α} {a : α} :
    ⋃ i, Ioc a (f i) = Ioi a ↔ forall x, a < x -> exists i, x <= f i := by
  simp [← Ioi_inter_Iic, ← inter_iUnion, subset_def]

@[to_dual (attr := simp)]
/--
theorem `iUnion_Icc_eq_Ici_self_iff` / 定理 `iUnion_Icc_eq_Ici_self_iff`

English:
theorem iUnion_Icc_eq_Ici_self_iff
  given: {f : ι -> α} {a : α}
  proof: by
  simp [← Ici_inter_Iic, ← inter_iUnion, subset_def]

@[simp]

中文:
定理 iUnion_Icc_eq_Ici_self_iff
  条件: {f : ι -> α} {a : α}
  证明: by
  simp [← Ici_inter_Iic, ← inter_iUnion, subset_def]

@[simp]

Depends on / 依赖: Ici_inter_Iic, inter_iUnion, subset_def
-/
theorem iUnion_Icc_eq_Ici_self_iff {f : ι -> α} {a : α} :
    ⋃ i, Icc a (f i) = Ici a ↔ forall x >= a, exists i, x <= f i := by
  simp [← Ici_inter_Iic, ← inter_iUnion, subset_def]

@[simp]
/--
theorem `biUnion_Ico_eq_Iio_self_iff` / 定理 `biUnion_Ico_eq_Iio_self_iff`

English:
theorem biUnion_Ico_eq_Iio_self_iff
  given: {p : ι -> Prop} {f : forall i, p i -> α} {a : α}
  proof: by
  simp [← Ici_inter_Iio, ← iUnion_inter, subset_def]

@[simp]

中文:
定理 biUnion_Ico_eq_Iio_self_iff
  条件: {p : ι -> 命题} {f : 对任意 i, p i -> α} {a : α}
  证明: by
  simp [← Ici_inter_Iio, ← iUnion_inter, subset_def]

@[simp]

Depends on / 依赖: Ici_inter_Iio, iUnion_inter, subset_def
-/
theorem biUnion_Ico_eq_Iio_self_iff {p : ι -> Prop} {f : forall i, p i -> α} {a : α} :
    ⋃ (i) (hi : p i), Ico (f i hi) a = Iio a ↔ forall x < a, exists i hi, f i hi <= x := by
  simp [← Ici_inter_Iio, ← iUnion_inter, subset_def]

@[simp]
/--
theorem `biUnion_Ioc_eq_Ioi_self_iff` / 定理 `biUnion_Ioc_eq_Ioi_self_iff`

English:
theorem biUnion_Ioc_eq_Ioi_self_iff
  given: {p : ι -> Prop} {f : forall i, p i -> α} {a : α}
  proof: by
  simp [← Ioi_inter_Iic, ← inter_iUnion, subset_def]

中文:
定理 biUnion_Ioc_eq_Ioi_self_iff
  条件: {p : ι -> 命题} {f : 对任意 i, p i -> α} {a : α}
  证明: by
  simp [← Ioi_inter_Iic, ← inter_iUnion, subset_def]

Depends on / 依赖: Ioi_inter_Iic, inter_iUnion, subset_def
-/
theorem biUnion_Ioc_eq_Ioi_self_iff {p : ι -> Prop} {f : forall i, p i -> α} {a : α} :
    ⋃ (i) (hi : p i), Ioc a (f i hi) = Ioi a ↔ forall x, a < x -> exists i hi, x <= f i hi := by
  simp [← Ioi_inter_Iic, ← inter_iUnion, subset_def]

end LinearOrder

end Set

section UnionIxx

variable [LinearOrder α] {s : Set α} {a : α} {f : ι -> α}

/--
theorem `IsGLB.biUnion_Ioi_eq` / 定理 `IsGLB.biUnion_Ioi_eq`

English:
theorem IsGLB.biUnion_Ioi_eq
  given: (h : IsGLB s a)
  statement: ⋃ x in s, Ioi x = Ioi a
  proof: by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ioi_subset_Ioi (h.1 hx)
  · rcases h.exists_between hx with ⟨y, hys, _, hyx⟩
    exact mem_biUnion hys hyx

中文:
定理 IsGLB.biUnion_Ioi_eq
  条件: (h : IsGLB s a)
  结论: ⋃ x in s, Ioi x = Ioi a
  证明: by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ioi_subset_Ioi (h.1 hx)
  · rcases h.exists_between hx with ⟨y, hys, _, hyx⟩
    exact mem_biUnion hys hyx

Depends on / 依赖: Ioi_subset_Ioi, antisymm, exists_between, h.exists_between, mem_biUnion
-/
theorem IsGLB.biUnion_Ioi_eq (h : IsGLB s a) : ⋃ x in s, Ioi x = Ioi a := by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ioi_subset_Ioi (h.1 hx)
  · rcases h.exists_between hx with ⟨y, hys, _, hyx⟩
    exact mem_biUnion hys hyx

/--
theorem `IsGLB.iUnion_Ioi_eq` / 定理 `IsGLB.iUnion_Ioi_eq`

English:
theorem IsGLB.iUnion_Ioi_eq
  given: (h : IsGLB (range f) a)
  statement: ⋃ x, Ioi (f x) = Ioi a
  proof: biUnion_range.symm.trans h.biUnion_Ioi_eq

中文:
定理 IsGLB.iUnion_Ioi_eq
  条件: (h : IsGLB (range f) a)
  结论: ⋃ x, Ioi (f x) = Ioi a
  证明: biUnion_range.symm.trans h.biUnion_Ioi_eq

Depends on / 依赖: biUnion_Ioi_eq, biUnion_range, biUnion_range.symm.trans, h.biUnion_Ioi_eq
-/
theorem IsGLB.iUnion_Ioi_eq (h : IsGLB (range f) a) : ⋃ x, Ioi (f x) = Ioi a :=
  biUnion_range.symm.trans h.biUnion_Ioi_eq

/--
theorem `IsLUB.biUnion_Iio_eq` / 定理 `IsLUB.biUnion_Iio_eq`

English:
theorem IsLUB.biUnion_Iio_eq
  given: (h : IsLUB s a)
  statement: ⋃ x in s, Iio x = Iio a
  proof: h.dual.biUnion_Ioi_eq

中文:
定理 IsLUB.biUnion_Iio_eq
  条件: (h : IsLUB s a)
  结论: ⋃ x in s, Iio x = Iio a
  证明: h.dual.biUnion_Ioi_eq

Depends on / 依赖: biUnion_Ioi_eq, h.dual.biUnion_Ioi_eq
-/
theorem IsLUB.biUnion_Iio_eq (h : IsLUB s a) : ⋃ x in s, Iio x = Iio a :=
  h.dual.biUnion_Ioi_eq

/--
theorem `IsLUB.iUnion_Iio_eq` / 定理 `IsLUB.iUnion_Iio_eq`

English:
theorem IsLUB.iUnion_Iio_eq
  given: (h : IsLUB (range f) a)
  statement: ⋃ x, Iio (f x) = Iio a
  proof: h.dual.iUnion_Ioi_eq

中文:
定理 IsLUB.iUnion_Iio_eq
  条件: (h : IsLUB (range f) a)
  结论: ⋃ x, Iio (f x) = Iio a
  证明: h.dual.iUnion_Ioi_eq

Depends on / 依赖: h.dual.iUnion_Ioi_eq, iUnion_Ioi_eq
-/
theorem IsLUB.iUnion_Iio_eq (h : IsLUB (range f) a) : ⋃ x, Iio (f x) = Iio a :=
  h.dual.iUnion_Ioi_eq

/--
theorem `iUnion_Ioi_eq_Ioi_iInf` / 定理 `iUnion_Ioi_eq_Ioi_iInf`

English:
theorem iUnion_Ioi_eq_Ioi_iInf
  given: {R : Type*} [CompleteLinearOrder R] {f : ι -> R}
  proof: isGLB_iInf.iUnion_Ioi_eq

中文:
定理 iUnion_Ioi_eq_Ioi_iInf
  条件: {R : 类型} [CompleteLinearOrder R] {f : ι -> R}
  证明: isGLB_iInf.iUnion_Ioi_eq

Depends on / 依赖: HomogeneousIdeal, Ideal.homogeneousCore.gc, IsGreatest, IsGreatest.isLUB, IsLUB.sSup_eq, Monotone, coe_mono, coe_mono.map_isGreatest, convert, homogeneousCore, iUnion_Ioi_eq, isGLB_iInf, isGLB_iInf.iUnion_Ioi_eq, isGreatest_u, isHomogeneous, map_isGreatest, mem_image, mem_ofPred_eq, sSup_eq, toIdeal
-/
theorem iUnion_Ioi_eq_Ioi_iInf {R : Type*} [CompleteLinearOrder R] {f : ι -> R} :
    ⋃ i : ι, Ioi (f i) = Ioi (⨅ i, f i) :=
  isGLB_iInf.iUnion_Ioi_eq

/--
theorem `iUnion_Iio_eq_Iio_iSup` / 定理 `iUnion_Iio_eq_Iio_iSup`

English:
theorem iUnion_Iio_eq_Iio_iSup
  given: {R : Type*} [CompleteLinearOrder R] {f : ι -> R}
  proof: isLUB_iSup.iUnion_Iio_eq

中文:
定理 iUnion_Iio_eq_Iio_iSup
  条件: {R : 类型} [CompleteLinearOrder R] {f : ι -> R}
  证明: isLUB_iSup.iUnion_Iio_eq

Depends on / 依赖: iUnion_Iio_eq, isLUB_iSup, isLUB_iSup.iUnion_Iio_eq
-/
theorem iUnion_Iio_eq_Iio_iSup {R : Type*} [CompleteLinearOrder R] {f : ι -> R} :
    ⋃ i : ι, Iio (f i) = Iio (⨆ i, f i) :=
  isLUB_iSup.iUnion_Iio_eq

/--
theorem `IsGLB.biUnion_Ici_eq_Ioi` / 定理 `IsGLB.biUnion_Ici_eq_Ioi`

English:
theorem IsGLB.biUnion_Ici_eq_Ioi
  given: (a_glb : IsGLB s a) (a_notMem : a ∉ s)
  proof: by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ici_subset_Ioi.mpr (lt_of_le_of_ne (a_glb.1 hx) fun h => (h ▸ a_notMem) hx)
  · rcases a_glb.exists_between hx with ⟨y, hys, _, hyx⟩
    rw [mem_iUnion₂]
    exact ⟨y, hys, hyx.le⟩

中文:
定理 IsGLB.biUnion_Ici_eq_Ioi
  条件: (a_glb : IsGLB s a) (a_notMem : a ∉ s)
  证明: by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ici_subset_Ioi.mpr (lt_of_le_of_ne (a_glb.1 hx) fun h => (h ▸ a_notMem) hx)
  · rcases a_glb.exists_between hx with ⟨y, hys, _, hyx⟩
    rw [mem_iUnion₂]
    exact ⟨y, hys, hyx.le⟩

Depends on / 依赖: Ici_subset_Ioi, Ici_subset_Ioi.mpr, a_glb, a_glb.exists_between, a_notMem, antisymm, exists_between, hyx.le, lt_of_le_of_ne
-/
theorem IsGLB.biUnion_Ici_eq_Ioi (a_glb : IsGLB s a) (a_notMem : a ∉ s) :
    ⋃ x in s, Ici x = Ioi a := by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ici_subset_Ioi.mpr (lt_of_le_of_ne (a_glb.1 hx) fun h => (h ▸ a_notMem) hx)
  · rcases a_glb.exists_between hx with ⟨y, hys, _, hyx⟩
    rw [mem_iUnion₂]
    exact ⟨y, hys, hyx.le⟩

/--
theorem `IsGLB.biUnion_Ici_eq_Ici` / 定理 `IsGLB.biUnion_Ici_eq_Ici`

English:
theorem IsGLB.biUnion_Ici_eq_Ici
  given: (a_glb : IsGLB s a) (a_mem : a in s)
  proof: by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ici_subset_Ici.mpr (mem_lowerBounds.mp a_glb.1 x hx)
  · exact mem_iUnion₂.mpr ⟨a, a_mem, hx⟩

中文:
定理 IsGLB.biUnion_Ici_eq_Ici
  条件: (a_glb : IsGLB s a) (a_mem : a in s)
  证明: by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ici_subset_Ici.mpr (mem_lowerBounds.mp a_glb.1 x hx)
  · exact mem_iUnion₂.mpr ⟨a, a_mem, hx⟩

Depends on / 依赖: Ici_subset_Ici, Ici_subset_Ici.mpr, a_glb, a_mem, antisymm, mem_lowerBounds, mem_lowerBounds.mp
-/
theorem IsGLB.biUnion_Ici_eq_Ici (a_glb : IsGLB s a) (a_mem : a in s) :
    ⋃ x in s, Ici x = Ici a := by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ici_subset_Ici.mpr (mem_lowerBounds.mp a_glb.1 x hx)
  · exact mem_iUnion₂.mpr ⟨a, a_mem, hx⟩

/--
theorem `IsLUB.biUnion_Iic_eq_Iio` / 定理 `IsLUB.biUnion_Iic_eq_Iio`

English:
theorem IsLUB.biUnion_Iic_eq_Iio
  given: (a_lub : IsLUB s a) (a_notMem : a ∉ s)
  proof: a_lub.dual.biUnion_Ici_eq_Ioi a_notMem

中文:
定理 IsLUB.biUnion_Iic_eq_Iio
  条件: (a_lub : IsLUB s a) (a_notMem : a ∉ s)
  证明: a_lub.dual.biUnion_Ici_eq_Ioi a_notMem

Depends on / 依赖: a_lub, a_lub.dual.biUnion_Ici_eq_Ioi, a_notMem, biUnion_Ici_eq_Ioi
-/
theorem IsLUB.biUnion_Iic_eq_Iio (a_lub : IsLUB s a) (a_notMem : a ∉ s) :
    ⋃ x in s, Iic x = Iio a :=
  a_lub.dual.biUnion_Ici_eq_Ioi a_notMem

/--
theorem `IsLUB.biUnion_Iic_eq_Iic` / 定理 `IsLUB.biUnion_Iic_eq_Iic`

English:
theorem IsLUB.biUnion_Iic_eq_Iic
  given: (a_lub : IsLUB s a) (a_mem : a in s)
  statement: ⋃ x in s, Iic x = Iic a
  proof: a_lub.dual.biUnion_Ici_eq_Ici a_mem

中文:
定理 IsLUB.biUnion_Iic_eq_Iic
  条件: (a_lub : IsLUB s a) (a_mem : a in s)
  结论: ⋃ x in s, Iic x = Iic a
  证明: a_lub.dual.biUnion_Ici_eq_Ici a_mem

Depends on / 依赖: a_lub, a_lub.dual.biUnion_Ici_eq_Ici, a_mem, biUnion_Ici_eq_Ici
-/
theorem IsLUB.biUnion_Iic_eq_Iic (a_lub : IsLUB s a) (a_mem : a in s) : ⋃ x in s, Iic x = Iic a :=
  a_lub.dual.biUnion_Ici_eq_Ici a_mem

/--
theorem `iUnion_Ici_eq_Ioi_iInf` / 定理 `iUnion_Ici_eq_Ioi_iInf`

English:
theorem iUnion_Ici_eq_Ioi_iInf
  statement: {R : Type*} [CompleteLinearOrder R] {f : ι -> R}
  proof: by
  simp only [← IsGLB.biUnion_Ici_eq_Ioi (@isGLB_iInf _ _ _ f) no_least_elem, mem_range,
    iUnion_exists, iUnion_iUnion_eq']

中文:
定理 iUnion_Ici_eq_Ioi_iInf
  结论: {R : 类型} [CompleteLinearOrder R] {f : ι -> R}
  证明: by
  simp only [← IsGLB.biUnion_Ici_eq_Ioi (@isGLB_iInf _ _ _ f) no_least_elem, mem_range,
    iUnion_exists, iUnion_iUnion_eq']

Depends on / 依赖: IsGLB.biUnion_Ici_eq_Ioi, biUnion_Ici_eq_Ioi, iUnion_exists, iUnion_iUnion_eq, isGLB_iInf, mem_range, no_least_elem
-/
theorem iUnion_Ici_eq_Ioi_iInf {R : Type*} [CompleteLinearOrder R] {f : ι -> R}
    (no_least_elem : ⨅ i, f i ∉ range f) : ⋃ i : ι, Ici (f i) = Ioi (⨅ i, f i) := by
  simp only [← IsGLB.biUnion_Ici_eq_Ioi (@isGLB_iInf _ _ _ f) no_least_elem, mem_range,
    iUnion_exists, iUnion_iUnion_eq']

/--
theorem `iUnion_Iic_eq_Iio_iSup` / 定理 `iUnion_Iic_eq_Iio_iSup`

English:
theorem iUnion_Iic_eq_Iio_iSup
  statement: {R : Type*} [CompleteLinearOrder R] {f : ι -> R}
  proof: @iUnion_Ici_eq_Ioi_iInf ι (OrderDual R) _ f no_greatest_elem

中文:
定理 iUnion_Iic_eq_Iio_iSup
  结论: {R : 类型} [CompleteLinearOrder R] {f : ι -> R}
  证明: @iUnion_Ici_eq_Ioi_iInf ι (OrderDual R) _ f no_greatest_elem

Depends on / 依赖: OrderDual, iUnion_Ici_eq_Ioi_iInf, no_greatest_elem
-/
theorem iUnion_Iic_eq_Iio_iSup {R : Type*} [CompleteLinearOrder R] {f : ι -> R}
    (no_greatest_elem : (⨆ i, f i) ∉ range f) : ⋃ i : ι, Iic (f i) = Iio (⨆ i, f i) :=
  @iUnion_Ici_eq_Ioi_iInf ι (OrderDual R) _ f no_greatest_elem

/--
theorem `iUnion_Ici_eq_Ici_iInf` / 定理 `iUnion_Ici_eq_Ici_iInf`

English:
theorem iUnion_Ici_eq_Ici_iInf
  statement: {R : Type*} [CompleteLinearOrder R] {f : ι -> R}
  proof: by
  simp only [← IsGLB.biUnion_Ici_eq_Ici (@isGLB_iInf _ _ _ f) has_least_elem, mem_range,
    iUnion_exists, iUnion_iUnion_eq']

中文:
定理 iUnion_Ici_eq_Ici_iInf
  结论: {R : 类型} [CompleteLinearOrder R] {f : ι -> R}
  证明: by
  simp only [← IsGLB.biUnion_Ici_eq_Ici (@isGLB_iInf _ _ _ f) has_least_elem, mem_range,
    iUnion_exists, iUnion_iUnion_eq']

Depends on / 依赖: IsGLB.biUnion_Ici_eq_Ici, biUnion_Ici_eq_Ici, has_least_elem, iUnion_exists, iUnion_iUnion_eq, isGLB_iInf, mem_range
-/
theorem iUnion_Ici_eq_Ici_iInf {R : Type*} [CompleteLinearOrder R] {f : ι -> R}
    (has_least_elem : (⨅ i, f i) in range f) : ⋃ i : ι, Ici (f i) = Ici (⨅ i, f i) := by
  simp only [← IsGLB.biUnion_Ici_eq_Ici (@isGLB_iInf _ _ _ f) has_least_elem, mem_range,
    iUnion_exists, iUnion_iUnion_eq']

/--
theorem `iUnion_Iic_eq_Iic_iSup` / 定理 `iUnion_Iic_eq_Iic_iSup`

English:
theorem iUnion_Iic_eq_Iic_iSup
  statement: {R : Type*} [CompleteLinearOrder R] {f : ι -> R}
  proof: @iUnion_Ici_eq_Ici_iInf ι (OrderDual R) _ f has_greatest_elem

中文:
定理 iUnion_Iic_eq_Iic_iSup
  结论: {R : 类型} [CompleteLinearOrder R] {f : ι -> R}
  证明: @iUnion_Ici_eq_Ici_iInf ι (OrderDual R) _ f has_greatest_elem

Depends on / 依赖: OrderDual, has_greatest_elem, iUnion_Ici_eq_Ici_iInf
-/
theorem iUnion_Iic_eq_Iic_iSup {R : Type*} [CompleteLinearOrder R] {f : ι -> R}
    (has_greatest_elem : (⨆ i, f i) in range f) : ⋃ i : ι, Iic (f i) = Iic (⨆ i, f i) :=
  @iUnion_Ici_eq_Ici_iInf ι (OrderDual R) _ f has_greatest_elem

/--
theorem `iUnion_Iio_eq_univ_iff` / 定理 `iUnion_Iio_eq_univ_iff`

English:
theorem iUnion_Iio_eq_univ_iff
  statement: ⋃ i, Iio (f i) = univ ↔ (¬ BddAbove (range f))
  proof: by
  simp [not_bddAbove_iff, Set.eq_univ_iff_forall]

中文:
定理 iUnion_Iio_eq_univ_iff
  结论: ⋃ i, Iio (f i) = univ ↔ (¬ BddAbove (range f))
  证明: by
  simp [not_bddAbove_iff, Set.eq_univ_iff_forall]

Depends on / 依赖: Set.eq_univ_iff_forall, eq_univ_iff_forall, not_bddAbove_iff
-/
theorem iUnion_Iio_eq_univ_iff : ⋃ i, Iio (f i) = univ ↔ (¬ BddAbove (range f)) := by
  simp [not_bddAbove_iff, Set.eq_univ_iff_forall]

/--
theorem `iUnion_Iic_of_not_bddAbove_range` / 定理 `iUnion_Iic_of_not_bddAbove_range`

English:
theorem iUnion_Iic_of_not_bddAbove_range
  given: (hf : ¬ BddAbove (range f))
  statement: ⋃ i, Iic (f i) = univ
  proof: by
  refine Set.eq_univ_of_subset ?_ (iUnion_Iio_eq_univ_iff.mpr hf)
  gcongr
  exact Iio_subset_Iic_self

中文:
定理 iUnion_Iic_of_not_bddAbove_range
  条件: (hf : ¬ BddAbove (range f))
  结论: ⋃ i, Iic (f i) = univ
  证明: by
  refine Set.eq_univ_of_subset ?_ (iUnion_Iio_eq_univ_iff.mpr hf)
  gcongr
  exact Iio_subset_Iic_self

Depends on / 依赖: Iio_subset_Iic_self, Set.eq_univ_of_subset, eq_univ_of_subset, iUnion_Iio_eq_univ_iff, iUnion_Iio_eq_univ_iff.mpr
-/
theorem iUnion_Iic_of_not_bddAbove_range (hf : ¬ BddAbove (range f)) : ⋃ i, Iic (f i) = univ := by
  refine Set.eq_univ_of_subset ?_ (iUnion_Iio_eq_univ_iff.mpr hf)
  gcongr
  exact Iio_subset_Iic_self

/--
theorem `iInter_Iic_eq_empty_iff` / 定理 `iInter_Iic_eq_empty_iff`

English:
theorem iInter_Iic_eq_empty_iff
  statement: ⋂ i, Iic (f i) = ∅ ↔ ¬ BddBelow (range f)
  proof: by
  simp [not_bddBelow_iff, Set.eq_empty_iff_forall_notMem]

中文:
定理 iInter_Iic_eq_empty_iff
  结论: ⋂ i, Iic (f i) = ∅ ↔ ¬ BddBelow (range f)
  证明: by
  simp [not_bddBelow_iff, Set.eq_empty_iff_forall_notMem]

Depends on / 依赖: Set.eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem, not_bddBelow_iff
-/
theorem iInter_Iic_eq_empty_iff : ⋂ i, Iic (f i) = ∅ ↔ ¬ BddBelow (range f) := by
  simp [not_bddBelow_iff, Set.eq_empty_iff_forall_notMem]

/--
theorem `iInter_Iio_of_not_bddBelow_range` / 定理 `iInter_Iio_of_not_bddBelow_range`

English:
theorem iInter_Iio_of_not_bddBelow_range
  given: (hf : ¬ BddBelow (range f))
  statement: ⋂ i, Iio (f i) = ∅
  proof: by
  refine eq_empty_of_subset_empty ?_
  rw [← iInter_Iic_eq_empty_iff.mpr hf]
  gcongr
  exact Iio_subset_Iic_self

中文:
定理 iInter_Iio_of_not_bddBelow_range
  条件: (hf : ¬ BddBelow (range f))
  结论: ⋂ i, Iio (f i) = ∅
  证明: by
  refine eq_empty_of_subset_empty ?_
  rw [← iInter_Iic_eq_empty_iff.mpr hf]
  gcongr
  exact Iio_subset_Iic_self

Depends on / 依赖: Iio_subset_Iic_self, eq_empty_of_subset_empty, iInter_Iic_eq_empty_iff, iInter_Iic_eq_empty_iff.mpr
-/
theorem iInter_Iio_of_not_bddBelow_range (hf : ¬ BddBelow (range f)) : ⋂ i, Iio (f i) = ∅ := by
  refine eq_empty_of_subset_empty ?_
  rw [← iInter_Iic_eq_empty_iff.mpr hf]
  gcongr
  exact Iio_subset_Iic_self

end UnionIxx
