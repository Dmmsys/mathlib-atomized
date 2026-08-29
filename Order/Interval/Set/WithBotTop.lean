/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.WithBot

/-!
# Intervals in `WithTop α` and `WithBot α`

In this file we prove various lemmas about `Set.image`s and `Set.preimage`s of intervals under
`some : α → WithTop α` and `some : α → WithBot α`.
-/

public section

open Set

variable {α : Type*}

namespace WithTop

@[to_dual (attr := simp)]
/--
theorem `preimage_coe_top` / 定理 `preimage_coe_top`

English:
theorem preimage_coe_top
  statement: (some : α -> WithTop α) ⁻¹' {⊤} = (∅ : Set α)
  proof: eq_empty_of_subset_empty fun _ => coe_ne_top

中文:
定理 preimage_coe_top
  结论: (some : α -> WithTop α) ⁻¹' {⊤} = (∅ : Set α)
  证明: eq_empty_of_subset_empty fun _ => coe_ne_top

Depends on / 依赖: IsTwoSided, coe_ne_top, eq_empty_of_subset_empty
-/
theorem preimage_coe_top : (some : α -> WithTop α) ⁻¹' {⊤} = (∅ : Set α) :=
  eq_empty_of_subset_empty fun _ => coe_ne_top

variable [Preorder α] {a b : α}

@[to_dual]
/--
theorem `range_coe` / 定理 `range_coe`

English:
theorem range_coe
  statement: range (some : α -> WithTop α) = Iio ⊤
  proof: by
  ext; simp [mem_range, WithTop.lt_top_iff_ne_top, ne_top_iff_exists]

@[to_dual (attr := simp)]

中文:
定理 range_coe
  结论: range (some : α -> WithTop α) = Iio ⊤
  证明: by
  ext; simp [mem_range, WithTop.lt_top_iff_ne_top, ne_top_iff_exists]

@[to_dual (attr := simp)]

Depends on / 依赖: IsTwoSided, WithTop, WithTop.lt_top_iff_ne_top, lt_top_iff_ne_top, mem_range, ne_top_iff_exists
-/
theorem range_coe : range (some : α -> WithTop α) = Iio ⊤ := by
  ext; simp [mem_range, WithTop.lt_top_iff_ne_top, ne_top_iff_exists]

@[to_dual (attr := simp)]
/--
theorem `preimage_coe_Ioi` / 定理 `preimage_coe_Ioi`

English:
theorem preimage_coe_Ioi
  statement: (some : α -> WithTop α) ⁻¹' Ioi a = Ioi a
  proof: ext fun _ => coe_lt_coe

@[to_dual (attr := simp)]

中文:
定理 preimage_coe_Ioi
  结论: (some : α -> WithTop α) ⁻¹' Ioi a = Ioi a
  证明: ext fun _ => coe_lt_coe

@[to_dual (attr := simp)]

Depends on / 依赖: IsTwoSided, coe_lt_coe
-/
theorem preimage_coe_Ioi : (some : α -> WithTop α) ⁻¹' Ioi a = Ioi a :=
  ext fun _ => coe_lt_coe

@[to_dual (attr := simp)]
/--
theorem `preimage_coe_Ici` / 定理 `preimage_coe_Ici`

English:
theorem preimage_coe_Ici
  statement: (some : α -> WithTop α) ⁻¹' Ici a = Ici a
  proof: ext fun _ => coe_le_coe

@[to_dual (attr := simp)]

中文:
定理 preimage_coe_Ici
  结论: (some : α -> WithTop α) ⁻¹' Ici a = Ici a
  证明: ext fun _ => coe_le_coe

@[to_dual (attr := simp)]

Depends on / 依赖: coe_le_coe
-/
theorem preimage_coe_Ici : (some : α -> WithTop α) ⁻¹' Ici a = Ici a :=
  ext fun _ => coe_le_coe

@[to_dual (attr := simp)]
/--
theorem `preimage_coe_Iio` / 定理 `preimage_coe_Iio`

English:
theorem preimage_coe_Iio
  statement: (some : α -> WithTop α) ⁻¹' Iio a = Iio a
  proof: ext fun _ => coe_lt_coe

@[to_dual (attr := simp)]

中文:
定理 preimage_coe_Iio
  结论: (some : α -> WithTop α) ⁻¹' Iio a = Iio a
  证明: ext fun _ => coe_lt_coe

@[to_dual (attr := simp)]

Depends on / 依赖: coe_lt_coe
-/
theorem preimage_coe_Iio : (some : α -> WithTop α) ⁻¹' Iio a = Iio a :=
  ext fun _ => coe_lt_coe

@[to_dual (attr := simp)]
/--
theorem `preimage_coe_Iic` / 定理 `preimage_coe_Iic`

English:
theorem preimage_coe_Iic
  statement: (some : α -> WithTop α) ⁻¹' Iic a = Iic a
  proof: ext fun _ => coe_le_coe

@[to_dual (attr := simp)]

中文:
定理 preimage_coe_Iic
  结论: (some : α -> WithTop α) ⁻¹' Iic a = Iic a
  证明: ext fun _ => coe_le_coe

@[to_dual (attr := simp)]

Depends on / 依赖: coe_le_coe
-/
theorem preimage_coe_Iic : (some : α -> WithTop α) ⁻¹' Iic a = Iic a :=
  ext fun _ => coe_le_coe

@[to_dual (attr := simp)]
/--
theorem `preimage_coe_Icc` / 定理 `preimage_coe_Icc`

English:
theorem preimage_coe_Icc
  statement: (some : α -> WithTop α) ⁻¹' Icc a b = Icc a b
  proof: by simp [← Ici_inter_Iic]

@[to_dual (attr := simp)]

中文:
定理 preimage_coe_Icc
  结论: (some : α -> WithTop α) ⁻¹' Icc a b = Icc a b
  证明: by simp [← Ici_inter_Iic]

@[to_dual (attr := simp)]

Depends on / 依赖: Ici_inter_Iic
-/
theorem preimage_coe_Icc : (some : α -> WithTop α) ⁻¹' Icc a b = Icc a b := by simp [← Ici_inter_Iic]

@[to_dual (attr := simp)]
/--
theorem `preimage_coe_Ico` / 定理 `preimage_coe_Ico`

English:
theorem preimage_coe_Ico
  statement: (some : α -> WithTop α) ⁻¹' Ico a b = Ico a b
  proof: by simp [← Ici_inter_Iio]

@[to_dual (attr := simp)]

中文:
定理 preimage_coe_Ico
  结论: (some : α -> WithTop α) ⁻¹' Ico a b = Ico a b
  证明: by simp [← Ici_inter_Iio]

@[to_dual (attr := simp)]

Depends on / 依赖: Ici_inter_Iio
-/
theorem preimage_coe_Ico : (some : α -> WithTop α) ⁻¹' Ico a b = Ico a b := by simp [← Ici_inter_Iio]

@[to_dual (attr := simp)]
/--
theorem `preimage_coe_Ioc` / 定理 `preimage_coe_Ioc`

English:
theorem preimage_coe_Ioc
  statement: (some : α -> WithTop α) ⁻¹' Ioc a b = Ioc a b
  proof: by simp [← Ioi_inter_Iic]

@[to_dual (attr := simp)]

中文:
定理 preimage_coe_Ioc
  结论: (some : α -> WithTop α) ⁻¹' Ioc a b = Ioc a b
  证明: by simp [← Ioi_inter_Iic]

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_inter_Iic
-/
theorem preimage_coe_Ioc : (some : α -> WithTop α) ⁻¹' Ioc a b = Ioc a b := by simp [← Ioi_inter_Iic]

@[to_dual (attr := simp)]
/--
theorem `preimage_coe_Ioo` / 定理 `preimage_coe_Ioo`

English:
theorem preimage_coe_Ioo
  statement: (some : α -> WithTop α) ⁻¹' Ioo a b = Ioo a b
  proof: by simp [← Ioi_inter_Iio]

@[to_dual (attr := simp)]

中文:
定理 preimage_coe_Ioo
  结论: (some : α -> WithTop α) ⁻¹' Ioo a b = Ioo a b
  证明: by simp [← Ioi_inter_Iio]

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_inter_Iio
-/
theorem preimage_coe_Ioo : (some : α -> WithTop α) ⁻¹' Ioo a b = Ioo a b := by simp [← Ioi_inter_Iio]

@[to_dual (attr := simp)]
/--
theorem `preimage_coe_Iio_top` / 定理 `preimage_coe_Iio_top`

English:
theorem preimage_coe_Iio_top
  statement: (some : α -> WithTop α) ⁻¹' Iio ⊤ = univ
  proof: by
  rw [← range_coe]; rw [preimage_range]

@[to_dual (attr := simp)]

中文:
定理 preimage_coe_Iio_top
  结论: (some : α -> WithTop α) ⁻¹' Iio ⊤ = univ
  证明: by
  rw [← range_coe]; rw [preimage_range]

@[to_dual (attr := simp)]

Depends on / 依赖: preimage_range, range_coe
-/
theorem preimage_coe_Iio_top : (some : α -> WithTop α) ⁻¹' Iio ⊤ = univ := by
  rw [← range_coe]; rw [preimage_range]

@[to_dual (attr := simp)]
/--
theorem `preimage_coe_Ico_top` / 定理 `preimage_coe_Ico_top`

English:
theorem preimage_coe_Ico_top
  statement: (some : α -> WithTop α) ⁻¹' Ico a ⊤ = Ici a
  proof: by
  simp [← Ici_inter_Iio]

@[to_dual (attr := simp)]

中文:
定理 preimage_coe_Ico_top
  结论: (some : α -> WithTop α) ⁻¹' Ico a ⊤ = Ici a
  证明: by
  simp [← Ici_inter_Iio]

@[to_dual (attr := simp)]

Depends on / 依赖: Ici_inter_Iio
-/
theorem preimage_coe_Ico_top : (some : α -> WithTop α) ⁻¹' Ico a ⊤ = Ici a := by
  simp [← Ici_inter_Iio]

@[to_dual (attr := simp)]
/--
theorem `preimage_coe_Ioo_top` / 定理 `preimage_coe_Ioo_top`

English:
theorem preimage_coe_Ioo_top
  statement: (some : α -> WithTop α) ⁻¹' Ioo a ⊤ = Ioi a
  proof: by
  simp [← Ioi_inter_Iio]

@[to_dual]

中文:
定理 preimage_coe_Ioo_top
  结论: (some : α -> WithTop α) ⁻¹' Ioo a ⊤ = Ioi a
  证明: by
  simp [← Ioi_inter_Iio]

@[to_dual]

Depends on / 依赖: Ioi_inter_Iio
-/
theorem preimage_coe_Ioo_top : (some : α -> WithTop α) ⁻¹' Ioo a ⊤ = Ioi a := by
  simp [← Ioi_inter_Iio]

@[to_dual]
/--
theorem `image_coe_Ioi` / 定理 `image_coe_Ioi`

English:
theorem image_coe_Ioi
  statement: (some : α -> WithTop α) '' Ioi a = Ioo (a : WithTop α) ⊤
  proof: by
  rw [← preimage_coe_Ioi]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [Ioi_inter_Iio]

@[to_dual]

中文:
定理 image_coe_Ioi
  结论: (some : α -> WithTop α) '' Ioi a = Ioo (a : WithTop α) ⊤
  证明: by
  rw [← preimage_coe_Ioi]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [Ioi_inter_Iio]

@[to_dual]

Depends on / 依赖: Ioi_inter_Iio, image_preimage_eq_inter_range, preimage_coe_Ioi, range_coe
-/
theorem image_coe_Ioi : (some : α -> WithTop α) '' Ioi a = Ioo (a : WithTop α) ⊤ := by
  rw [← preimage_coe_Ioi]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [Ioi_inter_Iio]

@[to_dual]
/--
theorem `image_coe_Ici` / 定理 `image_coe_Ici`

English:
theorem image_coe_Ici
  statement: (some : α -> WithTop α) '' Ici a = Ico (a : WithTop α) ⊤
  proof: by
  rw [← preimage_coe_Ici]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [Ici_inter_Iio]

@[to_dual]

中文:
定理 image_coe_Ici
  结论: (some : α -> WithTop α) '' Ici a = Ico (a : WithTop α) ⊤
  证明: by
  rw [← preimage_coe_Ici]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [Ici_inter_Iio]

@[to_dual]

Depends on / 依赖: Ici_inter_Iio, image_preimage_eq_inter_range, preimage_coe_Ici, range_coe
-/
theorem image_coe_Ici : (some : α -> WithTop α) '' Ici a = Ico (a : WithTop α) ⊤ := by
  rw [← preimage_coe_Ici]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [Ici_inter_Iio]

@[to_dual]
/--
theorem `image_coe_Iio` / 定理 `image_coe_Iio`

English:
theorem image_coe_Iio
  statement: (some : α -> WithTop α) '' Iio a = Iio (a : WithTop α)
  proof: by
  rw [← preimage_coe_Iio]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left (Iio_subset_Iio le_top)]

@[to_dual]

中文:
定理 image_coe_Iio
  结论: (some : α -> WithTop α) '' Iio a = Iio (a : WithTop α)
  证明: by
  rw [← preimage_coe_Iio]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left (Iio_subset_Iio le_top)]

@[to_dual]

Depends on / 依赖: Iio_subset_Iio, image_preimage_eq_inter_range, inter_eq_self_of_subset_left, le_top, preimage_coe_Iio, range_coe
-/
theorem image_coe_Iio : (some : α -> WithTop α) '' Iio a = Iio (a : WithTop α) := by
  rw [← preimage_coe_Iio]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left (Iio_subset_Iio le_top)]

@[to_dual]
/--
theorem `image_coe_Iic` / 定理 `image_coe_Iic`

English:
theorem image_coe_Iic
  statement: (some : α -> WithTop α) '' Iic a = Iic (a : WithTop α)
  proof: by
  rw [← preimage_coe_Iic]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left (Iic_subset_Iio.2 <| coe_lt_top a)]

@[to_dual]

中文:
定理 image_coe_Iic
  结论: (some : α -> WithTop α) '' Iic a = Iic (a : WithTop α)
  证明: by
  rw [← preimage_coe_Iic]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left (Iic_subset_Iio.2 <| coe_lt_top a)]

@[to_dual]

Depends on / 依赖: Iic_subset_Iio, coe_lt_top, image_preimage_eq_inter_range, inter_eq_self_of_subset_left, preimage_coe_Iic, range_coe
-/
theorem image_coe_Iic : (some : α -> WithTop α) '' Iic a = Iic (a : WithTop α) := by
  rw [← preimage_coe_Iic]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left (Iic_subset_Iio.2 <| coe_lt_top a)]

@[to_dual]
/--
theorem `image_coe_Icc` / 定理 `image_coe_Icc`

English:
theorem image_coe_Icc
  statement: (some : α -> WithTop α) '' Icc a b = Icc (a : WithTop α) b
  proof: by
  rw [← preimage_coe_Icc]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left
      (Subset.trans Icc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

@[to_dual]

中文:
定理 image_coe_Icc
  结论: (some : α -> WithTop α) '' Icc a b = Icc (a : WithTop α) b
  证明: by
  rw [← preimage_coe_Icc]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left
      (Subset.trans Icc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

@[to_dual]

Depends on / 依赖: Icc_subset_Iic_self, Iic_subset_Iio, Subset, Subset.trans, coe_lt_top, image_preimage_eq_inter_range, inter_eq_self_of_subset_left, preimage_coe_Icc, range_coe
-/
theorem image_coe_Icc : (some : α -> WithTop α) '' Icc a b = Icc (a : WithTop α) b := by
  rw [← preimage_coe_Icc]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left
      (Subset.trans Icc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

@[to_dual]
/--
theorem `image_coe_Ico` / 定理 `image_coe_Ico`

English:
theorem image_coe_Ico
  statement: (some : α -> WithTop α) '' Ico a b = Ico (a : WithTop α) b
  proof: by
  rw [← preimage_coe_Ico]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left (Subset.trans Ico_subset_Iio_self <| Iio_subset_Iio le_top)]

@[to_dual]

中文:
定理 image_coe_Ico
  结论: (some : α -> WithTop α) '' Ico a b = Ico (a : WithTop α) b
  证明: by
  rw [← preimage_coe_Ico]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left (Subset.trans Ico_subset_Iio_self <| Iio_subset_Iio le_top)]

@[to_dual]

Depends on / 依赖: Ico_subset_Iio_self, Iio_subset_Iio, Subset, Subset.trans, image_preimage_eq_inter_range, inter_eq_self_of_subset_left, le_top, preimage_coe_Ico, range_coe
-/
theorem image_coe_Ico : (some : α -> WithTop α) '' Ico a b = Ico (a : WithTop α) b := by
  rw [← preimage_coe_Ico]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left (Subset.trans Ico_subset_Iio_self <| Iio_subset_Iio le_top)]

@[to_dual]
/--
theorem `image_coe_Ioc` / 定理 `image_coe_Ioc`

English:
theorem image_coe_Ioc
  statement: (some : α -> WithTop α) '' Ioc a b = Ioc (a : WithTop α) b
  proof: by
  rw [← preimage_coe_Ioc]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left
      (Subset.trans Ioc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

@[to_dual]

中文:
定理 image_coe_Ioc
  结论: (some : α -> WithTop α) '' Ioc a b = Ioc (a : WithTop α) b
  证明: by
  rw [← preimage_coe_Ioc]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left
      (Subset.trans Ioc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

@[to_dual]

Depends on / 依赖: Iic_subset_Iio, Ioc_subset_Iic_self, Subset, Subset.trans, coe_lt_top, image_preimage_eq_inter_range, inter_eq_self_of_subset_left, preimage_coe_Ioc, range_coe
-/
theorem image_coe_Ioc : (some : α -> WithTop α) '' Ioc a b = Ioc (a : WithTop α) b := by
  rw [← preimage_coe_Ioc]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left
      (Subset.trans Ioc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

@[to_dual]
/--
theorem `image_coe_Ioo` / 定理 `image_coe_Ioo`

English:
theorem image_coe_Ioo
  statement: (some : α -> WithTop α) '' Ioo a b = Ioo (a : WithTop α) b
  proof: by
  rw [← preimage_coe_Ioo]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left (Subset.trans Ioo_subset_Iio_self <| Iio_subset_Iio le_top)]

@[to_dual]

中文:
定理 image_coe_Ioo
  结论: (some : α -> WithTop α) '' Ioo a b = Ioo (a : WithTop α) b
  证明: by
  rw [← preimage_coe_Ioo]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left (Subset.trans Ioo_subset_Iio_self <| Iio_subset_Iio le_top)]

@[to_dual]

Depends on / 依赖: Iio_subset_Iio, Ioo_subset_Iio_self, Subset, Subset.trans, image_preimage_eq_inter_range, inter_eq_self_of_subset_left, le_top, preimage_coe_Ioo, range_coe
-/
theorem image_coe_Ioo : (some : α -> WithTop α) '' Ioo a b = Ioo (a : WithTop α) b := by
  rw [← preimage_coe_Ioo]; rw [image_preimage_eq_inter_range]; rw [range_coe]; rw [inter_eq_self_of_subset_left (Subset.trans Ioo_subset_Iio_self <| Iio_subset_Iio le_top)]

@[to_dual]
/--
theorem `Ioi_coe` / 定理 `Ioi_coe`

English:
theorem Ioi_coe
  statement: Ioi (a : WithTop α) = (↑) '' (Ioi a) union {⊤}
  proof: by
  ext x; induction x <;> simp

@[to_dual]

中文:
定理 Ioi_coe
  结论: Ioi (a : WithTop α) = (↑) '' (Ioi a) union {⊤}
  证明: by
  ext x; induction x <;> simp

@[to_dual]
-/
theorem Ioi_coe : Ioi (a : WithTop α) = (↑) '' (Ioi a) union {⊤} := by
  ext x; induction x <;> simp

@[to_dual]
/--
theorem `Ici_coe` / 定理 `Ici_coe`

English:
theorem Ici_coe
  statement: Ici (a : WithTop α) = (↑) '' (Ici a) union {⊤}
  proof: by
  ext x; induction x <;> simp

@[to_dual]

中文:
定理 Ici_coe
  结论: Ici (a : WithTop α) = (↑) '' (Ici a) union {⊤}
  证明: by
  ext x; induction x <;> simp

@[to_dual]
-/
theorem Ici_coe : Ici (a : WithTop α) = (↑) '' (Ici a) union {⊤} := by
  ext x; induction x <;> simp

@[to_dual]
/--
theorem `Iio_coe` / 定理 `Iio_coe`

English:
theorem Iio_coe
  statement: Iio (a : WithTop α) = (↑) '' (Iio a)
  proof: image_coe_Iio.symm

@[to_dual]

中文:
定理 Iio_coe
  结论: Iio (a : WithTop α) = (↑) '' (Iio a)
  证明: image_coe_Iio.symm

@[to_dual]

Depends on / 依赖: image_coe_Iio, image_coe_Iio.symm
-/
theorem Iio_coe : Iio (a : WithTop α) = (↑) '' (Iio a) := image_coe_Iio.symm

@[to_dual]
/--
theorem `Iic_coe` / 定理 `Iic_coe`

English:
theorem Iic_coe
  statement: Iic (a : WithTop α) = (↑) '' (Iic a)
  proof: image_coe_Iic.symm

@[to_dual]

中文:
定理 Iic_coe
  结论: Iic (a : WithTop α) = (↑) '' (Iic a)
  证明: image_coe_Iic.symm

@[to_dual]

Depends on / 依赖: image_coe_Iic, image_coe_Iic.symm
-/
theorem Iic_coe : Iic (a : WithTop α) = (↑) '' (Iic a) := image_coe_Iic.symm

@[to_dual]
/--
theorem `Icc_coe` / 定理 `Icc_coe`

English:
theorem Icc_coe
  statement: Icc (a : WithTop α) b = (↑) '' (Icc a b)
  proof: image_coe_Icc.symm

@[to_dual]

中文:
定理 Icc_coe
  结论: Icc (a : WithTop α) b = (↑) '' (Icc a b)
  证明: image_coe_Icc.symm

@[to_dual]

Depends on / 依赖: image_coe_Icc, image_coe_Icc.symm
-/
theorem Icc_coe : Icc (a : WithTop α) b = (↑) '' (Icc a b) := image_coe_Icc.symm

@[to_dual]
/--
theorem `Ico_coe` / 定理 `Ico_coe`

English:
theorem Ico_coe
  statement: Ico (a : WithTop α) b = (↑) '' (Ico a b)
  proof: image_coe_Ico.symm

@[to_dual]

中文:
定理 Ico_coe
  结论: Ico (a : WithTop α) b = (↑) '' (Ico a b)
  证明: image_coe_Ico.symm

@[to_dual]

Depends on / 依赖: image_coe_Ico, image_coe_Ico.symm
-/
theorem Ico_coe : Ico (a : WithTop α) b = (↑) '' (Ico a b) := image_coe_Ico.symm

@[to_dual]
/--
theorem `Ioc_coe` / 定理 `Ioc_coe`

English:
theorem Ioc_coe
  statement: Ioc (a : WithTop α) b = (↑) '' (Ioc a b)
  proof: image_coe_Ioc.symm

@[to_dual]

中文:
定理 Ioc_coe
  结论: Ioc (a : WithTop α) b = (↑) '' (Ioc a b)
  证明: image_coe_Ioc.symm

@[to_dual]

Depends on / 依赖: image_coe_Ioc, image_coe_Ioc.symm
-/
theorem Ioc_coe : Ioc (a : WithTop α) b = (↑) '' (Ioc a b) := image_coe_Ioc.symm

@[to_dual]
/--
theorem `Ioo_coe` / 定理 `Ioo_coe`

English:
theorem Ioo_coe
  statement: Ioo (a : WithTop α) b = (↑) '' (Ioo a b)
  proof: image_coe_Ioo.symm

中文:
定理 Ioo_coe
  结论: Ioo (a : WithTop α) b = (↑) '' (Ioo a b)
  证明: image_coe_Ioo.symm

Depends on / 依赖: image_coe_Ioo, image_coe_Ioo.symm
-/
theorem Ioo_coe : Ioo (a : WithTop α) b = (↑) '' (Ioo a b) := image_coe_Ioo.symm

end WithTop
