/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE

/-!
# Images of intervals under `(+ d)`

The lemmas in this file state that addition maps intervals bijectively. The typeclass
`ExistsAddOfLE` is defined specifically to make them work when combined with
`IsOrderedCancelAddMonoid`; the lemmas below therefore apply to all ordered groups,
but also to `ℕ` and `ℝ≥0`, which are not groups.
-/

public section


namespace Set

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]
  [ExistsAddOfLE M] (a b c d : M)

/--
theorem `Ici_add_bij` / 定理 `Ici_add_bij`

English:
theorem Ici_add_bij
  statement: BijOn (· + d) (Ici a) (Ici (a + d))
  proof: by
  refine ⟨by simp [MapsTo], by simp, fun _ h => ?_⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ici.mp h)
  rw [mem_Ici]; rw [add_right_comm]; rw [add_le_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

中文:
定理 Ici_add_bij
  结论: BijOn (· + d) (Ici a) (Ici (a + d))
  证明: by
  refine ⟨by simp [MapsTo], by simp, fun _ h => ?_⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ici.mp h)
  rw [mem_Ici]; rw [add_right_comm]; rw [add_le_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

Depends on / 依赖: MapsTo, add_le_add_iff_right, add_right_comm, exists_add_of_le, mem_Ici, mem_Ici.mp
-/
theorem Ici_add_bij : BijOn (· + d) (Ici a) (Ici (a + d)) := by
  refine ⟨by simp [MapsTo], by simp, fun _ h => ?_⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ici.mp h)
  rw [mem_Ici]; rw [add_right_comm]; rw [add_le_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

/--
theorem `Ioi_add_bij` / 定理 `Ioi_add_bij`

English:
theorem Ioi_add_bij
  statement: BijOn (· + d) (Ioi a) (Ioi (a + d))
  proof: by
  refine ⟨by simp [MapsTo], by simp, fun _ h => ?_⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ioi.mp h).le
  rw [mem_Ioi]; rw [add_right_comm]; rw [add_lt_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

中文:
定理 Ioi_add_bij
  结论: BijOn (· + d) (Ioi a) (Ioi (a + d))
  证明: by
  refine ⟨by simp [MapsTo], by simp, fun _ h => ?_⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ioi.mp h).le
  rw [mem_Ioi]; rw [add_right_comm]; rw [add_lt_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

Depends on / 依赖: MapsTo, add_lt_add_iff_right, add_right_comm, exists_add_of_le, mem_Ioi, mem_Ioi.mp
-/
theorem Ioi_add_bij : BijOn (· + d) (Ioi a) (Ioi (a + d)) := by
  refine ⟨by simp [MapsTo], by simp, fun _ h => ?_⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ioi.mp h).le
  rw [mem_Ioi]; rw [add_right_comm]; rw [add_lt_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

/--
theorem `Icc_add_bij` / 定理 `Icc_add_bij`

English:
theorem Icc_add_bij
  statement: BijOn (· + d) (Icc a b) (Icc (a + d) (b + d))
  proof: by
  rw [← Ici_inter_Iic]; rw [← Ici_inter_Iic]
  exact (Ici_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => le_of_add_le_add_right hx.2

中文:
定理 Icc_add_bij
  结论: BijOn (· + d) (Icc a b) (Icc (a + d) (b + d))
  证明: by
  rw [← Ici_inter_Iic]; rw [← Ici_inter_Iic]
  exact (Ici_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => le_of_add_le_add_right hx.2

Depends on / 依赖: Ici_add_bij, Ici_inter_Iic, MapsTo, inter_mapsTo, le_of_add_le_add_right
-/
theorem Icc_add_bij : BijOn (· + d) (Icc a b) (Icc (a + d) (b + d)) := by
  rw [← Ici_inter_Iic]; rw [← Ici_inter_Iic]
  exact (Ici_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => le_of_add_le_add_right hx.2

/--
theorem `Ioo_add_bij` / 定理 `Ioo_add_bij`

English:
theorem Ioo_add_bij
  statement: BijOn (· + d) (Ioo a b) (Ioo (a + d) (b + d))
  proof: by
  rw [← Ioi_inter_Iio]; rw [← Ioi_inter_Iio]
  exact (Ioi_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => lt_of_add_lt_add_right hx.2

中文:
定理 Ioo_add_bij
  结论: BijOn (· + d) (Ioo a b) (Ioo (a + d) (b + d))
  证明: by
  rw [← Ioi_inter_Iio]; rw [← Ioi_inter_Iio]
  exact (Ioi_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => lt_of_add_lt_add_right hx.2

Depends on / 依赖: Ioi_add_bij, Ioi_inter_Iio, MapsTo, inter_mapsTo, lt_of_add_lt_add_right
-/
theorem Ioo_add_bij : BijOn (· + d) (Ioo a b) (Ioo (a + d) (b + d)) := by
  rw [← Ioi_inter_Iio]; rw [← Ioi_inter_Iio]
  exact (Ioi_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => lt_of_add_lt_add_right hx.2

/--
theorem `Ioc_add_bij` / 定理 `Ioc_add_bij`

English:
theorem Ioc_add_bij
  statement: BijOn (· + d) (Ioc a b) (Ioc (a + d) (b + d))
  proof: by
  rw [← Ioi_inter_Iic]; rw [← Ioi_inter_Iic]
  exact (Ioi_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => le_of_add_le_add_right hx.2

中文:
定理 Ioc_add_bij
  结论: BijOn (· + d) (Ioc a b) (Ioc (a + d) (b + d))
  证明: by
  rw [← Ioi_inter_Iic]; rw [← Ioi_inter_Iic]
  exact (Ioi_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => le_of_add_le_add_right hx.2

Depends on / 依赖: Ioi_add_bij, Ioi_inter_Iic, MapsTo, inter_mapsTo, le_of_add_le_add_right
-/
theorem Ioc_add_bij : BijOn (· + d) (Ioc a b) (Ioc (a + d) (b + d)) := by
  rw [← Ioi_inter_Iic]; rw [← Ioi_inter_Iic]
  exact (Ioi_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => le_of_add_le_add_right hx.2

/--
theorem `Ico_add_bij` / 定理 `Ico_add_bij`

English:
theorem Ico_add_bij
  statement: BijOn (· + d) (Ico a b) (Ico (a + d) (b + d))
  proof: by
  rw [← Ici_inter_Iio]; rw [← Ici_inter_Iio]
  exact (Ici_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => lt_of_add_lt_add_right hx.2

中文:
定理 Ico_add_bij
  结论: BijOn (· + d) (Ico a b) (Ico (a + d) (b + d))
  证明: by
  rw [← Ici_inter_Iio]; rw [← Ici_inter_Iio]
  exact (Ici_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => lt_of_add_lt_add_right hx.2

Depends on / 依赖: Ici_add_bij, Ici_inter_Iio, MapsTo, inter_mapsTo, lt_of_add_lt_add_right
-/
theorem Ico_add_bij : BijOn (· + d) (Ico a b) (Ico (a + d) (b + d)) := by
  rw [← Ici_inter_Iio]; rw [← Ici_inter_Iio]
  exact (Ici_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => lt_of_add_lt_add_right hx.2

/-!
### Images under `x ↦ x + a`
-/


@[simp]
/--
theorem `image_add_const_Ici` / 定理 `image_add_const_Ici`

English:
theorem image_add_const_Ici
  statement: (fun x => x + a) '' Ici b = Ici (b + a)
  proof: (Ici_add_bij _ _).image_eq

@[simp]

中文:
定理 image_add_const_Ici
  结论: (fun x => x + a) '' Ici b = Ici (b + a)
  证明: (Ici_add_bij _ _).image_eq

@[simp]

Depends on / 依赖: Ici_add_bij, image_eq
-/
theorem image_add_const_Ici : (fun x => x + a) '' Ici b = Ici (b + a) :=
  (Ici_add_bij _ _).image_eq

@[simp]
/--
theorem `image_add_const_Ioi` / 定理 `image_add_const_Ioi`

English:
theorem image_add_const_Ioi
  statement: (fun x => x + a) '' Ioi b = Ioi (b + a)
  proof: (Ioi_add_bij _ _).image_eq

@[simp]

中文:
定理 image_add_const_Ioi
  结论: (fun x => x + a) '' Ioi b = Ioi (b + a)
  证明: (Ioi_add_bij _ _).image_eq

@[simp]

Depends on / 依赖: Ioi_add_bij, image_eq
-/
theorem image_add_const_Ioi : (fun x => x + a) '' Ioi b = Ioi (b + a) :=
  (Ioi_add_bij _ _).image_eq

@[simp]
/--
theorem `image_add_const_Icc` / 定理 `image_add_const_Icc`

English:
theorem image_add_const_Icc
  statement: (fun x => x + a) '' Icc b c = Icc (b + a) (c + a)
  proof: (Icc_add_bij _ _ _).image_eq

@[simp]

中文:
定理 image_add_const_Icc
  结论: (fun x => x + a) '' Icc b c = Icc (b + a) (c + a)
  证明: (Icc_add_bij _ _ _).image_eq

@[simp]

Depends on / 依赖: Icc_add_bij, image_eq
-/
theorem image_add_const_Icc : (fun x => x + a) '' Icc b c = Icc (b + a) (c + a) :=
  (Icc_add_bij _ _ _).image_eq

@[simp]
/--
theorem `image_add_const_Ico` / 定理 `image_add_const_Ico`

English:
theorem image_add_const_Ico
  statement: (fun x => x + a) '' Ico b c = Ico (b + a) (c + a)
  proof: (Ico_add_bij _ _ _).image_eq

@[simp]

中文:
定理 image_add_const_Ico
  结论: (fun x => x + a) '' Ico b c = Ico (b + a) (c + a)
  证明: (Ico_add_bij _ _ _).image_eq

@[simp]

Depends on / 依赖: Ico_add_bij, image_eq
-/
theorem image_add_const_Ico : (fun x => x + a) '' Ico b c = Ico (b + a) (c + a) :=
  (Ico_add_bij _ _ _).image_eq

@[simp]
/--
theorem `image_add_const_Ioc` / 定理 `image_add_const_Ioc`

English:
theorem image_add_const_Ioc
  statement: (fun x => x + a) '' Ioc b c = Ioc (b + a) (c + a)
  proof: (Ioc_add_bij _ _ _).image_eq

@[simp]

中文:
定理 image_add_const_Ioc
  结论: (fun x => x + a) '' Ioc b c = Ioc (b + a) (c + a)
  证明: (Ioc_add_bij _ _ _).image_eq

@[simp]

Depends on / 依赖: Ioc_add_bij, image_eq
-/
theorem image_add_const_Ioc : (fun x => x + a) '' Ioc b c = Ioc (b + a) (c + a) :=
  (Ioc_add_bij _ _ _).image_eq

@[simp]
/--
theorem `image_add_const_Ioo` / 定理 `image_add_const_Ioo`

English:
theorem image_add_const_Ioo
  statement: (fun x => x + a) '' Ioo b c = Ioo (b + a) (c + a)
  proof: (Ioo_add_bij _ _ _).image_eq

中文:
定理 image_add_const_Ioo
  结论: (fun x => x + a) '' Ioo b c = Ioo (b + a) (c + a)
  证明: (Ioo_add_bij _ _ _).image_eq

Depends on / 依赖: Ioo_add_bij, image_eq
-/
theorem image_add_const_Ioo : (fun x => x + a) '' Ioo b c = Ioo (b + a) (c + a) :=
  (Ioo_add_bij _ _ _).image_eq

/-!
### Images under `x ↦ a + x`
-/


@[simp]
/--
theorem `image_const_add_Ici` / 定理 `image_const_add_Ici`

English:
theorem image_const_add_Ici
  statement: (fun x => a + x) '' Ici b = Ici (a + b)
  proof: by
  simp only [add_comm a, image_add_const_Ici]

@[simp]

中文:
定理 image_const_add_Ici
  结论: (fun x => a + x) '' Ici b = Ici (a + b)
  证明: by
  simp only [add_comm a, image_add_const_Ici]

@[simp]

Depends on / 依赖: add_comm, image_add_const_Ici
-/
theorem image_const_add_Ici : (fun x => a + x) '' Ici b = Ici (a + b) := by
  simp only [add_comm a, image_add_const_Ici]

@[simp]
/--
theorem `image_const_add_Ioi` / 定理 `image_const_add_Ioi`

English:
theorem image_const_add_Ioi
  statement: (fun x => a + x) '' Ioi b = Ioi (a + b)
  proof: by
  simp only [add_comm a, image_add_const_Ioi]

@[simp]

中文:
定理 image_const_add_Ioi
  结论: (fun x => a + x) '' Ioi b = Ioi (a + b)
  证明: by
  simp only [add_comm a, image_add_const_Ioi]

@[simp]

Depends on / 依赖: add_comm, image_add_const_Ioi
-/
theorem image_const_add_Ioi : (fun x => a + x) '' Ioi b = Ioi (a + b) := by
  simp only [add_comm a, image_add_const_Ioi]

@[simp]
/--
theorem `image_const_add_Icc` / 定理 `image_const_add_Icc`

English:
theorem image_const_add_Icc
  statement: (fun x => a + x) '' Icc b c = Icc (a + b) (a + c)
  proof: by
  simp only [add_comm a, image_add_const_Icc]

@[simp]

中文:
定理 image_const_add_Icc
  结论: (fun x => a + x) '' Icc b c = Icc (a + b) (a + c)
  证明: by
  simp only [add_comm a, image_add_const_Icc]

@[simp]

Depends on / 依赖: add_comm, image_add_const_Icc
-/
theorem image_const_add_Icc : (fun x => a + x) '' Icc b c = Icc (a + b) (a + c) := by
  simp only [add_comm a, image_add_const_Icc]

@[simp]
/--
theorem `image_const_add_Ico` / 定理 `image_const_add_Ico`

English:
theorem image_const_add_Ico
  statement: (fun x => a + x) '' Ico b c = Ico (a + b) (a + c)
  proof: by
  simp only [add_comm a, image_add_const_Ico]

@[simp]

中文:
定理 image_const_add_Ico
  结论: (fun x => a + x) '' Ico b c = Ico (a + b) (a + c)
  证明: by
  simp only [add_comm a, image_add_const_Ico]

@[simp]

Depends on / 依赖: add_comm, image_add_const_Ico
-/
theorem image_const_add_Ico : (fun x => a + x) '' Ico b c = Ico (a + b) (a + c) := by
  simp only [add_comm a, image_add_const_Ico]

@[simp]
/--
theorem `image_const_add_Ioc` / 定理 `image_const_add_Ioc`

English:
theorem image_const_add_Ioc
  statement: (fun x => a + x) '' Ioc b c = Ioc (a + b) (a + c)
  proof: by
  simp only [add_comm a, image_add_const_Ioc]

@[simp]

中文:
定理 image_const_add_Ioc
  结论: (fun x => a + x) '' Ioc b c = Ioc (a + b) (a + c)
  证明: by
  simp only [add_comm a, image_add_const_Ioc]

@[simp]

Depends on / 依赖: add_comm, image_add_const_Ioc
-/
theorem image_const_add_Ioc : (fun x => a + x) '' Ioc b c = Ioc (a + b) (a + c) := by
  simp only [add_comm a, image_add_const_Ioc]

@[simp]
/--
theorem `image_const_add_Ioo` / 定理 `image_const_add_Ioo`

English:
theorem image_const_add_Ioo
  statement: (fun x => a + x) '' Ioo b c = Ioo (a + b) (a + c)
  proof: by
  simp only [add_comm a, image_add_const_Ioo]

中文:
定理 image_const_add_Ioo
  结论: (fun x => a + x) '' Ioo b c = Ioo (a + b) (a + c)
  证明: by
  simp only [add_comm a, image_add_const_Ioo]

Depends on / 依赖: add_comm, image_add_const_Ioo
-/
theorem image_const_add_Ioo : (fun x => a + x) '' Ioo b c = Ioo (a + b) (a + c) := by
  simp only [add_comm a, image_add_const_Ioo]

end Set
