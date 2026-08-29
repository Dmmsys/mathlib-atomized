/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# (Pre)images of set intervals under `Fin` operations

In this file we prove basic lemmas about preimages and images of the intervals
under the following operations:

- `Fin.val`,
- `Fin.castLE` (preimages only),
- `Fin.castAdd`,
- `Fin.cast`,
- `Fin.castSucc`,
- `Fin.natAdd`,
- `Fin.addNat`,
- `Fin.succ`,
- `Fin.rev`.
-/

public section

open Function Set

namespace Fin

variable {m n : Nat}

/-!
### (Pre)images under `Fin.val`
-/

@[simp]
/--
theorem `range_val` / 定理 `range_val`

English:
theorem range_val
  statement: range ((↑) : Fin n -> Nat) = Set.Iio n
  proof: by ext; simp [Fin.exists_iff]

中文:
定理 range_val
  结论: range ((↑) : Fin n -> 自然数) = Set.Iio n
  证明: by ext; simp [Fin.exists_iff]

Depends on / 依赖: Fin.exists_iff, exists_iff
-/
theorem range_val : range ((↑) : Fin n -> Nat) = Set.Iio n := by ext; simp [Fin.exists_iff]

/--
theorem `preimage_val_Ici_val` / 定理 `preimage_val_Ici_val`

English:
theorem preimage_val_Ici_val
  given: (i : Fin n)
  statement: (↑) ⁻¹' Ici (i : Nat) = Ici i
  proof: rfl

中文:
定理 preimage_val_Ici_val
  条件: (i : Fin n)
  结论: (↑) ⁻¹' Ici (i : 自然数) = Ici i
  证明: rfl
-/
@[simp] theorem preimage_val_Ici_val (i : Fin n) : (↑) ⁻¹' Ici (i : Nat) = Ici i := rfl
/--
theorem `preimage_val_Ioi_val` / 定理 `preimage_val_Ioi_val`

English:
theorem preimage_val_Ioi_val
  given: (i : Fin n)
  statement: (↑) ⁻¹' Ioi (i : Nat) = Ioi i
  proof: rfl

中文:
定理 preimage_val_Ioi_val
  条件: (i : Fin n)
  结论: (↑) ⁻¹' Ioi (i : 自然数) = Ioi i
  证明: rfl
-/
@[simp] theorem preimage_val_Ioi_val (i : Fin n) : (↑) ⁻¹' Ioi (i : Nat) = Ioi i := rfl
/--
theorem `preimage_val_Iic_val` / 定理 `preimage_val_Iic_val`

English:
theorem preimage_val_Iic_val
  given: (i : Fin n)
  statement: (↑) ⁻¹' Iic (i : Nat) = Iic i
  proof: rfl

中文:
定理 preimage_val_Iic_val
  条件: (i : Fin n)
  结论: (↑) ⁻¹' Iic (i : 自然数) = Iic i
  证明: rfl
-/
@[simp] theorem preimage_val_Iic_val (i : Fin n) : (↑) ⁻¹' Iic (i : Nat) = Iic i := rfl
/--
theorem `preimage_val_Iio_val` / 定理 `preimage_val_Iio_val`

English:
theorem preimage_val_Iio_val
  given: (i : Fin n)
  statement: (↑) ⁻¹' Iio (i : Nat) = Iio i
  proof: rfl

中文:
定理 preimage_val_Iio_val
  条件: (i : Fin n)
  结论: (↑) ⁻¹' Iio (i : 自然数) = Iio i
  证明: rfl
-/
@[simp] theorem preimage_val_Iio_val (i : Fin n) : (↑) ⁻¹' Iio (i : Nat) = Iio i := rfl

/--
theorem `preimage_val_Icc_val` / 定理 `preimage_val_Icc_val`

English:
theorem preimage_val_Icc_val
  given: (i j : Fin n)
  statement: (↑) ⁻¹' Icc (i : Nat) j = Icc i j
  proof: rfl

中文:
定理 preimage_val_Icc_val
  条件: (i j : Fin n)
  结论: (↑) ⁻¹' Icc (i : 自然数) j = Icc i j
  证明: rfl
-/
@[simp] theorem preimage_val_Icc_val (i j : Fin n) : (↑) ⁻¹' Icc (i : Nat) j = Icc i j := rfl
/--
theorem `preimage_val_Ico_val` / 定理 `preimage_val_Ico_val`

English:
theorem preimage_val_Ico_val
  given: (i j : Fin n)
  statement: (↑) ⁻¹' Ico (i : Nat) j = Ico i j
  proof: rfl

中文:
定理 preimage_val_Ico_val
  条件: (i j : Fin n)
  结论: (↑) ⁻¹' Ico (i : 自然数) j = Ico i j
  证明: rfl
-/
@[simp] theorem preimage_val_Ico_val (i j : Fin n) : (↑) ⁻¹' Ico (i : Nat) j = Ico i j := rfl
/--
theorem `preimage_val_Ioc_val` / 定理 `preimage_val_Ioc_val`

English:
theorem preimage_val_Ioc_val
  given: (i j : Fin n)
  statement: (↑) ⁻¹' Ioc (i : Nat) j = Ioc i j
  proof: rfl

中文:
定理 preimage_val_Ioc_val
  条件: (i j : Fin n)
  结论: (↑) ⁻¹' Ioc (i : 自然数) j = Ioc i j
  证明: rfl
-/
@[simp] theorem preimage_val_Ioc_val (i j : Fin n) : (↑) ⁻¹' Ioc (i : Nat) j = Ioc i j := rfl
/--
theorem `preimage_val_Ioo_val` / 定理 `preimage_val_Ioo_val`

English:
theorem preimage_val_Ioo_val
  given: (i j : Fin n)
  statement: (↑) ⁻¹' Ioo (i : Nat) j = Ioo i j
  proof: rfl

中文:
定理 preimage_val_Ioo_val
  条件: (i j : Fin n)
  结论: (↑) ⁻¹' Ioo (i : 自然数) j = Ioo i j
  证明: rfl
-/
@[simp] theorem preimage_val_Ioo_val (i j : Fin n) : (↑) ⁻¹' Ioo (i : Nat) j = Ioo i j := rfl
/--
theorem `preimage_val_uIcc_val` / 定理 `preimage_val_uIcc_val`

English:
theorem preimage_val_uIcc_val
  given: (i j : Fin n)
  statement: (↑) ⁻¹' uIcc (i : Nat) j = uIcc i j
  proof: rfl

中文:
定理 preimage_val_uIcc_val
  条件: (i j : Fin n)
  结论: (↑) ⁻¹' uIcc (i : 自然数) j = uIcc i j
  证明: rfl
-/
@[simp] theorem preimage_val_uIcc_val (i j : Fin n) : (↑) ⁻¹' uIcc (i : Nat) j = uIcc i j := rfl
/--
theorem `preimage_val_uIoc_val` / 定理 `preimage_val_uIoc_val`

English:
theorem preimage_val_uIoc_val
  given: (i j : Fin n)
  statement: (↑) ⁻¹' uIoc (i : Nat) j = uIoc i j
  proof: rfl

中文:
定理 preimage_val_uIoc_val
  条件: (i j : Fin n)
  结论: (↑) ⁻¹' uIoc (i : 自然数) j = uIoc i j
  证明: rfl
-/
@[simp] theorem preimage_val_uIoc_val (i j : Fin n) : (↑) ⁻¹' uIoc (i : Nat) j = uIoc i j := rfl
/--
theorem `preimage_val_uIoo_val` / 定理 `preimage_val_uIoo_val`

English:
theorem preimage_val_uIoo_val
  given: (i j : Fin n)
  statement: (↑) ⁻¹' uIoo (i : Nat) j = uIoo i j
  proof: rfl

@[simp]

中文:
定理 preimage_val_uIoo_val
  条件: (i j : Fin n)
  结论: (↑) ⁻¹' uIoo (i : 自然数) j = uIoo i j
  证明: rfl

@[simp]
-/
@[simp] theorem preimage_val_uIoo_val (i j : Fin n) : (↑) ⁻¹' uIoo (i : Nat) j = uIoo i j := rfl

@[simp]
/--
theorem `image_val_Ici` / 定理 `image_val_Ici`

English:
theorem image_val_Ici
  given: (i : Fin n)
  statement: (↑) '' Ici i = Ico (i : Nat) n
  proof: by
  rw [← preimage_val_Ici_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [Ici_inter_Iio]

@[simp]

中文:
定理 image_val_Ici
  条件: (i : Fin n)
  结论: (↑) '' Ici i = Ico (i : 自然数) n
  证明: by
  rw [← preimage_val_Ici_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [Ici_inter_Iio]

@[simp]

Depends on / 依赖: Ici_inter_Iio, image_preimage_eq_inter_range, preimage_val_Ici_val, range_val
-/
theorem image_val_Ici (i : Fin n) : (↑) '' Ici i = Ico (i : Nat) n := by
  rw [← preimage_val_Ici_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [Ici_inter_Iio]

@[simp]
/--
theorem `image_val_Iic` / 定理 `image_val_Iic`

English:
theorem image_val_Iic
  given: (i : Fin n)
  statement: (↑) '' Iic i = Iic (i : Nat)
  proof: by
  rw [← preimage_val_Iic_val]; rw [image_preimage_eq_of_subset]
  simp [range_val]

@[simp]

中文:
定理 image_val_Iic
  条件: (i : Fin n)
  结论: (↑) '' Iic i = Iic (i : 自然数)
  证明: by
  rw [← preimage_val_Iic_val]; rw [image_preimage_eq_of_subset]
  simp [range_val]

@[simp]

Depends on / 依赖: image_preimage_eq_of_subset, preimage_val_Iic_val, range_val
-/
theorem image_val_Iic (i : Fin n) : (↑) '' Iic i = Iic (i : Nat) := by
  rw [← preimage_val_Iic_val]; rw [image_preimage_eq_of_subset]
  simp [range_val]

@[simp]
/--
theorem `image_val_Ioi` / 定理 `image_val_Ioi`

English:
theorem image_val_Ioi
  given: (i : Fin n)
  statement: (↑) '' Ioi i = Ioo (i : Nat) n
  proof: by
  rw [← preimage_val_Ioi_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [Ioi_inter_Iio]

@[simp]

中文:
定理 image_val_Ioi
  条件: (i : Fin n)
  结论: (↑) '' Ioi i = Ioo (i : 自然数) n
  证明: by
  rw [← preimage_val_Ioi_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [Ioi_inter_Iio]

@[simp]

Depends on / 依赖: Ioi_inter_Iio, image_preimage_eq_inter_range, preimage_val_Ioi_val, range_val
-/
theorem image_val_Ioi (i : Fin n) : (↑) '' Ioi i = Ioo (i : Nat) n := by
  rw [← preimage_val_Ioi_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [Ioi_inter_Iio]

@[simp]
/--
theorem `image_val_Iio` / 定理 `image_val_Iio`

English:
theorem image_val_Iio
  given: (i : Fin n)
  statement: (↑) '' Iio i = Iio (i : Nat)
  proof: by
  rw [← preimage_val_Iio_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact Iio_subset_Iio i.is_lt.le

@[simp]

中文:
定理 image_val_Iio
  条件: (i : Fin n)
  结论: (↑) '' Iio i = Iio (i : 自然数)
  证明: by
  rw [← preimage_val_Iio_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact Iio_subset_Iio i.is_lt.le

@[simp]

Depends on / 依赖: Iio_subset_Iio, i.is_lt.le, image_preimage_eq_inter_range, inter_eq_left, is_lt, preimage_val_Iio_val, range_val
-/
theorem image_val_Iio (i : Fin n) : (↑) '' Iio i = Iio (i : Nat) := by
  rw [← preimage_val_Iio_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact Iio_subset_Iio i.is_lt.le

@[simp]
/--
theorem `image_val_Icc` / 定理 `image_val_Icc`

English:
theorem image_val_Icc
  given: (i j : Fin n)
  statement: (↑) '' Icc i j = Icc (i : Nat) j
  proof: by
  rw [← preimage_val_Icc_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact fun k hk => hk.2.trans_lt j.is_lt

@[simp]

中文:
定理 image_val_Icc
  条件: (i j : Fin n)
  结论: (↑) '' Icc i j = Icc (i : 自然数) j
  证明: by
  rw [← preimage_val_Icc_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact fun k hk => hk.2.trans_lt j.is_lt

@[simp]

Depends on / 依赖: image_preimage_eq_inter_range, inter_eq_left, is_lt, j.is_lt, preimage_val_Icc_val, range_val, trans_lt
-/
theorem image_val_Icc (i j : Fin n) : (↑) '' Icc i j = Icc (i : Nat) j := by
  rw [← preimage_val_Icc_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact fun k hk => hk.2.trans_lt j.is_lt

@[simp]
/--
theorem `image_val_Ico` / 定理 `image_val_Ico`

English:
theorem image_val_Ico
  given: (i j : Fin n)
  statement: (↑) '' Ico i j = Ico (i : Nat) j
  proof: by
  rw [← preimage_val_Ico_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact fun k hk => hk.2.trans j.is_lt

@[simp]

中文:
定理 image_val_Ico
  条件: (i j : Fin n)
  结论: (↑) '' Ico i j = Ico (i : 自然数) j
  证明: by
  rw [← preimage_val_Ico_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact fun k hk => hk.2.trans j.is_lt

@[simp]

Depends on / 依赖: image_preimage_eq_inter_range, inter_eq_left, is_lt, j.is_lt, preimage_val_Ico_val, range_val
-/
theorem image_val_Ico (i j : Fin n) : (↑) '' Ico i j = Ico (i : Nat) j := by
  rw [← preimage_val_Ico_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact fun k hk => hk.2.trans j.is_lt

@[simp]
/--
theorem `image_val_Ioc` / 定理 `image_val_Ioc`

English:
theorem image_val_Ioc
  given: (i j : Fin n)
  statement: (↑) '' Ioc i j = Ioc (i : Nat) j
  proof: by
  rw [← preimage_val_Ioc_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact fun k hk => hk.2.trans_lt j.is_lt

@[simp]

中文:
定理 image_val_Ioc
  条件: (i j : Fin n)
  结论: (↑) '' Ioc i j = Ioc (i : 自然数) j
  证明: by
  rw [← preimage_val_Ioc_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact fun k hk => hk.2.trans_lt j.is_lt

@[simp]

Depends on / 依赖: image_preimage_eq_inter_range, inter_eq_left, is_lt, j.is_lt, preimage_val_Ioc_val, range_val, trans_lt
-/
theorem image_val_Ioc (i j : Fin n) : (↑) '' Ioc i j = Ioc (i : Nat) j := by
  rw [← preimage_val_Ioc_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact fun k hk => hk.2.trans_lt j.is_lt

@[simp]
/--
theorem `image_val_Ioo` / 定理 `image_val_Ioo`

English:
theorem image_val_Ioo
  given: (i j : Fin n)
  statement: (↑) '' Ioo i j = Ioo (i : Nat) j
  proof: by
  rw [← preimage_val_Ioo_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact fun k hk => hk.2.trans j.is_lt

中文:
定理 image_val_Ioo
  条件: (i j : Fin n)
  结论: (↑) '' Ioo i j = Ioo (i : 自然数) j
  证明: by
  rw [← preimage_val_Ioo_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact fun k hk => hk.2.trans j.is_lt

Depends on / 依赖: image_preimage_eq_inter_range, inter_eq_left, is_lt, j.is_lt, preimage_val_Ioo_val, range_val
-/
theorem image_val_Ioo (i j : Fin n) : (↑) '' Ioo i j = Ioo (i : Nat) j := by
  rw [← preimage_val_Ioo_val]; rw [image_preimage_eq_inter_range]; rw [range_val]; rw [inter_eq_left]
  exact fun k hk => hk.2.trans j.is_lt

/--
theorem `image_val_uIcc` / 定理 `image_val_uIcc`

English:
theorem image_val_uIcc
  given: (i j : Fin n)
  statement: (↑) '' uIcc i j = uIcc (i : Nat) j
  proof: by simp [uIcc]

中文:
定理 image_val_uIcc
  条件: (i j : Fin n)
  结论: (↑) '' uIcc i j = uIcc (i : 自然数) j
  证明: by simp [uIcc]
-/
@[simp] theorem image_val_uIcc (i j : Fin n) : (↑) '' uIcc i j = uIcc (i : Nat) j := by simp [uIcc]
/--
theorem `image_val_uIoc` / 定理 `image_val_uIoc`

English:
theorem image_val_uIoc
  given: (i j : Fin n)
  statement: (↑) '' uIoc i j = uIoc (i : Nat) j
  proof: by simp [uIoc]

中文:
定理 image_val_uIoc
  条件: (i j : Fin n)
  结论: (↑) '' uIoc i j = uIoc (i : 自然数) j
  证明: by simp [uIoc]
-/
@[simp] theorem image_val_uIoc (i j : Fin n) : (↑) '' uIoc i j = uIoc (i : Nat) j := by simp [uIoc]
/--
theorem `image_val_uIoo` / 定理 `image_val_uIoo`

English:
theorem image_val_uIoo
  given: (i j : Fin n)
  statement: (↑) '' uIoo i j = uIoo (i : Nat) j
  proof: by simp [uIoo]

中文:
定理 image_val_uIoo
  条件: (i j : Fin n)
  结论: (↑) '' uIoo i j = uIoo (i : 自然数) j
  证明: by simp [uIoo]
-/
@[simp] theorem image_val_uIoo (i j : Fin n) : (↑) '' uIoo i j = uIoo (i : Nat) j := by simp [uIoo]

/-!
### Preimages under `Fin.castLE`
-/

@[simp]
/--
theorem `preimage_castLE_Ici_castLE` / 定理 `preimage_castLE_Ici_castLE`

English:
theorem preimage_castLE_Ici_castLE
  given: (i : Fin m) (h : m <= n)
  proof: rfl

@[simp]

中文:
定理 preimage_castLE_Ici_castLE
  条件: (i : Fin m) (h : m <= n)
  证明: rfl

@[simp]
-/
theorem preimage_castLE_Ici_castLE (i : Fin m) (h : m <= n) :
    castLE h ⁻¹' Ici (castLE h i) = Ici i :=
  rfl

@[simp]
/--
theorem `preimage_castLE_Ioi_castLE` / 定理 `preimage_castLE_Ioi_castLE`

English:
theorem preimage_castLE_Ioi_castLE
  given: (i : Fin m) (h : m <= n)
  proof: rfl

@[simp]

中文:
定理 preimage_castLE_Ioi_castLE
  条件: (i : Fin m) (h : m <= n)
  证明: rfl

@[simp]
-/
theorem preimage_castLE_Ioi_castLE (i : Fin m) (h : m <= n) :
    castLE h ⁻¹' Ioi (castLE h i) = Ioi i :=
  rfl

@[simp]
/--
theorem `preimage_castLE_Iic_castLE` / 定理 `preimage_castLE_Iic_castLE`

English:
theorem preimage_castLE_Iic_castLE
  given: (i : Fin m) (h : m <= n)
  proof: rfl

@[simp]

中文:
定理 preimage_castLE_Iic_castLE
  条件: (i : Fin m) (h : m <= n)
  证明: rfl

@[simp]
-/
theorem preimage_castLE_Iic_castLE (i : Fin m) (h : m <= n) :
    castLE h ⁻¹' Iic (castLE h i) = Iic i :=
  rfl

@[simp]
/--
theorem `preimage_castLE_Iio_castLE` / 定理 `preimage_castLE_Iio_castLE`

English:
theorem preimage_castLE_Iio_castLE
  given: (i : Fin m) (h : m <= n)
  proof: rfl

@[simp]

中文:
定理 preimage_castLE_Iio_castLE
  条件: (i : Fin m) (h : m <= n)
  证明: rfl

@[simp]
-/
theorem preimage_castLE_Iio_castLE (i : Fin m) (h : m <= n) :
    castLE h ⁻¹' Iio (castLE h i) = Iio i :=
  rfl

@[simp]
/--
theorem `preimage_castLE_Icc_castLE` / 定理 `preimage_castLE_Icc_castLE`

English:
theorem preimage_castLE_Icc_castLE
  given: (i j : Fin m) (h : m <= n)
  proof: rfl

@[simp]

中文:
定理 preimage_castLE_Icc_castLE
  条件: (i j : Fin m) (h : m <= n)
  证明: rfl

@[simp]
-/
theorem preimage_castLE_Icc_castLE (i j : Fin m) (h : m <= n) :
    castLE h ⁻¹' Icc (castLE h i) (castLE h j) = Icc i j :=
  rfl

@[simp]
/--
theorem `preimage_castLE_Ico_castLE` / 定理 `preimage_castLE_Ico_castLE`

English:
theorem preimage_castLE_Ico_castLE
  given: (i j : Fin m) (h : m <= n)
  proof: rfl

@[simp]

中文:
定理 preimage_castLE_Ico_castLE
  条件: (i j : Fin m) (h : m <= n)
  证明: rfl

@[simp]
-/
theorem preimage_castLE_Ico_castLE (i j : Fin m) (h : m <= n) :
    castLE h ⁻¹' Ico (castLE h i) (castLE h j) = Ico i j :=
  rfl

@[simp]
/--
theorem `preimage_castLE_Ioc_castLE` / 定理 `preimage_castLE_Ioc_castLE`

English:
theorem preimage_castLE_Ioc_castLE
  given: (i j : Fin m) (h : m <= n)
  proof: rfl

@[simp]

中文:
定理 preimage_castLE_Ioc_castLE
  条件: (i j : Fin m) (h : m <= n)
  证明: rfl

@[simp]
-/
theorem preimage_castLE_Ioc_castLE (i j : Fin m) (h : m <= n) :
    castLE h ⁻¹' Ioc (castLE h i) (castLE h j) = Ioc i j :=
  rfl

@[simp]
/--
theorem `preimage_castLE_Ioo_castLE` / 定理 `preimage_castLE_Ioo_castLE`

English:
theorem preimage_castLE_Ioo_castLE
  given: (i j : Fin m) (h : m <= n)
  proof: rfl

@[simp]

中文:
定理 preimage_castLE_Ioo_castLE
  条件: (i j : Fin m) (h : m <= n)
  证明: rfl

@[simp]
-/
theorem preimage_castLE_Ioo_castLE (i j : Fin m) (h : m <= n) :
    castLE h ⁻¹' Ioo (castLE h i) (castLE h j) = Ioo i j :=
  rfl

@[simp]
/--
theorem `preimage_castLE_uIcc_castLE` / 定理 `preimage_castLE_uIcc_castLE`

English:
theorem preimage_castLE_uIcc_castLE
  given: (i j : Fin m) (h : m <= n)
  proof: rfl

@[simp]

中文:
定理 preimage_castLE_uIcc_castLE
  条件: (i j : Fin m) (h : m <= n)
  证明: rfl

@[simp]
-/
theorem preimage_castLE_uIcc_castLE (i j : Fin m) (h : m <= n) :
    castLE h ⁻¹' uIcc (castLE h i) (castLE h j) = uIcc i j :=
  rfl

@[simp]
/--
theorem `preimage_castLE_uIoc_castLE` / 定理 `preimage_castLE_uIoc_castLE`

English:
theorem preimage_castLE_uIoc_castLE
  given: (i j : Fin m) (h : m <= n)
  proof: rfl

@[simp]

中文:
定理 preimage_castLE_uIoc_castLE
  条件: (i j : Fin m) (h : m <= n)
  证明: rfl

@[simp]
-/
theorem preimage_castLE_uIoc_castLE (i j : Fin m) (h : m <= n) :
    castLE h ⁻¹' uIoc (castLE h i) (castLE h j) = uIoc i j :=
  rfl

@[simp]
/--
theorem `preimage_castLE_uIoo_castLE` / 定理 `preimage_castLE_uIoo_castLE`

English:
theorem preimage_castLE_uIoo_castLE
  given: (i j : Fin m) (h : m <= n)
  proof: rfl

@[simp]

中文:
定理 preimage_castLE_uIoo_castLE
  条件: (i j : Fin m) (h : m <= n)
  证明: rfl

@[simp]
-/
theorem preimage_castLE_uIoo_castLE (i j : Fin m) (h : m <= n) :
    castLE h ⁻¹' uIoo (castLE h i) (castLE h j) = uIoo i j :=
  rfl

@[simp]
/--
theorem `image_castLE_Iic` / 定理 `image_castLE_Iic`

English:
theorem image_castLE_Iic
  given: (i : Fin m) (h : m <= n)
  statement: castLE h '' Iic i = Iic (castLE h i)
  proof: val_injective.image_injective by simp [image_image]

@[simp]

中文:
定理 image_castLE_Iic
  条件: (i : Fin m) (h : m <= n)
  结论: castLE h '' Iic i = Iic (castLE h i)
  证明: val_injective.image_injective by simp [image_image]

@[simp]

Depends on / 依赖: image_image, image_injective, val_injective, val_injective.image_injective
-/
theorem image_castLE_Iic (i : Fin m) (h : m <= n) : castLE h '' Iic i = Iic (castLE h i) :=
val_injective.image_injective by simp [image_image]

@[simp]
/--
theorem `image_castLE_Iio` / 定理 `image_castLE_Iio`

English:
theorem image_castLE_Iio
  given: (i : Fin m) (h : m <= n)
  statement: castLE h '' Iio i = Iio (castLE h i)
  proof: val_injective.image_injective by simp [image_image]

@[simp]

中文:
定理 image_castLE_Iio
  条件: (i : Fin m) (h : m <= n)
  结论: castLE h '' Iio i = Iio (castLE h i)
  证明: val_injective.image_injective by simp [image_image]

@[simp]

Depends on / 依赖: image_image, image_injective, val_injective, val_injective.image_injective
-/
theorem image_castLE_Iio (i : Fin m) (h : m <= n) : castLE h '' Iio i = Iio (castLE h i) :=
val_injective.image_injective by simp [image_image]

@[simp]
/--
theorem `image_castLE_Icc` / 定理 `image_castLE_Icc`

English:
theorem image_castLE_Icc
  given: (i j : Fin m) (h : m <= n)
  proof: val_injective.image_injective by simp [image_image]

@[simp]

中文:
定理 image_castLE_Icc
  条件: (i j : Fin m) (h : m <= n)
  证明: val_injective.image_injective by simp [image_image]

@[simp]

Depends on / 依赖: image_image, image_injective, val_injective, val_injective.image_injective
-/
theorem image_castLE_Icc (i j : Fin m) (h : m <= n) :
    castLE h '' Icc i j = Icc (castLE h i) (castLE h j) :=
val_injective.image_injective by simp [image_image]

@[simp]
/--
theorem `image_castLE_Ico` / 定理 `image_castLE_Ico`

English:
theorem image_castLE_Ico
  given: (i j : Fin m) (h : m <= n)
  proof: val_injective.image_injective by simp [image_image]

@[simp]

中文:
定理 image_castLE_Ico
  条件: (i j : Fin m) (h : m <= n)
  证明: val_injective.image_injective by simp [image_image]

@[simp]

Depends on / 依赖: image_image, image_injective, val_injective, val_injective.image_injective
-/
theorem image_castLE_Ico (i j : Fin m) (h : m <= n) :
    castLE h '' Ico i j = Ico (castLE h i) (castLE h j) :=
val_injective.image_injective by simp [image_image]

@[simp]
/--
theorem `image_castLE_Ioc` / 定理 `image_castLE_Ioc`

English:
theorem image_castLE_Ioc
  given: (i j : Fin m) (h : m <= n)
  proof: val_injective.image_injective by simp [image_image]

@[simp]

中文:
定理 image_castLE_Ioc
  条件: (i j : Fin m) (h : m <= n)
  证明: val_injective.image_injective by simp [image_image]

@[simp]

Depends on / 依赖: image_image, image_injective, val_injective, val_injective.image_injective
-/
theorem image_castLE_Ioc (i j : Fin m) (h : m <= n) :
    castLE h '' Ioc i j = Ioc (castLE h i) (castLE h j) :=
val_injective.image_injective by simp [image_image]

@[simp]
/--
theorem `image_castLE_Ioo` / 定理 `image_castLE_Ioo`

English:
theorem image_castLE_Ioo
  given: (i j : Fin m) (h : m <= n)
  proof: val_injective.image_injective by simp [image_image]

@[simp]

中文:
定理 image_castLE_Ioo
  条件: (i j : Fin m) (h : m <= n)
  证明: val_injective.image_injective by simp [image_image]

@[simp]

Depends on / 依赖: image_image, image_injective, val_injective, val_injective.image_injective
-/
theorem image_castLE_Ioo (i j : Fin m) (h : m <= n) :
    castLE h '' Ioo i j = Ioo (castLE h i) (castLE h j) :=
val_injective.image_injective by simp [image_image]

@[simp]
/--
theorem `image_castLE_uIcc` / 定理 `image_castLE_uIcc`

English:
theorem image_castLE_uIcc
  given: (i j : Fin m) (h : m <= n)
  proof: val_injective.image_injective by simp [image_image]

@[simp]

中文:
定理 image_castLE_uIcc
  条件: (i j : Fin m) (h : m <= n)
  证明: val_injective.image_injective by simp [image_image]

@[simp]

Depends on / 依赖: image_image, image_injective, val_injective, val_injective.image_injective
-/
theorem image_castLE_uIcc (i j : Fin m) (h : m <= n) :
    castLE h '' uIcc i j = uIcc (castLE h i) (castLE h j) :=
val_injective.image_injective by simp [image_image]

@[simp]
/--
theorem `image_castLE_uIoc` / 定理 `image_castLE_uIoc`

English:
theorem image_castLE_uIoc
  given: (i j : Fin m) (h : m <= n)
  proof: val_injective.image_injective by simp [image_image]

@[simp]

中文:
定理 image_castLE_uIoc
  条件: (i j : Fin m) (h : m <= n)
  证明: val_injective.image_injective by simp [image_image]

@[simp]

Depends on / 依赖: image_image, image_injective, val_injective, val_injective.image_injective
-/
theorem image_castLE_uIoc (i j : Fin m) (h : m <= n) :
    castLE h '' uIoc i j = uIoc (castLE h i) (castLE h j) :=
val_injective.image_injective by simp [image_image]

@[simp]
/--
theorem `image_castLE_uIoo` / 定理 `image_castLE_uIoo`

English:
theorem image_castLE_uIoo
  given: (i j : Fin m) (h : m <= n)
  proof: val_injective.image_injective by simp [image_image]

中文:
定理 image_castLE_uIoo
  条件: (i j : Fin m) (h : m <= n)
  证明: val_injective.image_injective by simp [image_image]

Depends on / 依赖: image_image, image_injective, val_injective, val_injective.image_injective
-/
theorem image_castLE_uIoo (i j : Fin m) (h : m <= n) :
    castLE h '' uIoo i j = uIoo (castLE h i) (castLE h j) :=
val_injective.image_injective by simp [image_image]

/-!
### (Pre)images under `Fin.castAdd`
-/

@[simp]
/--
theorem `range_castAdd` / 定理 `range_castAdd`

English:
theorem range_castAdd
  given: [NeZero m]
  statement: range (castAdd m : Fin n -> Fin (n + m)) = Iio (natAdd n 0)
  proof: val_injective.image_injective by simp [← range_comp, comp_def]

@[simp]

中文:
定理 range_castAdd
  条件: [NeZero m]
  结论: range (castAdd m : Fin n -> Fin (n + m)) = Iio (natAdd n 0)
  证明: val_injective.image_injective by simp [← range_comp, comp_def]

@[simp]

Depends on / 依赖: comp_def, image_injective, range_comp, val_injective, val_injective.image_injective
-/
theorem range_castAdd [NeZero m] : range (castAdd m : Fin n -> Fin (n + m)) = Iio (natAdd n 0) :=
val_injective.image_injective by simp [← range_comp, comp_def]

@[simp]
/--
theorem `preimage_castAdd_Ici_castAdd` / 定理 `preimage_castAdd_Ici_castAdd`

English:
theorem preimage_castAdd_Ici_castAdd
  given: (m) (i : Fin n)
  statement: castAdd m ⁻¹' Ici (castAdd m i) = Ici i
  proof: rfl

@[simp]

中文:
定理 preimage_castAdd_Ici_castAdd
  条件: (m) (i : Fin n)
  结论: castAdd m ⁻¹' Ici (castAdd m i) = Ici i
  证明: rfl

@[simp]
-/
theorem preimage_castAdd_Ici_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Ici (castAdd m i) = Ici i :=
  rfl

@[simp]
/--
theorem `preimage_castAdd_Ioi_castAdd` / 定理 `preimage_castAdd_Ioi_castAdd`

English:
theorem preimage_castAdd_Ioi_castAdd
  given: (m) (i : Fin n)
  statement: castAdd m ⁻¹' Ioi (castAdd m i) = Ioi i
  proof: rfl

@[simp]

中文:
定理 preimage_castAdd_Ioi_castAdd
  条件: (m) (i : Fin n)
  结论: castAdd m ⁻¹' Ioi (castAdd m i) = Ioi i
  证明: rfl

@[simp]
-/
theorem preimage_castAdd_Ioi_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Ioi (castAdd m i) = Ioi i :=
  rfl

@[simp]
/--
theorem `preimage_castAdd_Iic_castAdd` / 定理 `preimage_castAdd_Iic_castAdd`

English:
theorem preimage_castAdd_Iic_castAdd
  given: (m) (i : Fin n)
  statement: castAdd m ⁻¹' Iic (castAdd m i) = Iic i
  proof: rfl

@[simp]

中文:
定理 preimage_castAdd_Iic_castAdd
  条件: (m) (i : Fin n)
  结论: castAdd m ⁻¹' Iic (castAdd m i) = Iic i
  证明: rfl

@[simp]
-/
theorem preimage_castAdd_Iic_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Iic (castAdd m i) = Iic i :=
  rfl

@[simp]
/--
theorem `preimage_castAdd_Iio_castAdd` / 定理 `preimage_castAdd_Iio_castAdd`

English:
theorem preimage_castAdd_Iio_castAdd
  given: (m) (i : Fin n)
  statement: castAdd m ⁻¹' Iio (castAdd m i) = Iio i
  proof: rfl

@[simp]

中文:
定理 preimage_castAdd_Iio_castAdd
  条件: (m) (i : Fin n)
  结论: castAdd m ⁻¹' Iio (castAdd m i) = Iio i
  证明: rfl

@[simp]
-/
theorem preimage_castAdd_Iio_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Iio (castAdd m i) = Iio i :=
  rfl

@[simp]
/--
theorem `preimage_castAdd_Icc_castAdd` / 定理 `preimage_castAdd_Icc_castAdd`

English:
theorem preimage_castAdd_Icc_castAdd
  given: (m) (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castAdd_Icc_castAdd
  条件: (m) (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castAdd_Icc_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' Icc (castAdd m i) (castAdd m j) = Icc i j :=
  rfl

@[simp]
/--
theorem `preimage_castAdd_Ico_castAdd` / 定理 `preimage_castAdd_Ico_castAdd`

English:
theorem preimage_castAdd_Ico_castAdd
  given: (m) (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castAdd_Ico_castAdd
  条件: (m) (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castAdd_Ico_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' Ico (castAdd m i) (castAdd m j) = Ico i j :=
  rfl

@[simp]
/--
theorem `preimage_castAdd_Ioc_castAdd` / 定理 `preimage_castAdd_Ioc_castAdd`

English:
theorem preimage_castAdd_Ioc_castAdd
  given: (m) (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castAdd_Ioc_castAdd
  条件: (m) (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castAdd_Ioc_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' Ioc (castAdd m i) (castAdd m j) = Ioc i j :=
  rfl

@[simp]
/--
theorem `preimage_castAdd_Ioo_castAdd` / 定理 `preimage_castAdd_Ioo_castAdd`

English:
theorem preimage_castAdd_Ioo_castAdd
  given: (m) (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castAdd_Ioo_castAdd
  条件: (m) (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castAdd_Ioo_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' Ioo (castAdd m i) (castAdd m j) = Ioo i j :=
  rfl

@[simp]
/--
theorem `preimage_castAdd_uIcc_castAdd` / 定理 `preimage_castAdd_uIcc_castAdd`

English:
theorem preimage_castAdd_uIcc_castAdd
  given: (m) (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castAdd_uIcc_castAdd
  条件: (m) (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castAdd_uIcc_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' uIcc (castAdd m i) (castAdd m j) = uIcc i j :=
  rfl

@[simp]
/--
theorem `preimage_castAdd_uIoc_castAdd` / 定理 `preimage_castAdd_uIoc_castAdd`

English:
theorem preimage_castAdd_uIoc_castAdd
  given: (m) (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castAdd_uIoc_castAdd
  条件: (m) (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castAdd_uIoc_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' uIoc (castAdd m i) (castAdd m j) = uIoc i j :=
  rfl

@[simp]
/--
theorem `preimage_castAdd_uIoo_castAdd` / 定理 `preimage_castAdd_uIoo_castAdd`

English:
theorem preimage_castAdd_uIoo_castAdd
  given: (m) (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castAdd_uIoo_castAdd
  条件: (m) (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castAdd_uIoo_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' uIoo (castAdd m i) (castAdd m j) = uIoo i j :=
  rfl

@[simp]
/--
theorem `image_castAdd_Ici` / 定理 `image_castAdd_Ici`

English:
theorem image_castAdd_Ici
  given: (m) [NeZero m] (i : Fin n)
  proof: val_injective.image_injective by simp [← image_comp]

@[simp]

中文:
定理 image_castAdd_Ici
  条件: (m) [NeZero m] (i : Fin n)
  证明: val_injective.image_injective by simp [← image_comp]

@[simp]

Depends on / 依赖: image_comp, image_injective, val_injective, val_injective.image_injective
-/
theorem image_castAdd_Ici (m) [NeZero m] (i : Fin n) :
    castAdd m '' Ici i = Ico (castAdd m i) (natAdd n 0) :=
val_injective.image_injective by simp [← image_comp]

@[simp]
/--
theorem `image_castAdd_Ioi` / 定理 `image_castAdd_Ioi`

English:
theorem image_castAdd_Ioi
  given: (m) [NeZero m] (i : Fin n)
  proof: val_injective.image_injective by simp [← image_comp]

@[simp]

中文:
定理 image_castAdd_Ioi
  条件: (m) [NeZero m] (i : Fin n)
  证明: val_injective.image_injective by simp [← image_comp]

@[simp]

Depends on / 依赖: image_comp, image_injective, val_injective, val_injective.image_injective
-/
theorem image_castAdd_Ioi (m) [NeZero m] (i : Fin n) :
    castAdd m '' Ioi i = Ioo (castAdd m i) (natAdd n 0) :=
val_injective.image_injective by simp [← image_comp]

@[simp]
/--
theorem `image_castAdd_Iic` / 定理 `image_castAdd_Iic`

English:
theorem image_castAdd_Iic
  given: (m) (i : Fin n)
  statement: castAdd m '' Iic i = Iic (castAdd m i)
  proof: image_castLE_Iic i _

@[simp]

中文:
定理 image_castAdd_Iic
  条件: (m) (i : Fin n)
  结论: castAdd m '' Iic i = Iic (castAdd m i)
  证明: image_castLE_Iic i _

@[simp]

Depends on / 依赖: image_castLE_Iic
-/
theorem image_castAdd_Iic (m) (i : Fin n) : castAdd m '' Iic i = Iic (castAdd m i) :=
  image_castLE_Iic i _

@[simp]
/--
theorem `image_castAdd_Iio` / 定理 `image_castAdd_Iio`

English:
theorem image_castAdd_Iio
  given: (m) (i : Fin n)
  statement: castAdd m '' Iio i = Iio (castAdd m i)
  proof: image_castLE_Iio ..

@[simp]

中文:
定理 image_castAdd_Iio
  条件: (m) (i : Fin n)
  结论: castAdd m '' Iio i = Iio (castAdd m i)
  证明: image_castLE_Iio ..

@[simp]

Depends on / 依赖: image_castLE_Iio
-/
theorem image_castAdd_Iio (m) (i : Fin n) : castAdd m '' Iio i = Iio (castAdd m i) :=
  image_castLE_Iio ..

@[simp]
/--
theorem `image_castAdd_Icc` / 定理 `image_castAdd_Icc`

English:
theorem image_castAdd_Icc
  given: (m) (i j : Fin n)
  proof: image_castLE_Icc ..

@[simp]

中文:
定理 image_castAdd_Icc
  条件: (m) (i j : Fin n)
  证明: image_castLE_Icc ..

@[simp]

Depends on / 依赖: image_castLE_Icc
-/
theorem image_castAdd_Icc (m) (i j : Fin n) :
    castAdd m '' Icc i j = Icc (castAdd m i) (castAdd m j) :=
  image_castLE_Icc ..

@[simp]
/--
theorem `image_castAdd_Ico` / 定理 `image_castAdd_Ico`

English:
theorem image_castAdd_Ico
  given: (m) (i j : Fin n)
  proof: image_castLE_Ico ..

@[simp]

中文:
定理 image_castAdd_Ico
  条件: (m) (i j : Fin n)
  证明: image_castLE_Ico ..

@[simp]

Depends on / 依赖: image_castLE_Ico
-/
theorem image_castAdd_Ico (m) (i j : Fin n) :
    castAdd m '' Ico i j = Ico (castAdd m i) (castAdd m j) :=
  image_castLE_Ico ..

@[simp]
/--
theorem `image_castAdd_Ioc` / 定理 `image_castAdd_Ioc`

English:
theorem image_castAdd_Ioc
  given: (m) (i j : Fin n)
  proof: image_castLE_Ioc ..

@[simp]

中文:
定理 image_castAdd_Ioc
  条件: (m) (i j : Fin n)
  证明: image_castLE_Ioc ..

@[simp]

Depends on / 依赖: image_castLE_Ioc
-/
theorem image_castAdd_Ioc (m) (i j : Fin n) :
    castAdd m '' Ioc i j = Ioc (castAdd m i) (castAdd m j) :=
  image_castLE_Ioc ..

@[simp]
/--
theorem `image_castAdd_Ioo` / 定理 `image_castAdd_Ioo`

English:
theorem image_castAdd_Ioo
  given: (m) (i j : Fin n)
  proof: image_castLE_Ioo ..

@[simp]

中文:
定理 image_castAdd_Ioo
  条件: (m) (i j : Fin n)
  证明: image_castLE_Ioo ..

@[simp]

Depends on / 依赖: image_castLE_Ioo
-/
theorem image_castAdd_Ioo (m) (i j : Fin n) :
    castAdd m '' Ioo i j = Ioo (castAdd m i) (castAdd m j) :=
  image_castLE_Ioo ..

@[simp]
/--
theorem `image_castAdd_uIcc` / 定理 `image_castAdd_uIcc`

English:
theorem image_castAdd_uIcc
  given: (m) (i j : Fin n)
  proof: image_castLE_uIcc ..

@[simp]

中文:
定理 image_castAdd_uIcc
  条件: (m) (i j : Fin n)
  证明: image_castLE_uIcc ..

@[simp]

Depends on / 依赖: image_castLE_uIcc
-/
theorem image_castAdd_uIcc (m) (i j : Fin n) :
    castAdd m '' uIcc i j = uIcc (castAdd m i) (castAdd m j) :=
  image_castLE_uIcc ..

@[simp]
/--
theorem `image_castAdd_uIoc` / 定理 `image_castAdd_uIoc`

English:
theorem image_castAdd_uIoc
  given: (m) (i j : Fin n)
  proof: image_castLE_uIoc ..

@[simp]

中文:
定理 image_castAdd_uIoc
  条件: (m) (i j : Fin n)
  证明: image_castLE_uIoc ..

@[simp]

Depends on / 依赖: image_castLE_uIoc
-/
theorem image_castAdd_uIoc (m) (i j : Fin n) :
    castAdd m '' uIoc i j = uIoc (castAdd m i) (castAdd m j) :=
  image_castLE_uIoc ..

@[simp]
/--
theorem `image_castAdd_uIoo` / 定理 `image_castAdd_uIoo`

English:
theorem image_castAdd_uIoo
  given: (m) (i j : Fin n)
  proof: image_castLE_uIoo ..

中文:
定理 image_castAdd_uIoo
  条件: (m) (i j : Fin n)
  证明: image_castLE_uIoo ..

Depends on / 依赖: image_castLE_uIoo
-/
theorem image_castAdd_uIoo (m) (i j : Fin n) :
    castAdd m '' uIoo i j = uIoo (castAdd m i) (castAdd m j) :=
  image_castLE_uIoo ..


/--
theorem `image_cast` / 定理 `image_cast`

English:
theorem image_cast
  given: (h : m = n) (s : Set (Fin m))
  statement: Fin.cast h '' s = Fin.cast h.symm ⁻¹' s
  proof: (finCongr h).image_eq_preimage_symm _

@[simp]

中文:
定理 image_cast
  条件: (h : m = n) (s : Set (Fin m))
  结论: Fin.cast h '' s = Fin.cast h.symm ⁻¹' s
  证明: (finCongr h).image_eq_preimage_symm _

@[simp]

Depends on / 依赖: finCongr, image_eq_preimage_symm
-/
theorem image_cast (h : m = n) (s : Set (Fin m)) : Fin.cast h '' s = Fin.cast h.symm ⁻¹' s :=
  (finCongr h).image_eq_preimage_symm _

@[simp]
/--
theorem `image_cast_fun` / 定理 `image_cast_fun`

English:
theorem image_cast_fun
  given: (h : m = n)
  statement: image (Fin.cast h) = preimage (Fin.cast h.symm)
  proof: funext image_cast h

@[simp]

中文:
定理 image_cast_fun
  条件: (h : m = n)
  结论: image (Fin.cast h) = preimage (Fin.cast h.symm)
  证明: funext image_cast h

@[simp]

Depends on / 依赖: image_cast
-/
theorem image_cast_fun (h : m = n) : image (Fin.cast h) = preimage (Fin.cast h.symm) :=
funext image_cast h

@[simp]
/--
theorem `preimage_cast_Ici` / 定理 `preimage_cast_Ici`

English:
theorem preimage_cast_Ici
  given: (h : m = n) (i : Fin n)
  statement: .cast h ⁻¹' Ici i = Ici (i.cast h.symm)
  proof: rfl

@[simp]

中文:
定理 preimage_cast_Ici
  条件: (h : m = n) (i : Fin n)
  结论: .cast h ⁻¹' Ici i = Ici (i.cast h.symm)
  证明: rfl

@[simp]
-/
theorem preimage_cast_Ici (h : m = n) (i : Fin n) : .cast h ⁻¹' Ici i = Ici (i.cast h.symm) := rfl

@[simp]
/--
theorem `preimage_cast_Ioi` / 定理 `preimage_cast_Ioi`

English:
theorem preimage_cast_Ioi
  given: (h : m = n) (i : Fin n)
  statement: .cast h ⁻¹' Ioi i = Ioi (i.cast h.symm)
  proof: rfl

@[simp]

中文:
定理 preimage_cast_Ioi
  条件: (h : m = n) (i : Fin n)
  结论: .cast h ⁻¹' Ioi i = Ioi (i.cast h.symm)
  证明: rfl

@[simp]
-/
theorem preimage_cast_Ioi (h : m = n) (i : Fin n) : .cast h ⁻¹' Ioi i = Ioi (i.cast h.symm) := rfl

@[simp]
/--
theorem `preimage_cast_Iic` / 定理 `preimage_cast_Iic`

English:
theorem preimage_cast_Iic
  given: (h : m = n) (i : Fin n)
  statement: .cast h ⁻¹' Iic i = Iic (i.cast h.symm)
  proof: rfl

@[simp]

中文:
定理 preimage_cast_Iic
  条件: (h : m = n) (i : Fin n)
  结论: .cast h ⁻¹' Iic i = Iic (i.cast h.symm)
  证明: rfl

@[simp]
-/
theorem preimage_cast_Iic (h : m = n) (i : Fin n) : .cast h ⁻¹' Iic i = Iic (i.cast h.symm) := rfl

@[simp]
/--
theorem `preimage_cast_Iio` / 定理 `preimage_cast_Iio`

English:
theorem preimage_cast_Iio
  given: (h : m = n) (i : Fin n)
  statement: .cast h ⁻¹' Iio i = Iio (i.cast h.symm)
  proof: rfl

@[simp]

中文:
定理 preimage_cast_Iio
  条件: (h : m = n) (i : Fin n)
  结论: .cast h ⁻¹' Iio i = Iio (i.cast h.symm)
  证明: rfl

@[simp]
-/
theorem preimage_cast_Iio (h : m = n) (i : Fin n) : .cast h ⁻¹' Iio i = Iio (i.cast h.symm) := rfl

@[simp]
/--
theorem `preimage_cast_Icc` / 定理 `preimage_cast_Icc`

English:
theorem preimage_cast_Icc
  given: (h : m = n) (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_cast_Icc
  条件: (h : m = n) (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_cast_Icc (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' Icc i j = Icc (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
/--
theorem `preimage_cast_Ico` / 定理 `preimage_cast_Ico`

English:
theorem preimage_cast_Ico
  given: (h : m = n) (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_cast_Ico
  条件: (h : m = n) (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_cast_Ico (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' Ico i j = Ico (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
/--
theorem `preimage_cast_Ioc` / 定理 `preimage_cast_Ioc`

English:
theorem preimage_cast_Ioc
  given: (h : m = n) (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_cast_Ioc
  条件: (h : m = n) (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_cast_Ioc (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' Ioc i j = Ioc (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
/--
theorem `preimage_cast_Ioo` / 定理 `preimage_cast_Ioo`

English:
theorem preimage_cast_Ioo
  given: (h : m = n) (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_cast_Ioo
  条件: (h : m = n) (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_cast_Ioo (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' Ioo i j = Ioo (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
/--
theorem `preimage_cast_uIcc` / 定理 `preimage_cast_uIcc`

English:
theorem preimage_cast_uIcc
  given: (h : m = n) (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_cast_uIcc
  条件: (h : m = n) (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_cast_uIcc (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' uIcc i j = uIcc (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
/--
theorem `preimage_cast_uIoc` / 定理 `preimage_cast_uIoc`

English:
theorem preimage_cast_uIoc
  given: (h : m = n) (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_cast_uIoc
  条件: (h : m = n) (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_cast_uIoc (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' uIoc i j = uIoc (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
/--
theorem `preimage_cast_uIoo` / 定理 `preimage_cast_uIoo`

English:
theorem preimage_cast_uIoo
  given: (h : m = n) (i j : Fin n)
  proof: rfl

中文:
定理 preimage_cast_uIoo
  条件: (h : m = n) (i j : Fin n)
  证明: rfl
-/
theorem preimage_cast_uIoo (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' uIoo i j = uIoo (i.cast h.symm) (j.cast h.symm) :=
  rfl

/-!
### `Fin.castSucc`
-/

@[simp]
/--
theorem `preimage_castSucc_Ici_castSucc` / 定理 `preimage_castSucc_Ici_castSucc`

English:
theorem preimage_castSucc_Ici_castSucc
  given: (i : Fin n)
  statement: castSucc ⁻¹' Ici i.castSucc = Ici i
  proof: rfl

@[simp]

中文:
定理 preimage_castSucc_Ici_castSucc
  条件: (i : Fin n)
  结论: castSucc ⁻¹' Ici i.castSucc = Ici i
  证明: rfl

@[simp]
-/
theorem preimage_castSucc_Ici_castSucc (i : Fin n) : castSucc ⁻¹' Ici i.castSucc = Ici i := rfl

@[simp]
/--
theorem `preimage_castSucc_Ioi_castSucc` / 定理 `preimage_castSucc_Ioi_castSucc`

English:
theorem preimage_castSucc_Ioi_castSucc
  given: (i : Fin n)
  statement: castSucc ⁻¹' Ioi i.castSucc = Ioi i
  proof: rfl

@[simp]

中文:
定理 preimage_castSucc_Ioi_castSucc
  条件: (i : Fin n)
  结论: castSucc ⁻¹' Ioi i.castSucc = Ioi i
  证明: rfl

@[simp]
-/
theorem preimage_castSucc_Ioi_castSucc (i : Fin n) : castSucc ⁻¹' Ioi i.castSucc = Ioi i := rfl

@[simp]
/--
theorem `preimage_castSucc_Iic_castSucc` / 定理 `preimage_castSucc_Iic_castSucc`

English:
theorem preimage_castSucc_Iic_castSucc
  given: (i : Fin n)
  statement: castSucc ⁻¹' Iic i.castSucc = Iic i
  proof: rfl

@[simp]

中文:
定理 preimage_castSucc_Iic_castSucc
  条件: (i : Fin n)
  结论: castSucc ⁻¹' Iic i.castSucc = Iic i
  证明: rfl

@[simp]
-/
theorem preimage_castSucc_Iic_castSucc (i : Fin n) : castSucc ⁻¹' Iic i.castSucc = Iic i := rfl

@[simp]
/--
theorem `preimage_castSucc_Iio_castSucc` / 定理 `preimage_castSucc_Iio_castSucc`

English:
theorem preimage_castSucc_Iio_castSucc
  given: (i : Fin n)
  statement: castSucc ⁻¹' Iio i.castSucc = Iio i
  proof: rfl

@[simp]

中文:
定理 preimage_castSucc_Iio_castSucc
  条件: (i : Fin n)
  结论: castSucc ⁻¹' Iio i.castSucc = Iio i
  证明: rfl

@[simp]
-/
theorem preimage_castSucc_Iio_castSucc (i : Fin n) : castSucc ⁻¹' Iio i.castSucc = Iio i := rfl

@[simp]
/--
theorem `preimage_castSucc_Icc_castSucc` / 定理 `preimage_castSucc_Icc_castSucc`

English:
theorem preimage_castSucc_Icc_castSucc
  given: (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castSucc_Icc_castSucc
  条件: (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castSucc_Icc_castSucc (i j : Fin n) :
    castSucc ⁻¹' Icc i.castSucc j.castSucc = Icc i j :=
  rfl

@[simp]
/--
theorem `preimage_castSucc_Ico_castSucc` / 定理 `preimage_castSucc_Ico_castSucc`

English:
theorem preimage_castSucc_Ico_castSucc
  given: (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castSucc_Ico_castSucc
  条件: (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castSucc_Ico_castSucc (i j : Fin n) :
    castSucc ⁻¹' Ico i.castSucc j.castSucc = Ico i j :=
  rfl

@[simp]
/--
theorem `preimage_castSucc_Ioc_castSucc` / 定理 `preimage_castSucc_Ioc_castSucc`

English:
theorem preimage_castSucc_Ioc_castSucc
  given: (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castSucc_Ioc_castSucc
  条件: (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castSucc_Ioc_castSucc (i j : Fin n) :
    castSucc ⁻¹' Ioc i.castSucc j.castSucc = Ioc i j :=
  rfl

@[simp]
/--
theorem `preimage_castSucc_Ioo_castSucc` / 定理 `preimage_castSucc_Ioo_castSucc`

English:
theorem preimage_castSucc_Ioo_castSucc
  given: (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castSucc_Ioo_castSucc
  条件: (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castSucc_Ioo_castSucc (i j : Fin n) :
    castSucc ⁻¹' Ioo i.castSucc j.castSucc = Ioo i j :=
  rfl

@[simp]
/--
theorem `preimage_castSucc_uIcc_castSucc` / 定理 `preimage_castSucc_uIcc_castSucc`

English:
theorem preimage_castSucc_uIcc_castSucc
  given: (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castSucc_uIcc_castSucc
  条件: (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castSucc_uIcc_castSucc (i j : Fin n) :
    castSucc ⁻¹' uIcc i.castSucc j.castSucc = uIcc i j :=
  rfl

@[simp]
/--
theorem `preimage_castSucc_uIoc_castSucc` / 定理 `preimage_castSucc_uIoc_castSucc`

English:
theorem preimage_castSucc_uIoc_castSucc
  given: (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castSucc_uIoc_castSucc
  条件: (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castSucc_uIoc_castSucc (i j : Fin n) :
    castSucc ⁻¹' uIoc i.castSucc j.castSucc = uIoc i j :=
  rfl

@[simp]
/--
theorem `preimage_castSucc_uIoo_castSucc` / 定理 `preimage_castSucc_uIoo_castSucc`

English:
theorem preimage_castSucc_uIoo_castSucc
  given: (i j : Fin n)
  proof: rfl

@[simp]

中文:
定理 preimage_castSucc_uIoo_castSucc
  条件: (i j : Fin n)
  证明: rfl

@[simp]
-/
theorem preimage_castSucc_uIoo_castSucc (i j : Fin n) :
    castSucc ⁻¹' uIoo i.castSucc j.castSucc = uIoo i j :=
  rfl

@[simp]
/--
theorem `image_castSucc_Ici` / 定理 `image_castSucc_Ici`

English:
theorem image_castSucc_Ici
  given: (i : Fin n)
  statement: castSucc '' Ici i = Ico i.castSucc (.last n)
  proof: image_castAdd_Ici ..

@[simp]

中文:
定理 image_castSucc_Ici
  条件: (i : Fin n)
  结论: castSucc '' Ici i = Ico i.castSucc (.last n)
  证明: image_castAdd_Ici ..

@[simp]

Depends on / 依赖: image_castAdd_Ici
-/
theorem image_castSucc_Ici (i : Fin n) : castSucc '' Ici i = Ico i.castSucc (.last n) :=
  image_castAdd_Ici ..

@[simp]
/--
theorem `image_castSucc_Ioi` / 定理 `image_castSucc_Ioi`

English:
theorem image_castSucc_Ioi
  given: (i : Fin n)
  statement: castSucc '' Ioi i = Ioo i.castSucc (.last n)
  proof: image_castAdd_Ioi ..

@[simp]

中文:
定理 image_castSucc_Ioi
  条件: (i : Fin n)
  结论: castSucc '' Ioi i = Ioo i.castSucc (.last n)
  证明: image_castAdd_Ioi ..

@[simp]

Depends on / 依赖: image_castAdd_Ioi
-/
theorem image_castSucc_Ioi (i : Fin n) : castSucc '' Ioi i = Ioo i.castSucc (.last n) :=
  image_castAdd_Ioi ..

@[simp]
/--
theorem `image_castSucc_Iic` / 定理 `image_castSucc_Iic`

English:
theorem image_castSucc_Iic
  given: (i : Fin n)
  statement: castSucc '' Iic i = Iic i.castSucc
  proof: image_castAdd_Iic ..

@[simp]

中文:
定理 image_castSucc_Iic
  条件: (i : Fin n)
  结论: castSucc '' Iic i = Iic i.castSucc
  证明: image_castAdd_Iic ..

@[simp]

Depends on / 依赖: image_castAdd_Iic
-/
theorem image_castSucc_Iic (i : Fin n) : castSucc '' Iic i = Iic i.castSucc :=
  image_castAdd_Iic ..

@[simp]
/--
theorem `image_castSucc_Iio` / 定理 `image_castSucc_Iio`

English:
theorem image_castSucc_Iio
  given: (i : Fin n)
  statement: castSucc '' Iio i = Iio i.castSucc
  proof: image_castAdd_Iio ..

@[simp]

中文:
定理 image_castSucc_Iio
  条件: (i : Fin n)
  结论: castSucc '' Iio i = Iio i.castSucc
  证明: image_castAdd_Iio ..

@[simp]

Depends on / 依赖: image_castAdd_Iio
-/
theorem image_castSucc_Iio (i : Fin n) : castSucc '' Iio i = Iio i.castSucc :=
  image_castAdd_Iio ..

@[simp]
/--
theorem `image_castSucc_Icc` / 定理 `image_castSucc_Icc`

English:
theorem image_castSucc_Icc
  given: (i j : Fin n)
  statement: castSucc '' Icc i j = Icc i.castSucc j.castSucc
  proof: image_castAdd_Icc ..

@[simp]

中文:
定理 image_castSucc_Icc
  条件: (i j : Fin n)
  结论: castSucc '' Icc i j = Icc i.castSucc j.castSucc
  证明: image_castAdd_Icc ..

@[simp]

Depends on / 依赖: image_castAdd_Icc
-/
theorem image_castSucc_Icc (i j : Fin n) : castSucc '' Icc i j = Icc i.castSucc j.castSucc :=
  image_castAdd_Icc ..

@[simp]
/--
theorem `image_castSucc_Ico` / 定理 `image_castSucc_Ico`

English:
theorem image_castSucc_Ico
  given: (i j : Fin n)
  statement: castSucc '' Ico i j = Ico i.castSucc j.castSucc
  proof: image_castAdd_Ico ..

@[simp]

中文:
定理 image_castSucc_Ico
  条件: (i j : Fin n)
  结论: castSucc '' Ico i j = Ico i.castSucc j.castSucc
  证明: image_castAdd_Ico ..

@[simp]

Depends on / 依赖: image_castAdd_Ico
-/
theorem image_castSucc_Ico (i j : Fin n) : castSucc '' Ico i j = Ico i.castSucc j.castSucc :=
  image_castAdd_Ico ..

@[simp]
/--
theorem `image_castSucc_Ioc` / 定理 `image_castSucc_Ioc`

English:
theorem image_castSucc_Ioc
  given: (i j : Fin n)
  statement: castSucc '' Ioc i j = Ioc i.castSucc j.castSucc
  proof: image_castAdd_Ioc ..

@[simp]

中文:
定理 image_castSucc_Ioc
  条件: (i j : Fin n)
  结论: castSucc '' Ioc i j = Ioc i.castSucc j.castSucc
  证明: image_castAdd_Ioc ..

@[simp]

Depends on / 依赖: image_castAdd_Ioc
-/
theorem image_castSucc_Ioc (i j : Fin n) : castSucc '' Ioc i j = Ioc i.castSucc j.castSucc :=
  image_castAdd_Ioc ..

@[simp]
/--
theorem `image_castSucc_Ioo` / 定理 `image_castSucc_Ioo`

English:
theorem image_castSucc_Ioo
  given: (i j : Fin n)
  statement: castSucc '' Ioo i j = Ioo i.castSucc j.castSucc
  proof: image_castAdd_Ioo ..

@[simp]

中文:
定理 image_castSucc_Ioo
  条件: (i j : Fin n)
  结论: castSucc '' Ioo i j = Ioo i.castSucc j.castSucc
  证明: image_castAdd_Ioo ..

@[simp]

Depends on / 依赖: image_castAdd_Ioo
-/
theorem image_castSucc_Ioo (i j : Fin n) : castSucc '' Ioo i j = Ioo i.castSucc j.castSucc :=
  image_castAdd_Ioo ..

@[simp]
/--
theorem `image_castSucc_uIcc` / 定理 `image_castSucc_uIcc`

English:
theorem image_castSucc_uIcc
  given: (i j : Fin n)
  statement: castSucc '' uIcc i j = uIcc i.castSucc j.castSucc
  proof: image_castAdd_uIcc ..

@[simp]

中文:
定理 image_castSucc_uIcc
  条件: (i j : Fin n)
  结论: castSucc '' uIcc i j = uIcc i.castSucc j.castSucc
  证明: image_castAdd_uIcc ..

@[simp]

Depends on / 依赖: image_castAdd_uIcc
-/
theorem image_castSucc_uIcc (i j : Fin n) : castSucc '' uIcc i j = uIcc i.castSucc j.castSucc :=
  image_castAdd_uIcc ..

@[simp]
/--
theorem `image_castSucc_uIoc` / 定理 `image_castSucc_uIoc`

English:
theorem image_castSucc_uIoc
  given: (i j : Fin n)
  statement: castSucc '' uIoc i j = uIoc i.castSucc j.castSucc
  proof: image_castAdd_uIoc ..

@[simp]

中文:
定理 image_castSucc_uIoc
  条件: (i j : Fin n)
  结论: castSucc '' uIoc i j = uIoc i.castSucc j.castSucc
  证明: image_castAdd_uIoc ..

@[simp]

Depends on / 依赖: image_castAdd_uIoc
-/
theorem image_castSucc_uIoc (i j : Fin n) : castSucc '' uIoc i j = uIoc i.castSucc j.castSucc :=
  image_castAdd_uIoc ..

@[simp]
/--
theorem `image_castSucc_uIoo` / 定理 `image_castSucc_uIoo`

English:
theorem image_castSucc_uIoo
  given: (i j : Fin n)
  statement: castSucc '' uIoo i j = uIoo i.castSucc j.castSucc
  proof: image_castAdd_uIoo ..

中文:
定理 image_castSucc_uIoo
  条件: (i j : Fin n)
  结论: castSucc '' uIoo i j = uIoo i.castSucc j.castSucc
  证明: image_castAdd_uIoo ..

Depends on / 依赖: image_castAdd_uIoo
-/
theorem image_castSucc_uIoo (i j : Fin n) : castSucc '' uIoo i j = uIoo i.castSucc j.castSucc :=
  image_castAdd_uIoo ..


/--
theorem `range_natAdd` / 定理 `range_natAdd`

English:
theorem range_natAdd
  given: (m n : Nat)
  statement: range (natAdd m : Fin n -> Fin (m + n)) = {i | m <= i.1}
  proof: by
  ext i
  constructor
  · rintro ⟨i, rfl⟩
    apply le_coe_natAdd
  · refine fun (hi : m <= i) => ⟨⟨i - m, by lia⟩, ?_⟩
    ext
    simp [hi]

中文:
定理 range_natAdd
  条件: (m n : 自然数)
  结论: range (natAdd m : Fin n -> Fin (m + n)) = {i | m <= i.1}
  证明: by
  ext i
  constructor
  · rintro ⟨i, rfl⟩
    apply le_coe_natAdd
  · refine fun (hi : m <= i) => ⟨⟨i - m, by lia⟩, ?_⟩
    ext
    simp [hi]

Depends on / 依赖: le_coe_natAdd
-/
theorem range_natAdd (m n : Nat) : range (natAdd m : Fin n -> Fin (m + n)) = {i | m <= i.1} := by
  ext i
  constructor
  · rintro ⟨i, rfl⟩
    apply le_coe_natAdd
  · refine fun (hi : m <= i) => ⟨⟨i - m, by lia⟩, ?_⟩
    ext
    simp [hi]

/--
theorem `range_natAdd_eq_Ici` / 定理 `range_natAdd_eq_Ici`

English:
theorem range_natAdd_eq_Ici
  given: (m n : Nat) [NeZero n]
  proof: range_natAdd m n

中文:
定理 range_natAdd_eq_Ici
  条件: (m n : 自然数) [NeZero n]
  证明: range_natAdd m n

Depends on / 依赖: range_natAdd
-/
theorem range_natAdd_eq_Ici (m n : Nat) [NeZero n] :
    range (natAdd m : Fin n -> Fin (m + n)) = Ici (natAdd m 0) :=
  range_natAdd m n

/--
theorem `range_natAdd_eq_Ioi` / 定理 `range_natAdd_eq_Ioi`

English:
theorem range_natAdd_eq_Ioi
  given: (m n : Nat) [NeZero m]
  proof: by
  ext ⟨_, _⟩
  simp [range_natAdd, lt_def, ← Nat.succ_le_iff, Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)]

@[simp]

中文:
定理 range_natAdd_eq_Ioi
  条件: (m n : 自然数) [NeZero m]
  证明: by
  ext ⟨_, _⟩
  simp [range_natAdd, lt_def, ← Nat.succ_le_iff, Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)]

@[simp]

Depends on / 依赖: Nat.one_le_iff_ne_zero.mpr, Nat.succ_le_iff, NeZero, NeZero.ne, lt_def, one_le_iff_ne_zero, range_natAdd, succ_le_iff
-/
theorem range_natAdd_eq_Ioi (m n : Nat) [NeZero m] :
    range (natAdd m : Fin n -> Fin (m + n)) = Ioi (castAdd n ⊤) := by
  ext ⟨_, _⟩
  simp [range_natAdd, lt_def, ← Nat.succ_le_iff, Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)]

@[simp]
/--
theorem `preimage_natAdd_Ici_natAdd` / 定理 `preimage_natAdd_Ici_natAdd`

English:
theorem preimage_natAdd_Ici_natAdd
  given: (m) (i : Fin n)
  statement: natAdd m ⁻¹' Ici (natAdd m i) = Ici i
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_natAdd_Ici_natAdd
  条件: (m) (i : Fin n)
  结论: natAdd m ⁻¹' Ici (natAdd m i) = Ici i
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_natAdd_Ici_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Ici (natAdd m i) = Ici i := by
  ext; simp

@[simp]
/--
theorem `preimage_natAdd_Ioi_natAdd` / 定理 `preimage_natAdd_Ioi_natAdd`

English:
theorem preimage_natAdd_Ioi_natAdd
  given: (m) (i : Fin n)
  statement: natAdd m ⁻¹' Ioi (natAdd m i) = Ioi i
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_natAdd_Ioi_natAdd
  条件: (m) (i : Fin n)
  结论: natAdd m ⁻¹' Ioi (natAdd m i) = Ioi i
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_natAdd_Ioi_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Ioi (natAdd m i) = Ioi i := by
  ext; simp

@[simp]
/--
theorem `preimage_natAdd_Iic_natAdd` / 定理 `preimage_natAdd_Iic_natAdd`

English:
theorem preimage_natAdd_Iic_natAdd
  given: (m) (i : Fin n)
  statement: natAdd m ⁻¹' Iic (natAdd m i) = Iic i
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_natAdd_Iic_natAdd
  条件: (m) (i : Fin n)
  结论: natAdd m ⁻¹' Iic (natAdd m i) = Iic i
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_natAdd_Iic_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Iic (natAdd m i) = Iic i := by
  ext; simp

@[simp]
/--
theorem `preimage_natAdd_Iio_natAdd` / 定理 `preimage_natAdd_Iio_natAdd`

English:
theorem preimage_natAdd_Iio_natAdd
  given: (m) (i : Fin n)
  statement: natAdd m ⁻¹' Iio (natAdd m i) = Iio i
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_natAdd_Iio_natAdd
  条件: (m) (i : Fin n)
  结论: natAdd m ⁻¹' Iio (natAdd m i) = Iio i
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_natAdd_Iio_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Iio (natAdd m i) = Iio i := by
  ext; simp

@[simp]
/--
theorem `preimage_natAdd_Icc_natAdd` / 定理 `preimage_natAdd_Icc_natAdd`

English:
theorem preimage_natAdd_Icc_natAdd
  given: (m) (i j : Fin n)
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_natAdd_Icc_natAdd
  条件: (m) (i j : Fin n)
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_natAdd_Icc_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' Icc (natAdd m i) (natAdd m j) = Icc i j := by
  ext; simp

@[simp]
/--
theorem `preimage_natAdd_Ico_natAdd` / 定理 `preimage_natAdd_Ico_natAdd`

English:
theorem preimage_natAdd_Ico_natAdd
  given: (m) (i j : Fin n)
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_natAdd_Ico_natAdd
  条件: (m) (i j : Fin n)
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_natAdd_Ico_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' Ico (natAdd m i) (natAdd m j) = Ico i j := by
  ext; simp

@[simp]
/--
theorem `preimage_natAdd_Ioc_natAdd` / 定理 `preimage_natAdd_Ioc_natAdd`

English:
theorem preimage_natAdd_Ioc_natAdd
  given: (m) (i j : Fin n)
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_natAdd_Ioc_natAdd
  条件: (m) (i j : Fin n)
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_natAdd_Ioc_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' Ioc (natAdd m i) (natAdd m j) = Ioc i j := by
  ext; simp

@[simp]
/--
theorem `preimage_natAdd_Ioo_natAdd` / 定理 `preimage_natAdd_Ioo_natAdd`

English:
theorem preimage_natAdd_Ioo_natAdd
  given: (m) (i j : Fin n)
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_natAdd_Ioo_natAdd
  条件: (m) (i j : Fin n)
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_natAdd_Ioo_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' Ioo (natAdd m i) (natAdd m j) = Ioo i j := by
  ext; simp

@[simp]
/--
theorem `preimage_natAdd_uIcc_natAdd` / 定理 `preimage_natAdd_uIcc_natAdd`

English:
theorem preimage_natAdd_uIcc_natAdd
  given: (m) (i j : Fin n)
  proof: by
  simp [uIcc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]

中文:
定理 preimage_natAdd_uIcc_natAdd
  条件: (m) (i j : Fin n)
  证明: by
  simp [uIcc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]

Depends on / 依赖: map_max, map_min, monotone, monotone.map_max, monotone.map_min, strictMono_natAdd
-/
theorem preimage_natAdd_uIcc_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' uIcc (natAdd m i) (natAdd m j) = uIcc i j := by
  simp [uIcc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
/--
theorem `preimage_natAdd_uIoc_natAdd` / 定理 `preimage_natAdd_uIoc_natAdd`

English:
theorem preimage_natAdd_uIoc_natAdd
  given: (m) (i j : Fin n)
  proof: by
  simp [uIoc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]

中文:
定理 preimage_natAdd_uIoc_natAdd
  条件: (m) (i j : Fin n)
  证明: by
  simp [uIoc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]

Depends on / 依赖: map_max, map_min, monotone, monotone.map_max, monotone.map_min, strictMono_natAdd
-/
theorem preimage_natAdd_uIoc_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' uIoc (natAdd m i) (natAdd m j) = uIoc i j := by
  simp [uIoc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
/--
theorem `preimage_natAdd_uIoo_natAdd` / 定理 `preimage_natAdd_uIoo_natAdd`

English:
theorem preimage_natAdd_uIoo_natAdd
  given: (m) (i j : Fin n)
  proof: by
  simp [uIoo, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]

中文:
定理 preimage_natAdd_uIoo_natAdd
  条件: (m) (i j : Fin n)
  证明: by
  simp [uIoo, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]

Depends on / 依赖: map_max, map_min, monotone, monotone.map_max, monotone.map_min, strictMono_natAdd
-/
theorem preimage_natAdd_uIoo_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' uIoo (natAdd m i) (natAdd m j) = uIoo i j := by
  simp [uIoo, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
/--
theorem `image_natAdd_Ici` / 定理 `image_natAdd_Ici`

English:
theorem image_natAdd_Ici
  given: (m) (i : Fin n)
  statement: natAdd m '' Ici i = Ici (natAdd m i)
  proof: by
  rw [← preimage_natAdd_Ici_natAdd]; rw [image_preimage_eq_of_subset]
  rw [range_natAdd]
  exact fun j hj => Nat.le_trans (le_coe_natAdd ..) hj

@[simp]

中文:
定理 image_natAdd_Ici
  条件: (m) (i : Fin n)
  结论: natAdd m '' Ici i = Ici (natAdd m i)
  证明: by
  rw [← preimage_natAdd_Ici_natAdd]; rw [image_preimage_eq_of_subset]
  rw [range_natAdd]
  exact fun j hj => Nat.le_trans (le_coe_natAdd ..) hj

@[simp]

Depends on / 依赖: Nat.le_trans, image_preimage_eq_of_subset, le_coe_natAdd, le_trans, preimage_natAdd_Ici_natAdd, range_natAdd
-/
theorem image_natAdd_Ici (m) (i : Fin n) : natAdd m '' Ici i = Ici (natAdd m i) := by
  rw [← preimage_natAdd_Ici_natAdd]; rw [image_preimage_eq_of_subset]
  rw [range_natAdd]
  exact fun j hj => Nat.le_trans (le_coe_natAdd ..) hj

@[simp]
/--
theorem `image_natAdd_Ioi` / 定理 `image_natAdd_Ioi`

English:
theorem image_natAdd_Ioi
  given: (m) (i : Fin n)
  statement: natAdd m '' Ioi i = Ioi (natAdd m i)
  proof: by
  rw [← preimage_natAdd_Ioi_natAdd]; rw [image_preimage_eq_of_subset]
exact Ioi_subset_Ici_self.trans image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]

中文:
定理 image_natAdd_Ioi
  条件: (m) (i : Fin n)
  结论: natAdd m '' Ioi i = Ioi (natAdd m i)
  证明: by
  rw [← preimage_natAdd_Ioi_natAdd]; rw [image_preimage_eq_of_subset]
exact Ioi_subset_Ici_self.trans image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]

Depends on / 依赖: Ioi_subset_Ici_self, Ioi_subset_Ici_self.trans, image_natAdd_Ici, image_preimage_eq_of_subset, image_subset_range, preimage_natAdd_Ioi_natAdd
-/
theorem image_natAdd_Ioi (m) (i : Fin n) : natAdd m '' Ioi i = Ioi (natAdd m i) := by
  rw [← preimage_natAdd_Ioi_natAdd]; rw [image_preimage_eq_of_subset]
exact Ioi_subset_Ici_self.trans image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]
/--
theorem `image_natAdd_Icc` / 定理 `image_natAdd_Icc`

English:
theorem image_natAdd_Icc
  given: (m) (i j : Fin n)
  proof: by
  rw [← preimage_natAdd_Icc_natAdd]; rw [image_preimage_eq_of_subset]
exact Icc_subset_Ici_self.trans image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]

中文:
定理 image_natAdd_Icc
  条件: (m) (i j : Fin n)
  证明: by
  rw [← preimage_natAdd_Icc_natAdd]; rw [image_preimage_eq_of_subset]
exact Icc_subset_Ici_self.trans image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]

Depends on / 依赖: Icc_subset_Ici_self, Icc_subset_Ici_self.trans, image_natAdd_Ici, image_preimage_eq_of_subset, image_subset_range, preimage_natAdd_Icc_natAdd
-/
theorem image_natAdd_Icc (m) (i j : Fin n) :
    natAdd m '' Icc i j = Icc (natAdd m i) (natAdd m j) := by
  rw [← preimage_natAdd_Icc_natAdd]; rw [image_preimage_eq_of_subset]
exact Icc_subset_Ici_self.trans image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]
/--
theorem `image_natAdd_Ico` / 定理 `image_natAdd_Ico`

English:
theorem image_natAdd_Ico
  given: (m) (i j : Fin n)
  proof: by
  rw [← preimage_natAdd_Ico_natAdd]; rw [image_preimage_eq_of_subset]
exact Ico_subset_Ici_self.trans image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]

中文:
定理 image_natAdd_Ico
  条件: (m) (i j : Fin n)
  证明: by
  rw [← preimage_natAdd_Ico_natAdd]; rw [image_preimage_eq_of_subset]
exact Ico_subset_Ici_self.trans image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]

Depends on / 依赖: Ico_subset_Ici_self, Ico_subset_Ici_self.trans, image_natAdd_Ici, image_preimage_eq_of_subset, image_subset_range, preimage_natAdd_Ico_natAdd
-/
theorem image_natAdd_Ico (m) (i j : Fin n) :
    natAdd m '' Ico i j = Ico (natAdd m i) (natAdd m j) := by
  rw [← preimage_natAdd_Ico_natAdd]; rw [image_preimage_eq_of_subset]
exact Ico_subset_Ici_self.trans image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]
/--
theorem `image_natAdd_Ioc` / 定理 `image_natAdd_Ioc`

English:
theorem image_natAdd_Ioc
  given: (m) (i j : Fin n)
  proof: by
  rw [← preimage_natAdd_Ioc_natAdd]; rw [image_preimage_eq_of_subset]
exact Ioc_subset_Ioi_self.trans image_natAdd_Ioi m i ▸ image_subset_range _ _

@[simp]

中文:
定理 image_natAdd_Ioc
  条件: (m) (i j : Fin n)
  证明: by
  rw [← preimage_natAdd_Ioc_natAdd]; rw [image_preimage_eq_of_subset]
exact Ioc_subset_Ioi_self.trans image_natAdd_Ioi m i ▸ image_subset_range _ _

@[simp]

Depends on / 依赖: Ioc_subset_Ioi_self, Ioc_subset_Ioi_self.trans, image_natAdd_Ioi, image_preimage_eq_of_subset, image_subset_range, preimage_natAdd_Ioc_natAdd
-/
theorem image_natAdd_Ioc (m) (i j : Fin n) :
    natAdd m '' Ioc i j = Ioc (natAdd m i) (natAdd m j) := by
  rw [← preimage_natAdd_Ioc_natAdd]; rw [image_preimage_eq_of_subset]
exact Ioc_subset_Ioi_self.trans image_natAdd_Ioi m i ▸ image_subset_range _ _

@[simp]
/--
theorem `image_natAdd_Ioo` / 定理 `image_natAdd_Ioo`

English:
theorem image_natAdd_Ioo
  given: (m) (i j : Fin n)
  proof: by
  rw [← preimage_natAdd_Ioo_natAdd]; rw [image_preimage_eq_of_subset]
exact Ioo_subset_Ioi_self.trans image_natAdd_Ioi m i ▸ image_subset_range _ _

@[simp]

中文:
定理 image_natAdd_Ioo
  条件: (m) (i j : Fin n)
  证明: by
  rw [← preimage_natAdd_Ioo_natAdd]; rw [image_preimage_eq_of_subset]
exact Ioo_subset_Ioi_self.trans image_natAdd_Ioi m i ▸ image_subset_range _ _

@[simp]

Depends on / 依赖: Ioo_subset_Ioi_self, Ioo_subset_Ioi_self.trans, image_natAdd_Ioi, image_preimage_eq_of_subset, image_subset_range, preimage_natAdd_Ioo_natAdd
-/
theorem image_natAdd_Ioo (m) (i j : Fin n) :
    natAdd m '' Ioo i j = Ioo (natAdd m i) (natAdd m j) := by
  rw [← preimage_natAdd_Ioo_natAdd]; rw [image_preimage_eq_of_subset]
exact Ioo_subset_Ioi_self.trans image_natAdd_Ioi m i ▸ image_subset_range _ _

@[simp]
/--
theorem `image_natAdd_uIcc` / 定理 `image_natAdd_uIcc`

English:
theorem image_natAdd_uIcc
  given: (m) (i j : Fin n)
  proof: by
  simp [uIcc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]

中文:
定理 image_natAdd_uIcc
  条件: (m) (i j : Fin n)
  证明: by
  simp [uIcc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]

Depends on / 依赖: map_max, map_min, monotone, monotone.map_max, monotone.map_min, strictMono_natAdd
-/
theorem image_natAdd_uIcc (m) (i j : Fin n) :
    natAdd m '' uIcc i j = uIcc (natAdd m i) (natAdd m j) := by
  simp [uIcc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
/--
theorem `image_natAdd_uIoc` / 定理 `image_natAdd_uIoc`

English:
theorem image_natAdd_uIoc
  given: (m) (i j : Fin n)
  proof: by
  simp [uIoc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]

中文:
定理 image_natAdd_uIoc
  条件: (m) (i j : Fin n)
  证明: by
  simp [uIoc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]

Depends on / 依赖: map_max, map_min, monotone, monotone.map_max, monotone.map_min, strictMono_natAdd
-/
theorem image_natAdd_uIoc (m) (i j : Fin n) :
    natAdd m '' uIoc i j = uIoc (natAdd m i) (natAdd m j) := by
  simp [uIoc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
/--
theorem `image_natAdd_uIoo` / 定理 `image_natAdd_uIoo`

English:
theorem image_natAdd_uIoo
  given: (m) (i j : Fin n)
  proof: by
  simp [uIoo, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

中文:
定理 image_natAdd_uIoo
  条件: (m) (i j : Fin n)
  证明: by
  simp [uIoo, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

Depends on / 依赖: map_max, map_min, monotone, monotone.map_max, monotone.map_min, strictMono_natAdd
-/
theorem image_natAdd_uIoo (m) (i j : Fin n) :
    natAdd m '' uIoo i j = uIoo (natAdd m i) (natAdd m j) := by
  simp [uIoo, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

/-!
### `Fin.addNat`
-/

@[simp]
/--
theorem `preimage_addNat_Ici_addNat` / 定理 `preimage_addNat_Ici_addNat`

English:
theorem preimage_addNat_Ici_addNat
  given: (m) (i : Fin n)
  statement: (addNat · m) ⁻¹' Ici (i.addNat m) = Ici i
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_addNat_Ici_addNat
  条件: (m) (i : Fin n)
  结论: (add自然数 · m) ⁻¹' Ici (i.add自然数 m) = Ici i
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_addNat_Ici_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Ici (i.addNat m) = Ici i := by
  ext; simp

@[simp]
/--
theorem `preimage_addNat_Ioi_addNat` / 定理 `preimage_addNat_Ioi_addNat`

English:
theorem preimage_addNat_Ioi_addNat
  given: (m) (i : Fin n)
  statement: (addNat · m) ⁻¹' Ioi (i.addNat m) = Ioi i
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_addNat_Ioi_addNat
  条件: (m) (i : Fin n)
  结论: (add自然数 · m) ⁻¹' Ioi (i.add自然数 m) = Ioi i
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_addNat_Ioi_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Ioi (i.addNat m) = Ioi i := by
  ext; simp

@[simp]
/--
theorem `preimage_addNat_Iic_addNat` / 定理 `preimage_addNat_Iic_addNat`

English:
theorem preimage_addNat_Iic_addNat
  given: (m) (i : Fin n)
  statement: (addNat · m) ⁻¹' Iic (i.addNat m) = Iic i
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_addNat_Iic_addNat
  条件: (m) (i : Fin n)
  结论: (add自然数 · m) ⁻¹' Iic (i.add自然数 m) = Iic i
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_addNat_Iic_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Iic (i.addNat m) = Iic i := by
  ext; simp

@[simp]
/--
theorem `preimage_addNat_Iio_addNat` / 定理 `preimage_addNat_Iio_addNat`

English:
theorem preimage_addNat_Iio_addNat
  given: (m) (i : Fin n)
  statement: (addNat · m) ⁻¹' Iio (i.addNat m) = Iio i
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_addNat_Iio_addNat
  条件: (m) (i : Fin n)
  结论: (add自然数 · m) ⁻¹' Iio (i.add自然数 m) = Iio i
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_addNat_Iio_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Iio (i.addNat m) = Iio i := by
  ext; simp

@[simp]
/--
theorem `preimage_addNat_Icc_addNat` / 定理 `preimage_addNat_Icc_addNat`

English:
theorem preimage_addNat_Icc_addNat
  given: (m) (i j : Fin n)
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_addNat_Icc_addNat
  条件: (m) (i j : Fin n)
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_addNat_Icc_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' Icc (i.addNat m) (j.addNat m) = Icc i j := by
  ext; simp

@[simp]
/--
theorem `preimage_addNat_Ico_addNat` / 定理 `preimage_addNat_Ico_addNat`

English:
theorem preimage_addNat_Ico_addNat
  given: (m) (i j : Fin n)
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_addNat_Ico_addNat
  条件: (m) (i j : Fin n)
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_addNat_Ico_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' Ico (i.addNat m) (j.addNat m) = Ico i j := by
  ext; simp

@[simp]
/--
theorem `preimage_addNat_Ioc_addNat` / 定理 `preimage_addNat_Ioc_addNat`

English:
theorem preimage_addNat_Ioc_addNat
  given: (m) (i j : Fin n)
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_addNat_Ioc_addNat
  条件: (m) (i j : Fin n)
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_addNat_Ioc_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' Ioc (i.addNat m) (j.addNat m) = Ioc i j := by
  ext; simp

@[simp]
/--
theorem `preimage_addNat_Ioo_addNat` / 定理 `preimage_addNat_Ioo_addNat`

English:
theorem preimage_addNat_Ioo_addNat
  given: (m) (i j : Fin n)
  proof: by
  ext; simp

@[simp]

中文:
定理 preimage_addNat_Ioo_addNat
  条件: (m) (i j : Fin n)
  证明: by
  ext; simp

@[simp]
-/
theorem preimage_addNat_Ioo_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' Ioo (i.addNat m) (j.addNat m) = Ioo i j := by
  ext; simp

@[simp]
/--
theorem `preimage_addNat_uIcc_addNat` / 定理 `preimage_addNat_uIcc_addNat`

English:
theorem preimage_addNat_uIcc_addNat
  given: (m) (i j : Fin n)
  proof: by
  simp [uIcc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]

中文:
定理 preimage_addNat_uIcc_addNat
  条件: (m) (i j : Fin n)
  证明: by
  simp [uIcc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]

Depends on / 依赖: map_max, map_min, monotone, monotone.map_max, monotone.map_min, strictMono_addNat
-/
theorem preimage_addNat_uIcc_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' uIcc (i.addNat m) (j.addNat m) = uIcc i j := by
  simp [uIcc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
/--
theorem `preimage_addNat_uIoc_addNat` / 定理 `preimage_addNat_uIoc_addNat`

English:
theorem preimage_addNat_uIoc_addNat
  given: (m) (i j : Fin n)
  proof: by
  simp [uIoc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]

中文:
定理 preimage_addNat_uIoc_addNat
  条件: (m) (i j : Fin n)
  证明: by
  simp [uIoc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]

Depends on / 依赖: map_max, map_min, monotone, monotone.map_max, monotone.map_min, strictMono_addNat
-/
theorem preimage_addNat_uIoc_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' uIoc (i.addNat m) (j.addNat m) = uIoc i j := by
  simp [uIoc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
/--
theorem `preimage_addNat_uIoo_addNat` / 定理 `preimage_addNat_uIoo_addNat`

English:
theorem preimage_addNat_uIoo_addNat
  given: (m) (i j : Fin n)
  proof: by
  simp [uIoo, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]

中文:
定理 preimage_addNat_uIoo_addNat
  条件: (m) (i j : Fin n)
  证明: by
  simp [uIoo, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]

Depends on / 依赖: map_max, map_min, monotone, monotone.map_max, monotone.map_min, strictMono_addNat
-/
theorem preimage_addNat_uIoo_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' uIoo (i.addNat m) (j.addNat m) = uIoo i j := by
  simp [uIoo, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
/--
theorem `image_addNat_Ici` / 定理 `image_addNat_Ici`

English:
theorem image_addNat_Ici
  given: (m) (i : Fin n)
  statement: (addNat · m) '' Ici i = Ici (i.addNat m)
  proof: by
  rw [← preimage_addNat_Ici_addNat]; rw [image_preimage_eq_of_subset]
  intro j hj
  have : (i : Nat) + m <= j := hj
  refine ⟨⟨j - m, by lia⟩, ?_⟩
  simp (disch := lia)

@[simp]

中文:
定理 image_addNat_Ici
  条件: (m) (i : Fin n)
  结论: (add自然数 · m) '' Ici i = Ici (i.add自然数 m)
  证明: by
  rw [← preimage_addNat_Ici_addNat]; rw [image_preimage_eq_of_subset]
  intro j hj
  have : (i : Nat) + m <= j := hj
  refine ⟨⟨j - m, by lia⟩, ?_⟩
  simp (disch := lia)

@[simp]

Depends on / 依赖: image_preimage_eq_of_subset, preimage_addNat_Ici_addNat
-/
theorem image_addNat_Ici (m) (i : Fin n) : (addNat · m) '' Ici i = Ici (i.addNat m) := by
  rw [← preimage_addNat_Ici_addNat]; rw [image_preimage_eq_of_subset]
  intro j hj
  have : (i : Nat) + m <= j := hj
  refine ⟨⟨j - m, by lia⟩, ?_⟩
  simp (disch := lia)

@[simp]
/--
theorem `image_addNat_Ioi` / 定理 `image_addNat_Ioi`

English:
theorem image_addNat_Ioi
  given: (m) (i : Fin n)
  statement: (addNat · m) '' Ioi i = Ioi (i.addNat m)
  proof: by
  rw [← preimage_addNat_Ioi_addNat]; rw [image_preimage_eq_of_subset]
exact Ioi_subset_Ici_self.trans image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]

中文:
定理 image_addNat_Ioi
  条件: (m) (i : Fin n)
  结论: (add自然数 · m) '' Ioi i = Ioi (i.add自然数 m)
  证明: by
  rw [← preimage_addNat_Ioi_addNat]; rw [image_preimage_eq_of_subset]
exact Ioi_subset_Ici_self.trans image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]

Depends on / 依赖: Ioi_subset_Ici_self, Ioi_subset_Ici_self.trans, image_addNat_Ici, image_preimage_eq_of_subset, image_subset_range, preimage_addNat_Ioi_addNat
-/
theorem image_addNat_Ioi (m) (i : Fin n) : (addNat · m) '' Ioi i = Ioi (i.addNat m) := by
  rw [← preimage_addNat_Ioi_addNat]; rw [image_preimage_eq_of_subset]
exact Ioi_subset_Ici_self.trans image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]
/--
theorem `image_addNat_Icc` / 定理 `image_addNat_Icc`

English:
theorem image_addNat_Icc
  given: (m) (i j : Fin n)
  proof: by
  rw [← preimage_addNat_Icc_addNat]; rw [image_preimage_eq_of_subset]
exact Icc_subset_Ici_self.trans image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]

中文:
定理 image_addNat_Icc
  条件: (m) (i j : Fin n)
  证明: by
  rw [← preimage_addNat_Icc_addNat]; rw [image_preimage_eq_of_subset]
exact Icc_subset_Ici_self.trans image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]

Depends on / 依赖: Icc_subset_Ici_self, Icc_subset_Ici_self.trans, image_addNat_Ici, image_preimage_eq_of_subset, image_subset_range, preimage_addNat_Icc_addNat
-/
theorem image_addNat_Icc (m) (i j : Fin n) :
    (addNat · m) '' Icc i j = Icc (i.addNat m) (j.addNat m) := by
  rw [← preimage_addNat_Icc_addNat]; rw [image_preimage_eq_of_subset]
exact Icc_subset_Ici_self.trans image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]
/--
theorem `image_addNat_Ico` / 定理 `image_addNat_Ico`

English:
theorem image_addNat_Ico
  given: (m) (i j : Fin n)
  proof: by
  rw [← preimage_addNat_Ico_addNat]; rw [image_preimage_eq_of_subset]
exact Ico_subset_Ici_self.trans image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]

中文:
定理 image_addNat_Ico
  条件: (m) (i j : Fin n)
  证明: by
  rw [← preimage_addNat_Ico_addNat]; rw [image_preimage_eq_of_subset]
exact Ico_subset_Ici_self.trans image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]

Depends on / 依赖: Ico_subset_Ici_self, Ico_subset_Ici_self.trans, image_addNat_Ici, image_preimage_eq_of_subset, image_subset_range, preimage_addNat_Ico_addNat
-/
theorem image_addNat_Ico (m) (i j : Fin n) :
    (addNat · m) '' Ico i j = Ico (i.addNat m) (j.addNat m) := by
  rw [← preimage_addNat_Ico_addNat]; rw [image_preimage_eq_of_subset]
exact Ico_subset_Ici_self.trans image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]
/--
theorem `image_addNat_Ioc` / 定理 `image_addNat_Ioc`

English:
theorem image_addNat_Ioc
  given: (m) (i j : Fin n)
  proof: by
  rw [← preimage_addNat_Ioc_addNat]; rw [image_preimage_eq_of_subset]
exact Ioc_subset_Ioi_self.trans image_addNat_Ioi m i ▸ image_subset_range _ _

@[simp]

中文:
定理 image_addNat_Ioc
  条件: (m) (i j : Fin n)
  证明: by
  rw [← preimage_addNat_Ioc_addNat]; rw [image_preimage_eq_of_subset]
exact Ioc_subset_Ioi_self.trans image_addNat_Ioi m i ▸ image_subset_range _ _

@[simp]

Depends on / 依赖: Ioc_subset_Ioi_self, Ioc_subset_Ioi_self.trans, image_addNat_Ioi, image_preimage_eq_of_subset, image_subset_range, preimage_addNat_Ioc_addNat
-/
theorem image_addNat_Ioc (m) (i j : Fin n) :
    (addNat · m) '' Ioc i j = Ioc (i.addNat m) (j.addNat m) := by
  rw [← preimage_addNat_Ioc_addNat]; rw [image_preimage_eq_of_subset]
exact Ioc_subset_Ioi_self.trans image_addNat_Ioi m i ▸ image_subset_range _ _

@[simp]
/--
theorem `image_addNat_Ioo` / 定理 `image_addNat_Ioo`

English:
theorem image_addNat_Ioo
  given: (m) (i j : Fin n)
  proof: by
  rw [← preimage_addNat_Ioo_addNat]; rw [image_preimage_eq_of_subset]
exact Ioo_subset_Ioi_self.trans image_addNat_Ioi m i ▸ image_subset_range _ _

@[simp]

中文:
定理 image_addNat_Ioo
  条件: (m) (i j : Fin n)
  证明: by
  rw [← preimage_addNat_Ioo_addNat]; rw [image_preimage_eq_of_subset]
exact Ioo_subset_Ioi_self.trans image_addNat_Ioi m i ▸ image_subset_range _ _

@[simp]

Depends on / 依赖: Ioo_subset_Ioi_self, Ioo_subset_Ioi_self.trans, image_addNat_Ioi, image_preimage_eq_of_subset, image_subset_range, preimage_addNat_Ioo_addNat
-/
theorem image_addNat_Ioo (m) (i j : Fin n) :
    (addNat · m) '' Ioo i j = Ioo (i.addNat m) (j.addNat m) := by
  rw [← preimage_addNat_Ioo_addNat]; rw [image_preimage_eq_of_subset]
exact Ioo_subset_Ioi_self.trans image_addNat_Ioi m i ▸ image_subset_range _ _

@[simp]
/--
theorem `image_addNat_uIcc` / 定理 `image_addNat_uIcc`

English:
theorem image_addNat_uIcc
  given: (m) (i j : Fin n)
  proof: by
  simp [uIcc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]

中文:
定理 image_addNat_uIcc
  条件: (m) (i j : Fin n)
  证明: by
  simp [uIcc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]

Depends on / 依赖: map_max, map_min, monotone, monotone.map_max, monotone.map_min, strictMono_addNat
-/
theorem image_addNat_uIcc (m) (i j : Fin n) :
    (addNat · m) '' uIcc i j = uIcc (i.addNat m) (j.addNat m) := by
  simp [uIcc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
/--
theorem `image_addNat_uIoc` / 定理 `image_addNat_uIoc`

English:
theorem image_addNat_uIoc
  given: (m) (i j : Fin n)
  proof: by
  simp [uIoc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]

中文:
定理 image_addNat_uIoc
  条件: (m) (i j : Fin n)
  证明: by
  simp [uIoc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]

Depends on / 依赖: map_max, map_min, monotone, monotone.map_max, monotone.map_min, strictMono_addNat
-/
theorem image_addNat_uIoc (m) (i j : Fin n) :
    (addNat · m) '' uIoc i j = uIoc (i.addNat m) (j.addNat m) := by
  simp [uIoc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
/--
theorem `image_addNat_uIoo` / 定理 `image_addNat_uIoo`

English:
theorem image_addNat_uIoo
  given: (m) (i j : Fin n)
  proof: by
  simp [uIoo, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

中文:
定理 image_addNat_uIoo
  条件: (m) (i j : Fin n)
  证明: by
  simp [uIoo, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

Depends on / 依赖: map_max, map_min, monotone, monotone.map_max, monotone.map_min, strictMono_addNat
-/
theorem image_addNat_uIoo (m) (i j : Fin n) :
    (addNat · m) '' uIoo i j = uIoo (i.addNat m) (j.addNat m) := by
  simp [uIoo, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

/-!
### `Fin.succ`
-/

@[simp]
/--
theorem `preimage_succ_Ici_succ` / 定理 `preimage_succ_Ici_succ`

English:
theorem preimage_succ_Ici_succ
  given: (i : Fin n)
  statement: succ ⁻¹' Ici i.succ = Ici i
  proof: preimage_addNat_Ici_addNat ..

@[simp]

中文:
定理 preimage_succ_Ici_succ
  条件: (i : Fin n)
  结论: succ ⁻¹' Ici i.succ = Ici i
  证明: preimage_addNat_Ici_addNat ..

@[simp]

Depends on / 依赖: preimage_addNat_Ici_addNat
-/
theorem preimage_succ_Ici_succ (i : Fin n) : succ ⁻¹' Ici i.succ = Ici i :=
  preimage_addNat_Ici_addNat ..

@[simp]
/--
theorem `preimage_succ_Ioi_succ` / 定理 `preimage_succ_Ioi_succ`

English:
theorem preimage_succ_Ioi_succ
  given: (i : Fin n)
  statement: succ ⁻¹' Ioi i.succ = Ioi i
  proof: preimage_addNat_Ioi_addNat ..

@[simp]

中文:
定理 preimage_succ_Ioi_succ
  条件: (i : Fin n)
  结论: succ ⁻¹' Ioi i.succ = Ioi i
  证明: preimage_addNat_Ioi_addNat ..

@[simp]

Depends on / 依赖: preimage_addNat_Ioi_addNat
-/
theorem preimage_succ_Ioi_succ (i : Fin n) : succ ⁻¹' Ioi i.succ = Ioi i :=
  preimage_addNat_Ioi_addNat ..

@[simp]
/--
theorem `preimage_succ_Iic_succ` / 定理 `preimage_succ_Iic_succ`

English:
theorem preimage_succ_Iic_succ
  given: (i : Fin n)
  statement: succ ⁻¹' Iic i.succ = Iic i
  proof: preimage_addNat_Iic_addNat ..

@[simp]

中文:
定理 preimage_succ_Iic_succ
  条件: (i : Fin n)
  结论: succ ⁻¹' Iic i.succ = Iic i
  证明: preimage_addNat_Iic_addNat ..

@[simp]

Depends on / 依赖: preimage_addNat_Iic_addNat
-/
theorem preimage_succ_Iic_succ (i : Fin n) : succ ⁻¹' Iic i.succ = Iic i :=
  preimage_addNat_Iic_addNat ..

@[simp]
/--
theorem `preimage_succ_Iio_succ` / 定理 `preimage_succ_Iio_succ`

English:
theorem preimage_succ_Iio_succ
  given: (i : Fin n)
  statement: succ ⁻¹' Iio i.succ = Iio i
  proof: preimage_addNat_Iio_addNat ..

@[simp]

中文:
定理 preimage_succ_Iio_succ
  条件: (i : Fin n)
  结论: succ ⁻¹' Iio i.succ = Iio i
  证明: preimage_addNat_Iio_addNat ..

@[simp]

Depends on / 依赖: preimage_addNat_Iio_addNat
-/
theorem preimage_succ_Iio_succ (i : Fin n) : succ ⁻¹' Iio i.succ = Iio i :=
  preimage_addNat_Iio_addNat ..

@[simp]
/--
theorem `preimage_succ_Icc_succ` / 定理 `preimage_succ_Icc_succ`

English:
theorem preimage_succ_Icc_succ
  given: (i j : Fin n)
  statement: succ ⁻¹' Icc i.succ j.succ = Icc i j
  proof: preimage_addNat_Icc_addNat ..

@[simp]

中文:
定理 preimage_succ_Icc_succ
  条件: (i j : Fin n)
  结论: succ ⁻¹' Icc i.succ j.succ = Icc i j
  证明: preimage_addNat_Icc_addNat ..

@[simp]

Depends on / 依赖: preimage_addNat_Icc_addNat
-/
theorem preimage_succ_Icc_succ (i j : Fin n) : succ ⁻¹' Icc i.succ j.succ = Icc i j :=
  preimage_addNat_Icc_addNat ..

@[simp]
/--
theorem `preimage_succ_Ico_succ` / 定理 `preimage_succ_Ico_succ`

English:
theorem preimage_succ_Ico_succ
  given: (i j : Fin n)
  statement: succ ⁻¹' Ico i.succ j.succ = Ico i j
  proof: preimage_addNat_Ico_addNat ..

@[simp]

中文:
定理 preimage_succ_Ico_succ
  条件: (i j : Fin n)
  结论: succ ⁻¹' Ico i.succ j.succ = Ico i j
  证明: preimage_addNat_Ico_addNat ..

@[simp]

Depends on / 依赖: preimage_addNat_Ico_addNat
-/
theorem preimage_succ_Ico_succ (i j : Fin n) : succ ⁻¹' Ico i.succ j.succ = Ico i j :=
  preimage_addNat_Ico_addNat ..

@[simp]
/--
theorem `preimage_succ_Ioc_succ` / 定理 `preimage_succ_Ioc_succ`

English:
theorem preimage_succ_Ioc_succ
  given: (i j : Fin n)
  statement: succ ⁻¹' Ioc i.succ j.succ = Ioc i j
  proof: preimage_addNat_Ioc_addNat ..

@[simp]

中文:
定理 preimage_succ_Ioc_succ
  条件: (i j : Fin n)
  结论: succ ⁻¹' Ioc i.succ j.succ = Ioc i j
  证明: preimage_addNat_Ioc_addNat ..

@[simp]

Depends on / 依赖: preimage_addNat_Ioc_addNat
-/
theorem preimage_succ_Ioc_succ (i j : Fin n) : succ ⁻¹' Ioc i.succ j.succ = Ioc i j :=
  preimage_addNat_Ioc_addNat ..

@[simp]
/--
theorem `preimage_succ_Ioo_succ` / 定理 `preimage_succ_Ioo_succ`

English:
theorem preimage_succ_Ioo_succ
  given: (i j : Fin n)
  statement: succ ⁻¹' Ioo i.succ j.succ = Ioo i j
  proof: preimage_addNat_Ioo_addNat ..

@[simp]

中文:
定理 preimage_succ_Ioo_succ
  条件: (i j : Fin n)
  结论: succ ⁻¹' Ioo i.succ j.succ = Ioo i j
  证明: preimage_addNat_Ioo_addNat ..

@[simp]

Depends on / 依赖: preimage_addNat_Ioo_addNat
-/
theorem preimage_succ_Ioo_succ (i j : Fin n) : succ ⁻¹' Ioo i.succ j.succ = Ioo i j :=
  preimage_addNat_Ioo_addNat ..

@[simp]
/--
theorem `preimage_succ_uIcc_succ` / 定理 `preimage_succ_uIcc_succ`

English:
theorem preimage_succ_uIcc_succ
  given: (i j : Fin n)
  statement: succ ⁻¹' uIcc i.succ j.succ = uIcc i j
  proof: preimage_addNat_uIcc_addNat ..

@[simp]

中文:
定理 preimage_succ_uIcc_succ
  条件: (i j : Fin n)
  结论: succ ⁻¹' uIcc i.succ j.succ = uIcc i j
  证明: preimage_addNat_uIcc_addNat ..

@[simp]

Depends on / 依赖: preimage_addNat_uIcc_addNat
-/
theorem preimage_succ_uIcc_succ (i j : Fin n) : succ ⁻¹' uIcc i.succ j.succ = uIcc i j :=
  preimage_addNat_uIcc_addNat ..

@[simp]
/--
theorem `preimage_succ_uIoc_succ` / 定理 `preimage_succ_uIoc_succ`

English:
theorem preimage_succ_uIoc_succ
  given: (i j : Fin n)
  statement: succ ⁻¹' uIoc i.succ j.succ = uIoc i j
  proof: preimage_addNat_uIoc_addNat ..

@[simp]

中文:
定理 preimage_succ_uIoc_succ
  条件: (i j : Fin n)
  结论: succ ⁻¹' uIoc i.succ j.succ = uIoc i j
  证明: preimage_addNat_uIoc_addNat ..

@[simp]

Depends on / 依赖: preimage_addNat_uIoc_addNat
-/
theorem preimage_succ_uIoc_succ (i j : Fin n) : succ ⁻¹' uIoc i.succ j.succ = uIoc i j :=
  preimage_addNat_uIoc_addNat ..

@[simp]
/--
theorem `preimage_succ_uIoo_succ` / 定理 `preimage_succ_uIoo_succ`

English:
theorem preimage_succ_uIoo_succ
  given: (i j : Fin n)
  statement: succ ⁻¹' uIoo i.succ j.succ = uIoo i j
  proof: preimage_addNat_uIoo_addNat ..

中文:
定理 preimage_succ_uIoo_succ
  条件: (i j : Fin n)
  结论: succ ⁻¹' uIoo i.succ j.succ = uIoo i j
  证明: preimage_addNat_uIoo_addNat ..

Depends on / 依赖: preimage_addNat_uIoo_addNat
-/
theorem preimage_succ_uIoo_succ (i j : Fin n) : succ ⁻¹' uIoo i.succ j.succ = uIoo i j :=
  preimage_addNat_uIoo_addNat ..

/--
theorem `image_succ_Ici` / 定理 `image_succ_Ici`

English:
theorem image_succ_Ici
  given: (i : Fin n)
  statement: succ '' Ici i = Ici i.succ
  proof: image_addNat_Ici ..

中文:
定理 image_succ_Ici
  条件: (i : Fin n)
  结论: succ '' Ici i = Ici i.succ
  证明: image_addNat_Ici ..
-/
@[simp] theorem image_succ_Ici (i : Fin n) : succ '' Ici i = Ici i.succ := image_addNat_Ici ..
/--
theorem `image_succ_Ioi` / 定理 `image_succ_Ioi`

English:
theorem image_succ_Ioi
  given: (i : Fin n)
  statement: succ '' Ioi i = Ioi i.succ
  proof: image_addNat_Ioi ..

@[simp]

中文:
定理 image_succ_Ioi
  条件: (i : Fin n)
  结论: succ '' Ioi i = Ioi i.succ
  证明: image_addNat_Ioi ..

@[simp]
-/
@[simp] theorem image_succ_Ioi (i : Fin n) : succ '' Ioi i = Ioi i.succ := image_addNat_Ioi ..

@[simp]
/--
theorem `image_succ_Iic` / 定理 `image_succ_Iic`

English:
theorem image_succ_Iic
  given: (i : Fin n)
  statement: succ '' Iic i = Ioc 0 i.succ
  proof: by
  refine Subset.antisymm (image_subset_iff.mpr fun j hj => ⟨j.succ_pos, succ_le_succ_iff.2 hj⟩) ?_
  rintro j ⟨hj₀, hj⟩
  rcases exists_succ_eq_of_ne_zero hj₀.ne' with ⟨j, rfl⟩
exact mem_image_of_mem _ succ_le_succ_iff.mp hj

@[simp]

中文:
定理 image_succ_Iic
  条件: (i : Fin n)
  结论: succ '' Iic i = Ioc 0 i.succ
  证明: by
  refine Subset.antisymm (image_subset_iff.mpr fun j hj => ⟨j.succ_pos, succ_le_succ_iff.2 hj⟩) ?_
  rintro j ⟨hj₀, hj⟩
  rcases exists_succ_eq_of_ne_zero hj₀.ne' with ⟨j, rfl⟩
exact mem_image_of_mem _ succ_le_succ_iff.mp hj

@[simp]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, exists_succ_eq_of_ne_zero, image_subset_iff, image_subset_iff.mpr, j.succ_pos, mem_image_of_mem, succ_le_succ_iff, succ_le_succ_iff.mp, succ_pos
-/
theorem image_succ_Iic (i : Fin n) : succ '' Iic i = Ioc 0 i.succ := by
  refine Subset.antisymm (image_subset_iff.mpr fun j hj => ⟨j.succ_pos, succ_le_succ_iff.2 hj⟩) ?_
  rintro j ⟨hj₀, hj⟩
  rcases exists_succ_eq_of_ne_zero hj₀.ne' with ⟨j, rfl⟩
exact mem_image_of_mem _ succ_le_succ_iff.mp hj

@[simp]
/--
theorem `image_succ_Iio` / 定理 `image_succ_Iio`

English:
theorem image_succ_Iio
  given: (i : Fin n)
  statement: succ '' Iio i = Ioo 0 i.succ
  proof: by
  refine Subset.antisymm (image_subset_iff.mpr fun j hj => ⟨j.succ_pos, succ_lt_succ_iff.2 hj⟩) ?_
  rintro j ⟨hj₀, hj⟩
  rcases exists_succ_eq_of_ne_zero hj₀.ne' with ⟨j, rfl⟩
exact mem_image_of_mem _ succ_lt_succ_iff.mp hj

@[simp]

中文:
定理 image_succ_Iio
  条件: (i : Fin n)
  结论: succ '' Iio i = Ioo 0 i.succ
  证明: by
  refine Subset.antisymm (image_subset_iff.mpr fun j hj => ⟨j.succ_pos, succ_lt_succ_iff.2 hj⟩) ?_
  rintro j ⟨hj₀, hj⟩
  rcases exists_succ_eq_of_ne_zero hj₀.ne' with ⟨j, rfl⟩
exact mem_image_of_mem _ succ_lt_succ_iff.mp hj

@[simp]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, exists_succ_eq_of_ne_zero, image_subset_iff, image_subset_iff.mpr, j.succ_pos, mem_image_of_mem, succ_lt_succ_iff, succ_lt_succ_iff.mp, succ_pos
-/
theorem image_succ_Iio (i : Fin n) : succ '' Iio i = Ioo 0 i.succ := by
  refine Subset.antisymm (image_subset_iff.mpr fun j hj => ⟨j.succ_pos, succ_lt_succ_iff.2 hj⟩) ?_
  rintro j ⟨hj₀, hj⟩
  rcases exists_succ_eq_of_ne_zero hj₀.ne' with ⟨j, rfl⟩
exact mem_image_of_mem _ succ_lt_succ_iff.mp hj

@[simp]
/--
theorem `image_succ_Icc` / 定理 `image_succ_Icc`

English:
theorem image_succ_Icc
  given: (i j : Fin n)
  statement: succ '' Icc i j = Icc i.succ j.succ
  proof: image_addNat_Icc ..

@[simp]

中文:
定理 image_succ_Icc
  条件: (i j : Fin n)
  结论: succ '' Icc i j = Icc i.succ j.succ
  证明: image_addNat_Icc ..

@[simp]

Depends on / 依赖: image_addNat_Icc
-/
theorem image_succ_Icc (i j : Fin n) : succ '' Icc i j = Icc i.succ j.succ := image_addNat_Icc ..

@[simp]
/--
theorem `image_succ_Ico` / 定理 `image_succ_Ico`

English:
theorem image_succ_Ico
  given: (i j : Fin n)
  statement: succ '' Ico i j = Ico i.succ j.succ
  proof: image_addNat_Ico ..

@[simp]

中文:
定理 image_succ_Ico
  条件: (i j : Fin n)
  结论: succ '' Ico i j = Ico i.succ j.succ
  证明: image_addNat_Ico ..

@[simp]

Depends on / 依赖: image_addNat_Ico
-/
theorem image_succ_Ico (i j : Fin n) : succ '' Ico i j = Ico i.succ j.succ := image_addNat_Ico ..

@[simp]
/--
theorem `image_succ_Ioc` / 定理 `image_succ_Ioc`

English:
theorem image_succ_Ioc
  given: (i j : Fin n)
  statement: succ '' Ioc i j = Ioc i.succ j.succ
  proof: image_addNat_Ioc ..

@[simp]

中文:
定理 image_succ_Ioc
  条件: (i j : Fin n)
  结论: succ '' Ioc i j = Ioc i.succ j.succ
  证明: image_addNat_Ioc ..

@[simp]

Depends on / 依赖: image_addNat_Ioc
-/
theorem image_succ_Ioc (i j : Fin n) : succ '' Ioc i j = Ioc i.succ j.succ := image_addNat_Ioc ..

@[simp]
/--
theorem `image_succ_Ioo` / 定理 `image_succ_Ioo`

English:
theorem image_succ_Ioo
  given: (i j : Fin n)
  statement: succ '' Ioo i j = Ioo i.succ j.succ
  proof: image_addNat_Ioo ..

@[simp]

中文:
定理 image_succ_Ioo
  条件: (i j : Fin n)
  结论: succ '' Ioo i j = Ioo i.succ j.succ
  证明: image_addNat_Ioo ..

@[simp]

Depends on / 依赖: image_addNat_Ioo
-/
theorem image_succ_Ioo (i j : Fin n) : succ '' Ioo i j = Ioo i.succ j.succ := image_addNat_Ioo ..

@[simp]
/--
theorem `image_succ_uIcc` / 定理 `image_succ_uIcc`

English:
theorem image_succ_uIcc
  given: (i j : Fin n)
  statement: succ '' uIcc i j = uIcc i.succ j.succ
  proof: image_addNat_uIcc ..

@[simp]

中文:
定理 image_succ_uIcc
  条件: (i j : Fin n)
  结论: succ '' uIcc i j = uIcc i.succ j.succ
  证明: image_addNat_uIcc ..

@[simp]

Depends on / 依赖: image_addNat_uIcc
-/
theorem image_succ_uIcc (i j : Fin n) : succ '' uIcc i j = uIcc i.succ j.succ :=
  image_addNat_uIcc ..

@[simp]
/--
theorem `image_succ_uIoc` / 定理 `image_succ_uIoc`

English:
theorem image_succ_uIoc
  given: (i j : Fin n)
  statement: succ '' uIoc i j = uIoc i.succ j.succ
  proof: image_addNat_uIoc ..

@[simp]

中文:
定理 image_succ_uIoc
  条件: (i j : Fin n)
  结论: succ '' uIoc i j = uIoc i.succ j.succ
  证明: image_addNat_uIoc ..

@[simp]

Depends on / 依赖: image_addNat_uIoc
-/
theorem image_succ_uIoc (i j : Fin n) : succ '' uIoc i j = uIoc i.succ j.succ :=
  image_addNat_uIoc ..

@[simp]
/--
theorem `image_succ_uIoo` / 定理 `image_succ_uIoo`

English:
theorem image_succ_uIoo
  given: (i j : Fin n)
  statement: succ '' uIoo i j = uIoo i.succ j.succ
  proof: image_addNat_uIoo ..

中文:
定理 image_succ_uIoo
  条件: (i j : Fin n)
  结论: succ '' uIoo i j = uIoo i.succ j.succ
  证明: image_addNat_uIoo ..

Depends on / 依赖: image_addNat_uIoo
-/
theorem image_succ_uIoo (i j : Fin n) : succ '' uIoo i j = uIoo i.succ j.succ :=
  image_addNat_uIoo ..

/-!
### `Fin.rev`
-/

@[simp]
/--
theorem `range_rev` / 定理 `range_rev`

English:
theorem range_rev
  statement: range (rev : Fin n -> Fin n) = univ
  proof: rev_surjective.range_eq

中文:
定理 range_rev
  结论: range (rev : Fin n -> Fin n) = univ
  证明: rev_surjective.range_eq

Depends on / 依赖: range_eq, rev_surjective, rev_surjective.range_eq
-/
theorem range_rev : range (rev : Fin n -> Fin n) = univ := rev_surjective.range_eq

/--
theorem `image_rev` / 定理 `image_rev`

English:
theorem image_rev
  given: (s : Set (Fin n))
  statement: rev '' s = rev ⁻¹' s
  proof: revPerm.image_eq_preimage_symm s

@[simp]

中文:
定理 image_rev
  条件: (s : Set (Fin n))
  结论: rev '' s = rev ⁻¹' s
  证明: revPerm.image_eq_preimage_symm s

@[simp]

Depends on / 依赖: image_eq_preimage_symm, revPerm, revPerm.image_eq_preimage_symm
-/
theorem image_rev (s : Set (Fin n)) : rev '' s = rev ⁻¹' s := revPerm.image_eq_preimage_symm s

@[simp]
/--
theorem `image_rev_fun` / 定理 `image_rev_fun`

English:
theorem image_rev_fun
  statement: image (@rev n) = preimage rev
  proof: funext image_rev

@[simp]

中文:
定理 image_rev_fun
  结论: image (@rev n) = preimage rev
  证明: funext image_rev

@[simp]

Depends on / 依赖: image_rev
-/
theorem image_rev_fun : image (@rev n) = preimage rev := funext image_rev

@[simp]
/--
theorem `preimage_rev_Ici` / 定理 `preimage_rev_Ici`

English:
theorem preimage_rev_Ici
  given: (i : Fin n)
  statement: rev ⁻¹' Ici i = Iic i.rev
  proof: by ext; simp [le_rev_iff]

@[simp]

中文:
定理 preimage_rev_Ici
  条件: (i : Fin n)
  结论: rev ⁻¹' Ici i = Iic i.rev
  证明: by ext; simp [le_rev_iff]

@[simp]

Depends on / 依赖: le_rev_iff
-/
theorem preimage_rev_Ici (i : Fin n) : rev ⁻¹' Ici i = Iic i.rev := by ext; simp [le_rev_iff]

@[simp]
/--
theorem `preimage_rev_Ioi` / 定理 `preimage_rev_Ioi`

English:
theorem preimage_rev_Ioi
  given: (i : Fin n)
  statement: rev ⁻¹' Ioi i = Iio i.rev
  proof: by ext; simp [lt_rev_iff]

@[simp]

中文:
定理 preimage_rev_Ioi
  条件: (i : Fin n)
  结论: rev ⁻¹' Ioi i = Iio i.rev
  证明: by ext; simp [lt_rev_iff]

@[simp]

Depends on / 依赖: lt_rev_iff
-/
theorem preimage_rev_Ioi (i : Fin n) : rev ⁻¹' Ioi i = Iio i.rev := by ext; simp [lt_rev_iff]

@[simp]
/--
theorem `preimage_rev_Iic` / 定理 `preimage_rev_Iic`

English:
theorem preimage_rev_Iic
  given: (i : Fin n)
  statement: rev ⁻¹' Iic i = Ici i.rev
  proof: by ext; simp [rev_le_iff]

@[simp]

中文:
定理 preimage_rev_Iic
  条件: (i : Fin n)
  结论: rev ⁻¹' Iic i = Ici i.rev
  证明: by ext; simp [rev_le_iff]

@[simp]

Depends on / 依赖: rev_le_iff
-/
theorem preimage_rev_Iic (i : Fin n) : rev ⁻¹' Iic i = Ici i.rev := by ext; simp [rev_le_iff]

@[simp]
/--
theorem `preimage_rev_Iio` / 定理 `preimage_rev_Iio`

English:
theorem preimage_rev_Iio
  given: (i : Fin n)
  statement: rev ⁻¹' Iio i = Ioi i.rev
  proof: by ext; simp [rev_lt_iff]

@[simp]

中文:
定理 preimage_rev_Iio
  条件: (i : Fin n)
  结论: rev ⁻¹' Iio i = Ioi i.rev
  证明: by ext; simp [rev_lt_iff]

@[simp]

Depends on / 依赖: rev_lt_iff
-/
theorem preimage_rev_Iio (i : Fin n) : rev ⁻¹' Iio i = Ioi i.rev := by ext; simp [rev_lt_iff]

@[simp]
/--
theorem `preimage_rev_Icc` / 定理 `preimage_rev_Icc`

English:
theorem preimage_rev_Icc
  given: (i j : Fin n)
  statement: rev ⁻¹' Icc i j = Icc j.rev i.rev
  proof: by
  ext; simp [le_rev_iff, rev_le_iff, and_comm]

@[simp]

中文:
定理 preimage_rev_Icc
  条件: (i j : Fin n)
  结论: rev ⁻¹' Icc i j = Icc j.rev i.rev
  证明: by
  ext; simp [le_rev_iff, rev_le_iff, and_comm]

@[simp]

Depends on / 依赖: and_comm, le_rev_iff, rev_le_iff
-/
theorem preimage_rev_Icc (i j : Fin n) : rev ⁻¹' Icc i j = Icc j.rev i.rev := by
  ext; simp [le_rev_iff, rev_le_iff, and_comm]

@[simp]
/--
theorem `preimage_rev_Ico` / 定理 `preimage_rev_Ico`

English:
theorem preimage_rev_Ico
  given: (i j : Fin n)
  statement: rev ⁻¹' Ico i j = Ioc j.rev i.rev
  proof: by
  ext; simp [le_rev_iff, rev_lt_iff, and_comm]

@[simp]

中文:
定理 preimage_rev_Ico
  条件: (i j : Fin n)
  结论: rev ⁻¹' Ico i j = Ioc j.rev i.rev
  证明: by
  ext; simp [le_rev_iff, rev_lt_iff, and_comm]

@[simp]

Depends on / 依赖: and_comm, le_rev_iff, rev_lt_iff
-/
theorem preimage_rev_Ico (i j : Fin n) : rev ⁻¹' Ico i j = Ioc j.rev i.rev := by
  ext; simp [le_rev_iff, rev_lt_iff, and_comm]

@[simp]
/--
theorem `preimage_rev_Ioc` / 定理 `preimage_rev_Ioc`

English:
theorem preimage_rev_Ioc
  given: (i j : Fin n)
  statement: rev ⁻¹' Ioc i j = Ico j.rev i.rev
  proof: by
  ext; simp [lt_rev_iff, rev_le_iff, and_comm]

@[simp]

中文:
定理 preimage_rev_Ioc
  条件: (i j : Fin n)
  结论: rev ⁻¹' Ioc i j = Ico j.rev i.rev
  证明: by
  ext; simp [lt_rev_iff, rev_le_iff, and_comm]

@[simp]

Depends on / 依赖: and_comm, lt_rev_iff, rev_le_iff
-/
theorem preimage_rev_Ioc (i j : Fin n) : rev ⁻¹' Ioc i j = Ico j.rev i.rev := by
  ext; simp [lt_rev_iff, rev_le_iff, and_comm]

@[simp]
/--
theorem `preimage_rev_Ioo` / 定理 `preimage_rev_Ioo`

English:
theorem preimage_rev_Ioo
  given: (i j : Fin n)
  statement: rev ⁻¹' Ioo i j = Ioo j.rev i.rev
  proof: by
  ext; simp [lt_rev_iff, rev_lt_iff, and_comm]

@[simp]

中文:
定理 preimage_rev_Ioo
  条件: (i j : Fin n)
  结论: rev ⁻¹' Ioo i j = Ioo j.rev i.rev
  证明: by
  ext; simp [lt_rev_iff, rev_lt_iff, and_comm]

@[simp]

Depends on / 依赖: and_comm, lt_rev_iff, rev_lt_iff
-/
theorem preimage_rev_Ioo (i j : Fin n) : rev ⁻¹' Ioo i j = Ioo j.rev i.rev := by
  ext; simp [lt_rev_iff, rev_lt_iff, and_comm]

@[simp]
/--
theorem `preimage_rev_uIcc` / 定理 `preimage_rev_uIcc`

English:
theorem preimage_rev_uIcc
  given: (i j : Fin n)
  statement: rev ⁻¹' uIcc i j = uIcc i.rev j.rev
  proof: by
  simp [uIcc, ← rev_anti.map_min, ← rev_anti.map_max]

@[simp]

中文:
定理 preimage_rev_uIcc
  条件: (i j : Fin n)
  结论: rev ⁻¹' uIcc i j = uIcc i.rev j.rev
  证明: by
  simp [uIcc, ← rev_anti.map_min, ← rev_anti.map_max]

@[simp]

Depends on / 依赖: map_max, map_min, rev_anti, rev_anti.map_max, rev_anti.map_min
-/
theorem preimage_rev_uIcc (i j : Fin n) : rev ⁻¹' uIcc i j = uIcc i.rev j.rev := by
  simp [uIcc, ← rev_anti.map_min, ← rev_anti.map_max]

@[simp]
/--
theorem `preimage_rev_uIoo` / 定理 `preimage_rev_uIoo`

English:
theorem preimage_rev_uIoo
  given: (i j : Fin n)
  statement: rev ⁻¹' uIoo i j = uIoo i.rev j.rev
  proof: by
  simp [uIoo, ← rev_anti.map_min, ← rev_anti.map_max]

中文:
定理 preimage_rev_uIoo
  条件: (i j : Fin n)
  结论: rev ⁻¹' uIoo i j = uIoo i.rev j.rev
  证明: by
  simp [uIoo, ← rev_anti.map_min, ← rev_anti.map_max]

Depends on / 依赖: map_max, map_min, rev_anti, rev_anti.map_max, rev_anti.map_min
-/
theorem preimage_rev_uIoo (i j : Fin n) : rev ⁻¹' uIoo i j = uIoo i.rev j.rev := by
  simp [uIoo, ← rev_anti.map_min, ← rev_anti.map_max]

end Fin
