/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Basic

/-!
# Set neighborhoods of intervals

In this file we prove basic theorems about `𝓝ˢ s`,
where `s` is one of the intervals
`Set.Ici`, `Set.Iic`, `Set.Ioi`, `Set.Iio`, `Set.Ico`, `Set.Ioc`, `Set.Ioo`, and `Set.Icc`.

First, we prove lemmas in terms of filter equalities.
Then we prove lemmas about `s ∈ 𝓝ˢ t`, where both `s` and `t` are intervals.
Finally, we prove a few lemmas about filter bases of `𝓝ˢ (Iic a)` and `𝓝ˢ (Ici a)`.
-/

public section


open Set Filter OrderDual
open scoped Topology

section OrderClosedTopology

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] {a b c d : α}


/--
theorem `nhdsSet_Ioi` / 定理 `nhdsSet_Ioi`

English:
theorem nhdsSet_Ioi
  statement: 𝓝ˢ (Ioi a) = 𝓟 (Ioi a)
  proof: isOpen_Ioi.nhdsSet_eq

中文:
定理 nhdsSet_Ioi
  结论: 𝓝ˢ (左开右无界区间 a) = 𝓟 (左开右无界区间 a)
  证明: isOpen_Ioi.nhdsSet_eq
-/
@[simp] theorem nhdsSet_Ioi : 𝓝ˢ (Ioi a) = 𝓟 (Ioi a) := isOpen_Ioi.nhdsSet_eq
/--
theorem `nhdsSet_Iio` / 定理 `nhdsSet_Iio`

English:
theorem nhdsSet_Iio
  statement: 𝓝ˢ (Iio a) = 𝓟 (Iio a)
  proof: isOpen_Iio.nhdsSet_eq

中文:
定理 nhdsSet_Iio
  结论: 𝓝ˢ (左无界右开区间 a) = 𝓟 (左无界右开区间 a)
  证明: isOpen_Iio.nhdsSet_eq
-/
@[simp] theorem nhdsSet_Iio : 𝓝ˢ (Iio a) = 𝓟 (Iio a) := isOpen_Iio.nhdsSet_eq
/--
theorem `nhdsSet_Ioo` / 定理 `nhdsSet_Ioo`

English:
theorem nhdsSet_Ioo
  statement: 𝓝ˢ (Ioo a b) = 𝓟 (Ioo a b)
  proof: isOpen_Ioo.nhdsSet_eq

中文:
定理 nhdsSet_Ioo
  结论: 𝓝ˢ (开区间 a b) = 𝓟 (开区间 a b)
  证明: isOpen_Ioo.nhdsSet_eq
-/
@[simp] theorem nhdsSet_Ioo : 𝓝ˢ (Ioo a b) = 𝓟 (Ioo a b) := isOpen_Ioo.nhdsSet_eq

/--
theorem `nhdsSet_Ici` / 定理 `nhdsSet_Ici`

English:
theorem nhdsSet_Ici
  statement: 𝓝ˢ (Ici a) = 𝓝 a ⊔ 𝓟 (Ioi a)
  proof: by
  rw [← Ioi_insert]; rw [nhdsSet_insert]; rw [nhdsSet_Ioi]

中文:
定理 nhdsSet_Ici
  结论: 𝓝ˢ (左闭右无界区间 a) = 𝓝 a ⊔ 𝓟 (左开右无界区间 a)
  证明: by
  rw [← Ioi_insert]; rw [nhdsSet_insert]; rw [nhdsSet_Ioi]

Depends on / 依赖: Ioi_insert, nhdsSet_Ioi, nhdsSet_insert
-/
theorem nhdsSet_Ici : 𝓝ˢ (Ici a) = 𝓝 a ⊔ 𝓟 (Ioi a) := by
  rw [← Ioi_insert]; rw [nhdsSet_insert]; rw [nhdsSet_Ioi]

/--
theorem `nhdsSet_Iic` / 定理 `nhdsSet_Iic`

English:
theorem nhdsSet_Iic
  statement: 𝓝ˢ (Iic a) = 𝓝 a ⊔ 𝓟 (Iio a)
  proof: nhdsSet_Ici (α := αᵒᵈ)

中文:
定理 nhdsSet_Iic
  结论: 𝓝ˢ (左无界右闭区间 a) = 𝓝 a ⊔ 𝓟 (左无界右开区间 a)
  证明: nhdsSet_Ici (α := αᵒᵈ)

Depends on / 依赖: nhdsSet_Ici
-/
theorem nhdsSet_Iic : 𝓝ˢ (Iic a) = 𝓝 a ⊔ 𝓟 (Iio a) := nhdsSet_Ici (α := αᵒᵈ)

/--
theorem `nhdsSet_Ico` / 定理 `nhdsSet_Ico`

English:
theorem nhdsSet_Ico
  given: (h : a < b)
  statement: 𝓝ˢ (Ico a b) = 𝓝 a ⊔ 𝓟 (Ioo a b)
  proof: by
  rw [← Ioo_insert_left h]; rw [nhdsSet_insert]; rw [nhdsSet_Ioo]

中文:
定理 nhdsSet_Ico
  条件: (h : a < b)
  结论: 𝓝ˢ (左闭右开区间 a b) = 𝓝 a ⊔ 𝓟 (开区间 a b)
  证明: by
  rw [← Ioo_insert_left h]; rw [nhdsSet_insert]; rw [nhdsSet_Ioo]

Depends on / 依赖: Ioo_insert_left, nhdsSet_Ioo, nhdsSet_insert
-/
theorem nhdsSet_Ico (h : a < b) : 𝓝ˢ (Ico a b) = 𝓝 a ⊔ 𝓟 (Ioo a b) := by
  rw [← Ioo_insert_left h]; rw [nhdsSet_insert]; rw [nhdsSet_Ioo]

/--
theorem `nhdsSet_Ioc` / 定理 `nhdsSet_Ioc`

English:
theorem nhdsSet_Ioc
  given: (h : a < b)
  statement: 𝓝ˢ (Ioc a b) = 𝓝 b ⊔ 𝓟 (Ioo a b)
  proof: by
  rw [← Ioo_insert_right h]; rw [nhdsSet_insert]; rw [nhdsSet_Ioo]

中文:
定理 nhdsSet_Ioc
  条件: (h : a < b)
  结论: 𝓝ˢ (左开右闭区间 a b) = 𝓝 b ⊔ 𝓟 (开区间 a b)
  证明: by
  rw [← Ioo_insert_right h]; rw [nhdsSet_insert]; rw [nhdsSet_Ioo]

Depends on / 依赖: Ioo_insert_right, nhdsSet_Ioo, nhdsSet_insert
-/
theorem nhdsSet_Ioc (h : a < b) : 𝓝ˢ (Ioc a b) = 𝓝 b ⊔ 𝓟 (Ioo a b) := by
  rw [← Ioo_insert_right h]; rw [nhdsSet_insert]; rw [nhdsSet_Ioo]

/--
theorem `nhdsSet_Icc` / 定理 `nhdsSet_Icc`

English:
theorem nhdsSet_Icc
  given: (h : a <= b)
  statement: 𝓝ˢ (Icc a b) = 𝓝 a ⊔ 𝓝 b ⊔ 𝓟 (Ioo a b)
  proof: by
  rcases h.eq_or_lt with rfl | hlt
  · simp
  · rw [← Ioc_insert_left h, nhdsSet_insert, nhdsSet_Ioc hlt, sup_assoc]

中文:
定理 nhdsSet_Icc
  条件: (h : a <= b)
  结论: 𝓝ˢ (闭区间 a b) = 𝓝 a ⊔ 𝓝 b ⊔ 𝓟 (开区间 a b)
  证明: by
  rcases h.eq_or_lt with rfl | hlt
  · simp
  · rw [← Ioc_insert_left h, nhdsSet_insert, nhdsSet_Ioc hlt, sup_assoc]

Depends on / 依赖: Ioc_insert_left, eq_or_lt, h.eq_or_lt, nhdsSet_Ioc, nhdsSet_insert, sup_assoc
-/
theorem nhdsSet_Icc (h : a <= b) : 𝓝ˢ (Icc a b) = 𝓝 a ⊔ 𝓝 b ⊔ 𝓟 (Ioo a b) := by
  rcases h.eq_or_lt with rfl | hlt
  · simp
  · rw [← Ioc_insert_left h, nhdsSet_insert, nhdsSet_Ioc hlt, sup_assoc]

/-!
### Lemmas about `Ixi _ ∈ 𝓝ˢ (Set.Ici _)`
-/

@[simp]
/--
theorem `Ioi_mem_nhdsSet_Ici_iff` / 定理 `Ioi_mem_nhdsSet_Ici_iff`

English:
theorem Ioi_mem_nhdsSet_Ici_iff
  statement: Ioi a in 𝓝ˢ (Ici b) ↔ a < b
  proof: by
  rw [isOpen_Ioi.mem_nhdsSet]; rw [Ici_subset_Ioi]

alias ⟨_, Ioi_mem_nhdsSet_Ici⟩ := Ioi_mem_nhdsSet_Ici_iff

中文:
定理 Ioi_mem_nhdsSet_Ici_iff
  结论: 左开右无界区间 a in 𝓝ˢ (左闭右无界区间 b) ↔ a < b
  证明: by
  rw [isOpen_Ioi.mem_nhdsSet]; rw [Ici_subset_Ioi]

alias ⟨_, Ioi_mem_nhdsSet_Ici⟩ := Ioi_mem_nhdsSet_Ici_iff

Depends on / 依赖: Ici_subset_Ioi, isOpen_Ioi, isOpen_Ioi.mem_nhdsSet, mem_nhdsSet
-/
theorem Ioi_mem_nhdsSet_Ici_iff : Ioi a in 𝓝ˢ (Ici b) ↔ a < b := by
  rw [isOpen_Ioi.mem_nhdsSet]; rw [Ici_subset_Ioi]

alias ⟨_, Ioi_mem_nhdsSet_Ici⟩ := Ioi_mem_nhdsSet_Ici_iff

/--
theorem `Ici_mem_nhdsSet_Ici` / 定理 `Ici_mem_nhdsSet_Ici`

English:
theorem Ici_mem_nhdsSet_Ici
  given: (h : a < b)
  statement: Ici a in 𝓝ˢ (Ici b)
  proof: mem_of_superset (Ioi_mem_nhdsSet_Ici h) Ioi_subset_Ici_self

中文:
定理 Ici_mem_nhdsSet_Ici
  条件: (h : a < b)
  结论: 左闭右无界区间 a in 𝓝ˢ (左闭右无界区间 b)
  证明: mem_of_superset (Ioi_mem_nhdsSet_Ici h) Ioi_subset_Ici_self

Depends on / 依赖: Ioi_mem_nhdsSet_Ici, Ioi_subset_Ici_self, mem_of_superset
-/
theorem Ici_mem_nhdsSet_Ici (h : a < b) : Ici a in 𝓝ˢ (Ici b) :=
  mem_of_superset (Ioi_mem_nhdsSet_Ici h) Ioi_subset_Ici_self


/--
theorem `Iio_mem_nhdsSet_Iic_iff` / 定理 `Iio_mem_nhdsSet_Iic_iff`

English:
theorem Iio_mem_nhdsSet_Iic_iff
  statement: Iio b in 𝓝ˢ (Iic a) ↔ a < b
  proof: Ioi_mem_nhdsSet_Ici_iff (α := αᵒᵈ)

alias ⟨_, Iio_mem_nhdsSet_Iic⟩ := Iio_mem_nhdsSet_Iic_iff

中文:
定理 Iio_mem_nhdsSet_Iic_iff
  结论: 左无界右开区间 b in 𝓝ˢ (左无界右闭区间 a) ↔ a < b
  证明: Ioi_mem_nhdsSet_Ici_iff (α := αᵒᵈ)

alias ⟨_, Iio_mem_nhdsSet_Iic⟩ := Iio_mem_nhdsSet_Iic_iff

Depends on / 依赖: Ioi_mem_nhdsSet_Ici_iff
-/
theorem Iio_mem_nhdsSet_Iic_iff : Iio b in 𝓝ˢ (Iic a) ↔ a < b :=
  Ioi_mem_nhdsSet_Ici_iff (α := αᵒᵈ)

alias ⟨_, Iio_mem_nhdsSet_Iic⟩ := Iio_mem_nhdsSet_Iic_iff

/--
theorem `Iic_mem_nhdsSet_Iic` / 定理 `Iic_mem_nhdsSet_Iic`

English:
theorem Iic_mem_nhdsSet_Iic
  given: (h : a < b)
  statement: Iic b in 𝓝ˢ (Iic a)
  proof: Ici_mem_nhdsSet_Ici (α := αᵒᵈ) h

中文:
定理 Iic_mem_nhdsSet_Iic
  条件: (h : a < b)
  结论: 左无界右闭区间 b in 𝓝ˢ (左无界右闭区间 a)
  证明: Ici_mem_nhdsSet_Ici (α := αᵒᵈ) h

Depends on / 依赖: Ici_mem_nhdsSet_Ici
-/
theorem Iic_mem_nhdsSet_Iic (h : a < b) : Iic b in 𝓝ˢ (Iic a) :=
  Ici_mem_nhdsSet_Ici (α := αᵒᵈ) h


/--
theorem `Ioi_mem_nhdsSet_Icc` / 定理 `Ioi_mem_nhdsSet_Icc`

English:
theorem Ioi_mem_nhdsSet_Icc
  given: (h : a < b)
  statement: Ioi a in 𝓝ˢ (Icc b c)
  proof: nhdsSet_mono Icc_subset_Ici_self Ioi_mem_nhdsSet_Ici h

中文:
定理 Ioi_mem_nhdsSet_Icc
  条件: (h : a < b)
  结论: 左开右无界区间 a in 𝓝ˢ (闭区间 b c)
  证明: nhdsSet_mono Icc_subset_Ici_self Ioi_mem_nhdsSet_Ici h

Depends on / 依赖: Icc_subset_Ici_self, Ioi_mem_nhdsSet_Ici, nhdsSet_mono
-/
theorem Ioi_mem_nhdsSet_Icc (h : a < b) : Ioi a in 𝓝ˢ (Icc b c) :=
nhdsSet_mono Icc_subset_Ici_self Ioi_mem_nhdsSet_Ici h

/--
theorem `Ici_mem_nhdsSet_Icc` / 定理 `Ici_mem_nhdsSet_Icc`

English:
theorem Ici_mem_nhdsSet_Icc
  given: (h : a < b)
  statement: Ici a in 𝓝ˢ (Icc b c)
  proof: mem_of_superset (Ioi_mem_nhdsSet_Icc h) Ioi_subset_Ici_self

中文:
定理 Ici_mem_nhdsSet_Icc
  条件: (h : a < b)
  结论: 左闭右无界区间 a in 𝓝ˢ (闭区间 b c)
  证明: mem_of_superset (Ioi_mem_nhdsSet_Icc h) Ioi_subset_Ici_self

Depends on / 依赖: Ioi_mem_nhdsSet_Icc, Ioi_subset_Ici_self, mem_of_superset
-/
theorem Ici_mem_nhdsSet_Icc (h : a < b) : Ici a in 𝓝ˢ (Icc b c) :=
  mem_of_superset (Ioi_mem_nhdsSet_Icc h) Ioi_subset_Ici_self

/--
theorem `Iio_mem_nhdsSet_Icc` / 定理 `Iio_mem_nhdsSet_Icc`

English:
theorem Iio_mem_nhdsSet_Icc
  given: (h : b < c)
  statement: Iio c in 𝓝ˢ (Icc a b)
  proof: nhdsSet_mono Icc_subset_Iic_self Iio_mem_nhdsSet_Iic h

中文:
定理 Iio_mem_nhdsSet_Icc
  条件: (h : b < c)
  结论: 左无界右开区间 c in 𝓝ˢ (闭区间 a b)
  证明: nhdsSet_mono Icc_subset_Iic_self Iio_mem_nhdsSet_Iic h

Depends on / 依赖: Icc_subset_Iic_self, Iio_mem_nhdsSet_Iic, nhdsSet_mono
-/
theorem Iio_mem_nhdsSet_Icc (h : b < c) : Iio c in 𝓝ˢ (Icc a b) :=
nhdsSet_mono Icc_subset_Iic_self Iio_mem_nhdsSet_Iic h

/--
theorem `Iic_mem_nhdsSet_Icc` / 定理 `Iic_mem_nhdsSet_Icc`

English:
theorem Iic_mem_nhdsSet_Icc
  given: (h : b < c)
  statement: Iic c in 𝓝ˢ (Icc a b)
  proof: mem_of_superset (Iio_mem_nhdsSet_Icc h) Iio_subset_Iic_self

中文:
定理 Iic_mem_nhdsSet_Icc
  条件: (h : b < c)
  结论: 左无界右闭区间 c in 𝓝ˢ (闭区间 a b)
  证明: mem_of_superset (Iio_mem_nhdsSet_Icc h) Iio_subset_Iic_self

Depends on / 依赖: Iio_mem_nhdsSet_Icc, Iio_subset_Iic_self, mem_of_superset
-/
theorem Iic_mem_nhdsSet_Icc (h : b < c) : Iic c in 𝓝ˢ (Icc a b) :=
  mem_of_superset (Iio_mem_nhdsSet_Icc h) Iio_subset_Iic_self

/--
theorem `Ioo_mem_nhdsSet_Icc` / 定理 `Ioo_mem_nhdsSet_Icc`

English:
theorem Ioo_mem_nhdsSet_Icc
  given: (h : a < b) (h' : c < d)
  statement: Ioo a d in 𝓝ˢ (Icc b c)
  proof: inter_mem (Ioi_mem_nhdsSet_Icc h) (Iio_mem_nhdsSet_Icc h')

中文:
定理 Ioo_mem_nhdsSet_Icc
  条件: (h : a < b) (h' : c < d)
  结论: 开区间 a d in 𝓝ˢ (闭区间 b c)
  证明: inter_mem (Ioi_mem_nhdsSet_Icc h) (Iio_mem_nhdsSet_Icc h')

Depends on / 依赖: Iio_mem_nhdsSet_Icc, Ioi_mem_nhdsSet_Icc, inter_mem
-/
theorem Ioo_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Ioo a d in 𝓝ˢ (Icc b c) :=
  inter_mem (Ioi_mem_nhdsSet_Icc h) (Iio_mem_nhdsSet_Icc h')

/--
theorem `Ico_mem_nhdsSet_Icc` / 定理 `Ico_mem_nhdsSet_Icc`

English:
theorem Ico_mem_nhdsSet_Icc
  given: (h : a < b) (h' : c < d)
  statement: Ico a d in 𝓝ˢ (Icc b c)
  proof: inter_mem (Ici_mem_nhdsSet_Icc h) (Iio_mem_nhdsSet_Icc h')

中文:
定理 Ico_mem_nhdsSet_Icc
  条件: (h : a < b) (h' : c < d)
  结论: 左闭右开区间 a d in 𝓝ˢ (闭区间 b c)
  证明: inter_mem (Ici_mem_nhdsSet_Icc h) (Iio_mem_nhdsSet_Icc h')

Depends on / 依赖: Ici_mem_nhdsSet_Icc, Iio_mem_nhdsSet_Icc, inter_mem
-/
theorem Ico_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Ico a d in 𝓝ˢ (Icc b c) :=
  inter_mem (Ici_mem_nhdsSet_Icc h) (Iio_mem_nhdsSet_Icc h')

/--
theorem `Ioc_mem_nhdsSet_Icc` / 定理 `Ioc_mem_nhdsSet_Icc`

English:
theorem Ioc_mem_nhdsSet_Icc
  given: (h : a < b) (h' : c < d)
  statement: Ioc a d in 𝓝ˢ (Icc b c)
  proof: inter_mem (Ioi_mem_nhdsSet_Icc h) (Iic_mem_nhdsSet_Icc h')

中文:
定理 Ioc_mem_nhdsSet_Icc
  条件: (h : a < b) (h' : c < d)
  结论: 左开右闭区间 a d in 𝓝ˢ (闭区间 b c)
  证明: inter_mem (Ioi_mem_nhdsSet_Icc h) (Iic_mem_nhdsSet_Icc h')

Depends on / 依赖: Iic_mem_nhdsSet_Icc, Ioi_mem_nhdsSet_Icc, inter_mem
-/
theorem Ioc_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Ioc a d in 𝓝ˢ (Icc b c) :=
  inter_mem (Ioi_mem_nhdsSet_Icc h) (Iic_mem_nhdsSet_Icc h')

/--
theorem `Icc_mem_nhdsSet_Icc` / 定理 `Icc_mem_nhdsSet_Icc`

English:
theorem Icc_mem_nhdsSet_Icc
  given: (h : a < b) (h' : c < d)
  statement: Icc a d in 𝓝ˢ (Icc b c)
  proof: inter_mem (Ici_mem_nhdsSet_Icc h) (Iic_mem_nhdsSet_Icc h')

中文:
定理 Icc_mem_nhdsSet_Icc
  条件: (h : a < b) (h' : c < d)
  结论: 闭区间 a d in 𝓝ˢ (闭区间 b c)
  证明: inter_mem (Ici_mem_nhdsSet_Icc h) (Iic_mem_nhdsSet_Icc h')

Depends on / 依赖: Ici_mem_nhdsSet_Icc, Iic_mem_nhdsSet_Icc, inter_mem
-/
theorem Icc_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Icc a d in 𝓝ˢ (Icc b c) :=
  inter_mem (Ici_mem_nhdsSet_Icc h) (Iic_mem_nhdsSet_Icc h')


/--
theorem `Ici_mem_nhdsSet_Ico` / 定理 `Ici_mem_nhdsSet_Ico`

English:
theorem Ici_mem_nhdsSet_Ico
  given: (h : a < b)
  statement: Ici a in 𝓝ˢ (Ico b c)
  proof: nhdsSet_mono Ico_subset_Icc_self Ici_mem_nhdsSet_Icc h

中文:
定理 Ici_mem_nhdsSet_Ico
  条件: (h : a < b)
  结论: 左闭右无界区间 a in 𝓝ˢ (左闭右开区间 b c)
  证明: nhdsSet_mono Ico_subset_Icc_self Ici_mem_nhdsSet_Icc h

Depends on / 依赖: Ici_mem_nhdsSet_Icc, Ico_subset_Icc_self, nhdsSet_mono
-/
theorem Ici_mem_nhdsSet_Ico (h : a < b) : Ici a in 𝓝ˢ (Ico b c) :=
nhdsSet_mono Ico_subset_Icc_self Ici_mem_nhdsSet_Icc h

/--
theorem `Ioi_mem_nhdsSet_Ico` / 定理 `Ioi_mem_nhdsSet_Ico`

English:
theorem Ioi_mem_nhdsSet_Ico
  given: (h : a < b)
  statement: Ioi a in 𝓝ˢ (Ico b c)
  proof: nhdsSet_mono Ico_subset_Icc_self Ioi_mem_nhdsSet_Icc h

中文:
定理 Ioi_mem_nhdsSet_Ico
  条件: (h : a < b)
  结论: 左开右无界区间 a in 𝓝ˢ (左闭右开区间 b c)
  证明: nhdsSet_mono Ico_subset_Icc_self Ioi_mem_nhdsSet_Icc h

Depends on / 依赖: Ico_subset_Icc_self, Ioi_mem_nhdsSet_Icc, nhdsSet_mono
-/
theorem Ioi_mem_nhdsSet_Ico (h : a < b) : Ioi a in 𝓝ˢ (Ico b c) :=
nhdsSet_mono Ico_subset_Icc_self Ioi_mem_nhdsSet_Icc h

/--
theorem `Iio_mem_nhdsSet_Ico` / 定理 `Iio_mem_nhdsSet_Ico`

English:
theorem Iio_mem_nhdsSet_Ico
  given: (h : b <= c)
  statement: Iio c in 𝓝ˢ (Ico a b)
  proof: nhdsSet_mono Ico_subset_Iio_self by simpa

中文:
定理 Iio_mem_nhdsSet_Ico
  条件: (h : b <= c)
  结论: 左无界右开区间 c in 𝓝ˢ (左闭右开区间 a b)
  证明: nhdsSet_mono Ico_subset_Iio_self by simpa

Depends on / 依赖: Ico_subset_Iio_self, nhdsSet_mono
-/
theorem Iio_mem_nhdsSet_Ico (h : b <= c) : Iio c in 𝓝ˢ (Ico a b) :=
nhdsSet_mono Ico_subset_Iio_self by simpa

/--
theorem `Iic_mem_nhdsSet_Ico` / 定理 `Iic_mem_nhdsSet_Ico`

English:
theorem Iic_mem_nhdsSet_Ico
  given: (h : b <= c)
  statement: Iic c in 𝓝ˢ (Ico a b)
  proof: mem_of_superset (Iio_mem_nhdsSet_Ico h) Iio_subset_Iic_self

中文:
定理 Iic_mem_nhdsSet_Ico
  条件: (h : b <= c)
  结论: 左无界右闭区间 c in 𝓝ˢ (左闭右开区间 a b)
  证明: mem_of_superset (Iio_mem_nhdsSet_Ico h) Iio_subset_Iic_self

Depends on / 依赖: Iio_mem_nhdsSet_Ico, Iio_subset_Iic_self, mem_of_superset
-/
theorem Iic_mem_nhdsSet_Ico (h : b <= c) : Iic c in 𝓝ˢ (Ico a b) :=
  mem_of_superset (Iio_mem_nhdsSet_Ico h) Iio_subset_Iic_self

/--
theorem `Ioo_mem_nhdsSet_Ico` / 定理 `Ioo_mem_nhdsSet_Ico`

English:
theorem Ioo_mem_nhdsSet_Ico
  given: (h : a < b) (h' : c <= d)
  statement: Ioo a d in 𝓝ˢ (Ico b c)
  proof: inter_mem (Ioi_mem_nhdsSet_Ico h) (Iio_mem_nhdsSet_Ico h')

中文:
定理 Ioo_mem_nhdsSet_Ico
  条件: (h : a < b) (h' : c <= d)
  结论: 开区间 a d in 𝓝ˢ (左闭右开区间 b c)
  证明: inter_mem (Ioi_mem_nhdsSet_Ico h) (Iio_mem_nhdsSet_Ico h')

Depends on / 依赖: Iio_mem_nhdsSet_Ico, Ioi_mem_nhdsSet_Ico, inter_mem
-/
theorem Ioo_mem_nhdsSet_Ico (h : a < b) (h' : c <= d) : Ioo a d in 𝓝ˢ (Ico b c) :=
  inter_mem (Ioi_mem_nhdsSet_Ico h) (Iio_mem_nhdsSet_Ico h')

/--
theorem `Icc_mem_nhdsSet_Ico` / 定理 `Icc_mem_nhdsSet_Ico`

English:
theorem Icc_mem_nhdsSet_Ico
  given: (h : a < b) (h' : c <= d)
  statement: Icc a d in 𝓝ˢ (Ico b c)
  proof: inter_mem (Ici_mem_nhdsSet_Ico h) (Iic_mem_nhdsSet_Ico h')

中文:
定理 Icc_mem_nhdsSet_Ico
  条件: (h : a < b) (h' : c <= d)
  结论: 闭区间 a d in 𝓝ˢ (左闭右开区间 b c)
  证明: inter_mem (Ici_mem_nhdsSet_Ico h) (Iic_mem_nhdsSet_Ico h')

Depends on / 依赖: Ici_mem_nhdsSet_Ico, Iic_mem_nhdsSet_Ico, inter_mem
-/
theorem Icc_mem_nhdsSet_Ico (h : a < b) (h' : c <= d) : Icc a d in 𝓝ˢ (Ico b c) :=
  inter_mem (Ici_mem_nhdsSet_Ico h) (Iic_mem_nhdsSet_Ico h')

/--
theorem `Ioc_mem_nhdsSet_Ico` / 定理 `Ioc_mem_nhdsSet_Ico`

English:
theorem Ioc_mem_nhdsSet_Ico
  given: (h : a < b) (h' : c <= d)
  statement: Ioc a d in 𝓝ˢ (Ico b c)
  proof: inter_mem (Ioi_mem_nhdsSet_Ico h) (Iic_mem_nhdsSet_Ico h')

中文:
定理 Ioc_mem_nhdsSet_Ico
  条件: (h : a < b) (h' : c <= d)
  结论: 左开右闭区间 a d in 𝓝ˢ (左闭右开区间 b c)
  证明: inter_mem (Ioi_mem_nhdsSet_Ico h) (Iic_mem_nhdsSet_Ico h')

Depends on / 依赖: Iic_mem_nhdsSet_Ico, Ioi_mem_nhdsSet_Ico, inter_mem
-/
theorem Ioc_mem_nhdsSet_Ico (h : a < b) (h' : c <= d) : Ioc a d in 𝓝ˢ (Ico b c) :=
  inter_mem (Ioi_mem_nhdsSet_Ico h) (Iic_mem_nhdsSet_Ico h')

/--
theorem `Ico_mem_nhdsSet_Ico` / 定理 `Ico_mem_nhdsSet_Ico`

English:
theorem Ico_mem_nhdsSet_Ico
  given: (h : a < b) (h' : c <= d)
  statement: Ico a d in 𝓝ˢ (Ico b c)
  proof: inter_mem (Ici_mem_nhdsSet_Ico h) (Iio_mem_nhdsSet_Ico h')

中文:
定理 Ico_mem_nhdsSet_Ico
  条件: (h : a < b) (h' : c <= d)
  结论: 左闭右开区间 a d in 𝓝ˢ (左闭右开区间 b c)
  证明: inter_mem (Ici_mem_nhdsSet_Ico h) (Iio_mem_nhdsSet_Ico h')

Depends on / 依赖: Ici_mem_nhdsSet_Ico, Iio_mem_nhdsSet_Ico, inter_mem
-/
theorem Ico_mem_nhdsSet_Ico (h : a < b) (h' : c <= d) : Ico a d in 𝓝ˢ (Ico b c) :=
  inter_mem (Ici_mem_nhdsSet_Ico h) (Iio_mem_nhdsSet_Ico h')


/--
theorem `Ioi_mem_nhdsSet_Ioc` / 定理 `Ioi_mem_nhdsSet_Ioc`

English:
theorem Ioi_mem_nhdsSet_Ioc
  given: (h : a <= b)
  statement: Ioi a in 𝓝ˢ (Ioc b c)
  proof: nhdsSet_mono Ioc_subset_Ioi_self by simpa

中文:
定理 Ioi_mem_nhdsSet_Ioc
  条件: (h : a <= b)
  结论: 左开右无界区间 a in 𝓝ˢ (左开右闭区间 b c)
  证明: nhdsSet_mono Ioc_subset_Ioi_self by simpa

Depends on / 依赖: Ioc_subset_Ioi_self, nhdsSet_mono
-/
theorem Ioi_mem_nhdsSet_Ioc (h : a <= b) : Ioi a in 𝓝ˢ (Ioc b c) :=
nhdsSet_mono Ioc_subset_Ioi_self by simpa

/--
theorem `Iio_mem_nhdsSet_Ioc` / 定理 `Iio_mem_nhdsSet_Ioc`

English:
theorem Iio_mem_nhdsSet_Ioc
  given: (h : b < c)
  statement: Iio c in 𝓝ˢ (Ioc a b)
  proof: nhdsSet_mono Ioc_subset_Icc_self Iio_mem_nhdsSet_Icc h

中文:
定理 Iio_mem_nhdsSet_Ioc
  条件: (h : b < c)
  结论: 左无界右开区间 c in 𝓝ˢ (左开右闭区间 a b)
  证明: nhdsSet_mono Ioc_subset_Icc_self Iio_mem_nhdsSet_Icc h

Depends on / 依赖: Iio_mem_nhdsSet_Icc, Ioc_subset_Icc_self, nhdsSet_mono
-/
theorem Iio_mem_nhdsSet_Ioc (h : b < c) : Iio c in 𝓝ˢ (Ioc a b) :=
nhdsSet_mono Ioc_subset_Icc_self Iio_mem_nhdsSet_Icc h

/--
theorem `Ici_mem_nhdsSet_Ioc` / 定理 `Ici_mem_nhdsSet_Ioc`

English:
theorem Ici_mem_nhdsSet_Ioc
  given: (h : a <= b)
  statement: Ici a in 𝓝ˢ (Ioc b c)
  proof: mem_of_superset (Ioi_mem_nhdsSet_Ioc h) Ioi_subset_Ici_self

中文:
定理 Ici_mem_nhdsSet_Ioc
  条件: (h : a <= b)
  结论: 左闭右无界区间 a in 𝓝ˢ (左开右闭区间 b c)
  证明: mem_of_superset (Ioi_mem_nhdsSet_Ioc h) Ioi_subset_Ici_self

Depends on / 依赖: Ioi_mem_nhdsSet_Ioc, Ioi_subset_Ici_self, mem_of_superset
-/
theorem Ici_mem_nhdsSet_Ioc (h : a <= b) : Ici a in 𝓝ˢ (Ioc b c) :=
  mem_of_superset (Ioi_mem_nhdsSet_Ioc h) Ioi_subset_Ici_self

/--
theorem `Iic_mem_nhdsSet_Ioc` / 定理 `Iic_mem_nhdsSet_Ioc`

English:
theorem Iic_mem_nhdsSet_Ioc
  given: (h : b < c)
  statement: Iic c in 𝓝ˢ (Ioc a b)
  proof: nhdsSet_mono Ioc_subset_Icc_self Iic_mem_nhdsSet_Icc h

中文:
定理 Iic_mem_nhdsSet_Ioc
  条件: (h : b < c)
  结论: 左无界右闭区间 c in 𝓝ˢ (左开右闭区间 a b)
  证明: nhdsSet_mono Ioc_subset_Icc_self Iic_mem_nhdsSet_Icc h

Depends on / 依赖: Iic_mem_nhdsSet_Icc, Ioc_subset_Icc_self, nhdsSet_mono
-/
theorem Iic_mem_nhdsSet_Ioc (h : b < c) : Iic c in 𝓝ˢ (Ioc a b) :=
nhdsSet_mono Ioc_subset_Icc_self Iic_mem_nhdsSet_Icc h

/--
theorem `Ioo_mem_nhdsSet_Ioc` / 定理 `Ioo_mem_nhdsSet_Ioc`

English:
theorem Ioo_mem_nhdsSet_Ioc
  given: (h : a <= b) (h' : c < d)
  statement: Ioo a d in 𝓝ˢ (Ioc b c)
  proof: inter_mem (Ioi_mem_nhdsSet_Ioc h) (Iio_mem_nhdsSet_Ioc h')

中文:
定理 Ioo_mem_nhdsSet_Ioc
  条件: (h : a <= b) (h' : c < d)
  结论: 开区间 a d in 𝓝ˢ (左开右闭区间 b c)
  证明: inter_mem (Ioi_mem_nhdsSet_Ioc h) (Iio_mem_nhdsSet_Ioc h')

Depends on / 依赖: Iio_mem_nhdsSet_Ioc, Ioi_mem_nhdsSet_Ioc, inter_mem
-/
theorem Ioo_mem_nhdsSet_Ioc (h : a <= b) (h' : c < d) : Ioo a d in 𝓝ˢ (Ioc b c) :=
  inter_mem (Ioi_mem_nhdsSet_Ioc h) (Iio_mem_nhdsSet_Ioc h')

/--
theorem `Icc_mem_nhdsSet_Ioc` / 定理 `Icc_mem_nhdsSet_Ioc`

English:
theorem Icc_mem_nhdsSet_Ioc
  given: (h : a <= b) (h' : c < d)
  statement: Icc a d in 𝓝ˢ (Ioc b c)
  proof: inter_mem (Ici_mem_nhdsSet_Ioc h) (Iic_mem_nhdsSet_Ioc h')

中文:
定理 Icc_mem_nhdsSet_Ioc
  条件: (h : a <= b) (h' : c < d)
  结论: 闭区间 a d in 𝓝ˢ (左开右闭区间 b c)
  证明: inter_mem (Ici_mem_nhdsSet_Ioc h) (Iic_mem_nhdsSet_Ioc h')

Depends on / 依赖: Ici_mem_nhdsSet_Ioc, Iic_mem_nhdsSet_Ioc, inter_mem
-/
theorem Icc_mem_nhdsSet_Ioc (h : a <= b) (h' : c < d) : Icc a d in 𝓝ˢ (Ioc b c) :=
  inter_mem (Ici_mem_nhdsSet_Ioc h) (Iic_mem_nhdsSet_Ioc h')

/--
theorem `Ioc_mem_nhdsSet_Ioc` / 定理 `Ioc_mem_nhdsSet_Ioc`

English:
theorem Ioc_mem_nhdsSet_Ioc
  given: (h : a <= b) (h' : c < d)
  statement: Ioc a d in 𝓝ˢ (Ioc b c)
  proof: inter_mem (Ioi_mem_nhdsSet_Ioc h) (Iic_mem_nhdsSet_Ioc h')

中文:
定理 Ioc_mem_nhdsSet_Ioc
  条件: (h : a <= b) (h' : c < d)
  结论: 左开右闭区间 a d in 𝓝ˢ (左开右闭区间 b c)
  证明: inter_mem (Ioi_mem_nhdsSet_Ioc h) (Iic_mem_nhdsSet_Ioc h')

Depends on / 依赖: Iic_mem_nhdsSet_Ioc, Ioi_mem_nhdsSet_Ioc, inter_mem
-/
theorem Ioc_mem_nhdsSet_Ioc (h : a <= b) (h' : c < d) : Ioc a d in 𝓝ˢ (Ioc b c) :=
  inter_mem (Ioi_mem_nhdsSet_Ioc h) (Iic_mem_nhdsSet_Ioc h')

/--
theorem `Ico_mem_nhdsSet_Ioc` / 定理 `Ico_mem_nhdsSet_Ioc`

English:
theorem Ico_mem_nhdsSet_Ioc
  given: (h : a <= b) (h' : c < d)
  statement: Ico a d in 𝓝ˢ (Ioc b c)
  proof: inter_mem (Ici_mem_nhdsSet_Ioc h) (Iio_mem_nhdsSet_Ioc h')

中文:
定理 Ico_mem_nhdsSet_Ioc
  条件: (h : a <= b) (h' : c < d)
  结论: 左闭右开区间 a d in 𝓝ˢ (左开右闭区间 b c)
  证明: inter_mem (Ici_mem_nhdsSet_Ioc h) (Iio_mem_nhdsSet_Ioc h')

Depends on / 依赖: Ici_mem_nhdsSet_Ioc, Iio_mem_nhdsSet_Ioc, inter_mem
-/
theorem Ico_mem_nhdsSet_Ioc (h : a <= b) (h' : c < d) : Ico a d in 𝓝ˢ (Ioc b c) :=
  inter_mem (Ici_mem_nhdsSet_Ioc h) (Iio_mem_nhdsSet_Ioc h')

end OrderClosedTopology

/-!
### Filter bases of `𝓝ˢ (Iic a)` and `𝓝ˢ (Ici a)`
-/

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]

/--
theorem `hasBasis_nhdsSet_Iic_Iio` / 定理 `hasBasis_nhdsSet_Iic_Iio`

English:
theorem hasBasis_nhdsSet_Iic_Iio
  given: (a : α) [h : Nonempty (Ioi a)]
  proof: by
  refine ⟨fun s => ⟨fun hs => ?_, fun ⟨b, hab, hb⟩ => mem_of_superset (Iio_mem_nhdsSet_Iic hab) hb⟩⟩
  rw [nhdsSet_Iic]; rw [mem_sup]; rw [mem_principal] at hs
  rcases exists_Ico_subset_of_mem_nhds hs.1 (Set.nonempty_coe_sort.1 h) with ⟨b, hab, hbs⟩
  exact ⟨b, hab, Iio_subset_Iio_union_Ico.tran

中文:
定理 hasBasis_nhdsSet_Iic_Iio
  条件: (a : α) [h : 非空 (左开右无界区间 a)]
  证明: by
  refine ⟨fun s => ⟨fun hs => ?_, fun ⟨b, hab, hb⟩ => mem_of_superset (Iio_mem_nhdsSet_Iic hab) hb⟩⟩
  rw [nhdsSet_Iic]; rw [mem_sup]; rw [mem_principal] at hs
  rcases exists_Ico_subset_of_mem_nhds hs.1 (Set.nonempty_coe_sort.1 h) with ⟨b, hab, hbs⟩
  exact ⟨b, hab, Iio_subset_Iio_union_Ico.tran

Depends on / 依赖: Iio_mem_nhdsSet_Iic, Iio_subset_Iio_union_Ico, Iio_subset_Iio_union_Ico.trans, Set.nonempty_coe_sort, exists_Ico_subset_of_mem_nhds, mem_of_superset, mem_principal, mem_sup, nhdsSet_Iic, nonempty_coe_sort, union_subset
-/
theorem hasBasis_nhdsSet_Iic_Iio (a : α) [h : Nonempty (Ioi a)] :
    HasBasis (𝓝ˢ (Iic a)) (a < ·) Iio := by
  refine ⟨fun s => ⟨fun hs => ?_, fun ⟨b, hab, hb⟩ => mem_of_superset (Iio_mem_nhdsSet_Iic hab) hb⟩⟩
  rw [nhdsSet_Iic]; rw [mem_sup]; rw [mem_principal] at hs
  rcases exists_Ico_subset_of_mem_nhds hs.1 (Set.nonempty_coe_sort.1 h) with ⟨b, hab, hbs⟩
  exact ⟨b, hab, Iio_subset_Iio_union_Ico.trans (union_subset hs.2 hbs)⟩

/--
theorem `hasBasis_nhdsSet_Iic_Iic` / 定理 `hasBasis_nhdsSet_Iic_Iic`

English:
theorem hasBasis_nhdsSet_Iic_Iic
  given: (a : α) [NeBot (𝓝[>] a)]
  proof: by
  have : Nonempty (Ioi a) :=
    (Filter.nonempty_of_mem (self_mem_nhdsWithin : Ioi a in 𝓝[>] a)).to_subtype
  refine (hasBasis_nhdsSet_Iic_Iio _).to_hasBasis
    (fun c hc => ?_) (fun _ h => ⟨_, h, Iio_subset_Iic_self⟩)
  simpa only [Iic_subset_Iio] using! Filter.nonempty_of_mem (Ioo_mem_nhdsGT 

中文:
定理 hasBasis_nhdsSet_Iic_Iic
  条件: (a : α) [NeBot (𝓝[>] a)]
  证明: by
  have : Nonempty (Ioi a) :=
    (Filter.nonempty_of_mem (self_mem_nhdsWithin : Ioi a in 𝓝[>] a)).to_subtype
  refine (hasBasis_nhdsSet_Iic_Iio _).to_hasBasis
    (fun c hc => ?_) (fun _ h => ⟨_, h, Iio_subset_Iic_self⟩)
  simpa only [Iic_subset_Iio] using! Filter.nonempty_of_mem (Ioo_mem_nhdsGT 

Depends on / 依赖: Filter, Filter.nonempty_of_mem, Iic_subset_Iio, Iio_subset_Iic_self, Ioo_mem_nhdsGT, Nonempty, hasBasis_nhdsSet_Iic_Iio, nonempty_of_mem, self_mem_nhdsWithin, to_hasBasis, to_subtype
-/
theorem hasBasis_nhdsSet_Iic_Iic (a : α) [NeBot (𝓝[>] a)] :
    HasBasis (𝓝ˢ (Iic a)) (a < ·) Iic := by
  have : Nonempty (Ioi a) :=
    (Filter.nonempty_of_mem (self_mem_nhdsWithin : Ioi a in 𝓝[>] a)).to_subtype
  refine (hasBasis_nhdsSet_Iic_Iio _).to_hasBasis
    (fun c hc => ?_) (fun _ h => ⟨_, h, Iio_subset_Iic_self⟩)
  simpa only [Iic_subset_Iio] using! Filter.nonempty_of_mem (Ioo_mem_nhdsGT hc)

@[simp]
/--
theorem `Iic_mem_nhdsSet_Iic_iff` / 定理 `Iic_mem_nhdsSet_Iic_iff`

English:
theorem Iic_mem_nhdsSet_Iic_iff
  given: {a b : α} [NeBot (𝓝[>] b)]
  statement: Iic a in 𝓝ˢ (Iic b) ↔ b < a
  proof: (hasBasis_nhdsSet_Iic_Iic b).mem_iff.trans
    ⟨fun ⟨_c, hbc, hca⟩ => hbc.trans_le (Iic_subset_Iic.1 hca), fun h => ⟨_, h, Subset.rfl⟩⟩

中文:
定理 Iic_mem_nhdsSet_Iic_iff
  条件: {a b : α} [NeBot (𝓝[>] b)]
  结论: 左无界右闭区间 a in 𝓝ˢ (左无界右闭区间 b) ↔ b < a
  证明: (hasBasis_nhdsSet_Iic_Iic b).mem_iff.trans
    ⟨fun ⟨_c, hbc, hca⟩ => hbc.trans_le (Iic_subset_Iic.1 hca), fun h => ⟨_, h, Subset.rfl⟩⟩

Depends on / 依赖: Iic_subset_Iic, Subset, Subset.rfl, hasBasis_nhdsSet_Iic_Iic, hbc.trans_le, mem_iff, mem_iff.trans, trans_le
-/
theorem Iic_mem_nhdsSet_Iic_iff {a b : α} [NeBot (𝓝[>] b)] : Iic a in 𝓝ˢ (Iic b) ↔ b < a :=
  (hasBasis_nhdsSet_Iic_Iic b).mem_iff.trans
    ⟨fun ⟨_c, hbc, hca⟩ => hbc.trans_le (Iic_subset_Iic.1 hca), fun h => ⟨_, h, Subset.rfl⟩⟩

/--
theorem `hasBasis_nhdsSet_Ici_Ioi` / 定理 `hasBasis_nhdsSet_Ici_Ioi`

English:
theorem hasBasis_nhdsSet_Ici_Ioi
  given: (a : α) [Nonempty (Iio a)]
  proof: have : Nonempty (Ioi (toDual a)) := ‹_›; hasBasis_nhdsSet_Iic_Iio (toDual a)

中文:
定理 hasBasis_nhdsSet_Ici_Ioi
  条件: (a : α) [非空 (左无界右开区间 a)]
  证明: have : Nonempty (Ioi (toDual a)) := ‹_›; hasBasis_nhdsSet_Iic_Iio (toDual a)

Depends on / 依赖: Nonempty, hasBasis_nhdsSet_Iic_Iio, toDual
-/
theorem hasBasis_nhdsSet_Ici_Ioi (a : α) [Nonempty (Iio a)] :
    HasBasis (𝓝ˢ (Ici a)) (· < a) Ioi :=
  have : Nonempty (Ioi (toDual a)) := ‹_›; hasBasis_nhdsSet_Iic_Iio (toDual a)

/--
theorem `hasBasis_nhdsSet_Ici_Ici` / 定理 `hasBasis_nhdsSet_Ici_Ici`

English:
theorem hasBasis_nhdsSet_Ici_Ici
  given: (a : α) [NeBot (𝓝[<] a)]
  proof: have : NeBot (𝓝[>] (toDual a)) := ‹_›; hasBasis_nhdsSet_Iic_Iic (toDual a)

@[simp]

中文:
定理 hasBasis_nhdsSet_Ici_Ici
  条件: (a : α) [NeBot (𝓝[<] a)]
  证明: have : NeBot (𝓝[>] (toDual a)) := ‹_›; hasBasis_nhdsSet_Iic_Iic (toDual a)

@[simp]

Depends on / 依赖: hasBasis_nhdsSet_Iic_Iic, toDual
-/
theorem hasBasis_nhdsSet_Ici_Ici (a : α) [NeBot (𝓝[<] a)] :
    HasBasis (𝓝ˢ (Ici a)) (· < a) Ici :=
  have : NeBot (𝓝[>] (toDual a)) := ‹_›; hasBasis_nhdsSet_Iic_Iic (toDual a)

@[simp]
/--
theorem `Ici_mem_nhdsSet_Ici_iff` / 定理 `Ici_mem_nhdsSet_Ici_iff`

English:
theorem Ici_mem_nhdsSet_Ici_iff
  given: {a b : α} [NeBot (𝓝[<] b)]
  statement: Ici a in 𝓝ˢ (Ici b) ↔ a < b
  proof: have : NeBot (𝓝[>] (toDual b)) := ‹_›; Iic_mem_nhdsSet_Iic_iff (a := toDual a) (b := toDual b)

中文:
定理 Ici_mem_nhdsSet_Ici_iff
  条件: {a b : α} [NeBot (𝓝[<] b)]
  结论: 左闭右无界区间 a in 𝓝ˢ (左闭右无界区间 b) ↔ a < b
  证明: have : NeBot (𝓝[>] (toDual b)) := ‹_›; Iic_mem_nhdsSet_Iic_iff (a := toDual a) (b := toDual b)

Depends on / 依赖: Iic_mem_nhdsSet_Iic_iff, toDual
-/
theorem Ici_mem_nhdsSet_Ici_iff {a b : α} [NeBot (𝓝[<] b)] : Ici a in 𝓝ˢ (Ici b) ↔ a < b :=
  have : NeBot (𝓝[>] (toDual b)) := ‹_›; Iic_mem_nhdsSet_Iic_iff (a := toDual a) (b := toDual b)
