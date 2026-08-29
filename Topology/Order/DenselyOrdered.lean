/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.IsLUB

/-!
# Order topology on a densely ordered set
-/

public section

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

section DenselyOrdered

variable [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [DenselyOrdered α] {a b : α}
  {s : Set α}

/--
theorem `closure_Ioi'` / 定理 `closure_Ioi'`

English:
theorem closure_Ioi'
  given: {a : α} (h : (Ioi a).Nonempty)
  statement: closure (Ioi a) = Ici a
  proof: by
  apply Subset.antisymm
  · exact closure_minimal Ioi_subset_Ici_self isClosed_Ici
  · rw [← sdiff_subset_closure_iff, Ici_sdiff_Ioi_same, singleton_subset_iff]
    exact isGLB_Ioi.mem_closure h

中文:
定理 closure_Ioi'
  条件: {a : α} (h : (Ioi a).Nonempty)
  结论: closure (Ioi a) = Ici a
  证明: by
  apply Subset.antisymm
  · exact closure_minimal Ioi_subset_Ici_self isClosed_Ici
  · rw [← sdiff_subset_closure_iff, Ici_sdiff_Ioi_same, singleton_subset_iff]
    exact isGLB_Ioi.mem_closure h

Depends on / 依赖: Ici_sdiff_Ioi_same, Ioi_subset_Ici_self, Subset, Subset.antisymm, antisymm, closure_minimal, isClosed_Ici, isGLB_Ioi, isGLB_Ioi.mem_closure, mem_closure, sdiff_subset_closure_iff, singleton_subset_iff
-/
theorem closure_Ioi' {a : α} (h : (Ioi a).Nonempty) : closure (Ioi a) = Ici a := by
  apply Subset.antisymm
  · exact closure_minimal Ioi_subset_Ici_self isClosed_Ici
  · rw [← sdiff_subset_closure_iff, Ici_sdiff_Ioi_same, singleton_subset_iff]
    exact isGLB_Ioi.mem_closure h

/-- The closure of the interval `(a, +∞)` is the closed interval `[a, +∞)`. -/
@[simp]
/--
theorem `closure_Ioi` / 定理 `closure_Ioi`

English:
theorem closure_Ioi
  given: (a : α) [NoMaxOrder α]
  statement: closure (Ioi a) = Ici a
  proof: closure_Ioi' nonempty_Ioi

中文:
定理 closure_Ioi
  条件: (a : α) [NoMaxOrder α]
  结论: closure (Ioi a) = Ici a
  证明: closure_Ioi' nonempty_Ioi

Depends on / 依赖: closure_Ioi, nonempty_Ioi
-/
theorem closure_Ioi (a : α) [NoMaxOrder α] : closure (Ioi a) = Ici a :=
  closure_Ioi' nonempty_Ioi

/--
theorem `closure_Iio'` / 定理 `closure_Iio'`

English:
theorem closure_Iio'
  given: (h : (Iio a).Nonempty)
  statement: closure (Iio a) = Iic a
  proof: closure_Ioi' (α := αᵒᵈ) h

中文:
定理 closure_Iio'
  条件: (h : (Iio a).Nonempty)
  结论: closure (Iio a) = Iic a
  证明: closure_Ioi' (α := αᵒᵈ) h

Depends on / 依赖: closure_Ioi
-/
theorem closure_Iio' (h : (Iio a).Nonempty) : closure (Iio a) = Iic a :=
  closure_Ioi' (α := αᵒᵈ) h

/-- The closure of the interval `(-∞, a)` is the interval `(-∞, a]`. -/
@[simp]
/--
theorem `closure_Iio` / 定理 `closure_Iio`

English:
theorem closure_Iio
  given: (a : α) [NoMinOrder α]
  statement: closure (Iio a) = Iic a
  proof: closure_Iio' nonempty_Iio

中文:
定理 closure_Iio
  条件: (a : α) [NoMinOrder α]
  结论: closure (Iio a) = Iic a
  证明: closure_Iio' nonempty_Iio

Depends on / 依赖: closure_Iio, nonempty_Iio
-/
theorem closure_Iio (a : α) [NoMinOrder α] : closure (Iio a) = Iic a :=
  closure_Iio' nonempty_Iio

/--
theorem `IsMax.of_disjoint_nhds_Ioi` / 定理 `IsMax.of_disjoint_nhds_Ioi`

English:
theorem IsMax.of_disjoint_nhds_Ioi
  statement: {x : α} {u : Set α} (hu : u in nhds x)
  proof: by
  by_contra hx
  exact (mem_closure_iff_nhds.mp (closure_Ioi' (not_isMax_iff.mp hx) ▸ self_mem_Ici) u hu).ne_empty
    (disjoint_iff.mp hd)

中文:
定理 IsMax.of_disjoint_nhds_Ioi
  结论: {x : α} {u : Set α} (hu : u in nhds x)
  证明: by
  by_contra hx
  exact (mem_closure_iff_nhds.mp (closure_Ioi' (not_isMax_iff.mp hx) ▸ self_mem_Ici) u hu).ne_empty
    (disjoint_iff.mp hd)

Depends on / 依赖: closure_Ioi, disjoint_iff, disjoint_iff.mp, mem_closure_iff_nhds, mem_closure_iff_nhds.mp, ne_empty, not_isMax_iff, not_isMax_iff.mp, self_mem_Ici
-/
theorem IsMax.of_disjoint_nhds_Ioi {x : α} {u : Set α} (hu : u in nhds x)
    (hd : Disjoint u (Set.Ioi x)) : IsMax x := by
  by_contra hx
  exact (mem_closure_iff_nhds.mp (closure_Ioi' (not_isMax_iff.mp hx) ▸ self_mem_Ici) u hu).ne_empty
    (disjoint_iff.mp hd)

/--
theorem `IsMin.of_disjoint_nhds_Iio` / 定理 `IsMin.of_disjoint_nhds_Iio`

English:
theorem IsMin.of_disjoint_nhds_Iio
  statement: {x : α} {u : Set α} (hu : u in nhds x)
  proof: IsMax.of_disjoint_nhds_Ioi (α := αᵒᵈ) hu hd

中文:
定理 IsMin.of_disjoint_nhds_Iio
  结论: {x : α} {u : Set α} (hu : u in nhds x)
  证明: IsMax.of_disjoint_nhds_Ioi (α := αᵒᵈ) hu hd

Depends on / 依赖: IsMax.of_disjoint_nhds_Ioi, of_disjoint_nhds_Ioi
-/
theorem IsMin.of_disjoint_nhds_Iio {x : α} {u : Set α} (hu : u in nhds x)
    (hd : Disjoint u (Set.Iio x)) : IsMin x :=
  IsMax.of_disjoint_nhds_Ioi (α := αᵒᵈ) hu hd

/--
theorem `nonempty_nhds_inter_Ioi` / 定理 `nonempty_nhds_inter_Ioi`

English:
theorem nonempty_nhds_inter_Ioi
  given: {x : α} {u : Set α} (hu : u in nhds x) (hx : ¬IsMax x)
  proof: by
  by_contra h
  exact hx (IsMax.of_disjoint_nhds_Ioi hu (Set.disjoint_iff_inter_eq_empty.mpr
    (Set.not_nonempty_iff_eq_empty.mp h)))

中文:
定理 nonempty_nhds_inter_Ioi
  条件: {x : α} {u : Set α} (hu : u in nhds x) (hx : ¬IsMax x)
  证明: by
  by_contra h
  exact hx (IsMax.of_disjoint_nhds_Ioi hu (Set.disjoint_iff_inter_eq_empty.mpr
    (Set.not_nonempty_iff_eq_empty.mp h)))

Depends on / 依赖: IsMax.of_disjoint_nhds_Ioi, Set.disjoint_iff_inter_eq_empty.mpr, Set.not_nonempty_iff_eq_empty.mp, disjoint_iff_inter_eq_empty, not_nonempty_iff_eq_empty, of_disjoint_nhds_Ioi
-/
theorem nonempty_nhds_inter_Ioi {x : α} {u : Set α} (hu : u in nhds x) (hx : ¬IsMax x) :
    (u inter Set.Ioi x).Nonempty := by
  by_contra h
  exact hx (IsMax.of_disjoint_nhds_Ioi hu (Set.disjoint_iff_inter_eq_empty.mpr
    (Set.not_nonempty_iff_eq_empty.mp h)))

/--
theorem `nonempty_nhds_inter_Iio` / 定理 `nonempty_nhds_inter_Iio`

English:
theorem nonempty_nhds_inter_Iio
  given: {x : α} {u : Set α} (hu : u in nhds x) (hx : ¬IsMin x)
  proof: nonempty_nhds_inter_Ioi (α := αᵒᵈ) hu hx

中文:
定理 nonempty_nhds_inter_Iio
  条件: {x : α} {u : Set α} (hu : u in nhds x) (hx : ¬IsMin x)
  证明: nonempty_nhds_inter_Ioi (α := αᵒᵈ) hu hx

Depends on / 依赖: nonempty_nhds_inter_Ioi
-/
theorem nonempty_nhds_inter_Iio {x : α} {u : Set α} (hu : u in nhds x) (hx : ¬IsMin x) :
    (u inter Set.Iio x).Nonempty :=
  nonempty_nhds_inter_Ioi (α := αᵒᵈ) hu hx

/-- The closure of the open interval `(a, b)` is the closed interval `[a, b]`. -/
@[simp]
/--
theorem `closure_Ioo` / 定理 `closure_Ioo`

English:
theorem closure_Ioo
  given: {a b : α} (hab : a != b)
  statement: closure (Ioo a b) = Icc a b
  proof: by
  apply Subset.antisymm
  · exact closure_minimal Ioo_subset_Icc_self isClosed_Icc
  · rcases hab.lt_or_gt with hab | hab
    · rw [← sdiff_subset_closure_iff, Icc_sdiff_Ioo_same hab.le]
      have hab' : (Ioo a b).Nonempty := nonempty_Ioo.2 hab
      simp only [insert_subset_iff, singleton_subse

中文:
定理 closure_Ioo
  条件: {a b : α} (hab : a != b)
  结论: closure (Ioo a b) = Icc a b
  证明: by
  apply Subset.antisymm
  · exact closure_minimal Ioo_subset_Icc_self isClosed_Icc
  · rcases hab.lt_or_gt with hab | hab
    · rw [← sdiff_subset_closure_iff, Icc_sdiff_Ioo_same hab.le]
      have hab' : (Ioo a b).Nonempty := nonempty_Ioo.2 hab
      simp only [insert_subset_iff, singleton_subse

Depends on / 依赖: Icc_eq_empty_of_lt, Icc_sdiff_Ioo_same, Ioo_subset_Icc_self, Nonempty, Subset, Subset.antisymm, antisymm, closure_minimal, empty_subset, hab.le, hab.lt_or_gt, insert_subset_iff, isClosed_Icc, isGLB_Ioo, isLUB_Ioo, lt_or_gt, mem_closure, nonempty_Ioo, sdiff_subset_closure_iff, singleton_subset_iff
-/
theorem closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal Ioo_subset_Icc_self isClosed_Icc
  · rcases hab.lt_or_gt with hab | hab
    · rw [← sdiff_subset_closure_iff, Icc_sdiff_Ioo_same hab.le]
      have hab' : (Ioo a b).Nonempty := nonempty_Ioo.2 hab
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨(isGLB_Ioo hab).mem_closure hab', (isLUB_Ioo hab).mem_closure hab'⟩
    · rw [Icc_eq_empty_of_lt hab]
      exact empty_subset _

@[simp]
/--
theorem `closure_uIoo` / 定理 `closure_uIoo`

English:
theorem closure_uIoo
  given: {a b : α} (hab : a != b)
  statement: closure (uIoo a b) = uIcc a b
  proof: by
  simp [uIoo, uIcc, hab]

中文:
定理 closure_uIoo
  条件: {a b : α} (hab : a != b)
  结论: closure (uIoo a b) = uIcc a b
  证明: by
  simp [uIoo, uIcc, hab]
-/
theorem closure_uIoo {a b : α} (hab : a != b) : closure (uIoo a b) = uIcc a b := by
  simp [uIoo, uIcc, hab]

/-- The closure of the interval `(a, b]` is the closed interval `[a, b]`. -/
@[simp]
/--
theorem `closure_Ioc` / 定理 `closure_Ioc`

English:
theorem closure_Ioc
  given: {a b : α} (hab : a != b)
  statement: closure (Ioc a b) = Icc a b
  proof: by
  apply Subset.antisymm
  · exact closure_minimal Ioc_subset_Icc_self isClosed_Icc
  · apply Subset.trans _ (closure_mono Ioo_subset_Ioc_self)
    rw [closure_Ioo hab]

@[simp]

中文:
定理 closure_Ioc
  条件: {a b : α} (hab : a != b)
  结论: closure (Ioc a b) = Icc a b
  证明: by
  apply Subset.antisymm
  · exact closure_minimal Ioc_subset_Icc_self isClosed_Icc
  · apply Subset.trans _ (closure_mono Ioo_subset_Ioc_self)
    rw [closure_Ioo hab]

@[simp]

Depends on / 依赖: Ioc_subset_Icc_self, Ioo_subset_Ioc_self, Subset, Subset.antisymm, Subset.trans, antisymm, closure_Ioo, closure_minimal, closure_mono, isClosed_Icc
-/
theorem closure_Ioc {a b : α} (hab : a != b) : closure (Ioc a b) = Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal Ioc_subset_Icc_self isClosed_Icc
  · apply Subset.trans _ (closure_mono Ioo_subset_Ioc_self)
    rw [closure_Ioo hab]

@[simp]
/--
theorem `closure_uIoc` / 定理 `closure_uIoc`

English:
theorem closure_uIoc
  given: {a b : α} (hab : a != b)
  statement: closure (uIoc a b) = uIcc a b
  proof: by
  simp [uIoc, uIcc, hab]

中文:
定理 closure_uIoc
  条件: {a b : α} (hab : a != b)
  结论: closure (uIoc a b) = uIcc a b
  证明: by
  simp [uIoc, uIcc, hab]
-/
theorem closure_uIoc {a b : α} (hab : a != b) : closure (uIoc a b) = uIcc a b := by
  simp [uIoc, uIcc, hab]

/-- The closure of the interval `[a, b)` is the closed interval `[a, b]`. -/
@[simp]
/--
theorem `closure_Ico` / 定理 `closure_Ico`

English:
theorem closure_Ico
  given: {a b : α} (hab : a != b)
  statement: closure (Ico a b) = Icc a b
  proof: by
  apply Subset.antisymm
  · exact closure_minimal Ico_subset_Icc_self isClosed_Icc
  · apply Subset.trans _ (closure_mono Ioo_subset_Ico_self)
    rw [closure_Ioo hab]

@[simp]

中文:
定理 closure_Ico
  条件: {a b : α} (hab : a != b)
  结论: closure (Ico a b) = Icc a b
  证明: by
  apply Subset.antisymm
  · exact closure_minimal Ico_subset_Icc_self isClosed_Icc
  · apply Subset.trans _ (closure_mono Ioo_subset_Ico_self)
    rw [closure_Ioo hab]

@[simp]

Depends on / 依赖: Ico_subset_Icc_self, Ioo_subset_Ico_self, Subset, Subset.antisymm, Subset.trans, antisymm, closure_Ioo, closure_minimal, closure_mono, isClosed_Icc
-/
theorem closure_Ico {a b : α} (hab : a != b) : closure (Ico a b) = Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal Ico_subset_Icc_self isClosed_Icc
  · apply Subset.trans _ (closure_mono Ioo_subset_Ico_self)
    rw [closure_Ioo hab]

@[simp]
/--
theorem `interior_Ici'` / 定理 `interior_Ici'`

English:
theorem interior_Ici'
  given: {a : α} (ha : (Iio a).Nonempty)
  statement: interior (Ici a) = Ioi a
  proof: by
  rw [← compl_Iio]; rw [interior_compl]; rw [closure_Iio' ha]; rw [compl_Iic]

中文:
定理 interior_Ici'
  条件: {a : α} (ha : (Iio a).Nonempty)
  结论: interior (Ici a) = Ioi a
  证明: by
  rw [← compl_Iio]; rw [interior_compl]; rw [closure_Iio' ha]; rw [compl_Iic]

Depends on / 依赖: closure_Iio, compl_Iic, compl_Iio, interior_compl
-/
theorem interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior (Ici a) = Ioi a := by
  rw [← compl_Iio]; rw [interior_compl]; rw [closure_Iio' ha]; rw [compl_Iic]

/--
theorem `interior_Ici` / 定理 `interior_Ici`

English:
theorem interior_Ici
  given: [NoMinOrder α] {a : α}
  statement: interior (Ici a) = Ioi a
  proof: interior_Ici' nonempty_Iio

@[simp]

中文:
定理 interior_Ici
  条件: [NoMinOrder α] {a : α}
  结论: interior (Ici a) = Ioi a
  证明: interior_Ici' nonempty_Iio

@[simp]

Depends on / 依赖: interior_Ici, nonempty_Iio
-/
theorem interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = Ioi a :=
  interior_Ici' nonempty_Iio

@[simp]
/--
theorem `interior_Iic'` / 定理 `interior_Iic'`

English:
theorem interior_Iic'
  given: {a : α} (ha : (Ioi a).Nonempty)
  statement: interior (Iic a) = Iio a
  proof: interior_Ici' (α := αᵒᵈ) ha

中文:
定理 interior_Iic'
  条件: {a : α} (ha : (Ioi a).Nonempty)
  结论: interior (Iic a) = Iio a
  证明: interior_Ici' (α := αᵒᵈ) ha

Depends on / 依赖: interior_Ici
-/
theorem interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior (Iic a) = Iio a :=
  interior_Ici' (α := αᵒᵈ) ha

/--
theorem `interior_Iic` / 定理 `interior_Iic`

English:
theorem interior_Iic
  given: [NoMaxOrder α] {a : α}
  statement: interior (Iic a) = Iio a
  proof: interior_Iic' nonempty_Ioi

@[simp]

中文:
定理 interior_Iic
  条件: [NoMaxOrder α] {a : α}
  结论: interior (Iic a) = Iio a
  证明: interior_Iic' nonempty_Ioi

@[simp]

Depends on / 依赖: interior_Iic, nonempty_Ioi
-/
theorem interior_Iic [NoMaxOrder α] {a : α} : interior (Iic a) = Iio a :=
  interior_Iic' nonempty_Ioi

@[simp]
/--
theorem `interior_Icc` / 定理 `interior_Icc`

English:
theorem interior_Icc
  given: [NoMinOrder α] [NoMaxOrder α] {a b : α}
  statement: interior (Icc a b) = Ioo a b
  proof: by
  rw [← Ici_inter_Iic]; rw [interior_inter]; rw [interior_Ici]; rw [interior_Iic]; rw [Ioi_inter_Iio]

@[simp]

中文:
定理 interior_Icc
  条件: [NoMinOrder α] [NoMaxOrder α] {a b : α}
  结论: interior (Icc a b) = Ioo a b
  证明: by
  rw [← Ici_inter_Iic]; rw [interior_inter]; rw [interior_Ici]; rw [interior_Iic]; rw [Ioi_inter_Iio]

@[simp]

Depends on / 依赖: Ici_inter_Iic, Ioi_inter_Iio, interior_Ici, interior_Iic, interior_inter
-/
theorem interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : interior (Icc a b) = Ioo a b := by
  rw [← Ici_inter_Iic]; rw [interior_inter]; rw [interior_Ici]; rw [interior_Iic]; rw [Ioi_inter_Iio]

@[simp]
/--
theorem `Icc_mem_nhds_iff` / 定理 `Icc_mem_nhds_iff`

English:
theorem Icc_mem_nhds_iff
  given: [NoMinOrder α] [NoMaxOrder α] {a b x : α}
  proof: by
  rw [← interior_Icc]; rw [mem_interior_iff_mem_nhds]

@[simp]

中文:
定理 Icc_mem_nhds_iff
  条件: [NoMinOrder α] [NoMaxOrder α] {a b x : α}
  证明: by
  rw [← interior_Icc]; rw [mem_interior_iff_mem_nhds]

@[simp]

Depends on / 依赖: interior_Icc, mem_interior_iff_mem_nhds
-/
theorem Icc_mem_nhds_iff [NoMinOrder α] [NoMaxOrder α] {a b x : α} :
    Icc a b in 𝓝 x ↔ x in Ioo a b := by
  rw [← interior_Icc]; rw [mem_interior_iff_mem_nhds]

@[simp]
/--
theorem `interior_Ico` / 定理 `interior_Ico`

English:
theorem interior_Ico
  given: [NoMinOrder α] {a b : α}
  statement: interior (Ico a b) = Ioo a b
  proof: by
  rw [← Ici_inter_Iio]; rw [interior_inter]; rw [interior_Ici]; rw [interior_Iio]; rw [Ioi_inter_Iio]

@[simp]

中文:
定理 interior_Ico
  条件: [NoMinOrder α] {a b : α}
  结论: interior (Ico a b) = Ioo a b
  证明: by
  rw [← Ici_inter_Iio]; rw [interior_inter]; rw [interior_Ici]; rw [interior_Iio]; rw [Ioi_inter_Iio]

@[simp]

Depends on / 依赖: Ici_inter_Iio, Ioi_inter_Iio, interior_Ici, interior_Iio, interior_inter
-/
theorem interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b) = Ioo a b := by
  rw [← Ici_inter_Iio]; rw [interior_inter]; rw [interior_Ici]; rw [interior_Iio]; rw [Ioi_inter_Iio]

@[simp]
/--
theorem `Ico_mem_nhds_iff` / 定理 `Ico_mem_nhds_iff`

English:
theorem Ico_mem_nhds_iff
  given: [NoMinOrder α] {a b x : α}
  statement: Ico a b in 𝓝 x ↔ x in Ioo a b
  proof: by
  rw [← interior_Ico]; rw [mem_interior_iff_mem_nhds]

@[simp]

中文:
定理 Ico_mem_nhds_iff
  条件: [NoMinOrder α] {a b x : α}
  结论: Ico a b in 𝓝 x ↔ x in Ioo a b
  证明: by
  rw [← interior_Ico]; rw [mem_interior_iff_mem_nhds]

@[simp]

Depends on / 依赖: interior_Ico, mem_interior_iff_mem_nhds
-/
theorem Ico_mem_nhds_iff [NoMinOrder α] {a b x : α} : Ico a b in 𝓝 x ↔ x in Ioo a b := by
  rw [← interior_Ico]; rw [mem_interior_iff_mem_nhds]

@[simp]
/--
theorem `interior_Ioc` / 定理 `interior_Ioc`

English:
theorem interior_Ioc
  given: [NoMaxOrder α] {a b : α}
  statement: interior (Ioc a b) = Ioo a b
  proof: by
  rw [← Ioi_inter_Iic]; rw [interior_inter]; rw [interior_Ioi]; rw [interior_Iic]; rw [Ioi_inter_Iio]

@[simp]

中文:
定理 interior_Ioc
  条件: [NoMaxOrder α] {a b : α}
  结论: interior (Ioc a b) = Ioo a b
  证明: by
  rw [← Ioi_inter_Iic]; rw [interior_inter]; rw [interior_Ioi]; rw [interior_Iic]; rw [Ioi_inter_Iio]

@[simp]

Depends on / 依赖: Ioi_inter_Iic, Ioi_inter_Iio, interior_Iic, interior_Ioi, interior_inter
-/
theorem interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b) = Ioo a b := by
  rw [← Ioi_inter_Iic]; rw [interior_inter]; rw [interior_Ioi]; rw [interior_Iic]; rw [Ioi_inter_Iio]

@[simp]
/--
theorem `Ioc_mem_nhds_iff` / 定理 `Ioc_mem_nhds_iff`

English:
theorem Ioc_mem_nhds_iff
  given: [NoMaxOrder α] {a b x : α}
  statement: Ioc a b in 𝓝 x ↔ x in Ioo a b
  proof: by
  rw [← interior_Ioc]; rw [mem_interior_iff_mem_nhds]

中文:
定理 Ioc_mem_nhds_iff
  条件: [NoMaxOrder α] {a b x : α}
  结论: Ioc a b in 𝓝 x ↔ x in Ioo a b
  证明: by
  rw [← interior_Ioc]; rw [mem_interior_iff_mem_nhds]

Depends on / 依赖: interior_Ioc, mem_interior_iff_mem_nhds
-/
theorem Ioc_mem_nhds_iff [NoMaxOrder α] {a b x : α} : Ioc a b in 𝓝 x ↔ x in Ioo a b := by
  rw [← interior_Ioc]; rw [mem_interior_iff_mem_nhds]

/--
theorem `closure_interior_Icc` / 定理 `closure_interior_Icc`

English:
theorem closure_interior_Icc
  given: {a b : α} (h : a != b)
  statement: closure (interior (Icc a b)) = Icc a b
  proof: (closure_minimal interior_subset isClosed_Icc).antisymm
    calc
      Icc a b = closure (Ioo a b) := (closure_Ioo h).symm
      _ subseteq closure (interior (Icc a b)) :=
        closure_mono (interior_maximal Ioo_subset_Icc_self isOpen_Ioo)

中文:
定理 closure_interior_Icc
  条件: {a b : α} (h : a != b)
  结论: closure (interior (Icc a b)) = Icc a b
  证明: (closure_minimal interior_subset isClosed_Icc).antisymm
    calc
      Icc a b = closure (Ioo a b) := (closure_Ioo h).symm
      _ subseteq closure (interior (Icc a b)) :=
        closure_mono (interior_maximal Ioo_subset_Icc_self isOpen_Ioo)

Depends on / 依赖: Ioo_subset_Icc_self, antisymm, closure, closure_Ioo, closure_minimal, closure_mono, interior, interior_maximal, interior_subset, isClosed_Icc, isOpen_Ioo, subseteq
-/
theorem closure_interior_Icc {a b : α} (h : a != b) : closure (interior (Icc a b)) = Icc a b :=
(closure_minimal interior_subset isClosed_Icc).antisymm
    calc
      Icc a b = closure (Ioo a b) := (closure_Ioo h).symm
      _ subseteq closure (interior (Icc a b)) :=
        closure_mono (interior_maximal Ioo_subset_Icc_self isOpen_Ioo)

/--
theorem `Ioc_subset_closure_interior` / 定理 `Ioc_subset_closure_interior`

English:
theorem Ioc_subset_closure_interior
  given: (a b : α)
  statement: Ioc a b subseteq closure (interior (Ioc a b))
  proof: by
  rcases eq_or_ne a b with (rfl | h)
  · simp
  · calc
      Ioc a b subseteq Icc a b := Ioc_subset_Icc_self
      _ = closure (Ioo a b) := (closure_Ioo h).symm
      _ subseteq closure (interior (Ioc a b)) :=
        closure_mono (interior_maximal Ioo_subset_Ioc_self isOpen_Ioo)

中文:
定理 Ioc_subset_closure_interior
  条件: (a b : α)
  结论: Ioc a b subseteq closure (interior (Ioc a b))
  证明: by
  rcases eq_or_ne a b with (rfl | h)
  · simp
  · calc
      Ioc a b subseteq Icc a b := Ioc_subset_Icc_self
      _ = closure (Ioo a b) := (closure_Ioo h).symm
      _ subseteq closure (interior (Ioc a b)) :=
        closure_mono (interior_maximal Ioo_subset_Ioc_self isOpen_Ioo)

Depends on / 依赖: Ioc_subset_Icc_self, Ioo_subset_Ioc_self, closure, closure_Ioo, closure_mono, eq_or_ne, interior, interior_maximal, isOpen_Ioo, subseteq
-/
theorem Ioc_subset_closure_interior (a b : α) : Ioc a b subseteq closure (interior (Ioc a b)) := by
  rcases eq_or_ne a b with (rfl | h)
  · simp
  · calc
      Ioc a b subseteq Icc a b := Ioc_subset_Icc_self
      _ = closure (Ioo a b) := (closure_Ioo h).symm
      _ subseteq closure (interior (Ioc a b)) :=
        closure_mono (interior_maximal Ioo_subset_Ioc_self isOpen_Ioo)

/--
theorem `Ico_subset_closure_interior` / 定理 `Ico_subset_closure_interior`

English:
theorem Ico_subset_closure_interior
  given: (a b : α)
  statement: Ico a b subseteq closure (interior (Ico a b))
  proof: by
  simpa only [Ioc_toDual] using!
    Ioc_subset_closure_interior (OrderDual.toDual b) (OrderDual.toDual a)

@[simp]

中文:
定理 Ico_subset_closure_interior
  条件: (a b : α)
  结论: Ico a b subseteq closure (interior (Ico a b))
  证明: by
  simpa only [Ioc_toDual] using!
    Ioc_subset_closure_interior (OrderDual.toDual b) (OrderDual.toDual a)

@[simp]

Depends on / 依赖: Ioc_subset_closure_interior, Ioc_toDual, OrderDual, OrderDual.toDual, toDual
-/
theorem Ico_subset_closure_interior (a b : α) : Ico a b subseteq closure (interior (Ico a b)) := by
  simpa only [Ioc_toDual] using!
    Ioc_subset_closure_interior (OrderDual.toDual b) (OrderDual.toDual a)

@[simp]
/--
theorem `frontier_Ici'` / 定理 `frontier_Ici'`

English:
theorem frontier_Ici'
  given: {a : α} (ha : (Iio a).Nonempty)
  statement: frontier (Ici a) = {a}
  proof: by
  simp [frontier, ha]

中文:
定理 frontier_Ici'
  条件: {a : α} (ha : (Iio a).Nonempty)
  结论: frontier (Ici a) = {a}
  证明: by
  simp [frontier, ha]

Depends on / 依赖: frontier
-/
theorem frontier_Ici' {a : α} (ha : (Iio a).Nonempty) : frontier (Ici a) = {a} := by
  simp [frontier, ha]

/--
theorem `frontier_Ici` / 定理 `frontier_Ici`

English:
theorem frontier_Ici
  given: [NoMinOrder α] {a : α}
  statement: frontier (Ici a) = {a}
  proof: frontier_Ici' nonempty_Iio

@[simp]

中文:
定理 frontier_Ici
  条件: [NoMinOrder α] {a : α}
  结论: frontier (Ici a) = {a}
  证明: frontier_Ici' nonempty_Iio

@[simp]

Depends on / 依赖: frontier_Ici, nonempty_Iio
-/
theorem frontier_Ici [NoMinOrder α] {a : α} : frontier (Ici a) = {a} :=
  frontier_Ici' nonempty_Iio

@[simp]
/--
theorem `frontier_Iic'` / 定理 `frontier_Iic'`

English:
theorem frontier_Iic'
  given: {a : α} (ha : (Ioi a).Nonempty)
  statement: frontier (Iic a) = {a}
  proof: by
  simp [frontier, ha]

中文:
定理 frontier_Iic'
  条件: {a : α} (ha : (Ioi a).Nonempty)
  结论: frontier (Iic a) = {a}
  证明: by
  simp [frontier, ha]

Depends on / 依赖: frontier
-/
theorem frontier_Iic' {a : α} (ha : (Ioi a).Nonempty) : frontier (Iic a) = {a} := by
  simp [frontier, ha]

/--
theorem `frontier_Iic` / 定理 `frontier_Iic`

English:
theorem frontier_Iic
  given: [NoMaxOrder α] {a : α}
  statement: frontier (Iic a) = {a}
  proof: frontier_Iic' nonempty_Ioi

@[simp]

中文:
定理 frontier_Iic
  条件: [NoMaxOrder α] {a : α}
  结论: frontier (Iic a) = {a}
  证明: frontier_Iic' nonempty_Ioi

@[simp]

Depends on / 依赖: frontier_Iic, nonempty_Ioi
-/
theorem frontier_Iic [NoMaxOrder α] {a : α} : frontier (Iic a) = {a} :=
  frontier_Iic' nonempty_Ioi

@[simp]
/--
theorem `frontier_Ioi'` / 定理 `frontier_Ioi'`

English:
theorem frontier_Ioi'
  given: {a : α} (ha : (Ioi a).Nonempty)
  statement: frontier (Ioi a) = {a}
  proof: by
  simp [frontier, closure_Ioi' ha]

中文:
定理 frontier_Ioi'
  条件: {a : α} (ha : (Ioi a).Nonempty)
  结论: frontier (Ioi a) = {a}
  证明: by
  simp [frontier, closure_Ioi' ha]

Depends on / 依赖: closure_Ioi, frontier
-/
theorem frontier_Ioi' {a : α} (ha : (Ioi a).Nonempty) : frontier (Ioi a) = {a} := by
  simp [frontier, closure_Ioi' ha]

/--
theorem `frontier_Ioi` / 定理 `frontier_Ioi`

English:
theorem frontier_Ioi
  given: [NoMaxOrder α] {a : α}
  statement: frontier (Ioi a) = {a}
  proof: frontier_Ioi' nonempty_Ioi

@[simp]

中文:
定理 frontier_Ioi
  条件: [NoMaxOrder α] {a : α}
  结论: frontier (Ioi a) = {a}
  证明: frontier_Ioi' nonempty_Ioi

@[simp]

Depends on / 依赖: frontier_Ioi, nonempty_Ioi
-/
theorem frontier_Ioi [NoMaxOrder α] {a : α} : frontier (Ioi a) = {a} :=
  frontier_Ioi' nonempty_Ioi

@[simp]
/--
theorem `frontier_Iio'` / 定理 `frontier_Iio'`

English:
theorem frontier_Iio'
  given: {a : α} (ha : (Iio a).Nonempty)
  statement: frontier (Iio a) = {a}
  proof: by
  simp [frontier, closure_Iio' ha]

中文:
定理 frontier_Iio'
  条件: {a : α} (ha : (Iio a).Nonempty)
  结论: frontier (Iio a) = {a}
  证明: by
  simp [frontier, closure_Iio' ha]

Depends on / 依赖: closure_Iio, frontier
-/
theorem frontier_Iio' {a : α} (ha : (Iio a).Nonempty) : frontier (Iio a) = {a} := by
  simp [frontier, closure_Iio' ha]

/--
theorem `frontier_Iio` / 定理 `frontier_Iio`

English:
theorem frontier_Iio
  given: [NoMinOrder α] {a : α}
  statement: frontier (Iio a) = {a}
  proof: frontier_Iio' nonempty_Iio

@[simp]

中文:
定理 frontier_Iio
  条件: [NoMinOrder α] {a : α}
  结论: frontier (Iio a) = {a}
  证明: frontier_Iio' nonempty_Iio

@[simp]

Depends on / 依赖: frontier_Iio, nonempty_Iio
-/
theorem frontier_Iio [NoMinOrder α] {a : α} : frontier (Iio a) = {a} :=
  frontier_Iio' nonempty_Iio

@[simp]
/--
theorem `frontier_Icc` / 定理 `frontier_Icc`

English:
theorem frontier_Icc
  given: [NoMinOrder α] [NoMaxOrder α] {a b : α} (h : a <= b)
  proof: by simp [frontier, h, Icc_sdiff_Ioo_same]

@[simp]

中文:
定理 frontier_Icc
  条件: [NoMinOrder α] [NoMaxOrder α] {a b : α} (h : a <= b)
  证明: by simp [frontier, h, Icc_sdiff_Ioo_same]

@[simp]

Depends on / 依赖: Icc_sdiff_Ioo_same, frontier
-/
theorem frontier_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} (h : a <= b) :
    frontier (Icc a b) = {a, b} := by simp [frontier, h, Icc_sdiff_Ioo_same]

@[simp]
/--
theorem `frontier_Ioo` / 定理 `frontier_Ioo`

English:
theorem frontier_Ioo
  given: {a b : α} (h : a < b)
  statement: frontier (Ioo a b) = {a, b}
  proof: by
  rw [frontier]; rw [closure_Ioo h.ne]; rw [interior_Ioo]; rw [Icc_sdiff_Ioo_same h.le]

@[simp]

中文:
定理 frontier_Ioo
  条件: {a b : α} (h : a < b)
  结论: frontier (Ioo a b) = {a, b}
  证明: by
  rw [frontier]; rw [closure_Ioo h.ne]; rw [interior_Ioo]; rw [Icc_sdiff_Ioo_same h.le]

@[simp]

Depends on / 依赖: Icc_sdiff_Ioo_same, closure_Ioo, frontier, h.le, h.ne, interior_Ioo
-/
theorem frontier_Ioo {a b : α} (h : a < b) : frontier (Ioo a b) = {a, b} := by
  rw [frontier]; rw [closure_Ioo h.ne]; rw [interior_Ioo]; rw [Icc_sdiff_Ioo_same h.le]

@[simp]
/--
theorem `frontier_Ico` / 定理 `frontier_Ico`

English:
theorem frontier_Ico
  given: [NoMinOrder α] {a b : α} (h : a < b)
  statement: frontier (Ico a b) = {a, b}
  proof: by
  rw [frontier]; rw [closure_Ico h.ne]; rw [interior_Ico]; rw [Icc_sdiff_Ioo_same h.le]

@[simp]

中文:
定理 frontier_Ico
  条件: [NoMinOrder α] {a b : α} (h : a < b)
  结论: frontier (Ico a b) = {a, b}
  证明: by
  rw [frontier]; rw [closure_Ico h.ne]; rw [interior_Ico]; rw [Icc_sdiff_Ioo_same h.le]

@[simp]

Depends on / 依赖: Icc_sdiff_Ioo_same, closure_Ico, frontier, h.le, h.ne, interior_Ico
-/
theorem frontier_Ico [NoMinOrder α] {a b : α} (h : a < b) : frontier (Ico a b) = {a, b} := by
  rw [frontier]; rw [closure_Ico h.ne]; rw [interior_Ico]; rw [Icc_sdiff_Ioo_same h.le]

@[simp]
/--
theorem `frontier_Ioc` / 定理 `frontier_Ioc`

English:
theorem frontier_Ioc
  given: [NoMaxOrder α] {a b : α} (h : a < b)
  statement: frontier (Ioc a b) = {a, b}
  proof: by
  rw [frontier]; rw [closure_Ioc h.ne]; rw [interior_Ioc]; rw [Icc_sdiff_Ioo_same h.le]

中文:
定理 frontier_Ioc
  条件: [NoMaxOrder α] {a b : α} (h : a < b)
  结论: frontier (Ioc a b) = {a, b}
  证明: by
  rw [frontier]; rw [closure_Ioc h.ne]; rw [interior_Ioc]; rw [Icc_sdiff_Ioo_same h.le]

Depends on / 依赖: Icc_sdiff_Ioo_same, closure_Ioc, frontier, h.le, h.ne, interior_Ioc
-/
theorem frontier_Ioc [NoMaxOrder α] {a b : α} (h : a < b) : frontier (Ioc a b) = {a, b} := by
  rw [frontier]; rw [closure_Ioc h.ne]; rw [interior_Ioc]; rw [Icc_sdiff_Ioo_same h.le]

/--
theorem `nhdsWithin_Ioi_neBot'` / 定理 `nhdsWithin_Ioi_neBot'`

English:
theorem nhdsWithin_Ioi_neBot'
  given: {a b : α} (H₁ : (Ioi a).Nonempty) (H₂ : a <= b)
  proof: mem_closure_iff_nhdsWithin_neBot.1 by rwa [closure_Ioi' H₁]

中文:
定理 nhdsWithin_Ioi_neBot'
  条件: {a b : α} (H₁ : (Ioi a).Nonempty) (H₂ : a <= b)
  证明: mem_closure_iff_nhdsWithin_neBot.1 by rwa [closure_Ioi' H₁]

Depends on / 依赖: closure_Ioi, mem_closure_iff_nhdsWithin_neBot
-/
theorem nhdsWithin_Ioi_neBot' {a b : α} (H₁ : (Ioi a).Nonempty) (H₂ : a <= b) :
    NeBot (𝓝[Ioi a] b) :=
mem_closure_iff_nhdsWithin_neBot.1 by rwa [closure_Ioi' H₁]

/--
theorem `nhdsWithin_Ioi_neBot` / 定理 `nhdsWithin_Ioi_neBot`

English:
theorem nhdsWithin_Ioi_neBot
  given: [NoMaxOrder α] {a b : α} (H : a <= b)
  statement: NeBot (𝓝[Ioi a] b)
  proof: nhdsWithin_Ioi_neBot' nonempty_Ioi H

中文:
定理 nhdsWithin_Ioi_neBot
  条件: [NoMaxOrder α] {a b : α} (H : a <= b)
  结论: NeBot (𝓝[Ioi a] b)
  证明: nhdsWithin_Ioi_neBot' nonempty_Ioi H

Depends on / 依赖: nhdsWithin_Ioi_neBot, nonempty_Ioi
-/
theorem nhdsWithin_Ioi_neBot [NoMaxOrder α] {a b : α} (H : a <= b) : NeBot (𝓝[Ioi a] b) :=
  nhdsWithin_Ioi_neBot' nonempty_Ioi H

/--
theorem `nhdsGT_neBot_of_exists_gt` / 定理 `nhdsGT_neBot_of_exists_gt`

English:
theorem nhdsGT_neBot_of_exists_gt
  given: {a : α} (H : exists b, a < b)
  statement: NeBot (𝓝[>] a)
  proof: nhdsWithin_Ioi_neBot' H (le_refl a)

中文:
定理 nhdsGT_neBot_of_exists_gt
  条件: {a : α} (H : 存在 b, a < b)
  结论: NeBot (𝓝[>] a)
  证明: nhdsWithin_Ioi_neBot' H (le_refl a)

Depends on / 依赖: le_refl, nhdsWithin_Ioi_neBot
-/
theorem nhdsGT_neBot_of_exists_gt {a : α} (H : exists b, a < b) : NeBot (𝓝[>] a) :=
  nhdsWithin_Ioi_neBot' H (le_refl a)

/--
Instance `nhdsGT_neBot` / 实例 `nhdsGT_neBot`

English:
instance nhdsGT_neBot
  signature: [NoMaxOrder α] (a : α)
  body: nhdsWithin_Ioi_neBot le_rfl

中文:
实例 nhdsGT_neBot
  签名: [NoMaxOrder α] (a : α)
  定义体: nhdsWithin_Ioi_neBot le_rfl

Depends on / 依赖: le_rfl, nhdsWithin_Ioi_neBot
-/
instance nhdsGT_neBot [NoMaxOrder α] (a : α) : NeBot (𝓝[>] a) := nhdsWithin_Ioi_neBot le_rfl

/--
theorem `nhdsWithin_Iio_neBot'` / 定理 `nhdsWithin_Iio_neBot'`

English:
theorem nhdsWithin_Iio_neBot'
  given: {b c : α} (H₁ : (Iio c).Nonempty) (H₂ : b <= c)
  proof: mem_closure_iff_nhdsWithin_neBot.1 by rwa [closure_Iio' H₁]

中文:
定理 nhdsWithin_Iio_neBot'
  条件: {b c : α} (H₁ : (Iio c).Nonempty) (H₂ : b <= c)
  证明: mem_closure_iff_nhdsWithin_neBot.1 by rwa [closure_Iio' H₁]

Depends on / 依赖: closure_Iio, mem_closure_iff_nhdsWithin_neBot
-/
theorem nhdsWithin_Iio_neBot' {b c : α} (H₁ : (Iio c).Nonempty) (H₂ : b <= c) :
    NeBot (𝓝[Iio c] b) :=
mem_closure_iff_nhdsWithin_neBot.1 by rwa [closure_Iio' H₁]

/--
theorem `nhdsWithin_Iio_neBot` / 定理 `nhdsWithin_Iio_neBot`

English:
theorem nhdsWithin_Iio_neBot
  given: [NoMinOrder α] {a b : α} (H : a <= b)
  statement: NeBot (𝓝[Iio b] a)
  proof: nhdsWithin_Iio_neBot' nonempty_Iio H

中文:
定理 nhdsWithin_Iio_neBot
  条件: [NoMinOrder α] {a b : α} (H : a <= b)
  结论: NeBot (𝓝[Iio b] a)
  证明: nhdsWithin_Iio_neBot' nonempty_Iio H

Depends on / 依赖: nhdsWithin_Iio_neBot, nonempty_Iio
-/
theorem nhdsWithin_Iio_neBot [NoMinOrder α] {a b : α} (H : a <= b) : NeBot (𝓝[Iio b] a) :=
  nhdsWithin_Iio_neBot' nonempty_Iio H

/--
theorem `nhdsLT_neBot_of_exists_lt` / 定理 `nhdsLT_neBot_of_exists_lt`

English:
theorem nhdsLT_neBot_of_exists_lt
  given: {b : α} (H : exists a, a < b)
  statement: NeBot (𝓝[<] b)
  proof: nhdsWithin_Iio_neBot' H (le_refl b)

@[deprecated (since := "2026-01-16")] alias nhdsWithin_Iio_self_neBot' := nhdsLT_neBot_of_exists_lt

中文:
定理 nhdsLT_neBot_of_exists_lt
  条件: {b : α} (H : 存在 a, a < b)
  结论: NeBot (𝓝[<] b)
  证明: nhdsWithin_Iio_neBot' H (le_refl b)

@[deprecated (since := "2026-01-16")] alias nhdsWithin_Iio_self_neBot' := nhdsLT_neBot_of_exists_lt

Depends on / 依赖: le_refl, nhdsWithin_Iio_neBot
-/
theorem nhdsLT_neBot_of_exists_lt {b : α} (H : exists a, a < b) : NeBot (𝓝[<] b) :=
  nhdsWithin_Iio_neBot' H (le_refl b)

@[deprecated (since := "2026-01-16")] alias nhdsWithin_Iio_self_neBot' := nhdsLT_neBot_of_exists_lt

/--
Instance `nhdsLT_neBot` / 实例 `nhdsLT_neBot`

English:
instance nhdsLT_neBot
  signature: [NoMinOrder α] (a : α)
  body: nhdsWithin_Iio_neBot (le_refl a)

中文:
实例 nhdsLT_neBot
  签名: [NoMinOrder α] (a : α)
  定义体: nhdsWithin_Iio_neBot (le_refl a)

Depends on / 依赖: le_refl, nhdsWithin_Iio_neBot
-/
instance nhdsLT_neBot [NoMinOrder α] (a : α) : NeBot (𝓝[<] a) := nhdsWithin_Iio_neBot (le_refl a)

/--
theorem `right_nhdsWithin_Ico_neBot` / 定理 `right_nhdsWithin_Ico_neBot`

English:
theorem right_nhdsWithin_Ico_neBot
  given: {a b : α} (H : a < b)
  statement: NeBot (𝓝[Ico a b] b)
  proof: (isLUB_Ico H).nhdsWithin_neBot (nonempty_Ico.2 H)

中文:
定理 right_nhdsWithin_Ico_neBot
  条件: {a b : α} (H : a < b)
  结论: NeBot (𝓝[Ico a b] b)
  证明: (isLUB_Ico H).nhdsWithin_neBot (nonempty_Ico.2 H)

Depends on / 依赖: isLUB_Ico, nhdsWithin_neBot, nonempty_Ico
-/
theorem right_nhdsWithin_Ico_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ico a b] b) :=
  (isLUB_Ico H).nhdsWithin_neBot (nonempty_Ico.2 H)

/--
theorem `left_nhdsWithin_Ioc_neBot` / 定理 `left_nhdsWithin_Ioc_neBot`

English:
theorem left_nhdsWithin_Ioc_neBot
  given: {a b : α} (H : a < b)
  statement: NeBot (𝓝[Ioc a b] a)
  proof: (isGLB_Ioc H).nhdsWithin_neBot (nonempty_Ioc.2 H)

中文:
定理 left_nhdsWithin_Ioc_neBot
  条件: {a b : α} (H : a < b)
  结论: NeBot (𝓝[Ioc a b] a)
  证明: (isGLB_Ioc H).nhdsWithin_neBot (nonempty_Ioc.2 H)

Depends on / 依赖: isGLB_Ioc, nhdsWithin_neBot, nonempty_Ioc
-/
theorem left_nhdsWithin_Ioc_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioc a b] a) :=
  (isGLB_Ioc H).nhdsWithin_neBot (nonempty_Ioc.2 H)

/--
theorem `left_nhdsWithin_Ioo_neBot` / 定理 `left_nhdsWithin_Ioo_neBot`

English:
theorem left_nhdsWithin_Ioo_neBot
  given: {a b : α} (H : a < b)
  statement: NeBot (𝓝[Ioo a b] a)
  proof: (isGLB_Ioo H).nhdsWithin_neBot (nonempty_Ioo.2 H)

中文:
定理 left_nhdsWithin_Ioo_neBot
  条件: {a b : α} (H : a < b)
  结论: NeBot (𝓝[Ioo a b] a)
  证明: (isGLB_Ioo H).nhdsWithin_neBot (nonempty_Ioo.2 H)

Depends on / 依赖: isGLB_Ioo, nhdsWithin_neBot, nonempty_Ioo
-/
theorem left_nhdsWithin_Ioo_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioo a b] a) :=
  (isGLB_Ioo H).nhdsWithin_neBot (nonempty_Ioo.2 H)

/--
theorem `right_nhdsWithin_Ioo_neBot` / 定理 `right_nhdsWithin_Ioo_neBot`

English:
theorem right_nhdsWithin_Ioo_neBot
  given: {a b : α} (H : a < b)
  statement: NeBot (𝓝[Ioo a b] b)
  proof: (isLUB_Ioo H).nhdsWithin_neBot (nonempty_Ioo.2 H)

中文:
定理 right_nhdsWithin_Ioo_neBot
  条件: {a b : α} (H : a < b)
  结论: NeBot (𝓝[Ioo a b] b)
  证明: (isLUB_Ioo H).nhdsWithin_neBot (nonempty_Ioo.2 H)

Depends on / 依赖: isLUB_Ioo, nhdsWithin_neBot, nonempty_Ioo
-/
theorem right_nhdsWithin_Ioo_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioo a b] b) :=
  (isLUB_Ioo H).nhdsWithin_neBot (nonempty_Ioo.2 H)

instance (x : α) [Nontrivial α] : NeBot (𝓝[!=] x) := by
  refine forall_mem_nonempty_iff_neBot.1 fun s hs => ?_
  obtain ⟨u, u_open, xu, us⟩ : exists u : Set α, IsOpen u ∧ x in u ∧ u inter {x}ᶜ subseteq s := mem_nhdsWithin.1 hs
  obtain ⟨a, b, a_lt_b, hab⟩ : exists a b : α, a < b ∧ Ioo a b subseteq u := u_open.exists_Ioo_subset ⟨x, xu⟩
  obtain ⟨y, hy⟩ : exists y, a < y ∧ y < b := exists_between a_lt_b
  rcases ne_or_eq x y with (xy | rfl)
  · exact ⟨y, us ⟨hab hy, xy.symm⟩⟩
  obtain ⟨z, hz⟩ : exists z, a < z ∧ z < x := exists_between hy.1
  exact ⟨z, us ⟨hab ⟨hz.1, hz.2.trans hy.2⟩, hz.2.ne⟩⟩

/--
lemma `DenselyOrdered.subsingleton_of_discreteTopology` / 引理 `DenselyOrdered.subsingleton_of_discreteTopology`

English:
lemma DenselyOrdered.subsingleton_of_discreteTopology
  given: [DiscreteTopology α]
  statement: Subsingleton α
  proof: by
  suffices forall a b : α, b <= a from ⟨fun a b => le_antisymm (this b a) (this a b)⟩
  intro a b
  by_contra! contra
  have : Ioo a b = Icc a b := by rw [← closure_discrete (Ioo a b), closure_Ioo contra.ne]
  grind => have : b in Ioo a b; finish

中文:
引理 DenselyOrdered.subsingleton_of_discreteTopology
  条件: [DiscreteTopology α]
  结论: Subsingleton α
  证明: by
  suffices forall a b : α, b <= a from ⟨fun a b => le_antisymm (this b a) (this a b)⟩
  intro a b
  by_contra! contra
  have : Ioo a b = Icc a b := by rw [← closure_discrete (Ioo a b), closure_Ioo contra.ne]
  grind => have : b in Ioo a b; finish

Depends on / 依赖: closure_Ioo, closure_discrete, contra, contra.ne, finish, le_antisymm
-/
lemma DenselyOrdered.subsingleton_of_discreteTopology [DiscreteTopology α] : Subsingleton α := by
  suffices forall a b : α, b <= a from ⟨fun a b => le_antisymm (this b a) (this a b)⟩
  intro a b
  by_contra! contra
  have : Ioo a b = Icc a b := by rw [← closure_discrete (Ioo a b), closure_Ioo contra.ne]
  grind => have : b in Ioo a b; finish

/--
theorem `Dense.exists_countable_dense_subset_no_bot_top` / 定理 `Dense.exists_countable_dense_subset_no_bot_top`

English:
theorem Dense.exists_countable_dense_subset_no_bot_top
  statement: [Nontrivial α] {s : Set α} [SeparableSpace s]
  proof: by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, htd⟩
  refine ⟨t \ ({ x | IsBot x } union { x | IsTop x }), ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact sdiff_subset.trans hts
  · exact htc.mono sdiff_subset
  · exact htd.sdiff_finite ((subsingleton_isBot α).finite.union (su

中文:
定理 Dense.exists_countable_dense_subset_no_bot_top
  结论: [Nontrivial α] {s : Set α} [SeparableSpace s]
  证明: by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, htd⟩
  refine ⟨t \ ({ x | IsBot x } union { x | IsTop x }), ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact sdiff_subset.trans hts
  · exact htc.mono sdiff_subset
  · exact htd.sdiff_finite ((subsingleton_isBot α).finite.union (su

Depends on / 依赖: exists_countable_dense_subset, finite, finite.union, hs.exists_countable_dense_subset, htc.mono, htd.sdiff_finite, sdiff_finite, sdiff_subset, sdiff_subset.trans, subsingleton_isBot, subsingleton_isTop
-/
theorem Dense.exists_countable_dense_subset_no_bot_top [Nontrivial α] {s : Set α} [SeparableSpace s]
    (hs : Dense s) :
    exists t, t subseteq s ∧ t.Countable ∧ Dense t ∧ (forall x, IsBot x -> x ∉ t) ∧ forall x, IsTop x -> x ∉ t := by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, htd⟩
  refine ⟨t \ ({ x | IsBot x } union { x | IsTop x }), ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact sdiff_subset.trans hts
  · exact htc.mono sdiff_subset
  · exact htd.sdiff_finite ((subsingleton_isBot α).finite.union (subsingleton_isTop α).finite)
  · simp [hx]
  · simp [hx]

variable (α) in
/--
theorem `exists_countable_dense_no_bot_top` / 定理 `exists_countable_dense_no_bot_top`

English:
theorem exists_countable_dense_no_bot_top
  given: [SeparableSpace α] [Nontrivial α]
  proof: by
  simpa using dense_univ.exists_countable_dense_subset_no_bot_top

中文:
定理 exists_countable_dense_no_bot_top
  条件: [SeparableSpace α] [Nontrivial α]
  证明: by
  simpa using dense_univ.exists_countable_dense_subset_no_bot_top

Depends on / 依赖: dense_univ, dense_univ.exists_countable_dense_subset_no_bot_top, exists_countable_dense_subset_no_bot_top
-/
theorem exists_countable_dense_no_bot_top [SeparableSpace α] [Nontrivial α] :
    exists s : Set α, s.Countable ∧ Dense s ∧ (forall x, IsBot x -> x ∉ s) ∧ forall x, IsTop x -> x ∉ s := by
  simpa using dense_univ.exists_countable_dense_subset_no_bot_top

/-- `Set.Ico a b` is only closed if it is empty. -/
@[simp]
/--
theorem `isClosed_Ico_iff` / 定理 `isClosed_Ico_iff`

English:
theorem isClosed_Ico_iff
  given: {a b : α}
  statement: IsClosed (Set.Ico a b) ↔ b <= a
  proof: by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ico hab.ne]; rw [Icc_eq_Ico_same_iff] at this
  exact this hab.le

中文:
定理 isClosed_Ico_iff
  条件: {a b : α}
  结论: IsClosed (Set.Ico a b) ↔ b <= a
  证明: by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ico hab.ne]; rw [Icc_eq_Ico_same_iff] at this
  exact this hab.le

Depends on / 依赖: Icc_eq_Ico_same_iff, closure_Ico, closure_eq, h.closure_eq, hab.le, hab.ne, le_of_not_gt
-/
theorem isClosed_Ico_iff {a b : α} : IsClosed (Set.Ico a b) ↔ b <= a := by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ico hab.ne]; rw [Icc_eq_Ico_same_iff] at this
  exact this hab.le

/-- `Set.Ioc a b` is only closed if it is empty. -/
@[simp]
/--
theorem `isClosed_Ioc_iff` / 定理 `isClosed_Ioc_iff`

English:
theorem isClosed_Ioc_iff
  given: {a b : α}
  statement: IsClosed (Set.Ioc a b) ↔ b <= a
  proof: by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ioc hab.ne]; rw [Icc_eq_Ioc_same_iff] at this
  exact this hab.le

中文:
定理 isClosed_Ioc_iff
  条件: {a b : α}
  结论: IsClosed (Set.Ioc a b) ↔ b <= a
  证明: by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ioc hab.ne]; rw [Icc_eq_Ioc_same_iff] at this
  exact this hab.le

Depends on / 依赖: Icc_eq_Ioc_same_iff, closure_Ioc, closure_eq, h.closure_eq, hab.le, hab.ne, le_of_not_gt
-/
theorem isClosed_Ioc_iff {a b : α} : IsClosed (Set.Ioc a b) ↔ b <= a := by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ioc hab.ne]; rw [Icc_eq_Ioc_same_iff] at this
  exact this hab.le

/-- `Set.Ioo a b` is only closed if it is empty. -/
@[simp]
/--
theorem `isClosed_Ioo_iff` / 定理 `isClosed_Ioo_iff`

English:
theorem isClosed_Ioo_iff
  given: {a b : α}
  statement: IsClosed (Set.Ioo a b) ↔ b <= a
  proof: by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ioo hab.ne]; rw [Icc_eq_Ioo_same_iff] at this
  exact this hab.le

中文:
定理 isClosed_Ioo_iff
  条件: {a b : α}
  结论: IsClosed (Set.Ioo a b) ↔ b <= a
  证明: by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ioo hab.ne]; rw [Icc_eq_Ioo_same_iff] at this
  exact this hab.le

Depends on / 依赖: Icc_eq_Ioo_same_iff, closure_Ioo, closure_eq, h.closure_eq, hab.le, hab.ne, le_of_not_gt
-/
theorem isClosed_Ioo_iff {a b : α} : IsClosed (Set.Ioo a b) ↔ b <= a := by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ioo hab.ne]; rw [Icc_eq_Ioo_same_iff] at this
  exact this hab.le

end DenselyOrdered
