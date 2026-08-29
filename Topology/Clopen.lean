/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.BoolIndicator
public import Mathlib.Topology.ContinuousOn

/-!
# Clopen sets

A clopen set is a set that is both closed and open.
-/

public section

open Set Filter Topology TopologicalSpace

universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Clopen

/--
theorem `IsClopen.isOpen` / 定理 `IsClopen.isOpen`

English:
theorem IsClopen.isOpen
  given: (hs : IsClopen s)
  statement: IsOpen s
  proof: hs.2

中文:
定理 IsClopen.isOpen
  条件: (hs : IsClopen s)
  结论: 是开集 s
  证明: hs.2
-/
protected theorem IsClopen.isOpen (hs : IsClopen s) : IsOpen s := hs.2

/--
theorem `IsClopen.isClosed` / 定理 `IsClopen.isClosed`

English:
theorem IsClopen.isClosed
  given: (hs : IsClopen s)
  statement: IsClosed s
  proof: hs.1

中文:
定理 IsClopen.isClosed
  条件: (hs : IsClopen s)
  结论: 是闭集 s
  证明: hs.1
-/
protected theorem IsClopen.isClosed (hs : IsClopen s) : IsClosed s := hs.1

/--
theorem `isClopen_iff_frontier_eq_empty` / 定理 `isClopen_iff_frontier_eq_empty`

English:
theorem isClopen_iff_frontier_eq_empty
  statement: IsClopen s ↔ frontier s = ∅
  proof: by
  rw [IsClopen]; rw [← closure_eq_iff_isClosed]; rw [← interior_eq_iff_isOpen]; rw [frontier]; rw [sdiff_eq_empty]
  refine ⟨fun h => (h.1.trans h.2.symm).subset, fun h => ?_⟩
  exact ⟨(h.trans interior_subset).antisymm subset_closure,
    interior_subset.antisymm (subset_closure.trans h)⟩

@[simp] alias ⟨IsClopen.frontier_eq, _⟩ := isClopen_iff_frontier_eq_empty

中文:
定理 isClopen_iff_frontier_eq_empty
  结论: IsClopen s ↔ frontier s = ∅
  证明: by
  rw [IsClopen]; rw [← closure_eq_iff_isClosed]; rw [← interior_eq_iff_isOpen]; rw [frontier]; rw [sdiff_eq_empty]
  refine ⟨fun h => (h.1.trans h.2.symm).subset, fun h => ?_⟩
  exact ⟨(h.trans interior_subset).antisymm subset_closure,
    interior_subset.antisymm (subset_closure.trans h)⟩

@[simp] alias ⟨IsClopen.frontier_eq, _⟩ := isClopen_iff_frontier_eq_empty

Depends on / 依赖: IsClopen, antisymm, closure_eq_iff_isClosed, frontier, h.trans, interior_eq_iff_isOpen, interior_subset, interior_subset.antisymm, sdiff_eq_empty, subset, subset_closure, subset_closure.trans
-/
theorem isClopen_iff_frontier_eq_empty : IsClopen s ↔ frontier s = ∅ := by
  rw [IsClopen]; rw [← closure_eq_iff_isClosed]; rw [← interior_eq_iff_isOpen]; rw [frontier]; rw [sdiff_eq_empty]
  refine ⟨fun h => (h.1.trans h.2.symm).subset, fun h => ?_⟩
  exact ⟨(h.trans interior_subset).antisymm subset_closure,
    interior_subset.antisymm (subset_closure.trans h)⟩

@[simp] alias ⟨IsClopen.frontier_eq, _⟩ := isClopen_iff_frontier_eq_empty

/--
theorem `IsClopen.union` / 定理 `IsClopen.union`

English:
theorem IsClopen.union
  given: (hs : IsClopen s) (ht : IsClopen t)
  statement: IsClopen (s union t)
  proof: ⟨hs.1.union ht.1, hs.2.union ht.2⟩

中文:
定理 IsClopen.union
  条件: (hs : IsClopen s) (ht : IsClopen t)
  结论: IsClopen (s union t)
  证明: ⟨hs.1.union ht.1, hs.2.union ht.2⟩
-/
theorem IsClopen.union (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s union t) :=
  ⟨hs.1.union ht.1, hs.2.union ht.2⟩

/--
theorem `IsClopen.inter` / 定理 `IsClopen.inter`

English:
theorem IsClopen.inter
  given: (hs : IsClopen s) (ht : IsClopen t)
  statement: IsClopen (s inter t)
  proof: ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

中文:
定理 IsClopen.inter
  条件: (hs : IsClopen s) (ht : IsClopen t)
  结论: IsClopen (s inter t)
  证明: ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩
-/
theorem IsClopen.inter (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s inter t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

/--
theorem `isClopen_empty` / 定理 `isClopen_empty`

English:
theorem isClopen_empty
  statement: IsClopen (∅ : Set X)
  proof: ⟨isClosed_empty, isOpen_empty⟩

中文:
定理 isClopen_empty
  结论: IsClopen (∅ : 集合 X)
  证明: ⟨isClosed_empty, isOpen_empty⟩

Depends on / 依赖: isClosed_empty, isOpen_empty
-/
theorem isClopen_empty : IsClopen (∅ : Set X) := ⟨isClosed_empty, isOpen_empty⟩

/--
theorem `isClopen_univ` / 定理 `isClopen_univ`

English:
theorem isClopen_univ
  statement: IsClopen (univ : Set X)
  proof: ⟨isClosed_univ, isOpen_univ⟩

中文:
定理 isClopen_univ
  结论: IsClopen (univ : 集合 X)
  证明: ⟨isClosed_univ, isOpen_univ⟩

Depends on / 依赖: isClosed_univ, isOpen_univ
-/
theorem isClopen_univ : IsClopen (univ : Set X) := ⟨isClosed_univ, isOpen_univ⟩

/--
theorem `IsClopen.compl` / 定理 `IsClopen.compl`

English:
theorem IsClopen.compl
  given: (hs : IsClopen s)
  statement: IsClopen sᶜ
  proof: ⟨hs.2.isClosed_compl, hs.1.isOpen_compl⟩

@[simp]

中文:
定理 IsClopen.compl
  条件: (hs : IsClopen s)
  结论: IsClopen sᶜ
  证明: ⟨hs.2.isClosed_compl, hs.1.isOpen_compl⟩

@[simp]

Depends on / 依赖: isClosed_compl, isOpen_compl
-/
theorem IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ :=
  ⟨hs.2.isClosed_compl, hs.1.isOpen_compl⟩

@[simp]
/--
theorem `isClopen_compl_iff` / 定理 `isClopen_compl_iff`

English:
theorem isClopen_compl_iff
  statement: IsClopen sᶜ ↔ IsClopen s
  proof: ⟨fun h => compl_compl s ▸ IsClopen.compl h, IsClopen.compl⟩

中文:
定理 isClopen_compl_iff
  结论: IsClopen sᶜ ↔ IsClopen s
  证明: ⟨fun h => compl_compl s ▸ IsClopen.compl h, IsClopen.compl⟩

Depends on / 依赖: IsClopen, IsClopen.compl, compl_compl
-/
theorem isClopen_compl_iff : IsClopen sᶜ ↔ IsClopen s :=
  ⟨fun h => compl_compl s ▸ IsClopen.compl h, IsClopen.compl⟩

/--
theorem `IsClopen.diff` / 定理 `IsClopen.diff`

English:
theorem IsClopen.diff
  given: (hs : IsClopen s) (ht : IsClopen t)
  statement: IsClopen (s \ t)
  proof: hs.inter ht.compl

中文:
定理 IsClopen.diff
  条件: (hs : IsClopen s) (ht : IsClopen t)
  结论: IsClopen (s \ t)
  证明: hs.inter ht.compl

Depends on / 依赖: hs.inter, ht.compl
-/
theorem IsClopen.diff (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s \ t) :=
  hs.inter ht.compl

/--
lemma `IsClopen.himp` / 引理 `IsClopen.himp`

English:
lemma IsClopen.himp
  given: (hs : IsClopen s) (ht : IsClopen t)
  statement: IsClopen (s ⇨ t)
  proof: by
  simpa [himp_eq] using ht.union hs.compl

中文:
引理 IsClopen.himp
  条件: (hs : IsClopen s) (ht : IsClopen t)
  结论: IsClopen (s ⇨ t)
  证明: by
  simpa [himp_eq] using ht.union hs.compl

Depends on / 依赖: himp_eq, hs.compl, ht.union
-/
lemma IsClopen.himp (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ⇨ t) := by
  simpa [himp_eq] using ht.union hs.compl

/--
theorem `IsClopen.prod` / 定理 `IsClopen.prod`

English:
theorem IsClopen.prod
  given: {t : Set Y} (hs : IsClopen s) (ht : IsClopen t)
  statement: IsClopen (s ×ˢ t)
  proof: ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩

中文:
定理 IsClopen.乘积
  条件: {t : 集合 Y} (hs : IsClopen s) (ht : IsClopen t)
  结论: IsClopen (s ×ˢ t)
  证明: ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩
-/
theorem IsClopen.prod {t : Set Y} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ×ˢ t) :=
  ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩

/--
theorem `isClopen_iUnion_of_finite` / 定理 `isClopen_iUnion_of_finite`

English:
theorem isClopen_iUnion_of_finite
  given: {Y} [Finite Y] {s : Y -> Set X} (h : forall i, IsClopen (s i))
  proof: ⟨isClosed_iUnion_of_finite (forall_and.1 h).1, isOpen_iUnion (forall_and.1 h).2⟩

中文:
定理 isClopen_iUnion_of_finite
  条件: {Y} [有限 Y] {s : Y -> 集合 X} (h : 对任意 i, IsClopen (s i))
  证明: ⟨isClosed_iUnion_of_finite (forall_and.1 h).1, isOpen_iUnion (forall_and.1 h).2⟩

Depends on / 依赖: forall_and, isClosed_iUnion_of_finite, isOpen_iUnion
-/
theorem isClopen_iUnion_of_finite {Y} [Finite Y] {s : Y -> Set X} (h : forall i, IsClopen (s i)) :
    IsClopen (⋃ i, s i) :=
  ⟨isClosed_iUnion_of_finite (forall_and.1 h).1, isOpen_iUnion (forall_and.1 h).2⟩

/--
theorem `Set.Finite.isClopen_biUnion` / 定理 `Set.Finite.isClopen_biUnion`

English:
theorem Set.Finite.isClopen_biUnion
  statement: {Y} {s : Set Y} {f : Y -> Set X} (hs : s.Finite)
  proof: ⟨hs.isClosed_biUnion fun i hi => (h i hi).1, isOpen_biUnion fun i hi => (h i hi).2⟩

中文:
定理 集合.有限.isClopen_biUnion
  结论: {Y} {s : 集合 Y} {f : Y -> 集合 X} (hs : s.有限)
  证明: ⟨hs.isClosed_biUnion fun i hi => (h i hi).1, isOpen_biUnion fun i hi => (h i hi).2⟩

Depends on / 依赖: hs.isClosed_biUnion, isClosed_biUnion, isOpen_biUnion
-/
theorem Set.Finite.isClopen_biUnion {Y} {s : Set Y} {f : Y -> Set X} (hs : s.Finite)
    (h : forall i in s, IsClopen <| f i) : IsClopen (⋃ i in s, f i) :=
  ⟨hs.isClosed_biUnion fun i hi => (h i hi).1, isOpen_biUnion fun i hi => (h i hi).2⟩

/--
theorem `isClopen_biUnion_finset` / 定理 `isClopen_biUnion_finset`

English:
theorem isClopen_biUnion_finset
  statement: {Y} {s : Finset Y} {f : Y -> Set X}
  proof: s.finite_toSet.isClopen_biUnion h

中文:
定理 isClopen_biUnion_finset
  结论: {Y} {s : 有限集 Y} {f : Y -> 集合 X}
  证明: s.finite_toSet.isClopen_biUnion h

Depends on / 依赖: finite_toSet, isClopen_biUnion, s.finite_toSet.isClopen_biUnion
-/
theorem isClopen_biUnion_finset {Y} {s : Finset Y} {f : Y -> Set X}
    (h : forall i in s, IsClopen <| f i) : IsClopen (⋃ i in s, f i) :=
  s.finite_toSet.isClopen_biUnion h

/--
theorem `isClopen_iInter_of_finite` / 定理 `isClopen_iInter_of_finite`

English:
theorem isClopen_iInter_of_finite
  given: {Y} [Finite Y] {s : Y -> Set X} (h : forall i, IsClopen (s i))
  proof: ⟨isClosed_iInter (forall_and.1 h).1, isOpen_iInter_of_finite (forall_and.1 h).2⟩

中文:
定理 isClopen_i整数er_of_finite
  条件: {Y} [有限 Y] {s : Y -> 集合 X} (h : 对任意 i, IsClopen (s i))
  证明: ⟨isClosed_iInter (forall_and.1 h).1, isOpen_iInter_of_finite (forall_and.1 h).2⟩

Depends on / 依赖: forall_and, isClosed_iInter, isOpen_iInter_of_finite
-/
theorem isClopen_iInter_of_finite {Y} [Finite Y] {s : Y -> Set X} (h : forall i, IsClopen (s i)) :
    IsClopen (⋂ i, s i) :=
  ⟨isClosed_iInter (forall_and.1 h).1, isOpen_iInter_of_finite (forall_and.1 h).2⟩

/--
theorem `Set.Finite.isClopen_biInter` / 定理 `Set.Finite.isClopen_biInter`

English:
theorem Set.Finite.isClopen_biInter
  statement: {Y} {s : Set Y} (hs : s.Finite) {f : Y -> Set X}
  proof: ⟨isClosed_biInter fun i hi => (h i hi).1, hs.isOpen_biInter fun i hi => (h i hi).2⟩

中文:
定理 集合.有限.isClopen_bi整数er
  结论: {Y} {s : 集合 Y} (hs : s.有限) {f : Y -> 集合 X}
  证明: ⟨isClosed_biInter fun i hi => (h i hi).1, hs.isOpen_biInter fun i hi => (h i hi).2⟩

Depends on / 依赖: hs.isOpen_biInter, isClosed_biInter, isOpen_biInter
-/
theorem Set.Finite.isClopen_biInter {Y} {s : Set Y} (hs : s.Finite) {f : Y -> Set X}
    (h : forall i in s, IsClopen (f i)) : IsClopen (⋂ i in s, f i) :=
  ⟨isClosed_biInter fun i hi => (h i hi).1, hs.isOpen_biInter fun i hi => (h i hi).2⟩

/--
theorem `isClopen_biInter_finset` / 定理 `isClopen_biInter_finset`

English:
theorem isClopen_biInter_finset
  statement: {Y} {s : Finset Y} {f : Y -> Set X}
  proof: s.finite_toSet.isClopen_biInter h

中文:
定理 isClopen_bi整数er_finset
  结论: {Y} {s : 有限集 Y} {f : Y -> 集合 X}
  证明: s.finite_toSet.isClopen_biInter h

Depends on / 依赖: finite_toSet, isClopen_biInter, s.finite_toSet.isClopen_biInter
-/
theorem isClopen_biInter_finset {Y} {s : Finset Y} {f : Y -> Set X}
    (h : forall i in s, IsClopen (f i)) : IsClopen (⋂ i in s, f i) :=
  s.finite_toSet.isClopen_biInter h

/--
theorem `IsClopen.preimage` / 定理 `IsClopen.preimage`

English:
theorem IsClopen.preimage
  given: {s : Set Y} (h : IsClopen s) {f : X -> Y} (hf : Continuous f)
  proof: ⟨h.1.preimage hf, h.2.preimage hf⟩

中文:
定理 IsClopen.原像
  条件: {s : 集合 Y} (h : IsClopen s) {f : X -> Y} (hf : 连续 f)
  证明: ⟨h.1.preimage hf, h.2.preimage hf⟩

Depends on / 依赖: preimage
-/
theorem IsClopen.preimage {s : Set Y} (h : IsClopen s) {f : X -> Y} (hf : Continuous f) :
    IsClopen (f ⁻¹' s) :=
  ⟨h.1.preimage hf, h.2.preimage hf⟩

/--
theorem `ContinuousOn.preimage_isClopen_of_isClopen` / 定理 `ContinuousOn.preimage_isClopen_of_isClopen`

English:
theorem ContinuousOn.preimage_isClopen_of_isClopen
  statement: {f : X -> Y} {s : Set X} {t : Set Y}
  proof: ⟨ContinuousOn.preimage_isClosed_of_isClosed hf hs.1 ht.1,
    ContinuousOn.isOpen_inter_preimage hf hs.2 ht.2⟩

中文:
定理 ContinuousOn.preimage_isClopen_of_isClopen
  结论: {f : X -> Y} {s : 集合 X} {t : 集合 Y}
  证明: ⟨ContinuousOn.preimage_isClosed_of_isClosed hf hs.1 ht.1,
    ContinuousOn.isOpen_inter_preimage hf hs.2 ht.2⟩

Depends on / 依赖: ContinuousOn, ContinuousOn.isOpen_inter_preimage, ContinuousOn.preimage_isClosed_of_isClosed, isOpen_inter_preimage, preimage_isClosed_of_isClosed
-/
theorem ContinuousOn.preimage_isClopen_of_isClopen {f : X -> Y} {s : Set X} {t : Set Y}
    (hf : ContinuousOn f s) (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s inter f ⁻¹' t) :=
  ⟨ContinuousOn.preimage_isClosed_of_isClosed hf hs.1 ht.1,
    ContinuousOn.isOpen_inter_preimage hf hs.2 ht.2⟩

/--
theorem `isClopen_inter_of_disjoint_cover_clopen` / 定理 `isClopen_inter_of_disjoint_cover_clopen`

English:
theorem isClopen_inter_of_disjoint_cover_clopen
  statement: {s a b : Set X} (h : IsClopen s) (cover : s subseteq a union b)
  proof: by
  refine ⟨?_, IsOpen.inter h.2 ha⟩
  have : IsClosed (s inter bᶜ) := IsClosed.inter h.1 (isClosed_compl_iff.2 hb)
  convert! this using 1
  refine (inter_subset_inter_right s hab.subset_compl_right).antisymm ?_
  rintro x ⟨hx₁, hx₂⟩
  exact ⟨hx₁, by simpa [notMem_of_mem_compl hx₂] using cover hx₁⟩

中文:
定理 isClopen_inter_of_disjoint_cover_clopen
  结论: {s a b : 集合 X} (h : IsClopen s) (cover : s subseteq a union b)
  证明: by
  refine ⟨?_, IsOpen.inter h.2 ha⟩
  have : IsClosed (s inter bᶜ) := IsClosed.inter h.1 (isClosed_compl_iff.2 hb)
  convert! this using 1
  refine (inter_subset_inter_right s hab.subset_compl_right).antisymm ?_
  rintro x ⟨hx₁, hx₂⟩
  exact ⟨hx₁, by simpa [notMem_of_mem_compl hx₂] using cover hx₁⟩

Depends on / 依赖: IsClosed, IsClosed.inter, IsOpen, IsOpen.inter, antisymm, convert, hab.subset_compl_right, inter_subset_inter_right, isClosed_compl_iff, notMem_of_mem_compl, subset_compl_right
-/
theorem isClopen_inter_of_disjoint_cover_clopen {s a b : Set X} (h : IsClopen s) (cover : s subseteq a union b)
    (ha : IsOpen a) (hb : IsOpen b) (hab : Disjoint a b) : IsClopen (s inter a) := by
  refine ⟨?_, IsOpen.inter h.2 ha⟩
  have : IsClosed (s inter bᶜ) := IsClosed.inter h.1 (isClosed_compl_iff.2 hb)
  convert! this using 1
  refine (inter_subset_inter_right s hab.subset_compl_right).antisymm ?_
  rintro x ⟨hx₁, hx₂⟩
  exact ⟨hx₁, by simpa [notMem_of_mem_compl hx₂] using cover hx₁⟩

/--
lemma `isClopen_inter_of_disjoint_cover_clopen'` / 引理 `isClopen_inter_of_disjoint_cover_clopen'`

English:
lemma isClopen_inter_of_disjoint_cover_clopen'
  statement: {s a b : Set X} (h : IsClopen s) (cover : s subseteq a union b)
  proof: by
  rw [show s inter a = s inter (s inter a) by simp]
  refine isClopen_inter_of_disjoint_cover_clopen h ?_ (h.2.inter ha) (h.2.inter hb) ?_
  · rw [← inter_union_distrib_left]
    exact subset_inter .rfl cover
  · rw [disjoint_iff_inter_eq_empty, inter_comm s b, ← inter_assoc, hab, empty_inter]

中文:
引理 isClopen_inter_of_disjoint_cover_clopen'
  结论: {s a b : 集合 X} (h : IsClopen s) (cover : s subseteq a union b)
  证明: by
  rw [show s inter a = s inter (s inter a) by simp]
  refine isClopen_inter_of_disjoint_cover_clopen h ?_ (h.2.inter ha) (h.2.inter hb) ?_
  · rw [← inter_union_distrib_left]
    exact subset_inter .rfl cover
  · rw [disjoint_iff_inter_eq_empty, inter_comm s b, ← inter_assoc, hab, empty_inter]

Depends on / 依赖: disjoint_iff_inter_eq_empty, empty_inter, inter_assoc, inter_comm, inter_union_distrib_left, isClopen_inter_of_disjoint_cover_clopen, subset_inter
-/
lemma isClopen_inter_of_disjoint_cover_clopen' {s a b : Set X} (h : IsClopen s) (cover : s subseteq a union b)
    (ha : IsOpen a) (hb : IsOpen b) (hab : s inter a inter b = ∅) : IsClopen (s inter a) := by
  rw [show s inter a = s inter (s inter a) by simp]
  refine isClopen_inter_of_disjoint_cover_clopen h ?_ (h.2.inter ha) (h.2.inter hb) ?_
  · rw [← inter_union_distrib_left]
    exact subset_inter .rfl cover
  · rw [disjoint_iff_inter_eq_empty, inter_comm s b, ← inter_assoc, hab, empty_inter]

/--
theorem `isClopen_of_disjoint_cover_open` / 定理 `isClopen_of_disjoint_cover_open`

English:
theorem isClopen_of_disjoint_cover_open
  statement: {a b : Set X} (cover : univ subseteq a union b)
  proof: univ_inter a ▸ isClopen_inter_of_disjoint_cover_clopen isClopen_univ cover ha hb hab

@[simp]

中文:
定理 isClopen_of_disjoint_cover_open
  结论: {a b : 集合 X} (cover : univ subseteq a union b)
  证明: univ_inter a ▸ isClopen_inter_of_disjoint_cover_clopen isClopen_univ cover ha hb hab

@[simp]

Depends on / 依赖: isClopen_inter_of_disjoint_cover_clopen, isClopen_univ, univ_inter
-/
theorem isClopen_of_disjoint_cover_open {a b : Set X} (cover : univ subseteq a union b)
    (ha : IsOpen a) (hb : IsOpen b) (hab : Disjoint a b) : IsClopen a :=
  univ_inter a ▸ isClopen_inter_of_disjoint_cover_clopen isClopen_univ cover ha hb hab

@[simp]
/--
theorem `isClopen_discrete` / 定理 `isClopen_discrete`

English:
theorem isClopen_discrete
  given: [DiscreteTopology X] (s : Set X)
  statement: IsClopen s
  proof: ⟨isClosed_discrete _, isOpen_discrete _⟩

中文:
定理 isClopen_discrete
  条件: [离散拓扑 X] (s : 集合 X)
  结论: IsClopen s
  证明: ⟨isClosed_discrete _, isOpen_discrete _⟩

Depends on / 依赖: isClosed_discrete, isOpen_discrete
-/
theorem isClopen_discrete [DiscreteTopology X] (s : Set X) : IsClopen s :=
  ⟨isClosed_discrete _, isOpen_discrete _⟩

/--
theorem `isClopen_range_inl` / 定理 `isClopen_range_inl`

English:
theorem isClopen_range_inl
  statement: IsClopen (range (Sum.inl : X -> X oplus Y))
  proof: ⟨isClosed_range_inl, isOpen_range_inl⟩

中文:
定理 isClopen_range_inl
  结论: IsClopen (range (和.inl : X -> X oplus Y))
  证明: ⟨isClosed_range_inl, isOpen_range_inl⟩

Depends on / 依赖: isClosed_range_inl, isOpen_range_inl
-/
theorem isClopen_range_inl : IsClopen (range (Sum.inl : X -> X oplus Y)) :=
  ⟨isClosed_range_inl, isOpen_range_inl⟩

/--
theorem `isClopen_range_inr` / 定理 `isClopen_range_inr`

English:
theorem isClopen_range_inr
  statement: IsClopen (range (Sum.inr : Y -> X oplus Y))
  proof: ⟨isClosed_range_inr, isOpen_range_inr⟩

中文:
定理 isClopen_range_inr
  结论: IsClopen (range (和.inr : Y -> X oplus Y))
  证明: ⟨isClosed_range_inr, isOpen_range_inr⟩

Depends on / 依赖: isClosed_range_inr, isOpen_range_inr
-/
theorem isClopen_range_inr : IsClopen (range (Sum.inr : Y -> X oplus Y)) :=
  ⟨isClosed_range_inr, isOpen_range_inr⟩

/--
theorem `isClopen_range_sigmaMk` / 定理 `isClopen_range_sigmaMk`

English:
theorem isClopen_range_sigmaMk
  given: {X : ι -> Type*} [forall i, TopologicalSpace (X i)] {i : ι}
  proof: ⟨IsClosedEmbedding.sigmaMk.isClosed_range, IsOpenEmbedding.sigmaMk.isOpen_range⟩

中文:
定理 isClopen_range_sigmaMk
  条件: {X : ι -> 类型} [对任意 i, 拓扑空间 (X i)] {i : ι}
  证明: ⟨IsClosedEmbedding.sigmaMk.isClosed_range, IsOpenEmbedding.sigmaMk.isOpen_range⟩

Depends on / 依赖: IsClosedEmbedding, IsClosedEmbedding.sigmaMk.isClosed_range, IsOpenEmbedding, IsOpenEmbedding.sigmaMk.isOpen_range, isClosed_range, isOpen_range, sigmaMk
-/
theorem isClopen_range_sigmaMk {X : ι -> Type*} [forall i, TopologicalSpace (X i)] {i : ι} :
    IsClopen (Set.range (@Sigma.mk ι X i)) :=
  ⟨IsClosedEmbedding.sigmaMk.isClosed_range, IsOpenEmbedding.sigmaMk.isOpen_range⟩

/--
theorem `Topology.IsQuotientMap.isClopen_preimage` / 定理 `Topology.IsQuotientMap.isClopen_preimage`

English:
theorem Topology.IsQuotientMap.isClopen_preimage
  statement: {f : X -> Y} (hf : IsQuotientMap f)
  proof: and_congr hf.isClosed_preimage hf.isOpen_preimage

中文:
定理 拓扑.是商映射.isClopen_preimage
  结论: {f : X -> Y} (hf : 是商映射 f)
  证明: and_congr hf.isClosed_preimage hf.isOpen_preimage
-/
protected theorem Topology.IsQuotientMap.isClopen_preimage {f : X -> Y} (hf : IsQuotientMap f)
    {s : Set Y} : IsClopen (f ⁻¹' s) ↔ IsClopen s :=
  and_congr hf.isClosed_preimage hf.isOpen_preimage

/--
theorem `continuous_boolIndicator_iff_isClopen` / 定理 `continuous_boolIndicator_iff_isClopen`

English:
theorem continuous_boolIndicator_iff_isClopen
  given: (U : Set X)
  proof: by
  rw [continuous_bool_rng true]; rw [preimage_boolIndicator_true]

中文:
定理 continuous_boolIndicator_iff_isClopen
  条件: (U : 集合 X)
  证明: by
  rw [continuous_bool_rng true]; rw [preimage_boolIndicator_true]

Depends on / 依赖: continuous_bool_rng, preimage_boolIndicator_true
-/
theorem continuous_boolIndicator_iff_isClopen (U : Set X) :
    Continuous U.boolIndicator ↔ IsClopen U := by
  rw [continuous_bool_rng true]; rw [preimage_boolIndicator_true]

/--
theorem `continuousOn_boolIndicator_iff_isClopen` / 定理 `continuousOn_boolIndicator_iff_isClopen`

English:
theorem continuousOn_boolIndicator_iff_isClopen
  given: (s U : Set X)
  proof: by
  rw [continuousOn_iff_continuous_domRestrict]; rw [← continuous_boolIndicator_iff_isClopen]
  rfl

中文:
定理 continuousOn_boolIndicator_iff_isClopen
  条件: (s U : 集合 X)
  证明: by
  rw [continuousOn_iff_continuous_domRestrict]; rw [← continuous_boolIndicator_iff_isClopen]
  rfl

Depends on / 依赖: continuousOn_iff_continuous_domRestrict, continuous_boolIndicator_iff_isClopen
-/
theorem continuousOn_boolIndicator_iff_isClopen (s U : Set X) :
    ContinuousOn U.boolIndicator s ↔ IsClopen (((↑) : s -> X) ⁻¹' U) := by
  rw [continuousOn_iff_continuous_domRestrict]; rw [← continuous_boolIndicator_iff_isClopen]
  rfl

end Clopen
