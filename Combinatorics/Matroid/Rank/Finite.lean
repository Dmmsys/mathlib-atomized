/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Closure

/-!
# Finite-rank sets

`Matroid.IsRkFinite M X` means that every basis of the set `X` in the matroid `M` is finite,
or equivalently that the restriction of `M` to `X` is `Matroid.RankFinite`.
Sets in a matroid with `IsRkFinite` are the largest class of sets for which one can do nontrivial
integer arithmetic involving the rank function.

## Implementation Details

Unlike most set predicates on matroids, a set `X` with `M.IsRkFinite X` need not satisfy `X ⊆ M.E`,
so may contain junk elements. This seems to be what makes the definition easiest to use.
-/

@[expose] public section

variable {α : Type*} {M : Matroid α} {X Y I : Set α} {e : α}

open Set

namespace Matroid

/--
Definition of `IsRkFinite` / `IsRkFinite` 的定义

English:
definition IsRkFinite
  signature: (M : Matroid α) (X : Set α)
  body: (M ↾ X).RankFinite

中文:
定义 IsRkFinite
  签名: (M : 拟阵 α) (X : 集合 α)
  定义体: (M ↾ X).RankFinite

Depends on / 依赖: RankFinite
-/
def IsRkFinite (M : Matroid α) (X : Set α) : Prop := (M ↾ X).RankFinite

/--
lemma `IsRkFinite.rankFinite` / 引理 `IsRkFinite.rankFinite`

English:
lemma IsRkFinite.rankFinite
  given: (hX : M.IsRkFinite X)
  statement: (M ↾ X).RankFinite
  proof: hX

中文:
引理 IsRkFinite.rankFinite
  条件: (hX : M.IsRkFinite X)
  结论: (M ↾ X).RankFinite
  证明: hX
-/
lemma IsRkFinite.rankFinite (hX : M.IsRkFinite X) : (M ↾ X).RankFinite :=
  hX

/--
lemma `RankFinite.isRkFinite` / 引理 `RankFinite.isRkFinite`

English:
lemma RankFinite.isRkFinite
  given: [RankFinite M] (X : Set α)
  statement: M.IsRkFinite X
  proof: inferInstanceAs (M ↾ X).RankFinite

中文:
引理 RankFinite.isRkFinite
  条件: [RankFinite M] (X : 集合 α)
  结论: M.IsRkFinite X
  证明: inferInstanceAs (M ↾ X).RankFinite
-/
@[simp] lemma RankFinite.isRkFinite [RankFinite M] (X : Set α) : M.IsRkFinite X :=
  inferInstanceAs (M ↾ X).RankFinite

/--
lemma `IsBasis'.finite_iff_isRkFinite` / 引理 `IsBasis'.finite_iff_isRkFinite`

English:
lemma IsBasis'.finite_iff_isRkFinite
  given: (hI : M.IsBasis' I X)
  statement: I.Finite ↔ M.IsRkFinite X
  proof: ⟨fun h => ⟨I, hI, h⟩, fun (_ : (M ↾ X).RankFinite) => hI.isBase_restrict.finite⟩

alias ⟨_, IsBasis'.finite_of_isRkFinite⟩ := IsBasis'.finite_iff_isRkFinite

中文:
引理 是基'.finite_iff_isRkFinite
  条件: (hI : M.是基' I X)
  结论: I.有限 ↔ M.IsRkFinite X
  证明: ⟨fun h => ⟨I, hI, h⟩, fun (_ : (M ↾ X).RankFinite) => hI.isBase_restrict.finite⟩

alias ⟨_, IsBasis'.finite_of_isRkFinite⟩ := IsBasis'.finite_iff_isRkFinite
-/
lemma IsBasis'.finite_iff_isRkFinite (hI : M.IsBasis' I X) : I.Finite ↔ M.IsRkFinite X :=
  ⟨fun h => ⟨I, hI, h⟩, fun (_ : (M ↾ X).RankFinite) => hI.isBase_restrict.finite⟩

alias ⟨_, IsBasis'.finite_of_isRkFinite⟩ := IsBasis'.finite_iff_isRkFinite

/--
lemma `IsBasis.finite_iff_isRkFinite` / 引理 `IsBasis.finite_iff_isRkFinite`

English:
lemma IsBasis.finite_iff_isRkFinite
  given: (hI : M.IsBasis I X)
  statement: I.Finite ↔ M.IsRkFinite X
  proof: hI.isBasis'.finite_iff_isRkFinite

alias ⟨_, IsBasis.finite_of_isRkFinite⟩ := IsBasis.finite_iff_isRkFinite

中文:
引理 是基.finite_iff_isRkFinite
  条件: (hI : M.是基 I X)
  结论: I.有限 ↔ M.IsRkFinite X
  证明: hI.isBasis'.finite_iff_isRkFinite

alias ⟨_, IsBasis.finite_of_isRkFinite⟩ := IsBasis.finite_iff_isRkFinite

Depends on / 依赖: finite_iff_isRkFinite, hI.isBasis, isBasis
-/
lemma IsBasis.finite_iff_isRkFinite (hI : M.IsBasis I X) : I.Finite ↔ M.IsRkFinite X :=
  hI.isBasis'.finite_iff_isRkFinite

alias ⟨_, IsBasis.finite_of_isRkFinite⟩ := IsBasis.finite_iff_isRkFinite

/--
lemma `IsBasis'.isRkFinite_of_finite` / 引理 `IsBasis'.isRkFinite_of_finite`

English:
lemma IsBasis'.isRkFinite_of_finite
  given: (hI : M.IsBasis' I X) (hIfin : I.Finite)
  statement: M.IsRkFinite X
  proof: ⟨I, hI, hIfin⟩

中文:
引理 是基'.isRkFinite_of_finite
  条件: (hI : M.是基' I X) (hIfin : I.有限)
  结论: M.IsRkFinite X
  证明: ⟨I, hI, hIfin⟩
-/
lemma IsBasis'.isRkFinite_of_finite (hI : M.IsBasis' I X) (hIfin : I.Finite) : M.IsRkFinite X :=
  ⟨I, hI, hIfin⟩

/--
lemma `IsBasis.isRkFinite_of_finite` / 引理 `IsBasis.isRkFinite_of_finite`

English:
lemma IsBasis.isRkFinite_of_finite
  given: (hI : M.IsBasis I X) (hIfin : I.Finite)
  statement: M.IsRkFinite X
  proof: ⟨I, hI.isBasis', hIfin⟩

中文:
引理 是基.isRkFinite_of_finite
  条件: (hI : M.是基 I X) (hIfin : I.有限)
  结论: M.IsRkFinite X
  证明: ⟨I, hI.isBasis', hIfin⟩

Depends on / 依赖: hI.isBasis, isBasis
-/
lemma IsBasis.isRkFinite_of_finite (hI : M.IsBasis I X) (hIfin : I.Finite) : M.IsRkFinite X :=
  ⟨I, hI.isBasis', hIfin⟩

/--
lemma `IsRkFinite.finite_of_isBasis'` / 引理 `IsRkFinite.finite_of_isBasis'`

English:
lemma IsRkFinite.finite_of_isBasis'
  given: (h : M.IsRkFinite X) (hI : M.IsBasis' I X)
  statement: I.Finite
  proof: have := h.rankFinite
  (isBase_restrict_iff'.2 hI).finite

中文:
引理 IsRkFinite.finite_of_isBasis'
  条件: (h : M.IsRkFinite X) (hI : M.是基' I X)
  结论: I.有限
  证明: have := h.rankFinite
  (isBase_restrict_iff'.2 hI).finite

Depends on / 依赖: finite, h.rankFinite, isBase_restrict_iff, rankFinite
-/
lemma IsRkFinite.finite_of_isBasis' (h : M.IsRkFinite X) (hI : M.IsBasis' I X) : I.Finite :=
  have := h.rankFinite
  (isBase_restrict_iff'.2 hI).finite

/--
lemma `IsRkFinite.finite_of_isBasis` / 引理 `IsRkFinite.finite_of_isBasis`

English:
lemma IsRkFinite.finite_of_isBasis
  given: (h : M.IsRkFinite X) (hI : M.IsBasis I X)
  statement: I.Finite
  proof: h.finite_of_isBasis' hI.isBasis'

中文:
引理 IsRkFinite.finite_of_isBasis
  条件: (h : M.IsRkFinite X) (hI : M.是基 I X)
  结论: I.有限
  证明: h.finite_of_isBasis' hI.isBasis'

Depends on / 依赖: finite_of_isBasis, h.finite_of_isBasis, hI.isBasis, isBasis
-/
lemma IsRkFinite.finite_of_isBasis (h : M.IsRkFinite X) (hI : M.IsBasis I X) : I.Finite :=
  h.finite_of_isBasis' hI.isBasis'

/--
lemma `IsRkFinite.exists_finite_isBasis'` / 引理 `IsRkFinite.exists_finite_isBasis'`

English:
lemma IsRkFinite.exists_finite_isBasis'
  given: (h : M.IsRkFinite X)
  statement: exists I, M.IsBasis' I X ∧ I.Finite
  proof: h.exists_finite_isBase

中文:
引理 IsRkFinite.存在_finite_isBasis'
  条件: (h : M.IsRkFinite X)
  结论: 存在 I, M.是基' I X ∧ I.有限
  证明: h.exists_finite_isBase

Depends on / 依赖: exists_finite_isBase, h.exists_finite_isBase
-/
lemma IsRkFinite.exists_finite_isBasis' (h : M.IsRkFinite X) : exists I, M.IsBasis' I X ∧ I.Finite :=
  h.exists_finite_isBase

/--
lemma `IsRkFinite.exists_finset_isBasis'` / 引理 `IsRkFinite.exists_finset_isBasis'`

English:
lemma IsRkFinite.exists_finset_isBasis'
  given: (h : M.IsRkFinite X)
  statement: exists (I : Finset α), M.IsBasis' I X
  proof: let ⟨I, hI, hIfin⟩ := h.exists_finite_isBasis'
  ⟨hIfin.toFinset, by simpa⟩

中文:
引理 IsRkFinite.存在_finset_isBasis'
  条件: (h : M.IsRkFinite X)
  结论: 存在 (I : 有限集 α), M.是基' I X
  证明: let ⟨I, hI, hIfin⟩ := h.exists_finite_isBasis'
  ⟨hIfin.toFinset, by simpa⟩

Depends on / 依赖: exists_finite_isBasis, h.exists_finite_isBasis, hIfin.toFinset, toFinset
-/
lemma IsRkFinite.exists_finset_isBasis' (h : M.IsRkFinite X) : exists (I : Finset α), M.IsBasis' I X :=
  let ⟨I, hI, hIfin⟩ := h.exists_finite_isBasis'
  ⟨hIfin.toFinset, by simpa⟩

/--
lemma `isRkFinite_iff_exists_isBasis'` / 引理 `isRkFinite_iff_exists_isBasis'`

English:
lemma isRkFinite_iff_exists_isBasis'
  statement: M.IsRkFinite X ↔ exists I, M.IsBasis' I X ∧ I.Finite
  proof: ⟨IsRkFinite.exists_finite_isBasis', fun ⟨_, hIX, hI⟩ => hIX.isRkFinite_of_finite hI⟩

中文:
引理 isRkFinite_iff_存在_isBasis'
  结论: M.IsRkFinite X ↔ 存在 I, M.是基' I X ∧ I.有限
  证明: ⟨IsRkFinite.exists_finite_isBasis', fun ⟨_, hIX, hI⟩ => hIX.isRkFinite_of_finite hI⟩

Depends on / 依赖: IsRkFinite, IsRkFinite.exists_finite_isBasis, exists_finite_isBasis, hIX.isRkFinite_of_finite, isRkFinite_of_finite
-/
lemma isRkFinite_iff_exists_isBasis' : M.IsRkFinite X ↔ exists I, M.IsBasis' I X ∧ I.Finite :=
  ⟨IsRkFinite.exists_finite_isBasis', fun ⟨_, hIX, hI⟩ => hIX.isRkFinite_of_finite hI⟩

/--
lemma `IsRkFinite.subset` / 引理 `IsRkFinite.subset`

English:
lemma IsRkFinite.subset
  given: (h : M.IsRkFinite X) (hXY : Y subseteq X)
  statement: M.IsRkFinite Y
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' Y
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
exact hI.isRkFinite_of_finite (hJ.finite_of_isRkFinite h).subset hIJ

@[simp]

中文:
引理 IsRkFinite.subset
  条件: (h : M.IsRkFinite X) (hXY : Y subseteq X)
  结论: M.IsRkFinite Y
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' Y
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
exact hI.isRkFinite_of_finite (hJ.finite_of_isRkFinite h).subset hIJ

@[simp]

Depends on / 依赖: M.exists_isBasis, _of_subset, exists_isBasis, finite_of_isRkFinite, hI.indep.subset_isBasis, hI.isRkFinite_of_finite, hI.subset.trans, hJ.finite_of_isRkFinite, isRkFinite_of_finite, subset, subset_isBasis
-/
lemma IsRkFinite.subset (h : M.IsRkFinite X) (hXY : Y subseteq X) : M.IsRkFinite Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' Y
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
exact hI.isRkFinite_of_finite (hJ.finite_of_isRkFinite h).subset hIJ

@[simp]
/--
lemma `isRkFinite_inter_ground_iff` / 引理 `isRkFinite_inter_ground_iff`

English:
lemma isRkFinite_inter_ground_iff
  statement: M.IsRkFinite (X inter M.E) ↔ M.IsRkFinite X
  proof: let ⟨_I, hI⟩ := M.exists_isBasis' X
  ⟨fun h => hI.isRkFinite_of_finite (hI.isBasis_inter_ground.finite_of_isRkFinite h),
    fun h => h.subset inter_subset_left⟩

中文:
引理 isRkFinite_inter_ground_iff
  结论: M.IsRkFinite (X inter M.E) ↔ M.IsRkFinite X
  证明: let ⟨_I, hI⟩ := M.exists_isBasis' X
  ⟨fun h => hI.isRkFinite_of_finite (hI.isBasis_inter_ground.finite_of_isRkFinite h),
    fun h => h.subset inter_subset_left⟩

Depends on / 依赖: M.exists_isBasis, exists_isBasis, finite_of_isRkFinite, h.subset, hI.isBasis_inter_ground.finite_of_isRkFinite, hI.isRkFinite_of_finite, inter_subset_left, isBasis_inter_ground, isRkFinite_of_finite, subset
-/
lemma isRkFinite_inter_ground_iff : M.IsRkFinite (X inter M.E) ↔ M.IsRkFinite X :=
  let ⟨_I, hI⟩ := M.exists_isBasis' X
  ⟨fun h => hI.isRkFinite_of_finite (hI.isBasis_inter_ground.finite_of_isRkFinite h),
    fun h => h.subset inter_subset_left⟩

/--
lemma `IsRkFinite.inter_ground` / 引理 `IsRkFinite.inter_ground`

English:
lemma IsRkFinite.inter_ground
  given: (h : M.IsRkFinite X)
  statement: M.IsRkFinite (X inter M.E)
  proof: isRkFinite_inter_ground_iff.2 h

中文:
引理 IsRkFinite.inter_ground
  条件: (h : M.IsRkFinite X)
  结论: M.IsRkFinite (X inter M.E)
  证明: isRkFinite_inter_ground_iff.2 h

Depends on / 依赖: isRkFinite_inter_ground_iff
-/
lemma IsRkFinite.inter_ground (h : M.IsRkFinite X) : M.IsRkFinite (X inter M.E) :=
  isRkFinite_inter_ground_iff.2 h

/--
lemma `isRkFinite_iff` / 引理 `isRkFinite_iff`

English:
lemma isRkFinite_iff
  given: (hX : X subseteq M.E := by aesop_mat)
  proof: by
  simp_rw [isRkFinite_iff_exists_isBasis', M.isBasis'_iff_isBasis hX]

中文:
引理 isRkFinite_iff
  条件: (hX : X subseteq M.E := by aesop_mat)
  证明: by
  simp_rw [isRkFinite_iff_exists_isBasis', M.isBasis'_iff_isBasis hX]

Depends on / 依赖: Finite, I.Finite, IsBasis, IsRkFinite, M.IsBasis, M.IsRkFinite, M.isBasis, _iff_isBasis, aesop_mat, isBasis, isRkFinite_iff_exists_isBasis, simp_rw
-/
lemma isRkFinite_iff (hX : X subseteq M.E := by aesop_mat) :
    M.IsRkFinite X ↔ exists I, M.IsBasis I X ∧ I.Finite := by
  simp_rw [isRkFinite_iff_exists_isBasis', M.isBasis'_iff_isBasis hX]

/--
lemma `Indep.isRkFinite_iff_finite` / 引理 `Indep.isRkFinite_iff_finite`

English:
lemma Indep.isRkFinite_iff_finite
  given: (hI : M.Indep I)
  statement: M.IsRkFinite I ↔ I.Finite
  proof: hI.isBasis_self.finite_iff_isRkFinite.symm

alias ⟨Indep.finite_of_isRkFinite, _⟩ := Indep.isRkFinite_iff_finite

@[simp]

中文:
引理 Indep.isRkFinite_iff_finite
  条件: (hI : M.Indep I)
  结论: M.IsRkFinite I ↔ I.有限
  证明: hI.isBasis_self.finite_iff_isRkFinite.symm

alias ⟨Indep.finite_of_isRkFinite, _⟩ := Indep.isRkFinite_iff_finite

@[simp]

Depends on / 依赖: finite_iff_isRkFinite, hI.isBasis_self.finite_iff_isRkFinite.symm, isBasis_self
-/
lemma Indep.isRkFinite_iff_finite (hI : M.Indep I) : M.IsRkFinite I ↔ I.Finite :=
  hI.isBasis_self.finite_iff_isRkFinite.symm

alias ⟨Indep.finite_of_isRkFinite, _⟩ := Indep.isRkFinite_iff_finite

@[simp]
/--
lemma `isRkFinite_of_finite` / 引理 `isRkFinite_of_finite`

English:
lemma isRkFinite_of_finite
  given: (M : Matroid α) (hX : X.Finite)
  statement: M.IsRkFinite X
  proof: let ⟨_, hI⟩ := M.exists_isBasis' X
  hI.isRkFinite_of_finite (hX.subset hI.subset)

中文:
引理 isRkFinite_of_finite
  条件: (M : 拟阵 α) (hX : X.有限)
  结论: M.IsRkFinite X
  证明: let ⟨_, hI⟩ := M.exists_isBasis' X
  hI.isRkFinite_of_finite (hX.subset hI.subset)

Depends on / 依赖: M.exists_isBasis, exists_isBasis, hI.isRkFinite_of_finite, hI.subset, hX.subset, isRkFinite_of_finite, subset
-/
lemma isRkFinite_of_finite (M : Matroid α) (hX : X.Finite) : M.IsRkFinite X :=
  let ⟨_, hI⟩ := M.exists_isBasis' X
  hI.isRkFinite_of_finite (hX.subset hI.subset)

/--
lemma `Indep.subset_finite_isBasis'_of_subset_of_isRkFinite` / 引理 `Indep.subset_finite_isBasis'_of_subset_of_isRkFinite`

English:
lemma Indep.subset_finite_isBasis'_of_subset_of_isRkFinite
  statement: (hI : M.Indep I) (hIX : I subseteq X)
  proof: (hI.subset_isBasis'_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_isRkFinite hX⟩

中文:
引理 Indep.subset_finite_isBasis'_of_subset_of_isRkFinite
  结论: (hI : M.Indep I) (hIX : I subseteq X)
  证明: (hI.subset_isBasis'_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_isRkFinite hX⟩

Depends on / 依赖: _of_subset, finite_of_isRkFinite, hI.subset_isBasis, subset_isBasis
-/
lemma Indep.subset_finite_isBasis'_of_subset_of_isRkFinite (hI : M.Indep I) (hIX : I subseteq X)
    (hX : M.IsRkFinite X) : exists J, M.IsBasis' J X ∧ I subseteq J ∧ J.Finite :=
  (hI.subset_isBasis'_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_isRkFinite hX⟩

/--
lemma `Indep.subset_finite_isBasis_of_subset_of_isRkFinite` / 引理 `Indep.subset_finite_isBasis_of_subset_of_isRkFinite`

English:
lemma Indep.subset_finite_isBasis_of_subset_of_isRkFinite
  statement: (hI : M.Indep I) (hIX : I subseteq X)
  proof: (hI.subset_isBasis_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_isRkFinite hX⟩

中文:
引理 Indep.subset_finite_isBasis_of_subset_of_isRkFinite
  结论: (hI : M.Indep I) (hIX : I subseteq X)
  证明: (hI.subset_isBasis_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_isRkFinite hX⟩

Depends on / 依赖: Finite, IsBasis, J.Finite, M.IsBasis, aesop_mat, finite_of_isRkFinite, hI.subset_isBasis_of_subset, subset_isBasis_of_subset, subseteq
-/
lemma Indep.subset_finite_isBasis_of_subset_of_isRkFinite (hI : M.Indep I) (hIX : I subseteq X)
    (hX : M.IsRkFinite X) (hXE : X subseteq M.E := by aesop_mat) : exists J, M.IsBasis J X ∧ I subseteq J ∧ J.Finite :=
  (hI.subset_isBasis_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_isRkFinite hX⟩

/--
lemma `isRkFinite_singleton` / 引理 `isRkFinite_singleton`

English:
lemma isRkFinite_singleton
  statement: M.IsRkFinite {e}
  proof: by
  simp

中文:
引理 isRkFinite_singleton
  结论: M.IsRkFinite {e}
  证明: by
  simp
-/
lemma isRkFinite_singleton : M.IsRkFinite {e} := by
  simp

/--
lemma `IsRkFinite.empty` / 引理 `IsRkFinite.empty`

English:
lemma IsRkFinite.empty
  given: (M : Matroid α)
  statement: M.IsRkFinite ∅
  proof: isRkFinite_of_finite M finite_empty

中文:
引理 IsRkFinite.empty
  条件: (M : 拟阵 α)
  结论: M.IsRkFinite ∅
  证明: isRkFinite_of_finite M finite_empty

Depends on / 依赖: finite_empty, isRkFinite_of_finite
-/
lemma IsRkFinite.empty (M : Matroid α) : M.IsRkFinite ∅ :=
  isRkFinite_of_finite M finite_empty

/--
lemma `IsRkFinite.finite_of_indep_subset` / 引理 `IsRkFinite.finite_of_indep_subset`

English:
lemma IsRkFinite.finite_of_indep_subset
  given: (hX : M.IsRkFinite X) (hI : M.Indep I) (hIX : I subseteq X)
  proof: hI.finite_of_isRkFinite hX.subset hIX

@[simp]

中文:
引理 IsRkFinite.finite_of_indep_subset
  条件: (hX : M.IsRkFinite X) (hI : M.Indep I) (hIX : I subseteq X)
  证明: hI.finite_of_isRkFinite hX.subset hIX

@[simp]

Depends on / 依赖: finite_of_isRkFinite, hI.finite_of_isRkFinite, hX.subset, subset
-/
lemma IsRkFinite.finite_of_indep_subset (hX : M.IsRkFinite X) (hI : M.Indep I) (hIX : I subseteq X) :
    I.Finite :=
hI.finite_of_isRkFinite hX.subset hIX

@[simp]
/--
lemma `isRkFinite_ground_iff_rankFinite` / 引理 `isRkFinite_ground_iff_rankFinite`

English:
lemma isRkFinite_ground_iff_rankFinite
  statement: M.IsRkFinite M.E ↔ M.RankFinite
  proof: by
  rw [IsRkFinite]; rw [restrict_ground_eq_self]

中文:
引理 isRkFinite_ground_iff_rankFinite
  结论: M.IsRkFinite M.E ↔ M.RankFinite
  证明: by
  rw [IsRkFinite]; rw [restrict_ground_eq_self]

Depends on / 依赖: IsRkFinite, restrict_ground_eq_self
-/
lemma isRkFinite_ground_iff_rankFinite : M.IsRkFinite M.E ↔ M.RankFinite := by
  rw [IsRkFinite]; rw [restrict_ground_eq_self]

/--
lemma `isRkFinite_ground` / 引理 `isRkFinite_ground`

English:
lemma isRkFinite_ground
  given: (M : Matroid α) [RankFinite M]
  statement: M.IsRkFinite M.E
  proof: by
  rwa [isRkFinite_ground_iff_rankFinite]

中文:
引理 isRkFinite_ground
  条件: (M : 拟阵 α) [RankFinite M]
  结论: M.IsRkFinite M.E
  证明: by
  rwa [isRkFinite_ground_iff_rankFinite]

Depends on / 依赖: isRkFinite_ground_iff_rankFinite
-/
lemma isRkFinite_ground (M : Matroid α) [RankFinite M] : M.IsRkFinite M.E := by
  rwa [isRkFinite_ground_iff_rankFinite]

/--
lemma `Indep.finite_of_subset_isRkFinite` / 引理 `Indep.finite_of_subset_isRkFinite`

English:
lemma Indep.finite_of_subset_isRkFinite
  given: (hI : M.Indep I) (hIX : I subseteq X) (hX : M.IsRkFinite X)
  proof: hX.finite_of_indep_subset hI hIX

中文:
引理 Indep.finite_of_subset_isRkFinite
  条件: (hI : M.Indep I) (hIX : I subseteq X) (hX : M.IsRkFinite X)
  证明: hX.finite_of_indep_subset hI hIX

Depends on / 依赖: finite_of_indep_subset, hX.finite_of_indep_subset
-/
lemma Indep.finite_of_subset_isRkFinite (hI : M.Indep I) (hIX : I subseteq X) (hX : M.IsRkFinite X) :
    I.Finite :=
  hX.finite_of_indep_subset hI hIX

/--
lemma `IsRkFinite.closure` / 引理 `IsRkFinite.closure`

English:
lemma IsRkFinite.closure
  given: (h : M.IsRkFinite X)
  statement: M.IsRkFinite (M.closure X)
  proof: let ⟨_, hI⟩ := M.exists_isBasis' X
hI.isBasis_closure_right.isRkFinite_of_finite hI.finite_of_isRkFinite h

@[simp]

中文:
引理 IsRkFinite.closure
  条件: (h : M.IsRkFinite X)
  结论: M.IsRkFinite (M.closure X)
  证明: let ⟨_, hI⟩ := M.exists_isBasis' X
hI.isBasis_closure_right.isRkFinite_of_finite hI.finite_of_isRkFinite h

@[simp]

Depends on / 依赖: M.exists_isBasis, exists_isBasis, finite_of_isRkFinite, hI.finite_of_isRkFinite, hI.isBasis_closure_right.isRkFinite_of_finite, isBasis_closure_right, isRkFinite_of_finite
-/
lemma IsRkFinite.closure (h : M.IsRkFinite X) : M.IsRkFinite (M.closure X) :=
  let ⟨_, hI⟩ := M.exists_isBasis' X
hI.isBasis_closure_right.isRkFinite_of_finite hI.finite_of_isRkFinite h

@[simp]
/--
lemma `isRkFinite_closure_iff` / 引理 `isRkFinite_closure_iff`

English:
lemma isRkFinite_closure_iff
  statement: M.IsRkFinite (M.closure X) ↔ M.IsRkFinite X
  proof: by
  rw [← isRkFinite_inter_ground_iff (X := X)]
exact ⟨fun h => h.subset M.inter_ground_subset_closure X, fun h => by simpa using h.closure⟩

中文:
引理 isRkFinite_closure_iff
  结论: M.IsRkFinite (M.closure X) ↔ M.IsRkFinite X
  证明: by
  rw [← isRkFinite_inter_ground_iff (X := X)]
exact ⟨fun h => h.subset M.inter_ground_subset_closure X, fun h => by simpa using h.closure⟩

Depends on / 依赖: M.inter_ground_subset_closure, closure, h.closure, h.subset, inter_ground_subset_closure, isRkFinite_inter_ground_iff, subset
-/
lemma isRkFinite_closure_iff : M.IsRkFinite (M.closure X) ↔ M.IsRkFinite X := by
  rw [← isRkFinite_inter_ground_iff (X := X)]
exact ⟨fun h => h.subset M.inter_ground_subset_closure X, fun h => by simpa using h.closure⟩

/--
lemma `IsRkFinite.union` / 引理 `IsRkFinite.union`

English:
lemma IsRkFinite.union
  given: (hX : M.IsRkFinite X) (hY : M.IsRkFinite Y)
  statement: M.IsRkFinite (X union Y)
  proof: by
  obtain ⟨I, hI, hIfin⟩ := hX.exists_finite_isBasis'
  obtain ⟨J, hJ, hJfin⟩ := hY.exists_finite_isBasis'
  rw [← isRkFinite_inter_ground_iff]
  refine (M.isRkFinite_of_finite (hIfin.union hJfin)).closure.subset ?_
  rw [closure_union_congr_left hI.closure_eq_closure]; rw [closure_union_congr_right hJ.closure_eq_closure]
  exact inter_ground_subset_closure M (X union Y)

中文:
引理 IsRkFinite.union
  条件: (hX : M.IsRkFinite X) (hY : M.IsRkFinite Y)
  结论: M.IsRkFinite (X union Y)
  证明: by
  obtain ⟨I, hI, hIfin⟩ := hX.exists_finite_isBasis'
  obtain ⟨J, hJ, hJfin⟩ := hY.exists_finite_isBasis'
  rw [← isRkFinite_inter_ground_iff]
  refine (M.isRkFinite_of_finite (hIfin.union hJfin)).closure.subset ?_
  rw [closure_union_congr_left hI.closure_eq_closure]; rw [closure_union_congr_right hJ.closure_eq_closure]
  exact inter_ground_subset_closure M (X union Y)

Depends on / 依赖: M.isRkFinite_of_finite, closure, closure.subset, closure_eq_closure, closure_union_congr_left, closure_union_congr_right, exists_finite_isBasis, hI.closure_eq_closure, hIfin.union, hJ.closure_eq_closure, hX.exists_finite_isBasis, hY.exists_finite_isBasis, inter_ground_subset_closure, isRkFinite_inter_ground_iff, isRkFinite_of_finite, subset
-/
lemma IsRkFinite.union (hX : M.IsRkFinite X) (hY : M.IsRkFinite Y) : M.IsRkFinite (X union Y) := by
  obtain ⟨I, hI, hIfin⟩ := hX.exists_finite_isBasis'
  obtain ⟨J, hJ, hJfin⟩ := hY.exists_finite_isBasis'
  rw [← isRkFinite_inter_ground_iff]
  refine (M.isRkFinite_of_finite (hIfin.union hJfin)).closure.subset ?_
  rw [closure_union_congr_left hI.closure_eq_closure]; rw [closure_union_congr_right hJ.closure_eq_closure]
  exact inter_ground_subset_closure M (X union Y)

/--
lemma `IsRkFinite.isRkFinite_union_iff` / 引理 `IsRkFinite.isRkFinite_union_iff`

English:
lemma IsRkFinite.isRkFinite_union_iff
  given: (hX : M.IsRkFinite X)
  proof: ⟨fun h => h.subset subset_union_right, fun h => hX.union h⟩

中文:
引理 IsRkFinite.isRkFinite_union_iff
  条件: (hX : M.IsRkFinite X)
  证明: ⟨fun h => h.subset subset_union_right, fun h => hX.union h⟩

Depends on / 依赖: h.subset, hX.union, subset, subset_union_right
-/
lemma IsRkFinite.isRkFinite_union_iff (hX : M.IsRkFinite X) :
    M.IsRkFinite (X union Y) ↔ M.IsRkFinite Y :=
  ⟨fun h => h.subset subset_union_right, fun h => hX.union h⟩

/--
lemma `IsRkFinite.isRkFinite_sdiff_iff` / 引理 `IsRkFinite.isRkFinite_sdiff_iff`

English:
lemma IsRkFinite.isRkFinite_sdiff_iff
  given: (hX : M.IsRkFinite X)
  proof: by
  rw [← hX.isRkFinite_union_iff]; rw [union_sdiff_self]; rw [hX.isRkFinite_union_iff]

@[deprecated (since := "2026-06-03")]
alias IsRkFinite.isRkFinite_diff_iff := IsRkFinite.isRkFinite_sdiff_iff

中文:
引理 IsRkFinite.isRkFinite_sdiff_iff
  条件: (hX : M.IsRkFinite X)
  证明: by
  rw [← hX.isRkFinite_union_iff]; rw [union_sdiff_self]; rw [hX.isRkFinite_union_iff]

@[deprecated (since := "2026-06-03")]
alias IsRkFinite.isRkFinite_diff_iff := IsRkFinite.isRkFinite_sdiff_iff

Depends on / 依赖: hX.isRkFinite_union_iff, isRkFinite_union_iff, union_sdiff_self
-/
lemma IsRkFinite.isRkFinite_sdiff_iff (hX : M.IsRkFinite X) :
    M.IsRkFinite (Y \ X) ↔ M.IsRkFinite Y := by
  rw [← hX.isRkFinite_union_iff]; rw [union_sdiff_self]; rw [hX.isRkFinite_union_iff]

@[deprecated (since := "2026-06-03")]
alias IsRkFinite.isRkFinite_diff_iff := IsRkFinite.isRkFinite_sdiff_iff

/--
lemma `IsRkFinite.inter_right` / 引理 `IsRkFinite.inter_right`

English:
lemma IsRkFinite.inter_right
  given: (hX : M.IsRkFinite X)
  statement: M.IsRkFinite (X inter Y)
  proof: hX.subset inter_subset_left

中文:
引理 IsRkFinite.inter_right
  条件: (hX : M.IsRkFinite X)
  结论: M.IsRkFinite (X inter Y)
  证明: hX.subset inter_subset_left

Depends on / 依赖: hX.subset, inter_subset_left, subset
-/
lemma IsRkFinite.inter_right (hX : M.IsRkFinite X) : M.IsRkFinite (X inter Y) :=
  hX.subset inter_subset_left

/--
lemma `IsRkFinite.inter_left` / 引理 `IsRkFinite.inter_left`

English:
lemma IsRkFinite.inter_left
  given: (hX : M.IsRkFinite X)
  statement: M.IsRkFinite (Y inter X)
  proof: hX.subset inter_subset_right

中文:
引理 IsRkFinite.inter_left
  条件: (hX : M.IsRkFinite X)
  结论: M.IsRkFinite (Y inter X)
  证明: hX.subset inter_subset_right

Depends on / 依赖: hX.subset, inter_subset_right, subset
-/
lemma IsRkFinite.inter_left (hX : M.IsRkFinite X) : M.IsRkFinite (Y inter X) :=
  hX.subset inter_subset_right

/--
lemma `IsRkFinite.diff` / 引理 `IsRkFinite.diff`

English:
lemma IsRkFinite.diff
  given: (hX : M.IsRkFinite X)
  statement: M.IsRkFinite (X \ Y)
  proof: hX.subset sdiff_subset

中文:
引理 IsRkFinite.diff
  条件: (hX : M.IsRkFinite X)
  结论: M.IsRkFinite (X \ Y)
  证明: hX.subset sdiff_subset

Depends on / 依赖: hX.subset, sdiff_subset, subset
-/
lemma IsRkFinite.diff (hX : M.IsRkFinite X) : M.IsRkFinite (X \ Y) :=
  hX.subset sdiff_subset

/--
lemma `IsRkFinite.insert` / 引理 `IsRkFinite.insert`

English:
lemma IsRkFinite.insert
  given: (hX : M.IsRkFinite X) (e : α)
  statement: M.IsRkFinite (insert e X)
  proof: by
  rw [← union_singleton]
  exact hX.union M.isRkFinite_singleton

@[simp]

中文:
引理 IsRkFinite.insert
  条件: (hX : M.IsRkFinite X) (e : α)
  结论: M.IsRkFinite (insert e X)
  证明: by
  rw [← union_singleton]
  exact hX.union M.isRkFinite_singleton

@[simp]

Depends on / 依赖: M.isRkFinite_singleton, hX.union, isRkFinite_singleton, union_singleton
-/
lemma IsRkFinite.insert (hX : M.IsRkFinite X) (e : α) : M.IsRkFinite (insert e X) := by
  rw [← union_singleton]
  exact hX.union M.isRkFinite_singleton

@[simp]
/--
lemma `isRkFinite_insert_iff` / 引理 `isRkFinite_insert_iff`

English:
lemma isRkFinite_insert_iff
  given: {e : α}
  statement: M.IsRkFinite (insert e X) ↔ M.IsRkFinite X
  proof: by
  rw [← singleton_union]; rw [isRkFinite_singleton.isRkFinite_union_iff]

@[simp]

中文:
引理 isRkFinite_insert_iff
  条件: {e : α}
  结论: M.IsRkFinite (insert e X) ↔ M.IsRkFinite X
  证明: by
  rw [← singleton_union]; rw [isRkFinite_singleton.isRkFinite_union_iff]

@[simp]

Depends on / 依赖: isRkFinite_singleton, isRkFinite_singleton.isRkFinite_union_iff, isRkFinite_union_iff, singleton_union
-/
lemma isRkFinite_insert_iff {e : α} : M.IsRkFinite (insert e X) ↔ M.IsRkFinite X := by
  rw [← singleton_union]; rw [isRkFinite_singleton.isRkFinite_union_iff]

@[simp]
/--
lemma `IsRkFinite.sdiff_singleton_iff` / 引理 `IsRkFinite.sdiff_singleton_iff`

English:
lemma IsRkFinite.sdiff_singleton_iff
  statement: M.IsRkFinite (X \ {e}) ↔ M.IsRkFinite X
  proof: by
  rw [isRkFinite_singleton.isRkFinite_sdiff_iff]

@[deprecated (since := "2026-06-03")]
alias IsRkFinite.diff_singleton_iff := IsRkFinite.sdiff_singleton_iff

中文:
引理 IsRkFinite.sdiff_singleton_iff
  结论: M.IsRkFinite (X \ {e}) ↔ M.IsRkFinite X
  证明: by
  rw [isRkFinite_singleton.isRkFinite_sdiff_iff]

@[deprecated (since := "2026-06-03")]
alias IsRkFinite.diff_singleton_iff := IsRkFinite.sdiff_singleton_iff

Depends on / 依赖: isRkFinite_sdiff_iff, isRkFinite_singleton, isRkFinite_singleton.isRkFinite_sdiff_iff
-/
lemma IsRkFinite.sdiff_singleton_iff : M.IsRkFinite (X \ {e}) ↔ M.IsRkFinite X := by
  rw [isRkFinite_singleton.isRkFinite_sdiff_iff]

@[deprecated (since := "2026-06-03")]
alias IsRkFinite.diff_singleton_iff := IsRkFinite.sdiff_singleton_iff

/--
lemma `isRkFinite_set` / 引理 `isRkFinite_set`

English:
lemma isRkFinite_set
  given: (M : Matroid α) [RankFinite M] (X : Set α)
  statement: M.IsRkFinite X
  proof: let ⟨_, hI⟩ := M.exists_isBasis' X
  hI.isRkFinite_of_finite hI.indep.finite

中文:
引理 isRkFinite_set
  条件: (M : 拟阵 α) [RankFinite M] (X : 集合 α)
  结论: M.IsRkFinite X
  证明: let ⟨_, hI⟩ := M.exists_isBasis' X
  hI.isRkFinite_of_finite hI.indep.finite

Depends on / 依赖: M.exists_isBasis, exists_isBasis, finite, hI.indep.finite, hI.isRkFinite_of_finite, isRkFinite_of_finite
-/
lemma isRkFinite_set (M : Matroid α) [RankFinite M] (X : Set α) : M.IsRkFinite X :=
  let ⟨_, hI⟩ := M.exists_isBasis' X
  hI.isRkFinite_of_finite hI.indep.finite

/--
lemma `IsRkFinite.iUnion` / 引理 `IsRkFinite.iUnion`

English:
lemma IsRkFinite.iUnion
  given: {ι : Type*} [Finite ι] {Xs : ι -> Set α} (h : forall i, M.IsRkFinite (Xs i))
  proof: by
  choose Is hIs using fun i => M.exists_isBasis' (Xs i)
have hfin : (⋃ i, Is i).Finite := finite_iUnion fun i => (h i).finite_of_isBasis' (hIs i)
refine isRkFinite_inter_ground_iff.1 (M.isRkFinite_of_finite hfin).closure.subset ?_
  rw [iUnion_inter]; rw [iUnion_subset_iff]
exact fun i => (hIs i).isBasis_inter_ground.subset_closure.trans M.closure_subset_closure
    subset_iUnion ..

中文:
引理 IsRkFinite.iUnion
  条件: {ι : 类型} [有限 ι] {Xs : ι -> 集合 α} (h : 对任意 i, M.IsRkFinite (Xs i))
  证明: by
  choose Is hIs using fun i => M.exists_isBasis' (Xs i)
have hfin : (⋃ i, Is i).Finite := finite_iUnion fun i => (h i).finite_of_isBasis' (hIs i)
refine isRkFinite_inter_ground_iff.1 (M.isRkFinite_of_finite hfin).closure.subset ?_
  rw [iUnion_inter]; rw [iUnion_subset_iff]
exact fun i => (hIs i).isBasis_inter_ground.subset_closure.trans M.closure_subset_closure
    subset_iUnion ..

Depends on / 依赖: Finite, M.closure_subset_closure, M.exists_isBasis, M.isRkFinite_of_finite, closure, closure.subset, closure_subset_closure, exists_isBasis, finite_iUnion, finite_of_isBasis, iUnion_inter, iUnion_subset_iff, isBasis_inter_ground, isBasis_inter_ground.subset_closure.trans, isRkFinite_inter_ground_iff, isRkFinite_of_finite, subset, subset_closure, subset_iUnion
-/
lemma IsRkFinite.iUnion {ι : Type*} [Finite ι] {Xs : ι -> Set α} (h : forall i, M.IsRkFinite (Xs i)) :
    M.IsRkFinite (⋃ i, Xs i) := by
  choose Is hIs using fun i => M.exists_isBasis' (Xs i)
have hfin : (⋃ i, Is i).Finite := finite_iUnion fun i => (h i).finite_of_isBasis' (hIs i)
refine isRkFinite_inter_ground_iff.1 (M.isRkFinite_of_finite hfin).closure.subset ?_
  rw [iUnion_inter]; rw [iUnion_subset_iff]
exact fun i => (hIs i).isBasis_inter_ground.subset_closure.trans M.closure_subset_closure
    subset_iUnion ..

end Matroid
