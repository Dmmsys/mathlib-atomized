/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Minor.Contract

/-!
# Matroid Minors

A matroid `N = M ／ C ＼ D` obtained from a matroid `M` by a contraction then a delete,
(or equivalently, by any number of contractions/deletions in any order) is a *minor* of `M`.
This gives a partial order on `Matroid α` that is ubiquitous in matroid theory,
and interacts nicely with duality and linear representations.

Although we provide a `PartialOrder` instance on `Matroid α` corresponding to the minor order,
we do not use the `M ≤ N` / `N < M` notation directly,
instead writing `N ≤m M` and `N <m M` for more convenient dot notation.

## Main Declarations

* `Matroid.IsMinor N M`, written `N ≤m M`, means that `N = M ／ C ＼ D` for some
  subset `C` and `D` of `M.E`.
* `Matroid.IsStrictMinor N M`, written `N <m M`, means that `N = M ／ C ＼ D`
  for some subsets `C` and `D` of `M.E` that are not both nonempty.
* `Matroid.IsMinor.exists_eq_contract_delete_disjoint` : we can choose `C` and `D` disjoint.

-/

@[expose] public section

namespace Matroid

open Set

section Minor

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I C D : Set α}

/-! ### Minors -/

/--
Definition of `IsMinor` / `IsMinor` 的定义

English:
definition IsMinor
  signature: (N M : Matroid α)
  body: exists C D, N = M ／ C ＼ D

中文:
定义 IsMinor
  签名: (N M : Matroid α)
  定义体: exists C D, N = M ／ C ＼ D
-/
def IsMinor (N M : Matroid α) : Prop := exists C D, N = M ／ C ＼ D

/-- `≤m` denotes the minor relation on matroids. -/
infixl:50 " <=m " => Matroid.IsMinor

@[simp]
/--
lemma `contract_delete_isMinor` / 引理 `contract_delete_isMinor`

English:
lemma contract_delete_isMinor
  given: (M : Matroid α) (C D : Set α)
  statement: M ／ C ＼ D <=m M
  proof: ⟨C, D, rfl⟩

中文:
引理 contract_delete_isMinor
  条件: (M : Matroid α) (C D : Set α)
  结论: M ／ C ＼ D <=m M
  证明: ⟨C, D, rfl⟩
-/
lemma contract_delete_isMinor (M : Matroid α) (C D : Set α) : M ／ C ＼ D <=m M :=
  ⟨C, D, rfl⟩

/--
lemma `IsMinor.exists_eq_contract_delete_disjoint` / 引理 `IsMinor.exists_eq_contract_delete_disjoint`

English:
lemma IsMinor.exists_eq_contract_delete_disjoint
  given: (h : N <=m M)
  proof: by
  obtain ⟨C, D, rfl⟩ := h
  exact ⟨C inter M.E, (D inter M.E) \ C, inter_subset_right, sdiff_subset.trans inter_subset_right,
    disjoint_sdiff_right.mono_left inter_subset_left,
    by simp [delete_eq_delete_iff, inter_assoc, inter_sdiff_assoc]⟩

中文:
引理 IsMinor.exists_eq_contract_delete_disjoint
  条件: (h : N <=m M)
  证明: by
  obtain ⟨C, D, rfl⟩ := h
  exact ⟨C inter M.E, (D inter M.E) \ C, inter_subset_right, sdiff_subset.trans inter_subset_right,
    disjoint_sdiff_right.mono_left inter_subset_left,
    by simp [delete_eq_delete_iff, inter_assoc, inter_sdiff_assoc]⟩

Depends on / 依赖: delete_eq_delete_iff, disjoint_sdiff_right, disjoint_sdiff_right.mono_left, inter_assoc, inter_sdiff_assoc, inter_subset_left, inter_subset_right, mono_left, sdiff_subset, sdiff_subset.trans
-/
lemma IsMinor.exists_eq_contract_delete_disjoint (h : N <=m M) :
    exists (C D : Set α), C subseteq M.E ∧ D subseteq M.E ∧ Disjoint C D ∧ N = M ／ C ＼ D := by
  obtain ⟨C, D, rfl⟩ := h
  exact ⟨C inter M.E, (D inter M.E) \ C, inter_subset_right, sdiff_subset.trans inter_subset_right,
    disjoint_sdiff_right.mono_left inter_subset_left,
    by simp [delete_eq_delete_iff, inter_assoc, inter_sdiff_assoc]⟩

/--
Definition of `IsStrictMinor` / `IsStrictMinor` 的定义

English:
definition IsStrictMinor
  signature: (N M : Matroid α)
  body: N <=m M ∧ ¬ M <=m N

中文:
定义 IsStrictMinor
  签名: (N M : Matroid α)
  定义体: N <=m M ∧ ¬ M <=m N
-/
def IsStrictMinor (N M : Matroid α) : Prop := N <=m M ∧ ¬ M <=m N

/-- `<m` denotes the strict minor relation on matroids. -/
infixl:50 " <m " => Matroid.IsStrictMinor

/--
lemma `IsMinor.subset` / 引理 `IsMinor.subset`

English:
lemma IsMinor.subset
  given: (h : N <=m M)
  statement: N.E subseteq M.E
  proof: by
  obtain ⟨C, D, rfl⟩ := h
  exact sdiff_subset.trans sdiff_subset

中文:
引理 IsMinor.subset
  条件: (h : N <=m M)
  结论: N.E subseteq M.E
  证明: by
  obtain ⟨C, D, rfl⟩ := h
  exact sdiff_subset.trans sdiff_subset

Depends on / 依赖: sdiff_subset, sdiff_subset.trans
-/
lemma IsMinor.subset (h : N <=m M) : N.E subseteq M.E := by
  obtain ⟨C, D, rfl⟩ := h
  exact sdiff_subset.trans sdiff_subset

/--
lemma `IsMinor.refl` / 引理 `IsMinor.refl`

English:
lemma IsMinor.refl
  given: {M : Matroid α}
  statement: M <=m M
  proof: ⟨∅, ∅, by simp⟩

中文:
引理 IsMinor.refl
  条件: {M : Matroid α}
  结论: M <=m M
  证明: ⟨∅, ∅, by simp⟩
-/
lemma IsMinor.refl {M : Matroid α} : M <=m M := ⟨∅, ∅, by simp⟩

/--
lemma `IsMinor.trans` / 引理 `IsMinor.trans`

English:
lemma IsMinor.trans
  given: {M₁ M₂ M₃ : Matroid α} (h : M₁ <=m M₂) (h' : M₂ <=m M₃)
  statement: M₁ <=m M₃
  proof: by
  obtain ⟨C₁, D₁, rfl⟩ := h
  obtain ⟨C₂, D₂, rfl⟩ := h'
  exact ⟨C₂ union C₁ \ D₂, D₂ union D₁, by rw [contract_delete_contract_delete']⟩

中文:
引理 IsMinor.trans
  条件: {M₁ M₂ M₃ : Matroid α} (h : M₁ <=m M₂) (h' : M₂ <=m M₃)
  结论: M₁ <=m M₃
  证明: by
  obtain ⟨C₁, D₁, rfl⟩ := h
  obtain ⟨C₂, D₂, rfl⟩ := h'
  exact ⟨C₂ union C₁ \ D₂, D₂ union D₁, by rw [contract_delete_contract_delete']⟩

Depends on / 依赖: contract_delete_contract_delete
-/
lemma IsMinor.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ <=m M₂) (h' : M₂ <=m M₃) : M₁ <=m M₃ := by
  obtain ⟨C₁, D₁, rfl⟩ := h
  obtain ⟨C₂, D₂, rfl⟩ := h'
  exact ⟨C₂ union C₁ \ D₂, D₂ union D₁, by rw [contract_delete_contract_delete']⟩

/--
lemma `IsMinor.eq_of_ground_subset` / 引理 `IsMinor.eq_of_ground_subset`

English:
lemma IsMinor.eq_of_ground_subset
  given: (h : N <=m M) (hE : M.E subseteq N.E)
  statement: M = N
  proof: by
  obtain ⟨C, D, rfl⟩ := h
  rw [delete_ground]; rw [contract_ground]; rw [subset_sdiff]; rw [subset_sdiff] at hE
  rw [← contract_inter_ground_eq]; rw [hE.1.2.symm.inter_eq]; rw [contract_empty]; rw [← delete_inter_ground_eq]; rw [hE.2.symm.inter_eq]; rw [delete_empty]

中文:
引理 IsMinor.eq_of_ground_subset
  条件: (h : N <=m M) (hE : M.E subseteq N.E)
  结论: M = N
  证明: by
  obtain ⟨C, D, rfl⟩ := h
  rw [delete_ground]; rw [contract_ground]; rw [subset_sdiff]; rw [subset_sdiff] at hE
  rw [← contract_inter_ground_eq]; rw [hE.1.2.symm.inter_eq]; rw [contract_empty]; rw [← delete_inter_ground_eq]; rw [hE.2.symm.inter_eq]; rw [delete_empty]

Depends on / 依赖: contract_empty, contract_ground, contract_inter_ground_eq, delete_empty, delete_ground, delete_inter_ground_eq, inter_eq, subset_sdiff, symm.inter_eq
-/
lemma IsMinor.eq_of_ground_subset (h : N <=m M) (hE : M.E subseteq N.E) : M = N := by
  obtain ⟨C, D, rfl⟩ := h
  rw [delete_ground]; rw [contract_ground]; rw [subset_sdiff]; rw [subset_sdiff] at hE
  rw [← contract_inter_ground_eq]; rw [hE.1.2.symm.inter_eq]; rw [contract_empty]; rw [← delete_inter_ground_eq]; rw [hE.2.symm.inter_eq]; rw [delete_empty]

/--
lemma `IsMinor.antisymm` / 引理 `IsMinor.antisymm`

English:
lemma IsMinor.antisymm
  given: (h : N <=m M) (h' : M <=m N)
  statement: N = M
  proof: h'.eq_of_ground_subset h.subset

中文:
引理 IsMinor.antisymm
  条件: (h : N <=m M) (h' : M <=m N)
  结论: N = M
  证明: h'.eq_of_ground_subset h.subset

Depends on / 依赖: eq_of_ground_subset, h.subset, subset
-/
lemma IsMinor.antisymm (h : N <=m M) (h' : M <=m N) : N = M :=
  h'.eq_of_ground_subset h.subset

/-- The minor order is a `PartialOrder` on `Matroid α`.
We prefer the spelling `N ≤m M` over `N ≤ M` for the dot notation. -/
instance (α : Type*) : PartialOrder (Matroid α) where
  le N M := N <=m M
  lt N M := N <m M
  le_refl _ := IsMinor.refl
  le_trans _ _ _ := IsMinor.trans
  le_antisymm _ _ := IsMinor.antisymm

/--
lemma `IsMinor.le` / 引理 `IsMinor.le`

English:
lemma IsMinor.le
  given: (h : N <=m M)
  statement: N <= M
  proof: h

中文:
引理 IsMinor.le
  条件: (h : N <=m M)
  结论: N <= M
  证明: h
-/
lemma IsMinor.le (h : N <=m M) : N <= M := h

/--
lemma `IsStrictMinor.lt` / 引理 `IsStrictMinor.lt`

English:
lemma IsStrictMinor.lt
  given: (h : N <m M)
  statement: N < M
  proof: h

@[simp]

中文:
引理 IsStrictMinor.lt
  条件: (h : N <m M)
  结论: N < M
  证明: h

@[simp]
-/
lemma IsStrictMinor.lt (h : N <m M) : N < M := h

@[simp]
/--
lemma `le_eq_isMinor` / 引理 `le_eq_isMinor`

English:
lemma le_eq_isMinor
  statement: (fun M M' : Matroid α => M <= M') = Matroid.IsMinor
  proof: rfl

@[simp]

中文:
引理 le_eq_isMinor
  结论: (fun M M' : Matroid α => M <= M') = Matroid.IsMinor
  证明: rfl

@[simp]
-/
lemma le_eq_isMinor : (fun M M' : Matroid α => M <= M') = Matroid.IsMinor := rfl

@[simp]
/--
lemma `lt_eq_isStrictMinor` / 引理 `lt_eq_isStrictMinor`

English:
lemma lt_eq_isStrictMinor
  statement: (fun M M' : Matroid α => M < M') = Matroid.IsStrictMinor
  proof: rfl

中文:
引理 lt_eq_isStrictMinor
  结论: (fun M M' : Matroid α => M < M') = Matroid.IsStrictMinor
  证明: rfl
-/
lemma lt_eq_isStrictMinor : (fun M M' : Matroid α => M < M') = Matroid.IsStrictMinor := rfl

/--
lemma `isStrictMinor_iff_isMinor_ne` / 引理 `isStrictMinor_iff_isMinor_ne`

English:
lemma isStrictMinor_iff_isMinor_ne
  statement: N <m M ↔ N <=m M ∧ N != M
  proof: lt_iff_le_and_ne (α := Matroid α)

中文:
引理 isStrictMinor_iff_isMinor_ne
  结论: N <m M ↔ N <=m M ∧ N != M
  证明: lt_iff_le_and_ne (α := Matroid α)

Depends on / 依赖: Matroid, lt_iff_le_and_ne
-/
lemma isStrictMinor_iff_isMinor_ne : N <m M ↔ N <=m M ∧ N != M :=
  lt_iff_le_and_ne (α := Matroid α)

/--
lemma `IsStrictMinor.ne` / 引理 `IsStrictMinor.ne`

English:
lemma IsStrictMinor.ne
  given: (h : N <m M)
  statement: N != M
  proof: h.lt.ne

中文:
引理 IsStrictMinor.ne
  条件: (h : N <m M)
  结论: N != M
  证明: h.lt.ne

Depends on / 依赖: h.lt.ne
-/
lemma IsStrictMinor.ne (h : N <m M) : N != M :=
  h.lt.ne

/--
lemma `isStrictMinor_irrefl` / 引理 `isStrictMinor_irrefl`

English:
lemma isStrictMinor_irrefl
  given: (M : Matroid α)
  statement: ¬ (M <m M)
  proof: lt_irrefl M

中文:
引理 isStrictMinor_irrefl
  条件: (M : Matroid α)
  结论: ¬ (M <m M)
  证明: lt_irrefl M

Depends on / 依赖: lt_irrefl
-/
lemma isStrictMinor_irrefl (M : Matroid α) : ¬ (M <m M) :=
  lt_irrefl M

/--
lemma `IsStrictMinor.isMinor` / 引理 `IsStrictMinor.isMinor`

English:
lemma IsStrictMinor.isMinor
  given: (h : N <m M)
  statement: N <=m M
  proof: h.lt.le

中文:
引理 IsStrictMinor.isMinor
  条件: (h : N <m M)
  结论: N <=m M
  证明: h.lt.le

Depends on / 依赖: h.lt.le
-/
lemma IsStrictMinor.isMinor (h : N <m M) : N <=m M :=
  h.lt.le

/--
lemma `IsStrictMinor.not_isMinor` / 引理 `IsStrictMinor.not_isMinor`

English:
lemma IsStrictMinor.not_isMinor
  given: (h : N <m M)
  statement: ¬ (M <=m N)
  proof: h.lt.not_ge

中文:
引理 IsStrictMinor.not_isMinor
  条件: (h : N <m M)
  结论: ¬ (M <=m N)
  证明: h.lt.not_ge

Depends on / 依赖: h.lt.not_ge, not_ge
-/
lemma IsStrictMinor.not_isMinor (h : N <m M) : ¬ (M <=m N) :=
  h.lt.not_ge

/--
lemma `IsStrictMinor.ssubset` / 引理 `IsStrictMinor.ssubset`

English:
lemma IsStrictMinor.ssubset
  given: (h : N <m M)
  statement: N.E ⊂ M.E
  proof: h.isMinor.subset.ssubset_of_ne (fun hE => h.ne (h.isMinor.eq_of_ground_subset hE.symm.subset).symm)

中文:
引理 IsStrictMinor.ssubset
  条件: (h : N <m M)
  结论: N.E ⊂ M.E
  证明: h.isMinor.subset.ssubset_of_ne (fun hE => h.ne (h.isMinor.eq_of_ground_subset hE.symm.subset).symm)

Depends on / 依赖: eq_of_ground_subset, h.isMinor.eq_of_ground_subset, h.isMinor.subset.ssubset_of_ne, h.ne, hE.symm.subset, isMinor, ssubset_of_ne, subset
-/
lemma IsStrictMinor.ssubset (h : N <m M) : N.E ⊂ M.E :=
  h.isMinor.subset.ssubset_of_ne (fun hE => h.ne (h.isMinor.eq_of_ground_subset hE.symm.subset).symm)

/--
lemma `isStrictMinor_iff_isMinor_ssubset` / 引理 `isStrictMinor_iff_isMinor_ssubset`

English:
lemma isStrictMinor_iff_isMinor_ssubset
  statement: N <m M ↔ N <=m M ∧ N.E ⊂ M.E
  proof: ⟨fun h => ⟨h.isMinor, h.ssubset⟩, fun ⟨h, hss⟩ => ⟨h, fun h' => hss.ne by rw [h'.antisymm h]⟩⟩

中文:
引理 isStrictMinor_iff_isMinor_ssubset
  结论: N <m M ↔ N <=m M ∧ N.E ⊂ M.E
  证明: ⟨fun h => ⟨h.isMinor, h.ssubset⟩, fun ⟨h, hss⟩ => ⟨h, fun h' => hss.ne by rw [h'.antisymm h]⟩⟩

Depends on / 依赖: antisymm, h.isMinor, h.ssubset, hss.ne, isMinor, ssubset
-/
lemma isStrictMinor_iff_isMinor_ssubset : N <m M ↔ N <=m M ∧ N.E ⊂ M.E :=
⟨fun h => ⟨h.isMinor, h.ssubset⟩, fun ⟨h, hss⟩ => ⟨h, fun h' => hss.ne by rw [h'.antisymm h]⟩⟩

/--
lemma `IsStrictMinor.trans_isMinor` / 引理 `IsStrictMinor.trans_isMinor`

English:
lemma IsStrictMinor.trans_isMinor
  given: (h : N <m M) (h' : M <=m M')
  statement: N <m M'
  proof: h.lt.trans_le h'

中文:
引理 IsStrictMinor.trans_isMinor
  条件: (h : N <m M) (h' : M <=m M')
  结论: N <m M'
  证明: h.lt.trans_le h'

Depends on / 依赖: h.lt.trans_le, trans_le
-/
lemma IsStrictMinor.trans_isMinor (h : N <m M) (h' : M <=m M') : N <m M' :=
  h.lt.trans_le h'

/--
lemma `IsMinor.trans_isStrictMinor` / 引理 `IsMinor.trans_isStrictMinor`

English:
lemma IsMinor.trans_isStrictMinor
  given: (h : N <=m M) (h' : M <m M')
  statement: N <m M'
  proof: h.le.trans_lt h'

中文:
引理 IsMinor.trans_isStrictMinor
  条件: (h : N <=m M) (h' : M <m M')
  结论: N <m M'
  证明: h.le.trans_lt h'

Depends on / 依赖: Realizer, Realizer.principal, h.le.trans_lt, principal, trans_lt
-/
lemma IsMinor.trans_isStrictMinor (h : N <=m M) (h' : M <m M') : N <m M' :=
  h.le.trans_lt h'

/--
lemma `IsStrictMinor.trans` / 引理 `IsStrictMinor.trans`

English:
lemma IsStrictMinor.trans
  given: (h : N <m M) (h' : M <m M')
  statement: N <m M'
  proof: h.lt.trans h'

中文:
引理 IsStrictMinor.trans
  条件: (h : N <m M) (h' : M <m M')
  结论: N <m M'
  证明: h.lt.trans h'

Depends on / 依赖: h.lt.trans
-/
lemma IsStrictMinor.trans (h : N <m M) (h' : M <m M') : N <m M' :=
  h.lt.trans h'

/--
lemma `Indep.of_isMinor` / 引理 `Indep.of_isMinor`

English:
lemma Indep.of_isMinor
  given: (hI : N.Indep I) (hNM : N <=m M)
  statement: M.Indep I
  proof: by
  obtain ⟨C, D, rfl⟩ := hNM
  exact hI.of_delete.of_contract

中文:
引理 Indep.of_isMinor
  条件: (hI : N.Indep I) (hNM : N <=m M)
  结论: M.Indep I
  证明: by
  obtain ⟨C, D, rfl⟩ := hNM
  exact hI.of_delete.of_contract

Depends on / 依赖: hI.of_delete.of_contract, of_contract, of_delete
-/
lemma Indep.of_isMinor (hI : N.Indep I) (hNM : N <=m M) : M.Indep I := by
  obtain ⟨C, D, rfl⟩ := hNM
  exact hI.of_delete.of_contract

/--
lemma `IsNonloop.of_isMinor` / 引理 `IsNonloop.of_isMinor`

English:
lemma IsNonloop.of_isMinor
  given: (h : N.IsNonloop e) (hNM : N <=m M)
  statement: M.IsNonloop e
  proof: by
  obtain ⟨C, D, rfl⟩ := hNM
  exact h.of_delete.of_contract

中文:
引理 IsNonloop.of_isMinor
  条件: (h : N.IsNonloop e) (hNM : N <=m M)
  结论: M.IsNonloop e
  证明: by
  obtain ⟨C, D, rfl⟩ := hNM
  exact h.of_delete.of_contract

Depends on / 依赖: h.of_delete.of_contract, of_contract, of_delete
-/
lemma IsNonloop.of_isMinor (h : N.IsNonloop e) (hNM : N <=m M) : M.IsNonloop e := by
  obtain ⟨C, D, rfl⟩ := hNM
  exact h.of_delete.of_contract

/--
lemma `Dep.of_isMinor` / 引理 `Dep.of_isMinor`

English:
lemma Dep.of_isMinor
  given: {D : Set α} (hD : M.Dep D) (hDN : D subseteq N.E) (hNM : N <=m M)
  statement: N.Dep D
  proof: ⟨fun h => hD.not_indep h.of_isMinor hNM, hDN⟩

中文:
引理 Dep.of_isMinor
  条件: {D : Set α} (hD : M.Dep D) (hDN : D subseteq N.E) (hNM : N <=m M)
  结论: N.Dep D
  证明: ⟨fun h => hD.not_indep h.of_isMinor hNM, hDN⟩

Depends on / 依赖: h.of_isMinor, hD.not_indep, not_indep, of_isMinor
-/
lemma Dep.of_isMinor {D : Set α} (hD : M.Dep D) (hDN : D subseteq N.E) (hNM : N <=m M) : N.Dep D :=
⟨fun h => hD.not_indep h.of_isMinor hNM, hDN⟩

/--
lemma `IsLoop.of_isMinor` / 引理 `IsLoop.of_isMinor`

English:
lemma IsLoop.of_isMinor
  given: (he : M.IsLoop e) (heN : e in N.E) (hNM : N <=m M)
  statement: N.IsLoop e
  proof: by
  rw [← singleton_dep] at he ⊢
  exact he.of_isMinor (by simpa) hNM

中文:
引理 IsLoop.of_isMinor
  条件: (he : M.IsLoop e) (heN : e in N.E) (hNM : N <=m M)
  结论: N.IsLoop e
  证明: by
  rw [← singleton_dep] at he ⊢
  exact he.of_isMinor (by simpa) hNM

Depends on / 依赖: he.of_isMinor, of_isMinor, singleton_dep
-/
lemma IsLoop.of_isMinor (he : M.IsLoop e) (heN : e in N.E) (hNM : N <=m M) : N.IsLoop e := by
  rw [← singleton_dep] at he ⊢
  exact he.of_isMinor (by simpa) hNM

end Minor

end Matroid
