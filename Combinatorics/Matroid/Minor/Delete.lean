/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Loop

/-!
# Matroid Deletion

For `M : Matroid α` and `X : Set α`, the *deletion* of `X` from `M` is the matroid `M ＼ X`
with ground set `M.E \ X`, in which a subset of `M.E \ X` is independent if and only if it is
independent in `M`.

The deletion `M ＼ X` is equal to the restriction `M ↾ (M.E \ X)`, but is of special importance
in the theory because it is the dual notion of *contraction*, and thus plays a more central
and natural role than restriction in many contexts.

Because of the implementation of the restriction `M ↾ R` allowing `R` to not be a subset of `M.E`,
the relation `M ↾ R ≤r M` holds only with the assumption `R ⊆ M.E`,
whereas `M ＼ D`, being defined as `M ↾ (M.E \ D)`, satisfies `M ＼ D ≤r M` unconditionally.
This is often quite convenient.

## Main Declarations

* `Matroid.delete M D`, written `M ＼ D`, is the restriction of `M` to the set `M.E \ D`,
  or equivalently the matroid on `M.E \ D` whose independent sets are the `M`-independent sets.

## Naming conventions

We use the abbreviation `deleteElem` in lemma names to refer to the deletion `M ＼ {e}`
of a single element `e : α` from `M : Matroid α`.
-/

@[expose] public section

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I B D R X : Set α}

namespace Matroid

/-! ## Deletion -/

section Delete

/--
Definition of `delete` / `delete` 的定义

English:
definition delete
  signature: (M : Matroid α) (D : Set α)
  body: M ↾ (M.E \ D)

中文:
定义 delete
  签名: (M : 拟阵 α) (D : 集合 α)
  定义体: M ↾ (M.E \ D)
-/
def delete (M : Matroid α) (D : Set α) : Matroid α := M ↾ (M.E \ D)

/-- `M ＼ D` refers to the deletion of a set `D` from the matroid `M`. -/
scoped infixl:75 " ＼ " => Matroid.delete

/--
lemma `delete_eq_restrict` / 引理 `delete_eq_restrict`

English:
lemma delete_eq_restrict
  given: (M : Matroid α) (D : Set α)
  statement: M ＼ D = M ↾ (M.E \ D)
  proof: rfl

中文:
引理 delete_eq_restrict
  条件: (M : 拟阵 α) (D : 集合 α)
  结论: M ＼ D = M ↾ (M.E \ D)
  证明: rfl
-/
lemma delete_eq_restrict (M : Matroid α) (D : Set α) : M ＼ D = M ↾ (M.E \ D) := rfl

/--
lemma `restrict_compl` / 引理 `restrict_compl`

English:
lemma restrict_compl
  given: (M : Matroid α) (D : Set α)
  statement: M ↾ (M.E \ D) = M ＼ D
  proof: rfl

@[simp]

中文:
引理 restrict_compl
  条件: (M : 拟阵 α) (D : 集合 α)
  结论: M ↾ (M.E \ D) = M ＼ D
  证明: rfl

@[simp]
-/
lemma restrict_compl (M : Matroid α) (D : Set α) : M ↾ (M.E \ D) = M ＼ D := rfl

@[simp]
/--
lemma `delete_compl` / 引理 `delete_compl`

English:
lemma delete_compl
  given: (hR : R subseteq M.E := by aesop_mat)
  statement: M ＼ (M.E \ R) = M ↾ R
  proof: by
  rw [← restrict_compl]; rw [sdiff_sdiff_cancel_left hR]

@[simp]

中文:
引理 delete_compl
  条件: (hR : R subseteq M.E := by aesop_mat)
  结论: M ＼ (M.E \ R) = M ↾ R
  证明: by
  rw [← restrict_compl]; rw [sdiff_sdiff_cancel_left hR]

@[simp]

Depends on / 依赖: aesop_mat, restrict_compl, sdiff_sdiff_cancel_left
-/
lemma delete_compl (hR : R subseteq M.E := by aesop_mat) : M ＼ (M.E \ R) = M ↾ R := by
  rw [← restrict_compl]; rw [sdiff_sdiff_cancel_left hR]

@[simp]
/--
lemma `delete_isRestriction` / 引理 `delete_isRestriction`

English:
lemma delete_isRestriction
  given: (M : Matroid α) (D : Set α)
  statement: M ＼ D <=r M
  proof: restrict_isRestriction _ _ sdiff_subset

中文:
引理 delete_isRestriction
  条件: (M : 拟阵 α) (D : 集合 α)
  结论: M ＼ D <=r M
  证明: restrict_isRestriction _ _ sdiff_subset

Depends on / 依赖: restrict_isRestriction, sdiff_subset
-/
lemma delete_isRestriction (M : Matroid α) (D : Set α) : M ＼ D <=r M :=
  restrict_isRestriction _ _ sdiff_subset

/--
lemma `IsRestriction.exists_eq_delete` / 引理 `IsRestriction.exists_eq_delete`

English:
lemma IsRestriction.exists_eq_delete
  given: (hNM : N <=r M)
  statement: exists D subseteq M.E, N = M ＼ D
  proof: ⟨M.E \ N.E, sdiff_subset, by obtain ⟨R, hR, rfl⟩ := hNM; rw [delete_compl, restrict_ground_eq]⟩

中文:
引理 IsRestriction.存在_eq_delete
  条件: (hNM : N <=r M)
  结论: 存在 D subseteq M.E, N = M ＼ D
  证明: ⟨M.E \ N.E, sdiff_subset, by obtain ⟨R, hR, rfl⟩ := hNM; rw [delete_compl, restrict_ground_eq]⟩

Depends on / 依赖: delete_compl, restrict_ground_eq, sdiff_subset
-/
lemma IsRestriction.exists_eq_delete (hNM : N <=r M) : exists D subseteq M.E, N = M ＼ D :=
  ⟨M.E \ N.E, sdiff_subset, by obtain ⟨R, hR, rfl⟩ := hNM; rw [delete_compl, restrict_ground_eq]⟩

/--
lemma `isRestriction_iff_exists_eq_delete` / 引理 `isRestriction_iff_exists_eq_delete`

English:
lemma isRestriction_iff_exists_eq_delete
  statement: N <=r M ↔ exists D subseteq M.E, N = M ＼ D
  proof: ⟨IsRestriction.exists_eq_delete, by rintro ⟨D, -, rfl⟩; apply delete_isRestriction⟩

@[simp]

中文:
引理 isRestriction_iff_存在_eq_delete
  结论: N <=r M ↔ 存在 D subseteq M.E, N = M ＼ D
  证明: ⟨IsRestriction.exists_eq_delete, by rintro ⟨D, -, rfl⟩; apply delete_isRestriction⟩

@[simp]

Depends on / 依赖: IsRestriction, IsRestriction.exists_eq_delete, delete_isRestriction, exists_eq_delete
-/
lemma isRestriction_iff_exists_eq_delete : N <=r M ↔ exists D subseteq M.E, N = M ＼ D :=
  ⟨IsRestriction.exists_eq_delete, by rintro ⟨D, -, rfl⟩; apply delete_isRestriction⟩

@[simp]
/--
lemma `delete_ground` / 引理 `delete_ground`

English:
lemma delete_ground
  given: (M : Matroid α) (D : Set α)
  statement: (M ＼ D).E = M.E \ D
  proof: rfl

@[aesop unsafe 10% (rule_sets := [Matroid])]

中文:
引理 delete_ground
  条件: (M : 拟阵 α) (D : 集合 α)
  结论: (M ＼ D).E = M.E \ D
  证明: rfl

@[aesop unsafe 10% (rule_sets := [Matroid])]
-/
lemma delete_ground (M : Matroid α) (D : Set α) : (M ＼ D).E = M.E \ D := rfl

@[aesop unsafe 10% (rule_sets := [Matroid])]
/--
lemma `delete_subset_ground` / 引理 `delete_subset_ground`

English:
lemma delete_subset_ground
  given: (M : Matroid α) (D : Set α)
  statement: (M ＼ D).E subseteq M.E
  proof: sdiff_subset

@[simp]

中文:
引理 delete_subset_ground
  条件: (M : 拟阵 α) (D : 集合 α)
  结论: (M ＼ D).E subseteq M.E
  证明: sdiff_subset

@[simp]

Depends on / 依赖: sdiff_subset
-/
lemma delete_subset_ground (M : Matroid α) (D : Set α) : (M ＼ D).E subseteq M.E :=
  sdiff_subset

@[simp]
/--
lemma `delete_eq_self_iff` / 引理 `delete_eq_self_iff`

English:
lemma delete_eq_self_iff
  statement: M ＼ D = M ↔ Disjoint D M.E
  proof: by
  rw [← restrict_compl]; rw [restrict_eq_self_iff]; rw [sdiff_eq_left]; rw [disjoint_comm]

alias ⟨_, delete_eq_self⟩ := delete_eq_self_iff

中文:
引理 delete_eq_self_iff
  结论: M ＼ D = M ↔ Disjoint D M.E
  证明: by
  rw [← restrict_compl]; rw [restrict_eq_self_iff]; rw [sdiff_eq_left]; rw [disjoint_comm]

alias ⟨_, delete_eq_self⟩ := delete_eq_self_iff

Depends on / 依赖: disjoint_comm, restrict_compl, restrict_eq_self_iff, sdiff_eq_left
-/
lemma delete_eq_self_iff : M ＼ D = M ↔ Disjoint D M.E := by
  rw [← restrict_compl]; rw [restrict_eq_self_iff]; rw [sdiff_eq_left]; rw [disjoint_comm]

alias ⟨_, delete_eq_self⟩ := delete_eq_self_iff

/--
lemma `deleteElem_eq_self` / 引理 `deleteElem_eq_self`

English:
lemma deleteElem_eq_self
  given: (he : e ∉ M.E)
  statement: M ＼ {e} = M
  proof: by
  simpa

@[simp]

中文:
引理 deleteElem_eq_self
  条件: (he : e ∉ M.E)
  结论: M ＼ {e} = M
  证明: by
  simpa

@[simp]
-/
lemma deleteElem_eq_self (he : e ∉ M.E) : M ＼ {e} = M := by
  simpa

@[simp]
/--
lemma `delete_delete` / 引理 `delete_delete`

English:
lemma delete_delete
  given: (M : Matroid α) (D₁ D₂ : Set α)
  statement: M ＼ D₁ ＼ D₂ = M ＼ (D₁ union D₂)
  proof: by
  rw [← restrict_compl]; rw [← restrict_compl]; rw [← restrict_compl]; rw [restrict_restrict_eq]; rw [restrict_ground_eq]; rw [sdiff_sdiff]
  simp

中文:
引理 delete_delete
  条件: (M : 拟阵 α) (D₁ D₂ : 集合 α)
  结论: M ＼ D₁ ＼ D₂ = M ＼ (D₁ union D₂)
  证明: by
  rw [← restrict_compl]; rw [← restrict_compl]; rw [← restrict_compl]; rw [restrict_restrict_eq]; rw [restrict_ground_eq]; rw [sdiff_sdiff]
  simp

Depends on / 依赖: restrict_compl, restrict_ground_eq, restrict_restrict_eq, sdiff_sdiff
-/
lemma delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M ＼ D₁ ＼ D₂ = M ＼ (D₁ union D₂) := by
  rw [← restrict_compl]; rw [← restrict_compl]; rw [← restrict_compl]; rw [restrict_restrict_eq]; rw [restrict_ground_eq]; rw [sdiff_sdiff]
  simp

/--
lemma `delete_comm` / 引理 `delete_comm`

English:
lemma delete_comm
  given: (M : Matroid α) (D₁ D₂ : Set α)
  statement: M ＼ D₁ ＼ D₂ = M ＼ D₂ ＼ D₁
  proof: by
  rw [delete_delete]; rw [union_comm]; rw [delete_delete]

中文:
引理 delete_comm
  条件: (M : 拟阵 α) (D₁ D₂ : 集合 α)
  结论: M ＼ D₁ ＼ D₂ = M ＼ D₂ ＼ D₁
  证明: by
  rw [delete_delete]; rw [union_comm]; rw [delete_delete]

Depends on / 依赖: delete_delete, union_comm
-/
lemma delete_comm (M : Matroid α) (D₁ D₂ : Set α) : M ＼ D₁ ＼ D₂ = M ＼ D₂ ＼ D₁ := by
  rw [delete_delete]; rw [union_comm]; rw [delete_delete]

/--
lemma `delete_inter_ground_eq` / 引理 `delete_inter_ground_eq`

English:
lemma delete_inter_ground_eq
  given: (M : Matroid α) (D : Set α)
  statement: M ＼ (D inter M.E) = M ＼ D
  proof: by
  rw [← restrict_compl]; rw [← restrict_compl]; rw [sdiff_inter_self_eq_sdiff]

中文:
引理 delete_inter_ground_eq
  条件: (M : 拟阵 α) (D : 集合 α)
  结论: M ＼ (D inter M.E) = M ＼ D
  证明: by
  rw [← restrict_compl]; rw [← restrict_compl]; rw [sdiff_inter_self_eq_sdiff]

Depends on / 依赖: restrict_compl, sdiff_inter_self_eq_sdiff
-/
lemma delete_inter_ground_eq (M : Matroid α) (D : Set α) : M ＼ (D inter M.E) = M ＼ D := by
  rw [← restrict_compl]; rw [← restrict_compl]; rw [sdiff_inter_self_eq_sdiff]

/--
lemma `delete_eq_delete_iff` / 引理 `delete_eq_delete_iff`

English:
lemma delete_eq_delete_iff
  given: {D₁ D₂ : Set α}
  statement: M ＼ D₁ = M ＼ D₂ ↔ D₁ inter M.E = D₂ inter M.E
  proof: by
  rw [← delete_inter_ground_eq]; rw [← M.delete_inter_ground_eq D₂]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  apply_fun (M.E \ Matroid.E ·) at h
  simp_rw [delete_ground, sdiff_sdiff_cancel_left inter_subset_right] at h
  assumption

@[simp]

中文:
引理 delete_eq_delete_iff
  条件: {D₁ D₂ : 集合 α}
  结论: M ＼ D₁ = M ＼ D₂ ↔ D₁ inter M.E = D₂ inter M.E
  证明: by
  rw [← delete_inter_ground_eq]; rw [← M.delete_inter_ground_eq D₂]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  apply_fun (M.E \ Matroid.E ·) at h
  simp_rw [delete_ground, sdiff_sdiff_cancel_left inter_subset_right] at h
  assumption

@[simp]

Depends on / 依赖: M.delete_inter_ground_eq, Matroid, Matroid.E, apply_fun, delete_ground, delete_inter_ground_eq, inter_subset_right, sdiff_sdiff_cancel_left, simp_rw
-/
lemma delete_eq_delete_iff {D₁ D₂ : Set α} : M ＼ D₁ = M ＼ D₂ ↔ D₁ inter M.E = D₂ inter M.E := by
  rw [← delete_inter_ground_eq]; rw [← M.delete_inter_ground_eq D₂]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  apply_fun (M.E \ Matroid.E ·) at h
  simp_rw [delete_ground, sdiff_sdiff_cancel_left inter_subset_right] at h
  assumption

@[simp]
/--
lemma `delete_empty` / 引理 `delete_empty`

English:
lemma delete_empty
  given: (M : Matroid α)
  statement: M ＼ ∅ = M
  proof: by
  rw [delete_eq_self_iff]
  exact empty_disjoint _

中文:
引理 delete_empty
  条件: (M : 拟阵 α)
  结论: M ＼ ∅ = M
  证明: by
  rw [delete_eq_self_iff]
  exact empty_disjoint _

Depends on / 依赖: delete_eq_self_iff, empty_disjoint
-/
lemma delete_empty (M : Matroid α) : M ＼ ∅ = M := by
  rw [delete_eq_self_iff]
  exact empty_disjoint _

/--
lemma `delete_delete_eq_delete_sdiff` / 引理 `delete_delete_eq_delete_sdiff`

English:
lemma delete_delete_eq_delete_sdiff
  given: (M : Matroid α) (D₁ D₂ : Set α)
  proof: by
  simp

@[deprecated (since := "2026-06-03")]
alias delete_delete_eq_delete_diff := delete_delete_eq_delete_sdiff

中文:
引理 delete_delete_eq_delete_sdiff
  条件: (M : 拟阵 α) (D₁ D₂ : 集合 α)
  证明: by
  simp

@[deprecated (since := "2026-06-03")]
alias delete_delete_eq_delete_diff := delete_delete_eq_delete_sdiff
-/
lemma delete_delete_eq_delete_sdiff (M : Matroid α) (D₁ D₂ : Set α) :
    M ＼ D₁ ＼ D₂ = M ＼ D₁ ＼ (D₂ \ D₁) := by
  simp

@[deprecated (since := "2026-06-03")]
alias delete_delete_eq_delete_diff := delete_delete_eq_delete_sdiff

/--
lemma `IsRestriction.restrict_delete_of_disjoint` / 引理 `IsRestriction.restrict_delete_of_disjoint`

English:
lemma IsRestriction.restrict_delete_of_disjoint
  given: (h : N <=r M) (hX : Disjoint X N.E)
  proof: by
  obtain ⟨D, hD, rfl⟩ := isRestriction_iff_exists_eq_delete.1 h
  refine isRestriction_iff_exists_eq_delete.2 ⟨D \ X, sdiff_subset_sdiff_left hD, ?_⟩
  rwa [delete_delete, union_sdiff_self, union_comm, ← delete_delete, eq_comm,
    delete_eq_self_iff]

中文:
引理 IsRestriction.restrict_delete_of_disjoint
  条件: (h : N <=r M) (hX : Disjoint X N.E)
  证明: by
  obtain ⟨D, hD, rfl⟩ := isRestriction_iff_exists_eq_delete.1 h
  refine isRestriction_iff_exists_eq_delete.2 ⟨D \ X, sdiff_subset_sdiff_left hD, ?_⟩
  rwa [delete_delete, union_sdiff_self, union_comm, ← delete_delete, eq_comm,
    delete_eq_self_iff]

Depends on / 依赖: delete_delete, delete_eq_self_iff, eq_comm, isRestriction_iff_exists_eq_delete, sdiff_subset_sdiff_left, union_comm, union_sdiff_self
-/
lemma IsRestriction.restrict_delete_of_disjoint (h : N <=r M) (hX : Disjoint X N.E) :
    N <=r (M ＼ X) := by
  obtain ⟨D, hD, rfl⟩ := isRestriction_iff_exists_eq_delete.1 h
  refine isRestriction_iff_exists_eq_delete.2 ⟨D \ X, sdiff_subset_sdiff_left hD, ?_⟩
  rwa [delete_delete, union_sdiff_self, union_comm, ← delete_delete, eq_comm,
    delete_eq_self_iff]

/--
lemma `IsRestriction.isRestriction_deleteElem` / 引理 `IsRestriction.isRestriction_deleteElem`

English:
lemma IsRestriction.isRestriction_deleteElem
  given: (h : N <=r M) (he : e ∉ N.E)
  statement: N <=r M ＼ {e}
  proof: h.restrict_delete_of_disjoint (by simpa)

中文:
引理 IsRestriction.isRestriction_deleteElem
  条件: (h : N <=r M) (he : e ∉ N.E)
  结论: N <=r M ＼ {e}
  证明: h.restrict_delete_of_disjoint (by simpa)

Depends on / 依赖: h.restrict_delete_of_disjoint, restrict_delete_of_disjoint
-/
lemma IsRestriction.isRestriction_deleteElem (h : N <=r M) (he : e ∉ N.E) : N <=r M ＼ {e} :=
  h.restrict_delete_of_disjoint (by simpa)

/-! ### Independence and Bases -/

@[simp]
/--
lemma `delete_indep_iff` / 引理 `delete_indep_iff`

English:
lemma delete_indep_iff
  statement: (M ＼ D).Indep I ↔ M.Indep I ∧ Disjoint I D
  proof: by
  rw [← restrict_compl]; rw [restrict_indep_iff]; rw [subset_sdiff]; rw [← and_assoc]; rw [and_iff_left_of_imp Indep.subset_ground]

中文:
引理 delete_indep_iff
  结论: (M ＼ D).Indep I ↔ M.Indep I ∧ Disjoint I D
  证明: by
  rw [← restrict_compl]; rw [restrict_indep_iff]; rw [subset_sdiff]; rw [← and_assoc]; rw [and_iff_left_of_imp Indep.subset_ground]

Depends on / 依赖: Indep.subset_ground, and_assoc, and_iff_left_of_imp, restrict_compl, restrict_indep_iff, subset_ground, subset_sdiff
-/
lemma delete_indep_iff : (M ＼ D).Indep I ↔ M.Indep I ∧ Disjoint I D := by
  rw [← restrict_compl]; rw [restrict_indep_iff]; rw [subset_sdiff]; rw [← and_assoc]; rw [and_iff_left_of_imp Indep.subset_ground]

/--
lemma `deleteElem_indep_iff` / 引理 `deleteElem_indep_iff`

English:
lemma deleteElem_indep_iff
  statement: (M ＼ {e}).Indep I ↔ M.Indep I ∧ e ∉ I
  proof: by
  simp

中文:
引理 deleteElem_indep_iff
  结论: (M ＼ {e}).Indep I ↔ M.Indep I ∧ e ∉ I
  证明: by
  simp
-/
lemma deleteElem_indep_iff : (M ＼ {e}).Indep I ↔ M.Indep I ∧ e ∉ I := by
  simp

/--
lemma `Indep.of_delete` / 引理 `Indep.of_delete`

English:
lemma Indep.of_delete
  given: (h : (M ＼ D).Indep I)
  statement: M.Indep I
  proof: (delete_indep_iff.mp h).1

中文:
引理 Indep.of_delete
  条件: (h : (M ＼ D).Indep I)
  结论: M.Indep I
  证明: (delete_indep_iff.mp h).1

Depends on / 依赖: delete_indep_iff, delete_indep_iff.mp
-/
lemma Indep.of_delete (h : (M ＼ D).Indep I) : M.Indep I :=
  (delete_indep_iff.mp h).1

/--
lemma `Indep.indep_delete_of_disjoint` / 引理 `Indep.indep_delete_of_disjoint`

English:
lemma Indep.indep_delete_of_disjoint
  given: (h : M.Indep I) (hID : Disjoint I D)
  statement: (M ＼ D).Indep I
  proof: delete_indep_iff.mpr ⟨h, hID⟩

中文:
引理 Indep.indep_delete_of_disjoint
  条件: (h : M.Indep I) (hID : Disjoint I D)
  结论: (M ＼ D).Indep I
  证明: delete_indep_iff.mpr ⟨h, hID⟩

Depends on / 依赖: delete_indep_iff, delete_indep_iff.mpr
-/
lemma Indep.indep_delete_of_disjoint (h : M.Indep I) (hID : Disjoint I D) : (M ＼ D).Indep I :=
  delete_indep_iff.mpr ⟨h, hID⟩

/--
lemma `indep_iff_delete_of_disjoint` / 引理 `indep_iff_delete_of_disjoint`

English:
lemma indep_iff_delete_of_disjoint
  given: (hID : Disjoint I D)
  statement: M.Indep I ↔ (M ＼ D).Indep I
  proof: ⟨fun h => h.indep_delete_of_disjoint hID, fun h => h.of_delete⟩

@[simp]

中文:
引理 indep_iff_delete_of_disjoint
  条件: (hID : Disjoint I D)
  结论: M.Indep I ↔ (M ＼ D).Indep I
  证明: ⟨fun h => h.indep_delete_of_disjoint hID, fun h => h.of_delete⟩

@[simp]

Depends on / 依赖: h.indep_delete_of_disjoint, h.of_delete, indep_delete_of_disjoint, of_delete
-/
lemma indep_iff_delete_of_disjoint (hID : Disjoint I D) : M.Indep I ↔ (M ＼ D).Indep I :=
  ⟨fun h => h.indep_delete_of_disjoint hID, fun h => h.of_delete⟩

@[simp]
/--
lemma `delete_dep_iff` / 引理 `delete_dep_iff`

English:
lemma delete_dep_iff
  statement: (M ＼ D).Dep X ↔ M.Dep X ∧ Disjoint X D
  proof: by
  rw [dep_iff]; rw [dep_iff]; rw [delete_indep_iff]; rw [delete_ground]; rw [subset_sdiff]; tauto

@[simp]

中文:
引理 delete_dep_iff
  结论: (M ＼ D).Dep X ↔ M.Dep X ∧ Disjoint X D
  证明: by
  rw [dep_iff]; rw [dep_iff]; rw [delete_indep_iff]; rw [delete_ground]; rw [subset_sdiff]; tauto

@[simp]

Depends on / 依赖: delete_ground, delete_indep_iff, dep_iff, subset_sdiff
-/
lemma delete_dep_iff : (M ＼ D).Dep X ↔ M.Dep X ∧ Disjoint X D := by
  rw [dep_iff]; rw [dep_iff]; rw [delete_indep_iff]; rw [delete_ground]; rw [subset_sdiff]; tauto

@[simp]
/--
lemma `delete_isBase_iff` / 引理 `delete_isBase_iff`

English:
lemma delete_isBase_iff
  statement: (M ＼ D).IsBase B ↔ M.IsBasis B (M.E \ D)
  proof: by
  rw [← restrict_compl]; rw [isBase_restrict_iff]

@[simp]

中文:
引理 delete_isBase_iff
  结论: (M ＼ D).IsBase B ↔ M.是基 B (M.E \ D)
  证明: by
  rw [← restrict_compl]; rw [isBase_restrict_iff]

@[simp]

Depends on / 依赖: isBase_restrict_iff, restrict_compl
-/
lemma delete_isBase_iff : (M ＼ D).IsBase B ↔ M.IsBasis B (M.E \ D) := by
  rw [← restrict_compl]; rw [isBase_restrict_iff]

@[simp]
/--
lemma `delete_isBasis_iff` / 引理 `delete_isBasis_iff`

English:
lemma delete_isBasis_iff
  statement: (M ＼ D).IsBasis I X ↔ M.IsBasis I X ∧ Disjoint X D
  proof: by
  rw [← restrict_compl]; rw [isBasis_restrict_iff]; rw [subset_sdiff]; rw [← and_assoc]; rw [and_iff_left_of_imp IsBasis.subset_ground]

@[simp]

中文:
引理 delete_isBasis_iff
  结论: (M ＼ D).是基 I X ↔ M.是基 I X ∧ Disjoint X D
  证明: by
  rw [← restrict_compl]; rw [isBasis_restrict_iff]; rw [subset_sdiff]; rw [← and_assoc]; rw [and_iff_left_of_imp IsBasis.subset_ground]

@[simp]

Depends on / 依赖: IsBasis, IsBasis.subset_ground, and_assoc, and_iff_left_of_imp, isBasis_restrict_iff, restrict_compl, subset_ground, subset_sdiff
-/
lemma delete_isBasis_iff : (M ＼ D).IsBasis I X ↔ M.IsBasis I X ∧ Disjoint X D := by
  rw [← restrict_compl]; rw [isBasis_restrict_iff]; rw [subset_sdiff]; rw [← and_assoc]; rw [and_iff_left_of_imp IsBasis.subset_ground]

@[simp]
/--
lemma `delete_isBasis'_iff` / 引理 `delete_isBasis'_iff`

English:
lemma delete_isBasis'_iff
  statement: (M ＼ D).IsBasis' I X ↔ M.IsBasis' I (X \ D)
  proof: by
  rw [isBasis'_iff_isBasis_inter_ground]; rw [delete_isBasis_iff]; rw [delete_ground]; rw [sdiff_eq]; rw [inter_comm M.E]; rw [← inter_assoc]; rw [← sdiff_eq]; rw [← isBasis'_iff_isBasis_inter_ground]; rw [and_iff_left_iff_imp]; rw [inter_comm]; rw [← inter_sdiff_assoc]
  exact fun _ => disjoint_sdiff_left

中文:
引理 delete_isBasis'_iff
  结论: (M ＼ D).是基' I X ↔ M.是基' I (X \ D)
  证明: by
  rw [isBasis'_iff_isBasis_inter_ground]; rw [delete_isBasis_iff]; rw [delete_ground]; rw [sdiff_eq]; rw [inter_comm M.E]; rw [← inter_assoc]; rw [← sdiff_eq]; rw [← isBasis'_iff_isBasis_inter_ground]; rw [and_iff_left_iff_imp]; rw [inter_comm]; rw [← inter_sdiff_assoc]
  exact fun _ => disjoint_sdiff_left

Depends on / 依赖: _iff_isBasis_inter_ground, and_iff_left_iff_imp, delete_ground, delete_isBasis_iff, disjoint_sdiff_left, inter_assoc, inter_comm, inter_sdiff_assoc, isBasis, sdiff_eq
-/
lemma delete_isBasis'_iff : (M ＼ D).IsBasis' I X ↔ M.IsBasis' I (X \ D) := by
  rw [isBasis'_iff_isBasis_inter_ground]; rw [delete_isBasis_iff]; rw [delete_ground]; rw [sdiff_eq]; rw [inter_comm M.E]; rw [← inter_assoc]; rw [← sdiff_eq]; rw [← isBasis'_iff_isBasis_inter_ground]; rw [and_iff_left_iff_imp]; rw [inter_comm]; rw [← inter_sdiff_assoc]
  exact fun _ => disjoint_sdiff_left

/--
lemma `IsBasis.of_delete` / 引理 `IsBasis.of_delete`

English:
lemma IsBasis.of_delete
  given: (h : (M ＼ D).IsBasis I X)
  statement: M.IsBasis I X
  proof: (delete_isBasis_iff.mp h).1

中文:
引理 是基.of_delete
  条件: (h : (M ＼ D).是基 I X)
  结论: M.是基 I X
  证明: (delete_isBasis_iff.mp h).1

Depends on / 依赖: delete_isBasis_iff, delete_isBasis_iff.mp
-/
lemma IsBasis.of_delete (h : (M ＼ D).IsBasis I X) : M.IsBasis I X :=
  (delete_isBasis_iff.mp h).1

/--
lemma `IsBasis.delete` / 引理 `IsBasis.delete`

English:
lemma IsBasis.delete
  given: (h : M.IsBasis I X) (hX : Disjoint X D)
  statement: (M ＼ D).IsBasis I X
  proof: by
  rw [delete_isBasis_iff]; exact ⟨h, hX⟩

中文:
引理 是基.delete
  条件: (h : M.是基 I X) (hX : Disjoint X D)
  结论: (M ＼ D).是基 I X
  证明: by
  rw [delete_isBasis_iff]; exact ⟨h, hX⟩

Depends on / 依赖: delete_isBasis_iff
-/
lemma IsBasis.delete (h : M.IsBasis I X) (hX : Disjoint X D) : (M ＼ D).IsBasis I X := by
  rw [delete_isBasis_iff]; exact ⟨h, hX⟩

/--
lemma `Coindep.delete_isBase_iff` / 引理 `Coindep.delete_isBase_iff`

English:
lemma Coindep.delete_isBase_iff
  given: (hD : M.Coindep D)
  proof: by
  rw [Matroid.delete_isBase_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hss := h.subset
    rw [subset_sdiff] at hss
    have hcl := h.isBasis_closure_right
    rw [hD.closure_compl]; rw [isBasis_ground_iff] at hcl
    exact ⟨hcl, hss.2⟩
  exact h.1.isBasis_ground.isBasis_subset (by simp [subset_sdiff, h.1.subset_ground, h.2])
    sdiff_subset

中文:
引理 Coindep.delete_isBase_iff
  条件: (hD : M.Coindep D)
  证明: by
  rw [Matroid.delete_isBase_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hss := h.subset
    rw [subset_sdiff] at hss
    have hcl := h.isBasis_closure_right
    rw [hD.closure_compl]; rw [isBasis_ground_iff] at hcl
    exact ⟨hcl, hss.2⟩
  exact h.1.isBasis_ground.isBasis_subset (by simp [subset_sdiff, h.1.subset_ground, h.2])
    sdiff_subset

Depends on / 依赖: Matroid, Matroid.delete_isBase_iff, closure_compl, delete_isBase_iff, h.isBasis_closure_right, h.subset, hD.closure_compl, isBasis_closure_right, isBasis_ground, isBasis_ground.isBasis_subset, isBasis_ground_iff, isBasis_subset, sdiff_subset, subset, subset_ground, subset_sdiff
-/
lemma Coindep.delete_isBase_iff (hD : M.Coindep D) :
    (M ＼ D).IsBase B ↔ M.IsBase B ∧ Disjoint B D := by
  rw [Matroid.delete_isBase_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hss := h.subset
    rw [subset_sdiff] at hss
    have hcl := h.isBasis_closure_right
    rw [hD.closure_compl]; rw [isBasis_ground_iff] at hcl
    exact ⟨hcl, hss.2⟩
  exact h.1.isBasis_ground.isBasis_subset (by simp [subset_sdiff, h.1.subset_ground, h.2])
    sdiff_subset

/--
lemma `Coindep.delete_rankPos` / 引理 `Coindep.delete_rankPos`

English:
lemma Coindep.delete_rankPos
  given: [M.RankPos] (hD : M.Coindep D)
  statement: (M ＼ D).RankPos
  proof: by
  rw [rankPos_iff]; rw [hD.delete_isBase_iff]
  simp [M.empty_not_isBase]

中文:
引理 Coindep.delete_rankPos
  条件: [M.RankPos] (hD : M.Coindep D)
  结论: (M ＼ D).RankPos
  证明: by
  rw [rankPos_iff]; rw [hD.delete_isBase_iff]
  simp [M.empty_not_isBase]

Depends on / 依赖: M.empty_not_isBase, delete_isBase_iff, empty_not_isBase, hD.delete_isBase_iff, rankPos_iff
-/
lemma Coindep.delete_rankPos [M.RankPos] (hD : M.Coindep D) : (M ＼ D).RankPos := by
  rw [rankPos_iff]; rw [hD.delete_isBase_iff]
  simp [M.empty_not_isBase]

/--
lemma `Coindep.delete_spanning_iff` / 引理 `Coindep.delete_spanning_iff`

English:
lemma Coindep.delete_spanning_iff
  given: {S : Set α} (hD : M.Coindep D)
  proof: by
  simp only [spanning_iff_exists_isBase_subset', hD.delete_isBase_iff, and_assoc, delete_ground,
    subset_sdiff, and_congr_left_iff, and_imp]
  refine fun hSE hSD => ⟨fun ⟨B, hB, hBD, hBS⟩ => ⟨B, hB, hBS⟩, fun ⟨B, hB, hBS⟩ => ⟨B, hB, ?_, hBS⟩⟩
  exact hSD.mono_left hBS

中文:
引理 Coindep.delete_spanning_iff
  条件: {S : 集合 α} (hD : M.Coindep D)
  证明: by
  simp only [spanning_iff_exists_isBase_subset', hD.delete_isBase_iff, and_assoc, delete_ground,
    subset_sdiff, and_congr_left_iff, and_imp]
  refine fun hSE hSD => ⟨fun ⟨B, hB, hBD, hBS⟩ => ⟨B, hB, hBS⟩, fun ⟨B, hB, hBS⟩ => ⟨B, hB, ?_, hBS⟩⟩
  exact hSD.mono_left hBS

Depends on / 依赖: and_assoc, and_congr_left_iff, and_imp, delete_ground, delete_isBase_iff, hD.delete_isBase_iff, hSD.mono_left, mono_left, spanning_iff_exists_isBase_subset, subset_sdiff
-/
lemma Coindep.delete_spanning_iff {S : Set α} (hD : M.Coindep D) :
    (M ＼ D).Spanning S ↔ M.Spanning S ∧ Disjoint S D := by
  simp only [spanning_iff_exists_isBase_subset', hD.delete_isBase_iff, and_assoc, delete_ground,
    subset_sdiff, and_congr_left_iff, and_imp]
  refine fun hSE hSD => ⟨fun ⟨B, hB, hBD, hBS⟩ => ⟨B, hB, hBS⟩, fun ⟨B, hB, hBS⟩ => ⟨B, hB, ?_, hBS⟩⟩
  exact hSD.mono_left hBS

/-! ### Loops, circuits and closure -/

@[simp]
/--
lemma `delete_isLoop_iff` / 引理 `delete_isLoop_iff`

English:
lemma delete_isLoop_iff
  statement: (M ＼ D).IsLoop e ↔ M.IsLoop e ∧ e ∉ D
  proof: by
  rw [← singleton_dep]; rw [delete_dep_iff]; rw [disjoint_singleton_left]; rw [singleton_dep]

@[simp]

中文:
引理 delete_isLoop_iff
  结论: (M ＼ D).IsLoop e ↔ M.IsLoop e ∧ e ∉ D
  证明: by
  rw [← singleton_dep]; rw [delete_dep_iff]; rw [disjoint_singleton_left]; rw [singleton_dep]

@[simp]

Depends on / 依赖: delete_dep_iff, disjoint_singleton_left, singleton_dep
-/
lemma delete_isLoop_iff : (M ＼ D).IsLoop e ↔ M.IsLoop e ∧ e ∉ D := by
  rw [← singleton_dep]; rw [delete_dep_iff]; rw [disjoint_singleton_left]; rw [singleton_dep]

@[simp]
/--
lemma `delete_isNonloop_iff` / 引理 `delete_isNonloop_iff`

English:
lemma delete_isNonloop_iff
  statement: (M ＼ D).IsNonloop e ↔ M.IsNonloop e ∧ e ∉ D
  proof: by
  rw [← indep_singleton]; rw [delete_indep_iff]; rw [disjoint_singleton_left]; rw [indep_singleton]

中文:
引理 delete_isNonloop_iff
  结论: (M ＼ D).是Nonloop e ↔ M.是Nonloop e ∧ e ∉ D
  证明: by
  rw [← indep_singleton]; rw [delete_indep_iff]; rw [disjoint_singleton_left]; rw [indep_singleton]

Depends on / 依赖: delete_indep_iff, disjoint_singleton_left, indep_singleton
-/
lemma delete_isNonloop_iff : (M ＼ D).IsNonloop e ↔ M.IsNonloop e ∧ e ∉ D := by
  rw [← indep_singleton]; rw [delete_indep_iff]; rw [disjoint_singleton_left]; rw [indep_singleton]

/--
lemma `IsNonloop.of_delete` / 引理 `IsNonloop.of_delete`

English:
lemma IsNonloop.of_delete
  given: (h : (M ＼ D).IsNonloop e)
  statement: M.IsNonloop e
  proof: (delete_isNonloop_iff.1 h).1

中文:
引理 是Nonloop.of_delete
  条件: (h : (M ＼ D).是Nonloop e)
  结论: M.是Nonloop e
  证明: (delete_isNonloop_iff.1 h).1

Depends on / 依赖: delete_isNonloop_iff
-/
lemma IsNonloop.of_delete (h : (M ＼ D).IsNonloop e) : M.IsNonloop e :=
  (delete_isNonloop_iff.1 h).1

/--
lemma `isNonloop_iff_delete_of_notMem` / 引理 `isNonloop_iff_delete_of_notMem`

English:
lemma isNonloop_iff_delete_of_notMem
  given: (he : e ∉ D)
  statement: M.IsNonloop e ↔ (M ＼ D).IsNonloop e
  proof: ⟨fun h => delete_isNonloop_iff.2 ⟨h, he⟩, fun h => h.of_delete⟩

中文:
引理 isNonloop_iff_delete_of_notMem
  条件: (he : e ∉ D)
  结论: M.是Nonloop e ↔ (M ＼ D).是Nonloop e
  证明: ⟨fun h => delete_isNonloop_iff.2 ⟨h, he⟩, fun h => h.of_delete⟩

Depends on / 依赖: delete_isNonloop_iff, h.of_delete, of_delete
-/
lemma isNonloop_iff_delete_of_notMem (he : e ∉ D) : M.IsNonloop e ↔ (M ＼ D).IsNonloop e :=
  ⟨fun h => delete_isNonloop_iff.2 ⟨h, he⟩, fun h => h.of_delete⟩

/--
lemma `delete_loops_eq_removeLoops` / 引理 `delete_loops_eq_removeLoops`

English:
lemma delete_loops_eq_removeLoops
  given: (M : Matroid α)
  statement: M ＼ M.loops = M.removeLoops
  proof: by
  rw [removeLoops]; rw [delete_eq_restrict]; rw [compl_loops_eq]

@[simp]

中文:
引理 delete_loops_eq_removeLoops
  条件: (M : 拟阵 α)
  结论: M ＼ M.loops = M.removeLoops
  证明: by
  rw [removeLoops]; rw [delete_eq_restrict]; rw [compl_loops_eq]

@[simp]

Depends on / 依赖: compl_loops_eq, delete_eq_restrict, removeLoops
-/
lemma delete_loops_eq_removeLoops (M : Matroid α) : M ＼ M.loops = M.removeLoops := by
  rw [removeLoops]; rw [delete_eq_restrict]; rw [compl_loops_eq]

@[simp]
/--
lemma `delete_isCircuit_iff` / 引理 `delete_isCircuit_iff`

English:
lemma delete_isCircuit_iff
  given: {C : Set α}
  proof: by
  rw [delete_eq_restrict]; rw [restrict_isCircuit_iff]; rw [and_congr_right_iff]; rw [subset_sdiff]; rw [and_iff_right_iff_imp]
  exact fun h _ => h.subset_ground

中文:
引理 delete_isCircuit_iff
  条件: {C : 集合 α}
  证明: by
  rw [delete_eq_restrict]; rw [restrict_isCircuit_iff]; rw [and_congr_right_iff]; rw [subset_sdiff]; rw [and_iff_right_iff_imp]
  exact fun h _ => h.subset_ground

Depends on / 依赖: and_congr_right_iff, and_iff_right_iff_imp, delete_eq_restrict, h.subset_ground, restrict_isCircuit_iff, subset_ground, subset_sdiff
-/
lemma delete_isCircuit_iff {C : Set α} :
    (M ＼ D).IsCircuit C ↔ M.IsCircuit C ∧ Disjoint C D := by
  rw [delete_eq_restrict]; rw [restrict_isCircuit_iff]; rw [and_congr_right_iff]; rw [subset_sdiff]; rw [and_iff_right_iff_imp]
  exact fun h _ => h.subset_ground

/--
lemma `IsCircuit.of_delete` / 引理 `IsCircuit.of_delete`

English:
lemma IsCircuit.of_delete
  given: {C : Set α} (h : (M ＼ D).IsCircuit C)
  statement: M.IsCircuit C
  proof: (delete_isCircuit_iff.1 h).1

中文:
引理 是Circuit.of_delete
  条件: {C : 集合 α} (h : (M ＼ D).是Circuit C)
  结论: M.是Circuit C
  证明: (delete_isCircuit_iff.1 h).1

Depends on / 依赖: delete_isCircuit_iff
-/
lemma IsCircuit.of_delete {C : Set α} (h : (M ＼ D).IsCircuit C) : M.IsCircuit C :=
  (delete_isCircuit_iff.1 h).1

/--
lemma `circuit_iff_delete_of_disjoint` / 引理 `circuit_iff_delete_of_disjoint`

English:
lemma circuit_iff_delete_of_disjoint
  given: {C : Set α} (hCD : Disjoint C D)
  proof: ⟨fun h => delete_isCircuit_iff.2 ⟨h, hCD⟩, fun h => h.of_delete⟩

@[simp]

中文:
引理 circuit_iff_delete_of_disjoint
  条件: {C : 集合 α} (hCD : Disjoint C D)
  证明: ⟨fun h => delete_isCircuit_iff.2 ⟨h, hCD⟩, fun h => h.of_delete⟩

@[simp]

Depends on / 依赖: delete_isCircuit_iff, h.of_delete, of_delete
-/
lemma circuit_iff_delete_of_disjoint {C : Set α} (hCD : Disjoint C D) :
    M.IsCircuit C ↔ (M ＼ D).IsCircuit C :=
  ⟨fun h => delete_isCircuit_iff.2 ⟨h, hCD⟩, fun h => h.of_delete⟩

@[simp]
/--
lemma `delete_closure_eq` / 引理 `delete_closure_eq`

English:
lemma delete_closure_eq
  given: (M : Matroid α) (D X : Set α)
  proof: by
  rw [← restrict_compl]; rw [restrict_closure_eq']; rw [sdiff_sdiff_self]; rw [bot_eq_empty]; rw [union_empty]; rw [sdiff_eq]; rw [inter_comm M.E]; rw [← inter_assoc X]; rw [← sdiff_eq]; rw [closure_inter_ground]; rw [← inter_assoc]; rw [← sdiff_eq]; rw [inter_eq_left]
  exact sdiff_subset.trans (M.closure_subset_ground _)

中文:
引理 delete_closure_eq
  条件: (M : 拟阵 α) (D X : 集合 α)
  证明: by
  rw [← restrict_compl]; rw [restrict_closure_eq']; rw [sdiff_sdiff_self]; rw [bot_eq_empty]; rw [union_empty]; rw [sdiff_eq]; rw [inter_comm M.E]; rw [← inter_assoc X]; rw [← sdiff_eq]; rw [closure_inter_ground]; rw [← inter_assoc]; rw [← sdiff_eq]; rw [inter_eq_left]
  exact sdiff_subset.trans (M.closure_subset_ground _)

Depends on / 依赖: M.closure_subset_ground, bot_eq_empty, closure_inter_ground, closure_subset_ground, inter_assoc, inter_comm, inter_eq_left, restrict_closure_eq, restrict_compl, sdiff_eq, sdiff_sdiff_self, sdiff_subset, sdiff_subset.trans, union_empty
-/
lemma delete_closure_eq (M : Matroid α) (D X : Set α) :
    (M ＼ D).closure X = M.closure (X \ D) \ D := by
  rw [← restrict_compl]; rw [restrict_closure_eq']; rw [sdiff_sdiff_self]; rw [bot_eq_empty]; rw [union_empty]; rw [sdiff_eq]; rw [inter_comm M.E]; rw [← inter_assoc X]; rw [← sdiff_eq]; rw [closure_inter_ground]; rw [← inter_assoc]; rw [← sdiff_eq]; rw [inter_eq_left]
  exact sdiff_subset.trans (M.closure_subset_ground _)

/--
lemma `delete_closure_eq_of_disjoint` / 引理 `delete_closure_eq_of_disjoint`

English:
lemma delete_closure_eq_of_disjoint
  given: (M : Matroid α) {D X : Set α} (hXD : Disjoint X D)
  proof: by
  rw [delete_closure_eq]; rw [hXD.sdiff_eq_left]

@[simp]

中文:
引理 delete_closure_eq_of_disjoint
  条件: (M : 拟阵 α) {D X : 集合 α} (hXD : Disjoint X D)
  证明: by
  rw [delete_closure_eq]; rw [hXD.sdiff_eq_left]

@[simp]

Depends on / 依赖: delete_closure_eq, hXD.sdiff_eq_left, sdiff_eq_left
-/
lemma delete_closure_eq_of_disjoint (M : Matroid α) {D X : Set α} (hXD : Disjoint X D) :
    (M ＼ D).closure X = M.closure X \ D := by
  rw [delete_closure_eq]; rw [hXD.sdiff_eq_left]

@[simp]
/--
lemma `delete_loops_eq` / 引理 `delete_loops_eq`

English:
lemma delete_loops_eq
  given: (M : Matroid α) (D : Set α)
  statement: (M ＼ D).loops = M.loops \ D
  proof: by
  simp [loops]

中文:
引理 delete_loops_eq
  条件: (M : 拟阵 α) (D : 集合 α)
  结论: (M ＼ D).loops = M.loops \ D
  证明: by
  simp [loops]
-/
lemma delete_loops_eq (M : Matroid α) (D : Set α) : (M ＼ D).loops = M.loops \ D := by
  simp [loops]

/--
lemma `delete_isColoop_iff` / 引理 `delete_isColoop_iff`

English:
lemma delete_isColoop_iff
  given: (M : Matroid α) (D : Set α)
  proof: by
  rw [delete_eq_restrict]; rw [restrict_isColoop_iff sdiff_subset]; rw [mem_sdiff]; rw [and_congr_left_iff]
  simp

中文:
引理 delete_isColoop_iff
  条件: (M : 拟阵 α) (D : 集合 α)
  证明: by
  rw [delete_eq_restrict]; rw [restrict_isColoop_iff sdiff_subset]; rw [mem_sdiff]; rw [and_congr_left_iff]
  simp

Depends on / 依赖: and_congr_left_iff, delete_eq_restrict, mem_sdiff, restrict_isColoop_iff, sdiff_subset
-/
lemma delete_isColoop_iff (M : Matroid α) (D : Set α) :
    (M ＼ D).IsColoop e ↔ e ∉ M.closure ((M.E \ D) \ {e}) ∧ e in M.E ∧ e ∉ D := by
  rw [delete_eq_restrict]; rw [restrict_isColoop_iff sdiff_subset]; rw [mem_sdiff]; rw [and_congr_left_iff]
  simp


/--
Instance `delete_finitary` / 实例 `delete_finitary`

English:
instance delete_finitary
  signature: (M : Matroid α) [Finitary M] (D : Set α)
  body: inferInstanceAs Finitary (M ↾ (M.E \ D))

中文:
实例 delete_finitary
  签名: (M : 拟阵 α) [Finitary M] (D : 集合 α)
  定义体: inferInstanceAs Finitary (M ↾ (M.E \ D))

Depends on / 依赖: Finitary
-/
instance delete_finitary (M : Matroid α) [Finitary M] (D : Set α) : Finitary (M ＼ D) :=
inferInstanceAs Finitary (M ↾ (M.E \ D))

/--
Instance `delete_finite` / 实例 `delete_finite`

English:
instance delete_finite
  signature: [M.Finite]
  body: ⟨M.ground_finite.sdiff⟩

中文:
实例 delete_finite
  签名: [M.有限]
  定义体: ⟨M.ground_finite.sdiff⟩

Depends on / 依赖: M.ground_finite.sdiff, ground_finite
-/
instance delete_finite [M.Finite] : (M ＼ D).Finite :=
  ⟨M.ground_finite.sdiff⟩

/--
Instance `delete_rankFinite` / 实例 `delete_rankFinite`

English:
instance delete_rankFinite
  signature: [RankFinite M]
  body: restrict_rankFinite _

中文:
实例 delete_rankFinite
  签名: [RankFinite M]
  定义体: restrict_rankFinite _

Depends on / 依赖: restrict_rankFinite
-/
instance delete_rankFinite [RankFinite M] : RankFinite (M ＼ D) :=
  restrict_rankFinite _

end Delete

end Matroid
