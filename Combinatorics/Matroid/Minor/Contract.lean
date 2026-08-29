/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Minor.Delete
public import Mathlib.Tactic.TautoSet

/-!
# Matroid Contraction

Instead of deleting the elements of `X : Set α` from `M : Matroid α`, we can contract them.
The *contraction* of `X` from `M`, denoted `M ／ X`, is the matroid on ground set `M.E \ X`
in which a set `I` is independent if and only if `I ∪ J` is independent in `M`,
where `J` is an arbitrarily chosen basis for `X`. Contraction corresponds to contracting
edges in graphic matroids (hence the name) and corresponds to projecting to a quotient
space in the case of linearly representable matroids. It is an important notion in both
these settings.

We can also define contraction much more tersely in terms of deletion and duality
with `M ／ X = (M✶ ＼ X)✶`: that is, contraction is the dual operation of deletion.
While this is perhaps less intuitive, we use this very concise expression as the definition,
and prove with the lemma `Matroid.IsBasis.contract_indep_iff` that this is equivalent to
the more verbose definition above.

## Main Declarations

* `Matroid.contract M C`, written `M ／ C`, is the matroid on ground set `M.E \ C` in which a set
  `I ⊆ M.E \ C` is independent if and only if `I ∪ J` is independent in `M`,
  where `J` is an arbitrary basis for `C`.
* `Matroid.contract_dual M C : (M ／ X)✶ = M✶ ＼ X`; the dual of contraction is deletion.
* `Matroid.delete_dual M C : (M ＼ X)✶ = M✶ ／ X`; the dual of deletion is contraction.
* `Matroid.IsBasis.contract_indep_iff`; if `I` is a basis for `C`, then the independent
  sets of `M ／ C` are exactly the `J ⊆ M.E \ C` for which `I ∪ J` is independent in `M`.
* `Matroid.contract_delete_comm` : `M ／ C ＼ D = M ＼ D ／ C` for disjoint `C` and `D`.

## Naming conventions

Mirroring the convention for deletion, we use the abbreviation `contractElem` in lemma names
to refer to the contraction `M ／ {e}` of a single element `e : α` from `M : Matroid α`.
-/

@[expose] public section

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R D B X Y Z K : Set α}

namespace Matroid

section Contract

variable {C C₁ C₂ : Set α}

/--
Definition of `contract` / `contract` 的定义

English:
definition contract
  signature: (M : Matroid α) (C : Set α)
  body: (M✶ ＼ C)✶

中文:
定义 contract
  签名: (M : Matroid α) (C : Set α)
  定义体: (M✶ ＼ C)✶
-/
def contract (M : Matroid α) (C : Set α) : Matroid α := (M✶ ＼ C)✶

/-- `M ／ C` refers to the contraction of a set `C` from the matroid `M`. -/
scoped infixl:75 " ／ " => Matroid.contract

/--
lemma `contract_ground` / 引理 `contract_ground`

English:
lemma contract_ground
  given: (M : Matroid α) (C : Set α)
  statement: (M ／ C).E = M.E \ C
  proof: rfl

中文:
引理 contract_ground
  条件: (M : Matroid α) (C : Set α)
  结论: (M ／ C).E = M.E \ C
  证明: rfl
-/
@[simp] lemma contract_ground (M : Matroid α) (C : Set α) : (M ／ C).E = M.E \ C := rfl

/--
lemma `dual_delete_dual` / 引理 `dual_delete_dual`

English:
lemma dual_delete_dual
  given: (M : Matroid α) (X : Set α)
  statement: (M✶ ＼ X)✶ = M ／ X
  proof: rfl

@[simp]

中文:
引理 dual_delete_dual
  条件: (M : Matroid α) (X : Set α)
  结论: (M✶ ＼ X)✶ = M ／ X
  证明: rfl

@[simp]
-/
lemma dual_delete_dual (M : Matroid α) (X : Set α) : (M✶ ＼ X)✶ = M ／ X := rfl

@[simp]
/--
lemma `dual_delete` / 引理 `dual_delete`

English:
lemma dual_delete
  given: (M : Matroid α) (X : Set α)
  statement: (M ＼ X)✶ = M✶ ／ X
  proof: by
  rw [← dual_dual M]; rw [dual_delete_dual]; rw [dual_dual]

@[simp]

中文:
引理 dual_delete
  条件: (M : Matroid α) (X : Set α)
  结论: (M ＼ X)✶ = M✶ ／ X
  证明: by
  rw [← dual_dual M]; rw [dual_delete_dual]; rw [dual_dual]

@[simp]

Depends on / 依赖: dual_delete_dual, dual_dual
-/
lemma dual_delete (M : Matroid α) (X : Set α) : (M ＼ X)✶ = M✶ ／ X := by
  rw [← dual_dual M]; rw [dual_delete_dual]; rw [dual_dual]

@[simp]
/--
lemma `dual_contract` / 引理 `dual_contract`

English:
lemma dual_contract
  given: (M : Matroid α) (X : Set α)
  statement: (M ／ X)✶ = M✶ ＼ X
  proof: by
  rw [← dual_delete_dual]; rw [dual_dual]

中文:
引理 dual_contract
  条件: (M : Matroid α) (X : Set α)
  结论: (M ／ X)✶ = M✶ ＼ X
  证明: by
  rw [← dual_delete_dual]; rw [dual_dual]

Depends on / 依赖: dual_delete_dual, dual_dual
-/
lemma dual_contract (M : Matroid α) (X : Set α) : (M ／ X)✶ = M✶ ＼ X := by
  rw [← dual_delete_dual]; rw [dual_dual]

/--
lemma `dual_contract_dual` / 引理 `dual_contract_dual`

English:
lemma dual_contract_dual
  given: (M : Matroid α) (X : Set α)
  statement: (M✶ ／ X)✶ = M ＼ X
  proof: by
  simp

@[simp]

中文:
引理 dual_contract_dual
  条件: (M : Matroid α) (X : Set α)
  结论: (M✶ ／ X)✶ = M ＼ X
  证明: by
  simp

@[simp]
-/
lemma dual_contract_dual (M : Matroid α) (X : Set α) : (M✶ ／ X)✶ = M ＼ X := by
  simp

@[simp]
/--
lemma `contract_contract` / 引理 `contract_contract`

English:
lemma contract_contract
  given: (M : Matroid α) (C₁ C₂ : Set α)
  statement: M ／ C₁ ／ C₂ = M ／ (C₁ union C₂)
  proof: by
  simp [← dual_inj]

中文:
引理 contract_contract
  条件: (M : Matroid α) (C₁ C₂ : Set α)
  结论: M ／ C₁ ／ C₂ = M ／ (C₁ union C₂)
  证明: by
  simp [← dual_inj]

Depends on / 依赖: dual_inj
-/
lemma contract_contract (M : Matroid α) (C₁ C₂ : Set α) : M ／ C₁ ／ C₂ = M ／ (C₁ union C₂) := by
  simp [← dual_inj]

/--
lemma `contract_comm` / 引理 `contract_comm`

English:
lemma contract_comm
  given: (M : Matroid α) (C₁ C₂ : Set α)
  statement: M ／ C₁ ／ C₂ = M ／ C₂ ／ C₁
  proof: by
  simp [union_comm]

中文:
引理 contract_comm
  条件: (M : Matroid α) (C₁ C₂ : Set α)
  结论: M ／ C₁ ／ C₂ = M ／ C₂ ／ C₁
  证明: by
  simp [union_comm]

Depends on / 依赖: union_comm
-/
lemma contract_comm (M : Matroid α) (C₁ C₂ : Set α) : M ／ C₁ ／ C₂ = M ／ C₂ ／ C₁ := by
  simp [union_comm]

/--
lemma `dual_contract_delete` / 引理 `dual_contract_delete`

English:
lemma dual_contract_delete
  given: (M : Matroid α) (X Y : Set α)
  statement: (M ／ X ＼ Y)✶ = M✶ ＼ X ／ Y
  proof: by
  simp

中文:
引理 dual_contract_delete
  条件: (M : Matroid α) (X Y : Set α)
  结论: (M ／ X ＼ Y)✶ = M✶ ＼ X ／ Y
  证明: by
  simp
-/
lemma dual_contract_delete (M : Matroid α) (X Y : Set α) : (M ／ X ＼ Y)✶ = M✶ ＼ X ／ Y := by
  simp

/--
lemma `dual_delete_contract` / 引理 `dual_delete_contract`

English:
lemma dual_delete_contract
  given: (M : Matroid α) (X Y : Set α)
  statement: (M ＼ X ／ Y)✶ = M✶ ／ X ＼ Y
  proof: by
  simp

中文:
引理 dual_delete_contract
  条件: (M : Matroid α) (X Y : Set α)
  结论: (M ＼ X ／ Y)✶ = M✶ ／ X ＼ Y
  证明: by
  simp
-/
lemma dual_delete_contract (M : Matroid α) (X Y : Set α) : (M ＼ X ／ Y)✶ = M✶ ／ X ＼ Y := by
  simp

/--
lemma `contract_eq_self_iff` / 引理 `contract_eq_self_iff`

English:
lemma contract_eq_self_iff
  statement: M ／ C = M ↔ Disjoint C M.E
  proof: by
  rw [← dual_delete_dual]; rw [← dual_inj]; rw [dual_dual]; rw [delete_eq_self_iff]; rw [dual_ground]

中文:
引理 contract_eq_self_iff
  结论: M ／ C = M ↔ Disjoint C M.E
  证明: by
  rw [← dual_delete_dual]; rw [← dual_inj]; rw [dual_dual]; rw [delete_eq_self_iff]; rw [dual_ground]

Depends on / 依赖: delete_eq_self_iff, dual_delete_dual, dual_dual, dual_ground, dual_inj
-/
lemma contract_eq_self_iff : M ／ C = M ↔ Disjoint C M.E := by
  rw [← dual_delete_dual]; rw [← dual_inj]; rw [dual_dual]; rw [delete_eq_self_iff]; rw [dual_ground]

/--
lemma `contractElem_eq_self` / 引理 `contractElem_eq_self`

English:
lemma contractElem_eq_self
  given: (he : e ∉ M.E)
  statement: M ／ {e} = M
  proof: by
  rw [← dual_delete_dual]; rw [deleteElem_eq_self (by simpa)]; rw [dual_dual]

中文:
引理 contractElem_eq_self
  条件: (he : e ∉ M.E)
  结论: M ／ {e} = M
  证明: by
  rw [← dual_delete_dual]; rw [deleteElem_eq_self (by simpa)]; rw [dual_dual]

Depends on / 依赖: deleteElem_eq_self, dual_delete_dual, dual_dual
-/
lemma contractElem_eq_self (he : e ∉ M.E) : M ／ {e} = M := by
  rw [← dual_delete_dual]; rw [deleteElem_eq_self (by simpa)]; rw [dual_dual]

/--
lemma `contract_empty` / 引理 `contract_empty`

English:
lemma contract_empty
  given: (M : Matroid α)
  statement: M ／ ∅ = M
  proof: by
  rw [← dual_delete_dual]; rw [delete_empty]; rw [dual_dual]

中文:
引理 contract_empty
  条件: (M : Matroid α)
  结论: M ／ ∅ = M
  证明: by
  rw [← dual_delete_dual]; rw [delete_empty]; rw [dual_dual]
-/
@[simp] lemma contract_empty (M : Matroid α) : M ／ ∅ = M := by
  rw [← dual_delete_dual]; rw [delete_empty]; rw [dual_dual]

/--
lemma `contract_contract_eq_contract_sdiff` / 引理 `contract_contract_eq_contract_sdiff`

English:
lemma contract_contract_eq_contract_sdiff
  given: (M : Matroid α) (C₁ C₂ : Set α)
  proof: by
  simp

@[deprecated (since := "2026-06-03")]
alias contract_contract_eq_contract_diff := contract_contract_eq_contract_sdiff

中文:
引理 contract_contract_eq_contract_sdiff
  条件: (M : Matroid α) (C₁ C₂ : Set α)
  证明: by
  simp

@[deprecated (since := "2026-06-03")]
alias contract_contract_eq_contract_diff := contract_contract_eq_contract_sdiff
-/
lemma contract_contract_eq_contract_sdiff (M : Matroid α) (C₁ C₂ : Set α) :
    M ／ C₁ ／ C₂ = M ／ C₁ ／ (C₂ \ C₁) := by
  simp

@[deprecated (since := "2026-06-03")]
alias contract_contract_eq_contract_diff := contract_contract_eq_contract_sdiff

/--
lemma `contract_eq_contract_iff` / 引理 `contract_eq_contract_iff`

English:
lemma contract_eq_contract_iff
  statement: M ／ C₁ = M ／ C₂ ↔ C₁ inter M.E = C₂ inter M.E
  proof: by
  rw [← dual_delete_dual]; rw [← dual_delete_dual]; rw [dual_inj]; rw [delete_eq_delete_iff]; rw [dual_ground]

中文:
引理 contract_eq_contract_iff
  结论: M ／ C₁ = M ／ C₂ ↔ C₁ inter M.E = C₂ inter M.E
  证明: by
  rw [← dual_delete_dual]; rw [← dual_delete_dual]; rw [dual_inj]; rw [delete_eq_delete_iff]; rw [dual_ground]

Depends on / 依赖: delete_eq_delete_iff, dual_delete_dual, dual_ground, dual_inj
-/
lemma contract_eq_contract_iff : M ／ C₁ = M ／ C₂ ↔ C₁ inter M.E = C₂ inter M.E := by
  rw [← dual_delete_dual]; rw [← dual_delete_dual]; rw [dual_inj]; rw [delete_eq_delete_iff]; rw [dual_ground]

/--
lemma `contract_inter_ground_eq` / 引理 `contract_inter_ground_eq`

English:
lemma contract_inter_ground_eq
  given: (M : Matroid α) (C : Set α)
  statement: M ／ (C inter M.E) = M ／ C
  proof: by
  rw [← dual_delete_dual]; rw [← dual_ground]; rw [delete_inter_ground_eq]; rw [dual_delete_dual]

@[aesop unsafe 10% (rule_sets := [Matroid])]

中文:
引理 contract_inter_ground_eq
  条件: (M : Matroid α) (C : Set α)
  结论: M ／ (C inter M.E) = M ／ C
  证明: by
  rw [← dual_delete_dual]; rw [← dual_ground]; rw [delete_inter_ground_eq]; rw [dual_delete_dual]

@[aesop unsafe 10% (rule_sets := [Matroid])]
-/
@[simp] lemma contract_inter_ground_eq (M : Matroid α) (C : Set α) : M ／ (C inter M.E) = M ／ C := by
  rw [← dual_delete_dual]; rw [← dual_ground]; rw [delete_inter_ground_eq]; rw [dual_delete_dual]

@[aesop unsafe 10% (rule_sets := [Matroid])]
/--
lemma `contract_ground_subset_ground` / 引理 `contract_ground_subset_ground`

English:
lemma contract_ground_subset_ground
  given: (M : Matroid α) (C : Set α)
  statement: (M ／ C).E subseteq M.E
  proof: (M.contract_ground C).trans_subset sdiff_subset

中文:
引理 contract_ground_subset_ground
  条件: (M : Matroid α) (C : Set α)
  结论: (M ／ C).E subseteq M.E
  证明: (M.contract_ground C).trans_subset sdiff_subset

Depends on / 依赖: M.contract_ground, contract_ground, sdiff_subset, trans_subset
-/
lemma contract_ground_subset_ground (M : Matroid α) (C : Set α) : (M ／ C).E subseteq M.E :=
  (M.contract_ground C).trans_subset sdiff_subset


/--
lemma `coindep_contract_iff` / 引理 `coindep_contract_iff`

English:
lemma coindep_contract_iff
  statement: (M ／ C).Coindep X ↔ M.Coindep X ∧ Disjoint X C
  proof: by
  rw [coindep_def]; rw [dual_contract]; rw [delete_indep_iff]; rw [← coindep_def]

中文:
引理 coindep_contract_iff
  结论: (M ／ C).Coindep X ↔ M.Coindep X ∧ Disjoint X C
  证明: by
  rw [coindep_def]; rw [dual_contract]; rw [delete_indep_iff]; rw [← coindep_def]

Depends on / 依赖: coindep_def, delete_indep_iff, dual_contract
-/
lemma coindep_contract_iff : (M ／ C).Coindep X ↔ M.Coindep X ∧ Disjoint X C := by
  rw [coindep_def]; rw [dual_contract]; rw [delete_indep_iff]; rw [← coindep_def]

/--
lemma `Coindep.coindep_contract_of_disjoint` / 引理 `Coindep.coindep_contract_of_disjoint`

English:
lemma Coindep.coindep_contract_of_disjoint
  given: (hX : M.Coindep X) (hXC : Disjoint X C)
  proof: coindep_contract_iff.2 ⟨hX, hXC⟩

中文:
引理 Coindep.coindep_contract_of_disjoint
  条件: (hX : M.Coindep X) (hXC : Disjoint X C)
  证明: coindep_contract_iff.2 ⟨hX, hXC⟩

Depends on / 依赖: coindep_contract_iff
-/
lemma Coindep.coindep_contract_of_disjoint (hX : M.Coindep X) (hXC : Disjoint X C) :
    (M ／ C).Coindep X :=
  coindep_contract_iff.2 ⟨hX, hXC⟩

/--
lemma `contract_isCocircuit_iff` / 引理 `contract_isCocircuit_iff`

English:
lemma contract_isCocircuit_iff
  proof: by
  rw [isCocircuit_def]; rw [dual_contract]; rw [delete_isCircuit_iff]

中文:
引理 contract_isCocircuit_iff
  证明: by
  rw [isCocircuit_def]; rw [dual_contract]; rw [delete_isCircuit_iff]
-/
@[simp] lemma contract_isCocircuit_iff :
    (M ／ C).IsCocircuit K ↔ M.IsCocircuit K ∧ Disjoint K C := by
  rw [isCocircuit_def]; rw [dual_contract]; rw [delete_isCircuit_iff]

/--
lemma `Indep.contract_isBase_iff` / 引理 `Indep.contract_isBase_iff`

English:
lemma Indep.contract_isBase_iff
  given: (hI : M.Indep I)
  proof: by
  rw [← dual_delete_dual]; rw [dual_isBase_iff']; rw [delete_ground]; rw [dual_ground]; rw [delete_isBase_iff]; rw [subset_sdiff]; rw [← and_assoc]; rw [and_congr_left_iff]; rw [← dual_dual M]; rw [dual_isBase_iff']; rw [dual_dual]; rw [dual_dual]; rw [union_comm]; rw [dual_ground]; rw [union_sub

中文:
引理 Indep.contract_isBase_iff
  条件: (hI : M.Indep I)
  证明: by
  rw [← dual_delete_dual]; rw [dual_isBase_iff']; rw [delete_ground]; rw [dual_ground]; rw [delete_isBase_iff]; rw [subset_sdiff]; rw [← and_assoc]; rw [and_congr_left_iff]; rw [← dual_dual M]; rw [dual_isBase_iff']; rw [dual_dual]; rw [dual_dual]; rw [union_comm]; rw [dual_ground]; rw [union_sub

Depends on / 依赖: Spanning, Spanning.isBase_restrict_iff, and_assoc, and_congr_left_iff, and_iff_left, and_iff_right, delete_ground, delete_isBase_iff, dual_delete_dual, dual_dual, dual_ground, dual_isBase_iff, hI.subset_ground, isBase_restrict_iff, sdiff_sdiff, sdiff_subset_sdiff_right, subset, subset_ground, subset_sdiff, union_comm
-/
lemma Indep.contract_isBase_iff (hI : M.Indep I) :
    (M ／ I).IsBase B ↔ M.IsBase (B union I) ∧ Disjoint B I := by
  rw [← dual_delete_dual]; rw [dual_isBase_iff']; rw [delete_ground]; rw [dual_ground]; rw [delete_isBase_iff]; rw [subset_sdiff]; rw [← and_assoc]; rw [and_congr_left_iff]; rw [← dual_dual M]; rw [dual_isBase_iff']; rw [dual_dual]; rw [dual_dual]; rw [union_comm]; rw [dual_ground]; rw [union_subset_iff]; rw [and_iff_right hI.subset_ground]; rw [and_congr_left_iff]; rw [← isBase_restrict_iff]; rw [sdiff_sdiff]; rw [Spanning.isBase_restrict_iff]; rw [and_iff_left (sdiff_subset_sdiff_right subset_union_left)]
  · simp
  rwa [← dual_ground, ← coindep_iff_compl_spanning, dual_coindep_iff]

/--
lemma `Indep.contract_indep_iff` / 引理 `Indep.contract_indep_iff`

English:
lemma Indep.contract_indep_iff
  given: (hI : M.Indep I)
  proof: by
  simp_rw [indep_iff, hI.contract_isBase_iff, union_subset_iff]
  exact ⟨fun ⟨B, ⟨hBI, hdj⟩, hJB⟩ => ⟨disjoint_of_subset_left hJB hdj, _, hBI,
    hJB.trans subset_union_left, subset_union_right⟩,
    fun ⟨hdj, B, hB, hJB, hIB⟩ => ⟨B \ I,⟨by simpa [union_eq_self_of_subset_right hIB],
      disjoi

中文:
引理 Indep.contract_indep_iff
  条件: (hI : M.Indep I)
  证明: by
  simp_rw [indep_iff, hI.contract_isBase_iff, union_subset_iff]
  exact ⟨fun ⟨B, ⟨hBI, hdj⟩, hJB⟩ => ⟨disjoint_of_subset_left hJB hdj, _, hBI,
    hJB.trans subset_union_left, subset_union_right⟩,
    fun ⟨hdj, B, hB, hJB, hIB⟩ => ⟨B \ I,⟨by simpa [union_eq_self_of_subset_right hIB],
      disjoi

Depends on / 依赖: contract_isBase_iff, disjoint_of_subset_left, disjoint_sdiff_left, hI.contract_isBase_iff, hJB.trans, indep_iff, simp_rw, subset_sdiff, subset_union_left, subset_union_right, union_eq_self_of_subset_right, union_subset_iff
-/
lemma Indep.contract_indep_iff (hI : M.Indep I) :
    (M ／ I).Indep J ↔ Disjoint J I ∧ M.Indep (J union I) := by
  simp_rw [indep_iff, hI.contract_isBase_iff, union_subset_iff]
  exact ⟨fun ⟨B, ⟨hBI, hdj⟩, hJB⟩ => ⟨disjoint_of_subset_left hJB hdj, _, hBI,
    hJB.trans subset_union_left, subset_union_right⟩,
    fun ⟨hdj, B, hB, hJB, hIB⟩ => ⟨B \ I,⟨by simpa [union_eq_self_of_subset_right hIB],
      disjoint_sdiff_left⟩, subset_sdiff.2 ⟨hJB, hdj⟩ ⟩⟩

/--
lemma `IsNonloop.contractElem_indep_iff` / 引理 `IsNonloop.contractElem_indep_iff`

English:
lemma IsNonloop.contractElem_indep_iff
  given: (he : M.IsNonloop e)
  proof: by
  simp [he.indep.contract_indep_iff]

中文:
引理 IsNonloop.contractElem_indep_iff
  条件: (he : M.IsNonloop e)
  证明: by
  simp [he.indep.contract_indep_iff]

Depends on / 依赖: contract_indep_iff, he.indep.contract_indep_iff
-/
lemma IsNonloop.contractElem_indep_iff (he : M.IsNonloop e) :
    (M ／ {e}).Indep I ↔ e ∉ I ∧ M.Indep (insert e I) := by
  simp [he.indep.contract_indep_iff]

/--
lemma `Indep.union_indep_iff_contract_indep` / 引理 `Indep.union_indep_iff_contract_indep`

English:
lemma Indep.union_indep_iff_contract_indep
  given: (hI : M.Indep I)
  proof: by
  rw [hI.contract_indep_iff]; rw [and_iff_right disjoint_sdiff_left]; rw [sdiff_union_self]; rw [union_comm]

中文:
引理 Indep.union_indep_iff_contract_indep
  条件: (hI : M.Indep I)
  证明: by
  rw [hI.contract_indep_iff]; rw [and_iff_right disjoint_sdiff_left]; rw [sdiff_union_self]; rw [union_comm]

Depends on / 依赖: and_iff_right, contract_indep_iff, disjoint_sdiff_left, hI.contract_indep_iff, sdiff_union_self, union_comm
-/
lemma Indep.union_indep_iff_contract_indep (hI : M.Indep I) :
    M.Indep (I union J) ↔ (M ／ I).Indep (J \ I) := by
  rw [hI.contract_indep_iff]; rw [and_iff_right disjoint_sdiff_left]; rw [sdiff_union_self]; rw [union_comm]

/--
lemma `Indep.diff_indep_contract_of_subset` / 引理 `Indep.diff_indep_contract_of_subset`

English:
lemma Indep.diff_indep_contract_of_subset
  given: (hJ : M.Indep J) (hIJ : I subseteq J)
  proof: by
  rwa [← (hJ.subset hIJ).union_indep_iff_contract_indep, union_eq_self_of_subset_left hIJ]

中文:
引理 Indep.diff_indep_contract_of_subset
  条件: (hJ : M.Indep J) (hIJ : I subseteq J)
  证明: by
  rwa [← (hJ.subset hIJ).union_indep_iff_contract_indep, union_eq_self_of_subset_left hIJ]

Depends on / 依赖: hJ.subset, subset, union_eq_self_of_subset_left, union_indep_iff_contract_indep
-/
lemma Indep.diff_indep_contract_of_subset (hJ : M.Indep J) (hIJ : I subseteq J) :
    (M ／ I).Indep (J \ I) := by
  rwa [← (hJ.subset hIJ).union_indep_iff_contract_indep, union_eq_self_of_subset_left hIJ]

/--
lemma `Indep.contract_dep_iff` / 引理 `Indep.contract_dep_iff`

English:
lemma Indep.contract_dep_iff
  given: (hI : M.Indep I)
  proof: by
  rw [dep_iff]; rw [hI.contract_indep_iff]; rw [dep_iff]; rw [contract_ground]; rw [subset_sdiff]; rw [disjoint_comm]; rw [union_subset_iff]; rw [and_iff_left hI.subset_ground]
  tauto

中文:
引理 Indep.contract_dep_iff
  条件: (hI : M.Indep I)
  证明: by
  rw [dep_iff]; rw [hI.contract_indep_iff]; rw [dep_iff]; rw [contract_ground]; rw [subset_sdiff]; rw [disjoint_comm]; rw [union_subset_iff]; rw [and_iff_left hI.subset_ground]
  tauto

Depends on / 依赖: and_iff_left, contract_ground, contract_indep_iff, dep_iff, disjoint_comm, hI.contract_indep_iff, hI.subset_ground, subset_ground, subset_sdiff, union_subset_iff
-/
lemma Indep.contract_dep_iff (hI : M.Indep I) :
    (M ／ I).Dep J ↔ Disjoint J I ∧ M.Dep (J union I) := by
  rw [dep_iff]; rw [hI.contract_indep_iff]; rw [dep_iff]; rw [contract_ground]; rw [subset_sdiff]; rw [disjoint_comm]; rw [union_subset_iff]; rw [and_iff_left hI.subset_ground]
  tauto

/-! ### Bases -/

/--
lemma `IsBasis.contract_eq_contract_delete` / 引理 `IsBasis.contract_eq_contract_delete`

English:
lemma IsBasis.contract_eq_contract_delete
  given: (hI : M.IsBasis I X)
  statement: M ／ X = M ／ I ＼ (X \ I)
  proof: by
  nth_rw 1 [← sdiff_union_of_subset hI.subset, ← dual_inj, dual_contract_delete, dual_contract,
    union_comm, ← delete_delete, ext_iff_indep]
  refine ⟨rfl, fun J hJ => ?_⟩
  have hss : X \ I subseteq (M✶ ＼ I).coloops := fun e he => by
    rw [← dual_contract]; rw [dual_coloops]; rw [← IsLoop];

中文:
引理 IsBasis.contract_eq_contract_delete
  条件: (hI : M.IsBasis I X)
  结论: M ／ X = M ／ I ＼ (X \ I)
  证明: by
  nth_rw 1 [← sdiff_union_of_subset hI.subset, ← dual_inj, dual_contract_delete, dual_contract,
    union_comm, ← delete_delete, ext_iff_indep]
  refine ⟨rfl, fun J hJ => ?_⟩
  have hss : X \ I subseteq (M✶ ＼ I).coloops := fun e he => by
    rw [← dual_contract]; rw [dual_coloops]; rw [← IsLoop];

Depends on / 依赖: IsLoop, M.subse, and_iff_right, closure_eq_closure, coloops, contract_dep_iff, delete_delete, dual_coloops, dual_contract, dual_contract_delete, dual_inj, ext_iff_indep, hI.closure_eq_closure, hI.indep.contract_dep_iff, hI.indep.insert_dep_iff, hI.subset, insert_dep_iff, nth_rw, sdiff_subset_sdiff_left, sdiff_union_of_subset
-/
lemma IsBasis.contract_eq_contract_delete (hI : M.IsBasis I X) : M ／ X = M ／ I ＼ (X \ I) := by
  nth_rw 1 [← sdiff_union_of_subset hI.subset, ← dual_inj, dual_contract_delete, dual_contract,
    union_comm, ← delete_delete, ext_iff_indep]
  refine ⟨rfl, fun J hJ => ?_⟩
  have hss : X \ I subseteq (M✶ ＼ I).coloops := fun e he => by
    rw [← dual_contract]; rw [dual_coloops]; rw [← IsLoop]; rw [← singleton_dep]; rw [hI.indep.contract_dep_iff]; rw [singleton_union]; rw [and_iff_right (by simpa using he.2)]; rw [hI.indep.insert_dep_iff]; rw [hI.closure_eq_closure]
    exact sdiff_subset_sdiff_left (M.subset_closure X) he
  rw [((coloops_indep _).subset hss).contract_indep_iff]; rw [delete_indep_iff]; rw [union_indep_iff_indep_of_subset_coloops hss]; rw [and_comm]

/--
lemma `Indep.union_isBasis_union_of_contract_isBasis` / 引理 `Indep.union_isBasis_union_of_contract_isBasis`

English:
lemma Indep.union_isBasis_union_of_contract_isBasis
  given: (hI : M.Indep I) (hB : (M ／ I).IsBasis J X)
  proof: by
  simp_rw [IsBasis, hI.contract_indep_iff, contract_ground, subset_sdiff,
    maximal_subset_iff, and_imp] at hB
  refine hB.1.1.1.2.isBasis_of_maximal_subset (union_subset_union_left _ hB.1.1.2)
    fun K hK hKJ hKX => ?_
  rw [union_subset_iff] at hKJ
  rw [hB.1.2 (t := K \ I) disjoint_sdiff_le

中文:
引理 Indep.union_isBasis_union_of_contract_isBasis
  条件: (hI : M.Indep I) (hB : (M ／ I).IsBasis J X)
  证明: by
  simp_rw [IsBasis, hI.contract_indep_iff, contract_ground, subset_sdiff,
    maximal_subset_iff, and_imp] at hB
  refine hB.1.1.1.2.isBasis_of_maximal_subset (union_subset_union_left _ hB.1.1.2)
    fun K hK hKJ hKX => ?_
  rw [union_subset_iff] at hKJ
  rw [hB.1.2 (t := K \ I) disjoint_sdiff_le

Depends on / 依赖: IsBasis, and_imp, contract_ground, contract_indep_iff, disjoint_sdiff_left, hI.contract_indep_iff, isBasis_of_maximal_subset, maximal_subset_iff, sdiff_subset_iff, sdiff_union_of_subset, simp_rw, subset_sdiff, union_comm, union_subset_iff, union_subset_union_left
-/
lemma Indep.union_isBasis_union_of_contract_isBasis (hI : M.Indep I) (hB : (M ／ I).IsBasis J X) :
    M.IsBasis (J union I) (X union I) := by
  simp_rw [IsBasis, hI.contract_indep_iff, contract_ground, subset_sdiff,
    maximal_subset_iff, and_imp] at hB
  refine hB.1.1.1.2.isBasis_of_maximal_subset (union_subset_union_left _ hB.1.1.2)
    fun K hK hKJ hKX => ?_
  rw [union_subset_iff] at hKJ
  rw [hB.1.2 (t := K \ I) disjoint_sdiff_left (by simpa [sdiff_union_of_subset hKJ.2])
    (sdiff_subset_iff.2 (by rwa [union_comm])) (subset_sdiff.2 ⟨hKJ.1, hB.1.1.1.1⟩),
    sdiff_union_of_subset hKJ.2]

/--
lemma `IsBasis'.contract_isBasis'_sdiff_sdiff_of_subset` / 引理 `IsBasis'.contract_isBasis'_sdiff_sdiff_of_subset`

English:
lemma IsBasis'.contract_isBasis'_sdiff_sdiff_of_subset
  given: (hIX : M.IsBasis' I X) (hJI : J subseteq I)
  proof: by
  suffices forall ⦃K⦄, Disjoint K J -> M.Indep (K union J) -> K subseteq X -> I subseteq K union J -> K subseteq I by
    simpa +contextual [IsBasis', (hIX.indep.subset hJI).contract_indep_iff,
      subset_sdiff, maximal_subset_iff, disjoint_sdiff_left,
      union_eq_self_of_subset_right hJI, h

中文:
引理 IsBasis'.contract_isBasis'_sdiff_sdiff_of_subset
  条件: (hIX : M.IsBasis' I X) (hJI : J subseteq I)
  证明: by
  suffices forall ⦃K⦄, Disjoint K J -> M.Indep (K union J) -> K subseteq X -> I subseteq K union J -> K subseteq I by
    simpa +contextual [IsBasis', (hIX.indep.subset hJI).contract_indep_iff,
      subset_sdiff, maximal_subset_iff, disjoint_sdiff_left,
      union_eq_self_of_subset_right hJI, h
-/
lemma IsBasis'.contract_isBasis'_sdiff_sdiff_of_subset (hIX : M.IsBasis' I X) (hJI : J subseteq I) :
    (M ／ J).IsBasis' (I \ J) (X \ J) := by
  suffices forall ⦃K⦄, Disjoint K J -> M.Indep (K union J) -> K subseteq X -> I subseteq K union J -> K subseteq I by
    simpa +contextual [IsBasis', (hIX.indep.subset hJI).contract_indep_iff,
      subset_sdiff, maximal_subset_iff, disjoint_sdiff_left,
      union_eq_self_of_subset_right hJI, hIX.indep, sdiff_subset.trans hIX.subset,
      sdiff_subset_iff, subset_antisymm_iff, union_comm J]
  exact fun K hJK hKJi hKX hIJK => by
    simp [hIX.eq_of_subset_indep hKJi hIJK (union_subset hKX (hJI.trans hIX.subset))]

@[deprecated (since := "2026-06-03")]
alias IsBasis'.contract_isBasis'_diff_diff_of_subset :=
  IsBasis'.contract_isBasis'_sdiff_sdiff_of_subset

/--
lemma `IsBasis'.contract_isBasis'_sdiff_of_subset` / 引理 `IsBasis'.contract_isBasis'_sdiff_of_subset`

English:
lemma IsBasis'.contract_isBasis'_sdiff_of_subset
  given: (hIX : M.IsBasis' I X) (hJI : J subseteq I)
  proof: by
  simpa [isBasis'_iff_isBasis_inter_ground, inter_sdiff_assoc, ← sdiff_inter_distrib_right] using
    (hIX.contract_isBasis'_sdiff_sdiff_of_subset hJI).isBasis_inter_ground

@[deprecated (since := "2026-06-03")]
alias IsBasis'.contract_isBasis'_diff_of_subset := IsBasis'.contract_isBasis'_sdiff_o

中文:
引理 IsBasis'.contract_isBasis'_sdiff_of_subset
  条件: (hIX : M.IsBasis' I X) (hJI : J subseteq I)
  证明: by
  simpa [isBasis'_iff_isBasis_inter_ground, inter_sdiff_assoc, ← sdiff_inter_distrib_right] using
    (hIX.contract_isBasis'_sdiff_sdiff_of_subset hJI).isBasis_inter_ground

@[deprecated (since := "2026-06-03")]
alias IsBasis'.contract_isBasis'_diff_of_subset := IsBasis'.contract_isBasis'_sdiff_o
-/
lemma IsBasis'.contract_isBasis'_sdiff_of_subset (hIX : M.IsBasis' I X) (hJI : J subseteq I) :
    (M ／ J).IsBasis' (I \ J) X := by
  simpa [isBasis'_iff_isBasis_inter_ground, inter_sdiff_assoc, ← sdiff_inter_distrib_right] using
    (hIX.contract_isBasis'_sdiff_sdiff_of_subset hJI).isBasis_inter_ground

@[deprecated (since := "2026-06-03")]
alias IsBasis'.contract_isBasis'_diff_of_subset := IsBasis'.contract_isBasis'_sdiff_of_subset

/--
lemma `IsBasis.contract_isBasis_sdiff_sdiff_of_subset` / 引理 `IsBasis.contract_isBasis_sdiff_sdiff_of_subset`

English:
lemma IsBasis.contract_isBasis_sdiff_sdiff_of_subset
  given: (hIX : M.IsBasis I X) (hJI : J subseteq I)
  proof: by
  have h := (hIX.isBasis'.contract_isBasis'_sdiff_of_subset hJI).isBasis_inter_ground
  rwa [contract_ground, ← inter_sdiff_assoc, inter_eq_self_of_subset_left hIX.subset_ground] at h

@[deprecated (since := "2026-06-03")]
alias IsBasis.contract_isBasis_diff_diff_of_subset := IsBasis.contract_isB

中文:
引理 IsBasis.contract_isBasis_sdiff_sdiff_of_subset
  条件: (hIX : M.IsBasis I X) (hJI : J subseteq I)
  证明: by
  have h := (hIX.isBasis'.contract_isBasis'_sdiff_of_subset hJI).isBasis_inter_ground
  rwa [contract_ground, ← inter_sdiff_assoc, inter_eq_self_of_subset_left hIX.subset_ground] at h

@[deprecated (since := "2026-06-03")]
alias IsBasis.contract_isBasis_diff_diff_of_subset := IsBasis.contract_isB

Depends on / 依赖: _sdiff_of_subset, contract_ground, contract_isBasis, hIX.isBasis, hIX.subset_ground, inter_eq_self_of_subset_left, inter_sdiff_assoc, isBasis, isBasis_inter_ground, subset_ground
-/
lemma IsBasis.contract_isBasis_sdiff_sdiff_of_subset (hIX : M.IsBasis I X) (hJI : J subseteq I) :
    (M ／ J).IsBasis (I \ J) (X \ J) := by
  have h := (hIX.isBasis'.contract_isBasis'_sdiff_of_subset hJI).isBasis_inter_ground
  rwa [contract_ground, ← inter_sdiff_assoc, inter_eq_self_of_subset_left hIX.subset_ground] at h

@[deprecated (since := "2026-06-03")]
alias IsBasis.contract_isBasis_diff_diff_of_subset := IsBasis.contract_isBasis_sdiff_sdiff_of_subset

/--
lemma `IsBasis.contract_sdiff_isBasis_sdiff` / 引理 `IsBasis.contract_sdiff_isBasis_sdiff`

English:
lemma IsBasis.contract_sdiff_isBasis_sdiff
  statement: (hIX : M.IsBasis I X) (hJY : M.IsBasis J Y)
  proof: by
  refine (hJY.contract_isBasis_sdiff_sdiff_of_subset hIJ).isBasis_subset ?_ ?_
  · rw [subset_sdiff, and_iff_right (sdiff_subset.trans hJY.subset),
      hIX.eq_of_subset_indep (hJY.indep.inter_right X) (subset_inter hIJ hIX.subset)
      inter_subset_right, sdiff_self_inter]
    exact disjoint_s

中文:
引理 IsBasis.contract_sdiff_isBasis_sdiff
  结论: (hIX : M.IsBasis I X) (hJY : M.IsBasis J Y)
  证明: by
  refine (hJY.contract_isBasis_sdiff_sdiff_of_subset hIJ).isBasis_subset ?_ ?_
  · rw [subset_sdiff, and_iff_right (sdiff_subset.trans hJY.subset),
      hIX.eq_of_subset_indep (hJY.indep.inter_right X) (subset_inter hIJ hIX.subset)
      inter_subset_right, sdiff_self_inter]
    exact disjoint_s

Depends on / 依赖: and_iff_right, contract_isBasis_sdiff_sdiff_of_subset, disjoint_sdiff_left, eq_of_subset_indep, hIX.eq_of_subset_indep, hIX.subset, hJY.contract_isBasis_sdiff_sdiff_of_subset, hJY.indep.inter_right, hJY.subset, inter_right, inter_subset_right, isBasis_subset, sdiff_self_inter, sdiff_subset, sdiff_subset.trans, sdiff_subset_sdiff_right, subset, subset_inter, subset_sdiff
-/
lemma IsBasis.contract_sdiff_isBasis_sdiff (hIX : M.IsBasis I X) (hJY : M.IsBasis J Y)
    (hIJ : I subseteq J) : (M ／ I).IsBasis (J \ I) (Y \ X) := by
  refine (hJY.contract_isBasis_sdiff_sdiff_of_subset hIJ).isBasis_subset ?_ ?_
  · rw [subset_sdiff, and_iff_right (sdiff_subset.trans hJY.subset),
      hIX.eq_of_subset_indep (hJY.indep.inter_right X) (subset_inter hIJ hIX.subset)
      inter_subset_right, sdiff_self_inter]
    exact disjoint_sdiff_left
  refine sdiff_subset_sdiff_right hIX.subset

@[deprecated (since := "2026-06-03")]
alias IsBasis.contract_diff_isBasis_diff := IsBasis.contract_sdiff_isBasis_sdiff

/--
lemma `IsBasis'.contract_isBasis_union_union` / 引理 `IsBasis'.contract_isBasis_union_union`

English:
lemma IsBasis'.contract_isBasis_union_union
  statement: (h : M.IsBasis' (J union I) (X union I))
  proof: by
  simpa [hJI.sdiff_eq_left, hXI.sdiff_eq_left] using
    h.contract_isBasis'_sdiff_sdiff_of_subset subset_union_right

中文:
引理 IsBasis'.contract_isBasis_union_union
  结论: (h : M.IsBasis' (J union I) (X union I))
  证明: by
  simpa [hJI.sdiff_eq_left, hXI.sdiff_eq_left] using
    h.contract_isBasis'_sdiff_sdiff_of_subset subset_union_right
-/
lemma IsBasis'.contract_isBasis_union_union (h : M.IsBasis' (J union I) (X union I))
    (hJI : Disjoint J I) (hXI : Disjoint X I) : (M ／ I).IsBasis' J X := by
  simpa [hJI.sdiff_eq_left, hXI.sdiff_eq_left] using
    h.contract_isBasis'_sdiff_sdiff_of_subset subset_union_right

/--
lemma `IsBasis.contract_isBasis_union_union` / 引理 `IsBasis.contract_isBasis_union_union`

English:
lemma IsBasis.contract_isBasis_union_union
  statement: (h : M.IsBasis (J union I) (X union I))
  proof: by
refine (isBasis'_iff_isBasis ?_).1 h.isBasis'.contract_isBasis_union_union hJI hXI
  rw [contract_ground]; rw [subset_sdiff]; rw [and_iff_left hXI]
  exact subset_union_left.trans h.subset_ground

中文:
引理 IsBasis.contract_isBasis_union_union
  结论: (h : M.IsBasis (J union I) (X union I))
  证明: by
refine (isBasis'_iff_isBasis ?_).1 h.isBasis'.contract_isBasis_union_union hJI hXI
  rw [contract_ground]; rw [subset_sdiff]; rw [and_iff_left hXI]
  exact subset_union_left.trans h.subset_ground

Depends on / 依赖: _iff_isBasis, and_iff_left, contract_ground, contract_isBasis_union_union, h.isBasis, h.subset_ground, isBasis, subset_ground, subset_sdiff, subset_union_left, subset_union_left.trans
-/
lemma IsBasis.contract_isBasis_union_union (h : M.IsBasis (J union I) (X union I))
    (hJI : Disjoint J I) (hXI : Disjoint X I) : (M ／ I).IsBasis J X := by
refine (isBasis'_iff_isBasis ?_).1 h.isBasis'.contract_isBasis_union_union hJI hXI
  rw [contract_ground]; rw [subset_sdiff]; rw [and_iff_left hXI]
  exact subset_union_left.trans h.subset_ground

/--
lemma `IsBasis'.contract_eq_contract_delete` / 引理 `IsBasis'.contract_eq_contract_delete`

English:
lemma IsBasis'.contract_eq_contract_delete
  given: (hI : M.IsBasis' I X)
  statement: M ／ X = M ／ I ＼ (X \ I)
  proof: by
  rw [← contract_inter_ground_eq]; rw [hI.isBasis_inter_ground.contract_eq_contract_delete]; rw [eq_comm]; rw [← delete_inter_ground_eq]; rw [contract_ground]; rw [sdiff_eq]; rw [sdiff_eq]; rw [← inter_inter_distrib_right]; rw [← sdiff_eq]

中文:
引理 IsBasis'.contract_eq_contract_delete
  条件: (hI : M.IsBasis' I X)
  结论: M ／ X = M ／ I ＼ (X \ I)
  证明: by
  rw [← contract_inter_ground_eq]; rw [hI.isBasis_inter_ground.contract_eq_contract_delete]; rw [eq_comm]; rw [← delete_inter_ground_eq]; rw [contract_ground]; rw [sdiff_eq]; rw [sdiff_eq]; rw [← inter_inter_distrib_right]; rw [← sdiff_eq]
-/
lemma IsBasis'.contract_eq_contract_delete (hI : M.IsBasis' I X) : M ／ X = M ／ I ＼ (X \ I) := by
  rw [← contract_inter_ground_eq]; rw [hI.isBasis_inter_ground.contract_eq_contract_delete]; rw [eq_comm]; rw [← delete_inter_ground_eq]; rw [contract_ground]; rw [sdiff_eq]; rw [sdiff_eq]; rw [← inter_inter_distrib_right]; rw [← sdiff_eq]

/--
lemma `IsBasis'.contract_indep_iff` / 引理 `IsBasis'.contract_indep_iff`

English:
lemma IsBasis'.contract_indep_iff
  given: (hI : M.IsBasis' I X)
  proof: by
  rw [hI.contract_eq_contract_delete]; rw [delete_indep_iff]; rw [hI.indep.contract_indep_iff]; rw [and_comm]; rw [← and_assoc]; rw [← disjoint_union_right]; rw [sdiff_union_self]; rw [union_eq_self_of_subset_right hI.subset]; rw [and_comm]; rw [disjoint_comm]

中文:
引理 IsBasis'.contract_indep_iff
  条件: (hI : M.IsBasis' I X)
  证明: by
  rw [hI.contract_eq_contract_delete]; rw [delete_indep_iff]; rw [hI.indep.contract_indep_iff]; rw [and_comm]; rw [← and_assoc]; rw [← disjoint_union_right]; rw [sdiff_union_self]; rw [union_eq_self_of_subset_right hI.subset]; rw [and_comm]; rw [disjoint_comm]
-/
lemma IsBasis'.contract_indep_iff (hI : M.IsBasis' I X) :
    (M ／ X).Indep J ↔ M.Indep (J union I) ∧ Disjoint X J := by
  rw [hI.contract_eq_contract_delete]; rw [delete_indep_iff]; rw [hI.indep.contract_indep_iff]; rw [and_comm]; rw [← and_assoc]; rw [← disjoint_union_right]; rw [sdiff_union_self]; rw [union_eq_self_of_subset_right hI.subset]; rw [and_comm]; rw [disjoint_comm]

/--
lemma `IsBasis.contract_indep_iff` / 引理 `IsBasis.contract_indep_iff`

English:
lemma IsBasis.contract_indep_iff
  given: (hI : M.IsBasis I X)
  proof: hI.isBasis'.contract_indep_iff

中文:
引理 IsBasis.contract_indep_iff
  条件: (hI : M.IsBasis I X)
  证明: hI.isBasis'.contract_indep_iff

Depends on / 依赖: contract_indep_iff, hI.isBasis, isBasis
-/
lemma IsBasis.contract_indep_iff (hI : M.IsBasis I X) :
    (M ／ X).Indep J ↔ M.Indep (J union I) ∧ Disjoint X J :=
  hI.isBasis'.contract_indep_iff

/--
lemma `IsBasis'.contract_dep_iff` / 引理 `IsBasis'.contract_dep_iff`

English:
lemma IsBasis'.contract_dep_iff
  given: (hI : M.IsBasis' I X) {D : Set α}
  proof: by
  rw [hI.contract_eq_contract_delete]; rw [delete_dep_iff]; rw [hI.indep.contract_dep_iff]; rw [and_comm]; rw [← and_assoc]; rw [← disjoint_union_right]; rw [sdiff_union_of_subset hI.subset]; rw [disjoint_comm]; rw [and_comm]

中文:
引理 IsBasis'.contract_dep_iff
  条件: (hI : M.IsBasis' I X) {D : Set α}
  证明: by
  rw [hI.contract_eq_contract_delete]; rw [delete_dep_iff]; rw [hI.indep.contract_dep_iff]; rw [and_comm]; rw [← and_assoc]; rw [← disjoint_union_right]; rw [sdiff_union_of_subset hI.subset]; rw [disjoint_comm]; rw [and_comm]
-/
lemma IsBasis'.contract_dep_iff (hI : M.IsBasis' I X) {D : Set α} :
    (M ／ X).Dep D ↔ M.Dep (D union I) ∧ Disjoint X D := by
  rw [hI.contract_eq_contract_delete]; rw [delete_dep_iff]; rw [hI.indep.contract_dep_iff]; rw [and_comm]; rw [← and_assoc]; rw [← disjoint_union_right]; rw [sdiff_union_of_subset hI.subset]; rw [disjoint_comm]; rw [and_comm]

/--
lemma `IsBasis.contract_dep_iff` / 引理 `IsBasis.contract_dep_iff`

English:
lemma IsBasis.contract_dep_iff
  given: (hI : M.IsBasis I X) {D : Set α}
  proof: hI.isBasis'.contract_dep_iff

中文:
引理 IsBasis.contract_dep_iff
  条件: (hI : M.IsBasis I X) {D : Set α}
  证明: hI.isBasis'.contract_dep_iff

Depends on / 依赖: contract_dep_iff, hI.isBasis, isBasis
-/
lemma IsBasis.contract_dep_iff (hI : M.IsBasis I X) {D : Set α} :
    (M ／ X).Dep D ↔ M.Dep (D union I) ∧ Disjoint X D :=
  hI.isBasis'.contract_dep_iff

/--
lemma `IsBasis.contract_indep_iff_of_disjoint` / 引理 `IsBasis.contract_indep_iff_of_disjoint`

English:
lemma IsBasis.contract_indep_iff_of_disjoint
  given: (hI : M.IsBasis I X) (hdj : Disjoint X J)
  proof: by
  rw [hI.contract_indep_iff]; rw [and_iff_left hdj]

中文:
引理 IsBasis.contract_indep_iff_of_disjoint
  条件: (hI : M.IsBasis I X) (hdj : Disjoint X J)
  证明: by
  rw [hI.contract_indep_iff]; rw [and_iff_left hdj]

Depends on / 依赖: and_iff_left, contract_indep_iff, hI.contract_indep_iff
-/
lemma IsBasis.contract_indep_iff_of_disjoint (hI : M.IsBasis I X) (hdj : Disjoint X J) :
    (M ／ X).Indep J ↔ M.Indep (J union I) := by
  rw [hI.contract_indep_iff]; rw [and_iff_left hdj]

/--
lemma `IsBasis.contract_indep_sdiff_iff` / 引理 `IsBasis.contract_indep_sdiff_iff`

English:
lemma IsBasis.contract_indep_sdiff_iff
  given: (hI : M.IsBasis I X)
  proof: by
  rw [hI.contract_indep_iff]; rw [and_iff_left disjoint_sdiff_right]

@[deprecated (since := "2026-06-03")]
alias IsBasis.contract_indep_diff_iff := IsBasis.contract_indep_sdiff_iff

中文:
引理 IsBasis.contract_indep_sdiff_iff
  条件: (hI : M.IsBasis I X)
  证明: by
  rw [hI.contract_indep_iff]; rw [and_iff_left disjoint_sdiff_right]

@[deprecated (since := "2026-06-03")]
alias IsBasis.contract_indep_diff_iff := IsBasis.contract_indep_sdiff_iff

Depends on / 依赖: and_iff_left, contract_indep_iff, disjoint_sdiff_right, hI.contract_indep_iff
-/
lemma IsBasis.contract_indep_sdiff_iff (hI : M.IsBasis I X) :
    (M ／ X).Indep (J \ X) ↔ M.Indep ((J \ X) union I) := by
  rw [hI.contract_indep_iff]; rw [and_iff_left disjoint_sdiff_right]

@[deprecated (since := "2026-06-03")]
alias IsBasis.contract_indep_diff_iff := IsBasis.contract_indep_sdiff_iff

/--
lemma `IsBasis'.contract_indep_sdiff_iff` / 引理 `IsBasis'.contract_indep_sdiff_iff`

English:
lemma IsBasis'.contract_indep_sdiff_iff
  given: (hI : M.IsBasis' I X)
  proof: by
  rw [hI.contract_indep_iff]; rw [and_iff_left disjoint_sdiff_right]

@[deprecated (since := "2026-06-03")]
alias IsBasis'.contract_indep_diff_iff := IsBasis'.contract_indep_sdiff_iff

中文:
引理 IsBasis'.contract_indep_sdiff_iff
  条件: (hI : M.IsBasis' I X)
  证明: by
  rw [hI.contract_indep_iff]; rw [and_iff_left disjoint_sdiff_right]

@[deprecated (since := "2026-06-03")]
alias IsBasis'.contract_indep_diff_iff := IsBasis'.contract_indep_sdiff_iff
-/
lemma IsBasis'.contract_indep_sdiff_iff (hI : M.IsBasis' I X) :
    (M ／ X).Indep (J \ X) ↔ M.Indep ((J \ X) union I) := by
  rw [hI.contract_indep_iff]; rw [and_iff_left disjoint_sdiff_right]

@[deprecated (since := "2026-06-03")]
alias IsBasis'.contract_indep_diff_iff := IsBasis'.contract_indep_sdiff_iff

/--
lemma `IsBasis.contract_isBasis_of_isBasis'` / 引理 `IsBasis.contract_isBasis_of_isBasis'`

English:
lemma IsBasis.contract_isBasis_of_isBasis'
  statement: (h : M.IsBasis I X) (hJC : M.IsBasis' J C)
  proof: by
  have hIX := h.subset
  have hJCss := hJC.subset
  rw [hJC.contract_eq_contract_delete]; rw [delete_isBasis_iff]
  refine ⟨contract_isBasis_union_union (h_ind.isBasis_of_subset_of_subset_closure ?_ ?_) ?_ ?_, ?_⟩
  rotate_left
  · rw [closure_union_congr_right hJC.closure_eq_closure, sdiff_union

中文:
引理 IsBasis.contract_isBasis_of_isBasis'
  结论: (h : M.IsBasis I X) (hJC : M.IsBasis' J C)
  证明: by
  have hIX := h.subset
  have hJCss := hJC.subset
  rw [hJC.contract_eq_contract_delete]; rw [delete_isBasis_iff]
  refine ⟨contract_isBasis_union_union (h_ind.isBasis_of_subset_of_subset_closure ?_ ?_) ?_ ?_, ?_⟩
  rotate_left
  · rw [closure_union_congr_right hJC.closure_eq_closure, sdiff_union

Depends on / 依赖: all_goals, closure_eq_closure, closure_union_congr_left, closure_union_congr_right, contract_eq_contract_delete, contract_isBasis_union_union, delete_isBasis_iff, h.closure_eq_closure, h.subset, h.subset_ground, hJC.closure_eq_closure, hJC.contract_eq_contract_delete, hJC.indep.subset_ground, hJC.subset, h_ind, h_ind.isBasis_of_subset_of_subset_closure, isBasis_of_subset_of_subset_closure, rotate_left, sdiff_subset, sdiff_subset.trans
-/
lemma IsBasis.contract_isBasis_of_isBasis' (h : M.IsBasis I X) (hJC : M.IsBasis' J C)
    (h_ind : M.Indep (I \ C union J)) : (M ／ C).IsBasis (I \ C) (X \ C) := by
  have hIX := h.subset
  have hJCss := hJC.subset
  rw [hJC.contract_eq_contract_delete]; rw [delete_isBasis_iff]
  refine ⟨contract_isBasis_union_union (h_ind.isBasis_of_subset_of_subset_closure ?_ ?_) ?_ ?_, ?_⟩
  rotate_left
  · rw [closure_union_congr_right hJC.closure_eq_closure, sdiff_union_self,
      closure_union_congr_left h.closure_eq_closure]
    exact subset_closure_of_subset' _ (by tauto_set)
      (union_subset (sdiff_subset.trans h.subset_ground) hJC.indep.subset_ground)
  all_goals tauto_set

/--
lemma `IsBasis'.contract_isBasis'` / 引理 `IsBasis'.contract_isBasis'`

English:
lemma IsBasis'.contract_isBasis'
  statement: (h : M.IsBasis' I X) (hJC : M.IsBasis' J C)
  proof: by
  rw [isBasis'_iff_isBasis_inter_ground]; rw [contract_ground]; rw [← sdiff_inter_distrib_right]
  exact h.isBasis_inter_ground.contract_isBasis_of_isBasis' hJC h_ind

中文:
引理 IsBasis'.contract_isBasis'
  结论: (h : M.IsBasis' I X) (hJC : M.IsBasis' J C)
  证明: by
  rw [isBasis'_iff_isBasis_inter_ground]; rw [contract_ground]; rw [← sdiff_inter_distrib_right]
  exact h.isBasis_inter_ground.contract_isBasis_of_isBasis' hJC h_ind
-/
lemma IsBasis'.contract_isBasis' (h : M.IsBasis' I X) (hJC : M.IsBasis' J C)
    (h_ind : M.Indep (I \ C union J)) : (M ／ C).IsBasis' (I \ C) (X \ C) := by
  rw [isBasis'_iff_isBasis_inter_ground]; rw [contract_ground]; rw [← sdiff_inter_distrib_right]
  exact h.isBasis_inter_ground.contract_isBasis_of_isBasis' hJC h_ind

/--
lemma `IsBasis.contract_isBasis` / 引理 `IsBasis.contract_isBasis`

English:
lemma IsBasis.contract_isBasis
  statement: (h : M.IsBasis I X) (hJC : M.IsBasis J C)
  proof: h.contract_isBasis_of_isBasis' hJC.isBasis' h_ind

中文:
引理 IsBasis.contract_isBasis
  结论: (h : M.IsBasis I X) (hJC : M.IsBasis J C)
  证明: h.contract_isBasis_of_isBasis' hJC.isBasis' h_ind

Depends on / 依赖: contract_isBasis_of_isBasis, h.contract_isBasis_of_isBasis, hJC.isBasis, h_ind, isBasis
-/
lemma IsBasis.contract_isBasis (h : M.IsBasis I X) (hJC : M.IsBasis J C)
    (h_ind : M.Indep (I \ C union J)) : (M ／ C).IsBasis (I \ C) (X \ C) :=
  h.contract_isBasis_of_isBasis' hJC.isBasis' h_ind

/--
lemma `IsBasis.contract_isBasis_of_disjoint` / 引理 `IsBasis.contract_isBasis_of_disjoint`

English:
lemma IsBasis.contract_isBasis_of_disjoint
  statement: (h : M.IsBasis I X) (hJC : M.IsBasis J C)
  proof: by
  have h' := h.contract_isBasis hJC
  rwa [(hdj.mono_right h.subset).sdiff_eq_right, hdj.sdiff_eq_right, imp_iff_right h_ind] at h'

中文:
引理 IsBasis.contract_isBasis_of_disjoint
  结论: (h : M.IsBasis I X) (hJC : M.IsBasis J C)
  证明: by
  have h' := h.contract_isBasis hJC
  rwa [(hdj.mono_right h.subset).sdiff_eq_right, hdj.sdiff_eq_right, imp_iff_right h_ind] at h'

Depends on / 依赖: contract_isBasis, h.contract_isBasis, h.subset, h_ind, hdj.mono_right, hdj.sdiff_eq_right, imp_iff_right, mono_right, sdiff_eq_right, subset
-/
lemma IsBasis.contract_isBasis_of_disjoint (h : M.IsBasis I X) (hJC : M.IsBasis J C)
    (hdj : Disjoint C X) (h_ind : M.Indep (I union J)) : (M ／ C).IsBasis I X := by
  have h' := h.contract_isBasis hJC
  rwa [(hdj.mono_right h.subset).sdiff_eq_right, hdj.sdiff_eq_right, imp_iff_right h_ind] at h'

/--
lemma `IsBasis'.contract_isBasis_of_indep` / 引理 `IsBasis'.contract_isBasis_of_indep`

English:
lemma IsBasis'.contract_isBasis_of_indep
  given: (h : M.IsBasis' I X) (h_ind : M.Indep (I union J))
  proof: h.contract_isBasis' (h_ind.subset subset_union_right).isBasis_self.isBasis' (by simpa)

中文:
引理 IsBasis'.contract_isBasis_of_indep
  条件: (h : M.IsBasis' I X) (h_ind : M.Indep (I union J))
  证明: h.contract_isBasis' (h_ind.subset subset_union_right).isBasis_self.isBasis' (by simpa)
-/
lemma IsBasis'.contract_isBasis_of_indep (h : M.IsBasis' I X) (h_ind : M.Indep (I union J)) :
    (M ／ J).IsBasis' (I \ J) (X \ J) :=
  h.contract_isBasis' (h_ind.subset subset_union_right).isBasis_self.isBasis' (by simpa)

/--
lemma `IsBasis.contract_isBasis_of_indep` / 引理 `IsBasis.contract_isBasis_of_indep`

English:
lemma IsBasis.contract_isBasis_of_indep
  given: (h : M.IsBasis I X) (h_ind : M.Indep (I union J))
  proof: h.contract_isBasis (h_ind.subset subset_union_right).isBasis_self (by simpa)

中文:
引理 IsBasis.contract_isBasis_of_indep
  条件: (h : M.IsBasis I X) (h_ind : M.Indep (I union J))
  证明: h.contract_isBasis (h_ind.subset subset_union_right).isBasis_self (by simpa)

Depends on / 依赖: contract_isBasis, h.contract_isBasis, h_ind, h_ind.subset, isBasis_self, subset, subset_union_right
-/
lemma IsBasis.contract_isBasis_of_indep (h : M.IsBasis I X) (h_ind : M.Indep (I union J)) :
    (M ／ J).IsBasis (I \ J) (X \ J) :=
  h.contract_isBasis (h_ind.subset subset_union_right).isBasis_self (by simpa)

/--
lemma `IsBasis.contract_isBasis_of_disjoint_indep` / 引理 `IsBasis.contract_isBasis_of_disjoint_indep`

English:
lemma IsBasis.contract_isBasis_of_disjoint_indep
  statement: (h : M.IsBasis I X) (hdj : Disjoint J X)
  proof: by
  rw [← hdj.sdiff_eq_right]; rw [← (hdj.mono_right h.subset).sdiff_eq_right]
  exact h.contract_isBasis_of_indep h_ind

中文:
引理 IsBasis.contract_isBasis_of_disjoint_indep
  结论: (h : M.IsBasis I X) (hdj : Disjoint J X)
  证明: by
  rw [← hdj.sdiff_eq_right]; rw [← (hdj.mono_right h.subset).sdiff_eq_right]
  exact h.contract_isBasis_of_indep h_ind

Depends on / 依赖: contract_isBasis_of_indep, h.contract_isBasis_of_indep, h.subset, h_ind, hdj.mono_right, hdj.sdiff_eq_right, mono_right, sdiff_eq_right, subset
-/
lemma IsBasis.contract_isBasis_of_disjoint_indep (h : M.IsBasis I X) (hdj : Disjoint J X)
    (h_ind : M.Indep (I union J)) : (M ／ J).IsBasis I X := by
  rw [← hdj.sdiff_eq_right]; rw [← (hdj.mono_right h.subset).sdiff_eq_right]
  exact h.contract_isBasis_of_indep h_ind

/--
lemma `Indep.of_contract` / 引理 `Indep.of_contract`

English:
lemma Indep.of_contract
  given: (hI : (M ／ C).Indep I)
  statement: M.Indep I
  proof: ((M.exists_isBasis' C).choose_spec.contract_indep_iff.1 hI).1.subset subset_union_left

中文:
引理 Indep.of_contract
  条件: (hI : (M ／ C).Indep I)
  结论: M.Indep I
  证明: ((M.exists_isBasis' C).choose_spec.contract_indep_iff.1 hI).1.subset subset_union_left

Depends on / 依赖: M.exists_isBasis, choose_spec, choose_spec.contract_indep_iff, contract_indep_iff, exists_isBasis, subset, subset_union_left
-/
lemma Indep.of_contract (hI : (M ／ C).Indep I) : M.Indep I :=
  ((M.exists_isBasis' C).choose_spec.contract_indep_iff.1 hI).1.subset subset_union_left

/--
lemma `Dep.of_contract` / 引理 `Dep.of_contract`

English:
lemma Dep.of_contract
  given: (h : (M ／ C).Dep X) (hC : C subseteq M.E := by aesop_mat)
  statement: M.Dep (C union X)
  proof: by
  rw [Dep]; rw [and_iff_left (union_subset hC (h.subset_ground.trans sdiff_subset))]
  intro hi
  rw [Dep]; rw [(hi.subset subset_union_left).contract_indep_iff]; rw [union_comm]; rw [and_iff_left hi] at h
  exact h.1 (subset_sdiff.1 h.2).2

中文:
引理 Dep.of_contract
  条件: (h : (M ／ C).Dep X) (hC : C subseteq M.E := by aesop_mat)
  结论: M.Dep (C union X)
  证明: by
  rw [Dep]; rw [and_iff_left (union_subset hC (h.subset_ground.trans sdiff_subset))]
  intro hi
  rw [Dep]; rw [(hi.subset subset_union_left).contract_indep_iff]; rw [union_comm]; rw [and_iff_left hi] at h
  exact h.1 (subset_sdiff.1 h.2).2

Depends on / 依赖: M.Dep, aesop_mat, and_iff_left, contract_indep_iff, h.subset_ground.trans, hi.subset, sdiff_subset, subset, subset_ground, subset_sdiff, subset_union_left, union_comm, union_subset
-/
lemma Dep.of_contract (h : (M ／ C).Dep X) (hC : C subseteq M.E := by aesop_mat) : M.Dep (C union X) := by
  rw [Dep]; rw [and_iff_left (union_subset hC (h.subset_ground.trans sdiff_subset))]
  intro hi
  rw [Dep]; rw [(hi.subset subset_union_left).contract_indep_iff]; rw [union_comm]; rw [and_iff_left hi] at h
  exact h.1 (subset_sdiff.1 h.2).2


/--
Instance `contract_finite` / 实例 `contract_finite`

English:
instance contract_finite
  signature: [M.Finite]
  body: by
  rw [← dual_delete_dual]
  infer_instance

中文:
实例 contract_finite
  签名: [M.Finite]
  定义体: by
  rw [← dual_delete_dual]
  infer_instance

Depends on / 依赖: dual_delete_dual, infer_instance
-/
instance contract_finite [M.Finite] : (M ／ C).Finite := by
  rw [← dual_delete_dual]
  infer_instance

/--
Instance `contract_rankFinite` / 实例 `contract_rankFinite`

English:
instance contract_rankFinite
  signature: [RankFinite M]
  body: let ⟨B, hB⟩ := (M ／ C).exists_isBase
  ⟨B, hB, hB.indep.of_contract.finite⟩

中文:
实例 contract_rankFinite
  签名: [RankFinite M]
  定义体: let ⟨B, hB⟩ := (M ／ C).exists_isBase
  ⟨B, hB, hB.indep.of_contract.finite⟩

Depends on / 依赖: exists_isBase, finite, hB.indep.of_contract.finite, of_contract
-/
instance contract_rankFinite [RankFinite M] : RankFinite (M ／ C) :=
  let ⟨B, hB⟩ := (M ／ C).exists_isBase
  ⟨B, hB, hB.indep.of_contract.finite⟩

/--
Instance `contract_finitary` / 实例 `contract_finitary`

English:
instance contract_finitary
  signature: [Finitary M]
  body: by
  obtain ⟨J, hJ⟩ := M.exists_isBasis' C
  suffices (M ／ J).Finitary by
    rw [hJ.contract_eq_contract_delete]
    infer_instance
  exact ⟨fun I hI => hJ.indep.contract_indep_iff.2 ⟨disjoint_left.2 fun e heI =>
    ((hI {e} (by simpa) (by simp)).subset_ground rfl).2,
    indep_of_forall_finite_su

中文:
实例 contract_finitary
  签名: [Finitary M]
  定义体: by
  obtain ⟨J, hJ⟩ := M.exists_isBasis' C
  suffices (M ／ J).Finitary by
    rw [hJ.contract_eq_contract_delete]
    infer_instance
  exact ⟨fun I hI => hJ.indep.contract_indep_iff.2 ⟨disjoint_left.2 fun e heI =>
    ((hI {e} (by simpa) (by simp)).subset_ground rfl).2,
    indep_of_forall_finite_su

Depends on / 依赖: Finitary, M.exists_isBasis, contract_eq_contract_delete, contract_indep_iff, disjoint_left, exists_isBasis, hJ.contract_eq_contract_delete, hJ.indep.contract_indep_iff, hKfin.inter_of_left, indep_of_forall_finite_subset_indep, infer_instance, inter_of_left, inter_subset_right, subset, subset_ground, tauto_set
-/
instance contract_finitary [Finitary M] : Finitary (M ／ C) := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis' C
  suffices (M ／ J).Finitary by
    rw [hJ.contract_eq_contract_delete]
    infer_instance
  exact ⟨fun I hI => hJ.indep.contract_indep_iff.2 ⟨disjoint_left.2 fun e heI =>
    ((hI {e} (by simpa) (by simp)).subset_ground rfl).2,
    indep_of_forall_finite_subset_indep _ fun K hK hKfin =>
      (hJ.indep.contract_indep_iff.1 <| hI (K inter I)
      inter_subset_right (hKfin.inter_of_left _)).2.subset (by tauto_set)⟩⟩


/--
lemma `contract_eq_delete_of_subset_loops` / 引理 `contract_eq_delete_of_subset_loops`

English:
lemma contract_eq_delete_of_subset_loops
  given: (hX : X subseteq M.loops)
  statement: M ／ X = M ＼ X
  proof: by
  simp [(empty_isBasis_iff.2 hX).contract_eq_contract_delete]

中文:
引理 contract_eq_delete_of_subset_loops
  条件: (hX : X subseteq M.loops)
  结论: M ／ X = M ＼ X
  证明: by
  simp [(empty_isBasis_iff.2 hX).contract_eq_contract_delete]

Depends on / 依赖: contract_eq_contract_delete, empty_isBasis_iff
-/
lemma contract_eq_delete_of_subset_loops (hX : X subseteq M.loops) : M ／ X = M ＼ X := by
  simp [(empty_isBasis_iff.2 hX).contract_eq_contract_delete]

/--
lemma `contract_eq_delete_of_subset_coloops` / 引理 `contract_eq_delete_of_subset_coloops`

English:
lemma contract_eq_delete_of_subset_coloops
  given: (hX : X subseteq M.coloops)
  statement: M ／ X = M ＼ X
  proof: by
  rw [← dual_inj]; rw [dual_delete]; rw [contract_eq_delete_of_subset_loops hX]; rw [dual_contract]

@[simp]

中文:
引理 contract_eq_delete_of_subset_coloops
  条件: (hX : X subseteq M.coloops)
  结论: M ／ X = M ＼ X
  证明: by
  rw [← dual_inj]; rw [dual_delete]; rw [contract_eq_delete_of_subset_loops hX]; rw [dual_contract]

@[simp]

Depends on / 依赖: contract_eq_delete_of_subset_loops, dual_contract, dual_delete, dual_inj
-/
lemma contract_eq_delete_of_subset_coloops (hX : X subseteq M.coloops) : M ／ X = M ＼ X := by
  rw [← dual_inj]; rw [dual_delete]; rw [contract_eq_delete_of_subset_loops hX]; rw [dual_contract]

@[simp]
/--
lemma `contract_isLoop_iff_mem_closure` / 引理 `contract_isLoop_iff_mem_closure`

English:
lemma contract_isLoop_iff_mem_closure
  statement: (M ／ C).IsLoop e ↔ e in M.closure C ∧ e ∉ C
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' C
  rw [hI.contract_eq_contract_delete]; rw [delete_isLoop_iff]; rw [← singleton_dep]; rw [hI.indep.contract_dep_iff]; rw [singleton_union]; rw [hI.indep.insert_dep_iff]; rw [hI.closure_eq_closure]
  by_cases heI : e in I
  · simp [heI, hI.subset heI]
  simp 

中文:
引理 contract_isLoop_iff_mem_closure
  结论: (M ／ C).IsLoop e ↔ e in M.closure C ∧ e ∉ C
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' C
  rw [hI.contract_eq_contract_delete]; rw [delete_isLoop_iff]; rw [← singleton_dep]; rw [hI.indep.contract_dep_iff]; rw [singleton_union]; rw [hI.indep.insert_dep_iff]; rw [hI.closure_eq_closure]
  by_cases heI : e in I
  · simp [heI, hI.subset heI]
  simp 

Depends on / 依赖: M.exists_isBasis, and_comm, closure_eq_closure, contract_dep_iff, contract_eq_contract_delete, delete_isLoop_iff, exists_isBasis, hI.closure_eq_closure, hI.contract_eq_contract_delete, hI.indep.contract_dep_iff, hI.indep.insert_dep_iff, hI.subset, insert_dep_iff, singleton_dep, singleton_union, subset
-/
lemma contract_isLoop_iff_mem_closure : (M ／ C).IsLoop e ↔ e in M.closure C ∧ e ∉ C := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' C
  rw [hI.contract_eq_contract_delete]; rw [delete_isLoop_iff]; rw [← singleton_dep]; rw [hI.indep.contract_dep_iff]; rw [singleton_union]; rw [hI.indep.insert_dep_iff]; rw [hI.closure_eq_closure]
  by_cases heI : e in I
  · simp [heI, hI.subset heI]
  simp [heI, and_comm]

@[simp]
/--
lemma `contract_loops_eq` / 引理 `contract_loops_eq`

English:
lemma contract_loops_eq
  given: (M : Matroid α) (C : Set α)
  statement: (M ／ C).loops = M.closure C \ C
  proof: by
  simp [Set.ext_iff, ← isLoop_iff, contract_isLoop_iff_mem_closure]

@[simp]

中文:
引理 contract_loops_eq
  条件: (M : Matroid α) (C : Set α)
  结论: (M ／ C).loops = M.closure C \ C
  证明: by
  simp [Set.ext_iff, ← isLoop_iff, contract_isLoop_iff_mem_closure]

@[simp]

Depends on / 依赖: Set.ext_iff, contract_isLoop_iff_mem_closure, ext_iff, isLoop_iff
-/
lemma contract_loops_eq (M : Matroid α) (C : Set α) : (M ／ C).loops = M.closure C \ C := by
  simp [Set.ext_iff, ← isLoop_iff, contract_isLoop_iff_mem_closure]

@[simp]
/--
lemma `contract_coloops_eq` / 引理 `contract_coloops_eq`

English:
lemma contract_coloops_eq
  given: (M : Matroid α) (C : Set α)
  statement: (M ／ C).coloops = M.coloops \ C
  proof: by
  rw [← dual_delete_dual]; rw [dual_coloops]; rw [delete_loops_eq]; rw [dual_loops]

@[simp]

中文:
引理 contract_coloops_eq
  条件: (M : Matroid α) (C : Set α)
  结论: (M ／ C).coloops = M.coloops \ C
  证明: by
  rw [← dual_delete_dual]; rw [dual_coloops]; rw [delete_loops_eq]; rw [dual_loops]

@[simp]

Depends on / 依赖: delete_loops_eq, dual_coloops, dual_delete_dual, dual_loops
-/
lemma contract_coloops_eq (M : Matroid α) (C : Set α) : (M ／ C).coloops = M.coloops \ C := by
  rw [← dual_delete_dual]; rw [dual_coloops]; rw [delete_loops_eq]; rw [dual_loops]

@[simp]
/--
lemma `contract_isColoop_iff` / 引理 `contract_isColoop_iff`

English:
lemma contract_isColoop_iff
  statement: (M ／ C).IsColoop e ↔ M.IsColoop e ∧ e ∉ C
  proof: by
  simp [isColoop_iff_mem_coloops]

中文:
引理 contract_isColoop_iff
  结论: (M ／ C).IsColoop e ↔ M.IsColoop e ∧ e ∉ C
  证明: by
  simp [isColoop_iff_mem_coloops]

Depends on / 依赖: isColoop_iff_mem_coloops
-/
lemma contract_isColoop_iff : (M ／ C).IsColoop e ↔ M.IsColoop e ∧ e ∉ C := by
  simp [isColoop_iff_mem_coloops]

/--
lemma `IsNonloop.of_contract` / 引理 `IsNonloop.of_contract`

English:
lemma IsNonloop.of_contract
  given: (h : (M ／ C).IsNonloop e)
  statement: M.IsNonloop e
  proof: by
  rw [← indep_singleton] at h ⊢
  exact h.of_contract

@[simp]

中文:
引理 IsNonloop.of_contract
  条件: (h : (M ／ C).IsNonloop e)
  结论: M.IsNonloop e
  证明: by
  rw [← indep_singleton] at h ⊢
  exact h.of_contract

@[simp]

Depends on / 依赖: h.of_contract, indep_singleton, of_contract
-/
lemma IsNonloop.of_contract (h : (M ／ C).IsNonloop e) : M.IsNonloop e := by
  rw [← indep_singleton] at h ⊢
  exact h.of_contract

@[simp]
/--
lemma `contract_isNonloop_iff` / 引理 `contract_isNonloop_iff`

English:
lemma contract_isNonloop_iff
  statement: (M ／ C).IsNonloop e ↔ e in M.E \ M.closure C
  proof: by
  rw [isNonloop_iff_mem_compl_loops]; rw [contract_ground]; rw [contract_loops_eq]
  refine ⟨fun ⟨he,heC⟩ => ⟨he.1, fun h => heC ⟨h, he.2⟩⟩,
    fun h => ⟨⟨h.1, fun heC => h.2 ?_⟩, fun h' => h.2 h'.1⟩⟩
  rw [← closure_inter_ground]
  exact (M.subset_closure (C inter M.E)) ⟨heC, h.1⟩

中文:
引理 contract_isNonloop_iff
  结论: (M ／ C).IsNonloop e ↔ e in M.E \ M.closure C
  证明: by
  rw [isNonloop_iff_mem_compl_loops]; rw [contract_ground]; rw [contract_loops_eq]
  refine ⟨fun ⟨he,heC⟩ => ⟨he.1, fun h => heC ⟨h, he.2⟩⟩,
    fun h => ⟨⟨h.1, fun heC => h.2 ?_⟩, fun h' => h.2 h'.1⟩⟩
  rw [← closure_inter_ground]
  exact (M.subset_closure (C inter M.E)) ⟨heC, h.1⟩

Depends on / 依赖: M.subset_closure, closure_inter_ground, contract_ground, contract_loops_eq, isNonloop_iff_mem_compl_loops, subset_closure
-/
lemma contract_isNonloop_iff : (M ／ C).IsNonloop e ↔ e in M.E \ M.closure C := by
  rw [isNonloop_iff_mem_compl_loops]; rw [contract_ground]; rw [contract_loops_eq]
  refine ⟨fun ⟨he,heC⟩ => ⟨he.1, fun h => heC ⟨h, he.2⟩⟩,
    fun h => ⟨⟨h.1, fun heC => h.2 ?_⟩, fun h' => h.2 h'.1⟩⟩
  rw [← closure_inter_ground]
  exact (M.subset_closure (C inter M.E)) ⟨heC, h.1⟩

/--
lemma `IsBasis.sdiff_subset_loops_contract` / 引理 `IsBasis.sdiff_subset_loops_contract`

English:
lemma IsBasis.sdiff_subset_loops_contract
  given: (hIX : M.IsBasis I X)
  statement: X \ I subseteq (M ／ I).loops
  proof: by
  rw [sdiff_subset_iff]; rw [contract_loops_eq]; rw [union_sdiff_self]; rw [union_eq_self_of_subset_left (M.subset_closure I)]
  exact hIX.subset_closure

@[deprecated (since := "2026-06-03")]
alias IsBasis.diff_subset_loops_contract := IsBasis.sdiff_subset_loops_contract

中文:
引理 IsBasis.sdiff_subset_loops_contract
  条件: (hIX : M.IsBasis I X)
  结论: X \ I subseteq (M ／ I).loops
  证明: by
  rw [sdiff_subset_iff]; rw [contract_loops_eq]; rw [union_sdiff_self]; rw [union_eq_self_of_subset_left (M.subset_closure I)]
  exact hIX.subset_closure

@[deprecated (since := "2026-06-03")]
alias IsBasis.diff_subset_loops_contract := IsBasis.sdiff_subset_loops_contract

Depends on / 依赖: M.subset_closure, contract_loops_eq, hIX.subset_closure, sdiff_subset_iff, subset_closure, union_eq_self_of_subset_left, union_sdiff_self
-/
lemma IsBasis.sdiff_subset_loops_contract (hIX : M.IsBasis I X) : X \ I subseteq (M ／ I).loops := by
  rw [sdiff_subset_iff]; rw [contract_loops_eq]; rw [union_sdiff_self]; rw [union_eq_self_of_subset_left (M.subset_closure I)]
  exact hIX.subset_closure

@[deprecated (since := "2026-06-03")]
alias IsBasis.diff_subset_loops_contract := IsBasis.sdiff_subset_loops_contract

/-! ### Closure -/

/--
lemma `contract_closure_eq_contract_delete` / 引理 `contract_closure_eq_contract_delete`

English:
lemma contract_closure_eq_contract_delete
  given: (M : Matroid α) (C : Set α)
  proof: by
  wlog hCE : C subseteq M.E with aux
  · rw [← M.contract_inter_ground_eq C, ← closure_inter_ground, aux _ _ inter_subset_right,
      sdiff_inter, sdiff_eq_empty.2 (M.closure_subset_ground _), union_empty]
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  rw [hI.isBasis_closure_right.contract_eq_contract

中文:
引理 contract_closure_eq_contract_delete
  条件: (M : Matroid α) (C : Set α)
  证明: by
  wlog hCE : C subseteq M.E with aux
  · rw [← M.contract_inter_ground_eq C, ← closure_inter_ground, aux _ _ inter_subset_right,
      sdiff_inter, sdiff_eq_empty.2 (M.closure_subset_ground _), union_empty]
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  rw [hI.isBasis_closure_right.contract_eq_contract

Depends on / 依赖: M.closure_subset_ground, M.contract_inter_ground_eq, M.exists_isBasis, M.subset_closure, closure_inter_ground, closure_subset_ground, contract_eq_contract_delete, contract_inter_ground_eq, delete_delete, exists_isBasis, hI.contract_eq_contract_delete, hI.isBasis_closure_right.contract_eq_contract_delete, hI.subset, inter_subset_right, isBasis_closure_right, sdiff_eq_empty, sdiff_inter, sdiff_union_sdiff_cancel, subset, subset_closure
-/
lemma contract_closure_eq_contract_delete (M : Matroid α) (C : Set α) :
    M ／ M.closure C = M ／ C ＼ (M.closure C \ C) := by
  wlog hCE : C subseteq M.E with aux
  · rw [← M.contract_inter_ground_eq C, ← closure_inter_ground, aux _ _ inter_subset_right,
      sdiff_inter, sdiff_eq_empty.2 (M.closure_subset_ground _), union_empty]
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  rw [hI.isBasis_closure_right.contract_eq_contract_delete]; rw [hI.contract_eq_contract_delete]; rw [delete_delete]; rw [union_comm]; rw [sdiff_union_sdiff_cancel (M.subset_closure C) hI.subset]

@[simp]
/--
lemma `contract_closure_eq` / 引理 `contract_closure_eq`

English:
lemma contract_closure_eq
  given: (M : Matroid α) (C X : Set α)
  proof: by
  rw [← sdiff_union_inter (M.closure (X union C) \ C) X]; rw [sdiff_sdiff]; rw [union_comm C]; rw [← contract_loops_eq]; rw [union_comm X]; rw [← contract_contract]; rw [contract_loops_eq]; rw [subset_antisymm_iff]; rw [union_subset_iff]; rw [and_iff_right sdiff_subset]; rw [← sdiff_subset_iff]
 

中文:
引理 contract_closure_eq
  条件: (M : Matroid α) (C X : Set α)
  证明: by
  rw [← sdiff_union_inter (M.closure (X union C) \ C) X]; rw [sdiff_sdiff]; rw [union_comm C]; rw [← contract_loops_eq]; rw [union_comm X]; rw [← contract_contract]; rw [contract_loops_eq]; rw [subset_antisymm_iff]; rw [union_subset_iff]; rw [and_iff_right sdiff_subset]; rw [← sdiff_subset_iff]
 

Depends on / 依赖: M.closure, and_iff_right, and_true, closure, closure_subset_ground, contract_contract, contract_loops_eq, inter_subset_right, mem_closure_of_mem, mem_ground_of_mem_closure, sdiff_sdiff, sdiff_sdiff_right_self, sdiff_subset, sdiff_subset_iff, sdiff_union_inter, subset_antisymm_iff, subset_inter_iff, union_comm, union_subset_iff
-/
lemma contract_closure_eq (M : Matroid α) (C X : Set α) :
    (M ／ C).closure X = M.closure (X union C) \ C := by
  rw [← sdiff_union_inter (M.closure (X union C) \ C) X]; rw [sdiff_sdiff]; rw [union_comm C]; rw [← contract_loops_eq]; rw [union_comm X]; rw [← contract_contract]; rw [contract_loops_eq]; rw [subset_antisymm_iff]; rw [union_subset_iff]; rw [and_iff_right sdiff_subset]; rw [← sdiff_subset_iff]
  simp only [sdiff_sdiff_right_self, subset_inter_iff, inter_subset_right, and_true]
  refine ⟨fun e ⟨he, he'⟩ => ⟨mem_closure_of_mem' _ (.inr he') (mem_ground_of_mem_closure he).1,
    (closure_subset_ground _ _ he).2⟩, fun e ⟨⟨he, heC⟩, he'⟩ =>
    mem_closure_of_mem' _ he' ⟨M.closure_subset_ground _ he, heC⟩⟩

/--
lemma `contract_spanning_iff` / 引理 `contract_spanning_iff`

English:
lemma contract_spanning_iff
  given: (hC : C subseteq M.E := by aesop_mat)
  proof: by
  rw [spanning_iff]; rw [contract_closure_eq]; rw [contract_ground]; rw [spanning_iff]; rw [union_subset_iff]; rw [subset_sdiff]; rw [← and_assoc]; rw [and_congr_left_iff]; rw [and_comm (a := X subseteq _)]; rw [← and_assoc]; rw [and_congr_left_iff]
  refine fun hdj hX => ⟨fun h => ⟨?_, hC⟩, fun 

中文:
引理 contract_spanning_iff
  条件: (hC : C subseteq M.E := by aesop_mat)
  证明: by
  rw [spanning_iff]; rw [contract_closure_eq]; rw [contract_ground]; rw [spanning_iff]; rw [union_subset_iff]; rw [subset_sdiff]; rw [← and_assoc]; rw [and_congr_left_iff]; rw [and_comm (a := X subseteq _)]; rw [← and_assoc]; rw [and_congr_left_iff]
  refine fun hdj hX => ⟨fun h => ⟨?_, hC⟩, fun 

Depends on / 依赖: Disjoint, M.Spanning, M.subset_closure_of_subset, Spanning, aesop_mat, and_assoc, and_comm, and_congr_left_iff, contract_closure_eq, contract_ground, spanning_iff, subset_closure_of_subset, subset_sdiff, subset_union_right, subseteq, union_sdiff_cancel, union_subset_iff
-/
lemma contract_spanning_iff (hC : C subseteq M.E := by aesop_mat) :
    (M ／ C).Spanning X ↔ M.Spanning (X union C) ∧ Disjoint X C := by
  rw [spanning_iff]; rw [contract_closure_eq]; rw [contract_ground]; rw [spanning_iff]; rw [union_subset_iff]; rw [subset_sdiff]; rw [← and_assoc]; rw [and_congr_left_iff]; rw [and_comm (a := X subseteq _)]; rw [← and_assoc]; rw [and_congr_left_iff]
  refine fun hdj hX => ⟨fun h => ⟨?_, hC⟩, fun h => by simp [h]⟩
  rwa [← union_sdiff_cancel (M.subset_closure_of_subset' subset_union_right hC), h,
    union_sdiff_cancel]

/--
lemma `contract_spanning_iff'` / 引理 `contract_spanning_iff'`

English:
lemma contract_spanning_iff'
  statement: (M ／ C).Spanning X ↔ M.Spanning (X union (C inter M.E)) ∧ Disjoint X C
  proof: by
  rw [← contract_inter_ground_eq]; rw [contract_spanning_iff]; rw [and_congr_right_iff]
  refine fun h => ⟨fun hdj => ?_, Disjoint.mono_right inter_subset_left⟩
  rw [← sdiff_union_inter C M.E]; rw [disjoint_union_right]; rw [and_iff_left hdj]
  exact disjoint_sdiff_right.mono_left (subset_union_

中文:
引理 contract_spanning_iff'
  结论: (M ／ C).Spanning X ↔ M.Spanning (X union (C inter M.E)) ∧ Disjoint X C
  证明: by
  rw [← contract_inter_ground_eq]; rw [contract_spanning_iff]; rw [and_congr_right_iff]
  refine fun h => ⟨fun hdj => ?_, Disjoint.mono_right inter_subset_left⟩
  rw [← sdiff_union_inter C M.E]; rw [disjoint_union_right]; rw [and_iff_left hdj]
  exact disjoint_sdiff_right.mono_left (subset_union_

Depends on / 依赖: Disjoint, Disjoint.mono_right, and_congr_right_iff, and_iff_left, contract_inter_ground_eq, contract_spanning_iff, disjoint_sdiff_right, disjoint_sdiff_right.mono_left, disjoint_union_right, h.subset_ground, inter_subset_left, mono_left, mono_right, sdiff_union_inter, subset_ground, subset_union_left, subset_union_left.trans
-/
lemma contract_spanning_iff' : (M ／ C).Spanning X ↔ M.Spanning (X union (C inter M.E)) ∧ Disjoint X C := by
  rw [← contract_inter_ground_eq]; rw [contract_spanning_iff]; rw [and_congr_right_iff]
  refine fun h => ⟨fun hdj => ?_, Disjoint.mono_right inter_subset_left⟩
  rw [← sdiff_union_inter C M.E]; rw [disjoint_union_right]; rw [and_iff_left hdj]
  exact disjoint_sdiff_right.mono_left (subset_union_left.trans h.subset_ground)

/--
lemma `Spanning.contract` / 引理 `Spanning.contract`

English:
lemma Spanning.contract
  given: (hX : M.Spanning X) (C : Set α)
  statement: (M ／ C).Spanning (X \ C)
  proof: by
  have hXE := hX.subset_ground
  rw [contract_spanning_iff']; rw [and_iff_left disjoint_sdiff_left]
  exact hX.superset (by tauto_set) (by tauto_set)

中文:
引理 Spanning.contract
  条件: (hX : M.Spanning X) (C : Set α)
  结论: (M ／ C).Spanning (X \ C)
  证明: by
  have hXE := hX.subset_ground
  rw [contract_spanning_iff']; rw [and_iff_left disjoint_sdiff_left]
  exact hX.superset (by tauto_set) (by tauto_set)

Depends on / 依赖: and_iff_left, contract_spanning_iff, disjoint_sdiff_left, hX.subset_ground, hX.superset, subset_ground, superset, tauto_set
-/
lemma Spanning.contract (hX : M.Spanning X) (C : Set α) : (M ／ C).Spanning (X \ C) := by
  have hXE := hX.subset_ground
  rw [contract_spanning_iff']; rw [and_iff_left disjoint_sdiff_left]
  exact hX.superset (by tauto_set) (by tauto_set)

/--
lemma `Spanning.contract_eq_loopyOn` / 引理 `Spanning.contract_eq_loopyOn`

English:
lemma Spanning.contract_eq_loopyOn
  given: (hX : M.Spanning X)
  statement: M ／ X = loopyOn (M.E \ X)
  proof: by
  rw [eq_loopyOn_iff_loops_eq]
  simp [hX.closure_eq]

中文:
引理 Spanning.contract_eq_loopyOn
  条件: (hX : M.Spanning X)
  结论: M ／ X = loopyOn (M.E \ X)
  证明: by
  rw [eq_loopyOn_iff_loops_eq]
  simp [hX.closure_eq]

Depends on / 依赖: closure_eq, eq_loopyOn_iff_loops_eq, hX.closure_eq
-/
lemma Spanning.contract_eq_loopyOn (hX : M.Spanning X) : M ／ X = loopyOn (M.E \ X) := by
  rw [eq_loopyOn_iff_loops_eq]
  simp [hX.closure_eq]


/--
lemma `IsCircuit.contract_isCircuit` / 引理 `IsCircuit.contract_isCircuit`

English:
lemma IsCircuit.contract_isCircuit
  given: (hK : M.IsCircuit K) (hC : C ⊂ K)
  proof: by
  suffices forall e in K, e ∉ C -> M.Indep (K \ {e} union C) by
    simpa [isCircuit_iff_dep_forall_sdiff_singleton_indep, sdiff_sdiff_comm (s := K) (t := C),
    dep_iff, (hK.ssubset_indep hC).contract_indep_iff, sdiff_subset_sdiff_left hK.subset_ground,
    disjoint_sdiff_left, sdiff_union_of_s

中文:
引理 IsCircuit.contract_isCircuit
  条件: (hK : M.IsCircuit K) (hC : C ⊂ K)
  证明: by
  suffices forall e in K, e ∉ C -> M.Indep (K \ {e} union C) by
    simpa [isCircuit_iff_dep_forall_sdiff_singleton_indep, sdiff_sdiff_comm (s := K) (t := C),
    dep_iff, (hK.ssubset_indep hC).contract_indep_iff, sdiff_subset_sdiff_left hK.subset_ground,
    disjoint_sdiff_left, sdiff_union_of_s

Depends on / 依赖: M.Indep, contract_indep_iff, dep_iff, disjoint_sdiff_left, hC.subset, hK.not_indep, hK.sdiff_singleton_indep, hK.ssubset_indep, hK.subset_ground, isCircuit_iff_dep_forall_sdiff_singleton_indep, not_indep, sdiff_sdiff_comm, sdiff_singleton_indep, sdiff_subset_sdiff_left, sdiff_union_of_subset, ssubset_indep, subset, subset_ground, subset_sdiff_singleton
-/
lemma IsCircuit.contract_isCircuit (hK : M.IsCircuit K) (hC : C ⊂ K) :
    (M ／ C).IsCircuit (K \ C) := by
  suffices forall e in K, e ∉ C -> M.Indep (K \ {e} union C) by
    simpa [isCircuit_iff_dep_forall_sdiff_singleton_indep, sdiff_sdiff_comm (s := K) (t := C),
    dep_iff, (hK.ssubset_indep hC).contract_indep_iff, sdiff_subset_sdiff_left hK.subset_ground,
    disjoint_sdiff_left, sdiff_union_of_subset hC.subset, hK.not_indep]
exact fun e heK heC => (hK.sdiff_singleton_indep heK).subset by
    simp [subset_sdiff_singleton hC.subset heC]

/--
lemma `IsCircuit.contractElem_isCircuit` / 引理 `IsCircuit.contractElem_isCircuit`

English:
lemma IsCircuit.contractElem_isCircuit
  given: (hC : M.IsCircuit C) (hnt : C.Nontrivial) (heC : e in C)
  proof: hC.contract_isCircuit (ssubset_of_ne_of_subset hnt.ne_singleton.symm (by simpa))

中文:
引理 IsCircuit.contractElem_isCircuit
  条件: (hC : M.IsCircuit C) (hnt : C.Nontrivial) (heC : e in C)
  证明: hC.contract_isCircuit (ssubset_of_ne_of_subset hnt.ne_singleton.symm (by simpa))

Depends on / 依赖: contract_isCircuit, hC.contract_isCircuit, hnt.ne_singleton.symm, ne_singleton, ssubset_of_ne_of_subset
-/
lemma IsCircuit.contractElem_isCircuit (hC : M.IsCircuit C) (hnt : C.Nontrivial) (heC : e in C) :
    (M ／ {e}).IsCircuit (C \ {e}) :=
  hC.contract_isCircuit (ssubset_of_ne_of_subset hnt.ne_singleton.symm (by simpa))

/--
lemma `IsCircuit.contract_dep` / 引理 `IsCircuit.contract_dep`

English:
lemma IsCircuit.contract_dep
  given: (hK : M.IsCircuit K) (hCK : Disjoint C K)
  statement: (M ／ C).Dep K
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis (C inter M.E)
  rw [← contract_inter_ground_eq]; rw [Dep]; rw [hI.contract_indep_iff]; rw [and_iff_left (hCK.mono_left inter_subset_left)]; rw [contract_ground]; rw [subset_sdiff]; rw [and_iff_left (hCK.symm.mono_right inter_subset_left)]; rw [and_iff_left hK.

中文:
引理 IsCircuit.contract_dep
  条件: (hK : M.IsCircuit K) (hCK : Disjoint C K)
  结论: (M ／ C).Dep K
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis (C inter M.E)
  rw [← contract_inter_ground_eq]; rw [Dep]; rw [hI.contract_indep_iff]; rw [and_iff_left (hCK.mono_left inter_subset_left)]; rw [contract_ground]; rw [subset_sdiff]; rw [and_iff_left (hCK.symm.mono_right inter_subset_left)]; rw [and_iff_left hK.

Depends on / 依赖: M.exists_isBasis, and_iff_left, contract_ground, contract_indep_iff, contract_inter_ground_eq, exists_isBasis, hCK.mono_left, hCK.symm.mono_right, hI.contract_indep_iff, hK.dep.not_indep, hK.subset_ground, hi.subset, inter_subset_left, mono_left, mono_right, not_indep, subset, subset_ground, subset_sdiff, subset_union_left
-/
lemma IsCircuit.contract_dep (hK : M.IsCircuit K) (hCK : Disjoint C K) : (M ／ C).Dep K := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (C inter M.E)
  rw [← contract_inter_ground_eq]; rw [Dep]; rw [hI.contract_indep_iff]; rw [and_iff_left (hCK.mono_left inter_subset_left)]; rw [contract_ground]; rw [subset_sdiff]; rw [and_iff_left (hCK.symm.mono_right inter_subset_left)]; rw [and_iff_left hK.subset_ground]
  exact fun hi => hK.dep.not_indep (hi.subset subset_union_left)

/--
lemma `IsCircuit.contract_dep_of_not_subset` / 引理 `IsCircuit.contract_dep_of_not_subset`

English:
lemma IsCircuit.contract_dep_of_not_subset
  given: (hK : M.IsCircuit K) {C : Set α} (hKC : ¬ K subseteq C)
  proof: by
  have h' := hK.contract_isCircuit (C := C inter K) (inter_subset_right.ssubset_of_ne (by simpa))
  simp only [sdiff_inter_self_eq_sdiff] at h'
  have hwin := h'.contract_dep (C := C \ K) disjoint_sdiff_sdiff
  rwa [contract_contract, inter_union_sdiff] at hwin

中文:
引理 IsCircuit.contract_dep_of_not_subset
  条件: (hK : M.IsCircuit K) {C : Set α} (hKC : ¬ K subseteq C)
  证明: by
  have h' := hK.contract_isCircuit (C := C inter K) (inter_subset_right.ssubset_of_ne (by simpa))
  simp only [sdiff_inter_self_eq_sdiff] at h'
  have hwin := h'.contract_dep (C := C \ K) disjoint_sdiff_sdiff
  rwa [contract_contract, inter_union_sdiff] at hwin

Depends on / 依赖: contract_contract, contract_dep, contract_isCircuit, disjoint_sdiff_sdiff, hK.contract_isCircuit, inter_subset_right, inter_subset_right.ssubset_of_ne, inter_union_sdiff, sdiff_inter_self_eq_sdiff, ssubset_of_ne
-/
lemma IsCircuit.contract_dep_of_not_subset (hK : M.IsCircuit K) {C : Set α} (hKC : ¬ K subseteq C) :
    (M ／ C).Dep (K \ C) := by
  have h' := hK.contract_isCircuit (C := C inter K) (inter_subset_right.ssubset_of_ne (by simpa))
  simp only [sdiff_inter_self_eq_sdiff] at h'
  have hwin := h'.contract_dep (C := C \ K) disjoint_sdiff_sdiff
  rwa [contract_contract, inter_union_sdiff] at hwin

/--
lemma `IsCircuit.contract_sdiff_isCircuit` / 引理 `IsCircuit.contract_sdiff_isCircuit`

English:
lemma IsCircuit.contract_sdiff_isCircuit
  given: (hC : M.IsCircuit C) (hK : K.Nonempty) (hKC : K subseteq C)
  proof: by
simpa [inter_eq_self_of_subset_right hKC] using hC.contract_isCircuit (C := C \ K)
    by rwa [sdiff_ssubset_left_iff, inter_eq_self_of_subset_right hKC]

@[deprecated (since := "2026-06-03")]
alias IsCircuit.contract_diff_isCircuit := IsCircuit.contract_sdiff_isCircuit

中文:
引理 IsCircuit.contract_sdiff_isCircuit
  条件: (hC : M.IsCircuit C) (hK : K.Nonempty) (hKC : K subseteq C)
  证明: by
simpa [inter_eq_self_of_subset_right hKC] using hC.contract_isCircuit (C := C \ K)
    by rwa [sdiff_ssubset_left_iff, inter_eq_self_of_subset_right hKC]

@[deprecated (since := "2026-06-03")]
alias IsCircuit.contract_diff_isCircuit := IsCircuit.contract_sdiff_isCircuit

Depends on / 依赖: contract_isCircuit, hC.contract_isCircuit, inter_eq_self_of_subset_right, sdiff_ssubset_left_iff
-/
lemma IsCircuit.contract_sdiff_isCircuit (hC : M.IsCircuit C) (hK : K.Nonempty) (hKC : K subseteq C) :
    (M ／ (C \ K)).IsCircuit K := by
simpa [inter_eq_self_of_subset_right hKC] using hC.contract_isCircuit (C := C \ K)
    by rwa [sdiff_ssubset_left_iff, inter_eq_self_of_subset_right hKC]

@[deprecated (since := "2026-06-03")]
alias IsCircuit.contract_diff_isCircuit := IsCircuit.contract_sdiff_isCircuit

/--
lemma `IsCircuit.exists_subset_isCircuit_of_contract` / 引理 `IsCircuit.exists_subset_isCircuit_of_contract`

English:
lemma IsCircuit.exists_subset_isCircuit_of_contract
  given: (hC : (M ／ K).IsCircuit C)
  proof: by
  wlog hKi : M.Indep K generalizing K with aux
  · obtain ⟨I, hI⟩ := M.exists_isBasis' K
    rw [hI.contract_eq_contract_delete]; rw [delete_isCircuit_iff] at hC
    obtain ⟨C', hC', hCC', hC'ss⟩ := aux hC.1 hI.indep
    exact ⟨C', hC', hCC', hC'ss.trans (union_subset_union_right _ hI.subset)⟩
  

中文:
引理 IsCircuit.exists_subset_isCircuit_of_contract
  条件: (hC : (M ／ K).IsCircuit C)
  证明: by
  wlog hKi : M.Indep K generalizing K with aux
  · obtain ⟨I, hI⟩ := M.exists_isBasis' K
    rw [hI.contract_eq_contract_delete]; rw [delete_isCircuit_iff] at hC
    obtain ⟨C', hC', hCC', hC'ss⟩ := aux hC.1 hI.indep
    exact ⟨C', hC', hCC', hC'ss.trans (union_subset_union_right _ hI.subset)⟩
  

Depends on / 依赖: Disjoint, M.Indep, M.exists_isBasis, contract_dep_iff, contract_eq_contract_delete, delete_isCircuit_iff, exists_isBasis, exists_isCircuit_subset, generalizing, hC.dep, hC.subset_ground, hI.contract_eq_contract_delete, hI.indep, hI.subset, hKi.contract_dep_iff, ss.trans, subset, subset_ground, subset_sdiff, subseteq
-/
lemma IsCircuit.exists_subset_isCircuit_of_contract (hC : (M ／ K).IsCircuit C) :
    exists C', M.IsCircuit C' ∧ C subseteq C' ∧ C' subseteq C union K := by
  wlog hKi : M.Indep K generalizing K with aux
  · obtain ⟨I, hI⟩ := M.exists_isBasis' K
    rw [hI.contract_eq_contract_delete]; rw [delete_isCircuit_iff] at hC
    obtain ⟨C', hC', hCC', hC'ss⟩ := aux hC.1 hI.indep
    exact ⟨C', hC', hCC', hC'ss.trans (union_subset_union_right _ hI.subset)⟩
  obtain ⟨hCE : C subseteq M.E, hCK : Disjoint C K⟩ := subset_sdiff.1 hC.subset_ground
  obtain ⟨C', hC'ss, hC'⟩ := (hKi.contract_dep_iff.1 hC.dep).2.exists_isCircuit_subset
  refine ⟨C', hC', ?_, hC'ss⟩
  have hdep2 : (M ／ K).Dep (C' \ K) := by
    rw [hKi.contract_dep_iff]; rw [and_iff_right disjoint_sdiff_left]
    refine hC'.dep.superset (by simp)
  rw [← (hC.eq_of_dep_subset hdep2 (sdiff_subset_iff.2 (union_comm _ _ ▸ hC'ss)))]
  exact sdiff_subset

/--
lemma `IsCocircuit.of_contract` / 引理 `IsCocircuit.of_contract`

English:
lemma IsCocircuit.of_contract
  given: (hK : (M ／ C).IsCocircuit K)
  statement: M.IsCocircuit K
  proof: by
  rw [isCocircuit_def]; rw [dual_contract] at hK
  exact hK.of_delete

中文:
引理 IsCocircuit.of_contract
  条件: (hK : (M ／ C).IsCocircuit K)
  结论: M.IsCocircuit K
  证明: by
  rw [isCocircuit_def]; rw [dual_contract] at hK
  exact hK.of_delete

Depends on / 依赖: dual_contract, hK.of_delete, isCocircuit_def, of_delete
-/
lemma IsCocircuit.of_contract (hK : (M ／ C).IsCocircuit K) : M.IsCocircuit K := by
  rw [isCocircuit_def]; rw [dual_contract] at hK
  exact hK.of_delete

/--
lemma `IsCocircuit.delete_isCocircuit` / 引理 `IsCocircuit.delete_isCocircuit`

English:
lemma IsCocircuit.delete_isCocircuit
  given: {D : Set α} (hK : M.IsCocircuit K) (hD : D ⊂ K)
  proof: by
  rw [isCocircuit_def]; rw [dual_delete]
  exact hK.isCircuit.contract_isCircuit hD

中文:
引理 IsCocircuit.delete_isCocircuit
  条件: {D : Set α} (hK : M.IsCocircuit K) (hD : D ⊂ K)
  证明: by
  rw [isCocircuit_def]; rw [dual_delete]
  exact hK.isCircuit.contract_isCircuit hD

Depends on / 依赖: contract_isCircuit, dual_delete, hK.isCircuit.contract_isCircuit, isCircuit, isCocircuit_def
-/
lemma IsCocircuit.delete_isCocircuit {D : Set α} (hK : M.IsCocircuit K) (hD : D ⊂ K) :
    (M ＼ D).IsCocircuit (K \ D) := by
  rw [isCocircuit_def]; rw [dual_delete]
  exact hK.isCircuit.contract_isCircuit hD

/--
lemma `IsCocircuit.delete_sdiff_isCocircuit` / 引理 `IsCocircuit.delete_sdiff_isCocircuit`

English:
lemma IsCocircuit.delete_sdiff_isCocircuit
  statement: {X : Set α} (hK : M.IsCocircuit K) (hXK : X subseteq K)
  proof: by
  rw [isCocircuit_def]; rw [dual_delete]
  exact hK.isCircuit.contract_sdiff_isCircuit hX hXK

@[deprecated (since := "2026-06-03")]
alias IsCocircuit.delete_diff_isCocircuit := IsCocircuit.delete_sdiff_isCocircuit

中文:
引理 IsCocircuit.delete_sdiff_isCocircuit
  结论: {X : Set α} (hK : M.IsCocircuit K) (hXK : X subseteq K)
  证明: by
  rw [isCocircuit_def]; rw [dual_delete]
  exact hK.isCircuit.contract_sdiff_isCircuit hX hXK

@[deprecated (since := "2026-06-03")]
alias IsCocircuit.delete_diff_isCocircuit := IsCocircuit.delete_sdiff_isCocircuit

Depends on / 依赖: contract_sdiff_isCircuit, dual_delete, hK.isCircuit.contract_sdiff_isCircuit, isCircuit, isCocircuit_def
-/
lemma IsCocircuit.delete_sdiff_isCocircuit {X : Set α} (hK : M.IsCocircuit K) (hXK : X subseteq K)
    (hX : X.Nonempty) : (M ＼ (K \ X)).IsCocircuit X := by
  rw [isCocircuit_def]; rw [dual_delete]
  exact hK.isCircuit.contract_sdiff_isCircuit hX hXK

@[deprecated (since := "2026-06-03")]
alias IsCocircuit.delete_diff_isCocircuit := IsCocircuit.delete_sdiff_isCocircuit


/--
lemma `contract_delete_sdiff` / 引理 `contract_delete_sdiff`

English:
lemma contract_delete_sdiff
  given: (M : Matroid α) (C D : Set α)
  statement: M ／ C ＼ D = M ／ C ＼ (D \ C)
  proof: by
  rw [delete_eq_delete_iff]; rw [contract_ground]; rw [sdiff_eq]; rw [sdiff_eq]; rw [← inter_inter_distrib_right]; rw [inter_assoc]

@[deprecated (since := "2026-06-03")] alias contract_delete_diff := contract_delete_sdiff

中文:
引理 contract_delete_sdiff
  条件: (M : Matroid α) (C D : Set α)
  结论: M ／ C ＼ D = M ／ C ＼ (D \ C)
  证明: by
  rw [delete_eq_delete_iff]; rw [contract_ground]; rw [sdiff_eq]; rw [sdiff_eq]; rw [← inter_inter_distrib_right]; rw [inter_assoc]

@[deprecated (since := "2026-06-03")] alias contract_delete_diff := contract_delete_sdiff

Depends on / 依赖: contract_ground, delete_eq_delete_iff, inter_assoc, inter_inter_distrib_right, sdiff_eq
-/
lemma contract_delete_sdiff (M : Matroid α) (C D : Set α) : M ／ C ＼ D = M ／ C ＼ (D \ C) := by
  rw [delete_eq_delete_iff]; rw [contract_ground]; rw [sdiff_eq]; rw [sdiff_eq]; rw [← inter_inter_distrib_right]; rw [inter_assoc]

@[deprecated (since := "2026-06-03")] alias contract_delete_diff := contract_delete_sdiff

/--
lemma `contract_restrict_eq_restrict_contract` / 引理 `contract_restrict_eq_restrict_contract`

English:
lemma contract_restrict_eq_restrict_contract
  given: (M : Matroid α) (h : Disjoint C R)
  proof: by
  refine ext_indep (by simp [h.sdiff_eq_right]) fun I (hI : I subseteq R) => ?_
  obtain ⟨J, hJ⟩ := (M ↾ (R union C)).exists_isBasis' C
  have hJ' : M.IsBasis' J C := by
    simpa [inter_eq_self_of_subset_left subset_union_right] using (isBasis'_restrict_iff.1 hJ).1
  rw [restrict_indep_iff]; rw 

中文:
引理 contract_restrict_eq_restrict_contract
  条件: (M : Matroid α) (h : Disjoint C R)
  证明: by
  refine ext_indep (by simp [h.sdiff_eq_right]) fun I (hI : I subseteq R) => ?_
  obtain ⟨J, hJ⟩ := (M ↾ (R union C)).exists_isBasis' C
  have hJ' : M.IsBasis' J C := by
    simpa [inter_eq_self_of_subset_left subset_union_right] using (isBasis'_restrict_iff.1 hJ).1
  rw [restrict_indep_iff]; rw 

Depends on / 依赖: IsBasis, M.IsBasis, _restrict_iff, contract_indep_iff, exists_isBasis, ext_indep, h.sdiff_eq_right, hJ.contract_indep_iff, inter_eq_self_of_subset_left, isBasis, restrict_indep_iff, sdiff_eq_right, subset, subset_union_right, subseteq, tauto_set
-/
lemma contract_restrict_eq_restrict_contract (M : Matroid α) (h : Disjoint C R) :
    (M ／ C) ↾ R = (M ↾ (R union C)) ／ C := by
  refine ext_indep (by simp [h.sdiff_eq_right]) fun I (hI : I subseteq R) => ?_
  obtain ⟨J, hJ⟩ := (M ↾ (R union C)).exists_isBasis' C
  have hJ' : M.IsBasis' J C := by
    simpa [inter_eq_self_of_subset_left subset_union_right] using (isBasis'_restrict_iff.1 hJ).1
  rw [restrict_indep_iff]; rw [hJ.contract_indep_iff]; rw [hJ'.contract_indep_iff]; rw [restrict_indep_iff]
  have hJC := hJ'.subset
  tauto_set

/--
lemma `restrict_contract_eq_contract_restrict` / 引理 `restrict_contract_eq_contract_restrict`

English:
lemma restrict_contract_eq_contract_restrict
  given: (M : Matroid α) (hCR : C subseteq R)
  proof: by
  rw [contract_restrict_eq_restrict_contract _ disjoint_sdiff_right]
  simp [union_eq_self_of_subset_right hCR]

中文:
引理 restrict_contract_eq_contract_restrict
  条件: (M : Matroid α) (hCR : C subseteq R)
  证明: by
  rw [contract_restrict_eq_restrict_contract _ disjoint_sdiff_right]
  simp [union_eq_self_of_subset_right hCR]

Depends on / 依赖: contract_restrict_eq_restrict_contract, disjoint_sdiff_right, union_eq_self_of_subset_right
-/
lemma restrict_contract_eq_contract_restrict (M : Matroid α) (hCR : C subseteq R) :
    (M ↾ R) ／ C = (M ／ C) ↾ (R \ C) := by
  rw [contract_restrict_eq_restrict_contract _ disjoint_sdiff_right]
  simp [union_eq_self_of_subset_right hCR]

/--
lemma `contract_delete_comm` / 引理 `contract_delete_comm`

English:
lemma contract_delete_comm
  given: (M : Matroid α) (hCD : Disjoint C D)
  statement: M ／ C ＼ D = M ＼ D ／ C
  proof: by
  wlog hCE : C subseteq M.E generalizing C with aux
  · rw [← contract_inter_ground_eq, aux (hCD.mono_left inter_subset_left) inter_subset_right,
      contract_eq_contract_iff, inter_assoc, delete_ground,
      inter_eq_self_of_subset_right sdiff_subset]
  rw [delete_eq_restrict]; rw [delete_eq_

中文:
引理 contract_delete_comm
  条件: (M : Matroid α) (hCD : Disjoint C D)
  结论: M ／ C ＼ D = M ＼ D ／ C
  证明: by
  wlog hCE : C subseteq M.E generalizing C with aux
  · rw [← contract_inter_ground_eq, aux (hCD.mono_left inter_subset_left) inter_subset_right,
      contract_eq_contract_iff, inter_assoc, delete_ground,
      inter_eq_self_of_subset_right sdiff_subset]
  rw [delete_eq_restrict]; rw [delete_eq_

Depends on / 依赖: contract_eq_contract_iff, contract_ground, contract_inter_ground_eq, delete_eq_restrict, delete_ground, generalizing, hCD.mono_left, inter_assoc, inter_eq_self_of_subset_right, inter_subset_left, inter_subset_right, mono_left, restrict_contract_eq_contract_restrict, sdiff_sdiff_comm, sdiff_subset, subset_sdiff, subseteq
-/
lemma contract_delete_comm (M : Matroid α) (hCD : Disjoint C D) : M ／ C ＼ D = M ＼ D ／ C := by
  wlog hCE : C subseteq M.E generalizing C with aux
  · rw [← contract_inter_ground_eq, aux (hCD.mono_left inter_subset_left) inter_subset_right,
      contract_eq_contract_iff, inter_assoc, delete_ground,
      inter_eq_self_of_subset_right sdiff_subset]
  rw [delete_eq_restrict]; rw [delete_eq_restrict]; rw [contract_ground]; rw [sdiff_sdiff_comm]; rw [restrict_contract_eq_contract_restrict _ (by simpa [hCE]; rw [subset_sdiff])]

/--
lemma `contract_delete_comm'` / 引理 `contract_delete_comm'`

English:
lemma contract_delete_comm'
  given: (M : Matroid α) (C D : Set α)
  statement: M ／ C ＼ D = M ＼ (D \ C) ／ C
  proof: by
  rw [contract_delete_sdiff]; rw [contract_delete_comm _ disjoint_sdiff_right]

中文:
引理 contract_delete_comm'
  条件: (M : Matroid α) (C D : Set α)
  结论: M ／ C ＼ D = M ＼ (D \ C) ／ C
  证明: by
  rw [contract_delete_sdiff]; rw [contract_delete_comm _ disjoint_sdiff_right]

Depends on / 依赖: contract_delete_comm, contract_delete_sdiff, disjoint_sdiff_right
-/
lemma contract_delete_comm' (M : Matroid α) (C D : Set α) : M ／ C ＼ D = M ＼ (D \ C) ／ C := by
  rw [contract_delete_sdiff]; rw [contract_delete_comm _ disjoint_sdiff_right]

/--
lemma `delete_contract_eq_sdiff` / 引理 `delete_contract_eq_sdiff`

English:
lemma delete_contract_eq_sdiff
  given: (M : Matroid α) (D C : Set α)
  statement: M ＼ D ／ C = M ＼ D ／ (C \ D)
  proof: by
  rw [contract_eq_contract_iff]; rw [delete_ground]; rw [← sdiff_inter_distrib_right]; rw [sdiff_eq]; rw [sdiff_eq]; rw [inter_assoc]

@[deprecated (since := "2026-06-03")] alias delete_contract_eq_diff := delete_contract_eq_sdiff

中文:
引理 delete_contract_eq_sdiff
  条件: (M : Matroid α) (D C : Set α)
  结论: M ＼ D ／ C = M ＼ D ／ (C \ D)
  证明: by
  rw [contract_eq_contract_iff]; rw [delete_ground]; rw [← sdiff_inter_distrib_right]; rw [sdiff_eq]; rw [sdiff_eq]; rw [inter_assoc]

@[deprecated (since := "2026-06-03")] alias delete_contract_eq_diff := delete_contract_eq_sdiff

Depends on / 依赖: contract_eq_contract_iff, delete_ground, inter_assoc, sdiff_eq, sdiff_inter_distrib_right
-/
lemma delete_contract_eq_sdiff (M : Matroid α) (D C : Set α) : M ＼ D ／ C = M ＼ D ／ (C \ D) := by
  rw [contract_eq_contract_iff]; rw [delete_ground]; rw [← sdiff_inter_distrib_right]; rw [sdiff_eq]; rw [sdiff_eq]; rw [inter_assoc]

@[deprecated (since := "2026-06-03")] alias delete_contract_eq_diff := delete_contract_eq_sdiff

/--
lemma `delete_contract_comm'` / 引理 `delete_contract_comm'`

English:
lemma delete_contract_comm'
  given: (M : Matroid α) (D C : Set α)
  statement: M ＼ D ／ C = M ／ (C \ D) ＼ D
  proof: by
  rw [delete_contract_eq_sdiff]; rw [← contract_delete_comm _ disjoint_sdiff_left]

中文:
引理 delete_contract_comm'
  条件: (M : Matroid α) (D C : Set α)
  结论: M ＼ D ／ C = M ／ (C \ D) ＼ D
  证明: by
  rw [delete_contract_eq_sdiff]; rw [← contract_delete_comm _ disjoint_sdiff_left]

Depends on / 依赖: contract_delete_comm, delete_contract_eq_sdiff, disjoint_sdiff_left
-/
lemma delete_contract_comm' (M : Matroid α) (D C : Set α) : M ＼ D ／ C = M ／ (C \ D) ＼ D := by
  rw [delete_contract_eq_sdiff]; rw [← contract_delete_comm _ disjoint_sdiff_left]

/--
lemma `contract_delete_contract'` / 引理 `contract_delete_contract'`

English:
lemma contract_delete_contract'
  given: (M : Matroid α) (C D C' : Set α)
  proof: by
  rw [delete_contract_eq_sdiff]; rw [← contract_delete_comm _ disjoint_sdiff_left]; rw [contract_contract]

中文:
引理 contract_delete_contract'
  条件: (M : Matroid α) (C D C' : Set α)
  证明: by
  rw [delete_contract_eq_sdiff]; rw [← contract_delete_comm _ disjoint_sdiff_left]; rw [contract_contract]

Depends on / 依赖: contract_contract, contract_delete_comm, delete_contract_eq_sdiff, disjoint_sdiff_left
-/
lemma contract_delete_contract' (M : Matroid α) (C D C' : Set α) :
    M ／ C ＼ D ／ C' = M ／ (C union C' \ D) ＼ D := by
  rw [delete_contract_eq_sdiff]; rw [← contract_delete_comm _ disjoint_sdiff_left]; rw [contract_contract]

/--
lemma `contract_delete_contract` / 引理 `contract_delete_contract`

English:
lemma contract_delete_contract
  given: (M : Matroid α) (C D C' : Set α) (h : Disjoint C' D)
  proof: by rw [contract_delete_contract', sdiff_eq_left.mpr h]

中文:
引理 contract_delete_contract
  条件: (M : Matroid α) (C D C' : Set α) (h : Disjoint C' D)
  证明: by rw [contract_delete_contract', sdiff_eq_left.mpr h]

Depends on / 依赖: contract_delete_contract, sdiff_eq_left, sdiff_eq_left.mpr
-/
lemma contract_delete_contract (M : Matroid α) (C D C' : Set α) (h : Disjoint C' D) :
    M ／ C ＼ D ／ C' = M ／ (C union C') ＼ D := by rw [contract_delete_contract', sdiff_eq_left.mpr h]

/--
lemma `contract_delete_contract_delete'` / 引理 `contract_delete_contract_delete'`

English:
lemma contract_delete_contract_delete'
  given: (M : Matroid α) (C D C' D' : Set α)
  proof: by
  rw [contract_delete_contract']; rw [delete_delete]

中文:
引理 contract_delete_contract_delete'
  条件: (M : Matroid α) (C D C' D' : Set α)
  证明: by
  rw [contract_delete_contract']; rw [delete_delete]

Depends on / 依赖: contract_delete_contract, delete_delete
-/
lemma contract_delete_contract_delete' (M : Matroid α) (C D C' D' : Set α) :
    M ／ C ＼ D ／ C' ＼ D' = M ／ (C union C' \ D) ＼ (D union D') := by
  rw [contract_delete_contract']; rw [delete_delete]

/--
lemma `contract_delete_contract_delete` / 引理 `contract_delete_contract_delete`

English:
lemma contract_delete_contract_delete
  given: (M : Matroid α) (C D C' D' : Set α) (h : Disjoint C' D)
  proof: by
  rw [contract_delete_contract_delete']; rw [sdiff_eq_left.mpr h]

中文:
引理 contract_delete_contract_delete
  条件: (M : Matroid α) (C D C' D' : Set α) (h : Disjoint C' D)
  证明: by
  rw [contract_delete_contract_delete']; rw [sdiff_eq_left.mpr h]

Depends on / 依赖: contract_delete_contract_delete, sdiff_eq_left, sdiff_eq_left.mpr
-/
lemma contract_delete_contract_delete (M : Matroid α) (C D C' D' : Set α) (h : Disjoint C' D) :
    M ／ C ＼ D ／ C' ＼ D' = M ／ (C union C') ＼ (D union D') := by
  rw [contract_delete_contract_delete']; rw [sdiff_eq_left.mpr h]

/--
lemma `delete_contract_delete'` / 引理 `delete_contract_delete'`

English:
lemma delete_contract_delete'
  given: (M : Matroid α) (D C D' : Set α)
  proof: by
  rw [delete_contract_comm']; rw [delete_delete]

中文:
引理 delete_contract_delete'
  条件: (M : Matroid α) (D C D' : Set α)
  证明: by
  rw [delete_contract_comm']; rw [delete_delete]

Depends on / 依赖: delete_contract_comm, delete_delete
-/
lemma delete_contract_delete' (M : Matroid α) (D C D' : Set α) :
    M ＼ D ／ C ＼ D' = M ／ (C \ D) ＼ (D union D') := by
  rw [delete_contract_comm']; rw [delete_delete]

/--
lemma `delete_contract_delete` / 引理 `delete_contract_delete`

English:
lemma delete_contract_delete
  given: (M : Matroid α) (D C D' : Set α) (h : Disjoint C D)
  proof: by
  rw [delete_contract_delete']; rw [sdiff_eq_left.mpr h]

中文:
引理 delete_contract_delete
  条件: (M : Matroid α) (D C D' : Set α) (h : Disjoint C D)
  证明: by
  rw [delete_contract_delete']; rw [sdiff_eq_left.mpr h]

Depends on / 依赖: delete_contract_delete, sdiff_eq_left, sdiff_eq_left.mpr
-/
lemma delete_contract_delete (M : Matroid α) (D C D' : Set α) (h : Disjoint C D) :
    M ＼ D ／ C ＼ D' = M ／ C ＼ (D union D') := by
  rw [delete_contract_delete']; rw [sdiff_eq_left.mpr h]

end Contract

end Matroid
