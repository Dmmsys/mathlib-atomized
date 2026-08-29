/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.IndepAxioms

/-!
# Matroid Duality

For a matroid `M` on ground set `E`, the collection of complements of the bases of `M` is the
collection of bases of another matroid on `E` called the 'dual' of `M`.
The map from `M` to its dual is an involution, interacts nicely with minors,
and preserves many important matroid properties such as representability and connectivity.

This file defines the dual matroid `M✶` of `M`, and gives associated API. The definition
is in terms of its independent sets, using `IndepMatroid.matroid`.

We also define 'Co-independence' (independence in the dual) of a set as a predicate `M.Coindep X`.
This is an abbreviation for `M✶.Indep X`, but has its own name for the sake of dot notation.

## Main Definitions

* `M.Dual`, written `M✶`, is the matroid on `M.E` which a set `B ⊆ M.E` is a base if and only if
  `M.E \ B` is a base for `M`.

* `M.Coindep X` means `M✶.Indep X`, or equivalently that `X` is contained in `M.E \ B` for some
  base `B` of `M`.
-/

@[expose] public section

assert_not_exists Field

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {I B X : Set α}

section dual

/--
Definition of `dualIndepMatroid` / `dualIndepMatroid` 的定义

English:
definition dualIndepMatroid
  signature: (M : Matroid α)
  body: M.E
  Indep I := I subseteq M.E ∧ exists B, M.IsBase B ∧ Disjoint I B
  indep_empty := ⟨empty_subset M.E, M.exists_isBase.imp (fun _ hB => ⟨hB, empty_disjoint _⟩)⟩
  indep_subset := by
    rintro I J ⟨hJE, B, hB, hJB⟩ hIJ
    exact ⟨hIJ.trans hJE, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩⟩
  indep_au

中文:
定义 dualIndepMatroid
  签名: (M : 拟阵 α)
  定义体: M.E
  Indep I := I subseteq M.E ∧ exists B, M.IsBase B ∧ Disjoint I B
  indep_empty := ⟨empty_subset M.E, M.exists_isBase.imp (fun _ hB => ⟨hB, empty_disjoint _⟩)⟩
  indep_subset := by
    rintro I J ⟨hJE, B, hB, hJB⟩ hIJ
    exact ⟨hIJ.trans hJE, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩⟩
  indep_au
-/
@[simps] def dualIndepMatroid (M : Matroid α) : IndepMatroid α where
  E := M.E
  Indep I := I subseteq M.E ∧ exists B, M.IsBase B ∧ Disjoint I B
  indep_empty := ⟨empty_subset M.E, M.exists_isBase.imp (fun _ hB => ⟨hB, empty_disjoint _⟩)⟩
  indep_subset := by
    rintro I J ⟨hJE, B, hB, hJB⟩ hIJ
    exact ⟨hIJ.trans hJE, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩⟩
  indep_aug := by
    rintro I X ⟨hIE, B, hB, hIB⟩ hI_not_max hX_max
    have hXE := hX_max.1.1
    have hB' := (isBase_compl_iff_maximal_disjoint_isBase hXE).mpr hX_max
    set B' := M.E \ X with hX
    have hI := (not_iff_not.mpr (isBase_compl_iff_maximal_disjoint_isBase)).mpr hI_not_max
    obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB'.indep.sdiff I).exists_isBase_subset_union_isBase hB
    rw [← compl_subset_compl]; rw [← hIB.sdiff_eq_right]; rw [← union_sdiff_distrib]; rw [sdiff_eq]; rw [compl_inter]; rw [compl_compl]; rw [union_subset_iff]; rw [compl_subset_compl] at hB''₂
    have hssu := (subset_inter (hB''₂.2) hIE).ssubset_of_ne
      (by { rintro rfl; apply hI; convert! hB''; simp [hB''.subset_ground] })
    obtain ⟨e, ⟨(heB'' : e ∉ _), heE⟩, heI⟩ := exists_of_ssubset hssu
    use e
    simp_rw [mem_sdiff, insert_subset_iff, and_iff_left heI, and_iff_right heE, and_iff_right hIE]
    refine ⟨by_contra (fun heX => heB'' (hB''₁ ⟨?_, heI⟩)), ⟨B'', hB'', ?_⟩⟩
    · rw [hX]; exact ⟨heE, heX⟩
    rw [← union_singleton]; rw [disjoint_union_left]; rw [disjoint_singleton_left]; rw [and_iff_left heB'']
    exact disjoint_of_subset_left hB''₂.2 disjoint_compl_left
  indep_maximal := by
    rintro X - I' ⟨hI'E, B, hB, hI'B⟩ hI'X
    obtain ⟨I, hI⟩ := M.exists_isBasis (M.E \ X)
    obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_isBase_subset_union_isBase hB
    obtain rfl : I = B' \ X := hI.eq_of_subset_indep (hB'.indep.sdiff _)
      (subset_sdiff.2 ⟨hIB', (subset_sdiff.1 hI.subset).2⟩)
      (sdiff_subset_sdiff_left hB'.subset_ground)
    simp_rw [maximal_subset_iff']
    refine ⟨(X \ B') inter M.E, ?_, ⟨⟨inter_subset_right, ?_⟩, ?_⟩, ?_⟩
    · rw [subset_inter_iff, and_iff_left hI'E, subset_sdiff, and_iff_right hI'X]
exact Disjoint.mono_right hB'IB disjoint_union_right.2
        ⟨disjoint_sdiff_right.mono_left hI'X, hI'B⟩
    · exact ⟨B', hB', (disjoint_sdiff_left (t := X)).mono_left inter_subset_left⟩
    · exact inter_subset_left.trans sdiff_subset
    simp only [subset_inter_iff, subset_sdiff, and_imp, forall_exists_index]
    refine fun J hJE B'' hB'' hdj hJX hXJ => ⟨⟨hJX, ?_⟩, hJE⟩
    have hI' : (B'' inter X) union (B' \ X) subseteq B' := by
      rw [union_subset_iff]; rw [and_iff_left sdiff_subset]; rw [← union_sdiff_cancel hJX]; rw [inter_union_distrib_left]; rw [hdj.symm.inter_eq]; rw [empty_union]; rw [sdiff_eq]; rw [← inter_assoc]; rw [← sdiff_eq]; rw [sdiff_subset_comm]; rw [sdiff_eq]; rw [inter_assoc]; rw [← sdiff_eq]; rw [inter_comm]
      exact subset_trans (inter_subset_inter_right _ hB''.subset_ground) hXJ
    obtain ⟨B₁, hB₁, hI'B₁, hB₁I⟩ := (hB'.indep.subset hI').exists_isBase_subset_union_isBase hB''
    rw [union_comm]; rw [← union_assoc]; rw [union_eq_self_of_subset_right inter_subset_left] at hB₁I
    obtain rfl : B₁ = B' := by
      refine hB₁.eq_of_subset_indep hB'.indep (fun e he => ?_)
      refine (hB₁I he).elim (fun heB'' => ?_) (fun h => h.1)
      refine (em (e in X)).elim (fun heX => hI' (Or.inl ⟨heB'', heX⟩)) (fun heX => hIB' ?_)
      refine hI.mem_of_insert_indep ⟨hB₁.subset_ground he, heX⟩ ?_
      exact hB₁.indep.subset (insert_subset he (subset_union_right.trans hI'B₁))
    by_contra hdj'
    obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hdj'
    obtain (heB'' | ⟨-, heX⟩) := hB₁I heB'
    · exact hdj.ne_of_mem heJ heB'' rfl
    exact heX (hJX heJ)
  subset_ground := by tauto

/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: (M : Matroid α)
  body: M.dualIndepMatroid.matroid

中文:
定义 dual
  签名: (M : 拟阵 α)
  定义体: M.dualIndepMatroid.matroid

Depends on / 依赖: M.dualIndepMatroid.matroid, dualIndepMatroid, matroid
-/
def dual (M : Matroid α) : Matroid α := M.dualIndepMatroid.matroid

/-- The `✶` symbol, which denotes matroid duality.
  (This is distinct from the usual `*` symbol for multiplication, due to precedence issues.) -/
postfix:max "✶" => Matroid.dual

/--
theorem `dual_indep_iff_exists'` / 定理 `dual_indep_iff_exists'`

English:
theorem dual_indep_iff_exists'
  statement: (M✶.Indep I) ↔ I subseteq M.E ∧ (exists B, M.IsBase B ∧ Disjoint I B)
  proof: Iff.rfl

中文:
定理 dual_indep_iff_存在'
  结论: (M✶.Indep I) ↔ I subseteq M.E ∧ (存在 B, M.IsBase B ∧ Disjoint I B)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem dual_indep_iff_exists' : (M✶.Indep I) ↔ I subseteq M.E ∧ (exists B, M.IsBase B ∧ Disjoint I B) :=
  Iff.rfl

/--
theorem `dual_ground` / 定理 `dual_ground`

English:
theorem dual_ground
  statement: M✶.E = M.E
  proof: rfl

中文:
定理 dual_ground
  结论: M✶.E = M.E
  证明: rfl
-/
@[simp] theorem dual_ground : M✶.E = M.E := rfl

/--
theorem `dual_indep_iff_exists` / 定理 `dual_indep_iff_exists`

English:
theorem dual_indep_iff_exists
  given: (hI : I subseteq M.E := by aesop_mat)
  proof: by
  rw [dual_indep_iff_exists']; rw [and_iff_right hI]

中文:
定理 dual_indep_iff_存在
  条件: (hI : I subseteq M.E := by aesop_mat)
  证明: by
  rw [dual_indep_iff_exists']; rw [and_iff_right hI]

Depends on / 依赖: Disjoint, IsBase, M.IsBase, aesop_mat, and_iff_right, dual_indep_iff_exists
-/
theorem dual_indep_iff_exists (hI : I subseteq M.E := by aesop_mat) :
    M✶.Indep I ↔ (exists B, M.IsBase B ∧ Disjoint I B) := by
  rw [dual_indep_iff_exists']; rw [and_iff_right hI]

/--
theorem `dual_dep_iff_forall` / 定理 `dual_dep_iff_forall`

English:
theorem dual_dep_iff_forall
  statement: (M✶.Dep I) ↔ (forall B, M.IsBase B -> (I inter B).Nonempty) ∧ I subseteq M.E
  proof: by
  simp_rw [dep_iff, dual_indep_iff_exists', dual_ground, and_congr_left_iff, not_and,
    not_exists, not_and, not_disjoint_iff_nonempty_inter, Classical.imp_iff_right_iff,
    iff_true_intro Or.inl]

中文:
定理 dual_dep_iff_对任意
  结论: (M✶.Dep I) ↔ (对任意 B, M.IsBase B -> (I inter B).非空) ∧ I subseteq M.E
  证明: by
  simp_rw [dep_iff, dual_indep_iff_exists', dual_ground, and_congr_left_iff, not_and,
    not_exists, not_and, not_disjoint_iff_nonempty_inter, Classical.imp_iff_right_iff,
    iff_true_intro Or.inl]

Depends on / 依赖: Classical, Classical.imp_iff_right_iff, Or.inl, and_congr_left_iff, dep_iff, dual_ground, dual_indep_iff_exists, iff_true_intro, imp_iff_right_iff, not_and, not_disjoint_iff_nonempty_inter, not_exists, simp_rw
-/
theorem dual_dep_iff_forall : (M✶.Dep I) ↔ (forall B, M.IsBase B -> (I inter B).Nonempty) ∧ I subseteq M.E := by
  simp_rw [dep_iff, dual_indep_iff_exists', dual_ground, and_congr_left_iff, not_and,
    not_exists, not_and, not_disjoint_iff_nonempty_inter, Classical.imp_iff_right_iff,
    iff_true_intro Or.inl]

/--
Instance `dual_finite` / 实例 `dual_finite`

English:
instance dual_finite
  signature: [M.Finite]
  body: ⟨M.ground_finite⟩

中文:
实例 dual_finite
  签名: [M.有限]
  定义体: ⟨M.ground_finite⟩

Depends on / 依赖: M.ground_finite, ground_finite
-/
instance dual_finite [M.Finite] : M✶.Finite :=
  ⟨M.ground_finite⟩

/--
Instance `dual_nonempty` / 实例 `dual_nonempty`

English:
instance dual_nonempty
  signature: [M.Nonempty]
  body: ⟨M.ground_nonempty⟩

中文:
实例 dual_nonempty
  签名: [M.非空]
  定义体: ⟨M.ground_nonempty⟩

Depends on / 依赖: M.ground_nonempty, ground_nonempty
-/
instance dual_nonempty [M.Nonempty] : M✶.Nonempty :=
  ⟨M.ground_nonempty⟩

/--
theorem `dual_isBase_iff` / 定理 `dual_isBase_iff`

English:
theorem dual_isBase_iff
  given: (hB : B subseteq M.E := by aesop_mat)
  proof: by
  rw [isBase_compl_iff_maximal_disjoint_isBase]; rw [isBase_iff_maximal_indep]; rw [maximal_subset_iff]; rw [maximal_subset_iff]
  simp [dual_indep_iff_exists', hB]

中文:
定理 dual_isBase_iff
  条件: (hB : B subseteq M.E := by aesop_mat)
  证明: by
  rw [isBase_compl_iff_maximal_disjoint_isBase]; rw [isBase_iff_maximal_indep]; rw [maximal_subset_iff]; rw [maximal_subset_iff]
  simp [dual_indep_iff_exists', hB]
-/
@[simp] theorem dual_isBase_iff (hB : B subseteq M.E := by aesop_mat) :
    M✶.IsBase B ↔ M.IsBase (M.E \ B) := by
  rw [isBase_compl_iff_maximal_disjoint_isBase]; rw [isBase_iff_maximal_indep]; rw [maximal_subset_iff]; rw [maximal_subset_iff]
  simp [dual_indep_iff_exists', hB]

/--
theorem `dual_isBase_iff'` / 定理 `dual_isBase_iff'`

English:
theorem dual_isBase_iff'
  statement: M✶.IsBase B ↔ M.IsBase (M.E \ B) ∧ B subseteq M.E
  proof: (em (B subseteq M.E)).elim (fun h => by rw [dual_isBase_iff, and_iff_left h])
    (fun h => iff_of_false (h ∘ (fun h' => h'.subset_ground)) (h ∘ And.right))

中文:
定理 dual_isBase_iff'
  结论: M✶.IsBase B ↔ M.IsBase (M.E \ B) ∧ B subseteq M.E
  证明: (em (B subseteq M.E)).elim (fun h => by rw [dual_isBase_iff, and_iff_left h])
    (fun h => iff_of_false (h ∘ (fun h' => h'.subset_ground)) (h ∘ And.right))

Depends on / 依赖: And.right, and_iff_left, dual_isBase_iff, iff_of_false, subset_ground, subseteq
-/
theorem dual_isBase_iff' : M✶.IsBase B ↔ M.IsBase (M.E \ B) ∧ B subseteq M.E :=
  (em (B subseteq M.E)).elim (fun h => by rw [dual_isBase_iff, and_iff_left h])
    (fun h => iff_of_false (h ∘ (fun h' => h'.subset_ground)) (h ∘ And.right))

/--
theorem `setOfPred_dual_isBase_eq` / 定理 `setOfPred_dual_isBase_eq`

English:
theorem setOfPred_dual_isBase_eq
  statement: {B | M✶.IsBase B} = (fun X => M.E \ X) '' {B | M.IsBase B}
  proof: by
  ext B
  simp only [mem_ofPred_eq, mem_image, dual_isBase_iff']
  refine ⟨fun h => ⟨_, h.1, sdiff_sdiff_cancel_left h.2⟩,
    fun ⟨B', hB', h⟩ => ⟨?_,h.symm.trans_subset sdiff_subset⟩⟩
  rwa [← h, sdiff_sdiff_cancel_left hB'.subset_ground]

@[deprecated (since := "2026-07-09")] alias setOf_dual_

中文:
定理 setOfPred_dual_isBase_eq
  结论: {B | M✶.IsBase B} = (fun X => M.E \ X) '' {B | M.IsBase B}
  证明: by
  ext B
  simp only [mem_ofPred_eq, mem_image, dual_isBase_iff']
  refine ⟨fun h => ⟨_, h.1, sdiff_sdiff_cancel_left h.2⟩,
    fun ⟨B', hB', h⟩ => ⟨?_,h.symm.trans_subset sdiff_subset⟩⟩
  rwa [← h, sdiff_sdiff_cancel_left hB'.subset_ground]

@[deprecated (since := "2026-07-09")] alias setOf_dual_

Depends on / 依赖: dual_isBase_iff, h.symm.trans_subset, mem_image, mem_ofPred_eq, sdiff_sdiff_cancel_left, sdiff_subset, subset_ground, trans_subset
-/
theorem setOfPred_dual_isBase_eq : {B | M✶.IsBase B} = (fun X => M.E \ X) '' {B | M.IsBase B} := by
  ext B
  simp only [mem_ofPred_eq, mem_image, dual_isBase_iff']
  refine ⟨fun h => ⟨_, h.1, sdiff_sdiff_cancel_left h.2⟩,
    fun ⟨B', hB', h⟩ => ⟨?_,h.symm.trans_subset sdiff_subset⟩⟩
  rwa [← h, sdiff_sdiff_cancel_left hB'.subset_ground]

@[deprecated (since := "2026-07-09")] alias setOf_dual_isBase_eq := setOfPred_dual_isBase_eq

/--
theorem `dual_dual` / 定理 `dual_dual`

English:
theorem dual_dual
  given: (M : Matroid α)
  statement: M✶✶ = M
  proof: ext_isBase rfl (fun B (h : B subseteq M.E) =>
    by rw [dual_isBase_iff, dual_isBase_iff, dual_ground, sdiff_sdiff_cancel_left h])

中文:
定理 dual_dual
  条件: (M : 拟阵 α)
  结论: M✶✶ = M
  证明: ext_isBase rfl (fun B (h : B subseteq M.E) =>
    by rw [dual_isBase_iff, dual_isBase_iff, dual_ground, sdiff_sdiff_cancel_left h])
-/
@[simp] theorem dual_dual (M : Matroid α) : M✶✶ = M :=
  ext_isBase rfl (fun B (h : B subseteq M.E) =>
    by rw [dual_isBase_iff, dual_isBase_iff, dual_ground, sdiff_sdiff_cancel_left h])

/--
theorem `dual_involutive` / 定理 `dual_involutive`

English:
theorem dual_involutive
  statement: Function.Involutive (dual : Matroid α -> Matroid α)
  proof: dual_dual

中文:
定理 dual_involutive
  结论: 函数.对合 (dual : 拟阵 α -> 拟阵 α)
  证明: dual_dual

Depends on / 依赖: dual_dual
-/
theorem dual_involutive : Function.Involutive (dual : Matroid α -> Matroid α) := dual_dual

/--
theorem `dual_injective` / 定理 `dual_injective`

English:
theorem dual_injective
  statement: Function.Injective (dual : Matroid α -> Matroid α)
  proof: dual_involutive.injective

中文:
定理 dual_injective
  结论: 函数.单射 (dual : 拟阵 α -> 拟阵 α)
  证明: dual_involutive.injective

Depends on / 依赖: dual_involutive, dual_involutive.injective, injective
-/
theorem dual_injective : Function.Injective (dual : Matroid α -> Matroid α) :=
  dual_involutive.injective

/--
theorem `dual_inj` / 定理 `dual_inj`

English:
theorem dual_inj
  given: {M₁ M₂ : Matroid α}
  statement: M₁✶ = M₂✶ ↔ M₁ = M₂
  proof: dual_injective.eq_iff

中文:
定理 dual_inj
  条件: {M₁ M₂ : 拟阵 α}
  结论: M₁✶ = M₂✶ ↔ M₁ = M₂
  证明: dual_injective.eq_iff
-/
@[simp] theorem dual_inj {M₁ M₂ : Matroid α} : M₁✶ = M₂✶ ↔ M₁ = M₂ :=
  dual_injective.eq_iff

/--
theorem `eq_dual_comm` / 定理 `eq_dual_comm`

English:
theorem eq_dual_comm
  given: {M₁ M₂ : Matroid α}
  statement: M₁ = M₂✶ ↔ M₂ = M₁✶
  proof: by
  rw [← dual_inj]; rw [dual_dual]; rw [eq_comm]

中文:
定理 eq_dual_comm
  条件: {M₁ M₂ : 拟阵 α}
  结论: M₁ = M₂✶ ↔ M₂ = M₁✶
  证明: by
  rw [← dual_inj]; rw [dual_dual]; rw [eq_comm]

Depends on / 依赖: dual_dual, dual_inj, eq_comm
-/
theorem eq_dual_comm {M₁ M₂ : Matroid α} : M₁ = M₂✶ ↔ M₂ = M₁✶ := by
  rw [← dual_inj]; rw [dual_dual]; rw [eq_comm]

/--
theorem `eq_dual_iff_dual_eq` / 定理 `eq_dual_iff_dual_eq`

English:
theorem eq_dual_iff_dual_eq
  given: {M₁ M₂ : Matroid α}
  statement: M₁ = M₂✶ ↔ M₁✶ = M₂
  proof: dual_involutive.eq_iff.symm

中文:
定理 eq_dual_iff_dual_eq
  条件: {M₁ M₂ : 拟阵 α}
  结论: M₁ = M₂✶ ↔ M₁✶ = M₂
  证明: dual_involutive.eq_iff.symm

Depends on / 依赖: dual_involutive, dual_involutive.eq_iff.symm, eq_iff
-/
theorem eq_dual_iff_dual_eq {M₁ M₂ : Matroid α} : M₁ = M₂✶ ↔ M₁✶ = M₂ :=
  dual_involutive.eq_iff.symm

/--
theorem `IsBase.compl_isBase_of_dual` / 定理 `IsBase.compl_isBase_of_dual`

English:
theorem IsBase.compl_isBase_of_dual
  given: (h : M✶.IsBase B)
  statement: M.IsBase (M.E \ B)
  proof: (dual_isBase_iff'.1 h).1

中文:
定理 IsBase.compl_isBase_of_dual
  条件: (h : M✶.IsBase B)
  结论: M.IsBase (M.E \ B)
  证明: (dual_isBase_iff'.1 h).1

Depends on / 依赖: dual_isBase_iff
-/
theorem IsBase.compl_isBase_of_dual (h : M✶.IsBase B) : M.IsBase (M.E \ B) :=
  (dual_isBase_iff'.1 h).1

/--
theorem `IsBase.compl_isBase_dual` / 定理 `IsBase.compl_isBase_dual`

English:
theorem IsBase.compl_isBase_dual
  given: (h : M.IsBase B)
  statement: M✶.IsBase (M.E \ B)
  proof: by
  rwa [dual_isBase_iff, sdiff_sdiff_cancel_left h.subset_ground]

中文:
定理 IsBase.compl_isBase_dual
  条件: (h : M.IsBase B)
  结论: M✶.IsBase (M.E \ B)
  证明: by
  rwa [dual_isBase_iff, sdiff_sdiff_cancel_left h.subset_ground]

Depends on / 依赖: dual_isBase_iff, h.subset_ground, sdiff_sdiff_cancel_left, subset_ground
-/
theorem IsBase.compl_isBase_dual (h : M.IsBase B) : M✶.IsBase (M.E \ B) := by
  rwa [dual_isBase_iff, sdiff_sdiff_cancel_left h.subset_ground]

/--
theorem `IsBase.compl_inter_isBasis_of_inter_isBasis` / 定理 `IsBase.compl_inter_isBasis_of_inter_isBasis`

English:
theorem IsBase.compl_inter_isBasis_of_inter_isBasis
  given: (hB : M.IsBase B) (hBX : M.IsBasis (B inter X) X)
  proof: by
  refine Indep.isBasis_of_forall_insert ?_ inter_subset_right (fun e he => ?_)
  · rw [dual_indep_iff_exists]
    exact ⟨B, hB, disjoint_of_subset_left inter_subset_left disjoint_sdiff_left⟩
  simp only [sdiff_inter_self_eq_sdiff, mem_sdiff, not_and, not_not, imp_iff_right he.1.1] at he
  simp_rw

中文:
定理 IsBase.compl_inter_isBasis_of_inter_isBasis
  条件: (hB : M.IsBase B) (hBX : M.是基 (B inter X) X)
  证明: by
  refine Indep.isBasis_of_forall_insert ?_ inter_subset_right (fun e he => ?_)
  · rw [dual_indep_iff_exists]
    exact ⟨B, hB, disjoint_of_subset_left inter_subset_left disjoint_sdiff_left⟩
  simp only [sdiff_inter_self_eq_sdiff, mem_sdiff, not_and, not_not, imp_iff_right he.1.1] at he
  simp_rw

Depends on / 依赖: Indep.isBasis_of_forall_insert, and_iff_left, and_iff_right, disjoint_of_subset_left, disjoint_sdiff_left, dual_dep_iff_forall, dual_indep_iff_exists, imp_iff_right, insert_subset_iff, inter_subset_left, inter_subset_left.trans, inter_subset_right, isBasis_of_forall_insert, mem_sdiff, nonempty_iff_ne_empty, not_and, not_ne_iff, not_not, sdiff_inter_self_eq_sdiff, sdiff_subset
-/
theorem IsBase.compl_inter_isBasis_of_inter_isBasis (hB : M.IsBase B) (hBX : M.IsBasis (B inter X) X) :
    M✶.IsBasis ((M.E \ B) inter (M.E \ X)) (M.E \ X) := by
  refine Indep.isBasis_of_forall_insert ?_ inter_subset_right (fun e he => ?_)
  · rw [dual_indep_iff_exists]
    exact ⟨B, hB, disjoint_of_subset_left inter_subset_left disjoint_sdiff_left⟩
  simp only [sdiff_inter_self_eq_sdiff, mem_sdiff, not_and, not_not, imp_iff_right he.1.1] at he
  simp_rw [dual_dep_iff_forall, insert_subset_iff, and_iff_right he.1.1,
    and_iff_left (inter_subset_left.trans sdiff_subset)]
  refine fun B' hB' => by_contra (fun hem => ?_)
  rw [nonempty_iff_ne_empty]; rw [not_ne_iff]; rw [← union_singleton]; rw [sdiff_inter_sdiff]; rw [union_inter_distrib_right]; rw [union_empty_iff]; rw [singleton_inter_eq_empty]; rw [sdiff_eq]; rw [inter_right_comm]; rw [inter_eq_self_of_subset_right hB'.subset_ground]; rw [← sdiff_eq]; rw [sdiff_eq_empty] at hem
  obtain ⟨f, hfb, hBf⟩ := hB.exchange hB' ⟨he.2, hem.2⟩
  have hi : M.Indep (insert f (B inter X)) := by
    refine hBf.indep.subset (insert_subset_insert ?_)
    simp_rw [subset_sdiff, and_iff_right inter_subset_left, disjoint_singleton_right,
      mem_inter_iff, iff_false_intro he.1.2, and_false, not_false_iff]
  exact hfb.2 (hBX.mem_of_insert_indep (Or.elim (hem.1 hfb.1) (False.elim ∘ hfb.2) id) hi).1

/--
theorem `IsBase.inter_isBasis_iff_compl_inter_isBasis_dual` / 定理 `IsBase.inter_isBasis_iff_compl_inter_isBasis_dual`

English:
theorem IsBase.inter_isBasis_iff_compl_inter_isBasis_dual
  statement: (hB : M.IsBase B)
  proof: by
  refine ⟨hB.compl_inter_isBasis_of_inter_isBasis, fun h => ?_⟩
  simpa [inter_eq_self_of_subset_right hX, inter_eq_self_of_subset_right hB.subset_ground] using
    hB.compl_isBase_dual.compl_inter_isBasis_of_inter_isBasis h

中文:
定理 IsBase.inter_isBasis_iff_compl_inter_isBasis_dual
  结论: (hB : M.IsBase B)
  证明: by
  refine ⟨hB.compl_inter_isBasis_of_inter_isBasis, fun h => ?_⟩
  simpa [inter_eq_self_of_subset_right hX, inter_eq_self_of_subset_right hB.subset_ground] using
    hB.compl_isBase_dual.compl_inter_isBasis_of_inter_isBasis h

Depends on / 依赖: IsBasis, M.IsBasis, aesop_mat, compl_inter_isBasis_of_inter_isBasis, compl_isBase_dual, hB.compl_inter_isBasis_of_inter_isBasis, hB.compl_isBase_dual.compl_inter_isBasis_of_inter_isBasis, hB.subset_ground, inter_eq_self_of_subset_right, subset_ground
-/
theorem IsBase.inter_isBasis_iff_compl_inter_isBasis_dual (hB : M.IsBase B)
    (hX : X subseteq M.E := by aesop_mat) :
    M.IsBasis (B inter X) X ↔ M✶.IsBasis ((M.E \ B) inter (M.E \ X)) (M.E \ X) := by
  refine ⟨hB.compl_inter_isBasis_of_inter_isBasis, fun h => ?_⟩
  simpa [inter_eq_self_of_subset_right hX, inter_eq_self_of_subset_right hB.subset_ground] using
    hB.compl_isBase_dual.compl_inter_isBasis_of_inter_isBasis h

/--
theorem `base_iff_dual_isBase_compl` / 定理 `base_iff_dual_isBase_compl`

English:
theorem base_iff_dual_isBase_compl
  given: (hB : B subseteq M.E := by aesop_mat)
  proof: by
  rw [dual_isBase_iff]; rw [sdiff_sdiff_cancel_left hB]

中文:
定理 base_iff_dual_isBase_compl
  条件: (hB : B subseteq M.E := by aesop_mat)
  证明: by
  rw [dual_isBase_iff]; rw [sdiff_sdiff_cancel_left hB]

Depends on / 依赖: IsBase, M.IsBase, aesop_mat, dual_isBase_iff, sdiff_sdiff_cancel_left
-/
theorem base_iff_dual_isBase_compl (hB : B subseteq M.E := by aesop_mat) :
    M.IsBase B ↔ M✶.IsBase (M.E \ B) := by
  rw [dual_isBase_iff]; rw [sdiff_sdiff_cancel_left hB]

/--
theorem `ground_not_isBase` / 定理 `ground_not_isBase`

English:
theorem ground_not_isBase
  given: (M : Matroid α) [h : RankPos M✶]
  statement: ¬M.IsBase M.E
  proof: by
  rwa [rankPos_iff, dual_isBase_iff, sdiff_empty] at h

中文:
定理 ground_not_isBase
  条件: (M : 拟阵 α) [h : RankPos M✶]
  结论: ¬M.IsBase M.E
  证明: by
  rwa [rankPos_iff, dual_isBase_iff, sdiff_empty] at h

Depends on / 依赖: dual_isBase_iff, rankPos_iff, sdiff_empty
-/
theorem ground_not_isBase (M : Matroid α) [h : RankPos M✶] : ¬M.IsBase M.E := by
  rwa [rankPos_iff, dual_isBase_iff, sdiff_empty] at h

/--
theorem `IsBase.ssubset_ground` / 定理 `IsBase.ssubset_ground`

English:
theorem IsBase.ssubset_ground
  given: [h : RankPos M✶] (hB : M.IsBase B)
  statement: B ⊂ M.E
  proof: hB.subset_ground.ssubset_of_ne (by rintro rfl; exact M.ground_not_isBase hB)

中文:
定理 IsBase.ssubset_ground
  条件: [h : RankPos M✶] (hB : M.IsBase B)
  结论: B ⊂ M.E
  证明: hB.subset_ground.ssubset_of_ne (by rintro rfl; exact M.ground_not_isBase hB)

Depends on / 依赖: M.ground_not_isBase, ground_not_isBase, hB.subset_ground.ssubset_of_ne, ssubset_of_ne, subset_ground
-/
theorem IsBase.ssubset_ground [h : RankPos M✶] (hB : M.IsBase B) : B ⊂ M.E :=
  hB.subset_ground.ssubset_of_ne (by rintro rfl; exact M.ground_not_isBase hB)

/--
theorem `Indep.ssubset_ground` / 定理 `Indep.ssubset_ground`

English:
theorem Indep.ssubset_ground
  given: [h : RankPos M✶] (hI : M.Indep I)
  statement: I ⊂ M.E
  proof: by
  obtain ⟨B, hB⟩ := hI.exists_isBase_superset; exact hB.2.trans_ssubset hB.1.ssubset_ground

中文:
定理 Indep.ssubset_ground
  条件: [h : RankPos M✶] (hI : M.Indep I)
  结论: I ⊂ M.E
  证明: by
  obtain ⟨B, hB⟩ := hI.exists_isBase_superset; exact hB.2.trans_ssubset hB.1.ssubset_ground

Depends on / 依赖: exists_isBase_superset, hI.exists_isBase_superset, ssubset_ground, trans_ssubset
-/
theorem Indep.ssubset_ground [h : RankPos M✶] (hI : M.Indep I) : I ⊂ M.E := by
  obtain ⟨B, hB⟩ := hI.exists_isBase_superset; exact hB.2.trans_ssubset hB.1.ssubset_ground

/--
Definition of `Coindep` / `Coindep` 的定义

English:
abbreviation Coindep
  signature: (M : Matroid α) (I : Set α)
  body: M✶.Indep I

中文:
缩写 Coindep
  签名: (M : 拟阵 α) (I : 集合 α)
  定义体: M✶.Indep I
-/
abbrev Coindep (M : Matroid α) (I : Set α) : Prop := M✶.Indep I

/--
theorem `coindep_def` / 定理 `coindep_def`

English:
theorem coindep_def
  statement: M.Coindep X ↔ M✶.Indep X
  proof: Iff.rfl

中文:
定理 coindep_def
  结论: M.Coindep X ↔ M✶.Indep X
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coindep_def : M.Coindep X ↔ M✶.Indep X := Iff.rfl

/--
theorem `Coindep.indep` / 定理 `Coindep.indep`

English:
theorem Coindep.indep
  given: (hX : M.Coindep X)
  statement: M✶.Indep X
  proof: hX

中文:
定理 Coindep.indep
  条件: (hX : M.Coindep X)
  结论: M✶.Indep X
  证明: hX
-/
theorem Coindep.indep (hX : M.Coindep X) : M✶.Indep X :=
  hX

/--
theorem `dual_coindep_iff` / 定理 `dual_coindep_iff`

English:
theorem dual_coindep_iff
  statement: M✶.Coindep X ↔ M.Indep X
  proof: by
  rw [Coindep]; rw [dual_dual]

中文:
定理 dual_coindep_iff
  结论: M✶.Coindep X ↔ M.Indep X
  证明: by
  rw [Coindep]; rw [dual_dual]
-/
@[simp] theorem dual_coindep_iff : M✶.Coindep X ↔ M.Indep X := by
  rw [Coindep]; rw [dual_dual]

/--
theorem `Indep.coindep` / 定理 `Indep.coindep`

English:
theorem Indep.coindep
  given: (hI : M.Indep I)
  statement: M✶.Coindep I
  proof: dual_coindep_iff.2 hI

中文:
定理 Indep.coindep
  条件: (hI : M.Indep I)
  结论: M✶.Coindep I
  证明: dual_coindep_iff.2 hI

Depends on / 依赖: dual_coindep_iff
-/
theorem Indep.coindep (hI : M.Indep I) : M✶.Coindep I :=
  dual_coindep_iff.2 hI

/--
theorem `coindep_iff_exists'` / 定理 `coindep_iff_exists'`

English:
theorem coindep_iff_exists'
  statement: M.Coindep X ↔ (exists B, M.IsBase B ∧ B subseteq M.E \ X) ∧ X subseteq M.E
  proof: by
  simp_rw [Coindep, dual_indep_iff_exists', and_comm (a := (_ : Set α) subseteq _), and_congr_left_iff,
    subset_sdiff]
  exact fun _ => ⟨fun ⟨B, hB, hXB⟩ => ⟨B, hB, hB.subset_ground, hXB.symm⟩,
    fun ⟨B, hB, _, hBX⟩ => ⟨B, hB, hBX.symm⟩⟩

中文:
定理 coindep_iff_存在'
  结论: M.Coindep X ↔ (存在 B, M.IsBase B ∧ B subseteq M.E \ X) ∧ X subseteq M.E
  证明: by
  simp_rw [Coindep, dual_indep_iff_exists', and_comm (a := (_ : Set α) subseteq _), and_congr_left_iff,
    subset_sdiff]
  exact fun _ => ⟨fun ⟨B, hB, hXB⟩ => ⟨B, hB, hB.subset_ground, hXB.symm⟩,
    fun ⟨B, hB, _, hBX⟩ => ⟨B, hB, hBX.symm⟩⟩

Depends on / 依赖: Coindep, and_comm, and_congr_left_iff, dual_indep_iff_exists, hB.subset_ground, hBX.symm, hXB.symm, simp_rw, subset_ground, subset_sdiff, subseteq
-/
theorem coindep_iff_exists' : M.Coindep X ↔ (exists B, M.IsBase B ∧ B subseteq M.E \ X) ∧ X subseteq M.E := by
  simp_rw [Coindep, dual_indep_iff_exists', and_comm (a := (_ : Set α) subseteq _), and_congr_left_iff,
    subset_sdiff]
  exact fun _ => ⟨fun ⟨B, hB, hXB⟩ => ⟨B, hB, hB.subset_ground, hXB.symm⟩,
    fun ⟨B, hB, _, hBX⟩ => ⟨B, hB, hBX.symm⟩⟩

/--
theorem `coindep_iff_exists` / 定理 `coindep_iff_exists`

English:
theorem coindep_iff_exists
  given: (hX : X subseteq M.E := by aesop_mat)
  proof: by
  rw [coindep_iff_exists']; rw [and_iff_left hX]

中文:
定理 coindep_iff_存在
  条件: (hX : X subseteq M.E := by aesop_mat)
  证明: by
  rw [coindep_iff_exists']; rw [and_iff_left hX]

Depends on / 依赖: Coindep, IsBase, M.Coindep, M.IsBase, aesop_mat, and_iff_left, coindep_iff_exists, subseteq
-/
theorem coindep_iff_exists (hX : X subseteq M.E := by aesop_mat) :
    M.Coindep X ↔ exists B, M.IsBase B ∧ B subseteq M.E \ X := by
  rw [coindep_iff_exists']; rw [and_iff_left hX]

/--
theorem `coindep_iff_subset_compl_isBase` / 定理 `coindep_iff_subset_compl_isBase`

English:
theorem coindep_iff_subset_compl_isBase
  statement: M.Coindep X ↔ exists B, M.IsBase B ∧ X subseteq M.E \ B
  proof: by
  simp_rw [coindep_iff_exists', subset_sdiff]
  exact ⟨fun ⟨⟨B, hB, _, hBX⟩, hX⟩ => ⟨B, hB, hX, hBX.symm⟩,
    fun ⟨B, hB, hXE, hXB⟩ => ⟨⟨B, hB, hB.subset_ground, hXB.symm⟩, hXE⟩⟩

@[aesop unsafe 10% (rule_sets := [Matroid])]

中文:
定理 coindep_iff_subset_compl_isBase
  结论: M.Coindep X ↔ 存在 B, M.IsBase B ∧ X subseteq M.E \ B
  证明: by
  simp_rw [coindep_iff_exists', subset_sdiff]
  exact ⟨fun ⟨⟨B, hB, _, hBX⟩, hX⟩ => ⟨B, hB, hX, hBX.symm⟩,
    fun ⟨B, hB, hXE, hXB⟩ => ⟨⟨B, hB, hB.subset_ground, hXB.symm⟩, hXE⟩⟩

@[aesop unsafe 10% (rule_sets := [Matroid])]

Depends on / 依赖: coindep_iff_exists, hB.subset_ground, hBX.symm, hXB.symm, simp_rw, subset_ground, subset_sdiff
-/
theorem coindep_iff_subset_compl_isBase : M.Coindep X ↔ exists B, M.IsBase B ∧ X subseteq M.E \ B := by
  simp_rw [coindep_iff_exists', subset_sdiff]
  exact ⟨fun ⟨⟨B, hB, _, hBX⟩, hX⟩ => ⟨B, hB, hX, hBX.symm⟩,
    fun ⟨B, hB, hXE, hXB⟩ => ⟨⟨B, hB, hB.subset_ground, hXB.symm⟩, hXE⟩⟩

@[aesop unsafe 10% (rule_sets := [Matroid])]
/--
theorem `Coindep.subset_ground` / 定理 `Coindep.subset_ground`

English:
theorem Coindep.subset_ground
  given: (hX : M.Coindep X)
  statement: X subseteq M.E
  proof: hX.indep.subset_ground

中文:
定理 Coindep.subset_ground
  条件: (hX : M.Coindep X)
  结论: X subseteq M.E
  证明: hX.indep.subset_ground

Depends on / 依赖: hX.indep.subset_ground, subset_ground
-/
theorem Coindep.subset_ground (hX : M.Coindep X) : X subseteq M.E :=
  hX.indep.subset_ground

/--
theorem `Coindep.exists_isBase_subset_compl` / 定理 `Coindep.exists_isBase_subset_compl`

English:
theorem Coindep.exists_isBase_subset_compl
  given: (h : M.Coindep X)
  statement: exists B, M.IsBase B ∧ B subseteq M.E \ X
  proof: (coindep_iff_exists h.subset_ground).1 h

中文:
定理 Coindep.存在_isBase_subset_compl
  条件: (h : M.Coindep X)
  结论: 存在 B, M.IsBase B ∧ B subseteq M.E \ X
  证明: (coindep_iff_exists h.subset_ground).1 h

Depends on / 依赖: coindep_iff_exists, h.subset_ground, subset_ground
-/
theorem Coindep.exists_isBase_subset_compl (h : M.Coindep X) : exists B, M.IsBase B ∧ B subseteq M.E \ X :=
  (coindep_iff_exists h.subset_ground).1 h

/--
theorem `Coindep.exists_subset_compl_isBase` / 定理 `Coindep.exists_subset_compl_isBase`

English:
theorem Coindep.exists_subset_compl_isBase
  given: (h : M.Coindep X)
  statement: exists B, M.IsBase B ∧ X subseteq M.E \ B
  proof: coindep_iff_subset_compl_isBase.1 h

中文:
定理 Coindep.存在_subset_compl_isBase
  条件: (h : M.Coindep X)
  结论: 存在 B, M.IsBase B ∧ X subseteq M.E \ B
  证明: coindep_iff_subset_compl_isBase.1 h

Depends on / 依赖: coindep_iff_subset_compl_isBase
-/
theorem Coindep.exists_subset_compl_isBase (h : M.Coindep X) : exists B, M.IsBase B ∧ X subseteq M.E \ B :=
  coindep_iff_subset_compl_isBase.1 h

end dual

end Matroid
