/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Rank.Finite
public import Mathlib.Combinatorics.Matroid.Loop
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Tactic.TautoSet

/-!
# `ℕ∞`-valued rank

If the 'cardinality' of `s : Set α` is taken to mean the `ℕ∞`-valued term `Set.encard s`,
then all bases of any `M : Matroid α` have the same cardinality,
and for each `X : Set α` with `X ⊆ M.E`, all `M`-bases for `X` have the same cardinality.
The 'rank' of a matroid is the cardinality of all its bases,
and the 'rank' of a set `X` in a matroid `M` is the cardinality of each `M`-basis of `X`.
This file defines these two concepts as a term `Matroid.eRank M : ℕ∞`
and a function `Matroid.eRk M : Set α → ℕ∞` respectively.

The rank function `Matroid.eRk` satisfies three properties, often known as (R1), (R2), (R3):
* `M.eRk X ≤ Set.encard X`,
* `M.eRk X ≤ M.eRk Y` for all `X ⊆ Y`,
* `M.eRk X + M.eRk Y ≥ M.eRk (X ∪ Y) + M.eRk (X ∩ Y)` for all `X, Y`.

In fact, if `α` is finite, then any function `Set α → ℕ∞` satisfying these properties
is the rank function of a `Matroid α`; in other words, properties (R1) - (R3) give an alternative
definition of finite matroids, and a finite matroid is determined by its rank function.
Because of this, and the convenient quantitative language of these axioms,
the rank function is often the preferred perspective on matroids in the literature.
(The above doesn't work as well for infinite matroids,
which is why mathlib defines matroids using bases/independence. )

## Main Declarations

* `Matroid.eRank M` is the `ℕ∞`-valued cardinality of each base of `M`.
* `Matroid.eRk M X` is the `ℕ∞`-valued cardinality of each `M`-basis of `X`.
* `Matroid.eRk_inter_add_eRk_union_le` : the function `M.eRk` is submodular.
* `Matroid.dual_eRk_add_eRank` : a subtraction-free formula for the dual rank of a set.

## Notes

It is natural to ask if equicardinality of bases holds if 'cardinality' refers to
a term in `Cardinal` instead of `ℕ∞`, but the answer is that it doesn't.
The cardinal-valued rank functions `Matroid.cRank` and `Matroid.cRk` are defined in
`Mathlib/Combinatorics/Matroid/Rank/Cardinal.lean`, but have less desirable properties in general.
See the module docstring of that file for a discussion.

## Implementation Details

It would be equivalent to define `Matroid.eRank (M : Matroid α) := (Matroid.cRank M).toENat`
and similar for `Matroid.eRk`, and some of the API for `cRank`/`cRk` would carry over
in a way that shortens certain proofs in this file (though not substantially).
Although this file transitively imports `Cardinal` via `Set.encard`,
there are plans to refactor the latter to be independent of the former,
which would carry over to the current version of this file.
-/

@[expose] public section

open Set ENat

namespace Matroid

variable {α : Type*} {M : Matroid α} {I B X Y : Set α} {n : Nat∞} {e f : α}

section Basic

/--
Definition of `eRank` / `eRank` 的定义

English:
definition eRank
  signature: (M : Matroid α)
  body: ⨆ B : {B // M.IsBase B}, B.1.encard

中文:
定义 eRank
  签名: (M : 拟阵 α)
  定义体: ⨆ B : {B // M.IsBase B}, B.1.encard

Depends on / 依赖: IsBase, M.IsBase, encard
-/
noncomputable def eRank (M : Matroid α) : Nat∞ := ⨆ B : {B // M.IsBase B}, B.1.encard

/--
Definition of `eRk` / `eRk` 的定义

English:
definition eRk
  signature: (M : Matroid α) (X : Set α)
  body: (M ↾ X).eRank

中文:
定义 eRk
  签名: (M : 拟阵 α) (X : 集合 α)
  定义体: (M ↾ X).eRank
-/
noncomputable def eRk (M : Matroid α) (X : Set α) : Nat∞ := (M ↾ X).eRank

/--
lemma `eRank_def` / 引理 `eRank_def`

English:
lemma eRank_def
  given: (M : Matroid α)
  statement: M.eRank = M.eRk M.E
  proof: by
  rw [eRk]; rw [restrict_ground_eq_self]

@[simp]

中文:
引理 eRank_def
  条件: (M : 拟阵 α)
  结论: M.eRank = M.eRk M.E
  证明: by
  rw [eRk]; rw [restrict_ground_eq_self]

@[simp]

Depends on / 依赖: restrict_ground_eq_self
-/
lemma eRank_def (M : Matroid α) : M.eRank = M.eRk M.E := by
  rw [eRk]; rw [restrict_ground_eq_self]

@[simp]
/--
lemma `eRk_ground` / 引理 `eRk_ground`

English:
lemma eRk_ground
  given: (M : Matroid α)
  statement: M.eRk M.E = M.eRank
  proof: M.eRank_def.symm

@[simp]

中文:
引理 eRk_ground
  条件: (M : 拟阵 α)
  结论: M.eRk M.E = M.eRank
  证明: M.eRank_def.symm

@[simp]

Depends on / 依赖: M.eRank_def.symm, eRank_def
-/
lemma eRk_ground (M : Matroid α) : M.eRk M.E = M.eRank :=
  M.eRank_def.symm

@[simp]
/--
lemma `eRank_restrict` / 引理 `eRank_restrict`

English:
lemma eRank_restrict
  given: (M : Matroid α) (X : Set α)
  statement: (M ↾ X).eRank = M.eRk X
  proof: rfl

中文:
引理 eRank_restrict
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: (M ↾ X).eRank = M.eRk X
  证明: rfl
-/
lemma eRank_restrict (M : Matroid α) (X : Set α) : (M ↾ X).eRank = M.eRk X := rfl

/--
lemma `IsBase.encard_eq_eRank` / 引理 `IsBase.encard_eq_eRank`

English:
lemma IsBase.encard_eq_eRank
  given: (hB : M.IsBase B)
  statement: B.encard = M.eRank
  proof: by
  simp [eRank, show forall B' : {B // M.IsBase B}, B'.1.encard = B.encard from
    fun B' => B'.2.encard_eq_encard_of_isBase hB]

中文:
引理 IsBase.encard_eq_eRank
  条件: (hB : M.IsBase B)
  结论: B.encard = M.eRank
  证明: by
  simp [eRank, show forall B' : {B // M.IsBase B}, B'.1.encard = B.encard from
    fun B' => B'.2.encard_eq_encard_of_isBase hB]

Depends on / 依赖: B.encard, IsBase, M.IsBase, encard, encard_eq_encard_of_isBase
-/
lemma IsBase.encard_eq_eRank (hB : M.IsBase B) : B.encard = M.eRank := by
  simp [eRank, show forall B' : {B // M.IsBase B}, B'.1.encard = B.encard from
    fun B' => B'.2.encard_eq_encard_of_isBase hB]

/--
lemma `IsBasis'.encard_eq_eRk` / 引理 `IsBasis'.encard_eq_eRk`

English:
lemma IsBasis'.encard_eq_eRk
  given: (hI : M.IsBasis' I X)
  statement: I.encard = M.eRk X
  proof: hI.isBase_restrict.encard_eq_eRank

中文:
引理 是基'.encard_eq_eRk
  条件: (hI : M.是基' I X)
  结论: I.encard = M.eRk X
  证明: hI.isBase_restrict.encard_eq_eRank
-/
lemma IsBasis'.encard_eq_eRk (hI : M.IsBasis' I X) : I.encard = M.eRk X :=
  hI.isBase_restrict.encard_eq_eRank

/--
lemma `IsBasis.encard_eq_eRk` / 引理 `IsBasis.encard_eq_eRk`

English:
lemma IsBasis.encard_eq_eRk
  given: (hI : M.IsBasis I X)
  statement: I.encard = M.eRk X
  proof: hI.isBasis'.encard_eq_eRk

中文:
引理 是基.encard_eq_eRk
  条件: (hI : M.是基 I X)
  结论: I.encard = M.eRk X
  证明: hI.isBasis'.encard_eq_eRk

Depends on / 依赖: encard_eq_eRk, hI.isBasis, isBasis
-/
lemma IsBasis.encard_eq_eRk (hI : M.IsBasis I X) : I.encard = M.eRk X :=
  hI.isBasis'.encard_eq_eRk

/--
lemma `eq_eRk_iff` / 引理 `eq_eRk_iff`

English:
lemma eq_eRk_iff
  given: (hX : X subseteq M.E := by aesop_mat)
  proof: ⟨fun h => (M.exists_isBasis X).elim (fun I hI => ⟨I, hI, by rw [hI.encard_eq_eRk, ← h]⟩),
    fun ⟨I, hI, hIc⟩ => by rw [← hI.encard_eq_eRk, hIc]⟩

中文:
引理 eq_eRk_iff
  条件: (hX : X subseteq M.E := by aesop_mat)
  证明: ⟨fun h => (M.exists_isBasis X).elim (fun I hI => ⟨I, hI, by rw [hI.encard_eq_eRk, ← h]⟩),
    fun ⟨I, hI, hIc⟩ => by rw [← hI.encard_eq_eRk, hIc]⟩

Depends on / 依赖: I.encard, IsBasis, M.IsBasis, M.eRk, M.exists_isBasis, aesop_mat, encard, encard_eq_eRk, exists_isBasis, hI.encard_eq_eRk
-/
lemma eq_eRk_iff (hX : X subseteq M.E := by aesop_mat) :
    M.eRk X = n ↔ exists I, M.IsBasis I X ∧ I.encard = n :=
  ⟨fun h => (M.exists_isBasis X).elim (fun I hI => ⟨I, hI, by rw [hI.encard_eq_eRk, ← h]⟩),
    fun ⟨I, hI, hIc⟩ => by rw [← hI.encard_eq_eRk, hIc]⟩

/--
lemma `Indep.eRk_eq_encard` / 引理 `Indep.eRk_eq_encard`

English:
lemma Indep.eRk_eq_encard
  given: (hI : M.Indep I)
  statement: M.eRk I = I.encard
  proof: (eq_eRk_iff hI.subset_ground).mpr ⟨I, hI.isBasis_self, rfl⟩

中文:
引理 Indep.eRk_eq_encard
  条件: (hI : M.Indep I)
  结论: M.eRk I = I.encard
  证明: (eq_eRk_iff hI.subset_ground).mpr ⟨I, hI.isBasis_self, rfl⟩

Depends on / 依赖: eq_eRk_iff, hI.isBasis_self, hI.subset_ground, isBasis_self, subset_ground
-/
lemma Indep.eRk_eq_encard (hI : M.Indep I) : M.eRk I = I.encard :=
  (eq_eRk_iff hI.subset_ground).mpr ⟨I, hI.isBasis_self, rfl⟩

/--
lemma `IsBasis'.eRk_eq_eRk` / 引理 `IsBasis'.eRk_eq_eRk`

English:
lemma IsBasis'.eRk_eq_eRk
  given: (hIX : M.IsBasis' I X)
  statement: M.eRk I = M.eRk X
  proof: by
  rw [← hIX.encard_eq_eRk]; rw [hIX.indep.eRk_eq_encard]

中文:
引理 是基'.eRk_eq_eRk
  条件: (hIX : M.是基' I X)
  结论: M.eRk I = M.eRk X
  证明: by
  rw [← hIX.encard_eq_eRk]; rw [hIX.indep.eRk_eq_encard]
-/
lemma IsBasis'.eRk_eq_eRk (hIX : M.IsBasis' I X) : M.eRk I = M.eRk X := by
  rw [← hIX.encard_eq_eRk]; rw [hIX.indep.eRk_eq_encard]

/--
lemma `IsBasis.eRk_eq_eRk` / 引理 `IsBasis.eRk_eq_eRk`

English:
lemma IsBasis.eRk_eq_eRk
  given: (hIX : M.IsBasis I X)
  statement: M.eRk I = M.eRk X
  proof: by
  rw [← hIX.encard_eq_eRk]; rw [hIX.indep.eRk_eq_encard]

中文:
引理 是基.eRk_eq_eRk
  条件: (hIX : M.是基 I X)
  结论: M.eRk I = M.eRk X
  证明: by
  rw [← hIX.encard_eq_eRk]; rw [hIX.indep.eRk_eq_encard]

Depends on / 依赖: eRk_eq_encard, encard_eq_eRk, hIX.encard_eq_eRk, hIX.indep.eRk_eq_encard
-/
lemma IsBasis.eRk_eq_eRk (hIX : M.IsBasis I X) : M.eRk I = M.eRk X := by
  rw [← hIX.encard_eq_eRk]; rw [hIX.indep.eRk_eq_encard]

/--
lemma `IsBasis'.eRk_eq_encard` / 引理 `IsBasis'.eRk_eq_encard`

English:
lemma IsBasis'.eRk_eq_encard
  given: (hIX : M.IsBasis' I X)
  statement: M.eRk X = I.encard
  proof: by
  rw [← hIX.eRk_eq_eRk]; rw [hIX.indep.eRk_eq_encard]

中文:
引理 是基'.eRk_eq_encard
  条件: (hIX : M.是基' I X)
  结论: M.eRk X = I.encard
  证明: by
  rw [← hIX.eRk_eq_eRk]; rw [hIX.indep.eRk_eq_encard]
-/
lemma IsBasis'.eRk_eq_encard (hIX : M.IsBasis' I X) : M.eRk X = I.encard := by
  rw [← hIX.eRk_eq_eRk]; rw [hIX.indep.eRk_eq_encard]

/--
lemma `IsBasis.eRk_eq_encard` / 引理 `IsBasis.eRk_eq_encard`

English:
lemma IsBasis.eRk_eq_encard
  given: (hIX : M.IsBasis I X)
  statement: M.eRk X = I.encard
  proof: by
  rw [← hIX.eRk_eq_eRk]; rw [hIX.indep.eRk_eq_encard]

中文:
引理 是基.eRk_eq_encard
  条件: (hIX : M.是基 I X)
  结论: M.eRk X = I.encard
  证明: by
  rw [← hIX.eRk_eq_eRk]; rw [hIX.indep.eRk_eq_encard]

Depends on / 依赖: eRk_eq_eRk, eRk_eq_encard, hIX.eRk_eq_eRk, hIX.indep.eRk_eq_encard
-/
lemma IsBasis.eRk_eq_encard (hIX : M.IsBasis I X) : M.eRk X = I.encard := by
  rw [← hIX.eRk_eq_eRk]; rw [hIX.indep.eRk_eq_encard]

/--
lemma `IsBase.eRk_eq_eRank` / 引理 `IsBase.eRk_eq_eRank`

English:
lemma IsBase.eRk_eq_eRank
  given: (hB : M.IsBase B)
  statement: M.eRk B = M.eRank
  proof: by
  rw [hB.indep.eRk_eq_encard]; rw [eRank_def]; rw [hB.isBasis_ground.encard_eq_eRk]

@[simp]

中文:
引理 IsBase.eRk_eq_eRank
  条件: (hB : M.IsBase B)
  结论: M.eRk B = M.eRank
  证明: by
  rw [hB.indep.eRk_eq_encard]; rw [eRank_def]; rw [hB.isBasis_ground.encard_eq_eRk]

@[simp]

Depends on / 依赖: eRank_def, eRk_eq_encard, encard_eq_eRk, hB.indep.eRk_eq_encard, hB.isBasis_ground.encard_eq_eRk, isBasis_ground
-/
lemma IsBase.eRk_eq_eRank (hB : M.IsBase B) : M.eRk B = M.eRank := by
  rw [hB.indep.eRk_eq_encard]; rw [eRank_def]; rw [hB.isBasis_ground.encard_eq_eRk]

@[simp]
/--
lemma `eRk_inter_ground` / 引理 `eRk_inter_ground`

English:
lemma eRk_inter_ground
  given: (M : Matroid α) (X : Set α)
  statement: M.eRk (X inter M.E) = M.eRk X
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.eRk_eq_eRk]; rw [hI.isBasis_inter_ground.eRk_eq_eRk]

@[simp]

中文:
引理 eRk_inter_ground
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: M.eRk (X inter M.E) = M.eRk X
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.eRk_eq_eRk]; rw [hI.isBasis_inter_ground.eRk_eq_eRk]

@[simp]

Depends on / 依赖: M.exists_isBasis, eRk_eq_eRk, exists_isBasis, hI.eRk_eq_eRk, hI.isBasis_inter_ground.eRk_eq_eRk, isBasis_inter_ground
-/
lemma eRk_inter_ground (M : Matroid α) (X : Set α) : M.eRk (X inter M.E) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.eRk_eq_eRk]; rw [hI.isBasis_inter_ground.eRk_eq_eRk]

@[simp]
/--
lemma `eRk_ground_inter` / 引理 `eRk_ground_inter`

English:
lemma eRk_ground_inter
  given: (M : Matroid α) (X : Set α)
  statement: M.eRk (M.E inter X) = M.eRk X
  proof: by
  rw [inter_comm]; rw [eRk_inter_ground]

@[simp]

中文:
引理 eRk_ground_inter
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: M.eRk (M.E inter X) = M.eRk X
  证明: by
  rw [inter_comm]; rw [eRk_inter_ground]

@[simp]

Depends on / 依赖: eRk_inter_ground, inter_comm
-/
lemma eRk_ground_inter (M : Matroid α) (X : Set α) : M.eRk (M.E inter X) = M.eRk X := by
  rw [inter_comm]; rw [eRk_inter_ground]

@[simp]
/--
lemma `eRk_union_ground` / 引理 `eRk_union_ground`

English:
lemma eRk_union_ground
  given: (M : Matroid α) (X : Set α)
  statement: M.eRk (X union M.E) = M.eRank
  proof: by
  rw [← eRk_inter_ground]; rw [inter_eq_self_of_subset_right subset_union_right]; rw [eRank_def]

@[simp]

中文:
引理 eRk_union_ground
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: M.eRk (X union M.E) = M.eRank
  证明: by
  rw [← eRk_inter_ground]; rw [inter_eq_self_of_subset_right subset_union_right]; rw [eRank_def]

@[simp]

Depends on / 依赖: eRank_def, eRk_inter_ground, inter_eq_self_of_subset_right, subset_union_right
-/
lemma eRk_union_ground (M : Matroid α) (X : Set α) : M.eRk (X union M.E) = M.eRank := by
  rw [← eRk_inter_ground]; rw [inter_eq_self_of_subset_right subset_union_right]; rw [eRank_def]

@[simp]
/--
lemma `eRk_ground_union` / 引理 `eRk_ground_union`

English:
lemma eRk_ground_union
  given: (M : Matroid α) (X : Set α)
  statement: M.eRk (M.E union X) = M.eRank
  proof: by
  rw [union_comm]; rw [eRk_union_ground]

中文:
引理 eRk_ground_union
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: M.eRk (M.E union X) = M.eRank
  证明: by
  rw [union_comm]; rw [eRk_union_ground]

Depends on / 依赖: eRk_union_ground, union_comm
-/
lemma eRk_ground_union (M : Matroid α) (X : Set α) : M.eRk (M.E union X) = M.eRank := by
  rw [union_comm]; rw [eRk_union_ground]

/--
lemma `eRk_insert_of_notMem_ground` / 引理 `eRk_insert_of_notMem_ground`

English:
lemma eRk_insert_of_notMem_ground
  given: (X : Set α) (he : e ∉ M.E)
  statement: M.eRk (insert e X) = M.eRk X
  proof: by
  rw [← eRk_inter_ground]; rw [insert_inter_of_notMem he]; rw [eRk_inter_ground]

中文:
引理 eRk_insert_of_notMem_ground
  条件: (X : 集合 α) (he : e ∉ M.E)
  结论: M.eRk (insert e X) = M.eRk X
  证明: by
  rw [← eRk_inter_ground]; rw [insert_inter_of_notMem he]; rw [eRk_inter_ground]

Depends on / 依赖: eRk_inter_ground, insert_inter_of_notMem
-/
lemma eRk_insert_of_notMem_ground (X : Set α) (he : e ∉ M.E) : M.eRk (insert e X) = M.eRk X := by
  rw [← eRk_inter_ground]; rw [insert_inter_of_notMem he]; rw [eRk_inter_ground]

/--
lemma `eRk_eq_eRank` / 引理 `eRk_eq_eRank`

English:
lemma eRk_eq_eRank
  given: (hX : M.E subseteq X)
  statement: M.eRk X = M.eRank
  proof: by
  rw [← eRk_inter_ground]; rw [inter_eq_self_of_subset_right hX]; rw [eRank_def]

中文:
引理 eRk_eq_eRank
  条件: (hX : M.E subseteq X)
  结论: M.eRk X = M.eRank
  证明: by
  rw [← eRk_inter_ground]; rw [inter_eq_self_of_subset_right hX]; rw [eRank_def]

Depends on / 依赖: eRank_def, eRk_inter_ground, inter_eq_self_of_subset_right
-/
lemma eRk_eq_eRank (hX : M.E subseteq X) : M.eRk X = M.eRank := by
  rw [← eRk_inter_ground]; rw [inter_eq_self_of_subset_right hX]; rw [eRank_def]

/--
lemma `eRk_compl_union_of_disjoint` / 引理 `eRk_compl_union_of_disjoint`

English:
lemma eRk_compl_union_of_disjoint
  given: (M : Matroid α) (hXY : Disjoint X Y)
  proof: by
  rw [← eRk_inter_ground]; rw [union_inter_distrib_right]; rw [inter_eq_self_of_subset_left sdiff_subset]; rw [union_eq_self_of_subset_right
      (subset_sdiff.2 ⟨inter_subset_right]; rw [hXY.symm.mono_left inter_subset_left⟩)]

中文:
引理 eRk_compl_union_of_disjoint
  条件: (M : 拟阵 α) (hXY : Disjoint X Y)
  证明: by
  rw [← eRk_inter_ground]; rw [union_inter_distrib_right]; rw [inter_eq_self_of_subset_left sdiff_subset]; rw [union_eq_self_of_subset_right
      (subset_sdiff.2 ⟨inter_subset_right]; rw [hXY.symm.mono_left inter_subset_left⟩)]

Depends on / 依赖: eRk_inter_ground, hXY.symm.mono_left, inter_eq_self_of_subset_left, inter_subset_left, inter_subset_right, mono_left, sdiff_subset, subset_sdiff, union_eq_self_of_subset_right, union_inter_distrib_right
-/
lemma eRk_compl_union_of_disjoint (M : Matroid α) (hXY : Disjoint X Y) :
    M.eRk (M.E \ X union Y) = M.eRk (M.E \ X) := by
  rw [← eRk_inter_ground]; rw [union_inter_distrib_right]; rw [inter_eq_self_of_subset_left sdiff_subset]; rw [union_eq_self_of_subset_right
      (subset_sdiff.2 ⟨inter_subset_right]; rw [hXY.symm.mono_left inter_subset_left⟩)]

/--
lemma `one_le_eRank` / 引理 `one_le_eRank`

English:
lemma one_le_eRank
  given: (M : Matroid α) [RankPos M]
  statement: 1 <= M.eRank
  proof: by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank]; rw [one_le_encard_iff_nonempty]
  exact hB.nonempty

@[simp]

中文:
引理 one_le_eRank
  条件: (M : 拟阵 α) [RankPos M]
  结论: 1 <= M.eRank
  证明: by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank]; rw [one_le_encard_iff_nonempty]
  exact hB.nonempty

@[simp]

Depends on / 依赖: M.exists_isBase, encard_eq_eRank, exists_isBase, hB.encard_eq_eRank, hB.nonempty, nonempty, one_le_encard_iff_nonempty
-/
lemma one_le_eRank (M : Matroid α) [RankPos M] : 1 <= M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank]; rw [one_le_encard_iff_nonempty]
  exact hB.nonempty

@[simp]
/--
lemma `eRk_univ_eq` / 引理 `eRk_univ_eq`

English:
lemma eRk_univ_eq
  given: (M : Matroid α)
  statement: M.eRk univ = M.eRank
  proof: by
  rw [← eRk_inter_ground]; rw [univ_inter]; rw [eRank_def]

@[simp]

中文:
引理 eRk_univ_eq
  条件: (M : 拟阵 α)
  结论: M.eRk univ = M.eRank
  证明: by
  rw [← eRk_inter_ground]; rw [univ_inter]; rw [eRank_def]

@[simp]

Depends on / 依赖: eRank_def, eRk_inter_ground, univ_inter
-/
lemma eRk_univ_eq (M : Matroid α) : M.eRk univ = M.eRank := by
  rw [← eRk_inter_ground]; rw [univ_inter]; rw [eRank_def]

@[simp]
/--
lemma `eRk_empty` / 引理 `eRk_empty`

English:
lemma eRk_empty
  given: (M : Matroid α)
  statement: M.eRk ∅ = 0
  proof: by
  rw [← M.empty_indep.isBasis_self.encard_eq_eRk]; rw [encard_empty]

@[simp]

中文:
引理 eRk_empty
  条件: (M : 拟阵 α)
  结论: M.eRk ∅ = 0
  证明: by
  rw [← M.empty_indep.isBasis_self.encard_eq_eRk]; rw [encard_empty]

@[simp]

Depends on / 依赖: M.empty_indep.isBasis_self.encard_eq_eRk, empty_indep, encard_empty, encard_eq_eRk, isBasis_self
-/
lemma eRk_empty (M : Matroid α) : M.eRk ∅ = 0 := by
  rw [← M.empty_indep.isBasis_self.encard_eq_eRk]; rw [encard_empty]

@[simp]
/--
lemma `eRk_closure_eq` / 引理 `eRk_closure_eq`

English:
lemma eRk_closure_eq
  given: (M : Matroid α) (X : Set α)
  statement: M.eRk (M.closure X) = M.eRk X
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.closure_eq_closure]; rw [← hI.indep.isBasis_closure.encard_eq_eRk]; rw [hI.encard_eq_eRk]

@[simp]

中文:
引理 eRk_closure_eq
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: M.eRk (M.closure X) = M.eRk X
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.closure_eq_closure]; rw [← hI.indep.isBasis_closure.encard_eq_eRk]; rw [hI.encard_eq_eRk]

@[simp]

Depends on / 依赖: M.exists_isBasis, closure_eq_closure, encard_eq_eRk, exists_isBasis, hI.closure_eq_closure, hI.encard_eq_eRk, hI.indep.isBasis_closure.encard_eq_eRk, isBasis_closure
-/
lemma eRk_closure_eq (M : Matroid α) (X : Set α) : M.eRk (M.closure X) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.closure_eq_closure]; rw [← hI.indep.isBasis_closure.encard_eq_eRk]; rw [hI.encard_eq_eRk]

@[simp]
/--
lemma `eRk_union_closure_right_eq` / 引理 `eRk_union_closure_right_eq`

English:
lemma eRk_union_closure_right_eq
  given: (M : Matroid α) (X Y : Set α)
  proof: by
  rw [← eRk_closure_eq]; rw [closure_union_closure_right_eq]; rw [eRk_closure_eq]

@[simp]

中文:
引理 eRk_union_closure_right_eq
  条件: (M : 拟阵 α) (X Y : 集合 α)
  证明: by
  rw [← eRk_closure_eq]; rw [closure_union_closure_right_eq]; rw [eRk_closure_eq]

@[simp]

Depends on / 依赖: closure_union_closure_right_eq, eRk_closure_eq
-/
lemma eRk_union_closure_right_eq (M : Matroid α) (X Y : Set α) :
    M.eRk (X union M.closure Y) = M.eRk (X union Y) := by
  rw [← eRk_closure_eq]; rw [closure_union_closure_right_eq]; rw [eRk_closure_eq]

@[simp]
/--
lemma `eRk_union_closure_left_eq` / 引理 `eRk_union_closure_left_eq`

English:
lemma eRk_union_closure_left_eq
  given: (M : Matroid α) (X Y : Set α)
  proof: by
  rw [← eRk_closure_eq]; rw [closure_union_closure_left_eq]; rw [eRk_closure_eq]

@[simp]

中文:
引理 eRk_union_closure_left_eq
  条件: (M : 拟阵 α) (X Y : 集合 α)
  证明: by
  rw [← eRk_closure_eq]; rw [closure_union_closure_left_eq]; rw [eRk_closure_eq]

@[simp]

Depends on / 依赖: closure_union_closure_left_eq, eRk_closure_eq
-/
lemma eRk_union_closure_left_eq (M : Matroid α) (X Y : Set α) :
    M.eRk (M.closure X union Y) = M.eRk (X union Y) := by
  rw [← eRk_closure_eq]; rw [closure_union_closure_left_eq]; rw [eRk_closure_eq]

@[simp]
/--
lemma `eRk_insert_closure_eq` / 引理 `eRk_insert_closure_eq`

English:
lemma eRk_insert_closure_eq
  given: (M : Matroid α) (e : α) (X : Set α)
  proof: by
  rw [← union_singleton]; rw [eRk_union_closure_left_eq]; rw [union_singleton]

中文:
引理 eRk_insert_closure_eq
  条件: (M : 拟阵 α) (e : α) (X : 集合 α)
  证明: by
  rw [← union_singleton]; rw [eRk_union_closure_left_eq]; rw [union_singleton]

Depends on / 依赖: eRk_union_closure_left_eq, union_singleton
-/
lemma eRk_insert_closure_eq (M : Matroid α) (e : α) (X : Set α) :
    M.eRk (insert e (M.closure X)) = M.eRk (insert e X) := by
  rw [← union_singleton]; rw [eRk_union_closure_left_eq]; rw [union_singleton]

/-- A version of `Matroid.restrict_eRk_eq` with no `X ⊆ R` hypothesis and thus a less simple RHS. -/
@[simp]
/--
lemma `restrict_eRk_eq'` / 引理 `restrict_eRk_eq'`

English:
lemma restrict_eRk_eq'
  given: (M : Matroid α) (R X : Set α)
  statement: (M ↾ R).eRk X = M.eRk (X inter R)
  proof: by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_isBasis' X
  rw [hI.eRk_eq_encard]
  rw [isBasis'_iff_isBasis_inter_ground]; rw [isBasis_restrict_iff']; rw [restrict_ground_eq] at hI
  rw [← eRk_inter_ground]; rw [← hI.1.eRk_eq_encard]

中文:
引理 restrict_eRk_eq'
  条件: (M : 拟阵 α) (R X : 集合 α)
  结论: (M ↾ R).eRk X = M.eRk (X inter R)
  证明: by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_isBasis' X
  rw [hI.eRk_eq_encard]
  rw [isBasis'_iff_isBasis_inter_ground]; rw [isBasis_restrict_iff']; rw [restrict_ground_eq] at hI
  rw [← eRk_inter_ground]; rw [← hI.1.eRk_eq_encard]

Depends on / 依赖: _iff_isBasis_inter_ground, eRk_eq_encard, eRk_inter_ground, exists_isBasis, hI.eRk_eq_encard, isBasis, isBasis_restrict_iff, restrict_ground_eq
-/
lemma restrict_eRk_eq' (M : Matroid α) (R X : Set α) : (M ↾ R).eRk X = M.eRk (X inter R) := by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_isBasis' X
  rw [hI.eRk_eq_encard]
  rw [isBasis'_iff_isBasis_inter_ground]; rw [isBasis_restrict_iff']; rw [restrict_ground_eq] at hI
  rw [← eRk_inter_ground]; rw [← hI.1.eRk_eq_encard]

/--
lemma `restrict_eRk_eq` / 引理 `restrict_eRk_eq`

English:
lemma restrict_eRk_eq
  given: (M : Matroid α) {R : Set α} (h : X subseteq R)
  statement: (M ↾ R).eRk X = M.eRk X
  proof: by
  rw [restrict_eRk_eq']; rw [inter_eq_self_of_subset_left h]

中文:
引理 restrict_eRk_eq
  条件: (M : 拟阵 α) {R : 集合 α} (h : X subseteq R)
  结论: (M ↾ R).eRk X = M.eRk X
  证明: by
  rw [restrict_eRk_eq']; rw [inter_eq_self_of_subset_left h]

Depends on / 依赖: inter_eq_self_of_subset_left, restrict_eRk_eq
-/
lemma restrict_eRk_eq (M : Matroid α) {R : Set α} (h : X subseteq R) : (M ↾ R).eRk X = M.eRk X := by
  rw [restrict_eRk_eq']; rw [inter_eq_self_of_subset_left h]

/--
lemma `IsBasis'.eRk_eq_eRk_union` / 引理 `IsBasis'.eRk_eq_eRk_union`

English:
lemma IsBasis'.eRk_eq_eRk_union
  given: (hIX : M.IsBasis' I X) (Y : Set α)
  proof: by
  rw [← eRk_union_closure_left_eq]; rw [hIX.closure_eq_closure]; rw [eRk_union_closure_left_eq]

中文:
引理 是基'.eRk_eq_eRk_union
  条件: (hIX : M.是基' I X) (Y : 集合 α)
  证明: by
  rw [← eRk_union_closure_left_eq]; rw [hIX.closure_eq_closure]; rw [eRk_union_closure_left_eq]
-/
lemma IsBasis'.eRk_eq_eRk_union (hIX : M.IsBasis' I X) (Y : Set α) :
    M.eRk (I union Y) = M.eRk (X union Y) := by
  rw [← eRk_union_closure_left_eq]; rw [hIX.closure_eq_closure]; rw [eRk_union_closure_left_eq]

/--
lemma `IsBasis'.eRk_eq_eRk_insert` / 引理 `IsBasis'.eRk_eq_eRk_insert`

English:
lemma IsBasis'.eRk_eq_eRk_insert
  given: (hIX : M.IsBasis' I X) (e : α)
  proof: by
  rw [← union_singleton]; rw [hIX.eRk_eq_eRk_union]; rw [union_singleton]

中文:
引理 是基'.eRk_eq_eRk_insert
  条件: (hIX : M.是基' I X) (e : α)
  证明: by
  rw [← union_singleton]; rw [hIX.eRk_eq_eRk_union]; rw [union_singleton]
-/
lemma IsBasis'.eRk_eq_eRk_insert (hIX : M.IsBasis' I X) (e : α) :
    M.eRk (insert e I) = M.eRk (insert e X) := by
  rw [← union_singleton]; rw [hIX.eRk_eq_eRk_union]; rw [union_singleton]

/--
lemma `IsBasis.eRk_eq_eRk_union` / 引理 `IsBasis.eRk_eq_eRk_union`

English:
lemma IsBasis.eRk_eq_eRk_union
  given: (hIX : M.IsBasis I X) (Y : Set α)
  statement: M.eRk (I union Y) = M.eRk (X union Y)
  proof: hIX.isBasis'.eRk_eq_eRk_union Y

中文:
引理 是基.eRk_eq_eRk_union
  条件: (hIX : M.是基 I X) (Y : 集合 α)
  结论: M.eRk (I union Y) = M.eRk (X union Y)
  证明: hIX.isBasis'.eRk_eq_eRk_union Y

Depends on / 依赖: eRk_eq_eRk_union, hIX.isBasis, isBasis
-/
lemma IsBasis.eRk_eq_eRk_union (hIX : M.IsBasis I X) (Y : Set α) : M.eRk (I union Y) = M.eRk (X union Y) :=
  hIX.isBasis'.eRk_eq_eRk_union Y

/--
lemma `IsBasis.eRk_eq_eRk_insert` / 引理 `IsBasis.eRk_eq_eRk_insert`

English:
lemma IsBasis.eRk_eq_eRk_insert
  given: (hIX : M.IsBasis I X) (e : α)
  proof: by
  rw [← union_singleton]; rw [hIX.eRk_eq_eRk_union]; rw [union_singleton]

中文:
引理 是基.eRk_eq_eRk_insert
  条件: (hIX : M.是基 I X) (e : α)
  证明: by
  rw [← union_singleton]; rw [hIX.eRk_eq_eRk_union]; rw [union_singleton]

Depends on / 依赖: eRk_eq_eRk_union, hIX.eRk_eq_eRk_union, union_singleton
-/
lemma IsBasis.eRk_eq_eRk_insert (hIX : M.IsBasis I X) (e : α) :
    M.eRk (insert e I) = M.eRk (insert e X) := by
  rw [← union_singleton]; rw [hIX.eRk_eq_eRk_union]; rw [union_singleton]

/--
lemma `eRk_le_encard` / 引理 `eRk_le_encard`

English:
lemma eRk_le_encard
  given: (M : Matroid α) (X : Set α)
  statement: M.eRk X <= X.encard
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard]
  exact encard_mono hI.subset

中文:
引理 eRk_le_encard
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: M.eRk X <= X.encard
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard]
  exact encard_mono hI.subset

Depends on / 依赖: M.exists_isBasis, eRk_eq_encard, encard_mono, exists_isBasis, hI.eRk_eq_encard, hI.subset, subset
-/
lemma eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk X <= X.encard := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard]
  exact encard_mono hI.subset

/--
lemma `eRank_le_encard_ground` / 引理 `eRank_le_encard_ground`

English:
lemma eRank_le_encard_ground
  given: (M : Matroid α)
  statement: M.eRank <= M.E.encard
  proof: M.eRank_def.trans_le M.eRk_le_encard M.E

中文:
引理 eRank_le_encard_ground
  条件: (M : 拟阵 α)
  结论: M.eRank <= M.E.encard
  证明: M.eRank_def.trans_le M.eRk_le_encard M.E

Depends on / 依赖: M.eRank_def.trans_le, M.eRk_le_encard, eRank_def, eRk_le_encard, trans_le
-/
lemma eRank_le_encard_ground (M : Matroid α) : M.eRank <= M.E.encard :=
M.eRank_def.trans_le M.eRk_le_encard M.E

/--
lemma `eRk_mono` / 引理 `eRk_mono`

English:
lemma eRk_mono
  given: (M : Matroid α)
  statement: Monotone M.eRk
  proof: by
  rintro X Y (hXY : X subseteq Y)
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard]; rw [hJ.eRk_eq_encard]
  exact encard_mono hIJ

中文:
引理 eRk_mono
  条件: (M : 拟阵 α)
  结论: 递增 M.eRk
  证明: by
  rintro X Y (hXY : X subseteq Y)
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard]; rw [hJ.eRk_eq_encard]
  exact encard_mono hIJ

Depends on / 依赖: M.exists_isBasis, _of_subset, eRk_eq_encard, encard_mono, exists_isBasis, hI.eRk_eq_encard, hI.indep.subset_isBasis, hI.subset.trans, hJ.eRk_eq_encard, subset, subset_isBasis, subseteq
-/
lemma eRk_mono (M : Matroid α) : Monotone M.eRk := by
  rintro X Y (hXY : X subseteq Y)
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard]; rw [hJ.eRk_eq_encard]
  exact encard_mono hIJ

/--
lemma `eRk_le_eRank` / 引理 `eRk_le_eRank`

English:
lemma eRk_le_eRank
  given: (M : Matroid α) (X : Set α)
  statement: M.eRk X <= M.eRank
  proof: by
  rw [eRank_def]; rw [← eRk_inter_ground]; exact M.eRk_mono inter_subset_right

中文:
引理 eRk_le_eRank
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: M.eRk X <= M.eRank
  证明: by
  rw [eRank_def]; rw [← eRk_inter_ground]; exact M.eRk_mono inter_subset_right

Depends on / 依赖: M.eRk_mono, eRank_def, eRk_inter_ground, eRk_mono, inter_subset_right
-/
lemma eRk_le_eRank (M : Matroid α) (X : Set α) : M.eRk X <= M.eRank := by
  rw [eRank_def]; rw [← eRk_inter_ground]; exact M.eRk_mono inter_subset_right

/--
lemma `eRk_eq_eRk_of_subset_of_le` / 引理 `eRk_eq_eRk_of_subset_of_le`

English:
lemma eRk_eq_eRk_of_subset_of_le
  given: (hXY : X subseteq Y) (hYX : M.eRk Y <= M.eRk X)
  statement: M.eRk X = M.eRk Y
  proof: (M.eRk_mono hXY).antisymm hYX

中文:
引理 eRk_eq_eRk_of_subset_of_le
  条件: (hXY : X subseteq Y) (hYX : M.eRk Y <= M.eRk X)
  结论: M.eRk X = M.eRk Y
  证明: (M.eRk_mono hXY).antisymm hYX

Depends on / 依赖: M.eRk_mono, antisymm, eRk_mono
-/
lemma eRk_eq_eRk_of_subset_of_le (hXY : X subseteq Y) (hYX : M.eRk Y <= M.eRk X) : M.eRk X = M.eRk Y :=
  (M.eRk_mono hXY).antisymm hYX

/--
lemma `le_eRk_iff` / 引理 `le_eRk_iff`

English:
lemma le_eRk_iff
  statement: n <= M.eRk X ↔ exists I, I subseteq X ∧ M.Indep I ∧ I.encard = n
  proof: by
  refine ⟨fun h => ?_, fun ⟨I, hIX, hI, hIc⟩ => ?_⟩
  · obtain ⟨J, hJ⟩ := M.exists_isBasis' X
    rw [← hJ.encard_eq_eRk] at h
    obtain ⟨I, hIJ, rfl⟩ := exists_subset_encard_eq h
    exact ⟨_, hIJ.trans hJ.subset, hJ.indep.subset hIJ, rfl⟩
  rw [← hIc]; rw [← hI.eRk_eq_encard]
  exact M.eRk_mon

中文:
引理 le_eRk_iff
  结论: n <= M.eRk X ↔ 存在 I, I subseteq X ∧ M.Indep I ∧ I.encard = n
  证明: by
  refine ⟨fun h => ?_, fun ⟨I, hIX, hI, hIc⟩ => ?_⟩
  · obtain ⟨J, hJ⟩ := M.exists_isBasis' X
    rw [← hJ.encard_eq_eRk] at h
    obtain ⟨I, hIJ, rfl⟩ := exists_subset_encard_eq h
    exact ⟨_, hIJ.trans hJ.subset, hJ.indep.subset hIJ, rfl⟩
  rw [← hIc]; rw [← hI.eRk_eq_encard]
  exact M.eRk_mon

Depends on / 依赖: M.eRk_mono, M.exists_isBasis, eRk_eq_encard, eRk_mono, encard_eq_eRk, exists_isBasis, exists_subset_encard_eq, hI.eRk_eq_encard, hIJ.trans, hJ.encard_eq_eRk, hJ.indep.subset, hJ.subset, subset
-/
lemma le_eRk_iff : n <= M.eRk X ↔ exists I, I subseteq X ∧ M.Indep I ∧ I.encard = n := by
  refine ⟨fun h => ?_, fun ⟨I, hIX, hI, hIc⟩ => ?_⟩
  · obtain ⟨J, hJ⟩ := M.exists_isBasis' X
    rw [← hJ.encard_eq_eRk] at h
    obtain ⟨I, hIJ, rfl⟩ := exists_subset_encard_eq h
    exact ⟨_, hIJ.trans hJ.subset, hJ.indep.subset hIJ, rfl⟩
  rw [← hIc]; rw [← hI.eRk_eq_encard]
  exact M.eRk_mono hIX

/--
lemma `eRk_le_iff` / 引理 `eRk_le_iff`

English:
lemma eRk_le_iff
  statement: M.eRk X <= n ↔ forall ⦃I⦄, I subseteq X -> M.Indep I -> I.encard <= n
  proof: by
  refine ⟨fun h I hIX hI => (hI.eRk_eq_encard.symm.trans_le ((M.eRk_mono hIX).trans h)), fun h => ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.encard_eq_eRk]
  exact h hI.subset hI.indep

中文:
引理 eRk_le_iff
  结论: M.eRk X <= n ↔ 对任意 ⦃I⦄, I subseteq X -> M.Indep I -> I.encard <= n
  证明: by
  refine ⟨fun h I hIX hI => (hI.eRk_eq_encard.symm.trans_le ((M.eRk_mono hIX).trans h)), fun h => ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.encard_eq_eRk]
  exact h hI.subset hI.indep

Depends on / 依赖: M.eRk_mono, M.exists_isBasis, eRk_eq_encard, eRk_mono, encard_eq_eRk, exists_isBasis, hI.eRk_eq_encard.symm.trans_le, hI.encard_eq_eRk, hI.indep, hI.subset, subset, trans_le
-/
lemma eRk_le_iff : M.eRk X <= n ↔ forall ⦃I⦄, I subseteq X -> M.Indep I -> I.encard <= n := by
  refine ⟨fun h I hIX hI => (hI.eRk_eq_encard.symm.trans_le ((M.eRk_mono hIX).trans h)), fun h => ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.encard_eq_eRk]
  exact h hI.subset hI.indep

/--
lemma `Indep.encard_le_eRk_of_subset` / 引理 `Indep.encard_le_eRk_of_subset`

English:
lemma Indep.encard_le_eRk_of_subset
  given: (hI : M.Indep I) (hIX : I subseteq X)
  statement: I.encard <= M.eRk X
  proof: hI.eRk_eq_encard ▸ M.eRk_mono hIX

中文:
引理 Indep.encard_le_eRk_of_subset
  条件: (hI : M.Indep I) (hIX : I subseteq X)
  结论: I.encard <= M.eRk X
  证明: hI.eRk_eq_encard ▸ M.eRk_mono hIX

Depends on / 依赖: M.eRk_mono, eRk_eq_encard, eRk_mono, hI.eRk_eq_encard
-/
lemma Indep.encard_le_eRk_of_subset (hI : M.Indep I) (hIX : I subseteq X) : I.encard <= M.eRk X :=
  hI.eRk_eq_encard ▸ M.eRk_mono hIX

/--
lemma `Indep.encard_le_eRank` / 引理 `Indep.encard_le_eRank`

English:
lemma Indep.encard_le_eRank
  given: (hI : M.Indep I)
  statement: I.encard <= M.eRank
  proof: by
  rw [← hI.eRk_eq_encard]; rw [eRank_def]
  exact M.eRk_mono hI.subset_ground

中文:
引理 Indep.encard_le_eRank
  条件: (hI : M.Indep I)
  结论: I.encard <= M.eRank
  证明: by
  rw [← hI.eRk_eq_encard]; rw [eRank_def]
  exact M.eRk_mono hI.subset_ground

Depends on / 依赖: M.eRk_mono, eRank_def, eRk_eq_encard, eRk_mono, hI.eRk_eq_encard, hI.subset_ground, subset_ground
-/
lemma Indep.encard_le_eRank (hI : M.Indep I) : I.encard <= M.eRank := by
  rw [← hI.eRk_eq_encard]; rw [eRank_def]
  exact M.eRk_mono hI.subset_ground

/--
lemma `eRk_eq_zero_iff'` / 引理 `eRk_eq_zero_iff'`

English:
lemma eRk_eq_zero_iff'
  statement: M.eRk X = 0 ↔ X inter M.E subseteq M.loops
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis (X inter M.E)
  rw [← eRk_inter_ground]; rw [← hI.encard_eq_eRk]; rw [encard_eq_zero]
  refine ⟨fun h => by simpa [h] using! hI, fun h => eq_empty_iff_forall_notMem.2 fun e heI => ?_⟩
  exact (hI.indep.isNonloop_of_mem heI).not_isLoop (h (hI.subset heI))

@[si

中文:
引理 eRk_eq_zero_iff'
  结论: M.eRk X = 0 ↔ X inter M.E subseteq M.loops
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis (X inter M.E)
  rw [← eRk_inter_ground]; rw [← hI.encard_eq_eRk]; rw [encard_eq_zero]
  refine ⟨fun h => by simpa [h] using! hI, fun h => eq_empty_iff_forall_notMem.2 fun e heI => ?_⟩
  exact (hI.indep.isNonloop_of_mem heI).not_isLoop (h (hI.subset heI))

@[si

Depends on / 依赖: M.exists_isBasis, eRk_inter_ground, encard_eq_eRk, encard_eq_zero, eq_empty_iff_forall_notMem, exists_isBasis, hI.encard_eq_eRk, hI.indep.isNonloop_of_mem, hI.subset, isNonloop_of_mem, not_isLoop, subset
-/
lemma eRk_eq_zero_iff' : M.eRk X = 0 ↔ X inter M.E subseteq M.loops := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (X inter M.E)
  rw [← eRk_inter_ground]; rw [← hI.encard_eq_eRk]; rw [encard_eq_zero]
  refine ⟨fun h => by simpa [h] using! hI, fun h => eq_empty_iff_forall_notMem.2 fun e heI => ?_⟩
  exact (hI.indep.isNonloop_of_mem heI).not_isLoop (h (hI.subset heI))

@[simp]
/--
lemma `eRk_eq_zero_iff` / 引理 `eRk_eq_zero_iff`

English:
lemma eRk_eq_zero_iff
  given: (hX : X subseteq M.E := by aesop_mat)
  statement: M.eRk X = 0 ↔ X subseteq M.loops
  proof: by
  rw [eRk_eq_zero_iff']; rw [inter_eq_self_of_subset_left hX]

@[simp]

中文:
引理 eRk_eq_zero_iff
  条件: (hX : X subseteq M.E := by aesop_mat)
  结论: M.eRk X = 0 ↔ X subseteq M.loops
  证明: by
  rw [eRk_eq_zero_iff']; rw [inter_eq_self_of_subset_left hX]

@[simp]

Depends on / 依赖: M.eRk, M.loops, aesop_mat, eRk_eq_zero_iff, inter_eq_self_of_subset_left, subseteq
-/
lemma eRk_eq_zero_iff (hX : X subseteq M.E := by aesop_mat) : M.eRk X = 0 ↔ X subseteq M.loops := by
  rw [eRk_eq_zero_iff']; rw [inter_eq_self_of_subset_left hX]

@[simp]
/--
lemma `eRk_loops` / 引理 `eRk_loops`

English:
lemma eRk_loops
  statement: M.eRk M.loops = 0
  proof: by
  simp [eRk_eq_zero_iff']

中文:
引理 eRk_loops
  结论: M.eRk M.loops = 0
  证明: by
  simp [eRk_eq_zero_iff']

Depends on / 依赖: eRk_eq_zero_iff
-/
lemma eRk_loops : M.eRk M.loops = 0 := by
  simp [eRk_eq_zero_iff']

/-! ### Submodularity -/

/--
lemma `eRk_inter_add_eRk_union_le` / 引理 `eRk_inter_add_eRk_union_le`

English:
lemma eRk_inter_add_eRk_union_le
  given: (M : Matroid α) (X Y : Set α)
  proof: by
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis' (X inter Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_right)
  rw [← hIX.eRk_eq_eRk_union]; rw 

中文:
引理 eRk_inter_add_eRk_union_le
  条件: (M : 拟阵 α) (X Y : 集合 α)
  证明: by
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis' (X inter Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_right)
  rw [← hIX.eRk_eq_eRk_union]; rw 

Depends on / 依赖: M.exists_isBasis, _of_subset, add_comm, add_le_add, eRk_eq_eRk_union, eRk_le_e, encard_eq_eRk, encard_union_add_encard_inter, exists_isBasis, hIX.eRk_eq_eRk_union, hIX.encard_eq_eRk, hIY.eRk_eq_eRk_union, hIY.encard_eq_eRk, hIi.encard_eq_eRk, hIi.indep.subset_isBasis, hIi.subset.trans, inter_subset_left, inter_subset_right, subset, subset_isBasis
-/
lemma eRk_inter_add_eRk_union_le (M : Matroid α) (X Y : Set α) :
    M.eRk (X inter Y) + M.eRk (X union Y) <= M.eRk X + M.eRk Y := by
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis' (X inter Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_right)
  rw [← hIX.eRk_eq_eRk_union]; rw [union_comm]; rw [← hIY.eRk_eq_eRk_union]; rw [← hIi.encard_eq_eRk]; rw [← hIX.encard_eq_eRk]; rw [← hIY.encard_eq_eRk]; rw [union_comm]; rw [← encard_union_add_encard_inter]; rw [add_comm]
  exact add_le_add (eRk_le_encard _ _) (encard_mono (subset_inter hIX' hIY'))

alias eRk_submod := eRk_inter_add_eRk_union_le

/--
lemma `eRk_insert_inter_add_eRk_insert_union_le` / 引理 `eRk_insert_inter_add_eRk_insert_union_le`

English:
lemma eRk_insert_inter_add_eRk_insert_union_le
  given: (M : Matroid α) (X Y : Set α)
  proof: by
  rw [insert_inter_distrib]; rw [insert_union_distrib]
  apply M.eRk_submod

中文:
引理 eRk_insert_inter_add_eRk_insert_union_le
  条件: (M : 拟阵 α) (X Y : 集合 α)
  证明: by
  rw [insert_inter_distrib]; rw [insert_union_distrib]
  apply M.eRk_submod

Depends on / 依赖: M.eRk_submod, eRk_submod, insert_inter_distrib, insert_union_distrib
-/
lemma eRk_insert_inter_add_eRk_insert_union_le (M : Matroid α) (X Y : Set α) :
    M.eRk (insert e (X inter Y)) + M.eRk (insert e (X union Y))
      <= M.eRk (insert e X) + M.eRk (insert e Y) := by
  rw [insert_inter_distrib]; rw [insert_union_distrib]
  apply M.eRk_submod

/--
lemma `eRk_compl_union_add_eRk_compl_inter_le` / 引理 `eRk_compl_union_add_eRk_compl_inter_le`

English:
lemma eRk_compl_union_add_eRk_compl_inter_le
  given: (M : Matroid α) (X Y : Set α)
  proof: by
  rw [← sdiff_inter_sdiff]; rw [sdiff_inter]
  apply M.eRk_submod

中文:
引理 eRk_compl_union_add_eRk_compl_inter_le
  条件: (M : 拟阵 α) (X Y : 集合 α)
  证明: by
  rw [← sdiff_inter_sdiff]; rw [sdiff_inter]
  apply M.eRk_submod

Depends on / 依赖: M.eRk_submod, eRk_submod, sdiff_inter, sdiff_inter_sdiff
-/
lemma eRk_compl_union_add_eRk_compl_inter_le (M : Matroid α) (X Y : Set α) :
    M.eRk (M.E \ (X union Y)) + M.eRk (M.E \ (X inter Y)) <= M.eRk (M.E \ X) + M.eRk (M.E \ Y) := by
  rw [← sdiff_inter_sdiff]; rw [sdiff_inter]
  apply M.eRk_submod

/--
lemma `eRk_compl_insert_union_add_eRk_compl_insert_inter_le` / 引理 `eRk_compl_insert_union_add_eRk_compl_insert_inter_le`

English:
lemma eRk_compl_insert_union_add_eRk_compl_insert_inter_le
  given: (M : Matroid α) (X Y : Set α)
  proof: by
  rw [insert_union_distrib]; rw [insert_inter_distrib]
  exact M.eRk_compl_union_add_eRk_compl_inter_le (insert e X) (insert e Y)

中文:
引理 eRk_compl_insert_union_add_eRk_compl_insert_inter_le
  条件: (M : 拟阵 α) (X Y : 集合 α)
  证明: by
  rw [insert_union_distrib]; rw [insert_inter_distrib]
  exact M.eRk_compl_union_add_eRk_compl_inter_le (insert e X) (insert e Y)

Depends on / 依赖: M.eRk_compl_union_add_eRk_compl_inter_le, eRk_compl_union_add_eRk_compl_inter_le, insert, insert_inter_distrib, insert_union_distrib
-/
lemma eRk_compl_insert_union_add_eRk_compl_insert_inter_le (M : Matroid α) (X Y : Set α) :
    M.eRk (M.E \ insert e (X union Y)) + M.eRk (M.E \ insert e (X inter Y)) <=
      M.eRk (M.E \ insert e X) + M.eRk (M.E \ insert e Y) := by
  rw [insert_union_distrib]; rw [insert_inter_distrib]
  exact M.eRk_compl_union_add_eRk_compl_inter_le (insert e X) (insert e Y)

/--
lemma `eRk_union_le_eRk_add_eRk` / 引理 `eRk_union_le_eRk_add_eRk`

English:
lemma eRk_union_le_eRk_add_eRk
  given: (M : Matroid α) (X Y : Set α)
  statement: M.eRk (X union Y) <= M.eRk X + M.eRk Y
  proof: le_add_self.trans (M.eRk_submod X Y)

中文:
引理 eRk_union_le_eRk_add_eRk
  条件: (M : 拟阵 α) (X Y : 集合 α)
  结论: M.eRk (X union Y) <= M.eRk X + M.eRk Y
  证明: le_add_self.trans (M.eRk_submod X Y)

Depends on / 依赖: M.eRk_submod, eRk_submod, le_add_self, le_add_self.trans
-/
lemma eRk_union_le_eRk_add_eRk (M : Matroid α) (X Y : Set α) : M.eRk (X union Y) <= M.eRk X + M.eRk Y :=
  le_add_self.trans (M.eRk_submod X Y)

/--
lemma `eRk_eq_eRk_union_eRk_le_zero` / 引理 `eRk_eq_eRk_union_eRk_le_zero`

English:
lemma eRk_eq_eRk_union_eRk_le_zero
  given: (X : Set α) (hY : M.eRk Y <= 0)
  statement: M.eRk (X union Y) = M.eRk X
  proof: (((M.eRk_union_le_eRk_add_eRk X Y).trans (by gcongr)).trans_eq (add_zero _)).antisymm
    (M.eRk_mono subset_union_left)

中文:
引理 eRk_eq_eRk_union_eRk_le_zero
  条件: (X : 集合 α) (hY : M.eRk Y <= 0)
  结论: M.eRk (X union Y) = M.eRk X
  证明: (((M.eRk_union_le_eRk_add_eRk X Y).trans (by gcongr)).trans_eq (add_zero _)).antisymm
    (M.eRk_mono subset_union_left)

Depends on / 依赖: M.eRk_mono, M.eRk_union_le_eRk_add_eRk, add_zero, antisymm, eRk_mono, eRk_union_le_eRk_add_eRk, subset_union_left, trans_eq
-/
lemma eRk_eq_eRk_union_eRk_le_zero (X : Set α) (hY : M.eRk Y <= 0) : M.eRk (X union Y) = M.eRk X :=
  (((M.eRk_union_le_eRk_add_eRk X Y).trans (by gcongr)).trans_eq (add_zero _)).antisymm
    (M.eRk_mono subset_union_left)

/--
lemma `eRk_eq_eRk_sdiff_eRk_le_zero` / 引理 `eRk_eq_eRk_sdiff_eRk_le_zero`

English:
lemma eRk_eq_eRk_sdiff_eRk_le_zero
  given: (X : Set α) (hY : M.eRk Y <= 0)
  statement: M.eRk (X \ Y) = M.eRk X
  proof: by
  rw [← eRk_eq_eRk_union_eRk_le_zero (X \ Y) hY]; rw [sdiff_union_self]; rw [eRk_eq_eRk_union_eRk_le_zero _ hY]

@[deprecated (since := "2026-06-03")]
alias eRk_eq_eRk_diff_eRk_le_zero := eRk_eq_eRk_sdiff_eRk_le_zero

中文:
引理 eRk_eq_eRk_sdiff_eRk_le_zero
  条件: (X : 集合 α) (hY : M.eRk Y <= 0)
  结论: M.eRk (X \ Y) = M.eRk X
  证明: by
  rw [← eRk_eq_eRk_union_eRk_le_zero (X \ Y) hY]; rw [sdiff_union_self]; rw [eRk_eq_eRk_union_eRk_le_zero _ hY]

@[deprecated (since := "2026-06-03")]
alias eRk_eq_eRk_diff_eRk_le_zero := eRk_eq_eRk_sdiff_eRk_le_zero

Depends on / 依赖: eRk_eq_eRk_union_eRk_le_zero, sdiff_union_self
-/
lemma eRk_eq_eRk_sdiff_eRk_le_zero (X : Set α) (hY : M.eRk Y <= 0) : M.eRk (X \ Y) = M.eRk X := by
  rw [← eRk_eq_eRk_union_eRk_le_zero (X \ Y) hY]; rw [sdiff_union_self]; rw [eRk_eq_eRk_union_eRk_le_zero _ hY]

@[deprecated (since := "2026-06-03")]
alias eRk_eq_eRk_diff_eRk_le_zero := eRk_eq_eRk_sdiff_eRk_le_zero

/--
lemma `eRk_le_eRk_inter_add_eRk_sdiff` / 引理 `eRk_le_eRk_inter_add_eRk_sdiff`

English:
lemma eRk_le_eRk_inter_add_eRk_sdiff
  given: (M : Matroid α) (X Y : Set α)
  proof: by
  nth_rw 1 [← inter_union_sdiff X Y]; apply eRk_union_le_eRk_add_eRk

@[deprecated (since := "2026-06-03")]
alias eRk_le_eRk_inter_add_eRk_diff := eRk_le_eRk_inter_add_eRk_sdiff

中文:
引理 eRk_le_eRk_inter_add_eRk_sdiff
  条件: (M : 拟阵 α) (X Y : 集合 α)
  证明: by
  nth_rw 1 [← inter_union_sdiff X Y]; apply eRk_union_le_eRk_add_eRk

@[deprecated (since := "2026-06-03")]
alias eRk_le_eRk_inter_add_eRk_diff := eRk_le_eRk_inter_add_eRk_sdiff

Depends on / 依赖: eRk_union_le_eRk_add_eRk, inter_union_sdiff, nth_rw
-/
lemma eRk_le_eRk_inter_add_eRk_sdiff (M : Matroid α) (X Y : Set α) :
    M.eRk X <= M.eRk (X inter Y) + M.eRk (X \ Y) := by
  nth_rw 1 [← inter_union_sdiff X Y]; apply eRk_union_le_eRk_add_eRk

@[deprecated (since := "2026-06-03")]
alias eRk_le_eRk_inter_add_eRk_diff := eRk_le_eRk_inter_add_eRk_sdiff

/--
lemma `eRk_le_eRk_add_eRk_sdiff` / 引理 `eRk_le_eRk_add_eRk_sdiff`

English:
lemma eRk_le_eRk_add_eRk_sdiff
  given: (M : Matroid α) (h : Y subseteq X)
  proof: by
  nth_rw 1 [← union_sdiff_cancel h]; apply eRk_union_le_eRk_add_eRk

@[deprecated (since := "2026-06-03")] alias eRk_le_eRk_add_eRk_diff := eRk_le_eRk_add_eRk_sdiff

中文:
引理 eRk_le_eRk_add_eRk_sdiff
  条件: (M : 拟阵 α) (h : Y subseteq X)
  证明: by
  nth_rw 1 [← union_sdiff_cancel h]; apply eRk_union_le_eRk_add_eRk

@[deprecated (since := "2026-06-03")] alias eRk_le_eRk_add_eRk_diff := eRk_le_eRk_add_eRk_sdiff

Depends on / 依赖: eRk_union_le_eRk_add_eRk, nth_rw, union_sdiff_cancel
-/
lemma eRk_le_eRk_add_eRk_sdiff (M : Matroid α) (h : Y subseteq X) :
    M.eRk X <= M.eRk Y + M.eRk (X \ Y) := by
  nth_rw 1 [← union_sdiff_cancel h]; apply eRk_union_le_eRk_add_eRk

@[deprecated (since := "2026-06-03")] alias eRk_le_eRk_add_eRk_diff := eRk_le_eRk_add_eRk_sdiff

/--
lemma `eRk_union_le_encard_add_eRk` / 引理 `eRk_union_le_encard_add_eRk`

English:
lemma eRk_union_le_encard_add_eRk
  given: (M : Matroid α) (X Y : Set α)
  proof: (M.eRk_union_le_eRk_add_eRk X Y).trans by grw [M.eRk_le_encard]

中文:
引理 eRk_union_le_encard_add_eRk
  条件: (M : 拟阵 α) (X Y : 集合 α)
  证明: (M.eRk_union_le_eRk_add_eRk X Y).trans by grw [M.eRk_le_encard]

Depends on / 依赖: M.eRk_le_encard, M.eRk_union_le_eRk_add_eRk, eRk_le_encard, eRk_union_le_eRk_add_eRk
-/
lemma eRk_union_le_encard_add_eRk (M : Matroid α) (X Y : Set α) :
    M.eRk (X union Y) <= X.encard + M.eRk Y :=
(M.eRk_union_le_eRk_add_eRk X Y).trans by grw [M.eRk_le_encard]

/--
lemma `eRk_union_le_eRk_add_encard` / 引理 `eRk_union_le_eRk_add_encard`

English:
lemma eRk_union_le_eRk_add_encard
  given: (M : Matroid α) (X Y : Set α)
  proof: (M.eRk_union_le_eRk_add_eRk X Y).trans by grw [← M.eRk_le_encard]

中文:
引理 eRk_union_le_eRk_add_encard
  条件: (M : 拟阵 α) (X Y : 集合 α)
  证明: (M.eRk_union_le_eRk_add_eRk X Y).trans by grw [← M.eRk_le_encard]

Depends on / 依赖: M.eRk_le_encard, M.eRk_union_le_eRk_add_eRk, eRk_le_encard, eRk_union_le_eRk_add_eRk
-/
lemma eRk_union_le_eRk_add_encard (M : Matroid α) (X Y : Set α) :
    M.eRk (X union Y) <= M.eRk X + Y.encard :=
(M.eRk_union_le_eRk_add_eRk X Y).trans by grw [← M.eRk_le_encard]

/--
lemma `eRank_le_encard_add_eRk_compl` / 引理 `eRank_le_encard_add_eRk_compl`

English:
lemma eRank_le_encard_add_eRk_compl
  given: (M : Matroid α) (X : Set α)
  proof: le_trans (by rw [← eRk_inter_ground, eRank_def, union_sdiff_self,
    union_inter_cancel_right]) (M.eRk_union_le_encard_add_eRk X (M.E \ X))

中文:
引理 eRank_le_encard_add_eRk_compl
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: le_trans (by rw [← eRk_inter_ground, eRank_def, union_sdiff_self,
    union_inter_cancel_right]) (M.eRk_union_le_encard_add_eRk X (M.E \ X))

Depends on / 依赖: M.eRk_union_le_encard_add_eRk, eRank_def, eRk_inter_ground, eRk_union_le_encard_add_eRk, le_trans, union_inter_cancel_right, union_sdiff_self
-/
lemma eRank_le_encard_add_eRk_compl (M : Matroid α) (X : Set α) :
    M.eRank <= X.encard + M.eRk (M.E \ X) :=
  le_trans (by rw [← eRk_inter_ground, eRank_def, union_sdiff_self,
    union_inter_cancel_right]) (M.eRk_union_le_encard_add_eRk X (M.E \ X))

end Basic


/--
lemma `eRank_ne_top_iff` / 引理 `eRank_ne_top_iff`

English:
lemma eRank_ne_top_iff
  given: (M : Matroid α)
  statement: M.eRank != ⊤ ↔ M.RankFinite
  proof: by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank]; rw [encard_ne_top_iff]
  exact ⟨fun h => hB.rankFinite_of_finite h, fun h => hB.finite⟩

@[simp]

中文:
引理 eRank_ne_top_iff
  条件: (M : 拟阵 α)
  结论: M.eRank != ⊤ ↔ M.RankFinite
  证明: by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank]; rw [encard_ne_top_iff]
  exact ⟨fun h => hB.rankFinite_of_finite h, fun h => hB.finite⟩

@[simp]

Depends on / 依赖: M.exists_isBase, encard_eq_eRank, encard_ne_top_iff, exists_isBase, finite, hB.encard_eq_eRank, hB.finite, hB.rankFinite_of_finite, rankFinite_of_finite
-/
lemma eRank_ne_top_iff (M : Matroid α) : M.eRank != ⊤ ↔ M.RankFinite := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank]; rw [encard_ne_top_iff]
  exact ⟨fun h => hB.rankFinite_of_finite h, fun h => hB.finite⟩

@[simp]
/--
lemma `eRank_eq_top_iff` / 引理 `eRank_eq_top_iff`

English:
lemma eRank_eq_top_iff
  given: (M : Matroid α)
  statement: M.eRank = ⊤ ↔ M.RankInfinite
  proof: by
  rw [← not_rankFinite_iff]; rw [← eRank_ne_top_iff]; rw [not_not]

@[simp]

中文:
引理 eRank_eq_top_iff
  条件: (M : 拟阵 α)
  结论: M.eRank = ⊤ ↔ M.RankInfinite
  证明: by
  rw [← not_rankFinite_iff]; rw [← eRank_ne_top_iff]; rw [not_not]

@[simp]

Depends on / 依赖: eRank_ne_top_iff, not_not, not_rankFinite_iff
-/
lemma eRank_eq_top_iff (M : Matroid α) : M.eRank = ⊤ ↔ M.RankInfinite := by
  rw [← not_rankFinite_iff]; rw [← eRank_ne_top_iff]; rw [not_not]

@[simp]
/--
lemma `eRank_lt_top_iff` / 引理 `eRank_lt_top_iff`

English:
lemma eRank_lt_top_iff
  statement: M.eRank < ⊤ ↔ M.RankFinite
  proof: by
  simp [lt_top_iff_ne_top]

@[simp]

中文:
引理 eRank_lt_top_iff
  结论: M.eRank < ⊤ ↔ M.RankFinite
  证明: by
  simp [lt_top_iff_ne_top]

@[simp]

Depends on / 依赖: lt_top_iff_ne_top
-/
lemma eRank_lt_top_iff : M.eRank < ⊤ ↔ M.RankFinite := by
  simp [lt_top_iff_ne_top]

@[simp]
/--
lemma `eRank_eq_top` / 引理 `eRank_eq_top`

English:
lemma eRank_eq_top
  given: [RankInfinite M]
  statement: M.eRank = ⊤
  proof: (eRank_eq_top_iff _).2 by assumption

@[simp]

中文:
引理 eRank_eq_top
  条件: [RankInfinite M]
  结论: M.eRank = ⊤
  证明: (eRank_eq_top_iff _).2 by assumption

@[simp]

Depends on / 依赖: eRank_eq_top_iff
-/
lemma eRank_eq_top [RankInfinite M] : M.eRank = ⊤ :=
(eRank_eq_top_iff _).2 by assumption

@[simp]
/--
lemma `eRk_eq_top_iff` / 引理 `eRk_eq_top_iff`

English:
lemma eRk_eq_top_iff
  statement: M.eRk X = ⊤ ↔ ¬ M.IsRkFinite X
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard]; rw [encard_eq_top_iff]; rw [← hI.finite_iff_isRkFinite]; rw [Set.Infinite]

中文:
引理 eRk_eq_top_iff
  结论: M.eRk X = ⊤ ↔ ¬ M.IsRkFinite X
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard]; rw [encard_eq_top_iff]; rw [← hI.finite_iff_isRkFinite]; rw [Set.Infinite]

Depends on / 依赖: Infinite, M.exists_isBasis, Set.Infinite, eRk_eq_encard, encard_eq_top_iff, exists_isBasis, finite_iff_isRkFinite, hI.eRk_eq_encard, hI.finite_iff_isRkFinite
-/
lemma eRk_eq_top_iff : M.eRk X = ⊤ ↔ ¬ M.IsRkFinite X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard]; rw [encard_eq_top_iff]; rw [← hI.finite_iff_isRkFinite]; rw [Set.Infinite]

/--
lemma `eRk_ne_top_iff` / 引理 `eRk_ne_top_iff`

English:
lemma eRk_ne_top_iff
  statement: M.eRk X != ⊤ ↔ M.IsRkFinite X
  proof: by
  simp

@[simp]

中文:
引理 eRk_ne_top_iff
  结论: M.eRk X != ⊤ ↔ M.IsRkFinite X
  证明: by
  simp

@[simp]
-/
lemma eRk_ne_top_iff : M.eRk X != ⊤ ↔ M.IsRkFinite X := by
  simp

@[simp]
/--
lemma `eRk_lt_top_iff` / 引理 `eRk_lt_top_iff`

English:
lemma eRk_lt_top_iff
  statement: M.eRk X < ⊤ ↔ M.IsRkFinite X
  proof: by
  rw [lt_top_iff_ne_top]; rw [eRk_ne_top_iff]

中文:
引理 eRk_lt_top_iff
  结论: M.eRk X < ⊤ ↔ M.IsRkFinite X
  证明: by
  rw [lt_top_iff_ne_top]; rw [eRk_ne_top_iff]

Depends on / 依赖: eRk_ne_top_iff, lt_top_iff_ne_top
-/
lemma eRk_lt_top_iff : M.eRk X < ⊤ ↔ M.IsRkFinite X := by
  rw [lt_top_iff_ne_top]; rw [eRk_ne_top_iff]

/--
lemma `IsRkFinite.eRk_lt_top` / 引理 `IsRkFinite.eRk_lt_top`

English:
lemma IsRkFinite.eRk_lt_top
  given: (h : M.IsRkFinite X)
  statement: M.eRk X < ⊤
  proof: eRk_lt_top_iff.2 h

中文:
引理 IsRkFinite.eRk_lt_top
  条件: (h : M.IsRkFinite X)
  结论: M.eRk X < ⊤
  证明: eRk_lt_top_iff.2 h

Depends on / 依赖: eRk_lt_top_iff
-/
lemma IsRkFinite.eRk_lt_top (h : M.IsRkFinite X) : M.eRk X < ⊤ :=
  eRk_lt_top_iff.2 h

/--
lemma `IsRkFinite.isBasis_of_subset_closure_of_subset_of_encard_le` / 引理 `IsRkFinite.isBasis_of_subset_closure_of_subset_of_encard_le`

English:
lemma IsRkFinite.isBasis_of_subset_closure_of_subset_of_encard_le
  statement: (hX : M.IsRkFinite X)
  proof: by
  obtain ⟨J, hJ⟩ := M.exists_isBasis (I inter M.E)
  have hIJ := hJ.subset.trans inter_subset_left
  rw [← closure_inter_ground] at hXI
replace hXI := hXI.trans M.closure_subset_closure_of_subset_closure hJ.subset_closure
  have hJX := hJ.indep.isBasis_of_subset_of_subset_closure (hIJ.trans hIX) 

中文:
引理 IsRkFinite.isBasis_of_subset_closure_of_subset_of_encard_le
  结论: (hX : M.IsRkFinite X)
  证明: by
  obtain ⟨J, hJ⟩ := M.exists_isBasis (I inter M.E)
  have hIJ := hJ.subset.trans inter_subset_left
  rw [← closure_inter_ground] at hXI
replace hXI := hXI.trans M.closure_subset_closure_of_subset_closure hJ.subset_closure
  have hJX := hJ.indep.isBasis_of_subset_of_subset_closure (hIJ.trans hIX) 

Depends on / 依赖: Finite, Finite.eq_of_subset_of_encard_le, M.closure_subset_closure_of_subset_closure, M.exists_isBasis, closure_inter_ground, closure_subset_closure_of_subset_closure, encard_eq_eRk, eq_of_subset_of_encard_le, exists_isBasis, finite_of_isBasis, hIJ.trans, hJ.indep.isBasis_of_subset_of_subset_closure, hJ.subset.trans, hJ.subset_closure, hJX.encard_eq_eRk, hX.finite_of_isBasis, hXI.trans, inter_subset_left, isBasis_of_subset_of_subset_closure, replace
-/
lemma IsRkFinite.isBasis_of_subset_closure_of_subset_of_encard_le (hX : M.IsRkFinite X)
    (hXI : X subseteq M.closure I) (hIX : I subseteq X) (hI : I.encard <= M.eRk X) : M.IsBasis I X := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis (I inter M.E)
  have hIJ := hJ.subset.trans inter_subset_left
  rw [← closure_inter_ground] at hXI
replace hXI := hXI.trans M.closure_subset_closure_of_subset_closure hJ.subset_closure
  have hJX := hJ.indep.isBasis_of_subset_of_subset_closure (hIJ.trans hIX) hXI
  rw [← hJX.encard_eq_eRk] at hI
  rwa [← Finite.eq_of_subset_of_encard_le (hX.finite_of_isBasis hJX) hIJ hI]

/--
lemma `IsRkFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk` / 引理 `IsRkFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk`

English:
lemma IsRkFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk
  statement: (hX : M.IsRkFinite X) (hXY : X subseteq Y)
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard]; rw [hJ.eRk_eq_encard] at hr
  rw [← closure_inter_ground]; rw [← M.closure_inter_ground Y]; rw [← hI.isBasis_inter_ground.closure_eq_closure]; rw [← h

中文:
引理 IsRkFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk
  结论: (hX : M.IsRkFinite X) (hXY : X subseteq Y)
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard]; rw [hJ.eRk_eq_encard] at hr
  rw [← closure_inter_ground]; rw [← M.closure_inter_ground Y]; rw [← hI.isBasis_inter_ground.closure_eq_closure]; rw [← h

Depends on / 依赖: Finite, Finite.eq_of_subset_of_encard_le, M.closure_inter_ground, M.exists_isBasis, _of_subset, closure_eq_closure, closure_inter_ground, eRk_eq_encard, eq_of_subset_of_encard_le, exists_isBasis, finite_of_subset_isRkFinite, hI.eRk_eq_encard, hI.indep.finite_of_subset_isRkFinite, hI.indep.subset_isBasis, hI.isBasis_inter_ground.closure_eq_closure, hI.subset, hI.subset.trans, hJ.eRk_eq_encard, hJ.isBasis_inter_ground.closure_eq_closure, isBasis_inter_ground
-/
lemma IsRkFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk (hX : M.IsRkFinite X) (hXY : X subseteq Y)
    (hr : M.eRk Y <= M.eRk X) : M.closure X = M.closure Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard]; rw [hJ.eRk_eq_encard] at hr
  rw [← closure_inter_ground]; rw [← M.closure_inter_ground Y]; rw [← hI.isBasis_inter_ground.closure_eq_closure]; rw [← hJ.isBasis_inter_ground.closure_eq_closure]; rw [Finite.eq_of_subset_of_encard_le
      (hI.indep.finite_of_subset_isRkFinite hI.subset hX) hIJ hr]


/--
lemma `eRk_insert_le_add_one` / 引理 `eRk_insert_le_add_one`

English:
lemma eRk_insert_le_add_one
  given: (M : Matroid α) (e : α) (X : Set α)
  proof: union_singleton ▸ (M.eRk_union_le_eRk_add_eRk _ _).trans by
    gcongr; simpa using M.eRk_le_encard {e}

中文:
引理 eRk_insert_le_add_one
  条件: (M : 拟阵 α) (e : α) (X : 集合 α)
  证明: union_singleton ▸ (M.eRk_union_le_eRk_add_eRk _ _).trans by
    gcongr; simpa using M.eRk_le_encard {e}

Depends on / 依赖: M.eRk_le_encard, M.eRk_union_le_eRk_add_eRk, eRk_le_encard, eRk_union_le_eRk_add_eRk, union_singleton
-/
lemma eRk_insert_le_add_one (M : Matroid α) (e : α) (X : Set α) :
    M.eRk (insert e X) <= M.eRk X + 1 :=
union_singleton ▸ (M.eRk_union_le_eRk_add_eRk _ _).trans by
    gcongr; simpa using M.eRk_le_encard {e}

/--
lemma `eRk_insert_eq_add_one` / 引理 `eRk_insert_eq_add_one`

English:
lemma eRk_insert_eq_add_one
  given: (he : e in M.E \ M.closure X)
  statement: M.eRk (insert e X) = M.eRk X + 1
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.closure_eq_closure]; rw [mem_sdiff]; rw [hI.indep.mem_closure_iff']; rw [not_and] at he
  rw [← eRk_closure_eq]; rw [← closure_insert_congr_right hI.closure_eq_closure]; rw [hI.eRk_eq_encard]; rw [eRk_closure_eq]; rw [Indep.eRk_eq_encard (by taut

中文:
引理 eRk_insert_eq_add_one
  条件: (he : e in M.E \ M.closure X)
  结论: M.eRk (insert e X) = M.eRk X + 1
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.closure_eq_closure]; rw [mem_sdiff]; rw [hI.indep.mem_closure_iff']; rw [not_and] at he
  rw [← eRk_closure_eq]; rw [← closure_insert_congr_right hI.closure_eq_closure]; rw [hI.eRk_eq_encard]; rw [eRk_closure_eq]; rw [Indep.eRk_eq_encard (by taut

Depends on / 依赖: Indep.eRk_eq_encard, M.exists_isBasis, closure_eq_closure, closure_insert_congr_right, eRk_closure_eq, eRk_eq_encard, encard_insert_of_notMem, exists_isBasis, hI.closure_eq_closure, hI.eRk_eq_encard, hI.indep.mem_closure_iff, mem_closure_iff, mem_sdiff, not_and
-/
lemma eRk_insert_eq_add_one (he : e in M.E \ M.closure X) : M.eRk (insert e X) = M.eRk X + 1 := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.closure_eq_closure]; rw [mem_sdiff]; rw [hI.indep.mem_closure_iff']; rw [not_and] at he
  rw [← eRk_closure_eq]; rw [← closure_insert_congr_right hI.closure_eq_closure]; rw [hI.eRk_eq_encard]; rw [eRk_closure_eq]; rw [Indep.eRk_eq_encard (by tauto)]; rw [encard_insert_of_notMem (by tauto)]

/--
lemma `exists_eRk_insert_eq_add_one_of_lt` / 引理 `exists_eRk_insert_eq_add_one_of_lt`

English:
lemma exists_eRk_insert_eq_add_one_of_lt
  given: (h : M.eRk X < M.eRk Y)
  proof: by
  have hz : ¬ Y inter M.E subseteq M.closure X := by
    contrapose! h
    simpa using M.eRk_mono h
  obtain ⟨e, ⟨heZ, heE⟩, heX⟩ := not_subset.1 hz
  refine ⟨e, ⟨heZ, fun heX' => heX (mem_closure_of_mem' _ heX')⟩, eRk_insert_eq_add_one ⟨heE, heX⟩⟩

中文:
引理 存在_eRk_insert_eq_add_one_of_lt
  条件: (h : M.eRk X < M.eRk Y)
  证明: by
  have hz : ¬ Y inter M.E subseteq M.closure X := by
    contrapose! h
    simpa using M.eRk_mono h
  obtain ⟨e, ⟨heZ, heE⟩, heX⟩ := not_subset.1 hz
  refine ⟨e, ⟨heZ, fun heX' => heX (mem_closure_of_mem' _ heX')⟩, eRk_insert_eq_add_one ⟨heE, heX⟩⟩

Depends on / 依赖: M.closure, M.eRk_mono, closure, contrapose, eRk_insert_eq_add_one, eRk_mono, mem_closure_of_mem, not_subset, subseteq
-/
lemma exists_eRk_insert_eq_add_one_of_lt (h : M.eRk X < M.eRk Y) :
    exists y in Y \ X, M.eRk (insert y X) = M.eRk X + 1 := by
  have hz : ¬ Y inter M.E subseteq M.closure X := by
    contrapose! h
    simpa using M.eRk_mono h
  obtain ⟨e, ⟨heZ, heE⟩, heX⟩ := not_subset.1 hz
  refine ⟨e, ⟨heZ, fun heX' => heX (mem_closure_of_mem' _ heX')⟩, eRk_insert_eq_add_one ⟨heE, heX⟩⟩

/--
lemma `IsRkFinite.closure_eq_closure_of_subset_of_forall_insert` / 引理 `IsRkFinite.closure_eq_closure_of_subset_of_forall_insert`

English:
lemma IsRkFinite.closure_eq_closure_of_subset_of_forall_insert
  statement: (hX : M.IsRkFinite X) (hXY : X subseteq Y)
  proof: by
refine hX.closure_eq_closure_of_subset_of_eRk_ge_eRk hXY not_lt.1 fun hlt => ?_
  obtain ⟨z, hz, hr⟩ := exists_eRk_insert_eq_add_one_of_lt hlt
  simpa [hr, ENat.add_one_le_iff hX.eRk_lt_top.ne] using hY z hz

中文:
引理 IsRkFinite.closure_eq_closure_of_subset_of_对任意_insert
  结论: (hX : M.IsRkFinite X) (hXY : X subseteq Y)
  证明: by
refine hX.closure_eq_closure_of_subset_of_eRk_ge_eRk hXY not_lt.1 fun hlt => ?_
  obtain ⟨z, hz, hr⟩ := exists_eRk_insert_eq_add_one_of_lt hlt
  simpa [hr, ENat.add_one_le_iff hX.eRk_lt_top.ne] using hY z hz

Depends on / 依赖: ENat.add_one_le_iff, add_one_le_iff, closure_eq_closure_of_subset_of_eRk_ge_eRk, eRk_lt_top, exists_eRk_insert_eq_add_one_of_lt, hX.closure_eq_closure_of_subset_of_eRk_ge_eRk, hX.eRk_lt_top.ne, not_lt
-/
lemma IsRkFinite.closure_eq_closure_of_subset_of_forall_insert (hX : M.IsRkFinite X) (hXY : X subseteq Y)
    (hY : forall e in Y \ X, M.eRk (Insert.insert e X) <= M.eRk X) : M.closure X = M.closure Y := by
refine hX.closure_eq_closure_of_subset_of_eRk_ge_eRk hXY not_lt.1 fun hlt => ?_
  obtain ⟨z, hz, hr⟩ := exists_eRk_insert_eq_add_one_of_lt hlt
  simpa [hr, ENat.add_one_le_iff hX.eRk_lt_top.ne] using hY z hz

/--
lemma `eRk_eq_of_eRk_insert_le_forall` / 引理 `eRk_eq_of_eRk_insert_le_forall`

English:
lemma eRk_eq_of_eRk_insert_le_forall
  statement: (hXY : X subseteq Y)
  proof: by
  by_cases hX : M.IsRkFinite X
  · rw [← eRk_closure_eq, hX.closure_eq_closure_of_subset_of_forall_insert hXY hY, eRk_closure_eq]
  rw [eRk_eq_top_iff.2 hX]; rw [eRk_eq_top_iff.2 (mt (fun h => h.subset hXY) hX)]

中文:
引理 eRk_eq_of_eRk_insert_le_对任意
  结论: (hXY : X subseteq Y)
  证明: by
  by_cases hX : M.IsRkFinite X
  · rw [← eRk_closure_eq, hX.closure_eq_closure_of_subset_of_forall_insert hXY hY, eRk_closure_eq]
  rw [eRk_eq_top_iff.2 hX]; rw [eRk_eq_top_iff.2 (mt (fun h => h.subset hXY) hX)]

Depends on / 依赖: IsRkFinite, M.IsRkFinite, closure_eq_closure_of_subset_of_forall_insert, eRk_closure_eq, eRk_eq_top_iff, h.subset, hX.closure_eq_closure_of_subset_of_forall_insert, subset
-/
lemma eRk_eq_of_eRk_insert_le_forall (hXY : X subseteq Y)
    (hY : forall e in Y \ X, M.eRk (insert e X) <= M.eRk X) : M.eRk X = M.eRk Y := by
  by_cases hX : M.IsRkFinite X
  · rw [← eRk_closure_eq, hX.closure_eq_closure_of_subset_of_forall_insert hXY hY, eRk_closure_eq]
  rw [eRk_eq_top_iff.2 hX]; rw [eRk_eq_top_iff.2 (mt (fun h => h.subset hXY) hX)]


/--
lemma `indep_iff_eRk_eq_encard_of_finite` / 引理 `indep_iff_eRk_eq_encard_of_finite`

English:
lemma indep_iff_eRk_eq_encard_of_finite
  given: (hI : I.Finite)
  statement: M.Indep I ↔ M.eRk I = I.encard
  proof: by
  refine ⟨fun h => by rw [h.eRk_eq_encard], fun h => ?_⟩
  obtain ⟨J, hJ⟩ := M.exists_isBasis' I
  rw [← hI.eq_of_subset_of_encard_le' hJ.subset]
  · exact hJ.indep
  rw [← h]; rw [← hJ.eRk_eq_encard]

中文:
引理 indep_iff_eRk_eq_encard_of_finite
  条件: (hI : I.有限)
  结论: M.Indep I ↔ M.eRk I = I.encard
  证明: by
  refine ⟨fun h => by rw [h.eRk_eq_encard], fun h => ?_⟩
  obtain ⟨J, hJ⟩ := M.exists_isBasis' I
  rw [← hI.eq_of_subset_of_encard_le' hJ.subset]
  · exact hJ.indep
  rw [← h]; rw [← hJ.eRk_eq_encard]

Depends on / 依赖: M.exists_isBasis, eRk_eq_encard, eq_of_subset_of_encard_le, exists_isBasis, h.eRk_eq_encard, hI.eq_of_subset_of_encard_le, hJ.eRk_eq_encard, hJ.indep, hJ.subset, subset
-/
lemma indep_iff_eRk_eq_encard_of_finite (hI : I.Finite) : M.Indep I ↔ M.eRk I = I.encard := by
  refine ⟨fun h => by rw [h.eRk_eq_encard], fun h => ?_⟩
  obtain ⟨J, hJ⟩ := M.exists_isBasis' I
  rw [← hI.eq_of_subset_of_encard_le' hJ.subset]
  · exact hJ.indep
  rw [← h]; rw [← hJ.eRk_eq_encard]

/--
lemma `indep_iff_eRk_eq_encard` / 引理 `indep_iff_eRk_eq_encard`

English:
lemma indep_iff_eRk_eq_encard
  given: [M.RankFinite]
  statement: M.Indep I ↔ M.eRk I = I.encard
  proof: by
  refine ⟨Indep.eRk_eq_encard, fun h => ?_⟩
  obtain hfin | hinf := I.finite_or_infinite
  · rwa [indep_iff_eRk_eq_encard_of_finite hfin]
  rw [hinf.encard_eq] at h
exact False.elim (M.isRkFinite_set I).eRk_lt_top.ne h

中文:
引理 indep_iff_eRk_eq_encard
  条件: [M.RankFinite]
  结论: M.Indep I ↔ M.eRk I = I.encard
  证明: by
  refine ⟨Indep.eRk_eq_encard, fun h => ?_⟩
  obtain hfin | hinf := I.finite_or_infinite
  · rwa [indep_iff_eRk_eq_encard_of_finite hfin]
  rw [hinf.encard_eq] at h
exact False.elim (M.isRkFinite_set I).eRk_lt_top.ne h

Depends on / 依赖: False.elim, I.finite_or_infinite, Indep.eRk_eq_encard, M.isRkFinite_set, eRk_eq_encard, eRk_lt_top, eRk_lt_top.ne, encard_eq, finite_or_infinite, hinf.encard_eq, indep_iff_eRk_eq_encard_of_finite, isRkFinite_set
-/
lemma indep_iff_eRk_eq_encard [M.RankFinite] : M.Indep I ↔ M.eRk I = I.encard := by
  refine ⟨Indep.eRk_eq_encard, fun h => ?_⟩
  obtain hfin | hinf := I.finite_or_infinite
  · rwa [indep_iff_eRk_eq_encard_of_finite hfin]
  rw [hinf.encard_eq] at h
exact False.elim (M.isRkFinite_set I).eRk_lt_top.ne h

/--
lemma `IsRkFinite.indep_of_encard_le_eRk` / 引理 `IsRkFinite.indep_of_encard_le_eRk`

English:
lemma IsRkFinite.indep_of_encard_le_eRk
  given: (hX : M.IsRkFinite I) (h : encard I <= M.eRk I)
  proof: by
  rw [indep_iff_eRk_eq_encard_of_finite _]
  · exact (M.eRk_le_encard I).antisymm h
  simpa using h.trans_lt hX.eRk_lt_top

中文:
引理 IsRkFinite.indep_of_encard_le_eRk
  条件: (hX : M.IsRkFinite I) (h : encard I <= M.eRk I)
  证明: by
  rw [indep_iff_eRk_eq_encard_of_finite _]
  · exact (M.eRk_le_encard I).antisymm h
  simpa using h.trans_lt hX.eRk_lt_top

Depends on / 依赖: M.eRk_le_encard, antisymm, eRk_le_encard, eRk_lt_top, h.trans_lt, hX.eRk_lt_top, indep_iff_eRk_eq_encard_of_finite, trans_lt
-/
lemma IsRkFinite.indep_of_encard_le_eRk (hX : M.IsRkFinite I) (h : encard I <= M.eRk I) :
    M.Indep I := by
  rw [indep_iff_eRk_eq_encard_of_finite _]
  · exact (M.eRk_le_encard I).antisymm h
  simpa using h.trans_lt hX.eRk_lt_top

/--
lemma `eRk_lt_encard_of_dep_of_finite` / 引理 `eRk_lt_encard_of_dep_of_finite`

English:
lemma eRk_lt_encard_of_dep_of_finite
  given: (h : X.Finite) (hX : M.Dep X)
  statement: M.eRk X < X.encard
  proof: lt_of_le_of_ne (M.eRk_le_encard X) fun h' =>
    ((indep_iff_eRk_eq_encard_of_finite h).mpr h').not_dep hX

中文:
引理 eRk_lt_encard_of_dep_of_finite
  条件: (h : X.有限) (hX : M.Dep X)
  结论: M.eRk X < X.encard
  证明: lt_of_le_of_ne (M.eRk_le_encard X) fun h' =>
    ((indep_iff_eRk_eq_encard_of_finite h).mpr h').not_dep hX

Depends on / 依赖: M.eRk_le_encard, eRk_le_encard, indep_iff_eRk_eq_encard_of_finite, lt_of_le_of_ne, not_dep
-/
lemma eRk_lt_encard_of_dep_of_finite (h : X.Finite) (hX : M.Dep X) : M.eRk X < X.encard :=
  lt_of_le_of_ne (M.eRk_le_encard X) fun h' =>
    ((indep_iff_eRk_eq_encard_of_finite h).mpr h').not_dep hX

/--
lemma `eRk_lt_encard_iff_dep_of_finite` / 引理 `eRk_lt_encard_iff_dep_of_finite`

English:
lemma eRk_lt_encard_iff_dep_of_finite
  given: (hX : X.Finite) (hXE : X subseteq M.E := by aesop_mat)
  proof: by
  refine ⟨fun h => ?_, fun h => eRk_lt_encard_of_dep_of_finite hX h⟩
  rw [← not_indep_iff]; rw [indep_iff_eRk_eq_encard_of_finite hX]
  exact h.ne

中文:
引理 eRk_lt_encard_iff_dep_of_finite
  条件: (hX : X.有限) (hXE : X subseteq M.E := by aesop_mat)
  证明: by
  refine ⟨fun h => ?_, fun h => eRk_lt_encard_of_dep_of_finite hX h⟩
  rw [← not_indep_iff]; rw [indep_iff_eRk_eq_encard_of_finite hX]
  exact h.ne

Depends on / 依赖: M.Dep, M.eRk, X.encard, aesop_mat, eRk_lt_encard_of_dep_of_finite, encard, h.ne, indep_iff_eRk_eq_encard_of_finite, not_indep_iff
-/
lemma eRk_lt_encard_iff_dep_of_finite (hX : X.Finite) (hXE : X subseteq M.E := by aesop_mat) :
    M.eRk X < X.encard ↔ M.Dep X := by
  refine ⟨fun h => ?_, fun h => eRk_lt_encard_of_dep_of_finite hX h⟩
  rw [← not_indep_iff]; rw [indep_iff_eRk_eq_encard_of_finite hX]
  exact h.ne

/--
lemma `Dep.eRk_lt_encard` / 引理 `Dep.eRk_lt_encard`

English:
lemma Dep.eRk_lt_encard
  given: [M.RankFinite] (hX : M.Dep X)
  statement: M.eRk X < X.encard
  proof: by
  refine (M.eRk_le_encard X).lt_of_ne ?_
  rw [ne_eq]; rw [← indep_iff_eRk_eq_encard]
  exact hX.not_indep

中文:
引理 Dep.eRk_lt_encard
  条件: [M.RankFinite] (hX : M.Dep X)
  结论: M.eRk X < X.encard
  证明: by
  refine (M.eRk_le_encard X).lt_of_ne ?_
  rw [ne_eq]; rw [← indep_iff_eRk_eq_encard]
  exact hX.not_indep

Depends on / 依赖: M.eRk_le_encard, eRk_le_encard, hX.not_indep, indep_iff_eRk_eq_encard, lt_of_ne, ne_eq, not_indep
-/
lemma Dep.eRk_lt_encard [M.RankFinite] (hX : M.Dep X) : M.eRk X < X.encard := by
  refine (M.eRk_le_encard X).lt_of_ne ?_
  rw [ne_eq]; rw [← indep_iff_eRk_eq_encard]
  exact hX.not_indep

/--
lemma `eRk_lt_encard_iff_dep` / 引理 `eRk_lt_encard_iff_dep`

English:
lemma eRk_lt_encard_iff_dep
  given: [M.RankFinite] (hXE : X subseteq M.E := by aesop_mat)
  proof: ⟨fun h => (not_indep_iff).1 fun hi => h.ne hi.eRk_eq_encard, Dep.eRk_lt_encard⟩

中文:
引理 eRk_lt_encard_iff_dep
  条件: [M.RankFinite] (hXE : X subseteq M.E := by aesop_mat)
  证明: ⟨fun h => (not_indep_iff).1 fun hi => h.ne hi.eRk_eq_encard, Dep.eRk_lt_encard⟩

Depends on / 依赖: Dep.eRk_lt_encard, M.Dep, M.eRk, X.encard, aesop_mat, eRk_eq_encard, eRk_lt_encard, encard, h.ne, hi.eRk_eq_encard, not_indep_iff
-/
lemma eRk_lt_encard_iff_dep [M.RankFinite] (hXE : X subseteq M.E := by aesop_mat) :
    M.eRk X < X.encard ↔ M.Dep X :=
  ⟨fun h => (not_indep_iff).1 fun hi => h.ne hi.eRk_eq_encard, Dep.eRk_lt_encard⟩

/--
lemma `Indep.exists_insert_of_encard_lt` / 引理 `Indep.exists_insert_of_encard_lt`

English:
lemma Indep.exists_insert_of_encard_lt
  statement: {I J : Set α} (hI : M.Indep I) (hJ : M.Indep J)
  proof: augment hI hJ hcard

中文:
引理 Indep.存在_insert_of_encard_lt
  结论: {I J : 集合 α} (hI : M.Indep I) (hJ : M.Indep J)
  证明: augment hI hJ hcard

Depends on / 依赖: augment
-/
lemma Indep.exists_insert_of_encard_lt {I J : Set α} (hI : M.Indep I) (hJ : M.Indep J)
    (hcard : I.encard < J.encard) : exists e in J \ I, M.Indep (insert e I) :=
  augment hI hJ hcard

/--
lemma `isBasis'_iff_indep_encard_eq_of_finite` / 引理 `isBasis'_iff_indep_encard_eq_of_finite`

English:
lemma isBasis'_iff_indep_encard_eq_of_finite
  given: (hIfin : I.Finite)
  proof: by
  refine ⟨fun h => ⟨h.subset,h.indep, h.eRk_eq_encard.symm⟩, fun ⟨hIX, hI, hcard⟩ => ?_⟩
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis'_of_subset hIX
  rwa [hIfin.eq_of_subset_of_encard_le hIJ (hJ.encard_eq_eRk.trans hcard.symm).le]

中文:
引理 isBasis'_iff_indep_encard_eq_of_finite
  条件: (hIfin : I.有限)
  证明: by
  refine ⟨fun h => ⟨h.subset,h.indep, h.eRk_eq_encard.symm⟩, fun ⟨hIX, hI, hcard⟩ => ?_⟩
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis'_of_subset hIX
  rwa [hIfin.eq_of_subset_of_encard_le hIJ (hJ.encard_eq_eRk.trans hcard.symm).le]
-/
lemma isBasis'_iff_indep_encard_eq_of_finite (hIfin : I.Finite) :
    M.IsBasis' I X ↔ I subseteq X ∧ M.Indep I ∧ I.encard = M.eRk X := by
  refine ⟨fun h => ⟨h.subset,h.indep, h.eRk_eq_encard.symm⟩, fun ⟨hIX, hI, hcard⟩ => ?_⟩
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis'_of_subset hIX
  rwa [hIfin.eq_of_subset_of_encard_le hIJ (hJ.encard_eq_eRk.trans hcard.symm).le]

/--
lemma `isBasis_iff_indep_encard_eq_of_finite` / 引理 `isBasis_iff_indep_encard_eq_of_finite`

English:
lemma isBasis_iff_indep_encard_eq_of_finite
  given: (hIfin : I.Finite) (hX : X subseteq M.E := by aesop_mat)
  proof: by
  rw [← isBasis'_iff_isBasis]; rw [isBasis'_iff_indep_encard_eq_of_finite hIfin]

中文:
引理 isBasis_iff_indep_encard_eq_of_finite
  条件: (hIfin : I.有限) (hX : X subseteq M.E := by aesop_mat)
  证明: by
  rw [← isBasis'_iff_isBasis]; rw [isBasis'_iff_indep_encard_eq_of_finite hIfin]

Depends on / 依赖: I.encard, IsBasis, M.Indep, M.IsBasis, M.eRk, _iff_indep_encard_eq_of_finite, _iff_isBasis, aesop_mat, encard, isBasis, subseteq
-/
lemma isBasis_iff_indep_encard_eq_of_finite (hIfin : I.Finite) (hX : X subseteq M.E := by aesop_mat) :
    M.IsBasis I X ↔ I subseteq X ∧ M.Indep I ∧ I.encard = M.eRk X := by
  rw [← isBasis'_iff_isBasis]; rw [isBasis'_iff_indep_encard_eq_of_finite hIfin]

/--
lemma `Indep.isBasis'_of_eRk_ge` / 引理 `Indep.isBasis'_of_eRk_ge`

English:
lemma Indep.isBasis'_of_eRk_ge
  statement: (hI : M.Indep I) (hIfin : I.Finite) (hIX : I subseteq X)
  proof: (isBasis'_iff_indep_encard_eq_of_finite hIfin).2
    ⟨hIX, hI, by rw [h.antisymm (M.eRk_mono hIX), hI.eRk_eq_encard]⟩

中文:
引理 Indep.isBasis'_of_eRk_ge
  结论: (hI : M.Indep I) (hIfin : I.有限) (hIX : I subseteq X)
  证明: (isBasis'_iff_indep_encard_eq_of_finite hIfin).2
    ⟨hIX, hI, by rw [h.antisymm (M.eRk_mono hIX), hI.eRk_eq_encard]⟩

Depends on / 依赖: M.eRk_mono, _iff_indep_encard_eq_of_finite, antisymm, eRk_eq_encard, eRk_mono, h.antisymm, hI.eRk_eq_encard, isBasis
-/
lemma Indep.isBasis'_of_eRk_ge (hI : M.Indep I) (hIfin : I.Finite) (hIX : I subseteq X)
    (h : M.eRk X <= M.eRk I) : M.IsBasis' I X :=
  (isBasis'_iff_indep_encard_eq_of_finite hIfin).2
    ⟨hIX, hI, by rw [h.antisymm (M.eRk_mono hIX), hI.eRk_eq_encard]⟩

/--
lemma `Indep.isBasis_of_eRk_ge` / 引理 `Indep.isBasis_of_eRk_ge`

English:
lemma Indep.isBasis_of_eRk_ge
  statement: (hI : M.Indep I) (hIfin : I.Finite) (hIX : I subseteq X)
  proof: (hI.isBasis'_of_eRk_ge hIfin hIX h).isBasis

中文:
引理 Indep.isBasis_of_eRk_ge
  结论: (hI : M.Indep I) (hIfin : I.有限) (hIX : I subseteq X)
  证明: (hI.isBasis'_of_eRk_ge hIfin hIX h).isBasis

Depends on / 依赖: IsBasis, M.IsBasis, _of_eRk_ge, aesop_mat, hI.isBasis, isBasis
-/
lemma Indep.isBasis_of_eRk_ge (hI : M.Indep I) (hIfin : I.Finite) (hIX : I subseteq X)
    (h : M.eRk X <= M.eRk I) (hX : X subseteq M.E := by aesop_mat) : M.IsBasis I X :=
  (hI.isBasis'_of_eRk_ge hIfin hIX h).isBasis

/--
lemma `Indep.isBase_of_eRk_ge` / 引理 `Indep.isBase_of_eRk_ge`

English:
lemma Indep.isBase_of_eRk_ge
  given: (hI : M.Indep I) (hIfin : I.Finite) (h : M.eRank <= M.eRk I)
  proof: by
  simpa using hI.isBasis_of_eRk_ge hIfin hI.subset_ground (M.eRk_ground.trans_le h)

中文:
引理 Indep.isBase_of_eRk_ge
  条件: (hI : M.Indep I) (hIfin : I.有限) (h : M.eRank <= M.eRk I)
  证明: by
  simpa using hI.isBasis_of_eRk_ge hIfin hI.subset_ground (M.eRk_ground.trans_le h)

Depends on / 依赖: M.eRk_ground.trans_le, eRk_ground, hI.isBasis_of_eRk_ge, hI.subset_ground, isBasis_of_eRk_ge, subset_ground, trans_le
-/
lemma Indep.isBase_of_eRk_ge (hI : M.Indep I) (hIfin : I.Finite) (h : M.eRank <= M.eRk I) :
    M.IsBase I := by
  simpa using hI.isBasis_of_eRk_ge hIfin hI.subset_ground (M.eRk_ground.trans_le h)

/--
lemma `IsCircuit.eRk_add_one_eq` / 引理 `IsCircuit.eRk_add_one_eq`

English:
lemma IsCircuit.eRk_add_one_eq
  given: {C : Set α} (hC : M.IsCircuit C)
  statement: M.eRk C + 1 = C.encard
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  obtain ⟨e, ⟨heC, heI⟩, rfl⟩ := hC.isBasis_iff_insert_eq.1 hI
  rw [hI.eRk_eq_encard]; rw [encard_insert_of_notMem heI]

中文:
引理 是Circuit.eRk_add_one_eq
  条件: {C : 集合 α} (hC : M.是Circuit C)
  结论: M.eRk C + 1 = C.encard
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  obtain ⟨e, ⟨heC, heI⟩, rfl⟩ := hC.isBasis_iff_insert_eq.1 hI
  rw [hI.eRk_eq_encard]; rw [encard_insert_of_notMem heI]

Depends on / 依赖: M.exists_isBasis, eRk_eq_encard, encard_insert_of_notMem, exists_isBasis, hC.isBasis_iff_insert_eq, hI.eRk_eq_encard, isBasis_iff_insert_eq
-/
lemma IsCircuit.eRk_add_one_eq {C : Set α} (hC : M.IsCircuit C) : M.eRk C + 1 = C.encard := by
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  obtain ⟨e, ⟨heC, heI⟩, rfl⟩ := hC.isBasis_iff_insert_eq.1 hI
  rw [hI.eRk_eq_encard]; rw [encard_insert_of_notMem heI]


/--
lemma `IsLoop.eRk_eq` / 引理 `IsLoop.eRk_eq`

English:
lemma IsLoop.eRk_eq
  given: (he : M.IsLoop e)
  statement: M.eRk {e} = 0
  proof: by
  rw [← eRk_closure_eq]; rw [he.closure]; rw [loops]; rw [eRk_closure_eq]; rw [eRk_empty]

中文:
引理 IsLoop.eRk_eq
  条件: (he : M.IsLoop e)
  结论: M.eRk {e} = 0
  证明: by
  rw [← eRk_closure_eq]; rw [he.closure]; rw [loops]; rw [eRk_closure_eq]; rw [eRk_empty]

Depends on / 依赖: closure, eRk_closure_eq, eRk_empty, he.closure
-/
lemma IsLoop.eRk_eq (he : M.IsLoop e) : M.eRk {e} = 0 := by
  rw [← eRk_closure_eq]; rw [he.closure]; rw [loops]; rw [eRk_closure_eq]; rw [eRk_empty]

/--
lemma `IsNonloop.eRk_eq` / 引理 `IsNonloop.eRk_eq`

English:
lemma IsNonloop.eRk_eq
  given: (he : M.IsNonloop e)
  statement: M.eRk {e} = 1
  proof: by
  rw [← he.indep.isBasis_self.encard_eq_eRk]; rw [encard_singleton]

中文:
引理 是Nonloop.eRk_eq
  条件: (he : M.是Nonloop e)
  结论: M.eRk {e} = 1
  证明: by
  rw [← he.indep.isBasis_self.encard_eq_eRk]; rw [encard_singleton]

Depends on / 依赖: encard_eq_eRk, encard_singleton, he.indep.isBasis_self.encard_eq_eRk, isBasis_self
-/
lemma IsNonloop.eRk_eq (he : M.IsNonloop e) : M.eRk {e} = 1 := by
  rw [← he.indep.isBasis_self.encard_eq_eRk]; rw [encard_singleton]

/--
lemma `eRk_singleton_eq` / 引理 `eRk_singleton_eq`

English:
lemma eRk_singleton_eq
  given: [Loopless M] (he : e in M.E := by aesop_mat)
  proof: (M.isNonloop_of_loopless he).eRk_eq

@[simp]

中文:
引理 eRk_singleton_eq
  条件: [无环 M] (he : e in M.E := by aesop_mat)
  证明: (M.isNonloop_of_loopless he).eRk_eq

@[simp]

Depends on / 依赖: M.eRk, M.isNonloop_of_loopless, aesop_mat, eRk_eq, isNonloop_of_loopless
-/
lemma eRk_singleton_eq [Loopless M] (he : e in M.E := by aesop_mat) :
    M.eRk {e} = 1 :=
  (M.isNonloop_of_loopless he).eRk_eq

@[simp]
/--
lemma `eRk_singleton_le` / 引理 `eRk_singleton_le`

English:
lemma eRk_singleton_le
  given: (M : Matroid α) (e : α)
  statement: M.eRk {e} <= 1
  proof: (M.eRk_le_encard {e}).trans_eq encard_singleton e

@[simp]

中文:
引理 eRk_singleton_le
  条件: (M : 拟阵 α) (e : α)
  结论: M.eRk {e} <= 1
  证明: (M.eRk_le_encard {e}).trans_eq encard_singleton e

@[simp]

Depends on / 依赖: M.eRk_le_encard, eRk_le_encard, encard_singleton, trans_eq
-/
lemma eRk_singleton_le (M : Matroid α) (e : α) : M.eRk {e} <= 1 :=
(M.eRk_le_encard {e}).trans_eq encard_singleton e

@[simp]
/--
lemma `eRk_singleton_eq_one_iff` / 引理 `eRk_singleton_eq_one_iff`

English:
lemma eRk_singleton_eq_one_iff
  given: {e : α}
  statement: M.eRk {e} = 1 ↔ M.IsNonloop e
  proof: by
  refine ⟨fun h => ?_, fun h => h.eRk_eq⟩
  rwa [← indep_singleton, indep_iff_eRk_eq_encard_of_finite (by simp), encard_singleton]

中文:
引理 eRk_singleton_eq_one_iff
  条件: {e : α}
  结论: M.eRk {e} = 1 ↔ M.是Nonloop e
  证明: by
  refine ⟨fun h => ?_, fun h => h.eRk_eq⟩
  rwa [← indep_singleton, indep_iff_eRk_eq_encard_of_finite (by simp), encard_singleton]

Depends on / 依赖: eRk_eq, encard_singleton, h.eRk_eq, indep_iff_eRk_eq_encard_of_finite, indep_singleton
-/
lemma eRk_singleton_eq_one_iff {e : α} : M.eRk {e} = 1 ↔ M.IsNonloop e := by
  refine ⟨fun h => ?_, fun h => h.eRk_eq⟩
  rwa [← indep_singleton, indep_iff_eRk_eq_encard_of_finite (by simp), encard_singleton]

/--
lemma `eRk_eq_one_iff` / 引理 `eRk_eq_one_iff`

English:
lemma eRk_eq_one_iff
  given: (hX : X subseteq M.E := by aesop_mat)
  proof: by
  refine ⟨?_, fun ⟨e, heX, he, hXe⟩ => ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis X
    rw [hI.eRk_eq_encard]; rw [encard_eq_one]
    rintro ⟨e, rfl⟩
    exact ⟨e, singleton_subset_iff.1 hI.subset, indep_singleton.1 hI.indep, hI.subset_closure⟩
  rw [← he.eRk_eq]
  exact ((M.eRk_mono hXe).trans (

中文:
引理 eRk_eq_one_iff
  条件: (hX : X subseteq M.E := by aesop_mat)
  证明: by
  refine ⟨?_, fun ⟨e, heX, he, hXe⟩ => ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis X
    rw [hI.eRk_eq_encard]; rw [encard_eq_one]
    rintro ⟨e, rfl⟩
    exact ⟨e, singleton_subset_iff.1 hI.subset, indep_singleton.1 hI.indep, hI.subset_closure⟩
  rw [← he.eRk_eq]
  exact ((M.eRk_mono hXe).trans (

Depends on / 依赖: IsNonloop, M.IsNonloop, M.closure, M.eRk, M.eRk_closure_eq, M.eRk_mono, M.exists_isBasis, aesop_mat, antisymm, closure, eRk_closure_eq, eRk_eq, eRk_eq_encard, eRk_mono, encard_eq_one, exists_isBasis, hI.eRk_eq_encard, hI.indep, hI.subset, hI.subset_closure
-/
lemma eRk_eq_one_iff (hX : X subseteq M.E := by aesop_mat) :
    M.eRk X = 1 ↔ exists e in X, M.IsNonloop e ∧ X subseteq M.closure {e} := by
  refine ⟨?_, fun ⟨e, heX, he, hXe⟩ => ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis X
    rw [hI.eRk_eq_encard]; rw [encard_eq_one]
    rintro ⟨e, rfl⟩
    exact ⟨e, singleton_subset_iff.1 hI.subset, indep_singleton.1 hI.indep, hI.subset_closure⟩
  rw [← he.eRk_eq]
  exact ((M.eRk_mono hXe).trans (M.eRk_closure_eq _).le).antisymm
    (M.eRk_mono (singleton_subset_iff.2 heX))

/--
lemma `eRk_le_one_iff` / 引理 `eRk_le_one_iff`

English:
lemma eRk_le_one_iff
  given: [M.Nonempty] (hX : X subseteq M.E := by aesop_mat)
  proof: by
  refine ⟨fun h => ?_, fun ⟨e, _, he⟩ => ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis X
    rw [hI.eRk_eq_encard]; rw [encard_le_one_iff_eq] at h
    obtain (rfl | ⟨e, rfl⟩) := h
    · obtain ⟨e, he⟩ := M.ground_nonempty
      exact ⟨e, he, hI.subset_closure.trans ((M.closure_subset_closure (empty_

中文:
引理 eRk_le_one_iff
  条件: [M.非空] (hX : X subseteq M.E := by aesop_mat)
  证明: by
  refine ⟨fun h => ?_, fun ⟨e, _, he⟩ => ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis X
    rw [hI.eRk_eq_encard]; rw [encard_le_one_iff_eq] at h
    obtain (rfl | ⟨e, rfl⟩) := h
    · obtain ⟨e, he⟩ := M.ground_nonempty
      exact ⟨e, he, hI.subset_closure.trans ((M.closure_subset_closure (empty_

Depends on / 依赖: M.closure, M.closure_subset_closure, M.eRk, M.eRk_mono, M.exists_isBasis, M.ground_nonempty, aesop_mat, closure, closure_subset_closure, eRk_closure_eq, eRk_eq_encard, eRk_mono, empty_subset, encard_le_one_iff_eq, encard_singleton, exists_isBasis, ground_nonempty, hI.eRk_eq_encard, hI.indep.subset_ground, hI.subset_closure
-/
lemma eRk_le_one_iff [M.Nonempty] (hX : X subseteq M.E := by aesop_mat) :
    M.eRk X <= 1 ↔ exists e in M.E, X subseteq M.closure {e} := by
  refine ⟨fun h => ?_, fun ⟨e, _, he⟩ => ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis X
    rw [hI.eRk_eq_encard]; rw [encard_le_one_iff_eq] at h
    obtain (rfl | ⟨e, rfl⟩) := h
    · obtain ⟨e, he⟩ := M.ground_nonempty
      exact ⟨e, he, hI.subset_closure.trans ((M.closure_subset_closure (empty_subset _)))⟩
    exact ⟨e, hI.indep.subset_ground rfl, hI.subset_closure⟩
  refine (M.eRk_mono he).trans ?_
  rw [eRk_closure_eq]; rw [← encard_singleton e]
  exact M.eRk_le_encard {e}


/--
lemma `Spanning.eRk_eq` / 引理 `Spanning.eRk_eq`

English:
lemma Spanning.eRk_eq
  given: (hX : M.Spanning X)
  statement: M.eRk X = M.eRank
  proof: by
  obtain ⟨B, hB⟩ := M.exists_isBasis X
exact (M.eRk_le_eRank X).antisymm by
    rw [← hB.encard_eq_eRk]; rw [← (hB.isBase_of_spanning hX).encard_eq_eRank]

中文:
引理 生成.eRk_eq
  条件: (hX : M.生成 X)
  结论: M.eRk X = M.eRank
  证明: by
  obtain ⟨B, hB⟩ := M.exists_isBasis X
exact (M.eRk_le_eRank X).antisymm by
    rw [← hB.encard_eq_eRk]; rw [← (hB.isBase_of_spanning hX).encard_eq_eRank]

Depends on / 依赖: M.eRk_le_eRank, M.exists_isBasis, antisymm, eRk_le_eRank, encard_eq_eRank, encard_eq_eRk, exists_isBasis, hB.encard_eq_eRk, hB.isBase_of_spanning, isBase_of_spanning
-/
lemma Spanning.eRk_eq (hX : M.Spanning X) : M.eRk X = M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBasis X
exact (M.eRk_le_eRank X).antisymm by
    rw [← hB.encard_eq_eRk]; rw [← (hB.isBase_of_spanning hX).encard_eq_eRank]

/--
lemma `spanning_iff_eRk_le'` / 引理 `spanning_iff_eRk_le'`

English:
lemma spanning_iff_eRk_le'
  given: [RankFinite M]
  statement: M.Spanning X ↔ M.eRank <= M.eRk X ∧ X subseteq M.E
  proof: by
  refine ⟨fun h => ⟨h.eRk_eq.symm.le, h.subset_ground⟩, fun ⟨h, hX⟩ => ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  exact (hI.indep.isBase_of_eRk_ge
    hI.indep.finite (h.trans hI.eRk_eq_eRk.symm.le)).spanning_of_superset hI.subset

中文:
引理 spanning_iff_eRk_le'
  条件: [RankFinite M]
  结论: M.生成 X ↔ M.eRank <= M.eRk X ∧ X subseteq M.E
  证明: by
  refine ⟨fun h => ⟨h.eRk_eq.symm.le, h.subset_ground⟩, fun ⟨h, hX⟩ => ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  exact (hI.indep.isBase_of_eRk_ge
    hI.indep.finite (h.trans hI.eRk_eq_eRk.symm.le)).spanning_of_superset hI.subset

Depends on / 依赖: M.exists_isBasis, eRk_eq, eRk_eq_eRk, exists_isBasis, finite, h.eRk_eq.symm.le, h.subset_ground, h.trans, hI.eRk_eq_eRk.symm.le, hI.indep.finite, hI.indep.isBase_of_eRk_ge, hI.subset, isBase_of_eRk_ge, spanning_of_superset, subset, subset_ground
-/
lemma spanning_iff_eRk_le' [RankFinite M] : M.Spanning X ↔ M.eRank <= M.eRk X ∧ X subseteq M.E := by
  refine ⟨fun h => ⟨h.eRk_eq.symm.le, h.subset_ground⟩, fun ⟨h, hX⟩ => ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  exact (hI.indep.isBase_of_eRk_ge
    hI.indep.finite (h.trans hI.eRk_eq_eRk.symm.le)).spanning_of_superset hI.subset

/--
lemma `spanning_iff_eRk_le` / 引理 `spanning_iff_eRk_le`

English:
lemma spanning_iff_eRk_le
  given: [RankFinite M] (hX : X subseteq M.E := by aesop_mat)
  proof: by
  rw [spanning_iff_eRk_le']; rw [and_iff_left hX]

中文:
引理 spanning_iff_eRk_le
  条件: [RankFinite M] (hX : X subseteq M.E := by aesop_mat)
  证明: by
  rw [spanning_iff_eRk_le']; rw [and_iff_left hX]

Depends on / 依赖: M.Spanning, M.eRank, M.eRk, Spanning, aesop_mat, and_iff_left, spanning_iff_eRk_le
-/
lemma spanning_iff_eRk_le [RankFinite M] (hX : X subseteq M.E := by aesop_mat) :
    M.Spanning X ↔ M.eRank <= M.eRk X := by
  rw [spanning_iff_eRk_le']; rw [and_iff_left hX]

/--
lemma `Spanning.eRank_restrict` / 引理 `Spanning.eRank_restrict`

English:
lemma Spanning.eRank_restrict
  given: (hX : M.Spanning X)
  statement: (M ↾ X).eRank = M.eRank
  proof: by
  rw [eRank_def]; rw [restrict_ground_eq]; rw [restrict_eRk_eq _ rfl.subset]; rw [hX.eRk_eq]

中文:
引理 生成.eRank_restrict
  条件: (hX : M.生成 X)
  结论: (M ↾ X).eRank = M.eRank
  证明: by
  rw [eRank_def]; rw [restrict_ground_eq]; rw [restrict_eRk_eq _ rfl.subset]; rw [hX.eRk_eq]

Depends on / 依赖: eRank_def, eRk_eq, hX.eRk_eq, restrict_eRk_eq, restrict_ground_eq, rfl.subset, subset
-/
lemma Spanning.eRank_restrict (hX : M.Spanning X) : (M ↾ X).eRank = M.eRank := by
  rw [eRank_def]; rw [restrict_ground_eq]; rw [restrict_eRk_eq _ rfl.subset]; rw [hX.eRk_eq]

/-! ### Constructions -/

@[simp]
/--
lemma `eRank_map` / 引理 `eRank_map`

English:
lemma eRank_map
  given: {β : Type*} {f : α -> β} (M : Matroid α) (hf : InjOn f M.E)
  proof: by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← (hB.map hf).encard_eq_eRank]; rw [← hB.encard_eq_eRank]; rw [(hf.mono hB.subset_ground).encard_image]

@[simp]

中文:
引理 eRank_map
  条件: {β : 类型} {f : α -> β} (M : 拟阵 α) (hf : 单射限制 f M.E)
  证明: by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← (hB.map hf).encard_eq_eRank]; rw [← hB.encard_eq_eRank]; rw [(hf.mono hB.subset_ground).encard_image]

@[simp]

Depends on / 依赖: M.exists_isBase, encard_eq_eRank, encard_image, exists_isBase, hB.encard_eq_eRank, hB.map, hB.subset_ground, hf.mono, subset_ground
-/
lemma eRank_map {β : Type*} {f : α -> β} (M : Matroid α) (hf : InjOn f M.E) :
    (M.map f hf).eRank = M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← (hB.map hf).encard_eq_eRank]; rw [← hB.encard_eq_eRank]; rw [(hf.mono hB.subset_ground).encard_image]

@[simp]
/--
lemma `eRk_map` / 引理 `eRk_map`

English:
lemma eRk_map
  statement: {β : Type*} {f : α -> β} (M : Matroid α) (hf : InjOn f M.E)
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [hI.eRk_eq_encard]; rw [(hI.map hf).eRk_eq_encard]; rw [(hf.mono hI.indep.subset_ground).encard_image]

@[simp]

中文:
引理 eRk_map
  结论: {β : 类型} {f : α -> β} (M : 拟阵 α) (hf : 单射限制 f M.E)
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [hI.eRk_eq_encard]; rw [(hI.map hf).eRk_eq_encard]; rw [(hf.mono hI.indep.subset_ground).encard_image]

@[simp]

Depends on / 依赖: M.eRk, M.exists_isBasis, M.map, aesop_mat, eRk_eq_encard, encard_image, exists_isBasis, hI.eRk_eq_encard, hI.indep.subset_ground, hI.map, hf.mono, subset_ground
-/
lemma eRk_map {β : Type*} {f : α -> β} (M : Matroid α) (hf : InjOn f M.E)
    (hX : X subseteq M.E := by aesop_mat) : (M.map f hf).eRk (f '' X) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [hI.eRk_eq_encard]; rw [(hI.map hf).eRk_eq_encard]; rw [(hf.mono hI.indep.subset_ground).encard_image]

@[simp]
/--
lemma `eRk_comap` / 引理 `eRk_comap`

English:
lemma eRk_comap
  given: {β : Type*} {f : α -> β} (M : Matroid β) (X : Set α)
  proof: by
  obtain ⟨I, hI⟩ := (M.comap f).exists_isBasis' X
  obtain ⟨hI', hinj, -⟩ := comap_isBasis'_iff.1 hI
  rw [← hI.encard_eq_eRk]; rw [← hI'.encard_eq_eRk]; rw [hinj.encard_image]

@[simp]

中文:
引理 eRk_comap
  条件: {β : 类型} {f : α -> β} (M : 拟阵 β) (X : 集合 α)
  证明: by
  obtain ⟨I, hI⟩ := (M.comap f).exists_isBasis' X
  obtain ⟨hI', hinj, -⟩ := comap_isBasis'_iff.1 hI
  rw [← hI.encard_eq_eRk]; rw [← hI'.encard_eq_eRk]; rw [hinj.encard_image]

@[simp]

Depends on / 依赖: M.comap, _iff, comap_isBasis, encard_eq_eRk, encard_image, exists_isBasis, hI.encard_eq_eRk, hinj.encard_image
-/
lemma eRk_comap {β : Type*} {f : α -> β} (M : Matroid β) (X : Set α) :
    (M.comap f).eRk X = M.eRk (f '' X) := by
  obtain ⟨I, hI⟩ := (M.comap f).exists_isBasis' X
  obtain ⟨hI', hinj, -⟩ := comap_isBasis'_iff.1 hI
  rw [← hI.encard_eq_eRk]; rw [← hI'.encard_eq_eRk]; rw [hinj.encard_image]

@[simp]
/--
lemma `eRk_loopyOn` / 引理 `eRk_loopyOn`

English:
lemma eRk_loopyOn
  given: (X Y : Set α)
  statement: (loopyOn Y).eRk X = 0
  proof: by
  obtain ⟨I, hI⟩ := (loopyOn Y).exists_isBasis' X
  rw [hI.eRk_eq_encard]; rw [loopyOn_indep_iff.1 hI.indep]; rw [encard_empty]

@[simp]

中文:
引理 eRk_loopyOn
  条件: (X Y : 集合 α)
  结论: (loopyOn Y).eRk X = 0
  证明: by
  obtain ⟨I, hI⟩ := (loopyOn Y).exists_isBasis' X
  rw [hI.eRk_eq_encard]; rw [loopyOn_indep_iff.1 hI.indep]; rw [encard_empty]

@[simp]

Depends on / 依赖: eRk_eq_encard, encard_empty, exists_isBasis, hI.eRk_eq_encard, hI.indep, loopyOn, loopyOn_indep_iff
-/
lemma eRk_loopyOn (X Y : Set α) : (loopyOn Y).eRk X = 0 := by
  obtain ⟨I, hI⟩ := (loopyOn Y).exists_isBasis' X
  rw [hI.eRk_eq_encard]; rw [loopyOn_indep_iff.1 hI.indep]; rw [encard_empty]

@[simp]
/--
lemma `eRank_loopyOn` / 引理 `eRank_loopyOn`

English:
lemma eRank_loopyOn
  given: (X : Set α)
  statement: (loopyOn X).eRank = 0
  proof: by
  rw [eRank_def]; rw [eRk_loopyOn]

中文:
引理 eRank_loopyOn
  条件: (X : 集合 α)
  结论: (loopyOn X).eRank = 0
  证明: by
  rw [eRank_def]; rw [eRk_loopyOn]

Depends on / 依赖: eRank_def, eRk_loopyOn
-/
lemma eRank_loopyOn (X : Set α) : (loopyOn X).eRank = 0 := by
  rw [eRank_def]; rw [eRk_loopyOn]

/--
lemma `eRank_eq_zero_iff` / 引理 `eRank_eq_zero_iff`

English:
lemma eRank_eq_zero_iff
  statement: M.eRank = 0 ↔ M = loopyOn M.E
  proof: by
  refine ⟨fun h => closure_empty_eq_ground_iff.1 ?_, fun h => by rw [h, eRank_loopyOn]⟩
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank]; rw [encard_eq_zero] at h
  rw [← h]; rw [hB.closure_eq]

中文:
引理 eRank_eq_zero_iff
  结论: M.eRank = 0 ↔ M = loopyOn M.E
  证明: by
  refine ⟨fun h => closure_empty_eq_ground_iff.1 ?_, fun h => by rw [h, eRank_loopyOn]⟩
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank]; rw [encard_eq_zero] at h
  rw [← h]; rw [hB.closure_eq]

Depends on / 依赖: M.exists_isBase, closure_empty_eq_ground_iff, closure_eq, eRank_loopyOn, encard_eq_eRank, encard_eq_zero, exists_isBase, hB.closure_eq, hB.encard_eq_eRank
-/
lemma eRank_eq_zero_iff : M.eRank = 0 ↔ M = loopyOn M.E := by
  refine ⟨fun h => closure_empty_eq_ground_iff.1 ?_, fun h => by rw [h, eRank_loopyOn]⟩
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank]; rw [encard_eq_zero] at h
  rw [← h]; rw [hB.closure_eq]

/--
lemma `exists_of_eRank_eq_zero` / 引理 `exists_of_eRank_eq_zero`

English:
lemma exists_of_eRank_eq_zero
  given: (h : M.eRank = 0)
  statement: exists X, M = loopyOn X
  proof: ⟨M.E, by simpa [eRank_eq_zero_iff] using h⟩

@[simp]

中文:
引理 存在_of_eRank_eq_zero
  条件: (h : M.eRank = 0)
  结论: 存在 X, M = loopyOn X
  证明: ⟨M.E, by simpa [eRank_eq_zero_iff] using h⟩

@[simp]

Depends on / 依赖: eRank_eq_zero_iff
-/
lemma exists_of_eRank_eq_zero (h : M.eRank = 0) : exists X, M = loopyOn X :=
  ⟨M.E, by simpa [eRank_eq_zero_iff] using h⟩

@[simp]
/--
lemma `eRank_emptyOn` / 引理 `eRank_emptyOn`

English:
lemma eRank_emptyOn
  given: (α : Type*)
  statement: (emptyOn α).eRank = 0
  proof: by
  rw [eRank_eq_zero_iff]; rw [emptyOn_ground]; rw [loopyOn_empty]

中文:
引理 eRank_emptyOn
  条件: (α : 类型)
  结论: (emptyOn α).eRank = 0
  证明: by
  rw [eRank_eq_zero_iff]; rw [emptyOn_ground]; rw [loopyOn_empty]

Depends on / 依赖: eRank_eq_zero_iff, emptyOn_ground, loopyOn_empty
-/
lemma eRank_emptyOn (α : Type*) : (emptyOn α).eRank = 0 := by
  rw [eRank_eq_zero_iff]; rw [emptyOn_ground]; rw [loopyOn_empty]

/--
lemma `eq_loopyOn_iff_eRank` / 引理 `eq_loopyOn_iff_eRank`

English:
lemma eq_loopyOn_iff_eRank
  statement: M = loopyOn X ↔ M.eRank = 0 ∧ M.E = X
  proof: ⟨fun h => by rw [h]; simp, fun ⟨h,h'⟩ => by rw [← h', ← eRank_eq_zero_iff, h]⟩

@[simp]

中文:
引理 eq_loopyOn_iff_eRank
  结论: M = loopyOn X ↔ M.eRank = 0 ∧ M.E = X
  证明: ⟨fun h => by rw [h]; simp, fun ⟨h,h'⟩ => by rw [← h', ← eRank_eq_zero_iff, h]⟩

@[simp]

Depends on / 依赖: eRank_eq_zero_iff
-/
lemma eq_loopyOn_iff_eRank : M = loopyOn X ↔ M.eRank = 0 ∧ M.E = X :=
  ⟨fun h => by rw [h]; simp, fun ⟨h,h'⟩ => by rw [← h', ← eRank_eq_zero_iff, h]⟩

@[simp]
/--
lemma `eRank_freeOn` / 引理 `eRank_freeOn`

English:
lemma eRank_freeOn
  given: (X : Set α)
  statement: (freeOn X).eRank = X.encard
  proof: by
  rw [eRank_def]; rw [freeOn_ground]; rw [(freeOn_indep_iff.2 rfl.subset).eRk_eq_encard]

中文:
引理 eRank_freeOn
  条件: (X : 集合 α)
  结论: (freeOn X).eRank = X.encard
  证明: by
  rw [eRank_def]; rw [freeOn_ground]; rw [(freeOn_indep_iff.2 rfl.subset).eRk_eq_encard]

Depends on / 依赖: eRank_def, eRk_eq_encard, freeOn_ground, freeOn_indep_iff, rfl.subset, subset
-/
lemma eRank_freeOn (X : Set α) : (freeOn X).eRank = X.encard := by
  rw [eRank_def]; rw [freeOn_ground]; rw [(freeOn_indep_iff.2 rfl.subset).eRk_eq_encard]

/--
lemma `eRk_freeOn` / 引理 `eRk_freeOn`

English:
lemma eRk_freeOn
  given: (hXY : X subseteq Y)
  statement: (freeOn Y).eRk X = X.encard
  proof: by
  obtain ⟨I, hI⟩ := (freeOn Y).exists_isBasis X
  rw [hI.eRk_eq_encard]; rw [(freeOn_indep hXY).eq_of_isBasis hI]

中文:
引理 eRk_freeOn
  条件: (hXY : X subseteq Y)
  结论: (freeOn Y).eRk X = X.encard
  证明: by
  obtain ⟨I, hI⟩ := (freeOn Y).exists_isBasis X
  rw [hI.eRk_eq_encard]; rw [(freeOn_indep hXY).eq_of_isBasis hI]

Depends on / 依赖: eRk_eq_encard, eq_of_isBasis, exists_isBasis, freeOn, freeOn_indep, hI.eRk_eq_encard
-/
lemma eRk_freeOn (hXY : X subseteq Y) : (freeOn Y).eRk X = X.encard := by
  obtain ⟨I, hI⟩ := (freeOn Y).exists_isBasis X
  rw [hI.eRk_eq_encard]; rw [(freeOn_indep hXY).eq_of_isBasis hI]


/--
lemma `IsBase.encard_compl_eq` / 引理 `IsBase.encard_compl_eq`

English:
lemma IsBase.encard_compl_eq
  given: (hB : M.IsBase B)
  statement: (M.E \ B).encard = M✶.eRank
  proof: (hB.compl_isBase_dual).encard_eq_eRank

中文:
引理 IsBase.encard_compl_eq
  条件: (hB : M.IsBase B)
  结论: (M.E \ B).encard = M✶.eRank
  证明: (hB.compl_isBase_dual).encard_eq_eRank

Depends on / 依赖: compl_isBase_dual, encard_eq_eRank, hB.compl_isBase_dual
-/
lemma IsBase.encard_compl_eq (hB : M.IsBase B) : (M.E \ B).encard = M✶.eRank :=
  (hB.compl_isBase_dual).encard_eq_eRank

/--
lemma `eRk_dual_add_eRank` / 引理 `eRk_dual_add_eRank`

English:
lemma eRk_dual_add_eRank
  given: (M : Matroid α) (X : Set α) (hX : X subseteq M.E := by aesop_mat)
  proof: by
  obtain ⟨I, hI⟩ := M✶.exists_isBasis X
  obtain ⟨B, hB, rfl⟩ := hI.exists_isBasis_inter_eq_of_superset hX
  have hB' : M✶.IsBase B := isBasis_ground_iff.1 hB
  have hd : M.IsBasis (M.E \ B inter (M.E \ X)) (M.E \ X) := by
    simpa using hB'.inter_isBasis_iff_compl_inter_isBasis_dual.1 hI
  rw [

中文:
引理 eRk_dual_add_eRank
  条件: (M : 拟阵 α) (X : 集合 α) (hX : X subseteq M.E := by aesop_mat)
  证明: by
  obtain ⟨I, hI⟩ := M✶.exists_isBasis X
  obtain ⟨B, hB, rfl⟩ := hI.exists_isBasis_inter_eq_of_superset hX
  have hB' : M✶.IsBase B := isBasis_ground_iff.1 hB
  have hd : M.IsBasis (M.E \ B inter (M.E \ X)) (M.E \ X) := by
    simpa using hB'.inter_isBasis_iff_compl_inter_isBasis_dual.1 hI
  rw [

Depends on / 依赖: IsBase, IsBasis, M.IsBasis, M.eRank, M.eRk, X.encard, aesop_mat, compl_isBase_of_dual, compl_isBase_of_dual.encard_eq_eRank, eRk_eq_encard, encard, encard_eq_eRank, encard_unio, encard_union_eq, exists_isBasis, exists_isBasis_inter_eq_of_superset, hI.eRk_eq_encard, hI.exists_isBasis_inter_eq_of_superset, hd.eRk_eq_encard, inter_isBasis_iff_compl_inter_isBasis_dual
-/
lemma eRk_dual_add_eRank (M : Matroid α) (X : Set α) (hX : X subseteq M.E := by aesop_mat) :
    M✶.eRk X + M.eRank = M.eRk (M.E \ X) + X.encard := by
  obtain ⟨I, hI⟩ := M✶.exists_isBasis X
  obtain ⟨B, hB, rfl⟩ := hI.exists_isBasis_inter_eq_of_superset hX
  have hB' : M✶.IsBase B := isBasis_ground_iff.1 hB
  have hd : M.IsBasis (M.E \ B inter (M.E \ X)) (M.E \ X) := by
    simpa using hB'.inter_isBasis_iff_compl_inter_isBasis_dual.1 hI
  rw [← hB'.compl_isBase_of_dual.encard_eq_eRank]; rw [hI.eRk_eq_encard]; rw [hd.eRk_eq_encard]; rw [← encard_union_eq (by tauto_set)]; rw [← encard_union_eq (by tauto_set)]
  exact congr_arg _ (by tauto_set)

/--
lemma `eRk_dual_add_eRank'` / 引理 `eRk_dual_add_eRank'`

English:
lemma eRk_dual_add_eRank'
  given: (M : Matroid α) (X : Set α)
  proof: by
  rw [← sdiff_inter_self_eq_sdiff]; rw [← eRk_dual_add_eRank ..]; rw [← dual_ground]; rw [eRk_inter_ground]

@[simp]

中文:
引理 eRk_dual_add_eRank'
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: by
  rw [← sdiff_inter_self_eq_sdiff]; rw [← eRk_dual_add_eRank ..]; rw [← dual_ground]; rw [eRk_inter_ground]

@[simp]

Depends on / 依赖: dual_ground, eRk_dual_add_eRank, eRk_inter_ground, sdiff_inter_self_eq_sdiff
-/
lemma eRk_dual_add_eRank' (M : Matroid α) (X : Set α) :
    M✶.eRk X + M.eRank = M.eRk (M.E \ X) + (X inter M.E).encard := by
  rw [← sdiff_inter_self_eq_sdiff]; rw [← eRk_dual_add_eRank ..]; rw [← dual_ground]; rw [eRk_inter_ground]

@[simp]
/--
lemma `eRank_add_eRank_dual` / 引理 `eRank_add_eRank_dual`

English:
lemma eRank_add_eRank_dual
  given: (M : Matroid α)
  statement: M.eRank + M✶.eRank = M.E.encard
  proof: by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank]; rw [← hB.compl_isBase_dual.encard_eq_eRank]; rw [← encard_union_eq disjoint_sdiff_right]; rw [union_sdiff_cancel hB.subset_ground]

中文:
引理 eRank_add_eRank_dual
  条件: (M : 拟阵 α)
  结论: M.eRank + M✶.eRank = M.E.encard
  证明: by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank]; rw [← hB.compl_isBase_dual.encard_eq_eRank]; rw [← encard_union_eq disjoint_sdiff_right]; rw [union_sdiff_cancel hB.subset_ground]

Depends on / 依赖: M.exists_isBase, compl_isBase_dual, disjoint_sdiff_right, encard_eq_eRank, encard_union_eq, exists_isBase, hB.compl_isBase_dual.encard_eq_eRank, hB.encard_eq_eRank, hB.subset_ground, subset_ground, union_sdiff_cancel
-/
lemma eRank_add_eRank_dual (M : Matroid α) : M.eRank + M✶.eRank = M.E.encard := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank]; rw [← hB.compl_isBase_dual.encard_eq_eRank]; rw [← encard_union_eq disjoint_sdiff_right]; rw [union_sdiff_cancel hB.subset_ground]

end Matroid
