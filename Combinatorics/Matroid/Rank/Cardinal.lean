/-
Copyright (c) 2025 Peter Nelson and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Junyan Xu
-/
module

public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Combinatorics.Matroid.Rank.Finite
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinal-valued rank

In a finitary matroid, all bases have the same cardinality.
In fact, something stronger holds: if each of `I` and `J` is a basis for a set `X`,
then `#(I \ J) = #(J \ I)` and (consequently) `#I = #J`.
This file introduces a typeclass `InvariantCardinalRank` that applies to any matroid
such that this property holds for all `I`, `J` and `X`.

A matroid satisfying this condition has a well-defined cardinality-valued rank function,
both for itself and all its minors.

## Main Declarations

* `Matroid.InvariantCardinalRank` : a typeclass capturing the idea that a matroid and all its minors
  have a well-behaved cardinal-valued rank function.
* `Matroid.cRank M` is the supremum of the cardinalities of the bases of matroid `M`.
* `Matroid.cRk M X` is the supremum of the cardinalities of the bases of a set `X` in a matroid `M`.
* `invariantCardinalRank_of_finitary` is the instance
  showing that `Finitary` matroids are `InvariantCardinalRank`.
* `cRk_inter_add_cRk_union_le` states that cardinal rank is submodular.

## Notes

It is not (provably) the case that all matroids are `InvariantCardinalRank`,
since the equicardinality of bases in general matroids is independent of ZFC
(see the module docstring of `Mathlib/Combinatorics/Matroid/Basic.lean`).
Lemmas like `Matroid.Base.cardinalMk_sdiff_comm` become true for all matroids
only if they are weakened by replacing `Cardinal.mk` with the cruder `ℕ∞`-valued `Set.encard`.
The `ℕ∞`-valued rank and rank functions `Matroid.eRank` and `Matroid.eRk`,
which have a more unconditionally strong API,
are developed in `Mathlib/Combinatorics/Matroid/Rank/ENat.lean`.

## Implementation Details

Since the functions `cRank` and `cRk` are defined as suprema,
independently of the `Matroid.InvariantCardinalRank` typeclass,
they are well-defined for all matroids.
However, for matroids that do not satisfy `InvariantCardinalRank`, they are badly behaved.
For instance, in general `cRk` is not submodular,
and its value may differ on a set `X` and the closure of `X`.
We state and prove theorems without `InvariantCardinalRank` whenever possible,
which sometime makes their proofs longer than they would be with the instance.

## TODO

* Higgs' theorem : if the generalized continuum hypothesis holds,
  then every matroid is `InvariantCardinalRank`.

-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type v} {f : α -> β} {M : Matroid α} {I J B B' X Y : Set α}

open Cardinal Set

namespace Matroid

section Rank

variable {κ : Cardinal}

/--
Definition of `cRank` / `cRank` 的定义

English:
definition cRank
  signature: (M : Matroid α)
  body: ⨆ B : {B // M.IsBase B}, #B

中文:
定义 cRank
  签名: (M : 拟阵 α)
  定义体: ⨆ B : {B // M.IsBase B}, #B

Depends on / 依赖: IsBase, M.IsBase
-/
noncomputable def cRank (M : Matroid α) := ⨆ B : {B // M.IsBase B}, #B

/--
Definition of `cRk` / `cRk` 的定义

English:
definition cRk
  signature: (M : Matroid α) (X : Set α)
  body: (M ↾ X).cRank

中文:
定义 cRk
  签名: (M : 拟阵 α) (X : 集合 α)
  定义体: (M ↾ X).cRank
-/
noncomputable def cRk (M : Matroid α) (X : Set α) := (M ↾ X).cRank

/--
theorem `IsBase.cardinalMk_le_cRank` / 定理 `IsBase.cardinalMk_le_cRank`

English:
theorem IsBase.cardinalMk_le_cRank
  given: (hB : M.IsBase B)
  statement: #B <= M.cRank
  proof: le_ciSup (f := fun B : {B // M.IsBase B} => #B.1) bddAbove_of_small ⟨B, hB⟩

中文:
定理 IsBase.cardinalMk_le_cRank
  条件: (hB : M.IsBase B)
  结论: #B <= M.cRank
  证明: le_ciSup (f := fun B : {B // M.IsBase B} => #B.1) bddAbove_of_small ⟨B, hB⟩

Depends on / 依赖: IsBase, M.IsBase, bddAbove_of_small, le_ciSup
-/
theorem IsBase.cardinalMk_le_cRank (hB : M.IsBase B) : #B <= M.cRank :=
  le_ciSup (f := fun B : {B // M.IsBase B} => #B.1) bddAbove_of_small ⟨B, hB⟩

/--
theorem `Indep.cardinalMk_le_cRank` / 定理 `Indep.cardinalMk_le_cRank`

English:
theorem Indep.cardinalMk_le_cRank
  given: (ind : M.Indep I)
  statement: #I <= M.cRank
  proof: have ⟨B, isBase, hIB⟩ := ind.exists_isBase_superset
  le_ciSup_of_le bddAbove_of_small ⟨B, isBase⟩ (mk_le_mk_of_subset hIB)

中文:
定理 Indep.cardinalMk_le_cRank
  条件: (ind : M.Indep I)
  结论: #I <= M.cRank
  证明: have ⟨B, isBase, hIB⟩ := ind.exists_isBase_superset
  le_ciSup_of_le bddAbove_of_small ⟨B, isBase⟩ (mk_le_mk_of_subset hIB)

Depends on / 依赖: bddAbove_of_small, exists_isBase_superset, ind.exists_isBase_superset, isBase, le_ciSup_of_le, mk_le_mk_of_subset
-/
theorem Indep.cardinalMk_le_cRank (ind : M.Indep I) : #I <= M.cRank :=
  have ⟨B, isBase, hIB⟩ := ind.exists_isBase_superset
  le_ciSup_of_le bddAbove_of_small ⟨B, isBase⟩ (mk_le_mk_of_subset hIB)

/--
theorem `cRank_eq_iSup_cardinalMk_indep` / 定理 `cRank_eq_iSup_cardinalMk_indep`

English:
theorem cRank_eq_iSup_cardinalMk_indep
  statement: M.cRank = ⨆ I : {I // M.Indep I}, #I
  proof: (ciSup_le' fun B => le_ciSup_of_le bddAbove_of_small ⟨B, B.2.indep⟩ <| by rfl).antisymm
    ciSup_le' fun I =>
      have ⟨B, isBase, hIB⟩ := I.2.exists_isBase_superset
      le_ciSup_of_le bddAbove_of_small ⟨B, isBase⟩ (mk_le_mk_of_subset hIB)

中文:
定理 cRank_eq_iSup_cardinalMk_indep
  结论: M.cRank = ⨆ I : {I // M.Indep I}, #I
  证明: (ciSup_le' fun B => le_ciSup_of_le bddAbove_of_small ⟨B, B.2.indep⟩ <| by rfl).antisymm
    ciSup_le' fun I =>
      have ⟨B, isBase, hIB⟩ := I.2.exists_isBase_superset
      le_ciSup_of_le bddAbove_of_small ⟨B, isBase⟩ (mk_le_mk_of_subset hIB)

Depends on / 依赖: antisymm, bddAbove_of_small, ciSup_le, exists_isBase_superset, isBase, le_ciSup_of_le, mk_le_mk_of_subset
-/
theorem cRank_eq_iSup_cardinalMk_indep : M.cRank = ⨆ I : {I // M.Indep I}, #I :=
(ciSup_le' fun B => le_ciSup_of_le bddAbove_of_small ⟨B, B.2.indep⟩ <| by rfl).antisymm
    ciSup_le' fun I =>
      have ⟨B, isBase, hIB⟩ := I.2.exists_isBase_superset
      le_ciSup_of_le bddAbove_of_small ⟨B, isBase⟩ (mk_le_mk_of_subset hIB)

/--
theorem `IsBasis'.cardinalMk_le_cRk` / 定理 `IsBasis'.cardinalMk_le_cRk`

English:
theorem IsBasis'.cardinalMk_le_cRk
  given: (hIX : M.IsBasis' I X)
  statement: #I <= M.cRk X
  proof: (isBase_restrict_iff'.2 hIX).cardinalMk_le_cRank

中文:
定理 是基'.cardinalMk_le_cRk
  条件: (hIX : M.是基' I X)
  结论: #I <= M.cRk X
  证明: (isBase_restrict_iff'.2 hIX).cardinalMk_le_cRank
-/
theorem IsBasis'.cardinalMk_le_cRk (hIX : M.IsBasis' I X) : #I <= M.cRk X :=
  (isBase_restrict_iff'.2 hIX).cardinalMk_le_cRank

/--
theorem `IsBasis.cardinalMk_le_cRk` / 定理 `IsBasis.cardinalMk_le_cRk`

English:
theorem IsBasis.cardinalMk_le_cRk
  given: (hIX : M.IsBasis I X)
  statement: #I <= M.cRk X
  proof: hIX.isBasis'.cardinalMk_le_cRk

中文:
定理 是基.cardinalMk_le_cRk
  条件: (hIX : M.是基 I X)
  结论: #I <= M.cRk X
  证明: hIX.isBasis'.cardinalMk_le_cRk

Depends on / 依赖: cardinalMk_le_cRk, hIX.isBasis, isBasis
-/
theorem IsBasis.cardinalMk_le_cRk (hIX : M.IsBasis I X) : #I <= M.cRk X :=
  hIX.isBasis'.cardinalMk_le_cRk

/--
theorem `cRank_le_iff` / 定理 `cRank_le_iff`

English:
theorem cRank_le_iff
  statement: M.cRank <= κ ↔ forall ⦃B⦄, M.IsBase B -> #B <= κ
  proof: ⟨fun h _ hB => (hB.cardinalMk_le_cRank.trans h), fun h => ciSup_le fun ⟨_, hB⟩ => h hB⟩

中文:
定理 cRank_le_iff
  结论: M.cRank <= κ ↔ 对任意 ⦃B⦄, M.IsBase B -> #B <= κ
  证明: ⟨fun h _ hB => (hB.cardinalMk_le_cRank.trans h), fun h => ciSup_le fun ⟨_, hB⟩ => h hB⟩

Depends on / 依赖: cardinalMk_le_cRank, ciSup_le, hB.cardinalMk_le_cRank.trans
-/
theorem cRank_le_iff : M.cRank <= κ ↔ forall ⦃B⦄, M.IsBase B -> #B <= κ :=
  ⟨fun h _ hB => (hB.cardinalMk_le_cRank.trans h), fun h => ciSup_le fun ⟨_, hB⟩ => h hB⟩

/--
theorem `cRk_le_iff` / 定理 `cRk_le_iff`

English:
theorem cRk_le_iff
  statement: M.cRk X <= κ ↔ forall ⦃I⦄, M.IsBasis' I X -> #I <= κ
  proof: by
  simp_rw [cRk, cRank_le_iff, isBase_restrict_iff']

中文:
定理 cRk_le_iff
  结论: M.cRk X <= κ ↔ 对任意 ⦃I⦄, M.是基' I X -> #I <= κ
  证明: by
  simp_rw [cRk, cRank_le_iff, isBase_restrict_iff']

Depends on / 依赖: cRank_le_iff, isBase_restrict_iff, simp_rw
-/
theorem cRk_le_iff : M.cRk X <= κ ↔ forall ⦃I⦄, M.IsBasis' I X -> #I <= κ := by
  simp_rw [cRk, cRank_le_iff, isBase_restrict_iff']

/--
theorem `Indep.cardinalMk_le_cRk_of_subset` / 定理 `Indep.cardinalMk_le_cRk_of_subset`

English:
theorem Indep.cardinalMk_le_cRk_of_subset
  given: (hI : M.Indep I) (hIX : I subseteq X)
  statement: #I <= M.cRk X
  proof: let ⟨_, hJ, hIJ⟩ := hI.subset_isBasis'_of_subset hIX
  (mk_le_mk_of_subset hIJ).trans hJ.cardinalMk_le_cRk

中文:
定理 Indep.cardinalMk_le_cRk_of_subset
  条件: (hI : M.Indep I) (hIX : I subseteq X)
  结论: #I <= M.cRk X
  证明: let ⟨_, hJ, hIJ⟩ := hI.subset_isBasis'_of_subset hIX
  (mk_le_mk_of_subset hIJ).trans hJ.cardinalMk_le_cRk

Depends on / 依赖: _of_subset, cardinalMk_le_cRk, hI.subset_isBasis, hJ.cardinalMk_le_cRk, mk_le_mk_of_subset, subset_isBasis
-/
theorem Indep.cardinalMk_le_cRk_of_subset (hI : M.Indep I) (hIX : I subseteq X) : #I <= M.cRk X :=
  let ⟨_, hJ, hIJ⟩ := hI.subset_isBasis'_of_subset hIX
  (mk_le_mk_of_subset hIJ).trans hJ.cardinalMk_le_cRk

/--
theorem `cRk_le_cardinalMk` / 定理 `cRk_le_cardinalMk`

English:
theorem cRk_le_cardinalMk
  given: (M : Matroid α) (X : Set α)
  statement: M.cRk X <= #X
  proof: ciSup_le fun ⟨_, hI⟩ => mk_le_mk_of_subset hI.subset_ground

中文:
定理 cRk_le_cardinalMk
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: M.cRk X <= #X
  证明: ciSup_le fun ⟨_, hI⟩ => mk_le_mk_of_subset hI.subset_ground

Depends on / 依赖: ciSup_le, hI.subset_ground, mk_le_mk_of_subset, subset_ground
-/
theorem cRk_le_cardinalMk (M : Matroid α) (X : Set α) : M.cRk X <= #X :=
  ciSup_le fun ⟨_, hI⟩ => mk_le_mk_of_subset hI.subset_ground

/--
theorem `cRk_ground` / 定理 `cRk_ground`

English:
theorem cRk_ground
  given: (M : Matroid α)
  statement: M.cRk M.E = M.cRank
  proof: by
  rw [cRk]; rw [restrict_ground_eq_self]

中文:
定理 cRk_ground
  条件: (M : 拟阵 α)
  结论: M.cRk M.E = M.cRank
  证明: by
  rw [cRk]; rw [restrict_ground_eq_self]
-/
@[simp] theorem cRk_ground (M : Matroid α) : M.cRk M.E = M.cRank := by
  rw [cRk]; rw [restrict_ground_eq_self]

/--
theorem `cRank_restrict` / 定理 `cRank_restrict`

English:
theorem cRank_restrict
  given: (M : Matroid α) (X : Set α)
  statement: (M ↾ X).cRank = M.cRk X
  proof: rfl

中文:
定理 cRank_restrict
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: (M ↾ X).cRank = M.cRk X
  证明: rfl
-/
@[simp] theorem cRank_restrict (M : Matroid α) (X : Set α) : (M ↾ X).cRank = M.cRk X := rfl

/--
theorem `cRk_mono` / 定理 `cRk_mono`

English:
theorem cRk_mono
  given: (M : Matroid α)
  statement: Monotone M.cRk
  proof: by
  simp only [Monotone, cRk_le_iff]
  intro X Y hXY I hIX
  obtain ⟨J, hJ, hIJ⟩ := hIX.indep.subset_isBasis'_of_subset (hIX.subset.trans hXY)
  exact (mk_le_mk_of_subset hIJ).trans hJ.cardinalMk_le_cRk

中文:
定理 cRk_mono
  条件: (M : 拟阵 α)
  结论: 递增 M.cRk
  证明: by
  simp only [Monotone, cRk_le_iff]
  intro X Y hXY I hIX
  obtain ⟨J, hJ, hIJ⟩ := hIX.indep.subset_isBasis'_of_subset (hIX.subset.trans hXY)
  exact (mk_le_mk_of_subset hIJ).trans hJ.cardinalMk_le_cRk

Depends on / 依赖: Monotone, _of_subset, cRk_le_iff, cardinalMk_le_cRk, hIX.indep.subset_isBasis, hIX.subset.trans, hJ.cardinalMk_le_cRk, mk_le_mk_of_subset, subset, subset_isBasis
-/
theorem cRk_mono (M : Matroid α) : Monotone M.cRk := by
  simp only [Monotone, cRk_le_iff]
  intro X Y hXY I hIX
  obtain ⟨J, hJ, hIJ⟩ := hIX.indep.subset_isBasis'_of_subset (hIX.subset.trans hXY)
  exact (mk_le_mk_of_subset hIJ).trans hJ.cardinalMk_le_cRk

/--
theorem `cRk_le_of_subset` / 定理 `cRk_le_of_subset`

English:
theorem cRk_le_of_subset
  given: (M : Matroid α) (hXY : X subseteq Y)
  statement: M.cRk X <= M.cRk Y
  proof: M.cRk_mono hXY

中文:
定理 cRk_le_of_subset
  条件: (M : 拟阵 α) (hXY : X subseteq Y)
  结论: M.cRk X <= M.cRk Y
  证明: M.cRk_mono hXY

Depends on / 依赖: M.cRk_mono, cRk_mono
-/
theorem cRk_le_of_subset (M : Matroid α) (hXY : X subseteq Y) : M.cRk X <= M.cRk Y :=
  M.cRk_mono hXY

/--
theorem `cRk_inter_ground` / 定理 `cRk_inter_ground`

English:
theorem cRk_inter_ground
  given: (M : Matroid α) (X : Set α)
  statement: M.cRk (X inter M.E) = M.cRk X
  proof: (M.cRk_le_of_subset inter_subset_left).antisymm cRk_le_iff.2
    fun _ h => h.isBasis_inter_ground.cardinalMk_le_cRk

中文:
定理 cRk_inter_ground
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: M.cRk (X inter M.E) = M.cRk X
  证明: (M.cRk_le_of_subset inter_subset_left).antisymm cRk_le_iff.2
    fun _ h => h.isBasis_inter_ground.cardinalMk_le_cRk
-/
@[simp] theorem cRk_inter_ground (M : Matroid α) (X : Set α) : M.cRk (X inter M.E) = M.cRk X :=
(M.cRk_le_of_subset inter_subset_left).antisymm cRk_le_iff.2
    fun _ h => h.isBasis_inter_ground.cardinalMk_le_cRk

/--
theorem `cRk_restrict_subset` / 定理 `cRk_restrict_subset`

English:
theorem cRk_restrict_subset
  given: (M : Matroid α) (hYX : Y subseteq X)
  statement: (M ↾ X).cRk Y = M.cRk Y
  proof: by
  have aux : forall ⦃I⦄, M.IsBasis' I Y ↔ (M ↾ X).IsBasis' I Y := by
    simp_rw [isBasis'_restrict_iff, inter_eq_self_of_subset_left hYX, iff_self_and]
    exact fun I h => h.subset.trans hYX
  simp_rw [le_antisymm_iff, cRk_le_iff]
  exact ⟨fun I hI => (aux.2 hI).cardinalMk_le_cRk, fun I hI => (aux.1 hI).cardinalMk_le_cRk⟩

中文:
定理 cRk_restrict_subset
  条件: (M : 拟阵 α) (hYX : Y subseteq X)
  结论: (M ↾ X).cRk Y = M.cRk Y
  证明: by
  have aux : forall ⦃I⦄, M.IsBasis' I Y ↔ (M ↾ X).IsBasis' I Y := by
    simp_rw [isBasis'_restrict_iff, inter_eq_self_of_subset_left hYX, iff_self_and]
    exact fun I h => h.subset.trans hYX
  simp_rw [le_antisymm_iff, cRk_le_iff]
  exact ⟨fun I hI => (aux.2 hI).cardinalMk_le_cRk, fun I hI => (aux.1 hI).cardinalMk_le_cRk⟩

Depends on / 依赖: IsBasis, M.IsBasis, _restrict_iff, cRk_le_iff, cardinalMk_le_cRk, h.subset.trans, iff_self_and, inter_eq_self_of_subset_left, isBasis, le_antisymm_iff, simp_rw, subset
-/
theorem cRk_restrict_subset (M : Matroid α) (hYX : Y subseteq X) : (M ↾ X).cRk Y = M.cRk Y := by
  have aux : forall ⦃I⦄, M.IsBasis' I Y ↔ (M ↾ X).IsBasis' I Y := by
    simp_rw [isBasis'_restrict_iff, inter_eq_self_of_subset_left hYX, iff_self_and]
    exact fun I h => h.subset.trans hYX
  simp_rw [le_antisymm_iff, cRk_le_iff]
  exact ⟨fun I hI => (aux.2 hI).cardinalMk_le_cRk, fun I hI => (aux.1 hI).cardinalMk_le_cRk⟩

/--
theorem `cRk_restrict` / 定理 `cRk_restrict`

English:
theorem cRk_restrict
  given: (M : Matroid α) (X Y : Set α)
  statement: (M ↾ X).cRk Y = M.cRk (X inter Y)
  proof: by
  rw [← cRk_inter_ground]; rw [restrict_ground_eq]; rw [cRk_restrict_subset _ inter_subset_right]; rw [inter_comm]

中文:
定理 cRk_restrict
  条件: (M : 拟阵 α) (X Y : 集合 α)
  结论: (M ↾ X).cRk Y = M.cRk (X inter Y)
  证明: by
  rw [← cRk_inter_ground]; rw [restrict_ground_eq]; rw [cRk_restrict_subset _ inter_subset_right]; rw [inter_comm]

Depends on / 依赖: cRk_inter_ground, cRk_restrict_subset, inter_comm, inter_subset_right, restrict_ground_eq
-/
theorem cRk_restrict (M : Matroid α) (X Y : Set α) : (M ↾ X).cRk Y = M.cRk (X inter Y) := by
  rw [← cRk_inter_ground]; rw [restrict_ground_eq]; rw [cRk_restrict_subset _ inter_subset_right]; rw [inter_comm]

/--
theorem `Indep.cRk_eq_cardinalMk` / 定理 `Indep.cRk_eq_cardinalMk`

English:
theorem Indep.cRk_eq_cardinalMk
  given: (hI : M.Indep I)
  statement: #I = M.cRk I
  proof: (M.cRk_le_cardinalMk I).antisymm' (hI.isBasis_self.cardinalMk_le_cRk)

中文:
定理 Indep.cRk_eq_cardinalMk
  条件: (hI : M.Indep I)
  结论: #I = M.cRk I
  证明: (M.cRk_le_cardinalMk I).antisymm' (hI.isBasis_self.cardinalMk_le_cRk)

Depends on / 依赖: M.cRk_le_cardinalMk, antisymm, cRk_le_cardinalMk, cardinalMk_le_cRk, hI.isBasis_self.cardinalMk_le_cRk, isBasis_self
-/
theorem Indep.cRk_eq_cardinalMk (hI : M.Indep I) : #I = M.cRk I :=
  (M.cRk_le_cardinalMk I).antisymm' (hI.isBasis_self.cardinalMk_le_cRk)

/--
theorem `cRk_map_image_lift` / 定理 `cRk_map_image_lift`

English:
theorem cRk_map_image_lift
  statement: (M : Matroid α) (hf : InjOn f M.E) (X : Set α)
  proof: by
  nth_rw 1 [cRk, cRank, le_antisymm_iff, lift_iSup bddAbove_of_small, cRk, cRank, cRk, cRank]
  nth_rw 2 [lift_iSup bddAbove_of_small]
  simp only [ciSup_le_iff bddAbove_of_small, Subtype.forall, isBase_restrict_iff',
    isBasis'_iff_isBasis hX, isBasis'_iff_isBasis (show f '' X subseteq (M.map f hf).E from image_mono hX)]
  refine ⟨fun I hI => ?_, fun I hI => ?_⟩
  · obtain ⟨I, X', hIX, rfl, hXX'⟩ := map_isBasis_iff'.1 hI
    rw [mk_image_eq_of_injOn_lift _ _ (hf.mono hIX.indep.subset_ground)]; rw [lift_le]
    obtain rfl : X = X' := by rwa [hf.image_eq_image_iff hX hIX.subset_ground] at hXX'
    exact hIX.cardinalMk_le_cRk
  rw [← mk_image_eq_of_injOn_lift _ _ (hf.mono hI.indep.subset_ground)]; rw [lift_le]
  exact (hI.map hf).cardinalMk_le_cRk

中文:
定理 cRk_map_image_lift
  结论: (M : 拟阵 α) (hf : 单射限制 f M.E) (X : 集合 α)
  证明: by
  nth_rw 1 [cRk, cRank, le_antisymm_iff, lift_iSup bddAbove_of_small, cRk, cRank, cRk, cRank]
  nth_rw 2 [lift_iSup bddAbove_of_small]
  simp only [ciSup_le_iff bddAbove_of_small, Subtype.forall, isBase_restrict_iff',
    isBasis'_iff_isBasis hX, isBasis'_iff_isBasis (show f '' X subseteq (M.map f hf).E from image_mono hX)]
  refine ⟨fun I hI => ?_, fun I hI => ?_⟩
  · obtain ⟨I, X', hIX, rfl, hXX'⟩ := map_isBasis_iff'.1 hI
    rw [mk_image_eq_of_injOn_lift _ _ (hf.mono hIX.indep.subset_ground)]; rw [lift_le]
    obtain rfl : X = X' := by rwa [hf.image_eq_image_iff hX hIX.subset_ground] at hXX'
    exact hIX.cardinalMk_le_cRk
  rw [← mk_image_eq_of_injOn_lift _ _ (hf.mono hI.indep.subset_ground)]; rw [lift_le]
  exact (hI.map hf).cardinalMk_le_cRk
-/
@[simp] theorem cRk_map_image_lift (M : Matroid α) (hf : InjOn f M.E) (X : Set α)
    (hX : X subseteq M.E := by aesop_mat) : lift.{u, v} ((M.map f hf).cRk (f '' X)) = lift (M.cRk X) := by
  nth_rw 1 [cRk, cRank, le_antisymm_iff, lift_iSup bddAbove_of_small, cRk, cRank, cRk, cRank]
  nth_rw 2 [lift_iSup bddAbove_of_small]
  simp only [ciSup_le_iff bddAbove_of_small, Subtype.forall, isBase_restrict_iff',
    isBasis'_iff_isBasis hX, isBasis'_iff_isBasis (show f '' X subseteq (M.map f hf).E from image_mono hX)]
  refine ⟨fun I hI => ?_, fun I hI => ?_⟩
  · obtain ⟨I, X', hIX, rfl, hXX'⟩ := map_isBasis_iff'.1 hI
    rw [mk_image_eq_of_injOn_lift _ _ (hf.mono hIX.indep.subset_ground)]; rw [lift_le]
    obtain rfl : X = X' := by rwa [hf.image_eq_image_iff hX hIX.subset_ground] at hXX'
    exact hIX.cardinalMk_le_cRk
  rw [← mk_image_eq_of_injOn_lift _ _ (hf.mono hI.indep.subset_ground)]; rw [lift_le]
  exact (hI.map hf).cardinalMk_le_cRk

/--
theorem `cRk_map_image` / 定理 `cRk_map_image`

English:
theorem cRk_map_image
  statement: {β : Type u} {f : α -> β} (M : Matroid α) (hf : InjOn f M.E)
  proof: lift_inj.1 M.cRk_map_image_lift ..

中文:
定理 cRk_map_image
  结论: {β : 类型u} {f : α -> β} (M : 拟阵 α) (hf : 单射限制 f M.E)
  证明: lift_inj.1 M.cRk_map_image_lift ..
-/
@[simp] theorem cRk_map_image {β : Type u} {f : α -> β} (M : Matroid α) (hf : InjOn f M.E)
    (X : Set α) (hX : X subseteq M.E := by aesop_mat) : (M.map f hf).cRk (f '' X) = M.cRk X :=
lift_inj.1 M.cRk_map_image_lift ..

/--
theorem `cRk_map_eq` / 定理 `cRk_map_eq`

English:
theorem cRk_map_eq
  given: {β : Type u} {f : α -> β} {X : Set β} (M : Matroid α) (hf : InjOn f M.E)
  proof: by
  rw [← M.cRk_inter_ground]; rw [← M.cRk_map_image hf _]; rw [image_preimage_inter]; rw [← map_ground _ _ hf]; rw [cRk_inter_ground]

中文:
定理 cRk_map_eq
  条件: {β : 类型u} {f : α -> β} {X : 集合 β} (M : 拟阵 α) (hf : 单射限制 f M.E)
  证明: by
  rw [← M.cRk_inter_ground]; rw [← M.cRk_map_image hf _]; rw [image_preimage_inter]; rw [← map_ground _ _ hf]; rw [cRk_inter_ground]

Depends on / 依赖: M.cRk_inter_ground, M.cRk_map_image, cRk_inter_ground, cRk_map_image, image_preimage_inter, map_ground
-/
theorem cRk_map_eq {β : Type u} {f : α -> β} {X : Set β} (M : Matroid α) (hf : InjOn f M.E) :
    (M.map f hf).cRk X = M.cRk (f ⁻¹' X) := by
  rw [← M.cRk_inter_ground]; rw [← M.cRk_map_image hf _]; rw [image_preimage_inter]; rw [← map_ground _ _ hf]; rw [cRk_inter_ground]

/--
theorem `cRk_comap_lift` / 定理 `cRk_comap_lift`

English:
theorem cRk_comap_lift
  given: (M : Matroid β) (f : α -> β) (X : Set α)
  proof: by
  nth_rw 1 [cRk, cRank, le_antisymm_iff, lift_iSup bddAbove_of_small, cRk, cRank, cRk, cRank]
  nth_rw 2 [lift_iSup bddAbove_of_small]
  simp only [ciSup_le_iff bddAbove_of_small, Subtype.forall, isBase_restrict_iff',
    comap_isBasis'_iff, and_imp]
  refine ⟨fun I hI hfI hIX => ?_, fun I hIX => ?_⟩
  · rw [← mk_image_eq_of_injOn_lift _ _ hfI, lift_le]
    exact hI.cardinalMk_le_cRk
  obtain ⟨I₀, hI₀X, rfl, hfI₀⟩ := show exists I₀ subseteq X, f '' I₀ = I ∧ InjOn f I₀ by
    obtain ⟨I₀, hI₀ss, hbij⟩ := exists_subset_bijOn (f ⁻¹' I inter X) f
    refine ⟨I₀, hI₀ss.trans inter_subset_right, ?_, hbij.injOn⟩
    rw [hbij.image_eq]; rw [image_preimage_inter]; rw [inter_eq_self_of_subset_left hIX.subset]
  rw [mk_image_eq_of_injOn_lift _ _ hfI₀]; rw [lift_le]
exact IsBasis'.cardinalMk_le_cRk comap_isBasis'_iff.2 ⟨hIX, hfI₀, hI₀X⟩

中文:
定理 cRk_comap_lift
  条件: (M : 拟阵 β) (f : α -> β) (X : 集合 α)
  证明: by
  nth_rw 1 [cRk, cRank, le_antisymm_iff, lift_iSup bddAbove_of_small, cRk, cRank, cRk, cRank]
  nth_rw 2 [lift_iSup bddAbove_of_small]
  simp only [ciSup_le_iff bddAbove_of_small, Subtype.forall, isBase_restrict_iff',
    comap_isBasis'_iff, and_imp]
  refine ⟨fun I hI hfI hIX => ?_, fun I hIX => ?_⟩
  · rw [← mk_image_eq_of_injOn_lift _ _ hfI, lift_le]
    exact hI.cardinalMk_le_cRk
  obtain ⟨I₀, hI₀X, rfl, hfI₀⟩ := show exists I₀ subseteq X, f '' I₀ = I ∧ InjOn f I₀ by
    obtain ⟨I₀, hI₀ss, hbij⟩ := exists_subset_bijOn (f ⁻¹' I inter X) f
    refine ⟨I₀, hI₀ss.trans inter_subset_right, ?_, hbij.injOn⟩
    rw [hbij.image_eq]; rw [image_preimage_inter]; rw [inter_eq_self_of_subset_left hIX.subset]
  rw [mk_image_eq_of_injOn_lift _ _ hfI₀]; rw [lift_le]
exact IsBasis'.cardinalMk_le_cRk comap_isBasis'_iff.2 ⟨hIX, hfI₀, hI₀X⟩
-/
@[simp] theorem cRk_comap_lift (M : Matroid β) (f : α -> β) (X : Set α) :
    lift.{v, u} ((M.comap f).cRk X) = lift (M.cRk (f '' X)) := by
  nth_rw 1 [cRk, cRank, le_antisymm_iff, lift_iSup bddAbove_of_small, cRk, cRank, cRk, cRank]
  nth_rw 2 [lift_iSup bddAbove_of_small]
  simp only [ciSup_le_iff bddAbove_of_small, Subtype.forall, isBase_restrict_iff',
    comap_isBasis'_iff, and_imp]
  refine ⟨fun I hI hfI hIX => ?_, fun I hIX => ?_⟩
  · rw [← mk_image_eq_of_injOn_lift _ _ hfI, lift_le]
    exact hI.cardinalMk_le_cRk
  obtain ⟨I₀, hI₀X, rfl, hfI₀⟩ := show exists I₀ subseteq X, f '' I₀ = I ∧ InjOn f I₀ by
    obtain ⟨I₀, hI₀ss, hbij⟩ := exists_subset_bijOn (f ⁻¹' I inter X) f
    refine ⟨I₀, hI₀ss.trans inter_subset_right, ?_, hbij.injOn⟩
    rw [hbij.image_eq]; rw [image_preimage_inter]; rw [inter_eq_self_of_subset_left hIX.subset]
  rw [mk_image_eq_of_injOn_lift _ _ hfI₀]; rw [lift_le]
exact IsBasis'.cardinalMk_le_cRk comap_isBasis'_iff.2 ⟨hIX, hfI₀, hI₀X⟩

/--
theorem `cRk_comap` / 定理 `cRk_comap`

English:
theorem cRk_comap
  given: {β : Type u} (M : Matroid β) (f : α -> β) (X : Set α)
  proof: lift_inj.1 M.cRk_comap_lift ..

中文:
定理 cRk_comap
  条件: {β : 类型u} (M : 拟阵 β) (f : α -> β) (X : 集合 α)
  证明: lift_inj.1 M.cRk_comap_lift ..
-/
@[simp] theorem cRk_comap {β : Type u} (M : Matroid β) (f : α -> β) (X : Set α) :
    (M.comap f).cRk X = M.cRk (f '' X) :=
lift_inj.1 M.cRk_comap_lift ..

end Rank

section Invariant

/-- A class stating that cardinality-valued rank is well-defined
(i.e. all bases are equicardinal) for a matroid `M` and its minors.
Notably, this holds for `Finitary` matroids; see `Matroid.invariantCardinalRank_of_finitary`. -/
@[mk_iff]
/--
Definition of `InvariantCardinalRank` / `InvariantCardinalRank` 的定义

English:
class InvariantCardinalRank
  parameters: (M : Matroid α)
  axioms and operations (1):
    - forall_card_isBasis_diff : forall ⦃I J X⦄, M.IsBasis I X -> M.IsBasis J X -> #(I \ J : Set α) = #(J \ I : Set α)

中文:
类 不变基数秩
  参数: (M : 拟阵 α)
  公理与运算 (1 个):
    - forall_card_isBasis_diff : 对任意 ⦃I J X⦄, M.是基 I X -> M.是基 J X -> #(I \ J : 集合 α) = #(J \ I : 集合 α)
-/
class InvariantCardinalRank (M : Matroid α) : Prop where
  forall_card_isBasis_diff :
    forall ⦃I J X⦄, M.IsBasis I X -> M.IsBasis J X -> #(I \ J : Set α) = #(J \ I : Set α)

variable [InvariantCardinalRank M]

/--
theorem `IsBasis.cardinalMk_sdiff_comm` / 定理 `IsBasis.cardinalMk_sdiff_comm`

English:
theorem IsBasis.cardinalMk_sdiff_comm
  given: (hIX : M.IsBasis I X) (hJX : M.IsBasis J X)
  proof: InvariantCardinalRank.forall_card_isBasis_diff hIX hJX

@[deprecated (since := "2026-06-03")]
alias IsBasis.cardinalMk_diff_comm := IsBasis.cardinalMk_sdiff_comm

中文:
定理 是基.cardinalMk_sdiff_comm
  条件: (hIX : M.是基 I X) (hJX : M.是基 J X)
  证明: InvariantCardinalRank.forall_card_isBasis_diff hIX hJX

@[deprecated (since := "2026-06-03")]
alias IsBasis.cardinalMk_diff_comm := IsBasis.cardinalMk_sdiff_comm

Depends on / 依赖: InvariantCardinalRank, InvariantCardinalRank.forall_card_isBasis_diff, forall_card_isBasis_diff
-/
theorem IsBasis.cardinalMk_sdiff_comm (hIX : M.IsBasis I X) (hJX : M.IsBasis J X) :
    #(I \ J : Set α) = #(J \ I : Set α) :=
  InvariantCardinalRank.forall_card_isBasis_diff hIX hJX

@[deprecated (since := "2026-06-03")]
alias IsBasis.cardinalMk_diff_comm := IsBasis.cardinalMk_sdiff_comm

/--
theorem `IsBasis'.cardinalMk_sdiff_comm` / 定理 `IsBasis'.cardinalMk_sdiff_comm`

English:
theorem IsBasis'.cardinalMk_sdiff_comm
  given: (hIX : M.IsBasis' I X) (hJX : M.IsBasis' J X)
  proof: hIX.isBasis_inter_ground.cardinalMk_sdiff_comm hJX.isBasis_inter_ground

@[deprecated (since := "2026-06-03")]
alias IsBasis'.cardinalMk_diff_comm := IsBasis'.cardinalMk_sdiff_comm

中文:
定理 是基'.cardinalMk_sdiff_comm
  条件: (hIX : M.是基' I X) (hJX : M.是基' J X)
  证明: hIX.isBasis_inter_ground.cardinalMk_sdiff_comm hJX.isBasis_inter_ground

@[deprecated (since := "2026-06-03")]
alias IsBasis'.cardinalMk_diff_comm := IsBasis'.cardinalMk_sdiff_comm
-/
theorem IsBasis'.cardinalMk_sdiff_comm (hIX : M.IsBasis' I X) (hJX : M.IsBasis' J X) :
    #(I \ J : Set α) = #(J \ I : Set α) :=
  hIX.isBasis_inter_ground.cardinalMk_sdiff_comm hJX.isBasis_inter_ground

@[deprecated (since := "2026-06-03")]
alias IsBasis'.cardinalMk_diff_comm := IsBasis'.cardinalMk_sdiff_comm

/--
theorem `IsBase.cardinalMk_sdiff_comm` / 定理 `IsBase.cardinalMk_sdiff_comm`

English:
theorem IsBase.cardinalMk_sdiff_comm
  given: (hB : M.IsBase B) (hB' : M.IsBase B')
  proof: hB.isBasis_ground.cardinalMk_sdiff_comm hB'.isBasis_ground

@[deprecated (since := "2026-06-03")]
alias IsBase.cardinalMk_diff_comm := IsBase.cardinalMk_sdiff_comm

中文:
定理 IsBase.cardinalMk_sdiff_comm
  条件: (hB : M.IsBase B) (hB' : M.IsBase B')
  证明: hB.isBasis_ground.cardinalMk_sdiff_comm hB'.isBasis_ground

@[deprecated (since := "2026-06-03")]
alias IsBase.cardinalMk_diff_comm := IsBase.cardinalMk_sdiff_comm

Depends on / 依赖: cardinalMk_sdiff_comm, hB.isBasis_ground.cardinalMk_sdiff_comm, isBasis_ground
-/
theorem IsBase.cardinalMk_sdiff_comm (hB : M.IsBase B) (hB' : M.IsBase B') :
    #(B \ B' : Set α) = #(B' \ B : Set α) :=
  hB.isBasis_ground.cardinalMk_sdiff_comm hB'.isBasis_ground

@[deprecated (since := "2026-06-03")]
alias IsBase.cardinalMk_diff_comm := IsBase.cardinalMk_sdiff_comm

/--
theorem `IsBasis.cardinalMk_eq` / 定理 `IsBasis.cardinalMk_eq`

English:
theorem IsBasis.cardinalMk_eq
  given: (hIX : M.IsBasis I X) (hJX : M.IsBasis J X)
  statement: #I = #J
  proof: by
  rw [← sdiff_union_inter I J]; rw [mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_right)]; rw [hIX.cardinalMk_sdiff_comm hJX]; rw [← mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_left)]; rw [inter_comm]; rw [sdiff_union_inter]

中文:
定理 是基.cardinalMk_eq
  条件: (hIX : M.是基 I X) (hJX : M.是基 J X)
  结论: #I = #J
  证明: by
  rw [← sdiff_union_inter I J]; rw [mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_right)]; rw [hIX.cardinalMk_sdiff_comm hJX]; rw [← mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_left)]; rw [inter_comm]; rw [sdiff_union_inter]

Depends on / 依赖: cardinalMk_sdiff_comm, disjoint_sdiff_left, disjoint_sdiff_left.mono_right, hIX.cardinalMk_sdiff_comm, inter_comm, inter_subset_left, inter_subset_right, mk_union_of_disjoint, mono_right, sdiff_union_inter
-/
theorem IsBasis.cardinalMk_eq (hIX : M.IsBasis I X) (hJX : M.IsBasis J X) : #I = #J := by
  rw [← sdiff_union_inter I J]; rw [mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_right)]; rw [hIX.cardinalMk_sdiff_comm hJX]; rw [← mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_left)]; rw [inter_comm]; rw [sdiff_union_inter]

/--
theorem `IsBasis'.cardinalMk_eq` / 定理 `IsBasis'.cardinalMk_eq`

English:
theorem IsBasis'.cardinalMk_eq
  given: (hIX : M.IsBasis' I X) (hJX : M.IsBasis' J X)
  statement: #I = #J
  proof: hIX.isBasis_inter_ground.cardinalMk_eq hJX.isBasis_inter_ground

中文:
定理 是基'.cardinalMk_eq
  条件: (hIX : M.是基' I X) (hJX : M.是基' J X)
  结论: #I = #J
  证明: hIX.isBasis_inter_ground.cardinalMk_eq hJX.isBasis_inter_ground
-/
theorem IsBasis'.cardinalMk_eq (hIX : M.IsBasis' I X) (hJX : M.IsBasis' J X) : #I = #J :=
  hIX.isBasis_inter_ground.cardinalMk_eq hJX.isBasis_inter_ground

/--
theorem `IsBase.cardinalMk_eq` / 定理 `IsBase.cardinalMk_eq`

English:
theorem IsBase.cardinalMk_eq
  given: (hB : M.IsBase B) (hB' : M.IsBase B')
  statement: #B = #B'
  proof: hB.isBasis_ground.cardinalMk_eq hB'.isBasis_ground

中文:
定理 IsBase.cardinalMk_eq
  条件: (hB : M.IsBase B) (hB' : M.IsBase B')
  结论: #B = #B'
  证明: hB.isBasis_ground.cardinalMk_eq hB'.isBasis_ground

Depends on / 依赖: cardinalMk_eq, hB.isBasis_ground.cardinalMk_eq, isBasis_ground
-/
theorem IsBase.cardinalMk_eq (hB : M.IsBase B) (hB' : M.IsBase B') : #B = #B' :=
  hB.isBasis_ground.cardinalMk_eq hB'.isBasis_ground

/--
theorem `Indep.cardinalMk_le_isBase` / 定理 `Indep.cardinalMk_le_isBase`

English:
theorem Indep.cardinalMk_le_isBase
  given: (hI : M.Indep I) (hB : M.IsBase B)
  statement: #I <= #B
  proof: have ⟨_B', hB', hIB'⟩ := hI.exists_isBase_superset
  hB'.cardinalMk_eq hB ▸ mk_le_mk_of_subset hIB'

中文:
定理 Indep.cardinalMk_le_isBase
  条件: (hI : M.Indep I) (hB : M.IsBase B)
  结论: #I <= #B
  证明: have ⟨_B', hB', hIB'⟩ := hI.exists_isBase_superset
  hB'.cardinalMk_eq hB ▸ mk_le_mk_of_subset hIB'

Depends on / 依赖: cardinalMk_eq, exists_isBase_superset, hI.exists_isBase_superset, mk_le_mk_of_subset
-/
theorem Indep.cardinalMk_le_isBase (hI : M.Indep I) (hB : M.IsBase B) : #I <= #B :=
  have ⟨_B', hB', hIB'⟩ := hI.exists_isBase_superset
  hB'.cardinalMk_eq hB ▸ mk_le_mk_of_subset hIB'

/--
theorem `Indep.cardinalMk_le_isBasis'` / 定理 `Indep.cardinalMk_le_isBasis'`

English:
theorem Indep.cardinalMk_le_isBasis'
  given: (hI : M.Indep I) (hJ : M.IsBasis' J X) (hIX : I subseteq X)
  proof: have ⟨_J', hJ', hIJ'⟩ := hI.subset_isBasis'_of_subset hIX
  hJ'.cardinalMk_eq hJ ▸ mk_le_mk_of_subset hIJ'

中文:
定理 Indep.cardinalMk_le_isBasis'
  条件: (hI : M.Indep I) (hJ : M.是基' J X) (hIX : I subseteq X)
  证明: have ⟨_J', hJ', hIJ'⟩ := hI.subset_isBasis'_of_subset hIX
  hJ'.cardinalMk_eq hJ ▸ mk_le_mk_of_subset hIJ'

Depends on / 依赖: _of_subset, cardinalMk_eq, hI.subset_isBasis, mk_le_mk_of_subset, subset_isBasis
-/
theorem Indep.cardinalMk_le_isBasis' (hI : M.Indep I) (hJ : M.IsBasis' J X) (hIX : I subseteq X) :
    #I <= #J :=
  have ⟨_J', hJ', hIJ'⟩ := hI.subset_isBasis'_of_subset hIX
  hJ'.cardinalMk_eq hJ ▸ mk_le_mk_of_subset hIJ'

/--
theorem `Indep.cardinalMk_le_isBasis` / 定理 `Indep.cardinalMk_le_isBasis`

English:
theorem Indep.cardinalMk_le_isBasis
  given: (hI : M.Indep I) (hJ : M.IsBasis J X) (hIX : I subseteq X)
  proof: hI.cardinalMk_le_isBasis' hJ.isBasis' hIX

中文:
定理 Indep.cardinalMk_le_isBasis
  条件: (hI : M.Indep I) (hJ : M.是基 J X) (hIX : I subseteq X)
  证明: hI.cardinalMk_le_isBasis' hJ.isBasis' hIX

Depends on / 依赖: cardinalMk_le_isBasis, hI.cardinalMk_le_isBasis, hJ.isBasis, isBasis
-/
theorem Indep.cardinalMk_le_isBasis (hI : M.Indep I) (hJ : M.IsBasis J X) (hIX : I subseteq X) :
    #I <= #J :=
  hI.cardinalMk_le_isBasis' hJ.isBasis' hIX

/--
theorem `IsBase.cardinalMk_eq_cRank` / 定理 `IsBase.cardinalMk_eq_cRank`

English:
theorem IsBase.cardinalMk_eq_cRank
  given: (hB : M.IsBase B)
  statement: #B = M.cRank
  proof: by
  have hrw : forall B' : {B : Set α // M.IsBase B}, #B' = #B := fun B' => B'.2.cardinalMk_eq hB
  simp [cRank, hrw]

中文:
定理 IsBase.cardinalMk_eq_cRank
  条件: (hB : M.IsBase B)
  结论: #B = M.cRank
  证明: by
  have hrw : forall B' : {B : Set α // M.IsBase B}, #B' = #B := fun B' => B'.2.cardinalMk_eq hB
  simp [cRank, hrw]

Depends on / 依赖: IsBase, M.IsBase, cardinalMk_eq
-/
theorem IsBase.cardinalMk_eq_cRank (hB : M.IsBase B) : #B = M.cRank := by
  have hrw : forall B' : {B : Set α // M.IsBase B}, #B' = #B := fun B' => B'.2.cardinalMk_eq hB
  simp [cRank, hrw]

/--
Instance `invariantCardinalRank_restrict` / 实例 `invariantCardinalRank_restrict`

English:
instance invariantCardinalRank_restrict
  signature: : InvariantCardinalRank (M ↾ X)
  body: by
  refine ⟨fun I J Y hI hJ => ?_⟩
  rw [isBasis_restrict_iff'] at hI hJ
  exact hI.1.cardinalMk_sdiff_comm hJ.1

中文:
实例 invariantCardinalRank_restrict
  签名: : 不变基数秩 (M ↾ X)
  定义体: by
  refine ⟨fun I J Y hI hJ => ?_⟩
  rw [isBasis_restrict_iff'] at hI hJ
  exact hI.1.cardinalMk_sdiff_comm hJ.1

Depends on / 依赖: cardinalMk_sdiff_comm, isBasis_restrict_iff
-/
instance invariantCardinalRank_restrict : InvariantCardinalRank (M ↾ X) := by
  refine ⟨fun I J Y hI hJ => ?_⟩
  rw [isBasis_restrict_iff'] at hI hJ
  exact hI.1.cardinalMk_sdiff_comm hJ.1

/--
theorem `IsBasis'.cardinalMk_eq_cRk` / 定理 `IsBasis'.cardinalMk_eq_cRk`

English:
theorem IsBasis'.cardinalMk_eq_cRk
  given: (hIX : M.IsBasis' I X)
  statement: #I = M.cRk X
  proof: by
  rw [cRk]; rw [(isBase_restrict_iff'.2 hIX).cardinalMk_eq_cRank]

中文:
定理 是基'.cardinalMk_eq_cRk
  条件: (hIX : M.是基' I X)
  结论: #I = M.cRk X
  证明: by
  rw [cRk]; rw [(isBase_restrict_iff'.2 hIX).cardinalMk_eq_cRank]
-/
theorem IsBasis'.cardinalMk_eq_cRk (hIX : M.IsBasis' I X) : #I = M.cRk X := by
  rw [cRk]; rw [(isBase_restrict_iff'.2 hIX).cardinalMk_eq_cRank]

/--
theorem `IsBasis.cardinalMk_eq_cRk` / 定理 `IsBasis.cardinalMk_eq_cRk`

English:
theorem IsBasis.cardinalMk_eq_cRk
  given: (hIX : M.IsBasis I X)
  statement: #I = M.cRk X
  proof: hIX.isBasis'.cardinalMk_eq_cRk

中文:
定理 是基.cardinalMk_eq_cRk
  条件: (hIX : M.是基 I X)
  结论: #I = M.cRk X
  证明: hIX.isBasis'.cardinalMk_eq_cRk

Depends on / 依赖: cardinalMk_eq_cRk, hIX.isBasis, isBasis
-/
theorem IsBasis.cardinalMk_eq_cRk (hIX : M.IsBasis I X) : #I = M.cRk X :=
  hIX.isBasis'.cardinalMk_eq_cRk

/--
theorem `cRk_closure` / 定理 `cRk_closure`

English:
theorem cRk_closure
  given: (M : Matroid α) [InvariantCardinalRank M] (X : Set α)
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.isBasis_closure_right.cardinalMk_eq_cRk]; rw [← hI.cardinalMk_eq_cRk]

中文:
定理 cRk_closure
  条件: (M : 拟阵 α) [不变基数秩 M] (X : 集合 α)
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.isBasis_closure_right.cardinalMk_eq_cRk]; rw [← hI.cardinalMk_eq_cRk]
-/
@[simp] theorem cRk_closure (M : Matroid α) [InvariantCardinalRank M] (X : Set α) :
    M.cRk (M.closure X) = M.cRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.isBasis_closure_right.cardinalMk_eq_cRk]; rw [← hI.cardinalMk_eq_cRk]

/--
theorem `cRk_closure_congr` / 定理 `cRk_closure_congr`

English:
theorem cRk_closure_congr
  given: (hXY : M.closure X = M.closure Y)
  statement: M.cRk X = M.cRk Y
  proof: by
  rw [← cRk_closure]; rw [hXY]; rw [cRk_closure]

中文:
定理 cRk_closure_congr
  条件: (hXY : M.closure X = M.closure Y)
  结论: M.cRk X = M.cRk Y
  证明: by
  rw [← cRk_closure]; rw [hXY]; rw [cRk_closure]

Depends on / 依赖: cRk_closure
-/
theorem cRk_closure_congr (hXY : M.closure X = M.closure Y) : M.cRk X = M.cRk Y := by
  rw [← cRk_closure]; rw [hXY]; rw [cRk_closure]

/--
theorem `Spanning.cRank_le_cardinalMk` / 定理 `Spanning.cRank_le_cardinalMk`

English:
theorem Spanning.cRank_le_cardinalMk
  given: (h : M.Spanning X)
  statement: M.cRank <= #X
  proof: have ⟨_B, hB, hBX⟩ := h.exists_isBase_subset
  (hB.cardinalMk_eq_cRank).symm.trans_le (mk_le_mk_of_subset hBX)

中文:
定理 生成.cRank_le_cardinalMk
  条件: (h : M.生成 X)
  结论: M.cRank <= #X
  证明: have ⟨_B, hB, hBX⟩ := h.exists_isBase_subset
  (hB.cardinalMk_eq_cRank).symm.trans_le (mk_le_mk_of_subset hBX)

Depends on / 依赖: cardinalMk_eq_cRank, exists_isBase_subset, h.exists_isBase_subset, hB.cardinalMk_eq_cRank, mk_le_mk_of_subset, symm.trans_le, trans_le
-/
theorem Spanning.cRank_le_cardinalMk (h : M.Spanning X) : M.cRank <= #X :=
  have ⟨_B, hB, hBX⟩ := h.exists_isBase_subset
  (hB.cardinalMk_eq_cRank).symm.trans_le (mk_le_mk_of_subset hBX)

variable (M : Matroid α) [InvariantCardinalRank M] (e : α) (X Y : Set α)

/--
theorem `cRk_union_closure_right_eq` / 定理 `cRk_union_closure_right_eq`

English:
theorem cRk_union_closure_right_eq
  statement: M.cRk (X union M.closure Y) = M.cRk (X union Y)
  proof: M.cRk_closure_congr (M.closure_union_closure_right_eq _ _)

中文:
定理 cRk_union_closure_right_eq
  结论: M.cRk (X union M.closure Y) = M.cRk (X union Y)
  证明: M.cRk_closure_congr (M.closure_union_closure_right_eq _ _)
-/
@[simp] theorem cRk_union_closure_right_eq : M.cRk (X union M.closure Y) = M.cRk (X union Y) :=
  M.cRk_closure_congr (M.closure_union_closure_right_eq _ _)

/--
theorem `cRk_union_closure_left_eq` / 定理 `cRk_union_closure_left_eq`

English:
theorem cRk_union_closure_left_eq
  statement: M.cRk (M.closure X union Y) = M.cRk (X union Y)
  proof: M.cRk_closure_congr (M.closure_union_closure_left_eq _ _)

中文:
定理 cRk_union_closure_left_eq
  结论: M.cRk (M.closure X union Y) = M.cRk (X union Y)
  证明: M.cRk_closure_congr (M.closure_union_closure_left_eq _ _)
-/
@[simp] theorem cRk_union_closure_left_eq : M.cRk (M.closure X union Y) = M.cRk (X union Y) :=
  M.cRk_closure_congr (M.closure_union_closure_left_eq _ _)

/--
theorem `cRk_insert_closure_eq` / 定理 `cRk_insert_closure_eq`

English:
theorem cRk_insert_closure_eq
  statement: M.cRk (insert e (M.closure X)) = M.cRk (insert e X)
  proof: by
  rw [← union_singleton]; rw [cRk_union_closure_left_eq]; rw [union_singleton]

中文:
定理 cRk_insert_closure_eq
  结论: M.cRk (insert e (M.closure X)) = M.cRk (insert e X)
  证明: by
  rw [← union_singleton]; rw [cRk_union_closure_left_eq]; rw [union_singleton]
-/
@[simp] theorem cRk_insert_closure_eq : M.cRk (insert e (M.closure X)) = M.cRk (insert e X) := by
  rw [← union_singleton]; rw [cRk_union_closure_left_eq]; rw [union_singleton]

/--
theorem `cRk_union_closure_eq` / 定理 `cRk_union_closure_eq`

English:
theorem cRk_union_closure_eq
  statement: M.cRk (M.closure X union M.closure Y) = M.cRk (X union Y)
  proof: by
  simp

中文:
定理 cRk_union_closure_eq
  结论: M.cRk (M.closure X union M.closure Y) = M.cRk (X union Y)
  证明: by
  simp
-/
theorem cRk_union_closure_eq : M.cRk (M.closure X union M.closure Y) = M.cRk (X union Y) := by
  simp

/--
theorem `cRk_inter_add_cRk_union_le` / 定理 `cRk_inter_add_cRk_union_le`

English:
theorem cRk_inter_add_cRk_union_le
  statement: M.cRk (X inter Y) + M.cRk (X union Y) <= M.cRk X + M.cRk Y
  proof: by
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis' (X inter Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_right)
  rw [← cRk_union_closure_eq]; rw [← hIX.closure_eq_closure]; rw [← hIY.closure_eq_closure]; rw [cRk_union_closure_eq]; rw [← hIi.cardinalMk_eq_cRk]; rw [← hIX.cardinalMk_eq_cRk]; rw [← hIY.cardinalMk_eq_cRk]; rw [← mk_union_add_mk_inter]; rw [add_comm]
  exact add_le_add (M.cRk_le_cardinalMk _) (mk_le_mk_of_subset (subset_inter hIX' hIY'))

中文:
定理 cRk_inter_add_cRk_union_le
  结论: M.cRk (X inter Y) + M.cRk (X union Y) <= M.cRk X + M.cRk Y
  证明: by
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis' (X inter Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_right)
  rw [← cRk_union_closure_eq]; rw [← hIX.closure_eq_closure]; rw [← hIY.closure_eq_closure]; rw [cRk_union_closure_eq]; rw [← hIi.cardinalMk_eq_cRk]; rw [← hIX.cardinalMk_eq_cRk]; rw [← hIY.cardinalMk_eq_cRk]; rw [← mk_union_add_mk_inter]; rw [add_comm]
  exact add_le_add (M.cRk_le_cardinalMk _) (mk_le_mk_of_subset (subset_inter hIX' hIY'))

Depends on / 依赖: M.exists_isBasis, _of_subset, add_co, cRk_union_closure_eq, cardinalMk_eq_cRk, closure_eq_closure, exists_isBasis, hIX.cardinalMk_eq_cRk, hIX.closure_eq_closure, hIY.cardinalMk_eq_cRk, hIY.closure_eq_closure, hIi.cardinalMk_eq_cRk, hIi.indep.subset_isBasis, hIi.subset.trans, inter_subset_left, inter_subset_right, mk_union_add_mk_inter, subset, subset_isBasis
-/
theorem cRk_inter_add_cRk_union_le : M.cRk (X inter Y) + M.cRk (X union Y) <= M.cRk X + M.cRk Y := by
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis' (X inter Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_right)
  rw [← cRk_union_closure_eq]; rw [← hIX.closure_eq_closure]; rw [← hIY.closure_eq_closure]; rw [cRk_union_closure_eq]; rw [← hIi.cardinalMk_eq_cRk]; rw [← hIX.cardinalMk_eq_cRk]; rw [← hIY.cardinalMk_eq_cRk]; rw [← mk_union_add_mk_inter]; rw [add_comm]
  exact add_le_add (M.cRk_le_cardinalMk _) (mk_le_mk_of_subset (subset_inter hIX' hIY'))

end Invariant

section Instances

/--
Instance `invariantCardinalRank_of_finitary` / 实例 `invariantCardinalRank_of_finitary`

English:
instance invariantCardinalRank_of_finitary
  signature: [Finitary M]
  body: by
  suffices aux : forall ⦃B B'⦄ ⦃N : Matroid α⦄, Finitary N -> N.IsBase B -> N.IsBase B' ->
      #(B \ B' : Set α) <= #(B' \ B : Set α) from
    ⟨fun I J X hI hJ => (aux (restrict_finitary X) hI.isBase_restrict hJ.isBase_restrict).antisymm
      (aux (restrict_finitary X) hJ.isBase_restrict hI.isBase_restrict)⟩
  intro B B' N hfin hB hB'
  by_cases h : (B' \ B).Finite
  · rw [← cast_ncard h, ← cast_ncard, hB.ncard_sdiff_comm hB']
    exact (hB'.sdiff_finite_comm hB).mp h
  rw [← Set.Infinite]; rw [← infinite_coe_iff] at h
  have (a : α) (ha : a in B' \ B) : exists S : Set α, Finite S ∧ S subseteq B ∧ ¬ N.Indep (insert a S) := by
    have := (hB.insert_dep ⟨hB'.subset_ground ha.1, ha.2⟩).1
    contrapose! this
    exact Finitary.indep_of_forall_finite _ fun J hJ fin => (this (J \ {a}) fin.sdiff.to_subtype <|
      sdiff_singleton_subset_iff.mpr hJ).subset (subset_insert_sdiff_singleton ..)
  choose S S_fin hSB dep using this
  let U := ⋃ a : ↥(B' \ B), S a a.2
  suffices B \ B' subseteq U by
refine (mk_le_mk_of_subset this).trans (mk_iUnion_le ..).trans
 (mul_le_max_of_aleph0_le_left (by simp)).trans ?_
    simp only [sup_le_iff, le_refl, true_and]
exact ciSup_le' fun e => (lt_aleph0_of_finite _).le.trans by simp
  rw [← sdiff_inter_self_eq_sdiff]; rw [sdiff_subset_iff]; rw [inter_comm]
  have hUB : (B inter B') union U subseteq B :=
    union_subset inter_subset_left (iUnion_subset fun e => (hSB e.1 e.2))
  by_contra hBU
  have ⟨a, ha, ind⟩ := hB.exists_insert_of_ssubset ⟨hUB, hBU⟩ hB'
  have : a in B' \ B := ⟨ha.1, fun haB => ha.2 (.inl ⟨haB, ha.1⟩)⟩
  refine dep a this (ind.subset <| insert_subset_insert <| .trans ?_ subset_union_right)
  exact subset_iUnion_of_subset ⟨a, this⟩ subset_rfl

中文:
实例 invariantCardinalRank_of_finitary
  签名: [Finitary M]
  定义体: by
  suffices aux : forall ⦃B B'⦄ ⦃N : Matroid α⦄, Finitary N -> N.IsBase B -> N.IsBase B' ->
      #(B \ B' : Set α) <= #(B' \ B : Set α) from
    ⟨fun I J X hI hJ => (aux (restrict_finitary X) hI.isBase_restrict hJ.isBase_restrict).antisymm
      (aux (restrict_finitary X) hJ.isBase_restrict hI.isBase_restrict)⟩
  intro B B' N hfin hB hB'
  by_cases h : (B' \ B).Finite
  · rw [← cast_ncard h, ← cast_ncard, hB.ncard_sdiff_comm hB']
    exact (hB'.sdiff_finite_comm hB).mp h
  rw [← Set.Infinite]; rw [← infinite_coe_iff] at h
  have (a : α) (ha : a in B' \ B) : exists S : Set α, Finite S ∧ S subseteq B ∧ ¬ N.Indep (insert a S) := by
    have := (hB.insert_dep ⟨hB'.subset_ground ha.1, ha.2⟩).1
    contrapose! this
    exact Finitary.indep_of_forall_finite _ fun J hJ fin => (this (J \ {a}) fin.sdiff.to_subtype <|
      sdiff_singleton_subset_iff.mpr hJ).subset (subset_insert_sdiff_singleton ..)
  choose S S_fin hSB dep using this
  let U := ⋃ a : ↥(B' \ B), S a a.2
  suffices B \ B' subseteq U by
refine (mk_le_mk_of_subset this).trans (mk_iUnion_le ..).trans
 (mul_le_max_of_aleph0_le_left (by simp)).trans ?_
    simp only [sup_le_iff, le_refl, true_and]
exact ciSup_le' fun e => (lt_aleph0_of_finite _).le.trans by simp
  rw [← sdiff_inter_self_eq_sdiff]; rw [sdiff_subset_iff]; rw [inter_comm]
  have hUB : (B inter B') union U subseteq B :=
    union_subset inter_subset_left (iUnion_subset fun e => (hSB e.1 e.2))
  by_contra hBU
  have ⟨a, ha, ind⟩ := hB.exists_insert_of_ssubset ⟨hUB, hBU⟩ hB'
  have : a in B' \ B := ⟨ha.1, fun haB => ha.2 (.inl ⟨haB, ha.1⟩)⟩
  refine dep a this (ind.subset <| insert_subset_insert <| .trans ?_ subset_union_right)
  exact subset_iUnion_of_subset ⟨a, this⟩ subset_rfl

Depends on / 依赖: Finitary, Finite, Infinite, IsBase, Matroid, N.IsBase, Set.Infinite, antisymm, cast_ncard, hB.ncard_sdiff_comm, hI.isBase_restrict, hJ.isBase_restrict, infinite_coe_iff, isBase_restrict, ncard_sdiff_comm, restrict_finitary, sdiff_finite_comm
-/
instance invariantCardinalRank_of_finitary [Finitary M] : InvariantCardinalRank M := by
  suffices aux : forall ⦃B B'⦄ ⦃N : Matroid α⦄, Finitary N -> N.IsBase B -> N.IsBase B' ->
      #(B \ B' : Set α) <= #(B' \ B : Set α) from
    ⟨fun I J X hI hJ => (aux (restrict_finitary X) hI.isBase_restrict hJ.isBase_restrict).antisymm
      (aux (restrict_finitary X) hJ.isBase_restrict hI.isBase_restrict)⟩
  intro B B' N hfin hB hB'
  by_cases h : (B' \ B).Finite
  · rw [← cast_ncard h, ← cast_ncard, hB.ncard_sdiff_comm hB']
    exact (hB'.sdiff_finite_comm hB).mp h
  rw [← Set.Infinite]; rw [← infinite_coe_iff] at h
  have (a : α) (ha : a in B' \ B) : exists S : Set α, Finite S ∧ S subseteq B ∧ ¬ N.Indep (insert a S) := by
    have := (hB.insert_dep ⟨hB'.subset_ground ha.1, ha.2⟩).1
    contrapose! this
    exact Finitary.indep_of_forall_finite _ fun J hJ fin => (this (J \ {a}) fin.sdiff.to_subtype <|
      sdiff_singleton_subset_iff.mpr hJ).subset (subset_insert_sdiff_singleton ..)
  choose S S_fin hSB dep using this
  let U := ⋃ a : ↥(B' \ B), S a a.2
  suffices B \ B' subseteq U by
refine (mk_le_mk_of_subset this).trans (mk_iUnion_le ..).trans
 (mul_le_max_of_aleph0_le_left (by simp)).trans ?_
    simp only [sup_le_iff, le_refl, true_and]
exact ciSup_le' fun e => (lt_aleph0_of_finite _).le.trans by simp
  rw [← sdiff_inter_self_eq_sdiff]; rw [sdiff_subset_iff]; rw [inter_comm]
  have hUB : (B inter B') union U subseteq B :=
    union_subset inter_subset_left (iUnion_subset fun e => (hSB e.1 e.2))
  by_contra hBU
  have ⟨a, ha, ind⟩ := hB.exists_insert_of_ssubset ⟨hUB, hBU⟩ hB'
  have : a in B' \ B := ⟨ha.1, fun haB => ha.2 (.inl ⟨haB, ha.1⟩)⟩
  refine dep a this (ind.subset <| insert_subset_insert <| .trans ?_ subset_union_right)
  exact subset_iUnion_of_subset ⟨a, this⟩ subset_rfl

/--
Instance `invariantCardinalRank_map` / 实例 `invariantCardinalRank_map`

English:
instance invariantCardinalRank_map
  signature: (M : Matroid α) [InvariantCardinalRank M] (hf : InjOn f M.E)
  body: by
  refine ⟨fun I J X hI hJ => ?_⟩
  obtain ⟨I, X, hIX, rfl, rfl⟩ := map_isBasis_iff'.1 hI
  obtain ⟨J, X', hJX, rfl, h'⟩ := map_isBasis_iff'.1 hJ
  obtain rfl : X = X' := by
    rwa [InjOn.image_eq_image_iff hf hIX.subset_ground hJX.subset_ground] at h'
  have hcard := hIX.cardinalMk_sdiff_comm hJX
  rwa [← lift_inj.{u, v},
    ← mk_image_eq_of_injOn_lift _ _ (hf.mono ((hIX.indep.sdiff _).subset_ground)),
    ← mk_image_eq_of_injOn_lift _ _ (hf.mono ((hJX.indep.sdiff _).subset_ground)),
    lift_inj, (hf.mono hIX.indep.subset_ground).image_sdiff,
    (hf.mono hJX.indep.subset_ground).image_sdiff, inter_comm,
    hf.image_inter hJX.indep.subset_ground hIX.indep.subset_ground,
    sdiff_inter_self_eq_sdiff, sdiff_self_inter] at hcard

中文:
实例 invariantCardinalRank_map
  签名: (M : 拟阵 α) [不变基数秩 M] (hf : 单射限制 f M.E)
  定义体: by
  refine ⟨fun I J X hI hJ => ?_⟩
  obtain ⟨I, X, hIX, rfl, rfl⟩ := map_isBasis_iff'.1 hI
  obtain ⟨J, X', hJX, rfl, h'⟩ := map_isBasis_iff'.1 hJ
  obtain rfl : X = X' := by
    rwa [InjOn.image_eq_image_iff hf hIX.subset_ground hJX.subset_ground] at h'
  have hcard := hIX.cardinalMk_sdiff_comm hJX
  rwa [← lift_inj.{u, v},
    ← mk_image_eq_of_injOn_lift _ _ (hf.mono ((hIX.indep.sdiff _).subset_ground)),
    ← mk_image_eq_of_injOn_lift _ _ (hf.mono ((hJX.indep.sdiff _).subset_ground)),
    lift_inj, (hf.mono hIX.indep.subset_ground).image_sdiff,
    (hf.mono hJX.indep.subset_ground).image_sdiff, inter_comm,
    hf.image_inter hJX.indep.subset_ground hIX.indep.subset_ground,
    sdiff_inter_self_eq_sdiff, sdiff_self_inter] at hcard

Depends on / 依赖: InjOn.image_eq_image_iff, cardinalMk_sdiff_comm, hIX.cardinalMk_sdiff_comm, hIX.indep.s, hIX.indep.sdiff, hIX.subset_ground, hJX.indep.sdiff, hJX.subset_ground, hf.mono, image_eq_image_iff, lift_inj, map_isBasis_iff, mk_image_eq_of_injOn_lift, subset_ground
-/
instance invariantCardinalRank_map (M : Matroid α) [InvariantCardinalRank M] (hf : InjOn f M.E) :
    InvariantCardinalRank (M.map f hf) := by
  refine ⟨fun I J X hI hJ => ?_⟩
  obtain ⟨I, X, hIX, rfl, rfl⟩ := map_isBasis_iff'.1 hI
  obtain ⟨J, X', hJX, rfl, h'⟩ := map_isBasis_iff'.1 hJ
  obtain rfl : X = X' := by
    rwa [InjOn.image_eq_image_iff hf hIX.subset_ground hJX.subset_ground] at h'
  have hcard := hIX.cardinalMk_sdiff_comm hJX
  rwa [← lift_inj.{u, v},
    ← mk_image_eq_of_injOn_lift _ _ (hf.mono ((hIX.indep.sdiff _).subset_ground)),
    ← mk_image_eq_of_injOn_lift _ _ (hf.mono ((hJX.indep.sdiff _).subset_ground)),
    lift_inj, (hf.mono hIX.indep.subset_ground).image_sdiff,
    (hf.mono hJX.indep.subset_ground).image_sdiff, inter_comm,
    hf.image_inter hJX.indep.subset_ground hIX.indep.subset_ground,
    sdiff_inter_self_eq_sdiff, sdiff_self_inter] at hcard

/--
Instance `invariantCardinalRank_comap` / 实例 `invariantCardinalRank_comap`

English:
instance invariantCardinalRank_comap
  signature: (M : Matroid β) [InvariantCardinalRank M] (f : α -> β)
  body: by
  refine ⟨fun I J X hI hJ => ?_⟩
  obtain ⟨hI, hfI, hIX⟩ := comap_isBasis_iff.1 hI
  obtain ⟨hJ, hfJ, hJX⟩ := comap_isBasis_iff.1 hJ
  rw [← lift_inj.{u]; rw [v}]; rw [← mk_image_eq_of_injOn_lift _ _ (hfI.mono sdiff_subset)]; rw [← mk_image_eq_of_injOn_lift _ _ (hfJ.mono sdiff_subset)]; rw [lift_inj]; rw [hfI.image_sdiff]; rw [hfJ.image_sdiff]; rw [← sdiff_union_sdiff_cancel inter_subset_left (image_inter_subset f I J)]; rw [inter_comm]; rw [sdiff_inter_self_eq_sdiff]; rw [mk_union_of_disjoint]; rw [hI.cardinalMk_sdiff_comm hJ]; rw [← sdiff_union_sdiff_cancel inter_subset_left (image_inter_subset f J I)]; rw [inter_comm]; rw [sdiff_inter_self_eq_sdiff]; rw [mk_union_of_disjoint]; rw [inter_comm J I] <;>
  exact disjoint_sdiff_left.mono_right (sdiff_subset.trans inter_subset_left)

中文:
实例 invariantCardinalRank_comap
  签名: (M : 拟阵 β) [不变基数秩 M] (f : α -> β)
  定义体: by
  refine ⟨fun I J X hI hJ => ?_⟩
  obtain ⟨hI, hfI, hIX⟩ := comap_isBasis_iff.1 hI
  obtain ⟨hJ, hfJ, hJX⟩ := comap_isBasis_iff.1 hJ
  rw [← lift_inj.{u]; rw [v}]; rw [← mk_image_eq_of_injOn_lift _ _ (hfI.mono sdiff_subset)]; rw [← mk_image_eq_of_injOn_lift _ _ (hfJ.mono sdiff_subset)]; rw [lift_inj]; rw [hfI.image_sdiff]; rw [hfJ.image_sdiff]; rw [← sdiff_union_sdiff_cancel inter_subset_left (image_inter_subset f I J)]; rw [inter_comm]; rw [sdiff_inter_self_eq_sdiff]; rw [mk_union_of_disjoint]; rw [hI.cardinalMk_sdiff_comm hJ]; rw [← sdiff_union_sdiff_cancel inter_subset_left (image_inter_subset f J I)]; rw [inter_comm]; rw [sdiff_inter_self_eq_sdiff]; rw [mk_union_of_disjoint]; rw [inter_comm J I] <;>
  exact disjoint_sdiff_left.mono_right (sdiff_subset.trans inter_subset_left)

Depends on / 依赖: comap_isBasis_iff, hfI.image_sdiff, hfI.mono, hfJ.image_sdiff, hfJ.mono, image_inter_subset, image_sdiff, inter_comm, inter_subset_left, lift_inj, mk_image_eq_of_injOn_lift, mk_union_of_disjoint, sdiff_inter_self_eq_sdiff, sdiff_subset, sdiff_union_sdiff_cancel
-/
instance invariantCardinalRank_comap (M : Matroid β) [InvariantCardinalRank M] (f : α -> β) :
    InvariantCardinalRank (M.comap f) := by
  refine ⟨fun I J X hI hJ => ?_⟩
  obtain ⟨hI, hfI, hIX⟩ := comap_isBasis_iff.1 hI
  obtain ⟨hJ, hfJ, hJX⟩ := comap_isBasis_iff.1 hJ
  rw [← lift_inj.{u]; rw [v}]; rw [← mk_image_eq_of_injOn_lift _ _ (hfI.mono sdiff_subset)]; rw [← mk_image_eq_of_injOn_lift _ _ (hfJ.mono sdiff_subset)]; rw [lift_inj]; rw [hfI.image_sdiff]; rw [hfJ.image_sdiff]; rw [← sdiff_union_sdiff_cancel inter_subset_left (image_inter_subset f I J)]; rw [inter_comm]; rw [sdiff_inter_self_eq_sdiff]; rw [mk_union_of_disjoint]; rw [hI.cardinalMk_sdiff_comm hJ]; rw [← sdiff_union_sdiff_cancel inter_subset_left (image_inter_subset f J I)]; rw [inter_comm]; rw [sdiff_inter_self_eq_sdiff]; rw [mk_union_of_disjoint]; rw [inter_comm J I] <;>
  exact disjoint_sdiff_left.mono_right (sdiff_subset.trans inter_subset_left)

end Instances

/--
theorem `rankFinite_iff_cRank_lt_aleph0` / 定理 `rankFinite_iff_cRank_lt_aleph0`

English:
theorem rankFinite_iff_cRank_lt_aleph0
  statement: M.RankFinite ↔ M.cRank < ℵ₀
  proof: by
  refine ⟨fun h => ?_, fun h => ⟨?_⟩⟩
  · have ⟨B, hB, fin⟩ := h
    exact hB.cardinalMk_eq_cRank ▸ lt_aleph0_iff_finite.mpr fin
  have ⟨B, hB⟩ := M.exists_isBase
  simp_rw [← finite_coe_iff, ← lt_aleph0_iff_finite]
  exact ⟨B, hB, hB.cardinalMk_le_cRank.trans_lt h⟩

中文:
定理 rankFinite_iff_cRank_lt_aleph0
  结论: M.RankFinite ↔ M.cRank < ℵ₀
  证明: by
  refine ⟨fun h => ?_, fun h => ⟨?_⟩⟩
  · have ⟨B, hB, fin⟩ := h
    exact hB.cardinalMk_eq_cRank ▸ lt_aleph0_iff_finite.mpr fin
  have ⟨B, hB⟩ := M.exists_isBase
  simp_rw [← finite_coe_iff, ← lt_aleph0_iff_finite]
  exact ⟨B, hB, hB.cardinalMk_le_cRank.trans_lt h⟩

Depends on / 依赖: M.exists_isBase, cardinalMk_eq_cRank, cardinalMk_le_cRank, exists_isBase, finite_coe_iff, hB.cardinalMk_eq_cRank, hB.cardinalMk_le_cRank.trans_lt, lt_aleph0_iff_finite, lt_aleph0_iff_finite.mpr, simp_rw, trans_lt
-/
theorem rankFinite_iff_cRank_lt_aleph0 : M.RankFinite ↔ M.cRank < ℵ₀ := by
  refine ⟨fun h => ?_, fun h => ⟨?_⟩⟩
  · have ⟨B, hB, fin⟩ := h
    exact hB.cardinalMk_eq_cRank ▸ lt_aleph0_iff_finite.mpr fin
  have ⟨B, hB⟩ := M.exists_isBase
  simp_rw [← finite_coe_iff, ← lt_aleph0_iff_finite]
  exact ⟨B, hB, hB.cardinalMk_le_cRank.trans_lt h⟩

/--
theorem `rankInfinite_iff_aleph0_le_cRank` / 定理 `rankInfinite_iff_aleph0_le_cRank`

English:
theorem rankInfinite_iff_aleph0_le_cRank
  statement: M.RankInfinite ↔ ℵ₀ <= M.cRank
  proof: by
  rw [← not_lt]; rw [← rankFinite_iff_cRank_lt_aleph0]; rw [not_rankFinite_iff]

中文:
定理 rankInfinite_iff_aleph0_le_cRank
  结论: M.RankInfinite ↔ ℵ₀ <= M.cRank
  证明: by
  rw [← not_lt]; rw [← rankFinite_iff_cRank_lt_aleph0]; rw [not_rankFinite_iff]

Depends on / 依赖: not_lt, not_rankFinite_iff, rankFinite_iff_cRank_lt_aleph0
-/
theorem rankInfinite_iff_aleph0_le_cRank : M.RankInfinite ↔ ℵ₀ <= M.cRank := by
  rw [← not_lt]; rw [← rankFinite_iff_cRank_lt_aleph0]; rw [not_rankFinite_iff]

/--
theorem `isRkFinite_iff_cRk_lt_aleph0` / 定理 `isRkFinite_iff_cRk_lt_aleph0`

English:
theorem isRkFinite_iff_cRk_lt_aleph0
  statement: M.IsRkFinite X ↔ M.cRk X < ℵ₀
  proof: by
  rw [IsRkFinite]; rw [rankFinite_iff_cRank_lt_aleph0]; rw [cRank_restrict]

中文:
定理 isRkFinite_iff_cRk_lt_aleph0
  结论: M.IsRkFinite X ↔ M.cRk X < ℵ₀
  证明: by
  rw [IsRkFinite]; rw [rankFinite_iff_cRank_lt_aleph0]; rw [cRank_restrict]

Depends on / 依赖: IsRkFinite, cRank_restrict, rankFinite_iff_cRank_lt_aleph0
-/
theorem isRkFinite_iff_cRk_lt_aleph0 : M.IsRkFinite X ↔ M.cRk X < ℵ₀ := by
  rw [IsRkFinite]; rw [rankFinite_iff_cRank_lt_aleph0]; rw [cRank_restrict]

/--
theorem `Indep.isBase_of_cRank_le` / 定理 `Indep.isBase_of_cRank_le`

English:
theorem Indep.isBase_of_cRank_le
  given: [M.RankFinite] (ind : M.Indep I) (le : M.cRank <= #I)
  proof: ind.isBase_of_maximal fun _J ind_J hIJ => ind.finite.eq_of_subset_of_encard_le hIJ
toENat.monotone' ind_J.cardinalMk_le_cRank.trans le

中文:
定理 Indep.isBase_of_cRank_le
  条件: [M.RankFinite] (ind : M.Indep I) (le : M.cRank <= #I)
  证明: ind.isBase_of_maximal fun _J ind_J hIJ => ind.finite.eq_of_subset_of_encard_le hIJ
toENat.monotone' ind_J.cardinalMk_le_cRank.trans le

Depends on / 依赖: cardinalMk_le_cRank, eq_of_subset_of_encard_le, finite, ind.finite.eq_of_subset_of_encard_le, ind.isBase_of_maximal, ind_J, ind_J.cardinalMk_le_cRank.trans, isBase_of_maximal, monotone, toENat, toENat.monotone
-/
theorem Indep.isBase_of_cRank_le [M.RankFinite] (ind : M.Indep I) (le : M.cRank <= #I) :
    M.IsBase I :=
ind.isBase_of_maximal fun _J ind_J hIJ => ind.finite.eq_of_subset_of_encard_le hIJ
toENat.monotone' ind_J.cardinalMk_le_cRank.trans le

/--
theorem `Spanning.isBase_of_le_cRank` / 定理 `Spanning.isBase_of_le_cRank`

English:
theorem Spanning.isBase_of_le_cRank
  given: [M.RankFinite] (h : M.Spanning X) (le : #X <= M.cRank)
  proof: by
  have ⟨B, hB, hBX⟩ := h.exists_isBase_subset
  rwa [← hB.finite.eq_of_subset_of_encard_le hBX
    (toENat.monotone' <| le.trans hB.cardinalMk_eq_cRank.ge)]

中文:
定理 生成.isBase_of_le_cRank
  条件: [M.RankFinite] (h : M.生成 X) (le : #X <= M.cRank)
  证明: by
  have ⟨B, hB, hBX⟩ := h.exists_isBase_subset
  rwa [← hB.finite.eq_of_subset_of_encard_le hBX
    (toENat.monotone' <| le.trans hB.cardinalMk_eq_cRank.ge)]

Depends on / 依赖: cardinalMk_eq_cRank, eq_of_subset_of_encard_le, exists_isBase_subset, finite, h.exists_isBase_subset, hB.cardinalMk_eq_cRank.ge, hB.finite.eq_of_subset_of_encard_le, le.trans, monotone, toENat, toENat.monotone
-/
theorem Spanning.isBase_of_le_cRank [M.RankFinite] (h : M.Spanning X) (le : #X <= M.cRank) :
    M.IsBase X := by
  have ⟨B, hB, hBX⟩ := h.exists_isBase_subset
  rwa [← hB.finite.eq_of_subset_of_encard_le hBX
    (toENat.monotone' <| le.trans hB.cardinalMk_eq_cRank.ge)]

/--
theorem `Indep.isBase_of_cRank_le_of_finite` / 定理 `Indep.isBase_of_cRank_le_of_finite`

English:
theorem Indep.isBase_of_cRank_le_of_finite
  statement: (ind : M.Indep I)
  proof: have := rankFinite_iff_cRank_lt_aleph0.mpr (le.trans_lt <| lt_aleph0_iff_finite.mpr fin)
  ind.isBase_of_cRank_le le

中文:
定理 Indep.isBase_of_cRank_le_of_finite
  结论: (ind : M.Indep I)
  证明: have := rankFinite_iff_cRank_lt_aleph0.mpr (le.trans_lt <| lt_aleph0_iff_finite.mpr fin)
  ind.isBase_of_cRank_le le

Depends on / 依赖: ind.isBase_of_cRank_le, isBase_of_cRank_le, le.trans_lt, lt_aleph0_iff_finite, lt_aleph0_iff_finite.mpr, rankFinite_iff_cRank_lt_aleph0, rankFinite_iff_cRank_lt_aleph0.mpr, trans_lt
-/
theorem Indep.isBase_of_cRank_le_of_finite (ind : M.Indep I)
    (le : M.cRank <= #I) (fin : I.Finite) : M.IsBase I :=
  have := rankFinite_iff_cRank_lt_aleph0.mpr (le.trans_lt <| lt_aleph0_iff_finite.mpr fin)
  ind.isBase_of_cRank_le le

/--
theorem `Spanning.isBase_of_le_cRank_of_finite` / 定理 `Spanning.isBase_of_le_cRank_of_finite`

English:
theorem Spanning.isBase_of_le_cRank_of_finite
  statement: (h : M.Spanning X)
  proof: have ⟨_B, hB, hBX⟩ := h.exists_isBase_subset
  have := hB.rankFinite_of_finite (fin.subset hBX)
  h.isBase_of_le_cRank le

@[simp]

中文:
定理 生成.isBase_of_le_cRank_of_finite
  结论: (h : M.生成 X)
  证明: have ⟨_B, hB, hBX⟩ := h.exists_isBase_subset
  have := hB.rankFinite_of_finite (fin.subset hBX)
  h.isBase_of_le_cRank le

@[simp]

Depends on / 依赖: exists_isBase_subset, fin.subset, h.exists_isBase_subset, h.isBase_of_le_cRank, hB.rankFinite_of_finite, isBase_of_le_cRank, rankFinite_of_finite, subset
-/
theorem Spanning.isBase_of_le_cRank_of_finite (h : M.Spanning X)
    (le : #X <= M.cRank) (fin : X.Finite) : M.IsBase X :=
  have ⟨_B, hB, hBX⟩ := h.exists_isBase_subset
  have := hB.rankFinite_of_finite (fin.subset hBX)
  h.isBase_of_le_cRank le

@[simp]
/--
theorem `toENat_cRank_eq` / 定理 `toENat_cRank_eq`

English:
theorem toENat_cRank_eq
  given: (M : Matroid α)
  statement: M.cRank.toENat = M.eRank
  proof: by
  obtain h | h := M.rankFinite_or_rankInfinite
  · obtain ⟨B, hB⟩ := M.exists_isBase
    rw [← hB.cardinalMk_eq_cRank]; rw [← hB.encard_eq_eRank]; rw [toENat_cardinalMk]
  simp [rankInfinite_iff_aleph0_le_cRank.1 h]

@[simp]

中文:
定理 toE自然数_cRank_eq
  条件: (M : 拟阵 α)
  结论: M.cRank.toE自然数 = M.eRank
  证明: by
  obtain h | h := M.rankFinite_or_rankInfinite
  · obtain ⟨B, hB⟩ := M.exists_isBase
    rw [← hB.cardinalMk_eq_cRank]; rw [← hB.encard_eq_eRank]; rw [toENat_cardinalMk]
  simp [rankInfinite_iff_aleph0_le_cRank.1 h]

@[simp]

Depends on / 依赖: M.exists_isBase, M.rankFinite_or_rankInfinite, cardinalMk_eq_cRank, encard_eq_eRank, exists_isBase, hB.cardinalMk_eq_cRank, hB.encard_eq_eRank, rankFinite_or_rankInfinite, rankInfinite_iff_aleph0_le_cRank, toENat_cardinalMk
-/
theorem toENat_cRank_eq (M : Matroid α) : M.cRank.toENat = M.eRank := by
  obtain h | h := M.rankFinite_or_rankInfinite
  · obtain ⟨B, hB⟩ := M.exists_isBase
    rw [← hB.cardinalMk_eq_cRank]; rw [← hB.encard_eq_eRank]; rw [toENat_cardinalMk]
  simp [rankInfinite_iff_aleph0_le_cRank.1 h]

@[simp]
/--
theorem `toENat_cRk_eq` / 定理 `toENat_cRk_eq`

English:
theorem toENat_cRk_eq
  given: (M : Matroid α) (X : Set α)
  statement: (M.cRk X).toENat = M.eRk X
  proof: by
  rw [cRk]; rw [toENat_cRank_eq]; rw [eRk]

中文:
定理 toE自然数_cRk_eq
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: (M.cRk X).toE自然数 = M.eRk X
  证明: by
  rw [cRk]; rw [toENat_cRank_eq]; rw [eRk]

Depends on / 依赖: toENat_cRank_eq
-/
theorem toENat_cRk_eq (M : Matroid α) (X : Set α) : (M.cRk X).toENat = M.eRk X := by
  rw [cRk]; rw [toENat_cRank_eq]; rw [eRk]

end Matroid
