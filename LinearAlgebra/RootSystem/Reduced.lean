/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-!
# Reduced root pairings

This file contains basic definitions and results related to reduced root pairings.

## Main definitions:

* `RootPairing.IsReduced`: A root pairing is said to be reduced if two linearly dependent roots are
  always related by a sign.
* `RootPairing.linearIndependent_iff_coxeterWeight_ne_four`: for a finite root pairing, two
  roots are linearly independent iff their Coxeter weight is not four.

## Implementation details:

For convenience we provide two versions of many lemmas, according to whether we know that the root
pairing is valued in a smaller ring (in the sense of `RootPairing.IsValuedIn`). For example we
provide both `RootPairing.linearIndependent_iff_coxeterWeight_ne_four` and
`RootPairing.linearIndependent_iff_coxeterWeightIn_ne_four`.

Several ways to avoid this duplication exist. We leave explorations of this for future work. One
possible solution is to drop `RootPairing.pairing` and `RootPairing.coxeterWeight` entirely and rely
solely on `RootPairing.pairingIn` and `RootPairing.coxeterWeightIn`.

-/

public section

open Module Set Function

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (S : Type*) {i j : ι}

namespace RootPairing

/--
Definition of `IsReduced` / `IsReduced` 的定义

English:
class IsReduced
  parameters: : Prop where
  axioms and operations (1):
    - eq_or_eq_neg((i j : ι) (h : ¬ LinearIndependent R ![P.root i, P.root j])) : P.root i = P.root j ∨ P.root i = - P.root j

中文:
类 是既约
  参数: : 命题 where
  公理与运算 (1 个):
    - eq_or_eq_neg((i j : ι) (h : ¬ LinearIndependent R ![P.root i, P.root j])) : P.root i = P.root j ∨ P.root i = - P.root j
-/
@[mk_iff] class IsReduced : Prop where
  eq_or_eq_neg (i j : ι) (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.root i = P.root j ∨ P.root i = - P.root j

/--
lemma `isReduced_iff'` / 引理 `isReduced_iff'`

English:
lemma isReduced_iff'
  statement: P.IsReduced ↔ forall i j : ι, i != j ->
  proof: by
  rw [isReduced_iff]
  refine ⟨fun h i j hij hLin => ?_, fun h i j hLin => ?_⟩
  · specialize h i j hLin
    simp_all
  · rcases eq_or_ne i j with rfl | h'
    · tauto
    · exact Or.inr (h i j h' hLin)

中文:
引理 isReduced_iff'
  结论: P.是既约 ↔ 对任意 i j : ι, i != j ->
  证明: by
  rw [isReduced_iff]
  refine ⟨fun h i j hij hLin => ?_, fun h i j hLin => ?_⟩
  · specialize h i j hLin
    simp_all
  · rcases eq_or_ne i j with rfl | h'
    · tauto
    · exact Or.inr (h i j h' hLin)

Depends on / 依赖: Or.inr, eq_or_ne, isReduced_iff, specialize
-/
lemma isReduced_iff' : P.IsReduced ↔ forall i j : ι, i != j ->
    ¬ LinearIndependent R ![P.root i, P.root j] -> P.root i = - P.root j := by
  rw [isReduced_iff]
  refine ⟨fun h i j hij hLin => ?_, fun h i j hLin => ?_⟩
  · specialize h i j hLin
    simp_all
  · rcases eq_or_ne i j with rfl | h'
    · tauto
    · exact Or.inr (h i j h' hLin)

/--
lemma `IsReduced.linearIndependent` / 引理 `IsReduced.linearIndependent`

English:
lemma IsReduced.linearIndependent
  given: [P.IsReduced] (h : i != j) (h' : P.root i != -P.root j)
  proof: by
  have := IsReduced.eq_or_eq_neg (P := P) i j
  simp_all

中文:
引理 是既约.linearIndependent
  条件: [P.是既约] (h : i != j) (h' : P.root i != -P.root j)
  证明: by
  have := IsReduced.eq_or_eq_neg (P := P) i j
  simp_all

Depends on / 依赖: IsReduced, IsReduced.eq_or_eq_neg, eq_or_eq_neg
-/
lemma IsReduced.linearIndependent [P.IsReduced] (h : i != j) (h' : P.root i != -P.root j) :
    LinearIndependent R ![P.root i, P.root j] := by
  have := IsReduced.eq_or_eq_neg (P := P) i j
  simp_all

/--
lemma `IsReduced.linearIndependent_iff` / 引理 `IsReduced.linearIndependent_iff`

English:
lemma IsReduced.linearIndependent_iff
  given: [Nontrivial R] [P.IsReduced]
  proof: by
  refine ⟨fun h => ?_, fun ⟨h, h'⟩ => linearIndependent P h h'⟩
  rw [LinearIndependent.pair_iff] at h
  contrapose! h
  rcases eq_or_ne i j with rfl | h'
  · exact ⟨1, -1, by simp⟩
  · rw [h h']
    exact ⟨1, 1, by simp⟩

中文:
引理 是既约.linearIndependent_iff
  条件: [非平凡 R] [P.是既约]
  证明: by
  refine ⟨fun h => ?_, fun ⟨h, h'⟩ => linearIndependent P h h'⟩
  rw [LinearIndependent.pair_iff] at h
  contrapose! h
  rcases eq_or_ne i j with rfl | h'
  · exact ⟨1, -1, by simp⟩
  · rw [h h']
    exact ⟨1, 1, by simp⟩

Depends on / 依赖: LinearIndependent, LinearIndependent.pair_iff, contrapose, eq_or_ne, linearIndependent, pair_iff
-/
lemma IsReduced.linearIndependent_iff [Nontrivial R] [P.IsReduced] :
    LinearIndependent R ![P.root i, P.root j] ↔ i != j ∧ P.root i != - P.root j := by
  refine ⟨fun h => ?_, fun ⟨h, h'⟩ => linearIndependent P h h'⟩
  rw [LinearIndependent.pair_iff] at h
  contrapose! h
  rcases eq_or_ne i j with rfl | h'
  · exact ⟨1, -1, by simp⟩
  · rw [h h']
    exact ⟨1, 1, by simp⟩

/--
lemma `nsmul_notMem_range_root` / 引理 `nsmul_notMem_range_root`

English:
lemma nsmul_notMem_range_root
  statement: [CharZero R] [IsAddTorsionFree M] [P.IsReduced]
  proof: by
  have : ¬ LinearIndependent R ![n • P.root i, P.root i] := by
    simpa only [LinearIndependent.pair_iff, not_forall] using
      ⟨1, -(n : R), by simp [Nat.cast_smul_eq_nsmul], by simp⟩
  rintro ⟨j, hj⟩
  replace this : j = i ∨ P.root j = -P.root i := by
    simpa only [← hj, IsReduced.linearIn

中文:
引理 nsmul_notMem_range_root
  结论: [特征零 R] [是加法无挠 M] [P.是既约]
  证明: by
  have : ¬ LinearIndependent R ![n • P.root i, P.root i] := by
    simpa only [LinearIndependent.pair_iff, not_forall] using
      ⟨1, -(n : R), by simp [Nat.cast_smul_eq_nsmul], by simp⟩
  rintro ⟨j, hj⟩
  replace this : j = i ∨ P.root j = -P.root i := by
    simpa only [← hj, IsReduced.linearIn

Depends on / 依赖: IsReduced, IsReduced.linearIndependent_iff, LinearIndependent, LinearIndependent.pair_iff, Nat.cast_smul_eq_nsmul, P.ne_zero, P.root, cast_smul_eq_nsmul, eq_comm, eq_iff, linearIndependent_iff, ne_zero, not_and_or, not_forall, not_not, pair_iff, replace, smul_left_injective
-/
lemma nsmul_notMem_range_root [CharZero R] [IsAddTorsionFree M] [P.IsReduced]
    {n : Nat} [n.AtLeastTwo] {i : ι} :
    n • P.root i ∉ range P.root := by
  have : ¬ LinearIndependent R ![n • P.root i, P.root i] := by
    simpa only [LinearIndependent.pair_iff, not_forall] using
      ⟨1, -(n : R), by simp [Nat.cast_smul_eq_nsmul], by simp⟩
  rintro ⟨j, hj⟩
  replace this : j = i ∨ P.root j = -P.root i := by
    simpa only [← hj, IsReduced.linearIndependent_iff, not_and_or, not_not] using this
  rcases this with rfl | this
  · replace hj : (1 : Int) • P.root j = (n : Int) • P.root j := by simpa
    rw [(smul_left_injective Int <| P.ne_zero j).eq_iff]; rw [eq_comm] at hj
    have : 2 <= n := Nat.AtLeastTwo.prop
    lia
  · rw [← one_smul Int (P.root i), ← neg_smul, hj] at this
    replace this : (n : Int) • P.root i = -1 • P.root i := by simpa
    rw [(smul_left_injective Int <| P.ne_zero i).eq_iff] at this
    lia

/--
lemma `linearIndependent_of_add_mem_range_root` / 引理 `linearIndependent_of_add_mem_range_root`

English:
lemma linearIndependent_of_add_mem_range_root
  proof: by
  refine IsReduced.linearIndependent P (fun hij => ?_) (fun hij => P.zero_notMem_range_root ?_)
  · rw [hij, ← two_smul (R := Nat)] at h
    exact P.nsmul_notMem_range_root h
  · rwa [hij, neg_add_cancel] at h

中文:
引理 linearIndependent_of_add_mem_range_root
  证明: by
  refine IsReduced.linearIndependent P (fun hij => ?_) (fun hij => P.zero_notMem_range_root ?_)
  · rw [hij, ← two_smul (R := Nat)] at h
    exact P.nsmul_notMem_range_root h
  · rwa [hij, neg_add_cancel] at h

Depends on / 依赖: IsReduced, IsReduced.linearIndependent, P.nsmul_notMem_range_root, P.zero_notMem_range_root, linearIndependent, neg_add_cancel, nsmul_notMem_range_root, two_smul, zero_notMem_range_root
-/
lemma linearIndependent_of_add_mem_range_root
    [CharZero R] [IsAddTorsionFree M] [P.IsReduced] {i j : ι}
    (h : P.root i + P.root j in range P.root) :
    LinearIndependent R ![P.root i, P.root j] := by
  refine IsReduced.linearIndependent P (fun hij => ?_) (fun hij => P.zero_notMem_range_root ?_)
  · rw [hij, ← two_smul (R := Nat)] at h
    exact P.nsmul_notMem_range_root h
  · rwa [hij, neg_add_cancel] at h

/--
lemma `linearIndependent_of_sub_mem_range_root` / 引理 `linearIndependent_of_sub_mem_range_root`

English:
lemma linearIndependent_of_sub_mem_range_root
  proof: by
  suffices LinearIndependent R ![P.root i, P.root (P.reflectionPerm j j)] by simpa using this
  apply P.linearIndependent_of_add_mem_range_root
  simpa [sub_eq_add_neg] using h

中文:
引理 linearIndependent_of_sub_mem_range_root
  证明: by
  suffices LinearIndependent R ![P.root i, P.root (P.reflectionPerm j j)] by simpa using this
  apply P.linearIndependent_of_add_mem_range_root
  simpa [sub_eq_add_neg] using h

Depends on / 依赖: LinearIndependent, P.linearIndependent_of_add_mem_range_root, P.reflectionPerm, P.root, linearIndependent_of_add_mem_range_root, reflectionPerm, sub_eq_add_neg
-/
lemma linearIndependent_of_sub_mem_range_root
    [CharZero R] [IsAddTorsionFree M] [P.IsReduced] {i j : ι}
    (h : P.root i - P.root j in range P.root) :
    LinearIndependent R ![P.root i, P.root j] := by
  suffices LinearIndependent R ![P.root i, P.root (P.reflectionPerm j j)] by simpa using this
  apply P.linearIndependent_of_add_mem_range_root
  simpa [sub_eq_add_neg] using h

/--
lemma `linearIndependent_of_add_mem_range_root'` / 引理 `linearIndependent_of_add_mem_range_root'`

English:
lemma linearIndependent_of_add_mem_range_root'
  statement: [CharZero R] [IsDomain R] [P.IsReduced] {i j : ι}
  proof: have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  P.linearIndependent_of_add_mem_range_root h

中文:
引理 linearIndependent_of_add_mem_range_root'
  结论: [特征零 R] [是整环 R] [P.是既约] {i j : ι}
  证明: have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  P.linearIndependent_of_add_mem_range_root h

Depends on / 依赖: IsAddTorsionFree, IsReflexive, P.linearIndependent_of_add_mem_range_root, P.toLinearMap, linearIndependent_of_add_mem_range_root, of_isPerfPair, of_isTorsionFree, toLinearMap
-/
lemma linearIndependent_of_add_mem_range_root' [CharZero R] [IsDomain R] [P.IsReduced] {i j : ι}
    (h : P.root i + P.root j in range P.root) :
    LinearIndependent R ![P.root i, P.root j] :=
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  P.linearIndependent_of_add_mem_range_root h

/--
lemma `linearIndependent_of_sub_mem_range_root'` / 引理 `linearIndependent_of_sub_mem_range_root'`

English:
lemma linearIndependent_of_sub_mem_range_root'
  statement: [CharZero R] [IsDomain R] [P.IsReduced] {i j : ι}
  proof: have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  P.linearIndependent_of_sub_mem_range_root h

中文:
引理 linearIndependent_of_sub_mem_range_root'
  结论: [特征零 R] [是整环 R] [P.是既约] {i j : ι}
  证明: have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  P.linearIndependent_of_sub_mem_range_root h

Depends on / 依赖: IsAddTorsionFree, IsReflexive, P.linearIndependent_of_sub_mem_range_root, P.toLinearMap, linearIndependent_of_sub_mem_range_root, of_isPerfPair, of_isTorsionFree, toLinearMap
-/
lemma linearIndependent_of_sub_mem_range_root' [CharZero R] [IsDomain R] [P.IsReduced] {i j : ι}
    (h : P.root i - P.root j in range P.root) :
    LinearIndependent R ![P.root i, P.root j] :=
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  P.linearIndependent_of_sub_mem_range_root h

/--
lemma `infinite_of_linearIndependent_coxeterWeight_four` / 引理 `infinite_of_linearIndependent_coxeterWeight_four`

English:
lemma infinite_of_linearIndependent_coxeterWeight_four
  statement: [NeZero (2 : R)] [IsAddTorsionFree M]
  proof: by
  refine (infinite_range_iff (Embedding.injective P.root)).mp (Infinite.mono ?_
    ((infinite_range_reflection_reflection_iterate_iff (P.coroot_root_two i)
    (P.coroot_root_two j) ?_).mpr ?_))
  · rw [range_subset_iff]
    intro n
    rw [← IsFixedPt.image_iterate ((bijOn_reflection_of_mapsTo 

中文:
引理 infinite_of_linearIndependent_coxeterWeight_four
  结论: [NeZero (2 : R)] [是加法无挠 M]
  证明: by
  refine (infinite_range_iff (Embedding.injective P.root)).mp (Infinite.mono ?_
    ((infinite_range_reflection_reflection_iterate_iff (P.coroot_root_two i)
    (P.coroot_root_two j) ?_).mpr ?_))
  · rw [range_subset_iff]
    intro n
    rw [← IsFixedPt.image_iterate ((bijOn_reflection_of_mapsTo 

Depends on / 依赖: Embedding, Embedding.injective, Infinite, Infinite.mono, IsFixedPt, IsFixedPt.image_iterate, P.coroot_root_two, P.mapsTo_reflection_root, P.root, bijOn_reflection_of_mapsTo, coroot_root_eq_pairi, coroot_root_two, image_eq, image_iterate, infinite_range_iff, infinite_range_reflection_reflection_iterate_iff, injective, mapsTo_reflection_root, mem_image_of_mem, mem_range_self
-/
lemma infinite_of_linearIndependent_coxeterWeight_four [NeZero (2 : R)] [IsAddTorsionFree M]
    (hl : LinearIndependent R ![P.root i, P.root j]) (hc : P.coxeterWeight i j = 4) :
    Infinite ι := by
  refine (infinite_range_iff (Embedding.injective P.root)).mp (Infinite.mono ?_
    ((infinite_range_reflection_reflection_iterate_iff (P.coroot_root_two i)
    (P.coroot_root_two j) ?_).mpr ?_))
  · rw [range_subset_iff]
    intro n
    rw [← IsFixedPt.image_iterate ((bijOn_reflection_of_mapsTo (P.coroot_root_two i)
      (P.mapsTo_reflection_root i)).comp (bijOn_reflection_of_mapsTo (P.coroot_root_two j)
      (P.mapsTo_reflection_root j))).image_eq n]
    exact mem_image_of_mem _ (mem_range_self j)
  · rw [coroot_root_eq_pairing, coroot_root_eq_pairing, ← hc, mul_comm, coxeterWeight]
  · rw [LinearIndependent.pair_iff] at hl
    specialize hl (P.pairing j i) (-2)
    simp only [neg_smul, neg_eq_zero, two_ne_zero (α := R), and_false, imp_false] at hl
    rw [ne_eq]; rw [coroot_root_eq_pairing]; rw [← sub_eq_zero]; rw [sub_eq_add_neg]
    exact hl

/--
lemma `pairing_smul_root_eq_of_not_linearIndependent` / 引理 `pairing_smul_root_eq_of_not_linearIndependent`

English:
lemma pairing_smul_root_eq_of_not_linearIndependent
  statement: [NeZero (2 : R)] [IsDomain R]
  proof: by
  rw [LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨s, t, h₁, h₂⟩ := h
  replace h₂ : s != 0 := by
    rcases eq_or_ne s 0 with rfl | hs
· exact False.elim h₂ rfl (smul_eq_zero_iff_left <| P.ne_zero j).mp by simpa using h₁
    · assumption
  have h₃ : t != 0 := by
    rcases eq_or_ne

中文:
引理 pairing_smul_root_eq_of_not_linearIndependent
  结论: [NeZero (2 : R)] [是整环 R]
  证明: by
  rw [LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨s, t, h₁, h₂⟩ := h
  replace h₂ : s != 0 := by
    rcases eq_or_ne s 0 with rfl | hs
· exact False.elim h₂ rfl (smul_eq_zero_iff_left <| P.ne_zero j).mp by simpa using h₁
    · assumption
  have h₃ : t != 0 := by
    rcases eq_or_ne

Depends on / 依赖: False.elim, LinearIndependent, LinearIndependent.pair_iff, P.ne_zero, P.root, eq_neg_iff_add_eq_zero, eq_or_ne, ne_zero, neg_smul, pair_iff, replace, smul_eq_zero_iff_left
-/
lemma pairing_smul_root_eq_of_not_linearIndependent [NeZero (2 : R)] [IsDomain R]
    [Module.IsTorsionFree R M] (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.pairing j i • P.root i = (2 : R) • P.root j := by
  rw [LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨s, t, h₁, h₂⟩ := h
  replace h₂ : s != 0 := by
    rcases eq_or_ne s 0 with rfl | hs
· exact False.elim h₂ rfl (smul_eq_zero_iff_left <| P.ne_zero j).mp by simpa using h₁
    · assumption
  have h₃ : t != 0 := by
    rcases eq_or_ne t 0 with rfl | ht
· exact False.elim h₂ (smul_eq_zero_iff_left <| P.ne_zero i).mp by simpa using h₁
    · assumption
  replace h₁ : s • P.root i = -t • P.root j := by rwa [← eq_neg_iff_add_eq_zero, ← neg_smul] at h₁
  have h₄ : s * 2 = -(t * P.pairing j i) := by simpa using congr_arg (P.coroot' i) h₁
  replace h₁ : (2 : R) • (s • P.root i) = (2 : R) • (-t • P.root j) := by rw [h₁]
  rw [smul_smul]; rw [mul_comm]; rw [h₄]; rw [smul_comm]; rw [← neg_mul]; rw [← smul_smul] at h₁
  exact smul_right_injective M (neg_ne_zero.mpr h₃) h₁

section Finite

variable [Finite ι]

/--
lemma `coxeterWeight_ne_four_of_linearIndependent` / 引理 `coxeterWeight_ne_four_of_linearIndependent`

English:
lemma coxeterWeight_ne_four_of_linearIndependent
  statement: [NeZero (2 : R)] [IsAddTorsionFree M]
  proof: by
  intro contra
  have := P.infinite_of_linearIndependent_coxeterWeight_four hl contra
  exact not_finite ι

中文:
引理 coxeterWeight_ne_four_of_linearIndependent
  结论: [NeZero (2 : R)] [是加法无挠 M]
  证明: by
  intro contra
  have := P.infinite_of_linearIndependent_coxeterWeight_four hl contra
  exact not_finite ι

Depends on / 依赖: P.infinite_of_linearIndependent_coxeterWeight_four, contra, infinite_of_linearIndependent_coxeterWeight_four, not_finite
-/
lemma coxeterWeight_ne_four_of_linearIndependent [NeZero (2 : R)] [IsAddTorsionFree M]
    (hl : LinearIndependent R ![P.root i, P.root j]) :
    P.coxeterWeight i j != 4 := by
  intro contra
  have := P.infinite_of_linearIndependent_coxeterWeight_four hl contra
  exact not_finite ι

variable [CharZero R] [IsDomain R] [Module.IsTorsionFree R M]

/--
lemma `linearIndependent_iff_coxeterWeight_ne_four` / 引理 `linearIndependent_iff_coxeterWeight_ne_four`

English:
lemma linearIndependent_iff_coxeterWeight_ne_four
  proof: by
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  refine ⟨coxeterWeight_ne_four_of_linearIndependent P, fun h => ?_⟩
  contrapose h
  have h₁ := P.pairing_smul_root_eq_of_not_linearIndependent h
  rw [LinearIndependent.pair_symm_iff] at h
  have h₂ := P.pairing_smul_root_eq_of_not_linearInde

中文:
引理 linearIndependent_iff_coxeterWeight_ne_four
  证明: by
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  refine ⟨coxeterWeight_ne_four_of_linearIndependent P, fun h => ?_⟩
  contrapose h
  have h₁ := P.pairing_smul_root_eq_of_not_linearIndependent h
  rw [LinearIndependent.pair_symm_iff] at h
  have h₂ := P.pairing_smul_root_eq_of_not_linearInde

Depends on / 依赖: IsAddTorsionFree, LinearIndependent, LinearIndependent.pair_symm_iff, P.coxeterWeight, P.ne_zero, P.pairing, P.pairing_smul_root_eq_of_not_linearIndependent, P.root, contrapose, coxeterWeight, coxeterWeight_ne_four_of_linearIndependent, ne_zero, of_isTorsionFree, pair_symm_iff, pairing, pairing_smul_root_eq_of_not_linearIndependent, smul_left_injective
-/
lemma linearIndependent_iff_coxeterWeight_ne_four :
    LinearIndependent R ![P.root i, P.root j] ↔ P.coxeterWeight i j != 4 := by
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  refine ⟨coxeterWeight_ne_four_of_linearIndependent P, fun h => ?_⟩
  contrapose h
  have h₁ := P.pairing_smul_root_eq_of_not_linearIndependent h
  rw [LinearIndependent.pair_symm_iff] at h
  have h₂ := P.pairing_smul_root_eq_of_not_linearIndependent h
  suffices P.coxeterWeight i j • P.root i = (4 : R) • P.root i from
    smul_left_injective R (P.ne_zero i) this
  calc P.coxeterWeight i j • P.root i
      = (P.pairing i j * P.pairing j i) • P.root i := by rfl
    _ = P.pairing i j • (2 : R) • P.root j := by rw [mul_smul, h₁]
    _ = (4 : R) • P.root i := by rw [smul_comm, h₂, ← mul_smul]; norm_num

/--
lemma `coxeterWeight_eq_four_iff_not_linearIndependent` / 引理 `coxeterWeight_eq_four_iff_not_linearIndependent`

English:
lemma coxeterWeight_eq_four_iff_not_linearIndependent
  proof: by
  rw [P.linearIndependent_iff_coxeterWeight_ne_four]; rw [not_not]

中文:
引理 coxeterWeight_eq_four_iff_not_linearIndependent
  证明: by
  rw [P.linearIndependent_iff_coxeterWeight_ne_four]; rw [not_not]

Depends on / 依赖: P.linearIndependent_iff_coxeterWeight_ne_four, linearIndependent_iff_coxeterWeight_ne_four, not_not
-/
lemma coxeterWeight_eq_four_iff_not_linearIndependent :
    P.coxeterWeight i j = 4 ↔ ¬ LinearIndependent R ![P.root i, P.root j] := by
  rw [P.linearIndependent_iff_coxeterWeight_ne_four]; rw [not_not]

/--
Instance `instFlipIsReduced` / 实例 `instFlipIsReduced`

English:
instance instFlipIsReduced
  signature: [P.IsReduced] [IsTorsionFree R N]
  body: by
  refine ⟨fun i j h => ?_⟩
  rcases eq_or_ne i j with rfl | hij; · tauto
  right
  rw [← coxeterWeight_eq_four_iff_not_linearIndependent]; rw [coxeterWeight_flip]; rw [coxeterWeight_eq_four_iff_not_linearIndependent]; rw [IsReduced.linearIndependent_iff] at h
  push Not at h
  simp [P.root_eq_neg

中文:
实例 instFlipIsReduced
  签名: [P.是既约] [是无挠 R N]
  定义体: by
  refine ⟨fun i j h => ?_⟩
  rcases eq_or_ne i j with rfl | hij; · tauto
  right
  rw [← coxeterWeight_eq_four_iff_not_linearIndependent]; rw [coxeterWeight_flip]; rw [coxeterWeight_eq_four_iff_not_linearIndependent]; rw [IsReduced.linearIndependent_iff] at h
  push Not at h
  simp [P.root_eq_neg

Depends on / 依赖: IsReduced, IsReduced.linearIndependent_iff, P.root_eq_neg_iff.mp, coxeterWeight_eq_four_iff_not_linearIndependent, coxeterWeight_flip, eq_or_ne, linearIndependent_iff, root_eq_neg_iff
-/
instance instFlipIsReduced [P.IsReduced] [IsTorsionFree R N] : P.flip.IsReduced := by
  refine ⟨fun i j h => ?_⟩
  rcases eq_or_ne i j with rfl | hij; · tauto
  right
  rw [← coxeterWeight_eq_four_iff_not_linearIndependent]; rw [coxeterWeight_flip]; rw [coxeterWeight_eq_four_iff_not_linearIndependent]; rw [IsReduced.linearIndependent_iff] at h
  push Not at h
  simp [P.root_eq_neg_iff.mp (h hij)]

variable (i j)

/-- See also `RootPairing.pairingIn_two_two_iff`. -/
@[simp]
/--
lemma `pairing_two_two_iff` / 引理 `pairing_two_two_iff`

English:
lemma pairing_two_two_iff
  proof: by
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun h => by simp [h]⟩
  have : ¬ LinearIndependent R ![P.root i, P.root j] := by
    rw [← coxeterWeight_eq_four_iff_not_linearIndependent]; rw [coxeterWeight]; rw [h₁]; rw [h₂]; norm_num
  replace this := P.pairing_smul_root_eq_of_not_linearIndependent this
exact P.

中文:
引理 pairing_two_two_iff
  证明: by
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun h => by simp [h]⟩
  have : ¬ LinearIndependent R ![P.root i, P.root j] := by
    rw [← coxeterWeight_eq_four_iff_not_linearIndependent]; rw [coxeterWeight]; rw [h₁]; rw [h₂]; norm_num
  replace this := P.pairing_smul_root_eq_of_not_linearIndependent this
exact P.

Depends on / 依赖: LinearIndependent, P.pairing_smul_root_eq_of_not_linearIndependent, P.root, P.root.injective, coxeterWeight, coxeterWeight_eq_four_iff_not_linearIndependent, injective, pairing_smul_root_eq_of_not_linearIndependent, replace, smul_right_injective, two_ne_zero
-/
lemma pairing_two_two_iff :
    P.pairing i j = 2 ∧ P.pairing j i = 2 ↔ i = j := by
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun h => by simp [h]⟩
  have : ¬ LinearIndependent R ![P.root i, P.root j] := by
    rw [← coxeterWeight_eq_four_iff_not_linearIndependent]; rw [coxeterWeight]; rw [h₁]; rw [h₂]; norm_num
  replace this := P.pairing_smul_root_eq_of_not_linearIndependent this
exact P.root.injective smul_right_injective M two_ne_zero (h₂ ▸ this)

/-- See also `RootPairing.pairingIn_neg_two_neg_two_iff`. -/
@[simp]
/--
lemma `pairing_neg_two_neg_two_iff` / 引理 `pairing_neg_two_neg_two_iff`

English:
lemma pairing_neg_two_neg_two_iff
  proof: by
  simp only [← neg_eq_iff_eq_neg]
  simpa [eq_comm (a := -P.root i), eq_comm (b := j)] using
    P.pairing_two_two_iff (P.reflectionPerm i i) j

中文:
引理 pairing_neg_two_neg_two_iff
  证明: by
  simp only [← neg_eq_iff_eq_neg]
  simpa [eq_comm (a := -P.root i), eq_comm (b := j)] using
    P.pairing_two_two_iff (P.reflectionPerm i i) j

Depends on / 依赖: P.pairing_two_two_iff, P.reflectionPerm, P.root, eq_comm, neg_eq_iff_eq_neg, pairing_two_two_iff, reflectionPerm
-/
lemma pairing_neg_two_neg_two_iff :
    P.pairing i j = -2 ∧ P.pairing j i = -2 ↔ P.root i = -P.root j := by
  simp only [← neg_eq_iff_eq_neg]
  simpa [eq_comm (a := -P.root i), eq_comm (b := j)] using
    P.pairing_two_two_iff (P.reflectionPerm i i) j

variable [Module.IsTorsionFree R N]

/--
lemma `pairing_one_four_iff'` / 引理 `pairing_one_four_iff'`

English:
lemma pairing_one_four_iff'
  given: (h2 : IsSMulRegular R (2 : R))
  proof: by
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  have : IsAddTorsionFree N := .of_isTorsionFree R N
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun h => ?_⟩
  · have : ¬ LinearIndependent R ![P.root i, P.root j] := by
      rw [← coxeterWeight_eq_four_iff_not_linearIndependent]; rw [coxeterWeight]; rw [h

中文:
引理 pairing_one_four_iff'
  条件: (h2 : IsSMulRegular R (2 : R))
  证明: by
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  have : IsAddTorsionFree N := .of_isTorsionFree R N
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun h => ?_⟩
  · have : ¬ LinearIndependent R ![P.root i, P.root j] := by
      rw [← coxeterWeight_eq_four_iff_not_linearIndependent]; rw [coxeterWeight]; rw [h

Depends on / 依赖: IsAddTorsionFree, LinearIndependent, P.pairing_smul_root_eq_of_not_linearIndependent, P.root, coxeterWeight, coxeterWeight_eq_four_iff_not_linearIndependent, mul_smul, of_isTorsionFree, pairing_smul_root_eq_of_not_linearIndependent, replace, smul_right_injective, this.symm, two_ne_zero
-/
lemma pairing_one_four_iff' (h2 : IsSMulRegular R (2 : R)) :
    P.pairing i j = 1 ∧ P.pairing j i = 4 ↔ P.root j = (2 : R) • P.root i := by
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  have : IsAddTorsionFree N := .of_isTorsionFree R N
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun h => ?_⟩
  · have : ¬ LinearIndependent R ![P.root i, P.root j] := by
      rw [← coxeterWeight_eq_four_iff_not_linearIndependent]; rw [coxeterWeight]; rw [h₁]; rw [h₂]; simp
    replace this := P.pairing_smul_root_eq_of_not_linearIndependent this
    rw [h₂]; rw [show (4 : R) = 2 * 2 by norm_num]; rw [mul_smul] at this
    exact smul_right_injective M two_ne_zero this.symm
  · rw [← coroot_eq_smul_coroot_iff] at h
    rw [pairing]; rw [pairing]; rw [h]
    norm_num
    suffices (2 : R) • P.pairing i j = (2 : R) • 1 from h2 this
    rw [pairing]; rw [← map_smul]; rw [← h]
    simp

/--
lemma `pairing_neg_one_neg_four_iff'` / 引理 `pairing_neg_one_neg_four_iff'`

English:
lemma pairing_neg_one_neg_four_iff'
  given: (h2 : IsSMulRegular R (2 : R))
  proof: by
  simpa [neg_smul, ← neg_eq_iff_eq_neg] using P.pairing_one_four_iff' i (P.reflectionPerm j j) h2

中文:
引理 pairing_neg_one_neg_four_iff'
  条件: (h2 : IsSMulRegular R (2 : R))
  证明: by
  simpa [neg_smul, ← neg_eq_iff_eq_neg] using P.pairing_one_four_iff' i (P.reflectionPerm j j) h2

Depends on / 依赖: P.pairing_one_four_iff, P.reflectionPerm, neg_eq_iff_eq_neg, neg_smul, pairing_one_four_iff, reflectionPerm
-/
lemma pairing_neg_one_neg_four_iff' (h2 : IsSMulRegular R (2 : R)) :
    P.pairing i j = -1 ∧ P.pairing j i = -4 ↔ P.root j = (-2 : R) • P.root i := by
  simpa [neg_smul, ← neg_eq_iff_eq_neg] using P.pairing_one_four_iff' i (P.reflectionPerm j j) h2

/-- See also `RootPairing.pairingIn_one_four_iff`. -/
@[simp]
/--
lemma `pairing_one_four_iff` / 引理 `pairing_one_four_iff`

English:
lemma pairing_one_four_iff
  proof: P.pairing_one_four_iff' i j smul_right_injective R two_ne_zero

中文:
引理 pairing_one_four_iff
  证明: P.pairing_one_four_iff' i j smul_right_injective R two_ne_zero

Depends on / 依赖: P.pairing_one_four_iff, pairing_one_four_iff, smul_right_injective, two_ne_zero
-/
lemma pairing_one_four_iff :
    P.pairing i j = 1 ∧ P.pairing j i = 4 ↔ P.root j = (2 : R) • P.root i :=
P.pairing_one_four_iff' i j smul_right_injective R two_ne_zero

/-- See also `RootPairing.pairingIn_neg_one_neg_four_iff`. -/
@[simp]
/--
lemma `pairing_neg_one_neg_four_iff` / 引理 `pairing_neg_one_neg_four_iff`

English:
lemma pairing_neg_one_neg_four_iff
  proof: P.pairing_neg_one_neg_four_iff' i j smul_right_injective R two_ne_zero

中文:
引理 pairing_neg_one_neg_four_iff
  证明: P.pairing_neg_one_neg_four_iff' i j smul_right_injective R two_ne_zero

Depends on / 依赖: P.pairing_neg_one_neg_four_iff, pairing_neg_one_neg_four_iff, smul_right_injective, two_ne_zero
-/
lemma pairing_neg_one_neg_four_iff :
    P.pairing i j = -1 ∧ P.pairing j i = -4 ↔ P.root j = (-2 : R) • P.root i :=
P.pairing_neg_one_neg_four_iff' i j smul_right_injective R two_ne_zero

section IsValuedIn

open FaithfulSMul

variable [CommRing S] [Algebra S R] [FaithfulSMul S R] [P.IsValuedIn S]
omit [Module.IsTorsionFree R N]
variable {i j}

/--
lemma `linearIndependent_iff_coxeterWeightIn_ne_four` / 引理 `linearIndependent_iff_coxeterWeightIn_ne_four`

English:
lemma linearIndependent_iff_coxeterWeightIn_ne_four
  proof: by
  rw [linearIndependent_iff_coxeterWeight_ne_four]; rw [← P.algebraMap_coxeterWeightIn S]; rw [← map_ofNat (algebraMap S R)]; rw [(algebraMap_injective S R).ne_iff]

中文:
引理 linearIndependent_iff_coxeterWeightIn_ne_four
  证明: by
  rw [linearIndependent_iff_coxeterWeight_ne_four]; rw [← P.algebraMap_coxeterWeightIn S]; rw [← map_ofNat (algebraMap S R)]; rw [(algebraMap_injective S R).ne_iff]

Depends on / 依赖: P.algebraMap_coxeterWeightIn, algebraMap, algebraMap_coxeterWeightIn, algebraMap_injective, linearIndependent_iff_coxeterWeight_ne_four, map_ofNat, ne_iff
-/
lemma linearIndependent_iff_coxeterWeightIn_ne_four :
    LinearIndependent R ![P.root i, P.root j] ↔ P.coxeterWeightIn S i j != 4 := by
  rw [linearIndependent_iff_coxeterWeight_ne_four]; rw [← P.algebraMap_coxeterWeightIn S]; rw [← map_ofNat (algebraMap S R)]; rw [(algebraMap_injective S R).ne_iff]

/--
lemma `coxeterWeightIn_eq_four_iff_not_linearIndependent` / 引理 `coxeterWeightIn_eq_four_iff_not_linearIndependent`

English:
lemma coxeterWeightIn_eq_four_iff_not_linearIndependent
  proof: by
  rw [P.linearIndependent_iff_coxeterWeightIn_ne_four S]; rw [not_not]

中文:
引理 coxeterWeightIn_eq_four_iff_not_linearIndependent
  证明: by
  rw [P.linearIndependent_iff_coxeterWeightIn_ne_four S]; rw [not_not]

Depends on / 依赖: P.linearIndependent_iff_coxeterWeightIn_ne_four, linearIndependent_iff_coxeterWeightIn_ne_four, not_not
-/
lemma coxeterWeightIn_eq_four_iff_not_linearIndependent :
    P.coxeterWeightIn S i j = 4 ↔ ¬ LinearIndependent R ![P.root i, P.root j] := by
  rw [P.linearIndependent_iff_coxeterWeightIn_ne_four S]; rw [not_not]

/--
lemma `coxeterWeightIn_ne_four` / 引理 `coxeterWeightIn_ne_four`

English:
lemma coxeterWeightIn_ne_four
  given: [P.IsReduced] (h : i != j) (h' : P.root i != -P.root j)
  proof: by
  rw [ne_eq]; rw [coxeterWeightIn_eq_four_iff_not_linearIndependent]; rw [not_not]
  exact IsReduced.linearIndependent P h h'

中文:
引理 coxeterWeightIn_ne_four
  条件: [P.是既约] (h : i != j) (h' : P.root i != -P.root j)
  证明: by
  rw [ne_eq]; rw [coxeterWeightIn_eq_four_iff_not_linearIndependent]; rw [not_not]
  exact IsReduced.linearIndependent P h h'

Depends on / 依赖: IsReduced, IsReduced.linearIndependent, coxeterWeightIn_eq_four_iff_not_linearIndependent, linearIndependent, ne_eq, not_not
-/
lemma coxeterWeightIn_ne_four [P.IsReduced] (h : i != j) (h' : P.root i != -P.root j) :
    P.coxeterWeightIn S i j != 4 := by
  rw [ne_eq]; rw [coxeterWeightIn_eq_four_iff_not_linearIndependent]; rw [not_not]
  exact IsReduced.linearIndependent P h h'

variable (i j)

@[simp]
/--
lemma `pairingIn_two_two_iff` / 引理 `pairingIn_two_two_iff`

English:
lemma pairingIn_two_two_iff
  proof: by
  simp only [← P.pairing_two_two_iff, ← P.algebraMap_pairingIn S, ← map_ofNat (algebraMap S R),
    (algebraMap_injective S R).eq_iff]

@[simp]

中文:
引理 pairingIn_two_two_iff
  证明: by
  simp only [← P.pairing_two_two_iff, ← P.algebraMap_pairingIn S, ← map_ofNat (algebraMap S R),
    (algebraMap_injective S R).eq_iff]

@[simp]

Depends on / 依赖: P.algebraMap_pairingIn, P.pairing_two_two_iff, algebraMap, algebraMap_injective, algebraMap_pairingIn, eq_iff, map_ofNat, pairing_two_two_iff
-/
lemma pairingIn_two_two_iff :
    P.pairingIn S i j = 2 ∧ P.pairingIn S j i = 2 ↔ i = j := by
  simp only [← P.pairing_two_two_iff, ← P.algebraMap_pairingIn S, ← map_ofNat (algebraMap S R),
    (algebraMap_injective S R).eq_iff]

@[simp]
/--
lemma `pairingIn_neg_two_neg_two_iff` / 引理 `pairingIn_neg_two_neg_two_iff`

English:
lemma pairingIn_neg_two_neg_two_iff
  proof: by
  simp only [← P.pairing_neg_two_neg_two_iff, ← P.algebraMap_pairingIn S,
    ← map_ofNat (algebraMap S R), (algebraMap_injective S R).eq_iff, ← map_neg]

中文:
引理 pairingIn_neg_two_neg_two_iff
  证明: by
  simp only [← P.pairing_neg_two_neg_two_iff, ← P.algebraMap_pairingIn S,
    ← map_ofNat (algebraMap S R), (algebraMap_injective S R).eq_iff, ← map_neg]

Depends on / 依赖: P.algebraMap_pairingIn, P.pairing_neg_two_neg_two_iff, algebraMap, algebraMap_injective, algebraMap_pairingIn, eq_iff, map_neg, map_ofNat, pairing_neg_two_neg_two_iff
-/
lemma pairingIn_neg_two_neg_two_iff :
    P.pairingIn S i j = -2 ∧ P.pairingIn S j i = -2 ↔ P.root i = -P.root j := by
  simp only [← P.pairing_neg_two_neg_two_iff, ← P.algebraMap_pairingIn S,
    ← map_ofNat (algebraMap S R), (algebraMap_injective S R).eq_iff, ← map_neg]

variable [Module.IsTorsionFree R N]

/--
lemma `pairingIn_one_four_iff` / 引理 `pairingIn_one_four_iff`

English:
lemma pairingIn_one_four_iff
  proof: by
  rw [← P.pairing_one_four_iff]; rw [← P.algebraMap_pairingIn S]; rw [← P.algebraMap_pairingIn S]; rw [← map_one (algebraMap S R)]; rw [← map_ofNat (algebraMap S R)]; rw [(algebraMap_injective S R).eq_iff]; rw [(algebraMap_injective S R).eq_iff]

中文:
引理 pairingIn_one_four_iff
  证明: by
  rw [← P.pairing_one_four_iff]; rw [← P.algebraMap_pairingIn S]; rw [← P.algebraMap_pairingIn S]; rw [← map_one (algebraMap S R)]; rw [← map_ofNat (algebraMap S R)]; rw [(algebraMap_injective S R).eq_iff]; rw [(algebraMap_injective S R).eq_iff]

Depends on / 依赖: P.algebraMap_pairingIn, P.pairing_one_four_iff, algebraMap, algebraMap_injective, algebraMap_pairingIn, eq_iff, map_ofNat, map_one, pairing_one_four_iff
-/
lemma pairingIn_one_four_iff :
    P.pairingIn S i j = 1 ∧ P.pairingIn S j i = 4 ↔ P.root j = (2 : R) • P.root i := by
  rw [← P.pairing_one_four_iff]; rw [← P.algebraMap_pairingIn S]; rw [← P.algebraMap_pairingIn S]; rw [← map_one (algebraMap S R)]; rw [← map_ofNat (algebraMap S R)]; rw [(algebraMap_injective S R).eq_iff]; rw [(algebraMap_injective S R).eq_iff]

/--
lemma `pairingIn_neg_one_neg_four_iff` / 引理 `pairingIn_neg_one_neg_four_iff`

English:
lemma pairingIn_neg_one_neg_four_iff
  proof: by
  rw [← P.pairing_neg_one_neg_four_iff]; rw [← P.algebraMap_pairingIn S]; rw [← P.algebraMap_pairingIn S]; rw [← map_one (algebraMap S R)]; rw [← map_ofNat (algebraMap S R)]; rw [← map_neg]; rw [← map_neg]; rw [(algebraMap_injective S R).eq_iff]; rw [(algebraMap_injective S R).eq_iff]

中文:
引理 pairingIn_neg_one_neg_four_iff
  证明: by
  rw [← P.pairing_neg_one_neg_four_iff]; rw [← P.algebraMap_pairingIn S]; rw [← P.algebraMap_pairingIn S]; rw [← map_one (algebraMap S R)]; rw [← map_ofNat (algebraMap S R)]; rw [← map_neg]; rw [← map_neg]; rw [(algebraMap_injective S R).eq_iff]; rw [(algebraMap_injective S R).eq_iff]

Depends on / 依赖: P.algebraMap_pairingIn, P.pairing_neg_one_neg_four_iff, algebraMap, algebraMap_injective, algebraMap_pairingIn, eq_iff, map_neg, map_ofNat, map_one, pairing_neg_one_neg_four_iff
-/
lemma pairingIn_neg_one_neg_four_iff :
    P.pairingIn S i j = -1 ∧ P.pairingIn S j i = -4 ↔ P.root j = (-2 : R) • P.root i := by
  rw [← P.pairing_neg_one_neg_four_iff]; rw [← P.algebraMap_pairingIn S]; rw [← P.algebraMap_pairingIn S]; rw [← map_one (algebraMap S R)]; rw [← map_ofNat (algebraMap S R)]; rw [← map_neg]; rw [← map_neg]; rw [(algebraMap_injective S R).eq_iff]; rw [(algebraMap_injective S R).eq_iff]

end IsValuedIn

end Finite

end RootPairing
