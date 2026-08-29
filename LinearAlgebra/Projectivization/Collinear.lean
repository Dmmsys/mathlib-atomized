/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Bhavik Mehta
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Mathlib.LinearAlgebra.Projectivization.Independence
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!

# Collinearity in Projective Space

This file defines collinearity of points in projective space and proves
the uniqueness of the line through two distinct points.

## Main Results

* `Projectivization.IsCollinear`: A family of points in projective space is collinear if there
  exists a submodule of dimension at most 2 containing all points in the family.
* `Projectivization.line_unique`: Given two distinct points in projective space, there is a unique
  line (submodule of dimension 2) containing both points.

## Tags
Projective space, collinearity, projective geometry

-/

@[expose] public section

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  (M : Submodule K V) (S : Set (Projectivization K V))

namespace Projectivization

/--
Definition of `IsCollinear` / `IsCollinear` 的定义

English:
definition IsCollinear
  signature: : Prop
  body: exists (M : Subspace K V), Module.Finite K M.submodule ∧
  Module.finrank K M.submodule <= 2 ∧ S subseteq M

中文:
定义 IsCollinear
  签名: : 命题
  定义体: exists (M : Subspace K V), Module.Finite K M.submodule ∧
  Module.finrank K M.submodule <= 2 ∧ S subseteq M

Depends on / 依赖: Finite, M.submodule, Module, Module.Finite, Subspace, submodule
-/
def IsCollinear : Prop := exists (M : Subspace K V), Module.Finite K M.submodule ∧
  Module.finrank K M.submodule <= 2 ∧ S subseteq M

/--
lemma `IsCollinear_iff` / 引理 `IsCollinear_iff`

English:
lemma IsCollinear_iff
  statement: IsCollinear S ↔ exists (M : Subspace K V), Module.Finite K M.submodule ∧
  proof: Iff.rfl

中文:
引理 IsCollinear_iff
  结论: IsCollinear S ↔ 存在 (M : Subspace K V), Module.Finite K M.submodule ∧
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma IsCollinear_iff : IsCollinear S ↔ exists (M : Subspace K V), Module.Finite K M.submodule ∧
  Module.finrank K M.submodule <= 2 ∧ S subseteq M := Iff.rfl

/--
lemma `IsCollinear_iff_rank` / 引理 `IsCollinear_iff_rank`

English:
lemma IsCollinear_iff_rank
  proof: by
  rw [IsCollinear_iff]
  refine ⟨fun ⟨M, hM1, hM2, hM3⟩ => ⟨M, ?_, hM3⟩, fun ⟨M, hM1, hM2⟩ => ⟨M, ?_, ?_, hM2⟩⟩
.1 hM2 · exact FiniteDimensional.finrank_le_iff_rank_le (K := K) (V := M.submodule) (n := 2)
  · exact Module.rank_lt_aleph0_iff.1 (hM1.trans_lt (by norm_num))
  · exact Module.finrank_

中文:
引理 IsCollinear_iff_rank
  证明: by
  rw [IsCollinear_iff]
  refine ⟨fun ⟨M, hM1, hM2, hM3⟩ => ⟨M, ?_, hM3⟩, fun ⟨M, hM1, hM2⟩ => ⟨M, ?_, ?_, hM2⟩⟩
.1 hM2 · exact FiniteDimensional.finrank_le_iff_rank_le (K := K) (V := M.submodule) (n := 2)
  · exact Module.rank_lt_aleph0_iff.1 (hM1.trans_lt (by norm_num))
  · exact Module.finrank_

Depends on / 依赖: FiniteDimensional, FiniteDimensional.finrank_le_iff_rank_le, IsCollinear_iff, M.submodule, Module, Module.finrank_le_of_rank_le, Module.rank_lt_aleph0_iff, finrank_le_iff_rank_le, finrank_le_of_rank_le, hM1.trans_lt, rank_lt_aleph0_iff, submodule, trans_lt
-/
lemma IsCollinear_iff_rank :
    IsCollinear S ↔
      exists (M : Subspace K V), Module.rank K M.submodule <= 2 ∧ S subseteq M := by
  rw [IsCollinear_iff]
  refine ⟨fun ⟨M, hM1, hM2, hM3⟩ => ⟨M, ?_, hM3⟩, fun ⟨M, hM1, hM2⟩ => ⟨M, ?_, ?_, hM2⟩⟩
.1 hM2 · exact FiniteDimensional.finrank_le_iff_rank_le (K := K) (V := M.submodule) (n := 2)
  · exact Module.rank_lt_aleph0_iff.1 (hM1.trans_lt (by norm_num))
  · exact Module.finrank_le_of_rank_le hM1

@[simp]
/--
lemma `isCollinear_empty` / 引理 `isCollinear_empty`

English:
lemma isCollinear_empty
  statement: IsCollinear (∅ : Set (Projectivization K V))
  proof: by
  rw [IsCollinear_iff_rank]
  use ⊥
  rw [map_bot]
  simp

中文:
引理 isCollinear_empty
  结论: IsCollinear (∅ : Set (Projectivization K V))
  证明: by
  rw [IsCollinear_iff_rank]
  use ⊥
  rw [map_bot]
  simp

Depends on / 依赖: IsCollinear_iff_rank, map_bot
-/
lemma isCollinear_empty : IsCollinear (∅ : Set (Projectivization K V)) := by
  rw [IsCollinear_iff_rank]
  use ⊥
  rw [map_bot]
  simp

open scoped LinearAlgebra.Projectivization

/--
lemma `isCollinear_subset` / 引理 `isCollinear_subset`

English:
lemma isCollinear_subset
  given: (s t : Set (ℙ K V)) (hst : s subseteq t) (h : IsCollinear t)
  statement: IsCollinear s
  proof: by
  obtain ⟨M, hMfin, hM1, hM2⟩ := h
  exact ⟨M, hMfin, hM1, hst.trans hM2⟩

@[simp]

中文:
引理 isCollinear_subset
  条件: (s t : Set (ℙ K V)) (hst : s subseteq t) (h : IsCollinear t)
  结论: IsCollinear s
  证明: by
  obtain ⟨M, hMfin, hM1, hM2⟩ := h
  exact ⟨M, hMfin, hM1, hst.trans hM2⟩

@[simp]

Depends on / 依赖: hst.trans
-/
lemma isCollinear_subset (s t : Set (ℙ K V)) (hst : s subseteq t) (h : IsCollinear t) : IsCollinear s := by
  obtain ⟨M, hMfin, hM1, hM2⟩ := h
  exact ⟨M, hMfin, hM1, hst.trans hM2⟩

@[simp]
/--
lemma `isCollinear_singleton'` / 引理 `isCollinear_singleton'`

English:
lemma isCollinear_singleton'
  given: (a : ℙ K V)
  statement: IsCollinear {a}
  proof: by
  induction a using ind with | h v hv =>
  refine ⟨(Submodule.span K {v}).projectivization, ?_, ?_, ?_⟩
  · rw [Subspace.submodule.apply_symm_apply]
    exact Module.Finite.span_of_finite _ (Set.toFinite _)
  · rw [Subspace.submodule.apply_symm_apply, finrank_span_singleton hv]
    omega
  · simp

中文:
引理 isCollinear_singleton'
  条件: (a : ℙ K V)
  结论: IsCollinear {a}
  证明: by
  induction a using ind with | h v hv =>
  refine ⟨(Submodule.span K {v}).projectivization, ?_, ?_, ?_⟩
  · rw [Subspace.submodule.apply_symm_apply]
    exact Module.Finite.span_of_finite _ (Set.toFinite _)
  · rw [Subspace.submodule.apply_symm_apply, finrank_span_singleton hv]
    omega
  · simp

Depends on / 依赖: Finite, Module, Module.Finite.span_of_finite, Set.toFinite, Submodule, Submodule.mem_span_of_mem, Submodule.span, Subspace, Subspace.submodule.apply_symm_apply, apply_symm_apply, finrank_span_singleton, mem_span_of_mem, projectivization, span_of_finite, submodule, toFinite
-/
lemma isCollinear_singleton' (a : ℙ K V) : IsCollinear {a} := by
  induction a using ind with | h v hv =>
  refine ⟨(Submodule.span K {v}).projectivization, ?_, ?_, ?_⟩
  · rw [Subspace.submodule.apply_symm_apply]
    exact Module.Finite.span_of_finite _ (Set.toFinite _)
  · rw [Subspace.submodule.apply_symm_apply, finrank_span_singleton hv]
    omega
  · simp [Submodule.mem_span_of_mem]

/--
lemma `isCollinear_subsingleton` / 引理 `isCollinear_subsingleton`

English:
lemma isCollinear_subsingleton
  given: (hS : S.Subsingleton)
  proof: by
  obtain hS' | ⟨x, hx⟩ := hS.eq_empty_or_singleton <;> simp_all

中文:
引理 isCollinear_subsingleton
  条件: (hS : S.Subsingleton)
  证明: by
  obtain hS' | ⟨x, hx⟩ := hS.eq_empty_or_singleton <;> simp_all

Depends on / 依赖: eq_empty_or_singleton, hS.eq_empty_or_singleton
-/
lemma isCollinear_subsingleton (hS : S.Subsingleton) :
    IsCollinear S := by
  obtain hS' | ⟨x, hx⟩ := hS.eq_empty_or_singleton <;> simp_all

/--
lemma `isCollinear_pair` / 引理 `isCollinear_pair`

English:
lemma isCollinear_pair
  given: (a b : ℙ K V)
  statement: IsCollinear {a, b}
  proof: by
  if h : a = b then simp [h] else
  induction a using Projectivization.ind with | h v hv =>
  induction b using Projectivization.ind with | h w hw =>
  rw [← ne_eq]; rw [← independent_pair_iff_ne]; rw [independent_mk_iff_LinearIndependent] at h
  refine ⟨(Submodule.span K {v, w}).projectivization

中文:
引理 isCollinear_pair
  条件: (a b : ℙ K V)
  结论: IsCollinear {a, b}
  证明: by
  if h : a = b then simp [h] else
  induction a using Projectivization.ind with | h v hv =>
  induction b using Projectivization.ind with | h w hw =>
  rw [← ne_eq]; rw [← independent_pair_iff_ne]; rw [independent_mk_iff_LinearIndependent] at h
  refine ⟨(Submodule.span K {v, w}).projectivization

Depends on / 依赖: Finite, Matrix, Matrix.range_cons_cons_empty, Module, Module.Finite.span_of_finite, Projectivization, Projectivization.ind, Set.toFinite, Submodule, Submodule.span, Subspace, Subspace.submodule.apply_symm_apply, apply_symm_apply, casesOn, hs.casesOn, independent_mk_iff_LinearIndependent, independent_pair_iff_ne, ne_eq, projectivization, range_cons_cons_empty
-/
lemma isCollinear_pair (a b : ℙ K V) : IsCollinear {a, b} := by
  if h : a = b then simp [h] else
  induction a using Projectivization.ind with | h v hv =>
  induction b using Projectivization.ind with | h w hw =>
  rw [← ne_eq]; rw [← independent_pair_iff_ne]; rw [independent_mk_iff_LinearIndependent] at h
  refine ⟨(Submodule.span K {v, w}).projectivization, ?_, ?_, fun s hs => hs.casesOn ?_ ?_⟩
  · rw [Subspace.submodule.apply_symm_apply]
    exact Module.Finite.span_of_finite _ (Set.toFinite _)
  · rw [Subspace.submodule.apply_symm_apply, ← Matrix.range_cons_cons_empty v w ![]]
    simp [finrank_span_eq_card h]
  all_goals rintro rfl; simp [Submodule.mem_span_of_mem]

/--
lemma `isCollinear_of_card_eq_two` / 引理 `isCollinear_of_card_eq_two`

English:
lemma isCollinear_of_card_eq_two
  given: (hS : S.ncard = 2)
  statement: IsCollinear S
  proof: by
  obtain ⟨x, y, _, rfl⟩ := Set.ncard_eq_two.1 hS
  exact isCollinear_pair x y

中文:
引理 isCollinear_of_card_eq_two
  条件: (hS : S.ncard = 2)
  结论: IsCollinear S
  证明: by
  obtain ⟨x, y, _, rfl⟩ := Set.ncard_eq_two.1 hS
  exact isCollinear_pair x y

Depends on / 依赖: Set.ncard_eq_two, isCollinear_pair, ncard_eq_two
-/
lemma isCollinear_of_card_eq_two (hS : S.ncard = 2) : IsCollinear S := by
  obtain ⟨x, y, _, rfl⟩ := Set.ncard_eq_two.1 hS
  exact isCollinear_pair x y

/--
lemma `line_unique'` / 引理 `line_unique'`

English:
lemma line_unique'
  statement: {u v : V} (hu : u != 0) (hv : v != 0) (huv : LinearIndependent K ![u, v])
  proof: by
  have h1 : Submodule.span K {u, v} <= p := by
    refine Submodule.span_le.2 fun x hx => ?_
    simp only [Submodule.mk_mem_projectivization_iff] at hp2 hp3
    refine hx.casesOn ?_ ?_ <;> simp_all
  have : Module.Finite K p := Module.finite_of_finrank_eq_succ hp1
.symm refine Submodule.eq_of_le

中文:
引理 line_unique'
  结论: {u v : V} (hu : u != 0) (hv : v != 0) (huv : LinearIndependent K ![u, v])
  证明: by
  have h1 : Submodule.span K {u, v} <= p := by
    refine Submodule.span_le.2 fun x hx => ?_
    simp only [Submodule.mk_mem_projectivization_iff] at hp2 hp3
    refine hx.casesOn ?_ ?_ <;> simp_all
  have : Module.Finite K p := Module.finite_of_finrank_eq_succ hp1
.symm refine Submodule.eq_of_le

Depends on / 依赖: Finite, Matrix, Matrix.range_cons_cons_empty, Module, Module.Finite, Module.finite_of_finrank_eq_succ, Submodule, Submodule.eq_of_le_of_finrank_eq, Submodule.mk_mem_projectivization_iff, Submodule.span, Submodule.span_le, casesOn, eq_of_le_of_finrank_eq, finite_of_finrank_eq_succ, finrank_span_eq_card, hx.casesOn, mk_mem_projectivization_iff, range_cons_cons_empty, span_le
-/
lemma line_unique' {u v : V} (hu : u != 0) (hv : v != 0) (huv : LinearIndependent K ![u, v])
    (p : Submodule K V) (hp1 : Module.finrank K p = 2)
    (hp2 : mk K u hu in p.projectivization) (hp3 : mk K v hv in p.projectivization) :
    p = Submodule.span K {u, v} := by
  have h1 : Submodule.span K {u, v} <= p := by
    refine Submodule.span_le.2 fun x hx => ?_
    simp only [Submodule.mk_mem_projectivization_iff] at hp2 hp3
    refine hx.casesOn ?_ ?_ <;> simp_all
  have : Module.Finite K p := Module.finite_of_finrank_eq_succ hp1
.symm refine Submodule.eq_of_le_of_finrank_eq h1 ?_
  rw [hp1]; rw [← Matrix.range_cons_cons_empty _ _ ![]]
  simp [finrank_span_eq_card huv]

/--
lemma `line_unique` / 引理 `line_unique`

English:
lemma line_unique
  statement: {x y : ℙ K V} (hxy : x != y) (p q : Submodule K V) (hp1 : Module.finrank K p = 2)
  proof: by
  induction x using ind with | h v hv =>
  induction y using ind with | h w hw =>
  rw [← independent_pair_iff_ne]; rw [independent_mk_iff_LinearIndependent] at hxy
  rw [line_unique' hv hw hxy p hp1 hp2 hp3]; rw [line_unique' hv hw hxy q hq1 hq2 hq3]

中文:
引理 line_unique
  结论: {x y : ℙ K V} (hxy : x != y) (p q : Submodule K V) (hp1 : Module.finrank K p = 2)
  证明: by
  induction x using ind with | h v hv =>
  induction y using ind with | h w hw =>
  rw [← independent_pair_iff_ne]; rw [independent_mk_iff_LinearIndependent] at hxy
  rw [line_unique' hv hw hxy p hp1 hp2 hp3]; rw [line_unique' hv hw hxy q hq1 hq2 hq3]

Depends on / 依赖: independent_mk_iff_LinearIndependent, independent_pair_iff_ne, line_unique
-/
lemma line_unique {x y : ℙ K V} (hxy : x != y) (p q : Submodule K V) (hp1 : Module.finrank K p = 2)
    (hq1 : Module.finrank K q = 2) (hp2 : x in p.projectivization) (hp3 : y in p.projectivization)
    (hq2 : x in q.projectivization) (hq3 : y in q.projectivization) : p = q := by
  induction x using ind with | h v hv =>
  induction y using ind with | h w hw =>
  rw [← independent_pair_iff_ne]; rw [independent_mk_iff_LinearIndependent] at hxy
  rw [line_unique' hv hw hxy p hp1 hp2 hp3]; rw [line_unique' hv hw hxy q hq1 hq2 hq3]

end Projectivization
