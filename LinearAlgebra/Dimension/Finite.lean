/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Subsingleton
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Conditions for rank to be finite

Also contains characterization for when rank equals zero or rank equals one.

-/

@[expose] public section

noncomputable section

universe u v v' w

variable {R : Type u} {M : Type v} {ι : Type w}
variable [Semiring R] [AddCommMonoid M]
variable [Module R M]

attribute [local instance] nontrivial_of_invariantBasisNumber

open Basis Cardinal Function Module Set Submodule

/--
theorem `linearIndependent_bounded_of_finset_linearIndependent_bounded` / 定理 `linearIndependent_bounded_of_finset_linearIndependent_bounded`

English:
theorem linearIndependent_bounded_of_finset_linearIndependent_bounded
  statement: {n : Nat}
  proof: by
  intro s li
  apply Cardinal.card_le_of
  intro t
  rw [← Finset.card_map (Embedding.subtype (· in s))]
  apply H
  apply linearIndependent_finset_map_embedding_subtype _ li

中文:
定理 linearIndependent_bounded_of_finset_linearIndependent_bounded
  结论: {n : 自然数}
  证明: by
  intro s li
  apply Cardinal.card_le_of
  intro t
  rw [← Finset.card_map (Embedding.subtype (· in s))]
  apply H
  apply linearIndependent_finset_map_embedding_subtype _ li

Depends on / 依赖: Cardinal, Cardinal.card_le_of, Embedding, Embedding.subtype, Finset, Finset.card_map, card_le_of, card_map, linearIndependent_finset_map_embedding_subtype, subtype
-/
theorem linearIndependent_bounded_of_finset_linearIndependent_bounded {n : Nat}
    (H : forall s : Finset M, (LinearIndependent R fun i : s => (i : M)) -> s.card <= n) :
    forall s : Set M, LinearIndependent R ((↑) : s -> M) -> #s <= n := by
  intro s li
  apply Cardinal.card_le_of
  intro t
  rw [← Finset.card_map (Embedding.subtype (· in s))]
  apply H
  apply linearIndependent_finset_map_embedding_subtype _ li

/--
theorem `rank_le` / 定理 `rank_le`

English:
theorem rank_le
  statement: {n : Nat}
  proof: by
  rw [Module.rank_def]
  apply ciSup_le'
  rintro ⟨s, li⟩
  exact linearIndependent_bounded_of_finset_linearIndependent_bounded H _ li

中文:
定理 rank_le
  结论: {n : 自然数}
  证明: by
  rw [Module.rank_def]
  apply ciSup_le'
  rintro ⟨s, li⟩
  exact linearIndependent_bounded_of_finset_linearIndependent_bounded H _ li

Depends on / 依赖: Module, Module.rank_def, ciSup_le, linearIndependent_bounded_of_finset_linearIndependent_bounded, rank_def
-/
theorem rank_le {n : Nat}
    (H : forall s : Finset M, (LinearIndependent R fun i : s => (i : M)) -> s.card <= n) :
    Module.rank R M <= n := by
  rw [Module.rank_def]
  apply ciSup_le'
  rintro ⟨s, li⟩
  exact linearIndependent_bounded_of_finset_linearIndependent_bounded H _ li

section RankZero

/--
lemma `rank_eq_zero_iff` / 引理 `rank_eq_zero_iff`

English:
lemma rank_eq_zero_iff
  given: {R M} [Ring R] [AddCommGroup M] [Module R M]
  proof: by
  nontriviality R
  constructor
  · contrapose!
    rintro ⟨x, hx⟩
    rw [← Cardinal.one_le_iff_ne_zero]
    have : LinearIndependent R (fun _ : Unit => x) :=
      linearIndependent_iff.mpr (fun l hl => Finsupp.unique_ext <| not_not.mp fun H =>
        hx _ H ((Finsupp.linearCombination_unique 

中文:
引理 rank_eq_zero_iff
  条件: {R M} [环 R] [加法交换群 M] [模 R M]
  证明: by
  nontriviality R
  constructor
  · contrapose!
    rintro ⟨x, hx⟩
    rw [← Cardinal.one_le_iff_ne_zero]
    have : LinearIndependent R (fun _ : Unit => x) :=
      linearIndependent_iff.mpr (fun l hl => Finsupp.unique_ext <| not_not.mp fun H =>
        hx _ H ((Finsupp.linearCombination_unique 

Depends on / 依赖: Cardinal, Cardinal.mk_eq_zero_iff, Cardinal.one_le_iff_ne_zero, Finsupp, Finsupp.linearCombination_unique, Finsupp.unique_ext, LinearIndependent, Module, Module.rank_def, cardinal_lift_le_rank, ciSup_le, contrapose, linearCombination_unique, linearIndependent_iff, linearIndependent_iff.mpr, mk_eq_zero_iff, nonpos_iff_eq_zero, nontriviality, not_nonempty_iff, not_not
-/
lemma rank_eq_zero_iff {R M} [Ring R] [AddCommGroup M] [Module R M] :
    Module.rank R M = 0 ↔ forall x : M, exists a : R, a != 0 ∧ a • x = 0 := by
  nontriviality R
  constructor
  · contrapose!
    rintro ⟨x, hx⟩
    rw [← Cardinal.one_le_iff_ne_zero]
    have : LinearIndependent R (fun _ : Unit => x) :=
      linearIndependent_iff.mpr (fun l hl => Finsupp.unique_ext <| not_not.mp fun H =>
        hx _ H ((Finsupp.linearCombination_unique _ _ _).symm.trans hl))
    simpa using this.cardinal_lift_le_rank
  · intro h
    rw [← nonpos_iff_eq_zero]; rw [Module.rank_def]
    apply ciSup_le'
    intro ⟨s, hs⟩
    rw [nonpos_iff_eq_zero]; rw [Cardinal.mk_eq_zero_iff]; rw [← not_nonempty_iff]
    rintro ⟨i : s⟩
    obtain ⟨a, ha, ha'⟩ := h i
    apply ha
    simpa using DFunLike.congr_fun (linearIndependent_iff.mp hs (Finsupp.single i a) (by simpa)) i

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

section
variable [IsDomain R] [IsTorsionFree R M]

/--
theorem `rank_zero_iff_forall_zero` / 定理 `rank_zero_iff_forall_zero`

English:
theorem rank_zero_iff_forall_zero
  proof: by
  simp_rw [rank_eq_zero_iff, smul_eq_zero, and_or_left, not_and_self_iff, false_or,
    exists_and_right, and_iff_right (exists_ne (0 : R))]

中文:
定理 rank_zero_iff_对任意_zero
  证明: by
  simp_rw [rank_eq_zero_iff, smul_eq_zero, and_or_left, not_and_self_iff, false_or,
    exists_and_right, and_iff_right (exists_ne (0 : R))]

Depends on / 依赖: and_iff_right, and_or_left, exists_and_right, exists_ne, false_or, not_and_self_iff, rank_eq_zero_iff, simp_rw, smul_eq_zero
-/
theorem rank_zero_iff_forall_zero :
    Module.rank R M = 0 ↔ forall x : M, x = 0 := by
  simp_rw [rank_eq_zero_iff, smul_eq_zero, and_or_left, not_and_self_iff, false_or,
    exists_and_right, and_iff_right (exists_ne (0 : R))]

/--
theorem `rank_zero_iff` / 定理 `rank_zero_iff`

English:
theorem rank_zero_iff
  statement: Module.rank R M = 0 ↔ Subsingleton M
  proof: rank_zero_iff_forall_zero.trans (subsingleton_iff_forall_eq 0).symm

中文:
定理 rank_zero_iff
  结论: 模.rank R M = 0 ↔ 子单例 M
  证明: rank_zero_iff_forall_zero.trans (subsingleton_iff_forall_eq 0).symm

Depends on / 依赖: rank_zero_iff_forall_zero, rank_zero_iff_forall_zero.trans, subsingleton_iff_forall_eq
-/
theorem rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M :=
  rank_zero_iff_forall_zero.trans (subsingleton_iff_forall_eq 0).symm

/--
theorem `rank_pos_iff_exists_ne_zero` / 定理 `rank_pos_iff_exists_ne_zero`

English:
theorem rank_pos_iff_exists_ne_zero
  statement: 0 < Module.rank R M ↔ exists x : M, x != 0
  proof: by
  contrapose!; rw [nonpos_iff_eq_zero]; exact rank_zero_iff_forall_zero

中文:
定理 rank_pos_iff_存在_ne_zero
  结论: 0 < 模.rank R M ↔ 存在 x : M, x != 0
  证明: by
  contrapose!; rw [nonpos_iff_eq_zero]; exact rank_zero_iff_forall_zero

Depends on / 依赖: contrapose, nonpos_iff_eq_zero, rank_zero_iff_forall_zero
-/
theorem rank_pos_iff_exists_ne_zero : 0 < Module.rank R M ↔ exists x : M, x != 0 := by
  contrapose!; rw [nonpos_iff_eq_zero]; exact rank_zero_iff_forall_zero

/--
theorem `rank_pos_iff_nontrivial` / 定理 `rank_pos_iff_nontrivial`

English:
theorem rank_pos_iff_nontrivial
  statement: 0 < Module.rank R M ↔ Nontrivial M
  proof: rank_pos_iff_exists_ne_zero.trans (nontrivial_iff_exists_ne 0).symm

中文:
定理 rank_pos_iff_nontrivial
  结论: 0 < 模.rank R M ↔ 非平凡 M
  证明: rank_pos_iff_exists_ne_zero.trans (nontrivial_iff_exists_ne 0).symm

Depends on / 依赖: nontrivial_iff_exists_ne, rank_pos_iff_exists_ne_zero, rank_pos_iff_exists_ne_zero.trans
-/
theorem rank_pos_iff_nontrivial : 0 < Module.rank R M ↔ Nontrivial M :=
  rank_pos_iff_exists_ne_zero.trans (nontrivial_iff_exists_ne 0).symm

/--
theorem `rank_pos` / 定理 `rank_pos`

English:
theorem rank_pos
  given: [Nontrivial M]
  statement: 0 < Module.rank R M
  proof: rank_pos_iff_nontrivial.mpr ‹_›

中文:
定理 rank_pos
  条件: [非平凡 M]
  结论: 0 < 模.rank R M
  证明: rank_pos_iff_nontrivial.mpr ‹_›

Depends on / 依赖: rank_pos_iff_nontrivial, rank_pos_iff_nontrivial.mpr
-/
theorem rank_pos [Nontrivial M] : 0 < Module.rank R M :=
  rank_pos_iff_nontrivial.mpr ‹_›

/--
theorem `Module.finite_of_rank_eq_zero` / 定理 `Module.finite_of_rank_eq_zero`

English:
theorem Module.finite_of_rank_eq_zero
  given: (h : Module.rank R M = 0)
  statement: Module.Finite R M
  proof: by
  nontriviality R
  rw [rank_zero_iff] at h
  infer_instance

中文:
定理 模.finite_of_rank_eq_zero
  条件: (h : 模.rank R M = 0)
  结论: 模.有限 R M
  证明: by
  nontriviality R
  rw [rank_zero_iff] at h
  infer_instance

Depends on / 依赖: infer_instance, nontriviality, rank_zero_iff
-/
theorem Module.finite_of_rank_eq_zero (h : Module.rank R M = 0) : Module.Finite R M := by
  nontriviality R
  rw [rank_zero_iff] at h
  infer_instance

end

/--
lemma `exists_mem_ne_zero_of_rank_pos` / 引理 `exists_mem_ne_zero_of_rank_pos`

English:
lemma exists_mem_ne_zero_of_rank_pos
  given: [Nontrivial R] {s : Submodule R M} (h : 0 < Module.rank R s)
  proof: exists_mem_ne_zero_of_ne_bot fun eq => by rw [eq, rank_bot] at h; exact lt_irrefl _ h

中文:
引理 存在_mem_ne_zero_of_rank_pos
  条件: [非平凡 R] {s : 子模 R M} (h : 0 < 模.rank R s)
  证明: exists_mem_ne_zero_of_ne_bot fun eq => by rw [eq, rank_bot] at h; exact lt_irrefl _ h

Depends on / 依赖: exists_mem_ne_zero_of_ne_bot, lt_irrefl, rank_bot
-/
lemma exists_mem_ne_zero_of_rank_pos [Nontrivial R] {s : Submodule R M} (h : 0 < Module.rank R s) :
    exists b : M, b in s ∧ b != 0 :=
  exists_mem_ne_zero_of_ne_bot fun eq => by rw [eq, rank_bot] at h; exact lt_irrefl _ h

end RankZero

section Finite

/--
theorem `Module.finite_of_rank_eq_nat` / 定理 `Module.finite_of_rank_eq_nat`

English:
theorem Module.finite_of_rank_eq_nat
  given: [Module.Free R M] {n : Nat} (h : Module.rank R M = n)
  proof: by
  nontriviality R
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
have := mk_lt_aleph0_iff.mp
.trans_lt natCast_lt_aleph0 .trans_eq h b.linearIndependent.cardinal_le_rank
  exact Module.Finite.of_basis b

中文:
定理 模.finite_of_rank_eq_nat
  条件: [模.自由 R M] {n : 自然数} (h : 模.rank R M = n)
  证明: by
  nontriviality R
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
have := mk_lt_aleph0_iff.mp
.trans_lt natCast_lt_aleph0 .trans_eq h b.linearIndependent.cardinal_le_rank
  exact Module.Finite.of_basis b

Depends on / 依赖: Finite, Module, Module.Finite.of_basis, Module.Free.exists_basis, b.linearIndependent.cardinal_le_rank, cardinal_le_rank, exists_basis, linearIndependent, mk_lt_aleph0_iff, mk_lt_aleph0_iff.mp, natCast_lt_aleph0, nontriviality, of_basis, trans_eq, trans_lt
-/
theorem Module.finite_of_rank_eq_nat [Module.Free R M] {n : Nat} (h : Module.rank R M = n) :
    Module.Finite R M := by
  nontriviality R
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
have := mk_lt_aleph0_iff.mp
.trans_lt natCast_lt_aleph0 .trans_eq h b.linearIndependent.cardinal_le_rank
  exact Module.Finite.of_basis b

/--
theorem `Module.finite_of_rank_eq_one` / 定理 `Module.finite_of_rank_eq_one`

English:
theorem Module.finite_of_rank_eq_one
  given: [Module.Free R M] (h : Module.rank R M = 1)
  proof: Module.finite_of_rank_eq_nat h.trans Nat.cast_one.symm

中文:
定理 模.finite_of_rank_eq_one
  条件: [模.自由 R M] (h : 模.rank R M = 1)
  证明: Module.finite_of_rank_eq_nat h.trans Nat.cast_one.symm

Depends on / 依赖: Module, Module.finite_of_rank_eq_nat, Nat.cast_one.symm, cast_one, finite_of_rank_eq_nat, h.trans
-/
theorem Module.finite_of_rank_eq_one [Module.Free R M] (h : Module.rank R M = 1) :
    Module.Finite R M :=
Module.finite_of_rank_eq_nat h.trans Nat.cast_one.symm

section
variable [StrongRankCondition R]

/--
theorem `Module.Basis.nonempty_fintype_index_of_rank_lt_aleph0` / 定理 `Module.Basis.nonempty_fintype_index_of_rank_lt_aleph0`

English:
theorem Module.Basis.nonempty_fintype_index_of_rank_lt_aleph0
  statement: {ι : Type*} (b : Basis ι R M)
  proof: by
  rwa [← Cardinal.lift_lt, ← b.mk_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_lt_aleph0,
    Cardinal.lt_aleph0_iff_fintype] at h

中文:
定理 模.基.nonempty_fintype_index_of_rank_lt_aleph0
  结论: {ι : 类型} (b : 基 ι R M)
  证明: by
  rwa [← Cardinal.lift_lt, ← b.mk_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_lt_aleph0,
    Cardinal.lt_aleph0_iff_fintype] at h

Depends on / 依赖: Cardinal, Cardinal.lift_aleph0, Cardinal.lift_lt, Cardinal.lift_lt_aleph0, Cardinal.lt_aleph0_iff_fintype, b.mk_eq_rank, lift_aleph0, lift_lt, lift_lt_aleph0, lt_aleph0_iff_fintype, mk_eq_rank
-/
theorem Module.Basis.nonempty_fintype_index_of_rank_lt_aleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Nonempty (Fintype ι) := by
  rwa [← Cardinal.lift_lt, ← b.mk_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_lt_aleph0,
    Cardinal.lt_aleph0_iff_fintype] at h

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
@[instance_reducible]
/--
Definition of `Module.Basis.fintypeIndexOfRankLtAleph0` / `Module.Basis.fintypeIndexOfRankLtAleph0` 的定义

English:
definition Module.Basis.fintypeIndexOfRankLtAleph0
  signature: {ι : Type*} (b : Basis ι R M)
  body: Classical.choice (b.nonempty_fintype_index_of_rank_lt_aleph0 h)

中文:
定义 模.基.fintypeIndexOfRankLtAleph0
  签名: {ι : 类型} (b : 基 ι R M)
  定义体: Classical.choice (b.nonempty_fintype_index_of_rank_lt_aleph0 h)

Depends on / 依赖: Classical, Classical.choice, b.nonempty_fintype_index_of_rank_lt_aleph0, choice, nonempty_fintype_index_of_rank_lt_aleph0
-/
noncomputable def Module.Basis.fintypeIndexOfRankLtAleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Fintype ι :=
  Classical.choice (b.nonempty_fintype_index_of_rank_lt_aleph0 h)

/--
theorem `Module.Basis.finite_index_of_rank_lt_aleph0` / 定理 `Module.Basis.finite_index_of_rank_lt_aleph0`

English:
theorem Module.Basis.finite_index_of_rank_lt_aleph0
  statement: {ι : Type*} {s : Set ι} (b : Basis s R M)
  proof: Set.finite_def.2 (b.nonempty_fintype_index_of_rank_lt_aleph0 h)

中文:
定理 模.基.finite_index_of_rank_lt_aleph0
  结论: {ι : 类型} {s : 集合 ι} (b : 基 s R M)
  证明: Set.finite_def.2 (b.nonempty_fintype_index_of_rank_lt_aleph0 h)

Depends on / 依赖: Set.finite_def, b.nonempty_fintype_index_of_rank_lt_aleph0, finite_def, nonempty_fintype_index_of_rank_lt_aleph0
-/
theorem Module.Basis.finite_index_of_rank_lt_aleph0 {ι : Type*} {s : Set ι} (b : Basis s R M)
    (h : Module.rank R M < ℵ₀) : s.Finite :=
  Set.finite_def.2 (b.nonempty_fintype_index_of_rank_lt_aleph0 h)

end

namespace LinearIndependent
variable [StrongRankCondition R]

/--
theorem `cardinalMk_le_finrank` / 定理 `cardinalMk_le_finrank`

English:
theorem cardinalMk_le_finrank
  statement: [Module.Finite R M]
  proof: by
  rw [← lift_le.{max v w}]
  simpa only [← finrank_eq_rank, lift_natCast, lift_le_nat_iff] using h.cardinal_lift_le_rank

中文:
定理 cardinalMk_le_finrank
  结论: [模.有限 R M]
  证明: by
  rw [← lift_le.{max v w}]
  simpa only [← finrank_eq_rank, lift_natCast, lift_le_nat_iff] using h.cardinal_lift_le_rank

Depends on / 依赖: cardinal_lift_le_rank, finrank_eq_rank, h.cardinal_lift_le_rank, lift_le, lift_le_nat_iff, lift_natCast
-/
theorem cardinalMk_le_finrank [Module.Finite R M]
    {ι : Type w} {b : ι -> M} (h : LinearIndependent R b) : #ι <= finrank R M := by
  rw [← lift_le.{max v w}]
  simpa only [← finrank_eq_rank, lift_natCast, lift_le_nat_iff] using h.cardinal_lift_le_rank

/--
theorem `fintype_card_le_finrank` / 定理 `fintype_card_le_finrank`

English:
theorem fintype_card_le_finrank
  statement: [Module.Finite R M]
  proof: by
  simpa using h.cardinalMk_le_finrank

中文:
定理 fintype_card_le_finrank
  结论: [模.有限 R M]
  证明: by
  simpa using h.cardinalMk_le_finrank

Depends on / 依赖: cardinalMk_le_finrank, h.cardinalMk_le_finrank
-/
theorem fintype_card_le_finrank [Module.Finite R M]
    {ι : Type*} [Fintype ι] {b : ι -> M} (h : LinearIndependent R b) :
    Fintype.card ι <= finrank R M := by
  simpa using h.cardinalMk_le_finrank

/--
theorem `finset_card_le_finrank` / 定理 `finset_card_le_finrank`

English:
theorem finset_card_le_finrank
  statement: [Module.Finite R M]
  proof: by
  rw [← Fintype.card_coe]
  exact h.fintype_card_le_finrank

中文:
定理 finset_card_le_finrank
  结论: [模.有限 R M]
  证明: by
  rw [← Fintype.card_coe]
  exact h.fintype_card_le_finrank

Depends on / 依赖: Fintype, Fintype.card_coe, card_coe, fintype_card_le_finrank, h.fintype_card_le_finrank
-/
theorem finset_card_le_finrank [Module.Finite R M]
    {b : Finset M} (h : LinearIndependent R (fun x => x : b -> M)) :
    b.card <= finrank R M := by
  rw [← Fintype.card_coe]
  exact h.fintype_card_le_finrank

/--
theorem `lt_aleph0_of_finite` / 定理 `lt_aleph0_of_finite`

English:
theorem lt_aleph0_of_finite
  statement: {ι : Type w}
  proof: by
  apply Cardinal.lift_lt.1
  apply lt_of_le_of_lt
  · apply h.cardinal_lift_le_rank
  · rw [← finrank_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_natCast]
    apply Cardinal.natCast_lt_aleph0

中文:
定理 lt_aleph0_of_finite
  结论: {ι : 类型 w}
  证明: by
  apply Cardinal.lift_lt.1
  apply lt_of_le_of_lt
  · apply h.cardinal_lift_le_rank
  · rw [← finrank_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_natCast]
    apply Cardinal.natCast_lt_aleph0

Depends on / 依赖: Cardinal, Cardinal.lift_aleph0, Cardinal.lift_lt, Cardinal.lift_natCast, Cardinal.natCast_lt_aleph0, cardinal_lift_le_rank, finrank_eq_rank, h.cardinal_lift_le_rank, lift_aleph0, lift_lt, lift_natCast, lt_of_le_of_lt, natCast_lt_aleph0
-/
theorem lt_aleph0_of_finite {ι : Type w}
    [Module.Finite R M] {v : ι -> M} (h : LinearIndependent R v) : #ι < ℵ₀ := by
  apply Cardinal.lift_lt.1
  apply lt_of_le_of_lt
  · apply h.cardinal_lift_le_rank
  · rw [← finrank_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_natCast]
    apply Cardinal.natCast_lt_aleph0

/--
theorem `finite` / 定理 `finite`

English:
theorem finite
  statement: [Module.Finite R M] {ι : Type*} {f : ι -> M}
  proof: Cardinal.lt_aleph0_iff_finite.1 h.lt_aleph0_of_finite

中文:
定理 finite
  结论: [模.有限 R M] {ι : 类型} {f : ι -> M}
  证明: Cardinal.lt_aleph0_iff_finite.1 h.lt_aleph0_of_finite

Depends on / 依赖: Cardinal, Cardinal.lt_aleph0_iff_finite, h.lt_aleph0_of_finite, lt_aleph0_iff_finite, lt_aleph0_of_finite
-/
theorem finite [Module.Finite R M] {ι : Type*} {f : ι -> M}
    (h : LinearIndependent R f) : Finite ι :=
Cardinal.lt_aleph0_iff_finite.1 h.lt_aleph0_of_finite

/--
theorem `setFinite` / 定理 `setFinite`

English:
theorem setFinite
  statement: [Module.Finite R M] {b : Set M}
  proof: Cardinal.lt_aleph0_iff_set_finite.mp h.lt_aleph0_of_finite

中文:
定理 setFinite
  结论: [模.有限 R M] {b : 集合 M}
  证明: Cardinal.lt_aleph0_iff_set_finite.mp h.lt_aleph0_of_finite

Depends on / 依赖: Cardinal, Cardinal.lt_aleph0_iff_set_finite.mp, h.lt_aleph0_of_finite, lt_aleph0_iff_set_finite, lt_aleph0_of_finite
-/
theorem setFinite [Module.Finite R M] {b : Set M}
    (h : LinearIndependent R fun x : b => (x : M)) : b.Finite :=
  Cardinal.lt_aleph0_iff_set_finite.mp h.lt_aleph0_of_finite

end LinearIndependent

/--
lemma `exists_finset_linearIndependent_of_le_rank` / 引理 `exists_finset_linearIndependent_of_le_rank`

English:
lemma exists_finset_linearIndependent_of_le_rank
  given: {n : Nat} (hn : n <= Module.rank R M)
  proof: by
  rcases hn.eq_or_lt with h | h
  · obtain ⟨⟨s, hs⟩, hs'⟩ := exists_eq_ciSup_of_not_isSuccLimit
      Cardinal.bddAbove_of_small (h.trans (Module.rank_def R M) ▸ not_isSuccLimit_natCast n)
    rw [← Module.rank_def]; rw [← h] at hs'
    have : Finite s := lt_aleph0_iff_finite.mp (hs' ▸ natCast_lt

中文:
引理 存在_finset_linearIndependent_of_le_rank
  条件: {n : 自然数} (hn : n <= 模.rank R M)
  证明: by
  rcases hn.eq_or_lt with h | h
  · obtain ⟨⟨s, hs⟩, hs'⟩ := exists_eq_ciSup_of_not_isSuccLimit
      Cardinal.bddAbove_of_small (h.trans (Module.rank_def R M) ▸ not_isSuccLimit_natCast n)
    rw [← Module.rank_def]; rw [← h] at hs'
    have : Finite s := lt_aleph0_iff_finite.mp (hs' ▸ natCast_lt

Depends on / 依赖: Cardinal, Cardinal.bddAbove_of_small, Finite, Module, Module.rank_def, bddAbove_of_small, eq_or_lt, exists_eq_ciSup_of_not_isSuccLimit, exists_set_linearIndependent_of_lt_rank, h.mono, h.trans, hg.mono, hn.eq_or_lt, le_abs_self, le_trans, lt_aleph0_iff_finite, lt_aleph0_iff_finite.mp, natCast_lt_aleph0, nonempty_fintype, not_isSuccLimit_natCast
-/
lemma exists_finset_linearIndependent_of_le_rank {n : Nat} (hn : n <= Module.rank R M) :
    exists s : Finset M, s.card = n ∧ LinearIndepOn R id (s : Set M) := by
  rcases hn.eq_or_lt with h | h
  · obtain ⟨⟨s, hs⟩, hs'⟩ := exists_eq_ciSup_of_not_isSuccLimit
      Cardinal.bddAbove_of_small (h.trans (Module.rank_def R M) ▸ not_isSuccLimit_natCast n)
    rw [← Module.rank_def]; rw [← h] at hs'
    have : Finite s := lt_aleph0_iff_finite.mp (hs' ▸ natCast_lt_aleph0)
    cases nonempty_fintype s
    refine ⟨s.toFinset, by simpa using hs', by simpa⟩
  · obtain ⟨s, hs, hs'⟩ := exists_set_linearIndependent_of_lt_rank h
    have : Finite s := lt_aleph0_iff_finite.mp (hs ▸ natCast_lt_aleph0)
    cases nonempty_fintype s
    exact ⟨s.toFinset, by simpa using hs, by simpa⟩

@[deprecated (since := "2026-04-13")]
alias exists_set_linearIndependent_of_lt_rank := Module.exists_set_linearIndependent_of_lt_rank

/--
lemma `exists_linearIndependent_of_le_rank` / 引理 `exists_linearIndependent_of_le_rank`

English:
lemma exists_linearIndependent_of_le_rank
  given: {n : Nat} (hn : n <= Module.rank R M)
  proof: have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_rank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

中文:
引理 存在_linearIndependent_of_le_rank
  条件: {n : 自然数} (hn : n <= 模.rank R M)
  证明: have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_rank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

Depends on / 依赖: Finset, Finset.equivFinOfCardEq, equivFinOfCardEq, exists_finset_linearIndependent_of_le_rank, linearIndependent_equiv
-/
lemma exists_linearIndependent_of_le_rank {n : Nat} (hn : n <= Module.rank R M) :
    exists f : Fin n -> M, LinearIndependent R f :=
  have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_rank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

/--
lemma `natCast_le_rank_iff` / 引理 `natCast_le_rank_iff`

English:
lemma natCast_le_rank_iff
  given: [Nontrivial R] {n : Nat}
  proof: ⟨exists_linearIndependent_of_le_rank,
    fun H => by simpa using H.choose_spec.cardinal_lift_le_rank⟩

中文:
引理 natCast_le_rank_iff
  条件: [非平凡 R] {n : 自然数}
  证明: ⟨exists_linearIndependent_of_le_rank,
    fun H => by simpa using H.choose_spec.cardinal_lift_le_rank⟩

Depends on / 依赖: EventuallyEq, EventuallyEq.le, EventuallyEq.symm, H.choose_spec.cardinal_lift_le_rank, cardinal_lift_le_rank, choose_spec, exists_linearIndependent_of_le_rank, hf.mono
-/
lemma natCast_le_rank_iff [Nontrivial R] {n : Nat} :
    n <= Module.rank R M ↔ exists f : Fin n -> M, LinearIndependent R f :=
  ⟨exists_linearIndependent_of_le_rank,
    fun H => by simpa using H.choose_spec.cardinal_lift_le_rank⟩

/--
lemma `natCast_le_rank_iff_finset` / 引理 `natCast_le_rank_iff_finset`

English:
lemma natCast_le_rank_iff_finset
  given: [Nontrivial R] {n : Nat}
  proof: ⟨exists_finset_linearIndependent_of_le_rank,
    fun ⟨s, h₁, h₂⟩ => by simpa [h₁] using h₂.cardinal_le_rank⟩

中文:
引理 natCast_le_rank_iff_finset
  条件: [非平凡 R] {n : 自然数}
  证明: ⟨exists_finset_linearIndependent_of_le_rank,
    fun ⟨s, h₁, h₂⟩ => by simpa [h₁] using h₂.cardinal_le_rank⟩

Depends on / 依赖: cardinal_le_rank, exists_finset_linearIndependent_of_le_rank
-/
lemma natCast_le_rank_iff_finset [Nontrivial R] {n : Nat} :
    n <= Module.rank R M ↔ exists s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s -> M) :=
  ⟨exists_finset_linearIndependent_of_le_rank,
    fun ⟨s, h₁, h₂⟩ => by simpa [h₁] using h₂.cardinal_le_rank⟩

/--
lemma `exists_finset_linearIndependent_of_le_finrank` / 引理 `exists_finset_linearIndependent_of_le_finrank`

English:
lemma exists_finset_linearIndependent_of_le_finrank
  given: {n : Nat} (hn : n <= finrank R M)
  proof: by
  by_cases h : finrank R M = 0
  · rw [le_zero_iff.mp (hn.trans_eq h)]
    exact ⟨∅, rfl, by convert! linearIndependent_empty R M using 2 <;> aesop⟩
  exact exists_finset_linearIndependent_of_le_rank
    ((Nat.cast_le.mpr hn).trans_eq (cast_toNat_of_lt_aleph0 (toNat_ne_zero.mp h).2))

中文:
引理 存在_finset_linearIndependent_of_le_finrank
  条件: {n : 自然数} (hn : n <= finrank R M)
  证明: by
  by_cases h : finrank R M = 0
  · rw [le_zero_iff.mp (hn.trans_eq h)]
    exact ⟨∅, rfl, by convert! linearIndependent_empty R M using 2 <;> aesop⟩
  exact exists_finset_linearIndependent_of_le_rank
    ((Nat.cast_le.mpr hn).trans_eq (cast_toNat_of_lt_aleph0 (toNat_ne_zero.mp h).2))

Depends on / 依赖: EventuallyEq, EventuallyEq.symm, Nat.cast_le.mpr, cast_le, cast_toNat_of_lt_aleph0, convert, exists_finset_linearIndependent_of_le_rank, finrank, hf.congr, hg.congr, hn.trans_eq, le_zero_iff, le_zero_iff.mp, linearIndependent_empty, toNat_ne_zero, toNat_ne_zero.mp, trans_eq
-/
lemma exists_finset_linearIndependent_of_le_finrank {n : Nat} (hn : n <= finrank R M) :
    exists s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s -> M) := by
  by_cases h : finrank R M = 0
  · rw [le_zero_iff.mp (hn.trans_eq h)]
    exact ⟨∅, rfl, by convert! linearIndependent_empty R M using 2 <;> aesop⟩
  exact exists_finset_linearIndependent_of_le_rank
    ((Nat.cast_le.mpr hn).trans_eq (cast_toNat_of_lt_aleph0 (toNat_ne_zero.mp h).2))

/--
lemma `exists_linearIndependent_of_le_finrank` / 引理 `exists_linearIndependent_of_le_finrank`

English:
lemma exists_linearIndependent_of_le_finrank
  given: {n : Nat} (hn : n <= finrank R M)
  proof: have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_finrank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

中文:
引理 存在_linearIndependent_of_le_finrank
  条件: {n : 自然数} (hn : n <= finrank R M)
  证明: have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_finrank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

Depends on / 依赖: Finset, Finset.equivFinOfCardEq, equivFinOfCardEq, exists_finset_linearIndependent_of_le_finrank, linearIndependent_equiv
-/
lemma exists_linearIndependent_of_le_finrank {n : Nat} (hn : n <= finrank R M) :
    exists f : Fin n -> M, LinearIndependent R f :=
  have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_finrank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

variable [Module.Finite R M] [StrongRankCondition R] in
/--
theorem `Module.Finite.not_linearIndependent_of_infinite` / 定理 `Module.Finite.not_linearIndependent_of_infinite`

English:
theorem Module.Finite.not_linearIndependent_of_infinite
  statement: {ι : Type*} [Infinite ι]
  proof: mt LinearIndependent.finite @not_finite _ _

中文:
定理 模.有限.not_linearIndependent_of_infinite
  结论: {ι : 类型} [无限 ι]
  证明: mt LinearIndependent.finite @not_finite _ _

Depends on / 依赖: LinearIndependent, LinearIndependent.finite, finite, not_finite
-/
theorem Module.Finite.not_linearIndependent_of_infinite {ι : Type*} [Infinite ι]
(v : ι -> M) : ¬LinearIndependent R v := mt LinearIndependent.finite @not_finite _ _

section
variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M] [IsDomain R]
  [IsTorsionFree R M]

/--
theorem `iSupIndep.subtype_ne_bot_le_rank` / 定理 `iSupIndep.subtype_ne_bot_le_rank`

English:
theorem iSupIndep.subtype_ne_bot_le_rank
  given: {V : ι -> Submodule R M} (hV : iSupIndep V)
  proof: by
  set I := { i : ι // V i != ⊥ }
  have hI : forall i : I, exists v in V i, v != (0 : M) := by
    intro i
    rw [← Submodule.ne_bot_iff]
    exact i.prop
  choose v hvV hv using hI
  have : LinearIndependent R v := (hV.comp Subtype.coe_injective).linearIndependent _ hvV hv
  exact this.cardinal

中文:
定理 iSupIndep.subtype_ne_bot_le_rank
  条件: {V : ι -> 子模 R M} (hV : iSupIndep V)
  证明: by
  set I := { i : ι // V i != ⊥ }
  have hI : forall i : I, exists v in V i, v != (0 : M) := by
    intro i
    rw [← Submodule.ne_bot_iff]
    exact i.prop
  choose v hvV hv using hI
  have : LinearIndependent R v := (hV.comp Subtype.coe_injective).linearIndependent _ hvV hv
  exact this.cardinal

Depends on / 依赖: LinearIndependent, Submodule, Submodule.ne_bot_iff, Subtype, Subtype.coe_injective, cardinal_lift_le_rank, coe_injective, hV.comp, i.prop, linearIndependent, ne_bot_iff, this.cardinal_lift_le_rank
-/
theorem iSupIndep.subtype_ne_bot_le_rank {V : ι -> Submodule R M} (hV : iSupIndep V) :
    Cardinal.lift.{v} #{ i : ι // V i != ⊥ } <= Cardinal.lift.{w} (Module.rank R M) := by
  set I := { i : ι // V i != ⊥ }
  have hI : forall i : I, exists v in V i, v != (0 : M) := by
    intro i
    rw [← Submodule.ne_bot_iff]
    exact i.prop
  choose v hvV hv using hI
  have : LinearIndependent R v := (hV.comp Subtype.coe_injective).linearIndependent _ hvV hv
  exact this.cardinal_lift_le_rank

variable [Module.Finite R M] [StrongRankCondition R]

/--
theorem `iSupIndep.subtype_ne_bot_le_finrank_aux` / 定理 `iSupIndep.subtype_ne_bot_le_finrank_aux`

English:
theorem iSupIndep.subtype_ne_bot_le_finrank_aux
  proof: by
  suffices Cardinal.lift.{v} #{ i // p i != ⊥ } <= Cardinal.lift.{v} (finrank R M : Cardinal.{w}) by
    rwa [Cardinal.lift_le] at this
  calc
    Cardinal.lift.{v} #{ i // p i != ⊥ } <= Cardinal.lift.{w} (Module.rank R M) :=
      hp.subtype_ne_bot_le_rank
    _ = Cardinal.lift.{w} (finrank R M 

中文:
定理 iSupIndep.subtype_ne_bot_le_finrank_aux
  证明: by
  suffices Cardinal.lift.{v} #{ i // p i != ⊥ } <= Cardinal.lift.{v} (finrank R M : Cardinal.{w}) by
    rwa [Cardinal.lift_le] at this
  calc
    Cardinal.lift.{v} #{ i // p i != ⊥ } <= Cardinal.lift.{w} (Module.rank R M) :=
      hp.subtype_ne_bot_le_rank
    _ = Cardinal.lift.{w} (finrank R M 

Depends on / 依赖: Cardinal, Cardinal.lift, Cardinal.lift_le, Module, Module.rank, finrank, finrank_eq_rank, hp.subtype_ne_bot_le_rank, lift_le, subtype_ne_bot_le_rank
-/
theorem iSupIndep.subtype_ne_bot_le_finrank_aux
    {p : ι -> Submodule R M} (hp : iSupIndep p) :
    #{ i // p i != ⊥ } <= (finrank R M : Cardinal.{w}) := by
  suffices Cardinal.lift.{v} #{ i // p i != ⊥ } <= Cardinal.lift.{v} (finrank R M : Cardinal.{w}) by
    rwa [Cardinal.lift_le] at this
  calc
    Cardinal.lift.{v} #{ i // p i != ⊥ } <= Cardinal.lift.{w} (Module.rank R M) :=
      hp.subtype_ne_bot_le_rank
    _ = Cardinal.lift.{w} (finrank R M : Cardinal.{v}) := by rw [finrank_eq_rank]
    _ = Cardinal.lift.{v} (finrank R M : Cardinal.{w}) := by simp

/-- If `p` is an independent family of submodules of an `R`-finite module `M`, then the
number of nontrivial subspaces in the family `p` is finite. -/
@[instance_reducible]
/--
Definition of `iSupIndep.fintypeNeBotOfFiniteDimensional` / `iSupIndep.fintypeNeBotOfFiniteDimensional` 的定义

English:
definition iSupIndep.fintypeNeBotOfFiniteDimensional
  body: by
  suffices #{ i // p i != ⊥ } < (ℵ₀ : Cardinal.{w}) by
    rw [Cardinal.lt_aleph0_iff_fintype] at this
    exact this.some
  refine lt_of_le_of_lt hp.subtype_ne_bot_le_finrank_aux ?_
  simp [Cardinal.natCast_lt_aleph0]

中文:
定义 iSupIndep.fintypeNeBotOfFiniteDimensional
  定义体: by
  suffices #{ i // p i != ⊥ } < (ℵ₀ : Cardinal.{w}) by
    rw [Cardinal.lt_aleph0_iff_fintype] at this
    exact this.some
  refine lt_of_le_of_lt hp.subtype_ne_bot_le_finrank_aux ?_
  simp [Cardinal.natCast_lt_aleph0]

Depends on / 依赖: Cardinal, Cardinal.lt_aleph0_iff_fintype, Cardinal.natCast_lt_aleph0, hp.subtype_ne_bot_le_finrank_aux, lt_aleph0_iff_fintype, lt_of_le_of_lt, natCast_lt_aleph0, subtype_ne_bot_le_finrank_aux, this.some
-/
noncomputable def iSupIndep.fintypeNeBotOfFiniteDimensional
    {p : ι -> Submodule R M} (hp : iSupIndep p) :
    Fintype { i : ι // p i != ⊥ } := by
  suffices #{ i // p i != ⊥ } < (ℵ₀ : Cardinal.{w}) by
    rw [Cardinal.lt_aleph0_iff_fintype] at this
    exact this.some
  refine lt_of_le_of_lt hp.subtype_ne_bot_le_finrank_aux ?_
  simp [Cardinal.natCast_lt_aleph0]

/--
theorem `iSupIndep.subtype_ne_bot_le_finrank` / 定理 `iSupIndep.subtype_ne_bot_le_finrank`

English:
theorem iSupIndep.subtype_ne_bot_le_finrank
  proof: by simpa using hp.subtype_ne_bot_le_finrank_aux

中文:
定理 iSupIndep.subtype_ne_bot_le_finrank
  证明: by simpa using hp.subtype_ne_bot_le_finrank_aux

Depends on / 依赖: hp.subtype_ne_bot_le_finrank_aux, subtype_ne_bot_le_finrank_aux
-/
theorem iSupIndep.subtype_ne_bot_le_finrank
    {p : ι -> Submodule R M} (hp : iSupIndep p) [Fintype { i // p i != ⊥ }] :
    Fintype.card { i // p i != ⊥ } <= finrank R M := by simpa using hp.subtype_ne_bot_le_finrank_aux

end

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [StrongRankCondition R]

section

open Finset

/--
theorem `Module.exists_nontrivial_relation_of_finrank_lt_card` / 定理 `Module.exists_nontrivial_relation_of_finrank_lt_card`

English:
theorem Module.exists_nontrivial_relation_of_finrank_lt_card
  statement: {t : Finset M}
  proof: by
  obtain ⟨g, sum, z, nonzero⟩ := Fintype.not_linearIndependent_iff.mp
    (mt LinearIndependent.finset_card_le_finrank h.not_ge)
  refine ⟨Subtype.val.extend g 0, ?_, z, z.2, by rwa [Subtype.val_injective.extend_apply]⟩
  rw [← Finset.sum_finset_coe]; convert! sum; apply Subtype.val_injective.ext

中文:
定理 模.存在_nontrivial_relation_of_finrank_lt_card
  结论: {t : 有限集 M}
  证明: by
  obtain ⟨g, sum, z, nonzero⟩ := Fintype.not_linearIndependent_iff.mp
    (mt LinearIndependent.finset_card_le_finrank h.not_ge)
  refine ⟨Subtype.val.extend g 0, ?_, z, z.2, by rwa [Subtype.val_injective.extend_apply]⟩
  rw [← Finset.sum_finset_coe]; convert! sum; apply Subtype.val_injective.ext

Depends on / 依赖: Finset, Finset.sum_finset_coe, Fintype, Fintype.not_linearIndependent_iff.mp, LinearIndependent, LinearIndependent.finset_card_le_finrank, Subtype, Subtype.val.extend, Subtype.val_injective.extend_apply, convert, extend, extend_apply, finset_card_le_finrank, h.not_ge, nonzero, not_ge, not_linearIndependent_iff, sum_finset_coe, val_injective
-/
theorem Module.exists_nontrivial_relation_of_finrank_lt_card {t : Finset M}
    (h : finrank R M < t.card) : exists f : M -> R, ∑ e in t, f e • e = 0 ∧ exists x in t, f x != 0 := by
  obtain ⟨g, sum, z, nonzero⟩ := Fintype.not_linearIndependent_iff.mp
    (mt LinearIndependent.finset_card_le_finrank h.not_ge)
  refine ⟨Subtype.val.extend g 0, ?_, z, z.2, by rwa [Subtype.val_injective.extend_apply]⟩
  rw [← Finset.sum_finset_coe]; convert! sum; apply Subtype.val_injective.extend_apply

/--
theorem `Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card` / 定理 `Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card`

English:
theorem Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card
  proof: by
  -- Pick an element x₀ ∈ t,
  obtain ⟨x₀, x₀_mem⟩ := card_pos.1 ((Nat.succ_pos _).trans h)
  -- and apply the previous lemma to the {xᵢ - x₀}
  let shift : M ↪ M := ⟨(· - x₀), sub_left_injective⟩
  classical
  let t' := (t.erase x₀).map shift
  have h' : finrank R M < t'.card := by
    rw [card_

中文:
定理 模.存在_nontrivial_relation_sum_zero_of_finrank_succ_lt_card
  证明: by
  -- Pick an element x₀ ∈ t,
  obtain ⟨x₀, x₀_mem⟩ := card_pos.1 ((Nat.succ_pos _).trans h)
  -- and apply the previous lemma to the {xᵢ - x₀}
  let shift : M ↪ M := ⟨(· - x₀), sub_left_injective⟩
  classical
  let t' := (t.erase x₀).map shift
  have h' : finrank R M < t'.card := by
    rw [card_
-/
theorem Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card
    {t : Finset M} (h : finrank R M + 1 < t.card) :
    exists f : M -> R, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ exists x in t, f x != 0 := by
  -- Pick an element x₀ ∈ t,
  obtain ⟨x₀, x₀_mem⟩ := card_pos.1 ((Nat.succ_pos _).trans h)
  -- and apply the previous lemma to the {xᵢ - x₀}
  let shift : M ↪ M := ⟨(· - x₀), sub_left_injective⟩
  classical
  let t' := (t.erase x₀).map shift
  have h' : finrank R M < t'.card := by
    rw [card_map]; rw [card_erase_of_mem x₀_mem]
    exact Nat.lt_pred_iff.mpr h
  -- to obtain a function `g`.
  obtain ⟨g, gsum, x₁, x₁_mem, nz⟩ := exists_nontrivial_relation_of_finrank_lt_card h'
  -- Then obtain `f` by translating back by `x₀`,
  -- and setting the value of `f` at `x₀` to ensure `∑ e ∈ t, f e = 0`.
  let f : M -> R := fun z => if z = x₀ then -∑ z in t.erase x₀, g (z - x₀) else g (z - x₀)
  refine ⟨f, ?_, ?_, ?_⟩
  -- After this, it's a matter of verifying the properties,
  -- based on the corresponding properties for `g`.
  · rw [sum_map, Embedding.coeFn_mk] at gsum
    simp_rw [f, ← t.sum_erase_add _ x₀_mem, if_pos, neg_smul, sum_smul,
             ← sub_eq_add_neg, ← sum_sub_distrib, ← gsum, smul_sub]
    refine sum_congr rfl fun x x_mem => ?_
    rw [if_neg (mem_erase.mp x_mem).1]
  · simp_rw [f, ← t.sum_erase_add _ x₀_mem, if_pos, add_neg_eq_zero]
    exact sum_congr rfl fun x x_mem => if_neg (mem_erase.mp x_mem).1
  · obtain ⟨x₁, x₁_mem', rfl⟩ := Finset.mem_map.mp x₁_mem
    have := mem_erase.mp x₁_mem'
    exact ⟨x₁, by
      simpa only [f, Embedding.coeFn_mk, sub_add_cancel, this.2, true_and, if_neg this.1]⟩

end

end Finite

section FinrankZero

section
variable [Nontrivial R]

/-- A (finite-dimensional) space that is a subsingleton has zero `finrank`. -/
@[nontriviality]
/--
theorem `Module.finrank_zero_of_subsingleton` / 定理 `Module.finrank_zero_of_subsingleton`

English:
theorem Module.finrank_zero_of_subsingleton
  given: [Subsingleton M]
  proof: by
  rw [finrank]; rw [rank_subsingleton']; rw [map_zero]

中文:
定理 模.finrank_zero_of_subsingleton
  条件: [子单例 M]
  证明: by
  rw [finrank]; rw [rank_subsingleton']; rw [map_zero]

Depends on / 依赖: finrank, map_zero, rank_subsingleton
-/
theorem Module.finrank_zero_of_subsingleton [Subsingleton M] :
    finrank R M = 0 := by
  rw [finrank]; rw [rank_subsingleton']; rw [map_zero]

/--
lemma `LinearIndependent.finrank_eq_zero_of_infinite` / 引理 `LinearIndependent.finrank_eq_zero_of_infinite`

English:
lemma LinearIndependent.finrank_eq_zero_of_infinite
  statement: {ι} [Infinite ι] {v : ι -> M}
  proof: toNat_eq_zero.mpr .inr hv.aleph0_le_rank

中文:
引理 LinearIndependent.finrank_eq_zero_of_infinite
  结论: {ι} [无限 ι] {v : ι -> M}
  证明: toNat_eq_zero.mpr .inr hv.aleph0_le_rank

Depends on / 依赖: aleph0_le_rank, hv.aleph0_le_rank, toNat_eq_zero, toNat_eq_zero.mpr
-/
lemma LinearIndependent.finrank_eq_zero_of_infinite {ι} [Infinite ι] {v : ι -> M}
(hv : LinearIndependent R v) : finrank R M = 0 := toNat_eq_zero.mpr .inr hv.aleph0_le_rank

/--
theorem `Module.nontrivial_of_finrank_pos` / 定理 `Module.nontrivial_of_finrank_pos`

English:
theorem Module.nontrivial_of_finrank_pos
  given: (h : 0 < finrank R M)
  statement: Nontrivial M
  proof: by
  contrapose! h; exact finrank_zero_of_subsingleton.le

中文:
定理 模.nontrivial_of_finrank_pos
  条件: (h : 0 < finrank R M)
  结论: 非平凡 M
  证明: by
  contrapose! h; exact finrank_zero_of_subsingleton.le

Depends on / 依赖: contrapose, finrank_zero_of_subsingleton, finrank_zero_of_subsingleton.le
-/
theorem Module.nontrivial_of_finrank_pos (h : 0 < finrank R M) : Nontrivial M := by
  contrapose! h; exact finrank_zero_of_subsingleton.le

/--
theorem `Module.nontrivial_of_finrank_eq_succ` / 定理 `Module.nontrivial_of_finrank_eq_succ`

English:
theorem Module.nontrivial_of_finrank_eq_succ
  statement: {n : Nat}
  proof: nontrivial_of_finrank_pos (R := R) (by rw [hn]; exact n.succ_pos)

中文:
定理 模.nontrivial_of_finrank_eq_succ
  结论: {n : 自然数}
  证明: nontrivial_of_finrank_pos (R := R) (by rw [hn]; exact n.succ_pos)

Depends on / 依赖: n.succ_pos, nontrivial_of_finrank_pos, succ_pos
-/
theorem Module.nontrivial_of_finrank_eq_succ {n : Nat}
    (hn : finrank R M = n.succ) : Nontrivial M :=
  nontrivial_of_finrank_pos (R := R) (by rw [hn]; exact n.succ_pos)

variable (R M)

@[simp]
/--
theorem `finrank_bot` / 定理 `finrank_bot`

English:
theorem finrank_bot
  statement: finrank R (⊥ : Submodule R M) = 0
  proof: finrank_eq_of_rank_eq (rank_bot _ _)

中文:
定理 finrank_bot
  结论: finrank R (⊥ : 子模 R M) = 0
  证明: finrank_eq_of_rank_eq (rank_bot _ _)

Depends on / 依赖: finrank_eq_of_rank_eq, rank_bot
-/
theorem finrank_bot : finrank R (⊥ : Submodule R M) = 0 :=
  finrank_eq_of_rank_eq (rank_bot _ _)

end

section StrongRankCondition

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
variable [StrongRankCondition R] [Module.Finite R M]

/--
theorem `Module.finrank_pos_iff_exists_ne_zero` / 定理 `Module.finrank_pos_iff_exists_ne_zero`

English:
theorem Module.finrank_pos_iff_exists_ne_zero
  given: [IsDomain R] [IsTorsionFree R M]
  proof: by
  rw [← @rank_pos_iff_exists_ne_zero R M]; rw [← finrank_eq_rank]
  norm_cast

中文:
定理 模.finrank_pos_iff_存在_ne_zero
  条件: [是整环 R] [是无挠 R M]
  证明: by
  rw [← @rank_pos_iff_exists_ne_zero R M]; rw [← finrank_eq_rank]
  norm_cast

Depends on / 依赖: finrank_eq_rank, rank_pos_iff_exists_ne_zero
-/
theorem Module.finrank_pos_iff_exists_ne_zero [IsDomain R] [IsTorsionFree R M] :
    0 < finrank R M ↔ exists x : M, x != 0 := by
  rw [← @rank_pos_iff_exists_ne_zero R M]; rw [← finrank_eq_rank]
  norm_cast

/--
theorem `Module.finrank_pos_iff` / 定理 `Module.finrank_pos_iff`

English:
theorem Module.finrank_pos_iff
  given: [IsDomain R] [IsTorsionFree R M]
  proof: by
  rw [← rank_pos_iff_nontrivial (R := R)]; rw [← finrank_eq_rank]
  norm_cast

中文:
定理 模.finrank_pos_iff
  条件: [是整环 R] [是无挠 R M]
  证明: by
  rw [← rank_pos_iff_nontrivial (R := R)]; rw [← finrank_eq_rank]
  norm_cast

Depends on / 依赖: finrank_eq_rank, rank_pos_iff_nontrivial
-/
theorem Module.finrank_pos_iff [IsDomain R] [IsTorsionFree R M] :
    0 < finrank R M ↔ Nontrivial M := by
  rw [← rank_pos_iff_nontrivial (R := R)]; rw [← finrank_eq_rank]
  norm_cast

/--
theorem `Module.finrank_pos` / 定理 `Module.finrank_pos`

English:
theorem Module.finrank_pos
  given: [IsDomain R] [IsTorsionFree R M] [h : Nontrivial M]
  proof: finrank_pos_iff.mpr h

中文:
定理 模.finrank_pos
  条件: [是整环 R] [是无挠 R M] [h : 非平凡 M]
  证明: finrank_pos_iff.mpr h

Depends on / 依赖: finrank_pos_iff, finrank_pos_iff.mpr
-/
theorem Module.finrank_pos [IsDomain R] [IsTorsionFree R M] [h : Nontrivial M] :
    0 < finrank R M :=
  finrank_pos_iff.mpr h

/--
theorem `Module.finrank_eq_zero_iff` / 定理 `Module.finrank_eq_zero_iff`

English:
theorem Module.finrank_eq_zero_iff
  proof: by
  rw [← rank_eq_zero_iff (R := R)]; rw [← finrank_eq_rank]
  norm_cast

中文:
定理 模.finrank_eq_zero_iff
  证明: by
  rw [← rank_eq_zero_iff (R := R)]; rw [← finrank_eq_rank]
  norm_cast

Depends on / 依赖: finrank_eq_rank, rank_eq_zero_iff
-/
theorem Module.finrank_eq_zero_iff :
    finrank R M = 0 ↔ forall x : M, exists a : R, a != 0 ∧ a • x = 0 := by
  rw [← rank_eq_zero_iff (R := R)]; rw [← finrank_eq_rank]
  norm_cast

/--
theorem `Module.finrank_zero_iff` / 定理 `Module.finrank_zero_iff`

English:
theorem Module.finrank_zero_iff
  given: [IsDomain R] [IsTorsionFree R M]
  proof: by
  rw [← rank_zero_iff (R := R)]; rw [← finrank_eq_rank]
  norm_cast

中文:
定理 模.finrank_zero_iff
  条件: [是整环 R] [是无挠 R M]
  证明: by
  rw [← rank_zero_iff (R := R)]; rw [← finrank_eq_rank]
  norm_cast

Depends on / 依赖: finrank_eq_rank, rank_zero_iff
-/
theorem Module.finrank_zero_iff [IsDomain R] [IsTorsionFree R M] :
    finrank R M = 0 ↔ Subsingleton M := by
  rw [← rank_zero_iff (R := R)]; rw [← finrank_eq_rank]
  norm_cast

/--
lemma `Module.finrank_quotient_add_finrank_le` / 引理 `Module.finrank_quotient_add_finrank_le`

English:
lemma Module.finrank_quotient_add_finrank_le
  given: (N : Submodule R M)
  proof: by
  have := nontrivial_of_invariantBasisNumber R
  have := rank_quotient_add_rank_le N
  rw [← finrank_eq_rank R M]; rw [← finrank_eq_rank R]; rw [← N.finrank_eq_rank] at this
  exact mod_cast this

中文:
引理 模.finrank_quotient_add_finrank_le
  条件: (N : 子模 R M)
  证明: by
  have := nontrivial_of_invariantBasisNumber R
  have := rank_quotient_add_rank_le N
  rw [← finrank_eq_rank R M]; rw [← finrank_eq_rank R]; rw [← N.finrank_eq_rank] at this
  exact mod_cast this

Depends on / 依赖: N.finrank_eq_rank, finrank_eq_rank, mod_cast, nontrivial_of_invariantBasisNumber, rank_quotient_add_rank_le
-/
lemma Module.finrank_quotient_add_finrank_le (N : Submodule R M) :
    finrank R (M ⧸ N) + finrank R N <= finrank R M := by
  have := nontrivial_of_invariantBasisNumber R
  have := rank_quotient_add_rank_le N
  rw [← finrank_eq_rank R M]; rw [← finrank_eq_rank R]; rw [← N.finrank_eq_rank] at this
  exact mod_cast this

end StrongRankCondition

/--
theorem `Module.finrank_eq_zero_of_rank_eq_zero` / 定理 `Module.finrank_eq_zero_of_rank_eq_zero`

English:
theorem Module.finrank_eq_zero_of_rank_eq_zero
  given: (h : Module.rank R M = 0)
  proof: by
  delta finrank
  rw [h]; rw [zero_toNat]

中文:
定理 模.finrank_eq_zero_of_rank_eq_zero
  条件: (h : 模.rank R M = 0)
  证明: by
  delta finrank
  rw [h]; rw [zero_toNat]

Depends on / 依赖: finrank, zero_toNat
-/
theorem Module.finrank_eq_zero_of_rank_eq_zero (h : Module.rank R M = 0) :
    finrank R M = 0 := by
  delta finrank
  rw [h]; rw [zero_toNat]

/--
theorem `Module.finrank_eq_zero_of_not_faithfulSMul` / 定理 `Module.finrank_eq_zero_of_not_faithfulSMul`

English:
theorem Module.finrank_eq_zero_of_not_faithfulSMul
  given: (h : ¬ FaithfulSMul R M)
  statement: finrank R M = 0
  proof: finrank_eq_zero_of_rank_eq_zero (rank_eq_zero_of_not_faithfulSMul h)

中文:
定理 模.finrank_eq_zero_of_not_faithfulSMul
  条件: (h : ¬ 忠实标量乘法 R M)
  结论: finrank R M = 0
  证明: finrank_eq_zero_of_rank_eq_zero (rank_eq_zero_of_not_faithfulSMul h)

Depends on / 依赖: finrank_eq_zero_of_rank_eq_zero, rank_eq_zero_of_not_faithfulSMul
-/
theorem Module.finrank_eq_zero_of_not_faithfulSMul (h : ¬ FaithfulSMul R M) : finrank R M = 0 :=
  finrank_eq_zero_of_rank_eq_zero (rank_eq_zero_of_not_faithfulSMul h)

section

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsDomain R] [IsTorsionFree R M]

/--
lemma `Submodule.bot_eq_top_of_rank_eq_zero` / 引理 `Submodule.bot_eq_top_of_rank_eq_zero`

English:
lemma Submodule.bot_eq_top_of_rank_eq_zero
  given: (h : Module.rank R M = 0)
  statement: (⊥ : Submodule R M) = ⊤
  proof: by
  nontriviality R
  rw [rank_zero_iff] at h
  subsingleton

中文:
引理 子模.bot_eq_top_of_rank_eq_zero
  条件: (h : 模.rank R M = 0)
  结论: (⊥ : 子模 R M) = ⊤
  证明: by
  nontriviality R
  rw [rank_zero_iff] at h
  subsingleton

Depends on / 依赖: nontriviality, rank_zero_iff, subsingleton
-/
lemma Submodule.bot_eq_top_of_rank_eq_zero (h : Module.rank R M = 0) : (⊥ : Submodule R M) = ⊤ := by
  nontriviality R
  rw [rank_zero_iff] at h
  subsingleton

/-- See `rank_subsingleton` for the reason that `Nontrivial R` is needed. -/
@[simp]
/--
theorem `Submodule.rank_eq_zero` / 定理 `Submodule.rank_eq_zero`

English:
theorem Submodule.rank_eq_zero
  given: {S : Submodule R M}
  statement: Module.rank R S = 0 ↔ S = ⊥
  proof: ⟨fun h =>
    (Submodule.eq_bot_iff _).2 fun x hx =>
congr_arg Subtype.val
        ((Submodule.eq_bot_iff _).1 <| Eq.symm <| Submodule.bot_eq_top_of_rank_eq_zero h) ⟨x, hx⟩
          Submodule.mem_top,
    fun h => by rw [h, rank_bot]⟩

@[simp]

中文:
定理 子模.rank_eq_zero
  条件: {S : 子模 R M}
  结论: 模.rank R S = 0 ↔ S = ⊥
  证明: ⟨fun h =>
    (Submodule.eq_bot_iff _).2 fun x hx =>
congr_arg Subtype.val
        ((Submodule.eq_bot_iff _).1 <| Eq.symm <| Submodule.bot_eq_top_of_rank_eq_zero h) ⟨x, hx⟩
          Submodule.mem_top,
    fun h => by rw [h, rank_bot]⟩

@[simp]

Depends on / 依赖: Eq.symm, Submodule, Submodule.bot_eq_top_of_rank_eq_zero, Submodule.eq_bot_iff, Submodule.mem_top, Subtype, Subtype.val, bot_eq_top_of_rank_eq_zero, congr_arg, eq_bot_iff, mem_top, rank_bot
-/
theorem Submodule.rank_eq_zero {S : Submodule R M} : Module.rank R S = 0 ↔ S = ⊥ :=
  ⟨fun h =>
    (Submodule.eq_bot_iff _).2 fun x hx =>
congr_arg Subtype.val
        ((Submodule.eq_bot_iff _).1 <| Eq.symm <| Submodule.bot_eq_top_of_rank_eq_zero h) ⟨x, hx⟩
          Submodule.mem_top,
    fun h => by rw [h, rank_bot]⟩

@[simp]
/--
theorem `Submodule.finrank_eq_zero` / 定理 `Submodule.finrank_eq_zero`

English:
theorem Submodule.finrank_eq_zero
  given: [StrongRankCondition R] {S : Submodule R M} [Module.Finite R S]
  proof: by
  rw [← Submodule.rank_eq_zero]; rw [← finrank_eq_rank]; rw [← @Nat.cast_zero Cardinal]; rw [Nat.cast_inj]

@[simp]

中文:
定理 子模.finrank_eq_zero
  条件: [StrongRankCondition R] {S : 子模 R M} [模.有限 R S]
  证明: by
  rw [← Submodule.rank_eq_zero]; rw [← finrank_eq_rank]; rw [← @Nat.cast_zero Cardinal]; rw [Nat.cast_inj]

@[simp]

Depends on / 依赖: Cardinal, Nat.cast_inj, Nat.cast_zero, Submodule, Submodule.rank_eq_zero, cast_inj, cast_zero, finrank_eq_rank, rank_eq_zero
-/
theorem Submodule.finrank_eq_zero [StrongRankCondition R] {S : Submodule R M} [Module.Finite R S] :
    finrank R S = 0 ↔ S = ⊥ := by
  rw [← Submodule.rank_eq_zero]; rw [← finrank_eq_rank]; rw [← @Nat.cast_zero Cardinal]; rw [Nat.cast_inj]

@[simp]
/--
lemma `Submodule.one_le_finrank_iff` / 引理 `Submodule.one_le_finrank_iff`

English:
lemma Submodule.one_le_finrank_iff
  given: [StrongRankCondition R] {S : Submodule R M} [Module.Finite R S]
  proof: by
  contrapose!; rw [Nat.lt_one_iff, finrank_eq_zero]

中文:
引理 子模.one_le_finrank_iff
  条件: [StrongRankCondition R] {S : 子模 R M} [模.有限 R S]
  证明: by
  contrapose!; rw [Nat.lt_one_iff, finrank_eq_zero]

Depends on / 依赖: Nat.lt_one_iff, contrapose, finrank_eq_zero, lt_one_iff
-/
lemma Submodule.one_le_finrank_iff [StrongRankCondition R] {S : Submodule R M} [Module.Finite R S] :
    1 <= finrank R S ↔ S != ⊥ := by
  contrapose!; rw [Nat.lt_one_iff, finrank_eq_zero]

end

@[simp]
/--
theorem `Set.finrank_empty` / 定理 `Set.finrank_empty`

English:
theorem Set.finrank_empty
  given: [Nontrivial R]
  proof: by
  rw [Set.finrank]; rw [span_empty]; rw [finrank_bot]

中文:
定理 集合.finrank_empty
  条件: [非平凡 R]
  证明: by
  rw [Set.finrank]; rw [span_empty]; rw [finrank_bot]

Depends on / 依赖: Set.finrank, finrank, finrank_bot, span_empty
-/
theorem Set.finrank_empty [Nontrivial R] :
    Set.finrank R (∅ : Set M) = 0 := by
  rw [Set.finrank]; rw [span_empty]; rw [finrank_bot]

variable [Module.Free R M]

/--
theorem `finrank_eq_zero_of_basis_imp_not_finite` / 定理 `finrank_eq_zero_of_basis_imp_not_finite`

English:
theorem finrank_eq_zero_of_basis_imp_not_finite
  proof: by
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    exact (h ∅ ⟨LinearEquiv.ofSubsingleton _ _⟩ Set.finite_empty).elim
  obtain ⟨_, ⟨b⟩⟩ := (Module.free_iff_set R M).mp ‹_›
  have := Set.Infinite.to_subtype (h _ b)
  exact b.linearIndependent.finrank_eq_zero_of_infinite

中文:
定理 finrank_eq_zero_of_basis_imp_not_finite
  证明: by
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    exact (h ∅ ⟨LinearEquiv.ofSubsingleton _ _⟩ Set.finite_empty).elim
  obtain ⟨_, ⟨b⟩⟩ := (Module.free_iff_set R M).mp ‹_›
  have := Set.Infinite.to_subtype (h _ b)
  exact b.linearIndependent.finrank_eq_zero_of_infinite

Depends on / 依赖: Infinite, LinearEquiv, LinearEquiv.ofSubsingleton, Module, Module.free_iff_set, Module.subsingleton, Set.Infinite.to_subtype, Set.finite_empty, b.linearIndependent.finrank_eq_zero_of_infinite, finite_empty, finrank_eq_zero_of_infinite, free_iff_set, linearIndependent, ofSubsingleton, subsingleton, subsingleton_or_nontrivial, to_subtype
-/
theorem finrank_eq_zero_of_basis_imp_not_finite
    (h : forall s : Set M, Basis.{v} (s : Set M) R M -> ¬s.Finite) : finrank R M = 0 := by
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    exact (h ∅ ⟨LinearEquiv.ofSubsingleton _ _⟩ Set.finite_empty).elim
  obtain ⟨_, ⟨b⟩⟩ := (Module.free_iff_set R M).mp ‹_›
  have := Set.Infinite.to_subtype (h _ b)
  exact b.linearIndependent.finrank_eq_zero_of_infinite

/--
theorem `finrank_eq_zero_of_basis_imp_false` / 定理 `finrank_eq_zero_of_basis_imp_false`

English:
theorem finrank_eq_zero_of_basis_imp_false
  given: (h : forall s : Finset M, Basis.{v} (s : Set M) R M -> False)
  proof: finrank_eq_zero_of_basis_imp_not_finite fun s b hs =>
    h hs.toFinset
      (by
        convert! b
        simp)

中文:
定理 finrank_eq_zero_of_basis_imp_false
  条件: (h : 对任意 s : 有限集 M, 基.{v} (s : 集合 M) R M -> 假)
  证明: finrank_eq_zero_of_basis_imp_not_finite fun s b hs =>
    h hs.toFinset
      (by
        convert! b
        simp)

Depends on / 依赖: convert, finrank_eq_zero_of_basis_imp_not_finite, hs.toFinset, toFinset
-/
theorem finrank_eq_zero_of_basis_imp_false (h : forall s : Finset M, Basis.{v} (s : Set M) R M -> False) :
    finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs =>
    h hs.toFinset
      (by
        convert! b
        simp)

/--
theorem `finrank_eq_zero_of_not_exists_basis` / 定理 `finrank_eq_zero_of_not_exists_basis`

English:
theorem finrank_eq_zero_of_not_exists_basis
  proof: finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

中文:
定理 finrank_eq_zero_of_not_存在_basis
  证明: finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

Depends on / 依赖: finrank_eq_zero_of_basis_imp_false
-/
theorem finrank_eq_zero_of_not_exists_basis
    (h : ¬exists s : Finset M, Nonempty (Basis (s : Set M) R M)) : finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

/--
theorem `finrank_eq_zero_of_not_exists_basis_finite` / 定理 `finrank_eq_zero_of_not_exists_basis_finite`

English:
theorem finrank_eq_zero_of_not_exists_basis_finite
  proof: finrank_eq_zero_of_basis_imp_not_finite fun s b hs => h ⟨s, b, hs⟩

中文:
定理 finrank_eq_zero_of_not_存在_basis_finite
  证明: finrank_eq_zero_of_basis_imp_not_finite fun s b hs => h ⟨s, b, hs⟩

Depends on / 依赖: finrank_eq_zero_of_basis_imp_not_finite
-/
theorem finrank_eq_zero_of_not_exists_basis_finite
    (h : ¬exists (s : Set M) (_ : Basis.{v} (s : Set M) R M), s.Finite) : finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs => h ⟨s, b, hs⟩

/--
theorem `finrank_eq_zero_of_not_exists_basis_finset` / 定理 `finrank_eq_zero_of_not_exists_basis_finset`

English:
theorem finrank_eq_zero_of_not_exists_basis_finset
  given: (h : ¬exists s : Finset M, Nonempty (Basis s R M))
  proof: finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

中文:
定理 finrank_eq_zero_of_not_存在_basis_finset
  条件: (h : ¬存在 s : 有限集 M, 非空 (基 s R M))
  证明: finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

Depends on / 依赖: finrank_eq_zero_of_basis_imp_false
-/
theorem finrank_eq_zero_of_not_exists_basis_finset (h : ¬exists s : Finset M, Nonempty (Basis s R M)) :
    finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

end FinrankZero

section RankOne

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
variable [IsDomain R] [IsTorsionFree R M] [StrongRankCondition R]

/--
theorem `rank_eq_one` / 定理 `rank_eq_one`

English:
theorem rank_eq_one
  given: (v : M) (n : v != 0) (h : forall w : M, exists c : R, c • v = w)
  proof: by
  have := nontrivial_of_invariantBasisNumber R
  obtain ⟨b⟩ := (Basis.basis_singleton_iff.{_, _, u} PUnit).mpr ⟨v, n, h⟩
  rw [rank_eq_card_basis b]; rw [Fintype.card_punit]; rw [Nat.cast_one]

中文:
定理 rank_eq_one
  条件: (v : M) (n : v != 0) (h : 对任意 w : M, 存在 c : R, c • v = w)
  证明: by
  have := nontrivial_of_invariantBasisNumber R
  obtain ⟨b⟩ := (Basis.basis_singleton_iff.{_, _, u} PUnit).mpr ⟨v, n, h⟩
  rw [rank_eq_card_basis b]; rw [Fintype.card_punit]; rw [Nat.cast_one]

Depends on / 依赖: Basis.basis_singleton_iff, Fintype, Fintype.card_punit, Nat.cast_one, basis_singleton_iff, card_punit, cast_one, nontrivial_of_invariantBasisNumber, rank_eq_card_basis
-/
theorem rank_eq_one (v : M) (n : v != 0) (h : forall w : M, exists c : R, c • v = w) :
    Module.rank R M = 1 := by
  have := nontrivial_of_invariantBasisNumber R
  obtain ⟨b⟩ := (Basis.basis_singleton_iff.{_, _, u} PUnit).mpr ⟨v, n, h⟩
  rw [rank_eq_card_basis b]; rw [Fintype.card_punit]; rw [Nat.cast_one]

/--
theorem `finrank_eq_one` / 定理 `finrank_eq_one`

English:
theorem finrank_eq_one
  given: (v : M) (n : v != 0) (h : forall w : M, exists c : R, c • v = w)
  statement: finrank R M = 1
  proof: finrank_eq_of_rank_eq (rank_eq_one v n h)

中文:
定理 finrank_eq_one
  条件: (v : M) (n : v != 0) (h : 对任意 w : M, 存在 c : R, c • v = w)
  结论: finrank R M = 1
  证明: finrank_eq_of_rank_eq (rank_eq_one v n h)

Depends on / 依赖: finrank_eq_of_rank_eq, rank_eq_one
-/
theorem finrank_eq_one (v : M) (n : v != 0) (h : forall w : M, exists c : R, c • v = w) : finrank R M = 1 :=
  finrank_eq_of_rank_eq (rank_eq_one v n h)

end RankOne

section

variable [StrongRankCondition R]

/--
theorem `rank_le_one` / 定理 `rank_le_one`

English:
theorem rank_le_one
  given: (v : M) (h : forall w : M, exists c : R, c • v = w)
  statement: Module.rank R M <= 1
  proof: by
  simpa using LinearMap.lift_rank_le_of_surjective _
    (id h : Surjective (LinearMap.toSpanSingleton R M v))

中文:
定理 rank_le_one
  条件: (v : M) (h : 对任意 w : M, 存在 c : R, c • v = w)
  结论: 模.rank R M <= 1
  证明: by
  simpa using LinearMap.lift_rank_le_of_surjective _
    (id h : Surjective (LinearMap.toSpanSingleton R M v))

Depends on / 依赖: LinearMap, LinearMap.lift_rank_le_of_surjective, LinearMap.toSpanSingleton, Surjective, lift_rank_le_of_surjective, toSpanSingleton
-/
theorem rank_le_one (v : M) (h : forall w : M, exists c : R, c • v = w) : Module.rank R M <= 1 := by
  simpa using LinearMap.lift_rank_le_of_surjective _
    (id h : Surjective (LinearMap.toSpanSingleton R M v))

/--
theorem `finrank_le_one` / 定理 `finrank_le_one`

English:
theorem finrank_le_one
  given: (v : M) (h : forall w : M, exists c : R, c • v = w)
  statement: finrank R M <= 1
  proof: by
  rw [← map_one toNat]; rw [finrank]
  exact toNat_le_toNat (rank_le_one v h) one_lt_aleph0

中文:
定理 finrank_le_one
  条件: (v : M) (h : 对任意 w : M, 存在 c : R, c • v = w)
  结论: finrank R M <= 1
  证明: by
  rw [← map_one toNat]; rw [finrank]
  exact toNat_le_toNat (rank_le_one v h) one_lt_aleph0

Depends on / 依赖: finrank, map_one, one_lt_aleph0, rank_le_one, toNat_le_toNat
-/
theorem finrank_le_one (v : M) (h : forall w : M, exists c : R, c • v = w) : finrank R M <= 1 := by
  rw [← map_one toNat]; rw [finrank]
  exact toNat_le_toNat (rank_le_one v h) one_lt_aleph0

end

namespace Module
variable {ι : Type*}

/--
lemma `finite_finsupp_iff` / 引理 `finite_finsupp_iff`

English:
lemma finite_finsupp_iff
  proof: by
    simp only [or_iff_not_imp_left, not_subsingleton_iff_nontrivial, not_isEmpty_iff]
    rintro h ⟨i⟩ _
    obtain ⟨s, hs⟩ := id h
    exact ⟨.of_surjective (Finsupp.lapply (R := R) (M := M) i) (Finsupp.apply_surjective i),
       finite_of_span_finite_eq_top_finsupp s.finite_toSet hs⟩
  mpr
  |

中文:
引理 finite_finsupp_iff
  证明: by
    simp only [or_iff_not_imp_left, not_subsingleton_iff_nontrivial, not_isEmpty_iff]
    rintro h ⟨i⟩ _
    obtain ⟨s, hs⟩ := id h
    exact ⟨.of_surjective (Finsupp.lapply (R := R) (M := M) i) (Finsupp.apply_surjective i),
       finite_of_span_finite_eq_top_finsupp s.finite_toSet hs⟩
  mpr
  |
-/
@[simp] lemma finite_finsupp_iff :
    Module.Finite R (ι ->₀ M) ↔ IsEmpty ι ∨ Subsingleton M ∨ Module.Finite R M ∧ Finite ι where
  mp := by
    simp only [or_iff_not_imp_left, not_subsingleton_iff_nontrivial, not_isEmpty_iff]
    rintro h ⟨i⟩ _
    obtain ⟨s, hs⟩ := id h
    exact ⟨.of_surjective (Finsupp.lapply (R := R) (M := M) i) (Finsupp.apply_surjective i),
       finite_of_span_finite_eq_top_finsupp s.finite_toSet hs⟩
  mpr
  | .inl _ => inferInstance
| .inr .inl h => inferInstance
| .inr .inr h => by cases h; infer_instance

@[simp high]
/--
lemma `finite_finsupp_self_iff` / 引理 `finite_finsupp_self_iff`

English:
lemma finite_finsupp_self_iff
  statement: Module.Finite R (ι ->₀ R) ↔ Subsingleton R ∨ Finite ι
  proof: by
  simp only [finite_finsupp_iff, Finite.self, true_and, or_iff_right_iff_imp]
  exact fun _ => .inr inferInstance

中文:
引理 finite_finsupp_self_iff
  结论: 模.有限 R (ι ->₀ R) ↔ 子单例 R ∨ 有限 ι
  证明: by
  simp only [finite_finsupp_iff, Finite.self, true_and, or_iff_right_iff_imp]
  exact fun _ => .inr inferInstance

Depends on / 依赖: Finite, Finite.self, finite_finsupp_iff, or_iff_right_iff_imp, true_and
-/
lemma finite_finsupp_self_iff : Module.Finite R (ι ->₀ R) ↔ Subsingleton R ∨ Finite ι := by
  simp only [finite_finsupp_iff, Finite.self, true_and, or_iff_right_iff_imp]
  exact fun _ => .inr inferInstance

end Module
