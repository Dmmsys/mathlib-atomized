/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# The nondegenerate simplices in the nerve of a partially ordered type

In this file, we show that if `X` is a partially ordered type,
then an `n`-simplex `s` of the nerve is nondegenerate iff
the monotone map `s.obj : Fin (n + 1) → X` is strictly monotone.

-/

public section

universe u

open CategoryTheory Simplicial

namespace PartialOrder

variable {X : Type*} [PartialOrder X] {n : Nat}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mem_range_nerve_σ_iff` / 引理 `mem_range_nerve_σ_iff`

English:
lemma mem_range_nerve_σ_iff
  given: (s : (nerve X) _⦋n + 1⦌) (i : Fin (n + 1))
  proof: by
  constructor
  · rintro ⟨s, rfl⟩
    simp [-nerve_obj, nerve.σ_obj]
  · intro h
    refine ⟨(nerve X).δ i.castSucc s, ?_⟩
    ext j
    rw [nerve.σ_obj]; rw [nerve.δ_obj]
    by_cases h₁ : i.castSucc < j
    · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h₁)
      rw [Fin.predAbo

中文:
引理 mem_range_nerve_σ_iff
  条件: (s : (nerve X) _⦋n + 1⦌) (i : Fin (n + 1))
  证明: by
  constructor
  · rintro ⟨s, rfl⟩
    simp [-nerve_obj, nerve.σ_obj]
  · intro h
    refine ⟨(nerve X).δ i.castSucc s, ?_⟩
    ext j
    rw [nerve.σ_obj]; rw [nerve.δ_obj]
    by_cases h₁ : i.castSucc < j
    · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h₁)
      rw [Fin.predAbo

Depends on / 依赖: Fin.castSucc_castPred, Fin.eq_succ_of_ne_zero, Fin.le_castSucc_iff, Fin.ne_zero_of_lt, Fin.predAbove_of_castSucc_lt, Fin.predAbove_of_le_castSucc, Fin.pred_succ, Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_le_castSucc, castSucc, castSucc_castPred, eq_succ_of_ne_zero, i.castSucc, le_castSucc_iff, ne_zero_of_lt, nerve_obj, not_lt, predAbove_of_castSucc_lt, predAbove_of_le_castSucc, pred_succ
-/
lemma mem_range_nerve_σ_iff (s : (nerve X) _⦋n + 1⦌) (i : Fin (n + 1)) :
    s in Set.range ((nerve X).σ i) ↔
      s.obj i.castSucc = s.obj i.succ := by
  constructor
  · rintro ⟨s, rfl⟩
    simp [-nerve_obj, nerve.σ_obj]
  · intro h
    refine ⟨(nerve X).δ i.castSucc s, ?_⟩
    ext j
    rw [nerve.σ_obj]; rw [nerve.δ_obj]
    by_cases h₁ : i.castSucc < j
    · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h₁)
      rw [Fin.predAbove_of_castSucc_lt _ _ h₁]; rw [Fin.pred_succ]; rw [Fin.succAbove_of_le_castSucc _ _ (Fin.le_castSucc_iff.2 h₁)]
    · simp only [not_lt] at h₁
      grind [-> Fin.succAbove_of_castSucc_lt,
        -> Fin.predAbove_of_le_castSucc, Fin.castSucc_castPred, Fin.castPred_castSucc,
        Fin.succAbove_castSucc_self, -> LE.le.lt_or_eq]

/--
lemma `mem_nerve_degenerate_of_eq` / 引理 `mem_nerve_degenerate_of_eq`

English:
lemma mem_nerve_degenerate_of_eq
  statement: (s : (nerve X) _⦋n + 1⦌) {i : Fin (n + 1)}
  proof: by
  simp only [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
  exact ⟨i, by rwa [← mem_range_nerve_σ_iff] at hi⟩

中文:
引理 mem_nerve_degenerate_of_eq
  结论: (s : (nerve X) _⦋n + 1⦌) {i : Fin (n + 1)}
  证明: by
  simp only [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
  exact ⟨i, by rwa [← mem_range_nerve_σ_iff] at hi⟩

Depends on / 依赖: SSet.degenerate_eq_iUnion_range_, Set.mem_iUnion, mem_iUnion
-/
lemma mem_nerve_degenerate_of_eq (s : (nerve X) _⦋n + 1⦌) {i : Fin (n + 1)}
    (hi : s.obj i.castSucc = s.obj i.succ) :
    s in (nerve X).degenerate (n + 1) := by
  simp only [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
  exact ⟨i, by rwa [← mem_range_nerve_σ_iff] at hi⟩

/--
lemma `mem_nerve_nonDegenerate_iff_strictMono` / 引理 `mem_nerve_nonDegenerate_iff_strictMono`

English:
lemma mem_nerve_nonDegenerate_iff_strictMono
  given: (s : (nerve X) _⦋n⦌)
  proof: by
  obtain _ | n := n
  · simpa using Subsingleton.strictMono _
  · rw [← not_iff_not, ← SSet.mem_degenerate_iff_notMem_nonDegenerate,
      Fin.strictMono_iff_lt_succ, SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
    simp only [mem_range_nerve_σ_iff, not_forall]
    apply exists_congr
    in

中文:
引理 mem_nerve_nonDegenerate_iff_strictMono
  条件: (s : (nerve X) _⦋n⦌)
  证明: by
  obtain _ | n := n
  · simpa using Subsingleton.strictMono _
  · rw [← not_iff_not, ← SSet.mem_degenerate_iff_notMem_nonDegenerate,
      Fin.strictMono_iff_lt_succ, SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
    simp only [mem_range_nerve_σ_iff, not_forall]
    apply exists_congr
    in

Depends on / 依赖: Fin.strictMono_iff_lt_succ, LE.le.lt_or_eq, SSet.degenerate_eq_iUnion_range_, SSet.mem_degenerate_iff_notMem_nonDegenerate, Set.mem_iUnion, Subsingleton, Subsingleton.strictMono, castSucc_le_succ, exists_congr, i.castSucc_le_succ, lt_or_eq, lt_self_iff_false, mem_degenerate_iff_notMem_nonDegenerate, mem_iUnion, monotone, not_forall, not_iff_not, s.monotone, strictMono, strictMono_iff_lt_succ
-/
lemma mem_nerve_nonDegenerate_iff_strictMono (s : (nerve X) _⦋n⦌) :
    s in (nerve X).nonDegenerate n ↔ StrictMono s.obj := by
  obtain _ | n := n
  · simpa using Subsingleton.strictMono _
  · rw [← not_iff_not, ← SSet.mem_degenerate_iff_notMem_nonDegenerate,
      Fin.strictMono_iff_lt_succ, SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
    simp only [mem_range_nerve_σ_iff, not_forall]
    apply exists_congr
    intro i
    have := s.monotone i.castSucc_le_succ
    grind [lt_self_iff_false, LE.le.lt_or_eq]

/--
lemma `mem_nerve_nonDegenerate_iff_injective` / 引理 `mem_nerve_nonDegenerate_iff_injective`

English:
lemma mem_nerve_nonDegenerate_iff_injective
  given: (s : (nerve X) _⦋n⦌)
  proof: by
  rw [mem_nerve_nonDegenerate_iff_strictMono]
  refine ⟨fun h => h.injective, fun h i j hij => ?_⟩
  obtain h' | h' := (s.monotone hij.le).lt_or_eq
  · exact h'
  · exact ((h h').not_lt hij).elim

中文:
引理 mem_nerve_nonDegenerate_iff_injective
  条件: (s : (nerve X) _⦋n⦌)
  证明: by
  rw [mem_nerve_nonDegenerate_iff_strictMono]
  refine ⟨fun h => h.injective, fun h i j hij => ?_⟩
  obtain h' | h' := (s.monotone hij.le).lt_or_eq
  · exact h'
  · exact ((h h').not_lt hij).elim

Depends on / 依赖: h.injective, hij.le, injective, lt_or_eq, mem_nerve_nonDegenerate_iff_strictMono, monotone, not_lt, s.monotone
-/
lemma mem_nerve_nonDegenerate_iff_injective (s : (nerve X) _⦋n⦌) :
    s in (nerve X).nonDegenerate n ↔ Function.Injective s.obj := by
  rw [mem_nerve_nonDegenerate_iff_strictMono]
  refine ⟨fun h => h.injective, fun h i j hij => ?_⟩
  obtain h' | h' := (s.monotone hij.le).lt_or_eq
  · exact h'
  · exact ((h h').not_lt hij).elim

end PartialOrder
