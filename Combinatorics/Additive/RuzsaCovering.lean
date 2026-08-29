/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Positivity.Finset

/-!
# Ruzsa's covering lemma

This file proves the Ruzsa covering lemma. This says that, for `A`, `B` finsets, we can cover `A`
with at most `#(A + B) / #B` copies of `B - B`.
-/

public section

open scoped Pointwise

variable {G : Type*} [Group G] {K : Real}

namespace Finset
variable [DecidableEq G] {A B : Finset G}

/-- **Ruzsa's covering lemma**. -/
@[to_additive /-- **Ruzsa's covering lemma** -/]
/--
theorem `ruzsa_covering_mul` / 定理 `ruzsa_covering_mul`

English:
theorem ruzsa_covering_mul
  given: (hB : B.Nonempty) (hK : #(A * B) <= K * #B)
  proof: by
  have : forall F, Decidable ((F : Set G).PairwiseDisjoint (· • B)) := fun F => Classical.dec _
  set C := {F in A.powerset | (SetLike.coe F).PairwiseDisjoint (· • B)}
obtain ⟨F, hFmax⟩ := C.exists_maximal filter_nonempty_iff.2
    ⟨∅, empty_mem_powerset _, by simp [coe_empty]⟩
  simp only [C, mem_filter, mem_powerset] at hFmax
  obtain ⟨hFA, hF⟩ := hFmax.1
  refine ⟨F, hFA, le_of_mul_le_mul_right ?_ (by positivity : (0 : Real) < #B), fun a ha => ?_⟩
  · calc
      (#F * #B : Real) = #(F * B) := by
        rw [card_mul_iff.2 <| pairwiseDisjoint_smul_iff.1 hF]; rw [Nat.cast_mul]
      _ <= #(A * B) := by gcongr
      _ <= K * #B := hK
  by_cases hau : a in F
  · exact subset_mul_left _ hB.one_mem_div hau
  by_cases! H : forall b in F, Disjoint (a • B) (b • B)
  · refine (hFmax.not_gt ?_ <| ssubset_insert hau).elim
    rw [insert_subset_iff]; rw [coe_insert]
    exact ⟨⟨ha, hFA⟩, hF.insert fun _ hb _ => H _ hb⟩
  simp_rw [not_disjoint_iff, ← inv_smul_mem_iff] at H
  obtain ⟨b, hb, c, hc₁, hc₂⟩ := H
  exact mem_mul.2 ⟨b, hb, b⁻¹ * a, mem_div.2 ⟨_, hc₂, _, hc₁, by simp⟩, by simp⟩

中文:
定理 ruzsa_covering_mul
  条件: (hB : B.非空) (hK : #(A * B) <= K * #B)
  证明: by
  have : forall F, Decidable ((F : Set G).PairwiseDisjoint (· • B)) := fun F => Classical.dec _
  set C := {F in A.powerset | (SetLike.coe F).PairwiseDisjoint (· • B)}
obtain ⟨F, hFmax⟩ := C.exists_maximal filter_nonempty_iff.2
    ⟨∅, empty_mem_powerset _, by simp [coe_empty]⟩
  simp only [C, mem_filter, mem_powerset] at hFmax
  obtain ⟨hFA, hF⟩ := hFmax.1
  refine ⟨F, hFA, le_of_mul_le_mul_right ?_ (by positivity : (0 : Real) < #B), fun a ha => ?_⟩
  · calc
      (#F * #B : Real) = #(F * B) := by
        rw [card_mul_iff.2 <| pairwiseDisjoint_smul_iff.1 hF]; rw [Nat.cast_mul]
      _ <= #(A * B) := by gcongr
      _ <= K * #B := hK
  by_cases hau : a in F
  · exact subset_mul_left _ hB.one_mem_div hau
  by_cases! H : forall b in F, Disjoint (a • B) (b • B)
  · refine (hFmax.not_gt ?_ <| ssubset_insert hau).elim
    rw [insert_subset_iff]; rw [coe_insert]
    exact ⟨⟨ha, hFA⟩, hF.insert fun _ hb _ => H _ hb⟩
  simp_rw [not_disjoint_iff, ← inv_smul_mem_iff] at H
  obtain ⟨b, hb, c, hc₁, hc₂⟩ := H
  exact mem_mul.2 ⟨b, hb, b⁻¹ * a, mem_div.2 ⟨_, hc₂, _, hc₁, by simp⟩, by simp⟩

Depends on / 依赖: A.powerset, C.exists_maximal, Classical, Classical.dec, Decidable, PairwiseDisjoint, SetLike, SetLike.coe, card_mul_if, coe_empty, empty_mem_powerset, exists_maximal, filter_nonempty_iff, le_of_mul_le_mul_right, mem_filter, mem_powerset, powerset
-/
theorem ruzsa_covering_mul (hB : B.Nonempty) (hK : #(A * B) <= K * #B) :
    exists F subseteq A, #F <= K ∧ A subseteq F * (B / B) := by
  have : forall F, Decidable ((F : Set G).PairwiseDisjoint (· • B)) := fun F => Classical.dec _
  set C := {F in A.powerset | (SetLike.coe F).PairwiseDisjoint (· • B)}
obtain ⟨F, hFmax⟩ := C.exists_maximal filter_nonempty_iff.2
    ⟨∅, empty_mem_powerset _, by simp [coe_empty]⟩
  simp only [C, mem_filter, mem_powerset] at hFmax
  obtain ⟨hFA, hF⟩ := hFmax.1
  refine ⟨F, hFA, le_of_mul_le_mul_right ?_ (by positivity : (0 : Real) < #B), fun a ha => ?_⟩
  · calc
      (#F * #B : Real) = #(F * B) := by
        rw [card_mul_iff.2 <| pairwiseDisjoint_smul_iff.1 hF]; rw [Nat.cast_mul]
      _ <= #(A * B) := by gcongr
      _ <= K * #B := hK
  by_cases hau : a in F
  · exact subset_mul_left _ hB.one_mem_div hau
  by_cases! H : forall b in F, Disjoint (a • B) (b • B)
  · refine (hFmax.not_gt ?_ <| ssubset_insert hau).elim
    rw [insert_subset_iff]; rw [coe_insert]
    exact ⟨⟨ha, hFA⟩, hF.insert fun _ hb _ => H _ hb⟩
  simp_rw [not_disjoint_iff, ← inv_smul_mem_iff] at H
  obtain ⟨b, hb, c, hc₁, hc₂⟩ := H
  exact mem_mul.2 ⟨b, hb, b⁻¹ * a, mem_div.2 ⟨_, hc₂, _, hc₁, by simp⟩, by simp⟩

end Finset

namespace Set
variable {A B : Set G}

/-- **Ruzsa's covering lemma** for sets. See also `Finset.ruzsa_covering_mul`. -/
@[to_additive /-- **Ruzsa's covering lemma** for sets. See also `Finset.ruzsa_covering_add`. -/]
/--
lemma `ruzsa_covering_mul` / 引理 `ruzsa_covering_mul`

English:
lemma ruzsa_covering_mul
  statement: (hA : A.Finite) (hB : B.Finite) (hB₀ : B.Nonempty)
  proof: by
  lift A to Finset G using hA
  lift B to Finset G using hB
  classical
  obtain ⟨F, hFA, hF, hAF⟩ := Finset.ruzsa_covering_mul hB₀ (by simpa [← Finset.coe_mul] using hK)
  exact ⟨F, by norm_cast; simp [*]⟩

中文:
引理 ruzsa_covering_mul
  结论: (hA : A.有限) (hB : B.有限) (hB₀ : B.非空)
  证明: by
  lift A to Finset G using hA
  lift B to Finset G using hB
  classical
  obtain ⟨F, hFA, hF, hAF⟩ := Finset.ruzsa_covering_mul hB₀ (by simpa [← Finset.coe_mul] using hK)
  exact ⟨F, by norm_cast; simp [*]⟩

Depends on / 依赖: Finset, Finset.coe_mul, Finset.ruzsa_covering_mul, classical, coe_mul, ruzsa_covering_mul
-/
lemma ruzsa_covering_mul (hA : A.Finite) (hB : B.Finite) (hB₀ : B.Nonempty)
    (hK : Nat.card (A * B) <= K * Nat.card B) :
    exists F subseteq A, Nat.card F <= K ∧ A subseteq F * (B / B) ∧ F.Finite := by
  lift A to Finset G using hA
  lift B to Finset G using hB
  classical
  obtain ⟨F, hFA, hF, hAF⟩ := Finset.ruzsa_covering_mul hB₀ (by simpa [← Finset.coe_mul] using hK)
  exact ⟨F, by norm_cast; simp [*]⟩

end Set
