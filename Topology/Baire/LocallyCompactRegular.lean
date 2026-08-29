/-
Copyright (c) 2022 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Topology.Sets.Compacts

/-!
# Second Baire theorem

In this file we prove that a locally compact regular topological space has Baire property.
-/

public section

open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X] {s : Set X} [R1Space X] [LocallyCompactSpace X]

/-- **Second Baire theorem**: locally compact R₁ spaces are Baire. -/
instance (priority := 100) BaireSpace.of_t2Space_locallyCompactSpace : BaireSpace X := by
  constructor
  intro f ho hd
  /- To prove that an intersection of open dense subsets is dense, prove that its intersection
    with any open neighbourhood `U` is dense. Define recursively a decreasing sequence `K` of
    compact neighbourhoods: start with some compact neighbourhood inside `U`, then at each step,
    take its interior, intersect with `f n`, then choose a compact neighbourhood inside the
    intersection. -/
  rw [dense_iff_inter_open]
  intro U U_open U_nonempty
  -- Choose an antitone sequence of positive compacts such that `closure (K 0) ⊆ U`
  -- and `closure (K (n + 1)) ⊆ f n` for all `n`
  obtain ⟨K, hK_anti, hKf, hKU⟩ : exists K : Nat -> PositiveCompacts X,
      (forall n, K (n + 1) <= K n) ∧ (forall n, closure ↑(K (n + 1)) subseteq f n) ∧ closure ↑(K 0) subseteq U := by
    rcases U_open.exists_positiveCompacts_closure_subset U_nonempty with ⟨K₀, hK₀⟩
    have : forall (n) (K : PositiveCompacts X),
        exists K' : PositiveCompacts X, closure ↑K' subseteq f n inter interior K := by
      refine fun n K => ((ho n).inter isOpen_interior).exists_positiveCompacts_closure_subset ?_
      rw [inter_comm]
      exact (hd n).inter_open_nonempty _ isOpen_interior K.interior_nonempty
    choose K_next hK_next using this
    -- The next two lines are faster than a single `refine`.
    use Nat.rec K₀ K_next
    refine ⟨fun n => ?_, fun n => (hK_next n _).trans inter_subset_left, hK₀⟩
exact subset_closure.trans (hK_next _ _).trans
      inter_subset_right.trans interior_subset
  -- Prove that `⋂ n : ℕ, closure (K n)` is inside `U ∩ ⋂ n : ℕ, f n`.
  have hK_subset : (⋂ n, closure (K n) : Set X) subseteq U inter ⋂ n, f n := fun x hx => by
    simp only [mem_iInter, mem_inter_iff] at hx ⊢
exact ⟨hKU hx 0, fun n => hKf n hx (n + 1)⟩
  /- Prove that `⋂ n : ℕ, closure (K n)` is not empty, as an intersection of a decreasing sequence
    of nonempty compact closed subsets. -/
  have hK_nonempty : (⋂ n, closure (K n) : Set X).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun n => closure_mono <| hK_anti n) (fun n => (K n).nonempty.closure)
      (K 0).isCompact.closure fun n => isClosed_closure
  exact hK_nonempty.mono hK_subset

/--
theorem `IsGδ.baireSpace_of_t2Space_locallyCompactSpace` / 定理 `IsGδ.baireSpace_of_t2Space_locallyCompactSpace`

English:
theorem IsGδ.baireSpace_of_t2Space_locallyCompactSpace
  given: (hG : IsGδ s)
  statement: BaireSpace s
  proof: by
  have : LocallyCompactSpace (closure s) := isClosed_closure.locallyCompactSpace
  have : BaireSpace (closure s) := .of_t2Space_locallyCompactSpace
  have : BaireSpace ((↑) ⁻¹' s : Set (closure s)) :=
    (hG.preimage continuous_subtype_val).baireSpace_of_dense
    (by simp [Subtype.dense_iff, in

中文:
定理 IsGδ.baireSpace_of_t2Space_locallyCompactSpace
  条件: (hG : IsGδ s)
  结论: BaireSpace s
  证明: by
  have : LocallyCompactSpace (closure s) := isClosed_closure.locallyCompactSpace
  have : BaireSpace (closure s) := .of_t2Space_locallyCompactSpace
  have : BaireSpace ((↑) ⁻¹' s : Set (closure s)) :=
    (hG.preimage continuous_subtype_val).baireSpace_of_dense
    (by simp [Subtype.dense_iff, in

Depends on / 依赖: BaireSpace, Homeomorph, LocallyCompactSpace, Subtype, Subtype.dense_iff, baireSpace_of_dense, closure, continuous_subtype_val, dense_iff, fun_prop, hG.preimage, h_ho, h_homeo, inter_eq_right, inter_eq_right.mpr, isClosed_closure, isClosed_closure.locallyCompactSpace, locallyCompactSpace, of_t2Space_locallyCompactSpace, preimage
-/
theorem IsGδ.baireSpace_of_t2Space_locallyCompactSpace (hG : IsGδ s) : BaireSpace s := by
  have : LocallyCompactSpace (closure s) := isClosed_closure.locallyCompactSpace
  have : BaireSpace (closure s) := .of_t2Space_locallyCompactSpace
  have : BaireSpace ((↑) ⁻¹' s : Set (closure s)) :=
    (hG.preimage continuous_subtype_val).baireSpace_of_dense
    (by simp [Subtype.dense_iff, inter_eq_right.mpr subset_closure])
  have h_homeo : Homeomorph ((↑) ⁻¹' s : Set (closure s)) s := ⟨⟨fun x => ⟨x, x.2⟩,
    fun x => ⟨⟨x, subset_closure x.2⟩, x.2⟩, by grind, by grind⟩, by fun_prop, by fun_prop⟩
  exact h_homeo.baireSpace

@[deprecated (since := "2026-06-04")]
alias IsGδ.of_t2Space_locallyCompactSpace := IsGδ.baireSpace_of_t2Space_locallyCompactSpace
