/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Logic.Embedding.Set

/-!
# Lemmas on finiteness of sets

This file should contain lemmas that prove some result under the *assumption* of `Set.Finite`.
If your proof has as *result* `Set.Finite`, then it should go to a more specific file.

## Tags

finite sets
-/

public section

assert_not_exists IsOrderedRing MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set


/--
theorem `Finite.fin_embedding` / 定理 `Finite.fin_embedding`

English:
theorem Finite.fin_embedding
  given: {s : Set α} (h : s.Finite)
  proof: ⟨_, (Fintype.equivFin (h.toFinset : Set α)).symm.asEmbedding, by
    simp only [Finset.coe_sort_coe, Equiv.asEmbedding_range, Finite.coe_toFinset, ofPred_mem_eq]⟩

中文:
定理 有限.fin_embedding
  条件: {s : 集合 α} (h : s.有限)
  证明: ⟨_, (Fintype.equivFin (h.toFinset : Set α)).symm.asEmbedding, by
    simp only [Finset.coe_sort_coe, Equiv.asEmbedding_range, Finite.coe_toFinset, ofPred_mem_eq]⟩

Depends on / 依赖: Equiv.asEmbedding_range, Finite, Finite.coe_toFinset, Finset, Finset.coe_sort_coe, Fintype, Fintype.equivFin, asEmbedding, asEmbedding_range, coe_sort_coe, coe_toFinset, equivFin, h.toFinset, ofPred_mem_eq, symm.asEmbedding, toFinset
-/
theorem Finite.fin_embedding {s : Set α} (h : s.Finite) :
    exists (n : Nat) (f : Fin n ↪ α), range f = s :=
  ⟨_, (Fintype.equivFin (h.toFinset : Set α)).symm.asEmbedding, by
    simp only [Finset.coe_sort_coe, Equiv.asEmbedding_range, Finite.coe_toFinset, ofPred_mem_eq]⟩

/--
theorem `Finite.fin_param` / 定理 `Finite.fin_param`

English:
theorem Finite.fin_param
  given: {s : Set α} (h : s.Finite)
  proof: let ⟨n, f, hf⟩ := h.fin_embedding
  ⟨n, f, f.injective, hf⟩

中文:
定理 有限.fin_param
  条件: {s : 集合 α} (h : s.有限)
  证明: let ⟨n, f, hf⟩ := h.fin_embedding
  ⟨n, f, f.injective, hf⟩

Depends on / 依赖: f.injective, fin_embedding, h.fin_embedding, injective
-/
theorem Finite.fin_param {s : Set α} (h : s.Finite) :
    exists (n : Nat) (f : Fin n -> α), Injective f ∧ range f = s :=
  let ⟨n, f, hf⟩ := h.fin_embedding
  ⟨n, f, f.injective, hf⟩

/--
theorem `Finite.induction_to` / 定理 `Finite.induction_to`

English:
theorem Finite.induction_to
  statement: {C : Set α -> Prop} {S : Set α} (h : S.Finite)
  proof: by
  have : Finite S := Finite.to_subtype h
  have : Finite {T : Set α // T subseteq S} := Finite.of_equiv (Set S) (Equiv.Set.powerset S).symm
  rw [← Subtype.coe_mk (p := (· subseteq S)) _ le_rfl]
  rw [← Subtype.coe_mk (p := (· subseteq S)) _ hS0] at H0
  refine Finite.to_wellFoundedGT.wf.induction_bot' (fun s hs hs' => ?_) H0
  obtain ⟨a, ⟨ha1, ha2⟩, ha'⟩ := H1 s (ssubset_of_ne_of_subset hs s.2) hs'
  exact ⟨⟨insert a s.1, insert_subset ha1 s.2⟩, Set.ssubset_insert ha2, ha'⟩

中文:
定理 有限.induction_to
  结论: {C : 集合 α -> 命题} {S : 集合 α} (h : S.有限)
  证明: by
  have : Finite S := Finite.to_subtype h
  have : Finite {T : Set α // T subseteq S} := Finite.of_equiv (Set S) (Equiv.Set.powerset S).symm
  rw [← Subtype.coe_mk (p := (· subseteq S)) _ le_rfl]
  rw [← Subtype.coe_mk (p := (· subseteq S)) _ hS0] at H0
  refine Finite.to_wellFoundedGT.wf.induction_bot' (fun s hs hs' => ?_) H0
  obtain ⟨a, ⟨ha1, ha2⟩, ha'⟩ := H1 s (ssubset_of_ne_of_subset hs s.2) hs'
  exact ⟨⟨insert a s.1, insert_subset ha1 s.2⟩, Set.ssubset_insert ha2, ha'⟩

Depends on / 依赖: Equiv.Set.powerset, Finite, Finite.of_equiv, Finite.to_subtype, Finite.to_wellFoundedGT.wf.induction_bot, Set.ssubset_insert, Subtype, Subtype.coe_mk, coe_mk, induction_bot, insert, insert_subset, le_rfl, of_equiv, powerset, ssubset_insert, ssubset_of_ne_of_subset, subseteq, to_subtype, to_wellFoundedGT
-/
theorem Finite.induction_to {C : Set α -> Prop} {S : Set α} (h : S.Finite)
    (S0 : Set α) (hS0 : S0 subseteq S) (H0 : C S0) (H1 : forall s ⊂ S, C s -> exists a in S \ s, C (insert a s)) :
    C S := by
  have : Finite S := Finite.to_subtype h
  have : Finite {T : Set α // T subseteq S} := Finite.of_equiv (Set S) (Equiv.Set.powerset S).symm
  rw [← Subtype.coe_mk (p := (· subseteq S)) _ le_rfl]
  rw [← Subtype.coe_mk (p := (· subseteq S)) _ hS0] at H0
  refine Finite.to_wellFoundedGT.wf.induction_bot' (fun s hs hs' => ?_) H0
  obtain ⟨a, ⟨ha1, ha2⟩, ha'⟩ := H1 s (ssubset_of_ne_of_subset hs s.2) hs'
  exact ⟨⟨insert a s.1, insert_subset ha1 s.2⟩, Set.ssubset_insert ha2, ha'⟩

/--
theorem `Finite.induction_to_univ` / 定理 `Finite.induction_to_univ`

English:
theorem Finite.induction_to_univ
  statement: [Finite α] {C : Set α -> Prop} (S0 : Set α)
  proof: finite_univ.induction_to S0 (subset_univ S0) H0 (by simpa [ssubset_univ_iff])

中文:
定理 有限.induction_to_univ
  结论: [有限 α] {C : 集合 α -> 命题} (S0 : 集合 α)
  证明: finite_univ.induction_to S0 (subset_univ S0) H0 (by simpa [ssubset_univ_iff])

Depends on / 依赖: finite_univ, finite_univ.induction_to, induction_to, ssubset_univ_iff, subset_univ
-/
theorem Finite.induction_to_univ [Finite α] {C : Set α -> Prop} (S0 : Set α)
    (H0 : C S0) (H1 : forall S != univ, C S -> exists a ∉ S, C (insert a S)) : C univ :=
  finite_univ.induction_to S0 (subset_univ S0) H0 (by simpa [ssubset_univ_iff])

/--
theorem `sUnion_finite_eq_univ` / 定理 `sUnion_finite_eq_univ`

English:
theorem sUnion_finite_eq_univ
  given: {X : Type*}
  statement: ⋃₀ {(s : Set X) | Set.Finite s} = Set.univ
  proof: sUnion_eq_univ_iff.mpr fun x => ⟨{x}, finite_singleton x, rfl⟩

中文:
定理 sUnion_finite_eq_univ
  条件: {X : 类型}
  结论: ⋃₀ {(s : 集合 X) | 集合.有限 s} = 集合.univ
  证明: sUnion_eq_univ_iff.mpr fun x => ⟨{x}, finite_singleton x, rfl⟩

Depends on / 依赖: finite_singleton, sUnion_eq_univ_iff, sUnion_eq_univ_iff.mpr
-/
theorem sUnion_finite_eq_univ {X : Type*} : ⋃₀ {(s : Set X) | Set.Finite s} = Set.univ :=
  sUnion_eq_univ_iff.mpr fun x => ⟨{x}, finite_singleton x, rfl⟩

/-! ### Infinite sets -/

variable {s t : Set α}


/--
theorem `exists_min_image` / 定理 `exists_min_image`

English:
theorem exists_min_image
  given: [LinearOrder β] (s : Set α) (f : α -> β) (h1 : s.Finite)

中文:
定理 存在_min_image
  条件: [线性序 β] (s : 集合 α) (f : α -> β) (h1 : s.有限)
-/
theorem exists_min_image [LinearOrder β] (s : Set α) (f : α -> β) (h1 : s.Finite) :
    s.Nonempty -> exists a in s, forall b in s, f a <= f b
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, Finite.mem_toFinset] using
      h1.toFinset.exists_min_image f ⟨x, h1.mem_toFinset.2 hx⟩

/--
theorem `exists_max_image` / 定理 `exists_max_image`

English:
theorem exists_max_image
  given: [LinearOrder β] (s : Set α) (f : α -> β) (h1 : s.Finite)

中文:
定理 存在_max_image
  条件: [线性序 β] (s : 集合 α) (f : α -> β) (h1 : s.有限)
-/
theorem exists_max_image [LinearOrder β] (s : Set α) (f : α -> β) (h1 : s.Finite) :
    s.Nonempty -> exists a in s, forall b in s, f b <= f a
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, Finite.mem_toFinset] using
      h1.toFinset.exists_max_image f ⟨x, h1.mem_toFinset.2 hx⟩

/--
theorem `exists_lower_bound_image` / 定理 `exists_lower_bound_image`

English:
theorem exists_lower_bound_image
  statement: [Nonempty α] [LinearOrder β] (s : Set α) (f : α -> β)
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ‹Nonempty α›.elim fun a => ⟨a, fun _ => False.elim⟩
  · rcases Set.exists_min_image s f h hs with ⟨x₀, _, hx₀⟩
    exact ⟨x₀, fun x hx => hx₀ x hx⟩

中文:
定理 存在_lower_bound_image
  结论: [非空 α] [线性序 β] (s : 集合 α) (f : α -> β)
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ‹Nonempty α›.elim fun a => ⟨a, fun _ => False.elim⟩
  · rcases Set.exists_min_image s f h hs with ⟨x₀, _, hx₀⟩
    exact ⟨x₀, fun x hx => hx₀ x hx⟩

Depends on / 依赖: False.elim, Nonempty, Set.exists_min_image, eq_empty_or_nonempty, exists_min_image, s.eq_empty_or_nonempty
-/
theorem exists_lower_bound_image [Nonempty α] [LinearOrder β] (s : Set α) (f : α -> β)
    (h : s.Finite) : exists a : α, forall b in s, f a <= f b := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ‹Nonempty α›.elim fun a => ⟨a, fun _ => False.elim⟩
  · rcases Set.exists_min_image s f h hs with ⟨x₀, _, hx₀⟩
    exact ⟨x₀, fun x hx => hx₀ x hx⟩

/--
theorem `exists_upper_bound_image` / 定理 `exists_upper_bound_image`

English:
theorem exists_upper_bound_image
  statement: [Nonempty α] [LinearOrder β] (s : Set α) (f : α -> β)
  proof: exists_lower_bound_image (β := βᵒᵈ) s f h

中文:
定理 存在_upper_bound_image
  结论: [非空 α] [线性序 β] (s : 集合 α) (f : α -> β)
  证明: exists_lower_bound_image (β := βᵒᵈ) s f h

Depends on / 依赖: exists_lower_bound_image
-/
theorem exists_upper_bound_image [Nonempty α] [LinearOrder β] (s : Set α) (f : α -> β)
    (h : s.Finite) : exists a : α, forall b in s, f b <= f a :=
  exists_lower_bound_image (β := βᵒᵈ) s f h

end Set
