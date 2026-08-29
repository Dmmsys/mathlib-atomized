/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Fin.Tuple.Embedding
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.NatCard

/-! # Existence of embeddings from finite types

Let `s : Set α` be a finite set.

* `Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card`
  If `s.ncard + n ≤ ENat.card α`,
  then there exists an embedding `Fin n ↪ α`
  whose range is disjoint from `s`.

* `Fin.Embedding.exists_embedding_disjoint_range_of_add_le_Nat_card`
  If `α` is finite and `s.ncard + n ≤ Nat.card α`,
  then there exists an embedding `Fin n ↪ α`
  whose range is disjoint from `s`.

* `Fin.Embedding.restrictSurjective_of_add_le_ENatCard`
  If `m + n ≤ ENat.card α`, then the restriction map
  from `Fin (m + n) ↪ α` to `Fin m ↪ α` is surjective.

* `Fin.Embedding.restrictSurjective_of_add_le_natCard`
  If `α` is finite and `m + n ≤ Nat.card α`, then the restriction
  map from `Fin (m + n) ↪ α` to `Fin m ↪ α` is surjective.
-/

public section

open Set Fin Function Function.Embedding

namespace Fin.Embedding

variable {α : Type*} {m n : Nat} {s : Set α}

/--
theorem `exists_embedding_disjoint_range_of_add_le_ENat_card` / 定理 `exists_embedding_disjoint_range_of_add_le_ENat_card`

English:
theorem exists_embedding_disjoint_range_of_add_le_ENat_card
  proof: by
  rsuffices ⟨y⟩ : Nonempty (Fin n ↪ (sᶜ : Set α))
  · use y.trans (subtype _)
    rw [Set.disjoint_right]
    rintro _ ⟨i, rfl⟩
    simpa only [← mem_compl_iff] using! Subtype.coe_prop (y i)
  rcases finite_or_infinite α with hα | hα
  · let _ : Fintype α := Fintype.ofFinite α
    classical
    a

中文:
定理 存在_embedding_disjoint_range_of_add_le_E自然数_card
  证明: by
  rsuffices ⟨y⟩ : Nonempty (Fin n ↪ (sᶜ : Set α))
  · use y.trans (subtype _)
    rw [Set.disjoint_right]
    rintro _ ⟨i, rfl⟩
    simpa only [← mem_compl_iff] using! Subtype.coe_prop (y i)
  rcases finite_or_infinite α with hα | hα
  · let _ : Fintype α := Fintype.ofFinite α
    classical
    a

Depends on / 依赖: ENat.card_eq_coe_natCard, ENat.natCast_add, ENat.natCast_le_natCast, Fintype, Fintype.card_fin, Fintype.ofFinite, Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Nonempty, Set.disjoint_right, Subtype, Subtype.coe_prop, add_le_add_iff_left, card_coe_set_eq, card_eq_coe_natCard, card_eq_fintype_card, card_fin, classical, coe_prop, disjoint_right
-/
theorem exists_embedding_disjoint_range_of_add_le_ENat_card
    [Finite s] (hs : s.ncard + n <= ENat.card α) :
    exists y : Fin n ↪ α, Disjoint s (range y) := by
  rsuffices ⟨y⟩ : Nonempty (Fin n ↪ (sᶜ : Set α))
  · use y.trans (subtype _)
    rw [Set.disjoint_right]
    rintro _ ⟨i, rfl⟩
    simpa only [← mem_compl_iff] using! Subtype.coe_prop (y i)
  rcases finite_or_infinite α with hα | hα
  · let _ : Fintype α := Fintype.ofFinite α
    classical
    apply nonempty_of_card_le
    rwa [Fintype.card_fin, ← add_le_add_iff_left s.ncard,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
        ncard_add_ncard_compl, ← ENat.natCast_le_natCast,
        ← ENat.card_eq_coe_natCard, ENat.natCast_add]
  · exact ⟨valEmbedding.trans s.toFinite.infinite_compl.to_subtype.natEmbedding⟩

/--
theorem `exists_embedding_disjoint_range_of_add_le_Nat_card` / 定理 `exists_embedding_disjoint_range_of_add_le_Nat_card`

English:
theorem exists_embedding_disjoint_range_of_add_le_Nat_card
  proof: by
  apply exists_embedding_disjoint_range_of_add_le_ENat_card
  rwa [← ENat.natCast_add, ENat.card_eq_coe_natCard, ENat.natCast_le_natCast]

中文:
定理 存在_embedding_disjoint_range_of_add_le_自然数_card
  证明: by
  apply exists_embedding_disjoint_range_of_add_le_ENat_card
  rwa [← ENat.natCast_add, ENat.card_eq_coe_natCard, ENat.natCast_le_natCast]

Depends on / 依赖: ENat.card_eq_coe_natCard, ENat.natCast_add, ENat.natCast_le_natCast, card_eq_coe_natCard, exists_embedding_disjoint_range_of_add_le_ENat_card, natCast_add, natCast_le_natCast
-/
theorem exists_embedding_disjoint_range_of_add_le_Nat_card
    [Finite α] (hs : s.ncard + n <= Nat.card α) :
    exists y : Fin n ↪ α, Disjoint s (range y) := by
  apply exists_embedding_disjoint_range_of_add_le_ENat_card
  rwa [← ENat.natCast_add, ENat.card_eq_coe_natCard, ENat.natCast_le_natCast]

/--
theorem `restrictSurjective_of_add_le_ENatCard` / 定理 `restrictSurjective_of_add_le_ENatCard`

English:
theorem restrictSurjective_of_add_le_ENatCard
  given: (hn : m + n <= ENat.card α)
  proof: by
  intro x
  obtain ⟨y, hxy⟩ :=
    exists_embedding_disjoint_range_of_add_le_ENat_card (s := range x)
      (by simpa [← Nat.card_coe_set_eq, Nat.card_range_of_injective x.injective])
  use append hxy
  ext i
  simp [trans_apply, coe_castAddEmb, append]

中文:
定理 restrictSurjective_of_add_le_E自然数Card
  条件: (hn : m + n <= E自然数.card α)
  证明: by
  intro x
  obtain ⟨y, hxy⟩ :=
    exists_embedding_disjoint_range_of_add_le_ENat_card (s := range x)
      (by simpa [← Nat.card_coe_set_eq, Nat.card_range_of_injective x.injective])
  use append hxy
  ext i
  simp [trans_apply, coe_castAddEmb, append]

Depends on / 依赖: Nat.card_coe_set_eq, Nat.card_range_of_injective, append, card_coe_set_eq, card_range_of_injective, coe_castAddEmb, exists_embedding_disjoint_range_of_add_le_ENat_card, injective, trans_apply, x.injective
-/
theorem restrictSurjective_of_add_le_ENatCard (hn : m + n <= ENat.card α) :
    Surjective (fun (x : Fin (m + n) ↪ α) => (Fin.castAddEmb n).trans x) := by
  intro x
  obtain ⟨y, hxy⟩ :=
    exists_embedding_disjoint_range_of_add_le_ENat_card (s := range x)
      (by simpa [← Nat.card_coe_set_eq, Nat.card_range_of_injective x.injective])
  use append hxy
  ext i
  simp [trans_apply, coe_castAddEmb, append]

/--
theorem `restrictSurjective_of_le_ENatCard` / 定理 `restrictSurjective_of_le_ENatCard`

English:
theorem restrictSurjective_of_le_ENatCard
  given: (hmn : m <= n) (hn : n <= ENat.card α)
  proof: by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact Fin.Embedding.restrictSurjective_of_add_le_ENatCard hn

中文:
定理 restrictSurjective_of_le_E自然数Card
  条件: (hmn : m <= n) (hn : n <= E自然数.card α)
  证明: by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact Fin.Embedding.restrictSurjective_of_add_le_ENatCard hn

Depends on / 依赖: Embedding, Fin.Embedding.restrictSurjective_of_add_le_ENatCard, Nat.exists_eq_add_of_le, exists_eq_add_of_le, restrictSurjective_of_add_le_ENatCard
-/
theorem restrictSurjective_of_le_ENatCard (hmn : m <= n) (hn : n <= ENat.card α) :
    Function.Surjective (fun x : Fin n ↪ α => (castLEEmb hmn).trans x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact Fin.Embedding.restrictSurjective_of_add_le_ENatCard hn

/--
theorem `restrictSurjective_of_add_le_natCard` / 定理 `restrictSurjective_of_add_le_natCard`

English:
theorem restrictSurjective_of_add_le_natCard
  given: [Finite α] (hn : m + n <= Nat.card α)
  proof: by
  apply restrictSurjective_of_add_le_ENatCard
  rwa [← ENat.natCast_add, ENat.card_eq_coe_natCard, ENat.natCast_le_natCast]

中文:
定理 restrictSurjective_of_add_le_natCard
  条件: [有限 α] (hn : m + n <= 自然数.card α)
  证明: by
  apply restrictSurjective_of_add_le_ENatCard
  rwa [← ENat.natCast_add, ENat.card_eq_coe_natCard, ENat.natCast_le_natCast]

Depends on / 依赖: ENat.card_eq_coe_natCard, ENat.natCast_add, ENat.natCast_le_natCast, card_eq_coe_natCard, natCast_add, natCast_le_natCast, restrictSurjective_of_add_le_ENatCard
-/
theorem restrictSurjective_of_add_le_natCard [Finite α] (hn : m + n <= Nat.card α) :
    Surjective (fun x : Fin (m + n) ↪ α => (castAddEmb n).trans x) := by
  apply restrictSurjective_of_add_le_ENatCard
  rwa [← ENat.natCast_add, ENat.card_eq_coe_natCard, ENat.natCast_le_natCast]

/--
theorem `restrictSurjective_of_le_natCard` / 定理 `restrictSurjective_of_le_natCard`

English:
theorem restrictSurjective_of_le_natCard
  given: [Finite α] (hmn : m <= n) (hn : n <= Nat.card α)
  proof: by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact Fin.Embedding.restrictSurjective_of_add_le_natCard hn

中文:
定理 restrictSurjective_of_le_natCard
  条件: [有限 α] (hmn : m <= n) (hn : n <= 自然数.card α)
  证明: by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact Fin.Embedding.restrictSurjective_of_add_le_natCard hn

Depends on / 依赖: Embedding, Fin.Embedding.restrictSurjective_of_add_le_natCard, Nat.exists_eq_add_of_le, exists_eq_add_of_le, restrictSurjective_of_add_le_natCard
-/
theorem restrictSurjective_of_le_natCard [Finite α] (hmn : m <= n) (hn : n <= Nat.card α) :
    Function.Surjective (fun x : Fin n ↪ α => (castLEEmb hmn).trans x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact Fin.Embedding.restrictSurjective_of_add_le_natCard hn

end Fin.Embedding
