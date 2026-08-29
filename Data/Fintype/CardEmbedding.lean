/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Logic.Equiv.Embedding

/-!
# Number of embeddings

This file establishes the cardinality of `α ↪ β` in full generality.
-/

public section


local notation "|" x "|" => Finset.card x

local notation "‖" x "‖" => Fintype.card x

open Function

open Nat

namespace Fintype

/--
theorem `card_embedding_eq_of_unique` / 定理 `card_embedding_eq_of_unique`

English:
theorem card_embedding_eq_of_unique
  given: {α β : Type*} [Unique α] [Fintype β] [Fintype (α ↪ β)]
  proof: card_congr Equiv.uniqueEmbeddingEquivResult

中文:
定理 card_embedding_eq_of_unique
  条件: {α β : 类型} [唯一 α] [有限类型 β] [有限类型 (α ↪ β)]
  证明: card_congr Equiv.uniqueEmbeddingEquivResult

Depends on / 依赖: Equiv.uniqueEmbeddingEquivResult, card_congr, uniqueEmbeddingEquivResult
-/
theorem card_embedding_eq_of_unique {α β : Type*} [Unique α] [Fintype β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = ‖β‖ :=
  card_congr Equiv.uniqueEmbeddingEquivResult

-- Establishes the cardinality of the type of all injections between two finite types.
-- Porting note: `induction α using Fintype.induction_empty_option` can't work with the `Fintype α`
-- instance so instead we make an ugly refine and `dsimp` a lot.
@[simp]
/--
theorem `card_embedding_eq` / 定理 `card_embedding_eq`

English:
theorem card_embedding_eq
  given: {α β : Type*} [Fintype α] [Fintype β] [emb : Fintype (α ↪ β)]
  proof: by
  rw [Subsingleton.elim emb Embedding.fintype]
  refine Fintype.induction_empty_option (P := fun t => ‖t ↪ β‖ = ‖β‖.descFactorial ‖t‖)
        (fun α₁ α₂ h₂ e ih => ?_) (?_) (fun γ h ih => ?_) α <;> clear! α
  · let := Fintype.ofEquiv _ e.symm
    rw [← card_congr (Equiv.embeddingCongr e (Equiv.r

中文:
定理 card_embedding_eq
  条件: {α β : 类型} [有限类型 α] [有限类型 β] [emb : 有限类型 (α ↪ β)]
  证明: by
  rw [Subsingleton.elim emb Embedding.fintype]
  refine Fintype.induction_empty_option (P := fun t => ‖t ↪ β‖ = ‖β‖.descFactorial ‖t‖)
        (fun α₁ α₂ h₂ e ih => ?_) (?_) (fun γ h ih => ?_) α <;> clear! α
  · let := Fintype.ofEquiv _ e.symm
    rw [← card_congr (Equiv.embeddingCongr e (Equiv.r

Depends on / 依赖: DFunLike, DFunLike.ext, Embedding, Embedding.fintype, Embedding.ofIsEmpty, Equiv.embeddingCongr, Equiv.refl, Fintype, Fintype.induction_empty_option, Fintype.ofEquiv, Nat.descFactorial_su, Nat.descFactorial_zero, Subsingleton, Subsingleton.elim, card_congr, card_eq_one_iff, card_option, card_pempty, classical, descFactorial
-/
theorem card_embedding_eq {α β : Type*} [Fintype α] [Fintype β] [emb : Fintype (α ↪ β)] :
    ‖α ↪ β‖ = ‖β‖.descFactorial ‖α‖ := by
  rw [Subsingleton.elim emb Embedding.fintype]
  refine Fintype.induction_empty_option (P := fun t => ‖t ↪ β‖ = ‖β‖.descFactorial ‖t‖)
        (fun α₁ α₂ h₂ e ih => ?_) (?_) (fun γ h ih => ?_) α <;> clear! α
  · let := Fintype.ofEquiv _ e.symm
    rw [← card_congr (Equiv.embeddingCongr e (Equiv.refl β))]; rw [ih]; rw [card_congr e]
  · rw [card_pempty, Nat.descFactorial_zero, card_eq_one_iff]
    exact ⟨Embedding.ofIsEmpty, fun x => DFunLike.ext _ _ isEmptyElim⟩
  · classical
    rw [card_option]; rw [Nat.descFactorial_succ]; rw [card_congr (Embedding.optionEmbeddingEquiv γ β)]; rw [card_sigma]; rw [← ih]
    simp only [Fintype.card_compl_set, Fintype.card_range, Finset.sum_const, Finset.card_univ,
      Nat.nsmul_eq_mul, mul_comm]

/--
theorem `card_embedding_eq_of_infinite` / 定理 `card_embedding_eq_of_infinite`

English:
theorem card_embedding_eq_of_infinite
  given: {α β : Type*} [Infinite α] [Finite β] [Fintype (α ↪ β)]
  proof: card_eq_zero

中文:
定理 card_embedding_eq_of_infinite
  条件: {α β : 类型} [无限 α] [有限 β] [有限类型 (α ↪ β)]
  证明: card_eq_zero

Depends on / 依赖: card_eq_zero
-/
theorem card_embedding_eq_of_infinite {α β : Type*} [Infinite α] [Finite β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = 0 :=
  card_eq_zero

end Fintype
