/-
Copyright (c) 2024 Thomas Lanard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Inna Capdeboscq, Johan Commelin, Thomas Lanard, Peiran Wu
-/
module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
/-!
# Cardinal of the general linear group over finite rings

This file computes the cardinal of the general linear group over finite rings.

## Main statements

* `card_linearIndependent` gives the cardinal of the set of linearly independent vectors over a
  finite-dimensional vector space over a finite field.
* `Matrix.card_GL_field` gives the cardinal of the general linear group over a finite field.
-/

@[expose] public section

open LinearMap Module

section LinearIndependent

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Finite V]

local notation "q" => Fintype.card K
local notation "n" => Module.finrank K V

attribute [local instance] Fintype.ofFinite in
open Fintype in
/--
theorem `card_linearIndependent` / 定理 `card_linearIndependent`

English:
theorem card_linearIndependent
  given: {k : Nat} (hk : k <= n)
  proof: by
  rw [Nat.card_eq_fintype_card]
  induction k with
  | zero =>
      have : Unique { s : Fin 0 -> V // (⊤ : Submodule K (Fin 0 ->₀ K)) = ⊥ } :=
        uniqueOfSubsingleton ⟨0, Subsingleton.elim ..⟩
      simp_rw [linearIndependent_iff_ker, Finsupp.linearCombination_fin_zero, ker_zero,
        Finset.univ_eq_empty, Finset.prod_empty, card_unique]
  | succ k ih =>
      have (s : { s : Fin k -> V // LinearIndependent K s }) :
          card ((Submodule.span K (Set.range (s : Fin k -> V)))ᶜ : Set (V)) =
          (q) ^ n - (q) ^ k := by
            rw [card_compl_set]; rw [Module.card_eq_pow_finrank (K := K)
            (V := ((Submodule.span K (Set.range (s : Fin k -> V))) : Set (V)))]
            simp only [SetLike.coe_sort_coe, finrank_span_eq_card s.2, card_fin]
            rw [Module.card_eq_pow_finrank (K := K)]
      simp [card_congr (equiv_linearIndependent k), sum_congr _ _ this, ih (Nat.le_of_succ_le hk),
        mul_comm, Fin.prod_univ_succAbove _ (Fin.last k), -Set.fintypeCard_eq_ncard]

中文:
定理 card_linearIndependent
  条件: {k : 自然数} (hk : k <= n)
  证明: by
  rw [Nat.card_eq_fintype_card]
  induction k with
  | zero =>
      have : Unique { s : Fin 0 -> V // (⊤ : Submodule K (Fin 0 ->₀ K)) = ⊥ } :=
        uniqueOfSubsingleton ⟨0, Subsingleton.elim ..⟩
      simp_rw [linearIndependent_iff_ker, Finsupp.linearCombination_fin_zero, ker_zero,
        Finset.univ_eq_empty, Finset.prod_empty, card_unique]
  | succ k ih =>
      have (s : { s : Fin k -> V // LinearIndependent K s }) :
          card ((Submodule.span K (Set.range (s : Fin k -> V)))ᶜ : Set (V)) =
          (q) ^ n - (q) ^ k := by
            rw [card_compl_set]; rw [Module.card_eq_pow_finrank (K := K)
            (V := ((Submodule.span K (Set.range (s : Fin k -> V))) : Set (V)))]
            simp only [SetLike.coe_sort_coe, finrank_span_eq_card s.2, card_fin]
            rw [Module.card_eq_pow_finrank (K := K)]
      simp [card_congr (equiv_linearIndependent k), sum_congr _ _ this, ih (Nat.le_of_succ_le hk),
        mul_comm, Fin.prod_univ_succAbove _ (Fin.last k), -Set.fintypeCard_eq_ncard]

Depends on / 依赖: Finset, Finset.prod_empty, Finset.univ_eq_empty, Finsupp, Finsupp.linearCombination_fin_zero, LinearIndependent, Nat.card_eq_fintype_card, Set.range, Submodule, Submodule.span, Subsingleton, Subsingleton.elim, Unique, card_compl_set, card_eq_fintype_card, card_unique, ker_zero, linearCombination_fin_zero, linearIndependent_iff_ker, prod_empty
-/
theorem card_linearIndependent {k : Nat} (hk : k <= n) :
    Nat.card { s : Fin k -> V // LinearIndependent K s } =
      ∏ i : Fin k, (q ^ n - q ^ i.val) := by
  rw [Nat.card_eq_fintype_card]
  induction k with
  | zero =>
      have : Unique { s : Fin 0 -> V // (⊤ : Submodule K (Fin 0 ->₀ K)) = ⊥ } :=
        uniqueOfSubsingleton ⟨0, Subsingleton.elim ..⟩
      simp_rw [linearIndependent_iff_ker, Finsupp.linearCombination_fin_zero, ker_zero,
        Finset.univ_eq_empty, Finset.prod_empty, card_unique]
  | succ k ih =>
      have (s : { s : Fin k -> V // LinearIndependent K s }) :
          card ((Submodule.span K (Set.range (s : Fin k -> V)))ᶜ : Set (V)) =
          (q) ^ n - (q) ^ k := by
            rw [card_compl_set]; rw [Module.card_eq_pow_finrank (K := K)
            (V := ((Submodule.span K (Set.range (s : Fin k -> V))) : Set (V)))]
            simp only [SetLike.coe_sort_coe, finrank_span_eq_card s.2, card_fin]
            rw [Module.card_eq_pow_finrank (K := K)]
      simp [card_congr (equiv_linearIndependent k), sum_congr _ _ this, ih (Nat.le_of_succ_le hk),
        mul_comm, Fin.prod_univ_succAbove _ (Fin.last k), -Set.fintypeCard_eq_ncard]

end LinearIndependent

namespace Matrix

section field

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]

local notation "q" => Fintype.card 𝔽

variable (n : Nat)

/--
Definition of `equiv_GL_linearindependent` / `equiv_GL_linearindependent` 的定义

English:
definition equiv_GL_linearindependent
  signature: :
  body: ⟨M.1.col, by
    apply linearIndependent_iff_card_eq_finrank_span.2
    rw [Set.finrank]; rw [← rank_eq_finrank_span_cols]; rw [rank_unit]⟩
invFun M := GeneralLinearGroup.mk'' (transpose (M.1)) by
    classical
    let b := basisOfPiSpaceOfLinearIndependent M.2
    have := (Pi.basisFun 𝔽 (Fin n)).invertibleToMatrix b
    rw [← Basis.coePiBasisFun.toMatrix_eq_transpose]; rw [← coe_basisOfPiSpaceOfLinearIndependent M.2]
    exact isUnit_det_of_invertible _
  right_inv := by exact congrFun rfl

中文:
定义 equiv_GL_linearindependent
  签名: :
  定义体: ⟨M.1.col, by
    apply linearIndependent_iff_card_eq_finrank_span.2
    rw [Set.finrank]; rw [← rank_eq_finrank_span_cols]; rw [rank_unit]⟩
invFun M := GeneralLinearGroup.mk'' (transpose (M.1)) by
    classical
    let b := basisOfPiSpaceOfLinearIndependent M.2
    have := (Pi.basisFun 𝔽 (Fin n)).invertibleToMatrix b
    rw [← Basis.coePiBasisFun.toMatrix_eq_transpose]; rw [← coe_basisOfPiSpaceOfLinearIndependent M.2]
    exact isUnit_det_of_invertible _
  right_inv := by exact congrFun rfl

Depends on / 依赖: Basis.coePiBasisFun.toMatrix_eq_transpose, GeneralLinearGroup, GeneralLinearGroup.mk, Pi.basisFun, Set.finrank, basisFun, basisOfPiSpaceOfLinearIndependent, classical, coePiBasisFun, coe_basisOfPiSpaceOfLinearIndependent, finrank, invFun, invertibleToMatrix, isUnit_det_of_invertible, linearIndependent_iff_card_eq_finrank_span, rank_eq_finrank_span_cols, rank_unit, right_inv, toMatrix_eq_transpose, transpose
-/
noncomputable def equiv_GL_linearindependent :
    GL (Fin n) 𝔽 ≃ { s : Fin n -> Fin n -> 𝔽 // LinearIndependent 𝔽 s } where
  toFun M := ⟨M.1.col, by
    apply linearIndependent_iff_card_eq_finrank_span.2
    rw [Set.finrank]; rw [← rank_eq_finrank_span_cols]; rw [rank_unit]⟩
invFun M := GeneralLinearGroup.mk'' (transpose (M.1)) by
    classical
    let b := basisOfPiSpaceOfLinearIndependent M.2
    have := (Pi.basisFun 𝔽 (Fin n)).invertibleToMatrix b
    rw [← Basis.coePiBasisFun.toMatrix_eq_transpose]; rw [← coe_basisOfPiSpaceOfLinearIndependent M.2]
    exact isUnit_det_of_invertible _
  right_inv := by exact congrFun rfl

/--
theorem `card_GL_field` / 定理 `card_GL_field`

English:
theorem card_GL_field
  proof: by
  rw [Nat.card_congr (equiv_GL_linearindependent n)]; rw [card_linearIndependent]; rw [Module.finrank_fintype_fun_eq_card]; rw [Fintype.card_fin]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, le_refl]

中文:
定理 card_GL_field
  证明: by
  rw [Nat.card_congr (equiv_GL_linearindependent n)]; rw [card_linearIndependent]; rw [Module.finrank_fintype_fun_eq_card]; rw [Fintype.card_fin]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, le_refl]

Depends on / 依赖: Fintype, Fintype.card_fin, Module, Module.finrank_fintype_fun_eq_card, Nat.card_congr, card_congr, card_fin, card_linearIndependent, equiv_GL_linearindependent, finrank_fintype_fun_eq_card, le_refl
-/
theorem card_GL_field :
    Nat.card (GL (Fin n) 𝔽) = ∏ i : (Fin n), (q ^ n - q ^ (i : Nat)) := by
  rw [Nat.card_congr (equiv_GL_linearindependent n)]; rw [card_linearIndependent]; rw [Module.finrank_fintype_fun_eq_card]; rw [Fintype.card_fin]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, le_refl]

end field

end Matrix
