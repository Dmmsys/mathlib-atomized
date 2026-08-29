/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne

/-!
# Binary products `Δ[n] ⊗ Δ[1]`

In this file, we define a bijection `SSet.prodStdSimplex.nonDegenerateEquiv₁`
between `Fin (p + 1)` and the type of nondegenerate `(p + 1)`-simplices
of `Δ[p] ⊗ Δ[1]`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial MonoidalCategory Opposite

namespace SSet

namespace prodStdSimplex

variable {p : Nat}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open stdSimplex in
/--
Definition of `nonDegenerateEquiv₁` / `nonDegenerateEquiv₁` 的定义

English:
definition nonDegenerateEquiv₁
  signature: :
  body: Equiv.ofBijective
    (fun i => ⟨⟨stdSimplex.objEquiv.{u}.symm (SimplexCategory.σ i),
      objMk₁ i.succ.castSucc⟩, by
      rw [nonDegenerate_max_dim_iff _ rfl]
      ext j
      dsimp
      by_cases hj : j <= i.castSucc
      · rw [objMk₁_of_castSucc_lt _ _ (by simpa),
          Fin.coe_ofNat_eq_

中文:
定义 nonDegenerateEquiv₁
  签名: :
  定义体: Equiv.ofBijective
    (fun i => ⟨⟨stdSimplex.objEquiv.{u}.symm (SimplexCategory.σ i),
      objMk₁ i.succ.castSucc⟩, by
      rw [nonDegenerate_max_dim_iff _ rfl]
      ext j
      dsimp
      by_cases hj : j <= i.castSucc
      · rw [objMk₁_of_castSucc_lt _ _ (by simpa),
          Fin.coe_ofNat_eq_

Depends on / 依赖: Equiv.ofBijective, Fin.coe_ofNat_eq_mod, Fin.predA, Fin.predAbove_of_le_castSucc, Nat.zero_mod, SimplexCategory, add_zero, castSucc, coe_ofNat_eq_mod, i.castSucc, i.predAbove, i.succ.castSucc, nonDegenerate_max_dim_iff, not_le, objEquiv, objEquiv_symm_apply, ofBijective, predAbove, predAbove_of_le_castSucc, stdSimplex
-/
noncomputable def nonDegenerateEquiv₁ :
    Fin (p + 1) ≃ (Δ[p] otimes Δ[1] : SSet.{u}).nonDegenerate (p + 1) :=
  Equiv.ofBijective
    (fun i => ⟨⟨stdSimplex.objEquiv.{u}.symm (SimplexCategory.σ i),
      objMk₁ i.succ.castSucc⟩, by
      rw [nonDegenerate_max_dim_iff _ rfl]
      ext j
      dsimp
      by_cases hj : j <= i.castSucc
      · rw [objMk₁_of_castSucc_lt _ _ (by simpa),
          Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero]
        change (i.predAbove j : Nat) = _
        simp [Fin.predAbove_of_le_castSucc _ _ hj]
      · simp only [not_le] at hj
        rw [objMk₁_of_le_castSucc _ _ (by simpa)]; rw [objEquiv_symm_apply]
        change (i.predAbove j : Nat) + 1 = _
        rw [Fin.predAbove_of_castSucc_lt _ _ hj]; rw [Fin.val_pred]
        lia⟩) (by
    refine ⟨fun _ _ h => ?_, fun ⟨⟨s₁, s₂⟩, hs⟩ => ?_⟩
    · simpa using stdSimplex.objMk₁_injective (congr_arg (Prod.snd ∘ Subtype.val) h)
    · rw [nonDegenerate_max_dim_iff _ rfl] at hs
      obtain ⟨i, rfl⟩ := stdSimplex.objMk₁_surjective s₂
      obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (i := i) (by
        rintro rfl
        have := DFunLike.congr_fun hs 0
        simp only [orderHomOfSimplex_coe,
          stdSimplex.objMk₁_of_le_castSucc (0 : Fin (p + 3)) 0 (by simp)] at this
        simp at this)
      obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
      · exact ⟨i, nonDegenerate_ext₂ rfl rfl⟩
      · have := DFunLike.congr_fun hs (Fin.last _)
        simp only [Fin.succ_last, orderHomOfSimplex_coe,
          OrderHom.id_coe, id_eq, Fin.ext_iff, Fin.val_last,
          stdSimplex.objMk₁_of_castSucc_lt (Fin.last (p + 2))
            (Fin.last (p + 1)) (by simp),
          Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero] at this
        lia)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `nonDegenerateEquiv₁_fst` / 引理 `nonDegenerateEquiv₁_fst`

English:
lemma nonDegenerateEquiv₁_fst
  given: (i : Fin (p + 1))
  proof: rfl

中文:
引理 nonDegenerateEquiv₁_fst
  条件: (i : 有限集 (p + 1))
  证明: rfl

Depends on / 依赖: SimplexCategory
-/
lemma nonDegenerateEquiv₁_fst (i : Fin (p + 1)) :
    dsimp% (nonDegenerateEquiv₁ i).1.1 =
      (stdSimplex.objEquiv (m := op ⦋p + 1⦌)).symm (SimplexCategory.σ i) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `nonDegenerateEquiv₁_snd` / 引理 `nonDegenerateEquiv₁_snd`

English:
lemma nonDegenerateEquiv₁_snd
  given: (i : Fin (p + 1))
  proof: rfl

中文:
引理 nonDegenerateEquiv₁_snd
  条件: (i : 有限集 (p + 1))
  证明: rfl
-/
lemma nonDegenerateEquiv₁_snd (i : Fin (p + 1)) :
    dsimp% (nonDegenerateEquiv₁ i).1.2 =
      stdSimplex.objMk₁ i.succ.castSucc := rfl

end prodStdSimplex

end SSet
