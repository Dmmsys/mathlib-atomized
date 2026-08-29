/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen,
Kim Morrison, Chris Hughes, Anne Baanen, Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Dimension of vector spaces

In this file we provide results about `Module.rank` and `Module.finrank` of vector spaces
over division rings.

## Main statements

For vector spaces (i.e. modules over a field), we have

* `rank_quotient_add_rank_of_divisionRing`: if `V₁` is a submodule of `V`, then
  `Module.rank (V/V₁) + Module.rank V₁ = Module.rank V`.
* `rank_range_add_rank_ker`: the rank-nullity theorem.

See also `Mathlib/LinearAlgebra/Dimension/ErdosKaplansky.lean` for the Erdős-Kaplansky theorem.

-/

public section


noncomputable section

universe u₀ u v v' v'' u₁' w w'

variable {K : Type u} {V V₁ V₂ V₃ : Type v}
variable {ι : Type w}

open Cardinal Basis Submodule Function Set

section Module

section DivisionRing

variable [DivisionRing K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup V₁] [Module K V₁]

/--
theorem `Module.Basis.finite_ofVectorSpaceIndex_of_rank_lt_aleph0` / 定理 `Module.Basis.finite_ofVectorSpaceIndex_of_rank_lt_aleph0`

English:
theorem Module.Basis.finite_ofVectorSpaceIndex_of_rank_lt_aleph0
  given: (h : Module.rank K V < ℵ₀)
  proof: Set.finite_def.2 (Basis.ofVectorSpace K V).nonempty_fintype_index_of_rank_lt_aleph0 h

中文:
定理 Module.Basis.finite_ofVectorSpaceIndex_of_rank_lt_aleph0
  条件: (h : Module.rank K V < ℵ₀)
  证明: Set.finite_def.2 (Basis.ofVectorSpace K V).nonempty_fintype_index_of_rank_lt_aleph0 h

Depends on / 依赖: Basis.ofVectorSpace, Set.finite_def, finite_def, nonempty_fintype_index_of_rank_lt_aleph0, ofVectorSpace
-/
theorem Module.Basis.finite_ofVectorSpaceIndex_of_rank_lt_aleph0 (h : Module.rank K V < ℵ₀) :
    (Basis.ofVectorSpaceIndex K V).Finite :=
Set.finite_def.2 (Basis.ofVectorSpace K V).nonempty_fintype_index_of_rank_lt_aleph0 h

/--
theorem `rank_quotient_add_rank_of_divisionRing` / 定理 `rank_quotient_add_rank_of_divisionRing`

English:
theorem rank_quotient_add_rank_of_divisionRing
  given: (p : Submodule K V)
  proof: by
  let ⟨f⟩ := quotient_prod_linearEquiv p
  exact rank_prod'.symm.trans f.rank_eq

中文:
定理 rank_quotient_add_rank_of_divisionRing
  条件: (p : Submodule K V)
  证明: by
  let ⟨f⟩ := quotient_prod_linearEquiv p
  exact rank_prod'.symm.trans f.rank_eq

Depends on / 依赖: f.rank_eq, quotient_prod_linearEquiv, rank_eq, rank_prod, symm.trans
-/
theorem rank_quotient_add_rank_of_divisionRing (p : Submodule K V) :
    Module.rank K (V ⧸ p) + Module.rank K p = Module.rank K V := by
  let ⟨f⟩ := quotient_prod_linearEquiv p
  exact rank_prod'.symm.trans f.rank_eq

/--
Instance `DivisionRing.hasRankNullity` / 实例 `DivisionRing.hasRankNullity`

English:
instance DivisionRing.hasRankNullity
  signature: : HasRankNullity.{u₀} K where
  body: rank_quotient_add_rank_of_divisionRing
  exists_set_linearIndependent V _ _ := by
    let b := Module.Free.chooseBasis K V
    refine ⟨range b, ?_, b.linearIndependent.linearIndepOn_id⟩
    rw [← lift_injective.eq_iff]; rw [mk_range_eq_of_injective b.injective]; rw [Module.Free.rank_eq_card_chooseBa

中文:
实例 DivisionRing.hasRankNullity
  签名: : HasRankNullity.{u₀} K where
  定义体: rank_quotient_add_rank_of_divisionRing
  exists_set_linearIndependent V _ _ := by
    let b := Module.Free.chooseBasis K V
    refine ⟨range b, ?_, b.linearIndependent.linearIndepOn_id⟩
    rw [← lift_injective.eq_iff]; rw [mk_range_eq_of_injective b.injective]; rw [Module.Free.rank_eq_card_chooseBa

Depends on / 依赖: rank_quotient_add_rank_of_divisionRing
-/
instance DivisionRing.hasRankNullity : HasRankNullity.{u₀} K where
  rank_quotient_add_rank := rank_quotient_add_rank_of_divisionRing
  exists_set_linearIndependent V _ _ := by
    let b := Module.Free.chooseBasis K V
    refine ⟨range b, ?_, b.linearIndependent.linearIndepOn_id⟩
    rw [← lift_injective.eq_iff]; rw [mk_range_eq_of_injective b.injective]; rw [Module.Free.rank_eq_card_chooseBasisIndex]

section

variable [AddCommGroup V₂] [Module K V₂]
variable [AddCommGroup V₃] [Module K V₃]

open LinearMap

/--
theorem `rank_add_rank_split` / 定理 `rank_add_rank_split`

English:
theorem rank_add_rank_split
  statement: (db : V₂ ->ₗ[K] V) (eb : V₃ ->ₗ[K] V) (cd : V₁ ->ₗ[K] V₂)
  proof: by
  have hf : Surjective (coprod db eb) := by
    rwa [← range_eq_top, range_coprod, eq_top_iff]
  conv =>
    rhs
    rw [← rank_prod']; rw [rank_eq_of_surjective hf]
  congr 1
  apply LinearEquiv.rank_eq
  let L : V₁ ->ₗ[K] ker (coprod db eb) :=
LinearMap.codRestrict _ (prod cd (-ce)) by
      si

中文:
定理 rank_add_rank_split
  结论: (db : V₂ ->ₗ[K] V) (eb : V₃ ->ₗ[K] V) (cd : V₁ ->ₗ[K] V₂)
  证明: by
  have hf : Surjective (coprod db eb) := by
    rwa [← range_eq_top, range_coprod, eq_top_iff]
  conv =>
    rhs
    rw [← rank_prod']; rw [rank_eq_of_surjective hf]
  congr 1
  apply LinearEquiv.rank_eq
  let L : V₁ ->ₗ[K] ker (coprod db eb) :=
LinearMap.codRestrict _ (prod cd (-ce)) by
      si

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, LinearEquiv.rank_eq, LinearMap, LinearMap.codRestrict, LinearMap.ext_iff, LinearMap.range_codRestrict, Surjective, add_eq_zero_iff_eq_neg, bot_inf_eq, codRestrict, coprod, eq_top_iff, ext_iff, ker_codRestrict, ker_eq_bot, ker_prod, ofBijective, range_codRestrict, range_coprod
-/
theorem rank_add_rank_split (db : V₂ ->ₗ[K] V) (eb : V₃ ->ₗ[K] V) (cd : V₁ ->ₗ[K] V₂)
    (ce : V₁ ->ₗ[K] V₃) (hde : ⊤ <= LinearMap.range db ⊔ LinearMap.range eb) (hgd : ker cd = ⊥)
    (eq : db.comp cd = eb.comp ce) (eq₂ : forall d e, db d = eb e -> exists c, cd c = d ∧ ce c = e) :
    Module.rank K V + Module.rank K V₁ = Module.rank K V₂ + Module.rank K V₃ := by
  have hf : Surjective (coprod db eb) := by
    rwa [← range_eq_top, range_coprod, eq_top_iff]
  conv =>
    rhs
    rw [← rank_prod']; rw [rank_eq_of_surjective hf]
  congr 1
  apply LinearEquiv.rank_eq
  let L : V₁ ->ₗ[K] ker (coprod db eb) :=
LinearMap.codRestrict _ (prod cd (-ce)) by
      simpa [add_eq_zero_iff_eq_neg] using LinearMap.ext_iff.1 eq
  refine LinearEquiv.ofBijective L ⟨?_, ?_⟩
  · rw [← ker_eq_bot, ker_codRestrict, ker_prod, hgd, bot_inf_eq]
  · rw [← range_eq_top, eq_top_iff, LinearMap.range_codRestrict, ← map_le_iff_le_comap,
      Submodule.map_top, range_subtype]
    rintro ⟨d, e⟩
    have h := eq₂ d (-e)
    simp only [add_eq_zero_iff_eq_neg, LinearMap.prod_apply, mem_ker,
      Prod.mk_inj, coprod_apply, map_neg, neg_apply, LinearMap.mem_range,
      Function.prod_apply] at h ⊢
    grind

end

end DivisionRing

end Module
