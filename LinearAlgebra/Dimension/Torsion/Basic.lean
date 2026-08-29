/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Subsingleton

/-!
# Rank and torsion

## Main statements

- `rank_quotient_eq_of_le_torsion` : `rank M/N = rank M` if `N ≤ torsion M`.
- `finrank_quotient_eq_of_le_torsion` : `finrank M/N = finrank M` if `N ≤ torsion M`.
- `finrank_quotient_torsion_eq` : `finrank ℤ (M / torsion M) = finrank ℤ M` for an additive
  commutative group `M`.
-/

public section

open Submodule

set_option backward.isDefEq.respectTransparency false in
/--
theorem `rank_quotient_eq_of_le_torsion` / 定理 `rank_quotient_eq_of_le_torsion`

English:
theorem rank_quotient_eq_of_le_torsion
  statement: {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  proof: (rank_quotient_le M').antisymm by
    nontriviality R
    rw [Module.rank]
    refine ciSup_le fun ⟨s, hs⟩ => LinearIndependent.cardinal_le_rank (v := (M'.mkQ ·)) ?_
    rw [LinearIndepOn]; rw [linearIndependent_iff'] at hs
    simp_rw [linearIndependent_iff', ← map_smul, ← map_sum, mkQ_apply, Quoti

中文:
定理 rank_quotient_eq_of_le_torsion
  结论: {R M : 类型} [CommRing R] [AddCommGroup M] [Module R M]
  证明: (rank_quotient_le M').antisymm by
    nontriviality R
    rw [Module.rank]
    refine ciSup_le fun ⟨s, hs⟩ => LinearIndependent.cardinal_le_rank (v := (M'.mkQ ·)) ?_
    rw [LinearIndepOn]; rw [linearIndependent_iff'] at hs
    simp_rw [linearIndependent_iff', ← map_smul, ← map_sum, mkQ_apply, Quoti

Depends on / 依赖: Finset, Finset.smul_sum, LinearIndepOn, LinearIndependent, LinearIndependent.cardinal_le_rank, Module, Module.rank, NNReal, NNReal.eq, Quotient, Quotient.mk_eq_zero, Submonoid, Submonoid.smul_def, _congr_nnnorm_ae, antisymm, cardinal_le_rank, ciSup_le, eLpNorm, hfg.mono, linearIndependent_iff
-/
theorem rank_quotient_eq_of_le_torsion {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {M' : Submodule R M} (hN : M' <= torsion R M) : Module.rank R (M ⧸ M') = Module.rank R M :=
(rank_quotient_le M').antisymm by
    nontriviality R
    rw [Module.rank]
    refine ciSup_le fun ⟨s, hs⟩ => LinearIndependent.cardinal_le_rank (v := (M'.mkQ ·)) ?_
    rw [LinearIndepOn]; rw [linearIndependent_iff'] at hs
    simp_rw [linearIndependent_iff', ← map_smul, ← map_sum, mkQ_apply, Quotient.mk_eq_zero]
    intro t g hg i hi
    obtain ⟨r, hg⟩ := hN hg
    simp_rw [Finset.smul_sum, Submonoid.smul_def, smul_smul] at hg
    exact r.prop.2 _ (mul_comm (g i) r ▸ hs t _ hg i hi)

/--
theorem `finrank_quotient_eq_of_le_torsion` / 定理 `finrank_quotient_eq_of_le_torsion`

English:
theorem finrank_quotient_eq_of_le_torsion
  statement: {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  proof: congr_arg Cardinal.toNat (rank_quotient_eq_of_le_torsion hN)

中文:
定理 finrank_quotient_eq_of_le_torsion
  结论: {R M : 类型} [CommRing R] [AddCommGroup M] [Module R M]
  证明: congr_arg Cardinal.toNat (rank_quotient_eq_of_le_torsion hN)

Depends on / 依赖: Cardinal, Cardinal.toNat, _congr_enorm_ae, congr_arg, eLpNorm, fun_comp, hfg.fun_comp, rank_quotient_eq_of_le_torsion
-/
theorem finrank_quotient_eq_of_le_torsion {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {M' : Submodule R M} (hN : M' <= torsion R M) :
    Module.finrank R (M ⧸ M') = Module.finrank R M :=
  congr_arg Cardinal.toNat (rank_quotient_eq_of_le_torsion hN)

/--
theorem `finrank_quotient_torsion_eq` / 定理 `finrank_quotient_torsion_eq`

English:
theorem finrank_quotient_torsion_eq
  given: {M : Type*} [AddCommGroup M]
  proof: finrank_quotient_eq_of_le_torsion le_of_eq by
    rw [← Submodule.torsion_int]; rw [Submodule.toAddSubgroup_toIntSubmodule]

中文:
定理 finrank_quotient_torsion_eq
  条件: {M : 类型} [AddCommGroup M]
  证明: finrank_quotient_eq_of_le_torsion le_of_eq by
    rw [← Submodule.torsion_int]; rw [Submodule.toAddSubgroup_toIntSubmodule]

Depends on / 依赖: Submodule, Submodule.toAddSubgroup_toIntSubmodule, Submodule.torsion_int, finrank_quotient_eq_of_le_torsion, le_of_eq, toAddSubgroup_toIntSubmodule, torsion_int
-/
theorem finrank_quotient_torsion_eq {M : Type*} [AddCommGroup M] :
    Module.finrank Int (M ⧸ (AddCommGroup.torsion M).toIntSubmodule) = Module.finrank Int M :=
finrank_quotient_eq_of_le_torsion le_of_eq by
    rw [← Submodule.torsion_int]; rw [Submodule.toAddSubgroup_toIntSubmodule]
