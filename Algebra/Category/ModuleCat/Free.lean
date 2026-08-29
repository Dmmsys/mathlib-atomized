/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exact sequences with free modules

This file proves results about linear independence and span in exact sequences of modules.

## Main theorems

* `linearIndependent_shortExact`: Given a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of
  `R`-modules and linearly independent families `v : ι → X₁` and `w : ι' → X₃`, we get a linearly
  independent family `ι ⊕ ι' → X₂`
* `span_rightExact`: Given an exact sequence `X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `R`-modules and spanning
  families `v : ι → X₁` and `w : ι' → X₃`, we get a spanning family `ι ⊕ ι' → X₂`
* Using `linearIndependent_shortExact` and `span_rightExact`, we prove `free_shortExact`: In a
  short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` where `X₁` and `X₃` are free, `X₂` is free as well.

## Tags
linear algebra, module, free

-/

@[expose] public section

open CategoryTheory Module

namespace ModuleCat

variable {ι ι' R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)}
  (hS : S.Exact) (hS' : S.ShortExact) {v : ι -> S.X₁}

open CategoryTheory Submodule Set

section LinearIndependent

variable (hv : LinearIndependent R v) {u : ι oplus ι' -> S.X₂}
  (hw : LinearIndependent R (S.g ∘ u ∘ Sum.inr))
  (hm : Mono S.f) (huv : u ∘ Sum.inl = S.f ∘ v)

section
include hS hw huv

/--
theorem `disjoint_span_sum` / 定理 `disjoint_span_sum`

English:
theorem disjoint_span_sum
  statement: Disjoint (span R (range (u ∘ Sum.inl)))
  proof: by
  rw [huv]; rw [disjoint_comm]
  refine Disjoint.mono_right (span_mono (range_comp_subset_range _ _)) ?_
  rw [← LinearMap.coe_range]; rw [span_eq (LinearMap.range S.f.hom)]; rw [hS.moduleCat_range_eq_ker]
  exact range_ker_disjoint hw

include hv hm in

中文:
定理 disjoint_span_sum
  结论: Disjoint (span R (range (u ∘ 和.inl)))
  证明: by
  rw [huv]; rw [disjoint_comm]
  refine Disjoint.mono_right (span_mono (range_comp_subset_range _ _)) ?_
  rw [← LinearMap.coe_range]; rw [span_eq (LinearMap.range S.f.hom)]; rw [hS.moduleCat_range_eq_ker]
  exact range_ker_disjoint hw

include hv hm in

Depends on / 依赖: Disjoint, Disjoint.mono_right, LinearMap, LinearMap.coe_range, LinearMap.range, S.f.hom, coe_range, disjoint_comm, hS.moduleCat_range_eq_ker, moduleCat_range_eq_ker, mono_right, range_comp_subset_range, range_ker_disjoint, span_eq, span_mono
-/
theorem disjoint_span_sum : Disjoint (span R (range (u ∘ Sum.inl)))
    (span R (range (u ∘ Sum.inr))) := by
  rw [huv]; rw [disjoint_comm]
  refine Disjoint.mono_right (span_mono (range_comp_subset_range _ _)) ?_
  rw [← LinearMap.coe_range]; rw [span_eq (LinearMap.range S.f.hom)]; rw [hS.moduleCat_range_eq_ker]
  exact range_ker_disjoint hw

include hv hm in
/--
theorem `linearIndependent_leftExact` / 定理 `linearIndependent_leftExact`

English:
theorem linearIndependent_leftExact
  statement: LinearIndependent R u
  proof: by
  rw [linearIndependent_sum]
  refine ⟨?_, LinearIndependent.of_comp S.g.hom hw, disjoint_span_sum hS hw huv⟩
  rw [huv]; rw [LinearMap.linearIndependent_iff S.f.hom]; swap
  · rw [LinearMap.ker_eq_bot, ← mono_iff_injective]
    infer_instance
  exact hv

中文:
定理 linearIndependent_leftExact
  结论: LinearIndependent R u
  证明: by
  rw [linearIndependent_sum]
  refine ⟨?_, LinearIndependent.of_comp S.g.hom hw, disjoint_span_sum hS hw huv⟩
  rw [huv]; rw [LinearMap.linearIndependent_iff S.f.hom]; swap
  · rw [LinearMap.ker_eq_bot, ← mono_iff_injective]
    infer_instance
  exact hv

Depends on / 依赖: LinearIndependent, LinearIndependent.of_comp, LinearMap, LinearMap.ker_eq_bot, LinearMap.linearIndependent_iff, S.f.hom, S.g.hom, disjoint_span_sum, infer_instance, ker_eq_bot, linearIndependent_iff, linearIndependent_sum, mono_iff_injective, of_comp
-/
theorem linearIndependent_leftExact : LinearIndependent R u := by
  rw [linearIndependent_sum]
  refine ⟨?_, LinearIndependent.of_comp S.g.hom hw, disjoint_span_sum hS hw huv⟩
  rw [huv]; rw [LinearMap.linearIndependent_iff S.f.hom]; swap
  · rw [LinearMap.ker_eq_bot, ← mono_iff_injective]
    infer_instance
  exact hv

end

include hS' hv in
/--
theorem `linearIndependent_shortExact` / 定理 `linearIndependent_shortExact`

English:
theorem linearIndependent_shortExact
  given: {w : ι' -> S.X₃} (hw : LinearIndependent R w)
  proof: by
  apply linearIndependent_leftExact hS'.exact hv _ hS'.mono_f rfl
  dsimp
  convert! hw
  ext
  apply Function.rightInverse_invFun ((epi_iff_surjective _).mp hS'.epi_g)

中文:
定理 linearIndependent_shortExact
  条件: {w : ι' -> S.X₃} (hw : LinearIndependent R w)
  证明: by
  apply linearIndependent_leftExact hS'.exact hv _ hS'.mono_f rfl
  dsimp
  convert! hw
  ext
  apply Function.rightInverse_invFun ((epi_iff_surjective _).mp hS'.epi_g)

Depends on / 依赖: Function, Function.rightInverse_invFun, convert, epi_g, epi_iff_surjective, linearIndependent_leftExact, mono_f, rightInverse_invFun
-/
theorem linearIndependent_shortExact {w : ι' -> S.X₃} (hw : LinearIndependent R w) :
    LinearIndependent R (Sum.elim (S.f ∘ v) (S.g.hom.toFun.invFun ∘ w)) := by
  apply linearIndependent_leftExact hS'.exact hv _ hS'.mono_f rfl
  dsimp
  convert! hw
  ext
  apply Function.rightInverse_invFun ((epi_iff_surjective _).mp hS'.epi_g)

end LinearIndependent

section Span

include hS in
/--
theorem `span_exact` / 定理 `span_exact`

English:
theorem span_exact
  statement: {β : Type*} {u : ι oplus β -> S.X₂} (huv : u ∘ Sum.inl = S.f ∘ v)
  proof: by
  intro m _
  have hgm : S.g m in span R (range (S.g ∘ u ∘ Sum.inr)) := hw mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hgm
  obtain ⟨cm, hm⟩ := hgm
  let m' : S.X₂ := Finsupp.sum cm fun j a => a • (u (Sum.inr j))
  have hsub : m - m' in LinearMap.range S.f.hom := by
    rw [hS.moduleCat_range_eq_ker]
    simp only [LinearMap.mem_ker, map_sub, sub_eq_zero]
    rw [← hm]; rw [map_finsuppSum]
    simp only [Function.comp_apply, map_smul]
  obtain ⟨n, hnm⟩ := hsub
  have hn : n in span R (range v) := hv mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨cn, hn⟩ := hn
  rw [← hn]; rw [map_finsuppSum] at hnm
  rw [← sub_add_cancel m m']; rw [← hnm]
  simp only [map_smul]
  have hn' : (Finsupp.sum cn fun a b => b • S.f (v a)) =
      (Finsupp.sum cn fun a b => b • u (Sum.inl a)) := by
    congr; ext a b; rw [← Function.comp_apply (f := S.f), ← huv, Function.comp_apply]
  rw [hn']
  apply add_mem
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cn.mapDomain (Sum.inl)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective]
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cm.mapDomain (Sum.inr)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inr_injective]

include hS in

中文:
定理 span_exact
  结论: {β : 类型} {u : ι oplus β -> S.X₂} (huv : u ∘ 和.inl = S.f ∘ v)
  证明: by
  intro m _
  have hgm : S.g m in span R (range (S.g ∘ u ∘ Sum.inr)) := hw mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hgm
  obtain ⟨cm, hm⟩ := hgm
  let m' : S.X₂ := Finsupp.sum cm fun j a => a • (u (Sum.inr j))
  have hsub : m - m' in LinearMap.range S.f.hom := by
    rw [hS.moduleCat_range_eq_ker]
    simp only [LinearMap.mem_ker, map_sub, sub_eq_zero]
    rw [← hm]; rw [map_finsuppSum]
    simp only [Function.comp_apply, map_smul]
  obtain ⟨n, hnm⟩ := hsub
  have hn : n in span R (range v) := hv mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨cn, hn⟩ := hn
  rw [← hn]; rw [map_finsuppSum] at hnm
  rw [← sub_add_cancel m m']; rw [← hnm]
  simp only [map_smul]
  have hn' : (Finsupp.sum cn fun a b => b • S.f (v a)) =
      (Finsupp.sum cn fun a b => b • u (Sum.inl a)) := by
    congr; ext a b; rw [← Function.comp_apply (f := S.f), ← huv, Function.comp_apply]
  rw [hn']
  apply add_mem
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cn.mapDomain (Sum.inl)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective]
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cm.mapDomain (Sum.inr)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inr_injective]

include hS in

Depends on / 依赖: Finsupp, Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.sum, Function, Function.comp_apply, LinearMap, LinearMap.mem_ker, LinearMap.range, S.f.hom, Sum.inr, comp_apply, hS.moduleCat_range_eq_ker, map_finsuppSum, map_smul, map_sub, mem_ker, mem_span_range_iff_exists_finsupp, mem_top, moduleCat_range_eq_ker, sub_eq_zero
-/
theorem span_exact {β : Type*} {u : ι oplus β -> S.X₂} (huv : u ∘ Sum.inl = S.f ∘ v)
    (hv : ⊤ <= span R (range v))
    (hw : ⊤ <= span R (range (S.g ∘ u ∘ Sum.inr))) :
    ⊤ <= span R (range u) := by
  intro m _
  have hgm : S.g m in span R (range (S.g ∘ u ∘ Sum.inr)) := hw mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hgm
  obtain ⟨cm, hm⟩ := hgm
  let m' : S.X₂ := Finsupp.sum cm fun j a => a • (u (Sum.inr j))
  have hsub : m - m' in LinearMap.range S.f.hom := by
    rw [hS.moduleCat_range_eq_ker]
    simp only [LinearMap.mem_ker, map_sub, sub_eq_zero]
    rw [← hm]; rw [map_finsuppSum]
    simp only [Function.comp_apply, map_smul]
  obtain ⟨n, hnm⟩ := hsub
  have hn : n in span R (range v) := hv mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨cn, hn⟩ := hn
  rw [← hn]; rw [map_finsuppSum] at hnm
  rw [← sub_add_cancel m m']; rw [← hnm]
  simp only [map_smul]
  have hn' : (Finsupp.sum cn fun a b => b • S.f (v a)) =
      (Finsupp.sum cn fun a b => b • u (Sum.inl a)) := by
    congr; ext a b; rw [← Function.comp_apply (f := S.f), ← huv, Function.comp_apply]
  rw [hn']
  apply add_mem
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cn.mapDomain (Sum.inl)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective]
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cm.mapDomain (Sum.inr)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inr_injective]

include hS in
/--
theorem `span_rightExact` / 定理 `span_rightExact`

English:
theorem span_rightExact
  statement: {w : ι' -> S.X₃} (hv : ⊤ <= span R (range v))
  proof: by
  refine span_exact hS ?_ hv ?_
  · simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inl]
  · convert! hw
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inr]
    rw [ModuleCat.epi_iff_surjective] at hE
    rw [← Function.comp_assoc]; rw [Function.RightInverse.comp_eq_id (Function.rightInverse_invFun hE)]; rw [Function.id_comp]

中文:
定理 span_rightExact
  结论: {w : ι' -> S.X₃} (hv : ⊤ <= span R (range v))
  证明: by
  refine span_exact hS ?_ hv ?_
  · simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inl]
  · convert! hw
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inr]
    rw [ModuleCat.epi_iff_surjective] at hE
    rw [← Function.comp_assoc]; rw [Function.RightInverse.comp_eq_id (Function.rightInverse_invFun hE)]; rw [Function.id_comp]

Depends on / 依赖: AddHom, AddHom.toFun_eq_coe, Function, Function.RightInverse.comp_eq_id, Function.comp_assoc, Function.id_comp, Function.rightInverse_invFun, LinearMap, LinearMap.coe_toAddHom, ModuleCat, ModuleCat.epi_iff_surjective, RightInverse, Sum.elim_comp_inl, Sum.elim_comp_inr, coe_toAddHom, comp_assoc, comp_eq_id, convert, elim_comp_inl, elim_comp_inr
-/
theorem span_rightExact {w : ι' -> S.X₃} (hv : ⊤ <= span R (range v))
    (hw : ⊤ <= span R (range w)) (hE : Epi S.g) :
    ⊤ <= span R (range (Sum.elim (S.f ∘ v) (S.g.hom.toFun.invFun ∘ w))) := by
  refine span_exact hS ?_ hv ?_
  · simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inl]
  · convert! hw
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inr]
    rw [ModuleCat.epi_iff_surjective] at hE
    rw [← Function.comp_assoc]; rw [Function.RightInverse.comp_eq_id (Function.rightInverse_invFun hE)]; rw [Function.id_comp]

end Span

/-- In a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, given bases for `X₁` and `X₃`
indexed by `ι` and `ι'` respectively, we get a basis for `X₂` indexed by `ι ⊕ ι'`. -/
noncomputable
/--
Definition of `Basis.ofShortExact` / `Basis.ofShortExact` 的定义

English:
definition Basis.ofShortExact
  body: Basis.mk (linearIndependent_shortExact hS' bN.linearIndependent bP.linearIndependent)
    (span_rightExact hS'.exact (le_of_eq (bN.span_eq.symm)) (le_of_eq (bP.span_eq.symm)) hS'.epi_g)

include hS'

中文:
定义 基.ofShortExact
  定义体: Basis.mk (linearIndependent_shortExact hS' bN.linearIndependent bP.linearIndependent)
    (span_rightExact hS'.exact (le_of_eq (bN.span_eq.symm)) (le_of_eq (bP.span_eq.symm)) hS'.epi_g)

include hS'

Depends on / 依赖: Basis.mk, bN.linearIndependent, bN.span_eq.symm, bP.linearIndependent, bP.span_eq.symm, epi_g, le_of_eq, linearIndependent, linearIndependent_shortExact, span_eq, span_rightExact
-/
def Basis.ofShortExact
    (bN : Basis ι R S.X₁) (bP : Basis ι' R S.X₃) : Basis (ι oplus ι') R S.X₂ :=
  Basis.mk (linearIndependent_shortExact hS' bN.linearIndependent bP.linearIndependent)
    (span_rightExact hS'.exact (le_of_eq (bN.span_eq.symm)) (le_of_eq (bP.span_eq.symm)) hS'.epi_g)

include hS'

/--
theorem `free_shortExact` / 定理 `free_shortExact`

English:
theorem free_shortExact
  given: [Module.Free R S.X₁] [Module.Free R S.X₃]
  proof: Module.Free.of_basis (Basis.ofShortExact hS' (Module.Free.chooseBasis R S.X₁)
    (Module.Free.chooseBasis R S.X₃))

中文:
定理 free_shortExact
  条件: [模.自由 R S.X₁] [模.自由 R S.X₃]
  证明: Module.Free.of_basis (Basis.ofShortExact hS' (Module.Free.chooseBasis R S.X₁)
    (Module.Free.chooseBasis R S.X₃))

Depends on / 依赖: Basis.ofShortExact, Module, Module.Free.chooseBasis, Module.Free.of_basis, chooseBasis, ofShortExact, of_basis
-/
theorem free_shortExact [Module.Free R S.X₁] [Module.Free R S.X₃] :
    Module.Free R S.X₂ :=
  Module.Free.of_basis (Basis.ofShortExact hS' (Module.Free.chooseBasis R S.X₁)
    (Module.Free.chooseBasis R S.X₃))

/--
theorem `free_shortExact_rank_add` / 定理 `free_shortExact_rank_add`

English:
theorem free_shortExact_rank_add
  statement: [Module.Free R S.X₁] [Module.Free R S.X₃]
  proof: by
  have := free_shortExact hS'
  rw [Module.Free.rank_eq_card_chooseBasisIndex]; rw [Module.Free.rank_eq_card_chooseBasisIndex R S.X₁]; rw [Module.Free.rank_eq_card_chooseBasisIndex R S.X₃]; rw [Cardinal.add_def]; rw [Cardinal.eq]
  exact ⟨Basis.indexEquiv (Module.Free.chooseBasis R S.X₂) (Basis.ofShortExact hS'
    (Module.Free.chooseBasis R S.X₁) (Module.Free.chooseBasis R S.X₃))⟩

中文:
定理 free_shortExact_rank_add
  结论: [模.自由 R S.X₁] [模.自由 R S.X₃]
  证明: by
  have := free_shortExact hS'
  rw [Module.Free.rank_eq_card_chooseBasisIndex]; rw [Module.Free.rank_eq_card_chooseBasisIndex R S.X₁]; rw [Module.Free.rank_eq_card_chooseBasisIndex R S.X₃]; rw [Cardinal.add_def]; rw [Cardinal.eq]
  exact ⟨Basis.indexEquiv (Module.Free.chooseBasis R S.X₂) (Basis.ofShortExact hS'
    (Module.Free.chooseBasis R S.X₁) (Module.Free.chooseBasis R S.X₃))⟩

Depends on / 依赖: Basis.indexEquiv, Basis.ofShortExact, Cardinal, Cardinal.add_def, Cardinal.eq, Module, Module.Free.chooseBasis, Module.Free.rank_eq_card_chooseBasisIndex, add_def, chooseBasis, free_shortExact, indexEquiv, ofShortExact, rank_eq_card_chooseBasisIndex
-/
theorem free_shortExact_rank_add [Module.Free R S.X₁] [Module.Free R S.X₃]
    [StrongRankCondition R] :
    Module.rank R S.X₂ = Module.rank R S.X₁ + Module.rank R S.X₃ := by
  have := free_shortExact hS'
  rw [Module.Free.rank_eq_card_chooseBasisIndex]; rw [Module.Free.rank_eq_card_chooseBasisIndex R S.X₁]; rw [Module.Free.rank_eq_card_chooseBasisIndex R S.X₃]; rw [Cardinal.add_def]; rw [Cardinal.eq]
  exact ⟨Basis.indexEquiv (Module.Free.chooseBasis R S.X₂) (Basis.ofShortExact hS'
    (Module.Free.chooseBasis R S.X₁) (Module.Free.chooseBasis R S.X₃))⟩

/--
theorem `free_shortExact_finrank_add` / 定理 `free_shortExact_finrank_add`

English:
theorem free_shortExact_finrank_add
  statement: {n p : Nat} [Module.Free R S.X₁] [Module.Free R S.X₃]
  proof: by
  apply finrank_eq_of_rank_eq
  rw [free_shortExact_rank_add hS']; rw [← hN]; rw [← hP]
  simp only [Nat.cast_add, finrank_eq_rank]

中文:
定理 free_shortExact_finrank_add
  结论: {n p : 自然数} [模.自由 R S.X₁] [模.自由 R S.X₃]
  证明: by
  apply finrank_eq_of_rank_eq
  rw [free_shortExact_rank_add hS']; rw [← hN]; rw [← hP]
  simp only [Nat.cast_add, finrank_eq_rank]

Depends on / 依赖: Nat.cast_add, cast_add, finrank_eq_of_rank_eq, finrank_eq_rank, free_shortExact_rank_add
-/
theorem free_shortExact_finrank_add {n p : Nat} [Module.Free R S.X₁] [Module.Free R S.X₃]
    [Module.Finite R S.X₁] [Module.Finite R S.X₃]
    (hN : Module.finrank R S.X₁ = n)
    (hP : Module.finrank R S.X₃ = p)
    [StrongRankCondition R] :
    finrank R S.X₂ = n + p := by
  apply finrank_eq_of_rank_eq
  rw [free_shortExact_rank_add hS']; rw [← hN]; rw [← hP]
  simp only [Nat.cast_add, finrank_eq_rank]

end ModuleCat
