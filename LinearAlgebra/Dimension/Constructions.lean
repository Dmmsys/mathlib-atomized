/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison, Chris Hughes, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Rank of various constructions

## Main statements

- `rank_quotient_add_rank_le` : `rank M/N + rank N ≤ rank M`.
- `lift_rank_add_lift_rank_le_rank_prod`: `rank M × N ≤ rank M + rank N`.
- `rank_span_le_of_finite`: `rank (span s) ≤ #s` for finite `s`.

For free modules, we have

- `rank_prod` : `rank M × N = rank M + rank N`.
- `rank_finsupp` : `rank (ι →₀ M) = #ι * rank M`
- `rank_directSum`: `rank (⨁ Mᵢ) = ∑ rank Mᵢ`
- `rank_tensorProduct`: `rank (M ⊗ N) = rank M * rank N`.

Lemmas for ranks of submodules and subalgebras are also provided.
We have `finrank` variants for most lemmas as well.

-/

@[expose] public section


noncomputable section

universe u u' v v' u₁' w w'

variable {R : Type u} {S : Type u'} {M : Type v} {M' : Type v'} {M₁ : Type v}
variable {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η -> Type*}

open Basis Cardinal DirectSum Function Module Set Submodule

section Quotient

variable [Ring R] [CommRing S] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M₁]
variable [Module R M]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `LinearIndependent.sumElim_of_quotient` / 定理 `LinearIndependent.sumElim_of_quotient`

English:
theorem LinearIndependent.sumElim_of_quotient
  proof: by
  refine .sum_type (hf.map' M'.subtype M'.ker_subtype) (.of_comp M'.mkQ hg) ?_
  refine disjoint_def.mpr fun x h₁ h₂ => ?_
  have : x in M' := span_le.mpr (Set.range_subset_iff.mpr fun i => (f i).prop) h₁
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h₂
  simp_rw [← Quotient.m

中文:
定理 LinearIndependent.sumElim_of_quotient
  证明: by
  refine .sum_type (hf.map' M'.subtype M'.ker_subtype) (.of_comp M'.mkQ hg) ?_
  refine disjoint_def.mpr fun x h₁ h₂ => ?_
  have : x in M' := span_le.mpr (Set.range_subset_iff.mpr fun i => (f i).prop) h₁
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h₂
  simp_rw [← Quotient.m
-/
theorem LinearIndependent.sumElim_of_quotient
    {M' : Submodule R M} {ι₁ ι₂} {f : ι₁ -> M'} (hf : LinearIndependent R f) (g : ι₂ -> M)
    (hg : LinearIndependent R (Submodule.Quotient.mk (p := M') ∘ g)) :
    LinearIndependent R (Sum.elim (f · : ι₁ -> M) g) := by
  refine .sum_type (hf.map' M'.subtype M'.ker_subtype) (.of_comp M'.mkQ hg) ?_
  refine disjoint_def.mpr fun x h₁ h₂ => ?_
  have : x in M' := span_le.mpr (Set.range_subset_iff.mpr fun i => (f i).prop) h₁
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h₂
  simp_rw [← Quotient.mk_eq_zero, ← mkQ_apply, map_finsuppSum, map_smul, mkQ_apply] at this
  rw [linearIndependent_iff.mp hg _ this]; rw [Finsupp.sum_zero_index]

/--
theorem `LinearIndepOn.union_of_quotient` / 定理 `LinearIndepOn.union_of_quotient`

English:
theorem LinearIndepOn.union_of_quotient
  statement: {s t : Set ι} {f : ι -> M} (hs : LinearIndepOn R f s)
  proof: by
  apply hs.union ht.of_comp
  convert! (Submodule.range_ker_disjoint ht).symm
  · simp
  aesop

中文:
定理 LinearIndepOn.union_of_quotient
  结论: {s t : Set ι} {f : ι -> M} (hs : LinearIndepOn R f s)
  证明: by
  apply hs.union ht.of_comp
  convert! (Submodule.range_ker_disjoint ht).symm
  · simp
  aesop

Depends on / 依赖: Submodule, Submodule.range_ker_disjoint, convert, hs.union, ht.of_comp, of_comp, range_ker_disjoint
-/
theorem LinearIndepOn.union_of_quotient {s t : Set ι} {f : ι -> M} (hs : LinearIndepOn R f s)
    (ht : LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t) : LinearIndepOn R f (s union t) := by
  apply hs.union ht.of_comp
  convert! (Submodule.range_ker_disjoint ht).symm
  · simp
  aesop

/--
theorem `LinearIndepOn.union_id_of_quotient` / 定理 `LinearIndepOn.union_id_of_quotient`

English:
theorem LinearIndepOn.union_id_of_quotient
  statement: {M' : Submodule R M}
  proof: hs'.union_of_quotient by
    rw [image_id]
    exact ht.of_comp ((span R s).mapQ M' (LinearMap.id) (span_le.2 hs))

中文:
定理 LinearIndepOn.union_id_of_quotient
  结论: {M' : Submodule R M}
  证明: hs'.union_of_quotient by
    rw [image_id]
    exact ht.of_comp ((span R s).mapQ M' (LinearMap.id) (span_le.2 hs))

Depends on / 依赖: LinearMap, LinearMap.id, ht.of_comp, image_id, of_comp, span_le, union_of_quotient
-/
theorem LinearIndepOn.union_id_of_quotient {M' : Submodule R M}
    {s : Set M} (hs : s subseteq M') (hs' : LinearIndepOn R id s) {t : Set M}
    (ht : LinearIndepOn R (mkQ M') t) : LinearIndepOn R id (s union t) :=
hs'.union_of_quotient by
    rw [image_id]
    exact ht.of_comp ((span R s).mapQ M' (LinearMap.id) (span_le.2 hs))

/--
theorem `linearIndepOn_union_iff_quotient` / 定理 `linearIndepOn_union_iff_quotient`

English:
theorem linearIndepOn_union_iff_quotient
  given: {s t : Set ι} {f : ι -> M} (hst : Disjoint s t)
  proof: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => h.1.union_of_quotient h.2⟩
  · exact h.mono subset_union_left
  apply (h.mono subset_union_right).map
  simpa [← image_eq_range] using ((linearIndepOn_union_iff hst).1 h).2.2.symm

中文:
定理 linearIndepOn_union_iff_quotient
  条件: {s t : Set ι} {f : ι -> M} (hst : Disjoint s t)
  证明: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => h.1.union_of_quotient h.2⟩
  · exact h.mono subset_union_left
  apply (h.mono subset_union_right).map
  simpa [← image_eq_range] using ((linearIndepOn_union_iff hst).1 h).2.2.symm

Depends on / 依赖: h.mono, image_eq_range, linearIndepOn_union_iff, subset_union_left, subset_union_right, union_of_quotient
-/
theorem linearIndepOn_union_iff_quotient {s t : Set ι} {f : ι -> M} (hst : Disjoint s t) :
    LinearIndepOn R f (s union t) ↔
    LinearIndepOn R f s ∧ LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => h.1.union_of_quotient h.2⟩
  · exact h.mono subset_union_left
  apply (h.mono subset_union_right).map
  simpa [← image_eq_range] using ((linearIndepOn_union_iff hst).1 h).2.2.symm

/--
theorem `LinearIndepOn.quotient_iff_union` / 定理 `LinearIndepOn.quotient_iff_union`

English:
theorem LinearIndepOn.quotient_iff_union
  statement: {s t : Set ι} {f : ι -> M} (hs : LinearIndepOn R f s)
  proof: by
  rw [linearIndepOn_union_iff_quotient hst]; rw [and_iff_right hs]

中文:
定理 LinearIndepOn.quotient_iff_union
  结论: {s t : Set ι} {f : ι -> M} (hs : LinearIndepOn R f s)
  证明: by
  rw [linearIndepOn_union_iff_quotient hst]; rw [and_iff_right hs]

Depends on / 依赖: and_iff_right, linearIndepOn_union_iff_quotient
-/
theorem LinearIndepOn.quotient_iff_union {s t : Set ι} {f : ι -> M} (hs : LinearIndepOn R f s)
    (hst : Disjoint s t) :
    LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t ↔ LinearIndepOn R f (s union t) := by
  rw [linearIndepOn_union_iff_quotient hst]; rw [and_iff_right hs]

/--
theorem `rank_quotient_add_rank_le` / 定理 `rank_quotient_add_rank_le`

English:
theorem rank_quotient_add_rank_le
  given: [Nontrivial R] (M' : Submodule R M)
  proof: by
  conv_lhs => simp only [Module.rank_def]
  rw [Cardinal.ciSup_add_ciSup _ bddAbove_of_small _ bddAbove_of_small]
  refine ciSup_le fun ⟨s, hs⟩ => ciSup_le fun ⟨t, ht⟩ => ?_
  choose f hf using Submodule.Quotient.mk_surjective M'
  simpa [add_comm] using! (LinearIndependent.sumElim_of_quotient ht

中文:
定理 rank_quotient_add_rank_le
  条件: [Nontrivial R] (M' : Submodule R M)
  证明: by
  conv_lhs => simp only [Module.rank_def]
  rw [Cardinal.ciSup_add_ciSup _ bddAbove_of_small _ bddAbove_of_small]
  refine ciSup_le fun ⟨s, hs⟩ => ciSup_le fun ⟨t, ht⟩ => ?_
  choose f hf using Submodule.Quotient.mk_surjective M'
  simpa [add_comm] using! (LinearIndependent.sumElim_of_quotient ht

Depends on / 依赖: Cardinal, Cardinal.ciSup_add_ciSup, Function, Function.comp_def, LinearIndependent, LinearIndependent.sumElim_of_quotient, Module, Module.rank_def, Quotient, Submodule, Submodule.Quotient.mk_surjective, add_comm, bddAbove_of_small, cardinal_le_rank, ciSup_add_ciSup, ciSup_le, comp_def, conv_lhs, mk_surjective, rank_def
-/
theorem rank_quotient_add_rank_le [Nontrivial R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' <= Module.rank R M := by
  conv_lhs => simp only [Module.rank_def]
  rw [Cardinal.ciSup_add_ciSup _ bddAbove_of_small _ bddAbove_of_small]
  refine ciSup_le fun ⟨s, hs⟩ => ciSup_le fun ⟨t, ht⟩ => ?_
  choose f hf using Submodule.Quotient.mk_surjective M'
  simpa [add_comm] using! (LinearIndependent.sumElim_of_quotient ht (fun (i : s) => f i)
    (by simpa [Function.comp_def, hf] using! hs)).cardinal_le_rank

/--
theorem `rank_quotient_le` / 定理 `rank_quotient_le`

English:
theorem rank_quotient_le
  given: (p : Submodule R M)
  statement: Module.rank R (M ⧸ p) <= Module.rank R M
  proof: (mkQ p).rank_le_of_surjective Quot.mk_surjective

中文:
定理 rank_quotient_le
  条件: (p : Submodule R M)
  结论: Module.rank R (M ⧸ p) <= Module.rank R M
  证明: (mkQ p).rank_le_of_surjective Quot.mk_surjective

Depends on / 依赖: Quot.mk_surjective, mk_surjective, rank_le_of_surjective
-/
theorem rank_quotient_le (p : Submodule R M) : Module.rank R (M ⧸ p) <= Module.rank R M :=
  (mkQ p).rank_le_of_surjective Quot.mk_surjective

/--
theorem `Submodule.finrank_quotient_le` / 定理 `Submodule.finrank_quotient_le`

English:
theorem Submodule.finrank_quotient_le
  statement: [StrongRankCondition R] [Module.Finite R M]
  proof: toNat_le_toNat ((Submodule.mkQ s).rank_le_of_surjective Quot.mk_surjective)
    (rank_lt_aleph0 _ _)

中文:
定理 Submodule.finrank_quotient_le
  结论: [StrongRankCondition R] [Module.Finite R M]
  证明: toNat_le_toNat ((Submodule.mkQ s).rank_le_of_surjective Quot.mk_surjective)
    (rank_lt_aleph0 _ _)

Depends on / 依赖: Quot.mk_surjective, Submodule, Submodule.mkQ, mk_surjective, rank_le_of_surjective, rank_lt_aleph0, toNat_le_toNat
-/
theorem Submodule.finrank_quotient_le [StrongRankCondition R] [Module.Finite R M]
    (s : Submodule R M) : finrank R (M ⧸ s) <= finrank R M :=
  toNat_le_toNat ((Submodule.mkQ s).rank_le_of_surjective Quot.mk_surjective)
    (rank_lt_aleph0 _ _)

end Quotient

variable [Semiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M₁]
variable [Module R M]

section ULift

@[simp]
/--
theorem `rank_ulift` / 定理 `rank_ulift`

English:
theorem rank_ulift
  statement: Module.rank R (ULift.{w} M) = Cardinal.lift.{w} (Module.rank R M)
  proof: Cardinal.lift_injective.{v} Eq.symm (lift_lift _).trans ULift.moduleEquiv.symm.lift_rank_eq

@[simp]

中文:
定理 rank_ulift
  结论: Module.rank R (ULift.{w} M) = Cardinal.lift.{w} (Module.rank R M)
  证明: Cardinal.lift_injective.{v} Eq.symm (lift_lift _).trans ULift.moduleEquiv.symm.lift_rank_eq

@[simp]

Depends on / 依赖: Cardinal, Cardinal.lift_injective, Eq.symm, ULift.moduleEquiv.symm.lift_rank_eq, lift_injective, lift_lift, lift_rank_eq, moduleEquiv
-/
theorem rank_ulift : Module.rank R (ULift.{w} M) = Cardinal.lift.{w} (Module.rank R M) :=
Cardinal.lift_injective.{v} Eq.symm (lift_lift _).trans ULift.moduleEquiv.symm.lift_rank_eq

@[simp]
/--
theorem `finrank_ulift` / 定理 `finrank_ulift`

English:
theorem finrank_ulift
  statement: finrank R (ULift M) = finrank R M
  proof: by
  simp_rw [finrank, rank_ulift, toNat_lift]

中文:
定理 finrank_ulift
  结论: finrank R (ULift M) = finrank R M
  证明: by
  simp_rw [finrank, rank_ulift, toNat_lift]

Depends on / 依赖: finrank, rank_ulift, simp_rw, toNat_lift
-/
theorem finrank_ulift : finrank R (ULift M) = finrank R M := by
  simp_rw [finrank, rank_ulift, toNat_lift]

end ULift

section Prod

variable (R M M')
variable [Module R M₁] [Module R M']

/--
theorem `rank_add_rank_le_rank_prod` / 定理 `rank_add_rank_le_rank_prod`

English:
theorem rank_add_rank_le_rank_prod
  given: [Nontrivial R]
  proof: by
  conv_lhs => simp only [Module.rank_def]
  rw [Cardinal.ciSup_add_ciSup _ bddAbove_of_small _ bddAbove_of_small]
  exact ciSup_le fun ⟨s, hs⟩ => ciSup_le fun ⟨t, ht⟩ =>
    (linearIndependent_inl_union_inr' hs ht).cardinal_le_rank

中文:
定理 rank_add_rank_le_rank_prod
  条件: [Nontrivial R]
  证明: by
  conv_lhs => simp only [Module.rank_def]
  rw [Cardinal.ciSup_add_ciSup _ bddAbove_of_small _ bddAbove_of_small]
  exact ciSup_le fun ⟨s, hs⟩ => ciSup_le fun ⟨t, ht⟩ =>
    (linearIndependent_inl_union_inr' hs ht).cardinal_le_rank

Depends on / 依赖: Cardinal, Cardinal.ciSup_add_ciSup, Module, Module.rank_def, bddAbove_of_small, cardinal_le_rank, ciSup_add_ciSup, ciSup_le, conv_lhs, linearIndependent_inl_union_inr, rank_def
-/
theorem rank_add_rank_le_rank_prod [Nontrivial R] :
    Module.rank R M + Module.rank R M₁ <= Module.rank R (M × M₁) := by
  conv_lhs => simp only [Module.rank_def]
  rw [Cardinal.ciSup_add_ciSup _ bddAbove_of_small _ bddAbove_of_small]
  exact ciSup_le fun ⟨s, hs⟩ => ciSup_le fun ⟨t, ht⟩ =>
    (linearIndependent_inl_union_inr' hs ht).cardinal_le_rank

/--
theorem `lift_rank_add_lift_rank_le_rank_prod` / 定理 `lift_rank_add_lift_rank_le_rank_prod`

English:
theorem lift_rank_add_lift_rank_le_rank_prod
  given: [Nontrivial R]
  proof: by
  rw [← rank_ulift]; rw [← rank_ulift]
  exact (rank_add_rank_le_rank_prod R _).trans_eq
    (ULift.moduleEquiv.prodCongr ULift.moduleEquiv).rank_eq

中文:
定理 lift_rank_add_lift_rank_le_rank_prod
  条件: [Nontrivial R]
  证明: by
  rw [← rank_ulift]; rw [← rank_ulift]
  exact (rank_add_rank_le_rank_prod R _).trans_eq
    (ULift.moduleEquiv.prodCongr ULift.moduleEquiv).rank_eq

Depends on / 依赖: ULift.moduleEquiv, ULift.moduleEquiv.prodCongr, moduleEquiv, prodCongr, rank_add_rank_le_rank_prod, rank_eq, rank_ulift, trans_eq
-/
theorem lift_rank_add_lift_rank_le_rank_prod [Nontrivial R] :
    lift.{v'} (Module.rank R M) + lift.{v} (Module.rank R M') <= Module.rank R (M × M') := by
  rw [← rank_ulift]; rw [← rank_ulift]
  exact (rank_add_rank_le_rank_prod R _).trans_eq
    (ULift.moduleEquiv.prodCongr ULift.moduleEquiv).rank_eq

variable {R M M'}
variable [StrongRankCondition R] [Module.Free R M] [Module.Free R M'] [Module.Free R M₁]

open Module.Free

/-- If `M` and `M'` are free, then the rank of `M × M'` is
`(Module.rank R M).lift + (Module.rank R M').lift`. -/
@[simp]
/--
theorem `rank_prod` / 定理 `rank_prod`

English:
theorem rank_prod
  statement: Module.rank R (M × M') =
  proof: by
  simpa [rank_eq_card_chooseBasisIndex R M, rank_eq_card_chooseBasisIndex R M', lift_umax]
    using ((chooseBasis R M).prod (chooseBasis R M')).mk_eq_rank.symm

中文:
定理 rank_prod
  结论: Module.rank R (M × M') =
  证明: by
  simpa [rank_eq_card_chooseBasisIndex R M, rank_eq_card_chooseBasisIndex R M', lift_umax]
    using ((chooseBasis R M).prod (chooseBasis R M')).mk_eq_rank.symm

Depends on / 依赖: chooseBasis, lift_umax, mk_eq_rank, mk_eq_rank.symm, rank_eq_card_chooseBasisIndex
-/
theorem rank_prod : Module.rank R (M × M') =
    Cardinal.lift.{v'} (Module.rank R M) + Cardinal.lift.{v, v'} (Module.rank R M') := by
  simpa [rank_eq_card_chooseBasisIndex R M, rank_eq_card_chooseBasisIndex R M', lift_umax]
    using ((chooseBasis R M).prod (chooseBasis R M')).mk_eq_rank.symm

/--
theorem `rank_prod'` / 定理 `rank_prod'`

English:
theorem rank_prod'
  statement: Module.rank R (M × M₁) = Module.rank R M + Module.rank R M₁
  proof: by simp

中文:
定理 rank_prod'
  结论: Module.rank R (M × M₁) = Module.rank R M + Module.rank R M₁
  证明: by simp
-/
theorem rank_prod' : Module.rank R (M × M₁) = Module.rank R M + Module.rank R M₁ := by simp

/-- The `finrank` of `M × M'` is `(finrank R M) + (finrank R M')`. -/
@[simp]
/--
theorem `Module.finrank_prod` / 定理 `Module.finrank_prod`

English:
theorem Module.finrank_prod
  given: [Module.Finite R M] [Module.Finite R M']
  proof: by
  simp [finrank, rank_lt_aleph0 R M, rank_lt_aleph0 R M']

中文:
定理 Module.finrank_prod
  条件: [Module.Finite R M] [Module.Finite R M']
  证明: by
  simp [finrank, rank_lt_aleph0 R M, rank_lt_aleph0 R M']

Depends on / 依赖: finrank, rank_lt_aleph0
-/
theorem Module.finrank_prod [Module.Finite R M] [Module.Finite R M'] :
    finrank R (M × M') = finrank R M + finrank R M' := by
  simp [finrank, rank_lt_aleph0 R M, rank_lt_aleph0 R M']

end Prod

section Finsupp

variable (R M M')
variable [StrongRankCondition R] [Module.Free R M] [Module R M'] [Module.Free R M']

open Module.Free

@[simp]
/--
theorem `rank_finsupp` / 定理 `rank_finsupp`

English:
theorem rank_finsupp
  given: (ι : Type w)
  proof: by
  obtain ⟨⟨_, bs⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [← bs.mk_eq_rank'']; rw [← (Finsupp.basis fun _ : ι => bs).mk_eq_rank'']; rw [Cardinal.mk_sigma]; rw [Cardinal.sum_const]

中文:
定理 rank_finsupp
  条件: (ι : Type w)
  证明: by
  obtain ⟨⟨_, bs⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [← bs.mk_eq_rank'']; rw [← (Finsupp.basis fun _ : ι => bs).mk_eq_rank'']; rw [Cardinal.mk_sigma]; rw [Cardinal.sum_const]

Depends on / 依赖: Cardinal, Cardinal.mk_sigma, Cardinal.sum_const, Finsupp, Finsupp.basis, Module, Module.Free.exists_basis, bs.mk_eq_rank, exists_basis, mk_eq_rank, mk_sigma, sum_const
-/
theorem rank_finsupp (ι : Type w) :
    Module.rank R (ι ->₀ M) = Cardinal.lift.{v} #ι * Cardinal.lift.{w} (Module.rank R M) := by
  obtain ⟨⟨_, bs⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [← bs.mk_eq_rank'']; rw [← (Finsupp.basis fun _ : ι => bs).mk_eq_rank'']; rw [Cardinal.mk_sigma]; rw [Cardinal.sum_const]

/--
theorem `rank_finsupp'` / 定理 `rank_finsupp'`

English:
theorem rank_finsupp'
  given: (ι : Type v)
  statement: Module.rank R (ι ->₀ M) = #ι * Module.rank R M
  proof: by
  simp [rank_finsupp]

中文:
定理 rank_finsupp'
  条件: (ι : 类型v)
  结论: Module.rank R (ι ->₀ M) = #ι * Module.rank R M
  证明: by
  simp [rank_finsupp]

Depends on / 依赖: rank_finsupp
-/
theorem rank_finsupp' (ι : Type v) : Module.rank R (ι ->₀ M) = #ι * Module.rank R M := by
  simp [rank_finsupp]

/--
theorem `rank_finsupp_self` / 定理 `rank_finsupp_self`

English:
theorem rank_finsupp_self
  given: (ι : Type w)
  statement: Module.rank R (ι ->₀ R) = Cardinal.lift.{u} #ι
  proof: by
  simp

中文:
定理 rank_finsupp_self
  条件: (ι : Type w)
  结论: Module.rank R (ι ->₀ R) = Cardinal.lift.{u} #ι
  证明: by
  simp
-/
theorem rank_finsupp_self (ι : Type w) : Module.rank R (ι ->₀ R) = Cardinal.lift.{u} #ι := by
  simp

/--
theorem `rank_finsupp_self'` / 定理 `rank_finsupp_self'`

English:
theorem rank_finsupp_self'
  given: {ι : Type u}
  statement: Module.rank R (ι ->₀ R) = #ι
  proof: by simp

中文:
定理 rank_finsupp_self'
  条件: {ι : 类型u}
  结论: Module.rank R (ι ->₀ R) = #ι
  证明: by simp
-/
theorem rank_finsupp_self' {ι : Type u} : Module.rank R (ι ->₀ R) = #ι := by simp

/-- The rank of the direct sum is the sum of the ranks. -/
@[simp]
/--
theorem `rank_directSum` / 定理 `rank_directSum`

English:
theorem rank_directSum
  statement: {ι : Type v} (M : ι -> Type w) [forall i : ι, AddCommMonoid (M i)]
  proof: by
  let B i := chooseBasis R (M i)
  let b : Basis _ R (⨁ i, M i) := DFinsupp.basis fun i => B i
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']

中文:
定理 rank_directSum
  结论: {ι : 类型v} (M : ι -> Type w) [对任意 i : ι, AddCommMonoid (M i)]
  证明: by
  let B i := chooseBasis R (M i)
  let b : Basis _ R (⨁ i, M i) := DFinsupp.basis fun i => B i
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']

Depends on / 依赖: DFinsupp, DFinsupp.basis, b.mk_eq_rank, chooseBasis, mk_eq_rank
-/
theorem rank_directSum {ι : Type v} (M : ι -> Type w) [forall i : ι, AddCommMonoid (M i)]
    [forall i : ι, Module R (M i)] [forall i : ι, Module.Free R (M i)] :
    Module.rank R (⨁ i, M i) = Cardinal.sum fun i => Module.rank R (M i) := by
  let B i := chooseBasis R (M i)
  let b : Basis _ R (⨁ i, M i) := DFinsupp.basis fun i => B i
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']

/-- If `m` and `n` are finite, the rank of `m × n` matrices over a module `M` is
`(#m).lift * (#n).lift * rank R M`. -/
@[simp]
/--
theorem `rank_matrix_module` / 定理 `rank_matrix_module`

English:
theorem rank_matrix_module
  given: (m : Type w) (n : Type w') [Finite m] [Finite n]
  proof: by
  cases nonempty_fintype m
  cases nonempty_fintype n
  obtain ⟨I, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [← (b.matrix m n).mk_eq_rank'']
  simp only [mk_prod, lift_mul, lift_lift, ← mul_assoc, b.mk_eq_rank'']

中文:
定理 rank_matrix_module
  条件: (m : Type w) (n : Type w') [Finite m] [Finite n]
  证明: by
  cases nonempty_fintype m
  cases nonempty_fintype n
  obtain ⟨I, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [← (b.matrix m n).mk_eq_rank'']
  simp only [mk_prod, lift_mul, lift_lift, ← mul_assoc, b.mk_eq_rank'']

Depends on / 依赖: Module, Module.Free.exists_basis, b.matrix, b.mk_eq_rank, exists_basis, lift_lift, lift_mul, matrix, mk_eq_rank, mk_prod, mul_assoc, nonempty_fintype
-/
theorem rank_matrix_module (m : Type w) (n : Type w') [Finite m] [Finite n] :
    Module.rank R (Matrix m n M) =
      lift.{max v w'} #m * lift.{max v w} #n * lift.{max w w'} (Module.rank R M) := by
  cases nonempty_fintype m
  cases nonempty_fintype n
  obtain ⟨I, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [← (b.matrix m n).mk_eq_rank'']
  simp only [mk_prod, lift_mul, lift_lift, ← mul_assoc, b.mk_eq_rank'']


/-- If `m` and `n` are finite and lie in the same universe, the rank of `m × n` matrices over a
module `M` is `(#m * #n).lift * rank R M`. -/
@[simp high]
/--
theorem `rank_matrix_module'` / 定理 `rank_matrix_module'`

English:
theorem rank_matrix_module'
  given: (m n : Type w) [Finite m] [Finite n]
  proof: by
  rw [rank_matrix_module]; rw [lift_mul]; rw [lift_umax.{w]; rw [v}]

中文:
定理 rank_matrix_module'
  条件: (m n : Type w) [Finite m] [Finite n]
  证明: by
  rw [rank_matrix_module]; rw [lift_mul]; rw [lift_umax.{w]; rw [v}]

Depends on / 依赖: lift_mul, lift_umax, rank_matrix_module
-/
theorem rank_matrix_module' (m n : Type w) [Finite m] [Finite n] :
    Module.rank R (Matrix m n M) =
      lift.{max v} (#m * #n) * lift.{w} (Module.rank R M) := by
  rw [rank_matrix_module]; rw [lift_mul]; rw [lift_umax.{w]; rw [v}]

/--
theorem `rank_matrix` / 定理 `rank_matrix`

English:
theorem rank_matrix
  given: (m : Type v) (n : Type w) [Finite m] [Finite n]
  proof: by
  rw [rank_matrix_module]; rw [rank_self]; rw [lift_one]; rw [mul_one]; rw [← lift_lift.{v]; rw [max u w}]; rw [lift_id]; rw [← lift_lift.{w]; rw [max u v}]; rw [lift_id]

中文:
定理 rank_matrix
  条件: (m : 类型v) (n : Type w) [Finite m] [Finite n]
  证明: by
  rw [rank_matrix_module]; rw [rank_self]; rw [lift_one]; rw [mul_one]; rw [← lift_lift.{v]; rw [max u w}]; rw [lift_id]; rw [← lift_lift.{w]; rw [max u v}]; rw [lift_id]

Depends on / 依赖: lift_id, lift_lift, lift_one, mul_one, rank_matrix_module, rank_self
-/
theorem rank_matrix (m : Type v) (n : Type w) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) =
      Cardinal.lift.{max v w u, v} #m * Cardinal.lift.{max v w u, w} #n := by
  rw [rank_matrix_module]; rw [rank_self]; rw [lift_one]; rw [mul_one]; rw [← lift_lift.{v]; rw [max u w}]; rw [lift_id]; rw [← lift_lift.{w]; rw [max u v}]; rw [lift_id]

/--
theorem `rank_matrix'` / 定理 `rank_matrix'`

English:
theorem rank_matrix'
  given: (m n : Type v) [Finite m] [Finite n]
  proof: by
  rw [rank_matrix]; rw [lift_mul]; rw [lift_umax.{v]; rw [u}]

中文:
定理 rank_matrix'
  条件: (m n : 类型v) [Finite m] [Finite n]
  证明: by
  rw [rank_matrix]; rw [lift_mul]; rw [lift_umax.{v]; rw [u}]

Depends on / 依赖: lift_mul, lift_umax, rank_matrix
-/
theorem rank_matrix' (m n : Type v) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = Cardinal.lift.{u} (#m * #n) := by
  rw [rank_matrix]; rw [lift_mul]; rw [lift_umax.{v]; rw [u}]

/--
theorem `rank_matrix''` / 定理 `rank_matrix''`

English:
theorem rank_matrix''
  given: (m n : Type u) [Finite m] [Finite n]
  proof: by simp

中文:
定理 rank_matrix''
  条件: (m n : 类型u) [Finite m] [Finite n]
  证明: by simp
-/
theorem rank_matrix'' (m n : Type u) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = #m * #n := by simp

open Fintype

namespace Module

@[simp]
/--
theorem `finrank_finsupp` / 定理 `finrank_finsupp`

English:
theorem finrank_finsupp
  given: {ι : Type v} [Fintype ι]
  statement: finrank R (ι ->₀ M) = card ι * finrank R M
  proof: by
  rw [finrank]; rw [finrank]; rw [rank_finsupp]; rw [← mk_toNat_eq_card]; rw [toNat_mul]; rw [toNat_lift]; rw [toNat_lift]

中文:
定理 finrank_finsupp
  条件: {ι : 类型v} [Fintype ι]
  结论: finrank R (ι ->₀ M) = card ι * finrank R M
  证明: by
  rw [finrank]; rw [finrank]; rw [rank_finsupp]; rw [← mk_toNat_eq_card]; rw [toNat_mul]; rw [toNat_lift]; rw [toNat_lift]

Depends on / 依赖: finrank, mk_toNat_eq_card, rank_finsupp, toNat_lift, toNat_mul
-/
theorem finrank_finsupp {ι : Type v} [Fintype ι] : finrank R (ι ->₀ M) = card ι * finrank R M := by
  rw [finrank]; rw [finrank]; rw [rank_finsupp]; rw [← mk_toNat_eq_card]; rw [toNat_mul]; rw [toNat_lift]; rw [toNat_lift]

/-- The `finrank` of `(ι →₀ R)` is `Fintype.card ι`. -/
@[simp]
/--
theorem `finrank_finsupp_self` / 定理 `finrank_finsupp_self`

English:
theorem finrank_finsupp_self
  given: {ι : Type v} [Fintype ι]
  statement: finrank R (ι ->₀ R) = card ι
  proof: by
  rw [finrank]; rw [rank_finsupp_self]; rw [← mk_toNat_eq_card]; rw [toNat_lift]

中文:
定理 finrank_finsupp_self
  条件: {ι : 类型v} [Fintype ι]
  结论: finrank R (ι ->₀ R) = card ι
  证明: by
  rw [finrank]; rw [rank_finsupp_self]; rw [← mk_toNat_eq_card]; rw [toNat_lift]

Depends on / 依赖: finrank, mk_toNat_eq_card, rank_finsupp_self, toNat_lift
-/
theorem finrank_finsupp_self {ι : Type v} [Fintype ι] : finrank R (ι ->₀ R) = card ι := by
  rw [finrank]; rw [rank_finsupp_self]; rw [← mk_toNat_eq_card]; rw [toNat_lift]

/-- The `finrank` of the direct sum is the sum of the `finrank`s. -/
@[simp]
/--
theorem `finrank_directSum` / 定理 `finrank_directSum`

English:
theorem finrank_directSum
  statement: {ι : Type v} [Fintype ι] (M : ι -> Type w) [forall i : ι, AddCommMonoid (M i)]
  proof: by
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_directSum, ← mk_sigma,
    mk_toNat_eq_card, card_sigma]

中文:
定理 finrank_directSum
  结论: {ι : 类型v} [Fintype ι] (M : ι -> Type w) [对任意 i : ι, AddCommMonoid (M i)]
  证明: by
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_directSum, ← mk_sigma,
    mk_toNat_eq_card, card_sigma]

Depends on / 依赖: card_sigma, finrank, mk_sigma, mk_toNat_eq_card, rank_directSum, rank_eq_card_chooseBasisIndex
-/
theorem finrank_directSum {ι : Type v} [Fintype ι] (M : ι -> Type w) [forall i : ι, AddCommMonoid (M i)]
    [forall i : ι, Module R (M i)] [forall i : ι, Module.Free R (M i)] [forall i : ι, Module.Finite R (M i)] :
    finrank R (⨁ i, M i) = ∑ i, finrank R (M i) := by
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_directSum, ← mk_sigma,
    mk_toNat_eq_card, card_sigma]

/--
theorem `finrank_matrix` / 定理 `finrank_matrix`

English:
theorem finrank_matrix
  given: (m n : Type*) [Fintype m] [Fintype n]
  proof: by simp [finrank]

中文:
定理 finrank_matrix
  条件: (m n : 类型) [Fintype m] [Fintype n]
  证明: by simp [finrank]

Depends on / 依赖: finrank
-/
theorem finrank_matrix (m n : Type*) [Fintype m] [Fintype n] :
    finrank R (Matrix m n M) = card m * card n * finrank R M := by simp [finrank]

end Module

end Finsupp

section Pi

variable [StrongRankCondition R] [Module.Free R M]
variable [forall i, AddCommMonoid (φ i)] [forall i, Module R (φ i)] [forall i, Module.Free R (φ i)]

open Module.Free

open LinearMap

/-- The rank of a finite product of free modules is the sum of the ranks. -/
-- this result is not true without the freeness assumption
@[simp]
/--
theorem `rank_pi` / 定理 `rank_pi`

English:
theorem rank_pi
  given: [Finite η]
  statement: Module.rank R (forall i, φ i) =
  proof: by
  cases nonempty_fintype η
  let B i := chooseBasis R (φ i)
  let b : Basis _ R (forall i, φ i) := Pi.basis fun i => B i
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']

中文:
定理 rank_pi
  条件: [Finite η]
  结论: Module.rank R (对任意 i, φ i) =
  证明: by
  cases nonempty_fintype η
  let B i := chooseBasis R (φ i)
  let b : Basis _ R (forall i, φ i) := Pi.basis fun i => B i
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']

Depends on / 依赖: Pi.basis, b.mk_eq_rank, chooseBasis, mk_eq_rank, nonempty_fintype
-/
theorem rank_pi [Finite η] : Module.rank R (forall i, φ i) =
    Cardinal.sum fun i => Module.rank R (φ i) := by
  cases nonempty_fintype η
  let B i := chooseBasis R (φ i)
  let b : Basis _ R (forall i, φ i) := Pi.basis fun i => B i
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']

variable (R)

/--
theorem `Module.finrank_pi` / 定理 `Module.finrank_pi`

English:
theorem Module.finrank_pi
  given: {ι : Type v} [Fintype ι]
  proof: by
  simp [finrank]

中文:
定理 Module.finrank_pi
  条件: {ι : 类型v} [Fintype ι]
  证明: by
  simp [finrank]

Depends on / 依赖: finrank
-/
theorem Module.finrank_pi {ι : Type v} [Fintype ι] :
    finrank R (ι -> R) = Fintype.card ι := by
  simp [finrank]

--TODO: this should follow from `LinearEquiv.finrank_eq`, that is over a field.
/--
theorem `Module.finrank_pi_fintype` / 定理 `Module.finrank_pi_fintype`

English:
theorem Module.finrank_pi_fintype
  proof: by
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_pi, ← mk_sigma,
    mk_toNat_eq_card, Fintype.card_sigma]

中文:
定理 Module.finrank_pi_fintype
  证明: by
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_pi, ← mk_sigma,
    mk_toNat_eq_card, Fintype.card_sigma]

Depends on / 依赖: Fintype, Fintype.card_sigma, card_sigma, finrank, mk_sigma, mk_toNat_eq_card, rank_eq_card_chooseBasisIndex, rank_pi
-/
theorem Module.finrank_pi_fintype
    {ι : Type v} [Fintype ι] {M : ι -> Type w} [forall i : ι, AddCommMonoid (M i)]
    [forall i : ι, Module R (M i)] [forall i : ι, Module.Free R (M i)] [forall i : ι, Module.Finite R (M i)] :
    finrank R (forall i, M i) = ∑ i, finrank R (M i) := by
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_pi, ← mk_sigma,
    mk_toNat_eq_card, Fintype.card_sigma]

variable {R}
variable [Fintype η]

/--
theorem `rank_fun` / 定理 `rank_fun`

English:
theorem rank_fun
  given: {M η : Type u} [Fintype η] [AddCommMonoid M] [Module R M] [Module.Free R M]
  proof: by
  rw [rank_pi]; rw [Cardinal.sum_const']; rw [Cardinal.mk_fintype]

中文:
定理 rank_fun
  条件: {M η : 类型u} [Fintype η] [AddCommMonoid M] [Module R M] [Module.Free R M]
  证明: by
  rw [rank_pi]; rw [Cardinal.sum_const']; rw [Cardinal.mk_fintype]

Depends on / 依赖: Cardinal, Cardinal.mk_fintype, Cardinal.sum_const, mk_fintype, rank_pi, sum_const
-/
theorem rank_fun {M η : Type u} [Fintype η] [AddCommMonoid M] [Module R M] [Module.Free R M] :
    Module.rank R (η -> M) = Fintype.card η * Module.rank R M := by
  rw [rank_pi]; rw [Cardinal.sum_const']; rw [Cardinal.mk_fintype]

/--
theorem `rank_fun_eq_lift_mul` / 定理 `rank_fun_eq_lift_mul`

English:
theorem rank_fun_eq_lift_mul
  statement: Module.rank R (η -> M) =
  proof: by
  rw [rank_pi]; rw [Cardinal.sum_const]; rw [Cardinal.mk_fintype]; rw [Cardinal.lift_natCast]

中文:
定理 rank_fun_eq_lift_mul
  结论: Module.rank R (η -> M) =
  证明: by
  rw [rank_pi]; rw [Cardinal.sum_const]; rw [Cardinal.mk_fintype]; rw [Cardinal.lift_natCast]

Depends on / 依赖: Cardinal, Cardinal.lift_natCast, Cardinal.mk_fintype, Cardinal.sum_const, lift_natCast, mk_fintype, rank_pi, sum_const
-/
theorem rank_fun_eq_lift_mul : Module.rank R (η -> M) =
    (Fintype.card η : Cardinal.{max u₁' v}) * Cardinal.lift.{u₁'} (Module.rank R M) := by
  rw [rank_pi]; rw [Cardinal.sum_const]; rw [Cardinal.mk_fintype]; rw [Cardinal.lift_natCast]

/--
theorem `rank_fun'` / 定理 `rank_fun'`

English:
theorem rank_fun'
  statement: Module.rank R (η -> R) = Fintype.card η
  proof: by
  rw [rank_fun_eq_lift_mul]; rw [rank_self]; rw [Cardinal.lift_one]; rw [mul_one]

中文:
定理 rank_fun'
  结论: Module.rank R (η -> R) = Fintype.card η
  证明: by
  rw [rank_fun_eq_lift_mul]; rw [rank_self]; rw [Cardinal.lift_one]; rw [mul_one]

Depends on / 依赖: Cardinal, Cardinal.lift_one, lift_one, mul_one, rank_fun_eq_lift_mul, rank_self
-/
theorem rank_fun' : Module.rank R (η -> R) = Fintype.card η := by
  rw [rank_fun_eq_lift_mul]; rw [rank_self]; rw [Cardinal.lift_one]; rw [mul_one]

/--
theorem `rank_fin_fun` / 定理 `rank_fin_fun`

English:
theorem rank_fin_fun
  given: (n : Nat)
  statement: Module.rank R (Fin n -> R) = n
  proof: by simp

中文:
定理 rank_fin_fun
  条件: (n : 自然数)
  结论: Module.rank R (Fin n -> R) = n
  证明: by simp
-/
theorem rank_fin_fun (n : Nat) : Module.rank R (Fin n -> R) = n := by simp

variable (R)

/-- The vector space of functions on a `Fintype ι` has `finrank` equal to the cardinality of `ι`. -/
@[simp]
/--
theorem `Module.finrank_fintype_fun_eq_card` / 定理 `Module.finrank_fintype_fun_eq_card`

English:
theorem Module.finrank_fintype_fun_eq_card
  statement: finrank R (η -> R) = Fintype.card η
  proof: finrank_eq_of_rank_eq rank_fun'

中文:
定理 Module.finrank_fintype_fun_eq_card
  结论: finrank R (η -> R) = Fintype.card η
  证明: finrank_eq_of_rank_eq rank_fun'

Depends on / 依赖: finrank_eq_of_rank_eq, rank_fun
-/
theorem Module.finrank_fintype_fun_eq_card : finrank R (η -> R) = Fintype.card η :=
  finrank_eq_of_rank_eq rank_fun'

/--
theorem `Module.finrank_fin_fun` / 定理 `Module.finrank_fin_fun`

English:
theorem Module.finrank_fin_fun
  given: {n : Nat}
  statement: finrank R (Fin n -> R) = n
  proof: by simp

中文:
定理 Module.finrank_fin_fun
  条件: {n : 自然数}
  结论: finrank R (Fin n -> R) = n
  证明: by simp
-/
theorem Module.finrank_fin_fun {n : Nat} : finrank R (Fin n -> R) = n := by simp

variable {R}

-- TODO: merge with the `Finrank` content
/--
Definition of `finDimVectorspaceEquiv` / `finDimVectorspaceEquiv` 的定义

English:
definition finDimVectorspaceEquiv
  signature: (n : Nat) (hn : Module.rank R M = n)
  body: by
  haveI := nontrivial_of_invariantBasisNumber R
  have : Cardinal.lift.{u} (n : Cardinal.{v}) = Cardinal.lift.{v} (n : Cardinal.{u}) := by simp
  have hn := Cardinal.lift_inj.{v, u}.2 hn
  rw [this] at hn
  rw [← @rank_fin_fun R _ _ n] at hn
  haveI : Module.Free R (Fin n -> R) := Module.Free.pi 

中文:
定义 finDimVectorspaceEquiv
  签名: (n : 自然数) (hn : Module.rank R M = n)
  定义体: by
  haveI := nontrivial_of_invariantBasisNumber R
  have : Cardinal.lift.{u} (n : Cardinal.{v}) = Cardinal.lift.{v} (n : Cardinal.{u}) := by simp
  have hn := Cardinal.lift_inj.{v, u}.2 hn
  rw [this] at hn
  rw [← @rank_fin_fun R _ _ n] at hn
  haveI : Module.Free R (Fin n -> R) := Module.Free.pi 

Depends on / 依赖: Cardinal, Cardinal.lift, Cardinal.lift_inj, Classical, Classical.choice, Module, Module.Free, Module.Free.pi, choice, lift_inj, nonempty_linearEquiv_of_lift_rank_eq, nontrivial_of_invariantBasisNumber, rank_fin_fun
-/
def finDimVectorspaceEquiv (n : Nat) (hn : Module.rank R M = n) : M ≃ₗ[R] Fin n -> R := by
  haveI := nontrivial_of_invariantBasisNumber R
  have : Cardinal.lift.{u} (n : Cardinal.{v}) = Cardinal.lift.{v} (n : Cardinal.{u}) := by simp
  have hn := Cardinal.lift_inj.{v, u}.2 hn
  rw [this] at hn
  rw [← @rank_fin_fun R _ _ n] at hn
  haveI : Module.Free R (Fin n -> R) := Module.Free.pi _ _
  exact Classical.choice (nonempty_linearEquiv_of_lift_rank_eq hn)

end Pi

section TensorProduct

open TensorProduct

variable [StrongRankCondition R] [StrongRankCondition S]
variable [Module S M] [Module S M'] [Module.Free S M']
variable [Module S M₁] [Module.Free S M₁]
variable [Algebra S R] [IsScalarTower S R M] [Module.Free R M]

open Module.Free

/-- The `S`-rank of `M ⊗[R] M'` is `(Module.rank S M).lift * (Module.rank R M').lift`. -/
@[simp]
/--
theorem `rank_tensorProduct` / 定理 `rank_tensorProduct`

English:
theorem rank_tensorProduct
  proof: by
  obtain ⟨⟨_, bM⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  obtain ⟨⟨_, bN⟩⟩ := Module.Free.exists_basis (R := S) (M := M')
  rw [← bM.mk_eq_rank'']; rw [← bN.mk_eq_rank'']; rw [← (bM.tensorProduct bN).mk_eq_rank'']; rw [Cardinal.mk_prod]

中文:
定理 rank_tensorProduct
  证明: by
  obtain ⟨⟨_, bM⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  obtain ⟨⟨_, bN⟩⟩ := Module.Free.exists_basis (R := S) (M := M')
  rw [← bM.mk_eq_rank'']; rw [← bN.mk_eq_rank'']; rw [← (bM.tensorProduct bN).mk_eq_rank'']; rw [Cardinal.mk_prod]

Depends on / 依赖: Cardinal, Cardinal.mk_prod, Module, Module.Free.exists_basis, bM.mk_eq_rank, bM.tensorProduct, bN.mk_eq_rank, exists_basis, mk_eq_rank, mk_prod, tensorProduct
-/
theorem rank_tensorProduct :
    Module.rank R (M otimes[S] M') =
      Cardinal.lift.{v'} (Module.rank R M) * Cardinal.lift.{v} (Module.rank S M') := by
  obtain ⟨⟨_, bM⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  obtain ⟨⟨_, bN⟩⟩ := Module.Free.exists_basis (R := S) (M := M')
  rw [← bM.mk_eq_rank'']; rw [← bN.mk_eq_rank'']; rw [← (bM.tensorProduct bN).mk_eq_rank'']; rw [Cardinal.mk_prod]

/--
theorem `rank_tensorProduct'` / 定理 `rank_tensorProduct'`

English:
theorem rank_tensorProduct'
  proof: by simp

中文:
定理 rank_tensorProduct'
  证明: by simp
-/
theorem rank_tensorProduct' :
    Module.rank R (M otimes[S] M₁) = Module.rank R M * Module.rank S M₁ := by simp

/--
theorem `Module.rank_baseChange` / 定理 `Module.rank_baseChange`

English:
theorem Module.rank_baseChange
  proof: by simp

中文:
定理 Module.rank_baseChange
  证明: by simp
-/
theorem Module.rank_baseChange :
    Module.rank R (R otimes[S] M') = Cardinal.lift.{u} (Module.rank S M') := by simp

/-- The `S`-`finrank` of `M ⊗[R] M'` is `(finrank S M) * (finrank R M')`. -/
@[simp]
/--
theorem `Module.finrank_tensorProduct` / 定理 `Module.finrank_tensorProduct`

English:
theorem Module.finrank_tensorProduct
  proof: by simp [finrank]

中文:
定理 Module.finrank_tensorProduct
  证明: by simp [finrank]

Depends on / 依赖: finrank
-/
theorem Module.finrank_tensorProduct :
    finrank R (M otimes[S] M') = finrank R M * finrank S M' := by simp [finrank]

/--
theorem `Module.finrank_baseChange` / 定理 `Module.finrank_baseChange`

English:
theorem Module.finrank_baseChange
  statement: finrank R (R otimes[S] M') = finrank S M'
  proof: by simp

中文:
定理 Module.finrank_baseChange
  结论: finrank R (R otimes[S] M') = finrank S M'
  证明: by simp
-/
theorem Module.finrank_baseChange : finrank R (R otimes[S] M') = finrank S M' := by simp

end TensorProduct

section SubmoduleRank

section

open Module

namespace Submodule

/--
theorem `lt_of_le_of_finrank_lt_finrank` / 定理 `lt_of_le_of_finrank_lt_finrank`

English:
theorem lt_of_le_of_finrank_lt_finrank
  statement: {s t : Submodule R M} (le : s <= t)
  proof: lt_of_le_of_ne le fun h => ne_of_lt lt (by rw [h])

中文:
定理 lt_of_le_of_finrank_lt_finrank
  结论: {s t : Submodule R M} (le : s <= t)
  证明: lt_of_le_of_ne le fun h => ne_of_lt lt (by rw [h])

Depends on / 依赖: lt_of_le_of_ne, ne_of_lt
-/
theorem lt_of_le_of_finrank_lt_finrank {s t : Submodule R M} (le : s <= t)
    (lt : finrank R s < finrank R t) : s < t :=
  lt_of_le_of_ne le fun h => ne_of_lt lt (by rw [h])

/--
theorem `lt_top_of_finrank_lt_finrank` / 定理 `lt_top_of_finrank_lt_finrank`

English:
theorem lt_top_of_finrank_lt_finrank
  given: {s : Submodule R M} (lt : finrank R s < finrank R M)
  proof: by
  rw [← finrank_top R M] at lt
  exact lt_of_le_of_finrank_lt_finrank le_top lt

中文:
定理 lt_top_of_finrank_lt_finrank
  条件: {s : Submodule R M} (lt : finrank R s < finrank R M)
  证明: by
  rw [← finrank_top R M] at lt
  exact lt_of_le_of_finrank_lt_finrank le_top lt

Depends on / 依赖: finrank_top, le_top, lt_of_le_of_finrank_lt_finrank
-/
theorem lt_top_of_finrank_lt_finrank {s : Submodule R M} (lt : finrank R s < finrank R M) :
    s < ⊤ := by
  rw [← finrank_top R M] at lt
  exact lt_of_le_of_finrank_lt_finrank le_top lt

end Submodule

variable [StrongRankCondition R]

/--
theorem `Submodule.finrank_le` / 定理 `Submodule.finrank_le`

English:
theorem Submodule.finrank_le
  given: [Module.Finite R M] (s : Submodule R M)
  proof: toNat_le_toNat (Submodule.rank_le s) (rank_lt_aleph0 _ _)

中文:
定理 Submodule.finrank_le
  条件: [Module.Finite R M] (s : Submodule R M)
  证明: toNat_le_toNat (Submodule.rank_le s) (rank_lt_aleph0 _ _)

Depends on / 依赖: Submodule, Submodule.rank_le, rank_le, rank_lt_aleph0, toNat_le_toNat
-/
theorem Submodule.finrank_le [Module.Finite R M] (s : Submodule R M) :
    finrank R s <= finrank R M :=
  toNat_le_toNat (Submodule.rank_le s) (rank_lt_aleph0 _ _)

/--
theorem `Submodule.finrank_map_le` / 定理 `Submodule.finrank_map_le`

English:
theorem Submodule.finrank_map_le
  proof: finrank_le_finrank_of_rank_le_rank (lift_rank_map_le _ _) (rank_lt_aleph0 _ _)

中文:
定理 Submodule.finrank_map_le
  证明: finrank_le_finrank_of_rank_le_rank (lift_rank_map_le _ _) (rank_lt_aleph0 _ _)

Depends on / 依赖: finrank_le_finrank_of_rank_le_rank, lift_rank_map_le, rank_lt_aleph0
-/
theorem Submodule.finrank_map_le
    [Module R M'] (f : M ->ₗ[R] M') (p : Submodule R M) [Module.Finite R p] :
    finrank R (p.map f) <= finrank R p :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_map_le _ _) (rank_lt_aleph0 _ _)

/--
theorem `Submodule.finrank_mono` / 定理 `Submodule.finrank_mono`

English:
theorem Submodule.finrank_mono
  given: {s t : Submodule R M} [Module.Finite R t] (hst : s <= t)
  proof: Cardinal.toNat_le_toNat (Submodule.rank_mono hst) (rank_lt_aleph0 R ↥t)

中文:
定理 Submodule.finrank_mono
  条件: {s t : Submodule R M} [Module.Finite R t] (hst : s <= t)
  证明: Cardinal.toNat_le_toNat (Submodule.rank_mono hst) (rank_lt_aleph0 R ↥t)

Depends on / 依赖: Cardinal, Cardinal.toNat_le_toNat, Submodule, Submodule.rank_mono, rank_lt_aleph0, rank_mono, toNat_le_toNat
-/
theorem Submodule.finrank_mono {s t : Submodule R M} [Module.Finite R t] (hst : s <= t) :
    finrank R s <= finrank R t :=
  Cardinal.toNat_le_toNat (Submodule.rank_mono hst) (rank_lt_aleph0 R ↥t)

end

end SubmoduleRank

section Span

variable [StrongRankCondition R]

/--
theorem `rank_span_le` / 定理 `rank_span_le`

English:
theorem rank_span_le
  given: (s : Set M)
  statement: Module.rank R (span R s) <= #s
  proof: by
  rw [Finsupp.span_eq_range_linearCombination]; rw [← lift_strictMono.le_iff_le]
  refine (lift_rank_range_le _).trans ?_
  rw [rank_finsupp_self]
  simp only [lift_lift, le_refl]

中文:
定理 rank_span_le
  条件: (s : Set M)
  结论: Module.rank R (span R s) <= #s
  证明: by
  rw [Finsupp.span_eq_range_linearCombination]; rw [← lift_strictMono.le_iff_le]
  refine (lift_rank_range_le _).trans ?_
  rw [rank_finsupp_self]
  simp only [lift_lift, le_refl]

Depends on / 依赖: Finsupp, Finsupp.span_eq_range_linearCombination, le_iff_le, le_refl, lift_lift, lift_rank_range_le, lift_strictMono, lift_strictMono.le_iff_le, rank_finsupp_self, span_eq_range_linearCombination
-/
theorem rank_span_le (s : Set M) : Module.rank R (span R s) <= #s := by
  rw [Finsupp.span_eq_range_linearCombination]; rw [← lift_strictMono.le_iff_le]
  refine (lift_rank_range_le _).trans ?_
  rw [rank_finsupp_self]
  simp only [lift_lift, le_refl]

/--
theorem `rank_span_finset_le` / 定理 `rank_span_finset_le`

English:
theorem rank_span_finset_le
  given: (s : Finset M)
  statement: Module.rank R (span R (s : Set M)) <= s.card
  proof: by
  simpa using rank_span_le (s : Set M)

中文:
定理 rank_span_finset_le
  条件: (s : Finset M)
  结论: Module.rank R (span R (s : Set M)) <= s.card
  证明: by
  simpa using rank_span_le (s : Set M)

Depends on / 依赖: rank_span_le
-/
theorem rank_span_finset_le (s : Finset M) : Module.rank R (span R (s : Set M)) <= s.card := by
  simpa using rank_span_le (s : Set M)

/--
theorem `rank_span_of_finset` / 定理 `rank_span_of_finset`

English:
theorem rank_span_of_finset
  given: (s : Finset M)
  statement: Module.rank R (span R (s : Set M)) < ℵ₀
  proof: (rank_span_finset_le s).trans_lt natCast_lt_aleph0

中文:
定理 rank_span_of_finset
  条件: (s : Finset M)
  结论: Module.rank R (span R (s : Set M)) < ℵ₀
  证明: (rank_span_finset_le s).trans_lt natCast_lt_aleph0

Depends on / 依赖: natCast_lt_aleph0, rank_span_finset_le, trans_lt
-/
theorem rank_span_of_finset (s : Finset M) : Module.rank R (span R (s : Set M)) < ℵ₀ :=
  (rank_span_finset_le s).trans_lt natCast_lt_aleph0

open Submodule Module

variable (R) in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Set.finrank (s : Set M)
  body: finrank R (span R s)

中文:
定义 noncomputable
  签名: def Set.finrank (s : Set M)
  定义体: finrank R (span R s)
-/
protected noncomputable def Set.finrank (s : Set M) : Nat :=
  finrank R (span R s)

/--
theorem `finrank_span_le_card` / 定理 `finrank_span_le_card`

English:
theorem finrank_span_le_card
  given: (s : Set M) [Fintype s]
  statement: finrank R (span R s) <= s.toFinset.card
  proof: finrank_le_of_rank_le (by simpa using rank_span_le (R := R) s)

中文:
定理 finrank_span_le_card
  条件: (s : Set M) [Fintype s]
  结论: finrank R (span R s) <= s.toFinset.card
  证明: finrank_le_of_rank_le (by simpa using rank_span_le (R := R) s)

Depends on / 依赖: finrank_le_of_rank_le, rank_span_le
-/
theorem finrank_span_le_card (s : Set M) [Fintype s] : finrank R (span R s) <= s.toFinset.card :=
  finrank_le_of_rank_le (by simpa using rank_span_le (R := R) s)

/--
theorem `finrank_span_finset_le_card` / 定理 `finrank_span_finset_le_card`

English:
theorem finrank_span_finset_le_card
  given: (s : Finset M)
  statement: (s : Set M).finrank R <= s.card
  proof: calc
    (s : Set M).finrank R <= (s : Set M).toFinset.card := finrank_span_le_card (M := M) s
    _ = s.card := by simp

中文:
定理 finrank_span_finset_le_card
  条件: (s : Finset M)
  结论: (s : Set M).finrank R <= s.card
  证明: calc
    (s : Set M).finrank R <= (s : Set M).toFinset.card := finrank_span_le_card (M := M) s
    _ = s.card := by simp

Depends on / 依赖: finrank, finrank_span_le_card, s.card, toFinset, toFinset.card
-/
theorem finrank_span_finset_le_card (s : Finset M) : (s : Set M).finrank R <= s.card :=
  calc
    (s : Set M).finrank R <= (s : Set M).toFinset.card := finrank_span_le_card (M := M) s
    _ = s.card := by simp

/--
theorem `finrank_range_le_card` / 定理 `finrank_range_le_card`

English:
theorem finrank_range_le_card
  given: {ι : Type*} [Fintype ι] (b : ι -> M)
  proof: by
  classical
  refine (finrank_span_le_card _).trans ?_
  rw [Set.toFinset_range]
  exact Finset.card_image_le

中文:
定理 finrank_range_le_card
  条件: {ι : 类型} [Fintype ι] (b : ι -> M)
  证明: by
  classical
  refine (finrank_span_le_card _).trans ?_
  rw [Set.toFinset_range]
  exact Finset.card_image_le

Depends on / 依赖: Finset, Finset.card_image_le, Set.toFinset_range, card_image_le, classical, finrank_span_le_card, toFinset_range
-/
theorem finrank_range_le_card {ι : Type*} [Fintype ι] (b : ι -> M) :
    (Set.range b).finrank R <= Fintype.card ι := by
  classical
  refine (finrank_span_le_card _).trans ?_
  rw [Set.toFinset_range]
  exact Finset.card_image_le

/--
theorem `finrank_span_eq_card` / 定理 `finrank_span_eq_card`

English:
theorem finrank_span_eq_card
  statement: [Nontrivial R] {ι : Type*} [Fintype ι] {b : ι -> M}
  proof: finrank_eq_of_rank_eq
    (by
      have : Module.rank R (span R (Set.range b)) = #(Set.range b) := rank_span hb
      rwa [← lift_inj, mk_range_eq_of_injective hb.injective, Cardinal.mk_fintype, lift_natCast,
        lift_eq_nat_iff] at this)

中文:
定理 finrank_span_eq_card
  结论: [Nontrivial R] {ι : 类型} [Fintype ι] {b : ι -> M}
  证明: finrank_eq_of_rank_eq
    (by
      have : Module.rank R (span R (Set.range b)) = #(Set.range b) := rank_span hb
      rwa [← lift_inj, mk_range_eq_of_injective hb.injective, Cardinal.mk_fintype, lift_natCast,
        lift_eq_nat_iff] at this)

Depends on / 依赖: Cardinal, Cardinal.mk_fintype, Module, Module.rank, Set.range, finrank_eq_of_rank_eq, hb.injective, injective, lift_eq_nat_iff, lift_inj, lift_natCast, mk_fintype, mk_range_eq_of_injective, rank_span
-/
theorem finrank_span_eq_card [Nontrivial R] {ι : Type*} [Fintype ι] {b : ι -> M}
    (hb : LinearIndependent R b) :
    finrank R (span R (Set.range b)) = Fintype.card ι :=
  finrank_eq_of_rank_eq
    (by
      have : Module.rank R (span R (Set.range b)) = #(Set.range b) := rank_span hb
      rwa [← lift_inj, mk_range_eq_of_injective hb.injective, Cardinal.mk_fintype, lift_natCast,
        lift_eq_nat_iff] at this)

/--
theorem `finrank_span_set_eq_card` / 定理 `finrank_span_set_eq_card`

English:
theorem finrank_span_set_eq_card
  given: {s : Set M} [Fintype s] (hs : LinearIndepOn R id s)
  proof: finrank_eq_of_rank_eq
    (by
      have : Module.rank R (span R s) = #s := rank_span_set hs
      rwa [Cardinal.mk_fintype, ← Set.toFinset_card] at this)

中文:
定理 finrank_span_set_eq_card
  条件: {s : Set M} [Fintype s] (hs : LinearIndepOn R id s)
  证明: finrank_eq_of_rank_eq
    (by
      have : Module.rank R (span R s) = #s := rank_span_set hs
      rwa [Cardinal.mk_fintype, ← Set.toFinset_card] at this)

Depends on / 依赖: Cardinal, Cardinal.mk_fintype, Module, Module.rank, Set.toFinset_card, finrank_eq_of_rank_eq, mk_fintype, rank_span_set, toFinset_card
-/
theorem finrank_span_set_eq_card {s : Set M} [Fintype s] (hs : LinearIndepOn R id s) :
    finrank R (span R s) = s.toFinset.card :=
  finrank_eq_of_rank_eq
    (by
      have : Module.rank R (span R s) = #s := rank_span_set hs
      rwa [Cardinal.mk_fintype, ← Set.toFinset_card] at this)

/--
theorem `finrank_span_finset_eq_card` / 定理 `finrank_span_finset_eq_card`

English:
theorem finrank_span_finset_eq_card
  given: {s : Finset M} (hs : LinearIndepOn R id (s : Set M))
  proof: by
  convert! finrank_span_set_eq_card (s := (s : Set M)) hs
  ext
  simp

中文:
定理 finrank_span_finset_eq_card
  条件: {s : Finset M} (hs : LinearIndepOn R id (s : Set M))
  证明: by
  convert! finrank_span_set_eq_card (s := (s : Set M)) hs
  ext
  simp

Depends on / 依赖: convert, finrank_span_set_eq_card
-/
theorem finrank_span_finset_eq_card {s : Finset M} (hs : LinearIndepOn R id (s : Set M)) :
    finrank R (span R (s : Set M)) = s.card := by
  convert! finrank_span_set_eq_card (s := (s : Set M)) hs
  ext
  simp

/--
theorem `span_lt_of_subset_of_card_lt_finrank` / 定理 `span_lt_of_subset_of_card_lt_finrank`

English:
theorem span_lt_of_subset_of_card_lt_finrank
  statement: {s : Set M} [Fintype s] {t : Submodule R M}
  proof: lt_of_le_of_finrank_lt_finrank (span_le.mpr subset)
    (lt_of_le_of_lt (finrank_span_le_card _) card_lt)

中文:
定理 span_lt_of_subset_of_card_lt_finrank
  结论: {s : Set M} [Fintype s] {t : Submodule R M}
  证明: lt_of_le_of_finrank_lt_finrank (span_le.mpr subset)
    (lt_of_le_of_lt (finrank_span_le_card _) card_lt)

Depends on / 依赖: card_lt, finrank_span_le_card, induction_on, integrable_mk, lt_of_le_of_finrank_lt_finrank, lt_of_le_of_lt, span_le, span_le.mpr, subset
-/
theorem span_lt_of_subset_of_card_lt_finrank {s : Set M} [Fintype s] {t : Submodule R M}
    (subset : s subseteq t) (card_lt : s.toFinset.card < finrank R t) : span R s < t :=
  lt_of_le_of_finrank_lt_finrank (span_le.mpr subset)
    (lt_of_le_of_lt (finrank_span_le_card _) card_lt)

/--
theorem `span_lt_top_of_card_lt_finrank` / 定理 `span_lt_top_of_card_lt_finrank`

English:
theorem span_lt_top_of_card_lt_finrank
  statement: {s : Set M} [Fintype s]
  proof: lt_top_of_finrank_lt_finrank (lt_of_le_of_lt (finrank_span_le_card _) card_lt)

中文:
定理 span_lt_top_of_card_lt_finrank
  结论: {s : Set M} [Fintype s]
  证明: lt_top_of_finrank_lt_finrank (lt_of_le_of_lt (finrank_span_le_card _) card_lt)

Depends on / 依赖: card_lt, finrank_span_le_card, lt_of_le_of_lt, lt_top_of_finrank_lt_finrank
-/
theorem span_lt_top_of_card_lt_finrank {s : Set M} [Fintype s]
    (card_lt : s.toFinset.card < finrank R M) : span R s < ⊤ :=
  lt_top_of_finrank_lt_finrank (lt_of_le_of_lt (finrank_span_le_card _) card_lt)

/--
lemma `finrank_le_of_span_eq_top` / 引理 `finrank_le_of_span_eq_top`

English:
lemma finrank_le_of_span_eq_top
  statement: {ι : Type*} [Fintype ι] {v : ι -> M}
  proof: by
  classical
  rw [← finrank_top]; rw [← hv]
  exact (finrank_span_le_card _).trans (by convert! Fintype.card_range_le v; rw [Set.toFinset_card])

@[simp]

中文:
引理 finrank_le_of_span_eq_top
  结论: {ι : 类型} [Fintype ι] {v : ι -> M}
  证明: by
  classical
  rw [← finrank_top]; rw [← hv]
  exact (finrank_span_le_card _).trans (by convert! Fintype.card_range_le v; rw [Set.toFinset_card])

@[simp]

Depends on / 依赖: Fintype, Fintype.card_range_le, Set.toFinset_card, card_range_le, classical, convert, finrank_span_le_card, finrank_top, hfi.add, integrable_mk, mk_add_mk, toFinset_card
-/
lemma finrank_le_of_span_eq_top {ι : Type*} [Fintype ι] {v : ι -> M}
    (hv : Submodule.span R (Set.range v) = ⊤) : finrank R M <= Fintype.card ι := by
  classical
  rw [← finrank_top]; rw [← hv]
  exact (finrank_span_le_card _).trans (by convert! Fintype.card_range_le v; rw [Set.toFinset_card])

@[simp]
/--
lemma `Pi.dim_spanSubset` / 引理 `Pi.dim_spanSubset`

English:
lemma Pi.dim_spanSubset
  given: [Finite ι] [Nontrivial R] {s : Set ι}
  proof: by
  classical
  have := Fintype.ofFinite ι
  rw [Pi.spanSubset]; rw [finrank_span_set_eq_card <| (Pi.basisFun R ι).linearIndepOn _ |>.id_image]; rw [Set.toFinset_card]; rw [Fintype.card_eq_nat_card]; rw [Nat.card_coe_set_eq]
exact Set.ncard_image_of_injective s (Pi.basisFun R ι).injective

中文:
引理 Pi.dim_spanSubset
  条件: [Finite ι] [Nontrivial R] {s : Set ι}
  证明: by
  classical
  have := Fintype.ofFinite ι
  rw [Pi.spanSubset]; rw [finrank_span_set_eq_card <| (Pi.basisFun R ι).linearIndepOn _ |>.id_image]; rw [Set.toFinset_card]; rw [Fintype.card_eq_nat_card]; rw [Nat.card_coe_set_eq]
exact Set.ncard_image_of_injective s (Pi.basisFun R ι).injective

Depends on / 依赖: Fintype, Fintype.card_eq_nat_card, Fintype.ofFinite, Nat.card_coe_set_eq, Pi.basisFun, Pi.spanSubset, Set.ncard_image_of_injective, Set.toFinset_card, basisFun, card_coe_set_eq, card_eq_nat_card, classical, finrank_span_set_eq_card, hf.add, hg.neg, id_image, injective, linearIndepOn, ncard_image_of_injective, ofFinite
-/
lemma Pi.dim_spanSubset [Finite ι] [Nontrivial R] {s : Set ι} :
    Module.finrank R (Pi.spanSubset R s) = s.ncard := by
  classical
  have := Fintype.ofFinite ι
  rw [Pi.spanSubset]; rw [finrank_span_set_eq_card <| (Pi.basisFun R ι).linearIndepOn _ |>.id_image]; rw [Set.toFinset_card]; rw [Fintype.card_eq_nat_card]; rw [Nat.card_coe_set_eq]
exact Set.ncard_image_of_injective s (Pi.basisFun R ι).injective

end Span

section SubalgebraRank

open Module

section Semiring

variable {F E : Type*} [CommSemiring F] [Semiring E] [Algebra F E]

@[simp]
/--
theorem `Subalgebra.rank_toSubmodule` / 定理 `Subalgebra.rank_toSubmodule`

English:
theorem Subalgebra.rank_toSubmodule
  given: (S : Subalgebra F E)
  proof: rfl

@[simp]

中文:
定理 Subalgebra.rank_toSubmodule
  条件: (S : Subalgebra F E)
  证明: rfl

@[simp]

Depends on / 依赖: induction_on, integrable_mk
-/
theorem Subalgebra.rank_toSubmodule (S : Subalgebra F E) :
    Module.rank F (Subalgebra.toSubmodule S) = Module.rank F S :=
  rfl

@[simp]
/--
theorem `Subalgebra.finrank_toSubmodule` / 定理 `Subalgebra.finrank_toSubmodule`

English:
theorem Subalgebra.finrank_toSubmodule
  given: (S : Subalgebra F E)
  proof: rfl

中文:
定理 Subalgebra.finrank_toSubmodule
  条件: (S : Subalgebra F E)
  证明: rfl
-/
theorem Subalgebra.finrank_toSubmodule (S : Subalgebra F E) :
    finrank F (Subalgebra.toSubmodule S) = finrank F S :=
  rfl

/--
theorem `subalgebra_top_rank_eq_submodule_top_rank` / 定理 `subalgebra_top_rank_eq_submodule_top_rank`

English:
theorem subalgebra_top_rank_eq_submodule_top_rank
  proof: by
  rw [← Algebra.top_toSubmodule]
  rfl

中文:
定理 subalgebra_top_rank_eq_submodule_top_rank
  证明: by
  rw [← Algebra.top_toSubmodule]
  rfl

Depends on / 依赖: Algebra, Algebra.top_toSubmodule, top_toSubmodule
-/
theorem subalgebra_top_rank_eq_submodule_top_rank :
    Module.rank F (⊤ : Subalgebra F E) = Module.rank F (⊤ : Submodule F E) := by
  rw [← Algebra.top_toSubmodule]
  rfl

/--
theorem `subalgebra_top_finrank_eq_submodule_top_finrank` / 定理 `subalgebra_top_finrank_eq_submodule_top_finrank`

English:
theorem subalgebra_top_finrank_eq_submodule_top_finrank
  proof: by
  rw [← Algebra.top_toSubmodule]
  rfl

中文:
定理 subalgebra_top_finrank_eq_submodule_top_finrank
  证明: by
  rw [← Algebra.top_toSubmodule]
  rfl

Depends on / 依赖: Algebra, Algebra.top_toSubmodule, top_toSubmodule
-/
theorem subalgebra_top_finrank_eq_submodule_top_finrank :
    finrank F (⊤ : Subalgebra F E) = finrank F (⊤ : Submodule F E) := by
  rw [← Algebra.top_toSubmodule]
  rfl

/--
theorem `Subalgebra.rank_top` / 定理 `Subalgebra.rank_top`

English:
theorem Subalgebra.rank_top
  statement: Module.rank F (⊤ : Subalgebra F E) = Module.rank F E
  proof: by
  rw [subalgebra_top_rank_eq_submodule_top_rank]
  exact _root_.rank_top F E

中文:
定理 Subalgebra.rank_top
  结论: Module.rank F (⊤ : Subalgebra F E) = Module.rank F E
  证明: by
  rw [subalgebra_top_rank_eq_submodule_top_rank]
  exact _root_.rank_top F E

Depends on / 依赖: _root_, _root_.rank_top, rank_top, subalgebra_top_rank_eq_submodule_top_rank
-/
theorem Subalgebra.rank_top : Module.rank F (⊤ : Subalgebra F E) = Module.rank F E := by
  rw [subalgebra_top_rank_eq_submodule_top_rank]
  exact _root_.rank_top F E

end Semiring

section Ring

variable {F E : Type*} [CommRing F] [IsDomain F] [Ring E] [Algebra F E]
variable [StrongRankCondition F] [IsTorsionFree F E] [Nontrivial E]

@[simp]
/--
theorem `Subalgebra.rank_bot` / 定理 `Subalgebra.rank_bot`

English:
theorem Subalgebra.rank_bot
  statement: Module.rank F (⊥ : Subalgebra F E) = 1
  proof: (Subalgebra.toSubmoduleEquiv (⊥ : Subalgebra F E)).symm.rank_eq.trans by
    rw [Algebra.toSubmodule_bot]; rw [one_eq_span]; rw [rank_span_set]; rw [mk_singleton _]
    have := Module.nontrivial F E
    exact .singleton one_ne_zero

@[simp]

中文:
定理 Subalgebra.rank_bot
  结论: Module.rank F (⊥ : Subalgebra F E) = 1
  证明: (Subalgebra.toSubmoduleEquiv (⊥ : Subalgebra F E)).symm.rank_eq.trans by
    rw [Algebra.toSubmodule_bot]; rw [one_eq_span]; rw [rank_span_set]; rw [mk_singleton _]
    have := Module.nontrivial F E
    exact .singleton one_ne_zero

@[simp]

Depends on / 依赖: Algebra, Algebra.toSubmodule_bot, Module, Module.nontrivial, Subalgebra, Subalgebra.toSubmoduleEquiv, mk_singleton, nontrivial, one_eq_span, one_ne_zero, rank_eq, rank_span_set, singleton, symm.rank_eq.trans, toSubmoduleEquiv, toSubmodule_bot
-/
theorem Subalgebra.rank_bot : Module.rank F (⊥ : Subalgebra F E) = 1 :=
(Subalgebra.toSubmoduleEquiv (⊥ : Subalgebra F E)).symm.rank_eq.trans by
    rw [Algebra.toSubmodule_bot]; rw [one_eq_span]; rw [rank_span_set]; rw [mk_singleton _]
    have := Module.nontrivial F E
    exact .singleton one_ne_zero

@[simp]
/--
theorem `Subalgebra.finrank_bot` / 定理 `Subalgebra.finrank_bot`

English:
theorem Subalgebra.finrank_bot
  statement: finrank F (⊥ : Subalgebra F E) = 1
  proof: finrank_eq_of_rank_eq (by simp)

中文:
定理 Subalgebra.finrank_bot
  结论: finrank F (⊥ : Subalgebra F E) = 1
  证明: finrank_eq_of_rank_eq (by simp)

Depends on / 依赖: finrank_eq_of_rank_eq
-/
theorem Subalgebra.finrank_bot : finrank F (⊥ : Subalgebra F E) = 1 :=
  finrank_eq_of_rank_eq (by simp)

end Ring

end SubalgebraRank

section Extend

namespace Module.Basis

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {W : Submodule R V} {m n : Type*}
    (bW : Basis m R W) (bQ : Basis n R (V ⧸ W))

/--
Definition of `sumQuot` / `sumQuot` 的定义

English:
definition sumQuot
  signature: :
  body: by
  let b : m oplus n -> V := Sum.elim (fun i => bW i) ((Function.surjInv W.mkQ_surjective) ∘ bQ)
  have br : W.mkQ ∘ b ∘ Sum.inr = bQ := by
    ext j
    apply Function.rightInverse_surjInv W.mkQ_surjective
  apply Basis.mk (v := b)
  · apply LinearIndependent.sumElim_of_quotient
    · exact bW.li

中文:
定义 sumQuot
  签名: :
  定义体: by
  let b : m oplus n -> V := Sum.elim (fun i => bW i) ((Function.surjInv W.mkQ_surjective) ∘ bQ)
  have br : W.mkQ ∘ b ∘ Sum.inr = bQ := by
    ext j
    apply Function.rightInverse_surjInv W.mkQ_surjective
  apply Basis.mk (v := b)
  · apply LinearIndependent.sumElim_of_quotient
    · exact bW.li

Depends on / 依赖: Basis.mk, Function, Function.rightInverse_surjInv, Function.surjInv, LinearIndependent, LinearIndependent.sumElim_of_quotient, Set.Sum.elim_range, Set.range, Submodul, Submodule, Submodule.span_union, Sum.elim, Sum.inr, W.mkQ, W.mkQ_surjective, W.subtype, bQ.linearIndependent, bW.linearIndependent, convert, elim_range
-/
noncomputable def sumQuot :
    Basis (m oplus n) R V := by
  let b : m oplus n -> V := Sum.elim (fun i => bW i) ((Function.surjInv W.mkQ_surjective) ∘ bQ)
  have br : W.mkQ ∘ b ∘ Sum.inr = bQ := by
    ext j
    apply Function.rightInverse_surjInv W.mkQ_surjective
  apply Basis.mk (v := b)
  · apply LinearIndependent.sumElim_of_quotient
    · exact bW.linearIndependent
    · convert! bQ.linearIndependent
  · unfold b
    rw [Set.Sum.elim_range]; rw [Submodule.span_union]; rw [show Set.range (fun i => (bW i : V)) = W.subtype '' (Set.range (fun i => bW i)) by aesop]; rw [← Submodule.map_span]; rw [bW.span_eq]; rw [Submodule.map_top]; rw [Submodule.range_subtype]; rw [top_le_iff]; rw [← Submodule.map_mkQ_eq_top]; rw [Submodule.map_span]; rw [← Set.range_comp]; rw [← bQ.span_eq]
    congr 2

@[simp]
/--
theorem `sumQuot_inl` / 定理 `sumQuot_inl`

English:
theorem sumQuot_inl
  given: (i : m)
  proof: by
  simp [sumQuot]

@[simp]

中文:
定理 sumQuot_inl
  条件: (i : m)
  证明: by
  simp [sumQuot]

@[simp]

Depends on / 依赖: sumQuot
-/
theorem sumQuot_inl (i : m) :
    sumQuot bW bQ (Sum.inl i) = bW i := by
  simp [sumQuot]

@[simp]
/--
theorem `sumQuot_inr` / 定理 `sumQuot_inr`

English:
theorem sumQuot_inr
  given: (j : n)
  proof: by
  simpa only [sumQuot, Basis.coe_mk, Sum.elim_inr, Function.comp_apply, ← W.mkQ_apply]
    using Function.rightInverse_surjInv W.mkQ_surjective _

@[simp]

中文:
定理 sumQuot_inr
  条件: (j : n)
  证明: by
  simpa only [sumQuot, Basis.coe_mk, Sum.elim_inr, Function.comp_apply, ← W.mkQ_apply]
    using Function.rightInverse_surjInv W.mkQ_surjective _

@[simp]

Depends on / 依赖: Basis.coe_mk, Function, Function.comp_apply, Function.rightInverse_surjInv, Sum.elim_inr, W.mkQ_apply, W.mkQ_surjective, coe_mk, comp_apply, elim_inr, mkQ_apply, mkQ_surjective, rightInverse_surjInv, sumQuot
-/
theorem sumQuot_inr (j : n) :
    Submodule.Quotient.mk (sumQuot bW bQ (Sum.inr j)) = bQ j := by
  simpa only [sumQuot, Basis.coe_mk, Sum.elim_inr, Function.comp_apply, ← W.mkQ_apply]
    using Function.rightInverse_surjInv W.mkQ_surjective _

@[simp]
/--
theorem `sumQuot_repr_left` / 定理 `sumQuot_repr_left`

English:
theorem sumQuot_repr_left
  given: (i : m)
  proof: by
  rw [← Module.Basis.apply_eq_iff]; rw [sumQuot_inl]

中文:
定理 sumQuot_repr_left
  条件: (i : m)
  证明: by
  rw [← Module.Basis.apply_eq_iff]; rw [sumQuot_inl]

Depends on / 依赖: Module, Module.Basis.apply_eq_iff, apply_eq_iff, sumQuot_inl
-/
theorem sumQuot_repr_left (i : m) :
    (sumQuot bW bQ).repr (bW i) = Finsupp.single (Sum.inl i) 1 := by
  rw [← Module.Basis.apply_eq_iff]; rw [sumQuot_inl]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sumQuot_repr_inl` / 定理 `sumQuot_repr_inl`

English:
theorem sumQuot_repr_inl
  given: (w : W) (i : m)
  proof: by
  classical
refine Eq.symm (bW.repr_apply_eq
      (fun w i => (sumQuot bW bQ).repr (W.subtype w) (Sum.inl i)) ?_ ?_ ?_ w i) <;>
  aesop (add simp Finsupp.single_apply)

@[simp]

中文:
定理 sumQuot_repr_inl
  条件: (w : W) (i : m)
  证明: by
  classical
refine Eq.symm (bW.repr_apply_eq
      (fun w i => (sumQuot bW bQ).repr (W.subtype w) (Sum.inl i)) ?_ ?_ ?_ w i) <;>
  aesop (add simp Finsupp.single_apply)

@[simp]

Depends on / 依赖: Eq.symm, Finsupp, Finsupp.single_apply, Sum.inl, W.subtype, bW.repr_apply_eq, classical, repr_apply_eq, single_apply, subtype, sumQuot
-/
theorem sumQuot_repr_inl (w : W) (i : m) :
    (sumQuot bW bQ).repr w (Sum.inl i) = bW.repr w i := by
  classical
refine Eq.symm (bW.repr_apply_eq
      (fun w i => (sumQuot bW bQ).repr (W.subtype w) (Sum.inl i)) ?_ ?_ ?_ w i) <;>
  aesop (add simp Finsupp.single_apply)

@[simp]
/--
theorem `sumQuot_repr_inl_of_mem` / 定理 `sumQuot_repr_inl_of_mem`

English:
theorem sumQuot_repr_inl_of_mem
  given: (v : V) (hv : v in W) (i : m)
  proof: sumQuot_repr_inl bW bQ ⟨v, hv⟩ i

@[simp]

中文:
定理 sumQuot_repr_inl_of_mem
  条件: (v : V) (hv : v in W) (i : m)
  证明: sumQuot_repr_inl bW bQ ⟨v, hv⟩ i

@[simp]

Depends on / 依赖: sumQuot_repr_inl
-/
theorem sumQuot_repr_inl_of_mem (v : V) (hv : v in W) (i : m) :
    (sumQuot bW bQ).repr v (Sum.inl i) = bW.repr ⟨v, hv⟩ i :=
  sumQuot_repr_inl bW bQ ⟨v, hv⟩ i

@[simp]
/--
theorem `sumQuot_repr_inr` / 定理 `sumQuot_repr_inr`

English:
theorem sumQuot_repr_inr
  given: (v : V) (j : n)
  proof: by
  simp only [← Module.Basis.coord_apply]
  rw [← LinearMap.comp_apply]
  revert v
  rw [← LinearMap.ext_iff]
  apply (sumQuot bW bQ).ext
  intro x
  induction x with
  | inl i =>
    simp [sumQuot_inl, LinearMap.comp_apply,
      (Quotient.mk_eq_zero W).mpr (Submodule.coe_mem (bW i))]
  | inr i =

中文:
定理 sumQuot_repr_inr
  条件: (v : V) (j : n)
  证明: by
  simp only [← Module.Basis.coord_apply]
  rw [← LinearMap.comp_apply]
  revert v
  rw [← LinearMap.ext_iff]
  apply (sumQuot bW bQ).ext
  intro x
  induction x with
  | inl i =>
    simp [sumQuot_inl, LinearMap.comp_apply,
      (Quotient.mk_eq_zero W).mpr (Submodule.coe_mem (bW i))]
  | inr i =

Depends on / 依赖: Finsupp, Finsupp.single_apply, LinearMap, LinearMap.comp_apply, LinearMap.ext_iff, Module, Module.Basis.coord_apply, Quotient, Quotient.mk_eq_zero, Submodule, Submodule.coe_mem, classical, coe_mem, comp_apply, coord_apply, ext_iff, mk_eq_zero, revert, single_apply, sumQuot
-/
theorem sumQuot_repr_inr (v : V) (j : n) :
    (sumQuot bW bQ).repr v (Sum.inr j) = bQ.repr (W.mkQ v) j := by
  simp only [← Module.Basis.coord_apply]
  rw [← LinearMap.comp_apply]
  revert v
  rw [← LinearMap.ext_iff]
  apply (sumQuot bW bQ).ext
  intro x
  induction x with
  | inl i =>
    simp [sumQuot_inl, LinearMap.comp_apply,
      (Quotient.mk_eq_zero W).mpr (Submodule.coe_mem (bW i))]
  | inr i =>
    classical
    simp [LinearMap.comp_apply, sumQuot_inr, Finsupp.single_apply]

/--
theorem `sumQuot_repr_inr_of_mem` / 定理 `sumQuot_repr_inr_of_mem`

English:
theorem sumQuot_repr_inr_of_mem
  given: (v : V) (hv : v in W) (j : n)
  proof: by
  suffices W.mkQ v = 0 by simp [sumQuot_repr_inr, this]
  aesop

中文:
定理 sumQuot_repr_inr_of_mem
  条件: (v : V) (hv : v in W) (j : n)
  证明: by
  suffices W.mkQ v = 0 by simp [sumQuot_repr_inr, this]
  aesop

Depends on / 依赖: W.mkQ, sumQuot_repr_inr
-/
theorem sumQuot_repr_inr_of_mem (v : V) (hv : v in W) (j : n) :
    (sumQuot bW bQ).repr v (Sum.inr j) = 0 := by
  suffices W.mkQ v = 0 by simp [sumQuot_repr_inr, this]
  aesop

end Module.Basis

end Extend
