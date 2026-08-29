/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Field.Opposite
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.SetTheory.Cardinal.Subfield

/-!
# Erdős-Kaplansky theorem

* `rank_dual_eq_card_dual_of_aleph0_le_rank`: The **Erdős-Kaplansky Theorem** which says that
  the dimension of an infinite-dimensional dual space over a division ring has dimension
  equal to its cardinality.

-/

public section

noncomputable section

universe u v

variable {K : Type u}

open Cardinal

section Cardinal

variable (K)
variable [DivisionRing K]

/--
theorem `max_aleph0_card_le_rank_fun_nat` / 定理 `max_aleph0_card_le_rank_fun_nat`

English:
theorem max_aleph0_card_le_rank_fun_nat
  statement: max ℵ₀ #K <= Module.rank K (Nat -> K)
  proof: by
  have aleph0_le : ℵ₀ <= Module.rank K (Nat -> K) := (rank_finsupp_self K Nat).symm.trans_le
    (Finsupp.lcoeFun.rank_le_of_injective <| by exact DFunLike.coe_injective)
  refine max_le aleph0_le ?_
  obtain card_K | card_K := le_or_gt #K ℵ₀
  · exact card_K.trans aleph0_le
  by_contra!
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := Nat -> K)
  let L := Subfield.closure (Set.range (fun i : ιK × Nat => bK i.1 i.2))
  have hLK : #L < #K := by
    refine (Subfield.cardinalMk_closure_le_max _).trans_lt
      (max_lt_iff.mpr ⟨mk_range_le.trans_lt ?_, card_K⟩)
    rwa [mk_prod, ← aleph0, lift_uzero, bK.mk_eq_rank'', mul_aleph0_eq aleph0_le]
  let := Module.compHom K (RingHom.op L.subtype)
  obtain ⟨⟨ιL, bL⟩⟩ := Module.Free.exists_basis (R := Lᵐᵒᵖ) (M := K)
  have card_ιL : ℵ₀ <= #ιL := by
    contrapose! hLK
    have := @Fintype.ofFinite _ (lt_aleph0_iff_finite.mp hLK)
    rw [bL.repr.toEquiv.cardinal_eq]; rw [mk_finsupp_of_fintype]; rw [← MulOpposite.opEquiv.cardinal_eq] at card_K ⊢
    apply power_nat_le
    contrapose! card_K
    exact (power_lt_aleph0 card_K natCast_lt_aleph0).le
  obtain ⟨e⟩ := lift_mk_le'.mp (card_ιL.trans_eq (lift_uzero #ιL).symm)
  have rep_e := bK.linearCombination_repr (bL ∘ e)
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum] at rep_e
  set c := bK.repr (bL ∘ e)
  set s := c.support
  let f i (j : s) : L := ⟨bK j i, Subfield.subset_closure ⟨(j, i), rfl⟩⟩
  have : ¬LinearIndependent Lᵐᵒᵖ f := fun h => by
    have := h.cardinal_lift_le_rank
    rw [lift_uzero]; rw [(LinearEquiv.piCongrRight fun _ => MulOpposite.opLinearEquiv Lᵐᵒᵖ).rank_eq]; rw [rank_fun'] at this
    exact natCast_lt_aleph0.not_ge this
  obtain ⟨t, g, eq0, i, hi, hgi⟩ := not_linearIndependent_iff.mp this
  refine hgi (linearIndependent_iff'.mp (bL.linearIndependent.comp e e.injective) t g ?_ i hi)
  clear_value c s
  simp_rw [← rep_e, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  replace eq0 := congr_arg L.subtype (congr_fun eq0 ⟨i, hi⟩)
  rw [Finset.sum_apply]; rw [map_sum] at eq0
  have : SMulCommClass Lᵐᵒᵖ K K := ⟨fun _ _ _ => mul_assoc _ _ _⟩
  simp_rw [smul_comm _ (c i), ← Finset.smul_sum]
  erw [eq0, smul_zero]

中文:
定理 max_aleph0_card_le_rank_fun_nat
  结论: 最大值 ℵ₀ #K <= 模.rank K (自然数 -> K)
  证明: by
  have aleph0_le : ℵ₀ <= Module.rank K (Nat -> K) := (rank_finsupp_self K Nat).symm.trans_le
    (Finsupp.lcoeFun.rank_le_of_injective <| by exact DFunLike.coe_injective)
  refine max_le aleph0_le ?_
  obtain card_K | card_K := le_or_gt #K ℵ₀
  · exact card_K.trans aleph0_le
  by_contra!
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := Nat -> K)
  let L := Subfield.closure (Set.range (fun i : ιK × Nat => bK i.1 i.2))
  have hLK : #L < #K := by
    refine (Subfield.cardinalMk_closure_le_max _).trans_lt
      (max_lt_iff.mpr ⟨mk_range_le.trans_lt ?_, card_K⟩)
    rwa [mk_prod, ← aleph0, lift_uzero, bK.mk_eq_rank'', mul_aleph0_eq aleph0_le]
  let := Module.compHom K (RingHom.op L.subtype)
  obtain ⟨⟨ιL, bL⟩⟩ := Module.Free.exists_basis (R := Lᵐᵒᵖ) (M := K)
  have card_ιL : ℵ₀ <= #ιL := by
    contrapose! hLK
    have := @Fintype.ofFinite _ (lt_aleph0_iff_finite.mp hLK)
    rw [bL.repr.toEquiv.cardinal_eq]; rw [mk_finsupp_of_fintype]; rw [← MulOpposite.opEquiv.cardinal_eq] at card_K ⊢
    apply power_nat_le
    contrapose! card_K
    exact (power_lt_aleph0 card_K natCast_lt_aleph0).le
  obtain ⟨e⟩ := lift_mk_le'.mp (card_ιL.trans_eq (lift_uzero #ιL).symm)
  have rep_e := bK.linearCombination_repr (bL ∘ e)
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum] at rep_e
  set c := bK.repr (bL ∘ e)
  set s := c.support
  let f i (j : s) : L := ⟨bK j i, Subfield.subset_closure ⟨(j, i), rfl⟩⟩
  have : ¬LinearIndependent Lᵐᵒᵖ f := fun h => by
    have := h.cardinal_lift_le_rank
    rw [lift_uzero]; rw [(LinearEquiv.piCongrRight fun _ => MulOpposite.opLinearEquiv Lᵐᵒᵖ).rank_eq]; rw [rank_fun'] at this
    exact natCast_lt_aleph0.not_ge this
  obtain ⟨t, g, eq0, i, hi, hgi⟩ := not_linearIndependent_iff.mp this
  refine hgi (linearIndependent_iff'.mp (bL.linearIndependent.comp e e.injective) t g ?_ i hi)
  clear_value c s
  simp_rw [← rep_e, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  replace eq0 := congr_arg L.subtype (congr_fun eq0 ⟨i, hi⟩)
  rw [Finset.sum_apply]; rw [map_sum] at eq0
  have : SMulCommClass Lᵐᵒᵖ K K := ⟨fun _ _ _ => mul_assoc _ _ _⟩
  simp_rw [smul_comm _ (c i), ← Finset.smul_sum]
  erw [eq0, smul_zero]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Finsupp, Finsupp.lcoeFun.rank_le_of_injective, Module, Module.Free.exists_basis, Module.rank, Set.range, Subfield, Subfield.cardinalMk_closure_le_max, Subfield.closure, aleph0_le, card_K, card_K.trans, cardinalMk_closure_le_max, closure, coe_injective, exists_basis, lcoeFun, le_or_gt
-/
theorem max_aleph0_card_le_rank_fun_nat : max ℵ₀ #K <= Module.rank K (Nat -> K) := by
  have aleph0_le : ℵ₀ <= Module.rank K (Nat -> K) := (rank_finsupp_self K Nat).symm.trans_le
    (Finsupp.lcoeFun.rank_le_of_injective <| by exact DFunLike.coe_injective)
  refine max_le aleph0_le ?_
  obtain card_K | card_K := le_or_gt #K ℵ₀
  · exact card_K.trans aleph0_le
  by_contra!
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := Nat -> K)
  let L := Subfield.closure (Set.range (fun i : ιK × Nat => bK i.1 i.2))
  have hLK : #L < #K := by
    refine (Subfield.cardinalMk_closure_le_max _).trans_lt
      (max_lt_iff.mpr ⟨mk_range_le.trans_lt ?_, card_K⟩)
    rwa [mk_prod, ← aleph0, lift_uzero, bK.mk_eq_rank'', mul_aleph0_eq aleph0_le]
  let := Module.compHom K (RingHom.op L.subtype)
  obtain ⟨⟨ιL, bL⟩⟩ := Module.Free.exists_basis (R := Lᵐᵒᵖ) (M := K)
  have card_ιL : ℵ₀ <= #ιL := by
    contrapose! hLK
    have := @Fintype.ofFinite _ (lt_aleph0_iff_finite.mp hLK)
    rw [bL.repr.toEquiv.cardinal_eq]; rw [mk_finsupp_of_fintype]; rw [← MulOpposite.opEquiv.cardinal_eq] at card_K ⊢
    apply power_nat_le
    contrapose! card_K
    exact (power_lt_aleph0 card_K natCast_lt_aleph0).le
  obtain ⟨e⟩ := lift_mk_le'.mp (card_ιL.trans_eq (lift_uzero #ιL).symm)
  have rep_e := bK.linearCombination_repr (bL ∘ e)
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum] at rep_e
  set c := bK.repr (bL ∘ e)
  set s := c.support
  let f i (j : s) : L := ⟨bK j i, Subfield.subset_closure ⟨(j, i), rfl⟩⟩
  have : ¬LinearIndependent Lᵐᵒᵖ f := fun h => by
    have := h.cardinal_lift_le_rank
    rw [lift_uzero]; rw [(LinearEquiv.piCongrRight fun _ => MulOpposite.opLinearEquiv Lᵐᵒᵖ).rank_eq]; rw [rank_fun'] at this
    exact natCast_lt_aleph0.not_ge this
  obtain ⟨t, g, eq0, i, hi, hgi⟩ := not_linearIndependent_iff.mp this
  refine hgi (linearIndependent_iff'.mp (bL.linearIndependent.comp e e.injective) t g ?_ i hi)
  clear_value c s
  simp_rw [← rep_e, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  replace eq0 := congr_arg L.subtype (congr_fun eq0 ⟨i, hi⟩)
  rw [Finset.sum_apply]; rw [map_sum] at eq0
  have : SMulCommClass Lᵐᵒᵖ K K := ⟨fun _ _ _ => mul_assoc _ _ _⟩
  simp_rw [smul_comm _ (c i), ← Finset.smul_sum]
  erw [eq0, smul_zero]

variable {K}

open Function in
/--
theorem `rank_fun_infinite` / 定理 `rank_fun_infinite`

English:
theorem rank_fun_infinite
  given: {ι : Type v} [hι : Infinite ι]
  statement: Module.rank K (ι -> K) = #(ι -> K)
  proof: by
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := ι -> K)
  obtain ⟨e⟩ := lift_mk_le'.mp ((aleph0_le_mk_iff.mpr hι).trans_eq (lift_uzero #ι).symm)
have := LinearMap.lift_rank_le_of_injective _
    LinearMap.funLeft_injective_of_surjective K K _ (invFun_surjective e.injective)
  rw [lift_umax.{u]; rw [v}]; rw [lift_id'.{u]; rw [v}] at this
  have key := (lift_le.{v}.mpr <| max_aleph0_card_le_rank_fun_nat K).trans this
  rw [lift_max]; rw [lift_aleph0]; rw [max_le_iff] at key
  have : Infinite ιK := by
    rw [← aleph0_le_mk_iff]; rw [bK.mk_eq_rank'']; exact key.1
  rw [bK.repr.toEquiv.cardinal_eq]; rw [mk_finsupp_lift_of_infinite]; rw [lift_umax.{u]; rw [v}]; rw [lift_id'.{u]; rw [v}]; rw [bK.mk_eq_rank'']; rw [eq_comm]; rw [max_eq_left]
  exact key.2

中文:
定理 rank_fun_infinite
  条件: {ι : 类型v} [hι : 无限 ι]
  结论: 模.rank K (ι -> K) = #(ι -> K)
  证明: by
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := ι -> K)
  obtain ⟨e⟩ := lift_mk_le'.mp ((aleph0_le_mk_iff.mpr hι).trans_eq (lift_uzero #ι).symm)
have := LinearMap.lift_rank_le_of_injective _
    LinearMap.funLeft_injective_of_surjective K K _ (invFun_surjective e.injective)
  rw [lift_umax.{u]; rw [v}]; rw [lift_id'.{u]; rw [v}] at this
  have key := (lift_le.{v}.mpr <| max_aleph0_card_le_rank_fun_nat K).trans this
  rw [lift_max]; rw [lift_aleph0]; rw [max_le_iff] at key
  have : Infinite ιK := by
    rw [← aleph0_le_mk_iff]; rw [bK.mk_eq_rank'']; exact key.1
  rw [bK.repr.toEquiv.cardinal_eq]; rw [mk_finsupp_lift_of_infinite]; rw [lift_umax.{u]; rw [v}]; rw [lift_id'.{u]; rw [v}]; rw [bK.mk_eq_rank'']; rw [eq_comm]; rw [max_eq_left]
  exact key.2

Depends on / 依赖: Infinite, LinearMap, LinearMap.funLeft_injective_of_surjective, LinearMap.lift_rank_le_of_injective, Module, Module.Free.exists_basis, aleph0_le_mk_iff, aleph0_le_mk_iff.mpr, e.injective, exists_basis, funLeft_injective_of_surjective, injective, invFun_surjective, lift_aleph0, lift_id, lift_le, lift_max, lift_mk_le, lift_rank_le_of_injective, lift_umax
-/
theorem rank_fun_infinite {ι : Type v} [hι : Infinite ι] : Module.rank K (ι -> K) = #(ι -> K) := by
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := ι -> K)
  obtain ⟨e⟩ := lift_mk_le'.mp ((aleph0_le_mk_iff.mpr hι).trans_eq (lift_uzero #ι).symm)
have := LinearMap.lift_rank_le_of_injective _
    LinearMap.funLeft_injective_of_surjective K K _ (invFun_surjective e.injective)
  rw [lift_umax.{u]; rw [v}]; rw [lift_id'.{u]; rw [v}] at this
  have key := (lift_le.{v}.mpr <| max_aleph0_card_le_rank_fun_nat K).trans this
  rw [lift_max]; rw [lift_aleph0]; rw [max_le_iff] at key
  have : Infinite ιK := by
    rw [← aleph0_le_mk_iff]; rw [bK.mk_eq_rank'']; exact key.1
  rw [bK.repr.toEquiv.cardinal_eq]; rw [mk_finsupp_lift_of_infinite]; rw [lift_umax.{u]; rw [v}]; rw [lift_id'.{u]; rw [v}]; rw [bK.mk_eq_rank'']; rw [eq_comm]; rw [max_eq_left]
  exact key.2

/--
theorem `rank_dual_eq_card_dual_of_aleph0_le_rank'` / 定理 `rank_dual_eq_card_dual_of_aleph0_le_rank'`

English:
theorem rank_dual_eq_card_dual_of_aleph0_le_rank'
  statement: {V : Type*} [AddCommGroup V] [Module K V]
  proof: by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'']; rw [aleph0_le_mk_iff] at h
  have e := (b.constr Kᵐᵒᵖ (M' := K)).symm.trans
    (LinearEquiv.piCongrRight fun _ => MulOpposite.opLinearEquiv Kᵐᵒᵖ)
  rw [e.rank_eq]; rw [e.toEquiv.cardinal_eq]
  apply rank_fun_infinite

中文:
定理 rank_dual_eq_card_dual_of_aleph0_le_rank'
  结论: {V : 类型} [加法交换群 V] [模 K V]
  证明: by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'']; rw [aleph0_le_mk_iff] at h
  have e := (b.constr Kᵐᵒᵖ (M' := K)).symm.trans
    (LinearEquiv.piCongrRight fun _ => MulOpposite.opLinearEquiv Kᵐᵒᵖ)
  rw [e.rank_eq]; rw [e.toEquiv.cardinal_eq]
  apply rank_fun_infinite

Depends on / 依赖: LinearEquiv, LinearEquiv.piCongrRight, Module, Module.Free.exists_basis, MulOpposite, MulOpposite.opLinearEquiv, aleph0_le_mk_iff, b.constr, b.mk_eq_rank, cardinal_eq, constr, e.rank_eq, e.toEquiv.cardinal_eq, exists_basis, mk_eq_rank, opLinearEquiv, piCongrRight, rank_eq, rank_fun_infinite, symm.trans
-/
theorem rank_dual_eq_card_dual_of_aleph0_le_rank' {V : Type*} [AddCommGroup V] [Module K V]
    (h : ℵ₀ <= Module.rank K V) : Module.rank Kᵐᵒᵖ (V ->ₗ[K] K) = #(V ->ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'']; rw [aleph0_le_mk_iff] at h
  have e := (b.constr Kᵐᵒᵖ (M' := K)).symm.trans
    (LinearEquiv.piCongrRight fun _ => MulOpposite.opLinearEquiv Kᵐᵒᵖ)
  rw [e.rank_eq]; rw [e.toEquiv.cardinal_eq]
  apply rank_fun_infinite

/--
theorem `rank_dual_eq_card_dual_of_aleph0_le_rank` / 定理 `rank_dual_eq_card_dual_of_aleph0_le_rank`

English:
theorem rank_dual_eq_card_dual_of_aleph0_le_rank
  statement: {K V} [Field K] [AddCommGroup V] [Module K V]
  proof: by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'']; rw [aleph0_le_mk_iff] at h
  have e := (b.constr K (M' := K)).symm
  rw [e.rank_eq]; rw [e.toEquiv.cardinal_eq]
  apply rank_fun_infinite

中文:
定理 rank_dual_eq_card_dual_of_aleph0_le_rank
  结论: {K V} [域 K] [加法交换群 V] [模 K V]
  证明: by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'']; rw [aleph0_le_mk_iff] at h
  have e := (b.constr K (M' := K)).symm
  rw [e.rank_eq]; rw [e.toEquiv.cardinal_eq]
  apply rank_fun_infinite

Depends on / 依赖: Module, Module.Free.exists_basis, aleph0_le_mk_iff, b.constr, b.mk_eq_rank, cardinal_eq, constr, e.rank_eq, e.toEquiv.cardinal_eq, exists_basis, mk_eq_rank, rank_eq, rank_fun_infinite, toEquiv
-/
theorem rank_dual_eq_card_dual_of_aleph0_le_rank {K V} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ <= Module.rank K V) : Module.rank K (V ->ₗ[K] K) = #(V ->ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'']; rw [aleph0_le_mk_iff] at h
  have e := (b.constr K (M' := K)).symm
  rw [e.rank_eq]; rw [e.toEquiv.cardinal_eq]
  apply rank_fun_infinite

/--
theorem `lift_rank_lt_rank_dual'` / 定理 `lift_rank_lt_rank_dual'`

English:
theorem lift_rank_lt_rank_dual'
  statement: {V : Type v} [AddCommGroup V] [Module K V]
  proof: by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'']; rw [rank_dual_eq_card_dual_of_aleph0_le_rank' h]; rw [← (b.constr Nat (M' := K)).toEquiv.cardinal_eq]; rw [mk_arrow]
  apply cantor'
  rw [one_lt_lift_iff]; rw [one_lt_iff_nontrivial]
  infer_instance

中文:
定理 lift_rank_lt_rank_dual'
  结论: {V : 类型v} [加法交换群 V] [模 K V]
  证明: by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'']; rw [rank_dual_eq_card_dual_of_aleph0_le_rank' h]; rw [← (b.constr Nat (M' := K)).toEquiv.cardinal_eq]; rw [mk_arrow]
  apply cantor'
  rw [one_lt_lift_iff]; rw [one_lt_iff_nontrivial]
  infer_instance

Depends on / 依赖: Module, Module.Free.exists_basis, b.constr, b.mk_eq_rank, cantor, cardinal_eq, constr, exists_basis, infer_instance, mk_arrow, mk_eq_rank, one_lt_iff_nontrivial, one_lt_lift_iff, rank_dual_eq_card_dual_of_aleph0_le_rank, toEquiv, toEquiv.cardinal_eq
-/
theorem lift_rank_lt_rank_dual' {V : Type v} [AddCommGroup V] [Module K V]
    (h : ℵ₀ <= Module.rank K V) :
    Cardinal.lift.{u} (Module.rank K V) < Module.rank Kᵐᵒᵖ (V ->ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'']; rw [rank_dual_eq_card_dual_of_aleph0_le_rank' h]; rw [← (b.constr Nat (M' := K)).toEquiv.cardinal_eq]; rw [mk_arrow]
  apply cantor'
  rw [one_lt_lift_iff]; rw [one_lt_iff_nontrivial]
  infer_instance

/--
theorem `lift_rank_lt_rank_dual` / 定理 `lift_rank_lt_rank_dual`

English:
theorem lift_rank_lt_rank_dual
  statement: {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  proof: by
  rw [rank_dual_eq_card_dual_of_aleph0_le_rank h]; rw [← rank_dual_eq_card_dual_of_aleph0_le_rank' h]
  exact lift_rank_lt_rank_dual' h

中文:
定理 lift_rank_lt_rank_dual
  结论: {K : 类型u} {V : 类型v} [域 K] [加法交换群 V] [模 K V]
  证明: by
  rw [rank_dual_eq_card_dual_of_aleph0_le_rank h]; rw [← rank_dual_eq_card_dual_of_aleph0_le_rank' h]
  exact lift_rank_lt_rank_dual' h

Depends on / 依赖: lift_rank_lt_rank_dual, rank_dual_eq_card_dual_of_aleph0_le_rank
-/
theorem lift_rank_lt_rank_dual {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ <= Module.rank K V) :
    Cardinal.lift.{u} (Module.rank K V) < Module.rank K (V ->ₗ[K] K) := by
  rw [rank_dual_eq_card_dual_of_aleph0_le_rank h]; rw [← rank_dual_eq_card_dual_of_aleph0_le_rank' h]
  exact lift_rank_lt_rank_dual' h

/--
theorem `rank_lt_rank_dual'` / 定理 `rank_lt_rank_dual'`

English:
theorem rank_lt_rank_dual'
  given: {V : Type u} [AddCommGroup V] [Module K V] (h : ℵ₀ <= Module.rank K V)
  proof: by
  convert! lift_rank_lt_rank_dual' h; rw [lift_id]

中文:
定理 rank_lt_rank_dual'
  条件: {V : 类型u} [加法交换群 V] [模 K V] (h : ℵ₀ <= 模.rank K V)
  证明: by
  convert! lift_rank_lt_rank_dual' h; rw [lift_id]

Depends on / 依赖: convert, lift_id, lift_rank_lt_rank_dual
-/
theorem rank_lt_rank_dual' {V : Type u} [AddCommGroup V] [Module K V] (h : ℵ₀ <= Module.rank K V) :
    Module.rank K V < Module.rank Kᵐᵒᵖ (V ->ₗ[K] K) := by
  convert! lift_rank_lt_rank_dual' h; rw [lift_id]

/--
theorem `rank_lt_rank_dual` / 定理 `rank_lt_rank_dual`

English:
theorem rank_lt_rank_dual
  statement: {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
  proof: by
  convert! lift_rank_lt_rank_dual h; rw [lift_id]

中文:
定理 rank_lt_rank_dual
  结论: {K V : 类型u} [域 K] [加法交换群 V] [模 K V]
  证明: by
  convert! lift_rank_lt_rank_dual h; rw [lift_id]

Depends on / 依赖: convert, lift_id, lift_rank_lt_rank_dual
-/
theorem rank_lt_rank_dual {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ <= Module.rank K V) : Module.rank K V < Module.rank K (V ->ₗ[K] K) := by
  convert! lift_rank_lt_rank_dual h; rw [lift_id]

end Cardinal
