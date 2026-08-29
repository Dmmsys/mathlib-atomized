/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# A module over a division ring is Noetherian if and only if it is finite.

-/

@[expose] public section


universe u v

open Cardinal Submodule Module Function

namespace IsNoetherian

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

/--
theorem `iff_rank_lt_aleph0` / 定理 `iff_rank_lt_aleph0`

English:
theorem iff_rank_lt_aleph0
  statement: IsNoetherian K V ↔ Module.rank K V < ℵ₀
  proof: by
  let b := Basis.ofVectorSpace K V
  rw [← b.mk_eq_rank'']; rw [lt_aleph0_iff_set_finite]
  constructor
  · intro
    exact (Basis.ofVectorSpaceIndex.linearIndependent K V).set_finite_of_isNoetherian
  · intro hbfinite
    refine
      @isNoetherian_of_linearEquiv K K (⊤ : Submodule K V) V _ _ _ _ _ _ (RingHom.id K) _ _ _
        (LinearEquiv.ofTop _ rfl) (id ?_)
    refine isNoetherian_of_fg_of_noetherian _ ⟨Set.Finite.toFinset hbfinite, ?_⟩
    rw [Set.Finite.coe_toFinset]; rw [← b.span_eq]; rw [Basis.coe_ofVectorSpace]; rw [Subtype.range_coe]

中文:
定理 iff_rank_lt_aleph0
  结论: 是Noether K V ↔ 模.rank K V < ℵ₀
  证明: by
  let b := Basis.ofVectorSpace K V
  rw [← b.mk_eq_rank'']; rw [lt_aleph0_iff_set_finite]
  constructor
  · intro
    exact (Basis.ofVectorSpaceIndex.linearIndependent K V).set_finite_of_isNoetherian
  · intro hbfinite
    refine
      @isNoetherian_of_linearEquiv K K (⊤ : Submodule K V) V _ _ _ _ _ _ (RingHom.id K) _ _ _
        (LinearEquiv.ofTop _ rfl) (id ?_)
    refine isNoetherian_of_fg_of_noetherian _ ⟨Set.Finite.toFinset hbfinite, ?_⟩
    rw [Set.Finite.coe_toFinset]; rw [← b.span_eq]; rw [Basis.coe_ofVectorSpace]; rw [Subtype.range_coe]

Depends on / 依赖: Basis.coe_ofVectorSpace, Basis.ofVectorSpace, Basis.ofVectorSpaceIndex.linearIndependent, Finite, LinearEquiv, LinearEquiv.ofTop, RingHom, RingHom.id, Set.Finite.coe_toFinset, Set.Finite.toFinset, Submodule, b.mk_eq_rank, b.span_eq, coe_ofVectorSpace, coe_toFinset, hbfinite, isNoetherian_of_fg_of_noetherian, isNoetherian_of_linearEquiv, linearIndependent, lt_aleph0_iff_set_finite
-/
theorem iff_rank_lt_aleph0 : IsNoetherian K V ↔ Module.rank K V < ℵ₀ := by
  let b := Basis.ofVectorSpace K V
  rw [← b.mk_eq_rank'']; rw [lt_aleph0_iff_set_finite]
  constructor
  · intro
    exact (Basis.ofVectorSpaceIndex.linearIndependent K V).set_finite_of_isNoetherian
  · intro hbfinite
    refine
      @isNoetherian_of_linearEquiv K K (⊤ : Submodule K V) V _ _ _ _ _ _ (RingHom.id K) _ _ _
        (LinearEquiv.ofTop _ rfl) (id ?_)
    refine isNoetherian_of_fg_of_noetherian _ ⟨Set.Finite.toFinset hbfinite, ?_⟩
    rw [Set.Finite.coe_toFinset]; rw [← b.span_eq]; rw [Basis.coe_ofVectorSpace]; rw [Subtype.range_coe]

/-- In a Noetherian module over a division ring, all bases are indexed by a finite type. -/
@[instance_reducible]
/--
Definition of `fintypeBasisIndex` / `fintypeBasisIndex` 的定义

English:
definition fintypeBasisIndex
  signature: {ι : Type*} [IsNoetherian K V] (b : Basis ι K V)
  body: b.fintypeIndexOfRankLtAleph0 (rank_lt_aleph0 K V)

中文:
定义 fintypeBasisIndex
  签名: {ι : 类型} [是Noether K V] (b : 基 ι K V)
  定义体: b.fintypeIndexOfRankLtAleph0 (rank_lt_aleph0 K V)

Depends on / 依赖: b.fintypeIndexOfRankLtAleph0, fintypeIndexOfRankLtAleph0, rank_lt_aleph0
-/
noncomputable def fintypeBasisIndex {ι : Type*} [IsNoetherian K V] (b : Basis ι K V) : Fintype ι :=
  b.fintypeIndexOfRankLtAleph0 (rank_lt_aleph0 K V)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNoetherian
  signature: K V] : Fintype (Basis.ofVectorSpaceIndex K V)
  body: fintypeBasisIndex (Basis.ofVectorSpace K V)

中文:
实例 [是Noether
  签名: K V] : 有限类型 (基.ofVectorSpaceIndex K V)
  定义体: fintypeBasisIndex (Basis.ofVectorSpace K V)

Depends on / 依赖: Basis.ofVectorSpace, fintypeBasisIndex, ofVectorSpace
-/
noncomputable instance [IsNoetherian K V] : Fintype (Basis.ofVectorSpaceIndex K V) :=
  fintypeBasisIndex (Basis.ofVectorSpace K V)

/--
theorem `finite_basis_index` / 定理 `finite_basis_index`

English:
theorem finite_basis_index
  given: {ι : Type*} {s : Set ι} [IsNoetherian K V] (b : Basis s K V)
  proof: b.finite_index_of_rank_lt_aleph0 (rank_lt_aleph0 K V)

中文:
定理 finite_basis_index
  条件: {ι : 类型} {s : 集合 ι} [是Noether K V] (b : 基 s K V)
  证明: b.finite_index_of_rank_lt_aleph0 (rank_lt_aleph0 K V)

Depends on / 依赖: b.finite_index_of_rank_lt_aleph0, finite_index_of_rank_lt_aleph0, rank_lt_aleph0
-/
theorem finite_basis_index {ι : Type*} {s : Set ι} [IsNoetherian K V] (b : Basis s K V) :
    s.Finite :=
  b.finite_index_of_rank_lt_aleph0 (rank_lt_aleph0 K V)

variable (K V)

/--
Definition of `finsetBasisIndex` / `finsetBasisIndex` 的定义

English:
definition finsetBasisIndex
  signature: [IsNoetherian K V]
  body: (finite_basis_index (Basis.ofVectorSpace K V)).toFinset

@[simp]

中文:
定义 finsetBasisIndex
  签名: [是Noether K V]
  定义体: (finite_basis_index (Basis.ofVectorSpace K V)).toFinset

@[simp]

Depends on / 依赖: Basis.ofVectorSpace, finite_basis_index, ofVectorSpace, toFinset
-/
noncomputable def finsetBasisIndex [IsNoetherian K V] : Finset V :=
  (finite_basis_index (Basis.ofVectorSpace K V)).toFinset

@[simp]
/--
theorem `coe_finsetBasisIndex` / 定理 `coe_finsetBasisIndex`

English:
theorem coe_finsetBasisIndex
  given: [IsNoetherian K V]
  proof: Set.Finite.coe_toFinset _

@[simp]

中文:
定理 coe_finsetBasisIndex
  条件: [是Noether K V]
  证明: Set.Finite.coe_toFinset _

@[simp]

Depends on / 依赖: Finite, Set.Finite.coe_toFinset, coe_toFinset
-/
theorem coe_finsetBasisIndex [IsNoetherian K V] :
    (↑(finsetBasisIndex K V) : Set V) = Basis.ofVectorSpaceIndex K V :=
  Set.Finite.coe_toFinset _

@[simp]
/--
theorem `coeSort_finsetBasisIndex` / 定理 `coeSort_finsetBasisIndex`

English:
theorem coeSort_finsetBasisIndex
  given: [IsNoetherian K V]
  proof: Set.Finite.coeSort_toFinset _

中文:
定理 coeSort_finsetBasisIndex
  条件: [是Noether K V]
  证明: Set.Finite.coeSort_toFinset _

Depends on / 依赖: Finite, Set.Finite.coeSort_toFinset, coeSort_toFinset
-/
theorem coeSort_finsetBasisIndex [IsNoetherian K V] :
    (finsetBasisIndex K V : Type _) = Basis.ofVectorSpaceIndex K V :=
  Set.Finite.coeSort_toFinset _

/--
Definition of `finsetBasis` / `finsetBasis` 的定义

English:
definition finsetBasis
  signature: [IsNoetherian K V]
  body: (Basis.ofVectorSpace K V).reindex (by rw [coeSort_finsetBasisIndex])

@[simp]

中文:
定义 finsetBasis
  签名: [是Noether K V]
  定义体: (Basis.ofVectorSpace K V).reindex (by rw [coeSort_finsetBasisIndex])

@[simp]

Depends on / 依赖: Basis.ofVectorSpace, coeSort_finsetBasisIndex, ofVectorSpace, reindex
-/
noncomputable def finsetBasis [IsNoetherian K V] : Basis (finsetBasisIndex K V) K V :=
  (Basis.ofVectorSpace K V).reindex (by rw [coeSort_finsetBasisIndex])

@[simp]
/--
theorem `range_finsetBasis` / 定理 `range_finsetBasis`

English:
theorem range_finsetBasis
  given: [IsNoetherian K V]
  proof: by
  rw [finsetBasis]; rw [Basis.range_reindex]; rw [Basis.range_ofVectorSpace]

中文:
定理 range_finsetBasis
  条件: [是Noether K V]
  证明: by
  rw [finsetBasis]; rw [Basis.range_reindex]; rw [Basis.range_ofVectorSpace]

Depends on / 依赖: Basis.range_ofVectorSpace, Basis.range_reindex, finsetBasis, range_ofVectorSpace, range_reindex
-/
theorem range_finsetBasis [IsNoetherian K V] :
    Set.range (finsetBasis K V) = Basis.ofVectorSpaceIndex K V := by
  rw [finsetBasis]; rw [Basis.range_reindex]; rw [Basis.range_ofVectorSpace]

variable {K V}

/--
theorem `_root_.Module.card_eq_pow_finrank` / 定理 `_root_.Module.card_eq_pow_finrank`

English:
theorem _root_.Module.card_eq_pow_finrank
  given: [Fintype K] [Fintype V]
  proof: by
  let b := IsNoetherian.finsetBasis K V
  rw [Module.card_fintype b]; rw [← Module.finrank_eq_card_basis b]

中文:
定理 _root_.模.card_eq_pow_finrank
  条件: [有限类型 K] [有限类型 V]
  证明: by
  let b := IsNoetherian.finsetBasis K V
  rw [Module.card_fintype b]; rw [← Module.finrank_eq_card_basis b]

Depends on / 依赖: IsNoetherian, IsNoetherian.finsetBasis, Module, Module.card_fintype, Module.finrank_eq_card_basis, card_fintype, finrank_eq_card_basis, finsetBasis
-/
theorem _root_.Module.card_eq_pow_finrank [Fintype K] [Fintype V] :
    Fintype.card V = Fintype.card K ^ Module.finrank K V := by
  let b := IsNoetherian.finsetBasis K V
  rw [Module.card_fintype b]; rw [← Module.finrank_eq_card_basis b]

/--
theorem `_root_.Module.natCard_eq_pow_finrank` / 定理 `_root_.Module.natCard_eq_pow_finrank`

English:
theorem _root_.Module.natCard_eq_pow_finrank
  given: [Module.Finite K V]
  proof: by
  let b := IsNoetherian.finsetBasis K V
  rw [Nat.card_congr b.equivFun.toEquiv]; rw [Nat.card_fun]; rw [finrank_eq_nat_card_basis b]

中文:
定理 _root_.模.natCard_eq_pow_finrank
  条件: [模.有限 K V]
  证明: by
  let b := IsNoetherian.finsetBasis K V
  rw [Nat.card_congr b.equivFun.toEquiv]; rw [Nat.card_fun]; rw [finrank_eq_nat_card_basis b]

Depends on / 依赖: IsNoetherian, IsNoetherian.finsetBasis, Nat.card_congr, Nat.card_fun, b.equivFun.toEquiv, card_congr, card_fun, equivFun, finrank_eq_nat_card_basis, finsetBasis, toEquiv
-/
theorem _root_.Module.natCard_eq_pow_finrank [Module.Finite K V] :
    Nat.card V = Nat.card K ^ finrank K V := by
  let b := IsNoetherian.finsetBasis K V
  rw [Nat.card_congr b.equivFun.toEquiv]; rw [Nat.card_fun]; rw [finrank_eq_nat_card_basis b]

/--
theorem `iff_fg` / 定理 `iff_fg`

English:
theorem iff_fg
  statement: IsNoetherian K V ↔ Module.Finite K V
  proof: ⟨fun _ => IsNoetherian.finite _ _, fun _ => isNoetherian_of_isNoetherianRing_of_finite _ _⟩

中文:
定理 iff_fg
  结论: 是Noether K V ↔ 模.有限 K V
  证明: ⟨fun _ => IsNoetherian.finite _ _, fun _ => isNoetherian_of_isNoetherianRing_of_finite _ _⟩

Depends on / 依赖: IsNoetherian, IsNoetherian.finite, finite, isNoetherian_of_isNoetherianRing_of_finite
-/
theorem iff_fg : IsNoetherian K V ↔ Module.Finite K V :=
  ⟨fun _ => IsNoetherian.finite _ _, fun _ => isNoetherian_of_isNoetherianRing_of_finite _ _⟩

end IsNoetherian
