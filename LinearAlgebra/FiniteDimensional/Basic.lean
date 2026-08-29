/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Finite-dimensional vector spaces

Basic properties of finite-dimensional vector spaces, of their dimensions, and
of linear maps on such spaces.

## Main definitions

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules (`FiniteDimensional.finiteDimensional_submodule`)
- quotients (for the dimension of a quotient, see `Submodule.finrank_quotient_add_finrank` in
  `Mathlib/LinearAlgebra/Dimension/RankNullity.lean`)
- linear equivs, in `LinearEquiv.finiteDimensional`

Basic properties of linear maps of a finite-dimensional vector space are given. Notably, the
equivalence of injectivity and surjectivity is proved in `LinearMap.injective_iff_surjective`,
and the equivalence between left-inverse and right-inverse in `LinearMap.mul_eq_one_comm`
and `LinearMap.comp_eq_id_comm`.

## Implementation notes

You should not assume that there has been any effort to state lemmas as generally as possible.

Plenty of the results hold for general finitely generated modules (see
`Mathlib/RingTheory/Finiteness/Basic.lean`) or Noetherian modules (see
`Mathlib/RingTheory/Noetherian/Basic.lean`).
-/

@[expose] public section

universe u v v' w

open Cardinal Function IsNoetherian Module Submodule

variable {K : Type u} {V : Type v}

namespace FiniteDimensional
section DivisionRing
variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/--
theorem `finrank_le_iff_rank_le` / 定理 `finrank_le_iff_rank_le`

English:
theorem finrank_le_iff_rank_le
  given: [FiniteDimensional K V] {n : Nat}
  proof: by
  simp [← Cardinal.toNat_le_iff_le_of_lt_aleph0 (rank_lt_aleph0 K V), finrank]

中文:
定理 finrank_le_iff_rank_le
  条件: [有限维 K V] {n : 自然数}
  证明: by
  simp [← Cardinal.toNat_le_iff_le_of_lt_aleph0 (rank_lt_aleph0 K V), finrank]

Depends on / 依赖: Cardinal, Cardinal.toNat_le_iff_le_of_lt_aleph0, finrank, rank_lt_aleph0, toNat_le_iff_le_of_lt_aleph0
-/
theorem finrank_le_iff_rank_le [FiniteDimensional K V] {n : Nat} :
    finrank K V <= n ↔ Module.rank K V <= n := by
  simp [← Cardinal.toNat_le_iff_le_of_lt_aleph0 (rank_lt_aleph0 K V), finrank]

/--
theorem `finrank_lt_iff_rank_lt` / 定理 `finrank_lt_iff_rank_lt`

English:
theorem finrank_lt_iff_rank_lt
  given: [FiniteDimensional K V] {n : Nat}
  proof: by
  simp [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0 (rank_lt_aleph0 K V), finrank]

中文:
定理 finrank_lt_iff_rank_lt
  条件: [有限维 K V] {n : 自然数}
  证明: by
  simp [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0 (rank_lt_aleph0 K V), finrank]

Depends on / 依赖: Cardinal, Cardinal.toNat_lt_iff_lt_of_lt_aleph0, finrank, rank_lt_aleph0, toNat_lt_iff_lt_of_lt_aleph0
-/
theorem finrank_lt_iff_rank_lt [FiniteDimensional K V] {n : Nat} :
    finrank K V < n ↔ Module.rank K V < n := by
  simp [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0 (rank_lt_aleph0 K V), finrank]

/--
theorem `_root_.LinearIndependent.lt_aleph0_of_finiteDimensional` / 定理 `_root_.LinearIndependent.lt_aleph0_of_finiteDimensional`

English:
theorem _root_.LinearIndependent.lt_aleph0_of_finiteDimensional
  statement: {ι : Type w} [FiniteDimensional K V]
  proof: h.lt_aleph0_of_finite

中文:
定理 _root_.LinearIndependent.lt_aleph0_of_finiteDimensional
  结论: {ι : 类型 w} [有限维 K V]
  证明: h.lt_aleph0_of_finite

Depends on / 依赖: h.lt_aleph0_of_finite, lt_aleph0_of_finite
-/
theorem _root_.LinearIndependent.lt_aleph0_of_finiteDimensional {ι : Type w} [FiniteDimensional K V]
    {v : ι -> V} (h : LinearIndependent K v) : #ι < ℵ₀ :=
  h.lt_aleph0_of_finite

/--
theorem `_root_.Submodule.eq_top_of_finrank_eq` / 定理 `_root_.Submodule.eq_top_of_finrank_eq`

English:
theorem _root_.Submodule.eq_top_of_finrank_eq
  statement: [FiniteDimensional K V] {S : Submodule K V}
  proof: by
  set bS := Basis.ofVectorSpace K S with bS_eq
  have : LinearIndepOn K id (Subtype.val '' Basis.ofVectorSpaceIndex K S) := by
    simpa [bS] using bS.linearIndependent.linearIndepOn_id.image
      (f := Submodule.subtype S) (by simp)
  set b := Basis.extend this with b_eq
  let i2 : Fintype (((↑

中文:
定理 _root_.子模.eq_top_of_finrank_eq
  结论: [有限维 K V] {S : 子模 K V}
  证明: by
  set bS := Basis.ofVectorSpace K S with bS_eq
  have : LinearIndepOn K id (Subtype.val '' Basis.ofVectorSpaceIndex K S) := by
    simpa [bS] using bS.linearIndependent.linearIndepOn_id.image
      (f := Submodule.subtype S) (by simp)
  set b := Basis.extend this with b_eq
  let i2 : Fintype (((↑

Depends on / 依赖: Basis.extend, Basis.ofVectorSpace, Basis.ofVectorSpaceIndex, Fintype, LinearIndepOn, LinearIndependent, LinearIndependent.set_finite_of_isNoetherian, Set.eq_of_subset_of_card_le, Set.subset_univ, Submodule, Submodule.subtype, Subtype, Subtype.val, bS.linearIndependent.linearIndepOn_id.image, bS_eq, b_eq, eq_of_subset_of_card_le, extend, fintype, linearIndepOn_id
-/
theorem _root_.Submodule.eq_top_of_finrank_eq [FiniteDimensional K V] {S : Submodule K V}
    (h : finrank K S = finrank K V) : S = ⊤ := by
  set bS := Basis.ofVectorSpace K S with bS_eq
  have : LinearIndepOn K id (Subtype.val '' Basis.ofVectorSpaceIndex K S) := by
    simpa [bS] using bS.linearIndependent.linearIndepOn_id.image
      (f := Submodule.subtype S) (by simp)
  set b := Basis.extend this with b_eq
  let i2 : Fintype (((↑) : S -> V) '' Basis.ofVectorSpaceIndex K S) :=
    (LinearIndependent.set_finite_of_isNoetherian this).fintype
  have : (↑) '' Basis.ofVectorSpaceIndex K S = this.extend (Set.subset_univ _) :=
    Set.eq_of_subset_of_card_le (this.subset_extend _)
      (by
        rw [Set.card_image_of_injective _ Subtype.coe_injective]; rw [← finrank_eq_card_basis bS]; rw [←
            finrank_eq_card_basis b]; rw [h])
  rw [← b.span_eq]; rw [b_eq]; rw [Basis.coe_extend]; rw [Subtype.range_coe]; rw [← this]; rw [← Submodule.coe_subtype]; rw [span_image]
  have := bS.span_eq
  rw [bS_eq]; rw [Basis.coe_ofVectorSpace]; rw [Subtype.range_coe] at this
  rw [this]; rw [Submodule.map_top (Submodule.subtype S)]; rw [range_subtype]

/--
theorem `_root_.Submodule.exists_linearEquiv_restrict_eq` / 定理 `_root_.Submodule.exists_linearEquiv_restrict_eq`

English:
theorem _root_.Submodule.exists_linearEquiv_restrict_eq
  proof: by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
  let eQ := W.prodEquivOfIsCompl Q hQ
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl W'
  let eQ' := W'.prodEquivOfIsCompl Q' hQ'
  suffices Nonempty (Q ≃ₗ[K] Q') from
    ⟨eQ.symm ≪≫ₗ (LinearEquiv.prodCongr f this.some) ≪≫ₗ eQ', by aesop⟩
  refine M

中文:
定理 _root_.子模.存在_linearEquiv_restrict_eq
  证明: by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
  let eQ := W.prodEquivOfIsCompl Q hQ
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl W'
  let eQ' := W'.prodEquivOfIsCompl Q' hQ'
  suffices Nonempty (Q ≃ₗ[K] Q') from
    ⟨eQ.symm ≪≫ₗ (LinearEquiv.prodCongr f this.some) ≪≫ₗ eQ', by aesop⟩
  refine M

Depends on / 依赖: Cardinal, Cardinal.add_right_inj_of_lt_aleph0, LinearEquiv, LinearEquiv.prodCongr, Module, Module.nonempty_linearEquiv_iff_rank_eq.mp, Module.nonempty_linearEquiv_iff_rank_eq.mpr, Module.rank, Nonempty, Submodule, Submodule.exists_isCompl, W.prodEquivOfIsCompl, add_comm, add_right_inj_of_lt_aleph0, eQ.symm, exists_isCompl, nonempty_linearEquiv_iff_rank_eq, prodCongr, prodEquivOfIsCompl, rank_prod
-/
theorem _root_.Submodule.exists_linearEquiv_restrict_eq
    {W W' : Submodule K V} [FiniteDimensional K W] (f : W ≃ₗ[K] W') :
    exists g : V ≃ₗ[K] V, forall x : W, f x = g x := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
  let eQ := W.prodEquivOfIsCompl Q hQ
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl W'
  let eQ' := W'.prodEquivOfIsCompl Q' hQ'
  suffices Nonempty (Q ≃ₗ[K] Q') from
    ⟨eQ.symm ≪≫ₗ (LinearEquiv.prodCongr f this.some) ≪≫ₗ eQ', by aesop⟩
  refine Module.nonempty_linearEquiv_iff_rank_eq.mpr ?_
  rw [← Cardinal.add_right_inj_of_lt_aleph0 (γ := Module.rank K W)]; rw [add_comm]; rw [← rank_prod']; rw [Module.nonempty_linearEquiv_iff_rank_eq.mp ⟨eQ⟩]; rw [add_comm]; rw [Module.nonempty_linearEquiv_iff_rank_eq.mp ⟨f⟩]; rw [← rank_prod']; rw [Module.nonempty_linearEquiv_iff_rank_eq.mp ⟨eQ'⟩]
  exact Module.rank_lt_aleph0 K ↥W

section

open Finset

variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
variable {W : Type v} [AddCommGroup W] [Module L W]

/--
theorem `exists_relation_sum_zero_pos_coefficient_of_finrank_succ_lt_card` / 定理 `exists_relation_sum_zero_pos_coefficient_of_finrank_succ_lt_card`

English:
theorem exists_relation_sum_zero_pos_coefficient_of_finrank_succ_lt_card
  statement: [FiniteDimensional L W]
  proof: by
  obtain ⟨f, sum, total, nonzero⟩ :=
    Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card h
  exact ⟨f, sum, total, exists_pos_of_sum_zero_of_exists_nonzero f total nonzero⟩

中文:
定理 存在_relation_sum_zero_pos_coefficient_of_finrank_succ_lt_card
  结论: [有限维 L W]
  证明: by
  obtain ⟨f, sum, total, nonzero⟩ :=
    Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card h
  exact ⟨f, sum, total, exists_pos_of_sum_zero_of_exists_nonzero f total nonzero⟩

Depends on / 依赖: Module, Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card, exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card, exists_pos_of_sum_zero_of_exists_nonzero, nonzero
-/
theorem exists_relation_sum_zero_pos_coefficient_of_finrank_succ_lt_card [FiniteDimensional L W]
    {t : Finset W} (h : finrank L W + 1 < t.card) :
    exists f : W -> L, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ exists x in t, 0 < f x := by
  obtain ⟨f, sum, total, nonzero⟩ :=
    Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card h
  exact ⟨f, sum, total, exists_pos_of_sum_zero_of_exists_nonzero f total nonzero⟩


end

set_option backward.isDefEq.respectTransparency false in
/-- In a vector space with dimension 1, each set `{v}` is a basis for `v ≠ 0`. -/
@[simps repr_apply]
/--
Definition of `basisSingleton` / `basisSingleton` 的定义

English:
definition basisSingleton
  signature: (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V)
  body: let b := Module.basisUnique ι h
  have h : b.repr v default != 0 := mt Module.basisUnique_repr_eq_zero_iff.mp hv
  Basis.ofRepr
    { toFun := fun w => Finsupp.single default (b.repr w default / b.repr v default)
      invFun := fun f => f default • v
      map_add' := by simp [add_div]
      map_sm

中文:
定义 basisSingleton
  签名: (ι : 类型) [唯一 ι] (h : finrank K V = 1) (v : V)
  定义体: let b := Module.basisUnique ι h
  have h : b.repr v default != 0 := mt Module.basisUnique_repr_eq_zero_iff.mp hv
  Basis.ofRepr
    { toFun := fun w => Finsupp.single default (b.repr w default / b.repr v default)
      invFun := fun f => f default • v
      map_add' := by simp [add_div]
      map_sm

Depends on / 依赖: Basis.ofRepr, Finsupp, Finsupp.coe_smul, Finsupp.single, Finsupp.single_eq_same, Finsupp.uniqueEquiv, Module, Module.basisUnique, Module.basisUnique_repr_eq_zero_iff.mp, Pi.smul_apply, add_div, apply_fun, b.repr, b.repr.toEquiv.injective, basisUnique, basisUnique_repr_eq_zero_iff, coe_smul, injective, invFun, left_inv
-/
noncomputable def basisSingleton (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V)
    (hv : v != 0) : Basis ι K V :=
  let b := Module.basisUnique ι h
  have h : b.repr v default != 0 := mt Module.basisUnique_repr_eq_zero_iff.mp hv
  Basis.ofRepr
    { toFun := fun w => Finsupp.single default (b.repr w default / b.repr v default)
      invFun := fun f => f default • v
      map_add' := by simp [add_div]
      map_smul' := by simp [mul_div]
      left_inv := fun w => by
        apply_fun b.repr using b.repr.toEquiv.injective
        apply_fun Finsupp.uniqueEquiv default
        simp only [map_smulₛₗ, Finsupp.coe_smul, Finsupp.single_eq_same,
          smul_eq_mul, Pi.smul_apply, Finsupp.uniqueEquiv_apply]
        exact div_mul_cancel₀ _ h
      right_inv := fun f => by
        ext
        simp only [map_smulₛₗ, Finsupp.coe_smul, Finsupp.single_eq_same,
          RingHom.id_apply, smul_eq_mul, Pi.smul_apply]
        exact mul_div_cancel_right₀ _ h }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `basisSingleton_apply` / 定理 `basisSingleton_apply`

English:
theorem basisSingleton_apply
  statement: (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v != 0)
  proof: by
  cases Unique.uniq ‹Unique ι› i
  simp [basisSingleton]

@[simp]

中文:
定理 basisSingleton_apply
  结论: (ι : 类型) [唯一 ι] (h : finrank K V = 1) (v : V) (hv : v != 0)
  证明: by
  cases Unique.uniq ‹Unique ι› i
  simp [basisSingleton]

@[simp]

Depends on / 依赖: Unique, Unique.uniq, basisSingleton
-/
theorem basisSingleton_apply (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v != 0)
    (i : ι) : basisSingleton ι h v hv i = v := by
  cases Unique.uniq ‹Unique ι› i
  simp [basisSingleton]

@[simp]
/--
theorem `range_basisSingleton` / 定理 `range_basisSingleton`

English:
theorem range_basisSingleton
  given: (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v != 0)
  proof: by rw [Set.range_unique, basisSingleton_apply]

中文:
定理 range_basisSingleton
  条件: (ι : 类型) [唯一 ι] (h : finrank K V = 1) (v : V) (hv : v != 0)
  证明: by rw [Set.range_unique, basisSingleton_apply]

Depends on / 依赖: Set.range_unique, basisSingleton_apply, range_unique
-/
theorem range_basisSingleton (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v != 0) :
    Set.range (basisSingleton ι h v hv) = {v} := by rw [Set.range_unique, basisSingleton_apply]

end DivisionRing

end FiniteDimensional

section ZeroRank

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/--
theorem `FiniteDimensional.of_rank_eq_nat` / 定理 `FiniteDimensional.of_rank_eq_nat`

English:
theorem FiniteDimensional.of_rank_eq_nat
  given: {n : Nat} (h : Module.rank K V = n)
  proof: Module.finite_of_rank_eq_nat h

中文:
定理 有限维.of_rank_eq_nat
  条件: {n : 自然数} (h : 模.rank K V = n)
  证明: Module.finite_of_rank_eq_nat h

Depends on / 依赖: Module, Module.finite_of_rank_eq_nat, finite_of_rank_eq_nat
-/
theorem FiniteDimensional.of_rank_eq_nat {n : Nat} (h : Module.rank K V = n) :
    FiniteDimensional K V :=
  Module.finite_of_rank_eq_nat h

/--
theorem `FiniteDimensional.of_rank_eq_zero` / 定理 `FiniteDimensional.of_rank_eq_zero`

English:
theorem FiniteDimensional.of_rank_eq_zero
  given: (h : Module.rank K V = 0)
  statement: FiniteDimensional K V
  proof: Module.finite_of_rank_eq_zero h

中文:
定理 有限维.of_rank_eq_zero
  条件: (h : 模.rank K V = 0)
  结论: 有限维 K V
  证明: Module.finite_of_rank_eq_zero h

Depends on / 依赖: Module, Module.finite_of_rank_eq_zero, finite_of_rank_eq_zero
-/
theorem FiniteDimensional.of_rank_eq_zero (h : Module.rank K V = 0) : FiniteDimensional K V :=
  Module.finite_of_rank_eq_zero h

/--
theorem `FiniteDimensional.of_rank_eq_one` / 定理 `FiniteDimensional.of_rank_eq_one`

English:
theorem FiniteDimensional.of_rank_eq_one
  given: (h : Module.rank K V = 1)
  statement: FiniteDimensional K V
  proof: Module.finite_of_rank_eq_one h

中文:
定理 有限维.of_rank_eq_one
  条件: (h : 模.rank K V = 1)
  结论: 有限维 K V
  证明: Module.finite_of_rank_eq_one h

Depends on / 依赖: Module, Module.finite_of_rank_eq_one, finite_of_rank_eq_one
-/
theorem FiniteDimensional.of_rank_eq_one (h : Module.rank K V = 1) : FiniteDimensional K V :=
  Module.finite_of_rank_eq_one h

variable (K V)

/--
Instance `finiteDimensional_bot` / 实例 `finiteDimensional_bot`

English:
instance finiteDimensional_bot
  signature: : FiniteDimensional K (⊥ : Submodule K V)
  body: .of_rank_eq_zero by simp

中文:
实例 finiteDimensional_bot
  签名: : 有限维 K (⊥ : 子模 K V)
  定义体: .of_rank_eq_zero by simp

Depends on / 依赖: of_rank_eq_zero
-/
instance finiteDimensional_bot : FiniteDimensional K (⊥ : Submodule K V) :=
.of_rank_eq_zero by simp

end ZeroRank

namespace Submodule

open IsNoetherian Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/--
theorem `finiteDimensional_of_le` / 定理 `finiteDimensional_of_le`

English:
theorem finiteDimensional_of_le
  given: {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (h : S₁ <= S₂)
  proof: (isNoetherian_of_le h).finite

中文:
定理 finiteDimensional_of_le
  条件: {S₁ S₂ : 子模 K V} [有限维 K S₂] (h : S₁ <= S₂)
  证明: (isNoetherian_of_le h).finite

Depends on / 依赖: finite, isNoetherian_of_le
-/
theorem finiteDimensional_of_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (h : S₁ <= S₂) :
    FiniteDimensional K S₁ :=
  (isNoetherian_of_le h).finite

/--
Instance `finiteDimensional_inf_left` / 实例 `finiteDimensional_inf_left`

English:
instance finiteDimensional_inf_left
  signature: (S₁ S₂ : Submodule K V) [FiniteDimensional K S₁]
  body: finiteDimensional_of_le inf_le_left

中文:
实例 finiteDimensional_inf_left
  签名: (S₁ S₂ : 子模 K V) [有限维 K S₁]
  定义体: finiteDimensional_of_le inf_le_left

Depends on / 依赖: finiteDimensional_of_le, inf_le_left
-/
instance finiteDimensional_inf_left (S₁ S₂ : Submodule K V) [FiniteDimensional K S₁] :
    FiniteDimensional K (S₁ ⊓ S₂ : Submodule K V) :=
  finiteDimensional_of_le inf_le_left

/--
Instance `finiteDimensional_inf_right` / 实例 `finiteDimensional_inf_right`

English:
instance finiteDimensional_inf_right
  signature: (S₁ S₂ : Submodule K V) [FiniteDimensional K S₂]
  body: finiteDimensional_of_le inf_le_right

中文:
实例 finiteDimensional_inf_right
  签名: (S₁ S₂ : 子模 K V) [有限维 K S₂]
  定义体: finiteDimensional_of_le inf_le_right

Depends on / 依赖: finiteDimensional_of_le, inf_le_right
-/
instance finiteDimensional_inf_right (S₁ S₂ : Submodule K V) [FiniteDimensional K S₂] :
    FiniteDimensional K (S₁ ⊓ S₂ : Submodule K V) :=
  finiteDimensional_of_le inf_le_right

/--
Instance `finiteDimensional_sup` / 实例 `finiteDimensional_sup`

English:
instance finiteDimensional_sup
  signature: (S₁ S₂ : Submodule K V) [h₁ : FiniteDimensional K S₁]
  body: finite_sup _ _

中文:
实例 finiteDimensional_sup
  签名: (S₁ S₂ : 子模 K V) [h₁ : 有限维 K S₁]
  定义体: finite_sup _ _

Depends on / 依赖: finite_sup
-/
instance finiteDimensional_sup (S₁ S₂ : Submodule K V) [h₁ : FiniteDimensional K S₁]
    [h₂ : FiniteDimensional K S₂] : FiniteDimensional K (S₁ ⊔ S₂ : Submodule K V) :=
  finite_sup _ _

/--
Instance `finiteDimensional_finset_sup` / 实例 `finiteDimensional_finset_sup`

English:
instance finiteDimensional_finset_sup
  signature: {ι : Type*} (s : Finset ι) (S : ι -> Submodule K V)
  body: Submodule.finite_finset_sup _ _

中文:
实例 finiteDimensional_finset_sup
  签名: {ι : 类型} (s : 有限集 ι) (S : ι -> 子模 K V)
  定义体: Submodule.finite_finset_sup _ _

Depends on / 依赖: Submodule, Submodule.finite_finset_sup, finite_finset_sup
-/
instance finiteDimensional_finset_sup {ι : Type*} (s : Finset ι) (S : ι -> Submodule K V)
    [forall i, FiniteDimensional K (S i)] : FiniteDimensional K (s.sup S : Submodule K V) :=
  Submodule.finite_finset_sup _ _

/--
Instance `finiteDimensional_iSup` / 实例 `finiteDimensional_iSup`

English:
instance finiteDimensional_iSup
  signature: {ι : Sort*} [Finite ι] (S : ι -> Submodule K V)
  body: Submodule.finite_iSup _

中文:
实例 finiteDimensional_iSup
  签名: {ι : 类型层*} [有限 ι] (S : ι -> 子模 K V)
  定义体: Submodule.finite_iSup _

Depends on / 依赖: Submodule, Submodule.finite_iSup, finite_iSup
-/
instance finiteDimensional_iSup {ι : Sort*} [Finite ι] (S : ι -> Submodule K V)
    [forall i, FiniteDimensional K (S i)] : FiniteDimensional K ↑(⨆ i, S i) :=
  Submodule.finite_iSup _

end DivisionRing

end Submodule

section

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/--
Instance `finiteDimensional_finsupp` / 实例 `finiteDimensional_finsupp`

English:
instance finiteDimensional_finsupp
  signature: {ι : Type*} [Finite ι] [FiniteDimensional K V]
  body: Module.Finite.finsupp

中文:
实例 finiteDimensional_finsupp
  签名: {ι : 类型} [有限 ι] [有限维 K V]
  定义体: Module.Finite.finsupp

Depends on / 依赖: Finite, Module, Module.Finite.finsupp, finsupp
-/
instance finiteDimensional_finsupp {ι : Type*} [Finite ι] [FiniteDimensional K V] :
    FiniteDimensional K (ι ->₀ V) :=
  Module.Finite.finsupp

end

namespace Submodule
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/--
theorem `eq_of_le_of_finrank_le` / 定理 `eq_of_le_of_finrank_le`

English:
theorem eq_of_le_of_finrank_le
  statement: {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂)
  proof: by
  rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)] at hd
  exact le_antisymm hle (Submodule.comap_subtype_eq_top.1
    (eq_top_of_finrank_eq (le_antisymm (comap (Submodule.subtype S₂) S₁).finrank_le hd)))

中文:
定理 eq_of_le_of_finrank_le
  结论: {S₁ S₂ : 子模 K V} [有限维 K S₂] (hle : S₁ <= S₂)
  证明: by
  rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)] at hd
  exact le_antisymm hle (Submodule.comap_subtype_eq_top.1
    (eq_top_of_finrank_eq (le_antisymm (comap (Submodule.subtype S₂) S₁).finrank_le hd)))

Depends on / 依赖: LinearEquiv, LinearEquiv.finrank_eq, Submodule, Submodule.comapSubtypeEquivOfLe, Submodule.comap_subtype_eq_top, Submodule.subtype, comapSubtypeEquivOfLe, comap_subtype_eq_top, eq_top_of_finrank_eq, finrank_eq, finrank_le, le_antisymm, subtype
-/
theorem eq_of_le_of_finrank_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂)
    (hd : finrank K S₂ <= finrank K S₁) : S₁ = S₂ := by
  rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)] at hd
  exact le_antisymm hle (Submodule.comap_subtype_eq_top.1
    (eq_top_of_finrank_eq (le_antisymm (comap (Submodule.subtype S₂) S₁).finrank_le hd)))

/--
theorem `eq_of_le_of_finrank_eq` / 定理 `eq_of_le_of_finrank_eq`

English:
theorem eq_of_le_of_finrank_eq
  statement: {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂)
  proof: eq_of_le_of_finrank_le hle hd.ge

中文:
定理 eq_of_le_of_finrank_eq
  结论: {S₁ S₂ : 子模 K V} [有限维 K S₂] (hle : S₁ <= S₂)
  证明: eq_of_le_of_finrank_le hle hd.ge

Depends on / 依赖: eq_of_le_of_finrank_le, hd.ge
-/
theorem eq_of_le_of_finrank_eq {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂)
    (hd : finrank K S₁ = finrank K S₂) : S₁ = S₂ :=
  eq_of_le_of_finrank_le hle hd.ge

end Submodule

namespace Subalgebra

variable {K L : Type*} [Field K] [Ring L] [Algebra K L] {F E : Subalgebra K L}
  [hfin : FiniteDimensional K E]

/--
theorem `eq_of_le_of_finrank_le` / 定理 `eq_of_le_of_finrank_le`

English:
theorem eq_of_le_of_finrank_le
  given: (h_le : F <= E) (h_finrank : finrank K E <= finrank K F)
  statement: F = E
  proof: haveI : Module.Finite K (Subalgebra.toSubmodule E) := hfin
toSubmodule_injective Submodule.eq_of_le_of_finrank_le h_le h_finrank

中文:
定理 eq_of_le_of_finrank_le
  条件: (h_le : F <= E) (h_finrank : finrank K E <= finrank K F)
  结论: F = E
  证明: haveI : Module.Finite K (Subalgebra.toSubmodule E) := hfin
toSubmodule_injective Submodule.eq_of_le_of_finrank_le h_le h_finrank

Depends on / 依赖: Finite, Module, Module.Finite, Subalgebra, Subalgebra.toSubmodule, Submodule, Submodule.eq_of_le_of_finrank_le, eq_of_le_of_finrank_le, h_finrank, h_le, toSubmodule, toSubmodule_injective
-/
theorem eq_of_le_of_finrank_le (h_le : F <= E) (h_finrank : finrank K E <= finrank K F) : F = E :=
  haveI : Module.Finite K (Subalgebra.toSubmodule E) := hfin
toSubmodule_injective Submodule.eq_of_le_of_finrank_le h_le h_finrank

/--
theorem `eq_of_le_of_finrank_eq` / 定理 `eq_of_le_of_finrank_eq`

English:
theorem eq_of_le_of_finrank_eq
  given: (h_le : F <= E) (h_finrank : finrank K F = finrank K E)
  statement: F = E
  proof: eq_of_le_of_finrank_le h_le h_finrank.ge

中文:
定理 eq_of_le_of_finrank_eq
  条件: (h_le : F <= E) (h_finrank : finrank K F = finrank K E)
  结论: F = E
  证明: eq_of_le_of_finrank_le h_le h_finrank.ge

Depends on / 依赖: eq_of_le_of_finrank_le, h_finrank, h_finrank.ge, h_le
-/
theorem eq_of_le_of_finrank_eq (h_le : F <= E) (h_finrank : finrank K F = finrank K E) : F = E :=
  eq_of_le_of_finrank_le h_le h_finrank.ge

end Subalgebra

namespace LinearMap

open Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/--
theorem `surjective_of_injective` / 定理 `surjective_of_injective`

English:
theorem surjective_of_injective
  given: [FiniteDimensional K V] {f : V ->ₗ[K] V} (hinj : Injective f)
  proof: by
  have h := rank_range_of_injective _ hinj
  rw [← finrank_eq_rank]; rw [← finrank_eq_rank]; rw [Nat.cast_inj] at h
  exact range_eq_top.1 (eq_top_of_finrank_eq h)

中文:
定理 surjective_of_injective
  条件: [有限维 K V] {f : V ->ₗ[K] V} (hinj : 单射 f)
  证明: by
  have h := rank_range_of_injective _ hinj
  rw [← finrank_eq_rank]; rw [← finrank_eq_rank]; rw [Nat.cast_inj] at h
  exact range_eq_top.1 (eq_top_of_finrank_eq h)

Depends on / 依赖: Nat.cast_inj, cast_inj, eq_top_of_finrank_eq, finrank_eq_rank, range_eq_top, rank_range_of_injective
-/
theorem surjective_of_injective [FiniteDimensional K V] {f : V ->ₗ[K] V} (hinj : Injective f) :
    Surjective f := by
  have h := rank_range_of_injective _ hinj
  rw [← finrank_eq_rank]; rw [← finrank_eq_rank]; rw [Nat.cast_inj] at h
  exact range_eq_top.1 (eq_top_of_finrank_eq h)

/--
theorem `finiteDimensional_of_surjective` / 定理 `finiteDimensional_of_surjective`

English:
theorem finiteDimensional_of_surjective
  statement: [FiniteDimensional K V] (f : V ->ₗ[K] V₂)
  proof: Module.Finite.of_surjective f range_eq_top.1 hf

中文:
定理 finiteDimensional_of_surjective
  结论: [有限维 K V] (f : V ->ₗ[K] V₂)
  证明: Module.Finite.of_surjective f range_eq_top.1 hf

Depends on / 依赖: Finite, Module, Module.Finite.of_surjective, of_surjective, range_eq_top
-/
theorem finiteDimensional_of_surjective [FiniteDimensional K V] (f : V ->ₗ[K] V₂)
    (hf : LinearMap.range f = ⊤) : FiniteDimensional K V₂ :=
Module.Finite.of_surjective f range_eq_top.1 hf

/--
Instance `finiteDimensional_range` / 实例 `finiteDimensional_range`

English:
instance finiteDimensional_range
  signature: [FiniteDimensional K V] (f : V ->ₗ[K] V₂)
  body: Module.Finite.range f

中文:
实例 finiteDimensional_range
  签名: [有限维 K V] (f : V ->ₗ[K] V₂)
  定义体: Module.Finite.range f

Depends on / 依赖: Finite, Module, Module.Finite.range
-/
instance finiteDimensional_range [FiniteDimensional K V] (f : V ->ₗ[K] V₂) :
    FiniteDimensional K (LinearMap.range f) :=
  Module.Finite.range f

/--
theorem `injective_iff_surjective` / 定理 `injective_iff_surjective`

English:
theorem injective_iff_surjective
  given: [FiniteDimensional K V] {f : V ->ₗ[K] V}
  proof: ⟨surjective_of_injective, fun hsurj =>
    let ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (range_eq_top.2 hsurj)
    have : Function.RightInverse g f := LinearMap.ext_iff.1 hg
    (leftInverse_of_surjective_of_rightInverse (surjective_of_injective this.injective)
        this).injective⟩

中文:
定理 injective_iff_surjective
  条件: [有限维 K V] {f : V ->ₗ[K] V}
  证明: ⟨surjective_of_injective, fun hsurj =>
    let ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (range_eq_top.2 hsurj)
    have : Function.RightInverse g f := LinearMap.ext_iff.1 hg
    (leftInverse_of_surjective_of_rightInverse (surjective_of_injective this.injective)
        this).injective⟩

Depends on / 依赖: Function, Function.RightInverse, LinearMap, LinearMap.ext_iff, RightInverse, exists_rightInverse_of_surjective, ext_iff, f.exists_rightInverse_of_surjective, injective, leftInverse_of_surjective_of_rightInverse, range_eq_top, surjective_of_injective, this.injective
-/
theorem injective_iff_surjective [FiniteDimensional K V] {f : V ->ₗ[K] V} :
    Injective f ↔ Surjective f :=
  ⟨surjective_of_injective, fun hsurj =>
    let ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (range_eq_top.2 hsurj)
    have : Function.RightInverse g f := LinearMap.ext_iff.1 hg
    (leftInverse_of_surjective_of_rightInverse (surjective_of_injective this.injective)
        this).injective⟩

/--
lemma `injOn_iff_surjOn` / 引理 `injOn_iff_surjOn`

English:
lemma injOn_iff_surjOn
  statement: {p : Submodule K V} [FiniteDimensional K p]
  proof: by
  rw [Set.injOn_iff_injective]; rw [← Set.MapsTo.restrict_surjective_iff h]
  change Injective (f.domRestrict p) ↔ Surjective (f.restrict h)
  simp [disjoint_iff, ← injective_iff_surjective]

中文:
引理 injOn_iff_surjOn
  结论: {p : 子模 K V} [有限维 K p]
  证明: by
  rw [Set.injOn_iff_injective]; rw [← Set.MapsTo.restrict_surjective_iff h]
  change Injective (f.domRestrict p) ↔ Surjective (f.restrict h)
  simp [disjoint_iff, ← injective_iff_surjective]

Depends on / 依赖: Injective, MapsTo, Set.MapsTo.restrict_surjective_iff, Set.injOn_iff_injective, Surjective, disjoint_iff, domRestrict, f.domRestrict, f.restrict, injOn_iff_injective, injective_iff_surjective, restrict, restrict_surjective_iff
-/
lemma injOn_iff_surjOn {p : Submodule K V} [FiniteDimensional K p]
    {f : V ->ₗ[K] V} (h : forall x in p, f x in p) :
    Set.InjOn f p ↔ Set.SurjOn f p p := by
  rw [Set.injOn_iff_injective]; rw [← Set.MapsTo.restrict_surjective_iff h]
  change Injective (f.domRestrict p) ↔ Surjective (f.restrict h)
  simp [disjoint_iff, ← injective_iff_surjective]

/--
theorem `ker_eq_bot_iff_range_eq_top` / 定理 `ker_eq_bot_iff_range_eq_top`

English:
theorem ker_eq_bot_iff_range_eq_top
  given: [FiniteDimensional K V] {f : V ->ₗ[K] V}
  proof: by
  rw [range_eq_top]; rw [ker_eq_bot]; rw [injective_iff_surjective]

中文:
定理 ker_eq_bot_iff_range_eq_top
  条件: [有限维 K V] {f : V ->ₗ[K] V}
  证明: by
  rw [range_eq_top]; rw [ker_eq_bot]; rw [injective_iff_surjective]

Depends on / 依赖: injective_iff_surjective, ker_eq_bot, range_eq_top
-/
theorem ker_eq_bot_iff_range_eq_top [FiniteDimensional K V] {f : V ->ₗ[K] V} :
    LinearMap.ker f = ⊥ ↔ LinearMap.range f = ⊤ := by
  rw [range_eq_top]; rw [ker_eq_bot]; rw [injective_iff_surjective]

/-- Any division ring is stably finite. -/
instance (priority := low) : IsStablyFiniteRing K := by
  refine isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd.mpr fun n => ⟨fun {f g} hfg => ?_⟩
  have ginj : Injective g :=
    HasLeftInverse.injective ⟨f, fun x => show (f * g) x = (1 : End K (Fin n -> K)) x by rw [hfg]⟩
  let ⟨i, hi⟩ := g.exists_rightInverse_of_surjective
    (range_eq_top.2 (injective_iff_surjective.1 ginj))
  have : f * (g * i) = f * 1 := congr_arg _ hi
  rw [← mul_assoc]; rw [hfg]; rw [one_mul]; rw [mul_one] at this; rwa [← this]

/--
theorem `_root_.IsField.of_isDomain_of_finite` / 定理 `_root_.IsField.of_isDomain_of_finite`

English:
theorem _root_.IsField.of_isDomain_of_finite
  statement: (K L : Type*) [Field K] [CommRing L] [IsDomain L]
  proof: Nontrivial.exists_pair_ne
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := (mulLeft K x).surjective_of_injective (mul_right_injective₀ hx) 1

中文:
定理 _root_.是域.of_isDomain_of_finite
  结论: (K L : 类型) [域 K] [交换环 L] [是整环 L]
  证明: Nontrivial.exists_pair_ne
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := (mulLeft K x).surjective_of_injective (mul_right_injective₀ hx) 1

Depends on / 依赖: Nontrivial, Nontrivial.exists_pair_ne, exists_pair_ne
-/
theorem _root_.IsField.of_isDomain_of_finite (K L : Type*) [Field K] [CommRing L] [IsDomain L]
    [Algebra K L] [Module.Finite K L] : IsField L where
  exists_pair_ne := Nontrivial.exists_pair_ne
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := (mulLeft K x).surjective_of_injective (mul_right_injective₀ hx) 1

section Semiring

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [Free R M] [Module.Finite R M]
variable [IsStablyFiniteRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStablyFiniteRing (Module.End R M)
  body: by
  let e := (Module.Free.chooseBasis R M).repr ≪≫ₗ Finsupp.linearEquivFunOnFinite ..
  rw [RingEquiv.isStablyFiniteRing_iff e.conjRingEquiv]
  infer_instance

中文:
实例 :
  签名: 是StablyFinite环 (模.End R M)
  定义体: by
  let e := (Module.Free.chooseBasis R M).repr ≪≫ₗ Finsupp.linearEquivFunOnFinite ..
  rw [RingEquiv.isStablyFiniteRing_iff e.conjRingEquiv]
  infer_instance

Depends on / 依赖: Finsupp, Finsupp.linearEquivFunOnFinite, Module, Module.Free.chooseBasis, RingEquiv, RingEquiv.isStablyFiniteRing_iff, chooseBasis, conjRingEquiv, e.conjRingEquiv, infer_instance, isStablyFiniteRing_iff, linearEquivFunOnFinite
-/
instance : IsStablyFiniteRing (Module.End R M) := by
  let e := (Module.Free.chooseBasis R M).repr ≪≫ₗ Finsupp.linearEquivFunOnFinite ..
  rw [RingEquiv.isStablyFiniteRing_iff e.conjRingEquiv]
  infer_instance

-- TODO: move the whole section to `Module.End` namespace.
/--
theorem `_root_.Module.End.injective_of_surjective` / 定理 `_root_.Module.End.injective_of_surjective`

English:
theorem _root_.Module.End.injective_of_surjective
  given: {f : Module.End R M} (hf : Surjective f)
  proof: have ⟨_, eq⟩ := projective_lifting_property _ .id hf
  injective_of_comp_eq_id _ _ (mul_eq_one_symm eq)

中文:
定理 _root_.模.End.injective_of_surjective
  条件: {f : 模.End R M} (hf : 满射 f)
  证明: have ⟨_, eq⟩ := projective_lifting_property _ .id hf
  injective_of_comp_eq_id _ _ (mul_eq_one_symm eq)

Depends on / 依赖: injective_of_comp_eq_id, mul_eq_one_symm, projective_lifting_property
-/
theorem _root_.Module.End.injective_of_surjective {f : Module.End R M} (hf : Surjective f) :
    Injective f :=
  have ⟨_, eq⟩ := projective_lifting_property _ .id hf
  injective_of_comp_eq_id _ _ (mul_eq_one_symm eq)

/--
theorem `comp_eq_id_comm` / 定理 `comp_eq_id_comm`

English:
theorem comp_eq_id_comm
  given: {f g : M ->ₗ[R] M}
  statement: f ∘ₗ g = id ↔ g ∘ₗ f = id
  proof: mul_eq_one_comm

中文:
定理 comp_eq_id_comm
  条件: {f g : M ->ₗ[R] M}
  结论: f ∘ₗ g = id ↔ g ∘ₗ f = id
  证明: mul_eq_one_comm

Depends on / 依赖: mul_eq_one_comm
-/
theorem comp_eq_id_comm {f g : M ->ₗ[R] M} : f ∘ₗ g = id ↔ g ∘ₗ f = id :=
  mul_eq_one_comm

end Semiring

/--
theorem `comap_eq_sup_ker_of_disjoint` / 定理 `comap_eq_sup_ker_of_disjoint`

English:
theorem comap_eq_sup_ker_of_disjoint
  statement: {p : Submodule K V} [FiniteDimensional K p] {f : V ->ₗ[K] V}
  proof: by
  refine le_antisymm (fun x hx => ?_) (sup_le_iff.mpr ⟨h, ker_le_comap _⟩)
  obtain ⟨⟨y, hy⟩, hxy⟩ :=
    surjective_of_injective ((injective_restrict_iff h).mpr h') ⟨f x, hx⟩
  replace hxy : f y = f x := by simpa [Subtype.ext_iff] using hxy
  exact Submodule.mem_sup.mpr ⟨y, hy, x - y, by simp [h

中文:
定理 comap_eq_sup_ker_of_disjoint
  结论: {p : 子模 K V} [有限维 K p] {f : V ->ₗ[K] V}
  证明: by
  refine le_antisymm (fun x hx => ?_) (sup_le_iff.mpr ⟨h, ker_le_comap _⟩)
  obtain ⟨⟨y, hy⟩, hxy⟩ :=
    surjective_of_injective ((injective_restrict_iff h).mpr h') ⟨f x, hx⟩
  replace hxy : f y = f x := by simpa [Subtype.ext_iff] using hxy
  exact Submodule.mem_sup.mpr ⟨y, hy, x - y, by simp [h

Depends on / 依赖: Submodule, Submodule.mem_sup.mpr, Subtype, Subtype.ext_iff, add_sub_cancel, ext_iff, injective_restrict_iff, ker_le_comap, le_antisymm, mem_sup, replace, sup_le_iff, sup_le_iff.mpr, surjective_of_injective
-/
theorem comap_eq_sup_ker_of_disjoint {p : Submodule K V} [FiniteDimensional K p] {f : V ->ₗ[K] V}
    (h : forall x in p, f x in p) (h' : Disjoint p (ker f)) :
    p.comap f = p ⊔ ker f := by
  refine le_antisymm (fun x hx => ?_) (sup_le_iff.mpr ⟨h, ker_le_comap _⟩)
  obtain ⟨⟨y, hy⟩, hxy⟩ :=
    surjective_of_injective ((injective_restrict_iff h).mpr h') ⟨f x, hx⟩
  replace hxy : f y = f x := by simpa [Subtype.ext_iff] using hxy
  exact Submodule.mem_sup.mpr ⟨y, hy, x - y, by simp [hxy], add_sub_cancel y x⟩

/--
theorem `ker_comp_eq_of_commute_of_disjoint_ker` / 定理 `ker_comp_eq_of_commute_of_disjoint_ker`

English:
theorem ker_comp_eq_of_commute_of_disjoint_ker
  statement: [FiniteDimensional K V] {f g : V ->ₗ[K] V}
  proof: by
  suffices forall x, f x = 0 -> f (g x) = 0 by rw [ker_comp, comap_eq_sup_ker_of_disjoint _ h']; simpa
  intro x hx
  rw [← comp_apply]; rw [← Module.End.mul_eq_comp]; rw [h.eq]; rw [Module.End.mul_apply]; rw [hx]; rw [map_zero]

中文:
定理 ker_comp_eq_of_commute_of_disjoint_ker
  结论: [有限维 K V] {f g : V ->ₗ[K] V}
  证明: by
  suffices forall x, f x = 0 -> f (g x) = 0 by rw [ker_comp, comap_eq_sup_ker_of_disjoint _ h']; simpa
  intro x hx
  rw [← comp_apply]; rw [← Module.End.mul_eq_comp]; rw [h.eq]; rw [Module.End.mul_apply]; rw [hx]; rw [map_zero]

Depends on / 依赖: Module, Module.End.mul_apply, Module.End.mul_eq_comp, comap_eq_sup_ker_of_disjoint, comp_apply, h.eq, ker_comp, map_zero, mul_apply, mul_eq_comp
-/
theorem ker_comp_eq_of_commute_of_disjoint_ker [FiniteDimensional K V] {f g : V ->ₗ[K] V}
    (h : Commute f g) (h' : Disjoint (ker f) (ker g)) :
    ker (f ∘ₗ g) = ker f ⊔ ker g := by
  suffices forall x, f x = 0 -> f (g x) = 0 by rw [ker_comp, comap_eq_sup_ker_of_disjoint _ h']; simpa
  intro x hx
  rw [← comp_apply]; rw [← Module.End.mul_eq_comp]; rw [h.eq]; rw [Module.End.mul_apply]; rw [hx]; rw [map_zero]

/--
theorem `ker_noncommProd_eq_of_supIndep_ker` / 定理 `ker_noncommProd_eq_of_supIndep_ker`

English:
theorem ker_noncommProd_eq_of_supIndep_ker
  statement: [FiniteDimensional K V] {ι : Type*} {f : ι -> V ->ₗ[K] V}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | insert i s hi ih =>
    replace ih : ker (Finset.noncommProd s f <| Set.Pairwise.mono (s.subset_insert i) comm) =
        ⨆ x in s, ker (f x) := ih _ (h.subset (s.subset_insert i))
    rw [Finset

中文:
定理 ker_noncommProd_eq_of_supIndep_ker
  结论: [有限维 K V] {ι : 类型} {f : ι -> V ->ₗ[K] V}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | insert i s hi ih =>
    replace ih : ker (Finset.noncommProd s f <| Set.Pairwise.mono (s.subset_insert i) comm) =
        ⨆ x in s, ker (f x) := ih _ (h.subset (s.subset_insert i))
    rw [Finset

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_coe, Finset.mem_insert_coe, Finset.noncommProd, Finset.noncommProd_insert_of_notMem, Module, Module.End.mul_eq_comp, Module.End.one_eq_id, Pairwise, Set.Pairwise.mono, classical, h.subset, iSup_insert, induction_on, insert, ker_comp_eq_of_commute_of_disjoint_ker, mem_coe, mem_insert_coe, mul_eq_comp
-/
theorem ker_noncommProd_eq_of_supIndep_ker [FiniteDimensional K V] {ι : Type*} {f : ι -> V ->ₗ[K] V}
    (s : Finset ι) (comm) (h : s.SupIndep fun i => ker (f i)) :
    ker (s.noncommProd f comm) = ⨆ i in s, ker (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | insert i s hi ih =>
    replace ih : ker (Finset.noncommProd s f <| Set.Pairwise.mono (s.subset_insert i) comm) =
        ⨆ x in s, ker (f x) := ih _ (h.subset (s.subset_insert i))
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi]; rw [Module.End.mul_eq_comp]; rw [ker_comp_eq_of_commute_of_disjoint_ker]
    · simp_rw [Finset.mem_insert_coe, iSup_insert, Finset.mem_coe, ih]
    · exact s.noncommProd_commute _ _ _ fun j hj =>
        comm (s.mem_insert_self i) (Finset.mem_insert_of_mem hj) (by lia)
    · replace h := Finset.supIndep_iff_disjoint_erase.mp h i (s.mem_insert_self i)
      simpa [ih, hi, Finset.sup_eq_iSup] using h

end DivisionRing

end LinearMap

namespace LinearEquiv

open Module

variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/--
Definition of `ofInjectiveEndo` / `ofInjectiveEndo` 的定义

English:
definition ofInjectiveEndo
  signature: (f : V ->ₗ[K] V) (h_inj : Injective f)
  body: LinearEquiv.ofBijective f ⟨h_inj, LinearMap.injective_iff_surjective.mp h_inj⟩

@[simp]

中文:
定义 ofInjectiveEndo
  签名: (f : V ->ₗ[K] V) (h_inj : 单射 f)
  定义体: LinearEquiv.ofBijective f ⟨h_inj, LinearMap.injective_iff_surjective.mp h_inj⟩

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, LinearMap, LinearMap.injective_iff_surjective.mp, h_inj, injective_iff_surjective, ofBijective
-/
noncomputable def ofInjectiveEndo (f : V ->ₗ[K] V) (h_inj : Injective f) : V ≃ₗ[K] V :=
  LinearEquiv.ofBijective f ⟨h_inj, LinearMap.injective_iff_surjective.mp h_inj⟩

@[simp]
/--
theorem `coe_ofInjectiveEndo` / 定理 `coe_ofInjectiveEndo`

English:
theorem coe_ofInjectiveEndo
  given: (f : V ->ₗ[K] V) (h_inj : Injective f)
  proof: rfl

@[simp]

中文:
定理 coe_ofInjectiveEndo
  条件: (f : V ->ₗ[K] V) (h_inj : 单射 f)
  证明: rfl

@[simp]
-/
theorem coe_ofInjectiveEndo (f : V ->ₗ[K] V) (h_inj : Injective f) :
    ⇑(ofInjectiveEndo f h_inj) = f :=
  rfl

@[simp]
/--
theorem `ofInjectiveEndo_right_inv` / 定理 `ofInjectiveEndo_right_inv`

English:
theorem ofInjectiveEndo_right_inv
  given: (f : V ->ₗ[K] V) (h_inj : Injective f)
  proof: LinearMap.ext (ofInjectiveEndo f h_inj).apply_symm_apply

@[simp]

中文:
定理 ofInjectiveEndo_right_inv
  条件: (f : V ->ₗ[K] V) (h_inj : 单射 f)
  证明: LinearMap.ext (ofInjectiveEndo f h_inj).apply_symm_apply

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, apply_symm_apply, h_inj, ofInjectiveEndo
-/
theorem ofInjectiveEndo_right_inv (f : V ->ₗ[K] V) (h_inj : Injective f) :
    f * (ofInjectiveEndo f h_inj).symm = 1 :=
LinearMap.ext (ofInjectiveEndo f h_inj).apply_symm_apply

@[simp]
/--
theorem `ofInjectiveEndo_left_inv` / 定理 `ofInjectiveEndo_left_inv`

English:
theorem ofInjectiveEndo_left_inv
  given: (f : V ->ₗ[K] V) (h_inj : Injective f)
  proof: LinearMap.ext (ofInjectiveEndo f h_inj).symm_apply_apply

中文:
定理 ofInjectiveEndo_left_inv
  条件: (f : V ->ₗ[K] V) (h_inj : 单射 f)
  证明: LinearMap.ext (ofInjectiveEndo f h_inj).symm_apply_apply

Depends on / 依赖: LinearMap, LinearMap.ext, h_inj, ofInjectiveEndo, symm_apply_apply
-/
theorem ofInjectiveEndo_left_inv (f : V ->ₗ[K] V) (h_inj : Injective f) :
    ((ofInjectiveEndo f h_inj).symm : V ->ₗ[K] V) * f = 1 :=
LinearMap.ext (ofInjectiveEndo f h_inj).symm_apply_apply

variable {V' : Type*} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
omit [FiniteDimensional K V]

/--
Definition of `ofInjectiveOfFinrankEq` / `ofInjectiveOfFinrankEq` 的定义

English:
definition ofInjectiveOfFinrankEq
  signature: (f : V ->ₗ[K] V') (hinj : Function.Injective f)
  body: haveI : LinearMap.range f = ⊤ :=
    Submodule.eq_top_of_finrank_eq ((LinearMap.finrank_range_of_inj hinj).trans hrank)
  (ofInjective f hinj).trans (ofTop (LinearMap.range f) this)

@[simp]

中文:
定义 ofInjectiveOfFinrankEq
  签名: (f : V ->ₗ[K] V') (hinj : 函数.单射 f)
  定义体: haveI : LinearMap.range f = ⊤ :=
    Submodule.eq_top_of_finrank_eq ((LinearMap.finrank_range_of_inj hinj).trans hrank)
  (ofInjective f hinj).trans (ofTop (LinearMap.range f) this)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.finrank_range_of_inj, LinearMap.range, Submodule, Submodule.eq_top_of_finrank_eq, eq_top_of_finrank_eq, finrank_range_of_inj, ofInjective
-/
noncomputable def ofInjectiveOfFinrankEq (f : V ->ₗ[K] V') (hinj : Function.Injective f)
    (hrank : Module.finrank K V = Module.finrank K V') : V ≃ₗ[K] V' :=
  haveI : LinearMap.range f = ⊤ :=
    Submodule.eq_top_of_finrank_eq ((LinearMap.finrank_range_of_inj hinj).trans hrank)
  (ofInjective f hinj).trans (ofTop (LinearMap.range f) this)

@[simp]
/--
lemma `coe_ofInjectiveOfFinrankEq` / 引理 `coe_ofInjectiveOfFinrankEq`

English:
lemma coe_ofInjectiveOfFinrankEq
  statement: (f : V ->ₗ[K] V') (hinj : Function.Injective f)
  proof: rfl

中文:
引理 coe_ofInjectiveOfFinrankEq
  结论: (f : V ->ₗ[K] V') (hinj : 函数.单射 f)
  证明: rfl
-/
lemma coe_ofInjectiveOfFinrankEq (f : V ->ₗ[K] V') (hinj : Function.Injective f)
    (hrank : Module.finrank K V = Module.finrank K V') :
    (ofInjectiveOfFinrankEq f hinj hrank).toLinearMap = f :=
  rfl
end LinearEquiv

namespace LinearMap

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/--
theorem `isUnit_iff_ker_eq_bot` / 定理 `isUnit_iff_ker_eq_bot`

English:
theorem isUnit_iff_ker_eq_bot
  given: [FiniteDimensional K V] (f : V ->ₗ[K] V)
  proof: by
  constructor
  · rintro ⟨u, rfl⟩
    exact LinearMap.ker_eq_bot_of_inverse u.inv_mul
  · intro h_inj
    rw [ker_eq_bot] at h_inj
    exact ⟨⟨f, (LinearEquiv.ofInjectiveEndo f h_inj).symm.toLinearMap,
      LinearEquiv.ofInjectiveEndo_right_inv f h_inj, LinearEquiv.ofInjectiveEndo_left_inv f h_i

中文:
定理 isUnit_iff_ker_eq_bot
  条件: [有限维 K V] (f : V ->ₗ[K] V)
  证明: by
  constructor
  · rintro ⟨u, rfl⟩
    exact LinearMap.ker_eq_bot_of_inverse u.inv_mul
  · intro h_inj
    rw [ker_eq_bot] at h_inj
    exact ⟨⟨f, (LinearEquiv.ofInjectiveEndo f h_inj).symm.toLinearMap,
      LinearEquiv.ofInjectiveEndo_right_inv f h_inj, LinearEquiv.ofInjectiveEndo_left_inv f h_i

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjectiveEndo, LinearEquiv.ofInjectiveEndo_left_inv, LinearEquiv.ofInjectiveEndo_right_inv, LinearMap, LinearMap.ker_eq_bot_of_inverse, h_inj, inv_mul, ker_eq_bot, ker_eq_bot_of_inverse, ofInjectiveEndo, ofInjectiveEndo_left_inv, ofInjectiveEndo_right_inv, symm.toLinearMap, toLinearMap, u.inv_mul
-/
theorem isUnit_iff_ker_eq_bot [FiniteDimensional K V] (f : V ->ₗ[K] V) :
    IsUnit f ↔ (LinearMap.ker f) = ⊥ := by
  constructor
  · rintro ⟨u, rfl⟩
    exact LinearMap.ker_eq_bot_of_inverse u.inv_mul
  · intro h_inj
    rw [ker_eq_bot] at h_inj
    exact ⟨⟨f, (LinearEquiv.ofInjectiveEndo f h_inj).symm.toLinearMap,
      LinearEquiv.ofInjectiveEndo_right_inv f h_inj, LinearEquiv.ofInjectiveEndo_left_inv f h_inj⟩,
      rfl⟩

/--
theorem `isUnit_iff_range_eq_top` / 定理 `isUnit_iff_range_eq_top`

English:
theorem isUnit_iff_range_eq_top
  given: [FiniteDimensional K V] (f : V ->ₗ[K] V)
  proof: by
  rw [isUnit_iff_ker_eq_bot]; rw [ker_eq_bot_iff_range_eq_top]

中文:
定理 isUnit_iff_range_eq_top
  条件: [有限维 K V] (f : V ->ₗ[K] V)
  证明: by
  rw [isUnit_iff_ker_eq_bot]; rw [ker_eq_bot_iff_range_eq_top]

Depends on / 依赖: isUnit_iff_ker_eq_bot, ker_eq_bot_iff_range_eq_top
-/
theorem isUnit_iff_range_eq_top [FiniteDimensional K V] (f : V ->ₗ[K] V) :
    IsUnit f ↔ (LinearMap.range f) = ⊤ := by
  rw [isUnit_iff_ker_eq_bot]; rw [ker_eq_bot_iff_range_eq_top]

end LinearMap

open FiniteDimensional Module

section

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/--
theorem `finrank_zero_iff_forall_zero` / 定理 `finrank_zero_iff_forall_zero`

English:
theorem finrank_zero_iff_forall_zero
  given: [FiniteDimensional K V]
  statement: finrank K V = 0 ↔ forall x : V, x = 0
  proof: Module.finrank_zero_iff.trans (subsingleton_iff_forall_eq 0)

中文:
定理 finrank_zero_iff_对任意_zero
  条件: [有限维 K V]
  结论: finrank K V = 0 ↔ 对任意 x : V, x = 0
  证明: Module.finrank_zero_iff.trans (subsingleton_iff_forall_eq 0)

Depends on / 依赖: Module, Module.finrank_zero_iff.trans, finrank_zero_iff, subsingleton_iff_forall_eq
-/
theorem finrank_zero_iff_forall_zero [FiniteDimensional K V] : finrank K V = 0 ↔ forall x : V, x = 0 :=
  Module.finrank_zero_iff.trans (subsingleton_iff_forall_eq 0)

/--
Definition of `basisOfFinrankZero` / `basisOfFinrankZero` 的定义

English:
definition basisOfFinrankZero
  signature: [FiniteDimensional K V] {ι : Type*} [IsEmpty ι]
  body: haveI : Subsingleton V := finrank_zero_iff.1 hV
  Basis.empty _

中文:
定义 basisOfFinrankZero
  签名: [有限维 K V] {ι : 类型} [是空 ι]
  定义体: haveI : Subsingleton V := finrank_zero_iff.1 hV
  Basis.empty _

Depends on / 依赖: Basis.empty, Subsingleton, finrank_zero_iff
-/
noncomputable def basisOfFinrankZero [FiniteDimensional K V] {ι : Type*} [IsEmpty ι]
    (hV : finrank K V = 0) : Basis ι K V :=
  haveI : Subsingleton V := finrank_zero_iff.1 hV
  Basis.empty _

end

section

/--
lemma `FiniteDimensional.exists_mul_eq_one` / 引理 `FiniteDimensional.exists_mul_eq_one`

English:
lemma FiniteDimensional.exists_mul_eq_one
  statement: (F : Type*) {K : Type*} [Field F] [Ring K] [IsDomain K]
  proof: by
  have : Function.Surjective (LinearMap.mulLeft F x) :=
    LinearMap.injective_iff_surjective.1 fun y z => ((mul_right_inj' H).1 : x * y = x * z -> y = z)
  exact this 1

中文:
引理 有限维.存在_mul_eq_one
  结论: (F : 类型) {K : 类型} [域 F] [环 K] [是整环 K]
  证明: by
  have : Function.Surjective (LinearMap.mulLeft F x) :=
    LinearMap.injective_iff_surjective.1 fun y z => ((mul_right_inj' H).1 : x * y = x * z -> y = z)
  exact this 1

Depends on / 依赖: Function, Function.Surjective, LinearMap, LinearMap.injective_iff_surjective, LinearMap.mulLeft, Surjective, injective_iff_surjective, mulLeft, mul_right_inj
-/
lemma FiniteDimensional.exists_mul_eq_one (F : Type*) {K : Type*} [Field F] [Ring K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] {x : K} (H : x != 0) : exists y, x * y = 1 := by
  have : Function.Surjective (LinearMap.mulLeft F x) :=
    LinearMap.injective_iff_surjective.1 fun y z => ((mul_right_inj' H).1 : x * y = x * z -> y = z)
  exact this 1

/-- A domain that is module-finite as an algebra over a field is a division ring. -/
@[instance_reducible]
/--
Definition of `divisionRingOfFiniteDimensional` / `divisionRingOfFiniteDimensional` 的定义

English:
definition divisionRingOfFiniteDimensional
  signature: (F K : Type*) [Field F] [Ring K] [IsDomain K]
  body: ‹IsDomain K›
  inv x :=
    letI := Classical.decEq K
if H : x = 0 then 0 else Classical.choose FiniteDimensional.exists_mul_eq_one F H
  mul_inv_cancel x hx := show x * dite _ (h := _) _ _ = _ by
    rw [dif_neg hx]
    exact (Classical.choose_spec (FiniteDimensional.exists_mul_eq_one F hx) :)
  in

中文:
定义 divisionRingOfFiniteDimensional
  签名: (F K : 类型) [域 F] [环 K] [是整环 K]
  定义体: ‹IsDomain K›
  inv x :=
    letI := Classical.decEq K
if H : x = 0 then 0 else Classical.choose FiniteDimensional.exists_mul_eq_one F H
  mul_inv_cancel x hx := show x * dite _ (h := _) _ _ = _ by
    rw [dif_neg hx]
    exact (Classical.choose_spec (FiniteDimensional.exists_mul_eq_one F hx) :)
  in

Depends on / 依赖: IsDomain
-/
noncomputable def divisionRingOfFiniteDimensional (F K : Type*) [Field F] [Ring K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] : DivisionRing K where
  __ := ‹IsDomain K›
  inv x :=
    letI := Classical.decEq K
if H : x = 0 then 0 else Classical.choose FiniteDimensional.exists_mul_eq_one F H
  mul_inv_cancel x hx := show x * dite _ (h := _) _ _ = _ by
    rw [dif_neg hx]
    exact (Classical.choose_spec (FiniteDimensional.exists_mul_eq_one F hx) :)
  inv_zero := dif_pos rfl
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/--
lemma `FiniteDimensional.isUnit` / 引理 `FiniteDimensional.isUnit`

English:
lemma FiniteDimensional.isUnit
  statement: (F : Type*) {K : Type*} [Field F] [Ring K] [IsDomain K]
  proof: let _ := divisionRingOfFiniteDimensional F K; H.isUnit

中文:
引理 有限维.isUnit
  结论: (F : 类型) {K : 类型} [域 F] [环 K] [是整环 K]
  证明: let _ := divisionRingOfFiniteDimensional F K; H.isUnit

Depends on / 依赖: H.isUnit, divisionRingOfFiniteDimensional, isUnit
-/
lemma FiniteDimensional.isUnit (F : Type*) {K : Type*} [Field F] [Ring K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] {x : K} (H : x != 0) : IsUnit x :=
  let _ := divisionRingOfFiniteDimensional F K; H.isUnit

/-- An integral domain that is module-finite as an algebra over a field is a field. -/
@[instance_reducible]
/--
Definition of `fieldOfFiniteDimensional` / `fieldOfFiniteDimensional` 的定义

English:
definition fieldOfFiniteDimensional
  signature: (F K : Type*) [Field F] [h : CommRing K] [IsDomain K]
  body: { divisionRingOfFiniteDimensional F K with
    toCommRing := h }

中文:
定义 fieldOfFiniteDimensional
  签名: (F K : 类型) [域 F] [h : 交换环 K] [是整环 K]
  定义体: { divisionRingOfFiniteDimensional F K with
    toCommRing := h }

Depends on / 依赖: divisionRingOfFiniteDimensional, toCommRing
-/
noncomputable def fieldOfFiniteDimensional (F K : Type*) [Field F] [h : CommRing K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] : Field K :=
  { divisionRingOfFiniteDimensional F K with
    toCommRing := h }

end
section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

section Span

open Submodule

/--
theorem `finrank_span_singleton` / 定理 `finrank_span_singleton`

English:
theorem finrank_span_singleton
  given: {v : V} (hv : v != 0)
  statement: finrank K (K ∙ v) = 1
  proof: by
  apply le_antisymm
  · exact finrank_span_le_card ({v} : Set V)
  · rw [Nat.succ_le_iff, finrank_pos_iff]
    use ⟨v, mem_span_singleton_self v⟩, 0
    apply Subtype.coe_ne_coe.mp
    simp [hv]

中文:
定理 finrank_span_singleton
  条件: {v : V} (hv : v != 0)
  结论: finrank K (K ∙ v) = 1
  证明: by
  apply le_antisymm
  · exact finrank_span_le_card ({v} : Set V)
  · rw [Nat.succ_le_iff, finrank_pos_iff]
    use ⟨v, mem_span_singleton_self v⟩, 0
    apply Subtype.coe_ne_coe.mp
    simp [hv]

Depends on / 依赖: Nat.succ_le_iff, Subtype, Subtype.coe_ne_coe.mp, coe_ne_coe, finrank_pos_iff, finrank_span_le_card, le_antisymm, mem_span_singleton_self, succ_le_iff
-/
theorem finrank_span_singleton {v : V} (hv : v != 0) : finrank K (K ∙ v) = 1 := by
  apply le_antisymm
  · exact finrank_span_le_card ({v} : Set V)
  · rw [Nat.succ_le_iff, finrank_pos_iff]
    use ⟨v, mem_span_singleton_self v⟩, 0
    apply Subtype.coe_ne_coe.mp
    simp [hv]

/--
theorem `Submodule.isAtom_iff_finrank_eq_one` / 定理 `Submodule.isAtom_iff_finrank_eq_one`

English:
theorem Submodule.isAtom_iff_finrank_eq_one
  given: {S : Submodule K V}
  proof: by
  refine ⟨fun hS => ?_, fun hS => ⟨by aesop, fun T hT => ?_⟩⟩
  · obtain ⟨v : V, hv : v in S, hv_ne : v != 0⟩ := S.ne_bot_iff.mp hS.ne_bot
    suffices K ∙ v = S by rw [← this, finrank_span_singleton hv_ne]
    have : K ∙ v != ⊥ := by
      rw [Submodule.ne_bot_iff]
      exact ⟨v, mem_span_singl

中文:
定理 子模.isAtom_iff_finrank_eq_one
  条件: {S : 子模 K V}
  证明: by
  refine ⟨fun hS => ?_, fun hS => ⟨by aesop, fun T hT => ?_⟩⟩
  · obtain ⟨v : V, hv : v in S, hv_ne : v != 0⟩ := S.ne_bot_iff.mp hS.ne_bot
    suffices K ∙ v = S by rw [← this, finrank_span_singleton hv_ne]
    have : K ∙ v != ⊥ := by
      rw [Submodule.ne_bot_iff]
      exact ⟨v, mem_span_singl

Depends on / 依赖: FiniteDimensional, S.ne_bot_iff.mp, Set.singleton_subset_iff, Submodule, Submodule.ne_bot_iff, finrank_span_singleton, hS.le_iff_eq, hS.ne_bot, hT.le, hv_ne, inclusion, inclusion_injective, le_iff_eq, mem_span_singleton_self, ne_bot, ne_bot_iff, of_finrank_eq_succ, of_injective, singleton_subset_iff, span_le
-/
theorem Submodule.isAtom_iff_finrank_eq_one {S : Submodule K V} :
    IsAtom S ↔ finrank K S = 1 := by
  refine ⟨fun hS => ?_, fun hS => ⟨by aesop, fun T hT => ?_⟩⟩
  · obtain ⟨v : V, hv : v in S, hv_ne : v != 0⟩ := S.ne_bot_iff.mp hS.ne_bot
    suffices K ∙ v = S by rw [← this, finrank_span_singleton hv_ne]
    have : K ∙ v != ⊥ := by
      rw [Submodule.ne_bot_iff]
      exact ⟨v, mem_span_singleton_self v, hv_ne⟩
    rwa [← hS.le_iff_eq this, span_le, Set.singleton_subset_iff]
  · have : FiniteDimensional K S := .of_finrank_eq_succ hS
    have : FiniteDimensional K T := .of_injective (inclusion hT.le) (inclusion_injective hT.le)
    rw [← finrank_eq_zero (R := K)]
    by_contra h
exact hT.ne eq_of_le_of_finrank_le hT.le by lia

/--
lemma `exists_smul_eq_of_finrank_eq_one` / 引理 `exists_smul_eq_of_finrank_eq_one`

English:
lemma exists_smul_eq_of_finrank_eq_one
  proof: by
  have : Submodule.span K {x} = ⊤ := by
    have : FiniteDimensional K V := .of_finrank_eq_succ h
    apply eq_top_of_finrank_eq
    rw [h]
    exact finrank_span_singleton hx
  have : y in Submodule.span K {x} := by rw [this]; exact mem_top
  exact mem_span_singleton.1 this

中文:
引理 存在_smul_eq_of_finrank_eq_one
  证明: by
  have : Submodule.span K {x} = ⊤ := by
    have : FiniteDimensional K V := .of_finrank_eq_succ h
    apply eq_top_of_finrank_eq
    rw [h]
    exact finrank_span_singleton hx
  have : y in Submodule.span K {x} := by rw [this]; exact mem_top
  exact mem_span_singleton.1 this

Depends on / 依赖: FiniteDimensional, Submodule, Submodule.span, eq_top_of_finrank_eq, finrank_span_singleton, mem_span_singleton, mem_top, of_finrank_eq_succ
-/
lemma exists_smul_eq_of_finrank_eq_one
    (h : finrank K V = 1) {x : V} (hx : x != 0) (y : V) :
    exists (c : K), c • x = y := by
  have : Submodule.span K {x} = ⊤ := by
    have : FiniteDimensional K V := .of_finrank_eq_succ h
    apply eq_top_of_finrank_eq
    rw [h]
    exact finrank_span_singleton hx
  have : y in Submodule.span K {x} := by rw [this]; exact mem_top
  exact mem_span_singleton.1 this

/--
theorem `eq_span_singleton_of_mem_of_finrank_eq_one` / 定理 `eq_span_singleton_of_mem_of_finrank_eq_one`

English:
theorem eq_span_singleton_of_mem_of_finrank_eq_one
  statement: {S : Submodule K V} {w : V}
  proof: by
  have : FiniteDimensional K S := Module.finite_of_finrank_pos (by lia)
exact Eq.symm eq_of_le_of_finrank_le (by simpa)
    (by rw [hS, finrank_span_singleton hw0])

中文:
定理 eq_span_singleton_of_mem_of_finrank_eq_one
  结论: {S : 子模 K V} {w : V}
  证明: by
  have : FiniteDimensional K S := Module.finite_of_finrank_pos (by lia)
exact Eq.symm eq_of_le_of_finrank_le (by simpa)
    (by rw [hS, finrank_span_singleton hw0])

Depends on / 依赖: Eq.symm, FiniteDimensional, Module, Module.finite_of_finrank_pos, eq_of_le_of_finrank_le, finite_of_finrank_pos, finrank_span_singleton
-/
theorem eq_span_singleton_of_mem_of_finrank_eq_one {S : Submodule K V} {w : V}
    (hS : finrank K S = 1) (hw : w in S) (hw0 : w != 0) :
    S = K ∙ w := by
  have : FiniteDimensional K S := Module.finite_of_finrank_pos (by lia)
exact Eq.symm eq_of_le_of_finrank_le (by simpa)
    (by rw [hS, finrank_span_singleton hw0])

/--
theorem `Set.finrank_mono` / 定理 `Set.finrank_mono`

English:
theorem Set.finrank_mono
  given: [FiniteDimensional K V] {s t : Set V} (h : s subseteq t)
  proof: Submodule.finrank_mono (span_mono h)

中文:
定理 集合.finrank_mono
  条件: [有限维 K V] {s t : 集合 V} (h : s subseteq t)
  证明: Submodule.finrank_mono (span_mono h)

Depends on / 依赖: Submodule, Submodule.finrank_mono, finrank_mono, span_mono
-/
theorem Set.finrank_mono [FiniteDimensional K V] {s t : Set V} (h : s subseteq t) :
    s.finrank K <= t.finrank K :=
  Submodule.finrank_mono (span_mono h)

end Span

/-!
We now give characterisations of `finrank K V = 1` and `finrank K V ≤ 1`.
-/


section finrank_eq_one

/--
theorem `finrank_eq_one_iff_of_nonzero` / 定理 `finrank_eq_one_iff_of_nonzero`

English:
theorem finrank_eq_one_iff_of_nonzero
  given: (v : V) (nz : v != 0)
  proof: by simpa using (basisSingleton Unit h v nz).span_eq
mpr s := finrank_eq_card_basis .mk (.of_subsingleton (v := ![v]) 0 nz) by simp [← s]

中文:
定理 finrank_eq_one_iff_of_nonzero
  条件: (v : V) (nz : v != 0)
  证明: by simpa using (basisSingleton Unit h v nz).span_eq
mpr s := finrank_eq_card_basis .mk (.of_subsingleton (v := ![v]) 0 nz) by simp [← s]

Depends on / 依赖: basisSingleton, finrank_eq_card_basis, of_subsingleton, span_eq
-/
theorem finrank_eq_one_iff_of_nonzero (v : V) (nz : v != 0) :
    finrank K V = 1 ↔ span K ({v} : Set V) = ⊤ where
  mp h := by simpa using (basisSingleton Unit h v nz).span_eq
mpr s := finrank_eq_card_basis .mk (.of_subsingleton (v := ![v]) 0 nz) by simp [← s]

/--
theorem `finrank_eq_one_iff_of_nonzero'` / 定理 `finrank_eq_one_iff_of_nonzero'`

English:
theorem finrank_eq_one_iff_of_nonzero'
  given: (v : V) (nz : v != 0)
  proof: by
  rw [finrank_eq_one_iff_of_nonzero v nz]
  apply span_singleton_eq_top_iff

中文:
定理 finrank_eq_one_iff_of_nonzero'
  条件: (v : V) (nz : v != 0)
  证明: by
  rw [finrank_eq_one_iff_of_nonzero v nz]
  apply span_singleton_eq_top_iff

Depends on / 依赖: finrank_eq_one_iff_of_nonzero, span_singleton_eq_top_iff
-/
theorem finrank_eq_one_iff_of_nonzero' (v : V) (nz : v != 0) :
    finrank K V = 1 ↔ forall w : V, exists c : K, c • v = w := by
  rw [finrank_eq_one_iff_of_nonzero v nz]
  apply span_singleton_eq_top_iff

-- We use the `LinearMap.CompatibleSMul` typeclass here, to encompass two situations:
-- * `A = K`
-- * `[Field K] [Algebra K A] [IsScalarTower K A V] [IsScalarTower K A W]`
/--
theorem `surjective_of_nonzero_of_finrank_eq_one` / 定理 `surjective_of_nonzero_of_finrank_eq_one`

English:
theorem surjective_of_nonzero_of_finrank_eq_one
  statement: {W A : Type*} [Semiring A] [Module A V]
  proof: by
  change Surjective (f.restrictScalars K)
  obtain ⟨v, n⟩ := DFunLike.ne_iff.mp w
  intro z
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (f v) n).mp h z
  exact ⟨c • v, by simp⟩

中文:
定理 surjective_of_nonzero_of_finrank_eq_one
  结论: {W A : 类型} [半环 A] [模 A V]
  证明: by
  change Surjective (f.restrictScalars K)
  obtain ⟨v, n⟩ := DFunLike.ne_iff.mp w
  intro z
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (f v) n).mp h z
  exact ⟨c • v, by simp⟩

Depends on / 依赖: DFunLike, DFunLike.ne_iff.mp, Surjective, f.restrictScalars, finrank_eq_one_iff_of_nonzero, ne_iff, restrictScalars
-/
theorem surjective_of_nonzero_of_finrank_eq_one {W A : Type*} [Semiring A] [Module A V]
    [AddCommGroup W] [Module K W] [Module A W] [LinearMap.CompatibleSMul V W K A]
    (h : finrank K W = 1) {f : V ->ₗ[A] W} (w : f != 0) : Surjective f := by
  change Surjective (f.restrictScalars K)
  obtain ⟨v, n⟩ := DFunLike.ne_iff.mp w
  intro z
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (f v) n).mp h z
  exact ⟨c • v, by simp⟩

end finrank_eq_one

end DivisionRing

section SubalgebraRank

open Module

variable {F E : Type*} [Field F] [Ring E] [Algebra F E]

/--
theorem `Subalgebra.finiteDimensional_toSubmodule` / 定理 `Subalgebra.finiteDimensional_toSubmodule`

English:
theorem Subalgebra.finiteDimensional_toSubmodule
  given: {S : Subalgebra F E}
  proof: Iff.rfl

alias ⟨FiniteDimensional.of_subalgebra_toSubmodule, FiniteDimensional.subalgebra_toSubmodule⟩ :=
  Subalgebra.finiteDimensional_toSubmodule

中文:
定理 子代数.finiteDimensional_toSubmodule
  条件: {S : 子代数 F E}
  证明: Iff.rfl

alias ⟨FiniteDimensional.of_subalgebra_toSubmodule, FiniteDimensional.subalgebra_toSubmodule⟩ :=
  Subalgebra.finiteDimensional_toSubmodule

Depends on / 依赖: Iff.rfl
-/
theorem Subalgebra.finiteDimensional_toSubmodule {S : Subalgebra F E} :
    FiniteDimensional F (Subalgebra.toSubmodule S) ↔ FiniteDimensional F S :=
  Iff.rfl

alias ⟨FiniteDimensional.of_subalgebra_toSubmodule, FiniteDimensional.subalgebra_toSubmodule⟩ :=
  Subalgebra.finiteDimensional_toSubmodule

/--
Instance `FiniteDimensional.finiteDimensional_subalgebra` / 实例 `FiniteDimensional.finiteDimensional_subalgebra`

English:
instance FiniteDimensional.finiteDimensional_subalgebra
  signature: [FiniteDimensional F E]
  body: FiniteDimensional.of_subalgebra_toSubmodule inferInstance

中文:
实例 有限维.finiteDimensional_subalgebra
  签名: [有限维 F E]
  定义体: FiniteDimensional.of_subalgebra_toSubmodule inferInstance

Depends on / 依赖: FiniteDimensional, FiniteDimensional.of_subalgebra_toSubmodule, of_subalgebra_toSubmodule
-/
instance FiniteDimensional.finiteDimensional_subalgebra [FiniteDimensional F E]
    (S : Subalgebra F E) : FiniteDimensional F S :=
  FiniteDimensional.of_subalgebra_toSubmodule inferInstance

end SubalgebraRank

namespace Module

namespace End

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/--
theorem `ker_pow_constant` / 定理 `ker_pow_constant`

English:
theorem ker_pow_constant
  statement: {f : End K V} {k : Nat}

中文:
定理 ker_pow_constant
  结论: {f : End K V} {k : 自然数}
-/
theorem ker_pow_constant {f : End K V} {k : Nat}
    (h : LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ)) :
    forall m, LinearMap.ker (f ^ k) = LinearMap.ker (f ^ (k + m))
  | 0 => by simp
  | m + 1 => by
    apply le_antisymm
    · rw [add_comm, pow_add]
      apply LinearMap.ker_le_ker_comp
    · rw [ker_pow_constant h m, add_comm m 1, ← add_assoc, pow_add, pow_add f k m,
        Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.ker_comp, LinearMap.ker_comp, h,
        Nat.add_one]

end End

end Module

/--
theorem `AlgHom.bijective` / 定理 `AlgHom.bijective`

English:
theorem AlgHom.bijective
  statement: {K S : Type*} [Field K] [Ring S] [IsSimpleRing S]
  proof: ⟨f.toRingHom.injective, f.toLinearMap.injective_iff_surjective.mp f.toRingHom.injective⟩

中文:
定理 代数态射.bijective
  结论: {K S : 类型} [域 K] [环 S] [是单环 S]
  证明: ⟨f.toRingHom.injective, f.toLinearMap.injective_iff_surjective.mp f.toRingHom.injective⟩

Depends on / 依赖: f.toLinearMap.injective_iff_surjective.mp, f.toRingHom.injective, injective, injective_iff_surjective, toLinearMap, toRingHom
-/
theorem AlgHom.bijective {K S : Type*} [Field K] [Ring S] [IsSimpleRing S]
    [Algebra K S] [FiniteDimensional K S] (f : S ->ₐ[K] S) : Function.Bijective f :=
  ⟨f.toRingHom.injective, f.toLinearMap.injective_iff_surjective.mp f.toRingHom.injective⟩
