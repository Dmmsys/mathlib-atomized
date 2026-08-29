/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!

# Weierstrass `℘` functions

## Main definitions and results
- `PeriodPair.weierstrassP`: The Weierstrass `℘`-function associated to a pair of periods.
- `PeriodPair.hasSumLocallyUniformly_weierstrassP`:
  The summands of `℘` sums to `℘` locally uniformly.
- `PeriodPair.differentiableOn_weierstrassP`: `℘` is differentiable away from the lattice points.
- `PeriodPair.weierstrassP_add_coe`: The Weierstrass `℘`-function is periodic.
- `PeriodPair.weierstrassP_neg`: The Weierstrass `℘`-function is even.

- `PeriodPair.derivWeierstrassP`:
  The derivative of the Weierstrass `℘`-function associated to a pair of periods.
- `PeriodPair.hasSumLocallyUniformly_derivWeierstrassP`:
  The summands of `℘'` sums to `℘'` locally uniformly.
- `PeriodPair.differentiableOn_derivWeierstrassP`:
  `℘'` is differentiable away from the lattice points.
- `PeriodPair.derivWeierstrassP_add_coe`: `℘'` is periodic.
- `PeriodPair.weierstrassP_neg`: `℘'` is odd.
- `PeriodPair.deriv_weierstrassP`: `deriv ℘ = ℘'`. This is true globally because of junk values.
- `PeriodPair.analyticOnNhd_weierstrassP`: `℘` is analytic away from the lattice points.
- `PeriodPair.meromorphic_weierstrassP`: `℘` is meromorphic on the whole plane.
- `PeriodPair.order_weierstrassP`: `℘` has a pole of order 2 at each of the lattice points.
- `PeriodPair.derivWeierstrassP_sq` : `℘'(z)² = 4 ℘(z)³ - g₂ ℘(z) - g₃`

## tags

Weierstrass p-functions, Weierstrass p functions

-/

@[expose] public section

open Module Filter
open scoped Topology Nat

noncomputable section

/--
Definition of `PeriodPair` / `PeriodPair` 的定义

English:
structure PeriodPair
  parameters: : Type where
  axioms and operations (3):
    - ω₁ : Complex
    - ω₂ : Complex
    - indep : LinearIndependent Real ![ω₁, ω₂]

中文:
结构 PeriodPair
  参数: : 类型 where
  公理与运算 (3 个):
    - ω₁ : 复形
    - ω₂ : 复形
    - indep : LinearIndependent 实数 ![ω₁, ω₂]
-/
structure PeriodPair : Type where
  /-- The first period in a `PeriodPair`. -/
  ω₁ : Complex
  /-- The second period in a `PeriodPair`. -/
  ω₂ : Complex
  indep : LinearIndependent Real ![ω₁, ω₂]

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (L : PeriodPair)

namespace PeriodPair

/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: : Basis (Fin 2) Real Complex
  body: basisOfLinearIndependentOfCardEqFinrank L.indep (by simp)

中文:
定义 basis
  签名: : 基 (有限集 2) 实数 复形
  定义体: basisOfLinearIndependentOfCardEqFinrank L.indep (by simp)
-/
protected def basis : Basis (Fin 2) Real Complex :=
  basisOfLinearIndependentOfCardEqFinrank L.indep (by simp)

/--
lemma `basis_zero` / 引理 `basis_zero`

English:
lemma basis_zero
  statement: L.basis 0 = L.ω₁
  proof: by simp [PeriodPair.basis]

中文:
引理 basis_zero
  结论: L.basis 0 = L.ω₁
  证明: by simp [PeriodPair.basis]
-/
@[simp] lemma basis_zero : L.basis 0 = L.ω₁ := by simp [PeriodPair.basis]
/--
lemma `basis_one` / 引理 `basis_one`

English:
lemma basis_one
  statement: L.basis 1 = L.ω₂
  proof: by simp [PeriodPair.basis]

中文:
引理 basis_one
  结论: L.basis 1 = L.ω₂
  证明: by simp [PeriodPair.basis]
-/
@[simp] lemma basis_one : L.basis 1 = L.ω₂ := by simp [PeriodPair.basis]

/--
Definition of `lattice` / `lattice` 的定义

English:
definition lattice
  signature: : Submodule Int Complex
  body: Submodule.span Int {L.ω₁, L.ω₂}

中文:
定义 lattice
  签名: : 子模 整数 复形
  定义体: Submodule.span Int {L.ω₁, L.ω₂}

Depends on / 依赖: Submodule, Submodule.span
-/
def lattice : Submodule Int Complex := Submodule.span Int {L.ω₁, L.ω₂}

/--
lemma `mem_lattice` / 引理 `mem_lattice`

English:
lemma mem_lattice
  given: {L : PeriodPair} {x : Complex}
  proof: by
  simp only [lattice, Submodule.mem_span_pair, zsmul_eq_mul]

中文:
引理 mem_lattice
  条件: {L : PeriodPair} {x : 复形}
  证明: by
  simp only [lattice, Submodule.mem_span_pair, zsmul_eq_mul]

Depends on / 依赖: Submodule, Submodule.mem_span_pair, lattice, mem_span_pair, zsmul_eq_mul
-/
lemma mem_lattice {L : PeriodPair} {x : Complex} :
    x in L.lattice ↔ exists m n : Int, m * L.ω₁ + n * L.ω₂ = x := by
  simp only [lattice, Submodule.mem_span_pair, zsmul_eq_mul]

/--
lemma `ω₁_mem_lattice` / 引理 `ω₁_mem_lattice`

English:
lemma ω₁_mem_lattice
  statement: L.ω₁ in L.lattice
  proof: Submodule.subset_span (by simp)

中文:
引理 ω₁_mem_lattice
  结论: L.ω₁ in L.lattice
  证明: Submodule.subset_span (by simp)

Depends on / 依赖: Submodule, Submodule.subset_span, subset_span
-/
lemma ω₁_mem_lattice : L.ω₁ in L.lattice := Submodule.subset_span (by simp)
/--
lemma `ω₂_mem_lattice` / 引理 `ω₂_mem_lattice`

English:
lemma ω₂_mem_lattice
  statement: L.ω₂ in L.lattice
  proof: Submodule.subset_span (by simp)

中文:
引理 ω₂_mem_lattice
  结论: L.ω₂ in L.lattice
  证明: Submodule.subset_span (by simp)

Depends on / 依赖: Submodule, Submodule.subset_span, subset_span
-/
lemma ω₂_mem_lattice : L.ω₂ in L.lattice := Submodule.subset_span (by simp)

/--
lemma `mul_ω₁_add_mul_ω₂_mem_lattice` / 引理 `mul_ω₁_add_mul_ω₂_mem_lattice`

English:
lemma mul_ω₁_add_mul_ω₂_mem_lattice
  given: {L : PeriodPair} {α β : Rat}
  proof: by
  refine ⟨fun H => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · obtain ⟨m, n, e⟩ := mem_lattice.mp H
    have := LinearIndependent.pair_iff.mp L.indep (m - α) (n - β)
      (by simp; linear_combination e)
    simp only [sub_eq_zero] at this
    norm_cast at this
    aesop
  · lift α to Int using h₁
    lift β to 

中文:
引理 mul_ω₁_add_mul_ω₂_mem_lattice
  条件: {L : PeriodPair} {α β : 有理数}
  证明: by
  refine ⟨fun H => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · obtain ⟨m, n, e⟩ := mem_lattice.mp H
    have := LinearIndependent.pair_iff.mp L.indep (m - α) (n - β)
      (by simp; linear_combination e)
    simp only [sub_eq_zero] at this
    norm_cast at this
    aesop
  · lift α to Int using h₁
    lift β to 

Depends on / 依赖: L.indep, LinearIndependent, LinearIndependent.pair_iff.mp, Rat.cast_intCast, Submodule, Submodule.smul_mem, add_mem, cast_intCast, linear_combination, mem_lattice, mem_lattice.mp, pair_iff, smul_mem, sub_eq_zero, zsmul_eq_mul
-/
lemma mul_ω₁_add_mul_ω₂_mem_lattice {L : PeriodPair} {α β : Rat} :
    α * L.ω₁ + β * L.ω₂ in L.lattice ↔ α.den = 1 ∧ β.den = 1 := by
  refine ⟨fun H => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · obtain ⟨m, n, e⟩ := mem_lattice.mp H
    have := LinearIndependent.pair_iff.mp L.indep (m - α) (n - β)
      (by simp; linear_combination e)
    simp only [sub_eq_zero] at this
    norm_cast at this
    aesop
  · lift α to Int using h₁
    lift β to Int using h₂
    simp only [Rat.cast_intCast, ← zsmul_eq_mul]
    exact add_mem (Submodule.smul_mem _ _ L.ω₁_mem_lattice)
      (Submodule.smul_mem _ _ L.ω₂_mem_lattice)

/--
lemma `ω₁_div_two_notMem_lattice` / 引理 `ω₁_div_two_notMem_lattice`

English:
lemma ω₁_div_two_notMem_lattice
  statement: L.ω₁ / 2 ∉ L.lattice
  proof: by
  simpa [inv_mul_eq_div] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 2) (β := 0)).not.mpr (by norm_num)

中文:
引理 ω₁_div_two_notMem_lattice
  结论: L.ω₁ / 2 ∉ L.lattice
  证明: by
  simpa [inv_mul_eq_div] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 2) (β := 0)).not.mpr (by norm_num)

Depends on / 依赖: L.mul_, inv_mul_eq_div, not.mpr
-/
lemma ω₁_div_two_notMem_lattice : L.ω₁ / 2 ∉ L.lattice := by
  simpa [inv_mul_eq_div] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 2) (β := 0)).not.mpr (by norm_num)

/--
lemma `ω₂_div_two_notMem_lattice` / 引理 `ω₂_div_two_notMem_lattice`

English:
lemma ω₂_div_two_notMem_lattice
  statement: L.ω₂ / 2 ∉ L.lattice
  proof: by
  simpa [inv_mul_eq_div] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 0) (β := 1 / 2)).not.mpr (by norm_num)

中文:
引理 ω₂_div_two_notMem_lattice
  结论: L.ω₂ / 2 ∉ L.lattice
  证明: by
  simpa [inv_mul_eq_div] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 0) (β := 1 / 2)).not.mpr (by norm_num)

Depends on / 依赖: L.mul_, inv_mul_eq_div, not.mpr
-/
lemma ω₂_div_two_notMem_lattice : L.ω₂ / 2 ∉ L.lattice := by
  simpa [inv_mul_eq_div] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 0) (β := 1 / 2)).not.mpr (by norm_num)

-- helper lemma to connect to the ZLattice API
/--
lemma `lattice_eq_span_range_basis` / 引理 `lattice_eq_span_range_basis`

English:
lemma lattice_eq_span_range_basis
  proof: by
  have : Finset.univ (α := Fin 2) = {0, 1} := rfl
  rw [lattice]; rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [this]
  simp [Set.image_insert_eq]

中文:
引理 lattice_eq_span_range_basis
  证明: by
  have : Finset.univ (α := Fin 2) = {0, 1} := rfl
  rw [lattice]; rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [this]
  simp [Set.image_insert_eq]

Depends on / 依赖: Finset, Finset.coe_univ, Finset.univ, Set.image_insert_eq, Set.image_univ, coe_univ, image_insert_eq, image_univ, lattice
-/
lemma lattice_eq_span_range_basis :
    L.lattice = Submodule.span Int (Set.range L.basis) := by
  have : Finset.univ (α := Fin 2) = {0, 1} := rfl
  rw [lattice]; rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [this]
  simp [Set.image_insert_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology L.lattice
  body: L.lattice_eq_span_range_basis ▸ inferInstance

中文:
实例 :
  签名: 离散拓扑 L.lattice
  定义体: L.lattice_eq_span_range_basis ▸ inferInstance

Depends on / 依赖: L.lattice_eq_span_range_basis, lattice_eq_span_range_basis
-/
instance : DiscreteTopology L.lattice := L.lattice_eq_span_range_basis ▸ inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZLattice Real L.lattice
  body: by
  simp_rw [L.lattice_eq_span_range_basis]
  infer_instance

中文:
实例 :
  签名: 是Z格 实数 L.lattice
  定义体: by
  simp_rw [L.lattice_eq_span_range_basis]
  infer_instance

Depends on / 依赖: L.lattice_eq_span_range_basis, Projective, Projective.projective_over, infer_instance, lattice_eq_span_range_basis, projective_over, simp_rw
-/
instance : IsZLattice Real L.lattice := by
  simp_rw [L.lattice_eq_span_range_basis]
  infer_instance

/--
lemma `isClosed_lattice` / 引理 `isClosed_lattice`

English:
lemma isClosed_lattice
  statement: IsClosed (X := Complex) L.lattice
  proof: @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.lattice.toAddSubgroup
    (inferInstanceAs (DiscreteTopology L.lattice))

中文:
引理 isClosed_lattice
  结论: 是闭集 (X := 复形) L.lattice
  证明: @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.lattice.toAddSubgroup
    (inferInstanceAs (DiscreteTopology L.lattice))

Depends on / 依赖: HasProjectiveResolution, L.lattice, lattice
-/
lemma isClosed_lattice : IsClosed (X := Complex) L.lattice :=
  @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.lattice.toAddSubgroup
    (inferInstanceAs (DiscreteTopology L.lattice))

/--
lemma `isClosed_of_subset_lattice` / 引理 `isClosed_of_subset_lattice`

English:
lemma isClosed_of_subset_lattice
  given: {s : Set Complex} (hs : s subseteq L.lattice)
  statement: IsClosed s
  proof: by
  convert!
    L.isClosed_lattice.isClosedMap_subtype_val _ (isClosed_discrete (α := L.lattice) ((↑) ⁻¹' s))
  convert! Set.image_preimage_eq_inter_range.symm using 1
  simpa

中文:
引理 isClosed_of_subset_lattice
  条件: {s : 集合 复形} (hs : s subseteq L.lattice)
  结论: 是闭集 s
  证明: by
  convert!
    L.isClosed_lattice.isClosedMap_subtype_val _ (isClosed_discrete (α := L.lattice) ((↑) ⁻¹' s))
  convert! Set.image_preimage_eq_inter_range.symm using 1
  simpa

Depends on / 依赖: HasProjectiveResolutions, L.isClosed_lattice.isClosedMap_subtype_val, L.lattice, Set.image_preimage_eq_inter_range.symm, convert, image_preimage_eq_inter_range, isClosedMap_subtype_val, isClosed_discrete, isClosed_lattice, lattice
-/
lemma isClosed_of_subset_lattice {s : Set Complex} (hs : s subseteq L.lattice) : IsClosed s := by
  convert!
    L.isClosed_lattice.isClosedMap_subtype_val _ (isClosed_discrete (α := L.lattice) ((↑) ⁻¹' s))
  convert! Set.image_preimage_eq_inter_range.symm using 1
  simpa

/--
lemma `isOpen_compl_lattice_sdiff` / 引理 `isOpen_compl_lattice_sdiff`

English:
lemma isOpen_compl_lattice_sdiff
  given: {s : Set Complex}
  statement: IsOpen (L.lattice \ s)ᶜ
  proof: (L.isClosed_of_subset_lattice Set.sdiff_subset).isOpen_compl

@[deprecated (since := "2026-06-03")] alias isOpen_compl_lattice_diff := isOpen_compl_lattice_sdiff

中文:
引理 isOpen_compl_lattice_sdiff
  条件: {s : 集合 复形}
  结论: 是开集 (L.lattice \ s)ᶜ
  证明: (L.isClosed_of_subset_lattice Set.sdiff_subset).isOpen_compl

@[deprecated (since := "2026-06-03")] alias isOpen_compl_lattice_diff := isOpen_compl_lattice_sdiff

Depends on / 依赖: L.isClosed_of_subset_lattice, Set.sdiff_subset, isClosed_of_subset_lattice, isOpen_compl, sdiff_subset
-/
lemma isOpen_compl_lattice_sdiff {s : Set Complex} : IsOpen (L.lattice \ s)ᶜ :=
  (L.isClosed_of_subset_lattice Set.sdiff_subset).isOpen_compl

@[deprecated (since := "2026-06-03")] alias isOpen_compl_lattice_diff := isOpen_compl_lattice_sdiff

open scoped Topology in
/--
lemma `compl_lattice_sdiff_singleton_mem_nhds` / 引理 `compl_lattice_sdiff_singleton_mem_nhds`

English:
lemma compl_lattice_sdiff_singleton_mem_nhds
  given: (x : Complex)
  statement: (↑L.lattice \ {x})ᶜ in 𝓝 x
  proof: L.isOpen_compl_lattice_sdiff.mem_nhds (by simp)

@[deprecated (since := "2026-06-03")]
alias compl_lattice_diff_singleton_mem_nhds := compl_lattice_sdiff_singleton_mem_nhds

中文:
引理 compl_lattice_sdiff_singleton_mem_nhds
  条件: (x : 复形)
  结论: (↑L.lattice \ {x})ᶜ in 𝓝 x
  证明: L.isOpen_compl_lattice_sdiff.mem_nhds (by simp)

@[deprecated (since := "2026-06-03")]
alias compl_lattice_diff_singleton_mem_nhds := compl_lattice_sdiff_singleton_mem_nhds

Depends on / 依赖: L.isOpen_compl_lattice_sdiff.mem_nhds, isOpen_compl_lattice_sdiff, mem_nhds
-/
lemma compl_lattice_sdiff_singleton_mem_nhds (x : Complex) : (↑L.lattice \ {x})ᶜ in 𝓝 x :=
  L.isOpen_compl_lattice_sdiff.mem_nhds (by simp)

@[deprecated (since := "2026-06-03")]
alias compl_lattice_diff_singleton_mem_nhds := compl_lattice_sdiff_singleton_mem_nhds

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ProperSpace L.lattice
  body: .of_isClosed L.isClosed_lattice

中文:
实例 :
  签名: 真空间 L.lattice
  定义体: .of_isClosed L.isClosed_lattice

Depends on / 依赖: L.isClosed_lattice, isClosed_lattice, of_isClosed
-/
instance : ProperSpace L.lattice := .of_isClosed L.isClosed_lattice

/--
Definition of `latticeBasis` / `latticeBasis` 的定义

English:
definition latticeBasis
  signature: : Basis (Fin 2) Int L.lattice
  body: (Basis.span (v := ![L.ω₁, L.ω₂]) (L.indep.restrict_scalars' _)).map
    (.ofEq _ _ (by simp [lattice, Set.pair_comm L.ω₂ L.ω₁]))

中文:
定义 latticeBasis
  签名: : 基 (有限集 2) 整数 L.lattice
  定义体: (Basis.span (v := ![L.ω₁, L.ω₂]) (L.indep.restrict_scalars' _)).map
    (.ofEq _ _ (by simp [lattice, Set.pair_comm L.ω₂ L.ω₁]))

Depends on / 依赖: Basis.span, L.indep.restrict_scalars, Set.pair_comm, lattice, pair_comm, restrict_scalars
-/
def latticeBasis : Basis (Fin 2) Int L.lattice :=
  (Basis.span (v := ![L.ω₁, L.ω₂]) (L.indep.restrict_scalars' _)).map
    (.ofEq _ _ (by simp [lattice, Set.pair_comm L.ω₂ L.ω₁]))

/--
lemma `latticeBasis_zero` / 引理 `latticeBasis_zero`

English:
lemma latticeBasis_zero
  statement: L.latticeBasis 0 = L.ω₁
  proof: by simp [latticeBasis]

中文:
引理 latticeBasis_zero
  结论: L.latticeBasis 0 = L.ω₁
  证明: by simp [latticeBasis]
-/
@[simp] lemma latticeBasis_zero : L.latticeBasis 0 = L.ω₁ := by simp [latticeBasis]
/--
lemma `latticeBasis_one` / 引理 `latticeBasis_one`

English:
lemma latticeBasis_one
  statement: L.latticeBasis 1 = L.ω₂
  proof: by simp [latticeBasis]

中文:
引理 latticeBasis_one
  结论: L.latticeBasis 1 = L.ω₂
  证明: by simp [latticeBasis]
-/
@[simp] lemma latticeBasis_one : L.latticeBasis 1 = L.ω₂ := by simp [latticeBasis]

/--
lemma `finrank_lattice` / 引理 `finrank_lattice`

English:
lemma finrank_lattice
  statement: finrank Int L.lattice = 2
  proof: finrank_eq_card_basis L.latticeBasis

中文:
引理 finrank_lattice
  结论: finrank 整数 L.lattice = 2
  证明: finrank_eq_card_basis L.latticeBasis
-/
@[simp] lemma finrank_lattice : finrank Int L.lattice = 2 := finrank_eq_card_basis L.latticeBasis

/--
Definition of `latticeEquivProd` / `latticeEquivProd` 的定义

English:
definition latticeEquivProd
  signature: : L.lattice ≃ₗ[Int] Int × Int
  body: L.latticeBasis.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _ ≪≫ₗ .finTwoArrow Int Int

中文:
定义 latticeEquivProd
  签名: : L.lattice ≃ₗ[整数] 整数 × 整数
  定义体: L.latticeBasis.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _ ≪≫ₗ .finTwoArrow Int Int

Depends on / 依赖: Finsupp, Finsupp.linearEquivFunOnFinite, L.latticeBasis.repr, finTwoArrow, latticeBasis, linearEquivFunOnFinite
-/
def latticeEquivProd : L.lattice ≃ₗ[Int] Int × Int :=
  L.latticeBasis.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _ ≪≫ₗ .finTwoArrow Int Int

/--
lemma `latticeEquiv_symm_apply` / 引理 `latticeEquiv_symm_apply`

English:
lemma latticeEquiv_symm_apply
  given: (x : Int × Int)
  proof: by
  simp [latticeEquivProd, Finsupp.linearCombination]

中文:
引理 latticeEquiv_symm_apply
  条件: (x : 整数 × 整数)
  证明: by
  simp [latticeEquivProd, Finsupp.linearCombination]

Depends on / 依赖: Finsupp, Finsupp.linearCombination, latticeEquivProd, linearCombination
-/
lemma latticeEquiv_symm_apply (x : Int × Int) :
    (L.latticeEquivProd.symm x).1 = x.1 * L.ω₁ + x.2 * L.ω₂ := by
  simp [latticeEquivProd, Finsupp.linearCombination]

/--
lemma `hasSumLocallyUniformly_aux` / 引理 `hasSumLocallyUniformly_aux`

English:
lemma hasSumLocallyUniformly_aux
  statement: (f : L.lattice -> Complex -> Complex)
  proof: by
  rw [hasSumLocallyUniformly_iff_tendstoLocallyUniformly]; rw [tendstoLocallyUniformly_iff_filter]
  intro x
  obtain ⟨r, hr, hr'⟩ : exists r, 0 < r ∧ 𝓝 x <= 𝓟 (Metric.ball 0 r) :=
    ⟨‖x‖ + 1, by positivity, Filter.le_principal_iff.mpr (Metric.isOpen_ball.mem_nhds (by simp))⟩
  refine .mono_rig

中文:
引理 hasSumLocallyUniformly_aux
  结论: (f : L.lattice -> 复形 -> 复形)
  证明: by
  rw [hasSumLocallyUniformly_iff_tendstoLocallyUniformly]; rw [tendstoLocallyUniformly_iff_filter]
  intro x
  obtain ⟨r, hr, hr'⟩ : exists r, 0 < r ∧ 𝓝 x <= 𝓟 (Metric.ball 0 r) :=
    ⟨‖x‖ + 1, by positivity, Filter.le_principal_iff.mpr (Metric.isOpen_ball.mem_nhds (by simp))⟩
  refine .mono_rig

Depends on / 依赖: Filter, Filter.le_principal_iff.mpr, Metric, Metric.ball, Metric.isOpen_ball.mem_nhds, eventually_atTop, eventually_atTop.mp, hasSumLocallyUniformly_iff_tendstoLocallyUniformly, isCompact_iff_finite, isCompact_iff_finite.mp, isOpen_ball, le_principal_iff, mem_nhds, mono_right, tendstoLocallyUniformly_iff_filter, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, tendstoUniformlyOn_tsum_of_cofinite_eventually
-/
lemma hasSumLocallyUniformly_aux (f : L.lattice -> Complex -> Complex)
    (u : Real -> L.lattice -> Real) (hu : forall r > 0, Summable (u r))
    (hf : forall r > 0, forallᶠ R in atTop, forall x, ‖x‖ < r -> forall l : L.lattice, ‖l.1‖ = R -> ‖f l x‖ <= u r l) :
    HasSumLocallyUniformly f (∑' j, f j ·) := by
  rw [hasSumLocallyUniformly_iff_tendstoLocallyUniformly]; rw [tendstoLocallyUniformly_iff_filter]
  intro x
  obtain ⟨r, hr, hr'⟩ : exists r, 0 < r ∧ 𝓝 x <= 𝓟 (Metric.ball 0 r) :=
    ⟨‖x‖ + 1, by positivity, Filter.le_principal_iff.mpr (Metric.isOpen_ball.mem_nhds (by simp))⟩
  refine .mono_right ?_ hr'
  rw [← tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]
  refine tendstoUniformlyOn_tsum_of_cofinite_eventually (hu r hr) ?_
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hf r hr)
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) R)).subset ?_
  intros l hl
  obtain ⟨s, hs, hs'⟩ : exists x, ‖x‖ < r ∧ u r l < ‖f l x‖ := by simpa using hl
  simp only [Metric.mem_closedBall, dist_zero_right]
  contrapose! hs'
  exact hR _ hs'.le _ hs _ rfl

-- Only the asymptotics matter and `10` is just a convenient constant to pick.
/--
lemma `weierstrassP_bound` / 引理 `weierstrassP_bound`

English:
lemma weierstrassP_bound
  given: (r : Real) (hr : 0 < r) (s : Complex) (hs : ‖s‖ < r) (l : Complex) (h : 2 * r <= ‖l‖)
  proof: by
  have : s != ↑l := by rintro rfl; linarith
  have : 0 < ‖l‖ := by linarith
  calc
    _ = ‖(↑l ^ 2 - (s - ↑l) ^ 2) / ((s - ↑l) ^ 2 * ↑l ^ 2)‖ := by
      rw [div_sub_div]; rw [one_mul]; rw [mul_one]
      · simpa [sub_eq_zero]
      · simpa
    _ = ‖l ^ 2 - (s - l) ^ 2‖ / (‖s - l‖ ^ 2 * ‖l‖ ^ 2)

中文:
引理 weierstrassP_bound
  条件: (r : 实数) (hr : 0 < r) (s : 复形) (hs : ‖s‖ < r) (l : 复形) (h : 2 * r <= ‖l‖)
  证明: by
  have : s != ↑l := by rintro rfl; linarith
  have : 0 < ‖l‖ := by linarith
  calc
    _ = ‖(↑l ^ 2 - (s - ↑l) ^ 2) / ((s - ↑l) ^ 2 * ↑l ^ 2)‖ := by
      rw [div_sub_div]; rw [one_mul]; rw [mul_one]
      · simpa [sub_eq_zero]
      · simpa
    _ = ‖l ^ 2 - (s - l) ^ 2‖ / (‖s - l‖ ^ 2 * ‖l‖ ^ 2)

Depends on / 依赖: div_sub_div, mul_one, norm_sub_norm_le, norm_sub_rev, one_mul, sq_sub_sq, sub_ad, sub_eq_zero
-/
lemma weierstrassP_bound (r : Real) (hr : 0 < r) (s : Complex) (hs : ‖s‖ < r) (l : Complex) (h : 2 * r <= ‖l‖) :
    ‖1 / (s - l) ^ 2 - 1 / l ^ 2‖ <= 10 * r * ‖l‖ ^ (-3 : Real) := by
  have : s != ↑l := by rintro rfl; linarith
  have : 0 < ‖l‖ := by linarith
  calc
    _ = ‖(↑l ^ 2 - (s - ↑l) ^ 2) / ((s - ↑l) ^ 2 * ↑l ^ 2)‖ := by
      rw [div_sub_div]; rw [one_mul]; rw [mul_one]
      · simpa [sub_eq_zero]
      · simpa
    _ = ‖l ^ 2 - (s - l) ^ 2‖ / (‖s - l‖ ^ 2 * ‖l‖ ^ 2) := by simp
    _ <= ‖l ^ 2 - (s - l) ^ 2‖ / ((‖l‖ / 2) ^ 2 * ‖l‖ ^ 2) := by
      gcongr
      rw [norm_sub_rev]
      exact .trans (by linarith) (norm_sub_norm_le l s)
    _ = ‖s * (2 * l - s)‖ / (‖l‖ ^ 4 / 4) := by
      congr 1
      · rw [sq_sub_sq]; simp [← sub_add, two_mul, sub_add_eq_add_sub]
      · ring
    _ = (‖s‖ * ‖2 * l - s‖) / (‖l‖ ^ 4 / 4) := by simp
    _ = (4 * ‖s‖ * ‖2 * l - s‖) / ‖l‖ ^ 4 := by field
    _ <= (4 * r * (2.5 * ‖l‖)) / ‖l‖ ^ 4 := by
      gcongr (4 * ?_ * ?_) / ‖l‖ ^ 4
      refine (norm_sub_le _ _).trans ?_
      simp only [Complex.norm_mul, Complex.norm_ofNat]
      linarith
    _ = 10 * r / ‖l‖ ^ 3 := by field
    _ = _ := by norm_cast

section weierstrassPExcept

/--
Definition of `weierstrassPExcept` / `weierstrassPExcept` 的定义

English:
definition weierstrassPExcept
  signature: (l₀ : Complex) (z : Complex)
  body: ∑' l : L.lattice, if l = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2)

@[inherit_doc weierstrassPExcept]
scoped notation3 "℘[" L:max " - " l₀ "]" => weierstrassPExcept L l₀

中文:
定义 weierstrassPExcept
  签名: (l₀ : 复形) (z : 复形)
  定义体: ∑' l : L.lattice, if l = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2)

@[inherit_doc weierstrassPExcept]
scoped notation3 "℘[" L:max " - " l₀ "]" => weierstrassPExcept L l₀

Depends on / 依赖: L.lattice, lattice
-/
def weierstrassPExcept (l₀ : Complex) (z : Complex) : Complex :=
  ∑' l : L.lattice, if l = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2)

@[inherit_doc weierstrassPExcept]
scoped notation3 "℘[" L:max " - " l₀ "]" => weierstrassPExcept L l₀

/--
lemma `hasSumLocallyUniformly_weierstrassPExcept` / 引理 `hasSumLocallyUniformly_weierstrassPExcept`

English:
lemma hasSumLocallyUniformly_weierstrassPExcept
  given: (l₀ : Complex)
  proof: by
  refine L.hasSumLocallyUniformly_aux (u := (10 * · * ‖·‖ ^ (-3 : Real))) _
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr =>
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simpa using! show 0 <= 10 * r * (‖↑l‖ ^ 3)⁻

中文:
引理 hasSumLocallyUniformly_weierstrassPExcept
  条件: (l₀ : 复形)
  证明: by
  refine L.hasSumLocallyUniformly_aux (u := (10 * · * ‖·‖ ^ (-3 : Real))) _
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr =>
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simpa using! show 0 <= 10 * r * (‖↑l‖ ^ 3)⁻

Depends on / 依赖: Filter, Filter.eventually_atTop.mpr, L.hasSumLocallyUniformly_aux, ZLattice, ZLattice.summable_norm_rpow, eventually_atTop, hasSumLocallyUniformly_aux, mul_left, split_ifs, summable_norm_rpow, weierstrassP_bound
-/
lemma hasSumLocallyUniformly_weierstrassPExcept (l₀ : Complex) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : Complex) => if l.1 = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2))
      ℘[L - l₀] := by
  refine L.hasSumLocallyUniformly_aux (u := (10 * · * ‖·‖ ^ (-3 : Real))) _
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr =>
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simpa using! show 0 <= 10 * r * (‖↑l‖ ^ 3)⁻¹ by positivity
  · exact weierstrassP_bound r hr s hs l h

/--
lemma `hasSum_weierstrassPExcept` / 引理 `hasSum_weierstrassPExcept`

English:
lemma hasSum_weierstrassPExcept
  given: (l₀ : Complex) (z : Complex)
  proof: (L.hasSumLocallyUniformly_weierstrassPExcept l₀).hasSum

中文:
引理 hasSum_weierstrassPExcept
  条件: (l₀ : 复形) (z : 复形)
  证明: (L.hasSumLocallyUniformly_weierstrassPExcept l₀).hasSum

Depends on / 依赖: L.hasSumLocallyUniformly_weierstrassPExcept, hasSum, hasSumLocallyUniformly_weierstrassPExcept
-/
lemma hasSum_weierstrassPExcept (l₀ : Complex) (z : Complex) :
    HasSum (fun l : L.lattice => if l = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2))
      (℘[L - l₀] z) :=
  (L.hasSumLocallyUniformly_weierstrassPExcept l₀).hasSum

/--
lemma `differentiableOn_weierstrassPExcept` / 引理 `differentiableOn_weierstrassPExcept`

English:
lemma differentiableOn_weierstrassPExcept
  given: (l₀ : Complex)
  proof: by
  refine (L.hasSumLocallyUniformly_weierstrassPExcept l₀).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun s => .fun_sum fun i hi => ?_) L.isOpen_compl_lattice_sdiff
  split_ifs
  · simp
  · exact .sub (.div (by fun_prop) (by fun_prop) (by aesop (add simp sub_eq_zero))) (by fun_prop)

中文:
引理 differentiableOn_weierstrassPExcept
  条件: (l₀ : 复形)
  证明: by
  refine (L.hasSumLocallyUniformly_weierstrassPExcept l₀).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun s => .fun_sum fun i hi => ?_) L.isOpen_compl_lattice_sdiff
  split_ifs
  · simp
  · exact .sub (.div (by fun_prop) (by fun_prop) (by aesop (add simp sub_eq_zero))) (by fun_prop)

Depends on / 依赖: L.hasSumLocallyUniformly_weierstrassPExcept, L.isOpen_compl_lattice_sdiff, differentiableOn, fun_prop, fun_sum, hasSumLocallyUniformlyOn, hasSumLocallyUniformlyOn.differentiableOn, hasSumLocallyUniformly_weierstrassPExcept, isOpen_compl_lattice_sdiff, of_forall, split_ifs, sub_eq_zero
-/
lemma differentiableOn_weierstrassPExcept (l₀ : Complex) :
    DifferentiableOn Complex ℘[L - l₀] (L.lattice \ {l₀})ᶜ := by
  refine (L.hasSumLocallyUniformly_weierstrassPExcept l₀).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun s => .fun_sum fun i hi => ?_) L.isOpen_compl_lattice_sdiff
  split_ifs
  · simp
  · exact .sub (.div (by fun_prop) (by fun_prop) (by aesop (add simp sub_eq_zero))) (by fun_prop)

/--
lemma `weierstrassPExcept_neg` / 引理 `weierstrassPExcept_neg`

English:
lemma weierstrassPExcept_neg
  given: (l₀ : Complex) (z : Complex)
  proof: by
  simp only [weierstrassPExcept]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  congr! 3 with l
  · simp [neg_eq_iff_eq_neg]
  simp
  ring

中文:
引理 weierstrassPExcept_neg
  条件: (l₀ : 复形) (z : 复形)
  证明: by
  simp only [weierstrassPExcept]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  congr! 3 with l
  · simp [neg_eq_iff_eq_neg]
  simp
  ring

Depends on / 依赖: Equiv.neg, L.lattice, lattice, neg_eq_iff_eq_neg, tsum_eq, weierstrassPExcept
-/
lemma weierstrassPExcept_neg (l₀ : Complex) (z : Complex) :
    ℘[L - l₀] (-z) = ℘[L - -l₀] z := by
  simp only [weierstrassPExcept]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  congr! 3 with l
  · simp [neg_eq_iff_eq_neg]
  simp
  ring

/--
lemma `weierstrassPExcept_zero` / 引理 `weierstrassPExcept_zero`

English:
lemma weierstrassPExcept_zero
  given: (l₀ : Complex)
  proof: by simp [weierstrassPExcept]

中文:
引理 weierstrassPExcept_zero
  条件: (l₀ : 复形)
  证明: by simp [weierstrassPExcept]
-/
@[simp] lemma weierstrassPExcept_zero (l₀ : Complex) :
    ℘[L - l₀] 0 = 0 := by simp [weierstrassPExcept]

end weierstrassPExcept

section weierstrassP

/--
Definition of `weierstrassP` / `weierstrassP` 的定义

English:
definition weierstrassP
  signature: (z : Complex)
  body: ∑' l : L.lattice, (1 / (z - l) ^ 2 - 1 / l ^ 2)

@[inherit_doc weierstrassP] scoped notation3 "℘[" L "]" => weierstrassP L

中文:
定义 weierstrassP
  签名: (z : 复形)
  定义体: ∑' l : L.lattice, (1 / (z - l) ^ 2 - 1 / l ^ 2)

@[inherit_doc weierstrassP] scoped notation3 "℘[" L "]" => weierstrassP L

Depends on / 依赖: L.lattice, lattice
-/
def weierstrassP (z : Complex) : Complex := ∑' l : L.lattice, (1 / (z - l) ^ 2 - 1 / l ^ 2)

@[inherit_doc weierstrassP] scoped notation3 "℘[" L "]" => weierstrassP L

/--
lemma `weierstrassPExcept_add` / 引理 `weierstrassPExcept_add`

English:
lemma weierstrassPExcept_add
  given: (l₀ : L.lattice) (z : Complex)
  proof: by
  trans ℘[L - l₀] z + ∑' i : L.lattice, if i = l₀.1 then (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) else 0
  · simp
  rw [weierstrassPExcept]; rw [← Summable.tsum_add]
  · congr with w; split_ifs <;> simp only [zero_add, add_zero, *]
  · exact ⟨_, L.hasSum_weierstrassPExcept _ _⟩
  · exact summable_of_h

中文:
引理 weierstrassPExcept_add
  条件: (l₀ : L.lattice) (z : 复形)
  证明: by
  trans ℘[L - l₀] z + ∑' i : L.lattice, if i = l₀.1 then (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) else 0
  · simp
  rw [weierstrassPExcept]; rw [← Summable.tsum_add]
  · congr with w; split_ifs <;> simp only [zero_add, add_zero, *]
  · exact ⟨_, L.hasSum_weierstrassPExcept _ _⟩
  · exact summable_of_h

Depends on / 依赖: L.hasSum_weierstrassPExcept, L.lattice, Set.finite_singleton, Summable, Summable.tsum_add, add_zero, finite_singleton, hasSum_weierstrassPExcept, lattice, split_ifs, subset, summable_of_hasFiniteSupport, tsum_add, weierstrassPExcept, zero_add
-/
lemma weierstrassPExcept_add (l₀ : L.lattice) (z : Complex) :
    ℘[L - l₀] z + (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) = ℘[L] z := by
  trans ℘[L - l₀] z + ∑' i : L.lattice, if i = l₀.1 then (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) else 0
  · simp
  rw [weierstrassPExcept]; rw [← Summable.tsum_add]
  · congr with w; split_ifs <;> simp only [zero_add, add_zero, *]
  · exact ⟨_, L.hasSum_weierstrassPExcept _ _⟩
  · exact summable_of_hasFiniteSupport ((Set.finite_singleton l₀).subset (by simp))

/--
lemma `weierstrassPExcept_def` / 引理 `weierstrassPExcept_def`

English:
lemma weierstrassPExcept_def
  given: (l₀ : L.lattice) (z : Complex)
  proof: by
  rw [← L.weierstrassPExcept_add l₀]
  abel

中文:
引理 weierstrassPExcept_def
  条件: (l₀ : L.lattice) (z : 复形)
  证明: by
  rw [← L.weierstrassPExcept_add l₀]
  abel

Depends on / 依赖: L.weierstrassPExcept_add, weierstrassPExcept_add
-/
lemma weierstrassPExcept_def (l₀ : L.lattice) (z : Complex) :
    ℘[L - l₀] z = ℘[L] z + (1 / l₀.1 ^ 2 - 1 / (z - l₀.1) ^ 2) := by
  rw [← L.weierstrassPExcept_add l₀]
  abel

/--
lemma `weierstrassPExcept_of_notMem` / 引理 `weierstrassPExcept_of_notMem`

English:
lemma weierstrassPExcept_of_notMem
  given: (l₀ : Complex) (hl : l₀ ∉ L.lattice)
  proof: by
  delta weierstrassPExcept weierstrassP
  congr! 3 with z l
  have : l.1 != l₀ := by rintro rfl; simp at hl
  simp [this]

中文:
引理 weierstrassPExcept_of_notMem
  条件: (l₀ : 复形) (hl : l₀ ∉ L.lattice)
  证明: by
  delta weierstrassPExcept weierstrassP
  congr! 3 with z l
  have : l.1 != l₀ := by rintro rfl; simp at hl
  simp [this]

Depends on / 依赖: weierstrassP, weierstrassPExcept
-/
lemma weierstrassPExcept_of_notMem (l₀ : Complex) (hl : l₀ ∉ L.lattice) :
    ℘[L - l₀] = ℘[L] := by
  delta weierstrassPExcept weierstrassP
  congr! 3 with z l
  have : l.1 != l₀ := by rintro rfl; simp at hl
  simp [this]

/--
lemma `hasSumLocallyUniformly_weierstrassP` / 引理 `hasSumLocallyUniformly_weierstrassP`

English:
lemma hasSumLocallyUniformly_weierstrassP
  proof: by
  convert! L.hasSumLocallyUniformly_weierstrassPExcept (L.ω₁ / 2) using 3 with l
  · rw [if_neg]; exact fun e => L.ω₁_div_two_notMem_lattice (e ▸ l.2)
  · rw [L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]

中文:
引理 hasSumLocallyUniformly_weierstrassP
  证明: by
  convert! L.hasSumLocallyUniformly_weierstrassPExcept (L.ω₁ / 2) using 3 with l
  · rw [if_neg]; exact fun e => L.ω₁_div_two_notMem_lattice (e ▸ l.2)
  · rw [L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]

Depends on / 依赖: L.hasSumLocallyUniformly_weierstrassPExcept, L.weierstrassPExcept_of_notMem, convert, hasSumLocallyUniformly_weierstrassPExcept, if_neg, weierstrassPExcept_of_notMem
-/
lemma hasSumLocallyUniformly_weierstrassP :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : Complex) => 1 / (z - ↑l) ^ 2 - 1 / l ^ 2) ℘[L] := by
  convert! L.hasSumLocallyUniformly_weierstrassPExcept (L.ω₁ / 2) using 3 with l
  · rw [if_neg]; exact fun e => L.ω₁_div_two_notMem_lattice (e ▸ l.2)
  · rw [L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]

/--
lemma `hasSum_weierstrassP` / 引理 `hasSum_weierstrassP`

English:
lemma hasSum_weierstrassP
  given: (z : Complex)
  proof: L.hasSumLocallyUniformly_weierstrassP.hasSum

中文:
引理 hasSum_weierstrassP
  条件: (z : 复形)
  证明: L.hasSumLocallyUniformly_weierstrassP.hasSum

Depends on / 依赖: L.hasSumLocallyUniformly_weierstrassP.hasSum, hasSum, hasSumLocallyUniformly_weierstrassP
-/
lemma hasSum_weierstrassP (z : Complex) :
    HasSum (fun l : L.lattice => (1 / (z - l) ^ 2 - 1 / l ^ 2)) (℘[L] z) :=
  L.hasSumLocallyUniformly_weierstrassP.hasSum

/--
lemma `differentiableOn_weierstrassP` / 引理 `differentiableOn_weierstrassP`

English:
lemma differentiableOn_weierstrassP
  proof: by
  rw [← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  convert! L.differentiableOn_weierstrassPExcept _
  simp [L.ω₁_div_two_notMem_lattice]

@[simp]

中文:
引理 differentiableOn_weierstrassP
  证明: by
  rw [← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  convert! L.differentiableOn_weierstrassPExcept _
  simp [L.ω₁_div_two_notMem_lattice]

@[simp]

Depends on / 依赖: L.differentiableOn_weierstrassPExcept, L.weierstrassPExcept_of_notMem, convert, differentiableOn_weierstrassPExcept, weierstrassPExcept_of_notMem
-/
lemma differentiableOn_weierstrassP :
    DifferentiableOn Complex ℘[L] L.latticeᶜ := by
  rw [← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  convert! L.differentiableOn_weierstrassPExcept _
  simp [L.ω₁_div_two_notMem_lattice]

@[simp]
/--
lemma `weierstrassP_neg` / 引理 `weierstrassP_neg`

English:
lemma weierstrassP_neg
  given: (z : Complex)
  statement: ℘[L] (-z) = ℘[L] z
  proof: by
  simp only [weierstrassP]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  congr with l
  simp
  ring

中文:
引理 weierstrassP_neg
  条件: (z : 复形)
  结论: ℘[L] (-z) = ℘[L] z
  证明: by
  simp only [weierstrassP]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  congr with l
  simp
  ring

Depends on / 依赖: Equiv.neg, L.lattice, lattice, tsum_eq, weierstrassP
-/
lemma weierstrassP_neg (z : Complex) : ℘[L] (-z) = ℘[L] z := by
  simp only [weierstrassP]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  congr with l
  simp
  ring

/--
lemma `not_continuousAt_weierstrassP` / 引理 `not_continuousAt_weierstrassP`

English:
lemma not_continuousAt_weierstrassP
  given: (x : Complex) (hx : x in L.lattice)
  statement: ¬ ContinuousAt ℘[L] x
  proof: by
  eta_expand
  simp_rw [← L.weierstrassPExcept_add ⟨x, hx⟩]
  intro H
  apply (NormedField.continuousAt_zpow (n := -2) (x := (0 : Complex))).not.mpr (by simp)
  simpa [Function.comp_def] using!
    (((H.sub ((L.differentiableOn_weierstrassPExcept x).differentiableAt
      (L.compl_lattice_sdiff_s

中文:
引理 not_continuousAt_weierstrassP
  条件: (x : 复形) (hx : x in L.lattice)
  结论: ¬ ContinuousAt ℘[L] x
  证明: by
  eta_expand
  simp_rw [← L.weierstrassPExcept_add ⟨x, hx⟩]
  intro H
  apply (NormedField.continuousAt_zpow (n := -2) (x := (0 : Complex))).not.mpr (by simp)
  simpa [Function.comp_def] using!
    (((H.sub ((L.differentiableOn_weierstrassPExcept x).differentiableAt
      (L.compl_lattice_sdiff_s

Depends on / 依赖: Function, Function.comp_def, H.sub, L.compl_lattice_sdiff_singleton_mem_nhds, L.differentiableOn_weierstrassPExcept, L.weierstrassPExcept_add, NormedField, NormedField.continuousAt_zpow, add_zero, comp_def, comp_of_eq, compl_lattice_sdiff_singleton_mem_nhds, continuousAt, continuousAt_zpow, continuous_const, continuous_const_add, differentiableAt, differentiableOn_weierstrassPExcept, eta_expand, not.mpr
-/
lemma not_continuousAt_weierstrassP (x : Complex) (hx : x in L.lattice) : ¬ ContinuousAt ℘[L] x := by
  eta_expand
  simp_rw [← L.weierstrassPExcept_add ⟨x, hx⟩]
  intro H
  apply (NormedField.continuousAt_zpow (n := -2) (x := (0 : Complex))).not.mpr (by simp)
  simpa [Function.comp_def] using!
    (((H.sub ((L.differentiableOn_weierstrassPExcept x).differentiableAt
      (L.compl_lattice_sdiff_singleton_mem_nhds x)).continuousAt).add
      (continuous_const (y := 1 / x ^ 2)).continuousAt).comp_of_eq
      (continuous_const_add x).continuousAt (add_zero _) :)

end weierstrassP

section derivWeierstrassPExcept

/--
Definition of `derivWeierstrassPExcept` / `derivWeierstrassPExcept` 的定义

English:
definition derivWeierstrassPExcept
  signature: (l₀ : Complex) (z : Complex)
  body: ∑' l : L.lattice, if l.1 = l₀ then 0 else -2 / (z - l) ^ 3

@[inherit_doc derivWeierstrassPExcept]
scoped notation3 "℘'[" L:max " - " l₀ "]" => derivWeierstrassPExcept L l₀

中文:
定义 derivWeierstrassPExcept
  签名: (l₀ : 复形) (z : 复形)
  定义体: ∑' l : L.lattice, if l.1 = l₀ then 0 else -2 / (z - l) ^ 3

@[inherit_doc derivWeierstrassPExcept]
scoped notation3 "℘'[" L:max " - " l₀ "]" => derivWeierstrassPExcept L l₀

Depends on / 依赖: L.lattice, lattice
-/
def derivWeierstrassPExcept (l₀ : Complex) (z : Complex) : Complex :=
  ∑' l : L.lattice, if l.1 = l₀ then 0 else -2 / (z - l) ^ 3

@[inherit_doc derivWeierstrassPExcept]
scoped notation3 "℘'[" L:max " - " l₀ "]" => derivWeierstrassPExcept L l₀

/--
lemma `hasSumLocallyUniformly_derivWeierstrassPExcept` / 引理 `hasSumLocallyUniformly_derivWeierstrassPExcept`

English:
lemma hasSumLocallyUniformly_derivWeierstrassPExcept
  given: (l₀ : Complex)
  proof: by
  refine L.hasSumLocallyUniformly_aux (u := fun _ => (16 * ‖·‖ ^ (-3 : Real))) _
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr =>
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simp
  have : s != ↑l := by rintro rfl

中文:
引理 hasSumLocallyUniformly_derivWeierstrassPExcept
  条件: (l₀ : 复形)
  证明: by
  refine L.hasSumLocallyUniformly_aux (u := fun _ => (16 * ‖·‖ ^ (-3 : Real))) _
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr =>
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simp
  have : s != ↑l := by rintro rfl

Depends on / 依赖: Complex.norm_div, Complex.norm_ofNat, Filter, Filter.eventually_atTop.mpr, L.hasSumLocallyUniformly_aux, Real.rpow_neg, ZLattice, ZLattice.summable_norm_rpow, div_eq_mul_inv, eventually_atTop, hasSumLocallyUniformly_aux, mul_left, norm_div, norm_neg, norm_ofNat, norm_pow, rpow_neg, split_ifs, summable_norm_rpow
-/
lemma hasSumLocallyUniformly_derivWeierstrassPExcept (l₀ : Complex) :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : Complex) => if l.1 = l₀ then 0 else -2 / (z - l) ^ 3)
      ℘'[L - l₀] := by
  refine L.hasSumLocallyUniformly_aux (u := fun _ => (16 * ‖·‖ ^ (-3 : Real))) _
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr =>
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simp
  have : s != ↑l := by rintro rfl; exfalso; linarith
  have : l != 0 := by rintro rfl; simp_all; linarith
  simp only [Complex.norm_div, norm_neg, Complex.norm_ofNat, norm_pow]
  rw [Real.rpow_neg (by positivity)]; rw [← div_eq_mul_inv]; rw [div_le_div_iff₀]; rw [norm_sub_rev]
  · refine LE.le.trans_eq (b := 2 * (2 * ‖l - s‖) ^ 3) ?_ (by ring)
    norm_cast
    gcongr
    refine le_trans ?_ (mul_le_mul le_rfl (norm_sub_norm_le _ _) (by linarith) (by linarith))
    norm_cast at *
    linarith
  · exact pow_pos (by simpa [sub_eq_zero]) _
  · exact Real.rpow_pos_of_pos (by simpa) _

/--
lemma `hasSum_derivWeierstrassPExcept` / 引理 `hasSum_derivWeierstrassPExcept`

English:
lemma hasSum_derivWeierstrassPExcept
  given: (l₀ : Complex) (z : Complex)
  proof: (L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀).tendstoLocallyUniformlyOn.tendsto_at
    (Set.mem_univ z)

中文:
引理 hasSum_derivWeierstrassPExcept
  条件: (l₀ : 复形) (z : 复形)
  证明: (L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀).tendstoLocallyUniformlyOn.tendsto_at
    (Set.mem_univ z)

Depends on / 依赖: L.hasSumLocallyUniformly_derivWeierstrassPExcept, Set.mem_univ, hasSumLocallyUniformly_derivWeierstrassPExcept, mem_univ, tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn.tendsto_at, tendsto_at
-/
lemma hasSum_derivWeierstrassPExcept (l₀ : Complex) (z : Complex) :
    HasSum (fun l : L.lattice => if l.1 = l₀ then 0 else -2 / (z - l) ^ 3) (℘'[L - l₀] z) :=
  (L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀).tendstoLocallyUniformlyOn.tendsto_at
    (Set.mem_univ z)

/--
lemma `differentiableOn_derivWeierstrassPExcept` / 引理 `differentiableOn_derivWeierstrassPExcept`

English:
lemma differentiableOn_derivWeierstrassPExcept
  given: (l₀ : Complex)
  proof: by
  refine L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀
.tendstoLocallyUniformlyOn.differentiableOn
      (.of_forall fun s => .fun_sum fun i hi => ?_) L.isOpen_compl_lattice_sdiff
  split_ifs
  · simp
  refine .div (by fun_prop) (by fun_prop) fun x hx => ?_
  have : x != i := by rintro rfl;

中文:
引理 differentiableOn_derivWeierstrassPExcept
  条件: (l₀ : 复形)
  证明: by
  refine L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀
.tendstoLocallyUniformlyOn.differentiableOn
      (.of_forall fun s => .fun_sum fun i hi => ?_) L.isOpen_compl_lattice_sdiff
  split_ifs
  · simp
  refine .div (by fun_prop) (by fun_prop) fun x hx => ?_
  have : x != i := by rintro rfl;

Depends on / 依赖: L.hasSumLocallyUniformly_derivWeierstrassPExcept, L.isOpen_compl_lattice_sdiff, differentiableOn, fun_prop, fun_sum, hasSumLocallyUniformly_derivWeierstrassPExcept, isOpen_compl_lattice_sdiff, of_forall, split_ifs, sub_eq_zero, tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn.differentiableOn
-/
lemma differentiableOn_derivWeierstrassPExcept (l₀ : Complex) :
    DifferentiableOn Complex ℘'[L - l₀] (L.lattice \ {l₀})ᶜ := by
  refine L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀
.tendstoLocallyUniformlyOn.differentiableOn
      (.of_forall fun s => .fun_sum fun i hi => ?_) L.isOpen_compl_lattice_sdiff
  split_ifs
  · simp
  refine .div (by fun_prop) (by fun_prop) fun x hx => ?_
  have : x != i := by rintro rfl; simp_all
  simpa [sub_eq_zero]

/--
lemma `eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept` / 引理 `eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept`

English:
lemma eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept
  given: (l₀ : Complex)
  proof: by
  refine ((L.hasSumLocallyUniformly_weierstrassPExcept l₀).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s => ?_) L.isOpen_compl_lattice_sdiff).unique ?_
  · refine .fun_sum fun i hi => ?_
    split_ifs
    · simp
    refine .sub (.div (by fun_prop) (by fun_prop) fun x hx => ?_) (by fun_pro

中文:
引理 eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept
  条件: (l₀ : 复形)
  证明: by
  refine ((L.hasSumLocallyUniformly_weierstrassPExcept l₀).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s => ?_) L.isOpen_compl_lattice_sdiff).unique ?_
  · refine .fun_sum fun i hi => ?_
    split_ifs
    · simp
    refine .sub (.div (by fun_prop) (by fun_prop) fun x hx => ?_) (by fun_pro

Depends on / 依赖: Function, Function.comp_apply, L.hasSumLocallyUniformly_derivWeierstrassPExcept, L.hasSumLocallyUniformly_weierstrassPExcept, L.isOpen_compl_lattice_sdiff, comp_apply, deriv_fun, fun_prop, fun_sum, hasSumLocallyUniformly_derivWeierstrassPExcept, hasSumLocallyUniformly_weierstrassPExcept, isOpen_compl_lattice_sdiff, of_forall, split_ifs, sub_eq_zero, tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn.congr, tendstoLocallyUniformlyOn.deriv, unique
-/
lemma eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept (l₀ : Complex) :
    Set.EqOn (deriv ℘[L - l₀]) ℘'[L - l₀] (L.lattice \ {l₀})ᶜ := by
  refine ((L.hasSumLocallyUniformly_weierstrassPExcept l₀).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s => ?_) L.isOpen_compl_lattice_sdiff).unique ?_
  · refine .fun_sum fun i hi => ?_
    split_ifs
    · simp
    refine .sub (.div (by fun_prop) (by fun_prop) fun x hx => ?_) (by fun_prop)
    have : x != i := by rintro rfl; simp_all
    simpa [sub_eq_zero]
  · refine (L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀).tendstoLocallyUniformlyOn.congr ?_
    intro s l hl
    simp only [Function.comp_apply]
    rw [deriv_fun_sum]
    · congr with x
      split_ifs with hl₁
      · simp
      have hl₁ : l - x != 0 := fun e => hl₁ (by
        obtain rfl := sub_eq_zero.mp e
        simpa using hl)
      rw [deriv_fun_sub (.fun_div (by fun_prop) (by fun_prop) (by simpa)) (by fun_prop)]; rw [deriv_const]
      simp_rw [← zpow_natCast, one_div, ← zpow_neg, Nat.cast_ofNat]
      rw [deriv_comp_sub_const (f := (· ^ (-2 : Int)))]; rw [deriv_zpow]
      simp
      field_simp
    · intros x hxs
      split_ifs with hl₁
      · simp
      have hl₁ : l - x != 0 := fun e => hl₁ (by
        obtain rfl := sub_eq_zero.mp e
        simpa using hl)
      exact .sub (.div (by fun_prop) (by fun_prop) (by simpa)) (by fun_prop)

/--
lemma `deriv_weierstrassPExcept_same` / 引理 `deriv_weierstrassPExcept_same`

English:
lemma deriv_weierstrassPExcept_same
  given: (l : Complex)
  statement: deriv ℘[L - l] l = ℘'[L - l] l
  proof: L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept l (x := l) (by simp)

中文:
引理 deriv_weierstrassPExcept_same
  条件: (l : 复形)
  结论: deriv ℘[L - l] l = ℘'[L - l] l
  证明: L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept l (x := l) (by simp)
-/
@[simp] lemma deriv_weierstrassPExcept_same (l : Complex) : deriv ℘[L - l] l = ℘'[L - l] l :=
  L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept l (x := l) (by simp)

/--
lemma `derivWeierstrassPExcept_neg` / 引理 `derivWeierstrassPExcept_neg`

English:
lemma derivWeierstrassPExcept_neg
  given: (l₀ : Complex) (z : Complex)
  proof: by
  simp only [derivWeierstrassPExcept]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sub_neg_eq_add, neg_add_eq_sub,
    ← div_neg, ← tsum_neg, apply_ite, neg_zero]
  congr! 3 with l
  · simp [neg_eq_iff_eq_neg]
  ring

中文:
引理 derivWeierstrassPExcept_neg
  条件: (l₀ : 复形) (z : 复形)
  证明: by
  simp only [derivWeierstrassPExcept]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sub_neg_eq_add, neg_add_eq_sub,
    ← div_neg, ← tsum_neg, apply_ite, neg_zero]
  congr! 3 with l
  · simp [neg_eq_iff_eq_neg]
  ring

Depends on / 依赖: Equiv.neg, Equiv.neg_apply, L.lattice, NegMemClass, NegMemClass.coe_neg, apply_ite, coe_neg, derivWeierstrassPExcept, div_neg, lattice, neg_add_eq_sub, neg_apply, neg_eq_iff_eq_neg, neg_zero, sub_neg_eq_add, tsum_eq, tsum_neg
-/
lemma derivWeierstrassPExcept_neg (l₀ : Complex) (z : Complex) :
    ℘'[L - l₀] (-z) = - ℘'[L - (-l₀)] z := by
  simp only [derivWeierstrassPExcept]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sub_neg_eq_add, neg_add_eq_sub,
    ← div_neg, ← tsum_neg, apply_ite, neg_zero]
  congr! 3 with l
  · simp [neg_eq_iff_eq_neg]
  ring

/--
lemma `derivWeierstrassPExcept_zero_zero` / 引理 `derivWeierstrassPExcept_zero_zero`

English:
lemma derivWeierstrassPExcept_zero_zero
  statement: ℘'[L - 0] 0 = 0
  proof: by
  simpa [CharZero.eq_neg_self_iff] using L.derivWeierstrassPExcept_neg 0 0

中文:
引理 derivWeierstrassPExcept_zero_zero
  结论: ℘'[L - 0] 0 = 0
  证明: by
  simpa [CharZero.eq_neg_self_iff] using L.derivWeierstrassPExcept_neg 0 0
-/
@[simp] lemma derivWeierstrassPExcept_zero_zero : ℘'[L - 0] 0 = 0 := by
  simpa [CharZero.eq_neg_self_iff] using L.derivWeierstrassPExcept_neg 0 0

end derivWeierstrassPExcept

section Periodicity

/--
lemma `derivWeierstrassPExcept_add_coe` / 引理 `derivWeierstrassPExcept_add_coe`

English:
lemma derivWeierstrassPExcept_add_coe
  given: (l₀ : Complex) (z : Complex) (l : L.lattice)
  proof: by
  simp only [derivWeierstrassPExcept]
  rw [← (Equiv.addRight l).tsum_eq]
  simp only [Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub, eq_sub_iff_add_eq]

中文:
引理 derivWeierstrassPExcept_add_coe
  条件: (l₀ : 复形) (z : 复形) (l : L.lattice)
  证明: by
  simp only [derivWeierstrassPExcept]
  rw [← (Equiv.addRight l).tsum_eq]
  simp only [Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub, eq_sub_iff_add_eq]

Depends on / 依赖: Equiv.addRight, Equiv.coe_addRight, Submodule, Submodule.coe_add, addRight, add_sub_add_right_eq_sub, coe_add, coe_addRight, derivWeierstrassPExcept, eq_sub_iff_add_eq, tsum_eq
-/
lemma derivWeierstrassPExcept_add_coe (l₀ : Complex) (z : Complex) (l : L.lattice) :
    ℘'[L - l₀] (z + l) = ℘'[L - (l₀ - l)] z := by
  simp only [derivWeierstrassPExcept]
  rw [← (Equiv.addRight l).tsum_eq]
  simp only [Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub, eq_sub_iff_add_eq]

-- Subsumed by `weierstrassP_add_coe`
/--
lemma `weierstrassPExcept_add_coe_aux` / 引理 `weierstrassPExcept_add_coe_aux`

English:
lemma weierstrassPExcept_add_coe_aux
  proof: by
  apply IsOpen.eqOn_of_deriv_eq (𝕜 := Complex) L.isOpen_compl_lattice_sdiff
    ?_ ?_ ?_ ?_ (x := -(l / 2)) ?_ ?_
  · refine (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) ?_).2
    exact .mono sdiff_le (countable_of_Lindelof_of_discrete (X := L.lattice))
  · refine (L.differentiableOn

中文:
引理 weierstrassPExcept_add_coe_aux
  证明: by
  apply IsOpen.eqOn_of_deriv_eq (𝕜 := Complex) L.isOpen_compl_lattice_sdiff
    ?_ ?_ ?_ ?_ (x := -(l / 2)) ?_ ?_
  · refine (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) ?_).2
    exact .mono sdiff_le (countable_of_Lindelof_of_discrete (X := L.lattice))
  · refine (L.differentiableOn
-/
private lemma weierstrassPExcept_add_coe_aux
    (l₀ : Complex) (hl₀ : l₀ in L.lattice) (l : L.lattice) (hl : l.1 / 2 ∉ L.lattice) :
    Set.EqOn (℘[L - l₀] <| · + l) (℘[L - (l₀ - l)] · + (1 / l₀ ^ 2 - 1 / (l₀ - ↑l) ^ 2))
      (L.lattice \ {l₀ - l})ᶜ := by
  apply IsOpen.eqOn_of_deriv_eq (𝕜 := Complex) L.isOpen_compl_lattice_sdiff
    ?_ ?_ ?_ ?_ (x := -(l / 2)) ?_ ?_
  · refine (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) ?_).2
    exact .mono sdiff_le (countable_of_Lindelof_of_discrete (X := L.lattice))
  · refine (L.differentiableOn_weierstrassPExcept l₀).comp (f := (· + l.1)) (by fun_prop) ?_
    rintro x h₁ ⟨h₂ : x + l in _, h₃ : x + l != l₀⟩
    exact h₁ ⟨by simpa using sub_mem h₂ l.2, by rintro rfl; simp at h₃⟩
  · refine .add (L.differentiableOn_weierstrassPExcept _) (by simp)
  · intro x hx
    simp only [deriv_add_const', deriv_comp_add_const]
    rw [L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept]; rw [L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept]; rw [L.derivWeierstrassPExcept_add_coe]
    · simpa using hx
    · simp only [Set.mem_compl_iff, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff, not_and,
        Decidable.not_not, eq_sub_iff_add_eq] at hx ⊢
      exact fun H => hx (by simpa using sub_mem H l.2)
  · simp [hl]
  · rw [L.weierstrassPExcept_neg, L.weierstrassPExcept_def ⟨l₀, hl₀⟩,
      L.weierstrassPExcept_def ⟨_, neg_mem (sub_mem hl₀ l.2)⟩, add_assoc]
    congr 2 <;> ring

-- Subsumed by `weierstrassP_add_coe`
/--
lemma `weierstrassP_add_coe_aux` / 引理 `weierstrassP_add_coe_aux`

English:
lemma weierstrassP_add_coe_aux
  given: (z : Complex) (l : L.lattice) (hl : l.1 / 2 ∉ L.lattice)
  proof: by
  have hl0 : l != 0 := by rintro rfl; simp at hl
  by_cases hz : z in L.lattice
  · have := L.weierstrassPExcept_add_coe_aux (z + l) (add_mem hz l.2) l hl (x := z) (by simp)
    dsimp at this
    rw [← L.weierstrassPExcept_add ⟨z + l]; rw [add_mem hz l.2⟩]; rw [this]; rw [← L.weierstrassPExcept_a

中文:
引理 weierstrassP_add_coe_aux
  条件: (z : 复形) (l : L.lattice) (hl : l.1 / 2 ∉ L.lattice)
  证明: by
  have hl0 : l != 0 := by rintro rfl; simp at hl
  by_cases hz : z in L.lattice
  · have := L.weierstrassPExcept_add_coe_aux (z + l) (add_mem hz l.2) l hl (x := z) (by simp)
    dsimp at this
    rw [← L.weierstrassPExcept_add ⟨z + l]; rw [add_mem hz l.2⟩]; rw [this]; rw [← L.weierstrassPExcept_a
-/
private lemma weierstrassP_add_coe_aux (z : Complex) (l : L.lattice) (hl : l.1 / 2 ∉ L.lattice) :
    ℘[L] (z + l) = ℘[L] z := by
  have hl0 : l != 0 := by rintro rfl; simp at hl
  by_cases hz : z in L.lattice
  · have := L.weierstrassPExcept_add_coe_aux (z + l) (add_mem hz l.2) l hl (x := z) (by simp)
    dsimp at this
    rw [← L.weierstrassPExcept_add ⟨z + l]; rw [add_mem hz l.2⟩]; rw [this]; rw [← L.weierstrassPExcept_add ⟨z]; rw [hz⟩]
    simp
    ring
  · have := L.weierstrassPExcept_add_coe_aux 0 (zero_mem _) l hl (x := z) (by simp [hz])
    simp only [zero_sub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
      even_two, Even.neg_pow, one_div] at this
    rw [← L.weierstrassPExcept_add 0]; rw [Submodule.coe_zero]; rw [this]; rw [← L.weierstrassPExcept_add (-l)]
    simp
    ring

@[simp]
/--
lemma `weierstrassP_add_coe` / 引理 `weierstrassP_add_coe`

English:
lemma weierstrassP_add_coe
  given: (z : Complex) (l : L.lattice)
  statement: ℘[L] (z + l) = ℘[L] z
  proof: by
  let G : AddSubgroup Complex :=
    { carrier := { z | (℘[L] <| · + z) = ℘[L] }
      add_mem' := by simp_all [funext_iff, ← add_assoc]
      zero_mem' := by simp
      neg_mem' {z} hz := funext fun i => by conv_lhs => rw [← hz]; simp }
  have : L.lattice <= G.toIntSubmodule := by
    rw [lattic

中文:
引理 weierstrassP_add_coe
  条件: (z : 复形) (l : L.lattice)
  结论: ℘[L] (z + l) = ℘[L] z
  证明: by
  let G : AddSubgroup Complex :=
    { carrier := { z | (℘[L] <| · + z) = ℘[L] }
      add_mem' := by simp_all [funext_iff, ← add_assoc]
      zero_mem' := by simp
      neg_mem' {z} hz := funext fun i => by conv_lhs => rw [← hz]; simp }
  have : L.lattice <= G.toIntSubmodule := by
    rw [lattic

Depends on / 依赖: AddSubgroup, G.toIntSubmodule, L.lattice, L.weierstrassP_add_coe_aux, Submodule, Submodule.span_le, add_assoc, add_mem, carrier, conv_lhs, funext_iff, lattice, neg_mem, span_le, toIntSubmodule, weierstrassP_add_coe_aux, zero_mem
-/
lemma weierstrassP_add_coe (z : Complex) (l : L.lattice) : ℘[L] (z + l) = ℘[L] z := by
  let G : AddSubgroup Complex :=
    { carrier := { z | (℘[L] <| · + z) = ℘[L] }
      add_mem' := by simp_all [funext_iff, ← add_assoc]
      zero_mem' := by simp
      neg_mem' {z} hz := funext fun i => by conv_lhs => rw [← hz]; simp }
  have : L.lattice <= G.toIntSubmodule := by
    rw [lattice]; rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · ext i
      exact L.weierstrassP_add_coe_aux _ ⟨_, L.ω₁_mem_lattice⟩ L.ω₁_div_two_notMem_lattice
    · ext i
      exact L.weierstrassP_add_coe_aux _ ⟨_, L.ω₂_mem_lattice⟩ L.ω₂_div_two_notMem_lattice
  exact congr_fun (this l.2) _

/--
lemma `periodic_weierstrassP` / 引理 `periodic_weierstrassP`

English:
lemma periodic_weierstrassP
  given: (l : L.lattice)
  statement: ℘[L].Periodic l
  proof: (L.weierstrassP_add_coe · l)

@[simp]

中文:
引理 periodic_weierstrassP
  条件: (l : L.lattice)
  结论: ℘[L].周期 l
  证明: (L.weierstrassP_add_coe · l)

@[simp]

Depends on / 依赖: L.weierstrassP_add_coe, weierstrassP_add_coe
-/
lemma periodic_weierstrassP (l : L.lattice) : ℘[L].Periodic l :=
  (L.weierstrassP_add_coe · l)

@[simp]
/--
lemma `weierstrassP_zero` / 引理 `weierstrassP_zero`

English:
lemma weierstrassP_zero
  statement: ℘[L] 0 = 0
  proof: by simp [weierstrassP]

@[simp]

中文:
引理 weierstrassP_zero
  结论: ℘[L] 0 = 0
  证明: by simp [weierstrassP]

@[simp]

Depends on / 依赖: weierstrassP
-/
lemma weierstrassP_zero : ℘[L] 0 = 0 := by simp [weierstrassP]

@[simp]
/--
lemma `weierstrassP_coe` / 引理 `weierstrassP_coe`

English:
lemma weierstrassP_coe
  given: (l : L.lattice)
  statement: ℘[L] l = 0
  proof: by
  rw [← zero_add l.1]; rw [L.weierstrassP_add_coe]; rw [L.weierstrassP_zero]

@[simp]

中文:
引理 weierstrassP_coe
  条件: (l : L.lattice)
  结论: ℘[L] l = 0
  证明: by
  rw [← zero_add l.1]; rw [L.weierstrassP_add_coe]; rw [L.weierstrassP_zero]

@[simp]

Depends on / 依赖: L.weierstrassP_add_coe, L.weierstrassP_zero, weierstrassP_add_coe, weierstrassP_zero, zero_add
-/
lemma weierstrassP_coe (l : L.lattice) : ℘[L] l = 0 := by
  rw [← zero_add l.1]; rw [L.weierstrassP_add_coe]; rw [L.weierstrassP_zero]

@[simp]
/--
lemma `weierstrassP_sub_coe` / 引理 `weierstrassP_sub_coe`

English:
lemma weierstrassP_sub_coe
  given: (z : Complex) (l : L.lattice)
  statement: ℘[L] (z - l) = ℘[L] z
  proof: by
  rw [← L.weierstrassP_add_coe _ l]; rw [sub_add_cancel]

中文:
引理 weierstrassP_sub_coe
  条件: (z : 复形) (l : L.lattice)
  结论: ℘[L] (z - l) = ℘[L] z
  证明: by
  rw [← L.weierstrassP_add_coe _ l]; rw [sub_add_cancel]

Depends on / 依赖: L.weierstrassP_add_coe, sub_add_cancel, weierstrassP_add_coe
-/
lemma weierstrassP_sub_coe (z : Complex) (l : L.lattice) : ℘[L] (z - l) = ℘[L] z := by
  rw [← L.weierstrassP_add_coe _ l]; rw [sub_add_cancel]

end Periodicity

section derivWeierstrassP

/--
Definition of `derivWeierstrassP` / `derivWeierstrassP` 的定义

English:
definition derivWeierstrassP
  signature: (z : Complex)
  body: - ∑' l : L.lattice, 2 / (z - l) ^ 3

@[inherit_doc weierstrassP] scoped notation3 "℘'[" L "]" => derivWeierstrassP L

中文:
定义 derivWeierstrassP
  签名: (z : 复形)
  定义体: - ∑' l : L.lattice, 2 / (z - l) ^ 3

@[inherit_doc weierstrassP] scoped notation3 "℘'[" L "]" => derivWeierstrassP L

Depends on / 依赖: L.lattice, lattice
-/
def derivWeierstrassP (z : Complex) : Complex := - ∑' l : L.lattice, 2 / (z - l) ^ 3

@[inherit_doc weierstrassP] scoped notation3 "℘'[" L "]" => derivWeierstrassP L

/--
lemma `derivWeierstrassPExcept_sub` / 引理 `derivWeierstrassPExcept_sub`

English:
lemma derivWeierstrassPExcept_sub
  given: (l₀ : L.lattice) (z : Complex)
  proof: by
  trans ℘'[L - l₀] z + ∑' i : L.lattice, if i.1 = l₀.1 then (- 2 / (z - l₀) ^ 3) else 0
  · simp [sub_eq_add_neg, neg_div]
  rw [derivWeierstrassP]; rw [derivWeierstrassPExcept]; rw [← Summable.tsum_add]; rw [← tsum_neg]
  · congr with w; split_ifs <;> simp only [zero_add, add_zero, *, neg_div]
 

中文:
引理 derivWeierstrassPExcept_sub
  条件: (l₀ : L.lattice) (z : 复形)
  证明: by
  trans ℘'[L - l₀] z + ∑' i : L.lattice, if i.1 = l₀.1 then (- 2 / (z - l₀) ^ 3) else 0
  · simp [sub_eq_add_neg, neg_div]
  rw [derivWeierstrassP]; rw [derivWeierstrassPExcept]; rw [← Summable.tsum_add]; rw [← tsum_neg]
  · congr with w; split_ifs <;> simp only [zero_add, add_zero, *, neg_div]
 

Depends on / 依赖: L.hasSum_derivWeierstrassPExcept, L.lattice, Set.finite_singleton, Summable, Summable.tsum_add, add_zero, derivWeierstrassP, derivWeierstrassPExcept, finite_singleton, hasSum_derivWeierstrassPExcept, lattice, neg_div, split_ifs, sub_eq_add_neg, subset, summable_of_hasFiniteSupport, tsum_add, tsum_neg, zero_add
-/
lemma derivWeierstrassPExcept_sub (l₀ : L.lattice) (z : Complex) :
    ℘'[L - l₀] z - 2 / (z - l₀) ^ 3 = ℘'[L] z := by
  trans ℘'[L - l₀] z + ∑' i : L.lattice, if i.1 = l₀.1 then (- 2 / (z - l₀) ^ 3) else 0
  · simp [sub_eq_add_neg, neg_div]
  rw [derivWeierstrassP]; rw [derivWeierstrassPExcept]; rw [← Summable.tsum_add]; rw [← tsum_neg]
  · congr with w; split_ifs <;> simp only [zero_add, add_zero, *, neg_div]
  · exact ⟨_, L.hasSum_derivWeierstrassPExcept _ _⟩
  · exact summable_of_hasFiniteSupport ((Set.finite_singleton l₀).subset (by simp))

/--
lemma `derivWeierstrassPExcept_def` / 引理 `derivWeierstrassPExcept_def`

English:
lemma derivWeierstrassPExcept_def
  given: (l₀ : L.lattice) (z : Complex)
  proof: by
  rw [← L.derivWeierstrassPExcept_sub l₀]; rw [sub_add_cancel]

中文:
引理 derivWeierstrassPExcept_def
  条件: (l₀ : L.lattice) (z : 复形)
  证明: by
  rw [← L.derivWeierstrassPExcept_sub l₀]; rw [sub_add_cancel]

Depends on / 依赖: L.derivWeierstrassPExcept_sub, derivWeierstrassPExcept_sub, sub_add_cancel
-/
lemma derivWeierstrassPExcept_def (l₀ : L.lattice) (z : Complex) :
    ℘'[L - l₀] z = ℘'[L] z + 2 / (z - l₀) ^ 3 := by
  rw [← L.derivWeierstrassPExcept_sub l₀]; rw [sub_add_cancel]

/--
lemma `derivWeierstrassPExcept_of_notMem` / 引理 `derivWeierstrassPExcept_of_notMem`

English:
lemma derivWeierstrassPExcept_of_notMem
  given: (l₀ : Complex) (hl : l₀ ∉ L.lattice)
  proof: by
  delta derivWeierstrassPExcept derivWeierstrassP
  simp_rw [← tsum_neg]
  congr! 3 with z l
  have : l.1 != l₀ := by rintro rfl; simp at hl
  simp [this, neg_div]

中文:
引理 derivWeierstrassPExcept_of_notMem
  条件: (l₀ : 复形) (hl : l₀ ∉ L.lattice)
  证明: by
  delta derivWeierstrassPExcept derivWeierstrassP
  simp_rw [← tsum_neg]
  congr! 3 with z l
  have : l.1 != l₀ := by rintro rfl; simp at hl
  simp [this, neg_div]

Depends on / 依赖: derivWeierstrassP, derivWeierstrassPExcept, neg_div, simp_rw, tsum_neg
-/
lemma derivWeierstrassPExcept_of_notMem (l₀ : Complex) (hl : l₀ ∉ L.lattice) :
    ℘'[L - l₀] = ℘'[L] := by
  delta derivWeierstrassPExcept derivWeierstrassP
  simp_rw [← tsum_neg]
  congr! 3 with z l
  have : l.1 != l₀ := by rintro rfl; simp at hl
  simp [this, neg_div]

/--
lemma `hasSumLocallyUniformly_derivWeierstrassP` / 引理 `hasSumLocallyUniformly_derivWeierstrassP`

English:
lemma hasSumLocallyUniformly_derivWeierstrassP
  proof: by
  convert! L.hasSumLocallyUniformly_derivWeierstrassPExcept (L.ω₁ / 2) using 3 with l z
  · rw [if_neg, neg_div]; exact fun e => L.ω₁_div_two_notMem_lattice (e ▸ l.2)
  · rw [L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]

中文:
引理 hasSumLocallyUniformly_derivWeierstrassP
  证明: by
  convert! L.hasSumLocallyUniformly_derivWeierstrassPExcept (L.ω₁ / 2) using 3 with l z
  · rw [if_neg, neg_div]; exact fun e => L.ω₁_div_two_notMem_lattice (e ▸ l.2)
  · rw [L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]

Depends on / 依赖: L.derivWeierstrassPExcept_of_notMem, L.hasSumLocallyUniformly_derivWeierstrassPExcept, convert, derivWeierstrassPExcept_of_notMem, hasSumLocallyUniformly_derivWeierstrassPExcept, if_neg, neg_div
-/
lemma hasSumLocallyUniformly_derivWeierstrassP :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : Complex) => - 2 / (z - l) ^ 3) ℘'[L] := by
  convert! L.hasSumLocallyUniformly_derivWeierstrassPExcept (L.ω₁ / 2) using 3 with l z
  · rw [if_neg, neg_div]; exact fun e => L.ω₁_div_two_notMem_lattice (e ▸ l.2)
  · rw [L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]

/--
lemma `hasSum_derivWeierstrassP` / 引理 `hasSum_derivWeierstrassP`

English:
lemma hasSum_derivWeierstrassP
  given: (z : Complex)
  proof: L.hasSumLocallyUniformly_derivWeierstrassP.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)

中文:
引理 hasSum_derivWeierstrassP
  条件: (z : 复形)
  证明: L.hasSumLocallyUniformly_derivWeierstrassP.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)

Depends on / 依赖: L.hasSumLocallyUniformly_derivWeierstrassP.tendstoLocallyUniformlyOn.tendsto_at, Set.mem_univ, hasSumLocallyUniformly_derivWeierstrassP, mem_univ, tendstoLocallyUniformlyOn, tendsto_at
-/
lemma hasSum_derivWeierstrassP (z : Complex) :
    HasSum (fun l : L.lattice => - 2 / (z - l) ^ 3) (℘'[L] z) :=
  L.hasSumLocallyUniformly_derivWeierstrassP.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)

/--
lemma `differentiableOn_derivWeierstrassP` / 引理 `differentiableOn_derivWeierstrassP`

English:
lemma differentiableOn_derivWeierstrassP
  proof: by
  rw [← L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  convert! L.differentiableOn_derivWeierstrassPExcept _
  simp [L.ω₁_div_two_notMem_lattice]

@[simp]

中文:
引理 differentiableOn_derivWeierstrassP
  证明: by
  rw [← L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  convert! L.differentiableOn_derivWeierstrassPExcept _
  simp [L.ω₁_div_two_notMem_lattice]

@[simp]

Depends on / 依赖: L.derivWeierstrassPExcept_of_notMem, L.differentiableOn_derivWeierstrassPExcept, convert, derivWeierstrassPExcept_of_notMem, differentiableOn_derivWeierstrassPExcept
-/
lemma differentiableOn_derivWeierstrassP :
    DifferentiableOn Complex ℘'[L] L.latticeᶜ := by
  rw [← L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  convert! L.differentiableOn_derivWeierstrassPExcept _
  simp [L.ω₁_div_two_notMem_lattice]

@[simp]
/--
lemma `derivWeierstrassP_neg` / 引理 `derivWeierstrassP_neg`

English:
lemma derivWeierstrassP_neg
  given: (z : Complex)
  statement: ℘'[L] (-z) = - ℘'[L] z
  proof: by
  simp only [derivWeierstrassP]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sub_neg_eq_add, neg_add_eq_sub, neg_neg,
    ← div_neg, ← tsum_neg]
  congr! with l
  ring

@[simp]

中文:
引理 derivWeierstrassP_neg
  条件: (z : 复形)
  结论: ℘'[L] (-z) = - ℘'[L] z
  证明: by
  simp only [derivWeierstrassP]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sub_neg_eq_add, neg_add_eq_sub, neg_neg,
    ← div_neg, ← tsum_neg]
  congr! with l
  ring

@[simp]

Depends on / 依赖: Equiv.neg, Equiv.neg_apply, L.lattice, NegMemClass, NegMemClass.coe_neg, coe_neg, derivWeierstrassP, div_neg, lattice, neg_add_eq_sub, neg_apply, neg_neg, sub_neg_eq_add, tsum_eq, tsum_neg
-/
lemma derivWeierstrassP_neg (z : Complex) : ℘'[L] (-z) = - ℘'[L] z := by
  simp only [derivWeierstrassP]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sub_neg_eq_add, neg_add_eq_sub, neg_neg,
    ← div_neg, ← tsum_neg]
  congr! with l
  ring

@[simp]
/--
lemma `derivWeierstrassP_add_coe` / 引理 `derivWeierstrassP_add_coe`

English:
lemma derivWeierstrassP_add_coe
  given: (z : Complex) (l : L.lattice)
  proof: by
  simp only [derivWeierstrassP]
  rw [← (Equiv.addRight l).tsum_eq]
  simp only [← tsum_neg, ← div_neg, Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub]

中文:
引理 derivWeierstrassP_add_coe
  条件: (z : 复形) (l : L.lattice)
  证明: by
  simp only [derivWeierstrassP]
  rw [← (Equiv.addRight l).tsum_eq]
  simp only [← tsum_neg, ← div_neg, Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub]

Depends on / 依赖: Equiv.addRight, Equiv.coe_addRight, Submodule, Submodule.coe_add, addRight, add_sub_add_right_eq_sub, coe_add, coe_addRight, derivWeierstrassP, div_neg, tsum_eq, tsum_neg
-/
lemma derivWeierstrassP_add_coe (z : Complex) (l : L.lattice) :
    ℘'[L] (z + l) = ℘'[L] z := by
  simp only [derivWeierstrassP]
  rw [← (Equiv.addRight l).tsum_eq]
  simp only [← tsum_neg, ← div_neg, Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub]

/--
lemma `periodic_derivWeierstrassP` / 引理 `periodic_derivWeierstrassP`

English:
lemma periodic_derivWeierstrassP
  given: (l : L.lattice)
  statement: ℘'[L].Periodic l
  proof: (L.derivWeierstrassP_add_coe · l)

@[simp]

中文:
引理 periodic_derivWeierstrassP
  条件: (l : L.lattice)
  结论: ℘'[L].周期 l
  证明: (L.derivWeierstrassP_add_coe · l)

@[simp]

Depends on / 依赖: L.derivWeierstrassP_add_coe, derivWeierstrassP_add_coe
-/
lemma periodic_derivWeierstrassP (l : L.lattice) : ℘'[L].Periodic l :=
  (L.derivWeierstrassP_add_coe · l)

@[simp]
/--
lemma `derivWeierstrassP_zero` / 引理 `derivWeierstrassP_zero`

English:
lemma derivWeierstrassP_zero
  statement: ℘'[L] 0 = 0
  proof: by
  rw [← CharZero.eq_neg_self_iff]; rw [← L.derivWeierstrassP_neg]; rw [neg_zero]

@[simp]

中文:
引理 derivWeierstrassP_zero
  结论: ℘'[L] 0 = 0
  证明: by
  rw [← CharZero.eq_neg_self_iff]; rw [← L.derivWeierstrassP_neg]; rw [neg_zero]

@[simp]

Depends on / 依赖: CharZero, CharZero.eq_neg_self_iff, L.derivWeierstrassP_neg, derivWeierstrassP_neg, eq_neg_self_iff, neg_zero
-/
lemma derivWeierstrassP_zero : ℘'[L] 0 = 0 := by
  rw [← CharZero.eq_neg_self_iff]; rw [← L.derivWeierstrassP_neg]; rw [neg_zero]

@[simp]
/--
lemma `derivWeierstrassP_coe` / 引理 `derivWeierstrassP_coe`

English:
lemma derivWeierstrassP_coe
  given: (l : L.lattice)
  statement: ℘'[L] l = 0
  proof: by
  rw [← zero_add l.1]; rw [L.derivWeierstrassP_add_coe]; rw [L.derivWeierstrassP_zero]

@[simp]

中文:
引理 derivWeierstrassP_coe
  条件: (l : L.lattice)
  结论: ℘'[L] l = 0
  证明: by
  rw [← zero_add l.1]; rw [L.derivWeierstrassP_add_coe]; rw [L.derivWeierstrassP_zero]

@[simp]

Depends on / 依赖: L.derivWeierstrassP_add_coe, L.derivWeierstrassP_zero, derivWeierstrassP_add_coe, derivWeierstrassP_zero, zero_add
-/
lemma derivWeierstrassP_coe (l : L.lattice) : ℘'[L] l = 0 := by
  rw [← zero_add l.1]; rw [L.derivWeierstrassP_add_coe]; rw [L.derivWeierstrassP_zero]

@[simp]
/--
lemma `derivWeierstrassP_sub_coe` / 引理 `derivWeierstrassP_sub_coe`

English:
lemma derivWeierstrassP_sub_coe
  given: (z : Complex) (l : L.lattice)
  proof: by
  rw [← L.derivWeierstrassP_add_coe _ l]; rw [sub_add_cancel]

中文:
引理 derivWeierstrassP_sub_coe
  条件: (z : 复形) (l : L.lattice)
  证明: by
  rw [← L.derivWeierstrassP_add_coe _ l]; rw [sub_add_cancel]

Depends on / 依赖: L.derivWeierstrassP_add_coe, derivWeierstrassP_add_coe, sub_add_cancel
-/
lemma derivWeierstrassP_sub_coe (z : Complex) (l : L.lattice) :
    ℘'[L] (z - l) = ℘'[L] z := by
  rw [← L.derivWeierstrassP_add_coe _ l]; rw [sub_add_cancel]

/--
lemma `deriv_weierstrassP` / 引理 `deriv_weierstrassP`

English:
lemma deriv_weierstrassP
  statement: deriv ℘[L] = ℘'[L]
  proof: by
  ext x
  by_cases hx : x in L.lattice
  · rw [deriv_zero_of_not_differentiableAt, L.derivWeierstrassP_coe ⟨x, hx⟩]
    exact fun H => L.not_continuousAt_weierstrassP x hx H.continuousAt
  · rw [← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice,
      ← L.derivWeierstrassPExcept_of_n

中文:
引理 deriv_weierstrassP
  结论: deriv ℘[L] = ℘'[L]
  证明: by
  ext x
  by_cases hx : x in L.lattice
  · rw [deriv_zero_of_not_differentiableAt, L.derivWeierstrassP_coe ⟨x, hx⟩]
    exact fun H => L.not_continuousAt_weierstrassP x hx H.continuousAt
  · rw [← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice,
      ← L.derivWeierstrassPExcept_of_n
-/
@[simp] lemma deriv_weierstrassP : deriv ℘[L] = ℘'[L] := by
  ext x
  by_cases hx : x in L.lattice
  · rw [deriv_zero_of_not_differentiableAt, L.derivWeierstrassP_coe ⟨x, hx⟩]
    exact fun H => L.not_continuousAt_weierstrassP x hx H.continuousAt
  · rw [← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice,
      ← L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice,
      L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept (L.ω₁ / 2) (x := x) (by simp [hx])]

end derivWeierstrassP

section AnalyticWeierstrassPExcept

/--
Definition of `sumInvPow` / `sumInvPow` 的定义

English:
definition sumInvPow
  signature: (x : Complex) (r : Nat)
  body: ∑' l : L.lattice, ((l - x) ^ r)⁻¹

中文:
定义 sumInvPow
  签名: (x : 复形) (r : 自然数)
  定义体: ∑' l : L.lattice, ((l - x) ^ r)⁻¹

Depends on / 依赖: L.lattice, lattice
-/
def sumInvPow (x : Complex) (r : Nat) : Complex := ∑' l : L.lattice, ((l - x) ^ r)⁻¹

/--
lemma `hasSum_sumInvPow` / 引理 `hasSum_sumInvPow`

English:
lemma hasSum_sumInvPow
  given: (x : Complex) {r : Nat} (hr : 2 < r)
  proof: by
  refine Summable.hasSum (.of_norm_bounded (ZLattice.summable_norm_sub_zpow _
    (-r) (by simpa) x) fun l => ?_)
  rw [← zpow_natCast]; rw [← zpow_neg]; rw [← norm_zpow]

中文:
引理 hasSum_sumInvPow
  条件: (x : 复形) {r : 自然数} (hr : 2 < r)
  证明: by
  refine Summable.hasSum (.of_norm_bounded (ZLattice.summable_norm_sub_zpow _
    (-r) (by simpa) x) fun l => ?_)
  rw [← zpow_natCast]; rw [← zpow_neg]; rw [← norm_zpow]

Depends on / 依赖: Summable, Summable.hasSum, ZLattice, ZLattice.summable_norm_sub_zpow, hasSum, norm_zpow, of_norm_bounded, summable_norm_sub_zpow, zpow_natCast, zpow_neg
-/
lemma hasSum_sumInvPow (x : Complex) {r : Nat} (hr : 2 < r) :
    HasSum (fun l : L.lattice => ((l - x) ^ r)⁻¹) (L.sumInvPow x r) := by
  refine Summable.hasSum (.of_norm_bounded (ZLattice.summable_norm_sub_zpow _
    (-r) (by simpa) x) fun l => ?_)
  rw [← zpow_natCast]; rw [← zpow_neg]; rw [← norm_zpow]

/--
Definition of `weierstrassPExceptSummand` / `weierstrassPExceptSummand` 的定义

English:
definition weierstrassPExceptSummand
  signature: (l₀ x : Complex) (i : Nat) (l : L.lattice)
  body: if l.1 = l₀ then 0 else ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : Int) - i.casesOn (l.1 ^ (-2 : Int)) 0)

中文:
定义 weierstrassPExceptSummand
  签名: (l₀ x : 复形) (i : 自然数) (l : L.lattice)
  定义体: if l.1 = l₀ then 0 else ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : Int) - i.casesOn (l.1 ^ (-2 : Int)) 0)

Depends on / 依赖: casesOn, i.casesOn
-/
def weierstrassPExceptSummand (l₀ x : Complex) (i : Nat) (l : L.lattice) : Complex :=
  if l.1 = l₀ then 0 else ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : Int) - i.casesOn (l.1 ^ (-2 : Int)) 0)

/--
Definition of `weierstrassPExceptSeries` / `weierstrassPExceptSeries` 的定义

English:
definition weierstrassPExceptSeries
  signature: (l₀ x : Complex)
  body: letI := Classical.propDecidable
  .ofScalars _ fun i => if i = 0 then (℘[L - l₀] x) else (i + 1) *
    (L.sumInvPow x (i + 2) - if l₀ in L.lattice then ((l₀ - x) ^ (i + 2))⁻¹ else 0)

中文:
定义 weierstrassPExceptSeries
  签名: (l₀ x : 复形)
  定义体: letI := Classical.propDecidable
  .ofScalars _ fun i => if i = 0 then (℘[L - l₀] x) else (i + 1) *
    (L.sumInvPow x (i + 2) - if l₀ in L.lattice then ((l₀ - x) ^ (i + 2))⁻¹ else 0)

Depends on / 依赖: Classical, Classical.propDecidable, L.lattice, L.sumInvPow, lattice, ofScalars, propDecidable, sumInvPow
-/
def weierstrassPExceptSeries (l₀ x : Complex) : FormalMultilinearSeries Complex Complex Complex :=
  letI := Classical.propDecidable
  .ofScalars _ fun i => if i = 0 then (℘[L - l₀] x) else (i + 1) *
    (L.sumInvPow x (i + 2) - if l₀ in L.lattice then ((l₀ - x) ^ (i + 2))⁻¹ else 0)

/--
lemma `coeff_weierstrassPExceptSeries` / 引理 `coeff_weierstrassPExceptSeries`

English:
lemma coeff_weierstrassPExceptSeries
  given: (l₀ x : Complex) (i : Nat)
  proof: by
  delta weierstrassPExceptSummand weierstrassPExceptSeries
  cases i with
  | zero => simp [weierstrassPExcept, sub_sq_comm x, zpow_ofNat]
  | succ i =>
    split_ifs with hl₀
    · trans (i + 2) * (L.sumInvPow x (i + 3) -
        ∑' l : L.lattice, if l = ⟨l₀, hl₀⟩ then (l₀ - x) ^ (-↑(i + 3) : In

中文:
引理 coeff_weierstrassPExceptSeries
  条件: (l₀ x : 复形) (i : 自然数)
  证明: by
  delta weierstrassPExceptSummand weierstrassPExceptSeries
  cases i with
  | zero => simp [weierstrassPExcept, sub_sq_comm x, zpow_ofNat]
  | succ i =>
    split_ifs with hl₀
    · trans (i + 2) * (L.sumInvPow x (i + 3) -
        ∑' l : L.lattice, if l = ⟨l₀, hl₀⟩ then (l₀ - x) ^ (-↑(i + 3) : In

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.coeff_ofScalars, L.lattice, L.sumInvPow, add_assoc, coeff_ofScalars, hasSum_sumInvPow, lattice, one_add_one_eq_two, split_ifs, sub_sq_comm, sumInvPow, summable, summable.tsum_sub, tsum_ite_eq, tsum_mul_left, tsum_sub, weierstrassPExcept, weierstrassPExceptSeries, weierstrassPExceptSummand
-/
lemma coeff_weierstrassPExceptSeries (l₀ x : Complex) (i : Nat) :
    (L.weierstrassPExceptSeries l₀ x).coeff i =
      ∑' l : L.lattice, L.weierstrassPExceptSummand l₀ x i l := by
  delta weierstrassPExceptSummand weierstrassPExceptSeries
  cases i with
  | zero => simp [weierstrassPExcept, sub_sq_comm x, zpow_ofNat]
  | succ i =>
    split_ifs with hl₀
    · trans (i + 2) * (L.sumInvPow x (i + 3) -
        ∑' l : L.lattice, if l = ⟨l₀, hl₀⟩ then (l₀ - x) ^ (-↑(i + 3) : Int) else 0)
      · rw [FormalMultilinearSeries.coeff_ofScalars, tsum_ite_eq, zpow_neg, zpow_natCast]
        simp [add_assoc, one_add_one_eq_two]
      · rw [sumInvPow, ← (hasSum_sumInvPow _ _ (by linarith)).summable.tsum_sub, ← tsum_mul_left]
        · simp_rw [Subtype.ext_iff, zpow_neg]
          congr with l
          split_ifs with e
          · simp only [e, zpow_natCast, sub_self, mul_zero]
          · dsimp; norm_cast; ring
        · exact summable_of_hasFiniteSupport ((Set.finite_singleton ⟨l₀, hl₀⟩).subset (by simp))
    · have h₁ (l : L.lattice) : l.1 != l₀ := fun e => hl₀ (e ▸ l.2)
      simp [h₁, tsum_mul_left, sumInvPow, add_assoc,
        one_add_one_eq_two, ← zpow_natCast, -neg_add_rev]

set_option backward.isDefEq.respectTransparency.types false in
-- We should be able to skip this computation via some general complex-analytic machinery but
-- they are missing at the moment.
-- Consider refactoring once we have developed more of the missing API.
/--
lemma `summable_weierstrassPExceptSummand` / 引理 `summable_weierstrassPExceptSummand`

English:
lemma summable_weierstrassPExceptSummand
  statement: (l₀ z x : Complex)
  proof: by
  -- We first find a `κ > 1`,
  -- such that the ball centered at `x` with radius `κ * ‖z - x‖` does not touch `L`.
  obtain ⟨κ, hκ, hκ'⟩ : exists κ : Real, 1 < κ ∧ forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ * κ < ‖l - x‖ := by
    obtain ⟨κ, hκ, hκ'⟩ := Metric.isOpen_iff.mp ((continuous_mul_cons

中文:
引理 summable_weierstrassPExceptSummand
  结论: (l₀ z x : 复形)
  证明: by
  -- We first find a `κ > 1`,
  -- such that the ball centered at `x` with radius `κ * ‖z - x‖` does not touch `L`.
  obtain ⟨κ, hκ, hκ'⟩ : exists κ : Real, 1 < κ ∧ forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ * κ < ‖l - x‖ := by
    obtain ⟨κ, hκ, hκ'⟩ := Metric.isOpen_iff.mp ((continuous_mul_cons
-/
lemma summable_weierstrassPExceptSummand (l₀ z x : Complex)
    (hx : forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ < ‖l - x‖) :
    Summable (Function.uncurry fun b c => L.weierstrassPExceptSummand l₀ x b c * (z - x) ^ b) := by
  -- We first find a `κ > 1`,
  -- such that the ball centered at `x` with radius `κ * ‖z - x‖` does not touch `L`.
  obtain ⟨κ, hκ, hκ'⟩ : exists κ : Real, 1 < κ ∧ forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ * κ < ‖l - x‖ := by
    obtain ⟨κ, hκ, hκ'⟩ := Metric.isOpen_iff.mp ((continuous_mul_const ‖z - x‖).isOpen_preimage _
      (isClosedMap_dist x _
      (L.isClosed_of_subset_lattice (Set.sdiff_subset (t := {l₀})))).upperClosure.isOpen_compl) 1
      (by simpa [Complex.dist_eq, @forall_comm Real, norm_sub_rev x] using hx)
    refine ⟨κ / 2 + 1, by simpa, fun l hl => ?_⟩
    have : forall l in L.lattice, l != l₀ -> (κ / 2 + 1) * ‖z - x‖ < dist x l := by
      simpa using @hκ' (κ / 2 + 1) (by simp [div_lt_iff₀, abs_eq_self.mpr hκ.le, hκ])
    simpa only [Complex.dist_eq, norm_sub_rev x, mul_comm] using this _ l.2 hl
  -- We single out the degree zero term via this equiv.
  let e : Nat × L.lattice ≃ L.lattice oplus (Nat × L.lattice) :=
    (Equiv.prodCongrLeft fun _ => (Denumerable.eqv (Option Nat)).symm).trans optionProdEquiv
  rw [← e.symm.summable_iff]
  apply Summable.sum
  · -- for the degree zero term, this is the usual summability of the definition of `℘`.
    simpa [weierstrassPExceptSummand, e, Function.comp_def, Function.uncurry, sub_sq_comm x,
      Denumerable.eqv] using! (L.hasSum_weierstrassPExcept l₀ x).summable
  · -- for the remaining terms, we bound it by `(i + 2) κ⁻ⁱ * ‖l - x‖⁻³ * ‖z - x‖`.
    dsimp [e, Function.comp_def, Function.uncurry_def, Denumerable.eqv, weierstrassPExceptSummand]
    have H₁ : Summable fun i : Nat => ((i + 2) * κ ^ (-i : Int)) := by
      have : |κ⁻¹| < 1 := by grind [abs_inv, inv_lt_one_iff₀]
      simpa [mul_comm] using ((Real.hasFPowerSeriesOnBall_ofScalars_mul_add_zero 1 2).hasSum
        (y := κ⁻¹) (by simpa [enorm_eq_nnnorm])).summable
    have H₂ : Summable fun l : L.lattice => ‖l - x‖ ^ (-3 : Int) * ‖z - x‖ :=
      (ZLattice.summable_norm_sub_zpow _ _ (by simp) _).mul_right _
    refine (H₁.mul_of_nonneg H₂ (by intro; positivity) (by intro; positivity)).of_norm_bounded ?_
    intro p
    split_ifs with hp
    · simp only [zero_mul, norm_zero, zpow_neg, zpow_natCast, Int.reduceNeg]; positivity
    have hpx : ‖p.2 - x‖ != 0 := fun h => by
      obtain rfl : p.2 = x := by simpa [sub_eq_zero] using h
      simpa [(norm_nonneg _).not_gt] using hx p.2 hp
    obtain rfl | hxz := eq_or_ne z x
    · simp
    calc
      _ = ‖(p.1 + 2 : Complex)‖ * ‖p.2 - x‖ ^ (-3 - p.1 : Int) * ‖z - x‖ ^ (p.1 + 1) := by
        norm_num; ring_nf; simp
      _ = ‖(p.1 + 2 : Complex)‖ * ((‖↑p.2 - x‖ / ‖z - x‖) ^ p.1)⁻¹ * ((‖p.2 - x‖ ^ 3)⁻¹ * ‖z - x‖) := by
        simp [hpx, zpow_sub₀, div_pow]; field
      _ <= (p.1 + 2) * (κ ^ p.1)⁻¹ * ((‖p.2 - x‖ ^ 3)⁻¹ * ‖z - x‖) := by
        gcongr
        · norm_cast
        · exact (le_div_iff₀ (by simpa [sub_eq_zero])).mpr ((mul_comm _ _).trans_le (hκ' p.2 hp).le)
      _ = _ := by simp [zpow_ofNat]

/--
lemma `weierstrassPExcept_eq_tsum` / 引理 `weierstrassPExcept_eq_tsum`

English:
lemma weierstrassPExcept_eq_tsum
  statement: (l₀ z x : Complex)
  proof: by
  trans ∑' (l : L.lattice) (i : Nat), if l.1 = l₀ then 0 else
      ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : Int) - i.casesOn (l.1 ^ (-2 : Int)) 0) * (z - x) ^ i
  · delta weierstrassPExcept
    congr 1 with l
    split_ifs with h
    · simp
    simpa [mul_comm] using ((Complex.one_div_sub_sq_sub_one

中文:
引理 weierstrassPExcept_eq_tsum
  结论: (l₀ z x : 复形)
  证明: by
  trans ∑' (l : L.lattice) (i : Nat), if l.1 = l₀ then 0 else
      ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : Int) - i.casesOn (l.1 ^ (-2 : Int)) 0) * (z - x) ^ i
  · delta weierstrassPExcept
    congr 1 with l
    split_ifs with h
    · simp
    simpa [mul_comm] using ((Complex.one_div_sub_sq_sub_one

Depends on / 依赖: Complex.one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero, L.lattice, L.weiers, casesOn, enorm_eq_nnnorm, hasSum, i.casesOn, lattice, mul_comm, norm_nonneg, one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero, split_ifs, sub_eq_zero, trans_lt, tsum_eq, tsum_eq.symm, weiers, weierstrassPExcept
-/
lemma weierstrassPExcept_eq_tsum (l₀ z x : Complex)
    (hx : forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ < ‖l - x‖) :
    ℘[L - l₀] z = ∑' i : Nat, (L.weierstrassPExceptSeries l₀ x).coeff i * (z - x) ^ i := by
  trans ∑' (l : L.lattice) (i : Nat), if l.1 = l₀ then 0 else
      ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : Int) - i.casesOn (l.1 ^ (-2 : Int)) 0) * (z - x) ^ i
  · delta weierstrassPExcept
    congr 1 with l
    split_ifs with h
    · simp
    simpa [mul_comm] using ((Complex.one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero l x
      (by simpa [sub_eq_zero] using (norm_nonneg _).trans_lt (hx l h))).hasSum (y := z - x)
      (by simpa [enorm_eq_nnnorm] using hx _ h)).tsum_eq.symm
  trans ∑' (l : ↥L.lattice) (i : Nat), L.weierstrassPExceptSummand l₀ x i l * (z - x) ^ i
  · simp only [weierstrassPExceptSummand, ite_mul, zero_mul]
  · simp_rw [coeff_weierstrassPExceptSeries, ← tsum_mul_right]
    apply Summable.tsum_comm
    exact L.summable_weierstrassPExceptSummand l₀ z x hx

/--
lemma `weierstrassPExceptSeries_hasSum` / 引理 `weierstrassPExceptSeries_hasSum`

English:
lemma weierstrassPExceptSeries_hasSum
  statement: (l₀ z x : Complex)
  proof: by
  refine (Summable.hasSum_iff ?_).mpr (L.weierstrassPExcept_eq_tsum l₀ z x hx).symm
  simp_rw [coeff_weierstrassPExceptSeries, ← tsum_mul_right]
  exact (L.summable_weierstrassPExceptSummand l₀ z x hx).prod

中文:
引理 weierstrassPExceptSeries_hasSum
  结论: (l₀ z x : 复形)
  证明: by
  refine (Summable.hasSum_iff ?_).mpr (L.weierstrassPExcept_eq_tsum l₀ z x hx).symm
  simp_rw [coeff_weierstrassPExceptSeries, ← tsum_mul_right]
  exact (L.summable_weierstrassPExceptSummand l₀ z x hx).prod

Depends on / 依赖: L.summable_weierstrassPExceptSummand, L.weierstrassPExcept_eq_tsum, Summable, Summable.hasSum_iff, coeff_weierstrassPExceptSeries, hasSum_iff, simp_rw, summable_weierstrassPExceptSummand, tsum_mul_right, weierstrassPExcept_eq_tsum
-/
lemma weierstrassPExceptSeries_hasSum (l₀ z x : Complex)
    (hx : forall l : L.lattice, l.1 != l₀ -> ‖z - x‖ < ‖l - x‖) :
    HasSum (fun i => (L.weierstrassPExceptSeries l₀ x).coeff i * (z - x) ^ i) (℘[L - l₀] z) := by
  refine (Summable.hasSum_iff ?_).mpr (L.weierstrassPExcept_eq_tsum l₀ z x hx).symm
  simp_rw [coeff_weierstrassPExceptSeries, ← tsum_mul_right]
  exact (L.summable_weierstrassPExceptSummand l₀ z x hx).prod

/--
lemma `hasFPowerSeriesOnBall_weierstrassPExcept` / 引理 `hasFPowerSeriesOnBall_weierstrassPExcept`

English:
lemma hasFPowerSeriesOnBall_weierstrassPExcept
  statement: (l₀ x : Complex) (r : NNReal) (hr0 : 0 < r)
  proof: by
  constructor
  · apply FormalMultilinearSeries.le_radius_of_tendsto (l := 0)
    convert!
      tendsto_norm.comp
        (L.weierstrassPExceptSeries_hasSum l₀ (x + r) x ?_).summable.tendsto_atTop_zero using
      2 with i
    · simp
    · simp
    · intro l hl
      simpa [-Metric.mem_closedBal

中文:
引理 hasFPowerSeriesOnBall_weierstrassPExcept
  结论: (l₀ x : 复形) (r : 非负实数) (hr0 : 0 < r)
  证明: by
  constructor
  · apply FormalMultilinearSeries.le_radius_of_tendsto (l := 0)
    convert!
      tendsto_norm.comp
        (L.weierstrassPExceptSeries_hasSum l₀ (x + r) x ?_).summable.tendsto_atTop_zero using
      2 with i
    · simp
    · simp
    · intro l hl
      simpa [-Metric.mem_closedBal

Depends on / 依赖: ENNReal, ENNReal.coe_pos.mpr, FormalMultilinearSeries, FormalMultilinearSeries.le_radius_of_tendsto, L.weierstrassPExceptSeries_hasSum, Metric, Metric.mem_closedBall, Set.subset_compl_comm.mp, add_sub_cancel_left, coe_pos, convert, le_radius_of_tendsto, mem_closedBall, mem_closedBall_iff_norm, replace, subset_compl_comm, summable, summable.tendsto_atTop_zero, tendsto_atTop_zero, tendsto_norm
-/
lemma hasFPowerSeriesOnBall_weierstrassPExcept (l₀ x : Complex) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x r subseteq (L.lattice \ {l₀})ᶜ) :
    HasFPowerSeriesOnBall ℘[L - l₀] (L.weierstrassPExceptSeries l₀ x) x r := by
  constructor
  · apply FormalMultilinearSeries.le_radius_of_tendsto (l := 0)
    convert!
      tendsto_norm.comp
        (L.weierstrassPExceptSeries_hasSum l₀ (x + r) x ?_).summable.tendsto_atTop_zero using
      2 with i
    · simp
    · simp
    · intro l hl
      simpa [-Metric.mem_closedBall, mem_closedBall_iff_norm]
        using Set.subset_compl_comm.mp hr ⟨l.2, hl⟩
  · exact ENNReal.coe_pos.mpr hr0
  · intro z hz
    replace hz : ‖z‖ < r := by simpa using hz
    have := L.weierstrassPExceptSeries_hasSum l₀ (x + z) x
    simp only [add_sub_cancel_left] at this
    have A (l : ↥L.lattice) (hl : ↑l != l₀) : r < ‖↑l - x‖ := by
      simpa [-Metric.mem_closedBall, mem_closedBall_iff_norm] using
        Set.subset_compl_comm.mp hr ⟨l.2, hl⟩
    convert! this (fun l hl => hz.trans (A l hl)) with i
    rw [weierstrassPExceptSeries]; rw [FormalMultilinearSeries.ofScalars_apply_eq]; rw [FormalMultilinearSeries.coeff_ofScalars]; rw [smul_eq_mul]

/--
lemma `hasFPowerSeriesAt_weierstrassPExcept` / 引理 `hasFPowerSeriesAt_weierstrassPExcept`

English:
lemma hasFPowerSeriesAt_weierstrassPExcept
  given: (l : Complex)
  proof: by
  obtain ⟨r, h₁, h₂⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.compl_lattice_sdiff_singleton_mem_nhds l)
  lift r to NNReal using h₁.le
  simpa [weierstrassPExceptSeries] using
    (L.hasFPowerSeriesOnBall_weierstrassPExcept l l r h₁ h₂).hasFPowerSeriesAt

中文:
引理 hasFPowerSeriesAt_weierstrassPExcept
  条件: (l : 复形)
  证明: by
  obtain ⟨r, h₁, h₂⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.compl_lattice_sdiff_singleton_mem_nhds l)
  lift r to NNReal using h₁.le
  simpa [weierstrassPExceptSeries] using
    (L.hasFPowerSeriesOnBall_weierstrassPExcept l l r h₁ h₂).hasFPowerSeriesAt
-/
lemma hasFPowerSeriesAt_weierstrassPExcept (l : Complex) :
    HasFPowerSeriesAt ℘[L - l] (.ofScalars (𝕜 := Complex) Complex fun i : Nat =>
      if i = 0 then ℘[L - l] l else (i + 1) * L.sumInvPow l (i + 2)) l := by
  obtain ⟨r, h₁, h₂⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.compl_lattice_sdiff_singleton_mem_nhds l)
  lift r to NNReal using h₁.le
  simpa [weierstrassPExceptSeries] using
    (L.hasFPowerSeriesOnBall_weierstrassPExcept l l r h₁ h₂).hasFPowerSeriesAt

/--
lemma `analyticOnNhd_weierstrassPExcept` / 引理 `analyticOnNhd_weierstrassPExcept`

English:
lemma analyticOnNhd_weierstrassPExcept
  given: (l₀ : Complex)
  statement: AnalyticOnNhd Complex ℘[L - l₀] (L.lattice \ {l₀})ᶜ
  proof: (L.differentiableOn_weierstrassPExcept l₀).analyticOnNhd L.isOpen_compl_lattice_sdiff

@[fun_prop]

中文:
引理 analyticOnNhd_weierstrassPExcept
  条件: (l₀ : 复形)
  结论: AnalyticOnNhd 复形 ℘[L - l₀] (L.lattice \ {l₀})ᶜ
  证明: (L.differentiableOn_weierstrassPExcept l₀).analyticOnNhd L.isOpen_compl_lattice_sdiff

@[fun_prop]

Depends on / 依赖: L.differentiableOn_weierstrassPExcept, L.isOpen_compl_lattice_sdiff, analyticOnNhd, differentiableOn_weierstrassPExcept, isOpen_compl_lattice_sdiff
-/
lemma analyticOnNhd_weierstrassPExcept (l₀ : Complex) : AnalyticOnNhd Complex ℘[L - l₀] (L.lattice \ {l₀})ᶜ :=
  (L.differentiableOn_weierstrassPExcept l₀).analyticOnNhd L.isOpen_compl_lattice_sdiff

@[fun_prop]
/--
lemma `analyticAt_weierstrassPExcept` / 引理 `analyticAt_weierstrassPExcept`

English:
lemma analyticAt_weierstrassPExcept
  given: (l₀ : Complex)
  statement: AnalyticAt Complex ℘[L - l₀] l₀
  proof: L.analyticOnNhd_weierstrassPExcept _ _ (by simp)

中文:
引理 analyticAt_weierstrassPExcept
  条件: (l₀ : 复形)
  结论: AnalyticAt 复形 ℘[L - l₀] l₀
  证明: L.analyticOnNhd_weierstrassPExcept _ _ (by simp)

Depends on / 依赖: L.analyticOnNhd_weierstrassPExcept, analyticOnNhd_weierstrassPExcept
-/
lemma analyticAt_weierstrassPExcept (l₀ : Complex) : AnalyticAt Complex ℘[L - l₀] l₀ :=
  L.analyticOnNhd_weierstrassPExcept _ _ (by simp)

attribute [local simp] Nat.factorial_ne_zero in
/--
lemma `iteratedDeriv_weierstrassPExcept_self` / 引理 `iteratedDeriv_weierstrassPExcept_self`

English:
lemma iteratedDeriv_weierstrassPExcept_self
  given: (l : Complex) {n : Nat}
  proof: by
  rw [← div_mul_cancel₀ (a := iteratedDeriv _ _ _) (b := ↑n !) (by simp)]; rw [← eq_div_iff_mul_eq (by simp)]
  trans if n = 0 then ℘[L - l] l else (n + 1) * L.sumInvPow l (n + 2)
  · simpa using congr($((L.analyticAt_weierstrassPExcept l).hasFPowerSeriesAt
.eq_formalMultilinearSeries (L.hasFPowe

中文:
引理 iteratedDeriv_weierstrassPExcept_self
  条件: (l : 复形) {n : 自然数}
  证明: by
  rw [← div_mul_cancel₀ (a := iteratedDeriv _ _ _) (b := ↑n !) (by simp)]; rw [← eq_div_iff_mul_eq (by simp)]
  trans if n = 0 then ℘[L - l] l else (n + 1) * L.sumInvPow l (n + 2)
  · simpa using congr($((L.analyticAt_weierstrassPExcept l).hasFPowerSeriesAt
.eq_formalMultilinearSeries (L.hasFPowe

Depends on / 依赖: L.analyticAt_weierstrassPExcept, L.hasFPowerSeriesAt_weierstrassPExcept, L.sumInvPow, Nat.factorial_succ, analyticAt_weierstrassPExcept, eq_div_iff_mul_eq, eq_formalMultilinearSeries, factorial_succ, hasFPowerSeriesAt, hasFPowerSeriesAt_weierstrassPExcept, iteratedDeriv, sumInvPow
-/
lemma iteratedDeriv_weierstrassPExcept_self (l : Complex) {n : Nat} :
    iteratedDeriv n ℘[L - l] l =
      if n = 0 then ℘[L - l] l else (n + 1)! * L.sumInvPow l (n + 2) := by
  rw [← div_mul_cancel₀ (a := iteratedDeriv _ _ _) (b := ↑n !) (by simp)]; rw [← eq_div_iff_mul_eq (by simp)]
  trans if n = 0 then ℘[L - l] l else (n + 1) * L.sumInvPow l (n + 2)
  · simpa using congr($((L.analyticAt_weierstrassPExcept l).hasFPowerSeriesAt
.eq_formalMultilinearSeries (L.hasFPowerSeriesAt_weierstrassPExcept l)).coeff n)
  · cases n <;> simp [Nat.factorial_succ]; field

end AnalyticWeierstrassPExcept

section AnalyticderivWeierstrassPExcept

/--
Definition of `derivWeierstrassPExceptSeries` / `derivWeierstrassPExceptSeries` 的定义

English:
definition derivWeierstrassPExceptSeries
  signature: (l₀ x : Complex)
  body: letI := Classical.propDecidable
  .ofScalars _ fun i => (i + 1) * (i + 2) *
    (L.sumInvPow x (i + 3) - if l₀ in L.lattice then ((l₀ - x) ^ (i + 3))⁻¹ else 0)

中文:
定义 derivWeierstrassPExceptSeries
  签名: (l₀ x : 复形)
  定义体: letI := Classical.propDecidable
  .ofScalars _ fun i => (i + 1) * (i + 2) *
    (L.sumInvPow x (i + 3) - if l₀ in L.lattice then ((l₀ - x) ^ (i + 3))⁻¹ else 0)

Depends on / 依赖: Classical, Classical.propDecidable, L.lattice, L.sumInvPow, lattice, ofScalars, propDecidable, sumInvPow
-/
def derivWeierstrassPExceptSeries (l₀ x : Complex) : FormalMultilinearSeries Complex Complex Complex :=
  letI := Classical.propDecidable
  .ofScalars _ fun i => (i + 1) * (i + 2) *
    (L.sumInvPow x (i + 3) - if l₀ in L.lattice then ((l₀ - x) ^ (i + 3))⁻¹ else 0)

/--
lemma `hasFPowerSeriesOnBall_derivWeierstrassPExcept` / 引理 `hasFPowerSeriesOnBall_derivWeierstrassPExcept`

English:
lemma hasFPowerSeriesOnBall_derivWeierstrassPExcept
  statement: (l₀ x : Complex) (r : NNReal) (hr0 : 0 < r)
  proof: by
  refine .congr ?_
    ((L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept l₀).mono (.trans ?_ hr))
  · have := (L.hasFPowerSeriesOnBall_weierstrassPExcept l₀ x r hr0 hr).fderiv
    convert! (ContinuousLinearMap.apply Complex Complex (1 : Complex)).comp_hasFPowerSeriesOnBall this
    ext n


中文:
引理 hasFPowerSeriesOnBall_derivWeierstrassPExcept
  结论: (l₀ x : 复形) (r : 非负实数) (hr0 : 0 < r)
  证明: by
  refine .congr ?_
    ((L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept l₀).mono (.trans ?_ hr))
  · have := (L.hasFPowerSeriesOnBall_weierstrassPExcept l₀ x r hr0 hr).fderiv
    convert! (ContinuousLinearMap.apply Complex Complex (1 : Complex)).comp_hasFPowerSeriesOnBall this
    ext n


Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.apply, L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept, L.hasFPowerSeriesOnBall_weierstrassPExcept, Metric, Metric.ball_subset_closedBall, ball_subset_closedBall, comp_hasFPowerSeriesOnBall, convert, derivWeierstrassPExceptSeries, eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept, fderiv, hasFPowerSeriesOnBall_weierstrassPExcept, weierstrassPExceptSeries
-/
lemma hasFPowerSeriesOnBall_derivWeierstrassPExcept (l₀ x : Complex) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x r subseteq (L.lattice \ {l₀})ᶜ) :
    HasFPowerSeriesOnBall ℘'[L - l₀] (L.derivWeierstrassPExceptSeries l₀ x) x r := by
  refine .congr ?_
    ((L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept l₀).mono (.trans ?_ hr))
  · have := (L.hasFPowerSeriesOnBall_weierstrassPExcept l₀ x r hr0 hr).fderiv
    convert! (ContinuousLinearMap.apply Complex Complex (1 : Complex)).comp_hasFPowerSeriesOnBall this
    ext n
    simp [weierstrassPExceptSeries, derivWeierstrassPExceptSeries]
    ring
  · simpa using Metric.ball_subset_closedBall

/--
lemma `hasFPowerSeriesAt_derivWeierstrassPExcept` / 引理 `hasFPowerSeriesAt_derivWeierstrassPExcept`

English:
lemma hasFPowerSeriesAt_derivWeierstrassPExcept
  given: (l : Complex)
  proof: by
  obtain ⟨r, h₁, h₂⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.compl_lattice_sdiff_singleton_mem_nhds l)
  simpa [derivWeierstrassPExceptSeries] using
    (L.hasFPowerSeriesOnBall_derivWeierstrassPExcept l l ⟨r, h₁.le⟩ h₁ h₂).hasFPowerSeriesAt

中文:
引理 hasFPowerSeriesAt_derivWeierstrassPExcept
  条件: (l : 复形)
  证明: by
  obtain ⟨r, h₁, h₂⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.compl_lattice_sdiff_singleton_mem_nhds l)
  simpa [derivWeierstrassPExceptSeries] using
    (L.hasFPowerSeriesOnBall_derivWeierstrassPExcept l l ⟨r, h₁.le⟩ h₁ h₂).hasFPowerSeriesAt

Depends on / 依赖: L.compl_lattice_sdiff_singleton_mem_nhds, L.hasFPowerSeriesOnBall_derivWeierstrassPExcept, Metric, Metric.nhds_basis_closedBall.mem_iff.mp, compl_lattice_sdiff_singleton_mem_nhds, derivWeierstrassPExceptSeries, hasFPowerSeriesAt, hasFPowerSeriesOnBall_derivWeierstrassPExcept, mem_iff, nhds_basis_closedBall
-/
lemma hasFPowerSeriesAt_derivWeierstrassPExcept (l : Complex) :
    HasFPowerSeriesAt ℘'[L - l]
      (.ofScalars Complex fun i => (i + 1) * (i + 2) * L.sumInvPow l (i + 3)) l := by
  obtain ⟨r, h₁, h₂⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.compl_lattice_sdiff_singleton_mem_nhds l)
  simpa [derivWeierstrassPExceptSeries] using
    (L.hasFPowerSeriesOnBall_derivWeierstrassPExcept l l ⟨r, h₁.le⟩ h₁ h₂).hasFPowerSeriesAt

/--
lemma `analyticOnNhd_derivWeierstrassPExcept` / 引理 `analyticOnNhd_derivWeierstrassPExcept`

English:
lemma analyticOnNhd_derivWeierstrassPExcept
  given: (l₀ : Complex)
  proof: (L.differentiableOn_derivWeierstrassPExcept l₀).analyticOnNhd L.isOpen_compl_lattice_sdiff

@[fun_prop]

中文:
引理 analyticOnNhd_derivWeierstrassPExcept
  条件: (l₀ : 复形)
  证明: (L.differentiableOn_derivWeierstrassPExcept l₀).analyticOnNhd L.isOpen_compl_lattice_sdiff

@[fun_prop]

Depends on / 依赖: L.differentiableOn_derivWeierstrassPExcept, L.isOpen_compl_lattice_sdiff, analyticOnNhd, differentiableOn_derivWeierstrassPExcept, isOpen_compl_lattice_sdiff
-/
lemma analyticOnNhd_derivWeierstrassPExcept (l₀ : Complex) :
    AnalyticOnNhd Complex ℘'[L - l₀] (L.lattice \ {l₀})ᶜ :=
  (L.differentiableOn_derivWeierstrassPExcept l₀).analyticOnNhd L.isOpen_compl_lattice_sdiff

@[fun_prop]
/--
lemma `analyticAt_derivWeierstrassPExcept` / 引理 `analyticAt_derivWeierstrassPExcept`

English:
lemma analyticAt_derivWeierstrassPExcept
  given: (l₀ : Complex)
  proof: L.analyticOnNhd_derivWeierstrassPExcept l₀ _ (by simp)

中文:
引理 analyticAt_derivWeierstrassPExcept
  条件: (l₀ : 复形)
  证明: L.analyticOnNhd_derivWeierstrassPExcept l₀ _ (by simp)

Depends on / 依赖: L.analyticOnNhd_derivWeierstrassPExcept, analyticOnNhd_derivWeierstrassPExcept
-/
lemma analyticAt_derivWeierstrassPExcept (l₀ : Complex) :
    AnalyticAt Complex ℘'[L - l₀] l₀ :=
  L.analyticOnNhd_derivWeierstrassPExcept l₀ _ (by simp)

/--
lemma `iteratedDeriv_derivWeierstrassPExcept_self` / 引理 `iteratedDeriv_derivWeierstrassPExcept_self`

English:
lemma iteratedDeriv_derivWeierstrassPExcept_self
  given: (l : Complex) {n : Nat}
  proof: by
  have : iteratedDeriv n ℘'[L - l] l / n ! = (↑n + 1) * (↑n + 2) * L.sumInvPow l (n + 3) := by
    simpa using congr($((L.analyticAt_derivWeierstrassPExcept l).hasFPowerSeriesAt
.eq_formalMultilinearSeries (L.hasFPowerSeriesAt_derivWeierstrassPExcept l)).coeff n)
  simp [div_eq_iff, Nat.factorial

中文:
引理 iteratedDeriv_derivWeierstrassPExcept_self
  条件: (l : 复形) {n : 自然数}
  证明: by
  have : iteratedDeriv n ℘'[L - l] l / n ! = (↑n + 1) * (↑n + 2) * L.sumInvPow l (n + 3) := by
    simpa using congr($((L.analyticAt_derivWeierstrassPExcept l).hasFPowerSeriesAt
.eq_formalMultilinearSeries (L.hasFPowerSeriesAt_derivWeierstrassPExcept l)).coeff n)
  simp [div_eq_iff, Nat.factorial

Depends on / 依赖: L.analyticAt_derivWeierstrassPExcept, L.hasFPowerSeriesAt_derivWeierstrassPExcept, L.sumInvPow, Nat.factorial_ne_zero, Nat.factorial_succ, analyticAt_derivWeierstrassPExcept, div_eq_iff, eq_formalMultilinearSeries, factorial_ne_zero, factorial_succ, hasFPowerSeriesAt, hasFPowerSeriesAt_derivWeierstrassPExcept, iteratedDeriv, sumInvPow
-/
lemma iteratedDeriv_derivWeierstrassPExcept_self (l : Complex) {n : Nat} :
    iteratedDeriv n ℘'[L - l] l = (n + 2)! * L.sumInvPow l (n + 3) := by
  have : iteratedDeriv n ℘'[L - l] l / n ! = (↑n + 1) * (↑n + 2) * L.sumInvPow l (n + 3) := by
    simpa using congr($((L.analyticAt_derivWeierstrassPExcept l).hasFPowerSeriesAt
.eq_formalMultilinearSeries (L.hasFPowerSeriesAt_derivWeierstrassPExcept l)).coeff n)
  simp [div_eq_iff, Nat.factorial_ne_zero, Nat.factorial_succ] at this ⊢
  grind

@[simp]
/--
lemma `deriv_derivWeierstrassPExcept_self` / 引理 `deriv_derivWeierstrassPExcept_self`

English:
lemma deriv_derivWeierstrassPExcept_self
  given: (l : Complex)
  proof: by
  simpa using! L.iteratedDeriv_derivWeierstrassPExcept_self l (n := 1)

中文:
引理 deriv_derivWeierstrassPExcept_self
  条件: (l : 复形)
  证明: by
  simpa using! L.iteratedDeriv_derivWeierstrassPExcept_self l (n := 1)

Depends on / 依赖: L.iteratedDeriv_derivWeierstrassPExcept_self, iteratedDeriv_derivWeierstrassPExcept_self
-/
lemma deriv_derivWeierstrassPExcept_self (l : Complex) :
    deriv ℘'[L - l] l = 6 * L.sumInvPow l 4 := by
  simpa using! L.iteratedDeriv_derivWeierstrassPExcept_self l (n := 1)

/--
lemma `analyticOnNhd_derivWeierstrassP` / 引理 `analyticOnNhd_derivWeierstrassP`

English:
lemma analyticOnNhd_derivWeierstrassP
  statement: AnalyticOnNhd Complex ℘'[L] L.latticeᶜ
  proof: L.differentiableOn_derivWeierstrassP.analyticOnNhd L.isClosed_lattice.isOpen_compl

中文:
引理 analyticOnNhd_derivWeierstrassP
  结论: AnalyticOnNhd 复形 ℘'[L] L.latticeᶜ
  证明: L.differentiableOn_derivWeierstrassP.analyticOnNhd L.isClosed_lattice.isOpen_compl

Depends on / 依赖: L.differentiableOn_derivWeierstrassP.analyticOnNhd, L.isClosed_lattice.isOpen_compl, analyticOnNhd, differentiableOn_derivWeierstrassP, isClosed_lattice, isOpen_compl
-/
lemma analyticOnNhd_derivWeierstrassP : AnalyticOnNhd Complex ℘'[L] L.latticeᶜ :=
  L.differentiableOn_derivWeierstrassP.analyticOnNhd L.isClosed_lattice.isOpen_compl

end AnalyticderivWeierstrassPExcept

section Analytic

/--
Definition of `weierstrassPSummand` / `weierstrassPSummand` 的定义

English:
definition weierstrassPSummand
  signature: (x : Complex) (i : Nat) (l : L.lattice)
  body: ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : Int) - i.casesOn (l.1 ^ (-2 : Int)) 0)

中文:
定义 weierstrassPSummand
  签名: (x : 复形) (i : 自然数) (l : L.lattice)
  定义体: ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : Int) - i.casesOn (l.1 ^ (-2 : Int)) 0)

Depends on / 依赖: casesOn, i.casesOn
-/
def weierstrassPSummand (x : Complex) (i : Nat) (l : L.lattice) : Complex :=
  ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : Int) - i.casesOn (l.1 ^ (-2 : Int)) 0)

/--
Definition of `weierstrassPSeries` / `weierstrassPSeries` 的定义

English:
definition weierstrassPSeries
  signature: (x : Complex)
  body: .ofScalars _ fun i => if i = 0 then (℘[L] x) else (i + 1) * L.sumInvPow x (i + 2)

中文:
定义 weierstrassPSeries
  签名: (x : 复形)
  定义体: .ofScalars _ fun i => if i = 0 then (℘[L] x) else (i + 1) * L.sumInvPow x (i + 2)

Depends on / 依赖: L.sumInvPow, ofScalars, sumInvPow
-/
def weierstrassPSeries (x : Complex) : FormalMultilinearSeries Complex Complex Complex :=
  .ofScalars _ fun i => if i = 0 then (℘[L] x) else (i + 1) * L.sumInvPow x (i + 2)

/--
lemma `weierstrassPExceptSeries_of_notMem` / 引理 `weierstrassPExceptSeries_of_notMem`

English:
lemma weierstrassPExceptSeries_of_notMem
  given: (l₀ : Complex) (hl₀ : l₀ ∉ L.lattice)
  proof: by
  delta weierstrassPSeries weierstrassPExceptSeries
  congr! with z i f
  · rw [L.weierstrassPExcept_of_notMem _ hl₀]
  · simp [hl₀]

中文:
引理 weierstrassPExceptSeries_of_notMem
  条件: (l₀ : 复形) (hl₀ : l₀ ∉ L.lattice)
  证明: by
  delta weierstrassPSeries weierstrassPExceptSeries
  congr! with z i f
  · rw [L.weierstrassPExcept_of_notMem _ hl₀]
  · simp [hl₀]

Depends on / 依赖: L.weierstrassPExcept_of_notMem, weierstrassPExceptSeries, weierstrassPExcept_of_notMem, weierstrassPSeries
-/
lemma weierstrassPExceptSeries_of_notMem (l₀ : Complex) (hl₀ : l₀ ∉ L.lattice) :
    L.weierstrassPExceptSeries l₀ = L.weierstrassPSeries := by
  delta weierstrassPSeries weierstrassPExceptSeries
  congr! with z i f
  · rw [L.weierstrassPExcept_of_notMem _ hl₀]
  · simp [hl₀]

/--
lemma `weierstrassPExceptSummand_of_notMem` / 引理 `weierstrassPExceptSummand_of_notMem`

English:
lemma weierstrassPExceptSummand_of_notMem
  given: (l₀ : Complex) (hl₀ : l₀ ∉ L.lattice)
  proof: by
  grind [weierstrassPSummand, weierstrassPExceptSummand]

中文:
引理 weierstrassPExceptSummand_of_notMem
  条件: (l₀ : 复形) (hl₀ : l₀ ∉ L.lattice)
  证明: by
  grind [weierstrassPSummand, weierstrassPExceptSummand]

Depends on / 依赖: weierstrassPExceptSummand, weierstrassPSummand
-/
lemma weierstrassPExceptSummand_of_notMem (l₀ : Complex) (hl₀ : l₀ ∉ L.lattice) :
    L.weierstrassPExceptSummand l₀ = L.weierstrassPSummand := by
  grind [weierstrassPSummand, weierstrassPExceptSummand]

/--
lemma `coeff_weierstrassPSeries` / 引理 `coeff_weierstrassPSeries`

English:
lemma coeff_weierstrassPSeries
  given: (x : Complex) (i : Nat)
  proof: by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    L.coeff_weierstrassPExceptSeries,
    ← L.weierstrassPExceptSummand_of_notMem _ L.ω₁_div_two_notMem_lattice]

中文:
引理 coeff_weierstrassPSeries
  条件: (x : 复形) (i : 自然数)
  证明: by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    L.coeff_weierstrassPExceptSeries,
    ← L.weierstrassPExceptSummand_of_notMem _ L.ω₁_div_two_notMem_lattice]

Depends on / 依赖: L.coeff_weierstrassPExceptSeries, L.weierstrassPExceptSeries_of_notMem, L.weierstrassPExceptSummand_of_notMem, coeff_weierstrassPExceptSeries, simp_rw, weierstrassPExceptSeries_of_notMem, weierstrassPExceptSummand_of_notMem
-/
lemma coeff_weierstrassPSeries (x : Complex) (i : Nat) :
    (L.weierstrassPSeries x).coeff i = ∑' l : L.lattice, L.weierstrassPSummand x i l := by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    L.coeff_weierstrassPExceptSeries,
    ← L.weierstrassPExceptSummand_of_notMem _ L.ω₁_div_two_notMem_lattice]

/--
lemma `summable_weierstrassPSummand` / 引理 `summable_weierstrassPSummand`

English:
lemma summable_weierstrassPSummand
  statement: (z x : Complex)
  proof: by
  simp_rw [← L.weierstrassPExceptSummand_of_notMem _ L.ω₁_div_two_notMem_lattice]
  refine L.summable_weierstrassPExceptSummand _ z x fun l hl => hx l

中文:
引理 summable_weierstrassPSummand
  结论: (z x : 复形)
  证明: by
  simp_rw [← L.weierstrassPExceptSummand_of_notMem _ L.ω₁_div_two_notMem_lattice]
  refine L.summable_weierstrassPExceptSummand _ z x fun l hl => hx l

Depends on / 依赖: L.summable_weierstrassPExceptSummand, L.weierstrassPExceptSummand_of_notMem, simp_rw, summable_weierstrassPExceptSummand, weierstrassPExceptSummand_of_notMem
-/
lemma summable_weierstrassPSummand (z x : Complex)
    (hx : forall l : L.lattice, ‖z - x‖ < ‖l - x‖) :
    Summable (Function.uncurry fun b c => L.weierstrassPSummand x b c * (z - x) ^ b) := by
  simp_rw [← L.weierstrassPExceptSummand_of_notMem _ L.ω₁_div_two_notMem_lattice]
  refine L.summable_weierstrassPExceptSummand _ z x fun l hl => hx l

/--
lemma `weierstrassPSeries_hasSum` / 引理 `weierstrassPSeries_hasSum`

English:
lemma weierstrassPSeries_hasSum
  given: (z x : Complex) (hx : forall l : L.lattice, ‖z - x‖ < ‖l - x‖)
  proof: by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    ← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  exact L.weierstrassPExceptSeries_hasSum _ z x fun l hl => hx l

中文:
引理 weierstrassPSeries_hasSum
  条件: (z x : 复形) (hx : 对任意 l : L.lattice, ‖z - x‖ < ‖l - x‖)
  证明: by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    ← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  exact L.weierstrassPExceptSeries_hasSum _ z x fun l hl => hx l

Depends on / 依赖: L.weierstrassPExceptSeries_hasSum, L.weierstrassPExceptSeries_of_notMem, L.weierstrassPExcept_of_notMem, simp_rw, weierstrassPExceptSeries_hasSum, weierstrassPExceptSeries_of_notMem, weierstrassPExcept_of_notMem
-/
lemma weierstrassPSeries_hasSum (z x : Complex) (hx : forall l : L.lattice, ‖z - x‖ < ‖l - x‖) :
    HasSum (fun i => (L.weierstrassPSeries x).coeff i * (z - x) ^ i) (℘[L] z) := by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    ← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  exact L.weierstrassPExceptSeries_hasSum _ z x fun l hl => hx l

/--
lemma `hasFPowerSeriesOnBall_weierstrassP` / 引理 `hasFPowerSeriesOnBall_weierstrassP`

English:
lemma hasFPowerSeriesOnBall_weierstrassP
  statement: (x : Complex) (r : NNReal) (hr0 : 0 < r)
  proof: by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    ← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  exact L.hasFPowerSeriesOnBall_weierstrassPExcept _ x r hr0
    (hr.trans (Set.compl_subset_compl.mpr Set.sdiff_subset))

中文:
引理 hasFPowerSeriesOnBall_weierstrassP
  结论: (x : 复形) (r : 非负实数) (hr0 : 0 < r)
  证明: by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    ← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  exact L.hasFPowerSeriesOnBall_weierstrassPExcept _ x r hr0
    (hr.trans (Set.compl_subset_compl.mpr Set.sdiff_subset))

Depends on / 依赖: L.hasFPowerSeriesOnBall_weierstrassPExcept, L.weierstrassPExceptSeries_of_notMem, L.weierstrassPExcept_of_notMem, Set.compl_subset_compl.mpr, Set.sdiff_subset, compl_subset_compl, hasFPowerSeriesOnBall_weierstrassPExcept, hr.trans, sdiff_subset, simp_rw, weierstrassPExceptSeries_of_notMem, weierstrassPExcept_of_notMem
-/
lemma hasFPowerSeriesOnBall_weierstrassP (x : Complex) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x r subseteq L.latticeᶜ) :
    HasFPowerSeriesOnBall ℘[L] (L.weierstrassPSeries x) x r := by
  simp_rw [← L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    ← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  exact L.hasFPowerSeriesOnBall_weierstrassPExcept _ x r hr0
    (hr.trans (Set.compl_subset_compl.mpr Set.sdiff_subset))

/--
lemma `analyticOnNhd_weierstrassP` / 引理 `analyticOnNhd_weierstrassP`

English:
lemma analyticOnNhd_weierstrassP
  statement: AnalyticOnNhd Complex ℘[L] L.latticeᶜ
  proof: L.differentiableOn_weierstrassP.analyticOnNhd L.isClosed_lattice.isOpen_compl

中文:
引理 analyticOnNhd_weierstrassP
  结论: AnalyticOnNhd 复形 ℘[L] L.latticeᶜ
  证明: L.differentiableOn_weierstrassP.analyticOnNhd L.isClosed_lattice.isOpen_compl

Depends on / 依赖: L.differentiableOn_weierstrassP.analyticOnNhd, L.isClosed_lattice.isOpen_compl, analyticOnNhd, differentiableOn_weierstrassP, isClosed_lattice, isOpen_compl
-/
lemma analyticOnNhd_weierstrassP : AnalyticOnNhd Complex ℘[L] L.latticeᶜ :=
  L.differentiableOn_weierstrassP.analyticOnNhd L.isClosed_lattice.isOpen_compl

/--
lemma `ite_eq_one_sub_sq_mul_weierstrassP` / 引理 `ite_eq_one_sub_sq_mul_weierstrassP`

English:
lemma ite_eq_one_sub_sq_mul_weierstrassP
  given: (l₀ : Complex) (hl₀ : l₀ in L.lattice) (z : Complex)
  proof: by
  grind [L.weierstrassPExcept_add ⟨_, hl₀⟩]

@[fun_prop]

中文:
引理 ite_eq_one_sub_sq_mul_weierstrassP
  条件: (l₀ : 复形) (hl₀ : l₀ in L.lattice) (z : 复形)
  证明: by
  grind [L.weierstrassPExcept_add ⟨_, hl₀⟩]

@[fun_prop]

Depends on / 依赖: L.weierstrassPExcept_add, weierstrassPExcept_add
-/
lemma ite_eq_one_sub_sq_mul_weierstrassP (l₀ : Complex) (hl₀ : l₀ in L.lattice) (z : Complex) :
    (if z = l₀ then 1 else (z - l₀) ^ 2 * ℘[L] z) =
      (z - l₀) ^ 2 * ℘[L - l₀] z + 1 - (z - l₀) ^ 2 / l₀ ^ 2 := by
  grind [L.weierstrassPExcept_add ⟨_, hl₀⟩]

@[fun_prop]
/--
lemma `meromorphic_weierstrassP` / 引理 `meromorphic_weierstrassP`

English:
lemma meromorphic_weierstrassP
  statement: Meromorphic ℘[L]
  proof: by
  intro x
  by_cases hx : x in L.lattice
  · simp_rw [← funext <| L.weierstrassPExcept_add ⟨x, hx⟩]
    have := (analyticOnNhd_weierstrassPExcept L x x (by simp)).meromorphicAt
    fun_prop
  · exact (L.analyticOnNhd_weierstrassP x hx).meromorphicAt

@[fun_prop]

中文:
引理 meromorphic_weierstrassP
  结论: 亚纯 ℘[L]
  证明: by
  intro x
  by_cases hx : x in L.lattice
  · simp_rw [← funext <| L.weierstrassPExcept_add ⟨x, hx⟩]
    have := (analyticOnNhd_weierstrassPExcept L x x (by simp)).meromorphicAt
    fun_prop
  · exact (L.analyticOnNhd_weierstrassP x hx).meromorphicAt

@[fun_prop]

Depends on / 依赖: L.analyticOnNhd_weierstrassP, L.lattice, L.weierstrassPExcept_add, analyticOnNhd_weierstrassP, analyticOnNhd_weierstrassPExcept, fun_prop, lattice, meromorphicAt, simp_rw, weierstrassPExcept_add
-/
lemma meromorphic_weierstrassP : Meromorphic ℘[L] := by
  intro x
  by_cases hx : x in L.lattice
  · simp_rw [← funext <| L.weierstrassPExcept_add ⟨x, hx⟩]
    have := (analyticOnNhd_weierstrassPExcept L x x (by simp)).meromorphicAt
    fun_prop
  · exact (L.analyticOnNhd_weierstrassP x hx).meromorphicAt

@[fun_prop]
/--
lemma `meromorphic_derivWeierstrassP` / 引理 `meromorphic_derivWeierstrassP`

English:
lemma meromorphic_derivWeierstrassP
  statement: Meromorphic ℘'[L]
  proof: by
  rw [← deriv_weierstrassP]
  fun_prop

中文:
引理 meromorphic_derivWeierstrassP
  结论: 亚纯 ℘'[L]
  证明: by
  rw [← deriv_weierstrassP]
  fun_prop

Depends on / 依赖: deriv_weierstrassP, fun_prop
-/
lemma meromorphic_derivWeierstrassP : Meromorphic ℘'[L] := by
  rw [← deriv_weierstrassP]
  fun_prop

/--
lemma `order_weierstrassP` / 引理 `order_weierstrassP`

English:
lemma order_weierstrassP
  given: (l₀ : Complex) (h : l₀ in L.lattice)
  proof: by
  trans ↑(-2 : Int)
  · rw [meromorphicOrderAt_eq_int_iff (L.meromorphic_weierstrassP l₀)]
    refine ⟨fun z => (z - l₀) ^ 2 * ℘[L - l₀] z + 1 - (z - l₀) ^ 2 / l₀ ^ 2, ?_, ?_, ?_⟩
    · have : AnalyticAt Complex ℘[L - l₀] l₀ := L.analyticOnNhd_weierstrassPExcept l₀ l₀ (by simp)
      suffices Ana

中文:
引理 order_weierstrassP
  条件: (l₀ : 复形) (h : l₀ in L.lattice)
  证明: by
  trans ↑(-2 : Int)
  · rw [meromorphicOrderAt_eq_int_iff (L.meromorphic_weierstrassP l₀)]
    refine ⟨fun z => (z - l₀) ^ 2 * ℘[L - l₀] z + 1 - (z - l₀) ^ 2 / l₀ ^ 2, ?_, ?_, ?_⟩
    · have : AnalyticAt Complex ℘[L - l₀] l₀ := L.analyticOnNhd_weierstrassPExcept l₀ l₀ (by simp)
      suffices Ana

Depends on / 依赖: AnalyticAt, L.analyticOnNhd_weierstrassPExcept, L.meromorphic_weierstrassP, analyticAt_const, analyticOnNhd_weierstrassPExcept, filter_upwards, fun_prop, meromorphicOrderAt_eq_int_iff, meromorphic_weierstrassP, self_mem_nhdsWithin
-/
lemma order_weierstrassP (l₀ : Complex) (h : l₀ in L.lattice) :
    meromorphicOrderAt ℘[L] l₀ = -2 := by
  trans ↑(-2 : Int)
  · rw [meromorphicOrderAt_eq_int_iff (L.meromorphic_weierstrassP l₀)]
    refine ⟨fun z => (z - l₀) ^ 2 * ℘[L - l₀] z + 1 - (z - l₀) ^ 2 / l₀ ^ 2, ?_, ?_, ?_⟩
    · have : AnalyticAt Complex ℘[L - l₀] l₀ := L.analyticOnNhd_weierstrassPExcept l₀ l₀ (by simp)
      suffices AnalyticAt Complex (fun z => (z - l₀) ^ 2 / l₀ ^ 2) l₀ by fun_prop
      by_cases hl₀ : l₀ = 0
      · simpa [hl₀] using analyticAt_const
      · fun_prop (disch := simpa)
    · simp
    · filter_upwards [self_mem_nhdsWithin] with z (hz : _ != _)
      have : (z - l₀) ^ 2 != 0 := by simpa [sub_eq_zero]
      simp [← L.ite_eq_one_sub_sq_mul_weierstrassP l₀ h,
        if_neg hz, inv_mul_cancel_left₀ this, zpow_ofNat]
  · norm_num

end Analytic

section Relation

/--
Definition of `G` / `G` 的定义

English:
definition G
  signature: (n : Nat)
  body: ∑' l : L.lattice, (l ^ n)⁻¹

@[simp]

中文:
定义 G
  签名: (n : 自然数)
  定义体: ∑' l : L.lattice, (l ^ n)⁻¹

@[simp]

Depends on / 依赖: L.lattice, lattice
-/
def G (n : Nat) : Complex := ∑' l : L.lattice, (l ^ n)⁻¹

@[simp]
/--
lemma `sumInvPow_zero` / 引理 `sumInvPow_zero`

English:
lemma sumInvPow_zero
  statement: L.sumInvPow 0 = L.G
  proof: by
  ext; simp [sumInvPow, G]

中文:
引理 sumInvPow_zero
  结论: L.sumInvPow 0 = L.G
  证明: by
  ext; simp [sumInvPow, G]

Depends on / 依赖: sumInvPow
-/
lemma sumInvPow_zero : L.sumInvPow 0 = L.G := by
  ext; simp [sumInvPow, G]

/--
lemma `G_eq_zero_of_odd` / 引理 `G_eq_zero_of_odd`

English:
lemma G_eq_zero_of_odd
  given: (n : Nat) (hn : Odd n)
  statement: L.G n = 0
  proof: by
  rw [← CharZero.eq_neg_self_iff]; rw [G]; rw [← tsum_neg]; rw [← (Equiv.neg _).tsum_eq]
  congr with l
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, neg_inv, hn.neg_pow]

中文:
引理 G_eq_zero_of_odd
  条件: (n : 自然数) (hn : Odd n)
  结论: L.G n = 0
  证明: by
  rw [← CharZero.eq_neg_self_iff]; rw [G]; rw [← tsum_neg]; rw [← (Equiv.neg _).tsum_eq]
  congr with l
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, neg_inv, hn.neg_pow]

Depends on / 依赖: CharZero, CharZero.eq_neg_self_iff, Equiv.neg, Equiv.neg_apply, NegMemClass, NegMemClass.coe_neg, coe_neg, eq_neg_self_iff, hn.neg_pow, neg_apply, neg_inv, neg_pow, tsum_eq, tsum_neg
-/
lemma G_eq_zero_of_odd (n : Nat) (hn : Odd n) : L.G n = 0 := by
  rw [← CharZero.eq_neg_self_iff]; rw [G]; rw [← tsum_neg]; rw [← (Equiv.neg _).tsum_eq]
  congr with l
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, neg_inv, hn.neg_pow]

/--
Definition of `g₂` / `g₂` 的定义

English:
definition g₂
  signature: : Complex
  body: 60 * L.G 4

中文:
定义 g₂
  签名: : 复形
  定义体: 60 * L.G 4
-/
def g₂ : Complex := 60 * L.G 4

/--
Definition of `g₃` / `g₃` 的定义

English:
definition g₃
  signature: : Complex
  body: 140 * L.G 6

中文:
定义 g₃
  签名: : 复形
  定义体: 140 * L.G 6
-/
def g₃ : Complex := 140 * L.G 6

/--
Definition of `relation` / `relation` 的定义

English:
definition relation
  signature: (z : Complex)
  body: letI := Classical.propDecidable
  if z in L.lattice then 0 else ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃

@[local fun_prop]

中文:
定义 relation
  签名: (z : 复形)
  定义体: letI := Classical.propDecidable
  if z in L.lattice then 0 else ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃

@[local fun_prop]
-/
private def relation (z : Complex) : Complex :=
  letI := Classical.propDecidable
  if z in L.lattice then 0 else ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃

@[local fun_prop]
/--
lemma `meromorphic_relation` / 引理 `meromorphic_relation`

English:
lemma meromorphic_relation
  statement: Meromorphic L.relation
  proof: by
  have : Meromorphic fun z => ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃ := by fun_prop
  refine fun z => (this _).congr ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_sdiff_singleton_mem_nhds _)] with w hw hw'
  rw [relation]; rw [if_neg (by si

中文:
引理 meromorphic_relation
  结论: 亚纯 L.relation
  证明: by
  have : Meromorphic fun z => ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃ := by fun_prop
  refine fun z => (this _).congr ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_sdiff_singleton_mem_nhds _)] with w hw hw'
  rw [relation]; rw [if_neg (by si
-/
private lemma meromorphic_relation : Meromorphic L.relation := by
  have : Meromorphic fun z => ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃ := by fun_prop
  refine fun z => (this _).congr ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_sdiff_singleton_mem_nhds _)] with w hw hw'
  rw [relation]; rw [if_neg (by simp_all)]

/--
lemma `relation_mul_id_pow_six_eventuallyEq` / 引理 `relation_mul_id_pow_six_eventuallyEq`

English:
lemma relation_mul_id_pow_six_eventuallyEq
  proof: by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds _] with z hz
  by_cases hz0 : z = 0
  · simp [hz0, relation]; norm_num
  replace hz : z ∉ L.lattice := by simp_all
  simp only [Pi.mul_apply, Pi.pow_apply, relation, ↓reduceIte, hz,
    ← ZeroMemClass.coe_zero L.lattice, L.derivWeierstras

中文:
引理 relation_mul_id_pow_six_eventuallyEq
  证明: by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds _] with z hz
  by_cases hz0 : z = 0
  · simp [hz0, relation]; norm_num
  replace hz : z ∉ L.lattice := by simp_all
  simp only [Pi.mul_apply, Pi.pow_apply, relation, ↓reduceIte, hz,
    ← ZeroMemClass.coe_zero L.lattice, L.derivWeierstras
-/
private lemma relation_mul_id_pow_six_eventuallyEq :
    (L.relation * id ^ 6) =ᶠ[nhds 0] fun z =>
      (℘'[L - (0 : Complex)] z * z ^ 3 - 2) ^ 2 - 4 *
      (℘[L - (0 : Complex)] z * z ^ 2 + 1) ^ 3 + L.g₂ *
      (℘[L - (0 : Complex)] z * z ^ 6 + z ^ 4) + L.g₃ * z ^ 6 := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds _] with z hz
  by_cases hz0 : z = 0
  · simp [hz0, relation]; norm_num
  replace hz : z ∉ L.lattice := by simp_all
  simp only [Pi.mul_apply, Pi.pow_apply, relation, ↓reduceIte, hz,
    ← ZeroMemClass.coe_zero L.lattice, L.derivWeierstrassPExcept_def, L.weierstrassPExcept_def]
  simp
  field

@[local fun_prop]
/--
lemma `analyticAt_relation_mul_id_pow_six` / 引理 `analyticAt_relation_mul_id_pow_six`

English:
lemma analyticAt_relation_mul_id_pow_six
  proof: by
  refine .congr ?_ L.relation_mul_id_pow_six_eventuallyEq.symm
  fun_prop

@[local simp]

中文:
引理 analyticAt_relation_mul_id_pow_six
  证明: by
  refine .congr ?_ L.relation_mul_id_pow_six_eventuallyEq.symm
  fun_prop

@[local simp]
-/
private lemma analyticAt_relation_mul_id_pow_six :
    AnalyticAt Complex (L.relation * id ^ 6) 0 := by
  refine .congr ?_ L.relation_mul_id_pow_six_eventuallyEq.symm
  fun_prop

@[local simp]
/--
lemma `relation_neg` / 引理 `relation_neg`

English:
lemma relation_neg
  given: (x)
  statement: L.relation (-x) = L.relation x
  proof: by
  classical simp [relation]

中文:
引理 relation_neg
  条件: (x)
  结论: L.relation (-x) = L.relation x
  证明: by
  classical simp [relation]
-/
private lemma relation_neg (x) : L.relation (-x) = L.relation x := by
  classical simp [relation]

attribute [local fun_prop] AnalyticAt.contDiffAt in
/--
lemma `iteratedDeriv_six_relation_mul_id_pow_six` / 引理 `iteratedDeriv_six_relation_mul_id_pow_six`

English:
lemma iteratedDeriv_six_relation_mul_id_pow_six
  proof: by
  rw [L.relation_mul_id_pow_six_eventuallyEq.iteratedDeriv_eq]
  simp_rw [pow_succ (_ + _), pow_succ (_ - _), pow_zero, one_mul]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_sub,
    iteratedDeriv_fun_mul, iteratedDeriv_const, iteratedDeriv_fun_pow_zero,
    iter

中文:
引理 iteratedDeriv_six_relation_mul_id_pow_six
  证明: by
  rw [L.relation_mul_id_pow_six_eventuallyEq.iteratedDeriv_eq]
  simp_rw [pow_succ (_ + _), pow_succ (_ - _), pow_zero, one_mul]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_sub,
    iteratedDeriv_fun_mul, iteratedDeriv_const, iteratedDeriv_fun_pow_zero,
    iter
-/
private lemma iteratedDeriv_six_relation_mul_id_pow_six :
    iteratedDeriv 6 (L.relation * id ^ 6) 0 = 0 := by
  rw [L.relation_mul_id_pow_six_eventuallyEq.iteratedDeriv_eq]
  simp_rw [pow_succ (_ + _), pow_succ (_ - _), pow_zero, one_mul]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_sub,
    iteratedDeriv_fun_mul, iteratedDeriv_const, iteratedDeriv_fun_pow_zero,
    iteratedDeriv_derivWeierstrassPExcept_self, iteratedDeriv_weierstrassPExcept_self]
  simp [Finset.sum_range_succ, L.G_eq_zero_of_odd 3 (by decide), g₃,
    show Nat.choose 6 4 = 15 by rfl, show Nat.choose 6 3 = 20 by rfl]
  ring

attribute [local fun_prop] AnalyticAt.contDiffAt in
/--
lemma `analyticAt_relation_zero` / 引理 `analyticAt_relation_zero`

English:
lemma analyticAt_relation_zero
  statement: AnalyticAt Complex L.relation 0
  proof: by
  refine .of_meromorphicOrderAt_pos (one_pos.trans_le ?_) (by simp [relation])
  suffices 7 <= meromorphicOrderAt (L.relation * id ^ 6) 0 by
    rw [meromorphicOrderAt_mul (by fun_prop) (by fun_prop)]; rw [meromorphicOrderAt_pow (by fun_prop)] at this
    rw [← WithTop.add_le_add_iff_right (z := 

中文:
引理 analyticAt_relation_zero
  结论: AnalyticAt 复形 L.relation 0
  证明: by
  refine .of_meromorphicOrderAt_pos (one_pos.trans_le ?_) (by simp [relation])
  suffices 7 <= meromorphicOrderAt (L.relation * id ^ 6) 0 by
    rw [meromorphicOrderAt_mul (by fun_prop) (by fun_prop)]; rw [meromorphicOrderAt_pow (by fun_prop)] at this
    rw [← WithTop.add_le_add_iff_right (z := 
-/
private lemma analyticAt_relation_zero : AnalyticAt Complex L.relation 0 := by
  refine .of_meromorphicOrderAt_pos (one_pos.trans_le ?_) (by simp [relation])
  suffices 7 <= meromorphicOrderAt (L.relation * id ^ 6) 0 by
    rw [meromorphicOrderAt_mul (by fun_prop) (by fun_prop)]; rw [meromorphicOrderAt_pow (by fun_prop)] at this
    rw [← WithTop.add_le_add_iff_right (z := 6) (by simp)]
    simpa [-add_le_add_iff_left_of_ne_top] using! this
  rw [AnalyticAt.meromorphicOrderAt_eq (by fun_prop)]
  refine ENat.monotone_map_iff.mpr Nat.mono_cast
    ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (by fun_prop)).mpr fun i hi₁ => ?_)
  by_cases hi₂ : Odd i
  · simpa [← CharZero.eq_neg_self_iff, hi₂, (show Even 6 by decide).neg_pow] using!
      (iteratedDeriv_comp_neg i (L.relation * id ^ 6) 0 :)
  by_cases hi₃ : i = 0
  · simp [hi₃]
  by_cases hi₄ : i = 6
  · exact hi₄ ▸ L.iteratedDeriv_six_relation_mul_id_pow_six
  rw [L.relation_mul_id_pow_six_eventuallyEq.iteratedDeriv_eq]
  simp_rw [pow_succ (_ + _), pow_succ (_ - _), pow_zero, one_mul]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_sub,
    iteratedDeriv_fun_mul, iteratedDeriv_const, iteratedDeriv_fun_pow_zero,
    iteratedDeriv_derivWeierstrassPExcept_self, iteratedDeriv_weierstrassPExcept_self]
  obtain rfl | rfl : i = 2 ∨ i = 4 := by grind
  · simp [Finset.sum_range_succ]
  · simp [Finset.sum_range_succ, show Nat.choose 4 2 = 6 by rfl, g₂]; ring

@[local simp]
/--
lemma `relation_add_coe` / 引理 `relation_add_coe`

English:
lemma relation_add_coe
  given: (x : Complex) (l : L.lattice)
  proof: by
  simp only [relation, derivWeierstrassP_add_coe, weierstrassP_add_coe]
  congr 1
  simpa using (L.lattice.toAddSubgroup.add_mem_cancel_right (y := x) l.2)

@[local simp]

中文:
引理 relation_add_coe
  条件: (x : 复形) (l : L.lattice)
  证明: by
  simp only [relation, derivWeierstrassP_add_coe, weierstrassP_add_coe]
  congr 1
  simpa using (L.lattice.toAddSubgroup.add_mem_cancel_right (y := x) l.2)

@[local simp]
-/
private lemma relation_add_coe (x : Complex) (l : L.lattice) :
    L.relation (x + l) = L.relation x := by
  simp only [relation, derivWeierstrassP_add_coe, weierstrassP_add_coe]
  congr 1
  simpa using (L.lattice.toAddSubgroup.add_mem_cancel_right (y := x) l.2)

@[local simp]
/--
lemma `relation_sub_coe` / 引理 `relation_sub_coe`

English:
lemma relation_sub_coe
  given: (x : Complex) (l : L.lattice)
  proof: by
  rw [← L.relation_add_coe _ l]; rw [sub_add_cancel]

中文:
引理 relation_sub_coe
  条件: (x : 复形) (l : L.lattice)
  证明: by
  rw [← L.relation_add_coe _ l]; rw [sub_add_cancel]

Depends on / 依赖: Action, f.hom, isIso_of_hom_isIso
-/
private lemma relation_sub_coe (x : Complex) (l : L.lattice) :
    L.relation (x - l) = L.relation x := by
  rw [← L.relation_add_coe _ l]; rw [sub_add_cancel]

/--
lemma `analyticAt_relation` / 引理 `analyticAt_relation`

English:
lemma analyticAt_relation
  given: (x : Complex)
  statement: AnalyticAt Complex L.relation x
  proof: by
  by_cases hx : x in L.lattice
  · lift x to L.lattice using hx
    have := L.analyticAt_relation_zero
    rw [← sub_self x.1] at this
    convert! this.comp (f := (· - x.1)) (by fun_prop)
    ext a
    simp
  · have : AnalyticAt Complex (fun z => ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.

中文:
引理 analyticAt_relation
  条件: (x : 复形)
  结论: AnalyticAt 复形 L.relation x
  证明: by
  by_cases hx : x in L.lattice
  · lift x to L.lattice using hx
    have := L.analyticAt_relation_zero
    rw [← sub_self x.1] at this
    convert! this.comp (f := (· - x.1)) (by fun_prop)
    ext a
    simp
  · have : AnalyticAt Complex (fun z => ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.
-/
private lemma analyticAt_relation (x : Complex) : AnalyticAt Complex L.relation x := by
  by_cases hx : x in L.lattice
  · lift x to L.lattice using hx
    have := L.analyticAt_relation_zero
    rw [← sub_self x.1] at this
    convert! this.comp (f := (· - x.1)) (by fun_prop)
    ext a
    simp
  · have : AnalyticAt Complex (fun z => ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃) x := by
      have := L.analyticOnNhd_derivWeierstrassP _ hx
      have := L.analyticOnNhd_weierstrassP _ hx
      fun_prop
    apply this.congr
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hx] with x hx
    simp_all [relation]

/--
lemma `relation_eq_zero` / 引理 `relation_eq_zero`

English:
lemma relation_eq_zero
  statement: L.relation = 0
  proof: by
  ext x
  have : Differentiable Complex L.relation := fun x => (L.analyticAt_relation x).differentiableAt
  exact (this.apply_eq_apply_of_bounded (IsZLattice.isCompact_range_of_periodic L.lattice _
    this.continuous fun z w hw => by lift w to L.lattice using hw; simp).isBounded x 0).trans
    (

中文:
引理 relation_eq_zero
  结论: L.relation = 0
  证明: by
  ext x
  have : Differentiable Complex L.relation := fun x => (L.analyticAt_relation x).differentiableAt
  exact (this.apply_eq_apply_of_bounded (IsZLattice.isCompact_range_of_periodic L.lattice _
    this.continuous fun z w hw => by lift w to L.lattice using hw; simp).isBounded x 0).trans
    (

Depends on / 依赖: f.inv.hom
-/
private lemma relation_eq_zero : L.relation = 0 := by
  ext x
  have : Differentiable Complex L.relation := fun x => (L.analyticAt_relation x).differentiableAt
  exact (this.apply_eq_apply_of_bounded (IsZLattice.isCompact_range_of_periodic L.lattice _
    this.continuous fun z w hw => by lift w to L.lattice using hw; simp).isBounded x 0).trans
    (if_pos (by simp))

/--
lemma `derivWeierstrassP_sq` / 引理 `derivWeierstrassP_sq`

English:
lemma derivWeierstrassP_sq
  given: (z : Complex) (hz : z ∉ L.lattice)
  proof: by
  simpa [sub_eq_zero, relation, hz, sub_add] using congr($L.relation_eq_zero z)

中文:
引理 derivWeierstrassP_sq
  条件: (z : 复形) (hz : z ∉ L.lattice)
  证明: by
  simpa [sub_eq_zero, relation, hz, sub_add] using congr($L.relation_eq_zero z)

Depends on / 依赖: L.relation_eq_zero, f.hom.hom, relation, relation_eq_zero, sub_add, sub_eq_zero
-/
lemma derivWeierstrassP_sq (z : Complex) (hz : z ∉ L.lattice) :
    ℘'[L] z ^ 2 = 4 * ℘[L] z ^ 3 - L.g₂ * ℘[L] z - L.g₃ := by
  simpa [sub_eq_zero, relation, hz, sub_add] using congr($L.relation_eq_zero z)

end Relation

end PeriodPair
