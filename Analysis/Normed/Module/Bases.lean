/-
Copyright (c) 2025 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Schauder Bases and Generalized Bases

This file defines the theory of bases in Banach spaces, unifying the classical
sequential notion with modern generalized bases.

## Overview

A **basis** in a normed space allows every vector to be expanded as a (potentially infinite) linear
combination of basis vectors. Historically, this was defined strictly for sequences with convergence
of partial sums (the "classical Schauder basis").

However, modern functional analysis requires bases indexed by arbitrary sets
`β` (e.g., for non-separable spaces or Hilbert spaces), where convergence
is defined via nets over finite subsets (unconditional convergence).

This file provides a unified structure `GeneralSchauderBasis` that captures both:
* **Classical Schauder Bases:** Indexed by `ℕ`, using `SummationFilter.conditional`
  to enforce sequential convergence of partial sums.
* **Unconditional/Extended Bases:** Indexed by an arbitrary type `β`, using
  `SummationFilter.unconditional` to enforce convergence of the net of all finite subsets.

## Main Definitions

* `GeneralSchauderBasis β 𝕜 X L`: A structure representing a generalized Schauder basis for a
  normed space `X` over a field `𝕜`, indexed by a type `β` with a `SummationFilter L`.
* `SchauderBasis 𝕜 X`: The classical Schauder basis, an abbreviation for
  `GeneralSchauderBasis ℕ 𝕜 X (SummationFilter.conditional ℕ)`.
* `UnconditionalSchauderBasis β 𝕜 X`: An unconditional Schauder basis, an abbreviation for
  `GeneralSchauderBasis β 𝕜 X (SummationFilter.unconditional β)`.
* `GeneralSchauderBasis.proj b A`: The projection onto a finite set `A` of basis vectors,
  mapping `x ↦ ∑ i ∈ A, b.coord i x • b i`.
* `SchauderBasis.proj b n`: The `n`-th projection `X → X`,
  mapping `x ↦ ∑ i ∈ Finset.range n, b.coord i x • b i`.
* `UnconditionalSchauderBasis.enormProjBound`: The supremum of projection norms (`ℝ≥0∞`).
* `UnconditionalSchauderBasis.nnnormProjBound`: The supremum of projection norms (`ℝ≥0`),
  requires `[CompleteSpace X]`.
* `RankOneDecomposition 𝕜 X`: Data for constructing a Schauder basis from
  a sequence of finite-rank projections whose differences are rank one.
* `RankOneDecomposition.basis`: Constructs a `SchauderBasis` from a `RankOneDecomposition`.

## Main Results

* `GeneralSchauderBasis.linearIndependent`: A Schauder basis is linearly independent.
* `GeneralSchauderBasis.tendsto_proj`: The projections `proj A` converge to identity
  along the summation filter.
* `GeneralSchauderBasis.range_proj_eq_span`: The range of `proj A` is the span of the basis
  elements in `A`.
* `GeneralSchauderBasis.proj_comp`: Composition of projections satisfies
  `proj A (proj B x) = proj (A ∩ B) x`.
* `SchauderBasis.exists_norm_proj_le`: In a Banach space, the projections are uniformly bounded.
* `UnconditionalSchauderBasis.exists_norm_proj_le`: For unconditional bases, projections
  onto all finite sets are uniformly bounded.

## References

* [Albiac, Fernando. and Kalton, Nigel J., Topics in Banach Space Theory][Albiac_Kalton_2016].
* [Singer, Ivan, Bases in Banach spaces][Singer_1970].
* [Marti, Jürg T., Introduction to the theory of bases][MartiJurg1969].

-/

@[expose] public section

noncomputable section

open Filter Topology LinearMap Set ENNReal NNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

open scoped Classical in
/--
A generalized Schauder basis indexed by `β` with summation along filter `L`.

The key fields are:
* `basis`: The basis vectors `e i` for `i : β`
* `coord`: The coordinate functionals `f i` for `i : β` in the dual space
* `ortho`: Biorthogonality condition `f i (e j) = if i = j then 1 else 0`
* `expansion`: Every `x` equals `∑ i, f i x • e i`, converging along `L`

See `SchauderBasis` for the classical `ℕ`-indexed case with conditional convergence,
and `UnconditionalSchauderBasis` for the unconditional case.
-/
@[ext]
/--
Definition of `GeneralSchauderBasis` / `GeneralSchauderBasis` 的定义

English:
structure GeneralSchauderBasis
  parameters: (β : Type*) (𝕜 : Type*)
  axioms and operations (4):
    - basis : β -> X
    - coord : β -> StrongDual 𝕜 X
    - ortho((i j : β)) : coord i (basis j) = (Pi.single j (1 : 𝕜) : β -> 𝕜) i
    - expansion((x : X)) : HasSum (fun i => (coord i) x • basis i) x L

中文:
结构 GeneralSchauderBasis
  参数: (β : 类型) (𝕜 : 类型)
  公理与运算 (4 个):
    - basis : β -> X
    - coord : β -> StrongDual 𝕜 X
    - ortho((i j : β)) : coord i (basis j) = (依赖函数类型.single j (1 : 𝕜) : β -> 𝕜) i
    - expansion((x : X)) : HasSum (fun i => (coord i) x • basis i) x L
-/
structure GeneralSchauderBasis (β : Type*) (𝕜 : Type*)
    (X : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (L : SummationFilter β) where
  /-- The basis vectors. -/
  basis : β -> X
  /-- Coordinate functionals. -/
  coord : β -> StrongDual 𝕜 X
  /-- Biorthogonality. -/
  ortho (i j : β) : coord i (basis j) = (Pi.single j (1 : 𝕜) : β -> 𝕜) i
  /-- The sum converges to `x` along the provided `SummationFilter L`. -/
  expansion (x : X) : HasSum (fun i => (coord i) x • basis i) x L

variable {β : Type*}
variable {L : SummationFilter β}

/--
Definition of `SchauderBasis` / `SchauderBasis` 的定义

English:
abbreviation SchauderBasis
  signature: (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜]
  body: GeneralSchauderBasis Nat 𝕜 X (SummationFilter.conditional Nat)

中文:
缩写 SchauderBasis
  签名: (𝕜 : 类型) (X : 类型) [NontriviallyNormedField 𝕜]
  定义体: GeneralSchauderBasis Nat 𝕜 X (SummationFilter.conditional Nat)

Depends on / 依赖: GeneralSchauderBasis, SummationFilter, SummationFilter.conditional, conditional
-/
abbrev SchauderBasis (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :=
  GeneralSchauderBasis Nat 𝕜 X (SummationFilter.conditional Nat)

/--
Definition of `UnconditionalSchauderBasis` / `UnconditionalSchauderBasis` 的定义

English:
abbreviation UnconditionalSchauderBasis
  signature: (β : Type*)
  body: GeneralSchauderBasis β 𝕜 X (SummationFilter.unconditional β)

中文:
缩写 UnconditionalSchauderBasis
  签名: (β : 类型)
  定义体: GeneralSchauderBasis β 𝕜 X (SummationFilter.unconditional β)

Depends on / 依赖: GeneralSchauderBasis, SummationFilter, SummationFilter.unconditional, unconditional
-/
abbrev UnconditionalSchauderBasis (β : Type*)
    (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] :=
  GeneralSchauderBasis β 𝕜 X (SummationFilter.unconditional β)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (GeneralSchauderBasis β 𝕜 X L) (fun _ => β -> X)
  body: b.basis

中文:
实例 :
  签名: CoeFun (GeneralSchauderBasis β 𝕜 X L) (fun _ => β -> X)
  定义体: b.basis

Depends on / 依赖: b.basis
-/
instance : CoeFun (GeneralSchauderBasis β 𝕜 X L) (fun _ => β -> X) where
  coe b := b.basis
attribute [coe] GeneralSchauderBasis.basis
namespace GeneralSchauderBasis

variable (b : GeneralSchauderBasis β 𝕜 X L)

/--
theorem `linearIndependent` / 定理 `linearIndependent`

English:
theorem linearIndependent
  statement: LinearIndependent 𝕜 b
  proof: by
  classical
  refine linearIndependent_iff.mpr (fun l hl => l.ext ?_)
  simpa [l.linearCombination_apply, Finsupp.sum, b.ortho, Pi.single_apply] using
    fun i => congr_arg (b.coord i) hl

中文:
定理 linearIndependent
  结论: LinearIndependent 𝕜 b
  证明: by
  classical
  refine linearIndependent_iff.mpr (fun l hl => l.ext ?_)
  simpa [l.linearCombination_apply, Finsupp.sum, b.ortho, Pi.single_apply] using
    fun i => congr_arg (b.coord i) hl

Depends on / 依赖: Finsupp, Finsupp.sum, Pi.single_apply, b.coord, b.ortho, classical, congr_arg, l.ext, l.linearCombination_apply, linearCombination_apply, linearIndependent_iff, linearIndependent_iff.mpr, single_apply
-/
theorem linearIndependent : LinearIndependent 𝕜 b := by
  classical
  refine linearIndependent_iff.mpr (fun l hl => l.ext ?_)
  simpa [l.linearCombination_apply, Finsupp.sum, b.ortho, Pi.single_apply] using
    fun i => congr_arg (b.coord i) hl

/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: (A : Finset β)
  body: ∑ i in A, (b.coord i).smulRight (b i)

中文:
定义 proj
  签名: (A : 有限集 β)
  定义体: ∑ i in A, (b.coord i).smulRight (b i)

Depends on / 依赖: b.coord, smulRight
-/
def proj (A : Finset β) : X ->L[𝕜] X := ∑ i in A, (b.coord i).smulRight (b i)

/-- The projection on the empty set is the zero map. -/
@[simp]
/--
theorem `proj_empty` / 定理 `proj_empty`

English:
theorem proj_empty
  statement: b.proj ∅ = 0
  proof: by simp [proj]

中文:
定理 proj_empty
  结论: b.proj ∅ = 0
  证明: by simp [proj]
-/
theorem proj_empty : b.proj ∅ = 0 := by simp [proj]

/-- The action of the projection on a vector `x`. -/
@[simp]
/--
theorem `proj_apply` / 定理 `proj_apply`

English:
theorem proj_apply
  given: (A : Finset β) (x : X)
  statement: b.proj A x = ∑ i in A, b.coord i x • b i
  proof: by
  simp [proj, _root_.sum_apply, ContinuousLinearMap.smulRight_apply]

中文:
定理 proj_apply
  条件: (A : 有限集 β) (x : X)
  结论: b.proj A x = ∑ i in A, b.coord i x • b i
  证明: by
  simp [proj, _root_.sum_apply, ContinuousLinearMap.smulRight_apply]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.smulRight_apply, _root_, _root_.sum_apply, smulRight_apply, sum_apply
-/
theorem proj_apply (A : Finset β) (x : X) : b.proj A x = ∑ i in A, b.coord i x • b i := by
  simp [proj, _root_.sum_apply, ContinuousLinearMap.smulRight_apply]

open scoped Classical in
/--
theorem `proj_apply_basis_mem` / 定理 `proj_apply_basis_mem`

English:
theorem proj_apply_basis_mem
  given: (A : Finset β) (i : β)
  proof: by
  simp [b.ortho, Pi.single_apply]

中文:
定理 proj_apply_basis_mem
  条件: (A : 有限集 β) (i : β)
  证明: by
  simp [b.ortho, Pi.single_apply]

Depends on / 依赖: Pi.single_apply, b.ortho, single_apply
-/
theorem proj_apply_basis_mem (A : Finset β) (i : β) :
    b.proj A (b i) = if i in A then b i else 0 := by
  simp [b.ortho, Pi.single_apply]

/--
theorem `tendsto_proj` / 定理 `tendsto_proj`

English:
theorem tendsto_proj
  given: (x : X)
  statement: Tendsto (fun A => b.proj A x) L.filter (𝓝 x)
  proof: by
  simpa using! b.expansion x

中文:
定理 tendsto_proj
  条件: (x : X)
  结论: 收敛 (fun A => b.proj A x) L.filter (𝓝 x)
  证明: by
  simpa using! b.expansion x

Depends on / 依赖: b.expansion, expansion
-/
theorem tendsto_proj (x : X) : Tendsto (fun A => b.proj A x) L.filter (𝓝 x) := by
  simpa using! b.expansion x

/--
theorem `range_proj_eq_span` / 定理 `range_proj_eq_span`

English:
theorem range_proj_eq_span
  given: (A : Finset β)
  proof: by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe]; rw [proj_apply]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    use b i
    rw [ContinuousLinearMap.

中文:
定理 range_proj_eq_span
  条件: (A : 有限集 β)
  证明: by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe]; rw [proj_apply]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    use b i
    rw [ContinuousLinearMap.

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_coe, Finset, Finset.mem_coe.mp, Submodule, Submodule.smul_mem, Submodule.span_le, Submodule.subset_span, Submodule.sum_mem, coe_coe, if_pos, le_antisymm, mem_coe, proj_apply, proj_apply_basis_mem, smul_mem, span_le, subset_span, sum_mem
-/
theorem range_proj_eq_span (A : Finset β) :
    (b.proj A).toLinearMap.range = Submodule.span 𝕜 (b '' A) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe]; rw [proj_apply]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    use b i
    rw [ContinuousLinearMap.coe_coe]; rw [proj_apply_basis_mem]; rw [if_pos (Finset.mem_coe.mp hi)]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
theorem `proj_comp` / 定理 `proj_comp`

English:
theorem proj_comp
  given: (A B : Finset β) (x : X)
  statement: b.proj A (b.proj B x) = b.proj (A inter B) x
  proof: by
  simp only [proj_apply, map_sum, map_smul, b.ortho, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', smul_ite, smul_zero, Finset.sum_ite_mem]
  congr 1
  ext _
  simp [and_comm]

中文:
定理 proj_comp
  条件: (A B : 有限集 β) (x : X)
  结论: b.proj A (b.proj B x) = b.proj (A inter B) x
  证明: by
  simp only [proj_apply, map_sum, map_smul, b.ortho, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', smul_ite, smul_zero, Finset.sum_ite_mem]
  congr 1
  ext _
  simp [and_comm]

Depends on / 依赖: Finset, Finset.sum_ite_eq, Finset.sum_ite_mem, Pi.single_apply, and_comm, b.ortho, ite_smul, map_smul, map_sum, one_smul, proj_apply, single_apply, smul_ite, smul_zero, sum_ite_eq, sum_ite_mem, zero_smul
-/
theorem proj_comp (A B : Finset β) (x : X) : b.proj A (b.proj B x) = b.proj (A inter B) x := by
  simp only [proj_apply, map_sum, map_smul, b.ortho, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', smul_ite, smul_zero, Finset.sum_ite_mem]
  congr 1
  ext _
  simp [and_comm]

/--
theorem `finrank_range_proj` / 定理 `finrank_range_proj`

English:
theorem finrank_range_proj
  given: (A : Finset β)
  proof: by
  rw [range_proj_eq_span]; rw [Set.image_eq_range]; rw [finrank_span_eq_card]
  · exact Fintype.card_coe A
  · exact b.linearIndependent.comp (fun i : A => i.val) Subtype.val_injective

中文:
定理 finrank_range_proj
  条件: (A : 有限集 β)
  证明: by
  rw [range_proj_eq_span]; rw [Set.image_eq_range]; rw [finrank_span_eq_card]
  · exact Fintype.card_coe A
  · exact b.linearIndependent.comp (fun i : A => i.val) Subtype.val_injective

Depends on / 依赖: Fintype, Fintype.card_coe, Set.image_eq_range, Subtype, Subtype.val_injective, b.linearIndependent.comp, card_coe, finrank_span_eq_card, i.val, image_eq_range, linearIndependent, range_proj_eq_span, val_injective
-/
theorem finrank_range_proj (A : Finset β) :
    Module.finrank 𝕜 (b.proj A).toLinearMap.range = A.card := by
  rw [range_proj_eq_span]; rw [Set.image_eq_range]; rw [finrank_span_eq_card]
  · exact Fintype.card_coe A
  · exact b.linearIndependent.comp (fun i : A => i.val) Subtype.val_injective

end GeneralSchauderBasis

/-! ### Unconditional Schauder bases -/

namespace UnconditionalSchauderBasis

variable (b : UnconditionalSchauderBasis β 𝕜 X)

/--
Definition of `enormProjBound` / `enormProjBound` 的定义

English:
definition enormProjBound
  signature: : Real>=0∞
  body: ⨆ A : Finset β, ‖b.proj A‖ₑ

中文:
定义 enormProjBound
  签名: : 实数>=0∞
  定义体: ⨆ A : Finset β, ‖b.proj A‖ₑ

Depends on / 依赖: Finset, b.proj
-/
noncomputable def enormProjBound : Real>=0∞ := ⨆ A : Finset β, ‖b.proj A‖ₑ

/--
theorem `enorm_proj_le_enormProjBound` / 定理 `enorm_proj_le_enormProjBound`

English:
theorem enorm_proj_le_enormProjBound
  given: (A : Finset β)
  statement: ‖b.proj A‖ₑ <= b.enormProjBound
  proof: le_iSup (fun A => ‖b.proj A‖ₑ) A

中文:
定理 enorm_proj_le_enormProjBound
  条件: (A : 有限集 β)
  结论: ‖b.proj A‖ₑ <= b.enormProjBound
  证明: le_iSup (fun A => ‖b.proj A‖ₑ) A

Depends on / 依赖: b.proj, le_iSup
-/
theorem enorm_proj_le_enormProjBound (A : Finset β) : ‖b.proj A‖ₑ <= b.enormProjBound :=
  le_iSup (fun A => ‖b.proj A‖ₑ) A

/--
theorem `exists_norm_proj_le` / 定理 `exists_norm_proj_le`

English:
theorem exists_norm_proj_le
  given: [CompleteSpace X]
  statement: exists C : Real, forall A : Finset β, ‖b.proj A‖ <= C
  proof: by
  classical
  apply banach_steinhaus
  intro x
  obtain ⟨A₀, hA₀⟩ := summable_iff_vanishing_norm.mp (b.expansion x).summable 1 zero_lt_one
  use (A₀.powerset.image fun B => ‖b.proj B x‖).sup' ((Finset.powerset_nonempty A₀).image _) id + 1
  intro A
  have hdecomp : b.proj A x = b.proj (A inter A₀

中文:
定理 存在_norm_proj_le
  条件: [完备空间 X]
  结论: 存在 C : 实数, 对任意 A : 有限集 β, ‖b.proj A‖ <= C
  证明: by
  classical
  apply banach_steinhaus
  intro x
  obtain ⟨A₀, hA₀⟩ := summable_iff_vanishing_norm.mp (b.expansion x).summable 1 zero_lt_one
  use (A₀.powerset.image fun B => ‖b.proj B x‖).sup' ((Finset.powerset_nonempty A₀).image _) id + 1
  intro A
  have hdecomp : b.proj A x = b.proj (A inter A₀

Depends on / 依赖: Finset, Finset.disjoint_sdiff_inter, Finset.powerset_nonempty, Finset.sdiff_union_inter, Finset.sum_union, Finset.union_comm, GeneralSchauderBasis, GeneralSchauderBasis.proj_apply, b.expansion, b.proj, banach_steinhaus, classical, disjoint_sdiff_inter, expansion, hdecomp, powerset, powerset.image, powerset_nonempty, proj_apply, sdiff_union_inter
-/
theorem exists_norm_proj_le [CompleteSpace X] : exists C : Real, forall A : Finset β, ‖b.proj A‖ <= C := by
  classical
  apply banach_steinhaus
  intro x
  obtain ⟨A₀, hA₀⟩ := summable_iff_vanishing_norm.mp (b.expansion x).summable 1 zero_lt_one
  use (A₀.powerset.image fun B => ‖b.proj B x‖).sup' ((Finset.powerset_nonempty A₀).image _) id + 1
  intro A
  have hdecomp : b.proj A x = b.proj (A inter A₀) x + b.proj (A \ A₀) x := by
    simp only [GeneralSchauderBasis.proj_apply]
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter A A₀).symm]; rw [Finset.union_comm]; rw [Finset.sdiff_union_inter]
  rw [hdecomp]
  -- -- The projection on the tail (A \ A₀) at `x` is bounded by 1
  have htail : ‖b.proj (A \ A₀) x‖ < 1 := by
    rw [GeneralSchauderBasis.proj_apply]
    exact hA₀ (A \ A₀) Finset.sdiff_disjoint
  apply (norm_add_le _ _).trans (add_le_add _ htail.le)
  -- The projection on (A ∩ A₀) at `x` is bounded by the `sup'`.
exact Finset.le_sup' id Finset.mem_image_of_mem (fun B => ‖b.proj B x‖)
      (Finset.mem_powerset.2 Finset.inter_subset_right)

/--
Definition of `nnnormProjBound` / `nnnormProjBound` 的定义

English:
definition nnnormProjBound
  signature: : Real>=0
  body: ⨆ A : Finset β, ‖b.proj A‖₊

中文:
定义 nnnormProjBound
  签名: : 实数>=0
  定义体: ⨆ A : Finset β, ‖b.proj A‖₊

Depends on / 依赖: Finset, b.proj
-/
noncomputable def nnnormProjBound : Real>=0 := ⨆ A : Finset β, ‖b.proj A‖₊

/--
theorem `bddAbove_range_nnnorm_proj` / 定理 `bddAbove_range_nnnorm_proj`

English:
theorem bddAbove_range_nnnorm_proj
  given: [CompleteSpace X]
  proof: by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hCpos : 0 <= C := by simpa [GeneralSchauderBasis.proj_empty] using hC ∅
  refine ⟨C.toNNReal, ?_⟩
  rintro _ ⟨A, rfl⟩
  rw [← NNReal.coe_le_coe]; rw [Real.coe_toNNReal C hCpos]; rw [coe_nnnorm]
  exact hC A

中文:
定理 bddAbove_range_nnnorm_proj
  条件: [完备空间 X]
  证明: by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hCpos : 0 <= C := by simpa [GeneralSchauderBasis.proj_empty] using hC ∅
  refine ⟨C.toNNReal, ?_⟩
  rintro _ ⟨A, rfl⟩
  rw [← NNReal.coe_le_coe]; rw [Real.coe_toNNReal C hCpos]; rw [coe_nnnorm]
  exact hC A

Depends on / 依赖: C.toNNReal, GeneralSchauderBasis, GeneralSchauderBasis.proj_empty, NNReal, NNReal.coe_le_coe, Real.coe_toNNReal, b.exists_norm_proj_le, coe_le_coe, coe_nnnorm, coe_toNNReal, exists_norm_proj_le, proj_empty, toNNReal
-/
theorem bddAbove_range_nnnorm_proj [CompleteSpace X] :
    BddAbove (Set.range (fun A : Finset β => ‖b.proj A‖₊)) := by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hCpos : 0 <= C := by simpa [GeneralSchauderBasis.proj_empty] using hC ∅
  refine ⟨C.toNNReal, ?_⟩
  rintro _ ⟨A, rfl⟩
  rw [← NNReal.coe_le_coe]; rw [Real.coe_toNNReal C hCpos]; rw [coe_nnnorm]
  exact hC A

/--
theorem `nnnorm_proj_le_nnnormProjBound` / 定理 `nnnorm_proj_le_nnnormProjBound`

English:
theorem nnnorm_proj_le_nnnormProjBound
  given: [CompleteSpace X] (A : Finset β)
  proof: le_ciSup (bddAbove_range_nnnorm_proj b) A

中文:
定理 nnnorm_proj_le_nnnormProjBound
  条件: [完备空间 X] (A : 有限集 β)
  证明: le_ciSup (bddAbove_range_nnnorm_proj b) A

Depends on / 依赖: bddAbove_range_nnnorm_proj, le_ciSup
-/
theorem nnnorm_proj_le_nnnormProjBound [CompleteSpace X] (A : Finset β) :
    ‖b.proj A‖₊ <= b.nnnormProjBound :=
  le_ciSup (bddAbove_range_nnnorm_proj b) A

/--
theorem `norm_proj_le_nnnormProjBound` / 定理 `norm_proj_le_nnnormProjBound`

English:
theorem norm_proj_le_nnnormProjBound
  given: [CompleteSpace X] (A : Finset β)
  proof: mod_cast b.nnnorm_proj_le_nnnormProjBound A

中文:
定理 norm_proj_le_nnnormProjBound
  条件: [完备空间 X] (A : 有限集 β)
  证明: mod_cast b.nnnorm_proj_le_nnnormProjBound A

Depends on / 依赖: b.nnnorm_proj_le_nnnormProjBound, mod_cast, nnnorm_proj_le_nnnormProjBound
-/
theorem norm_proj_le_nnnormProjBound [CompleteSpace X] (A : Finset β) :
    ‖b.proj A‖ <= b.nnnormProjBound :=
  mod_cast b.nnnorm_proj_le_nnnormProjBound A

end UnconditionalSchauderBasis

/-! ### ℕ-indexed Schauder bases with conditional convergence -/

namespace SchauderBasis

variable (b : SchauderBasis 𝕜 X)

/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: (n : Nat)
  body: GeneralSchauderBasis.proj b (Finset.range n)

中文:
定义 proj
  签名: (n : 自然数)
  定义体: GeneralSchauderBasis.proj b (Finset.range n)

Depends on / 依赖: Finset, Finset.range, GeneralSchauderBasis, GeneralSchauderBasis.proj
-/
def proj (n : Nat) : X ->L[𝕜] X := GeneralSchauderBasis.proj b (Finset.range n)

/-- The projection at `0` is the zero map. -/
@[simp]
/--
theorem `proj_zero` / 定理 `proj_zero`

English:
theorem proj_zero
  statement: b.proj 0 = 0
  proof: by rw [proj, Finset.range_zero, GeneralSchauderBasis.proj_empty]

中文:
定理 proj_zero
  结论: b.proj 0 = 0
  证明: by rw [proj, Finset.range_zero, GeneralSchauderBasis.proj_empty]

Depends on / 依赖: Finset, Finset.range_zero, GeneralSchauderBasis, GeneralSchauderBasis.proj_empty, proj_empty, range_zero
-/
theorem proj_zero : b.proj 0 = 0 := by rw [proj, Finset.range_zero, GeneralSchauderBasis.proj_empty]

/-- The action of the projection on a vector. -/
@[simp]
/--
theorem `proj_apply` / 定理 `proj_apply`

English:
theorem proj_apply
  given: (n : Nat) (x : X)
  statement: b.proj n x = ∑ i in Finset.range n, b.coord i x • b i
  proof: by
  rw [proj]; rw [GeneralSchauderBasis.proj_apply]

中文:
定理 proj_apply
  条件: (n : 自然数) (x : X)
  结论: b.proj n x = ∑ i in 有限集.range n, b.coord i x • b i
  证明: by
  rw [proj]; rw [GeneralSchauderBasis.proj_apply]

Depends on / 依赖: GeneralSchauderBasis, GeneralSchauderBasis.proj_apply, proj_apply
-/
theorem proj_apply (n : Nat) (x : X) : b.proj n x = ∑ i in Finset.range n, b.coord i x • b i := by
  rw [proj]; rw [GeneralSchauderBasis.proj_apply]

/--
theorem `proj_apply_basis_mem` / 定理 `proj_apply_basis_mem`

English:
theorem proj_apply_basis_mem
  given: (n i : Nat)
  statement: b.proj n (b i) = if i < n then b i else 0
  proof: by
  rw [proj]; rw [GeneralSchauderBasis.proj_apply_basis_mem]
  simp

中文:
定理 proj_apply_basis_mem
  条件: (n i : 自然数)
  结论: b.proj n (b i) = if i < n then b i else 0
  证明: by
  rw [proj]; rw [GeneralSchauderBasis.proj_apply_basis_mem]
  simp

Depends on / 依赖: GeneralSchauderBasis, GeneralSchauderBasis.proj_apply_basis_mem, proj_apply_basis_mem
-/
theorem proj_apply_basis_mem (n i : Nat) : b.proj n (b i) = if i < n then b i else 0 := by
  rw [proj]; rw [GeneralSchauderBasis.proj_apply_basis_mem]
  simp

/--
theorem `range_proj_eq_span` / 定理 `range_proj_eq_span`

English:
theorem range_proj_eq_span
  given: (n : Nat)
  proof: by
  rw [proj]; rw [GeneralSchauderBasis.range_proj_eq_span]

中文:
定理 range_proj_eq_span
  条件: (n : 自然数)
  证明: by
  rw [proj]; rw [GeneralSchauderBasis.range_proj_eq_span]

Depends on / 依赖: GeneralSchauderBasis, GeneralSchauderBasis.range_proj_eq_span, range_proj_eq_span
-/
theorem range_proj_eq_span (n : Nat) :
    (b.proj n).toLinearMap.range = Submodule.span 𝕜 (b '' ↑(Finset.range n)) := by
  rw [proj]; rw [GeneralSchauderBasis.range_proj_eq_span]

/--
theorem `finrank_range_proj` / 定理 `finrank_range_proj`

English:
theorem finrank_range_proj
  given: (n : Nat)
  proof: by
  rw [proj]; rw [GeneralSchauderBasis.finrank_range_proj]; rw [Finset.card_range]

中文:
定理 finrank_range_proj
  条件: (n : 自然数)
  证明: by
  rw [proj]; rw [GeneralSchauderBasis.finrank_range_proj]; rw [Finset.card_range]

Depends on / 依赖: Finset, Finset.card_range, GeneralSchauderBasis, GeneralSchauderBasis.finrank_range_proj, card_range, finrank_range_proj
-/
theorem finrank_range_proj (n : Nat) :
    Module.finrank 𝕜 (b.proj n).toLinearMap.range = n := by
  rw [proj]; rw [GeneralSchauderBasis.finrank_range_proj]; rw [Finset.card_range]

/--
theorem `tendsto_proj` / 定理 `tendsto_proj`

English:
theorem tendsto_proj
  given: (x : X)
  statement: Tendsto (fun n => b.proj n x) atTop (𝓝 x)
  proof: by
  have := GeneralSchauderBasis.tendsto_proj b x
  rwa [SummationFilter.conditional_filter_eq_map_range] at this

中文:
定理 tendsto_proj
  条件: (x : X)
  结论: 收敛 (fun n => b.proj n x) atTop (𝓝 x)
  证明: by
  have := GeneralSchauderBasis.tendsto_proj b x
  rwa [SummationFilter.conditional_filter_eq_map_range] at this

Depends on / 依赖: GeneralSchauderBasis, GeneralSchauderBasis.tendsto_proj, SummationFilter, SummationFilter.conditional_filter_eq_map_range, conditional_filter_eq_map_range, tendsto_proj
-/
theorem tendsto_proj (x : X) : Tendsto (fun n => b.proj n x) atTop (𝓝 x) := by
  have := GeneralSchauderBasis.tendsto_proj b x
  rwa [SummationFilter.conditional_filter_eq_map_range] at this

/--
theorem `proj_comp` / 定理 `proj_comp`

English:
theorem proj_comp
  given: (n m : Nat) (x : X)
  statement: b.proj n (b.proj m x) = b.proj (min n m) x
  proof: by
  simp only [proj, GeneralSchauderBasis.proj_comp]
  congr 2
  ext _
  simp only [Finset.mem_inter, Finset.mem_range]
  omega

中文:
定理 proj_comp
  条件: (n m : 自然数) (x : X)
  结论: b.proj n (b.proj m x) = b.proj (最小值 n m) x
  证明: by
  simp only [proj, GeneralSchauderBasis.proj_comp]
  congr 2
  ext _
  simp only [Finset.mem_inter, Finset.mem_range]
  omega

Depends on / 依赖: Finset, Finset.mem_inter, Finset.mem_range, GeneralSchauderBasis, GeneralSchauderBasis.proj_comp, mem_inter, mem_range, proj_comp
-/
theorem proj_comp (n m : Nat) (x : X) : b.proj n (b.proj m x) = b.proj (min n m) x := by
  simp only [proj, GeneralSchauderBasis.proj_comp]
  congr 2
  ext _
  simp only [Finset.mem_inter, Finset.mem_range]
  omega

/--
theorem `exists_norm_proj_le` / 定理 `exists_norm_proj_le`

English:
theorem exists_norm_proj_le
  given: [CompleteSpace X]
  statement: exists C : Real, forall n : Nat, ‖b.proj n‖ <= C
  proof: by
  apply banach_steinhaus
  intro x
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto (fun n => b.proj n x) (tendsto_proj b x))
  exact ⟨M, Set.forall_mem_range.mp hM⟩

中文:
定理 存在_norm_proj_le
  条件: [完备空间 X]
  结论: 存在 C : 实数, 对任意 n : 自然数, ‖b.proj n‖ <= C
  证明: by
  apply banach_steinhaus
  intro x
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto (fun n => b.proj n x) (tendsto_proj b x))
  exact ⟨M, Set.forall_mem_range.mp hM⟩

Depends on / 依赖: Metric, Metric.isBounded_range_of_tendsto, Set.forall_mem_range.mp, b.proj, banach_steinhaus, forall_mem_range, isBounded_iff_forall_norm_le, isBounded_iff_forall_norm_le.mp, isBounded_range_of_tendsto, tendsto_proj
-/
theorem exists_norm_proj_le [CompleteSpace X] : exists C : Real, forall n : Nat, ‖b.proj n‖ <= C := by
  apply banach_steinhaus
  intro x
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto (fun n => b.proj n x) (tendsto_proj b x))
  exact ⟨M, Set.forall_mem_range.mp hM⟩

/--
Definition of `enormProjBound` / `enormProjBound` 的定义

English:
definition enormProjBound
  signature: : Real>=0∞
  body: ⨆ n, ‖b.proj n‖ₑ

中文:
定义 enormProjBound
  签名: : 实数>=0∞
  定义体: ⨆ n, ‖b.proj n‖ₑ

Depends on / 依赖: b.proj
-/
noncomputable def enormProjBound : Real>=0∞ := ⨆ n, ‖b.proj n‖ₑ

/--
theorem `enorm_proj_le_enormProjBound` / 定理 `enorm_proj_le_enormProjBound`

English:
theorem enorm_proj_le_enormProjBound
  given: (n : Nat)
  statement: ‖b.proj n‖ₑ <= b.enormProjBound
  proof: le_iSup (fun i => ‖b.proj i‖ₑ) n

中文:
定理 enorm_proj_le_enormProjBound
  条件: (n : 自然数)
  结论: ‖b.proj n‖ₑ <= b.enormProjBound
  证明: le_iSup (fun i => ‖b.proj i‖ₑ) n

Depends on / 依赖: b.proj, le_iSup
-/
theorem enorm_proj_le_enormProjBound (n : Nat) : ‖b.proj n‖ₑ <= b.enormProjBound :=
  le_iSup (fun i => ‖b.proj i‖ₑ) n

/--
Definition of `nnnormProjBound` / `nnnormProjBound` 的定义

English:
definition nnnormProjBound
  signature: : Real>=0
  body: ⨆ n, ‖b.proj n‖₊

中文:
定义 nnnormProjBound
  签名: : 实数>=0
  定义体: ⨆ n, ‖b.proj n‖₊

Depends on / 依赖: b.proj
-/
noncomputable def nnnormProjBound : Real>=0 := ⨆ n, ‖b.proj n‖₊

/--
theorem `bddAbove_range_nnnorm_proj` / 定理 `bddAbove_range_nnnorm_proj`

English:
theorem bddAbove_range_nnnorm_proj
  given: [CompleteSpace X]
  proof: by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hCpos : 0 <= C := by simpa [proj_zero] using hC 0
  refine ⟨C.toNNReal, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [← NNReal.coe_le_coe]; rw [Real.coe_toNNReal C hCpos]; rw [coe_nnnorm]
  exact hC n

中文:
定理 bddAbove_range_nnnorm_proj
  条件: [完备空间 X]
  证明: by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hCpos : 0 <= C := by simpa [proj_zero] using hC 0
  refine ⟨C.toNNReal, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [← NNReal.coe_le_coe]; rw [Real.coe_toNNReal C hCpos]; rw [coe_nnnorm]
  exact hC n

Depends on / 依赖: C.toNNReal, NNReal, NNReal.coe_le_coe, Real.coe_toNNReal, b.exists_norm_proj_le, coe_le_coe, coe_nnnorm, coe_toNNReal, exists_norm_proj_le, proj_zero, toNNReal
-/
theorem bddAbove_range_nnnorm_proj [CompleteSpace X] :
    BddAbove (Set.range (fun n : Nat => ‖b.proj n‖₊)) := by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hCpos : 0 <= C := by simpa [proj_zero] using hC 0
  refine ⟨C.toNNReal, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [← NNReal.coe_le_coe]; rw [Real.coe_toNNReal C hCpos]; rw [coe_nnnorm]
  exact hC n

/--
theorem `nnnorm_proj_le_nnnormProjBound` / 定理 `nnnorm_proj_le_nnnormProjBound`

English:
theorem nnnorm_proj_le_nnnormProjBound
  given: [CompleteSpace X] (n : Nat)
  proof: le_ciSup (bddAbove_range_nnnorm_proj b) n

中文:
定理 nnnorm_proj_le_nnnormProjBound
  条件: [完备空间 X] (n : 自然数)
  证明: le_ciSup (bddAbove_range_nnnorm_proj b) n

Depends on / 依赖: bddAbove_range_nnnorm_proj, le_ciSup
-/
theorem nnnorm_proj_le_nnnormProjBound [CompleteSpace X] (n : Nat) :
    ‖b.proj n‖₊ <= b.nnnormProjBound :=
  le_ciSup (bddAbove_range_nnnorm_proj b) n

/--
theorem `norm_proj_le_nnnormProjBound` / 定理 `norm_proj_le_nnnormProjBound`

English:
theorem norm_proj_le_nnnormProjBound
  given: [CompleteSpace X] (n : Nat)
  proof: mod_cast b.nnnorm_proj_le_nnnormProjBound n

中文:
定理 norm_proj_le_nnnormProjBound
  条件: [完备空间 X] (n : 自然数)
  证明: mod_cast b.nnnorm_proj_le_nnnormProjBound n

Depends on / 依赖: b.nnnorm_proj_le_nnnormProjBound, mod_cast, nnnorm_proj_le_nnnormProjBound
-/
theorem norm_proj_le_nnnormProjBound [CompleteSpace X] (n : Nat) :
    ‖b.proj n‖ <= b.nnnormProjBound :=
  mod_cast b.nnnorm_proj_le_nnnormProjBound n

/-!
### Construction of Schauder basis

We explain how to construct a Schauder basis from a sequence `P n` of projections
satisfying `P n ∘ P m = P (min n m)`, converging to the identity pointwise, and such that each
`P (n+1) - P n` has rank one. The idea is to define the basis vectors as
`e n = (P (n+1) - P n) x` for some `x` such that this is non-zero, and then
show that these vectors form a Schauder basis. -/

/--
Definition of `succSub` / `succSub` 的定义

English:
definition succSub
  signature: (P : Nat -> X ->L[𝕜] X) (n : Nat)
  body: P (n + 1) - P n

中文:
定义 succSub
  签名: (P : 自然数 -> X ->L[𝕜] X) (n : 自然数)
  定义体: P (n + 1) - P n
-/
def succSub (P : Nat -> X ->L[𝕜] X) (n : Nat) : X ->L[𝕜] X := P (n + 1) - P n

/-- The sum of `succSub` operators up to `n` equals `P n`. -/
@[simp]
/--
lemma `sum_succSub` / 引理 `sum_succSub`

English:
lemma sum_succSub
  given: (P : Nat -> X ->L[𝕜] X) (h0 : P 0 = 0) (n : Nat)
  proof: by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Finset.sum_range_succ, ih, succSub]; abel

中文:
引理 sum_succSub
  条件: (P : 自然数 -> X ->L[𝕜] X) (h0 : P 0 = 0) (n : 自然数)
  证明: by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Finset.sum_range_succ, ih, succSub]; abel

Depends on / 依赖: Finset, Finset.sum_range_succ, succSub, sum_range_succ
-/
lemma sum_succSub (P : Nat -> X ->L[𝕜] X) (h0 : P 0 = 0) (n : Nat) :
    ∑ i in Finset.range n, succSub P i = P n := by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Finset.sum_range_succ, ih, succSub]; abel

/--
lemma `succSub_ortho` / 引理 `succSub_ortho`

English:
lemma succSub_ortho
  statement: {P : Nat -> X ->L[𝕜] X} (hcomp : forall n m, forall x : X, P n (P m x) = P (min n m) x)
  proof: by
  simp only [succSub, _root_.sub_apply, map_sub, hcomp,
    Nat.add_min_add_right]
  split_ifs with h
  · rw [h, min_self, min_eq_right (Nat.le_succ j), Nat.min_eq_left (Nat.le_succ j)]
    abel
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · rw [min_eq_left_of_lt h', min_eq_left (Nat.succ_le_

中文:
引理 succSub_ortho
  结论: {P : 自然数 -> X ->L[𝕜] X} (hcomp : 对任意 n m, 对任意 x : X, P n (P m x) = P (最小值 n m) x)
  证明: by
  simp only [succSub, _root_.sub_apply, map_sub, hcomp,
    Nat.add_min_add_right]
  split_ifs with h
  · rw [h, min_self, min_eq_right (Nat.le_succ j), Nat.min_eq_left (Nat.le_succ j)]
    abel
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · rw [min_eq_left_of_lt h', min_eq_left (Nat.succ_le_

Depends on / 依赖: Nat.add_min_add_right, Nat.le_succ, Nat.lt_or_gt_of_ne, Nat.lt_succ_of_lt, Nat.min_eq_left, Nat.succ_le_of_lt, _root_, _root_.sub_apply, add_min_add_right, le_succ, lt_or_gt_of_ne, lt_succ_of_lt, map_sub, min_eq_left, min_eq_left_of_lt, min_eq_right, min_eq_right_of_lt, min_self, split_ifs, sub_apply
-/
lemma succSub_ortho {P : Nat -> X ->L[𝕜] X} (hcomp : forall n m, forall x : X, P n (P m x) = P (min n m) x)
    (i j : Nat) (x : X) : succSub P i (succSub P j x) = if i = j then succSub P j x else 0 := by
  simp only [succSub, _root_.sub_apply, map_sub, hcomp,
    Nat.add_min_add_right]
  split_ifs with h
  · rw [h, min_self, min_eq_right (Nat.le_succ j), Nat.min_eq_left (Nat.le_succ j)]
    abel
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · rw [min_eq_left_of_lt h', min_eq_left (Nat.succ_le_of_lt h'),
        min_eq_left_of_lt (Nat.lt_succ_of_lt h')]
      abel
    · rw [min_eq_right_of_lt h', min_eq_right (Nat.succ_le_of_lt h'),
        min_eq_right_of_lt (Nat.lt_succ_of_lt h')]
      abel

/--
lemma `finrank_range_succSub_eq_one` / 引理 `finrank_range_succSub_eq_one`

English:
lemma finrank_range_succSub_eq_one
  statement: {P : Nat -> X ->L[𝕜] X}
  proof: by
  let U := (succSub P n).toLinearMap.range
  let V := (P n).toLinearMap.range
  let W := (P (n + 1)).toLinearMap.range
  have hV : V <= W := by
    rintro _ ⟨y, rfl⟩
    exact ⟨P n y, by simp [ContinuousLinearMap.coe_coe, hcomp]⟩
  have hUW : U <= W := by
    rintro _ ⟨y, rfl⟩
    exact Submodule

中文:
引理 finrank_range_succSub_eq_one
  结论: {P : 自然数 -> X ->L[𝕜] X}
  证明: by
  let U := (succSub P n).toLinearMap.range
  let V := (P n).toLinearMap.range
  let W := (P (n + 1)).toLinearMap.range
  have hV : V <= W := by
    rintro _ ⟨y, rfl⟩
    exact ⟨P n y, by simp [ContinuousLinearMap.coe_coe, hcomp]⟩
  have hUW : U <= W := by
    rintro _ ⟨y, rfl⟩
    exact Submodule

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_coe, Submodule, Submodule.add_mem_sup, Submodule.sub_mem, add_mem_sup, coe_coe, le_antisymm, sub_add_cancel, sub_mem, succSub, toLinearMap, toLinearMap.range
-/
lemma finrank_range_succSub_eq_one {P : Nat -> X ->L[𝕜] X}
    (hrank : forall n, Module.finrank 𝕜 (P n).toLinearMap.range = n)
    (hcomp : forall n m, forall x : X, P n (P m x) = P (min n m) x) (n : Nat) :
    Module.finrank 𝕜 (succSub P n).toLinearMap.range = 1 := by
  let U := (succSub P n).toLinearMap.range
  let V := (P n).toLinearMap.range
  let W := (P (n + 1)).toLinearMap.range
  have hV : V <= W := by
    rintro _ ⟨y, rfl⟩
    exact ⟨P n y, by simp [ContinuousLinearMap.coe_coe, hcomp]⟩
  have hUW : U <= W := by
    rintro _ ⟨y, rfl⟩
    exact Submodule.sub_mem W ⟨y, rfl⟩ (hV ⟨y, rfl⟩)
  have hW : W = U ⊔ V := by
    apply le_antisymm
    · rintro x ⟨y, hy⟩
      rw [← hy]; rw [ContinuousLinearMap.coe_coe]; rw [← sub_add_cancel ((P (n + 1)) y) ((P n) y)]
      exact Submodule.add_mem_sup ⟨y, rfl⟩ ⟨y, rfl⟩
    · exact sup_le hUW hV
  have hdisj : U ⊓ V = ⊥ := eq_bot_iff.mpr fun x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ => by
    simp only [Submodule.mem_bot]
    calc x = (P n) x := by rw [← hz, ContinuousLinearMap.coe_coe, hcomp, min_self]
         _ = 0 := by rw [← hy, ContinuousLinearMap.coe_coe]; simp [succSub, map_sub, hcomp]
  have : FiniteDimensional 𝕜 W := .of_finrank_pos (by rw [hrank]; exact Nat.succ_pos n)
  have : FiniteDimensional 𝕜 U := Submodule.finiteDimensional_of_le hUW
  have : FiniteDimensional 𝕜 V := Submodule.finiteDimensional_of_le hV
  have h_dim := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [hdisj]; rw [finrank_bot]; rw [add_zero]; rw [← hW]; rw [hrank]; rw [hrank]; rw [Nat.add_comm] at h_dim
  exact Nat.add_right_cancel h_dim.symm

variable (𝕜 X) in
/--
Definition of `RankOneDecomposition` / `RankOneDecomposition` 的定义

English:
structure RankOneDecomposition
  parameters: where
  axioms and operations (8):
    - P : Nat -> X ->L[𝕜] X
    - e : Nat -> X
    - proj_zero : P 0 = 0
    - finrank_range((n : Nat)) : Module.finrank 𝕜 (P n).toLinearMap.range = n
    - proj_comp((n m : Nat) (x : X)) : P n (P m x) = P (min n m) x
    - proj_tendsto((x : X)) : Tendsto (fun n => P n x) atTop (𝓝 x)
    - e_mem_range((n : Nat)) : e n in (succSub P n).toLinearMap.range
    - e_ne_zero((n : Nat)) : e n != 0

中文:
结构 RankOneDecomposition
  参数: where
  公理与运算 (8 个):
    - P : 自然数 -> X ->L[𝕜] X
    - e : 自然数 -> X
    - proj_zero : P 0 = 0
    - finrank_range((n : 自然数)) : 模.finrank 𝕜 (P n).toLinearMap.range = n
    - proj_comp((n m : 自然数) (x : X)) : P n (P m x) = P (最小值 n m) x
    - proj_tendsto((x : X)) : 收敛 (fun n => P n x) atTop (𝓝 x)
    - e_mem_range((n : 自然数)) : e n in (succSub P n).toLinearMap.range
    - e_ne_zero((n : 自然数)) : e n != 0
-/
structure RankOneDecomposition where
  /-- The sequence of finite-rank projections. -/
  P : Nat -> X ->L[𝕜] X
  /-- The sequence of candidate basis vectors. -/
  e : Nat -> X
  /-- The projections start at `0`. -/
  proj_zero : P 0 = 0
  /-- The `n`-th projection has rank `n`. -/
  finrank_range (n : Nat) : Module.finrank 𝕜 (P n).toLinearMap.range = n
  /-- The projections commute and are nested `P n (P m) = P (min n m)`. -/
  proj_comp (n m : Nat) (x : X) : P n (P m x) = P (min n m) x
  /-- The projections converge pointwise to the identity. -/
  proj_tendsto (x : X) : Tendsto (fun n => P n x) atTop (𝓝 x)
  /-- The vector `e_n` lies in the range of the operator `succSub P n = P (n+1) - P n`. -/
  e_mem_range (n : Nat) : e n in (succSub P n).toLinearMap.range
  /-- The vector `e_n` is non-zero. -/
  e_ne_zero (n : Nat) : e n != 0

namespace RankOneDecomposition

variable (D : RankOneDecomposition 𝕜 X)

/--
lemma `exists_coeff` / 引理 `exists_coeff`

English:
lemma exists_coeff
  given: (n : Nat) (x : X)
  proof: by
  let S := (succSub D.P n).toLinearMap
  have hrank : Module.finrank 𝕜 S.range = 1 :=
    finrank_range_succSub_eq_one D.finrank_range D.proj_comp n
  have : FiniteDimensional 𝕜 S.range := .of_finrank_pos (hrank.symm ▸ zero_lt_one)
  have hspan : Submodule.span 𝕜 {D.e n} = S.range := by
    apply

中文:
引理 存在_coeff
  条件: (n : 自然数) (x : X)
  证明: by
  let S := (succSub D.P n).toLinearMap
  have hrank : Module.finrank 𝕜 S.range = 1 :=
    finrank_range_succSub_eq_one D.finrank_range D.proj_comp n
  have : FiniteDimensional 𝕜 S.range := .of_finrank_pos (hrank.symm ▸ zero_lt_one)
  have hspan : Submodule.span 𝕜 {D.e n} = S.range := by
    apply

Depends on / 依赖: D.e_mem_range, D.e_ne_zero, D.finrank_range, D.proj_comp, FiniteDimensional, Module, Module.finrank, S.range, Submodule, Submodule.eq_of_le_of_finrank_eq, Submodule.mem_span_singleton.mp, Submodule.span, Submodule.span_singleton_le_iff_mem, e_mem_range, e_ne_zero, eq_of_le_of_finrank_eq, finrank, finrank_range, finrank_range_succSub_eq_one, finrank_span_singleton
-/
lemma exists_coeff (n : Nat) (x : X) :
    exists c : 𝕜, c • D.e n = (succSub D.P n) x := by
  let S := (succSub D.P n).toLinearMap
  have hrank : Module.finrank 𝕜 S.range = 1 :=
    finrank_range_succSub_eq_one D.finrank_range D.proj_comp n
  have : FiniteDimensional 𝕜 S.range := .of_finrank_pos (hrank.symm ▸ zero_lt_one)
  have hspan : Submodule.span 𝕜 {D.e n} = S.range := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (D.e_mem_range n)
    · simp [hrank, finrank_span_singleton (D.e_ne_zero n)]
  exact Submodule.mem_span_singleton.mp (hspan.symm ▸ LinearMap.mem_range_self S x)

/--
Definition of `basisCoeff` / `basisCoeff` 的定义

English:
definition basisCoeff
  signature: (n : Nat) (x : X)
  body: Classical.choose (exists_coeff D n x)

中文:
定义 basisCoeff
  签名: (n : 自然数) (x : X)
  定义体: Classical.choose (exists_coeff D n x)

Depends on / 依赖: Classical, Classical.choose, exists_coeff
-/
def basisCoeff (n : Nat) (x : X) : 𝕜 :=
  Classical.choose (exists_coeff D n x)

/-- The coefficient satisfies `basisCoeff D n x • D.e n = (succSub D.P n) x`. -/
@[simp]
/--
lemma `basisCoeff_spec` / 引理 `basisCoeff_spec`

English:
lemma basisCoeff_spec
  given: (n : Nat) (x : X)
  proof: Classical.choose_spec (exists_coeff D n x)

中文:
引理 basisCoeff_spec
  条件: (n : 自然数) (x : X)
  证明: Classical.choose_spec (exists_coeff D n x)

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_coeff
-/
lemma basisCoeff_spec (n : Nat) (x : X) :
    basisCoeff D n x • D.e n = (succSub D.P n) x :=
  Classical.choose_spec (exists_coeff D n x)

/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: : SchauderBasis 𝕜 X
  body: let coeff := basisCoeff D
  have hcoeff : forall n x, (succSub D.P n) x = coeff n x • D.e n := fun n x =>
    (basisCoeff_spec D n x).symm
  { basis := D.e
    coord := fun n => LinearMap.mkContinuous
      { toFun := coeff n
map_add' := fun x y => smul_left_injective 𝕜 (D.e_ne_zero n) by
          

中文:
定义 basis
  签名: : SchauderBasis 𝕜 X
  定义体: let coeff := basisCoeff D
  have hcoeff : forall n x, (succSub D.P n) x = coeff n x • D.e n := fun n x =>
    (basisCoeff_spec D n x).symm
  { basis := D.e
    coord := fun n => LinearMap.mkContinuous
      { toFun := coeff n
map_add' := fun x y => smul_left_injective 𝕜 (D.e_ne_zero n) by
          

Depends on / 依赖: D.e_ne_zero, LinearMap, LinearMap.mkContinuous, RingHom, RingHom.id_apply, add_smul, basisCoeff, basisCoeff_spec, e_ne_zero, hcoeff, id_apply, map_add, map_smul, mkContinuous, smul_eq_mul, smul_left_injective, smul_smul, succSub
-/
def basis : SchauderBasis 𝕜 X :=
  let coeff := basisCoeff D
  have hcoeff : forall n x, (succSub D.P n) x = coeff n x • D.e n := fun n x =>
    (basisCoeff_spec D n x).symm
  { basis := D.e
    coord := fun n => LinearMap.mkContinuous
      { toFun := coeff n
map_add' := fun x y => smul_left_injective 𝕜 (D.e_ne_zero n) by
          simp only [add_smul, ← hcoeff, map_add]
map_smul' := fun c x => smul_left_injective 𝕜 (D.e_ne_zero n) by
          dsimp only [RingHom.id_apply]
          rw [smul_eq_mul]; rw [← smul_smul]; rw [← hcoeff]; rw [← hcoeff]; rw [map_smul] }
      (‖succSub D.P n‖ / ‖D.e n‖)
      (fun x => by
        rw [div_mul_eq_mul_div]; rw [le_div_iff₀ (norm_pos_iff.mpr (D.e_ne_zero n))]
        calc ‖coeff n x‖ * ‖D.e n‖ = ‖coeff n x • D.e n‖ := (norm_smul _ _).symm
          _ = ‖(succSub D.P n) x‖ := by rw [hcoeff]
          _ <= ‖succSub D.P n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _)
ortho := fun i j => smul_left_injective 𝕜 (D.e_ne_zero i) by
      obtain ⟨x, hx⟩ : exists x, (succSub D.P j) x = D.e j := D.e_mem_range j
      simp only [mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← hcoeff]; rw [← hx]; rw [succSub_ortho D.proj_comp]; rw [hx]
      simp only [Pi.single_apply]
      split_ifs with h <;> simp [h]
    expansion := fun x => by
      rw [HasSum]; rw [SummationFilter.conditional_filter_eq_map_range]; rw [tendsto_map'_iff]
      exact (D.proj_tendsto x).congr fun n => by
        simp only [Function.comp, LinearMap.coe_mk, AddHom.coe_mk,
                   LinearMap.mkContinuous_apply, ← hcoeff]
        rw [← _root_.sum_apply]; rw [sum_succSub D.P D.proj_zero] }

/-- The projections of the constructed basis correspond to the input data `D.P`. -/
@[simp]
/--
theorem `basis_proj` / 定理 `basis_proj`

English:
theorem basis_proj
  statement: (basis D).proj = D.P
  proof: by
  ext n _
  rw [SchauderBasis.proj_apply]; rw [← sum_succSub D.P D.proj_zero n]
  simp only [_root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp [basis, mkContinuous_apply, IsLinearMap.mk'_apply]
  rw [basisCoeff_spec]

中文:
定理 basis_proj
  结论: (basis D).proj = D.P
  证明: by
  ext n _
  rw [SchauderBasis.proj_apply]; rw [← sum_succSub D.P D.proj_zero n]
  simp only [_root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp [basis, mkContinuous_apply, IsLinearMap.mk'_apply]
  rw [basisCoeff_spec]

Depends on / 依赖: D.proj_zero, Finset, Finset.sum_congr, IsLinearMap, IsLinearMap.mk, SchauderBasis, SchauderBasis.proj_apply, _apply, _root_, _root_.sum_apply, basisCoeff_spec, mkContinuous_apply, proj_apply, proj_zero, sum_apply, sum_congr, sum_succSub
-/
theorem basis_proj : (basis D).proj = D.P := by
  ext n _
  rw [SchauderBasis.proj_apply]; rw [← sum_succSub D.P D.proj_zero n]
  simp only [_root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp [basis, mkContinuous_apply, IsLinearMap.mk'_apply]
  rw [basisCoeff_spec]

/-- The sequence of the constructed basis corresponds to the input data `D.e`. -/
@[simp]
/--
theorem `basis_coe` / 定理 `basis_coe`

English:
theorem basis_coe
  statement: ⇑(basis D) = D.e
  proof: rfl

中文:
定理 basis_coe
  结论: ⇑(basis D) = D.e
  证明: rfl
-/
theorem basis_coe : ⇑(basis D) = D.e :=
  rfl

end RankOneDecomposition

end SchauderBasis
