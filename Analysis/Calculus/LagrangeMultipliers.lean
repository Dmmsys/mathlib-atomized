/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Lagrange multipliers

In this file we formalize the
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) method of solving
conditional extremum problems: if a function `φ` has a local extremum at `x₀` on the set
`f ⁻¹' {f x₀}`, `f x = (f₀ x, ..., fₙ₋₁ x)`, then the differentials of `fₖ` and `φ` are linearly
dependent. First we formulate a geometric version of this theorem which does not rely on the
target space being `ℝⁿ`, then restate it in terms of coordinates.

## TODO

Formalize Karush-Kuhn-Tucker theorem

## Tags

lagrange multiplier, local extremum

-/

public section


open Filter Set

open scoped Topology Filter

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] {f : E -> F} {φ : E -> Real} {x₀ : E}
  {f' : E ->L[Real] F} {φ' : StrongDual Real E}

/--
theorem `IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt` / 定理 `IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt`

English:
theorem IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt
  proof: by
  intro htop
  set fφ := fun x => (f x, φ x)
  have A : map φ (𝓝[f ⁻¹' {f x₀}] x₀) = 𝓝 (φ x₀) := by
    change map (Prod.snd ∘ fφ) (𝓝[fφ ⁻¹' {p | p.1 = f x₀}] x₀) = 𝓝 (φ x₀)
    rw [← map_map]; rw [nhdsWithin]; rw [map_inf_principal_preimage]; rw [(hf'.prodMk hφ').map_nhds_eq_of_surj htop]
    exact map_snd_nhdsWithin _
  exact hextr.not_nhds_le_map A.ge

中文:
定理 IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt
  证明: by
  intro htop
  set fφ := fun x => (f x, φ x)
  have A : map φ (𝓝[f ⁻¹' {f x₀}] x₀) = 𝓝 (φ x₀) := by
    change map (Prod.snd ∘ fφ) (𝓝[fφ ⁻¹' {p | p.1 = f x₀}] x₀) = 𝓝 (φ x₀)
    rw [← map_map]; rw [nhdsWithin]; rw [map_inf_principal_preimage]; rw [(hf'.prodMk hφ').map_nhds_eq_of_surj htop]
    exact map_snd_nhdsWithin _
  exact hextr.not_nhds_le_map A.ge

Depends on / 依赖: A.ge, CStarRing, CStarRing.norm_self_mul_star, MulOpposite, MulOpposite.unop, Prod.snd, hextr.not_nhds_le_map, map_inf_principal_preimage, map_map, map_nhds_eq_of_surj, map_snd_nhdsWithin, nhdsWithin, norm_self_mul_star, not_nhds_le_map, prodMk
-/
theorem IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt
    (hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀) (hf' : HasStrictFDerivAt f f' x₀)
    (hφ' : HasStrictFDerivAt φ φ' x₀) : (f'.prod φ').range != ⊤ := by
  intro htop
  set fφ := fun x => (f x, φ x)
  have A : map φ (𝓝[f ⁻¹' {f x₀}] x₀) = 𝓝 (φ x₀) := by
    change map (Prod.snd ∘ fφ) (𝓝[fφ ⁻¹' {p | p.1 = f x₀}] x₀) = 𝓝 (φ x₀)
    rw [← map_map]; rw [nhdsWithin]; rw [map_inf_principal_preimage]; rw [(hf'.prodMk hφ').map_nhds_eq_of_surj htop]
    exact map_snd_nhdsWithin _
  exact hextr.not_nhds_le_map A.ge

/--
theorem `IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt` / 定理 `IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt`

English:
theorem IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt
  proof: by
  rcases Submodule.exists_le_ker_of_lt_top _
      (lt_top_iff_ne_top.2 <| hextr.range_ne_top_of_hasStrictFDerivAt hf' hφ') with
    ⟨Λ', h0, hΛ'⟩
  set e : ((F ->ₗ[Real] Real) × Real) ≃ₗ[Real] F × Real ->ₗ[Real] Real :=
    ((LinearEquiv.refl Real (F ->ₗ[Real] Real)).prodCongr (LinearMap.ringLmapEquivSelf Real Real Real).symm).trans
      (LinearMap.coprodEquiv Real)
  rcases e.surjective Λ' with ⟨⟨Λ, Λ₀⟩, rfl⟩
  refine ⟨Λ, Λ₀, e.map_ne_zero_iff.1 h0, fun x => ?_⟩
  convert! LinearMap.congr_fun (LinearMap.range_le_ker_iff.1 hΛ') x using 1
    -- squeezed `simp [mul_comm]` to speed up elaboration

  -- squeezed `simp [mul_comm]` to speed up elaboration
  simp only [e, smul_eq_mul, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, LinearMap.ringLmapEquivSelf_symm_apply, LinearMap.coprodEquiv_apply,
    ContinuousLinearMap.coe_prod, LinearMap.coprod_comp_prod, LinearMap.add_apply,
    LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply, LinearMap.coe_smulRight,
    Module.End.one_apply, mul_comm]

中文:
定理 IsLocalExtrOn.存在_linear_map_of_hasStrictFDerivAt
  证明: by
  rcases Submodule.exists_le_ker_of_lt_top _
      (lt_top_iff_ne_top.2 <| hextr.range_ne_top_of_hasStrictFDerivAt hf' hφ') with
    ⟨Λ', h0, hΛ'⟩
  set e : ((F ->ₗ[Real] Real) × Real) ≃ₗ[Real] F × Real ->ₗ[Real] Real :=
    ((LinearEquiv.refl Real (F ->ₗ[Real] Real)).prodCongr (LinearMap.ringLmapEquivSelf Real Real Real).symm).trans
      (LinearMap.coprodEquiv Real)
  rcases e.surjective Λ' with ⟨⟨Λ, Λ₀⟩, rfl⟩
  refine ⟨Λ, Λ₀, e.map_ne_zero_iff.1 h0, fun x => ?_⟩
  convert! LinearMap.congr_fun (LinearMap.range_le_ker_iff.1 hΛ') x using 1
    -- squeezed `simp [mul_comm]` to speed up elaboration

  -- squeezed `simp [mul_comm]` to speed up elaboration
  simp only [e, smul_eq_mul, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, LinearMap.ringLmapEquivSelf_symm_apply, LinearMap.coprodEquiv_apply,
    ContinuousLinearMap.coe_prod, LinearMap.coprod_comp_prod, LinearMap.add_apply,
    LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply, LinearMap.coe_smulRight,
    Module.End.one_apply, mul_comm]

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, LinearMap, LinearMap.congr_fun, LinearMap.coprodEquiv, LinearMap.range_le_ker_if, LinearMap.ringLmapEquivSelf, Submodule, Submodule.exists_le_ker_of_lt_top, congr_fun, convert, coprodEquiv, e.map_ne_zero_iff, e.surjective, exists_le_ker_of_lt_top, hextr.range_ne_top_of_hasStrictFDerivAt, lt_top_iff_ne_top, map_ne_zero_iff, prodCongr, range_le_ker_if
-/
theorem IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt
    (hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀) (hf' : HasStrictFDerivAt f f' x₀)
    (hφ' : HasStrictFDerivAt φ φ' x₀) :
    exists (Λ : Module.Dual Real F) (Λ₀ : Real), (Λ, Λ₀) != 0 ∧ forall x, Λ (f' x) + Λ₀ • φ' x = 0 := by
  rcases Submodule.exists_le_ker_of_lt_top _
      (lt_top_iff_ne_top.2 <| hextr.range_ne_top_of_hasStrictFDerivAt hf' hφ') with
    ⟨Λ', h0, hΛ'⟩
  set e : ((F ->ₗ[Real] Real) × Real) ≃ₗ[Real] F × Real ->ₗ[Real] Real :=
    ((LinearEquiv.refl Real (F ->ₗ[Real] Real)).prodCongr (LinearMap.ringLmapEquivSelf Real Real Real).symm).trans
      (LinearMap.coprodEquiv Real)
  rcases e.surjective Λ' with ⟨⟨Λ, Λ₀⟩, rfl⟩
  refine ⟨Λ, Λ₀, e.map_ne_zero_iff.1 h0, fun x => ?_⟩
  convert! LinearMap.congr_fun (LinearMap.range_le_ker_iff.1 hΛ') x using 1
    -- squeezed `simp [mul_comm]` to speed up elaboration

  -- squeezed `simp [mul_comm]` to speed up elaboration
  simp only [e, smul_eq_mul, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, LinearMap.ringLmapEquivSelf_symm_apply, LinearMap.coprodEquiv_apply,
    ContinuousLinearMap.coe_prod, LinearMap.coprod_comp_prod, LinearMap.add_apply,
    LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply, LinearMap.coe_smulRight,
    Module.End.one_apply, mul_comm]

/--
theorem `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d` / 定理 `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d`

English:
theorem IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d
  statement: {f : E -> Real} {f' : StrongDual Real E}
  proof: by
  obtain ⟨Λ, Λ₀, hΛ, hfΛ⟩ := hextr.exists_linear_map_of_hasStrictFDerivAt hf' hφ'
  refine ⟨Λ 1, Λ₀, ?_, ?_⟩
  · contrapose hΛ
    simp only [Prod.mk_eq_zero] at hΛ ⊢
    refine ⟨LinearMap.ext fun x => ?_, hΛ.2⟩
    simpa [hΛ.1] using Λ.map_smul x 1
  · ext x
    have H₁ : Λ (f' x) = f' x * Λ 1 := by
      simpa only [mul_one, smul_eq_mul] using Λ.map_smul (f' x) 1
    have H₂ : f' x * Λ 1 + Λ₀ * φ' x = 0 := by simpa only [smul_eq_mul, H₁] using hfΛ x
    simpa [mul_comm] using H₂

中文:
定理 IsLocalExtrOn.存在_multipliers_of_hasStrictFDerivAt_1d
  结论: {f : E -> 实数} {f' : StrongDual 实数 E}
  证明: by
  obtain ⟨Λ, Λ₀, hΛ, hfΛ⟩ := hextr.exists_linear_map_of_hasStrictFDerivAt hf' hφ'
  refine ⟨Λ 1, Λ₀, ?_, ?_⟩
  · contrapose hΛ
    simp only [Prod.mk_eq_zero] at hΛ ⊢
    refine ⟨LinearMap.ext fun x => ?_, hΛ.2⟩
    simpa [hΛ.1] using Λ.map_smul x 1
  · ext x
    have H₁ : Λ (f' x) = f' x * Λ 1 := by
      simpa only [mul_one, smul_eq_mul] using Λ.map_smul (f' x) 1
    have H₂ : f' x * Λ 1 + Λ₀ * φ' x = 0 := by simpa only [smul_eq_mul, H₁] using hfΛ x
    simpa [mul_comm] using H₂

Depends on / 依赖: LinearMap, LinearMap.ext, Nontrivial, NormOneClass, Prod.mk_eq_zero, contrapose, exists_linear_map_of_hasStrictFDerivAt, hextr.exists_linear_map_of_hasStrictFDerivAt, map_smul, mk_eq_zero, mul_comm, mul_one, smul_eq_mul
-/
theorem IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d {f : E -> Real} {f' : StrongDual Real E}
    (hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀) (hf' : HasStrictFDerivAt f f' x₀)
    (hφ' : HasStrictFDerivAt φ φ' x₀) : exists a b : Real, (a, b) != 0 ∧ a • f' + b • φ' = 0 := by
  obtain ⟨Λ, Λ₀, hΛ, hfΛ⟩ := hextr.exists_linear_map_of_hasStrictFDerivAt hf' hφ'
  refine ⟨Λ 1, Λ₀, ?_, ?_⟩
  · contrapose hΛ
    simp only [Prod.mk_eq_zero] at hΛ ⊢
    refine ⟨LinearMap.ext fun x => ?_, hΛ.2⟩
    simpa [hΛ.1] using Λ.map_smul x 1
  · ext x
    have H₁ : Λ (f' x) = f' x * Λ 1 := by
      simpa only [mul_one, smul_eq_mul] using Λ.map_smul (f' x) 1
    have H₂ : f' x * Λ 1 + Λ₀ * φ' x = 0 := by simpa only [smul_eq_mul, H₁] using hfΛ x
    simpa [mul_comm] using H₂

/--
theorem `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt` / 定理 `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`

English:
theorem IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt
  statement: {ι : Type*} [Fintype ι]
  proof: by
  let := Classical.decEq ι
  replace hextr : IsLocalExtrOn φ {x | (fun i => f i x) = fun i => f i x₀} x₀ := by
    simpa only [funext_iff] using hextr
  rcases hextr.exists_linear_map_of_hasStrictFDerivAt (hasStrictFDerivAt_pi.2 fun i => hf' i)
      hφ' with
    ⟨Λ, Λ₀, h0, hsum⟩
  rcases (LinearEquiv.piRing Real Real ι Real).symm.surjective Λ with ⟨Λ, rfl⟩
  refine ⟨Λ, Λ₀, ?_, ?_⟩
  · simpa only [Ne, Prod.ext_iff, LinearEquiv.map_eq_zero_iff, Prod.fst_zero] using! h0
  · ext x; simpa [mul_comm] using hsum x

中文:
定理 IsLocalExtrOn.存在_multipliers_of_hasStrictFDerivAt
  结论: {ι : 类型} [有限类型 ι]
  证明: by
  let := Classical.decEq ι
  replace hextr : IsLocalExtrOn φ {x | (fun i => f i x) = fun i => f i x₀} x₀ := by
    simpa only [funext_iff] using hextr
  rcases hextr.exists_linear_map_of_hasStrictFDerivAt (hasStrictFDerivAt_pi.2 fun i => hf' i)
      hφ' with
    ⟨Λ, Λ₀, h0, hsum⟩
  rcases (LinearEquiv.piRing Real Real ι Real).symm.surjective Λ with ⟨Λ, rfl⟩
  refine ⟨Λ, Λ₀, ?_, ?_⟩
  · simpa only [Ne, Prod.ext_iff, LinearEquiv.map_eq_zero_iff, Prod.fst_zero] using! h0
  · ext x; simpa [mul_comm] using hsum x

Depends on / 依赖: Classical, Classical.decEq, IsLocalExtrOn, LinearEquiv, LinearEquiv.map_eq_zero_iff, LinearEquiv.piRing, Prod.ext_iff, Prod.fst_zero, exists_linear_map_of_hasStrictFDerivAt, ext_iff, fst_zero, funext_iff, hasStrictFDerivAt_pi, hextr.exists_linear_map_of_hasStrictFDerivAt, map_eq_zero_iff, mul_comm, piRing, replace, surjective, symm.surjective
-/
theorem IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt {ι : Type*} [Fintype ι]
    {f : ι -> E -> Real} {f' : ι -> StrongDual Real E} (hextr : IsLocalExtrOn φ {x | forall i, f i x = f i x₀} x₀)
    (hf' : forall i, HasStrictFDerivAt (f i) (f' i) x₀) (hφ' : HasStrictFDerivAt φ φ' x₀) :
    exists (Λ : ι -> Real) (Λ₀ : Real), (Λ, Λ₀) != 0 ∧ (∑ i, Λ i • f' i) + Λ₀ • φ' = 0 := by
  let := Classical.decEq ι
  replace hextr : IsLocalExtrOn φ {x | (fun i => f i x) = fun i => f i x₀} x₀ := by
    simpa only [funext_iff] using hextr
  rcases hextr.exists_linear_map_of_hasStrictFDerivAt (hasStrictFDerivAt_pi.2 fun i => hf' i)
      hφ' with
    ⟨Λ, Λ₀, h0, hsum⟩
  rcases (LinearEquiv.piRing Real Real ι Real).symm.surjective Λ with ⟨Λ, rfl⟩
  refine ⟨Λ, Λ₀, ?_, ?_⟩
  · simpa only [Ne, Prod.ext_iff, LinearEquiv.map_eq_zero_iff, Prod.fst_zero] using! h0
  · ext x; simpa [mul_comm] using hsum x

/--
theorem `IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt` / 定理 `IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt`

English:
theorem IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt
  statement: {ι : Type*} [Finite ι] {f : ι -> E -> Real}
  proof: by
  cases nonempty_fintype ι
  rw [Fintype.linearIndependent_iff]; push Not
  rcases hextr.exists_multipliers_of_hasStrictFDerivAt hf' hφ' with ⟨Λ, Λ₀, hΛ, hΛf⟩
  refine ⟨Option.elim' Λ₀ Λ, ?_, ?_⟩
  · simpa [add_comm] using hΛf
  · simpa only [funext_iff, not_and_or, or_comm, Option.exists, Prod.mk_eq_zero, Ne,
      not_forall] using! hΛ

中文:
定理 IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt
  结论: {ι : 类型} [有限 ι] {f : ι -> E -> 实数}
  证明: by
  cases nonempty_fintype ι
  rw [Fintype.linearIndependent_iff]; push Not
  rcases hextr.exists_multipliers_of_hasStrictFDerivAt hf' hφ' with ⟨Λ, Λ₀, hΛ, hΛf⟩
  refine ⟨Option.elim' Λ₀ Λ, ?_, ?_⟩
  · simpa [add_comm] using hΛf
  · simpa only [funext_iff, not_and_or, or_comm, Option.exists, Prod.mk_eq_zero, Ne,
      not_forall] using! hΛ

Depends on / 依赖: Fintype, Fintype.linearIndependent_iff, Option.elim, Option.exists, Prod.mk_eq_zero, add_comm, exists_multipliers_of_hasStrictFDerivAt, funext_iff, hextr.exists_multipliers_of_hasStrictFDerivAt, linearIndependent_iff, mk_eq_zero, nonempty_fintype, not_and_or, not_forall, or_comm
-/
theorem IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt {ι : Type*} [Finite ι] {f : ι -> E -> Real}
    {f' : ι -> StrongDual Real E} (hextr : IsLocalExtrOn φ {x | forall i, f i x = f i x₀} x₀)
    (hf' : forall i, HasStrictFDerivAt (f i) (f' i) x₀) (hφ' : HasStrictFDerivAt φ φ' x₀) :
    ¬LinearIndependent Real (Option.elim' φ' f' : Option ι -> StrongDual Real E) := by
  cases nonempty_fintype ι
  rw [Fintype.linearIndependent_iff]; push Not
  rcases hextr.exists_multipliers_of_hasStrictFDerivAt hf' hφ' with ⟨Λ, Λ₀, hΛ, hΛf⟩
  refine ⟨Option.elim' Λ₀ Λ, ?_, ?_⟩
  · simpa [add_comm] using hΛf
  · simpa only [funext_iff, not_and_or, or_comm, Option.exists, Prod.mk_eq_zero, Ne,
      not_forall] using! hΛ
