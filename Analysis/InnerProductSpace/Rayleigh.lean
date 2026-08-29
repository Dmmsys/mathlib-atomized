/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Calculus.LagrangeMultipliers
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# The Rayleigh quotient

The Rayleigh quotient of a self-adjoint operator `T` on an inner product space `E` is the function
`fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2`.

The main results of this file are `IsSelfAdjoint.hasEigenvector_of_isMaxOn` and
`IsSelfAdjoint.hasEigenvector_of_isMinOn`, which state that if `E` is complete, and if the
Rayleigh quotient attains its global maximum/minimum over some sphere at the point `x₀`, then `x₀`
is an eigenvector of `T`, and the `iSup`/`iInf` of `fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2` is the corresponding
eigenvalue.

The corollaries `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` and
`LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` state that if `E` is
finite-dimensional and nontrivial, then `T` has some (nonzero) eigenvectors with eigenvalue the
`iSup`/`iInf` of `fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2`.

## TODO

A slightly more elaborate corollary is that if `E` is complete and `T` is a compact operator, then
`T` has some (nonzero) eigenvector with eigenvalue either `⨆ x, ⟪T x, x⟫ / ‖x‖ ^ 2` or
`⨅ x, ⟪T x, x⟫ / ‖x‖ ^ 2` (not necessarily both).

-/

public section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open scoped NNReal

open Module.End Metric RCLike InnerProductSpace

namespace ContinuousLinearMap

variable (T : E ->L[𝕜] E)

/--
Definition of `rayleighQuotient` / `rayleighQuotient` 的定义

English:
abbreviation rayleighQuotient
  signature: (x : E)
  body: T.reApplyInnerSelf x / ‖(x : E)‖ ^ 2

中文:
缩写 rayleighQuotient
  签名: (x : E)
  定义体: T.reApplyInnerSelf x / ‖(x : E)‖ ^ 2

Depends on / 依赖: T.reApplyInnerSelf, reApplyInnerSelf
-/
noncomputable abbrev rayleighQuotient (x : E) := T.reApplyInnerSelf x / ‖(x : E)‖ ^ 2

/--
theorem `rayleigh_smul` / 定理 `rayleigh_smul`

English:
theorem rayleigh_smul
  given: (x : E) {c : 𝕜} (hc : c != 0)
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  simp [field, norm_smul, T.reApplyInnerSelf_smul]

中文:
定理 rayleigh_smul
  条件: (x : E) {c : 𝕜} (hc : c != 0)
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  simp [field, norm_smul, T.reApplyInnerSelf_smul]

Depends on / 依赖: T.reApplyInnerSelf_smul, norm_smul, reApplyInnerSelf_smul
-/
theorem rayleigh_smul (x : E) {c : 𝕜} (hc : c != 0) :
    rayleighQuotient T (c • x) = rayleighQuotient T x := by
  by_cases hx : x = 0
  · simp [hx]
  simp [field, norm_smul, T.reApplyInnerSelf_smul]

/--
theorem `rayleighQuotient_add` / 定理 `rayleighQuotient_add`

English:
theorem rayleighQuotient_add
  given: (S : E ->L[𝕜] E) {x : E}
  proof: by
  simp [rayleighQuotient, reApplyInnerSelf_apply, inner_add_left, add_div]

@[simp]

中文:
定理 rayleighQuotient_add
  条件: (S : E ->L[𝕜] E) {x : E}
  证明: by
  simp [rayleighQuotient, reApplyInnerSelf_apply, inner_add_left, add_div]

@[simp]

Depends on / 依赖: add_div, inner_add_left, rayleighQuotient, reApplyInnerSelf_apply
-/
theorem rayleighQuotient_add (S : E ->L[𝕜] E) {x : E} :
    (T + S).rayleighQuotient x = T.rayleighQuotient x + S.rayleighQuotient x := by
  simp [rayleighQuotient, reApplyInnerSelf_apply, inner_add_left, add_div]

@[simp]
/--
theorem `rayleighQuotient_zero_apply` / 定理 `rayleighQuotient_zero_apply`

English:
theorem rayleighQuotient_zero_apply
  given: (x : E)
  statement: rayleighQuotient (0 : E ->L[𝕜] E) x = 0
  proof: by
  simp [reApplyInnerSelf_apply]

@[simp]

中文:
定理 rayleighQuotient_zero_apply
  条件: (x : E)
  结论: rayleighQuotient (0 : E ->L[𝕜] E) x = 0
  证明: by
  simp [reApplyInnerSelf_apply]

@[simp]

Depends on / 依赖: reApplyInnerSelf_apply
-/
theorem rayleighQuotient_zero_apply (x : E) : rayleighQuotient (0 : E ->L[𝕜] E) x = 0 := by
  simp [reApplyInnerSelf_apply]

@[simp]
/--
theorem `rayleighQuotient_apply_zero` / 定理 `rayleighQuotient_apply_zero`

English:
theorem rayleighQuotient_apply_zero
  statement: rayleighQuotient T 0 = 0
  proof: by
  simp [reApplyInnerSelf_apply]

@[simp]

中文:
定理 rayleighQuotient_apply_zero
  结论: rayleighQuotient T 0 = 0
  证明: by
  simp [reApplyInnerSelf_apply]

@[simp]

Depends on / 依赖: reApplyInnerSelf_apply
-/
theorem rayleighQuotient_apply_zero : rayleighQuotient T 0 = 0 := by
  simp [reApplyInnerSelf_apply]

@[simp]
/--
theorem `rayleighQuotient_neg_apply` / 定理 `rayleighQuotient_neg_apply`

English:
theorem rayleighQuotient_neg_apply
  given: (x : E)
  statement: rayleighQuotient (-T) x = -rayleighQuotient T x
  proof: by
  simp [rayleighQuotient, reApplyInnerSelf_apply, neg_div]

@[simp]

中文:
定理 rayleighQuotient_neg_apply
  条件: (x : E)
  结论: rayleighQuotient (-T) x = -rayleighQuotient T x
  证明: by
  simp [rayleighQuotient, reApplyInnerSelf_apply, neg_div]

@[simp]

Depends on / 依赖: neg_div, rayleighQuotient, reApplyInnerSelf_apply
-/
theorem rayleighQuotient_neg_apply (x : E) : rayleighQuotient (-T) x = -rayleighQuotient T x := by
  simp [rayleighQuotient, reApplyInnerSelf_apply, neg_div]

@[simp]
/--
theorem `rayleighQuotient_apply_neg` / 定理 `rayleighQuotient_apply_neg`

English:
theorem rayleighQuotient_apply_neg
  given: (x : E)
  statement: rayleighQuotient T (-x) = rayleighQuotient T x
  proof: by
  simp [rayleighQuotient, reApplyInnerSelf_apply]

中文:
定理 rayleighQuotient_apply_neg
  条件: (x : E)
  结论: rayleighQuotient T (-x) = rayleighQuotient T x
  证明: by
  simp [rayleighQuotient, reApplyInnerSelf_apply]

Depends on / 依赖: rayleighQuotient, reApplyInnerSelf_apply
-/
theorem rayleighQuotient_apply_neg (x : E) : rayleighQuotient T (-x) = rayleighQuotient T x := by
  simp [rayleighQuotient, reApplyInnerSelf_apply]

/--
theorem `image_rayleigh_eq_image_rayleigh_sphere` / 定理 `image_rayleigh_eq_image_rayleigh_sphere`

English:
theorem image_rayleigh_eq_image_rayleigh_sphere
  given: {r : Real} (hr : 0 < r)
  proof: by
  ext a
  constructor
  · rintro ⟨x, hx : x != 0, hxT⟩
    let c : 𝕜 := ‖x‖⁻¹ * r
    have : c != 0 := by simp [c, hx, hr.ne']
    refine ⟨c • x, ?_, ?_⟩
    · simp [field, c, norm_smul, abs_of_pos hr]
    · rw [T.rayleigh_smul x this]
      exact hxT
  · rintro ⟨x, hx, hxT⟩
    exact ⟨x, ne_zero

中文:
定理 image_rayleigh_eq_image_rayleigh_sphere
  条件: {r : 实数} (hr : 0 < r)
  证明: by
  ext a
  constructor
  · rintro ⟨x, hx : x != 0, hxT⟩
    let c : 𝕜 := ‖x‖⁻¹ * r
    have : c != 0 := by simp [c, hx, hr.ne']
    refine ⟨c • x, ?_, ?_⟩
    · simp [field, c, norm_smul, abs_of_pos hr]
    · rw [T.rayleigh_smul x this]
      exact hxT
  · rintro ⟨x, hx, hxT⟩
    exact ⟨x, ne_zero

Depends on / 依赖: T.rayleigh_smul, abs_of_pos, hr.ne, ne_zero_of_mem_sphere, norm_smul, rayleigh_smul
-/
theorem image_rayleigh_eq_image_rayleigh_sphere {r : Real} (hr : 0 < r) :
    rayleighQuotient T '' {0}ᶜ = rayleighQuotient T '' sphere 0 r := by
  ext a
  constructor
  · rintro ⟨x, hx : x != 0, hxT⟩
    let c : 𝕜 := ‖x‖⁻¹ * r
    have : c != 0 := by simp [c, hx, hr.ne']
    refine ⟨c • x, ?_, ?_⟩
    · simp [field, c, norm_smul, abs_of_pos hr]
    · rw [T.rayleigh_smul x this]
      exact hxT
  · rintro ⟨x, hx, hxT⟩
    exact ⟨x, ne_zero_of_mem_sphere hr.ne' ⟨x, hx⟩, hxT⟩

/--
theorem `iSup_rayleigh_eq_iSup_rayleigh_sphere` / 定理 `iSup_rayleigh_eq_iSup_rayleigh_sphere`

English:
theorem iSup_rayleigh_eq_iSup_rayleigh_sphere
  given: {r : Real} (hr : 0 < r)
  proof: show ⨆ x : ({0}ᶜ : Set E), rayleighQuotient T x = _ by
    simp only [← @sSup_image' _ _ _ _ (rayleighQuotient T),
      T.image_rayleigh_eq_image_rayleigh_sphere hr]

中文:
定理 iSup_rayleigh_eq_iSup_rayleigh_sphere
  条件: {r : 实数} (hr : 0 < r)
  证明: show ⨆ x : ({0}ᶜ : Set E), rayleighQuotient T x = _ by
    simp only [← @sSup_image' _ _ _ _ (rayleighQuotient T),
      T.image_rayleigh_eq_image_rayleigh_sphere hr]

Depends on / 依赖: T.image_rayleigh_eq_image_rayleigh_sphere, image_rayleigh_eq_image_rayleigh_sphere, rayleighQuotient, sSup_image
-/
theorem iSup_rayleigh_eq_iSup_rayleigh_sphere {r : Real} (hr : 0 < r) :
    ⨆ x : { x : E // x != 0 }, rayleighQuotient T x =
      ⨆ x : sphere (0 : E) r, rayleighQuotient T x :=
  show ⨆ x : ({0}ᶜ : Set E), rayleighQuotient T x = _ by
    simp only [← @sSup_image' _ _ _ _ (rayleighQuotient T),
      T.image_rayleigh_eq_image_rayleigh_sphere hr]

/--
theorem `iInf_rayleigh_eq_iInf_rayleigh_sphere` / 定理 `iInf_rayleigh_eq_iInf_rayleigh_sphere`

English:
theorem iInf_rayleigh_eq_iInf_rayleigh_sphere
  given: {r : Real} (hr : 0 < r)
  proof: show ⨅ x : ({0}ᶜ : Set E), rayleighQuotient T x = _ by
    simp only [← @sInf_image' _ _ _ _ (rayleighQuotient T),
      T.image_rayleigh_eq_image_rayleigh_sphere hr]

中文:
定理 iInf_rayleigh_eq_iInf_rayleigh_sphere
  条件: {r : 实数} (hr : 0 < r)
  证明: show ⨅ x : ({0}ᶜ : Set E), rayleighQuotient T x = _ by
    simp only [← @sInf_image' _ _ _ _ (rayleighQuotient T),
      T.image_rayleigh_eq_image_rayleigh_sphere hr]

Depends on / 依赖: T.image_rayleigh_eq_image_rayleigh_sphere, image_rayleigh_eq_image_rayleigh_sphere, rayleighQuotient, sInf_image
-/
theorem iInf_rayleigh_eq_iInf_rayleigh_sphere {r : Real} (hr : 0 < r) :
    ⨅ x : { x : E // x != 0 }, rayleighQuotient T x =
      ⨅ x : sphere (0 : E) r, rayleighQuotient T x :=
  show ⨅ x : ({0}ᶜ : Set E), rayleighQuotient T x = _ by
    simp only [← @sInf_image' _ _ _ _ (rayleighQuotient T),
      T.image_rayleigh_eq_image_rayleigh_sphere hr]

/--
theorem `rayleighQuotient_le_norm` / 定理 `rayleighQuotient_le_norm`

English:
theorem rayleighQuotient_le_norm
  given: (x : E)
  statement: |T.rayleighQuotient x| <= ‖T‖
  proof: by
  grw [rayleighQuotient, reApplyInnerSelf_apply, abs_div, abs_sq, abs_re_le_norm,
    norm_inner_le_norm, le_opNorm, mul_assoc, ← sq, mul_div_assoc]
  exact mul_le_of_le_one_right T.opNorm_nonneg (div_self_le_one (‖x‖ ^ 2))

中文:
定理 rayleighQuotient_le_norm
  条件: (x : E)
  结论: |T.rayleighQuotient x| <= ‖T‖
  证明: by
  grw [rayleighQuotient, reApplyInnerSelf_apply, abs_div, abs_sq, abs_re_le_norm,
    norm_inner_le_norm, le_opNorm, mul_assoc, ← sq, mul_div_assoc]
  exact mul_le_of_le_one_right T.opNorm_nonneg (div_self_le_one (‖x‖ ^ 2))

Depends on / 依赖: T.opNorm_nonneg, abs_div, abs_re_le_norm, abs_sq, div_self_le_one, le_opNorm, mul_assoc, mul_div_assoc, mul_le_of_le_one_right, norm_inner_le_norm, opNorm_nonneg, rayleighQuotient, reApplyInnerSelf_apply
-/
theorem rayleighQuotient_le_norm (x : E) : |T.rayleighQuotient x| <= ‖T‖ := by
  grw [rayleighQuotient, reApplyInnerSelf_apply, abs_div, abs_sq, abs_re_le_norm,
    norm_inner_le_norm, le_opNorm, mul_assoc, ← sq, mul_div_assoc]
  exact mul_le_of_le_one_right T.opNorm_nonneg (div_self_le_one (‖x‖ ^ 2))

/--
theorem `bddAbove_rayleighQuotient` / 定理 `bddAbove_rayleighQuotient`

English:
theorem bddAbove_rayleighQuotient
  statement: BddAbove (Set.range fun x => |T.rayleighQuotient x|)
  proof: ⟨‖T‖, fun _ ⟨y, h⟩ => h ▸ T.rayleighQuotient_le_norm y⟩

中文:
定理 bddAbove_rayleighQuotient
  结论: BddAbove (集合.range fun x => |T.rayleighQuotient x|)
  证明: ⟨‖T‖, fun _ ⟨y, h⟩ => h ▸ T.rayleighQuotient_le_norm y⟩

Depends on / 依赖: T.rayleighQuotient_le_norm, rayleighQuotient_le_norm
-/
theorem bddAbove_rayleighQuotient : BddAbove (Set.range fun x => |T.rayleighQuotient x|) :=
  ⟨‖T‖, fun _ ⟨y, h⟩ => h ▸ T.rayleighQuotient_le_norm y⟩

/--
theorem `norm_eq_iSup_rayleighQuotient` / 定理 `norm_eq_iSup_rayleighQuotient`

English:
theorem norm_eq_iSup_rayleighQuotient
  given: (hT : T.IsSymmetric)
  proof: by
  set M := ⨆ x, |T.rayleighQuotient x|
  have nonneg : 0 <= M := le_ciSup_of_le T.bddAbove_rayleighQuotient 0 (abs_nonneg _)
  have hM x : |re ⟪T x, x⟫| <= M * ‖x‖ ^ 2 := by
    have hM : |T.rayleighQuotient x| <= M := le_ciSup T.bddAbove_rayleighQuotient x
    by_cases hx : 0 < ‖x‖ ^ 2
    · rwa

中文:
定理 norm_eq_iSup_rayleighQuotient
  条件: (hT : T.IsSymmetric)
  证明: by
  set M := ⨆ x, |T.rayleighQuotient x|
  have nonneg : 0 <= M := le_ciSup_of_le T.bddAbove_rayleighQuotient 0 (abs_nonneg _)
  have hM x : |re ⟪T x, x⟫| <= M * ‖x‖ ^ 2 := by
    have hM : |T.rayleighQuotient x| <= M := le_ciSup T.bddAbove_rayleighQuotient x
    by_cases hx : 0 < ‖x‖ ^ 2
    · rwa

Depends on / 依赖: T.bddAbove_rayleighQuotient, T.rayleighQuotient, T.rayleighQuotient_le_norm, abs_div, abs_nonneg, abs_sq, bddAbove_rayleighQuotient, ciSup_le, le_antisymm, le_ciSup, le_ciSup_of_le, nonneg, opNorm_le_of_re_inner_le, rayleighQuotient, rayleighQuotient_le_norm, reApplyInnerSelf, transitivit
-/
theorem norm_eq_iSup_rayleighQuotient (hT : T.IsSymmetric) :
    ‖T‖ = ⨆ x, |T.rayleighQuotient x| := by
  set M := ⨆ x, |T.rayleighQuotient x|
  have nonneg : 0 <= M := le_ciSup_of_le T.bddAbove_rayleighQuotient 0 (abs_nonneg _)
  have hM x : |re ⟪T x, x⟫| <= M * ‖x‖ ^ 2 := by
    have hM : |T.rayleighQuotient x| <= M := le_ciSup T.bddAbove_rayleighQuotient x
    by_cases hx : 0 < ‖x‖ ^ 2
    · rwa [rayleighQuotient, abs_div, abs_sq, reApplyInnerSelf, div_le_iff₀ hx] at hM
    · simp_all
  refine le_antisymm ?_ (ciSup_le T.rayleighQuotient_le_norm)
  refine opNorm_le_of_re_inner_le nonneg fun x y hx hy => ?_
  transitivity M * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 4
  · have key := congrArg re (add_conj ⟪T x, y⟫)
    rw [map_add]; rw [conj_inner_symm]; rw [← coe_coe]; rw [← hT]; rw [coe_coe]; rw [re_mul_ofReal]; rw [ofNat_re] at key
    grind [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  · rw [parallelogram_law_with_norm 𝕜 x y, hx, hy]
    grind

/--
theorem `rayleighQuotient_le_of_mem_resolventSet` / 定理 `rayleighQuotient_le_of_mem_resolventSet`

English:
theorem rayleighQuotient_le_of_mem_resolventSet
  proof: by
  by_cases hT0 : T = 0
  · exact ⟨t ^ 2 / (2 * t), by positivity, by simp [hT0]⟩
  obtain ⟨c, hc0, hc⟩ := antilipschitzWith_iff_exists_mul_le_norm.mp
    (antilipschitz_of_isEmbedding _ (isHomeomorph_of_isUnit hT').isEmbedding)
  refine ⟨min (c ^ 2 / (2 * t)) ((t ^ 2 + ‖T‖ ^ 2) / (2 * t)), by pos

中文:
定理 rayleighQuotient_le_of_mem_resolventSet
  证明: by
  by_cases hT0 : T = 0
  · exact ⟨t ^ 2 / (2 * t), by positivity, by simp [hT0]⟩
  obtain ⟨c, hc0, hc⟩ := antilipschitzWith_iff_exists_mul_le_norm.mp
    (antilipschitz_of_isEmbedding _ (isHomeomorph_of_isUnit hT').isEmbedding)
  refine ⟨min (c ^ 2 / (2 * t)) ((t ^ 2 + ‖T‖ ^ 2) / (2 * t)), by pos
-/
private theorem rayleighQuotient_le_of_mem_resolventSet
    (t : Real) (ht : 0 < t) (hT' : (algebraMap Real 𝕜) t in resolventSet 𝕜 T) :
    exists c > 0, forall x, T.rayleighQuotient x <= (t ^ 2 + ‖T‖ ^ 2) / (2 * t) - c := by
  by_cases hT0 : T = 0
  · exact ⟨t ^ 2 / (2 * t), by positivity, by simp [hT0]⟩
  obtain ⟨c, hc0, hc⟩ := antilipschitzWith_iff_exists_mul_le_norm.mp
    (antilipschitz_of_isEmbedding _ (isHomeomorph_of_isUnit hT').isEmbedding)
  refine ⟨min (c ^ 2 / (2 * t)) ((t ^ 2 + ‖T‖ ^ 2) / (2 * t)), by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  suffices T.rayleighQuotient x <= (t ^ 2 + ‖T‖ ^ 2) / (2 * t) - c ^ 2 / (2 * t) by
    grw [this, min_le_left]
  rw [rayleighQuotient]; rw [reApplyInnerSelf_apply]
  specialize hc x
  rw [← sq_le_sq₀ (by positivity) (by positivity)]; rw [sub_apply]; rw [algebraMap_apply]; rw [norm_sub_sq (𝕜 := 𝕜)]; rw [inner_re_symm] at hc
  grw [le_opNorm] at hc
  simp [inner_smul_right, norm_smul, abs_of_pos ht] at hc
  field_simp
  grind

/--
theorem `rayleighQuotient_le_of_norm_mem_resolventSet` / 定理 `rayleighQuotient_le_of_norm_mem_resolventSet`

English:
theorem rayleighQuotient_le_of_norm_mem_resolventSet
  statement: [Nontrivial E]
  proof: by
  by_cases hT0 : T = 0
  · simp [hT0, spectrum.mem_resolventSet_iff] at hT'
  obtain ⟨ε, hε0, hε⟩ := T.rayleighQuotient_le_of_mem_resolventSet ‖T‖ (by positivity) hT'
  refine ⟨ε, hε0, fun x => ?_⟩
  grw [hε]
  field_simp
  grind

中文:
定理 rayleighQuotient_le_of_norm_mem_resolventSet
  结论: [非平凡 E]
  证明: by
  by_cases hT0 : T = 0
  · simp [hT0, spectrum.mem_resolventSet_iff] at hT'
  obtain ⟨ε, hε0, hε⟩ := T.rayleighQuotient_le_of_mem_resolventSet ‖T‖ (by positivity) hT'
  refine ⟨ε, hε0, fun x => ?_⟩
  grw [hε]
  field_simp
  grind

Depends on / 依赖: T.rayleighQuotient_le_of_mem_resolventSet, mem_resolventSet_iff, rayleighQuotient_le_of_mem_resolventSet, spectrum, spectrum.mem_resolventSet_iff
-/
theorem rayleighQuotient_le_of_norm_mem_resolventSet [Nontrivial E]
    (hT' : algebraMap Real 𝕜 ‖T‖ in resolventSet 𝕜 T) :
    exists ε > 0, forall x, T.rayleighQuotient x <= ‖T‖ - ε := by
  by_cases hT0 : T = 0
  · simp [hT0, spectrum.mem_resolventSet_iff] at hT'
  obtain ⟨ε, hε0, hε⟩ := T.rayleighQuotient_le_of_mem_resolventSet ‖T‖ (by positivity) hT'
  refine ⟨ε, hε0, fun x => ?_⟩
  grw [hε]
  field_simp
  grind

/--
theorem `abs_rayleighQuotient_le_of_norm_mem_resolventSet` / 定理 `abs_rayleighQuotient_le_of_norm_mem_resolventSet`

English:
theorem abs_rayleighQuotient_le_of_norm_mem_resolventSet
  statement: [Nontrivial E]
  proof: by
  obtain ⟨ε, hε0, hε⟩ := T.rayleighQuotient_le_of_norm_mem_resolventSet hT'
obtain ⟨ε', hε'0, hε'⟩ := (-T).rayleighQuotient_le_of_norm_mem_resolventSet by
    simpa [resolventSet_neg]
  exact ⟨min ε ε', by grind, fun x => by grind [rayleighQuotient_neg_apply, norm_neg]⟩

中文:
定理 abs_rayleighQuotient_le_of_norm_mem_resolventSet
  结论: [非平凡 E]
  证明: by
  obtain ⟨ε, hε0, hε⟩ := T.rayleighQuotient_le_of_norm_mem_resolventSet hT'
obtain ⟨ε', hε'0, hε'⟩ := (-T).rayleighQuotient_le_of_norm_mem_resolventSet by
    simpa [resolventSet_neg]
  exact ⟨min ε ε', by grind, fun x => by grind [rayleighQuotient_neg_apply, norm_neg]⟩

Depends on / 依赖: T.rayleighQuotient_le_of_norm_mem_resolventSet, norm_neg, rayleighQuotient_le_of_norm_mem_resolventSet, rayleighQuotient_neg_apply, resolventSet_neg
-/
theorem abs_rayleighQuotient_le_of_norm_mem_resolventSet [Nontrivial E]
    (hT' : algebraMap Real 𝕜 ‖T‖ in resolventSet 𝕜 T) (hT'' : -algebraMap Real 𝕜 ‖T‖ in resolventSet 𝕜 T) :
    exists ε > 0, forall x, |T.rayleighQuotient x| <= ‖T‖ - ε := by
  obtain ⟨ε, hε0, hε⟩ := T.rayleighQuotient_le_of_norm_mem_resolventSet hT'
obtain ⟨ε', hε'0, hε'⟩ := (-T).rayleighQuotient_le_of_norm_mem_resolventSet by
    simpa [resolventSet_neg]
  exact ⟨min ε ε', by grind, fun x => by grind [rayleighQuotient_neg_apply, norm_neg]⟩

-- TODO: Prove this from `IsSelfAdjoint.toReal_spectralRadius_eq_norm` using complexification.
/--
theorem `spectralRadius_eq_nnnorm` / 定理 `spectralRadius_eq_nnnorm`

English:
theorem spectralRadius_eq_nnnorm
  given: [CompleteSpace E] (hT : IsSelfAdjoint T)
  proof: by
  nontriviality E
  apply le_antisymm (spectrum.spectralRadius_le_nnnorm T)
  suffices h : algebraMap Real 𝕜 ‖T‖ in spectrum 𝕜 T ∨ algebraMap Real 𝕜 (-‖T‖) in spectrum 𝕜 T by
    rcases h with h | h <;> exact le_trans (by simp) (le_biSup _ h)
  simp_rw [spectrum, Set.mem_compl_iff, map_neg]
  by_

中文:
定理 spectralRadius_eq_nnnorm
  条件: [完备空间 E] (hT : IsSelfAdjoint T)
  证明: by
  nontriviality E
  apply le_antisymm (spectrum.spectralRadius_le_nnnorm T)
  suffices h : algebraMap Real 𝕜 ‖T‖ in spectrum 𝕜 T ∨ algebraMap Real 𝕜 (-‖T‖) in spectrum 𝕜 T by
    rcases h with h | h <;> exact le_trans (by simp) (le_biSup _ h)
  simp_rw [spectrum, Set.mem_compl_iff, map_neg]
  by_

Depends on / 依赖: Set.mem_compl_iff, T.abs_rayleighQuotient_le_of_norm_mem_resolventSet, abs_rayleighQuotient_le_of_norm_mem_resolventSet, algebraMap, ciSup_le, hT.isSymmetric, isSymmetric, le_antisymm, le_biSup, le_trans, map_neg, mem_compl_iff, nontriviality, norm_eq_iSup_rayleighQuotient, simp_rw, spectralRadius_le_nnnorm, spectrum, spectrum.spectralRadius_le_nnnorm
-/
theorem spectralRadius_eq_nnnorm [CompleteSpace E] (hT : IsSelfAdjoint T) :
    spectralRadius 𝕜 T = ‖T‖₊ := by
  nontriviality E
  apply le_antisymm (spectrum.spectralRadius_le_nnnorm T)
  suffices h : algebraMap Real 𝕜 ‖T‖ in spectrum 𝕜 T ∨ algebraMap Real 𝕜 (-‖T‖) in spectrum 𝕜 T by
    rcases h with h | h <;> exact le_trans (by simp) (le_biSup _ h)
  simp_rw [spectrum, Set.mem_compl_iff, map_neg]
  by_contra! h
  obtain ⟨c, hc0, hc⟩ := T.abs_rayleighQuotient_le_of_norm_mem_resolventSet h.1 h.2
  grind [ciSup_le hc, norm_eq_iSup_rayleighQuotient T hT.isSymmetric]

end ContinuousLinearMap

namespace IsSelfAdjoint

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]

/--
theorem `_root_.LinearMap.IsSymmetric.hasStrictFDerivAt_reApplyInnerSelf` / 定理 `_root_.LinearMap.IsSymmetric.hasStrictFDerivAt_reApplyInnerSelf`

English:
theorem _root_.LinearMap.IsSymmetric.hasStrictFDerivAt_reApplyInnerSelf
  statement: {T : F ->L[Real] F}
  proof: by
  convert! T.hasStrictFDerivAt.inner Real (hasStrictFDerivAt_id x₀) using 1
  ext y
  rw [smul_apply]; rw [ContinuousLinearMap.comp_apply]; rw [fderivInnerCLM_apply]; rw [ContinuousLinearMap.prod_apply]; rw [innerSL_apply_apply]; rw [id]; rw [ContinuousLinearMap.id_apply]; rw [hT.apply_clm x₀ y];

中文:
定理 _root_.线性映射.IsSymmetric.hasStrictFDerivAt_reApplyInnerSelf
  结论: {T : F ->L[实数] F}
  证明: by
  convert! T.hasStrictFDerivAt.inner Real (hasStrictFDerivAt_id x₀) using 1
  ext y
  rw [smul_apply]; rw [ContinuousLinearMap.comp_apply]; rw [fderivInnerCLM_apply]; rw [ContinuousLinearMap.prod_apply]; rw [innerSL_apply_apply]; rw [id]; rw [ContinuousLinearMap.id_apply]; rw [hT.apply_clm x₀ y];

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.prod_apply, T.hasStrictFDerivAt.inner, apply_clm, comp_apply, convert, fderivInnerCLM_apply, hT.apply_clm, hasStrictFDerivAt, hasStrictFDerivAt_id, id_apply, innerSL_apply_apply, prod_apply, real_inner_comm, smul_apply, two_smul
-/
theorem _root_.LinearMap.IsSymmetric.hasStrictFDerivAt_reApplyInnerSelf {T : F ->L[Real] F}
    (hT : (T : F ->ₗ[Real] F).IsSymmetric) (x₀ : F) :
    HasStrictFDerivAt T.reApplyInnerSelf (2 • (innerSL Real (T x₀))) x₀ := by
  convert! T.hasStrictFDerivAt.inner Real (hasStrictFDerivAt_id x₀) using 1
  ext y
  rw [smul_apply]; rw [ContinuousLinearMap.comp_apply]; rw [fderivInnerCLM_apply]; rw [ContinuousLinearMap.prod_apply]; rw [innerSL_apply_apply]; rw [id]; rw [ContinuousLinearMap.id_apply]; rw [hT.apply_clm x₀ y]; rw [real_inner_comm _ x₀]; rw [two_smul]

variable [CompleteSpace F] {T : F ->L[Real] F}

/--
theorem `linearly_dependent_of_isLocalExtrOn` / 定理 `linearly_dependent_of_isLocalExtrOn`

English:
theorem linearly_dependent_of_isLocalExtrOn
  statement: (hT : IsSelfAdjoint T) {x₀ : F}
  proof: by
  have H : IsLocalExtrOn T.reApplyInnerSelf {x : F | ‖x‖ ^ 2 = ‖x₀‖ ^ 2} x₀ := by
    convert! hextr
    ext x
    simp
  -- find Lagrange multipliers for the function `T.re_apply_inner_self` and the
  -- hypersurface-defining function `fun x ↦ ‖x‖ ^ 2`
  obtain ⟨a, b, h₁, h₂⟩ :=
    IsLocalExtrO

中文:
定理 linearly_dependent_of_isLocalExtrOn
  结论: (hT : IsSelfAdjoint T) {x₀ : F}
  证明: by
  have H : IsLocalExtrOn T.reApplyInnerSelf {x : F | ‖x‖ ^ 2 = ‖x₀‖ ^ 2} x₀ := by
    convert! hextr
    ext x
    simp
  -- find Lagrange multipliers for the function `T.re_apply_inner_self` and the
  -- hypersurface-defining function `fun x ↦ ‖x‖ ^ 2`
  obtain ⟨a, b, h₁, h₂⟩ :=
    IsLocalExtrO

Depends on / 依赖: IsLocalExtrOn, T.reApplyInnerSelf, convert, reApplyInnerSelf
-/
theorem linearly_dependent_of_isLocalExtrOn (hT : IsSelfAdjoint T) {x₀ : F}
    (hextr : IsLocalExtrOn T.reApplyInnerSelf (sphere (0 : F) ‖x₀‖) x₀) :
    exists a b : Real, (a, b) != 0 ∧ a • x₀ + b • T x₀ = 0 := by
  have H : IsLocalExtrOn T.reApplyInnerSelf {x : F | ‖x‖ ^ 2 = ‖x₀‖ ^ 2} x₀ := by
    convert! hextr
    ext x
    simp
  -- find Lagrange multipliers for the function `T.re_apply_inner_self` and the
  -- hypersurface-defining function `fun x ↦ ‖x‖ ^ 2`
  obtain ⟨a, b, h₁, h₂⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d H (hasStrictFDerivAt_norm_sq x₀)
      (hT.isSymmetric.hasStrictFDerivAt_reApplyInnerSelf x₀)
  refine ⟨a, b, h₁, ?_⟩
  apply (InnerProductSpace.toDualMap Real F).injective
  simp only [LinearIsometry.map_add, LinearIsometry.map_zero]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
  simp only [map_smulₛₗ _, RCLike.conj_to_real]
  change a • innerSL Real x₀ + b • innerSL Real (T x₀) = 0
  apply smul_right_injective (F ->L[Real] Real) (two_ne_zero : (2 : Real) != 0)
  simpa only [two_smul, smul_add, add_smul, add_zero] using h₂

open scoped InnerProductSpace in
/--
theorem `eq_smul_self_of_isLocalExtrOn_real` / 定理 `eq_smul_self_of_isLocalExtrOn_real`

English:
theorem eq_smul_self_of_isLocalExtrOn_real
  statement: (hT : IsSelfAdjoint T) {x₀ : F}
  proof: by
  obtain ⟨a, b, h₁, h₂⟩ := hT.linearly_dependent_of_isLocalExtrOn hextr
  by_cases hx₀ : x₀ = 0
  · simp [hx₀]
  by_cases hb : b = 0
  · have : a != 0 := by simpa [hb] using! h₁
    refine absurd ?_ hx₀
    apply smul_right_injective F this
    simpa [hb] using! h₂
  have hc : T x₀ = (-b⁻¹ * a) •

中文:
定理 eq_smul_self_of_isLocalExtrOn_real
  结论: (hT : IsSelfAdjoint T) {x₀ : F}
  证明: by
  obtain ⟨a, b, h₁, h₂⟩ := hT.linearly_dependent_of_isLocalExtrOn hextr
  by_cases hx₀ : x₀ = 0
  · simp [hx₀]
  by_cases hb : b = 0
  · have : a != 0 := by simpa [hb] using! h₁
    refine absurd ?_ hx₀
    apply smul_right_injective F this
    simpa [hb] using! h₂
  have hc : T x₀ = (-b⁻¹ * a) •

Depends on / 依赖: _Real, absurd, congr_arg, convert, hT.linearly_dependent_of_isLocalExtrOn, inner_smul_left, linear_combination, linearly_dependent_of_isLocalExtrOn, match_scalars, mul_comm, smul_right_injective
-/
theorem eq_smul_self_of_isLocalExtrOn_real (hT : IsSelfAdjoint T) {x₀ : F}
    (hextr : IsLocalExtrOn T.reApplyInnerSelf (sphere (0 : F) ‖x₀‖) x₀) :
    T x₀ = T.rayleighQuotient x₀ • x₀ := by
  obtain ⟨a, b, h₁, h₂⟩ := hT.linearly_dependent_of_isLocalExtrOn hextr
  by_cases hx₀ : x₀ = 0
  · simp [hx₀]
  by_cases hb : b = 0
  · have : a != 0 := by simpa [hb] using! h₁
    refine absurd ?_ hx₀
    apply smul_right_injective F this
    simpa [hb] using! h₂
  have hc : T x₀ = (-b⁻¹ * a) • x₀ := by
    linear_combination (norm := match_scalars <;> field) b⁻¹ • h₂
  set c : Real := -b⁻¹ * a
  convert hc
  simpa [field, inner_smul_left, mul_comm a] using! congr_arg (fun x => ⟪x, x₀⟫_Real) hc

end Real

section CompleteSpace

variable [CompleteSpace E] {T : E ->L[𝕜] E}

/--
theorem `eq_smul_self_of_isLocalExtrOn` / 定理 `eq_smul_self_of_isLocalExtrOn`

English:
theorem eq_smul_self_of_isLocalExtrOn
  statement: (hT : IsSelfAdjoint T) {x₀ : E}
  proof: by
  let := InnerProductSpace.rclikeToReal 𝕜 E
  let hSA := hT.isSymmetric.restrictScalars.toSelfAdjoint.prop
  exact hSA.eq_smul_self_of_isLocalExtrOn_real hextr

中文:
定理 eq_smul_self_of_isLocalExtrOn
  结论: (hT : IsSelfAdjoint T) {x₀ : E}
  证明: by
  let := InnerProductSpace.rclikeToReal 𝕜 E
  let hSA := hT.isSymmetric.restrictScalars.toSelfAdjoint.prop
  exact hSA.eq_smul_self_of_isLocalExtrOn_real hextr

Depends on / 依赖: InnerProductSpace, InnerProductSpace.rclikeToReal, eq_smul_self_of_isLocalExtrOn_real, hSA.eq_smul_self_of_isLocalExtrOn_real, hT.isSymmetric.restrictScalars.toSelfAdjoint.prop, isSymmetric, rclikeToReal, restrictScalars, toSelfAdjoint
-/
theorem eq_smul_self_of_isLocalExtrOn (hT : IsSelfAdjoint T) {x₀ : E}
    (hextr : IsLocalExtrOn T.reApplyInnerSelf (sphere (0 : E) ‖x₀‖) x₀) :
    T x₀ = (T.rayleighQuotient x₀ : 𝕜) • x₀ := by
  let := InnerProductSpace.rclikeToReal 𝕜 E
  let hSA := hT.isSymmetric.restrictScalars.toSelfAdjoint.prop
  exact hSA.eq_smul_self_of_isLocalExtrOn_real hextr

/--
theorem `hasEigenvector_of_isLocalExtrOn` / 定理 `hasEigenvector_of_isLocalExtrOn`

English:
theorem hasEigenvector_of_isLocalExtrOn
  statement: (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ != 0)
  proof: by
  refine ⟨?_, hx₀⟩
  rw [Module.End.mem_eigenspace_iff]
  exact hT.eq_smul_self_of_isLocalExtrOn hextr

中文:
定理 hasEigenvector_of_isLocalExtrOn
  结论: (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ != 0)
  证明: by
  refine ⟨?_, hx₀⟩
  rw [Module.End.mem_eigenspace_iff]
  exact hT.eq_smul_self_of_isLocalExtrOn hextr

Depends on / 依赖: Module, Module.End.mem_eigenspace_iff, eq_smul_self_of_isLocalExtrOn, hT.eq_smul_self_of_isLocalExtrOn, mem_eigenspace_iff
-/
theorem hasEigenvector_of_isLocalExtrOn (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ != 0)
    (hextr : IsLocalExtrOn T.reApplyInnerSelf (sphere (0 : E) ‖x₀‖) x₀) :
    HasEigenvector (T : E ->ₗ[𝕜] E) (T.rayleighQuotient x₀) x₀ := by
  refine ⟨?_, hx₀⟩
  rw [Module.End.mem_eigenspace_iff]
  exact hT.eq_smul_self_of_isLocalExtrOn hextr

/--
theorem `hasEigenvector_of_isMaxOn` / 定理 `hasEigenvector_of_isMaxOn`

English:
theorem hasEigenvector_of_isMaxOn
  statement: (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ != 0)
  proof: by
  convert! hT.hasEigenvector_of_isLocalExtrOn hx₀ (Or.inr hextr.localize)
  have hx₀' : 0 < ‖x₀‖ := by simp [hx₀]
  have hx₀'' : x₀ in sphere (0 : E) ‖x₀‖ := by simp
  rw [T.iSup_rayleigh_eq_iSup_rayleigh_sphere hx₀']
  refine IsMaxOn.iSup_eq hx₀'' ?_
  intro x hx
  dsimp
  have : ‖x‖ = ‖x₀‖ := b

中文:
定理 hasEigenvector_of_isMaxOn
  结论: (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ != 0)
  证明: by
  convert! hT.hasEigenvector_of_isLocalExtrOn hx₀ (Or.inr hextr.localize)
  have hx₀' : 0 < ‖x₀‖ := by simp [hx₀]
  have hx₀'' : x₀ in sphere (0 : E) ‖x₀‖ := by simp
  rw [T.iSup_rayleigh_eq_iSup_rayleigh_sphere hx₀']
  refine IsMaxOn.iSup_eq hx₀'' ?_
  intro x hx
  dsimp
  have : ‖x‖ = ‖x₀‖ := b

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.rayleighQuotient, IsMaxOn, IsMaxOn.iSup_eq, Or.inr, T.iSup_rayleigh_eq_iSup_rayleigh_sphere, convert, hT.hasEigenvector_of_isLocalExtrOn, hasEigenvector_of_isLocalExtrOn, hextr.localize, iSup_eq, iSup_rayleigh_eq_iSup_rayleigh_sphere, localize, rayleighQuotient, sphere
-/
theorem hasEigenvector_of_isMaxOn (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ != 0)
    (hextr : IsMaxOn T.reApplyInnerSelf (sphere (0 : E) ‖x₀‖) x₀) :
    HasEigenvector (T : E ->ₗ[𝕜] E) (⨆ x : { x : E // x != 0 }, T.rayleighQuotient x : Real) x₀ := by
  convert! hT.hasEigenvector_of_isLocalExtrOn hx₀ (Or.inr hextr.localize)
  have hx₀' : 0 < ‖x₀‖ := by simp [hx₀]
  have hx₀'' : x₀ in sphere (0 : E) ‖x₀‖ := by simp
  rw [T.iSup_rayleigh_eq_iSup_rayleigh_sphere hx₀']
  refine IsMaxOn.iSup_eq hx₀'' ?_
  intro x hx
  dsimp
  have : ‖x‖ = ‖x₀‖ := by simpa using hx
  simp only [ContinuousLinearMap.rayleighQuotient]
  rw [this]
  gcongr
  exact hextr hx

/--
theorem `hasEigenvector_of_isMinOn` / 定理 `hasEigenvector_of_isMinOn`

English:
theorem hasEigenvector_of_isMinOn
  statement: (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ != 0)
  proof: by
  convert! hT.hasEigenvector_of_isLocalExtrOn hx₀ (Or.inl hextr.localize)
  have hx₀' : 0 < ‖x₀‖ := by simp [hx₀]
  have hx₀'' : x₀ in sphere (0 : E) ‖x₀‖ := by simp
  rw [T.iInf_rayleigh_eq_iInf_rayleigh_sphere hx₀']
  refine IsMinOn.iInf_eq hx₀'' ?_
  intro x hx
  dsimp
  have : ‖x‖ = ‖x₀‖ := b

中文:
定理 hasEigenvector_of_isMinOn
  结论: (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ != 0)
  证明: by
  convert! hT.hasEigenvector_of_isLocalExtrOn hx₀ (Or.inl hextr.localize)
  have hx₀' : 0 < ‖x₀‖ := by simp [hx₀]
  have hx₀'' : x₀ in sphere (0 : E) ‖x₀‖ := by simp
  rw [T.iInf_rayleigh_eq_iInf_rayleigh_sphere hx₀']
  refine IsMinOn.iInf_eq hx₀'' ?_
  intro x hx
  dsimp
  have : ‖x‖ = ‖x₀‖ := b

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.rayleighQuotient, IsMinOn, IsMinOn.iInf_eq, Or.inl, T.iInf_rayleigh_eq_iInf_rayleigh_sphere, convert, hT.hasEigenvector_of_isLocalExtrOn, hasEigenvector_of_isLocalExtrOn, hextr.localize, iInf_eq, iInf_rayleigh_eq_iInf_rayleigh_sphere, localize, rayleighQuotient, sphere
-/
theorem hasEigenvector_of_isMinOn (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ != 0)
    (hextr : IsMinOn T.reApplyInnerSelf (sphere (0 : E) ‖x₀‖) x₀) :
    HasEigenvector (T : E ->ₗ[𝕜] E) (⨅ x : { x : E // x != 0 }, T.rayleighQuotient x : Real) x₀ := by
  convert! hT.hasEigenvector_of_isLocalExtrOn hx₀ (Or.inl hextr.localize)
  have hx₀' : 0 < ‖x₀‖ := by simp [hx₀]
  have hx₀'' : x₀ in sphere (0 : E) ‖x₀‖ := by simp
  rw [T.iInf_rayleigh_eq_iInf_rayleigh_sphere hx₀']
  refine IsMinOn.iInf_eq hx₀'' ?_
  intro x hx
  dsimp
  have : ‖x‖ = ‖x₀‖ := by simpa using hx
  simp only [ContinuousLinearMap.rayleighQuotient]
  rw [this]
  gcongr
  exact hextr hx

end CompleteSpace

end IsSelfAdjoint

section FiniteDimensional

variable [FiniteDimensional 𝕜 E] {T : E ->ₗ[𝕜] E}

namespace LinearMap

namespace IsSymmetric

/--
theorem `hasEigenvalue_iSup_of_finiteDimensional` / 定理 `hasEigenvalue_iSup_of_finiteDimensional`

English:
theorem hasEigenvalue_iSup_of_finiteDimensional
  given: [Nontrivial E] (hT : T.IsSymmetric)
  proof: by
  have := FiniteDimensional.proper_rclike 𝕜 E
  let T' := hT.toSelfAdjoint
  obtain ⟨x, hx⟩ : exists x : E, x != 0 := exists_ne 0
  have H₁ : IsCompact (sphere (0 : E) ‖x‖) := isCompact_sphere _ _
  have H₂ : (sphere (0 : E) ‖x‖).Nonempty := ⟨x, by simp⟩
  -- key point: in finite dimension, a con

中文:
定理 hasEigenvalue_iSup_of_finiteDimensional
  条件: [非平凡 E] (hT : T.IsSymmetric)
  证明: by
  have := FiniteDimensional.proper_rclike 𝕜 E
  let T' := hT.toSelfAdjoint
  obtain ⟨x, hx⟩ : exists x : E, x != 0 := exists_ne 0
  have H₁ : IsCompact (sphere (0 : E) ‖x‖) := isCompact_sphere _ _
  have H₂ : (sphere (0 : E) ‖x‖).Nonempty := ⟨x, by simp⟩
  -- key point: in finite dimension, a con

Depends on / 依赖: FiniteDimensional, FiniteDimensional.proper_rclike, IsCompact, Nonempty, exists_ne, hT.toSelfAdjoint, isCompact_sphere, proper_rclike, sphere, toSelfAdjoint
-/
theorem hasEigenvalue_iSup_of_finiteDimensional [Nontrivial E] (hT : T.IsSymmetric) :
    HasEigenvalue T (⨆ x : { x : E // x != 0 }, RCLike.re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2 : Real) := by
  have := FiniteDimensional.proper_rclike 𝕜 E
  let T' := hT.toSelfAdjoint
  obtain ⟨x, hx⟩ : exists x : E, x != 0 := exists_ne 0
  have H₁ : IsCompact (sphere (0 : E) ‖x‖) := isCompact_sphere _ _
  have H₂ : (sphere (0 : E) ‖x‖).Nonempty := ⟨x, by simp⟩
  -- key point: in finite dimension, a continuous function on the sphere has a max
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_isMaxOn H₂ T'.val.reApplyInnerSelf_continuous.continuousOn
  have hx₀ : ‖x₀‖ = ‖x‖ := by simpa using hx₀'
  have : IsMaxOn T'.val.reApplyInnerSelf (sphere 0 ‖x₀‖) x₀ := by simpa only [← hx₀] using hTx₀
  have hx₀_ne : x₀ != 0 := by
    have : ‖x₀‖ != 0 := by simp only [hx₀, norm_eq_zero, hx, Ne, not_false_iff]
    simpa [← norm_eq_zero, Ne]
  exact hasEigenvalue_of_hasEigenvector (T'.prop.hasEigenvector_of_isMaxOn hx₀_ne this)

/--
theorem `hasEigenvalue_iInf_of_finiteDimensional` / 定理 `hasEigenvalue_iInf_of_finiteDimensional`

English:
theorem hasEigenvalue_iInf_of_finiteDimensional
  given: [Nontrivial E] (hT : T.IsSymmetric)
  proof: by
  have := FiniteDimensional.proper_rclike 𝕜 E
  let T' := hT.toSelfAdjoint
  obtain ⟨x, hx⟩ : exists x : E, x != 0 := exists_ne 0
  have H₁ : IsCompact (sphere (0 : E) ‖x‖) := isCompact_sphere _ _
  have H₂ : (sphere (0 : E) ‖x‖).Nonempty := ⟨x, by simp⟩
  -- key point: in finite dimension, a con

中文:
定理 hasEigenvalue_iInf_of_finiteDimensional
  条件: [非平凡 E] (hT : T.IsSymmetric)
  证明: by
  have := FiniteDimensional.proper_rclike 𝕜 E
  let T' := hT.toSelfAdjoint
  obtain ⟨x, hx⟩ : exists x : E, x != 0 := exists_ne 0
  have H₁ : IsCompact (sphere (0 : E) ‖x‖) := isCompact_sphere _ _
  have H₂ : (sphere (0 : E) ‖x‖).Nonempty := ⟨x, by simp⟩
  -- key point: in finite dimension, a con

Depends on / 依赖: FiniteDimensional, FiniteDimensional.proper_rclike, IsCompact, Nonempty, exists_ne, hT.toSelfAdjoint, isCompact_sphere, proper_rclike, sphere, toSelfAdjoint
-/
theorem hasEigenvalue_iInf_of_finiteDimensional [Nontrivial E] (hT : T.IsSymmetric) :
    HasEigenvalue T (⨅ x : { x : E // x != 0 }, RCLike.re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2 : Real) := by
  have := FiniteDimensional.proper_rclike 𝕜 E
  let T' := hT.toSelfAdjoint
  obtain ⟨x, hx⟩ : exists x : E, x != 0 := exists_ne 0
  have H₁ : IsCompact (sphere (0 : E) ‖x‖) := isCompact_sphere _ _
  have H₂ : (sphere (0 : E) ‖x‖).Nonempty := ⟨x, by simp⟩
  -- key point: in finite dimension, a continuous function on the sphere has a min
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_isMinOn H₂ T'.val.reApplyInnerSelf_continuous.continuousOn
  have hx₀ : ‖x₀‖ = ‖x‖ := by simpa using hx₀'
  have : IsMinOn T'.val.reApplyInnerSelf (sphere 0 ‖x₀‖) x₀ := by simpa only [← hx₀] using hTx₀
  have hx₀_ne : x₀ != 0 := by
    have : ‖x₀‖ != 0 := by simp only [hx₀, norm_eq_zero, hx, Ne, not_false_iff]
    simpa [← norm_eq_zero, Ne]
  exact hasEigenvalue_of_hasEigenvector (T'.prop.hasEigenvector_of_isMinOn hx₀_ne this)

/--
theorem `subsingleton_of_no_eigenvalue_finiteDimensional` / 定理 `subsingleton_of_no_eigenvalue_finiteDimensional`

English:
theorem subsingleton_of_no_eigenvalue_finiteDimensional
  statement: (hT : T.IsSymmetric)
  proof: (subsingleton_or_nontrivial E).resolve_right fun _h =>
    absurd (hT' _) hT.hasEigenvalue_iSup_of_finiteDimensional

中文:
定理 subsingleton_of_no_eigenvalue_finiteDimensional
  结论: (hT : T.IsSymmetric)
  证明: (subsingleton_or_nontrivial E).resolve_right fun _h =>
    absurd (hT' _) hT.hasEigenvalue_iSup_of_finiteDimensional

Depends on / 依赖: absurd, hT.hasEigenvalue_iSup_of_finiteDimensional, hasEigenvalue_iSup_of_finiteDimensional, resolve_right, subsingleton_or_nontrivial
-/
theorem subsingleton_of_no_eigenvalue_finiteDimensional (hT : T.IsSymmetric)
    (hT' : forall μ : 𝕜, Module.End.eigenspace (T : E ->ₗ[𝕜] E) μ = ⊥) : Subsingleton E :=
  (subsingleton_or_nontrivial E).resolve_right fun _h =>
    absurd (hT' _) hT.hasEigenvalue_iSup_of_finiteDimensional

end IsSymmetric

end LinearMap

end FiniteDimensional
