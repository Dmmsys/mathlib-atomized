/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated

/-!
# Transitivity and properness of actions

We show that the actions of `SL(2, ℝ)` and `GL(2, ℝ)` on the upper half-plane are jointly
continuous, and the action of `SL(2, ℝ)` is proper. (These results require more imports
than in `UpperHalfPlane.Topology`, because they use the topology on the group as well)

TODO: Show properness of the action of `PGL(2, ℝ)` once this is defined.
-/

open scoped MatrixGroups Pointwise

public section

namespace UpperHalfPlane

@[fun_prop]
/--
theorem `num_continuous` / 定理 `num_continuous`

English:
theorem num_continuous
  statement: Continuous ↿num
  proof: by unfold num; fun_prop

@[fun_prop]

中文:
定理 num_continuous
  结论: 连续 ↿num
  证明: by unfold num; fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
theorem num_continuous : Continuous ↿num := by unfold num; fun_prop

@[fun_prop]
/--
theorem `denom_continuous` / 定理 `denom_continuous`

English:
theorem denom_continuous
  statement: Continuous ↿denom
  proof: by unfold denom; fun_prop

中文:
定理 denom_continuous
  结论: 连续 ↿denom
  证明: by unfold denom; fun_prop

Depends on / 依赖: fun_prop
-/
theorem denom_continuous : Continuous ↿denom := by unfold denom; fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `continuous_toSL2R` / 引理 `continuous_toSL2R`

English:
lemma continuous_toSL2R
  statement: Continuous toSL2R
  proof: by
  apply continuous_induced_rng.mpr
  simp only [Function.comp_def, coe_toSL2R]
  fun_prop (disch := grind [im_pos])

中文:
引理 continuous_toSL2R
  结论: 连续 toSL2R
  证明: by
  apply continuous_induced_rng.mpr
  simp only [Function.comp_def, coe_toSL2R]
  fun_prop (disch := grind [im_pos])

Depends on / 依赖: Function, Function.comp_def, coe_toSL2R, comp_def, continuous_induced_rng, continuous_induced_rng.mpr, fun_prop, im_pos
-/
lemma continuous_toSL2R : Continuous toSL2R := by
  apply continuous_induced_rng.mpr
  simp only [Function.comp_def, coe_toSL2R]
  fun_prop (disch := grind [im_pos])

/--
Instance `instContinuousSMulSL2R` / 实例 `instContinuousSMulSL2R`

English:
instance instContinuousSMulSL2R
  signature: : ContinuousSMul SL(2, Real) ℍ where
  body: by
    suffices forall (g : SL(2, Real)) (τ : ℍ),
        ContinuousAt (fun ⟨h, z⟩ => (h 0 0 * (z : Complex) + h 0 1) / (h 1 0 * z + h 1 1)) (g, τ) by
      simpa [continuous_induced_rng, continuous_iff_continuousAt, Function.comp_def,
        coe_specialLinearGroup_apply]
    intro g τ
    fun_prop

中文:
实例 instContinuousSMulSL2R
  签名: : 连续标量乘法 SL(2, 实数) ℍ where
  定义体: by
    suffices forall (g : SL(2, Real)) (τ : ℍ),
        ContinuousAt (fun ⟨h, z⟩ => (h 0 0 * (z : Complex) + h 0 1) / (h 1 0 * z + h 1 1)) (g, τ) by
      simpa [continuous_induced_rng, continuous_iff_continuousAt, Function.comp_def,
        coe_specialLinearGroup_apply]
    intro g τ
    fun_prop

Depends on / 依赖: ContinuousAt, Function, Function.comp_def, coe_specialLinearGroup_apply, comp_def, continuous_iff_continuousAt, continuous_induced_rng, denom_ne_zero, fun_prop
-/
instance instContinuousSMulSL2R : ContinuousSMul SL(2, Real) ℍ where
  continuous_smul := by
    suffices forall (g : SL(2, Real)) (τ : ℍ),
        ContinuousAt (fun ⟨h, z⟩ => (h 0 0 * (z : Complex) + h 0 1) / (h 1 0 * z + h 1 1)) (g, τ) by
      simpa [continuous_induced_rng, continuous_iff_continuousAt, Function.comp_def,
        coe_specialLinearGroup_apply]
    intro g τ
    fun_prop (disch := exact denom_ne_zero g τ)

open Topology in
/--
lemma `σ_eventuallyEq` / 引理 `σ_eventuallyEq`

English:
lemma σ_eventuallyEq
  given: (g : GL (Fin 2) Real)
  statement: σ =ᶠ[𝓝 g] fun _ => σ g
  proof: by
  by_cases hg : 0 < g.det.val
  · suffices {h | 0 < h.det.val} in 𝓝 g by
      filter_upwards [this] with h hh using by simp only [σ, hh, ↓reduceIte, hg]
.mem_nhds hg .preimage (by fun_prop) exact isOpen_Ioi (a := (0 : Real))
  · suffices {h | ¬0 < h.det.val} in 𝓝 g by
      filter_upwards [this]

中文:
引理 σ_eventuallyEq
  条件: (g : GL (有限集 2) 实数)
  结论: σ =ᶠ[𝓝 g] fun _ => σ g
  证明: by
  by_cases hg : 0 < g.det.val
  · suffices {h | 0 < h.det.val} in 𝓝 g by
      filter_upwards [this] with h hh using by simp only [σ, hh, ↓reduceIte, hg]
.mem_nhds hg .preimage (by fun_prop) exact isOpen_Ioi (a := (0 : Real))
  · suffices {h | ¬0 < h.det.val} in 𝓝 g by
      filter_upwards [this]

Depends on / 依赖: Units.ne_zero, filter_upwards, fun_prop, g.det.val, h.det.val, isOpen_Iio, isOpen_Ioi, le_iff_lt_or_eq, mem_nhds, ne_zero, not_lt, or_false, preimage, reduceIte
-/
lemma σ_eventuallyEq (g : GL (Fin 2) Real) : σ =ᶠ[𝓝 g] fun _ => σ g := by
  by_cases hg : 0 < g.det.val
  · suffices {h | 0 < h.det.val} in 𝓝 g by
      filter_upwards [this] with h hh using by simp only [σ, hh, ↓reduceIte, hg]
.mem_nhds hg .preimage (by fun_prop) exact isOpen_Ioi (a := (0 : Real))
  · suffices {h | ¬0 < h.det.val} in 𝓝 g by
      filter_upwards [this] with h hh using by simp only [σ, hh, ↓reduceIte, hg]
    simp only [not_lt, le_iff_lt_or_eq, Units.ne_zero, or_false] at hg ⊢
.mem_nhds hg .preimage (by fun_prop) exact isOpen_Iio (a := (0 : Real))

/--
Instance `instContinuousSMulGL2R` / 实例 `instContinuousSMulGL2R`

English:
instance instContinuousSMulGL2R
  signature: : ContinuousSMul (GL (Fin 2) Real) ℍ
  body: by
  constructor
  simp only [continuous_induced_rng, Function.comp_def, coe_smul, continuous_iff_continuousAt,
    Prod.forall]
  refine fun g τ => .congr ?_ (f := fun x => (σ g) (num x.1 x.2 / denom x.1 x.2))
    (by filter_upwards [(σ_eventuallyEq g).prod_inl_nhds _] using by simp +contextual)
  

中文:
实例 instContinuousSMulGL2R
  签名: : 连续标量乘法 (GL (有限集 2) 实数) ℍ
  定义体: by
  constructor
  simp only [continuous_induced_rng, Function.comp_def, coe_smul, continuous_iff_continuousAt,
    Prod.forall]
  refine fun g τ => .congr ?_ (f := fun x => (σ g) (num x.1 x.2 / denom x.1 x.2))
    (by filter_upwards [(σ_eventuallyEq g).prod_inl_nhds _] using by simp +contextual)
  

Depends on / 依赖: Function, Function.comp_def, Prod.forall, coe_smul, comp_def, contextual, continuous_iff_continuousAt, continuous_induced_rng, denom_ne_zero, filter_upwards, fun_prop, prod_inl_nhds
-/
instance instContinuousSMulGL2R : ContinuousSMul (GL (Fin 2) Real) ℍ := by
  constructor
  simp only [continuous_induced_rng, Function.comp_def, coe_smul, continuous_iff_continuousAt,
    Prod.forall]
  refine fun g τ => .congr ?_ (f := fun x => (σ g) (num x.1 x.2 / denom x.1 x.2))
    (by filter_upwards [(σ_eventuallyEq g).prod_inl_nhds _] using by simp +contextual)
  fun_prop (disch := apply denom_ne_zero)

section proper_orbit_map

/--
lemma `cdsq_le` / 引理 `cdsq_le`

English:
lemma cdsq_le
  given: {K : Set ℍ} (hK : IsCompact K)
  proof: by
  rcases K.eq_empty_or_nonempty with rfl | hKne; · simp
  obtain ⟨δ, hδ, hδK⟩ : exists δ > 0, forall z in K, δ <= z.im :=
    match hK.exists_isMinOn hKne continuous_im.continuousOn with | ⟨z, _, h⟩ => ⟨_, z.im_pos, h⟩
  refine ⟨1 / δ, fun g hg => ?_⟩
  specialize hδK (g • I) hg
  simp only [MulA

中文:
引理 cdsq_le
  条件: {K : 集合 ℍ} (hK : 是紧集 K)
  证明: by
  rcases K.eq_empty_or_nonempty with rfl | hKne; · simp
  obtain ⟨δ, hδ, hδK⟩ : exists δ > 0, forall z in K, δ <= z.im :=
    match hK.exists_isMinOn hKne continuous_im.continuousOn with | ⟨z, _, h⟩ => ⟨_, z.im_pos, h⟩
  refine ⟨1 / δ, fun g hg => ?_⟩
  specialize hδK (g • I) hg
  simp only [MulA
-/
private lemma cdsq_le {K : Set ℍ} (hK : IsCompact K) :
    exists A, forall g : SL(2, Real), g • I in K -> g 1 0 ^ 2 + g 1 1 ^ 2 <= A := by
  rcases K.eq_empty_or_nonempty with rfl | hKne; · simp
  obtain ⟨δ, hδ, hδK⟩ : exists δ > 0, forall z in K, δ <= z.im :=
    match hK.exists_isMinOn hKne continuous_im.continuousOn with | ⟨z, _, h⟩ => ⟨_, z.im_pos, h⟩
  refine ⟨1 / δ, fun g hg => ?_⟩
  specialize hδK (g • I) hg
  simp only [MulAction.compHom_smul_def, im_smul_eq_div_normSq, Matrix.SpecialLinearGroup.det_mapGL,
    Units.val_one, abs_one, I_im, mul_one] at hδK
  rw [le_div_iff₀ (normSq_denom_pos (Matrix.SpecialLinearGroup.mapGL Real g) (show I.im != 0 by simp))]; rw [mul_comm]; rw [← le_div_iff₀ hδ] at hδK
  simpa [Complex.normSq, add_comm, denom, sq] using hδK

/--
lemma `absq_le` / 引理 `absq_le`

English:
lemma absq_le
  given: {K : Set ℍ} (hK : IsCompact K)
  proof: by
  let S : SL(2, Real) := ⟨!![0, -1; 1, 0], by simp⟩
  obtain ⟨A, hA⟩ := cdsq_le (K := S • K) (hK.image <| continuous_const_smul S)
  refine ⟨A, fun g hg => ?_⟩
  convert! hA (S * g) (by rwa [mul_smul, Set.smul_mem_smul_set_iff]) using 1
  rw [Matrix.SpecialLinearGroup.coe_mul]; rw [Matrix.eta_fin

中文:
引理 absq_le
  条件: {K : 集合 ℍ} (hK : 是紧集 K)
  证明: by
  let S : SL(2, Real) := ⟨!![0, -1; 1, 0], by simp⟩
  obtain ⟨A, hA⟩ := cdsq_le (K := S • K) (hK.image <| continuous_const_smul S)
  refine ⟨A, fun g hg => ?_⟩
  convert! hA (S * g) (by rwa [mul_smul, Set.smul_mem_smul_set_iff]) using 1
  rw [Matrix.SpecialLinearGroup.coe_mul]; rw [Matrix.eta_fin
-/
private lemma absq_le {K : Set ℍ} (hK : IsCompact K) :
    exists A : Real, forall g : SL(2, Real), g • I in K -> g 0 0 ^ 2 + g 0 1 ^ 2 <= A := by
  let S : SL(2, Real) := ⟨!![0, -1; 1, 0], by simp⟩
  obtain ⟨A, hA⟩ := cdsq_le (K := S • K) (hK.image <| continuous_const_smul S)
  refine ⟨A, fun g hg => ?_⟩
  convert! hA (S * g) (by rwa [mul_smul, Set.smul_mem_smul_set_iff]) using 1
  rw [Matrix.SpecialLinearGroup.coe_mul]; rw [Matrix.eta_fin_two g.val]; rw [Matrix.mul_fin_two]
  simp

/--
lemma `isProperMap_smul_I` / 引理 `isProperMap_smul_I`

English:
lemma isProperMap_smul_I
  statement: IsProperMap fun g : SL(2, Real) => g • I
  proof: by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨by fun_prop, fun K hK => ?_⟩
  obtain ⟨A, hA⟩ := absq_le hK
  obtain ⟨A', hA'⟩ := cdsq_le hK
  -- activate the sup-norm on matrices
  let : SeminormedAddCommGroup (Matrix (Fin 2) (Fin 2) Real) := Matrix.seminormedAddCommGroup
  have : ProperSpace (

中文:
引理 isProperMap_smul_I
  结论: 是真映射 fun g : SL(2, 实数) => g • I
  证明: by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨by fun_prop, fun K hK => ?_⟩
  obtain ⟨A, hA⟩ := absq_le hK
  obtain ⟨A', hA'⟩ := cdsq_le hK
  -- activate the sup-norm on matrices
  let : SeminormedAddCommGroup (Matrix (Fin 2) (Fin 2) Real) := Matrix.seminormedAddCommGroup
  have : ProperSpace (

Depends on / 依赖: absq_le, cdsq_le, fun_prop, isProperMap_iff_isCompact_preimage, isProperMap_iff_isCompact_preimage.mpr
-/
lemma isProperMap_smul_I : IsProperMap fun g : SL(2, Real) => g • I := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨by fun_prop, fun K hK => ?_⟩
  obtain ⟨A, hA⟩ := absq_le hK
  obtain ⟨A', hA'⟩ := cdsq_le hK
  -- activate the sup-norm on matrices
  let : SeminormedAddCommGroup (Matrix (Fin 2) (Fin 2) Real) := Matrix.seminormedAddCommGroup
  have : ProperSpace (Matrix (Fin 2) (Fin 2) Real) := pi_properSpace
  have : IsCompact {m : Matrix (Fin 2) (Fin 2) Real | forall i j, |m i j| <= max √A √A'} := by
    convert! ProperSpace.isCompact_closedBall (0 : Matrix (Fin 2) (Fin 2) Real) (max √A √A')
    simp only [le_sup_iff, Fin.forall_fin_two, Fin.isValue, Metric.closedBall, dist_zero_right,
      Matrix.norm_def, pi_norm_le_iff_of_nonempty, Real.norm_eq_abs]
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `ext` was not necessary.
    The cause of this might be `Matrix` function application defeq abuse. -/
    ext; grind
  have := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage this
  refine this.of_isClosed_subset (hK.isClosed.preimage <| by fun_prop) (fun g hg => ?_)
  intro i j
  fin_cases i
· refine le_trans ?_ le_max_left √A √A'
exact Real.le_sqrt_of_sq_le le_trans (by fin_cases j <;> simp [sq_nonneg]) (hA g hg)
· refine le_trans ?_ le_max_right √A √A'
exact Real.le_sqrt_of_sq_le le_trans (by fin_cases j <;> simp [sq_nonneg]) (hA' g hg)

/--
Instance `instProperSMul` / 实例 `instProperSMul`

English:
instance instProperSMul
  signature: : ProperSMul SL(2, Real) ℍ
  body: MulAction.properSMul_of_proper_orbitMap isProperMap_smul_I

中文:
实例 instProperSMul
  签名: : 真标量乘法 SL(2, 实数) ℍ
  定义体: MulAction.properSMul_of_proper_orbitMap isProperMap_smul_I

Depends on / 依赖: MulAction, MulAction.properSMul_of_proper_orbitMap, isProperMap_smul_I, properSMul_of_proper_orbitMap
-/
instance instProperSMul : ProperSMul SL(2, Real) ℍ :=
  MulAction.properSMul_of_proper_orbitMap isProperMap_smul_I

end proper_orbit_map

/--
Instance `instProperlyDiscontinuousSL2RSubgroup` / 实例 `instProperlyDiscontinuousSL2RSubgroup`

English:
instance instProperlyDiscontinuousSL2RSubgroup
  signature: (𝒢 : Subgroup SL(2, Real)) [DiscreteTopology 𝒢]
  body: by
  have : IsClosed (𝒢 : Set SL(2, Real)) := Subgroup.isClosed_of_discrete
  rw [properlyDiscontinuousSMul_iff_properSMul]
  infer_instance

中文:
实例 instProperlyDiscontinuousSL2RSubgroup
  签名: (𝒢 : 子群 SL(2, 实数)) [离散拓扑 𝒢]
  定义体: by
  have : IsClosed (𝒢 : Set SL(2, Real)) := Subgroup.isClosed_of_discrete
  rw [properlyDiscontinuousSMul_iff_properSMul]
  infer_instance

Depends on / 依赖: IsClosed, Subgroup, Subgroup.isClosed_of_discrete, infer_instance, isClosed_of_discrete, properlyDiscontinuousSMul_iff_properSMul
-/
instance instProperlyDiscontinuousSL2RSubgroup (𝒢 : Subgroup SL(2, Real)) [DiscreteTopology 𝒢] :
    ProperlyDiscontinuousSMul 𝒢 ℍ := by
  have : IsClosed (𝒢 : Set SL(2, Real)) := Subgroup.isClosed_of_discrete
  rw [properlyDiscontinuousSMul_iff_properSMul]
  infer_instance

end UpperHalfPlane

end
