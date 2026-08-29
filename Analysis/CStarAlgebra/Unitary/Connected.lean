/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-! # The unitary group in a unital C⋆-algebra is locally path connected

When `A` is a unital C⋆-algebra and `u : unitary A` is a unitary element whose distance to `1` is
less that `2`, the spectrum of `u` is contained in the slit plane, so the principal branch of the
logarithm is continuous on the spectrum of `u` (or equivalently, `Complex.arg` is continuous on the
spectrum). The continuous functional calculus can then be used to define a selfadjoint element `x`
such that `u = exp (I • x)`. Moreover, there is a relatively nice relationship between the norm of
`x` and the norm of `u - 1`, namely `‖u - 1‖ ^ 2 = 2 * (1 - cos ‖x‖)`. In fact, these maps `u ↦ x`
and `x ↦ u` establish a partial homeomorphism between `ball (1 : unitary A) 2` and
`ball (0 : selfAdjoint A) π`.

The map `t ↦ exp (t • (I • x))` constitutes a path from `1` to `u`, showing that unitary elements
sufficiently close (i.e., within a distance `2`) to `1 : unitary A` are path connected to `1`.
This property can be translated around the unitary group to show that if `u v : unitary A` are
unitary elements with `‖u - v‖ < 2`, then there is a path joining them. In fact, this path has the
property that it lies within `closedBall u ‖u - v‖`, and consequently any ball of radius `δ < 2` in
`unitary A` is path connected. Therefore, the unitary group is locally path connected.

Finally, we provide the standard characterization of the path component of `1 : unitary A` as finite
products of exponential unitaries.

## Main results

+ `Unitary.argSelfAdjoint`: the selfadjoint element obtained by taking the argument (using the
  principal branch and the continuous functional calculus) of a unitary. This returns `0` if
  the principal branch of the logarithm is not continuous on the spectrum of the unitary element.
+ `selfAdjoint.norm_sq_expUnitary_sub_one`:
  `‖(selfAdjoint.expUnitary x - 1 : A)‖ ^ 2 = 2 * (1 - Real.cos ‖x‖)`
+ `Unitary.norm_argSelfAdjoint`:
  `‖Unitary.argSelfAdjoint u‖ = Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2)`
+ `Unitary.openPartialHomeomorph`: the maps `Unitary.argSelfAdjoint` and `selfAdjoint.expUnitary`
  form a partial homeomorphism between `ball (1 : unitary A) 2` and `ball (0 : selfAdjoint A) π`.
+ `selfAdjoint.expUnitaryPathToOne`: the path `t ↦ expUnitary (t • x)` from `1` to
  `expUnitary x` for a selfadjoint element `x`.
+ `Unitary.isPathConnected_ball`: any ball of radius `δ < 2` in the unitary group of a unital
  C⋆-algebra is path connected.
+ `Unitary.instLocallyPathConnectedSpace`: the unitary group of a C⋆-algebra is
  locally path connected.
+ `Unitary.mem_pathComponentOne_iff`: The path component of the identity in the unitary group of a
  C⋆-algebra is the set of unitaries that can be expressed as a product of exponentials of
  selfadjoint elements.
-/

@[expose] public section

variable {A : Type*} [CStarAlgebra A]

open Complex Metric NormedSpace selfAdjoint Unitary
open scoped Real

/--
lemma `Unitary.two_mul_one_sub_le_norm_sub_one_sq` / 引理 `Unitary.two_mul_one_sub_le_norm_sub_one_sq`

English:
lemma Unitary.two_mul_one_sub_le_norm_sub_one_sq
  statement: {u : A} (hu : u in unitary A)
  proof: by
  rw [← Real.sqrt_le_left (by positivity)]
  have := spectrum.subset_circle_of_unitary hu hz
  simp only [mem_sphere_iff_norm, sub_zero] at this
  rw [← cfc_id' Complex u]; rw [← cfc_one Complex u]; rw [← cfc_sub ..]
  convert! norm_apply_le_norm_cfc (fun z => z - 1) u hz
  simpa using congr(Real

中文:
引理 酉.two_mul_one_sub_le_norm_sub_one_sq
  结论: {u : A} (hu : u in unitary A)
  证明: by
  rw [← Real.sqrt_le_left (by positivity)]
  have := spectrum.subset_circle_of_unitary hu hz
  simp only [mem_sphere_iff_norm, sub_zero] at this
  rw [← cfc_id' Complex u]; rw [← cfc_one Complex u]; rw [← cfc_sub ..]
  convert! norm_apply_le_norm_cfc (fun z => z - 1) u hz
  simpa using congr(Real

Depends on / 依赖: Real.sqrt, Real.sqrt_le_left, cfc_id, cfc_one, cfc_sub, convert, mem_sphere_iff_norm, norm_apply_le_norm_cfc, norm_sub_one_sq_eq_of_norm_eq_one, spectrum, spectrum.subset_circle_of_unitary, sqrt_le_left, sub_zero, subset_circle_of_unitary
-/
lemma Unitary.two_mul_one_sub_le_norm_sub_one_sq {u : A} (hu : u in unitary A)
    {z : Complex} (hz : z in spectrum Complex u) :
    2 * (1 - z.re) <= ‖u - 1‖ ^ 2 := by
  rw [← Real.sqrt_le_left (by positivity)]
  have := spectrum.subset_circle_of_unitary hu hz
  simp only [mem_sphere_iff_norm, sub_zero] at this
  rw [← cfc_id' Complex u]; rw [← cfc_one Complex u]; rw [← cfc_sub ..]
  convert! norm_apply_le_norm_cfc (fun z => z - 1) u hz
  simpa using congr(Real.sqrt $(norm_sub_one_sq_eq_of_norm_eq_one this)).symm

/--
lemma `Unitary.norm_sub_one_sq_eq` / 引理 `Unitary.norm_sub_one_sq_eq`

English:
lemma Unitary.norm_sub_one_sq_eq
  statement: {u : A} (hu : u in unitary A) {x : Real}
  proof: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · exfalso; apply hz.nonempty.of_image.ne_empty; simp
  rw [← cfc_id' Complex u]; rw [← cfc_one Complex u]; rw [← cfc_sub ..]
  have h_eqOn : (spectrum Complex u).EqOn (fun z => ‖z - 1‖ ^ 2) (fun z => 2 * (1 - z.re)) :=
Complex.norm_sub_one_sq_eqO

中文:
引理 酉.norm_sub_one_sq_eq
  结论: {u : A} (hu : u in unitary A) {x : 实数}
  证明: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · exfalso; apply hz.nonempty.of_image.ne_empty; simp
  rw [← cfc_id' Complex u]; rw [← cfc_one Complex u]; rw [← cfc_sub ..]
  have h_eqOn : (spectrum Complex u).EqOn (fun z => ‖z - 1‖ ^ 2) (fun z => 2 * (1 - z.re)) :=
Complex.norm_sub_one_sq_eqO

Depends on / 依赖: Antitone, Complex.norm_sub_one_sq_eqOn_sphere.mono, IsGreatest, cfc_id, cfc_one, cfc_sub, h_eqOn, hz.nonempty.of_image.ne_empty, ne_empty, nonempty, norm_sub_one_sq_eqOn_sphere, of_image, spectrum, spectrum.subset_circle_of_unitary, subset_circle_of_unitary, subsingleton_or_nontrivial, z.re
-/
lemma Unitary.norm_sub_one_sq_eq {u : A} (hu : u in unitary A) {x : Real}
    (hz : IsLeast (re '' (spectrum Complex u)) x) :
    ‖u - 1‖ ^ 2 = 2 * (1 - x) := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · exfalso; apply hz.nonempty.of_image.ne_empty; simp
  rw [← cfc_id' Complex u]; rw [← cfc_one Complex u]; rw [← cfc_sub ..]
  have h_eqOn : (spectrum Complex u).EqOn (fun z => ‖z - 1‖ ^ 2) (fun z => 2 * (1 - z.re)) :=
Complex.norm_sub_one_sq_eqOn_sphere.mono spectrum.subset_circle_of_unitary (𝕜 := Complex) hu
  have h₂ : IsGreatest ((fun z => 2 * (1 - z.re)) '' (spectrum Complex u)) (2 * (1 - x)) := by
    have : Antitone (fun y : Real => 2 * (1 - y)) := by intro _ _ _; simp only; gcongr
    simpa [Set.image_image] using this.map_isLeast hz
  have h₃ : IsGreatest ((‖· - 1‖ ^ 2) '' spectrum Complex u) (‖cfc (· - 1 : Complex -> Complex) u‖ ^ 2) := by
.mono (s₂ := ((‖· - 1‖) '' spectrum Complex u)) (by simp) have := pow_left_monotoneOn (n := 2)
    simpa [Set.image_image] using this.map_isGreatest (IsGreatest.norm_cfc (fun z : Complex => z - 1) u)
  exact h₃.unique (h_eqOn.image_eq ▸ h₂)

/--
lemma `Unitary.norm_sub_one_lt_two_iff` / 引理 `Unitary.norm_sub_one_lt_two_iff`

English:
lemma Unitary.norm_sub_one_lt_two_iff
  given: {u : A} (hu : u in unitary A)
  proof: by
  nontriviality A
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  constructor
  · intro h h1
.trans_lt h have := two_mul_one_sub_le_norm_sub_one_sq hu h1
    norm_num at this
  · contrapose!
.exists_isLeast .image continuous_re obtain ⟨x, hx⟩ := spectrum.isCompact (𝕜 := Complex) u
      (spe

中文:
引理 酉.norm_sub_one_lt_two_iff
  条件: {u : A} (hu : u in unitary A)
  证明: by
  nontriviality A
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  constructor
  · intro h h1
.trans_lt h have := two_mul_one_sub_le_norm_sub_one_sq hu h1
    norm_num at this
  · contrapose!
.exists_isLeast .image continuous_re obtain ⟨x, hx⟩ := spectrum.isCompact (𝕜 := Complex) u
      (spe

Depends on / 依赖: continuous_re, contrapose, exists_isLeast, hz_norm, isCompact, nonempty, nontriviality, norm_eq_one_of_unitary, norm_sub_one_sq_eq, replace, spectrum, spectrum.isCompact, spectrum.nonempty, spectrum.norm_eq_one_of_unitary, trans_lt, two_mul_one_sub_le_norm_sub_one_sq, z.re
-/
lemma Unitary.norm_sub_one_lt_two_iff {u : A} (hu : u in unitary A) :
    ‖u - 1‖ < 2 ↔ -1 ∉ spectrum Complex u := by
  nontriviality A
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  constructor
  · intro h h1
.trans_lt h have := two_mul_one_sub_le_norm_sub_one_sq hu h1
    norm_num at this
  · contrapose!
.exists_isLeast .image continuous_re obtain ⟨x, hx⟩ := spectrum.isCompact (𝕜 := Complex) u
      (spectrum.nonempty _).image _
    rw [norm_sub_one_sq_eq hu hx]
    obtain ⟨z, hz, rfl⟩ := hx.1
    intro key
    replace key : z.re <= -1 := by linarith
    have hz_norm : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary hu hz
    rw [← hz_norm]; rw [← RCLike.re_eq_complex_re]; rw [RCLike.re_le_neg_norm_iff_eq_neg_norm]; rw [hz_norm] at key
    exact key ▸ hz

/--
lemma `Unitary.spectrum_subset_slitPlane_iff_norm_lt_two` / 引理 `Unitary.spectrum_subset_slitPlane_iff_norm_lt_two`

English:
lemma Unitary.spectrum_subset_slitPlane_iff_norm_lt_two
  given: {u : A} (hu : u in unitary A)
  proof: by
  simp [subset_slitPlane_iff_of_subset_sphere (spectrum.subset_circle_of_unitary hu),
    norm_sub_one_lt_two_iff hu]

@[aesop safe apply (rule_sets := [CStarAlgebra])]

中文:
引理 酉.spectrum_subset_slitPlane_iff_norm_lt_two
  条件: {u : A} (hu : u in unitary A)
  证明: by
  simp [subset_slitPlane_iff_of_subset_sphere (spectrum.subset_circle_of_unitary hu),
    norm_sub_one_lt_two_iff hu]

@[aesop safe apply (rule_sets := [CStarAlgebra])]

Depends on / 依赖: norm_sub_one_lt_two_iff, spectrum, spectrum.subset_circle_of_unitary, subset_circle_of_unitary, subset_slitPlane_iff_of_subset_sphere
-/
lemma Unitary.spectrum_subset_slitPlane_iff_norm_lt_two {u : A} (hu : u in unitary A) :
    spectrum Complex u subseteq slitPlane ↔ ‖u - 1‖ < 2 := by
  simp [subset_slitPlane_iff_of_subset_sphere (spectrum.subset_circle_of_unitary hu),
    norm_sub_one_lt_two_iff hu]

@[aesop safe apply (rule_sets := [CStarAlgebra])]
/--
lemma `IsSelfAdjoint.cfc_arg` / 引理 `IsSelfAdjoint.cfc_arg`

English:
lemma IsSelfAdjoint.cfc_arg
  given: (u : A)
  statement: IsSelfAdjoint (cfc (ofReal ∘ arg : Complex -> Complex) u)
  proof: by
  simp [isSelfAdjoint_iff, ← cfc_star, Function.comp_def]

中文:
引理 IsSelfAdjoint.cfc_arg
  条件: (u : A)
  结论: IsSelfAdjoint (cfc (of实数 ∘ arg : 复形 -> 复形) u)
  证明: by
  simp [isSelfAdjoint_iff, ← cfc_star, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, cfc_star, comp_def, isSelfAdjoint_iff
-/
lemma IsSelfAdjoint.cfc_arg (u : A) : IsSelfAdjoint (cfc (ofReal ∘ arg : Complex -> Complex) u) := by
  simp [isSelfAdjoint_iff, ← cfc_star, Function.comp_def]

/-- The selfadjoint element obtained by taking the argument (using the principal branch and the
continuous functional calculus) of a unitary whose spectrum does not contain `-1`. This returns
`0` if the principal branch of the logarithm is not continuous on the spectrum of the unitary
element. -/
@[simps]
/--
Definition of `Unitary.argSelfAdjoint` / `Unitary.argSelfAdjoint` 的定义

English:
definition Unitary.argSelfAdjoint
  signature: (u : unitary A)
  body: ⟨cfc (arg · : Complex -> Complex) (u : A), .cfc_arg (u : A)⟩

中文:
定义 酉.argSelfAdjoint
  签名: (u : unitary A)
  定义体: ⟨cfc (arg · : Complex -> Complex) (u : A), .cfc_arg (u : A)⟩

Depends on / 依赖: cfc_arg
-/
noncomputable def Unitary.argSelfAdjoint (u : unitary A) : selfAdjoint A :=
  ⟨cfc (arg · : Complex -> Complex) (u : A), .cfc_arg (u : A)⟩

/--
lemma `selfAdjoint.norm_sq_expUnitary_sub_one` / 引理 `selfAdjoint.norm_sq_expUnitary_sub_one`

English:
lemma selfAdjoint.norm_sq_expUnitary_sub_one
  given: {x : selfAdjoint A} (hx : ‖x‖ <= π)
  proof: by
  nontriviality A
  apply norm_sub_one_sq_eq (expUnitary x).2
  simp only [expUnitary_coe]
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := Complex)]; rw [← cfc_comp_smul I _ (x : A)]; rw [cfc_map_spectrum ..]; rw [← x.2.spectrumRestricts.algebraMap_image]
  simp only [Set.image_image, coe_algebraMap, sm

中文:
引理 selfAdjoint.norm_sq_expUnitary_sub_one
  条件: {x : selfAdjoint A} (hx : ‖x‖ <= π)
  证明: by
  nontriviality A
  apply norm_sub_one_sq_eq (expUnitary x).2
  simp only [expUnitary_coe]
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := Complex)]; rw [← cfc_comp_smul I _ (x : A)]; rw [cfc_map_spectrum ..]; rw [← x.2.spectrumRestricts.algebraMap_image]
  simp only [Set.image_image, coe_algebraMap, sm

Depends on / 依赖: CFC.exp_eq_normedSpace_exp, CStarAlgebra, CStarAlgebra.norm_or_neg_norm_mem_spectrum, Set.image_image, algebraMap_image, cfc_comp_smul, cfc_map_spectrum, coe_algebraMap, expUnitary, expUnitary_coe, exp_eq_exp_Complex, exp_eq_normedSpace_exp, exp_ofReal_mul_I_re, image_image, mul_comm, nontriviality, norm_or_neg_norm_mem_spectrum, norm_sub_one_sq_eq, smul_eq_mul, spectrumRestricts
-/
lemma selfAdjoint.norm_sq_expUnitary_sub_one {x : selfAdjoint A} (hx : ‖x‖ <= π) :
    ‖(expUnitary x - 1 : A)‖ ^ 2 = 2 * (1 - Real.cos ‖x‖) := by
  nontriviality A
  apply norm_sub_one_sq_eq (expUnitary x).2
  simp only [expUnitary_coe]
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := Complex)]; rw [← cfc_comp_smul I _ (x : A)]; rw [cfc_map_spectrum ..]; rw [← x.2.spectrumRestricts.algebraMap_image]
  simp only [Set.image_image, coe_algebraMap, smul_eq_mul, mul_comm I, ← exp_eq_exp_Complex,
    exp_ofReal_mul_I_re]
  refine ⟨?_, ?_⟩
  · cases CStarAlgebra.norm_or_neg_norm_mem_spectrum x.2 with
    | inl h => exact ⟨_, h, rfl⟩
    | inr h => exact ⟨_, h, by simp⟩
  · rintro - ⟨y, hy, rfl⟩
exact Real.cos_abs y ▸ Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hx
      spectrum.norm_le_norm_of_mem hy

/--
lemma `argSelfAdjoint_expUnitary` / 引理 `argSelfAdjoint_expUnitary`

English:
lemma argSelfAdjoint_expUnitary
  given: {x : selfAdjoint A} (hx : ‖x‖ < π)
  proof: by
  nontriviality A
  ext
  have : spectrum Complex (expUnitary x : A) subseteq slitPlane := by
    rw [spectrum_subset_slitPlane_iff_norm_lt_two (expUnitary x).2]; rw [← sq_lt_sq₀ (by positivity) (by positivity)]; rw [norm_sq_expUnitary_sub_one hx.le]
    calc
      2 * (1 - Real.cos ‖x‖) < 2 * (1

中文:
引理 argSelfAdjoint_expUnitary
  条件: {x : selfAdjoint A} (hx : ‖x‖ < π)
  证明: by
  nontriviality A
  ext
  have : spectrum Complex (expUnitary x : A) subseteq slitPlane := by
    rw [spectrum_subset_slitPlane_iff_norm_lt_two (expUnitary x).2]; rw [← sq_lt_sq₀ (by positivity) (by positivity)]; rw [norm_sq_expUnitary_sub_one hx.le]
    calc
      2 * (1 - Real.cos ‖x‖) < 2 * (1

Depends on / 依赖: CFC.exp_eq_normedSpace_exp, Real.cos, Real.cos_lt_cos_of_nonneg_of_le_pi, argSelfAdjoint_coe, cos_lt_cos_of_nonneg_of_le_pi, expUnitary, expUnitary_coe, exp_eq_normedSpace_exp, hx.le, le_rfl, nontriviality, norm_sq_expUnitary_sub_one, slitPlane, spectrum, spectrum_subset_slitPlane_iff_norm_lt_two, subseteq
-/
lemma argSelfAdjoint_expUnitary {x : selfAdjoint A} (hx : ‖x‖ < π) :
    argSelfAdjoint (expUnitary x) = x := by
  nontriviality A
  ext
  have : spectrum Complex (expUnitary x : A) subseteq slitPlane := by
    rw [spectrum_subset_slitPlane_iff_norm_lt_two (expUnitary x).2]; rw [← sq_lt_sq₀ (by positivity) (by positivity)]; rw [norm_sq_expUnitary_sub_one hx.le]
    calc
      2 * (1 - Real.cos ‖x‖) < 2 * (1 - Real.cos π) := by
        gcongr
        exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) le_rfl hx
      _ = 2 ^ 2 := by norm_num
  simp only [argSelfAdjoint_coe, expUnitary_coe]
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := Complex)]; rw [← cfc_comp_smul ..]; rw [← cfc_comp' (hg := ?hg)]
  case hg =>
refine continuous_ofReal.comp_continuousOn continuousOn_arg.mono ?_
    rwa [expUnitary_coe, ← CFC.exp_eq_normedSpace_exp (𝕜 := Complex), ← cfc_comp_smul ..,
      cfc_map_spectrum ..] at this
  conv_rhs => rw [← cfc_id' Complex (x : A)]
  refine cfc_congr fun y hy => ?_
  rw [← x.2.spectrumRestricts.algebraMap_image] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  simp only [coe_algebraMap, smul_eq_mul, mul_comm I, ← exp_eq_exp_Complex, ofReal_inj]
.trans_lt hx replace hy : ‖y‖ < π := spectrum.norm_le_norm_of_mem hy
  simp only [Real.norm_eq_abs, abs_lt] at hy
  rw [← Circle.coe_exp]; rw [Circle.arg_exp hy.1 hy.2.le]

/--
lemma `expUnitary_argSelfAdjoint` / 引理 `expUnitary_argSelfAdjoint`

English:
lemma expUnitary_argSelfAdjoint
  given: {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2)
  proof: by
  ext
  have : ContinuousOn arg (spectrum Complex (u : A)) :=
continuousOn_arg.mono (spectrum_subset_slitPlane_iff_norm_lt_two u.2).mpr hu
  rw [expUnitary_coe]; rw [argSelfAdjoint_coe]; rw [← CFC.exp_eq_normedSpace_exp (𝕜 := Complex)]; rw [← cfc_comp_smul ..]; rw [← cfc_comp' ..]
  conv_rhs => r

中文:
引理 expUnitary_argSelfAdjoint
  条件: {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2)
  证明: by
  ext
  have : ContinuousOn arg (spectrum Complex (u : A)) :=
continuousOn_arg.mono (spectrum_subset_slitPlane_iff_norm_lt_two u.2).mpr hu
  rw [expUnitary_coe]; rw [argSelfAdjoint_coe]; rw [← CFC.exp_eq_normedSpace_exp (𝕜 := Complex)]; rw [← cfc_comp_smul ..]; rw [← cfc_comp' ..]
  conv_rhs => r

Depends on / 依赖: CFC.exp_eq_normedSpace_exp, Complex.ext, ContinuousOn, argSelfAdjoint_coe, cfc_comp, cfc_comp_smul, cfc_congr, cfc_id, continuousOn_arg, continuousOn_arg.mono, conv_rhs, expUnitary_coe, exp_eq_normedSpace_exp, log_re, norm_eq_one_of_uni, norm_eq_one_of_unitary, spectrum, spectrum.norm_eq_one_of_uni, spectrum.norm_eq_one_of_unitary, spectrum_subset_slitPlane_iff_norm_lt_two
-/
lemma expUnitary_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    expUnitary (argSelfAdjoint u) = u := by
  ext
  have : ContinuousOn arg (spectrum Complex (u : A)) :=
continuousOn_arg.mono (spectrum_subset_slitPlane_iff_norm_lt_two u.2).mpr hu
  rw [expUnitary_coe]; rw [argSelfAdjoint_coe]; rw [← CFC.exp_eq_normedSpace_exp (𝕜 := Complex)]; rw [← cfc_comp_smul ..]; rw [← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' Complex (u : A)]
  refine cfc_congr fun y hy => ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have : I * y.arg = log y :=
    Complex.ext (by simp [log_re, spectrum.norm_eq_one_of_unitary u.2 hy]) (by simp [log_im])
  simpa [← exp_eq_exp_Complex, this] using exp_log (by aesop)

/--
lemma `Unitary.norm_argSelfAdjoint_le_pi` / 引理 `Unitary.norm_argSelfAdjoint_le_pi`

English:
lemma Unitary.norm_argSelfAdjoint_le_pi
  given: (u : unitary A)
  proof: norm_cfc_le (by positivity) fun y hy => by simpa using abs_arg_le_pi y

中文:
引理 酉.norm_argSelfAdjoint_le_pi
  条件: (u : unitary A)
  证明: norm_cfc_le (by positivity) fun y hy => by simpa using abs_arg_le_pi y

Depends on / 依赖: abs_arg_le_pi, norm_cfc_le
-/
lemma Unitary.norm_argSelfAdjoint_le_pi (u : unitary A) :
    ‖argSelfAdjoint u‖ <= π :=
  norm_cfc_le (by positivity) fun y hy => by simpa using abs_arg_le_pi y

/--
lemma `Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint` / 引理 `Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint`

English:
lemma Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint
  given: {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2)
  proof: by
  conv_rhs => rw [← expUnitary_argSelfAdjoint hu]
exact Eq.symm norm_sq_expUnitary_sub_one norm_argSelfAdjoint_le_pi u

中文:
引理 酉.two_mul_one_sub_cos_norm_argSelfAdjoint
  条件: {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2)
  证明: by
  conv_rhs => rw [← expUnitary_argSelfAdjoint hu]
exact Eq.symm norm_sq_expUnitary_sub_one norm_argSelfAdjoint_le_pi u

Depends on / 依赖: Eq.symm, conv_rhs, expUnitary_argSelfAdjoint, norm_argSelfAdjoint_le_pi, norm_sq_expUnitary_sub_one
-/
lemma Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    2 * (1 - Real.cos ‖argSelfAdjoint u‖) = ‖(u - 1 : A)‖ ^ 2 := by
  conv_rhs => rw [← expUnitary_argSelfAdjoint hu]
exact Eq.symm norm_sq_expUnitary_sub_one norm_argSelfAdjoint_le_pi u

/--
lemma `Unitary.norm_argSelfAdjoint` / 引理 `Unitary.norm_argSelfAdjoint`

English:
lemma Unitary.norm_argSelfAdjoint
  given: {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2)
  proof: by
.symm refine Real.arccos_eq_of_eq_cos (by positivity) (norm_argSelfAdjoint_le_pi u) ?_
  linarith [two_mul_one_sub_cos_norm_argSelfAdjoint hu]

中文:
引理 酉.norm_argSelfAdjoint
  条件: {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2)
  证明: by
.symm refine Real.arccos_eq_of_eq_cos (by positivity) (norm_argSelfAdjoint_le_pi u) ?_
  linarith [two_mul_one_sub_cos_norm_argSelfAdjoint hu]

Depends on / 依赖: Real.arccos_eq_of_eq_cos, arccos_eq_of_eq_cos, norm_argSelfAdjoint_le_pi, two_mul_one_sub_cos_norm_argSelfAdjoint
-/
lemma Unitary.norm_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    ‖argSelfAdjoint u‖ = Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2) := by
.symm refine Real.arccos_eq_of_eq_cos (by positivity) (norm_argSelfAdjoint_le_pi u) ?_
  linarith [two_mul_one_sub_cos_norm_argSelfAdjoint hu]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le` / 引理 `Unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le`

English:
lemma Unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le
  statement: (u : unitary A)
  proof: by
  have key : ‖t • argSelfAdjoint u‖ <= ‖argSelfAdjoint u‖ := by
    rw [← one_mul ‖argSelfAdjoint u‖]
    simp_rw [AddSubgroupClass.coe_norm, val_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    gcongr
    exact ht.2
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  rw [norm_sq_expUn

中文:
引理 酉.norm_expUnitary_smul_argSelfAdjoint_sub_one_le
  结论: (u : unitary A)
  证明: by
  have key : ‖t • argSelfAdjoint u‖ <= ‖argSelfAdjoint u‖ := by
    rw [← one_mul ‖argSelfAdjoint u‖]
    simp_rw [AddSubgroupClass.coe_norm, val_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    gcongr
    exact ht.2
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  rw [norm_sq_expUn

Depends on / 依赖: AddSubgroupClass, AddSubgroupClass.coe_norm, Real.cos, Real.cos_le_cos_of_nonneg_of_le_pi, Real.norm_eq_abs, abs_of_nonneg, argSelfAdjoint, coe_norm, cos_le_cos_of_nonneg_of_le_pi, key.trans, norm_argSelfAdjoint_le_pi, norm_eq_abs, norm_smul, norm_sq_expUnitary_sub_one, one_mul, simp_rw, two_mul_one, val_smul
-/
lemma Unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le (u : unitary A)
    {t : Real} (ht : t in Set.Icc 0 1) (hu : ‖(u - 1 : A)‖ < 2) :
    ‖(expUnitary (t • argSelfAdjoint u) - 1 : A)‖ <= ‖(u - 1 : A)‖ := by
  have key : ‖t • argSelfAdjoint u‖ <= ‖argSelfAdjoint u‖ := by
    rw [← one_mul ‖argSelfAdjoint u‖]
    simp_rw [AddSubgroupClass.coe_norm, val_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    gcongr
    exact ht.2
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  rw [norm_sq_expUnitary_sub_one (key.trans <| norm_argSelfAdjoint_le_pi u)]
  trans 2 * (1 - Real.cos ‖argSelfAdjoint u‖)
  · gcongr
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (norm_argSelfAdjoint_le_pi u) key
  · exact (two_mul_one_sub_cos_norm_argSelfAdjoint hu).le

@[fun_prop]
/--
lemma `Unitary.continuousOn_argSelfAdjoint` / 引理 `Unitary.continuousOn_argSelfAdjoint`

English:
lemma Unitary.continuousOn_argSelfAdjoint
  proof: by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  simp only [Function.comp_def, argSelfAdjoint_coe]
  rw [isOpen_ball.continuousOn_iff]
  intro u (hu : dist u 1 < 2)
  obtain ⟨ε, huε, hε2⟩ := exists_between (sq_lt_sq₀ (by positivity) (by positivity) |>.mpr hu)
  have hε : 0 < ε := lt_of_le

中文:
引理 酉.continuousOn_argSelfAdjoint
  证明: by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  simp only [Function.comp_def, argSelfAdjoint_coe]
  rw [isOpen_ball.continuousOn_iff]
  intro u (hu : dist u 1 < 2)
  obtain ⟨ε, huε, hε2⟩ := exists_between (sq_lt_sq₀ (by positivity) (by positivity) |>.mpr hu)
  have hε : 0 < ε := lt_of_le

Depends on / 依赖: ContinuousOn, ContinuousOn.continuousAt, ContinuousOn.image_comp_continuous, Function, Function.comp_def, IsInducing, Real.lt_sqrt_of_sq_lt, Topology, Topology.IsInducing.subtypeVal.continuousOn_iff, argSelfAdjoint_coe, closedBall_mem_nhds_of_mem, comp_def, continuousAt, continuousOn_iff, continuous_subtyp, exists_between, image_comp_continuous, isOpen_ball, isOpen_ball.continuousOn_iff, lt_of_le_of_lt
-/
lemma Unitary.continuousOn_argSelfAdjoint :
    ContinuousOn (argSelfAdjoint : unitary A -> selfAdjoint A) (ball (1 : unitary A) 2) := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  simp only [Function.comp_def, argSelfAdjoint_coe]
  rw [isOpen_ball.continuousOn_iff]
  intro u (hu : dist u 1 < 2)
  obtain ⟨ε, huε, hε2⟩ := exists_between (sq_lt_sq₀ (by positivity) (by positivity) |>.mpr hu)
  have hε : 0 < ε := lt_of_le_of_lt (by positivity) huε
  have huε' : dist u 1 < √ε := Real.lt_sqrt_of_sq_lt huε
  apply ContinuousOn.continuousAt ?_ (closedBall_mem_nhds_of_mem huε')
  apply ContinuousOn.image_comp_continuous ?_ continuous_subtype_val
.mono apply continuousOn_cfc A (s := sphere 0 1 inter {z | 2 * (1 - z.re) <= ε}) ?_ _ ?_
  · rintro - ⟨v, hv, rfl⟩
    simp only [Set.subset_inter_iff, Set.mem_ofPred_eq]
    refine ⟨inferInstance, spectrum_subset_circle v, ?_⟩
    intro z hz
    simp only [Set.mem_ofPred_eq]
    trans ‖(v - 1 : A)‖ ^ 2
    · exact two_mul_one_sub_le_norm_sub_one_sq v.2 hz
.mp ?_ · refine Real.le_sqrt (by positivity) (by positivity)
      simpa [Subtype.dist_eq, dist_eq_norm] using hv
.inter_right isClosed_le (by fun_prop) (by fun_prop) · exact isCompact_sphere 0 1
· refine continuous_ofReal.comp_continuousOn continuousOn_arg.mono ?_
.mpr apply subset_slitPlane_iff_of_subset_sphere Set.inter_subset_left
    norm_num at hε2 ⊢
    exact hε2

set_option backward.isDefEq.respectTransparency false in
/-- the maps `unitary.argSelfAdjoint` and `selfAdjoint.expUnitary` form a partial
homeomorphism between `ball (1 : unitary A) 2` and `ball (0 : selfAdjoint A) π`. -/
@[simps]
/--
Definition of `Unitary.openPartialHomeomorph` / `Unitary.openPartialHomeomorph` 的定义

English:
definition Unitary.openPartialHomeomorph
  signature: :
  body: argSelfAdjoint
  invFun := expUnitary
  source := ball 1 2
  target := ball 0 π
  map_source' u hu := by
    simp only [mem_ball, Subtype.dist_eq, OneMemClass.coe_one, dist_eq_norm, sub_zero] at hu ⊢
    rw [norm_argSelfAdjoint hu]
    calc
      Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2) < Real.arccos

中文:
定义 酉.openPartialHomeomorph
  签名: :
  定义体: argSelfAdjoint
  invFun := expUnitary
  source := ball 1 2
  target := ball 0 π
  map_source' u hu := by
    simp only [mem_ball, Subtype.dist_eq, OneMemClass.coe_one, dist_eq_norm, sub_zero] at hu ⊢
    rw [norm_argSelfAdjoint hu]
    calc
      Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2) < Real.arccos

Depends on / 依赖: argSelfAdjoint
-/
noncomputable def Unitary.openPartialHomeomorph :
    OpenPartialHomeomorph (unitary A) (selfAdjoint A) where
  toFun := argSelfAdjoint
  invFun := expUnitary
  source := ball 1 2
  target := ball 0 π
  map_source' u hu := by
    simp only [mem_ball, Subtype.dist_eq, OneMemClass.coe_one, dist_eq_norm, sub_zero] at hu ⊢
    rw [norm_argSelfAdjoint hu]
    calc
      Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2) < Real.arccos (1 - 2 ^ 2 / 2) := by
        apply Real.arccos_lt_arccos (by norm_num) (by gcongr)
        linarith [(by positivity : 0 <= ‖(u - 1 : A)‖ ^ 2 / 2)]
      _ = π := by norm_num
  map_target' x hx := by
    simp only [mem_ball, Subtype.dist_eq, OneMemClass.coe_one, dist_eq_norm, sub_zero] at hx ⊢
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]; rw [norm_sq_expUnitary_sub_one hx.le]
    have : -1 < Real.cos ‖(x : A)‖ :=
      Real.cos_pi ▸ Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) le_rfl hx
    simp only [AddSubgroupClass.coe_norm, mul_sub, mul_one, sq, gt_iff_lt]
    linarith
left_inv' u hu := expUnitary_argSelfAdjoint by
    simpa [Subtype.dist_eq, dist_eq_norm] using hu
right_inv' x hx := argSelfAdjoint_expUnitary by simpa using hx
  open_source := isOpen_ball
  open_target := isOpen_ball
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := by fun_prop

/--
lemma `Unitary.norm_sub_eq` / 引理 `Unitary.norm_sub_eq`

English:
lemma Unitary.norm_sub_eq
  given: (u v : unitary A)
  proof: calc
  ‖(u - v : A)‖ = ‖(u * star v - 1 : A) * v‖ := by simp [sub_mul, mul_assoc]
  _ = ‖((u * star v : unitary A) - 1 : A)‖ := by simp

中文:
引理 酉.norm_sub_eq
  条件: (u v : unitary A)
  证明: calc
  ‖(u - v : A)‖ = ‖(u * star v - 1 : A) * v‖ := by simp [sub_mul, mul_assoc]
  _ = ‖((u * star v : unitary A) - 1 : A)‖ := by simp
-/
lemma Unitary.norm_sub_eq (u v : unitary A) :
    ‖(u - v : A)‖ = ‖((u * star v : unitary A) - 1 : A)‖ := calc
  ‖(u - v : A)‖ = ‖(u * star v - 1 : A) * v‖ := by simp [sub_mul, mul_assoc]
  _ = ‖((u * star v : unitary A) - 1 : A)‖ := by simp

/--
lemma `Unitary.expUnitary_eq_mul_inv` / 引理 `Unitary.expUnitary_eq_mul_inv`

English:
lemma Unitary.expUnitary_eq_mul_inv
  given: (u v : unitary A) (huv : ‖(u - v : A)‖ < 2)
  proof: expUnitary_argSelfAdjoint norm_sub_eq u v ▸ huv

中文:
引理 酉.expUnitary_eq_mul_inv
  条件: (u v : unitary A) (huv : ‖(u - v : A)‖ < 2)
  证明: expUnitary_argSelfAdjoint norm_sub_eq u v ▸ huv

Depends on / 依赖: expUnitary_argSelfAdjoint, norm_sub_eq
-/
lemma Unitary.expUnitary_eq_mul_inv (u v : unitary A) (huv : ‖(u - v : A)‖ < 2) :
    expUnitary (argSelfAdjoint (u * star v)) = u * star v :=
expUnitary_argSelfAdjoint norm_sub_eq u v ▸ huv

/-- For a selfadjoint element `x` in a C⋆-algebra, this is the path from `1` to `expUnitary x`
given by `t ↦ expUnitary (t • x)`. -/
@[simps]
/--
Definition of `selfAdjoint.expUnitaryPathToOne` / `selfAdjoint.expUnitaryPathToOne` 的定义

English:
definition selfAdjoint.expUnitaryPathToOne
  signature: (x : selfAdjoint A)
  body: expUnitary ((t : Real) • x)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]

中文:
定义 selfAdjoint.expUnitaryPathToOne
  签名: (x : selfAdjoint A)
  定义体: expUnitary ((t : Real) • x)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]

Depends on / 依赖: expUnitary
-/
noncomputable def selfAdjoint.expUnitaryPathToOne (x : selfAdjoint A) :
    Path 1 (expUnitary x) where
  toFun t := expUnitary ((t : Real) • x)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]
/--
lemma `selfAdjoint.joined_one_expUnitary` / 引理 `selfAdjoint.joined_one_expUnitary`

English:
lemma selfAdjoint.joined_one_expUnitary
  given: (x : selfAdjoint A)
  proof: ⟨expUnitaryPathToOne x⟩

中文:
引理 selfAdjoint.joined_one_expUnitary
  条件: (x : selfAdjoint A)
  证明: ⟨expUnitaryPathToOne x⟩

Depends on / 依赖: expUnitaryPathToOne
-/
lemma selfAdjoint.joined_one_expUnitary (x : selfAdjoint A) :
    Joined (1 : unitary A) (expUnitary x) :=
  ⟨expUnitaryPathToOne x⟩

/-- The path `t ↦ expUnitary (t • argSelfAdjoint (v * star u)) * u`
from `u : unitary A` to `v` when `‖v - u‖ < 2`. -/
@[simps]
/--
Definition of `Unitary.path` / `Unitary.path` 的定义

English:
definition Unitary.path
  signature: (u v : unitary A) (huv : ‖(v - u : A)‖ < 2)
  body: expUnitary ((t : Real) • argSelfAdjoint (v * star u)) * u
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by simp [expUnitary_eq_mul_inv v u huv, mul_assoc]

中文:
定义 酉.path
  签名: (u v : unitary A) (huv : ‖(v - u : A)‖ < 2)
  定义体: expUnitary ((t : Real) • argSelfAdjoint (v * star u)) * u
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by simp [expUnitary_eq_mul_inv v u huv, mul_assoc]

Depends on / 依赖: argSelfAdjoint, expUnitary
-/
noncomputable def Unitary.path (u v : unitary A) (huv : ‖(v - u : A)‖ < 2) :
    Path u v where
  toFun t := expUnitary ((t : Real) • argSelfAdjoint (v * star u)) * u
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by simp [expUnitary_eq_mul_inv v u huv, mul_assoc]

/--
lemma `Unitary.joined` / 引理 `Unitary.joined`

English:
lemma Unitary.joined
  given: (u v : unitary A) (huv : ‖(v - u : A)‖ < 2)
  proof: ⟨path u v huv⟩

中文:
引理 酉.joined
  条件: (u v : unitary A) (huv : ‖(v - u : A)‖ < 2)
  证明: ⟨path u v huv⟩
-/
lemma Unitary.joined (u v : unitary A) (huv : ‖(v - u : A)‖ < 2) :
    Joined u v :=
  ⟨path u v huv⟩

/--
lemma `Unitary.isPathConnected_ball` / 引理 `Unitary.isPathConnected_ball`

English:
lemma Unitary.isPathConnected_ball
  given: (u : unitary A) (δ : Real) (hδ₀ : 0 < δ) (hδ₂ : δ < 2)
  proof: by
  suffices IsPathConnected (ball (1 : unitary A) δ) by
.image (f := (u * ·)) (by fun_prop) convert! this
    ext v
    rw [← inv_mul_cancel u]
    simp [-inv_mul_cancel, Subtype.dist_eq, dist_eq_norm, ← mul_sub]
  refine ⟨1, by simpa, fun {u} hu => ?_⟩
  have hu : ‖(u - 1 : A)‖ < δ := by simpa [S

中文:
引理 酉.isPathConnected_ball
  条件: (u : unitary A) (δ : 实数) (hδ₀ : 0 < δ) (hδ₂ : δ < 2)
  证明: by
  suffices IsPathConnected (ball (1 : unitary A) δ) by
.image (f := (u * ·)) (by fun_prop) convert! this
    ext v
    rw [← inv_mul_cancel u]
    simp [-inv_mul_cancel, Subtype.dist_eq, dist_eq_norm, ← mul_sub]
  refine ⟨1, by simpa, fun {u} hu => ?_⟩
  have hu : ‖(u - 1 : A)‖ < δ := by simpa [S

Depends on / 依赖: IsPathConnected, Subtype, Subtype.dist_eq, convert, dist_eq, dist_eq_norm, fun_prop, hu.trans, inv_mul_cancel, mul_sub, norm_expUnitary_smul_argSelfAdjoint_sub_one_le, trans_lt, unitary
-/
lemma Unitary.isPathConnected_ball (u : unitary A) (δ : Real) (hδ₀ : 0 < δ) (hδ₂ : δ < 2) :
    IsPathConnected (ball (u : unitary A) δ) := by
  suffices IsPathConnected (ball (1 : unitary A) δ) by
.image (f := (u * ·)) (by fun_prop) convert! this
    ext v
    rw [← inv_mul_cancel u]
    simp [-inv_mul_cancel, Subtype.dist_eq, dist_eq_norm, ← mul_sub]
  refine ⟨1, by simpa, fun {u} hu => ?_⟩
  have hu : ‖(u - 1 : A)‖ < δ := by simpa [Subtype.dist_eq, dist_eq_norm] using hu
  refine ⟨path 1 u (hu.trans hδ₂), fun t => ?_⟩
  simpa [Subtype.dist_eq, dist_eq_norm] using
.trans_lt hu norm_expUnitary_smul_argSelfAdjoint_sub_one_le u t.2 (hu.trans hδ₂)

/--
Instance `Unitary.instLocallyPathConnectedSpace` / 实例 `Unitary.instLocallyPathConnectedSpace`

English:
instance Unitary.instLocallyPathConnectedSpace
  signature: : LocallyPathConnectedSpace (unitary A)
  body: .of_bases (fun _ => nhds_basis_uniformity <| uniformity_basis_dist_lt zero_lt_two) by
    simpa using! isPathConnected_ball

中文:
实例 酉.instLocallyPathConnectedSpace
  签名: : LocallyPathConnected空间 (unitary A)
  定义体: .of_bases (fun _ => nhds_basis_uniformity <| uniformity_basis_dist_lt zero_lt_two) by
    simpa using! isPathConnected_ball

Depends on / 依赖: isPathConnected_ball, nhds_basis_uniformity, of_bases, uniformity_basis_dist_lt, zero_lt_two
-/
instance Unitary.instLocallyPathConnectedSpace : LocallyPathConnectedSpace (unitary A) :=
.of_bases (fun _ => nhds_basis_uniformity <| uniformity_basis_dist_lt zero_lt_two) by
    simpa using! isPathConnected_ball

/--
lemma `Unitary.mem_pathComponentOne_iff` / 引理 `Unitary.mem_pathComponentOne_iff`

English:
lemma Unitary.mem_pathComponentOne_iff
  given: {u : unitary A}
  proof: by
  constructor
  · revert u
    simp_rw [← Set.mem_range, ← Set.subset_def, pathComponent_eq_connectedComponent]
    refine IsClopen.connectedComponent_subset ?_ ⟨[], by simp⟩
    refine .of_thickening_subset_self zero_lt_two ?_
    intro u hu
    rw [mem_thickening_iff] at hu
    obtain ⟨v, ⟨⟨l, 

中文:
引理 酉.mem_pathComponentOne_iff
  条件: {u : unitary A}
  证明: by
  constructor
  · revert u
    simp_rw [← Set.mem_range, ← Set.subset_def, pathComponent_eq_connectedComponent]
    refine IsClopen.connectedComponent_subset ?_ ⟨[], by simp⟩
    refine .of_thickening_subset_self zero_lt_two ?_
    intro u hu
    rw [mem_thickening_iff] at hu
    obtain ⟨v, ⟨⟨l, 

Depends on / 依赖: IsClopen, IsClopen.connectedComponent_subset, Set.mem_range, Set.subset_def, Subtype, Subtype.dist_eq, argSelfAdjoint, connectedComponent_subset, dist_eq, dist_eq_norm, expUnitary, expUnitary_eq_mul_inv, l.map, mem_range, mem_thickening_iff, mul_assoc, of_thickening_subset_self, pathComponent_eq_connectedComponent, revert, simp_rw
-/
lemma Unitary.mem_pathComponentOne_iff {u : unitary A} :
    u in pathComponent 1 ↔ exists l : List (selfAdjoint A), (l.map expUnitary).prod = u := by
  constructor
  · revert u
    simp_rw [← Set.mem_range, ← Set.subset_def, pathComponent_eq_connectedComponent]
    refine IsClopen.connectedComponent_subset ?_ ⟨[], by simp⟩
    refine .of_thickening_subset_self zero_lt_two ?_
    intro u hu
    rw [mem_thickening_iff] at hu
    obtain ⟨v, ⟨⟨l, (hlv : (l.map expUnitary).prod = v)⟩, huv⟩⟩ := hu
    refine ⟨argSelfAdjoint (u * star v) :: l, ?_⟩
    simp [hlv, mul_assoc,
      expUnitary_eq_mul_inv u v (by simpa [Subtype.dist_eq, dist_eq_norm] using! huv)]
  · rintro ⟨l, rfl⟩
    induction l with
    | nil => simp
    | cons x xs ih => simpa using! (joined_one_expUnitary x).mul ih
