/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Polar coordinates

We define polar coordinates, as an open partial homeomorphism in `ℝ^2` between `ℝ^2 - (-∞, 0]` and
`(0, +∞) × (-π, π)`. Its inverse is given by `(r, θ) ↦ (r cos θ, r sin θ)`.

It satisfies the following change of variables formula (see `integral_comp_polarCoord_symm`):
`∫ p in polarCoord.target, p.1 • f (polarCoord.symm p) = ∫ p, f p`

-/

@[expose] public section

noncomputable section Real

open Real Set MeasureTheory

open scoped ENNReal Real Topology

/-- The polar coordinates are an open partial homeomorphism in `ℝ^2`, mapping `(r cos θ, r sin θ)`
to `(r, θ)`. It is a homeomorphism between `ℝ^2 - (-∞, 0]` and `(0, +∞) × (-π, π)`. -/
@[simps]
/--
Definition of `polarCoord` / `polarCoord` 的定义

English:
definition polarCoord
  signature: : OpenPartialHomeomorph (Real × Real) (Real × Real) where
  body: (√(q.1 ^ 2 + q.2 ^ 2), Complex.arg (Complex.equivRealProd.symm q))
  invFun p := (p.1 * cos p.2, p.1 * sin p.2)
  source := {q | 0 < q.1} union {q | q.2 != 0}
  target := Ioi (0 : Real) ×ˢ Ioo (-π) π
  map_target' := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    dsimp at hr hθ
    rcases eq_or_ne θ 0 with (rfl | h'θ)
    · simpa using! hr
    · right
      simp at hr
      simpa only [ne_of_gt hr, Ne, mem_ofPred_eq, mul_eq_zero, false_or,
        sin_eq_zero_iff_of_lt_of_lt hθ.1 hθ.2] using! h'θ
  map_source' := by
    rintro ⟨x, y⟩ hxy
    simp only [prodMk_mem_set_prod_eq, mem_Ioi, sqrt_pos, mem_Ioo, Complex.neg_pi_lt_arg,
      true_and, Complex.arg_lt_pi_iff]
    constructor
    · rcases hxy with hxy | hxy
      · dsimp at hxy; linarith [sq_pos_of_ne_zero hxy.ne', sq_nonneg y]
      · linarith [sq_nonneg x, sq_pos_of_ne_zero hxy]
    · rcases hxy with hxy | hxy
      · exact Or.inl (le_of_lt hxy)
      · exact Or.inr hxy
  right_inv' := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    ext <;> dsimp at hr hθ ⊢
    · conv_rhs => rw [← sqrt_sq (le_of_lt hr), ← one_mul (r ^ 2), ← sin_sq_add_cos_sq θ]
      congr 1
      ring
    · convert! Complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩
      simp only [Complex.equivRealProd_symm_apply, Complex.ofReal_mul, Complex.ofReal_cos,
        Complex.ofReal_sin]
      ring
  left_inv' := by
    rintro ⟨x, y⟩ _
    have A : √(x ^ 2 + y ^ 2) = ‖x + y * Complex.I‖ := by
      rw [Complex.norm_def]; rw [Complex.normSq_add_mul_I]
    simp [A]
  open_target := isOpen_Ioi.prod isOpen_Ioo
  open_source :=
    (isOpen_lt continuous_const continuous_fst).union
      (isOpen_ne_fun continuous_snd continuous_const)
  continuousOn_invFun := by fun_prop
  continuousOn_toFun := by
    refine .prodMk (by fun_prop) ?_
    have A : MapsTo Complex.equivRealProd.symm ({q : Real × Real | 0 < q.1} union {q : Real × Real | q.2 != 0})
        Complex.slitPlane := by
      rintro ⟨x, y⟩ hxy; simpa only using! hxy
    refine ContinuousOn.comp (f := Complex.equivRealProd.symm)
      (g := Complex.arg) (fun z hz => ?_) ?_ A
    · exact (Complex.continuousAt_arg hz).continuousWithinAt
    · exact Complex.equivRealProdCLM.symm.continuous.continuousOn

@[fun_prop]

中文:
定义 polarCoord
  签名: : OpenPartialHomeomorph (实数 × 实数) (实数 × 实数) where
  定义体: (√(q.1 ^ 2 + q.2 ^ 2), Complex.arg (Complex.equivRealProd.symm q))
  invFun p := (p.1 * cos p.2, p.1 * sin p.2)
  source := {q | 0 < q.1} union {q | q.2 != 0}
  target := Ioi (0 : Real) ×ˢ Ioo (-π) π
  map_target' := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    dsimp at hr hθ
    rcases eq_or_ne θ 0 with (rfl | h'θ)
    · simpa using! hr
    · right
      simp at hr
      simpa only [ne_of_gt hr, Ne, mem_ofPred_eq, mul_eq_zero, false_or,
        sin_eq_zero_iff_of_lt_of_lt hθ.1 hθ.2] using! h'θ
  map_source' := by
    rintro ⟨x, y⟩ hxy
    simp only [prodMk_mem_set_prod_eq, mem_Ioi, sqrt_pos, mem_Ioo, Complex.neg_pi_lt_arg,
      true_and, Complex.arg_lt_pi_iff]
    constructor
    · rcases hxy with hxy | hxy
      · dsimp at hxy; linarith [sq_pos_of_ne_zero hxy.ne', sq_nonneg y]
      · linarith [sq_nonneg x, sq_pos_of_ne_zero hxy]
    · rcases hxy with hxy | hxy
      · exact Or.inl (le_of_lt hxy)
      · exact Or.inr hxy
  right_inv' := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    ext <;> dsimp at hr hθ ⊢
    · conv_rhs => rw [← sqrt_sq (le_of_lt hr), ← one_mul (r ^ 2), ← sin_sq_add_cos_sq θ]
      congr 1
      ring
    · convert! Complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩
      simp only [Complex.equivRealProd_symm_apply, Complex.ofReal_mul, Complex.ofReal_cos,
        Complex.ofReal_sin]
      ring
  left_inv' := by
    rintro ⟨x, y⟩ _
    have A : √(x ^ 2 + y ^ 2) = ‖x + y * Complex.I‖ := by
      rw [Complex.norm_def]; rw [Complex.normSq_add_mul_I]
    simp [A]
  open_target := isOpen_Ioi.prod isOpen_Ioo
  open_source :=
    (isOpen_lt continuous_const continuous_fst).union
      (isOpen_ne_fun continuous_snd continuous_const)
  continuousOn_invFun := by fun_prop
  continuousOn_toFun := by
    refine .prodMk (by fun_prop) ?_
    have A : MapsTo Complex.equivRealProd.symm ({q : Real × Real | 0 < q.1} union {q : Real × Real | q.2 != 0})
        Complex.slitPlane := by
      rintro ⟨x, y⟩ hxy; simpa only using! hxy
    refine ContinuousOn.comp (f := Complex.equivRealProd.symm)
      (g := Complex.arg) (fun z hz => ?_) ?_ A
    · exact (Complex.continuousAt_arg hz).continuousWithinAt
    · exact Complex.equivRealProdCLM.symm.continuous.continuousOn

@[fun_prop]

Depends on / 依赖: Complex.arg, Complex.equivRealProd.symm, equivRealProd
-/
def polarCoord : OpenPartialHomeomorph (Real × Real) (Real × Real) where
  toFun q := (√(q.1 ^ 2 + q.2 ^ 2), Complex.arg (Complex.equivRealProd.symm q))
  invFun p := (p.1 * cos p.2, p.1 * sin p.2)
  source := {q | 0 < q.1} union {q | q.2 != 0}
  target := Ioi (0 : Real) ×ˢ Ioo (-π) π
  map_target' := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    dsimp at hr hθ
    rcases eq_or_ne θ 0 with (rfl | h'θ)
    · simpa using! hr
    · right
      simp at hr
      simpa only [ne_of_gt hr, Ne, mem_ofPred_eq, mul_eq_zero, false_or,
        sin_eq_zero_iff_of_lt_of_lt hθ.1 hθ.2] using! h'θ
  map_source' := by
    rintro ⟨x, y⟩ hxy
    simp only [prodMk_mem_set_prod_eq, mem_Ioi, sqrt_pos, mem_Ioo, Complex.neg_pi_lt_arg,
      true_and, Complex.arg_lt_pi_iff]
    constructor
    · rcases hxy with hxy | hxy
      · dsimp at hxy; linarith [sq_pos_of_ne_zero hxy.ne', sq_nonneg y]
      · linarith [sq_nonneg x, sq_pos_of_ne_zero hxy]
    · rcases hxy with hxy | hxy
      · exact Or.inl (le_of_lt hxy)
      · exact Or.inr hxy
  right_inv' := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    ext <;> dsimp at hr hθ ⊢
    · conv_rhs => rw [← sqrt_sq (le_of_lt hr), ← one_mul (r ^ 2), ← sin_sq_add_cos_sq θ]
      congr 1
      ring
    · convert! Complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩
      simp only [Complex.equivRealProd_symm_apply, Complex.ofReal_mul, Complex.ofReal_cos,
        Complex.ofReal_sin]
      ring
  left_inv' := by
    rintro ⟨x, y⟩ _
    have A : √(x ^ 2 + y ^ 2) = ‖x + y * Complex.I‖ := by
      rw [Complex.norm_def]; rw [Complex.normSq_add_mul_I]
    simp [A]
  open_target := isOpen_Ioi.prod isOpen_Ioo
  open_source :=
    (isOpen_lt continuous_const continuous_fst).union
      (isOpen_ne_fun continuous_snd continuous_const)
  continuousOn_invFun := by fun_prop
  continuousOn_toFun := by
    refine .prodMk (by fun_prop) ?_
    have A : MapsTo Complex.equivRealProd.symm ({q : Real × Real | 0 < q.1} union {q : Real × Real | q.2 != 0})
        Complex.slitPlane := by
      rintro ⟨x, y⟩ hxy; simpa only using! hxy
    refine ContinuousOn.comp (f := Complex.equivRealProd.symm)
      (g := Complex.arg) (fun z hz => ?_) ?_ A
    · exact (Complex.continuousAt_arg hz).continuousWithinAt
    · exact Complex.equivRealProdCLM.symm.continuous.continuousOn

@[fun_prop]
/--
theorem `continuous_polarCoord_symm` / 定理 `continuous_polarCoord_symm`

English:
theorem continuous_polarCoord_symm
  proof: .prodMk (by fun_prop) (by fun_prop)

中文:
定理 continuous_polarCoord_symm
  证明: .prodMk (by fun_prop) (by fun_prop)

Depends on / 依赖: fun_prop, prodMk
-/
theorem continuous_polarCoord_symm :
    Continuous polarCoord.symm :=
  .prodMk (by fun_prop) (by fun_prop)

/--
Definition of `fderivPolarCoordSymm` / `fderivPolarCoordSymm` 的定义

English:
definition fderivPolarCoordSymm
  signature: (p : Real × Real)
  body: (Matrix.toLin (.finTwoProd Real) (.finTwoProd Real)
    !![cos p.2, -p.1 * sin p.2; sin p.2, p.1 * cos p.2]).toContinuousLinearMap

中文:
定义 fderivPolarCoordSymm
  签名: (p : 实数 × 实数)
  定义体: (Matrix.toLin (.finTwoProd Real) (.finTwoProd Real)
    !![cos p.2, -p.1 * sin p.2; sin p.2, p.1 * cos p.2]).toContinuousLinearMap

Depends on / 依赖: Matrix, Matrix.toLin, finTwoProd, toContinuousLinearMap
-/
def fderivPolarCoordSymm (p : Real × Real) : Real × Real ->L[Real] Real × Real :=
  (Matrix.toLin (.finTwoProd Real) (.finTwoProd Real)
    !![cos p.2, -p.1 * sin p.2; sin p.2, p.1 * cos p.2]).toContinuousLinearMap

/--
theorem `hasFDerivAt_polarCoord_symm` / 定理 `hasFDerivAt_polarCoord_symm`

English:
theorem hasFDerivAt_polarCoord_symm
  given: (p : Real × Real)
  proof: by
  unfold fderivPolarCoordSymm
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert!
    HasFDerivAt.prodMk (𝕜 := Real)
      (hasFDerivAt_fst.mul ((hasDerivAt_cos p.2).comp_hasFDerivAt p hasFDerivAt_snd))
      (hasFDerivAt_fst.mul ((hasDerivAt_sin p.2).comp_hasFDerivAt p hasFDerivAt_snd)) using
    2 <;>
  simp [smul_smul, add_comm, neg_mul, smul_neg, neg_smul _ (ContinuousLinearMap.snd Real Real Real)]

中文:
定理 hasFDerivAt_polarCoord_symm
  条件: (p : 实数 × 实数)
  证明: by
  unfold fderivPolarCoordSymm
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert!
    HasFDerivAt.prodMk (𝕜 := Real)
      (hasFDerivAt_fst.mul ((hasDerivAt_cos p.2).comp_hasFDerivAt p hasFDerivAt_snd))
      (hasFDerivAt_fst.mul ((hasDerivAt_sin p.2).comp_hasFDerivAt p hasFDerivAt_snd)) using
    2 <;>
  simp [smul_smul, add_comm, neg_mul, smul_neg, neg_smul _ (ContinuousLinearMap.snd Real Real Real)]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.snd, HasFDerivAt, HasFDerivAt.prodMk, Matrix, Matrix.toLin_finTwoProd_toContinuousLinearMap, add_comm, comp_hasFDerivAt, convert, fderivPolarCoordSymm, hasDerivAt_cos, hasDerivAt_sin, hasFDerivAt_fst, hasFDerivAt_fst.mul, hasFDerivAt_snd, neg_mul, neg_smul, prodMk, smul_neg, smul_smul
-/
theorem hasFDerivAt_polarCoord_symm (p : Real × Real) :
    HasFDerivAt polarCoord.symm (fderivPolarCoordSymm p) p := by
  unfold fderivPolarCoordSymm
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert!
    HasFDerivAt.prodMk (𝕜 := Real)
      (hasFDerivAt_fst.mul ((hasDerivAt_cos p.2).comp_hasFDerivAt p hasFDerivAt_snd))
      (hasFDerivAt_fst.mul ((hasDerivAt_sin p.2).comp_hasFDerivAt p hasFDerivAt_snd)) using
    2 <;>
  simp [smul_smul, add_comm, neg_mul, smul_neg, neg_smul _ (ContinuousLinearMap.snd Real Real Real)]

/--
theorem `det_fderivPolarCoordSymm` / 定理 `det_fderivPolarCoordSymm`

English:
theorem det_fderivPolarCoordSymm
  given: (p : Real × Real)
  proof: by
  conv_rhs => rw [← one_mul p.1, ← cos_sq_add_sin_sq p.2]
  unfold fderivPolarCoordSymm
  simp only [neg_mul, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of, sub_neg_eq_add]
  ring

中文:
定理 det_fderivPolarCoordSymm
  条件: (p : 实数 × 实数)
  证明: by
  conv_rhs => rw [← one_mul p.1, ← cos_sq_add_sin_sq p.2]
  unfold fderivPolarCoordSymm
  simp only [neg_mul, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of, sub_neg_eq_add]
  ring

Depends on / 依赖: LinearMap, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin, Matrix, Matrix.det_fin_two_of, conv_rhs, cos_sq_add_sin_sq, det_fin_two_of, det_toContinuousLinearMap, det_toLin, fderivPolarCoordSymm, neg_mul, one_mul, sub_neg_eq_add
-/
theorem det_fderivPolarCoordSymm (p : Real × Real) :
    (fderivPolarCoordSymm p).det = p.1 := by
  conv_rhs => rw [← one_mul p.1, ← cos_sq_add_sin_sq p.2]
  unfold fderivPolarCoordSymm
  simp only [neg_mul, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of, sub_neg_eq_add]
  ring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Measure.IsAddHaarMeasure volume (G := Real × Real)
  body: Measure.prod.instIsAddHaarMeasure _ _

中文:
实例 :
  签名: 测度.是加法Haar测度 volume (G := 实数 × 实数)
  定义体: Measure.prod.instIsAddHaarMeasure _ _
-/
instance : Measure.IsAddHaarMeasure volume (G := Real × Real) :=
  Measure.prod.instIsAddHaarMeasure _ _

/--
theorem `polarCoord_source_ae_eq_univ` / 定理 `polarCoord_source_ae_eq_univ`

English:
theorem polarCoord_source_ae_eq_univ
  statement: polarCoord.source =ᵐ[volume] univ
  proof: by
  have A : polarCoord.sourceᶜ subseteq LinearMap.ker (LinearMap.snd Real Real Real) := by
    intro x hx
    simp only [polarCoord_source, compl_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_lt,
      Classical.not_not] at hx
    exact hx.2
  have B : volume (LinearMap.ker (LinearMap.snd Real Real Real) : Set (Real × Real)) = 0 := by
    apply Measure.addHaar_submodule
    rw [Ne]; rw [LinearMap.ker_eq_top]
    intro h
    have : (LinearMap.snd Real Real Real) (0, 1) = (0 : Real × Real ->ₗ[Real] Real) (0, 1) := by rw [h]
    simp at this
  simp only [ae_eq_univ]
  exact le_antisymm ((measure_mono A).trans (le_of_eq B)) bot_le

中文:
定理 polarCoord_source_ae_eq_univ
  结论: polarCoord.source =ᵐ[volume] univ
  证明: by
  have A : polarCoord.sourceᶜ subseteq LinearMap.ker (LinearMap.snd Real Real Real) := by
    intro x hx
    simp only [polarCoord_source, compl_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_lt,
      Classical.not_not] at hx
    exact hx.2
  have B : volume (LinearMap.ker (LinearMap.snd Real Real Real) : Set (Real × Real)) = 0 := by
    apply Measure.addHaar_submodule
    rw [Ne]; rw [LinearMap.ker_eq_top]
    intro h
    have : (LinearMap.snd Real Real Real) (0, 1) = (0 : Real × Real ->ₗ[Real] Real) (0, 1) := by rw [h]
    simp at this
  simp only [ae_eq_univ]
  exact le_antisymm ((measure_mono A).trans (le_of_eq B)) bot_le

Depends on / 依赖: Classical, Classical.not_not, LinearMap, LinearMap.ker, LinearMap.ker_eq_top, LinearMap.snd, Measure, Measure.addHaar_submodule, addHaar_submodule, compl_union, ker_eq_top, mem_compl_iff, mem_inter_iff, mem_ofPred_eq, not_lt, not_not, polarCoord, polarCoord.source, polarCoord_source, subseteq
-/
theorem polarCoord_source_ae_eq_univ : polarCoord.source =ᵐ[volume] univ := by
  have A : polarCoord.sourceᶜ subseteq LinearMap.ker (LinearMap.snd Real Real Real) := by
    intro x hx
    simp only [polarCoord_source, compl_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_lt,
      Classical.not_not] at hx
    exact hx.2
  have B : volume (LinearMap.ker (LinearMap.snd Real Real Real) : Set (Real × Real)) = 0 := by
    apply Measure.addHaar_submodule
    rw [Ne]; rw [LinearMap.ker_eq_top]
    intro h
    have : (LinearMap.snd Real Real Real) (0, 1) = (0 : Real × Real ->ₗ[Real] Real) (0, 1) := by rw [h]
    simp at this
  simp only [ae_eq_univ]
  exact le_antisymm ((measure_mono A).trans (le_of_eq B)) bot_le

/--
theorem `integral_comp_polarCoord_symm` / 定理 `integral_comp_polarCoord_symm`

English:
theorem integral_comp_polarCoord_symm
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  symm
  calc
    ∫ p, f p = ∫ p in polarCoord.source, f p := by
      rw [← setIntegral_univ]
      apply setIntegral_congr_set
      exact polarCoord_source_ae_eq_univ.symm
    _ = ∫ p in polarCoord.target, |p.1| • f (polarCoord.symm p) := by
      rw [← OpenPartialHomeomorph.symm_target]; rw [integral_target_eq_integral_abs_det_fderiv_smul volume
      (fun p _ => hasFDerivAt_polarCoord_symm p)]; rw [OpenPartialHomeomorph.symm_source]
      simp_rw [det_fderivPolarCoordSymm]
    _ = ∫ p in polarCoord.target, p.1 • f (polarCoord.symm p) := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet fun x hx => ?_
      rw [abs_of_pos hx.1]

中文:
定理 integral_comp_polarCoord_symm
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  symm
  calc
    ∫ p, f p = ∫ p in polarCoord.source, f p := by
      rw [← setIntegral_univ]
      apply setIntegral_congr_set
      exact polarCoord_source_ae_eq_univ.symm
    _ = ∫ p in polarCoord.target, |p.1| • f (polarCoord.symm p) := by
      rw [← OpenPartialHomeomorph.symm_target]; rw [integral_target_eq_integral_abs_det_fderiv_smul volume
      (fun p _ => hasFDerivAt_polarCoord_symm p)]; rw [OpenPartialHomeomorph.symm_source]
      simp_rw [det_fderivPolarCoordSymm]
    _ = ∫ p in polarCoord.target, p.1 • f (polarCoord.symm p) := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet fun x hx => ?_
      rw [abs_of_pos hx.1]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.symm_target, det_fderivPolarCoordSymm, hasFDerivAt_polarCoord_symm, integral_target_eq_integral_abs_det_fderiv_smul, polarCoord, polarCoord.source, polarCoord.symm, polarCoord.target, polarCoord_source_ae_eq_univ, polarCoord_source_ae_eq_univ.symm, setIntegral_congr_set, setIntegral_univ, simp_rw, source, symm_source, symm_target, target, volume
-/
theorem integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f : Real × Real -> E) :
    (∫ p in polarCoord.target, p.1 • f (polarCoord.symm p)) = ∫ p, f p := by
  symm
  calc
    ∫ p, f p = ∫ p in polarCoord.source, f p := by
      rw [← setIntegral_univ]
      apply setIntegral_congr_set
      exact polarCoord_source_ae_eq_univ.symm
    _ = ∫ p in polarCoord.target, |p.1| • f (polarCoord.symm p) := by
      rw [← OpenPartialHomeomorph.symm_target]; rw [integral_target_eq_integral_abs_det_fderiv_smul volume
      (fun p _ => hasFDerivAt_polarCoord_symm p)]; rw [OpenPartialHomeomorph.symm_source]
      simp_rw [det_fderivPolarCoordSymm]
    _ = ∫ p in polarCoord.target, p.1 • f (polarCoord.symm p) := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet fun x hx => ?_
      rw [abs_of_pos hx.1]

/--
theorem `lintegral_comp_polarCoord_symm` / 定理 `lintegral_comp_polarCoord_symm`

English:
theorem lintegral_comp_polarCoord_symm
  given: (f : Real × Real -> Real>=0∞)
  proof: by
  symm
  calc
    _ = ∫⁻ p in polarCoord.symm '' polarCoord.target, f p := by
      rw [← setLIntegral_univ]; rw [setLIntegral_congr polarCoord_source_ae_eq_univ.symm]; rw [polarCoord.symm_image_target_eq_source]
    _ = ∫⁻ (p : Real × Real) in polarCoord.target, ENNReal.ofReal |p.1| • f (polarCoord.symm p) := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume _
        (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)]
      · simp_rw [det_fderivPolarCoordSymm]; rfl
      exacts [polarCoord.symm.injOn, measurableSet_Ioi.prod measurableSet_Ioo]
    _ = ∫⁻ (p : Real × Real) in polarCoord.target, ENNReal.ofReal p.1 • f (polarCoord.symm p) := by
      refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun x hx => ?_)
      rw [abs_of_pos hx.1]

中文:
定理 lintegral_comp_polarCoord_symm
  条件: (f : 实数 × 实数 -> 实数>=0∞)
  证明: by
  symm
  calc
    _ = ∫⁻ p in polarCoord.symm '' polarCoord.target, f p := by
      rw [← setLIntegral_univ]; rw [setLIntegral_congr polarCoord_source_ae_eq_univ.symm]; rw [polarCoord.symm_image_target_eq_source]
    _ = ∫⁻ (p : Real × Real) in polarCoord.target, ENNReal.ofReal |p.1| • f (polarCoord.symm p) := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume _
        (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)]
      · simp_rw [det_fderivPolarCoordSymm]; rfl
      exacts [polarCoord.symm.injOn, measurableSet_Ioi.prod measurableSet_Ioo]
    _ = ∫⁻ (p : Real × Real) in polarCoord.target, ENNReal.ofReal p.1 • f (polarCoord.symm p) := by
      refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun x hx => ?_)
      rw [abs_of_pos hx.1]

Depends on / 依赖: ENNReal, ENNReal.ofReal, det_fderivPolarCoordSymm, exacts, hasFDerivAt_polarCoord_symm, hasFDerivWithinAt, lintegral_image_eq_lintegral_abs_det_fderiv_mul, ofReal, polarCoord, polarCoord.symm, polarCoord.symm.injOn, polarCoord.symm_image_target_eq_source, polarCoord.target, polarCoord_source_ae_eq_univ, polarCoord_source_ae_eq_univ.symm, setLIntegral_congr, setLIntegral_univ, simp_rw, symm_image_target_eq_source, target
-/
theorem lintegral_comp_polarCoord_symm (f : Real × Real -> Real>=0∞) :
    ∫⁻ (p : Real × Real) in polarCoord.target, ENNReal.ofReal p.1 • f (polarCoord.symm p) =
      ∫⁻ (p : Real × Real), f p := by
  symm
  calc
    _ = ∫⁻ p in polarCoord.symm '' polarCoord.target, f p := by
      rw [← setLIntegral_univ]; rw [setLIntegral_congr polarCoord_source_ae_eq_univ.symm]; rw [polarCoord.symm_image_target_eq_source]
    _ = ∫⁻ (p : Real × Real) in polarCoord.target, ENNReal.ofReal |p.1| • f (polarCoord.symm p) := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume _
        (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)]
      · simp_rw [det_fderivPolarCoordSymm]; rfl
      exacts [polarCoord.symm.injOn, measurableSet_Ioi.prod measurableSet_Ioo]
    _ = ∫⁻ (p : Real × Real) in polarCoord.target, ENNReal.ofReal p.1 • f (polarCoord.symm p) := by
      refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun x hx => ?_)
      rw [abs_of_pos hx.1]

end Real

noncomputable section Complex

namespace Complex

open scoped Real ENNReal

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def polarCoord
  body: equivRealProdCLM.toHomeomorph.transOpenPartialHomeomorph polarCoord

中文:
定义 noncomputable
  签名: def polarCoord
  定义体: equivRealProdCLM.toHomeomorph.transOpenPartialHomeomorph polarCoord
-/
protected noncomputable def polarCoord : OpenPartialHomeomorph Complex (Real × Real) :=
  equivRealProdCLM.toHomeomorph.transOpenPartialHomeomorph polarCoord

/--
theorem `polarCoord_apply` / 定理 `polarCoord_apply`

English:
theorem polarCoord_apply
  given: (a : Complex)
  proof: by
  simp_rw [Complex.norm_def, Complex.normSq_apply, ← pow_two]
  rfl

中文:
定理 polarCoord_apply
  条件: (a : 复形)
  证明: by
  simp_rw [Complex.norm_def, Complex.normSq_apply, ← pow_two]
  rfl

Depends on / 依赖: F.mapId, inv.toNatTrans.naturality, naturality, toNatTrans
-/
protected theorem polarCoord_apply (a : Complex) :
    Complex.polarCoord a = (‖a‖, Complex.arg a) := by
  simp_rw [Complex.norm_def, Complex.normSq_apply, ← pow_two]
  rfl

/--
theorem `polarCoord_source` / 定理 `polarCoord_source`

English:
theorem polarCoord_source
  statement: Complex.polarCoord.source = slitPlane
  proof: rfl

中文:
定理 polarCoord_source
  结论: 复形.polarCoord.source = slitPlane
  证明: rfl
-/
protected theorem polarCoord_source : Complex.polarCoord.source = slitPlane := rfl

/--
theorem `polarCoord_target` / 定理 `polarCoord_target`

English:
theorem polarCoord_target
  proof: rfl

@[simp]

中文:
定理 polarCoord_target
  证明: rfl

@[simp]

Depends on / 依赖: F.mapComp, inv.toNatTrans.naturality, mapComp, naturality, toNatTrans
-/
protected theorem polarCoord_target :
    Complex.polarCoord.target = Set.Ioi (0 : Real) ×ˢ Set.Ioo (-π) π := rfl

@[simp]
/--
theorem `polarCoord_symm_apply` / 定理 `polarCoord_symm_apply`

English:
theorem polarCoord_symm_apply
  given: (p : Real × Real)
  proof: by
  simp [Complex.polarCoord, equivRealProdCLM_symm_apply, mul_add, mul_assoc]

中文:
定理 polarCoord_symm_apply
  条件: (p : 实数 × 实数)
  证明: by
  simp [Complex.polarCoord, equivRealProdCLM_symm_apply, mul_add, mul_assoc]

Depends on / 依赖: Cat.Hom.toNatIso, F.mapComp, NatIso, NatIso.naturality_1, mapComp, naturality_1, toNatIso
-/
protected theorem polarCoord_symm_apply (p : Real × Real) :
    Complex.polarCoord.symm p = p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
  simp [Complex.polarCoord, equivRealProdCLM_symm_apply, mul_add, mul_assoc]

/--
theorem `measurableEquivRealProd_symm_polarCoord_symm_apply` / 定理 `measurableEquivRealProd_symm_polarCoord_symm_apply`

English:
theorem measurableEquivRealProd_symm_polarCoord_symm_apply
  given: (p : Real × Real)
  proof: rfl

中文:
定理 measurableEquiv实数Prod_symm_polarCoord_symm_apply
  条件: (p : 实数 × 实数)
  证明: rfl

Depends on / 依赖: Cat.Hom.toNatIso, F.mapComp, NatIso, NatIso.naturality_2, mapComp, naturality_2, toNatIso
-/
theorem measurableEquivRealProd_symm_polarCoord_symm_apply (p : Real × Real) :
    (measurableEquivRealProd.symm (polarCoord.symm p)) = Complex.polarCoord.symm p := rfl

/--
theorem `norm_polarCoord_symm` / 定理 `norm_polarCoord_symm`

English:
theorem norm_polarCoord_symm
  given: (p : Real × Real)
  proof: by simp

中文:
定理 norm_polarCoord_symm
  条件: (p : 实数 × 实数)
  证明: by simp
-/
theorem norm_polarCoord_symm (p : Real × Real) :
    ‖Complex.polarCoord.symm p‖ = |p.1| := by simp

/--
theorem `integral_comp_polarCoord_symm` / 定理 `integral_comp_polarCoord_symm`

English:
theorem integral_comp_polarCoord_symm
  statement: {E : Type*} [NormedAddCommGroup E]
  proof: by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    measurableEquivRealProd.symm.measurableEmbedding]; rw [← integral_comp_polarCoord_symm]
  simp_rw [measurableEquivRealProd_symm_polarCoord_symm_apply]

中文:
定理 integral_comp_polarCoord_symm
  结论: {E : 类型} [赋范交换加群 E]
  证明: by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    measurableEquivRealProd.symm.measurableEmbedding]; rw [← integral_comp_polarCoord_symm]
  simp_rw [measurableEquivRealProd_symm_polarCoord_symm_apply]
-/
protected theorem integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] (f : Complex -> E) :
    (∫ p in polarCoord.target, p.1 • f (Complex.polarCoord.symm p)) = ∫ p, f p := by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    measurableEquivRealProd.symm.measurableEmbedding]; rw [← integral_comp_polarCoord_symm]
  simp_rw [measurableEquivRealProd_symm_polarCoord_symm_apply]

/--
theorem `lintegral_comp_polarCoord_symm` / 定理 `lintegral_comp_polarCoord_symm`

English:
theorem lintegral_comp_polarCoord_symm
  given: (f : Complex -> Real>=0∞)
  proof: by
  rw [← (volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
    measurableEquivRealProd.symm.measurableEmbedding]; rw [← lintegral_comp_polarCoord_symm]
  simp_rw [measurableEquivRealProd_symm_polarCoord_symm_apply]

中文:
定理 lintegral_comp_polarCoord_symm
  条件: (f : 复形 -> 实数>=0∞)
  证明: by
  rw [← (volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
    measurableEquivRealProd.symm.measurableEmbedding]; rw [← lintegral_comp_polarCoord_symm]
  simp_rw [measurableEquivRealProd_symm_polarCoord_symm_apply]
-/
protected theorem lintegral_comp_polarCoord_symm (f : Complex -> Real>=0∞) :
    (∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p)) =
      ∫⁻ p, f p := by
  rw [← (volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
    measurableEquivRealProd.symm.measurableEmbedding]; rw [← lintegral_comp_polarCoord_symm]
  simp_rw [measurableEquivRealProd_symm_polarCoord_symm_apply]

end Complex

section Pi

open ENNReal MeasureTheory MeasureTheory.Measure

variable {ι : Type*}

open ContinuousLinearMap in
/--
Definition of `fderivPiPolarCoordSymm` / `fderivPiPolarCoordSymm` 的定义

English:
definition fderivPiPolarCoordSymm
  signature: (p : ι -> Real × Real)
  body: pi fun i => (fderivPolarCoordSymm (p i)).comp (proj i)

中文:
定义 fderivPiPolarCoordSymm
  签名: (p : ι -> 实数 × 实数)
  定义体: pi fun i => (fderivPolarCoordSymm (p i)).comp (proj i)

Depends on / 依赖: fderivPolarCoordSymm
-/
noncomputable def fderivPiPolarCoordSymm (p : ι -> Real × Real) : (ι -> Real × Real) ->L[Real] ι -> Real × Real :=
  pi fun i => (fderivPolarCoordSymm (p i)).comp (proj i)

/--
theorem `injOn_pi_polarCoord_symm` / 定理 `injOn_pi_polarCoord_symm`

English:
theorem injOn_pi_polarCoord_symm
  proof: fun _ hx _ hy h => funext fun i => polarCoord.symm.injOn (hx i trivial) (hy i trivial)
    ((funext_iff.mp h) i)

中文:
定理 injOn_pi_polarCoord_symm
  证明: fun _ hx _ hy h => funext fun i => polarCoord.symm.injOn (hx i trivial) (hy i trivial)
    ((funext_iff.mp h) i)

Depends on / 依赖: funext_iff, funext_iff.mp, polarCoord, polarCoord.symm.injOn
-/
theorem injOn_pi_polarCoord_symm :
    Set.InjOn (fun p (i : ι) => polarCoord.symm (p i)) (Set.univ.pi fun _ => polarCoord.target) :=
  fun _ hx _ hy h => funext fun i => polarCoord.symm.injOn (hx i trivial) (hy i trivial)
    ((funext_iff.mp h) i)

/--
theorem `abs_fst_of_mem_pi_polarCoord_target` / 定理 `abs_fst_of_mem_pi_polarCoord_target`

English:
theorem abs_fst_of_mem_pi_polarCoord_target
  statement: {p : ι -> Real × Real}
  proof: abs_of_pos ((Set.mem_univ_pi.mp hp) i).1

中文:
定理 abs_fst_of_mem_pi_polarCoord_target
  结论: {p : ι -> 实数 × 实数}
  证明: abs_of_pos ((Set.mem_univ_pi.mp hp) i).1

Depends on / 依赖: Set.mem_univ_pi.mp, abs_of_pos, mem_univ_pi
-/
theorem abs_fst_of_mem_pi_polarCoord_target {p : ι -> Real × Real}
    (hp : p in (Set.univ.pi fun _ : ι => polarCoord.target)) (i : ι) :
    |(p i).1| = (p i).1 :=
  abs_of_pos ((Set.mem_univ_pi.mp hp) i).1

/--
theorem `hasFDerivAt_pi_polarCoord_symm` / 定理 `hasFDerivAt_pi_polarCoord_symm`

English:
theorem hasFDerivAt_pi_polarCoord_symm
  given: [Finite ι] (p : ι -> Real × Real)
  proof: by
  have := Fintype.ofFinite ι
  rw [fderivPiPolarCoordSymm]; rw [hasFDerivAt_pi]
  exact fun i => HasFDerivAt.comp _ (hasFDerivAt_polarCoord_symm _) (hasFDerivAt_apply i _)

中文:
定理 hasFDerivAt_pi_polarCoord_symm
  条件: [有限 ι] (p : ι -> 实数 × 实数)
  证明: by
  have := Fintype.ofFinite ι
  rw [fderivPiPolarCoordSymm]; rw [hasFDerivAt_pi]
  exact fun i => HasFDerivAt.comp _ (hasFDerivAt_polarCoord_symm _) (hasFDerivAt_apply i _)

Depends on / 依赖: Fintype, Fintype.ofFinite, HasFDerivAt, HasFDerivAt.comp, fderivPiPolarCoordSymm, hasFDerivAt_apply, hasFDerivAt_pi, hasFDerivAt_polarCoord_symm, ofFinite
-/
theorem hasFDerivAt_pi_polarCoord_symm [Finite ι] (p : ι -> Real × Real) :
    HasFDerivAt (fun x i => polarCoord.symm (x i)) (fderivPiPolarCoordSymm p) p := by
  have := Fintype.ofFinite ι
  rw [fderivPiPolarCoordSymm]; rw [hasFDerivAt_pi]
  exact fun i => HasFDerivAt.comp _ (hasFDerivAt_polarCoord_symm _) (hasFDerivAt_apply i _)

/--
theorem `measurableSet_pi_polarCoord_target` / 定理 `measurableSet_pi_polarCoord_target`

English:
theorem measurableSet_pi_polarCoord_target
  given: [Finite ι]
  proof: MeasurableSet.univ_pi fun _ => polarCoord.open_target.measurableSet

中文:
定理 measurableSet_pi_polarCoord_target
  条件: [有限 ι]
  证明: MeasurableSet.univ_pi fun _ => polarCoord.open_target.measurableSet

Depends on / 依赖: MeasurableSet, MeasurableSet.univ_pi, measurableSet, open_target, polarCoord, polarCoord.open_target.measurableSet, univ_pi
-/
theorem measurableSet_pi_polarCoord_target [Finite ι] :
    MeasurableSet (Set.univ.pi fun _ : ι => polarCoord.target) :=
  MeasurableSet.univ_pi fun _ => polarCoord.open_target.measurableSet

variable [Fintype ι]

/--
theorem `det_fderivPiPolarCoordSymm` / 定理 `det_fderivPiPolarCoordSymm`

English:
theorem det_fderivPiPolarCoordSymm
  given: (p : ι -> Real × Real)
  proof: by
  simp_rw [fderivPiPolarCoordSymm, ContinuousLinearMap.det_pi, det_fderivPolarCoordSymm]

中文:
定理 det_fderivPiPolarCoordSymm
  条件: (p : ι -> 实数 × 实数)
  证明: by
  simp_rw [fderivPiPolarCoordSymm, ContinuousLinearMap.det_pi, det_fderivPolarCoordSymm]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.det_pi, det_fderivPolarCoordSymm, det_pi, fderivPiPolarCoordSymm, simp_rw
-/
theorem det_fderivPiPolarCoordSymm (p : ι -> Real × Real) :
    (fderivPiPolarCoordSymm p).det = ∏ i, (p i).1 := by
  simp_rw [fderivPiPolarCoordSymm, ContinuousLinearMap.det_pi, det_fderivPolarCoordSymm]

/--
theorem `pi_polarCoord_symm_target_ae_eq_univ` / 定理 `pi_polarCoord_symm_target_ae_eq_univ`

English:
theorem pi_polarCoord_symm_target_ae_eq_univ
  proof: by
  rw [Set.piMap_image_univ_pi]; rw [polarCoord.symm_image_target_eq_source]; rw [volume_pi]; rw [← Set.pi_univ]
  exact ae_eq_set_pi fun _ _ => polarCoord_source_ae_eq_univ

中文:
定理 pi_polarCoord_symm_target_ae_eq_univ
  证明: by
  rw [Set.piMap_image_univ_pi]; rw [polarCoord.symm_image_target_eq_source]; rw [volume_pi]; rw [← Set.pi_univ]
  exact ae_eq_set_pi fun _ _ => polarCoord_source_ae_eq_univ

Depends on / 依赖: Set.piMap_image_univ_pi, Set.pi_univ, ae_eq_set_pi, piMap_image_univ_pi, pi_univ, polarCoord, polarCoord.symm_image_target_eq_source, polarCoord_source_ae_eq_univ, symm_image_target_eq_source, volume_pi
-/
theorem pi_polarCoord_symm_target_ae_eq_univ :
    (Pi.map (fun _ : ι => polarCoord.symm) '' Set.univ.pi fun _ => polarCoord.target)
        =ᵐ[volume] Set.univ := by
  rw [Set.piMap_image_univ_pi]; rw [polarCoord.symm_image_target_eq_source]; rw [volume_pi]; rw [← Set.pi_univ]
  exact ae_eq_set_pi fun _ _ => polarCoord_source_ae_eq_univ

/--
theorem `integral_comp_pi_polarCoord_symm` / 定理 `integral_comp_pi_polarCoord_symm`

English:
theorem integral_comp_pi_polarCoord_symm
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  rw [← setIntegral_univ (f := f)]; rw [← setIntegral_congr_set pi_polarCoord_symm_target_ae_eq_univ]
  convert!
    (integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_pi_polarCoord_target
        (fun p _ => (hasFDerivAt_pi_polarCoord_symm p).hasFDerivWithinAt) injOn_pi_polarCoord_symm
        f).symm using 1
  refine setIntegral_congr_fun measurableSet_pi_polarCoord_target fun x hx => ?_
  simp_rw [det_fderivPiPolarCoordSymm, Finset.abs_prod, abs_fst_of_mem_pi_polarCoord_target hx]

中文:
定理 integral_comp_pi_polarCoord_symm
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  rw [← setIntegral_univ (f := f)]; rw [← setIntegral_congr_set pi_polarCoord_symm_target_ae_eq_univ]
  convert!
    (integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_pi_polarCoord_target
        (fun p _ => (hasFDerivAt_pi_polarCoord_symm p).hasFDerivWithinAt) injOn_pi_polarCoord_symm
        f).symm using 1
  refine setIntegral_congr_fun measurableSet_pi_polarCoord_target fun x hx => ?_
  simp_rw [det_fderivPiPolarCoordSymm, Finset.abs_prod, abs_fst_of_mem_pi_polarCoord_target hx]

Depends on / 依赖: Finset, Finset.abs_prod, abs_fst_of_mem_pi_polarCoord_target, abs_prod, convert, det_fderivPiPolarCoordSymm, hasFDerivAt_pi_polarCoord_symm, hasFDerivWithinAt, injOn_pi_polarCoord_symm, integral_image_eq_integral_abs_det_fderiv_smul, mapComp, measurableSet_pi_polarCoord_target, pi_polarCoord_symm_target_ae_eq_univ, setIntegral_congr_fun, setIntegral_congr_set, setIntegral_univ, simp_rw, volume
-/
theorem integral_comp_pi_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f : (ι -> Real × Real) -> E) :
    (∫ p in (Set.univ.pi fun _ : ι => polarCoord.target),
      (∏ i, (p i).1) • f (fun i => polarCoord.symm (p i))) = ∫ p, f p := by
  rw [← setIntegral_univ (f := f)]; rw [← setIntegral_congr_set pi_polarCoord_symm_target_ae_eq_univ]
  convert!
    (integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_pi_polarCoord_target
        (fun p _ => (hasFDerivAt_pi_polarCoord_symm p).hasFDerivWithinAt) injOn_pi_polarCoord_symm
        f).symm using 1
  refine setIntegral_congr_fun measurableSet_pi_polarCoord_target fun x hx => ?_
  simp_rw [det_fderivPiPolarCoordSymm, Finset.abs_prod, abs_fst_of_mem_pi_polarCoord_target hx]

/--
theorem `Complex.integral_comp_pi_polarCoord_symm` / 定理 `Complex.integral_comp_pi_polarCoord_symm`

English:
theorem Complex.integral_comp_pi_polarCoord_symm
  statement: {E : Type*} [NormedAddCommGroup E]
  proof: by
  let e := MeasurableEquiv.piCongrRight (fun _ : ι => measurableEquivRealProd.symm)
  have := volume_preserving_pi (fun _ : ι => Complex.volume_preserving_equiv_real_prod.symm)
  rw [← MeasurePreserving.integral_comp this e.measurableEmbedding f]
  exact integral_comp_pi_polarCoord_symm (f ∘ e)

中文:
定理 复形.integral_comp_pi_polarCoord_symm
  结论: {E : 类型} [赋范交换加群 E]
  证明: by
  let e := MeasurableEquiv.piCongrRight (fun _ : ι => measurableEquivRealProd.symm)
  have := volume_preserving_pi (fun _ : ι => Complex.volume_preserving_equiv_real_prod.symm)
  rw [← MeasurePreserving.integral_comp this e.measurableEmbedding f]
  exact integral_comp_pi_polarCoord_symm (f ∘ e)
-/
protected theorem Complex.integral_comp_pi_polarCoord_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] (f : (ι -> Complex) -> E) :
    (∫ p in (Set.univ.pi fun _ : ι => Complex.polarCoord.target),
      (∏ i, (p i).1) • f (fun i => Complex.polarCoord.symm (p i))) = ∫ p, f p := by
  let e := MeasurableEquiv.piCongrRight (fun _ : ι => measurableEquivRealProd.symm)
  have := volume_preserving_pi (fun _ : ι => Complex.volume_preserving_equiv_real_prod.symm)
  rw [← MeasurePreserving.integral_comp this e.measurableEmbedding f]
  exact integral_comp_pi_polarCoord_symm (f ∘ e)

/--
theorem `lintegral_comp_pi_polarCoord_symm` / 定理 `lintegral_comp_pi_polarCoord_symm`

English:
theorem lintegral_comp_pi_polarCoord_symm
  given: (f : (ι -> Real × Real) -> Real>=0∞)
  proof: by
  rw [← setLIntegral_univ f]; rw [← setLIntegral_congr pi_polarCoord_symm_target_ae_eq_univ]
  convert!
    (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_pi_polarCoord_target
        (fun p _ => (hasFDerivAt_pi_polarCoord_symm p).hasFDerivWithinAt) injOn_pi_polarCoord_symm
        f).symm using 1
  refine setLIntegral_congr_fun measurableSet_pi_polarCoord_target (fun x hx => ?_)
  simp_rw [det_fderivPiPolarCoordSymm, Finset.abs_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ =>
    abs_nonneg _), abs_fst_of_mem_pi_polarCoord_target hx]

中文:
定理 lintegral_comp_pi_polarCoord_symm
  条件: (f : (ι -> 实数 × 实数) -> 实数>=0∞)
  证明: by
  rw [← setLIntegral_univ f]; rw [← setLIntegral_congr pi_polarCoord_symm_target_ae_eq_univ]
  convert!
    (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_pi_polarCoord_target
        (fun p _ => (hasFDerivAt_pi_polarCoord_symm p).hasFDerivWithinAt) injOn_pi_polarCoord_symm
        f).symm using 1
  refine setLIntegral_congr_fun measurableSet_pi_polarCoord_target (fun x hx => ?_)
  simp_rw [det_fderivPiPolarCoordSymm, Finset.abs_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ =>
    abs_nonneg _), abs_fst_of_mem_pi_polarCoord_target hx]

Depends on / 依赖: ENNReal, ENNReal.ofReal_prod_of_nonneg, Finset, Finset.abs_prod, abs_fs, abs_nonneg, abs_prod, convert, det_fderivPiPolarCoordSymm, hasFDerivAt_pi_polarCoord_symm, hasFDerivWithinAt, injOn_pi_polarCoord_symm, lintegral_image_eq_lintegral_abs_det_fderiv_mul, measurableSet_pi_polarCoord_target, ofReal_prod_of_nonneg, pi_polarCoord_symm_target_ae_eq_univ, setLIntegral_congr, setLIntegral_congr_fun, setLIntegral_univ, simp_rw
-/
theorem lintegral_comp_pi_polarCoord_symm (f : (ι -> Real × Real) -> Real>=0∞) :
    ∫⁻ p in (Set.univ.pi fun _ : ι => polarCoord.target),
      (∏ i, .ofReal (p i).1) * f (fun i => polarCoord.symm (p i)) = ∫⁻ p, f p := by
  rw [← setLIntegral_univ f]; rw [← setLIntegral_congr pi_polarCoord_symm_target_ae_eq_univ]
  convert!
    (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_pi_polarCoord_target
        (fun p _ => (hasFDerivAt_pi_polarCoord_symm p).hasFDerivWithinAt) injOn_pi_polarCoord_symm
        f).symm using 1
  refine setLIntegral_congr_fun measurableSet_pi_polarCoord_target (fun x hx => ?_)
  simp_rw [det_fderivPiPolarCoordSymm, Finset.abs_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ =>
    abs_nonneg _), abs_fst_of_mem_pi_polarCoord_target hx]

/--
theorem `Complex.lintegral_comp_pi_polarCoord_symm` / 定理 `Complex.lintegral_comp_pi_polarCoord_symm`

English:
theorem Complex.lintegral_comp_pi_polarCoord_symm
  given: (f : (ι -> Complex) -> Real>=0∞)
  proof: by
  let e := MeasurableEquiv.piCongrRight (fun _ : ι => measurableEquivRealProd.symm)
  have := volume_preserving_pi (fun _ : ι => Complex.volume_preserving_equiv_real_prod.symm)
  rw [← MeasurePreserving.lintegral_comp_emb this e.measurableEmbedding]
  exact lintegral_comp_pi_polarCoord_symm (f ∘ e)

中文:
定理 复形.lintegral_comp_pi_polarCoord_symm
  条件: (f : (ι -> 复形) -> 实数>=0∞)
  证明: by
  let e := MeasurableEquiv.piCongrRight (fun _ : ι => measurableEquivRealProd.symm)
  have := volume_preserving_pi (fun _ : ι => Complex.volume_preserving_equiv_real_prod.symm)
  rw [← MeasurePreserving.lintegral_comp_emb this e.measurableEmbedding]
  exact lintegral_comp_pi_polarCoord_symm (f ∘ e)
-/
protected theorem Complex.lintegral_comp_pi_polarCoord_symm (f : (ι -> Complex) -> Real>=0∞) :
    ∫⁻ p in (Set.univ.pi fun _ : ι => Complex.polarCoord.target),
      (∏ i, .ofReal (p i).1) * f (fun i => Complex.polarCoord.symm (p i)) = ∫⁻ p, f p := by
  let e := MeasurableEquiv.piCongrRight (fun _ : ι => measurableEquivRealProd.symm)
  have := volume_preserving_pi (fun _ : ι => Complex.volume_preserving_equiv_real_prod.symm)
  rw [← MeasurePreserving.lintegral_comp_emb this e.measurableEmbedding]
  exact lintegral_comp_pi_polarCoord_symm (f ∘ e)

end Pi
