/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-! # Interactions of the continuous functional calculus with the real and imaginary part -/

public section

open Complex ComplexStarModule

variable {A : Type*} [TopologicalSpace A]

section NonUnital

variable [NonUnitalRing A] [StarRing A] [Module Complex A] [IsScalarTower Complex A A] [SMulCommClass Complex A A]
  [StarModule Complex A] [NonUnitalContinuousFunctionalCalculus Complex A IsStarNormal]

/--
lemma `cfcₙ_re_id` / 引理 `cfcₙ_re_id`

English:
lemma cfcₙ_re_id
  given: (a : A) (ha : IsStarNormal a := by cfc_tac)
  proof: by
  conv_rhs => rw [realPart_apply_coe, ← cfcₙ_id' Complex a, ← cfcₙ_star, ← cfcₙ_add .., ← cfcₙ_smul ..]
  refine cfcₙ_congr fun x hx => ?_
  rw [Complex.re_eq_add_conj]; rw [← smul_one_smul Complex 2⁻¹]
  simp [div_eq_inv_mul]

中文:
引理 cfcₙ_re_id
  条件: (a : A) (ha : 是StarNormal a := by cfc_tac)
  证明: by
  conv_rhs => rw [realPart_apply_coe, ← cfcₙ_id' Complex a, ← cfcₙ_star, ← cfcₙ_add .., ← cfcₙ_smul ..]
  refine cfcₙ_congr fun x hx => ?_
  rw [Complex.re_eq_add_conj]; rw [← smul_one_smul Complex 2⁻¹]
  simp [div_eq_inv_mul]

Depends on / 依赖: Complex.re_eq_add_conj, cfc_tac, conv_rhs, div_eq_inv_mul, re_eq_add_conj, realPart_apply_coe, smul_one_smul
-/
lemma cfcₙ_re_id (a : A) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (re · : Complex -> Complex) a = ℜ a := by
  conv_rhs => rw [realPart_apply_coe, ← cfcₙ_id' Complex a, ← cfcₙ_star, ← cfcₙ_add .., ← cfcₙ_smul ..]
  refine cfcₙ_congr fun x hx => ?_
  rw [Complex.re_eq_add_conj]; rw [← smul_one_smul Complex 2⁻¹]
  simp [div_eq_inv_mul]

/--
lemma `cfcₙ_im_id` / 引理 `cfcₙ_im_id`

English:
lemma cfcₙ_im_id
  given: (a : A) (ha : IsStarNormal a := by cfc_tac)
  proof: by
  suffices cfcₙ (fun z : Complex => re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfcₙ_add ..]; rw [cfcₙ_const_mul ..]; rw [cfcₙ_re_id a] at this
    simpa
  simp [mul_comm I, re_add_im, cfcₙ_id' .., realPart_add_I_smul_imaginaryPart]

中文:
引理 cfcₙ_im_id
  条件: (a : A) (ha : 是StarNormal a := by cfc_tac)
  证明: by
  suffices cfcₙ (fun z : Complex => re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfcₙ_add ..]; rw [cfcₙ_const_mul ..]; rw [cfcₙ_re_id a] at this
    simpa
  simp [mul_comm I, re_add_im, cfcₙ_id' .., realPart_add_I_smul_imaginaryPart]

Depends on / 依赖: cfc_tac, mul_comm, re_add_im, realPart_add_I_smul_imaginaryPart
-/
lemma cfcₙ_im_id (a : A) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (im · : Complex -> Complex) a = ℑ a := by
  suffices cfcₙ (fun z : Complex => re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfcₙ_add ..]; rw [cfcₙ_const_mul ..]; rw [cfcₙ_re_id a] at this
    simpa
  simp [mul_comm I, re_add_im, cfcₙ_id' .., realPart_add_I_smul_imaginaryPart]

/--
lemma `quasispectrum_realPart` / 引理 `quasispectrum_realPart`

English:
lemma quasispectrum_realPart
  given: (a : A) (ha : IsStarNormal a := by cfc_tac)
  proof: by
  rw [← cfcₙ_re_id a]; rw [cfcₙ_map_quasispectrum ..]

中文:
引理 quasispectrum_realPart
  条件: (a : A) (ha : 是StarNormal a := by cfc_tac)
  证明: by
  rw [← cfcₙ_re_id a]; rw [cfcₙ_map_quasispectrum ..]

Depends on / 依赖: cfc_tac, quasispectrum
-/
lemma quasispectrum_realPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum Complex (ℜ a : A) = (fun x => (re x : Complex)) '' (quasispectrum Complex a) := by
  rw [← cfcₙ_re_id a]; rw [cfcₙ_map_quasispectrum ..]

-- fails to find `IsScalarTower ℝ ℂ A`.
/--
lemma `quasispectrum_realPart'` / 引理 `quasispectrum_realPart'`

English:
lemma quasispectrum_realPart'
  given: (a : A) (ha : IsStarNormal a := by cfc_tac)
  proof: by
  simp [← (ℜ a).2.quasispectrumRestricts.image, quasispectrum_realPart a, Set.image_image]

中文:
引理 quasispectrum_realPart'
  条件: (a : A) (ha : 是StarNormal a := by cfc_tac)
  证明: by
  simp [← (ℜ a).2.quasispectrumRestricts.image, quasispectrum_realPart a, Set.image_image]

Depends on / 依赖: Set.image_image, cfc_tac, image_image, quasispectrum, quasispectrumRestricts, quasispectrumRestricts.image, quasispectrum_realPart
-/
lemma quasispectrum_realPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum Real (ℜ a : A) = re '' (quasispectrum Complex a) := by
  simp [← (ℜ a).2.quasispectrumRestricts.image, quasispectrum_realPart a, Set.image_image]

/--
lemma `quasispectrum_imaginaryPart` / 引理 `quasispectrum_imaginaryPart`

English:
lemma quasispectrum_imaginaryPart
  given: (a : A) (ha : IsStarNormal a := by cfc_tac)
  proof: by
  rw [← cfcₙ_im_id a]; rw [cfcₙ_map_quasispectrum ..]

中文:
引理 quasispectrum_imaginaryPart
  条件: (a : A) (ha : 是StarNormal a := by cfc_tac)
  证明: by
  rw [← cfcₙ_im_id a]; rw [cfcₙ_map_quasispectrum ..]

Depends on / 依赖: cfc_tac, quasispectrum
-/
lemma quasispectrum_imaginaryPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum Complex (ℑ a : A) = (fun x => (im x : Complex)) '' (quasispectrum Complex a) := by
  rw [← cfcₙ_im_id a]; rw [cfcₙ_map_quasispectrum ..]

-- fails to find `IsScalarTower ℝ ℂ A`.
/--
lemma `quasispectrum_imaginaryPart'` / 引理 `quasispectrum_imaginaryPart'`

English:
lemma quasispectrum_imaginaryPart'
  given: (a : A) (ha : IsStarNormal a := by cfc_tac)
  proof: by
  simp [← (ℑ a).2.quasispectrumRestricts.image, quasispectrum_imaginaryPart a, Set.image_image]

中文:
引理 quasispectrum_imaginaryPart'
  条件: (a : A) (ha : 是StarNormal a := by cfc_tac)
  证明: by
  simp [← (ℑ a).2.quasispectrumRestricts.image, quasispectrum_imaginaryPart a, Set.image_image]

Depends on / 依赖: Set.image_image, cfc_tac, image_image, quasispectrum, quasispectrumRestricts, quasispectrumRestricts.image, quasispectrum_imaginaryPart
-/
lemma quasispectrum_imaginaryPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum Real (ℑ a : A) = im '' (quasispectrum Complex a) := by
  simp [← (ℑ a).2.quasispectrumRestricts.image, quasispectrum_imaginaryPart a, Set.image_image]

variable [ContinuousMapZero.UniqueHom Complex A]

/--
lemma `cfcₙ_realPart` / 引理 `cfcₙ_realPart`

English:
lemma cfcₙ_realPart
  statement: (f : Complex -> Complex) (a : A)
  proof: by
  rw [quasispectrum_realPart a] at hf
  rw [← cfcₙ_re_id a]; rw [← cfcₙ_comp' ..]

中文:
引理 cfcₙ_realPart
  结论: (f : 复形 -> 复形) (a : A)
  证明: by
  rw [quasispectrum_realPart a] at hf
  rw [← cfcₙ_re_id a]; rw [← cfcₙ_comp' ..]

Depends on / 依赖: IsStarNormal, cfc_cont_tac, cfc_tac, cfc_zero_tac, quasispectrum_realPart
-/
lemma cfcₙ_realPart (f : Complex -> Complex) (a : A)
    (hf : ContinuousOn f (quasispectrum Complex (ℜ a : A)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ f (ℜ a : A) = cfcₙ (fun x => f (re x)) a := by
  rw [quasispectrum_realPart a] at hf
  rw [← cfcₙ_re_id a]; rw [← cfcₙ_comp' ..]

/--
lemma `cfcₙ_imaginaryPart` / 引理 `cfcₙ_imaginaryPart`

English:
lemma cfcₙ_imaginaryPart
  statement: (f : Complex -> Complex) (a : A)
  proof: by
  rw [quasispectrum_imaginaryPart a] at hf
  rw [← cfcₙ_im_id a]; rw [← cfcₙ_comp' ..]

中文:
引理 cfcₙ_imaginaryPart
  结论: (f : 复形 -> 复形) (a : A)
  证明: by
  rw [quasispectrum_imaginaryPart a] at hf
  rw [← cfcₙ_im_id a]; rw [← cfcₙ_comp' ..]

Depends on / 依赖: IsStarNormal, cfc_cont_tac, cfc_tac, cfc_zero_tac, quasispectrum_imaginaryPart
-/
lemma cfcₙ_imaginaryPart (f : Complex -> Complex) (a : A)
    (hf : ContinuousOn f (quasispectrum Complex (ℑ a : A)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ f (ℑ a : A) = cfcₙ (fun x => f (im x)) a := by
  rw [quasispectrum_imaginaryPart a] at hf
  rw [← cfcₙ_im_id a]; rw [← cfcₙ_comp' ..]

variable [T2Space A]

/--
lemma `cfcₙ_comp_re` / 引理 `cfcₙ_comp_re`

English:
lemma cfcₙ_comp_re
  statement: (f : Real -> Real) (a : A)
  proof: by
  have : ContinuousOn (fun x => (f x.re) : Complex -> Complex) ((re · : Complex -> Complex) '' quasispectrum Complex a) := by
    rw [quasispectrum_realPart' a] at hf
refine continuous_ofReal.comp_continuousOn hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.

中文:
引理 cfcₙ_comp_re
  结论: (f : 实数 -> 实数) (a : A)
  证明: by
  have : ContinuousOn (fun x => (f x.re) : Complex -> Complex) ((re · : Complex -> Complex) '' quasispectrum Complex a) := by
    rw [quasispectrum_realPart' a] at hf
refine continuous_ofReal.comp_continuousOn hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.

Depends on / 依赖: ContinuousOn, Function, Function.comp_def, IsStarNormal, Set.mapsTo_image, Set.mapsTo_image_iff, cfc_cont_tac, cfc_tac, cfc_zero_tac, comp_continuousOn, comp_def, continuous_ofReal, continuous_ofReal.comp_continuousOn, conv_rhs, fun_prop, hf.comp, mapsTo_image, mapsTo_image_iff, quasispectrum, quasispectrum_realPart
-/
lemma cfcₙ_comp_re (f : Real -> Real) (a : A)
    (hf : ContinuousOn f (quasispectrum Real (ℜ a : A)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (fun x : Complex => f (re x)) a = cfcₙ f (ℜ a : A) := by
  have : ContinuousOn (fun x => (f x.re) : Complex -> Complex) ((re · : Complex -> Complex) '' quasispectrum Complex a) := by
    rw [quasispectrum_realPart' a] at hf
refine continuous_ofReal.comp_continuousOn hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfcₙ_real_eq_complex]; rw [← cfcₙ_re_id a]; rw [← cfcₙ_comp' ..]
    simp

/--
lemma `cfcₙ_comp_im` / 引理 `cfcₙ_comp_im`

English:
lemma cfcₙ_comp_im
  statement: (f : Real -> Real) (a : A)
  proof: by
  have : ContinuousOn (fun x => (f x.re) : Complex -> Complex) ((im · : Complex -> Complex) '' quasispectrum Complex a) := by
    rw [quasispectrum_imaginaryPart' a] at hf
refine continuous_ofReal.comp_continuousOn hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using

中文:
引理 cfcₙ_comp_im
  结论: (f : 实数 -> 实数) (a : A)
  证明: by
  have : ContinuousOn (fun x => (f x.re) : Complex -> Complex) ((im · : Complex -> Complex) '' quasispectrum Complex a) := by
    rw [quasispectrum_imaginaryPart' a] at hf
refine continuous_ofReal.comp_continuousOn hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using

Depends on / 依赖: ContinuousOn, Function, Function.comp_def, IsStarNormal, Set.mapsTo_image, Set.mapsTo_image_iff, cfc_cont_tac, cfc_tac, cfc_zero_tac, comp_continuousOn, comp_def, continuous_ofReal, continuous_ofReal.comp_continuousOn, conv_rhs, fun_prop, hf.comp, mapsTo_image, mapsTo_image_iff, quasispectrum, quasispectrum_imaginaryPart
-/
lemma cfcₙ_comp_im (f : Real -> Real) (a : A)
    (hf : ContinuousOn f (quasispectrum Real (ℑ a : A)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (fun x : Complex => f (im x)) a = cfcₙ f (ℑ a : A) := by
  have : ContinuousOn (fun x => (f x.re) : Complex -> Complex) ((im · : Complex -> Complex) '' quasispectrum Complex a) := by
    rw [quasispectrum_imaginaryPart' a] at hf
refine continuous_ofReal.comp_continuousOn hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfcₙ_real_eq_complex]; rw [← cfcₙ_im_id a]; rw [← cfcₙ_comp' ..]
    simp

end NonUnital

section Unital

variable [Ring A] [StarRing A] [Algebra Complex A] [StarModule Complex A]
  [ContinuousFunctionalCalculus Complex A IsStarNormal]

/--
lemma `cfc_re_id` / 引理 `cfc_re_id`

English:
lemma cfc_re_id
  given: (a : A) (hp : IsStarNormal a := by cfc_tac)
  proof: by
  conv_rhs => rw [realPart_apply_coe, ← cfc_id' Complex a, ← cfc_star, ← cfc_add .., ← cfc_smul ..]
  refine cfc_congr fun x hx => ?_
  rw [Complex.re_eq_add_conj]; rw [← smul_one_smul Complex 2⁻¹]
  simp [div_eq_inv_mul]

中文:
引理 cfc_re_id
  条件: (a : A) (hp : 是StarNormal a := by cfc_tac)
  证明: by
  conv_rhs => rw [realPart_apply_coe, ← cfc_id' Complex a, ← cfc_star, ← cfc_add .., ← cfc_smul ..]
  refine cfc_congr fun x hx => ?_
  rw [Complex.re_eq_add_conj]; rw [← smul_one_smul Complex 2⁻¹]
  simp [div_eq_inv_mul]

Depends on / 依赖: Complex.re_eq_add_conj, cfc_add, cfc_congr, cfc_id, cfc_smul, cfc_star, cfc_tac, conv_rhs, div_eq_inv_mul, re_eq_add_conj, realPart_apply_coe, smul_one_smul
-/
lemma cfc_re_id (a : A) (hp : IsStarNormal a := by cfc_tac) :
    cfc (re · : Complex -> Complex) a = ℜ a := by
  conv_rhs => rw [realPart_apply_coe, ← cfc_id' Complex a, ← cfc_star, ← cfc_add .., ← cfc_smul ..]
  refine cfc_congr fun x hx => ?_
  rw [Complex.re_eq_add_conj]; rw [← smul_one_smul Complex 2⁻¹]
  simp [div_eq_inv_mul]

/--
lemma `cfc_im_id` / 引理 `cfc_im_id`

English:
lemma cfc_im_id
  given: (a : A) (hp : IsStarNormal a := by cfc_tac)
  proof: by
  suffices cfc (fun z : Complex => re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfc_add ..]; rw [cfc_const_mul ..]; rw [cfc_re_id a] at this
    simpa
  simp [mul_comm I, re_add_im, cfc_id' .., realPart_add_I_smul_imaginaryPart]

中文:
引理 cfc_im_id
  条件: (a : A) (hp : 是StarNormal a := by cfc_tac)
  证明: by
  suffices cfc (fun z : Complex => re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfc_add ..]; rw [cfc_const_mul ..]; rw [cfc_re_id a] at this
    simpa
  simp [mul_comm I, re_add_im, cfc_id' .., realPart_add_I_smul_imaginaryPart]

Depends on / 依赖: cfc_add, cfc_const_mul, cfc_id, cfc_re_id, cfc_tac, mul_comm, re_add_im, realPart_add_I_smul_imaginaryPart
-/
lemma cfc_im_id (a : A) (hp : IsStarNormal a := by cfc_tac) :
    cfc (im · : Complex -> Complex) a = ℑ a := by
  suffices cfc (fun z : Complex => re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfc_add ..]; rw [cfc_const_mul ..]; rw [cfc_re_id a] at this
    simpa
  simp [mul_comm I, re_add_im, cfc_id' .., realPart_add_I_smul_imaginaryPart]

/--
lemma `spectrum_realPart` / 引理 `spectrum_realPart`

English:
lemma spectrum_realPart
  given: (a : A) (ha : IsStarNormal a := by cfc_tac)
  proof: by
  rw [← cfc_re_id a]; rw [cfc_map_spectrum ..]

中文:
引理 spectrum_realPart
  条件: (a : A) (ha : 是StarNormal a := by cfc_tac)
  证明: by
  rw [← cfc_re_id a]; rw [cfc_map_spectrum ..]

Depends on / 依赖: cfc_map_spectrum, cfc_re_id, cfc_tac, spectrum
-/
lemma spectrum_realPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum Complex (ℜ a : A) = (fun x => (re x : Complex)) '' (spectrum Complex a) := by
  rw [← cfc_re_id a]; rw [cfc_map_spectrum ..]

/--
lemma `spectrum_realPart'` / 引理 `spectrum_realPart'`

English:
lemma spectrum_realPart'
  given: (a : A) (ha : IsStarNormal a := by cfc_tac)
  proof: by
  simp [← (ℜ a).2.spectrumRestricts.image, spectrum_realPart a, Set.image_image]

中文:
引理 spectrum_realPart'
  条件: (a : A) (ha : 是StarNormal a := by cfc_tac)
  证明: by
  simp [← (ℜ a).2.spectrumRestricts.image, spectrum_realPart a, Set.image_image]

Depends on / 依赖: Set.image_image, cfc_tac, image_image, spectrum, spectrumRestricts, spectrumRestricts.image, spectrum_realPart
-/
lemma spectrum_realPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum Real (ℜ a : A) = re '' (spectrum Complex a) := by
  simp [← (ℜ a).2.spectrumRestricts.image, spectrum_realPart a, Set.image_image]

/--
lemma `spectrum_imaginaryPart` / 引理 `spectrum_imaginaryPart`

English:
lemma spectrum_imaginaryPart
  given: (a : A) (ha : IsStarNormal a := by cfc_tac)
  proof: by
  rw [← cfc_im_id a]; rw [cfc_map_spectrum ..]

中文:
引理 spectrum_imaginaryPart
  条件: (a : A) (ha : 是StarNormal a := by cfc_tac)
  证明: by
  rw [← cfc_im_id a]; rw [cfc_map_spectrum ..]

Depends on / 依赖: cfc_im_id, cfc_map_spectrum, cfc_tac, spectrum
-/
lemma spectrum_imaginaryPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum Complex (ℑ a : A) = (fun x => (im x : Complex)) '' (spectrum Complex a) := by
  rw [← cfc_im_id a]; rw [cfc_map_spectrum ..]

/--
lemma `spectrum_imaginaryPart'` / 引理 `spectrum_imaginaryPart'`

English:
lemma spectrum_imaginaryPart'
  given: (a : A) (ha : IsStarNormal a := by cfc_tac)
  proof: by
  simp [← (ℑ a).2.spectrumRestricts.image, spectrum_imaginaryPart a, Set.image_image]

中文:
引理 spectrum_imaginaryPart'
  条件: (a : A) (ha : 是StarNormal a := by cfc_tac)
  证明: by
  simp [← (ℑ a).2.spectrumRestricts.image, spectrum_imaginaryPart a, Set.image_image]

Depends on / 依赖: Set.image_image, cfc_tac, image_image, spectrum, spectrumRestricts, spectrumRestricts.image, spectrum_imaginaryPart
-/
lemma spectrum_imaginaryPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum Real (ℑ a : A) = im '' (spectrum Complex a) := by
  simp [← (ℑ a).2.spectrumRestricts.image, spectrum_imaginaryPart a, Set.image_image]

variable [ContinuousMap.UniqueHom Complex A]

/--
lemma `cfc_realPart` / 引理 `cfc_realPart`

English:
lemma cfc_realPart
  statement: (f : Complex -> Complex) (a : A) (hf : ContinuousOn f (spectrum Complex (ℜ a : A)) := by cfc_tac)
  proof: by
  rw [spectrum_realPart a] at hf
  rw [← cfc_re_id a]; rw [← cfc_comp' ..]

中文:
引理 cfc_realPart
  结论: (f : 复形 -> 复形) (a : A) (hf : ContinuousOn f (spectrum 复形 (ℜ a : A)) := by cfc_tac)
  证明: by
  rw [spectrum_realPart a] at hf
  rw [← cfc_re_id a]; rw [← cfc_comp' ..]

Depends on / 依赖: IsStarNormal, cfc_comp, cfc_re_id, cfc_tac, spectrum_realPart
-/
lemma cfc_realPart (f : Complex -> Complex) (a : A) (hf : ContinuousOn f (spectrum Complex (ℜ a : A)) := by cfc_tac)
    (ha : IsStarNormal a := by cfc_tac) :
    cfc f (ℜ a : A) = cfc (fun x => f (re x)) a := by
  rw [spectrum_realPart a] at hf
  rw [← cfc_re_id a]; rw [← cfc_comp' ..]

/--
lemma `cfc_imaginaryPart` / 引理 `cfc_imaginaryPart`

English:
lemma cfc_imaginaryPart
  statement: (f : Complex -> Complex) (a : A)
  proof: by
  rw [spectrum_imaginaryPart a] at hf
  rw [← cfc_im_id a]; rw [← cfc_comp' ..]

中文:
引理 cfc_imaginaryPart
  结论: (f : 复形 -> 复形) (a : A)
  证明: by
  rw [spectrum_imaginaryPart a] at hf
  rw [← cfc_im_id a]; rw [← cfc_comp' ..]

Depends on / 依赖: IsStarNormal, cfc_comp, cfc_im_id, cfc_tac, spectrum_imaginaryPart
-/
lemma cfc_imaginaryPart (f : Complex -> Complex) (a : A)
    (hf : ContinuousOn f (spectrum Complex (ℑ a : A)) := by cfc_tac)
    (ha : IsStarNormal a := by cfc_tac) :
    cfc f (ℑ a : A) = cfc (fun x => f (im x)) a := by
  rw [spectrum_imaginaryPart a] at hf
  rw [← cfc_im_id a]; rw [← cfc_comp' ..]

variable [T2Space A]

/--
lemma `cfc_comp_re` / 引理 `cfc_comp_re`

English:
lemma cfc_comp_re
  statement: (f : Real -> Real) (a : A)
  proof: by
  have : ContinuousOn (fun x => (f x.re) : Complex -> Complex) ((re · : Complex -> Complex) '' spectrum Complex a) := by
    rw [spectrum_realPart' a] at hf
refine continuous_ofReal.comp_continuousOn hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_ima

中文:
引理 cfc_comp_re
  结论: (f : 实数 -> 实数) (a : A)
  证明: by
  have : ContinuousOn (fun x => (f x.re) : Complex -> Complex) ((re · : Complex -> Complex) '' spectrum Complex a) := by
    rw [spectrum_realPart' a] at hf
refine continuous_ofReal.comp_continuousOn hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_ima

Depends on / 依赖: ContinuousOn, Function, Function.comp_def, IsStarNormal, Set.mapsTo_image, Set.mapsTo_image_iff, cfc_comp, cfc_re_id, cfc_real_eq_complex, cfc_tac, comp_continuousOn, comp_def, continuous_ofReal, continuous_ofReal.comp_continuousOn, conv_rhs, fun_prop, hf.comp, mapsTo_image, mapsTo_image_iff, spectrum
-/
lemma cfc_comp_re (f : Real -> Real) (a : A)
    (hf : ContinuousOn f (spectrum Real (ℜ a : A)) := by cfc_tac)
    (ha : IsStarNormal a := by cfc_tac) :
    cfc (fun x : Complex => f (re x)) a = cfc f (ℜ a : A) := by
  have : ContinuousOn (fun x => (f x.re) : Complex -> Complex) ((re · : Complex -> Complex) '' spectrum Complex a) := by
    rw [spectrum_realPart' a] at hf
refine continuous_ofReal.comp_continuousOn hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfc_real_eq_complex]; rw [← cfc_re_id a]; rw [← cfc_comp' ..]
    simp

/--
lemma `cfc_comp_im` / 引理 `cfc_comp_im`

English:
lemma cfc_comp_im
  statement: (f : Real -> Real) (a : A) (hf : ContinuousOn f (spectrum Real (ℑ a : A)))
  proof: by
  have : ContinuousOn (fun x => (f x.re) : Complex -> Complex) ((im · : Complex -> Complex) '' spectrum Complex a) := by
    rw [spectrum_imaginaryPart' a] at hf
refine continuous_ofReal.comp_continuousOn hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsT

中文:
引理 cfc_comp_im
  结论: (f : 实数 -> 实数) (a : A) (hf : ContinuousOn f (spectrum 实数 (ℑ a : A)))
  证明: by
  have : ContinuousOn (fun x => (f x.re) : Complex -> Complex) ((im · : Complex -> Complex) '' spectrum Complex a) := by
    rw [spectrum_imaginaryPart' a] at hf
refine continuous_ofReal.comp_continuousOn hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsT

Depends on / 依赖: ContinuousOn, Function, Function.comp_def, Set.mapsTo_image, Set.mapsTo_image_iff, cfc_comp, cfc_im_id, cfc_real_eq_complex, cfc_tac, comp_continuousOn, comp_def, continuous_ofReal, continuous_ofReal.comp_continuousOn, conv_rhs, fun_prop, hf.comp, mapsTo_image, mapsTo_image_iff, spectrum, spectrum_imaginaryPart
-/
lemma cfc_comp_im (f : Real -> Real) (a : A) (hf : ContinuousOn f (spectrum Real (ℑ a : A)))
    (ha : IsStarNormal a := by cfc_tac) :
    cfc (fun x : Complex => f (im x)) a = cfc f (ℑ a : A) := by
  have : ContinuousOn (fun x => (f x.re) : Complex -> Complex) ((im · : Complex -> Complex) '' spectrum Complex a) := by
    rw [spectrum_imaginaryPart' a] at hf
refine continuous_ofReal.comp_continuousOn hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfc_real_eq_complex]; rw [← cfc_im_id a]; rw [← cfc_comp' ..]
    simp

end Unital
