/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# derivatives of the inverse trigonometric functions

Derivatives of `arcsin` and `arccos`.
-/

public section

noncomputable section

open scoped Topology Filter Real ContDiff
open Set

namespace Real

section Arcsin

/--
theorem `deriv_arcsin_aux` / 定理 `deriv_arcsin_aux`

English:
theorem deriv_arcsin_aux
  given: {x : Real} (h₁ : x != -1) (h₂ : x != 1)
  proof: by
  rcases h₁.lt_or_gt with h₁ | h₁
  · have : 1 - x ^ 2 < 0 := by nlinarith [h₁]
    rw [sqrt_eq_zero'.2 this.le]; rw [div_zero]
    have : arcsin =ᶠ[𝓝 x] fun _ => -(π / 2) :=
      (gt_mem_nhds h₁).mono fun y hy => arcsin_of_le_neg_one hy.le
    exact ⟨(hasStrictDerivAt_const x _).congr_of_eventuallyEq this.symm,
      contDiffAt_const.congr_of_eventuallyEq this⟩
  rcases h₂.lt_or_gt with h₂ | h₂
  · have : 0 < √(1 - x ^ 2) := sqrt_pos.2 (by nlinarith [h₁, h₂])
    simp only [← cos_arcsin, one_div] at this ⊢
    exact ⟨sinPartialHomeomorph.hasStrictDerivAt_symm ⟨h₁, h₂⟩ this.ne' (hasStrictDerivAt_sin _),
      sinPartialHomeomorph.contDiffAt_symm_deriv this.ne' ⟨h₁, h₂⟩ (hasDerivAt_sin _)
        contDiff_sin.contDiffAt⟩
  · have : 1 - x ^ 2 < 0 := by nlinarith [h₂]
    rw [sqrt_eq_zero'.2 this.le]; rw [div_zero]
    have : arcsin =ᶠ[𝓝 x] fun _ => π / 2 := (lt_mem_nhds h₂).mono fun y hy => arcsin_of_one_le hy.le
    exact ⟨(hasStrictDerivAt_const x _).congr_of_eventuallyEq this.symm,
      contDiffAt_const.congr_of_eventuallyEq this⟩

中文:
定理 deriv_arcsin_aux
  条件: {x : 实数} (h₁ : x != -1) (h₂ : x != 1)
  证明: by
  rcases h₁.lt_or_gt with h₁ | h₁
  · have : 1 - x ^ 2 < 0 := by nlinarith [h₁]
    rw [sqrt_eq_zero'.2 this.le]; rw [div_zero]
    have : arcsin =ᶠ[𝓝 x] fun _ => -(π / 2) :=
      (gt_mem_nhds h₁).mono fun y hy => arcsin_of_le_neg_one hy.le
    exact ⟨(hasStrictDerivAt_const x _).congr_of_eventuallyEq this.symm,
      contDiffAt_const.congr_of_eventuallyEq this⟩
  rcases h₂.lt_or_gt with h₂ | h₂
  · have : 0 < √(1 - x ^ 2) := sqrt_pos.2 (by nlinarith [h₁, h₂])
    simp only [← cos_arcsin, one_div] at this ⊢
    exact ⟨sinPartialHomeomorph.hasStrictDerivAt_symm ⟨h₁, h₂⟩ this.ne' (hasStrictDerivAt_sin _),
      sinPartialHomeomorph.contDiffAt_symm_deriv this.ne' ⟨h₁, h₂⟩ (hasDerivAt_sin _)
        contDiff_sin.contDiffAt⟩
  · have : 1 - x ^ 2 < 0 := by nlinarith [h₂]
    rw [sqrt_eq_zero'.2 this.le]; rw [div_zero]
    have : arcsin =ᶠ[𝓝 x] fun _ => π / 2 := (lt_mem_nhds h₂).mono fun y hy => arcsin_of_one_le hy.le
    exact ⟨(hasStrictDerivAt_const x _).congr_of_eventuallyEq this.symm,
      contDiffAt_const.congr_of_eventuallyEq this⟩

Depends on / 依赖: arcsin, arcsin_of_le_neg_one, congr_of_eventuallyEq, contDiffAt_const, contDiffAt_const.congr_of_eventuallyEq, cos_arcsin, div_zero, gt_mem_nhds, hasStrictDerivAt_const, hy.le, lt_or_gt, one_div, sinPartialHo, sqrt_eq_zero, sqrt_pos, this.le, this.symm
-/
theorem deriv_arcsin_aux {x : Real} (h₁ : x != -1) (h₂ : x != 1) :
    HasStrictDerivAt arcsin (1 / √(1 - x ^ 2)) x ∧ ContDiffAt Real ω arcsin x := by
  rcases h₁.lt_or_gt with h₁ | h₁
  · have : 1 - x ^ 2 < 0 := by nlinarith [h₁]
    rw [sqrt_eq_zero'.2 this.le]; rw [div_zero]
    have : arcsin =ᶠ[𝓝 x] fun _ => -(π / 2) :=
      (gt_mem_nhds h₁).mono fun y hy => arcsin_of_le_neg_one hy.le
    exact ⟨(hasStrictDerivAt_const x _).congr_of_eventuallyEq this.symm,
      contDiffAt_const.congr_of_eventuallyEq this⟩
  rcases h₂.lt_or_gt with h₂ | h₂
  · have : 0 < √(1 - x ^ 2) := sqrt_pos.2 (by nlinarith [h₁, h₂])
    simp only [← cos_arcsin, one_div] at this ⊢
    exact ⟨sinPartialHomeomorph.hasStrictDerivAt_symm ⟨h₁, h₂⟩ this.ne' (hasStrictDerivAt_sin _),
      sinPartialHomeomorph.contDiffAt_symm_deriv this.ne' ⟨h₁, h₂⟩ (hasDerivAt_sin _)
        contDiff_sin.contDiffAt⟩
  · have : 1 - x ^ 2 < 0 := by nlinarith [h₂]
    rw [sqrt_eq_zero'.2 this.le]; rw [div_zero]
    have : arcsin =ᶠ[𝓝 x] fun _ => π / 2 := (lt_mem_nhds h₂).mono fun y hy => arcsin_of_one_le hy.le
    exact ⟨(hasStrictDerivAt_const x _).congr_of_eventuallyEq this.symm,
      contDiffAt_const.congr_of_eventuallyEq this⟩

/--
theorem `hasStrictDerivAt_arcsin` / 定理 `hasStrictDerivAt_arcsin`

English:
theorem hasStrictDerivAt_arcsin
  given: {x : Real} (h₁ : x != -1) (h₂ : x != 1)
  proof: (deriv_arcsin_aux h₁ h₂).1

中文:
定理 hasStrictDerivAt_arcsin
  条件: {x : 实数} (h₁ : x != -1) (h₂ : x != 1)
  证明: (deriv_arcsin_aux h₁ h₂).1

Depends on / 依赖: deriv_arcsin_aux
-/
theorem hasStrictDerivAt_arcsin {x : Real} (h₁ : x != -1) (h₂ : x != 1) :
    HasStrictDerivAt arcsin (1 / √(1 - x ^ 2)) x :=
  (deriv_arcsin_aux h₁ h₂).1

/--
theorem `hasDerivAt_arcsin` / 定理 `hasDerivAt_arcsin`

English:
theorem hasDerivAt_arcsin
  given: {x : Real} (h₁ : x != -1) (h₂ : x != 1)
  proof: (hasStrictDerivAt_arcsin h₁ h₂).hasDerivAt

中文:
定理 hasDerivAt_arcsin
  条件: {x : 实数} (h₁ : x != -1) (h₂ : x != 1)
  证明: (hasStrictDerivAt_arcsin h₁ h₂).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_arcsin
-/
theorem hasDerivAt_arcsin {x : Real} (h₁ : x != -1) (h₂ : x != 1) :
    HasDerivAt arcsin (1 / √(1 - x ^ 2)) x :=
  (hasStrictDerivAt_arcsin h₁ h₂).hasDerivAt

/--
theorem `contDiffAt_arcsin` / 定理 `contDiffAt_arcsin`

English:
theorem contDiffAt_arcsin
  given: {x : Real} (h₁ : x != -1) (h₂ : x != 1) {n : Nat∞ω}
  proof: (deriv_arcsin_aux h₁ h₂).2.of_le le_top

中文:
定理 contDiffAt_arcsin
  条件: {x : 实数} (h₁ : x != -1) (h₂ : x != 1) {n : 自然数∞ω}
  证明: (deriv_arcsin_aux h₁ h₂).2.of_le le_top

Depends on / 依赖: deriv_arcsin_aux, le_top, of_le
-/
theorem contDiffAt_arcsin {x : Real} (h₁ : x != -1) (h₂ : x != 1) {n : Nat∞ω} :
    ContDiffAt Real n arcsin x :=
  (deriv_arcsin_aux h₁ h₂).2.of_le le_top

/--
theorem `hasDerivWithinAt_arcsin_Ici` / 定理 `hasDerivWithinAt_arcsin_Ici`

English:
theorem hasDerivWithinAt_arcsin_Ici
  given: {x : Real} (h : x != -1)
  proof: by
  rcases eq_or_ne x 1 with (rfl | h')
  · convert! (hasDerivWithinAt_const (1 : Real) _ (π / 2)).congr _ _ <;>
      simp +contextual [arcsin_of_one_le]
  · exact (hasDerivAt_arcsin h h').hasDerivWithinAt

中文:
定理 hasDerivWithinAt_arcsin_Ici
  条件: {x : 实数} (h : x != -1)
  证明: by
  rcases eq_or_ne x 1 with (rfl | h')
  · convert! (hasDerivWithinAt_const (1 : Real) _ (π / 2)).congr _ _ <;>
      simp +contextual [arcsin_of_one_le]
  · exact (hasDerivAt_arcsin h h').hasDerivWithinAt

Depends on / 依赖: arcsin_of_one_le, contextual, convert, eq_or_ne, hasDerivAt_arcsin, hasDerivWithinAt, hasDerivWithinAt_const
-/
theorem hasDerivWithinAt_arcsin_Ici {x : Real} (h : x != -1) :
    HasDerivWithinAt arcsin (1 / √(1 - x ^ 2)) (Ici x) x := by
  rcases eq_or_ne x 1 with (rfl | h')
  · convert! (hasDerivWithinAt_const (1 : Real) _ (π / 2)).congr _ _ <;>
      simp +contextual [arcsin_of_one_le]
  · exact (hasDerivAt_arcsin h h').hasDerivWithinAt

/--
theorem `hasDerivWithinAt_arcsin_Iic` / 定理 `hasDerivWithinAt_arcsin_Iic`

English:
theorem hasDerivWithinAt_arcsin_Iic
  given: {x : Real} (h : x != 1)
  proof: by
  rcases em (x = -1) with (rfl | h')
  · convert! (hasDerivWithinAt_const (-1 : Real) _ (-(π / 2))).congr _ _ <;>
      simp +contextual [arcsin_of_le_neg_one]
  · exact (hasDerivAt_arcsin h' h).hasDerivWithinAt

中文:
定理 hasDerivWithinAt_arcsin_Iic
  条件: {x : 实数} (h : x != 1)
  证明: by
  rcases em (x = -1) with (rfl | h')
  · convert! (hasDerivWithinAt_const (-1 : Real) _ (-(π / 2))).congr _ _ <;>
      simp +contextual [arcsin_of_le_neg_one]
  · exact (hasDerivAt_arcsin h' h).hasDerivWithinAt

Depends on / 依赖: arcsin_of_le_neg_one, contextual, convert, hasDerivAt_arcsin, hasDerivWithinAt, hasDerivWithinAt_const
-/
theorem hasDerivWithinAt_arcsin_Iic {x : Real} (h : x != 1) :
    HasDerivWithinAt arcsin (1 / √(1 - x ^ 2)) (Iic x) x := by
  rcases em (x = -1) with (rfl | h')
  · convert! (hasDerivWithinAt_const (-1 : Real) _ (-(π / 2))).congr _ _ <;>
      simp +contextual [arcsin_of_le_neg_one]
  · exact (hasDerivAt_arcsin h' h).hasDerivWithinAt

/--
theorem `differentiableWithinAt_arcsin_Ici` / 定理 `differentiableWithinAt_arcsin_Ici`

English:
theorem differentiableWithinAt_arcsin_Ici
  given: {x : Real}
  proof: by
  refine ⟨?_, fun h => (hasDerivWithinAt_arcsin_Ici h).differentiableWithinAt⟩
  rintro h rfl
  have : sin ∘ arcsin =ᶠ[𝓝[>=] (-1 : Real)] id := by
    filter_upwards [Icc_mem_nhdsGE (neg_lt_self zero_lt_one)] with x using sin_arcsin'
  have := h.hasDerivWithinAt.sin.congr_of_eventuallyEq this.symm (by simp)
  simpa using (uniqueDiffOn_Ici _ _ self_mem_Ici).eq_deriv _ this (hasDerivWithinAt_id _ _)

中文:
定理 differentiableWithinAt_arcsin_Ici
  条件: {x : 实数}
  证明: by
  refine ⟨?_, fun h => (hasDerivWithinAt_arcsin_Ici h).differentiableWithinAt⟩
  rintro h rfl
  have : sin ∘ arcsin =ᶠ[𝓝[>=] (-1 : Real)] id := by
    filter_upwards [Icc_mem_nhdsGE (neg_lt_self zero_lt_one)] with x using sin_arcsin'
  have := h.hasDerivWithinAt.sin.congr_of_eventuallyEq this.symm (by simp)
  simpa using (uniqueDiffOn_Ici _ _ self_mem_Ici).eq_deriv _ this (hasDerivWithinAt_id _ _)

Depends on / 依赖: Icc_mem_nhdsGE, arcsin, congr_of_eventuallyEq, differentiableWithinAt, eq_deriv, filter_upwards, h.hasDerivWithinAt.sin.congr_of_eventuallyEq, hasDerivWithinAt, hasDerivWithinAt_arcsin_Ici, hasDerivWithinAt_id, neg_lt_self, self_mem_Ici, sin_arcsin, this.symm, uniqueDiffOn_Ici, zero_lt_one
-/
theorem differentiableWithinAt_arcsin_Ici {x : Real} :
    DifferentiableWithinAt Real arcsin (Ici x) x ↔ x != -1 := by
  refine ⟨?_, fun h => (hasDerivWithinAt_arcsin_Ici h).differentiableWithinAt⟩
  rintro h rfl
  have : sin ∘ arcsin =ᶠ[𝓝[>=] (-1 : Real)] id := by
    filter_upwards [Icc_mem_nhdsGE (neg_lt_self zero_lt_one)] with x using sin_arcsin'
  have := h.hasDerivWithinAt.sin.congr_of_eventuallyEq this.symm (by simp)
  simpa using (uniqueDiffOn_Ici _ _ self_mem_Ici).eq_deriv _ this (hasDerivWithinAt_id _ _)

/--
theorem `differentiableWithinAt_arcsin_Iic` / 定理 `differentiableWithinAt_arcsin_Iic`

English:
theorem differentiableWithinAt_arcsin_Iic
  given: {x : Real}
  proof: by
  refine ⟨fun h => ?_, fun h => (hasDerivWithinAt_arcsin_Iic h).differentiableWithinAt⟩
  rw [← neg_neg x]; rw [← image_neg_Ici] at h
  have := (h.comp (-x) differentiableWithinAt_id.fun_neg (mapsTo_image _ _)).fun_neg
  simpa [(· ∘ ·), differentiableWithinAt_arcsin_Ici] using this

中文:
定理 differentiableWithinAt_arcsin_Iic
  条件: {x : 实数}
  证明: by
  refine ⟨fun h => ?_, fun h => (hasDerivWithinAt_arcsin_Iic h).differentiableWithinAt⟩
  rw [← neg_neg x]; rw [← image_neg_Ici] at h
  have := (h.comp (-x) differentiableWithinAt_id.fun_neg (mapsTo_image _ _)).fun_neg
  simpa [(· ∘ ·), differentiableWithinAt_arcsin_Ici] using this

Depends on / 依赖: differentiableWithinAt, differentiableWithinAt_arcsin_Ici, differentiableWithinAt_id, differentiableWithinAt_id.fun_neg, fun_neg, h.comp, hasDerivWithinAt_arcsin_Iic, image_neg_Ici, mapsTo_image, neg_neg
-/
theorem differentiableWithinAt_arcsin_Iic {x : Real} :
    DifferentiableWithinAt Real arcsin (Iic x) x ↔ x != 1 := by
  refine ⟨fun h => ?_, fun h => (hasDerivWithinAt_arcsin_Iic h).differentiableWithinAt⟩
  rw [← neg_neg x]; rw [← image_neg_Ici] at h
  have := (h.comp (-x) differentiableWithinAt_id.fun_neg (mapsTo_image _ _)).fun_neg
  simpa [(· ∘ ·), differentiableWithinAt_arcsin_Ici] using this

/--
theorem `differentiableAt_arcsin` / 定理 `differentiableAt_arcsin`

English:
theorem differentiableAt_arcsin
  given: {x : Real}
  statement: DifferentiableAt Real arcsin x ↔ x != -1 ∧ x != 1
  proof: ⟨fun h => ⟨differentiableWithinAt_arcsin_Ici.1 h.differentiableWithinAt,
      differentiableWithinAt_arcsin_Iic.1 h.differentiableWithinAt⟩,
    fun h => (hasDerivAt_arcsin h.1 h.2).differentiableAt⟩

@[simp]

中文:
定理 differentiableAt_arcsin
  条件: {x : 实数}
  结论: DifferentiableAt 实数 arcsin x ↔ x != -1 ∧ x != 1
  证明: ⟨fun h => ⟨differentiableWithinAt_arcsin_Ici.1 h.differentiableWithinAt,
      differentiableWithinAt_arcsin_Iic.1 h.differentiableWithinAt⟩,
    fun h => (hasDerivAt_arcsin h.1 h.2).differentiableAt⟩

@[simp]

Depends on / 依赖: differentiableAt, differentiableWithinAt, differentiableWithinAt_arcsin_Ici, differentiableWithinAt_arcsin_Iic, h.differentiableWithinAt, hasDerivAt_arcsin
-/
theorem differentiableAt_arcsin {x : Real} : DifferentiableAt Real arcsin x ↔ x != -1 ∧ x != 1 :=
  ⟨fun h => ⟨differentiableWithinAt_arcsin_Ici.1 h.differentiableWithinAt,
      differentiableWithinAt_arcsin_Iic.1 h.differentiableWithinAt⟩,
    fun h => (hasDerivAt_arcsin h.1 h.2).differentiableAt⟩

@[simp]
/--
theorem `deriv_arcsin` / 定理 `deriv_arcsin`

English:
theorem deriv_arcsin
  statement: deriv arcsin = fun x => 1 / √(1 - x ^ 2)
  proof: by
  funext x
  by_cases h : x != -1 ∧ x != 1
  · exact (hasDerivAt_arcsin h.1 h.2).deriv
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_arcsin.1 h)]
    simp only [not_and_or, Ne, Classical.not_not] at h
    rcases h with (rfl | rfl) <;> simp

中文:
定理 deriv_arcsin
  结论: deriv arcsin = fun x => 1 / √(1 - x ^ 2)
  证明: by
  funext x
  by_cases h : x != -1 ∧ x != 1
  · exact (hasDerivAt_arcsin h.1 h.2).deriv
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_arcsin.1 h)]
    simp only [not_and_or, Ne, Classical.not_not] at h
    rcases h with (rfl | rfl) <;> simp

Depends on / 依赖: Classical, Classical.not_not, deriv_zero_of_not_differentiableAt, differentiableAt_arcsin, hasDerivAt_arcsin, not_and_or, not_not
-/
theorem deriv_arcsin : deriv arcsin = fun x => 1 / √(1 - x ^ 2) := by
  funext x
  by_cases h : x != -1 ∧ x != 1
  · exact (hasDerivAt_arcsin h.1 h.2).deriv
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_arcsin.1 h)]
    simp only [not_and_or, Ne, Classical.not_not] at h
    rcases h with (rfl | rfl) <;> simp

/--
theorem `differentiableOn_arcsin` / 定理 `differentiableOn_arcsin`

English:
theorem differentiableOn_arcsin
  statement: DifferentiableOn Real arcsin {-1, 1}ᶜ
  proof: fun _x hx =>
  (differentiableAt_arcsin.2
      ⟨fun h => hx (Or.inl h), fun h => hx (Or.inr h)⟩).differentiableWithinAt

中文:
定理 differentiableOn_arcsin
  结论: DifferentiableOn 实数 arcsin {-1, 1}ᶜ
  证明: fun _x hx =>
  (differentiableAt_arcsin.2
      ⟨fun h => hx (Or.inl h), fun h => hx (Or.inr h)⟩).differentiableWithinAt
-/
theorem differentiableOn_arcsin : DifferentiableOn Real arcsin {-1, 1}ᶜ := fun _x hx =>
  (differentiableAt_arcsin.2
      ⟨fun h => hx (Or.inl h), fun h => hx (Or.inr h)⟩).differentiableWithinAt

/--
theorem `contDiffOn_arcsin` / 定理 `contDiffOn_arcsin`

English:
theorem contDiffOn_arcsin
  given: {n : Nat∞ω}
  statement: ContDiffOn Real n arcsin {-1, 1}ᶜ
  proof: fun _x hx =>
  (contDiffAt_arcsin (mt Or.inl hx) (mt Or.inr hx)).contDiffWithinAt

中文:
定理 contDiffOn_arcsin
  条件: {n : 自然数∞ω}
  结论: ContDiffOn 实数 n arcsin {-1, 1}ᶜ
  证明: fun _x hx =>
  (contDiffAt_arcsin (mt Or.inl hx) (mt Or.inr hx)).contDiffWithinAt
-/
theorem contDiffOn_arcsin {n : Nat∞ω} : ContDiffOn Real n arcsin {-1, 1}ᶜ := fun _x hx =>
  (contDiffAt_arcsin (mt Or.inl hx) (mt Or.inr hx)).contDiffWithinAt

/--
theorem `contDiffAt_arcsin_iff` / 定理 `contDiffAt_arcsin_iff`

English:
theorem contDiffAt_arcsin_iff
  given: {x : Real} {n : Nat∞ω}
  proof: ⟨fun h => or_iff_not_imp_left.2 fun hn => differentiableAt_arcsin.1 h.differentiableAt hn,
    fun h => h.elim (fun hn => hn.symm ▸ (contDiff_zero.2 continuous_arcsin).contDiffAt) fun hx =>
      contDiffAt_arcsin hx.1 hx.2⟩

中文:
定理 contDiffAt_arcsin_iff
  条件: {x : 实数} {n : 自然数∞ω}
  证明: ⟨fun h => or_iff_not_imp_left.2 fun hn => differentiableAt_arcsin.1 h.differentiableAt hn,
    fun h => h.elim (fun hn => hn.symm ▸ (contDiff_zero.2 continuous_arcsin).contDiffAt) fun hx =>
      contDiffAt_arcsin hx.1 hx.2⟩

Depends on / 依赖: contDiffAt, contDiffAt_arcsin, contDiff_zero, continuous_arcsin, differentiableAt, differentiableAt_arcsin, h.differentiableAt, h.elim, hn.symm, or_iff_not_imp_left
-/
theorem contDiffAt_arcsin_iff {x : Real} {n : Nat∞ω} :
    ContDiffAt Real n arcsin x ↔ n = 0 ∨ x != -1 ∧ x != 1 :=
⟨fun h => or_iff_not_imp_left.2 fun hn => differentiableAt_arcsin.1 h.differentiableAt hn,
    fun h => h.elim (fun hn => hn.symm ▸ (contDiff_zero.2 continuous_arcsin).contDiffAt) fun hx =>
      contDiffAt_arcsin hx.1 hx.2⟩

end Arcsin

section Arccos

/--
theorem `hasStrictDerivAt_arccos` / 定理 `hasStrictDerivAt_arccos`

English:
theorem hasStrictDerivAt_arccos
  given: {x : Real} (h₁ : x != -1) (h₂ : x != 1)
  proof: (hasStrictDerivAt_arcsin h₁ h₂).const_sub (π / 2)

中文:
定理 hasStrictDerivAt_arccos
  条件: {x : 实数} (h₁ : x != -1) (h₂ : x != 1)
  证明: (hasStrictDerivAt_arcsin h₁ h₂).const_sub (π / 2)

Depends on / 依赖: const_sub, hasStrictDerivAt_arcsin
-/
theorem hasStrictDerivAt_arccos {x : Real} (h₁ : x != -1) (h₂ : x != 1) :
    HasStrictDerivAt arccos (-(1 / √(1 - x ^ 2))) x :=
  (hasStrictDerivAt_arcsin h₁ h₂).const_sub (π / 2)

/--
theorem `hasDerivAt_arccos` / 定理 `hasDerivAt_arccos`

English:
theorem hasDerivAt_arccos
  given: {x : Real} (h₁ : x != -1) (h₂ : x != 1)
  proof: (hasDerivAt_arcsin h₁ h₂).const_sub (π / 2)

中文:
定理 hasDerivAt_arccos
  条件: {x : 实数} (h₁ : x != -1) (h₂ : x != 1)
  证明: (hasDerivAt_arcsin h₁ h₂).const_sub (π / 2)

Depends on / 依赖: const_sub, hasDerivAt_arcsin
-/
theorem hasDerivAt_arccos {x : Real} (h₁ : x != -1) (h₂ : x != 1) :
    HasDerivAt arccos (-(1 / √(1 - x ^ 2))) x :=
  (hasDerivAt_arcsin h₁ h₂).const_sub (π / 2)

/--
theorem `contDiffAt_arccos` / 定理 `contDiffAt_arccos`

English:
theorem contDiffAt_arccos
  given: {x : Real} (h₁ : x != -1) (h₂ : x != 1) {n : Nat∞ω}
  proof: contDiffAt_const.sub (contDiffAt_arcsin h₁ h₂)

中文:
定理 contDiffAt_arccos
  条件: {x : 实数} (h₁ : x != -1) (h₂ : x != 1) {n : 自然数∞ω}
  证明: contDiffAt_const.sub (contDiffAt_arcsin h₁ h₂)

Depends on / 依赖: contDiffAt_arcsin, contDiffAt_const, contDiffAt_const.sub
-/
theorem contDiffAt_arccos {x : Real} (h₁ : x != -1) (h₂ : x != 1) {n : Nat∞ω} :
    ContDiffAt Real n arccos x :=
  contDiffAt_const.sub (contDiffAt_arcsin h₁ h₂)

/--
theorem `hasDerivWithinAt_arccos_Ici` / 定理 `hasDerivWithinAt_arccos_Ici`

English:
theorem hasDerivWithinAt_arccos_Ici
  given: {x : Real} (h : x != -1)
  proof: (hasDerivWithinAt_arcsin_Ici h).const_sub _

中文:
定理 hasDerivWithinAt_arccos_Ici
  条件: {x : 实数} (h : x != -1)
  证明: (hasDerivWithinAt_arcsin_Ici h).const_sub _

Depends on / 依赖: const_sub, hasDerivWithinAt_arcsin_Ici
-/
theorem hasDerivWithinAt_arccos_Ici {x : Real} (h : x != -1) :
    HasDerivWithinAt arccos (-(1 / √(1 - x ^ 2))) (Ici x) x :=
  (hasDerivWithinAt_arcsin_Ici h).const_sub _

/--
theorem `hasDerivWithinAt_arccos_Iic` / 定理 `hasDerivWithinAt_arccos_Iic`

English:
theorem hasDerivWithinAt_arccos_Iic
  given: {x : Real} (h : x != 1)
  proof: (hasDerivWithinAt_arcsin_Iic h).const_sub _

中文:
定理 hasDerivWithinAt_arccos_Iic
  条件: {x : 实数} (h : x != 1)
  证明: (hasDerivWithinAt_arcsin_Iic h).const_sub _

Depends on / 依赖: const_sub, hasDerivWithinAt_arcsin_Iic
-/
theorem hasDerivWithinAt_arccos_Iic {x : Real} (h : x != 1) :
    HasDerivWithinAt arccos (-(1 / √(1 - x ^ 2))) (Iic x) x :=
  (hasDerivWithinAt_arcsin_Iic h).const_sub _

/--
theorem `differentiableWithinAt_arccos_Ici` / 定理 `differentiableWithinAt_arccos_Ici`

English:
theorem differentiableWithinAt_arccos_Ici
  given: {x : Real}
  proof: (differentiableWithinAt_const_sub_iff _).trans differentiableWithinAt_arcsin_Ici

中文:
定理 differentiableWithinAt_arccos_Ici
  条件: {x : 实数}
  证明: (differentiableWithinAt_const_sub_iff _).trans differentiableWithinAt_arcsin_Ici

Depends on / 依赖: differentiableWithinAt_arcsin_Ici, differentiableWithinAt_const_sub_iff
-/
theorem differentiableWithinAt_arccos_Ici {x : Real} :
    DifferentiableWithinAt Real arccos (Ici x) x ↔ x != -1 :=
  (differentiableWithinAt_const_sub_iff _).trans differentiableWithinAt_arcsin_Ici

/--
theorem `differentiableWithinAt_arccos_Iic` / 定理 `differentiableWithinAt_arccos_Iic`

English:
theorem differentiableWithinAt_arccos_Iic
  given: {x : Real}
  proof: (differentiableWithinAt_const_sub_iff _).trans differentiableWithinAt_arcsin_Iic

中文:
定理 differentiableWithinAt_arccos_Iic
  条件: {x : 实数}
  证明: (differentiableWithinAt_const_sub_iff _).trans differentiableWithinAt_arcsin_Iic

Depends on / 依赖: differentiableWithinAt_arcsin_Iic, differentiableWithinAt_const_sub_iff
-/
theorem differentiableWithinAt_arccos_Iic {x : Real} :
    DifferentiableWithinAt Real arccos (Iic x) x ↔ x != 1 :=
  (differentiableWithinAt_const_sub_iff _).trans differentiableWithinAt_arcsin_Iic

/--
theorem `differentiableAt_arccos` / 定理 `differentiableAt_arccos`

English:
theorem differentiableAt_arccos
  given: {x : Real}
  statement: DifferentiableAt Real arccos x ↔ x != -1 ∧ x != 1
  proof: (differentiableAt_const _).sub_iff_right.trans differentiableAt_arcsin

@[simp]

中文:
定理 differentiableAt_arccos
  条件: {x : 实数}
  结论: DifferentiableAt 实数 arccos x ↔ x != -1 ∧ x != 1
  证明: (differentiableAt_const _).sub_iff_right.trans differentiableAt_arcsin

@[simp]

Depends on / 依赖: differentiableAt_arcsin, differentiableAt_const, sub_iff_right, sub_iff_right.trans
-/
theorem differentiableAt_arccos {x : Real} : DifferentiableAt Real arccos x ↔ x != -1 ∧ x != 1 :=
  (differentiableAt_const _).sub_iff_right.trans differentiableAt_arcsin

@[simp]
/--
theorem `deriv_arccos` / 定理 `deriv_arccos`

English:
theorem deriv_arccos
  statement: deriv arccos = fun x => -(1 / √(1 - x ^ 2))
  proof: funext fun x => (deriv_const_sub _).trans by simp only [deriv_arcsin]

中文:
定理 deriv_arccos
  结论: deriv arccos = fun x => -(1 / √(1 - x ^ 2))
  证明: funext fun x => (deriv_const_sub _).trans by simp only [deriv_arcsin]

Depends on / 依赖: deriv_arcsin, deriv_const_sub
-/
theorem deriv_arccos : deriv arccos = fun x => -(1 / √(1 - x ^ 2)) :=
funext fun x => (deriv_const_sub _).trans by simp only [deriv_arcsin]

/--
theorem `differentiableOn_arccos` / 定理 `differentiableOn_arccos`

English:
theorem differentiableOn_arccos
  statement: DifferentiableOn Real arccos {-1, 1}ᶜ
  proof: differentiableOn_arcsin.const_sub _

中文:
定理 differentiableOn_arccos
  结论: DifferentiableOn 实数 arccos {-1, 1}ᶜ
  证明: differentiableOn_arcsin.const_sub _

Depends on / 依赖: const_sub, differentiableOn_arcsin, differentiableOn_arcsin.const_sub
-/
theorem differentiableOn_arccos : DifferentiableOn Real arccos {-1, 1}ᶜ :=
  differentiableOn_arcsin.const_sub _

/--
theorem `contDiffOn_arccos` / 定理 `contDiffOn_arccos`

English:
theorem contDiffOn_arccos
  given: {n : Nat∞ω}
  statement: ContDiffOn Real n arccos {-1, 1}ᶜ
  proof: contDiffOn_const.sub contDiffOn_arcsin

中文:
定理 contDiffOn_arccos
  条件: {n : 自然数∞ω}
  结论: ContDiffOn 实数 n arccos {-1, 1}ᶜ
  证明: contDiffOn_const.sub contDiffOn_arcsin

Depends on / 依赖: contDiffOn_arcsin, contDiffOn_const, contDiffOn_const.sub
-/
theorem contDiffOn_arccos {n : Nat∞ω} : ContDiffOn Real n arccos {-1, 1}ᶜ :=
  contDiffOn_const.sub contDiffOn_arcsin

/--
theorem `contDiffAt_arccos_iff` / 定理 `contDiffAt_arccos_iff`

English:
theorem contDiffAt_arccos_iff
  given: {x : Real} {n : Nat∞ω}
  proof: by
  refine Iff.trans ⟨fun h => ?_, fun h => ?_⟩ contDiffAt_arcsin_iff <;>
    simpa [arccos] using! (contDiffAt_const (c := π / 2)).sub h

中文:
定理 contDiffAt_arccos_iff
  条件: {x : 实数} {n : 自然数∞ω}
  证明: by
  refine Iff.trans ⟨fun h => ?_, fun h => ?_⟩ contDiffAt_arcsin_iff <;>
    simpa [arccos] using! (contDiffAt_const (c := π / 2)).sub h

Depends on / 依赖: Iff.trans, arccos, contDiffAt_arcsin_iff, contDiffAt_const
-/
theorem contDiffAt_arccos_iff {x : Real} {n : Nat∞ω} :
    ContDiffAt Real n arccos x ↔ n = 0 ∨ x != -1 ∧ x != 1 := by
  refine Iff.trans ⟨fun h => ?_, fun h => ?_⟩ contDiffAt_arcsin_iff <;>
    simpa [arccos] using! (contDiffAt_const (c := π / 2)).sub h

end Arccos

end Real
