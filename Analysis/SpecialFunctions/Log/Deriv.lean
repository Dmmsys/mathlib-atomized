/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.AdaptationNote

/-!
# Derivative and series expansion of real logarithm

In this file we prove that `Real.log` is infinitely smooth at all nonzero `x : ℝ`. We also prove
that the series `∑' n : ℕ, x ^ (n + 1) / (n + 1)` converges to `(-Real.log (1 - x))` for all
`x : ℝ`, `|x| < 1`.

## Tags

logarithm, derivative
-/

public section


open Filter Finset Set

open scoped Topology ContDiff

namespace Real

variable {x : Real}

/--
theorem `hasStrictDerivAt_log_of_pos` / 定理 `hasStrictDerivAt_log_of_pos`

English:
theorem hasStrictDerivAt_log_of_pos
  given: (hx : 0 < x)
  statement: HasStrictDerivAt log x⁻¹ x
  proof: by
  have : HasStrictDerivAt log (exp <| log x)⁻¹ x :=
    (hasStrictDerivAt_exp <| log x).of_local_left_inverse (continuousAt_log hx.ne')
(ne_of_gt <| exp_pos _)
      Eventually.mono (lt_mem_nhds hx) @exp_log
  rwa [exp_log hx] at this

中文:
定理 hasStrictDerivAt_log_of_pos
  条件: (hx : 0 < x)
  结论: HasStrictDerivAt log x⁻¹ x
  证明: by
  have : HasStrictDerivAt log (exp <| log x)⁻¹ x :=
    (hasStrictDerivAt_exp <| log x).of_local_left_inverse (continuousAt_log hx.ne')
(ne_of_gt <| exp_pos _)
      Eventually.mono (lt_mem_nhds hx) @exp_log
  rwa [exp_log hx] at this

Depends on / 依赖: Eventually, Eventually.mono, HasStrictDerivAt, continuousAt_log, exp_log, exp_pos, hasStrictDerivAt_exp, hx.ne, lt_mem_nhds, ne_of_gt, of_local_left_inverse
-/
theorem hasStrictDerivAt_log_of_pos (hx : 0 < x) : HasStrictDerivAt log x⁻¹ x := by
  have : HasStrictDerivAt log (exp <| log x)⁻¹ x :=
    (hasStrictDerivAt_exp <| log x).of_local_left_inverse (continuousAt_log hx.ne')
(ne_of_gt <| exp_pos _)
      Eventually.mono (lt_mem_nhds hx) @exp_log
  rwa [exp_log hx] at this

/--
theorem `hasStrictDerivAt_log` / 定理 `hasStrictDerivAt_log`

English:
theorem hasStrictDerivAt_log
  given: (hx : x != 0)
  statement: HasStrictDerivAt log x⁻¹ x
  proof: by
  rcases hx.lt_or_gt with hx | hx
  · convert! (hasStrictDerivAt_log_of_pos (neg_pos.mpr hx)).comp x (hasStrictDerivAt_neg x) using 1
    · ext y; exact (log_neg_eq_log y).symm
    · ring
  · exact hasStrictDerivAt_log_of_pos hx

中文:
定理 hasStrictDerivAt_log
  条件: (hx : x != 0)
  结论: HasStrictDerivAt log x⁻¹ x
  证明: by
  rcases hx.lt_or_gt with hx | hx
  · convert! (hasStrictDerivAt_log_of_pos (neg_pos.mpr hx)).comp x (hasStrictDerivAt_neg x) using 1
    · ext y; exact (log_neg_eq_log y).symm
    · ring
  · exact hasStrictDerivAt_log_of_pos hx

Depends on / 依赖: convert, hasStrictDerivAt_log_of_pos, hasStrictDerivAt_neg, hx.lt_or_gt, log_neg_eq_log, lt_or_gt, neg_pos, neg_pos.mpr
-/
theorem hasStrictDerivAt_log (hx : x != 0) : HasStrictDerivAt log x⁻¹ x := by
  rcases hx.lt_or_gt with hx | hx
  · convert! (hasStrictDerivAt_log_of_pos (neg_pos.mpr hx)).comp x (hasStrictDerivAt_neg x) using 1
    · ext y; exact (log_neg_eq_log y).symm
    · ring
  · exact hasStrictDerivAt_log_of_pos hx

/--
theorem `hasDerivAt_log` / 定理 `hasDerivAt_log`

English:
theorem hasDerivAt_log
  given: (hx : x != 0)
  statement: HasDerivAt log x⁻¹ x
  proof: (hasStrictDerivAt_log hx).hasDerivAt

中文:
定理 hasDerivAt_log
  条件: (hx : x != 0)
  结论: 在点处可导 log x⁻¹ x
  证明: (hasStrictDerivAt_log hx).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_log
-/
theorem hasDerivAt_log (hx : x != 0) : HasDerivAt log x⁻¹ x :=
  (hasStrictDerivAt_log hx).hasDerivAt

/--
theorem `differentiableAt_log` / 定理 `differentiableAt_log`

English:
theorem differentiableAt_log
  given: (hx : x != 0)
  statement: DifferentiableAt Real log x
  proof: (hasDerivAt_log hx).differentiableAt

中文:
定理 differentiableAt_log
  条件: (hx : x != 0)
  结论: DifferentiableAt 实数 log x
  证明: (hasDerivAt_log hx).differentiableAt
-/
@[fun_prop] theorem differentiableAt_log (hx : x != 0) : DifferentiableAt Real log x :=
  (hasDerivAt_log hx).differentiableAt

/--
theorem `differentiableOn_log` / 定理 `differentiableOn_log`

English:
theorem differentiableOn_log
  statement: DifferentiableOn Real log {0}ᶜ
  proof: fun _x hx =>
  (differentiableAt_log hx).differentiableWithinAt

@[simp]

中文:
定理 differentiableOn_log
  结论: DifferentiableOn 实数 log {0}ᶜ
  证明: fun _x hx =>
  (differentiableAt_log hx).differentiableWithinAt

@[simp]
-/
theorem differentiableOn_log : DifferentiableOn Real log {0}ᶜ := fun _x hx =>
  (differentiableAt_log hx).differentiableWithinAt

@[simp]
/--
theorem `differentiableAt_log_iff` / 定理 `differentiableAt_log_iff`

English:
theorem differentiableAt_log_iff
  statement: DifferentiableAt Real log x ↔ x != 0
  proof: ⟨fun h => continuousAt_log_iff.1 h.continuousAt, differentiableAt_log⟩

中文:
定理 differentiableAt_log_iff
  结论: DifferentiableAt 实数 log x ↔ x != 0
  证明: ⟨fun h => continuousAt_log_iff.1 h.continuousAt, differentiableAt_log⟩

Depends on / 依赖: continuousAt, continuousAt_log_iff, differentiableAt_log, h.continuousAt
-/
theorem differentiableAt_log_iff : DifferentiableAt Real log x ↔ x != 0 :=
  ⟨fun h => continuousAt_log_iff.1 h.continuousAt, differentiableAt_log⟩

/--
theorem `deriv_log` / 定理 `deriv_log`

English:
theorem deriv_log
  given: (x : Real)
  statement: deriv log x = x⁻¹
  proof: if hx : x = 0 then by
    rw [deriv_zero_of_not_differentiableAt (differentiableAt_log_iff.not_left.2 hx)]; rw [hx]; rw [inv_zero]
  else (hasDerivAt_log hx).deriv

@[simp]

中文:
定理 deriv_log
  条件: (x : 实数)
  结论: deriv log x = x⁻¹
  证明: if hx : x = 0 then by
    rw [deriv_zero_of_not_differentiableAt (differentiableAt_log_iff.not_left.2 hx)]; rw [hx]; rw [inv_zero]
  else (hasDerivAt_log hx).deriv

@[simp]

Depends on / 依赖: deriv_zero_of_not_differentiableAt, differentiableAt_log_iff, differentiableAt_log_iff.not_left, hasDerivAt_log, inv_zero, not_left
-/
theorem deriv_log (x : Real) : deriv log x = x⁻¹ :=
  if hx : x = 0 then by
    rw [deriv_zero_of_not_differentiableAt (differentiableAt_log_iff.not_left.2 hx)]; rw [hx]; rw [inv_zero]
  else (hasDerivAt_log hx).deriv

@[simp]
/--
theorem `deriv_log'` / 定理 `deriv_log'`

English:
theorem deriv_log'
  statement: deriv log = Inv.inv
  proof: funext deriv_log

中文:
定理 deriv_log'
  结论: deriv log = 取逆.inv
  证明: funext deriv_log

Depends on / 依赖: deriv_log
-/
theorem deriv_log' : deriv log = Inv.inv :=
  funext deriv_log

/--
theorem `contDiffAt_log` / 定理 `contDiffAt_log`

English:
theorem contDiffAt_log
  given: {n : Nat∞ω} {x : Real}
  statement: ContDiffAt Real n log x ↔ x != 0
  proof: by
  refine ⟨fun h => continuousAt_log_iff.1 h.continuousAt, fun hx => ?_⟩
  have A y (hy : 0 < y) : ContDiffAt Real n log y := by
    apply expPartialHomeomorph.contDiffAt_symm_deriv (f₀' := y) hy.ne' (by simpa)
    · convert! hasDerivAt_exp (log y)
      rw [exp_log hy]
    · exact analyticAt_rexp.contDiffAt
  rcases hx.lt_or_gt with hx | hx
  · have : ContDiffAt Real n (log ∘ (fun y => -y)) x := by
      apply ContDiffAt.comp
      · apply A _ (Left.neg_pos_iff.mpr hx)
      apply contDiffAt_id.neg
    convert! this
    ext x
    simp
  · exact A x hx

@[fun_prop]

中文:
定理 contDiffAt_log
  条件: {n : 自然数∞ω} {x : 实数}
  结论: ContDiffAt 实数 n log x ↔ x != 0
  证明: by
  refine ⟨fun h => continuousAt_log_iff.1 h.continuousAt, fun hx => ?_⟩
  have A y (hy : 0 < y) : ContDiffAt Real n log y := by
    apply expPartialHomeomorph.contDiffAt_symm_deriv (f₀' := y) hy.ne' (by simpa)
    · convert! hasDerivAt_exp (log y)
      rw [exp_log hy]
    · exact analyticAt_rexp.contDiffAt
  rcases hx.lt_or_gt with hx | hx
  · have : ContDiffAt Real n (log ∘ (fun y => -y)) x := by
      apply ContDiffAt.comp
      · apply A _ (Left.neg_pos_iff.mpr hx)
      apply contDiffAt_id.neg
    convert! this
    ext x
    simp
  · exact A x hx

@[fun_prop]

Depends on / 依赖: ContDiffAt, ContDiffAt.comp, Left.neg_pos_iff.mpr, analyticAt_rexp, analyticAt_rexp.contDiffAt, contDiffAt, contDiffAt_id, contDiffAt_id.neg, contDiffAt_symm_deriv, continuousAt, continuousAt_log_iff, convert, expPartialHomeomorph, expPartialHomeomorph.contDiffAt_symm_deriv, exp_log, h.continuousAt, hasDerivAt_exp, hx.lt_or_gt, hy.ne, lt_or_gt
-/
theorem contDiffAt_log {n : Nat∞ω} {x : Real} : ContDiffAt Real n log x ↔ x != 0 := by
  refine ⟨fun h => continuousAt_log_iff.1 h.continuousAt, fun hx => ?_⟩
  have A y (hy : 0 < y) : ContDiffAt Real n log y := by
    apply expPartialHomeomorph.contDiffAt_symm_deriv (f₀' := y) hy.ne' (by simpa)
    · convert! hasDerivAt_exp (log y)
      rw [exp_log hy]
    · exact analyticAt_rexp.contDiffAt
  rcases hx.lt_or_gt with hx | hx
  · have : ContDiffAt Real n (log ∘ (fun y => -y)) x := by
      apply ContDiffAt.comp
      · apply A _ (Left.neg_pos_iff.mpr hx)
      apply contDiffAt_id.neg
    convert! this
    ext x
    simp
  · exact A x hx

@[fun_prop]
/--
theorem `contDiffOn_log` / 定理 `contDiffOn_log`

English:
theorem contDiffOn_log
  given: {n : Nat∞ω}
  statement: ContDiffOn Real n log {0}ᶜ
  proof: by
  intro x hx
  push _ in _ at hx
  exact (contDiffAt_log.2 hx).contDiffWithinAt

中文:
定理 contDiffOn_log
  条件: {n : 自然数∞ω}
  结论: ContDiffOn 实数 n log {0}ᶜ
  证明: by
  intro x hx
  push _ in _ at hx
  exact (contDiffAt_log.2 hx).contDiffWithinAt

Depends on / 依赖: contDiffAt_log, contDiffWithinAt
-/
theorem contDiffOn_log {n : Nat∞ω} : ContDiffOn Real n log {0}ᶜ := by
  intro x hx
  push _ in _ at hx
  exact (contDiffAt_log.2 hx).contDiffWithinAt

end Real

section LogDifferentiable

open Real

section deriv

variable {f : Real -> Real} {x f' : Real} {s : Set Real}

/--
theorem `HasDerivWithinAt.log` / 定理 `HasDerivWithinAt.log`

English:
theorem HasDerivWithinAt.log
  given: (hf : HasDerivWithinAt f f' s x) (hx : f x != 0)
  proof: by
  rw [div_eq_inv_mul]
  exact (hasDerivAt_log hx).comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.log
  条件: (hf : HasDerivWithinAt f f' s x) (hx : f x != 0)
  证明: by
  rw [div_eq_inv_mul]
  exact (hasDerivAt_log hx).comp_hasDerivWithinAt x hf

Depends on / 依赖: comp_hasDerivWithinAt, div_eq_inv_mul, hasDerivAt_log
-/
theorem HasDerivWithinAt.log (hf : HasDerivWithinAt f f' s x) (hx : f x != 0) :
    HasDerivWithinAt (fun y => log (f y)) (f' / f x) s x := by
  rw [div_eq_inv_mul]
  exact (hasDerivAt_log hx).comp_hasDerivWithinAt x hf

/--
theorem `HasDerivAt.log` / 定理 `HasDerivAt.log`

English:
theorem HasDerivAt.log
  given: (hf : HasDerivAt f f' x) (hx : f x != 0)
  proof: by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.log hx

中文:
定理 在点处可导.log
  条件: (hf : 在点处可导 f f' x) (hx : f x != 0)
  证明: by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.log hx

Depends on / 依赖: hasDerivWithinAt_univ, hf.log
-/
theorem HasDerivAt.log (hf : HasDerivAt f f' x) (hx : f x != 0) :
    HasDerivAt (fun y => log (f y)) (f' / f x) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.log hx

/--
theorem `HasStrictDerivAt.log` / 定理 `HasStrictDerivAt.log`

English:
theorem HasStrictDerivAt.log
  given: (hf : HasStrictDerivAt f f' x) (hx : f x != 0)
  proof: by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_log hx).comp x hf

中文:
定理 HasStrictDerivAt.log
  条件: (hf : HasStrictDerivAt f f' x) (hx : f x != 0)
  证明: by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_log hx).comp x hf

Depends on / 依赖: div_eq_inv_mul, hasStrictDerivAt_log
-/
theorem HasStrictDerivAt.log (hf : HasStrictDerivAt f f' x) (hx : f x != 0) :
    HasStrictDerivAt (fun y => log (f y)) (f' / f x) x := by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_log hx).comp x hf

/--
theorem `derivWithin.log` / 定理 `derivWithin.log`

English:
theorem derivWithin.log
  statement: (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0)
  proof: (hf.hasDerivWithinAt.log hx).derivWithin hxs

@[simp]

中文:
定理 derivWithin.log
  结论: (hf : DifferentiableWithinAt 实数 f s x) (hx : f x != 0)
  证明: (hf.hasDerivWithinAt.log hx).derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.log
-/
theorem derivWithin.log (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0)
    (hxs : UniqueDiffWithinAt Real s x) :
    derivWithin (fun x => log (f x)) s x = derivWithin f s x / f x :=
  (hf.hasDerivWithinAt.log hx).derivWithin hxs

@[simp]
/--
theorem `deriv.log` / 定理 `deriv.log`

English:
theorem deriv.log
  given: (hf : DifferentiableAt Real f x) (hx : f x != 0)
  proof: (hf.hasDerivAt.log hx).deriv

中文:
定理 deriv.log
  条件: (hf : DifferentiableAt 实数 f x) (hx : f x != 0)
  证明: (hf.hasDerivAt.log hx).deriv

Depends on / 依赖: hasDerivAt, hf.hasDerivAt.log
-/
theorem deriv.log (hf : DifferentiableAt Real f x) (hx : f x != 0) :
    deriv (fun x => log (f x)) x = deriv f x / f x :=
  (hf.hasDerivAt.log hx).deriv

/--
lemma `Real.deriv_log_comp_eq_logDeriv` / 引理 `Real.deriv_log_comp_eq_logDeriv`

English:
lemma Real.deriv_log_comp_eq_logDeriv
  statement: {f : Real -> Real} {x : Real} (h₁ : DifferentiableAt Real f x)
  proof: by
  simp only [logDeriv, Pi.div_apply, ← deriv.log h₁ h₂, Function.comp_def]

中文:
引理 实数.deriv_log_comp_eq_logDeriv
  结论: {f : 实数 -> 实数} {x : 实数} (h₁ : DifferentiableAt 实数 f x)
  证明: by
  simp only [logDeriv, Pi.div_apply, ← deriv.log h₁ h₂, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Pi.div_apply, comp_def, deriv.log, div_apply, logDeriv
-/
lemma Real.deriv_log_comp_eq_logDeriv {f : Real -> Real} {x : Real} (h₁ : DifferentiableAt Real f x)
    (h₂ : f x != 0) : deriv (log ∘ f) x = logDeriv f x := by
  simp only [logDeriv, Pi.div_apply, ← deriv.log h₁ h₂, Function.comp_def]

end deriv

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : E -> Real} {x : E}
  {f' : StrongDual Real E} {s : Set E}

/--
theorem `HasFDerivWithinAt.log` / 定理 `HasFDerivWithinAt.log`

English:
theorem HasFDerivWithinAt.log
  given: (hf : HasFDerivWithinAt f f' s x) (hx : f x != 0)
  proof: (hasDerivAt_log hx).comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.log
  条件: (hf : HasFDerivWithinAt f f' s x) (hx : f x != 0)
  证明: (hasDerivAt_log hx).comp_hasFDerivWithinAt x hf

Depends on / 依赖: comp_hasFDerivWithinAt, hasDerivAt_log
-/
theorem HasFDerivWithinAt.log (hf : HasFDerivWithinAt f f' s x) (hx : f x != 0) :
    HasFDerivWithinAt (fun x => log (f x)) ((f x)⁻¹ • f') s x :=
  (hasDerivAt_log hx).comp_hasFDerivWithinAt x hf

/--
theorem `HasFDerivAt.log` / 定理 `HasFDerivAt.log`

English:
theorem HasFDerivAt.log
  given: (hf : HasFDerivAt f f' x) (hx : f x != 0)
  proof: (hasDerivAt_log hx).comp_hasFDerivAt x hf

中文:
定理 在点处Fréchet可导.log
  条件: (hf : 在点处Fréchet可导 f f' x) (hx : f x != 0)
  证明: (hasDerivAt_log hx).comp_hasFDerivAt x hf

Depends on / 依赖: comp_hasFDerivAt, hasDerivAt_log
-/
theorem HasFDerivAt.log (hf : HasFDerivAt f f' x) (hx : f x != 0) :
    HasFDerivAt (fun x => log (f x)) ((f x)⁻¹ • f') x :=
  (hasDerivAt_log hx).comp_hasFDerivAt x hf

/--
theorem `HasStrictFDerivAt.log` / 定理 `HasStrictFDerivAt.log`

English:
theorem HasStrictFDerivAt.log
  given: (hf : HasStrictFDerivAt f f' x) (hx : f x != 0)
  proof: (hasStrictDerivAt_log hx).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.log
  条件: (hf : HasStrictFDerivAt f f' x) (hx : f x != 0)
  证明: (hasStrictDerivAt_log hx).comp_hasStrictFDerivAt x hf

Depends on / 依赖: comp_hasStrictFDerivAt, hasStrictDerivAt_log
-/
theorem HasStrictFDerivAt.log (hf : HasStrictFDerivAt f f' x) (hx : f x != 0) :
    HasStrictFDerivAt (fun x => log (f x)) ((f x)⁻¹ • f') x :=
  (hasStrictDerivAt_log hx).comp_hasStrictFDerivAt x hf

/--
theorem `DifferentiableWithinAt.log` / 定理 `DifferentiableWithinAt.log`

English:
theorem DifferentiableWithinAt.log
  given: (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0)
  proof: (hf.hasFDerivWithinAt.log hx).differentiableWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.log
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hx : f x != 0)
  证明: (hf.hasFDerivWithinAt.log hx).differentiableWithinAt

@[simp, fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.log
-/
theorem DifferentiableWithinAt.log (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0) :
    DifferentiableWithinAt Real (fun x => log (f x)) s x :=
  (hf.hasFDerivWithinAt.log hx).differentiableWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.log` / 定理 `DifferentiableAt.log`

English:
theorem DifferentiableAt.log
  given: (hf : DifferentiableAt Real f x) (hx : f x != 0)
  proof: (hf.hasFDerivAt.log hx).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.log
  条件: (hf : DifferentiableAt 实数 f x) (hx : f x != 0)
  证明: (hf.hasFDerivAt.log hx).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt, hf.hasFDerivAt.log
-/
theorem DifferentiableAt.log (hf : DifferentiableAt Real f x) (hx : f x != 0) :
    DifferentiableAt Real (fun x => log (f x)) x :=
  (hf.hasFDerivAt.log hx).differentiableAt

@[fun_prop]
/--
theorem `ContDiffAt.log` / 定理 `ContDiffAt.log`

English:
theorem ContDiffAt.log
  given: {n} (hf : ContDiffAt Real n f x) (hx : f x != 0)
  proof: (contDiffAt_log.2 hx).comp x hf

@[fun_prop]

中文:
定理 ContDiffAt.log
  条件: {n} (hf : ContDiffAt 实数 n f x) (hx : f x != 0)
  证明: (contDiffAt_log.2 hx).comp x hf

@[fun_prop]

Depends on / 依赖: contDiffAt_log
-/
theorem ContDiffAt.log {n} (hf : ContDiffAt Real n f x) (hx : f x != 0) :
    ContDiffAt Real n (fun x => log (f x)) x :=
  (contDiffAt_log.2 hx).comp x hf

@[fun_prop]
/--
theorem `ContDiffWithinAt.log` / 定理 `ContDiffWithinAt.log`

English:
theorem ContDiffWithinAt.log
  given: {n} (hf : ContDiffWithinAt Real n f s x) (hx : f x != 0)
  proof: (contDiffAt_log.2 hx).comp_contDiffWithinAt x hf

@[fun_prop]

中文:
定理 ContDiffWithinAt.log
  条件: {n} (hf : ContDiffWithinAt 实数 n f s x) (hx : f x != 0)
  证明: (contDiffAt_log.2 hx).comp_contDiffWithinAt x hf

@[fun_prop]

Depends on / 依赖: comp_contDiffWithinAt, contDiffAt_log
-/
theorem ContDiffWithinAt.log {n} (hf : ContDiffWithinAt Real n f s x) (hx : f x != 0) :
    ContDiffWithinAt Real n (fun x => log (f x)) s x :=
  (contDiffAt_log.2 hx).comp_contDiffWithinAt x hf

@[fun_prop]
/--
theorem `ContDiffOn.log` / 定理 `ContDiffOn.log`

English:
theorem ContDiffOn.log
  given: {n} (hf : ContDiffOn Real n f s) (hs : forall x in s, f x != 0)
  proof: fun x hx => (hf x hx).log (hs x hx)

@[fun_prop]

中文:
定理 ContDiffOn.log
  条件: {n} (hf : ContDiffOn 实数 n f s) (hs : 对任意 x in s, f x != 0)
  证明: fun x hx => (hf x hx).log (hs x hx)

@[fun_prop]
-/
theorem ContDiffOn.log {n} (hf : ContDiffOn Real n f s) (hs : forall x in s, f x != 0) :
    ContDiffOn Real n (fun x => log (f x)) s := fun x hx => (hf x hx).log (hs x hx)

@[fun_prop]
/--
theorem `ContDiff.log` / 定理 `ContDiff.log`

English:
theorem ContDiff.log
  given: {n} (hf : ContDiff Real n f) (h : forall x, f x != 0)
  proof: contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.log (h x)

@[fun_prop]

中文:
定理 连续可微.log
  条件: {n} (hf : 连续可微 实数 n f) (h : 对任意 x, f x != 0)
  证明: contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.log (h x)

@[fun_prop]

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, hf.contDiffAt.log
-/
theorem ContDiff.log {n} (hf : ContDiff Real n f) (h : forall x, f x != 0) :
    ContDiff Real n fun x => log (f x) :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.log (h x)

@[fun_prop]
/--
theorem `DifferentiableOn.log` / 定理 `DifferentiableOn.log`

English:
theorem DifferentiableOn.log
  given: (hf : DifferentiableOn Real f s) (hx : forall x in s, f x != 0)
  proof: fun x h => (hf x h).log (hx x h)

@[simp, fun_prop]

中文:
定理 DifferentiableOn.log
  条件: (hf : DifferentiableOn 实数 f s) (hx : 对任意 x in s, f x != 0)
  证明: fun x h => (hf x h).log (hx x h)

@[simp, fun_prop]

Depends on / 依赖: Hom.of
-/
theorem DifferentiableOn.log (hf : DifferentiableOn Real f s) (hx : forall x in s, f x != 0) :
    DifferentiableOn Real (fun x => log (f x)) s := fun x h => (hf x h).log (hx x h)

@[simp, fun_prop]
/--
theorem `Differentiable.log` / 定理 `Differentiable.log`

English:
theorem Differentiable.log
  given: (hf : Differentiable Real f) (hx : forall x, f x != 0)
  proof: fun x => (hf x).log (hx x)

中文:
定理 可微.log
  条件: (hf : 可微 实数 f) (hx : 对任意 x, f x != 0)
  证明: fun x => (hf x).log (hx x)
-/
theorem Differentiable.log (hf : Differentiable Real f) (hx : forall x, f x != 0) :
    Differentiable Real fun x => log (f x) := fun x => (hf x).log (hx x)

/--
theorem `fderivWithin.log` / 定理 `fderivWithin.log`

English:
theorem fderivWithin.log
  statement: (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0)
  proof: (hf.hasFDerivWithinAt.log hx).fderivWithin hxs

@[simp]

中文:
定理 fderivWithin.log
  结论: (hf : DifferentiableWithinAt 实数 f s x) (hx : f x != 0)
  证明: (hf.hasFDerivWithinAt.log hx).fderivWithin hxs

@[simp]

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.log
-/
theorem fderivWithin.log (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0)
    (hxs : UniqueDiffWithinAt Real s x) :
    fderivWithin Real (fun x => log (f x)) s x = (f x)⁻¹ • fderivWithin Real f s x :=
  (hf.hasFDerivWithinAt.log hx).fderivWithin hxs

@[simp]
/--
theorem `fderiv.log` / 定理 `fderiv.log`

English:
theorem fderiv.log
  given: (hf : DifferentiableAt Real f x) (hx : f x != 0)
  proof: (hf.hasFDerivAt.log hx).fderiv

中文:
定理 fderiv.log
  条件: (hf : DifferentiableAt 实数 f x) (hx : f x != 0)
  证明: (hf.hasFDerivAt.log hx).fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hf.hasFDerivAt.log
-/
theorem fderiv.log (hf : DifferentiableAt Real f x) (hx : f x != 0) :
    fderiv Real (fun x => log (f x)) x = (f x)⁻¹ • fderiv Real f x :=
  (hf.hasFDerivAt.log hx).fderiv

end fderiv

end LogDifferentiable

namespace Real

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/--
theorem `abs_log_sub_add_sum_range_le` / 定理 `abs_log_sub_add_sum_range_le`

English:
theorem abs_log_sub_add_sum_range_le
  given: {x : Real} (h : |x| < 1) (n : Nat)
  proof: by
  /- For the proof, we show that the derivative of the function to be estimated is small,
    and then apply the mean value inequality. -/
  let F : Real -> Real := fun x => (∑ i in range n, x ^ (i + 1) / (i + 1)) + log (1 - x)
  let F' : Real -> Real := fun x => -x ^ n / (1 - x)
  -- Porting note: In `mathlib3`, the proof used `deriv`/`DifferentiableAt`. `simp` failed to
  -- compute `deriv`, so I changed the proof to use `HasDerivAt` instead
  -- First step: compute the derivative of `F`
  have A : forall y in Ioo (-1 : Real) 1, HasDerivAt F (F' y) y := fun y hy => by
    have : HasDerivAt F ((∑ i in range n, ↑(i + 1) * y ^ i / (↑i + 1)) + (-1) / (1 - y)) y :=
      .add (.fun_sum fun i _ => (hasDerivAt_pow (i + 1) y).div_const ((i : Real) + 1))
        (((hasDerivAt_id y).const_sub _).log <| sub_ne_zero.2 hy.2.ne')
    convert! this using 1
    calc
      -y ^ n / (1 - y) = ∑ i in Finset.range n, y ^ i + -1 / (1 - y) := by
        simp [field, geom_sum_eq hy.2.ne, sub_ne_zero.2 hy.2.ne, sub_ne_zero.2 hy.2.ne']
        ring
      _ = ∑ i in Finset.range n, ↑(i + 1) * y ^ i / (↑i + 1) + -1 / (1 - y) := by
        congr with i
        rw [Nat.cast_succ]; rw [mul_div_cancel_left₀ _ (Nat.cast_add_one_pos i).ne']
  -- second step: show that the derivative of `F` is small
  have B : forall y in Icc (-|x|) |x|, |F' y| <= |x| ^ n / (1 - |x|) := fun y hy =>
    calc
      |F' y| = |y| ^ n / |1 - y| := by simp [F', abs_div]
      _ <= |x| ^ n / (1 - |x|) := by
        have : |y| <= |x| := abs_le.2 hy
        have : 1 - |x| <= |1 - y| := le_trans (by linarith [hy.2]) (le_abs_self _)
        gcongr
  -- third step: apply the mean value inequality
  have C : ‖F x - F 0‖ <= |x| ^ n / (1 - |x|) * ‖x - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (A _ ?_).hasDerivWithinAt) B (convex_Icc _ _) ?_ ?_
    · exact Icc_subset_Ioo (neg_lt_neg h) h hy
    · simp
    · simp [le_abs_self x, neg_le.mp (neg_le_abs x)]
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [F, div_mul_eq_mul_div, pow_succ] using C

中文:
定理 abs_log_sub_add_sum_range_le
  条件: {x : 实数} (h : |x| < 1) (n : 自然数)
  证明: by
  /- For the proof, we show that the derivative of the function to be estimated is small,
    and then apply the mean value inequality. -/
  let F : Real -> Real := fun x => (∑ i in range n, x ^ (i + 1) / (i + 1)) + log (1 - x)
  let F' : Real -> Real := fun x => -x ^ n / (1 - x)
  -- Porting note: In `mathlib3`, the proof used `deriv`/`DifferentiableAt`. `simp` failed to
  -- compute `deriv`, so I changed the proof to use `HasDerivAt` instead
  -- First step: compute the derivative of `F`
  have A : forall y in Ioo (-1 : Real) 1, HasDerivAt F (F' y) y := fun y hy => by
    have : HasDerivAt F ((∑ i in range n, ↑(i + 1) * y ^ i / (↑i + 1)) + (-1) / (1 - y)) y :=
      .add (.fun_sum fun i _ => (hasDerivAt_pow (i + 1) y).div_const ((i : Real) + 1))
        (((hasDerivAt_id y).const_sub _).log <| sub_ne_zero.2 hy.2.ne')
    convert! this using 1
    calc
      -y ^ n / (1 - y) = ∑ i in Finset.range n, y ^ i + -1 / (1 - y) := by
        simp [field, geom_sum_eq hy.2.ne, sub_ne_zero.2 hy.2.ne, sub_ne_zero.2 hy.2.ne']
        ring
      _ = ∑ i in Finset.range n, ↑(i + 1) * y ^ i / (↑i + 1) + -1 / (1 - y) := by
        congr with i
        rw [Nat.cast_succ]; rw [mul_div_cancel_left₀ _ (Nat.cast_add_one_pos i).ne']
  -- second step: show that the derivative of `F` is small
  have B : forall y in Icc (-|x|) |x|, |F' y| <= |x| ^ n / (1 - |x|) := fun y hy =>
    calc
      |F' y| = |y| ^ n / |1 - y| := by simp [F', abs_div]
      _ <= |x| ^ n / (1 - |x|) := by
        have : |y| <= |x| := abs_le.2 hy
        have : 1 - |x| <= |1 - y| := le_trans (by linarith [hy.2]) (le_abs_self _)
        gcongr
  -- third step: apply the mean value inequality
  have C : ‖F x - F 0‖ <= |x| ^ n / (1 - |x|) * ‖x - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (A _ ?_).hasDerivWithinAt) B (convex_Icc _ _) ?_ ?_
    · exact Icc_subset_Ioo (neg_lt_neg h) h hy
    · simp
    · simp [le_abs_self x, neg_le.mp (neg_le_abs x)]
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [F, div_mul_eq_mul_div, pow_succ] using C
-/
theorem abs_log_sub_add_sum_range_le {x : Real} (h : |x| < 1) (n : Nat) :
    |(∑ i in range n, x ^ (i + 1) / (i + 1)) + log (1 - x)| <= |x| ^ (n + 1) / (1 - |x|) := by
  /- For the proof, we show that the derivative of the function to be estimated is small,
    and then apply the mean value inequality. -/
  let F : Real -> Real := fun x => (∑ i in range n, x ^ (i + 1) / (i + 1)) + log (1 - x)
  let F' : Real -> Real := fun x => -x ^ n / (1 - x)
  -- Porting note: In `mathlib3`, the proof used `deriv`/`DifferentiableAt`. `simp` failed to
  -- compute `deriv`, so I changed the proof to use `HasDerivAt` instead
  -- First step: compute the derivative of `F`
  have A : forall y in Ioo (-1 : Real) 1, HasDerivAt F (F' y) y := fun y hy => by
    have : HasDerivAt F ((∑ i in range n, ↑(i + 1) * y ^ i / (↑i + 1)) + (-1) / (1 - y)) y :=
      .add (.fun_sum fun i _ => (hasDerivAt_pow (i + 1) y).div_const ((i : Real) + 1))
        (((hasDerivAt_id y).const_sub _).log <| sub_ne_zero.2 hy.2.ne')
    convert! this using 1
    calc
      -y ^ n / (1 - y) = ∑ i in Finset.range n, y ^ i + -1 / (1 - y) := by
        simp [field, geom_sum_eq hy.2.ne, sub_ne_zero.2 hy.2.ne, sub_ne_zero.2 hy.2.ne']
        ring
      _ = ∑ i in Finset.range n, ↑(i + 1) * y ^ i / (↑i + 1) + -1 / (1 - y) := by
        congr with i
        rw [Nat.cast_succ]; rw [mul_div_cancel_left₀ _ (Nat.cast_add_one_pos i).ne']
  -- second step: show that the derivative of `F` is small
  have B : forall y in Icc (-|x|) |x|, |F' y| <= |x| ^ n / (1 - |x|) := fun y hy =>
    calc
      |F' y| = |y| ^ n / |1 - y| := by simp [F', abs_div]
      _ <= |x| ^ n / (1 - |x|) := by
        have : |y| <= |x| := abs_le.2 hy
        have : 1 - |x| <= |1 - y| := le_trans (by linarith [hy.2]) (le_abs_self _)
        gcongr
  -- third step: apply the mean value inequality
  have C : ‖F x - F 0‖ <= |x| ^ n / (1 - |x|) * ‖x - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (A _ ?_).hasDerivWithinAt) B (convex_Icc _ _) ?_ ?_
    · exact Icc_subset_Ioo (neg_lt_neg h) h hy
    · simp
    · simp [le_abs_self x, neg_le.mp (neg_le_abs x)]
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [F, div_mul_eq_mul_div, pow_succ] using C

/--
lemma `hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range` / 引理 `hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range`

English:
lemma hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
  proof: by
  refine ((((((hasDerivAt_id _).const_add _).div ((hasDerivAt_id _).const_sub _) (by grind)).log
          ?_).const_mul _).sub (HasDerivAt.fun_sum fun i hi => (hasDerivAt_pow _ _).div_const _))
.congr_deriv ?_
  · simp only [div_ne_zero_iff, Pi.div_apply]; grind
  have : (∑ i in range n, (2 * i + 1) * y ^ (2 * i) / (2 * i + 1)) =
      (∑ i in range n, (y ^ 2) ^ i) := by
    congr with i
    simp [field, mul_comm, ← pow_mul]
  have hy₃ : y ^ 2 != 1 := by simp [hy₁.ne', hy₂.ne]
  have hy₄ : (1 - y) * (1 + y) = 1 - y ^ 2 := by ring
  simp [this, field, geom_sum_eq hy₃, hy₄]
  ring

中文:
引理 hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
  证明: by
  refine ((((((hasDerivAt_id _).const_add _).div ((hasDerivAt_id _).const_sub _) (by grind)).log
          ?_).const_mul _).sub (HasDerivAt.fun_sum fun i hi => (hasDerivAt_pow _ _).div_const _))
.congr_deriv ?_
  · simp only [div_ne_zero_iff, Pi.div_apply]; grind
  have : (∑ i in range n, (2 * i + 1) * y ^ (2 * i) / (2 * i + 1)) =
      (∑ i in range n, (y ^ 2) ^ i) := by
    congr with i
    simp [field, mul_comm, ← pow_mul]
  have hy₃ : y ^ 2 != 1 := by simp [hy₁.ne', hy₂.ne]
  have hy₄ : (1 - y) * (1 + y) = 1 - y ^ 2 := by ring
  simp [this, field, geom_sum_eq hy₃, hy₄]
  ring

Depends on / 依赖: HasDerivAt, HasDerivAt.fun_sum, Pi.div_apply, congr_deriv, const_add, const_mul, const_sub, div_apply, div_const, div_ne_zero_iff, fun_sum, hasDerivAt_id, hasDerivAt_pow, mul_comm, pow_mul
-/
lemma hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
    {y : Real} (n : Nat) (hy₁ : -1 < y) (hy₂ : y < 1) :
    HasDerivAt
      (fun x => 1 / 2 * log ((1 + x) / (1 - x)) - (∑ i in range n, x ^ (2 * i + 1) / (2 * i + 1)))
      ((y ^ 2) ^ n / (1 - y ^ 2)) y := by
  refine ((((((hasDerivAt_id _).const_add _).div ((hasDerivAt_id _).const_sub _) (by grind)).log
          ?_).const_mul _).sub (HasDerivAt.fun_sum fun i hi => (hasDerivAt_pow _ _).div_const _))
.congr_deriv ?_
  · simp only [div_ne_zero_iff, Pi.div_apply]; grind
  have : (∑ i in range n, (2 * i + 1) * y ^ (2 * i) / (2 * i + 1)) =
      (∑ i in range n, (y ^ 2) ^ i) := by
    congr with i
    simp [field, mul_comm, ← pow_mul]
  have hy₃ : y ^ 2 != 1 := by simp [hy₁.ne', hy₂.ne]
  have hy₄ : (1 - y) * (1 + y) = 1 - y ^ 2 := by ring
  simp [this, field, geom_sum_eq hy₃, hy₄]
  ring

/--
lemma `sum_range_sub_log_div_le` / 引理 `sum_range_sub_log_div_le`

English:
lemma sum_range_sub_log_div_le
  given: {x : Real} (h : |x| < 1) (n : Nat)
  proof: by
  let F (x : Real) : Real :=
    1 / 2 * log ((1 + x) / (1 - x)) - (∑ i in range n, x ^ (2 * i + 1) / (2 * i + 1))
  let F' (y : Real) : Real := (y ^ 2) ^ n / (1 - y ^ 2)
  have hI : Icc (-|x|) |x| subseteq Ioo (-1 : Real) 1 := Icc_subset_Ioo (by simp [h]) h
  -- First step: compute the derivative of `F`
  have A : forall y in Ioo (-1 : Real) 1, HasDerivAt F (F' y) y := by
    intro y hy
    exact hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range _ (by grind) (by grind)
  -- second step: show that the derivative of `F` is small
  have B : forall y in Set.Icc (-|x|) |x|, ‖F' y‖ <= |x| ^ (2 * n) / (1 - x ^ 2) := fun y hy => by
    have : y ^ 2 <= x ^ 2 := sq_le_sq.2 (abs_le.2 hy)
    calc
      ‖F' y‖ = (y ^ 2) ^ n / |1 - y ^ 2| := by simp [F']
      _ = (y ^ 2) ^ n / (1 - y ^ 2) := by rw [abs_of_pos (by simpa [abs_lt] using hI hy)]
      _ <= (x ^ 2) ^ n / (1 - x ^ 2) := by gcongr ?_ ^ n / (1 - ?_); simpa [abs_lt] using h
      _ <= |x| ^ (2 * n) / (1 - x ^ 2) := by simp [pow_mul]
  -- third step: apply the mean value inequality
  have C : ‖F x - F 0‖ <= |x| ^ (2 * n) / (1 - x ^ 2) * ‖x - 0‖ :=
    (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (A _ (hI hy)).hasDerivWithinAt) B
      (by simp) (by simp [le_abs_self, neg_le, neg_le_abs x])
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [F, pow_succ, div_mul_eq_mul_div] using C

中文:
引理 sum_range_sub_log_div_le
  条件: {x : 实数} (h : |x| < 1) (n : 自然数)
  证明: by
  let F (x : Real) : Real :=
    1 / 2 * log ((1 + x) / (1 - x)) - (∑ i in range n, x ^ (2 * i + 1) / (2 * i + 1))
  let F' (y : Real) : Real := (y ^ 2) ^ n / (1 - y ^ 2)
  have hI : Icc (-|x|) |x| subseteq Ioo (-1 : Real) 1 := Icc_subset_Ioo (by simp [h]) h
  -- First step: compute the derivative of `F`
  have A : forall y in Ioo (-1 : Real) 1, HasDerivAt F (F' y) y := by
    intro y hy
    exact hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range _ (by grind) (by grind)
  -- second step: show that the derivative of `F` is small
  have B : forall y in Set.Icc (-|x|) |x|, ‖F' y‖ <= |x| ^ (2 * n) / (1 - x ^ 2) := fun y hy => by
    have : y ^ 2 <= x ^ 2 := sq_le_sq.2 (abs_le.2 hy)
    calc
      ‖F' y‖ = (y ^ 2) ^ n / |1 - y ^ 2| := by simp [F']
      _ = (y ^ 2) ^ n / (1 - y ^ 2) := by rw [abs_of_pos (by simpa [abs_lt] using hI hy)]
      _ <= (x ^ 2) ^ n / (1 - x ^ 2) := by gcongr ?_ ^ n / (1 - ?_); simpa [abs_lt] using h
      _ <= |x| ^ (2 * n) / (1 - x ^ 2) := by simp [pow_mul]
  -- third step: apply the mean value inequality
  have C : ‖F x - F 0‖ <= |x| ^ (2 * n) / (1 - x ^ 2) * ‖x - 0‖ :=
    (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (A _ (hI hy)).hasDerivWithinAt) B
      (by simp) (by simp [le_abs_self, neg_le, neg_le_abs x])
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [F, pow_succ, div_mul_eq_mul_div] using C

Depends on / 依赖: Icc_subset_Ioo, subseteq
-/
lemma sum_range_sub_log_div_le {x : Real} (h : |x| < 1) (n : Nat) :
    |1 / 2 * log ((1 + x) / (1 - x)) - ∑ i in range n, x ^ (2 * i + 1) / (2 * i + 1)| <=
      |x| ^ (2 * n + 1) / (1 - x ^ 2) := by
  let F (x : Real) : Real :=
    1 / 2 * log ((1 + x) / (1 - x)) - (∑ i in range n, x ^ (2 * i + 1) / (2 * i + 1))
  let F' (y : Real) : Real := (y ^ 2) ^ n / (1 - y ^ 2)
  have hI : Icc (-|x|) |x| subseteq Ioo (-1 : Real) 1 := Icc_subset_Ioo (by simp [h]) h
  -- First step: compute the derivative of `F`
  have A : forall y in Ioo (-1 : Real) 1, HasDerivAt F (F' y) y := by
    intro y hy
    exact hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range _ (by grind) (by grind)
  -- second step: show that the derivative of `F` is small
  have B : forall y in Set.Icc (-|x|) |x|, ‖F' y‖ <= |x| ^ (2 * n) / (1 - x ^ 2) := fun y hy => by
    have : y ^ 2 <= x ^ 2 := sq_le_sq.2 (abs_le.2 hy)
    calc
      ‖F' y‖ = (y ^ 2) ^ n / |1 - y ^ 2| := by simp [F']
      _ = (y ^ 2) ^ n / (1 - y ^ 2) := by rw [abs_of_pos (by simpa [abs_lt] using hI hy)]
      _ <= (x ^ 2) ^ n / (1 - x ^ 2) := by gcongr ?_ ^ n / (1 - ?_); simpa [abs_lt] using h
      _ <= |x| ^ (2 * n) / (1 - x ^ 2) := by simp [pow_mul]
  -- third step: apply the mean value inequality
  have C : ‖F x - F 0‖ <= |x| ^ (2 * n) / (1 - x ^ 2) * ‖x - 0‖ :=
    (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (A _ (hI hy)).hasDerivWithinAt) B
      (by simp) (by simp [le_abs_self, neg_le, neg_le_abs x])
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [F, pow_succ, div_mul_eq_mul_div] using C

/--
lemma `sum_range_le_log_div` / 引理 `sum_range_le_log_div`

English:
lemma sum_range_le_log_div
  given: {x : Real} (h₀ : 0 <= x) (h : x < 1) (n : Nat)
  proof: by
  let F (x : Real) : Real :=
    1 / 2 * log ((1 + x) / (1 - x)) - (∑ i in range n, x ^ (2 * i + 1) / (2 * i + 1))
  let F' (y : Real) : Real := (y ^ 2) ^ n / (1 - y ^ 2)
  -- First step: compute the derivative of `F`
  have A : forall y in Icc 0 x, HasDerivAt F (F' y) y := by
    intro y hy
    exact hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range _ (by grind) (by grind)
  -- It suffices to show that `F` is monotone on `[0, x]`
  suffices MonotoneOn F (Icc 0 x) by simpa [F] using this ⟨le_rfl, h₀⟩ ⟨h₀, le_rfl⟩ h₀
  -- Second step: show that the derivative of `F` is nonnegative; it has been computed already.
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
    (fun y hy => (A y hy).continuousAt.continuousWithinAt)
    (fun y hy => (A y (interior_subset hy)).hasDerivWithinAt) ?_
  intro y hy
  simp only [interior_Icc, Set.mem_Ioo] at hy
  have : 0 <= 1 - y ^ 2 := by calc
    0 <= 1 - x ^ 2 := by simp [abs_of_nonneg h₀, h.le]
    _ <= 1 - y ^ 2 := sub_le_sub_left (pow_le_pow_left₀ hy.1.le hy.2.le 2) 1
  positivity

中文:
引理 sum_range_le_log_div
  条件: {x : 实数} (h₀ : 0 <= x) (h : x < 1) (n : 自然数)
  证明: by
  let F (x : Real) : Real :=
    1 / 2 * log ((1 + x) / (1 - x)) - (∑ i in range n, x ^ (2 * i + 1) / (2 * i + 1))
  let F' (y : Real) : Real := (y ^ 2) ^ n / (1 - y ^ 2)
  -- First step: compute the derivative of `F`
  have A : forall y in Icc 0 x, HasDerivAt F (F' y) y := by
    intro y hy
    exact hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range _ (by grind) (by grind)
  -- It suffices to show that `F` is monotone on `[0, x]`
  suffices MonotoneOn F (Icc 0 x) by simpa [F] using this ⟨le_rfl, h₀⟩ ⟨h₀, le_rfl⟩ h₀
  -- Second step: show that the derivative of `F` is nonnegative; it has been computed already.
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
    (fun y hy => (A y hy).continuousAt.continuousWithinAt)
    (fun y hy => (A y (interior_subset hy)).hasDerivWithinAt) ?_
  intro y hy
  simp only [interior_Icc, Set.mem_Ioo] at hy
  have : 0 <= 1 - y ^ 2 := by calc
    0 <= 1 - x ^ 2 := by simp [abs_of_nonneg h₀, h.le]
    _ <= 1 - y ^ 2 := sub_le_sub_left (pow_le_pow_left₀ hy.1.le hy.2.le 2) 1
  positivity
-/
lemma sum_range_le_log_div {x : Real} (h₀ : 0 <= x) (h : x < 1) (n : Nat) :
    ∑ i in range n, x ^ (2 * i + 1) / (2 * i + 1) <= 1 / 2 * log ((1 + x) / (1 - x)) := by
  let F (x : Real) : Real :=
    1 / 2 * log ((1 + x) / (1 - x)) - (∑ i in range n, x ^ (2 * i + 1) / (2 * i + 1))
  let F' (y : Real) : Real := (y ^ 2) ^ n / (1 - y ^ 2)
  -- First step: compute the derivative of `F`
  have A : forall y in Icc 0 x, HasDerivAt F (F' y) y := by
    intro y hy
    exact hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range _ (by grind) (by grind)
  -- It suffices to show that `F` is monotone on `[0, x]`
  suffices MonotoneOn F (Icc 0 x) by simpa [F] using this ⟨le_rfl, h₀⟩ ⟨h₀, le_rfl⟩ h₀
  -- Second step: show that the derivative of `F` is nonnegative; it has been computed already.
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
    (fun y hy => (A y hy).continuousAt.continuousWithinAt)
    (fun y hy => (A y (interior_subset hy)).hasDerivWithinAt) ?_
  intro y hy
  simp only [interior_Icc, Set.mem_Ioo] at hy
  have : 0 <= 1 - y ^ 2 := by calc
    0 <= 1 - x ^ 2 := by simp [abs_of_nonneg h₀, h.le]
    _ <= 1 - y ^ 2 := sub_le_sub_left (pow_le_pow_left₀ hy.1.le hy.2.le 2) 1
  positivity

/--
lemma `log_div_le_sum_range_add` / 引理 `log_div_le_sum_range_add`

English:
lemma log_div_le_sum_range_add
  given: {x : Real} (h₀ : 0 <= x) (h : x < 1) (n : Nat)
  proof: by
  have h₁ := sum_range_sub_log_div_le (by rwa [abs_of_nonneg h₀]) n
  rwa [abs_of_nonneg (sub_nonneg_of_le (sum_range_le_log_div h₀ h n)), abs_of_nonneg h₀,
    sub_le_iff_le_add'] at h₁

中文:
引理 log_div_le_sum_range_add
  条件: {x : 实数} (h₀ : 0 <= x) (h : x < 1) (n : 自然数)
  证明: by
  have h₁ := sum_range_sub_log_div_le (by rwa [abs_of_nonneg h₀]) n
  rwa [abs_of_nonneg (sub_nonneg_of_le (sum_range_le_log_div h₀ h n)), abs_of_nonneg h₀,
    sub_le_iff_le_add'] at h₁

Depends on / 依赖: abs_of_nonneg, sub_le_iff_le_add, sub_nonneg_of_le, sum_range_le_log_div, sum_range_sub_log_div_le
-/
lemma log_div_le_sum_range_add {x : Real} (h₀ : 0 <= x) (h : x < 1) (n : Nat) :
    1 / 2 * log ((1 + x) / (1 - x)) <=
      (∑ i in range n, x ^ (2 * i + 1) / (2 * i + 1)) + x ^ (2 * n + 1) / (1 - x ^ 2) := by
  have h₁ := sum_range_sub_log_div_le (by rwa [abs_of_nonneg h₀]) n
  rwa [abs_of_nonneg (sub_nonneg_of_le (sum_range_le_log_div h₀ h n)), abs_of_nonneg h₀,
    sub_le_iff_le_add'] at h₁

/--
theorem `hasSum_pow_div_log_of_abs_lt_one` / 定理 `hasSum_pow_div_log_of_abs_lt_one`

English:
theorem hasSum_pow_div_log_of_abs_lt_one
  given: {x : Real} (h : |x| < 1)
  proof: by
  rw [Summable.hasSum_iff_tendsto_nat]
  · show Tendsto (fun n : Nat => ∑ i in range n, x ^ (i + 1) / (i + 1)) atTop (𝓝 (-log (1 - x)))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [norm_eq_abs, sub_neg_eq_add]
    refine squeeze_zero (fun n => abs_nonneg _) (abs_log_sub_add_sum_range_le h) ?_
    suffices Tendsto (fun t : Nat => |x| ^ (t + 1) / (1 - |x|)) atTop (𝓝 (|x| * 0 / (1 - |x|))) by
      simpa
    simp only [pow_succ']
    refine (tendsto_const_nhds.mul ?_).div_const _
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) h
  show Summable fun n : Nat => x ^ (n + 1) / (n + 1)
  refine .of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg _) h) fun i => ?_
  calc
    ‖x ^ (i + 1) / (i + 1)‖ = |x| ^ (i + 1) / (i + 1) := by
      have : (0 : Real) <= i + 1 := le_of_lt (Nat.cast_add_one_pos i)
      rw [norm_eq_abs]; rw [abs_div]; rw [← pow_abs]; rw [abs_of_nonneg this]
    _ <= |x| ^ (i + 1) / (0 + 1) := by
      gcongr
      positivity
    _ <= |x| ^ i := by
      simpa [pow_succ] using mul_le_of_le_one_right (by positivity) h.le

中文:
定理 hasSum_pow_div_log_of_abs_lt_one
  条件: {x : 实数} (h : |x| < 1)
  证明: by
  rw [Summable.hasSum_iff_tendsto_nat]
  · show Tendsto (fun n : Nat => ∑ i in range n, x ^ (i + 1) / (i + 1)) atTop (𝓝 (-log (1 - x)))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [norm_eq_abs, sub_neg_eq_add]
    refine squeeze_zero (fun n => abs_nonneg _) (abs_log_sub_add_sum_range_le h) ?_
    suffices Tendsto (fun t : Nat => |x| ^ (t + 1) / (1 - |x|)) atTop (𝓝 (|x| * 0 / (1 - |x|))) by
      simpa
    simp only [pow_succ']
    refine (tendsto_const_nhds.mul ?_).div_const _
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) h
  show Summable fun n : Nat => x ^ (n + 1) / (n + 1)
  refine .of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg _) h) fun i => ?_
  calc
    ‖x ^ (i + 1) / (i + 1)‖ = |x| ^ (i + 1) / (i + 1) := by
      have : (0 : Real) <= i + 1 := le_of_lt (Nat.cast_add_one_pos i)
      rw [norm_eq_abs]; rw [abs_div]; rw [← pow_abs]; rw [abs_of_nonneg this]
    _ <= |x| ^ (i + 1) / (0 + 1) := by
      gcongr
      positivity
    _ <= |x| ^ i := by
      simpa [pow_succ] using mul_le_of_le_one_right (by positivity) h.le

Depends on / 依赖: Summable, Summable.hasSum_iff_tendsto_nat, Tendsto, abs_log_sub_add_sum_range_le, abs_nonneg, div_const, hasSum_iff_tendsto_nat, norm_eq_abs, pow_succ, squeeze_zero, sub_neg_eq_add, tendsto_const_nhds, tendsto_const_nhds.mul, tendsto_iff_norm_sub_tendsto_zero, tendsto_pow_atTop_nhds_zero_of
-/
theorem hasSum_pow_div_log_of_abs_lt_one {x : Real} (h : |x| < 1) :
    HasSum (fun n : Nat => x ^ (n + 1) / (n + 1)) (-log (1 - x)) := by
  rw [Summable.hasSum_iff_tendsto_nat]
  · show Tendsto (fun n : Nat => ∑ i in range n, x ^ (i + 1) / (i + 1)) atTop (𝓝 (-log (1 - x)))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [norm_eq_abs, sub_neg_eq_add]
    refine squeeze_zero (fun n => abs_nonneg _) (abs_log_sub_add_sum_range_le h) ?_
    suffices Tendsto (fun t : Nat => |x| ^ (t + 1) / (1 - |x|)) atTop (𝓝 (|x| * 0 / (1 - |x|))) by
      simpa
    simp only [pow_succ']
    refine (tendsto_const_nhds.mul ?_).div_const _
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) h
  show Summable fun n : Nat => x ^ (n + 1) / (n + 1)
  refine .of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg _) h) fun i => ?_
  calc
    ‖x ^ (i + 1) / (i + 1)‖ = |x| ^ (i + 1) / (i + 1) := by
      have : (0 : Real) <= i + 1 := le_of_lt (Nat.cast_add_one_pos i)
      rw [norm_eq_abs]; rw [abs_div]; rw [← pow_abs]; rw [abs_of_nonneg this]
    _ <= |x| ^ (i + 1) / (0 + 1) := by
      gcongr
      positivity
    _ <= |x| ^ i := by
      simpa [pow_succ] using mul_le_of_le_one_right (by positivity) h.le

/--
theorem `hasSum_log_sub_log_of_abs_lt_one` / 定理 `hasSum_log_sub_log_of_abs_lt_one`

English:
theorem hasSum_log_sub_log_of_abs_lt_one
  given: {x : Real} (h : |x| < 1)
  proof: by
  set term := fun n : Nat => -1 * ((-x) ^ (n + 1) / ((n : Real) + 1)) + x ^ (n + 1) / (n + 1)
  have h_term_eq_goal :
      term ∘ (2 * ·) = fun k : Nat => 2 * (1 / (2 * k + 1)) * x ^ (2 * k + 1) := by
    ext n
    dsimp only [term, (· ∘ ·)]
    rw [Odd.neg_pow (⟨n]; rw [rfl⟩ : Odd (2 * n + 1)) x]
    push_cast
    ring_nf
  rw [← h_term_eq_goal]; rw [(mul_right_injective₀ (two_ne_zero' Nat)).hasSum_iff]
  · have h₁ := (hasSum_pow_div_log_of_abs_lt_one (Eq.trans_lt (abs_neg x) h)).mul_left (-1)
    convert! h₁.add (hasSum_pow_div_log_of_abs_lt_one h) using 1
    ring_nf
  · intro m hm
    rw [range_two_mul]; rw [Set.mem_ofPred_eq]; rw [← Nat.even_add_one] at hm
    dsimp [term]
    rw [Even.neg_pow hm]; rw [neg_one_mul]; rw [neg_add_cancel]

中文:
定理 hasSum_log_sub_log_of_abs_lt_one
  条件: {x : 实数} (h : |x| < 1)
  证明: by
  set term := fun n : Nat => -1 * ((-x) ^ (n + 1) / ((n : Real) + 1)) + x ^ (n + 1) / (n + 1)
  have h_term_eq_goal :
      term ∘ (2 * ·) = fun k : Nat => 2 * (1 / (2 * k + 1)) * x ^ (2 * k + 1) := by
    ext n
    dsimp only [term, (· ∘ ·)]
    rw [Odd.neg_pow (⟨n]; rw [rfl⟩ : Odd (2 * n + 1)) x]
    push_cast
    ring_nf
  rw [← h_term_eq_goal]; rw [(mul_right_injective₀ (two_ne_zero' Nat)).hasSum_iff]
  · have h₁ := (hasSum_pow_div_log_of_abs_lt_one (Eq.trans_lt (abs_neg x) h)).mul_left (-1)
    convert! h₁.add (hasSum_pow_div_log_of_abs_lt_one h) using 1
    ring_nf
  · intro m hm
    rw [range_two_mul]; rw [Set.mem_ofPred_eq]; rw [← Nat.even_add_one] at hm
    dsimp [term]
    rw [Even.neg_pow hm]; rw [neg_one_mul]; rw [neg_add_cancel]

Depends on / 依赖: Eq.trans_lt, Odd.neg_pow, abs_neg, convert, h_term_eq_goal, hasSum_iff, hasSum_pow_di, hasSum_pow_div_log_of_abs_lt_one, mul_left, neg_pow, ring_nf, trans_lt, two_ne_zero
-/
theorem hasSum_log_sub_log_of_abs_lt_one {x : Real} (h : |x| < 1) :
    HasSum (fun k : Nat => (2 : Real) * (1 / (2 * k + 1)) * x ^ (2 * k + 1))
      (log (1 + x) - log (1 - x)) := by
  set term := fun n : Nat => -1 * ((-x) ^ (n + 1) / ((n : Real) + 1)) + x ^ (n + 1) / (n + 1)
  have h_term_eq_goal :
      term ∘ (2 * ·) = fun k : Nat => 2 * (1 / (2 * k + 1)) * x ^ (2 * k + 1) := by
    ext n
    dsimp only [term, (· ∘ ·)]
    rw [Odd.neg_pow (⟨n]; rw [rfl⟩ : Odd (2 * n + 1)) x]
    push_cast
    ring_nf
  rw [← h_term_eq_goal]; rw [(mul_right_injective₀ (two_ne_zero' Nat)).hasSum_iff]
  · have h₁ := (hasSum_pow_div_log_of_abs_lt_one (Eq.trans_lt (abs_neg x) h)).mul_left (-1)
    convert! h₁.add (hasSum_pow_div_log_of_abs_lt_one h) using 1
    ring_nf
  · intro m hm
    rw [range_two_mul]; rw [Set.mem_ofPred_eq]; rw [← Nat.even_add_one] at hm
    dsimp [term]
    rw [Even.neg_pow hm]; rw [neg_one_mul]; rw [neg_add_cancel]

/--
theorem `hasSum_log_one_add_inv` / 定理 `hasSum_log_one_add_inv`

English:
theorem hasSum_log_one_add_inv
  given: {a : Real} (h : 0 < a)
  proof: by
  have h₁ : |1 / (2 * a + 1)| < 1 := by
    rw [abs_of_pos]; rw [div_lt_one]
    · linarith
    · linarith
    · exact div_pos one_pos (by linarith)
  convert! hasSum_log_sub_log_of_abs_lt_one h₁ using 1
  have h₂ : (2 : Real) * a + 1 != 0 := by linarith
  have h₃ := h.ne'
  rw [← log_div]
  · congr
    simp [field]
    ring
  · field_simp
    positivity
  · simp [field, h₃]

中文:
定理 hasSum_log_one_add_inv
  条件: {a : 实数} (h : 0 < a)
  证明: by
  have h₁ : |1 / (2 * a + 1)| < 1 := by
    rw [abs_of_pos]; rw [div_lt_one]
    · linarith
    · linarith
    · exact div_pos one_pos (by linarith)
  convert! hasSum_log_sub_log_of_abs_lt_one h₁ using 1
  have h₂ : (2 : Real) * a + 1 != 0 := by linarith
  have h₃ := h.ne'
  rw [← log_div]
  · congr
    simp [field]
    ring
  · field_simp
    positivity
  · simp [field, h₃]

Depends on / 依赖: abs_of_pos, convert, div_lt_one, div_pos, h.ne, hasSum_log_sub_log_of_abs_lt_one, log_div, one_pos
-/
theorem hasSum_log_one_add_inv {a : Real} (h : 0 < a) :
    HasSum (fun k : Nat => (2 : Real) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1))
      (log (1 + a⁻¹)) := by
  have h₁ : |1 / (2 * a + 1)| < 1 := by
    rw [abs_of_pos]; rw [div_lt_one]
    · linarith
    · linarith
    · exact div_pos one_pos (by linarith)
  convert! hasSum_log_sub_log_of_abs_lt_one h₁ using 1
  have h₂ : (2 : Real) * a + 1 != 0 := by linarith
  have h₃ := h.ne'
  rw [← log_div]
  · congr
    simp [field]
    ring
  · field_simp
    positivity
  · simp [field, h₃]

/--
theorem `hasSum_log_one_add` / 定理 `hasSum_log_one_add`

English:
theorem hasSum_log_one_add
  given: {a : Real} (h : 0 <= a)
  proof: by
  obtain (rfl | ha0) := eq_or_ne a 0
  · simp [hasSum_zero]
  · convert! hasSum_log_one_add_inv (inv_pos.mpr (lt_of_le_of_ne h ha0.symm)) using 4
    all_goals simp [field, add_comm]

中文:
定理 hasSum_log_one_add
  条件: {a : 实数} (h : 0 <= a)
  证明: by
  obtain (rfl | ha0) := eq_or_ne a 0
  · simp [hasSum_zero]
  · convert! hasSum_log_one_add_inv (inv_pos.mpr (lt_of_le_of_ne h ha0.symm)) using 4
    all_goals simp [field, add_comm]

Depends on / 依赖: add_comm, all_goals, convert, eq_or_ne, ha0.symm, hasSum_log_one_add_inv, hasSum_zero, inv_pos, inv_pos.mpr, lt_of_le_of_ne
-/
theorem hasSum_log_one_add {a : Real} (h : 0 <= a) :
    HasSum (fun k : Nat => (2 : Real) * (1 / (2 * k + 1)) * (a / (a + 2)) ^ (2 * k + 1))
      (log (1 + a)) := by
  obtain (rfl | ha0) := eq_or_ne a 0
  · simp [hasSum_zero]
  · convert! hasSum_log_one_add_inv (inv_pos.mpr (lt_of_le_of_ne h ha0.symm)) using 4
    all_goals simp [field, add_comm]

end Real
