/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Derivatives of Schwartz functions

In this file we define the various notions of derivatives of Schwartz functions.

## Main definitions

* `SchwartzMap.fderivCLM`: The differential as a continuous linear map
  `𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F)`
* `SchwartzMap.derivCLM`: The one-dimensional derivative as a continuous linear map
  `𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F)`
* `SchwartzMap.instLineDeriv`: The directional derivative with notation `∂_{m} f`
* `SchwartzMap.instLaplacian`: The Laplacian for `𝓢(E, F)` as an instance of the notation type-class
  `Laplacian`.

## Main statements

* `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`: the iterated directional derivative is given
  by the applied Fréchet derivative of a Schwartz function.
* `SchwartzMap.laplacian_eq_sum`: the Laplacian is given by the sum of second derivatives in any
  orthonormal basis.
* `SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left`: Integration by parts using the
  directional derivative `∂_{m}`
* `SchwartzMap.integral_bilinear_laplacian_right_eq_left`: Integration by parts for the Laplacian

-/

@[expose] public noncomputable section

variable {ι 𝕜 𝕜' D E F V F F₁ F₂ F₃ : Type*}

namespace SchwartzMap

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real F]

section Derivatives

/-! ### Derivatives of Schwartz functions -/

variable [NormedSpace Real E]

variable (𝕜)
variable [RCLike 𝕜] [NormedSpace 𝕜 F]

variable (F) in
/--
Definition of `derivCLM` / `derivCLM` 的定义

English:
definition derivCLM
  signature: : 𝓢(Real, F) ->L[𝕜] 𝓢(Real, F)
  body: mkCLM (deriv ·) (fun f g _ => deriv_add f.differentiableAt g.differentiableAt)
    (fun a f _ => deriv_const_smul a f.differentiableAt)
    (fun f => (contDiff_succ_iff_deriv.mp (f.smooth ⊤)).2.2) fun ⟨k, n⟩ =>
    ⟨{⟨k, n + 1⟩}, 1, zero_le_one, fun f x => by
      simpa only [Real.norm_eq_abs, Fins

中文:
定义 derivCLM
  签名: : 𝓢(实数, F) ->L[𝕜] 𝓢(实数, F)
  定义体: mkCLM (deriv ·) (fun f g _ => deriv_add f.differentiableAt g.differentiableAt)
    (fun a f _ => deriv_const_smul a f.differentiableAt)
    (fun f => (contDiff_succ_iff_deriv.mp (f.smooth ⊤)).2.2) fun ⟨k, n⟩ =>
    ⟨{⟨k, n + 1⟩}, 1, zero_le_one, fun f x => by
      simpa only [Real.norm_eq_abs, Fins

Depends on / 依赖: Finset, Finset.sup_singleton, Real.norm_eq_abs, contDiff_succ_iff_deriv, contDiff_succ_iff_deriv.mp, deriv_add, deriv_const_smul, differentiableAt, f.differentiableAt, f.le_seminorm, f.smooth, g.differentiableAt, iteratedDeriv_succ, le_seminorm, norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, one_mul, schwartzSeminormFamily_apply, smooth, sup_singleton
-/
def derivCLM : 𝓢(Real, F) ->L[𝕜] 𝓢(Real, F) :=
  mkCLM (deriv ·) (fun f g _ => deriv_add f.differentiableAt g.differentiableAt)
    (fun a f _ => deriv_const_smul a f.differentiableAt)
    (fun f => (contDiff_succ_iff_deriv.mp (f.smooth ⊤)).2.2) fun ⟨k, n⟩ =>
    ⟨{⟨k, n + 1⟩}, 1, zero_le_one, fun f x => by
      simpa only [Real.norm_eq_abs, Finset.sup_singleton, schwartzSeminormFamily_apply, one_mul,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedDeriv_succ'] using
        f.le_seminorm' 𝕜 k (n + 1) x⟩

@[simp]
/--
theorem `derivCLM_apply` / 定理 `derivCLM_apply`

English:
theorem derivCLM_apply
  given: (f : 𝓢(Real, F)) (x : Real)
  statement: derivCLM 𝕜 F f x = deriv f x
  proof: rfl

中文:
定理 derivCLM_apply
  条件: (f : 𝓢(实数, F)) (x : 实数)
  结论: derivCLM 𝕜 F f x = deriv f x
  证明: rfl
-/
theorem derivCLM_apply (f : 𝓢(Real, F)) (x : Real) : derivCLM 𝕜 F f x = deriv f x :=
  rfl

/--
theorem `hasDerivAt` / 定理 `hasDerivAt`

English:
theorem hasDerivAt
  given: (f : 𝓢(Real, F)) (x : Real)
  statement: HasDerivAt f (deriv f x) x
  proof: f.differentiableAt.hasDerivAt

中文:
定理 hasDerivAt
  条件: (f : 𝓢(实数, F)) (x : 实数)
  结论: 在点处可导 f (deriv f x) x
  证明: f.differentiableAt.hasDerivAt

Depends on / 依赖: differentiableAt, f.differentiableAt.hasDerivAt, hasDerivAt
-/
theorem hasDerivAt (f : 𝓢(Real, F)) (x : Real) : HasDerivAt f (deriv f x) x :=
  f.differentiableAt.hasDerivAt

open LineDeriv

section fderiv

variable [SMulCommClass Real 𝕜 F]

variable (E F) in
/--
Definition of `fderivCLM` / `fderivCLM` 的定义

English:
definition fderivCLM
  signature: : 𝓢(E, F) ->L[𝕜] 𝓢(E, E ->L[Real] F)
  body: mkCLM (fderiv Real ·) (fun f g _ => fderiv_add f.differentiableAt g.differentiableAt)
    (fun a f _ => fderiv_const_smul f.differentiableAt a)
    (fun f => (contDiff_succ_iff_fderiv.mp (f.smooth ⊤)).2.2) fun ⟨k, n⟩ =>
    ⟨{⟨k, n + 1⟩}, 1, zero_le_one, fun f x => by
      simpa only [schwartzSemin

中文:
定义 fderivCLM
  签名: : 𝓢(E, F) ->L[𝕜] 𝓢(E, E ->L[实数] F)
  定义体: mkCLM (fderiv Real ·) (fun f g _ => fderiv_add f.differentiableAt g.differentiableAt)
    (fun a f _ => fderiv_const_smul f.differentiableAt a)
    (fun f => (contDiff_succ_iff_fderiv.mp (f.smooth ⊤)).2.2) fun ⟨k, n⟩ =>
    ⟨{⟨k, n + 1⟩}, 1, zero_le_one, fun f x => by
      simpa only [schwartzSemin

Depends on / 依赖: Finset, Finset.sup_singleton, Seminorm, Seminorm.comp_apply, comp_apply, contDiff_succ_iff_fderiv, contDiff_succ_iff_fderiv.mp, differentiableAt, f.differentiableAt, f.le_seminorm, f.smooth, fderiv, fderiv_add, fderiv_const_smul, g.differentiableAt, le_seminorm, norm_iteratedFDeriv_fderiv, one_mul, one_smul, schwartzSeminormFamily_apply
-/
def fderivCLM : 𝓢(E, F) ->L[𝕜] 𝓢(E, E ->L[Real] F) :=
  mkCLM (fderiv Real ·) (fun f g _ => fderiv_add f.differentiableAt g.differentiableAt)
    (fun a f _ => fderiv_const_smul f.differentiableAt a)
    (fun f => (contDiff_succ_iff_fderiv.mp (f.smooth ⊤)).2.2) fun ⟨k, n⟩ =>
    ⟨{⟨k, n + 1⟩}, 1, zero_le_one, fun f x => by
      simpa only [schwartzSeminormFamily_apply, Seminorm.comp_apply, Finset.sup_singleton,
        one_smul, norm_iteratedFDeriv_fderiv, one_mul] using f.le_seminorm 𝕜 k (n + 1) x⟩

@[simp]
/--
theorem `fderivCLM_apply` / 定理 `fderivCLM_apply`

English:
theorem fderivCLM_apply
  given: (f : 𝓢(E, F)) (x : E)
  statement: fderivCLM 𝕜 E F f x = fderiv Real f x
  proof: rfl

中文:
定理 fderivCLM_apply
  条件: (f : 𝓢(E, F)) (x : E)
  结论: fderivCLM 𝕜 E F f x = fderiv 实数 f x
  证明: rfl
-/
theorem fderivCLM_apply (f : 𝓢(E, F)) (x : E) : fderivCLM 𝕜 E F f x = fderiv Real f x :=
  rfl

/--
theorem `hasFDerivAt` / 定理 `hasFDerivAt`

English:
theorem hasFDerivAt
  given: (f : 𝓢(E, F)) (x : E)
  statement: HasFDerivAt f (fderiv Real f x) x
  proof: f.differentiableAt.hasFDerivAt

中文:
定理 hasFDerivAt
  条件: (f : 𝓢(E, F)) (x : E)
  结论: 在点处Fréchet可导 f (fderiv 实数 f x) x
  证明: f.differentiableAt.hasFDerivAt

Depends on / 依赖: differentiableAt, f.differentiableAt.hasFDerivAt, hasFDerivAt
-/
theorem hasFDerivAt (f : 𝓢(E, F)) (x : E) : HasFDerivAt f (fderiv Real f x) x :=
  f.differentiableAt.hasFDerivAt

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDeriv E 𝓢(E, F) 𝓢(E, F)
  body: (SchwartzMap.evalCLM Real E F m ∘L fderivCLM Real E F) f

中文:
实例 :
  签名: LineDeriv E 𝓢(E, F) 𝓢(E, F)
  定义体: (SchwartzMap.evalCLM Real E F m ∘L fderivCLM Real E F) f

Depends on / 依赖: SchwartzMap, SchwartzMap.evalCLM, evalCLM, fderivCLM
-/
instance : LineDeriv E 𝓢(E, F) 𝓢(E, F) where
  lineDerivOp m f := (SchwartzMap.evalCLM Real E F m ∘L fderivCLM Real E F) f

/--
theorem `lineDerivOp_apply_eq_fderiv` / 定理 `lineDerivOp_apply_eq_fderiv`

English:
theorem lineDerivOp_apply_eq_fderiv
  given: (m : E) (f : 𝓢(E, F)) (x : E)
  proof: rfl

中文:
定理 lineDerivOp_apply_eq_fderiv
  条件: (m : E) (f : 𝓢(E, F)) (x : E)
  证明: rfl
-/
theorem lineDerivOp_apply_eq_fderiv (m : E) (f : 𝓢(E, F)) (x : E) :
    ∂_{m} f x = fderiv Real f x m := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDerivAdd E 𝓢(E, F) 𝓢(E, F)
  body: ((SchwartzMap.evalCLM Real E F m).comp (fderivCLM Real E F)).map_add
  lineDerivOp_left_add v w f := by
    ext x
    simp [lineDerivOp_apply_eq_fderiv]

中文:
实例 :
  签名: LineDerivAdd E 𝓢(E, F) 𝓢(E, F)
  定义体: ((SchwartzMap.evalCLM Real E F m).comp (fderivCLM Real E F)).map_add
  lineDerivOp_left_add v w f := by
    ext x
    simp [lineDerivOp_apply_eq_fderiv]

Depends on / 依赖: SchwartzMap, SchwartzMap.evalCLM, evalCLM, fderivCLM, map_add
-/
instance : LineDerivAdd E 𝓢(E, F) 𝓢(E, F) where
  lineDerivOp_add m := ((SchwartzMap.evalCLM Real E F m).comp (fderivCLM Real E F)).map_add
  lineDerivOp_left_add v w f := by
    ext x
    simp [lineDerivOp_apply_eq_fderiv]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDerivSMul 𝕜 E 𝓢(E, F) 𝓢(E, F)
  body: (SchwartzMap.evalCLM 𝕜 E F m ∘L fderivCLM 𝕜 E F).map_smul

中文:
实例 :
  签名: LineDerivSMul 𝕜 E 𝓢(E, F) 𝓢(E, F)
  定义体: (SchwartzMap.evalCLM 𝕜 E F m ∘L fderivCLM 𝕜 E F).map_smul

Depends on / 依赖: SchwartzMap, SchwartzMap.evalCLM, evalCLM, fderivCLM, map_smul
-/
instance : LineDerivSMul 𝕜 E 𝓢(E, F) 𝓢(E, F) where
  lineDerivOp_smul m := (SchwartzMap.evalCLM 𝕜 E F m ∘L fderivCLM 𝕜 E F).map_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDerivLeftSMul Real E 𝓢(E, F) 𝓢(E, F)
  body: by
    ext x
    simp [lineDerivOp_apply_eq_fderiv]

中文:
实例 :
  签名: LineDerivLeftSMul 实数 E 𝓢(E, F) 𝓢(E, F)
  定义体: by
    ext x
    simp [lineDerivOp_apply_eq_fderiv]

Depends on / 依赖: lineDerivOp_apply_eq_fderiv
-/
instance : LineDerivLeftSMul Real E 𝓢(E, F) 𝓢(E, F) where
  lineDerivOp_left_smul r y f := by
    ext x
    simp [lineDerivOp_apply_eq_fderiv]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousLineDeriv E 𝓢(E, F) 𝓢(E, F)
  body: (SchwartzMap.evalCLM Real E F m ∘L fderivCLM Real E F).continuous

中文:
实例 :
  签名: 余ntinuousLineDeriv E 𝓢(E, F) 𝓢(E, F)
  定义体: (SchwartzMap.evalCLM Real E F m ∘L fderivCLM Real E F).continuous

Depends on / 依赖: SchwartzMap, SchwartzMap.evalCLM, continuous, evalCLM, fderivCLM
-/
instance : ContinuousLineDeriv E 𝓢(E, F) 𝓢(E, F) where
  continuous_lineDerivOp m := (SchwartzMap.evalCLM Real E F m ∘L fderivCLM Real E F).continuous

open LineDeriv

/--
theorem `lineDerivOpCLM_eq` / 定理 `lineDerivOpCLM_eq`

English:
theorem lineDerivOpCLM_eq
  given: (m : E)
  proof: rfl

中文:
定理 lineDerivOpCLM_eq
  条件: (m : E)
  证明: rfl
-/
theorem lineDerivOpCLM_eq (m : E) :
    lineDerivOpCLM 𝕜 𝓢(E, F) m = SchwartzMap.evalCLM 𝕜 E F m ∘L fderivCLM 𝕜 E F := rfl

/--
theorem `lineDerivOp_apply` / 定理 `lineDerivOp_apply`

English:
theorem lineDerivOp_apply
  given: (m : E) (f : 𝓢(E, F)) (x : E)
  statement: ∂_{m} f x = lineDeriv Real f x m
  proof: f.differentiableAt.lineDeriv_eq_fderiv.symm

中文:
定理 lineDerivOp_apply
  条件: (m : E) (f : 𝓢(E, F)) (x : E)
  结论: ∂_{m} f x = lineDeriv 实数 f x m
  证明: f.differentiableAt.lineDeriv_eq_fderiv.symm

Depends on / 依赖: differentiableAt, f.differentiableAt.lineDeriv_eq_fderiv.symm, lineDeriv_eq_fderiv
-/
theorem lineDerivOp_apply (m : E) (f : 𝓢(E, F)) (x : E) : ∂_{m} f x = lineDeriv Real f x m :=
  f.differentiableAt.lineDeriv_eq_fderiv.symm

/--
theorem `iteratedLineDerivOp_eq_iteratedFDeriv` / 定理 `iteratedLineDerivOp_eq_iteratedFDeriv`

English:
theorem iteratedLineDerivOp_eq_iteratedFDeriv
  given: {n : Nat} {m : Fin n -> E} {f : 𝓢(E, F)} {x : E}
  proof: by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left]; rw [iteratedFDeriv_succ_apply_left]; rw [← fderiv_continuousMultilinear_apply_const_apply]
    · simp only [lineDerivOp_apply_eq_fderiv, ← ih]
    · exact (f.smooth ⊤).differentiable_iterat

中文:
定理 iteratedLineDerivOp_eq_iteratedFDeriv
  条件: {n : 自然数} {m : 有限集 n -> E} {f : 𝓢(E, F)} {x : E}
  证明: by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left]; rw [iteratedFDeriv_succ_apply_left]; rw [← fderiv_continuousMultilinear_apply_const_apply]
    · simp only [lineDerivOp_apply_eq_fderiv, ← ih]
    · exact (f.smooth ⊤).differentiable_iterat

Depends on / 依赖: ENat.natCast_lt_top, differentiable_iteratedFDeriv, f.smooth, fderiv_continuousMultilinear_apply_const_apply, generalizing, iteratedFDeriv_succ_apply_left, iteratedLineDerivOp_succ_left, lineDerivOp_apply_eq_fderiv, mod_cast, natCast_lt_top, smooth
-/
theorem iteratedLineDerivOp_eq_iteratedFDeriv {n : Nat} {m : Fin n -> E} {f : 𝓢(E, F)} {x : E} :
    ∂^{m} f x = iteratedFDeriv Real n f x m := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left]; rw [iteratedFDeriv_succ_apply_left]; rw [← fderiv_continuousMultilinear_apply_const_apply]
    · simp only [lineDerivOp_apply_eq_fderiv, ← ih]
    · exact (f.smooth ⊤).differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n) x

end fderiv

variable [NormedAddCommGroup D] [NormedSpace Real D]

/--
theorem `lineDerivOp_compCLMOfContinuousLinearEquiv` / 定理 `lineDerivOp_compCLMOfContinuousLinearEquiv`

English:
theorem lineDerivOp_compCLMOfContinuousLinearEquiv
  given: (m : D) (g : D ≃L[Real] E) (f : 𝓢(E, F))
  proof: by
  ext x
  simp [lineDerivOp_apply_eq_fderiv, ContinuousLinearEquiv.comp_right_fderiv]

中文:
定理 lineDerivOp_compCLMOfContinuousLinearEquiv
  条件: (m : D) (g : D ≃L[实数] E) (f : 𝓢(E, F))
  证明: by
  ext x
  simp [lineDerivOp_apply_eq_fderiv, ContinuousLinearEquiv.comp_right_fderiv]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.comp_right_fderiv, comp_right_fderiv, lineDerivOp_apply_eq_fderiv
-/
theorem lineDerivOp_compCLMOfContinuousLinearEquiv (m : D) (g : D ≃L[Real] E) (f : 𝓢(E, F)) :
    ∂_{m} (compCLMOfContinuousLinearEquiv 𝕜 g f) =
    compCLMOfContinuousLinearEquiv 𝕜 g (∂_{g m} f) := by
  ext x
  simp [lineDerivOp_apply_eq_fderiv, ContinuousLinearEquiv.comp_right_fderiv]

end Derivatives

section support

variable (𝕜)
variable [RCLike 𝕜] [NormedSpace 𝕜 F]

/--
theorem `tsupport_derivCLM_subset` / 定理 `tsupport_derivCLM_subset`

English:
theorem tsupport_derivCLM_subset
  given: (f : 𝓢(Real, F))
  statement: tsupport (derivCLM 𝕜 F f) subseteq tsupport f
  proof: by
  change tsupport (deriv f ·) subseteq _
  simp_rw [← fderiv_apply_one_eq_deriv]
  exact tsupport_fderiv_apply_subset Real 1

中文:
定理 tsupport_derivCLM_subset
  条件: (f : 𝓢(实数, F))
  结论: tsupport (derivCLM 𝕜 F f) subseteq tsupport f
  证明: by
  change tsupport (deriv f ·) subseteq _
  simp_rw [← fderiv_apply_one_eq_deriv]
  exact tsupport_fderiv_apply_subset Real 1

Depends on / 依赖: fderiv_apply_one_eq_deriv, simp_rw, subseteq, tsupport, tsupport_fderiv_apply_subset
-/
theorem tsupport_derivCLM_subset (f : 𝓢(Real, F)) : tsupport (derivCLM 𝕜 F f) subseteq tsupport f := by
  change tsupport (deriv f ·) subseteq _
  simp_rw [← fderiv_apply_one_eq_deriv]
  exact tsupport_fderiv_apply_subset Real 1

variable [NormedSpace Real E] [SMulCommClass Real 𝕜 F]

/--
theorem `tsupport_fderivCLM_subset` / 定理 `tsupport_fderivCLM_subset`

English:
theorem tsupport_fderivCLM_subset
  given: (f : 𝓢(E, F))
  statement: tsupport (fderivCLM 𝕜 E F f) subseteq tsupport f
  proof: tsupport_fderiv_subset Real

中文:
定理 tsupport_fderivCLM_subset
  条件: (f : 𝓢(E, F))
  结论: tsupport (fderivCLM 𝕜 E F f) subseteq tsupport f
  证明: tsupport_fderiv_subset Real

Depends on / 依赖: tsupport_fderiv_subset
-/
theorem tsupport_fderivCLM_subset (f : 𝓢(E, F)) : tsupport (fderivCLM 𝕜 E F f) subseteq tsupport f :=
  tsupport_fderiv_subset Real

open LineDeriv

/--
theorem `tsupport_lineDerivOp_subset` / 定理 `tsupport_lineDerivOp_subset`

English:
theorem tsupport_lineDerivOp_subset
  given: (m : E) (f : 𝓢(E, F))
  proof: tsupport_fderiv_apply_subset Real m

中文:
定理 tsupport_lineDerivOp_subset
  条件: (m : E) (f : 𝓢(E, F))
  证明: tsupport_fderiv_apply_subset Real m

Depends on / 依赖: tsupport_fderiv_apply_subset
-/
theorem tsupport_lineDerivOp_subset (m : E) (f : 𝓢(E, F)) :
    tsupport (∂_{m} f : 𝓢(E, F)) subseteq tsupport f :=
  tsupport_fderiv_apply_subset Real m

/--
theorem `tsupport_iteratedLineDerivOp_subset` / 定理 `tsupport_iteratedLineDerivOp_subset`

English:
theorem tsupport_iteratedLineDerivOp_subset
  given: {n : Nat} (m : Fin n -> E) (f : 𝓢(E, F))
  proof: by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left]
    exact (tsupport_lineDerivOp_subset (m 0) _).trans (IH <| Fin.tail m)

中文:
定理 tsupport_iteratedLineDerivOp_subset
  条件: {n : 自然数} (m : 有限集 n -> E) (f : 𝓢(E, F))
  证明: by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left]
    exact (tsupport_lineDerivOp_subset (m 0) _).trans (IH <| Fin.tail m)

Depends on / 依赖: Fin.tail, iteratedLineDerivOp_succ_left, tsupport_lineDerivOp_subset
-/
theorem tsupport_iteratedLineDerivOp_subset {n : Nat} (m : Fin n -> E) (f : 𝓢(E, F)) :
    tsupport (∂^{m} f : 𝓢(E, F)) subseteq tsupport f := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left]
    exact (tsupport_lineDerivOp_subset (m 0) _).trans (IH <| Fin.tail m)

end support

section Laplacian

/-! ## Laplacian on `𝓢(E, F)` -/

variable [InnerProductSpace Real E] [FiniteDimensional Real E]

open Laplacian LineDeriv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Laplacian 𝓢(E, F) 𝓢(E, F)
  body: laplacianCLM Real E 𝓢(E, F)

中文:
实例 :
  签名: Laplace算子 𝓢(E, F) 𝓢(E, F)
  定义体: laplacianCLM Real E 𝓢(E, F)

Depends on / 依赖: laplacianCLM
-/
instance : Laplacian 𝓢(E, F) 𝓢(E, F) where
  laplacian := laplacianCLM Real E 𝓢(E, F)

/--
theorem `laplacianCLM_eq'` / 定理 `laplacianCLM_eq'`

English:
theorem laplacianCLM_eq'
  given: (f : 𝓢(E, F))
  statement: laplacianCLM Real E 𝓢(E, F) f = Δ f
  proof: rfl

中文:
定理 laplacianCLM_eq'
  条件: (f : 𝓢(E, F))
  结论: laplacianCLM 实数 E 𝓢(E, F) f = Δ f
  证明: rfl
-/
theorem laplacianCLM_eq' (f : 𝓢(E, F)) : laplacianCLM Real E 𝓢(E, F) f = Δ f := rfl

/--
theorem `laplacian_eq_sum` / 定理 `laplacian_eq_sum`

English:
theorem laplacian_eq_sum
  given: [Fintype ι] (b : OrthonormalBasis ι Real E) (f : 𝓢(E, F))
  proof: LineDeriv.laplacianCLM_eq_sum b f

中文:
定理 laplacian_eq_sum
  条件: [有限类型 ι] (b : 正交标准基 ι 实数 E) (f : 𝓢(E, F))
  证明: LineDeriv.laplacianCLM_eq_sum b f

Depends on / 依赖: LineDeriv, LineDeriv.laplacianCLM_eq_sum, laplacianCLM_eq_sum
-/
theorem laplacian_eq_sum [Fintype ι] (b : OrthonormalBasis ι Real E) (f : 𝓢(E, F)) :
    Δ f = ∑ i, ∂_{b i} (∂_{b i} f) :=
  LineDeriv.laplacianCLM_eq_sum b f

variable (𝕜) in
@[simp]
/--
theorem `laplacianCLM_eq` / 定理 `laplacianCLM_eq`

English:
theorem laplacianCLM_eq
  given: [RCLike 𝕜] [NormedSpace 𝕜 F] (f : 𝓢(E, F))
  proof: by
  simp [laplacianCLM, laplacian_eq_sum (stdOrthonormalBasis Real E)]

中文:
定理 laplacianCLM_eq
  条件: [RCLike 𝕜] [赋范空间 𝕜 F] (f : 𝓢(E, F))
  证明: by
  simp [laplacianCLM, laplacian_eq_sum (stdOrthonormalBasis Real E)]

Depends on / 依赖: laplacianCLM, laplacian_eq_sum, stdOrthonormalBasis
-/
theorem laplacianCLM_eq [RCLike 𝕜] [NormedSpace 𝕜 F] (f : 𝓢(E, F)) :
    laplacianCLM 𝕜 E 𝓢(E, F) f = Δ f := by
  simp [laplacianCLM, laplacian_eq_sum (stdOrthonormalBasis Real E)]

/--
theorem `laplacian_apply` / 定理 `laplacian_apply`

English:
theorem laplacian_apply
  given: (f : 𝓢(E, F)) (x : E)
  statement: Δ f x = Δ (f : E -> F) x
  proof: by
  rw [laplacian_eq_sum (stdOrthonormalBasis Real E)]
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis Real E),
    sum_apply, ← iteratedLineDerivOp_eq_iteratedFDeriv, iteratedLineDerivOp_succ_left]

中文:
定理 laplacian_apply
  条件: (f : 𝓢(E, F)) (x : E)
  结论: Δ f x = Δ (f : E -> F) x
  证明: by
  rw [laplacian_eq_sum (stdOrthonormalBasis Real E)]
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis Real E),
    sum_apply, ← iteratedLineDerivOp_eq_iteratedFDeriv, iteratedLineDerivOp_succ_left]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis, iteratedLineDerivOp_eq_iteratedFDeriv, iteratedLineDerivOp_succ_left, laplacian_eq_iteratedFDeriv_orthonormalBasis, laplacian_eq_sum, stdOrthonormalBasis, sum_apply
-/
theorem laplacian_apply (f : 𝓢(E, F)) (x : E) : Δ f x = Δ (f : E -> F) x := by
  rw [laplacian_eq_sum (stdOrthonormalBasis Real E)]
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis Real E),
    sum_apply, ← iteratedLineDerivOp_eq_iteratedFDeriv, iteratedLineDerivOp_succ_left]

end Laplacian

section integration_by_parts

variable [NormedSpace Real E]

open ENNReal MeasureTheory

section one_dim

variable [NormedAddCommGroup V] [NormedSpace Real V]

/--
theorem `integral_bilinear_deriv_right_eq_neg_left` / 定理 `integral_bilinear_deriv_right_eq_neg_left`

English:
theorem integral_bilinear_deriv_right_eq_neg_left
  statement: (f : 𝓢(Real, E)) (g : 𝓢(Real, F))
  proof: MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (fun x _ => f.hasDerivAt x) (fun x _ => g.hasDerivAt x) (pairing L f (derivCLM Real F g)).integrable
    (pairing L (derivCLM Real E f) g).integrable (pairing L f g).integrable

中文:
定理 integral_bilinear_deriv_right_eq_neg_left
  结论: (f : 𝓢(实数, E)) (g : 𝓢(实数, F))
  证明: MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (fun x _ => f.hasDerivAt x) (fun x _ => g.hasDerivAt x) (pairing L f (derivCLM Real F g)).integrable
    (pairing L (derivCLM Real E f) g).integrable (pairing L f g).integrable

Depends on / 依赖: MeasureTheory, MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable, derivCLM, f.hasDerivAt, g.hasDerivAt, hasDerivAt, integrable, integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable, pairing
-/
theorem integral_bilinear_deriv_right_eq_neg_left (f : 𝓢(Real, E)) (g : 𝓢(Real, F))
    (L : E ->L[Real] F ->L[Real] V) :
    ∫ (x : Real), L (f x) (deriv g x) = -∫ (x : Real), L (deriv f x) (g x) :=
  MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (fun x _ => f.hasDerivAt x) (fun x _ => g.hasDerivAt x) (pairing L f (derivCLM Real F g)).integrable
    (pairing L (derivCLM Real E f) g).integrable (pairing L f g).integrable

variable [NormedRing 𝕜] [NormedSpace Real 𝕜] [IsScalarTower Real 𝕜 𝕜] [SMulCommClass Real 𝕜 𝕜] in
/--
theorem `integral_mul_deriv_eq_neg_deriv_mul` / 定理 `integral_mul_deriv_eq_neg_deriv_mul`

English:
theorem integral_mul_deriv_eq_neg_deriv_mul
  given: (f : 𝓢(Real, 𝕜)) (g : 𝓢(Real, 𝕜))
  proof: integral_bilinear_deriv_right_eq_neg_left f g (ContinuousLinearMap.mul Real 𝕜)

中文:
定理 integral_mul_deriv_eq_neg_deriv_mul
  条件: (f : 𝓢(实数, 𝕜)) (g : 𝓢(实数, 𝕜))
  证明: integral_bilinear_deriv_right_eq_neg_left f g (ContinuousLinearMap.mul Real 𝕜)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, integral_bilinear_deriv_right_eq_neg_left
-/
theorem integral_mul_deriv_eq_neg_deriv_mul (f : 𝓢(Real, 𝕜)) (g : 𝓢(Real, 𝕜)) :
    ∫ (x : Real), f x * (deriv g x) = -∫ (x : Real), deriv f x * (g x) :=
  integral_bilinear_deriv_right_eq_neg_left f g (ContinuousLinearMap.mul Real 𝕜)

variable [RCLike 𝕜] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]

/--
theorem `integral_smul_deriv_right_eq_neg_left` / 定理 `integral_smul_deriv_right_eq_neg_left`

English:
theorem integral_smul_deriv_right_eq_neg_left
  given: (f : 𝓢(Real, 𝕜)) (g : 𝓢(Real, F))
  proof: integral_bilinear_deriv_right_eq_neg_left f g (ContinuousLinearMap.lsmul Real 𝕜)

中文:
定理 integral_smul_deriv_right_eq_neg_left
  条件: (f : 𝓢(实数, 𝕜)) (g : 𝓢(实数, F))
  证明: integral_bilinear_deriv_right_eq_neg_left f g (ContinuousLinearMap.lsmul Real 𝕜)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, integral_bilinear_deriv_right_eq_neg_left
-/
theorem integral_smul_deriv_right_eq_neg_left (f : 𝓢(Real, 𝕜)) (g : 𝓢(Real, F)) :
    ∫ (x : Real), f x • deriv g x = -∫ (x : Real), deriv f x • g x :=
  integral_bilinear_deriv_right_eq_neg_left f g (ContinuousLinearMap.lsmul Real 𝕜)

/--
theorem `integral_clm_comp_deriv_right_eq_neg_left` / 定理 `integral_clm_comp_deriv_right_eq_neg_left`

English:
theorem integral_clm_comp_deriv_right_eq_neg_left
  given: (f : 𝓢(Real, F ->L[𝕜] V)) (g : 𝓢(Real, F))
  proof: integral_bilinear_deriv_right_eq_neg_left f g
    ((ContinuousLinearMap.id 𝕜 (F ->L[𝕜] V)).bilinearRestrictScalars Real)

中文:
定理 integral_clm_comp_deriv_right_eq_neg_left
  条件: (f : 𝓢(实数, F ->L[𝕜] V)) (g : 𝓢(实数, F))
  证明: integral_bilinear_deriv_right_eq_neg_left f g
    ((ContinuousLinearMap.id 𝕜 (F ->L[𝕜] V)).bilinearRestrictScalars Real)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, bilinearRestrictScalars, integral_bilinear_deriv_right_eq_neg_left
-/
theorem integral_clm_comp_deriv_right_eq_neg_left (f : 𝓢(Real, F ->L[𝕜] V)) (g : 𝓢(Real, F)) :
    ∫ (x : Real), f x (deriv g x) = -∫ (x : Real), deriv f x (g x) :=
  integral_bilinear_deriv_right_eq_neg_left f g
    ((ContinuousLinearMap.id 𝕜 (F ->L[𝕜] V)).bilinearRestrictScalars Real)

end one_dim

variable [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup D] [NormedSpace Real D]
  [MeasurableSpace D] {μ : Measure D} [BorelSpace D] [FiniteDimensional Real D] [μ.IsAddHaarMeasure]

open scoped LineDeriv

/--
theorem `integral_bilinear_lineDerivOp_right_eq_neg_left` / 定理 `integral_bilinear_lineDerivOp_right_eq_neg_left`

English:
theorem integral_bilinear_lineDerivOp_right_eq_neg_left
  statement: (f : 𝓢(D, E)) (g : 𝓢(D, F))
  proof: by
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (v := v)
    (bilinLeftCLM L g.hasTemperateGrowth _).integrable
    (bilinLeftCLM L (∂_{v} g).hasTemperateGrowth _).integrable
    (bilinLeftCLM L g.hasTemperateGrowth _).integrable
  all_goals exact fun x _ => (hasFDerivAt 

中文:
定理 integral_bilinear_lineDerivOp_right_eq_neg_left
  结论: (f : 𝓢(D, E)) (g : 𝓢(D, F))
  证明: by
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (v := v)
    (bilinLeftCLM L g.hasTemperateGrowth _).integrable
    (bilinLeftCLM L (∂_{v} g).hasTemperateGrowth _).integrable
    (bilinLeftCLM L g.hasTemperateGrowth _).integrable
  all_goals exact fun x _ => (hasFDerivAt 

Depends on / 依赖: all_goals, bilinLeftCLM, g.hasTemperateGrowth, hasFDerivAt, hasLineDerivAt, hasTemperateGrowth, integrable, integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
-/
theorem integral_bilinear_lineDerivOp_right_eq_neg_left (f : 𝓢(D, E)) (g : 𝓢(D, F))
    (L : E ->L[Real] F ->L[Real] V) (v : D) :
    ∫ (x : D), L (f x) (∂_{v} g x) ∂μ = -∫ (x : D), L (∂_{v} f x) (g x) ∂μ := by
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (v := v)
    (bilinLeftCLM L g.hasTemperateGrowth _).integrable
    (bilinLeftCLM L (∂_{v} g).hasTemperateGrowth _).integrable
    (bilinLeftCLM L g.hasTemperateGrowth _).integrable
  all_goals exact fun x _ => (hasFDerivAt _ x).hasLineDerivAt v

variable [NormedRing 𝕜] [NormedSpace Real 𝕜] [IsScalarTower Real 𝕜 𝕜] [SMulCommClass Real 𝕜 𝕜] in
/--
theorem `integral_mul_lineDerivOp_right_eq_neg_left` / 定理 `integral_mul_lineDerivOp_right_eq_neg_left`

English:
theorem integral_mul_lineDerivOp_right_eq_neg_left
  given: (f : 𝓢(D, 𝕜)) (g : 𝓢(D, 𝕜)) (v : D)
  proof: integral_bilinear_lineDerivOp_right_eq_neg_left f g (ContinuousLinearMap.mul Real 𝕜) v

中文:
定理 integral_mul_lineDerivOp_right_eq_neg_left
  条件: (f : 𝓢(D, 𝕜)) (g : 𝓢(D, 𝕜)) (v : D)
  证明: integral_bilinear_lineDerivOp_right_eq_neg_left f g (ContinuousLinearMap.mul Real 𝕜) v

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, integral_bilinear_lineDerivOp_right_eq_neg_left
-/
theorem integral_mul_lineDerivOp_right_eq_neg_left (f : 𝓢(D, 𝕜)) (g : 𝓢(D, 𝕜)) (v : D) :
    ∫ (x : D), f x * ∂_{v} g x ∂μ = -∫ (x : D), ∂_{v} f x * g x ∂μ :=
  integral_bilinear_lineDerivOp_right_eq_neg_left f g (ContinuousLinearMap.mul Real 𝕜) v

variable [RCLike 𝕜] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]

/--
theorem `integral_smul_lineDerivOp_right_eq_neg_left` / 定理 `integral_smul_lineDerivOp_right_eq_neg_left`

English:
theorem integral_smul_lineDerivOp_right_eq_neg_left
  given: (f : 𝓢(D, 𝕜)) (g : 𝓢(D, F)) (v : D)
  proof: integral_bilinear_lineDerivOp_right_eq_neg_left f g (ContinuousLinearMap.lsmul Real 𝕜) v

中文:
定理 integral_smul_lineDerivOp_right_eq_neg_left
  条件: (f : 𝓢(D, 𝕜)) (g : 𝓢(D, F)) (v : D)
  证明: integral_bilinear_lineDerivOp_right_eq_neg_left f g (ContinuousLinearMap.lsmul Real 𝕜) v

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, integral_bilinear_lineDerivOp_right_eq_neg_left
-/
theorem integral_smul_lineDerivOp_right_eq_neg_left (f : 𝓢(D, 𝕜)) (g : 𝓢(D, F)) (v : D) :
    ∫ (x : D), f x • ∂_{v} g x ∂μ = -∫ (x : D), ∂_{v} f x • g x ∂μ :=
  integral_bilinear_lineDerivOp_right_eq_neg_left f g (ContinuousLinearMap.lsmul Real 𝕜) v

/--
theorem `integral_clm_comp_lineDerivOp_right_eq_neg_left` / 定理 `integral_clm_comp_lineDerivOp_right_eq_neg_left`

English:
theorem integral_clm_comp_lineDerivOp_right_eq_neg_left
  statement: (f : 𝓢(D, F ->L[𝕜] V)) (g : 𝓢(D, F))
  proof: integral_bilinear_lineDerivOp_right_eq_neg_left f g
    ((ContinuousLinearMap.id 𝕜 (F ->L[𝕜] V)).bilinearRestrictScalars Real) v

中文:
定理 integral_clm_comp_lineDerivOp_right_eq_neg_left
  结论: (f : 𝓢(D, F ->L[𝕜] V)) (g : 𝓢(D, F))
  证明: integral_bilinear_lineDerivOp_right_eq_neg_left f g
    ((ContinuousLinearMap.id 𝕜 (F ->L[𝕜] V)).bilinearRestrictScalars Real) v

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, bilinearRestrictScalars, integral_bilinear_lineDerivOp_right_eq_neg_left
-/
theorem integral_clm_comp_lineDerivOp_right_eq_neg_left (f : 𝓢(D, F ->L[𝕜] V)) (g : 𝓢(D, F))
    (v : D) : ∫ (x : D), f x (∂_{v} g x) ∂μ = -∫ (x : D), ∂_{v} f x (g x) ∂μ :=
  integral_bilinear_lineDerivOp_right_eq_neg_left f g
    ((ContinuousLinearMap.id 𝕜 (F ->L[𝕜] V)).bilinearRestrictScalars Real) v

end integration_by_parts

section laplacian_integration_by_parts

open MeasureTheory Laplacian LineDeriv

/-! ### Integration by parts -/

variable [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NormedAddCommGroup F₁] [NormedSpace Real F₁]
  [NormedAddCommGroup F₂] [NormedSpace Real F₂]
  [NormedAddCommGroup F₃] [NormedSpace Real F₃]
  [MeasurableSpace E] {μ : Measure E} [BorelSpace E] [μ.IsAddHaarMeasure]

/--
theorem `integral_bilinear_laplacian_right_eq_left` / 定理 `integral_bilinear_laplacian_right_eq_left`

English:
theorem integral_bilinear_laplacian_right_eq_left
  statement: (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂))
  proof: by
  simp_rw [laplacian_eq_sum (stdOrthonormalBasis Real E), sum_apply, map_sum,
    _root_.sum_apply]
  rw [MeasureTheory.integral_finsetSum]; rw [MeasureTheory.integral_finsetSum]
  · simp [integral_bilinear_lineDerivOp_right_eq_neg_left]
  · exact fun _ _ => (pairing L (∂_{_} <| ∂_{_} f) g).integ

中文:
定理 integral_bilinear_laplacian_right_eq_left
  结论: (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂))
  证明: by
  simp_rw [laplacian_eq_sum (stdOrthonormalBasis Real E), sum_apply, map_sum,
    _root_.sum_apply]
  rw [MeasureTheory.integral_finsetSum]; rw [MeasureTheory.integral_finsetSum]
  · simp [integral_bilinear_lineDerivOp_right_eq_neg_left]
  · exact fun _ _ => (pairing L (∂_{_} <| ∂_{_} f) g).integ

Depends on / 依赖: MeasureTheory, MeasureTheory.integral_finsetSum, _root_, _root_.sum_apply, integrable, integral_bilinear_lineDerivOp_right_eq_neg_left, integral_finsetSum, laplacian_eq_sum, map_sum, pairing, simp_rw, stdOrthonormalBasis, sum_apply
-/
theorem integral_bilinear_laplacian_right_eq_left (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂))
    (L : F₁ ->L[Real] F₂ ->L[Real] F₃) :
    ∫ x, L (f x) (Δ g x) ∂μ = ∫ x, L (Δ f x) (g x) ∂μ := by
  simp_rw [laplacian_eq_sum (stdOrthonormalBasis Real E), sum_apply, map_sum,
    _root_.sum_apply]
  rw [MeasureTheory.integral_finsetSum]; rw [MeasureTheory.integral_finsetSum]
  · simp [integral_bilinear_lineDerivOp_right_eq_neg_left]
  · exact fun _ _ => (pairing L (∂_{_} <| ∂_{_} f) g).integrable
  · exact fun _ _ => (pairing L f (∂_{_} <| ∂_{_} g)).integrable

variable [NormedRing 𝕜] [NormedSpace Real 𝕜] [IsScalarTower Real 𝕜 𝕜] [SMulCommClass Real 𝕜 𝕜] in
/--
theorem `integral_mul_laplacian_right_eq_left` / 定理 `integral_mul_laplacian_right_eq_left`

English:
theorem integral_mul_laplacian_right_eq_left
  given: (f : 𝓢(E, 𝕜)) (g : 𝓢(E, 𝕜))
  proof: integral_bilinear_laplacian_right_eq_left f g (ContinuousLinearMap.mul Real 𝕜)

中文:
定理 integral_mul_laplacian_right_eq_left
  条件: (f : 𝓢(E, 𝕜)) (g : 𝓢(E, 𝕜))
  证明: integral_bilinear_laplacian_right_eq_left f g (ContinuousLinearMap.mul Real 𝕜)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, integral_bilinear_laplacian_right_eq_left
-/
theorem integral_mul_laplacian_right_eq_left (f : 𝓢(E, 𝕜)) (g : 𝓢(E, 𝕜)) :
    ∫ x, f x * Δ g x ∂μ = ∫ x, Δ f x * g x ∂μ :=
  integral_bilinear_laplacian_right_eq_left f g (ContinuousLinearMap.mul Real 𝕜)

variable [RCLike 𝕜] [NormedSpace 𝕜 F]

/--
theorem `integral_smul_laplacian_right_eq_left` / 定理 `integral_smul_laplacian_right_eq_left`

English:
theorem integral_smul_laplacian_right_eq_left
  given: (f : 𝓢(E, 𝕜)) (g : 𝓢(E, F))
  proof: integral_bilinear_laplacian_right_eq_left f g (ContinuousLinearMap.lsmul Real 𝕜)

中文:
定理 integral_smul_laplacian_right_eq_left
  条件: (f : 𝓢(E, 𝕜)) (g : 𝓢(E, F))
  证明: integral_bilinear_laplacian_right_eq_left f g (ContinuousLinearMap.lsmul Real 𝕜)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, integral_bilinear_laplacian_right_eq_left
-/
theorem integral_smul_laplacian_right_eq_left (f : 𝓢(E, 𝕜)) (g : 𝓢(E, F)) :
    ∫ x, f x • Δ g x ∂μ = ∫ x, Δ f x • g x ∂μ :=
  integral_bilinear_laplacian_right_eq_left f g (ContinuousLinearMap.lsmul Real 𝕜)

variable [NormedSpace 𝕜 F₁] [NormedSpace 𝕜 F₂]

/--
theorem `integral_clm_comp_laplacian_right_eq_left` / 定理 `integral_clm_comp_laplacian_right_eq_left`

English:
theorem integral_clm_comp_laplacian_right_eq_left
  given: (f : 𝓢(E, F₁ ->L[𝕜] F₂)) (g : 𝓢(E, F₁))
  proof: integral_bilinear_laplacian_right_eq_left f g
    ((ContinuousLinearMap.id 𝕜 (F₁ ->L[𝕜] F₂)).bilinearRestrictScalars Real)

中文:
定理 integral_clm_comp_laplacian_right_eq_left
  条件: (f : 𝓢(E, F₁ ->L[𝕜] F₂)) (g : 𝓢(E, F₁))
  证明: integral_bilinear_laplacian_right_eq_left f g
    ((ContinuousLinearMap.id 𝕜 (F₁ ->L[𝕜] F₂)).bilinearRestrictScalars Real)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, bilinearRestrictScalars, integral_bilinear_laplacian_right_eq_left
-/
theorem integral_clm_comp_laplacian_right_eq_left (f : 𝓢(E, F₁ ->L[𝕜] F₂)) (g : 𝓢(E, F₁)) :
    ∫ x, f x (Δ g x) ∂μ = ∫ x, Δ f x (g x) ∂μ :=
  integral_bilinear_laplacian_right_eq_left f g
    ((ContinuousLinearMap.id 𝕜 (F₁ ->L[𝕜] F₂)).bilinearRestrictScalars Real)

end laplacian_integration_by_parts

end SchwartzMap
