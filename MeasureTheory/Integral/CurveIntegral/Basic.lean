/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Field.Pointwise
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral of a 1-form along a path

In this file we define the integral of a 1-form along a path indexed by `[0, 1]`
and prove basic properties of this operation.

The integral `∫ᶜ x in γ, ω x` is defined as $\int_0^1 \omega(\gamma(t))(\gamma'(t))$.
More precisely, we use

- `Path.extend γ t` instead of `γ t`, because both derivatives and `intervalIntegral`
  expect globally defined functions;
- `derivWithin γ.extend (Set.Icc 0 1) t`, not `deriv γ.extend t`, for the derivative,
  so that it takes meaningful values at `t = 0` and `t = 1`,
  even though this does not affect the integral.

The argument `ω : E → E →L[𝕜] F` is a `𝕜`-linear 1-form on `E` taking values in `F`,
where `𝕜` is `ℝ` or `ℂ`.
The definition does not depend on `𝕜`, see `curveIntegral_restrictScalars` and nearby lemmas.
However, the fact that `𝕜 = ℝ` is not hardcoded
allows us to avoid inserting `ContinuousLinearMap.restrictScalars` here and there.

## Main definitions

- `curveIntegral ω γ`, notation `∫ᶜ x in γ, ω x`, is the integral of a 1-form `ω` along a path `γ`.
- `CurveIntegrable ω γ` is the predicate saying that the above integral makes sense.

## Main results

We prove that `curveIntegral` behaves well with respect to

- operations on `Path`s, see `curveIntegral_refl`, `curveIntegral_symm`, `curveIntegral_trans` etc;
- algebraic operations on 1-forms, see `curveIntegral_add` etc.

We also show that the derivative of `fun b ↦ ∫ᶜ x in Path.segment a b, ω x`
has derivative `ω a` at `b = a`.
We provide 2 versions of this result: one for derivative (`HasFDerivWithinAt`) within a convex set
and one for `HasFDerivAt`.

## Implementation notes

### Naming

In literature, the integral of a function or a 1-form along a path
is called “line integral”, “path integral”, “curve integral”, or “curvilinear integral”.

We use the name “curve integral” instead of other names for the following reasons:

- for many people whose mother tongue is not English,
  “line integral” sounds like an integral along a straight line;

- we reserve the name "path integral" for Feynman-style integrals over the space of paths.

### Usage of `ContinuousLinearMap`s for 1-forms

Similarly to the way `fderiv` uses continuous linear maps
while higher order derivatives use continuous multilinear maps,
this file uses `E → E →L[𝕜] F` instead of continuous alternating maps for 1-forms.

### Differentiability assumptions

The definitions in this file make sense if the path is a piecewise $C^1$ curve.
Poincaré lemma (formalization WIP, see #24019) implies that for a closed 1-form on an open set `U`,
the integral depends on the homotopy class of the path only,
thus we can define the integral along a continuous path
or an element of the fundamental groupoid of `U`.

### Usage of an extra field

The definitions in this file deal with `𝕜`-linear 1-forms.
This allows us to avoid using `ContinuousLinearMap.restrictScalars`
in `HasFDerivWithinAt.curveIntegral_segment_source`
and a future formalization of Poincaré lemma.
-/

@[expose] public section

open Metric MeasureTheory Topology Set Interval AffineMap Convex Filter
open scoped Pointwise unitInterval

section Defs

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {a b : E}

/-- The function `t ↦ ω (γ t) (γ' t)` which appears in the definition of a curve integral.

This definition is used to factor out common parts of lemmas
about `CurveIntegrable` and `curveIntegral`. -/
noncomputable irreducible_def curveIntegralFun (lemma := curveIntegralFun_def')
    (ω : E -> E ->L[𝕜] F) (γ : Path a b) (t : Real) : F :=
  letI : NormedSpace Real E := .restrictScalars Real 𝕜 E
  ω (γ.extend t) (derivWithin γ.extend I t)

/--
Definition of `CurveIntegrable` / `CurveIntegrable` 的定义

English:
definition CurveIntegrable
  signature: (ω : E -> E ->L[𝕜] F) (γ : Path a b)
  body: IntervalIntegrable (curveIntegralFun ω γ) volume 0 1

中文:
定义 Curve整数egrable
  签名: (ω : E -> E ->L[𝕜] F) (γ : 道路 a b)
  定义体: IntervalIntegrable (curveIntegralFun ω γ) volume 0 1

Depends on / 依赖: IntervalIntegrable, curveIntegralFun, volume
-/
def CurveIntegrable (ω : E -> E ->L[𝕜] F) (γ : Path a b) : Prop :=
  IntervalIntegrable (curveIntegralFun ω γ) volume 0 1

/-- Integral of a 1-form `ω : E → E →L[𝕜] F` along a path `γ`,
defined as $\int_0^1 \omega(\gamma(t))(\gamma'(t))$.

The actual definition uses `curveIntegralFun` which uses `Path.extend γ`
and `derivWithin (Path.extend γ) (Set.Icc 0 1) t`,
because calculus-related definitions in Mathlib expect globally defined functions as arguments. -/
noncomputable irreducible_def curveIntegral (lemma := curveIntegral_def')
    (ω : E -> E ->L[𝕜] F) (γ : Path a b) : F :=
  letI : NormedSpace Real F := .restrictScalars Real 𝕜 F
  ∫ t in 0..1, curveIntegralFun ω γ t

@[inherit_doc curveIntegral]
notation3 "∫ᶜ "(...)" in " γ ", "r:67:(scoped ω => curveIntegral ω γ) => r

/--
theorem `curveIntegral_of_not_completeSpace` / 定理 `curveIntegral_of_not_completeSpace`

English:
theorem curveIntegral_of_not_completeSpace
  statement: (h : ¬CompleteSpace F) (ω : E -> E ->L[𝕜] F)
  proof: by
  simp [curveIntegral, intervalIntegral, integral, h]

中文:
定理 curve整数egral_of_not_completeSpace
  结论: (h : ¬完备空间 F) (ω : E -> E ->L[𝕜] F)
  证明: by
  simp [curveIntegral, intervalIntegral, integral, h]

Depends on / 依赖: curveIntegral, integral, intervalIntegral
-/
theorem curveIntegral_of_not_completeSpace (h : ¬CompleteSpace F) (ω : E -> E ->L[𝕜] F)
    (γ : Path a b) : ∫ᶜ x in γ, ω x = 0 := by
  simp [curveIntegral, intervalIntegral, integral, h]

/--
theorem `curveIntegralFun_def` / 定理 `curveIntegralFun_def`

English:
theorem curveIntegralFun_def
  given: [NormedSpace Real E] (ω : E -> E ->L[𝕜] F) (γ : Path a b) (t : Real)
  proof: by
  simp +instances only [curveIntegralFun, NormedSpace.restrictScalars_eq]

中文:
定理 curve整数egralFun_def
  条件: [赋范空间 实数 E] (ω : E -> E ->L[𝕜] F) (γ : 道路 a b) (t : 实数)
  证明: by
  simp +instances only [curveIntegralFun, NormedSpace.restrictScalars_eq]

Depends on / 依赖: NormedSpace, NormedSpace.restrictScalars_eq, curveIntegralFun, instances, restrictScalars_eq
-/
theorem curveIntegralFun_def [NormedSpace Real E] (ω : E -> E ->L[𝕜] F) (γ : Path a b) (t : Real) :
    curveIntegralFun ω γ t = ω (γ.extend t) (derivWithin γ.extend I t) := by
  simp +instances only [curveIntegralFun, NormedSpace.restrictScalars_eq]

/--
theorem `curveIntegral_def` / 定理 `curveIntegral_def`

English:
theorem curveIntegral_def
  given: [NormedSpace Real F] (ω : E -> E ->L[𝕜] F) (γ : Path a b)
  proof: by
  simp +instances only [curveIntegral, NormedSpace.restrictScalars_eq]

中文:
定理 curve整数egral_def
  条件: [赋范空间 实数 F] (ω : E -> E ->L[𝕜] F) (γ : 道路 a b)
  证明: by
  simp +instances only [curveIntegral, NormedSpace.restrictScalars_eq]

Depends on / 依赖: NormedSpace, NormedSpace.restrictScalars_eq, curveIntegral, instances, restrictScalars_eq
-/
theorem curveIntegral_def [NormedSpace Real F] (ω : E -> E ->L[𝕜] F) (γ : Path a b) :
    curveIntegral ω γ = ∫ t in 0..1, curveIntegralFun ω γ t := by
  simp +instances only [curveIntegral, NormedSpace.restrictScalars_eq]

/--
theorem `curveIntegral_eq_intervalIntegral_deriv` / 定理 `curveIntegral_eq_intervalIntegral_deriv`

English:
theorem curveIntegral_eq_intervalIntegral_deriv
  statement: [NormedSpace Real E] [NormedSpace Real F]
  proof: by
  simp only [curveIntegral_def, curveIntegralFun_def]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le zero_le_one]; rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem (by measurability)] with x hx
  rw [derivWithin_of_mem_nhds (by simpa)]

中文:
定理 curve整数egral_eq_interval整数egral_deriv
  结论: [赋范空间 实数 E] [赋范空间 实数 F]
  证明: by
  simp only [curveIntegral_def, curveIntegralFun_def]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le zero_le_one]; rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem (by measurability)] with x hx
  rw [derivWithin_of_mem_nhds (by simpa)]

Depends on / 依赖: ae_restrict_mem, curveIntegralFun_def, curveIntegral_def, derivWithin_of_mem_nhds, filter_upwards, integral_congr_ae_restrict, intervalIntegral, intervalIntegral.integral_congr_ae_restrict, measurability, restrict_Ioo_eq_restrict_Ioc, uIoc_of_le, zero_le_one
-/
theorem curveIntegral_eq_intervalIntegral_deriv [NormedSpace Real E] [NormedSpace Real F]
    (ω : E -> E ->L[𝕜] F) (γ : Path a b) :
    ∫ᶜ x in γ, ω x = ∫ t in 0..1, ω (γ.extend t) (deriv γ.extend t) := by
  simp only [curveIntegral_def, curveIntegralFun_def]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le zero_le_one]; rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem (by measurability)] with x hx
  rw [derivWithin_of_mem_nhds (by simpa)]

end Defs

/-!
### Operations on paths
-/

section PathOperations

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {a b c d : E} {ω : E -> E ->L[𝕜] F}
  {γ γab : Path a b} {γbc : Path b c} {t : Real}

@[simp]
/--
theorem `curveIntegralFun_refl` / 定理 `curveIntegralFun_refl`

English:
theorem curveIntegralFun_refl
  given: (ω : E -> E ->L[𝕜] F) (a : E)
  statement: curveIntegralFun ω (.refl a) = 0
  proof: by
  ext
  simp [curveIntegralFun, ← Function.const_def]

@[simp]

中文:
定理 curve整数egralFun_refl
  条件: (ω : E -> E ->L[𝕜] F) (a : E)
  结论: curve整数egralFun ω (.refl a) = 0
  证明: by
  ext
  simp [curveIntegralFun, ← Function.const_def]

@[simp]

Depends on / 依赖: Function, Function.const_def, const_def, curveIntegralFun
-/
theorem curveIntegralFun_refl (ω : E -> E ->L[𝕜] F) (a : E) : curveIntegralFun ω (.refl a) = 0 := by
  ext
  simp [curveIntegralFun, ← Function.const_def]

@[simp]
/--
theorem `curveIntegral_refl` / 定理 `curveIntegral_refl`

English:
theorem curveIntegral_refl
  given: (ω : E -> E ->L[𝕜] F) (a : E)
  statement: ∫ᶜ x in .refl a, ω x = 0
  proof: by
  simp [curveIntegral]

@[simp]

中文:
定理 curve整数egral_refl
  条件: (ω : E -> E ->L[𝕜] F) (a : E)
  结论: ∫ᶜ x in .refl a, ω x = 0
  证明: by
  simp [curveIntegral]

@[simp]

Depends on / 依赖: curveIntegral
-/
theorem curveIntegral_refl (ω : E -> E ->L[𝕜] F) (a : E) : ∫ᶜ x in .refl a, ω x = 0 := by
  simp [curveIntegral]

@[simp]
/--
theorem `CurveIntegrable.refl` / 定理 `CurveIntegrable.refl`

English:
theorem CurveIntegrable.refl
  given: (ω : E -> E ->L[𝕜] F) (a : E)
  statement: CurveIntegrable ω (.refl a)
  proof: by
  simp [CurveIntegrable, Pi.zero_def]

@[simp]

中文:
定理 Curve整数egrable.refl
  条件: (ω : E -> E ->L[𝕜] F) (a : E)
  结论: Curve整数egrable ω (.refl a)
  证明: by
  simp [CurveIntegrable, Pi.zero_def]

@[simp]

Depends on / 依赖: CurveIntegrable, Pi.zero_def, zero_def
-/
theorem CurveIntegrable.refl (ω : E -> E ->L[𝕜] F) (a : E) : CurveIntegrable ω (.refl a) := by
  simp [CurveIntegrable, Pi.zero_def]

@[simp]
/--
theorem `curveIntegralFun_cast` / 定理 `curveIntegralFun_cast`

English:
theorem curveIntegralFun_cast
  given: (ω : E -> E ->L[𝕜] F) (γ : Path a b) (hc : c = a) (hd : d = b)
  proof: by
  ext t
  simp only [curveIntegralFun_def', Path.extend_cast]

@[simp]

中文:
定理 curve整数egralFun_cast
  条件: (ω : E -> E ->L[𝕜] F) (γ : 道路 a b) (hc : c = a) (hd : d = b)
  证明: by
  ext t
  simp only [curveIntegralFun_def', Path.extend_cast]

@[simp]

Depends on / 依赖: Path.extend_cast, curveIntegralFun_def, extend_cast
-/
theorem curveIntegralFun_cast (ω : E -> E ->L[𝕜] F) (γ : Path a b) (hc : c = a) (hd : d = b) :
    curveIntegralFun ω (γ.cast hc hd) = curveIntegralFun ω γ := by
  ext t
  simp only [curveIntegralFun_def', Path.extend_cast]

@[simp]
/--
theorem `curveIntegral_cast` / 定理 `curveIntegral_cast`

English:
theorem curveIntegral_cast
  given: (ω : E -> E ->L[𝕜] F) (γ : Path a b) (hc : c = a) (hd : d = b)
  proof: by
  simp [curveIntegral]

@[simp]

中文:
定理 curve整数egral_cast
  条件: (ω : E -> E ->L[𝕜] F) (γ : 道路 a b) (hc : c = a) (hd : d = b)
  证明: by
  simp [curveIntegral]

@[simp]

Depends on / 依赖: curveIntegral
-/
theorem curveIntegral_cast (ω : E -> E ->L[𝕜] F) (γ : Path a b) (hc : c = a) (hd : d = b) :
    ∫ᶜ x in γ.cast hc hd, ω x = ∫ᶜ x in γ, ω x := by
  simp [curveIntegral]

@[simp]
/--
theorem `curveIntegrable_cast_iff` / 定理 `curveIntegrable_cast_iff`

English:
theorem curveIntegrable_cast_iff
  given: (hc : c = a) (hd : d = b)
  proof: by
  simp [CurveIntegrable]

protected alias ⟨_, CurveIntegrable.cast⟩ := curveIntegrable_cast_iff

中文:
定理 curve整数egrable_cast_iff
  条件: (hc : c = a) (hd : d = b)
  证明: by
  simp [CurveIntegrable]

protected alias ⟨_, CurveIntegrable.cast⟩ := curveIntegrable_cast_iff

Depends on / 依赖: CurveIntegrable
-/
theorem curveIntegrable_cast_iff (hc : c = a) (hd : d = b) :
    CurveIntegrable ω (γ.cast hc hd) ↔ CurveIntegrable ω γ := by
  simp [CurveIntegrable]

protected alias ⟨_, CurveIntegrable.cast⟩ := curveIntegrable_cast_iff

/--
theorem `curveIntegralFun_symm_apply` / 定理 `curveIntegralFun_symm_apply`

English:
theorem curveIntegralFun_symm_apply
  given: (ω : E -> E ->L[𝕜] F) (γ : Path a b) (t : Real)
  proof: by
  simp [curveIntegralFun, γ.extend_symm, derivWithin_comp_const_sub]

@[simp]

中文:
定理 curve整数egralFun_symm_apply
  条件: (ω : E -> E ->L[𝕜] F) (γ : 道路 a b) (t : 实数)
  证明: by
  simp [curveIntegralFun, γ.extend_symm, derivWithin_comp_const_sub]

@[simp]

Depends on / 依赖: curveIntegralFun, derivWithin_comp_const_sub, extend_symm
-/
theorem curveIntegralFun_symm_apply (ω : E -> E ->L[𝕜] F) (γ : Path a b) (t : Real) :
    curveIntegralFun ω γ.symm t = -curveIntegralFun ω γ (1 - t) := by
  simp [curveIntegralFun, γ.extend_symm, derivWithin_comp_const_sub]

@[simp]
/--
theorem `curveIntegralFun_symm` / 定理 `curveIntegralFun_symm`

English:
theorem curveIntegralFun_symm
  given: (ω : E -> E ->L[𝕜] F) (γ : Path a b)
  proof: funext curveIntegralFun_symm_apply ω γ

中文:
定理 curve整数egralFun_symm
  条件: (ω : E -> E ->L[𝕜] F) (γ : 道路 a b)
  证明: funext curveIntegralFun_symm_apply ω γ

Depends on / 依赖: curveIntegralFun_symm_apply
-/
theorem curveIntegralFun_symm (ω : E -> E ->L[𝕜] F) (γ : Path a b) :
    curveIntegralFun ω γ.symm = (-curveIntegralFun ω γ <| 1 - ·) :=
funext curveIntegralFun_symm_apply ω γ

/--
theorem `CurveIntegrable.symm` / 定理 `CurveIntegrable.symm`

English:
theorem CurveIntegrable.symm
  given: (h : CurveIntegrable ω γ)
  statement: CurveIntegrable ω γ.symm
  proof: by
  simpa [CurveIntegrable] using! (h.comp_sub_left 1).neg.symm

@[simp]

中文:
定理 Curve整数egrable.symm
  条件: (h : Curve整数egrable ω γ)
  结论: Curve整数egrable ω γ.symm
  证明: by
  simpa [CurveIntegrable] using! (h.comp_sub_left 1).neg.symm

@[simp]
-/
protected theorem CurveIntegrable.symm (h : CurveIntegrable ω γ) : CurveIntegrable ω γ.symm := by
  simpa [CurveIntegrable] using! (h.comp_sub_left 1).neg.symm

@[simp]
/--
theorem `curveIntegrable_symm` / 定理 `curveIntegrable_symm`

English:
theorem curveIntegrable_symm
  statement: CurveIntegrable ω γ.symm ↔ CurveIntegrable ω γ
  proof: ⟨fun h => by simpa using h.symm, .symm⟩

@[simp]

中文:
定理 curve整数egrable_symm
  结论: Curve整数egrable ω γ.symm ↔ Curve整数egrable ω γ
  证明: ⟨fun h => by simpa using h.symm, .symm⟩

@[simp]

Depends on / 依赖: h.symm
-/
theorem curveIntegrable_symm : CurveIntegrable ω γ.symm ↔ CurveIntegrable ω γ :=
  ⟨fun h => by simpa using h.symm, .symm⟩

@[simp]
/--
theorem `curveIntegral_symm` / 定理 `curveIntegral_symm`

English:
theorem curveIntegral_symm
  given: (ω : E -> E ->L[𝕜] F) (γ : Path a b)
  proof: by
  simp [curveIntegral, curveIntegralFun_symm]

中文:
定理 curve整数egral_symm
  条件: (ω : E -> E ->L[𝕜] F) (γ : 道路 a b)
  证明: by
  simp [curveIntegral, curveIntegralFun_symm]

Depends on / 依赖: curveIntegral, curveIntegralFun_symm
-/
theorem curveIntegral_symm (ω : E -> E ->L[𝕜] F) (γ : Path a b) :
    ∫ᶜ x in γ.symm, ω x = -∫ᶜ x in γ, ω x := by
  simp [curveIntegral, curveIntegralFun_symm]

/--
theorem `curveIntegralFun_trans_of_lt_half` / 定理 `curveIntegralFun_trans_of_lt_half`

English:
theorem curveIntegralFun_trans_of_lt_half
  statement: (ω : E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c)
  proof: by
  let instE := NormedSpace.restrictScalars Real 𝕜 E
  have H₁ : (γab.trans γbc).extend =ᶠ[𝓝 t] (fun s => γab.extend (2 * s)) :=
    (eventually_le_nhds ht).mono fun _ => Path.extend_trans_of_le_half _ _
  have H₂ : (2 : Real) • I =ᶠ[𝓝 (2 * t)] I := by
    rw [LinearOrderedField.smul_Icc two_pos]; rw [mul_zero]; rw [mul_one]; rw [← nhdsWithin_eq_iff_eventuallyEq]
    rcases lt_trichotomy t 0 with ht₀ | rfl | ht₀
    · rw [notMem_closure_iff_nhdsWithin_eq_bot.mp, notMem_closure_iff_nhdsWithin_eq_bot.mp] <;>
        simp_intro h <;> linarith
    · simp
    · rw [nhdsWithin_eq_nhds.2, nhdsWithin_eq_nhds.2] <;> simp [*] <;> linarith
  rw [curveIntegralFun_def]; rw [H₁.self_of_nhds]; rw [H₁.derivWithin_eq_of_nhds]; rw [curveIntegralFun_def]; rw [derivWithin_comp_mul_left]; rw [ofNat_smul_eq_nsmul]; rw [map_nsmul]; rw [derivWithin_congr_set H₂]

中文:
定理 curve整数egralFun_trans_of_lt_half
  结论: (ω : E -> E ->L[𝕜] F) (γab : 道路 a b) (γbc : 道路 b c)
  证明: by
  let instE := NormedSpace.restrictScalars Real 𝕜 E
  have H₁ : (γab.trans γbc).extend =ᶠ[𝓝 t] (fun s => γab.extend (2 * s)) :=
    (eventually_le_nhds ht).mono fun _ => Path.extend_trans_of_le_half _ _
  have H₂ : (2 : Real) • I =ᶠ[𝓝 (2 * t)] I := by
    rw [LinearOrderedField.smul_Icc two_pos]; rw [mul_zero]; rw [mul_one]; rw [← nhdsWithin_eq_iff_eventuallyEq]
    rcases lt_trichotomy t 0 with ht₀ | rfl | ht₀
    · rw [notMem_closure_iff_nhdsWithin_eq_bot.mp, notMem_closure_iff_nhdsWithin_eq_bot.mp] <;>
        simp_intro h <;> linarith
    · simp
    · rw [nhdsWithin_eq_nhds.2, nhdsWithin_eq_nhds.2] <;> simp [*] <;> linarith
  rw [curveIntegralFun_def]; rw [H₁.self_of_nhds]; rw [H₁.derivWithin_eq_of_nhds]; rw [curveIntegralFun_def]; rw [derivWithin_comp_mul_left]; rw [ofNat_smul_eq_nsmul]; rw [map_nsmul]; rw [derivWithin_congr_set H₂]

Depends on / 依赖: LinearOrderedField, LinearOrderedField.smul_Icc, NormedSpace, NormedSpace.restrictScalars, Path.extend_trans_of_le_half, ab.extend, ab.trans, eventually_le_nhds, extend, extend_trans_of_le_half, lt_trichotomy, mul_one, mul_zero, nhdsWithin_eq_iff_eventuallyEq, notMem_closure_iff_nhdsWithin_eq_bot, notMem_closure_iff_nhdsWithin_eq_bot.mp, restrictScalars, simp_int, smul_Icc, two_pos
-/
theorem curveIntegralFun_trans_of_lt_half (ω : E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c)
    (ht : t < 1 / 2) :
    curveIntegralFun ω (γab.trans γbc) t = (2 : Nat) • curveIntegralFun ω γab (2 * t) := by
  let instE := NormedSpace.restrictScalars Real 𝕜 E
  have H₁ : (γab.trans γbc).extend =ᶠ[𝓝 t] (fun s => γab.extend (2 * s)) :=
    (eventually_le_nhds ht).mono fun _ => Path.extend_trans_of_le_half _ _
  have H₂ : (2 : Real) • I =ᶠ[𝓝 (2 * t)] I := by
    rw [LinearOrderedField.smul_Icc two_pos]; rw [mul_zero]; rw [mul_one]; rw [← nhdsWithin_eq_iff_eventuallyEq]
    rcases lt_trichotomy t 0 with ht₀ | rfl | ht₀
    · rw [notMem_closure_iff_nhdsWithin_eq_bot.mp, notMem_closure_iff_nhdsWithin_eq_bot.mp] <;>
        simp_intro h <;> linarith
    · simp
    · rw [nhdsWithin_eq_nhds.2, nhdsWithin_eq_nhds.2] <;> simp [*] <;> linarith
  rw [curveIntegralFun_def]; rw [H₁.self_of_nhds]; rw [H₁.derivWithin_eq_of_nhds]; rw [curveIntegralFun_def]; rw [derivWithin_comp_mul_left]; rw [ofNat_smul_eq_nsmul]; rw [map_nsmul]; rw [derivWithin_congr_set H₂]

/--
theorem `curveIntegralFun_trans_aeeq_left` / 定理 `curveIntegralFun_trans_aeeq_left`

English:
theorem curveIntegralFun_trans_aeeq_left
  given: (ω : E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c)
  proof: by
  rw [uIoc_of_le (by positivity)]; rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₀, ht⟩
  exact curveIntegralFun_trans_of_lt_half ω γab γbc ht

中文:
定理 curve整数egralFun_trans_aeeq_left
  条件: (ω : E -> E ->L[𝕜] F) (γab : 道路 a b) (γbc : 道路 b c)
  证明: by
  rw [uIoc_of_le (by positivity)]; rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₀, ht⟩
  exact curveIntegralFun_trans_of_lt_half ω γab γbc ht

Depends on / 依赖: ae_restrict_mem, curveIntegralFun_trans_of_lt_half, filter_upwards, measurableSet_Ioo, restrict_Ioo_eq_restrict_Ioc, uIoc_of_le
-/
theorem curveIntegralFun_trans_aeeq_left (ω : E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c) :
    curveIntegralFun ω (γab.trans γbc) =ᵐ[volume.restrict (Ι (0 : Real) (1 / 2))]
      fun t => (2 : Nat) • curveIntegralFun ω γab (2 * t) := by
  rw [uIoc_of_le (by positivity)]; rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₀, ht⟩
  exact curveIntegralFun_trans_of_lt_half ω γab γbc ht

/--
theorem `curveIntegralFun_trans_of_half_lt` / 定理 `curveIntegralFun_trans_of_half_lt`

English:
theorem curveIntegralFun_trans_of_half_lt
  statement: (ω : E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c)
  proof: by
  rw [← (γab.trans γbc).symm_symm]; rw [curveIntegralFun_symm_apply]; rw [Path.trans_symm]; rw [curveIntegralFun_trans_of_lt_half (ht := by linarith)]; rw [curveIntegralFun_symm_apply]; rw [smul_neg]; rw [neg_neg]
  congr 2
  ring

中文:
定理 curve整数egralFun_trans_of_half_lt
  结论: (ω : E -> E ->L[𝕜] F) (γab : 道路 a b) (γbc : 道路 b c)
  证明: by
  rw [← (γab.trans γbc).symm_symm]; rw [curveIntegralFun_symm_apply]; rw [Path.trans_symm]; rw [curveIntegralFun_trans_of_lt_half (ht := by linarith)]; rw [curveIntegralFun_symm_apply]; rw [smul_neg]; rw [neg_neg]
  congr 2
  ring

Depends on / 依赖: Path.trans_symm, ab.trans, curveIntegralFun_symm_apply, curveIntegralFun_trans_of_lt_half, neg_neg, smul_neg, symm_symm, trans_symm
-/
theorem curveIntegralFun_trans_of_half_lt (ω : E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c)
    (ht₀ : 1 / 2 < t) :
    curveIntegralFun ω (γab.trans γbc) t = (2 : Nat) • curveIntegralFun ω γbc (2 * t - 1) := by
  rw [← (γab.trans γbc).symm_symm]; rw [curveIntegralFun_symm_apply]; rw [Path.trans_symm]; rw [curveIntegralFun_trans_of_lt_half (ht := by linarith)]; rw [curveIntegralFun_symm_apply]; rw [smul_neg]; rw [neg_neg]
  congr 2
  ring

/--
theorem `curveIntegralFun_trans_aeeq_right` / 定理 `curveIntegralFun_trans_aeeq_right`

English:
theorem curveIntegralFun_trans_aeeq_right
  given: (ω : E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c)
  proof: by
  rw [uIoc_of_le (by linarith)]; rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₁, ht₂⟩
  exact curveIntegralFun_trans_of_half_lt ω γab γbc ht₁

中文:
定理 curve整数egralFun_trans_aeeq_right
  条件: (ω : E -> E ->L[𝕜] F) (γab : 道路 a b) (γbc : 道路 b c)
  证明: by
  rw [uIoc_of_le (by linarith)]; rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₁, ht₂⟩
  exact curveIntegralFun_trans_of_half_lt ω γab γbc ht₁

Depends on / 依赖: ae_restrict_mem, curveIntegralFun_trans_of_half_lt, filter_upwards, measurableSet_Ioo, restrict_Ioo_eq_restrict_Ioc, uIoc_of_le
-/
theorem curveIntegralFun_trans_aeeq_right (ω : E -> E ->L[𝕜] F) (γab : Path a b) (γbc : Path b c) :
    curveIntegralFun ω (γab.trans γbc) =ᵐ[volume.restrict (Ι (1 / 2 : Real) 1)]
      fun t => (2 : Nat) • curveIntegralFun ω γbc (2 * t - 1) := by
  rw [uIoc_of_le (by linarith)]; rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₁, ht₂⟩
  exact curveIntegralFun_trans_of_half_lt ω γab γbc ht₁

/--
theorem `CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_left` / 定理 `CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_left`

English:
theorem CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_left
  proof: by
  refine .congr_ae ?_ (curveIntegralFun_trans_aeeq_left _ _ _).symm
  simpa [ofNat_smul_eq_nsmul] using! h.comp_mul_left.smul (2 : 𝕜)

中文:
定理 Curve整数egrable.interval整数egrable_curve整数egralFun_trans_left
  证明: by
  refine .congr_ae ?_ (curveIntegralFun_trans_aeeq_left _ _ _).symm
  simpa [ofNat_smul_eq_nsmul] using! h.comp_mul_left.smul (2 : 𝕜)

Depends on / 依赖: comp_mul_left, congr_ae, curveIntegralFun_trans_aeeq_left, h.comp_mul_left.smul, ofNat_smul_eq_nsmul
-/
theorem CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_left
    (h : CurveIntegrable ω γab) (γbc : Path b c) :
    IntervalIntegrable (curveIntegralFun ω (γab.trans γbc)) volume 0 (1 / 2) := by
  refine .congr_ae ?_ (curveIntegralFun_trans_aeeq_left _ _ _).symm
  simpa [ofNat_smul_eq_nsmul] using! h.comp_mul_left.smul (2 : 𝕜)

/--
theorem `CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_right` / 定理 `CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_right`

English:
theorem CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_right
  proof: by
  refine .congr_ae ?_ (curveIntegralFun_trans_aeeq_right _ _ _).symm
.smul (2 : 𝕜) .comp_mul_left (c := 2) simpa [ofNat_smul_eq_nsmul] using! h.comp_sub_right 1

中文:
定理 Curve整数egrable.interval整数egrable_curve整数egralFun_trans_right
  证明: by
  refine .congr_ae ?_ (curveIntegralFun_trans_aeeq_right _ _ _).symm
.smul (2 : 𝕜) .comp_mul_left (c := 2) simpa [ofNat_smul_eq_nsmul] using! h.comp_sub_right 1

Depends on / 依赖: comp_mul_left, comp_sub_right, congr_ae, curveIntegralFun_trans_aeeq_right, h.comp_sub_right, ofNat_smul_eq_nsmul
-/
theorem CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_right
    (γab : Path a b) (h : CurveIntegrable ω γbc) :
    IntervalIntegrable (curveIntegralFun ω (γab.trans γbc)) volume (1 / 2) 1 := by
  refine .congr_ae ?_ (curveIntegralFun_trans_aeeq_right _ _ _).symm
.smul (2 : 𝕜) .comp_mul_left (c := 2) simpa [ofNat_smul_eq_nsmul] using! h.comp_sub_right 1

/--
theorem `CurveIntegrable.trans` / 定理 `CurveIntegrable.trans`

English:
theorem CurveIntegrable.trans
  given: (h₁ : CurveIntegrable ω γab) (h₂ : CurveIntegrable ω γbc)
  proof: (h₁.intervalIntegrable_curveIntegralFun_trans_left γbc).trans
    (h₂.intervalIntegrable_curveIntegralFun_trans_right γab)

中文:
定理 Curve整数egrable.trans
  条件: (h₁ : Curve整数egrable ω γab) (h₂ : Curve整数egrable ω γbc)
  证明: (h₁.intervalIntegrable_curveIntegralFun_trans_left γbc).trans
    (h₂.intervalIntegrable_curveIntegralFun_trans_right γab)
-/
protected theorem CurveIntegrable.trans (h₁ : CurveIntegrable ω γab) (h₂ : CurveIntegrable ω γbc) :
    CurveIntegrable ω (γab.trans γbc) :=
  (h₁.intervalIntegrable_curveIntegralFun_trans_left γbc).trans
    (h₂.intervalIntegrable_curveIntegralFun_trans_right γab)

/--
theorem `curveIntegral_trans` / 定理 `curveIntegral_trans`

English:
theorem curveIntegral_trans
  given: (h₁ : CurveIntegrable ω γab) (h₂ : CurveIntegrable ω γbc)
  proof: by
  let instF := NormedSpace.restrictScalars Real 𝕜 F
  rw [curveIntegral_def]; rw [← intervalIntegral.integral_add_adjacent_intervals
    (h₁.intervalIntegrable_curveIntegralFun_trans_left γbc)
    (h₂.intervalIntegrable_curveIntegralFun_trans_right γab)]; rw [intervalIntegral.integral_congr_ae_restrict (curveIntegralFun_trans_aeeq_left _ _ _)]; rw [intervalIntegral.integral_congr_ae_restrict (curveIntegralFun_trans_aeeq_right _ _ _)]
  simp only [← ofNat_smul_eq_nsmul (R := Real)]
  rw [intervalIntegral.integral_smul]; rw [intervalIntegral.smul_integral_comp_mul_left]; rw [intervalIntegral.integral_smul]; rw [intervalIntegral.smul_integral_comp_mul_left (f := (curveIntegralFun ω γbc <| · - 1))]; rw [intervalIntegral.integral_comp_sub_right]
  simp only [curveIntegral_def]
  norm_num

中文:
定理 curve整数egral_trans
  条件: (h₁ : Curve整数egrable ω γab) (h₂ : Curve整数egrable ω γbc)
  证明: by
  let instF := NormedSpace.restrictScalars Real 𝕜 F
  rw [curveIntegral_def]; rw [← intervalIntegral.integral_add_adjacent_intervals
    (h₁.intervalIntegrable_curveIntegralFun_trans_left γbc)
    (h₂.intervalIntegrable_curveIntegralFun_trans_right γab)]; rw [intervalIntegral.integral_congr_ae_restrict (curveIntegralFun_trans_aeeq_left _ _ _)]; rw [intervalIntegral.integral_congr_ae_restrict (curveIntegralFun_trans_aeeq_right _ _ _)]
  simp only [← ofNat_smul_eq_nsmul (R := Real)]
  rw [intervalIntegral.integral_smul]; rw [intervalIntegral.smul_integral_comp_mul_left]; rw [intervalIntegral.integral_smul]; rw [intervalIntegral.smul_integral_comp_mul_left (f := (curveIntegralFun ω γbc <| · - 1))]; rw [intervalIntegral.integral_comp_sub_right]
  simp only [curveIntegral_def]
  norm_num

Depends on / 依赖: NormedSpace, NormedSpace.restrictScalars, curveIntegralFun_trans_aeeq_left, curveIntegralFun_trans_aeeq_right, curveIntegral_def, integral_add_adjacent_intervals, integral_congr_ae_restrict, intervalIntegrable_curveIntegralFun_trans_left, intervalIntegrable_curveIntegralFun_trans_right, intervalIntegral, intervalIntegral.inte, intervalIntegral.integral_add_adjacent_intervals, intervalIntegral.integral_congr_ae_restrict, ofNat_smul_eq_nsmul, restrictScalars
-/
theorem curveIntegral_trans (h₁ : CurveIntegrable ω γab) (h₂ : CurveIntegrable ω γbc) :
    ∫ᶜ x in γab.trans γbc, ω x = (∫ᶜ x in γab, ω x) + ∫ᶜ x in γbc, ω x := by
  let instF := NormedSpace.restrictScalars Real 𝕜 F
  rw [curveIntegral_def]; rw [← intervalIntegral.integral_add_adjacent_intervals
    (h₁.intervalIntegrable_curveIntegralFun_trans_left γbc)
    (h₂.intervalIntegrable_curveIntegralFun_trans_right γab)]; rw [intervalIntegral.integral_congr_ae_restrict (curveIntegralFun_trans_aeeq_left _ _ _)]; rw [intervalIntegral.integral_congr_ae_restrict (curveIntegralFun_trans_aeeq_right _ _ _)]
  simp only [← ofNat_smul_eq_nsmul (R := Real)]
  rw [intervalIntegral.integral_smul]; rw [intervalIntegral.smul_integral_comp_mul_left]; rw [intervalIntegral.integral_smul]; rw [intervalIntegral.smul_integral_comp_mul_left (f := (curveIntegralFun ω γbc <| · - 1))]; rw [intervalIntegral.integral_comp_sub_right]
  simp only [curveIntegral_def]
  norm_num

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `curveIntegralFun_segment` / 定理 `curveIntegralFun_segment`

English:
theorem curveIntegralFun_segment
  statement: [NormedSpace Real E] (ω : E -> E ->L[𝕜] F) (a b : E)
  proof: by
  have := Path.eqOn_extend_segment a b
  simp only [curveIntegralFun_def, this ht, derivWithin_congr this (this ht),
    (hasDerivWithinAt_lineMap ..).derivWithin (uniqueDiffOn_Icc_zero_one t ht)]

中文:
定理 curve整数egralFun_segment
  结论: [赋范空间 实数 E] (ω : E -> E ->L[𝕜] F) (a b : E)
  证明: by
  have := Path.eqOn_extend_segment a b
  simp only [curveIntegralFun_def, this ht, derivWithin_congr this (this ht),
    (hasDerivWithinAt_lineMap ..).derivWithin (uniqueDiffOn_Icc_zero_one t ht)]

Depends on / 依赖: Path.eqOn_extend_segment, curveIntegralFun_def, derivWithin, derivWithin_congr, eqOn_extend_segment, hasDerivWithinAt_lineMap, uniqueDiffOn_Icc_zero_one
-/
theorem curveIntegralFun_segment [NormedSpace Real E] (ω : E -> E ->L[𝕜] F) (a b : E)
    {t : Real} (ht : t in I) : curveIntegralFun ω (.segment a b) t = ω (lineMap a b t) (b - a) := by
  have := Path.eqOn_extend_segment a b
  simp only [curveIntegralFun_def, this ht, derivWithin_congr this (this ht),
    (hasDerivWithinAt_lineMap ..).derivWithin (uniqueDiffOn_Icc_zero_one t ht)]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `curveIntegrable_segment` / 定理 `curveIntegrable_segment`

English:
theorem curveIntegrable_segment
  given: [NormedSpace Real E]
  proof: by
  rw [CurveIntegrable]; rw [intervalIntegrable_congr]
  rw [uIoc_of_le zero_le_one]
  exact .mono Ioc_subset_Icc_self fun _t => curveIntegralFun_segment ω a b

中文:
定理 curve整数egrable_segment
  条件: [赋范空间 实数 E]
  证明: by
  rw [CurveIntegrable]; rw [intervalIntegrable_congr]
  rw [uIoc_of_le zero_le_one]
  exact .mono Ioc_subset_Icc_self fun _t => curveIntegralFun_segment ω a b

Depends on / 依赖: CurveIntegrable, Ioc_subset_Icc_self, curveIntegralFun_segment, intervalIntegrable_congr, uIoc_of_le, zero_le_one
-/
theorem curveIntegrable_segment [NormedSpace Real E] :
    CurveIntegrable ω (.segment a b) ↔
      IntervalIntegrable (fun t => ω (lineMap a b t) (b - a)) volume 0 1 := by
  rw [CurveIntegrable]; rw [intervalIntegrable_congr]
  rw [uIoc_of_le zero_le_one]
  exact .mono Ioc_subset_Icc_self fun _t => curveIntegralFun_segment ω a b

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `curveIntegral_segment` / 定理 `curveIntegral_segment`

English:
theorem curveIntegral_segment
  given: [NormedSpace Real E] [NormedSpace Real F] (ω : E -> E ->L[𝕜] F) (a b : E)
  proof: by
  rw [curveIntegral_def]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  exact curveIntegralFun_segment ω a b ht

@[simp]

中文:
定理 curve整数egral_segment
  条件: [赋范空间 实数 E] [赋范空间 实数 F] (ω : E -> E ->L[𝕜] F) (a b : E)
  证明: by
  rw [curveIntegral_def]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  exact curveIntegralFun_segment ω a b ht

@[simp]

Depends on / 依赖: curveIntegralFun_segment, curveIntegral_def, integral_congr, intervalIntegral, intervalIntegral.integral_congr, uIcc_of_le, zero_le_one
-/
theorem curveIntegral_segment [NormedSpace Real E] [NormedSpace Real F] (ω : E -> E ->L[𝕜] F) (a b : E) :
    ∫ᶜ x in .segment a b, ω x = ∫ t in 0..1, ω (lineMap a b t) (b - a) := by
  rw [curveIntegral_def]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  exact curveIntegralFun_segment ω a b ht

@[simp]
/--
theorem `curveIntegral_segment_const` / 定理 `curveIntegral_segment_const`

English:
theorem curveIntegral_segment_const
  given: [NormedSpace Real E] [CompleteSpace F] (ω : E ->L[𝕜] F) (a b : E)
  proof: by
  let : NormedSpace Real F := .restrictScalars Real 𝕜 F
  simp [curveIntegral_segment]

中文:
定理 curve整数egral_segment_const
  条件: [赋范空间 实数 E] [完备空间 F] (ω : E ->L[𝕜] F) (a b : E)
  证明: by
  let : NormedSpace Real F := .restrictScalars Real 𝕜 F
  simp [curveIntegral_segment]

Depends on / 依赖: NormedSpace, curveIntegral_segment, restrictScalars
-/
theorem curveIntegral_segment_const [NormedSpace Real E] [CompleteSpace F] (ω : E ->L[𝕜] F) (a b : E) :
    ∫ᶜ _ in .segment a b, ω = ω (b - a) := by
  let : NormedSpace Real F := .restrictScalars Real 𝕜 F
  simp [curveIntegral_segment]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `norm_curveIntegral_segment_le` / 定理 `norm_curveIntegral_segment_le`

English:
theorem norm_curveIntegral_segment_le
  given: [NormedSpace Real E] {C : Real} (h : forall z in [a -[Real] b], ‖ω z‖ <= C)
  proof: calc
  ‖∫ᶜ x in .segment a b, ω x‖ <= C * ‖b - a‖ * |1 - 0| := by
    let : NormedSpace Real F := .restrictScalars Real 𝕜 F
    rw [curveIntegral_segment]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [segment_eq_image_lineMap] at h
    rw [uIoc_of_le zero_le_one] at ht
    apply_rules [(ω _).le_of_opNorm_le, mem_image_of_mem, Ioc_subset_Icc_self]
  _ = C * ‖b - a‖ := by simp

中文:
定理 norm_curve整数egral_segment_le
  条件: [赋范空间 实数 E] {C : 实数} (h : 对任意 z in [a -[实数] b], ‖ω z‖ <= C)
  证明: calc
  ‖∫ᶜ x in .segment a b, ω x‖ <= C * ‖b - a‖ * |1 - 0| := by
    let : NormedSpace Real F := .restrictScalars Real 𝕜 F
    rw [curveIntegral_segment]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [segment_eq_image_lineMap] at h
    rw [uIoc_of_le zero_le_one] at ht
    apply_rules [(ω _).le_of_opNorm_le, mem_image_of_mem, Ioc_subset_Icc_self]
  _ = C * ‖b - a‖ := by simp
-/
theorem norm_curveIntegral_segment_le [NormedSpace Real E] {C : Real} (h : forall z in [a -[Real] b], ‖ω z‖ <= C) :
    ‖∫ᶜ x in .segment a b, ω x‖ <= C * ‖b - a‖ := calc
  ‖∫ᶜ x in .segment a b, ω x‖ <= C * ‖b - a‖ * |1 - 0| := by
    let : NormedSpace Real F := .restrictScalars Real 𝕜 F
    rw [curveIntegral_segment]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [segment_eq_image_lineMap] at h
    rw [uIoc_of_le zero_le_one] at ht
    apply_rules [(ω _).le_of_opNorm_le, mem_image_of_mem, Ioc_subset_Icc_self]
  _ = C * ‖b - a‖ := by simp

/--
theorem `ContinuousOn.curveIntegrable_of_contDiffOn` / 定理 `ContinuousOn.curveIntegrable_of_contDiffOn`

English:
theorem ContinuousOn.curveIntegrable_of_contDiffOn
  statement: [NormedSpace Real E] {s : Set E}
  proof: by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  simp only [funext (curveIntegralFun_def ω γ)]
  apply ContinuousOn.clm_apply
  · exact hω.comp (by fun_prop) fun _ _ => hγs _
  · exact hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl

中文:
定理 ContinuousOn.curve整数egrable_of_contDiffOn
  结论: [赋范空间 实数 E] {s : 集合 E}
  证明: by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  simp only [funext (curveIntegralFun_def ω γ)]
  apply ContinuousOn.clm_apply
  · exact hω.comp (by fun_prop) fun _ _ => hγs _
  · exact hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl

Depends on / 依赖: ContinuousOn, ContinuousOn.clm_apply, ContinuousOn.intervalIntegrable_of_Icc, clm_apply, continuousOn_derivWithin, curveIntegralFun_def, fun_prop, intervalIntegrable_of_Icc, le_rfl, uniqueDiffOn_Icc_zero_one, zero_le_one
-/
theorem ContinuousOn.curveIntegrable_of_contDiffOn [NormedSpace Real E] {s : Set E}
    (hω : ContinuousOn ω s) (hγ : ContDiffOn Real 1 γ.extend I) (hγs : forall t, γ t in s) :
    CurveIntegrable ω γ := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  simp only [funext (curveIntegralFun_def ω γ)]
  apply ContinuousOn.clm_apply
  · exact hω.comp (by fun_prop) fun _ _ => hγs _
  · exact hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl

end PathOperations

/-!
### Algebraic operations on the 1-form
-/

section Algebra

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {a b : E}
  {ω ω₁ ω₂ : E -> E ->L[𝕜] F} {γ : Path a b} {t : Real}

@[simp]
/--
theorem `curveIntegralFun_add` / 定理 `curveIntegralFun_add`

English:
theorem curveIntegralFun_add
  proof: by
  ext; simp [curveIntegralFun]

中文:
定理 curve整数egralFun_add
  证明: by
  ext; simp [curveIntegralFun]

Depends on / 依赖: curveIntegralFun
-/
theorem curveIntegralFun_add :
    curveIntegralFun (ω₁ + ω₂) γ = curveIntegralFun ω₁ γ + curveIntegralFun ω₂ γ := by
  ext; simp [curveIntegralFun]

/--
theorem `CurveIntegrable.add` / 定理 `CurveIntegrable.add`

English:
theorem CurveIntegrable.add
  given: (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ)
  proof: by
  simpa [CurveIntegrable] using! IntervalIntegrable.add h₁ h₂

中文:
定理 Curve整数egrable.add
  条件: (h₁ : Curve整数egrable ω₁ γ) (h₂ : Curve整数egrable ω₂ γ)
  证明: by
  simpa [CurveIntegrable] using! IntervalIntegrable.add h₁ h₂
-/
protected theorem CurveIntegrable.add (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    CurveIntegrable (ω₁ + ω₂) γ := by
  simpa [CurveIntegrable] using! IntervalIntegrable.add h₁ h₂

-- TODO: `to_fun` generates wrong lemma name
/--
theorem `curveIntegral_add` / 定理 `curveIntegral_add`

English:
theorem curveIntegral_add
  given: (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ)
  proof: by
  let : NormedSpace Real F := .restrictScalars Real 𝕜 F
  simp only [curveIntegral, curveIntegralFun_add]
  exact intervalIntegral.integral_add h₁ h₂

中文:
定理 curve整数egral_add
  条件: (h₁ : Curve整数egrable ω₁ γ) (h₂ : Curve整数egrable ω₂ γ)
  证明: by
  let : NormedSpace Real F := .restrictScalars Real 𝕜 F
  simp only [curveIntegral, curveIntegralFun_add]
  exact intervalIntegral.integral_add h₁ h₂

Depends on / 依赖: NormedSpace, curveIntegral, curveIntegralFun_add, integral_add, intervalIntegral, intervalIntegral.integral_add, restrictScalars
-/
theorem curveIntegral_add (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    curveIntegral (ω₁ + ω₂) γ = ∫ᶜ x in γ, ω₁ x + ∫ᶜ x in γ, ω₂ x := by
  let : NormedSpace Real F := .restrictScalars Real 𝕜 F
  simp only [curveIntegral, curveIntegralFun_add]
  exact intervalIntegral.integral_add h₁ h₂

/--
theorem `curveIntegral_fun_add` / 定理 `curveIntegral_fun_add`

English:
theorem curveIntegral_fun_add
  given: (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ)
  proof: curveIntegral_add h₁ h₂

@[simp]

中文:
定理 curve整数egral_fun_add
  条件: (h₁ : Curve整数egrable ω₁ γ) (h₂ : Curve整数egrable ω₂ γ)
  证明: curveIntegral_add h₁ h₂

@[simp]

Depends on / 依赖: curveIntegral_add
-/
theorem curveIntegral_fun_add (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    ∫ᶜ x in γ, (ω₁ x + ω₂ x) = ∫ᶜ x in γ, ω₁ x + ∫ᶜ x in γ, ω₂ x :=
  curveIntegral_add h₁ h₂

@[simp]
/--
theorem `curveIntegralFun_zero` / 定理 `curveIntegralFun_zero`

English:
theorem curveIntegralFun_zero
  statement: curveIntegralFun (0 : E -> E ->L[𝕜] F) γ = 0
  proof: by
  ext; simp [curveIntegralFun]

@[simp]

中文:
定理 curve整数egralFun_zero
  结论: curve整数egralFun (0 : E -> E ->L[𝕜] F) γ = 0
  证明: by
  ext; simp [curveIntegralFun]

@[simp]

Depends on / 依赖: curveIntegralFun
-/
theorem curveIntegralFun_zero : curveIntegralFun (0 : E -> E ->L[𝕜] F) γ = 0 := by
  ext; simp [curveIntegralFun]

@[simp]
/--
theorem `curveIntegralFun_fun_zero` / 定理 `curveIntegralFun_fun_zero`

English:
theorem curveIntegralFun_fun_zero
  statement: curveIntegralFun (fun _ => 0 : E -> E ->L[𝕜] F) γ = 0
  proof: curveIntegralFun_zero

@[to_fun]

中文:
定理 curve整数egralFun_fun_zero
  结论: curve整数egralFun (fun _ => 0 : E -> E ->L[𝕜] F) γ = 0
  证明: curveIntegralFun_zero

@[to_fun]

Depends on / 依赖: curveIntegralFun_zero
-/
theorem curveIntegralFun_fun_zero : curveIntegralFun (fun _ => 0 : E -> E ->L[𝕜] F) γ = 0 :=
  curveIntegralFun_zero

@[to_fun]
/--
theorem `CurveIntegrable.zero` / 定理 `CurveIntegrable.zero`

English:
theorem CurveIntegrable.zero
  statement: CurveIntegrable (0 : E -> E ->L[𝕜] F) γ
  proof: by
  simp [CurveIntegrable, IntervalIntegrable.zero]

@[simp]

中文:
定理 Curve整数egrable.zero
  结论: Curve整数egrable (0 : E -> E ->L[𝕜] F) γ
  证明: by
  simp [CurveIntegrable, IntervalIntegrable.zero]

@[simp]

Depends on / 依赖: CurveIntegrable, IntervalIntegrable, IntervalIntegrable.zero
-/
theorem CurveIntegrable.zero : CurveIntegrable (0 : E -> E ->L[𝕜] F) γ := by
  simp [CurveIntegrable, IntervalIntegrable.zero]

@[simp]
/--
theorem `curveIntegral_zero` / 定理 `curveIntegral_zero`

English:
theorem curveIntegral_zero
  statement: curveIntegral (0 : E -> E ->L[𝕜] F) γ = 0
  proof: by simp [curveIntegral]

@[simp]

中文:
定理 curve整数egral_zero
  结论: curve整数egral (0 : E -> E ->L[𝕜] F) γ = 0
  证明: by simp [curveIntegral]

@[simp]

Depends on / 依赖: curveIntegral
-/
theorem curveIntegral_zero : curveIntegral (0 : E -> E ->L[𝕜] F) γ = 0 := by simp [curveIntegral]

@[simp]
/--
theorem `curveIntegral_fun_zero` / 定理 `curveIntegral_fun_zero`

English:
theorem curveIntegral_fun_zero
  statement: ∫ᶜ _ in γ, (0 : E ->L[𝕜] F) = 0
  proof: curveIntegral_zero

@[simp]

中文:
定理 curve整数egral_fun_zero
  结论: ∫ᶜ _ in γ, (0 : E ->L[𝕜] F) = 0
  证明: curveIntegral_zero

@[simp]

Depends on / 依赖: curveIntegral_zero
-/
theorem curveIntegral_fun_zero : ∫ᶜ _ in γ, (0 : E ->L[𝕜] F) = 0 := curveIntegral_zero

@[simp]
/--
theorem `curveIntegralFun_neg` / 定理 `curveIntegralFun_neg`

English:
theorem curveIntegralFun_neg
  statement: curveIntegralFun (-ω) γ = -curveIntegralFun ω γ
  proof: by
  ext; simp [curveIntegralFun]

@[to_fun]

中文:
定理 curve整数egralFun_neg
  结论: curve整数egralFun (-ω) γ = -curve整数egralFun ω γ
  证明: by
  ext; simp [curveIntegralFun]

@[to_fun]

Depends on / 依赖: curveIntegralFun
-/
theorem curveIntegralFun_neg : curveIntegralFun (-ω) γ = -curveIntegralFun ω γ := by
  ext; simp [curveIntegralFun]

@[to_fun]
/--
theorem `CurveIntegrable.neg` / 定理 `CurveIntegrable.neg`

English:
theorem CurveIntegrable.neg
  given: (h : CurveIntegrable ω γ)
  statement: CurveIntegrable (-ω) γ
  proof: by
  simpa [CurveIntegrable] using IntervalIntegrable.neg h

@[simp]

中文:
定理 Curve整数egrable.neg
  条件: (h : Curve整数egrable ω γ)
  结论: Curve整数egrable (-ω) γ
  证明: by
  simpa [CurveIntegrable] using IntervalIntegrable.neg h

@[simp]

Depends on / 依赖: CurveIntegrable, IntervalIntegrable, IntervalIntegrable.neg
-/
theorem CurveIntegrable.neg (h : CurveIntegrable ω γ) : CurveIntegrable (-ω) γ := by
  simpa [CurveIntegrable] using IntervalIntegrable.neg h

@[simp]
/--
theorem `curveIntegrable_neg_iff` / 定理 `curveIntegrable_neg_iff`

English:
theorem curveIntegrable_neg_iff
  statement: CurveIntegrable (-ω) γ ↔ CurveIntegrable ω γ
  proof: ⟨fun h => by simpa using h.neg, .neg⟩

@[simp]

中文:
定理 curve整数egrable_neg_iff
  结论: Curve整数egrable (-ω) γ ↔ Curve整数egrable ω γ
  证明: ⟨fun h => by simpa using h.neg, .neg⟩

@[simp]

Depends on / 依赖: h.neg
-/
theorem curveIntegrable_neg_iff : CurveIntegrable (-ω) γ ↔ CurveIntegrable ω γ :=
  ⟨fun h => by simpa using h.neg, .neg⟩

@[simp]
/--
theorem `curveIntegrable_fun_neg_iff` / 定理 `curveIntegrable_fun_neg_iff`

English:
theorem curveIntegrable_fun_neg_iff
  statement: CurveIntegrable (-ω ·) γ ↔ CurveIntegrable ω γ
  proof: curveIntegrable_neg_iff

@[simp]

中文:
定理 curve整数egrable_fun_neg_iff
  结论: Curve整数egrable (-ω ·) γ ↔ Curve整数egrable ω γ
  证明: curveIntegrable_neg_iff

@[simp]

Depends on / 依赖: curveIntegrable_neg_iff
-/
theorem curveIntegrable_fun_neg_iff : CurveIntegrable (-ω ·) γ ↔ CurveIntegrable ω γ :=
  curveIntegrable_neg_iff

@[simp]
/--
theorem `curveIntegral_neg` / 定理 `curveIntegral_neg`

English:
theorem curveIntegral_neg
  statement: curveIntegral (-ω) γ = -∫ᶜ x in γ, ω x
  proof: by
  simp [curveIntegral]

@[simp]

中文:
定理 curve整数egral_neg
  结论: curve整数egral (-ω) γ = -∫ᶜ x in γ, ω x
  证明: by
  simp [curveIntegral]

@[simp]

Depends on / 依赖: curveIntegral
-/
theorem curveIntegral_neg : curveIntegral (-ω) γ = -∫ᶜ x in γ, ω x := by
  simp [curveIntegral]

@[simp]
/--
theorem `curveIntegral_fun_neg` / 定理 `curveIntegral_fun_neg`

English:
theorem curveIntegral_fun_neg
  statement: ∫ᶜ x in γ, -ω x = -∫ᶜ x in γ, ω x
  proof: curveIntegral_neg

@[simp]

中文:
定理 curve整数egral_fun_neg
  结论: ∫ᶜ x in γ, -ω x = -∫ᶜ x in γ, ω x
  证明: curveIntegral_neg

@[simp]

Depends on / 依赖: curveIntegral_neg
-/
theorem curveIntegral_fun_neg : ∫ᶜ x in γ, -ω x = -∫ᶜ x in γ, ω x := curveIntegral_neg

@[simp]
/--
theorem `curveIntegralFun_sub` / 定理 `curveIntegralFun_sub`

English:
theorem curveIntegralFun_sub
  proof: by
  simp [sub_eq_add_neg]

中文:
定理 curve整数egralFun_sub
  证明: by
  simp [sub_eq_add_neg]

Depends on / 依赖: sub_eq_add_neg
-/
theorem curveIntegralFun_sub :
    curveIntegralFun (ω₁ - ω₂) γ = curveIntegralFun ω₁ γ - curveIntegralFun ω₂ γ := by
  simp [sub_eq_add_neg]

/--
theorem `CurveIntegrable.sub` / 定理 `CurveIntegrable.sub`

English:
theorem CurveIntegrable.sub
  given: (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ)
  proof: sub_eq_add_neg ω₁ ω₂ ▸ h₁.add h₂.neg

中文:
定理 Curve整数egrable.sub
  条件: (h₁ : Curve整数egrable ω₁ γ) (h₂ : Curve整数egrable ω₂ γ)
  证明: sub_eq_add_neg ω₁ ω₂ ▸ h₁.add h₂.neg
-/
protected theorem CurveIntegrable.sub (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    CurveIntegrable (ω₁ - ω₂) γ :=
  sub_eq_add_neg ω₁ ω₂ ▸ h₁.add h₂.neg

/--
theorem `curveIntegral_sub` / 定理 `curveIntegral_sub`

English:
theorem curveIntegral_sub
  given: (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ)
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [curveIntegral_add h₁ h₂.neg]; rw [curveIntegral_neg]

中文:
定理 curve整数egral_sub
  条件: (h₁ : Curve整数egrable ω₁ γ) (h₂ : Curve整数egrable ω₂ γ)
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [curveIntegral_add h₁ h₂.neg]; rw [curveIntegral_neg]

Depends on / 依赖: curveIntegral_add, curveIntegral_neg, sub_eq_add_neg
-/
theorem curveIntegral_sub (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    curveIntegral (ω₁ - ω₂) γ = ∫ᶜ x in γ, ω₁ x - ∫ᶜ x in γ, ω₂ x := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [curveIntegral_add h₁ h₂.neg]; rw [curveIntegral_neg]

/--
theorem `curveIntegral_fun_sub` / 定理 `curveIntegral_fun_sub`

English:
theorem curveIntegral_fun_sub
  given: (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ)
  proof: curveIntegral_sub h₁ h₂

中文:
定理 curve整数egral_fun_sub
  条件: (h₁ : Curve整数egrable ω₁ γ) (h₂ : Curve整数egrable ω₂ γ)
  证明: curveIntegral_sub h₁ h₂

Depends on / 依赖: curveIntegral_sub
-/
theorem curveIntegral_fun_sub (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    ∫ᶜ x in γ, (ω₁ x - ω₂ x) = ∫ᶜ x in γ, ω₁ x - ∫ᶜ x in γ, ω₂ x :=
  curveIntegral_sub h₁ h₂


section RestrictScalars

variable {𝕝 : Type*} [RCLike 𝕝] [NormedSpace 𝕝 F] [NormedSpace 𝕝 E]
  [LinearMap.CompatibleSMul E F 𝕝 𝕜]

@[simp]
/--
theorem `curveIntegralFun_restrictScalars` / 定理 `curveIntegralFun_restrictScalars`

English:
theorem curveIntegralFun_restrictScalars
  proof: by
  ext
  let : NormedSpace Real E := .restrictScalars Real 𝕜 E
  simp [curveIntegralFun_def]

@[simp]

中文:
定理 curve整数egralFun_restrictScalars
  证明: by
  ext
  let : NormedSpace Real E := .restrictScalars Real 𝕜 E
  simp [curveIntegralFun_def]

@[simp]

Depends on / 依赖: NormedSpace, curveIntegralFun_def, restrictScalars
-/
theorem curveIntegralFun_restrictScalars :
    curveIntegralFun (fun t => (ω t).restrictScalars 𝕝) γ = curveIntegralFun ω γ := by
  ext
  let : NormedSpace Real E := .restrictScalars Real 𝕜 E
  simp [curveIntegralFun_def]

@[simp]
/--
theorem `curveIntegrable_restrictScalars_iff` / 定理 `curveIntegrable_restrictScalars_iff`

English:
theorem curveIntegrable_restrictScalars_iff
  proof: by
  simp [CurveIntegrable]

@[simp]

中文:
定理 curve整数egrable_restrictScalars_iff
  证明: by
  simp [CurveIntegrable]

@[simp]

Depends on / 依赖: CurveIntegrable
-/
theorem curveIntegrable_restrictScalars_iff :
    CurveIntegrable (fun t => (ω t).restrictScalars 𝕝) γ ↔ CurveIntegrable ω γ := by
  simp [CurveIntegrable]

@[simp]
/--
theorem `curveIntegral_restrictScalars` / 定理 `curveIntegral_restrictScalars`

English:
theorem curveIntegral_restrictScalars
  proof: by
  let : NormedSpace Real F := .restrictScalars Real 𝕜 F
  simp [curveIntegral_def]

中文:
定理 curve整数egral_restrictScalars
  证明: by
  let : NormedSpace Real F := .restrictScalars Real 𝕜 F
  simp [curveIntegral_def]

Depends on / 依赖: NormedSpace, curveIntegral_def, restrictScalars
-/
theorem curveIntegral_restrictScalars :
    ∫ᶜ x in γ, (ω x).restrictScalars 𝕝 = ∫ᶜ x in γ, ω x := by
  let : NormedSpace Real F := .restrictScalars Real 𝕜 F
  simp [curveIntegral_def]

end RestrictScalars

variable {𝕝 : Type*} [RCLike 𝕝] [NormedSpace 𝕝 F] [SMulCommClass 𝕜 𝕝 F] {c : 𝕝}

@[simp]
/--
theorem `curveIntegralFun_smul` / 定理 `curveIntegralFun_smul`

English:
theorem curveIntegralFun_smul
  statement: curveIntegralFun (c • ω) γ = c • curveIntegralFun ω γ
  proof: by
  ext
  simp [curveIntegralFun]

中文:
定理 curve整数egralFun_smul
  结论: curve整数egralFun (c • ω) γ = c • curve整数egralFun ω γ
  证明: by
  ext
  simp [curveIntegralFun]

Depends on / 依赖: curveIntegralFun
-/
theorem curveIntegralFun_smul : curveIntegralFun (c • ω) γ = c • curveIntegralFun ω γ := by
  ext
  simp [curveIntegralFun]

/--
theorem `CurveIntegrable.smul` / 定理 `CurveIntegrable.smul`

English:
theorem CurveIntegrable.smul
  given: (h : CurveIntegrable ω γ)
  proof: by
  simpa [CurveIntegrable] using IntervalIntegrable.smul h c

@[simp]

中文:
定理 Curve整数egrable.smul
  条件: (h : Curve整数egrable ω γ)
  证明: by
  simpa [CurveIntegrable] using IntervalIntegrable.smul h c

@[simp]

Depends on / 依赖: CurveIntegrable, IntervalIntegrable, IntervalIntegrable.smul
-/
theorem CurveIntegrable.smul (h : CurveIntegrable ω γ) :
    CurveIntegrable (c • ω) γ := by
  simpa [CurveIntegrable] using IntervalIntegrable.smul h c

@[simp]
/--
theorem `curveIntegrable_smul_iff` / 定理 `curveIntegrable_smul_iff`

English:
theorem curveIntegrable_smul_iff
  statement: CurveIntegrable (c • ω) γ ↔ c = 0 ∨ CurveIntegrable ω γ
  proof: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [CurveIntegrable.zero]
  · simp only [hc, false_or]
    refine ⟨fun h => ?_, .smul⟩
    simpa [hc] using h.smul (c := c⁻¹)

@[simp]

中文:
定理 curve整数egrable_smul_iff
  结论: Curve整数egrable (c • ω) γ ↔ c = 0 ∨ Curve整数egrable ω γ
  证明: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [CurveIntegrable.zero]
  · simp only [hc, false_or]
    refine ⟨fun h => ?_, .smul⟩
    simpa [hc] using h.smul (c := c⁻¹)

@[simp]

Depends on / 依赖: CurveIntegrable, CurveIntegrable.zero, eq_or_ne, false_or, h.smul
-/
theorem curveIntegrable_smul_iff : CurveIntegrable (c • ω) γ ↔ c = 0 ∨ CurveIntegrable ω γ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [CurveIntegrable.zero]
  · simp only [hc, false_or]
    refine ⟨fun h => ?_, .smul⟩
    simpa [hc] using h.smul (c := c⁻¹)

@[simp]
/--
theorem `curveIntegral_smul` / 定理 `curveIntegral_smul`

English:
theorem curveIntegral_smul
  statement: curveIntegral (c • ω) γ = c • curveIntegral ω γ
  proof: by
  let : NormedSpace Real F := .restrictScalars Real 𝕜 F
  simp [curveIntegral_def, intervalIntegral.integral_smul]

@[simp]

中文:
定理 curve整数egral_smul
  结论: curve整数egral (c • ω) γ = c • curve整数egral ω γ
  证明: by
  let : NormedSpace Real F := .restrictScalars Real 𝕜 F
  simp [curveIntegral_def, intervalIntegral.integral_smul]

@[simp]

Depends on / 依赖: NormedSpace, curveIntegral_def, integral_smul, intervalIntegral, intervalIntegral.integral_smul, restrictScalars
-/
theorem curveIntegral_smul : curveIntegral (c • ω) γ = c • curveIntegral ω γ := by
  let : NormedSpace Real F := .restrictScalars Real 𝕜 F
  simp [curveIntegral_def, intervalIntegral.integral_smul]

@[simp]
/--
theorem `curveIntegral_fun_smul` / 定理 `curveIntegral_fun_smul`

English:
theorem curveIntegral_fun_smul
  statement: ∫ᶜ x in γ, c • ω x = c • ∫ᶜ x in γ, ω x
  proof: curveIntegral_smul

中文:
定理 curve整数egral_fun_smul
  结论: ∫ᶜ x in γ, c • ω x = c • ∫ᶜ x in γ, ω x
  证明: curveIntegral_smul

Depends on / 依赖: curveIntegral_smul
-/
theorem curveIntegral_fun_smul : ∫ᶜ x in γ, c • ω x = c • ∫ᶜ x in γ, ω x := curveIntegral_smul

end Algebra

section FDeriv

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace Real E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {a b : E} {s : Set E} {ω : E -> E ->L[𝕜] F}

/-!
### Derivative of the curve integral w.r.t. the right endpoint

In this section we prove that the integral of `ω` along `[a -[ℝ] b]`, as a function of `b`,
has derivative `ω a` at `b = a`.
We provide several versions of this theorem, for `HasFDerivWithinAt` and `HasFDerivAt`,
as well as for continuity near a point and for continuity on the whole set or space.

Note that we take the derivative at the left endpoint of the segment.
Similar facts about the derivative at a different point are true
provided that `ω` is a closed 1-form (formalization WIP, see #24019).
-/

/--
theorem `HasFDerivWithinAt.curveIntegral_segment_source'` / 定理 `HasFDerivWithinAt.curveIntegral_segment_source'`

English:
theorem HasFDerivWithinAt.curveIntegral_segment_source'
  statement: (hs : Convex Real s)
  proof: by
  /- Given `ε > 0`, take a number `δ > 0` such that `ω` is continuous on `ball a δ ∩ s`
  and `‖ω z - ω a‖ ≤ ε` on this set.
  Then for `b ∈ ball a δ ∩ s`, we have
  `‖(∫ᶜ x in .segment a b, ω x) - ω a (b - a)‖
    = ‖(∫ᶜ x in .segment a b, ω x) - ∫ᶜ x in .segment a b, ω a‖
    ≤ ∫ x in 0..1, ‖ω x - ω a‖ * ‖b - a‖
    ≤ ε * ‖b - a‖`
  -/
  simp only [hasFDerivWithinAt_iff_isLittleO, Path.segment_same, curveIntegral_refl, sub_zero,
    Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ₀, hδ⟩ : exists δ > 0,
      ball a δ inter s subseteq {z | ContinuousWithinAt ω s z ∧ dist (ω z) (ω a) <= ε} := by
    rw [← Metric.mem_nhdsWithin_iff]; rw [ofPred_and]; rw [inter_mem_iff]
exact ⟨hω, (hω.self_of_nhdsWithin ha).eventually closedBall_mem_nhds _ hε⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds _ hδ₀] with b hb hbs
  have hsub : [a -[Real] b] subseteq ball a δ inter s :=
    ((convex_ball _ _).inter hs).segment_subset (by simp [*]) (by simp [*])
  rw [← curveIntegral_segment_const]; rw [← curveIntegral_fun_sub]
  · refine norm_curveIntegral_segment_le fun z hz => ?_
    simpa [dist_eq_norm] using (hδ (hsub hz)).2
  · rw [curveIntegrable_segment]
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one fun t ht => ?_
    refine ((hδ ?_).1.eval_const _).comp AffineMap.lineMap_continuous.continuousWithinAt ?_
· exact hsub lineMap_mem_segment Real a b ht
    · rw [mapsTo_iff_image_subset, ← segment_eq_image_lineMap]
      exact hs.segment_subset ha hbs
  · rw [curveIntegrable_segment]
    exact intervalIntegrable_const

中文:
定理 HasFDerivWithinAt.curve整数egral_segment_source'
  结论: (hs : 凸 实数 s)
  证明: by
  /- Given `ε > 0`, take a number `δ > 0` such that `ω` is continuous on `ball a δ ∩ s`
  and `‖ω z - ω a‖ ≤ ε` on this set.
  Then for `b ∈ ball a δ ∩ s`, we have
  `‖(∫ᶜ x in .segment a b, ω x) - ω a (b - a)‖
    = ‖(∫ᶜ x in .segment a b, ω x) - ∫ᶜ x in .segment a b, ω a‖
    ≤ ∫ x in 0..1, ‖ω x - ω a‖ * ‖b - a‖
    ≤ ε * ‖b - a‖`
  -/
  simp only [hasFDerivWithinAt_iff_isLittleO, Path.segment_same, curveIntegral_refl, sub_zero,
    Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ₀, hδ⟩ : exists δ > 0,
      ball a δ inter s subseteq {z | ContinuousWithinAt ω s z ∧ dist (ω z) (ω a) <= ε} := by
    rw [← Metric.mem_nhdsWithin_iff]; rw [ofPred_and]; rw [inter_mem_iff]
exact ⟨hω, (hω.self_of_nhdsWithin ha).eventually closedBall_mem_nhds _ hε⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds _ hδ₀] with b hb hbs
  have hsub : [a -[Real] b] subseteq ball a δ inter s :=
    ((convex_ball _ _).inter hs).segment_subset (by simp [*]) (by simp [*])
  rw [← curveIntegral_segment_const]; rw [← curveIntegral_fun_sub]
  · refine norm_curveIntegral_segment_le fun z hz => ?_
    simpa [dist_eq_norm] using (hδ (hsub hz)).2
  · rw [curveIntegrable_segment]
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one fun t ht => ?_
    refine ((hδ ?_).1.eval_const _).comp AffineMap.lineMap_continuous.continuousWithinAt ?_
· exact hsub lineMap_mem_segment Real a b ht
    · rw [mapsTo_iff_image_subset, ← segment_eq_image_lineMap]
      exact hs.segment_subset ha hbs
  · rw [curveIntegrable_segment]
    exact intervalIntegrable_const
-/
theorem HasFDerivWithinAt.curveIntegral_segment_source' (hs : Convex Real s)
    (hω : forallᶠ x in 𝓝[s] a, ContinuousWithinAt ω s x) (ha : a in s) :
    HasFDerivWithinAt (∫ᶜ x in .segment a ·, ω x) (ω a) s a := by
  /- Given `ε > 0`, take a number `δ > 0` such that `ω` is continuous on `ball a δ ∩ s`
  and `‖ω z - ω a‖ ≤ ε` on this set.
  Then for `b ∈ ball a δ ∩ s`, we have
  `‖(∫ᶜ x in .segment a b, ω x) - ω a (b - a)‖
    = ‖(∫ᶜ x in .segment a b, ω x) - ∫ᶜ x in .segment a b, ω a‖
    ≤ ∫ x in 0..1, ‖ω x - ω a‖ * ‖b - a‖
    ≤ ε * ‖b - a‖`
  -/
  simp only [hasFDerivWithinAt_iff_isLittleO, Path.segment_same, curveIntegral_refl, sub_zero,
    Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ₀, hδ⟩ : exists δ > 0,
      ball a δ inter s subseteq {z | ContinuousWithinAt ω s z ∧ dist (ω z) (ω a) <= ε} := by
    rw [← Metric.mem_nhdsWithin_iff]; rw [ofPred_and]; rw [inter_mem_iff]
exact ⟨hω, (hω.self_of_nhdsWithin ha).eventually closedBall_mem_nhds _ hε⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds _ hδ₀] with b hb hbs
  have hsub : [a -[Real] b] subseteq ball a δ inter s :=
    ((convex_ball _ _).inter hs).segment_subset (by simp [*]) (by simp [*])
  rw [← curveIntegral_segment_const]; rw [← curveIntegral_fun_sub]
  · refine norm_curveIntegral_segment_le fun z hz => ?_
    simpa [dist_eq_norm] using (hδ (hsub hz)).2
  · rw [curveIntegrable_segment]
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one fun t ht => ?_
    refine ((hδ ?_).1.eval_const _).comp AffineMap.lineMap_continuous.continuousWithinAt ?_
· exact hsub lineMap_mem_segment Real a b ht
    · rw [mapsTo_iff_image_subset, ← segment_eq_image_lineMap]
      exact hs.segment_subset ha hbs
  · rw [curveIntegrable_segment]
    exact intervalIntegrable_const

/--
theorem `HasFDerivWithinAt.curveIntegral_segment_source` / 定理 `HasFDerivWithinAt.curveIntegral_segment_source`

English:
theorem HasFDerivWithinAt.curveIntegral_segment_source
  statement: (hs : Convex Real s) (hω : ContinuousOn ω s)
  proof: .curveIntegral_segment_source' hs (mem_of_superset self_mem_nhdsWithin hω) ha

中文:
定理 HasFDerivWithinAt.curve整数egral_segment_source
  结论: (hs : 凸 实数 s) (hω : ContinuousOn ω s)
  证明: .curveIntegral_segment_source' hs (mem_of_superset self_mem_nhdsWithin hω) ha

Depends on / 依赖: curveIntegral_segment_source, mem_of_superset, self_mem_nhdsWithin
-/
theorem HasFDerivWithinAt.curveIntegral_segment_source (hs : Convex Real s) (hω : ContinuousOn ω s)
    (ha : a in s) : HasFDerivWithinAt (∫ᶜ x in .segment a ·, ω x) (ω a) s a :=
  .curveIntegral_segment_source' hs (mem_of_superset self_mem_nhdsWithin hω) ha

/--
theorem `HasFDerivAt.curveIntegral_segment_source'` / 定理 `HasFDerivAt.curveIntegral_segment_source'`

English:
theorem HasFDerivAt.curveIntegral_segment_source'
  given: (hω : forallᶠ z in 𝓝 a, ContinuousAt ω z)
  proof: HasFDerivWithinAt.curveIntegral_segment_source' convex_univ
.hasFDerivAt_of_univ (by simpa only [nhdsWithin_univ, continuousWithinAt_univ]) (mem_univ _)

中文:
定理 在点处Fréchet可导.curve整数egral_segment_source'
  条件: (hω : 对任意ᶠ z in 𝓝 a, ContinuousAt ω z)
  证明: HasFDerivWithinAt.curveIntegral_segment_source' convex_univ
.hasFDerivAt_of_univ (by simpa only [nhdsWithin_univ, continuousWithinAt_univ]) (mem_univ _)

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.curveIntegral_segment_source, continuousWithinAt_univ, convex_univ, curveIntegral_segment_source, hasFDerivAt_of_univ, mem_univ, nhdsWithin_univ
-/
theorem HasFDerivAt.curveIntegral_segment_source' (hω : forallᶠ z in 𝓝 a, ContinuousAt ω z) :
    HasFDerivAt (∫ᶜ x in .segment a ·, ω x) (ω a) a :=
  HasFDerivWithinAt.curveIntegral_segment_source' convex_univ
.hasFDerivAt_of_univ (by simpa only [nhdsWithin_univ, continuousWithinAt_univ]) (mem_univ _)

/--
theorem `HasFDerivAt.curveIntegral_segment_source` / 定理 `HasFDerivAt.curveIntegral_segment_source`

English:
theorem HasFDerivAt.curveIntegral_segment_source
  given: (hω : Continuous ω)
  proof: .curveIntegral_segment_source' .of_forall fun _ => hω.continuousAt

中文:
定理 在点处Fréchet可导.curve整数egral_segment_source
  条件: (hω : 连续 ω)
  证明: .curveIntegral_segment_source' .of_forall fun _ => hω.continuousAt

Depends on / 依赖: continuousAt, curveIntegral_segment_source, of_forall
-/
theorem HasFDerivAt.curveIntegral_segment_source (hω : Continuous ω) :
    HasFDerivAt (∫ᶜ x in .segment a ·, ω x) (ω a) a :=
.curveIntegral_segment_source' .of_forall fun _ => hω.continuousAt

end FDeriv
