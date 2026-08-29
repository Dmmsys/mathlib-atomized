/-
Copyright (c) 2022 Cuma Kökmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cuma Kökmen, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integral over a torus in `ℂⁿ`

In this file we define the integral of a function `f : ℂⁿ → E` over a torus
`{z : ℂⁿ | ∀ i, z i ∈ Metric.sphere (c i) (R i)}`. In order to do this, we define
`torusMap (c : ℂⁿ) (R θ : ℝⁿ)` to be the point in `ℂⁿ` given by $z_k=c_k+R_ke^{θ_ki}$,
where $i$ is the imaginary unit, then define `torusIntegral f c R` as the integral over
the cube $[0, (fun _ ↦ 2π)] = \{θ\|∀ k, 0 ≤ θ_k ≤ 2π\}$ of the Jacobian of the
`torusMap` multiplied by `f (torusMap c R θ)`.

We also define a predicate saying that `f ∘ torusMap c R` is integrable on the cube
`[0, (fun _ ↦ 2π)]`.

## Main definitions

* `torusMap c R`: the generalized multidimensional exponential map from `ℝⁿ` to `ℂⁿ` that sends
  $θ=(θ_0,…,θ_{n-1})$ to $z=(z_0,…,z_{n-1})$, where $z_k= c_k + R_ke^{θ_k i}$;

* `TorusIntegrable f c R`: a function `f : ℂⁿ → E` is integrable over the generalized torus
  with center `c : ℂⁿ` and radius `R : ℝⁿ` if `f ∘ torusMap c R` is integrable on the
  closed cube `Icc (0 : ℝⁿ) (fun _ ↦ 2 * π)`;

* `torusIntegral f c R`: the integral of a function `f : ℂⁿ → E` over a torus with
  center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ` defined as
  $\iiint_{[0, 2 * π]} (∏_{k = 1}^{n} i R_k e^{θ_k * i}) • f (c + Re^{θ_k i})\,dθ_0…dθ_{k-1}$.

## Main statements

* `torusIntegral_dim0`, `torusIntegral_dim1`, `torusIntegral_succ`: formulas for `torusIntegral`
  in cases of dimension `0`, `1`, and `n + 1`.

## Notation

- `ℝ⁰`, `ℝ¹`, `ℝⁿ`, `ℝⁿ⁺¹`: local notation for `Fin 0 → ℝ`, `Fin 1 → ℝ`, `Fin n → ℝ`, and
  `Fin (n + 1) → ℝ`, respectively;
- `ℂ⁰`, `ℂ¹`, `ℂⁿ`, `ℂⁿ⁺¹`: local notation for `Fin 0 → ℂ`, `Fin 1 → ℂ`, `Fin n → ℂ`, and
  `Fin (n + 1) → ℂ`, respectively;
- `∯ z in T(c, R), f z`: notation for `torusIntegral f c R`;
- `∮ z in C(c, R), f z`: notation for `circleIntegral f c R`, defined elsewhere;
- `∏ k, f k`: notation for `Finset.prod`, defined elsewhere;
- `π`: notation for `Real.pi`, defined elsewhere.

## Tags

integral, torus
-/

@[expose] public section


variable {n : Nat}
variable {E : Type*} [NormedAddCommGroup E]

noncomputable section

open Complex Set MeasureTheory Function Filter TopologicalSpace
open Mathlib.Tactic (superscriptTerm)

open scoped Real

local syntax:arg term:max noWs superscriptTerm : term
local macro_rules | `($t:term$n:superscript) => `(Fin $n -> $t)

/-!
### `torusMap`, a parametrization of a torus
-/

/--
Definition of `torusMap` / `torusMap` 的定义

English:
definition torusMap
  signature: (c : Complexⁿ) (R : Realⁿ)
  body: fun θ i => c i + R i * exp (θ i * I)

中文:
定义 torusMap
  签名: (c : Complexⁿ) (R : 实数ⁿ)
  定义体: fun θ i => c i + R i * exp (θ i * I)
-/
def torusMap (c : Complexⁿ) (R : Realⁿ) : Realⁿ -> Complexⁿ := fun θ i => c i + R i * exp (θ i * I)

/--
theorem `torusMap_sub_center` / 定理 `torusMap_sub_center`

English:
theorem torusMap_sub_center
  given: (c : Complexⁿ) (R : Realⁿ) (θ : Realⁿ)
  statement: torusMap c R θ - c = torusMap 0 R θ
  proof: by
  ext1 i; simp [torusMap]

中文:
定理 torusMap_sub_center
  条件: (c : Complexⁿ) (R : 实数ⁿ) (θ : 实数ⁿ)
  结论: torusMap c R θ - c = torusMap 0 R θ
  证明: by
  ext1 i; simp [torusMap]

Depends on / 依赖: torusMap
-/
theorem torusMap_sub_center (c : Complexⁿ) (R : Realⁿ) (θ : Realⁿ) : torusMap c R θ - c = torusMap 0 R θ := by
  ext1 i; simp [torusMap]

/--
theorem `torusMap_eq_center_iff` / 定理 `torusMap_eq_center_iff`

English:
theorem torusMap_eq_center_iff
  given: {c : Complexⁿ} {R : Realⁿ} {θ : Realⁿ}
  statement: torusMap c R θ = c ↔ R = 0
  proof: by
  simp [funext_iff, torusMap, exp_ne_zero]

@[simp]

中文:
定理 torusMap_eq_center_iff
  条件: {c : Complexⁿ} {R : 实数ⁿ} {θ : 实数ⁿ}
  结论: torusMap c R θ = c ↔ R = 0
  证明: by
  simp [funext_iff, torusMap, exp_ne_zero]

@[simp]

Depends on / 依赖: exp_ne_zero, funext_iff, torusMap
-/
theorem torusMap_eq_center_iff {c : Complexⁿ} {R : Realⁿ} {θ : Realⁿ} : torusMap c R θ = c ↔ R = 0 := by
  simp [funext_iff, torusMap, exp_ne_zero]

@[simp]
/--
theorem `torusMap_zero_radius` / 定理 `torusMap_zero_radius`

English:
theorem torusMap_zero_radius
  given: (c : Complexⁿ)
  statement: torusMap c 0 = const Realⁿ c
  proof: funext fun _ => torusMap_eq_center_iff.2 rfl

中文:
定理 torusMap_zero_radius
  条件: (c : Complexⁿ)
  结论: torusMap c 0 = const 实数ⁿ c
  证明: funext fun _ => torusMap_eq_center_iff.2 rfl

Depends on / 依赖: torusMap_eq_center_iff
-/
theorem torusMap_zero_radius (c : Complexⁿ) : torusMap c 0 = const Realⁿ c :=
  funext fun _ => torusMap_eq_center_iff.2 rfl

/-!
### Integrability of a function on a generalized torus
-/

/--
Definition of `TorusIntegrable` / `TorusIntegrable` 的定义

English:
definition TorusIntegrable
  signature: (f : Complexⁿ -> E) (c : Complexⁿ) (R : Realⁿ)
  body: IntegrableOn (fun θ : Realⁿ => f (torusMap c R θ)) (Icc (0 : Realⁿ) fun _ => 2 * π) volume

中文:
定义 TorusIntegrable
  签名: (f : Complexⁿ -> E) (c : Complexⁿ) (R : 实数ⁿ)
  定义体: IntegrableOn (fun θ : Realⁿ => f (torusMap c R θ)) (Icc (0 : Realⁿ) fun _ => 2 * π) volume

Depends on / 依赖: IntegrableOn, torusMap, volume
-/
def TorusIntegrable (f : Complexⁿ -> E) (c : Complexⁿ) (R : Realⁿ) : Prop :=
  IntegrableOn (fun θ : Realⁿ => f (torusMap c R θ)) (Icc (0 : Realⁿ) fun _ => 2 * π) volume

namespace TorusIntegrable

variable {f g : Complexⁿ -> E} {c : Complexⁿ} {R : Realⁿ}

/--
theorem `torusIntegrable_const` / 定理 `torusIntegrable_const`

English:
theorem torusIntegrable_const
  given: (a : E) (c : Complexⁿ) (R : Realⁿ)
  statement: TorusIntegrable (fun _ => a) c R
  proof: by
  simp [TorusIntegrable, measure_Icc_lt_top]

中文:
定理 torusIntegrable_const
  条件: (a : E) (c : Complexⁿ) (R : 实数ⁿ)
  结论: Torus整数egrable (fun _ => a) c R
  证明: by
  simp [TorusIntegrable, measure_Icc_lt_top]

Depends on / 依赖: TorusIntegrable, measure_Icc_lt_top
-/
theorem torusIntegrable_const (a : E) (c : Complexⁿ) (R : Realⁿ) : TorusIntegrable (fun _ => a) c R := by
  simp [TorusIntegrable, measure_Icc_lt_top]

/-- If `f` is torus integrable then `-f` is torus integrable. -/
protected nonrec theorem neg (hf : TorusIntegrable f c R) : TorusIntegrable (-f) c R := hf.neg

/-- If `f` and `g` are two torus integrable functions, then so is `f + g`. -/
protected nonrec theorem add (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    TorusIntegrable (f + g) c R :=
  hf.add hg

/-- If `f` and `g` are two torus integrable functions, then so is `f - g`. -/
protected nonrec theorem sub (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    TorusIntegrable (f - g) c R :=
  hf.sub hg

/--
theorem `torusIntegrable_zero_radius` / 定理 `torusIntegrable_zero_radius`

English:
theorem torusIntegrable_zero_radius
  given: {f : Complexⁿ -> E} {c : Complexⁿ}
  statement: TorusIntegrable f c 0
  proof: by
  rw [TorusIntegrable]; rw [torusMap_zero_radius]
  apply torusIntegrable_const (f c) c 0

中文:
定理 torusIntegrable_zero_radius
  条件: {f : Complexⁿ -> E} {c : Complexⁿ}
  结论: Torus整数egrable f c 0
  证明: by
  rw [TorusIntegrable]; rw [torusMap_zero_radius]
  apply torusIntegrable_const (f c) c 0

Depends on / 依赖: TorusIntegrable, torusIntegrable_const, torusMap_zero_radius
-/
theorem torusIntegrable_zero_radius {f : Complexⁿ -> E} {c : Complexⁿ} : TorusIntegrable f c 0 := by
  rw [TorusIntegrable]; rw [torusMap_zero_radius]
  apply torusIntegrable_const (f c) c 0

/--
theorem `function_integrable` / 定理 `function_integrable`

English:
theorem function_integrable
  given: [NormedSpace Complex E] (hf : TorusIntegrable f c R)
  proof: by
  refine (hf.norm.const_mul (∏ i, |R i|)).mono' ?_ ?_
  · refine (Continuous.aestronglyMeasurable ?_).smul hf.1; fun_prop
  simp [norm_smul]

中文:
定理 function_integrable
  条件: [NormedSpace Complex E] (hf : Torus整数egrable f c R)
  证明: by
  refine (hf.norm.const_mul (∏ i, |R i|)).mono' ?_ ?_
  · refine (Continuous.aestronglyMeasurable ?_).smul hf.1; fun_prop
  simp [norm_smul]

Depends on / 依赖: Continuous, Continuous.aestronglyMeasurable, aestronglyMeasurable, const_mul, fun_prop, hf.norm.const_mul, norm_smul
-/
theorem function_integrable [NormedSpace Complex E] (hf : TorusIntegrable f c R) :
    IntegrableOn (fun θ : Realⁿ => (∏ i, R i * exp (θ i * I) * I : Complex) • f (torusMap c R θ))
      (Icc (0 : Realⁿ) fun _ => 2 * π) volume := by
  refine (hf.norm.const_mul (∏ i, |R i|)).mono' ?_ ?_
  · refine (Continuous.aestronglyMeasurable ?_).smul hf.1; fun_prop
  simp [norm_smul]

end TorusIntegrable

variable [NormedSpace Complex E] {f g : Complexⁿ -> E} {c : Complexⁿ} {R : Realⁿ}

/--
Definition of `torusIntegral` / `torusIntegral` 的定义

English:
definition torusIntegral
  signature: (f : Complexⁿ -> E) (c : Complexⁿ) (R : Realⁿ)
  body: ∫ θ : Realⁿ in Icc (0 : Realⁿ) fun _ => 2 * π, (∏ i, R i * exp (θ i * I) * I : Complex) • f (torusMap c R θ)

@[inherit_doc torusIntegral]
notation3 "∯ " (...) " in " "T(" c ", " R ")" ", " r:(scoped f => torusIntegral f c R) => r

中文:
定义 torusIntegral
  签名: (f : Complexⁿ -> E) (c : Complexⁿ) (R : 实数ⁿ)
  定义体: ∫ θ : Realⁿ in Icc (0 : Realⁿ) fun _ => 2 * π, (∏ i, R i * exp (θ i * I) * I : Complex) • f (torusMap c R θ)

@[inherit_doc torusIntegral]
notation3 "∯ " (...) " in " "T(" c ", " R ")" ", " r:(scoped f => torusIntegral f c R) => r

Depends on / 依赖: torusMap
-/
def torusIntegral (f : Complexⁿ -> E) (c : Complexⁿ) (R : Realⁿ) :=
  ∫ θ : Realⁿ in Icc (0 : Realⁿ) fun _ => 2 * π, (∏ i, R i * exp (θ i * I) * I : Complex) • f (torusMap c R θ)

@[inherit_doc torusIntegral]
notation3 "∯ " (...) " in " "T(" c ", " R ")" ", " r:(scoped f => torusIntegral f c R) => r

/--
theorem `torusIntegral_radius_zero` / 定理 `torusIntegral_radius_zero`

English:
theorem torusIntegral_radius_zero
  given: (hn : n != 0) (f : Complexⁿ -> E) (c : Complexⁿ)
  proof: by
  simp only [torusIntegral, Pi.zero_apply, ofReal_zero, zero_mul, Fin.prod_const,
    zero_pow hn, zero_smul, integral_zero]

中文:
定理 torusIntegral_radius_zero
  条件: (hn : n != 0) (f : Complexⁿ -> E) (c : Complexⁿ)
  证明: by
  simp only [torusIntegral, Pi.zero_apply, ofReal_zero, zero_mul, Fin.prod_const,
    zero_pow hn, zero_smul, integral_zero]

Depends on / 依赖: Fin.prod_const, Pi.zero_apply, integral_zero, ofReal_zero, prod_const, torusIntegral, zero_apply, zero_mul, zero_pow, zero_smul
-/
theorem torusIntegral_radius_zero (hn : n != 0) (f : Complexⁿ -> E) (c : Complexⁿ) :
    (∯ x in T(c, 0), f x) = 0 := by
  simp only [torusIntegral, Pi.zero_apply, ofReal_zero, zero_mul, Fin.prod_const,
    zero_pow hn, zero_smul, integral_zero]

/--
theorem `torusIntegral_neg` / 定理 `torusIntegral_neg`

English:
theorem torusIntegral_neg
  given: (f : Complexⁿ -> E) (c : Complexⁿ) (R : Realⁿ)
  proof: by simp [torusIntegral, integral_neg]

中文:
定理 torusIntegral_neg
  条件: (f : Complexⁿ -> E) (c : Complexⁿ) (R : 实数ⁿ)
  证明: by simp [torusIntegral, integral_neg]

Depends on / 依赖: integral_neg, torusIntegral
-/
theorem torusIntegral_neg (f : Complexⁿ -> E) (c : Complexⁿ) (R : Realⁿ) :
    (∯ x in T(c, R), -f x) = -∯ x in T(c, R), f x := by simp [torusIntegral, integral_neg]

/--
theorem `torusIntegral_add` / 定理 `torusIntegral_add`

English:
theorem torusIntegral_add
  given: (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R)
  proof: by
  simpa only [torusIntegral, smul_add, Pi.add_apply] using
    integral_add hf.function_integrable hg.function_integrable

中文:
定理 torusIntegral_add
  条件: (hf : Torus整数egrable f c R) (hg : Torus整数egrable g c R)
  证明: by
  simpa only [torusIntegral, smul_add, Pi.add_apply] using
    integral_add hf.function_integrable hg.function_integrable

Depends on / 依赖: Pi.add_apply, add_apply, function_integrable, hf.function_integrable, hg.function_integrable, integral_add, smul_add, torusIntegral
-/
theorem torusIntegral_add (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    (∯ x in T(c, R), f x + g x) = (∯ x in T(c, R), f x) + ∯ x in T(c, R), g x := by
  simpa only [torusIntegral, smul_add, Pi.add_apply] using
    integral_add hf.function_integrable hg.function_integrable

/--
theorem `torusIntegral_sub` / 定理 `torusIntegral_sub`

English:
theorem torusIntegral_sub
  given: (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R)
  proof: by
  simpa only [sub_eq_add_neg, ← torusIntegral_neg] using! torusIntegral_add hf hg.neg

中文:
定理 torusIntegral_sub
  条件: (hf : Torus整数egrable f c R) (hg : Torus整数egrable g c R)
  证明: by
  simpa only [sub_eq_add_neg, ← torusIntegral_neg] using! torusIntegral_add hf hg.neg

Depends on / 依赖: hg.neg, sub_eq_add_neg, torusIntegral_add, torusIntegral_neg
-/
theorem torusIntegral_sub (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    (∯ x in T(c, R), f x - g x) = (∯ x in T(c, R), f x) - ∯ x in T(c, R), g x := by
  simpa only [sub_eq_add_neg, ← torusIntegral_neg] using! torusIntegral_add hf hg.neg

/--
theorem `torusIntegral_smul` / 定理 `torusIntegral_smul`

English:
theorem torusIntegral_smul
  statement: {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 Complex E] (a : 𝕜)
  proof: by
  simp only [torusIntegral, integral_smul, ← smul_comm a (_ : Complex) (_ : E)]

中文:
定理 torusIntegral_smul
  结论: {𝕜 : 类型} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 Complex E] (a : 𝕜)
  证明: by
  simp only [torusIntegral, integral_smul, ← smul_comm a (_ : Complex) (_ : E)]

Depends on / 依赖: integral_smul, smul_comm, torusIntegral
-/
theorem torusIntegral_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 Complex E] (a : 𝕜)
    (f : Complexⁿ -> E) (c : Complexⁿ) (R : Realⁿ) : (∯ x in T(c, R), a • f x) = a • ∯ x in T(c, R), f x := by
  simp only [torusIntegral, integral_smul, ← smul_comm a (_ : Complex) (_ : E)]

/--
theorem `torusIntegral_const_mul` / 定理 `torusIntegral_const_mul`

English:
theorem torusIntegral_const_mul
  given: (a : Complex) (f : Complexⁿ -> Complex) (c : Complexⁿ) (R : Realⁿ)
  proof: torusIntegral_smul a f c R

中文:
定理 torusIntegral_const_mul
  条件: (a : Complex) (f : Complexⁿ -> Complex) (c : Complexⁿ) (R : 实数ⁿ)
  证明: torusIntegral_smul a f c R

Depends on / 依赖: torusIntegral_smul
-/
theorem torusIntegral_const_mul (a : Complex) (f : Complexⁿ -> Complex) (c : Complexⁿ) (R : Realⁿ) :
    (∯ x in T(c, R), a * f x) = a * ∯ x in T(c, R), f x :=
  torusIntegral_smul a f c R

/--
theorem `norm_torusIntegral_le_of_norm_le_const` / 定理 `norm_torusIntegral_le_of_norm_le_const`

English:
theorem norm_torusIntegral_le_of_norm_le_const
  given: {C : Real} (hf : forall θ, ‖f (torusMap c R θ)‖ <= C)
  proof: calc
    ‖∯ x in T(c, R), f x‖ <= (∏ i, |R i|) * C * (volume (Icc (0 : Realⁿ) fun _ => 2 * π)).toReal :=
      norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top fun θ _ =>
        calc
          ‖(∏ i : Fin n, R i * exp (θ i * I) * I : Complex) • f (torusMap c R θ)‖ =
              (∏ i : Fin 

中文:
定理 norm_torusIntegral_le_of_norm_le_const
  条件: {C : 实数} (hf : 对任意 θ, ‖f (torusMap c R θ)‖ <= C)
  证明: calc
    ‖∯ x in T(c, R), f x‖ <= (∏ i, |R i|) * C * (volume (Icc (0 : Realⁿ) fun _ => 2 * π)).toReal :=
      norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top fun θ _ =>
        calc
          ‖(∏ i : Fin n, R i * exp (θ i * I) * I : Complex) • f (torusMap c R θ)‖ =
              (∏ i : Fin 

Depends on / 依赖: Pi.zero_def, Real.volume_Icc_pi_toReal, measure_Icc_lt_top, mul_le_mul_of_nonneg_left, norm_setIntegral_le_of_norm_le_const, norm_smul, toReal, torusMap, volume, volume_Icc_pi_toReal, zero_def
-/
theorem norm_torusIntegral_le_of_norm_le_const {C : Real} (hf : forall θ, ‖f (torusMap c R θ)‖ <= C) :
    ‖∯ x in T(c, R), f x‖ <= ((2 * π) ^ (n : Nat) * ∏ i, |R i|) * C :=
  calc
    ‖∯ x in T(c, R), f x‖ <= (∏ i, |R i|) * C * (volume (Icc (0 : Realⁿ) fun _ => 2 * π)).toReal :=
      norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top fun θ _ =>
        calc
          ‖(∏ i : Fin n, R i * exp (θ i * I) * I : Complex) • f (torusMap c R θ)‖ =
              (∏ i : Fin n, |R i|) * ‖f (torusMap c R θ)‖ := by simp [norm_smul]
_ <= (∏ i : Fin n, |R i|) * C := mul_le_mul_of_nonneg_left (hf _) by positivity
    _ = ((2 * π) ^ (n : Nat) * ∏ i, |R i|) * C := by
      simp only [Pi.zero_def, Real.volume_Icc_pi_toReal fun _ => Real.two_pi_pos.le, sub_zero,
        Fin.prod_const, mul_assoc, mul_comm ((2 * π) ^ (n : Nat))]

@[simp]
/--
theorem `torusIntegral_dim0` / 定理 `torusIntegral_dim0`

English:
theorem torusIntegral_dim0
  statement: [CompleteSpace E]
  proof: by
  simp only [torusIntegral, Fin.prod_univ_zero, one_smul,
    Subsingleton.elim (fun _ : Fin 0 => 2 * π) 0, Icc_self, Measure.restrict_singleton, volume_pi,
    integral_dirac, Measure.pi_of_empty (fun _ : Fin 0 => volume) 0,
    Measure.dirac_apply_of_mem (mem_singleton _), Subsingleton.elim (to

中文:
定理 torusIntegral_dim0
  结论: [CompleteSpace E]
  证明: by
  simp only [torusIntegral, Fin.prod_univ_zero, one_smul,
    Subsingleton.elim (fun _ : Fin 0 => 2 * π) 0, Icc_self, Measure.restrict_singleton, volume_pi,
    integral_dirac, Measure.pi_of_empty (fun _ : Fin 0 => volume) 0,
    Measure.dirac_apply_of_mem (mem_singleton _), Subsingleton.elim (to

Depends on / 依赖: Fin.prod_univ_zero, Icc_self, Measure, Measure.dirac_apply_of_mem, Measure.pi_of_empty, Measure.restrict_singleton, Subsingleton, Subsingleton.elim, dirac_apply_of_mem, integral_dirac, mem_singleton, one_smul, pi_of_empty, prod_univ_zero, restrict_singleton, torusIntegral, torusMap, volume, volume_pi
-/
theorem torusIntegral_dim0 [CompleteSpace E]
    (f : Complex⁰ -> E) (c : Complex⁰) (R : Real⁰) : (∯ x in T(c, R), f x) = f c := by
  simp only [torusIntegral, Fin.prod_univ_zero, one_smul,
    Subsingleton.elim (fun _ : Fin 0 => 2 * π) 0, Icc_self, Measure.restrict_singleton, volume_pi,
    integral_dirac, Measure.pi_of_empty (fun _ : Fin 0 => volume) 0,
    Measure.dirac_apply_of_mem (mem_singleton _), Subsingleton.elim (torusMap c R 0) c]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `torusIntegral_dim1` / 定理 `torusIntegral_dim1`

English:
theorem torusIntegral_dim1
  given: (f : Complex¹ -> E) (c : Complex¹) (R : Real¹)
  proof: by
  have H₁ : (((MeasurableEquiv.funUnique _ _).symm) ⁻¹' Icc 0 fun _ => 2 * π) = Icc 0 (2 * π) :=
    (OrderIso.funUnique (Fin 1) Real).symm.preimage_Icc _ _
  have H₂ : torusMap c R = fun θ _ => circleMap (c 0) (R 0) (θ 0) := by
    ext θ i : 2
    rw [Subsingleton.elim i 0]; rfl
  rw [torusInteg

中文:
定理 torusIntegral_dim1
  条件: (f : Complex¹ -> E) (c : Complex¹) (R : 实数¹)
  证明: by
  have H₁ : (((MeasurableEquiv.funUnique _ _).symm) ⁻¹' Icc 0 fun _ => 2 * π) = Icc 0 (2 * π) :=
    (OrderIso.funUnique (Fin 1) Real).symm.preimage_Icc _ _
  have H₂ : torusMap c R = fun θ _ => circleMap (c 0) (R 0) (θ 0) := by
    ext θ i : 2
    rw [Subsingleton.elim i 0]; rfl
  rw [torusInteg

Depends on / 依赖: Ioc_ae_eq_Icc, MeasurableEquiv, MeasurableEquiv.funUnique, Measure, Measure.restrict_congr_set, OrderIso, OrderIso.funUnique, Real.two_pi_pos.le, Subsingleton, Subsingleton.elim, circleIntegral, circleMap, funUnique, integral_of_le, intervalIntegral, intervalIntegral.integral_of_le, preimage_Icc, restrict_congr_set, setIntegral_preimage_emb, symm.preimage_Icc
-/
theorem torusIntegral_dim1 (f : Complex¹ -> E) (c : Complex¹) (R : Real¹) :
    (∯ x in T(c, R), f x) = ∮ z in C(c 0, R 0), f fun _ => z := by
  have H₁ : (((MeasurableEquiv.funUnique _ _).symm) ⁻¹' Icc 0 fun _ => 2 * π) = Icc 0 (2 * π) :=
    (OrderIso.funUnique (Fin 1) Real).symm.preimage_Icc _ _
  have H₂ : torusMap c R = fun θ _ => circleMap (c 0) (R 0) (θ 0) := by
    ext θ i : 2
    rw [Subsingleton.elim i 0]; rfl
  rw [torusIntegral]; rw [circleIntegral]; rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]; rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]; rw [← ((volume_preserving_funUnique (Fin 1) Real).symm _).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding _)]; rw [H₁]; rw [H₂]
  simp [circleMap_zero]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `torusIntegral_succAbove` / 定理 `torusIntegral_succAbove`

English:
theorem torusIntegral_succAbove
  proof: by
  set e : Real × Realⁿ ≃ᵐ Realⁿ⁺¹ := (MeasurableEquiv.piFinSuccAbove (fun _ => Real) i).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Real) i).symm _
  have heπ : (e ⁻¹' Icc 0 fun _ => 2 * π) = Icc 0 (2 * π) ×ˢ Icc (0 : Realⁿ) fun _ => 2 * 

中文:
定理 torusIntegral_succAbove
  证明: by
  set e : Real × Realⁿ ≃ᵐ Realⁿ⁺¹ := (MeasurableEquiv.piFinSuccAbove (fun _ => Real) i).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Real) i).symm _
  have heπ : (e ⁻¹' Icc 0 fun _ => 2 * π) = Icc 0 (2 * π) ×ˢ Icc (0 : Realⁿ) fun _ => 2 * 

Depends on / 依赖: Fin.insertNthOrderIso, Icc_prod_eq, MeasurableEquiv, MeasurableEquiv.piFinSuccAbove, Measure, Measure.volume_eq_prod, MeasurePreserving, hem.map_eq, insertNthOrderIso, map_eq, piFinSuccAbove, preimage_Icc, setIntegra, setIntegral_map_equiv, torusIntegral, volume_eq_prod, volume_preserving_piFinSuccAbove
-/
theorem torusIntegral_succAbove
    {f : Complexⁿ⁺¹ -> E} {c : Complexⁿ⁺¹} {R : Realⁿ⁺¹} (hf : TorusIntegrable f c R)
    (i : Fin (n + 1)) :
    (∯ x in T(c, R), f x) =
      ∮ x in C(c i, R i), ∯ y in T(c ∘ i.succAbove, R ∘ i.succAbove), f (i.insertNth x y) := by
  set e : Real × Realⁿ ≃ᵐ Realⁿ⁺¹ := (MeasurableEquiv.piFinSuccAbove (fun _ => Real) i).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Real) i).symm _
  have heπ : (e ⁻¹' Icc 0 fun _ => 2 * π) = Icc 0 (2 * π) ×ˢ Icc (0 : Realⁿ) fun _ => 2 * π :=
    ((Fin.insertNthOrderIso (fun _ => Real) i).preimage_Icc _ _).trans (Icc_prod_eq _ _)
  rw [torusIntegral]; rw [← hem.map_eq]; rw [setIntegral_map_equiv]; rw [heπ]; rw [Measure.volume_eq_prod]; rw [setIntegral_prod]; rw [circleIntegral_def_Icc]
  · refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    simp +unfoldPartialApp only [e, torusIntegral, ← integral_smul,
      deriv_circleMap, i.prod_univ_succAbove _, smul_smul, torusMap, circleMap_zero]
    refine setIntegral_congr_fun measurableSet_Icc fun Θ _ => ?_
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, i.insertNth_apply_same,
      i.insertNth_apply_succAbove, (· ∘ ·), Fin.insertNthEquiv, Equiv.coe_fn_mk]
    congr 2
    simp only [funext_iff, i.forall_iff_succAbove, circleMap, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, imp_true_iff, and_self_iff]
  · have := hf.function_integrable
    rwa [← hem.integrableOn_comp_preimage e.measurableEmbedding, heπ] at this

/--
theorem `torusIntegral_succ` / 定理 `torusIntegral_succ`

English:
theorem torusIntegral_succ
  proof: by
  simpa using torusIntegral_succAbove hf 0

中文:
定理 torusIntegral_succ
  证明: by
  simpa using torusIntegral_succAbove hf 0

Depends on / 依赖: torusIntegral_succAbove
-/
theorem torusIntegral_succ
    {f : Complexⁿ⁺¹ -> E} {c : Complexⁿ⁺¹} {R : Realⁿ⁺¹} (hf : TorusIntegrable f c R) :
    (∯ x in T(c, R), f x) =
      ∮ x in C(c 0, R 0), ∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ), f (Fin.cons x y) := by
  simpa using torusIntegral_succAbove hf 0
