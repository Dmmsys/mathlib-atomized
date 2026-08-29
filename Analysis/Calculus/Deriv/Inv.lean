/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Derivatives of `x ↦ x⁻¹` and `f x / g x`

In this file we prove `(x⁻¹)' = -1 / x ^ 2`, `((f x)⁻¹)' = -f' x / (f x) ^ 2`, and
`(f x / g x)' = (f' x * g x - f x * g' x) / (g x) ^ 2` for different notions of derivative.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative
-/

public section


universe u

open scoped Topology
open Filter Asymptotics Set

open ContinuousLinearMap (toSpanSingleton)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}

section Inverse


/--
theorem `hasStrictDerivAt_inv` / 定理 `hasStrictDerivAt_inv`

English:
theorem hasStrictDerivAt_inv
  given: (hx : x != 0)
  statement: HasStrictDerivAt Inv.inv (-(x ^ 2)⁻¹) x
  proof: by
  suffices
    (fun p : 𝕜 × 𝕜 => (p.1 - p.2) * ((x * x)⁻¹ - (p.1 * p.2)⁻¹)) =o[𝓝 (x, x)] fun p =>
      (p.1 - p.2) * 1 by
refine .of_isLittleO this.congr' ?_ (Eventually.of_forall fun _ => mul_one _)
    refine Eventually.mono ((isOpen_ne.prod isOpen_ne).mem_nhds ⟨hx, hx⟩) ?_
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    simp only [mem_ofPred_eq] at hy hz
    simp [field]
    ring
  refine (isBigO_refl (fun p : 𝕜 × 𝕜 => p.1 - p.2) _).mul_isLittleO ((isLittleO_one_iff 𝕜).2 ?_)
  rw [← sub_self (x * x)⁻¹]
  exact tendsto_const_nhds.sub ((continuous_mul.tendsto (x, x)).inv₀ <| mul_ne_zero hx hx)

中文:
定理 hasStrictDerivAt_inv
  条件: (hx : x != 0)
  结论: HasStrictDerivAt 取逆.inv (-(x ^ 2)⁻¹) x
  证明: by
  suffices
    (fun p : 𝕜 × 𝕜 => (p.1 - p.2) * ((x * x)⁻¹ - (p.1 * p.2)⁻¹)) =o[𝓝 (x, x)] fun p =>
      (p.1 - p.2) * 1 by
refine .of_isLittleO this.congr' ?_ (Eventually.of_forall fun _ => mul_one _)
    refine Eventually.mono ((isOpen_ne.prod isOpen_ne).mem_nhds ⟨hx, hx⟩) ?_
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    simp only [mem_ofPred_eq] at hy hz
    simp [field]
    ring
  refine (isBigO_refl (fun p : 𝕜 × 𝕜 => p.1 - p.2) _).mul_isLittleO ((isLittleO_one_iff 𝕜).2 ?_)
  rw [← sub_self (x * x)⁻¹]
  exact tendsto_const_nhds.sub ((continuous_mul.tendsto (x, x)).inv₀ <| mul_ne_zero hx hx)

Depends on / 依赖: Eventually, Eventually.mono, Eventually.of_forall, continu, isBigO_refl, isLittleO_one_iff, isOpen_ne, isOpen_ne.prod, mem_nhds, mem_ofPred_eq, mul_isLittleO, mul_one, of_forall, of_isLittleO, sub_self, tendsto_const_nhds, tendsto_const_nhds.sub, this.congr
-/
theorem hasStrictDerivAt_inv (hx : x != 0) : HasStrictDerivAt Inv.inv (-(x ^ 2)⁻¹) x := by
  suffices
    (fun p : 𝕜 × 𝕜 => (p.1 - p.2) * ((x * x)⁻¹ - (p.1 * p.2)⁻¹)) =o[𝓝 (x, x)] fun p =>
      (p.1 - p.2) * 1 by
refine .of_isLittleO this.congr' ?_ (Eventually.of_forall fun _ => mul_one _)
    refine Eventually.mono ((isOpen_ne.prod isOpen_ne).mem_nhds ⟨hx, hx⟩) ?_
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    simp only [mem_ofPred_eq] at hy hz
    simp [field]
    ring
  refine (isBigO_refl (fun p : 𝕜 × 𝕜 => p.1 - p.2) _).mul_isLittleO ((isLittleO_one_iff 𝕜).2 ?_)
  rw [← sub_self (x * x)⁻¹]
  exact tendsto_const_nhds.sub ((continuous_mul.tendsto (x, x)).inv₀ <| mul_ne_zero hx hx)

/--
theorem `hasDerivAt_inv` / 定理 `hasDerivAt_inv`

English:
theorem hasDerivAt_inv
  given: (x_ne_zero : x != 0)
  statement: HasDerivAt (fun y => y⁻¹) (-(x ^ 2)⁻¹) x
  proof: (hasStrictDerivAt_inv x_ne_zero).hasDerivAt

中文:
定理 hasDerivAt_inv
  条件: (x_ne_zero : x != 0)
  结论: 在点处可导 (fun y => y⁻¹) (-(x ^ 2)⁻¹) x
  证明: (hasStrictDerivAt_inv x_ne_zero).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_inv, x_ne_zero
-/
theorem hasDerivAt_inv (x_ne_zero : x != 0) : HasDerivAt (fun y => y⁻¹) (-(x ^ 2)⁻¹) x :=
  (hasStrictDerivAt_inv x_ne_zero).hasDerivAt

/--
theorem `hasDerivWithinAt_inv` / 定理 `hasDerivWithinAt_inv`

English:
theorem hasDerivWithinAt_inv
  given: (x_ne_zero : x != 0) (s : Set 𝕜)
  proof: (hasDerivAt_inv x_ne_zero).hasDerivWithinAt

中文:
定理 hasDerivWithinAt_inv
  条件: (x_ne_zero : x != 0) (s : 集合 𝕜)
  证明: (hasDerivAt_inv x_ne_zero).hasDerivWithinAt

Depends on / 依赖: hasDerivAt_inv, hasDerivWithinAt, x_ne_zero
-/
theorem hasDerivWithinAt_inv (x_ne_zero : x != 0) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x⁻¹) (-(x ^ 2)⁻¹) s x :=
  (hasDerivAt_inv x_ne_zero).hasDerivWithinAt

/--
theorem `differentiableAt_inv_iff` / 定理 `differentiableAt_inv_iff`

English:
theorem differentiableAt_inv_iff
  statement: DifferentiableAt 𝕜 (fun x => x⁻¹) x ↔ x != 0
  proof: ⟨fun H => NormedField.continuousAt_inv.1 H.continuousAt, fun H =>
    (hasDerivAt_inv H).differentiableAt⟩

中文:
定理 differentiableAt_inv_iff
  结论: DifferentiableAt 𝕜 (fun x => x⁻¹) x ↔ x != 0
  证明: ⟨fun H => NormedField.continuousAt_inv.1 H.continuousAt, fun H =>
    (hasDerivAt_inv H).differentiableAt⟩

Depends on / 依赖: H.continuousAt, NormedField, NormedField.continuousAt_inv, continuousAt, continuousAt_inv, differentiableAt, hasDerivAt_inv
-/
theorem differentiableAt_inv_iff : DifferentiableAt 𝕜 (fun x => x⁻¹) x ↔ x != 0 :=
  ⟨fun H => NormedField.continuousAt_inv.1 H.continuousAt, fun H =>
    (hasDerivAt_inv H).differentiableAt⟩

/--
theorem `deriv_inv` / 定理 `deriv_inv`

English:
theorem deriv_inv
  statement: deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹
  proof: by
  rcases eq_or_ne x 0 with (rfl | hne)
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_inv_iff.1 (not_not.2 rfl))]
    simp
  · exact (hasDerivAt_inv hne).deriv

@[simp]

中文:
定理 deriv_inv
  结论: deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹
  证明: by
  rcases eq_or_ne x 0 with (rfl | hne)
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_inv_iff.1 (not_not.2 rfl))]
    simp
  · exact (hasDerivAt_inv hne).deriv

@[simp]

Depends on / 依赖: deriv_zero_of_not_differentiableAt, differentiableAt_inv_iff, eq_or_ne, hasDerivAt_inv, not_not
-/
theorem deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹ := by
  rcases eq_or_ne x 0 with (rfl | hne)
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_inv_iff.1 (not_not.2 rfl))]
    simp
  · exact (hasDerivAt_inv hne).deriv

@[simp]
/--
theorem `deriv_inv'` / 定理 `deriv_inv'`

English:
theorem deriv_inv'
  statement: (deriv fun x : 𝕜 => x⁻¹) = fun x => -(x ^ 2)⁻¹
  proof: funext fun _ => deriv_inv

中文:
定理 deriv_inv'
  结论: (deriv fun x : 𝕜 => x⁻¹) = fun x => -(x ^ 2)⁻¹
  证明: funext fun _ => deriv_inv

Depends on / 依赖: deriv_inv
-/
theorem deriv_inv' : (deriv fun x : 𝕜 => x⁻¹) = fun x => -(x ^ 2)⁻¹ :=
  funext fun _ => deriv_inv

/--
theorem `derivWithin_inv` / 定理 `derivWithin_inv`

English:
theorem derivWithin_inv
  given: (x_ne_zero : x != 0) (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  rw [DifferentiableAt.derivWithin (differentiableAt_inv x_ne_zero) hxs]
  exact deriv_inv

中文:
定理 derivWithin_inv
  条件: (x_ne_zero : x != 0) (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  rw [DifferentiableAt.derivWithin (differentiableAt_inv x_ne_zero) hxs]
  exact deriv_inv

Depends on / 依赖: DifferentiableAt, DifferentiableAt.derivWithin, derivWithin, deriv_inv, differentiableAt_inv, x_ne_zero
-/
theorem derivWithin_inv (x_ne_zero : x != 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => x⁻¹) s x = -(x ^ 2)⁻¹ := by
  rw [DifferentiableAt.derivWithin (differentiableAt_inv x_ne_zero) hxs]
  exact deriv_inv

/--
theorem `hasFDerivAt_inv` / 定理 `hasFDerivAt_inv`

English:
theorem hasFDerivAt_inv
  given: (x_ne_zero : x != 0)
  proof: hasDerivAt_inv x_ne_zero

中文:
定理 hasFDerivAt_inv
  条件: (x_ne_zero : x != 0)
  证明: hasDerivAt_inv x_ne_zero

Depends on / 依赖: hasDerivAt_inv, x_ne_zero
-/
theorem hasFDerivAt_inv (x_ne_zero : x != 0) :
    HasFDerivAt (fun x => x⁻¹) (toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) : 𝕜 ->L[𝕜] 𝕜) x :=
  hasDerivAt_inv x_ne_zero

/--
theorem `hasStrictFDerivAt_inv` / 定理 `hasStrictFDerivAt_inv`

English:
theorem hasStrictFDerivAt_inv
  given: (x_ne_zero : x != 0)
  proof: hasStrictDerivAt_inv x_ne_zero

中文:
定理 hasStrictFDerivAt_inv
  条件: (x_ne_zero : x != 0)
  证明: hasStrictDerivAt_inv x_ne_zero

Depends on / 依赖: hasStrictDerivAt_inv, x_ne_zero
-/
theorem hasStrictFDerivAt_inv (x_ne_zero : x != 0) :
    HasStrictFDerivAt (fun x => x⁻¹) (toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) : 𝕜 ->L[𝕜] 𝕜) x :=
  hasStrictDerivAt_inv x_ne_zero

/--
theorem `hasFDerivWithinAt_inv` / 定理 `hasFDerivWithinAt_inv`

English:
theorem hasFDerivWithinAt_inv
  given: (x_ne_zero : x != 0)
  proof: (hasFDerivAt_inv x_ne_zero).hasFDerivWithinAt

中文:
定理 hasFDerivWithinAt_inv
  条件: (x_ne_zero : x != 0)
  证明: (hasFDerivAt_inv x_ne_zero).hasFDerivWithinAt

Depends on / 依赖: hasFDerivAt_inv, hasFDerivWithinAt, x_ne_zero
-/
theorem hasFDerivWithinAt_inv (x_ne_zero : x != 0) :
    HasFDerivWithinAt (fun x => x⁻¹) (toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) : 𝕜 ->L[𝕜] 𝕜) s x :=
  (hasFDerivAt_inv x_ne_zero).hasFDerivWithinAt

/--
theorem `fderiv_inv` / 定理 `fderiv_inv`

English:
theorem fderiv_inv
  statement: fderiv 𝕜 (fun x => x⁻¹) x = toSpanSingleton 𝕜 (-(x ^ 2)⁻¹)
  proof: by
  rw [← toSpanSingleton_deriv]; rw [deriv_inv]

中文:
定理 fderiv_inv
  结论: fderiv 𝕜 (fun x => x⁻¹) x = toSpanSingleton 𝕜 (-(x ^ 2)⁻¹)
  证明: by
  rw [← toSpanSingleton_deriv]; rw [deriv_inv]

Depends on / 依赖: deriv_inv, toSpanSingleton_deriv
-/
theorem fderiv_inv : fderiv 𝕜 (fun x => x⁻¹) x = toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) := by
  rw [← toSpanSingleton_deriv]; rw [deriv_inv]

/--
theorem `fderivWithin_inv` / 定理 `fderivWithin_inv`

English:
theorem fderivWithin_inv
  given: (x_ne_zero : x != 0) (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  rw [DifferentiableAt.fderivWithin (differentiableAt_inv x_ne_zero) hxs]
  exact fderiv_inv

中文:
定理 fderivWithin_inv
  条件: (x_ne_zero : x != 0) (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  rw [DifferentiableAt.fderivWithin (differentiableAt_inv x_ne_zero) hxs]
  exact fderiv_inv

Depends on / 依赖: DifferentiableAt, DifferentiableAt.fderivWithin, differentiableAt_inv, fderivWithin, fderiv_inv, x_ne_zero
-/
theorem fderivWithin_inv (x_ne_zero : x != 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => x⁻¹) s x = toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) := by
  rw [DifferentiableAt.fderivWithin (differentiableAt_inv x_ne_zero) hxs]
  exact fderiv_inv

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable {c : 𝕜 -> 𝕜'} {c' : 𝕜'}

@[to_fun]
/--
theorem `HasDerivWithinAt.inv` / 定理 `HasDerivWithinAt.inv`

English:
theorem HasDerivWithinAt.inv
  given: (hc : HasDerivWithinAt c c' s x) (hx : c x != 0)
  proof: by
  convert! (hasDerivAt_inv hx).comp_hasDerivWithinAt x hc using 1
  ring

@[to_fun]

中文:
定理 HasDerivWithinAt.inv
  条件: (hc : HasDerivWithinAt c c' s x) (hx : c x != 0)
  证明: by
  convert! (hasDerivAt_inv hx).comp_hasDerivWithinAt x hc using 1
  ring

@[to_fun]

Depends on / 依赖: comp_hasDerivWithinAt, convert, hasDerivAt_inv
-/
theorem HasDerivWithinAt.inv (hc : HasDerivWithinAt c c' s x) (hx : c x != 0) :
    HasDerivWithinAt (c⁻¹) (-c' / c x ^ 2) s x := by
  convert! (hasDerivAt_inv hx).comp_hasDerivWithinAt x hc using 1
  ring

@[to_fun]
/--
theorem `HasDerivAt.inv` / 定理 `HasDerivAt.inv`

English:
theorem HasDerivAt.inv
  given: (hc : HasDerivAt c c' x) (hx : c x != 0)
  proof: by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.inv hx

中文:
定理 在点处可导.inv
  条件: (hc : 在点处可导 c c' x) (hx : c x != 0)
  证明: by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.inv hx

Depends on / 依赖: hasDerivWithinAt_univ, hc.inv
-/
theorem HasDerivAt.inv (hc : HasDerivAt c c' x) (hx : c x != 0) :
    HasDerivAt (c⁻¹) (-c' / c x ^ 2) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.inv hx

/--
theorem `derivWithin_fun_inv'` / 定理 `derivWithin_fun_inv'`

English:
theorem derivWithin_fun_inv'
  given: (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x != 0)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.inv hx).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_fun_inv'
  条件: (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x != 0)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.inv hx).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hc.hasDerivWithinAt.inv
-/
theorem derivWithin_fun_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x != 0) :
    derivWithin (fun x => (c x)⁻¹) s x = -derivWithin c s x / c x ^ 2 := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.inv hx).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `derivWithin_inv'` / 定理 `derivWithin_inv'`

English:
theorem derivWithin_inv'
  given: (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x != 0)
  proof: derivWithin_fun_inv' hc hx

@[simp]

中文:
定理 derivWithin_inv'
  条件: (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x != 0)
  证明: derivWithin_fun_inv' hc hx

@[simp]

Depends on / 依赖: derivWithin_fun_inv
-/
theorem derivWithin_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x != 0) :
    derivWithin (c⁻¹) s x = -derivWithin c s x / c x ^ 2 :=
  derivWithin_fun_inv' hc hx

@[simp]
/--
theorem `deriv_fun_inv''` / 定理 `deriv_fun_inv''`

English:
theorem deriv_fun_inv''
  given: (hc : DifferentiableAt 𝕜 c x) (hx : c x != 0)
  proof: (hc.hasDerivAt.inv hx).deriv

@[simp]

中文:
定理 deriv_fun_inv''
  条件: (hc : DifferentiableAt 𝕜 c x) (hx : c x != 0)
  证明: (hc.hasDerivAt.inv hx).deriv

@[simp]

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.inv
-/
theorem deriv_fun_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x != 0) :
    deriv (fun x => (c x)⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.hasDerivAt.inv hx).deriv

@[simp]
/--
theorem `deriv_inv''` / 定理 `deriv_inv''`

English:
theorem deriv_inv''
  given: (hc : DifferentiableAt 𝕜 c x) (hx : c x != 0)
  proof: (hc.hasDerivAt.inv hx).deriv

中文:
定理 deriv_inv''
  条件: (hc : DifferentiableAt 𝕜 c x) (hx : c x != 0)
  证明: (hc.hasDerivAt.inv hx).deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.inv
-/
theorem deriv_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x != 0) :
    deriv (c⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.hasDerivAt.inv hx).deriv

end Inverse

section Division

/-! ### Derivative of `x ↦ c x / d x` -/

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {c d : 𝕜 -> 𝕜'} {c' d' : 𝕜'}

/--
theorem `HasDerivWithinAt.fun_div` / 定理 `HasDerivWithinAt.fun_div`

English:
theorem HasDerivWithinAt.fun_div
  statement: (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
  proof: by
  convert hc.fun_mul ((hasDerivAt_inv hx).comp_hasDerivWithinAt x hd)
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · simp [field]
    ring

中文:
定理 HasDerivWithinAt.fun_div
  结论: (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
  证明: by
  convert hc.fun_mul ((hasDerivAt_inv hx).comp_hasDerivWithinAt x hd)
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · simp [field]
    ring

Depends on / 依赖: comp_hasDerivWithinAt, convert, div_eq_mul_inv, fun_mul, hasDerivAt_inv, hc.fun_mul
-/
theorem HasDerivWithinAt.fun_div (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
    (hx : d x != 0) :
    HasDerivWithinAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) s x := by
  convert hc.fun_mul ((hasDerivAt_inv hx).comp_hasDerivWithinAt x hd)
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · simp [field]
    ring

/--
theorem `HasDerivWithinAt.div` / 定理 `HasDerivWithinAt.div`

English:
theorem HasDerivWithinAt.div
  statement: (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
  proof: hc.fun_div hd hx

中文:
定理 HasDerivWithinAt.div
  结论: (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
  证明: hc.fun_div hd hx

Depends on / 依赖: fun_div, hc.fun_div
-/
theorem HasDerivWithinAt.div (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
    (hx : d x != 0) :
    HasDerivWithinAt (c / d) ((c' * d x - c x * d') / d x ^ 2) s x :=
  hc.fun_div hd hx

/--
theorem `HasStrictDerivAt.fun_div` / 定理 `HasStrictDerivAt.fun_div`

English:
theorem HasStrictDerivAt.fun_div
  statement: (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
  proof: by
  convert hc.fun_mul ((hasStrictDerivAt_inv hx).comp x hd)
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · simp [field]
    ring

中文:
定理 HasStrictDerivAt.fun_div
  结论: (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
  证明: by
  convert hc.fun_mul ((hasStrictDerivAt_inv hx).comp x hd)
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · simp [field]
    ring

Depends on / 依赖: convert, div_eq_mul_inv, fun_mul, hasStrictDerivAt_inv, hc.fun_mul
-/
theorem HasStrictDerivAt.fun_div (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
    (hx : d x != 0) : HasStrictDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x := by
  convert hc.fun_mul ((hasStrictDerivAt_inv hx).comp x hd)
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · simp [field]
    ring

/--
theorem `HasStrictDerivAt.div` / 定理 `HasStrictDerivAt.div`

English:
theorem HasStrictDerivAt.div
  statement: (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
  proof: hc.fun_div hd hx

中文:
定理 HasStrictDerivAt.div
  结论: (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
  证明: hc.fun_div hd hx

Depends on / 依赖: fun_div, hc.fun_div
-/
theorem HasStrictDerivAt.div (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
    (hx : d x != 0) : HasStrictDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x :=
  hc.fun_div hd hx

/--
theorem `HasDerivAt.fun_div` / 定理 `HasDerivAt.fun_div`

English:
theorem HasDerivAt.fun_div
  given: (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x != 0)
  proof: by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.div hd hx

中文:
定理 在点处可导.fun_div
  条件: (hc : 在点处可导 c c' x) (hd : 在点处可导 d d' x) (hx : d x != 0)
  证明: by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.div hd hx

Depends on / 依赖: hasDerivWithinAt_univ, hc.div
-/
theorem HasDerivAt.fun_div (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x != 0) :
    HasDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.div hd hx

/--
theorem `HasDerivAt.div` / 定理 `HasDerivAt.div`

English:
theorem HasDerivAt.div
  given: (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x != 0)
  proof: hc.fun_div hd hx

中文:
定理 在点处可导.div
  条件: (hc : 在点处可导 c c' x) (hd : 在点处可导 d d' x) (hx : d x != 0)
  证明: hc.fun_div hd hx

Depends on / 依赖: fun_div, hc.fun_div
-/
theorem HasDerivAt.div (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x != 0) :
    HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x :=
  hc.fun_div hd hx

/--
theorem `DifferentiableWithinAt.fun_div` / 定理 `DifferentiableWithinAt.fun_div`

English:
theorem DifferentiableWithinAt.fun_div
  statement: (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).differentiableWithinAt

中文:
定理 DifferentiableWithinAt.fun_div
  结论: (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).differentiableWithinAt

Depends on / 依赖: differentiableWithinAt, hasDerivWithinAt, hc.hasDerivWithinAt.div, hd.hasDerivWithinAt
-/
theorem DifferentiableWithinAt.fun_div (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x != 0) :
    DifferentiableWithinAt 𝕜 (fun x => c x / d x) s x :=
  (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).differentiableWithinAt

/--
theorem `DifferentiableWithinAt.div` / 定理 `DifferentiableWithinAt.div`

English:
theorem DifferentiableWithinAt.div
  statement: (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: hc.fun_div hd hx

@[to_fun (attr := simp, fun_prop)]

中文:
定理 DifferentiableWithinAt.div
  结论: (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: hc.fun_div hd hx

@[to_fun (attr := simp, fun_prop)]

Depends on / 依赖: fun_div, hc.fun_div
-/
theorem DifferentiableWithinAt.div (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x != 0) :
    DifferentiableWithinAt 𝕜 (c / d) s x :=
  hc.fun_div hd hx

@[to_fun (attr := simp, fun_prop)]
/--
theorem `DifferentiableAt.div` / 定理 `DifferentiableAt.div`

English:
theorem DifferentiableAt.div
  statement: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  proof: (hc.hasDerivAt.div hd.hasDerivAt hx).differentiableAt

@[to_fun (attr := fun_prop)]

中文:
定理 DifferentiableAt.div
  结论: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  证明: (hc.hasDerivAt.div hd.hasDerivAt hx).differentiableAt

@[to_fun (attr := fun_prop)]

Depends on / 依赖: differentiableAt, hasDerivAt, hc.hasDerivAt.div, hd.hasDerivAt
-/
theorem DifferentiableAt.div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
    (hx : d x != 0) : DifferentiableAt 𝕜 (c / d) x :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).differentiableAt

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableOn.div` / 定理 `DifferentiableOn.div`

English:
theorem DifferentiableOn.div
  statement: (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s)
  proof: fun x h =>
  (hc x h).div (hd x h) (hx x h)

@[to_fun (attr := simp, fun_prop)]

中文:
定理 DifferentiableOn.div
  结论: (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s)
  证明: fun x h =>
  (hc x h).div (hd x h) (hx x h)

@[to_fun (attr := simp, fun_prop)]
-/
theorem DifferentiableOn.div (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s)
    (hx : forall x in s, d x != 0) : DifferentiableOn 𝕜 (c / d) s := fun x h =>
  (hc x h).div (hd x h) (hx x h)

@[to_fun (attr := simp, fun_prop)]
/--
theorem `Differentiable.div` / 定理 `Differentiable.div`

English:
theorem Differentiable.div
  given: (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) (hx : forall x, d x != 0)
  proof: fun x => (hc x).div (hd x) (hx x)

中文:
定理 可微.div
  条件: (hc : 可微 𝕜 c) (hd : 可微 𝕜 d) (hx : 对任意 x, d x != 0)
  证明: fun x => (hc x).div (hd x) (hx x)
-/
theorem Differentiable.div (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) (hx : forall x, d x != 0) :
    Differentiable 𝕜 (c / d) := fun x => (hc x).div (hd x) (hx x)

/--
theorem `derivWithin_fun_div` / 定理 `derivWithin_fun_div`

English:
theorem derivWithin_fun_div
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_fun_div
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hc.hasDerivWithinAt.div, hd.hasDerivWithinAt
-/
theorem derivWithin_fun_div
    (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x != 0) :
    derivWithin (fun x => c x / d x) s x =
      (derivWithin c s x * d x - c x * derivWithin d s x) / d x ^ 2 := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `derivWithin_div` / 定理 `derivWithin_div`

English:
theorem derivWithin_div
  statement: (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x)
  proof: derivWithin_fun_div hc hd hx

@[simp]

中文:
定理 derivWithin_div
  结论: (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x)
  证明: derivWithin_fun_div hc hd hx

@[simp]

Depends on / 依赖: derivWithin_fun_div
-/
theorem derivWithin_div (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x)
    (hx : d x != 0) :
    derivWithin (c / d) s x = (derivWithin c s x * d x - c x * derivWithin d s x) / d x ^ 2 :=
  derivWithin_fun_div hc hd hx

@[simp]
/--
theorem `deriv_fun_div` / 定理 `deriv_fun_div`

English:
theorem deriv_fun_div
  given: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0)
  proof: (hc.hasDerivAt.div hd.hasDerivAt hx).deriv

@[simp]

中文:
定理 deriv_fun_div
  条件: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0)
  证明: (hc.hasDerivAt.div hd.hasDerivAt hx).deriv

@[simp]

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.div, hd.hasDerivAt
-/
theorem deriv_fun_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0) :
    deriv (fun x => c x / d x) x = (deriv c x * d x - c x * deriv d x) / d x ^ 2 :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).deriv

@[simp]
/--
theorem `deriv_div` / 定理 `deriv_div`

English:
theorem deriv_div
  given: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0)
  proof: (hc.hasDerivAt.div hd.hasDerivAt hx).deriv

中文:
定理 deriv_div
  条件: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0)
  证明: (hc.hasDerivAt.div hd.hasDerivAt hx).deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.div, hd.hasDerivAt
-/
theorem deriv_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0) :
    deriv (c / d) x = (deriv c x * d x - c x * deriv d x) / d x ^ 2 :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).deriv

/--
theorem `deriv_const_div` / 定理 `deriv_const_div`

English:
theorem deriv_const_div
  given: (c : 𝕜') (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0)
  proof: by
  simp [deriv_fun_div (differentiableAt_const c) hd hx]

@[simp]

中文:
定理 deriv_const_div
  条件: (c : 𝕜') (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0)
  证明: by
  simp [deriv_fun_div (differentiableAt_const c) hd hx]

@[simp]

Depends on / 依赖: deriv_fun_div, differentiableAt_const
-/
theorem deriv_const_div (c : 𝕜') (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0) :
    deriv (fun x => c / d x) x = - c * deriv d x / d x ^ 2 := by
  simp [deriv_fun_div (differentiableAt_const c) hd hx]

@[simp]
/--
theorem `deriv_const_div_id` / 定理 `deriv_const_div_id`

English:
theorem deriv_const_div_id
  given: (c : 𝕜)
  proof: by
  simp [div_eq_mul_inv]

中文:
定理 deriv_const_div_id
  条件: (c : 𝕜)
  证明: by
  simp [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv
-/
theorem deriv_const_div_id (c : 𝕜) :
    deriv (fun x => c / x) x = - c / x ^ 2 := by
  simp [div_eq_mul_inv]

end Division
