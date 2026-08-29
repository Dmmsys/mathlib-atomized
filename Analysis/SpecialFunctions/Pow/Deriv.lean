/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Derivatives of power function on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`

We also prove differentiability and provide derivatives for the power functions `x ^ y`.
-/

public section


noncomputable section

open scoped Real Topology NNReal ENNReal
open Filter

namespace Complex

/--
theorem `hasStrictFDerivAt_cpow` / 定理 `hasStrictFDerivAt_cpow`

English:
theorem hasStrictFDerivAt_cpow
  given: {p : Complex × Complex} (hp : p.1 in slitPlane)
  proof: by
  have A : p.1 != 0 := slitPlane_ne_zero hp
  have : (fun x : Complex × Complex => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    ((isOpen_ne.preimage continuous_fst).eventually_mem A).mono fun p hp =>
      cpow_def_of_ne_zero hp _
  rw [cpow_sub _ _ A]; rw [cpow_one]; rw [mul_div_left_c

中文:
定理 hasStrictFDerivAt_cpow
  条件: {p : 复形 × 复形} (hp : p.1 in slitPlane)
  证明: by
  have A : p.1 != 0 := slitPlane_ne_zero hp
  have : (fun x : Complex × Complex => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    ((isOpen_ne.preimage continuous_fst).eventually_mem A).mono fun p hp =>
      cpow_def_of_ne_zero hp _
  rw [cpow_sub _ _ A]; rw [cpow_one]; rw [mul_div_left_c

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.congr_of_eventuallyEq, add_comm, congr_of_eventuallyEq, continuous_fst, cpow_def_of_ne_zero, cpow_one, cpow_sub, div_eq_mul_inv, eventually_mem, hasStrictFDerivAt_fst, hasStrictFDerivAt_fst.clog, isOpen_ne, isOpen_ne.preimage, mul_div_left_comm, mul_smul, preimage, slitPlane_ne_zero, smul_add, this.symm
-/
theorem hasStrictFDerivAt_cpow {p : Complex × Complex} (hp : p.1 in slitPlane) :
    HasStrictFDerivAt (fun x : Complex × Complex => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst Complex Complex Complex +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd Complex Complex Complex) p := by
  have A : p.1 != 0 := slitPlane_ne_zero hp
  have : (fun x : Complex × Complex => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    ((isOpen_ne.preimage continuous_fst).eventually_mem A).mono fun p hp =>
      cpow_def_of_ne_zero hp _
  rw [cpow_sub _ _ A]; rw [cpow_one]; rw [mul_div_left_comm]; rw [mul_smul]; rw [mul_smul]
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  simpa only [cpow_def_of_ne_zero A, div_eq_mul_inv, mul_smul, add_comm, smul_add] using!
    ((hasStrictFDerivAt_fst.clog hp).mul hasStrictFDerivAt_snd).cexp

/--
theorem `hasStrictFDerivAt_cpow'` / 定理 `hasStrictFDerivAt_cpow'`

English:
theorem hasStrictFDerivAt_cpow'
  given: {x y : Complex} (hp : x in slitPlane)
  proof: @hasStrictFDerivAt_cpow (x, y) hp

中文:
定理 hasStrictFDerivAt_cpow'
  条件: {x y : 复形} (hp : x in slitPlane)
  证明: @hasStrictFDerivAt_cpow (x, y) hp

Depends on / 依赖: hasStrictFDerivAt_cpow
-/
theorem hasStrictFDerivAt_cpow' {x y : Complex} (hp : x in slitPlane) :
    HasStrictFDerivAt (fun x : Complex × Complex => x.1 ^ x.2)
      ((y * x ^ (y - 1)) • ContinuousLinearMap.fst Complex Complex Complex +
        (x ^ y * log x) • ContinuousLinearMap.snd Complex Complex Complex) (x, y) :=
  @hasStrictFDerivAt_cpow (x, y) hp

/--
theorem `hasStrictDerivAt_const_cpow` / 定理 `hasStrictDerivAt_const_cpow`

English:
theorem hasStrictDerivAt_const_cpow
  given: {x y : Complex} (h : x != 0 ∨ y != 0)
  proof: by
  rcases em (x = 0) with (rfl | hx)
  · replace h := h.neg_resolve_left rfl
    rw [log_zero]; rw [mul_zero]
    refine (hasStrictDerivAt_const y 0).congr_of_eventuallyEq ?_
    exact (isOpen_ne.eventually_mem h).mono fun y hy => (zero_cpow hy).symm
  · simpa only [cpow_def_of_ne_zero hx, mul_one

中文:
定理 hasStrictDerivAt_const_cpow
  条件: {x y : 复形} (h : x != 0 ∨ y != 0)
  证明: by
  rcases em (x = 0) with (rfl | hx)
  · replace h := h.neg_resolve_left rfl
    rw [log_zero]; rw [mul_zero]
    refine (hasStrictDerivAt_const y 0).congr_of_eventuallyEq ?_
    exact (isOpen_ne.eventually_mem h).mono fun y hy => (zero_cpow hy).symm
  · simpa only [cpow_def_of_ne_zero hx, mul_one

Depends on / 依赖: congr_of_eventuallyEq, const_mul, cpow_def_of_ne_zero, eventually_mem, h.neg_resolve_left, hasStrictDerivAt_const, hasStrictDerivAt_id, isOpen_ne, isOpen_ne.eventually_mem, log_zero, mul_one, mul_zero, neg_resolve_left, replace, zero_cpow
-/
theorem hasStrictDerivAt_const_cpow {x y : Complex} (h : x != 0 ∨ y != 0) :
    HasStrictDerivAt (fun y => x ^ y) (x ^ y * log x) y := by
  rcases em (x = 0) with (rfl | hx)
  · replace h := h.neg_resolve_left rfl
    rw [log_zero]; rw [mul_zero]
    refine (hasStrictDerivAt_const y 0).congr_of_eventuallyEq ?_
    exact (isOpen_ne.eventually_mem h).mono fun y hy => (zero_cpow hy).symm
  · simpa only [cpow_def_of_ne_zero hx, mul_one] using!
      ((hasStrictDerivAt_id y).const_mul (log x)).cexp

/--
theorem `hasFDerivAt_cpow` / 定理 `hasFDerivAt_cpow`

English:
theorem hasFDerivAt_cpow
  given: {p : Complex × Complex} (hp : p.1 in slitPlane)
  proof: (hasStrictFDerivAt_cpow hp).hasFDerivAt

中文:
定理 hasFDerivAt_cpow
  条件: {p : 复形 × 复形} (hp : p.1 in slitPlane)
  证明: (hasStrictFDerivAt_cpow hp).hasFDerivAt

Depends on / 依赖: hasFDerivAt, hasStrictFDerivAt_cpow
-/
theorem hasFDerivAt_cpow {p : Complex × Complex} (hp : p.1 in slitPlane) :
    HasFDerivAt (fun x : Complex × Complex => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst Complex Complex Complex +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd Complex Complex Complex) p :=
  (hasStrictFDerivAt_cpow hp).hasFDerivAt

end Complex

section fderiv

open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] {f g : E -> Complex} {f' g' : StrongDual Complex E}
  {x : E} {s : Set E} {c : Complex}

/--
theorem `HasStrictFDerivAt.cpow` / 定理 `HasStrictFDerivAt.cpow`

English:
theorem HasStrictFDerivAt.cpow
  statement: (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
  proof: (hasStrictFDerivAt_cpow (p := (f x, g x)) h0).comp x (hf.prodMk hg)

中文:
定理 HasStrictFDerivAt.cpow
  结论: (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
  证明: (hasStrictFDerivAt_cpow (p := (f x, g x)) h0).comp x (hf.prodMk hg)

Depends on / 依赖: hasStrictFDerivAt_cpow, hf.prodMk, prodMk
-/
theorem HasStrictFDerivAt.cpow (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
    (h0 : f x in slitPlane) : HasStrictFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') x :=
  (hasStrictFDerivAt_cpow (p := (f x, g x)) h0).comp x (hf.prodMk hg)

/--
theorem `HasStrictFDerivAt.const_cpow` / 定理 `HasStrictFDerivAt.const_cpow`

English:
theorem HasStrictFDerivAt.const_cpow
  given: (hf : HasStrictFDerivAt f f' x) (h0 : c != 0 ∨ f x != 0)
  proof: (hasStrictDerivAt_const_cpow h0).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.const_cpow
  条件: (hf : HasStrictFDerivAt f f' x) (h0 : c != 0 ∨ f x != 0)
  证明: (hasStrictDerivAt_const_cpow h0).comp_hasStrictFDerivAt x hf

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, comp_hasStrictFDerivAt, hasStrictDerivAt_const_cpow, isKanOfWhiskerLeftAdjoint, lanIsKan, ofIsLeftAdjoint
-/
theorem HasStrictFDerivAt.const_cpow (hf : HasStrictFDerivAt f f' x) (h0 : c != 0 ∨ f x != 0) :
    HasStrictFDerivAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • f') x :=
  (hasStrictDerivAt_const_cpow h0).comp_hasStrictFDerivAt x hf

/--
theorem `HasFDerivAt.cpow` / 定理 `HasFDerivAt.cpow`

English:
theorem HasFDerivAt.cpow
  statement: (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
  proof: by
  convert! (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp x (hf.prodMk hg)

中文:
定理 在点处Fréchet可导.cpow
  结论: (hf : 在点处Fréchet可导 f f' x) (hg : 在点处Fréchet可导 g g' x)
  证明: by
  convert! (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp x (hf.prodMk hg)

Depends on / 依赖: Complex.hasFDerivAt_cpow, convert, hasFDerivAt_cpow, hf.prodMk, prodMk
-/
theorem HasFDerivAt.cpow (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (h0 : f x in slitPlane) : HasFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') x := by
  convert! (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp x (hf.prodMk hg)

/--
theorem `HasFDerivAt.const_cpow` / 定理 `HasFDerivAt.const_cpow`

English:
theorem HasFDerivAt.const_cpow
  given: (hf : HasFDerivAt f f' x) (h0 : c != 0 ∨ f x != 0)
  proof: (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasFDerivAt x hf

中文:
定理 在点处Fréchet可导.const_cpow
  条件: (hf : 在点处Fréchet可导 f f' x) (h0 : c != 0 ∨ f x != 0)
  证明: (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasFDerivAt x hf

Depends on / 依赖: comp_hasFDerivAt, hasDerivAt, hasDerivAt.comp_hasFDerivAt, hasStrictDerivAt_const_cpow
-/
theorem HasFDerivAt.const_cpow (hf : HasFDerivAt f f' x) (h0 : c != 0 ∨ f x != 0) :
    HasFDerivAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • f') x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasFDerivAt x hf

/--
theorem `HasFDerivWithinAt.cpow` / 定理 `HasFDerivWithinAt.cpow`

English:
theorem HasFDerivWithinAt.cpow
  statement: (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x)
  proof: by
  convert!
    (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp_hasFDerivWithinAt x (hf.prodMk hg)

中文:
定理 HasFDerivWithinAt.cpow
  结论: (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x)
  证明: by
  convert!
    (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp_hasFDerivWithinAt x (hf.prodMk hg)

Depends on / 依赖: Complex.hasFDerivAt_cpow, comp_hasFDerivWithinAt, convert, hasFDerivAt_cpow, hf.prodMk, prodMk
-/
theorem HasFDerivWithinAt.cpow (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x)
    (h0 : f x in slitPlane) : HasFDerivWithinAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') s x := by
  convert!
    (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp_hasFDerivWithinAt x (hf.prodMk hg)

/--
theorem `HasFDerivWithinAt.const_cpow` / 定理 `HasFDerivWithinAt.const_cpow`

English:
theorem HasFDerivWithinAt.const_cpow
  given: (hf : HasFDerivWithinAt f f' s x) (h0 : c != 0 ∨ f x != 0)
  proof: (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasFDerivWithinAt x hf

@[fun_prop]

中文:
定理 HasFDerivWithinAt.const_cpow
  条件: (hf : HasFDerivWithinAt f f' s x) (h0 : c != 0 ∨ f x != 0)
  证明: (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasFDerivWithinAt x hf

@[fun_prop]

Depends on / 依赖: comp_hasFDerivWithinAt, hasDerivAt, hasDerivAt.comp_hasFDerivWithinAt, hasStrictDerivAt_const_cpow
-/
theorem HasFDerivWithinAt.const_cpow (hf : HasFDerivWithinAt f f' s x) (h0 : c != 0 ∨ f x != 0) :
    HasFDerivWithinAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • f') s x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasFDerivWithinAt x hf

@[fun_prop]
/--
theorem `DifferentiableAt.cpow` / 定理 `DifferentiableAt.cpow`

English:
theorem DifferentiableAt.cpow
  statement: (hf : DifferentiableAt Complex f x) (hg : DifferentiableAt Complex g x)
  proof: (hf.hasFDerivAt.cpow hg.hasFDerivAt h0).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.cpow
  结论: (hf : DifferentiableAt 复形 f x) (hg : DifferentiableAt 复形 g x)
  证明: (hf.hasFDerivAt.cpow hg.hasFDerivAt h0).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt, hf.hasFDerivAt.cpow, hg.hasFDerivAt
-/
theorem DifferentiableAt.cpow (hf : DifferentiableAt Complex f x) (hg : DifferentiableAt Complex g x)
    (h0 : f x in slitPlane) : DifferentiableAt Complex (fun x => f x ^ g x) x :=
  (hf.hasFDerivAt.cpow hg.hasFDerivAt h0).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableAt.const_cpow` / 定理 `DifferentiableAt.const_cpow`

English:
theorem DifferentiableAt.const_cpow
  given: (hf : DifferentiableAt Complex f x) (h0 : c != 0 ∨ f x != 0)
  proof: (hf.hasFDerivAt.const_cpow h0).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.const_cpow
  条件: (hf : DifferentiableAt 复形 f x) (h0 : c != 0 ∨ f x != 0)
  证明: (hf.hasFDerivAt.const_cpow h0).differentiableAt

@[fun_prop]

Depends on / 依赖: const_cpow, differentiableAt, hasFDerivAt, hf.hasFDerivAt.const_cpow
-/
theorem DifferentiableAt.const_cpow (hf : DifferentiableAt Complex f x) (h0 : c != 0 ∨ f x != 0) :
    DifferentiableAt Complex (fun x => c ^ f x) x :=
  (hf.hasFDerivAt.const_cpow h0).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableAt.cpow_const` / 定理 `DifferentiableAt.cpow_const`

English:
theorem DifferentiableAt.cpow_const
  given: (hf : DifferentiableAt Complex f x) (h0 : f x in slitPlane)
  proof: hf.cpow (differentiableAt_const c) h0

@[fun_prop]

中文:
定理 DifferentiableAt.cpow_const
  条件: (hf : DifferentiableAt 复形 f x) (h0 : f x in slitPlane)
  证明: hf.cpow (differentiableAt_const c) h0

@[fun_prop]

Depends on / 依赖: differentiableAt_const, hf.cpow
-/
theorem DifferentiableAt.cpow_const (hf : DifferentiableAt Complex f x) (h0 : f x in slitPlane) :
    DifferentiableAt Complex (fun x => f x ^ c) x :=
  hf.cpow (differentiableAt_const c) h0

@[fun_prop]
/--
theorem `DifferentiableWithinAt.cpow` / 定理 `DifferentiableWithinAt.cpow`

English:
theorem DifferentiableWithinAt.cpow
  statement: (hf : DifferentiableWithinAt Complex f s x)
  proof: (hf.hasFDerivWithinAt.cpow hg.hasFDerivWithinAt h0).differentiableWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.cpow
  结论: (hf : DifferentiableWithinAt 复形 f s x)
  证明: (hf.hasFDerivWithinAt.cpow hg.hasFDerivWithinAt h0).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.cpow, hg.hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.cpow (hf : DifferentiableWithinAt Complex f s x)
    (hg : DifferentiableWithinAt Complex g s x) (h0 : f x in slitPlane) :
    DifferentiableWithinAt Complex (fun x => f x ^ g x) s x :=
  (hf.hasFDerivWithinAt.cpow hg.hasFDerivWithinAt h0).differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableWithinAt.const_cpow` / 定理 `DifferentiableWithinAt.const_cpow`

English:
theorem DifferentiableWithinAt.const_cpow
  statement: (hf : DifferentiableWithinAt Complex f s x)
  proof: (hf.hasFDerivWithinAt.const_cpow h0).differentiableWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.const_cpow
  结论: (hf : DifferentiableWithinAt 复形 f s x)
  证明: (hf.hasFDerivWithinAt.const_cpow h0).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: const_cpow, differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.const_cpow
-/
theorem DifferentiableWithinAt.const_cpow (hf : DifferentiableWithinAt Complex f s x)
    (h0 : c != 0 ∨ f x != 0) : DifferentiableWithinAt Complex (fun x => c ^ f x) s x :=
  (hf.hasFDerivWithinAt.const_cpow h0).differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableWithinAt.cpow_const` / 定理 `DifferentiableWithinAt.cpow_const`

English:
theorem DifferentiableWithinAt.cpow_const
  statement: (hf : DifferentiableWithinAt Complex f s x)
  proof: hf.cpow (differentiableWithinAt_const c) h0

@[fun_prop]

中文:
定理 DifferentiableWithinAt.cpow_const
  结论: (hf : DifferentiableWithinAt 复形 f s x)
  证明: hf.cpow (differentiableWithinAt_const c) h0

@[fun_prop]

Depends on / 依赖: differentiableWithinAt_const, hf.cpow
-/
theorem DifferentiableWithinAt.cpow_const (hf : DifferentiableWithinAt Complex f s x)
    (h0 : f x in slitPlane) :
    DifferentiableWithinAt Complex (fun x => f x ^ c) s x :=
  hf.cpow (differentiableWithinAt_const c) h0

@[fun_prop]
/--
theorem `DifferentiableOn.cpow` / 定理 `DifferentiableOn.cpow`

English:
theorem DifferentiableOn.cpow
  statement: (hf : DifferentiableOn Complex f s) (hg : DifferentiableOn Complex g s)
  proof: fun x hx => (hf x hx).cpow (hg x hx) (h0 hx)

@[fun_prop]

中文:
定理 DifferentiableOn.cpow
  结论: (hf : DifferentiableOn 复形 f s) (hg : DifferentiableOn 复形 g s)
  证明: fun x hx => (hf x hx).cpow (hg x hx) (h0 hx)

@[fun_prop]
-/
theorem DifferentiableOn.cpow (hf : DifferentiableOn Complex f s) (hg : DifferentiableOn Complex g s)
    (h0 : Set.MapsTo f s slitPlane) : DifferentiableOn Complex (fun x => f x ^ g x) s :=
  fun x hx => (hf x hx).cpow (hg x hx) (h0 hx)

@[fun_prop]
/--
theorem `DifferentiableOn.const_cpow` / 定理 `DifferentiableOn.const_cpow`

English:
theorem DifferentiableOn.const_cpow
  statement: (hf : DifferentiableOn Complex f s)
  proof: fun x hx => (hf x hx).const_cpow (h0.imp_right fun h => h x hx)

@[fun_prop]

中文:
定理 DifferentiableOn.const_cpow
  结论: (hf : DifferentiableOn 复形 f s)
  证明: fun x hx => (hf x hx).const_cpow (h0.imp_right fun h => h x hx)

@[fun_prop]

Depends on / 依赖: const_cpow, h0.imp_right, imp_right
-/
theorem DifferentiableOn.const_cpow (hf : DifferentiableOn Complex f s)
    (h0 : c != 0 ∨ forall x in s, f x != 0) : DifferentiableOn Complex (fun x => c ^ f x) s :=
  fun x hx => (hf x hx).const_cpow (h0.imp_right fun h => h x hx)

@[fun_prop]
/--
theorem `DifferentiableOn.cpow_const` / 定理 `DifferentiableOn.cpow_const`

English:
theorem DifferentiableOn.cpow_const
  statement: (hf : DifferentiableOn Complex f s)
  proof: hf.cpow (differentiableOn_const c) h0

@[fun_prop]

中文:
定理 DifferentiableOn.cpow_const
  结论: (hf : DifferentiableOn 复形 f s)
  证明: hf.cpow (differentiableOn_const c) h0

@[fun_prop]

Depends on / 依赖: differentiableOn_const, hf.cpow
-/
theorem DifferentiableOn.cpow_const (hf : DifferentiableOn Complex f s)
    (h0 : forall x in s, f x in slitPlane) :
    DifferentiableOn Complex (fun x => f x ^ c) s :=
  hf.cpow (differentiableOn_const c) h0

@[fun_prop]
/--
theorem `Differentiable.cpow` / 定理 `Differentiable.cpow`

English:
theorem Differentiable.cpow
  statement: (hf : Differentiable Complex f) (hg : Differentiable Complex g)
  proof: fun x => (hf x).cpow (hg x) (h0 x)

@[fun_prop]

中文:
定理 可微.cpow
  结论: (hf : 可微 复形 f) (hg : 可微 复形 g)
  证明: fun x => (hf x).cpow (hg x) (h0 x)

@[fun_prop]
-/
theorem Differentiable.cpow (hf : Differentiable Complex f) (hg : Differentiable Complex g)
    (h0 : forall x, f x in slitPlane) : Differentiable Complex (fun x => f x ^ g x) :=
  fun x => (hf x).cpow (hg x) (h0 x)

@[fun_prop]
/--
theorem `Differentiable.const_cpow` / 定理 `Differentiable.const_cpow`

English:
theorem Differentiable.const_cpow
  statement: (hf : Differentiable Complex f)
  proof: fun x => (hf x).const_cpow (h0.imp_right fun h => h x)

@[fun_prop]

中文:
定理 可微.const_cpow
  结论: (hf : 可微 复形 f)
  证明: fun x => (hf x).const_cpow (h0.imp_right fun h => h x)

@[fun_prop]

Depends on / 依赖: const_cpow, h0.imp_right, imp_right
-/
theorem Differentiable.const_cpow (hf : Differentiable Complex f)
    (h0 : c != 0 ∨ forall x, f x != 0) : Differentiable Complex (fun x => c ^ f x) :=
  fun x => (hf x).const_cpow (h0.imp_right fun h => h x)

@[fun_prop]
/--
lemma `differentiable_const_cpow_of_neZero` / 引理 `differentiable_const_cpow_of_neZero`

English:
lemma differentiable_const_cpow_of_neZero
  given: (z : Complex) [NeZero z]
  proof: differentiable_id.const_cpow (.inl <| NeZero.ne z)

@[fun_prop]

中文:
引理 differentiable_const_cpow_of_neZero
  条件: (z : 复形) [NeZero z]
  证明: differentiable_id.const_cpow (.inl <| NeZero.ne z)

@[fun_prop]

Depends on / 依赖: NeZero, NeZero.ne, const_cpow, differentiable_id, differentiable_id.const_cpow
-/
lemma differentiable_const_cpow_of_neZero (z : Complex) [NeZero z] :
    Differentiable Complex fun s : Complex => z ^ s :=
  differentiable_id.const_cpow (.inl <| NeZero.ne z)

@[fun_prop]
/--
lemma `differentiableAt_const_cpow_of_neZero` / 引理 `differentiableAt_const_cpow_of_neZero`

English:
lemma differentiableAt_const_cpow_of_neZero
  given: (z : Complex) [NeZero z] (t : Complex)
  proof: differentiableAt_id.const_cpow (.inl <| NeZero.ne z)

中文:
引理 differentiableAt_const_cpow_of_neZero
  条件: (z : 复形) [NeZero z] (t : 复形)
  证明: differentiableAt_id.const_cpow (.inl <| NeZero.ne z)

Depends on / 依赖: NeZero, NeZero.ne, const_cpow, differentiableAt_id, differentiableAt_id.const_cpow
-/
lemma differentiableAt_const_cpow_of_neZero (z : Complex) [NeZero z] (t : Complex) :
    DifferentiableAt Complex (fun s : Complex => z ^ s) t :=
  differentiableAt_id.const_cpow (.inl <| NeZero.ne z)

end fderiv

section deriv

open Complex

variable {f g : Complex -> Complex} {s : Set Complex} {f' g' x c : Complex}

nonrec theorem HasStrictDerivAt.cpow (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x)
    (h0 : f x in slitPlane) : HasStrictDerivAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') x := by
  simpa using (hf.hasStrictFDerivAt.cpow hg h0).hasStrictDerivAt

/--
theorem `HasStrictDerivAt.const_cpow` / 定理 `HasStrictDerivAt.const_cpow`

English:
theorem HasStrictDerivAt.const_cpow
  given: (hf : HasStrictDerivAt f f' x) (h : c != 0 ∨ f x != 0)
  proof: (hasStrictDerivAt_const_cpow h).comp x hf

中文:
定理 HasStrictDerivAt.const_cpow
  条件: (hf : HasStrictDerivAt f f' x) (h : c != 0 ∨ f x != 0)
  证明: (hasStrictDerivAt_const_cpow h).comp x hf

Depends on / 依赖: hasStrictDerivAt_const_cpow
-/
theorem HasStrictDerivAt.const_cpow (hf : HasStrictDerivAt f f' x) (h : c != 0 ∨ f x != 0) :
    HasStrictDerivAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') x :=
  (hasStrictDerivAt_const_cpow h).comp x hf

/--
theorem `Complex.hasStrictDerivAt_cpow_const` / 定理 `Complex.hasStrictDerivAt_cpow_const`

English:
theorem Complex.hasStrictDerivAt_cpow_const
  given: (h : x in slitPlane)
  proof: by
  simpa only [mul_zero, add_zero, mul_one] using!
    (hasStrictDerivAt_id x).cpow (hasStrictDerivAt_const x c) h

中文:
定理 复形.hasStrictDerivAt_cpow_const
  条件: (h : x in slitPlane)
  证明: by
  simpa only [mul_zero, add_zero, mul_one] using!
    (hasStrictDerivAt_id x).cpow (hasStrictDerivAt_const x c) h

Depends on / 依赖: add_zero, hasStrictDerivAt_const, hasStrictDerivAt_id, mul_one, mul_zero
-/
theorem Complex.hasStrictDerivAt_cpow_const (h : x in slitPlane) :
    HasStrictDerivAt (fun z : Complex => z ^ c) (c * x ^ (c - 1)) x := by
  simpa only [mul_zero, add_zero, mul_one] using!
    (hasStrictDerivAt_id x).cpow (hasStrictDerivAt_const x c) h

/--
theorem `HasStrictDerivAt.cpow_const` / 定理 `HasStrictDerivAt.cpow_const`

English:
theorem HasStrictDerivAt.cpow_const
  statement: (hf : HasStrictDerivAt f f' x)
  proof: (Complex.hasStrictDerivAt_cpow_const h0).comp x hf

中文:
定理 HasStrictDerivAt.cpow_const
  结论: (hf : HasStrictDerivAt f f' x)
  证明: (Complex.hasStrictDerivAt_cpow_const h0).comp x hf

Depends on / 依赖: Complex.hasStrictDerivAt_cpow_const, hasStrictDerivAt_cpow_const
-/
theorem HasStrictDerivAt.cpow_const (hf : HasStrictDerivAt f f' x)
    (h0 : f x in slitPlane) :
    HasStrictDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAt_cpow_const h0).comp x hf

/--
theorem `HasDerivAt.cpow` / 定理 `HasDerivAt.cpow`

English:
theorem HasDerivAt.cpow
  statement: (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
  proof: by
  simpa using (hf.hasFDerivAt.cpow hg h0).hasDerivAt

中文:
定理 在点处可导.cpow
  结论: (hf : 在点处可导 f f' x) (hg : 在点处可导 g g' x)
  证明: by
  simpa using (hf.hasFDerivAt.cpow hg h0).hasDerivAt

Depends on / 依赖: hasDerivAt, hasFDerivAt, hf.hasFDerivAt.cpow
-/
theorem HasDerivAt.cpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (h0 : f x in slitPlane) : HasDerivAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') x := by
  simpa using (hf.hasFDerivAt.cpow hg h0).hasDerivAt

/--
theorem `HasDerivAt.const_cpow` / 定理 `HasDerivAt.const_cpow`

English:
theorem HasDerivAt.const_cpow
  given: (hf : HasDerivAt f f' x) (h0 : c != 0 ∨ f x != 0)
  proof: (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp x hf

中文:
定理 在点处可导.const_cpow
  条件: (hf : 在点处可导 f f' x) (h0 : c != 0 ∨ f x != 0)
  证明: (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp x hf

Depends on / 依赖: hasDerivAt, hasDerivAt.comp, hasStrictDerivAt_const_cpow
-/
theorem HasDerivAt.const_cpow (hf : HasDerivAt f f' x) (h0 : c != 0 ∨ f x != 0) :
    HasDerivAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp x hf

/--
theorem `HasDerivAt.cpow_const` / 定理 `HasDerivAt.cpow_const`

English:
theorem HasDerivAt.cpow_const
  given: (hf : HasDerivAt f f' x) (h0 : f x in slitPlane)
  proof: (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp x hf

中文:
定理 在点处可导.cpow_const
  条件: (hf : 在点处可导 f f' x) (h0 : f x in slitPlane)
  证明: (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp x hf

Depends on / 依赖: Complex.hasStrictDerivAt_cpow_const, hasDerivAt, hasDerivAt.comp, hasStrictDerivAt_cpow_const
-/
theorem HasDerivAt.cpow_const (hf : HasDerivAt f f' x) (h0 : f x in slitPlane) :
    HasDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp x hf

/--
theorem `HasDerivWithinAt.cpow` / 定理 `HasDerivWithinAt.cpow`

English:
theorem HasDerivWithinAt.cpow
  statement: (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
  proof: by
  simpa using (hf.hasFDerivWithinAt.cpow hg h0).hasDerivWithinAt

中文:
定理 HasDerivWithinAt.cpow
  结论: (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
  证明: by
  simpa using (hf.hasFDerivWithinAt.cpow hg h0).hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.cpow
-/
theorem HasDerivWithinAt.cpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
    (h0 : f x in slitPlane) : HasDerivWithinAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') s x := by
  simpa using (hf.hasFDerivWithinAt.cpow hg h0).hasDerivWithinAt

/--
theorem `HasDerivWithinAt.const_cpow` / 定理 `HasDerivWithinAt.const_cpow`

English:
theorem HasDerivWithinAt.const_cpow
  given: (hf : HasDerivWithinAt f f' s x) (h0 : c != 0 ∨ f x != 0)
  proof: (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.const_cpow
  条件: (hf : HasDerivWithinAt f f' s x) (h0 : c != 0 ∨ f x != 0)
  证明: (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasDerivWithinAt x hf

Depends on / 依赖: comp_hasDerivWithinAt, hasDerivAt, hasDerivAt.comp_hasDerivWithinAt, hasStrictDerivAt_const_cpow
-/
theorem HasDerivWithinAt.const_cpow (hf : HasDerivWithinAt f f' s x) (h0 : c != 0 ∨ f x != 0) :
    HasDerivWithinAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') s x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasDerivWithinAt x hf

/--
theorem `HasDerivWithinAt.cpow_const` / 定理 `HasDerivWithinAt.cpow_const`

English:
theorem HasDerivWithinAt.cpow_const
  statement: (hf : HasDerivWithinAt f f' s x)
  proof: (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.cpow_const
  结论: (hf : HasDerivWithinAt f f' s x)
  证明: (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp_hasDerivWithinAt x hf

Depends on / 依赖: Complex.hasStrictDerivAt_cpow_const, comp_hasDerivWithinAt, hasDerivAt, hasDerivAt.comp_hasDerivWithinAt, hasStrictDerivAt_cpow_const
-/
theorem HasDerivWithinAt.cpow_const (hf : HasDerivWithinAt f f' s x)
    (h0 : f x in slitPlane) :
    HasDerivWithinAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') s x :=
  (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp_hasDerivWithinAt x hf

/--
theorem `Complex.derivWithin_const_cpow` / 定理 `Complex.derivWithin_const_cpow`

English:
theorem Complex.derivWithin_const_cpow
  given: (hf : DifferentiableWithinAt Complex f s x) (c : Complex)
  proof: by
  by_cases h : UniqueDiffWithinAt Complex s x; swap
  · rw [derivWithin_zero_of_not_uniqueDiffWithinAt h,
      derivWithin_zero_of_not_uniqueDiffWithinAt h, mul_zero, zero_mul]
  by_cases hc : c = 0; swap
  · rw [mul_comm, ← mul_assoc]
    exact (hf.hasDerivWithinAt.const_cpow (Or.inl hc)).deriv

中文:
定理 复形.derivWithin_const_cpow
  条件: (hf : DifferentiableWithinAt 复形 f s x) (c : 复形)
  证明: by
  by_cases h : UniqueDiffWithinAt Complex s x; swap
  · rw [derivWithin_zero_of_not_uniqueDiffWithinAt h,
      derivWithin_zero_of_not_uniqueDiffWithinAt h, mul_zero, zero_mul]
  by_cases hc : c = 0; swap
  · rw [mul_comm, ← mul_assoc]
    exact (hf.hasDerivWithinAt.const_cpow (Or.inl hc)).deriv

Depends on / 依赖: Infinite, Or.inl, Set.Infinite.of_accPt, UniqueDiffWithinAt, accPt_principal_iff_nhdsWithin, const_cpow, derivWithin, derivWithin_zero_of_frequently_mem, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hf.hasDerivWithinAt.const_cpow, log_zero, mul_assoc, mul_comm, mul_zero, of_accPt, uniqueDiffWithinAt_iff_accPt, zero_c, zero_mul
-/
theorem Complex.derivWithin_const_cpow (hf : DifferentiableWithinAt Complex f s x) (c : Complex) :
    derivWithin (fun x => c ^ f x) s x = log c * derivWithin f s x * c ^ f x := by
  by_cases h : UniqueDiffWithinAt Complex s x; swap
  · rw [derivWithin_zero_of_not_uniqueDiffWithinAt h,
      derivWithin_zero_of_not_uniqueDiffWithinAt h, mul_zero, zero_mul]
  by_cases hc : c = 0; swap
  · rw [mul_comm, ← mul_assoc]
    exact (hf.hasDerivWithinAt.const_cpow (Or.inl hc)).derivWithin h
  rw [uniqueDiffWithinAt_iff_accPt]; rw [accPt_principal_iff_nhdsWithin] at h
  simp only [hc, log_zero, zero_mul]
  apply derivWithin_zero_of_frequently_mem {0, 1} (mt Set.Infinite.of_accPt (by simp))
  simpa [zero_cpow_eq_iff, em']

/--
theorem `Complex.deriv_const_cpow` / 定理 `Complex.deriv_const_cpow`

English:
theorem Complex.deriv_const_cpow
  given: (hf : DifferentiableAt Complex f x) (c : Complex)
  proof: by
  rw [← derivWithin_univ]; rw [derivWithin_const_cpow]; rw [derivWithin_univ]
  rwa [differentiableWithinAt_univ]

中文:
定理 复形.deriv_const_cpow
  条件: (hf : DifferentiableAt 复形 f x) (c : 复形)
  证明: by
  rw [← derivWithin_univ]; rw [derivWithin_const_cpow]; rw [derivWithin_univ]
  rwa [differentiableWithinAt_univ]

Depends on / 依赖: derivWithin_const_cpow, derivWithin_univ, differentiableWithinAt_univ
-/
theorem Complex.deriv_const_cpow (hf : DifferentiableAt Complex f x) (c : Complex) :
    deriv (fun x => c ^ f x) x = log c * deriv f x * c ^ f x := by
  rw [← derivWithin_univ]; rw [derivWithin_const_cpow]; rw [derivWithin_univ]
  rwa [differentiableWithinAt_univ]

/--
theorem `hasDerivAt_ofReal_cpow_const'` / 定理 `hasDerivAt_ofReal_cpow_const'`

English:
theorem hasDerivAt_ofReal_cpow_const'
  given: {x : Real} (hx : x != 0) {r : Complex} (hr : r != -1)
  proof: by
  rw [Ne]; rw [← add_eq_zero_iff_eq_neg]; rw [← Ne] at hr
  rcases lt_or_gt_of_ne hx.symm with (hx | hx)
  · -- easy case : `0 < x`
    apply HasDerivAt.comp_ofReal (e := fun y => (y : Complex) ^ (r + 1) / (r + 1))
    convert! HasDerivAt.div_const (𝕜 := Complex) ?_ (r + 1) using 1
    · exact (m

中文:
定理 hasDerivAt_of实数_cpow_const'
  条件: {x : 实数} (hx : x != 0) {r : 复形} (hr : r != -1)
  证明: by
  rw [Ne]; rw [← add_eq_zero_iff_eq_neg]; rw [← Ne] at hr
  rcases lt_or_gt_of_ne hx.symm with (hx | hx)
  · -- easy case : `0 < x`
    apply HasDerivAt.comp_ofReal (e := fun y => (y : Complex) ^ (r + 1) / (r + 1))
    convert! HasDerivAt.div_const (𝕜 := Complex) ?_ (r + 1) using 1
    · exact (m

Depends on / 依赖: HasDerivAt, HasDerivAt.comp_ofReal, HasDerivAt.cpow_const, HasDerivAt.div_const, add_eq_zero_iff_eq_neg, add_sub_cancel_right, comp_ofReal, convert, cpow_const, div_const, harder, hasDerivAt_id, hx.symm, lt_or_gt_of_ne, mul_comm, mul_one
-/
theorem hasDerivAt_ofReal_cpow_const' {x : Real} (hx : x != 0) {r : Complex} (hr : r != -1) :
    HasDerivAt (fun y : Real => (y : Complex) ^ (r + 1) / (r + 1)) (x ^ r) x := by
  rw [Ne]; rw [← add_eq_zero_iff_eq_neg]; rw [← Ne] at hr
  rcases lt_or_gt_of_ne hx.symm with (hx | hx)
  · -- easy case : `0 < x`
    apply HasDerivAt.comp_ofReal (e := fun y => (y : Complex) ^ (r + 1) / (r + 1))
    convert! HasDerivAt.div_const (𝕜 := Complex) ?_ (r + 1) using 1
    · exact (mul_div_cancel_right₀ _ hr).symm
    · convert! HasDerivAt.cpow_const ?_ ?_ using 1
      · rw [add_sub_cancel_right, mul_comm]; exact (mul_one _).symm
      · exact hasDerivAt_id (x : Complex)
      · simp [hx]
  · -- harder case : `x < 0`
    have : forallᶠ y : Real in 𝓝 x,
        (y : Complex) ^ (r + 1) / (r + 1) = (-y : Complex) ^ (r + 1) * exp (π * I * (r + 1)) / (r + 1) := by
      refine Filter.eventually_of_mem (Iio_mem_nhds hx) fun y hy => ?_
      rw [ofReal_cpow_of_nonpos (le_of_lt hy)]
    refine HasDerivAt.congr_of_eventuallyEq ?_ this
    rw [ofReal_cpow_of_nonpos (le_of_lt hx)]
    suffices HasDerivAt (fun y : Real => (-↑y) ^ (r + 1) * exp (↑π * I * (r + 1)))
        ((r + 1) * (-↑x) ^ r * exp (↑π * I * r)) x by
      convert! this.div_const (r + 1) using 1
      conv_rhs => rw [mul_assoc, mul_comm, mul_div_cancel_right₀ _ hr]
    rw [mul_add ((π : Complex) * _)]; rw [mul_one]; rw [exp_add]; rw [exp_pi_mul_I]; rw [mul_comm (_ : Complex) (-1 : Complex)]; rw [neg_one_mul]
    simp_rw [mul_neg, ← neg_mul, ← ofReal_neg]
    suffices HasDerivAt (fun y : Real => (↑(-y) : Complex) ^ (r + 1)) (-(r + 1) * ↑(-x) ^ r) x by
      convert! this.neg.mul_const _ using 1; ring
    suffices HasDerivAt (fun y : Real => (y : Complex) ^ (r + 1)) ((r + 1) * ↑(-x) ^ r) (-x) by
      convert! @HasDerivAt.scomp Real _ Complex _ _ x Real _ _ _ _ _ _ _ _ this (hasDerivAt_neg x) using 1
      rw [real_smul]; rw [ofReal_neg 1]; rw [ofReal_one]; ring
    suffices HasDerivAt (fun y : Complex => y ^ (r + 1)) ((r + 1) * ↑(-x) ^ r) ↑(-x) by
      exact this.comp_ofReal
    conv in ↑_ ^ _ => rw [(by ring : r = r + 1 - 1)]
    convert! HasDerivAt.cpow_const ?_ ?_ using 1
    · rw [add_sub_cancel_right, add_sub_cancel_right]; exact (mul_one _).symm
    · exact hasDerivAt_id ((-x : Real) : Complex)
    · simp [hx]

/--
theorem `hasDerivAt_ofReal_cpow_const` / 定理 `hasDerivAt_ofReal_cpow_const`

English:
theorem hasDerivAt_ofReal_cpow_const
  given: {x : Real} (hx : x != 0) {r : Complex} (hr : r != 0)
  proof: by
have := HasDerivAt.const_mul r hasDerivAt_ofReal_cpow_const' hx
    (by rwa [ne_eq, sub_eq_neg_self])
  simpa [sub_add_cancel, mul_div_cancel₀ _ hr] using this

中文:
定理 hasDerivAt_of实数_cpow_const
  条件: {x : 实数} (hx : x != 0) {r : 复形} (hr : r != 0)
  证明: by
have := HasDerivAt.const_mul r hasDerivAt_ofReal_cpow_const' hx
    (by rwa [ne_eq, sub_eq_neg_self])
  simpa [sub_add_cancel, mul_div_cancel₀ _ hr] using this

Depends on / 依赖: HasDerivAt, HasDerivAt.const_mul, const_mul, hasDerivAt_ofReal_cpow_const, ne_eq, sub_add_cancel, sub_eq_neg_self
-/
theorem hasDerivAt_ofReal_cpow_const {x : Real} (hx : x != 0) {r : Complex} (hr : r != 0) :
    HasDerivAt (fun y : Real => (y : Complex) ^ r) (r * x ^ (r - 1)) x := by
have := HasDerivAt.const_mul r hasDerivAt_ofReal_cpow_const' hx
    (by rwa [ne_eq, sub_eq_neg_self])
  simpa [sub_add_cancel, mul_div_cancel₀ _ hr] using this

/--
theorem `DifferentiableAt.ofReal_cpow_const` / 定理 `DifferentiableAt.ofReal_cpow_const`

English:
theorem DifferentiableAt.ofReal_cpow_const
  statement: {f : Real -> Real} {x : Real} (hf : DifferentiableAt Real f x)
  proof: (hasDerivAt_ofReal_cpow_const h0 h1).differentiableAt.comp x hf

中文:
定理 DifferentiableAt.of实数_cpow_const
  结论: {f : 实数 -> 实数} {x : 实数} (hf : DifferentiableAt 实数 f x)
  证明: (hasDerivAt_ofReal_cpow_const h0 h1).differentiableAt.comp x hf

Depends on / 依赖: differentiableAt, differentiableAt.comp, hasDerivAt_ofReal_cpow_const
-/
theorem DifferentiableAt.ofReal_cpow_const {f : Real -> Real} {x : Real} (hf : DifferentiableAt Real f x)
    (h0 : f x != 0) (h1 : c != 0) :
    DifferentiableAt Real (fun (y : Real) => (f y : Complex) ^ c) x :=
  (hasDerivAt_ofReal_cpow_const h0 h1).differentiableAt.comp x hf

/--
theorem `Complex.deriv_cpow_const` / 定理 `Complex.deriv_cpow_const`

English:
theorem Complex.deriv_cpow_const
  given: (hx : x in Complex.slitPlane)
  proof: (hasStrictDerivAt_cpow_const hx).hasDerivAt.deriv

中文:
定理 复形.deriv_cpow_const
  条件: (hx : x in 复形.slitPlane)
  证明: (hasStrictDerivAt_cpow_const hx).hasDerivAt.deriv

Depends on / 依赖: hasDerivAt, hasDerivAt.deriv, hasStrictDerivAt_cpow_const
-/
theorem Complex.deriv_cpow_const (hx : x in Complex.slitPlane) :
    deriv (fun (x : Complex) => x ^ c) x = c * x ^ (c - 1) :=
  (hasStrictDerivAt_cpow_const hx).hasDerivAt.deriv

/--
theorem `Complex.deriv_ofReal_cpow_const` / 定理 `Complex.deriv_ofReal_cpow_const`

English:
theorem Complex.deriv_ofReal_cpow_const
  given: {x : Real} (hx : x != 0) (hc : c != 0)
  proof: (hasDerivAt_ofReal_cpow_const hx hc).deriv

中文:
定理 复形.deriv_of实数_cpow_const
  条件: {x : 实数} (hx : x != 0) (hc : c != 0)
  证明: (hasDerivAt_ofReal_cpow_const hx hc).deriv

Depends on / 依赖: hasDerivAt_ofReal_cpow_const
-/
theorem Complex.deriv_ofReal_cpow_const {x : Real} (hx : x != 0) (hc : c != 0) :
    deriv (fun x : Real => (x : Complex) ^ c) x = c * x ^ (c - 1) :=
  (hasDerivAt_ofReal_cpow_const hx hc).deriv

/--
theorem `deriv_cpow_const` / 定理 `deriv_cpow_const`

English:
theorem deriv_cpow_const
  given: (hf : DifferentiableAt Complex f x) (hx : f x in Complex.slitPlane)
  proof: (hf.hasDerivAt.cpow_const hx).deriv

中文:
定理 deriv_cpow_const
  条件: (hf : DifferentiableAt 复形 f x) (hx : f x in 复形.slitPlane)
  证明: (hf.hasDerivAt.cpow_const hx).deriv

Depends on / 依赖: cpow_const, hasDerivAt, hf.hasDerivAt.cpow_const
-/
theorem deriv_cpow_const (hf : DifferentiableAt Complex f x) (hx : f x in Complex.slitPlane) :
    deriv (fun (x : Complex) => f x ^ c) x = c * f x ^ (c - 1) * deriv f x :=
  (hf.hasDerivAt.cpow_const hx).deriv

/--
theorem `isTheta_deriv_ofReal_cpow_const_atTop` / 定理 `isTheta_deriv_ofReal_cpow_const_atTop`

English:
theorem isTheta_deriv_ofReal_cpow_const_atTop
  given: {c : Complex} (hc : c != 0)
  proof: by
  calc
    _ =ᶠ[atTop] fun x : Real => c * x ^ (c - 1) := by
      filter_upwards [eventually_ne_atTop 0] with x hx using by rw [deriv_ofReal_cpow_const hx hc]
    _ =Θ[atTop] fun x : Real => ‖(x : Complex) ^ (c - 1)‖ :=
      (Asymptotics.IsTheta.of_norm_eventuallyEq EventuallyEq.rfl).const_mul_

中文:
定理 isTheta_deriv_of实数_cpow_const_atTop
  条件: {c : 复形} (hc : c != 0)
  证明: by
  calc
    _ =ᶠ[atTop] fun x : Real => c * x ^ (c - 1) := by
      filter_upwards [eventually_ne_atTop 0] with x hx using by rw [deriv_ofReal_cpow_const hx hc]
    _ =Θ[atTop] fun x : Real => ‖(x : Complex) ^ (c - 1)‖ :=
      (Asymptotics.IsTheta.of_norm_eventuallyEq EventuallyEq.rfl).const_mul_

Depends on / 依赖: Asymptotics, Asymptotics.IsTheta.of_norm_eventuallyEq, EventuallyEq, EventuallyEq.rfl, IsTheta, c.re, const_mul_left, deriv_ofReal_cpow_const, eventually_gt_atTop, eventually_ne_atTop, filter_upwards, norm_cpow_eq_rpow_re_of_pos, of_norm_eventuallyEq, one_re, sub_re
-/
theorem isTheta_deriv_ofReal_cpow_const_atTop {c : Complex} (hc : c != 0) :
    deriv (fun (x : Real) => (x : Complex) ^ c) =Θ[atTop] fun x => x ^ (c.re - 1) := by
  calc
    _ =ᶠ[atTop] fun x : Real => c * x ^ (c - 1) := by
      filter_upwards [eventually_ne_atTop 0] with x hx using by rw [deriv_ofReal_cpow_const hx hc]
    _ =Θ[atTop] fun x : Real => ‖(x : Complex) ^ (c - 1)‖ :=
      (Asymptotics.IsTheta.of_norm_eventuallyEq EventuallyEq.rfl).const_mul_left hc
    _ =ᶠ[atTop] fun x => x ^ (c.re - 1) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [norm_cpow_eq_rpow_re_of_pos hx]; rw [sub_re]; rw [one_re]

/--
theorem `isBigO_deriv_ofReal_cpow_const_atTop` / 定理 `isBigO_deriv_ofReal_cpow_const_atTop`

English:
theorem isBigO_deriv_ofReal_cpow_const_atTop
  given: (c : Complex)
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · simp_rw [cpow_zero, deriv_const', Asymptotics.isBigO_zero]
  · exact (isTheta_deriv_ofReal_cpow_const_atTop hc).1

中文:
定理 isBigO_deriv_of实数_cpow_const_atTop
  条件: (c : 复形)
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · simp_rw [cpow_zero, deriv_const', Asymptotics.isBigO_zero]
  · exact (isTheta_deriv_ofReal_cpow_const_atTop hc).1

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_zero, cpow_zero, deriv_const, eq_or_ne, isBigO_zero, isTheta_deriv_ofReal_cpow_const_atTop, simp_rw
-/
theorem isBigO_deriv_ofReal_cpow_const_atTop (c : Complex) :
    deriv (fun (x : Real) => (x : Complex) ^ c) =O[atTop] fun x => x ^ (c.re - 1) := by
  obtain rfl | hc := eq_or_ne c 0
  · simp_rw [cpow_zero, deriv_const', Asymptotics.isBigO_zero]
  · exact (isTheta_deriv_ofReal_cpow_const_atTop hc).1

end deriv

namespace Real

variable {x y z : Real}

/--
theorem `hasStrictFDerivAt_rpow_of_pos` / 定理 `hasStrictFDerivAt_rpow_of_pos`

English:
theorem hasStrictFDerivAt_rpow_of_pos
  given: (p : Real × Real) (hp : 0 < p.1)
  proof: by
  have : (fun x : Real × Real => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    (continuousAt_fst.eventually (lt_mem_nhds hp)).mono fun p hp => rpow_def_of_pos hp _
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  convert! ((hasStrictFDerivAt_fst.log hp.ne').fun_mul hasStri

中文:
定理 hasStrictFDerivAt_rpow_of_pos
  条件: (p : 实数 × 实数) (hp : 0 < p.1)
  证明: by
  have : (fun x : Real × Real => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    (continuousAt_fst.eventually (lt_mem_nhds hp)).mono fun p hp => rpow_def_of_pos hp _
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  convert! ((hasStrictFDerivAt_fst.log hp.ne').fun_mul hasStri

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.congr_of_eventuallyEq, congr_of_eventuallyEq, continuousAt_fst, continuousAt_fst.eventually, convert, div_eq_mul_inv, eventually, fun_mul, hasStrictFDerivAt_fst, hasStrictFDerivAt_fst.log, hasStrictFDerivAt_snd, hp.ne, lt_mem_nhds, mul_assoc, mul_div_left_comm, rpow_def_of_pos, rpow_sub_one, smul_add, smul_smul
-/
theorem hasStrictFDerivAt_rpow_of_pos (p : Real × Real) (hp : 0 < p.1) :
    HasStrictFDerivAt (fun x : Real × Real => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst Real Real Real +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd Real Real Real) p := by
  have : (fun x : Real × Real => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    (continuousAt_fst.eventually (lt_mem_nhds hp)).mono fun p hp => rpow_def_of_pos hp _
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  convert! ((hasStrictFDerivAt_fst.log hp.ne').fun_mul hasStrictFDerivAt_snd).exp using 1
  rw [rpow_sub_one hp.ne']; rw [← rpow_def_of_pos hp]; rw [smul_add]; rw [smul_smul]; rw [mul_div_left_comm]; rw [div_eq_mul_inv]; rw [smul_smul]; rw [smul_smul]; rw [mul_assoc]; rw [add_comm]

/--
theorem `hasStrictFDerivAt_rpow_of_neg` / 定理 `hasStrictFDerivAt_rpow_of_neg`

English:
theorem hasStrictFDerivAt_rpow_of_neg
  given: (p : Real × Real) (hp : p.1 < 0)
  proof: by
  have : (fun x : Real × Real => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) :=
    (continuousAt_fst.eventually (gt_mem_nhds hp)).mono fun p hp => rpow_def_of_neg hp _
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  convert!
    ((hasStrictFDerivAt_fst.log hp.

中文:
定理 hasStrictFDerivAt_rpow_of_neg
  条件: (p : 实数 × 实数) (hp : p.1 < 0)
  证明: by
  have : (fun x : Real × Real => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) :=
    (continuousAt_fst.eventually (gt_mem_nhds hp)).mono fun p hp => rpow_def_of_neg hp _
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  convert!
    ((hasStrictFDerivAt_fst.log hp.

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.congr_of_eventuallyEq, add_assoc, add_smul, congr_of_eventuallyEq, continuousAt_fst, continuousAt_fst.eventually, convert, eventually, exp.fun_mul, fun_mul, gt_mem_nhds, hasStrictFDerivAt_fst, hasStrictFDerivAt_fst.log, hasStrictFDerivAt_snd, hasStrictFDerivAt_snd.mul_const, hp.ne, mul_assoc, mul_comm, mul_const
-/
theorem hasStrictFDerivAt_rpow_of_neg (p : Real × Real) (hp : p.1 < 0) :
    HasStrictFDerivAt (fun x : Real × Real => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst Real Real Real +
        (p.1 ^ p.2 * log p.1 - exp (log p.1 * p.2) * sin (p.2 * π) * π) •
          ContinuousLinearMap.snd Real Real Real) p := by
  have : (fun x : Real × Real => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) :=
    (continuousAt_fst.eventually (gt_mem_nhds hp)).mono fun p hp => rpow_def_of_neg hp _
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  convert!
    ((hasStrictFDerivAt_fst.log hp.ne).fun_mul hasStrictFDerivAt_snd).exp.fun_mul
      (hasStrictFDerivAt_snd.mul_const π).cos using 1
  simp_rw [rpow_sub_one hp.ne, smul_add, ← add_assoc, smul_smul, ← add_smul, ← mul_assoc,
    mul_comm (cos _), ← rpow_def_of_neg hp]
  rw [div_eq_mul_inv]; rw [add_comm]; congr 2 <;> ring

/--
theorem `contDiffAt_rpow_of_ne` / 定理 `contDiffAt_rpow_of_ne`

English:
theorem contDiffAt_rpow_of_ne
  given: (p : Real × Real) (hp : p.1 != 0) {n : WithTop Nat∞}
  proof: by
  rcases hp.lt_or_gt with hneg | hpos
  exacts
    [(((contDiffAt_fst.log hneg.ne).mul contDiffAt_snd).exp.mul
          (contDiffAt_snd.mul contDiffAt_const).cos).congr_of_eventuallyEq
      ((continuousAt_fst.eventually (gt_mem_nhds hneg)).mono fun p hp => rpow_def_of_neg hp _),
    ((contDiffA

中文:
定理 contDiffAt_rpow_of_ne
  条件: (p : 实数 × 实数) (hp : p.1 != 0) {n : WithTop 自然数∞}
  证明: by
  rcases hp.lt_or_gt with hneg | hpos
  exacts
    [(((contDiffAt_fst.log hneg.ne).mul contDiffAt_snd).exp.mul
          (contDiffAt_snd.mul contDiffAt_const).cos).congr_of_eventuallyEq
      ((continuousAt_fst.eventually (gt_mem_nhds hneg)).mono fun p hp => rpow_def_of_neg hp _),
    ((contDiffA

Depends on / 依赖: congr_of_eventuallyEq, contDiffAt_const, contDiffAt_fst, contDiffAt_fst.log, contDiffAt_snd, contDiffAt_snd.mul, continuousAt_fst, continuousAt_fst.eventually, eventually, exacts, exp.congr_of_eventuallyEq, exp.mul, gt_mem_nhds, hneg.ne, hp.lt_or_gt, hpos.ne, lt_mem_nhds, lt_or_gt, rpow_def_of_neg, rpow_def_of_pos
-/
theorem contDiffAt_rpow_of_ne (p : Real × Real) (hp : p.1 != 0) {n : WithTop Nat∞} :
    ContDiffAt Real n (fun p : Real × Real => p.1 ^ p.2) p := by
  rcases hp.lt_or_gt with hneg | hpos
  exacts
    [(((contDiffAt_fst.log hneg.ne).mul contDiffAt_snd).exp.mul
          (contDiffAt_snd.mul contDiffAt_const).cos).congr_of_eventuallyEq
      ((continuousAt_fst.eventually (gt_mem_nhds hneg)).mono fun p hp => rpow_def_of_neg hp _),
    ((contDiffAt_fst.log hpos.ne').mul contDiffAt_snd).exp.congr_of_eventuallyEq
      ((continuousAt_fst.eventually (lt_mem_nhds hpos)).mono fun p hp => rpow_def_of_pos hp _)]

/--
theorem `differentiableAt_rpow_of_ne` / 定理 `differentiableAt_rpow_of_ne`

English:
theorem differentiableAt_rpow_of_ne
  given: (p : Real × Real) (hp : p.1 != 0)
  proof: (contDiffAt_rpow_of_ne p hp).differentiableAt one_ne_zero

中文:
定理 differentiableAt_rpow_of_ne
  条件: (p : 实数 × 实数) (hp : p.1 != 0)
  证明: (contDiffAt_rpow_of_ne p hp).differentiableAt one_ne_zero

Depends on / 依赖: contDiffAt_rpow_of_ne, differentiableAt, one_ne_zero
-/
theorem differentiableAt_rpow_of_ne (p : Real × Real) (hp : p.1 != 0) :
    DifferentiableAt Real (fun p : Real × Real => p.1 ^ p.2) p :=
  (contDiffAt_rpow_of_ne p hp).differentiableAt one_ne_zero

/--
theorem `_root_.HasStrictDerivAt.rpow` / 定理 `_root_.HasStrictDerivAt.rpow`

English:
theorem _root_.HasStrictDerivAt.rpow
  statement: {f g : Real -> Real} {f' g' : Real} (hf : HasStrictDerivAt f f' x)
  proof: by
  convert!
    (hasStrictFDerivAt_rpow_of_pos ((fun x => (f x, g x)) x) h).comp_hasStrictDerivAt x
      (hf.prodMk hg) using 1
  simp [mul_assoc, mul_comm]

中文:
定理 _root_.HasStrictDerivAt.rpow
  结论: {f g : 实数 -> 实数} {f' g' : 实数} (hf : HasStrictDerivAt f f' x)
  证明: by
  convert!
    (hasStrictFDerivAt_rpow_of_pos ((fun x => (f x, g x)) x) h).comp_hasStrictDerivAt x
      (hf.prodMk hg) using 1
  simp [mul_assoc, mul_comm]

Depends on / 依赖: comp_hasStrictDerivAt, convert, hasStrictFDerivAt_rpow_of_pos, hf.prodMk, mul_assoc, mul_comm, prodMk
-/
theorem _root_.HasStrictDerivAt.rpow {f g : Real -> Real} {f' g' : Real} (hf : HasStrictDerivAt f f' x)
    (hg : HasStrictDerivAt g g' x) (h : 0 < f x) : HasStrictDerivAt (fun x => f x ^ g x)
      (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * Real.log (f x)) x := by
  convert!
    (hasStrictFDerivAt_rpow_of_pos ((fun x => (f x, g x)) x) h).comp_hasStrictDerivAt x
      (hf.prodMk hg) using 1
  simp [mul_assoc, mul_comm]

/--
theorem `hasStrictDerivAt_rpow_const_of_ne` / 定理 `hasStrictDerivAt_rpow_const_of_ne`

English:
theorem hasStrictDerivAt_rpow_const_of_ne
  given: {x : Real} (hx : x != 0) (p : Real)
  proof: by
  rcases hx.lt_or_gt with hx | hx
  · have := (hasStrictFDerivAt_rpow_of_neg (x, p) hx).comp_hasStrictDerivAt x
      ((hasStrictDerivAt_id x).prodMk (hasStrictDerivAt_const x p))
    convert! this using 1; simp
  · simpa using (hasStrictDerivAt_id x).rpow (hasStrictDerivAt_const x p) hx

中文:
定理 hasStrictDerivAt_rpow_const_of_ne
  条件: {x : 实数} (hx : x != 0) (p : 实数)
  证明: by
  rcases hx.lt_or_gt with hx | hx
  · have := (hasStrictFDerivAt_rpow_of_neg (x, p) hx).comp_hasStrictDerivAt x
      ((hasStrictDerivAt_id x).prodMk (hasStrictDerivAt_const x p))
    convert! this using 1; simp
  · simpa using (hasStrictDerivAt_id x).rpow (hasStrictDerivAt_const x p) hx

Depends on / 依赖: comp_hasStrictDerivAt, convert, hasStrictDerivAt_const, hasStrictDerivAt_id, hasStrictFDerivAt_rpow_of_neg, hx.lt_or_gt, lt_or_gt, prodMk
-/
theorem hasStrictDerivAt_rpow_const_of_ne {x : Real} (hx : x != 0) (p : Real) :
    HasStrictDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x := by
  rcases hx.lt_or_gt with hx | hx
  · have := (hasStrictFDerivAt_rpow_of_neg (x, p) hx).comp_hasStrictDerivAt x
      ((hasStrictDerivAt_id x).prodMk (hasStrictDerivAt_const x p))
    convert! this using 1; simp
  · simpa using (hasStrictDerivAt_id x).rpow (hasStrictDerivAt_const x p) hx

/--
theorem `hasStrictDerivAt_const_rpow` / 定理 `hasStrictDerivAt_const_rpow`

English:
theorem hasStrictDerivAt_const_rpow
  given: {a : Real} (ha : 0 < a) (x : Real)
  proof: by
  simpa using (hasStrictDerivAt_const _ _).rpow (hasStrictDerivAt_id x) ha

中文:
定理 hasStrictDerivAt_const_rpow
  条件: {a : 实数} (ha : 0 < a) (x : 实数)
  证明: by
  simpa using (hasStrictDerivAt_const _ _).rpow (hasStrictDerivAt_id x) ha

Depends on / 依赖: hasStrictDerivAt_const, hasStrictDerivAt_id
-/
theorem hasStrictDerivAt_const_rpow {a : Real} (ha : 0 < a) (x : Real) :
    HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a) x := by
  simpa using (hasStrictDerivAt_const _ _).rpow (hasStrictDerivAt_id x) ha

/--
lemma `differentiableAt_rpow_const_of_ne` / 引理 `differentiableAt_rpow_const_of_ne`

English:
lemma differentiableAt_rpow_const_of_ne
  given: (p : Real) {x : Real} (hx : x != 0)
  proof: (hasStrictDerivAt_rpow_const_of_ne hx p).hasStrictFDerivAt.differentiableAt

中文:
引理 differentiableAt_rpow_const_of_ne
  条件: (p : 实数) {x : 实数} (hx : x != 0)
  证明: (hasStrictDerivAt_rpow_const_of_ne hx p).hasStrictFDerivAt.differentiableAt

Depends on / 依赖: differentiableAt, hasStrictDerivAt_rpow_const_of_ne, hasStrictFDerivAt, hasStrictFDerivAt.differentiableAt
-/
lemma differentiableAt_rpow_const_of_ne (p : Real) {x : Real} (hx : x != 0) :
    DifferentiableAt Real (fun x => x ^ p) x :=
  (hasStrictDerivAt_rpow_const_of_ne hx p).hasStrictFDerivAt.differentiableAt

/--
theorem `not_differentiableAt_rpow_const_zero` / 定理 `not_differentiableAt_rpow_const_zero`

English:
theorem not_differentiableAt_rpow_const_zero
  given: {r : Real} (hr : r < 1) (hr' : r != 0)
  proof: by
  by_contra h
  set y := deriv (fun x => x ^ r) (0 : Real)
  -- If `x ^ r` was differentiable at `0`, then `x ^ (r - 1)` would have a finite limit at `0`.
  have h : Filter.Tendsto (fun t => t ^ (r - 1)) (𝓝[>] 0) (𝓝 y) := by
    apply tendsto_nhdsWithin_congr _ h.hasDerivAt.tendsto_slope_zero_rig

中文:
定理 not_differentiableAt_rpow_const_zero
  条件: {r : 实数} (hr : r < 1) (hr' : r != 0)
  证明: by
  by_contra h
  set y := deriv (fun x => x ^ r) (0 : Real)
  -- If `x ^ r` was differentiable at `0`, then `x ^ (r - 1)` would have a finite limit at `0`.
  have h : Filter.Tendsto (fun t => t ^ (r - 1)) (𝓝[>] 0) (𝓝 y) := by
    apply tendsto_nhdsWithin_congr _ h.hasDerivAt.tendsto_slope_zero_rig
-/
theorem not_differentiableAt_rpow_const_zero {r : Real} (hr : r < 1) (hr' : r != 0) :
    ¬ DifferentiableAt Real (fun x => x ^ r) (0 : Real) := by
  by_contra h
  set y := deriv (fun x => x ^ r) (0 : Real)
  -- If `x ^ r` was differentiable at `0`, then `x ^ (r - 1)` would have a finite limit at `0`.
  have h : Filter.Tendsto (fun t => t ^ (r - 1)) (𝓝[>] 0) (𝓝 y) := by
    apply tendsto_nhdsWithin_congr _ h.hasDerivAt.tendsto_slope_zero_right
    intro x (hx : 0 < x)
    simp only [zero_add, ne_eq, hr', not_false_eq_true, Real.zero_rpow, sub_zero, smul_eq_mul]
    field_simp
    nth_rw 1 [← add_sub_cancel 1 r, Real.rpow_add hx]
    simp
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_rpow_neg_nhdsGT_zero (by simp [hr])) y h

/--
lemma `differentiableOn_rpow_const` / 引理 `differentiableOn_rpow_const`

English:
lemma differentiableOn_rpow_const
  given: (p : Real)
  proof: fun _ hx => (Real.differentiableAt_rpow_const_of_ne p hx).differentiableWithinAt

中文:
引理 differentiableOn_rpow_const
  条件: (p : 实数)
  证明: fun _ hx => (Real.differentiableAt_rpow_const_of_ne p hx).differentiableWithinAt

Depends on / 依赖: Real.differentiableAt_rpow_const_of_ne, differentiableAt_rpow_const_of_ne, differentiableWithinAt
-/
lemma differentiableOn_rpow_const (p : Real) :
    DifferentiableOn Real (fun x => (x : Real) ^ p) {0}ᶜ :=
  fun _ hx => (Real.differentiableAt_rpow_const_of_ne p hx).differentiableWithinAt

/--
theorem `hasStrictDerivAt_const_rpow_of_neg` / 定理 `hasStrictDerivAt_const_rpow_of_neg`

English:
theorem hasStrictDerivAt_const_rpow_of_neg
  given: {a x : Real} (ha : a < 0)
  proof: by
  simpa using! (hasStrictFDerivAt_rpow_of_neg (a, x) ha).comp_hasStrictDerivAt x
    ((hasStrictDerivAt_const _ _).prodMk (hasStrictDerivAt_id _))

中文:
定理 hasStrictDerivAt_const_rpow_of_neg
  条件: {a x : 实数} (ha : a < 0)
  证明: by
  simpa using! (hasStrictFDerivAt_rpow_of_neg (a, x) ha).comp_hasStrictDerivAt x
    ((hasStrictDerivAt_const _ _).prodMk (hasStrictDerivAt_id _))

Depends on / 依赖: comp_hasStrictDerivAt, hasStrictDerivAt_const, hasStrictDerivAt_id, hasStrictFDerivAt_rpow_of_neg, prodMk
-/
theorem hasStrictDerivAt_const_rpow_of_neg {a x : Real} (ha : a < 0) :
    HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a - exp (log a * x) * sin (x * π) * π) x := by
  simpa using! (hasStrictFDerivAt_rpow_of_neg (a, x) ha).comp_hasStrictDerivAt x
    ((hasStrictDerivAt_const _ _).prodMk (hasStrictDerivAt_id _))

end Real

namespace Real

variable {z x y : Real}

/--
theorem `hasDerivAt_rpow_const` / 定理 `hasDerivAt_rpow_const`

English:
theorem hasDerivAt_rpow_const
  given: {x p : Real} (h : x != 0 ∨ 1 <= p)
  proof: by
  rcases ne_or_eq x 0 with (hx | rfl)
  · exact (hasStrictDerivAt_rpow_const_of_ne hx _).hasDerivAt
  replace h : 1 <= p := h.neg_resolve_left rfl
  apply hasDerivAt_of_hasDerivAt_of_ne fun x hx =>
    (hasStrictDerivAt_rpow_const_of_ne hx p).hasDerivAt
  exacts [continuousAt_id.rpow_const (Or.in

中文:
定理 hasDerivAt_rpow_const
  条件: {x p : 实数} (h : x != 0 ∨ 1 <= p)
  证明: by
  rcases ne_or_eq x 0 with (hx | rfl)
  · exact (hasStrictDerivAt_rpow_const_of_ne hx _).hasDerivAt
  replace h : 1 <= p := h.neg_resolve_left rfl
  apply hasDerivAt_of_hasDerivAt_of_ne fun x hx =>
    (hasStrictDerivAt_rpow_const_of_ne hx p).hasDerivAt
  exacts [continuousAt_id.rpow_const (Or.in

Depends on / 依赖: Or.inr, continuousAt_const, continuousAt_const.mul, continuousAt_id, continuousAt_id.rpow_const, exacts, h.neg_resolve_left, hasDerivAt, hasDerivAt_of_hasDerivAt_of_ne, hasStrictDerivAt_rpow_const_of_ne, ne_or_eq, neg_resolve_left, replace, rpow_const, sub_nonneg, zero_le_one, zero_le_one.trans
-/
theorem hasDerivAt_rpow_const {x p : Real} (h : x != 0 ∨ 1 <= p) :
    HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x := by
  rcases ne_or_eq x 0 with (hx | rfl)
  · exact (hasStrictDerivAt_rpow_const_of_ne hx _).hasDerivAt
  replace h : 1 <= p := h.neg_resolve_left rfl
  apply hasDerivAt_of_hasDerivAt_of_ne fun x hx =>
    (hasStrictDerivAt_rpow_const_of_ne hx p).hasDerivAt
  exacts [continuousAt_id.rpow_const (Or.inr (zero_le_one.trans h)),
    continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr (sub_nonneg.2 h)))]

/--
theorem `differentiable_rpow_const` / 定理 `differentiable_rpow_const`

English:
theorem differentiable_rpow_const
  given: {p : Real} (hp : 1 <= p)
  statement: Differentiable Real fun x : Real => x ^ p
  proof: fun _ => (hasDerivAt_rpow_const (Or.inr hp)).differentiableAt

中文:
定理 differentiable_rpow_const
  条件: {p : 实数} (hp : 1 <= p)
  结论: 可微 实数 fun x : 实数 => x ^ p
  证明: fun _ => (hasDerivAt_rpow_const (Or.inr hp)).differentiableAt

Depends on / 依赖: Or.inr, differentiableAt, hasDerivAt_rpow_const
-/
theorem differentiable_rpow_const {p : Real} (hp : 1 <= p) : Differentiable Real fun x : Real => x ^ p :=
  fun _ => (hasDerivAt_rpow_const (Or.inr hp)).differentiableAt

/--
theorem `deriv_rpow_const` / 定理 `deriv_rpow_const`

English:
theorem deriv_rpow_const
  given: (x p : Real)
  statement: deriv (fun x => x ^ p) x = p * x ^ (p - 1)
  proof: by
  by_cases! h : p = 0
  · simp [h]
  by_cases! h' : x != 0 ∨ 1 <= p
  · apply (Real.hasDerivAt_rpow_const h').deriv
  have h'' := deriv_zero_of_not_differentiableAt (not_differentiableAt_rpow_const_zero h'.2 h ·)
  grind [Real.zero_rpow]

中文:
定理 deriv_rpow_const
  条件: (x p : 实数)
  结论: deriv (fun x => x ^ p) x = p * x ^ (p - 1)
  证明: by
  by_cases! h : p = 0
  · simp [h]
  by_cases! h' : x != 0 ∨ 1 <= p
  · apply (Real.hasDerivAt_rpow_const h').deriv
  have h'' := deriv_zero_of_not_differentiableAt (not_differentiableAt_rpow_const_zero h'.2 h ·)
  grind [Real.zero_rpow]

Depends on / 依赖: Real.hasDerivAt_rpow_const, Real.zero_rpow, deriv_zero_of_not_differentiableAt, hasDerivAt_rpow_const, not_differentiableAt_rpow_const_zero, zero_rpow
-/
theorem deriv_rpow_const (x p : Real) : deriv (fun x => x ^ p) x = p * x ^ (p - 1) := by
  by_cases! h : p = 0
  · simp [h]
  by_cases! h' : x != 0 ∨ 1 <= p
  · apply (Real.hasDerivAt_rpow_const h').deriv
  have h'' := deriv_zero_of_not_differentiableAt (not_differentiableAt_rpow_const_zero h'.2 h ·)
  grind [Real.zero_rpow]

/--
theorem `deriv_rpow_const'` / 定理 `deriv_rpow_const'`

English:
theorem deriv_rpow_const'
  given: (p : Real)
  proof: funext (deriv_rpow_const · p)

中文:
定理 deriv_rpow_const'
  条件: (p : 实数)
  证明: funext (deriv_rpow_const · p)

Depends on / 依赖: deriv_rpow_const
-/
theorem deriv_rpow_const' (p : Real) :
    (deriv fun x : Real => x ^ p) = fun x => p * x ^ (p - 1) :=
  funext (deriv_rpow_const · p)

/--
theorem `contDiffAt_rpow_const_of_ne` / 定理 `contDiffAt_rpow_const_of_ne`

English:
theorem contDiffAt_rpow_const_of_ne
  given: {x p : Real} {n : WithTop Nat∞} (h : x != 0)
  proof: (contDiffAt_rpow_of_ne (x, p) h).comp x (contDiffAt_id.prodMk contDiffAt_const)

中文:
定理 contDiffAt_rpow_const_of_ne
  条件: {x p : 实数} {n : WithTop 自然数∞} (h : x != 0)
  证明: (contDiffAt_rpow_of_ne (x, p) h).comp x (contDiffAt_id.prodMk contDiffAt_const)

Depends on / 依赖: contDiffAt_const, contDiffAt_id, contDiffAt_id.prodMk, contDiffAt_rpow_of_ne, prodMk
-/
theorem contDiffAt_rpow_const_of_ne {x p : Real} {n : WithTop Nat∞} (h : x != 0) :
    ContDiffAt Real n (fun x => x ^ p) x :=
  (contDiffAt_rpow_of_ne (x, p) h).comp x (contDiffAt_id.prodMk contDiffAt_const)

/--
theorem `contDiff_rpow_const_of_le` / 定理 `contDiff_rpow_const_of_le`

English:
theorem contDiff_rpow_const_of_le
  given: {p : Real} {n : Nat} (h : ↑n <= p)
  proof: by
  induction n generalizing p with
  | zero => exact contDiff_zero.2 (continuous_id.rpow_const fun x => Or.inr <| by simpa using h)
  | succ n ihn =>
    have h1 : 1 <= p := le_trans (by simp) h
    rw [Nat.cast_add_one]; rw [← le_sub_iff_add_le] at h
    rw [Nat.cast_add_one]; rw [contDiff_succ_i

中文:
定理 contDiff_rpow_const_of_le
  条件: {p : 实数} {n : 自然数} (h : ↑n <= p)
  证明: by
  induction n generalizing p with
  | zero => exact contDiff_zero.2 (continuous_id.rpow_const fun x => Or.inr <| by simpa using h)
  | succ n ihn =>
    have h1 : 1 <= p := le_trans (by simp) h
    rw [Nat.cast_add_one]; rw [← le_sub_iff_add_le] at h
    rw [Nat.cast_add_one]; rw [contDiff_succ_i

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff, Nat.cast_add_one, Or.inr, WithTop, WithTop.natCast_ne_top, analyticOn_univ, cast_add_one, contDiff_const, contDiff_const.mul, contDiff_succ_iff_deriv, contDiff_zero, continuous_id, continuous_id.rpow_const, deriv_rpow_const, differentiable_rpow_const, forall_iff, generalizing, le_sub_iff_add_le, le_trans
-/
theorem contDiff_rpow_const_of_le {p : Real} {n : Nat} (h : ↑n <= p) :
    ContDiff Real n fun x : Real => x ^ p := by
  induction n generalizing p with
  | zero => exact contDiff_zero.2 (continuous_id.rpow_const fun x => Or.inr <| by simpa using h)
  | succ n ihn =>
    have h1 : 1 <= p := le_trans (by simp) h
    rw [Nat.cast_add_one]; rw [← le_sub_iff_add_le] at h
    rw [Nat.cast_add_one]; rw [contDiff_succ_iff_deriv]; rw [deriv_rpow_const' p]
    simp only [WithTop.natCast_ne_top, analyticOn_univ, IsEmpty.forall_iff, true_and]
    exact ⟨differentiable_rpow_const h1, contDiff_const.mul (ihn h)⟩

/--
theorem `contDiffAt_rpow_const_of_le` / 定理 `contDiffAt_rpow_const_of_le`

English:
theorem contDiffAt_rpow_const_of_le
  given: {x p : Real} {n : Nat} (h : ↑n <= p)
  proof: (contDiff_rpow_const_of_le h).contDiffAt

中文:
定理 contDiffAt_rpow_const_of_le
  条件: {x p : 实数} {n : 自然数} (h : ↑n <= p)
  证明: (contDiff_rpow_const_of_le h).contDiffAt

Depends on / 依赖: contDiffAt, contDiff_rpow_const_of_le
-/
theorem contDiffAt_rpow_const_of_le {x p : Real} {n : Nat} (h : ↑n <= p) :
    ContDiffAt Real n (fun x : Real => x ^ p) x :=
  (contDiff_rpow_const_of_le h).contDiffAt

/--
theorem `contDiffAt_rpow_const` / 定理 `contDiffAt_rpow_const`

English:
theorem contDiffAt_rpow_const
  given: {x p : Real} {n : Nat} (h : x != 0 ∨ ↑n <= p)
  proof: h.elim contDiffAt_rpow_const_of_ne contDiffAt_rpow_const_of_le

中文:
定理 contDiffAt_rpow_const
  条件: {x p : 实数} {n : 自然数} (h : x != 0 ∨ ↑n <= p)
  证明: h.elim contDiffAt_rpow_const_of_ne contDiffAt_rpow_const_of_le

Depends on / 依赖: contDiffAt_rpow_const_of_le, contDiffAt_rpow_const_of_ne, h.elim
-/
theorem contDiffAt_rpow_const {x p : Real} {n : Nat} (h : x != 0 ∨ ↑n <= p) :
    ContDiffAt Real n (fun x : Real => x ^ p) x :=
  h.elim contDiffAt_rpow_const_of_ne contDiffAt_rpow_const_of_le

/--
theorem `iter_deriv_rpow_const` / 定理 `iter_deriv_rpow_const`

English:
theorem iter_deriv_rpow_const
  given: (r x : Real) (k : Nat)
  proof: by
  apply funext_iff.mp
  induction k with
  | zero => simp
  | succ k IH =>
    simp only [Function.iterate_succ', Function.comp_apply, Nat.cast_add, Nat.cast_one, IH]
    ext y
    simp only [deriv_const_mul_field, deriv_rpow_const, ← mul_assoc, descPochhammer_succ_right,
      Polynomial.eval_mu

中文:
定理 iter_deriv_rpow_const
  条件: (r x : 实数) (k : 自然数)
  证明: by
  apply funext_iff.mp
  induction k with
  | zero => simp
  | succ k IH =>
    simp only [Function.iterate_succ', Function.comp_apply, Nat.cast_add, Nat.cast_one, IH]
    ext y
    simp only [deriv_const_mul_field, deriv_rpow_const, ← mul_assoc, descPochhammer_succ_right,
      Polynomial.eval_mu

Depends on / 依赖: Function, Function.comp_apply, Function.iterate_succ, Nat.cast_add, Nat.cast_one, Polynomial, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_sub, cast_add, cast_one, comp_apply, deriv_const_mul_field, deriv_rpow_const, descPochhammer_succ_right, eval_X, eval_mul, eval_natCast, eval_sub
-/
theorem iter_deriv_rpow_const (r x : Real) (k : Nat) :
    deriv^[k] (fun (x : Real) => x ^ r) x = (descPochhammer Real k).eval r * x ^ (r - k) := by
  apply funext_iff.mp
  induction k with
  | zero => simp
  | succ k IH =>
    simp only [Function.iterate_succ', Function.comp_apply, Nat.cast_add, Nat.cast_one, IH]
    ext y
    simp only [deriv_const_mul_field, deriv_rpow_const, ← mul_assoc, descPochhammer_succ_right,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
      mul_eq_mul_left_iff, mul_eq_zero]
    grind

/--
theorem `hasStrictDerivAt_rpow_const` / 定理 `hasStrictDerivAt_rpow_const`

English:
theorem hasStrictDerivAt_rpow_const
  given: {x p : Real} (hx : x != 0 ∨ 1 <= p)
  proof: ContDiffAt.hasStrictDerivAt' (contDiffAt_rpow_const (by rwa [← Nat.cast_one] at hx))
    (hasDerivAt_rpow_const hx) one_ne_zero

中文:
定理 hasStrictDerivAt_rpow_const
  条件: {x p : 实数} (hx : x != 0 ∨ 1 <= p)
  证明: ContDiffAt.hasStrictDerivAt' (contDiffAt_rpow_const (by rwa [← Nat.cast_one] at hx))
    (hasDerivAt_rpow_const hx) one_ne_zero

Depends on / 依赖: ContDiffAt, ContDiffAt.hasStrictDerivAt, Nat.cast_one, cast_one, contDiffAt_rpow_const, hasDerivAt_rpow_const, hasStrictDerivAt, one_ne_zero
-/
theorem hasStrictDerivAt_rpow_const {x p : Real} (hx : x != 0 ∨ 1 <= p) :
    HasStrictDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x :=
  ContDiffAt.hasStrictDerivAt' (contDiffAt_rpow_const (by rwa [← Nat.cast_one] at hx))
    (hasDerivAt_rpow_const hx) one_ne_zero

end Real

section Differentiability

open Real

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f g : E -> Real} {f' g' : StrongDual Real E}
  {x : E} {s : Set E} {c p : Real} {n : WithTop Nat∞}

/--
theorem `HasFDerivWithinAt.rpow` / 定理 `HasFDerivWithinAt.rpow`

English:
theorem HasFDerivWithinAt.rpow
  statement: (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x)
  proof: by
  -- `by exact` to deal with tricky unification.
  exact (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).hasFDerivAt.comp_hasFDerivWithinAt x
    (hf.prodMk hg)

中文:
定理 HasFDerivWithinAt.rpow
  结论: (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x)
  证明: by
  -- `by exact` to deal with tricky unification.
  exact (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).hasFDerivAt.comp_hasFDerivWithinAt x
    (hf.prodMk hg)
-/
theorem HasFDerivWithinAt.rpow (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x)
    (h : 0 < f x) : HasFDerivWithinAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') s x := by
  -- `by exact` to deal with tricky unification.
  exact (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).hasFDerivAt.comp_hasFDerivWithinAt x
    (hf.prodMk hg)

/--
theorem `HasFDerivAt.rpow` / 定理 `HasFDerivAt.rpow`

English:
theorem HasFDerivAt.rpow
  given: (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) (h : 0 < f x)
  proof: by
  exact (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).hasFDerivAt.comp x (hf.prodMk hg)

中文:
定理 在点处Fréchet可导.rpow
  条件: (hf : 在点处Fréchet可导 f f' x) (hg : 在点处Fréchet可导 g g' x) (h : 0 < f x)
  证明: by
  exact (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).hasFDerivAt.comp x (hf.prodMk hg)

Depends on / 依赖: hasFDerivAt, hasFDerivAt.comp, hasStrictFDerivAt_rpow_of_pos, hf.prodMk, prodMk
-/
theorem HasFDerivAt.rpow (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) (h : 0 < f x) :
    HasFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') x := by
  exact (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).hasFDerivAt.comp x (hf.prodMk hg)

/--
theorem `HasStrictFDerivAt.rpow` / 定理 `HasStrictFDerivAt.rpow`

English:
theorem HasStrictFDerivAt.rpow
  statement: (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
  proof: (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]

中文:
定理 HasStrictFDerivAt.rpow
  结论: (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
  证明: (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]

Depends on / 依赖: hasStrictFDerivAt_rpow_of_pos, hf.prodMk, prodMk
-/
theorem HasStrictFDerivAt.rpow (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
    (h : 0 < f x) : HasStrictFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') x :=
  (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]
/--
theorem `DifferentiableWithinAt.rpow` / 定理 `DifferentiableWithinAt.rpow`

English:
theorem DifferentiableWithinAt.rpow
  statement: (hf : DifferentiableWithinAt Real f s x)
  proof: by
  -- `by exact` to deal with tricky unification.
  exact (differentiableAt_rpow_of_ne (f x, g x) h).comp_differentiableWithinAt x (hf.prodMk hg)

@[fun_prop]

中文:
定理 DifferentiableWithinAt.rpow
  结论: (hf : DifferentiableWithinAt 实数 f s x)
  证明: by
  -- `by exact` to deal with tricky unification.
  exact (differentiableAt_rpow_of_ne (f x, g x) h).comp_differentiableWithinAt x (hf.prodMk hg)

@[fun_prop]
-/
theorem DifferentiableWithinAt.rpow (hf : DifferentiableWithinAt Real f s x)
    (hg : DifferentiableWithinAt Real g s x) (h : f x != 0) :
    DifferentiableWithinAt Real (fun x => f x ^ g x) s x := by
  -- `by exact` to deal with tricky unification.
  exact (differentiableAt_rpow_of_ne (f x, g x) h).comp_differentiableWithinAt x (hf.prodMk hg)

@[fun_prop]
/--
theorem `DifferentiableAt.rpow` / 定理 `DifferentiableAt.rpow`

English:
theorem DifferentiableAt.rpow
  statement: (hf : DifferentiableAt Real f x) (hg : DifferentiableAt Real g x)
  proof: by
  -- `by exact` to deal with tricky unification.
  exact (differentiableAt_rpow_of_ne (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]

中文:
定理 DifferentiableAt.rpow
  结论: (hf : DifferentiableAt 实数 f x) (hg : DifferentiableAt 实数 g x)
  证明: by
  -- `by exact` to deal with tricky unification.
  exact (differentiableAt_rpow_of_ne (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]
-/
theorem DifferentiableAt.rpow (hf : DifferentiableAt Real f x) (hg : DifferentiableAt Real g x)
    (h : f x != 0) : DifferentiableAt Real (fun x => f x ^ g x) x := by
  -- `by exact` to deal with tricky unification.
  exact (differentiableAt_rpow_of_ne (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]
/--
theorem `DifferentiableOn.rpow` / 定理 `DifferentiableOn.rpow`

English:
theorem DifferentiableOn.rpow
  statement: (hf : DifferentiableOn Real f s) (hg : DifferentiableOn Real g s)
  proof: fun x hx =>
  (hf x hx).rpow (hg x hx) (h x hx)

@[fun_prop]

中文:
定理 DifferentiableOn.rpow
  结论: (hf : DifferentiableOn 实数 f s) (hg : DifferentiableOn 实数 g s)
  证明: fun x hx =>
  (hf x hx).rpow (hg x hx) (h x hx)

@[fun_prop]
-/
theorem DifferentiableOn.rpow (hf : DifferentiableOn Real f s) (hg : DifferentiableOn Real g s)
    (h : forall x in s, f x != 0) : DifferentiableOn Real (fun x => f x ^ g x) s := fun x hx =>
  (hf x hx).rpow (hg x hx) (h x hx)

@[fun_prop]
/--
theorem `Differentiable.rpow` / 定理 `Differentiable.rpow`

English:
theorem Differentiable.rpow
  given: (hf : Differentiable Real f) (hg : Differentiable Real g) (h : forall x, f x != 0)
  proof: fun x => (hf x).rpow (hg x) (h x)

@[fun_prop]

中文:
定理 可微.rpow
  条件: (hf : 可微 实数 f) (hg : 可微 实数 g) (h : 对任意 x, f x != 0)
  证明: fun x => (hf x).rpow (hg x) (h x)

@[fun_prop]
-/
theorem Differentiable.rpow (hf : Differentiable Real f) (hg : Differentiable Real g) (h : forall x, f x != 0) :
    Differentiable Real fun x => f x ^ g x := fun x => (hf x).rpow (hg x) (h x)

@[fun_prop]
/--
theorem `HasFDerivWithinAt.rpow_const` / 定理 `HasFDerivWithinAt.rpow_const`

English:
theorem HasFDerivWithinAt.rpow_const
  given: (hf : HasFDerivWithinAt f f' s x) (h : f x != 0 ∨ 1 <= p)
  proof: (hasDerivAt_rpow_const h).comp_hasFDerivWithinAt x hf

@[fun_prop]

中文:
定理 HasFDerivWithinAt.rpow_const
  条件: (hf : HasFDerivWithinAt f f' s x) (h : f x != 0 ∨ 1 <= p)
  证明: (hasDerivAt_rpow_const h).comp_hasFDerivWithinAt x hf

@[fun_prop]

Depends on / 依赖: comp_hasFDerivWithinAt, hasDerivAt_rpow_const
-/
theorem HasFDerivWithinAt.rpow_const (hf : HasFDerivWithinAt f f' s x) (h : f x != 0 ∨ 1 <= p) :
    HasFDerivWithinAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') s x :=
  (hasDerivAt_rpow_const h).comp_hasFDerivWithinAt x hf

@[fun_prop]
/--
theorem `HasFDerivAt.rpow_const` / 定理 `HasFDerivAt.rpow_const`

English:
theorem HasFDerivAt.rpow_const
  given: (hf : HasFDerivAt f f' x) (h : f x != 0 ∨ 1 <= p)
  proof: (hasDerivAt_rpow_const h).comp_hasFDerivAt x hf

中文:
定理 在点处Fréchet可导.rpow_const
  条件: (hf : 在点处Fréchet可导 f f' x) (h : f x != 0 ∨ 1 <= p)
  证明: (hasDerivAt_rpow_const h).comp_hasFDerivAt x hf

Depends on / 依赖: comp_hasFDerivAt, hasDerivAt_rpow_const
-/
theorem HasFDerivAt.rpow_const (hf : HasFDerivAt f f' x) (h : f x != 0 ∨ 1 <= p) :
    HasFDerivAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') x :=
  (hasDerivAt_rpow_const h).comp_hasFDerivAt x hf

/--
theorem `HasStrictFDerivAt.rpow_const` / 定理 `HasStrictFDerivAt.rpow_const`

English:
theorem HasStrictFDerivAt.rpow_const
  given: (hf : HasStrictFDerivAt f f' x) (h : f x != 0 ∨ 1 <= p)
  proof: (hasStrictDerivAt_rpow_const h).comp_hasStrictFDerivAt x hf

@[fun_prop]

中文:
定理 HasStrictFDerivAt.rpow_const
  条件: (hf : HasStrictFDerivAt f f' x) (h : f x != 0 ∨ 1 <= p)
  证明: (hasStrictDerivAt_rpow_const h).comp_hasStrictFDerivAt x hf

@[fun_prop]

Depends on / 依赖: comp_hasStrictFDerivAt, hasStrictDerivAt_rpow_const
-/
theorem HasStrictFDerivAt.rpow_const (hf : HasStrictFDerivAt f f' x) (h : f x != 0 ∨ 1 <= p) :
    HasStrictFDerivAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') x :=
  (hasStrictDerivAt_rpow_const h).comp_hasStrictFDerivAt x hf

@[fun_prop]
/--
theorem `DifferentiableWithinAt.rpow_const` / 定理 `DifferentiableWithinAt.rpow_const`

English:
theorem DifferentiableWithinAt.rpow_const
  statement: (hf : DifferentiableWithinAt Real f s x)
  proof: (hf.hasFDerivWithinAt.rpow_const h).differentiableWithinAt

@[simp]

中文:
定理 DifferentiableWithinAt.rpow_const
  结论: (hf : DifferentiableWithinAt 实数 f s x)
  证明: (hf.hasFDerivWithinAt.rpow_const h).differentiableWithinAt

@[simp]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.rpow_const, rpow_const
-/
theorem DifferentiableWithinAt.rpow_const (hf : DifferentiableWithinAt Real f s x)
    (h : f x != 0 ∨ 1 <= p) : DifferentiableWithinAt Real (fun x => f x ^ p) s x :=
  (hf.hasFDerivWithinAt.rpow_const h).differentiableWithinAt

@[simp]
/--
theorem `DifferentiableAt.rpow_const` / 定理 `DifferentiableAt.rpow_const`

English:
theorem DifferentiableAt.rpow_const
  given: (hf : DifferentiableAt Real f x) (h : f x != 0 ∨ 1 <= p)
  proof: (hf.hasFDerivAt.rpow_const h).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.rpow_const
  条件: (hf : DifferentiableAt 实数 f x) (h : f x != 0 ∨ 1 <= p)
  证明: (hf.hasFDerivAt.rpow_const h).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt, hf.hasFDerivAt.rpow_const, rpow_const
-/
theorem DifferentiableAt.rpow_const (hf : DifferentiableAt Real f x) (h : f x != 0 ∨ 1 <= p) :
    DifferentiableAt Real (fun x => f x ^ p) x :=
  (hf.hasFDerivAt.rpow_const h).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableOn.rpow_const` / 定理 `DifferentiableOn.rpow_const`

English:
theorem DifferentiableOn.rpow_const
  given: (hf : DifferentiableOn Real f s) (h : forall x in s, f x != 0 ∨ 1 <= p)
  proof: fun x hx => (hf x hx).rpow_const (h x hx)

@[fun_prop]

中文:
定理 DifferentiableOn.rpow_const
  条件: (hf : DifferentiableOn 实数 f s) (h : 对任意 x in s, f x != 0 ∨ 1 <= p)
  证明: fun x hx => (hf x hx).rpow_const (h x hx)

@[fun_prop]

Depends on / 依赖: rpow_const
-/
theorem DifferentiableOn.rpow_const (hf : DifferentiableOn Real f s) (h : forall x in s, f x != 0 ∨ 1 <= p) :
    DifferentiableOn Real (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const (h x hx)

@[fun_prop]
/--
theorem `Differentiable.rpow_const` / 定理 `Differentiable.rpow_const`

English:
theorem Differentiable.rpow_const
  given: (hf : Differentiable Real f) (h : forall x, f x != 0 ∨ 1 <= p)
  proof: fun x => (hf x).rpow_const (h x)

中文:
定理 可微.rpow_const
  条件: (hf : 可微 实数 f) (h : 对任意 x, f x != 0 ∨ 1 <= p)
  证明: fun x => (hf x).rpow_const (h x)

Depends on / 依赖: rpow_const
-/
theorem Differentiable.rpow_const (hf : Differentiable Real f) (h : forall x, f x != 0 ∨ 1 <= p) :
    Differentiable Real fun x => f x ^ p := fun x => (hf x).rpow_const (h x)

/--
theorem `HasFDerivWithinAt.const_rpow` / 定理 `HasFDerivWithinAt.const_rpow`

English:
theorem HasFDerivWithinAt.const_rpow
  given: (hf : HasFDerivWithinAt f f' s x) (hc : 0 < c)
  proof: (hasStrictDerivAt_const_rpow hc (f x)).hasDerivAt.comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.const_rpow
  条件: (hf : HasFDerivWithinAt f f' s x) (hc : 0 < c)
  证明: (hasStrictDerivAt_const_rpow hc (f x)).hasDerivAt.comp_hasFDerivWithinAt x hf

Depends on / 依赖: comp_hasFDerivWithinAt, hasDerivAt, hasDerivAt.comp_hasFDerivWithinAt, hasStrictDerivAt_const_rpow
-/
theorem HasFDerivWithinAt.const_rpow (hf : HasFDerivWithinAt f f' s x) (hc : 0 < c) :
    HasFDerivWithinAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') s x :=
  (hasStrictDerivAt_const_rpow hc (f x)).hasDerivAt.comp_hasFDerivWithinAt x hf

/--
theorem `HasFDerivAt.const_rpow` / 定理 `HasFDerivAt.const_rpow`

English:
theorem HasFDerivAt.const_rpow
  given: (hf : HasFDerivAt f f' x) (hc : 0 < c)
  proof: (hasStrictDerivAt_const_rpow hc (f x)).hasDerivAt.comp_hasFDerivAt x hf

中文:
定理 在点处Fréchet可导.const_rpow
  条件: (hf : 在点处Fréchet可导 f f' x) (hc : 0 < c)
  证明: (hasStrictDerivAt_const_rpow hc (f x)).hasDerivAt.comp_hasFDerivAt x hf

Depends on / 依赖: comp_hasFDerivAt, hasDerivAt, hasDerivAt.comp_hasFDerivAt, hasStrictDerivAt_const_rpow
-/
theorem HasFDerivAt.const_rpow (hf : HasFDerivAt f f' x) (hc : 0 < c) :
    HasFDerivAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') x :=
  (hasStrictDerivAt_const_rpow hc (f x)).hasDerivAt.comp_hasFDerivAt x hf

/--
theorem `HasStrictFDerivAt.const_rpow` / 定理 `HasStrictFDerivAt.const_rpow`

English:
theorem HasStrictFDerivAt.const_rpow
  given: (hf : HasStrictFDerivAt f f' x) (hc : 0 < c)
  proof: (hasStrictDerivAt_const_rpow hc (f x)).comp_hasStrictFDerivAt x hf

@[fun_prop]

中文:
定理 HasStrictFDerivAt.const_rpow
  条件: (hf : HasStrictFDerivAt f f' x) (hc : 0 < c)
  证明: (hasStrictDerivAt_const_rpow hc (f x)).comp_hasStrictFDerivAt x hf

@[fun_prop]

Depends on / 依赖: comp_hasStrictFDerivAt, hasStrictDerivAt_const_rpow
-/
theorem HasStrictFDerivAt.const_rpow (hf : HasStrictFDerivAt f f' x) (hc : 0 < c) :
    HasStrictFDerivAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') x :=
  (hasStrictDerivAt_const_rpow hc (f x)).comp_hasStrictFDerivAt x hf

@[fun_prop]
/--
theorem `ContDiffWithinAt.rpow` / 定理 `ContDiffWithinAt.rpow`

English:
theorem ContDiffWithinAt.rpow
  statement: (hf : ContDiffWithinAt Real n f s x) (hg : ContDiffWithinAt Real n g s x)
  proof: by
  -- `by exact` to deal with tricky unification.
  exact (contDiffAt_rpow_of_ne (f x, g x) h).comp_contDiffWithinAt x (hf.prodMk hg)

@[fun_prop]

中文:
定理 ContDiffWithinAt.rpow
  结论: (hf : ContDiffWithinAt 实数 n f s x) (hg : ContDiffWithinAt 实数 n g s x)
  证明: by
  -- `by exact` to deal with tricky unification.
  exact (contDiffAt_rpow_of_ne (f x, g x) h).comp_contDiffWithinAt x (hf.prodMk hg)

@[fun_prop]
-/
theorem ContDiffWithinAt.rpow (hf : ContDiffWithinAt Real n f s x) (hg : ContDiffWithinAt Real n g s x)
    (h : f x != 0) : ContDiffWithinAt Real n (fun x => f x ^ g x) s x := by
  -- `by exact` to deal with tricky unification.
  exact (contDiffAt_rpow_of_ne (f x, g x) h).comp_contDiffWithinAt x (hf.prodMk hg)

@[fun_prop]
/--
theorem `ContDiffAt.rpow` / 定理 `ContDiffAt.rpow`

English:
theorem ContDiffAt.rpow
  given: (hf : ContDiffAt Real n f x) (hg : ContDiffAt Real n g x) (h : f x != 0)
  proof: by
  -- `by exact` to deal with tricky unification.
  exact (contDiffAt_rpow_of_ne (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]

中文:
定理 ContDiffAt.rpow
  条件: (hf : ContDiffAt 实数 n f x) (hg : ContDiffAt 实数 n g x) (h : f x != 0)
  证明: by
  -- `by exact` to deal with tricky unification.
  exact (contDiffAt_rpow_of_ne (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]
-/
theorem ContDiffAt.rpow (hf : ContDiffAt Real n f x) (hg : ContDiffAt Real n g x) (h : f x != 0) :
    ContDiffAt Real n (fun x => f x ^ g x) x := by
  -- `by exact` to deal with tricky unification.
  exact (contDiffAt_rpow_of_ne (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]
/--
theorem `ContDiffOn.rpow` / 定理 `ContDiffOn.rpow`

English:
theorem ContDiffOn.rpow
  given: (hf : ContDiffOn Real n f s) (hg : ContDiffOn Real n g s) (h : forall x in s, f x != 0)
  proof: fun x hx => (hf x hx).rpow (hg x hx) (h x hx)

@[fun_prop]

中文:
定理 ContDiffOn.rpow
  条件: (hf : ContDiffOn 实数 n f s) (hg : ContDiffOn 实数 n g s) (h : 对任意 x in s, f x != 0)
  证明: fun x hx => (hf x hx).rpow (hg x hx) (h x hx)

@[fun_prop]
-/
theorem ContDiffOn.rpow (hf : ContDiffOn Real n f s) (hg : ContDiffOn Real n g s) (h : forall x in s, f x != 0) :
    ContDiffOn Real n (fun x => f x ^ g x) s := fun x hx => (hf x hx).rpow (hg x hx) (h x hx)

@[fun_prop]
/--
theorem `ContDiff.rpow` / 定理 `ContDiff.rpow`

English:
theorem ContDiff.rpow
  given: (hf : ContDiff Real n f) (hg : ContDiff Real n g) (h : forall x, f x != 0)
  proof: contDiff_iff_contDiffAt.mpr fun x => hf.contDiffAt.rpow hg.contDiffAt (h x)

@[fun_prop]

中文:
定理 连续可微.rpow
  条件: (hf : 连续可微 实数 n f) (hg : 连续可微 实数 n g) (h : 对任意 x, f x != 0)
  证明: contDiff_iff_contDiffAt.mpr fun x => hf.contDiffAt.rpow hg.contDiffAt (h x)

@[fun_prop]

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, contDiff_iff_contDiffAt.mpr, hf.contDiffAt.rpow, hg.contDiffAt
-/
theorem ContDiff.rpow (hf : ContDiff Real n f) (hg : ContDiff Real n g) (h : forall x, f x != 0) :
    ContDiff Real n fun x => f x ^ g x :=
  contDiff_iff_contDiffAt.mpr fun x => hf.contDiffAt.rpow hg.contDiffAt (h x)

@[fun_prop]
/--
theorem `ContDiffWithinAt.rpow_const_of_ne` / 定理 `ContDiffWithinAt.rpow_const_of_ne`

English:
theorem ContDiffWithinAt.rpow_const_of_ne
  given: (hf : ContDiffWithinAt Real n f s x) (h : f x != 0)
  proof: hf.rpow contDiffWithinAt_const h

@[fun_prop]

中文:
定理 ContDiffWithinAt.rpow_const_of_ne
  条件: (hf : ContDiffWithinAt 实数 n f s x) (h : f x != 0)
  证明: hf.rpow contDiffWithinAt_const h

@[fun_prop]

Depends on / 依赖: contDiffWithinAt_const, hf.rpow
-/
theorem ContDiffWithinAt.rpow_const_of_ne (hf : ContDiffWithinAt Real n f s x) (h : f x != 0) :
    ContDiffWithinAt Real n (fun x => f x ^ p) s x :=
  hf.rpow contDiffWithinAt_const h

@[fun_prop]
/--
theorem `ContDiffAt.rpow_const_of_ne` / 定理 `ContDiffAt.rpow_const_of_ne`

English:
theorem ContDiffAt.rpow_const_of_ne
  given: (hf : ContDiffAt Real n f x) (h : f x != 0)
  proof: hf.rpow contDiffAt_const h

@[fun_prop]

中文:
定理 ContDiffAt.rpow_const_of_ne
  条件: (hf : ContDiffAt 实数 n f x) (h : f x != 0)
  证明: hf.rpow contDiffAt_const h

@[fun_prop]

Depends on / 依赖: contDiffAt_const, hf.rpow
-/
theorem ContDiffAt.rpow_const_of_ne (hf : ContDiffAt Real n f x) (h : f x != 0) :
    ContDiffAt Real n (fun x => f x ^ p) x :=
  hf.rpow contDiffAt_const h

@[fun_prop]
/--
theorem `ContDiffOn.rpow_const_of_ne` / 定理 `ContDiffOn.rpow_const_of_ne`

English:
theorem ContDiffOn.rpow_const_of_ne
  given: (hf : ContDiffOn Real n f s) (h : forall x in s, f x != 0)
  proof: fun x hx => (hf x hx).rpow_const_of_ne (h x hx)

@[fun_prop]

中文:
定理 ContDiffOn.rpow_const_of_ne
  条件: (hf : ContDiffOn 实数 n f s) (h : 对任意 x in s, f x != 0)
  证明: fun x hx => (hf x hx).rpow_const_of_ne (h x hx)

@[fun_prop]

Depends on / 依赖: rpow_const_of_ne
-/
theorem ContDiffOn.rpow_const_of_ne (hf : ContDiffOn Real n f s) (h : forall x in s, f x != 0) :
    ContDiffOn Real n (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const_of_ne (h x hx)

@[fun_prop]
/--
theorem `ContDiff.rpow_const_of_ne` / 定理 `ContDiff.rpow_const_of_ne`

English:
theorem ContDiff.rpow_const_of_ne
  given: (hf : ContDiff Real n f) (h : forall x, f x != 0)
  proof: hf.rpow contDiff_const h

中文:
定理 连续可微.rpow_const_of_ne
  条件: (hf : 连续可微 实数 n f) (h : 对任意 x, f x != 0)
  证明: hf.rpow contDiff_const h

Depends on / 依赖: contDiff_const, hf.rpow
-/
theorem ContDiff.rpow_const_of_ne (hf : ContDiff Real n f) (h : forall x, f x != 0) :
    ContDiff Real n fun x => f x ^ p :=
  hf.rpow contDiff_const h

variable {m : Nat}

@[fun_prop]
/--
theorem `ContDiffWithinAt.rpow_const_of_le` / 定理 `ContDiffWithinAt.rpow_const_of_le`

English:
theorem ContDiffWithinAt.rpow_const_of_le
  given: (hf : ContDiffWithinAt Real m f s x) (h : ↑m <= p)
  proof: (contDiffAt_rpow_const_of_le h).comp_contDiffWithinAt x hf

@[fun_prop]

中文:
定理 ContDiffWithinAt.rpow_const_of_le
  条件: (hf : ContDiffWithinAt 实数 m f s x) (h : ↑m <= p)
  证明: (contDiffAt_rpow_const_of_le h).comp_contDiffWithinAt x hf

@[fun_prop]

Depends on / 依赖: comp_contDiffWithinAt, contDiffAt_rpow_const_of_le
-/
theorem ContDiffWithinAt.rpow_const_of_le (hf : ContDiffWithinAt Real m f s x) (h : ↑m <= p) :
    ContDiffWithinAt Real m (fun x => f x ^ p) s x :=
  (contDiffAt_rpow_const_of_le h).comp_contDiffWithinAt x hf

@[fun_prop]
/--
theorem `ContDiffAt.rpow_const_of_le` / 定理 `ContDiffAt.rpow_const_of_le`

English:
theorem ContDiffAt.rpow_const_of_le
  given: (hf : ContDiffAt Real m f x) (h : ↑m <= p)
  proof: by
  rw [← contDiffWithinAt_univ] at *; exact hf.rpow_const_of_le h

@[fun_prop]

中文:
定理 ContDiffAt.rpow_const_of_le
  条件: (hf : ContDiffAt 实数 m f x) (h : ↑m <= p)
  证明: by
  rw [← contDiffWithinAt_univ] at *; exact hf.rpow_const_of_le h

@[fun_prop]

Depends on / 依赖: contDiffWithinAt_univ, hf.rpow_const_of_le, rpow_const_of_le
-/
theorem ContDiffAt.rpow_const_of_le (hf : ContDiffAt Real m f x) (h : ↑m <= p) :
    ContDiffAt Real m (fun x => f x ^ p) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.rpow_const_of_le h

@[fun_prop]
/--
theorem `ContDiffOn.rpow_const_of_le` / 定理 `ContDiffOn.rpow_const_of_le`

English:
theorem ContDiffOn.rpow_const_of_le
  given: (hf : ContDiffOn Real m f s) (h : ↑m <= p)
  proof: fun x hx => (hf x hx).rpow_const_of_le h

@[fun_prop]

中文:
定理 ContDiffOn.rpow_const_of_le
  条件: (hf : ContDiffOn 实数 m f s) (h : ↑m <= p)
  证明: fun x hx => (hf x hx).rpow_const_of_le h

@[fun_prop]

Depends on / 依赖: rpow_const_of_le
-/
theorem ContDiffOn.rpow_const_of_le (hf : ContDiffOn Real m f s) (h : ↑m <= p) :
    ContDiffOn Real m (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const_of_le h

@[fun_prop]
/--
theorem `ContDiff.rpow_const_of_le` / 定理 `ContDiff.rpow_const_of_le`

English:
theorem ContDiff.rpow_const_of_le
  given: (hf : ContDiff Real m f) (h : ↑m <= p)
  proof: contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.rpow_const_of_le h

中文:
定理 连续可微.rpow_const_of_le
  条件: (hf : 连续可微 实数 m f) (h : ↑m <= p)
  证明: contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.rpow_const_of_le h

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, contDiff_iff_contDiffAt.mpr, hf.contDiffAt.rpow_const_of_le, rpow_const_of_le
-/
theorem ContDiff.rpow_const_of_le (hf : ContDiff Real m f) (h : ↑m <= p) :
    ContDiff Real m fun x => f x ^ p :=
  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.rpow_const_of_le h

end fderiv

section deriv

variable {f g : Real -> Real} {f' g' x y p : Real} {s : Set Real}

/--
theorem `HasDerivWithinAt.rpow` / 定理 `HasDerivWithinAt.rpow`

English:
theorem HasDerivWithinAt.rpow
  statement: (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
  proof: by
  convert! (hf.hasFDerivWithinAt.rpow hg.hasFDerivWithinAt h).hasDerivWithinAt using 1
  simp; ring

中文:
定理 HasDerivWithinAt.rpow
  结论: (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
  证明: by
  convert! (hf.hasFDerivWithinAt.rpow hg.hasFDerivWithinAt h).hasDerivWithinAt using 1
  simp; ring

Depends on / 依赖: convert, hasDerivWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.rpow, hg.hasFDerivWithinAt
-/
theorem HasDerivWithinAt.rpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
    (h : 0 < f x) : HasDerivWithinAt (fun x => f x ^ g x)
      (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * Real.log (f x)) s x := by
  convert! (hf.hasFDerivWithinAt.rpow hg.hasFDerivWithinAt h).hasDerivWithinAt using 1
  simp; ring

/--
theorem `HasDerivAt.rpow` / 定理 `HasDerivAt.rpow`

English:
theorem HasDerivAt.rpow
  given: (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (h : 0 < f x)
  proof: by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.rpow hg h

中文:
定理 在点处可导.rpow
  条件: (hf : 在点处可导 f f' x) (hg : 在点处可导 g g' x) (h : 0 < f x)
  证明: by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.rpow hg h

Depends on / 依赖: hasDerivWithinAt_univ, hf.rpow
-/
theorem HasDerivAt.rpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (h : 0 < f x) :
    HasDerivAt (fun x => f x ^ g x)
      (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * Real.log (f x)) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.rpow hg h

/--
theorem `HasDerivWithinAt.rpow_const` / 定理 `HasDerivWithinAt.rpow_const`

English:
theorem HasDerivWithinAt.rpow_const
  given: (hf : HasDerivWithinAt f f' s x) (hx : f x != 0 ∨ 1 <= p)
  proof: by
  convert! (hasDerivAt_rpow_const hx).comp_hasDerivWithinAt x hf using 1
  ring

中文:
定理 HasDerivWithinAt.rpow_const
  条件: (hf : HasDerivWithinAt f f' s x) (hx : f x != 0 ∨ 1 <= p)
  证明: by
  convert! (hasDerivAt_rpow_const hx).comp_hasDerivWithinAt x hf using 1
  ring

Depends on / 依赖: comp_hasDerivWithinAt, convert, hasDerivAt_rpow_const
-/
theorem HasDerivWithinAt.rpow_const (hf : HasDerivWithinAt f f' s x) (hx : f x != 0 ∨ 1 <= p) :
    HasDerivWithinAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) s x := by
  convert! (hasDerivAt_rpow_const hx).comp_hasDerivWithinAt x hf using 1
  ring

/--
theorem `HasDerivAt.rpow_const` / 定理 `HasDerivAt.rpow_const`

English:
theorem HasDerivAt.rpow_const
  given: (hf : HasDerivAt f f' x) (hx : f x != 0 ∨ 1 <= p)
  proof: by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.rpow_const hx

中文:
定理 在点处可导.rpow_const
  条件: (hf : 在点处可导 f f' x) (hx : f x != 0 ∨ 1 <= p)
  证明: by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.rpow_const hx

Depends on / 依赖: hasDerivWithinAt_univ, hf.rpow_const, rpow_const
-/
theorem HasDerivAt.rpow_const (hf : HasDerivAt f f' x) (hx : f x != 0 ∨ 1 <= p) :
    HasDerivAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.rpow_const hx

/--
theorem `derivWithin_rpow_const` / 定理 `derivWithin_rpow_const`

English:
theorem derivWithin_rpow_const
  statement: (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0 ∨ 1 <= p)
  proof: (hf.hasDerivWithinAt.rpow_const hx).derivWithin hxs

@[simp]

中文:
定理 derivWithin_rpow_const
  结论: (hf : DifferentiableWithinAt 实数 f s x) (hx : f x != 0 ∨ 1 <= p)
  证明: (hf.hasDerivWithinAt.rpow_const hx).derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.rpow_const, rpow_const
-/
theorem derivWithin_rpow_const (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0 ∨ 1 <= p)
    (hxs : UniqueDiffWithinAt Real s x) :
    derivWithin (fun x => f x ^ p) s x = derivWithin f s x * p * f x ^ (p - 1) :=
  (hf.hasDerivWithinAt.rpow_const hx).derivWithin hxs

@[simp]
/--
theorem `deriv_rpow_const` / 定理 `deriv_rpow_const`

English:
theorem deriv_rpow_const
  given: (hf : DifferentiableAt Real f x) (hx : f x != 0 ∨ 1 <= p)
  proof: (hf.hasDerivAt.rpow_const hx).deriv

中文:
定理 deriv_rpow_const
  条件: (hf : DifferentiableAt 实数 f x) (hx : f x != 0 ∨ 1 <= p)
  证明: (hf.hasDerivAt.rpow_const hx).deriv

Depends on / 依赖: hasDerivAt, hf.hasDerivAt.rpow_const, rpow_const
-/
theorem deriv_rpow_const (hf : DifferentiableAt Real f x) (hx : f x != 0 ∨ 1 <= p) :
    deriv (fun x => f x ^ p) x = deriv f x * p * f x ^ (p - 1) :=
  (hf.hasDerivAt.rpow_const hx).deriv

/--
theorem `deriv_norm_ofReal_cpow` / 定理 `deriv_norm_ofReal_cpow`

English:
theorem deriv_norm_ofReal_cpow
  given: (c : Complex) {t : Real} (ht : 0 < t)
  proof: by
  rw [EventuallyEq.deriv_eq (f := fun x => x ^ c.re)]
  · rw [Real.deriv_rpow_const t]
  · filter_upwards [eventually_gt_nhds ht] with x hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]

中文:
定理 deriv_norm_of实数_cpow
  条件: (c : 复形) {t : 实数} (ht : 0 < t)
  证明: by
  rw [EventuallyEq.deriv_eq (f := fun x => x ^ c.re)]
  · rw [Real.deriv_rpow_const t]
  · filter_upwards [eventually_gt_nhds ht] with x hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]

Depends on / 依赖: Complex.norm_cpow_eq_rpow_re_of_pos, EventuallyEq, EventuallyEq.deriv_eq, Real.deriv_rpow_const, c.re, deriv_eq, deriv_rpow_const, eventually_gt_nhds, filter_upwards, norm_cpow_eq_rpow_re_of_pos
-/
theorem deriv_norm_ofReal_cpow (c : Complex) {t : Real} (ht : 0 < t) :
    (deriv fun x : Real => ‖(x : Complex) ^ c‖) t = c.re * t ^ (c.re - 1) := by
  rw [EventuallyEq.deriv_eq (f := fun x => x ^ c.re)]
  · rw [Real.deriv_rpow_const t]
  · filter_upwards [eventually_gt_nhds ht] with x hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]

/--
lemma `isTheta_deriv_rpow_const_atTop` / 引理 `isTheta_deriv_rpow_const_atTop`

English:
lemma isTheta_deriv_rpow_const_atTop
  given: {p : Real} (hp : p != 0)
  proof: by
  calc deriv (fun (x : Real) => x ^ p) = fun x => p * x ^ (p - 1) := Real.deriv_rpow_const' p
    _ =Θ[atTop] fun x => x ^ (p - 1) :=
      Asymptotics.IsTheta.const_mul_left hp Asymptotics.isTheta_rfl

中文:
引理 isTheta_deriv_rpow_const_atTop
  条件: {p : 实数} (hp : p != 0)
  证明: by
  calc deriv (fun (x : Real) => x ^ p) = fun x => p * x ^ (p - 1) := Real.deriv_rpow_const' p
    _ =Θ[atTop] fun x => x ^ (p - 1) :=
      Asymptotics.IsTheta.const_mul_left hp Asymptotics.isTheta_rfl

Depends on / 依赖: Asymptotics, Asymptotics.IsTheta.const_mul_left, Asymptotics.isTheta_rfl, IsTheta, Real.deriv_rpow_const, const_mul_left, deriv_rpow_const, isTheta_rfl
-/
lemma isTheta_deriv_rpow_const_atTop {p : Real} (hp : p != 0) :
    deriv (fun (x : Real) => x ^ p) =Θ[atTop] fun x => x ^ (p - 1) := by
  calc deriv (fun (x : Real) => x ^ p) = fun x => p * x ^ (p - 1) := Real.deriv_rpow_const' p
    _ =Θ[atTop] fun x => x ^ (p - 1) :=
      Asymptotics.IsTheta.const_mul_left hp Asymptotics.isTheta_rfl

/--
lemma `isBigO_deriv_rpow_const_atTop` / 引理 `isBigO_deriv_rpow_const_atTop`

English:
lemma isBigO_deriv_rpow_const_atTop
  given: (p : Real)
  proof: by
  rcases eq_or_ne p 0 with rfl | hp
  case inl =>
    simp [zero_sub, Real.rpow_neg_one, Real.rpow_zero, deriv_const', Asymptotics.isBigO_zero]
  case inr =>
    exact (isTheta_deriv_rpow_const_atTop hp).1

中文:
引理 isBigO_deriv_rpow_const_atTop
  条件: (p : 实数)
  证明: by
  rcases eq_or_ne p 0 with rfl | hp
  case inl =>
    simp [zero_sub, Real.rpow_neg_one, Real.rpow_zero, deriv_const', Asymptotics.isBigO_zero]
  case inr =>
    exact (isTheta_deriv_rpow_const_atTop hp).1

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_zero, Real.rpow_neg_one, Real.rpow_zero, deriv_const, eq_or_ne, isBigO_zero, isTheta_deriv_rpow_const_atTop, rpow_neg_one, rpow_zero, zero_sub
-/
lemma isBigO_deriv_rpow_const_atTop (p : Real) :
    deriv (fun (x : Real) => x ^ p) =O[atTop] fun x => x ^ (p - 1) := by
  rcases eq_or_ne p 0 with rfl | hp
  case inl =>
    simp [zero_sub, Real.rpow_neg_one, Real.rpow_zero, deriv_const', Asymptotics.isBigO_zero]
  case inr =>
    exact (isTheta_deriv_rpow_const_atTop hp).1

variable {a : Real}

/--
theorem `HasDerivWithinAt.const_rpow` / 定理 `HasDerivWithinAt.const_rpow`

English:
theorem HasDerivWithinAt.const_rpow
  given: (ha : 0 < a) (hf : HasDerivWithinAt f f' s x)
  proof: by
  convert! (hasDerivWithinAt_const x s a).rpow hf ha using 1
  ring

中文:
定理 HasDerivWithinAt.const_rpow
  条件: (ha : 0 < a) (hf : HasDerivWithinAt f f' s x)
  证明: by
  convert! (hasDerivWithinAt_const x s a).rpow hf ha using 1
  ring

Depends on / 依赖: convert, hasDerivWithinAt_const
-/
theorem HasDerivWithinAt.const_rpow (ha : 0 < a) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (a ^ f ·) (Real.log a * f' * a ^ f x) s x := by
  convert! (hasDerivWithinAt_const x s a).rpow hf ha using 1
  ring

/--
theorem `HasDerivAt.const_rpow` / 定理 `HasDerivAt.const_rpow`

English:
theorem HasDerivAt.const_rpow
  given: (ha : 0 < a) (hf : HasDerivAt f f' x)
  proof: by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.const_rpow ha

中文:
定理 在点处可导.const_rpow
  条件: (ha : 0 < a) (hf : 在点处可导 f f' x)
  证明: by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.const_rpow ha

Depends on / 依赖: const_rpow, hasDerivWithinAt_univ, hf.const_rpow
-/
theorem HasDerivAt.const_rpow (ha : 0 < a) (hf : HasDerivAt f f' x) :
    HasDerivAt (a ^ f ·) (Real.log a * f' * a ^ f x) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.const_rpow ha

/--
theorem `derivWithin_const_rpow` / 定理 `derivWithin_const_rpow`

English:
theorem derivWithin_const_rpow
  given: (ha : 0 < a) (hf : DifferentiableWithinAt Real f s x)
  proof: by
  by_cases hxs : UniqueDiffWithinAt Real s x
  · exact (hf.hasDerivWithinAt.const_rpow ha).derivWithin hxs
  · rw [derivWithin_zero_of_not_uniqueDiffWithinAt hxs,
      derivWithin_zero_of_not_uniqueDiffWithinAt hxs,
      mul_zero, zero_mul]

@[simp]

中文:
定理 derivWithin_const_rpow
  条件: (ha : 0 < a) (hf : DifferentiableWithinAt 实数 f s x)
  证明: by
  by_cases hxs : UniqueDiffWithinAt Real s x
  · exact (hf.hasDerivWithinAt.const_rpow ha).derivWithin hxs
  · rw [derivWithin_zero_of_not_uniqueDiffWithinAt hxs,
      derivWithin_zero_of_not_uniqueDiffWithinAt hxs,
      mul_zero, zero_mul]

@[simp]

Depends on / 依赖: UniqueDiffWithinAt, const_rpow, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hf.hasDerivWithinAt.const_rpow, mul_zero, zero_mul
-/
theorem derivWithin_const_rpow (ha : 0 < a) (hf : DifferentiableWithinAt Real f s x) :
    derivWithin (a ^ f ·) s x = Real.log a * derivWithin f s x * a ^ f x := by
  by_cases hxs : UniqueDiffWithinAt Real s x
  · exact (hf.hasDerivWithinAt.const_rpow ha).derivWithin hxs
  · rw [derivWithin_zero_of_not_uniqueDiffWithinAt hxs,
      derivWithin_zero_of_not_uniqueDiffWithinAt hxs,
      mul_zero, zero_mul]

@[simp]
/--
theorem `deriv_const_rpow` / 定理 `deriv_const_rpow`

English:
theorem deriv_const_rpow
  given: (ha : 0 < a) (hf : DifferentiableAt Real f x)
  proof: (hf.hasDerivAt.const_rpow ha).deriv

@[simp]

中文:
定理 deriv_const_rpow
  条件: (ha : 0 < a) (hf : DifferentiableAt 实数 f x)
  证明: (hf.hasDerivAt.const_rpow ha).deriv

@[simp]

Depends on / 依赖: const_rpow, hasDerivAt, hf.hasDerivAt.const_rpow
-/
theorem deriv_const_rpow (ha : 0 < a) (hf : DifferentiableAt Real f x) :
    deriv (a ^ f ·) x = Real.log a * deriv f x * a ^ f x :=
  (hf.hasDerivAt.const_rpow ha).deriv

@[simp]
/--
theorem `deriv_const_rpow_id` / 定理 `deriv_const_rpow_id`

English:
theorem deriv_const_rpow_id
  given: (ha : 0 < a)
  proof: by
  rw [deriv_const_rpow ha differentiableAt_fun_id]; rw [deriv_id'']; rw [mul_one]

中文:
定理 deriv_const_rpow_id
  条件: (ha : 0 < a)
  证明: by
  rw [deriv_const_rpow ha differentiableAt_fun_id]; rw [deriv_id'']; rw [mul_one]

Depends on / 依赖: deriv_const_rpow, deriv_id, differentiableAt_fun_id, mul_one
-/
theorem deriv_const_rpow_id (ha : 0 < a) :
    deriv (a ^ ·) x = Real.log a * a ^ x := by
  rw [deriv_const_rpow ha differentiableAt_fun_id]; rw [deriv_id'']; rw [mul_one]

end deriv

end Differentiability
