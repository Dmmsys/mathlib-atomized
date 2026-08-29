/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Smoothness of `Real.sqrt`

In this file we prove that `Real.sqrt` is infinitely smooth at all points `x ≠ 0` and provide some
dot-notation lemmas.

## Tags

sqrt, differentiable
-/

@[expose] public section


open Set

open scoped Topology

namespace Real

/--
Definition of `sqPartialHomeomorph` / `sqPartialHomeomorph` 的定义

English:
definition sqPartialHomeomorph
  signature: : OpenPartialHomeomorph Real Real where
  body: x ^ 2
  invFun := (√·)
  source := Ioi 0
  target := Ioi 0
  map_source' _ h := mem_Ioi.2 (pow_pos (mem_Ioi.1 h) _)
  map_target' _ h := mem_Ioi.2 (sqrt_pos.2 h)
  left_inv' _ h := sqrt_sq (le_of_lt h)
  right_inv' _ h := sq_sqrt (le_of_lt h)
  open_source := isOpen_Ioi
  open_target := isOpen_Ioi
 

中文:
定义 sqPartialHomeomorph
  签名: : OpenPartialHomeomorph 实数 实数 where
  定义体: x ^ 2
  invFun := (√·)
  source := Ioi 0
  target := Ioi 0
  map_source' _ h := mem_Ioi.2 (pow_pos (mem_Ioi.1 h) _)
  map_target' _ h := mem_Ioi.2 (sqrt_pos.2 h)
  left_inv' _ h := sqrt_sq (le_of_lt h)
  right_inv' _ h := sq_sqrt (le_of_lt h)
  open_source := isOpen_Ioi
  open_target := isOpen_Ioi
 
-/
noncomputable def sqPartialHomeomorph : OpenPartialHomeomorph Real Real where
  toFun x := x ^ 2
  invFun := (√·)
  source := Ioi 0
  target := Ioi 0
  map_source' _ h := mem_Ioi.2 (pow_pos (mem_Ioi.1 h) _)
  map_target' _ h := mem_Ioi.2 (sqrt_pos.2 h)
  left_inv' _ h := sqrt_sq (le_of_lt h)
  right_inv' _ h := sq_sqrt (le_of_lt h)
  open_source := isOpen_Ioi
  open_target := isOpen_Ioi
  continuousOn_toFun := (continuous_pow 2).continuousOn
  continuousOn_invFun := continuousOn_id.sqrt

/--
theorem `deriv_sqrt_aux` / 定理 `deriv_sqrt_aux`

English:
theorem deriv_sqrt_aux
  given: {x : Real} (hx : x != 0)
  proof: by
  rcases hx.lt_or_gt with hx | hx
  · rw [sqrt_eq_zero_of_nonpos hx.le, mul_zero, div_zero]
    have : (√·) =ᶠ[𝓝 x] fun _ => 0 := (gt_mem_nhds hx).mono fun x hx => sqrt_eq_zero_of_nonpos hx.le
    exact
      ⟨(hasStrictDerivAt_const x (0 : Real)).congr_of_eventuallyEq this.symm, fun n =>
       

中文:
定理 deriv_sqrt_aux
  条件: {x : 实数} (hx : x != 0)
  证明: by
  rcases hx.lt_or_gt with hx | hx
  · rw [sqrt_eq_zero_of_nonpos hx.le, mul_zero, div_zero]
    have : (√·) =ᶠ[𝓝 x] fun _ => 0 := (gt_mem_nhds hx).mono fun x hx => sqrt_eq_zero_of_nonpos hx.le
    exact
      ⟨(hasStrictDerivAt_const x (0 : Real)).congr_of_eventuallyEq this.symm, fun n =>
       

Depends on / 依赖: congr_of_eventuallyEq, contDiffAt_const, contDiffAt_const.congr_of_eventuallyEq, div_zero, gt_mem_nhds, hasStrictDerivAt_const, hasStrictDerivAt_p, hasStrictDerivAt_symm, hx.le, hx.lt_or_gt, lt_or_gt, mul_zero, sqPartialHomeomorph, sqPartialHomeomorph.hasStrictDerivAt_symm, sqrt_eq_zero_of_nonpos, sqrt_pos, this.symm, two_ne_zero
-/
theorem deriv_sqrt_aux {x : Real} (hx : x != 0) :
    HasStrictDerivAt (√·) (1 / (2 * √x)) x ∧ forall n, ContDiffAt Real n (√·) x := by
  rcases hx.lt_or_gt with hx | hx
  · rw [sqrt_eq_zero_of_nonpos hx.le, mul_zero, div_zero]
    have : (√·) =ᶠ[𝓝 x] fun _ => 0 := (gt_mem_nhds hx).mono fun x hx => sqrt_eq_zero_of_nonpos hx.le
    exact
      ⟨(hasStrictDerivAt_const x (0 : Real)).congr_of_eventuallyEq this.symm, fun n =>
        contDiffAt_const.congr_of_eventuallyEq this⟩
  · have : ↑2 * √x ^ (2 - 1) != 0 := by simp [(sqrt_pos.2 hx).ne', @two_ne_zero Real]
    constructor
    · simpa using! sqPartialHomeomorph.hasStrictDerivAt_symm hx this (hasStrictDerivAt_pow 2 _)
    · exact fun n => sqPartialHomeomorph.contDiffAt_symm_deriv this hx (hasDerivAt_pow 2 (√x))
        (contDiffAt_id.pow 2)

/--
theorem `hasStrictDerivAt_sqrt` / 定理 `hasStrictDerivAt_sqrt`

English:
theorem hasStrictDerivAt_sqrt
  given: {x : Real} (hx : x != 0)
  statement: HasStrictDerivAt (√·) (1 / (2 * √x)) x
  proof: (deriv_sqrt_aux hx).1

@[fun_prop]

中文:
定理 hasStrictDerivAt_sqrt
  条件: {x : 实数} (hx : x != 0)
  结论: HasStrictDerivAt (√·) (1 / (2 * √x)) x
  证明: (deriv_sqrt_aux hx).1

@[fun_prop]

Depends on / 依赖: deriv_sqrt_aux
-/
theorem hasStrictDerivAt_sqrt {x : Real} (hx : x != 0) : HasStrictDerivAt (√·) (1 / (2 * √x)) x :=
  (deriv_sqrt_aux hx).1

@[fun_prop]
/--
theorem `contDiffAt_sqrt` / 定理 `contDiffAt_sqrt`

English:
theorem contDiffAt_sqrt
  given: {x : Real} {n : WithTop Nat∞} (hx : x != 0)
  statement: ContDiffAt Real n (√·) x
  proof: (deriv_sqrt_aux hx).2 n

中文:
定理 contDiffAt_sqrt
  条件: {x : 实数} {n : WithTop 自然数∞} (hx : x != 0)
  结论: ContDiffAt 实数 n (√·) x
  证明: (deriv_sqrt_aux hx).2 n

Depends on / 依赖: deriv_sqrt_aux, homDiagram
-/
theorem contDiffAt_sqrt {x : Real} {n : WithTop Nat∞} (hx : x != 0) : ContDiffAt Real n (√·) x :=
  (deriv_sqrt_aux hx).2 n

/--
theorem `hasDerivAt_sqrt` / 定理 `hasDerivAt_sqrt`

English:
theorem hasDerivAt_sqrt
  given: {x : Real} (hx : x != 0)
  statement: HasDerivAt (√·) (1 / (2 * √x)) x
  proof: (hasStrictDerivAt_sqrt hx).hasDerivAt

中文:
定理 hasDerivAt_sqrt
  条件: {x : 实数} (hx : x != 0)
  结论: HasDerivAt (√·) (1 / (2 * √x)) x
  证明: (hasStrictDerivAt_sqrt hx).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_sqrt
-/
theorem hasDerivAt_sqrt {x : Real} (hx : x != 0) : HasDerivAt (√·) (1 / (2 * √x)) x :=
  (hasStrictDerivAt_sqrt hx).hasDerivAt

end Real

open Real

section deriv

variable {f : Real -> Real} {s : Set Real} {f' x : Real}

/--
theorem `HasDerivWithinAt.sqrt` / 定理 `HasDerivWithinAt.sqrt`

English:
theorem HasDerivWithinAt.sqrt
  given: (hf : HasDerivWithinAt f f' s x) (hx : f x != 0)
  proof: by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using!
    (hasDerivAt_sqrt hx).comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.sqrt
  条件: (hf : HasDerivWithinAt f f' s x) (hx : f x != 0)
  证明: by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using!
    (hasDerivAt_sqrt hx).comp_hasDerivWithinAt x hf

Depends on / 依赖: comp_hasDerivWithinAt, div_eq_inv_mul, hasDerivAt_sqrt, mul_one
-/
theorem HasDerivWithinAt.sqrt (hf : HasDerivWithinAt f f' s x) (hx : f x != 0) :
    HasDerivWithinAt (fun y => √(f y)) (f' / (2 * √(f x))) s x := by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using!
    (hasDerivAt_sqrt hx).comp_hasDerivWithinAt x hf

/--
theorem `HasDerivAt.sqrt` / 定理 `HasDerivAt.sqrt`

English:
theorem HasDerivAt.sqrt
  given: (hf : HasDerivAt f f' x) (hx : f x != 0)
  proof: by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using! (hasDerivAt_sqrt hx).comp x hf

中文:
定理 HasDerivAt.sqrt
  条件: (hf : HasDerivAt f f' x) (hx : f x != 0)
  证明: by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using! (hasDerivAt_sqrt hx).comp x hf

Depends on / 依赖: div_eq_inv_mul, hasDerivAt_sqrt, mul_one
-/
theorem HasDerivAt.sqrt (hf : HasDerivAt f f' x) (hx : f x != 0) :
    HasDerivAt (fun y => √(f y)) (f' / (2 * √(f x))) x := by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using! (hasDerivAt_sqrt hx).comp x hf

/--
theorem `HasStrictDerivAt.sqrt` / 定理 `HasStrictDerivAt.sqrt`

English:
theorem HasStrictDerivAt.sqrt
  given: (hf : HasStrictDerivAt f f' x) (hx : f x != 0)
  proof: by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using! (hasStrictDerivAt_sqrt hx).comp x hf

中文:
定理 HasStrictDerivAt.sqrt
  条件: (hf : HasStrictDerivAt f f' x) (hx : f x != 0)
  证明: by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using! (hasStrictDerivAt_sqrt hx).comp x hf

Depends on / 依赖: div_eq_inv_mul, hasStrictDerivAt_sqrt, mul_one
-/
theorem HasStrictDerivAt.sqrt (hf : HasStrictDerivAt f f' x) (hx : f x != 0) :
    HasStrictDerivAt (fun t => √(f t)) (f' / (2 * √(f x))) x := by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using! (hasStrictDerivAt_sqrt hx).comp x hf

/--
theorem `derivWithin_sqrt` / 定理 `derivWithin_sqrt`

English:
theorem derivWithin_sqrt
  statement: (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0)
  proof: (hf.hasDerivWithinAt.sqrt hx).derivWithin hxs

@[simp]

中文:
定理 derivWithin_sqrt
  结论: (hf : DifferentiableWithinAt 实数 f s x) (hx : f x != 0)
  证明: (hf.hasDerivWithinAt.sqrt hx).derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.sqrt
-/
theorem derivWithin_sqrt (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0)
    (hxs : UniqueDiffWithinAt Real s x) :
    derivWithin (fun x => √(f x)) s x = derivWithin f s x / (2 * √(f x)) :=
  (hf.hasDerivWithinAt.sqrt hx).derivWithin hxs

@[simp]
/--
theorem `deriv_sqrt` / 定理 `deriv_sqrt`

English:
theorem deriv_sqrt
  given: (hf : DifferentiableAt Real f x) (hx : f x != 0)
  proof: (hf.hasDerivAt.sqrt hx).deriv

中文:
定理 deriv_sqrt
  条件: (hf : DifferentiableAt 实数 f x) (hx : f x != 0)
  证明: (hf.hasDerivAt.sqrt hx).deriv

Depends on / 依赖: hasDerivAt, hf.hasDerivAt.sqrt
-/
theorem deriv_sqrt (hf : DifferentiableAt Real f x) (hx : f x != 0) :
    deriv (fun x => √(f x)) x = deriv f x / (2 * √(f x)) :=
  (hf.hasDerivAt.sqrt hx).deriv

end deriv

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : E -> Real} {n : WithTop Nat∞}
  {s : Set E} {x : E} {f' : StrongDual Real E}

/--
theorem `HasFDerivAt.sqrt` / 定理 `HasFDerivAt.sqrt`

English:
theorem HasFDerivAt.sqrt
  given: (hf : HasFDerivAt f f' x) (hx : f x != 0)
  proof: (hasDerivAt_sqrt hx).comp_hasFDerivAt x hf

中文:
定理 HasFDerivAt.sqrt
  条件: (hf : HasFDerivAt f f' x) (hx : f x != 0)
  证明: (hasDerivAt_sqrt hx).comp_hasFDerivAt x hf

Depends on / 依赖: comp_hasFDerivAt, hasDerivAt_sqrt
-/
theorem HasFDerivAt.sqrt (hf : HasFDerivAt f f' x) (hx : f x != 0) :
    HasFDerivAt (fun y => √(f y)) ((1 / (2 * √(f x))) • f') x :=
  (hasDerivAt_sqrt hx).comp_hasFDerivAt x hf

/--
theorem `HasStrictFDerivAt.sqrt` / 定理 `HasStrictFDerivAt.sqrt`

English:
theorem HasStrictFDerivAt.sqrt
  given: (hf : HasStrictFDerivAt f f' x) (hx : f x != 0)
  proof: (hasStrictDerivAt_sqrt hx).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.sqrt
  条件: (hf : HasStrictFDerivAt f f' x) (hx : f x != 0)
  证明: (hasStrictDerivAt_sqrt hx).comp_hasStrictFDerivAt x hf

Depends on / 依赖: comp_hasStrictFDerivAt, hasStrictDerivAt_sqrt
-/
theorem HasStrictFDerivAt.sqrt (hf : HasStrictFDerivAt f f' x) (hx : f x != 0) :
    HasStrictFDerivAt (fun y => √(f y)) ((1 / (2 * √(f x))) • f') x :=
  (hasStrictDerivAt_sqrt hx).comp_hasStrictFDerivAt x hf

/--
theorem `HasFDerivWithinAt.sqrt` / 定理 `HasFDerivWithinAt.sqrt`

English:
theorem HasFDerivWithinAt.sqrt
  given: (hf : HasFDerivWithinAt f f' s x) (hx : f x != 0)
  proof: (hasDerivAt_sqrt hx).comp_hasFDerivWithinAt x hf

@[fun_prop]

中文:
定理 HasFDerivWithinAt.sqrt
  条件: (hf : HasFDerivWithinAt f f' s x) (hx : f x != 0)
  证明: (hasDerivAt_sqrt hx).comp_hasFDerivWithinAt x hf

@[fun_prop]

Depends on / 依赖: comp_hasFDerivWithinAt, hasDerivAt_sqrt
-/
theorem HasFDerivWithinAt.sqrt (hf : HasFDerivWithinAt f f' s x) (hx : f x != 0) :
    HasFDerivWithinAt (fun y => √(f y)) ((1 / (2 * √(f x))) • f') s x :=
  (hasDerivAt_sqrt hx).comp_hasFDerivWithinAt x hf

@[fun_prop]
/--
theorem `DifferentiableWithinAt.sqrt` / 定理 `DifferentiableWithinAt.sqrt`

English:
theorem DifferentiableWithinAt.sqrt
  given: (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0)
  proof: (hf.hasFDerivWithinAt.sqrt hx).differentiableWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.sqrt
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hx : f x != 0)
  证明: (hf.hasFDerivWithinAt.sqrt hx).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.sqrt
-/
theorem DifferentiableWithinAt.sqrt (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0) :
    DifferentiableWithinAt Real (fun y => √(f y)) s x :=
  (hf.hasFDerivWithinAt.sqrt hx).differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableAt.sqrt` / 定理 `DifferentiableAt.sqrt`

English:
theorem DifferentiableAt.sqrt
  given: (hf : DifferentiableAt Real f x) (hx : f x != 0)
  proof: (hf.hasFDerivAt.sqrt hx).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.sqrt
  条件: (hf : DifferentiableAt 实数 f x) (hx : f x != 0)
  证明: (hf.hasFDerivAt.sqrt hx).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt, hf.hasFDerivAt.sqrt
-/
theorem DifferentiableAt.sqrt (hf : DifferentiableAt Real f x) (hx : f x != 0) :
    DifferentiableAt Real (fun y => √(f y)) x :=
  (hf.hasFDerivAt.sqrt hx).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableOn.sqrt` / 定理 `DifferentiableOn.sqrt`

English:
theorem DifferentiableOn.sqrt
  given: (hf : DifferentiableOn Real f s) (hs : forall x in s, f x != 0)
  proof: fun x hx => (hf x hx).sqrt (hs x hx)

@[fun_prop]

中文:
定理 DifferentiableOn.sqrt
  条件: (hf : DifferentiableOn 实数 f s) (hs : 对任意 x in s, f x != 0)
  证明: fun x hx => (hf x hx).sqrt (hs x hx)

@[fun_prop]
-/
theorem DifferentiableOn.sqrt (hf : DifferentiableOn Real f s) (hs : forall x in s, f x != 0) :
    DifferentiableOn Real (fun y => √(f y)) s := fun x hx => (hf x hx).sqrt (hs x hx)

@[fun_prop]
/--
theorem `Differentiable.sqrt` / 定理 `Differentiable.sqrt`

English:
theorem Differentiable.sqrt
  given: (hf : Differentiable Real f) (hs : forall x, f x != 0)
  proof: fun x => (hf x).sqrt (hs x)

中文:
定理 Differentiable.sqrt
  条件: (hf : Differentiable 实数 f) (hs : 对任意 x, f x != 0)
  证明: fun x => (hf x).sqrt (hs x)
-/
theorem Differentiable.sqrt (hf : Differentiable Real f) (hs : forall x, f x != 0) :
    Differentiable Real fun y => √(f y) := fun x => (hf x).sqrt (hs x)

/--
theorem `fderivWithin_sqrt` / 定理 `fderivWithin_sqrt`

English:
theorem fderivWithin_sqrt
  statement: (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0)
  proof: (hf.hasFDerivWithinAt.sqrt hx).fderivWithin hxs

@[simp]

中文:
定理 fderivWithin_sqrt
  结论: (hf : DifferentiableWithinAt 实数 f s x) (hx : f x != 0)
  证明: (hf.hasFDerivWithinAt.sqrt hx).fderivWithin hxs

@[simp]

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.sqrt
-/
theorem fderivWithin_sqrt (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0)
    (hxs : UniqueDiffWithinAt Real s x) :
    fderivWithin Real (fun x => √(f x)) s x = (1 / (2 * √(f x))) • fderivWithin Real f s x :=
  (hf.hasFDerivWithinAt.sqrt hx).fderivWithin hxs

@[simp]
/--
theorem `fderiv_sqrt` / 定理 `fderiv_sqrt`

English:
theorem fderiv_sqrt
  given: (hf : DifferentiableAt Real f x) (hx : f x != 0)
  proof: (hf.hasFDerivAt.sqrt hx).fderiv

@[fun_prop]

中文:
定理 fderiv_sqrt
  条件: (hf : DifferentiableAt 实数 f x) (hx : f x != 0)
  证明: (hf.hasFDerivAt.sqrt hx).fderiv

@[fun_prop]

Depends on / 依赖: fderiv, hasFDerivAt, hf.hasFDerivAt.sqrt
-/
theorem fderiv_sqrt (hf : DifferentiableAt Real f x) (hx : f x != 0) :
    fderiv Real (fun x => √(f x)) x = (1 / (2 * √(f x))) • fderiv Real f x :=
  (hf.hasFDerivAt.sqrt hx).fderiv

@[fun_prop]
/--
theorem `ContDiffAt.sqrt` / 定理 `ContDiffAt.sqrt`

English:
theorem ContDiffAt.sqrt
  given: (hf : ContDiffAt Real n f x) (hx : f x != 0)
  proof: (contDiffAt_sqrt hx).comp x hf

@[fun_prop]

中文:
定理 ContDiffAt.sqrt
  条件: (hf : ContDiffAt 实数 n f x) (hx : f x != 0)
  证明: (contDiffAt_sqrt hx).comp x hf

@[fun_prop]

Depends on / 依赖: contDiffAt_sqrt
-/
theorem ContDiffAt.sqrt (hf : ContDiffAt Real n f x) (hx : f x != 0) :
    ContDiffAt Real n (fun y => √(f y)) x :=
  (contDiffAt_sqrt hx).comp x hf

@[fun_prop]
/--
theorem `ContDiffWithinAt.sqrt` / 定理 `ContDiffWithinAt.sqrt`

English:
theorem ContDiffWithinAt.sqrt
  given: (hf : ContDiffWithinAt Real n f s x) (hx : f x != 0)
  proof: (contDiffAt_sqrt hx).comp_contDiffWithinAt x hf

@[fun_prop]

中文:
定理 ContDiffWithinAt.sqrt
  条件: (hf : ContDiffWithinAt 实数 n f s x) (hx : f x != 0)
  证明: (contDiffAt_sqrt hx).comp_contDiffWithinAt x hf

@[fun_prop]

Depends on / 依赖: comp_contDiffWithinAt, contDiffAt_sqrt
-/
theorem ContDiffWithinAt.sqrt (hf : ContDiffWithinAt Real n f s x) (hx : f x != 0) :
    ContDiffWithinAt Real n (fun y => √(f y)) s x :=
  (contDiffAt_sqrt hx).comp_contDiffWithinAt x hf

@[fun_prop]
/--
theorem `ContDiffOn.sqrt` / 定理 `ContDiffOn.sqrt`

English:
theorem ContDiffOn.sqrt
  given: (hf : ContDiffOn Real n f s) (hs : forall x in s, f x != 0)
  proof: fun x hx => (hf x hx).sqrt (hs x hx)

@[fun_prop]

中文:
定理 ContDiffOn.sqrt
  条件: (hf : ContDiffOn 实数 n f s) (hs : 对任意 x in s, f x != 0)
  证明: fun x hx => (hf x hx).sqrt (hs x hx)

@[fun_prop]
-/
theorem ContDiffOn.sqrt (hf : ContDiffOn Real n f s) (hs : forall x in s, f x != 0) :
    ContDiffOn Real n (fun y => √(f y)) s := fun x hx => (hf x hx).sqrt (hs x hx)

@[fun_prop]
/--
theorem `ContDiff.sqrt` / 定理 `ContDiff.sqrt`

English:
theorem ContDiff.sqrt
  given: (hf : ContDiff Real n f) (h : forall x, f x != 0)
  statement: ContDiff Real n fun y => √(f y)
  proof: contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.sqrt (h x)

中文:
定理 ContDiff.sqrt
  条件: (hf : ContDiff 实数 n f) (h : 对任意 x, f x != 0)
  结论: ContDiff 实数 n fun y => √(f y)
  证明: contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.sqrt (h x)

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, hf.contDiffAt.sqrt
-/
theorem ContDiff.sqrt (hf : ContDiff Real n f) (h : forall x, f x != 0) : ContDiff Real n fun y => √(f y) :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.sqrt (h x)

end fderiv
