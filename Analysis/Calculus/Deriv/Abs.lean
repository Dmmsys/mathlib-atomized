/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivative of the absolute value

This file compiles basic derivability properties of the absolute value, and is largely inspired from
`Mathlib/Analysis/InnerProductSpace/Calculus.lean`, which is the analogous file for norms derived
from an inner product space.

## Tags

absolute value, derivative
-/

public section

open Filter Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {n : Nat∞} {f : E -> Real} {f' : StrongDual Real E} {s : Set E} {x : E}

/--
theorem `contDiffAt_abs` / 定理 `contDiffAt_abs`

English:
theorem contDiffAt_abs
  given: {x : Real} (hx : x != 0)
  statement: ContDiffAt Real n (|·|) x
  proof: contDiffAt_norm Real hx

中文:
定理 contDiffAt_abs
  条件: {x : 实数} (hx : x != 0)
  结论: ContDiffAt 实数 n (|·|) x
  证明: contDiffAt_norm Real hx

Depends on / 依赖: contDiffAt_norm
-/
theorem contDiffAt_abs {x : Real} (hx : x != 0) : ContDiffAt Real n (|·|) x := contDiffAt_norm Real hx

/--
theorem `ContDiffAt.abs` / 定理 `ContDiffAt.abs`

English:
theorem ContDiffAt.abs
  given: (hf : ContDiffAt Real n f x) (h₀ : f x != 0)
  proof: hf.norm Real h₀

中文:
定理 ContDiffAt.abs
  条件: (hf : ContDiffAt 实数 n f x) (h₀ : f x != 0)
  证明: hf.norm Real h₀

Depends on / 依赖: hf.norm
-/
theorem ContDiffAt.abs (hf : ContDiffAt Real n f x) (h₀ : f x != 0) :
    ContDiffAt Real n (fun x => |f x|) x := hf.norm Real h₀

/--
theorem `contDiffWithinAt_abs` / 定理 `contDiffWithinAt_abs`

English:
theorem contDiffWithinAt_abs
  given: {x : Real} (hx : x != 0) (s : Set Real)
  proof: (contDiffAt_abs hx).contDiffWithinAt

中文:
定理 contDiffWithinAt_abs
  条件: {x : 实数} (hx : x != 0) (s : Set 实数)
  证明: (contDiffAt_abs hx).contDiffWithinAt

Depends on / 依赖: contDiffAt_abs, contDiffWithinAt
-/
theorem contDiffWithinAt_abs {x : Real} (hx : x != 0) (s : Set Real) :
    ContDiffWithinAt Real n (|·|) s x := (contDiffAt_abs hx).contDiffWithinAt

/--
theorem `ContDiffWithinAt.abs` / 定理 `ContDiffWithinAt.abs`

English:
theorem ContDiffWithinAt.abs
  given: (hf : ContDiffWithinAt Real n f s x) (h₀ : f x != 0)
  proof: (contDiffAt_abs h₀).comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.abs
  条件: (hf : ContDiffWithinAt 实数 n f s x) (h₀ : f x != 0)
  证明: (contDiffAt_abs h₀).comp_contDiffWithinAt x hf

Depends on / 依赖: comp_contDiffWithinAt, contDiffAt_abs
-/
theorem ContDiffWithinAt.abs (hf : ContDiffWithinAt Real n f s x) (h₀ : f x != 0) :
    ContDiffWithinAt Real n (fun y => |f y|) s x :=
  (contDiffAt_abs h₀).comp_contDiffWithinAt x hf

/--
theorem `contDiffOn_abs` / 定理 `contDiffOn_abs`

English:
theorem contDiffOn_abs
  given: {s : Set Real} (hs : forall x in s, x != 0)
  proof: fun x hx => contDiffWithinAt_abs (hs x hx) s

中文:
定理 contDiffOn_abs
  条件: {s : Set 实数} (hs : 对任意 x in s, x != 0)
  证明: fun x hx => contDiffWithinAt_abs (hs x hx) s

Depends on / 依赖: contDiffWithinAt_abs
-/
theorem contDiffOn_abs {s : Set Real} (hs : forall x in s, x != 0) :
    ContDiffOn Real n (|·|) s := fun x hx => contDiffWithinAt_abs (hs x hx) s

/--
theorem `ContDiffOn.abs` / 定理 `ContDiffOn.abs`

English:
theorem ContDiffOn.abs
  given: (hf : ContDiffOn Real n f s) (h₀ : forall x in s, f x != 0)
  proof: fun x hx => (hf x hx).abs (h₀ x hx)

中文:
定理 ContDiffOn.abs
  条件: (hf : ContDiffOn 实数 n f s) (h₀ : 对任意 x in s, f x != 0)
  证明: fun x hx => (hf x hx).abs (h₀ x hx)
-/
theorem ContDiffOn.abs (hf : ContDiffOn Real n f s) (h₀ : forall x in s, f x != 0) :
    ContDiffOn Real n (fun y => |f y|) s := fun x hx => (hf x hx).abs (h₀ x hx)

/--
theorem `ContDiff.abs` / 定理 `ContDiff.abs`

English:
theorem ContDiff.abs
  given: (hf : ContDiff Real n f) (h₀ : forall x, f x != 0)
  statement: ContDiff Real n fun y => |f y|
  proof: contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.abs (h₀ x)

中文:
定理 ContDiff.abs
  条件: (hf : ContDiff 实数 n f) (h₀ : 对任意 x, f x != 0)
  结论: ContDiff 实数 n fun y => |f y|
  证明: contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.abs (h₀ x)

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, hf.contDiffAt.abs
-/
theorem ContDiff.abs (hf : ContDiff Real n f) (h₀ : forall x, f x != 0) : ContDiff Real n fun y => |f y| :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.abs (h₀ x)

/--
theorem `hasStrictDerivAt_abs_neg` / 定理 `hasStrictDerivAt_abs_neg`

English:
theorem hasStrictDerivAt_abs_neg
  given: {x : Real} (hx : x < 0)
  proof: (hasStrictDerivAt_neg x).congr_of_eventuallyEq
    EqOn.eventuallyEq_of_mem (fun _ hy => (abs_of_neg (mem_Iio.1 hy)).symm) (Iio_mem_nhds hx)

中文:
定理 hasStrictDerivAt_abs_neg
  条件: {x : 实数} (hx : x < 0)
  证明: (hasStrictDerivAt_neg x).congr_of_eventuallyEq
    EqOn.eventuallyEq_of_mem (fun _ hy => (abs_of_neg (mem_Iio.1 hy)).symm) (Iio_mem_nhds hx)

Depends on / 依赖: EqOn.eventuallyEq_of_mem, Iio_mem_nhds, abs_of_neg, congr_of_eventuallyEq, eventuallyEq_of_mem, hasStrictDerivAt_neg, mem_Iio
-/
theorem hasStrictDerivAt_abs_neg {x : Real} (hx : x < 0) :
    HasStrictDerivAt (|·|) (-1) x :=
(hasStrictDerivAt_neg x).congr_of_eventuallyEq
    EqOn.eventuallyEq_of_mem (fun _ hy => (abs_of_neg (mem_Iio.1 hy)).symm) (Iio_mem_nhds hx)

/--
theorem `hasDerivAt_abs_neg` / 定理 `hasDerivAt_abs_neg`

English:
theorem hasDerivAt_abs_neg
  given: {x : Real} (hx : x < 0)
  proof: (hasStrictDerivAt_abs_neg hx).hasDerivAt

中文:
定理 hasDerivAt_abs_neg
  条件: {x : 实数} (hx : x < 0)
  证明: (hasStrictDerivAt_abs_neg hx).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_abs_neg
-/
theorem hasDerivAt_abs_neg {x : Real} (hx : x < 0) :
    HasDerivAt (|·|) (-1) x := (hasStrictDerivAt_abs_neg hx).hasDerivAt

/--
theorem `hasStrictDerivAt_abs_pos` / 定理 `hasStrictDerivAt_abs_pos`

English:
theorem hasStrictDerivAt_abs_pos
  given: {x : Real} (hx : 0 < x)
  proof: (hasStrictDerivAt_id x).congr_of_eventuallyEq
    EqOn.eventuallyEq_of_mem (fun _ hy => (abs_of_pos (mem_Iio.1 hy)).symm) (Ioi_mem_nhds hx)

中文:
定理 hasStrictDerivAt_abs_pos
  条件: {x : 实数} (hx : 0 < x)
  证明: (hasStrictDerivAt_id x).congr_of_eventuallyEq
    EqOn.eventuallyEq_of_mem (fun _ hy => (abs_of_pos (mem_Iio.1 hy)).symm) (Ioi_mem_nhds hx)

Depends on / 依赖: EqOn.eventuallyEq_of_mem, Ioi_mem_nhds, abs_of_pos, congr_of_eventuallyEq, eventuallyEq_of_mem, hasStrictDerivAt_id, mem_Iio
-/
theorem hasStrictDerivAt_abs_pos {x : Real} (hx : 0 < x) :
    HasStrictDerivAt (|·|) 1 x :=
(hasStrictDerivAt_id x).congr_of_eventuallyEq
    EqOn.eventuallyEq_of_mem (fun _ hy => (abs_of_pos (mem_Iio.1 hy)).symm) (Ioi_mem_nhds hx)

/--
theorem `hasDerivAt_abs_pos` / 定理 `hasDerivAt_abs_pos`

English:
theorem hasDerivAt_abs_pos
  given: {x : Real} (hx : 0 < x)
  proof: (hasStrictDerivAt_abs_pos hx).hasDerivAt

中文:
定理 hasDerivAt_abs_pos
  条件: {x : 实数} (hx : 0 < x)
  证明: (hasStrictDerivAt_abs_pos hx).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_abs_pos
-/
theorem hasDerivAt_abs_pos {x : Real} (hx : 0 < x) :
    HasDerivAt (|·|) 1 x := (hasStrictDerivAt_abs_pos hx).hasDerivAt

/--
theorem `hasStrictDerivAt_abs` / 定理 `hasStrictDerivAt_abs`

English:
theorem hasStrictDerivAt_abs
  given: {x : Real} (hx : x != 0)
  proof: by
  obtain hx | hx := hx.lt_or_gt
  · simpa [hx] using hasStrictDerivAt_abs_neg hx
  · simpa [hx] using hasStrictDerivAt_abs_pos hx

中文:
定理 hasStrictDerivAt_abs
  条件: {x : 实数} (hx : x != 0)
  证明: by
  obtain hx | hx := hx.lt_or_gt
  · simpa [hx] using hasStrictDerivAt_abs_neg hx
  · simpa [hx] using hasStrictDerivAt_abs_pos hx

Depends on / 依赖: hasStrictDerivAt_abs_neg, hasStrictDerivAt_abs_pos, hx.lt_or_gt, lt_or_gt
-/
theorem hasStrictDerivAt_abs {x : Real} (hx : x != 0) :
    HasStrictDerivAt (|·|) (SignType.sign x : Real) x := by
  obtain hx | hx := hx.lt_or_gt
  · simpa [hx] using hasStrictDerivAt_abs_neg hx
  · simpa [hx] using hasStrictDerivAt_abs_pos hx

/--
theorem `hasDerivAt_abs` / 定理 `hasDerivAt_abs`

English:
theorem hasDerivAt_abs
  given: {x : Real} (hx : x != 0)
  proof: (hasStrictDerivAt_abs hx).hasDerivAt

中文:
定理 hasDerivAt_abs
  条件: {x : 实数} (hx : x != 0)
  证明: (hasStrictDerivAt_abs hx).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_abs
-/
theorem hasDerivAt_abs {x : Real} (hx : x != 0) :
    HasDerivAt (|·|) (SignType.sign x : Real) x := (hasStrictDerivAt_abs hx).hasDerivAt

/--
theorem `HasStrictFDerivAt.abs_of_neg` / 定理 `HasStrictFDerivAt.abs_of_neg`

English:
theorem HasStrictFDerivAt.abs_of_neg
  statement: (hf : HasStrictFDerivAt f f' x)
  proof: by
  convert! (hasStrictDerivAt_abs_neg h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp

中文:
定理 HasStrictFDerivAt.abs_of_neg
  结论: (hf : HasStrictFDerivAt f f' x)
  证明: by
  convert! (hasStrictDerivAt_abs_neg h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp

Depends on / 依赖: convert, hasStrictDerivAt_abs_neg, hasStrictFDerivAt, hasStrictFDerivAt.comp
-/
theorem HasStrictFDerivAt.abs_of_neg (hf : HasStrictFDerivAt f f' x)
    (h₀ : f x < 0) : HasStrictFDerivAt (fun x => |f x|) (-f') x := by
  convert! (hasStrictDerivAt_abs_neg h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp

/--
theorem `HasFDerivAt.abs_of_neg` / 定理 `HasFDerivAt.abs_of_neg`

English:
theorem HasFDerivAt.abs_of_neg
  statement: (hf : HasFDerivAt f f' x)
  proof: by
  convert! (hasDerivAt_abs_neg h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp

中文:
定理 HasFDerivAt.abs_of_neg
  结论: (hf : HasFDerivAt f f' x)
  证明: by
  convert! (hasDerivAt_abs_neg h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp

Depends on / 依赖: convert, hasDerivAt_abs_neg, hasFDerivAt, hasFDerivAt.comp
-/
theorem HasFDerivAt.abs_of_neg (hf : HasFDerivAt f f' x)
    (h₀ : f x < 0) : HasFDerivAt (fun x => |f x|) (-f') x := by
  convert! (hasDerivAt_abs_neg h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp

/--
theorem `HasStrictFDerivAt.abs_of_pos` / 定理 `HasStrictFDerivAt.abs_of_pos`

English:
theorem HasStrictFDerivAt.abs_of_pos
  statement: (hf : HasStrictFDerivAt f f' x)
  proof: by
  convert! (hasStrictDerivAt_abs_pos h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp

中文:
定理 HasStrictFDerivAt.abs_of_pos
  结论: (hf : HasStrictFDerivAt f f' x)
  证明: by
  convert! (hasStrictDerivAt_abs_pos h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp

Depends on / 依赖: convert, hasStrictDerivAt_abs_pos, hasStrictFDerivAt, hasStrictFDerivAt.comp
-/
theorem HasStrictFDerivAt.abs_of_pos (hf : HasStrictFDerivAt f f' x)
    (h₀ : 0 < f x) : HasStrictFDerivAt (fun x => |f x|) f' x := by
  convert! (hasStrictDerivAt_abs_pos h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp

/--
theorem `HasFDerivAt.abs_of_pos` / 定理 `HasFDerivAt.abs_of_pos`

English:
theorem HasFDerivAt.abs_of_pos
  statement: (hf : HasFDerivAt f f' x)
  proof: by
  convert! (hasDerivAt_abs_pos h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp

中文:
定理 HasFDerivAt.abs_of_pos
  结论: (hf : HasFDerivAt f f' x)
  证明: by
  convert! (hasDerivAt_abs_pos h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp

Depends on / 依赖: convert, hasDerivAt_abs_pos, hasFDerivAt, hasFDerivAt.comp
-/
theorem HasFDerivAt.abs_of_pos (hf : HasFDerivAt f f' x)
    (h₀ : 0 < f x) : HasFDerivAt (fun x => |f x|) f' x := by
  convert! (hasDerivAt_abs_pos h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp

/--
theorem `HasStrictFDerivAt.abs` / 定理 `HasStrictFDerivAt.abs`

English:
theorem HasStrictFDerivAt.abs
  statement: (hf : HasStrictFDerivAt f f' x)
  proof: by
  convert! (hasStrictDerivAt_abs h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp [mul_comm]

中文:
定理 HasStrictFDerivAt.abs
  结论: (hf : HasStrictFDerivAt f f' x)
  证明: by
  convert! (hasStrictDerivAt_abs h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp [mul_comm]

Depends on / 依赖: convert, hasStrictDerivAt_abs, hasStrictFDerivAt, hasStrictFDerivAt.comp, mul_comm
-/
theorem HasStrictFDerivAt.abs (hf : HasStrictFDerivAt f f' x)
    (h₀ : f x != 0) : HasStrictFDerivAt (fun x => |f x|) ((SignType.sign (f x) : Real) • f') x := by
  convert! (hasStrictDerivAt_abs h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp [mul_comm]

/--
theorem `HasFDerivAt.abs` / 定理 `HasFDerivAt.abs`

English:
theorem HasFDerivAt.abs
  statement: (hf : HasFDerivAt f f' x)
  proof: by
  convert! (hasDerivAt_abs h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp [mul_comm]

中文:
定理 HasFDerivAt.abs
  结论: (hf : HasFDerivAt f f' x)
  证明: by
  convert! (hasDerivAt_abs h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp [mul_comm]

Depends on / 依赖: convert, hasDerivAt_abs, hasFDerivAt, hasFDerivAt.comp, mul_comm
-/
theorem HasFDerivAt.abs (hf : HasFDerivAt f f' x)
    (h₀ : f x != 0) : HasFDerivAt (fun x => |f x|) ((SignType.sign (f x) : Real) • f') x := by
  convert! (hasDerivAt_abs h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp [mul_comm]

/--
theorem `hasDerivWithinAt_abs_neg` / 定理 `hasDerivWithinAt_abs_neg`

English:
theorem hasDerivWithinAt_abs_neg
  given: (s : Set Real) {x : Real} (hx : x < 0)
  proof: (hasDerivAt_abs_neg hx).hasDerivWithinAt

中文:
定理 hasDerivWithinAt_abs_neg
  条件: (s : Set 实数) {x : 实数} (hx : x < 0)
  证明: (hasDerivAt_abs_neg hx).hasDerivWithinAt

Depends on / 依赖: hasDerivAt_abs_neg, hasDerivWithinAt
-/
theorem hasDerivWithinAt_abs_neg (s : Set Real) {x : Real} (hx : x < 0) :
    HasDerivWithinAt (|·|) (-1) s x := (hasDerivAt_abs_neg hx).hasDerivWithinAt

/--
theorem `hasDerivWithinAt_abs_pos` / 定理 `hasDerivWithinAt_abs_pos`

English:
theorem hasDerivWithinAt_abs_pos
  given: (s : Set Real) {x : Real} (hx : 0 < x)
  proof: (hasDerivAt_abs_pos hx).hasDerivWithinAt

中文:
定理 hasDerivWithinAt_abs_pos
  条件: (s : Set 实数) {x : 实数} (hx : 0 < x)
  证明: (hasDerivAt_abs_pos hx).hasDerivWithinAt

Depends on / 依赖: hasDerivAt_abs_pos, hasDerivWithinAt
-/
theorem hasDerivWithinAt_abs_pos (s : Set Real) {x : Real} (hx : 0 < x) :
    HasDerivWithinAt (|·|) 1 s x := (hasDerivAt_abs_pos hx).hasDerivWithinAt

/--
theorem `hasDerivWithinAt_abs` / 定理 `hasDerivWithinAt_abs`

English:
theorem hasDerivWithinAt_abs
  given: (s : Set Real) {x : Real} (hx : x != 0)
  proof: (hasDerivAt_abs hx).hasDerivWithinAt

中文:
定理 hasDerivWithinAt_abs
  条件: (s : Set 实数) {x : 实数} (hx : x != 0)
  证明: (hasDerivAt_abs hx).hasDerivWithinAt

Depends on / 依赖: hasDerivAt_abs, hasDerivWithinAt
-/
theorem hasDerivWithinAt_abs (s : Set Real) {x : Real} (hx : x != 0) :
    HasDerivWithinAt (|·|) (SignType.sign x : Real) s x := (hasDerivAt_abs hx).hasDerivWithinAt

/--
theorem `HasFDerivWithinAt.abs_of_neg` / 定理 `HasFDerivWithinAt.abs_of_neg`

English:
theorem HasFDerivWithinAt.abs_of_neg
  statement: (hf : HasFDerivWithinAt f f' s x)
  proof: by
  convert! (hasDerivAt_abs_neg h₀).comp_hasFDerivWithinAt x hf using 1
  simp

中文:
定理 HasFDerivWithinAt.abs_of_neg
  结论: (hf : HasFDerivWithinAt f f' s x)
  证明: by
  convert! (hasDerivAt_abs_neg h₀).comp_hasFDerivWithinAt x hf using 1
  simp

Depends on / 依赖: comp_hasFDerivWithinAt, convert, hasDerivAt_abs_neg
-/
theorem HasFDerivWithinAt.abs_of_neg (hf : HasFDerivWithinAt f f' s x)
    (h₀ : f x < 0) : HasFDerivWithinAt (fun x => |f x|) (-f') s x := by
  convert! (hasDerivAt_abs_neg h₀).comp_hasFDerivWithinAt x hf using 1
  simp

/--
theorem `HasFDerivWithinAt.abs_of_pos` / 定理 `HasFDerivWithinAt.abs_of_pos`

English:
theorem HasFDerivWithinAt.abs_of_pos
  statement: (hf : HasFDerivWithinAt f f' s x)
  proof: by
  convert! (hasDerivAt_abs_pos h₀).comp_hasFDerivWithinAt x hf using 1
  simp

中文:
定理 HasFDerivWithinAt.abs_of_pos
  结论: (hf : HasFDerivWithinAt f f' s x)
  证明: by
  convert! (hasDerivAt_abs_pos h₀).comp_hasFDerivWithinAt x hf using 1
  simp

Depends on / 依赖: comp_hasFDerivWithinAt, convert, hasDerivAt_abs_pos
-/
theorem HasFDerivWithinAt.abs_of_pos (hf : HasFDerivWithinAt f f' s x)
    (h₀ : 0 < f x) : HasFDerivWithinAt (fun x => |f x|) f' s x := by
  convert! (hasDerivAt_abs_pos h₀).comp_hasFDerivWithinAt x hf using 1
  simp

/--
theorem `HasFDerivWithinAt.abs` / 定理 `HasFDerivWithinAt.abs`

English:
theorem HasFDerivWithinAt.abs
  statement: (hf : HasFDerivWithinAt f f' s x)
  proof: (hasDerivAt_abs h₀).comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.abs
  结论: (hf : HasFDerivWithinAt f f' s x)
  证明: (hasDerivAt_abs h₀).comp_hasFDerivWithinAt x hf

Depends on / 依赖: comp_hasFDerivWithinAt, hasDerivAt_abs
-/
theorem HasFDerivWithinAt.abs (hf : HasFDerivWithinAt f f' s x)
    (h₀ : f x != 0) : HasFDerivWithinAt (fun x => |f x|) ((SignType.sign (f x) : Real) • f') s x :=
  (hasDerivAt_abs h₀).comp_hasFDerivWithinAt x hf

/--
theorem `differentiableAt_abs_neg` / 定理 `differentiableAt_abs_neg`

English:
theorem differentiableAt_abs_neg
  given: {x : Real} (hx : x < 0)
  proof: (hasDerivAt_abs_neg hx).differentiableAt

中文:
定理 differentiableAt_abs_neg
  条件: {x : 实数} (hx : x < 0)
  证明: (hasDerivAt_abs_neg hx).differentiableAt

Depends on / 依赖: differentiableAt, hasDerivAt_abs_neg
-/
theorem differentiableAt_abs_neg {x : Real} (hx : x < 0) :
    DifferentiableAt Real (|·|) x := (hasDerivAt_abs_neg hx).differentiableAt

/--
theorem `differentiableAt_abs_pos` / 定理 `differentiableAt_abs_pos`

English:
theorem differentiableAt_abs_pos
  given: {x : Real} (hx : 0 < x)
  proof: (hasDerivAt_abs_pos hx).differentiableAt

中文:
定理 differentiableAt_abs_pos
  条件: {x : 实数} (hx : 0 < x)
  证明: (hasDerivAt_abs_pos hx).differentiableAt

Depends on / 依赖: differentiableAt, hasDerivAt_abs_pos
-/
theorem differentiableAt_abs_pos {x : Real} (hx : 0 < x) :
    DifferentiableAt Real (|·|) x := (hasDerivAt_abs_pos hx).differentiableAt

/--
theorem `differentiableAt_abs` / 定理 `differentiableAt_abs`

English:
theorem differentiableAt_abs
  given: {x : Real} (hx : x != 0)
  proof: (hasDerivAt_abs hx).differentiableAt

中文:
定理 differentiableAt_abs
  条件: {x : 实数} (hx : x != 0)
  证明: (hasDerivAt_abs hx).differentiableAt

Depends on / 依赖: differentiableAt, hasDerivAt_abs
-/
theorem differentiableAt_abs {x : Real} (hx : x != 0) :
    DifferentiableAt Real (|·|) x := (hasDerivAt_abs hx).differentiableAt

/--
theorem `DifferentiableAt.abs_of_neg` / 定理 `DifferentiableAt.abs_of_neg`

English:
theorem DifferentiableAt.abs_of_neg
  given: (hf : DifferentiableAt Real f x) (h₀ : f x < 0)
  proof: (differentiableAt_abs_neg h₀).comp x hf

中文:
定理 DifferentiableAt.abs_of_neg
  条件: (hf : DifferentiableAt 实数 f x) (h₀ : f x < 0)
  证明: (differentiableAt_abs_neg h₀).comp x hf

Depends on / 依赖: differentiableAt_abs_neg
-/
theorem DifferentiableAt.abs_of_neg (hf : DifferentiableAt Real f x) (h₀ : f x < 0) :
    DifferentiableAt Real (fun x => |f x|) x := (differentiableAt_abs_neg h₀).comp x hf

/--
theorem `DifferentiableAt.abs_of_pos` / 定理 `DifferentiableAt.abs_of_pos`

English:
theorem DifferentiableAt.abs_of_pos
  given: (hf : DifferentiableAt Real f x) (h₀ : 0 < f x)
  proof: (differentiableAt_abs_pos h₀).comp x hf

中文:
定理 DifferentiableAt.abs_of_pos
  条件: (hf : DifferentiableAt 实数 f x) (h₀ : 0 < f x)
  证明: (differentiableAt_abs_pos h₀).comp x hf

Depends on / 依赖: differentiableAt_abs_pos
-/
theorem DifferentiableAt.abs_of_pos (hf : DifferentiableAt Real f x) (h₀ : 0 < f x) :
    DifferentiableAt Real (fun x => |f x|) x := (differentiableAt_abs_pos h₀).comp x hf

/--
theorem `DifferentiableAt.abs` / 定理 `DifferentiableAt.abs`

English:
theorem DifferentiableAt.abs
  given: (hf : DifferentiableAt Real f x) (h₀ : f x != 0)
  proof: (differentiableAt_abs h₀).comp x hf

中文:
定理 DifferentiableAt.abs
  条件: (hf : DifferentiableAt 实数 f x) (h₀ : f x != 0)
  证明: (differentiableAt_abs h₀).comp x hf

Depends on / 依赖: differentiableAt_abs
-/
theorem DifferentiableAt.abs (hf : DifferentiableAt Real f x) (h₀ : f x != 0) :
    DifferentiableAt Real (fun x => |f x|) x := (differentiableAt_abs h₀).comp x hf

/--
theorem `differentiableWithinAt_abs_neg` / 定理 `differentiableWithinAt_abs_neg`

English:
theorem differentiableWithinAt_abs_neg
  given: (s : Set Real) {x : Real} (hx : x < 0)
  proof: (differentiableAt_abs_neg hx).differentiableWithinAt

中文:
定理 differentiableWithinAt_abs_neg
  条件: (s : Set 实数) {x : 实数} (hx : x < 0)
  证明: (differentiableAt_abs_neg hx).differentiableWithinAt

Depends on / 依赖: differentiableAt_abs_neg, differentiableWithinAt
-/
theorem differentiableWithinAt_abs_neg (s : Set Real) {x : Real} (hx : x < 0) :
    DifferentiableWithinAt Real (|·|) s x := (differentiableAt_abs_neg hx).differentiableWithinAt

/--
theorem `differentiableWithinAt_abs_pos` / 定理 `differentiableWithinAt_abs_pos`

English:
theorem differentiableWithinAt_abs_pos
  given: (s : Set Real) {x : Real} (hx : 0 < x)
  proof: (differentiableAt_abs_pos hx).differentiableWithinAt

中文:
定理 differentiableWithinAt_abs_pos
  条件: (s : Set 实数) {x : 实数} (hx : 0 < x)
  证明: (differentiableAt_abs_pos hx).differentiableWithinAt

Depends on / 依赖: differentiableAt_abs_pos, differentiableWithinAt
-/
theorem differentiableWithinAt_abs_pos (s : Set Real) {x : Real} (hx : 0 < x) :
    DifferentiableWithinAt Real (|·|) s x := (differentiableAt_abs_pos hx).differentiableWithinAt

/--
theorem `differentiableWithinAt_abs` / 定理 `differentiableWithinAt_abs`

English:
theorem differentiableWithinAt_abs
  given: (s : Set Real) {x : Real} (hx : x != 0)
  proof: (differentiableAt_abs hx).differentiableWithinAt

中文:
定理 differentiableWithinAt_abs
  条件: (s : Set 实数) {x : 实数} (hx : x != 0)
  证明: (differentiableAt_abs hx).differentiableWithinAt

Depends on / 依赖: differentiableAt_abs, differentiableWithinAt
-/
theorem differentiableWithinAt_abs (s : Set Real) {x : Real} (hx : x != 0) :
    DifferentiableWithinAt Real (|·|) s x := (differentiableAt_abs hx).differentiableWithinAt

/--
theorem `DifferentiableWithinAt.abs_of_neg` / 定理 `DifferentiableWithinAt.abs_of_neg`

English:
theorem DifferentiableWithinAt.abs_of_neg
  given: (hf : DifferentiableWithinAt Real f s x) (h₀ : f x < 0)
  proof: (differentiableAt_abs_neg h₀).comp_differentiableWithinAt x hf

中文:
定理 DifferentiableWithinAt.abs_of_neg
  条件: (hf : DifferentiableWithinAt 实数 f s x) (h₀ : f x < 0)
  证明: (differentiableAt_abs_neg h₀).comp_differentiableWithinAt x hf

Depends on / 依赖: comp_differentiableWithinAt, differentiableAt_abs_neg
-/
theorem DifferentiableWithinAt.abs_of_neg (hf : DifferentiableWithinAt Real f s x) (h₀ : f x < 0) :
    DifferentiableWithinAt Real (fun x => |f x|) s x :=
  (differentiableAt_abs_neg h₀).comp_differentiableWithinAt x hf

/--
theorem `DifferentiableWithinAt.abs_of_pos` / 定理 `DifferentiableWithinAt.abs_of_pos`

English:
theorem DifferentiableWithinAt.abs_of_pos
  given: (hf : DifferentiableWithinAt Real f s x) (h₀ : 0 < f x)
  proof: (differentiableAt_abs_pos h₀).comp_differentiableWithinAt x hf

中文:
定理 DifferentiableWithinAt.abs_of_pos
  条件: (hf : DifferentiableWithinAt 实数 f s x) (h₀ : 0 < f x)
  证明: (differentiableAt_abs_pos h₀).comp_differentiableWithinAt x hf

Depends on / 依赖: comp_differentiableWithinAt, differentiableAt_abs_pos
-/
theorem DifferentiableWithinAt.abs_of_pos (hf : DifferentiableWithinAt Real f s x) (h₀ : 0 < f x) :
    DifferentiableWithinAt Real (fun x => |f x|) s x :=
  (differentiableAt_abs_pos h₀).comp_differentiableWithinAt x hf

/--
theorem `DifferentiableWithinAt.abs` / 定理 `DifferentiableWithinAt.abs`

English:
theorem DifferentiableWithinAt.abs
  given: (hf : DifferentiableWithinAt Real f s x) (h₀ : f x != 0)
  proof: (differentiableAt_abs h₀).comp_differentiableWithinAt x hf

中文:
定理 DifferentiableWithinAt.abs
  条件: (hf : DifferentiableWithinAt 实数 f s x) (h₀ : f x != 0)
  证明: (differentiableAt_abs h₀).comp_differentiableWithinAt x hf

Depends on / 依赖: comp_differentiableWithinAt, differentiableAt_abs
-/
theorem DifferentiableWithinAt.abs (hf : DifferentiableWithinAt Real f s x) (h₀ : f x != 0) :
    DifferentiableWithinAt Real (fun x => |f x|) s x :=
  (differentiableAt_abs h₀).comp_differentiableWithinAt x hf

/--
theorem `differentiableOn_abs` / 定理 `differentiableOn_abs`

English:
theorem differentiableOn_abs
  given: {s : Set Real} (hs : forall x in s, x != 0)
  statement: DifferentiableOn Real (|·|) s
  proof: fun x hx => differentiableWithinAt_abs s (hs x hx)

中文:
定理 differentiableOn_abs
  条件: {s : Set 实数} (hs : 对任意 x in s, x != 0)
  结论: DifferentiableOn 实数 (|·|) s
  证明: fun x hx => differentiableWithinAt_abs s (hs x hx)

Depends on / 依赖: differentiableWithinAt_abs
-/
theorem differentiableOn_abs {s : Set Real} (hs : forall x in s, x != 0) : DifferentiableOn Real (|·|) s :=
  fun x hx => differentiableWithinAt_abs s (hs x hx)

/--
theorem `DifferentiableOn.abs` / 定理 `DifferentiableOn.abs`

English:
theorem DifferentiableOn.abs
  given: (hf : DifferentiableOn Real f s) (h₀ : forall x in s, f x != 0)
  proof: fun x hx => (hf x hx).abs (h₀ x hx)

中文:
定理 DifferentiableOn.abs
  条件: (hf : DifferentiableOn 实数 f s) (h₀ : 对任意 x in s, f x != 0)
  证明: fun x hx => (hf x hx).abs (h₀ x hx)
-/
theorem DifferentiableOn.abs (hf : DifferentiableOn Real f s) (h₀ : forall x in s, f x != 0) :
    DifferentiableOn Real (fun x => |f x|) s :=
  fun x hx => (hf x hx).abs (h₀ x hx)

/--
theorem `Differentiable.abs` / 定理 `Differentiable.abs`

English:
theorem Differentiable.abs
  given: (hf : Differentiable Real f) (h₀ : forall x, f x != 0)
  proof: fun x => (hf x).abs (h₀ x)

中文:
定理 Differentiable.abs
  条件: (hf : Differentiable 实数 f) (h₀ : 对任意 x, f x != 0)
  证明: fun x => (hf x).abs (h₀ x)
-/
theorem Differentiable.abs (hf : Differentiable Real f) (h₀ : forall x, f x != 0) :
    Differentiable Real (fun x => |f x|) := fun x => (hf x).abs (h₀ x)

/--
theorem `not_differentiableAt_abs_zero` / 定理 `not_differentiableAt_abs_zero`

English:
theorem not_differentiableAt_abs_zero
  statement: ¬ DifferentiableAt Real (abs : Real -> Real) 0
  proof: by
  intro h
  have h₁ : deriv abs (0 : Real) = 1 :=
(uniqueDiffOn_Ici _ _ Set.self_mem_Ici).eq_deriv _ h.hasDerivAt.hasDerivWithinAt
      (hasDerivWithinAt_id _ _).congr_of_mem (fun _ h => abs_of_nonneg h) Set.self_mem_Ici
  have h₂ : deriv abs (0 : Real) = -1 :=
(uniqueDiffOn_Iic _ _ Set.self_mem

中文:
定理 not_differentiableAt_abs_zero
  结论: ¬ DifferentiableAt 实数 (abs : 实数 -> 实数) 0
  证明: by
  intro h
  have h₁ : deriv abs (0 : Real) = 1 :=
(uniqueDiffOn_Ici _ _ Set.self_mem_Ici).eq_deriv _ h.hasDerivAt.hasDerivWithinAt
      (hasDerivWithinAt_id _ _).congr_of_mem (fun _ h => abs_of_nonneg h) Set.self_mem_Ici
  have h₂ : deriv abs (0 : Real) = -1 :=
(uniqueDiffOn_Iic _ _ Set.self_mem

Depends on / 依赖: Set.self_mem_Ici, Set.self_mem_Iic, abs_of_nonneg, abs_of_nonpos, congr_of_mem, eq_deriv, h.hasDerivAt.hasDerivWithinAt, hasDerivAt, hasDerivWithinAt, hasDerivWithinAt_id, hasDerivWithinAt_neg, self_mem_Ici, self_mem_Iic, uniqueDiffOn_Ici, uniqueDiffOn_Iic
-/
theorem not_differentiableAt_abs_zero : ¬ DifferentiableAt Real (abs : Real -> Real) 0 := by
  intro h
  have h₁ : deriv abs (0 : Real) = 1 :=
(uniqueDiffOn_Ici _ _ Set.self_mem_Ici).eq_deriv _ h.hasDerivAt.hasDerivWithinAt
      (hasDerivWithinAt_id _ _).congr_of_mem (fun _ h => abs_of_nonneg h) Set.self_mem_Ici
  have h₂ : deriv abs (0 : Real) = -1 :=
(uniqueDiffOn_Iic _ _ Set.self_mem_Iic).eq_deriv _ h.hasDerivAt.hasDerivWithinAt
      (hasDerivWithinAt_neg _ _).congr_of_mem (fun _ h => abs_of_nonpos h) Set.self_mem_Iic
  linarith

/--
theorem `deriv_abs_neg` / 定理 `deriv_abs_neg`

English:
theorem deriv_abs_neg
  given: {x : Real} (hx : x < 0)
  statement: deriv (|·|) x = -1
  proof: (hasDerivAt_abs_neg hx).deriv

中文:
定理 deriv_abs_neg
  条件: {x : 实数} (hx : x < 0)
  结论: deriv (|·|) x = -1
  证明: (hasDerivAt_abs_neg hx).deriv

Depends on / 依赖: hasDerivAt_abs_neg
-/
theorem deriv_abs_neg {x : Real} (hx : x < 0) : deriv (|·|) x = -1 := (hasDerivAt_abs_neg hx).deriv

/--
theorem `deriv_abs_pos` / 定理 `deriv_abs_pos`

English:
theorem deriv_abs_pos
  given: {x : Real} (hx : 0 < x)
  statement: deriv (|·|) x = 1
  proof: (hasDerivAt_abs_pos hx).deriv

中文:
定理 deriv_abs_pos
  条件: {x : 实数} (hx : 0 < x)
  结论: deriv (|·|) x = 1
  证明: (hasDerivAt_abs_pos hx).deriv

Depends on / 依赖: hasDerivAt_abs_pos
-/
theorem deriv_abs_pos {x : Real} (hx : 0 < x) : deriv (|·|) x = 1 := (hasDerivAt_abs_pos hx).deriv

/--
theorem `deriv_abs_zero` / 定理 `deriv_abs_zero`

English:
theorem deriv_abs_zero
  statement: deriv (|·|) (0 : Real) = 0
  proof: deriv_zero_of_not_differentiableAt not_differentiableAt_abs_zero

中文:
定理 deriv_abs_zero
  结论: deriv (|·|) (0 : 实数) = 0
  证明: deriv_zero_of_not_differentiableAt not_differentiableAt_abs_zero

Depends on / 依赖: deriv_zero_of_not_differentiableAt, not_differentiableAt_abs_zero
-/
theorem deriv_abs_zero : deriv (|·|) (0 : Real) = 0 :=
  deriv_zero_of_not_differentiableAt not_differentiableAt_abs_zero

/--
theorem `deriv_abs` / 定理 `deriv_abs`

English:
theorem deriv_abs
  given: (x : Real)
  statement: deriv (|·|) x = SignType.sign x
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · simpa using deriv_abs_zero
  · simpa [hx] using (hasDerivAt_abs hx).deriv

中文:
定理 deriv_abs
  条件: (x : 实数)
  结论: deriv (|·|) x = SignType.sign x
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · simpa using deriv_abs_zero
  · simpa [hx] using (hasDerivAt_abs hx).deriv

Depends on / 依赖: deriv_abs_zero, eq_or_ne, hasDerivAt_abs
-/
theorem deriv_abs (x : Real) : deriv (|·|) x = SignType.sign x := by
  obtain rfl | hx := eq_or_ne x 0
  · simpa using deriv_abs_zero
  · simpa [hx] using (hasDerivAt_abs hx).deriv
