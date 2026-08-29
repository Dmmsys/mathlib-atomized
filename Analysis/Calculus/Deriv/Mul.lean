/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Anatole Dedecker, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Derivative of `f x * g x`

In this file we prove formulas for `(f x * g x)'` and `(f x • g x)'`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, multiplication
-/

public section

universe u v w

noncomputable section

open scoped Topology Filter ENNReal

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f : 𝕜 -> F}
variable {f' : F}
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {L : Filter (𝕜 × 𝕜)}

/-! ### Derivative of bilinear maps -/

namespace ContinuousLinearMap

variable {B : E ->L[𝕜] F ->L[𝕜] G} {u : 𝕜 -> E} {v : 𝕜 -> F} {u' : E} {v' : F}

/--
theorem `hasDerivWithinAt_of_bilinear` / 定理 `hasDerivWithinAt_of_bilinear`

English:
theorem hasDerivWithinAt_of_bilinear
  proof: by
  simpa using (B.hasFDerivWithinAt_of_bilinear
    hu.hasFDerivWithinAt hv.hasFDerivWithinAt).hasDerivWithinAt

中文:
定理 hasDerivWithinAt_of_bilinear
  证明: by
  simpa using (B.hasFDerivWithinAt_of_bilinear
    hu.hasFDerivWithinAt hv.hasFDerivWithinAt).hasDerivWithinAt

Depends on / 依赖: B.hasFDerivWithinAt_of_bilinear, hasDerivWithinAt, hasFDerivWithinAt, hasFDerivWithinAt_of_bilinear, hu.hasFDerivWithinAt, hv.hasFDerivWithinAt
-/
theorem hasDerivWithinAt_of_bilinear
    (hu : HasDerivWithinAt u u' s x) (hv : HasDerivWithinAt v v' s x) :
    HasDerivWithinAt (fun x => B (u x) (v x)) (B (u x) v' + B u' (v x)) s x := by
  simpa using (B.hasFDerivWithinAt_of_bilinear
    hu.hasFDerivWithinAt hv.hasFDerivWithinAt).hasDerivWithinAt

/--
theorem `hasDerivAt_of_bilinear` / 定理 `hasDerivAt_of_bilinear`

English:
theorem hasDerivAt_of_bilinear
  statement: (hu : x in tsupport v -> HasDerivAt u u' x)
  proof: by
  by_cases hxu : x in tsupport u
  · by_cases hxv : x in tsupport v
    · simpa using (B.hasFDerivAt_of_bilinear (hu hxv).hasFDerivAt (hv hxu).hasFDerivAt).hasDerivAt
    · have hx : x ∉ tsupport fun x => B (u x) (v x) :=
        mt (closure_mono (fun x => mt fun h => by simp [h]) ·) hxv
      co

中文:
定理 hasDerivAt_of_bilinear
  结论: (hu : x in tsupport v -> 在点处可导 u u' x)
  证明: by
  by_cases hxu : x in tsupport u
  · by_cases hxv : x in tsupport v
    · simpa using (B.hasFDerivAt_of_bilinear (hu hxv).hasFDerivAt (hv hxu).hasFDerivAt).hasDerivAt
    · have hx : x ∉ tsupport fun x => B (u x) (v x) :=
        mt (closure_mono (fun x => mt fun h => by simp [h]) ·) hxv
      co

Depends on / 依赖: B.hasFDerivAt_of_bilinear, HasDerivAt, HasDerivAt.of_notMem_tsupport, closure_mono, convert, hasDerivAt, hasFDerivAt, hasFDerivAt_of_bilinear, image_eq_zero_of_notMem_tsupport, of_notMem_tsupport, tsupport, unique
-/
theorem hasDerivAt_of_bilinear (hu : x in tsupport v -> HasDerivAt u u' x)
    (hv : x in tsupport u -> HasDerivAt v v' x) :
    HasDerivAt (fun x => B (u x) (v x)) (B (u x) v' + B u' (v x)) x := by
  by_cases hxu : x in tsupport u
  · by_cases hxv : x in tsupport v
    · simpa using (B.hasFDerivAt_of_bilinear (hu hxv).hasFDerivAt (hv hxu).hasFDerivAt).hasDerivAt
    · have hx : x ∉ tsupport fun x => B (u x) (v x) :=
        mt (closure_mono (fun x => mt fun h => by simp [h]) ·) hxv
      convert! HasDerivAt.of_notMem_tsupport hx
      simp [(hv hxu).unique <| .of_notMem_tsupport hxv, image_eq_zero_of_notMem_tsupport hxv]
  · have hx : x ∉ tsupport fun x => B (u x) (v x) :=
      mt (closure_mono (fun x => mt fun h => by simp [h]) ·) hxu
    convert! HasDerivAt.of_notMem_tsupport hx
    by_cases hxv : x in tsupport v
    · simp [image_eq_zero_of_notMem_tsupport hxu, (hu hxv).unique <| .of_notMem_tsupport hxu]
    · simp [image_eq_zero_of_notMem_tsupport hxu, image_eq_zero_of_notMem_tsupport hxv]

/--
theorem `hasStrictDerivAt_of_bilinear` / 定理 `hasStrictDerivAt_of_bilinear`

English:
theorem hasStrictDerivAt_of_bilinear
  given: (hu : HasStrictDerivAt u u' x) (hv : HasStrictDerivAt v v' x)
  proof: by
  simpa using
    (B.hasStrictFDerivAt_of_bilinear hu.hasStrictFDerivAt hv.hasStrictFDerivAt).hasStrictDerivAt

中文:
定理 hasStrictDerivAt_of_bilinear
  条件: (hu : HasStrictDerivAt u u' x) (hv : HasStrictDerivAt v v' x)
  证明: by
  simpa using
    (B.hasStrictFDerivAt_of_bilinear hu.hasStrictFDerivAt hv.hasStrictFDerivAt).hasStrictDerivAt

Depends on / 依赖: B.hasStrictFDerivAt_of_bilinear, hasStrictDerivAt, hasStrictFDerivAt, hasStrictFDerivAt_of_bilinear, hu.hasStrictFDerivAt, hv.hasStrictFDerivAt
-/
theorem hasStrictDerivAt_of_bilinear (hu : HasStrictDerivAt u u' x) (hv : HasStrictDerivAt v v' x) :
    HasStrictDerivAt (fun x => B (u x) (v x)) (B (u x) v' + B u' (v x)) x := by
  simpa using
    (B.hasStrictFDerivAt_of_bilinear hu.hasStrictFDerivAt hv.hasStrictFDerivAt).hasStrictDerivAt

/--
theorem `derivWithin_of_bilinear` / 定理 `derivWithin_of_bilinear`

English:
theorem derivWithin_of_bilinear
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (B.hasDerivWithinAt_of_bilinear hu.hasDerivWithinAt hv.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_of_bilinear
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (B.hasDerivWithinAt_of_bilinear hu.hasDerivWithinAt hv.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: B.hasDerivWithinAt_of_bilinear, UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hasDerivWithinAt_of_bilinear, hu.hasDerivWithinAt, hv.hasDerivWithinAt
-/
theorem derivWithin_of_bilinear
    (hu : DifferentiableWithinAt 𝕜 u s x) (hv : DifferentiableWithinAt 𝕜 v s x) :
    derivWithin (fun y => B (u y) (v y)) s x =
      B (u x) (derivWithin v s x) + B (derivWithin u s x) (v x) := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (B.hasDerivWithinAt_of_bilinear hu.hasDerivWithinAt hv.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `deriv_of_bilinear` / 定理 `deriv_of_bilinear`

English:
theorem deriv_of_bilinear
  statement: (hu : x in tsupport v -> DifferentiableAt 𝕜 u x)
  proof: (B.hasDerivAt_of_bilinear (fun hx => (hu hx).hasDerivAt) fun hx => (hv hx).hasDerivAt).deriv

中文:
定理 deriv_of_bilinear
  结论: (hu : x in tsupport v -> DifferentiableAt 𝕜 u x)
  证明: (B.hasDerivAt_of_bilinear (fun hx => (hu hx).hasDerivAt) fun hx => (hv hx).hasDerivAt).deriv

Depends on / 依赖: B.hasDerivAt_of_bilinear, hasDerivAt, hasDerivAt_of_bilinear
-/
theorem deriv_of_bilinear (hu : x in tsupport v -> DifferentiableAt 𝕜 u x)
    (hv : x in tsupport u -> DifferentiableAt 𝕜 v x) :
    deriv (fun y => B (u y) (v y)) x = B (u x) (deriv v x) + B (deriv u x) (v x) :=
  (B.hasDerivAt_of_bilinear (fun hx => (hu hx).hasDerivAt) fun hx => (hv hx).hasDerivAt).deriv

end ContinuousLinearMap

section SMul

/-! ### Derivative of the multiplication of a scalar function and a vector function -/


variable {𝕜' : Type*} [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {c : 𝕜 -> 𝕜'} {c' : 𝕜'}

@[to_fun]
/--
theorem `HasDerivWithinAt.smul` / 定理 `HasDerivWithinAt.smul`

English:
theorem HasDerivWithinAt.smul
  given: (hc : HasDerivWithinAt c c' s x) (hf : HasDerivWithinAt f f' s x)
  proof: by
  simpa using (HasFDerivWithinAt.smul hc hf).hasDerivWithinAt

@[to_fun]

中文:
定理 HasDerivWithinAt.smul
  条件: (hc : HasDerivWithinAt c c' s x) (hf : HasDerivWithinAt f f' s x)
  证明: by
  simpa using (HasFDerivWithinAt.smul hc hf).hasDerivWithinAt

@[to_fun]

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.smul, hasDerivWithinAt
-/
theorem HasDerivWithinAt.smul (hc : HasDerivWithinAt c c' s x) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (c • f) (c x • f' + c' • f x) s x := by
  simpa using (HasFDerivWithinAt.smul hc hf).hasDerivWithinAt

@[to_fun]
/--
theorem `HasDerivAt.smul` / 定理 `HasDerivAt.smul`

English:
theorem HasDerivAt.smul
  given: (hc : HasDerivAt c c' x) (hf : HasDerivAt f f' x)
  proof: by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.smul hf

@[to_fun]

中文:
定理 在点处可导.smul
  条件: (hc : 在点处可导 c c' x) (hf : 在点处可导 f f' x)
  证明: by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.smul hf

@[to_fun]

Depends on / 依赖: hasDerivWithinAt_univ, hc.smul
-/
theorem HasDerivAt.smul (hc : HasDerivAt c c' x) (hf : HasDerivAt f f' x) :
    HasDerivAt (c • f) (c x • f' + c' • f x) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.smul hf

@[to_fun]
/--
theorem `HasStrictDerivAt.smul` / 定理 `HasStrictDerivAt.smul`

English:
theorem HasStrictDerivAt.smul
  given: (hc : HasStrictDerivAt c c' x) (hf : HasStrictDerivAt f f' x)
  proof: by
  simpa using (HasStrictFDerivAt.smul hc hf).hasStrictDerivAt

中文:
定理 HasStrictDerivAt.smul
  条件: (hc : HasStrictDerivAt c c' x) (hf : HasStrictDerivAt f f' x)
  证明: by
  simpa using (HasStrictFDerivAt.smul hc hf).hasStrictDerivAt

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.smul, hasStrictDerivAt
-/
theorem HasStrictDerivAt.smul (hc : HasStrictDerivAt c c' x) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (c • f) (c x • f' + c' • f x) x := by
  simpa using (HasStrictFDerivAt.smul hc hf).hasStrictDerivAt

/--
theorem `derivWithin_fun_smul` / 定理 `derivWithin_fun_smul`

English:
theorem derivWithin_fun_smul
  statement: (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.smul hf.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_fun_smul
  结论: (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.smul hf.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hc.hasDerivWithinAt.smul, hf.hasDerivWithinAt
-/
theorem derivWithin_fun_smul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (fun y => c y • f y) s x = c x • derivWithin f s x + derivWithin c s x • f x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.smul hf.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `derivWithin_smul` / 定理 `derivWithin_smul`

English:
theorem derivWithin_smul
  statement: (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: derivWithin_fun_smul hc hf

中文:
定理 derivWithin_smul
  结论: (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: derivWithin_fun_smul hc hf

Depends on / 依赖: derivWithin_fun_smul
-/
theorem derivWithin_smul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (c • f) s x = c x • derivWithin f s x + derivWithin c s x • f x :=
  derivWithin_fun_smul hc hf

/--
theorem `deriv_fun_smul` / 定理 `deriv_fun_smul`

English:
theorem deriv_fun_smul
  given: (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x)
  proof: (hc.hasDerivAt.smul hf.hasDerivAt).deriv

中文:
定理 deriv_fun_smul
  条件: (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x)
  证明: (hc.hasDerivAt.smul hf.hasDerivAt).deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.smul, hf.hasDerivAt
-/
theorem deriv_fun_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    deriv (fun y => c y • f y) x = c x • deriv f x + deriv c x • f x :=
  (hc.hasDerivAt.smul hf.hasDerivAt).deriv

/--
theorem `deriv_smul` / 定理 `deriv_smul`

English:
theorem deriv_smul
  given: (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x)
  proof: (hc.hasDerivAt.smul hf.hasDerivAt).deriv

中文:
定理 deriv_smul
  条件: (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x)
  证明: (hc.hasDerivAt.smul hf.hasDerivAt).deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.smul, hf.hasDerivAt
-/
theorem deriv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    deriv (c • f) x = c x • deriv f x + deriv c x • f x :=
  (hc.hasDerivAt.smul hf.hasDerivAt).deriv

/--
theorem `HasStrictDerivAt.smul_const` / 定理 `HasStrictDerivAt.smul_const`

English:
theorem HasStrictDerivAt.smul_const
  given: (hc : HasStrictDerivAt c c' x) (f : F)
  proof: by
  have := hc.smul (hasStrictDerivAt_const x f)
  rwa [smul_zero, zero_add] at this

中文:
定理 HasStrictDerivAt.smul_const
  条件: (hc : HasStrictDerivAt c c' x) (f : F)
  证明: by
  have := hc.smul (hasStrictDerivAt_const x f)
  rwa [smul_zero, zero_add] at this

Depends on / 依赖: hasStrictDerivAt_const, hc.smul, smul_zero, zero_add
-/
theorem HasStrictDerivAt.smul_const (hc : HasStrictDerivAt c c' x) (f : F) :
    HasStrictDerivAt (fun y => c y • f) (c' • f) x := by
  have := hc.smul (hasStrictDerivAt_const x f)
  rwa [smul_zero, zero_add] at this

/--
theorem `HasDerivWithinAt.smul_const` / 定理 `HasDerivWithinAt.smul_const`

English:
theorem HasDerivWithinAt.smul_const
  given: (hc : HasDerivWithinAt c c' s x) (f : F)
  proof: by
  have := hc.smul (hasDerivWithinAt_const x s f)
  rwa [smul_zero, zero_add] at this

中文:
定理 HasDerivWithinAt.smul_const
  条件: (hc : HasDerivWithinAt c c' s x) (f : F)
  证明: by
  have := hc.smul (hasDerivWithinAt_const x s f)
  rwa [smul_zero, zero_add] at this

Depends on / 依赖: hasDerivWithinAt_const, hc.smul, smul_zero, zero_add
-/
theorem HasDerivWithinAt.smul_const (hc : HasDerivWithinAt c c' s x) (f : F) :
    HasDerivWithinAt (fun y => c y • f) (c' • f) s x := by
  have := hc.smul (hasDerivWithinAt_const x s f)
  rwa [smul_zero, zero_add] at this

/--
theorem `HasDerivAt.smul_const` / 定理 `HasDerivAt.smul_const`

English:
theorem HasDerivAt.smul_const
  given: (hc : HasDerivAt c c' x) (f : F)
  proof: by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.smul_const f

中文:
定理 在点处可导.smul_const
  条件: (hc : 在点处可导 c c' x) (f : F)
  证明: by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.smul_const f

Depends on / 依赖: hasDerivWithinAt_univ, hc.smul_const, smul_const
-/
theorem HasDerivAt.smul_const (hc : HasDerivAt c c' x) (f : F) :
    HasDerivAt (fun y => c y • f) (c' • f) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.smul_const f

-- TODO: Version of this without differentiability assumptions when `c` takes values in a
-- division ring (seems non-trivial)
/--
theorem `derivWithin_smul_const` / 定理 `derivWithin_smul_const`

English:
theorem derivWithin_smul_const
  given: (hc : DifferentiableWithinAt 𝕜 c s x) (f : F)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.smul_const f).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_smul_const
  条件: (hc : DifferentiableWithinAt 𝕜 c s x) (f : F)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.smul_const f).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hc.hasDerivWithinAt.smul_const, smul_const
-/
theorem derivWithin_smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    derivWithin (fun y => c y • f) s x = derivWithin c s x • f := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.smul_const f).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `deriv_smul_const` / 定理 `deriv_smul_const`

English:
theorem deriv_smul_const
  given: (hc : DifferentiableAt 𝕜 c x) (f : F)
  proof: (hc.hasDerivAt.smul_const f).deriv

中文:
定理 deriv_smul_const
  条件: (hc : DifferentiableAt 𝕜 c x) (f : F)
  证明: (hc.hasDerivAt.smul_const f).deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.smul_const, smul_const
-/
theorem deriv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    deriv (fun y => c y • f) x = deriv c x • f :=
  (hc.hasDerivAt.smul_const f).deriv

end SMul

section ConstSMul

variable
  {R : Type*} [Monoid R] [DistribMulAction R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  -- TODO: all results involving `𝕝` would actually work for a `GroupWithZero` if we had a
  -- `DistribMulActionWithZero` typeclass
  {𝕝 : Type*} [DivisionSemiring 𝕝] [Module 𝕝 F] [SMulCommClass 𝕜 𝕝 F] [ContinuousConstSMul 𝕝 F]

@[to_fun]
/--
theorem `HasStrictDerivAt.const_smul` / 定理 `HasStrictDerivAt.const_smul`

English:
theorem HasStrictDerivAt.const_smul
  given: (c : R) (hf : HasStrictDerivAt f f' x)
  proof: by
  simpa using (HasStrictFDerivAt.const_smul hf c).hasStrictDerivAt

@[to_fun]

中文:
定理 HasStrictDerivAt.const_smul
  条件: (c : R) (hf : HasStrictDerivAt f f' x)
  证明: by
  simpa using (HasStrictFDerivAt.const_smul hf c).hasStrictDerivAt

@[to_fun]

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.const_smul, const_smul, hasStrictDerivAt
-/
theorem HasStrictDerivAt.const_smul (c : R) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (c • f) (c • f') x := by
  simpa using (HasStrictFDerivAt.const_smul hf c).hasStrictDerivAt

@[to_fun]
/--
theorem `HasDerivAtFilter.const_smul` / 定理 `HasDerivAtFilter.const_smul`

English:
theorem HasDerivAtFilter.const_smul
  given: (c : R) (hf : HasDerivAtFilter f f' L)
  proof: by
  simpa using (HasFDerivAtFilter.const_smul hf c).hasDerivAtFilter

@[to_fun]

中文:
定理 HasDerivAtFilter.const_smul
  条件: (c : R) (hf : HasDerivAtFilter f f' L)
  证明: by
  simpa using (HasFDerivAtFilter.const_smul hf c).hasDerivAtFilter

@[to_fun]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.const_smul, const_smul, hasDerivAtFilter
-/
theorem HasDerivAtFilter.const_smul (c : R) (hf : HasDerivAtFilter f f' L) :
    HasDerivAtFilter (c • f) (c • f') L := by
  simpa using (HasFDerivAtFilter.const_smul hf c).hasDerivAtFilter

@[to_fun]
/--
theorem `HasDerivWithinAt.const_smul` / 定理 `HasDerivWithinAt.const_smul`

English:
theorem HasDerivWithinAt.const_smul
  given: (c : R) (hf : HasDerivWithinAt f f' s x)
  proof: HasDerivAtFilter.const_smul c hf

@[to_fun]

中文:
定理 HasDerivWithinAt.const_smul
  条件: (c : R) (hf : HasDerivWithinAt f f' s x)
  证明: HasDerivAtFilter.const_smul c hf

@[to_fun]

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.const_smul, const_smul
-/
theorem HasDerivWithinAt.const_smul (c : R) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (c • f) (c • f') s x :=
  HasDerivAtFilter.const_smul c hf

@[to_fun]
/--
theorem `HasDerivAt.const_smul` / 定理 `HasDerivAt.const_smul`

English:
theorem HasDerivAt.const_smul
  given: (c : R) (hf : HasDerivAt f f' x)
  proof: HasDerivAtFilter.const_smul c hf

中文:
定理 在点处可导.const_smul
  条件: (c : R) (hf : 在点处可导 f f' x)
  证明: HasDerivAtFilter.const_smul c hf

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.const_smul, const_smul
-/
theorem HasDerivAt.const_smul (c : R) (hf : HasDerivAt f f' x) :
    HasDerivAt (c • f) (c • f') x :=
  HasDerivAtFilter.const_smul c hf

/--
theorem `derivWithin_fun_const_smul` / 定理 `derivWithin_fun_const_smul`

English:
theorem derivWithin_fun_const_smul
  given: (c : R) (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hf.hasDerivWithinAt.const_smul c).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_fun_const_smul
  条件: (c : R) (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hf.hasDerivWithinAt.const_smul c).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: UniqueDiffWithinAt, const_smul, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hf.hasDerivWithinAt.const_smul
-/
theorem derivWithin_fun_const_smul (c : R) (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (fun y => c • f y) s x = c • derivWithin f s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hf.hasDerivWithinAt.const_smul c).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `derivWithin_const_smul` / 定理 `derivWithin_const_smul`

English:
theorem derivWithin_const_smul
  given: (c : R) (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: derivWithin_fun_const_smul c hf

中文:
定理 derivWithin_const_smul
  条件: (c : R) (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: derivWithin_fun_const_smul c hf

Depends on / 依赖: derivWithin_fun_const_smul
-/
theorem derivWithin_const_smul (c : R) (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (c • f) s x = c • derivWithin f s x :=
  derivWithin_fun_const_smul c hf

/--
lemma `derivWithin_fun_const_smul_field` / 引理 `derivWithin_fun_const_smul_field`

English:
lemma derivWithin_fun_const_smul_field
  given: (c : 𝕝) (f : 𝕜 -> F)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · simp [← fderivWithin_derivWithin, ← Pi.smul_def, fderivWithin_const_smul_field c hsx]
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[deprecated (since := "2026-01-11")] alias derivWithin_fun_const_smul' :=
  derivWithin_fun_const_smul_fi

中文:
引理 derivWithin_fun_const_smul_field
  条件: (c : 𝕝) (f : 𝕜 -> F)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · simp [← fderivWithin_derivWithin, ← Pi.smul_def, fderivWithin_const_smul_field c hsx]
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[deprecated (since := "2026-01-11")] alias derivWithin_fun_const_smul' :=
  derivWithin_fun_const_smul_fi

Depends on / 依赖: Pi.smul_def, UniqueDiffWithinAt, derivWithin_zero_of_not_uniqueDiffWithinAt, fderivWithin_const_smul_field, fderivWithin_derivWithin, smul_def
-/
lemma derivWithin_fun_const_smul_field (c : 𝕝) (f : 𝕜 -> F) :
    derivWithin (fun y => c • f y) s x = c • derivWithin f s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · simp [← fderivWithin_derivWithin, ← Pi.smul_def, fderivWithin_const_smul_field c hsx]
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[deprecated (since := "2026-01-11")] alias derivWithin_fun_const_smul' :=
  derivWithin_fun_const_smul_field

/--
lemma `derivWithin_const_smul_field` / 引理 `derivWithin_const_smul_field`

English:
lemma derivWithin_const_smul_field
  given: (c : 𝕝) (f : 𝕜 -> F)
  proof: derivWithin_fun_const_smul_field c f

@[deprecated (since := "2026-01-11")] alias derivWithin_const_smul' :=
  derivWithin_const_smul_field

中文:
引理 derivWithin_const_smul_field
  条件: (c : 𝕝) (f : 𝕜 -> F)
  证明: derivWithin_fun_const_smul_field c f

@[deprecated (since := "2026-01-11")] alias derivWithin_const_smul' :=
  derivWithin_const_smul_field

Depends on / 依赖: derivWithin_fun_const_smul_field
-/
lemma derivWithin_const_smul_field (c : 𝕝) (f : 𝕜 -> F) :
    derivWithin (c • f) s x = c • derivWithin f s x :=
  derivWithin_fun_const_smul_field c f

@[deprecated (since := "2026-01-11")] alias derivWithin_const_smul' :=
  derivWithin_const_smul_field

/--
theorem `deriv_fun_const_smul` / 定理 `deriv_fun_const_smul`

English:
theorem deriv_fun_const_smul
  given: (c : R) (hf : DifferentiableAt 𝕜 f x)
  proof: (hf.hasDerivAt.const_smul c).deriv

中文:
定理 deriv_fun_const_smul
  条件: (c : R) (hf : DifferentiableAt 𝕜 f x)
  证明: (hf.hasDerivAt.const_smul c).deriv

Depends on / 依赖: const_smul, hasDerivAt, hf.hasDerivAt.const_smul
-/
theorem deriv_fun_const_smul (c : R) (hf : DifferentiableAt 𝕜 f x) :
    deriv (fun y => c • f y) x = c • deriv f x :=
  (hf.hasDerivAt.const_smul c).deriv

/--
theorem `deriv_const_smul` / 定理 `deriv_const_smul`

English:
theorem deriv_const_smul
  given: (c : R) (hf : DifferentiableAt 𝕜 f x)
  proof: (hf.hasDerivAt.const_smul c).deriv

中文:
定理 deriv_const_smul
  条件: (c : R) (hf : DifferentiableAt 𝕜 f x)
  证明: (hf.hasDerivAt.const_smul c).deriv

Depends on / 依赖: const_smul, hasDerivAt, hf.hasDerivAt.const_smul
-/
theorem deriv_const_smul (c : R) (hf : DifferentiableAt 𝕜 f x) :
    deriv (c • f) x = c • deriv f x :=
  (hf.hasDerivAt.const_smul c).deriv

/--
lemma `deriv_fun_const_smul_field` / 引理 `deriv_fun_const_smul_field`

English:
lemma deriv_fun_const_smul_field
  given: (c : 𝕝) (f : 𝕜 -> F)
  proof: by
  simp only [← derivWithin_univ, derivWithin_fun_const_smul_field]

@[deprecated (since := "2026-01-11")] alias deriv_fun_const_smul' := deriv_fun_const_smul_field

中文:
引理 deriv_fun_const_smul_field
  条件: (c : 𝕝) (f : 𝕜 -> F)
  证明: by
  simp only [← derivWithin_univ, derivWithin_fun_const_smul_field]

@[deprecated (since := "2026-01-11")] alias deriv_fun_const_smul' := deriv_fun_const_smul_field

Depends on / 依赖: derivWithin_fun_const_smul_field, derivWithin_univ
-/
lemma deriv_fun_const_smul_field (c : 𝕝) (f : 𝕜 -> F) :
    deriv (fun y => c • f y) x = c • deriv f x := by
  simp only [← derivWithin_univ, derivWithin_fun_const_smul_field]

@[deprecated (since := "2026-01-11")] alias deriv_fun_const_smul' := deriv_fun_const_smul_field

/--
lemma `deriv_const_smul_field` / 引理 `deriv_const_smul_field`

English:
lemma deriv_const_smul_field
  given: (c : 𝕝) (f : 𝕜 -> F)
  proof: by
  simp only [← derivWithin_univ, derivWithin_const_smul_field]

@[deprecated (since := "2026-01-11")] alias deriv_const_smul' := deriv_const_smul_field

中文:
引理 deriv_const_smul_field
  条件: (c : 𝕝) (f : 𝕜 -> F)
  证明: by
  simp only [← derivWithin_univ, derivWithin_const_smul_field]

@[deprecated (since := "2026-01-11")] alias deriv_const_smul' := deriv_const_smul_field

Depends on / 依赖: derivWithin_const_smul_field, derivWithin_univ
-/
lemma deriv_const_smul_field (c : 𝕝) (f : 𝕜 -> F) :
    deriv (c • f) x = c • deriv f x := by
  simp only [← derivWithin_univ, derivWithin_const_smul_field]

@[deprecated (since := "2026-01-11")] alias deriv_const_smul' := deriv_const_smul_field

end ConstSMul

section Mul

/-! ### Derivative of the multiplication of two functions -/


variable {𝕜' 𝔸 : Type*} [NormedDivisionRing 𝕜'] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝕜']
  [NormedAlgebra 𝕜 𝔸] {c d : 𝕜 -> 𝔸} {c' d' : 𝔸} {u v : 𝕜 -> 𝕜'}

@[to_fun]
/--
theorem `HasDerivWithinAt.mul` / 定理 `HasDerivWithinAt.mul`

English:
theorem HasDerivWithinAt.mul
  given: (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
  proof: by
  simpa [add_comm] using (HasFDerivWithinAt.mul' hc hd).hasDerivWithinAt

@[to_fun]

中文:
定理 HasDerivWithinAt.mul
  条件: (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
  证明: by
  simpa [add_comm] using (HasFDerivWithinAt.mul' hc hd).hasDerivWithinAt

@[to_fun]

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.mul, add_comm, hasDerivWithinAt
-/
theorem HasDerivWithinAt.mul (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (c * d) (c' * d x + c x * d') s x := by
  simpa [add_comm] using (HasFDerivWithinAt.mul' hc hd).hasDerivWithinAt

@[to_fun]
/--
theorem `HasDerivAt.mul` / 定理 `HasDerivAt.mul`

English:
theorem HasDerivAt.mul
  given: (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x)
  proof: by
  rw [← hasDerivWithinAt_univ] at *
  exact HasDerivWithinAt.mul hc hd

@[to_fun]

中文:
定理 在点处可导.mul
  条件: (hc : 在点处可导 c c' x) (hd : 在点处可导 d d' x)
  证明: by
  rw [← hasDerivWithinAt_univ] at *
  exact HasDerivWithinAt.mul hc hd

@[to_fun]

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.mul, hasDerivWithinAt_univ
-/
theorem HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (c * d) (c' * d x + c x * d') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact HasDerivWithinAt.mul hc hd

@[to_fun]
/--
theorem `HasStrictDerivAt.mul` / 定理 `HasStrictDerivAt.mul`

English:
theorem HasStrictDerivAt.mul
  given: (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
  proof: by
  simpa [add_comm] using (HasStrictFDerivAt.mul' hc hd).hasStrictDerivAt

中文:
定理 HasStrictDerivAt.mul
  条件: (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
  证明: by
  simpa [add_comm] using (HasStrictFDerivAt.mul' hc hd).hasStrictDerivAt

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.mul, add_comm, hasStrictDerivAt
-/
theorem HasStrictDerivAt.mul (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (c * d) (c' * d x + c x * d') x := by
  simpa [add_comm] using (HasStrictFDerivAt.mul' hc hd).hasStrictDerivAt

/--
theorem `derivWithin_fun_mul` / 定理 `derivWithin_fun_mul`

English:
theorem derivWithin_fun_mul
  statement: (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.mul hd.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_fun_mul
  结论: (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.mul hd.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hc.hasDerivWithinAt.mul, hd.hasDerivWithinAt
-/
theorem derivWithin_fun_mul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => c y * d y) s x = derivWithin c s x * d x + c x * derivWithin d s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.mul hd.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `derivWithin_mul` / 定理 `derivWithin_mul`

English:
theorem derivWithin_mul
  statement: (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: derivWithin_fun_mul hc hd

@[simp]

中文:
定理 derivWithin_mul
  结论: (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: derivWithin_fun_mul hc hd

@[simp]

Depends on / 依赖: derivWithin_fun_mul
-/
theorem derivWithin_mul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (c * d) s x = derivWithin c s x * d x + c x * derivWithin d s x :=
  derivWithin_fun_mul hc hd

@[simp]
/--
theorem `deriv_fun_mul` / 定理 `deriv_fun_mul`

English:
theorem deriv_fun_mul
  given: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  proof: (hc.hasDerivAt.mul hd.hasDerivAt).deriv

@[simp]

中文:
定理 deriv_fun_mul
  条件: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  证明: (hc.hasDerivAt.mul hd.hasDerivAt).deriv

@[simp]

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.mul, hd.hasDerivAt
-/
theorem deriv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv d x :=
  (hc.hasDerivAt.mul hd.hasDerivAt).deriv

@[simp]
/--
theorem `deriv_mul` / 定理 `deriv_mul`

English:
theorem deriv_mul
  given: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  proof: (hc.hasDerivAt.mul hd.hasDerivAt).deriv

中文:
定理 deriv_mul
  条件: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  证明: (hc.hasDerivAt.mul hd.hasDerivAt).deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.mul, hd.hasDerivAt
-/
theorem deriv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (c * d) x = deriv c x * d x + c x * deriv d x :=
  (hc.hasDerivAt.mul hd.hasDerivAt).deriv

/--
theorem `HasDerivWithinAt.mul_const` / 定理 `HasDerivWithinAt.mul_const`

English:
theorem HasDerivWithinAt.mul_const
  given: (hc : HasDerivWithinAt c c' s x) (d : 𝔸)
  proof: by
  convert! hc.mul (hasDerivWithinAt_const x s d) using 1
  rw [mul_zero]; rw [add_zero]

中文:
定理 HasDerivWithinAt.mul_const
  条件: (hc : HasDerivWithinAt c c' s x) (d : 𝔸)
  证明: by
  convert! hc.mul (hasDerivWithinAt_const x s d) using 1
  rw [mul_zero]; rw [add_zero]

Depends on / 依赖: add_zero, convert, hasDerivWithinAt_const, hc.mul, mul_zero
-/
theorem HasDerivWithinAt.mul_const (hc : HasDerivWithinAt c c' s x) (d : 𝔸) :
    HasDerivWithinAt (fun y => c y * d) (c' * d) s x := by
  convert! hc.mul (hasDerivWithinAt_const x s d) using 1
  rw [mul_zero]; rw [add_zero]

/--
theorem `HasDerivAt.mul_const` / 定理 `HasDerivAt.mul_const`

English:
theorem HasDerivAt.mul_const
  given: (hc : HasDerivAt c c' x) (d : 𝔸)
  proof: by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.mul_const d

中文:
定理 在点处可导.mul_const
  条件: (hc : 在点处可导 c c' x) (d : 𝔸)
  证明: by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.mul_const d

Depends on / 依赖: hasDerivWithinAt_univ, hc.mul_const, mul_const
-/
theorem HasDerivAt.mul_const (hc : HasDerivAt c c' x) (d : 𝔸) :
    HasDerivAt (fun y => c y * d) (c' * d) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.mul_const d

/--
theorem `hasDerivAt_mul_const` / 定理 `hasDerivAt_mul_const`

English:
theorem hasDerivAt_mul_const
  given: (c : 𝕜)
  statement: HasDerivAt (fun x => x * c) c x
  proof: by
  simpa only [one_mul] using (hasDerivAt_id' x).mul_const c

中文:
定理 hasDerivAt_mul_const
  条件: (c : 𝕜)
  结论: 在点处可导 (fun x => x * c) c x
  证明: by
  simpa only [one_mul] using (hasDerivAt_id' x).mul_const c

Depends on / 依赖: hasDerivAt_id, mul_const, one_mul
-/
theorem hasDerivAt_mul_const (c : 𝕜) : HasDerivAt (fun x => x * c) c x := by
  simpa only [one_mul] using (hasDerivAt_id' x).mul_const c

/--
theorem `HasStrictDerivAt.mul_const` / 定理 `HasStrictDerivAt.mul_const`

English:
theorem HasStrictDerivAt.mul_const
  given: (hc : HasStrictDerivAt c c' x) (d : 𝔸)
  proof: by
  convert! hc.mul (hasStrictDerivAt_const x d) using 1
  rw [mul_zero]; rw [add_zero]

中文:
定理 HasStrictDerivAt.mul_const
  条件: (hc : HasStrictDerivAt c c' x) (d : 𝔸)
  证明: by
  convert! hc.mul (hasStrictDerivAt_const x d) using 1
  rw [mul_zero]; rw [add_zero]

Depends on / 依赖: add_zero, convert, hasStrictDerivAt_const, hc.mul, mul_zero
-/
theorem HasStrictDerivAt.mul_const (hc : HasStrictDerivAt c c' x) (d : 𝔸) :
    HasStrictDerivAt (fun y => c y * d) (c' * d) x := by
  convert! hc.mul (hasStrictDerivAt_const x d) using 1
  rw [mul_zero]; rw [add_zero]

/--
theorem `derivWithin_mul_const` / 定理 `derivWithin_mul_const`

English:
theorem derivWithin_mul_const
  given: (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.mul_const d).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_mul_const
  条件: (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.mul_const d).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hc.hasDerivWithinAt.mul_const, mul_const
-/
theorem derivWithin_mul_const (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸) :
    derivWithin (fun y => c y * d) s x = derivWithin c s x * d := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.mul_const d).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
lemma `derivWithin_mul_const_field` / 引理 `derivWithin_mul_const_field`

English:
lemma derivWithin_mul_const_field
  given: (u : 𝕜')
  proof: by
  by_cases hv : DifferentiableWithinAt 𝕜 v s x
  · rw [derivWithin_mul_const hv u]
  by_cases hu : u = 0
  · simp [hu]
  rw [derivWithin_zero_of_not_differentiableWithinAt hv]; rw [zero_mul]; rw [derivWithin_zero_of_not_differentiableWithinAt]
  have : v = fun x => (v x * u) * u⁻¹ := by ext; simp

中文:
引理 derivWithin_mul_const_field
  条件: (u : 𝕜')
  证明: by
  by_cases hv : DifferentiableWithinAt 𝕜 v s x
  · rw [derivWithin_mul_const hv u]
  by_cases hu : u = 0
  · simp [hu]
  rw [derivWithin_zero_of_not_differentiableWithinAt hv]; rw [zero_mul]; rw [derivWithin_zero_of_not_differentiableWithinAt]
  have : v = fun x => (v x * u) * u⁻¹ := by ext; simp

Depends on / 依赖: DifferentiableWithinAt, derivWithin_mul_const, derivWithin_zero_of_not_differentiableWithinAt, h_diff, h_diff.mul_const, mul_const, zero_mul
-/
lemma derivWithin_mul_const_field (u : 𝕜') :
    derivWithin (fun y => v y * u) s x = derivWithin v s x * u := by
  by_cases hv : DifferentiableWithinAt 𝕜 v s x
  · rw [derivWithin_mul_const hv u]
  by_cases hu : u = 0
  · simp [hu]
  rw [derivWithin_zero_of_not_differentiableWithinAt hv]; rw [zero_mul]; rw [derivWithin_zero_of_not_differentiableWithinAt]
  have : v = fun x => (v x * u) * u⁻¹ := by ext; simp [hu]
exact fun h_diff => hv this ▸ h_diff.mul_const _

/--
theorem `deriv_mul_const` / 定理 `deriv_mul_const`

English:
theorem deriv_mul_const
  given: (hc : DifferentiableAt 𝕜 c x) (d : 𝔸)
  proof: (hc.hasDerivAt.mul_const d).deriv

中文:
定理 deriv_mul_const
  条件: (hc : DifferentiableAt 𝕜 c x) (d : 𝔸)
  证明: (hc.hasDerivAt.mul_const d).deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.mul_const, mul_const
-/
theorem deriv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸) :
    deriv (fun y => c y * d) x = deriv c x * d :=
  (hc.hasDerivAt.mul_const d).deriv

/--
theorem `deriv_mul_const_field` / 定理 `deriv_mul_const_field`

English:
theorem deriv_mul_const_field
  given: (v : 𝕜')
  statement: deriv (fun y => u y * v) x = deriv u x * v
  proof: by
  by_cases hu : DifferentiableAt 𝕜 u x
  · exact deriv_mul_const hu v
  · rw [deriv_zero_of_not_differentiableAt hu, zero_mul]
    rcases eq_or_ne v 0 with (rfl | hd)
    · simp only [mul_zero, deriv_const]
    · refine deriv_zero_of_not_differentiableAt (mt (fun H => ?_) hu)
      simpa only [mu

中文:
定理 deriv_mul_const_field
  条件: (v : 𝕜')
  结论: deriv (fun y => u y * v) x = deriv u x * v
  证明: by
  by_cases hu : DifferentiableAt 𝕜 u x
  · exact deriv_mul_const hu v
  · rw [deriv_zero_of_not_differentiableAt hu, zero_mul]
    rcases eq_or_ne v 0 with (rfl | hd)
    · simp only [mul_zero, deriv_const]
    · refine deriv_zero_of_not_differentiableAt (mt (fun H => ?_) hu)
      simpa only [mu

Depends on / 依赖: DifferentiableAt, H.mul_const, deriv_const, deriv_mul_const, deriv_zero_of_not_differentiableAt, eq_or_ne, mul_const, mul_zero, zero_mul
-/
theorem deriv_mul_const_field (v : 𝕜') : deriv (fun y => u y * v) x = deriv u x * v := by
  by_cases hu : DifferentiableAt 𝕜 u x
  · exact deriv_mul_const hu v
  · rw [deriv_zero_of_not_differentiableAt hu, zero_mul]
    rcases eq_or_ne v 0 with (rfl | hd)
    · simp only [mul_zero, deriv_const]
    · refine deriv_zero_of_not_differentiableAt (mt (fun H => ?_) hu)
      simpa only [mul_inv_cancel_right₀ hd] using H.mul_const v⁻¹

@[simp]
/--
theorem `deriv_mul_const_field'` / 定理 `deriv_mul_const_field'`

English:
theorem deriv_mul_const_field'
  given: (v : 𝕜')
  statement: (deriv fun x => u x * v) = fun x => deriv u x * v
  proof: funext fun _ => deriv_mul_const_field v

中文:
定理 deriv_mul_const_field'
  条件: (v : 𝕜')
  结论: (deriv fun x => u x * v) = fun x => deriv u x * v
  证明: funext fun _ => deriv_mul_const_field v

Depends on / 依赖: deriv_mul_const_field
-/
theorem deriv_mul_const_field' (v : 𝕜') : (deriv fun x => u x * v) = fun x => deriv u x * v :=
  funext fun _ => deriv_mul_const_field v

/--
theorem `HasDerivWithinAt.const_mul` / 定理 `HasDerivWithinAt.const_mul`

English:
theorem HasDerivWithinAt.const_mul
  given: (c : 𝔸) (hd : HasDerivWithinAt d d' s x)
  proof: by
  convert! (hasDerivWithinAt_const x s c).mul hd using 1
  rw [zero_mul]; rw [zero_add]

中文:
定理 HasDerivWithinAt.const_mul
  条件: (c : 𝔸) (hd : HasDerivWithinAt d d' s x)
  证明: by
  convert! (hasDerivWithinAt_const x s c).mul hd using 1
  rw [zero_mul]; rw [zero_add]

Depends on / 依赖: convert, hasDerivWithinAt_const, zero_add, zero_mul
-/
theorem HasDerivWithinAt.const_mul (c : 𝔸) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => c * d y) (c * d') s x := by
  convert! (hasDerivWithinAt_const x s c).mul hd using 1
  rw [zero_mul]; rw [zero_add]

/--
theorem `HasDerivAt.const_mul` / 定理 `HasDerivAt.const_mul`

English:
theorem HasDerivAt.const_mul
  given: (c : 𝔸) (hd : HasDerivAt d d' x)
  proof: by
  rw [← hasDerivWithinAt_univ] at *
  exact hd.const_mul c

中文:
定理 在点处可导.const_mul
  条件: (c : 𝔸) (hd : 在点处可导 d d' x)
  证明: by
  rw [← hasDerivWithinAt_univ] at *
  exact hd.const_mul c

Depends on / 依赖: const_mul, hasDerivWithinAt_univ, hd.const_mul
-/
theorem HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => c * d y) (c * d') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hd.const_mul c

/--
theorem `hasDerivAt_const_mul` / 定理 `hasDerivAt_const_mul`

English:
theorem hasDerivAt_const_mul
  given: (c : 𝕜)
  statement: HasDerivAt (fun y => c * y) c x
  proof: by
  simpa only [mul_one] using (hasDerivAt_id' x).const_mul c

中文:
定理 hasDerivAt_const_mul
  条件: (c : 𝕜)
  结论: 在点处可导 (fun y => c * y) c x
  证明: by
  simpa only [mul_one] using (hasDerivAt_id' x).const_mul c

Depends on / 依赖: const_mul, hasDerivAt_id, mul_one
-/
theorem hasDerivAt_const_mul (c : 𝕜) : HasDerivAt (fun y => c * y) c x := by
  simpa only [mul_one] using (hasDerivAt_id' x).const_mul c

/--
theorem `HasStrictDerivAt.const_mul` / 定理 `HasStrictDerivAt.const_mul`

English:
theorem HasStrictDerivAt.const_mul
  given: (c : 𝔸) (hd : HasStrictDerivAt d d' x)
  proof: by
  convert! (hasStrictDerivAt_const _ _).mul hd using 1
  rw [zero_mul]; rw [zero_add]

中文:
定理 HasStrictDerivAt.const_mul
  条件: (c : 𝔸) (hd : HasStrictDerivAt d d' x)
  证明: by
  convert! (hasStrictDerivAt_const _ _).mul hd using 1
  rw [zero_mul]; rw [zero_add]

Depends on / 依赖: convert, hasStrictDerivAt_const, zero_add, zero_mul
-/
theorem HasStrictDerivAt.const_mul (c : 𝔸) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c * d y) (c * d') x := by
  convert! (hasStrictDerivAt_const _ _).mul hd using 1
  rw [zero_mul]; rw [zero_add]

/--
theorem `derivWithin_const_mul` / 定理 `derivWithin_const_mul`

English:
theorem derivWithin_const_mul
  given: (c : 𝔸) (hd : DifferentiableWithinAt 𝕜 d s x)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hd.hasDerivWithinAt.const_mul c).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_const_mul
  条件: (c : 𝔸) (hd : DifferentiableWithinAt 𝕜 d s x)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hd.hasDerivWithinAt.const_mul c).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: UniqueDiffWithinAt, const_mul, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hd.hasDerivWithinAt.const_mul
-/
theorem derivWithin_const_mul (c : 𝔸) (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => c * d y) s x = c * derivWithin d s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hd.hasDerivWithinAt.const_mul c).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
lemma `derivWithin_const_mul_field` / 引理 `derivWithin_const_mul_field`

English:
lemma derivWithin_const_mul_field
  given: (u : 𝕜')
  proof: by
  apply derivWithin_const_smul_field (c := u)

中文:
引理 derivWithin_const_mul_field
  条件: (u : 𝕜')
  证明: by
  apply derivWithin_const_smul_field (c := u)

Depends on / 依赖: derivWithin_const_smul_field
-/
lemma derivWithin_const_mul_field (u : 𝕜') :
    derivWithin (fun y => u * v y) s x = u * derivWithin v s x := by
  apply derivWithin_const_smul_field (c := u)

/--
theorem `deriv_const_mul` / 定理 `deriv_const_mul`

English:
theorem deriv_const_mul
  given: (c : 𝔸) (hd : DifferentiableAt 𝕜 d x)
  proof: (hd.hasDerivAt.const_mul c).deriv

中文:
定理 deriv_const_mul
  条件: (c : 𝔸) (hd : DifferentiableAt 𝕜 d x)
  证明: (hd.hasDerivAt.const_mul c).deriv

Depends on / 依赖: const_mul, hasDerivAt, hd.hasDerivAt.const_mul
-/
theorem deriv_const_mul (c : 𝔸) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => c * d y) x = c * deriv d x :=
  (hd.hasDerivAt.const_mul c).deriv

/--
theorem `deriv_const_mul_field` / 定理 `deriv_const_mul_field`

English:
theorem deriv_const_mul_field
  given: (u : 𝕜')
  statement: deriv (fun y => u * v y) x = u * deriv v x
  proof: by
  simpa only [← derivWithin_univ] using derivWithin_const_mul_field u

@[simp]

中文:
定理 deriv_const_mul_field
  条件: (u : 𝕜')
  结论: deriv (fun y => u * v y) x = u * deriv v x
  证明: by
  simpa only [← derivWithin_univ] using derivWithin_const_mul_field u

@[simp]

Depends on / 依赖: derivWithin_const_mul_field, derivWithin_univ
-/
theorem deriv_const_mul_field (u : 𝕜') : deriv (fun y => u * v y) x = u * deriv v x := by
  simpa only [← derivWithin_univ] using derivWithin_const_mul_field u

@[simp]
/--
theorem `deriv_const_mul_field'` / 定理 `deriv_const_mul_field'`

English:
theorem deriv_const_mul_field'
  given: (u : 𝕜')
  statement: (deriv fun x => u * v x) = fun x => u * deriv v x
  proof: funext fun _ => deriv_const_mul_field u

中文:
定理 deriv_const_mul_field'
  条件: (u : 𝕜')
  结论: (deriv fun x => u * v x) = fun x => u * deriv v x
  证明: funext fun _ => deriv_const_mul_field u

Depends on / 依赖: deriv_const_mul_field
-/
theorem deriv_const_mul_field' (u : 𝕜') : (deriv fun x => u * v x) = fun x => u * deriv v x :=
  funext fun _ => deriv_const_mul_field u

/--
theorem `deriv_const_mul_id` / 定理 `deriv_const_mul_id`

English:
theorem deriv_const_mul_id
  given: (c : 𝕜)
  statement: deriv (fun y => c * y) x = c
  proof: by
  simp only [deriv_const_mul c differentiableAt_fun_id, deriv_id'', mul_one]

@[simp]

中文:
定理 deriv_const_mul_id
  条件: (c : 𝕜)
  结论: deriv (fun y => c * y) x = c
  证明: by
  simp only [deriv_const_mul c differentiableAt_fun_id, deriv_id'', mul_one]

@[simp]

Depends on / 依赖: deriv_const_mul, deriv_id, differentiableAt_fun_id, mul_one
-/
theorem deriv_const_mul_id (c : 𝕜) : deriv (fun y => c * y) x = c := by
  simp only [deriv_const_mul c differentiableAt_fun_id, deriv_id'', mul_one]

@[simp]
/--
theorem `deriv_const_mul_id'` / 定理 `deriv_const_mul_id'`

English:
theorem deriv_const_mul_id'
  given: (c : 𝕜)
  statement: deriv (fun x => c * x) = fun _ => c
  proof: funext fun _ => by simp only [deriv_const_mul_id]

中文:
定理 deriv_const_mul_id'
  条件: (c : 𝕜)
  结论: deriv (fun x => c * x) = fun _ => c
  证明: funext fun _ => by simp only [deriv_const_mul_id]

Depends on / 依赖: deriv_const_mul_id
-/
theorem deriv_const_mul_id' (c : 𝕜) : deriv (fun x => c * x) = fun _ => c :=
  funext fun _ => by simp only [deriv_const_mul_id]

end Mul

section Prod

section HasDeriv

variable {ι : Type*} [DecidableEq ι] {𝔸' : Type*} [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸']
  {u : Finset ι} {f : ι -> 𝕜 -> 𝔸'} {f' : ι -> 𝔸'}

/--
theorem `HasDerivAt.fun_finsetProd` / 定理 `HasDerivAt.fun_finsetProd`

English:
theorem HasDerivAt.fun_finsetProd
  given: (hf : forall i in u, HasDerivAt (f i) (f' i) x)
  proof: by
  simpa using (HasFDerivAt.finsetProd (hf · · |> hasFDerivAt)).hasDerivAt

@[deprecated (since := "2026-04-08")] alias HasDerivAt.fun_finset_prod := HasDerivAt.fun_finsetProd

中文:
定理 在点处可导.fun_finsetProd
  条件: (hf : 对任意 i in u, 在点处可导 (f i) (f' i) x)
  证明: by
  simpa using (HasFDerivAt.finsetProd (hf · · |> hasFDerivAt)).hasDerivAt

@[deprecated (since := "2026-04-08")] alias HasDerivAt.fun_finset_prod := HasDerivAt.fun_finsetProd

Depends on / 依赖: HasFDerivAt, HasFDerivAt.finsetProd, finsetProd, hasDerivAt, hasFDerivAt
-/
theorem HasDerivAt.fun_finsetProd (hf : forall i in u, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u.erase i, f j x) • f' i) x := by
  simpa using (HasFDerivAt.finsetProd (hf · · |> hasFDerivAt)).hasDerivAt

@[deprecated (since := "2026-04-08")] alias HasDerivAt.fun_finset_prod := HasDerivAt.fun_finsetProd

/--
theorem `HasDerivAt.finsetProd` / 定理 `HasDerivAt.finsetProd`

English:
theorem HasDerivAt.finsetProd
  given: (hf : forall i in u, HasDerivAt (f i) (f' i) x)
  proof: by
  convert! HasDerivAt.fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")] alias HasDerivAt.finset_prod := HasDerivAt.finsetProd

中文:
定理 在点处可导.finsetProd
  条件: (hf : 对任意 i in u, 在点处可导 (f i) (f' i) x)
  证明: by
  convert! HasDerivAt.fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")] alias HasDerivAt.finset_prod := HasDerivAt.finsetProd

Depends on / 依赖: HasDerivAt, HasDerivAt.fun_finsetProd, convert, fun_finsetProd
-/
theorem HasDerivAt.finsetProd (hf : forall i in u, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (∏ i in u, f i) (∑ i in u, (∏ j in u.erase i, f j x) • f' i) x := by
  convert! HasDerivAt.fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")] alias HasDerivAt.finset_prod := HasDerivAt.finsetProd

/--
theorem `HasDerivWithinAt.fun_finsetProd` / 定理 `HasDerivWithinAt.fun_finsetProd`

English:
theorem HasDerivWithinAt.fun_finsetProd
  given: (hf : forall i in u, HasDerivWithinAt (f i) (f' i) s x)
  proof: by
  simpa using (HasFDerivWithinAt.finsetProd (hf · · |> hasFDerivWithinAt)).hasDerivWithinAt

@[deprecated (since := "2026-04-08")]
alias HasDerivWithinAt.fun_finset_prod := HasDerivWithinAt.fun_finsetProd

中文:
定理 HasDerivWithinAt.fun_finsetProd
  条件: (hf : 对任意 i in u, HasDerivWithinAt (f i) (f' i) s x)
  证明: by
  simpa using (HasFDerivWithinAt.finsetProd (hf · · |> hasFDerivWithinAt)).hasDerivWithinAt

@[deprecated (since := "2026-04-08")]
alias HasDerivWithinAt.fun_finset_prod := HasDerivWithinAt.fun_finsetProd

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.finsetProd, finsetProd, hasDerivWithinAt, hasFDerivWithinAt
-/
theorem HasDerivWithinAt.fun_finsetProd (hf : forall i in u, HasDerivWithinAt (f i) (f' i) s x) :
    HasDerivWithinAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u.erase i, f j x) • f' i) s x := by
  simpa using (HasFDerivWithinAt.finsetProd (hf · · |> hasFDerivWithinAt)).hasDerivWithinAt

@[deprecated (since := "2026-04-08")]
alias HasDerivWithinAt.fun_finset_prod := HasDerivWithinAt.fun_finsetProd

/--
theorem `HasDerivWithinAt.finsetProd` / 定理 `HasDerivWithinAt.finsetProd`

English:
theorem HasDerivWithinAt.finsetProd
  given: (hf : forall i in u, HasDerivWithinAt (f i) (f' i) s x)
  proof: by
  convert! HasDerivWithinAt.fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")]
alias HasDerivWithinAt.finset_prod := HasDerivWithinAt.finsetProd

中文:
定理 HasDerivWithinAt.finsetProd
  条件: (hf : 对任意 i in u, HasDerivWithinAt (f i) (f' i) s x)
  证明: by
  convert! HasDerivWithinAt.fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")]
alias HasDerivWithinAt.finset_prod := HasDerivWithinAt.finsetProd

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.fun_finsetProd, convert, fun_finsetProd
-/
theorem HasDerivWithinAt.finsetProd (hf : forall i in u, HasDerivWithinAt (f i) (f' i) s x) :
    HasDerivWithinAt (∏ i in u, f i) (∑ i in u, (∏ j in u.erase i, f j x) • f' i) s x := by
  convert! HasDerivWithinAt.fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")]
alias HasDerivWithinAt.finset_prod := HasDerivWithinAt.finsetProd

/--
theorem `HasStrictDerivAt.fun_finsetProd` / 定理 `HasStrictDerivAt.fun_finsetProd`

English:
theorem HasStrictDerivAt.fun_finsetProd
  given: (hf : forall i in u, HasStrictDerivAt (f i) (f' i) x)
  proof: by
  simpa using (HasStrictFDerivAt.finsetProd (hf · · |> hasStrictFDerivAt)).hasStrictDerivAt

@[deprecated (since := "2026-04-08")]
alias HasStrictDerivAt.fun_finset_prod := HasStrictDerivAt.fun_finsetProd

中文:
定理 HasStrictDerivAt.fun_finsetProd
  条件: (hf : 对任意 i in u, HasStrictDerivAt (f i) (f' i) x)
  证明: by
  simpa using (HasStrictFDerivAt.finsetProd (hf · · |> hasStrictFDerivAt)).hasStrictDerivAt

@[deprecated (since := "2026-04-08")]
alias HasStrictDerivAt.fun_finset_prod := HasStrictDerivAt.fun_finsetProd

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.finsetProd, finsetProd, hasStrictDerivAt, hasStrictFDerivAt
-/
theorem HasStrictDerivAt.fun_finsetProd (hf : forall i in u, HasStrictDerivAt (f i) (f' i) x) :
    HasStrictDerivAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u.erase i, f j x) • f' i) x := by
  simpa using (HasStrictFDerivAt.finsetProd (hf · · |> hasStrictFDerivAt)).hasStrictDerivAt

@[deprecated (since := "2026-04-08")]
alias HasStrictDerivAt.fun_finset_prod := HasStrictDerivAt.fun_finsetProd

/--
theorem `HasStrictDerivAt.finsetProd` / 定理 `HasStrictDerivAt.finsetProd`

English:
theorem HasStrictDerivAt.finsetProd
  given: (hf : forall i in u, HasStrictDerivAt (f i) (f' i) x)
  proof: by
  convert! HasStrictDerivAt.fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")]
alias HasStrictDerivAt.finset_prod := HasStrictDerivAt.finsetProd

中文:
定理 HasStrictDerivAt.finsetProd
  条件: (hf : 对任意 i in u, HasStrictDerivAt (f i) (f' i) x)
  证明: by
  convert! HasStrictDerivAt.fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")]
alias HasStrictDerivAt.finset_prod := HasStrictDerivAt.finsetProd

Depends on / 依赖: HasStrictDerivAt, HasStrictDerivAt.fun_finsetProd, convert, fun_finsetProd
-/
theorem HasStrictDerivAt.finsetProd (hf : forall i in u, HasStrictDerivAt (f i) (f' i) x) :
    HasStrictDerivAt (∏ i in u, f i) (∑ i in u, (∏ j in u.erase i, f j x) • f' i) x := by
  convert! HasStrictDerivAt.fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")]
alias HasStrictDerivAt.finset_prod := HasStrictDerivAt.finsetProd

/--
theorem `deriv_fun_finsetProd` / 定理 `deriv_fun_finsetProd`

English:
theorem deriv_fun_finsetProd
  given: (hf : forall i in u, DifferentiableAt 𝕜 (f i) x)
  proof: (HasDerivAt.fun_finsetProd fun i hi => (hf i hi).hasDerivAt).deriv

@[deprecated (since := "2026-04-08")] alias deriv_fun_finset_prod := deriv_fun_finsetProd

中文:
定理 deriv_fun_finsetProd
  条件: (hf : 对任意 i in u, DifferentiableAt 𝕜 (f i) x)
  证明: (HasDerivAt.fun_finsetProd fun i hi => (hf i hi).hasDerivAt).deriv

@[deprecated (since := "2026-04-08")] alias deriv_fun_finset_prod := deriv_fun_finsetProd

Depends on / 依赖: HasDerivAt, HasDerivAt.fun_finsetProd, fun_finsetProd, hasDerivAt
-/
theorem deriv_fun_finsetProd (hf : forall i in u, DifferentiableAt 𝕜 (f i) x) :
    deriv (∏ i in u, f i ·) x = ∑ i in u, (∏ j in u.erase i, f j x) • deriv (f i) x :=
  (HasDerivAt.fun_finsetProd fun i hi => (hf i hi).hasDerivAt).deriv

@[deprecated (since := "2026-04-08")] alias deriv_fun_finset_prod := deriv_fun_finsetProd

/--
theorem `deriv_finsetProd` / 定理 `deriv_finsetProd`

English:
theorem deriv_finsetProd
  given: (hf : forall i in u, DifferentiableAt 𝕜 (f i) x)
  proof: (HasDerivAt.finsetProd fun i hi => (hf i hi).hasDerivAt).deriv

@[deprecated (since := "2026-04-08")] alias deriv_finset_prod := deriv_finsetProd

中文:
定理 deriv_finsetProd
  条件: (hf : 对任意 i in u, DifferentiableAt 𝕜 (f i) x)
  证明: (HasDerivAt.finsetProd fun i hi => (hf i hi).hasDerivAt).deriv

@[deprecated (since := "2026-04-08")] alias deriv_finset_prod := deriv_finsetProd

Depends on / 依赖: HasDerivAt, HasDerivAt.finsetProd, finsetProd, hasDerivAt
-/
theorem deriv_finsetProd (hf : forall i in u, DifferentiableAt 𝕜 (f i) x) :
    deriv (∏ i in u, f i) x = ∑ i in u, (∏ j in u.erase i, f j x) • deriv (f i) x :=
  (HasDerivAt.finsetProd fun i hi => (hf i hi).hasDerivAt).deriv

@[deprecated (since := "2026-04-08")] alias deriv_finset_prod := deriv_finsetProd

/--
theorem `derivWithin_fun_finsetProd` / 定理 `derivWithin_fun_finsetProd`

English:
theorem derivWithin_fun_finsetProd
  given: (hf : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.fun_finsetProd fun i hi => (hf i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[deprecated (since := "2026-04-08")]
alias derivWithin_fun_finset_prod := derivWithin_fun_finset

中文:
定理 derivWithin_fun_finsetProd
  条件: (hf : 对任意 i in u, DifferentiableWithinAt 𝕜 (f i) s x)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.fun_finsetProd fun i hi => (hf i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[deprecated (since := "2026-04-08")]
alias derivWithin_fun_finset_prod := derivWithin_fun_finset

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.fun_finsetProd, UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, fun_finsetProd, hasDerivWithinAt
-/
theorem derivWithin_fun_finsetProd (hf : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x) :
    derivWithin (∏ i in u, f i ·) s x =
      ∑ i in u, (∏ j in u.erase i, f j x) • derivWithin (f i) s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.fun_finsetProd fun i hi => (hf i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[deprecated (since := "2026-04-08")]
alias derivWithin_fun_finset_prod := derivWithin_fun_finsetProd

/--
theorem `derivWithin_finsetProd` / 定理 `derivWithin_finsetProd`

English:
theorem derivWithin_finsetProd
  given: (hf : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x)
  proof: by
  convert! derivWithin_fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")] alias derivWithin_finset_prod := derivWithin_finsetProd

中文:
定理 derivWithin_finsetProd
  条件: (hf : 对任意 i in u, DifferentiableWithinAt 𝕜 (f i) s x)
  证明: by
  convert! derivWithin_fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")] alias derivWithin_finset_prod := derivWithin_finsetProd

Depends on / 依赖: convert, derivWithin_fun_finsetProd
-/
theorem derivWithin_finsetProd (hf : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x) :
    derivWithin (∏ i in u, f i) s x =
      ∑ i in u, (∏ j in u.erase i, f j x) • derivWithin (f i) s x := by
  convert! derivWithin_fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")] alias derivWithin_finset_prod := derivWithin_finsetProd

end HasDeriv

variable {ι : Type*} {𝔸' : Type*} [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸']
  {u : Finset ι} {f : ι -> 𝕜 -> 𝔸'}

@[fun_prop]
/--
theorem `DifferentiableAt.fun_finsetProd` / 定理 `DifferentiableAt.fun_finsetProd`

English:
theorem DifferentiableAt.fun_finsetProd
  given: (hd : forall i in u, DifferentiableAt 𝕜 (f i) x)
  proof: by
  classical
  exact
    (HasDerivAt.fun_finsetProd (fun i hi => DifferentiableAt.hasDerivAt (hd i hi))).differentiableAt

@[deprecated (since := "2026-04-08")]
alias DifferentiableAt.fun_finset_prod := DifferentiableAt.fun_finsetProd

@[fun_prop]

中文:
定理 DifferentiableAt.fun_finsetProd
  条件: (hd : 对任意 i in u, DifferentiableAt 𝕜 (f i) x)
  证明: by
  classical
  exact
    (HasDerivAt.fun_finsetProd (fun i hi => DifferentiableAt.hasDerivAt (hd i hi))).differentiableAt

@[deprecated (since := "2026-04-08")]
alias DifferentiableAt.fun_finset_prod := DifferentiableAt.fun_finsetProd

@[fun_prop]

Depends on / 依赖: DifferentiableAt, DifferentiableAt.hasDerivAt, HasDerivAt, HasDerivAt.fun_finsetProd, classical, differentiableAt, fun_finsetProd, hasDerivAt
-/
theorem DifferentiableAt.fun_finsetProd (hd : forall i in u, DifferentiableAt 𝕜 (f i) x) :
    DifferentiableAt 𝕜 (∏ i in u, f i ·) x := by
  classical
  exact
    (HasDerivAt.fun_finsetProd (fun i hi => DifferentiableAt.hasDerivAt (hd i hi))).differentiableAt

@[deprecated (since := "2026-04-08")]
alias DifferentiableAt.fun_finset_prod := DifferentiableAt.fun_finsetProd

@[fun_prop]
/--
theorem `DifferentiableAt.finsetProd` / 定理 `DifferentiableAt.finsetProd`

English:
theorem DifferentiableAt.finsetProd
  given: (hd : forall i in u, DifferentiableAt 𝕜 (f i) x)
  proof: by
  convert! DifferentiableAt.fun_finsetProd hd; simp

@[deprecated (since := "2026-04-08")]
alias DifferentiableAt.finset_prod := DifferentiableAt.finsetProd

@[fun_prop]

中文:
定理 DifferentiableAt.finsetProd
  条件: (hd : 对任意 i in u, DifferentiableAt 𝕜 (f i) x)
  证明: by
  convert! DifferentiableAt.fun_finsetProd hd; simp

@[deprecated (since := "2026-04-08")]
alias DifferentiableAt.finset_prod := DifferentiableAt.finsetProd

@[fun_prop]

Depends on / 依赖: DifferentiableAt, DifferentiableAt.fun_finsetProd, convert, fun_finsetProd
-/
theorem DifferentiableAt.finsetProd (hd : forall i in u, DifferentiableAt 𝕜 (f i) x) :
    DifferentiableAt 𝕜 (∏ i in u, f i) x := by
  convert! DifferentiableAt.fun_finsetProd hd; simp

@[deprecated (since := "2026-04-08")]
alias DifferentiableAt.finset_prod := DifferentiableAt.finsetProd

@[fun_prop]
/--
theorem `DifferentiableWithinAt.fun_finsetProd` / 定理 `DifferentiableWithinAt.fun_finsetProd`

English:
theorem DifferentiableWithinAt.fun_finsetProd
  given: (hd : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x)
  proof: by
  classical
  exact (HasDerivWithinAt.fun_finsetProd (fun i hi =>
    DifferentiableWithinAt.hasDerivWithinAt (hd i hi))).differentiableWithinAt

@[deprecated (since := "2026-04-08")]
alias DifferentiableWithinAt.fun_finset_prod := DifferentiableWithinAt.fun_finsetProd

@[fun_prop]

中文:
定理 DifferentiableWithinAt.fun_finsetProd
  条件: (hd : 对任意 i in u, DifferentiableWithinAt 𝕜 (f i) s x)
  证明: by
  classical
  exact (HasDerivWithinAt.fun_finsetProd (fun i hi =>
    DifferentiableWithinAt.hasDerivWithinAt (hd i hi))).differentiableWithinAt

@[deprecated (since := "2026-04-08")]
alias DifferentiableWithinAt.fun_finset_prod := DifferentiableWithinAt.fun_finsetProd

@[fun_prop]

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.hasDerivWithinAt, HasDerivWithinAt, HasDerivWithinAt.fun_finsetProd, classical, differentiableWithinAt, fun_finsetProd, hasDerivWithinAt
-/
theorem DifferentiableWithinAt.fun_finsetProd (hd : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x) :
    DifferentiableWithinAt 𝕜 (∏ i in u, f i ·) s x := by
  classical
  exact (HasDerivWithinAt.fun_finsetProd (fun i hi =>
    DifferentiableWithinAt.hasDerivWithinAt (hd i hi))).differentiableWithinAt

@[deprecated (since := "2026-04-08")]
alias DifferentiableWithinAt.fun_finset_prod := DifferentiableWithinAt.fun_finsetProd

@[fun_prop]
/--
theorem `DifferentiableWithinAt.finsetProd` / 定理 `DifferentiableWithinAt.finsetProd`

English:
theorem DifferentiableWithinAt.finsetProd
  given: (hd : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x)
  proof: by
  convert! DifferentiableWithinAt.fun_finsetProd hd; simp

@[deprecated (since := "2026-04-08")]
alias DifferentiableWithinAt.finset_prod := DifferentiableWithinAt.finsetProd

@[fun_prop]

中文:
定理 DifferentiableWithinAt.finsetProd
  条件: (hd : 对任意 i in u, DifferentiableWithinAt 𝕜 (f i) s x)
  证明: by
  convert! DifferentiableWithinAt.fun_finsetProd hd; simp

@[deprecated (since := "2026-04-08")]
alias DifferentiableWithinAt.finset_prod := DifferentiableWithinAt.finsetProd

@[fun_prop]

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.fun_finsetProd, convert, fun_finsetProd
-/
theorem DifferentiableWithinAt.finsetProd (hd : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x) :
    DifferentiableWithinAt 𝕜 (∏ i in u, f i) s x := by
  convert! DifferentiableWithinAt.fun_finsetProd hd; simp

@[deprecated (since := "2026-04-08")]
alias DifferentiableWithinAt.finset_prod := DifferentiableWithinAt.finsetProd

@[fun_prop]
/--
theorem `DifferentiableOn.fun_finsetProd` / 定理 `DifferentiableOn.fun_finsetProd`

English:
theorem DifferentiableOn.fun_finsetProd
  given: (hd : forall i in u, DifferentiableOn 𝕜 (f i) s)
  proof: fun x hx => .fun_finsetProd (fun i hi => hd i hi x hx)

@[deprecated (since := "2026-04-08")]
alias DifferentiableOn.fun_finset_prod := DifferentiableOn.fun_finsetProd

@[fun_prop]

中文:
定理 DifferentiableOn.fun_finsetProd
  条件: (hd : 对任意 i in u, DifferentiableOn 𝕜 (f i) s)
  证明: fun x hx => .fun_finsetProd (fun i hi => hd i hi x hx)

@[deprecated (since := "2026-04-08")]
alias DifferentiableOn.fun_finset_prod := DifferentiableOn.fun_finsetProd

@[fun_prop]

Depends on / 依赖: fun_finsetProd
-/
theorem DifferentiableOn.fun_finsetProd (hd : forall i in u, DifferentiableOn 𝕜 (f i) s) :
    DifferentiableOn 𝕜 (∏ i in u, f i ·) s :=
  fun x hx => .fun_finsetProd (fun i hi => hd i hi x hx)

@[deprecated (since := "2026-04-08")]
alias DifferentiableOn.fun_finset_prod := DifferentiableOn.fun_finsetProd

@[fun_prop]
/--
theorem `DifferentiableOn.finsetProd` / 定理 `DifferentiableOn.finsetProd`

English:
theorem DifferentiableOn.finsetProd
  given: (hd : forall i in u, DifferentiableOn 𝕜 (f i) s)
  proof: fun x hx => .finsetProd (fun i hi => hd i hi x hx)

@[deprecated (since := "2026-04-08")]
alias DifferentiableOn.finset_prod := DifferentiableOn.finsetProd

@[fun_prop]

中文:
定理 DifferentiableOn.finsetProd
  条件: (hd : 对任意 i in u, DifferentiableOn 𝕜 (f i) s)
  证明: fun x hx => .finsetProd (fun i hi => hd i hi x hx)

@[deprecated (since := "2026-04-08")]
alias DifferentiableOn.finset_prod := DifferentiableOn.finsetProd

@[fun_prop]

Depends on / 依赖: finsetProd
-/
theorem DifferentiableOn.finsetProd (hd : forall i in u, DifferentiableOn 𝕜 (f i) s) :
    DifferentiableOn 𝕜 (∏ i in u, f i) s :=
  fun x hx => .finsetProd (fun i hi => hd i hi x hx)

@[deprecated (since := "2026-04-08")]
alias DifferentiableOn.finset_prod := DifferentiableOn.finsetProd

@[fun_prop]
/--
theorem `Differentiable.fun_finsetProd` / 定理 `Differentiable.fun_finsetProd`

English:
theorem Differentiable.fun_finsetProd
  given: (hd : forall i in u, Differentiable 𝕜 (f i))
  proof: fun x => .fun_finsetProd (fun i hi => hd i hi x)

@[deprecated (since := "2026-04-08")]
alias Differentiable.fun_finset_prod := Differentiable.fun_finsetProd

@[fun_prop]

中文:
定理 可微.fun_finsetProd
  条件: (hd : 对任意 i in u, 可微 𝕜 (f i))
  证明: fun x => .fun_finsetProd (fun i hi => hd i hi x)

@[deprecated (since := "2026-04-08")]
alias Differentiable.fun_finset_prod := Differentiable.fun_finsetProd

@[fun_prop]

Depends on / 依赖: fun_finsetProd
-/
theorem Differentiable.fun_finsetProd (hd : forall i in u, Differentiable 𝕜 (f i)) :
    Differentiable 𝕜 (∏ i in u, f i ·) :=
  fun x => .fun_finsetProd (fun i hi => hd i hi x)

@[deprecated (since := "2026-04-08")]
alias Differentiable.fun_finset_prod := Differentiable.fun_finsetProd

@[fun_prop]
/--
theorem `Differentiable.finsetProd` / 定理 `Differentiable.finsetProd`

English:
theorem Differentiable.finsetProd
  given: (hd : forall i in u, Differentiable 𝕜 (f i))
  proof: fun x => .finsetProd (fun i hi => hd i hi x)

@[deprecated (since := "2026-04-08")] alias Differentiable.finset_prod := Differentiable.finsetProd

中文:
定理 可微.finsetProd
  条件: (hd : 对任意 i in u, 可微 𝕜 (f i))
  证明: fun x => .finsetProd (fun i hi => hd i hi x)

@[deprecated (since := "2026-04-08")] alias Differentiable.finset_prod := Differentiable.finsetProd

Depends on / 依赖: finsetProd
-/
theorem Differentiable.finsetProd (hd : forall i in u, Differentiable 𝕜 (f i)) :
    Differentiable 𝕜 (∏ i in u, f i) :=
  fun x => .finsetProd (fun i hi => hd i hi x)

@[deprecated (since := "2026-04-08")] alias Differentiable.finset_prod := Differentiable.finsetProd

end Prod

section Div

variable {𝕜' : Type*} [NormedDivisionRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] {c : 𝕜 -> 𝕜'} {c' : 𝕜'}

/--
theorem `HasDerivAt.div_const` / 定理 `HasDerivAt.div_const`

English:
theorem HasDerivAt.div_const
  given: (hc : HasDerivAt c c' x) (d : 𝕜')
  proof: by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

中文:
定理 在点处可导.div_const
  条件: (hc : 在点处可导 c c' x) (d : 𝕜')
  证明: by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

Depends on / 依赖: div_eq_mul_inv, hc.mul_const, mul_const
-/
theorem HasDerivAt.div_const (hc : HasDerivAt c c' x) (d : 𝕜') :
    HasDerivAt (fun x => c x / d) (c' / d) x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

/--
theorem `HasDerivWithinAt.div_const` / 定理 `HasDerivWithinAt.div_const`

English:
theorem HasDerivWithinAt.div_const
  given: (hc : HasDerivWithinAt c c' s x) (d : 𝕜')
  proof: by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

中文:
定理 HasDerivWithinAt.div_const
  条件: (hc : HasDerivWithinAt c c' s x) (d : 𝕜')
  证明: by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

Depends on / 依赖: div_eq_mul_inv, hc.mul_const, mul_const
-/
theorem HasDerivWithinAt.div_const (hc : HasDerivWithinAt c c' s x) (d : 𝕜') :
    HasDerivWithinAt (fun x => c x / d) (c' / d) s x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

/--
theorem `HasStrictDerivAt.div_const` / 定理 `HasStrictDerivAt.div_const`

English:
theorem HasStrictDerivAt.div_const
  given: (hc : HasStrictDerivAt c c' x) (d : 𝕜')
  proof: by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

@[fun_prop]

中文:
定理 HasStrictDerivAt.div_const
  条件: (hc : HasStrictDerivAt c c' x) (d : 𝕜')
  证明: by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

@[fun_prop]

Depends on / 依赖: div_eq_mul_inv, hc.mul_const, mul_const
-/
theorem HasStrictDerivAt.div_const (hc : HasStrictDerivAt c c' x) (d : 𝕜') :
    HasStrictDerivAt (fun x => c x / d) (c' / d) x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

@[fun_prop]
/--
theorem `DifferentiableWithinAt.div_const` / 定理 `DifferentiableWithinAt.div_const`

English:
theorem DifferentiableWithinAt.div_const
  given: (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝕜')
  proof: (hc.hasDerivWithinAt.div_const _).differentiableWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.div_const
  条件: (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝕜')
  证明: (hc.hasDerivWithinAt.div_const _).differentiableWithinAt

@[simp, fun_prop]

Depends on / 依赖: differentiableWithinAt, div_const, hasDerivWithinAt, hc.hasDerivWithinAt.div_const
-/
theorem DifferentiableWithinAt.div_const (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝕜') :
    DifferentiableWithinAt 𝕜 (fun x => c x / d) s x :=
  (hc.hasDerivWithinAt.div_const _).differentiableWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.div_const` / 定理 `DifferentiableAt.div_const`

English:
theorem DifferentiableAt.div_const
  given: (hc : DifferentiableAt 𝕜 c x) (d : 𝕜')
  proof: (hc.hasDerivAt.div_const _).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.div_const
  条件: (hc : DifferentiableAt 𝕜 c x) (d : 𝕜')
  证明: (hc.hasDerivAt.div_const _).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, div_const, hasDerivAt, hc.hasDerivAt.div_const
-/
theorem DifferentiableAt.div_const (hc : DifferentiableAt 𝕜 c x) (d : 𝕜') :
    DifferentiableAt 𝕜 (fun x => c x / d) x :=
  (hc.hasDerivAt.div_const _).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableOn.div_const` / 定理 `DifferentiableOn.div_const`

English:
theorem DifferentiableOn.div_const
  given: (hc : DifferentiableOn 𝕜 c s) (d : 𝕜')
  proof: fun x hx => (hc x hx).div_const d

@[simp, fun_prop]

中文:
定理 DifferentiableOn.div_const
  条件: (hc : DifferentiableOn 𝕜 c s) (d : 𝕜')
  证明: fun x hx => (hc x hx).div_const d

@[simp, fun_prop]

Depends on / 依赖: div_const
-/
theorem DifferentiableOn.div_const (hc : DifferentiableOn 𝕜 c s) (d : 𝕜') :
    DifferentiableOn 𝕜 (fun x => c x / d) s := fun x hx => (hc x hx).div_const d

@[simp, fun_prop]
/--
theorem `Differentiable.div_const` / 定理 `Differentiable.div_const`

English:
theorem Differentiable.div_const
  given: (hc : Differentiable 𝕜 c) (d : 𝕜')
  proof: fun x => (hc x).div_const d

中文:
定理 可微.div_const
  条件: (hc : 可微 𝕜 c) (d : 𝕜')
  证明: fun x => (hc x).div_const d

Depends on / 依赖: div_const
-/
theorem Differentiable.div_const (hc : Differentiable 𝕜 c) (d : 𝕜') :
    Differentiable 𝕜 fun x => c x / d := fun x => (hc x).div_const d

/--
theorem `derivWithin_div_const` / 定理 `derivWithin_div_const`

English:
theorem derivWithin_div_const
  given: (c : 𝕜 -> 𝕜') (d : 𝕜')
  proof: by
  simp [div_eq_mul_inv, derivWithin_mul_const_field]

@[simp]

中文:
定理 derivWithin_div_const
  条件: (c : 𝕜 -> 𝕜') (d : 𝕜')
  证明: by
  simp [div_eq_mul_inv, derivWithin_mul_const_field]

@[simp]

Depends on / 依赖: derivWithin_mul_const_field, div_eq_mul_inv
-/
theorem derivWithin_div_const (c : 𝕜 -> 𝕜') (d : 𝕜') :
    derivWithin (fun x => c x / d) s x = derivWithin c s x / d := by
  simp [div_eq_mul_inv, derivWithin_mul_const_field]

@[simp]
/--
theorem `deriv_div_const` / 定理 `deriv_div_const`

English:
theorem deriv_div_const
  given: (d : 𝕜')
  statement: deriv (fun x => c x / d) x = deriv c x / d
  proof: by
  simp only [div_eq_mul_inv, deriv_mul_const_field]

中文:
定理 deriv_div_const
  条件: (d : 𝕜')
  结论: deriv (fun x => c x / d) x = deriv c x / d
  证明: by
  simp only [div_eq_mul_inv, deriv_mul_const_field]

Depends on / 依赖: deriv_mul_const_field, div_eq_mul_inv
-/
theorem deriv_div_const (d : 𝕜') : deriv (fun x => c x / d) x = deriv c x / d := by
  simp only [div_eq_mul_inv, deriv_mul_const_field]

end Div

section CLMCompApply

/-! ### Derivative of the pointwise composition/application of continuous linear maps -/


open ContinuousLinearMap

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {c : 𝕜 -> F ->L[𝕜] G} {c' : F ->L[𝕜] G}
  {d : 𝕜 -> E ->L[𝕜] F} {d' : E ->L[𝕜] F} {u : 𝕜 -> F} {u' : F}

/--
theorem `HasStrictDerivAt.clm_comp` / 定理 `HasStrictDerivAt.clm_comp`

English:
theorem HasStrictDerivAt.clm_comp
  given: (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
  proof: by
  simpa [add_comm] using (hc.hasStrictFDerivAt.clm_comp hd.hasStrictFDerivAt).hasStrictDerivAt

中文:
定理 HasStrictDerivAt.clm_comp
  条件: (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
  证明: by
  simpa [add_comm] using (hc.hasStrictFDerivAt.clm_comp hd.hasStrictFDerivAt).hasStrictDerivAt

Depends on / 依赖: add_comm, clm_comp, hasStrictDerivAt, hasStrictFDerivAt, hc.hasStrictFDerivAt.clm_comp, hd.hasStrictFDerivAt
-/
theorem HasStrictDerivAt.clm_comp (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x := by
  simpa [add_comm] using (hc.hasStrictFDerivAt.clm_comp hd.hasStrictFDerivAt).hasStrictDerivAt

/--
theorem `HasDerivWithinAt.clm_comp` / 定理 `HasDerivWithinAt.clm_comp`

English:
theorem HasDerivWithinAt.clm_comp
  statement: (hc : HasDerivWithinAt c c' s x)
  proof: by
  simpa [add_comm] using (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).hasDerivWithinAt

中文:
定理 HasDerivWithinAt.clm_comp
  结论: (hc : HasDerivWithinAt c c' s x)
  证明: by
  simpa [add_comm] using (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).hasDerivWithinAt

Depends on / 依赖: add_comm, clm_comp, hasDerivWithinAt, hasFDerivWithinAt, hc.hasFDerivWithinAt.clm_comp, hd.hasFDerivWithinAt
-/
theorem HasDerivWithinAt.clm_comp (hc : HasDerivWithinAt c c' s x)
    (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') s x := by
  simpa [add_comm] using (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).hasDerivWithinAt

/--
theorem `HasDerivAt.clm_comp` / 定理 `HasDerivAt.clm_comp`

English:
theorem HasDerivAt.clm_comp
  given: (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x)
  proof: by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.clm_comp hd

中文:
定理 在点处可导.clm_comp
  条件: (hc : 在点处可导 c c' x) (hd : 在点处可导 d d' x)
  证明: by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.clm_comp hd

Depends on / 依赖: clm_comp, hasDerivWithinAt_univ, hc.clm_comp
-/
theorem HasDerivAt.clm_comp (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.clm_comp hd

/--
theorem `derivWithin_clm_comp` / 定理 `derivWithin_clm_comp`

English:
theorem derivWithin_clm_comp
  statement: (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.clm_comp hd.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_clm_comp
  结论: (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.clm_comp hd.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: UniqueDiffWithinAt, clm_comp, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hc.hasDerivWithinAt.clm_comp, hd.hasDerivWithinAt
-/
theorem derivWithin_clm_comp (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => (c y).comp (d y)) s x =
      (derivWithin c s x).comp (d x) + (c x).comp (derivWithin d s x) := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.clm_comp hd.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `deriv_clm_comp` / 定理 `deriv_clm_comp`

English:
theorem deriv_clm_comp
  given: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  proof: (hc.hasDerivAt.clm_comp hd.hasDerivAt).deriv

中文:
定理 deriv_clm_comp
  条件: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  证明: (hc.hasDerivAt.clm_comp hd.hasDerivAt).deriv

Depends on / 依赖: clm_comp, hasDerivAt, hc.hasDerivAt.clm_comp, hd.hasDerivAt
-/
theorem deriv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => (c y).comp (d y)) x = (deriv c x).comp (d x) + (c x).comp (deriv d x) :=
  (hc.hasDerivAt.clm_comp hd.hasDerivAt).deriv

/--
theorem `HasStrictDerivAt.clm_apply` / 定理 `HasStrictDerivAt.clm_apply`

English:
theorem HasStrictDerivAt.clm_apply
  given: (hc : HasStrictDerivAt c c' x) (hu : HasStrictDerivAt u u' x)
  proof: by
  simpa [add_comm] using (hc.hasStrictFDerivAt.clm_apply hu.hasStrictFDerivAt).hasStrictDerivAt

中文:
定理 HasStrictDerivAt.clm_apply
  条件: (hc : HasStrictDerivAt c c' x) (hu : HasStrictDerivAt u u' x)
  证明: by
  simpa [add_comm] using (hc.hasStrictFDerivAt.clm_apply hu.hasStrictFDerivAt).hasStrictDerivAt

Depends on / 依赖: add_comm, clm_apply, hasStrictDerivAt, hasStrictFDerivAt, hc.hasStrictFDerivAt.clm_apply, hu.hasStrictFDerivAt
-/
theorem HasStrictDerivAt.clm_apply (hc : HasStrictDerivAt c c' x) (hu : HasStrictDerivAt u u' x) :
    HasStrictDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x := by
  simpa [add_comm] using (hc.hasStrictFDerivAt.clm_apply hu.hasStrictFDerivAt).hasStrictDerivAt

/--
theorem `HasDerivWithinAt.clm_apply` / 定理 `HasDerivWithinAt.clm_apply`

English:
theorem HasDerivWithinAt.clm_apply
  statement: (hc : HasDerivWithinAt c c' s x)
  proof: by
  simpa [add_comm] using (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).hasDerivWithinAt

中文:
定理 HasDerivWithinAt.clm_apply
  结论: (hc : HasDerivWithinAt c c' s x)
  证明: by
  simpa [add_comm] using (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).hasDerivWithinAt

Depends on / 依赖: add_comm, clm_apply, hasDerivWithinAt, hasFDerivWithinAt, hc.hasFDerivWithinAt.clm_apply, hu.hasFDerivWithinAt
-/
theorem HasDerivWithinAt.clm_apply (hc : HasDerivWithinAt c c' s x)
    (hu : HasDerivWithinAt u u' s x) :
    HasDerivWithinAt (fun y => (c y) (u y)) (c' (u x) + c x u') s x := by
  simpa [add_comm] using (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).hasDerivWithinAt

/--
theorem `HasDerivAt.clm_apply` / 定理 `HasDerivAt.clm_apply`

English:
theorem HasDerivAt.clm_apply
  given: (hc : HasDerivAt c c' x) (hu : HasDerivAt u u' x)
  proof: by
  simpa [add_comm] using (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).hasDerivAt

中文:
定理 在点处可导.clm_apply
  条件: (hc : 在点处可导 c c' x) (hu : 在点处可导 u u' x)
  证明: by
  simpa [add_comm] using (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).hasDerivAt

Depends on / 依赖: add_comm, clm_apply, hasDerivAt, hasFDerivAt, hc.hasFDerivAt.clm_apply, hu.hasFDerivAt
-/
theorem HasDerivAt.clm_apply (hc : HasDerivAt c c' x) (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x := by
  simpa [add_comm] using (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).hasDerivAt

/--
theorem `derivWithin_clm_apply` / 定理 `derivWithin_clm_apply`

English:
theorem derivWithin_clm_apply
  statement: (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.clm_apply hu.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_clm_apply
  结论: (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.clm_apply hu.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: UniqueDiffWithinAt, clm_apply, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hc.hasDerivWithinAt.clm_apply, hu.hasDerivWithinAt
-/
theorem derivWithin_clm_apply (hc : DifferentiableWithinAt 𝕜 c s x)
    (hu : DifferentiableWithinAt 𝕜 u s x) :
    derivWithin (fun y => (c y) (u y)) s x = derivWithin c s x (u x) + c x (derivWithin u s x) := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.clm_apply hu.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `deriv_clm_apply` / 定理 `deriv_clm_apply`

English:
theorem deriv_clm_apply
  given: (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x)
  proof: (hc.hasDerivAt.clm_apply hu.hasDerivAt).deriv

中文:
定理 deriv_clm_apply
  条件: (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x)
  证明: (hc.hasDerivAt.clm_apply hu.hasDerivAt).deriv

Depends on / 依赖: clm_apply, hasDerivAt, hc.hasDerivAt.clm_apply, hu.hasDerivAt
-/
theorem deriv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    deriv (fun y => (c y) (u y)) x = deriv c x (u x) + c x (deriv u x) :=
  (hc.hasDerivAt.clm_apply hu.hasDerivAt).deriv

end CLMCompApply
