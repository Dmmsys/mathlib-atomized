/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Additive operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* sum of finitely many functions
* multiplication of a function by a scalar constant
* negative of a function
* subtraction of two functions
-/

public section


open Filter Asymptotics ContinuousLinearMap

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f g : E -> F}
variable {f' g' : E ->L[𝕜] F}
variable {x : E}
variable {s : Set E}
variable {L : Filter (E × E)}

section ConstSMul

variable {R : Type*} [Monoid R] [DistribMulAction R F] [SMulCommClass 𝕜 R F]
  [ContinuousConstSMul R F]

/-! ### Derivative of a function multiplied by a constant -/

@[to_fun]
/--
theorem `HasFDerivAtFilter.const_smul` / 定理 `HasFDerivAtFilter.const_smul`

English:
theorem HasFDerivAtFilter.const_smul
  given: (h : HasFDerivAtFilter f f' L) (c : R)
  proof: (c • (1 : F ->L[𝕜] F)).hasFDerivAtFilter.comp h tendsto_map

@[to_fun (attr := fun_prop)]

中文:
定理 有FDerivAtFilter.const_smul
  条件: (h : 有FDerivAtFilter f f' L) (c : R)
  证明: (c • (1 : F ->L[𝕜] F)).hasFDerivAtFilter.comp h tendsto_map

@[to_fun (attr := fun_prop)]

Depends on / 依赖: hasFDerivAtFilter, hasFDerivAtFilter.comp, tendsto_map
-/
theorem HasFDerivAtFilter.const_smul (h : HasFDerivAtFilter f f' L) (c : R) :
    HasFDerivAtFilter (c • f) (c • f') L :=
  (c • (1 : F ->L[𝕜] F)).hasFDerivAtFilter.comp h tendsto_map

@[to_fun (attr := fun_prop)]
/--
theorem `HasStrictFDerivAt.const_smul` / 定理 `HasStrictFDerivAt.const_smul`

English:
theorem HasStrictFDerivAt.const_smul
  given: (h : HasStrictFDerivAt f f' x) (c : R)
  proof: HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]

中文:
定理 HasStrictFDerivAt.const_smul
  条件: (h : HasStrictFDerivAt f f' x) (c : R)
  证明: HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.const_smul, const_smul
-/
theorem HasStrictFDerivAt.const_smul (h : HasStrictFDerivAt f f' x) (c : R) :
    HasStrictFDerivAt (c • f) (c • f') x :=
  HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivWithinAt.const_smul` / 定理 `HasFDerivWithinAt.const_smul`

English:
theorem HasFDerivWithinAt.const_smul
  given: (h : HasFDerivWithinAt f f' s x) (c : R)
  proof: HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]

中文:
定理 HasFDerivWithinAt.const_smul
  条件: (h : HasFDerivWithinAt f f' s x) (c : R)
  证明: HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.const_smul, const_smul
-/
theorem HasFDerivWithinAt.const_smul (h : HasFDerivWithinAt f f' s x) (c : R) :
    HasFDerivWithinAt (c • f) (c • f') s x :=
  HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivAt.const_smul` / 定理 `HasFDerivAt.const_smul`

English:
theorem HasFDerivAt.const_smul
  given: (h : HasFDerivAt f f' x) (c : R)
  proof: HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]

中文:
定理 在点处Fréchet可导.const_smul
  条件: (h : 在点处Fréchet可导 f f' x) (c : R)
  证明: HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.const_smul, const_smul
-/
theorem HasFDerivAt.const_smul (h : HasFDerivAt f f' x) (c : R) :
    HasFDerivAt (c • f) (c • f') x :=
  HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableWithinAt.const_smul` / 定理 `DifferentiableWithinAt.const_smul`

English:
theorem DifferentiableWithinAt.const_smul
  given: (h : DifferentiableWithinAt 𝕜 f s x) (c : R)
  proof: (h.hasFDerivWithinAt.const_smul c).differentiableWithinAt

@[to_fun (attr := fun_prop)]

中文:
定理 DifferentiableWithinAt.const_smul
  条件: (h : DifferentiableWithinAt 𝕜 f s x) (c : R)
  证明: (h.hasFDerivWithinAt.const_smul c).differentiableWithinAt

@[to_fun (attr := fun_prop)]

Depends on / 依赖: const_smul, differentiableWithinAt, h.hasFDerivWithinAt.const_smul, hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    DifferentiableWithinAt 𝕜 (c • f) s x :=
  (h.hasFDerivWithinAt.const_smul c).differentiableWithinAt

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableAt.const_smul` / 定理 `DifferentiableAt.const_smul`

English:
theorem DifferentiableAt.const_smul
  given: (h : DifferentiableAt 𝕜 f x) (c : R)
  proof: (h.hasFDerivAt.const_smul c).differentiableAt

@[to_fun (attr := fun_prop)]

中文:
定理 DifferentiableAt.const_smul
  条件: (h : DifferentiableAt 𝕜 f x) (c : R)
  证明: (h.hasFDerivAt.const_smul c).differentiableAt

@[to_fun (attr := fun_prop)]

Depends on / 依赖: const_smul, differentiableAt, h.hasFDerivAt.const_smul, hasFDerivAt
-/
theorem DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    DifferentiableAt 𝕜 (c • f) x :=
  (h.hasFDerivAt.const_smul c).differentiableAt

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableOn.const_smul` / 定理 `DifferentiableOn.const_smul`

English:
theorem DifferentiableOn.const_smul
  given: (h : DifferentiableOn 𝕜 f s) (c : R)
  proof: fun x hx => (h x hx).const_smul c

@[to_fun (attr := fun_prop)]

中文:
定理 DifferentiableOn.const_smul
  条件: (h : DifferentiableOn 𝕜 f s) (c : R)
  证明: fun x hx => (h x hx).const_smul c

@[to_fun (attr := fun_prop)]

Depends on / 依赖: const_smul
-/
theorem DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) :
    DifferentiableOn 𝕜 (c • f) s := fun x hx => (h x hx).const_smul c

@[to_fun (attr := fun_prop)]
/--
theorem `Differentiable.const_smul` / 定理 `Differentiable.const_smul`

English:
theorem Differentiable.const_smul
  given: (h : Differentiable 𝕜 f) (c : R)
  proof: fun x => (h x).const_smul c

中文:
定理 可微.const_smul
  条件: (h : 可微 𝕜 f) (c : R)
  证明: fun x => (h x).const_smul c

Depends on / 依赖: const_smul
-/
theorem Differentiable.const_smul (h : Differentiable 𝕜 f) (c : R) :
    Differentiable 𝕜 (c • f) := fun x => (h x).const_smul c

/--
theorem `fderivWithin_fun_const_smul` / 定理 `fderivWithin_fun_const_smul`

English:
theorem fderivWithin_fun_const_smul
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (h.hasFDerivWithinAt.const_smul c).fderivWithin hxs

中文:
定理 fderivWithin_fun_const_smul
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (h.hasFDerivWithinAt.const_smul c).fderivWithin hxs

Depends on / 依赖: const_smul, fderivWithin, h.hasFDerivWithinAt.const_smul, hasFDerivWithinAt
-/
theorem fderivWithin_fun_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (fun y => c • f y) s x = c • fderivWithin 𝕜 f s x :=
  (h.hasFDerivWithinAt.const_smul c).fderivWithin hxs

/--
theorem `fderivWithin_const_smul` / 定理 `fderivWithin_const_smul`

English:
theorem fderivWithin_const_smul
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: fderivWithin_fun_const_smul hxs h c

中文:
定理 fderivWithin_const_smul
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: fderivWithin_fun_const_smul hxs h c

Depends on / 依赖: fderivWithin_fun_const_smul
-/
theorem fderivWithin_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x :=
  fderivWithin_fun_const_smul hxs h c

/--
lemma `differentiableWithinAt_smul_iff` / 引理 `differentiableWithinAt_smul_iff`

English:
lemma differentiableWithinAt_smul_iff
  given: (c : R) [Invertible c]
  proof: by
  refine ⟨fun h => ?_, fun h => h.const_smul c⟩
  apply (h.const_smul ⅟c).congr_of_eventuallyEq ?_ (by simp)
  filter_upwards with x using by simp

中文:
引理 differentiableWithinAt_smul_iff
  条件: (c : R) [可逆 c]
  证明: by
  refine ⟨fun h => ?_, fun h => h.const_smul c⟩
  apply (h.const_smul ⅟c).congr_of_eventuallyEq ?_ (by simp)
  filter_upwards with x using by simp

Depends on / 依赖: congr_of_eventuallyEq, const_smul, filter_upwards, h.const_smul
-/
lemma differentiableWithinAt_smul_iff (c : R) [Invertible c] :
    DifferentiableWithinAt 𝕜 (c • f) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  refine ⟨fun h => ?_, fun h => h.const_smul c⟩
  apply (h.const_smul ⅟c).congr_of_eventuallyEq ?_ (by simp)
  filter_upwards with x using by simp

/--
theorem `fderivWithin_const_smul_of_invertible` / 定理 `fderivWithin_const_smul_of_invertible`

English:
theorem fderivWithin_const_smul_of_invertible
  statement: (c : R) [Invertible c]
  proof: by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact (h.hasFDerivWithinAt.const_smul c).fderivWithin hs
  · have : ¬DifferentiableWithinAt 𝕜 (c • f) s x := by
      contrapose h
      exact (differentiableWithinAt_smul_iff c).mp h
    simp [fderivWithin_zero_of_not_differentiableWithinAt h,
  

中文:
定理 fderivWithin_const_smul_of_invertible
  结论: (c : R) [可逆 c]
  证明: by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact (h.hasFDerivWithinAt.const_smul c).fderivWithin hs
  · have : ¬DifferentiableWithinAt 𝕜 (c • f) s x := by
      contrapose h
      exact (differentiableWithinAt_smul_iff c).mp h
    simp [fderivWithin_zero_of_not_differentiableWithinAt h,
  

Depends on / 依赖: DifferentiableWithinAt, const_smul, contrapose, differentiableWithinAt_smul_iff, fderivWithin, fderivWithin_zero_of_not_differentiableWithinAt, h.hasFDerivWithinAt.const_smul, hasFDerivWithinAt
-/
theorem fderivWithin_const_smul_of_invertible (c : R) [Invertible c]
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x := by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact (h.hasFDerivWithinAt.const_smul c).fderivWithin hs
  · have : ¬DifferentiableWithinAt 𝕜 (c • f) s x := by
      contrapose h
      exact (differentiableWithinAt_smul_iff c).mp h
    simp [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt this]

/--
theorem `fderiv_fun_const_smul` / 定理 `fderiv_fun_const_smul`

English:
theorem fderiv_fun_const_smul
  given: (h : DifferentiableAt 𝕜 f x) (c : R)
  proof: (h.hasFDerivAt.const_smul c).fderiv

中文:
定理 fderiv_fun_const_smul
  条件: (h : DifferentiableAt 𝕜 f x) (c : R)
  证明: (h.hasFDerivAt.const_smul c).fderiv

Depends on / 依赖: const_smul, fderiv, h.hasFDerivAt.const_smul, hasFDerivAt
-/
theorem fderiv_fun_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (fun y => c • f y) x = c • fderiv 𝕜 f x :=
  (h.hasFDerivAt.const_smul c).fderiv

/--
theorem `fderiv_const_smul` / 定理 `fderiv_const_smul`

English:
theorem fderiv_const_smul
  given: (h : DifferentiableAt 𝕜 f x) (c : R)
  proof: (h.hasFDerivAt.const_smul c).fderiv

中文:
定理 fderiv_const_smul
  条件: (h : DifferentiableAt 𝕜 f x) (c : R)
  证明: (h.hasFDerivAt.const_smul c).fderiv

Depends on / 依赖: const_smul, fderiv, h.hasFDerivAt.const_smul, hasFDerivAt
-/
theorem fderiv_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (c • f) x = c • fderiv 𝕜 f x :=
  (h.hasFDerivAt.const_smul c).fderiv

/--
lemma `differentiableAt_smul_iff` / 引理 `differentiableAt_smul_iff`

English:
lemma differentiableAt_smul_iff
  given: (c : R) [Invertible c]
  proof: by
  rw [← differentiableWithinAt_univ]; rw [differentiableWithinAt_smul_iff]; rw [differentiableWithinAt_univ]

中文:
引理 differentiableAt_smul_iff
  条件: (c : R) [可逆 c]
  证明: by
  rw [← differentiableWithinAt_univ]; rw [differentiableWithinAt_smul_iff]; rw [differentiableWithinAt_univ]

Depends on / 依赖: differentiableWithinAt_smul_iff, differentiableWithinAt_univ
-/
lemma differentiableAt_smul_iff (c : R) [Invertible c] :
    DifferentiableAt 𝕜 (c • f) x ↔ DifferentiableAt 𝕜 f x := by
  rw [← differentiableWithinAt_univ]; rw [differentiableWithinAt_smul_iff]; rw [differentiableWithinAt_univ]

/--
theorem `fderiv_const_smul_of_invertible` / 定理 `fderiv_const_smul_of_invertible`

English:
theorem fderiv_const_smul_of_invertible
  given: (c : R) [Invertible c]
  proof: by
  simp [← fderivWithin_univ, fderivWithin_const_smul_of_invertible c uniqueDiffWithinAt_univ]

中文:
定理 fderiv_const_smul_of_invertible
  条件: (c : R) [可逆 c]
  证明: by
  simp [← fderivWithin_univ, fderivWithin_const_smul_of_invertible c uniqueDiffWithinAt_univ]

Depends on / 依赖: fderivWithin_const_smul_of_invertible, fderivWithin_univ, uniqueDiffWithinAt_univ
-/
theorem fderiv_const_smul_of_invertible (c : R) [Invertible c] :
    fderiv 𝕜 (c • f) x = c • fderiv 𝕜 f x := by
  simp [← fderivWithin_univ, fderivWithin_const_smul_of_invertible c uniqueDiffWithinAt_univ]

end ConstSMul

section ConstSMulDivisionRing

variable {R : Type*} [DivisionSemiring R] [Module R F] [SMulCommClass 𝕜 R F]
  [ContinuousConstSMul R F]

/--
lemma `fderivWithin_const_smul_field` / 引理 `fderivWithin_const_smul_field`

English:
lemma fderivWithin_const_smul_field
  given: (c : R) (hs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  obtain (rfl | ha) := eq_or_ne c 0
  · simp
  · have : Invertible c := invertibleOfNonzero ha
    simp [fderivWithin_const_smul_of_invertible c hs]

中文:
引理 fderivWithin_const_smul_field
  条件: (c : R) (hs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  obtain (rfl | ha) := eq_or_ne c 0
  · simp
  · have : Invertible c := invertibleOfNonzero ha
    simp [fderivWithin_const_smul_of_invertible c hs]

Depends on / 依赖: Invertible, eq_or_ne, fderivWithin_const_smul_of_invertible, invertibleOfNonzero
-/
lemma fderivWithin_const_smul_field (c : R) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x := by
  obtain (rfl | ha) := eq_or_ne c 0
  · simp
  · have : Invertible c := invertibleOfNonzero ha
    simp [fderivWithin_const_smul_of_invertible c hs]

/--
lemma `fderivWithin_const_smul_field'` / 引理 `fderivWithin_const_smul_field'`

English:
lemma fderivWithin_const_smul_field'
  given: {s : Set 𝕜} {f : 𝕜 -> F} {x : 𝕜} (c : R)
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact fderivWithin_const_smul_field c hsx
  · simp [fderivWithin_zero_of_not_uniqueDiffWithinAt hsx]

omit [DivisionSemiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F] in

中文:
引理 fderivWithin_const_smul_field'
  条件: {s : 集合 𝕜} {f : 𝕜 -> F} {x : 𝕜} (c : R)
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact fderivWithin_const_smul_field c hsx
  · simp [fderivWithin_zero_of_not_uniqueDiffWithinAt hsx]

omit [DivisionSemiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F] in

Depends on / 依赖: UniqueDiffWithinAt, fderivWithin_const_smul_field, fderivWithin_zero_of_not_uniqueDiffWithinAt
-/
lemma fderivWithin_const_smul_field' {s : Set 𝕜} {f : 𝕜 -> F} {x : 𝕜} (c : R) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact fderivWithin_const_smul_field c hsx
  · simp [fderivWithin_zero_of_not_uniqueDiffWithinAt hsx]

omit [DivisionSemiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F] in
/--
lemma `fderivWithin_neg'` / 引理 `fderivWithin_neg'`

English:
lemma fderivWithin_neg'
  given: {s : Set 𝕜} {f : 𝕜 -> F} {x : 𝕜}
  proof: by
  simpa only [neg_smul, one_smul] using fderivWithin_const_smul_field' (f := f) (-1 : 𝕜)

@[deprecated (since := "2026-01-11")] alias fderivWithin_const_smul_of_field :=
  fderivWithin_const_smul_field

中文:
引理 fderivWithin_neg'
  条件: {s : 集合 𝕜} {f : 𝕜 -> F} {x : 𝕜}
  证明: by
  simpa only [neg_smul, one_smul] using fderivWithin_const_smul_field' (f := f) (-1 : 𝕜)

@[deprecated (since := "2026-01-11")] alias fderivWithin_const_smul_of_field :=
  fderivWithin_const_smul_field

Depends on / 依赖: fderivWithin_const_smul_field, neg_smul, one_smul
-/
lemma fderivWithin_neg' {s : Set 𝕜} {f : 𝕜 -> F} {x : 𝕜} :
    fderivWithin 𝕜 (-f) s x = -fderivWithin 𝕜 f s x := by
  simpa only [neg_smul, one_smul] using fderivWithin_const_smul_field' (f := f) (-1 : 𝕜)

@[deprecated (since := "2026-01-11")] alias fderivWithin_const_smul_of_field :=
  fderivWithin_const_smul_field

/--
lemma `fderiv_const_smul_field` / 引理 `fderiv_const_smul_field`

English:
lemma fderiv_const_smul_field
  given: (c : R)
  statement: fderiv 𝕜 (c • f) = c • fderiv 𝕜 f
  proof: by
  simp_rw [← fderivWithin_univ]
  ext x
  simp [fderivWithin_const_smul_field c uniqueDiffWithinAt_univ]

@[deprecated (since := "2026-01-11")] alias fderiv_const_smul_of_field := fderiv_const_smul_field

中文:
引理 fderiv_const_smul_field
  条件: (c : R)
  结论: fderiv 𝕜 (c • f) = c • fderiv 𝕜 f
  证明: by
  simp_rw [← fderivWithin_univ]
  ext x
  simp [fderivWithin_const_smul_field c uniqueDiffWithinAt_univ]

@[deprecated (since := "2026-01-11")] alias fderiv_const_smul_of_field := fderiv_const_smul_field

Depends on / 依赖: fderivWithin_const_smul_field, fderivWithin_univ, simp_rw, uniqueDiffWithinAt_univ
-/
lemma fderiv_const_smul_field (c : R) : fderiv 𝕜 (c • f) = c • fderiv 𝕜 f := by
  simp_rw [← fderivWithin_univ]
  ext x
  simp [fderivWithin_const_smul_field c uniqueDiffWithinAt_univ]

@[deprecated (since := "2026-01-11")] alias fderiv_const_smul_of_field := fderiv_const_smul_field

end ConstSMulDivisionRing

section Add

/-! ### Derivative of the sum of two functions -/

@[to_fun]
/--
theorem `HasFDerivAtFilter.add` / 定理 `HasFDerivAtFilter.add`

English:
theorem HasFDerivAtFilter.add
  statement: (hf : HasFDerivAtFilter f f' L)
  proof: .of_isLittleO (hf.isLittleO.add hg.isLittleO).congr_left fun _ => by
    grind [Pi.add_apply]

@[to_fun (attr := fun_prop)]

中文:
定理 有FDerivAtFilter.add
  结论: (hf : 有FDerivAtFilter f f' L)
  证明: .of_isLittleO (hf.isLittleO.add hg.isLittleO).congr_left fun _ => by
    grind [Pi.add_apply]

@[to_fun (attr := fun_prop)]

Depends on / 依赖: Pi.add_apply, add_apply, congr_left, hf.isLittleO.add, hg.isLittleO, isLittleO, of_isLittleO
-/
theorem HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f' L)
    (hg : HasFDerivAtFilter g g' L) : HasFDerivAtFilter (f + g) (f' + g') L :=
.of_isLittleO (hf.isLittleO.add hg.isLittleO).congr_left fun _ => by
    grind [Pi.add_apply]

@[to_fun (attr := fun_prop)]
/--
theorem `HasStrictFDerivAt.add` / 定理 `HasStrictFDerivAt.add`

English:
theorem HasStrictFDerivAt.add
  given: (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
  proof: HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]

中文:
定理 HasStrictFDerivAt.add
  条件: (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
  证明: HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.add
-/
theorem HasStrictFDerivAt.add (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (f + g) (f' + g') x :=
  HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivWithinAt.add` / 定理 `HasFDerivWithinAt.add`

English:
theorem HasFDerivWithinAt.add
  statement: (hf : HasFDerivWithinAt f f' s x)
  proof: HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]

中文:
定理 HasFDerivWithinAt.add
  结论: (hf : HasFDerivWithinAt f f' s x)
  证明: HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.add
-/
theorem HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f + g) (f' + g') s x :=
  HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivAt.add` / 定理 `HasFDerivAt.add`

English:
theorem HasFDerivAt.add
  given: (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
  proof: HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]

中文:
定理 在点处Fréchet可导.add
  条件: (hf : 在点处Fréchet可导 f f' x) (hg : 在点处Fréchet可导 g g' x)
  证明: HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.add
-/
theorem HasFDerivAt.add (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (f + g) (f' + g') x :=
  HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableWithinAt.add` / 定理 `DifferentiableWithinAt.add`

English:
theorem DifferentiableWithinAt.add
  statement: (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]

中文:
定理 DifferentiableWithinAt.add
  结论: (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.add, hg.hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (f + g) s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
/--
theorem `DifferentiableAt.add` / 定理 `DifferentiableAt.add`

English:
theorem DifferentiableAt.add
  given: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  proof: (hf.hasFDerivAt.add hg.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]

中文:
定理 DifferentiableAt.add
  条件: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  证明: (hf.hasFDerivAt.add hg.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]

Depends on / 依赖: differentiableAt, hasFDerivAt, hf.hasFDerivAt.add, hg.hasFDerivAt
-/
theorem DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f + g) x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableOn.add` / 定理 `DifferentiableOn.add`

English:
theorem DifferentiableOn.add
  given: (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
  proof: fun x hx => (hf x hx).add (hg x hx)

@[to_fun (attr := simp, fun_prop)]

中文:
定理 DifferentiableOn.add
  条件: (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
  证明: fun x hx => (hf x hx).add (hg x hx)

@[to_fun (attr := simp, fun_prop)]
-/
theorem DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f + g) s := fun x hx => (hf x hx).add (hg x hx)

@[to_fun (attr := simp, fun_prop)]
/--
theorem `Differentiable.add` / 定理 `Differentiable.add`

English:
theorem Differentiable.add
  given: (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g)
  proof: fun x => (hf x).add (hg x)

中文:
定理 可微.add
  条件: (hf : 可微 𝕜 f) (hg : 可微 𝕜 g)
  证明: fun x => (hf x).add (hg x)
-/
theorem Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f + g) := fun x => (hf x).add (hg x)

-- TODO: `@[to_fun]` gives incorrect lemma name
/--
theorem `fderivWithin_add` / 定理 `fderivWithin_add`

English:
theorem fderivWithin_add
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).fderivWithin hxs

中文:
定理 fderivWithin_add
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.add, hg.hasFDerivWithinAt
-/
theorem fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (f + g) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).fderivWithin hxs

/--
theorem `fderivWithin_fun_add` / 定理 `fderivWithin_fun_add`

English:
theorem fderivWithin_fun_add
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: fderivWithin_add hxs hf hg

中文:
定理 fderivWithin_fun_add
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: fderivWithin_add hxs hf hg

Depends on / 依赖: fderivWithin_add
-/
theorem fderivWithin_fun_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y + g y) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  fderivWithin_add hxs hf hg

-- TODO: `@[to_fun]` gives incorrect lemma name
/--
theorem `fderiv_add` / 定理 `fderiv_add`

English:
theorem fderiv_add
  given: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  proof: (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv

中文:
定理 fderiv_add
  条件: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  证明: (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hf.hasFDerivAt.add, hg.hasFDerivAt
-/
theorem fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (f + g) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv

/--
theorem `fderiv_fun_add` / 定理 `fderiv_fun_add`

English:
theorem fderiv_fun_add
  given: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  proof: fderiv_add hf hg

@[simp]

中文:
定理 fderiv_fun_add
  条件: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  证明: fderiv_add hf hg

@[simp]

Depends on / 依赖: fderiv_add
-/
theorem fderiv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  fderiv_add hf hg

@[simp]
/--
theorem `hasFDerivAtFilter_add_const_iff` / 定理 `hasFDerivAtFilter_add_const_iff`

English:
theorem hasFDerivAtFilter_add_const_iff
  given: (c : F)
  proof: by
  simp [hasFDerivAtFilter_iff_isLittleOTVS]

alias ⟨_, HasFDerivAtFilter.add_const⟩ := hasFDerivAtFilter_add_const_iff

@[simp]

中文:
定理 hasFDerivAtFilter_add_const_iff
  条件: (c : F)
  证明: by
  simp [hasFDerivAtFilter_iff_isLittleOTVS]

alias ⟨_, HasFDerivAtFilter.add_const⟩ := hasFDerivAtFilter_add_const_iff

@[simp]

Depends on / 依赖: hasFDerivAtFilter_iff_isLittleOTVS
-/
theorem hasFDerivAtFilter_add_const_iff (c : F) :
    HasFDerivAtFilter (f · + c) f' L ↔ HasFDerivAtFilter f f' L := by
  simp [hasFDerivAtFilter_iff_isLittleOTVS]

alias ⟨_, HasFDerivAtFilter.add_const⟩ := hasFDerivAtFilter_add_const_iff

@[simp]
/--
theorem `hasStrictFDerivAt_add_const_iff` / 定理 `hasStrictFDerivAt_add_const_iff`

English:
theorem hasStrictFDerivAt_add_const_iff
  given: (c : F)
  proof: by
  simp [hasStrictFDerivAt_iff_isLittleO]

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.add_const⟩ := hasStrictFDerivAt_add_const_iff

@[simp]

中文:
定理 hasStrictFDerivAt_add_const_iff
  条件: (c : F)
  证明: by
  simp [hasStrictFDerivAt_iff_isLittleO]

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.add_const⟩ := hasStrictFDerivAt_add_const_iff

@[simp]

Depends on / 依赖: hasStrictFDerivAt_iff_isLittleO
-/
theorem hasStrictFDerivAt_add_const_iff (c : F) :
    HasStrictFDerivAt (f · + c) f' x ↔ HasStrictFDerivAt f f' x := by
  simp [hasStrictFDerivAt_iff_isLittleO]

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.add_const⟩ := hasStrictFDerivAt_add_const_iff

@[simp]
/--
theorem `hasFDerivWithinAt_add_const_iff` / 定理 `hasFDerivWithinAt_add_const_iff`

English:
theorem hasFDerivWithinAt_add_const_iff
  given: (c : F)
  proof: hasFDerivAtFilter_add_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.add_const⟩ := hasFDerivWithinAt_add_const_iff

@[simp]

中文:
定理 hasFDerivWithinAt_add_const_iff
  条件: (c : F)
  证明: hasFDerivAtFilter_add_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.add_const⟩ := hasFDerivWithinAt_add_const_iff

@[simp]

Depends on / 依赖: hasFDerivAtFilter_add_const_iff
-/
theorem hasFDerivWithinAt_add_const_iff (c : F) :
    HasFDerivWithinAt (f · + c) f' s x ↔ HasFDerivWithinAt f f' s x :=
  hasFDerivAtFilter_add_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.add_const⟩ := hasFDerivWithinAt_add_const_iff

@[simp]
/--
theorem `hasFDerivAt_add_const_iff` / 定理 `hasFDerivAt_add_const_iff`

English:
theorem hasFDerivAt_add_const_iff
  given: (c : F)
  statement: HasFDerivAt (f · + c) f' x ↔ HasFDerivAt f f' x
  proof: hasFDerivAtFilter_add_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.add_const⟩ := hasFDerivAt_add_const_iff

@[simp]

中文:
定理 hasFDerivAt_add_const_iff
  条件: (c : F)
  结论: 在点处Fréchet可导 (f · + c) f' x ↔ 在点处Fréchet可导 f f' x
  证明: hasFDerivAtFilter_add_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.add_const⟩ := hasFDerivAt_add_const_iff

@[simp]

Depends on / 依赖: hasFDerivAtFilter_add_const_iff
-/
theorem hasFDerivAt_add_const_iff (c : F) : HasFDerivAt (f · + c) f' x ↔ HasFDerivAt f f' x :=
  hasFDerivAtFilter_add_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.add_const⟩ := hasFDerivAt_add_const_iff

@[simp]
/--
theorem `differentiableWithinAt_add_const_iff` / 定理 `differentiableWithinAt_add_const_iff`

English:
theorem differentiableWithinAt_add_const_iff
  given: (c : F)
  proof: exists_congr fun _ => hasFDerivWithinAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableWithinAt.add_const⟩ := differentiableWithinAt_add_const_iff

@[simp]

中文:
定理 differentiableWithinAt_add_const_iff
  条件: (c : F)
  证明: exists_congr fun _ => hasFDerivWithinAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableWithinAt.add_const⟩ := differentiableWithinAt_add_const_iff

@[simp]

Depends on / 依赖: exists_congr, hasFDerivWithinAt_add_const_iff
-/
theorem differentiableWithinAt_add_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y + c) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  exists_congr fun _ => hasFDerivWithinAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableWithinAt.add_const⟩ := differentiableWithinAt_add_const_iff

@[simp]
/--
theorem `differentiableAt_add_const_iff` / 定理 `differentiableAt_add_const_iff`

English:
theorem differentiableAt_add_const_iff
  given: (c : F)
  proof: exists_congr fun _ => hasFDerivAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableAt.add_const⟩ := differentiableAt_add_const_iff

@[simp]

中文:
定理 differentiableAt_add_const_iff
  条件: (c : F)
  证明: exists_congr fun _ => hasFDerivAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableAt.add_const⟩ := differentiableAt_add_const_iff

@[simp]

Depends on / 依赖: exists_congr, hasFDerivAt_add_const_iff
-/
theorem differentiableAt_add_const_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => f y + c) x ↔ DifferentiableAt 𝕜 f x :=
  exists_congr fun _ => hasFDerivAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableAt.add_const⟩ := differentiableAt_add_const_iff

@[simp]
/--
theorem `differentiableOn_add_const_iff` / 定理 `differentiableOn_add_const_iff`

English:
theorem differentiableOn_add_const_iff
  given: (c : F)
  proof: forall₂_congr fun _ _ => differentiableWithinAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableOn.add_const⟩ := differentiableOn_add_const_iff

@[simp]

中文:
定理 differentiableOn_add_const_iff
  条件: (c : F)
  证明: forall₂_congr fun _ _ => differentiableWithinAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableOn.add_const⟩ := differentiableOn_add_const_iff

@[simp]

Depends on / 依赖: differentiableWithinAt_add_const_iff
-/
theorem differentiableOn_add_const_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => f y + c) s ↔ DifferentiableOn 𝕜 f s :=
  forall₂_congr fun _ _ => differentiableWithinAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableOn.add_const⟩ := differentiableOn_add_const_iff

@[simp]
/--
theorem `differentiable_add_const_iff` / 定理 `differentiable_add_const_iff`

English:
theorem differentiable_add_const_iff
  given: (c : F)
  proof: forall_congr' fun _ => differentiableAt_add_const_iff c

@[fun_prop]
alias ⟨_, Differentiable.add_const⟩ := differentiable_add_const_iff

@[simp]

中文:
定理 differentiable_add_const_iff
  条件: (c : F)
  证明: forall_congr' fun _ => differentiableAt_add_const_iff c

@[fun_prop]
alias ⟨_, Differentiable.add_const⟩ := differentiable_add_const_iff

@[simp]

Depends on / 依赖: differentiableAt_add_const_iff, forall_congr
-/
theorem differentiable_add_const_iff (c : F) :
    (Differentiable 𝕜 fun y => f y + c) ↔ Differentiable 𝕜 f :=
  forall_congr' fun _ => differentiableAt_add_const_iff c

@[fun_prop]
alias ⟨_, Differentiable.add_const⟩ := differentiable_add_const_iff

@[simp]
/--
theorem `fderivWithin_add_const` / 定理 `fderivWithin_add_const`

English:
theorem fderivWithin_add_const
  given: (c : F)
  proof: by
  classical simp [fderivWithin]

@[simp]

中文:
定理 fderivWithin_add_const
  条件: (c : F)
  证明: by
  classical simp [fderivWithin]

@[simp]

Depends on / 依赖: classical, fderivWithin
-/
theorem fderivWithin_add_const (c : F) :
    fderivWithin 𝕜 (fun y => f y + c) s x = fderivWithin 𝕜 f s x := by
  classical simp [fderivWithin]

@[simp]
/--
theorem `fderiv_add_const` / 定理 `fderiv_add_const`

English:
theorem fderiv_add_const
  given: (c : F)
  statement: fderiv 𝕜 (fun y => f y + c) x = fderiv 𝕜 f x
  proof: by
  simp only [← fderivWithin_univ, fderivWithin_add_const]

@[simp]

中文:
定理 fderiv_add_const
  条件: (c : F)
  结论: fderiv 𝕜 (fun y => f y + c) x = fderiv 𝕜 f x
  证明: by
  simp only [← fderivWithin_univ, fderivWithin_add_const]

@[simp]

Depends on / 依赖: fderivWithin_add_const, fderivWithin_univ
-/
theorem fderiv_add_const (c : F) : fderiv 𝕜 (fun y => f y + c) x = fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_add_const]

@[simp]
/--
theorem `hasFDerivAtFilter_const_add_iff` / 定理 `hasFDerivAtFilter_const_add_iff`

English:
theorem hasFDerivAtFilter_const_add_iff
  given: (c : F)
  proof: by
  simpa only [add_comm] using hasFDerivAtFilter_add_const_iff c

alias ⟨_, HasFDerivAtFilter.const_add⟩ := hasFDerivAtFilter_const_add_iff

@[simp]

中文:
定理 hasFDerivAtFilter_const_add_iff
  条件: (c : F)
  证明: by
  simpa only [add_comm] using hasFDerivAtFilter_add_const_iff c

alias ⟨_, HasFDerivAtFilter.const_add⟩ := hasFDerivAtFilter_const_add_iff

@[simp]

Depends on / 依赖: add_comm, hasFDerivAtFilter_add_const_iff
-/
theorem hasFDerivAtFilter_const_add_iff (c : F) :
    HasFDerivAtFilter (c + f ·) f' L ↔ HasFDerivAtFilter f f' L := by
  simpa only [add_comm] using hasFDerivAtFilter_add_const_iff c

alias ⟨_, HasFDerivAtFilter.const_add⟩ := hasFDerivAtFilter_const_add_iff

@[simp]
/--
theorem `hasStrictFDerivAt_const_add_iff` / 定理 `hasStrictFDerivAt_const_add_iff`

English:
theorem hasStrictFDerivAt_const_add_iff
  given: (c : F)
  proof: by
  simpa only [add_comm] using hasStrictFDerivAt_add_const_iff c

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.const_add⟩ := hasStrictFDerivAt_const_add_iff

@[simp]

中文:
定理 hasStrictFDerivAt_const_add_iff
  条件: (c : F)
  证明: by
  simpa only [add_comm] using hasStrictFDerivAt_add_const_iff c

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.const_add⟩ := hasStrictFDerivAt_const_add_iff

@[simp]

Depends on / 依赖: add_comm, hasStrictFDerivAt_add_const_iff
-/
theorem hasStrictFDerivAt_const_add_iff (c : F) :
    HasStrictFDerivAt (c + f ·) f' x ↔ HasStrictFDerivAt f f' x := by
  simpa only [add_comm] using hasStrictFDerivAt_add_const_iff c

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.const_add⟩ := hasStrictFDerivAt_const_add_iff

@[simp]
/--
theorem `hasFDerivWithinAt_const_add_iff` / 定理 `hasFDerivWithinAt_const_add_iff`

English:
theorem hasFDerivWithinAt_const_add_iff
  given: (c : F)
  proof: hasFDerivAtFilter_const_add_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.const_add⟩ := hasFDerivWithinAt_const_add_iff

@[simp]

中文:
定理 hasFDerivWithinAt_const_add_iff
  条件: (c : F)
  证明: hasFDerivAtFilter_const_add_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.const_add⟩ := hasFDerivWithinAt_const_add_iff

@[simp]

Depends on / 依赖: hasFDerivAtFilter_const_add_iff
-/
theorem hasFDerivWithinAt_const_add_iff (c : F) :
    HasFDerivWithinAt (c + f ·) f' s x ↔ HasFDerivWithinAt f f' s x :=
  hasFDerivAtFilter_const_add_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.const_add⟩ := hasFDerivWithinAt_const_add_iff

@[simp]
/--
theorem `hasFDerivAt_const_add_iff` / 定理 `hasFDerivAt_const_add_iff`

English:
theorem hasFDerivAt_const_add_iff
  given: (c : F)
  statement: HasFDerivAt (c + f ·) f' x ↔ HasFDerivAt f f' x
  proof: hasFDerivAtFilter_const_add_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.const_add⟩ := hasFDerivAt_const_add_iff

@[simp]

中文:
定理 hasFDerivAt_const_add_iff
  条件: (c : F)
  结论: 在点处Fréchet可导 (c + f ·) f' x ↔ 在点处Fréchet可导 f f' x
  证明: hasFDerivAtFilter_const_add_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.const_add⟩ := hasFDerivAt_const_add_iff

@[simp]

Depends on / 依赖: hasFDerivAtFilter_const_add_iff
-/
theorem hasFDerivAt_const_add_iff (c : F) : HasFDerivAt (c + f ·) f' x ↔ HasFDerivAt f f' x :=
  hasFDerivAtFilter_const_add_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.const_add⟩ := hasFDerivAt_const_add_iff

@[simp]
/--
theorem `differentiableWithinAt_const_add_iff` / 定理 `differentiableWithinAt_const_add_iff`

English:
theorem differentiableWithinAt_const_add_iff
  given: (c : F)
  proof: exists_congr fun _ => hasFDerivWithinAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableWithinAt.const_add⟩ := differentiableWithinAt_const_add_iff

@[simp]

中文:
定理 differentiableWithinAt_const_add_iff
  条件: (c : F)
  证明: exists_congr fun _ => hasFDerivWithinAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableWithinAt.const_add⟩ := differentiableWithinAt_const_add_iff

@[simp]

Depends on / 依赖: exists_congr, hasFDerivWithinAt_const_add_iff
-/
theorem differentiableWithinAt_const_add_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c + f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  exists_congr fun _ => hasFDerivWithinAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableWithinAt.const_add⟩ := differentiableWithinAt_const_add_iff

@[simp]
/--
theorem `differentiableAt_const_add_iff` / 定理 `differentiableAt_const_add_iff`

English:
theorem differentiableAt_const_add_iff
  given: (c : F)
  proof: exists_congr fun _ => hasFDerivAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableAt.const_add⟩ := differentiableAt_const_add_iff

@[simp]

中文:
定理 differentiableAt_const_add_iff
  条件: (c : F)
  证明: exists_congr fun _ => hasFDerivAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableAt.const_add⟩ := differentiableAt_const_add_iff

@[simp]

Depends on / 依赖: exists_congr, hasFDerivAt_const_add_iff
-/
theorem differentiableAt_const_add_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => c + f y) x ↔ DifferentiableAt 𝕜 f x :=
  exists_congr fun _ => hasFDerivAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableAt.const_add⟩ := differentiableAt_const_add_iff

@[simp]
/--
theorem `differentiableOn_const_add_iff` / 定理 `differentiableOn_const_add_iff`

English:
theorem differentiableOn_const_add_iff
  given: (c : F)
  proof: forall₂_congr fun _ _ => differentiableWithinAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableOn.const_add⟩ := differentiableOn_const_add_iff

@[simp]

中文:
定理 differentiableOn_const_add_iff
  条件: (c : F)
  证明: forall₂_congr fun _ _ => differentiableWithinAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableOn.const_add⟩ := differentiableOn_const_add_iff

@[simp]

Depends on / 依赖: differentiableWithinAt_const_add_iff
-/
theorem differentiableOn_const_add_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => c + f y) s ↔ DifferentiableOn 𝕜 f s :=
  forall₂_congr fun _ _ => differentiableWithinAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableOn.const_add⟩ := differentiableOn_const_add_iff

@[simp]
/--
theorem `differentiable_const_add_iff` / 定理 `differentiable_const_add_iff`

English:
theorem differentiable_const_add_iff
  given: (c : F)
  proof: forall_congr' fun _ => differentiableAt_const_add_iff c

@[fun_prop]
alias ⟨_, Differentiable.const_add⟩ := differentiable_const_add_iff

@[simp]

中文:
定理 differentiable_const_add_iff
  条件: (c : F)
  证明: forall_congr' fun _ => differentiableAt_const_add_iff c

@[fun_prop]
alias ⟨_, Differentiable.const_add⟩ := differentiable_const_add_iff

@[simp]

Depends on / 依赖: differentiableAt_const_add_iff, forall_congr
-/
theorem differentiable_const_add_iff (c : F) :
    (Differentiable 𝕜 fun y => c + f y) ↔ Differentiable 𝕜 f :=
  forall_congr' fun _ => differentiableAt_const_add_iff c

@[fun_prop]
alias ⟨_, Differentiable.const_add⟩ := differentiable_const_add_iff

@[simp]
/--
theorem `fderivWithin_const_add` / 定理 `fderivWithin_const_add`

English:
theorem fderivWithin_const_add
  given: (c : F)
  proof: by
  simpa only [add_comm] using fderivWithin_add_const c

@[simp]

中文:
定理 fderivWithin_const_add
  条件: (c : F)
  证明: by
  simpa only [add_comm] using fderivWithin_add_const c

@[simp]

Depends on / 依赖: add_comm, fderivWithin_add_const
-/
theorem fderivWithin_const_add (c : F) :
    fderivWithin 𝕜 (fun y => c + f y) s x = fderivWithin 𝕜 f s x := by
  simpa only [add_comm] using fderivWithin_add_const c

@[simp]
/--
theorem `fderiv_const_add` / 定理 `fderiv_const_add`

English:
theorem fderiv_const_add
  given: (c : F)
  statement: fderiv 𝕜 (fun y => c + f y) x = fderiv 𝕜 f x
  proof: by
  simp only [add_comm c, fderiv_add_const]

中文:
定理 fderiv_const_add
  条件: (c : F)
  结论: fderiv 𝕜 (fun y => c + f y) x = fderiv 𝕜 f x
  证明: by
  simp only [add_comm c, fderiv_add_const]

Depends on / 依赖: add_comm, fderiv_add_const
-/
theorem fderiv_const_add (c : F) : fderiv 𝕜 (fun y => c + f y) x = fderiv 𝕜 f x := by
  simp only [add_comm c, fderiv_add_const]

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


variable {ι : Type*} {u : Finset ι} {A : ι -> E -> F} {A' : ι -> E ->L[𝕜] F}

@[fun_prop]
/--
theorem `HasStrictFDerivAt.fun_sum` / 定理 `HasStrictFDerivAt.fun_sum`

English:
theorem HasStrictFDerivAt.fun_sum
  given: (h : forall i in u, HasStrictFDerivAt (A i) (A' i) x)
  proof: by
  simp only [hasStrictFDerivAt_iff_isLittleO] at *
  convert! IsLittleO.sum h
  simp [Finset.sum_sub_distrib]

@[fun_prop]

中文:
定理 HasStrictFDerivAt.fun_sum
  条件: (h : 对任意 i in u, HasStrictFDerivAt (A i) (A' i) x)
  证明: by
  simp only [hasStrictFDerivAt_iff_isLittleO] at *
  convert! IsLittleO.sum h
  simp [Finset.sum_sub_distrib]

@[fun_prop]

Depends on / 依赖: Finset, Finset.sum_sub_distrib, IsLittleO, IsLittleO.sum, convert, hasStrictFDerivAt_iff_isLittleO, sum_sub_distrib
-/
theorem HasStrictFDerivAt.fun_sum (h : forall i in u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x := by
  simp only [hasStrictFDerivAt_iff_isLittleO] at *
  convert! IsLittleO.sum h
  simp [Finset.sum_sub_distrib]

@[fun_prop]
/--
theorem `HasStrictFDerivAt.sum` / 定理 `HasStrictFDerivAt.sum`

English:
theorem HasStrictFDerivAt.sum
  given: (h : forall i in u, HasStrictFDerivAt (A i) (A' i) x)
  proof: by
  convert! HasStrictFDerivAt.fun_sum h; simp

中文:
定理 HasStrictFDerivAt.求和
  条件: (h : 对任意 i in u, HasStrictFDerivAt (A i) (A' i) x)
  证明: by
  convert! HasStrictFDerivAt.fun_sum h; simp

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.fun_sum, convert, fun_sum
-/
theorem HasStrictFDerivAt.sum (h : forall i in u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (∑ i in u, A i) (∑ i in u, A' i) x := by
  convert! HasStrictFDerivAt.fun_sum h; simp

/--
theorem `HasFDerivAtFilter.fun_sum` / 定理 `HasFDerivAtFilter.fun_sum`

English:
theorem HasFDerivAtFilter.fun_sum
  given: (h : forall i in u, HasFDerivAtFilter (A i) (A' i) L)
  proof: by
  simp only [hasFDerivAtFilter_iff_isLittleO] at *
  convert! IsLittleO.sum h
  simp

中文:
定理 有FDerivAtFilter.fun_sum
  条件: (h : 对任意 i in u, 有FDerivAtFilter (A i) (A' i) L)
  证明: by
  simp only [hasFDerivAtFilter_iff_isLittleO] at *
  convert! IsLittleO.sum h
  simp

Depends on / 依赖: IsLittleO, IsLittleO.sum, convert, hasFDerivAtFilter_iff_isLittleO
-/
theorem HasFDerivAtFilter.fun_sum (h : forall i in u, HasFDerivAtFilter (A i) (A' i) L) :
    HasFDerivAtFilter (fun y => ∑ i in u, A i y) (∑ i in u, A' i) L := by
  simp only [hasFDerivAtFilter_iff_isLittleO] at *
  convert! IsLittleO.sum h
  simp

/--
theorem `HasFDerivAtFilter.sum` / 定理 `HasFDerivAtFilter.sum`

English:
theorem HasFDerivAtFilter.sum
  given: (h : forall i in u, HasFDerivAtFilter (A i) (A' i) L)
  proof: by
  convert! HasFDerivAtFilter.fun_sum h; simp

@[fun_prop]

中文:
定理 有FDerivAtFilter.求和
  条件: (h : 对任意 i in u, 有FDerivAtFilter (A i) (A' i) L)
  证明: by
  convert! HasFDerivAtFilter.fun_sum h; simp

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.fun_sum, convert, fun_sum
-/
theorem HasFDerivAtFilter.sum (h : forall i in u, HasFDerivAtFilter (A i) (A' i) L) :
    HasFDerivAtFilter (∑ i in u, A i) (∑ i in u, A' i) L := by
  convert! HasFDerivAtFilter.fun_sum h; simp

@[fun_prop]
/--
theorem `HasFDerivWithinAt.fun_sum` / 定理 `HasFDerivWithinAt.fun_sum`

English:
theorem HasFDerivWithinAt.fun_sum
  given: (h : forall i in u, HasFDerivWithinAt (A i) (A' i) s x)
  proof: HasFDerivAtFilter.fun_sum h

@[fun_prop]

中文:
定理 HasFDerivWithinAt.fun_sum
  条件: (h : 对任意 i in u, HasFDerivWithinAt (A i) (A' i) s x)
  证明: HasFDerivAtFilter.fun_sum h

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.fun_sum, fun_sum
-/
theorem HasFDerivWithinAt.fun_sum (h : forall i in u, HasFDerivWithinAt (A i) (A' i) s x) :
    HasFDerivWithinAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) s x :=
  HasFDerivAtFilter.fun_sum h

@[fun_prop]
/--
theorem `HasFDerivWithinAt.sum` / 定理 `HasFDerivWithinAt.sum`

English:
theorem HasFDerivWithinAt.sum
  given: (h : forall i in u, HasFDerivWithinAt (A i) (A' i) s x)
  proof: HasFDerivAtFilter.sum h

@[fun_prop]

中文:
定理 HasFDerivWithinAt.求和
  条件: (h : 对任意 i in u, HasFDerivWithinAt (A i) (A' i) s x)
  证明: HasFDerivAtFilter.sum h

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.sum
-/
theorem HasFDerivWithinAt.sum (h : forall i in u, HasFDerivWithinAt (A i) (A' i) s x) :
    HasFDerivWithinAt (∑ i in u, A i) (∑ i in u, A' i) s x :=
  HasFDerivAtFilter.sum h

@[fun_prop]
/--
theorem `HasFDerivAt.fun_sum` / 定理 `HasFDerivAt.fun_sum`

English:
theorem HasFDerivAt.fun_sum
  given: (h : forall i in u, HasFDerivAt (A i) (A' i) x)
  proof: HasFDerivAtFilter.fun_sum h

@[fun_prop]

中文:
定理 在点处Fréchet可导.fun_sum
  条件: (h : 对任意 i in u, 在点处Fréchet可导 (A i) (A' i) x)
  证明: HasFDerivAtFilter.fun_sum h

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.fun_sum, fun_sum
-/
theorem HasFDerivAt.fun_sum (h : forall i in u, HasFDerivAt (A i) (A' i) x) :
    HasFDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x :=
  HasFDerivAtFilter.fun_sum h

@[fun_prop]
/--
theorem `HasFDerivAt.sum` / 定理 `HasFDerivAt.sum`

English:
theorem HasFDerivAt.sum
  given: (h : forall i in u, HasFDerivAt (A i) (A' i) x)
  proof: HasFDerivAtFilter.sum h

@[fun_prop]

中文:
定理 在点处Fréchet可导.求和
  条件: (h : 对任意 i in u, 在点处Fréchet可导 (A i) (A' i) x)
  证明: HasFDerivAtFilter.sum h

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.sum
-/
theorem HasFDerivAt.sum (h : forall i in u, HasFDerivAt (A i) (A' i) x) :
    HasFDerivAt (∑ i in u, A i) (∑ i in u, A' i) x :=
  HasFDerivAtFilter.sum h

@[fun_prop]
/--
theorem `DifferentiableWithinAt.fun_sum` / 定理 `DifferentiableWithinAt.fun_sum`

English:
theorem DifferentiableWithinAt.fun_sum
  given: (h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x)
  proof: HasFDerivWithinAt.differentiableWithinAt
    HasFDerivWithinAt.fun_sum fun i hi => (h i hi).hasFDerivWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.fun_sum
  条件: (h : 对任意 i in u, DifferentiableWithinAt 𝕜 (A i) s x)
  证明: HasFDerivWithinAt.differentiableWithinAt
    HasFDerivWithinAt.fun_sum fun i hi => (h i hi).hasFDerivWithinAt

@[fun_prop]

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.differentiableWithinAt, HasFDerivWithinAt.fun_sum, differentiableWithinAt, fun_sum, hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.fun_sum (h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x) :
    DifferentiableWithinAt 𝕜 (fun y => ∑ i in u, A i y) s x :=
HasFDerivWithinAt.differentiableWithinAt
    HasFDerivWithinAt.fun_sum fun i hi => (h i hi).hasFDerivWithinAt

@[fun_prop]
/--
theorem `DifferentiableWithinAt.sum` / 定理 `DifferentiableWithinAt.sum`

English:
theorem DifferentiableWithinAt.sum
  given: (h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x)
  proof: HasFDerivWithinAt.differentiableWithinAt
    HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.求和
  条件: (h : 对任意 i in u, DifferentiableWithinAt 𝕜 (A i) s x)
  证明: HasFDerivWithinAt.differentiableWithinAt
    HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt

@[simp, fun_prop]

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.differentiableWithinAt, HasFDerivWithinAt.sum, differentiableWithinAt, hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.sum (h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x) :
    DifferentiableWithinAt 𝕜 (∑ i in u, A i) s x :=
HasFDerivWithinAt.differentiableWithinAt
    HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.fun_sum` / 定理 `DifferentiableAt.fun_sum`

English:
theorem DifferentiableAt.fun_sum
  given: (h : forall i in u, DifferentiableAt 𝕜 (A i) x)
  proof: HasFDerivAt.differentiableAt HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt

@[simp, fun_prop]

中文:
定理 DifferentiableAt.fun_sum
  条件: (h : 对任意 i in u, DifferentiableAt 𝕜 (A i) x)
  证明: HasFDerivAt.differentiableAt HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt

@[simp, fun_prop]

Depends on / 依赖: HasFDerivAt, HasFDerivAt.differentiableAt, HasFDerivAt.fun_sum, differentiableAt, fun_sum, hasFDerivAt
-/
theorem DifferentiableAt.fun_sum (h : forall i in u, DifferentiableAt 𝕜 (A i) x) :
    DifferentiableAt 𝕜 (fun y => ∑ i in u, A i y) x :=
HasFDerivAt.differentiableAt HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.sum` / 定理 `DifferentiableAt.sum`

English:
theorem DifferentiableAt.sum
  given: (h : forall i in u, DifferentiableAt 𝕜 (A i) x)
  proof: HasFDerivAt.differentiableAt HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt

@[fun_prop]

中文:
定理 DifferentiableAt.求和
  条件: (h : 对任意 i in u, DifferentiableAt 𝕜 (A i) x)
  证明: HasFDerivAt.differentiableAt HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt

@[fun_prop]

Depends on / 依赖: HasFDerivAt, HasFDerivAt.differentiableAt, HasFDerivAt.sum, differentiableAt, hasFDerivAt
-/
theorem DifferentiableAt.sum (h : forall i in u, DifferentiableAt 𝕜 (A i) x) :
    DifferentiableAt 𝕜 (∑ i in u, A i) x :=
HasFDerivAt.differentiableAt HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt

@[fun_prop]
/--
theorem `DifferentiableOn.fun_sum` / 定理 `DifferentiableOn.fun_sum`

English:
theorem DifferentiableOn.fun_sum
  given: (h : forall i in u, DifferentiableOn 𝕜 (A i) s)
  proof: fun x hx =>
  DifferentiableWithinAt.fun_sum fun i hi => h i hi x hx

@[fun_prop]

中文:
定理 DifferentiableOn.fun_sum
  条件: (h : 对任意 i in u, DifferentiableOn 𝕜 (A i) s)
  证明: fun x hx =>
  DifferentiableWithinAt.fun_sum fun i hi => h i hi x hx

@[fun_prop]
-/
theorem DifferentiableOn.fun_sum (h : forall i in u, DifferentiableOn 𝕜 (A i) s) :
    DifferentiableOn 𝕜 (fun y => ∑ i in u, A i y) s := fun x hx =>
  DifferentiableWithinAt.fun_sum fun i hi => h i hi x hx

@[fun_prop]
/--
theorem `DifferentiableOn.sum` / 定理 `DifferentiableOn.sum`

English:
theorem DifferentiableOn.sum
  given: (h : forall i in u, DifferentiableOn 𝕜 (A i) s)
  proof: fun x hx =>
  DifferentiableWithinAt.sum fun i hi => h i hi x hx

@[simp, fun_prop]

中文:
定理 DifferentiableOn.求和
  条件: (h : 对任意 i in u, DifferentiableOn 𝕜 (A i) s)
  证明: fun x hx =>
  DifferentiableWithinAt.sum fun i hi => h i hi x hx

@[simp, fun_prop]
-/
theorem DifferentiableOn.sum (h : forall i in u, DifferentiableOn 𝕜 (A i) s) :
    DifferentiableOn 𝕜 (∑ i in u, A i) s := fun x hx =>
  DifferentiableWithinAt.sum fun i hi => h i hi x hx

@[simp, fun_prop]
/--
theorem `Differentiable.fun_sum` / 定理 `Differentiable.fun_sum`

English:
theorem Differentiable.fun_sum
  given: (h : forall i in u, Differentiable 𝕜 (A i))
  proof: fun x => DifferentiableAt.fun_sum fun i hi => h i hi x

@[simp, fun_prop]

中文:
定理 可微.fun_sum
  条件: (h : 对任意 i in u, 可微 𝕜 (A i))
  证明: fun x => DifferentiableAt.fun_sum fun i hi => h i hi x

@[simp, fun_prop]

Depends on / 依赖: DifferentiableAt, DifferentiableAt.fun_sum, fun_sum
-/
theorem Differentiable.fun_sum (h : forall i in u, Differentiable 𝕜 (A i)) :
    Differentiable 𝕜 fun y => ∑ i in u, A i y :=
  fun x => DifferentiableAt.fun_sum fun i hi => h i hi x

@[simp, fun_prop]
/--
theorem `Differentiable.sum` / 定理 `Differentiable.sum`

English:
theorem Differentiable.sum
  given: (h : forall i in u, Differentiable 𝕜 (A i))
  proof: fun x => DifferentiableAt.sum fun i hi => h i hi x

中文:
定理 可微.求和
  条件: (h : 对任意 i in u, 可微 𝕜 (A i))
  证明: fun x => DifferentiableAt.sum fun i hi => h i hi x

Depends on / 依赖: DifferentiableAt, DifferentiableAt.sum
-/
theorem Differentiable.sum (h : forall i in u, Differentiable 𝕜 (A i)) :
    Differentiable 𝕜 (∑ i in u, A i) := fun x => DifferentiableAt.sum fun i hi => h i hi x

/--
theorem `fderivWithin_fun_sum` / 定理 `fderivWithin_fun_sum`

English:
theorem fderivWithin_fun_sum
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (HasFDerivWithinAt.fun_sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

中文:
定理 fderivWithin_fun_sum
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (HasFDerivWithinAt.fun_sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.fun_sum, fderivWithin, fun_sum, hasFDerivWithinAt
-/
theorem fderivWithin_fun_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x) :
    fderivWithin 𝕜 (fun y => ∑ i in u, A i y) s x = ∑ i in u, fderivWithin 𝕜 (A i) s x :=
  (HasFDerivWithinAt.fun_sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

/--
theorem `fderivWithin_sum` / 定理 `fderivWithin_sum`

English:
theorem fderivWithin_sum
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

中文:
定理 fderivWithin_sum
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.sum, fderivWithin, hasFDerivWithinAt
-/
theorem fderivWithin_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x) :
    fderivWithin 𝕜 (∑ i in u, A i) s x = ∑ i in u, fderivWithin 𝕜 (A i) s x :=
  (HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

/--
theorem `fderiv_fun_sum` / 定理 `fderiv_fun_sum`

English:
theorem fderiv_fun_sum
  given: (h : forall i in u, DifferentiableAt 𝕜 (A i) x)
  proof: (HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt).fderiv

中文:
定理 fderiv_fun_sum
  条件: (h : 对任意 i in u, DifferentiableAt 𝕜 (A i) x)
  证明: (HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt).fderiv

Depends on / 依赖: HasFDerivAt, HasFDerivAt.fun_sum, fderiv, fun_sum, hasFDerivAt
-/
theorem fderiv_fun_sum (h : forall i in u, DifferentiableAt 𝕜 (A i) x) :
    fderiv 𝕜 (fun y => ∑ i in u, A i y) x = ∑ i in u, fderiv 𝕜 (A i) x :=
  (HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt).fderiv

/--
theorem `fderiv_sum` / 定理 `fderiv_sum`

English:
theorem fderiv_sum
  given: (h : forall i in u, DifferentiableAt 𝕜 (A i) x)
  proof: (HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt).fderiv

中文:
定理 fderiv_sum
  条件: (h : 对任意 i in u, DifferentiableAt 𝕜 (A i) x)
  证明: (HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt).fderiv

Depends on / 依赖: HasFDerivAt, HasFDerivAt.sum, fderiv, hasFDerivAt
-/
theorem fderiv_sum (h : forall i in u, DifferentiableAt 𝕜 (A i) x) :
    fderiv 𝕜 (∑ i in u, A i) x = ∑ i in u, fderiv 𝕜 (A i) x :=
  (HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt).fderiv

end Sum

section Neg

/-! ### Derivative of the negative of a function -/


@[to_fun]
/--
theorem `HasFDerivAtFilter.neg` / 定理 `HasFDerivAtFilter.neg`

English:
theorem HasFDerivAtFilter.neg
  given: (h : HasFDerivAtFilter f f' L)
  proof: (-1 : F ->L[𝕜] F).hasFDerivAtFilter.comp h tendsto_map

@[to_fun (attr := fun_prop)]

中文:
定理 有FDerivAtFilter.neg
  条件: (h : 有FDerivAtFilter f f' L)
  证明: (-1 : F ->L[𝕜] F).hasFDerivAtFilter.comp h tendsto_map

@[to_fun (attr := fun_prop)]

Depends on / 依赖: hasFDerivAtFilter, hasFDerivAtFilter.comp, tendsto_map
-/
theorem HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f' L) :
    HasFDerivAtFilter (-f) (-f') L :=
  (-1 : F ->L[𝕜] F).hasFDerivAtFilter.comp h tendsto_map

@[to_fun (attr := fun_prop)]
/--
theorem `HasStrictFDerivAt.neg` / 定理 `HasStrictFDerivAt.neg`

English:
theorem HasStrictFDerivAt.neg
  given: (h : HasStrictFDerivAt f f' x)
  proof: HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]

中文:
定理 HasStrictFDerivAt.neg
  条件: (h : HasStrictFDerivAt f f' x)
  证明: HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.neg
-/
theorem HasStrictFDerivAt.neg (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (-f) (-f') x :=
  HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivWithinAt.neg` / 定理 `HasFDerivWithinAt.neg`

English:
theorem HasFDerivWithinAt.neg
  given: (h : HasFDerivWithinAt f f' s x)
  proof: HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]

中文:
定理 HasFDerivWithinAt.neg
  条件: (h : HasFDerivWithinAt f f' s x)
  证明: HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.neg
-/
theorem HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (-f) (-f') s x :=
  HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivAt.neg` / 定理 `HasFDerivAt.neg`

English:
theorem HasFDerivAt.neg
  given: (h : HasFDerivAt f f' x)
  statement: HasFDerivAt (-f) (-f') x
  proof: HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]

中文:
定理 在点处Fréchet可导.neg
  条件: (h : 在点处Fréchet可导 f f' x)
  结论: 在点处Fréchet可导 (-f) (-f') x
  证明: HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.neg
-/
theorem HasFDerivAt.neg (h : HasFDerivAt f f' x) : HasFDerivAt (-f) (-f') x :=
  HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableWithinAt.neg` / 定理 `DifferentiableWithinAt.neg`

English:
theorem DifferentiableWithinAt.neg
  given: (h : DifferentiableWithinAt 𝕜 f s x)
  proof: h.hasFDerivWithinAt.neg.differentiableWithinAt

@[simp]

中文:
定理 DifferentiableWithinAt.neg
  条件: (h : DifferentiableWithinAt 𝕜 f s x)
  证明: h.hasFDerivWithinAt.neg.differentiableWithinAt

@[simp]

Depends on / 依赖: differentiableWithinAt, h.hasFDerivWithinAt.neg.differentiableWithinAt, hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.neg (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (-f) s x :=
  h.hasFDerivWithinAt.neg.differentiableWithinAt

@[simp]
/--
theorem `differentiableWithinAt_fun_neg_iff` / 定理 `differentiableWithinAt_fun_neg_iff`

English:
theorem differentiableWithinAt_fun_neg_iff
  proof: ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]

中文:
定理 differentiableWithinAt_fun_neg_iff
  证明: ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]

Depends on / 依赖: fun_neg, h.fun_neg, h.neg, neg_neg
-/
theorem differentiableWithinAt_fun_neg_iff :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
/--
theorem `differentiableWithinAt_neg_iff` / 定理 `differentiableWithinAt_neg_iff`

English:
theorem differentiableWithinAt_neg_iff
  proof: ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]

中文:
定理 differentiableWithinAt_neg_iff
  证明: ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]

Depends on / 依赖: h.neg, neg_neg
-/
theorem differentiableWithinAt_neg_iff :
    DifferentiableWithinAt 𝕜 (-f) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableAt.neg` / 定理 `DifferentiableAt.neg`

English:
theorem DifferentiableAt.neg
  given: (h : DifferentiableAt 𝕜 f x)
  statement: DifferentiableAt 𝕜 (-f) x
  proof: h.hasFDerivAt.neg.differentiableAt

@[simp]

中文:
定理 DifferentiableAt.neg
  条件: (h : DifferentiableAt 𝕜 f x)
  结论: DifferentiableAt 𝕜 (-f) x
  证明: h.hasFDerivAt.neg.differentiableAt

@[simp]

Depends on / 依赖: differentiableAt, h.hasFDerivAt.neg.differentiableAt, hasFDerivAt
-/
theorem DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (-f) x :=
  h.hasFDerivAt.neg.differentiableAt

@[simp]
/--
theorem `differentiableAt_fun_neg_iff` / 定理 `differentiableAt_fun_neg_iff`

English:
theorem differentiableAt_fun_neg_iff
  proof: ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]

中文:
定理 differentiableAt_fun_neg_iff
  证明: ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]

Depends on / 依赖: fun_neg, h.fun_neg, h.neg, neg_neg
-/
theorem differentiableAt_fun_neg_iff :
    DifferentiableAt 𝕜 (fun y => -f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
/--
theorem `differentiableAt_neg_iff` / 定理 `differentiableAt_neg_iff`

English:
theorem differentiableAt_neg_iff
  statement: DifferentiableAt 𝕜 (-f) x ↔ DifferentiableAt 𝕜 f x
  proof: ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]

中文:
定理 differentiableAt_neg_iff
  结论: DifferentiableAt 𝕜 (-f) x ↔ DifferentiableAt 𝕜 f x
  证明: ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]

Depends on / 依赖: h.neg, neg_neg
-/
theorem differentiableAt_neg_iff : DifferentiableAt 𝕜 (-f) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableOn.neg` / 定理 `DifferentiableOn.neg`

English:
theorem DifferentiableOn.neg
  given: (h : DifferentiableOn 𝕜 f s)
  statement: DifferentiableOn 𝕜 (-f) s
  proof: fun x hx => (h x hx).neg

@[simp]

中文:
定理 DifferentiableOn.neg
  条件: (h : DifferentiableOn 𝕜 f s)
  结论: DifferentiableOn 𝕜 (-f) s
  证明: fun x hx => (h x hx).neg

@[simp]
-/
theorem DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (-f) s :=
  fun x hx => (h x hx).neg

@[simp]
/--
theorem `differentiableOn_fun_neg_iff` / 定理 `differentiableOn_fun_neg_iff`

English:
theorem differentiableOn_fun_neg_iff
  proof: ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]

中文:
定理 differentiableOn_fun_neg_iff
  证明: ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]

Depends on / 依赖: fun_neg, h.fun_neg, h.neg, neg_neg
-/
theorem differentiableOn_fun_neg_iff :
    DifferentiableOn 𝕜 (fun y => -f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
/--
theorem `differentiableOn_neg_iff` / 定理 `differentiableOn_neg_iff`

English:
theorem differentiableOn_neg_iff
  statement: DifferentiableOn 𝕜 (-f) s ↔ DifferentiableOn 𝕜 f s
  proof: ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]

中文:
定理 differentiableOn_neg_iff
  结论: DifferentiableOn 𝕜 (-f) s ↔ DifferentiableOn 𝕜 f s
  证明: ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]

Depends on / 依赖: h.neg, neg_neg
-/
theorem differentiableOn_neg_iff : DifferentiableOn 𝕜 (-f) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]
/--
theorem `Differentiable.neg` / 定理 `Differentiable.neg`

English:
theorem Differentiable.neg
  given: (h : Differentiable 𝕜 f)
  statement: Differentiable 𝕜 (-f)
  proof: fun x =>
  (h x).neg

@[simp]

中文:
定理 可微.neg
  条件: (h : 可微 𝕜 f)
  结论: 可微 𝕜 (-f)
  证明: fun x =>
  (h x).neg

@[simp]
-/
theorem Differentiable.neg (h : Differentiable 𝕜 f) : Differentiable 𝕜 (-f) := fun x =>
  (h x).neg

@[simp]
/--
theorem `differentiable_fun_neg_iff` / 定理 `differentiable_fun_neg_iff`

English:
theorem differentiable_fun_neg_iff
  statement: (Differentiable 𝕜 fun y => -f y) ↔ Differentiable 𝕜 f
  proof: ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]

中文:
定理 differentiable_fun_neg_iff
  结论: (可微 𝕜 fun y => -f y) ↔ 可微 𝕜 f
  证明: ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]

Depends on / 依赖: fun_neg, h.fun_neg, h.neg, neg_neg
-/
theorem differentiable_fun_neg_iff : (Differentiable 𝕜 fun y => -f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
/--
theorem `differentiable_neg_iff` / 定理 `differentiable_neg_iff`

English:
theorem differentiable_neg_iff
  statement: Differentiable 𝕜 (-f) ↔ Differentiable 𝕜 f
  proof: ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

中文:
定理 differentiable_neg_iff
  结论: 可微 𝕜 (-f) ↔ 可微 𝕜 f
  证明: ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

Depends on / 依赖: h.neg, neg_neg
-/
theorem differentiable_neg_iff : Differentiable 𝕜 (-f) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

/--
theorem `fderivWithin_fun_neg` / 定理 `fderivWithin_fun_neg`

English:
theorem fderivWithin_fun_neg
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact h.hasFDerivWithinAt.neg.fderivWithin hxs
  · rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    simpa

中文:
定理 fderivWithin_fun_neg
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact h.hasFDerivWithinAt.neg.fderivWithin hxs
  · rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    simpa

Depends on / 依赖: DifferentiableWithinAt, fderivWithin, fderivWithin_zero_of_not_differentiableWithinAt, h.hasFDerivWithinAt.neg.fderivWithin, hasFDerivWithinAt, neg_zero
-/
theorem fderivWithin_fun_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => -f y) s x = -fderivWithin 𝕜 f s x := by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact h.hasFDerivWithinAt.neg.fderivWithin hxs
  · rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    simpa

/--
theorem `fderivWithin_neg` / 定理 `fderivWithin_neg`

English:
theorem fderivWithin_neg
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: fderivWithin_fun_neg hxs

@[simp]

中文:
定理 fderivWithin_neg
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: fderivWithin_fun_neg hxs

@[simp]

Depends on / 依赖: fderivWithin_fun_neg
-/
theorem fderivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (-f) s x = -fderivWithin 𝕜 f s x :=
  fderivWithin_fun_neg hxs

@[simp]
/--
theorem `fderiv_fun_neg` / 定理 `fderiv_fun_neg`

English:
theorem fderiv_fun_neg
  statement: fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 f x
  proof: by
  simp only [← fderivWithin_univ, fderivWithin_fun_neg uniqueDiffWithinAt_univ]

中文:
定理 fderiv_fun_neg
  结论: fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 f x
  证明: by
  simp only [← fderivWithin_univ, fderivWithin_fun_neg uniqueDiffWithinAt_univ]

Depends on / 依赖: fderivWithin_fun_neg, fderivWithin_univ, uniqueDiffWithinAt_univ
-/
theorem fderiv_fun_neg : fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_fun_neg uniqueDiffWithinAt_univ]

/--
theorem `fderiv_neg` / 定理 `fderiv_neg`

English:
theorem fderiv_neg
  statement: fderiv 𝕜 (-f) x = -fderiv 𝕜 f x
  proof: fderiv_fun_neg

中文:
定理 fderiv_neg
  结论: fderiv 𝕜 (-f) x = -fderiv 𝕜 f x
  证明: fderiv_fun_neg

Depends on / 依赖: fderiv_fun_neg
-/
theorem fderiv_neg : fderiv 𝕜 (-f) x = -fderiv 𝕜 f x :=
  fderiv_fun_neg

end Neg

section Sub

/-! ### Derivative of the difference of two functions -/


@[to_fun]
/--
theorem `HasFDerivAtFilter.sub` / 定理 `HasFDerivAtFilter.sub`

English:
theorem HasFDerivAtFilter.sub
  given: (hf : HasFDerivAtFilter f f' L) (hg : HasFDerivAtFilter g g' L)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun (attr := fun_prop)]

中文:
定理 有FDerivAtFilter.sub
  条件: (hf : 有FDerivAtFilter f f' L) (hg : 有FDerivAtFilter g g' L)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun (attr := fun_prop)]

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem HasFDerivAtFilter.sub (hf : HasFDerivAtFilter f f' L) (hg : HasFDerivAtFilter g g' L) :
    HasFDerivAtFilter (f - g) (f' - g') L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun (attr := fun_prop)]
/--
theorem `HasStrictFDerivAt.sub` / 定理 `HasStrictFDerivAt.sub`

English:
theorem HasStrictFDerivAt.sub
  given: (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
  proof: HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]

中文:
定理 HasStrictFDerivAt.sub
  条件: (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
  证明: HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.sub
-/
theorem HasStrictFDerivAt.sub (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (f - g) (f' - g') x :=
  HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivWithinAt.sub` / 定理 `HasFDerivWithinAt.sub`

English:
theorem HasFDerivWithinAt.sub
  statement: (hf : HasFDerivWithinAt f f' s x)
  proof: HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]

中文:
定理 HasFDerivWithinAt.sub
  结论: (hf : HasFDerivWithinAt f f' s x)
  证明: HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.sub
-/
theorem HasFDerivWithinAt.sub (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f - g) (f' - g') s x :=
  HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivAt.sub` / 定理 `HasFDerivAt.sub`

English:
theorem HasFDerivAt.sub
  given: (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
  proof: HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]

中文:
定理 在点处Fréchet可导.sub
  条件: (hf : 在点处Fréchet可导 f f' x) (hg : 在点处Fréchet可导 g g' x)
  证明: HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.sub
-/
theorem HasFDerivAt.sub (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (f - g) (f' - g') x :=
  HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableWithinAt.sub` / 定理 `DifferentiableWithinAt.sub`

English:
theorem DifferentiableWithinAt.sub
  statement: (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]

中文:
定理 DifferentiableWithinAt.sub
  结论: (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.sub, hg.hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (f - g) s x :=
  (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
/--
theorem `DifferentiableAt.sub` / 定理 `DifferentiableAt.sub`

English:
theorem DifferentiableAt.sub
  given: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  proof: (hf.hasFDerivAt.sub hg.hasFDerivAt).differentiableAt

@[to_fun (attr := simp)]

中文:
定理 DifferentiableAt.sub
  条件: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  证明: (hf.hasFDerivAt.sub hg.hasFDerivAt).differentiableAt

@[to_fun (attr := simp)]

Depends on / 依赖: differentiableAt, hasFDerivAt, hf.hasFDerivAt.sub, hg.hasFDerivAt
-/
theorem DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f - g) x :=
  (hf.hasFDerivAt.sub hg.hasFDerivAt).differentiableAt

@[to_fun (attr := simp)]
/--
lemma `DifferentiableAt.add_iff_left` / 引理 `DifferentiableAt.add_iff_left`

English:
lemma DifferentiableAt.add_iff_left
  given: (hg : DifferentiableAt 𝕜 g x)
  proof: by
  refine ⟨fun h => ?_, fun hf => hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]

中文:
引理 DifferentiableAt.add_iff_left
  条件: (hg : DifferentiableAt 𝕜 g x)
  证明: by
  refine ⟨fun h => ?_, fun hf => hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]

Depends on / 依赖: add_sub_cancel_right, h.sub, hf.add
-/
lemma DifferentiableAt.add_iff_left (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f + g) x ↔ DifferentiableAt 𝕜 f x := by
  refine ⟨fun h => ?_, fun hf => hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]
/--
lemma `DifferentiableAt.add_iff_right` / 引理 `DifferentiableAt.add_iff_right`

English:
lemma DifferentiableAt.add_iff_right
  given: (hg : DifferentiableAt 𝕜 f x)
  proof: by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]

中文:
引理 DifferentiableAt.add_iff_right
  条件: (hg : DifferentiableAt 𝕜 f x)
  证明: by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]

Depends on / 依赖: add_comm, add_iff_left, hg.add_iff_left
-/
lemma DifferentiableAt.add_iff_right (hg : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (f + g) x ↔ DifferentiableAt 𝕜 g x := by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]
/--
lemma `DifferentiableAt.sub_iff_left` / 引理 `DifferentiableAt.sub_iff_left`

English:
lemma DifferentiableAt.sub_iff_left
  given: (hg : DifferentiableAt 𝕜 g x)
  proof: by
  simp only [sub_eq_add_neg, differentiableAt_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]

中文:
引理 DifferentiableAt.sub_iff_left
  条件: (hg : DifferentiableAt 𝕜 g x)
  证明: by
  simp only [sub_eq_add_neg, differentiableAt_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]

Depends on / 依赖: add_iff_left, differentiableAt_neg_iff, sub_eq_add_neg
-/
lemma DifferentiableAt.sub_iff_left (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f - g) x ↔ DifferentiableAt 𝕜 f x := by
  simp only [sub_eq_add_neg, differentiableAt_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]
/--
lemma `DifferentiableAt.sub_iff_right` / 引理 `DifferentiableAt.sub_iff_right`

English:
lemma DifferentiableAt.sub_iff_right
  given: (hg : DifferentiableAt 𝕜 f x)
  proof: by
  simp only [sub_eq_add_neg, hg, add_iff_right, differentiableAt_neg_iff]

@[to_fun (attr := fun_prop)]

中文:
引理 DifferentiableAt.sub_iff_right
  条件: (hg : DifferentiableAt 𝕜 f x)
  证明: by
  simp only [sub_eq_add_neg, hg, add_iff_right, differentiableAt_neg_iff]

@[to_fun (attr := fun_prop)]

Depends on / 依赖: add_iff_right, differentiableAt_neg_iff, sub_eq_add_neg
-/
lemma DifferentiableAt.sub_iff_right (hg : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (f - g) x ↔ DifferentiableAt 𝕜 g x := by
  simp only [sub_eq_add_neg, hg, add_iff_right, differentiableAt_neg_iff]

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableOn.sub` / 定理 `DifferentiableOn.sub`

English:
theorem DifferentiableOn.sub
  given: (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
  proof: fun x hx => (hf x hx).sub (hg x hx)

@[to_fun (attr := simp)]

中文:
定理 DifferentiableOn.sub
  条件: (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
  证明: fun x hx => (hf x hx).sub (hg x hx)

@[to_fun (attr := simp)]
-/
theorem DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f - g) s := fun x hx => (hf x hx).sub (hg x hx)

@[to_fun (attr := simp)]
/--
lemma `DifferentiableOn.add_iff_left` / 引理 `DifferentiableOn.add_iff_left`

English:
lemma DifferentiableOn.add_iff_left
  given: (hg : DifferentiableOn 𝕜 g s)
  proof: by
  refine ⟨fun h => ?_, fun hf => hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]

中文:
引理 DifferentiableOn.add_iff_left
  条件: (hg : DifferentiableOn 𝕜 g s)
  证明: by
  refine ⟨fun h => ?_, fun hf => hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]

Depends on / 依赖: add_sub_cancel_right, h.sub, hf.add
-/
lemma DifferentiableOn.add_iff_left (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f + g) s ↔ DifferentiableOn 𝕜 f s := by
  refine ⟨fun h => ?_, fun hf => hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]
/--
lemma `DifferentiableOn.add_iff_right` / 引理 `DifferentiableOn.add_iff_right`

English:
lemma DifferentiableOn.add_iff_right
  given: (hg : DifferentiableOn 𝕜 f s)
  proof: by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]

中文:
引理 DifferentiableOn.add_iff_right
  条件: (hg : DifferentiableOn 𝕜 f s)
  证明: by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]

Depends on / 依赖: add_comm, add_iff_left, hg.add_iff_left
-/
lemma DifferentiableOn.add_iff_right (hg : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (f + g) s ↔ DifferentiableOn 𝕜 g s := by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]
/--
lemma `DifferentiableOn.sub_iff_left` / 引理 `DifferentiableOn.sub_iff_left`

English:
lemma DifferentiableOn.sub_iff_left
  given: (hg : DifferentiableOn 𝕜 g s)
  proof: by
  simp only [sub_eq_add_neg, differentiableOn_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]

中文:
引理 DifferentiableOn.sub_iff_left
  条件: (hg : DifferentiableOn 𝕜 g s)
  证明: by
  simp only [sub_eq_add_neg, differentiableOn_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]

Depends on / 依赖: add_iff_left, differentiableOn_neg_iff, sub_eq_add_neg
-/
lemma DifferentiableOn.sub_iff_left (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f - g) s ↔ DifferentiableOn 𝕜 f s := by
  simp only [sub_eq_add_neg, differentiableOn_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]
/--
lemma `DifferentiableOn.sub_iff_right` / 引理 `DifferentiableOn.sub_iff_right`

English:
lemma DifferentiableOn.sub_iff_right
  given: (hg : DifferentiableOn 𝕜 f s)
  proof: by
  simp only [sub_eq_add_neg, differentiableOn_neg_iff, hg, add_iff_right]

@[to_fun (attr := simp, fun_prop)]

中文:
引理 DifferentiableOn.sub_iff_right
  条件: (hg : DifferentiableOn 𝕜 f s)
  证明: by
  simp only [sub_eq_add_neg, differentiableOn_neg_iff, hg, add_iff_right]

@[to_fun (attr := simp, fun_prop)]

Depends on / 依赖: add_iff_right, differentiableOn_neg_iff, sub_eq_add_neg
-/
lemma DifferentiableOn.sub_iff_right (hg : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (f - g) s ↔ DifferentiableOn 𝕜 g s := by
  simp only [sub_eq_add_neg, differentiableOn_neg_iff, hg, add_iff_right]

@[to_fun (attr := simp, fun_prop)]
/--
theorem `Differentiable.sub` / 定理 `Differentiable.sub`

English:
theorem Differentiable.sub
  given: (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g)
  proof: fun x => (hf x).sub (hg x)

@[to_fun (attr := simp)]

中文:
定理 可微.sub
  条件: (hf : 可微 𝕜 f) (hg : 可微 𝕜 g)
  证明: fun x => (hf x).sub (hg x)

@[to_fun (attr := simp)]
-/
theorem Differentiable.sub (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f - g) := fun x => (hf x).sub (hg x)

@[to_fun (attr := simp)]
/--
lemma `Differentiable.add_iff_left` / 引理 `Differentiable.add_iff_left`

English:
lemma Differentiable.add_iff_left
  given: (hg : Differentiable 𝕜 g)
  proof: by
  refine ⟨fun h => ?_, fun hf => hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]

中文:
引理 可微.add_iff_left
  条件: (hg : 可微 𝕜 g)
  证明: by
  refine ⟨fun h => ?_, fun hf => hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]

Depends on / 依赖: add_sub_cancel_right, h.sub, hf.add
-/
lemma Differentiable.add_iff_left (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f + g) ↔ Differentiable 𝕜 f := by
  refine ⟨fun h => ?_, fun hf => hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]
/--
lemma `Differentiable.add_iff_right` / 引理 `Differentiable.add_iff_right`

English:
lemma Differentiable.add_iff_right
  given: (hg : Differentiable 𝕜 f)
  proof: by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]

中文:
引理 可微.add_iff_right
  条件: (hg : 可微 𝕜 f)
  证明: by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]

Depends on / 依赖: add_comm, add_iff_left, hg.add_iff_left
-/
lemma Differentiable.add_iff_right (hg : Differentiable 𝕜 f) :
    Differentiable 𝕜 (f + g) ↔ Differentiable 𝕜 g := by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]
/--
lemma `Differentiable.sub_iff_left` / 引理 `Differentiable.sub_iff_left`

English:
lemma Differentiable.sub_iff_left
  given: (hg : Differentiable 𝕜 g)
  proof: by
  simp only [sub_eq_add_neg, differentiable_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]

中文:
引理 可微.sub_iff_left
  条件: (hg : 可微 𝕜 g)
  证明: by
  simp only [sub_eq_add_neg, differentiable_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]

Depends on / 依赖: add_iff_left, differentiable_neg_iff, sub_eq_add_neg
-/
lemma Differentiable.sub_iff_left (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f - g) ↔ Differentiable 𝕜 f := by
  simp only [sub_eq_add_neg, differentiable_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]
/--
lemma `Differentiable.sub_iff_right` / 引理 `Differentiable.sub_iff_right`

English:
lemma Differentiable.sub_iff_right
  given: (hg : Differentiable 𝕜 f)
  proof: by
  simp only [sub_eq_add_neg, differentiable_neg_iff, hg, add_iff_right]

中文:
引理 可微.sub_iff_right
  条件: (hg : 可微 𝕜 f)
  证明: by
  simp only [sub_eq_add_neg, differentiable_neg_iff, hg, add_iff_right]

Depends on / 依赖: add_iff_right, differentiable_neg_iff, sub_eq_add_neg
-/
lemma Differentiable.sub_iff_right (hg : Differentiable 𝕜 f) :
    Differentiable 𝕜 (f - g) ↔ Differentiable 𝕜 g := by
  simp only [sub_eq_add_neg, differentiable_neg_iff, hg, add_iff_right]

/--
theorem `fderivWithin_fun_sub` / 定理 `fderivWithin_fun_sub`

English:
theorem fderivWithin_fun_sub
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).fderivWithin hxs

中文:
定理 fderivWithin_fun_sub
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.sub, hg.hasFDerivWithinAt
-/
theorem fderivWithin_fun_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y - g y) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x :=
  (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).fderivWithin hxs

/--
theorem `fderivWithin_sub` / 定理 `fderivWithin_sub`

English:
theorem fderivWithin_sub
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: fderivWithin_fun_sub hxs hf hg

中文:
定理 fderivWithin_sub
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: fderivWithin_fun_sub hxs hf hg

Depends on / 依赖: fderivWithin_fun_sub
-/
theorem fderivWithin_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (f - g) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x :=
  fderivWithin_fun_sub hxs hf hg

/--
theorem `fderiv_fun_sub` / 定理 `fderiv_fun_sub`

English:
theorem fderiv_fun_sub
  given: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  proof: (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv

中文:
定理 fderiv_fun_sub
  条件: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  证明: (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hf.hasFDerivAt.sub, hg.hasFDerivAt
-/
theorem fderiv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv

/--
theorem `fderiv_sub` / 定理 `fderiv_sub`

English:
theorem fderiv_sub
  given: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  proof: fderiv_fun_sub hf hg

@[simp]

中文:
定理 fderiv_sub
  条件: (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
  证明: fderiv_fun_sub hf hg

@[simp]

Depends on / 依赖: fderiv_fun_sub
-/
theorem fderiv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (f - g) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  fderiv_fun_sub hf hg

@[simp]
/--
theorem `hasFDerivAtFilter_sub_const_iff` / 定理 `hasFDerivAtFilter_sub_const_iff`

English:
theorem hasFDerivAtFilter_sub_const_iff
  given: (c : F)
  proof: by
  simp only [sub_eq_add_neg, hasFDerivAtFilter_add_const_iff]

alias ⟨_, HasFDerivAtFilter.sub_const⟩ := hasFDerivAtFilter_sub_const_iff

@[simp]

中文:
定理 hasFDerivAtFilter_sub_const_iff
  条件: (c : F)
  证明: by
  simp only [sub_eq_add_neg, hasFDerivAtFilter_add_const_iff]

alias ⟨_, HasFDerivAtFilter.sub_const⟩ := hasFDerivAtFilter_sub_const_iff

@[simp]

Depends on / 依赖: hasFDerivAtFilter_add_const_iff, sub_eq_add_neg
-/
theorem hasFDerivAtFilter_sub_const_iff (c : F) :
    HasFDerivAtFilter (f · - c) f' L ↔ HasFDerivAtFilter f f' L := by
  simp only [sub_eq_add_neg, hasFDerivAtFilter_add_const_iff]

alias ⟨_, HasFDerivAtFilter.sub_const⟩ := hasFDerivAtFilter_sub_const_iff

@[simp]
/--
theorem `hasStrictFDerivAt_sub_const_iff` / 定理 `hasStrictFDerivAt_sub_const_iff`

English:
theorem hasStrictFDerivAt_sub_const_iff
  given: (c : F)
  proof: hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.sub_const⟩ := hasStrictFDerivAt_sub_const_iff

@[simp]

中文:
定理 hasStrictFDerivAt_sub_const_iff
  条件: (c : F)
  证明: hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.sub_const⟩ := hasStrictFDerivAt_sub_const_iff

@[simp]

Depends on / 依赖: hasFDerivAtFilter_sub_const_iff
-/
theorem hasStrictFDerivAt_sub_const_iff (c : F) :
    HasStrictFDerivAt (f · - c) f' x ↔ HasStrictFDerivAt f f' x :=
  hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.sub_const⟩ := hasStrictFDerivAt_sub_const_iff

@[simp]
/--
theorem `hasFDerivWithinAt_sub_const_iff` / 定理 `hasFDerivWithinAt_sub_const_iff`

English:
theorem hasFDerivWithinAt_sub_const_iff
  given: (c : F)
  proof: hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.sub_const⟩ := hasFDerivWithinAt_sub_const_iff

@[simp]

中文:
定理 hasFDerivWithinAt_sub_const_iff
  条件: (c : F)
  证明: hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.sub_const⟩ := hasFDerivWithinAt_sub_const_iff

@[simp]

Depends on / 依赖: hasFDerivAtFilter_sub_const_iff
-/
theorem hasFDerivWithinAt_sub_const_iff (c : F) :
    HasFDerivWithinAt (f · - c) f' s x ↔ HasFDerivWithinAt f f' s x :=
  hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.sub_const⟩ := hasFDerivWithinAt_sub_const_iff

@[simp]
/--
theorem `hasFDerivAt_sub_const_iff` / 定理 `hasFDerivAt_sub_const_iff`

English:
theorem hasFDerivAt_sub_const_iff
  given: (c : F)
  statement: HasFDerivAt (f · - c) f' x ↔ HasFDerivAt f f' x
  proof: hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.sub_const⟩ := hasFDerivAt_sub_const_iff

@[fun_prop]

中文:
定理 hasFDerivAt_sub_const_iff
  条件: (c : F)
  结论: 在点处Fréchet可导 (f · - c) f' x ↔ 在点处Fréchet可导 f f' x
  证明: hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.sub_const⟩ := hasFDerivAt_sub_const_iff

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_sub_const_iff
-/
theorem hasFDerivAt_sub_const_iff (c : F) : HasFDerivAt (f · - c) f' x ↔ HasFDerivAt f f' x :=
  hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.sub_const⟩ := hasFDerivAt_sub_const_iff

@[fun_prop]
/--
theorem `hasStrictFDerivAt_sub_const` / 定理 `hasStrictFDerivAt_sub_const`

English:
theorem hasStrictFDerivAt_sub_const
  given: {x : F} (c : F)
  statement: HasStrictFDerivAt (· - c) (.id 𝕜 F) x
  proof: (hasStrictFDerivAt_id x).sub_const c

@[fun_prop]

中文:
定理 hasStrictFDerivAt_sub_const
  条件: {x : F} (c : F)
  结论: HasStrictFDerivAt (· - c) (.id 𝕜 F) x
  证明: (hasStrictFDerivAt_id x).sub_const c

@[fun_prop]

Depends on / 依赖: hasStrictFDerivAt_id, sub_const
-/
theorem hasStrictFDerivAt_sub_const {x : F} (c : F) : HasStrictFDerivAt (· - c) (.id 𝕜 F) x :=
  (hasStrictFDerivAt_id x).sub_const c

@[fun_prop]
/--
theorem `hasFDerivAt_sub_const` / 定理 `hasFDerivAt_sub_const`

English:
theorem hasFDerivAt_sub_const
  given: {x : F} (c : F)
  statement: HasFDerivAt (· - c) (.id 𝕜 F) x
  proof: (hasFDerivAt_id x).sub_const c

@[fun_prop]

中文:
定理 hasFDerivAt_sub_const
  条件: {x : F} (c : F)
  结论: 在点处Fréchet可导 (· - c) (.id 𝕜 F) x
  证明: (hasFDerivAt_id x).sub_const c

@[fun_prop]

Depends on / 依赖: hasFDerivAt_id, sub_const
-/
theorem hasFDerivAt_sub_const {x : F} (c : F) : HasFDerivAt (· - c) (.id 𝕜 F) x :=
  (hasFDerivAt_id x).sub_const c

@[fun_prop]
/--
theorem `DifferentiableWithinAt.sub_const` / 定理 `DifferentiableWithinAt.sub_const`

English:
theorem DifferentiableWithinAt.sub_const
  given: (hf : DifferentiableWithinAt 𝕜 f s x) (c : F)
  proof: (hf.hasFDerivWithinAt.sub_const c).differentiableWithinAt

@[simp]

中文:
定理 DifferentiableWithinAt.sub_const
  条件: (hf : DifferentiableWithinAt 𝕜 f s x) (c : F)
  证明: (hf.hasFDerivWithinAt.sub_const c).differentiableWithinAt

@[simp]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.sub_const, sub_const
-/
theorem DifferentiableWithinAt.sub_const (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y - c) s x :=
  (hf.hasFDerivWithinAt.sub_const c).differentiableWithinAt

@[simp]
/--
theorem `differentiableWithinAt_sub_const_iff` / 定理 `differentiableWithinAt_sub_const_iff`

English:
theorem differentiableWithinAt_sub_const_iff
  given: (c : F)
  proof: by
  simp only [sub_eq_add_neg, differentiableWithinAt_add_const_iff]

@[fun_prop]

中文:
定理 differentiableWithinAt_sub_const_iff
  条件: (c : F)
  证明: by
  simp only [sub_eq_add_neg, differentiableWithinAt_add_const_iff]

@[fun_prop]

Depends on / 依赖: differentiableWithinAt_add_const_iff, sub_eq_add_neg
-/
theorem differentiableWithinAt_sub_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y - c) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [sub_eq_add_neg, differentiableWithinAt_add_const_iff]

@[fun_prop]
/--
theorem `DifferentiableAt.sub_const` / 定理 `DifferentiableAt.sub_const`

English:
theorem DifferentiableAt.sub_const
  given: (hf : DifferentiableAt 𝕜 f x) (c : F)
  proof: (hf.hasFDerivAt.sub_const c).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.sub_const
  条件: (hf : DifferentiableAt 𝕜 f x) (c : F)
  证明: (hf.hasFDerivAt.sub_const c).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt, hf.hasFDerivAt.sub_const, sub_const
-/
theorem DifferentiableAt.sub_const (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => f y - c) x :=
  (hf.hasFDerivAt.sub_const c).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableOn.sub_const` / 定理 `DifferentiableOn.sub_const`

English:
theorem DifferentiableOn.sub_const
  given: (hf : DifferentiableOn 𝕜 f s) (c : F)
  proof: fun x hx => (hf x hx).sub_const c

@[fun_prop]

中文:
定理 DifferentiableOn.sub_const
  条件: (hf : DifferentiableOn 𝕜 f s) (c : F)
  证明: fun x hx => (hf x hx).sub_const c

@[fun_prop]

Depends on / 依赖: sub_const
-/
theorem DifferentiableOn.sub_const (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => f y - c) s := fun x hx => (hf x hx).sub_const c

@[fun_prop]
/--
theorem `Differentiable.sub_const` / 定理 `Differentiable.sub_const`

English:
theorem Differentiable.sub_const
  given: (hf : Differentiable 𝕜 f) (c : F)
  proof: fun x => (hf x).sub_const c

中文:
定理 可微.sub_const
  条件: (hf : 可微 𝕜 f) (c : F)
  证明: fun x => (hf x).sub_const c

Depends on / 依赖: sub_const
-/
theorem Differentiable.sub_const (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => f y - c := fun x => (hf x).sub_const c

/--
theorem `fderivWithin_sub_const` / 定理 `fderivWithin_sub_const`

English:
theorem fderivWithin_sub_const
  given: (c : F)
  proof: by
  simp only [sub_eq_add_neg, fderivWithin_add_const]

中文:
定理 fderivWithin_sub_const
  条件: (c : F)
  证明: by
  simp only [sub_eq_add_neg, fderivWithin_add_const]

Depends on / 依赖: fderivWithin_add_const, sub_eq_add_neg
-/
theorem fderivWithin_sub_const (c : F) :
    fderivWithin 𝕜 (fun y => f y - c) s x = fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_add_const]

/--
theorem `fderiv_sub_const` / 定理 `fderiv_sub_const`

English:
theorem fderiv_sub_const
  given: (c : F)
  statement: fderiv 𝕜 (fun y => f y - c) x = fderiv 𝕜 f x
  proof: by
  simp only [sub_eq_add_neg, fderiv_add_const]

中文:
定理 fderiv_sub_const
  条件: (c : F)
  结论: fderiv 𝕜 (fun y => f y - c) x = fderiv 𝕜 f x
  证明: by
  simp only [sub_eq_add_neg, fderiv_add_const]

Depends on / 依赖: fderiv_add_const, sub_eq_add_neg
-/
theorem fderiv_sub_const (c : F) : fderiv 𝕜 (fun y => f y - c) x = fderiv 𝕜 f x := by
  simp only [sub_eq_add_neg, fderiv_add_const]

/--
theorem `HasFDerivAtFilter.const_sub` / 定理 `HasFDerivAtFilter.const_sub`

English:
theorem HasFDerivAtFilter.const_sub
  given: (hf : HasFDerivAtFilter f f' L) (c : F)
  proof: by
  simpa only [sub_eq_add_neg] using! hf.neg.const_add c

@[fun_prop]

中文:
定理 有FDerivAtFilter.const_sub
  条件: (hf : 有FDerivAtFilter f f' L) (c : F)
  证明: by
  simpa only [sub_eq_add_neg] using! hf.neg.const_add c

@[fun_prop]

Depends on / 依赖: const_add, hf.neg.const_add, sub_eq_add_neg
-/
theorem HasFDerivAtFilter.const_sub (hf : HasFDerivAtFilter f f' L) (c : F) :
    HasFDerivAtFilter (fun x => c - f x) (-f') L := by
  simpa only [sub_eq_add_neg] using! hf.neg.const_add c

@[fun_prop]
/--
theorem `HasStrictFDerivAt.const_sub` / 定理 `HasStrictFDerivAt.const_sub`

English:
theorem HasStrictFDerivAt.const_sub
  given: (hf : HasStrictFDerivAt f f' x) (c : F)
  proof: HasFDerivAtFilter.const_sub hf c

@[fun_prop]

中文:
定理 HasStrictFDerivAt.const_sub
  条件: (hf : HasStrictFDerivAt f f' x) (c : F)
  证明: HasFDerivAtFilter.const_sub hf c

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.const_sub, const_sub
-/
theorem HasStrictFDerivAt.const_sub (hf : HasStrictFDerivAt f f' x) (c : F) :
    HasStrictFDerivAt (fun x => c - f x) (-f') x :=
  HasFDerivAtFilter.const_sub hf c

@[fun_prop]
/--
theorem `HasFDerivWithinAt.const_sub` / 定理 `HasFDerivWithinAt.const_sub`

English:
theorem HasFDerivWithinAt.const_sub
  given: (hf : HasFDerivWithinAt f f' s x) (c : F)
  proof: HasFDerivAtFilter.const_sub hf c

@[fun_prop]

中文:
定理 HasFDerivWithinAt.const_sub
  条件: (hf : HasFDerivWithinAt f f' s x) (c : F)
  证明: HasFDerivAtFilter.const_sub hf c

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.const_sub, const_sub
-/
theorem HasFDerivWithinAt.const_sub (hf : HasFDerivWithinAt f f' s x) (c : F) :
    HasFDerivWithinAt (fun x => c - f x) (-f') s x :=
  HasFDerivAtFilter.const_sub hf c

@[fun_prop]
/--
theorem `HasFDerivAt.const_sub` / 定理 `HasFDerivAt.const_sub`

English:
theorem HasFDerivAt.const_sub
  given: (hf : HasFDerivAt f f' x) (c : F)
  proof: HasFDerivAtFilter.const_sub hf c

@[fun_prop]

中文:
定理 在点处Fréchet可导.const_sub
  条件: (hf : 在点处Fréchet可导 f f' x) (c : F)
  证明: HasFDerivAtFilter.const_sub hf c

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.const_sub, const_sub
-/
theorem HasFDerivAt.const_sub (hf : HasFDerivAt f f' x) (c : F) :
    HasFDerivAt (fun x => c - f x) (-f') x :=
  HasFDerivAtFilter.const_sub hf c

@[fun_prop]
/--
theorem `DifferentiableWithinAt.const_sub` / 定理 `DifferentiableWithinAt.const_sub`

English:
theorem DifferentiableWithinAt.const_sub
  given: (hf : DifferentiableWithinAt 𝕜 f s x) (c : F)
  proof: (hf.hasFDerivWithinAt.const_sub c).differentiableWithinAt

@[simp]

中文:
定理 DifferentiableWithinAt.const_sub
  条件: (hf : DifferentiableWithinAt 𝕜 f s x) (c : F)
  证明: (hf.hasFDerivWithinAt.const_sub c).differentiableWithinAt

@[simp]

Depends on / 依赖: const_sub, differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.const_sub
-/
theorem DifferentiableWithinAt.const_sub (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c - f y) s x :=
  (hf.hasFDerivWithinAt.const_sub c).differentiableWithinAt

@[simp]
/--
theorem `differentiableWithinAt_const_sub_iff` / 定理 `differentiableWithinAt_const_sub_iff`

English:
theorem differentiableWithinAt_const_sub_iff
  given: (c : F)
  proof: by
  simp [sub_eq_add_neg]

@[fun_prop]

中文:
定理 differentiableWithinAt_const_sub_iff
  条件: (c : F)
  证明: by
  simp [sub_eq_add_neg]

@[fun_prop]

Depends on / 依赖: sub_eq_add_neg
-/
theorem differentiableWithinAt_const_sub_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c - f y) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp [sub_eq_add_neg]

@[fun_prop]
/--
theorem `DifferentiableAt.const_sub` / 定理 `DifferentiableAt.const_sub`

English:
theorem DifferentiableAt.const_sub
  given: (hf : DifferentiableAt 𝕜 f x) (c : F)
  proof: (hf.hasFDerivAt.const_sub c).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.const_sub
  条件: (hf : DifferentiableAt 𝕜 f x) (c : F)
  证明: (hf.hasFDerivAt.const_sub c).differentiableAt

@[fun_prop]

Depends on / 依赖: const_sub, differentiableAt, hasFDerivAt, hf.hasFDerivAt.const_sub
-/
theorem DifferentiableAt.const_sub (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => c - f y) x :=
  (hf.hasFDerivAt.const_sub c).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableOn.const_sub` / 定理 `DifferentiableOn.const_sub`

English:
theorem DifferentiableOn.const_sub
  given: (hf : DifferentiableOn 𝕜 f s) (c : F)
  proof: fun x hx => (hf x hx).const_sub c

@[fun_prop]

中文:
定理 DifferentiableOn.const_sub
  条件: (hf : DifferentiableOn 𝕜 f s) (c : F)
  证明: fun x hx => (hf x hx).const_sub c

@[fun_prop]

Depends on / 依赖: const_sub
-/
theorem DifferentiableOn.const_sub (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => c - f y) s := fun x hx => (hf x hx).const_sub c

@[fun_prop]
/--
theorem `Differentiable.const_sub` / 定理 `Differentiable.const_sub`

English:
theorem Differentiable.const_sub
  given: (hf : Differentiable 𝕜 f) (c : F)
  proof: fun x => (hf x).const_sub c

中文:
定理 可微.const_sub
  条件: (hf : 可微 𝕜 f) (c : F)
  证明: fun x => (hf x).const_sub c

Depends on / 依赖: const_sub
-/
theorem Differentiable.const_sub (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => c - f y := fun x => (hf x).const_sub c

/--
theorem `fderivWithin_const_sub` / 定理 `fderivWithin_const_sub`

English:
theorem fderivWithin_const_sub
  given: (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F)
  proof: by
  simp only [sub_eq_add_neg, fderivWithin_const_add, fderivWithin_fun_neg, hxs]

中文:
定理 fderivWithin_const_sub
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F)
  证明: by
  simp only [sub_eq_add_neg, fderivWithin_const_add, fderivWithin_fun_neg, hxs]

Depends on / 依赖: fderivWithin_const_add, fderivWithin_fun_neg, sub_eq_add_neg
-/
theorem fderivWithin_const_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => c - f y) s x = -fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_const_add, fderivWithin_fun_neg, hxs]

/--
theorem `fderiv_const_sub` / 定理 `fderiv_const_sub`

English:
theorem fderiv_const_sub
  given: (c : F)
  statement: fderiv 𝕜 (fun y => c - f y) x = -fderiv 𝕜 f x
  proof: by
  simp only [← fderivWithin_univ, fderivWithin_const_sub uniqueDiffWithinAt_univ]

中文:
定理 fderiv_const_sub
  条件: (c : F)
  结论: fderiv 𝕜 (fun y => c - f y) x = -fderiv 𝕜 f x
  证明: by
  simp only [← fderivWithin_univ, fderivWithin_const_sub uniqueDiffWithinAt_univ]

Depends on / 依赖: fderivWithin_const_sub, fderivWithin_univ, uniqueDiffWithinAt_univ
-/
theorem fderiv_const_sub (c : F) : fderiv 𝕜 (fun y => c - f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_const_sub uniqueDiffWithinAt_univ]

end Sub

section CompAdd

/-! ### Derivative of the composition with a translation -/

open scoped Pointwise Topology

/--
theorem `hasFDerivWithinAt_comp_add_left` / 定理 `hasFDerivWithinAt_comp_add_left`

English:
theorem hasFDerivWithinAt_comp_add_left
  given: (a : E)
  proof: by
  have : map (a + ·) (𝓝[s] x) = 𝓝[a +ᵥ s] (a + x) := by
    simp only [nhdsWithin, Filter.map_inf (add_right_injective a)]
    simp [← Set.image_vadd]
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS, ← this, Function.comp_def]

中文:
定理 hasFDerivWithinAt_comp_add_left
  条件: (a : E)
  证明: by
  have : map (a + ·) (𝓝[s] x) = 𝓝[a +ᵥ s] (a + x) := by
    simp only [nhdsWithin, Filter.map_inf (add_right_injective a)]
    simp [← Set.image_vadd]
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS, ← this, Function.comp_def]

Depends on / 依赖: Filter, Filter.map_inf, Function, Function.comp_def, HasFDerivWithinAt, Set.image_vadd, add_right_injective, comp_def, hasFDerivAtFilter_iff_isLittleOTVS, image_vadd, map_inf, nhdsWithin
-/
theorem hasFDerivWithinAt_comp_add_left (a : E) :
    HasFDerivWithinAt (fun x => f (a + x)) f' s x ↔ HasFDerivWithinAt f f' (a +ᵥ s) (a + x) := by
  have : map (a + ·) (𝓝[s] x) = 𝓝[a +ᵥ s] (a + x) := by
    simp only [nhdsWithin, Filter.map_inf (add_right_injective a)]
    simp [← Set.image_vadd]
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS, ← this, Function.comp_def]

/--
theorem `differentiableWithinAt_comp_add_left` / 定理 `differentiableWithinAt_comp_add_left`

English:
theorem differentiableWithinAt_comp_add_left
  given: (a : E)
  proof: by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_add_left]

中文:
定理 differentiableWithinAt_comp_add_left
  条件: (a : E)
  证明: by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_add_left]

Depends on / 依赖: DifferentiableWithinAt, hasFDerivWithinAt_comp_add_left
-/
theorem differentiableWithinAt_comp_add_left (a : E) :
    DifferentiableWithinAt 𝕜 (fun x => f (a + x)) s x ↔
      DifferentiableWithinAt 𝕜 f (a +ᵥ s) (a + x) := by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_add_left]

/--
theorem `fderivWithin_comp_add_left` / 定理 `fderivWithin_comp_add_left`

English:
theorem fderivWithin_comp_add_left
  given: (a : E)
  proof: by
  classical
  simp only [fderivWithin, hasFDerivWithinAt_comp_add_left, differentiableWithinAt_comp_add_left]

中文:
定理 fderivWithin_comp_add_left
  条件: (a : E)
  证明: by
  classical
  simp only [fderivWithin, hasFDerivWithinAt_comp_add_left, differentiableWithinAt_comp_add_left]

Depends on / 依赖: classical, differentiableWithinAt_comp_add_left, fderivWithin, hasFDerivWithinAt_comp_add_left
-/
theorem fderivWithin_comp_add_left (a : E) :
    fderivWithin 𝕜 (fun x => f (a + x)) s x = fderivWithin 𝕜 f (a +ᵥ s) (a + x) := by
  classical
  simp only [fderivWithin, hasFDerivWithinAt_comp_add_left, differentiableWithinAt_comp_add_left]

/--
theorem `hasFDerivWithinAt_comp_add_right` / 定理 `hasFDerivWithinAt_comp_add_right`

English:
theorem hasFDerivWithinAt_comp_add_right
  given: (a : E)
  proof: by
  simpa only [add_comm a] using hasFDerivWithinAt_comp_add_left a

中文:
定理 hasFDerivWithinAt_comp_add_right
  条件: (a : E)
  证明: by
  simpa only [add_comm a] using hasFDerivWithinAt_comp_add_left a

Depends on / 依赖: add_comm, hasFDerivWithinAt_comp_add_left
-/
theorem hasFDerivWithinAt_comp_add_right (a : E) :
    HasFDerivWithinAt (fun x => f (x + a)) f' s x ↔ HasFDerivWithinAt f f' (a +ᵥ s) (x + a) := by
  simpa only [add_comm a] using hasFDerivWithinAt_comp_add_left a

/--
theorem `differentiableWithinAt_comp_add_right` / 定理 `differentiableWithinAt_comp_add_right`

English:
theorem differentiableWithinAt_comp_add_right
  given: (a : E)
  proof: by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_add_right]

中文:
定理 differentiableWithinAt_comp_add_right
  条件: (a : E)
  证明: by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_add_right]

Depends on / 依赖: DifferentiableWithinAt, hasFDerivWithinAt_comp_add_right
-/
theorem differentiableWithinAt_comp_add_right (a : E) :
    DifferentiableWithinAt 𝕜 (fun x => f (x + a)) s x ↔
      DifferentiableWithinAt 𝕜 f (a +ᵥ s) (x + a) := by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_add_right]

/--
theorem `fderivWithin_comp_add_right` / 定理 `fderivWithin_comp_add_right`

English:
theorem fderivWithin_comp_add_right
  given: (a : E)
  proof: by
  simp only [add_comm _ a, fderivWithin_comp_add_left]

中文:
定理 fderivWithin_comp_add_right
  条件: (a : E)
  证明: by
  simp only [add_comm _ a, fderivWithin_comp_add_left]

Depends on / 依赖: add_comm, fderivWithin_comp_add_left
-/
theorem fderivWithin_comp_add_right (a : E) :
    fderivWithin 𝕜 (fun x => f (x + a)) s x = fderivWithin 𝕜 f (a +ᵥ s) (x + a) := by
  simp only [add_comm _ a, fderivWithin_comp_add_left]

/--
theorem `hasFDerivAt_comp_add_right` / 定理 `hasFDerivAt_comp_add_right`

English:
theorem hasFDerivAt_comp_add_right
  given: (a : E)
  proof: by
  simp [← hasFDerivWithinAt_univ, hasFDerivWithinAt_comp_add_right]

中文:
定理 hasFDerivAt_comp_add_right
  条件: (a : E)
  证明: by
  simp [← hasFDerivWithinAt_univ, hasFDerivWithinAt_comp_add_right]

Depends on / 依赖: hasFDerivWithinAt_comp_add_right, hasFDerivWithinAt_univ
-/
theorem hasFDerivAt_comp_add_right (a : E) :
    HasFDerivAt (fun x => f (x + a)) f' x ↔ HasFDerivAt f f' (x + a) := by
  simp [← hasFDerivWithinAt_univ, hasFDerivWithinAt_comp_add_right]

/--
theorem `differentiableAt_comp_add_right` / 定理 `differentiableAt_comp_add_right`

English:
theorem differentiableAt_comp_add_right
  given: (a : E)
  proof: by
  simp [DifferentiableAt, hasFDerivAt_comp_add_right]

中文:
定理 differentiableAt_comp_add_right
  条件: (a : E)
  证明: by
  simp [DifferentiableAt, hasFDerivAt_comp_add_right]

Depends on / 依赖: DifferentiableAt, hasFDerivAt_comp_add_right
-/
theorem differentiableAt_comp_add_right (a : E) :
    DifferentiableAt 𝕜 (fun x => f (x + a)) x ↔ DifferentiableAt 𝕜 f (x + a) := by
  simp [DifferentiableAt, hasFDerivAt_comp_add_right]

/--
theorem `fderiv_comp_add_right` / 定理 `fderiv_comp_add_right`

English:
theorem fderiv_comp_add_right
  given: (a : E)
  proof: by
  simp [← fderivWithin_univ, fderivWithin_comp_add_right]

中文:
定理 fderiv_comp_add_right
  条件: (a : E)
  证明: by
  simp [← fderivWithin_univ, fderivWithin_comp_add_right]

Depends on / 依赖: fderivWithin_comp_add_right, fderivWithin_univ
-/
theorem fderiv_comp_add_right (a : E) :
    fderiv 𝕜 (fun x => f (x + a)) x = fderiv 𝕜 f (x + a) := by
  simp [← fderivWithin_univ, fderivWithin_comp_add_right]

/--
theorem `hasFDerivAt_comp_add_left` / 定理 `hasFDerivAt_comp_add_left`

English:
theorem hasFDerivAt_comp_add_left
  given: (a : E)
  proof: by
  simpa [add_comm a] using hasFDerivAt_comp_add_right a

中文:
定理 hasFDerivAt_comp_add_left
  条件: (a : E)
  证明: by
  simpa [add_comm a] using hasFDerivAt_comp_add_right a

Depends on / 依赖: add_comm, hasFDerivAt_comp_add_right
-/
theorem hasFDerivAt_comp_add_left (a : E) :
    HasFDerivAt (fun x => f (a + x)) f' x ↔ HasFDerivAt f f' (a + x) := by
  simpa [add_comm a] using hasFDerivAt_comp_add_right a

/--
theorem `differentiableAt_comp_add_left` / 定理 `differentiableAt_comp_add_left`

English:
theorem differentiableAt_comp_add_left
  given: (a : E)
  proof: by
  simp [DifferentiableAt, hasFDerivAt_comp_add_left]

中文:
定理 differentiableAt_comp_add_left
  条件: (a : E)
  证明: by
  simp [DifferentiableAt, hasFDerivAt_comp_add_left]

Depends on / 依赖: DifferentiableAt, hasFDerivAt_comp_add_left
-/
theorem differentiableAt_comp_add_left (a : E) :
    DifferentiableAt 𝕜 (fun x => f (a + x)) x ↔ DifferentiableAt 𝕜 f (a + x) := by
  simp [DifferentiableAt, hasFDerivAt_comp_add_left]

/--
theorem `fderiv_comp_add_left` / 定理 `fderiv_comp_add_left`

English:
theorem fderiv_comp_add_left
  given: (a : E)
  proof: by
  simpa [add_comm a] using fderiv_comp_add_right a

中文:
定理 fderiv_comp_add_left
  条件: (a : E)
  证明: by
  simpa [add_comm a] using fderiv_comp_add_right a

Depends on / 依赖: add_comm, fderiv_comp_add_right
-/
theorem fderiv_comp_add_left (a : E) :
    fderiv 𝕜 (fun x => f (a + x)) x = fderiv 𝕜 f (a + x) := by
  simpa [add_comm a] using fderiv_comp_add_right a

/--
theorem `hasFDerivWithinAt_comp_sub` / 定理 `hasFDerivWithinAt_comp_sub`

English:
theorem hasFDerivWithinAt_comp_sub
  given: (a : E)
  proof: by
  simpa [sub_eq_add_neg] using hasFDerivWithinAt_comp_add_right (-a)

中文:
定理 hasFDerivWithinAt_comp_sub
  条件: (a : E)
  证明: by
  simpa [sub_eq_add_neg] using hasFDerivWithinAt_comp_add_right (-a)

Depends on / 依赖: hasFDerivWithinAt_comp_add_right, sub_eq_add_neg
-/
theorem hasFDerivWithinAt_comp_sub (a : E) :
    HasFDerivWithinAt (fun x => f (x - a)) f' s x ↔ HasFDerivWithinAt f f' (-a +ᵥ s) (x - a) := by
  simpa [sub_eq_add_neg] using hasFDerivWithinAt_comp_add_right (-a)

/--
theorem `differentiableWithinAt_comp_sub` / 定理 `differentiableWithinAt_comp_sub`

English:
theorem differentiableWithinAt_comp_sub
  given: (a : E)
  proof: by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_sub]

中文:
定理 differentiableWithinAt_comp_sub
  条件: (a : E)
  证明: by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_sub]

Depends on / 依赖: DifferentiableWithinAt, hasFDerivWithinAt_comp_sub
-/
theorem differentiableWithinAt_comp_sub (a : E) :
    DifferentiableWithinAt 𝕜 (fun x => f (x - a)) s x ↔
      DifferentiableWithinAt 𝕜 f (-a +ᵥ s) (x - a) := by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_sub]

/--
theorem `fderivWithin_comp_sub` / 定理 `fderivWithin_comp_sub`

English:
theorem fderivWithin_comp_sub
  given: (a : E)
  proof: by
  simpa [sub_eq_add_neg] using fderivWithin_comp_add_right (-a)

中文:
定理 fderivWithin_comp_sub
  条件: (a : E)
  证明: by
  simpa [sub_eq_add_neg] using fderivWithin_comp_add_right (-a)

Depends on / 依赖: fderivWithin_comp_add_right, sub_eq_add_neg
-/
theorem fderivWithin_comp_sub (a : E) :
    fderivWithin 𝕜 (fun x => f (x - a)) s x = fderivWithin 𝕜 f (-a +ᵥ s) (x - a) := by
  simpa [sub_eq_add_neg] using fderivWithin_comp_add_right (-a)

/--
theorem `hasFDerivAt_comp_sub` / 定理 `hasFDerivAt_comp_sub`

English:
theorem hasFDerivAt_comp_sub
  given: (a : E)
  proof: by
  simp [← hasFDerivWithinAt_univ, hasFDerivWithinAt_comp_sub]

中文:
定理 hasFDerivAt_comp_sub
  条件: (a : E)
  证明: by
  simp [← hasFDerivWithinAt_univ, hasFDerivWithinAt_comp_sub]

Depends on / 依赖: hasFDerivWithinAt_comp_sub, hasFDerivWithinAt_univ
-/
theorem hasFDerivAt_comp_sub (a : E) :
    HasFDerivAt (fun x => f (x - a)) f' x ↔ HasFDerivAt f f' (x - a) := by
  simp [← hasFDerivWithinAt_univ, hasFDerivWithinAt_comp_sub]

/--
theorem `differentiableAt_comp_sub` / 定理 `differentiableAt_comp_sub`

English:
theorem differentiableAt_comp_sub
  given: (a : E)
  proof: by
  simp [DifferentiableAt, hasFDerivAt_comp_sub]

中文:
定理 differentiableAt_comp_sub
  条件: (a : E)
  证明: by
  simp [DifferentiableAt, hasFDerivAt_comp_sub]

Depends on / 依赖: DifferentiableAt, hasFDerivAt_comp_sub
-/
theorem differentiableAt_comp_sub (a : E) :
    DifferentiableAt 𝕜 (fun x => f (x - a)) x ↔ DifferentiableAt 𝕜 f (x - a) := by
  simp [DifferentiableAt, hasFDerivAt_comp_sub]

/--
theorem `fderiv_comp_sub` / 定理 `fderiv_comp_sub`

English:
theorem fderiv_comp_sub
  given: (a : E)
  proof: by
  simp [← fderivWithin_univ, fderivWithin_comp_sub]

中文:
定理 fderiv_comp_sub
  条件: (a : E)
  证明: by
  simp [← fderivWithin_univ, fderivWithin_comp_sub]

Depends on / 依赖: fderivWithin_comp_sub, fderivWithin_univ
-/
theorem fderiv_comp_sub (a : E) :
    fderiv 𝕜 (fun x => f (x - a)) x = fderiv 𝕜 f (x - a) := by
  simp [← fderivWithin_univ, fderivWithin_comp_sub]

end CompAdd

end
