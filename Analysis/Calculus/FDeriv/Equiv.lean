/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# The derivative of a linear equivalence

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
continuous linear equivalences.

We also prove the usual formula for the derivative of the inverse function, assuming it exists.
The inverse function theorem is in `Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`.
-/

public section

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
variable {f : E -> F} {f' : E ->L[𝕜] F} {x : E} {s : Set E} {c : F}

namespace ContinuousLinearEquiv

/-! ### Differentiability of linear equivs, and invariance of differentiability -/


variable (iso : E ≃L[𝕜] F)

@[fun_prop]
/--
theorem `hasStrictFDerivAt` / 定理 `hasStrictFDerivAt`

English:
theorem hasStrictFDerivAt
  statement: HasStrictFDerivAt iso (iso : E ->L[𝕜] F) x
  proof: iso.toContinuousLinearMap.hasStrictFDerivAt

@[fun_prop]

中文:
定理 hasStrictFDerivAt
  结论: HasStrictFDerivAt iso (iso : E ->L[𝕜] F) x
  证明: iso.toContinuousLinearMap.hasStrictFDerivAt

@[fun_prop]
-/
protected theorem hasStrictFDerivAt : HasStrictFDerivAt iso (iso : E ->L[𝕜] F) x :=
  iso.toContinuousLinearMap.hasStrictFDerivAt

@[fun_prop]
/--
theorem `hasFDerivWithinAt` / 定理 `hasFDerivWithinAt`

English:
theorem hasFDerivWithinAt
  statement: HasFDerivWithinAt iso (iso : E ->L[𝕜] F) s x
  proof: iso.toContinuousLinearMap.hasFDerivWithinAt

@[fun_prop]

中文:
定理 hasFDerivWithinAt
  结论: HasFDerivWithinAt iso (iso : E ->L[𝕜] F) s x
  证明: iso.toContinuousLinearMap.hasFDerivWithinAt

@[fun_prop]
-/
protected theorem hasFDerivWithinAt : HasFDerivWithinAt iso (iso : E ->L[𝕜] F) s x :=
  iso.toContinuousLinearMap.hasFDerivWithinAt

@[fun_prop]
/--
theorem `hasFDerivAt` / 定理 `hasFDerivAt`

English:
theorem hasFDerivAt
  statement: HasFDerivAt iso (iso : E ->L[𝕜] F) x
  proof: iso.toContinuousLinearMap.hasFDerivAtFilter

@[fun_prop]

中文:
定理 hasFDerivAt
  结论: 在点处Fréchet可导 iso (iso : E ->L[𝕜] F) x
  证明: iso.toContinuousLinearMap.hasFDerivAtFilter

@[fun_prop]
-/
protected theorem hasFDerivAt : HasFDerivAt iso (iso : E ->L[𝕜] F) x :=
  iso.toContinuousLinearMap.hasFDerivAtFilter

@[fun_prop]
/--
theorem `differentiableAt` / 定理 `differentiableAt`

English:
theorem differentiableAt
  statement: DifferentiableAt 𝕜 iso x
  proof: iso.hasFDerivAt.differentiableAt

@[fun_prop]

中文:
定理 differentiableAt
  结论: DifferentiableAt 𝕜 iso x
  证明: iso.hasFDerivAt.differentiableAt

@[fun_prop]
-/
protected theorem differentiableAt : DifferentiableAt 𝕜 iso x :=
  iso.hasFDerivAt.differentiableAt

@[fun_prop]
/--
theorem `differentiableWithinAt` / 定理 `differentiableWithinAt`

English:
theorem differentiableWithinAt
  statement: DifferentiableWithinAt 𝕜 iso s x
  proof: iso.differentiableAt.differentiableWithinAt

中文:
定理 differentiableWithinAt
  结论: DifferentiableWithinAt 𝕜 iso s x
  证明: iso.differentiableAt.differentiableWithinAt
-/
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 iso s x :=
  iso.differentiableAt.differentiableWithinAt

/--
theorem `fderiv` / 定理 `fderiv`

English:
theorem fderiv
  statement: fderiv 𝕜 iso x = iso
  proof: iso.hasFDerivAt.fderiv

中文:
定理 fderiv
  结论: fderiv 𝕜 iso x = iso
  证明: iso.hasFDerivAt.fderiv
-/
protected theorem fderiv : fderiv 𝕜 iso x = iso :=
  iso.hasFDerivAt.fderiv

/--
theorem `fderivWithin` / 定理 `fderivWithin`

English:
theorem fderivWithin
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  statement: fderivWithin 𝕜 iso s x = iso
  proof: iso.toContinuousLinearMap.fderivWithin hxs

@[fun_prop]

中文:
定理 fderivWithin
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  结论: fderivWithin 𝕜 iso s x = iso
  证明: iso.toContinuousLinearMap.fderivWithin hxs

@[fun_prop]
-/
protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 iso s x = iso :=
  iso.toContinuousLinearMap.fderivWithin hxs

@[fun_prop]
/--
theorem `differentiable` / 定理 `differentiable`

English:
theorem differentiable
  statement: Differentiable 𝕜 iso
  proof: fun _ => iso.differentiableAt

@[fun_prop]

中文:
定理 differentiable
  结论: 可微 𝕜 iso
  证明: fun _ => iso.differentiableAt

@[fun_prop]
-/
protected theorem differentiable : Differentiable 𝕜 iso := fun _ => iso.differentiableAt

@[fun_prop]
/--
theorem `differentiableOn` / 定理 `differentiableOn`

English:
theorem differentiableOn
  statement: DifferentiableOn 𝕜 iso s
  proof: iso.differentiable.differentiableOn

中文:
定理 differentiableOn
  结论: DifferentiableOn 𝕜 iso s
  证明: iso.differentiable.differentiableOn
-/
protected theorem differentiableOn : DifferentiableOn 𝕜 iso s :=
  iso.differentiable.differentiableOn

/--
theorem `comp_differentiableWithinAt_iff` / 定理 `comp_differentiableWithinAt_iff`

English:
theorem comp_differentiableWithinAt_iff
  given: {f : G -> E} {s : Set G} {x : G}
  proof: by
  refine ⟨fun H => ?_, fun H => iso.differentiable.differentiableAt.comp_differentiableWithinAt x H⟩
  have : DifferentiableWithinAt 𝕜 (iso.symm ∘ iso ∘ f) s x :=
    iso.symm.differentiable.differentiableAt.comp_differentiableWithinAt x H
  rwa [← Function.comp_assoc iso.symm iso f, iso.symm_comp_self] at this

中文:
定理 comp_differentiableWithinAt_iff
  条件: {f : G -> E} {s : 集合 G} {x : G}
  证明: by
  refine ⟨fun H => ?_, fun H => iso.differentiable.differentiableAt.comp_differentiableWithinAt x H⟩
  have : DifferentiableWithinAt 𝕜 (iso.symm ∘ iso ∘ f) s x :=
    iso.symm.differentiable.differentiableAt.comp_differentiableWithinAt x H
  rwa [← Function.comp_assoc iso.symm iso f, iso.symm_comp_self] at this

Depends on / 依赖: DifferentiableWithinAt, Function, Function.comp_assoc, comp_assoc, comp_differentiableWithinAt, differentiable, differentiableAt, iso.differentiable.differentiableAt.comp_differentiableWithinAt, iso.symm, iso.symm.differentiable.differentiableAt.comp_differentiableWithinAt, iso.symm_comp_self, symm_comp_self
-/
theorem comp_differentiableWithinAt_iff {f : G -> E} {s : Set G} {x : G} :
    DifferentiableWithinAt 𝕜 (iso ∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  refine ⟨fun H => ?_, fun H => iso.differentiable.differentiableAt.comp_differentiableWithinAt x H⟩
  have : DifferentiableWithinAt 𝕜 (iso.symm ∘ iso ∘ f) s x :=
    iso.symm.differentiable.differentiableAt.comp_differentiableWithinAt x H
  rwa [← Function.comp_assoc iso.symm iso f, iso.symm_comp_self] at this

/--
theorem `comp_differentiableAt_iff` / 定理 `comp_differentiableAt_iff`

English:
theorem comp_differentiableAt_iff
  given: {f : G -> E} {x : G}
  proof: by
  rw [← differentiableWithinAt_univ]; rw [← differentiableWithinAt_univ]; rw [iso.comp_differentiableWithinAt_iff]

中文:
定理 comp_differentiableAt_iff
  条件: {f : G -> E} {x : G}
  证明: by
  rw [← differentiableWithinAt_univ]; rw [← differentiableWithinAt_univ]; rw [iso.comp_differentiableWithinAt_iff]

Depends on / 依赖: comp_differentiableWithinAt_iff, differentiableWithinAt_univ, iso.comp_differentiableWithinAt_iff
-/
theorem comp_differentiableAt_iff {f : G -> E} {x : G} :
    DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f x := by
  rw [← differentiableWithinAt_univ]; rw [← differentiableWithinAt_univ]; rw [iso.comp_differentiableWithinAt_iff]

/--
theorem `comp_differentiableOn_iff` / 定理 `comp_differentiableOn_iff`

English:
theorem comp_differentiableOn_iff
  given: {f : G -> E} {s : Set G}
  proof: by
  rw [DifferentiableOn]; rw [DifferentiableOn]
  simp only [iso.comp_differentiableWithinAt_iff]

中文:
定理 comp_differentiableOn_iff
  条件: {f : G -> E} {s : 集合 G}
  证明: by
  rw [DifferentiableOn]; rw [DifferentiableOn]
  simp only [iso.comp_differentiableWithinAt_iff]

Depends on / 依赖: DifferentiableOn, comp_differentiableWithinAt_iff, iso.comp_differentiableWithinAt_iff
-/
theorem comp_differentiableOn_iff {f : G -> E} {s : Set G} :
    DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 𝕜 f s := by
  rw [DifferentiableOn]; rw [DifferentiableOn]
  simp only [iso.comp_differentiableWithinAt_iff]

/--
theorem `comp_differentiable_iff` / 定理 `comp_differentiable_iff`

English:
theorem comp_differentiable_iff
  given: {f : G -> E}
  statement: Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f
  proof: by
  rw [← differentiableOn_univ]; rw [← differentiableOn_univ]
  exact iso.comp_differentiableOn_iff

中文:
定理 comp_differentiable_iff
  条件: {f : G -> E}
  结论: 可微 𝕜 (iso ∘ f) ↔ 可微 𝕜 f
  证明: by
  rw [← differentiableOn_univ]; rw [← differentiableOn_univ]
  exact iso.comp_differentiableOn_iff

Depends on / 依赖: comp_differentiableOn_iff, differentiableOn_univ, iso.comp_differentiableOn_iff
-/
theorem comp_differentiable_iff {f : G -> E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f := by
  rw [← differentiableOn_univ]; rw [← differentiableOn_univ]
  exact iso.comp_differentiableOn_iff

/--
theorem `comp_hasFDerivWithinAt_iff` / 定理 `comp_hasFDerivWithinAt_iff`

English:
theorem comp_hasFDerivWithinAt_iff
  given: {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] E}
  proof: by
  refine ⟨fun H => ?_, fun H => iso.hasFDerivAt.comp_hasFDerivWithinAt x H⟩
  simpa [Function.comp_def, ← ContinuousLinearMap.comp_assoc]
    using iso.symm.hasFDerivAt.comp_hasFDerivWithinAt x H

中文:
定理 comp_hasFDerivWithinAt_iff
  条件: {f : G -> E} {s : 集合 G} {x : G} {f' : G ->L[𝕜] E}
  证明: by
  refine ⟨fun H => ?_, fun H => iso.hasFDerivAt.comp_hasFDerivWithinAt x H⟩
  simpa [Function.comp_def, ← ContinuousLinearMap.comp_assoc]
    using iso.symm.hasFDerivAt.comp_hasFDerivWithinAt x H

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_assoc, Function, Function.comp_def, comp_assoc, comp_def, comp_hasFDerivWithinAt, hasFDerivAt, iso.hasFDerivAt.comp_hasFDerivWithinAt, iso.symm.hasFDerivAt.comp_hasFDerivWithinAt
-/
theorem comp_hasFDerivWithinAt_iff {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] E} :
    HasFDerivWithinAt (iso ∘ f) ((iso : E ->L[𝕜] F).comp f') s x ↔ HasFDerivWithinAt f f' s x := by
  refine ⟨fun H => ?_, fun H => iso.hasFDerivAt.comp_hasFDerivWithinAt x H⟩
  simpa [Function.comp_def, ← ContinuousLinearMap.comp_assoc]
    using iso.symm.hasFDerivAt.comp_hasFDerivWithinAt x H

/--
theorem `comp_hasStrictFDerivAt_iff` / 定理 `comp_hasStrictFDerivAt_iff`

English:
theorem comp_hasStrictFDerivAt_iff
  given: {f : G -> E} {x : G} {f' : G ->L[𝕜] E}
  proof: by
  refine ⟨fun H => ?_, fun H => iso.hasStrictFDerivAt.comp x H⟩
  convert! iso.symm.hasStrictFDerivAt.comp x H using 1 <;>
    ext z <;> apply (iso.symm_apply_apply _).symm

中文:
定理 comp_hasStrictFDerivAt_iff
  条件: {f : G -> E} {x : G} {f' : G ->L[𝕜] E}
  证明: by
  refine ⟨fun H => ?_, fun H => iso.hasStrictFDerivAt.comp x H⟩
  convert! iso.symm.hasStrictFDerivAt.comp x H using 1 <;>
    ext z <;> apply (iso.symm_apply_apply _).symm

Depends on / 依赖: convert, hasStrictFDerivAt, iso.hasStrictFDerivAt.comp, iso.symm.hasStrictFDerivAt.comp, iso.symm_apply_apply, symm_apply_apply
-/
theorem comp_hasStrictFDerivAt_iff {f : G -> E} {x : G} {f' : G ->L[𝕜] E} :
    HasStrictFDerivAt (iso ∘ f) ((iso : E ->L[𝕜] F).comp f') x ↔ HasStrictFDerivAt f f' x := by
  refine ⟨fun H => ?_, fun H => iso.hasStrictFDerivAt.comp x H⟩
  convert! iso.symm.hasStrictFDerivAt.comp x H using 1 <;>
    ext z <;> apply (iso.symm_apply_apply _).symm

/--
theorem `comp_hasFDerivAt_iff` / 定理 `comp_hasFDerivAt_iff`

English:
theorem comp_hasFDerivAt_iff
  given: {f : G -> E} {x : G} {f' : G ->L[𝕜] E}
  proof: by
  simp_rw [← hasFDerivWithinAt_univ, iso.comp_hasFDerivWithinAt_iff]

中文:
定理 comp_hasFDerivAt_iff
  条件: {f : G -> E} {x : G} {f' : G ->L[𝕜] E}
  证明: by
  simp_rw [← hasFDerivWithinAt_univ, iso.comp_hasFDerivWithinAt_iff]

Depends on / 依赖: comp_hasFDerivWithinAt_iff, hasFDerivWithinAt_univ, iso.comp_hasFDerivWithinAt_iff, simp_rw
-/
theorem comp_hasFDerivAt_iff {f : G -> E} {x : G} {f' : G ->L[𝕜] E} :
    HasFDerivAt (iso ∘ f) ((iso : E ->L[𝕜] F).comp f') x ↔ HasFDerivAt f f' x := by
  simp_rw [← hasFDerivWithinAt_univ, iso.comp_hasFDerivWithinAt_iff]

/--
theorem `comp_hasFDerivWithinAt_iff'` / 定理 `comp_hasFDerivWithinAt_iff'`

English:
theorem comp_hasFDerivWithinAt_iff'
  given: {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] F}
  proof: by
  rw [← iso.comp_hasFDerivWithinAt_iff]; rw [← ContinuousLinearMap.comp_assoc]; rw [iso.coe_comp_coe_symm]; rw [ContinuousLinearMap.id_comp]

中文:
定理 comp_hasFDerivWithinAt_iff'
  条件: {f : G -> E} {s : 集合 G} {x : G} {f' : G ->L[𝕜] F}
  证明: by
  rw [← iso.comp_hasFDerivWithinAt_iff]; rw [← ContinuousLinearMap.comp_assoc]; rw [iso.coe_comp_coe_symm]; rw [ContinuousLinearMap.id_comp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.id_comp, coe_comp_coe_symm, comp_assoc, comp_hasFDerivWithinAt_iff, id_comp, iso.coe_comp_coe_symm, iso.comp_hasFDerivWithinAt_iff
-/
theorem comp_hasFDerivWithinAt_iff' {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] F} :
    HasFDerivWithinAt (iso ∘ f) f' s x ↔
      HasFDerivWithinAt f ((iso.symm : F ->L[𝕜] E).comp f') s x := by
  rw [← iso.comp_hasFDerivWithinAt_iff]; rw [← ContinuousLinearMap.comp_assoc]; rw [iso.coe_comp_coe_symm]; rw [ContinuousLinearMap.id_comp]

/--
theorem `comp_hasFDerivAt_iff'` / 定理 `comp_hasFDerivAt_iff'`

English:
theorem comp_hasFDerivAt_iff'
  given: {f : G -> E} {x : G} {f' : G ->L[𝕜] F}
  proof: by
  simp_rw [← hasFDerivWithinAt_univ, iso.comp_hasFDerivWithinAt_iff']

中文:
定理 comp_hasFDerivAt_iff'
  条件: {f : G -> E} {x : G} {f' : G ->L[𝕜] F}
  证明: by
  simp_rw [← hasFDerivWithinAt_univ, iso.comp_hasFDerivWithinAt_iff']

Depends on / 依赖: comp_hasFDerivWithinAt_iff, hasFDerivWithinAt_univ, iso.comp_hasFDerivWithinAt_iff, simp_rw
-/
theorem comp_hasFDerivAt_iff' {f : G -> E} {x : G} {f' : G ->L[𝕜] F} :
    HasFDerivAt (iso ∘ f) f' x ↔ HasFDerivAt f ((iso.symm : F ->L[𝕜] E).comp f') x := by
  simp_rw [← hasFDerivWithinAt_univ, iso.comp_hasFDerivWithinAt_iff']

/--
theorem `comp_fderivWithin` / 定理 `comp_fderivWithin`

English:
theorem comp_fderivWithin
  given: {f : G -> E} {s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · rw [fderiv_comp_fderivWithin x iso.differentiableAt h hxs, iso.fderiv]
  · have : ¬DifferentiableWithinAt 𝕜 (iso ∘ f) s x := mt iso.comp_differentiableWithinAt_iff.1 h
    rw [fderivWithin_zero_of_not_differentiableWithinAt h]; rw [fderivWithin_zero_of_not_differentiableWithinAt this]; rw [ContinuousLinearMap.comp_zero]

中文:
定理 comp_fderivWithin
  条件: {f : G -> E} {s : 集合 G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · rw [fderiv_comp_fderivWithin x iso.differentiableAt h hxs, iso.fderiv]
  · have : ¬DifferentiableWithinAt 𝕜 (iso ∘ f) s x := mt iso.comp_differentiableWithinAt_iff.1 h
    rw [fderivWithin_zero_of_not_differentiableWithinAt h]; rw [fderivWithin_zero_of_not_differentiableWithinAt this]; rw [ContinuousLinearMap.comp_zero]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_zero, DifferentiableWithinAt, comp_differentiableWithinAt_iff, comp_zero, differentiableAt, fderiv, fderivWithin_zero_of_not_differentiableWithinAt, fderiv_comp_fderivWithin, iso.comp_differentiableWithinAt_iff, iso.differentiableAt, iso.fderiv
-/
theorem comp_fderivWithin {f : G -> E} {s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (iso ∘ f) s x = (iso : E ->L[𝕜] F).comp (fderivWithin 𝕜 f s x) := by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · rw [fderiv_comp_fderivWithin x iso.differentiableAt h hxs, iso.fderiv]
  · have : ¬DifferentiableWithinAt 𝕜 (iso ∘ f) s x := mt iso.comp_differentiableWithinAt_iff.1 h
    rw [fderivWithin_zero_of_not_differentiableWithinAt h]; rw [fderivWithin_zero_of_not_differentiableWithinAt this]; rw [ContinuousLinearMap.comp_zero]

/--
theorem `comp_fderiv` / 定理 `comp_fderiv`

English:
theorem comp_fderiv
  given: {f : G -> E} {x : G}
  proof: by
  rw [← fderivWithin_univ]; rw [← fderivWithin_univ]
  exact iso.comp_fderivWithin uniqueDiffWithinAt_univ

中文:
定理 comp_fderiv
  条件: {f : G -> E} {x : G}
  证明: by
  rw [← fderivWithin_univ]; rw [← fderivWithin_univ]
  exact iso.comp_fderivWithin uniqueDiffWithinAt_univ

Depends on / 依赖: comp_fderivWithin, fderivWithin_univ, iso.comp_fderivWithin, uniqueDiffWithinAt_univ
-/
theorem comp_fderiv {f : G -> E} {x : G} :
    fderiv 𝕜 (iso ∘ f) x = (iso : E ->L[𝕜] F).comp (fderiv 𝕜 f x) := by
  rw [← fderivWithin_univ]; rw [← fderivWithin_univ]
  exact iso.comp_fderivWithin uniqueDiffWithinAt_univ

/--
lemma `_root_.fderivWithin_continuousLinearEquiv_comp` / 引理 `_root_.fderivWithin_continuousLinearEquiv_comp`

English:
lemma _root_.fderivWithin_continuousLinearEquiv_comp
  statement: (L : G ≃L[𝕜] G') (f : E -> (F ->L[𝕜] G))
  proof: by
  change fderivWithin 𝕜 (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L) ∘ f) s x = _
  rw [ContinuousLinearEquiv.comp_fderivWithin _ hs]

中文:
引理 _root_.fderivWithin_continuousLinearEquiv_comp
  结论: (L : G ≃L[𝕜] G') (f : E -> (F ->L[𝕜] G))
  证明: by
  change fderivWithin 𝕜 (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L) ∘ f) s x = _
  rw [ContinuousLinearEquiv.comp_fderivWithin _ hs]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.comp_fderivWithin, ContinuousLinearEquiv.refl, arrowCongr, comp_fderivWithin, fderivWithin
-/
lemma _root_.fderivWithin_continuousLinearEquiv_comp (L : G ≃L[𝕜] G') (f : E -> (F ->L[𝕜] G))
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => (L : G ->L[𝕜] G').comp (f x)) s x =
      (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L)) ∘L (fderivWithin 𝕜 f s x) := by
  change fderivWithin 𝕜 (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L) ∘ f) s x = _
  rw [ContinuousLinearEquiv.comp_fderivWithin _ hs]

/--
lemma `_root_.fderiv_continuousLinearEquiv_comp` / 引理 `_root_.fderiv_continuousLinearEquiv_comp`

English:
lemma _root_.fderiv_continuousLinearEquiv_comp
  given: (L : G ≃L[𝕜] G') (f : E -> (F ->L[𝕜] G)) (x : E)
  proof: by
  change fderiv 𝕜 (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L) ∘ f) x = _
  rw [ContinuousLinearEquiv.comp_fderiv]

中文:
引理 _root_.fderiv_continuousLinearEquiv_comp
  条件: (L : G ≃L[𝕜] G') (f : E -> (F ->L[𝕜] G)) (x : E)
  证明: by
  change fderiv 𝕜 (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L) ∘ f) x = _
  rw [ContinuousLinearEquiv.comp_fderiv]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.comp_fderiv, ContinuousLinearEquiv.refl, arrowCongr, comp_fderiv, fderiv
-/
lemma _root_.fderiv_continuousLinearEquiv_comp (L : G ≃L[𝕜] G') (f : E -> (F ->L[𝕜] G)) (x : E) :
    fderiv 𝕜 (fun x => (L : G ->L[𝕜] G').comp (f x)) x =
      (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L)) ∘L (fderiv 𝕜 f x) := by
  change fderiv 𝕜 (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L) ∘ f) x = _
  rw [ContinuousLinearEquiv.comp_fderiv]

/--
lemma `_root_.fderiv_continuousLinearEquiv_comp'` / 引理 `_root_.fderiv_continuousLinearEquiv_comp'`

English:
lemma _root_.fderiv_continuousLinearEquiv_comp'
  given: (L : G ≃L[𝕜] G') (f : E -> (F ->L[𝕜] G))
  proof: by
  ext x : 1
  exact fderiv_continuousLinearEquiv_comp L f x

中文:
引理 _root_.fderiv_continuousLinearEquiv_comp'
  条件: (L : G ≃L[𝕜] G') (f : E -> (F ->L[𝕜] G))
  证明: by
  ext x : 1
  exact fderiv_continuousLinearEquiv_comp L f x

Depends on / 依赖: fderiv_continuousLinearEquiv_comp
-/
lemma _root_.fderiv_continuousLinearEquiv_comp' (L : G ≃L[𝕜] G') (f : E -> (F ->L[𝕜] G)) :
    fderiv 𝕜 (fun x => (L : G ->L[𝕜] G').comp (f x)) =
      fun x => (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L)) ∘L (fderiv 𝕜 f x) := by
  ext x : 1
  exact fderiv_continuousLinearEquiv_comp L f x

/--
theorem `comp_right_differentiableWithinAt_iff` / 定理 `comp_right_differentiableWithinAt_iff`

English:
theorem comp_right_differentiableWithinAt_iff
  given: {f : F -> G} {s : Set F} {x : E}
  proof: by
  refine ⟨fun H => ?_, fun H => H.comp x iso.differentiableWithinAt (mapsTo_preimage _ s)⟩
  have : DifferentiableWithinAt 𝕜 ((f ∘ iso) ∘ iso.symm) s (iso x) := by
    rw [← iso.symm_apply_apply x] at H
    apply H.comp (iso x) iso.symm.differentiableWithinAt
    intro y hy
    simpa only [mem_preimage, apply_symm_apply] using hy
  rwa [Function.comp_assoc, iso.self_comp_symm] at this

中文:
定理 comp_right_differentiableWithinAt_iff
  条件: {f : F -> G} {s : 集合 F} {x : E}
  证明: by
  refine ⟨fun H => ?_, fun H => H.comp x iso.differentiableWithinAt (mapsTo_preimage _ s)⟩
  have : DifferentiableWithinAt 𝕜 ((f ∘ iso) ∘ iso.symm) s (iso x) := by
    rw [← iso.symm_apply_apply x] at H
    apply H.comp (iso x) iso.symm.differentiableWithinAt
    intro y hy
    simpa only [mem_preimage, apply_symm_apply] using hy
  rwa [Function.comp_assoc, iso.self_comp_symm] at this

Depends on / 依赖: DifferentiableWithinAt, Function, Function.comp_assoc, H.comp, apply_symm_apply, comp_assoc, differentiableWithinAt, iso.differentiableWithinAt, iso.self_comp_symm, iso.symm, iso.symm.differentiableWithinAt, iso.symm_apply_apply, mapsTo_preimage, mem_preimage, self_comp_symm, symm_apply_apply
-/
theorem comp_right_differentiableWithinAt_iff {f : F -> G} {s : Set F} {x : E} :
    DifferentiableWithinAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x ↔ DifferentiableWithinAt 𝕜 f s (iso x) := by
  refine ⟨fun H => ?_, fun H => H.comp x iso.differentiableWithinAt (mapsTo_preimage _ s)⟩
  have : DifferentiableWithinAt 𝕜 ((f ∘ iso) ∘ iso.symm) s (iso x) := by
    rw [← iso.symm_apply_apply x] at H
    apply H.comp (iso x) iso.symm.differentiableWithinAt
    intro y hy
    simpa only [mem_preimage, apply_symm_apply] using hy
  rwa [Function.comp_assoc, iso.self_comp_symm] at this

/--
theorem `comp_right_differentiableAt_iff` / 定理 `comp_right_differentiableAt_iff`

English:
theorem comp_right_differentiableAt_iff
  given: {f : F -> G} {x : E}
  proof: by
  simp only [← differentiableWithinAt_univ, ← iso.comp_right_differentiableWithinAt_iff,
    preimage_univ]

中文:
定理 comp_right_differentiableAt_iff
  条件: {f : F -> G} {x : E}
  证明: by
  simp only [← differentiableWithinAt_univ, ← iso.comp_right_differentiableWithinAt_iff,
    preimage_univ]

Depends on / 依赖: comp_right_differentiableWithinAt_iff, differentiableWithinAt_univ, iso.comp_right_differentiableWithinAt_iff, preimage_univ
-/
theorem comp_right_differentiableAt_iff {f : F -> G} {x : E} :
    DifferentiableAt 𝕜 (f ∘ iso) x ↔ DifferentiableAt 𝕜 f (iso x) := by
  simp only [← differentiableWithinAt_univ, ← iso.comp_right_differentiableWithinAt_iff,
    preimage_univ]

/--
theorem `comp_right_differentiableOn_iff` / 定理 `comp_right_differentiableOn_iff`

English:
theorem comp_right_differentiableOn_iff
  given: {f : F -> G} {s : Set F}
  proof: by
  refine ⟨fun H y hy => ?_, fun H y hy => iso.comp_right_differentiableWithinAt_iff.2 (H _ hy)⟩
  rw [← iso.apply_symm_apply y]; rw [← comp_right_differentiableWithinAt_iff]
  apply H
  simpa only [mem_preimage, apply_symm_apply] using hy

中文:
定理 comp_right_differentiableOn_iff
  条件: {f : F -> G} {s : 集合 F}
  证明: by
  refine ⟨fun H y hy => ?_, fun H y hy => iso.comp_right_differentiableWithinAt_iff.2 (H _ hy)⟩
  rw [← iso.apply_symm_apply y]; rw [← comp_right_differentiableWithinAt_iff]
  apply H
  simpa only [mem_preimage, apply_symm_apply] using hy

Depends on / 依赖: apply_symm_apply, comp_right_differentiableWithinAt_iff, iso.apply_symm_apply, iso.comp_right_differentiableWithinAt_iff, mem_preimage
-/
theorem comp_right_differentiableOn_iff {f : F -> G} {s : Set F} :
    DifferentiableOn 𝕜 (f ∘ iso) (iso ⁻¹' s) ↔ DifferentiableOn 𝕜 f s := by
  refine ⟨fun H y hy => ?_, fun H y hy => iso.comp_right_differentiableWithinAt_iff.2 (H _ hy)⟩
  rw [← iso.apply_symm_apply y]; rw [← comp_right_differentiableWithinAt_iff]
  apply H
  simpa only [mem_preimage, apply_symm_apply] using hy

/--
theorem `comp_right_differentiable_iff` / 定理 `comp_right_differentiable_iff`

English:
theorem comp_right_differentiable_iff
  given: {f : F -> G}
  proof: by
  simp only [← differentiableOn_univ, ← iso.comp_right_differentiableOn_iff, preimage_univ]

中文:
定理 comp_right_differentiable_iff
  条件: {f : F -> G}
  证明: by
  simp only [← differentiableOn_univ, ← iso.comp_right_differentiableOn_iff, preimage_univ]

Depends on / 依赖: comp_right_differentiableOn_iff, differentiableOn_univ, iso.comp_right_differentiableOn_iff, preimage_univ
-/
theorem comp_right_differentiable_iff {f : F -> G} :
    Differentiable 𝕜 (f ∘ iso) ↔ Differentiable 𝕜 f := by
  simp only [← differentiableOn_univ, ← iso.comp_right_differentiableOn_iff, preimage_univ]

/--
theorem `comp_right_hasFDerivWithinAt_iff` / 定理 `comp_right_hasFDerivWithinAt_iff`

English:
theorem comp_right_hasFDerivWithinAt_iff
  given: {f : F -> G} {s : Set F} {x : E} {f' : F ->L[𝕜] G}
  proof: by
  refine ⟨fun H => ?_, fun H => H.comp x iso.hasFDerivWithinAt (mapsTo_preimage _ s)⟩
  rw [← iso.symm_apply_apply x] at H
  have A : f = (f ∘ iso) ∘ iso.symm := by
    rw [Function.comp_assoc]; rw [iso.self_comp_symm]
    rfl
  have B : f' = (f'.comp (iso : E ->L[𝕜] F)).comp (iso.symm : F ->L[𝕜] E) := by
    rw [ContinuousLinearMap.comp_assoc]; rw [iso.coe_comp_coe_symm]; rw [ContinuousLinearMap.comp_id]
  rw [A]; rw [B]
  apply H.comp (iso x) iso.symm.hasFDerivWithinAt
  intro y hy
  simpa only [mem_preimage, apply_symm_apply] using hy

中文:
定理 comp_right_hasFDerivWithinAt_iff
  条件: {f : F -> G} {s : 集合 F} {x : E} {f' : F ->L[𝕜] G}
  证明: by
  refine ⟨fun H => ?_, fun H => H.comp x iso.hasFDerivWithinAt (mapsTo_preimage _ s)⟩
  rw [← iso.symm_apply_apply x] at H
  have A : f = (f ∘ iso) ∘ iso.symm := by
    rw [Function.comp_assoc]; rw [iso.self_comp_symm]
    rfl
  have B : f' = (f'.comp (iso : E ->L[𝕜] F)).comp (iso.symm : F ->L[𝕜] E) := by
    rw [ContinuousLinearMap.comp_assoc]; rw [iso.coe_comp_coe_symm]; rw [ContinuousLinearMap.comp_id]
  rw [A]; rw [B]
  apply H.comp (iso x) iso.symm.hasFDerivWithinAt
  intro y hy
  simpa only [mem_preimage, apply_symm_apply] using hy

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_id, Function, Function.comp_assoc, H.comp, apply_sy, coe_comp_coe_symm, comp_assoc, comp_id, hasFDerivWithinAt, iso.coe_comp_coe_symm, iso.hasFDerivWithinAt, iso.self_comp_symm, iso.symm, iso.symm.hasFDerivWithinAt, iso.symm_apply_apply, mapsTo_preimage, mem_preimage, self_comp_symm
-/
theorem comp_right_hasFDerivWithinAt_iff {f : F -> G} {s : Set F} {x : E} {f' : F ->L[𝕜] G} :
    HasFDerivWithinAt (f ∘ iso) (f'.comp (iso : E ->L[𝕜] F)) (iso ⁻¹' s) x ↔
      HasFDerivWithinAt f f' s (iso x) := by
  refine ⟨fun H => ?_, fun H => H.comp x iso.hasFDerivWithinAt (mapsTo_preimage _ s)⟩
  rw [← iso.symm_apply_apply x] at H
  have A : f = (f ∘ iso) ∘ iso.symm := by
    rw [Function.comp_assoc]; rw [iso.self_comp_symm]
    rfl
  have B : f' = (f'.comp (iso : E ->L[𝕜] F)).comp (iso.symm : F ->L[𝕜] E) := by
    rw [ContinuousLinearMap.comp_assoc]; rw [iso.coe_comp_coe_symm]; rw [ContinuousLinearMap.comp_id]
  rw [A]; rw [B]
  apply H.comp (iso x) iso.symm.hasFDerivWithinAt
  intro y hy
  simpa only [mem_preimage, apply_symm_apply] using hy

/--
theorem `comp_right_hasFDerivAt_iff` / 定理 `comp_right_hasFDerivAt_iff`

English:
theorem comp_right_hasFDerivAt_iff
  given: {f : F -> G} {x : E} {f' : F ->L[𝕜] G}
  proof: by
  simp only [← hasFDerivWithinAt_univ, ← comp_right_hasFDerivWithinAt_iff, preimage_univ]

中文:
定理 comp_right_hasFDerivAt_iff
  条件: {f : F -> G} {x : E} {f' : F ->L[𝕜] G}
  证明: by
  simp only [← hasFDerivWithinAt_univ, ← comp_right_hasFDerivWithinAt_iff, preimage_univ]

Depends on / 依赖: comp_right_hasFDerivWithinAt_iff, hasFDerivWithinAt_univ, preimage_univ
-/
theorem comp_right_hasFDerivAt_iff {f : F -> G} {x : E} {f' : F ->L[𝕜] G} :
    HasFDerivAt (f ∘ iso) (f'.comp (iso : E ->L[𝕜] F)) x ↔ HasFDerivAt f f' (iso x) := by
  simp only [← hasFDerivWithinAt_univ, ← comp_right_hasFDerivWithinAt_iff, preimage_univ]

/--
theorem `comp_right_hasFDerivWithinAt_iff'` / 定理 `comp_right_hasFDerivWithinAt_iff'`

English:
theorem comp_right_hasFDerivWithinAt_iff'
  given: {f : F -> G} {s : Set F} {x : E} {f' : E ->L[𝕜] G}
  proof: by
  rw [← iso.comp_right_hasFDerivWithinAt_iff]; rw [ContinuousLinearMap.comp_assoc]; rw [iso.coe_symm_comp_coe]; rw [ContinuousLinearMap.comp_id]

中文:
定理 comp_right_hasFDerivWithinAt_iff'
  条件: {f : F -> G} {s : 集合 F} {x : E} {f' : E ->L[𝕜] G}
  证明: by
  rw [← iso.comp_right_hasFDerivWithinAt_iff]; rw [ContinuousLinearMap.comp_assoc]; rw [iso.coe_symm_comp_coe]; rw [ContinuousLinearMap.comp_id]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_id, coe_symm_comp_coe, comp_assoc, comp_id, comp_right_hasFDerivWithinAt_iff, iso.coe_symm_comp_coe, iso.comp_right_hasFDerivWithinAt_iff
-/
theorem comp_right_hasFDerivWithinAt_iff' {f : F -> G} {s : Set F} {x : E} {f' : E ->L[𝕜] G} :
    HasFDerivWithinAt (f ∘ iso) f' (iso ⁻¹' s) x ↔
      HasFDerivWithinAt f (f'.comp (iso.symm : F ->L[𝕜] E)) s (iso x) := by
  rw [← iso.comp_right_hasFDerivWithinAt_iff]; rw [ContinuousLinearMap.comp_assoc]; rw [iso.coe_symm_comp_coe]; rw [ContinuousLinearMap.comp_id]

/--
theorem `comp_right_hasFDerivAt_iff'` / 定理 `comp_right_hasFDerivAt_iff'`

English:
theorem comp_right_hasFDerivAt_iff'
  given: {f : F -> G} {x : E} {f' : E ->L[𝕜] G}
  proof: by
  simp only [← hasFDerivWithinAt_univ, ← iso.comp_right_hasFDerivWithinAt_iff', preimage_univ]

中文:
定理 comp_right_hasFDerivAt_iff'
  条件: {f : F -> G} {x : E} {f' : E ->L[𝕜] G}
  证明: by
  simp only [← hasFDerivWithinAt_univ, ← iso.comp_right_hasFDerivWithinAt_iff', preimage_univ]

Depends on / 依赖: comp_right_hasFDerivWithinAt_iff, hasFDerivWithinAt_univ, iso.comp_right_hasFDerivWithinAt_iff, preimage_univ
-/
theorem comp_right_hasFDerivAt_iff' {f : F -> G} {x : E} {f' : E ->L[𝕜] G} :
    HasFDerivAt (f ∘ iso) f' x ↔ HasFDerivAt f (f'.comp (iso.symm : F ->L[𝕜] E)) (iso x) := by
  simp only [← hasFDerivWithinAt_univ, ← iso.comp_right_hasFDerivWithinAt_iff', preimage_univ]

/--
theorem `comp_right_fderivWithin` / 定理 `comp_right_fderivWithin`

English:
theorem comp_right_fderivWithin
  statement: {f : F -> G} {s : Set F} {x : E}
  proof: by
  by_cases h : DifferentiableWithinAt 𝕜 f s (iso x)
  · exact (iso.comp_right_hasFDerivWithinAt_iff.2 h.hasFDerivWithinAt).fderivWithin hxs
  · have : ¬DifferentiableWithinAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x := by
      intro h'
      exact h (iso.comp_right_differentiableWithinAt_iff.1 h')
    rw [fderivWithin_zero_of_not_differentiableWithinAt h]; rw [fderivWithin_zero_of_not_differentiableWithinAt this]; rw [ContinuousLinearMap.zero_comp]

中文:
定理 comp_right_fderivWithin
  结论: {f : F -> G} {s : 集合 F} {x : E}
  证明: by
  by_cases h : DifferentiableWithinAt 𝕜 f s (iso x)
  · exact (iso.comp_right_hasFDerivWithinAt_iff.2 h.hasFDerivWithinAt).fderivWithin hxs
  · have : ¬DifferentiableWithinAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x := by
      intro h'
      exact h (iso.comp_right_differentiableWithinAt_iff.1 h')
    rw [fderivWithin_zero_of_not_differentiableWithinAt h]; rw [fderivWithin_zero_of_not_differentiableWithinAt this]; rw [ContinuousLinearMap.zero_comp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.zero_comp, DifferentiableWithinAt, comp_right_differentiableWithinAt_iff, comp_right_hasFDerivWithinAt_iff, fderivWithin, fderivWithin_zero_of_not_differentiableWithinAt, h.hasFDerivWithinAt, hasFDerivWithinAt, iso.comp_right_differentiableWithinAt_iff, iso.comp_right_hasFDerivWithinAt_iff, zero_comp
-/
theorem comp_right_fderivWithin {f : F -> G} {s : Set F} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 (iso ⁻¹' s) x) :
    fderivWithin 𝕜 (f ∘ iso) (iso ⁻¹' s) x =
      (fderivWithin 𝕜 f s (iso x)).comp (iso : E ->L[𝕜] F) := by
  by_cases h : DifferentiableWithinAt 𝕜 f s (iso x)
  · exact (iso.comp_right_hasFDerivWithinAt_iff.2 h.hasFDerivWithinAt).fderivWithin hxs
  · have : ¬DifferentiableWithinAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x := by
      intro h'
      exact h (iso.comp_right_differentiableWithinAt_iff.1 h')
    rw [fderivWithin_zero_of_not_differentiableWithinAt h]; rw [fderivWithin_zero_of_not_differentiableWithinAt this]; rw [ContinuousLinearMap.zero_comp]

/--
theorem `comp_right_fderiv` / 定理 `comp_right_fderiv`

English:
theorem comp_right_fderiv
  given: {f : F -> G} {x : E}
  proof: by
  rw [← fderivWithin_univ]; rw [← fderivWithin_univ]; rw [← iso.comp_right_fderivWithin]; rw [preimage_univ]
  exact uniqueDiffWithinAt_univ

中文:
定理 comp_right_fderiv
  条件: {f : F -> G} {x : E}
  证明: by
  rw [← fderivWithin_univ]; rw [← fderivWithin_univ]; rw [← iso.comp_right_fderivWithin]; rw [preimage_univ]
  exact uniqueDiffWithinAt_univ

Depends on / 依赖: comp_right_fderivWithin, fderivWithin_univ, iso.comp_right_fderivWithin, preimage_univ, uniqueDiffWithinAt_univ
-/
theorem comp_right_fderiv {f : F -> G} {x : E} :
    fderiv 𝕜 (f ∘ iso) x = (fderiv 𝕜 f (iso x)).comp (iso : E ->L[𝕜] F) := by
  rw [← fderivWithin_univ]; rw [← fderivWithin_univ]; rw [← iso.comp_right_fderivWithin]; rw [preimage_univ]
  exact uniqueDiffWithinAt_univ

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

/-! ### Differentiability of linear isometry equivs, and invariance of differentiability -/


variable (iso : E ≃ₗᵢ[𝕜] F)

@[fun_prop]
/--
theorem `hasStrictFDerivAt` / 定理 `hasStrictFDerivAt`

English:
theorem hasStrictFDerivAt
  statement: HasStrictFDerivAt iso (iso : E ->L[𝕜] F) x
  proof: (iso : E ≃L[𝕜] F).hasStrictFDerivAt

@[fun_prop]

中文:
定理 hasStrictFDerivAt
  结论: HasStrictFDerivAt iso (iso : E ->L[𝕜] F) x
  证明: (iso : E ≃L[𝕜] F).hasStrictFDerivAt

@[fun_prop]
-/
protected theorem hasStrictFDerivAt : HasStrictFDerivAt iso (iso : E ->L[𝕜] F) x :=
  (iso : E ≃L[𝕜] F).hasStrictFDerivAt

@[fun_prop]
/--
theorem `hasFDerivWithinAt` / 定理 `hasFDerivWithinAt`

English:
theorem hasFDerivWithinAt
  statement: HasFDerivWithinAt iso (iso : E ->L[𝕜] F) s x
  proof: (iso : E ≃L[𝕜] F).hasFDerivWithinAt

@[fun_prop]

中文:
定理 hasFDerivWithinAt
  结论: HasFDerivWithinAt iso (iso : E ->L[𝕜] F) s x
  证明: (iso : E ≃L[𝕜] F).hasFDerivWithinAt

@[fun_prop]
-/
protected theorem hasFDerivWithinAt : HasFDerivWithinAt iso (iso : E ->L[𝕜] F) s x :=
  (iso : E ≃L[𝕜] F).hasFDerivWithinAt

@[fun_prop]
/--
theorem `hasFDerivAt` / 定理 `hasFDerivAt`

English:
theorem hasFDerivAt
  statement: HasFDerivAt iso (iso : E ->L[𝕜] F) x
  proof: (iso : E ≃L[𝕜] F).hasFDerivAt

@[fun_prop]

中文:
定理 hasFDerivAt
  结论: 在点处Fréchet可导 iso (iso : E ->L[𝕜] F) x
  证明: (iso : E ≃L[𝕜] F).hasFDerivAt

@[fun_prop]
-/
protected theorem hasFDerivAt : HasFDerivAt iso (iso : E ->L[𝕜] F) x :=
  (iso : E ≃L[𝕜] F).hasFDerivAt

@[fun_prop]
/--
theorem `differentiableAt` / 定理 `differentiableAt`

English:
theorem differentiableAt
  statement: DifferentiableAt 𝕜 iso x
  proof: iso.hasFDerivAt.differentiableAt

@[fun_prop]

中文:
定理 differentiableAt
  结论: DifferentiableAt 𝕜 iso x
  证明: iso.hasFDerivAt.differentiableAt

@[fun_prop]
-/
protected theorem differentiableAt : DifferentiableAt 𝕜 iso x :=
  iso.hasFDerivAt.differentiableAt

@[fun_prop]
/--
theorem `differentiableWithinAt` / 定理 `differentiableWithinAt`

English:
theorem differentiableWithinAt
  statement: DifferentiableWithinAt 𝕜 iso s x
  proof: iso.differentiableAt.differentiableWithinAt

中文:
定理 differentiableWithinAt
  结论: DifferentiableWithinAt 𝕜 iso s x
  证明: iso.differentiableAt.differentiableWithinAt
-/
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 iso s x :=
  iso.differentiableAt.differentiableWithinAt

/--
theorem `fderiv` / 定理 `fderiv`

English:
theorem fderiv
  statement: fderiv 𝕜 iso x = iso
  proof: iso.hasFDerivAt.fderiv

中文:
定理 fderiv
  结论: fderiv 𝕜 iso x = iso
  证明: iso.hasFDerivAt.fderiv
-/
protected theorem fderiv : fderiv 𝕜 iso x = iso :=
  iso.hasFDerivAt.fderiv

/--
theorem `fderivWithin` / 定理 `fderivWithin`

English:
theorem fderivWithin
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  statement: fderivWithin 𝕜 iso s x = iso
  proof: (iso : E ≃L[𝕜] F).fderivWithin hxs

@[fun_prop]

中文:
定理 fderivWithin
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  结论: fderivWithin 𝕜 iso s x = iso
  证明: (iso : E ≃L[𝕜] F).fderivWithin hxs

@[fun_prop]
-/
protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 iso s x = iso :=
  (iso : E ≃L[𝕜] F).fderivWithin hxs

@[fun_prop]
/--
theorem `differentiable` / 定理 `differentiable`

English:
theorem differentiable
  statement: Differentiable 𝕜 iso
  proof: fun _ => iso.differentiableAt

@[fun_prop]

中文:
定理 differentiable
  结论: 可微 𝕜 iso
  证明: fun _ => iso.differentiableAt

@[fun_prop]
-/
protected theorem differentiable : Differentiable 𝕜 iso := fun _ => iso.differentiableAt

@[fun_prop]
/--
theorem `differentiableOn` / 定理 `differentiableOn`

English:
theorem differentiableOn
  statement: DifferentiableOn 𝕜 iso s
  proof: iso.differentiable.differentiableOn

中文:
定理 differentiableOn
  结论: DifferentiableOn 𝕜 iso s
  证明: iso.differentiable.differentiableOn
-/
protected theorem differentiableOn : DifferentiableOn 𝕜 iso s :=
  iso.differentiable.differentiableOn

/--
theorem `comp_differentiableWithinAt_iff` / 定理 `comp_differentiableWithinAt_iff`

English:
theorem comp_differentiableWithinAt_iff
  given: {f : G -> E} {s : Set G} {x : G}
  proof: (iso : E ≃L[𝕜] F).comp_differentiableWithinAt_iff

中文:
定理 comp_differentiableWithinAt_iff
  条件: {f : G -> E} {s : 集合 G} {x : G}
  证明: (iso : E ≃L[𝕜] F).comp_differentiableWithinAt_iff

Depends on / 依赖: comp_differentiableWithinAt_iff
-/
theorem comp_differentiableWithinAt_iff {f : G -> E} {s : Set G} {x : G} :
    DifferentiableWithinAt 𝕜 (iso ∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  (iso : E ≃L[𝕜] F).comp_differentiableWithinAt_iff

/--
theorem `comp_differentiableAt_iff` / 定理 `comp_differentiableAt_iff`

English:
theorem comp_differentiableAt_iff
  given: {f : G -> E} {x : G}
  proof: (iso : E ≃L[𝕜] F).comp_differentiableAt_iff

中文:
定理 comp_differentiableAt_iff
  条件: {f : G -> E} {x : G}
  证明: (iso : E ≃L[𝕜] F).comp_differentiableAt_iff

Depends on / 依赖: comp_differentiableAt_iff
-/
theorem comp_differentiableAt_iff {f : G -> E} {x : G} :
    DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f x :=
  (iso : E ≃L[𝕜] F).comp_differentiableAt_iff

/--
theorem `comp_differentiableOn_iff` / 定理 `comp_differentiableOn_iff`

English:
theorem comp_differentiableOn_iff
  given: {f : G -> E} {s : Set G}
  proof: (iso : E ≃L[𝕜] F).comp_differentiableOn_iff

中文:
定理 comp_differentiableOn_iff
  条件: {f : G -> E} {s : 集合 G}
  证明: (iso : E ≃L[𝕜] F).comp_differentiableOn_iff

Depends on / 依赖: comp_differentiableOn_iff
-/
theorem comp_differentiableOn_iff {f : G -> E} {s : Set G} :
    DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 𝕜 f s :=
  (iso : E ≃L[𝕜] F).comp_differentiableOn_iff

/--
theorem `comp_differentiable_iff` / 定理 `comp_differentiable_iff`

English:
theorem comp_differentiable_iff
  given: {f : G -> E}
  statement: Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f
  proof: (iso : E ≃L[𝕜] F).comp_differentiable_iff

中文:
定理 comp_differentiable_iff
  条件: {f : G -> E}
  结论: 可微 𝕜 (iso ∘ f) ↔ 可微 𝕜 f
  证明: (iso : E ≃L[𝕜] F).comp_differentiable_iff

Depends on / 依赖: comp_differentiable_iff
-/
theorem comp_differentiable_iff {f : G -> E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f :=
  (iso : E ≃L[𝕜] F).comp_differentiable_iff

/--
theorem `comp_hasFDerivWithinAt_iff` / 定理 `comp_hasFDerivWithinAt_iff`

English:
theorem comp_hasFDerivWithinAt_iff
  given: {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] E}
  proof: (iso : E ≃L[𝕜] F).comp_hasFDerivWithinAt_iff

中文:
定理 comp_hasFDerivWithinAt_iff
  条件: {f : G -> E} {s : 集合 G} {x : G} {f' : G ->L[𝕜] E}
  证明: (iso : E ≃L[𝕜] F).comp_hasFDerivWithinAt_iff

Depends on / 依赖: comp_hasFDerivWithinAt_iff
-/
theorem comp_hasFDerivWithinAt_iff {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] E} :
    HasFDerivWithinAt (iso ∘ f) ((iso : E ->L[𝕜] F).comp f') s x ↔ HasFDerivWithinAt f f' s x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivWithinAt_iff

/--
theorem `comp_hasStrictFDerivAt_iff` / 定理 `comp_hasStrictFDerivAt_iff`

English:
theorem comp_hasStrictFDerivAt_iff
  given: {f : G -> E} {x : G} {f' : G ->L[𝕜] E}
  proof: (iso : E ≃L[𝕜] F).comp_hasStrictFDerivAt_iff

中文:
定理 comp_hasStrictFDerivAt_iff
  条件: {f : G -> E} {x : G} {f' : G ->L[𝕜] E}
  证明: (iso : E ≃L[𝕜] F).comp_hasStrictFDerivAt_iff

Depends on / 依赖: comp_hasStrictFDerivAt_iff
-/
theorem comp_hasStrictFDerivAt_iff {f : G -> E} {x : G} {f' : G ->L[𝕜] E} :
    HasStrictFDerivAt (iso ∘ f) ((iso : E ->L[𝕜] F).comp f') x ↔ HasStrictFDerivAt f f' x :=
  (iso : E ≃L[𝕜] F).comp_hasStrictFDerivAt_iff

/--
theorem `comp_hasFDerivAt_iff` / 定理 `comp_hasFDerivAt_iff`

English:
theorem comp_hasFDerivAt_iff
  given: {f : G -> E} {x : G} {f' : G ->L[𝕜] E}
  proof: (iso : E ≃L[𝕜] F).comp_hasFDerivAt_iff

中文:
定理 comp_hasFDerivAt_iff
  条件: {f : G -> E} {x : G} {f' : G ->L[𝕜] E}
  证明: (iso : E ≃L[𝕜] F).comp_hasFDerivAt_iff

Depends on / 依赖: comp_hasFDerivAt_iff
-/
theorem comp_hasFDerivAt_iff {f : G -> E} {x : G} {f' : G ->L[𝕜] E} :
    HasFDerivAt (iso ∘ f) ((iso : E ->L[𝕜] F).comp f') x ↔ HasFDerivAt f f' x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivAt_iff

/--
theorem `comp_hasFDerivWithinAt_iff'` / 定理 `comp_hasFDerivWithinAt_iff'`

English:
theorem comp_hasFDerivWithinAt_iff'
  given: {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] F}
  proof: (iso : E ≃L[𝕜] F).comp_hasFDerivWithinAt_iff'

中文:
定理 comp_hasFDerivWithinAt_iff'
  条件: {f : G -> E} {s : 集合 G} {x : G} {f' : G ->L[𝕜] F}
  证明: (iso : E ≃L[𝕜] F).comp_hasFDerivWithinAt_iff'

Depends on / 依赖: comp_hasFDerivWithinAt_iff
-/
theorem comp_hasFDerivWithinAt_iff' {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] F} :
    HasFDerivWithinAt (iso ∘ f) f' s x ↔ HasFDerivWithinAt f ((iso.symm : F ->L[𝕜] E).comp f') s x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivWithinAt_iff'

/--
theorem `comp_hasFDerivAt_iff'` / 定理 `comp_hasFDerivAt_iff'`

English:
theorem comp_hasFDerivAt_iff'
  given: {f : G -> E} {x : G} {f' : G ->L[𝕜] F}
  proof: (iso : E ≃L[𝕜] F).comp_hasFDerivAt_iff'

中文:
定理 comp_hasFDerivAt_iff'
  条件: {f : G -> E} {x : G} {f' : G ->L[𝕜] F}
  证明: (iso : E ≃L[𝕜] F).comp_hasFDerivAt_iff'

Depends on / 依赖: comp_hasFDerivAt_iff
-/
theorem comp_hasFDerivAt_iff' {f : G -> E} {x : G} {f' : G ->L[𝕜] F} :
    HasFDerivAt (iso ∘ f) f' x ↔ HasFDerivAt f ((iso.symm : F ->L[𝕜] E).comp f') x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivAt_iff'

/--
theorem `comp_fderivWithin` / 定理 `comp_fderivWithin`

English:
theorem comp_fderivWithin
  given: {f : G -> E} {s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (iso : E ≃L[𝕜] F).comp_fderivWithin hxs

中文:
定理 comp_fderivWithin
  条件: {f : G -> E} {s : 集合 G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (iso : E ≃L[𝕜] F).comp_fderivWithin hxs

Depends on / 依赖: comp_fderivWithin
-/
theorem comp_fderivWithin {f : G -> E} {s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (iso ∘ f) s x = (iso : E ->L[𝕜] F).comp (fderivWithin 𝕜 f s x) :=
  (iso : E ≃L[𝕜] F).comp_fderivWithin hxs

/--
theorem `comp_fderiv` / 定理 `comp_fderiv`

English:
theorem comp_fderiv
  given: {f : G -> E} {x : G}
  proof: (iso : E ≃L[𝕜] F).comp_fderiv

中文:
定理 comp_fderiv
  条件: {f : G -> E} {x : G}
  证明: (iso : E ≃L[𝕜] F).comp_fderiv

Depends on / 依赖: comp_fderiv
-/
theorem comp_fderiv {f : G -> E} {x : G} :
    fderiv 𝕜 (iso ∘ f) x = (iso : E ->L[𝕜] F).comp (fderiv 𝕜 f x) :=
  (iso : E ≃L[𝕜] F).comp_fderiv

/--
theorem `comp_fderiv'` / 定理 `comp_fderiv'`

English:
theorem comp_fderiv'
  given: {f : G -> E}
  proof: by
  ext x : 1
  exact LinearIsometryEquiv.comp_fderiv iso

中文:
定理 comp_fderiv'
  条件: {f : G -> E}
  证明: by
  ext x : 1
  exact LinearIsometryEquiv.comp_fderiv iso

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.comp_fderiv, comp_fderiv
-/
theorem comp_fderiv' {f : G -> E} :
    fderiv 𝕜 (iso ∘ f) = fun x => (iso : E ->L[𝕜] F).comp (fderiv 𝕜 f x) := by
  ext x : 1
  exact LinearIsometryEquiv.comp_fderiv iso

end LinearIsometryEquiv

/--
theorem `HasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE` / 定理 `HasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE`

English:
theorem HasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE
  statement: (h : HasFDerivWithinAt f f' s x)
  proof: by
  replace hf' : exists C, forall z, ‖z‖ <= C * ‖f' z‖ := by
    obtain ⟨C, hC⟩ := hf'
    exact ⟨C, fun x => by simpa using hC.le_mul_dist 0 x⟩
  have A : (fun z => z - x) =O[𝓝[s] x] fun z => f' (z - x) :=
isBigO_iff.mpr hf'.imp fun C hC => Eventually.of_forall fun z => hC (z - x)
  have : (fun z => f z - f x) ~[𝓝[s] x] fun z => f' (z - x) := h.isLittleO.trans_isBigO A
  have : forallᶠ (x_1 : E) in 𝓝[s] x, x_1 in ({x}ᶜ : Set E) -> f x_1 in ({f x}ᶜ : Set F) := by
    simpa [sub_eq_zero, not_imp_not] using (A.trans this.isBigO_symm).eq_zero_imp
  apply le_inf ((map_mono (nhdsWithin_mono x sdiff_subset)).trans h.continuousWithinAt)
  rwa [le_principal_iff, ← eventually_mem_set, eventually_map, sdiff_eq, nhdsWithin_inter',
    eventually_inf_principal]

中文:
定理 HasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE
  结论: (h : HasFDerivWithinAt f f' s x)
  证明: by
  replace hf' : exists C, forall z, ‖z‖ <= C * ‖f' z‖ := by
    obtain ⟨C, hC⟩ := hf'
    exact ⟨C, fun x => by simpa using hC.le_mul_dist 0 x⟩
  have A : (fun z => z - x) =O[𝓝[s] x] fun z => f' (z - x) :=
isBigO_iff.mpr hf'.imp fun C hC => Eventually.of_forall fun z => hC (z - x)
  have : (fun z => f z - f x) ~[𝓝[s] x] fun z => f' (z - x) := h.isLittleO.trans_isBigO A
  have : forallᶠ (x_1 : E) in 𝓝[s] x, x_1 in ({x}ᶜ : Set E) -> f x_1 in ({f x}ᶜ : Set F) := by
    simpa [sub_eq_zero, not_imp_not] using (A.trans this.isBigO_symm).eq_zero_imp
  apply le_inf ((map_mono (nhdsWithin_mono x sdiff_subset)).trans h.continuousWithinAt)
  rwa [le_principal_iff, ← eventually_mem_set, eventually_map, sdiff_eq, nhdsWithin_inter',
    eventually_inf_principal]

Depends on / 依赖: A.tran, Eventually, Eventually.of_forall, h.isLittleO.trans_isBigO, hC.le_mul_dist, isBigO_iff, isBigO_iff.mpr, isLittleO, le_mul_dist, not_imp_not, of_forall, replace, sub_eq_zero, trans_isBigO
-/
theorem HasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE (h : HasFDerivWithinAt f f' s x)
    (hf' : exists C, AntilipschitzWith C f') : Tendsto f (𝓝[s \ {x}] x) (𝓝[!=] f x) := by
  replace hf' : exists C, forall z, ‖z‖ <= C * ‖f' z‖ := by
    obtain ⟨C, hC⟩ := hf'
    exact ⟨C, fun x => by simpa using hC.le_mul_dist 0 x⟩
  have A : (fun z => z - x) =O[𝓝[s] x] fun z => f' (z - x) :=
isBigO_iff.mpr hf'.imp fun C hC => Eventually.of_forall fun z => hC (z - x)
  have : (fun z => f z - f x) ~[𝓝[s] x] fun z => f' (z - x) := h.isLittleO.trans_isBigO A
  have : forallᶠ (x_1 : E) in 𝓝[s] x, x_1 in ({x}ᶜ : Set E) -> f x_1 in ({f x}ᶜ : Set F) := by
    simpa [sub_eq_zero, not_imp_not] using (A.trans this.isBigO_symm).eq_zero_imp
  apply le_inf ((map_mono (nhdsWithin_mono x sdiff_subset)).trans h.continuousWithinAt)
  rwa [le_principal_iff, ← eventually_mem_set, eventually_map, sdiff_eq, nhdsWithin_inter',
    eventually_inf_principal]

/--
theorem `HasFDerivWithinAt.eventually_ne` / 定理 `HasFDerivWithinAt.eventually_ne`

English:
theorem HasFDerivWithinAt.eventually_ne
  statement: (h : HasFDerivWithinAt f f' s x)
  proof: by
  rw [← eventually_map (m := f) (P := fun z => z != c)]
  apply Eventually.filter_mono (h.tendsto_nhdsWithin_nhdsNE hf')
  rcases eq_or_ne (f x) c with rfl | hc
  · exact eventually_mem_nhdsWithin
  · exact eventually_ne_nhdsWithin hc

中文:
定理 HasFDerivWithinAt.eventually_ne
  结论: (h : HasFDerivWithinAt f f' s x)
  证明: by
  rw [← eventually_map (m := f) (P := fun z => z != c)]
  apply Eventually.filter_mono (h.tendsto_nhdsWithin_nhdsNE hf')
  rcases eq_or_ne (f x) c with rfl | hc
  · exact eventually_mem_nhdsWithin
  · exact eventually_ne_nhdsWithin hc

Depends on / 依赖: Eventually, Eventually.filter_mono, eq_or_ne, eventually_map, eventually_mem_nhdsWithin, eventually_ne_nhdsWithin, filter_mono, h.tendsto_nhdsWithin_nhdsNE, tendsto_nhdsWithin_nhdsNE
-/
theorem HasFDerivWithinAt.eventually_ne (h : HasFDerivWithinAt f f' s x)
    (hf' : exists C, AntilipschitzWith C f') : forallᶠ z in 𝓝[s \ {x}] x, f z != c := by
  rw [← eventually_map (m := f) (P := fun z => z != c)]
  apply Eventually.filter_mono (h.tendsto_nhdsWithin_nhdsNE hf')
  rcases eq_or_ne (f x) c with rfl | hc
  · exact eventually_mem_nhdsWithin
  · exact eventually_ne_nhdsWithin hc

/--
theorem `HasFDerivWithinAt.eventually_notMem` / 定理 `HasFDerivWithinAt.eventually_notMem`

English:
theorem HasFDerivWithinAt.eventually_notMem
  statement: (h : HasFDerivWithinAt f f' s x)
  proof: by
  rw [accPt_iff_frequently_nhdsNE]; rw [not_frequently] at ht
  exact eventually_map.mp (ht.filter_mono (h.tendsto_nhdsWithin_nhdsNE hf'))

中文:
定理 HasFDerivWithinAt.eventually_notMem
  结论: (h : HasFDerivWithinAt f f' s x)
  证明: by
  rw [accPt_iff_frequently_nhdsNE]; rw [not_frequently] at ht
  exact eventually_map.mp (ht.filter_mono (h.tendsto_nhdsWithin_nhdsNE hf'))

Depends on / 依赖: accPt_iff_frequently_nhdsNE, eventually_map, eventually_map.mp, filter_mono, h.tendsto_nhdsWithin_nhdsNE, ht.filter_mono, not_frequently, tendsto_nhdsWithin_nhdsNE
-/
theorem HasFDerivWithinAt.eventually_notMem (h : HasFDerivWithinAt f f' s x)
    (hf' : exists C, AntilipschitzWith C f') (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) :
    forallᶠ z in 𝓝[s \ {x}] x, f z ∉ t := by
  rw [accPt_iff_frequently_nhdsNE]; rw [not_frequently] at ht
  exact eventually_map.mp (ht.filter_mono (h.tendsto_nhdsWithin_nhdsNE hf'))

/--
theorem `HasFDerivAt.tendsto_nhdsNE` / 定理 `HasFDerivAt.tendsto_nhdsNE`

English:
theorem HasFDerivAt.tendsto_nhdsNE
  statement: (h : HasFDerivAt f f' x)
  proof: by
  simpa only [compl_eq_univ_sdiff] using (hasFDerivWithinAt_univ.2 h).tendsto_nhdsWithin_nhdsNE hf'

中文:
定理 在点处Fréchet可导.tendsto_nhdsNE
  结论: (h : 在点处Fréchet可导 f f' x)
  证明: by
  simpa only [compl_eq_univ_sdiff] using (hasFDerivWithinAt_univ.2 h).tendsto_nhdsWithin_nhdsNE hf'

Depends on / 依赖: compl_eq_univ_sdiff, hasFDerivWithinAt_univ, tendsto_nhdsWithin_nhdsNE
-/
theorem HasFDerivAt.tendsto_nhdsNE (h : HasFDerivAt f f' x)
    (hf' : exists C, AntilipschitzWith C f') : Tendsto f (𝓝[!=] x) (𝓝[!=] f x) := by
  simpa only [compl_eq_univ_sdiff] using (hasFDerivWithinAt_univ.2 h).tendsto_nhdsWithin_nhdsNE hf'

/--
theorem `HasFDerivAt.eventually_ne` / 定理 `HasFDerivAt.eventually_ne`

English:
theorem HasFDerivAt.eventually_ne
  given: (h : HasFDerivAt f f' x) (hf' : exists C, AntilipschitzWith C f')
  proof: by
  simpa only [compl_eq_univ_sdiff] using (hasFDerivWithinAt_univ.2 h).eventually_ne hf'

中文:
定理 在点处Fréchet可导.eventually_ne
  条件: (h : 在点处Fréchet可导 f f' x) (hf' : 存在 C, AntilipschitzWith C f')
  证明: by
  simpa only [compl_eq_univ_sdiff] using (hasFDerivWithinAt_univ.2 h).eventually_ne hf'

Depends on / 依赖: compl_eq_univ_sdiff, eventually_ne, hasFDerivWithinAt_univ
-/
theorem HasFDerivAt.eventually_ne (h : HasFDerivAt f f' x) (hf' : exists C, AntilipschitzWith C f') :
    forallᶠ z in 𝓝[!=] x, f z != c := by
  simpa only [compl_eq_univ_sdiff] using (hasFDerivWithinAt_univ.2 h).eventually_ne hf'

/--
theorem `HasFDerivAt.eventually_notMem` / 定理 `HasFDerivAt.eventually_notMem`

English:
theorem HasFDerivAt.eventually_notMem
  statement: (h : HasFDerivAt f f' x) (hf' : exists C, AntilipschitzWith C f')
  proof: by
  simpa only [compl_eq_univ_sdiff] using (hasFDerivWithinAt_univ.2 h).eventually_notMem hf' t ht

中文:
定理 在点处Fréchet可导.eventually_notMem
  结论: (h : 在点处Fréchet可导 f f' x) (hf' : 存在 C, AntilipschitzWith C f')
  证明: by
  simpa only [compl_eq_univ_sdiff] using (hasFDerivWithinAt_univ.2 h).eventually_notMem hf' t ht

Depends on / 依赖: compl_eq_univ_sdiff, eventually_notMem, hasFDerivWithinAt_univ
-/
theorem HasFDerivAt.eventually_notMem (h : HasFDerivAt f f' x) (hf' : exists C, AntilipschitzWith C f')
    (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) : forallᶠ z in 𝓝[!=] x, f z ∉ t := by
  simpa only [compl_eq_univ_sdiff] using (hasFDerivWithinAt_univ.2 h).eventually_notMem hf' t ht

end

section

/-
  In the special case of a normed space over the reals,
  we can use scalar multiplication in the `tendsto` characterization
  of the Fréchet derivative.
-/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {f : E -> F} {f' : E ->L[Real] F} {x : E}

/--
theorem `has_fderiv_at_filter_real_equiv` / 定理 `has_fderiv_at_filter_real_equiv`

English:
theorem has_fderiv_at_filter_real_equiv
  given: {L : Filter E}
  proof: by
  symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_congr fun x' => ?_
  simp [norm_smul]

中文:
定理 has_fderiv_at_filter_real_equiv
  条件: {L : 滤子 E}
  证明: by
  symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_congr fun x' => ?_
  simp [norm_smul]

Depends on / 依赖: norm_smul, tendsto_congr, tendsto_iff_norm_sub_tendsto_zero
-/
theorem has_fderiv_at_filter_real_equiv {L : Filter E} :
    Tendsto (fun x' : E => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) L (𝓝 0) ↔
      Tendsto (fun x' : E => ‖x' - x‖⁻¹ • (f x' - f x - f' (x' - x))) L (𝓝 0) := by
  symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_congr fun x' => ?_
  simp [norm_smul]

/--
theorem `HasFDerivAt.lim_real` / 定理 `HasFDerivAt.lim_real`

English:
theorem HasFDerivAt.lim_real
  given: (hf : HasFDerivAt f f' x) (v : E)
  proof: by
  apply hf.lim v
  rw [tendsto_atTop_atTop]
  exact fun b => ⟨b, fun a ha => le_trans ha (le_abs_self _)⟩

中文:
定理 在点处Fréchet可导.lim_real
  条件: (hf : 在点处Fréchet可导 f f' x) (v : E)
  证明: by
  apply hf.lim v
  rw [tendsto_atTop_atTop]
  exact fun b => ⟨b, fun a ha => le_trans ha (le_abs_self _)⟩

Depends on / 依赖: hf.lim, le_abs_self, le_trans, tendsto_atTop_atTop
-/
theorem HasFDerivAt.lim_real (hf : HasFDerivAt f f' x) (v : E) :
    Tendsto (fun c : Real => c • (f (x + c⁻¹ • v) - f x)) atTop (𝓝 (f' v)) := by
  apply hf.lim v
  rw [tendsto_atTop_atTop]
  exact fun b => ⟨b, fun a ha => le_trans ha (le_abs_self _)⟩

end

open scoped Pointwise

section TangentCone

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E -> F} {s : Set E}
  {f' : E ->L[𝕜] F} {x : E}

/--
theorem `HasFDerivWithinAt.mapsTo_tangent_cone` / 定理 `HasFDerivWithinAt.mapsTo_tangent_cone`

English:
theorem HasFDerivWithinAt.mapsTo_tangent_cone
  given: (h : HasFDerivWithinAt f f' s x)
  proof: by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  apply mem_tangentConeAt_of_seq l c (fun n => f (x + d n) - f x)
  · rw [tendsto_sub_nhds_zero_iff]
refine h.continuousWithinAt.tendsto.comp tendsto_nhdsWithin_iff.mpr ⟨?_, hds⟩
    simpa using tendsto_const_nhds.add hd₀
  · exact hds.mono fun n hn => ⟨x + d n, hn, by simp⟩
  · exact h.lim hd₀ hds hcd

中文:
定理 HasFDerivWithinAt.mapsTo_tangent_cone
  条件: (h : HasFDerivWithinAt f f' s x)
  证明: by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  apply mem_tangentConeAt_of_seq l c (fun n => f (x + d n) - f x)
  · rw [tendsto_sub_nhds_zero_iff]
refine h.continuousWithinAt.tendsto.comp tendsto_nhdsWithin_iff.mpr ⟨?_, hds⟩
    simpa using tendsto_const_nhds.add hd₀
  · exact hds.mono fun n hn => ⟨x + d n, hn, by simp⟩
  · exact h.lim hd₀ hds hcd

Depends on / 依赖: continuousWithinAt, exists_fun_of_mem_tangentConeAt, h.continuousWithinAt.tendsto.comp, h.lim, hds.mono, mem_tangentConeAt_of_seq, tendsto, tendsto_const_nhds, tendsto_const_nhds.add, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mpr, tendsto_sub_nhds_zero_iff
-/
theorem HasFDerivWithinAt.mapsTo_tangent_cone (h : HasFDerivWithinAt f f' s x) :
    MapsTo f' (tangentConeAt 𝕜 s x) (tangentConeAt 𝕜 (f '' s) (f x)) := by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  apply mem_tangentConeAt_of_seq l c (fun n => f (x + d n) - f x)
  · rw [tendsto_sub_nhds_zero_iff]
refine h.continuousWithinAt.tendsto.comp tendsto_nhdsWithin_iff.mpr ⟨?_, hds⟩
    simpa using tendsto_const_nhds.add hd₀
  · exact hds.mono fun n hn => ⟨x + d n, hn, by simp⟩
  · exact h.lim hd₀ hds hcd

/--
theorem `HasFDerivWithinAt.uniqueDiffWithinAt` / 定理 `HasFDerivWithinAt.uniqueDiffWithinAt`

English:
theorem HasFDerivWithinAt.uniqueDiffWithinAt
  statement: (h : HasFDerivWithinAt f f' s x)
  proof: by
  refine ⟨h'.dense_of_mapsTo f'.continuous hs.1 ?_, h.continuousWithinAt.mem_closure_image hs.2⟩
  change
    Submodule.span 𝕜 (tangentConeAt 𝕜 s x) <=
      (Submodule.span 𝕜 (tangentConeAt 𝕜 (f '' s) (f x))).comap f'.toLinearMap
  rw [Submodule.span_le]
  exact h.mapsTo_tangent_cone.mono Subset.rfl Submodule.subset_span

中文:
定理 HasFDerivWithinAt.uniqueDiffWithinAt
  结论: (h : HasFDerivWithinAt f f' s x)
  证明: by
  refine ⟨h'.dense_of_mapsTo f'.continuous hs.1 ?_, h.continuousWithinAt.mem_closure_image hs.2⟩
  change
    Submodule.span 𝕜 (tangentConeAt 𝕜 s x) <=
      (Submodule.span 𝕜 (tangentConeAt 𝕜 (f '' s) (f x))).comap f'.toLinearMap
  rw [Submodule.span_le]
  exact h.mapsTo_tangent_cone.mono Subset.rfl Submodule.subset_span

Depends on / 依赖: Submodule, Submodule.span, Submodule.span_le, Submodule.subset_span, Subset, Subset.rfl, continuous, continuousWithinAt, dense_of_mapsTo, h.continuousWithinAt.mem_closure_image, h.mapsTo_tangent_cone.mono, mapsTo_tangent_cone, mem_closure_image, span_le, subset_span, tangentConeAt, toLinearMap
-/
theorem HasFDerivWithinAt.uniqueDiffWithinAt (h : HasFDerivWithinAt f f' s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) (h' : DenseRange f') : UniqueDiffWithinAt 𝕜 (f '' s) (f x) := by
  refine ⟨h'.dense_of_mapsTo f'.continuous hs.1 ?_, h.continuousWithinAt.mem_closure_image hs.2⟩
  change
    Submodule.span 𝕜 (tangentConeAt 𝕜 s x) <=
      (Submodule.span 𝕜 (tangentConeAt 𝕜 (f '' s) (f x))).comap f'.toLinearMap
  rw [Submodule.span_le]
  exact h.mapsTo_tangent_cone.mono Subset.rfl Submodule.subset_span

/--
theorem `UniqueDiffOn.image` / 定理 `UniqueDiffOn.image`

English:
theorem UniqueDiffOn.image
  statement: {f' : E -> E ->L[𝕜] F} (hs : UniqueDiffOn 𝕜 s)
  proof: forall_mem_image.2 fun x hx => (hf' x hx).uniqueDiffWithinAt (hs x hx) (hd x hx)

中文:
定理 UniqueDiffOn.像
  结论: {f' : E -> E ->L[𝕜] F} (hs : UniqueDiffOn 𝕜 s)
  证明: forall_mem_image.2 fun x hx => (hf' x hx).uniqueDiffWithinAt (hs x hx) (hd x hx)

Depends on / 依赖: forall_mem_image, uniqueDiffWithinAt
-/
theorem UniqueDiffOn.image {f' : E -> E ->L[𝕜] F} (hs : UniqueDiffOn 𝕜 s)
    (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hd : forall x in s, DenseRange (f' x)) :
    UniqueDiffOn 𝕜 (f '' s) :=
  forall_mem_image.2 fun x hx => (hf' x hx).uniqueDiffWithinAt (hs x hx) (hd x hx)

/--
theorem `HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv` / 定理 `HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv`

English:
theorem HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv
  statement: (e' : E ≃L[𝕜] F)
  proof: h.uniqueDiffWithinAt hs e'.surjective.denseRange

中文:
定理 HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv
  结论: (e' : E ≃L[𝕜] F)
  证明: h.uniqueDiffWithinAt hs e'.surjective.denseRange

Depends on / 依赖: denseRange, h.uniqueDiffWithinAt, surjective, surjective.denseRange, uniqueDiffWithinAt
-/
theorem HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv (e' : E ≃L[𝕜] F)
    (h : HasFDerivWithinAt f (e' : E ->L[𝕜] F) s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜 (f '' s) (f x) :=
  h.uniqueDiffWithinAt hs e'.surjective.denseRange

/--
theorem `ContinuousLinearEquiv.uniqueDiffOn_image` / 定理 `ContinuousLinearEquiv.uniqueDiffOn_image`

English:
theorem ContinuousLinearEquiv.uniqueDiffOn_image
  given: (e : E ≃L[𝕜] F) (h : UniqueDiffOn 𝕜 s)
  proof: h.image (fun _ _ => e.hasFDerivWithinAt) fun _ _ => e.surjective.denseRange

@[simp]

中文:
定理 连续线性等价.uniqueDiffOn_image
  条件: (e : E ≃L[𝕜] F) (h : UniqueDiffOn 𝕜 s)
  证明: h.image (fun _ _ => e.hasFDerivWithinAt) fun _ _ => e.surjective.denseRange

@[simp]

Depends on / 依赖: denseRange, e.hasFDerivWithinAt, e.surjective.denseRange, h.image, hasFDerivWithinAt, surjective
-/
theorem ContinuousLinearEquiv.uniqueDiffOn_image (e : E ≃L[𝕜] F) (h : UniqueDiffOn 𝕜 s) :
    UniqueDiffOn 𝕜 (e '' s) :=
  h.image (fun _ _ => e.hasFDerivWithinAt) fun _ _ => e.surjective.denseRange

@[simp]
/--
theorem `ContinuousLinearEquiv.uniqueDiffOn_image_iff` / 定理 `ContinuousLinearEquiv.uniqueDiffOn_image_iff`

English:
theorem ContinuousLinearEquiv.uniqueDiffOn_image_iff
  given: (e : E ≃L[𝕜] F)
  proof: ⟨fun h => e.symm_image_image s ▸ e.symm.uniqueDiffOn_image h, e.uniqueDiffOn_image⟩

@[simp]

中文:
定理 连续线性等价.uniqueDiffOn_image_iff
  条件: (e : E ≃L[𝕜] F)
  证明: ⟨fun h => e.symm_image_image s ▸ e.symm.uniqueDiffOn_image h, e.uniqueDiffOn_image⟩

@[simp]

Depends on / 依赖: e.symm.uniqueDiffOn_image, e.symm_image_image, e.uniqueDiffOn_image, symm_image_image, uniqueDiffOn_image
-/
theorem ContinuousLinearEquiv.uniqueDiffOn_image_iff (e : E ≃L[𝕜] F) :
    UniqueDiffOn 𝕜 (e '' s) ↔ UniqueDiffOn 𝕜 s :=
  ⟨fun h => e.symm_image_image s ▸ e.symm.uniqueDiffOn_image h, e.uniqueDiffOn_image⟩

@[simp]
/--
theorem `ContinuousLinearEquiv.uniqueDiffOn_preimage_iff` / 定理 `ContinuousLinearEquiv.uniqueDiffOn_preimage_iff`

English:
theorem ContinuousLinearEquiv.uniqueDiffOn_preimage_iff
  given: (e : F ≃L[𝕜] E)
  proof: by
  rw [← e.image_symm_eq_preimage]; rw [e.symm.uniqueDiffOn_image_iff]

中文:
定理 连续线性等价.uniqueDiffOn_preimage_iff
  条件: (e : F ≃L[𝕜] E)
  证明: by
  rw [← e.image_symm_eq_preimage]; rw [e.symm.uniqueDiffOn_image_iff]

Depends on / 依赖: e.image_symm_eq_preimage, e.symm.uniqueDiffOn_image_iff, image_symm_eq_preimage, uniqueDiffOn_image_iff
-/
theorem ContinuousLinearEquiv.uniqueDiffOn_preimage_iff (e : F ≃L[𝕜] E) :
    UniqueDiffOn 𝕜 (e ⁻¹' s) ↔ UniqueDiffOn 𝕜 s := by
  rw [← e.image_symm_eq_preimage]; rw [e.symm.uniqueDiffOn_image_iff]

/--
theorem `UniqueDiffWithinAt.smul` / 定理 `UniqueDiffWithinAt.smul`

English:
theorem UniqueDiffWithinAt.smul
  statement: (h : UniqueDiffWithinAt 𝕜 s x)
  proof: (ContinuousLinearEquiv.smulLeft <| Units.mk0 c hc).hasFDerivWithinAt
.uniqueDiffWithinAt_of_continuousLinearEquiv _ h

中文:
定理 UniqueDiffWithinAt.smul
  结论: (h : UniqueDiffWithinAt 𝕜 s x)
  证明: (ContinuousLinearEquiv.smulLeft <| Units.mk0 c hc).hasFDerivWithinAt
.uniqueDiffWithinAt_of_continuousLinearEquiv _ h
-/
protected theorem UniqueDiffWithinAt.smul (h : UniqueDiffWithinAt 𝕜 s x)
    {G : Type*} [GroupWithZero G] [DistribMulAction G E] [ContinuousConstSMul G E]
    [SMulCommClass G 𝕜 E] {c : G} (hc : c != 0) :
    UniqueDiffWithinAt 𝕜 (c • s) (c • x) :=
  (ContinuousLinearEquiv.smulLeft <| Units.mk0 c hc).hasFDerivWithinAt
.uniqueDiffWithinAt_of_continuousLinearEquiv _ h

/--
theorem `UniqueDiffWithinAt.smul_iff` / 定理 `UniqueDiffWithinAt.smul_iff`

English:
theorem UniqueDiffWithinAt.smul_iff
  proof: ⟨fun h => by simpa [hc] using h.smul (inv_ne_zero hc), (.smul · hc)⟩

中文:
定理 UniqueDiffWithinAt.smul_iff
  证明: ⟨fun h => by simpa [hc] using h.smul (inv_ne_zero hc), (.smul · hc)⟩
-/
protected theorem UniqueDiffWithinAt.smul_iff
    {G : Type*} [GroupWithZero G] [DistribMulAction G E] [ContinuousConstSMul G E]
    [SMulCommClass G 𝕜 E] {c : G} (hc : c != 0) :
    UniqueDiffWithinAt 𝕜 (c • s) (c • x) ↔ UniqueDiffWithinAt 𝕜 s x :=
  ⟨fun h => by simpa [hc] using h.smul (inv_ne_zero hc), (.smul · hc)⟩

end TangentCone

section SMulLeft

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E -> F} {s : Set E}
  {f' : E ->L[𝕜] F} {x : E}

/--
theorem `hasFDerivWithinAt_comp_smul_smul_iff` / 定理 `hasFDerivWithinAt_comp_smul_smul_iff`

English:
theorem hasFDerivWithinAt_comp_smul_smul_iff
  given: {c : 𝕜}
  proof: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [hasFDerivWithinAt_const, HasFDerivWithinAt.of_subsingleton (subsingleton_zero_smul_set _)]
  · lift c to 𝕜ˣ using IsUnit.mk0 c hc
    have A : f'.comp ((ContinuousLinearEquiv.smulLeft c : E ≃L[𝕜] E) : E ->L[𝕜] E) = c • f' := by
      ext; simp
    rw [← Units.smul_def c x]; rw [← ContinuousLinearEquiv.smulLeft_apply_apply (R₁ := 𝕜)]; rw [← ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff]; rw [A]
    simp [Function.comp_def, ← Units.smul_def, ← preimage_smul_inv, preimage_preimage]

中文:
定理 hasFDerivWithinAt_comp_smul_smul_iff
  条件: {c : 𝕜}
  证明: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [hasFDerivWithinAt_const, HasFDerivWithinAt.of_subsingleton (subsingleton_zero_smul_set _)]
  · lift c to 𝕜ˣ using IsUnit.mk0 c hc
    have A : f'.comp ((ContinuousLinearEquiv.smulLeft c : E ≃L[𝕜] E) : E ->L[𝕜] E) = c • f' := by
      ext; simp
    rw [← Units.smul_def c x]; rw [← ContinuousLinearEquiv.smulLeft_apply_apply (R₁ := 𝕜)]; rw [← ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff]; rw [A]
    simp [Function.comp_def, ← Units.smul_def, ← preimage_smul_inv, preimage_preimage]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff, ContinuousLinearEquiv.smulLeft, ContinuousLinearEquiv.smulLeft_apply_apply, Function, Function.comp_def, HasFDerivWithinAt, HasFDerivWithinAt.of_subsingleton, IsUnit, IsUnit.mk0, Units.smul_def, comp_def, comp_right_hasFDerivWithinAt_iff, eq_or_ne, hasFDerivWithinAt_const, of_subsingleton, preimage_smul_inv, smulLeft, smulLeft_apply_apply, smul_def
-/
theorem hasFDerivWithinAt_comp_smul_smul_iff {c : 𝕜} :
    HasFDerivWithinAt (f <| c • ·) (c • f') s x ↔ HasFDerivWithinAt f f' (c • s) (c • x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [hasFDerivWithinAt_const, HasFDerivWithinAt.of_subsingleton (subsingleton_zero_smul_set _)]
  · lift c to 𝕜ˣ using IsUnit.mk0 c hc
    have A : f'.comp ((ContinuousLinearEquiv.smulLeft c : E ≃L[𝕜] E) : E ->L[𝕜] E) = c • f' := by
      ext; simp
    rw [← Units.smul_def c x]; rw [← ContinuousLinearEquiv.smulLeft_apply_apply (R₁ := 𝕜)]; rw [← ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff]; rw [A]
    simp [Function.comp_def, ← Units.smul_def, ← preimage_smul_inv, preimage_preimage]

/--
theorem `hasFDerivWithinAt_comp_smul_iff_smul` / 定理 `hasFDerivWithinAt_comp_smul_iff_smul`

English:
theorem hasFDerivWithinAt_comp_smul_iff_smul
  given: {c : 𝕜} (hc : c != 0)
  proof: by
  simp only [← hasFDerivWithinAt_comp_smul_smul_iff, Pi.smul_apply]
  lift c to 𝕜ˣ using IsUnit.mk0 c hc
  exact (ContinuousLinearEquiv.smulLeft c).comp_hasFDerivWithinAt_iff.symm

中文:
定理 hasFDerivWithinAt_comp_smul_iff_smul
  条件: {c : 𝕜} (hc : c != 0)
  证明: by
  simp only [← hasFDerivWithinAt_comp_smul_smul_iff, Pi.smul_apply]
  lift c to 𝕜ˣ using IsUnit.mk0 c hc
  exact (ContinuousLinearEquiv.smulLeft c).comp_hasFDerivWithinAt_iff.symm

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.smulLeft, IsUnit, IsUnit.mk0, Pi.smul_apply, comp_hasFDerivWithinAt_iff, comp_hasFDerivWithinAt_iff.symm, hasFDerivWithinAt_comp_smul_smul_iff, smulLeft, smul_apply
-/
theorem hasFDerivWithinAt_comp_smul_iff_smul {c : 𝕜} (hc : c != 0) :
    HasFDerivWithinAt (f <| c • ·) f' s x ↔ HasFDerivWithinAt (c • f) f' (c • s) (c • x) := by
  simp only [← hasFDerivWithinAt_comp_smul_smul_iff, Pi.smul_apply]
  lift c to 𝕜ˣ using IsUnit.mk0 c hc
  exact (ContinuousLinearEquiv.smulLeft c).comp_hasFDerivWithinAt_iff.symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fderivWithin_comp_smul_eq_fderivWithin_smul` / 定理 `fderivWithin_comp_smul_eq_fderivWithin_smul`

English:
theorem fderivWithin_comp_smul_eq_fderivWithin_smul
  given: (c : 𝕜)
  proof: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · classical
    simp only [fderivWithin, DifferentiableWithinAt, hasFDerivWithinAt_comp_smul_iff_smul hc]

中文:
定理 fderivWithin_comp_smul_eq_fderivWithin_smul
  条件: (c : 𝕜)
  证明: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · classical
    simp only [fderivWithin, DifferentiableWithinAt, hasFDerivWithinAt_comp_smul_iff_smul hc]

Depends on / 依赖: DifferentiableWithinAt, classical, eq_or_ne, fderivWithin, hasFDerivWithinAt_comp_smul_iff_smul
-/
theorem fderivWithin_comp_smul_eq_fderivWithin_smul (c : 𝕜) :
    fderivWithin 𝕜 (f <| c • ·) s x = fderivWithin 𝕜 (c • f) (c • s) (c • x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · classical
    simp only [fderivWithin, DifferentiableWithinAt, hasFDerivWithinAt_comp_smul_iff_smul hc]

/--
theorem `fderivWithin_comp_smul` / 定理 `fderivWithin_comp_smul`

English:
theorem fderivWithin_comp_smul
  given: (c : 𝕜) (hs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [fderivWithin_comp_smul_eq_fderivWithin_smul, fderivWithin_const_smul_field]
    exact hs.smul hc

中文:
定理 fderivWithin_comp_smul
  条件: (c : 𝕜) (hs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [fderivWithin_comp_smul_eq_fderivWithin_smul, fderivWithin_const_smul_field]
    exact hs.smul hc

Depends on / 依赖: eq_or_ne, fderivWithin_comp_smul_eq_fderivWithin_smul, fderivWithin_const_smul_field, hs.smul
-/
theorem fderivWithin_comp_smul (c : 𝕜) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (f <| c • ·) s x = c • fderivWithin 𝕜 f (c • s) (c • x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [fderivWithin_comp_smul_eq_fderivWithin_smul, fderivWithin_const_smul_field]
    exact hs.smul hc

/--
theorem `fderiv_comp_smul` / 定理 `fderiv_comp_smul`

English:
theorem fderiv_comp_smul
  given: (c : 𝕜)
  statement: fderiv 𝕜 (f <| c • ·) x = c • fderiv 𝕜 f (c • x)
  proof: by
  rw [← fderivWithin_univ]; rw [fderivWithin_comp_smul _ uniqueDiffWithinAt_univ]
  rcases eq_or_ne c 0 with rfl | hc <;> simp [smul_set_univ₀, *]

中文:
定理 fderiv_comp_smul
  条件: (c : 𝕜)
  结论: fderiv 𝕜 (f <| c • ·) x = c • fderiv 𝕜 f (c • x)
  证明: by
  rw [← fderivWithin_univ]; rw [fderivWithin_comp_smul _ uniqueDiffWithinAt_univ]
  rcases eq_or_ne c 0 with rfl | hc <;> simp [smul_set_univ₀, *]

Depends on / 依赖: eq_or_ne, fderivWithin_comp_smul, fderivWithin_univ, uniqueDiffWithinAt_univ
-/
theorem fderiv_comp_smul (c : 𝕜) : fderiv 𝕜 (f <| c • ·) x = c • fderiv 𝕜 f (c • x) := by
  rw [← fderivWithin_univ]; rw [fderivWithin_comp_smul _ uniqueDiffWithinAt_univ]
  rcases eq_or_ne c 0 with rfl | hc <;> simp [smul_set_univ₀, *]

/--
theorem `fderivWithin_comp_neg` / 定理 `fderivWithin_comp_neg`

English:
theorem fderivWithin_comp_neg
  given: {f : 𝕜 -> F} {s : Set 𝕜} {x : 𝕜}
  proof: by
  have t1 := fderivWithin_comp_smul_eq_fderivWithin_smul (-1 : 𝕜) (f := f) (s := s) (x := x)
  simp only [neg_smul, one_smul, Set.neg_smul_set] at t1
  exact t1.trans fderivWithin_neg'

中文:
定理 fderivWithin_comp_neg
  条件: {f : 𝕜 -> F} {s : 集合 𝕜} {x : 𝕜}
  证明: by
  have t1 := fderivWithin_comp_smul_eq_fderivWithin_smul (-1 : 𝕜) (f := f) (s := s) (x := x)
  simp only [neg_smul, one_smul, Set.neg_smul_set] at t1
  exact t1.trans fderivWithin_neg'

Depends on / 依赖: Set.neg_smul_set, fderivWithin_comp_smul_eq_fderivWithin_smul, fderivWithin_neg, neg_smul, neg_smul_set, one_smul, t1.trans
-/
theorem fderivWithin_comp_neg {f : 𝕜 -> F} {s : Set 𝕜} {x : 𝕜} :
    fderivWithin 𝕜 (fun a => f (-a)) s x = -fderivWithin 𝕜 f (-s) (-x) := by
  have t1 := fderivWithin_comp_smul_eq_fderivWithin_smul (-1 : 𝕜) (f := f) (s := s) (x := x)
  simp only [neg_smul, one_smul, Set.neg_smul_set] at t1
  exact t1.trans fderivWithin_neg'

end SMulLeft
