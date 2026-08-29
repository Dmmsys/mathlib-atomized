/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Derivative of the Cartesian product of functions

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
Cartesian products of functions, and functions into Pi-types.
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
variable {f f₀ f₁ g : E -> F}
variable {f' f₀' f₁' g' : E ->L[𝕜] F}
variable (e : E ->L[𝕜] F)
variable {x : E}
variable {s t : Set E}
variable {L : Filter (E × E)}

section CartesianProduct

/-! ### Derivative of the Cartesian product of two functions -/


section Prod

variable {f₂ : E -> G} {f₂' : E ->L[𝕜] G}

/--
theorem `HasFDerivAtFilter.prodMk` / 定理 `HasFDerivAtFilter.prodMk`

English:
theorem HasFDerivAtFilter.prodMk
  statement: (hf₁ : HasFDerivAtFilter f₁ f₁' L)
  proof: .of_isLittleO hf₁.isLittleO.prod_left hf₂.isLittleO

中文:
定理 有FDerivAtFilter.prodMk
  结论: (hf₁ : 有FDerivAtFilter f₁ f₁' L)
  证明: .of_isLittleO hf₁.isLittleO.prod_left hf₂.isLittleO

Depends on / 依赖: isLittleO, isLittleO.prod_left, of_isLittleO, prod_left
-/
theorem HasFDerivAtFilter.prodMk (hf₁ : HasFDerivAtFilter f₁ f₁' L)
    (hf₂ : HasFDerivAtFilter f₂ f₂' L) :
    HasFDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') L :=
.of_isLittleO hf₁.isLittleO.prod_left hf₂.isLittleO

/--
theorem `HasStrictFDerivAt.prodMk` / 定理 `HasStrictFDerivAt.prodMk`

English:
theorem HasStrictFDerivAt.prodMk
  statement: (hf₁ : HasStrictFDerivAt f₁ f₁' x)
  proof: HasFDerivAtFilter.prodMk hf₁ hf₂

@[fun_prop]
nonrec theorem HasFDerivWithinAt.prodMk (hf₁ : HasFDerivWithinAt f₁ f₁' s x)
    (hf₂ : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') s x :=
  hf₁.prodMk hf₂

@[fun_prop]
nonrec theorem HasFDerivAt.prodMk (h

中文:
定理 HasStrictFDerivAt.prodMk
  结论: (hf₁ : HasStrictFDerivAt f₁ f₁' x)
  证明: HasFDerivAtFilter.prodMk hf₁ hf₂

@[fun_prop]
nonrec theorem HasFDerivWithinAt.prodMk (hf₁ : HasFDerivWithinAt f₁ f₁' s x)
    (hf₂ : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') s x :=
  hf₁.prodMk hf₂

@[fun_prop]
nonrec theorem HasFDerivAt.prodMk (h
-/
protected theorem HasStrictFDerivAt.prodMk (hf₁ : HasStrictFDerivAt f₁ f₁' x)
    (hf₂ : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
  HasFDerivAtFilter.prodMk hf₁ hf₂

@[fun_prop]
nonrec theorem HasFDerivWithinAt.prodMk (hf₁ : HasFDerivWithinAt f₁ f₁' s x)
    (hf₂ : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') s x :=
  hf₁.prodMk hf₂

@[fun_prop]
nonrec theorem HasFDerivAt.prodMk (hf₁ : HasFDerivAt f₁ f₁' x) (hf₂ : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
  hf₁.prodMk hf₂

@[fun_prop]
/--
theorem `hasFDerivAt_prodMk_left` / 定理 `hasFDerivAt_prodMk_left`

English:
theorem hasFDerivAt_prodMk_left
  given: (e₀ : E) (f₀ : F)
  proof: (hasFDerivAt_id e₀).prodMk (hasFDerivAt_const f₀ e₀)

@[fun_prop]

中文:
定理 hasFDerivAt_prodMk_left
  条件: (e₀ : E) (f₀ : F)
  证明: (hasFDerivAt_id e₀).prodMk (hasFDerivAt_const f₀ e₀)

@[fun_prop]

Depends on / 依赖: hasFDerivAt_const, hasFDerivAt_id, prodMk
-/
theorem hasFDerivAt_prodMk_left (e₀ : E) (f₀ : F) :
    HasFDerivAt (fun e : E => (e, f₀)) (inl 𝕜 E F) e₀ :=
  (hasFDerivAt_id e₀).prodMk (hasFDerivAt_const f₀ e₀)

@[fun_prop]
/--
theorem `hasFDerivAt_prodMk_right` / 定理 `hasFDerivAt_prodMk_right`

English:
theorem hasFDerivAt_prodMk_right
  given: (e₀ : E) (f₀ : F)
  proof: (hasFDerivAt_const e₀ f₀).prodMk (hasFDerivAt_id f₀)

@[fun_prop]

中文:
定理 hasFDerivAt_prodMk_right
  条件: (e₀ : E) (f₀ : F)
  证明: (hasFDerivAt_const e₀ f₀).prodMk (hasFDerivAt_id f₀)

@[fun_prop]

Depends on / 依赖: hasFDerivAt_const, hasFDerivAt_id, prodMk
-/
theorem hasFDerivAt_prodMk_right (e₀ : E) (f₀ : F) :
    HasFDerivAt (fun f : F => (e₀, f)) (inr 𝕜 E F) f₀ :=
  (hasFDerivAt_const e₀ f₀).prodMk (hasFDerivAt_id f₀)

@[fun_prop]
/--
theorem `DifferentiableWithinAt.prodMk` / 定理 `DifferentiableWithinAt.prodMk`

English:
theorem DifferentiableWithinAt.prodMk
  statement: (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
  proof: (hf₁.hasFDerivWithinAt.prodMk hf₂.hasFDerivWithinAt).differentiableWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.prodMk
  结论: (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
  证明: (hf₁.hasFDerivWithinAt.prodMk hf₂.hasFDerivWithinAt).differentiableWithinAt

@[simp, fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hasFDerivWithinAt.prodMk, prodMk
-/
theorem DifferentiableWithinAt.prodMk (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x : E => (f₁ x, f₂ x)) s x :=
  (hf₁.hasFDerivWithinAt.prodMk hf₂.hasFDerivWithinAt).differentiableWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.prodMk` / 定理 `DifferentiableAt.prodMk`

English:
theorem DifferentiableAt.prodMk
  given: (hf₁ : DifferentiableAt 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x)
  proof: (hf₁.hasFDerivAt.prodMk hf₂.hasFDerivAt).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.prodMk
  条件: (hf₁ : DifferentiableAt 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x)
  证明: (hf₁.hasFDerivAt.prodMk hf₂.hasFDerivAt).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt, hasFDerivAt.prodMk, prodMk
-/
theorem DifferentiableAt.prodMk (hf₁ : DifferentiableAt 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x : E => (f₁ x, f₂ x)) x :=
  (hf₁.hasFDerivAt.prodMk hf₂.hasFDerivAt).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableOn.prodMk` / 定理 `DifferentiableOn.prodMk`

English:
theorem DifferentiableOn.prodMk
  given: (hf₁ : DifferentiableOn 𝕜 f₁ s) (hf₂ : DifferentiableOn 𝕜 f₂ s)
  proof: fun x hx => (hf₁ x hx).prodMk (hf₂ x hx)

@[simp, fun_prop]

中文:
定理 DifferentiableOn.prodMk
  条件: (hf₁ : DifferentiableOn 𝕜 f₁ s) (hf₂ : DifferentiableOn 𝕜 f₂ s)
  证明: fun x hx => (hf₁ x hx).prodMk (hf₂ x hx)

@[simp, fun_prop]

Depends on / 依赖: prodMk
-/
theorem DifferentiableOn.prodMk (hf₁ : DifferentiableOn 𝕜 f₁ s) (hf₂ : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x : E => (f₁ x, f₂ x)) s := fun x hx => (hf₁ x hx).prodMk (hf₂ x hx)

@[simp, fun_prop]
/--
theorem `Differentiable.prodMk` / 定理 `Differentiable.prodMk`

English:
theorem Differentiable.prodMk
  given: (hf₁ : Differentiable 𝕜 f₁) (hf₂ : Differentiable 𝕜 f₂)
  proof: fun x =>
  (hf₁ x).prodMk (hf₂ x)

中文:
定理 可微.prodMk
  条件: (hf₁ : 可微 𝕜 f₁) (hf₂ : 可微 𝕜 f₂)
  证明: fun x =>
  (hf₁ x).prodMk (hf₂ x)
-/
theorem Differentiable.prodMk (hf₁ : Differentiable 𝕜 f₁) (hf₂ : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x : E => (f₁ x, f₂ x) := fun x =>
  (hf₁ x).prodMk (hf₂ x)

/--
theorem `DifferentiableAt.fderiv_prodMk` / 定理 `DifferentiableAt.fderiv_prodMk`

English:
theorem DifferentiableAt.fderiv_prodMk
  statement: (hf₁ : DifferentiableAt 𝕜 f₁ x)
  proof: (hf₁.hasFDerivAt.prodMk hf₂.hasFDerivAt).fderiv

中文:
定理 DifferentiableAt.fderiv_prodMk
  结论: (hf₁ : DifferentiableAt 𝕜 f₁ x)
  证明: (hf₁.hasFDerivAt.prodMk hf₂.hasFDerivAt).fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hasFDerivAt.prodMk, prodMk
-/
theorem DifferentiableAt.fderiv_prodMk (hf₁ : DifferentiableAt 𝕜 f₁ x)
    (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x : E => (f₁ x, f₂ x)) x = (fderiv 𝕜 f₁ x).prod (fderiv 𝕜 f₂ x) :=
  (hf₁.hasFDerivAt.prodMk hf₂.hasFDerivAt).fderiv

/--
theorem `DifferentiableWithinAt.fderivWithin_prodMk` / 定理 `DifferentiableWithinAt.fderivWithin_prodMk`

English:
theorem DifferentiableWithinAt.fderivWithin_prodMk
  statement: (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
  proof: (hf₁.hasFDerivWithinAt.prodMk hf₂.hasFDerivWithinAt).fderivWithin hxs

中文:
定理 DifferentiableWithinAt.fderivWithin_prodMk
  结论: (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
  证明: (hf₁.hasFDerivWithinAt.prodMk hf₂.hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hasFDerivWithinAt.prodMk, prodMk
-/
theorem DifferentiableWithinAt.fderivWithin_prodMk (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : E => (f₁ x, f₂ x)) s x =
      (fderivWithin 𝕜 f₁ s x).prod (fderivWithin 𝕜 f₂ s x) :=
  (hf₁.hasFDerivWithinAt.prodMk hf₂.hasFDerivWithinAt).fderivWithin hxs

end Prod

section Fst

variable {f₂ : E -> F × G} {f₂' : E ->L[𝕜] F × G} {p : E × F}

/--
theorem `hasFDerivAtFilter_fst` / 定理 `hasFDerivAtFilter_fst`

English:
theorem hasFDerivAtFilter_fst
  given: {L : Filter ((E × F) × (E × F))}
  proof: (fst 𝕜 E F).hasFDerivAtFilter

@[fun_prop]

中文:
定理 hasFDerivAtFilter_fst
  条件: {L : 滤子 ((E × F) × (E × F))}
  证明: (fst 𝕜 E F).hasFDerivAtFilter

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter
-/
theorem hasFDerivAtFilter_fst {L : Filter ((E × F) × (E × F))} :
    HasFDerivAtFilter Prod.fst (fst 𝕜 E F) L :=
  (fst 𝕜 E F).hasFDerivAtFilter

@[fun_prop]
/--
theorem `hasStrictFDerivAt_fst` / 定理 `hasStrictFDerivAt_fst`

English:
theorem hasStrictFDerivAt_fst
  statement: HasStrictFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p
  proof: hasFDerivAtFilter_fst

@[fun_prop]

中文:
定理 hasStrictFDerivAt_fst
  结论: HasStrictFDerivAt (@积类型.fst E F) (fst 𝕜 E F) p
  证明: hasFDerivAtFilter_fst

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_fst
-/
theorem hasStrictFDerivAt_fst : HasStrictFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  hasFDerivAtFilter_fst

@[fun_prop]
/--
theorem `HasStrictFDerivAt.fst` / 定理 `HasStrictFDerivAt.fst`

English:
theorem HasStrictFDerivAt.fst
  given: (h : HasStrictFDerivAt f₂ f₂' x)
  proof: hasStrictFDerivAt_fst.comp x h

中文:
定理 HasStrictFDerivAt.fst
  条件: (h : HasStrictFDerivAt f₂ f₂' x)
  证明: hasStrictFDerivAt_fst.comp x h
-/
protected theorem HasStrictFDerivAt.fst (h : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  hasStrictFDerivAt_fst.comp x h

/--
theorem `HasFDerivAtFilter.fst` / 定理 `HasFDerivAtFilter.fst`

English:
theorem HasFDerivAtFilter.fst
  given: (h : HasFDerivAtFilter f₂ f₂' L)
  proof: hasFDerivAtFilter_fst.comp h tendsto_map

@[fun_prop]

中文:
定理 有FDerivAtFilter.fst
  条件: (h : 有FDerivAtFilter f₂ f₂' L)
  证明: hasFDerivAtFilter_fst.comp h tendsto_map

@[fun_prop]
-/
protected theorem HasFDerivAtFilter.fst (h : HasFDerivAtFilter f₂ f₂' L) :
    HasFDerivAtFilter (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') L :=
  hasFDerivAtFilter_fst.comp h tendsto_map

@[fun_prop]
/--
theorem `hasFDerivAt_fst` / 定理 `hasFDerivAt_fst`

English:
theorem hasFDerivAt_fst
  statement: HasFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p
  proof: hasFDerivAtFilter_fst

@[fun_prop]
protected nonrec theorem HasFDerivAt.fst (h : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  h.fst

@[fun_prop]

中文:
定理 hasFDerivAt_fst
  结论: 在点处Fréchet可导 (@积类型.fst E F) (fst 𝕜 E F) p
  证明: hasFDerivAtFilter_fst

@[fun_prop]
protected nonrec theorem HasFDerivAt.fst (h : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  h.fst

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_fst
-/
theorem hasFDerivAt_fst : HasFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  hasFDerivAtFilter_fst

@[fun_prop]
protected nonrec theorem HasFDerivAt.fst (h : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  h.fst

@[fun_prop]
/--
theorem `hasFDerivWithinAt_fst` / 定理 `hasFDerivWithinAt_fst`

English:
theorem hasFDerivWithinAt_fst
  given: {s : Set (E × F)}
  proof: hasFDerivAtFilter_fst

@[fun_prop]
protected nonrec theorem HasFDerivWithinAt.fst (h : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') s x :=
  h.fst

@[fun_prop]

中文:
定理 hasFDerivWithinAt_fst
  条件: {s : 集合 (E × F)}
  证明: hasFDerivAtFilter_fst

@[fun_prop]
protected nonrec theorem HasFDerivWithinAt.fst (h : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') s x :=
  h.fst

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_fst
-/
theorem hasFDerivWithinAt_fst {s : Set (E × F)} :
    HasFDerivWithinAt (@Prod.fst E F) (fst 𝕜 E F) s p :=
  hasFDerivAtFilter_fst

@[fun_prop]
protected nonrec theorem HasFDerivWithinAt.fst (h : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') s x :=
  h.fst

@[fun_prop]
/--
theorem `differentiableAt_fst` / 定理 `differentiableAt_fst`

English:
theorem differentiableAt_fst
  statement: DifferentiableAt 𝕜 Prod.fst p
  proof: hasFDerivAt_fst.differentiableAt

@[simp, fun_prop]

中文:
定理 differentiableAt_fst
  结论: DifferentiableAt 𝕜 积类型.fst p
  证明: hasFDerivAt_fst.differentiableAt

@[simp, fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt_fst, hasFDerivAt_fst.differentiableAt
-/
theorem differentiableAt_fst : DifferentiableAt 𝕜 Prod.fst p :=
  hasFDerivAt_fst.differentiableAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.fst` / 定理 `DifferentiableAt.fst`

English:
theorem DifferentiableAt.fst
  given: (h : DifferentiableAt 𝕜 f₂ x)
  proof: differentiableAt_fst.comp x h

@[fun_prop]

中文:
定理 DifferentiableAt.fst
  条件: (h : DifferentiableAt 𝕜 f₂ x)
  证明: differentiableAt_fst.comp x h

@[fun_prop]
-/
protected theorem DifferentiableAt.fst (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).1) x :=
  differentiableAt_fst.comp x h

@[fun_prop]
/--
theorem `differentiable_fst` / 定理 `differentiable_fst`

English:
theorem differentiable_fst
  statement: Differentiable 𝕜 (Prod.fst : E × F -> E)
  proof: fun _ =>
  differentiableAt_fst

@[simp, fun_prop]

中文:
定理 differentiable_fst
  结论: 可微 𝕜 (积类型.fst : E × F -> E)
  证明: fun _ =>
  differentiableAt_fst

@[simp, fun_prop]
-/
theorem differentiable_fst : Differentiable 𝕜 (Prod.fst : E × F -> E) := fun _ =>
  differentiableAt_fst

@[simp, fun_prop]
/--
theorem `Differentiable.fst` / 定理 `Differentiable.fst`

English:
theorem Differentiable.fst
  given: (h : Differentiable 𝕜 f₂)
  proof: differentiable_fst.comp h

@[fun_prop]

中文:
定理 可微.fst
  条件: (h : 可微 𝕜 f₂)
  证明: differentiable_fst.comp h

@[fun_prop]
-/
protected theorem Differentiable.fst (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).1 :=
  differentiable_fst.comp h

@[fun_prop]
/--
theorem `differentiableWithinAt_fst` / 定理 `differentiableWithinAt_fst`

English:
theorem differentiableWithinAt_fst
  given: {s : Set (E × F)}
  statement: DifferentiableWithinAt 𝕜 Prod.fst s p
  proof: differentiableAt_fst.differentiableWithinAt

@[fun_prop]

中文:
定理 differentiableWithinAt_fst
  条件: {s : 集合 (E × F)}
  结论: DifferentiableWithinAt 𝕜 积类型.fst s p
  证明: differentiableAt_fst.differentiableWithinAt

@[fun_prop]

Depends on / 依赖: differentiableAt_fst, differentiableAt_fst.differentiableWithinAt, differentiableWithinAt
-/
theorem differentiableWithinAt_fst {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.fst s p :=
  differentiableAt_fst.differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableWithinAt.fst` / 定理 `DifferentiableWithinAt.fst`

English:
theorem DifferentiableWithinAt.fst
  given: (h : DifferentiableWithinAt 𝕜 f₂ s x)
  proof: differentiableAt_fst.comp_differentiableWithinAt x h

@[fun_prop]

中文:
定理 DifferentiableWithinAt.fst
  条件: (h : DifferentiableWithinAt 𝕜 f₂ s x)
  证明: differentiableAt_fst.comp_differentiableWithinAt x h

@[fun_prop]
-/
protected theorem DifferentiableWithinAt.fst (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).1) s x :=
  differentiableAt_fst.comp_differentiableWithinAt x h

@[fun_prop]
/--
theorem `differentiableOn_fst` / 定理 `differentiableOn_fst`

English:
theorem differentiableOn_fst
  given: {s : Set (E × F)}
  statement: DifferentiableOn 𝕜 Prod.fst s
  proof: differentiable_fst.differentiableOn

@[fun_prop]

中文:
定理 differentiableOn_fst
  条件: {s : 集合 (E × F)}
  结论: DifferentiableOn 𝕜 积类型.fst s
  证明: differentiable_fst.differentiableOn

@[fun_prop]

Depends on / 依赖: differentiableOn, differentiable_fst, differentiable_fst.differentiableOn
-/
theorem differentiableOn_fst {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.fst s :=
  differentiable_fst.differentiableOn

@[fun_prop]
/--
theorem `DifferentiableOn.fst` / 定理 `DifferentiableOn.fst`

English:
theorem DifferentiableOn.fst
  given: (h : DifferentiableOn 𝕜 f₂ s)
  proof: differentiable_fst.comp_differentiableOn h

中文:
定理 DifferentiableOn.fst
  条件: (h : DifferentiableOn 𝕜 f₂ s)
  证明: differentiable_fst.comp_differentiableOn h
-/
protected theorem DifferentiableOn.fst (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).1) s :=
  differentiable_fst.comp_differentiableOn h

/--
theorem `fderiv_fst` / 定理 `fderiv_fst`

English:
theorem fderiv_fst
  statement: fderiv 𝕜 Prod.fst p = fst 𝕜 E F
  proof: hasFDerivAt_fst.fderiv

中文:
定理 fderiv_fst
  结论: fderiv 𝕜 积类型.fst p = fst 𝕜 E F
  证明: hasFDerivAt_fst.fderiv

Depends on / 依赖: fderiv, hasFDerivAt_fst, hasFDerivAt_fst.fderiv
-/
theorem fderiv_fst : fderiv 𝕜 Prod.fst p = fst 𝕜 E F :=
  hasFDerivAt_fst.fderiv

/--
theorem `fderiv.fst` / 定理 `fderiv.fst`

English:
theorem fderiv.fst
  given: (h : DifferentiableAt 𝕜 f₂ x)
  proof: h.hasFDerivAt.fst.fderiv

中文:
定理 fderiv.fst
  条件: (h : DifferentiableAt 𝕜 f₂ x)
  证明: h.hasFDerivAt.fst.fderiv

Depends on / 依赖: fderiv, h.hasFDerivAt.fst.fderiv, hasFDerivAt
-/
theorem fderiv.fst (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).1) x = (fst 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.hasFDerivAt.fst.fderiv

/--
theorem `fderivWithin_fst` / 定理 `fderivWithin_fst`

English:
theorem fderivWithin_fst
  given: {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p)
  proof: hasFDerivWithinAt_fst.fderivWithin hs

中文:
定理 fderivWithin_fst
  条件: {s : 集合 (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p)
  证明: hasFDerivWithinAt_fst.fderivWithin hs

Depends on / 依赖: fderivWithin, hasFDerivWithinAt_fst, hasFDerivWithinAt_fst.fderivWithin
-/
theorem fderivWithin_fst {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.fst s p = fst 𝕜 E F :=
  hasFDerivWithinAt_fst.fderivWithin hs

/--
theorem `fderivWithin.fst` / 定理 `fderivWithin.fst`

English:
theorem fderivWithin.fst
  given: (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x)
  proof: h.hasFDerivWithinAt.fst.fderivWithin hs

中文:
定理 fderivWithin.fst
  条件: (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x)
  证明: h.hasFDerivWithinAt.fst.fderivWithin hs

Depends on / 依赖: fderivWithin, h.hasFDerivWithinAt.fst.fderivWithin, hasFDerivWithinAt
-/
theorem fderivWithin.fst (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).1) s x = (fst 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.hasFDerivWithinAt.fst.fderivWithin hs

end Fst

section Snd

variable {f₂ : E -> F × G} {f₂' : E ->L[𝕜] F × G} {p : E × F}

/--
theorem `hasFDerivAtFilter_snd` / 定理 `hasFDerivAtFilter_snd`

English:
theorem hasFDerivAtFilter_snd
  given: {L : Filter ((E × F) × (E × F))}
  proof: (snd 𝕜 E F).hasFDerivAtFilter

中文:
定理 hasFDerivAtFilter_snd
  条件: {L : 滤子 ((E × F) × (E × F))}
  证明: (snd 𝕜 E F).hasFDerivAtFilter

Depends on / 依赖: hasFDerivAtFilter
-/
theorem hasFDerivAtFilter_snd {L : Filter ((E × F) × (E × F))} :
    HasFDerivAtFilter (@Prod.snd E F) (snd 𝕜 E F) L :=
  (snd 𝕜 E F).hasFDerivAtFilter

/--
theorem `HasFDerivAtFilter.snd` / 定理 `HasFDerivAtFilter.snd`

English:
theorem HasFDerivAtFilter.snd
  given: (h : HasFDerivAtFilter f₂ f₂' L)
  proof: hasFDerivAtFilter_snd.comp h tendsto_map

@[fun_prop]

中文:
定理 有FDerivAtFilter.snd
  条件: (h : 有FDerivAtFilter f₂ f₂' L)
  证明: hasFDerivAtFilter_snd.comp h tendsto_map

@[fun_prop]
-/
protected theorem HasFDerivAtFilter.snd (h : HasFDerivAtFilter f₂ f₂' L) :
    HasFDerivAtFilter (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') L :=
  hasFDerivAtFilter_snd.comp h tendsto_map

@[fun_prop]
/--
theorem `hasStrictFDerivAt_snd` / 定理 `hasStrictFDerivAt_snd`

English:
theorem hasStrictFDerivAt_snd
  statement: HasStrictFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p
  proof: hasFDerivAtFilter_snd

@[fun_prop]

中文:
定理 hasStrictFDerivAt_snd
  结论: HasStrictFDerivAt (@积类型.snd E F) (snd 𝕜 E F) p
  证明: hasFDerivAtFilter_snd

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_snd
-/
theorem hasStrictFDerivAt_snd : HasStrictFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  hasFDerivAtFilter_snd

@[fun_prop]
/--
theorem `HasStrictFDerivAt.snd` / 定理 `HasStrictFDerivAt.snd`

English:
theorem HasStrictFDerivAt.snd
  given: (h : HasStrictFDerivAt f₂ f₂' x)
  proof: HasFDerivAtFilter.snd h

@[fun_prop]

中文:
定理 HasStrictFDerivAt.snd
  条件: (h : HasStrictFDerivAt f₂ f₂' x)
  证明: HasFDerivAtFilter.snd h

@[fun_prop]
-/
protected theorem HasStrictFDerivAt.snd (h : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  HasFDerivAtFilter.snd h

@[fun_prop]
/--
theorem `hasFDerivAt_snd` / 定理 `hasFDerivAt_snd`

English:
theorem hasFDerivAt_snd
  statement: HasFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p
  proof: hasFDerivAtFilter_snd

@[fun_prop]

中文:
定理 hasFDerivAt_snd
  结论: 在点处Fréchet可导 (@积类型.snd E F) (snd 𝕜 E F) p
  证明: hasFDerivAtFilter_snd

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_snd
-/
theorem hasFDerivAt_snd : HasFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  hasFDerivAtFilter_snd

@[fun_prop]
/--
theorem `HasFDerivAt.snd` / 定理 `HasFDerivAt.snd`

English:
theorem HasFDerivAt.snd
  given: (h : HasFDerivAt f₂ f₂' x)
  proof: HasFDerivAtFilter.snd h

@[fun_prop]

中文:
定理 在点处Fréchet可导.snd
  条件: (h : 在点处Fréchet可导 f₂ f₂' x)
  证明: HasFDerivAtFilter.snd h

@[fun_prop]
-/
protected theorem HasFDerivAt.snd (h : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  HasFDerivAtFilter.snd h

@[fun_prop]
/--
theorem `hasFDerivWithinAt_snd` / 定理 `hasFDerivWithinAt_snd`

English:
theorem hasFDerivWithinAt_snd
  given: {s : Set (E × F)}
  proof: hasFDerivAtFilter_snd

@[fun_prop]

中文:
定理 hasFDerivWithinAt_snd
  条件: {s : 集合 (E × F)}
  证明: hasFDerivAtFilter_snd

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_snd
-/
theorem hasFDerivWithinAt_snd {s : Set (E × F)} :
    HasFDerivWithinAt (@Prod.snd E F) (snd 𝕜 E F) s p :=
  hasFDerivAtFilter_snd

@[fun_prop]
/--
theorem `HasFDerivWithinAt.snd` / 定理 `HasFDerivWithinAt.snd`

English:
theorem HasFDerivWithinAt.snd
  given: (h : HasFDerivWithinAt f₂ f₂' s x)
  proof: HasFDerivAtFilter.snd h

@[fun_prop]

中文:
定理 HasFDerivWithinAt.snd
  条件: (h : HasFDerivWithinAt f₂ f₂' s x)
  证明: HasFDerivAtFilter.snd h

@[fun_prop]
-/
protected theorem HasFDerivWithinAt.snd (h : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') s x :=
  HasFDerivAtFilter.snd h

@[fun_prop]
/--
theorem `differentiableAt_snd` / 定理 `differentiableAt_snd`

English:
theorem differentiableAt_snd
  statement: DifferentiableAt 𝕜 Prod.snd p
  proof: hasFDerivAt_snd.differentiableAt

@[simp, fun_prop]

中文:
定理 differentiableAt_snd
  结论: DifferentiableAt 𝕜 积类型.snd p
  证明: hasFDerivAt_snd.differentiableAt

@[simp, fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt_snd, hasFDerivAt_snd.differentiableAt
-/
theorem differentiableAt_snd : DifferentiableAt 𝕜 Prod.snd p :=
  hasFDerivAt_snd.differentiableAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.snd` / 定理 `DifferentiableAt.snd`

English:
theorem DifferentiableAt.snd
  given: (h : DifferentiableAt 𝕜 f₂ x)
  proof: differentiableAt_snd.comp x h

@[fun_prop]

中文:
定理 DifferentiableAt.snd
  条件: (h : DifferentiableAt 𝕜 f₂ x)
  证明: differentiableAt_snd.comp x h

@[fun_prop]
-/
protected theorem DifferentiableAt.snd (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).2) x :=
  differentiableAt_snd.comp x h

@[fun_prop]
/--
theorem `differentiable_snd` / 定理 `differentiable_snd`

English:
theorem differentiable_snd
  statement: Differentiable 𝕜 (Prod.snd : E × F -> F)
  proof: fun _ =>
  differentiableAt_snd

@[simp, fun_prop]

中文:
定理 differentiable_snd
  结论: 可微 𝕜 (积类型.snd : E × F -> F)
  证明: fun _ =>
  differentiableAt_snd

@[simp, fun_prop]
-/
theorem differentiable_snd : Differentiable 𝕜 (Prod.snd : E × F -> F) := fun _ =>
  differentiableAt_snd

@[simp, fun_prop]
/--
theorem `Differentiable.snd` / 定理 `Differentiable.snd`

English:
theorem Differentiable.snd
  given: (h : Differentiable 𝕜 f₂)
  proof: differentiable_snd.comp h

@[fun_prop]

中文:
定理 可微.snd
  条件: (h : 可微 𝕜 f₂)
  证明: differentiable_snd.comp h

@[fun_prop]
-/
protected theorem Differentiable.snd (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).2 :=
  differentiable_snd.comp h

@[fun_prop]
/--
theorem `differentiableWithinAt_snd` / 定理 `differentiableWithinAt_snd`

English:
theorem differentiableWithinAt_snd
  given: {s : Set (E × F)}
  statement: DifferentiableWithinAt 𝕜 Prod.snd s p
  proof: differentiableAt_snd.differentiableWithinAt

@[fun_prop]

中文:
定理 differentiableWithinAt_snd
  条件: {s : 集合 (E × F)}
  结论: DifferentiableWithinAt 𝕜 积类型.snd s p
  证明: differentiableAt_snd.differentiableWithinAt

@[fun_prop]

Depends on / 依赖: differentiableAt_snd, differentiableAt_snd.differentiableWithinAt, differentiableWithinAt
-/
theorem differentiableWithinAt_snd {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.snd s p :=
  differentiableAt_snd.differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableWithinAt.snd` / 定理 `DifferentiableWithinAt.snd`

English:
theorem DifferentiableWithinAt.snd
  given: (h : DifferentiableWithinAt 𝕜 f₂ s x)
  proof: differentiableAt_snd.comp_differentiableWithinAt x h

@[fun_prop]

中文:
定理 DifferentiableWithinAt.snd
  条件: (h : DifferentiableWithinAt 𝕜 f₂ s x)
  证明: differentiableAt_snd.comp_differentiableWithinAt x h

@[fun_prop]
-/
protected theorem DifferentiableWithinAt.snd (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).2) s x :=
  differentiableAt_snd.comp_differentiableWithinAt x h

@[fun_prop]
/--
theorem `differentiableOn_snd` / 定理 `differentiableOn_snd`

English:
theorem differentiableOn_snd
  given: {s : Set (E × F)}
  statement: DifferentiableOn 𝕜 Prod.snd s
  proof: differentiable_snd.differentiableOn

@[fun_prop]

中文:
定理 differentiableOn_snd
  条件: {s : 集合 (E × F)}
  结论: DifferentiableOn 𝕜 积类型.snd s
  证明: differentiable_snd.differentiableOn

@[fun_prop]

Depends on / 依赖: differentiableOn, differentiable_snd, differentiable_snd.differentiableOn
-/
theorem differentiableOn_snd {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.snd s :=
  differentiable_snd.differentiableOn

@[fun_prop]
/--
theorem `DifferentiableOn.snd` / 定理 `DifferentiableOn.snd`

English:
theorem DifferentiableOn.snd
  given: (h : DifferentiableOn 𝕜 f₂ s)
  proof: differentiable_snd.comp_differentiableOn h

中文:
定理 DifferentiableOn.snd
  条件: (h : DifferentiableOn 𝕜 f₂ s)
  证明: differentiable_snd.comp_differentiableOn h
-/
protected theorem DifferentiableOn.snd (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).2) s :=
  differentiable_snd.comp_differentiableOn h

/--
theorem `fderiv_snd` / 定理 `fderiv_snd`

English:
theorem fderiv_snd
  statement: fderiv 𝕜 Prod.snd p = snd 𝕜 E F
  proof: hasFDerivAt_snd.fderiv

中文:
定理 fderiv_snd
  结论: fderiv 𝕜 积类型.snd p = snd 𝕜 E F
  证明: hasFDerivAt_snd.fderiv

Depends on / 依赖: fderiv, hasFDerivAt_snd, hasFDerivAt_snd.fderiv
-/
theorem fderiv_snd : fderiv 𝕜 Prod.snd p = snd 𝕜 E F :=
  hasFDerivAt_snd.fderiv

/--
theorem `fderiv.snd` / 定理 `fderiv.snd`

English:
theorem fderiv.snd
  given: (h : DifferentiableAt 𝕜 f₂ x)
  proof: h.hasFDerivAt.snd.fderiv

中文:
定理 fderiv.snd
  条件: (h : DifferentiableAt 𝕜 f₂ x)
  证明: h.hasFDerivAt.snd.fderiv

Depends on / 依赖: fderiv, h.hasFDerivAt.snd.fderiv, hasFDerivAt
-/
theorem fderiv.snd (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).2) x = (snd 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.hasFDerivAt.snd.fderiv

/--
theorem `fderivWithin_snd` / 定理 `fderivWithin_snd`

English:
theorem fderivWithin_snd
  given: {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p)
  proof: hasFDerivWithinAt_snd.fderivWithin hs

中文:
定理 fderivWithin_snd
  条件: {s : 集合 (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p)
  证明: hasFDerivWithinAt_snd.fderivWithin hs

Depends on / 依赖: fderivWithin, hasFDerivWithinAt_snd, hasFDerivWithinAt_snd.fderivWithin
-/
theorem fderivWithin_snd {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.snd s p = snd 𝕜 E F :=
  hasFDerivWithinAt_snd.fderivWithin hs

/--
theorem `fderivWithin.snd` / 定理 `fderivWithin.snd`

English:
theorem fderivWithin.snd
  given: (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x)
  proof: h.hasFDerivWithinAt.snd.fderivWithin hs

中文:
定理 fderivWithin.snd
  条件: (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x)
  证明: h.hasFDerivWithinAt.snd.fderivWithin hs

Depends on / 依赖: fderivWithin, h.hasFDerivWithinAt.snd.fderivWithin, hasFDerivWithinAt
-/
theorem fderivWithin.snd (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).2) s x = (snd 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.hasFDerivWithinAt.snd.fderivWithin hs

end Snd

section prodMap

variable {f₂ : G -> G'} {f₂' : G ->L[𝕜] G'} {y : G} (p : E × G)

@[fun_prop]
/--
theorem `HasStrictFDerivAt.prodMap` / 定理 `HasStrictFDerivAt.prodMap`

English:
theorem HasStrictFDerivAt.prodMap
  statement: (hf : HasStrictFDerivAt f f' p.1)
  proof: (hf.comp p hasStrictFDerivAt_fst).prodMk (hf₂.comp p hasStrictFDerivAt_snd)

@[fun_prop]

中文:
定理 HasStrictFDerivAt.prodMap
  结论: (hf : HasStrictFDerivAt f f' p.1)
  证明: (hf.comp p hasStrictFDerivAt_fst).prodMk (hf₂.comp p hasStrictFDerivAt_snd)

@[fun_prop]
-/
protected theorem HasStrictFDerivAt.prodMap (hf : HasStrictFDerivAt f f' p.1)
    (hf₂ : HasStrictFDerivAt f₂ f₂' p.2) : HasStrictFDerivAt (Prod.map f f₂) (f'.prodMap f₂') p :=
  (hf.comp p hasStrictFDerivAt_fst).prodMk (hf₂.comp p hasStrictFDerivAt_snd)

@[fun_prop]
/--
theorem `HasFDerivWithinAt.prodMap` / 定理 `HasFDerivWithinAt.prodMap`

English:
theorem HasFDerivWithinAt.prodMap
  statement: {s : Set <| E × G}
  proof: (hf.comp _ hasFDerivWithinAt_fst mapsTo_fst_prod).prodMk
.mono (by grind) (hf₂.comp _ hasFDerivWithinAt_snd mapsTo_snd_prod)

@[fun_prop]

中文:
定理 HasFDerivWithinAt.prodMap
  结论: {s : 集合 <| E × G}
  证明: (hf.comp _ hasFDerivWithinAt_fst mapsTo_fst_prod).prodMk
.mono (by grind) (hf₂.comp _ hasFDerivWithinAt_snd mapsTo_snd_prod)

@[fun_prop]
-/
protected theorem HasFDerivWithinAt.prodMap {s : Set <| E × G}
    (hf : HasFDerivWithinAt f f' (Prod.fst '' s) p.1)
    (hf₂ : HasFDerivWithinAt f₂ f₂' (Prod.snd '' s) p.2) :
    HasFDerivWithinAt (Prod.map f f₂) (f'.prodMap f₂') s p :=
  (hf.comp _ hasFDerivWithinAt_fst mapsTo_fst_prod).prodMk
.mono (by grind) (hf₂.comp _ hasFDerivWithinAt_snd mapsTo_snd_prod)

@[fun_prop]
/--
theorem `HasFDerivAt.prodMap` / 定理 `HasFDerivAt.prodMap`

English:
theorem HasFDerivAt.prodMap
  given: (hf : HasFDerivAt f f' p.1) (hf₂ : HasFDerivAt f₂ f₂' p.2)
  proof: (hf.comp p hasFDerivAt_fst).prodMk (hf₂.comp p hasFDerivAt_snd)

@[simp, fun_prop]

中文:
定理 在点处Fréchet可导.prodMap
  条件: (hf : 在点处Fréchet可导 f f' p.1) (hf₂ : 在点处Fréchet可导 f₂ f₂' p.2)
  证明: (hf.comp p hasFDerivAt_fst).prodMk (hf₂.comp p hasFDerivAt_snd)

@[simp, fun_prop]
-/
protected theorem HasFDerivAt.prodMap (hf : HasFDerivAt f f' p.1) (hf₂ : HasFDerivAt f₂ f₂' p.2) :
    HasFDerivAt (Prod.map f f₂) (f'.prodMap f₂') p :=
  (hf.comp p hasFDerivAt_fst).prodMk (hf₂.comp p hasFDerivAt_snd)

@[simp, fun_prop]
/--
theorem `DifferentiableAt.prodMap` / 定理 `DifferentiableAt.prodMap`

English:
theorem DifferentiableAt.prodMap
  statement: (hf : DifferentiableAt 𝕜 f p.1)
  proof: (hf.comp p differentiableAt_fst).prodMk (hf₂.comp p differentiableAt_snd)

中文:
定理 DifferentiableAt.prodMap
  结论: (hf : DifferentiableAt 𝕜 f p.1)
  证明: (hf.comp p differentiableAt_fst).prodMk (hf₂.comp p differentiableAt_snd)
-/
protected theorem DifferentiableAt.prodMap (hf : DifferentiableAt 𝕜 f p.1)
    (hf₂ : DifferentiableAt 𝕜 f₂ p.2) : DifferentiableAt 𝕜 (fun p : E × G => (f p.1, f₂ p.2)) p :=
  (hf.comp p differentiableAt_fst).prodMk (hf₂.comp p differentiableAt_snd)

end prodMap

section Pi

/-!
### Derivatives of functions `f : E → Π i, F' i`

In this section we formulate `has*FDeriv*_pi` theorems as `iff`s, and provide two versions of each
theorem:

* the version without `'` deals with `φ : Π i, E → F' i` and `φ' : Π i, E →L[𝕜] F' i`
  and is designed to deduce differentiability of `fun x i ↦ φ i x` from differentiability
  of each `φ i`;
* the version with `'` deals with `Φ : E → Π i, F' i` and `Φ' : E →L[𝕜] Π i, F' i`
  and is designed to deduce differentiability of the components `fun x ↦ Φ x i` from
  differentiability of `Φ`.
-/


variable {ι : Type*} {F' : ι -> Type*} [forall i, NormedAddCommGroup (F' i)]
  [forall i, NormedSpace 𝕜 (F' i)] {φ : forall i, E -> F' i} {φ' : forall i, E ->L[𝕜] F' i} {Φ : E -> forall i, F' i}
  {Φ' : E ->L[𝕜] forall i, F' i}

@[simp]
/--
theorem `hasFDerivAtFilter_pi'` / 定理 `hasFDerivAtFilter_pi'`

English:
theorem hasFDerivAtFilter_pi'
  proof: by
  simp [hasFDerivAtFilter_iff_isLittleOTVS, isLittleOTVS_pi]

@[simp]

中文:
定理 hasFDerivAtFilter_pi'
  证明: by
  simp [hasFDerivAtFilter_iff_isLittleOTVS, isLittleOTVS_pi]

@[simp]

Depends on / 依赖: hasFDerivAtFilter_iff_isLittleOTVS, isLittleOTVS_pi
-/
theorem hasFDerivAtFilter_pi' :
    HasFDerivAtFilter Φ Φ' L ↔
      forall i, HasFDerivAtFilter (fun x => Φ x i) ((proj i).comp Φ') L := by
  simp [hasFDerivAtFilter_iff_isLittleOTVS, isLittleOTVS_pi]

@[simp]
/--
theorem `hasStrictFDerivAt_pi'` / 定理 `hasStrictFDerivAt_pi'`

English:
theorem hasStrictFDerivAt_pi'
  proof: hasFDerivAtFilter_pi'

@[fun_prop]

中文:
定理 hasStrictFDerivAt_pi'
  证明: hasFDerivAtFilter_pi'

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_pi
-/
theorem hasStrictFDerivAt_pi' :
    HasStrictFDerivAt Φ Φ' x ↔ forall i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  hasFDerivAtFilter_pi'

@[fun_prop]
/--
theorem `hasStrictFDerivAt_pi''` / 定理 `hasStrictFDerivAt_pi''`

English:
theorem hasStrictFDerivAt_pi''
  given: (hφ : forall i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x)
  proof: hasStrictFDerivAt_pi'.2 hφ

@[fun_prop]

中文:
定理 hasStrictFDerivAt_pi''
  条件: (hφ : 对任意 i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x)
  证明: hasStrictFDerivAt_pi'.2 hφ

@[fun_prop]

Depends on / 依赖: hasStrictFDerivAt_pi
-/
theorem hasStrictFDerivAt_pi'' (hφ : forall i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
    HasStrictFDerivAt Φ Φ' x := hasStrictFDerivAt_pi'.2 hφ

@[fun_prop]
/--
theorem `hasStrictFDerivAt_apply` / 定理 `hasStrictFDerivAt_apply`

English:
theorem hasStrictFDerivAt_apply
  given: (i : ι) (f : forall i, F' i)
  proof: (proj (R := 𝕜) (φ := F') i).hasStrictFDerivAt

中文:
定理 hasStrictFDerivAt_apply
  条件: (i : ι) (f : 对任意 i, F' i)
  证明: (proj (R := 𝕜) (φ := F') i).hasStrictFDerivAt
-/
theorem hasStrictFDerivAt_apply (i : ι) (f : forall i, F' i) :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun f : forall i, F' i => f i) (proj i) f :=
  (proj (R := 𝕜) (φ := F') i).hasStrictFDerivAt

/--
theorem `hasStrictFDerivAt_pi` / 定理 `hasStrictFDerivAt_pi`

English:
theorem hasStrictFDerivAt_pi
  proof: hasStrictFDerivAt_pi'

中文:
定理 hasStrictFDerivAt_pi
  证明: hasStrictFDerivAt_pi'

Depends on / 依赖: hasStrictFDerivAt_pi
-/
theorem hasStrictFDerivAt_pi :
    HasStrictFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      forall i, HasStrictFDerivAt (φ i) (φ' i) x :=
  hasStrictFDerivAt_pi'

/--
theorem `hasFDerivAtFilter_pi` / 定理 `hasFDerivAtFilter_pi`

English:
theorem hasFDerivAtFilter_pi
  proof: hasFDerivAtFilter_pi'

@[simp]

中文:
定理 hasFDerivAtFilter_pi
  证明: hasFDerivAtFilter_pi'

@[simp]

Depends on / 依赖: hasFDerivAtFilter_pi
-/
theorem hasFDerivAtFilter_pi :
    HasFDerivAtFilter (fun x i => φ i x) (ContinuousLinearMap.pi φ') L ↔
      forall i, HasFDerivAtFilter (φ i) (φ' i) L :=
  hasFDerivAtFilter_pi'

@[simp]
/--
theorem `hasFDerivAt_pi'` / 定理 `hasFDerivAt_pi'`

English:
theorem hasFDerivAt_pi'
  proof: hasFDerivAtFilter_pi'

@[fun_prop]

中文:
定理 hasFDerivAt_pi'
  证明: hasFDerivAtFilter_pi'

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_pi
-/
theorem hasFDerivAt_pi' :
    HasFDerivAt Φ Φ' x ↔ forall i, HasFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  hasFDerivAtFilter_pi'

@[fun_prop]
/--
theorem `hasFDerivAt_pi''` / 定理 `hasFDerivAt_pi''`

English:
theorem hasFDerivAt_pi''
  given: (hφ : forall i, HasFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x)
  proof: hasFDerivAt_pi'.2 hφ

@[fun_prop]

中文:
定理 hasFDerivAt_pi''
  条件: (hφ : 对任意 i, 在点处Fréchet可导 (fun x => Φ x i) ((proj i).comp Φ') x)
  证明: hasFDerivAt_pi'.2 hφ

@[fun_prop]

Depends on / 依赖: hasFDerivAt_pi
-/
theorem hasFDerivAt_pi'' (hφ : forall i, HasFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
    HasFDerivAt Φ Φ' x := hasFDerivAt_pi'.2 hφ

@[fun_prop]
/--
theorem `hasFDerivAt_apply` / 定理 `hasFDerivAt_apply`

English:
theorem hasFDerivAt_apply
  given: (i : ι) (f : forall i, F' i)
  proof: (proj (R := 𝕜) (φ := F') i).hasFDerivAt

中文:
定理 hasFDerivAt_apply
  条件: (i : ι) (f : 对任意 i, F' i)
  证明: (proj (R := 𝕜) (φ := F') i).hasFDerivAt
-/
theorem hasFDerivAt_apply (i : ι) (f : forall i, F' i) :
    HasFDerivAt (𝕜 := 𝕜) (fun f : forall i, F' i => f i) (proj i) f :=
  (proj (R := 𝕜) (φ := F') i).hasFDerivAt

/--
theorem `hasFDerivAt_pi` / 定理 `hasFDerivAt_pi`

English:
theorem hasFDerivAt_pi
  proof: hasFDerivAtFilter_pi

@[simp]

中文:
定理 hasFDerivAt_pi
  证明: hasFDerivAtFilter_pi

@[simp]

Depends on / 依赖: hasFDerivAtFilter_pi
-/
theorem hasFDerivAt_pi :
    HasFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      forall i, HasFDerivAt (φ i) (φ' i) x :=
  hasFDerivAtFilter_pi

@[simp]
/--
theorem `hasFDerivWithinAt_pi'` / 定理 `hasFDerivWithinAt_pi'`

English:
theorem hasFDerivWithinAt_pi'
  proof: hasFDerivAtFilter_pi'

@[fun_prop]

中文:
定理 hasFDerivWithinAt_pi'
  证明: hasFDerivAtFilter_pi'

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_pi
-/
theorem hasFDerivWithinAt_pi' :
    HasFDerivWithinAt Φ Φ' s x ↔ forall i, HasFDerivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x :=
  hasFDerivAtFilter_pi'

@[fun_prop]
/--
theorem `hasFDerivWithinAt_pi''` / 定理 `hasFDerivWithinAt_pi''`

English:
theorem hasFDerivWithinAt_pi''
  proof: hasFDerivWithinAt_pi'.2 hφ

@[fun_prop]

中文:
定理 hasFDerivWithinAt_pi''
  证明: hasFDerivWithinAt_pi'.2 hφ

@[fun_prop]

Depends on / 依赖: hasFDerivWithinAt_pi
-/
theorem hasFDerivWithinAt_pi''
    (hφ : forall i, HasFDerivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x) :
    HasFDerivWithinAt Φ Φ' s x := hasFDerivWithinAt_pi'.2 hφ

@[fun_prop]
/--
theorem `hasFDerivWithinAt_apply` / 定理 `hasFDerivWithinAt_apply`

English:
theorem hasFDerivWithinAt_apply
  given: (i : ι) (f : forall i, F' i) (s' : Set (forall i, F' i))
  proof: (hasFDerivAt_apply i f).hasFDerivWithinAt

中文:
定理 hasFDerivWithinAt_apply
  条件: (i : ι) (f : 对任意 i, F' i) (s' : 集合 (对任意 i, F' i))
  证明: (hasFDerivAt_apply i f).hasFDerivWithinAt
-/
theorem hasFDerivWithinAt_apply (i : ι) (f : forall i, F' i) (s' : Set (forall i, F' i)) :
    HasFDerivWithinAt (𝕜 := 𝕜) (fun f : forall i, F' i => f i) (proj i) s' f :=
  (hasFDerivAt_apply i f).hasFDerivWithinAt

/--
theorem `hasFDerivWithinAt_pi` / 定理 `hasFDerivWithinAt_pi`

English:
theorem hasFDerivWithinAt_pi
  proof: hasFDerivAtFilter_pi

@[simp]

中文:
定理 hasFDerivWithinAt_pi
  证明: hasFDerivAtFilter_pi

@[simp]

Depends on / 依赖: hasFDerivAtFilter_pi
-/
theorem hasFDerivWithinAt_pi :
    HasFDerivWithinAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') s x ↔
      forall i, HasFDerivWithinAt (φ i) (φ' i) s x :=
  hasFDerivAtFilter_pi

@[simp]
/--
theorem `differentiableWithinAt_pi` / 定理 `differentiableWithinAt_pi`

English:
theorem differentiableWithinAt_pi
  proof: ⟨fun h i => (hasFDerivWithinAt_pi'.1 h.hasFDerivWithinAt i).differentiableWithinAt, fun h =>
    (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).differentiableWithinAt⟩

@[fun_prop]

中文:
定理 differentiableWithinAt_pi
  证明: ⟨fun h i => (hasFDerivWithinAt_pi'.1 h.hasFDerivWithinAt i).differentiableWithinAt, fun h =>
    (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).differentiableWithinAt⟩

@[fun_prop]

Depends on / 依赖: differentiableWithinAt, h.hasFDerivWithinAt, hasFDerivWithinAt, hasFDerivWithinAt_pi
-/
theorem differentiableWithinAt_pi :
    DifferentiableWithinAt 𝕜 Φ s x ↔ forall i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x :=
  ⟨fun h i => (hasFDerivWithinAt_pi'.1 h.hasFDerivWithinAt i).differentiableWithinAt, fun h =>
    (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).differentiableWithinAt⟩

@[fun_prop]
/--
theorem `differentiableWithinAt_pi''` / 定理 `differentiableWithinAt_pi''`

English:
theorem differentiableWithinAt_pi''
  given: (hφ : forall i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x)
  proof: differentiableWithinAt_pi.2 hφ

@[fun_prop]

中文:
定理 differentiableWithinAt_pi''
  条件: (hφ : 对任意 i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x)
  证明: differentiableWithinAt_pi.2 hφ

@[fun_prop]

Depends on / 依赖: differentiableWithinAt_pi
-/
theorem differentiableWithinAt_pi'' (hφ : forall i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x) :
    DifferentiableWithinAt 𝕜 Φ s x := differentiableWithinAt_pi.2 hφ

@[fun_prop]
/--
theorem `differentiableWithinAt_apply` / 定理 `differentiableWithinAt_apply`

English:
theorem differentiableWithinAt_apply
  given: (i : ι) (f : forall i, F' i) (s' : Set (forall i, F' i))
  proof: by
  apply HasFDerivWithinAt.differentiableWithinAt
  fun_prop

@[simp]

中文:
定理 differentiableWithinAt_apply
  条件: (i : ι) (f : 对任意 i, F' i) (s' : 集合 (对任意 i, F' i))
  证明: by
  apply HasFDerivWithinAt.differentiableWithinAt
  fun_prop

@[simp]

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.differentiableWithinAt, differentiableWithinAt, fun_prop
-/
theorem differentiableWithinAt_apply (i : ι) (f : forall i, F' i) (s' : Set (forall i, F' i)) :
    DifferentiableWithinAt (𝕜 := 𝕜) (fun f : forall i, F' i => f i) s' f := by
  apply HasFDerivWithinAt.differentiableWithinAt
  fun_prop

@[simp]
/--
theorem `differentiableAt_pi` / 定理 `differentiableAt_pi`

English:
theorem differentiableAt_pi
  statement: DifferentiableAt 𝕜 Φ x ↔ forall i, DifferentiableAt 𝕜 (fun x => Φ x i) x
  proof: ⟨fun h i => (hasFDerivAt_pi'.1 h.hasFDerivAt i).differentiableAt, fun h =>
    (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).differentiableAt⟩

@[fun_prop]

中文:
定理 differentiableAt_pi
  结论: DifferentiableAt 𝕜 Φ x ↔ 对任意 i, DifferentiableAt 𝕜 (fun x => Φ x i) x
  证明: ⟨fun h i => (hasFDerivAt_pi'.1 h.hasFDerivAt i).differentiableAt, fun h =>
    (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).differentiableAt⟩

@[fun_prop]

Depends on / 依赖: differentiableAt, h.hasFDerivAt, hasFDerivAt, hasFDerivAt_pi
-/
theorem differentiableAt_pi : DifferentiableAt 𝕜 Φ x ↔ forall i, DifferentiableAt 𝕜 (fun x => Φ x i) x :=
  ⟨fun h i => (hasFDerivAt_pi'.1 h.hasFDerivAt i).differentiableAt, fun h =>
    (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).differentiableAt⟩

@[fun_prop]
/--
theorem `differentiableAt_pi''` / 定理 `differentiableAt_pi''`

English:
theorem differentiableAt_pi''
  given: (hφ : forall i, DifferentiableAt 𝕜 (fun x => Φ x i) x)
  proof: differentiableAt_pi.2 hφ

@[fun_prop]

中文:
定理 differentiableAt_pi''
  条件: (hφ : 对任意 i, DifferentiableAt 𝕜 (fun x => Φ x i) x)
  证明: differentiableAt_pi.2 hφ

@[fun_prop]

Depends on / 依赖: differentiableAt_pi
-/
theorem differentiableAt_pi'' (hφ : forall i, DifferentiableAt 𝕜 (fun x => Φ x i) x) :
    DifferentiableAt 𝕜 Φ x := differentiableAt_pi.2 hφ

@[fun_prop]
/--
theorem `differentiableAt_apply` / 定理 `differentiableAt_apply`

English:
theorem differentiableAt_apply
  given: (i : ι) (f : forall i, F' i)
  proof: ⟨_, hasFDerivAt_apply ..⟩

中文:
定理 differentiableAt_apply
  条件: (i : ι) (f : 对任意 i, F' i)
  证明: ⟨_, hasFDerivAt_apply ..⟩
-/
theorem differentiableAt_apply (i : ι) (f : forall i, F' i) :
    DifferentiableAt (𝕜 := 𝕜) (fun f : forall i, F' i => f i) f :=
  ⟨_, hasFDerivAt_apply ..⟩

/--
theorem `differentiableOn_pi` / 定理 `differentiableOn_pi`

English:
theorem differentiableOn_pi
  statement: DifferentiableOn 𝕜 Φ s ↔ forall i, DifferentiableOn 𝕜 (fun x => Φ x i) s
  proof: ⟨fun h i x hx => differentiableWithinAt_pi.1 (h x hx) i, fun h x hx =>
    differentiableWithinAt_pi.2 fun i => h i x hx⟩

@[fun_prop]

中文:
定理 differentiableOn_pi
  结论: DifferentiableOn 𝕜 Φ s ↔ 对任意 i, DifferentiableOn 𝕜 (fun x => Φ x i) s
  证明: ⟨fun h i x hx => differentiableWithinAt_pi.1 (h x hx) i, fun h x hx =>
    differentiableWithinAt_pi.2 fun i => h i x hx⟩

@[fun_prop]

Depends on / 依赖: differentiableWithinAt_pi
-/
theorem differentiableOn_pi : DifferentiableOn 𝕜 Φ s ↔ forall i, DifferentiableOn 𝕜 (fun x => Φ x i) s :=
  ⟨fun h i x hx => differentiableWithinAt_pi.1 (h x hx) i, fun h x hx =>
    differentiableWithinAt_pi.2 fun i => h i x hx⟩

@[fun_prop]
/--
theorem `differentiableOn_pi''` / 定理 `differentiableOn_pi''`

English:
theorem differentiableOn_pi''
  given: (hφ : forall i, DifferentiableOn 𝕜 (fun x => Φ x i) s)
  proof: differentiableOn_pi.2 hφ

@[fun_prop]

中文:
定理 differentiableOn_pi''
  条件: (hφ : 对任意 i, DifferentiableOn 𝕜 (fun x => Φ x i) s)
  证明: differentiableOn_pi.2 hφ

@[fun_prop]

Depends on / 依赖: differentiableOn_pi
-/
theorem differentiableOn_pi'' (hφ : forall i, DifferentiableOn 𝕜 (fun x => Φ x i) s) :
    DifferentiableOn 𝕜 Φ s := differentiableOn_pi.2 hφ

@[fun_prop]
/--
theorem `differentiableOn_apply` / 定理 `differentiableOn_apply`

English:
theorem differentiableOn_apply
  given: (i : ι) (s' : Set (forall i, F' i))
  proof: fun _ _ => differentiableWithinAt_apply ..

中文:
定理 differentiableOn_apply
  条件: (i : ι) (s' : 集合 (对任意 i, F' i))
  证明: fun _ _ => differentiableWithinAt_apply ..
-/
theorem differentiableOn_apply (i : ι) (s' : Set (forall i, F' i)) :
    DifferentiableOn (𝕜 := 𝕜) (fun f : forall i, F' i => f i) s' :=
  fun _ _ => differentiableWithinAt_apply ..

/--
theorem `differentiable_pi` / 定理 `differentiable_pi`

English:
theorem differentiable_pi
  statement: Differentiable 𝕜 Φ ↔ forall i, Differentiable 𝕜 fun x => Φ x i
  proof: ⟨fun h i x => differentiableAt_pi.1 (h x) i, fun h x => differentiableAt_pi.2 fun i => h i x⟩

@[fun_prop]

中文:
定理 differentiable_pi
  结论: 可微 𝕜 Φ ↔ 对任意 i, 可微 𝕜 fun x => Φ x i
  证明: ⟨fun h i x => differentiableAt_pi.1 (h x) i, fun h x => differentiableAt_pi.2 fun i => h i x⟩

@[fun_prop]

Depends on / 依赖: differentiableAt_pi
-/
theorem differentiable_pi : Differentiable 𝕜 Φ ↔ forall i, Differentiable 𝕜 fun x => Φ x i :=
  ⟨fun h i x => differentiableAt_pi.1 (h x) i, fun h x => differentiableAt_pi.2 fun i => h i x⟩

@[fun_prop]
/--
theorem `differentiable_pi''` / 定理 `differentiable_pi''`

English:
theorem differentiable_pi''
  given: (hφ : forall i, Differentiable 𝕜 fun x => Φ x i)
  proof: differentiable_pi.2 hφ

@[fun_prop]

中文:
定理 differentiable_pi''
  条件: (hφ : 对任意 i, 可微 𝕜 fun x => Φ x i)
  证明: differentiable_pi.2 hφ

@[fun_prop]

Depends on / 依赖: differentiable_pi
-/
theorem differentiable_pi'' (hφ : forall i, Differentiable 𝕜 fun x => Φ x i) :
    Differentiable 𝕜 Φ := differentiable_pi.2 hφ

@[fun_prop]
/--
theorem `differentiable_apply` / 定理 `differentiable_apply`

English:
theorem differentiable_apply
  given: (i : ι)
  proof: by intro x; apply differentiableAt_apply

中文:
定理 differentiable_apply
  条件: (i : ι)
  证明: by intro x; apply differentiableAt_apply

Depends on / 依赖: differentiableAt_apply
-/
theorem differentiable_apply (i : ι) :
    Differentiable (𝕜 := 𝕜) (fun f : forall i, F' i => f i) := by intro x; apply differentiableAt_apply

-- TODO: find out which version (`φ` or `Φ`) works better with `rw`/`simp`
/--
theorem `fderivWithin_pi` / 定理 `fderivWithin_pi`

English:
theorem fderivWithin_pi
  statement: (h : forall i, DifferentiableWithinAt 𝕜 (φ i) s x)
  proof: (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).fderivWithin hs

中文:
定理 fderivWithin_pi
  结论: (h : 对任意 i, DifferentiableWithinAt 𝕜 (φ i) s x)
  证明: (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).fderivWithin hs

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hasFDerivWithinAt_pi
-/
theorem fderivWithin_pi (h : forall i, DifferentiableWithinAt 𝕜 (φ i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x i => φ i x) s x = pi fun i => fderivWithin 𝕜 (φ i) s x :=
  (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).fderivWithin hs

/--
theorem `fderiv_pi` / 定理 `fderiv_pi`

English:
theorem fderiv_pi
  given: (h : forall i, DifferentiableAt 𝕜 (φ i) x)
  proof: (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).fderiv

中文:
定理 fderiv_pi
  条件: (h : 对任意 i, DifferentiableAt 𝕜 (φ i) x)
  证明: (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hasFDerivAt_pi
-/
theorem fderiv_pi (h : forall i, DifferentiableAt 𝕜 (φ i) x) :
    fderiv 𝕜 (fun x i => φ i x) x = pi fun i => fderiv 𝕜 (φ i) x :=
  (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).fderiv

/--
theorem `fderivWithin_apply` / 定理 `fderivWithin_apply`

English:
theorem fderivWithin_apply
  statement: (hΦ : DifferentiableWithinAt 𝕜 Φ s x)
  proof: (hasFDerivWithinAt_pi'.1 hΦ.hasFDerivWithinAt i).fderivWithin hs

中文:
定理 fderivWithin_apply
  结论: (hΦ : DifferentiableWithinAt 𝕜 Φ s x)
  证明: (hasFDerivWithinAt_pi'.1 hΦ.hasFDerivWithinAt i).fderivWithin hs

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hasFDerivWithinAt_pi
-/
theorem fderivWithin_apply (hΦ : DifferentiableWithinAt 𝕜 Φ s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) (i : ι) :
    fderivWithin 𝕜 (fun x => Φ x i) s x = (proj i).comp (fderivWithin 𝕜 Φ s x) :=
  (hasFDerivWithinAt_pi'.1 hΦ.hasFDerivWithinAt i).fderivWithin hs

/--
theorem `fderiv_apply` / 定理 `fderiv_apply`

English:
theorem fderiv_apply
  given: (hΦ : DifferentiableAt 𝕜 Φ x) (i : ι)
  proof: (hasFDerivAt_pi'.1 hΦ.hasFDerivAt i).fderiv

中文:
定理 fderiv_apply
  条件: (hΦ : DifferentiableAt 𝕜 Φ x) (i : ι)
  证明: (hasFDerivAt_pi'.1 hΦ.hasFDerivAt i).fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hasFDerivAt_pi
-/
theorem fderiv_apply (hΦ : DifferentiableAt 𝕜 Φ x) (i : ι) :
    fderiv 𝕜 (fun x => Φ x i) x = (proj i).comp (fderiv 𝕜 Φ x) :=
  (hasFDerivAt_pi'.1 hΦ.hasFDerivAt i).fderiv

end Pi

/-!
### Derivatives of tuples `f : E → Π i : Fin n.succ, F' i`

These can be used to prove results about functions of the form `fun x ↦ ![f x, g x, h x]`,
as `Matrix.vecCons` is defeq to `Fin.cons`.
-/
section PiFin

variable {n : Nat} {F' : Fin n.succ -> Type*}
variable [forall i, NormedAddCommGroup (F' i)] [forall i, NormedSpace 𝕜 (F' i)]
variable {φ : E -> F' 0} {φs : E -> forall i, F' (Fin.succ i)}

/--
theorem `hasFDerivAtFilter_finCons` / 定理 `hasFDerivAtFilter_finCons`

English:
theorem hasFDerivAtFilter_finCons
  proof: by
  rw [hasFDerivAtFilter_pi']; rw [Fin.forall_fin_succ]; rw [hasFDerivAtFilter_pi']
  dsimp [ContinuousLinearMap.comp, LinearMap.comp, Function.comp_def]
  simp only [Fin.cons_zero, Fin.cons_succ]

中文:
定理 hasFDerivAtFilter_finCons
  证明: by
  rw [hasFDerivAtFilter_pi']; rw [Fin.forall_fin_succ]; rw [hasFDerivAtFilter_pi']
  dsimp [ContinuousLinearMap.comp, LinearMap.comp, Function.comp_def]
  simp only [Fin.cons_zero, Fin.cons_succ]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp, Fin.cons_succ, Fin.cons_zero, Fin.forall_fin_succ, Function, Function.comp_def, LinearMap, LinearMap.comp, comp_def, cons_succ, cons_zero, forall_fin_succ, hasFDerivAtFilter_pi
-/
theorem hasFDerivAtFilter_finCons
    {φ' : E ->L[𝕜] Π i, F' i} {l : Filter (E × E)} :
    HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) φ' l ↔
      HasFDerivAtFilter φ (.proj 0 ∘L φ') l ∧
      HasFDerivAtFilter φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') l := by
  rw [hasFDerivAtFilter_pi']; rw [Fin.forall_fin_succ]; rw [hasFDerivAtFilter_pi']
  dsimp [ContinuousLinearMap.comp, LinearMap.comp, Function.comp_def]
  simp only [Fin.cons_zero, Fin.cons_succ]

/--
theorem `hasFDerivAtFilter_finCons'` / 定理 `hasFDerivAtFilter_finCons'`

English:
theorem hasFDerivAtFilter_finCons'
  proof: hasFDerivAtFilter_finCons

中文:
定理 hasFDerivAtFilter_finCons'
  证明: hasFDerivAtFilter_finCons

Depends on / 依赖: hasFDerivAtFilter_finCons
-/
theorem hasFDerivAtFilter_finCons'
    {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (Fin.succ i)} {l : Filter (E × E)} :
    HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') l ↔
      HasFDerivAtFilter φ φ' l ∧ HasFDerivAtFilter φs φs' l :=
  hasFDerivAtFilter_finCons

/--
theorem `HasFDerivAtFilter.finCons` / 定理 `HasFDerivAtFilter.finCons`

English:
theorem HasFDerivAtFilter.finCons
  proof: hasFDerivAtFilter_finCons'.mpr ⟨h, hs⟩

中文:
定理 有FDerivAtFilter.finCons
  证明: hasFDerivAtFilter_finCons'.mpr ⟨h, hs⟩

Depends on / 依赖: hasFDerivAtFilter_finCons
-/
theorem HasFDerivAtFilter.finCons
    {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (Fin.succ i)} {l : Filter (E × E)}
    (h : HasFDerivAtFilter φ φ' l) (hs : HasFDerivAtFilter φs φs' l) :
    HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') l :=
  hasFDerivAtFilter_finCons'.mpr ⟨h, hs⟩

/--
theorem `hasStrictFDerivAt_finCons` / 定理 `hasStrictFDerivAt_finCons`

English:
theorem hasStrictFDerivAt_finCons
  given: {φ' : E ->L[𝕜] Π i, F' i}
  proof: hasFDerivAtFilter_finCons

中文:
定理 hasStrictFDerivAt_finCons
  条件: {φ' : E ->L[𝕜] Π i, F' i}
  证明: hasFDerivAtFilter_finCons

Depends on / 依赖: hasFDerivAtFilter_finCons
-/
theorem hasStrictFDerivAt_finCons {φ' : E ->L[𝕜] Π i, F' i} :
    HasStrictFDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔
      HasStrictFDerivAt φ (.proj 0 ∘L φ') x ∧
      HasStrictFDerivAt φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') x :=
  hasFDerivAtFilter_finCons

/--
theorem `hasStrictFDerivAt_finCons'` / 定理 `hasStrictFDerivAt_finCons'`

English:
theorem hasStrictFDerivAt_finCons'
  proof: hasStrictFDerivAt_finCons

@[fun_prop]

中文:
定理 hasStrictFDerivAt_finCons'
  证明: hasStrictFDerivAt_finCons

@[fun_prop]

Depends on / 依赖: hasStrictFDerivAt_finCons
-/
theorem hasStrictFDerivAt_finCons'
    {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (Fin.succ i)} :
    HasStrictFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x ↔
      HasStrictFDerivAt φ φ' x ∧ HasStrictFDerivAt φs φs' x :=
  hasStrictFDerivAt_finCons

@[fun_prop]
/--
theorem `HasStrictFDerivAt.finCons` / 定理 `HasStrictFDerivAt.finCons`

English:
theorem HasStrictFDerivAt.finCons
  proof: hasStrictFDerivAt_finCons'.mpr ⟨h, hs⟩

中文:
定理 HasStrictFDerivAt.finCons
  证明: hasStrictFDerivAt_finCons'.mpr ⟨h, hs⟩

Depends on / 依赖: hasStrictFDerivAt_finCons
-/
theorem HasStrictFDerivAt.finCons
    {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (Fin.succ i)}
    (h : HasStrictFDerivAt φ φ' x) (hs : HasStrictFDerivAt φs φs' x) :
    HasStrictFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x :=
  hasStrictFDerivAt_finCons'.mpr ⟨h, hs⟩

/--
theorem `hasFDerivAt_finCons` / 定理 `hasFDerivAt_finCons`

English:
theorem hasFDerivAt_finCons
  proof: hasFDerivAtFilter_finCons

中文:
定理 hasFDerivAt_finCons
  证明: hasFDerivAtFilter_finCons

Depends on / 依赖: hasFDerivAtFilter_finCons
-/
theorem hasFDerivAt_finCons
    {φ' : E ->L[𝕜] Π i, F' i} :
    HasFDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔
      HasFDerivAt φ (.proj 0 ∘L φ') x ∧ HasFDerivAt φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') x :=
  hasFDerivAtFilter_finCons

/--
theorem `hasFDerivAt_finCons'` / 定理 `hasFDerivAt_finCons'`

English:
theorem hasFDerivAt_finCons'
  proof: hasFDerivAt_finCons

@[fun_prop]

中文:
定理 hasFDerivAt_finCons'
  证明: hasFDerivAt_finCons

@[fun_prop]

Depends on / 依赖: hasFDerivAt_finCons
-/
theorem hasFDerivAt_finCons'
    {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (Fin.succ i)} :
    HasFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x ↔
      HasFDerivAt φ φ' x ∧ HasFDerivAt φs φs' x :=
  hasFDerivAt_finCons

@[fun_prop]
/--
theorem `HasFDerivAt.finCons` / 定理 `HasFDerivAt.finCons`

English:
theorem HasFDerivAt.finCons
  proof: hasFDerivAt_finCons'.mpr ⟨h, hs⟩

中文:
定理 在点处Fréchet可导.finCons
  证明: hasFDerivAt_finCons'.mpr ⟨h, hs⟩

Depends on / 依赖: hasFDerivAt_finCons
-/
theorem HasFDerivAt.finCons
    {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (Fin.succ i)}
    (h : HasFDerivAt φ φ' x) (hs : HasFDerivAt φs φs' x) :
    HasFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x :=
  hasFDerivAt_finCons'.mpr ⟨h, hs⟩

/--
theorem `hasFDerivWithinAt_finCons` / 定理 `hasFDerivWithinAt_finCons`

English:
theorem hasFDerivWithinAt_finCons
  proof: hasFDerivAtFilter_finCons

中文:
定理 hasFDerivWithinAt_finCons
  证明: hasFDerivAtFilter_finCons

Depends on / 依赖: hasFDerivAtFilter_finCons
-/
theorem hasFDerivWithinAt_finCons
    {φ' : E ->L[𝕜] Π i, F' i} :
    HasFDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) φ' s x ↔
      HasFDerivWithinAt φ (.proj 0 ∘L φ') s x ∧
      HasFDerivWithinAt φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') s x :=
  hasFDerivAtFilter_finCons

/--
theorem `hasFDerivWithinAt_finCons'` / 定理 `hasFDerivWithinAt_finCons'`

English:
theorem hasFDerivWithinAt_finCons'
  proof: hasFDerivAtFilter_finCons

@[fun_prop]

中文:
定理 hasFDerivWithinAt_finCons'
  证明: hasFDerivAtFilter_finCons

@[fun_prop]

Depends on / 依赖: hasFDerivAtFilter_finCons
-/
theorem hasFDerivWithinAt_finCons'
    {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (Fin.succ i)} :
    HasFDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') s x ↔
      HasFDerivWithinAt φ φ' s x ∧ HasFDerivWithinAt φs φs' s x :=
  hasFDerivAtFilter_finCons

@[fun_prop]
/--
theorem `HasFDerivWithinAt.finCons` / 定理 `HasFDerivWithinAt.finCons`

English:
theorem HasFDerivWithinAt.finCons
  proof: hasFDerivWithinAt_finCons'.mpr ⟨h, hs⟩

中文:
定理 HasFDerivWithinAt.finCons
  证明: hasFDerivWithinAt_finCons'.mpr ⟨h, hs⟩

Depends on / 依赖: hasFDerivWithinAt_finCons
-/
theorem HasFDerivWithinAt.finCons
    {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (Fin.succ i)}
    (h : HasFDerivWithinAt φ φ' s x) (hs : HasFDerivWithinAt φs φs' s x) :
    HasFDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') s x :=
  hasFDerivWithinAt_finCons'.mpr ⟨h, hs⟩

/--
theorem `differentiableWithinAt_finCons` / 定理 `differentiableWithinAt_finCons`

English:
theorem differentiableWithinAt_finCons
  proof: by
  rw [differentiableWithinAt_pi]; rw [Fin.forall_fin_succ]; rw [differentiableWithinAt_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

中文:
定理 differentiableWithinAt_finCons
  证明: by
  rw [differentiableWithinAt_pi]; rw [Fin.forall_fin_succ]; rw [differentiableWithinAt_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

Depends on / 依赖: Fin.cons_succ, Fin.cons_zero, Fin.forall_fin_succ, cons_succ, cons_zero, differentiableWithinAt_pi, forall_fin_succ
-/
theorem differentiableWithinAt_finCons :
    DifferentiableWithinAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) s x ↔
      DifferentiableWithinAt 𝕜 φ s x ∧ DifferentiableWithinAt 𝕜 φs s x := by
  rw [differentiableWithinAt_pi]; rw [Fin.forall_fin_succ]; rw [differentiableWithinAt_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

/--
theorem `differentiableWithinAt_finCons'` / 定理 `differentiableWithinAt_finCons'`

English:
theorem differentiableWithinAt_finCons'
  proof: differentiableWithinAt_finCons

@[fun_prop]

中文:
定理 differentiableWithinAt_finCons'
  证明: differentiableWithinAt_finCons

@[fun_prop]

Depends on / 依赖: differentiableWithinAt_finCons
-/
theorem differentiableWithinAt_finCons' :
    DifferentiableWithinAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) s x ↔
      DifferentiableWithinAt 𝕜 φ s x ∧ DifferentiableWithinAt 𝕜 φs s x :=
  differentiableWithinAt_finCons

@[fun_prop]
/--
theorem `DifferentiableWithinAt.finCons` / 定理 `DifferentiableWithinAt.finCons`

English:
theorem DifferentiableWithinAt.finCons
  proof: differentiableWithinAt_finCons'.mpr ⟨h, hs⟩

中文:
定理 DifferentiableWithinAt.finCons
  证明: differentiableWithinAt_finCons'.mpr ⟨h, hs⟩

Depends on / 依赖: differentiableWithinAt_finCons
-/
theorem DifferentiableWithinAt.finCons
    (h : DifferentiableWithinAt 𝕜 φ s x) (hs : DifferentiableWithinAt 𝕜 φs s x) :
    DifferentiableWithinAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) s x :=
  differentiableWithinAt_finCons'.mpr ⟨h, hs⟩

/--
theorem `differentiableAt_finCons` / 定理 `differentiableAt_finCons`

English:
theorem differentiableAt_finCons
  proof: by
  rw [differentiableAt_pi]; rw [Fin.forall_fin_succ]; rw [differentiableAt_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

中文:
定理 differentiableAt_finCons
  证明: by
  rw [differentiableAt_pi]; rw [Fin.forall_fin_succ]; rw [differentiableAt_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

Depends on / 依赖: Fin.cons_succ, Fin.cons_zero, Fin.forall_fin_succ, cons_succ, cons_zero, differentiableAt_pi, forall_fin_succ
-/
theorem differentiableAt_finCons :
    DifferentiableAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) x ↔
      DifferentiableAt 𝕜 φ x ∧ DifferentiableAt 𝕜 φs x := by
  rw [differentiableAt_pi]; rw [Fin.forall_fin_succ]; rw [differentiableAt_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

/--
theorem `differentiableAt_finCons'` / 定理 `differentiableAt_finCons'`

English:
theorem differentiableAt_finCons'
  proof: differentiableAt_finCons

@[fun_prop]

中文:
定理 differentiableAt_finCons'
  证明: differentiableAt_finCons

@[fun_prop]

Depends on / 依赖: differentiableAt_finCons
-/
theorem differentiableAt_finCons' :
    DifferentiableAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) x ↔
      DifferentiableAt 𝕜 φ x ∧ DifferentiableAt 𝕜 φs x :=
  differentiableAt_finCons

@[fun_prop]
/--
theorem `DifferentiableAt.finCons` / 定理 `DifferentiableAt.finCons`

English:
theorem DifferentiableAt.finCons
  proof: differentiableAt_finCons'.mpr ⟨h, hs⟩

中文:
定理 DifferentiableAt.finCons
  证明: differentiableAt_finCons'.mpr ⟨h, hs⟩

Depends on / 依赖: differentiableAt_finCons
-/
theorem DifferentiableAt.finCons
    (h : DifferentiableAt 𝕜 φ x) (hs : DifferentiableAt 𝕜 φs x) :
    DifferentiableAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) x :=
  differentiableAt_finCons'.mpr ⟨h, hs⟩

/--
theorem `differentiableOn_finCons` / 定理 `differentiableOn_finCons`

English:
theorem differentiableOn_finCons
  proof: by
  rw [differentiableOn_pi]; rw [Fin.forall_fin_succ]; rw [differentiableOn_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

中文:
定理 differentiableOn_finCons
  证明: by
  rw [differentiableOn_pi]; rw [Fin.forall_fin_succ]; rw [differentiableOn_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

Depends on / 依赖: Fin.cons_succ, Fin.cons_zero, Fin.forall_fin_succ, cons_succ, cons_zero, differentiableOn_pi, forall_fin_succ
-/
theorem differentiableOn_finCons :
    DifferentiableOn 𝕜 (fun x => Fin.cons (φ x) (φs x)) s ↔
      DifferentiableOn 𝕜 φ s ∧ DifferentiableOn 𝕜 φs s := by
  rw [differentiableOn_pi]; rw [Fin.forall_fin_succ]; rw [differentiableOn_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

/--
theorem `differentiableOn_finCons'` / 定理 `differentiableOn_finCons'`

English:
theorem differentiableOn_finCons'
  proof: differentiableOn_finCons

@[fun_prop]

中文:
定理 differentiableOn_finCons'
  证明: differentiableOn_finCons

@[fun_prop]

Depends on / 依赖: differentiableOn_finCons
-/
theorem differentiableOn_finCons' :
    DifferentiableOn 𝕜 (fun x => Fin.cons (φ x) (φs x)) s ↔
      DifferentiableOn 𝕜 φ s ∧ DifferentiableOn 𝕜 φs s :=
  differentiableOn_finCons

@[fun_prop]
/--
theorem `DifferentiableOn.finCons` / 定理 `DifferentiableOn.finCons`

English:
theorem DifferentiableOn.finCons
  proof: differentiableOn_finCons'.mpr ⟨h, hs⟩

中文:
定理 DifferentiableOn.finCons
  证明: differentiableOn_finCons'.mpr ⟨h, hs⟩

Depends on / 依赖: differentiableOn_finCons
-/
theorem DifferentiableOn.finCons
    (h : DifferentiableOn 𝕜 φ s) (hs : DifferentiableOn 𝕜 φs s) :
    DifferentiableOn 𝕜 (fun x => Fin.cons (φ x) (φs x)) s :=
  differentiableOn_finCons'.mpr ⟨h, hs⟩

/--
theorem `differentiable_finCons` / 定理 `differentiable_finCons`

English:
theorem differentiable_finCons
  proof: by
  rw [differentiable_pi]; rw [Fin.forall_fin_succ]; rw [differentiable_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

中文:
定理 differentiable_finCons
  证明: by
  rw [differentiable_pi]; rw [Fin.forall_fin_succ]; rw [differentiable_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

Depends on / 依赖: Fin.cons_succ, Fin.cons_zero, Fin.forall_fin_succ, cons_succ, cons_zero, differentiable_pi, forall_fin_succ
-/
theorem differentiable_finCons :
    Differentiable 𝕜 (fun x => Fin.cons (φ x) (φs x)) ↔
      Differentiable 𝕜 φ ∧ Differentiable 𝕜 φs := by
  rw [differentiable_pi]; rw [Fin.forall_fin_succ]; rw [differentiable_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

/--
theorem `differentiable_finCons'` / 定理 `differentiable_finCons'`

English:
theorem differentiable_finCons'
  proof: differentiable_finCons

@[fun_prop]

中文:
定理 differentiable_finCons'
  证明: differentiable_finCons

@[fun_prop]

Depends on / 依赖: differentiable_finCons
-/
theorem differentiable_finCons' :
    Differentiable 𝕜 (fun x => Fin.cons (φ x) (φs x)) ↔
      Differentiable 𝕜 φ ∧ Differentiable 𝕜 φs :=
  differentiable_finCons

@[fun_prop]
/--
theorem `Differentiable.finCons` / 定理 `Differentiable.finCons`

English:
theorem Differentiable.finCons
  proof: differentiable_finCons'.mpr ⟨h, hs⟩

中文:
定理 可微.finCons
  证明: differentiable_finCons'.mpr ⟨h, hs⟩

Depends on / 依赖: differentiable_finCons
-/
theorem Differentiable.finCons
    (h : Differentiable 𝕜 φ) (hs : Differentiable 𝕜 φs) :
    Differentiable 𝕜 (fun x => Fin.cons (φ x) (φs x)) :=
  differentiable_finCons'.mpr ⟨h, hs⟩

-- TODO: write the `Fin.cons` versions of `fderivWithin_pi` and `fderiv_pi`

end PiFin

end CartesianProduct

end
