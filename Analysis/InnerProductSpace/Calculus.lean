/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Calculus in inner product spaces

In this file we prove that the inner product and square of the norm in an inner space are
infinitely `ℝ`-smooth. In order to state these results, we need a `NormedSpace ℝ E`
instance. Though we can deduce this structure from `InnerProductSpace 𝕜 E`, this instance may be
not definitionally equal to some other “natural” instance. So, we assume `[NormedSpace ℝ E]`.

We also prove that functions to a `EuclideanSpace` are (higher) differentiable if and only if
their components are. This follows from the corresponding fact for finite product of normed spaces,
and from the equivalence of norms in finite dimensions.

## TODO

The last part of the file should be generalized to `PiLp`.
-/

@[expose] public section

noncomputable section

open RCLike Real Filter

section DerivInner

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace Real F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (𝕜) [NormedSpace Real E]

/--
Definition of `fderivInnerCLM` / `fderivInnerCLM` 的定义

English:
definition fderivInnerCLM
  signature: (p : E × E)
  body: isBoundedBilinearMap_inner.deriv p

@[simp]

中文:
定义 fderivInnerCLM
  签名: (p : E × E)
  定义体: isBoundedBilinearMap_inner.deriv p

@[simp]

Depends on / 依赖: isBoundedBilinearMap_inner, isBoundedBilinearMap_inner.deriv
-/
def fderivInnerCLM (p : E × E) : E × E ->L[Real] 𝕜 :=
  isBoundedBilinearMap_inner.deriv p

@[simp]
/--
theorem `fderivInnerCLM_apply` / 定理 `fderivInnerCLM_apply`

English:
theorem fderivInnerCLM_apply
  given: (p x : E × E)
  statement: fderivInnerCLM 𝕜 p x = ⟪p.1, x.2⟫ + ⟪x.1, p.2⟫
  proof: rfl

中文:
定理 fderivInnerCLM_apply
  条件: (p x : E × E)
  结论: fderivInnerCLM 𝕜 p x = ⟪p.1, x.2⟫ + ⟪x.1, p.2⟫
  证明: rfl
-/
theorem fderivInnerCLM_apply (p x : E × E) : fderivInnerCLM 𝕜 p x = ⟪p.1, x.2⟫ + ⟪x.1, p.2⟫ :=
  rfl

variable {𝕜}

/--
theorem `contDiff_inner` / 定理 `contDiff_inner`

English:
theorem contDiff_inner
  given: {n}
  statement: ContDiff Real n fun p : E × E => ⟪p.1, p.2⟫
  proof: isBoundedBilinearMap_inner.contDiff

中文:
定理 contDiff_inner
  条件: {n}
  结论: 连续可微 实数 n fun p : E × E => ⟪p.1, p.2⟫
  证明: isBoundedBilinearMap_inner.contDiff

Depends on / 依赖: contDiff, isBoundedBilinearMap_inner, isBoundedBilinearMap_inner.contDiff
-/
theorem contDiff_inner {n} : ContDiff Real n fun p : E × E => ⟪p.1, p.2⟫ :=
  isBoundedBilinearMap_inner.contDiff

/--
theorem `contDiffAt_inner` / 定理 `contDiffAt_inner`

English:
theorem contDiffAt_inner
  given: {p : E × E} {n}
  statement: ContDiffAt Real n (fun p : E × E => ⟪p.1, p.2⟫) p
  proof: ContDiff.contDiffAt contDiff_inner

中文:
定理 contDiffAt_inner
  条件: {p : E × E} {n}
  结论: ContDiffAt 实数 n (fun p : E × E => ⟪p.1, p.2⟫) p
  证明: ContDiff.contDiffAt contDiff_inner

Depends on / 依赖: ContDiff, ContDiff.contDiffAt, contDiffAt, contDiff_inner
-/
theorem contDiffAt_inner {p : E × E} {n} : ContDiffAt Real n (fun p : E × E => ⟪p.1, p.2⟫) p :=
  ContDiff.contDiffAt contDiff_inner

/--
theorem `differentiable_inner` / 定理 `differentiable_inner`

English:
theorem differentiable_inner
  statement: Differentiable Real fun p : E × E => ⟪p.1, p.2⟫
  proof: isBoundedBilinearMap_inner.differentiableAt

中文:
定理 differentiable_inner
  结论: 可微 实数 fun p : E × E => ⟪p.1, p.2⟫
  证明: isBoundedBilinearMap_inner.differentiableAt

Depends on / 依赖: differentiableAt, isBoundedBilinearMap_inner, isBoundedBilinearMap_inner.differentiableAt
-/
theorem differentiable_inner : Differentiable Real fun p : E × E => ⟪p.1, p.2⟫ :=
  isBoundedBilinearMap_inner.differentiableAt

variable (𝕜)
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace Real G] {f g : G -> E} {f' g' : G ->L[Real] E}
  {s : Set G} {x : G} {n : WithTop Nat∞}

/--
theorem `ContDiffWithinAt.inner` / 定理 `ContDiffWithinAt.inner`

English:
theorem ContDiffWithinAt.inner
  given: (hf : ContDiffWithinAt Real n f s x) (hg : ContDiffWithinAt Real n g s x)
  proof: contDiffAt_inner.comp_contDiffWithinAt x (hf.prodMk hg)

nonrec theorem ContDiffAt.inner (hf : ContDiffAt Real n f x) (hg : ContDiffAt Real n g x) :
    ContDiffAt Real n (fun x => ⟪f x, g x⟫) x :=
  hf.inner 𝕜 hg

中文:
定理 ContDiffWithinAt.inner
  条件: (hf : ContDiffWithinAt 实数 n f s x) (hg : ContDiffWithinAt 实数 n g s x)
  证明: contDiffAt_inner.comp_contDiffWithinAt x (hf.prodMk hg)

nonrec theorem ContDiffAt.inner (hf : ContDiffAt Real n f x) (hg : ContDiffAt Real n g x) :
    ContDiffAt Real n (fun x => ⟪f x, g x⟫) x :=
  hf.inner 𝕜 hg

Depends on / 依赖: comp_contDiffWithinAt, contDiffAt_inner, contDiffAt_inner.comp_contDiffWithinAt, hf.prodMk, prodMk
-/
theorem ContDiffWithinAt.inner (hf : ContDiffWithinAt Real n f s x) (hg : ContDiffWithinAt Real n g s x) :
    ContDiffWithinAt Real n (fun x => ⟪f x, g x⟫) s x :=
  contDiffAt_inner.comp_contDiffWithinAt x (hf.prodMk hg)

nonrec theorem ContDiffAt.inner (hf : ContDiffAt Real n f x) (hg : ContDiffAt Real n g x) :
    ContDiffAt Real n (fun x => ⟪f x, g x⟫) x :=
  hf.inner 𝕜 hg

/--
theorem `ContDiffOn.inner` / 定理 `ContDiffOn.inner`

English:
theorem ContDiffOn.inner
  given: (hf : ContDiffOn Real n f s) (hg : ContDiffOn Real n g s)
  proof: fun x hx => (hf x hx).inner 𝕜 (hg x hx)

中文:
定理 ContDiffOn.inner
  条件: (hf : ContDiffOn 实数 n f s) (hg : ContDiffOn 实数 n g s)
  证明: fun x hx => (hf x hx).inner 𝕜 (hg x hx)
-/
theorem ContDiffOn.inner (hf : ContDiffOn Real n f s) (hg : ContDiffOn Real n g s) :
    ContDiffOn Real n (fun x => ⟪f x, g x⟫) s := fun x hx => (hf x hx).inner 𝕜 (hg x hx)

/--
theorem `ContDiff.inner` / 定理 `ContDiff.inner`

English:
theorem ContDiff.inner
  given: (hf : ContDiff Real n f) (hg : ContDiff Real n g)
  proof: contDiff_inner.comp (hf.prodMk hg)

中文:
定理 连续可微.inner
  条件: (hf : 连续可微 实数 n f) (hg : 连续可微 实数 n g)
  证明: contDiff_inner.comp (hf.prodMk hg)

Depends on / 依赖: contDiff_inner, contDiff_inner.comp, hf.prodMk, prodMk
-/
theorem ContDiff.inner (hf : ContDiff Real n f) (hg : ContDiff Real n g) :
    ContDiff Real n fun x => ⟪f x, g x⟫ :=
  contDiff_inner.comp (hf.prodMk hg)

/--
theorem `HasFDerivWithinAt.inner` / 定理 `HasFDerivWithinAt.inner`

English:
theorem HasFDerivWithinAt.inner
  statement: (hf : HasFDerivWithinAt f f' s x)
  proof: by
  -- `by exact` to handle a tricky unification.
  exact isBoundedBilinearMap_inner (𝕜 := 𝕜) (E := E)
.comp_hasFDerivWithinAt x (hf.prodMk hg) .hasFDerivAt (f x, g x)

中文:
定理 HasFDerivWithinAt.inner
  结论: (hf : HasFDerivWithinAt f f' s x)
  证明: by
  -- `by exact` to handle a tricky unification.
  exact isBoundedBilinearMap_inner (𝕜 := 𝕜) (E := E)
.comp_hasFDerivWithinAt x (hf.prodMk hg) .hasFDerivAt (f x, g x)
-/
theorem HasFDerivWithinAt.inner (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) :
    HasFDerivWithinAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x, g x)).comp <| f'.prod g') s
      x := by
  -- `by exact` to handle a tricky unification.
  exact isBoundedBilinearMap_inner (𝕜 := 𝕜) (E := E)
.comp_hasFDerivWithinAt x (hf.prodMk hg) .hasFDerivAt (f x, g x)

/--
theorem `HasStrictFDerivAt.inner` / 定理 `HasStrictFDerivAt.inner`

English:
theorem HasStrictFDerivAt.inner
  given: (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
  proof: isBoundedBilinearMap_inner (𝕜 := 𝕜) (E := E)
.comp x (hf.prodMk hg) .hasStrictFDerivAt (f x, g x)

中文:
定理 HasStrictFDerivAt.inner
  条件: (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
  证明: isBoundedBilinearMap_inner (𝕜 := 𝕜) (E := E)
.comp x (hf.prodMk hg) .hasStrictFDerivAt (f x, g x)

Depends on / 依赖: hasStrictFDerivAt, hf.prodMk, isBoundedBilinearMap_inner, prodMk
-/
theorem HasStrictFDerivAt.inner (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x, g x)).comp <| f'.prod g') x :=
  isBoundedBilinearMap_inner (𝕜 := 𝕜) (E := E)
.comp x (hf.prodMk hg) .hasStrictFDerivAt (f x, g x)

/--
theorem `HasFDerivAt.inner` / 定理 `HasFDerivAt.inner`

English:
theorem HasFDerivAt.inner
  given: (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
  proof: by
  -- `by exact` to handle a tricky unification.
  exact isBoundedBilinearMap_inner (𝕜 := 𝕜) (E := E)
.comp x (hf.prodMk hg) .hasFDerivAt (f x, g x)

中文:
定理 在点处Fréchet可导.inner
  条件: (hf : 在点处Fréchet可导 f f' x) (hg : 在点处Fréchet可导 g g' x)
  证明: by
  -- `by exact` to handle a tricky unification.
  exact isBoundedBilinearMap_inner (𝕜 := 𝕜) (E := E)
.comp x (hf.prodMk hg) .hasFDerivAt (f x, g x)
-/
theorem HasFDerivAt.inner (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x, g x)).comp <| f'.prod g') x := by
  -- `by exact` to handle a tricky unification.
  exact isBoundedBilinearMap_inner (𝕜 := 𝕜) (E := E)
.comp x (hf.prodMk hg) .hasFDerivAt (f x, g x)

/--
theorem `HasDerivWithinAt.inner` / 定理 `HasDerivWithinAt.inner`

English:
theorem HasDerivWithinAt.inner
  statement: {f g : Real -> E} {f' g' : E} {s : Set Real} {x : Real}
  proof: by
  simpa using (hf.hasFDerivWithinAt.inner 𝕜 hg.hasFDerivWithinAt).hasDerivWithinAt

中文:
定理 HasDerivWithinAt.inner
  结论: {f g : 实数 -> E} {f' g' : E} {s : 集合 实数} {x : 实数}
  证明: by
  simpa using (hf.hasFDerivWithinAt.inner 𝕜 hg.hasFDerivWithinAt).hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.inner, hg.hasFDerivWithinAt
-/
theorem HasDerivWithinAt.inner {f g : Real -> E} {f' g' : E} {s : Set Real} {x : Real}
    (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x) :
    HasDerivWithinAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) s x := by
  simpa using (hf.hasFDerivWithinAt.inner 𝕜 hg.hasFDerivWithinAt).hasDerivWithinAt

/--
theorem `HasDerivAt.inner` / 定理 `HasDerivAt.inner`

English:
theorem HasDerivAt.inner
  given: {f g : Real -> E} {f' g' : E} {x : Real}
  proof: by
  simpa only [← hasDerivWithinAt_univ] using HasDerivWithinAt.inner 𝕜

中文:
定理 在点处可导.inner
  条件: {f g : 实数 -> E} {f' g' : E} {x : 实数}
  证明: by
  simpa only [← hasDerivWithinAt_univ] using HasDerivWithinAt.inner 𝕜

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.inner, hasDerivWithinAt_univ
-/
theorem HasDerivAt.inner {f g : Real -> E} {f' g' : E} {x : Real} :
    HasDerivAt f f' x -> HasDerivAt g g' x ->
      HasDerivAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) x := by
  simpa only [← hasDerivWithinAt_univ] using HasDerivWithinAt.inner 𝕜

/--
theorem `DifferentiableWithinAt.inner` / 定理 `DifferentiableWithinAt.inner`

English:
theorem DifferentiableWithinAt.inner
  statement: (hf : DifferentiableWithinAt Real f s x)
  proof: (hf.hasFDerivWithinAt.inner 𝕜 hg.hasFDerivWithinAt).differentiableWithinAt

中文:
定理 DifferentiableWithinAt.inner
  结论: (hf : DifferentiableWithinAt 实数 f s x)
  证明: (hf.hasFDerivWithinAt.inner 𝕜 hg.hasFDerivWithinAt).differentiableWithinAt

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.inner, hg.hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.inner (hf : DifferentiableWithinAt Real f s x)
    (hg : DifferentiableWithinAt Real g s x) : DifferentiableWithinAt Real (fun x => ⟪f x, g x⟫) s x :=
  (hf.hasFDerivWithinAt.inner 𝕜 hg.hasFDerivWithinAt).differentiableWithinAt

/--
theorem `DifferentiableAt.inner` / 定理 `DifferentiableAt.inner`

English:
theorem DifferentiableAt.inner
  given: (hf : DifferentiableAt Real f x) (hg : DifferentiableAt Real g x)
  proof: (hf.hasFDerivAt.inner 𝕜 hg.hasFDerivAt).differentiableAt

中文:
定理 DifferentiableAt.inner
  条件: (hf : DifferentiableAt 实数 f x) (hg : DifferentiableAt 实数 g x)
  证明: (hf.hasFDerivAt.inner 𝕜 hg.hasFDerivAt).differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hf.hasFDerivAt.inner, hg.hasFDerivAt
-/
theorem DifferentiableAt.inner (hf : DifferentiableAt Real f x) (hg : DifferentiableAt Real g x) :
    DifferentiableAt Real (fun x => ⟪f x, g x⟫) x :=
  (hf.hasFDerivAt.inner 𝕜 hg.hasFDerivAt).differentiableAt

/--
theorem `DifferentiableOn.inner` / 定理 `DifferentiableOn.inner`

English:
theorem DifferentiableOn.inner
  given: (hf : DifferentiableOn Real f s) (hg : DifferentiableOn Real g s)
  proof: fun x hx => (hf x hx).inner 𝕜 (hg x hx)

中文:
定理 DifferentiableOn.inner
  条件: (hf : DifferentiableOn 实数 f s) (hg : DifferentiableOn 实数 g s)
  证明: fun x hx => (hf x hx).inner 𝕜 (hg x hx)
-/
theorem DifferentiableOn.inner (hf : DifferentiableOn Real f s) (hg : DifferentiableOn Real g s) :
    DifferentiableOn Real (fun x => ⟪f x, g x⟫) s := fun x hx => (hf x hx).inner 𝕜 (hg x hx)

/--
theorem `Differentiable.inner` / 定理 `Differentiable.inner`

English:
theorem Differentiable.inner
  given: (hf : Differentiable Real f) (hg : Differentiable Real g)
  proof: fun x => (hf x).inner 𝕜 (hg x)

中文:
定理 可微.inner
  条件: (hf : 可微 实数 f) (hg : 可微 实数 g)
  证明: fun x => (hf x).inner 𝕜 (hg x)
-/
theorem Differentiable.inner (hf : Differentiable Real f) (hg : Differentiable Real g) :
    Differentiable Real fun x => ⟪f x, g x⟫ := fun x => (hf x).inner 𝕜 (hg x)

/--
theorem `fderiv_inner_apply` / 定理 `fderiv_inner_apply`

English:
theorem fderiv_inner_apply
  given: (hf : DifferentiableAt Real f x) (hg : DifferentiableAt Real g x) (y : G)
  proof: by
  rw [(hf.hasFDerivAt.inner 𝕜 hg.hasFDerivAt).fderiv]; rfl

中文:
定理 fderiv_inner_apply
  条件: (hf : DifferentiableAt 实数 f x) (hg : DifferentiableAt 实数 g x) (y : G)
  证明: by
  rw [(hf.hasFDerivAt.inner 𝕜 hg.hasFDerivAt).fderiv]; rfl

Depends on / 依赖: fderiv, hasFDerivAt, hf.hasFDerivAt.inner, hg.hasFDerivAt
-/
theorem fderiv_inner_apply (hf : DifferentiableAt Real f x) (hg : DifferentiableAt Real g x) (y : G) :
    fderiv Real (fun t => ⟪f t, g t⟫) x y = ⟪f x, fderiv Real g x y⟫ + ⟪fderiv Real f x y, g x⟫ := by
  rw [(hf.hasFDerivAt.inner 𝕜 hg.hasFDerivAt).fderiv]; rfl

/--
theorem `deriv_inner_apply` / 定理 `deriv_inner_apply`

English:
theorem deriv_inner_apply
  statement: {f g : Real -> E} {x : Real} (hf : DifferentiableAt Real f x)
  proof: (hf.hasDerivAt.inner 𝕜 hg.hasDerivAt).deriv

中文:
定理 deriv_inner_apply
  结论: {f g : 实数 -> E} {x : 实数} (hf : DifferentiableAt 实数 f x)
  证明: (hf.hasDerivAt.inner 𝕜 hg.hasDerivAt).deriv

Depends on / 依赖: hasDerivAt, hf.hasDerivAt.inner, hg.hasDerivAt
-/
theorem deriv_inner_apply {f g : Real -> E} {x : Real} (hf : DifferentiableAt Real f x)
    (hg : DifferentiableAt Real g x) :
    deriv (fun t => ⟪f t, g t⟫) x = ⟪f x, deriv g x⟫ + ⟪deriv f x, g x⟫ :=
  (hf.hasDerivAt.inner 𝕜 hg.hasDerivAt).deriv

section
include 𝕜

/--
theorem `contDiff_norm_sq` / 定理 `contDiff_norm_sq`

English:
theorem contDiff_norm_sq
  statement: ContDiff Real n fun x : E => ‖x‖ ^ 2
  proof: by
  convert! (reCLM : 𝕜 ->L[Real] Real).contDiff.comp ((contDiff_id (E := E)).inner 𝕜 (contDiff_id (E := E)))
  exact (inner_self_eq_norm_sq _).symm

中文:
定理 contDiff_norm_sq
  结论: 连续可微 实数 n fun x : E => ‖x‖ ^ 2
  证明: by
  convert! (reCLM : 𝕜 ->L[Real] Real).contDiff.comp ((contDiff_id (E := E)).inner 𝕜 (contDiff_id (E := E)))
  exact (inner_self_eq_norm_sq _).symm

Depends on / 依赖: contDiff, contDiff.comp, contDiff_id, convert, inner_self_eq_norm_sq
-/
theorem contDiff_norm_sq : ContDiff Real n fun x : E => ‖x‖ ^ 2 := by
  convert! (reCLM : 𝕜 ->L[Real] Real).contDiff.comp ((contDiff_id (E := E)).inner 𝕜 (contDiff_id (E := E)))
  exact (inner_self_eq_norm_sq _).symm

/--
theorem `ContDiff.norm_sq` / 定理 `ContDiff.norm_sq`

English:
theorem ContDiff.norm_sq
  given: (hf : ContDiff Real n f)
  statement: ContDiff Real n fun x => ‖f x‖ ^ 2
  proof: (contDiff_norm_sq 𝕜).comp hf

中文:
定理 连续可微.norm_sq
  条件: (hf : 连续可微 实数 n f)
  结论: 连续可微 实数 n fun x => ‖f x‖ ^ 2
  证明: (contDiff_norm_sq 𝕜).comp hf

Depends on / 依赖: contDiff_norm_sq
-/
theorem ContDiff.norm_sq (hf : ContDiff Real n f) : ContDiff Real n fun x => ‖f x‖ ^ 2 :=
  (contDiff_norm_sq 𝕜).comp hf

/--
theorem `ContDiffWithinAt.norm_sq` / 定理 `ContDiffWithinAt.norm_sq`

English:
theorem ContDiffWithinAt.norm_sq
  given: (hf : ContDiffWithinAt Real n f s x)
  proof: (contDiff_norm_sq 𝕜).contDiffAt.comp_contDiffWithinAt x hf

nonrec theorem ContDiffAt.norm_sq (hf : ContDiffAt Real n f x) : ContDiffAt Real n (‖f ·‖ ^ 2) x :=
  hf.norm_sq 𝕜

中文:
定理 ContDiffWithinAt.norm_sq
  条件: (hf : ContDiffWithinAt 实数 n f s x)
  证明: (contDiff_norm_sq 𝕜).contDiffAt.comp_contDiffWithinAt x hf

nonrec theorem ContDiffAt.norm_sq (hf : ContDiffAt Real n f x) : ContDiffAt Real n (‖f ·‖ ^ 2) x :=
  hf.norm_sq 𝕜

Depends on / 依赖: comp_contDiffWithinAt, contDiffAt, contDiffAt.comp_contDiffWithinAt, contDiff_norm_sq
-/
theorem ContDiffWithinAt.norm_sq (hf : ContDiffWithinAt Real n f s x) :
    ContDiffWithinAt Real n (fun y => ‖f y‖ ^ 2) s x :=
  (contDiff_norm_sq 𝕜).contDiffAt.comp_contDiffWithinAt x hf

nonrec theorem ContDiffAt.norm_sq (hf : ContDiffAt Real n f x) : ContDiffAt Real n (‖f ·‖ ^ 2) x :=
  hf.norm_sq 𝕜

/--
theorem `contDiffAt_norm` / 定理 `contDiffAt_norm`

English:
theorem contDiffAt_norm
  given: {x : E} (hx : x != 0)
  statement: ContDiffAt Real n norm x
  proof: by
  have : ‖id x‖ ^ 2 != 0 := pow_ne_zero 2 (norm_pos_iff.2 hx).ne'
  simpa only [id, sqrt_sq, norm_nonneg] using (contDiffAt_id.norm_sq 𝕜).sqrt this

中文:
定理 contDiffAt_norm
  条件: {x : E} (hx : x != 0)
  结论: ContDiffAt 实数 n norm x
  证明: by
  have : ‖id x‖ ^ 2 != 0 := pow_ne_zero 2 (norm_pos_iff.2 hx).ne'
  simpa only [id, sqrt_sq, norm_nonneg] using (contDiffAt_id.norm_sq 𝕜).sqrt this

Depends on / 依赖: contDiffAt_id, contDiffAt_id.norm_sq, norm_nonneg, norm_pos_iff, norm_sq, pow_ne_zero, sqrt_sq
-/
theorem contDiffAt_norm {x : E} (hx : x != 0) : ContDiffAt Real n norm x := by
  have : ‖id x‖ ^ 2 != 0 := pow_ne_zero 2 (norm_pos_iff.2 hx).ne'
  simpa only [id, sqrt_sq, norm_nonneg] using (contDiffAt_id.norm_sq 𝕜).sqrt this

/--
theorem `ContDiffAt.norm` / 定理 `ContDiffAt.norm`

English:
theorem ContDiffAt.norm
  given: (hf : ContDiffAt Real n f x) (h0 : f x != 0)
  proof: (contDiffAt_norm 𝕜 h0).comp x hf

中文:
定理 ContDiffAt.norm
  条件: (hf : ContDiffAt 实数 n f x) (h0 : f x != 0)
  证明: (contDiffAt_norm 𝕜 h0).comp x hf

Depends on / 依赖: contDiffAt_norm
-/
theorem ContDiffAt.norm (hf : ContDiffAt Real n f x) (h0 : f x != 0) :
    ContDiffAt Real n (fun y => ‖f y‖) x :=
  (contDiffAt_norm 𝕜 h0).comp x hf

/--
theorem `ContDiffAt.dist` / 定理 `ContDiffAt.dist`

English:
theorem ContDiffAt.dist
  given: (hf : ContDiffAt Real n f x) (hg : ContDiffAt Real n g x) (hne : f x != g x)
  proof: by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)

中文:
定理 ContDiffAt.dist
  条件: (hf : ContDiffAt 实数 n f x) (hg : ContDiffAt 实数 n g x) (hne : f x != g x)
  证明: by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)

Depends on / 依赖: dist_eq_norm, hf.sub, sub_ne_zero
-/
theorem ContDiffAt.dist (hf : ContDiffAt Real n f x) (hg : ContDiffAt Real n g x) (hne : f x != g x) :
    ContDiffAt Real n (fun y => dist (f y) (g y)) x := by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)

/--
theorem `ContDiffWithinAt.norm` / 定理 `ContDiffWithinAt.norm`

English:
theorem ContDiffWithinAt.norm
  given: (hf : ContDiffWithinAt Real n f s x) (h0 : f x != 0)
  proof: (contDiffAt_norm 𝕜 h0).comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.norm
  条件: (hf : ContDiffWithinAt 实数 n f s x) (h0 : f x != 0)
  证明: (contDiffAt_norm 𝕜 h0).comp_contDiffWithinAt x hf

Depends on / 依赖: comp_contDiffWithinAt, contDiffAt_norm
-/
theorem ContDiffWithinAt.norm (hf : ContDiffWithinAt Real n f s x) (h0 : f x != 0) :
    ContDiffWithinAt Real n (fun y => ‖f y‖) s x :=
  (contDiffAt_norm 𝕜 h0).comp_contDiffWithinAt x hf

/--
theorem `ContDiffWithinAt.dist` / 定理 `ContDiffWithinAt.dist`

English:
theorem ContDiffWithinAt.dist
  statement: (hf : ContDiffWithinAt Real n f s x) (hg : ContDiffWithinAt Real n g s x)
  proof: by
  simp only [dist_eq_norm]; exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)

中文:
定理 ContDiffWithinAt.dist
  结论: (hf : ContDiffWithinAt 实数 n f s x) (hg : ContDiffWithinAt 实数 n g s x)
  证明: by
  simp only [dist_eq_norm]; exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)

Depends on / 依赖: dist_eq_norm, hf.sub, sub_ne_zero
-/
theorem ContDiffWithinAt.dist (hf : ContDiffWithinAt Real n f s x) (hg : ContDiffWithinAt Real n g s x)
    (hne : f x != g x) : ContDiffWithinAt Real n (fun y => dist (f y) (g y)) s x := by
  simp only [dist_eq_norm]; exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)

/--
theorem `ContDiffOn.norm_sq` / 定理 `ContDiffOn.norm_sq`

English:
theorem ContDiffOn.norm_sq
  given: (hf : ContDiffOn Real n f s)
  statement: ContDiffOn Real n (fun y => ‖f y‖ ^ 2) s
  proof: fun x hx => (hf x hx).norm_sq 𝕜

中文:
定理 ContDiffOn.norm_sq
  条件: (hf : ContDiffOn 实数 n f s)
  结论: ContDiffOn 实数 n (fun y => ‖f y‖ ^ 2) s
  证明: fun x hx => (hf x hx).norm_sq 𝕜

Depends on / 依赖: norm_sq
-/
theorem ContDiffOn.norm_sq (hf : ContDiffOn Real n f s) : ContDiffOn Real n (fun y => ‖f y‖ ^ 2) s :=
  fun x hx => (hf x hx).norm_sq 𝕜

/--
theorem `ContDiffOn.norm` / 定理 `ContDiffOn.norm`

English:
theorem ContDiffOn.norm
  given: (hf : ContDiffOn Real n f s) (h0 : forall x in s, f x != 0)
  proof: fun x hx => (hf x hx).norm 𝕜 (h0 x hx)

中文:
定理 ContDiffOn.norm
  条件: (hf : ContDiffOn 实数 n f s) (h0 : 对任意 x in s, f x != 0)
  证明: fun x hx => (hf x hx).norm 𝕜 (h0 x hx)
-/
theorem ContDiffOn.norm (hf : ContDiffOn Real n f s) (h0 : forall x in s, f x != 0) :
    ContDiffOn Real n (fun y => ‖f y‖) s := fun x hx => (hf x hx).norm 𝕜 (h0 x hx)

/--
theorem `ContDiffOn.dist` / 定理 `ContDiffOn.dist`

English:
theorem ContDiffOn.dist
  statement: (hf : ContDiffOn Real n f s) (hg : ContDiffOn Real n g s)
  proof: fun x hx =>
  (hf x hx).dist 𝕜 (hg x hx) (hne x hx)

中文:
定理 ContDiffOn.dist
  结论: (hf : ContDiffOn 实数 n f s) (hg : ContDiffOn 实数 n g s)
  证明: fun x hx =>
  (hf x hx).dist 𝕜 (hg x hx) (hne x hx)
-/
theorem ContDiffOn.dist (hf : ContDiffOn Real n f s) (hg : ContDiffOn Real n g s)
    (hne : forall x in s, f x != g x) : ContDiffOn Real n (fun y => dist (f y) (g y)) s := fun x hx =>
  (hf x hx).dist 𝕜 (hg x hx) (hne x hx)

/--
theorem `ContDiff.norm` / 定理 `ContDiff.norm`

English:
theorem ContDiff.norm
  given: (hf : ContDiff Real n f) (h0 : forall x, f x != 0)
  statement: ContDiff Real n fun y => ‖f y‖
  proof: contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.norm 𝕜 (h0 x)

中文:
定理 连续可微.norm
  条件: (hf : 连续可微 实数 n f) (h0 : 对任意 x, f x != 0)
  结论: 连续可微 实数 n fun y => ‖f y‖
  证明: contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.norm 𝕜 (h0 x)

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, hf.contDiffAt.norm
-/
theorem ContDiff.norm (hf : ContDiff Real n f) (h0 : forall x, f x != 0) : ContDiff Real n fun y => ‖f y‖ :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.norm 𝕜 (h0 x)

/--
theorem `ContDiff.dist` / 定理 `ContDiff.dist`

English:
theorem ContDiff.dist
  given: (hf : ContDiff Real n f) (hg : ContDiff Real n g) (hne : forall x, f x != g x)
  proof: contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.dist 𝕜 hg.contDiffAt (hne x)

中文:
定理 连续可微.dist
  条件: (hf : 连续可微 实数 n f) (hg : 连续可微 实数 n g) (hne : 对任意 x, f x != g x)
  证明: contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.dist 𝕜 hg.contDiffAt (hne x)

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, hf.contDiffAt.dist, hg.contDiffAt
-/
theorem ContDiff.dist (hf : ContDiff Real n f) (hg : ContDiff Real n g) (hne : forall x, f x != g x) :
    ContDiff Real n fun y => dist (f y) (g y) :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.dist 𝕜 hg.contDiffAt (hne x)

end

section
open scoped RealInnerProductSpace

/--
theorem `hasStrictFDerivAt_norm_sq` / 定理 `hasStrictFDerivAt_norm_sq`

English:
theorem hasStrictFDerivAt_norm_sq
  given: (x : F)
  proof: by
  simp only [sq, ← @inner_self_eq_norm_mul_norm Real]
  convert! (hasStrictFDerivAt_id x).inner Real (hasStrictFDerivAt_id x)
  ext y
  simp [two_smul, real_inner_comm]

@[simp]

中文:
定理 hasStrictFDerivAt_norm_sq
  条件: (x : F)
  证明: by
  simp only [sq, ← @inner_self_eq_norm_mul_norm Real]
  convert! (hasStrictFDerivAt_id x).inner Real (hasStrictFDerivAt_id x)
  ext y
  simp [two_smul, real_inner_comm]

@[simp]

Depends on / 依赖: convert, hasStrictFDerivAt_id, inner_self_eq_norm_mul_norm, real_inner_comm, two_smul
-/
theorem hasStrictFDerivAt_norm_sq (x : F) :
    HasStrictFDerivAt (fun x => ‖x‖ ^ 2) (2 • (innerSL Real x)) x := by
  simp only [sq, ← @inner_self_eq_norm_mul_norm Real]
  convert! (hasStrictFDerivAt_id x).inner Real (hasStrictFDerivAt_id x)
  ext y
  simp [two_smul, real_inner_comm]

@[simp]
/--
theorem `fderiv_norm_sq_apply` / 定理 `fderiv_norm_sq_apply`

English:
theorem fderiv_norm_sq_apply
  given: (x : F)
  statement: fderiv Real (fun (x : F) => ‖x‖ ^ 2) x = 2 • innerSL Real x
  proof: (hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv

中文:
定理 fderiv_norm_sq_apply
  条件: (x : F)
  结论: fderiv 实数 (fun (x : F) => ‖x‖ ^ 2) x = 2 • innerSL 实数 x
  证明: (hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hasFDerivAt.fderiv, hasStrictFDerivAt_norm_sq
-/
theorem fderiv_norm_sq_apply (x : F) : fderiv Real (fun (x : F) => ‖x‖ ^ 2) x = 2 • innerSL Real x :=
  (hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv

/--
theorem `fderiv_norm_sq` / 定理 `fderiv_norm_sq`

English:
theorem fderiv_norm_sq
  statement: fderiv Real (fun (x : F) => ‖x‖ ^ 2) = 2 • (innerSL Real (E := F))
  proof: by
  ext1; simp

中文:
定理 fderiv_norm_sq
  结论: fderiv 实数 (fun (x : F) => ‖x‖ ^ 2) = 2 • (innerSL 实数 (E := F))
  证明: by
  ext1; simp
-/
theorem fderiv_norm_sq : fderiv Real (fun (x : F) => ‖x‖ ^ 2) = 2 • (innerSL Real (E := F)) := by
  ext1; simp

/--
theorem `HasFDerivAt.norm_sq` / 定理 `HasFDerivAt.norm_sq`

English:
theorem HasFDerivAt.norm_sq
  given: {f : G -> F} {f' : G ->L[Real] F} (hf : HasFDerivAt f f' x)
  proof: (hasStrictFDerivAt_norm_sq _).hasFDerivAt.comp x hf

中文:
定理 在点处Fréchet可导.norm_sq
  条件: {f : G -> F} {f' : G ->L[实数] F} (hf : 在点处Fréchet可导 f f' x)
  证明: (hasStrictFDerivAt_norm_sq _).hasFDerivAt.comp x hf

Depends on / 依赖: hasFDerivAt, hasFDerivAt.comp, hasStrictFDerivAt_norm_sq
-/
theorem HasFDerivAt.norm_sq {f : G -> F} {f' : G ->L[Real] F} (hf : HasFDerivAt f f' x) :
    HasFDerivAt (‖f ·‖ ^ 2) (2 • (innerSL Real (f x)).comp f') x :=
  (hasStrictFDerivAt_norm_sq _).hasFDerivAt.comp x hf

/--
theorem `HasDerivAt.norm_sq` / 定理 `HasDerivAt.norm_sq`

English:
theorem HasDerivAt.norm_sq
  given: {f : Real -> F} {f' : F} {x : Real} (hf : HasDerivAt f f' x)
  proof: by
  simpa using hf.hasFDerivAt.norm_sq.hasDerivAt

中文:
定理 在点处可导.norm_sq
  条件: {f : 实数 -> F} {f' : F} {x : 实数} (hf : 在点处可导 f f' x)
  证明: by
  simpa using hf.hasFDerivAt.norm_sq.hasDerivAt

Depends on / 依赖: hasDerivAt, hasFDerivAt, hf.hasFDerivAt.norm_sq.hasDerivAt, norm_sq
-/
theorem HasDerivAt.norm_sq {f : Real -> F} {f' : F} {x : Real} (hf : HasDerivAt f f' x) :
    HasDerivAt (‖f ·‖ ^ 2) (2 * ⟪f x, f'⟫) x := by
  simpa using hf.hasFDerivAt.norm_sq.hasDerivAt

/--
theorem `HasFDerivWithinAt.norm_sq` / 定理 `HasFDerivWithinAt.norm_sq`

English:
theorem HasFDerivWithinAt.norm_sq
  given: {f : G -> F} {f' : G ->L[Real] F} (hf : HasFDerivWithinAt f f' s x)
  proof: (hasStrictFDerivAt_norm_sq _).hasFDerivAt.comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.norm_sq
  条件: {f : G -> F} {f' : G ->L[实数] F} (hf : HasFDerivWithinAt f f' s x)
  证明: (hasStrictFDerivAt_norm_sq _).hasFDerivAt.comp_hasFDerivWithinAt x hf

Depends on / 依赖: comp_hasFDerivWithinAt, hasFDerivAt, hasFDerivAt.comp_hasFDerivWithinAt, hasStrictFDerivAt_norm_sq
-/
theorem HasFDerivWithinAt.norm_sq {f : G -> F} {f' : G ->L[Real] F} (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (‖f ·‖ ^ 2) (2 • (innerSL Real (f x)).comp f') s x :=
  (hasStrictFDerivAt_norm_sq _).hasFDerivAt.comp_hasFDerivWithinAt x hf

/--
theorem `HasDerivWithinAt.norm_sq` / 定理 `HasDerivWithinAt.norm_sq`

English:
theorem HasDerivWithinAt.norm_sq
  statement: {f : Real -> F} {f' : F} {s : Set Real} {x : Real}
  proof: by
  simpa using hf.hasFDerivWithinAt.norm_sq.hasDerivWithinAt

中文:
定理 HasDerivWithinAt.norm_sq
  结论: {f : 实数 -> F} {f' : F} {s : 集合 实数} {x : 实数}
  证明: by
  simpa using hf.hasFDerivWithinAt.norm_sq.hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.norm_sq.hasDerivWithinAt, norm_sq
-/
theorem HasDerivWithinAt.norm_sq {f : Real -> F} {f' : F} {s : Set Real} {x : Real}
    (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (‖f ·‖ ^ 2) (2 * ⟪f x, f'⟫) s x := by
  simpa using hf.hasFDerivWithinAt.norm_sq.hasDerivWithinAt

end

section
include 𝕜

/--
theorem `DifferentiableAt.norm_sq` / 定理 `DifferentiableAt.norm_sq`

English:
theorem DifferentiableAt.norm_sq
  given: (hf : DifferentiableAt Real f x)
  proof: ((contDiffAt_id.norm_sq 𝕜).differentiableAt one_ne_zero).comp x hf

中文:
定理 DifferentiableAt.norm_sq
  条件: (hf : DifferentiableAt 实数 f x)
  证明: ((contDiffAt_id.norm_sq 𝕜).differentiableAt one_ne_zero).comp x hf

Depends on / 依赖: contDiffAt_id, contDiffAt_id.norm_sq, differentiableAt, norm_sq, one_ne_zero
-/
theorem DifferentiableAt.norm_sq (hf : DifferentiableAt Real f x) :
    DifferentiableAt Real (fun y => ‖f y‖ ^ 2) x :=
  ((contDiffAt_id.norm_sq 𝕜).differentiableAt one_ne_zero).comp x hf

/--
theorem `DifferentiableAt.norm` / 定理 `DifferentiableAt.norm`

English:
theorem DifferentiableAt.norm
  given: (hf : DifferentiableAt Real f x) (h0 : f x != 0)
  proof: ((contDiffAt_norm 𝕜 h0).differentiableAt one_ne_zero).comp x hf

中文:
定理 DifferentiableAt.norm
  条件: (hf : DifferentiableAt 实数 f x) (h0 : f x != 0)
  证明: ((contDiffAt_norm 𝕜 h0).differentiableAt one_ne_zero).comp x hf

Depends on / 依赖: contDiffAt_norm, differentiableAt, one_ne_zero
-/
theorem DifferentiableAt.norm (hf : DifferentiableAt Real f x) (h0 : f x != 0) :
    DifferentiableAt Real (fun y => ‖f y‖) x :=
  ((contDiffAt_norm 𝕜 h0).differentiableAt one_ne_zero).comp x hf

/--
theorem `DifferentiableAt.dist` / 定理 `DifferentiableAt.dist`

English:
theorem DifferentiableAt.dist
  statement: (hf : DifferentiableAt Real f x) (hg : DifferentiableAt Real g x)
  proof: by
  simp only [dist_eq_norm]; exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)

中文:
定理 DifferentiableAt.dist
  结论: (hf : DifferentiableAt 实数 f x) (hg : DifferentiableAt 实数 g x)
  证明: by
  simp only [dist_eq_norm]; exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)

Depends on / 依赖: dist_eq_norm, hf.sub, sub_ne_zero
-/
theorem DifferentiableAt.dist (hf : DifferentiableAt Real f x) (hg : DifferentiableAt Real g x)
    (hne : f x != g x) : DifferentiableAt Real (fun y => dist (f y) (g y)) x := by
  simp only [dist_eq_norm]; exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)

/--
theorem `Differentiable.norm_sq` / 定理 `Differentiable.norm_sq`

English:
theorem Differentiable.norm_sq
  given: (hf : Differentiable Real f)
  statement: Differentiable Real fun y => ‖f y‖ ^ 2
  proof: fun x => (hf x).norm_sq 𝕜

中文:
定理 可微.norm_sq
  条件: (hf : 可微 实数 f)
  结论: 可微 实数 fun y => ‖f y‖ ^ 2
  证明: fun x => (hf x).norm_sq 𝕜

Depends on / 依赖: norm_sq
-/
theorem Differentiable.norm_sq (hf : Differentiable Real f) : Differentiable Real fun y => ‖f y‖ ^ 2 :=
  fun x => (hf x).norm_sq 𝕜

/--
theorem `Differentiable.norm` / 定理 `Differentiable.norm`

English:
theorem Differentiable.norm
  given: (hf : Differentiable Real f) (h0 : forall x, f x != 0)
  proof: fun x => (hf x).norm 𝕜 (h0 x)

中文:
定理 可微.norm
  条件: (hf : 可微 实数 f) (h0 : 对任意 x, f x != 0)
  证明: fun x => (hf x).norm 𝕜 (h0 x)
-/
theorem Differentiable.norm (hf : Differentiable Real f) (h0 : forall x, f x != 0) :
    Differentiable Real fun y => ‖f y‖ := fun x => (hf x).norm 𝕜 (h0 x)

/--
theorem `Differentiable.dist` / 定理 `Differentiable.dist`

English:
theorem Differentiable.dist
  statement: (hf : Differentiable Real f) (hg : Differentiable Real g)
  proof: fun x =>
  (hf x).dist 𝕜 (hg x) (hne x)

中文:
定理 可微.dist
  结论: (hf : 可微 实数 f) (hg : 可微 实数 g)
  证明: fun x =>
  (hf x).dist 𝕜 (hg x) (hne x)
-/
theorem Differentiable.dist (hf : Differentiable Real f) (hg : Differentiable Real g)
    (hne : forall x, f x != g x) : Differentiable Real fun y => dist (f y) (g y) := fun x =>
  (hf x).dist 𝕜 (hg x) (hne x)

/--
theorem `DifferentiableWithinAt.norm_sq` / 定理 `DifferentiableWithinAt.norm_sq`

English:
theorem DifferentiableWithinAt.norm_sq
  given: (hf : DifferentiableWithinAt Real f s x)
  proof: ((contDiffAt_id.norm_sq 𝕜).differentiableAt one_ne_zero).comp_differentiableWithinAt x hf

中文:
定理 DifferentiableWithinAt.norm_sq
  条件: (hf : DifferentiableWithinAt 实数 f s x)
  证明: ((contDiffAt_id.norm_sq 𝕜).differentiableAt one_ne_zero).comp_differentiableWithinAt x hf

Depends on / 依赖: comp_differentiableWithinAt, contDiffAt_id, contDiffAt_id.norm_sq, differentiableAt, norm_sq, one_ne_zero
-/
theorem DifferentiableWithinAt.norm_sq (hf : DifferentiableWithinAt Real f s x) :
    DifferentiableWithinAt Real (fun y => ‖f y‖ ^ 2) s x :=
  ((contDiffAt_id.norm_sq 𝕜).differentiableAt one_ne_zero).comp_differentiableWithinAt x hf

/--
theorem `DifferentiableWithinAt.norm` / 定理 `DifferentiableWithinAt.norm`

English:
theorem DifferentiableWithinAt.norm
  given: (hf : DifferentiableWithinAt Real f s x) (h0 : f x != 0)
  proof: ((contDiffAt_id.norm 𝕜 h0).differentiableAt one_ne_zero).comp_differentiableWithinAt x hf

中文:
定理 DifferentiableWithinAt.norm
  条件: (hf : DifferentiableWithinAt 实数 f s x) (h0 : f x != 0)
  证明: ((contDiffAt_id.norm 𝕜 h0).differentiableAt one_ne_zero).comp_differentiableWithinAt x hf

Depends on / 依赖: comp_differentiableWithinAt, contDiffAt_id, contDiffAt_id.norm, differentiableAt, one_ne_zero
-/
theorem DifferentiableWithinAt.norm (hf : DifferentiableWithinAt Real f s x) (h0 : f x != 0) :
    DifferentiableWithinAt Real (fun y => ‖f y‖) s x :=
  ((contDiffAt_id.norm 𝕜 h0).differentiableAt one_ne_zero).comp_differentiableWithinAt x hf

/--
theorem `DifferentiableWithinAt.dist` / 定理 `DifferentiableWithinAt.dist`

English:
theorem DifferentiableWithinAt.dist
  statement: (hf : DifferentiableWithinAt Real f s x)
  proof: by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)

中文:
定理 DifferentiableWithinAt.dist
  结论: (hf : DifferentiableWithinAt 实数 f s x)
  证明: by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)

Depends on / 依赖: dist_eq_norm, hf.sub, sub_ne_zero
-/
theorem DifferentiableWithinAt.dist (hf : DifferentiableWithinAt Real f s x)
    (hg : DifferentiableWithinAt Real g s x) (hne : f x != g x) :
    DifferentiableWithinAt Real (fun y => dist (f y) (g y)) s x := by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)

/--
theorem `DifferentiableOn.norm_sq` / 定理 `DifferentiableOn.norm_sq`

English:
theorem DifferentiableOn.norm_sq
  given: (hf : DifferentiableOn Real f s)
  proof: fun x hx => (hf x hx).norm_sq 𝕜

中文:
定理 DifferentiableOn.norm_sq
  条件: (hf : DifferentiableOn 实数 f s)
  证明: fun x hx => (hf x hx).norm_sq 𝕜

Depends on / 依赖: norm_sq
-/
theorem DifferentiableOn.norm_sq (hf : DifferentiableOn Real f s) :
    DifferentiableOn Real (fun y => ‖f y‖ ^ 2) s := fun x hx => (hf x hx).norm_sq 𝕜

/--
theorem `DifferentiableOn.norm` / 定理 `DifferentiableOn.norm`

English:
theorem DifferentiableOn.norm
  given: (hf : DifferentiableOn Real f s) (h0 : forall x in s, f x != 0)
  proof: fun x hx => (hf x hx).norm 𝕜 (h0 x hx)

中文:
定理 DifferentiableOn.norm
  条件: (hf : DifferentiableOn 实数 f s) (h0 : 对任意 x in s, f x != 0)
  证明: fun x hx => (hf x hx).norm 𝕜 (h0 x hx)
-/
theorem DifferentiableOn.norm (hf : DifferentiableOn Real f s) (h0 : forall x in s, f x != 0) :
    DifferentiableOn Real (fun y => ‖f y‖) s := fun x hx => (hf x hx).norm 𝕜 (h0 x hx)

/--
theorem `DifferentiableOn.dist` / 定理 `DifferentiableOn.dist`

English:
theorem DifferentiableOn.dist
  statement: (hf : DifferentiableOn Real f s) (hg : DifferentiableOn Real g s)
  proof: fun x hx =>
  (hf x hx).dist 𝕜 (hg x hx) (hne x hx)

中文:
定理 DifferentiableOn.dist
  结论: (hf : DifferentiableOn 实数 f s) (hg : DifferentiableOn 实数 g s)
  证明: fun x hx =>
  (hf x hx).dist 𝕜 (hg x hx) (hne x hx)
-/
theorem DifferentiableOn.dist (hf : DifferentiableOn Real f s) (hg : DifferentiableOn Real g s)
    (hne : forall x in s, f x != g x) : DifferentiableOn Real (fun y => dist (f y) (g y)) s := fun x hx =>
  (hf x hx).dist 𝕜 (hg x hx) (hne x hx)

end

end DerivInner

section PiLike

/-! ### Convenience aliases of `PiLp` lemmas for `EuclideanSpace` -/

open ContinuousLinearMap

variable {𝕜 ι H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {f : H -> EuclideanSpace 𝕜 ι} {f' : H ->L[𝕜] EuclideanSpace 𝕜 ι} {t : Set H} {y : H}

section finite

variable [Finite ι]

/--
theorem `differentiableWithinAt_euclidean` / 定理 `differentiableWithinAt_euclidean`

English:
theorem differentiableWithinAt_euclidean
  proof: differentiableWithinAt_piLp _

中文:
定理 differentiableWithinAt_euclidean
  证明: differentiableWithinAt_piLp _

Depends on / 依赖: differentiableWithinAt_piLp
-/
theorem differentiableWithinAt_euclidean :
    DifferentiableWithinAt 𝕜 f t y ↔ forall i, DifferentiableWithinAt 𝕜 (fun x => f x i) t y :=
  differentiableWithinAt_piLp _

/--
theorem `differentiableAt_euclidean` / 定理 `differentiableAt_euclidean`

English:
theorem differentiableAt_euclidean
  proof: differentiableAt_piLp _

中文:
定理 differentiableAt_euclidean
  证明: differentiableAt_piLp _

Depends on / 依赖: differentiableAt_piLp
-/
theorem differentiableAt_euclidean :
    DifferentiableAt 𝕜 f y ↔ forall i, DifferentiableAt 𝕜 (fun x => f x i) y :=
  differentiableAt_piLp _

/--
theorem `differentiableOn_euclidean` / 定理 `differentiableOn_euclidean`

English:
theorem differentiableOn_euclidean
  proof: differentiableOn_piLp _

中文:
定理 differentiableOn_euclidean
  证明: differentiableOn_piLp _

Depends on / 依赖: differentiableOn_piLp
-/
theorem differentiableOn_euclidean :
    DifferentiableOn 𝕜 f t ↔ forall i, DifferentiableOn 𝕜 (fun x => f x i) t :=
  differentiableOn_piLp _

/--
theorem `differentiable_euclidean` / 定理 `differentiable_euclidean`

English:
theorem differentiable_euclidean
  statement: Differentiable 𝕜 f ↔ forall i, Differentiable 𝕜 fun x => f x i
  proof: differentiable_piLp _

中文:
定理 differentiable_euclidean
  结论: 可微 𝕜 f ↔ 对任意 i, 可微 𝕜 fun x => f x i
  证明: differentiable_piLp _

Depends on / 依赖: differentiable_piLp
-/
theorem differentiable_euclidean : Differentiable 𝕜 f ↔ forall i, Differentiable 𝕜 fun x => f x i :=
  differentiable_piLp _

/--
theorem `hasStrictFDerivAt_euclidean` / 定理 `hasStrictFDerivAt_euclidean`

English:
theorem hasStrictFDerivAt_euclidean
  proof: hasStrictFDerivAt_piLp _

中文:
定理 hasStrictFDerivAt_euclidean
  证明: hasStrictFDerivAt_piLp _

Depends on / 依赖: hasStrictFDerivAt_piLp
-/
theorem hasStrictFDerivAt_euclidean :
    HasStrictFDerivAt f f' y ↔
      forall i, HasStrictFDerivAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') y :=
  hasStrictFDerivAt_piLp _

/--
theorem `hasFDerivWithinAt_euclidean` / 定理 `hasFDerivWithinAt_euclidean`

English:
theorem hasFDerivWithinAt_euclidean
  proof: hasFDerivWithinAt_piLp _

中文:
定理 hasFDerivWithinAt_euclidean
  证明: hasFDerivWithinAt_piLp _

Depends on / 依赖: hasFDerivWithinAt_piLp
-/
theorem hasFDerivWithinAt_euclidean :
    HasFDerivWithinAt f f' t y ↔
      forall i, HasFDerivWithinAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') t y :=
  hasFDerivWithinAt_piLp _

end finite

section fintype

variable [Fintype ι]

/--
theorem `contDiffWithinAt_euclidean` / 定理 `contDiffWithinAt_euclidean`

English:
theorem contDiffWithinAt_euclidean
  given: {n : WithTop Nat∞}
  proof: contDiffWithinAt_piLp _

中文:
定理 contDiffWithinAt_euclidean
  条件: {n : WithTop 自然数∞}
  证明: contDiffWithinAt_piLp _

Depends on / 依赖: contDiffWithinAt_piLp
-/
theorem contDiffWithinAt_euclidean {n : WithTop Nat∞} :
    ContDiffWithinAt 𝕜 n f t y ↔ forall i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y :=
  contDiffWithinAt_piLp _

/--
theorem `contDiffAt_euclidean` / 定理 `contDiffAt_euclidean`

English:
theorem contDiffAt_euclidean
  given: {n : WithTop Nat∞}
  proof: contDiffAt_piLp _

中文:
定理 contDiffAt_euclidean
  条件: {n : WithTop 自然数∞}
  证明: contDiffAt_piLp _

Depends on / 依赖: contDiffAt_piLp
-/
theorem contDiffAt_euclidean {n : WithTop Nat∞} :
    ContDiffAt 𝕜 n f y ↔ forall i, ContDiffAt 𝕜 n (fun x => f x i) y :=
  contDiffAt_piLp _

/--
theorem `contDiffOn_euclidean` / 定理 `contDiffOn_euclidean`

English:
theorem contDiffOn_euclidean
  given: {n : WithTop Nat∞}
  proof: contDiffOn_piLp _

中文:
定理 contDiffOn_euclidean
  条件: {n : WithTop 自然数∞}
  证明: contDiffOn_piLp _

Depends on / 依赖: contDiffOn_piLp
-/
theorem contDiffOn_euclidean {n : WithTop Nat∞} :
    ContDiffOn 𝕜 n f t ↔ forall i, ContDiffOn 𝕜 n (fun x => f x i) t :=
  contDiffOn_piLp _

/--
theorem `contDiff_euclidean` / 定理 `contDiff_euclidean`

English:
theorem contDiff_euclidean
  given: {n : WithTop Nat∞}
  statement: ContDiff 𝕜 n f ↔ forall i, ContDiff 𝕜 n fun x => f x i
  proof: contDiff_piLp _

中文:
定理 contDiff_euclidean
  条件: {n : WithTop 自然数∞}
  结论: 连续可微 𝕜 n f ↔ 对任意 i, 连续可微 𝕜 n fun x => f x i
  证明: contDiff_piLp _

Depends on / 依赖: contDiff_piLp
-/
theorem contDiff_euclidean {n : WithTop Nat∞} : ContDiff 𝕜 n f ↔ forall i, ContDiff 𝕜 n fun x => f x i :=
  contDiff_piLp _

end fintype

end PiLike

section DiffeomorphUnitBall

open Metric hiding mem_nhds_iff

variable {n : Nat∞} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]

/--
theorem `OpenPartialHomeomorph.contDiff_univUnitBall` / 定理 `OpenPartialHomeomorph.contDiff_univUnitBall`

English:
theorem OpenPartialHomeomorph.contDiff_univUnitBall
  statement: ContDiff Real n (univUnitBall : E -> E)
  proof: by
  suffices ContDiff Real n fun x : E => (√(1 + ‖x‖ ^ 2 : Real))⁻¹ from this.smul contDiff_id
  have h : forall x : E, (0 : Real) < (1 : Real) + ‖x‖ ^ 2 := fun x => by positivity
  refine ContDiff.inv ?_ fun x => Real.sqrt_ne_zero'.mpr (h x)
  exact (contDiff_const.add <| contDiff_norm_sq Real).sqrt fun x => (h x).ne'

中文:
定理 OpenPartialHomeomorph.contDiff_univUnitBall
  结论: 连续可微 实数 n (univUnitBall : E -> E)
  证明: by
  suffices ContDiff Real n fun x : E => (√(1 + ‖x‖ ^ 2 : Real))⁻¹ from this.smul contDiff_id
  have h : forall x : E, (0 : Real) < (1 : Real) + ‖x‖ ^ 2 := fun x => by positivity
  refine ContDiff.inv ?_ fun x => Real.sqrt_ne_zero'.mpr (h x)
  exact (contDiff_const.add <| contDiff_norm_sq Real).sqrt fun x => (h x).ne'

Depends on / 依赖: ContDiff, ContDiff.inv, Real.sqrt_ne_zero, contDiff_const, contDiff_const.add, contDiff_id, contDiff_norm_sq, sqrt_ne_zero, this.smul
-/
theorem OpenPartialHomeomorph.contDiff_univUnitBall : ContDiff Real n (univUnitBall : E -> E) := by
  suffices ContDiff Real n fun x : E => (√(1 + ‖x‖ ^ 2 : Real))⁻¹ from this.smul contDiff_id
  have h : forall x : E, (0 : Real) < (1 : Real) + ‖x‖ ^ 2 := fun x => by positivity
  refine ContDiff.inv ?_ fun x => Real.sqrt_ne_zero'.mpr (h x)
  exact (contDiff_const.add <| contDiff_norm_sq Real).sqrt fun x => (h x).ne'

/--
theorem `OpenPartialHomeomorph.contDiffOn_univUnitBall_symm` / 定理 `OpenPartialHomeomorph.contDiffOn_univUnitBall_symm`

English:
theorem OpenPartialHomeomorph.contDiffOn_univUnitBall_symm
  proof: fun y hy => by
  apply ContDiffAt.contDiffWithinAt
  suffices ContDiffAt Real n (fun y : E => (√(1 - ‖y‖ ^ 2 : Real))⁻¹) y from this.smul contDiffAt_id
  have h : (0 : Real) < (1 : Real) - ‖(y : E)‖ ^ 2 := by
    rwa [mem_ball_zero_iff, ← _root_.abs_one, ← abs_norm, ← sq_lt_sq, one_pow, ← sub_pos] at hy
  refine ContDiffAt.inv ?_ (Real.sqrt_ne_zero'.mpr h)
  change ContDiffAt Real n ((fun y => √(y)) ∘ fun y => (1 - ‖y‖ ^ 2)) y
  refine (contDiffAt_sqrt h.ne').comp y ?_
  exact contDiffAt_const.sub (contDiff_norm_sq Real).contDiffAt

中文:
定理 OpenPartialHomeomorph.contDiffOn_univUnitBall_symm
  证明: fun y hy => by
  apply ContDiffAt.contDiffWithinAt
  suffices ContDiffAt Real n (fun y : E => (√(1 - ‖y‖ ^ 2 : Real))⁻¹) y from this.smul contDiffAt_id
  have h : (0 : Real) < (1 : Real) - ‖(y : E)‖ ^ 2 := by
    rwa [mem_ball_zero_iff, ← _root_.abs_one, ← abs_norm, ← sq_lt_sq, one_pow, ← sub_pos] at hy
  refine ContDiffAt.inv ?_ (Real.sqrt_ne_zero'.mpr h)
  change ContDiffAt Real n ((fun y => √(y)) ∘ fun y => (1 - ‖y‖ ^ 2)) y
  refine (contDiffAt_sqrt h.ne').comp y ?_
  exact contDiffAt_const.sub (contDiff_norm_sq Real).contDiffAt

Depends on / 依赖: ContDiffAt, ContDiffAt.contDiffWithinAt, ContDiffAt.inv, Real.sqrt_ne_zero, _root_, _root_.abs_one, abs_norm, abs_one, contDiffAt_const, contDiffAt_const.sub, contDiffAt_id, contDiffAt_sqrt, contDiffWithinAt, contDiff_norm_, h.ne, mem_ball_zero_iff, one_pow, sq_lt_sq, sqrt_ne_zero, sub_pos
-/
theorem OpenPartialHomeomorph.contDiffOn_univUnitBall_symm :
    ContDiffOn Real n univUnitBall.symm (ball (0 : E) 1) := fun y hy => by
  apply ContDiffAt.contDiffWithinAt
  suffices ContDiffAt Real n (fun y : E => (√(1 - ‖y‖ ^ 2 : Real))⁻¹) y from this.smul contDiffAt_id
  have h : (0 : Real) < (1 : Real) - ‖(y : E)‖ ^ 2 := by
    rwa [mem_ball_zero_iff, ← _root_.abs_one, ← abs_norm, ← sq_lt_sq, one_pow, ← sub_pos] at hy
  refine ContDiffAt.inv ?_ (Real.sqrt_ne_zero'.mpr h)
  change ContDiffAt Real n ((fun y => √(y)) ∘ fun y => (1 - ‖y‖ ^ 2)) y
  refine (contDiffAt_sqrt h.ne').comp y ?_
  exact contDiffAt_const.sub (contDiff_norm_sq Real).contDiffAt

/--
theorem `Homeomorph.contDiff_unitBall` / 定理 `Homeomorph.contDiff_unitBall`

English:
theorem Homeomorph.contDiff_unitBall
  statement: ContDiff Real n fun x : E => (unitBall x : E)
  proof: OpenPartialHomeomorph.contDiff_univUnitBall

中文:
定理 同胚.contDiff_unitBall
  结论: 连续可微 实数 n fun x : E => (unitBall x : E)
  证明: OpenPartialHomeomorph.contDiff_univUnitBall

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.contDiff_univUnitBall, contDiff_univUnitBall
-/
theorem Homeomorph.contDiff_unitBall : ContDiff Real n fun x : E => (unitBall x : E) :=
  OpenPartialHomeomorph.contDiff_univUnitBall

namespace OpenPartialHomeomorph

variable {c : E} {r : Real}

/--
theorem `contDiff_unitBallBall` / 定理 `contDiff_unitBallBall`

English:
theorem contDiff_unitBallBall
  given: (hr : 0 < r)
  statement: ContDiff Real n (unitBallBall c r hr)
  proof: (contDiff_id.const_smul r).add contDiff_const

中文:
定理 contDiff_unitBallBall
  条件: (hr : 0 < r)
  结论: 连续可微 实数 n (unitBallBall c r hr)
  证明: (contDiff_id.const_smul r).add contDiff_const

Depends on / 依赖: const_smul, contDiff_const, contDiff_id, contDiff_id.const_smul
-/
theorem contDiff_unitBallBall (hr : 0 < r) : ContDiff Real n (unitBallBall c r hr) :=
  (contDiff_id.const_smul r).add contDiff_const

/--
theorem `contDiff_unitBallBall_symm` / 定理 `contDiff_unitBallBall_symm`

English:
theorem contDiff_unitBallBall_symm
  given: (hr : 0 < r)
  statement: ContDiff Real n (unitBallBall c r hr).symm
  proof: (contDiff_id.sub contDiff_const).const_smul r⁻¹

中文:
定理 contDiff_unitBallBall_symm
  条件: (hr : 0 < r)
  结论: 连续可微 实数 n (unitBallBall c r hr).symm
  证明: (contDiff_id.sub contDiff_const).const_smul r⁻¹

Depends on / 依赖: const_smul, contDiff_const, contDiff_id, contDiff_id.sub
-/
theorem contDiff_unitBallBall_symm (hr : 0 < r) : ContDiff Real n (unitBallBall c r hr).symm :=
  (contDiff_id.sub contDiff_const).const_smul r⁻¹

/--
theorem `contDiff_univBall` / 定理 `contDiff_univBall`

English:
theorem contDiff_univBall
  statement: ContDiff Real n (univBall c r)
  proof: by
  unfold univBall; split_ifs with h
  · exact (contDiff_unitBallBall h).comp contDiff_univUnitBall
  · exact contDiff_id.add contDiff_const

中文:
定理 contDiff_univBall
  结论: 连续可微 实数 n (univBall c r)
  证明: by
  unfold univBall; split_ifs with h
  · exact (contDiff_unitBallBall h).comp contDiff_univUnitBall
  · exact contDiff_id.add contDiff_const

Depends on / 依赖: contDiff_const, contDiff_id, contDiff_id.add, contDiff_unitBallBall, contDiff_univUnitBall, split_ifs, univBall
-/
theorem contDiff_univBall : ContDiff Real n (univBall c r) := by
  unfold univBall; split_ifs with h
  · exact (contDiff_unitBallBall h).comp contDiff_univUnitBall
  · exact contDiff_id.add contDiff_const

/--
theorem `contDiffOn_univBall_symm` / 定理 `contDiffOn_univBall_symm`

English:
theorem contDiffOn_univBall_symm
  proof: by
  unfold univBall; split_ifs with h
  · refine contDiffOn_univUnitBall_symm.comp (contDiff_unitBallBall_symm h).contDiffOn ?_
    rw [← unitBallBall_source c r h]; rw [← unitBallBall_target c r h]
    apply OpenPartialHomeomorph.mapsTo_symm
  · exact contDiffOn_id.sub contDiffOn_const

中文:
定理 contDiffOn_univBall_symm
  证明: by
  unfold univBall; split_ifs with h
  · refine contDiffOn_univUnitBall_symm.comp (contDiff_unitBallBall_symm h).contDiffOn ?_
    rw [← unitBallBall_source c r h]; rw [← unitBallBall_target c r h]
    apply OpenPartialHomeomorph.mapsTo_symm
  · exact contDiffOn_id.sub contDiffOn_const

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.mapsTo_symm, contDiffOn, contDiffOn_const, contDiffOn_id, contDiffOn_id.sub, contDiffOn_univUnitBall_symm, contDiffOn_univUnitBall_symm.comp, contDiff_unitBallBall_symm, mapsTo_symm, split_ifs, unitBallBall_source, unitBallBall_target, univBall
-/
theorem contDiffOn_univBall_symm :
    ContDiffOn Real n (univBall c r).symm (ball c r) := by
  unfold univBall; split_ifs with h
  · refine contDiffOn_univUnitBall_symm.comp (contDiff_unitBallBall_symm h).contDiffOn ?_
    rw [← unitBallBall_source c r h]; rw [← unitBallBall_target c r h]
    apply OpenPartialHomeomorph.mapsTo_symm
  · exact contDiffOn_id.sub contDiffOn_const

end OpenPartialHomeomorph

end DiffeomorphUnitBall
