/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# One-dimensional iterated derivatives

We define the `n`-th derivative of a function `f : 𝕜 → F` as a function
`iteratedDeriv n f : 𝕜 → F`, as well as a version on domains `iteratedDerivWithin n f s : 𝕜 → F`,
and prove their basic properties.

## Main definitions and results

Let `𝕜` be a nontrivially normed field, and `F` a normed vector space over `𝕜`. Let `f : 𝕜 → F`.

* `iteratedDeriv n f` is the `n`-th derivative of `f`, seen as a function from `𝕜` to `F`.
  It is defined as the `n`-th Fréchet derivative (which is a multilinear map) applied to the
  vector `(1, ..., 1)`, to take advantage of all the existing framework, but we show that it
  coincides with the naive iterative definition.
* `iteratedDeriv_eq_iterate` states that the `n`-th derivative of `f` is obtained by starting
  from `f` and differentiating it `n` times.
* `iteratedDerivWithin n f s` is the `n`-th derivative of `f` within the domain `s`. It only
  behaves well when `s` has the unique derivative property.
* `iteratedDerivWithin_eq_iterate` states that the `n`-th derivative of `f` in the domain `s` is
  obtained by starting from `f` and differentiating it `n` times within `s`. This only holds when
  `s` has the unique derivative property.

## Implementation details

The results are deduced from the corresponding results for the more general (multilinear) iterated
Fréchet derivative. For this, we write `iteratedDeriv n f` as the composition of
`iteratedFDeriv 𝕜 n f` and a continuous linear equiv. As continuous linear equivs respect
differentiability and commute with differentiation, this makes it possible to prove readily that
the derivative of the `n`-th derivative is the `n+1`-th derivative in `iteratedDerivWithin_succ`,
by translating the corresponding result `iteratedFDerivWithin_succ_apply_left` for the
iterated Fréchet derivative.
-/

@[expose] public section

noncomputable section

open scoped Topology ContDiff
open Filter Asymptotics Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/--
Definition of `iteratedDeriv` / `iteratedDeriv` 的定义

English:
definition iteratedDeriv
  signature: (n : Nat) (f : 𝕜 -> F) (x : 𝕜)
  body: (iteratedFDeriv 𝕜 n f x : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1

中文:
定义 iteratedDeriv
  签名: (n : 自然数) (f : 𝕜 -> F) (x : 𝕜)
  定义体: (iteratedFDeriv 𝕜 n f x : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1

Depends on / 依赖: iteratedFDeriv
-/
def iteratedDeriv (n : Nat) (f : 𝕜 -> F) (x : 𝕜) : F :=
  (iteratedFDeriv 𝕜 n f x : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1

/--
Definition of `iteratedDerivWithin` / `iteratedDerivWithin` 的定义

English:
definition iteratedDerivWithin
  signature: (n : Nat) (f : 𝕜 -> F) (s : Set 𝕜) (x : 𝕜)
  body: (iteratedFDerivWithin 𝕜 n f s x : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1

中文:
定义 iteratedDerivWithin
  签名: (n : 自然数) (f : 𝕜 -> F) (s : 集合 𝕜) (x : 𝕜)
  定义体: (iteratedFDerivWithin 𝕜 n f s x : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1

Depends on / 依赖: iteratedFDerivWithin
-/
def iteratedDerivWithin (n : Nat) (f : 𝕜 -> F) (s : Set 𝕜) (x : 𝕜) : F :=
  (iteratedFDerivWithin 𝕜 n f s x : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1

variable {n : Nat} {f : 𝕜 -> F} {s : Set 𝕜} {x : 𝕜}

@[simp]
/--
theorem `iteratedDerivWithin_univ` / 定理 `iteratedDerivWithin_univ`

English:
theorem iteratedDerivWithin_univ
  statement: iteratedDerivWithin n f univ = iteratedDeriv n f
  proof: by
  ext x
  rw [iteratedDerivWithin]; rw [iteratedDeriv]; rw [iteratedFDerivWithin_univ]

中文:
定理 iteratedDerivWithin_univ
  结论: iteratedDerivWithin n f univ = iteratedDeriv n f
  证明: by
  ext x
  rw [iteratedDerivWithin]; rw [iteratedDeriv]; rw [iteratedFDerivWithin_univ]

Depends on / 依赖: iteratedDeriv, iteratedDerivWithin, iteratedFDerivWithin_univ
-/
theorem iteratedDerivWithin_univ : iteratedDerivWithin n f univ = iteratedDeriv n f := by
  ext x
  rw [iteratedDerivWithin]; rw [iteratedDeriv]; rw [iteratedFDerivWithin_univ]

/--
theorem `iteratedDerivWithin_eq_iteratedDeriv` / 定理 `iteratedDerivWithin_eq_iteratedDeriv`

English:
theorem iteratedDerivWithin_eq_iteratedDeriv
  statement: (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x)
  proof: by
  rw [iteratedDerivWithin]; rw [iteratedDeriv]; rw [iteratedFDerivWithin_eq_iteratedFDeriv hs h hx]

中文:
定理 iteratedDerivWithin_eq_iteratedDeriv
  结论: (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x)
  证明: by
  rw [iteratedDerivWithin]; rw [iteratedDeriv]; rw [iteratedFDerivWithin_eq_iteratedFDeriv hs h hx]

Depends on / 依赖: iteratedDeriv, iteratedDerivWithin, iteratedFDerivWithin_eq_iteratedFDeriv
-/
theorem iteratedDerivWithin_eq_iteratedDeriv (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x)
    (hx : x in s) : iteratedDerivWithin n f s x = iteratedDeriv n f x := by
  rw [iteratedDerivWithin]; rw [iteratedDeriv]; rw [iteratedFDerivWithin_eq_iteratedFDeriv hs h hx]



/--
theorem `iteratedDerivWithin_eq_iteratedFDerivWithin` / 定理 `iteratedDerivWithin_eq_iteratedFDerivWithin`

English:
theorem iteratedDerivWithin_eq_iteratedFDerivWithin
  statement: iteratedDerivWithin n f s x =
  proof: rfl

中文:
定理 iteratedDerivWithin_eq_iteratedFDerivWithin
  结论: iteratedDerivWithin n f s x =
  证明: rfl
-/
theorem iteratedDerivWithin_eq_iteratedFDerivWithin : iteratedDerivWithin n f s x =
    (iteratedFDerivWithin 𝕜 n f s x : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1 :=
  rfl

/--
theorem `iteratedDerivWithin_eq_equiv_comp` / 定理 `iteratedDerivWithin_eq_equiv_comp`

English:
theorem iteratedDerivWithin_eq_equiv_comp
  statement: iteratedDerivWithin n f s =
  proof: by
  ext x; rfl

中文:
定理 iteratedDerivWithin_eq_equiv_comp
  结论: iteratedDerivWithin n f s =
  证明: by
  ext x; rfl
-/
theorem iteratedDerivWithin_eq_equiv_comp : iteratedDerivWithin n f s =
    (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).symm ∘ iteratedFDerivWithin 𝕜 n f s := by
  ext x; rfl

/--
theorem `iteratedFDerivWithin_eq_equiv_comp` / 定理 `iteratedFDerivWithin_eq_equiv_comp`

English:
theorem iteratedFDerivWithin_eq_equiv_comp
  proof: by
  rw [iteratedDerivWithin_eq_equiv_comp]; rw [← Function.comp_assoc]; rw [LinearIsometryEquiv.self_comp_symm]; rw [Function.id_comp]

中文:
定理 iteratedFDerivWithin_eq_equiv_comp
  证明: by
  rw [iteratedDerivWithin_eq_equiv_comp]; rw [← Function.comp_assoc]; rw [LinearIsometryEquiv.self_comp_symm]; rw [Function.id_comp]

Depends on / 依赖: Function, Function.comp_assoc, Function.id_comp, LinearIsometryEquiv, LinearIsometryEquiv.self_comp_symm, comp_assoc, id_comp, iteratedDerivWithin_eq_equiv_comp, self_comp_symm
-/
theorem iteratedFDerivWithin_eq_equiv_comp :
    iteratedFDerivWithin 𝕜 n f s =
      ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F ∘ iteratedDerivWithin n f s := by
  rw [iteratedDerivWithin_eq_equiv_comp]; rw [← Function.comp_assoc]; rw [LinearIsometryEquiv.self_comp_symm]; rw [Function.id_comp]

/--
theorem `iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod` / 定理 `iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod`

English:
theorem iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod
  given: {m : Fin n -> 𝕜}
  proof: by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin]; rw [← ContinuousMultilinearMap.map_smul_univ]
  simp

中文:
定理 iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod
  条件: {m : 有限集 n -> 𝕜}
  证明: by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin]; rw [← ContinuousMultilinearMap.map_smul_univ]
  simp

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.map_smul_univ, iteratedDerivWithin_eq_iteratedFDerivWithin, map_smul_univ
-/
theorem iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod {m : Fin n -> 𝕜} :
    (iteratedFDerivWithin 𝕜 n f s x : (Fin n -> 𝕜) -> F) m =
      (∏ i, m i) • iteratedDerivWithin n f s x := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin]; rw [← ContinuousMultilinearMap.map_smul_univ]
  simp

/--
theorem `norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin` / 定理 `norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin`

English:
theorem norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin
  proof: by
  rw [iteratedDerivWithin_eq_equiv_comp]; rw [Function.comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]

中文:
定理 norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin
  证明: by
  rw [iteratedDerivWithin_eq_equiv_comp]; rw [Function.comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, LinearIsometryEquiv, LinearIsometryEquiv.norm_map, comp_apply, iteratedDerivWithin_eq_equiv_comp, norm_map
-/
theorem norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin :
    ‖iteratedFDerivWithin 𝕜 n f s x‖ = ‖iteratedDerivWithin n f s x‖ := by
  rw [iteratedDerivWithin_eq_equiv_comp]; rw [Function.comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]
/--
theorem `iteratedDerivWithin_zero` / 定理 `iteratedDerivWithin_zero`

English:
theorem iteratedDerivWithin_zero
  statement: iteratedDerivWithin 0 f s = f
  proof: by
  ext x
  simp [iteratedDerivWithin]

@[simp]

中文:
定理 iteratedDerivWithin_zero
  结论: iteratedDerivWithin 0 f s = f
  证明: by
  ext x
  simp [iteratedDerivWithin]

@[simp]

Depends on / 依赖: iteratedDerivWithin
-/
theorem iteratedDerivWithin_zero : iteratedDerivWithin 0 f s = f := by
  ext x
  simp [iteratedDerivWithin]

@[simp]
/--
theorem `iteratedDerivWithin_one` / 定理 `iteratedDerivWithin_one`

English:
theorem iteratedDerivWithin_one
  proof: by
  ext x
  by_cases hsx : AccPt x (𝓟 s)
  · simp only [iteratedDerivWithin, iteratedFDerivWithin_one_apply hsx.uniqueDiffWithinAt,
      derivWithin]
  · simp [derivWithin_zero_of_not_accPt hsx, iteratedDerivWithin, iteratedFDerivWithin,
      fderivWithin_zero_of_not_accPt hsx]

中文:
定理 iteratedDerivWithin_one
  证明: by
  ext x
  by_cases hsx : AccPt x (𝓟 s)
  · simp only [iteratedDerivWithin, iteratedFDerivWithin_one_apply hsx.uniqueDiffWithinAt,
      derivWithin]
  · simp [derivWithin_zero_of_not_accPt hsx, iteratedDerivWithin, iteratedFDerivWithin,
      fderivWithin_zero_of_not_accPt hsx]

Depends on / 依赖: derivWithin, derivWithin_zero_of_not_accPt, fderivWithin_zero_of_not_accPt, hsx.uniqueDiffWithinAt, iteratedDerivWithin, iteratedFDerivWithin, iteratedFDerivWithin_one_apply, uniqueDiffWithinAt
-/
theorem iteratedDerivWithin_one :
    iteratedDerivWithin 1 f s = derivWithin f s := by
  ext x
  by_cases hsx : AccPt x (𝓟 s)
  · simp only [iteratedDerivWithin, iteratedFDerivWithin_one_apply hsx.uniqueDiffWithinAt,
      derivWithin]
  · simp [derivWithin_zero_of_not_accPt hsx, iteratedDerivWithin, iteratedFDerivWithin,
      fderivWithin_zero_of_not_accPt hsx]

/--
theorem `contDiffOn_of_continuousOn_differentiableOn_deriv` / 定理 `contDiffOn_of_continuousOn_differentiableOn_deriv`

English:
theorem contDiffOn_of_continuousOn_differentiableOn_deriv
  statement: {n : Nat∞}
  proof: by
  apply contDiffOn_of_continuousOn_differentiableOn
  · simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_continuousOn_iff]
  · simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_differentiableOn_iff]

中文:
定理 contDiffOn_of_continuousOn_differentiableOn_deriv
  结论: {n : 自然数∞}
  证明: by
  apply contDiffOn_of_continuousOn_differentiableOn
  · simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_continuousOn_iff]
  · simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_differentiableOn_iff]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.comp_continuousOn_iff, LinearIsometryEquiv.comp_differentiableOn_iff, comp_continuousOn_iff, comp_differentiableOn_iff, contDiffOn_of_continuousOn_differentiableOn, iteratedFDerivWithin_eq_equiv_comp
-/
theorem contDiffOn_of_continuousOn_differentiableOn_deriv {n : Nat∞}
    (Hcont : forall m : Nat, (m : Nat∞) <= n -> ContinuousOn (fun x => iteratedDerivWithin m f s x) s)
    (Hdiff : forall m : Nat, (m : Nat∞) < n -> DifferentiableOn 𝕜 (fun x => iteratedDerivWithin m f s x) s) :
    ContDiffOn 𝕜 n f s := by
  apply contDiffOn_of_continuousOn_differentiableOn
  · simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_continuousOn_iff]
  · simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_differentiableOn_iff]

/--
theorem `contDiffOn_of_differentiableOn_deriv` / 定理 `contDiffOn_of_differentiableOn_deriv`

English:
theorem contDiffOn_of_differentiableOn_deriv
  statement: {n : Nat∞}
  proof: by
  apply contDiffOn_of_differentiableOn
  simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_differentiableOn_iff]

中文:
定理 contDiffOn_of_differentiableOn_deriv
  结论: {n : 自然数∞}
  证明: by
  apply contDiffOn_of_differentiableOn
  simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_differentiableOn_iff]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.comp_differentiableOn_iff, comp_differentiableOn_iff, contDiffOn_of_differentiableOn, iteratedFDerivWithin_eq_equiv_comp
-/
theorem contDiffOn_of_differentiableOn_deriv {n : Nat∞}
    (h : forall m : Nat, (m : Nat∞) <= n -> DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s) :
    ContDiffOn 𝕜 n f s := by
  apply contDiffOn_of_differentiableOn
  simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_differentiableOn_iff]

/--
theorem `ContDiffOn.continuousOn_iteratedDerivWithin` / 定理 `ContDiffOn.continuousOn_iteratedDerivWithin`

English:
theorem ContDiffOn.continuousOn_iteratedDerivWithin
  proof: by
  simpa only [iteratedDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_continuousOn_iff] using
    h.continuousOn_iteratedFDerivWithin hmn hs

中文:
定理 ContDiffOn.continuousOn_iteratedDerivWithin
  证明: by
  simpa only [iteratedDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_continuousOn_iff] using
    h.continuousOn_iteratedFDerivWithin hmn hs

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.comp_continuousOn_iff, comp_continuousOn_iff, continuousOn_iteratedFDerivWithin, h.continuousOn_iteratedFDerivWithin, iteratedDerivWithin_eq_equiv_comp
-/
theorem ContDiffOn.continuousOn_iteratedDerivWithin
    {n : Nat∞ω} {m : Nat} (h : ContDiffOn 𝕜 n f s)
    (hmn : m <= n) (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iteratedDerivWithin m f s) s := by
  simpa only [iteratedDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_continuousOn_iff] using
    h.continuousOn_iteratedFDerivWithin hmn hs

/--
theorem `ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin` / 定理 `ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin`

English:
theorem ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin
  statement: {n : Nat∞ω} {m : Nat}
  proof: by
  simpa only [iteratedDerivWithin_eq_equiv_comp,
    LinearIsometryEquiv.comp_differentiableWithinAt_iff] using
    h.differentiableWithinAt_iteratedFDerivWithin hmn hs

中文:
定理 ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin
  结论: {n : 自然数∞ω} {m : 自然数}
  证明: by
  simpa only [iteratedDerivWithin_eq_equiv_comp,
    LinearIsometryEquiv.comp_differentiableWithinAt_iff] using
    h.differentiableWithinAt_iteratedFDerivWithin hmn hs

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.comp_differentiableWithinAt_iff, comp_differentiableWithinAt_iff, differentiableWithinAt_iteratedFDerivWithin, h.differentiableWithinAt_iteratedFDerivWithin, iteratedDerivWithin_eq_equiv_comp
-/
theorem ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin {n : Nat∞ω} {m : Nat}
    (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m < n) (hs : UniqueDiffOn 𝕜 (insert x s)) :
    DifferentiableWithinAt 𝕜 (iteratedDerivWithin m f s) s x := by
  simpa only [iteratedDerivWithin_eq_equiv_comp,
    LinearIsometryEquiv.comp_differentiableWithinAt_iff] using
    h.differentiableWithinAt_iteratedFDerivWithin hmn hs

/--
theorem `ContDiffOn.differentiableOn_iteratedDerivWithin` / 定理 `ContDiffOn.differentiableOn_iteratedDerivWithin`

English:
theorem ContDiffOn.differentiableOn_iteratedDerivWithin
  statement: {n : Nat∞ω} {m : Nat}
  proof: fun x hx =>
(h x hx).differentiableWithinAt_iteratedDerivWithin hmn by rwa [insert_eq_of_mem hx]

中文:
定理 ContDiffOn.differentiableOn_iteratedDerivWithin
  结论: {n : 自然数∞ω} {m : 自然数}
  证明: fun x hx =>
(h x hx).differentiableWithinAt_iteratedDerivWithin hmn by rwa [insert_eq_of_mem hx]
-/
theorem ContDiffOn.differentiableOn_iteratedDerivWithin {n : Nat∞ω} {m : Nat}
    (h : ContDiffOn 𝕜 n f s) (hmn : m < n) (hs : UniqueDiffOn 𝕜 s) :
    DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s := fun x hx =>
(h x hx).differentiableWithinAt_iteratedDerivWithin hmn by rwa [insert_eq_of_mem hx]

/--
theorem `contDiffOn_iff_continuousOn_differentiableOn_deriv` / 定理 `contDiffOn_iff_continuousOn_differentiableOn_deriv`

English:
theorem contDiffOn_iff_continuousOn_differentiableOn_deriv
  given: {n : Nat∞} (hs : UniqueDiffOn 𝕜 s)
  proof: by
  simp only [contDiffOn_iff_continuousOn_differentiableOn hs, iteratedFDerivWithin_eq_equiv_comp,
    LinearIsometryEquiv.comp_continuousOn_iff, LinearIsometryEquiv.comp_differentiableOn_iff]

中文:
定理 contDiffOn_iff_continuousOn_differentiableOn_deriv
  条件: {n : 自然数∞} (hs : UniqueDiffOn 𝕜 s)
  证明: by
  simp only [contDiffOn_iff_continuousOn_differentiableOn hs, iteratedFDerivWithin_eq_equiv_comp,
    LinearIsometryEquiv.comp_continuousOn_iff, LinearIsometryEquiv.comp_differentiableOn_iff]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.comp_continuousOn_iff, LinearIsometryEquiv.comp_differentiableOn_iff, comp_continuousOn_iff, comp_differentiableOn_iff, contDiffOn_iff_continuousOn_differentiableOn, iteratedFDerivWithin_eq_equiv_comp
-/
theorem contDiffOn_iff_continuousOn_differentiableOn_deriv {n : Nat∞} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔ (forall m : Nat, (m : Nat∞) <= n -> ContinuousOn (iteratedDerivWithin m f s) s) ∧
      forall m : Nat, (m : Nat∞) < n -> DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s := by
  simp only [contDiffOn_iff_continuousOn_differentiableOn hs, iteratedFDerivWithin_eq_equiv_comp,
    LinearIsometryEquiv.comp_continuousOn_iff, LinearIsometryEquiv.comp_differentiableOn_iff]

/--
theorem `contDiffOn_nat_iff_continuousOn_differentiableOn_deriv` / 定理 `contDiffOn_nat_iff_continuousOn_differentiableOn_deriv`

English:
theorem contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
  given: {n : Nat} (hs : UniqueDiffOn 𝕜 s)
  proof: by
  rw [show n = ((n : Nat∞) : Nat∞ω) from rfl]; rw [contDiffOn_iff_continuousOn_differentiableOn_deriv hs]
  simp

中文:
定理 contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
  条件: {n : 自然数} (hs : UniqueDiffOn 𝕜 s)
  证明: by
  rw [show n = ((n : Nat∞) : Nat∞ω) from rfl]; rw [contDiffOn_iff_continuousOn_differentiableOn_deriv hs]
  simp

Depends on / 依赖: contDiffOn_iff_continuousOn_differentiableOn_deriv
-/
theorem contDiffOn_nat_iff_continuousOn_differentiableOn_deriv {n : Nat} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔ (forall m : Nat, m <= n -> ContinuousOn (iteratedDerivWithin m f s) s) ∧
      forall m : Nat, m < n -> DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s := by
  rw [show n = ((n : Nat∞) : Nat∞ω) from rfl]; rw [contDiffOn_iff_continuousOn_differentiableOn_deriv hs]
  simp

/--
theorem `iteratedDerivWithin_succ` / 定理 `iteratedDerivWithin_succ`

English:
theorem iteratedDerivWithin_succ
  proof: by
  ext x
  by_cases hxs : AccPt x (𝓟 s)
  · rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedFDerivWithin_succ_apply_left,
      iteratedFDerivWithin_eq_equiv_comp,
      LinearIsometryEquiv.comp_fderivWithin _ hxs.uniqueDiffWithinAt, derivWithin]
    change ((ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) ((fderivWithin 𝕜
      (iteratedDerivWithin n f s) s x : 𝕜 -> F) 1) : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1) =
      (fderivWithin 𝕜 (iteratedDerivWithin n f s) s x : 𝕜 -> F) 1
    simp
  · simp [derivWithin_zero_of_not_accPt hxs, iteratedDerivWithin, iteratedFDerivWithin,
      fderivWithin_zero_of_not_accPt hxs]

中文:
定理 iteratedDerivWithin_succ
  证明: by
  ext x
  by_cases hxs : AccPt x (𝓟 s)
  · rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedFDerivWithin_succ_apply_left,
      iteratedFDerivWithin_eq_equiv_comp,
      LinearIsometryEquiv.comp_fderivWithin _ hxs.uniqueDiffWithinAt, derivWithin]
    change ((ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) ((fderivWithin 𝕜
      (iteratedDerivWithin n f s) s x : 𝕜 -> F) 1) : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1) =
      (fderivWithin 𝕜 (iteratedDerivWithin n f s) s x : 𝕜 -> F) 1
    simp
  · simp [derivWithin_zero_of_not_accPt hxs, iteratedDerivWithin, iteratedFDerivWithin,
      fderivWithin_zero_of_not_accPt hxs]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiRing, LinearIsometryEquiv, LinearIsometryEquiv.comp_fderivWithin, comp_fderivWithin, derivWithin, derivWithin_zero_of_not_accPt, fderivWithin, hxs.uniqueDiffWithinAt, iteratedDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedFDerivWithin_eq_equiv_comp, iteratedFDerivWithin_succ_apply_left, mkPiRing, uniqueDiffWithinAt
-/
theorem iteratedDerivWithin_succ :
    iteratedDerivWithin (n + 1) f s = derivWithin (iteratedDerivWithin n f s) s := by
  ext x
  by_cases hxs : AccPt x (𝓟 s)
  · rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedFDerivWithin_succ_apply_left,
      iteratedFDerivWithin_eq_equiv_comp,
      LinearIsometryEquiv.comp_fderivWithin _ hxs.uniqueDiffWithinAt, derivWithin]
    change ((ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) ((fderivWithin 𝕜
      (iteratedDerivWithin n f s) s x : 𝕜 -> F) 1) : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1) =
      (fderivWithin 𝕜 (iteratedDerivWithin n f s) s x : 𝕜 -> F) 1
    simp
  · simp [derivWithin_zero_of_not_accPt hxs, iteratedDerivWithin, iteratedFDerivWithin,
      fderivWithin_zero_of_not_accPt hxs]

/--
theorem `iteratedDerivWithin_eq_iterate` / 定理 `iteratedDerivWithin_eq_iterate`

English:
theorem iteratedDerivWithin_eq_iterate
  given: {x : 𝕜}
  proof: by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    rw [iteratedDerivWithin_succ]; rw [Function.iterate_succ']
    exact derivWithin_congr (fun y hy => IH) IH

中文:
定理 iteratedDerivWithin_eq_iterate
  条件: {x : 𝕜}
  证明: by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    rw [iteratedDerivWithin_succ]; rw [Function.iterate_succ']
    exact derivWithin_congr (fun y hy => IH) IH

Depends on / 依赖: Function, Function.iterate_succ, derivWithin_congr, generalizing, iterate_succ, iteratedDerivWithin_succ
-/
theorem iteratedDerivWithin_eq_iterate {x : 𝕜} :
    iteratedDerivWithin n f s x = (fun g : 𝕜 -> F => derivWithin g s)^[n] f x := by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    rw [iteratedDerivWithin_succ]; rw [Function.iterate_succ']
    exact derivWithin_congr (fun y hy => IH) IH

/--
theorem `iteratedDerivWithin_succ'` / 定理 `iteratedDerivWithin_succ'`

English:
theorem iteratedDerivWithin_succ'
  proof: by
  ext x; rw [iteratedDerivWithin_eq_iterate, iteratedDerivWithin_eq_iterate]; rfl

中文:
定理 iteratedDerivWithin_succ'
  证明: by
  ext x; rw [iteratedDerivWithin_eq_iterate, iteratedDerivWithin_eq_iterate]; rfl

Depends on / 依赖: iteratedDerivWithin_eq_iterate
-/
theorem iteratedDerivWithin_succ' :
    iteratedDerivWithin (n + 1) f s = (iteratedDerivWithin n (derivWithin f s) s) := by
  ext x; rw [iteratedDerivWithin_eq_iterate, iteratedDerivWithin_eq_iterate]; rfl

/--
theorem `contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin` / 定理 `contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin`

English:
theorem contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin
  statement: {n : Nat}
  proof: by
  simp only [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv, hs,
    contDiffOn_one_iff_derivWithin, ← iteratedDerivWithin_succ]
  grind

中文:
定理 contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin
  结论: {n : 自然数}
  证明: by
  simp only [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv, hs,
    contDiffOn_one_iff_derivWithin, ← iteratedDerivWithin_succ]
  grind

Depends on / 依赖: contDiffOn_nat_iff_continuousOn_differentiableOn_deriv, contDiffOn_one_iff_derivWithin, iteratedDerivWithin_succ
-/
theorem contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin {n : Nat}
    (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1 : Nat) f s ↔
      ContDiffOn 𝕜 n f s ∧ ContDiffOn 𝕜 1 (iteratedDerivWithin n f s) s := by
  simp only [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv, hs,
    contDiffOn_one_iff_derivWithin, ← iteratedDerivWithin_succ]
  grind



/--
theorem `iteratedDeriv_eq_iteratedFDeriv` / 定理 `iteratedDeriv_eq_iteratedFDeriv`

English:
theorem iteratedDeriv_eq_iteratedFDeriv
  proof: rfl

中文:
定理 iteratedDeriv_eq_iteratedFDeriv
  证明: rfl
-/
theorem iteratedDeriv_eq_iteratedFDeriv :
    iteratedDeriv n f x = (iteratedFDeriv 𝕜 n f x : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1 :=
  rfl

/--
theorem `iteratedDeriv_eq_equiv_comp` / 定理 `iteratedDeriv_eq_equiv_comp`

English:
theorem iteratedDeriv_eq_equiv_comp
  statement: iteratedDeriv n f =
  proof: by
  ext x; rfl

中文:
定理 iteratedDeriv_eq_equiv_comp
  结论: iteratedDeriv n f =
  证明: by
  ext x; rfl
-/
theorem iteratedDeriv_eq_equiv_comp : iteratedDeriv n f =
    (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).symm ∘ iteratedFDeriv 𝕜 n f := by
  ext x; rfl

/--
theorem `iteratedFDeriv_eq_equiv_comp` / 定理 `iteratedFDeriv_eq_equiv_comp`

English:
theorem iteratedFDeriv_eq_equiv_comp
  statement: iteratedFDeriv 𝕜 n f =
  proof: by
  rw [iteratedDeriv_eq_equiv_comp]; rw [← Function.comp_assoc]; rw [LinearIsometryEquiv.self_comp_symm]; rw [Function.id_comp]

中文:
定理 iteratedFDeriv_eq_equiv_comp
  结论: iteratedFDeriv 𝕜 n f =
  证明: by
  rw [iteratedDeriv_eq_equiv_comp]; rw [← Function.comp_assoc]; rw [LinearIsometryEquiv.self_comp_symm]; rw [Function.id_comp]

Depends on / 依赖: Function, Function.comp_assoc, Function.id_comp, LinearIsometryEquiv, LinearIsometryEquiv.self_comp_symm, comp_assoc, id_comp, iteratedDeriv_eq_equiv_comp, self_comp_symm
-/
theorem iteratedFDeriv_eq_equiv_comp : iteratedFDeriv 𝕜 n f =
    ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F ∘ iteratedDeriv n f := by
  rw [iteratedDeriv_eq_equiv_comp]; rw [← Function.comp_assoc]; rw [LinearIsometryEquiv.self_comp_symm]; rw [Function.id_comp]

/--
theorem `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` / 定理 `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`

English:
theorem iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod
  given: {m : Fin n -> 𝕜}
  proof: by
  rw [iteratedDeriv_eq_iteratedFDeriv]; rw [← ContinuousMultilinearMap.map_smul_univ]; simp

中文:
定理 iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod
  条件: {m : 有限集 n -> 𝕜}
  证明: by
  rw [iteratedDeriv_eq_iteratedFDeriv]; rw [← ContinuousMultilinearMap.map_smul_univ]; simp

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.map_smul_univ, iteratedDeriv_eq_iteratedFDeriv, map_smul_univ
-/
theorem iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod {m : Fin n -> 𝕜} :
    (iteratedFDeriv 𝕜 n f x : (Fin n -> 𝕜) -> F) m = (∏ i, m i) • iteratedDeriv n f x := by
  rw [iteratedDeriv_eq_iteratedFDeriv]; rw [← ContinuousMultilinearMap.map_smul_univ]; simp

/--
theorem `norm_iteratedFDeriv_eq_norm_iteratedDeriv` / 定理 `norm_iteratedFDeriv_eq_norm_iteratedDeriv`

English:
theorem norm_iteratedFDeriv_eq_norm_iteratedDeriv
  proof: by
  rw [iteratedDeriv_eq_equiv_comp]; rw [Function.comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]

中文:
定理 norm_iteratedFDeriv_eq_norm_iteratedDeriv
  证明: by
  rw [iteratedDeriv_eq_equiv_comp]; rw [Function.comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, LinearIsometryEquiv, LinearIsometryEquiv.norm_map, comp_apply, iteratedDeriv_eq_equiv_comp, norm_map
-/
theorem norm_iteratedFDeriv_eq_norm_iteratedDeriv :
    ‖iteratedFDeriv 𝕜 n f x‖ = ‖iteratedDeriv n f x‖ := by
  rw [iteratedDeriv_eq_equiv_comp]; rw [Function.comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]
/--
theorem `iteratedDeriv_zero` / 定理 `iteratedDeriv_zero`

English:
theorem iteratedDeriv_zero
  statement: iteratedDeriv 0 f = f
  proof: by ext x; simp [iteratedDeriv]

@[simp]

中文:
定理 iteratedDeriv_zero
  结论: iteratedDeriv 0 f = f
  证明: by ext x; simp [iteratedDeriv]

@[simp]

Depends on / 依赖: iteratedDeriv
-/
theorem iteratedDeriv_zero : iteratedDeriv 0 f = f := by ext x; simp [iteratedDeriv]

@[simp]
/--
theorem `iteratedDeriv_one` / 定理 `iteratedDeriv_one`

English:
theorem iteratedDeriv_one
  statement: iteratedDeriv 1 f = deriv f
  proof: by ext x; simp [iteratedDeriv]

中文:
定理 iteratedDeriv_one
  结论: iteratedDeriv 1 f = deriv f
  证明: by ext x; simp [iteratedDeriv]

Depends on / 依赖: iteratedDeriv
-/
theorem iteratedDeriv_one : iteratedDeriv 1 f = deriv f := by ext x; simp [iteratedDeriv]

/--
theorem `contDiff_iff_iteratedDeriv` / 定理 `contDiff_iff_iteratedDeriv`

English:
theorem contDiff_iff_iteratedDeriv
  given: {n : Nat∞}
  statement: ContDiff 𝕜 n f ↔
  proof: by
  simp only [contDiff_iff_continuous_differentiable, iteratedFDeriv_eq_equiv_comp,
    LinearIsometryEquiv.comp_continuous_iff, LinearIsometryEquiv.comp_differentiable_iff]

中文:
定理 contDiff_iff_iteratedDeriv
  条件: {n : 自然数∞}
  结论: 连续可微 𝕜 n f ↔
  证明: by
  simp only [contDiff_iff_continuous_differentiable, iteratedFDeriv_eq_equiv_comp,
    LinearIsometryEquiv.comp_continuous_iff, LinearIsometryEquiv.comp_differentiable_iff]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.comp_continuous_iff, LinearIsometryEquiv.comp_differentiable_iff, comp_continuous_iff, comp_differentiable_iff, contDiff_iff_continuous_differentiable, iteratedFDeriv_eq_equiv_comp
-/
theorem contDiff_iff_iteratedDeriv {n : Nat∞} : ContDiff 𝕜 n f ↔
    (forall m : Nat, (m : Nat∞) <= n -> Continuous (iteratedDeriv m f)) ∧
      forall m : Nat, (m : Nat∞) < n -> Differentiable 𝕜 (iteratedDeriv m f) := by
  simp only [contDiff_iff_continuous_differentiable, iteratedFDeriv_eq_equiv_comp,
    LinearIsometryEquiv.comp_continuous_iff, LinearIsometryEquiv.comp_differentiable_iff]

/--
theorem `contDiff_nat_iff_iteratedDeriv` / 定理 `contDiff_nat_iff_iteratedDeriv`

English:
theorem contDiff_nat_iff_iteratedDeriv
  given: {n : Nat}
  statement: ContDiff 𝕜 n f ↔
  proof: by
  rw [← WithTop.coe_natCast]; rw [contDiff_iff_iteratedDeriv]
  simp

中文:
定理 contDiff_nat_iff_iteratedDeriv
  条件: {n : 自然数}
  结论: 连续可微 𝕜 n f ↔
  证明: by
  rw [← WithTop.coe_natCast]; rw [contDiff_iff_iteratedDeriv]
  simp

Depends on / 依赖: WithTop, WithTop.coe_natCast, coe_natCast, contDiff_iff_iteratedDeriv
-/
theorem contDiff_nat_iff_iteratedDeriv {n : Nat} : ContDiff 𝕜 n f ↔
    (forall m : Nat, m <= n -> Continuous (iteratedDeriv m f)) ∧
      forall m : Nat, m < n -> Differentiable 𝕜 (iteratedDeriv m f) := by
  rw [← WithTop.coe_natCast]; rw [contDiff_iff_iteratedDeriv]
  simp

/--
theorem `contDiff_of_differentiable_iteratedDeriv` / 定理 `contDiff_of_differentiable_iteratedDeriv`

English:
theorem contDiff_of_differentiable_iteratedDeriv
  statement: {n : Nat∞}
  proof: contDiff_iff_iteratedDeriv.2 ⟨fun m hm => (h m hm).continuous, fun m hm => h m (le_of_lt hm)⟩

中文:
定理 contDiff_of_differentiable_iteratedDeriv
  结论: {n : 自然数∞}
  证明: contDiff_iff_iteratedDeriv.2 ⟨fun m hm => (h m hm).continuous, fun m hm => h m (le_of_lt hm)⟩

Depends on / 依赖: contDiff_iff_iteratedDeriv, continuous, le_of_lt
-/
theorem contDiff_of_differentiable_iteratedDeriv {n : Nat∞}
    (h : forall m : Nat, (m : Nat∞) <= n -> Differentiable 𝕜 (iteratedDeriv m f)) : ContDiff 𝕜 n f :=
  contDiff_iff_iteratedDeriv.2 ⟨fun m hm => (h m hm).continuous, fun m hm => h m (le_of_lt hm)⟩

/--
theorem `ContDiff.continuous_iteratedDeriv` / 定理 `ContDiff.continuous_iteratedDeriv`

English:
theorem ContDiff.continuous_iteratedDeriv
  statement: {n : Nat∞ω} (m : Nat) (h : ContDiff 𝕜 n f)
  proof: (contDiff_iff_iteratedDeriv.1 (h.of_le hmn)).1 m le_rfl

@[fun_prop]

中文:
定理 连续可微.continuous_iteratedDeriv
  结论: {n : 自然数∞ω} (m : 自然数) (h : 连续可微 𝕜 n f)
  证明: (contDiff_iff_iteratedDeriv.1 (h.of_le hmn)).1 m le_rfl

@[fun_prop]

Depends on / 依赖: contDiff_iff_iteratedDeriv, h.of_le, le_rfl, of_le
-/
theorem ContDiff.continuous_iteratedDeriv {n : Nat∞ω} (m : Nat) (h : ContDiff 𝕜 n f)
    (hmn : m <= n) : Continuous (iteratedDeriv m f) :=
  (contDiff_iff_iteratedDeriv.1 (h.of_le hmn)).1 m le_rfl

@[fun_prop]
/--
theorem `ContDiff.continuous_iteratedDeriv'` / 定理 `ContDiff.continuous_iteratedDeriv'`

English:
theorem ContDiff.continuous_iteratedDeriv'
  given: (m : Nat) (h : ContDiff 𝕜 m f)
  proof: ContDiff.continuous_iteratedDeriv m h (le_refl _)

中文:
定理 连续可微.continuous_iteratedDeriv'
  条件: (m : 自然数) (h : 连续可微 𝕜 m f)
  证明: ContDiff.continuous_iteratedDeriv m h (le_refl _)

Depends on / 依赖: ContDiff, ContDiff.continuous_iteratedDeriv, continuous_iteratedDeriv, le_refl
-/
theorem ContDiff.continuous_iteratedDeriv' (m : Nat) (h : ContDiff 𝕜 m f) :
    Continuous (iteratedDeriv m f) :=
  ContDiff.continuous_iteratedDeriv m h (le_refl _)

/--
theorem `ContDiff.differentiable_iteratedDeriv` / 定理 `ContDiff.differentiable_iteratedDeriv`

English:
theorem ContDiff.differentiable_iteratedDeriv
  statement: {n : Nat∞ω} (m : Nat) (h : ContDiff 𝕜 n f)
  proof: (contDiff_iff_iteratedDeriv.1 (h.of_le (ENat.add_one_natCast_le_withTop_of_lt hmn))).2 m
    (mod_cast (lt_add_one m))

@[fun_prop]

中文:
定理 连续可微.differentiable_iteratedDeriv
  结论: {n : 自然数∞ω} (m : 自然数) (h : 连续可微 𝕜 n f)
  证明: (contDiff_iff_iteratedDeriv.1 (h.of_le (ENat.add_one_natCast_le_withTop_of_lt hmn))).2 m
    (mod_cast (lt_add_one m))

@[fun_prop]

Depends on / 依赖: ENat.add_one_natCast_le_withTop_of_lt, add_one_natCast_le_withTop_of_lt, contDiff_iff_iteratedDeriv, h.of_le, lt_add_one, mod_cast, of_le
-/
theorem ContDiff.differentiable_iteratedDeriv {n : Nat∞ω} (m : Nat) (h : ContDiff 𝕜 n f)
    (hmn : m < n) : Differentiable 𝕜 (iteratedDeriv m f) :=
  (contDiff_iff_iteratedDeriv.1 (h.of_le (ENat.add_one_natCast_le_withTop_of_lt hmn))).2 m
    (mod_cast (lt_add_one m))

@[fun_prop]
/--
theorem `ContDiff.differentiable_iteratedDeriv'` / 定理 `ContDiff.differentiable_iteratedDeriv'`

English:
theorem ContDiff.differentiable_iteratedDeriv'
  given: (m : Nat) (h : ContDiff 𝕜 (m + 1) f)
  proof: h.differentiable_iteratedDeriv m (Nat.cast_lt.mpr m.lt_succ_self)

中文:
定理 连续可微.differentiable_iteratedDeriv'
  条件: (m : 自然数) (h : 连续可微 𝕜 (m + 1) f)
  证明: h.differentiable_iteratedDeriv m (Nat.cast_lt.mpr m.lt_succ_self)

Depends on / 依赖: Nat.cast_lt.mpr, cast_lt, differentiable_iteratedDeriv, h.differentiable_iteratedDeriv, lt_succ_self, m.lt_succ_self
-/
theorem ContDiff.differentiable_iteratedDeriv' (m : Nat) (h : ContDiff 𝕜 (m + 1) f) :
    Differentiable 𝕜 (iteratedDeriv m f) :=
  h.differentiable_iteratedDeriv m (Nat.cast_lt.mpr m.lt_succ_self)

/--
theorem `iteratedDeriv_succ` / 定理 `iteratedDeriv_succ`

English:
theorem iteratedDeriv_succ
  statement: iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f)
  proof: by
  rw [← iteratedDerivWithin_univ]; rw [← iteratedDerivWithin_univ]; rw [← derivWithin_univ]
  exact iteratedDerivWithin_succ

中文:
定理 iteratedDeriv_succ
  结论: iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f)
  证明: by
  rw [← iteratedDerivWithin_univ]; rw [← iteratedDerivWithin_univ]; rw [← derivWithin_univ]
  exact iteratedDerivWithin_succ

Depends on / 依赖: derivWithin_univ, iteratedDerivWithin_succ, iteratedDerivWithin_univ
-/
theorem iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f) := by
  rw [← iteratedDerivWithin_univ]; rw [← iteratedDerivWithin_univ]; rw [← derivWithin_univ]
  exact iteratedDerivWithin_succ

/--
theorem `iteratedDeriv_eq_iterate` / 定理 `iteratedDeriv_eq_iterate`

English:
theorem iteratedDeriv_eq_iterate
  statement: iteratedDeriv n f = deriv^[n] f
  proof: by
  ext x
  rw [← iteratedDerivWithin_univ]
  convert! iteratedDerivWithin_eq_iterate (F := F)
  simp [derivWithin_univ]

中文:
定理 iteratedDeriv_eq_iterate
  结论: iteratedDeriv n f = deriv^[n] f
  证明: by
  ext x
  rw [← iteratedDerivWithin_univ]
  convert! iteratedDerivWithin_eq_iterate (F := F)
  simp [derivWithin_univ]

Depends on / 依赖: convert, derivWithin_univ, iteratedDerivWithin_eq_iterate, iteratedDerivWithin_univ
-/
theorem iteratedDeriv_eq_iterate : iteratedDeriv n f = deriv^[n] f := by
  ext x
  rw [← iteratedDerivWithin_univ]
  convert! iteratedDerivWithin_eq_iterate (F := F)
  simp [derivWithin_univ]

/--
theorem `iteratedDerivWithin_of_isOpen` / 定理 `iteratedDerivWithin_of_isOpen`

English:
theorem iteratedDerivWithin_of_isOpen
  given: (hs : IsOpen s)
  proof: by
  intro x hx
  simp_rw [iteratedDerivWithin, iteratedDeriv, iteratedFDerivWithin_of_isOpen n hs hx]

中文:
定理 iteratedDerivWithin_of_isOpen
  条件: (hs : 是开集 s)
  证明: by
  intro x hx
  simp_rw [iteratedDerivWithin, iteratedDeriv, iteratedFDerivWithin_of_isOpen n hs hx]

Depends on / 依赖: iteratedDeriv, iteratedDerivWithin, iteratedFDerivWithin_of_isOpen, simp_rw
-/
theorem iteratedDerivWithin_of_isOpen (hs : IsOpen s) :
    Set.EqOn (iteratedDerivWithin n f s) (iteratedDeriv n f) s := by
  intro x hx
  simp_rw [iteratedDerivWithin, iteratedDeriv, iteratedFDerivWithin_of_isOpen n hs hx]

/--
theorem `iteratedDerivWithin_congr_right_of_isOpen` / 定理 `iteratedDerivWithin_congr_right_of_isOpen`

English:
theorem iteratedDerivWithin_congr_right_of_isOpen
  statement: (f : 𝕜 -> F) (n : Nat) {s t : Set 𝕜} (hs : IsOpen s)
  proof: by
  intro r hr
  rw [iteratedDerivWithin_of_isOpen hs hr.1]; rw [iteratedDerivWithin_of_isOpen ht hr.2]

中文:
定理 iteratedDerivWithin_congr_right_of_isOpen
  结论: (f : 𝕜 -> F) (n : 自然数) {s t : 集合 𝕜} (hs : 是开集 s)
  证明: by
  intro r hr
  rw [iteratedDerivWithin_of_isOpen hs hr.1]; rw [iteratedDerivWithin_of_isOpen ht hr.2]

Depends on / 依赖: iteratedDerivWithin_of_isOpen
-/
theorem iteratedDerivWithin_congr_right_of_isOpen (f : 𝕜 -> F) (n : Nat) {s t : Set 𝕜} (hs : IsOpen s)
    (ht : IsOpen t) : (s inter t).EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n f t) := by
  intro r hr
  rw [iteratedDerivWithin_of_isOpen hs hr.1]; rw [iteratedDerivWithin_of_isOpen ht hr.2]

/--
theorem `iteratedDerivWithin_of_isOpen_eq_iterate` / 定理 `iteratedDerivWithin_of_isOpen_eq_iterate`

English:
theorem iteratedDerivWithin_of_isOpen_eq_iterate
  given: (hs : IsOpen s)
  proof: by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  rw [iteratedDeriv_eq_iterate]
  exact Set.eqOn_refl _ _

中文:
定理 iteratedDerivWithin_of_isOpen_eq_iterate
  条件: (hs : 是开集 s)
  证明: by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  rw [iteratedDeriv_eq_iterate]
  exact Set.eqOn_refl _ _

Depends on / 依赖: Set.EqOn.trans, Set.eqOn_refl, eqOn_refl, iteratedDerivWithin_of_isOpen, iteratedDeriv_eq_iterate
-/
theorem iteratedDerivWithin_of_isOpen_eq_iterate (hs : IsOpen s) :
    EqOn (iteratedDerivWithin n f s) (deriv^[n] f) s := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  rw [iteratedDeriv_eq_iterate]
  exact Set.eqOn_refl _ _

/--
theorem `iteratedDeriv_succ'` / 定理 `iteratedDeriv_succ'`

English:
theorem iteratedDeriv_succ'
  statement: iteratedDeriv (n + 1) f = iteratedDeriv n (deriv f)
  proof: by
  rw [iteratedDeriv_eq_iterate]; rw [iteratedDeriv_eq_iterate]; rw [Function.iterate_succ_apply]

中文:
定理 iteratedDeriv_succ'
  结论: iteratedDeriv (n + 1) f = iteratedDeriv n (deriv f)
  证明: by
  rw [iteratedDeriv_eq_iterate]; rw [iteratedDeriv_eq_iterate]; rw [Function.iterate_succ_apply]

Depends on / 依赖: Function, Function.iterate_succ_apply, iterate_succ_apply, iteratedDeriv_eq_iterate
-/
theorem iteratedDeriv_succ' : iteratedDeriv (n + 1) f = iteratedDeriv n (deriv f) := by
  rw [iteratedDeriv_eq_iterate]; rw [iteratedDeriv_eq_iterate]; rw [Function.iterate_succ_apply]

/--
lemma `AnalyticAt.hasFPowerSeriesAt` / 引理 `AnalyticAt.hasFPowerSeriesAt`

English:
lemma AnalyticAt.hasFPowerSeriesAt
  statement: {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  proof: by
  obtain ⟨p, hp⟩ := h
  convert! hp
  obtain ⟨r, hpr⟩ := hp
  ext n
  have h_fact_smul := hpr.factorial_smul 1
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul, one_pow, one_mul] at h_fact_smul
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_eq_mul_left_iff]
  left
  rw [div_eq_iff]; rw [mul_comm]; rw [h_fact_smul]; rw [← iteratedDeriv_eq_iteratedFDeriv]
  norm_cast
  positivity

中文:
引理 AnalyticAt.hasFPowerSeriesAt
  结论: {𝕜 : 类型} [NontriviallyNormedField 𝕜] [完备空间 𝕜]
  证明: by
  obtain ⟨p, hp⟩ := h
  convert! hp
  obtain ⟨r, hpr⟩ := hp
  ext n
  have h_fact_smul := hpr.factorial_smul 1
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul, one_pow, one_mul] at h_fact_smul
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_eq_mul_left_iff]
  left
  rw [div_eq_iff]; rw [mul_comm]; rw [h_fact_smul]; rw [← iteratedDeriv_eq_iteratedFDeriv]
  norm_cast
  positivity

Depends on / 依赖: Finset, Finset.card_univ, Finset.prod_const, Fintype, Fintype.card_fin, FormalMultilinearSeries, FormalMultilinearSeries.apply_eq_prod_smul_coeff, FormalMultilinearSeries.coeff_ofScalars, apply_eq_prod_smul_coeff, card_fin, card_univ, coeff_ofScalars, convert, div_eq_iff, factorial_smul, h_fact_smul, hpr.factorial_smul, iteratedDeriv_eq_iterat, mul_comm, mul_eq_mul_left_iff
-/
lemma AnalyticAt.hasFPowerSeriesAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [CharZero 𝕜] {f : 𝕜 -> 𝕜} {x : 𝕜} (h : AnalyticAt 𝕜 f x) :
    HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars 𝕜 (fun n => iteratedDeriv n f x / n.factorial)) x := by
  obtain ⟨p, hp⟩ := h
  convert! hp
  obtain ⟨r, hpr⟩ := hp
  ext n
  have h_fact_smul := hpr.factorial_smul 1
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul, one_pow, one_mul] at h_fact_smul
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_eq_mul_left_iff]
  left
  rw [div_eq_iff]; rw [mul_comm]; rw [h_fact_smul]; rw [← iteratedDeriv_eq_iteratedFDeriv]
  norm_cast
  positivity

/--
theorem `iteratedDeriv_const` / 定理 `iteratedDeriv_const`

English:
theorem iteratedDeriv_const
  given: {n : Nat} {c : F} {x : 𝕜}
  proof: by
  induction n generalizing c with
  | zero => simp
  | succ n h => simp [iteratedDeriv_succ', h]

中文:
定理 iteratedDeriv_const
  条件: {n : 自然数} {c : F} {x : 𝕜}
  证明: by
  induction n generalizing c with
  | zero => simp
  | succ n h => simp [iteratedDeriv_succ', h]

Depends on / 依赖: generalizing, iteratedDeriv_succ
-/
theorem iteratedDeriv_const {n : Nat} {c : F} {x : 𝕜} :
    iteratedDeriv n (fun _ => c) x = if n = 0 then c else 0 := by
  induction n generalizing c with
  | zero => simp
  | succ n h => simp [iteratedDeriv_succ', h]

/--
theorem `iteratedDerivWithin_const` / 定理 `iteratedDerivWithin_const`

English:
theorem iteratedDerivWithin_const
  given: {n : Nat} {c : F} {s : Set 𝕜} {x : 𝕜}
  proof: by
  induction n generalizing c with
  | zero => simp
  | succ n h => simp [iteratedDerivWithin_succ', Pi.zero_def, h]

@[simp]

中文:
定理 iteratedDerivWithin_const
  条件: {n : 自然数} {c : F} {s : 集合 𝕜} {x : 𝕜}
  证明: by
  induction n generalizing c with
  | zero => simp
  | succ n h => simp [iteratedDerivWithin_succ', Pi.zero_def, h]

@[simp]

Depends on / 依赖: Pi.zero_def, generalizing, iteratedDerivWithin_succ, zero_def
-/
theorem iteratedDerivWithin_const {n : Nat} {c : F} {s : Set 𝕜} {x : 𝕜} :
    iteratedDerivWithin n (fun _ => c) s x = if n = 0 then c else 0 := by
  induction n generalizing c with
  | zero => simp
  | succ n h => simp [iteratedDerivWithin_succ', Pi.zero_def, h]

@[simp]
/--
lemma `iteratedDeriv_fun_const_zero` / 引理 `iteratedDeriv_fun_const_zero`

English:
lemma iteratedDeriv_fun_const_zero
  statement: iteratedDeriv n (fun _ => 0) x = (0 : F)
  proof: by
  simpa using @iteratedDeriv_const 𝕜 _ F _ _ n 0

@[simp]

中文:
引理 iteratedDeriv_fun_const_zero
  结论: iteratedDeriv n (fun _ => 0) x = (0 : F)
  证明: by
  simpa using @iteratedDeriv_const 𝕜 _ F _ _ n 0

@[simp]

Depends on / 依赖: iteratedDeriv_const
-/
lemma iteratedDeriv_fun_const_zero : iteratedDeriv n (fun _ => 0) x = (0 : F) := by
  simpa using @iteratedDeriv_const 𝕜 _ F _ _ n 0

@[simp]
/--
lemma `iteratedDeriv_const_zero` / 引理 `iteratedDeriv_const_zero`

English:
lemma iteratedDeriv_const_zero
  statement: iteratedDeriv n (0 : 𝕜 -> F) x = (0 : F)
  proof: by
  simp [Pi.zero_def]

@[simp]

中文:
引理 iteratedDeriv_const_zero
  结论: iteratedDeriv n (0 : 𝕜 -> F) x = (0 : F)
  证明: by
  simp [Pi.zero_def]

@[simp]

Depends on / 依赖: Pi.zero_def, zero_def
-/
lemma iteratedDeriv_const_zero : iteratedDeriv n (0 : 𝕜 -> F) x = (0 : F) := by
  simp [Pi.zero_def]

@[simp]
/--
lemma `iteratedDerivWithin_fun_const_zero` / 引理 `iteratedDerivWithin_fun_const_zero`

English:
lemma iteratedDerivWithin_fun_const_zero
  given: {s : Set 𝕜}
  proof: by
  simpa using @iteratedDerivWithin_const 𝕜 _ F _ _ n 0

@[simp]

中文:
引理 iteratedDerivWithin_fun_const_zero
  条件: {s : 集合 𝕜}
  证明: by
  simpa using @iteratedDerivWithin_const 𝕜 _ F _ _ n 0

@[simp]

Depends on / 依赖: iteratedDerivWithin_const
-/
lemma iteratedDerivWithin_fun_const_zero {s : Set 𝕜} :
    iteratedDerivWithin n (fun _ => 0) s x = (0 : F) := by
  simpa using @iteratedDerivWithin_const 𝕜 _ F _ _ n 0

@[simp]
/--
lemma `iteratedDerivWithin_const_zero` / 引理 `iteratedDerivWithin_const_zero`

English:
lemma iteratedDerivWithin_const_zero
  given: {s : Set 𝕜}
  proof: by
  simp [Pi.zero_def]

中文:
引理 iteratedDerivWithin_const_zero
  条件: {s : 集合 𝕜}
  证明: by
  simp [Pi.zero_def]

Depends on / 依赖: Pi.zero_def, zero_def
-/
lemma iteratedDerivWithin_const_zero {s : Set 𝕜} :
    iteratedDerivWithin n (0 : 𝕜 -> F) s x = (0 : F) := by
  simp [Pi.zero_def]

/--
theorem `contDiff_nat_succ_iff_contDiff_one_iteratedDeriv` / 定理 `contDiff_nat_succ_iff_contDiff_one_iteratedDeriv`

English:
theorem contDiff_nat_succ_iff_contDiff_one_iteratedDeriv
  given: {n : Nat}
  statement: ContDiff 𝕜 (n + 1 : Nat) f ↔
  proof: by
  simp only [contDiff_nat_iff_iteratedDeriv, contDiff_one_iff_deriv, ← iteratedDeriv_succ]
  grind

中文:
定理 contDiff_nat_succ_iff_contDiff_one_iteratedDeriv
  条件: {n : 自然数}
  结论: 连续可微 𝕜 (n + 1 : 自然数) f ↔
  证明: by
  simp only [contDiff_nat_iff_iteratedDeriv, contDiff_one_iff_deriv, ← iteratedDeriv_succ]
  grind

Depends on / 依赖: contDiff_nat_iff_iteratedDeriv, contDiff_one_iff_deriv, iteratedDeriv_succ
-/
theorem contDiff_nat_succ_iff_contDiff_one_iteratedDeriv {n : Nat} : ContDiff 𝕜 (n + 1 : Nat) f ↔
    ContDiff 𝕜 n f ∧ ContDiff 𝕜 1 (iteratedDeriv n f) := by
  simp only [contDiff_nat_iff_iteratedDeriv, contDiff_one_iff_deriv, ← iteratedDeriv_succ]
  grind
