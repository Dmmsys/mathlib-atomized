/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Inverse function theorem

In this file we prove the inverse function theorem. It says that if a map `f : E → F`
has an invertible strict derivative `f'` at `a`, then it is locally invertible,
and the inverse function has derivative `f' ⁻¹`.

We define `HasStrictFDerivAt.toOpenPartialHomeomorph` that repacks a function `f`
with a `hf : HasStrictFDerivAt f f' a`, `f' : E ≃L[𝕜] F`, into an `OpenPartialHomeomorph`.
The `toFun` of this `OpenPartialHomeomorph` is defeq to `f`, so one can apply theorems
about `OpenPartialHomeomorph` to `hf.toOpenPartialHomeomorph f`, and get statements about `f`.

Then we define `HasStrictFDerivAt.localInverse` to be the `invFun` of this `OpenPartialHomeomorph`,
and prove two versions of the inverse function theorem:

* `HasStrictFDerivAt.to_localInverse`: if `f` has an invertible derivative `f'` at `a` in the
  strict sense (`hf`), then `hf.localInverse f f' a` has derivative `f'.symm` at `f a` in the
  strict sense;

* `HasStrictFDerivAt.to_local_left_inverse`: if `f` has an invertible derivative `f'` at `a` in
  the strict sense and `g` is locally left inverse to `f` near `a`, then `g` has derivative
  `f'.symm` at `f a` in the strict sense.

Some related theorems, providing the derivative and higher regularity assuming that we already know
the inverse function, are formulated in the `Analysis/Calculus/FDeriv` and `Analysis/Calculus/Deriv`
folders, and in `ContDiff.lean`.

## Tags

derivative, strictly differentiable, continuously differentiable, smooth, inverse function
-/

@[expose] public section

open Function Set Filter Metric

open scoped Topology NNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Asymptotics Filter Metric Set

open ContinuousLinearMap (id)


/-!
### Inverse function theorem

Let `f : E → F` be a map defined on a complete vector
space `E`. Assume that `f` has an invertible derivative `f' : E ≃L[𝕜] F` at `a : E` in the strict
sense. Then `f` approximates `f'` in the sense of `ApproximatesLinearOn` on an open neighborhood
of `a`, and we can apply `ApproximatesLinearOn.toOpenPartialHomeomorph` to construct the inverse
function. -/

namespace HasStrictFDerivAt

/--
theorem `approximates_deriv_on_nhds` / 定理 `approximates_deriv_on_nhds`

English:
theorem approximates_deriv_on_nhds
  statement: {f : E -> F} {f' : E ->L[𝕜] F} {a : E}
  proof: by
  rcases hc with hE | hc
  · refine ⟨univ, IsOpen.mem_nhds isOpen_univ trivial, fun x _ y _ => ?_⟩
    simp [@Subsingleton.elim E hE x y]
  have := hf.isLittleO.def hc
  rw [nhds_prod_eq]; rw [Filter.Eventually]; rw [mem_prod_same_iff] at this
  rcases this with ⟨s, has, hs⟩
  exact ⟨s, has, fun 

中文:
定理 approximates_deriv_on_nhds
  结论: {f : E -> F} {f' : E ->L[𝕜] F} {a : E}
  证明: by
  rcases hc with hE | hc
  · refine ⟨univ, IsOpen.mem_nhds isOpen_univ trivial, fun x _ y _ => ?_⟩
    simp [@Subsingleton.elim E hE x y]
  have := hf.isLittleO.def hc
  rw [nhds_prod_eq]; rw [Filter.Eventually]; rw [mem_prod_same_iff] at this
  rcases this with ⟨s, has, hs⟩
  exact ⟨s, has, fun 

Depends on / 依赖: Eventually, Filter, Filter.Eventually, IsOpen, IsOpen.mem_nhds, Subsingleton, Subsingleton.elim, hf.isLittleO.def, isLittleO, isOpen_univ, mem_nhds, mem_prod_same_iff, mk_mem_prod, nhds_prod_eq
-/
theorem approximates_deriv_on_nhds {f : E -> F} {f' : E ->L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) {c : Real>=0} (hc : Subsingleton E ∨ 0 < c) :
    exists s in 𝓝 a, ApproximatesLinearOn f f' s c := by
  rcases hc with hE | hc
  · refine ⟨univ, IsOpen.mem_nhds isOpen_univ trivial, fun x _ y _ => ?_⟩
    simp [@Subsingleton.elim E hE x y]
  have := hf.isLittleO.def hc
  rw [nhds_prod_eq]; rw [Filter.Eventually]; rw [mem_prod_same_iff] at this
  rcases this with ⟨s, has, hs⟩
  exact ⟨s, has, fun x hx y hy => hs (mk_mem_prod hx hy)⟩

/--
theorem `map_nhds_eq_of_surj` / 定理 `map_nhds_eq_of_surj`

English:
theorem map_nhds_eq_of_surj
  statement: [CompleteSpace E] [CompleteSpace F] {f : E -> F} {f' : E ->L[𝕜] F} {a : E}
  proof: by
  let f'symm := f'.nonlinearRightInverseOfSurjective h
  set c : Real>=0 := f'symm.nnnorm⁻¹ / 2 with hc
  have f'symm_pos : 0 < f'symm.nnnorm := f'.nonlinearRightInverseOfSurjective_nnnorm_pos h
  have cpos : 0 < c := by simp [hc, inv_pos, f'symm_pos]
  obtain ⟨s, s_nhds, hs⟩ : exists s in 𝓝 a, A

中文:
定理 map_nhds_eq_of_surj
  结论: [CompleteSpace E] [CompleteSpace F] {f : E -> F} {f' : E ->L[𝕜] F} {a : E}
  证明: by
  let f'symm := f'.nonlinearRightInverseOfSurjective h
  set c : Real>=0 := f'symm.nnnorm⁻¹ / 2 with hc
  have f'symm_pos : 0 < f'symm.nnnorm := f'.nonlinearRightInverseOfSurjective_nnnorm_pos h
  have cpos : 0 < c := by simp [hc, inv_pos, f'symm_pos]
  obtain ⟨s, s_nhds, hs⟩ : exists s in 𝓝 a, A

Depends on / 依赖: ApproximatesLinearOn, NNReal, NNReal.half_lt_self, Or.inr, approximates_deriv_on_nhds, half_lt_self, hf.approximates_deriv_on_nhds, hs.map_nhds_eq, inv_pos, map_nhds_eq, ne_of_gt, nnnorm, nonlinearRightInverseOfSurjective, nonlinearRightInverseOfSurjective_nnnorm_pos, s_nhds, symm.nnnorm, symm_pos
-/
theorem map_nhds_eq_of_surj [CompleteSpace E] [CompleteSpace F] {f : E -> F} {f' : E ->L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) (h : f'.range = ⊤) :
    map f (𝓝 a) = 𝓝 (f a) := by
  let f'symm := f'.nonlinearRightInverseOfSurjective h
  set c : Real>=0 := f'symm.nnnorm⁻¹ / 2 with hc
  have f'symm_pos : 0 < f'symm.nnnorm := f'.nonlinearRightInverseOfSurjective_nnnorm_pos h
  have cpos : 0 < c := by simp [hc, inv_pos, f'symm_pos]
  obtain ⟨s, s_nhds, hs⟩ : exists s in 𝓝 a, ApproximatesLinearOn f f' s c :=
    hf.approximates_deriv_on_nhds (Or.inr cpos)
  apply hs.map_nhds_eq f'symm s_nhds (Or.inr (NNReal.half_lt_self _))
  simp [ne_of_gt f'symm_pos]

variable {f : E -> F} {f' : E ≃L[𝕜] F} {a : E}

/--
theorem `approximates_deriv_on_open_nhds` / 定理 `approximates_deriv_on_open_nhds`

English:
theorem approximates_deriv_on_open_nhds
  given: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  proof: by
  simp only [← and_assoc]
  refine ((nhds_basis_opens a).exists_iff fun s t => ApproximatesLinearOn.mono_set).1 ?_
  exact
hf.approximates_deriv_on_nhds
f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' => half_pos inv_pos.2 hf'

中文:
定理 approximates_deriv_on_open_nhds
  条件: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  证明: by
  simp only [← and_assoc]
  refine ((nhds_basis_opens a).exists_iff fun s t => ApproximatesLinearOn.mono_set).1 ?_
  exact
hf.approximates_deriv_on_nhds
f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' => half_pos inv_pos.2 hf'

Depends on / 依赖: ApproximatesLinearOn, ApproximatesLinearOn.mono_set, and_assoc, approximates_deriv_on_nhds, exists_iff, half_pos, hf.approximates_deriv_on_nhds, inv_pos, mono_set, nhds_basis_opens, subsingleton_or_nnnorm_symm_pos, subsingleton_or_nnnorm_symm_pos.imp
-/
theorem approximates_deriv_on_open_nhds (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
    exists s : Set E, a in s ∧ IsOpen s ∧
      ApproximatesLinearOn f (f' : E ->L[𝕜] F) s (‖(f'.symm : F ->L[𝕜] E)‖₊⁻¹ / 2) := by
  simp only [← and_assoc]
  refine ((nhds_basis_opens a).exists_iff fun s t => ApproximatesLinearOn.mono_set).1 ?_
  exact
hf.approximates_deriv_on_nhds
f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' => half_pos inv_pos.2 hf'

variable (f)
variable [CompleteSpace E]

/--
Definition of `toOpenPartialHomeomorph` / `toOpenPartialHomeomorph` 的定义

English:
definition toOpenPartialHomeomorph
  signature: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  body: ApproximatesLinearOn.toOpenPartialHomeomorph f
    (Classical.choose hf.approximates_deriv_on_open_nhds)
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.2
    (f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' =>
NNReal.half_lt_self ne_of_gt inv_pos.2 hf')
    (Classical.choose_spec

中文:
定义 toOpenPartialHomeomorph
  签名: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  定义体: ApproximatesLinearOn.toOpenPartialHomeomorph f
    (Classical.choose hf.approximates_deriv_on_open_nhds)
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.2
    (f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' =>
NNReal.half_lt_self ne_of_gt inv_pos.2 hf')
    (Classical.choose_spec

Depends on / 依赖: ApproximatesLinearOn, ApproximatesLinearOn.toOpenPartialHomeomorph, Classical, Classical.choose, Classical.choose_spec, NNReal, NNReal.half_lt_self, approximates_deriv_on_open_nhds, choose_spec, half_lt_self, hf.approximates_deriv_on_open_nhds, inv_pos, ne_of_gt, subsingleton_or_nnnorm_symm_pos, subsingleton_or_nnnorm_symm_pos.imp, toOpenPartialHomeomorph
-/
def toOpenPartialHomeomorph (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
  OpenPartialHomeomorph E F :=
    ApproximatesLinearOn.toOpenPartialHomeomorph f
    (Classical.choose hf.approximates_deriv_on_open_nhds)
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.2
    (f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' =>
NNReal.half_lt_self ne_of_gt inv_pos.2 hf')
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.1

variable {f}

@[simp]
/--
theorem `toOpenPartialHomeomorph_coe` / 定理 `toOpenPartialHomeomorph_coe`

English:
theorem toOpenPartialHomeomorph_coe
  given: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  proof: rfl

中文:
定理 toOpenPartialHomeomorph_coe
  条件: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  证明: rfl
-/
theorem toOpenPartialHomeomorph_coe (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
    (hf.toOpenPartialHomeomorph f : E -> F) = f :=
  rfl

/--
theorem `mem_toOpenPartialHomeomorph_source` / 定理 `mem_toOpenPartialHomeomorph_source`

English:
theorem mem_toOpenPartialHomeomorph_source
  given: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  proof: (Classical.choose_spec hf.approximates_deriv_on_open_nhds).1

中文:
定理 mem_toOpenPartialHomeomorph_source
  条件: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  证明: (Classical.choose_spec hf.approximates_deriv_on_open_nhds).1

Depends on / 依赖: Classical, Classical.choose_spec, approximates_deriv_on_open_nhds, choose_spec, hf.approximates_deriv_on_open_nhds
-/
theorem mem_toOpenPartialHomeomorph_source (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
    a in (hf.toOpenPartialHomeomorph f).source :=
  (Classical.choose_spec hf.approximates_deriv_on_open_nhds).1

/--
theorem `image_mem_toOpenPartialHomeomorph_target` / 定理 `image_mem_toOpenPartialHomeomorph_target`

English:
theorem image_mem_toOpenPartialHomeomorph_target
  given: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  proof: (hf.toOpenPartialHomeomorph f).map_source hf.mem_toOpenPartialHomeomorph_source

中文:
定理 image_mem_toOpenPartialHomeomorph_target
  条件: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  证明: (hf.toOpenPartialHomeomorph f).map_source hf.mem_toOpenPartialHomeomorph_source

Depends on / 依赖: hf.mem_toOpenPartialHomeomorph_source, hf.toOpenPartialHomeomorph, map_source, mem_toOpenPartialHomeomorph_source, toOpenPartialHomeomorph
-/
theorem image_mem_toOpenPartialHomeomorph_target (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
    f a in (hf.toOpenPartialHomeomorph f).target :=
  (hf.toOpenPartialHomeomorph f).map_source hf.mem_toOpenPartialHomeomorph_source

/--
theorem `map_nhds_eq_of_equiv` / 定理 `map_nhds_eq_of_equiv`

English:
theorem map_nhds_eq_of_equiv
  given: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  proof: (hf.toOpenPartialHomeomorph f).map_nhds_eq hf.mem_toOpenPartialHomeomorph_source

中文:
定理 map_nhds_eq_of_equiv
  条件: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  证明: (hf.toOpenPartialHomeomorph f).map_nhds_eq hf.mem_toOpenPartialHomeomorph_source

Depends on / 依赖: hf.mem_toOpenPartialHomeomorph_source, hf.toOpenPartialHomeomorph, map_nhds_eq, mem_toOpenPartialHomeomorph_source, toOpenPartialHomeomorph
-/
theorem map_nhds_eq_of_equiv (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
    map f (𝓝 a) = 𝓝 (f a) :=
  (hf.toOpenPartialHomeomorph f).map_nhds_eq hf.mem_toOpenPartialHomeomorph_source

variable (f f' a)

/--
Definition of `localInverse` / `localInverse` 的定义

English:
definition localInverse
  signature: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  body: (hf.toOpenPartialHomeomorph f).symm

中文:
定义 localInverse
  签名: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  定义体: (hf.toOpenPartialHomeomorph f).symm

Depends on / 依赖: hf.toOpenPartialHomeomorph, toOpenPartialHomeomorph
-/
def localInverse (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : F -> E :=
  (hf.toOpenPartialHomeomorph f).symm

variable {f f' a}

/--
theorem `localInverse_def` / 定理 `localInverse_def`

English:
theorem localInverse_def
  given: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  proof: rfl

中文:
定理 localInverse_def
  条件: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  证明: rfl
-/
theorem localInverse_def (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
    hf.localInverse f _ _ = (hf.toOpenPartialHomeomorph f).symm :=
  rfl

/--
theorem `eventually_left_inverse` / 定理 `eventually_left_inverse`

English:
theorem eventually_left_inverse
  given: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  proof: (hf.toOpenPartialHomeomorph f).eventually_left_inverse hf.mem_toOpenPartialHomeomorph_source

@[simp]

中文:
定理 eventually_left_inverse
  条件: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  证明: (hf.toOpenPartialHomeomorph f).eventually_left_inverse hf.mem_toOpenPartialHomeomorph_source

@[simp]

Depends on / 依赖: eventually_left_inverse, hf.mem_toOpenPartialHomeomorph_source, hf.toOpenPartialHomeomorph, mem_toOpenPartialHomeomorph_source, toOpenPartialHomeomorph
-/
theorem eventually_left_inverse (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
    forallᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x :=
  (hf.toOpenPartialHomeomorph f).eventually_left_inverse hf.mem_toOpenPartialHomeomorph_source

@[simp]
/--
theorem `localInverse_apply_image` / 定理 `localInverse_apply_image`

English:
theorem localInverse_apply_image
  given: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  proof: hf.eventually_left_inverse.self_of_nhds

中文:
定理 localInverse_apply_image
  条件: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  证明: hf.eventually_left_inverse.self_of_nhds

Depends on / 依赖: eventually_left_inverse, hf.eventually_left_inverse.self_of_nhds, self_of_nhds
-/
theorem localInverse_apply_image (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
    hf.localInverse f f' a (f a) = a :=
  hf.eventually_left_inverse.self_of_nhds

/--
theorem `eventually_right_inverse` / 定理 `eventually_right_inverse`

English:
theorem eventually_right_inverse
  given: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  proof: (hf.toOpenPartialHomeomorph f).eventually_right_inverse' hf.mem_toOpenPartialHomeomorph_source

中文:
定理 eventually_right_inverse
  条件: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  证明: (hf.toOpenPartialHomeomorph f).eventually_right_inverse' hf.mem_toOpenPartialHomeomorph_source

Depends on / 依赖: eventually_right_inverse, hf.mem_toOpenPartialHomeomorph_source, hf.toOpenPartialHomeomorph, mem_toOpenPartialHomeomorph_source, toOpenPartialHomeomorph
-/
theorem eventually_right_inverse (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
    forallᶠ y in 𝓝 (f a), f (hf.localInverse f f' a y) = y :=
  (hf.toOpenPartialHomeomorph f).eventually_right_inverse' hf.mem_toOpenPartialHomeomorph_source

/--
theorem `localInverse_continuousAt` / 定理 `localInverse_continuousAt`

English:
theorem localInverse_continuousAt
  given: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  proof: (hf.toOpenPartialHomeomorph f).continuousAt_symm hf.image_mem_toOpenPartialHomeomorph_target

中文:
定理 localInverse_continuousAt
  条件: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  证明: (hf.toOpenPartialHomeomorph f).continuousAt_symm hf.image_mem_toOpenPartialHomeomorph_target

Depends on / 依赖: continuousAt_symm, hf.image_mem_toOpenPartialHomeomorph_target, hf.toOpenPartialHomeomorph, image_mem_toOpenPartialHomeomorph_target, toOpenPartialHomeomorph
-/
theorem localInverse_continuousAt (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
    ContinuousAt (hf.localInverse f f' a) (f a) :=
  (hf.toOpenPartialHomeomorph f).continuousAt_symm hf.image_mem_toOpenPartialHomeomorph_target

/--
theorem `localInverse_tendsto` / 定理 `localInverse_tendsto`

English:
theorem localInverse_tendsto
  given: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  proof: (hf.toOpenPartialHomeomorph f).tendsto_symm hf.mem_toOpenPartialHomeomorph_source

中文:
定理 localInverse_tendsto
  条件: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  证明: (hf.toOpenPartialHomeomorph f).tendsto_symm hf.mem_toOpenPartialHomeomorph_source

Depends on / 依赖: hf.mem_toOpenPartialHomeomorph_source, hf.toOpenPartialHomeomorph, mem_toOpenPartialHomeomorph_source, tendsto_symm, toOpenPartialHomeomorph
-/
theorem localInverse_tendsto (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
    Tendsto (hf.localInverse f f' a) (𝓝 <| f a) (𝓝 a) :=
  (hf.toOpenPartialHomeomorph f).tendsto_symm hf.mem_toOpenPartialHomeomorph_source

/--
theorem `localInverse_unique` / 定理 `localInverse_unique`

English:
theorem localInverse_unique
  statement: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) {g : F -> E}
  proof: eventuallyEq_of_left_inv_of_right_inv hg hf.eventually_right_inverse
    (hf.toOpenPartialHomeomorph f).tendsto_symm hf.mem_toOpenPartialHomeomorph_source

中文:
定理 localInverse_unique
  结论: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) {g : F -> E}
  证明: eventuallyEq_of_left_inv_of_right_inv hg hf.eventually_right_inverse
    (hf.toOpenPartialHomeomorph f).tendsto_symm hf.mem_toOpenPartialHomeomorph_source

Depends on / 依赖: eventuallyEq_of_left_inv_of_right_inv, eventually_right_inverse, hf.eventually_right_inverse, hf.mem_toOpenPartialHomeomorph_source, hf.toOpenPartialHomeomorph, mem_toOpenPartialHomeomorph_source, tendsto_symm, toOpenPartialHomeomorph
-/
theorem localInverse_unique (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) {g : F -> E}
    (hg : forallᶠ x in 𝓝 a, g (f x) = x) : forallᶠ y in 𝓝 (f a), g y = localInverse f f' a hf y :=
eventuallyEq_of_left_inv_of_right_inv hg hf.eventually_right_inverse
    (hf.toOpenPartialHomeomorph f).tendsto_symm hf.mem_toOpenPartialHomeomorph_source

/--
theorem `to_localInverse` / 定理 `to_localInverse`

English:
theorem to_localInverse
  given: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  proof: (hf.toOpenPartialHomeomorph f).hasStrictFDerivAt_symm
hf.image_mem_toOpenPartialHomeomorph_target by
    simpa [← localInverse_def] using hf

中文:
定理 to_localInverse
  条件: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
  证明: (hf.toOpenPartialHomeomorph f).hasStrictFDerivAt_symm
hf.image_mem_toOpenPartialHomeomorph_target by
    simpa [← localInverse_def] using hf

Depends on / 依赖: hasStrictFDerivAt_symm, hf.image_mem_toOpenPartialHomeomorph_target, hf.toOpenPartialHomeomorph, image_mem_toOpenPartialHomeomorph_target, localInverse_def, toOpenPartialHomeomorph
-/
theorem to_localInverse (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
    HasStrictFDerivAt (hf.localInverse f f' a) (f'.symm : F ->L[𝕜] E) (f a) :=
  (hf.toOpenPartialHomeomorph f).hasStrictFDerivAt_symm
hf.image_mem_toOpenPartialHomeomorph_target by
    simpa [← localInverse_def] using hf

/--
theorem `to_local_left_inverse` / 定理 `to_local_left_inverse`

English:
theorem to_local_left_inverse
  statement: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) {g : F -> E}
  proof: hf.to_localInverse.congr_of_eventuallyEq (hf.localInverse_unique hg).mono fun _ => Eq.symm

中文:
定理 to_local_left_inverse
  结论: (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) {g : F -> E}
  证明: hf.to_localInverse.congr_of_eventuallyEq (hf.localInverse_unique hg).mono fun _ => Eq.symm

Depends on / 依赖: Eq.symm, congr_of_eventuallyEq, hf.localInverse_unique, hf.to_localInverse.congr_of_eventuallyEq, localInverse_unique, to_localInverse
-/
theorem to_local_left_inverse (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) {g : F -> E}
    (hg : forallᶠ x in 𝓝 a, g (f x) = x) : HasStrictFDerivAt g (f'.symm : F ->L[𝕜] E) (f a) :=
hf.to_localInverse.congr_of_eventuallyEq (hf.localInverse_unique hg).mono fun _ => Eq.symm

end HasStrictFDerivAt

/--
theorem `isOpenMap_of_hasStrictFDerivAt_equiv` / 定理 `isOpenMap_of_hasStrictFDerivAt_equiv`

English:
theorem isOpenMap_of_hasStrictFDerivAt_equiv
  statement: [CompleteSpace E] {f : E -> F} {f' : E -> E ≃L[𝕜] F}
  proof: isOpenMap_iff_nhds_le.2 fun x => (hf x).map_nhds_eq_of_equiv.ge

中文:
定理 isOpenMap_of_hasStrictFDerivAt_equiv
  结论: [CompleteSpace E] {f : E -> F} {f' : E -> E ≃L[𝕜] F}
  证明: isOpenMap_iff_nhds_le.2 fun x => (hf x).map_nhds_eq_of_equiv.ge

Depends on / 依赖: isOpenMap_iff_nhds_le, map_nhds_eq_of_equiv, map_nhds_eq_of_equiv.ge
-/
theorem isOpenMap_of_hasStrictFDerivAt_equiv [CompleteSpace E] {f : E -> F} {f' : E -> E ≃L[𝕜] F}
    (hf : forall x, HasStrictFDerivAt f (f' x : E ->L[𝕜] F) x) : IsOpenMap f :=
  isOpenMap_iff_nhds_le.2 fun x => (hf x).map_nhds_eq_of_equiv.ge
