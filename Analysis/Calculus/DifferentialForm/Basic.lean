/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Sam Lindauer
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap

/-!
# Exterior derivative of a differential form on a normed space

In this file we define the exterior derivative of a differential form on a normed space.
Under certain smoothness assumptions, we prove that this operation is linear in the form
and the second exterior derivative of a form is zero.

We represent a differential `n`-form on `E` taking values in `F` as `E → E [⋀^Fin n]→L[𝕜] F`.

## Implementation notes

There are a few competing definitions of the exterior derivative of a differential form
that differ from each other by a normalization factor.
We use the following one:

$$
dω(x; v_0, \dots, v_n) = \sum_{i=0}^n (-1)^i D_x ω(x; v_0, \dots, \widehat{v_i}, \dots, v_n) · v_i
$$

where $\widehat{v_i}$ means that we omit this element of the tuple, see `extDeriv_apply`.

## TODO

- Introduce notation for:
  - an unbundled `n`-form on a normed space;
  - a bundled `C^r`-smooth `n`-form on a normed space;
  - same for manifolds (not defined yet).
- Introduce bundled `C^r`-smooth `n`-forms on normed spaces and manifolds.
  - Discuss the future API and the use cases that need to be covered on Zulip.
  - Introduce new types & notation, copy the API.
- Add shorter and more readable definitions (or abbreviations?)
  for `0`-forms (`constOfIsEmpty`) and `1`-forms (`ofSubsingleton`),
  sync with the API for `ContinuousMultilinearMap`.
-/

@[expose] public section

open Filter ContinuousAlternatingMap Set
open scoped Topology

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n m k : Nat} {r : WithTop Nat∞}
  {ω ω₁ ω₂ : E -> E [⋀^Fin n]->L[𝕜] F} {s t : Set E} {x : E}

/--
Definition of `extDeriv` / `extDeriv` 的定义

English:
definition extDeriv
  signature: (ω : E -> E [⋀^Fin n]->L[𝕜] F) (x : E)
  body: .alternatizeUncurryFin (fderiv 𝕜 ω x)

中文:
定义 extDeriv
  签名: (ω : E -> E [⋀^有限集 n]->L[𝕜] F) (x : E)
  定义体: .alternatizeUncurryFin (fderiv 𝕜 ω x)

Depends on / 依赖: alternatizeUncurryFin, fderiv
-/
noncomputable def extDeriv (ω : E -> E [⋀^Fin n]->L[𝕜] F) (x : E) : E [⋀^Fin (n + 1)]->L[𝕜] F :=
  .alternatizeUncurryFin (fderiv 𝕜 ω x)

/--
Definition of `extDerivWithin` / `extDerivWithin` 的定义

English:
definition extDerivWithin
  signature: (ω : E -> E [⋀^Fin n]->L[𝕜] F) (s : Set E) (x : E)
  body: .alternatizeUncurryFin (fderivWithin 𝕜 ω s x)

@[simp]

中文:
定义 extDerivWithin
  签名: (ω : E -> E [⋀^有限集 n]->L[𝕜] F) (s : 集合 E) (x : E)
  定义体: .alternatizeUncurryFin (fderivWithin 𝕜 ω s x)

@[simp]

Depends on / 依赖: alternatizeUncurryFin, fderivWithin
-/
noncomputable def extDerivWithin (ω : E -> E [⋀^Fin n]->L[𝕜] F) (s : Set E) (x : E) :
    E [⋀^Fin (n + 1)]->L[𝕜] F :=
  .alternatizeUncurryFin (fderivWithin 𝕜 ω s x)

@[simp]
/--
theorem `extDerivWithin_univ` / 定理 `extDerivWithin_univ`

English:
theorem extDerivWithin_univ
  given: (ω : E -> E [⋀^Fin n]->L[𝕜] F)
  proof: by
  ext1 x
  rw [extDerivWithin]; rw [extDeriv]; rw [fderivWithin_univ]

中文:
定理 extDerivWithin_univ
  条件: (ω : E -> E [⋀^有限集 n]->L[𝕜] F)
  证明: by
  ext1 x
  rw [extDerivWithin]; rw [extDeriv]; rw [fderivWithin_univ]

Depends on / 依赖: extDeriv, extDerivWithin, fderivWithin_univ
-/
theorem extDerivWithin_univ (ω : E -> E [⋀^Fin n]->L[𝕜] F) :
    extDerivWithin ω univ = extDeriv ω := by
  ext1 x
  rw [extDerivWithin]; rw [extDeriv]; rw [fderivWithin_univ]

/--
theorem `extDerivWithin_add` / 定理 `extDerivWithin_add`

English:
theorem extDerivWithin_add
  statement: (hsx : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  simp [extDerivWithin, fderivWithin_add hsx hω₁ hω₂, alternatizeUncurryFin_add]

中文:
定理 extDerivWithin_add
  结论: (hsx : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  simp [extDerivWithin, fderivWithin_add hsx hω₁ hω₂, alternatizeUncurryFin_add]

Depends on / 依赖: alternatizeUncurryFin_add, extDerivWithin, fderivWithin_add
-/
theorem extDerivWithin_add (hsx : UniqueDiffWithinAt 𝕜 s x)
    (hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) :
    extDerivWithin (ω₁ + ω₂) s x = extDerivWithin ω₁ s x + extDerivWithin ω₂ s x := by
  simp [extDerivWithin, fderivWithin_add hsx hω₁ hω₂, alternatizeUncurryFin_add]

/--
theorem `extDerivWithin_fun_add` / 定理 `extDerivWithin_fun_add`

English:
theorem extDerivWithin_fun_add
  statement: (hsx : UniqueDiffWithinAt 𝕜 s x)
  proof: extDerivWithin_add hsx hω₁ hω₂

中文:
定理 extDerivWithin_fun_add
  结论: (hsx : UniqueDiffWithinAt 𝕜 s x)
  证明: extDerivWithin_add hsx hω₁ hω₂

Depends on / 依赖: extDerivWithin_add
-/
theorem extDerivWithin_fun_add (hsx : UniqueDiffWithinAt 𝕜 s x)
    (hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) :
    extDerivWithin (fun x => ω₁ x + ω₂ x) s x = extDerivWithin ω₁ s x + extDerivWithin ω₂ s x :=
  extDerivWithin_add hsx hω₁ hω₂

/--
theorem `extDeriv_add` / 定理 `extDeriv_add`

English:
theorem extDeriv_add
  given: (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x)
  proof: by
  simp [← extDerivWithin_univ, extDerivWithin_add, *, DifferentiableAt.differentiableWithinAt]

中文:
定理 extDeriv_add
  条件: (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x)
  证明: by
  simp [← extDerivWithin_univ, extDerivWithin_add, *, DifferentiableAt.differentiableWithinAt]

Depends on / 依赖: DifferentiableAt, DifferentiableAt.differentiableWithinAt, differentiableWithinAt, extDerivWithin_add, extDerivWithin_univ
-/
theorem extDeriv_add (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x) :
    extDeriv (ω₁ + ω₂) x = extDeriv ω₁ x + extDeriv ω₂ x := by
  simp [← extDerivWithin_univ, extDerivWithin_add, *, DifferentiableAt.differentiableWithinAt]

/--
theorem `extDeriv_fun_add` / 定理 `extDeriv_fun_add`

English:
theorem extDeriv_fun_add
  given: (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x)
  proof: extDeriv_add hω₁ hω₂

中文:
定理 extDeriv_fun_add
  条件: (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x)
  证明: extDeriv_add hω₁ hω₂

Depends on / 依赖: extDeriv_add
-/
theorem extDeriv_fun_add (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x) :
    extDeriv (fun x => ω₁ x + ω₂ x) x = extDeriv ω₁ x + extDeriv ω₂ x :=
  extDeriv_add hω₁ hω₂

/--
theorem `extDerivWithin_smul` / 定理 `extDerivWithin_smul`

English:
theorem extDerivWithin_smul
  given: (c : 𝕜) (ω : E -> E [⋀^Fin n]->L[𝕜] F) (hsx : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  simp [extDerivWithin, fderivWithin_const_smul_field, hsx, alternatizeUncurryFin_smul]

中文:
定理 extDerivWithin_smul
  条件: (c : 𝕜) (ω : E -> E [⋀^有限集 n]->L[𝕜] F) (hsx : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  simp [extDerivWithin, fderivWithin_const_smul_field, hsx, alternatizeUncurryFin_smul]

Depends on / 依赖: alternatizeUncurryFin_smul, extDerivWithin, fderivWithin_const_smul_field
-/
theorem extDerivWithin_smul (c : 𝕜) (ω : E -> E [⋀^Fin n]->L[𝕜] F) (hsx : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin (c • ω) s x = c • extDerivWithin ω s x := by
  simp [extDerivWithin, fderivWithin_const_smul_field, hsx, alternatizeUncurryFin_smul]

/--
theorem `extDerivWithin_fun_smul` / 定理 `extDerivWithin_fun_smul`

English:
theorem extDerivWithin_fun_smul
  statement: (c : 𝕜) (ω : E -> E [⋀^Fin n]->L[𝕜] F)
  proof: extDerivWithin_smul c ω hsx

中文:
定理 extDerivWithin_fun_smul
  结论: (c : 𝕜) (ω : E -> E [⋀^有限集 n]->L[𝕜] F)
  证明: extDerivWithin_smul c ω hsx

Depends on / 依赖: extDerivWithin_smul
-/
theorem extDerivWithin_fun_smul (c : 𝕜) (ω : E -> E [⋀^Fin n]->L[𝕜] F)
    (hsx : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin (fun x => c • ω x) s x = c • extDerivWithin ω s x :=
  extDerivWithin_smul c ω hsx

/--
theorem `extDeriv_smul` / 定理 `extDeriv_smul`

English:
theorem extDeriv_smul
  given: (c : 𝕜) (ω : E -> E [⋀^Fin n]->L[𝕜] F)
  proof: by
  simp [← extDerivWithin_univ, extDerivWithin_smul]

中文:
定理 extDeriv_smul
  条件: (c : 𝕜) (ω : E -> E [⋀^有限集 n]->L[𝕜] F)
  证明: by
  simp [← extDerivWithin_univ, extDerivWithin_smul]

Depends on / 依赖: extDerivWithin_smul, extDerivWithin_univ
-/
theorem extDeriv_smul (c : 𝕜) (ω : E -> E [⋀^Fin n]->L[𝕜] F) :
    extDeriv (c • ω) x = c • extDeriv ω x := by
  simp [← extDerivWithin_univ, extDerivWithin_smul]

/--
theorem `extDeriv_fun_smul` / 定理 `extDeriv_fun_smul`

English:
theorem extDeriv_fun_smul
  given: (c : 𝕜) (ω : E -> E [⋀^Fin n]->L[𝕜] F)
  proof: extDeriv_smul c ω

中文:
定理 extDeriv_fun_smul
  条件: (c : 𝕜) (ω : E -> E [⋀^有限集 n]->L[𝕜] F)
  证明: extDeriv_smul c ω

Depends on / 依赖: extDeriv_smul
-/
theorem extDeriv_fun_smul (c : 𝕜) (ω : E -> E [⋀^Fin n]->L[𝕜] F) :
    extDeriv (c • ω) x = c • extDeriv ω x :=
  extDeriv_smul c ω

/--
theorem `extDerivWithin_constOfIsEmpty` / 定理 `extDerivWithin_constOfIsEmpty`

English:
theorem extDerivWithin_constOfIsEmpty
  given: (f : E -> F) (hs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  simp only [extDerivWithin, ← constOfIsEmptyLIE_apply, ← Function.comp_def _ f,
    (constOfIsEmptyLIE 𝕜 E F (Fin 0)).comp_fderivWithin hs,
    alternatizeUncurryFin_constOfIsEmptyLIE_comp]

中文:
定理 extDerivWithin_constOfIsEmpty
  条件: (f : E -> F) (hs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  simp only [extDerivWithin, ← constOfIsEmptyLIE_apply, ← Function.comp_def _ f,
    (constOfIsEmptyLIE 𝕜 E F (Fin 0)).comp_fderivWithin hs,
    alternatizeUncurryFin_constOfIsEmptyLIE_comp]

Depends on / 依赖: Function, Function.comp_def, alternatizeUncurryFin_constOfIsEmptyLIE_comp, comp_def, comp_fderivWithin, constOfIsEmptyLIE, constOfIsEmptyLIE_apply, extDerivWithin
-/
theorem extDerivWithin_constOfIsEmpty (f : E -> F) (hs : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin (fun x => constOfIsEmpty 𝕜 E (Fin 0) (f x)) s x =
      .ofSubsingleton _ _ _ (0 : Fin 1) (fderivWithin 𝕜 f s x) := by
  simp only [extDerivWithin, ← constOfIsEmptyLIE_apply, ← Function.comp_def _ f,
    (constOfIsEmptyLIE 𝕜 E F (Fin 0)).comp_fderivWithin hs,
    alternatizeUncurryFin_constOfIsEmptyLIE_comp]

/--
theorem `extDeriv_constOfIsEmpty` / 定理 `extDeriv_constOfIsEmpty`

English:
theorem extDeriv_constOfIsEmpty
  given: (f : E -> F) (x : E)
  proof: by
  simp [← extDerivWithin_univ, extDerivWithin_constOfIsEmpty, fderivWithin_univ]

中文:
定理 extDeriv_constOfIsEmpty
  条件: (f : E -> F) (x : E)
  证明: by
  simp [← extDerivWithin_univ, extDerivWithin_constOfIsEmpty, fderivWithin_univ]

Depends on / 依赖: extDerivWithin_constOfIsEmpty, extDerivWithin_univ, fderivWithin_univ
-/
theorem extDeriv_constOfIsEmpty (f : E -> F) (x : E) :
    extDeriv (fun x => constOfIsEmpty 𝕜 E (Fin 0) (f x)) x =
      .ofSubsingleton _ _ _ (0 : Fin 1) (fderiv 𝕜 f x) := by
  simp [← extDerivWithin_univ, extDerivWithin_constOfIsEmpty, fderivWithin_univ]

/--
theorem `Filter.EventuallyEq.extDerivWithin_eq` / 定理 `Filter.EventuallyEq.extDerivWithin_eq`

English:
theorem Filter.EventuallyEq.extDerivWithin_eq
  given: (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x)
  proof: by
  simp only [extDerivWithin, alternatizeUncurryFin, hs.fderivWithin_eq hx]

中文:
定理 滤子.EventuallyEq.extDerivWithin_eq
  条件: (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x)
  证明: by
  simp only [extDerivWithin, alternatizeUncurryFin, hs.fderivWithin_eq hx]

Depends on / 依赖: alternatizeUncurryFin, extDerivWithin, fderivWithin_eq, hs.fderivWithin_eq
-/
theorem Filter.EventuallyEq.extDerivWithin_eq (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x := by
  simp only [extDerivWithin, alternatizeUncurryFin, hs.fderivWithin_eq hx]

/--
theorem `Filter.EventuallyEq.extDerivWithin_eq_of_mem` / 定理 `Filter.EventuallyEq.extDerivWithin_eq_of_mem`

English:
theorem Filter.EventuallyEq.extDerivWithin_eq_of_mem
  given: (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : x in s)
  proof: hs.extDerivWithin_eq (mem_of_mem_nhdsWithin hx hs :)

中文:
定理 滤子.EventuallyEq.extDerivWithin_eq_of_mem
  条件: (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : x in s)
  证明: hs.extDerivWithin_eq (mem_of_mem_nhdsWithin hx hs :)

Depends on / 依赖: extDerivWithin_eq, hs.extDerivWithin_eq, mem_of_mem_nhdsWithin
-/
theorem Filter.EventuallyEq.extDerivWithin_eq_of_mem (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : x in s) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  hs.extDerivWithin_eq (mem_of_mem_nhdsWithin hx hs :)

/--
theorem `Filter.EventuallyEq.extDerivWithin_eq_of_insert` / 定理 `Filter.EventuallyEq.extDerivWithin_eq_of_insert`

English:
theorem Filter.EventuallyEq.extDerivWithin_eq_of_insert
  given: (hs : ω₁ =ᶠ[𝓝[insert x s] x] ω₂)
  proof: by
  apply Filter.EventuallyEq.extDerivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)

中文:
定理 滤子.EventuallyEq.extDerivWithin_eq_of_insert
  条件: (hs : ω₁ =ᶠ[𝓝[insert x s] x] ω₂)
  证明: by
  apply Filter.EventuallyEq.extDerivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.extDerivWithin_eq, extDerivWithin_eq, mem_insert, mem_of_mem_nhdsWithin, nhdsWithin_mono, subset_insert
-/
theorem Filter.EventuallyEq.extDerivWithin_eq_of_insert (hs : ω₁ =ᶠ[𝓝[insert x s] x] ω₂) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x := by
  apply Filter.EventuallyEq.extDerivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)

/--
theorem `Filter.EventuallyEq.extDerivWithin'` / 定理 `Filter.EventuallyEq.extDerivWithin'`

English:
theorem Filter.EventuallyEq.extDerivWithin'
  given: (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (ht : t subseteq s)
  proof: (eventually_eventually_nhdsWithin.2 hs).mp eventually_mem_nhdsWithin.mono fun _y hys hs =>
    EventuallyEq.extDerivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)

中文:
定理 滤子.EventuallyEq.extDerivWithin'
  条件: (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (ht : t subseteq s)
  证明: (eventually_eventually_nhdsWithin.2 hs).mp eventually_mem_nhdsWithin.mono fun _y hys hs =>
    EventuallyEq.extDerivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)

Depends on / 依赖: EventuallyEq, EventuallyEq.extDerivWithin_eq, eventually_eventually_nhdsWithin, eventually_mem_nhdsWithin, eventually_mem_nhdsWithin.mono, extDerivWithin_eq, filter_mono, hs.filter_mono, hs.self_of_nhdsWithin, nhdsWithin_mono, self_of_nhdsWithin
-/
theorem Filter.EventuallyEq.extDerivWithin' (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (ht : t subseteq s) :
    extDerivWithin ω₁ t =ᶠ[𝓝[s] x] extDerivWithin ω₂ t :=
(eventually_eventually_nhdsWithin.2 hs).mp eventually_mem_nhdsWithin.mono fun _y hys hs =>
    EventuallyEq.extDerivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)

/--
theorem `Filter.EventuallyEq.extDerivWithin` / 定理 `Filter.EventuallyEq.extDerivWithin`

English:
theorem Filter.EventuallyEq.extDerivWithin
  given: (hs : ω₁ =ᶠ[𝓝[s] x] ω₂)
  proof: hs.extDerivWithin' .rfl

中文:
定理 滤子.EventuallyEq.extDerivWithin
  条件: (hs : ω₁ =ᶠ[𝓝[s] x] ω₂)
  证明: hs.extDerivWithin' .rfl
-/
protected theorem Filter.EventuallyEq.extDerivWithin (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) :
    extDerivWithin ω₁ s =ᶠ[𝓝[s] x] extDerivWithin ω₂ s :=
  hs.extDerivWithin' .rfl

/--
theorem `Filter.EventuallyEq.extDerivWithin_eq_nhds` / 定理 `Filter.EventuallyEq.extDerivWithin_eq_nhds`

English:
theorem Filter.EventuallyEq.extDerivWithin_eq_nhds
  given: (h : ω₁ =ᶠ[𝓝 x] ω₂)
  proof: (h.filter_mono nhdsWithin_le_nhds).extDerivWithin_eq h.self_of_nhds

中文:
定理 滤子.EventuallyEq.extDerivWithin_eq_nhds
  条件: (h : ω₁ =ᶠ[𝓝 x] ω₂)
  证明: (h.filter_mono nhdsWithin_le_nhds).extDerivWithin_eq h.self_of_nhds

Depends on / 依赖: extDerivWithin_eq, filter_mono, h.filter_mono, h.self_of_nhds, nhdsWithin_le_nhds, self_of_nhds
-/
theorem Filter.EventuallyEq.extDerivWithin_eq_nhds (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  (h.filter_mono nhdsWithin_le_nhds).extDerivWithin_eq h.self_of_nhds

/--
theorem `extDerivWithin_congr` / 定理 `extDerivWithin_congr`

English:
theorem extDerivWithin_congr
  given: (hs : EqOn ω₁ ω₂ s) (hx : ω₁ x = ω₂ x)
  proof: (hs.eventuallyEq.filter_mono inf_le_right).extDerivWithin_eq hx

中文:
定理 extDerivWithin_congr
  条件: (hs : EqOn ω₁ ω₂ s) (hx : ω₁ x = ω₂ x)
  证明: (hs.eventuallyEq.filter_mono inf_le_right).extDerivWithin_eq hx

Depends on / 依赖: eventuallyEq, extDerivWithin_eq, filter_mono, hs.eventuallyEq.filter_mono, inf_le_right
-/
theorem extDerivWithin_congr (hs : EqOn ω₁ ω₂ s) (hx : ω₁ x = ω₂ x) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).extDerivWithin_eq hx

/--
theorem `extDerivWithin_congr'` / 定理 `extDerivWithin_congr'`

English:
theorem extDerivWithin_congr'
  given: (hs : EqOn ω₁ ω₂ s) (hx : x in s)
  proof: extDerivWithin_congr hs (hs hx)

中文:
定理 extDerivWithin_congr'
  条件: (hs : EqOn ω₁ ω₂ s) (hx : x in s)
  证明: extDerivWithin_congr hs (hs hx)

Depends on / 依赖: extDerivWithin_congr
-/
theorem extDerivWithin_congr' (hs : EqOn ω₁ ω₂ s) (hx : x in s) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  extDerivWithin_congr hs (hs hx)

/--
theorem `Filter.EventuallyEq.extDeriv` / 定理 `Filter.EventuallyEq.extDeriv`

English:
theorem Filter.EventuallyEq.extDeriv
  given: (h : ω₁ =ᶠ[𝓝 x] ω₂)
  proof: by
  simp only [← nhdsWithin_univ, ← extDerivWithin_univ] at *
  exact h.extDerivWithin

中文:
定理 滤子.EventuallyEq.extDeriv
  条件: (h : ω₁ =ᶠ[𝓝 x] ω₂)
  证明: by
  simp only [← nhdsWithin_univ, ← extDerivWithin_univ] at *
  exact h.extDerivWithin
-/
protected theorem Filter.EventuallyEq.extDeriv (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    extDeriv ω₁ =ᶠ[𝓝 x] extDeriv ω₂ := by
  simp only [← nhdsWithin_univ, ← extDerivWithin_univ] at *
  exact h.extDerivWithin

/--
theorem `Filter.EventuallyEq.extDeriv_eq` / 定理 `Filter.EventuallyEq.extDeriv_eq`

English:
theorem Filter.EventuallyEq.extDeriv_eq
  given: (h : ω₁ =ᶠ[𝓝 x] ω₂)
  statement: extDeriv ω₁ x = extDeriv ω₂ x
  proof: h.extDeriv.self_of_nhds

中文:
定理 滤子.EventuallyEq.extDeriv_eq
  条件: (h : ω₁ =ᶠ[𝓝 x] ω₂)
  结论: extDeriv ω₁ x = extDeriv ω₂ x
  证明: h.extDeriv.self_of_nhds

Depends on / 依赖: extDeriv, h.extDeriv.self_of_nhds, self_of_nhds
-/
theorem Filter.EventuallyEq.extDeriv_eq (h : ω₁ =ᶠ[𝓝 x] ω₂) : extDeriv ω₁ x = extDeriv ω₂ x :=
  h.extDeriv.self_of_nhds

/--
theorem `extDerivWithin_apply` / 定理 `extDerivWithin_apply`

English:
theorem extDerivWithin_apply
  statement: (h : DifferentiableWithinAt 𝕜 ω s x) (hs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  simp [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    fderivWithin_continuousAlternatingMap_apply_const_apply, *]

中文:
定理 extDerivWithin_apply
  结论: (h : DifferentiableWithinAt 𝕜 ω s x) (hs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  simp [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    fderivWithin_continuousAlternatingMap_apply_const_apply, *]

Depends on / 依赖: ContinuousAlternatingMap, ContinuousAlternatingMap.alternatizeUncurryFin_apply, alternatizeUncurryFin_apply, extDerivWithin, fderivWithin_continuousAlternatingMap_apply_const_apply
-/
theorem extDerivWithin_apply (h : DifferentiableWithinAt 𝕜 ω s x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (v : Fin (n + 1) -> E) :
    extDerivWithin ω s x v =
      ∑ i, (-1) ^ i.val • fderivWithin 𝕜 (ω · (i.removeNth v)) s x (v i) := by
  simp [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    fderivWithin_continuousAlternatingMap_apply_const_apply, *]

/--
theorem `extDeriv_apply` / 定理 `extDeriv_apply`

English:
theorem extDeriv_apply
  given: (h : DifferentiableAt 𝕜 ω x) (v : Fin (n + 1) -> E)
  proof: by
  simp [← extDerivWithin_univ, extDerivWithin_apply h.differentiableWithinAt]

中文:
定理 extDeriv_apply
  条件: (h : DifferentiableAt 𝕜 ω x) (v : 有限集 (n + 1) -> E)
  证明: by
  simp [← extDerivWithin_univ, extDerivWithin_apply h.differentiableWithinAt]

Depends on / 依赖: differentiableWithinAt, extDerivWithin_apply, extDerivWithin_univ, h.differentiableWithinAt
-/
theorem extDeriv_apply (h : DifferentiableAt 𝕜 ω x) (v : Fin (n + 1) -> E) :
    extDeriv ω x v = ∑ i, (-1) ^ i.val • fderiv 𝕜 (ω · (i.removeNth v)) x (v i) := by
  simp [← extDerivWithin_univ, extDerivWithin_apply h.differentiableWithinAt]

/--
theorem `extDerivWithin_extDerivWithin_apply` / 定理 `extDerivWithin_extDerivWithin_apply`

English:
theorem extDerivWithin_extDerivWithin_apply
  statement: (hω : ContDiffWithinAt 𝕜 r ω s x)
  proof: calc
  extDerivWithin (extDerivWithin ω s) s x
    = alternatizeUncurryFin (fderivWithin 𝕜 (fun y =>
        alternatizeUncurryFin (fderivWithin 𝕜 ω s y)) s x) := rfl
  _ = alternatizeUncurryFin (alternatizeUncurryFinCLM _ _ _ ∘L
        fderivWithin 𝕜 (fderivWithin 𝕜 ω s) s x) := by
    congr 1
   

中文:
定理 extDerivWithin_extDerivWithin_apply
  结论: (hω : ContDiffWithinAt 𝕜 r ω s x)
  证明: calc
  extDerivWithin (extDerivWithin ω s) s x
    = alternatizeUncurryFin (fderivWithin 𝕜 (fun y =>
        alternatizeUncurryFin (fderivWithin 𝕜 ω s y)) s x) := rfl
  _ = alternatizeUncurryFin (alternatizeUncurryFinCLM _ _ _ ∘L
        fderivWithin 𝕜 (fderivWithin 𝕜 ω s) s x) := by
    congr 1
   
-/
theorem extDerivWithin_extDerivWithin_apply (hω : ContDiffWithinAt 𝕜 r ω s x)
    (hr : minSmoothness 𝕜 2 <= r) (hs : UniqueDiffOn 𝕜 s) (hx : x in closure (interior s))
    (h'x : x in s) : extDerivWithin (extDerivWithin ω s) s x = 0 := calc
  extDerivWithin (extDerivWithin ω s) s x
    = alternatizeUncurryFin (fderivWithin 𝕜 (fun y =>
        alternatizeUncurryFin (fderivWithin 𝕜 ω s y)) s x) := rfl
  _ = alternatizeUncurryFin (alternatizeUncurryFinCLM _ _ _ ∘L
        fderivWithin 𝕜 (fderivWithin 𝕜 ω s) s x) := by
    congr 1
    have : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 ω s) s x := by
      refine (hω.fderivWithin_right hs ?_ h'x).differentiableWithinAt one_ne_zero
      exact le_minSmoothness.trans hr
.hasFDerivAt.comp_hasFDerivWithinAt x exact alternatizeUncurryFinCLM _ _ _
.fderivWithin (hs.uniqueDiffWithinAt h'x) this.hasFDerivWithinAt
_ = 0 := alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric
    hω.isSymmSndFDerivWithinAt hr hs hx h'x

/--
theorem `extDerivWithin_extDerivWithin_eqOn` / 定理 `extDerivWithin_extDerivWithin_eqOn`

English:
theorem extDerivWithin_extDerivWithin_eqOn
  statement: (hω : ContDiffOn 𝕜 r ω s) (hr : minSmoothness 𝕜 2 <= r)
  proof: by
  rintro x ⟨h'x, hx⟩
  exact extDerivWithin_extDerivWithin_apply (hω.contDiffWithinAt h'x) hr hs hx h'x

中文:
定理 extDerivWithin_extDerivWithin_eqOn
  结论: (hω : ContDiffOn 𝕜 r ω s) (hr : minSmoothness 𝕜 2 <= r)
  证明: by
  rintro x ⟨h'x, hx⟩
  exact extDerivWithin_extDerivWithin_apply (hω.contDiffWithinAt h'x) hr hs hx h'x

Depends on / 依赖: contDiffWithinAt, extDerivWithin_extDerivWithin_apply
-/
theorem extDerivWithin_extDerivWithin_eqOn (hω : ContDiffOn 𝕜 r ω s) (hr : minSmoothness 𝕜 2 <= r)
    (hs : UniqueDiffOn 𝕜 s) :
    EqOn (extDerivWithin (extDerivWithin ω s) s) 0 (s inter closure (interior s)) := by
  rintro x ⟨h'x, hx⟩
  exact extDerivWithin_extDerivWithin_apply (hω.contDiffWithinAt h'x) hr hs hx h'x

/--
theorem `extDeriv_extDeriv_apply` / 定理 `extDeriv_extDeriv_apply`

English:
theorem extDeriv_extDeriv_apply
  given: (hω : ContDiffAt 𝕜 r ω x) (hr : minSmoothness 𝕜 2 <= r)
  proof: by
  simp only [← extDerivWithin_univ]
  apply extDerivWithin_extDerivWithin_apply (s := univ) hω.contDiffWithinAt hr <;> simp

中文:
定理 extDeriv_extDeriv_apply
  条件: (hω : ContDiffAt 𝕜 r ω x) (hr : minSmoothness 𝕜 2 <= r)
  证明: by
  simp only [← extDerivWithin_univ]
  apply extDerivWithin_extDerivWithin_apply (s := univ) hω.contDiffWithinAt hr <;> simp

Depends on / 依赖: contDiffWithinAt, extDerivWithin_extDerivWithin_apply, extDerivWithin_univ
-/
theorem extDeriv_extDeriv_apply (hω : ContDiffAt 𝕜 r ω x) (hr : minSmoothness 𝕜 2 <= r) :
    extDeriv (extDeriv ω) x = 0 := by
  simp only [← extDerivWithin_univ]
  apply extDerivWithin_extDerivWithin_apply (s := univ) hω.contDiffWithinAt hr <;> simp

/--
theorem `extDeriv_extDeriv` / 定理 `extDeriv_extDeriv`

English:
theorem extDeriv_extDeriv
  given: (h : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 <= r)
  proof: funext fun _ => extDeriv_extDeriv_apply h.contDiffAt hr

中文:
定理 extDeriv_extDeriv
  条件: (h : 连续可微 𝕜 r ω) (hr : minSmoothness 𝕜 2 <= r)
  证明: funext fun _ => extDeriv_extDeriv_apply h.contDiffAt hr

Depends on / 依赖: contDiffAt, extDeriv_extDeriv_apply, h.contDiffAt
-/
theorem extDeriv_extDeriv (h : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 <= r) :
    extDeriv (extDeriv ω) = 0 :=
  funext fun _ => extDeriv_extDeriv_apply h.contDiffAt hr

/--
theorem `extDerivWithin_pullback` / 定理 `extDerivWithin_pullback`

English:
theorem extDerivWithin_pullback
  statement: {ω : F -> F [⋀^Fin n]->L[𝕜] G} {f : E -> F} {t : Set F}
  proof: by
  have hdf : DifferentiableWithinAt 𝕜 f s x :=
hf.differentiableWithinAt (two_pos.trans_le <| le_minSmoothness.trans hr).ne'
  have hd2f : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 f s) s x :=
    (hf.fderivWithin_right hs (le_minSmoothness.trans hr) hxs).differentiableWithinAt one_ne_zero
  rw [e

中文:
定理 extDerivWithin_pullback
  结论: {ω : F -> F [⋀^有限集 n]->L[𝕜] G} {f : E -> F} {t : 集合 F}
  证明: by
  have hdf : DifferentiableWithinAt 𝕜 f s x :=
hf.differentiableWithinAt (two_pos.trans_le <| le_minSmoothness.trans hr).ne'
  have hd2f : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 f s) s x :=
    (hf.fderivWithin_right hs (le_minSmoothness.trans hr) hxs).differentiableWithinAt one_ne_zero
  rw [e

Depends on / 依赖: DifferentiableWithinAt, alternatizeUncurryFin_add, differentiableWithinAt, extDerivWithin, fderivWithin, fderivWithin_continuousAlternatingMapCompContinuousLinearMap, fderivWithin_fun_comp, fderivWithin_right, hf.differentiableWithinAt, hf.fderivWithin_right, le_minSmoothness, le_minSmoothness.trans, one_ne_zero, trans_le, two_pos, two_pos.trans_le
-/
theorem extDerivWithin_pullback {ω : F -> F [⋀^Fin n]->L[𝕜] G} {f : E -> F} {t : Set F}
    (hω : DifferentiableWithinAt 𝕜 ω t (f x)) (hf : ContDiffWithinAt 𝕜 r f s x)
    (hr : minSmoothness 𝕜 2 <= r) (hs : UniqueDiffOn 𝕜 s)
    (hxc : x in closure (interior s)) (hxs : x in s) (hst : MapsTo f s t) :
    extDerivWithin (fun x => (ω (f x)).compContinuousLinearMap (fderivWithin 𝕜 f s x)) s x =
      (extDerivWithin ω t (f x)).compContinuousLinearMap (fderivWithin 𝕜 f s x) := by
  have hdf : DifferentiableWithinAt 𝕜 f s x :=
hf.differentiableWithinAt (two_pos.trans_le <| le_minSmoothness.trans hr).ne'
  have hd2f : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 f s) s x :=
    (hf.fderivWithin_right hs (le_minSmoothness.trans hr) hxs).differentiableWithinAt one_ne_zero
  rw [extDerivWithin]; rw [fderivWithin_continuousAlternatingMapCompContinuousLinearMap (by exact hω.comp x hdf hst) hd2f
      (hs x hxs)]; rw [alternatizeUncurryFin_add]; rw [fderivWithin_fun_comp _ hω hdf hst (hs x hxs)]; rw [extDerivWithin]; rw [alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero]; rw [add_zero]
  · ext v
    simp +unfoldPartialApp [alternatizeUncurryFin_apply, Fin.removeNth, Function.comp_def]
  · apply hf.isSymmSndFDerivWithinAt <;> assumption

/--
theorem `extDeriv_pullback` / 定理 `extDeriv_pullback`

English:
theorem extDeriv_pullback
  statement: {ω : F -> F [⋀^Fin n]->L[𝕜] G} {f : E -> F}
  proof: by
  simp only [← differentiableWithinAt_univ, ← extDerivWithin_univ, ← contDiffWithinAt_univ,
    ← fderivWithin_univ] at *
  apply extDerivWithin_pullback (r := r) <;> simp [*]

中文:
定理 extDeriv_pullback
  结论: {ω : F -> F [⋀^有限集 n]->L[𝕜] G} {f : E -> F}
  证明: by
  simp only [← differentiableWithinAt_univ, ← extDerivWithin_univ, ← contDiffWithinAt_univ,
    ← fderivWithin_univ] at *
  apply extDerivWithin_pullback (r := r) <;> simp [*]

Depends on / 依赖: contDiffWithinAt_univ, differentiableWithinAt_univ, extDerivWithin_pullback, extDerivWithin_univ, fderivWithin_univ
-/
theorem extDeriv_pullback {ω : F -> F [⋀^Fin n]->L[𝕜] G} {f : E -> F}
    (hω : DifferentiableAt 𝕜 ω (f x)) (hf : ContDiffAt 𝕜 r f x) (hr : minSmoothness 𝕜 2 <= r) :
    extDeriv (fun x => (ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x)) x =
      (extDeriv ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x) := by
  simp only [← differentiableWithinAt_univ, ← extDerivWithin_univ, ← contDiffWithinAt_univ,
    ← fderivWithin_univ] at *
  apply extDerivWithin_pullback (r := r) <;> simp [*]
