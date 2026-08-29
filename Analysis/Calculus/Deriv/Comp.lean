/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel, Yury Kudryashov, Yuyang Zhao
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# One-dimensional derivatives of compositions of functions

In this file we prove the chain rule for the following cases:

* `HasDerivAt.comp` etc: `f : 𝕜' → 𝕜'` composed with `g : 𝕜 → 𝕜'`;
* `HasDerivAt.scomp` etc: `f : 𝕜' → E` composed with `g : 𝕜 → 𝕜'`;
* `HasFDerivAt.comp_hasDerivAt` etc: `f : E → F` composed with `g : 𝕜 → E`;

Here `𝕜` is the base normed field, `E` and `F` are normed spaces over `𝕜` and `𝕜'` is an algebra
over `𝕜` (e.g., `𝕜'=𝕜` or `𝕜=ℝ`, `𝕜'=ℂ`).

We also give versions with the `of_eq` suffix, which require an equality proof instead
of definitional equality of the different points used in the composition. These versions are
often more flexible to use.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, chain rule
-/

public section


universe u v w

open scoped Topology Filter ENNReal

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : 𝕜 -> F}
variable {f' : F}
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {L : Filter (𝕜 × 𝕜)}

section Composition

/-!
### Derivative of the composition of a vector function and a scalar function

We use `scomp` in lemmas on composition of vector-valued and scalar-valued functions, and `comp`
in lemmas on composition of scalar-valued functions, in analogy for `smul` and `mul` (and also
because the `comp` version with the shorter name will show up much more often in applications).
The formula for the derivative involves `smul` in `scomp` lemmas, which can be reduced to
usual multiplication in `comp` lemmas.
-/


/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {s' t' : Set 𝕜'} {h : 𝕜 -> 𝕜'} {h₂ : 𝕜' -> 𝕜'} {h' h₂' : 𝕜'}
  {g₁ : 𝕜' -> F} {g₁' : F} {L' : Filter (𝕜' × 𝕜')} {y : 𝕜'} (x)

/--
theorem `HasDerivAtFilter.scomp` / 定理 `HasDerivAtFilter.scomp`

English:
theorem HasDerivAtFilter.scomp
  statement: (hg : HasDerivAtFilter g₁ g₁' L')
  proof: by
  simpa using ((hg.hasFDerivAtFilter.restrictScalars 𝕜).comp hh hL).hasDerivAtFilter

@[deprecated HasDerivAtFilter.scomp (since := "2026-02-17")]

中文:
定理 HasDerivAtFilter.scomp
  结论: (hg : HasDerivAtFilter g₁ g₁' L')
  证明: by
  simpa using ((hg.hasFDerivAtFilter.restrictScalars 𝕜).comp hh hL).hasDerivAtFilter

@[deprecated HasDerivAtFilter.scomp (since := "2026-02-17")]

Depends on / 依赖: hasDerivAtFilter, hasFDerivAtFilter, hg.hasFDerivAtFilter.restrictScalars, restrictScalars
-/
theorem HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁ g₁' L')
    (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') :
    HasDerivAtFilter (g₁ ∘ h) (h' • g₁') L := by
  simpa using ((hg.hasFDerivAtFilter.restrictScalars 𝕜).comp hh hL).hasDerivAtFilter

@[deprecated HasDerivAtFilter.scomp (since := "2026-02-17")]
/--
theorem `HasDerivAtFilter.scomp_of_eq` / 定理 `HasDerivAtFilter.scomp_of_eq`

English:
theorem HasDerivAtFilter.scomp_of_eq
  statement: {L : Filter 𝕜} {L' : Filter 𝕜'}
  proof: hg.scomp hh .prodMap hL by simp [hy]

中文:
定理 HasDerivAtFilter.scomp_of_eq
  结论: {L : Filter 𝕜} {L' : Filter 𝕜'}
  证明: hg.scomp hh .prodMap hL by simp [hy]

Depends on / 依赖: hg.scomp, prodMap
-/
theorem HasDerivAtFilter.scomp_of_eq {L : Filter 𝕜} {L' : Filter 𝕜'}
    (hg : HasDerivAtFilter g₁ g₁' (L' ×ˢ pure y)) (hh : HasDerivAtFilter h h' (L ×ˢ pure x))
    (hy : y = h x) (hL : Tendsto h L L') :
    HasDerivAtFilter (g₁ ∘ h) (h' • g₁') (L ×ˢ pure x) :=
hg.scomp hh .prodMap hL by simp [hy]

/--
theorem `HasDerivWithinAt.scomp_hasDerivAt` / 定理 `HasDerivWithinAt.scomp_hasDerivAt`

English:
theorem HasDerivWithinAt.scomp_hasDerivAt
  statement: (hg : HasDerivWithinAt g₁ g₁' s' (h x))
  proof: hg.scomp hh .prodMap (tendsto_nhdsWithin_iff.mpr ⟨hh.continuousAt, .of_forall hs⟩)
    (tendsto_pure_pure _ _)

中文:
定理 HasDerivWithinAt.scomp_hasDerivAt
  结论: (hg : HasDerivWithinAt g₁ g₁' s' (h x))
  证明: hg.scomp hh .prodMap (tendsto_nhdsWithin_iff.mpr ⟨hh.continuousAt, .of_forall hs⟩)
    (tendsto_pure_pure _ _)

Depends on / 依赖: continuousAt, hg.scomp, hh.continuousAt, of_forall, prodMap, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mpr, tendsto_pure_pure
-/
theorem HasDerivWithinAt.scomp_hasDerivAt (hg : HasDerivWithinAt g₁ g₁' s' (h x))
    (hh : HasDerivAt h h' x) (hs : forall x, h x in s') : HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
hg.scomp hh .prodMap (tendsto_nhdsWithin_iff.mpr ⟨hh.continuousAt, .of_forall hs⟩)
    (tendsto_pure_pure _ _)

/--
theorem `HasDerivWithinAt.scomp_hasDerivAt_of_eq` / 定理 `HasDerivWithinAt.scomp_hasDerivAt_of_eq`

English:
theorem HasDerivWithinAt.scomp_hasDerivAt_of_eq
  statement: (hg : HasDerivWithinAt g₁ g₁' s' y)
  proof: by
  rw [hy] at hg; exact hg.scomp_hasDerivAt x hh hs

中文:
定理 HasDerivWithinAt.scomp_hasDerivAt_of_eq
  结论: (hg : HasDerivWithinAt g₁ g₁' s' y)
  证明: by
  rw [hy] at hg; exact hg.scomp_hasDerivAt x hh hs

Depends on / 依赖: hg.scomp_hasDerivAt, scomp_hasDerivAt
-/
theorem HasDerivWithinAt.scomp_hasDerivAt_of_eq (hg : HasDerivWithinAt g₁ g₁' s' y)
    (hh : HasDerivAt h h' x) (hs : forall x, h x in s') (hy : y = h x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x := by
  rw [hy] at hg; exact hg.scomp_hasDerivAt x hh hs

/--
theorem `HasDerivWithinAt.scomp` / 定理 `HasDerivWithinAt.scomp`

English:
theorem HasDerivWithinAt.scomp
  statement: (hg : HasDerivWithinAt g₁ g₁' t' (h x))
  proof: HasDerivAtFilter.scomp hg hh .prodMap hh.continuousWithinAt.tendsto_nhdsWithin hst
    tendsto_pure_pure ..

中文:
定理 HasDerivWithinAt.scomp
  结论: (hg : HasDerivWithinAt g₁ g₁' t' (h x))
  证明: HasDerivAtFilter.scomp hg hh .prodMap hh.continuousWithinAt.tendsto_nhdsWithin hst
    tendsto_pure_pure ..

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.scomp, continuousWithinAt, hh.continuousWithinAt.tendsto_nhdsWithin, prodMap, tendsto_nhdsWithin, tendsto_pure_pure
-/
theorem HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁ g₁' t' (h x))
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
HasDerivAtFilter.scomp hg hh .prodMap hh.continuousWithinAt.tendsto_nhdsWithin hst
    tendsto_pure_pure ..

/--
theorem `HasDerivWithinAt.scomp_of_eq` / 定理 `HasDerivWithinAt.scomp_of_eq`

English:
theorem HasDerivWithinAt.scomp_of_eq
  statement: (hg : HasDerivWithinAt g₁ g₁' t' y)
  proof: by
  rw [hy] at hg; exact hg.scomp x hh hst

中文:
定理 HasDerivWithinAt.scomp_of_eq
  结论: (hg : HasDerivWithinAt g₁ g₁' t' y)
  证明: by
  rw [hy] at hg; exact hg.scomp x hh hst

Depends on / 依赖: hg.scomp
-/
theorem HasDerivWithinAt.scomp_of_eq (hg : HasDerivWithinAt g₁ g₁' t' y)
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') (hy : y = h x) :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x := by
  rw [hy] at hg; exact hg.scomp x hh hst

/--
theorem `HasDerivAt.scomp` / 定理 `HasDerivAt.scomp`

English:
theorem HasDerivAt.scomp
  given: (hg : HasDerivAt g₁ g₁' (h x)) (hh : HasDerivAt h h' x)
  proof: HasDerivAtFilter.scomp hg hh hh.continuousAt.tendsto.prodMap tendsto_pure_pure _ _

中文:
定理 HasDerivAt.scomp
  条件: (hg : HasDerivAt g₁ g₁' (h x)) (hh : HasDerivAt h h' x)
  证明: HasDerivAtFilter.scomp hg hh hh.continuousAt.tendsto.prodMap tendsto_pure_pure _ _

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.scomp, continuousAt, hh.continuousAt.tendsto.prodMap, prodMap, tendsto, tendsto_pure_pure
-/
theorem HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
HasDerivAtFilter.scomp hg hh hh.continuousAt.tendsto.prodMap tendsto_pure_pure _ _

/--
theorem `HasDerivAt.scomp_of_eq` / 定理 `HasDerivAt.scomp_of_eq`

English:
theorem HasDerivAt.scomp_of_eq
  proof: by
  rw [hy] at hg; exact hg.scomp x hh

中文:
定理 HasDerivAt.scomp_of_eq
  证明: by
  rw [hy] at hg; exact hg.scomp x hh

Depends on / 依赖: hg.scomp
-/
theorem HasDerivAt.scomp_of_eq
    (hg : HasDerivAt g₁ g₁' y) (hh : HasDerivAt h h' x) (hy : y = h x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x := by
  rw [hy] at hg; exact hg.scomp x hh

/--
theorem `HasStrictDerivAt.scomp` / 定理 `HasStrictDerivAt.scomp`

English:
theorem HasStrictDerivAt.scomp
  given: (hg : HasStrictDerivAt g₁ g₁' (h x)) (hh : HasStrictDerivAt h h' x)
  proof: HasDerivAtFilter.scomp hg hh
    hh.hasStrictFDerivAt.continuousAt.prodMap hh.hasStrictFDerivAt.continuousAt

中文:
定理 HasStrictDerivAt.scomp
  条件: (hg : HasStrictDerivAt g₁ g₁' (h x)) (hh : HasStrictDerivAt h h' x)
  证明: HasDerivAtFilter.scomp hg hh
    hh.hasStrictFDerivAt.continuousAt.prodMap hh.hasStrictFDerivAt.continuousAt

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.scomp, continuousAt, hasStrictFDerivAt, hh.hasStrictFDerivAt.continuousAt, hh.hasStrictFDerivAt.continuousAt.prodMap, prodMap
-/
theorem HasStrictDerivAt.scomp (hg : HasStrictDerivAt g₁ g₁' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (g₁ ∘ h) (h' • g₁') x :=
HasDerivAtFilter.scomp hg hh
    hh.hasStrictFDerivAt.continuousAt.prodMap hh.hasStrictFDerivAt.continuousAt

/--
theorem `HasStrictDerivAt.scomp_of_eq` / 定理 `HasStrictDerivAt.scomp_of_eq`

English:
theorem HasStrictDerivAt.scomp_of_eq
  proof: by
  rw [hy] at hg; exact hg.scomp x hh

中文:
定理 HasStrictDerivAt.scomp_of_eq
  证明: by
  rw [hy] at hg; exact hg.scomp x hh

Depends on / 依赖: hg.scomp
-/
theorem HasStrictDerivAt.scomp_of_eq
    (hg : HasStrictDerivAt g₁ g₁' y) (hh : HasStrictDerivAt h h' x) (hy : y = h x) :
    HasStrictDerivAt (g₁ ∘ h) (h' • g₁') x := by
  rw [hy] at hg; exact hg.scomp x hh

/--
theorem `HasDerivAt.scomp_hasDerivWithinAt` / 定理 `HasDerivAt.scomp_hasDerivWithinAt`

English:
theorem HasDerivAt.scomp_hasDerivWithinAt
  statement: (hg : HasDerivAt g₁ g₁' (h x))
  proof: HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh (mapsTo_univ _ _)

中文:
定理 HasDerivAt.scomp_hasDerivWithinAt
  结论: (hg : HasDerivAt g₁ g₁' (h x))
  证明: HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh (mapsTo_univ _ _)

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.scomp, hasDerivWithinAt, hg.hasDerivWithinAt, mapsTo_univ
-/
theorem HasDerivAt.scomp_hasDerivWithinAt (hg : HasDerivAt g₁ g₁' (h x))
    (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
  HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh (mapsTo_univ _ _)

/--
theorem `HasDerivAt.scomp_hasDerivWithinAt_of_eq` / 定理 `HasDerivAt.scomp_hasDerivWithinAt_of_eq`

English:
theorem HasDerivAt.scomp_hasDerivWithinAt_of_eq
  statement: (hg : HasDerivAt g₁ g₁' y)
  proof: by
  rw [hy] at hg; exact hg.scomp_hasDerivWithinAt x hh

中文:
定理 HasDerivAt.scomp_hasDerivWithinAt_of_eq
  结论: (hg : HasDerivAt g₁ g₁' y)
  证明: by
  rw [hy] at hg; exact hg.scomp_hasDerivWithinAt x hh

Depends on / 依赖: hg.scomp_hasDerivWithinAt, scomp_hasDerivWithinAt
-/
theorem HasDerivAt.scomp_hasDerivWithinAt_of_eq (hg : HasDerivAt g₁ g₁' y)
    (hh : HasDerivWithinAt h h' s x) (hy : y = h x) :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x := by
  rw [hy] at hg; exact hg.scomp_hasDerivWithinAt x hh

/--
theorem `derivWithin.scomp` / 定理 `derivWithin.scomp`

English:
theorem derivWithin.scomp
  statement: (hg : DifferentiableWithinAt 𝕜' g₁ t' (h x))
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin.scomp
  结论: (hg : DifferentiableWithinAt 𝕜' g₁ t' (h x))
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.scomp, UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hg.hasDerivWithinAt, hh.hasDerivWithinAt
-/
theorem derivWithin.scomp (hg : DifferentiableWithinAt 𝕜' g₁ t' (h x))
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t') :
    derivWithin (g₁ ∘ h) s x = derivWithin h s x • derivWithin g₁ t' (h x) := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `derivWithin.scomp_of_eq` / 定理 `derivWithin.scomp_of_eq`

English:
theorem derivWithin.scomp_of_eq
  statement: (hg : DifferentiableWithinAt 𝕜' g₁ t' y)
  proof: by
  rw [hy] at hg; exact derivWithin.scomp x hg hh hs

中文:
定理 derivWithin.scomp_of_eq
  结论: (hg : DifferentiableWithinAt 𝕜' g₁ t' y)
  证明: by
  rw [hy] at hg; exact derivWithin.scomp x hg hh hs

Depends on / 依赖: derivWithin, derivWithin.scomp
-/
theorem derivWithin.scomp_of_eq (hg : DifferentiableWithinAt 𝕜' g₁ t' y)
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t')
    (hy : y = h x) :
    derivWithin (g₁ ∘ h) s x = derivWithin h s x • derivWithin g₁ t' (h x) := by
  rw [hy] at hg; exact derivWithin.scomp x hg hh hs

/--
theorem `deriv.scomp` / 定理 `deriv.scomp`

English:
theorem deriv.scomp
  given: (hg : DifferentiableAt 𝕜' g₁ (h x)) (hh : DifferentiableAt 𝕜 h x)
  proof: (HasDerivAt.scomp x hg.hasDerivAt hh.hasDerivAt).deriv

中文:
定理 deriv.scomp
  条件: (hg : DifferentiableAt 𝕜' g₁ (h x)) (hh : DifferentiableAt 𝕜 h x)
  证明: (HasDerivAt.scomp x hg.hasDerivAt hh.hasDerivAt).deriv

Depends on / 依赖: HasDerivAt, HasDerivAt.scomp, hasDerivAt, hg.hasDerivAt, hh.hasDerivAt
-/
theorem deriv.scomp (hg : DifferentiableAt 𝕜' g₁ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x) :=
  (HasDerivAt.scomp x hg.hasDerivAt hh.hasDerivAt).deriv

/--
theorem `deriv.scomp_of_eq` / 定理 `deriv.scomp_of_eq`

English:
theorem deriv.scomp_of_eq
  proof: by
  rw [hy] at hg; exact deriv.scomp x hg hh

中文:
定理 deriv.scomp_of_eq
  证明: by
  rw [hy] at hg; exact deriv.scomp x hg hh

Depends on / 依赖: deriv.scomp
-/
theorem deriv.scomp_of_eq
    (hg : DifferentiableAt 𝕜' g₁ y) (hh : DifferentiableAt 𝕜 h x) (hy : y = h x) :
    deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x) := by
  rw [hy] at hg; exact deriv.scomp x hg hh


/--
theorem `HasDerivAtFilter.comp_hasFDerivAtFilter` / 定理 `HasDerivAtFilter.comp_hasFDerivAtFilter`

English:
theorem HasDerivAtFilter.comp_hasFDerivAtFilter
  statement: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'}
  proof: by
  convert! (hh₂.restrictScalars 𝕜).comp hf hL
  ext x
  simp [mul_comm]

@[deprecated HasDerivAtFilter.comp_hasFDerivAtFilter (since := "2026-02-17")]

中文:
定理 HasDerivAtFilter.comp_hasFDerivAtFilter
  结论: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'}
  证明: by
  convert! (hh₂.restrictScalars 𝕜).comp hf hL
  ext x
  simp [mul_comm]

@[deprecated HasDerivAtFilter.comp_hasFDerivAtFilter (since := "2026-02-17")]

Depends on / 依赖: convert, mul_comm, restrictScalars
-/
theorem HasDerivAtFilter.comp_hasFDerivAtFilter {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'}
    {L'' : Filter (E × E)} (hh₂ : HasDerivAtFilter h₂ h₂' L') (hf : HasFDerivAtFilter f f' L'')
    (hL : Tendsto (Prod.map f f) L'' L') :
    HasFDerivAtFilter (h₂ ∘ f) (h₂' • f') L'' := by
  convert! (hh₂.restrictScalars 𝕜).comp hf hL
  ext x
  simp [mul_comm]

@[deprecated HasDerivAtFilter.comp_hasFDerivAtFilter (since := "2026-02-17")]
/--
theorem `HasDerivAtFilter.comp_hasFDerivAtFilter_of_eq` / 定理 `HasDerivAtFilter.comp_hasFDerivAtFilter_of_eq`

English:
theorem HasDerivAtFilter.comp_hasFDerivAtFilter_of_eq
  proof: hh₂.comp_hasFDerivAtFilter hf hL.prodMap by simp [hy]

中文:
定理 HasDerivAtFilter.comp_hasFDerivAtFilter_of_eq
  证明: hh₂.comp_hasFDerivAtFilter hf hL.prodMap by simp [hy]

Depends on / 依赖: comp_hasFDerivAtFilter, hL.prodMap, prodMap
-/
theorem HasDerivAtFilter.comp_hasFDerivAtFilter_of_eq
    {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) {L' : Filter 𝕜'} {L'' : Filter E}
    (hh₂ : HasDerivAtFilter h₂ h₂' (L' ×ˢ pure y)) (hf : HasFDerivAtFilter f f' (L'' ×ˢ pure x))
    (hL : Tendsto f L'' L') (hy : y = f x) :
    HasFDerivAtFilter (h₂ ∘ f) (h₂' • f') (L'' ×ˢ pure x) :=
hh₂.comp_hasFDerivAtFilter hf hL.prodMap by simp [hy]

/--
theorem `HasStrictDerivAt.comp_hasStrictFDerivAt` / 定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`

English:
theorem HasStrictDerivAt.comp_hasStrictFDerivAt
  statement: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x)
  proof: HasDerivAtFilter.comp_hasFDerivAtFilter hh hf hf.continuousAt.prodMap hf.continuousAt

中文:
定理 HasStrictDerivAt.comp_hasStrictFDerivAt
  结论: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x)
  证明: HasDerivAtFilter.comp_hasFDerivAtFilter hh hf hf.continuousAt.prodMap hf.continuousAt

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.comp_hasFDerivAtFilter, comp_hasFDerivAtFilter, continuousAt, hf.continuousAt, hf.continuousAt.prodMap, prodMap
-/
theorem HasStrictDerivAt.comp_hasStrictFDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x)
    (hh : HasStrictDerivAt h₂ h₂' (f x)) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (h₂ ∘ f) (h₂' • f') x :=
HasDerivAtFilter.comp_hasFDerivAtFilter hh hf hf.continuousAt.prodMap hf.continuousAt

/--
theorem `HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq` / 定理 `HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq`

English:
theorem HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq
  statement: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x)
  proof: by
  rw [hy] at hh; exact hh.comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq
  结论: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x)
  证明: by
  rw [hy] at hh; exact hh.comp_hasStrictFDerivAt x hf

Depends on / 依赖: comp_hasStrictFDerivAt, hh.comp_hasStrictFDerivAt
-/
theorem HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x)
    (hh : HasStrictDerivAt h₂ h₂' y) (hf : HasStrictFDerivAt f f' x) (hy : y = f x) :
    HasStrictFDerivAt (h₂ ∘ f) (h₂' • f') x := by
  rw [hy] at hh; exact hh.comp_hasStrictFDerivAt x hf

/--
theorem `HasDerivAt.comp_hasFDerivAt` / 定理 `HasDerivAt.comp_hasFDerivAt`

English:
theorem HasDerivAt.comp_hasFDerivAt
  statement: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x)
  proof: hh.comp_hasFDerivAtFilter hf hf.continuousAt.tendsto.prodMap tendsto_pure_pure _ _

中文:
定理 HasDerivAt.comp_hasFDerivAt
  结论: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x)
  证明: hh.comp_hasFDerivAtFilter hf hf.continuousAt.tendsto.prodMap tendsto_pure_pure _ _

Depends on / 依赖: comp_hasFDerivAtFilter, continuousAt, hf.continuousAt.tendsto.prodMap, hh.comp_hasFDerivAtFilter, prodMap, tendsto, tendsto_pure_pure
-/
theorem HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x)
    (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (h₂ ∘ f) (h₂' • f') x :=
hh.comp_hasFDerivAtFilter hf hf.continuousAt.tendsto.prodMap tendsto_pure_pure _ _

/--
theorem `HasDerivAt.comp_hasFDerivAt_of_eq` / 定理 `HasDerivAt.comp_hasFDerivAt_of_eq`

English:
theorem HasDerivAt.comp_hasFDerivAt_of_eq
  statement: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x)
  proof: by
  rw [hy] at hh; exact hh.comp_hasFDerivAt x hf

中文:
定理 HasDerivAt.comp_hasFDerivAt_of_eq
  结论: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x)
  证明: by
  rw [hy] at hh; exact hh.comp_hasFDerivAt x hf

Depends on / 依赖: comp_hasFDerivAt, hh.comp_hasFDerivAt
-/
theorem HasDerivAt.comp_hasFDerivAt_of_eq {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x)
    (hh : HasDerivAt h₂ h₂' y) (hf : HasFDerivAt f f' x) (hy : y = f x) :
    HasFDerivAt (h₂ ∘ f) (h₂' • f') x := by
  rw [hy] at hh; exact hh.comp_hasFDerivAt x hf

/--
theorem `HasDerivAt.comp_hasFDerivWithinAt` / 定理 `HasDerivAt.comp_hasFDerivWithinAt`

English:
theorem HasDerivAt.comp_hasFDerivWithinAt
  statement: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x)
  proof: hh.comp_hasFDerivAtFilter hf hf.continuousWithinAt.tendsto.prodMap tendsto_pure_pure _ _

中文:
定理 HasDerivAt.comp_hasFDerivWithinAt
  结论: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x)
  证明: hh.comp_hasFDerivAtFilter hf hf.continuousWithinAt.tendsto.prodMap tendsto_pure_pure _ _

Depends on / 依赖: comp_hasFDerivAtFilter, continuousWithinAt, hf.continuousWithinAt.tendsto.prodMap, hh.comp_hasFDerivAtFilter, prodMap, tendsto, tendsto_pure_pure
-/
theorem HasDerivAt.comp_hasFDerivWithinAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x)
    (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
hh.comp_hasFDerivAtFilter hf hf.continuousWithinAt.tendsto.prodMap tendsto_pure_pure _ _

/--
theorem `HasDerivAt.comp_hasFDerivWithinAt_of_eq` / 定理 `HasDerivAt.comp_hasFDerivWithinAt_of_eq`

English:
theorem HasDerivAt.comp_hasFDerivWithinAt_of_eq
  statement: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x)
  proof: by
  rw [hy] at hh; exact hh.comp_hasFDerivWithinAt x hf

中文:
定理 HasDerivAt.comp_hasFDerivWithinAt_of_eq
  结论: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x)
  证明: by
  rw [hy] at hh; exact hh.comp_hasFDerivWithinAt x hf

Depends on / 依赖: comp_hasFDerivWithinAt, hh.comp_hasFDerivWithinAt
-/
theorem HasDerivAt.comp_hasFDerivWithinAt_of_eq {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x)
    (hh : HasDerivAt h₂ h₂' y) (hf : HasFDerivWithinAt f f' s x) (hy : y = f x) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x := by
  rw [hy] at hh; exact hh.comp_hasFDerivWithinAt x hf

/--
theorem `HasDerivWithinAt.comp_hasFDerivWithinAt` / 定理 `HasDerivWithinAt.comp_hasFDerivWithinAt`

English:
theorem HasDerivWithinAt.comp_hasFDerivWithinAt
  statement: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s t} (x)
  proof: hh.comp_hasFDerivAtFilter hf .prodMap hf.continuousWithinAt.tendsto_nhdsWithin hst
    tendsto_pure_pure _ _

中文:
定理 HasDerivWithinAt.comp_hasFDerivWithinAt
  结论: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s t} (x)
  证明: hh.comp_hasFDerivAtFilter hf .prodMap hf.continuousWithinAt.tendsto_nhdsWithin hst
    tendsto_pure_pure _ _

Depends on / 依赖: comp_hasFDerivAtFilter, continuousWithinAt, hf.continuousWithinAt.tendsto_nhdsWithin, hh.comp_hasFDerivAtFilter, prodMap, tendsto_nhdsWithin, tendsto_pure_pure
-/
theorem HasDerivWithinAt.comp_hasFDerivWithinAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t (f x)) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
hh.comp_hasFDerivAtFilter hf .prodMap hf.continuousWithinAt.tendsto_nhdsWithin hst
    tendsto_pure_pure _ _

/--
theorem `HasDerivWithinAt.comp_hasFDerivWithinAt_of_eq` / 定理 `HasDerivWithinAt.comp_hasFDerivWithinAt_of_eq`

English:
theorem HasDerivWithinAt.comp_hasFDerivWithinAt_of_eq
  statement: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s t} (x)
  proof: by
  rw [hy] at hh; exact hh.comp_hasFDerivWithinAt x hf hst

中文:
定理 HasDerivWithinAt.comp_hasFDerivWithinAt_of_eq
  结论: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s t} (x)
  证明: by
  rw [hy] at hh; exact hh.comp_hasFDerivWithinAt x hf hst

Depends on / 依赖: comp_hasFDerivWithinAt, hh.comp_hasFDerivWithinAt
-/
theorem HasDerivWithinAt.comp_hasFDerivWithinAt_of_eq {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t y) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t)
    (hy : y = f x) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x := by
  rw [hy] at hh; exact hh.comp_hasFDerivWithinAt x hf hst

/--
theorem `HasDerivWithinAt.comp_hasFDerivAt` / 定理 `HasDerivWithinAt.comp_hasFDerivAt`

English:
theorem HasDerivWithinAt.comp_hasFDerivAt
  statement: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {t} (x)
  proof: hh.comp_hasFDerivAtFilter hf .prodMap tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt, ht⟩
    tendsto_pure_pure _ _

中文:
定理 HasDerivWithinAt.comp_hasFDerivAt
  结论: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {t} (x)
  证明: hh.comp_hasFDerivAtFilter hf .prodMap tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt, ht⟩
    tendsto_pure_pure _ _

Depends on / 依赖: comp_hasFDerivAtFilter, continuousAt, hf.continuousAt, hh.comp_hasFDerivAtFilter, prodMap, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mpr, tendsto_pure_pure
-/
theorem HasDerivWithinAt.comp_hasFDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t (f x)) (hf : HasFDerivAt f f' x) (ht : forallᶠ x' in 𝓝 x, f x' in t) :
    HasFDerivAt (h₂ ∘ f) (h₂' • f') x :=
hh.comp_hasFDerivAtFilter hf .prodMap tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt, ht⟩
    tendsto_pure_pure _ _

/--
theorem `HasDerivWithinAt.comp_hasFDerivAt_of_eq` / 定理 `HasDerivWithinAt.comp_hasFDerivAt_of_eq`

English:
theorem HasDerivWithinAt.comp_hasFDerivAt_of_eq
  statement: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {t} (x)
  proof: by
  subst y; exact hh.comp_hasFDerivAt x hf ht

中文:
定理 HasDerivWithinAt.comp_hasFDerivAt_of_eq
  结论: {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {t} (x)
  证明: by
  subst y; exact hh.comp_hasFDerivAt x hf ht

Depends on / 依赖: comp_hasFDerivAt, hh.comp_hasFDerivAt
-/
theorem HasDerivWithinAt.comp_hasFDerivAt_of_eq {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t y) (hf : HasFDerivAt f f' x) (ht : forallᶠ x' in 𝓝 x, f x' in t)
    (hy : y = f x) : HasFDerivAt (h₂ ∘ f) (h₂' • f') x := by
  subst y; exact hh.comp_hasFDerivAt x hf ht


/--
theorem `HasDerivAtFilter.comp` / 定理 `HasDerivAtFilter.comp`

English:
theorem HasDerivAtFilter.comp
  statement: (hh₂ : HasDerivAtFilter h₂ h₂' L')
  proof: by
  rw [mul_comm]
  exact hh₂.scomp hh hL

@[deprecated HasDerivAtFilter.comp (since := "2026-07-17")]

中文:
定理 HasDerivAtFilter.comp
  结论: (hh₂ : HasDerivAtFilter h₂ h₂' L')
  证明: by
  rw [mul_comm]
  exact hh₂.scomp hh hL

@[deprecated HasDerivAtFilter.comp (since := "2026-07-17")]

Depends on / 依赖: mul_comm
-/
theorem HasDerivAtFilter.comp (hh₂ : HasDerivAtFilter h₂ h₂' L')
    (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') :
    HasDerivAtFilter (h₂ ∘ h) (h₂' * h') L := by
  rw [mul_comm]
  exact hh₂.scomp hh hL

@[deprecated HasDerivAtFilter.comp (since := "2026-07-17")]
/--
theorem `HasDerivAtFilter.comp_of_eq` / 定理 `HasDerivAtFilter.comp_of_eq`

English:
theorem HasDerivAtFilter.comp_of_eq
  statement: {L : Filter 𝕜} {L' : Filter 𝕜'}
  proof: hh₂.comp hh hL.prodMap by simp [hy]

中文:
定理 HasDerivAtFilter.comp_of_eq
  结论: {L : Filter 𝕜} {L' : Filter 𝕜'}
  证明: hh₂.comp hh hL.prodMap by simp [hy]

Depends on / 依赖: hL.prodMap, prodMap
-/
theorem HasDerivAtFilter.comp_of_eq {L : Filter 𝕜} {L' : Filter 𝕜'}
    (hh₂ : HasDerivAtFilter h₂ h₂' (L' ×ˢ pure y))
    (hh : HasDerivAtFilter h h' (L ×ˢ pure x)) (hL : Tendsto h L L') (hy : y = h x) :
    HasDerivAtFilter (h₂ ∘ h) (h₂' * h') (L ×ˢ pure x) :=
hh₂.comp hh hL.prodMap by simp [hy]

/--
theorem `HasDerivWithinAt.comp` / 定理 `HasDerivWithinAt.comp`

English:
theorem HasDerivWithinAt.comp
  statement: (hh₂ : HasDerivWithinAt h₂ h₂' s' (h x))
  proof: by
  rw [mul_comm]
  exact hh₂.scomp x hh hst

中文:
定理 HasDerivWithinAt.comp
  结论: (hh₂ : HasDerivWithinAt h₂ h₂' s' (h x))
  证明: by
  rw [mul_comm]
  exact hh₂.scomp x hh hst

Depends on / 依赖: mul_comm
-/
theorem HasDerivWithinAt.comp (hh₂ : HasDerivWithinAt h₂ h₂' s' (h x))
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [mul_comm]
  exact hh₂.scomp x hh hst

/--
theorem `HasDerivWithinAt.comp_of_eq` / 定理 `HasDerivWithinAt.comp_of_eq`

English:
theorem HasDerivWithinAt.comp_of_eq
  statement: (hh₂ : HasDerivWithinAt h₂ h₂' s' y)
  proof: by
  rw [hy] at hh₂; exact hh₂.comp x hh hst

中文:
定理 HasDerivWithinAt.comp_of_eq
  结论: (hh₂ : HasDerivWithinAt h₂ h₂' s' y)
  证明: by
  rw [hy] at hh₂; exact hh₂.comp x hh hst
-/
theorem HasDerivWithinAt.comp_of_eq (hh₂ : HasDerivWithinAt h₂ h₂' s' y)
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') (hy : y = h x) :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [hy] at hh₂; exact hh₂.comp x hh hst

/--
theorem `HasDerivAt.comp` / 定理 `HasDerivAt.comp`

English:
theorem HasDerivAt.comp
  given: (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x)
  proof: HasDerivAtFilter.comp hh₂ hh hh.continuousAt.tendsto.prodMap tendsto_pure_pure _ _

中文:
定理 HasDerivAt.comp
  条件: (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x)
  证明: HasDerivAtFilter.comp hh₂ hh hh.continuousAt.tendsto.prodMap tendsto_pure_pure _ _

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.comp, continuousAt, hh.continuousAt.tendsto.prodMap, prodMap, tendsto, tendsto_pure_pure
-/
theorem HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (h₂ ∘ h) (h₂' * h') x :=
HasDerivAtFilter.comp hh₂ hh hh.continuousAt.tendsto.prodMap tendsto_pure_pure _ _

/--
theorem `HasDerivAt.comp_of_eq` / 定理 `HasDerivAt.comp_of_eq`

English:
theorem HasDerivAt.comp_of_eq
  proof: by
  rw [hy] at hh₂; exact hh₂.comp x hh

中文:
定理 HasDerivAt.comp_of_eq
  证明: by
  rw [hy] at hh₂; exact hh₂.comp x hh
-/
theorem HasDerivAt.comp_of_eq
    (hh₂ : HasDerivAt h₂ h₂' y) (hh : HasDerivAt h h' x) (hy : y = h x) :
    HasDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [hy] at hh₂; exact hh₂.comp x hh

/--
theorem `HasStrictDerivAt.comp` / 定理 `HasStrictDerivAt.comp`

English:
theorem HasStrictDerivAt.comp
  given: (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x)
  proof: by
  rw [mul_comm]
  exact hh₂.scomp x hh

中文:
定理 HasStrictDerivAt.comp
  条件: (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x)
  证明: by
  rw [mul_comm]
  exact hh₂.scomp x hh

Depends on / 依赖: mul_comm
-/
theorem HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [mul_comm]
  exact hh₂.scomp x hh

/--
theorem `HasStrictDerivAt.comp_of_eq` / 定理 `HasStrictDerivAt.comp_of_eq`

English:
theorem HasStrictDerivAt.comp_of_eq
  proof: by
  rw [hy] at hh₂; exact hh₂.comp x hh

中文:
定理 HasStrictDerivAt.comp_of_eq
  证明: by
  rw [hy] at hh₂; exact hh₂.comp x hh
-/
theorem HasStrictDerivAt.comp_of_eq
    (hh₂ : HasStrictDerivAt h₂ h₂' y) (hh : HasStrictDerivAt h h' x) (hy : y = h x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [hy] at hh₂; exact hh₂.comp x hh

/--
theorem `HasDerivAt.comp_hasDerivWithinAt` / 定理 `HasDerivAt.comp_hasDerivWithinAt`

English:
theorem HasDerivAt.comp_hasDerivWithinAt
  statement: (hh₂ : HasDerivAt h₂ h₂' (h x))
  proof: hh₂.hasDerivWithinAt.comp x hh (mapsTo_univ _ _)

中文:
定理 HasDerivAt.comp_hasDerivWithinAt
  结论: (hh₂ : HasDerivAt h₂ h₂' (h x))
  证明: hh₂.hasDerivWithinAt.comp x hh (mapsTo_univ _ _)

Depends on / 依赖: hasDerivWithinAt, hasDerivWithinAt.comp, mapsTo_univ
-/
theorem HasDerivAt.comp_hasDerivWithinAt (hh₂ : HasDerivAt h₂ h₂' (h x))
    (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x :=
  hh₂.hasDerivWithinAt.comp x hh (mapsTo_univ _ _)

/--
theorem `HasDerivAt.comp_hasDerivWithinAt_of_eq` / 定理 `HasDerivAt.comp_hasDerivWithinAt_of_eq`

English:
theorem HasDerivAt.comp_hasDerivWithinAt_of_eq
  statement: (hh₂ : HasDerivAt h₂ h₂' y)
  proof: by
  rw [hy] at hh₂; exact hh₂.comp_hasDerivWithinAt x hh

中文:
定理 HasDerivAt.comp_hasDerivWithinAt_of_eq
  结论: (hh₂ : HasDerivAt h₂ h₂' y)
  证明: by
  rw [hy] at hh₂; exact hh₂.comp_hasDerivWithinAt x hh

Depends on / 依赖: comp_hasDerivWithinAt
-/
theorem HasDerivAt.comp_hasDerivWithinAt_of_eq (hh₂ : HasDerivAt h₂ h₂' y)
    (hh : HasDerivWithinAt h h' s x) (hy : y = h x) :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [hy] at hh₂; exact hh₂.comp_hasDerivWithinAt x hh

/--
theorem `HasDerivWithinAt.comp_hasDerivAt` / 定理 `HasDerivWithinAt.comp_hasDerivAt`

English:
theorem HasDerivWithinAt.comp_hasDerivAt
  statement: {t} (hh₂ : HasDerivWithinAt h₂ h₂' t (h x))
  proof: HasDerivAtFilter.comp hh₂ hh .prodMap tendsto_nhdsWithin_iff.mpr ⟨hh.continuousAt, ht⟩
    tendsto_pure_pure _ _

中文:
定理 HasDerivWithinAt.comp_hasDerivAt
  结论: {t} (hh₂ : HasDerivWithinAt h₂ h₂' t (h x))
  证明: HasDerivAtFilter.comp hh₂ hh .prodMap tendsto_nhdsWithin_iff.mpr ⟨hh.continuousAt, ht⟩
    tendsto_pure_pure _ _

Depends on / 依赖: HasDerivAtFilter, HasDerivAtFilter.comp, continuousAt, hh.continuousAt, prodMap, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mpr, tendsto_pure_pure
-/
theorem HasDerivWithinAt.comp_hasDerivAt {t} (hh₂ : HasDerivWithinAt h₂ h₂' t (h x))
    (hh : HasDerivAt h h' x) (ht : forallᶠ x' in 𝓝 x, h x' in t) : HasDerivAt (h₂ ∘ h) (h₂' * h') x :=
HasDerivAtFilter.comp hh₂ hh .prodMap tendsto_nhdsWithin_iff.mpr ⟨hh.continuousAt, ht⟩
    tendsto_pure_pure _ _

/--
theorem `HasDerivWithinAt.comp_hasDerivAt_of_eq` / 定理 `HasDerivWithinAt.comp_hasDerivAt_of_eq`

English:
theorem HasDerivWithinAt.comp_hasDerivAt_of_eq
  statement: {t} (hh₂ : HasDerivWithinAt h₂ h₂' t y)
  proof: by
  subst y; exact hh₂.comp_hasDerivAt x hh ht

中文:
定理 HasDerivWithinAt.comp_hasDerivAt_of_eq
  结论: {t} (hh₂ : HasDerivWithinAt h₂ h₂' t y)
  证明: by
  subst y; exact hh₂.comp_hasDerivAt x hh ht

Depends on / 依赖: comp_hasDerivAt
-/
theorem HasDerivWithinAt.comp_hasDerivAt_of_eq {t} (hh₂ : HasDerivWithinAt h₂ h₂' t y)
    (hh : HasDerivAt h h' x) (ht : forallᶠ x' in 𝓝 x, h x' in t) (hy : y = h x) :
    HasDerivAt (h₂ ∘ h) (h₂' * h') x := by
  subst y; exact hh₂.comp_hasDerivAt x hh ht

/--
theorem `derivWithin_comp` / 定理 `derivWithin_comp`

English:
theorem derivWithin_comp
  statement: (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' (h x))
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hh₂.hasDerivWithinAt.comp x hh.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 derivWithin_comp
  结论: (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' (h x))
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hh₂.hasDerivWithinAt.comp x hh.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: UniqueDiffWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hasDerivWithinAt.comp, hh.hasDerivWithinAt
-/
theorem derivWithin_comp (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' (h x))
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s s') :
    derivWithin (h₂ ∘ h) s x = derivWithin h₂ s' (h x) * derivWithin h s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hh₂.hasDerivWithinAt.comp x hh.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `derivWithin_comp_of_eq` / 定理 `derivWithin_comp_of_eq`

English:
theorem derivWithin_comp_of_eq
  statement: (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' y)
  proof: by
  subst hy; exact derivWithin_comp x hh₂ hh hs

中文:
定理 derivWithin_comp_of_eq
  结论: (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' y)
  证明: by
  subst hy; exact derivWithin_comp x hh₂ hh hs

Depends on / 依赖: derivWithin_comp
-/
theorem derivWithin_comp_of_eq (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' y)
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s s')
    (hy : h x = y) :
    derivWithin (h₂ ∘ h) s x = derivWithin h₂ s' (h x) * derivWithin h s x := by
  subst hy; exact derivWithin_comp x hh₂ hh hs

/--
theorem `deriv_comp` / 定理 `deriv_comp`

English:
theorem deriv_comp
  given: (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : DifferentiableAt 𝕜 h x)
  proof: (hh₂.hasDerivAt.comp x hh.hasDerivAt).deriv

中文:
定理 deriv_comp
  条件: (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : DifferentiableAt 𝕜 h x)
  证明: (hh₂.hasDerivAt.comp x hh.hasDerivAt).deriv

Depends on / 依赖: hasDerivAt, hasDerivAt.comp, hh.hasDerivAt
-/
theorem deriv_comp (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x :=
  (hh₂.hasDerivAt.comp x hh.hasDerivAt).deriv

/--
theorem `deriv_comp_of_eq` / 定理 `deriv_comp_of_eq`

English:
theorem deriv_comp_of_eq
  statement: (hh₂ : DifferentiableAt 𝕜' h₂ y) (hh : DifferentiableAt 𝕜 h x)
  proof: by
  subst hy; exact deriv_comp x hh₂ hh

protected nonrec theorem HasDerivAtFilter.iterate {f : 𝕜 -> 𝕜} {f' : 𝕜}
    (hf : HasDerivAtFilter f f' L) (hL : Tendsto (Prod.map f f) L L) (n : Nat) :
    HasDerivAtFilter f^[n] (f' ^ n) L := by
  have := hf.hasFDerivAtFilter.iterate hL n
  rwa [Continuous

中文:
定理 deriv_comp_of_eq
  结论: (hh₂ : DifferentiableAt 𝕜' h₂ y) (hh : DifferentiableAt 𝕜 h x)
  证明: by
  subst hy; exact deriv_comp x hh₂ hh

protected nonrec theorem HasDerivAtFilter.iterate {f : 𝕜 -> 𝕜} {f' : 𝕜}
    (hf : HasDerivAtFilter f f' L) (hL : Tendsto (Prod.map f f) L L) (n : Nat) :
    HasDerivAtFilter f^[n] (f' ^ n) L := by
  have := hf.hasFDerivAtFilter.iterate hL n
  rwa [Continuous

Depends on / 依赖: deriv_comp
-/
theorem deriv_comp_of_eq (hh₂ : DifferentiableAt 𝕜' h₂ y) (hh : DifferentiableAt 𝕜 h x)
    (hy : h x = y) :
    deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x := by
  subst hy; exact deriv_comp x hh₂ hh

protected nonrec theorem HasDerivAtFilter.iterate {f : 𝕜 -> 𝕜} {f' : 𝕜}
    (hf : HasDerivAtFilter f f' L) (hL : Tendsto (Prod.map f f) L L) (n : Nat) :
    HasDerivAtFilter f^[n] (f' ^ n) L := by
  have := hf.hasFDerivAtFilter.iterate hL n
  rwa [ContinuousLinearMap.toSpanSingleton_pow] at this

protected nonrec theorem HasDerivAt.iterate {f : 𝕜 -> 𝕜} {f' : 𝕜} (hf : HasDerivAt f f' x)
    (hx : f x = x) (n : Nat) : HasDerivAt f^[n] (f' ^ n) x :=
  hf.iterate (by simpa [hx] using hf.continuousAt.tendsto.prodMap <| tendsto_pure_pure f x) _

/--
theorem `HasDerivWithinAt.iterate` / 定理 `HasDerivWithinAt.iterate`

English:
theorem HasDerivWithinAt.iterate
  statement: {f : 𝕜 -> 𝕜} {f' : 𝕜} (hf : HasDerivWithinAt f f' s x)
  proof: by
  have := HasFDerivWithinAt.iterate hf hx hs n
  rwa [ContinuousLinearMap.toSpanSingleton_pow] at this

中文:
定理 HasDerivWithinAt.iterate
  结论: {f : 𝕜 -> 𝕜} {f' : 𝕜} (hf : HasDerivWithinAt f f' s x)
  证明: by
  have := HasFDerivWithinAt.iterate hf hx hs n
  rwa [ContinuousLinearMap.toSpanSingleton_pow] at this
-/
protected theorem HasDerivWithinAt.iterate {f : 𝕜 -> 𝕜} {f' : 𝕜} (hf : HasDerivWithinAt f f' s x)
    (hx : f x = x) (hs : MapsTo f s s) (n : Nat) : HasDerivWithinAt f^[n] (f' ^ n) s x := by
  have := HasFDerivWithinAt.iterate hf hx hs n
  rwa [ContinuousLinearMap.toSpanSingleton_pow] at this

/--
theorem `HasStrictDerivAt.iterate` / 定理 `HasStrictDerivAt.iterate`

English:
theorem HasStrictDerivAt.iterate
  statement: {f : 𝕜 -> 𝕜} {f' : 𝕜}
  proof: by
  have := hf.hasStrictFDerivAt.iterate hx n
  rwa [ContinuousLinearMap.toSpanSingleton_pow] at this

中文:
定理 HasStrictDerivAt.iterate
  结论: {f : 𝕜 -> 𝕜} {f' : 𝕜}
  证明: by
  have := hf.hasStrictFDerivAt.iterate hx n
  rwa [ContinuousLinearMap.toSpanSingleton_pow] at this
-/
protected theorem HasStrictDerivAt.iterate {f : 𝕜 -> 𝕜} {f' : 𝕜}
    (hf : HasStrictDerivAt f f' x) (hx : f x = x) (n : Nat) :
    HasStrictDerivAt f^[n] (f' ^ n) x := by
  have := hf.hasStrictFDerivAt.iterate hx n
  rwa [ContinuousLinearMap.toSpanSingleton_pow] at this

end Composition

section CompositionVector

/-! ### Derivative of the composition of a function between vector spaces and a function on `𝕜` -/

open ContinuousLinearMap

variable {l : F -> E} {l' : F ->L[𝕜] E} {y : F}
variable (x)

/--
theorem `HasFDerivWithinAt.comp_hasDerivWithinAt` / 定理 `HasFDerivWithinAt.comp_hasDerivWithinAt`

English:
theorem HasFDerivWithinAt.comp_hasDerivWithinAt
  statement: {t : Set F} (hl : HasFDerivWithinAt l l' t (f x))
  proof: by
  simpa using (hl.comp x hf.hasFDerivWithinAt hst).hasDerivWithinAt

中文:
定理 HasFDerivWithinAt.comp_hasDerivWithinAt
  结论: {t : Set F} (hl : HasFDerivWithinAt l l' t (f x))
  证明: by
  simpa using (hl.comp x hf.hasFDerivWithinAt hst).hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt, hl.comp
-/
theorem HasFDerivWithinAt.comp_hasDerivWithinAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x))
    (hf : HasDerivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasDerivWithinAt (l ∘ f) (l' f') s x := by
  simpa using (hl.comp x hf.hasFDerivWithinAt hst).hasDerivWithinAt

/--
theorem `HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq` / 定理 `HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq`

English:
theorem HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq
  statement: {t : Set F}
  proof: by
  rw [hy] at hl; exact hl.comp_hasDerivWithinAt x hf hst

中文:
定理 HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq
  结论: {t : Set F}
  证明: by
  rw [hy] at hl; exact hl.comp_hasDerivWithinAt x hf hst

Depends on / 依赖: comp_hasDerivWithinAt, hl.comp_hasDerivWithinAt
-/
theorem HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq {t : Set F}
    (hl : HasFDerivWithinAt l l' t y)
    (hf : HasDerivWithinAt f f' s x) (hst : MapsTo f s t) (hy : y = f x) :
    HasDerivWithinAt (l ∘ f) (l' f') s x := by
  rw [hy] at hl; exact hl.comp_hasDerivWithinAt x hf hst

/--
theorem `HasFDerivWithinAt.comp_hasDerivAt` / 定理 `HasFDerivWithinAt.comp_hasDerivAt`

English:
theorem HasFDerivWithinAt.comp_hasDerivAt
  statement: {t : Set F} (hl : HasFDerivWithinAt l l' t (f x))
  proof: by
  simpa using (hl.comp_hasFDerivAt x hf.hasFDerivAt ht).hasDerivAt

中文:
定理 HasFDerivWithinAt.comp_hasDerivAt
  结论: {t : Set F} (hl : HasFDerivWithinAt l l' t (f x))
  证明: by
  simpa using (hl.comp_hasFDerivAt x hf.hasFDerivAt ht).hasDerivAt

Depends on / 依赖: comp_hasFDerivAt, hasDerivAt, hasFDerivAt, hf.hasFDerivAt, hl.comp_hasFDerivAt
-/
theorem HasFDerivWithinAt.comp_hasDerivAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x))
    (hf : HasDerivAt f f' x) (ht : forallᶠ x' in 𝓝 x, f x' in t) : HasDerivAt (l ∘ f) (l' f') x := by
  simpa using (hl.comp_hasFDerivAt x hf.hasFDerivAt ht).hasDerivAt

/--
theorem `HasFDerivWithinAt.comp_hasDerivAt_of_eq` / 定理 `HasFDerivWithinAt.comp_hasDerivAt_of_eq`

English:
theorem HasFDerivWithinAt.comp_hasDerivAt_of_eq
  statement: {t : Set F} (hl : HasFDerivWithinAt l l' t y)
  proof: by
  subst y; exact hl.comp_hasDerivAt x hf ht

中文:
定理 HasFDerivWithinAt.comp_hasDerivAt_of_eq
  结论: {t : Set F} (hl : HasFDerivWithinAt l l' t y)
  证明: by
  subst y; exact hl.comp_hasDerivAt x hf ht

Depends on / 依赖: comp_hasDerivAt, hl.comp_hasDerivAt
-/
theorem HasFDerivWithinAt.comp_hasDerivAt_of_eq {t : Set F} (hl : HasFDerivWithinAt l l' t y)
    (hf : HasDerivAt f f' x) (ht : forallᶠ x' in 𝓝 x, f x' in t) (hy : y = f x) :
    HasDerivAt (l ∘ f) (l' f') x := by
  subst y; exact hl.comp_hasDerivAt x hf ht

/--
theorem `HasFDerivAt.comp_hasDerivWithinAt` / 定理 `HasFDerivAt.comp_hasDerivWithinAt`

English:
theorem HasFDerivAt.comp_hasDerivWithinAt
  statement: (hl : HasFDerivAt l l' (f x))
  proof: hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf (mapsTo_univ _ _)

中文:
定理 HasFDerivAt.comp_hasDerivWithinAt
  结论: (hl : HasFDerivAt l l' (f x))
  证明: hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf (mapsTo_univ _ _)

Depends on / 依赖: comp_hasDerivWithinAt, hasFDerivWithinAt, hl.hasFDerivWithinAt.comp_hasDerivWithinAt, mapsTo_univ
-/
theorem HasFDerivAt.comp_hasDerivWithinAt (hl : HasFDerivAt l l' (f x))
    (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (l ∘ f) (l' f') s x :=
  hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf (mapsTo_univ _ _)

/--
theorem `HasFDerivAt.comp_hasDerivWithinAt_of_eq` / 定理 `HasFDerivAt.comp_hasDerivWithinAt_of_eq`

English:
theorem HasFDerivAt.comp_hasDerivWithinAt_of_eq
  statement: (hl : HasFDerivAt l l' y)
  proof: by
  rw [hy] at hl; exact hl.comp_hasDerivWithinAt x hf

中文:
定理 HasFDerivAt.comp_hasDerivWithinAt_of_eq
  结论: (hl : HasFDerivAt l l' y)
  证明: by
  rw [hy] at hl; exact hl.comp_hasDerivWithinAt x hf

Depends on / 依赖: comp_hasDerivWithinAt, hl.comp_hasDerivWithinAt
-/
theorem HasFDerivAt.comp_hasDerivWithinAt_of_eq (hl : HasFDerivAt l l' y)
    (hf : HasDerivWithinAt f f' s x) (hy : y = f x) :
    HasDerivWithinAt (l ∘ f) (l' f') s x := by
  rw [hy] at hl; exact hl.comp_hasDerivWithinAt x hf

/--
theorem `HasFDerivAt.comp_hasDerivAt` / 定理 `HasFDerivAt.comp_hasDerivAt`

English:
theorem HasFDerivAt.comp_hasDerivAt
  given: (hl : HasFDerivAt l l' (f x)) (hf : HasDerivAt f f' x)
  proof: hasDerivWithinAt_univ.mp hl.comp_hasDerivWithinAt x hf.hasDerivWithinAt

中文:
定理 HasFDerivAt.comp_hasDerivAt
  条件: (hl : HasFDerivAt l l' (f x)) (hf : HasDerivAt f f' x)
  证明: hasDerivWithinAt_univ.mp hl.comp_hasDerivWithinAt x hf.hasDerivWithinAt

Depends on / 依赖: comp_hasDerivWithinAt, hasDerivWithinAt, hasDerivWithinAt_univ, hasDerivWithinAt_univ.mp, hf.hasDerivWithinAt, hl.comp_hasDerivWithinAt
-/
theorem HasFDerivAt.comp_hasDerivAt (hl : HasFDerivAt l l' (f x)) (hf : HasDerivAt f f' x) :
    HasDerivAt (l ∘ f) (l' f') x :=
hasDerivWithinAt_univ.mp hl.comp_hasDerivWithinAt x hf.hasDerivWithinAt

/--
theorem `HasFDerivAt.comp_hasDerivAt_of_eq` / 定理 `HasFDerivAt.comp_hasDerivAt_of_eq`

English:
theorem HasFDerivAt.comp_hasDerivAt_of_eq
  proof: by
  rw [hy] at hl; exact hl.comp_hasDerivAt x hf

中文:
定理 HasFDerivAt.comp_hasDerivAt_of_eq
  证明: by
  rw [hy] at hl; exact hl.comp_hasDerivAt x hf

Depends on / 依赖: comp_hasDerivAt, hl.comp_hasDerivAt
-/
theorem HasFDerivAt.comp_hasDerivAt_of_eq
    (hl : HasFDerivAt l l' y) (hf : HasDerivAt f f' x) (hy : y = f x) :
    HasDerivAt (l ∘ f) (l' f') x := by
  rw [hy] at hl; exact hl.comp_hasDerivAt x hf

/--
theorem `HasStrictFDerivAt.comp_hasStrictDerivAt` / 定理 `HasStrictFDerivAt.comp_hasStrictDerivAt`

English:
theorem HasStrictFDerivAt.comp_hasStrictDerivAt
  statement: (hl : HasStrictFDerivAt l l' (f x))
  proof: by
  simpa using! (hl.comp x hf.hasStrictFDerivAt).hasStrictDerivAt

中文:
定理 HasStrictFDerivAt.comp_hasStrictDerivAt
  结论: (hl : HasStrictFDerivAt l l' (f x))
  证明: by
  simpa using! (hl.comp x hf.hasStrictFDerivAt).hasStrictDerivAt

Depends on / 依赖: hasStrictDerivAt, hasStrictFDerivAt, hf.hasStrictFDerivAt, hl.comp
-/
theorem HasStrictFDerivAt.comp_hasStrictDerivAt (hl : HasStrictFDerivAt l l' (f x))
    (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (l ∘ f) (l' f') x := by
  simpa using! (hl.comp x hf.hasStrictFDerivAt).hasStrictDerivAt

/--
theorem `HasStrictFDerivAt.comp_hasStrictDerivAt_of_eq` / 定理 `HasStrictFDerivAt.comp_hasStrictDerivAt_of_eq`

English:
theorem HasStrictFDerivAt.comp_hasStrictDerivAt_of_eq
  statement: (hl : HasStrictFDerivAt l l' y)
  proof: by
  rw [hy] at hl; exact hl.comp_hasStrictDerivAt x hf

中文:
定理 HasStrictFDerivAt.comp_hasStrictDerivAt_of_eq
  结论: (hl : HasStrictFDerivAt l l' y)
  证明: by
  rw [hy] at hl; exact hl.comp_hasStrictDerivAt x hf

Depends on / 依赖: comp_hasStrictDerivAt, hl.comp_hasStrictDerivAt
-/
theorem HasStrictFDerivAt.comp_hasStrictDerivAt_of_eq (hl : HasStrictFDerivAt l l' y)
    (hf : HasStrictDerivAt f f' x) (hy : y = f x) :
    HasStrictDerivAt (l ∘ f) (l' f') x := by
  rw [hy] at hl; exact hl.comp_hasStrictDerivAt x hf

/--
theorem `fderivWithin_comp_derivWithin` / 定理 `fderivWithin_comp_derivWithin`

English:
theorem fderivWithin_comp_derivWithin
  statement: {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t (f x))
  proof: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

中文:
定理 fderivWithin_comp_derivWithin
  结论: {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t (f x))
  证明: by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

Depends on / 依赖: UniqueDiffWithinAt, comp_hasDerivWithinAt, derivWithin, derivWithin_zero_of_not_uniqueDiffWithinAt, hasDerivWithinAt, hasFDerivWithinAt, hf.hasDerivWithinAt, hl.hasFDerivWithinAt.comp_hasDerivWithinAt
-/
theorem fderivWithin_comp_derivWithin {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (hs : MapsTo f s t) :
    derivWithin (l ∘ f) s x = (fderivWithin 𝕜 l t (f x) : F -> E) (derivWithin f s x) := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/--
theorem `fderivWithin_comp_derivWithin_of_eq` / 定理 `fderivWithin_comp_derivWithin_of_eq`

English:
theorem fderivWithin_comp_derivWithin_of_eq
  statement: {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t y)
  proof: by
  rw [hy] at hl; exact fderivWithin_comp_derivWithin x hl hf hs

中文:
定理 fderivWithin_comp_derivWithin_of_eq
  结论: {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t y)
  证明: by
  rw [hy] at hl; exact fderivWithin_comp_derivWithin x hl hf hs

Depends on / 依赖: fderivWithin_comp_derivWithin
-/
theorem fderivWithin_comp_derivWithin_of_eq {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t y)
    (hf : DifferentiableWithinAt 𝕜 f s x) (hs : MapsTo f s t) (hy : y = f x) :
    derivWithin (l ∘ f) s x = (fderivWithin 𝕜 l t (f x) : F -> E) (derivWithin f s x) := by
  rw [hy] at hl; exact fderivWithin_comp_derivWithin x hl hf hs

/--
theorem `fderiv_comp_deriv` / 定理 `fderiv_comp_deriv`

English:
theorem fderiv_comp_deriv
  given: (hl : DifferentiableAt 𝕜 l (f x)) (hf : DifferentiableAt 𝕜 f x)
  proof: (hl.hasFDerivAt.comp_hasDerivAt x hf.hasDerivAt).deriv

中文:
定理 fderiv_comp_deriv
  条件: (hl : DifferentiableAt 𝕜 l (f x)) (hf : DifferentiableAt 𝕜 f x)
  证明: (hl.hasFDerivAt.comp_hasDerivAt x hf.hasDerivAt).deriv

Depends on / 依赖: comp_hasDerivAt, hasDerivAt, hasFDerivAt, hf.hasDerivAt, hl.hasFDerivAt.comp_hasDerivAt
-/
theorem fderiv_comp_deriv (hl : DifferentiableAt 𝕜 l (f x)) (hf : DifferentiableAt 𝕜 f x) :
    deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F -> E) (deriv f x) :=
  (hl.hasFDerivAt.comp_hasDerivAt x hf.hasDerivAt).deriv

/--
theorem `fderiv_comp_deriv_of_eq` / 定理 `fderiv_comp_deriv_of_eq`

English:
theorem fderiv_comp_deriv_of_eq
  statement: (hl : DifferentiableAt 𝕜 l y) (hf : DifferentiableAt 𝕜 f x)
  proof: by
  rw [hy] at hl; exact fderiv_comp_deriv x hl hf

中文:
定理 fderiv_comp_deriv_of_eq
  结论: (hl : DifferentiableAt 𝕜 l y) (hf : DifferentiableAt 𝕜 f x)
  证明: by
  rw [hy] at hl; exact fderiv_comp_deriv x hl hf

Depends on / 依赖: fderiv_comp_deriv
-/
theorem fderiv_comp_deriv_of_eq (hl : DifferentiableAt 𝕜 l y) (hf : DifferentiableAt 𝕜 f x)
    (hy : y = f x) :
    deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F -> E) (deriv f x) := by
  rw [hy] at hl; exact fderiv_comp_deriv x hl hf

end CompositionVector
