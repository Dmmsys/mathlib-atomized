/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.PolarCoord
public import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Fundamental Cone: set of elements of norm ≤ 1

In this file, we study the subset `NormLeOne` of the `fundamentalCone` of elements `x` with
`mixedEmbedding.norm x ≤ 1`.

Mainly, we prove that it is bounded, its frontier has volume zero and compute its volume.

## Strategy of proof

The proof is loosely based on the strategy given in [D. Marcus, *Number Fields*][marcus1977number].

1. since `NormLeOne K` is norm-stable, in the sense that
  `normLeOne K = normAtAllPlaces⁻¹' (normAtAllPlaces '' (normLeOne K))`,
  see `normLeOne_eq_preimage_image`, it's enough to study the subset
  `normAtAllPlaces '' (normLeOne K)` of `realSpace K`.

2. A description of `normAtAllPlaces '' (normLeOne K)` is given by `normAtAllPlaces_normLeOne`, it
  is the set of `x : realSpace K`, nonnegative at all places, whose norm is nonzero and `≤ 1` and
  such that `logMap x` is in the `fundamentalDomain` of `basisUnitLattice K`.
  Note that, here and elsewhere, we identify `x` with its image in `mixedSpace K` given
  by `mixedSpaceOfRealSpace x`.

3. In order to describe the inverse image in `realSpace K` of the `fundamentalDomain` of
  `basisUnitLattice K`, we define the map `expMap : realSpace K → realSpace K` that is, in
  some way, the right inverse of `logMap`, see `logMap_expMap`.

4. Denote by `ηᵢ` (with `i ≠ w₀` where `w₀` is the distinguished infinite place,
  see the description of `logSpace` below) the fundamental system of units given by
  `fundSystem` and let `|ηᵢ|` denote `normAtAllPlaces (mixedEmbedding ηᵢ)`, that is the vector
  `(w (ηᵢ))_w` in `realSpace K`. Then, the image of `|ηᵢ|` by `expMap.symm` form a basis of the
  subspace `{x : realSpace K | ∑ w, x w = 0}`. We complete by adding the vector `(mult w)_w` to
  get a basis, called `completeBasis`, of `realSpace K`. The basis `completeBasis K` has
  the property that, for `i ≠ w₀`, the image of `completeBasis K i` by the
  natural restriction map `realSpace K → logSpace K` is `basisUnitLattice K`.

5. At this point, we can construct the map `expMapBasis` that plays a crucial part in the proof.
  It is the map that sends `x : realSpace K` to `Real.exp (x w₀) * ∏_{i ≠ w₀} |ηᵢ| ^ x i`, see
  `expMapBasis_apply'`. Then, we prove a change of variable formula for `expMapBasis`, see
  `setLIntegral_expMapBasis_image`.

6. We define a set `paramSet` in `realSpace K` and prove that
  `normAtAllPlaces '' (normLeOne K) = expMapBasis (paramSet K)`, see
  `normAtAllPlaces_normLeOne_eq_image`. Using this, `setLIntegral_expMapBasis_image` and the results
  from `mixedEmbedding.polarCoord`, we can then compute the volume of `normLeOne K`, see
  `volume_normLeOne`.

7. Finally, we need to prove that the frontier of `normLeOne K` has zero-volume (we will prove
  in passing that `normLeOne K` is bounded.) For that we prove that
  `volume (interior (normLeOne K)) = volume (closure (normLeOne K))`, see
  `volume_interior_eq_volume_closure`. Since we know that the volume of `interior (normLeOne K)` is
  finite since it is bounded by the volume of `normLeOne K`, the result follows, see
  `volume_frontier_normLeOne`. We proceed in several steps.

  7.1. We prove first that
    `normAtAllPlaces⁻¹' (expMapBasis '' interior (paramSet K)) ⊆ interior (normLeOne K)`, see
    `subset_interior_normLeOne` (Note that here again we identify `realSpace K` with its image
    in `mixedSpace K`). The main argument is that `expMapBasis` is an open partial homeomorphism
    and that `interior (paramSet K)` is a subset of its source, so its image by `expMapBasis`
    is still open.

  7.2. The same kind of argument does not work with `closure (paramSet)` since it is not contained
    in the source of `expMapBasis`. So we define a compact set, called `compactSet K`, such that
    `closure (normLeOne K) ⊆ normAtAllPlaces⁻¹' (compactSet K)`, see `closure_normLeOne_subset`,
    and it is almost equal to `expMapBasis '' closure (paramSet K)`, see `compactSet_ae`.

  7.3. We get from the above that `normLeOne K ⊆ normAtAllPlaces⁻¹' (compactSet K)`, from which
    it follows easily that `normLeOne K` is bounded, see `isBounded_normLeOne`.

  7.4. Finally, we prove that `volume (normAtAllPlaces ⁻¹' compactSet K) =
    volume (normAtAllPlaces ⁻¹' (expMapBasis '' interior (paramSet K)))`, which implies that
    `volume (interior (normLeOne K)) = volume (closure (normLeOne K))` by the above and the fact
    that `volume (interior (normLeOne K)) ≤ volume (closure (normLeOne K))`, which boils down to
    the fact that the interior and closure of `paramSet K` are almost equal, see
    `closure_paramSet_ae_interior`.

## Spaces and maps

To help understand the proof, we make a list of (almost) all the spaces and maps used and
their connections (as hinted above, we do not mention the map `mixedSpaceOfRealSpace` since we
identify `realSpace K` with its image in `mixedSpace K`).

* `mixedSpace`: the set `({w // IsReal w} → ℝ) × (w // IsComplex w → ℂ)` where `w` denote the
  infinite places of `K`.

* `realSpace`: the set `w → ℝ` where `w` denote the infinite places of `K`

* `logSpace`: the set `{w // w ≠ w₀} → ℝ` where `w₀` is a distinguished place of `K`. It is the set
  used in the proof of Dirichlet Unit Theorem.

* `mixedEmbedding : K → mixedSpace K`: the map that sends `x : K` to `φ_w(x)` where, for all
  infinite place `w`, `φ_w : K → ℝ` or `ℂ`, resp. if `w` is real or if `w` is complex, denote a
  complex embedding associated to `w`.

* `logEmbedding : (𝓞 K)ˣ → logSpace K`: the map that sends the unit `u : (𝓞 K)ˣ` to
  `(mult w * log (w u))_w` for `w ≠ w₀`. Its image is `unitLattice K`, a `ℤ`-lattice of
  `logSpace K`, that admits `basisUnitLattice K` as a basis.

* `logMap : mixedSpace K → logSpace K`: this map is defined such that it factors `logEmbedding`,
  that is, for `u : (𝓞 K)ˣ`, `logMap (mixedEmbedding x) = logEmbedding x`, and that
  `logMap (c • x) = logMap x` for `c ≠ 0` and `norm x ≠ 0`. The inverse image of the fundamental
  domain of `basisUnitLattice K` by `logMap` (minus the elements of norm zero) is
  `fundamentalCone K`.

* `expMap : realSpace K → realSpace K`: the right inverse of `logMap` in the sense that
  `logMap (expMap x) = (x_w)_{w ≠ w₀}`.

* `expMapBasis : realSpace K → realSpace K`: the map that sends `x : realSpace K` to
  `Real.exp (x w₀) * ∏_{i ≠ w₀} |ηᵢ| ^ x i` where `|ηᵢ|` denote the vector of `realSpace K` given
  by `w (ηᵢ)` and `ηᵢ` denote the units in `fundSystem K`.

-/

@[expose] public section

variable (K : Type*) [Field K]

open Finset Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units dirichletUnitTheorem

namespace NumberField.mixedEmbedding.fundamentalCone

section normAtAllPlaces

variable [NumberField K]

variable {K}

/--
theorem `logMap_normAtAllPlaces` / 定理 `logMap_normAtAllPlaces`

English:
theorem logMap_normAtAllPlaces
  given: (x : mixedSpace K)
  proof: logMap_eq_of_normAtPlace_eq
    fun w => by rw [normAtPlace_mixedSpaceOfRealSpace (normAtPlace_nonneg w x)]

中文:
定理 logMap_normAtAllPlaces
  条件: (x : mixedSpace K)
  证明: logMap_eq_of_normAtPlace_eq
    fun w => by rw [normAtPlace_mixedSpaceOfRealSpace (normAtPlace_nonneg w x)]

Depends on / 依赖: logMap_eq_of_normAtPlace_eq, normAtPlace_mixedSpaceOfRealSpace, normAtPlace_nonneg
-/
theorem logMap_normAtAllPlaces (x : mixedSpace K) :
    logMap (mixedSpaceOfRealSpace (normAtAllPlaces x)) = logMap x :=
  logMap_eq_of_normAtPlace_eq
    fun w => by rw [normAtPlace_mixedSpaceOfRealSpace (normAtPlace_nonneg w x)]

/--
theorem `norm_normAtAllPlaces` / 定理 `norm_normAtAllPlaces`

English:
theorem norm_normAtAllPlaces
  given: (x : mixedSpace K)
  proof: by
  simp_rw [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (normAtAllPlaces_nonneg _ _)]

中文:
定理 norm_normAtAllPlaces
  条件: (x : mixedSpace K)
  证明: by
  simp_rw [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (normAtAllPlaces_nonneg _ _)]

Depends on / 依赖: mixedEmbedding, mixedEmbedding.norm_apply, normAtAllPlaces_nonneg, normAtPlace_mixedSpaceOfRealSpace, norm_apply, simp_rw
-/
theorem norm_normAtAllPlaces (x : mixedSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (normAtAllPlaces x)) = mixedEmbedding.norm x := by
  simp_rw [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (normAtAllPlaces_nonneg _ _)]

/--
theorem `normAtAllPlaces_mem_fundamentalCone_iff` / 定理 `normAtAllPlaces_mem_fundamentalCone_iff`

English:
theorem normAtAllPlaces_mem_fundamentalCone_iff
  given: {x : mixedSpace K}
  proof: by
  simp_rw [fundamentalCone, Set.mem_sdiff, Set.mem_preimage, logMap_normAtAllPlaces,
    Set.mem_ofPred_eq, norm_normAtAllPlaces]

中文:
定理 normAtAllPlaces_mem_fundamentalCone_iff
  条件: {x : mixedSpace K}
  证明: by
  simp_rw [fundamentalCone, Set.mem_sdiff, Set.mem_preimage, logMap_normAtAllPlaces,
    Set.mem_ofPred_eq, norm_normAtAllPlaces]

Depends on / 依赖: Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_sdiff, fundamentalCone, logMap_normAtAllPlaces, mem_ofPred_eq, mem_preimage, mem_sdiff, norm_normAtAllPlaces, simp_rw
-/
theorem normAtAllPlaces_mem_fundamentalCone_iff {x : mixedSpace K} :
    mixedSpaceOfRealSpace (normAtAllPlaces x) in fundamentalCone K ↔ x in fundamentalCone K := by
  simp_rw [fundamentalCone, Set.mem_sdiff, Set.mem_preimage, logMap_normAtAllPlaces,
    Set.mem_ofPred_eq, norm_normAtAllPlaces]

end normAtAllPlaces

section normLeOne_def

variable [NumberField K]

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `normLeOne` / `normLeOne` 的定义

English:
abbreviation normLeOne
  signature: : Set (mixedSpace K)
  body: fundamentalCone K inter {x | mixedEmbedding.norm x <= 1}

中文:
缩写 normLeOne
  签名: : Set (mixedSpace K)
  定义体: fundamentalCone K inter {x | mixedEmbedding.norm x <= 1}

Depends on / 依赖: fundamentalCone, mixedEmbedding, mixedEmbedding.norm
-/
noncomputable abbrev normLeOne : Set (mixedSpace K) :=
  fundamentalCone K inter {x | mixedEmbedding.norm x <= 1}

variable {K} in
/--
theorem `mem_normLeOne` / 定理 `mem_normLeOne`

English:
theorem mem_normLeOne
  given: {x : mixedSpace K}
  proof: Set.mem_sep_iff

中文:
定理 mem_normLeOne
  条件: {x : mixedSpace K}
  证明: Set.mem_sep_iff

Depends on / 依赖: Set.mem_sep_iff, mem_sep_iff
-/
theorem mem_normLeOne {x : mixedSpace K} :
    x in normLeOne K ↔ x in fundamentalCone K ∧ mixedEmbedding.norm x <= 1 := Set.mem_sep_iff

/--
theorem `measurableSet_normLeOne` / 定理 `measurableSet_normLeOne`

English:
theorem measurableSet_normLeOne
  proof: (measurableSet_fundamentalCone K).inter
    measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const

中文:
定理 measurableSet_normLeOne
  证明: (measurableSet_fundamentalCone K).inter
    measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const

Depends on / 依赖: continuous_norm, measurable, measurableSet_fundamentalCone, measurableSet_le, measurable_const, mixedEmbedding, mixedEmbedding.continuous_norm
-/
theorem measurableSet_normLeOne :
    MeasurableSet (normLeOne K) :=
(measurableSet_fundamentalCone K).inter
    measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const

/--
theorem `normLeOne_eq_preimage_image` / 定理 `normLeOne_eq_preimage_image`

English:
theorem normLeOne_eq_preimage_image
  proof: by
  refine subset_antisymm (Set.subset_preimage_image _ _) ?_
  rintro x ⟨y, hy₁, hy₂⟩
  rw [mem_normLeOne]; rw [← normAtAllPlaces_mem_fundamentalCone_iff]; rw [← norm_normAtAllPlaces]; rw [← mem_normLeOne] at hy₁ ⊢
  rwa [← hy₂]

中文:
定理 normLeOne_eq_preimage_image
  证明: by
  refine subset_antisymm (Set.subset_preimage_image _ _) ?_
  rintro x ⟨y, hy₁, hy₂⟩
  rw [mem_normLeOne]; rw [← normAtAllPlaces_mem_fundamentalCone_iff]; rw [← norm_normAtAllPlaces]; rw [← mem_normLeOne] at hy₁ ⊢
  rwa [← hy₂]

Depends on / 依赖: Set.subset_preimage_image, mem_normLeOne, normAtAllPlaces_mem_fundamentalCone_iff, norm_normAtAllPlaces, subset_antisymm, subset_preimage_image
-/
theorem normLeOne_eq_preimage_image :
    normLeOne K = normAtAllPlaces ⁻¹' normAtAllPlaces '' (normLeOne K) := by
  refine subset_antisymm (Set.subset_preimage_image _ _) ?_
  rintro x ⟨y, hy₁, hy₂⟩
  rw [mem_normLeOne]; rw [← normAtAllPlaces_mem_fundamentalCone_iff]; rw [← norm_normAtAllPlaces]; rw [← mem_normLeOne] at hy₁ ⊢
  rwa [← hy₂]

open scoped Classical in
/--
theorem `normAtAllPlaces_normLeOne` / 定理 `normAtAllPlaces_normLeOne`

English:
theorem normAtAllPlaces_normLeOne
  proof: by
  ext x
  refine ⟨?_, fun ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ => ?_⟩
  · rintro ⟨y, ⟨⟨h₁, h₂⟩, h₃⟩, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rwa [Set.mem_preimage, ← logMap_normAtAllPlaces] at h₁
    · exact fun w => normAtPlace_nonneg w y
    · rwa [Set.mem_ofPred_eq, ← norm_normAtAllPlaces] at h₂
    · rwa 

中文:
定理 normAtAllPlaces_normLeOne
  证明: by
  ext x
  refine ⟨?_, fun ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ => ?_⟩
  · rintro ⟨y, ⟨⟨h₁, h₂⟩, h₃⟩, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rwa [Set.mem_preimage, ← logMap_normAtAllPlaces] at h₁
    · exact fun w => normAtPlace_nonneg w y
    · rwa [Set.mem_ofPred_eq, ← norm_normAtAllPlaces] at h₂
    · rwa 

Depends on / 依赖: Set.mem_ofPred_eq, Set.mem_preimage, logMap_normAtAllPlaces, mem_ofPred_eq, mem_preimage, mixedSpaceOfRealSpace, normAtAllPlaces_mixedSpaceOfRealSpace, normAtPlace_nonneg, norm_normAtAllPlaces
-/
theorem normAtAllPlaces_normLeOne :
    normAtAllPlaces '' (normLeOne K) =
    mixedSpaceOfRealSpace ⁻¹'
      (logMap ⁻¹'
          ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis Real (unitLattice K))) inter
      {x | (forall w, 0 <= x w)} inter
      {x | mixedEmbedding.norm (mixedSpaceOfRealSpace x) != 0} inter
      {x | mixedEmbedding.norm (mixedSpaceOfRealSpace x) <= 1} := by
  ext x
  refine ⟨?_, fun ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ => ?_⟩
  · rintro ⟨y, ⟨⟨h₁, h₂⟩, h₃⟩, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rwa [Set.mem_preimage, ← logMap_normAtAllPlaces] at h₁
    · exact fun w => normAtPlace_nonneg w y
    · rwa [Set.mem_ofPred_eq, ← norm_normAtAllPlaces] at h₂
    · rwa [Set.mem_ofPred_eq, ← norm_normAtAllPlaces] at h₃
  · exact ⟨mixedSpaceOfRealSpace x, ⟨⟨h₁, h₃⟩, h₄⟩, normAtAllPlaces_mixedSpaceOfRealSpace h₂⟩

end normLeOne_def

noncomputable section expMap

variable {K}

/--
The component of `expMap` at the place `w`.
-/
@[simps]
/--
Definition of `expMap_single` / `expMap_single` 的定义

English:
definition expMap_single
  signature: (w : InfinitePlace K)
  body: fun x => Real.exp ((w.mult : Real)⁻¹ * x)
  invFun := fun x => w.mult * Real.log x
  source := Set.univ
  target := Set.Ioi 0
  open_source := isOpen_univ
  open_target := isOpen_Ioi
  map_source' _ _ := Real.exp_pos _
  map_target' _ _ := trivial
  left_inv' _ _ := by simp only [Real.log_exp, mul_i

中文:
定义 expMap_single
  签名: (w : InfinitePlace K)
  定义体: fun x => Real.exp ((w.mult : Real)⁻¹ * x)
  invFun := fun x => w.mult * Real.log x
  source := Set.univ
  target := Set.Ioi 0
  open_source := isOpen_univ
  open_target := isOpen_Ioi
  map_source' _ _ := Real.exp_pos _
  map_target' _ _ := trivial
  left_inv' _ _ := by simp only [Real.log_exp, mul_i

Depends on / 依赖: Real.exp, w.mult
-/
def expMap_single (w : InfinitePlace K) : OpenPartialHomeomorph Real Real where
  toFun := fun x => Real.exp ((w.mult : Real)⁻¹ * x)
  invFun := fun x => w.mult * Real.log x
  source := Set.univ
  target := Set.Ioi 0
  open_source := isOpen_univ
  open_target := isOpen_Ioi
  map_source' _ _ := Real.exp_pos _
  map_target' _ _ := trivial
  left_inv' _ _ := by simp only [Real.log_exp, mul_inv_cancel_left₀ mult_coe_ne_zero]
  right_inv' _ h := by simp only [inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log h]
  continuousOn_toFun := (continuousOn_const.mul continuousOn_id).rexp
  continuousOn_invFun := continuousOn_const.mul (Real.continuousOn_log.mono (by simp))

/--
Definition of `deriv_expMap_single` / `deriv_expMap_single` 的定义

English:
abbreviation deriv_expMap_single
  signature: (w : InfinitePlace K) (x : Real)
  body: (expMap_single w x) * (w.mult : Real)⁻¹

中文:
缩写 deriv_expMap_single
  签名: (w : InfinitePlace K) (x : 实数)
  定义体: (expMap_single w x) * (w.mult : Real)⁻¹

Depends on / 依赖: expMap_single, w.mult
-/
abbrev deriv_expMap_single (w : InfinitePlace K) (x : Real) : Real :=
  (expMap_single w x) * (w.mult : Real)⁻¹

/--
theorem `hasDerivAt_expMap_single` / 定理 `hasDerivAt_expMap_single`

English:
theorem hasDerivAt_expMap_single
  given: (w : InfinitePlace K) (x : Real)
  proof: by
  simpa [expMap_single, mul_comm] using!
    (HasDerivAt.comp x (Real.hasDerivAt_exp _) (hasDerivAt_mul_const (w.mult : Real)⁻¹))

中文:
定理 hasDerivAt_expMap_single
  条件: (w : InfinitePlace K) (x : 实数)
  证明: by
  simpa [expMap_single, mul_comm] using!
    (HasDerivAt.comp x (Real.hasDerivAt_exp _) (hasDerivAt_mul_const (w.mult : Real)⁻¹))

Depends on / 依赖: HasDerivAt, HasDerivAt.comp, Real.hasDerivAt_exp, expMap_single, hasDerivAt_exp, hasDerivAt_mul_const, mul_comm, w.mult
-/
theorem hasDerivAt_expMap_single (w : InfinitePlace K) (x : Real) :
    HasDerivAt (expMap_single w) (deriv_expMap_single w x) x := by
  simpa [expMap_single, mul_comm] using!
    (HasDerivAt.comp x (Real.hasDerivAt_exp _) (hasDerivAt_mul_const (w.mult : Real)⁻¹))


variable [NumberField K]

/--
Definition of `expMap` / `expMap` 的定义

English:
definition expMap
  signature: : OpenPartialHomeomorph (realSpace K) (realSpace K)
  body: OpenPartialHomeomorph.pi fun w => expMap_single w

中文:
定义 expMap
  签名: : OpenPartialHomeomorph (realSpace K) (realSpace K)
  定义体: OpenPartialHomeomorph.pi fun w => expMap_single w

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.pi, expMap_single
-/
def expMap : OpenPartialHomeomorph (realSpace K) (realSpace K) :=
  OpenPartialHomeomorph.pi fun w => expMap_single w

variable (K)

/--
theorem `expMap_source` / 定理 `expMap_source`

English:
theorem expMap_source
  proof: by
  simp_rw [expMap, OpenPartialHomeomorph.pi_toPartialHomeomorph,
    PartialEquiv.pi_source, expMap_single, Set.pi_univ Set.univ]

中文:
定理 expMap_source
  证明: by
  simp_rw [expMap, OpenPartialHomeomorph.pi_toPartialHomeomorph,
    PartialEquiv.pi_source, expMap_single, Set.pi_univ Set.univ]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.pi_toPartialHomeomorph, PartialEquiv, PartialEquiv.pi_source, Set.pi_univ, Set.univ, expMap, expMap_single, pi_source, pi_toPartialHomeomorph, pi_univ, simp_rw
-/
theorem expMap_source :
    expMap.source = (Set.univ : Set (realSpace K)) := by
  simp_rw [expMap, OpenPartialHomeomorph.pi_toPartialHomeomorph,
    PartialEquiv.pi_source, expMap_single, Set.pi_univ Set.univ]

/--
theorem `expMap_target` / 定理 `expMap_target`

English:
theorem expMap_target
  proof: by
  simp_rw [expMap, OpenPartialHomeomorph.pi_toPartialHomeomorph,
    PartialEquiv.pi_target, expMap_single]

中文:
定理 expMap_target
  证明: by
  simp_rw [expMap, OpenPartialHomeomorph.pi_toPartialHomeomorph,
    PartialEquiv.pi_target, expMap_single]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.pi_toPartialHomeomorph, PartialEquiv, PartialEquiv.pi_target, expMap, expMap_single, pi_target, pi_toPartialHomeomorph, simp_rw
-/
theorem expMap_target :
    expMap.target = Set.univ.pi fun (_ : InfinitePlace K) => Set.Ioi 0 := by
  simp_rw [expMap, OpenPartialHomeomorph.pi_toPartialHomeomorph,
    PartialEquiv.pi_target, expMap_single]

/--
theorem `injective_expMap` / 定理 `injective_expMap`

English:
theorem injective_expMap
  proof: Set.injOn_univ.1 (expMap_source K ▸ expMap.injOn)

中文:
定理 injective_expMap
  证明: Set.injOn_univ.1 (expMap_source K ▸ expMap.injOn)

Depends on / 依赖: Set.injOn_univ, expMap, expMap.injOn, expMap_source, injOn_univ
-/
theorem injective_expMap :
    Function.Injective (expMap : realSpace K -> realSpace K) :=
  Set.injOn_univ.1 (expMap_source K ▸ expMap.injOn)

/--
theorem `continuous_expMap` / 定理 `continuous_expMap`

English:
theorem continuous_expMap
  proof: continuousOn_univ.mp (expMap_source K) ▸ expMap.continuousOn

中文:
定理 continuous_expMap
  证明: continuousOn_univ.mp (expMap_source K) ▸ expMap.continuousOn

Depends on / 依赖: continuousOn, continuousOn_univ, continuousOn_univ.mp, expMap, expMap.continuousOn, expMap_source
-/
theorem continuous_expMap :
    Continuous (expMap : realSpace K -> realSpace K) :=
continuousOn_univ.mp (expMap_source K) ▸ expMap.continuousOn

variable {K}

@[simp]
/--
theorem `expMap_apply` / 定理 `expMap_apply`

English:
theorem expMap_apply
  given: (x : realSpace K) (w : InfinitePlace K)
  proof: rfl

中文:
定理 expMap_apply
  条件: (x : realSpace K) (w : InfinitePlace K)
  证明: rfl
-/
theorem expMap_apply (x : realSpace K) (w : InfinitePlace K) :
    expMap x w = Real.exp ((↑w.mult)⁻¹ * x w) := rfl

/--
theorem `expMap_pos` / 定理 `expMap_pos`

English:
theorem expMap_pos
  given: (x : realSpace K) (w : InfinitePlace K)
  proof: Real.exp_pos _

中文:
定理 expMap_pos
  条件: (x : realSpace K) (w : InfinitePlace K)
  证明: Real.exp_pos _

Depends on / 依赖: Real.exp_pos, exp_pos
-/
theorem expMap_pos (x : realSpace K) (w : InfinitePlace K) :
    0 < expMap x w := Real.exp_pos _

/--
theorem `expMap_smul` / 定理 `expMap_smul`

English:
theorem expMap_smul
  given: (c : Real) (x : realSpace K)
  proof: by
  ext
  simp [mul_comm c _, ← mul_assoc, Real.exp_mul]

中文:
定理 expMap_smul
  条件: (c : 实数) (x : realSpace K)
  证明: by
  ext
  simp [mul_comm c _, ← mul_assoc, Real.exp_mul]

Depends on / 依赖: Real.exp_mul, exp_mul, mul_assoc, mul_comm
-/
theorem expMap_smul (c : Real) (x : realSpace K) :
    expMap (c • x) = (expMap x) ^ c := by
  ext
  simp [mul_comm c _, ← mul_assoc, Real.exp_mul]

/--
theorem `expMap_add` / 定理 `expMap_add`

English:
theorem expMap_add
  given: (x y : realSpace K)
  proof: by
  ext
  simp [mul_add, Real.exp_add]

中文:
定理 expMap_add
  条件: (x y : realSpace K)
  证明: by
  ext
  simp [mul_add, Real.exp_add]

Depends on / 依赖: Real.exp_add, exp_add, mul_add
-/
theorem expMap_add (x y : realSpace K) :
    expMap (x + y) = expMap x * expMap y := by
  ext
  simp [mul_add, Real.exp_add]

/--
theorem `expMap_sum` / 定理 `expMap_sum`

English:
theorem expMap_sum
  given: {ι : Type*} (s : Finset ι) (f : ι -> realSpace K)
  proof: by
  ext
  simp [← Real.exp_sum, ← mul_sum]

@[simp]

中文:
定理 expMap_sum
  条件: {ι : 类型} (s : Finset ι) (f : ι -> realSpace K)
  证明: by
  ext
  simp [← Real.exp_sum, ← mul_sum]

@[simp]

Depends on / 依赖: Real.exp_sum, exp_sum, mul_sum
-/
theorem expMap_sum {ι : Type*} (s : Finset ι) (f : ι -> realSpace K) :
    expMap (∑ i in s, f i) = ∏ i in s, expMap (f i) := by
  ext
  simp [← Real.exp_sum, ← mul_sum]

@[simp]
/--
theorem `expMap_symm_apply` / 定理 `expMap_symm_apply`

English:
theorem expMap_symm_apply
  given: (x : realSpace K) (w : InfinitePlace K)
  proof: rfl

中文:
定理 expMap_symm_apply
  条件: (x : realSpace K) (w : InfinitePlace K)
  证明: rfl
-/
theorem expMap_symm_apply (x : realSpace K) (w : InfinitePlace K) :
    expMap.symm x w = ↑w.mult * Real.log (x w) := rfl

/--
theorem `logMap_expMap` / 定理 `logMap_expMap`

English:
theorem logMap_expMap
  statement: {x : realSpace K}
  proof: by
  ext
  rw [logMap]; rw [normAtPlace_mixedSpaceOfRealSpace (Real.exp_nonneg _)]; rw [expMap_apply]; rw [Real.log_exp]; rw [mul_sub]; rw [mul_inv_cancel_left₀ mult_coe_ne_zero]; rw [hx]; rw [Real.log_one]; rw [zero_mul]; rw [mul_zero]; rw [sub_zero]

中文:
定理 logMap_expMap
  结论: {x : realSpace K}
  证明: by
  ext
  rw [logMap]; rw [normAtPlace_mixedSpaceOfRealSpace (Real.exp_nonneg _)]; rw [expMap_apply]; rw [Real.log_exp]; rw [mul_sub]; rw [mul_inv_cancel_left₀ mult_coe_ne_zero]; rw [hx]; rw [Real.log_one]; rw [zero_mul]; rw [mul_zero]; rw [sub_zero]

Depends on / 依赖: Real.exp_nonneg, Real.log_exp, Real.log_one, expMap_apply, exp_nonneg, logMap, log_exp, log_one, mul_sub, mul_zero, mult_coe_ne_zero, normAtPlace_mixedSpaceOfRealSpace, sub_zero, zero_mul
-/
theorem logMap_expMap {x : realSpace K}
    (hx : mixedEmbedding.norm (mixedSpaceOfRealSpace (expMap x)) = 1) :
    logMap (mixedSpaceOfRealSpace (expMap x)) = fun w => x w.1 := by
  ext
  rw [logMap]; rw [normAtPlace_mixedSpaceOfRealSpace (Real.exp_nonneg _)]; rw [expMap_apply]; rw [Real.log_exp]; rw [mul_sub]; rw [mul_inv_cancel_left₀ mult_coe_ne_zero]; rw [hx]; rw [Real.log_one]; rw [zero_mul]; rw [mul_zero]; rw [sub_zero]

/--
theorem `sum_expMap_symm_apply` / 定理 `sum_expMap_symm_apply`

English:
theorem sum_expMap_symm_apply
  given: {x : K} (hx : x != 0)
  proof: by
  simp_rw [← prod_eq_abs_norm, Real.log_prod (fun _ _ => pow_ne_zero _ ((map_ne_zero _).mpr hx)),
    Real.log_pow, expMap_symm_apply, normAtAllPlaces_mixedEmbedding]

中文:
定理 sum_expMap_symm_apply
  条件: {x : K} (hx : x != 0)
  证明: by
  simp_rw [← prod_eq_abs_norm, Real.log_prod (fun _ _ => pow_ne_zero _ ((map_ne_zero _).mpr hx)),
    Real.log_pow, expMap_symm_apply, normAtAllPlaces_mixedEmbedding]

Depends on / 依赖: Real.log_pow, Real.log_prod, expMap_symm_apply, log_pow, log_prod, map_ne_zero, normAtAllPlaces_mixedEmbedding, pow_ne_zero, prod_eq_abs_norm, simp_rw
-/
theorem sum_expMap_symm_apply {x : K} (hx : x != 0) :
    ∑ w : InfinitePlace K, expMap.symm ((normAtAllPlaces (mixedEmbedding K x))) w =
      Real.log (|Algebra.norm Rat x| : Rat) := by
  simp_rw [← prod_eq_abs_norm, Real.log_prod (fun _ _ => pow_ne_zero _ ((map_ne_zero _).mpr hx)),
    Real.log_pow, expMap_symm_apply, normAtAllPlaces_mixedEmbedding]

/--
Definition of `fderiv_expMap` / `fderiv_expMap` 的定义

English:
abbreviation fderiv_expMap
  signature: (x : realSpace K)
  body: .pi fun w => (ContinuousLinearMap.smulRight (1 : Real ->L[Real] Real) (deriv_expMap_single w (x w))).comp
    (.proj w)

中文:
缩写 fderiv_expMap
  签名: (x : realSpace K)
  定义体: .pi fun w => (ContinuousLinearMap.smulRight (1 : Real ->L[Real] Real) (deriv_expMap_single w (x w))).comp
    (.proj w)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.smulRight, deriv_expMap_single, smulRight
-/
abbrev fderiv_expMap (x : realSpace K) : realSpace K ->L[Real] realSpace K :=
  .pi fun w => (ContinuousLinearMap.smulRight (1 : Real ->L[Real] Real) (deriv_expMap_single w (x w))).comp
    (.proj w)

/--
theorem `hasFDerivAt_expMap` / 定理 `hasFDerivAt_expMap`

English:
theorem hasFDerivAt_expMap
  given: (x : realSpace K)
  statement: HasFDerivAt expMap (fderiv_expMap x) x
  proof: by
  simpa [expMap, fderiv_expMap, hasFDerivAt_pi', OpenPartialHomeomorph.pi_apply,
    ContinuousLinearMap.proj_pi] using!
    fun w => (hasDerivAt_expMap_single w _).hasFDerivAt.comp x (hasFDerivAt_apply w x)

中文:
定理 hasFDerivAt_expMap
  条件: (x : realSpace K)
  结论: HasFDerivAt expMap (fderiv_expMap x) x
  证明: by
  simpa [expMap, fderiv_expMap, hasFDerivAt_pi', OpenPartialHomeomorph.pi_apply,
    ContinuousLinearMap.proj_pi] using!
    fun w => (hasDerivAt_expMap_single w _).hasFDerivAt.comp x (hasFDerivAt_apply w x)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.proj_pi, OpenPartialHomeomorph, OpenPartialHomeomorph.pi_apply, expMap, fderiv_expMap, hasDerivAt_expMap_single, hasFDerivAt, hasFDerivAt.comp, hasFDerivAt_apply, hasFDerivAt_pi, pi_apply, proj_pi
-/
theorem hasFDerivAt_expMap (x : realSpace K) : HasFDerivAt expMap (fderiv_expMap x) x := by
  simpa [expMap, fderiv_expMap, hasFDerivAt_pi', OpenPartialHomeomorph.pi_apply,
    ContinuousLinearMap.proj_pi] using!
    fun w => (hasDerivAt_expMap_single w _).hasFDerivAt.comp x (hasFDerivAt_apply w x)

end expMap

noncomputable section completeBasis

variable [NumberField K]

variable {K}

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
Definition of `equivFinRank` / `equivFinRank` 的定义

English:
definition equivFinRank
  signature: : Fin (rank K) ≃ {w : InfinitePlace K // w != w₀}
  body: Fintype.equivOfCardEq by
    rw [Fintype.card_subtype_compl]; rw [Fintype.card_ofSubsingleton]; rw [Fintype.card_fin]; rw [rank]

中文:
定义 equivFinRank
  签名: : Fin (rank K) ≃ {w : InfinitePlace K // w != w₀}
  定义体: Fintype.equivOfCardEq by
    rw [Fintype.card_subtype_compl]; rw [Fintype.card_ofSubsingleton]; rw [Fintype.card_fin]; rw [rank]

Depends on / 依赖: Fintype, Fintype.card_fin, Fintype.card_ofSubsingleton, Fintype.card_subtype_compl, Fintype.equivOfCardEq, card_fin, card_ofSubsingleton, card_subtype_compl, equivOfCardEq
-/
def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w != w₀} :=
Fintype.equivOfCardEq by
    rw [Fintype.card_subtype_compl]; rw [Fintype.card_ofSubsingleton]; rw [Fintype.card_fin]; rw [rank]

open scoped Classical in
variable (K) in
/--
Definition of `completeFamily` / `completeFamily` 的定义

English:
definition completeFamily
  signature: : InfinitePlace K -> realSpace K
  body: fun i => if hi : i = w₀ then fun w => mult w else
expMap.symm normAtAllPlaces mixedEmbedding K fundSystem K equivFinRank.symm ⟨i, hi⟩

中文:
定义 completeFamily
  签名: : InfinitePlace K -> realSpace K
  定义体: fun i => if hi : i = w₀ then fun w => mult w else
expMap.symm normAtAllPlaces mixedEmbedding K fundSystem K equivFinRank.symm ⟨i, hi⟩

Depends on / 依赖: equivFinRank, equivFinRank.symm, expMap, expMap.symm, fundSystem, mixedEmbedding, normAtAllPlaces
-/
def completeFamily : InfinitePlace K -> realSpace K :=
  fun i => if hi : i = w₀ then fun w => mult w else
expMap.symm normAtAllPlaces mixedEmbedding K fundSystem K equivFinRank.symm ⟨i, hi⟩

/--
Definition of `realSpaceToLogSpace` / `realSpaceToLogSpace` 的定义

English:
definition realSpaceToLogSpace
  signature: : realSpace K ->ₗ[Real] {w : InfinitePlace K // w != w₀} -> Real where
  body: fun x w => x w.1 - w.1.mult * (∑ w', x w') * (Module.finrank Rat K : Real)⁻¹
  map_add' := fun _ _ => funext fun _ => by simp [sum_add_distrib]; ring
  map_smul' := fun _ _ => funext fun _ => by simp [← mul_sum]; ring

中文:
定义 realSpaceToLogSpace
  签名: : realSpace K ->ₗ[实数] {w : InfinitePlace K // w != w₀} -> 实数 where
  定义体: fun x w => x w.1 - w.1.mult * (∑ w', x w') * (Module.finrank Rat K : Real)⁻¹
  map_add' := fun _ _ => funext fun _ => by simp [sum_add_distrib]; ring
  map_smul' := fun _ _ => funext fun _ => by simp [← mul_sum]; ring

Depends on / 依赖: Module, Module.finrank, finrank
-/
def realSpaceToLogSpace : realSpace K ->ₗ[Real] {w : InfinitePlace K // w != w₀} -> Real where
  toFun := fun x w => x w.1 - w.1.mult * (∑ w', x w') * (Module.finrank Rat K : Real)⁻¹
  map_add' := fun _ _ => funext fun _ => by simp [sum_add_distrib]; ring
  map_smul' := fun _ _ => funext fun _ => by simp [← mul_sum]; ring

/--
theorem `realSpaceToLogSpace_apply` / 定理 `realSpaceToLogSpace_apply`

English:
theorem realSpaceToLogSpace_apply
  given: (x : realSpace K) (w : {w : InfinitePlace K // w != w₀})
  proof: rfl

中文:
定理 realSpaceToLogSpace_apply
  条件: (x : realSpace K) (w : {w : InfinitePlace K // w != w₀})
  证明: rfl
-/
theorem realSpaceToLogSpace_apply (x : realSpace K) (w : {w : InfinitePlace K // w != w₀}) :
    realSpaceToLogSpace x w = x w - w.1.mult * (∑ w', x w') * (Module.finrank Rat K : Real)⁻¹ := rfl

/--
theorem `realSpaceToLogSpace_expMap_symm` / 定理 `realSpaceToLogSpace_expMap_symm`

English:
theorem realSpaceToLogSpace_expMap_symm
  given: {x : K} (hx : x != 0)
  proof: by
  ext w
  simp_rw [realSpaceToLogSpace_apply, sum_expMap_symm_apply hx, expMap_symm_apply,
    logMap, normAtPlace_apply, mul_sub, mul_assoc, norm_eq_norm]

中文:
定理 realSpaceToLogSpace_expMap_symm
  条件: {x : K} (hx : x != 0)
  证明: by
  ext w
  simp_rw [realSpaceToLogSpace_apply, sum_expMap_symm_apply hx, expMap_symm_apply,
    logMap, normAtPlace_apply, mul_sub, mul_assoc, norm_eq_norm]

Depends on / 依赖: expMap_symm_apply, logMap, mul_assoc, mul_sub, normAtPlace_apply, norm_eq_norm, realSpaceToLogSpace_apply, simp_rw, sum_expMap_symm_apply
-/
theorem realSpaceToLogSpace_expMap_symm {x : K} (hx : x != 0) :
    realSpaceToLogSpace (expMap.symm (normAtAllPlaces (mixedEmbedding K x))) =
      logMap (mixedEmbedding K x) := by
  ext w
  simp_rw [realSpaceToLogSpace_apply, sum_expMap_symm_apply hx, expMap_symm_apply,
    logMap, normAtPlace_apply, mul_sub, mul_assoc, norm_eq_norm]

/--
theorem `realSpaceToLogSpace_completeFamily_of_eq` / 定理 `realSpaceToLogSpace_completeFamily_of_eq`

English:
theorem realSpaceToLogSpace_completeFamily_of_eq
  proof: by
  ext
  rw [realSpaceToLogSpace_apply]; rw [completeFamily]; rw [dif_pos rfl]; rw [← Nat.cast_sum]; rw [sum_mult_eq]; rw [mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')]; rw [sub_self]; rw [Pi.zero_apply]

中文:
定理 realSpaceToLogSpace_completeFamily_of_eq
  证明: by
  ext
  rw [realSpaceToLogSpace_apply]; rw [completeFamily]; rw [dif_pos rfl]; rw [← Nat.cast_sum]; rw [sum_mult_eq]; rw [mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')]; rw [sub_self]; rw [Pi.zero_apply]

Depends on / 依赖: Module, Module.finrank_pos.ne, Nat.cast_ne_zero.mpr, Nat.cast_sum, Pi.zero_apply, cast_ne_zero, cast_sum, completeFamily, dif_pos, finrank_pos, realSpaceToLogSpace_apply, sub_self, sum_mult_eq, zero_apply
-/
theorem realSpaceToLogSpace_completeFamily_of_eq :
    realSpaceToLogSpace (completeFamily K w₀) = 0 := by
  ext
  rw [realSpaceToLogSpace_apply]; rw [completeFamily]; rw [dif_pos rfl]; rw [← Nat.cast_sum]; rw [sum_mult_eq]; rw [mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')]; rw [sub_self]; rw [Pi.zero_apply]

/--
theorem `realSpaceToLogSpace_completeFamily_of_ne` / 定理 `realSpaceToLogSpace_completeFamily_of_ne`

English:
theorem realSpaceToLogSpace_completeFamily_of_ne
  given: (i : {w : InfinitePlace K // w != w₀})
  proof: by
  ext
  rw [← logEmbedding_fundSystem]; rw [← logMap_eq_logEmbedding]; rw [completeFamily]; rw [dif_neg]; rw [realSpaceToLogSpace_expMap_symm]
  exact coe_ne_zero _

中文:
定理 realSpaceToLogSpace_completeFamily_of_ne
  条件: (i : {w : InfinitePlace K // w != w₀})
  证明: by
  ext
  rw [← logEmbedding_fundSystem]; rw [← logMap_eq_logEmbedding]; rw [completeFamily]; rw [dif_neg]; rw [realSpaceToLogSpace_expMap_symm]
  exact coe_ne_zero _

Depends on / 依赖: coe_ne_zero, completeFamily, dif_neg, logEmbedding_fundSystem, logMap_eq_logEmbedding, realSpaceToLogSpace_expMap_symm
-/
theorem realSpaceToLogSpace_completeFamily_of_ne (i : {w : InfinitePlace K // w != w₀}) :
    realSpaceToLogSpace (completeFamily K i) = basisUnitLattice K (equivFinRank.symm i) := by
  ext
  rw [← logEmbedding_fundSystem]; rw [← logMap_eq_logEmbedding]; rw [completeFamily]; rw [dif_neg]; rw [realSpaceToLogSpace_expMap_symm]
  exact coe_ne_zero _

/--
theorem `sum_eq_zero_of_mem_span_completeFamily` / 定理 `sum_eq_zero_of_mem_span_completeFamily`

English:
theorem sum_eq_zero_of_mem_span_completeFamily
  statement: {x : realSpace K}
  proof: by
  induction hx using Submodule.span_induction with
  | mem _ h =>
      obtain ⟨w, rfl⟩ := h
      simp_rw [completeFamily, dif_neg w.prop, sum_expMap_symm_apply (coe_ne_zero _),
        Units.norm, Rat.cast_one, Real.log_one]
  | zero => simp
  | add _ _ _ _ hx hy => simp [sum_add_distrib, hx, h

中文:
定理 sum_eq_zero_of_mem_span_completeFamily
  结论: {x : realSpace K}
  证明: by
  induction hx using Submodule.span_induction with
  | mem _ h =>
      obtain ⟨w, rfl⟩ := h
      simp_rw [completeFamily, dif_neg w.prop, sum_expMap_symm_apply (coe_ne_zero _),
        Units.norm, Rat.cast_one, Real.log_one]
  | zero => simp
  | add _ _ _ _ hx hy => simp [sum_add_distrib, hx, h

Depends on / 依赖: Rat.cast_one, Real.log_one, Submodule, Submodule.span_induction, Units.norm, cast_one, coe_ne_zero, completeFamily, dif_neg, log_one, mul_sum, simp_rw, span_induction, sum_add_distrib, sum_expMap_symm_apply, w.prop
-/
theorem sum_eq_zero_of_mem_span_completeFamily {x : realSpace K}
    (hx : x in Submodule.span Real (Set.range fun w : {w // w != w₀} => completeFamily K w.1)) :
    ∑ w, x w = 0 := by
  induction hx using Submodule.span_induction with
  | mem _ h =>
      obtain ⟨w, rfl⟩ := h
      simp_rw [completeFamily, dif_neg w.prop, sum_expMap_symm_apply (coe_ne_zero _),
        Units.norm, Rat.cast_one, Real.log_one]
  | zero => simp
  | add _ _ _ _ hx hy => simp [sum_add_distrib, hx, hy]
  | smul _ _ _ hx => simp [← mul_sum, hx]

variable (K)

/--
theorem `linearIndependent_completeFamily` / 定理 `linearIndependent_completeFamily`

English:
theorem linearIndependent_completeFamily
  proof: by
  classical
  have h₁ : LinearIndependent Real (fun w : {w // w != w₀} => completeFamily K w.1) := by
    refine LinearIndependent.of_comp realSpaceToLogSpace ?_
    simp_rw [Function.comp_def, realSpaceToLogSpace_completeFamily_of_ne]
    convert! (((basisUnitLattice K).ofZLatticeBasis Real _).r

中文:
定理 linearIndependent_completeFamily
  证明: by
  classical
  have h₁ : LinearIndependent Real (fun w : {w // w != w₀} => completeFamily K w.1) := by
    refine LinearIndependent.of_comp realSpaceToLogSpace ?_
    simp_rw [Function.comp_def, realSpaceToLogSpace_completeFamily_of_ne]
    convert! (((basisUnitLattice K).ofZLatticeBasis Real _).r

Depends on / 依赖: Function, Function.comp_def, LinearIndependent, LinearIndependent.of_comp, Set.range, Submodule, Submodule.span, basisUnitLattice, classical, comp_def, completeFamily, convert, equivFinRank, linearIndependent, ofZLatticeBasis, of_comp, realSpaceToLogSpace, realSpaceToLogSpace_completeFamily_of_ne, reindex, simp_rw
-/
theorem linearIndependent_completeFamily :
    LinearIndependent Real (completeFamily K) := by
  classical
  have h₁ : LinearIndependent Real (fun w : {w // w != w₀} => completeFamily K w.1) := by
    refine LinearIndependent.of_comp realSpaceToLogSpace ?_
    simp_rw [Function.comp_def, realSpaceToLogSpace_completeFamily_of_ne]
    convert! (((basisUnitLattice K).ofZLatticeBasis Real _).reindex equivFinRank).linearIndependent
    simp
  have h₂ : completeFamily K w₀ ∉ Submodule.span Real
      (Set.range (fun w : {w // w != w₀} => completeFamily K w.1)) := by
    intro h
    have := sum_eq_zero_of_mem_span_completeFamily h
    rw [completeFamily]; rw [dif_pos rfl]; rw [← Nat.cast_sum]; rw [sum_mult_eq]; rw [Nat.cast_eq_zero] at this
    exact Module.finrank_pos.ne' this
  rw [← linearIndependent_equiv (Equiv.optionSubtypeNe w₀)]; rw [linearIndependent_option]
  exact ⟨h₁, h₂⟩

/--
Definition of `completeBasis` / `completeBasis` 的定义

English:
definition completeBasis
  signature: : Basis (InfinitePlace K) Real (realSpace K)
  body: basisOfLinearIndependentOfCardEqFinrank (linearIndependent_completeFamily K)
    (Module.finrank_fintype_fun_eq_card _).symm

中文:
定义 completeBasis
  签名: : Basis (InfinitePlace K) 实数 (realSpace K)
  定义体: basisOfLinearIndependentOfCardEqFinrank (linearIndependent_completeFamily K)
    (Module.finrank_fintype_fun_eq_card _).symm

Depends on / 依赖: Module, Module.finrank_fintype_fun_eq_card, basisOfLinearIndependentOfCardEqFinrank, finrank_fintype_fun_eq_card, linearIndependent_completeFamily
-/
def completeBasis : Basis (InfinitePlace K) Real (realSpace K) :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_completeFamily K)
    (Module.finrank_fintype_fun_eq_card _).symm

/--
theorem `completeBasis_apply_of_eq` / 定理 `completeBasis_apply_of_eq`

English:
theorem completeBasis_apply_of_eq
  proof: by
  rw [completeBasis]; rw [coe_basisOfLinearIndependentOfCardEqFinrank]; rw [completeFamily]; rw [dif_pos rfl]

中文:
定理 completeBasis_apply_of_eq
  证明: by
  rw [completeBasis]; rw [coe_basisOfLinearIndependentOfCardEqFinrank]; rw [completeFamily]; rw [dif_pos rfl]

Depends on / 依赖: coe_basisOfLinearIndependentOfCardEqFinrank, completeBasis, completeFamily, dif_pos
-/
theorem completeBasis_apply_of_eq :
    completeBasis K w₀ = fun w => (mult w : Real) := by
  rw [completeBasis]; rw [coe_basisOfLinearIndependentOfCardEqFinrank]; rw [completeFamily]; rw [dif_pos rfl]

/--
theorem `completeBasis_apply_of_ne` / 定理 `completeBasis_apply_of_ne`

English:
theorem completeBasis_apply_of_ne
  given: (i : {w : InfinitePlace K // w != w₀})
  proof: by
  rw [completeBasis]; rw [coe_basisOfLinearIndependentOfCardEqFinrank]; rw [completeFamily]; rw [dif_neg]

中文:
定理 completeBasis_apply_of_ne
  条件: (i : {w : InfinitePlace K // w != w₀})
  证明: by
  rw [completeBasis]; rw [coe_basisOfLinearIndependentOfCardEqFinrank]; rw [completeFamily]; rw [dif_neg]

Depends on / 依赖: coe_basisOfLinearIndependentOfCardEqFinrank, completeBasis, completeFamily, dif_neg
-/
theorem completeBasis_apply_of_ne (i : {w : InfinitePlace K // w != w₀}) :
    completeBasis K i =
      expMap.symm (normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm i)))) := by
  rw [completeBasis]; rw [coe_basisOfLinearIndependentOfCardEqFinrank]; rw [completeFamily]; rw [dif_neg]

/--
theorem `expMap_basis_of_eq` / 定理 `expMap_basis_of_eq`

English:
theorem expMap_basis_of_eq
  proof: by
  ext
  simp_rw [expMap_apply, completeBasis_apply_of_eq, inv_mul_cancel₀ mult_coe_ne_zero]

中文:
定理 expMap_basis_of_eq
  证明: by
  ext
  simp_rw [expMap_apply, completeBasis_apply_of_eq, inv_mul_cancel₀ mult_coe_ne_zero]

Depends on / 依赖: completeBasis_apply_of_eq, expMap_apply, mult_coe_ne_zero, simp_rw
-/
theorem expMap_basis_of_eq :
    expMap (completeBasis K w₀) = fun _ => Real.exp 1 := by
  ext
  simp_rw [expMap_apply, completeBasis_apply_of_eq, inv_mul_cancel₀ mult_coe_ne_zero]

/--
theorem `expMap_basis_of_ne` / 定理 `expMap_basis_of_ne`

English:
theorem expMap_basis_of_ne
  given: (i : {w : InfinitePlace K // w != w₀})
  proof: by
  rw [completeBasis_apply_of_ne]; rw [expMap.right_inv (by simp [expMap_target]; rw [pos_at_place])]

中文:
定理 expMap_basis_of_ne
  条件: (i : {w : InfinitePlace K // w != w₀})
  证明: by
  rw [completeBasis_apply_of_ne]; rw [expMap.right_inv (by simp [expMap_target]; rw [pos_at_place])]

Depends on / 依赖: completeBasis_apply_of_ne, expMap, expMap.right_inv, expMap_target, pos_at_place, right_inv
-/
theorem expMap_basis_of_ne (i : {w : InfinitePlace K // w != w₀}) :
    expMap (completeBasis K i) =
      normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm i))) := by
  rw [completeBasis_apply_of_ne]; rw [expMap.right_inv (by simp [expMap_target]; rw [pos_at_place])]

/--
theorem `abs_det_completeBasis_equivFunL_symm` / 定理 `abs_det_completeBasis_equivFunL_symm`

English:
theorem abs_det_completeBasis_equivFunL_symm
  proof: by
  classical
  rw [ContinuousLinearMap.det]; rw [← LinearMap.det_toMatrix (completeBasis K)]; rw [← Matrix.det_transpose]; rw [regulator_eq_regOfFamily_fundSystem]; rw [finrank_mul_regOfFamily_eq_det _ w₀ equivFinRank.symm]
  congr 2 with w i
  rw [Matrix.transpose_apply]; rw [LinearMap.toMatrix_a

中文:
定理 abs_det_completeBasis_equivFunL_symm
  证明: by
  classical
  rw [ContinuousLinearMap.det]; rw [← LinearMap.det_toMatrix (completeBasis K)]; rw [← Matrix.det_transpose]; rw [regulator_eq_regOfFamily_fundSystem]; rw [finrank_mul_regOfFamily_eq_det _ w₀ equivFinRank.symm]
  congr 2 with w i
  rw [Matrix.transpose_apply]; rw [LinearMap.toMatrix_a

Depends on / 依赖: Basis.equivFunL_apply, ContinuousLinearEquiv, ContinuousLinearEquiv.coe_apply, ContinuousLinearMap, ContinuousLinearMap.coe_coe, ContinuousLinearMap.det, LinearMap, LinearMap.det_toMatrix, LinearMap.toMatrix_apply, Matrix, Matrix.det_transpose, Matrix.of_apply, Matrix.transpose_apply, apply_symm_apply, classical, coe_apply, coe_coe, completeBasis, det_toMatrix, det_transpose
-/
theorem abs_det_completeBasis_equivFunL_symm :
    |((completeBasis K).equivFunL.symm : realSpace K ->L[Real] realSpace K).det| =
      Module.finrank Rat K * regulator K := by
  classical
  rw [ContinuousLinearMap.det]; rw [← LinearMap.det_toMatrix (completeBasis K)]; rw [← Matrix.det_transpose]; rw [regulator_eq_regOfFamily_fundSystem]; rw [finrank_mul_regOfFamily_eq_det _ w₀ equivFinRank.symm]
  congr 2 with w i
  rw [Matrix.transpose_apply]; rw [LinearMap.toMatrix_apply]; rw [Matrix.of_apply]; rw [← Basis.equivFunL_apply]; rw [ContinuousLinearMap.coe_coe]; rw [ContinuousLinearEquiv.coe_apply]; rw [(completeBasis K).equivFunL.apply_symm_apply]
  split_ifs with hw
  · rw [hw, completeBasis_apply_of_eq]
  · simp_rw [completeBasis_apply_of_ne K ⟨w, hw⟩, expMap_symm_apply, normAtAllPlaces_mixedEmbedding]

end completeBasis

noncomputable section expMapBasis

variable [NumberField K]

variable {K}

/--
Definition of `expMapBasis` / `expMapBasis` 的定义

English:
definition expMapBasis
  signature: : OpenPartialHomeomorph (realSpace K) (realSpace K)
  body: (completeBasis K).equivFunL.symm.toHomeomorph.transOpenPartialHomeomorph expMap

中文:
定义 expMapBasis
  签名: : OpenPartialHomeomorph (realSpace K) (realSpace K)
  定义体: (completeBasis K).equivFunL.symm.toHomeomorph.transOpenPartialHomeomorph expMap

Depends on / 依赖: completeBasis, equivFunL, equivFunL.symm.toHomeomorph.transOpenPartialHomeomorph, expMap, toHomeomorph, transOpenPartialHomeomorph
-/
def expMapBasis : OpenPartialHomeomorph (realSpace K) (realSpace K) :=
  (completeBasis K).equivFunL.symm.toHomeomorph.transOpenPartialHomeomorph expMap

variable (K)

/--
theorem `expMapBasis_source` / 定理 `expMapBasis_source`

English:
theorem expMapBasis_source
  proof: by
  simp [expMapBasis, expMap_source]

中文:
定理 expMapBasis_source
  证明: by
  simp [expMapBasis, expMap_source]

Depends on / 依赖: expMapBasis, expMap_source
-/
theorem expMapBasis_source :
    expMapBasis.source = (Set.univ : Set (realSpace K)) := by
  simp [expMapBasis, expMap_source]

/--
theorem `injective_expMapBasis` / 定理 `injective_expMapBasis`

English:
theorem injective_expMapBasis
  proof: (injective_expMap K).comp (completeBasis K).equivFun.symm.injective

中文:
定理 injective_expMapBasis
  证明: (injective_expMap K).comp (completeBasis K).equivFun.symm.injective

Depends on / 依赖: completeBasis, equivFun, equivFun.symm.injective, injective, injective_expMap
-/
theorem injective_expMapBasis :
    Function.Injective (expMapBasis : realSpace K -> realSpace K) :=
  (injective_expMap K).comp (completeBasis K).equivFun.symm.injective

/--
theorem `continuous_expMapBasis` / 定理 `continuous_expMapBasis`

English:
theorem continuous_expMapBasis
  proof: (continuous_expMap K).comp (ContinuousLinearEquiv.continuous _)

中文:
定理 continuous_expMapBasis
  证明: (continuous_expMap K).comp (ContinuousLinearEquiv.continuous _)

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.continuous, continuous, continuous_expMap
-/
theorem continuous_expMapBasis :
    Continuous (expMapBasis : realSpace K -> realSpace K) :=
  (continuous_expMap K).comp (ContinuousLinearEquiv.continuous _)

variable {K}

/--
theorem `expMapBasis_pos` / 定理 `expMapBasis_pos`

English:
theorem expMapBasis_pos
  given: (x : realSpace K) (w : InfinitePlace K)
  proof: expMap_pos _ _

中文:
定理 expMapBasis_pos
  条件: (x : realSpace K) (w : InfinitePlace K)
  证明: expMap_pos _ _

Depends on / 依赖: expMap_pos
-/
theorem expMapBasis_pos (x : realSpace K) (w : InfinitePlace K) :
    0 < expMapBasis x w := expMap_pos _ _

/--
theorem `expMapBasis_nonneg` / 定理 `expMapBasis_nonneg`

English:
theorem expMapBasis_nonneg
  given: (x : realSpace K) (w : InfinitePlace K)
  proof: (expMapBasis_pos _ _).le

中文:
定理 expMapBasis_nonneg
  条件: (x : realSpace K) (w : InfinitePlace K)
  证明: (expMapBasis_pos _ _).le

Depends on / 依赖: expMapBasis_pos
-/
theorem expMapBasis_nonneg (x : realSpace K) (w : InfinitePlace K) :
    0 <= expMapBasis x w := (expMapBasis_pos _ _).le

/--
theorem `expMapBasis_apply` / 定理 `expMapBasis_apply`

English:
theorem expMapBasis_apply
  given: (x : realSpace K)
  proof: rfl

中文:
定理 expMapBasis_apply
  条件: (x : realSpace K)
  证明: rfl
-/
theorem expMapBasis_apply (x : realSpace K) :
    expMapBasis x = expMap ((completeBasis K).equivFun.symm x) := rfl

open scoped Classical in
/--
theorem `expMapBasis_apply'` / 定理 `expMapBasis_apply'`

English:
theorem expMapBasis_apply'
  given: (x : realSpace K)
  proof: by
  simp_rw [expMapBasis_apply, Basis.equivFun_symm_apply, Fintype.sum_eq_add_sum_subtype_ne _ w₀,
    expMap_add, expMap_smul, expMap_basis_of_eq, Pi.pow_def, Real.exp_one_rpow, Pi.mul_def,
    expMap_sum, expMap_smul, expMap_basis_of_ne, Pi.smul_def, smul_eq_mul, prod_apply, Pi.pow_apply,
    nor

中文:
定理 expMapBasis_apply'
  条件: (x : realSpace K)
  证明: by
  simp_rw [expMapBasis_apply, Basis.equivFun_symm_apply, Fintype.sum_eq_add_sum_subtype_ne _ w₀,
    expMap_add, expMap_smul, expMap_basis_of_eq, Pi.pow_def, Real.exp_one_rpow, Pi.mul_def,
    expMap_sum, expMap_smul, expMap_basis_of_ne, Pi.smul_def, smul_eq_mul, prod_apply, Pi.pow_apply,
    nor

Depends on / 依赖: Basis.equivFun_symm_apply, Fintype, Fintype.sum_eq_add_sum_subtype_ne, Pi.mul_def, Pi.pow_apply, Pi.pow_def, Pi.smul_def, Real.exp_one_rpow, equivFun_symm_apply, expMapBasis_apply, expMap_add, expMap_basis_of_eq, expMap_basis_of_ne, expMap_smul, expMap_sum, exp_one_rpow, mul_def, normAtAllPlaces_mixedEmbedding, pow_apply, pow_def
-/
theorem expMapBasis_apply' (x : realSpace K) :
    expMapBasis x = Real.exp (x w₀) •
      fun w : InfinitePlace K =>
         ∏ i : {w // w != w₀}, w (fundSystem K (equivFinRank.symm i)) ^ x i := by
  simp_rw [expMapBasis_apply, Basis.equivFun_symm_apply, Fintype.sum_eq_add_sum_subtype_ne _ w₀,
    expMap_add, expMap_smul, expMap_basis_of_eq, Pi.pow_def, Real.exp_one_rpow, Pi.mul_def,
    expMap_sum, expMap_smul, expMap_basis_of_ne, Pi.smul_def, smul_eq_mul, prod_apply, Pi.pow_apply,
    normAtAllPlaces_mixedEmbedding]

open scoped Classical in
/--
theorem `expMapBasis_apply''` / 定理 `expMapBasis_apply''`

English:
theorem expMapBasis_apply''
  given: (x : realSpace K)
  proof: by
  rw [expMapBasis_apply']; rw [expMapBasis_apply']; rw [if_pos rfl]; rw [smul_smul]; rw [← Real.exp_add]; rw [add_zero]
  conv_rhs =>
    enter [2, w, 2, i]
    rw [if_neg i.prop]

中文:
定理 expMapBasis_apply''
  条件: (x : realSpace K)
  证明: by
  rw [expMapBasis_apply']; rw [expMapBasis_apply']; rw [if_pos rfl]; rw [smul_smul]; rw [← Real.exp_add]; rw [add_zero]
  conv_rhs =>
    enter [2, w, 2, i]
    rw [if_neg i.prop]

Depends on / 依赖: Real.exp_add, add_zero, conv_rhs, expMapBasis_apply, exp_add, i.prop, if_neg, if_pos, smul_smul
-/
theorem expMapBasis_apply'' (x : realSpace K) :
    expMapBasis x = Real.exp (x w₀) • expMapBasis (fun i => if i = w₀ then 0 else x i) := by
  rw [expMapBasis_apply']; rw [expMapBasis_apply']; rw [if_pos rfl]; rw [smul_smul]; rw [← Real.exp_add]; rw [add_zero]
  conv_rhs =>
    enter [2, w, 2, i]
    rw [if_neg i.prop]

/--
theorem `prod_expMapBasis_pow` / 定理 `prod_expMapBasis_pow`

English:
theorem prod_expMapBasis_pow
  given: (x : realSpace K)
  proof: by
  simp_rw [expMapBasis_apply', Pi.smul_def, smul_eq_mul, mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, sum_mult_eq, ← prod_pow]
  rw [prod_comm]
  simp_rw [Real.rpow_pow_comm (apply_nonneg _ _), Real.finsetProd_rpow _ _
    fun _ _ => pow_nonneg (apply_nonneg _ _) _, prod_eq_abs_norm, Units

中文:
定理 prod_expMapBasis_pow
  条件: (x : realSpace K)
  证明: by
  simp_rw [expMapBasis_apply', Pi.smul_def, smul_eq_mul, mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, sum_mult_eq, ← prod_pow]
  rw [prod_comm]
  simp_rw [Real.rpow_pow_comm (apply_nonneg _ _), Real.finsetProd_rpow _ _
    fun _ _ => pow_nonneg (apply_nonneg _ _) _, prod_eq_abs_norm, Units

Depends on / 依赖: Pi.smul_def, Rat.cast_one, Real.finsetProd_rpow, Real.one_rpow, Real.rpow_pow_comm, Units.norm, apply_nonneg, cast_one, expMapBasis_apply, finsetProd_rpow, mul_one, mul_pow, one_rpow, pow_nonneg, prod_comm, prod_const_one, prod_eq_abs_norm, prod_mul_distrib, prod_pow, prod_pow_eq_pow_sum
-/
theorem prod_expMapBasis_pow (x : realSpace K) :
    ∏ w, (expMapBasis x w) ^ w.mult = Real.exp (x w₀) ^ Module.finrank Rat K := by
  simp_rw [expMapBasis_apply', Pi.smul_def, smul_eq_mul, mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, sum_mult_eq, ← prod_pow]
  rw [prod_comm]
  simp_rw [Real.rpow_pow_comm (apply_nonneg _ _), Real.finsetProd_rpow _ _
    fun _ _ => pow_nonneg (apply_nonneg _ _) _, prod_eq_abs_norm, Units.norm, Rat.cast_one,
    Real.one_rpow, prod_const_one, mul_one]

/--
theorem `norm_expMapBasis` / 定理 `norm_expMapBasis`

English:
theorem norm_expMapBasis
  given: (x : realSpace K)
  proof: by
  simpa only [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (expMapBasis_pos _ _).le] using prod_expMapBasis_pow x

中文:
定理 norm_expMapBasis
  条件: (x : realSpace K)
  证明: by
  simpa only [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (expMapBasis_pos _ _).le] using prod_expMapBasis_pow x

Depends on / 依赖: expMapBasis_pos, mixedEmbedding, mixedEmbedding.norm_apply, normAtPlace_mixedSpaceOfRealSpace, norm_apply, prod_expMapBasis_pow
-/
theorem norm_expMapBasis (x : realSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasis x)) =
      Real.exp (x w₀) ^ Module.finrank Rat K := by
  simpa only [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (expMapBasis_pos _ _).le] using prod_expMapBasis_pow x

/--
theorem `norm_expMapBasis_ne_zero` / 定理 `norm_expMapBasis_ne_zero`

English:
theorem norm_expMapBasis_ne_zero
  given: (x : realSpace K)
  proof: norm_expMapBasis x ▸ pow_ne_zero _ (Real.exp_ne_zero _)

中文:
定理 norm_expMapBasis_ne_zero
  条件: (x : realSpace K)
  证明: norm_expMapBasis x ▸ pow_ne_zero _ (Real.exp_ne_zero _)

Depends on / 依赖: Real.exp_ne_zero, exp_ne_zero, norm_expMapBasis, pow_ne_zero
-/
theorem norm_expMapBasis_ne_zero (x : realSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasis x)) != 0 :=
  norm_expMapBasis x ▸ pow_ne_zero _ (Real.exp_ne_zero _)

open scoped Classical in
/--
theorem `logMap_expMapBasis` / 定理 `logMap_expMapBasis`

English:
theorem logMap_expMapBasis
  given: (x : realSpace K)
  proof: by
  simp_rw [ZSpan.mem_fundamentalDomain, equivFinRank.forall_congr_left, Subtype.forall]
  refine forall₂_congr fun w hw => ?_
  rw [expMapBasis_apply'']; rw [map_smul]; rw [logMap_real_smul (norm_expMapBasis_ne_zero _)
    (Real.exp_ne_zero _)]; rw [expMapBasis_apply]; rw [logMap_expMap (by rw [←

中文:
定理 logMap_expMapBasis
  条件: (x : realSpace K)
  证明: by
  simp_rw [ZSpan.mem_fundamentalDomain, equivFinRank.forall_congr_left, Subtype.forall]
  refine forall₂_congr fun w hw => ?_
  rw [expMapBasis_apply'']; rw [map_smul]; rw [logMap_real_smul (norm_expMapBasis_ne_zero _)
    (Real.exp_ne_zero _)]; rw [expMapBasis_apply]; rw [logMap_expMap (by rw [←

Depends on / 依赖: Basis.equivFun_symm_apply, Fintype, Fintype.sum_eq_add_sum_subtype_ne, Real.exp_ne_zero, Real.exp_zero, Subtype, Subtype.forall, ZSpan.mem_fundamentalDomain, conv_lhs, equivFinRank, equivFinRank.forall_congr_left, equivFun_symm_apply, expMapBasis_apply, exp_ne_zero, exp_zero, forall_congr_left, if_pos, logMap_expMap, logMap_real_smul, map_smul
-/
theorem logMap_expMapBasis (x : realSpace K) :
    logMap (mixedSpaceOfRealSpace (expMapBasis x)) in
        ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis Real (unitLattice K))
      ↔ forall w, w != w₀ -> x w in Set.Ico 0 1 := by
  simp_rw [ZSpan.mem_fundamentalDomain, equivFinRank.forall_congr_left, Subtype.forall]
  refine forall₂_congr fun w hw => ?_
  rw [expMapBasis_apply'']; rw [map_smul]; rw [logMap_real_smul (norm_expMapBasis_ne_zero _)
    (Real.exp_ne_zero _)]; rw [expMapBasis_apply]; rw [logMap_expMap (by rw [← expMapBasis_apply]; rw [norm_expMapBasis]; rw [if_pos rfl]; rw [Real.exp_zero]; rw [one_pow]), Basis.equivFun_symm_apply,
    Fintype.sum_eq_add_sum_subtype_ne _ w₀, if_pos rfl, zero_smul, zero_add]
  conv_lhs =>
    enter [2, 1, 2, w, 2, i]
    rw [if_neg i.prop]
  simp_rw [Finset.sum_apply, ← sum_fn, map_sum, Pi.smul_apply, ← Pi.smul_def, map_smul,
    completeBasis_apply_of_ne, expMap_symm_apply, normAtAllPlaces_mixedEmbedding,
    ← logEmbedding_component, logEmbedding_fundSystem, Finsupp.coe_finsetSum, Finsupp.coe_smul,
    Finset.sum_apply, Pi.smul_apply, Basis.ofZLatticeBasis_repr_apply, Basis.repr_self,
    Finsupp.single_apply, EmbeddingLike.apply_eq_iff_eq, Int.cast_ite, Int.cast_one, Int.cast_zero,
    smul_ite, smul_eq_mul, mul_one, mul_zero, Fintype.sum_ite_eq']

/--
theorem `normAtAllPlaces_image_preimage_expMapBasis` / 定理 `normAtAllPlaces_image_preimage_expMapBasis`

English:
theorem normAtAllPlaces_image_preimage_expMapBasis
  given: (s : Set (realSpace K))
  proof: by
  apply normAtAllPlaces_image_preimage_of_nonneg
  rintro _ ⟨x, _, rfl⟩ w
  exact (expMapBasis_pos _ _).le

中文:
定理 normAtAllPlaces_image_preimage_expMapBasis
  条件: (s : Set (realSpace K))
  证明: by
  apply normAtAllPlaces_image_preimage_of_nonneg
  rintro _ ⟨x, _, rfl⟩ w
  exact (expMapBasis_pos _ _).le

Depends on / 依赖: expMapBasis_pos, normAtAllPlaces_image_preimage_of_nonneg
-/
theorem normAtAllPlaces_image_preimage_expMapBasis (s : Set (realSpace K)) :
    normAtAllPlaces '' normAtAllPlaces ⁻¹' expMapBasis '' s = expMapBasis '' s := by
  apply normAtAllPlaces_image_preimage_of_nonneg
  rintro _ ⟨x, _, rfl⟩ w
  exact (expMapBasis_pos _ _).le

open scoped Classical in
/--
theorem `prod_deriv_expMap_single` / 定理 `prod_deriv_expMap_single`

English:
theorem prod_deriv_expMap_single
  given: (x : realSpace K)
  proof: by
  simp only [deriv_expMap_single, expMap_single_apply]
  rw [Finset.prod_mul_distrib]
  congr 1
  · simp_rw [← prod_expMapBasis_pow, prod_eq_prod_mul_prod, expMapBasis_apply, expMap_apply,
      mult_isReal, mult_isComplex, pow_one, Finset.prod_pow, pow_two, mul_assoc, mul_inv_cancel₀
      (Fins

中文:
定理 prod_deriv_expMap_single
  条件: (x : realSpace K)
  证明: by
  simp only [deriv_expMap_single, expMap_single_apply]
  rw [Finset.prod_mul_distrib]
  congr 1
  · simp_rw [← prod_expMapBasis_pow, prod_eq_prod_mul_prod, expMapBasis_apply, expMap_apply,
      mult_isReal, mult_isComplex, pow_one, Finset.prod_pow, pow_two, mul_assoc, mul_inv_cancel₀
      (Fins

Depends on / 依赖: Finset, Finset.prod_mul_distrib, Finset.prod_ne_zero_iff.mpr, Finset.prod_pow, Real.exp_ne_zero, deriv_expMap_single, expMapBasis_apply, expMap_apply, expMap_single_apply, exp_ne_zero, mul_assoc, mul_one, mult_isComplex, mult_isReal, pow_one, pow_two, prod_eq_prod_mul_prod, prod_expMapBasis_pow, prod_mul_distrib, prod_ne_zero_iff
-/
theorem prod_deriv_expMap_single (x : realSpace K) :
    ∏ w, deriv_expMap_single w ((completeBasis K).equivFun.symm x w) =
      Real.exp (x w₀) ^ Module.finrank Rat K * (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ *
        (2⁻¹) ^ nrComplexPlaces K := by
  simp only [deriv_expMap_single, expMap_single_apply]
  rw [Finset.prod_mul_distrib]
  congr 1
  · simp_rw [← prod_expMapBasis_pow, prod_eq_prod_mul_prod, expMapBasis_apply, expMap_apply,
      mult_isReal, mult_isComplex, pow_one, Finset.prod_pow, pow_two, mul_assoc, mul_inv_cancel₀
      (Finset.prod_ne_zero_iff.mpr <| fun _ _ => Real.exp_ne_zero _), mul_one]
  · simp [prod_eq_prod_mul_prod, mult_isReal, mult_isComplex]

variable (K)

/--
Definition of `fderiv_expMapBasis` / `fderiv_expMapBasis` 的定义

English:
abbreviation fderiv_expMapBasis
  signature: (x : realSpace K)
  body: (fderiv_expMap ((completeBasis K).equivFun.symm x)).comp
    (completeBasis K).equivFunL.symm.toContinuousLinearMap

中文:
缩写 fderiv_expMapBasis
  签名: (x : realSpace K)
  定义体: (fderiv_expMap ((completeBasis K).equivFun.symm x)).comp
    (completeBasis K).equivFunL.symm.toContinuousLinearMap

Depends on / 依赖: completeBasis, equivFun, equivFun.symm, equivFunL, equivFunL.symm.toContinuousLinearMap, fderiv_expMap, toContinuousLinearMap
-/
abbrev fderiv_expMapBasis (x : realSpace K) : realSpace K ->L[Real] realSpace K :=
  (fderiv_expMap ((completeBasis K).equivFun.symm x)).comp
    (completeBasis K).equivFunL.symm.toContinuousLinearMap

/--
theorem `hasFDerivAt_expMapBasis` / 定理 `hasFDerivAt_expMapBasis`

English:
theorem hasFDerivAt_expMapBasis
  given: (x : realSpace K)
  proof: by
  change HasFDerivAt (expMap ∘ (completeBasis K).equivFunL.symm) (fderiv_expMapBasis K x) x
  exact (hasFDerivAt_expMap _).comp x (completeBasis K).equivFunL.symm.hasFDerivAt

中文:
定理 hasFDerivAt_expMapBasis
  条件: (x : realSpace K)
  证明: by
  change HasFDerivAt (expMap ∘ (completeBasis K).equivFunL.symm) (fderiv_expMapBasis K x) x
  exact (hasFDerivAt_expMap _).comp x (completeBasis K).equivFunL.symm.hasFDerivAt

Depends on / 依赖: HasFDerivAt, completeBasis, equivFunL, equivFunL.symm, equivFunL.symm.hasFDerivAt, expMap, fderiv_expMapBasis, hasFDerivAt, hasFDerivAt_expMap
-/
theorem hasFDerivAt_expMapBasis (x : realSpace K) :
    HasFDerivAt expMapBasis (fderiv_expMapBasis K x) x := by
  change HasFDerivAt (expMap ∘ (completeBasis K).equivFunL.symm) (fderiv_expMapBasis K x) x
  exact (hasFDerivAt_expMap _).comp x (completeBasis K).equivFunL.symm.hasFDerivAt

open Classical ContinuousLinearMap in
/--
theorem `abs_det_fderiv_expMapBasis` / 定理 `abs_det_fderiv_expMapBasis`

English:
theorem abs_det_fderiv_expMapBasis
  given: (x : realSpace K)
  proof: by
  simp_rw [fderiv_expMapBasis, det, toLinearMap_comp, LinearMap.det_comp, fderiv_expMap, coe_pi,
    toLinearMap_comp, coe_proj, LinearMap.det_pi, LinearMap.det_ring, ContinuousLinearMap.coe_coe,
    smulRight_apply, one_apply_eq_self, one_smul, abs_mul, abs_det_completeBasis_equivFunL_symm,
    

中文:
定理 abs_det_fderiv_expMapBasis
  条件: (x : realSpace K)
  证明: by
  simp_rw [fderiv_expMapBasis, det, toLinearMap_comp, LinearMap.det_comp, fderiv_expMap, coe_pi,
    toLinearMap_comp, coe_proj, LinearMap.det_pi, LinearMap.det_ring, ContinuousLinearMap.coe_coe,
    smulRight_apply, one_apply_eq_self, one_smul, abs_mul, abs_det_completeBasis_equivFunL_symm,
    

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_coe, LinearMap, LinearMap.det_comp, LinearMap.det_pi, LinearMap.det_ring, Nat.abs_ofNat, Real.exp_mul, Real.exp_nonneg, Real.rpow_natCast, abs_det_completeBasis_equivFunL_symm, abs_inv, abs_mul, abs_ofNat, abs_of_nonneg, abs_pow, abs_prod, coe_coe, coe_pi, coe_proj
-/
theorem abs_det_fderiv_expMapBasis (x : realSpace K) :
    |(fderiv_expMapBasis K x).det| =
      Real.exp (x w₀ * Module.finrank Rat K) *
      (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ * 2⁻¹ ^ nrComplexPlaces K *
        (Module.finrank Rat K) * regulator K := by
  simp_rw [fderiv_expMapBasis, det, toLinearMap_comp, LinearMap.det_comp, fderiv_expMap, coe_pi,
    toLinearMap_comp, coe_proj, LinearMap.det_pi, LinearMap.det_ring, ContinuousLinearMap.coe_coe,
    smulRight_apply, one_apply_eq_self, one_smul, abs_mul, abs_det_completeBasis_equivFunL_symm,
    prod_deriv_expMap_single]
  simp_rw [abs_mul, Real.exp_mul, abs_pow, Real.rpow_natCast, abs_of_nonneg (Real.exp_nonneg _),
    abs_inv, abs_prod, abs_of_nonneg (expMapBasis_nonneg _ _), Nat.abs_ofNat]
  ring

variable {K}

open ENNReal MeasureTheory

open scoped Classical in
/--
theorem `setLIntegral_expMapBasis_image` / 定理 `setLIntegral_expMapBasis_image`

English:
theorem setLIntegral_expMapBasis_image
  statement: {s : Set (realSpace K)} (hs : MeasurableSet s)
  proof: by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x _ => (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt) (injective_expMapBasis K).injOn]
  simp_rw [abs_det_fderiv_expMapBasis]
  have : Measurable expMapBasis := (continuous_expMapBasis K).measurable
  rw [← lintegral_const

中文:
定理 setLIntegral_expMapBasis_image
  结论: {s : Set (realSpace K)} (hs : MeasurableSet s)
  证明: by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x _ => (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt) (injective_expMapBasis K).injOn]
  simp_rw [abs_det_fderiv_expMapBasis]
  have : Measurable expMapBasis := (continuous_expMapBasis K).measurable
  rw [← lintegral_const

Depends on / 依赖: Finset, Finset.prod_nonneg, IsComplex, Measurable, abs_det_fderiv_expMapBasis, continuous_expMapBasis, expMapBasis, expMapBasis_pos, fun_prop, hasFDerivAt_expMapBasis, hasFDerivWithinAt, injective_expMapBasis, inv_nonneg, inv_nonneg.mpr, lintegral_const_mul, lintegral_image_eq_lintegral_abs_det_fderiv_mul, measurable, ofReal_, ofReal_mul, prod_nonneg
-/
theorem setLIntegral_expMapBasis_image {s : Set (realSpace K)} (hs : MeasurableSet s)
    {f : (InfinitePlace K -> Real) -> Real>=0∞} (hf : Measurable f) :
    ∫⁻ x in expMapBasis '' s, f x =
      (2 : Real>=0∞)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (Module.finrank Rat K) *
        ∫⁻ x in s, ENNReal.ofReal (Real.exp (x w₀ * Module.finrank Rat K)) *
          (∏ i : {w : InfinitePlace K // IsComplex w},
            .ofReal (expMapBasis (fun w => x w) i))⁻¹ * f (expMapBasis x) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x _ => (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt) (injective_expMapBasis K).injOn]
  simp_rw [abs_det_fderiv_expMapBasis]
  have : Measurable expMapBasis := (continuous_expMapBasis K).measurable
  rw [← lintegral_const_mul _ (by fun_prop)]
  congr with x
  have : 0 <= (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ :=
inv_nonneg.mpr Finset.prod_nonneg fun _ _ => (expMapBasis_pos _ _).le
  rw [ofReal_mul (by positivity)]; rw [ofReal_mul (by positivity)]; rw [ofReal_mul (by positivity)]; rw [ofReal_mul (by positivity)]; rw [ofReal_pow (by positivity)]; rw [ofReal_inv_of_pos (Finset.prod_pos
    fun _ _ => expMapBasis_pos _ _)]; rw [ofReal_inv_of_pos zero_lt_two]; rw [ofReal_ofNat]; rw [ofReal_natCast]; rw [ofReal_prod_of_nonneg (fun _ _ => (expMapBasis_pos _ _).le)]
  ring

end expMapBasis

section paramSet

variable [NumberField K]

open scoped Classical in
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `paramSet` / `paramSet` 的定义

English:
abbreviation paramSet
  signature: : Set (realSpace K)
  body: Set.univ.pi fun w => if w = w₀ then Set.Iic 0 else Set.Ico 0 1

中文:
缩写 paramSet
  签名: : Set (realSpace K)
  定义体: Set.univ.pi fun w => if w = w₀ then Set.Iic 0 else Set.Ico 0 1

Depends on / 依赖: Set.Ico, Set.Iic, Set.univ.pi
-/
noncomputable abbrev paramSet : Set (realSpace K) :=
  Set.univ.pi fun w => if w = w₀ then Set.Iic 0 else Set.Ico 0 1

/--
theorem `measurableSet_paramSet` / 定理 `measurableSet_paramSet`

English:
theorem measurableSet_paramSet
  proof: by
  refine MeasurableSet.univ_pi fun _ => ?_
  split_ifs
  · exact measurableSet_Iic
  · exact measurableSet_Ico

中文:
定理 measurableSet_paramSet
  证明: by
  refine MeasurableSet.univ_pi fun _ => ?_
  split_ifs
  · exact measurableSet_Iic
  · exact measurableSet_Ico

Depends on / 依赖: MeasurableSet, MeasurableSet.univ_pi, measurableSet_Ico, measurableSet_Iic, split_ifs, univ_pi
-/
theorem measurableSet_paramSet :
    MeasurableSet (paramSet K) := by
  refine MeasurableSet.univ_pi fun _ => ?_
  split_ifs
  · exact measurableSet_Iic
  · exact measurableSet_Ico

open scoped Classical in
/--
theorem `interior_paramSet` / 定理 `interior_paramSet`

English:
theorem interior_paramSet
  proof: by
  simp [interior_pi_set Set.finite_univ, apply_ite]

中文:
定理 interior_paramSet
  证明: by
  simp [interior_pi_set Set.finite_univ, apply_ite]

Depends on / 依赖: Set.finite_univ, apply_ite, finite_univ, interior_pi_set
-/
theorem interior_paramSet :
    interior (paramSet K) = Set.univ.pi fun w => if w = w₀ then Set.Iio 0 else Set.Ioo 0 1 := by
  simp [interior_pi_set Set.finite_univ, apply_ite]

open scoped Classical in
/--
theorem `closure_paramSet` / 定理 `closure_paramSet`

English:
theorem closure_paramSet
  proof: by
  simp [closure_pi_set, apply_ite]

中文:
定理 closure_paramSet
  证明: by
  simp [closure_pi_set, apply_ite]

Depends on / 依赖: apply_ite, closure_pi_set
-/
theorem closure_paramSet :
    closure (paramSet K) = Set.univ.pi fun w => if w = w₀ then Set.Iic 0 else Set.Icc 0 1 := by
  simp [closure_pi_set, apply_ite]

/--
theorem `normAtAllPlaces_normLeOne_eq_image` / 定理 `normAtAllPlaces_normLeOne_eq_image`

English:
theorem normAtAllPlaces_normLeOne_eq_image
  proof: by
  ext x
  by_cases hx : forall w, 0 < x w
  · rw [← expMapBasis.right_inv (Set.mem_univ_pi.mpr hx), (injective_expMapBasis K).mem_set_image]
    simp only [normAtAllPlaces_normLeOne, Set.mem_inter_iff, Set.mem_ofPred_eq, expMapBasis_nonneg,
      Set.mem_preimage, logMap_expMapBasis, implies_true

中文:
定理 normAtAllPlaces_normLeOne_eq_image
  证明: by
  ext x
  by_cases hx : forall w, 0 < x w
  · rw [← expMapBasis.right_inv (Set.mem_univ_pi.mpr hx), (injective_expMapBasis K).mem_set_image]
    simp only [normAtAllPlaces_normLeOne, Set.mem_inter_iff, Set.mem_ofPred_eq, expMapBasis_nonneg,
      Set.mem_preimage, logMap_expMapBasis, implies_true

Depends on / 依赖: Module, Module.finrank_pos.ne, Real.exp_le_one_iff, Real.exp_ne_zero, Real.exp_nonneg, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi, Set.mem_univ_pi.mpr, and_true, expMapBasis, expMapBasis.right_inv, expMapBasis_nonneg, exp_le_one_iff, exp_ne_zero, exp_nonneg, false_and, finrank_pos, implies_true
-/
theorem normAtAllPlaces_normLeOne_eq_image :
    normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K) := by
  ext x
  by_cases hx : forall w, 0 < x w
  · rw [← expMapBasis.right_inv (Set.mem_univ_pi.mpr hx), (injective_expMapBasis K).mem_set_image]
    simp only [normAtAllPlaces_normLeOne, Set.mem_inter_iff, Set.mem_ofPred_eq, expMapBasis_nonneg,
      Set.mem_preimage, logMap_expMapBasis, implies_true, and_true, norm_expMapBasis,
      pow_le_one_iff_of_nonneg (Real.exp_nonneg _) Module.finrank_pos.ne', Real.exp_le_one_iff,
      ne_eq, pow_eq_zero_iff', Real.exp_ne_zero, false_and, not_false_eq_true, Set.mem_univ_pi]
    refine ⟨fun ⟨h₁, h₂⟩ w => ?_, fun h => ⟨fun w hw => by simpa [hw] using h w, by simpa using h w₀⟩⟩
    · split_ifs with hw
      · exact hw ▸ h₂
      · exact h₁ w hw
  · refine ⟨?_, ?_⟩
    · rintro ⟨a, ⟨ha, _⟩, rfl⟩
      exact (hx fun w => fundamentalCone.normAtPlace_pos_of_mem ha w).elim
    · rintro ⟨a, _, rfl⟩
      exact (hx fun w => expMapBasis_pos a w).elim

/--
theorem `normLeOne_eq_preimage` / 定理 `normLeOne_eq_preimage`

English:
theorem normLeOne_eq_preimage
  proof: by
  rw [normLeOne_eq_preimage_image]; rw [normAtAllPlaces_normLeOne_eq_image]

中文:
定理 normLeOne_eq_preimage
  证明: by
  rw [normLeOne_eq_preimage_image]; rw [normAtAllPlaces_normLeOne_eq_image]

Depends on / 依赖: normAtAllPlaces_normLeOne_eq_image, normLeOne_eq_preimage_image
-/
theorem normLeOne_eq_preimage :
    normLeOne K = normAtAllPlaces ⁻¹' expMapBasis '' (paramSet K) := by
  rw [normLeOne_eq_preimage_image]; rw [normAtAllPlaces_normLeOne_eq_image]

/--
theorem `subset_interior_normLeOne` / 定理 `subset_interior_normLeOne`

English:
theorem subset_interior_normLeOne
  proof: by
  rw [normLeOne_eq_preimage]
refine subset_trans (Set.preimage_mono ?_)
    preimage_interior_subset_interior_preimage (continuous_normAtAllPlaces K)
  have : IsOpen (expMapBasis '' (interior (paramSet K))) :=
    expMapBasis.isOpen_image_of_subset_source isOpen_interior (by simp [expMapBasis_sou

中文:
定理 subset_interior_normLeOne
  证明: by
  rw [normLeOne_eq_preimage]
refine subset_trans (Set.preimage_mono ?_)
    preimage_interior_subset_interior_preimage (continuous_normAtAllPlaces K)
  have : IsOpen (expMapBasis '' (interior (paramSet K))) :=
    expMapBasis.isOpen_image_of_subset_source isOpen_interior (by simp [expMapBasis_sou

Depends on / 依赖: IsOpen, Set.image_mono, Set.preimage_mono, continuous_normAtAllPlaces, expMapBasis, expMapBasis.isOpen_image_of_subset_source, expMapBasis_source, image_mono, interior, interior_maximal, interior_subset, isOpen_image_of_subset_source, isOpen_interior, normLeOne_eq_preimage, paramSet, preimage_interior_subset_interior_preimage, preimage_mono, subset_trans
-/
theorem subset_interior_normLeOne :
    normAtAllPlaces ⁻¹' expMapBasis '' interior (paramSet K) subseteq interior (normLeOne K) := by
  rw [normLeOne_eq_preimage]
refine subset_trans (Set.preimage_mono ?_)
    preimage_interior_subset_interior_preimage (continuous_normAtAllPlaces K)
  have : IsOpen (expMapBasis '' (interior (paramSet K))) :=
    expMapBasis.isOpen_image_of_subset_source isOpen_interior (by simp [expMapBasis_source])
  exact interior_maximal (Set.image_mono interior_subset) this

open ENNReal MeasureTheory

/--
theorem `closure_paramSet_ae_interior` / 定理 `closure_paramSet_ae_interior`

English:
theorem closure_paramSet_ae_interior
  statement: closure (paramSet K) =ᵐ[volume] interior (paramSet K)
  proof: by
  rw [closure_paramSet]; rw [interior_paramSet]; rw [volume_pi]
  refine Measure.ae_eq_set_pi fun w _ => ?_
  split_ifs
  · exact Iio_ae_eq_Iic.symm
  · exact Ioo_ae_eq_Icc.symm

中文:
定理 closure_paramSet_ae_interior
  结论: closure (paramSet K) =ᵐ[volume] interior (paramSet K)
  证明: by
  rw [closure_paramSet]; rw [interior_paramSet]; rw [volume_pi]
  refine Measure.ae_eq_set_pi fun w _ => ?_
  split_ifs
  · exact Iio_ae_eq_Iic.symm
  · exact Ioo_ae_eq_Icc.symm

Depends on / 依赖: Iio_ae_eq_Iic, Iio_ae_eq_Iic.symm, Ioo_ae_eq_Icc, Ioo_ae_eq_Icc.symm, Measure, Measure.ae_eq_set_pi, ae_eq_set_pi, closure_paramSet, interior_paramSet, split_ifs, volume_pi
-/
theorem closure_paramSet_ae_interior : closure (paramSet K) =ᵐ[volume] interior (paramSet K) := by
  rw [closure_paramSet]; rw [interior_paramSet]; rw [volume_pi]
  refine Measure.ae_eq_set_pi fun w _ => ?_
  split_ifs
  · exact Iio_ae_eq_Iic.symm
  · exact Ioo_ae_eq_Icc.symm

/--
theorem `setLIntegral_paramSet_exp` / 定理 `setLIntegral_paramSet_exp`

English:
theorem setLIntegral_paramSet_exp
  given: {n : Nat} (hn : 0 < n)
  proof: by
  classical
  have hn : 0 < (n : Real) := Nat.cast_pos.mpr hn
  rw [volume_pi]; rw [paramSet]; rw [Measure.restrict_pi_pi]; rw [lintegral_eq_lmarginal_univ 0]; rw [lmarginal_erase' _ (by fun_prop) (Finset.mem_univ w₀)]; rw [if_pos rfl]
  simp_rw [Function.update_self, lmarginal, lintegral_const, 

中文:
定理 setLIntegral_paramSet_exp
  条件: {n : 自然数} (hn : 0 < n)
  证明: by
  classical
  have hn : 0 < (n : Real) := Nat.cast_pos.mpr hn
  rw [volume_pi]; rw [paramSet]; rw [Measure.restrict_pi_pi]; rw [lintegral_eq_lmarginal_univ 0]; rw [lmarginal_erase' _ (by fun_prop) (Finset.mem_univ w₀)]; rw [if_pos rfl]
  simp_rw [Function.update_self, lmarginal, lintegral_const, 

Depends on / 依赖: Finset, Finset.mem_univ, Finset.ne_of_mem_erase, Function, Function.update_self, Measure, Measure.pi_univ, Measure.restrict_apply_univ, Measure.restrict_pi_pi, Nat.cast_pos.mpr, Real.volume_Ico, Subtype, Subtype.prop, cast_pos, classical, fun_prop, if_neg, if_pos, lintegral_const, lintegral_eq_lmarginal_univ
-/
theorem setLIntegral_paramSet_exp {n : Nat} (hn : 0 < n) :
    ∫⁻ (x : realSpace K) in paramSet K, .ofReal (Real.exp (x w₀ * n)) = (n : Real>=0∞)⁻¹ := by
  classical
  have hn : 0 < (n : Real) := Nat.cast_pos.mpr hn
  rw [volume_pi]; rw [paramSet]; rw [Measure.restrict_pi_pi]; rw [lintegral_eq_lmarginal_univ 0]; rw [lmarginal_erase' _ (by fun_prop) (Finset.mem_univ w₀)]; rw [if_pos rfl]
  simp_rw [Function.update_self, lmarginal, lintegral_const, Measure.pi_univ, if_neg
    (Finset.ne_of_mem_erase (Subtype.prop _)), Measure.restrict_apply_univ, Real.volume_Ico,
    sub_zero, ofReal_one, prod_const_one, mul_one, mul_comm _ (n : Real)]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic hn _)]; rw [integral_exp_mul_Iic
    hn]; rw [mul_zero]; rw [Real.exp_zero]; rw [ofReal_div_of_pos hn]; rw [ofReal_one]; rw [ofReal_natCast]; rw [one_div]
  filter_upwards with _ using Real.exp_nonneg _

end paramSet

section compactSet

variable [NumberField K]

open scoped Pointwise

open scoped Classical in
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `compactSet` / `compactSet` 的定义

English:
abbreviation compactSet
  signature: : Set (realSpace K)
  body: (Set.Icc (0 : Real) 1) • (expMapBasis '' Set.univ.pi fun w => if w = w₀ then {0} else Set.Icc 0 1)

中文:
缩写 compactSet
  签名: : Set (realSpace K)
  定义体: (Set.Icc (0 : Real) 1) • (expMapBasis '' Set.univ.pi fun w => if w = w₀ then {0} else Set.Icc 0 1)

Depends on / 依赖: Set.Icc, Set.univ.pi, expMapBasis
-/
noncomputable abbrev compactSet : Set (realSpace K) :=
  (Set.Icc (0 : Real) 1) • (expMapBasis '' Set.univ.pi fun w => if w = w₀ then {0} else Set.Icc 0 1)

/--
theorem `isCompact_compactSet` / 定理 `isCompact_compactSet`

English:
theorem isCompact_compactSet
  proof: by
refine isCompact_Icc.smul_set (isCompact_univ_pi fun w => ?_).image_of_continuousOn
    (continuous_expMapBasis K).continuousOn
  split_ifs
  · exact isCompact_singleton
  · exact isCompact_Icc

中文:
定理 isCompact_compactSet
  证明: by
refine isCompact_Icc.smul_set (isCompact_univ_pi fun w => ?_).image_of_continuousOn
    (continuous_expMapBasis K).continuousOn
  split_ifs
  · exact isCompact_singleton
  · exact isCompact_Icc

Depends on / 依赖: continuousOn, continuous_expMapBasis, image_of_continuousOn, isCompact_Icc, isCompact_Icc.smul_set, isCompact_singleton, isCompact_univ_pi, smul_set, split_ifs
-/
theorem isCompact_compactSet :
    IsCompact (compactSet K) := by
refine isCompact_Icc.smul_set (isCompact_univ_pi fun w => ?_).image_of_continuousOn
    (continuous_expMapBasis K).continuousOn
  split_ifs
  · exact isCompact_singleton
  · exact isCompact_Icc

/--
theorem `zero_mem_compactSet` / 定理 `zero_mem_compactSet`

English:
theorem zero_mem_compactSet
  proof: by
  refine Set.zero_mem_smul_iff.mpr (Or.inl ⟨Set.left_mem_Icc.mpr zero_le_one, ?_⟩)
  exact Set.image_nonempty.mpr (Set.univ_pi_nonempty_iff.mpr (by aesop))

中文:
定理 zero_mem_compactSet
  证明: by
  refine Set.zero_mem_smul_iff.mpr (Or.inl ⟨Set.left_mem_Icc.mpr zero_le_one, ?_⟩)
  exact Set.image_nonempty.mpr (Set.univ_pi_nonempty_iff.mpr (by aesop))

Depends on / 依赖: Or.inl, Set.image_nonempty.mpr, Set.left_mem_Icc.mpr, Set.univ_pi_nonempty_iff.mpr, Set.zero_mem_smul_iff.mpr, image_nonempty, left_mem_Icc, univ_pi_nonempty_iff, zero_le_one, zero_mem_smul_iff
-/
theorem zero_mem_compactSet :
    0 in compactSet K := by
  refine Set.zero_mem_smul_iff.mpr (Or.inl ⟨Set.left_mem_Icc.mpr zero_le_one, ?_⟩)
  exact Set.image_nonempty.mpr (Set.univ_pi_nonempty_iff.mpr (by aesop))

/--
theorem `nonneg_of_mem_compactSet` / 定理 `nonneg_of_mem_compactSet`

English:
theorem nonneg_of_mem_compactSet
  given: {x : realSpace K} (hx : x in compactSet K) (w : InfinitePlace K)
  proof: by
  obtain ⟨c, hc, ⟨_, ⟨⟨a, ha, rfl⟩, _, rfl⟩⟩⟩ := hx
  exact mul_nonneg hc.1 (expMapBasis_pos _ _).le

中文:
定理 nonneg_of_mem_compactSet
  条件: {x : realSpace K} (hx : x in compactSet K) (w : InfinitePlace K)
  证明: by
  obtain ⟨c, hc, ⟨_, ⟨⟨a, ha, rfl⟩, _, rfl⟩⟩⟩ := hx
  exact mul_nonneg hc.1 (expMapBasis_pos _ _).le

Depends on / 依赖: expMapBasis_pos, mul_nonneg
-/
theorem nonneg_of_mem_compactSet {x : realSpace K} (hx : x in compactSet K) (w : InfinitePlace K) :
    0 <= x w := by
  obtain ⟨c, hc, ⟨_, ⟨⟨a, ha, rfl⟩, _, rfl⟩⟩⟩ := hx
  exact mul_nonneg hc.1 (expMapBasis_pos _ _).le

variable {K} in
/--
theorem `compactSet_eq_union_aux₁` / 定理 `compactSet_eq_union_aux₁`

English:
theorem compactSet_eq_union_aux₁
  statement: {x : realSpace K} (hx₀ : x != 0)
  proof: by
  classical
  obtain ⟨c, hc, ⟨_, ⟨y, hy, rfl⟩, rfl⟩⟩ := hx₁
  refine ⟨fun w => if w = w₀ then Real.log c else y w, ?_, ?_⟩
  · rw [closure_paramSet, Set.mem_univ_pi]
    intro w
    split_ifs with h
    · refine Real.log_nonpos hc.1 hc.2
    · simpa [h] using hy w (Set.mem_univ _)
  · have hc' : 

中文:
定理 compactSet_eq_union_aux₁
  结论: {x : realSpace K} (hx₀ : x != 0)
  证明: by
  classical
  obtain ⟨c, hc, ⟨_, ⟨y, hy, rfl⟩, rfl⟩⟩ := hx₁
  refine ⟨fun w => if w = w₀ then Real.log c else y w, ?_, ?_⟩
  · rw [closure_paramSet, Set.mem_univ_pi]
    intro w
    split_ifs with h
    · refine Real.log_nonpos hc.1 hc.2
    · simpa [h] using hy w (Set.mem_univ _)
  · have hc' : 

Depends on / 依赖: Real.exp_log, Real.log, Real.log_nonpos, Set.mem_univ, Set.mem_univ_pi, classical, closure_paramSet, contrapose, eq_comm, expMapBasis_apply, exp_log, if_pos, le_antisymm, log_nonpos, mem_univ, mem_univ_pi, split_ifs, zero_smul
-/
theorem compactSet_eq_union_aux₁ {x : realSpace K} (hx₀ : x != 0)
    (hx₁ : x in compactSet K) :
    x in expMapBasis '' closure (paramSet K) := by
  classical
  obtain ⟨c, hc, ⟨_, ⟨y, hy, rfl⟩, rfl⟩⟩ := hx₁
  refine ⟨fun w => if w = w₀ then Real.log c else y w, ?_, ?_⟩
  · rw [closure_paramSet, Set.mem_univ_pi]
    intro w
    split_ifs with h
    · refine Real.log_nonpos hc.1 hc.2
    · simpa [h] using hy w (Set.mem_univ _)
  · have hc' : 0 < c := by
      contrapose! hx₀
      rw [le_antisymm hx₀ hc.1]; rw [zero_smul]
    rw [expMapBasis_apply'']; rw [if_pos rfl]; rw [Real.exp_log hc']
    congr with w
    split_ifs with h
    · simpa [h, eq_comm] using hy w₀
    · rfl

variable {K} in
/--
theorem `compactSet_eq_union_aux₂` / 定理 `compactSet_eq_union_aux₂`

English:
theorem compactSet_eq_union_aux₂
  statement: {x : realSpace K} (hx₀ : x != 0)
  proof: by
  classical
  simp only [closure_paramSet, Set.mem_image, Set.mem_smul, exists_exists_and_eq_and] at hx₁ ⊢
  obtain ⟨y, hy, rfl⟩ := hx₁
  refine ⟨Real.exp (y w₀), ⟨Real.exp_nonneg _, ?_⟩,
        fun i => if i = w₀ then 0 else y i, Set.mem_univ_pi.mpr fun w => ?_,
        by rw [expMapBasis_apply

中文:
定理 compactSet_eq_union_aux₂
  结论: {x : realSpace K} (hx₀ : x != 0)
  证明: by
  classical
  simp only [closure_paramSet, Set.mem_image, Set.mem_smul, exists_exists_and_eq_and] at hx₁ ⊢
  obtain ⟨y, hy, rfl⟩ := hx₁
  refine ⟨Real.exp (y w₀), ⟨Real.exp_nonneg _, ?_⟩,
        fun i => if i = w₀ then 0 else y i, Set.mem_univ_pi.mpr fun w => ?_,
        by rw [expMapBasis_apply

Depends on / 依赖: Real.exp, Real.exp_le_one_iff.mpr, Real.exp_nonneg, Set.mem_image, Set.mem_smul, Set.mem_univ, Set.mem_univ_pi.mpr, classical, closure_paramSet, exists_exists_and_eq_and, expMapBasis_apply, exp_le_one_iff, exp_nonneg, mem_image, mem_smul, mem_univ, mem_univ_pi, split_ifs
-/
theorem compactSet_eq_union_aux₂ {x : realSpace K} (hx₀ : x != 0)
    (hx₁ : x in expMapBasis '' closure (paramSet K)) :
    x in compactSet K := by
  classical
  simp only [closure_paramSet, Set.mem_image, Set.mem_smul, exists_exists_and_eq_and] at hx₁ ⊢
  obtain ⟨y, hy, rfl⟩ := hx₁
  refine ⟨Real.exp (y w₀), ⟨Real.exp_nonneg _, ?_⟩,
        fun i => if i = w₀ then 0 else y i, Set.mem_univ_pi.mpr fun w => ?_,
        by rw [expMapBasis_apply'' y]⟩
  · exact Real.exp_le_one_iff.mpr (by simpa using hy w₀ (Set.mem_univ _))
  · split_ifs with h
    · rfl
    · simpa [h] using hy w (Set.mem_univ _)

/--
theorem `compactSet_eq_union` / 定理 `compactSet_eq_union`

English:
theorem compactSet_eq_union
  proof: by
  ext x
  by_cases hx₀ : x = 0
  · simpa [hx₀] using zero_mem_compactSet K
  · refine ⟨fun hx => Set.mem_union_left _ (compactSet_eq_union_aux₁ hx₀ hx), fun hx => ?_⟩
    simp only [Set.union_singleton, Set.mem_insert_iff, hx₀, false_or] at hx
    exact compactSet_eq_union_aux₂ hx₀ hx

中文:
定理 compactSet_eq_union
  证明: by
  ext x
  by_cases hx₀ : x = 0
  · simpa [hx₀] using zero_mem_compactSet K
  · refine ⟨fun hx => Set.mem_union_left _ (compactSet_eq_union_aux₁ hx₀ hx), fun hx => ?_⟩
    simp only [Set.union_singleton, Set.mem_insert_iff, hx₀, false_or] at hx
    exact compactSet_eq_union_aux₂ hx₀ hx

Depends on / 依赖: Set.mem_insert_iff, Set.mem_union_left, Set.union_singleton, false_or, mem_insert_iff, mem_union_left, union_singleton, zero_mem_compactSet
-/
theorem compactSet_eq_union :
    compactSet K = expMapBasis '' closure (paramSet K) union {0} := by
  ext x
  by_cases hx₀ : x = 0
  · simpa [hx₀] using zero_mem_compactSet K
  · refine ⟨fun hx => Set.mem_union_left _ (compactSet_eq_union_aux₁ hx₀ hx), fun hx => ?_⟩
    simp only [Set.union_singleton, Set.mem_insert_iff, hx₀, false_or] at hx
    exact compactSet_eq_union_aux₂ hx₀ hx

/--
theorem `expMapBasis_closure_subset_compactSet` / 定理 `expMapBasis_closure_subset_compactSet`

English:
theorem expMapBasis_closure_subset_compactSet
  proof: by
  rw [compactSet_eq_union]
  exact Set.subset_union_left

中文:
定理 expMapBasis_closure_subset_compactSet
  证明: by
  rw [compactSet_eq_union]
  exact Set.subset_union_left

Depends on / 依赖: Set.subset_union_left, compactSet_eq_union, subset_union_left
-/
theorem expMapBasis_closure_subset_compactSet :
    expMapBasis '' closure (paramSet K) subseteq compactSet K := by
  rw [compactSet_eq_union]
  exact Set.subset_union_left

/--
theorem `closure_normLeOne_subset` / 定理 `closure_normLeOne_subset`

English:
theorem closure_normLeOne_subset
  proof: by
  rw [normLeOne_eq_preimage]
  refine ((continuous_normAtAllPlaces K).closure_preimage_subset _).trans (Set.preimage_mono ?_)
  refine (isCompact_compactSet K).isClosed.closure_subset_iff.mpr ?_
  exact (Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet _)

中文:
定理 closure_normLeOne_subset
  证明: by
  rw [normLeOne_eq_preimage]
  refine ((continuous_normAtAllPlaces K).closure_preimage_subset _).trans (Set.preimage_mono ?_)
  refine (isCompact_compactSet K).isClosed.closure_subset_iff.mpr ?_
  exact (Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet _)

Depends on / 依赖: Set.image_mono, Set.preimage_mono, closure_preimage_subset, closure_subset_iff, continuous_normAtAllPlaces, expMapBasis_closure_subset_compactSet, image_mono, isClosed, isClosed.closure_subset_iff.mpr, isCompact_compactSet, normLeOne_eq_preimage, preimage_mono, subset_closure
-/
theorem closure_normLeOne_subset :
    closure (normLeOne K) subseteq normAtAllPlaces ⁻¹' (compactSet K) := by
  rw [normLeOne_eq_preimage]
  refine ((continuous_normAtAllPlaces K).closure_preimage_subset _).trans (Set.preimage_mono ?_)
  refine (isCompact_compactSet K).isClosed.closure_subset_iff.mpr ?_
  exact (Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet _)

open MeasureTheory

/--
theorem `compactSet_ae` / 定理 `compactSet_ae`

English:
theorem compactSet_ae
  proof: by
  rw [compactSet_eq_union]
  exact union_ae_eq_left_of_ae_eq_empty (by simp)

中文:
定理 compactSet_ae
  证明: by
  rw [compactSet_eq_union]
  exact union_ae_eq_left_of_ae_eq_empty (by simp)

Depends on / 依赖: compactSet_eq_union, union_ae_eq_left_of_ae_eq_empty
-/
theorem compactSet_ae :
    compactSet K =ᵐ[volume] expMapBasis '' closure (paramSet K) := by
  rw [compactSet_eq_union]
  exact union_ae_eq_left_of_ae_eq_empty (by simp)

end compactSet

section main_results

variable [NumberField K]

open Bornology ENNReal MeasureTheory

/--
theorem `isBounded_normLeOne` / 定理 `isBounded_normLeOne`

English:
theorem isBounded_normLeOne
  proof: by
  classical
  rw [normLeOne_eq_preimage]
  suffices IsBounded (expMapBasis '' paramSet K) by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp this
    refine isBounded_iff_forall_norm_le.mpr ⟨C, fun x hx => ?_⟩
    rw [norm_eq_sup'_normAtPlace]
    refine sup'_le _ _ fun w _ => ?_
    simpa 

中文:
定理 isBounded_normLeOne
  证明: by
  classical
  rw [normLeOne_eq_preimage]
  suffices IsBounded (expMapBasis '' paramSet K) by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp this
    refine isBounded_iff_forall_norm_le.mpr ⟨C, fun x hx => ?_⟩
    rw [norm_eq_sup'_normAtPlace]
    refine sup'_le _ _ fun w _ => ?_
    simpa 

Depends on / 依赖: IsBounded, IsBounded.subset, Real.norm_of_nonneg, Set.image_mono, _normAtPlace, classical, expMapBasis, image_mono, isBounded, isBounded.subs, isBounded_iff_forall_norm_le, isBounded_iff_forall_norm_le.mp, isBounded_iff_forall_norm_le.mpr, isCompact_compactSet, normAtAllPlaces_apply, normAtPlace_nonneg, normLeOne_eq_preimage, norm_eq_sup, norm_of_nonneg, paramSet
-/
theorem isBounded_normLeOne :
    IsBounded (normLeOne K) := by
  classical
  rw [normLeOne_eq_preimage]
  suffices IsBounded (expMapBasis '' paramSet K) by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp this
    refine isBounded_iff_forall_norm_le.mpr ⟨C, fun x hx => ?_⟩
    rw [norm_eq_sup'_normAtPlace]
    refine sup'_le _ _ fun w _ => ?_
    simpa [normAtAllPlaces_apply, Real.norm_of_nonneg (normAtPlace_nonneg w x)]
      using (pi_norm_le_iff_of_nonempty _).mp (hC _ hx) w
  refine IsBounded.subset ?_ (Set.image_mono subset_closure)
  exact (isCompact_compactSet K).isBounded.subset (expMapBasis_closure_subset_compactSet K)

open scoped Classical in
/--
theorem `volume_normLeOne` / 定理 `volume_normLeOne`

English:
theorem volume_normLeOne
  statement: volume (normLeOne K) =
  proof: by
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral (normLeOne_eq_preimage_image K).symm
    (measurableSet_normLeOne K)]; rw [normLeOne_eq_preimage]; rw [normAtAllPlaces_image_preimage_expMapBasis]; rw [setLIntegral_expMapBasis_image (measurableSet_paramSet K) (by fun_prop)]
  simp_rw [ENNReal.i

中文:
定理 volume_normLeOne
  结论: volume (normLeOne K) =
  证明: by
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral (normLeOne_eq_preimage_image K).symm
    (measurableSet_normLeOne K)]; rw [normLeOne_eq_preimage]; rw [normAtAllPlaces_image_preimage_expMapBasis]; rw [setLIntegral_expMapBasis_image (measurableSet_paramSet K) (by fun_prop)]
  simp_rw [ENNReal.i

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel_right, Finset, Finset.prod_ne_zero_iff.mpr, Module, Module.finrank_pos, expMapBasis_pos, finrank_pos, fun_prop, inv_mul_cancel_right, measurableSet_normLeOne, measurableSet_paramSet, normAtAllPlaces_image_preimage_expMapBasis, normLeOne_eq_preimage, normLeOne_eq_preimage_image, ofReal_ne_top, ofReal_ne_zero_iff, ofReal_ne_zero_iff.mpr, prod_ne_top, prod_ne_zero_iff
-/
theorem volume_normLeOne : volume (normLeOne K) =
    2 ^ nrRealPlaces K * NNReal.pi ^ nrComplexPlaces K * .ofReal (regulator K) := by
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral (normLeOne_eq_preimage_image K).symm
    (measurableSet_normLeOne K)]; rw [normLeOne_eq_preimage]; rw [normAtAllPlaces_image_preimage_expMapBasis]; rw [setLIntegral_expMapBasis_image (measurableSet_paramSet K) (by fun_prop)]
  simp_rw [ENNReal.inv_mul_cancel_right
    (Finset.prod_ne_zero_iff.mpr fun _ _ => ofReal_ne_zero_iff.mpr (expMapBasis_pos _ _))
    (prod_ne_top fun _ _ => ofReal_ne_top)]
  rw [setLIntegral_paramSet_exp K Module.finrank_pos]; rw [ofReal_mul zero_le_two]; rw [mul_pow]; rw [ofReal_ofNat]; rw [ENNReal.mul_inv_cancel_right (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
    (natCast_ne_top _)]; rw [coe_nnreal_eq]; rw [NNReal.coe_real_pi]; rw [mul_mul_mul_comm]; rw [← ENNReal.inv_pow]; rw [← mul_assoc]; rw [← mul_assoc]; rw [ENNReal.inv_mul_cancel_right (pow_ne_zero _ two_ne_zero)
    (pow_ne_top ENNReal.ofNat_ne_top)]

open scoped Classical in
/--
theorem `volume_interior_eq_volume_closure` / 定理 `volume_interior_eq_volume_closure`

English:
theorem volume_interior_eq_volume_closure
  proof: by
  have h₁ : MeasurableSet (normAtAllPlaces ⁻¹' compactSet K) :=
    (isCompact_compactSet K).measurableSet.preimage (continuous_normAtAllPlaces K).measurable
  have h₂ : MeasurableSet (normAtAllPlaces ⁻¹' expMapBasis '' interior (paramSet K)) := by
    refine MeasurableSet.preimage ?_ (continuous

中文:
定理 volume_interior_eq_volume_closure
  证明: by
  have h₁ : MeasurableSet (normAtAllPlaces ⁻¹' compactSet K) :=
    (isCompact_compactSet K).measurableSet.preimage (continuous_normAtAllPlaces K).measurable
  have h₂ : MeasurableSet (normAtAllPlaces ⁻¹' expMapBasis '' interior (paramSet K)) := by
    refine MeasurableSet.preimage ?_ (continuous

Depends on / 依赖: MeasurableSet, MeasurableSet.image_of_continuousOn_injOn, MeasurableSet.preimage, compactSet, continuousOn, continuous_expMapBasis, continuous_normAtAllPlaces, expMapBasis, image_of_continuousOn_injOn, injective_expMapBasis, interior, isCompact_compactSet, le_antisymm, measurable, measurableSet, measurableSet.preimage, measurableSet_interior, measure_, normAtAllPlaces, paramSet
-/
theorem volume_interior_eq_volume_closure :
    volume (interior (normLeOne K)) = volume (closure (normLeOne K)) := by
  have h₁ : MeasurableSet (normAtAllPlaces ⁻¹' compactSet K) :=
    (isCompact_compactSet K).measurableSet.preimage (continuous_normAtAllPlaces K).measurable
  have h₂ : MeasurableSet (normAtAllPlaces ⁻¹' expMapBasis '' interior (paramSet K)) := by
    refine MeasurableSet.preimage ?_ (continuous_normAtAllPlaces K).measurable
    refine MeasurableSet.image_of_continuousOn_injOn ?_ (continuous_expMapBasis K).continuousOn
      (injective_expMapBasis K).injOn
    exact measurableSet_interior
  refine le_antisymm (measure_mono interior_subset_closure) ?_
  refine (measure_mono (closure_normLeOne_subset K)).trans ?_
  refine le_of_eq_of_le ?_ (measure_mono (subset_interior_normLeOne K))
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral Set.preimage_image_preimage h₁]; rw [normAtAllPlaces_image_preimage_of_nonneg (fun x a w => nonneg_of_mem_compactSet K a w)]; rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral Set.preimage_image_preimage h₂]; rw [normAtAllPlaces_image_preimage_expMapBasis]; rw [setLIntegral_congr (compactSet_ae K)]; rw [setLIntegral_expMapBasis_image measurableSet_closure (by fun_prop)]; rw [setLIntegral_expMapBasis_image measurableSet_interior (by fun_prop)]; rw [setLIntegral_congr (closure_paramSet_ae_interior K)]

open scoped Classical in
/--
theorem `volume_frontier_normLeOne` / 定理 `volume_frontier_normLeOne`

English:
theorem volume_frontier_normLeOne
  proof: by
  rw [frontier]; rw [measure_sdiff]; rw [volume_interior_eq_volume_closure]; rw [tsub_self]
  · exact interior_subset_closure
  · exact measurableSet_interior.nullMeasurableSet
· refine lt_top_iff_ne_top.mp lt_of_le_of_lt (measure_mono interior_subset) ?_
    rw [volume_normLeOne]
    exact Batte

中文:
定理 volume_frontier_normLeOne
  证明: by
  rw [frontier]; rw [measure_sdiff]; rw [volume_interior_eq_volume_closure]; rw [tsub_self]
  · exact interior_subset_closure
  · exact measurableSet_interior.nullMeasurableSet
· refine lt_top_iff_ne_top.mp lt_of_le_of_lt (measure_mono interior_subset) ?_
    rw [volume_normLeOne]
    exact Batte

Depends on / 依赖: Batteries, Batteries.compareOfLessAndEq_eq_lt.mp, compareOfLessAndEq_eq_lt, frontier, interior_subset, interior_subset_closure, lt_of_le_of_lt, lt_top_iff_ne_top, lt_top_iff_ne_top.mp, measurableSet_interior, measurableSet_interior.nullMeasurableSet, measure_mono, measure_sdiff, nullMeasurableSet, tsub_self, volume_interior_eq_volume_closure, volume_normLeOne
-/
theorem volume_frontier_normLeOne :
     volume (frontier (normLeOne K)) = 0 := by
  rw [frontier]; rw [measure_sdiff]; rw [volume_interior_eq_volume_closure]; rw [tsub_self]
  · exact interior_subset_closure
  · exact measurableSet_interior.nullMeasurableSet
· refine lt_top_iff_ne_top.mp lt_of_le_of_lt (measure_mono interior_subset) ?_
    rw [volume_normLeOne]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl

end main_results

end NumberField.mixedEmbedding.fundamentalCone
